/-
# The inductive installs, differentially (task #97 P2d, part 2)

The module-level differential check, the shape `CoreTest.lean` and
`ExprOpsTest.lean` use one tier down (DESIGN §8.4, "correctness before
proofs"):

> write a base environment and an inductive block ONCE, as con-leche
> `ConstantInfo` values; run **con-leche's own `checkDecl`** on
> `.indDecl block nP`; run the arena's `Inductives.checkIndDecl` on the
> interned block; compare the WHOLE outcome.

"Whole outcome" means: an `ok` must meet an `ok` **at the same environment**
— every installed constant's type, value, rules, capability record and
projection table compared — and an error must meet an error of the same KIND
and the same MESSAGE.  So a check passes only if the two checkers agree about
what happened, not merely about whether something did.

**How the two environments are compared without a readback.**  con-leche's
answer is an `Env` of `ConstantInfo` values; the arena's is an `IFEnv` of
`IConstantInfo` handles.  The comparison INTERNS con-leche's answer into the
arena's own store, after the arena's run, and compares the two handle lists.
That is sound in exactly the way the arena's other tests rely on: `intern` is
hash-consing and `denoteE` is injective (task #97a's `denoteE_inj`), so two
handles in one store are equal iff they denote the same term.  It is also the
strictest available comparison — it sees a difference in a binder's `PropWhen`
datum, which a `Repr` comparison would show and a definitional one would not.

**Why `checkDecl` and not the arm directly.**  con-leche's `checkDecl` tests
`basisPinHit` before the inductive routes: a block whose members are named as
one of the five pinned basis blocks' installs the PIN instead.  Every block
here is deliberately named OUTSIDE that family (`N`, `Eq'`, `Pair`, …) — it
has to be, since `checkConstantVal` rejects a reserved basis name outright —
so `basisPinHit` misses and `checkDecl` IS the `.indDecl` arm, which is what
`Inductives.checkIndDecl` twins.

**The blocks are generated, not hand-written.**  A recursor type and its rule
right-hand sides are large terms; writing them by hand would test the fixture
rather than the checker.  `mkNativeBlock` below builds them with con-leche's
OWN generators (`structRecTyR`, `structRecRhsR`) — the same terms the install
fabricates and compares against — so a fixture is the block a real elaborator
would export.  The generator is common INPUT to both checkers and so cannot
bias the differential, which is between the two checkers.

Nothing here is a proof and nothing here is an `#eval` print: every check is
kernel-reduced, so a disagreement is a build failure.
-/
import ConRon.Arena.Inductives
import ConLeche.Kernel.Checker

namespace ConRon.Arena.InductivesTest

open ConLeche
open ConRon.Arena

/-! ## Interning a con-leche environment

The one direction the test needs.  `CoreTest.lean`'s converters are `private`
to that module and `Arena/Intern.lean`'s do not cover the `projInfo` arm —
which this module DOES reach — so it is written here. -/

/-- con-leche: none — intern a con-leche `Expr` into the arena, structurally.
Test scaffolding: the real parser interns from the export's bytes. -/
private def iE : ConLeche.Expr → AM EIdx
  | .bvar i => internE (.bvar i)
  | .fvar i ty => do internE (.fvar i (← iE ty))
  | .sort u => do internE (.sort (← internLevel u))
  | .const n us => do internE (.const (← internName n) (← internLevels us))
  | .app f a => do internE (.app (← iE f) (← iE a))
  | .lam ty b m => do internE (.lam (← iE ty) (← iE b) m)
  | .forallE ty b m => do internE (.forallE (← iE ty) (← iE b) m)
  | .letE ty v b => do internE (.letE (← iE ty) (← iE v) (← iE b))
  | .lit l => internE (.lit l)
  | .proj s i e => do internE (.proj (← internName s) i (← iE e))

/-- con-leche: none — intern a `ConstantVal`. -/
private def iCV (cv : ConstantVal) : AM IConstantVal := do
  pure ⟨← internName cv.name, ← cv.levelParams.mapM internName, ← iE cv.type⟩

/-- con-leche: none — intern an `IndCaps`. -/
private def iCaps (c : IndCaps) : AM IIndCaps := do
  pure { eta := c.eta, etaCtor := ← internName c.etaCtor, etaParams := c.etaParams,
         etaFields := c.etaFields, unitlike := c.unitlike, unitParams := c.unitParams,
         ruleK := c.ruleK, sortZ := c.sortZ }

/-- con-leche: none — intern a `RecRule`. -/
private def iRule (rl : RecRule) : AM IRecRule := do
  let fire ← match rl.fire with
    | .inert => pure IRecRuleFire.inert
    | .plain => pure IRecRuleFire.plain
    | .nested lvls pins => do
      pure (.nested (← lvls.mapM internLevel) (← pins.mapM iE))
  pure { ctor := ← internName rl.ctor, nfields := rl.nfields,
         ctorParams := rl.ctorParams, fire := fire, rhs := ← iE rl.rhs,
         k := rl.k, eta := rl.eta, paramsBlind := rl.paramsBlind }

/-- con-leche: none — intern a `ProjTable`.  `IProjTable.tableName` is the
field `Arena/Env.lean` adds: the reserved name the install interned, which is
by construction `projTableName structName`. -/
private def iTbl (t : ProjTable) : AM IProjTable := do
  let sn ← internName t.structName
  pure { structName := sn, tableName := ← projTableName sn,
         levelParams := ← t.levelParams.mapM internName, numParams := t.numParams,
         ctor := ← internName t.ctor, numFields := t.numFields,
         structSort := ← internLevel t.structSort,
         bodies := ← t.bodies.mapM iE, guards := ← t.guards.mapM internLevel,
         off := t.off }

/-- con-leche: none — intern a `ConstantInfo`. -/
private def iCI : ConstantInfo → AM IConstantInfo
  | .axiomInfo cv => do pure (.axiomInfo (← iCV cv))
  | .defnInfo cv v h => do pure (.defnInfo (← iCV cv) (← iE v) h)
  | .thmInfo cv v => do pure (.thmInfo (← iCV cv) (← iE v))
  | .indInfo cv caps => do pure (.indInfo (← iCV cv) (← iCaps caps))
  | .ctorInfo cv nP nF => do pure (.ctorInfo (← iCV cv) nP nF)
  | .recInfo cv mI rP rules => do
    pure (.recInfo (← iCV cv) mI rP (← rules.mapM iRule))
  | .projInfo t => do pure (.projInfo (← iTbl t))

/-! ## Running the two checkers -/

/-- con-leche: none — the mode both checkers run at; the bridge is stated at
`.verified` (DESIGN §8.2). -/
private def MU : CheckMode := .verified

/-- con-leche: none — an arena error against a con-leche error, by KIND, the
message not compared (DESIGN §3.1).  The modelled route's declines carry the
Rust port's constant messages, which name no declaration: the twin reads no
name on those paths, as `check_member_model` does not (task #97-T2-LOCKSTEP
lane Inductives; the same ruling as `CheckerTest.lean`'s `errKindEq`).  The
arena's `CheckError` has a fourth constructor (`.native`, the store's capacity
limit), which no con-leche error can meet. -/
private def errEq : CheckError → ConLeche.CheckError → Bool
  | .notImplemented _, .notImplemented _ => true
  | .invalid _, .invalid _ => true
  | .internal _, .internal _ => true
  | _, _ => false

/-- con-leche: none — **the differential**: con-leche's `checkDecl` on
`.indDecl block nP` at `base`, against the arena's `checkIndDecl` on the
interned block at the interned `base`, over the whole outcome. -/
private def chk (base : List ConstantInfo) (block : List ConstantInfo) (nP : Nat) :
    Bool :=
  let expect : ConLeche.CheckM ConLeche.Env :=
    ConLeche.checkDecl MU (ConLeche.pureOps MU) [] ⟨base⟩ (.indDecl block nP)
  let run : AM (List IConstantInfo × Option (List IConstantInfo)) := do
    let fe := mkIFEnv ⟨← base.mapM iCI⟩
    let iblock ← block.mapM iCI
    let fe' ← ConRon.Arena.Inductives.checkIndDecl MU fe iblock nP
    -- the expected environment is interned INTO THE ARENA'S OWN STORE, after
    -- the run, so the comparison below is handle equality (module note)
    let want ← match expect with
      | .ok envE => do pure (some (← envE.consts.mapM iCI))
      | .error _ => pure none
    pure (fe'.env.consts, want)
  match (do internReservedPins; run).run (AState.init EStore.empty), expect with
  | .ok ((got, some want), _), .ok _ => got == want
  | .error a, .error b => errEq a b
  | _, _ => false

/-- con-leche: none — does con-leche ACCEPT this block?  Used to pin the
positive fixtures, so that `chk` cannot pass vacuously on two agreeing
errors. -/
private def accepts (base : List ConstantInfo) (block : List ConstantInfo)
    (nP : Nat) : Bool :=
  (ConLeche.checkDecl MU (ConLeche.pureOps MU) [] ⟨base⟩
    (.indDecl block nP) : ConLeche.CheckM ConLeche.Env).toOption.isSome

/-- con-leche: none — does con-leche's run install a projection TABLE?  The
structure-like blocks' extra install (`checkNativeTable`), whose bodies and
guard levels `chk` then compares handle for handle. -/
private def hasTable (base : List ConstantInfo) (block : List ConstantInfo)
    (nP : Nat) : Bool :=
  match (ConLeche.checkDecl MU (ConLeche.pureOps MU) [] ⟨base⟩
      (.indDecl block nP) : ConLeche.CheckM ConLeche.Env) with
  | .ok e => e.consts.any fun ci => match ci with
    | .projInfo _ => true
    | _ => false
  | .error _ => false

/-- con-leche: none — how many constants con-leche's run installs. -/
private def installed (base : List ConstantInfo) (block : List ConstantInfo)
    (nP : Nat) : Nat :=
  match (ConLeche.checkDecl MU (ConLeche.pureOps MU) [] ⟨base⟩
      (.indDecl block nP) : ConLeche.CheckM ConLeche.Env) with
  | .ok e => e.consts.length - base.length
  | .error _ => 0

/-! ## The fixture builder

A block as an elaborator exports it: the type former and the constructors as
written, the recursor GENERATED by con-leche's own `structRecTyR` /
`structRecRhsR` (module note), and one rule per constructor carrying the parse
placeholders (`ctorParams := 0`, `fire := .inert`, the three bits `false`). -/

/-- con-leche: none — a `∀` binder at the parse placeholder datum. -/
private def pi (ty b : ConLeche.Expr) : ConLeche.Expr := .forallE ty b ⟨.never⟩
/-- con-leche: none — a constant at no universe arguments. -/
private def c0 (n : ConLeche.Name) : ConLeche.Expr := .const n []
/-- con-leche: none — a fixture name. -/
private def nm (s : String) : ConLeche.Name := ConLeche.Name.anonymous.str s

/-- con-leche: none — build a block the fixpoint route recognises: the
recursor's type and rules are con-leche's own generated ones, so the fixture
is what a real export carries. -/
private def mkNativeBlock (T : ConLeche.Name) (lps : List ConLeche.Name)
    (elim : ConLeche.Name) (large : Bool) (nP nIdx : Nat) (tty : ConLeche.Expr)
    (ctors : List (ConLeche.Name × Nat × ConLeche.Expr)) :
    Option (List ConstantInfo) := do
  let n := ctors.length
  let kinds ← ctors.mapM fun c =>
    ConLeche.recCtorKinds T lps nP nIdx (⟨c.1, lps, c.2.2⟩, c.2.1)
  let ctors4 : List (ConLeche.Name × Nat × ConLeche.Expr × List Nat) :=
    List.zipWith (fun c ks => (c.1, c.2.1, c.2.2, ConLeche.recIdxOf ks)) ctors kinds
  let recName := T.str "rec"
  let rlps := if large then elim :: lps else lps
  let rlvls := rlps.map ConLeche.Level.param
  let recTy ← ConLeche.structRecTyR T lps elim large nP nIdx tty ctors4
  let rhss ← (List.range n).mapM fun j =>
    ConLeche.structRecRhsR T lps elim large nP nIdx tty ctors4 recName rlvls j
  let rules : List RecRule := List.zipWith
    (fun (c : ConLeche.Name × Nat × ConLeche.Expr) rhs =>
      ({ ctor := c.1, nfields := c.2.1, ctorParams := 0, fire := .inert,
         rhs := rhs } : RecRule))
    ctors rhss
  let rP := nP + 1 + n
  pure (.indInfo ⟨T, lps, tty⟩ {} ::
    ctors.map (fun c => .ctorInfo ⟨c.1, lps, c.2.2⟩ nP c.2.1) ++
    [.recInfo ⟨recName, rlps, recTy⟩ (rP + nIdx) rP rules])

/-- con-leche: none — an empty block stands in when a generator declines; the
`chk` on it is still a differential (both checkers see the same input). -/
private def orEmpty (o : Option (List ConstantInfo)) : List ConstantInfo :=
  o.getD []

/-! ## Fixture 1 — `N`, the `Nat` shape

con-leche's own pinned `Nat` block, renamed out of the reserved family so that
`basisPinHit` misses and the ordinary inductive route runs.  Two constructors,
one of them recursive: the fixpoint route's core case. -/

/-- con-leche: none — a fixture name. -/
private def nN : ConLeche.Name := nm "N"
/-- con-leche: none — a fixture term. -/
private def nT : ConLeche.Expr := c0 nN

/-- con-leche: none — the `N` block, generated. -/
private def natBlock : List ConstantInfo :=
  orEmpty (mkNativeBlock nN [] (nm "u") true 0 0 (.sort (.succ .zero))
    [(nN.str "zero", 0, nT), (nN.str "succ", 1, pi nT nT)])

#guard natBlock.length == 4
#guard accepts [] natBlock 0
/- the former, the two constructors and the recursor; a two-constructor block
is not structure-like, so no projection table. -/
#guard installed [] natBlock 0 == 4
#guard !hasTable [] natBlock 0
#guard chk [] natBlock 0

/-! ## Fixture 2 — `Lst α`, a parametric recursive family -/

/-- con-leche: none — a fixture name. -/
private def nL : ConLeche.Name := nm "Lst"
/-- con-leche: none — a fixture name. -/
private def uu : ConLeche.Name := nm "u"
/-- con-leche: none — a fixture term: `Sort u`. -/
private def sU : ConLeche.Expr := .sort (.param uu)
/-- con-leche: none — a fixture term: `Type u`, a sort that is provably
nonzero (`Level.isNeverZero`) — which official's `elim_only_at_universe_zero`
requires of a MULTI-constructor family with a large eliminator. -/
private def tU : ConLeche.Expr := .sort (.succ (.param uu))
/-- con-leche: none — a fixture term: `Lst α` under one binder. -/
private def lstA : ConLeche.Expr := .app (.const nL [.param uu]) (.bvar 0)

/-- con-leche: none — the `Lst` block, generated: `Lst.{u} (α : Sort u) :
Sort u` with `nil` and `cons`. -/
private def lstBlock : List ConstantInfo :=
  orEmpty (mkNativeBlock nL [uu] (nm "v") true 1 0 (pi tU tU)
    [(nL.str "nil", 0, pi tU lstA),
     (nL.str "cons", 2, pi tU (pi (.bvar 0)
       (pi (.app (.const nL [.param uu]) (.bvar 1))
         (.app (.const nL [.param uu]) (.bvar 2)))))])

#guard lstBlock.length == 4
#guard accepts [] lstBlock 1
#guard installed [] lstBlock 1 == 4
#guard !hasTable [] lstBlock 1
#guard chk [] lstBlock 1

/-! ## Fixture 3 — `Pair α β`, a two-field structure and its projections

One constructor, no index, no recursive field: official's `is_structure_like`,
so the install stores a projection TABLE (`checkNativeTable` →
`checkStructProjTable`) beside the four constants — five installs, and the
table's bodies and guard levels are compared with con-leche's. -/

/-- con-leche: none — a fixture name. -/
private def nPr : ConLeche.Name := nm "Pair"
/-- con-leche: none — a fixture term: `Pair.{u} α β` under `k` extra binders. -/
private def prAt (a b : Nat) : ConLeche.Expr :=
  .app (.app (.const nPr [.param uu]) (.bvar a)) (.bvar b)

/-- con-leche: none — the `Pair` block, generated. -/
private def pairBlock : List ConstantInfo :=
  orEmpty (mkNativeBlock nPr [uu] (nm "v") true 2 0 (pi sU (pi sU sU))
    [(nPr.str "mk", 2, pi sU (pi sU (pi (.bvar 1) (pi (.bvar 1) (prAt 3 2)))))])

#guard pairBlock.length == 3
#guard accepts [] pairBlock 2
/- four installs: the former, the constructor, the recursor and the
projection TABLE (`off = 1`, two guard levels, one body per field). -/
#guard installed [] pairBlock 2 == 4
#guard hasTable [] pairBlock 2
#guard chk [] pairBlock 2

/-! ## Fixture 4 — `Eq'`, an indexed propositional family

The subsingleton-elimination case: one constructor, an index, a `Prop` result
and a LARGE eliminator — `checkStructFieldSortsI`'s `isProp && large` arm, and
official's `elim_only_at_universe_zero` escape hatch. -/

/-- con-leche: none — a fixture name. -/
private def nEq : ConLeche.Name := nm "Eq'"
/-- con-leche: none — a fixture term: `Eq'.{u} α a` at the given binders. -/
private def eqAt (a b c : Nat) : ConLeche.Expr :=
  .app (.app (.app (.const nEq [.param uu]) (.bvar a)) (.bvar b)) (.bvar c)

/-- con-leche: none — the `Eq'` block, generated: `Eq'.{u} (α : Sort u)
(a : α) : α → Prop` with `refl`. -/
private def eqBlock : List ConstantInfo :=
  orEmpty (mkNativeBlock nEq [uu] (nm "v") true 2 1
    (pi sU (pi (.bvar 0) (pi (.bvar 1) (.sort .zero))))
    [(nEq.str "refl", 0, pi sU (pi (.bvar 0) (eqAt 1 0 0)))])

#guard eqBlock.length == 3
#guard accepts [] eqBlock 2
/- an INDEXED family is not structure-like: no projection table. -/
#guard installed [] eqBlock 2 == 3
#guard !hasTable [] eqBlock 2
#guard chk [] eqBlock 2

/-! ## Fixture 5 — `Tru`, a `Prop` with one fieldless constructor

`ruleK` at official's `is_K_target`, and unit-likeness: the capability record
this block earns is the one the differential compares field for field. -/

/-- con-leche: none — a fixture name. -/
private def nTr : ConLeche.Name := nm "Tru"

/-- con-leche: none — the `Tru` block, generated. -/
private def truBlock : List ConstantInfo :=
  orEmpty (mkNativeBlock nTr [] (nm "u") true 0 0 (.sort .zero)
    [(nTr.str "intro", 0, c0 nTr)])

#guard truBlock.length == 3
#guard accepts [] truBlock 0
#guard installed [] truBlock 0 == 4
#guard hasTable [] truBlock 0
#guard chk [] truBlock 0

/-! ## Fixture 6 — a MUTUAL block, through the modelled route

Two type formers: `sumSplit` refuses the shape outright, so no model lookup is
needed to route it (task #219) and `checkModeled` is what runs.  The `_model`
companions are in the base environment, so the block INSTALLS — the route's
member check (`checkMemberVal`: the member's type renamed under the
group-local map must be the model's) is what decides it. -/

/-- con-leche: none — a fixture name. -/
private def nA : ConLeche.Name := nm "MutA"
/-- con-leche: none — a fixture name. -/
private def nB : ConLeche.Name := nm "MutB"

/-- con-leche: none — the base environment for the mutual fixture: the two
`_model` companions, as ordinary definitions. -/
private def mutBase : List ConstantInfo :=
  [ .defnInfo ⟨nB.str "_model", [], .sort (.succ .zero)⟩ (.sort .zero) (.regular 1),
    .defnInfo ⟨nA.str "_model", [], .sort (.succ .zero)⟩ (.sort .zero) (.regular 1) ]

/-- con-leche: none — the mutual block: two type formers, no recursor. -/
private def mutBlock : List ConstantInfo :=
  [ .indInfo ⟨nA, [], .sort (.succ .zero)⟩ {},
    .indInfo ⟨nB, [], .sort (.succ .zero)⟩ {} ]

#guard accepts mutBase mutBlock 0
#guard installed mutBase mutBlock 0 == 2
#guard chk mutBase mutBlock 0

/- The same block with NO models: the modelled route declines, naming the
block — the positive statement con-leche makes when it has no model (the kind is
compared, not the message). -/
#guard !accepts [] mutBlock 0
#guard chk [] mutBlock 0

/-! ## Fixture 7 — a NESTED block, through the modelled route

Two RECURSORS: the kernel's nested→mutual specialisation mints one per mimic,
so `sumSplit` refuses this shape too and the block is the modelled route's.
With no `_model` artifacts it declines. -/

/-- con-leche: none — a fixture name. -/
private def nNest : ConLeche.Name := nm "Nest"

/-- con-leche: none — a nested-shaped block: one former, one constructor, TWO
recursor records. -/
private def nestBlock : List ConstantInfo :=
  [ .indInfo ⟨nNest, [], .sort (.succ .zero)⟩ {},
    .ctorInfo ⟨nNest.str "mk", [], c0 nNest⟩ 0 0,
    .recInfo ⟨nNest.str "rec", [], pi (c0 nNest) (.sort .zero)⟩ 1 1 [],
    .recInfo ⟨nNest.str "rec_1", [], pi (c0 nNest) (.sort .zero)⟩ 1 1 [] ]

#guard !accepts [] nestBlock 0
#guard chk [] nestBlock 0

/-! ## Fixture 8 — the declared parameter count

`indParamsOk` runs FIRST and for both routes (task #228): a block whose former
cannot peel `nP` binders is official's own reject, with the message
`checkDecl`'s arm throws. -/

#guard !accepts [] natBlock 3
#guard chk [] natBlock 3
#guard !accepts [] lstBlock 2
#guard chk [] lstBlock 2

/-! ## Fixture 9 — a non-positive occurrence

`classifyFixKinds` on the stored (normalised) constructors: official's "non
positive occurrence", a REJECT. -/

/-- con-leche: none — a fixture name. -/
private def nBad : ConLeche.Name := nm "Bad"

/-- con-leche: none — `Bad : Type` with `Bad.mk : (Bad → Bad) → Bad`. -/
private def badBlock : List ConstantInfo :=
  orEmpty (mkNativeBlock nBad [] (nm "u") true 0 0 (.sort (.succ .zero))
    [(nBad.str "mk", 1, pi (pi (c0 nBad) (c0 nBad)) (c0 nBad))])

#guard badBlock.length == 3
#guard !accepts [] badBlock 0
#guard chk [] badBlock 0

/-! ## Fixture 10 — a duplicate constructor name

`checkNative`'s front guard. -/

/-- con-leche: none — the `N` block with both constructors under one name. -/
private def dupBlock : List ConstantInfo :=
  orEmpty (mkNativeBlock nN [] (nm "u") true 0 0 (.sort (.succ .zero))
    [(nN.str "zero", 0, nT), (nN.str "zero", 1, pi nT nT)])

#guard dupBlock.length == 4
#guard !accepts [] dupBlock 0
#guard chk [] dupBlock 0

/-! ## Fixture 11 — a block whose recursor record is not the generated one

The recursor pin (task #220), thrown at the recursor stage so that the
block's TYPE and CONSTRUCTORS are checked first. -/

/-- con-leche: none — `N` with its recursor's rules dropped. -/
private def stubRecBlock : List ConstantInfo :=
  natBlock.map fun ci => match ci with
    | .recInfo cv mI rP _ => .recInfo cv mI rP []
    | c => c

#guard !accepts [] stubRecBlock 0
#guard chk [] stubRecBlock 0

/-! ## Fixture 12 — a member re-declaring a stored name

`checkConstantVal`'s duplicate guard, reached through the inductive route. -/

#guard !accepts natBlock natBlock 0
#guard chk natBlock natBlock 0

end ConRon.Arena.InductivesTest
