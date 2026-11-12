/-
# `ConRon.Arena.Core` — the checker core of (B), over handles

The twin of `ConLeche/Kernel/Core.lean`, clause for clause: the five bodies
(`whnfCore`, `whnf`, `infer`, `inferIO`, `defeq`), the helpers
they call, and the knot `coreKnot` that ties them at fuel through the
record `CoreFnsA`.  `ConLeche/Kernel/TypeChecker.lean`'s seven fueled
entry points are at the bottom of this module, beside the knot they call
(deviation 5 below).

Everything here is DESIGN §8.4's "Rust-shaped Lean": one `def` per
intended Rust function, the monad is `AM` and nothing else, fuel is an
explicit `Nat`, and the arms are INLINE — P2b's reversal (task #97b, "The
arms are INLINE, and that is a deliberate reversal") holds for this module
too, because the alternative passes the dispatcher to each arm as a
function argument and a closure is what DESIGN §3.4 forbids.

## The six systematic deviations from con-leche's clause structure

1. **`env : Env` becomes `fe : IFEnv`.**  con-leche's kernel tier reads a
   linear association list and its `Cached` tier reads the index
   (`ConLeche/Cached/CoreC.lean` takes `fe : FEnv` throughout); the arena
   has ONE environment type, the index, because DESIGN §8.3's lesson 13
   makes `find?` the only read of the environment.  Consequently every
   `…Of`/`…F` PAIR of con-leche declarations — `natLitSupported` /
   `natLitSupportedF`, `natLitStored` / `natLitStoredF`, `natOpGuard` /
   `natOpGuardF`, `andRescueSlotsOf` / `andRescueSlots` /
   `andRescueSlotsF`,
   `strLitStored` / `strLitStoredF` — collapses into
   ONE twin, which carries a `con-leche:` line per collapsed declaration.
   That is P2b's own rule for the `…Go`/`…Fast` triples, applied to the
   lookup abstraction instead of to the memo.
2. **Every structural match on a term is a `view`**, so a pure `Expr → α`
   is an `EIdx → AM α` and a walk takes an explicit `fuel : Nat`
   (`coreWalkFuel` below).  Recursions that are structural on something
   else — a binder count, an argument list, a `Nat` — take none, exactly
   as con-leche's do.
3. **Reserved names are INTERNED, not compared structurally**
   (`pin` below).  `natName`, `eqName`, … are `AM NIdx` and every
   comparison against them is handle equality, which DESIGN §8.3 licenses:
   `denoteN` is injective, so index inequality IS structural inequality.
4. **Levels are read back, not twinned** (DESIGN §8.3, lesson 4):
   `Level.isEquiv`, `Level.subst`, `Level.substPW`, `Level.zeronessOf` and
   `Level.isNeverZero` are con-leche's own, run on transient
   `ConLeche.Level` trees, with the two VERDICTS cached on the handles
   (`lvlEq?`, `lvlsEq?`).
5. **One knot, the memoized one.**  con-leche has three (`coreKnot` at
   `id`, `Cached.coreKnotI` with the memos, `coreKnotGated`); the arena's
   `coreKnot` carries the memo probes in its own slots, exactly as the
   Rust port has one knot (DESIGN §3.1, `kernel/type_checker.rs`'s module
   note).  `TypeChecker.lean`'s entries therefore live here.
6. **The memo probes are INLINE in the knot's slots**, not a higher-order
   `memoEI`: con-leche's spelling passes a getter and a setter lambda per
   table, and two closures per slot is what §3.4 rules out.  The BODIES
   stay pure of memo logic, which is the property that matters.

## The caches this module installs

`Arena/CoreState.lean` holds the record; the probes are here.  Four
entry-point memos keyed on the node alone (the depth is not in the key —
a handle carries its own typing context, DESIGN §8.3), `defeq` on the
ordered pair with the verdict, the two level-verdict tables, and the three
lazy instantiated-constant tables that replace every
`cv.type.instantiateLevelParams cv.levelParams us` in the checker.
-/
module

public import ConRon.Arena.PropRead
public import ConRon.Arena.Pins
public import ConLeche.Kernel.Basis.Names

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## Fuel for the store walks

DESIGN §8.4 asks for fuel as an explicit `Nat`.  The walks below are over
the handle DAG, so any bound above the store's node count is unreachable;
one top-level `def` (lesson 7: `Nat` literals behind a `def`) keeps the
Rust a `const u64` and keeps the elaborator from unfolding a literal into
every comparison.  `4 000 000 000` is above the representable
expression-node count (per tier, 2^30 `app` nodes and 2^26 of each of the
nine other constructors; two tiers: 3 355 443 200) and below `2^63`, so it
is one machine word. -/

/-- con-leche: none — the fuel every store walk in this module runs at;
see the section note. -/
def coreWalkFuel : Nat := 4000000000

/-! ## Reserved names, interned

DESIGN §8.3, "Exactness": names are compared for INEQUALITY throughout the
checker, and a handle comparison is that comparison because `denoteN` is
injective.  So a reserved name is interned once and compared by word.
Interning a name already in the store is a cons-table probe and appends
nothing; a reserved name absent from the store interns into whatever tier
is live and compares equal to nothing, which is the right answer and goes
with the tier.

**The `Pins` record is in the state since task #97-P6-4a** (`Arena/Pins.lean`,
`Arena/CoreState.lean`'s `Pins`): every reserved name is interned ONCE at the
driver and each of these clauses is now a field read.  Task #97c's
initialisation-order hazard — a pin read before it is filled compares against
the zero word — is killed by the table being an `Array` rather than a record
of fields: an unfilled table is EMPTY, so `pinAt` takes its bounds branch and
stops.  `pin` itself survives for the names that are NOT reserved (the
recursor and projection-function names the modeller builds). -/

/-- con-leche: none — the empty universe-argument list, off the pin table.
`us == emptyLevels` is con-leche's pattern `.const _ []`. -/
def emptyLevels : AM LsIdx := pinEmptyLevels

/-- con-leche: none — the level `0`, off the pin table: the comparand of every
`Level.isEquiv u .zero` in this module. -/
def zeroLevel : AM LIdx := pinZeroLevel

/-- con-leche: none — the expression `Sort 1` (`.sort (.succ .zero)`), off the
pin table: the pinned type of `Nat`, `String`, `Char` and `Bool`. -/
def sortOne : AM EIdx := pinSortOne

/-- con-leche: none — a level-monomorphic constant `.const n []`,
interned. -/
def constE (n : NIdx) : AM EIdx := do
  let us ← emptyLevels
  internE (.const n us)

/-! ## The level verdicts, cached

DESIGN §8.3: the level ALGORITHM runs on transient trees; what is cached
is the VERDICT, keyed on the handles.  Both tables are per-declaration and
both are dropped by `Caches.dropScratchEntries`. -/

/-- con-leche: ConLeche/Kernel/Level.lean:164-169 isEquiv — `Level.isEquiv`
at two level HANDLES, with the verdict cached on the pair.  `none` is
con-leche's fuel exhaustion and is never cached. -/
def lvlEq? (u v : LIdx) : AM (Option Bool) := do
  let s ← get
  match s.caches.lvlEqC[(u, v)]? with
  | some r => pure (some r)
  | none => do
    let lu ← readLevelM u
    let lv ← readLevelM v
    match Level.isEquiv lu lv with
    | some r => do
      let s ← get
      let mp := s.caches.lvlEqC
      let s := { s with caches := { s.caches with lvlEqC := ∅ } }
      set { s with caches := { s.caches with lvlEqC := mp.insert (u, v) r } }
      pure (some r)
    | none => pure none

/-- con-leche: ConLeche/Kernel/Level.lean:169-175 isEquivList — pairwise
`Level.isEquiv` at two universe-argument LIST handles, cached on the
pair. -/
def lvlsEq? (us vs : LsIdx) : AM (Option Bool) := do
  let s ← get
  match s.caches.lvlsEqC[(us, vs)]? with
  | some r => pure (some r)
  | none => do
    let lu ← readLevelsM us
    let lv ← readLevelsM vs
    match Level.isEquivList lu lv with
    | some r => do
      let s ← get
      let mp := s.caches.lvlsEqC
      let s := { s with caches := { s.caches with lvlsEqC := ∅ } }
      set { s with caches := { s.caches with lvlsEqC := mp.insert (us, vs) r } }
      pure (some r)
    | none => pure none

/-! ## The lazy instantiated-constant caches (DESIGN §8.3, con-leche's
arena task #26)

Every `cv.type.instantiateLevelParams cv.levelParams us` in the checker is
one of the three below.  The key is the name and the universe-argument
list — never the instantiated term, which is the point: the instantiation
is what the cache avoids computing. -/

/-- con-leche: none — a stored constant's TYPE at a universe
instantiation, memoized on `(name, levels)`.  DESIGN §8.3's
"instantiated-constant cache", `constTyAt`. -/
def constTyAt (cv : IConstantVal) (us : LsIdx) : AM EIdx := do
  let s ← get
  match s.caches.constTyC[(cv.name, us)]? with
  | some r => pure r
  | none => do
    let r ← instLPFast coreWalkFuel cv.levelParams us cv.type
    let s ← get
    let mp := s.caches.constTyC
    let s := { s with caches := { s.caches with constTyC := ∅ } }
    set { s with caches := { s.caches with constTyC := mp.insert (cv.name, us) r } }
    pure r

/-- con-leche: none — a stored definition's VALUE at a universe
instantiation, memoized on `(name, levels)` (DESIGN §8.3, `constValAt`).
The delta step's only expensive half. -/
def constValAt (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx) :
    AM EIdx := do
  let s ← get
  match s.caches.constValC[(n, us)]? with
  | some r => pure r
  | none => do
    let r ← instLPFast coreWalkFuel lps us value
    let s ← get
    let mp := s.caches.constValC
    let s := { s with caches := { s.caches with constValC := ∅ } }
    set { s with caches := { s.caches with constValC := mp.insert (n, us) r } }
    pure r

/-- con-leche: none — an iota rule's right-hand side at the recursor's
universe instantiation, memoized on `(recursor, rule constructor, levels)`
— the three data that determine it (DESIGN §8.3, `ruleRhsAt`). -/
def ruleRhsAt (recName ctor : NIdx) (lps : List NIdx) (rhs : EIdx)
    (us : LsIdx) : AM EIdx := do
  let s ← get
  match s.caches.ruleRhsC[(recName, ctor, us)]? with
  | some r => pure r
  | none => do
    let r ← instLPFast coreWalkFuel lps us rhs
    let s ← get
    let mp := s.caches.ruleRhsC
    let s := { s with caches := { s.caches with ruleRhsC := ∅ } }
    set { s with caches :=
      { s.caches with ruleRhsC := mp.insert (recName, ctor, us) r } }
    pure r

/-! ## The error -/

/-- con-leche: ConLeche/Kernel/Core.lean:50-68 unknownConstError — **the
verdict at a constant the environment does not know**: `sorryAx` is a
positively detected unsupported feature and DECLINES, every other
unresolved name is a malformed stream and REJECTS.

**No readback for the message** (task #97-P5-Core round 4's audit): the name
used to be read back with `readNameM` for the text, which the port does not do
— its message drops the interpolation (§3.1) — so at a dangling name handle
the twin failed `internal` where the port answers `Invalid`, and on a live one
it wrote `readNC`, a cache the port's run leaves alone.  Messages are never
compared (DESIGN §3.1), so the text is constant. -/
def unknownConstError (n : NIdx) : AM CheckError := do
  let sa ← pinSorryAx
  if n == sa then pure (.notImplemented "use of the sorryAx axiom")
  else pure (.invalid "unknown constant")

/-! ## The record of mutually recursive entry points -/

/-- con-leche: ConLeche/Kernel/Core.lean:112-136 CoreFns — the record of
mutually recursive core entry points, over handles.  con-leche is
polymorphic in the monad; the arena is at `AM` and nothing else (DESIGN
§8.4), so the `m` parameter is gone and the name carries an `A`. -/
structure CoreFnsA where
  /-- Head normalization without delta; the `Bool` is the official kernel's
  `cheap_proj` (`whnfCoreBody`). -/
  whnfCore : Bool → Nat → EIdx → AM EIdx
  whnf : Nat → EIdx → AM EIdx
  infer : Nat → EIdx → AM EIdx
  defeq : Nat → EIdx → EIdx → AM Bool
  /-- Definitional equality in the **eager tower**: the official kernel's
  `is_def_eq` with `m_eager_reduce` set, which `infer_app` sets for the
  comparison of an `eagerReduce _ _` argument's type with its domain
  (`defeqArg`). -/
  defeqE : Nat → EIdx → EIdx → AM Bool
  /-- Type inference at the **infer-only grade** (con-leche's task #170):
  the entry every *internal* inference call site uses. -/
  inferIO : Nat → EIdx → AM EIdx

/-- con-leche: ConLeche/Kernel/Core.lean:138-144 CoreFns.ioView — the
**io-grade view** of a core record: the record whose full-grade `infer`
slot is the io slot, so a body written against `r.infer` recurses at the io
grade when handed `r.ioView`. -/
def CoreFnsA.ioView (r : CoreFnsA) : CoreFnsA :=
  { r with infer := r.inferIO }

/-! ## The bodies' small helpers -/

/-- con-leche: ConLeche/Kernel/Core.lean:70-95 projIndexedStructLike — **could
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.projIndexedStructLike_bridge, then delete this line
official's `infer_proj` type `.proj sn i _` at a subject of type `T a⃗` where
we store no projection table for `T`?**  Only at a single-constructor
inductive `T` named by the node, applied to MORE arguments than its
parameters, at a field index below the constructor's field count: an INDEXED
structure-like type.  The cited `&&` chain, left to right. -/
def projIndexedStructLike (fe : IFEnv) (T sn : NIdx) (i nArgs : Nat) : Bool :=
  if T != sn then false
  else
    match fe.find? T with
    | some (.indInfo _ caps) =>
      match caps.ctors with
      | [c] =>
        if caps.nparams < nArgs then
          match fe.find? c with
          | some (.ctorInfo _ _ nF) => decide (i < nF)
          | _ => false
        else false
      | _ => false
    | _ => false

/-- con-leche: ConLeche/Kernel/Core.lean:97-110 projMissError — **the verdict
at a `.proj sn i _` whose subject type is headed by `T` (applied to `nArgs`
arguments) with no table entry at field `i`**: an out-of-range index at a
table; a positively detected indexed structure-like type DECLINES
(`lean4#14977`); everything else is official's reject.  `hasTable` is the
cited `(findTable? T).isSome`, read by the caller. -/
def projMissError (fe : IFEnv) (hasTable : Bool) (T sn : NIdx) (i nArgs : Nat) :
    CheckError :=
  if hasTable then .invalid "projection index out of range"
  else if projIndexedStructLike fe T sn i nArgs then
    .notImplemented "projection on an indexed structure-like type"
  else .invalid "invalid projection: not a structure-like type, or no such field"

/-- con-leche: ConLeche/Kernel/Core.lean:155-166 liftFueled — lift a
fuel-style partial result; `none` is OUR resource limit running out, so a
DECLINE (con-leche's charter item 9), never a verdict. -/
def liftFueled {α : Type} (what : String) : Option α → AM α
  | some a => pure a
  | none => fail (.notImplemented s!"resource limit: fuel exhausted: {what}")

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:37-45 Expr.ioNeutral — **is the
spine's head neither a λ nor a `let` (nor a loose bound variable)?**  The η
check's guard (`etaCert`): the head's TAG, off the handle word. -/
def ioNeutral (e : EIdx) : AM Bool := do
  let h ← getAppFn coreWalkFuel e
  let t := h.tag
  if t == ETag.lam then pure false
  else if t == ETag.letE then pure false
  else if t == ETag.bvar then pure false
  else pure true

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:48-55 isCtorApp — is the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.isCtorApp_bridge, then delete this line
expression headed by a stored constructor? -/
def isCtorApp (fe : IFEnv) (e : EIdx) : AM Bool := do
  let h ← getAppFn coreWalkFuel e
  if h.tag == ETag.const then
    match ← view h with
    | .const c _ =>
      match fe.find? c with
      | some (.ctorInfo _ _ _) => pure true
      | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:57-63 formerResSort — **a stored
inductive's result sort, read where it is needed**: the sort its stored type
ends in, `none` where the type does not end in one. -/
def formerResSort (ty : EIdx) : AM (Option LIdx) := do
  let pr ← piResult coreWalkFuel ty
  if pr.tag == ETag.sort then
    match ← viewSort pr with
    | none => failDanglingE
    | some s => pure (some s)
  else pure none

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:65-67 formerDefHeaded — a stored
former that does not show its telescope. -/
def formerDefHeaded (cv : IConstantVal) : AM Bool := do
  match ← formerResSort cv.type with
  | some _ => pure false
  | none => pure true

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:69-75 formerZ — **the family's
result-sort zero-ness datum**, read off its type (the level read back,
deviation 4); where the sort is not read, `ifAllZero []`. -/
def formerZ (cvT : IConstantVal) : AM PropWhen := do
  match ← formerResSort cvT.type with
  | some s => do
    let l ← readLevelM s
    pure (Level.zeronessOf l)
  | none => pure (.ifAllZero [])

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:77-85 formerNeverZero — is a
stored inductive's result sort, at the level instantiation `us`, provably
nonzero (official `is_never_zero`)?  The instantiated zero-ness datum is
unsatisfiable exactly where the instantiated sort is never zero. -/
def formerNeverZero (cvT : IConstantVal) (us : LsIdx) : AM Bool := do
  let z ← formerZ cvT
  let ks ← readNamesM cvT.levelParams
  let vs ← readLevelsM us
  pure (Level.substPW ks vs z).isNever

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:87-94 ctorFamily — **the family a
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.ctorFamily_bridge, then delete this line
constructor's type concludes in**: its former and its capabilities, `none`
where its type concludes in no stored inductive. -/
def ctorFamily (fe : IFEnv) (cvj : IConstantVal) :
    AM (Option (IConstantVal × IIndCaps)) := do
  let hh ← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)
  if hh.tag == ETag.const then
    match ← viewConstName hh with
    | none => failDanglingE
    | some T =>
      match fe.find? T with
      | some (.indInfo cvT caps) => pure (some (cvT, caps))
      | _ => pure none
  else pure none

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:96-115 unfoldDefinition — unfold
the (application of a) definition at the head, one step.  The stored value
is instantiated through `constValAt`, so a constant unfolded twice at the
same levels pays the substitution once. -/
def unfoldDefinition (fe : IFEnv) (e : EIdx) : AM (Option EIdx) := do
  let hh ← getAppFn coreWalkFuel e
  if hh.tag == ETag.const then
    match ← view hh with
    | .const n us =>
      match fe.find? n with
      | some (.defnInfo cv value _) => do
        let usl ← viewLs us
        if usl.length = cv.levelParams.length then do
          let v ← constValAt n cv.levelParams value us
          let args ← getAppArgs coreWalkFuel e
          let r ← mkAppN v args
          pure (some r)
        else pure none
      | _ => pure none
    | _ => pure none
  else pure none

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:117-130 unfoldableHead — may the
delta step unfold `e`'s head (the official kernel's `is_delta`)?  The
DECISION, taken before the unfolding is materialized. -/
def unfoldableHead (fe : IFEnv) (e : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel e
  if hh.tag == ETag.const then
    match ← view hh with
    | .const n us =>
      match fe.find? n with
      | some (.defnInfo cv _ _) => do
        match ← viewLsLen us with
        | none => failDanglingLs
        | some usl =>
        pure (usl == cv.levelParams.length)
      | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:132-141 headHint — the
reducibility hint of the constant at the head of `e`. -/
def headHint (fe : IFEnv) (e : EIdx) : AM ReducibilityHint := do
  let hh ← getAppFn coreWalkFuel e
  if hh.tag == ETag.const then
    match ← view hh with
    | .const n _ =>
      match fe.find? n with
      | some (.defnInfo _ _ hint) => pure hint
      | _ => pure .opaque
    | _ => pure .opaque
  else pure .opaque

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:143-152 sameConstHeads — are `a`
and `b` applications of the *same* constant (the lazy delta same-head
short-circuit)?  Both sides must actually be applications. -/
def sameConstHeads (a b : EIdx) : AM Bool := do
  if a.tag == ETag.app then
    match ← view a with
    | .app f₁ _ =>
      if b.tag == ETag.app then
        match ← view b with
        | .app f₂ _ => do
          let hh ← getAppFn coreWalkFuel f₁
          if hh.tag == ETag.const then
            match ← view hh with
            | .const n₁ _ =>
              let hh ← getAppFn coreWalkFuel f₂
              if hh.tag == ETag.const then
                match ← view hh with
                | .const n₂ _ => pure (n₁ == n₂)
                | _ => pure false
              else pure false
            | _ => pure false
          else pure false
        | _ => pure false
      else pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:154-160 natLitToConstructor — the
constructor form of a `Nat` literal, one layer. -/
def natLitToConstructor (n : Nat) : AM EIdx := do
  match n with
  | 0 => do
    let z ← pinNatZero
    constE z
  | k + 1 => do
    let s ← pinNatSucc
    let sc ← constE s
    let l ← internE (.lit (.natVal k))
    internE (.app sc l)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:162-166 natIndOk — the stored `Nat`
declaration has the expected shape. -/
def natIndOk : Option IConstantInfo → AM Bool
  | some (.indInfo cv _) => do
    let s1 ← sortOne
    pure (cv.levelParams.isEmpty && cv.type == s1)
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:168-172 natZeroOk — the stored
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.natZeroOk_bridge, then delete this line
`Nat.zero` declaration has the expected shape. -/
def natZeroOk : Option IConstantInfo → AM Bool
  | some (.ctorInfo cv _ _) => do
    let nt ← pinNat
    let nc ← constE nt
    pure (cv.levelParams.isEmpty && cv.type == nc)
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:174-182 natSuccOk — the stored
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.natSuccOk_bridge, then delete this line
`Nat.succ` declaration has the expected (annotated) shape. -/
def natSuccOk : Option IConstantInfo → AM Bool
  | some (.ctorInfo cv _ _) => do
    if !cv.levelParams.isEmpty then pure false else do
      let nt ← pinNat
      let nc ← constE nt
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE dom body => pure (dom == nc && body == nc)
        | _ => pure false
      else pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:184-189 natLitSupported
con-leche: ConLeche/Kernel/FEnv.lean:195-198 natLitSupportedF
Whether the environment supports `Nat` literals.  One twin for con-leche's
two spellings (deviation 1). -/
def natLitSupported (fe : IFEnv) : AM Bool := do
  let nt ← pinNat
  if !(← natIndOk (fe.find? nt)) then pure false else do
    let nz ← pinNatZero
    if !(← natZeroOk (fe.find? nz)) then pure false else do
      let ns ← pinNatSucc
      natSuccOk (fe.find? ns)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:191-194 natLitStored
con-leche: ConLeche/Kernel/FEnv.lean:200-202 natLitStoredF
Whether a `Nat` literal's constants are stored (presence only: what they are
is the declarations' own check, `litShapeOk`).  One twin for con-leche's two
spellings (deviation 1); the three names are pinned before the conjunction,
as `constsResolve`'s `.natVal` arm pins them. -/
def natLitStored (fe : IFEnv) : AM Bool := do
  let nt ← pinNat
  let nz ← pinNatZero
  let ns ← pinNatSucc
  pure ((fe.find? nt).isSome && (fe.find? nz).isSome && (fe.find? ns).isSome)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:196-221 Expr.constsResolve — do all
constants referenced in `e` (including inside `fvar` type annotations)
resolve in `fe`?  A full walk over the term, hence fuel; unlike the
checker's hot walks it is run once per declaration and carries no memo, as
con-leche's does not. -/
def constsResolve (fe : IFEnv) : Nat → EIdx → AM Bool
  | 0, _ => fail (.internal "fuel exhausted: constsResolve")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ | .sort _ => pure true
    | .lit (.natVal _) => do
      let nt ← pinNat
      let nz ← pinNatZero
      let ns ← pinNatSucc
      pure ((fe.find? nt).isSome && (fe.find? nz).isSome &&
        (fe.find? ns).isSome)
    | .lit (.strVal _) => do
      let nt ← pinNat
      let nz ← pinNatZero
      let ns ← pinNatSucc
      let st ← pinString
      let sl ← pinStringOfList
      let li ← pinList
      let ln ← pinListNil
      let lc ← pinListCons
      let ch ← pinChar
      let co ← pinCharOfNat
      pure ((fe.find? nt).isSome && (fe.find? nz).isSome &&
        (fe.find? ns).isSome && (fe.find? st).isSome &&
        (fe.find? sl).isSome && (fe.find? li).isSome &&
        (fe.find? ln).isSome && (fe.find? lc).isSome &&
        (fe.find? ch).isSome && (fe.find? co).isSome)
    | .const n _ => pure (fe.find? n).isSome
    | .fvar _ ty => constsResolve fe fuel ty
    | .app f a => do
      let x ← constsResolve fe fuel f
      if x then constsResolve fe fuel a else pure false
    | .lam ty body | .forallE ty body => do
      let x ← constsResolve fe fuel ty
      if x then constsResolve fe fuel body else pure false
    | .letE ty val body => do
      let x ← constsResolve fe fuel ty
      if !x then pure false else do
        let y ← constsResolve fe fuel val
        if y then constsResolve fe fuel body else pure false
    | .proj s _ sub => do
      if (fe.find? s).isSome then constsResolve fe fuel sub else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:223-228 litToCtorIfNat — convert a
`Nat`-literal major premise to constructor form, one layer. -/
def litToCtorIfNat (fe : IFEnv) (h : EIdx) : AM EIdx := do
  if h.tag == ETag.lit then
    match ← view h with
    | .lit (.natVal n) => do
      if ← natLitStored fe then natLitToConstructor n else pure h
    | _ => pure h
  else pure h

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:230-235 rawNatLit? — a `Nat`
literal reading of a whnf'd expression (the official kernel's
`rawNatLitExt?`). -/
def rawNatLit? (h : EIdx) : AM (Option Nat) := do
  match ← view h with
  | .lit (.natVal n) => pure (some n)
  | .const c us => do
    let e ← emptyLevels
    let nz ← pinNatZero
    pure (if c == nz && us == e then some 0 else none)
  | _ => pure none

/-! ## String literals -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:250-261 strLitToConstructor — the
`List.cons` spine of a string literal's constructor form.  con-leche writes
`s.toList.foldr (init := nil) fun c e => …`; DESIGN §3.4 turns the closure
into this explicit recursion over the character list (P2b's closure audit,
same rule). -/
def strLitConsSpine (cons ofNat nilE : EIdx) : List Char → AM EIdx
  | [] => pure nilE
  | c :: cs => do
    let rest ← strLitConsSpine cons ofNat nilE cs
    let lit ← internE (.lit (.natVal c.toNat))
    let ch ← internE (.app ofNat lit)
    let f ← internE (.app cons ch)
    internE (.app f rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:250-261 strLitToConstructor — the
constructor form of a `String` literal: `String.ofList (List.cons.{0} Char
(Char.ofNat (lit c₁)) (… (List.nil.{0} Char)))`. -/
def strLitToConstructor (s : String) : AM EIdx := do
  let z ← zeroLevel
  let zs ← internLsNode [z]
  let chN ← pinChar
  let chC ← constE chN
  let lnN ← pinListNil
  let ln ← internE (.const lnN zs)
  let nilE ← internE (.app ln chC)
  let lcN ← pinListCons
  let lc ← internE (.const lcN zs)
  let cons ← internE (.app lc chC)
  let coN ← pinCharOfNat
  let ofNat ← constE coN
  let spine ← strLitConsSpine cons ofNat nilE s.toList
  let slN ← pinStringOfList
  let sl ← constE slN
  internE (.app sl spine)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:263-269 stringTyOk — the stored
`String` declaration has the expected shape. -/
def stringTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv := ci.toConstantVal
    let s1 ← sortOne
    pure (cv.levelParams.isEmpty && cv.type == s1)
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:271-277 charTyOk — the stored
`Char` declaration has the expected shape. -/
def charTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv := ci.toConstantVal
    let s1 ← sortOne
    pure (cv.levelParams.isEmpty && cv.type == s1)
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:279-290 listTyOk — the stored
`List` declaration has the expected (annotated) shape `List.{p} : Type p →
Type p`. -/
def listTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv := ci.toConstantVal
    match cv.levelParams with
    | [p] => do
      let pl ← internLNode (.param p)
      let sp ← internLNode (.succ pl)
      let sort ← internE (.sort sp)
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE d b => pure (d == sort && b == sort)
        | _ => pure false
      else pure false
    | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:292-303 listNilTyOk — the stored
`List.nil` declaration has the expected (annotated) shape. -/
def listNilTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv := ci.toConstantVal
    match cv.levelParams with
    | [p] => do
      let pl ← internLNode (.param p)
      let sp ← internLNode (.succ pl)
      let sort ← internE (.sort sp)
      let ps ← internLsNode [pl]
      let li ← pinList
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE d b => do
          if d != sort then pure false else
          if b.tag == ETag.app then
            match ← view b with
            | .app f a =>
              if f.tag == ETag.const then
                match ← view f with
                | .const l1 us1 =>
                  if a.tag == ETag.bvar then
                    match ← view a with
                    | .bvar 0 => pure (l1 == li && us1 == ps)
                    | _ => pure false
                  else pure false
                | _ => pure false
              else pure false
            | _ => pure false
          else pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:305-321 listConsTyOk — the stored
`List.cons` declaration has the expected (annotated) shape. -/
def listConsTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv := ci.toConstantVal
    match cv.levelParams with
    | [p] => do
      let pl ← internLNode (.param p)
      let sp ← internLNode (.succ pl)
      let sort ← internE (.sort sp)
      let ps ← internLsNode [pl]
      let li ← pinList
      let b0 ← internE (.bvar 0)
      let b1 ← internE (.bvar 1)
      let b2 ← internE (.bvar 2)
      let l1 ← internE (.const li ps)
      let dom3 ← internE (.app l1 b1)
      let cod3 ← internE (.app l1 b2)
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE d1 r1 => do
          if d1 != sort then pure false else
          if r1.tag == ETag.forallE then
            match ← view r1 with
            | .forallE d2 r2 => do
              if d2 != b0 then pure false else
              if r2.tag == ETag.forallE then
                match ← view r2 with
                | .forallE d3 c3 => pure (d3 == dom3 && c3 == cod3)
                | _ => pure false
              else pure false
            | _ => pure false
          else pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:323-332 charOfNatTyOk — the stored
`Char.ofNat` declaration has the expected (annotated) shape `Nat → Char`. -/
def charOfNatTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv := ci.toConstantVal
    if !cv.levelParams.isEmpty then pure false else do
      let nt ← pinNat
      let nc ← constE nt
      let ch ← pinChar
      let cc ← constE ch
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE d b => pure (d == nc && b == cc)
        | _ => pure false
      else pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:334-344 stringOfListTyOk — the
stored `String.ofList` declaration has the expected (annotated) shape
`List.{0} Char → String`. -/
def stringOfListTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv := ci.toConstantVal
    if !cv.levelParams.isEmpty then pure false else do
      let z ← zeroLevel
      let zs ← internLsNode [z]
      let li ← pinList
      let lc ← internE (.const li zs)
      let ch ← pinChar
      let cc ← constE ch
      let dom ← internE (.app lc cc)
      let st ← pinString
      let sc ← constE st
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE d b => pure (d == dom && b == sc)
        | _ => pure false
      else pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:362-367 strLitStored
con-leche: ConLeche/Kernel/FEnv.lean:204-209 strLitStoredF
Whether a `String` literal's constants are stored: `natLitStored` and the
seven string-support names, by presence only (deviation 1).  The seven are
pinned before their conjunction, as `constsResolve`'s `.strVal` arm pins
them. -/
def strLitStored (fe : IFEnv) : AM Bool := do
  if !(← natLitStored fe) then pure false else do
    let st ← pinString
    let sl ← pinStringOfList
    let li ← pinList
    let ln ← pinListNil
    let lc ← pinListCons
    let ch ← pinChar
    let co ← pinCharOfNat
    pure ((fe.find? st).isSome && (fe.find? sl).isSome && (fe.find? li).isSome &&
      (fe.find? ln).isSome && (fe.find? lc).isSome && (fe.find? ch).isSome &&
      (fe.find? co).isSome)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:369-385 litShapeOk — **the shape a
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.litShapeOk_bridge, then delete this line
declaration at a literal's name must have**, its level parameters and type,
checked at the declaration; any other name passes.  A declaration check cannot
show a kind, so the three `Nat` names are read at the kinds their guards ask
for.  The cited `if`-chain, each name pinned only when the chain reaches it. -/
def litShapeOk (c : IConstantInfo) : AM Bool := do
  let n := c.name
  if n == (← pinNat) then natIndOk (some (.indInfo c.toConstantVal {}))
  else if n == (← pinNatZero) then natZeroOk (some (.ctorInfo c.toConstantVal 0 0))
  else if n == (← pinNatSucc) then natSuccOk (some (.ctorInfo c.toConstantVal 0 1))
  else if n == (← pinString) then stringTyOk (some c)
  else if n == (← pinStringOfList) then stringOfListTyOk (some c)
  else if n == (← pinList) then listTyOk (some c)
  else if n == (← pinListNil) then listNilTyOk (some c)
  else if n == (← pinListCons) then listConsTyOk (some c)
  else if n == (← pinChar) then charTyOk (some c)
  else if n == (← pinCharOfNat) then charOfNatTyOk (some c)
  else pure true

/-! ## Structural-`Nat` literal acceleration

con-leche's certified fast path (`Core.lean:514-863`): an operation
participates only when its defining recurrence equations hold by
definitional equality — checked once, at its check, so *presence in the store
is the certificate*.  The sixteen reserved names are interned here exactly
as the literal guards' are. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:415 natPredName -/
def natPredName : AM NIdx := pinNatPred
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:416 natAddName -/
def natAddName : AM NIdx := pinNatAdd
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:417 natSubName -/
def natSubName : AM NIdx := pinNatSub
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:418 natMulName -/
def natMulName : AM NIdx := pinNatMul
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:419 natPowName -/
def natPowName : AM NIdx := pinNatPow
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:420 natBeqName -/
def natBeqName : AM NIdx := pinNatBeq
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:421 natBleName -/
def natBleName : AM NIdx := pinNatBle
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:422 natDivName -/
def natDivName : AM NIdx := pinNatDiv
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:423 natModName -/
def natModName : AM NIdx := pinNatMod
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:424 natGcdName -/
def natGcdName : AM NIdx := pinNatGcd
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:425 natLandName -/
def natLandName : AM NIdx := pinNatLand
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:426 natLorName -/
def natLorName : AM NIdx := pinNatLor
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:427 natXorName -/
def natXorName : AM NIdx := pinNatXor
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:428 natShiftLeftName -/
def natShiftLeftName : AM NIdx := pinNatShiftLeft
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:429 natShiftRightName -/
def natShiftRightName : AM NIdx := pinNatShiftRight
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:430 boolName -/
def boolName : AM NIdx := pinBool
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:442 boolTrueName -/
def boolTrueName : AM NIdx := pinBoolTrue
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:443 boolFalseName -/
def boolFalseName : AM NIdx := pinBoolFalse
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:432-434 eagerReduceName -/
def eagerReduceName : AM NIdx := pinEagerReduce

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:445-450 Expr.isBoolTrue — is `e` the
constant `Bool.true` (the official kernel's `is_constant(e, Bool.true)`):
the name, no universe levels. -/
def isBoolTrue (h : EIdx) : AM Bool := do
  if h.tag == ETag.const then
    match ← view h with
    | .const c us => do
      let el ← emptyLevels
      if us != el then pure false else do
        let bt ← boolTrueName
        pure (c == bt)
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:436-441 Expr.isEagerReduce — is
`e` of the form `eagerReduce _ _` (official `is_eager_reduce`): the head
constant `eagerReduce`, exactly two arguments, any universe levels. -/
def isEagerReduce (h : EIdx) : AM Bool := do
  if h.tag == ETag.app then
    match ← viewApp h with
    | none => failDanglingE
    | some (f, _) =>
      if f.tag == ETag.app then
        match ← viewApp f with
        | none => failDanglingE
        | some (g, _) =>
          if g.tag == ETag.const then
            match ← viewConst g with
            | none => failDanglingE
            | some (c, _) => do
              let er ← eagerReduceName
              pure (c == er)
          else pure false
      else pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-460 natOpNames — the certified
structural-`Nat` operations. -/
def natOpNames : AM (List NIdx) := do
  let a ← natPredName; let b ← natAddName; let c ← natSubName
  let d ← natMulName; let e ← natPowName; let f ← natBeqName
  let g ← natBleName
  pure [a, b, c, d, e, f, g]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:462-475 natDivModNames — the
WF-recursive operations with a *pinned-declaration* certified fast path. -/
def natDivModNames : AM (List NIdx) := do
  let a ← natDivName; let b ← natModName; let c ← natGcdName
  let d ← natLandName; let e ← natLorName; let f ← natXorName
  let g ← natShiftLeftName; let h ← natShiftRightName
  pure [a, b, c, d, e, f, g, h]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:477-481 natOpName — **the
certified operations' names**: the fast path fires on them by name, so only a
definition may take one (`checkConstantVal`, `reservedRecName`). -/
def natOpName (n : NIdx) : AM Bool := do
  let ops ← natOpNames
  if ops.contains n then pure true else do
    let dms ← natDivModNames
    pure (dms.contains n)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:522-545 natOpDeps — the operations
(transitively) involved in `c`'s recurrences. -/
def natOpDeps (c : NIdx) : AM (List NIdx) := do
  let pr ← natPredName; let ad ← natAddName; let su ← natSubName
  let mu ← natMulName; let po ← natPowName; let be ← natBeqName
  let bl ← natBleName; let di ← natDivName; let mo ← natModName
  let gc ← natGcdName; let la ← natLandName; let lo ← natLorName
  let xo ← natXorName; let sl ← natShiftLeftName; let sr ← natShiftRightName
  if c == pr then pure [pr]
  else if c == ad then pure [ad]
  else if c == su then pure [pr, su]
  else if c == mu then pure [ad, mu]
  else if c == po then pure [ad, mu, po]
  else if c == be then pure [be]
  else if c == bl then pure [bl]
  else if c == di then pure [pr, su, bl, di]
  else if c == mo then pure [pr, su, bl, mo]
  else if c == gc then pure [bl, mo, gc]
  else if c == la then pure [ad, mu, bl, di, mo, la]
  else if c == lo then pure [ad, su, mu, bl, di, mo, lo]
  else if c == xo then pure [ad, mu, bl, di, mo, xo]
  else if c == sl then pure [su, mu, bl, sl]
  else if c == sr then pure [su, bl, di, sr]
  else pure []

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations — `ap1 n a`,
one of the equation builder's three local lambdas.  DESIGN §3.4 forbids the
closure, so each is a named `def`. -/
def natAp1 (n : NIdx) (a : EIdx) : AM EIdx := do
  let f ← constE n
  internE (.app f a)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations — `ap2 n a b`. -/
def natAp2 (n : NIdx) (a b : EIdx) : AM EIdx := do
  let f ← natAp1 n a
  internE (.app f b)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations — the
defining recurrence equations of a structural-`Nat` operation, over
constructor forms with free variables `d`, `d + 1` (binder-free, so the
equation sides carry no annotations). -/
def natOpEquations (d : Nat) (c : NIdx) : AM (List (EIdx × EIdx)) := do
  let nN ← pinNat
  let natTy ← constE nN
  let x ← internE (.fvar d natTy)
  let y ← internE (.fvar (d + 1) natTy)
  let zN ← pinNatZero
  let z ← constE zN
  let sN ← pinNatSucc
  let sx ← natAp1 sN x
  let sy ← natAp1 sN y
  let bT ← constE (← boolTrueName)
  let bF ← constE (← boolFalseName)
  let pr ← natPredName; let ad ← natAddName; let su ← natSubName
  let mu ← natMulName; let po ← natPowName; let be ← natBeqName
  let bl ← natBleName
  -- the Rust reads all fifteen operation pins at once (`nat_op_pins`), so the
  -- twin does too: a pin read can fail (task #97-T2-LOCKSTEP lane Checker
  -- DeclCheck)
  let _di ← natDivName; let _mo ← natModName; let _gc ← natGcdName
  let _la ← natLandName; let _lo ← natLorName; let _xo ← natXorName
  let _sl ← natShiftLeftName; let _sr ← natShiftRightName
  if c == pr then do
    let l1 ← natAp1 c z
    let l2 ← natAp1 c sx
    pure [(l1, z), (l2, x)]
  else if c == ad then do
    let l1 ← natAp2 c x z
    let l2 ← natAp2 c x sy
    let r2 ← natAp1 sN (← natAp2 c x y)
    pure [(l1, x), (l2, r2)]
  else if c == su then do
    let l1 ← natAp2 c x z
    let l2 ← natAp2 c x sy
    let r2 ← natAp1 pr (← natAp2 c x y)
    pure [(l1, x), (l2, r2)]
  else if c == mu then do
    let l1 ← natAp2 c x z
    let l2 ← natAp2 c x sy
    let r2 ← natAp2 ad (← natAp2 c x y) x
    pure [(l1, z), (l2, r2)]
  else if c == po then do
    let l1 ← natAp2 c x z
    let sz ← natAp1 sN z
    let l2 ← natAp2 c x sy
    let r2 ← natAp2 mu (← natAp2 c x y) x
    pure [(l1, sz), (l2, r2)]
  else if c == be then do
    let l1 ← natAp2 c z z
    let l2 ← natAp2 c z sy
    let l3 ← natAp2 c sx z
    let l4 ← natAp2 c sx sy
    let r4 ← natAp2 c x y
    pure [(l1, bT), (l2, bF), (l3, bF), (l4, r4)]
  else if c == bl then do
    let l1 ← natAp2 c z y
    let l2 ← natAp2 c sx z
    let l3 ← natAp2 c sx sy
    let r3 ← natAp2 c x y
    pure [(l1, bT), (l2, bF), (l3, r3)]
  else pure []

/-- con-leche: ConLeche/Cached/StateC.lean:156-159 natSizeBytes — the official
kernel's size of a numeral in bytes (`lean_nat_size_in_bytes`): 8 bytes per
started 64 bits, and at least 8. -/
def natSizeBytes (n : Nat) : Nat := 8 * (n.log2 / 64 + 1)

/-- con-leche: ConLeche/Cached/StateC.lean:156-159 natSizeBytes
con-leche: ConLeche/Cached/StateC.lean:326-330 maxNatSizeM — whether the numeral
`n` is above the run's maximum `Nat` size, `natSizeBytes n > maxNatSize`. -/
def natSizeRefused (n : Nat) : AM Bool := do
  let m ← maxNatSizeM
  pure (decide (natSizeBytes n > m))

/-- con-leche: ConLeche/Cached/StateC.lean:254-263 natResultRefused
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.litNatSized_bridge, then delete this line
con-leche: ConLeche/Cached/StateC.lean:165-168 natNumeralTooBig
con-leche: ConLeche/Cached/CoreC.lean:403-457 reduceNatI — a computed numeral,
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.litNatSized_bridge, then delete this line
refused above the run's maximum `Nat` size (the cited `natNumeralTooBig`),
otherwise interned. -/
def litNatSized (n : Nat) : AM (Option EIdx) := do
  if ← natSizeRefused n then
    fail (.invalid "the kernel refused a `Nat` numeral because its size exceeds the maximum; raise it with --max-nat-size")
  else do
    let x ← internE (.lit (.natVal n))
    pure (some x)

/-- con-leche: ConLeche/Cached/StateC.lean:234-252 natOpRefusal — `a ^ b` has
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.powRefused_bridge, then delete this line
at most `natSizeBytes a * b` bytes, and a base `≤ 1` gives `0` or `1`. -/
def powRefused (a b : Nat) : AM Bool := do
  if a ≤ 1 then pure false
  else if b = 0 then pure false
  else do
    let m ← maxNatSizeM
    pure (decide (natSizeBytes a > m / b))

/-- con-leche: ConLeche/Cached/StateC.lean:234-252 natOpRefusal
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.powGuard_bridge, then delete this line
con-leche: ConLeche/Cached/StateC.lean:161-163 natCountMax
con-leche: ConLeche/Cached/StateC.lean:170-173 natCountTooBig — the cited
`Nat.pow` clause: an exponent above `natCountMax` is refused whatever the base,
and so is a result above the maximum size (`powRefused`). -/
def powGuard (a b : Nat) : AM Unit := do
  if b > 4294967295 then
    fail (.invalid "the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer")
  else if ← powRefused a b then
    fail (.invalid "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size; raise it with --max-nat-size")
  else pure ()

/-- con-leche: ConLeche/Cached/StateC.lean:234-252 natOpRefusal —
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.shiftLeftRefused_bridge, then delete this line
`natSizeBytes a + b / 8 + 1 > maxNatSize`, the `/ 8` a shift. -/
def shiftLeftRefused (a b : Nat) : AM Bool := do
  let m ← maxNatSizeM
  pure (decide (m < natSizeBytes a + Nat.shiftRight b 3 + 1))

/-- con-leche: ConLeche/Cached/StateC.lean:234-252 natOpRefusal — the cited
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.shiftLeftGuard_bridge, then delete this line
`Nat.shiftLeft` clause: `0 <<< b = 0` computes; otherwise an amount above
`natCountMax` is refused, and so is a result above the maximum size
(`shiftLeftRefused`). -/
def shiftLeftGuard (a b : Nat) : AM Unit := do
  if a = 0 then pure ()
  else if b > 4294967295 then
    fail (.invalid "the kernel refused to evaluate `Nat.shiftLeft` because its second argument does not fit in a 32-bit unsigned integer")
  else if ← shiftLeftRefused a b then
    fail (.invalid "the kernel refused a `Nat` numeral because its size exceeds the maximum; raise it with --max-nat-size")
  else pure ()

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:578-603 natOpResult
con-leche: ConLeche/Cached/StateC.lean:234-252 natOpRefusal
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.natOpResult_bridge, then delete this line
con-leche: ConLeche/Cached/StateC.lean:254-263 natResultRefused
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.natOpResult_bridge, then delete this line
con-leche: ConLeche/Cached/CoreC.lean:403-457 reduceNatI — the reduct of op `c`
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.natOpResult_bridge, then delete this line
on literal arguments (`pred` ignores the second slot).  `ron::Nat` is
con-leche's `Nat` here, and a literal is a `Literal` value in a `lit` node.
The computation is the cited one at any size; the run's maximum `Nat` size
(con-leche's cached `reduceNatI`) refuses `pow` and `shiftLeft` before
computing (`powGuard`, `shiftLeftGuard`: the cited `natOpRefusal`) and an
`add`, `sub` or `mul` result after it (`litNatSized`: `natResultRefused`). -/
def natOpResult (c : NIdx) (a b : Nat) : AM (Option EIdx) := do
  let pr ← natPredName; let ad ← natAddName; let su ← natSubName
  let mu ← natMulName; let po ← natPowName; let be ← natBeqName
  let bl ← natBleName; let di ← natDivName; let mo ← natModName
  let gc ← natGcdName; let la ← natLandName; let lo ← natLorName
  let xo ← natXorName; let sl ← natShiftLeftName; let sr ← natShiftRightName
  if c == pr then do let x ← internE (.lit (.natVal (a - 1))); pure (some x)
  else if c == ad then litNatSized (a + b)
  else if c == su then litNatSized (a - b)
  else if c == mu then litNatSized (a * b)
  else if c == po then do
    powGuard a b
    let x ← internE (.lit (.natVal (a ^ b))); pure (some x)
  else if c == di then do let x ← internE (.lit (.natVal (a / b))); pure (some x)
  else if c == mo then do let x ← internE (.lit (.natVal (a % b))); pure (some x)
  else if c == gc then do
    let x ← internE (.lit (.natVal (Nat.gcd a b))); pure (some x)
  else if c == la then do
    let x ← internE (.lit (.natVal (Nat.land a b))); pure (some x)
  else if c == lo then do
    let x ← internE (.lit (.natVal (Nat.lor a b))); pure (some x)
  else if c == xo then do
    let x ← internE (.lit (.natVal (Nat.xor a b))); pure (some x)
  else if c == sl then do
    shiftLeftGuard a b
    let x ← internE (.lit (.natVal (Nat.shiftLeft a b))); pure (some x)
  else if c == sr then do
    let x ← internE (.lit (.natVal (Nat.shiftRight a b))); pure (some x)
  else if c == be then do
    let n ← if a = b then boolTrueName else boolFalseName
    let x ← constE n
    pure (some x)
  else if c == bl then do
    let n ← if a <= b then boolTrueName else boolFalseName
    let x ← constE n
    pure (some x)
  else pure none

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:605-626 natOpGuard — the dependency
half of the guard.  con-leche writes `(natOpDeps c).all (fun n => …)`;
DESIGN §3.4's rule for a `List` walk is a named helper, so this is one. -/
def natOpDepsStored (fe : IFEnv) : List NIdx → AM Bool
  | [] => pure true
  | n :: ns =>
    match fe.find? n with
    | some (.defnInfo cv _ _) =>
      if cv.levelParams.isEmpty then natOpDepsStored fe ns else pure false
    | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:605-626 natOpGuard — a stored
`Bool` constructor's conjunct, `ci.toConstantVal.levelParams.isEmpty &&
ci.toConstantVal.type == .const boolName []`: level-free, at the type `Bool`
itself (con-leche's task #342).  The `&&` short-circuits as con-leche's does;
the type test is handle equality against the interned `Bool` (exactness). -/
def boolCtorOk (ci : IConstantInfo) : AM Bool := do
  let cv := ci.toConstantVal
  if cv.levelParams.isEmpty then do
    let b ← constE (← boolName)
    pure (cv.type == b)
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:605-626 natOpGuard
con-leche: ConLeche/Kernel/FEnv.lean:211-226 natOpGuardF
Stored-constant guards for op `c`: the `Nat` basis, every dependency stored
as a definition, and (for the `Bool`-valued ops and the `ble`-guarded
`div`/`mod`) the `Bool` constructors stored, level-free, at the type `Bool`
itself (`boolCtorOk`). -/
def natOpGuard (fe : IFEnv) (c : NIdx) : AM Bool := do
  if !(← natLitSupported fe) then pure false else do
    let deps ← natOpDeps c
    if !(← natOpDepsStored fe deps) then pure false else do
      let be ← natBeqName
      let bl ← natBleName
      let dm ← natDivModNames
      if c == be || c == bl || dm.contains c then do
        let bt ← boolTrueName
        let okT ←
          match fe.find? bt with
          | some ci => boolCtorOk ci
          | none => pure false
        if !okT then pure false else do
          let bf ← boolFalseName
          match fe.find? bf with
          | some ci => boolCtorOk ci
          | none => pure false
      else pure true

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:630-640 natOpWfNames — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.natOpWfNames_bridge, then delete this line
pin-certified WF-recursive `Nat` operations, as a *safety net*. -/
def natOpWfNames : AM (List NIdx) := do
  let a ← natDivName; let b ← natModName; let c ← natGcdName
  let d ← natLandName; let e ← natLorName; let f ← natXorName
  let g ← natShiftLeftName; let h ← natShiftRightName
  pure [a, b, c, d, e, f, g, h]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:628-634 Expr.substConst0 —
substitute the level-monomorphic constant `n` by `r` through an application
spine (the equation sides are binder-free, so only `app` recurses). -/
def substConst0 (n : NIdx) (r : EIdx) : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: substConst0")
  | fuel + 1, h => do
    match ← view h with
    | .const c us => do
      let el ← emptyLevels
      if c == n && us == el then pure r else pure h
    | .app f a => do
      let f' ← substConst0 n r fuel f
      let a' ← substConst0 n r fuel a
      internE (.app f' a')
    | _ => pure h

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:636-652 Expr.substConstAll —
substitute the level-monomorphic constant `n` by the *closed* term `r`
everywhere, including under binders.  `fvar` annotations are not entered. -/
def substConstAll (n : NIdx) (r : EIdx) : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: substConstAll")
  | fuel + 1, h => do
    match ← view h with
    | .const c us => do
      let el ← emptyLevels
      if c == n && us == el then pure r else pure h
    | .app f a => do
      let f' ← substConstAll n r fuel f
      let a' ← substConstAll n r fuel a
      internE (.app f' a')
    | .lam ty b => do
      let ty' ← substConstAll n r fuel ty
      let b' ← substConstAll n r fuel b
      internLamE ty' b'
    | .forallE ty b => do
      let ty' ← substConstAll n r fuel ty
      let b' ← substConstAll n r fuel b
      internForallEE ty' b'
    | .letE ty v b => do
      let ty' ← substConstAll n r fuel ty
      let v' ← substConstAll n r fuel v
      let b' ← substConstAll n r fuel b
      internE (.letE ty' v' b')
    | .proj s i e => do
      let e' ← substConstAll n r fuel e
      internE (.proj s i e')
    | _ => pure h

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:654-664 natOpCod — the pinned
codomain of a structural-`Nat` operation: `Bool` for the comparisons, `Nat`
otherwise. -/
def natOpCod (fe : IFEnv) (c : NIdx) (e : EIdx) : AM Bool := do
  let be ← natBeqName
  let bl ← natBleName
  if c == be || c == bl then do
    let bn ← boolName
    let bc ← constE bn
    if e != bc then pure false else
      match fe.find? bn with
      | some ci => do
        let cv := ci.toConstantVal
        let s1 ← sortOne
        pure (cv.levelParams.isEmpty && cv.type == s1)
      | none => pure false
  else do
    let nn ← pinNat
    let nc ← constE nn
    pure (e == nc)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:666-681 natOpTyPinned — the pinned
type of a certified `Nat` operation: `Nat → Nat` for the unary `pred`,
`Nat → Nat → Nat` for the arithmetic operations, `Nat → Nat → Bool` for the
comparisons. -/
def natOpTyPinned (fe : IFEnv) (c : NIdx) (ty : EIdx) : AM Bool := do
  let nn ← pinNat
  let nc ← constE nn
  let pr ← natPredName
  if c == pr then do
    if ty.tag == ETag.forallE then
      match ← view ty with
      | .forallE dom body =>
        if dom == nc then natOpCod fe c body else pure false
      | _ => pure false
    else pure false
  else do
    if ty.tag == ETag.forallE then
      match ← view ty with
      | .forallE dom rest => do
        if rest.tag == ETag.forallE then
          match ← view rest with
          | .forallE dom2 body =>
            if dom == nc && dom2 == nc then natOpCod fe c body else pure false
          | _ => pure false
        else pure false
      | _ => pure false
    else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:683-689 natOpStoredOk — op `n` is
stored as a level-monomorphic definition with the pinned type. -/
def natOpStoredOk (fe : IFEnv) (n : NIdx) : AM Bool := do
  match fe.find? n with
  | some (.defnInfo cv _ _) =>
    if cv.levelParams.isEmpty then natOpTyPinned fe n cv.type else pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:168-209 reduceNat — the binary
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.natBinOpName_bridge, then delete this line
literal acceleration's name test.  con-leche writes a fourteen-way disjunction
inline; over handles the comparands have to be interned first, so the
chain is its own `def` and the caller reads one `Bool`. -/
def natBinOpName (c : NIdx) : AM Bool := do
  let ad ← natAddName; let su ← natSubName; let mu ← natMulName
  let po ← natPowName; let be ← natBeqName; let bl ← natBleName
  let di ← natDivName; let mo ← natModName; let gc ← natGcdName
  let la ← natLandName; let lo ← natLorName; let xo ← natXorName
  let sl ← natShiftLeftName; let sr ← natShiftRightName
  pure (c == ad || c == su || c == mu || c == po || c == be || c == bl ||
    c == di || c == mo || c == gc || c == la || c == lo || c == xo ||
    c == sl || c == sr)

/-- con-leche: ConLeche/Kernel/Core.lean:168-209 reduceNat — literal
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.reduceNat_bridge, then delete this line
acceleration (the official kernel's `reduceNat`, run in the `whnf` loop
*before* delta-unfolding).  The divergence audit's D15 is preserved: the
FIRST argument is head-normalised and, unless it is a literal, the step
fails WITHOUT touching the second. -/
def reduceNat (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e : EIdx) :
    AM (Option EIdx) := do
  if e.tag == ETag.app then
    match ← view e with
    | .app f b => do
      match ← view f with
      | .const c us => do
        -- con-leche's `.app (.const c []) a`: `b` is its `a`
        let el ← emptyLevels
        if us != el then pure none else do
          let ns ← pinNatSucc
          if c == ns && (← natLitStored fe) then do
            match ← rawNatLit? (← r.whnf depth b) with
            | some n => litNatSized (n + 1)
            | none => pure none
          else pure none
      | .app g a => do
        -- con-leche's `.app (.app (.const c []) a) b`
        if g.tag == ETag.const then
          match ← view g with
          | .const c us => do
            let el ← emptyLevels
            if us != el then pure none else do
              if ← natBinOpName c then do
                match ← rawNatLit? (← r.whnf depth a) with
                | some n₁ => do
                  match ← rawNatLit? (← r.whnf depth b) with
                  | some n₂ => natOpResult c n₁ n₂
                  | none => pure none
                | none => pure none
              else do
                let wf ← natOpWfNames
                if wf.contains c then do
                  match ← rawNatLit? (← r.whnf depth a) with
                  | some _ => do
                    match ← rawNatLit? (← r.whnf depth b) with
                    | some _ => do
                      -- no readback for the message: the port has none
                      -- (round 4's audit)
                      fail (.notImplemented "native Nat computation on literals")
                    | none => pure none
                  | none => pure none
                else pure none
          | _ => pure none
        else pure none
      | _ => pure none
    | _ => pure none
  else pure none

/-! ## The certification helpers

con-leche's `Core.lean`:865-1310.  Every one of these recurses structurally
on a LIST (an argument spine, a slot index list), so none of them takes
fuel; what they call into the store does. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:459-483 iotaCertsFullIAux — certify a
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.iotaCertsFullAux_bridge, then delete this line
spine against a constructor telescope at ι's case 3 (con-leche's task #342
L10): each argument's FULL-grade inferred type is defeq to the corresponding
(instantiated) domain.  Every slot is certified.

**Batched** (task #97-P6-9), which is con-leche's own CACHED-tier clause: the
chained spec runs one `instantiate1` per slot down the telescope; this carries
the pending substitutions in an accumulator and opens each domain in ONE
`instantiateList`.

The accumulator is an `Array` in PUSH order (task #97-P6-15). -/
def iotaCertsFullAux (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (h : EIdx) (acc : Array EIdx) (args : Array EIdx) (i : Nat) : AM Bool := do
  if hi : i < args.size then do
    match ← view h with
    | .forallE ty body => do
      let arg := args[i]
      let ty2 ← instantiateListFast coreWalkFuel ty acc 0
      let ta ← r.infer depth arg
      if ← r.defeq depth ta ty2 then
        iotaCertsFullAux r fe depth body (acc.push arg) args (i + 1)
      else pure false
    | .bvar _ => do
      -- The telescope ran out of syntactic binders with a pending
      -- substitution: flush it and look again.  This is `iotaCertsFullIAux`'s
      -- own re-entry clause and is why the measure is lexicographic.
      if acc.size = 0 then pure false
      else do
        let ty2 ← instantiateListFast coreWalkFuel h acc 0
        iotaCertsFullAux r fe depth ty2 #[] args i
    | _ => pure false
  else pure true
termination_by (args.size - i, acc.size)

/-- con-leche: ConLeche/Kernel/Core.lean:212-227 iotaCertsFull
con-leche: ConLeche/Cached/CoreC.lean:485-489 iotaCertsFullI — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.iotaCertsFull_bridge, then delete this line
empty-accumulator entry of `iotaCertsFullAux`. -/
def iotaCertsFull (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (h : EIdx) (args : List EIdx) : AM Bool :=
  iotaCertsFullAux r fe depth h #[] args.toArray 0

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:691-696 piResidual — peel a
∀-telescope along an argument list. -/
def piResidual : EIdx → List EIdx → AM (Option EIdx)
  | e, [] => pure (some e)
  | h, a :: as => do
    if h.tag == ETag.forallE then
      match ← viewBind h with
      | none => failDanglingE
      | some (_, b) => do
        let b' ← instantiate1Fast coreWalkFuel b a 0
        piResidual b' as
    else pure none

/-- con-leche: ConLeche/Kernel/Core.lean:229-238 defEqList — pairwise
definitional equality of two spines. -/
def defEqList (r : CoreFnsA) (fe : IFEnv) (depth : Nat) :
    List EIdx → List EIdx → AM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then defEqList r fe depth as bs else pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:240-254 iotaIndexOk — the
canonical-index comparison of a firing ι redex. -/
def iotaIndexOk (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (mI rP cnP : Nat)
    (tyCtor : EIdx) (margs idx : List EIdx) : AM Bool :=
  if mI = rP then pure true
  else do
    match ← piResidual tyCtor margs with
    | some residual => do
      let args ← getAppArgs coreWalkFuel residual
      defEqList r fe depth (args.drop cnP) idx
    | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:256-278 proofIrrel — proof
irrelevance certification: both sides' types' *sorts* are `Prop` (the
unit-like branch went with con-leche's PUNIT). -/
def proofIrrel (r : CoreFnsA) (_fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM Bool := do
  -- con-leche's task #172 B4: every inference here is at the io grade
  let ta ← r.inferIO depth a
  let hh ← r.whnf depth (← r.inferIO depth ta)
  if hh.tag == ETag.sort then
    match ← view hh with
    | .sort uT => do
      let z ← zeroLevel
      let okA ← liftFueled "level comparison" (← lvlEq? uT z)
      let tb ← r.inferIO depth b
      let hh ← r.whnf depth (← r.inferIO depth tb)
      if hh.tag == ETag.sort then
        match ← view hh with
        | .sort vT => do
          -- the Rust's `prop_sorts_zero_right` reads `zeroLevel` again here
          let z ← zeroLevel
          let okB ← liftFueled "level comparison" (← lvlEq? vT z)
          pure (okA && okB)
        | _ => pure false
      else pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:280-322 propIrrel — **the hoisted
proof-irrelevance test** (con-leche's task #168, Option U): the `Prop`
branch of `proofIrrel` alone, with the head-symbol readers deciding both
fast arms before any inference. -/
def propIrrel (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM Bool := do
  if (← notProofFast fe coreWalkFuel a) || (← notProofFast fe coreWalkFuel b) then
    pure false
  else if (← isProofFast fe coreWalkFuel a) && (← isProofFast fe coreWalkFuel b) then
    -- the yes arm (con-leche's task #168 stage 3): the squash-regime licence
    pure true
  else do
    let ta ← r.inferIO depth a
    let hh ← r.whnf depth (← r.inferIO depth ta)
    if hh.tag == ETag.sort then
      match ← view hh with
      | .sort uT => do
        let z ← zeroLevel
        let okA ← liftFueled "level comparison" (← lvlEq? uT z)
        let tb ← r.inferIO depth b
        let hh ← r.whnf depth (← r.inferIO depth tb)
        if hh.tag == ETag.sort then
          match ← view hh with
          | .sort vT => do
            -- the Rust's `prop_sorts_zero_right` reads `zeroLevel` again here
            let z ← zeroLevel
            let okB ← liftFueled "level comparison" (← lvlEq? vT z)
            pure (okA && okB)
          | _ => pure false
        else pure false
      | _ => pure false
    else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:698-702 etaProjs — the `.proj`
spine, as a counted recursion (con-leche's `(List.range nF).map`). -/
def projNodesGo (T : NIdx) (b : EIdx) : Nat → Nat → AM (List EIdx)
  | 0, _ => pure []
  | n + 1, j => do
    let p ← internE (.proj T j b)
    let rest ← projNodesGo T b n (j + 1)
    pure (p :: rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:698-702 etaProjs
con-leche: ConLeche/Cached/CoreC.lean:94-101 projNodesI — the fabricated
projections of a structure-eta spine: the `.proj T j b` nodes, one per field
of the family's projection table. -/
def etaProjs (T : NIdx) (b : EIdx) (nF : Nat) : AM (List EIdx) :=
  projNodesGo T b nF 0

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:95-102 reservedBasisNames —
the names reserved for the pinned basis blocks, interned.  `contains` is
then handle equality, as everywhere else in this module. -/
def reservedBasisNames : AM (List NIdx) :=
  pinReserved

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:499-504 litGuardNames — the ten
names the two literal guards look up: the `Nat` guard's three and the
`String` guard's seven, off the pin table (every one is pinned).  Placed after
`reservedBasisNames` (its one reader's other list) rather than beside
`natOpWfNames` as in the Rust: a module-order difference only. -/
def litGuardNames : AM (List NIdx) := do
  let a ← pinNat
  let b ← pinNatZero
  let c ← pinNatSucc
  let d ← pinString
  let f ← pinStringOfList
  let g ← pinList
  let h ← pinListNil
  let i ← pinListCons
  let j ← pinChar
  let k ← pinCharOfNat
  pure [a, b, c, d, f, g, h, i, j, k]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:506-520 reservedRecName — the last
three disjuncts: `n == boolName || n == boolTrueName || n == boolFalseName`. -/
def reservedRecBool (n : NIdx) : AM Bool := do
  let b ← pinBool
  if n == b then pure true
  else do
    let t ← pinBoolTrue
    if n == t then pure true
    else do
      let f ← pinBoolFalse
      pure (n == f)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:506-520 reservedRecName — **a
name no block RECURSOR may take**: one a literal guard looks up, one of the
certified `Nat` operations, or `Bool` and its two constructors, whose stored
entries the certified operations' guards read.  The basis names are
`basisNamesOk`'s (a pinned block's own recursor carries one).  The cited `||`
chain, each list read off the pin table (handle equality). -/
def reservedRecName (n : NIdx) : AM Bool := do
  let ls ← litGuardNames
  if ls.contains n then pure true
  else do
    let os ← natOpNames
    if os.contains n then pure true
    else do
      let ds ← natDivModNames
      if ds.contains n then pure true
      else reservedRecBool n

/-- con-leche: ConLeche/Kernel/Core.lean:324-364 structEtaCertWith
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.structEtaCertWith_bridge, then delete this line
con-leche: ConLeche/Cached/CoreC.lean:585-623 structEtaCertWithI — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.structEtaCertWith_bridge, then delete this line
structure-eta certificate against a *given* weak-head-normal type of the stuck
side: the type's head is a stored η family whose projection table's
constructor is the candidate's, at the table's parameter count and the
former's level parameters; the level comparison, then the parameters and the
fields against the fabricated projections (no type-application certificate,
con-leche's task #342 L11b).  The constructor and the counts are the table's,
at every field count. -/
def structEtaCertWith (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b wtb : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel a
  if hh.tag == ETag.const then
    match ← view hh with
    | .const c us =>
      match fe.find? c with
      | some (.ctorInfo cvc cnP cnF) => do
        let aargs ← getAppArgs coreWalkFuel a
        if aargs.length = cnP + cnF then do
          let hh ← getAppFn coreWalkFuel wtb
          if hh.tag == ETag.const then
            match ← view hh with
            | .const T us' =>
              match fe.find? T with
              | some (.indInfo cvT caps) =>
                match fe.findTable? T with
                | none => pure false
                | some tbl => do
                  let targs ← getAppArgs coreWalkFuel wtb
                  match ← viewLsLen us' with
                  | none => failDanglingLs
                  | some uslen =>
                  if caps.eta = true ∧ tbl.ctor = c ∧
                      targs.length = tbl.numParams ∧
                      uslen = cvT.levelParams.length ∧
                      cvc.levelParams = cvT.levelParams then do
                    if ← liftFueled "level comparison" (← lvlsEq? us us') then do
                      if ← defEqList r fe depth (aargs.take tbl.numParams) targs then do
                        let projs ← etaProjs T b tbl.numFields
                        defEqList r fe depth (aargs.drop tbl.numParams) projs
                      else pure false
                    else pure false
                  else pure false
              | _ => pure false
            | _ => pure false
          else pure false
        else pure false
      | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:704-715 etaCtorShape — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.etaCtorShape_bridge, then delete this line
constructor shape official's `try_eta_struct_core` tests before inferring
anything: the candidate's head is a stored constructor applied to exactly
its parameters and fields. -/
def etaCtorShape (fe : IFEnv) (a : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel a
  if hh.tag == ETag.const then
    match ← view hh with
    | .const c _ =>
      match fe.find? c with
      | some (.ctorInfo _ cnP cnF) => do
        let args ← getAppArgs coreWalkFuel a
        pure (args.length == cnP + cnF)
      | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:717-740 etaCtorPartial
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.etaCtorPartialFam_bridge, then delete this line
con-leche: ConLeche/Cached/StateC.lean:97-115 etaCtorPartialC — the family
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.etaCtorPartialFam_bridge, then delete this line
half of `etaCtorPartial`: the family the constructor's type `ty` ends in is a
stored η family whose projection table's constructor is `c`. -/
def etaCtorPartialFam (fe : IFEnv) (c : NIdx) (ty : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel (← piResult coreWalkFuel ty)
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T _ =>
      match fe.find? T with
      | some (.indInfo _ caps) =>
        match fe.findTable? T with
        | some tbl => if caps.eta then pure (tbl.ctor == c) else pure false
        | none => pure false
      | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:717-740 etaCtorPartial
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.etaCtorPartial_bridge, then delete this line
con-leche: ConLeche/Cached/StateC.lean:97-115 etaCtorPartialC — **a
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.etaCtorPartial_bridge, then delete this line
partially applied η constructor** (official's `try_eta_struct_core` since
lean4#15373): the candidate's head is a stored constructor applied to fewer
than its parameters and fields, of a stored η family whose projection table's
constructor it is.  `some k`, `k > 0` the arguments it lacks.  Read off the
stored records alone, before any inference. -/
def etaCtorPartial (fe : IFEnv) (a : EIdx) : AM (Option Nat) := do
  let hh ← getAppFn coreWalkFuel a
  if hh.tag == ETag.const then
    match ← view hh with
    | .const c _ =>
      match fe.find? c with
      | some (.ctorInfo cvc cnP cnF) => do
        let args ← getAppArgs coreWalkFuel a
        if args.length < cnP + cnF then do
          if ← etaCtorPartialFam fe c cvc.type then pure (some (cnP + cnF - args.length))
          else pure none
        else pure none
      | _ => pure none
    | _ => pure none
  else pure none

/-- con-leche: ConLeche/Kernel/Core.lean:366-387 structEtaFull
con-leche: ConLeche/Cached/CoreC.lean:625-635 structEtaFullI — the body of
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.structEtaFullAt_bridge, then delete this line
**structure η at a fully applied constructor**, past the constructor-shape
gate: `b`'s io-inferred type, head-normalised, and the certificate against
it. -/
def structEtaFullAt (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b : EIdx) : AM Bool := do
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  structEtaCertWith r fe depth a b wtb

/-- con-leche: ConLeche/Kernel/Core.lean:366-387 structEtaFull
con-leche: ConLeche/Cached/CoreC.lean:625-635 structEtaFullI — **structure η
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.structEtaFull_bridge, then delete this line
at a fully applied constructor**.  The constructor-shape test comes FIRST (the
divergence audit's D13). -/
def structEtaFull (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b : EIdx) : AM Bool := do
  if ← etaCtorShape fe a then structEtaFullAt r fe depth a b
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:389-401 structEtaExpand
con-leche: ConLeche/Cached/CoreC.lean:637-646 structEtaExpandI — **the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.structEtaExpand_bridge, then delete this line
η-expansion of a partially applied constructor**: both sides applied to fresh
variables along the constructor side's type `ta`, one binder per missing
argument, read syntactically; at the full application, `structEtaFull`. -/
def structEtaExpand (r : CoreFnsA) (fe : IFEnv) :
    Nat → Nat → EIdx → EIdx → EIdx → AM Bool
  | 0, depth, a, b, _ => structEtaFull r fe depth a b
  | k + 1, depth, a, b, ta => do
    if ta.tag == ETag.forallE then
      match ← viewBind ta with
      | none => failDanglingE
      | some (dom, body) => do
        let fv ← internE (.fvar depth dom)
        let a2 ← internE (.app a fv)
        let b2 ← internE (.app b fv)
        let body2 ← instantiate1Fast coreWalkFuel body fv 0
        structEtaExpand r fe k (depth + 1) a2 b2 body2
    else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:403-421 structEtaCert
con-leche: ConLeche/Cached/CoreC.lean:648-661 structEtaCertI — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.structEtaCertPartial_bridge, then delete this line
partial-constructor arm of `structEtaCert`, at `k` missing arguments: the
other side neutral, the two io-inferred types compared (official's
`is_def_eq(t_type, s_type)`), then both sides η-expanded. -/
def structEtaCertPartial (r : CoreFnsA) (fe : IFEnv)
    (depth k : Nat) (a b : EIdx) : AM Bool := do
  if !(← ioNeutral b) then pure false
  else do
    let ta ← r.inferIO depth a
    let tb ← r.inferIO depth b
    if ← r.defeq depth tb ta then structEtaExpand r fe k depth a b ta
    else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:403-421 structEtaCert
con-leche: ConLeche/Cached/CoreC.lean:648-661 structEtaCertI — structural eta
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.structEtaCert_bridge, then delete this line
certification (official's `try_eta_struct_core`): `a` is a constructor
application of a stored η family, fully applied (`structEtaFull`'s body: the
shape gate is read once) or partially (`etaCtorPartial`). -/
def structEtaCert (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b : EIdx) : AM Bool := do
  if ← etaCtorShape fe a then structEtaFullAt r fe depth a b
  else
    match ← etaCtorPartial fe a with
    | some k => structEtaCertPartial r fe depth k a b
    | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:423-428 isPropType
con-leche: ConLeche/Cached/CoreC.lean:663-672 isPropTypeI — **is a
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.isPropType_bridge, then delete this line
proposition** (official's `is_prop`): `T`'s io-inferred type head-normalises
to a sort equivalent to `Prop`. -/
def isPropType (r : CoreFnsA) (depth : Nat) (T : EIdx) : AM Bool := do
  let tt ← r.inferIO depth T
  let w ← r.whnf depth tt
  if w.tag == ETag.sort then
    match ← viewSort w with
    | none => failDanglingE
    | some u => do
      let z ← zeroLevel
      liftFueled "level comparison" (← lvlEq? u z)
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:430-445 unitLikeFields
con-leche: ConLeche/Cached/CoreC.lean:674-688 unitLikeFieldsI — **the field
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.unitLikeFields_bridge, then delete this line
loop of official's `is_unit_like`**: each of the `n` field binders of an η
family's instance telescope has a proposition or a unit-like type (`ul`,
official's recursive `is_unit_like`), the field opened at a fresh variable
before the next.  The binders are syntactic. -/
def unitLikeFields (r : CoreFnsA) (ul : Nat → EIdx → AM Bool) :
    Nat → Nat → EIdx → AM Bool
  | 0, _, _ => pure true
  | n + 1, depth, tele => do
    if tele.tag == ETag.forallE then
      match ← viewBind tele with
      | none => failDanglingE
      | some (dom, body) => do
        if ← isPropType r depth dom then do
          let fv ← internE (.fvar depth dom)
          let body2 ← instantiate1Fast coreWalkFuel body fv 0
          unitLikeFields r ul n (depth + 1) body2
        else if ← ul depth dom then do
          let fv ← internE (.fvar depth dom)
          let body2 ← instantiate1Fast coreWalkFuel body fv 0
          unitLikeFields r ul n (depth + 1) body2
        else pure false
    else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:447-450 unitLikeFuel — recursion
budget of the unit-like test (`unitLikeLoop`).  Exhaustion is "not
unit-like", which is always sound. -/
@[noinline] def unitLikeFuel : Nat := 4611686018427387904  -- 2^62

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:750-777 unitLikeShape
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.unitLikeShapeAt_bridge, then delete this line
con-leche: ConLeche/Kernel/CoreDefs.lean:742-748 unitFieldTele
con-leche: ConLeche/Cached/CoreC.lean:103-124 unitLikeShapeF — the field
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.unitLikeShapeAt_bridge, then delete this line
telescope of an instance at its family's table: the table's constructor,
stored, its type at the instance's levels `us`, the table's `nP` parameter
binders dropped and instantiated with the instance's arguments in one pass. -/
def unitLikeShapeAt (fe : IFEnv) (us : LsIdx) (targs : List EIdx) (tctor : NIdx)
    (nP nF : Nat) : AM (Option (EIdx × Nat)) := do
  match fe.find? tctor with
  | some (.ctorInfo cvc _ _) => do
    let cty ← instLPFast coreWalkFuel cvc.levelParams us cvc.type
    match ← peelPis nP cty with
    | none => pure none
    | some body => do
      let tele ← instantiateListFast coreWalkFuel body targs.toArray 0
      pure (some (tele, nF))
  | _ => pure none

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:750-777 unitLikeShape
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.unitLikeShape_bridge, then delete this line
con-leche: ConLeche/Cached/CoreC.lean:103-124 unitLikeShapeF — **the shape of
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.unitLikeShape_bridge, then delete this line
an instance in official's `is_unit_like`**, read off the stored records: `w`
is an instance of a stored η family at its parameters (the table's count),
whose constructor's field telescope at the instance's parameters is `tele`
with `n` fields to check (`some (tele, n)`), or not (`none`). -/
def unitLikeShape (fe : IFEnv) (w : EIdx) : AM (Option (EIdx × Nat)) := do
  let hh ← getAppFn coreWalkFuel w
  if hh.tag == ETag.const then
    match ← view hh with
    | .const S us =>
      match fe.find? S with
      | some (.indInfo cvS caps) => do
        match ← viewLsLen us with
        | none => failDanglingLs
        | some usl =>
        if caps.eta = true ∧ usl = cvS.levelParams.length then
          match fe.findTable? S with
          | none => pure none
          | some tbl => do
            let targs ← getAppArgs coreWalkFuel w
            if targs.length = tbl.numParams then
              unitLikeShapeAt fe us targs tbl.ctor tbl.numParams tbl.numFields
            else pure none
        else pure none
      | _ => pure none
    | _ => pure none
  else pure none

/-- con-leche: ConLeche/Kernel/Core.lean:452-462 unitLikeStruct
con-leche: ConLeche/Cached/CoreC.lean:690-696 unitLikeStructI — **the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.unitLikeStruct_bridge, then delete this line
structure arm of official's `is_unit_like`**: `w`, a head normal form that is
no ∀, is an instance of a stored η family every field of whose constructor,
at the instance's parameters, has a proposition or a unit-like type (`ul`). -/
def unitLikeStruct (r : CoreFnsA) (ul : Nat → EIdx → AM Bool) (fe : IFEnv)
    (depth : Nat) (w : EIdx) : AM Bool := do
  match ← unitLikeShape fe w with
  | some (tele, n) => unitLikeFields r ul n depth tele
  | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:464-476 unitLikeLoop
con-leche: ConLeche/Cached/CoreC.lean:698-708 unitLikeLoopI — **is a type
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.unitLikeLoop_bridge, then delete this line
unit-like** (official's `is_unit_like`, lean4#15372): its head normal form is
a ∀ whose codomain, opened at a fresh variable, is unit-like, or an instance
of a stored η family every field of whose constructor is a proposition or
unit-like (`unitLikeStruct`). -/
def unitLikeLoop (r : CoreFnsA) (fe : IFEnv) : Nat → Nat → EIdx → AM Bool
  | 0, _, _ => pure false
  | fuel + 1, depth, T => do
    let w ← r.whnf depth T
    if w.tag == ETag.forallE then
      match ← viewBind w with
      | none => failDanglingE
      | some (dom, body) => do
        let fv ← internE (.fvar depth dom)
        let body2 ← instantiate1Fast coreWalkFuel body fv 0
        unitLikeLoop r fe fuel (depth + 1) body2
    else unitLikeStruct r (unitLikeLoop r fe fuel) fe depth w

/-- con-leche: ConLeche/Kernel/Core.lean:478-495 structUnitCert
con-leche: ConLeche/Cached/CoreC.lean:710-722 structUnitCertI —
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.structUnitCert_bridge, then delete this line
**unit-likeness** (official's `is_def_eq_unit_like`): `a`'s io-inferred type,
head-normalised, is unit-like (`unitLikeLoop`), and `b`'s type is
definitionally equal to it (no type-application certificate).  A side whose
type is a ∀ must be neutral (`ioNeutral`, con-leche's task #342 L18). -/
def structUnitCert (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b : EIdx) : AM Bool := do
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  let ga ← if isForallE wta then ioNeutral a else pure true
  if !ga then pure false
  else if ← unitLikeLoop r fe unitLikeFuel depth wta then do
    let tb ← r.inferIO depth b
    let wtb ← r.whnf depth tb
    let gb ← if isForallE wtb then ioNeutral b else pure true
    if !gb then pure false
    else r.defeq depth wta wtb
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:497-523 etaCert — eta
certification for a one-sided λ against a stuck term `b`: `b`'s head must be
neutral (`ioNeutral`), its type a ∀ whose domain is the λ's; the bodies are
compared at a fresh variable, and at the verified mode the λ body's FULL-grade
type is compared with the ∀'s codomain there (con-leche's task #342, T2). -/
def etaCert (mode : CheckMode) (r : CoreFnsA) (_fe : IFEnv) (depth : Nat)
    (ty₁ body₁ : EIdx) (b : EIdx) : AM Bool := do
  if !(← ioNeutral b) then pure false
  else do
  let tb ← r.inferIO depth b
  let hh ← r.whnf depth tb
  if hh.tag == ETag.forallE then
    match ← view hh with
    | .forallE ty₂ cod₂ => do
      if ← r.defeq depth ty₂ ty₁ then do
        let fv ← internE (.fvar depth ty₁)
        let lhs ← instantiate1Fast coreWalkFuel body₁ fv 0
        let rhs ← internE (.app b fv)
        if !(← r.defeq (depth + 1) lhs rhs) then pure false else do
          if mode.verifiedChecks then do
            let t₁ ← r.infer (depth + 1) lhs
            let t₂ ← instantiate1Fast coreWalkFuel cod₂ fv 0
            r.defeq (depth + 1) t₁ t₂
          else pure true
      else pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:525-532 stuckIrrel — the fallback
for structurally distinct stuck terms: structural eta in either direction,
unit-likeness, else proof irrelevance. -/
def stuckIrrel (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) : AM Bool := do
  if ← structEtaCert r fe depth a b then pure true
  else if ← structEtaCert r fe depth b a then pure true
  else if ← structUnitCert r fe depth a b then pure true
  else proofIrrel r fe depth a b

/-- con-leche: ConLeche/Kernel/Core.lean:534-545 formerSortLoop
con-leche: ConLeche/Cached/CoreC.lean:759-773 formerSortLoopI
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.formerSortLoop_bridge, then delete this line
**Official's walk to a family's sort** (the loop of `check_inductive_types` at
the use): `n` binders down, each reached by head normalization (`r.whnf`),
then a sort; `none` where the type does not get there.  Structural on `n`;
the body is instantiated through the memoized `instantiate1`, as the cached
twin's `inst1M`. -/
def formerSortLoop (r : CoreFnsA) : Nat → Nat → EIdx → AM (Option LIdx)
  | d, 0, e => do
    let w ← r.whnf d e
    if w.tag == ETag.sort then
      match ← viewSort w with
      | none => failDanglingE
      | some s => pure (some s)
    else pure none
  | d, n + 1, e => do
    let w ← r.whnf d e
    if w.tag == ETag.forallE then
      match ← viewBind w with
      | none => failDanglingE
      | some (dom, b) => do
        let fv ← internE (.fvar d dom)
        let b2 ← instantiate1Fast coreWalkFuel b fv 0
        formerSortLoop r (d + 1) n b2
    else pure none

/-- con-leche: ConLeche/Kernel/Core.lean:547-560 formerNeverZeroAt
con-leche: ConLeche/Cached/CoreC.lean:775-786 formerNeverZeroI
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.formerNeverZeroAt_bridge, then delete this line
**Is a family's sort never zero at the levels `us`** (official
`is_never_zero`), computed where it is asked.  A stored type that ends in a
sort is read off directly (`formerNeverZero`); any other is walked by
`formerSortLoop` at the use's levels, and where the walk reaches no sort the
answer is the conservative `false`. -/
def formerNeverZeroAt (r : CoreFnsA) (cvT : IConstantVal) (caps : IIndCaps)
    (us : LsIdx) : AM Bool := do
  match ← formerResSort cvT.type with
  | some _ => formerNeverZero cvT us
  | none => do
    let ty ← instLPFast coreWalkFuel cvT.levelParams us cvT.type
    match ← formerSortLoop r 0 (caps.nparams + caps.nIdx) ty with
    | some s => do
      let l ← readLevelM s
      pure (Level.zeronessOf l).isNever
    | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:562-583 iotaCase3At
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.iotaCase3At_bridge, then delete this line
con-leche: ConLeche/Cached/CoreC.lean:794-805 iotaCase3I
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.iotaCase3At_bridge, then delete this line
**Case 3 of the ι case split** (con-leche task #342 L10, S5c): a rule that is
not K (the record's `isK`) whose constructor's family may be `Prop` at the
comparand levels `us`.  The family is not read at a K recursor. -/
def iotaCase3At (r : CoreFnsA) (fe : IFEnv) (isK : Bool) (cvj : IConstantVal)
    (us : LsIdx) : AM Bool := do
  if isK then pure false
  else
    match ← ctorFamily fe cvj with
    | some (cvT, caps) => do
      match ← viewLsLen us with
      | none => failDanglingLs
      | some usl =>
        if cvT.levelParams.length == usl then do
          let nz ← formerNeverZeroAt r cvT caps us
          pure !nz
        else pure true
    | none => pure true

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:779-783 etaFabArgsE — the
eta-rescue fabrication's argument spine: the major's type's arguments, then
the major's projections (`etaProjs`). -/
def etaFabArgsE (T : NIdx) (targs : List EIdx) (major : EIdx) (nF : Nat) :
    AM (List EIdx) := do
  let ps ← etaProjs T major nF
  pure (targs ++ ps)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:891-901 andRescueSlotsOf — the
two-slot walk, as a counted recursion (con-leche's `(List.range 2).all`):
each slot stored, naming the rule's constructor at the major's parameter
count, with two fields.  Pure, as con-leche's is. -/
def andRescueSlotsGo (fe : IFEnv) (an ctor : NIdx) (nP : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, j =>
    match fe.findProj? an j with
    | some e =>
      if e.ctor == ctor && e.numParams == nP && e.numFields == 2 then
        andRescueSlotsGo fe an ctor nP n (j + 1)
      else false
    | none => false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:891-901 andRescueSlotsOf
con-leche: ConLeche/Kernel/CoreDefs.lean:903-905 andRescueSlots
con-leche: ConLeche/Kernel/FEnv.lean:187-189 FEnv.andRescueSlotsF
**The pinned `And`'s projection slots, ready to fire.**  One twin for
con-leche's three spellings (deviation 1). -/
def andRescueSlots (fe : IFEnv) (ctor : NIdx) (nP : Nat) : AM Bool := do
  let an ← pinAnd
  pure (andRescueSlotsGo fe an ctor nP 2 0)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:907-924 etaRescueTable? — **the
structure-η rescue's standing condition, at use**: the single rule's
constructor `ctor` (stored as `cvj`) is the constructor of its family's
projection table `tbl?` (the family `cvT` structure-like, `IIndCaps.eta`), and
carries the family's level parameters; the table, for the fabrication's
counts.  `And.intro` is left to `And`'s own rescue.  The cited `&&` chain,
left to right (the `And.intro` pin is read only when the chain reaches it). -/
def etaRescueTable? (tbl? : Option IProjTable) (ctor : NIdx) (cvj cvT : IConstantVal)
    (caps : IIndCaps) : AM (Option IProjTable) := do
  match tbl? with
  | none => pure none
  | some t =>
    if caps.eta && t.ctor == ctor && cvj.levelParams == cvT.levelParams then do
      let ai ← pinAndIntro
      if ctor != ai then pure (some t) else pure none
    else pure none

/-! ## The stuck-major rescue and the ι step

con-leche's `Core.lean`:1311-1832. -/

/-- con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.fabScopeOk_bridge, then delete this line
con-leche: ConLeche/Cached/CoreC.lean:807-906 majorToCtorI — the scope guard
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.fabScopeOk_bridge, then delete this line
the three rescue branches share (cf. `annotateProjElim`): the fabricated major
is well-scoped, closed under loose bvars, and mentions no free variable the
stuck major does not.

**The three tests are the EXECUTED tier's** (task #97g).  `Kernel/Core.lean`
spells the last one `fab.fvarLeaves.all (fun l => major.fvarLeaves.contains
l)`, and task #97d twinned that literally: two unmemoized DAG walks and a
quadratic list containment, which on `core.ndjson` was 43.9 % of the whole
run's cycles.  `Cached/CoreC.lean` runs `wscopedBC`, `looseBVarsBounded` off
the packed field and `leafGuard` instead — the same predicate, one memoized
walk each — and those are what (B) runs now.  `fvarLeavesSubset` below stays
as the specification of what `leafGuard` decides. -/
def fabScopeOk (depth : Nat) (fab major : EIdx) : AM Bool := do
  if !(← wscopedBFast coreWalkFuel depth fab) then pure false
  else if !(← looseBVarsBoundedFast coreWalkFuel 0 fab) then pure false
  else leafGuard coreWalkFuel fab major

/-- con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.majorToCtor_bridge, then delete this line
con-leche: ConLeche/Cached/CoreC.lean:807-906 majorToCtorI — **the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.majorToCtor_bridge, then delete this line
stuck-major rescue** (`to_cnstr_when_K` and `to_cnstr_when_structure`): a
recursor's major premise that is not a constructor application may still be
*replaced* by one — K-flagged (the record's `isK`), η-capable (`etaRescueTable?`),
or the pinned `And`.  No certificate
on a fabricated spine (con-leche's task #342 L-DEAD, L11b); the K and `And`
fabrications keep official's type check, and their proof-irrelevance run is a
certificate family (off at `.trusted`). -/
def majorToCtor (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (_recName : NIdx) (isK : Bool) (rules : List IRecRule) (major : EIdx) :
    AM EIdx := do
  -- cheap syntactic gates before any inference
  if ← isCtorApp fe major then pure major else
  match rules with
  | [rl] =>
    match fe.find? rl.ctor with
    | some (.ctorInfo cvj cnP _cnF) => do
      let hh ← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)
      if hh.tag == ETag.const then
        match ← view hh with
        | .const T _ =>
          match fe.find? T with
          | some (.indInfo cvT caps) => do
            if isK = true then do
              -- io grade (lean4lean `toCtorWhenK`'s `inferType`)
              let tmaj ← r.whnf depth (← r.inferIO depth major)
              let hh ← getAppFn coreWalkFuel tmaj
              if hh.tag == ETag.const then
                match ← view hh with
                | .const T' ust => do
                  let ustl ← viewLs ust
                  if T' = T ∧ cvj.levelParams.length = ustl.length then do
                    let targs ← getAppArgs coreWalkFuel tmaj
                    if cnP ≤ targs.length then do
                      let hd ← internE (.const rl.ctor ust)
                      let fab ← mkAppN hd (targs.take cnP)
                      if ← fabScopeOk depth fab major then do
                        -- the official `to_cnstr_when_K` type check, both modes
                        if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
                          -- `proofIrrel`, a certificate family (official stops
                          -- at the type check): off at `.trusted`
                          let irK ←
                            if mode.verifiedChecks then proofIrrel r fe depth fab major
                            else pure true
                          if irK then pure fab else pure major
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                | _ => pure major
              else pure major
            else match ← etaRescueTable? (fe.findTable? T) rl.ctor cvj cvT caps with
            | some tbl => do
              let tmaj ← r.whnf depth (← r.inferIO depth major)
              let hh ← getAppFn coreWalkFuel tmaj
              if hh.tag == ETag.const then
                match ← view hh with
                | .const T' ust => do
                  let ustl ← viewLs ust
                  let targs ← getAppArgs coreWalkFuel tmaj
                  if T' = T ∧ targs.length = tbl.numParams ∧
                      ustl.length = cvT.levelParams.length then do
                    -- the *instantiated* non-Prop test at the use
                    -- (`formerNeverZeroAt`); the constructor and the counts
                    -- are the table's
                    if ← formerNeverZeroAt r cvT caps ust then do
                      let fabArgs ← etaFabArgsE T targs major tbl.numFields
                      let hd ← internE (.const tbl.ctor ust)
                      let fab ← mkAppN hd fabArgs
                      -- no certificate on the fabricated spine (task #342 L11b)
                      if ← fabScopeOk depth fab major then pure fab
                      else pure major
                    else pure major
                  else pure major
                | _ => pure major
              else pure major
            | none => do
              let an ← pinAnd
              if T = an then do
                -- THE `And`-ONLY η RESCUE (user ruling: `And` and nothing else)
                let tmaj ← r.whnf depth (← r.inferIO depth major)
                let hh ← getAppFn coreWalkFuel tmaj
                if hh.tag == ETag.const then
                  match ← view hh with
                  | .const T' ust => do
                    match ← viewLsLen ust with
                    | none => failDanglingLs
                    | some ustl =>
                    let targs ← getAppArgs coreWalkFuel tmaj
                    let ars ← andRescueSlots fe rl.ctor cnP
                    if T' = T ∧ targs.length = cnP ∧
                        cvj.levelParams.length = ustl ∧ ars = true then do
                      let p0 ← internE (.proj T 0 major)
                      let p1 ← internE (.proj T 1 major)
                      let fabArgs := targs ++ [p0, p1]
                      let hd ← internE (.const rl.ctor ust)
                      let fab ← mkAppN hd fabArgs
                      if ← fabScopeOk depth fab major then do
                        if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
                          let irA ←
                            if mode.verifiedChecks then proofIrrel r fe depth fab major
                            else pure true
                          if irA then pure fab else pure major
                        else pure major
                      else pure major
                    else pure major
                  | _ => pure major
                else pure major
              else pure major
          | _ => pure major
        | _ => pure major
      else pure major
    | _ => pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:759-771 litMajorToCtor — convert a
literal major premise to constructor form: a `Nat` literal one layer, a
`String` literal to its *reduced* constructor form. -/
def litMajorToCtor (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : EIdx) :
    AM EIdx := do
  if h.tag == ETag.lit then
    match ← view h with
    | .lit (.strVal s) => do
      if ← strLitStored fe then do
        let c ← strLitToConstructor s
        r.whnf depth c
      else pure h
    | _ => litToCtorIfNat fe h
  else litToCtorIfNat fe h

/-- con-leche: ConLeche/Kernel/Core.lean:773-787 projLitToCtor — convert a
string-literal projection scrutinee to its *reduced* constructor form. -/
def projLitToCtor (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : EIdx) :
    AM EIdx := do
  if h.tag == ETag.lit then
    match ← view h with
    | .lit (.strVal s) => do
      if ← strLitStored fe then do
        let c ← strLitToConstructor s
        r.whnf depth c
      else pure h
    | _ => pure h
  else pure h

/-- con-leche: ConLeche/Kernel/Core.lean:789-793 Expr.isStrLit — is the
expression a `String` literal?  The tag, then the literal. -/
def isStrLit (h : EIdx) : AM Bool := do
  if h.tag == ETag.lit then
    match ← viewLit h with
    | none => failDanglingE
    | some (.strVal _) => pure true
    | some _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:795-869 prepareMajor
con-leche: ConLeche/Cached/CoreC.lean:932-955 prepareMajorI — the major
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.prepareMajor_bridge, then delete this line
premise's preparation before a rule fires: at a K-flagged recursor (the
record's `isK`) the K
rescue runs on the **raw** major and, if it did not produce a constructor
application, the major is left as it is (con-leche task #334); elsewhere the
structure rescues run on the major AS FOUND first (lean4#15351, con-leche's
task #342 R2; a `String` literal skips that attempt), and only if they produce
no constructor is the major head-normalized, its literal converted and the
rescue tried on the reduct. -/
def prepareMajor (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (recName : NIdx) (isK : Bool) (rules : List IRecRule) (major : EIdx) :
    AM EIdx := do
  if isK then do
    let majorK ← majorToCtor mode r fe depth recName isK rules major
    if ← isCtorApp fe majorK then
      litMajorToCtor r fe depth majorK
    else pure majorK
  else do
    let majorE ←
      if ← isStrLit major then pure major
      else majorToCtor mode r fe depth recName isK rules major
    if ← isCtorApp fe majorE then pure majorE
    else do
      let major₀ ← r.whnf depth majorE
      let major₁ ← litMajorToCtor r fe depth major₀
      majorToCtor mode r fe depth recName isK rules major₁

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:942-964 recFireComparands — the
nested rule's stored level comparands, substituted and re-interned
(`lvls.map (Level.subst lps us)` as a named recursion). -/
def substLevelsAt (ks : List ConLeche.Name) (vs : List Level) :
    List LIdx → AM (List LIdx)
  | [] => pure []
  | u :: us => do
    let l ← readLevelM u
    let h ← internLevel (Level.subst ks vs l)
    let rest ← substLevelsAt ks vs us
    pure (h :: rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:942-964 recFireComparands — the
canonical rule's level comparands, `cvjLps.map fun p => Level.subst lps us
(.param p)`, as a named recursion. -/
def substParamLevels (ks : List ConLeche.Name) (vs : List Level) :
    List NIdx → AM (List LIdx)
  | [] => pure []
  | p :: ps => do
    let pn ← readNameM p
    let h ← internLevel (Level.subst ks vs (.param pn))
    let rest ← substParamLevels ks vs ps
    pure (h :: rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:942-964 recFireComparands — the
nested rule's stored parameter pins, level-instantiated and instantiated at
the recursor's leading-argument spine, as a named recursion. -/
def instSpinePins (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat) :
    List EIdx → AM (List EIdx)
  | [] => pure []
  | p :: ps => do
    let q ← instLPFast coreWalkFuel lps us p
    let s ← instSpine coreWalkFuel (args.take rP) (rP - 1) q
    let rest ← instSpinePins lps us args rP ps
    pure (s :: rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:942-964 recFireComparands — the
LEVEL comparands of a firing rule (`(recFireComparands …).1`), interned: a
`.nested` or `.levels` rule's stored levels at the recursor's instantiation,
a `.plain` rule's constructor level parameters linked to the recursor's.  The
ι case split is decided at them (`iotaCase3At`), so they are computed before the
parameter comparands, which only case 3 reads (con-leche's task #342 S5c). -/
def recFireLevels (rl : IRecRule) (lps : List NIdx) (us : LsIdx)
    (cvjLps : List NIdx) : AM LsIdx := do
  match rl.fire with
  | .nested lvls _ => do
    let ks ← readNamesM lps
    let vs ← readLevelsM us
    let ls ← substLevelsAt ks vs lvls
    internLsNode ls
  | .plain => do
    let ks ← readNamesM lps
    let vs ← readLevelsM us
    let ls ← substParamLevels ks vs cvjLps
    internLsNode ls
  | .levels lvls => do
    let ks ← readNamesM lps
    let vs ← readLevelsM us
    let ls ← substLevelsAt ks vs lvls
    internLsNode ls

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:942-964 recFireComparands — the
constructor-PARAMETER comparands of a firing rule (`(recFireComparands …).2`):
a `.nested` rule's stored pins at the recursor's levels and leading-argument
spine, a `.plain` or `.levels` rule's the recursor's leading `cnP` arguments
(the stored constructor's parameter count). -/
def recFireArgs (rl : IRecRule) (cnP : Nat) (lps : List NIdx) (us : LsIdx)
    (args : List EIdx) (rP : Nat) : AM (List EIdx) := do
  match rl.fire with
  | .nested _ pins => instSpinePins lps us args rP pins
  | .plain => pure (args.take cnP)
  | .levels _ => pure (args.take cnP)

/-- con-leche: ConLeche/Kernel/Core.lean:871-970 iotaRec — the rule lookup
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.findRule_bridge, then delete this line
`rules.find? (fun r' => r'.ctor == cj)`, as a named recursion (DESIGN
§3.4). -/
def findRule : List IRecRule → NIdx → Option IRecRule
  | [], _ => none
  | rl :: rs, c => if rl.ctor == c then some rl else findRule rs c

/-- con-leche: ConLeche/Kernel/Core.lean:871-970 iotaRec — **one iota step at
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.iotaRecAt_bridge, then delete this line
a spine the caller already holds** (task #97-P6-9's hoist).  `iotaRec`'s own
first two steps are `getAppFn` and `getAppArgs`, and the batched β asks for an
iota step at every reduction step of a spine it is already walking: this entry
takes the head and the argument vector instead of re-walking them, which is
`getAppFn (mkAppN h as) = h` and `getAppArgsC (mkAppN h as) = as` — the
equation the bridge owes and the only thing OWED here that is not con-leche's
own clause.

The arity conjunct is moved in FRONT of the level-list read and of the
recursor's value copies (task #97-P6-10): both sides of `n = mI + 1` are pure
tests of the same conjunction and this one is `O(1)`.  con-leche's own
`iotaArityOk` is the same guard inside its `whnfAppI`. -/
def iotaRecAt (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (hd : EIdx) (sargs : Array EIdx) (n : Nat) : AM (Option EIdx) := do
  if hd.tag == ETag.const then
    match ← viewConst hd with
    | none => failDanglingE
    | some (c, us) =>
      match fe.find? c with
      | some (.recInfo cv mI rP isK rules) => do
        if n ≠ mI + 1 then pure none
        else do
        let args := (takeEidx sargs n).toList
        match ← viewLsLen us with
        | none => failDanglingLs
        | some usl =>
        -- checker change #9: the recursor's level arity, guarded as
        -- `unfoldDefinition` guards it
        -- the recursor's own telescope has the arity it is applied at
        -- (con-leche's task #342: in place of the spine's certificate);
        -- peeled before the three-way test, as the port does
        let peeled ← peelPis (mI + 1) cv.type
        if args.length = mI + 1 ∧ usl = cv.levelParams.length ∧
            peeled.isSome then do
          let b0 ← internE (.bvar 0)
          let major ← prepareMajor mode r fe depth c isK rules (args.getD mI b0)
          let hh ← getAppFn coreWalkFuel major
          if hh.tag == ETag.const then
            match ← view hh with
            | .const cj usj =>
              match fe.find? cj with
              | some (.ctorInfo cvj cnP _) =>
                match findRule rules cj with
                | some rl => do
                  let margs ← getAppArgs coreWalkFuel major
                  -- the parameter count is the stored constructor's, the
                  -- field count the rule's
                  if margs.length = cnP + rl.nfields then do
                    -- ONE certificate family (con-leche's task #342 L10, S5c;
                    -- official's `inductive_reduce_rec` checks nothing of the
                    -- major's constructor), so the whole block is what
                    -- `.trusted` omits: at a case-3 redex — not K, the
                    -- constructor's family may be `Prop` at the comparand
                    -- levels — the constructor's levels and parameters against
                    -- the comparands, the constructor telescope at the FULL
                    -- grade and the canonical-index comparison
                    -- (`Cached/CoreC.lean:647-670`)
                    let fam ←
                      if mode.verifiedChecks then do
                        let cmpL ← recFireLevels rl cv.levelParams us cvj.levelParams
                        if ← iotaCase3At r fe isK cvj cmpL then do
                          if ← liftFueled "level comparison" (← lvlsEq? usj cmpL) then do
                            let cmpA ← recFireArgs rl cnP cv.levelParams us args rP
                            if ← defEqList r fe depth (margs.take cnP) cmpA then do
                              let tyC ← constTyAt cvj usj
                              if ← iotaCertsFull r fe depth tyC margs then
                                iotaIndexOk r fe depth mI rP cnP tyC
                                  margs ((args.take mI).drop rP)
                              else pure false
                            else pure false
                          else pure false
                        else pure true
                      else pure true
                    if fam then do
                      let rhs ← ruleRhsAt c rl.ctor cv.levelParams rl.rhs us
                      let x ← mkAppN rhs
                        (args.take rP ++ margs.drop cnP)
                      pure (some x)
                    else pure none
                  else pure none
                | none => pure none
              | _ => pure none
            | _ => pure none
          else pure none
        else pure none
      | _ => pure none
  else pure none

/-! ## The application spine, the batched β, and the two stuck tags

DESIGN §8.6 item 9 (`whnfAppI` / `betaPeelI`) and item 7 (the stuck tags). -/

/-- con-leche: none — `internE` with task #97-P6-5's upward cutoff at the
`.app` node the reduction rebuilds: applying one more argument to a spine
whose head did not move is the node the spine already has. -/
@[inline] def internAppRebuilt (h : EIdx) (same : Bool) (f a : EIdx) : AM EIdx :=
  if same then pure h else internE (.app f a)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:847-850 getAppFn
con-leche: ConLeche/Kernel/ExprOps.lean:852-855 getAppArgs
The head, the argument vector AND the spine's own `.app` NODES, in ONE walk —
the third result is the arena's own and is what carries `internAppRebuilt`'s
`same` (the node the reduction may hand back unchanged). -/
def getAppSpineGo : Nat → EIdx → AM (EIdx × Array EIdx × Array EIdx)
  | 0, _ => fail (.internal "fuel exhausted: getAppSpine")
  | fuel + 1, h => do
    if h.tag == ETag.app then
      match ← viewApp h with
      | none => failDanglingE
      | some (f, a) => do
        let t ← getAppSpineGo fuel f
        pure (t.1, t.2.1.push a, t.2.2.push h)
    else pure (h, #[], #[])

/-- con-leche: ConLeche/Kernel/ExprOps.lean:847-855 getAppFn — the spine walk's
entry. -/
def getAppSpine (fuel : Nat) (h : EIdx) : AM (EIdx × Array EIdx × Array EIdx) :=
  getAppSpineGo fuel h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:847-855 getAppFn — the head and the
argument vector of a reduct, which is what `whnfApp` re-enters on.  A
non-application is its own head with no arguments. -/
def headAndArgs (v : EIdx) : AM (EIdx × Array EIdx) := do
  if v.tag == ETag.app then do
    let hd ← getAppFn coreWalkFuel v
    let va ← getAppArgs coreWalkFuel v
    pure (hd, va.toArray)
  else pure (v, #[])

/-- con-leche: ConLeche/Kernel/Core.lean:1025-1074 whnfCoreBody
con-leche: ConLeche/Cached/CoreC.lean:236-244 whnfCoreEasy — **the head
kinds `whnfCoreBody` returns unchanged, off the handle's TAG**: `sort`, `fvar`,
`forallE`, `lam`, `const` and `lit` are the body's own first six clauses and
exactly `whnfCoreEasy`'s kinds, and a handle carries the tag of its own view
on a well-formed store, so the memo probe and the node read are both skipped,
in both modes, as the cited knot does.  The obligation is `whnfCoreBody e =
pure e` for the six tags. -/
@[inline] def whnfCoreStuckTag (e : EIdx) : Bool :=
  let t := e.tag
  if t == ETag.app then false
  else if t == ETag.proj then false
  else if t == ETag.letE then false
  else if t == ETag.bvar then false
  else true

/-- con-leche: ConLeche/Kernel/Core.lean:1152-1154 whnfBody
con-leche: ConLeche/Cached/CoreC.lean:318-324 whnfEasy — **the head kinds
`whnfBody` returns unchanged**, the same test one rung up: `sort`, `fvar`,
`lam`, `forallE` and `lit`.  Deviation: `whnfEasy` leaves `lam` to the memo
(official `whnf` does); a `lam` is its own head normal form, so the memo could
only answer it with itself, and the test returns that answer before the probe.  The obligation adds `reduceNat e = none` (its
`match` is on `.app`) and `unfoldDefinition e = none` (`getAppFn` of a
non-`app` is the node itself and the `match` is on `.const`). -/
@[inline] def whnfStuckTag (e : EIdx) : Bool :=
  let t := e.tag
  if t == ETag.sort then true
  else if t == ETag.fvar then true
  else if t == ETag.lam then true
  else if t == ETag.forallE then true
  else if t == ETag.lit then true
  else false

/-! ### The step a reduction loop iterates (con-leche's task #342 R2) -/

/-- con-leche: ConLeche/Kernel/Core.lean:1094-1103 WhnfStep — the outcome of one
step of a head-normalization loop: the head normal form, or the term the loop
continues with.  A step RETURNS its continuation instead of calling it, so
every reduction step is the loop's own iteration and a chain of any length —
a non-terminating one included — runs in constant native stack. -/
inductive WhnfStep where
  | done (e : EIdx)
  | cont (e : EIdx)
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/Core.lean:1076-1092 whnfCoreLoopFuel — step budget
of the head-normalization loop: `2^62`, con-leche's value (task #330);
exhaustion is an internal error, never a verdict.  `@[noinline]` for
con-leche's reason: a literal at or above `2^32` is parsed from its decimal
string at every use otherwise. -/
@[noinline] def whnfCoreLoopFuel : Nat := 4611686018427387904  -- 2^62

/-! ### The batched β spine

con-leche's own CACHED-tier clauses (`Cached/CoreC.lean:739-766 whnfAppI` and
`:720-737 betaPeelI`), whose identification with the chained spec bodies
con-leche proves in `Verify/BetaSpine.lean` over `Expr.instantiateList_cons`.
The spec-shaped clause they replace re-entered the knot once per argument;
these peel a consecutive run of λ binders into ONE `instantiateList` walk.
Both RETURN a `WhnfStep` (con-leche's task #342 R2): a fired ι or a finished
peel hands the loop its reduct applied to the rest of the spine.

The accumulator is an `Array` in PUSH order (task #97-P6-15's clause change),
which `instantiateList` reads from the end — the same list con-leche's `::`
chain builds, the other way round. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:1069-1090 betaPeelI — peel a
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.betaPeel_bridge, then delete this line
consecutive run of λ binders, collecting their arguments, and substitute the
whole run in ONE `instantiateList`; the reduct, applied to the arguments left
over, is the term the loop continues with.  β is uniform (con-leche's task
#342 S0: no certificate, no gate). -/
def betaPeel (t : EIdx) (acc : Array EIdx) (args : Array EIdx) (i : Nat) :
    AM WhnfStep := do
  if hi : i < args.size then do
    if t.tag == ETag.lam then
      match ← viewBind t with
      | none => failDanglingE
      | some (_, body) => betaPeel body (acc.push args[i]) args (i + 1)
    else do
      let e2 ← instantiateListFast coreWalkFuel t acc 0
      let e3 ← mkAppNFrom e2 args i
      pure (.cont e3)
  else do
    let e2 ← instantiateListFast coreWalkFuel t acc 0
    pure (.cont e2)
termination_by args.size - i

/-- con-leche: ConLeche/Cached/CoreC.lean:1092-1120 whnfAppI — walk the spine's
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.whnfApp_bridge, then delete this line
arguments, applying each to the head's reduct: a λ head opens a peel group
(`betaPeel`), a stuck head applies the argument and tries one ι step at the
spine the walk already holds; a fired ι hands the loop its reduct applied to
the rest of the spine (`.cont`), the stuck spine is `.done`. -/
def whnfApp (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (v hd : EIdx) (vargs : Array EIdx) (same : Bool) (args nodes : Array EIdx)
    (i : Nat) : AM WhnfStep := do
  if hi : i < args.size then do
    let a := args[i]
    let node := nodes[i]!
    if v.tag == ETag.lam then
      match ← viewBind v with
      | none => failDanglingE
      | some (_, body) => betaPeel body #[a] args (i + 1)
    else do
      let ap ← internAppRebuilt node same v a
      let same2 := ap == node
      let va := vargs.push a
      let step ←
        if hd.tag == ETag.const then iotaRecAt mode r fe depth hd va va.size
        -- `iotaRec`'s own first two steps are `getAppFn` and a `.const` match,
        -- so a spine whose head is anything else answers `none` from every
        -- prefix: con-leche's `iotaArityOk` guard, off the handle's tag.
        else pure none
      match step with
      | none => whnfApp mode r fe depth ap hd va same2 args nodes (i + 1)
      | some e2 => do
        let e3 ← mkAppNFrom e2 args (i + 1)
        pure (.cont e3)
  else pure (.done v)
termination_by args.size - i

/-! ## The projection certificate and the reduction bodies

con-leche's `Core.lean`:1834-2074. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:992-1001 ProjEntry.typeAt — **the
type of a `.proj` node at a tower-backed entry**: the stored body,
level-instantiated at the subject type's levels, with the subject type's
arguments and the subject substituted for its `numParams + 1` loose
variables in ONE traversal. -/
def IProjEntry.typeAt (entry : IProjEntry) (us : LsIdx) (targs : List EIdx)
    (pe : EIdx) : AM EIdx := do
  let b ← instLPFast coreWalkFuel entry.levelParams us entry.body
  -- push order (task #97-P6-15): `pe :: targs.reverse` as a list is
  -- `targs ++ [pe]` as a push-order array, which is what the accumulator
  -- ruling makes every substituting site look like.
  instantiateListFast coreWalkFuel b (targs.toArray.push pe) 0

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:785-793 teleArityOk — **the
telescope check of a spine** (con-leche's task #342 L18): the telescope's
syntactic arity, nothing else. -/
def teleArityOk (ty : EIdx) (args : List EIdx) : AM Bool := do
  let p ← peelPis args.length ty
  pure p.isSome

/-- con-leche: ConLeche/Kernel/Core.lean:972-984 projCert
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.projCert_bridge, then delete this line
con-leche: ConLeche/Cached/CoreC.lean:199-203 projCertF — **the structural
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.projCert_bridge, then delete this line
projection's certificate**: the redex `proj_i (C p⃗ x⃗)`'s spine has the arity
of `C`'s stored (uninstantiated) type (`teleArityOk`). -/
def projCert (fe : IFEnv) (c : NIdx) (args : List EIdx) : AM Bool := do
  match fe.find? c with
  | some (.ctorInfo cvC _ _) => teleArityOk cvC.type args
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:986-993 projCertAt
con-leche: ConLeche/Cached/CoreC.lean:205-208 projCertAtF — **the fire
certificate as the mode runs it**: the verified core checks the arity; the
trusted core is the official kernel's, which checks nothing. -/
def projCertAt (fe : IFEnv) (verified : Bool) (c : NIdx) (args : List EIdx) :
    AM Bool :=
  if verified then projCert fe c args else pure true

/-- con-leche: ConLeche/Kernel/Core.lean:995-1023 reduceProjCore
con-leche: ConLeche/Cached/CoreC.lean:1044-1067 reduceProjCoreI — **the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.reduceProjCore_bridge, then delete this line
projection rule on a reduced scrutinee** (the official kernel's
`reduce_proj_core`): `proj_i (ctor p⃗ x⃗) ↦ x_i`, driven by the projection
table; the rule fires unguarded.  A string-literal scrutinee first expands to
its reduced constructor form; at the verified mode the fire is certified
(`projCertAt`).  `none` when
the rule does not fire.  Callers: `whnfCoreBody`'s `.proj` clause and
`lazyDeltaProjReduction`. -/
def reduceProjCore (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (sn : NIdx) (i : Nat) (c : EIdx) : AM (Option EIdx) := do
  let e' ← projLitToCtor r fe depth c
  match fe.findProj? sn i with
  | some entry => do
    let hh ← getAppFn coreWalkFuel e'
    if hh.tag == ETag.const then
      match ← view hh with
      | .const k us => do
        let args ← getAppArgs coreWalkFuel e'
        match ← viewLsLen us with
        | none => failDanglingLs
        | some usl =>
        if k = entry.ctor ∧ i < entry.numFields ∧
            args.length = entry.numParams + entry.numFields ∧
            usl = entry.levelParams.length then do
          let b0 ← internE (.bvar 0)
          let arg := args.getD (entry.numParams + i) b0
          if ← projCertAt fe mode.verifiedChecks k args then
            pure (some arg)
          else pure none
        else pure none
      | _ => pure none
    else pure none
  | none => pure none

/-- con-leche: ConLeche/Kernel/Core.lean:1025-1074 whnfCoreBody
con-leche: ConLeche/Cached/CoreC.lean:1140-1181 whnfCoreStepI — the `.proj`
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.whnfCoreStepProj_bridge, then delete this line
clause of the step: the scrutinee by `whnf`, or — in the CHEAP mode (official
`cheap_proj`) — by the cheap `whnfCore`, then the projection rule: a fired
field is the term the loop continues with, a stuck projection is its own
input. -/
def whnfCoreStepProj (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) (e : EIdx) (sn : NIdx) (i : Nat) (pe : EIdx) : AM WhnfStep := do
  let c ← if cheap then r.whnfCore true depth pe else r.whnf depth pe
  match ← reduceProjCore mode r fe depth sn i c with
  | some m' => pure (.cont m')
  | none => pure (.done e)

/-- con-leche: ConLeche/Kernel/Core.lean:1025-1074 whnfCoreBody
con-leche: ConLeche/Cached/CoreC.lean:1140-1181 whnfCoreStepI — **one
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.whnfCoreStep_bridge, then delete this line
head-normalization step** (β, ι, projection, ζ — **no δ**), returning the head
normal form or the term to continue with.  Only the spine head's
normalization stays a knot call (genuine nesting, bounded by the term's
depth); every *reduction* step is the loop's iteration.  Values return
themselves, which over handles is the handle itself. -/
def whnfCoreStep (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) (e : EIdx) : AM WhnfStep := do
  match ← view e with
  | .sort _ | .fvar _ _ | .forallE _ _ | .lam _ _ | .const _ _
  | .lit _ => pure (.done e)
  -- **The batched β spine** (task #97-P6-9): the spine's head is normalized
  -- once and the whole argument vector is run through `whnfApp`.
  | .app _ _ => do
    let sp ← getAppSpine coreWalkFuel e
    let v ← r.whnfCore cheap depth sp.1
    let same := v == sp.1
    let hv ← headAndArgs v
    whnfApp mode r fe depth v hv.1 hv.2 same sp.2.1 sp.2.2 0
  | .proj sn i pe => whnfCoreStepProj mode r fe cheap depth e sn i pe
  | .letE _ v b => do
    -- ζ, Lean's way (con-leche's task #342 S0: lets are stored as Lean
    -- stores them)
    let e' ← instantiate1Fast coreWalkFuel b v 0
    pure (.cont e')
  | .bvar _ =>
    fail (.notImplemented "whnf beyond the supported fragment")

/-- con-leche: ConLeche/Cached/CoreC.lean:1183-1229 whnfCoreLoopI — iterate
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.whnfCoreLoop_bridge, then delete this line
`whnfCoreStep` on its own step budget: the continuation is the loop's own tail
call (con-leche's task #342 R2), so a reduction chain of any length runs in
constant native stack, and a non-terminating one runs until the external
timeout.  The Rust spells the iteration as a loop. -/
def whnfCoreLoop (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: whnfCore loop")
  | n + 1, e => do
    match ← whnfCoreStep mode r fe cheap depth e with
    | .done v => pure v
    | .cont e' => whnfCoreLoop mode r fe cheap depth n e'

/-- con-leche: ConLeche/Kernel/Core.lean:1025-1074 whnfCoreBody
con-leche: ConLeche/Cached/CoreC.lean:1231-1235 whnfCoreBodyI — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.whnfCoreBody_bridge, then delete this line
head-normalization body: the loop at its own step budget.  `cheap` is the
official kernel's `cheap_proj`: a projection's scrutinee is reduced by
`whnfCore` itself instead of `whnf`, and the flag propagates to every
recursive head normalization. -/
def whnfCoreBody (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) :
    Bool → Nat → EIdx → AM EIdx :=
  fun cheap depth e => whnfCoreLoop mode r fe cheap depth whnfCoreLoopFuel e

/-- con-leche: ConLeche/Kernel/Core.lean:1105-1116 whnfLoopFuel — step budget
of the `whnf` reduction loop.  Literal-acceleration and delta steps are
*iteration*, not recursion.  Effectively unbounded since con-leche task #330:
`2^62`, con-leche's value (exhaustion is an internal error, never an accept).
`@[noinline]` for con-leche's reason: a literal at or above `2^32` is parsed
from its decimal string at every use otherwise. -/
@[noinline] def whnfLoopFuel : Nat := 4611686018427387904  -- 2^62

/-- con-leche: ConLeche/Kernel/Core.lean:1123-1143 whnfStep
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.whnfStep_bridge, then delete this line
con-leche: ConLeche/Cached/CoreC.lean:1004-1018 whnfStepI — one iteration of
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.whnfStep_bridge, then delete this line
the reduction loop: head-normalize, try literal acceleration, unfold one
definition.  **The continuation is returned, not called**: con-leche's `k e'`
is `.cont e'` (con-leche inlines the step so that its continuation call is
the loop's own tail call, task #342 R2; the twin returns the step, as the
Rust does). -/
def whnfStep (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e : EIdx) :
    AM WhnfStep := do
  let e₁ ← r.whnfCore false depth e
  match ← reduceNat r fe depth e₁ with
  | some e₂ => pure (.cont e₂)
  | none =>
    match ← unfoldDefinition fe e₁ with
    | some e₂ => pure (.cont e₂)
    | none => pure (.done e₁)

/-- con-leche: ConLeche/Kernel/Core.lean:1145-1150 whnfLoop
con-leche: ConLeche/Cached/CoreC.lean:1297-1316 whnfLoopI — the reduction loop:
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.whnfLoop_bridge, then delete this line
iterate `whnfStep` on its own step budget, so the whole chain costs one knot
level however many steps it takes, in constant native stack. -/
def whnfLoop (r : CoreFnsA) (fe : IFEnv) (depth : Nat) : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: whnf loop")
  | n + 1, e => do
    match ← whnfStep r fe depth e with
    | .done v => pure v
    | .cont e' => whnfLoop r fe depth n e'

/-- con-leche: ConLeche/Kernel/Core.lean:1152-1154 whnfBody — the reduction
loop's body: run `whnfLoop` at its own step budget. -/
def whnfBody (r : CoreFnsA) (fe : IFEnv) : Nat → EIdx → AM EIdx :=
  fun depth e => whnfLoop r fe depth whnfLoopFuel e

/-- con-leche: ConLeche/Kernel/Core.lean:1156-1162 ensureSort — ensure `e`
(the type of some expression) is a sort, returning its level. -/
def ensureSort (r : CoreFnsA) (_fe : IFEnv) (depth : Nat) (e : EIdx) :
    AM LIdx := do
  let hh ← r.whnf depth e
  if hh.tag == ETag.sort then
    match ← view hh with
    | .sort u => pure u
    | _ => fail (.invalid "expected a sort")
  else fail (.invalid "expected a sort")

/-- con-leche: ConLeche/Kernel/Core.lean:1164-1178 checkGuardRows
con-leche: ConLeche/Cached/CoreC.lean:1331-1344 checkGuardRowsI
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.checkGuardRows_bridge, then delete this line
**The rows of a projection's guard** (official `infer_proj`'s `is_prop`
tests): each row's term, inferred at the io grade at its own depth and
head-normalized, has a sort that is zero wherever `guardSort` is
(`Level.zeroWhereZero`, on the levels read back).  The list recursion is an
index recursion over the push-order rows. -/
def checkGuardRows (r : CoreFnsA) (guardSort : Level) (rows : Array (Nat × EIdx))
    (i : Nat) : AM Unit := do
  if hi : i < rows.size then do
    let (d, dom) := rows[i]
    let t ← r.inferIO d dom
    let w ← r.whnf d t
    if w.tag == ETag.sort then
      match ← viewSort w with
      | none => failDanglingE
      | some u => do
        let ul ← readLevelM u
        if Level.zeroWhereZero guardSort ul then checkGuardRows r guardSort rows (i + 1)
        else fail (.invalid "projection from a propositional structure must be a proposition")
    else fail (.invalid "expected a sort")
  else pure ()
termination_by rows.size - i

/-- con-leche: ConLeche/Kernel/Core.lean:1180-1196 projGuardSort
con-leche: ConLeche/Cached/CoreC.lean:1346-1357 projGuardSortI
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.projGuardSort_bridge, then delete this line
**The sort a projection's rows answer to**, at this use: `none` where the
guard has nothing to ask.  A stored type that ends in a sort answers at once
(`Prop` asks for propositions, any other sort nothing); otherwise the sort is
walked to at the use's levels (`formerSortLoop`): never zero asks nothing, a
sort that may be zero is the guard sort, and no sort at all is a reject.  The
level is read back (deviation 4). -/
def projGuardSort (r : CoreFnsA) (cvT : IConstantVal) (caps : IIndCaps)
    (us : LsIdx) : AM (Option Level) := do
  match ← formerResSort cvT.type with
  | some s => do
    let sl ← readLevelM s
    pure (if sl.isAlwaysZero then some .zero else none)
  | none => do
    let ty ← instLPFast coreWalkFuel cvT.levelParams us cvT.type
    match ← formerSortLoop r 0 (caps.nparams + caps.nIdx) ty with
    | some s => do
      let sl ← readLevelM s
      pure (if (Level.zeronessOf sl).isNever then none else some sl)
    | none => fail (.invalid "projection from a structure whose type reaches no sort")

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:795-805 openPisAtFvars — open
the first `n` `∀`-binders at fresh free variables `0..n-1` (each fvar's type
is the binder domain, instantiated with the earlier fvars).  Structural on
`n`, so no fuel of its own. -/
def openPisAtFvars : Nat → EIdx → Nat → AM (Option (List EIdx × EIdx))
  | 0, e, _ => pure (some ([], e))
  | n + 1, h, i => do
    if h.tag == ETag.forallE then
      match ← view h with
      | .forallE dom body => do
        let fv ← internE (.fvar i dom)
        let b ← instantiate1Fast coreWalkFuel body fv 0
        match ← openPisAtFvars n b (i + 1) with
        | some (fvs, e) => pure (some (fv :: fvs, e))
        | none => pure none
      | _ => pure none
    else pure none

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:2155-2170 openPisRawGoC — the
one-pass opening loop, the residual left raw: `acc` holds the already-created
fvars, innermost binder LAST (the push order `instantiateListFast` reads), and
each domain is instantiated by them in one `instantiateList` pass, where
`openPisAtFvars` re-instantiates the whole remaining body at every binder.
Returns the fvars, the substitution they make and the raw residual. -/
def openPisRawGo (acc : Array EIdx) :
    Nat → EIdx → Nat → AM (Option (List EIdx × Array EIdx × EIdx))
  | 0, e, _ => pure (some ([], acc, e))
  | n + 1, h, i => do
    if h.tag == ETag.forallE then
      match ← view h with
      | .forallE dom body => do
        let d ← instantiateListFast coreWalkFuel dom acc 0
        let fv ← internE (.fvar i d)
        match ← openPisRawGo (acc.push fv) n body (i + 1) with
        | some (fvs, acc', e) => pure (some (fv :: fvs, acc', e))
        | none => pure none
      | _ => pure none
    else pure none

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:2172-2179 openPisAtFvarsGoC
con-leche: ConLeche/Cached/ExprOpsC.lean:2181-2189 openPisAtFvarsC
The one-pass `openPisAtFvars`: the raw opening, then the residual in one
`instantiateList` pass.  No fallback: instantiating at free variables never
makes a binder appear, so where the one pass finds no `∀` the sequential
opening finds none either. -/
def openPisAtFvarsF (n : Nat) (e : EIdx) (i : Nat) :
    AM (Option (List EIdx × EIdx)) := do
  match ← openPisRawGo #[] n e i with
  | some (fvs, acc, r) => pure (some (fvs, ← instantiateListFast coreWalkFuel r acc 0))
  | none => pure none

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1506-1573 hasLooseBVarBXP
Record one answer for `(e, i)` in the memo the walk hands back. -/
@[inline] def hasLooseBVarBIns (e : EIdx) (i : Nat)
    (r : Bool × Std.HashMap (EIdx × Nat) Bool) :
    Bool × Std.HashMap (EIdx × Nat) Bool :=
  (r.1, r.2.insert (e, i) r.1)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:807-820 Expr.hasLooseBVar
con-leche: ConLeche/Kernel/CoreDefs.lean:822-840 Expr.hasLooseBVarB
con-leche: ConLeche/Cached/ExprOpsC.lean:1506-1573 hasLooseBVarBXP
Does `bvar i` occur loose in `e`?  The packed-bound cutoff (`bvarB ≤ i`) and a
per-call memo, as the cached walk has them: the cutoff stops the walk where
the variable CANNOT occur, the memo shares a shared node's answer
across the paths that reach it.  The memo is keyed by the node and the index,
because the index shifts under binders. -/
def hasLooseBVarBGo (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat) :
    Nat → EIdx → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | 0, _ => fail (.internal "fuel exhausted: hasLooseBVarB")
  | fuel + 1, h => do
    let bb ← bvarB fuel h
    if bb ≤ i then pure (false, memo) else
    match ← view h with
    | .bvar j => pure (i == j, memo)
    | .fvar _ _ => pure (false, memo)
    | .sort _ => pure (false, memo)
    | .const _ _ => pure (false, memo)
    | .lit _ => pure (false, memo)
    | v =>
      match memo[(h, i)]? with
      | some r => pure (r, memo)
      | none => do
        let r ← match v with
          | .app f a => do
            match ← hasLooseBVarBGo memo i fuel f with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hasLooseBVarBGo memo i fuel a
          | .lam ty b => do
            match ← hasLooseBVarBGo memo i fuel ty with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
          | .forallE ty b => do
            match ← hasLooseBVarBGo memo i fuel ty with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
          | .letE t v b => do
            match ← hasLooseBVarBGo memo i fuel t with
            | (true, memo) => pure (true, memo)
            | (false, memo) => do
              match ← hasLooseBVarBGo memo i fuel v with
              | (true, memo) => pure (true, memo)
              | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
          | .proj _ _ sub => hasLooseBVarBGo memo i fuel sub
          | _ => pure (false, memo)
        pure (hasLooseBVarBIns h i r)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1575-1579 hasLooseBVarBC
The executed `hasLooseBVarB` (one memoized DAG walk). -/
def hasLooseBVarBFast (i : Nat) (e : EIdx) : AM Bool := do
  pure (← hasLooseBVarBGo ∅ i coreWalkFuel e).1

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1590-1603 hasLooseBVarInP
con-leche: ConLeche/Cached/ExprOpsC.lean:1619-1672 hasLooseBVarInXP
Does a loose bound variable of index `d ..< d + w` occur in `e`?  Read only:
no node is built.  The packed-bound cutoff (`bvarB ≤ d`: no loose variable at
or above `d`) at every node; under a binder the window moves up by one.  The
memo is `hasLooseBVarBGo`'s, keyed by the node and the window's base (`w` is
fixed for the walk). -/
def hasLooseBVarInGo (memo : Std.HashMap (EIdx × Nat) Bool) (w d : Nat) :
    Nat → EIdx → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | 0, _ => fail (.internal "fuel exhausted: hasLooseBVarIn")
  | fuel + 1, h => do
    let bb ← bvarB fuel h
    if bb ≤ d then pure (false, memo) else
    match ← view h with
    | .bvar j => pure (decide (d ≤ j) && decide (j - d < w), memo)
    | .fvar _ _ => pure (false, memo)
    | .sort _ => pure (false, memo)
    | .const _ _ => pure (false, memo)
    | .lit _ => pure (false, memo)
    | v =>
      match memo[(h, d)]? with
      | some r => pure (r, memo)
      | none => do
        let r ← match v with
          | .app f a => do
            match ← hasLooseBVarInGo memo w d fuel f with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hasLooseBVarInGo memo w d fuel a
          | .lam ty b => do
            match ← hasLooseBVarInGo memo w d fuel ty with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hasLooseBVarInGo memo w (d + 1) fuel b
          | .forallE ty b => do
            match ← hasLooseBVarInGo memo w d fuel ty with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hasLooseBVarInGo memo w (d + 1) fuel b
          | .letE t v b => do
            match ← hasLooseBVarInGo memo w d fuel t with
            | (true, memo) => pure (true, memo)
            | (false, memo) => do
              match ← hasLooseBVarInGo memo w d fuel v with
              | (true, memo) => pure (true, memo)
              | (false, memo) => hasLooseBVarInGo memo w (d + 1) fuel b
          | .proj _ _ sub => hasLooseBVarInGo memo w d fuel sub
          | _ => pure (false, memo)
        pure (hasLooseBVarBIns h d r)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1674-1678 hasLooseBVarInC
The window query (one memoized DAG walk); an empty window asks nothing. -/
def hasLooseBVarIn (d w : Nat) (e : EIdx) : AM Bool := do
  if w == 0 then pure false
  else pure (← hasLooseBVarInGo ∅ w d coreWalkFuel e).1

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:842-849 structUsedLater
**Field `j` is used by a later field** — the official `infer_proj`'s
`has_loose_bvars(binding_body(r))` at step `j`. -/
def structUsedLater (cty : EIdx) (nP j : Nat) : AM Bool := do
  match ← stripPis (nP + j + 1) cty with
  | some (_, rest) => hasLooseBVarBFast 0 rest
  | none => pure false


/-- con-leche: ConLeche/Kernel/CoreDefs.lean:851-869 projGuardRowsGo
con-leche: ConLeche/Cached/ExprOpsC.lean:2240-2251 projGuardRowsGoC — **the
rows of a projection's guard: the field loop of the official `infer_proj`.**
`h` is the constructor telescope with its parameters and every field before the
current one opened, the current field's variable at depth `d`; `k` fields
remain before the projected one.  A field the rest of the telescope uses is a
row (its domain at depth `d`) and is opened at its variable; one it does not
use is stepped over.  The projected field's domain is the last row.  `none`
where the telescope binds too few fields.  The cited list is built front to
back, here as an accumulator in push order. -/
def projGuardRowsGo : Nat → Nat → EIdx → Array (Nat × EIdx) → AM (Option (Array (Nat × EIdx)))
  | k, d, h, out => do
    if h.tag == ETag.forallE then
      match ← view h with
      | .forallE dom body =>
        match k with
        | 0 => pure (some (out.push (d, dom)))
        | k + 1 =>
          if ← hasLooseBVarBFast 0 body then do
            let fv ← internE (.fvar d dom)
            let b2 ← instantiate1Fast coreWalkFuel body fv 0
            projGuardRowsGo k (d + 1) b2 (out.push (d, dom))
          else projGuardRowsGo k (d + 1) body out
      | _ => pure none
    else pure none

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:2253-2265 projGuardFastC —
**the projection guard's fast case**, on the RAW field telescope (the
parameters not substituted): `some` the projected field's raw domain where no
field's type up to the projected one, and nothing after it, mentions a field
before it — then no earlier field is used and the projected field's domain is
the one row.  `none` otherwise, and where the telescope binds too few fields.
`j` counts the fields passed; every query is the read-only window query
`hasLooseBVarIn` over the fields, the parameters above it. -/
def projGuardFast : Nat → Nat → EIdx → AM (Option EIdx)
  | k, j, h => do
    if h.tag == ETag.forallE then
      match ← view h with
      | .forallE dom body =>
        match k with
        | 0 => if ← hasLooseBVarIn 0 j h then pure none else pure (some dom)
        | k + 1 =>
          if ← hasLooseBVarIn 0 j dom then pure none
          else projGuardFast k (j + 1) body
      | _ => pure none
    else pure none

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:2267-2282 projGuardRowsC — the
rows past the parameters' raw opening: the fast case, its one domain
substituted, else the substituted residual stepped. -/
def projGuardRowsAt (entry : IProjEntry) (acc : Array EIdx) (r : EIdx) :
    AM (Option (Array (Nat × EIdx))) := do
  match ← projGuardFast entry.idx 0 r with
  | some dom => do
    let d ← instantiateListFast coreWalkFuel dom acc entry.idx
    pure (some (#[] |>.push (entry.numParams + entry.idx, d)))
  | none => do
    let r2 ← instantiateListFast coreWalkFuel r acc 0
    projGuardRowsGo entry.idx entry.numParams r2 #[]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:871-889 projGuardRows
con-leche: ConLeche/Cached/ExprOpsC.lean:2267-2282 projGuardRowsC
con-leche: ConLeche/Cached/CoreC.lean:1359-1371 checkProjRowsI
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.projGuardRows_bridge, then delete this line
**What a `.proj` use on a structure that may be a proposition must show**:
the domains, at the use's level instantiation and at the constructor
telescope's own variables, that must be propositions.  `none` where the
stored constructor does not bind what the entry says.  The executed shape is
the cached twin's: the constructor's type at the use's levels through the
per-declaration memo (`constTyAt`), its parameters opened with the residual
left raw (`openPisRawGo`).  Where no field before the projected one is
mentioned after it (`projGuardFast`), the one row is the projected field's
domain, its parameters substituted — the rest of the telescope is read, not
rebuilt.  Otherwise the residual is substituted and its fields stepped
(`projGuardRowsGo`). -/
def projGuardRows (fe : IFEnv) (entry : IProjEntry) (us : LsIdx) :
    AM (Option (Array (Nat × EIdx))) := do
  match fe.find? entry.ctor with
  | some ci => do
    let cv := ci.toConstantVal
    let cty ← constTyAt cv us
    match ← openPisRawGo #[] entry.numParams cty 0 with
    | some (_, acc, r) => projGuardRowsAt entry acc r
    | none => pure none
  | none => pure none

/-- con-leche: ConLeche/Kernel/Core.lean:1198-1211 checkProjGuard
con-leche: ConLeche/Cached/CoreC.lean:1373-1403 checkProjGuardI
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.checkProjGuard_bridge, then delete this line
con-leche: ConLeche/Cached/CoreC.lean:1359-1371 checkProjRowsI
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.checkProjGuard_bridge, then delete this line
**The official `infer_proj` restriction** at this use (con-leche task #480),
computed here from the stored structure and constructor types; nothing about
it is stored.  The rows are inferred at the io grade in every body, as
official's `infer_type` inside `is_prop`. -/
def checkProjGuard (r : CoreFnsA) (fe : IFEnv) (entry : IProjEntry) (us : LsIdx) :
    AM Unit := do
  match fe.find? entry.structName with
  | some (.indInfo cvT caps) => do
    match ← projGuardSort r cvT caps us with
    | none => pure ()
    | some gs =>
      match ← projGuardRows fe entry us with
      | some rows => checkGuardRows r gs rows 0
      | none => fail (.invalid "projection from a propositional structure must be a proposition")
  | _ => fail (.invalid "projection from a propositional structure must be a proposition")

/-- con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody — the λ clause's
result, `.forallE ty (bt.abstract1 depth)`.  con-leche writes it once at
the end of a clause with three exits; the arena names it, so the three exits
share one spelling and no arm is duplicated (DESIGN §8.4's Rust shape). -/
def inferLamResult (ty bt : EIdx) (depth : Nat) : AM EIdx := do
  let ab ← abstract1Fast coreWalkFuel bt depth 0
  internForallEE ty ab

/-! ### The binder telescopes

DESIGN §8.6 items 11 and 12.  con-leche's cached tier keeps four
binder-telescope loops that its PURE tier writes as per-binder chains, and
`ConLeche/Verify/BinderLoop.lean` proves all four sound against the chained
bodies; `Verify/Cached/BinderLoopC.lean` relates the cached spelling to those
pure mirrors walk by walk.  A loop peels the whole chain, opens every domain
against the free variables it has introduced in ONE `instantiateList`, and
rebuilds outward with `abstractRange` — where the chain paid one
`instantiate1` per binder per domain and one `abstract1` per binder on the way
out.

The stack is an `Array` pushed outermost-first and consumed by a count
counting down, where con-leche conses a `List` innermost-first and consumes
its head: the same entries in the same order, and `stk[j]`'s index IS
con-leche's `j`.  `fvs` is a push-order `Array` read by `instantiateList` from
the end, which is the same convention the batched β already uses. -/

/-- con-leche: ConLeche/Cached/StateC.lean:318-322 peelFuel — the telescope
loops' own step budget.  con-leche's note says the peel fuel is semantically
transparent: on exhaustion the leaf phase hands the residual chain back to the
knot, which is the chained spec's next step. -/
def peelFuel : Nat := 16777216

/-- con-leche: ConLeche/Cached/CoreC.lean:210-221 inferLamsOutI — the λ
loop's OUTWARD rebuild: `abstractRange` closes each stored domain over the `j`
free variables below it and the ∀ node is rebuilt, innermost binder first. -/
def inferLamsOut (d : Nat) (stk : Array EIdx) (n : Nat) (cur : EIdx) :
    AM EIdx := do
  if n = 0 then pure cur
  else do
    let j := n - 1
    let tyAbs ← abstractRangeFast coreWalkFuel stk[j]! d j 0
    let nd ← internForallEE tyAbs cur
    inferLamsOut d stk j nd
termination_by n

/-- con-leche: ConLeche/Cached/CoreC.lean:1405-1419 inferLamsLeafI — the λ
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferLamsLeaf_bridge, then delete this line
loop's LEAF: open the residual body against every free variable at once,
infer it, and hand the outward rebuild its starting point. -/
def inferLamsLeaf (r : CoreFnsA) (d : Nat) (t : EIdx) (k : Nat)
    (fvs : Array EIdx) (stk : Array EIdx) : AM EIdx := do
  let ob ← instantiateListFast coreWalkFuel t fvs 0
  let bt ← r.infer (d + k) ob
  let cur ← abstractRangeFast coreWalkFuel bt d k 0
  inferLamsOut d stk stk.size cur

/-- con-leche: ConLeche/Cached/CoreC.lean:1421-1442 inferLamsI — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferLams_bridge, then delete this line
λ-telescope inference loop: peel a consecutive run of λ binders, opening each
domain against the free variables introduced so far and checking that it is a
type, then hand the residual to the leaf. -/
def inferLams (r : CoreFnsA) (d : Nat) :
    Nat → EIdx → Nat → Array EIdx → Array EIdx → AM EIdx
  | 0, t, k, fvs, stk => inferLamsLeaf r d t k fvs stk
  | peel + 1, t, k, fvs, stk => do
    -- The peel's test is a tag read off the handle word and the binder
    -- PROJECTION (task #97-P6-10).
    if t.tag != ETag.lam then inferLamsLeaf r d t k fvs stk
    else
      match ← viewBind t with
      | none => failDanglingE
      | some (ty, body) => do
        let tyo ← instantiateListFast coreWalkFuel ty fvs 0
        let tty ← r.infer (d + k) tyo
        let w ← r.whnf (d + k) tty
        -- The codomain sort's LEVEL is not used — the `.lam` case wants only
        -- that the type's whnf IS a sort, which the handle's own tag says;
        -- the node is not read (as the port's `infer_lams`, task #119).
        if w.tag == ETag.sort then do
          let fv ← internFVarE (d + k) tyo
          inferLams r d peel body (k + 1) (fvs.push fv) (stk.push tyo)
        else fail (.invalid "expected a sort")

/-- con-leche: ConLeche/Cached/CoreC.lean:223-234 inferPisOutI — the ∀
loop's outward `imax` fold, innermost binder first (con-leche's task #272:
the fold reads no per-node datum). -/
def inferPisOut (stk : Array LIdx) (n : Nat) (v : LIdx) : AM LIdx := do
  if n = 0 then pure v
  else do
    let j := n - 1
    let v2 ← internLNode (.imax stk[j]! v)
    inferPisOut stk j v2
termination_by n

/-- con-leche: ConLeche/Cached/CoreC.lean:1444-1456 inferPisLeafI — the ∀
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferPisLeaf_bridge, then delete this line
loop's LEAF: open the residual codomain against every free variable at once,
infer its sort and fold `imax` outward. -/
def inferPisLeaf (r : CoreFnsA) (fe : IFEnv) (d : Nat)
    (t : EIdx) (k : Nat) (fvs : Array EIdx) (stk : Array LIdx) :
    AM EIdx := do
  let ob ← instantiateListFast coreWalkFuel t fvs 0
  let bt ← r.infer (d + k) ob
  let v ← ensureSort r fe (d + k) bt
  let iv ← inferPisOut stk stk.size v
  internSortE iv

/-- con-leche: ConLeche/Cached/CoreC.lean:1458-1480 inferPisI — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferPis_bridge, then delete this line
∀-telescope inference loop, `inferLams`' twin: peel the chain, open each
domain in bulk, and stack the binder's SORT (for the `imax` fold). -/
def inferPis (r : CoreFnsA) (fe : IFEnv) (d : Nat) :
    Nat → EIdx → Nat → Array EIdx → Array LIdx → AM EIdx
  | 0, t, k, fvs, stk => inferPisLeaf r fe d t k fvs stk
  | peel + 1, t, k, fvs, stk => do
    if t.tag != ETag.forallE then inferPisLeaf r fe d t k fvs stk
    else
      match ← viewBind t with
      | none => failDanglingE
      | some (ty, body) => do
        let tyo ← instantiateListFast coreWalkFuel ty fvs 0
        let tty ← r.infer (d + k) tyo
        let w ← r.whnf (d + k) tty
        if w.tag == ETag.sort then
          match ← viewSort w with
          | none => failDanglingE
          | some u => do
            let fv ← internFVarE (d + k) tyo
            inferPis r fe d peel body (k + 1) (fvs.push fv) (stk.push u)
        else fail (.invalid "expected a sort")

/-- con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI — the `.lam`
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferLam_bridge, then delete this line
clause: the binder's own domain is checked to be a type here (which is why the
loop starts at `k = 1` with one free variable and a one-entry stack), and the
rest of the λ-chain is peeled by `inferLams`. -/
def inferLam (r : CoreFnsA) (depth : Nat) (ty body : EIdx) : AM EIdx := do
  let tty ← r.infer depth ty
  let w ← r.whnf depth tty
  if w.tag == ETag.sort then do
    let fv ← internFVarE depth ty
    inferLams r depth peelFuel body 1 #[fv] #[ty]
  else fail (.invalid "expected a sort")

/-- con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferForall_bridge, then delete this line
`.forallE` clause, `inferLam`'s twin. -/
def inferForall (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (ty body : EIdx) : AM EIdx := do
  let tty ← r.infer depth ty
  let w ← r.whnf depth tty
  if w.tag == ETag.sort then
    match ← viewSort w with
    | none => failDanglingE
    | some u => do
      let fv ← internFVarE depth ty
      inferPis r fe depth peelFuel body 1 #[fv] #[u]
  else fail (.invalid "expected a sort")

/-! ### The application spine's inference

con-leche's own CACHED-tier clauses `Cached/CoreC.lean:1011-1042 inferSpineI`
and `:1044-1091 inferSpineIOI` (task #97-P6-9).  The spec-shaped `.app` clause
infers the type of every PREFIX of the spine and `whnf`s it, which is `O(n²)`
node work down a long application; these walk the head's type once and carry
the pending substitutions in an accumulator, opening each domain in ONE
`instantiateList`.  The bridge cites `Verify/BetaSpine.lean:1566
inferSpine_sound` and `:1576 inferSpine_sound_body`.

The `whnf` re-entry at a non-∀ head is where the chained clause's own `whnf`
sits, and it RESETS the accumulator, because the reduct is already the opened
type. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1213-1219 defeqArg
con-leche: ConLeche/Cached/CoreC.lean:1237-1241 defeqArgI — **the argument check
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.defeqArg_bridge, then delete this line
of a full-grade application** (official `infer_app`): the type of an
`eagerReduce _ _` argument is compared with the domain in the eager tower
(`CoreFnsA.defeqE`), every other argument's in the knot's own. -/
def defeqArg (r : CoreFnsA) (depth : Nat) (a ta ty : EIdx) : AM Bool := do
  if ← isEagerReduce a then r.defeqE depth ta ty else r.defeq depth ta ty

/-- con-leche: ConLeche/Cached/CoreC.lean:1243-1273 inferSpineI — walk the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferSpine_bridge, then delete this line
head's type down the argument vector at the FULL grade. -/
def inferSpine (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (ty : EIdx) (acc : Array EIdx) (args : Array EIdx) (i : Nat) : AM EIdx := do
  if hi : i < args.size then do
    let a := args[i]
    if ty.tag == ETag.forallE then
      match ← viewBind ty with
      | none => failDanglingE
      | some (dom, body) => do
        let dom2 ← instantiateListFast coreWalkFuel dom acc 0
        let ta ← r.infer depth a
        if !(← defeqArg r depth a ta dom2) then
          fail (.invalid "application type mismatch")
        else inferSpine r fe depth body (acc.push a) args (i + 1)
    else do
      let ty2 ← instantiateListFast coreWalkFuel ty acc 0
      let w ← r.whnf depth ty2
      if w.tag == ETag.forallE then
        match ← viewBind w with
        | none => failDanglingE
        | some (dom, body) => do
          let ta ← r.infer depth a
          if !(← defeqArg r depth a ta dom) then
            fail (.invalid "application type mismatch")
          else inferSpine r fe depth body #[a] args (i + 1)
      else fail (.invalid "function expected")
  else instantiateListFast coreWalkFuel ty acc 0
termination_by args.size - i

/-- con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI — the `.app`
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferApp_bridge, then delete this line
clause: the head is inferred ONCE and the whole argument vector is run through
`inferSpine`. -/
def inferApp (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (e : EIdx) : AM EIdx := do
  let hv ← headAndArgs e
  let tf ← r.infer depth hv.1
  inferSpine r fe depth tf #[] hv.2 0

/-- con-leche: ConLeche/Cached/CoreC.lean:1275-1295 inferSpineIOI — the io
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferSpineIO_bridge, then delete this line
lane's spine walk, official's `infer_only`: the head's type is walked through
the arguments with no argument inference and no domain comparison
(con-leche's tasks #342, #346). -/
def inferSpineIO (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (ty : EIdx) (acc : Array EIdx) (args : Array EIdx) (i : Nat) : AM EIdx := do
  if hi : i < args.size then do
    let a := args[i]
    if ty.tag == ETag.forallE then
      match ← viewBind ty with
      | none => failDanglingE
      | some (_, body) => inferSpineIO r fe depth body (acc.push a) args (i + 1)
    else do
      let ty2 ← instantiateListFast coreWalkFuel ty acc 0
      let w ← r.whnf depth ty2
      if w.tag == ETag.forallE then
        match ← viewBind w with
        | none => failDanglingE
        | some (_, body) => inferSpineIO r fe depth body #[a] args (i + 1)
      else fail (.invalid "function expected")
  else instantiateListFast coreWalkFuel ty acc 0
termination_by args.size - i

/-- con-leche: ConLeche/Cached/CoreC.lean:1590-1640 inferBodyIOI — the io
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferAppIOAt_bridge, then delete this line
lane's `.app` clause. -/
def inferAppIOAt (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (e : EIdx) : AM EIdx := do
  let hv ← headAndArgs e
  let tf ← r.infer depth hv.1
  inferSpineIO r fe depth tf #[] hv.2 0

/-- con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI — the `.proj`
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.inferProj_bridge, then delete this line
clause, shared by `inferBody` and `inferBodyIO` (con-leche's `inferBodyIOI`
dispatches its `.proj` to `inferBodyI`'s): the subject type's head must be the
node's structure at the table's arity (official `infer_proj`; these guards are
the retired annotate pass's, con-leche's task #342 L-CK), the projection's
guard holds at this use (`checkProjGuard`), and a miss is `projMissError`'s
verdict. -/
def inferProj (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (sn : NIdx) (i : Nat)
    (pe : EIdx) : AM EIdx := do
  let te ← r.whnf depth (← r.infer depth pe)
  let hh ← getAppFn coreWalkFuel te
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T us => do
      match fe.findProj? T i with
      | some entry => do
        let targs ← getAppArgs coreWalkFuel te
        if T != sn then
          fail (.invalid "invalid projection: the node names another structure")
        else if targs.length != entry.numParams then
          fail (.invalid "projection parameter mismatch")
        else
          match ← viewLsLen us with
          | none => failDanglingLs
          | some usl =>
          if usl = entry.levelParams.length then do
            checkProjGuard r fe entry us
            entry.typeAt us targs pe
          else fail (.notImplemented "projection without a native entry")
      | none => do
        let hasTable := (fe.findTable? T).isSome
        let targs ← getAppArgs coreWalkFuel te
        fail (projMissError fe hasTable T sn i targs.length)
    | _ => failDanglingE
  else fail (.invalid "invalid projection: not a structure-like type, or no such field")

/-- con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody — the inference
body.  The `.const` clause reads the stored type through `constTyAt`, so a
constant inferred twice at the same levels pays the level substitution
once. -/
def inferBody (r : CoreFnsA) (fe : IFEnv) :
    Nat → EIdx → AM EIdx :=
  fun depth e => do
    match ← view e with
    | .sort u => do
      let su ← internLNode (.succ u)
      internE (.sort su)
    | .fvar idx ty =>
      -- scope check at the leaf of a traversal that happens anyway
      if idx < depth then pure ty
      else fail (.invalid "free variable out of scope")
    | .const n us => do
      match fe.find? n with
      | none => do
        let err ← unknownConstError n
        fail err
      | some ci => do
        let cv := ci.toConstantVal
        let usl ← viewLs us
        if usl.length != cv.levelParams.length then do
          fail (.invalid "incorrect number of universe levels")
        else constTyAt cv us
    | .lit (.natVal n) => do
      if ← natLitStored fe then do
        -- a numeral entering the checker is bounded by the run's maximum
        -- `Nat` size (con-leche's cached `inferBodyI`, official `infer_lit`)
        if ← natSizeRefused n then
          fail (.invalid "the kernel refused a `Nat` numeral because its size exceeds the maximum; raise it with --max-nat-size")
        else do
          let nn ← pinNat
          constE nn
      else fail (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if ← strLitStored fe then do
        let sn ← pinString
        constE sn
      else fail (.notImplemented
        "string literals before the String support declarations")
    -- **The binder-telescope loops** (task #97-P6-12), con-leche's own
    -- `Cached/CoreC.lean:1292-1389 inferBodyI`: the whole chain is peeled and
    -- opened in bulk rather than one binder at a time through the knot.
    | .forallE ty body => inferForall r fe depth ty body
    | .lam ty body => inferLam r depth ty body
    -- **The batched spine** (task #97-P6-9), con-leche's own
    -- `Cached/CoreC.lean:1292-1389 inferBodyI`.
    | .app _ _ => inferApp r fe depth e
    | .proj sn i pe => inferProj r fe depth sn i pe
    | .letE ty v b => do
      -- official `infer_let` (con-leche's task #342): the `let`'s type is a
      -- type, the value's type matches it, then the body at the value
      let tty ← r.infer depth ty
      let _ ← ensureSort r fe depth tty
      let tv ← r.infer depth v
      if !(← r.defeq depth tv ty) then
        fail (.invalid "let value type mismatch")
      else do
        let ob ← instantiate1Fast coreWalkFuel b v 0
        r.infer depth ob
    | .bvar _ =>
      fail (.notImplemented "inferType beyond the supported fragment")

/-- con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO — **the io
inference body**, official's `infer_only`: `inferBody` with the application,
∀, λ and `let` clauses changed — no argument check (`inferSpineIO`), the
binder clauses chained, no domain-sort run at the λ, and a `let` infers its
body at its value with no check of the type or the value. -/
def inferBodyIO (r : CoreFnsA) (fe : IFEnv) :
    Nat → EIdx → AM EIdx :=
  fun depth e => do
    match ← view e with
    | .sort u => do
      let su ← internLNode (.succ u)
      internE (.sort su)
    | .fvar idx ty =>
      if idx < depth then pure ty
      else fail (.invalid "free variable out of scope")
    | .const n us => do
      match fe.find? n with
      | none => do
        let err ← unknownConstError n
        fail err
      | some ci => do
        let cv := ci.toConstantVal
        match ← viewLsLen us with
        | none => failDanglingLs
        | some usl =>
        if usl != cv.levelParams.length then do
          fail (.invalid "incorrect number of universe levels")
        else constTyAt cv us
    | .lit (.natVal n) => do
      if ← natLitStored fe then do
        -- a numeral entering the checker is bounded by the run's maximum
        -- `Nat` size (con-leche's cached `inferBodyI`, official `infer_lit`)
        if ← natSizeRefused n then
          fail (.invalid "the kernel refused a `Nat` numeral because its size exceeds the maximum; raise it with --max-nat-size")
        else do
          let nn ← pinNat
          constE nn
      else fail (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if ← strLitStored fe then do
        let sn ← pinString
        constE sn
      else fail (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body => do
      let hh ← r.whnf depth (← r.infer depth ty)
      if hh.tag == ETag.sort then
        match ← view hh with
        | .sort u => do
          let fv ← internE (.fvar depth ty)
          let ob ← instantiate1Fast coreWalkFuel body fv 0
          let v ← ensureSort r fe (depth + 1) (← r.infer (depth + 1) ob)
          let iu ← internLNode (.imax u v)
          internE (.sort iu)
        | _ => fail (.invalid "expected a sort")
      else fail (.invalid "expected a sort")
    | .lam ty body => do
      -- con-leche's task #168 stage 2: no domain-sort run at the io grade
      let fv ← internE (.fvar depth ty)
      let ob ← instantiate1Fast coreWalkFuel body fv 0
      let bt ← r.infer (depth + 1) ob
      inferLamResult ty bt depth
    -- **The batched spine at the io grade** (task #97-P6-9), con-leche's own
    -- `Cached/CoreC.lean:1136-1184 inferBodyIOI`: no argument check
    -- (official's `infer_only`, con-leche's task #346).
    | .app _ _ => inferAppIOAt r fe depth e
    | .proj sn i pe => inferProj r fe depth sn i pe
    | .letE _ v b => do
      -- official `infer_let` at `infer_only`: the body at its value, no check
      -- of the type or the value (con-leche's task #342 R-C)
      let ob ← instantiate1Fast coreWalkFuel b v 0
      r.infer depth ob
    | .bvar _ =>
      fail (.notImplemented "inferType beyond the supported fragment")

/-! ## Definitional equality

con-leche's `Core.lean`:2373-2697. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1411-1424 boolTrueShortcut — **the
eq-true shortcut** (the divergence audit's E2): the left side is fully
head-normalised and the verdict is `true` iff the reduct is `Bool.true`. -/
def boolTrueShortcut (r : CoreFnsA) (depth : Nat) (a : EIdx) : AM Bool := do
  let w ← r.whnf depth a
  isBoolTrue w

/-- con-leche: ConLeche/Kernel/Core.lean:1426-1455 defeqSpine —
levels-and-spine congruence for two applications of the *same* stored
constant (the lazy delta same-head short-circuit, official's
`try_eq_const_app`).  The arguments are compared **last to first**, as
official `is_def_eq_args` walks `app_arg`/`app_fn` from the outermost
application inwards. -/
def defeqSpine (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM Bool := do
  let hh ← getAppFn coreWalkFuel a
  if hh.tag == ETag.const then
    match ← view hh with
    | .const n us =>
      let hh ← getAppFn coreWalkFuel b
      if hh.tag == ETag.const then
        match ← view hh with
        | .const n' us' => do
          let aa ← getAppArgs coreWalkFuel a
          let bb ← getAppArgs coreWalkFuel b
          if n = n' ∧ aa.length = bb.length then
            match ← lvlsEq? us us' with
            | some true => defEqList r fe depth aa.reverse bb.reverse
            | _ => pure false
          else pure false
        | _ => pure false
      else pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1663-1698 lazyDeltaReduction — the
literal-acceleration guard: *both* sides free of free variables, mirroring
the official kernel's `lazy_delta_reduction`.  The arena reads the `O(1)`
eager per-node fvar range where the specification walks. -/
def defeqNoFvars (a b : EIdx) : AM Bool := do
  if ← hasFvarFast coreWalkFuel a then pure false
  else do
    let y ← hasFvarFast coreWalkFuel b
    pure !y

/-- con-leche: ConLeche/Kernel/Core.lean:1663-1698 lazyDeltaReduction — **the
literal fold's guard**: the eager flag (official
`m_eager_reduce`) or both sides free of free variables — official's
`(!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce`.  Under the flag the
sides are not walked. -/
def lazyFoldOk (eager : Bool) (a b : EIdx) : AM Bool := do
  if eager then pure true else defeqNoFvars a b

/-! ### The binder-telescope congruence -/

/-- con-leche: ConLeche/Kernel/Core.lean:1457-1460 bindersFuel — the
binder-telescope descent's own budget (`2^62`; `@[noinline]` for con-leche's
reason: a literal at or above `2^32` is parsed from its decimal string at
every use otherwise). -/
@[noinline] def bindersFuel : Nat := 4611686018427387904  -- 2^62

/-- con-leche: ConLeche/Kernel/Core.lean:1462-1469 defeqBindersInner
con-leche: ConLeche/Cached/CoreC.lean:1648-1657 defeqBindersInnerI — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.defeqBindersInner_bridge, then delete this line
innermost level of `defeqBinders`: the opened bodies, and for two
λ-telescopes at the verified mode their FULL-grade types (the λ check). -/
def defeqBindersInner (mode : CheckMode) (r : CoreFnsA) (lam : Bool) (depth : Nat)
    (b₁ b₂ : EIdx) : AM Bool := do
  if !(← r.defeq (depth + 1) b₁ b₂) then pure false
  else if lam && mode.verifiedChecks then do
    let t₁ ← r.infer (depth + 1) b₁
    let t₂ ← r.infer (depth + 1) b₂
    r.defeq (depth + 1) t₁ t₂
  else pure true

/-- con-leche: ConLeche/Kernel/Core.lean:1471-1475 defeqDomain
con-leche: ConLeche/Cached/CoreC.lean:1659-1665 defeqDomainI — one level's
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.defeqDomain_bridge, then delete this line
domains in `defeqBinders`: the same RAW domain handle is `true`; otherwise the
left domain, opened over the variables so far (`fvs`, push order) in one
`instantiateList`, against the opened right one `dom₂`. -/
def defeqDomain (r : CoreFnsA) (depth : Nat) (fvs : Array EIdx) (ty₁ ty₂ dom₂ : EIdx) :
    AM Bool := do
  if ty₁ == ty₂ then pure true
  else do
    let dom₁ ← instantiateListFast coreWalkFuel ty₁ fvs 0
    r.defeq depth dom₁ dom₂

/-- con-leche: ConLeche/Kernel/Core.lean:1477-1500 defeqBinders
con-leche: ConLeche/Cached/CoreC.lean:1667-1683 defeqBindersI —
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.defeqBinders_bridge, then delete this line
**binder-telescope congruence** (the official kernel's `is_def_eq_binding`):
two ∀-telescopes (`lam = false`) or two λ-telescopes (`lam = true`) are peeled
together while both bodies are binders of that kind (`binderPair?`).  The
bodies stay RAW: `fvs` holds the variables of the levels above in push order
(outermost first, the specification's list reversed), and every opening is
one `instantiateList` over it.  Per level the right domain is opened (`dom₂`),
the domains are compared by `defeqDomain`, and the variable
`fvar depth dom₂` is pushed; at the innermost level both bodies are opened
once and compared by `defeqBindersInner`. -/
def defeqBinders (mode : CheckMode) (r : CoreFnsA) (lam : Bool) :
    Nat → Nat → Array EIdx → EIdx → EIdx → EIdx → EIdx → AM Bool
  | fuel, depth, fvs, ty₁, body₁, ty₂, body₂ => do
    let dom₂ ← instantiateListFast coreWalkFuel ty₂ fvs 0
    if !(← defeqDomain r depth fvs ty₁ ty₂ dom₂) then pure false
    else do
    let fv ← internFVarE depth dom₂
    match fuel with
    | 0 => do
      let b₁ ← instantiateListFast coreWalkFuel body₁ (fvs.push fv) 0
      let b₂ ← instantiateListFast coreWalkFuel body₂ (fvs.push fv) 0
      defeqBindersInner mode r lam depth b₁ b₂
    | fuel + 1 =>
      match ← binderPair? lam body₁ body₂ with
      | some (ty₁', body₁', ty₂', body₂') =>
        defeqBinders mode r lam fuel (depth + 1) (fvs.push fv) ty₁' body₁' ty₂' body₂'
      | none => do
        let b₁ ← instantiateListFast coreWalkFuel body₁ (fvs.push fv) 0
        let b₂ ← instantiateListFast coreWalkFuel body₂ (fvs.push fv) 0
        defeqBindersInner mode r lam depth b₁ b₂

/-- con-leche: ConLeche/Kernel/Core.lean:1502-1524 quickDefEq
con-leche: ConLeche/Cached/CoreC.lean:1685-1701 quickDefEqI — **the easy
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.quickDefEq_bridge, then delete this line
cases** (the official kernel's `quick_is_def_eq`): the syntactic fast path,
and the pairs decided on the spot — two sorts, two literals, two `∀`s and two
`λ`s (binder-telescope congruence, `defeqBinders`).  `none` is
"not an easy case".  The pair match is on the two handles' TAGS first: only a
pair of equal tags among the four kinds is viewed. -/
def quickDefEq (mode : CheckMode) (r : CoreFnsA) (depth : Nat) (a b : EIdx) :
    AM (Option Bool) := do
  if a == b then pure (some true) else do
  let ta := a.tag
  if ta != b.tag then pure none
  else if ta == ETag.sort || ta == ETag.lit || ta == ETag.forallE ||
      ta == ETag.lam then
    match ← view a, ← view b with
    | .sort u, .sort v => do
      let ok ← liftFueled "level comparison" (← lvlEq? u v)
      pure (some ok)
    | .lit l₁, .lit l₂ => pure (some (l₁ == l₂))
    | .forallE ty₁ body₁, .forallE ty₂ body₂ => do
      let ok ← defeqBinders mode r false bindersFuel depth #[] ty₁ body₁ ty₂ body₂
      pure (some ok)
    | .lam ty₁ body₁, .lam ty₂ body₂ => do
      let ok ← defeqBinders mode r true bindersFuel depth #[] ty₁ body₁ ty₂ body₂
      pure (some ok)
    | _, _ => pure none
  else pure none

/-- con-leche: ConLeche/Kernel/Core.lean:1526-1530 Expr.isNatZero — `Nat.zero`
or the literal `0` (official `is_nat_zero`). -/
def isNatZero (e : EIdx) : AM Bool := do
  if e.tag == ETag.lit then
    match ← view e with
    | .lit (.natVal n) => pure (n == 0)
    | _ => pure false
  else if e.tag == ETag.const then
    match ← view e with
    | .const c us => do
      let el ← emptyLevels
      let nz ← pinNatZero
      pure (c == nz && us == el)
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1532-1537 Expr.natPred? — the
predecessor of a successor form (official `is_nat_succ`): a nonzero literal
(its predecessor literal interned), or `Nat.succ x`. -/
def natPred? (e : EIdx) : AM (Option EIdx) := do
  if e.tag == ETag.lit then
    match ← view e with
    | .lit (.natVal (n + 1)) => do
      let l ← internE (.lit (.natVal n))
      pure (some l)
    | _ => pure none
  else if e.tag == ETag.app then
    match ← viewApp e with
    | none => failDanglingE
    | some (f, x) =>
      if f.tag == ETag.const then
        match ← view f with
        | .const c us => do
          let el ← emptyLevels
          let ns ← pinNatSucc
          if c == ns && us == el then pure (some x) else pure none
        | _ => pure none
      else pure none
  else pure none

/-- con-leche: ConLeche/Kernel/Core.lean:1539-1551 defeqOffset
con-leche: ConLeche/Cached/CoreC.lean:1703-1713 defeqOffsetI — **offsets**
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.defeqOffset_bridge, then delete this line
(the official kernel's `is_def_eq_offset`): two zeros are equal, two
successor forms compare their predecessors; two literals are left to
`quickDefEq`.  (`Expr.isLit` is the tag test.)  The second side's
predecessor is only computed when the first has one, which is the pure
`match`'s verdict. -/
def defeqOffset (r : CoreFnsA) (depth : Nat) (a b : EIdx) : AM (Option Bool) := do
  if (← isNatZero a) && (← isNatZero b) then pure (some true)
  else if a.tag == ETag.lit && b.tag == ETag.lit then pure none
  else
    match ← natPred? a with
    | none => pure none
    | some x =>
      match ← natPred? b with
      | none => pure none
      | some y => do
        let ok ← r.defeq depth x y
        pure (some ok)

/-- con-leche: ConLeche/Kernel/Core.lean:1553-1557 Expr.headIsProj — is the
head of the application spine a projection? -/
def headIsProj (e : EIdx) : AM Bool := do
  let h ← getAppFn coreWalkFuel e
  pure (h.tag == ETag.proj)

/-- con-leche: ConLeche/Kernel/Core.lean:1559-1567 tryUnfoldProjApp
con-leche: ConLeche/Cached/CoreC.lean:1715-1722 tryUnfoldProjAppI — official
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.tryUnfoldProjApp_bridge, then delete this line
`try_unfold_proj_app`: a projection-headed term through the FULL `whnfCore`;
`some` whenever that changed it. -/
def tryUnfoldProjApp (r : CoreFnsA) (depth : Nat) (e : EIdx) :
    AM (Option EIdx) := do
  if ← headIsProj e then do
    let e' ← r.whnfCore false depth e
    if e' == e then pure none else pure (some e')
  else pure none

/-- con-leche: ConLeche/Kernel/Core.lean:1569-1576 DeltaStep — the outcome of
one lazy-delta step (official `reduction_status`), over handles. -/
inductive DeltaStepA where
  | cont (a b : EIdx)
  | eq
  | diff
  | unknown

/-- con-leche: ConLeche/Kernel/Core.lean:1578-1583 deltaQuick
con-leche: ConLeche/Cached/CoreC.lean:1724-1730 deltaQuickI — the end of a
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.deltaQuick_bridge, then delete this line
lazy-delta step: `quickDefEq` on the new pair. -/
def deltaQuick (mode : CheckMode) (r : CoreFnsA) (depth : Nat) (a b : EIdx) :
    AM DeltaStepA := do
  match ← quickDefEq mode r depth a b with
  | some true => pure .eq
  | some false => pure .diff
  | none => pure (.cont a b)

/-- con-leche: ConLeche/Kernel/Core.lean:1585-1646 lazyDeltaStep
con-leche: ConLeche/Cached/CoreC.lean:1732-1780 lazyDeltaStepI — **one
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.lazyDeltaStep_bridge, then delete this line
lazy-delta step** (the official kernel's `lazy_delta_reduction_step`): unfold
the side with the greater height (both at equal hints, after the same-head
spine shortcut at equal *regular* hints), put the unfolded side through the
CHEAP `whnfCore`, and finish with `quickDefEq`; with one side unfoldable, a
projection application on the other side is reduced instead. -/
def lazyDeltaStep (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) : AM DeltaStepA := do
  let ua ← unfoldableHead fe a
  let ub ← unfoldableHead fe b
  match ua, ub with
  | false, false => pure .unknown
  | true, false =>
    match ← tryUnfoldProjApp r depth b with
    | some b₂ => deltaQuick mode r depth a b₂
    | none =>
      match ← unfoldDefinition fe a with
      | some a₂ => do
        let a₃ ← r.whnfCore true depth a₂
        deltaQuick mode r depth a₃ b
      | none => pure .unknown
  | false, true =>
    match ← tryUnfoldProjApp r depth a with
    | some a₂ => deltaQuick mode r depth a₂ b
    | none =>
      match ← unfoldDefinition fe b with
      | some b₂ => do
        let b₃ ← r.whnfCore true depth b₂
        deltaQuick mode r depth a b₃
      | none => pure .unknown
  | true, true => do
    let ha ← headHint fe a
    let hb ← headHint fe b
    if ReducibilityHint.lt hb ha then
      match ← unfoldDefinition fe a with
      | some a₂ => do
        let a₃ ← r.whnfCore true depth a₂
        deltaQuick mode r depth a₃ b
      | none => pure .unknown
    else if ReducibilityHint.lt ha hb then
      match ← unfoldDefinition fe b with
      | some b₂ => do
        let b₃ ← r.whnfCore true depth b₂
        deltaQuick mode r depth a b₃
      | none => pure .unknown
    else do
      let sch ← sameConstHeads a b
      let sp ← if ReducibilityHint.sameRegular ha hb && sch then
          defeqSpine r fe depth a b else pure false
      if sp then pure .eq
      else
        match ← unfoldDefinition fe a, ← unfoldDefinition fe b with
        | some a₂, some b₂ => do
          let a₃ ← r.whnfCore true depth a₂
          let b₃ ← r.whnfCore true depth b₂
          deltaQuick mode r depth a₃ b₃
        | _, _ => pure .unknown

/-- con-leche: ConLeche/Kernel/Core.lean:1648-1653 LazyRes — the outcome of the
lazy-delta loop, over handles: a verdict, or the pair it got stuck on. -/
inductive LazyResA where
  | verdict (v : Bool)
  | unknown (a b : EIdx)

/-- con-leche: ConLeche/Kernel/Core.lean:1655-1661 defeqLoopFuel — step
budget of the two lazy-delta loops.  Exhaustion is an internal error, never a
verdict.  Effectively unbounded since con-leche task #330: `2^62`. -/
@[noinline] def defeqLoopFuel : Nat := 4611686018427387904  -- 2^62

/-- con-leche: ConLeche/Kernel/Core.lean:1663-1698 lazyDeltaReduction
con-leche: ConLeche/Cached/CoreC.lean:1782-1807 lazyDeltaReductionI — **the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.lazyDeltaReduction_bridge, then delete this line
lazy-delta loop** (the official kernel's `lazy_delta_reduction`): per
iteration the offset check, the fvar-guarded literal acceleration — whose
reduct restarts the comparison (`defeq`) — then one `lazyDeltaStep`, each
unfolding one iteration on the loop's own budget. -/
def lazyDeltaReduction (mode : CheckMode) (eager : Bool) (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) : Nat → EIdx → EIdx → AM LazyResA
  | 0, _, _ => fail (.internal "fuel exhausted: defeq loop")
  | n + 1, a, b => do
    match ← defeqOffset r depth a b with
    | some v => pure (.verdict v)
    | none =>
    let nf ← lazyFoldOk eager a b
    match ← (if nf then reduceNat r fe depth a else pure none) with
    | some a₂ => do
      let v ← r.defeq depth a₂ b
      pure (.verdict v)
    | none =>
    match ← (if nf then reduceNat r fe depth b else pure none) with
    | some b₂ => do
      let v ← r.defeq depth a b₂
      pure (.verdict v)
    | none =>
    match ← lazyDeltaStep mode r fe depth a b with
    | .cont a' b' => lazyDeltaReduction mode eager r fe depth n a' b'
    | .eq => pure (.verdict true)
    | .diff => pure (.verdict false)
    | .unknown => pure (.unknown a b)

/-- con-leche: ConLeche/Kernel/Core.lean:1700-1718 lazyDeltaProjReduction
con-leche: ConLeche/Cached/CoreC.lean:1809-1824 lazyDeltaProjReductionI —
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.lazyDeltaProjReduction_bridge, then delete this line
**`a.i =?= b.i` by its scrutinees** (the official kernel's
`lazy_delta_proj_reduction`): lazy-delta steps on the two scrutinees; when
neither unfolds any more (or the step found them different), the projection
is tried on both and only the projected fields are compared; failing that,
the scrutinees themselves. -/
def lazyDeltaProjReduction (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (sn : NIdx) (i : Nat) : Nat → EIdx → EIdx → AM Bool
  | 0, _, _ => fail (.internal "fuel exhausted: lazy delta projection loop")
  | n + 1, a, b => do
    match ← lazyDeltaStep mode r fe depth a b with
    | .cont a' b' => lazyDeltaProjReduction mode r fe depth sn i n a' b'
    | .eq => pure true
    | .diff | .unknown =>
      match ← reduceProjCore mode r fe depth sn i a with
      | some x =>
        match ← reduceProjCore mode r fe depth sn i b with
        | some y => r.defeq depth x y
        | none => r.defeq depth a b
      | none => r.defeq depth a b

/-- con-leche: ConLeche/Kernel/Core.lean:1720-1729 defeqProjPair
con-leche: ConLeche/Cached/CoreC.lean:1826-1835 defeqProjPairI — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.defeqProjPair_bridge, then delete this line
proj/proj check of `is_def_eq_core`: two projections at the same slot go
through `lazyDeltaProjReduction` on their scrutinees. -/
def defeqProjPair (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) : AM Bool := do
  if a.tag == ETag.proj && b.tag == ETag.proj then
    match ← view a, ← view b with
    | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ =>
      if s₁ == s₂ && i₁ == i₂ then
        lazyDeltaProjReduction mode r fe depth s₁ i₁ defeqLoopFuel e₁ e₂
      else pure false
    | _, _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1731-1798 defeqStuck
con-leche: ConLeche/Cached/CoreC.lean:1837-1885 defeqStuckI — **the stuck
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.defeqStuck_bridge, then delete this line
comparison** (the tail of the official kernel's `is_def_eq_core`): a string
literal against `String.ofList`, the same free variable, the same constant at
equivalent levels, the application spine, η on a one-sided λ; every failing
arm ends in `stuckIrrel`. -/
def defeqStuck (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) : AM Bool := do
  match ← view a, ← view b with
  -- a string literal against a unary `String.ofList` application
  | .lit l, .app fo _ => do
    match l with
    | .strVal st =>
      if fo.tag == ETag.const then
        match ← view fo with
        | .const cO usO => do
          let el ← emptyLevels
          let sl ← pinStringOfList
          if cO = sl ∧ usO = el ∧ (← strLitStored fe) then do
            let c ← strLitToConstructor st
            r.defeq depth c b
          else stuckIrrel r fe depth a b
        | _ => stuckIrrel r fe depth a b
      else stuckIrrel r fe depth a b
    | _ => stuckIrrel r fe depth a b
  | .app fo _, .lit l => do
    match l with
    | .strVal st =>
      if fo.tag == ETag.const then
        match ← view fo with
        | .const cO usO => do
          let el ← emptyLevels
          let sl ← pinStringOfList
          if cO = sl ∧ usO = el ∧ (← strLitStored fe) then do
            let c ← strLitToConstructor st
            r.defeq depth a c
          else stuckIrrel r fe depth a b
        | _ => stuckIrrel r fe depth a b
      else stuckIrrel r fe depth a b
    | _ => stuckIrrel r fe depth a b
  | .fvar i _, .fvar j _ =>
    if i == j then pure true else stuckIrrel r fe depth a b
  | .const n us, .const n' us' => do
    if n = n' then do
      if ← liftFueled "level comparison" (← lvlsEq? us us') then pure true
      else stuckIrrel r fe depth a b
    else stuckIrrel r fe depth a b
  | .app _ _, .app _ _ => do
    -- stuck applications: **spine-wise** congruence (official's
    -- `is_def_eq_app`), never a recursion on the partial applications
    let aa ← getAppArgs coreWalkFuel a
    let bb ← getAppArgs coreWalkFuel b
    if aa.length = bb.length then do
      let fa ← getAppFn coreWalkFuel a
      let fb ← getAppFn coreWalkFuel b
      if ← r.defeq depth fa fb then do
        if ← defEqList r fe depth aa bb then pure true
        else stuckIrrel r fe depth a b
      else stuckIrrel r fe depth a b
    else stuckIrrel r fe depth a b
  -- one-sided λ: eta, else the stuck fallbacks (two λs never get here:
  -- `quickDefEq` decides them)
  | .lam ty₁ body₁, _ => do
    if ← etaCert mode r fe depth ty₁ body₁ b then pure true
    else stuckIrrel r fe depth a b
  | _, .lam ty₂ body₂ => do
    if ← etaCert mode r fe depth ty₂ body₂ a then pure true
    else stuckIrrel r fe depth a b
  -- distinct whnf-stuck head symbols
  | _, _ => stuckIrrel r fe depth a b

/-- con-leche: ConLeche/Kernel/Core.lean:1800-1858 defeqBody — **the
definitional-equality body** (the official kernel's `is_def_eq_core`, clause
for clause except con-leche task #333's reordering): the syntactic fast path;
the `Bool.true` shortcut; `quickDefEq` and proof irrelevance on the UNREDUCED
pair (so that a proof is never head-normalized to be compared); the CHEAP head
normalization of both sides; `quickDefEq` again; the lazy-delta loop; the proj/proj check; the FULL `whnfCore` of both sides (only when one
of them is projection-headed — elsewhere the two modes agree) and, if either
changed, a restart; and the stuck comparison. -/
def defeqBody (mode : CheckMode) (eager : Bool) (r : CoreFnsA) (fe : IFEnv) :
    Nat → EIdx → EIdx → AM Bool :=
  fun depth a b => do
  if a == b then pure true else do
  -- the eq-true shortcut (E2): right side `Bool.true`, left side fvar-free
  -- or the eager flag set (official `m_eager_reduce`)
  let sc ←
    if (← isBoolTrue b) && (eager || !(← hasFvarFast coreWalkFuel a)) then
      boolTrueShortcut r depth a
    else pure false
  if sc then pure true else do
  match ← quickDefEq mode r depth a b with
  | some v => pure v
  | none =>
  if ← propIrrel r fe depth a b then pure true else do
  let a' ← r.whnfCore true depth a
  let b' ← r.whnfCore true depth b
  match ← quickDefEq mode r depth a' b' with
  | some v => pure v
  | none =>
  match ← lazyDeltaReduction mode eager r fe depth defeqLoopFuel a' b' with
  | .verdict v => pure v
  | .unknown a₁ b₁ =>
  if ← defeqProjPair mode r fe depth a₁ b₁ then pure true else do
  let pa ← headIsProj a₁
  let pb ← headIsProj b₁
  if !pa && !pb then defeqStuck mode r fe depth a₁ b₁ else do
  let a₂ ← r.whnfCore false depth a₁
  let b₂ ← r.whnfCore false depth b₁
  if a₂ == a₁ && b₂ == b₁ then defeqStuck mode r fe depth a₁ b₁
  else r.defeq depth a₂ b₂

/-! ## The knot

con-leche's `Core.lean`:2897-2936 with the memo probes of
`ConLeche/Cached/CoreC.lean`:1877-1906 inlined in the slots (deviation 6):
`memoEI` passes a getter and a setter lambda per table, and two closures per
slot is what DESIGN §3.4 rules out.  The bodies above are pure of memo
logic, which is the property that matters. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:332-345 memoEI — record a
`whnfCore` answer (detach before update, DESIGN §8.4 lesson 14).  A plain
insert, as con-leche's: the table's cap was removed by task #115. -/
@[noinline] def whnfCoreSet (e r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.whnfCoreC
  let s := { s with caches := { s.caches with whnfCoreC := ∅ } }
  set { s with caches := { s.caches with whnfCoreC := mp.insert e r } }

/-- con-leche: ConLeche/Cached/CoreC.lean:326-344 memoEI — record a
CHEAP-mode `whnfCore` answer, in the cheap mode's OWN table (con-leche's
`whnfCoreCheapC`: the two modes differ on a stuck projection). -/
@[noinline] def whnfCoreCheapSet (e r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.whnfCoreCheapC
  let s := { s with caches := { s.caches with whnfCoreCheapC := ∅ } }
  set { s with caches := { s.caches with whnfCoreCheapC := mp.insert e r } }

/-- con-leche: ConLeche/Cached/CoreC.lean:332-345 memoEI — record a `whnf`
answer. -/
@[noinline] def whnfSet (e r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.whnfC
  let s := { s with caches := { s.caches with whnfC := ∅ } }
  set { s with caches := { s.caches with whnfC := mp.insert e r } }

/-- con-leche: ConLeche/Cached/CoreC.lean:332-345 memoEI — record a
full-grade `infer` answer. -/
@[noinline] def inferSet (e r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.inferC
  let s := { s with caches := { s.caches with inferC := ∅ } }
  set { s with caches := { s.caches with inferC := mp.insert e r } }

/-- con-leche: ConLeche/Cached/CoreC.lean:332-345 memoEI — record an
io-grade `infer` answer, in the io grade's OWN table (con-leche's task #170
memo ruling). -/
@[noinline] def inferIOSet (e r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.inferIOC
  let s := { s with caches := { s.caches with inferIOC := ∅ } }
  set { s with caches := { s.caches with inferIOC := mp.insert e r } }

/-- con-leche: ConLeche/Cached/CoreC.lean:346-359 memoBI — record a `defeq`
verdict at the ORDERED pair, both signs (con-leche's `defeqC` stores the
`Bool` result `r`, which is what makes a negative memo sound). -/
@[noinline] def defeqSet (a b : EIdx) (r : Bool) : AM Unit := do
  let s ← get
  let mp := s.caches.defeqC
  let s := { s with caches := { s.caches with defeqC := ∅ } }
  set { s with caches := { s.caches with defeqC := mp.insert (a, b) r } }

/-- con-leche: ConLeche/Cached/StateC.lean:514-526 CState.enterEager — enter
the eager tower.  From a plain mode (`eager = false`): the plain memos move out
(returned), the stored eager ones move into the six fields, and the eager slot
is left empty.  From an eager mode the six fields already hold the eager set:
nothing moves. -/
@[noinline] def enterEager (eager : Bool) : AM (Option ModeMemos) := do
  if eager then pure none
  else
    let s ← get
    let c := s.caches
    let em := c.eagerMemos
    set { s with caches :=
      { c with whnfCoreC := em.whnfCoreC, whnfCoreCheapC := em.whnfCoreCheapC,
               whnfC := em.whnfC, inferC := em.inferC, inferIOC := em.inferIOC,
               defeqC := em.defeqC, eagerMemos := ModeMemos.empty } }
    pure (some c.modeMemos)

/-- con-leche: ConLeche/Cached/StateC.lean:528-538 CState.leaveEager — leave
the eager tower: the six fields (now the eager tower's, with what the run
added) are stored back as the eager set, and the plain memos `saved` return to
the six fields; nothing moves when `enterEager` moved nothing. -/
@[noinline] def leaveEager (saved : Option ModeMemos) : AM Unit := do
  match saved with
  | none => pure ()
  | some mm =>
    let s ← get
    let c := s.caches
    set { s with caches :=
      { c with eagerMemos := c.modeMemos,
               whnfCoreC := mm.whnfCoreC, whnfCoreCheapC := mm.whnfCoreCheapC,
               whnfC := mm.whnfC, inferC := mm.inferC, inferIOC := mm.inferIOC,
               defeqC := mm.defeqC } }

/-- con-leche: ConLeche/Kernel/Core.lean:1862-1897 coreKnot
con-leche: ConLeche/Cached/CoreC.lean:1767-1788 coreKnotI
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Core.coreKnot_bridge, then delete this line
Tie the bodies together: the record whose entry points are the bodies applied
to the record one fuel level down, each under its own memo.  Fuel is *only*
here — exhaustion is an internal error, never a verdict — and the next level
is constructed lazily inside each entry point's closure.

The io slot is the io body at both modes (con-leche's task #346: official's
`infer_only`), tied to the io-grade view of the previous level.  The io body runs under its own table (`inferIOC`), the full body under
`inferC`: a hit in one grade never serves the other (DESIGN §8.3, lesson 9).
The same holds of `whnfCore`'s two modes (official `cheap_proj`): the cheap
mode runs under `whnfCoreCheapC`, the full mode under `whnfCoreC`. -/
def coreKnot (mode : CheckMode) (eager : Bool) (fe : IFEnv) (wrap : CoreFnsA → CoreFnsA) :
    Nat → CoreFnsA
  | 0 =>
    { whnfCore := fun _ _ _ => fail (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => fail (.internal "fuel exhausted: whnf")
      infer := fun _ _ => fail (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => fail (.internal "fuel exhausted: defeq")
      defeqE := fun _ _ _ => fail (.internal "fuel exhausted: defeq")
      inferIO := fun _ _ => fail (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    wrap
      { whnfCore := fun c d e => do
          -- **The answer IS the argument, off the tag** (task #97-P6-7's
          -- lever 2): the six head kinds `whnfCoreBody` returns unchanged are
          -- read off the handle word, so neither the memo nor the store is
          -- touched — and neither is the memo WRITTEN, which is what keeps the
          -- table small enough for `clear_fit`'s high-water mark to settle.
          if whnfCoreStuckTag e then pure e
          else if c then
            match (← get).caches.whnfCoreCheapC[e]? with
            | some x => pure x
            | none => do
              let x ← whnfCoreBody mode (coreKnot mode eager fe wrap fuel) fe true d e
              whnfCoreCheapSet e x
              pure x
          else
          match (← get).caches.whnfCoreC[e]? with
          | some x => pure x
          | none => do
            let x ← whnfCoreBody mode (coreKnot mode eager fe wrap fuel) fe false d e
            whnfCoreSet e x
            pure x
        whnf := fun d e => do
          if whnfStuckTag e then pure e
          else
          match (← get).caches.whnfC[e]? with
          | some x => pure x
          | none => do
            let x ← whnfBody (coreKnot mode eager fe wrap fuel) fe d e
            whnfSet e x
            pure x
        infer := fun d e => do
          match (← get).caches.inferC[e]? with
          | some x => pure x
          | none => do
            let x ← inferBody (coreKnot mode eager fe wrap fuel) fe d e
            inferSet e x
            pure x
        defeq := fun d a b => do
          match (← get).caches.defeqC[(a, b)]? with
          | some x => pure x
          | none => do
            let x ← defeqBody mode eager (coreKnot mode eager fe wrap fuel) fe d a b
            defeqSet a b x
            pure x
        -- **The eager slot**: the eager tower — the knot at `eager := true`
        -- one level down — memoized at the ordered pair on the eager tower's
        -- own memos, kept in the state between eager comparisons
        -- (con-leche's `withEagerMemos mode (memoBI …)`, the bind pushed into
        -- the probe's two branches): an eager entry never serves a plain
        -- query.
        defeqE := fun d a b => do
          let saved ← enterEager eager
          match (← get).caches.defeqC[(a, b)]? with
          | some x => do
            leaveEager saved
            pure x
          | none => do
            let x ← defeqBody mode true (coreKnot mode true fe wrap fuel) fe d a b
            defeqSet a b x
            leaveEager saved
            pure x
        inferIO := fun d e => do
          match (← get).caches.inferIOC[e]? with
          | some x => pure x
          | none => do
            let x ← inferBodyIO (CoreFnsA.ioView (coreKnot mode eager fe wrap fuel)) fe d e
            inferIOSet e x
            pure x }

/-- con-leche: ConLeche/Kernel/Core.lean:1899-1918 checkFuel — the shared
fuel for the checker core, counted in knot levels.  **Effectively
unbounded** (`2^62`, as `whnfCoreLoopFuel`): the fuel exists so that the knot
is a structural recursion the proofs can induct over, and running out of it
is an internal error, never an accept.  What bounds the depth of the executed
checker is its native stack (`arena::core::CHECK_FUEL`'s note). -/
@[noinline] def checkFuel : Nat := 4611686018427387904  -- 2^62

/-! ## The fueled entry points

`ConLeche/Kernel/TypeChecker.lean`, whose seven (T) declarations live here
because the arena has ONE knot (deviation 5): con-leche's `pureFns` is
`coreKnot mode env id` at `CheckM` with no memo, and the arena's
`coreKnot` already carries the memos, so `pureFnsA` is the same expression
over handles and the seven entries call it. -/

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:23-25 pureFns — the core, tied
at `AM`, fuel in the knot.  Named `pureFnsA` because the arena's is the
MEMOIZED knot; con-leche's `pureFns` is its unmemoized specification, whose
verdicts the memo does not change (DESIGN §8.3: the memo answers what the
body would have answered). -/
def pureFnsA (mode : CheckMode) (eager : Bool) (fe : IFEnv) : Nat → CoreFnsA :=
  coreKnot mode eager fe id

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:33-35 whnf — the full
reduction loop (fueled). -/
def whnf (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat) (e : EIdx) :
    AM EIdx :=
  (pureFnsA mode false fe fuel).whnf depth e

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:37-40 inferTypeCore —
full-grade type inference (fueled): the declaration front door's entry. -/
def inferTypeCore (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM EIdx :=
  (pureFnsA mode false fe fuel).infer depth e

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:48-50 isDefEqCore —
definitional equality (fueled). -/
def isDefEqCore (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (a b : EIdx) : AM Bool :=
  (pureFnsA mode false fe fuel).defeq depth a b

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:52-54 ensureSortCore —
`ensureSort` over the knot (fueled). -/
def ensureSortCore (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM LIdx :=
  ensureSort (pureFnsA mode false fe fuel) fe depth e

/-! ## The per-declaration bracket

DESIGN §8.3, "Drop".  P2d calls these at each declaration boundary: the
store's scratch tier goes with `EStore.dropScratch`, and the caches lose
exactly the entries that name a handle of that tier. -/

/-- con-leche: none — **the per-declaration cache drop** (DESIGN §8.3): every
memo entry whose key or value names a scratch handle goes with the tier,
everything persistent stays (con-leche's arena #51).  P2d calls this beside
`EStore.dropScratch`, which is why it is a state operation of its own. -/
@[noinline] def flushCaches : AM Unit := do
  let s ← get
  set { s with caches := Caches.empty }

/-- con-leche: none — **the per-declaration bracket, closed**: drop the
scratch tier of the store and the cache entries that name it, in one
operation, so the two halves cannot drift apart. -/
@[noinline] def dropScratch : AM Unit := do
  flushCaches
  let s ← get
  let st := s.store
  let s := { s with store := EStore.empty }
  set { s with store := st.dropScratch }

/-- con-leche: none — **the per-declaration bracket, opened**: turn the
scratch tier on, and clear the per-call memo tables of `Memos`, which belong
to no tier and whose keys the new tier may reuse. -/
@[noinline] def enterScratch : AM Unit := do
  let s ← get
  let st := s.store
  let s := { s with store := EStore.empty, memos := Memos.empty }
  set { s with store := st.enableScratch }

end ConRon.Arena
