/-
# The declaration checker, differentially (task #97 P2d)

The module-level differential check of `Arena/Checker.lean` and everything
under it, in the shape `ExprOpsTest.lean` and `CoreTest.lean` use one and two
tiers down (DESIGN §8.4, "correctness before proofs"):

> write a declaration list ONCE, as con-leche `Declaration` values; intern it
> into the arena; run the arena's `checkDecl` / `checkDeclsPure` /
> `checkStream` on handles; read the resulting environment back with
> `denoteCIList`, and compare with con-leche's own `checkDecl` /
> `checkDeclsPure` applied to the SAME values.

The comparison is over the **whole outcome**: an accept must meet an accept
at the same environment — every constant, its type and its stored
value compared as `ConstantInfo` values — and a failure must meet a failure
of the same KIND (`errEq`; messages are not compared, DESIGN §3.1 — since
task #97-T2-LOCKSTEP lane Checker the twin's declines carry the Rust port's
constant messages, with no declaration name read back).  So the rejects and
the declines below are real tests, not "both sides threw".

**What this file covers.**  The declaration kinds other than inductive
blocks — a definition checked and installed, a theorem checked against its
statement, an axiom pinned, a pinned basis block compared with its pin and
installed at its own level-parameter names, the quotient records, the fold and
the driver's jobs agreeing — on declaration lists whose `Eq` and `Nat` are the
pinned blocks and so need no uniform inductive install at all.  The inductive route has its own differential,
`InductivesTest.lean`, and `scripts/diff-e2e.sh --bin` runs the whole twin on
the e2e corpus.

Nothing here is a proof and nothing here is an `#eval` print: every check is
kernel-reduced, so a disagreement is a build failure.
-/
module -- shake: keep-all (a `#guard` stores no constant shake can see)

public import ConRon.Arena.Checker
public import ConLeche.Kernel.CheckDecl
/- The `#guard`s below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConRon.Arena.Checker
meta import ConLeche.Kernel.CheckDecl

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## The mode, the fuel, and the outcome comparisons -/

/-- con-leche: none — the mode every check runs at: `.verified`, the lane the
bridge is stated at. -/
private def MU : CheckMode := .verified

/-- con-leche: none — the knot fuel.  The subjects' deepest reduction is a
handful of knot levels; 200 is a comfortable margin and keeps the kernel
reduction of these `#guard`s cheap. -/
private def F : Nat := 200

/-- con-leche: none — con-leche's entry point record at this fuel. -/
private def OPS : ConLeche.CheckerOps ConLeche.CheckM := ConLeche.fueledOps MU F

/-- con-leche: none — the arena's error against con-leche's: same
constructor; the message is not compared (DESIGN §3.1: the twin declines with
the Rust port's constant messages, task #97-T2-LOCKSTEP lane Checker).  The
arena's fourth constructor (`native`) has no con-leche counterpart and never
matches, which is right: a `native` claims nothing. -/
private def errEq : CheckError → ConLeche.CheckError → Bool
  | .notImplemented _, .notImplemented _ => true
  | .invalid _, .invalid _ => true
  | .internal _, .internal _ => true
  | _, _ => false

/-- con-leche: none — the arena's error against con-leche's: same
constructor, message NOT compared (DESIGN §3.1), for `chkJobs`, whose failure
also carries a position. -/
private def errKindEq : CheckError → ConLeche.CheckError → Bool
  | .notImplemented _, .notImplemented _ => true
  | .invalid _, .invalid _ => true
  | .internal _, .internal _ => true
  | _, _ => false

/-- con-leche: none — intern an environment and a declaration and run the
arena's `checkDecl` on them. -/
private def runDecl (envCL : ConLeche.Env) (dCL : Declaration) : AM IFEnv := do
  let cs ← internCIList envCL.consts
  let (_, ds) ← Frontend.internDecls ∅ [dCL]
  checkDecl MU [] (mkIFEnv ⟨cs, []⟩) (ds.headD default)

/-- con-leche: none — the arena's `checkDecl` against con-leche's, over the
whole outcome: the same environment, constant for constant, or the same
error. -/
private def chkDecl (envCL : ConLeche.Env) (dCL : Declaration) : Bool :=
  match (do internReservedPins; runDecl envCL dCL).run (AState.init EStore.empty),
      ConLeche.checkDecl MU OPS [] envCL dCL with
  | .ok (fe, s'), .ok env =>
    Frontend.denoteCIList s'.store fe.env.consts == some env.consts
  | .error a, .error b => errEq a b
  | _, _ => false

/-- con-leche: none — intern a declaration list and run the arena's
`checkDeclsPure` on it. -/
private def runDecls (dsCL : List Declaration) : AM IFEnv := do
  let (_, ds) ← Frontend.internDecls ∅ dsCL
  checkDeclsPure MU [] ds

/-- con-leche: none — the arena's `checkDeclsPure` against con-leche's, over
the whole outcome. -/
private def chkDecls (dsCL : List Declaration) : Bool :=
  match (do internReservedPins; runDecls dsCL).run (AState.init EStore.empty),
      ConLeche.checkDeclsPure MU OPS [] dsCL with
  | .ok (fe, s'), .ok env =>
    Frontend.denoteCIList s'.store fe.env.consts == some env.consts
  | .error a, .error b => errEq a b
  | _, _ => false

/-- con-leche: none — intern a declaration list and run the arena's check of
a stream as the driver runs it (`checkStream`: the index of the records, then
every record's job at its view), with the startup pin walk in front. -/
private def runJobs (dsCL : List Declaration) :
    AM (Except (CheckError × Nat) Unit) := do
  let (_, ds) ← Frontend.internDecls ∅ dsCL
  let pins ← internAllPins []
  checkStream MU pins ds.toArray

/-- con-leche: none — the driver's jobs against con-leche's fold
`checkDeclsPure`: the same accept, or a failure of the same kind.  A job's
environment is not read back (`checkStream` returns none); its accept is the
fold's by con-leche's `checkDecls_of_jobs`, and this is that agreement,
measured. -/
private def chkJobs (dsCL : List Declaration) : Bool :=
  match (do internReservedPins; runJobs dsCL).run (AState.init EStore.empty),
      ConLeche.checkDeclsPure MU OPS [] dsCL with
  | .ok (.ok (), _), .ok _ => true
  | .ok (.error (a, _), _), .error b => errKindEq a b
  | _, _ => false

/-- con-leche: none — con-leche's own outcome, pinned by hand: an accept
whose environment has this many constants. -/
private def okSize : ConLeche.CheckM ConLeche.Env → Nat → Bool
  | .ok env, n => env.consts.length == n
  | .error _, _ => false

/-- con-leche: none — con-leche's own outcome, pinned by hand: a failure of
this kind and this message. -/
private def failsWith : ConLeche.CheckM ConLeche.Env → ConLeche.CheckError → Bool
  | .error e, x => (toString (repr e)) == (toString (repr x))
  | .ok _, _ => false

/-! ## The subjects, written once as con-leche values

`Eq` and `Nat` arrive as their pinned blocks (`.indDecl eqBasis 2`, the
record an export writes), which the names route to the block's comparison with
its pin, so none of these lists needs the uniform inductive install. -/

/-- con-leche: none — a fixture value of the differential, written once as a con-leche value; the arena side is its interning. -/
private def anon : ConLeche.Name := .anonymous
/-- con-leche: none — a fixture value of the differential, written once as a con-leche value; the arena side is its interning. -/
private def natTy : ConLeche.Expr := .const ConLeche.natName []
/-- con-leche: none — a fixture value of the differential, written once as a con-leche value; the arena side is its interning. -/
private def zeroE : ConLeche.Expr := .const ConLeche.natZeroName []
/-- con-leche: none — a fixture value of the differential, written once as a con-leche value; the arena side is its interning. -/
private def succE : ConLeche.Expr := .const ConLeche.natSuccName []

/-- con-leche: none — a fixture value of the differential, written once as a con-leche value; the arena side is its interning. -/
private def twoName : ConLeche.Name := anon.str "two"
/-- con-leche: none — a fixture value of the differential, written once as a con-leche value; the arena side is its interning. -/
private def twoVal : ConLeche.Expr := .app succE (.app succE zeroE)
/-- con-leche: none — a fixture value of the differential, written once as a con-leche value; the arena side is its interning. -/
private def dTwo : Declaration := .defnDecl ⟨twoName, [], natTy⟩ twoVal (.regular 1)

/-- con-leche: none — A definition whose value does not inhabit its declared type. -/
private def dTwoBad : Declaration :=
  .defnDecl ⟨anon.str "bad", [], natTy⟩ (.sort .zero) (.regular 1)

/-- con-leche: none — A definition whose type mentions a constant nothing declares. -/
private def dUnknown : Declaration :=
  .defnDecl ⟨anon.str "u", [], .const (anon.str "nope") []⟩ zeroE (.regular 1)

/-- con-leche: none — A definition under a reserved basis name. -/
private def dReserved : Declaration :=
  .defnDecl ⟨ConLeche.natName, [], natTy⟩ zeroE (.regular 1)

/-- con-leche: none — A definition with a loose bound variable in its value. -/
private def dLoose : Declaration :=
  .defnDecl ⟨anon.str "l", [], natTy⟩ (.bvar 0) (.regular 1)

/-- con-leche: none — A definition with duplicate universe parameters. -/
private def dDupUniv : Declaration :=
  .defnDecl ⟨anon.str "d", [anon.str "u", anon.str "u"], natTy⟩ zeroE (.regular 1)

/-- con-leche: none — The proposition a theorem is stated at: `Eq.{1} Nat 0 0`, over the pinned
`Eq` basis — an ORDINARY user axiom is a positive decline at its own record,
so a proposition has to come from the basis rather than be postulated. -/
private def eq1 : ConLeche.Expr := .const ConLeche.eqName [.succ .zero]
/-- con-leche: none — a fixture value of the differential, written once as a con-leche value; the arena side is its interning. -/
private def pE : ConLeche.Expr := .app (.app (.app eq1 natTy) zeroE) zeroE
/-- con-leche: none — a fixture value of the differential, written once as a con-leche value; the arena side is its interning. -/
private def pfE : ConLeche.Expr :=
  .app (.app (.const ConLeche.eqReflName [.succ .zero]) natTy) zeroE

/-- con-leche: none — A theorem: `Eq.refl Nat 0` proves `0 = 0`. -/
private def dThm : Declaration := .thmDecl ⟨anon.str "t", [], pE⟩ pfE

/-- con-leche: none — A theorem whose type is not a proposition. -/
private def dThmNotProp : Declaration :=
  .thmDecl ⟨anon.str "tn", [], natTy⟩ zeroE

/-- con-leche: none — A theorem whose value does not inhabit its statement. -/
private def dThmBad : Declaration := .thmDecl ⟨anon.str "tb", [], pE⟩ zeroE

/-- con-leche: none — An `opaque`: stored as an `axiomInfo`, its value a discarded witness. -/
private def dOpaque : Declaration :=
  .opaqueDecl ⟨anon.str "o", [], natTy⟩ twoVal

/-- con-leche: none — `sorryAx`: the one axiom tolerated as a DECLARATION, installing nothing. -/
private def dSorry : Declaration :=
  .axiomDecl ⟨ConLeche.sorryAxName, [],
    .forallE (.sort (.succ .zero)) (.bvar 0)⟩

/-- con-leche: none — `propext` at a shape the pinned `Iff` family does not back. -/
private def dPropext : Declaration :=
  .axiomDecl ⟨ConLeche.propextName, [], .sort .zero⟩

/-- con-leche: none — An ordinary user axiom: a positive decline at its own record. -/
private def dOtherAx : Declaration := .axiomDecl ⟨anon.str "myax", [], natTy⟩

/-- con-leche: none — `Nat.add` under a nonstandard body: the structural-`Nat` pin gate's
subject.  The environment has no `Nat.add` dependencies, so the gate declines
with its environment message. -/
private def dNatAdd : Declaration :=
  .defnDecl ⟨ConLeche.natName.str "add", [],
    .forallE natTy (.forallE natTy natTy)⟩
    (.lam natTy (.lam natTy (.bvar 1))) (.regular 1)

/-- con-leche: none — `Nat.div` under a nonstandard body: the WF-recursive pin gate's subject,
declining at `divModEnvGuard` (the environment has no `Nat.ble`). -/
private def dNatDiv : Declaration :=
  .defnDecl ⟨ConLeche.natName.str "div", [],
    .forallE natTy (.forallE natTy natTy)⟩
    (.lam natTy (.lam natTy (.bvar 1))) (.regular 1)

/-! ## The lists -/

/-- con-leche: none — the pinned `Eq` block as an export writes it. -/
private def dEq : Declaration := .indDecl ConLeche.eqBasis 2
/-- con-leche: none — the pinned `Nat` block as an export writes it. -/
private def dNat : Declaration := .indDecl ConLeche.natBasis 0

/-- con-leche: none — The basis prefix every accepting list starts with: the pinned `Eq` block,
then the pinned `Nat` block (which `Eq` does not need, and which the value
declarations below do). -/
private def basisPrefix : List Declaration := [dEq, dNat]

/-- con-leche: none — the pinned `Eq` block at other level-parameter names:
accepted, and stored at the stream's names. -/
private def dEqOther : Declaration :=
  let w : ConLeche.Name := anon.str "w"
  let z : ConLeche.Name := anon.str "z"
  .indDecl [ConLeche.eqA.atLps [w], ConLeche.eqReflA.atLps [w], ConLeche.eqRecA.atLps [z, w]] 2

/-- con-leche: none — the `Eq` block with the recursor's names swapped, so its rule
no longer reads the constructor's parameters as the pin's does: invalid, at the
block's own recursor check (before the reserved names' comparison with the
pin). -/
private def dEqSwapped : Declaration :=
  let w : ConLeche.Name := anon.str "w"
  let z : ConLeche.Name := anon.str "z"
  .indDecl [ConLeche.eqA.atLps [w], ConLeche.eqReflA.atLps [w], ConLeche.eqRecA.atLps [w, z]] 2

/-- con-leche: none — the five quotient records, each at its pin. -/
private def quotRecords : List Declaration :=
  [.quotDecl .type ConLeche.quotA.toConstantVal,
   .quotDecl .ctor ConLeche.quotMkA.toConstantVal,
   .quotDecl .lift ConLeche.quotLiftA.toConstantVal,
   .quotDecl .ind ConLeche.quotIndA.toConstantVal,
   .axiomDecl ConLeche.quotSoundA.toConstantVal]

/-- con-leche: none — The accepting list: the two basis blocks, a definition, a proposition and
its proof, a theorem, an opaque, and a tolerated `sorryAx`. -/
private def dsGood : List Declaration :=
  basisPrefix ++ [dTwo, dThm, dOpaque, dSorry]

/-- con-leche: none — The quotient package, whose `Quot` record requires `Eq` stored first. -/
private def dsQuot : List Declaration := dEq :: quotRecords

/-- con-leche: none — The quotient package WITHOUT `Eq`: a decline, at con-leche's own
message. -/
private def dsQuotBad : List Declaration := quotRecords

/-- con-leche: none — A duplicate declaration: the second `two` is invalid input. -/
private def dsDup : List Declaration := basisPrefix ++ [dTwo, dTwo]

/-! ## What con-leche itself says

`chkDecl` passes when the two checkers AGREE, and two agreeing failures
agree.  These lines pin con-leche's own outcome by hand, so that the
differential below is evidence of something. -/

#guard okSize (ConLeche.checkDeclsPure MU OPS [] basisPrefix) 7
#guard okSize (ConLeche.checkDeclsPure MU OPS [] dsGood) 10
#guard okSize (ConLeche.checkDeclsPure MU OPS [] dsQuot) 8
#guard failsWith (ConLeche.checkDeclsPure MU OPS [] dsQuotBad)
  (.notImplemented "quotient declaration before what it needs")
#guard okSize (ConLeche.checkDeclsPure MU OPS [] [dEqOther]) 3
#guard failsWith (ConLeche.checkDeclsPure MU OPS [] [dEqSwapped])
  (.invalid "target rec: the recursor's major premise is not the member at its parameters and \
    its index binders")
#guard failsWith (ConLeche.checkDeclsPure MU OPS [] dsDup)
  (.invalid "duplicate declaration two")

/-! ## The differential: `checkDeclsPure` -/

#guard chkDecls basisPrefix
#guard chkDecls dsGood
#guard chkDecls dsQuot
#guard chkDecls dsQuotBad
#guard chkDecls dsDup
#guard chkDecls [.indDecl ConLeche.emptyBasis 0]
#guard chkDecls [.indDecl ConLeche.falseBasis 0]
#guard chkDecls [dEqOther]
#guard chkDecls [dEqSwapped]
#guard chkDecls (basisPrefix ++ [dTwoBad])
#guard chkDecls (basisPrefix ++ [dUnknown])
#guard chkDecls (basisPrefix ++ [dReserved])
#guard chkDecls (basisPrefix ++ [dLoose])
#guard chkDecls (basisPrefix ++ [dDupUniv])
#guard chkDecls (basisPrefix ++ [dThmBad])
#guard chkDecls (basisPrefix ++ [dThmNotProp])
#guard chkDecls (basisPrefix ++ [dSorry])
#guard chkDecls (basisPrefix ++ [dPropext])
#guard chkDecls (basisPrefix ++ [dOtherAx])
#guard chkDecls (basisPrefix ++ [dNatAdd])
#guard chkDecls (basisPrefix ++ [dNatDiv])

/-! ## The differential: `checkDecl` at a non-empty environment

The environment is built by `checkDeclsPure` on con-leche's side and by
interning ITS result on the arena's, so the two `checkDecl` calls see the
same environment and the check is about the STEP. -/

/-- con-leche: none — the environment `basisPrefix` installs, on con-leche's
side; the arena's is its interning. -/
private def envBasis : ConLeche.Env :=
  match ConLeche.checkDeclsPure MU OPS [] basisPrefix with
  | .ok env => env
  | .error _ => ⟨[], []⟩

#guard envBasis.consts.length == 7

#guard chkDecl envBasis dTwo
#guard chkDecl envBasis dTwoBad
#guard chkDecl envBasis dUnknown
#guard chkDecl envBasis dReserved
#guard chkDecl envBasis dLoose
#guard chkDecl envBasis dDupUniv
#guard chkDecl envBasis dOpaque
#guard chkDecl envBasis dSorry
#guard chkDecl envBasis dPropext
#guard chkDecl envBasis dOtherAx
#guard chkDecl envBasis dNatAdd
#guard chkDecl envBasis dNatDiv
#guard chkDecl envBasis (.indDecl ConLeche.emptyBasis 0)
#guard chkDecl envBasis (.quotDecl .type ConLeche.quotA.toConstantVal)
#guard chkDecl envBasis (.quotDecl .lift ConLeche.quotLiftA.toConstantVal)
#guard chkDecl envBasis (.quotDecl .type ⟨ConLeche.quotName, [], natTy⟩)

/-! ## The differential: the driver's jobs

`checkStream` is what `runPipeline` runs: the stream's index, then every
record's job at its view, each in its scratch bracket.  con-leche's own theorem
(`checkDecls_of_jobs`) is that every job passing is the fold's accept; each line
below is that agreement on one list. -/

#guard chkJobs basisPrefix
#guard chkJobs dsGood
#guard chkJobs dsQuot
#guard chkJobs dsQuotBad
#guard chkJobs dsDup
#guard chkJobs (basisPrefix ++ [dTwoBad])
#guard chkJobs (basisPrefix ++ [dUnknown])
#guard chkJobs (basisPrefix ++ [dThmBad])
#guard chkJobs (basisPrefix ++ [dThmNotProp])
#guard chkJobs (basisPrefix ++ [dOpaque])
#guard chkJobs (basisPrefix ++ [dNatAdd])
#guard chkJobs (basisPrefix ++ [dNatDiv])

/-! ## The pieces below `checkDecl`

Four of them have no `checkDecl` path that reaches them on a list this small,
so they are checked directly against con-leche's own. -/

/-- con-leche: none — the arena's `stdAxiomOk` against con-leche's. -/
private def chkStdAxiom (envCL : ConLeche.Env) (cv : ConstantVal) : Bool :=
  let prog : AM Bool := do
    let cs ← internCIList envCL.consts
    let (_, icv) ← Frontend.internCV ∅ cv
    stdAxiomOk (mkIFEnv ⟨cs, []⟩) icv
  match (do internReservedPins; prog).run (AState.init EStore.empty) with
  | .ok (r, _) => r == ConLeche.stdAxiomOk envCL cv
  | .error _ => false

#guard chkStdAxiom envBasis ⟨ConLeche.propextName, [], .sort .zero⟩
#guard chkStdAxiom envBasis ⟨ConLeche.choiceName, [], .sort .zero⟩
#guard chkStdAxiom envBasis ⟨anon.str "x", [], natTy⟩

/-- con-leche: none — the arena's `matchesPin` against con-leche's (plain
equality since con-leche's task #342): an equal pin, a different type, a
binder type that differs in its codomain, and different level parameters. -/
private def chkMatchesPin (cv pin : ConstantVal) : Bool :=
  let prog : AM Bool := do
    let (m, a) ← Frontend.internCV ∅ cv
    let (_, b) ← Frontend.internCV m pin
    a.matchesPin b
  match (do internReservedPins; prog).run (AState.init EStore.empty) with
  | .ok (r, _) => r == ConLeche.ConstantVal.matchesPin cv pin
  | .error _ => false

#guard chkMatchesPin ⟨twoName, [], natTy⟩ ⟨twoName, [], natTy⟩
#guard chkMatchesPin ⟨twoName, [], natTy⟩ ⟨twoName, [], .sort .zero⟩
#guard chkMatchesPin ⟨twoName, [], .forallE natTy natTy⟩
  ⟨twoName, [], .forallE natTy (.sort .zero)⟩
#guard chkMatchesPin ⟨twoName, [anon.str "u"], natTy⟩ ⟨twoName, [], natTy⟩

/-- con-leche: none — the arena's `canonEqList` against con-leche's, on the
pinned blocks and on a block that is not one. -/
private def chkCanonList (xs ys : List ConstantInfo) : Bool :=
  let prog : AM Bool := do
    let (m, a) ← Frontend.internCIList ∅ xs
    let (_, b) ← Frontend.internCIList m ys
    canonEqList a b
  match (do internReservedPins; prog).run (AState.init EStore.empty) with
  | .ok (r, _) => r == ConLeche.canonEqList xs ys
  | .error _ => false

#guard chkCanonList (ConLeche.BasisKind.natK.decls) (ConLeche.BasisKind.natK.decls)
#guard chkCanonList (ConLeche.BasisKind.eqK.decls) (ConLeche.BasisKind.eqK.decls)
#guard chkCanonList (ConLeche.BasisKind.eqK.decls) (ConLeche.BasisKind.natK.decls)

/-- con-leche: none — the arena's `basisNameHit` against con-leche's. -/
private def chkBasisNameHit (block : List ConstantInfo) : Bool :=
  let prog : AM (Option BasisKind) := do
    let (_, b) ← Frontend.internCIList ∅ block
    basisNameHit b
  match (do internReservedPins; prog).run (AState.init EStore.empty) with
  | .ok (r, _) => r == ConLeche.basisNameHit block
  | .error _ => false

#guard chkBasisNameHit (ConLeche.BasisKind.natK.decls)
#guard chkBasisNameHit (ConLeche.BasisKind.eqK.decls)
#guard chkBasisNameHit (ConLeche.BasisKind.quotK.decls)
#guard chkBasisNameHit []

/-- con-leche: none — the arena's `pinListOk` against con-leche's. -/
private def chkPinListOk (block pins : List ConstantInfo) : Bool :=
  let prog : AM Bool := do
    let (m, b) ← Frontend.internCIList ∅ block
    let (_, p) ← Frontend.internCIList m pins
    pinListOk b p
  match (do internReservedPins; prog).run (AState.init EStore.empty) with
  | .ok (r, _) => r == ConLeche.pinListOk block pins
  | .error _ => false

#guard chkPinListOk ConLeche.eqBasis ConLeche.eqBasis
#guard chkPinListOk ConLeche.natBasis ConLeche.eqBasis
#guard chkPinListOk
  [ConLeche.eqA.atLps [anon.str "w"], ConLeche.eqReflA.atLps [anon.str "w"],
    ConLeche.eqRecA.atLps [anon.str "w", anon.str "z"]] ConLeche.eqBasis

/-- con-leche: none — the arena's `quotPinHit` against con-leche's. -/
private def chkQuotPinHit (k : QuotKind) (cv : ConstantVal) : Bool :=
  let prog : AM Bool := do
    let (_, icv) ← Frontend.internCV ∅ cv
    quotPinHit k icv
  match (do internReservedPins; prog).run (AState.init EStore.empty) with
  | .ok (r, _) => r == ConLeche.quotPinHit k cv
  | .error _ => false

#guard chkQuotPinHit .lift ConLeche.quotLiftA.toConstantVal
#guard chkQuotPinHit .lift (ConLeche.quotLiftA.atLps [anon.str "a", anon.str "b"]).toConstantVal
#guard chkQuotPinHit .lift ConLeche.quotIndA.toConstantVal

end ConRon.Arena
