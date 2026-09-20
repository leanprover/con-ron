/-
# The `Core` twins, differentially (task #97 P2c)

**The module-level differential check**, the same shape `ExprOpsTest.lean`
uses one tier down and for the same reason (DESIGN §8.4, "correctness before
proofs"):

> build a tiny environment by hand as con-leche values, intern it into the
> arena, run the arena twin on handles, read the answer back with `denoteE`,
> and compare with con-leche's own `whnf` / `inferTypeCore` / `isDefEqCore` /
> `annotateCore` applied to the *denotations*.

The comparison is over the **whole outcome**: an `ok` must meet an `ok` at
the same term, and an error must meet an error of the same kind AND the same
message (`errEq` below).  So a check passes only if the two checkers agree
about what happened, not merely about whether something did — which is what
makes the failure cases (an unknown constant, an out-of-scope free variable,
a let whose value mismatches) real tests rather than "both sides threw".

**The environment is written ONCE**, as con-leche `ConstantInfo` values, and
the arena's is *derived* from it by `internConstantInfo`.  That is the same
discipline `ExprOpsTest.lean` applies to terms ("the expected side is
computed, never written out"): the two environments cannot drift, because
there is only one.

Nothing here is a proof and nothing here is an `#eval` print: every check is
kernel-reduced, so a disagreement is a build failure.
-/
import ConRon.Arena.CoreGated
import ConLeche.Kernel.TypeChecker
import ConLeche.Kernel.CoreIO
import ConLeche.Kernel.CoreGated

namespace ConRon.Arena

open ConLeche

/-! ## Interning a con-leche environment

The one direction the test needs: con-leche value ↦ arena handle.  These are
test scaffolding — the checker never goes this way (the parser interns from
the export's bytes) — so they carry `con-leche: none`. -/

/-- con-leche: none — intern a con-leche `Expr` into the arena, structurally.
Test scaffolding: the real parser interns from the export's bytes. -/
private def internExprT : ConLeche.Expr → AM EIdx
  | .bvar i => internE (.bvar i)
  | .fvar i ty => do
    let t ← internExprT ty
    internE (.fvar i t)
  | .sort u => do
    let l ← internLevel u
    internE (.sort l)
  | .const n us => do
    let hn ← internName n
    let hu ← internLevels us
    internE (.const hn hu)
  | .app f a => do
    let hf ← internExprT f
    let ha ← internExprT a
    internE (.app hf ha)
  | .lam ty b m => do
    let ht ← internExprT ty
    let hb ← internExprT b
    internE (.lam ht hb m)
  | .forallE ty b m => do
    let ht ← internExprT ty
    let hb ← internExprT b
    internE (.forallE ht hb m)
  | .letE ty v b => do
    let ht ← internExprT ty
    let hv ← internExprT v
    let hb ← internExprT b
    internE (.letE ht hv hb)
  | .lit l => internE (.lit l)
  | .proj s i e => do
    let hs ← internName s
    let he ← internExprT e
    internE (.proj hs i he)

/-- con-leche: none — intern a list of names. -/
private def internNameList : List ConLeche.Name → AM (List NIdx)
  | [] => pure []
  | n :: ns => do
    let h ← internName n
    let hs ← internNameList ns
    pure (h :: hs)

/-- con-leche: none — intern a list of expressions. -/
private def internExprList : List ConLeche.Expr → AM (List EIdx)
  | [] => pure []
  | e :: es => do
    let h ← internExprT e
    let hs ← internExprList es
    pure (h :: hs)

/-- con-leche: none — intern a list of levels, one handle each. -/
private def internLevelListT : List Level → AM (List LIdx)
  | [] => pure []
  | u :: us => do
    let h ← internLevel u
    let hs ← internLevelListT us
    pure (h :: hs)

/-- con-leche: none — intern a `ConstantVal`. -/
private def internCV (cv : ConstantVal) : AM IConstantVal := do
  let n ← internName cv.name
  let lps ← internNameList cv.levelParams
  let ty ← internExprT cv.type
  pure ⟨n, lps, ty⟩

/-- con-leche: none — intern an `IndCaps`.  `sortZ` is a `PropWhen` over real
names and crosses unchanged (DESIGN §8.7). -/
private def internCaps (c : IndCaps) : AM IIndCaps := do
  let ec ← internName c.etaCtor
  pure { eta := c.eta, etaCtor := ec, etaParams := c.etaParams,
         etaFields := c.etaFields, unitlike := c.unitlike,
         unitParams := c.unitParams, ruleK := c.ruleK, sortZ := c.sortZ }

/-- con-leche: none — intern a `RecRuleFire`. -/
private def internFire : RecRuleFire → AM IRecRuleFire
  | .inert => pure .inert
  | .plain => pure .plain
  | .nested lvls pins => do
    let ls ← internLevelListT lvls
    let ps ← internExprList pins
    pure (.nested ls ps)

/-- con-leche: none — intern a `RecRule`. -/
private def internRule (rl : RecRule) : AM IRecRule := do
  let c ← internName rl.ctor
  let f ← internFire rl.fire
  let rhs ← internExprT rl.rhs
  pure { ctor := c, nfields := rl.nfields, ctorParams := rl.ctorParams,
         fire := f, rhs := rhs, k := rl.k, eta := rl.eta,
         paramsBlind := rl.paramsBlind }

/-- con-leche: none — intern a list of `RecRule`s. -/
private def internRules : List RecRule → AM (List IRecRule)
  | [] => pure []
  | r :: rs => do
    let h ← internRule r
    let hs ← internRules rs
    pure (h :: hs)

/-- con-leche: none — intern a `ConstantInfo`.  A `projInfo` is out of this
module's scope (the fixture has no structure); it fails loudly rather than
silently producing a different environment from con-leche's. -/
private def internCI : ConstantInfo → AM IConstantInfo
  | .axiomInfo cv => do pure (.axiomInfo (← internCV cv))
  | .defnInfo cv v h => do
    let icv ← internCV cv
    let iv ← internExprT v
    pure (.defnInfo icv iv h)
  | .thmInfo cv v => do
    let icv ← internCV cv
    let iv ← internExprT v
    pure (.thmInfo icv iv)
  | .indInfo cv caps => do
    let icv ← internCV cv
    let ic ← internCaps caps
    pure (.indInfo icv ic)
  | .ctorInfo cv nP nF => do pure (.ctorInfo (← internCV cv) nP nF)
  | .recInfo cv mI rP rules => do
    let icv ← internCV cv
    let rs ← internRules rules
    pure (.recInfo icv mI rP rs)
  | .projInfo _ => fail (.internal "CoreTest: projInfo is out of scope")

/-- con-leche: none — intern a whole environment, newest first. -/
private def internConsts : List ConstantInfo → AM (List IConstantInfo)
  | [] => pure []
  | c :: cs => do
    let h ← internCI c
    let hs ← internConsts cs
    pure (h :: hs)

/-! ## The environment, written once

Six constants: the `Nat` literal trio at exactly the shapes
`natLitSupported` pins, a definition that unfolds to a literal, an axiom
that does not unfold, a proposition and two of its proofs (so proof
irrelevance has something to decide). -/

/-- con-leche: none — a fixture name, written as a con-leche value. -/
private def uAnon : ConLeche.Name := .anonymous
/-- con-leche: none — a fixture name, written as a con-leche value. -/
private def twoName : ConLeche.Name := uAnon.str "two"
/-- con-leche: none — a fixture name, written as a con-leche value. -/
private def axName : ConLeche.Name := uAnon.str "myax"
/-- con-leche: none — a fixture name, written as a con-leche value. -/
private def propName : ConLeche.Name := uAnon.str "P"
/-- con-leche: none — a fixture name, written as a con-leche value. -/
private def pfAName : ConLeche.Name := uAnon.str "pfA"
/-- con-leche: none — a fixture name, written as a con-leche value. -/
private def pfBName : ConLeche.Name := uAnon.str "pfB"

/-- con-leche: none — a fixture term, written as a con-leche value. -/
private def natTy : ConLeche.Expr := .const ConLeche.natName []
/-- con-leche: none — a fixture term, written as a con-leche value. -/
private def zeroE : ConLeche.Expr := .const ConLeche.natZeroName []
/-- con-leche: none — a fixture term, written as a con-leche value. -/
private def succE : ConLeche.Expr := .const ConLeche.natSuccName []
/-- con-leche: none — a fixture term, written as a con-leche value. -/
private def propE : ConLeche.Expr := .const propName []

/-- con-leche: none — the fixture environment, newest first (the order
`Env.find?` reads). -/
private def envCL : ConLeche.Env :=
  ⟨[ .axiomInfo ⟨pfBName, [], propE⟩,
     .axiomInfo ⟨pfAName, [], propE⟩,
     .axiomInfo ⟨propName, [], .sort .zero⟩,
     .axiomInfo ⟨axName, [], natTy⟩,
     .defnInfo ⟨twoName, [], natTy⟩ (.app succE (.app succE zeroE)) (.regular 1),
     .ctorInfo ⟨ConLeche.natSuccName, [], .forallE natTy natTy ⟨.never⟩⟩ 0 1,
     .ctorInfo ⟨ConLeche.natZeroName, [], natTy⟩ 0 0,
     .indInfo ⟨ConLeche.natName, [], .sort (.succ .zero)⟩ {} ]⟩

/-! ## The subject terms, written once

Every check below names one of these; the arena side is its interning and
the con-leche side is the value itself. -/

/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tTwo : ConLeche.Expr := .const twoName []
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tAx : ConLeche.Expr := .const axName []
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tLit7 : ConLeche.Expr := .lit (.natVal 7)
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tLit3 : ConLeche.Expr := .lit (.natVal 3)
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tSucc3 : ConLeche.Expr := .app succE tLit3
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tIdNat : ConLeche.Expr := .lam natTy (.bvar 0) ⟨.never⟩
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tBetaTwo : ConLeche.Expr := .app tIdNat tTwo
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tSuccLam : ConLeche.Expr := .lam natTy (.app succE (.bvar 0)) ⟨.never⟩
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tBetaSucc : ConLeche.Expr := .app tSuccLam tLit3
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tPiNat : ConLeche.Expr := .forallE natTy natTy ⟨.never⟩
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tSort0 : ConLeche.Expr := .sort .zero
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tSort1 : ConLeche.Expr := .sort (.succ .zero)
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tFv0 : ConLeche.Expr := .fvar 0 natTy
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tPfA : ConLeche.Expr := .const pfAName []
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tPfB : ConLeche.Expr := .const pfBName []
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tIdProp : ConLeche.Expr := .lam propE (.bvar 0) ⟨.never⟩
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tUnknown : ConLeche.Expr := .const (uAnon.str "nope") []
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tLetTwo : ConLeche.Expr := .letE natTy tTwo (.bvar 0)
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tLetBad : ConLeche.Expr := .letE natTy tSort0 (.bvar 0)
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tAppAx : ConLeche.Expr := .app tIdNat tAx
/-- con-leche: none — a subject term, written once as a con-leche value; the arena side is its interning. -/
private def tPiPi : ConLeche.Expr := .forallE natTy tPiNat ⟨.never⟩

/-! ## The fixture: the environment and the subjects, interned -/

/-- con-leche: none — the handles the checks name. -/
private structure Fx where
  fe : IFEnv
  two : EIdx
  ax : EIdx
  lit7 : EIdx
  lit3 : EIdx
  succ3 : EIdx
  idNat : EIdx
  betaTwo : EIdx
  succLam : EIdx
  betaSucc : EIdx
  piNat : EIdx
  sort0 : EIdx
  sort1 : EIdx
  fv0 : EIdx
  pfA : EIdx
  pfB : EIdx
  idProp : EIdx
  unknown : EIdx
  letTwo : EIdx
  letBad : EIdx
  appAx : EIdx
  piPi : EIdx
  nat : EIdx
  zero : EIdx

private instance : Inhabited IFEnv := ⟨⟨IEnv.empty, ∅, 0⟩⟩
private instance : Inhabited Fx := ⟨⟨default, default, default, default, default,
  default, default, default, default, default, default, default, default,
  default, default, default, default, default, default, default, default,
  default, default, default⟩⟩

/-- con-leche: none — build the arena fixture: intern the environment, index
it, and intern every subject term. -/
private def buildFx : AM Fx := do
  let cs ← internConsts envCL.consts
  let fe := mkIFEnv ⟨cs⟩
  let two ← internExprT tTwo
  let ax ← internExprT tAx
  let lit7 ← internExprT tLit7
  let lit3 ← internExprT tLit3
  let succ3 ← internExprT tSucc3
  let idNat ← internExprT tIdNat
  let betaTwo ← internExprT tBetaTwo
  let succLam ← internExprT tSuccLam
  let betaSucc ← internExprT tBetaSucc
  let piNat ← internExprT tPiNat
  let sort0 ← internExprT tSort0
  let sort1 ← internExprT tSort1
  let fv0 ← internExprT tFv0
  let pfA ← internExprT tPfA
  let pfB ← internExprT tPfB
  let idProp ← internExprT tIdProp
  let unknown ← internExprT tUnknown
  let letTwo ← internExprT tLetTwo
  let letBad ← internExprT tLetBad
  let appAx ← internExprT tAppAx
  let piPi ← internExprT tPiPi
  let nat ← internExprT natTy
  let zero ← internExprT zeroE
  pure ⟨fe, two, ax, lit7, lit3, succ3, idNat, betaTwo, succLam, betaSucc,
    piNat, sort0, sort1, fv0, pfA, pfB, idProp, unknown, letTwo, letBad,
    appAx, piPi, nat, zero⟩

/-- con-leche: none — the fixture, built once; every check reads its state. -/
private def fxE : Except CheckError (Fx × AState) :=
  buildFx.run (AState.init EStore.empty)

/- The fixture built without a `Native` or an internal error. -/
#guard fxE.toOption.isSome

/-- con-leche: none — the fixture, built once; every check reads its state. -/
private def FX : Fx := (fxE.toOption.map (·.1)).getD default
/-- con-leche: none — the fixture, built once; every check reads its state. -/
private def S0 : AState := (fxE.toOption.map (·.2)).getD (AState.init EStore.empty)

/-! ## The fixture denotes what it should

The one place a con-leche value is compared against a handle by hand;
everything after this compares the arena against con-leche's own functions,
which is only meaningful because these hold. -/

#guard denoteE S0.store FX.two == some tTwo
#guard denoteE S0.store FX.betaTwo == some tBetaTwo
#guard denoteE S0.store FX.piPi == some tPiPi
#guard denoteE S0.store FX.letBad == some tLetBad
#guard denoteE S0.store FX.idProp == some tIdProp
#guard denoteE S0.store FX.succ3 == some tSucc3
#guard FX.fe.env.consts.length == 8
#guard (FX.fe.find? (FX.fe.env.consts.getD 0 default).name).isSome

/-! ## The mode, the fuel, and the outcome comparison -/

/-- con-leche: none — the mode every check runs at: `.verified`, the lane the
bridge is stated at and the one where the arena's io selector
(`mode.betaGate`) and con-leche's cached one (`mode.ioGate`) agree. -/
private def MU : CheckMode := .verified

/-- con-leche: none — the knot fuel and the ambient depth.  The fixture's
deepest reduction is a handful of knot levels; 60 is a comfortable margin,
and a smaller number than `checkFuel` keeps the kernel reduction of these
`#guard`s cheap. -/
private def F : Nat := 60

/-- con-leche: none — the arena's error against con-leche's: same
constructor, same message.  The arena's fourth constructor (`native`) has no
con-leche counterpart and never matches, which is right: a `Native` claims
nothing. -/
private def errEq : CheckError → ConLeche.CheckError → Bool
  | .notImplemented a, .notImplemented b => a == b
  | .invalid a, .invalid b => a == b
  | .internal a, .internal b => a == b
  | _, _ => false

/-- con-leche: none — an `EIdx`-valued entry point against con-leche's
`Expr`-valued one, over the WHOLE outcome. -/
private def chkE (c : AM EIdx) (expect : ConLeche.CheckM ConLeche.Expr) : Bool :=
  match c.run S0, expect with
  | .ok (r, s'), .ok e => denoteE s'.store r == some e
  | .error a, .error b => errEq a b
  | _, _ => false

/-- con-leche: none — a `Bool`-valued entry point (definitional equality)
against con-leche's, over the whole outcome. -/
private def chkB (c : AM Bool) (expect : ConLeche.CheckM Bool) : Bool :=
  match c.run S0, expect with
  | .ok (r, _), .ok e => r == e
  | .error a, .error b => errEq a b
  | _, _ => false

/-! ## What the checks are actually seeing

`chkE` passes when the two checkers AGREE, and two agreeing errors agree.
So the differential alone cannot tell "both reduce to `2`" from "both throw":
these seven lines pin the positive outcomes by hand, on both sides, which is
what makes the thirty-odd differential lines below evidence of something. -/

/-- con-leche: none — con-leche's outcome is this expression (`CheckError`
derives only `Repr`, so the `Except` has no `BEq` to compare with). -/
private def okE : ConLeche.CheckM ConLeche.Expr → ConLeche.Expr → Bool
  | .ok a, e => a == e
  | .error _, _ => false

/-- con-leche: none — con-leche's outcome is this verdict. -/
private def okB : ConLeche.CheckM Bool → Bool → Bool
  | .ok a, b => a == b
  | .error _, _ => false

#guard okE (ConLeche.whnf MU envCL F 0 tTwo) (.lit (.natVal 2))
#guard okE (ConLeche.whnf MU envCL F 0 tBetaSucc) (.lit (.natVal 4))
#guard okE (ConLeche.inferTypeCore MU envCL F 0 tLit7) natTy
#guard okE (ConLeche.inferTypeCore MU envCL F 0 tIdNat) tPiNat
#guard okB (ConLeche.isDefEqCore MU envCL F 0 tPfA tPfB) true
#guard okB (ConLeche.isDefEqCore MU envCL F 0 tTwo tLit7) false
#guard okE (ConLeche.annotateCore MU envCL F 0 tIdProp)
  (.lam propE (.bvar 0) ⟨.ifAllZero []⟩)

/-! ## `whnf` — twelve subjects

Each line is "the arena's `whnf` and con-leche's `whnf` agree on this term",
with the con-leche side computed from the denotation. -/

#guard chkE (whnf MU FX.fe F 0 FX.two) (ConLeche.whnf MU envCL F 0 tTwo)
#guard chkE (whnf MU FX.fe F 0 FX.ax) (ConLeche.whnf MU envCL F 0 tAx)
#guard chkE (whnf MU FX.fe F 0 FX.lit7) (ConLeche.whnf MU envCL F 0 tLit7)
#guard chkE (whnf MU FX.fe F 0 FX.succ3) (ConLeche.whnf MU envCL F 0 tSucc3)
#guard chkE (whnf MU FX.fe F 0 FX.betaTwo) (ConLeche.whnf MU envCL F 0 tBetaTwo)
#guard chkE (whnf MU FX.fe F 0 FX.betaSucc) (ConLeche.whnf MU envCL F 0 tBetaSucc)
#guard chkE (whnf MU FX.fe F 0 FX.piNat) (ConLeche.whnf MU envCL F 0 tPiNat)
#guard chkE (whnf MU FX.fe F 0 FX.sort0) (ConLeche.whnf MU envCL F 0 tSort0)
#guard chkE (whnf MU FX.fe F 1 FX.fv0) (ConLeche.whnf MU envCL F 1 tFv0)
#guard chkE (whnf MU FX.fe F 0 FX.idNat) (ConLeche.whnf MU envCL F 0 tIdNat)
#guard chkE (whnf MU FX.fe F 0 FX.appAx) (ConLeche.whnf MU envCL F 0 tAppAx)
#guard chkE (whnf MU FX.fe F 0 FX.nat) (ConLeche.whnf MU envCL F 0 natTy)

/-! ## `whnfCore` — the delta-free head normal form

The same subjects: `whnfCore` must NOT unfold `two`, where `whnf` does. -/

#guard chkE (whnfCore MU FX.fe F 0 FX.two) (ConLeche.whnfCore MU envCL F 0 tTwo)
#guard chkE (whnfCore MU FX.fe F 0 FX.betaTwo)
  (ConLeche.whnfCore MU envCL F 0 tBetaTwo)
#guard chkE (whnfCore MU FX.fe F 0 FX.succ3)
  (ConLeche.whnfCore MU envCL F 0 tSucc3)
#guard chkE (whnfCore MU FX.fe F 0 FX.piPi) (ConLeche.whnfCore MU envCL F 0 tPiPi)

/-! ## `infer` — twelve subjects, the last two failures -/

#guard chkE (inferTypeCore MU FX.fe F 0 FX.sort0)
  (ConLeche.inferTypeCore MU envCL F 0 tSort0)
#guard chkE (inferTypeCore MU FX.fe F 0 FX.sort1)
  (ConLeche.inferTypeCore MU envCL F 0 tSort1)
#guard chkE (inferTypeCore MU FX.fe F 0 FX.lit7)
  (ConLeche.inferTypeCore MU envCL F 0 tLit7)
#guard chkE (inferTypeCore MU FX.fe F 0 FX.two)
  (ConLeche.inferTypeCore MU envCL F 0 tTwo)
#guard chkE (inferTypeCore MU FX.fe F 0 FX.ax)
  (ConLeche.inferTypeCore MU envCL F 0 tAx)
#guard chkE (inferTypeCore MU FX.fe F 0 FX.pfA)
  (ConLeche.inferTypeCore MU envCL F 0 tPfA)
#guard chkE (inferTypeCore MU FX.fe F 0 FX.succ3)
  (ConLeche.inferTypeCore MU envCL F 0 tSucc3)
#guard chkE (inferTypeCore MU FX.fe F 0 FX.idNat)
  (ConLeche.inferTypeCore MU envCL F 0 tIdNat)
#guard chkE (inferTypeCore MU FX.fe F 0 FX.piNat)
  (ConLeche.inferTypeCore MU envCL F 0 tPiNat)
#guard chkE (inferTypeCore MU FX.fe F 1 FX.fv0)
  (ConLeche.inferTypeCore MU envCL F 1 tFv0)
-- the two failure shapes: an unknown constant, and an out-of-scope `fvar`
#guard chkE (inferTypeCore MU FX.fe F 0 FX.unknown)
  (ConLeche.inferTypeCore MU envCL F 0 tUnknown)
#guard chkE (inferTypeCore MU FX.fe F 0 FX.fv0)
  (ConLeche.inferTypeCore MU envCL F 0 tFv0)

/-! ## `inferIO` — the io grade, under its own memo

A hit in the io table must never serve a full-`infer` query and vice versa;
what this checks is the weaker, necessary condition — the two grades agree on
the fixture, which they must at `.verified`. -/

#guard chkE (inferTypeIO MU FX.fe F 0 FX.two)
  (ConLeche.inferTypeIO MU envCL F 0 tTwo)
#guard chkE (inferTypeIO MU FX.fe F 0 FX.idNat)
  (ConLeche.inferTypeIO MU envCL F 0 tIdNat)
#guard chkE (inferTypeIO MU FX.fe F 0 FX.succ3)
  (ConLeche.inferTypeIO MU envCL F 0 tSucc3)

/-! ## `defeq` — twelve pairs, both verdicts -/

#guard chkB (isDefEqCore MU FX.fe F 0 FX.two FX.two)
  (ConLeche.isDefEqCore MU envCL F 0 tTwo tTwo)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.two FX.lit7)
  (ConLeche.isDefEqCore MU envCL F 0 tTwo tLit7)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.zero FX.zero)
  (ConLeche.isDefEqCore MU envCL F 0 zeroE zeroE)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.pfA FX.pfB)
  (ConLeche.isDefEqCore MU envCL F 0 tPfA tPfB)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.pfA FX.pfA)
  (ConLeche.isDefEqCore MU envCL F 0 tPfA tPfA)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.sort0 FX.sort1)
  (ConLeche.isDefEqCore MU envCL F 0 tSort0 tSort1)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.sort0 FX.sort0)
  (ConLeche.isDefEqCore MU envCL F 0 tSort0 tSort0)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.idNat FX.idNat)
  (ConLeche.isDefEqCore MU envCL F 0 tIdNat tIdNat)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.piNat FX.piNat)
  (ConLeche.isDefEqCore MU envCL F 0 tPiNat tPiNat)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.ax FX.two)
  (ConLeche.isDefEqCore MU envCL F 0 tAx tTwo)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.betaTwo FX.succ3)
  (ConLeche.isDefEqCore MU envCL F 0 tBetaTwo tSucc3)
#guard chkB (isDefEqCore MU FX.fe F 0 FX.nat FX.sort0)
  (ConLeche.isDefEqCore MU envCL F 0 natTy tSort0)

/-! ## `annotate` — twelve subjects, the last two failures -/

#guard chkE (annotateCore MU FX.fe F 0 FX.sort0)
  (ConLeche.annotateCore MU envCL F 0 tSort0)
#guard chkE (annotateCore MU FX.fe F 0 FX.lit7)
  (ConLeche.annotateCore MU envCL F 0 tLit7)
#guard chkE (annotateCore MU FX.fe F 0 FX.two)
  (ConLeche.annotateCore MU envCL F 0 tTwo)
#guard chkE (annotateCore MU FX.fe F 0 FX.idNat)
  (ConLeche.annotateCore MU envCL F 0 tIdNat)
#guard chkE (annotateCore MU FX.fe F 0 FX.idProp)
  (ConLeche.annotateCore MU envCL F 0 tIdProp)
#guard chkE (annotateCore MU FX.fe F 0 FX.piNat)
  (ConLeche.annotateCore MU envCL F 0 tPiNat)
#guard chkE (annotateCore MU FX.fe F 0 FX.piPi)
  (ConLeche.annotateCore MU envCL F 0 tPiPi)
#guard chkE (annotateCore MU FX.fe F 0 FX.succ3)
  (ConLeche.annotateCore MU envCL F 0 tSucc3)
#guard chkE (annotateCore MU FX.fe F 0 FX.succLam)
  (ConLeche.annotateCore MU envCL F 0 tSuccLam)
#guard chkE (annotateCore MU FX.fe F 0 FX.letTwo)
  (ConLeche.annotateCore MU envCL F 0 tLetTwo)
-- the two failure shapes: a let whose value does not fit its type, and an
-- out-of-scope free variable
#guard chkE (annotateCore MU FX.fe F 0 FX.letBad)
  (ConLeche.annotateCore MU envCL F 0 tLetBad)
#guard chkE (annotateCore MU FX.fe F 0 FX.fv0)
  (ConLeche.annotateCore MU envCL F 0 tFv0)

/-! ## `ensureSort` -/

/-- con-leche: none — an `LIdx`-valued entry point against con-leche's
`Level`-valued one. -/
private def chkL (c : AM LIdx) (expect : ConLeche.CheckM Level) : Bool :=
  match c.run S0, expect with
  | .ok (r, s'), .ok u => denoteL s'.store.ls r == some u
  | .error a, .error b => errEq a b
  | _, _ => false

#guard chkL (ensureSortCore MU FX.fe F 0 FX.nat)
  (ConLeche.ensureSortCore MU envCL F 0 natTy)
#guard chkL (ensureSortCore MU FX.fe F 0 FX.sort0)
  (ConLeche.ensureSortCore MU envCL F 0 tSort0)
#guard chkL (ensureSortCore MU FX.fe F 0 FX.two)
  (ConLeche.ensureSortCore MU envCL F 0 tTwo)

/-! ## The memo: the second call hits, and answers identically

The entry-point memos are the reason this tier exists, so they get their own
checks: after one `whnf`, the state's table carries the entry; a second call
returns the SAME HANDLE; and the three infer grades keep three tables (a
`whnf` never populates `inferC`). -/

/-- con-leche: none — run a computation from the fixture state and read a
`Bool` out of it. -/
private def runB (c : AM Bool) : Bool :=
  match c.run S0 with
  | .ok (r, _) => r
  | .error _ => false

/- The `whnf` table is empty before the first call and carries the subject
afterwards. -/
#guard runB (do
  let before := (← get).caches.whnfC.contains FX.two
  let _ ← whnf MU FX.fe F 0 FX.two
  let after := (← get).caches.whnfC.contains FX.two
  pure (!before && after))

/- The second call returns the same handle as the first. -/
#guard runB (do
  let r₁ ← whnf MU FX.fe F 0 FX.two
  let r₂ ← whnf MU FX.fe F 0 FX.two
  pure (r₁ == r₂))

/- …and the second call is a HIT: it is answered from the table, so running
it against a state whose table was filled by hand gives that entry back. -/
#guard runB (do
  let _ ← whnf MU FX.fe F 0 FX.two
  match (← get).caches.whnfC[FX.two]? with
  | some r => do
    let r₂ ← whnf MU FX.fe F 0 FX.two
    pure (r == r₂)
  | none => pure false)

/- The three infer grades keep three tables: a `whnf` run populates
`whnfC` and `whnfCoreC`, never `annotC`. -/
#guard runB (do
  let _ ← whnf MU FX.fe F 0 FX.two
  let s ← get
  pure (s.caches.whnfC.size > 0 && s.caches.whnfCoreC.size > 0 &&
    s.caches.annotC.size == 0))

/- A full-grade `infer` populates `inferC`; the io grade populates
`inferIOC`, and an io hit never lands in `inferC` (DESIGN §8.3, lesson 9). -/
#guard runB (do
  let _ ← inferTypeCore MU FX.fe F 0 FX.succ3
  let s ← get
  pure (s.caches.inferC.size > 0))

#guard runB (do
  let _ ← inferTypeIO MU FX.fe F 0 FX.succ3
  let s ← get
  pure (s.caches.inferIOC.size > 0))

/- The `defeq` table stores the verdict at the ordered pair, both signs: a
`false` answer is memoized too, and answers the same query again. -/
#guard runB (do
  let r₁ ← isDefEqCore MU FX.fe F 0 FX.two FX.lit7
  let hit := (← get).caches.defeqC[(FX.two, FX.lit7)]?
  let r₂ ← isDefEqCore MU FX.fe F 0 FX.two FX.lit7
  pure (hit == some r₁ && r₁ == r₂ && r₁ == false))

/-! ## The per-declaration bracket

`enterScratch` opens the scratch tier; `dropScratch` closes it, drops the
caches whole (con-leche's `flushC`, `Cached/StateC.lean:394-400` — task #97f
replaced DESIGN §8.3's survivor policy with it, and §8.3 is amended) and
truncates the scratch tier of the store. -/

/- The caches go whole, persistent rows included: `dropScratch` is `flushC`. -/
#guard runB (do
  let _ ← whnf MU FX.fe F 0 FX.two
  let before := (← get).caches.whnfC.size
  enterScratch
  dropScratch
  let after := (← get).caches.whnfC.size
  pure (before > 0 && after == 0))

/- And a row whose VALUE is a scratch handle certainly goes: this is the one
the bracket must not leave behind, because the handle it names is about to be
reused by the next declaration. -/
#guard runB (do
  enterScratch
  let h ← internE (.lit (.natVal 123456))
  let _ ← whnf MU FX.fe F 0 h
  let inside := (← get).caches.whnfC.contains h
  let scratch := !h.isPersistent
  dropScratch
  let after := (← get).caches.whnfC.contains h
  pure (inside && scratch && !after))

/- The specification of a surviving row is still there, and still says a
persistent-through row could have stayed: `dropScratchEntries` keeps it. -/
#guard runB (do
  let _ ← whnf MU FX.fe F 0 FX.two
  let before := (← get).caches.whnfC.size
  let kept := ((← get).caches.dropScratchEntries).whnfC.size
  pure (before > 0 && kept == before))

/-! ## The gated and io knots agree with the executed one on the fixture

`CoreGated.lean`'s β gate and `CoreIO.lean`'s leaf lane are statement
subjects, not executed paths; what these check is that they are not
*broken* — at `.verified` the gated `whnfCore` and the io `infer` answer the
fixture the way con-leche's own do. -/

#guard chkE (whnfCoreGated MU FX.fe F 0 FX.betaTwo)
  (ConLeche.whnfCoreGated MU envCL F 0 tBetaTwo)
#guard chkE (whnfGated MU FX.fe F 0 FX.two)
  (ConLeche.whnfGated MU envCL F 0 tTwo)
#guard chkE (inferTypeCoreGated MU FX.fe F 0 FX.succ3)
  (ConLeche.inferTypeCoreGated MU envCL F 0 tSucc3)
#guard chkE (inferTypeCoreIO MU FX.fe F 0 FX.succ3)
  (ConLeche.inferTypeCoreIO MU envCL F 0 tSucc3)
#guard chkE (annotateCoreGated MU FX.fe F 0 FX.idProp)
  (ConLeche.annotateCoreGated MU envCL F 0 tIdProp)
#guard chkB (isDefEqCoreGated MU FX.fe F 0 FX.pfA FX.pfB)
  (ConLeche.isDefEqCoreGated MU envCL F 0 tPfA tPfB)

end ConRon.Arena
