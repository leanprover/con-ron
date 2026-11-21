/-
# `ConRon.Bridge.Inductives.IotaRead` — Theorem 1 for the ι reading rule

`Arena/Inductives/IotaRead.lean` against con-leche's
`ConLeche/Kernel/Inductives/IotaRead.lean` (`blockReadsOk`) and `IotaEq.lean`.
-/
module

public import ConRon.Bridge.Grind
import ConRon.Bridge.Specs
import ConRon.Bridge.SpecsL
import ConRon.Bridge.GrindAttr
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.IotaLeaves
public import ConRon.Arena.Inductives.IotaRead
public import ConLeche.Kernel.Inductives.IotaRead

public section

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## `piTele` -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:83-86 Expr.piTele — one
equation over the tag. -/
theorem piTele_eq (x : Expr) : x.piTele =
    if exprTag x = ETag.forallE then ((exprBody x).piTele.1 + 1, (exprBody x).piTele.2)
    else (0, x) := by
  cases x <;> simp [Expr.piTele, exprTag, exprBody, ETag.forallE, ETag.bvar,
    ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:83-86 Expr.piTele —
**THEOREM 1** for `piTele`: the binder count and the body. -/
theorem piTele_spec : ∀ (fuel : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ piTele fuel h
    ⦃fun r s' => s' = s₀ ∧ RelV (fun e => e.piTele.1) s₀.store h r.1 ∧
        RelE (fun e => e.piTele.2) s₀.store h s₀.store r.2; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ h _ _
    sym only [bridge_grind] => vcgen [piTele] <;> finish
  | succ fuel ih =>
    intro s₀ h hok hden
    sym only [bridge_grind, piTele_eq] => vcgen [piTele, ih] <;> finish

variable {eager : Bool} {env : Env} {fe : IFEnv}

/-! ## `lvlEq` -/

local grind_pattern [bridge_grind] nameIdx => denoteN st.ns n
local grind_pattern [bridge_grind] NameIdx.some => NameIdx st n (some nm)
local grind_pattern [bridge_grind] eIdxAt => denoteE st n
local grind_pattern [bridge_grind] EIdxAt.some => EIdxAt st n (some e)

local grind_pattern [bridge_grind] view_of_viewConst => st.viewConst i, some (n, us) where
  guard st.viewConst i = some (n, us)

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:99-112 Expr.lvlEq — its
answer at two denotations. -/
@[expose] def LvlEqA (x y : Expr) (r : Bool) : Prop := r = x.lvlEq y

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:99-112 Expr.lvlEq — one
equation over the tags and the projections. -/
theorem lvlEq_eq (x y : Expr) : x.lvlEq y =
    if x = y then true
    else if exprTag x ≠ exprTag y then false
    else if exprTag x = ETag.sort then Level.isEquiv (exprSort x) (exprSort y) == some true
    else if exprTag x = ETag.const then
      (exprConstName x == exprConstName y &&
        Level.isEquivList (exprConstLevels x) (exprConstLevels y) == some true)
    else if exprTag x = ETag.app then
      ((exprFn x).lvlEq (exprFn y) && (exprArg x).lvlEq (exprArg y))
    else if exprTag x = ETag.lam ∨ exprTag x = ETag.forallE then
      ((exprBinderType x).lvlEq (exprBinderType y) && (exprBody x).lvlEq (exprBody y))
    else if exprTag x = ETag.letE then
      ((exprBinderType x).lvlEq (exprBinderType y) &&
        (exprLetVal x).lvlEq (exprLetVal y) && (exprBody x).lvlEq (exprBody y))
    else if exprTag x = ETag.proj then
      (exprProjName x == exprProjName y && exprProjIdx x == exprProjIdx y &&
        (exprProjStruct x).lvlEq (exprProjStruct y))
    else false := by
  by_cases hxy : x = y
  · subst hxy; simp only [↓reduceIte]; cases x <;> simp [Expr.lvlEq]
  simp only [hxy, ↓reduceIte]
  have hb : (x == y) = false := by simpa using hxy
  have lv : ∀ t v b, exprLetVal (.letE t v b) = v := fun t v b => by
    have := exprTag_letE (e := .letE t v b) rfl
    injection this with _ h; exact h.symm
  have ps : ∀ n i e, exprProjStruct (.proj n i e) = e := fun n i e => by
    have := exprTag_proj (e := .proj n i e) rfl
    injection this with _ _ h; exact h.symm
  cases x <;> cases y <;> simp_all [Expr.lvlEq, exprTag, exprSort, exprConstName,
    exprConstLevels, exprFn, exprArg, exprBinderType, exprBody, exprProjName, exprProjIdx,
    ETag.forallE, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE,
    ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:99-112 Expr.lvlEq —
**THEOREM 1** for `lvlEq`: equal up to equivalent universe levels. -/
theorem lvlEq_spec : ∀ (fuel : Nat) (s₀ : AState) (a b : EIdx),
    CheckOK eager env fe s₀ → (denoteE s₀.store a).isSome = true →
    (denoteE s₀.store b).isSome = true →
    ⦃fun s => s = s₀⦄ lvlEq fuel a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        PairAns LvlEqA (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ a b _ _ _
    sym only [bridge_grind] => vcgen [lvlEq] <;> finish
  | succ fuel ih =>
    intro s₀ a b hok ha hb
    sym only [bridge_grind, lvlEq_eq, LvlEqA] =>
      vcgen [lvlEq, ih, Core.readLevelM_specC (eager := eager) (env := env) (fe := fe),
        Core.readLevelsM_specC (eager := eager) (env := env) (fe := fe)] <;> finish

end ConRon.Bridge.Inductives
