import ConRon.Bridge.Specs

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

structure SizeBSpec (rec : EIdx → AM Nat) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx), StateOK s₁ →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c
    ⦃⇓? r s' => ⌜s' = s₁ ∧ RelV Expr.sizeB s₁.store c r⌝⦄

theorem sizeB_spec : ∀ fuel, SizeBSpec (Arena.sizeB fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _
    mvcgen [Arena.sizeB]
    all_goals bridge_vcs [Expr.sizeB, RelV]
  | succ fuel ih =>
    constructor
    intro s₀ h hok hden
    have hrec := ih.run
    mvcgen [Arena.sizeB, hrec]
    all_goals bridge_vcs [Expr.sizeB, RelV]

end ConRon.Bridge.ExprOps
