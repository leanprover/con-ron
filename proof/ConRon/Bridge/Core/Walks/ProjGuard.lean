/-
# `ConRon.Bridge.Core.Walks.ProjGuard` — the projection guard, at use

con-leche task #480 checks official `infer_proj`'s restriction where a `.proj`
node is typed (`ConLeche/Kernel/Core.lean:1072-1119`): `projGuardSort`
(`Walks/Former.lean`) decides whether the structure may be a proposition at
the use's levels, `projGuardRows` reads the domains that must then be
propositions off the stored constructor's telescope, and `checkGuardRows`
infers each at the io grade and compares its sort.  This module is Theorem 1
for those walks and for `checkProjGuard`, which `inferProj`
(`Arms/Infer.lean`) runs.
-/
module

public import ConRon.Bridge.Core.Walks.Former
import ConRon.Bridge.Core.Walks.IotaLeaves
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Core.Memo
public import ConRon.Bridge.Core.Knot
public import ConRon.Bridge.Grind
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {eager : Bool} {env : Env} {fe : IFEnv}

/-- con-leche: none — a denoting projection entry survives a store extension. -/
theorem denoteProjEntry_ext {st st' : EStore} {e : IProjEntry} {p : ProjEntry}
    (h : denoteProjEntry st e = some p) (hx : Ext st st') :
    denoteProjEntry st' e = some p := by
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := denoteProjEntry_inv h
  simp only [denoteProjEntry] at h ⊢
  rw [denoteN_ext h1 hx, denoteNListE_ext hx _ _ h2, denoteN_ext h3 hx, denote_ext h4 hx]
  rw [h1, h2, h3, h4] at h
  exact h

/-- con-leche: ConLeche/Kernel/Core.lean:1106-1119 checkProjGuard — **the
guard's answer**: the pure guard passes at some fuel (it answers `()` or
throws, so passing is all a run says). -/
@[expose] def GuardOK (eager : Bool) (env : Env) (p : ProjEntry) (us : List Level) : Prop :=
  ∃ F, checkProjGuard (pureFns .verified eager env F).inferIO (pureFns .verified eager env F).whnf
    env p us = .ok ()

/-- con-leche: ConLeche/Kernel/Core.lean:1106-1119 checkProjGuard
con-leche: ConLeche/Cached/CoreC.lean:993-1004 checkProjGuardI — **THEOREM 1
for `checkProjGuard`**: official `infer_proj`'s restriction at this use. -/
theorem checkProjGuard_spec {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (henv : EnvWF env) (s₀ : AState) (entry : IProjEntry) (p : ProjEntry) (us : LsIdx)
    (ls : List Level) (hok : CheckOK eager env fe s₀)
    (hp : denoteProjEntry s₀.store entry = some p) (hus : denoteLs s₀.store.lss us = some ls) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.checkProjGuard (coreKnot .verified eager fe id fuel) fe entry us
    ⦃fun _ s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        GuardOK eager env p ls; ⊤⦄ := by
  sorry

/-! ## The io view's guard is the record's

`inferBodyIO` runs `inferProj` at `CoreFnsA.ioView r`, whose `inferIO` and
`whnf` slots are `r`'s; the guard reads no other slot. -/

/-- con-leche: none — `formerSortLoop` reads only the `whnf` slot. -/
theorem formerSortLoop_ioView (r : CoreFnsA) :
    ∀ (n d : Nat) (e : EIdx),
      ConRon.Arena.formerSortLoop r.ioView d n e = ConRon.Arena.formerSortLoop r d n e
  | 0, d, e => rfl
  | n + 1, d, e => by
    simp only [ConRon.Arena.formerSortLoop, formerSortLoop_ioView r n]; rfl

/-- con-leche: none — `checkGuardRows` reads only the `inferIO` and `whnf`
slots. -/
theorem checkGuardRows_ioView (r : CoreFnsA) (g : Level) (rows : Array (Nat × EIdx))
    (i : Nat) :
    ConRon.Arena.checkGuardRows r.ioView g rows i = ConRon.Arena.checkGuardRows r g rows i := by
  rw [ConRon.Arena.checkGuardRows.eq_1 r.ioView, ConRon.Arena.checkGuardRows.eq_1 r]
  by_cases hi : i < rows.size
  · simp only [dite_eq_left hi, checkGuardRows_ioView r g rows (i + 1)]; rfl
  · simp only [dite_eq_right hi]
termination_by rows.size - i

/-- con-leche: none — `checkProjGuard` reads only the `inferIO` and `whnf`
slots. -/
theorem checkProjGuard_ioView (r : CoreFnsA) (entry : IProjEntry) (us : LsIdx) :
    ConRon.Arena.checkProjGuard r.ioView fe entry us =
      ConRon.Arena.checkProjGuard r fe entry us := by
  simp only [ConRon.Arena.checkProjGuard, ConRon.Arena.projGuardSort, formerSortLoop_ioView,
    checkGuardRows_ioView]

end ConRon.Bridge.Core
