/-
# `ConRon.Bridge.Core.Arms.Defeq` — Theorem 1 for `defeqBody`

DESIGN §8.2, rule 8's inventory for con-leche 8afe1815's definitional
equality (`ConLeche/Kernel/Core.lean:1478-1831`, `quickDefEq` … `defeqBody`),
restructured after the official `is_def_eq_core` (DESIGN `### Task #109`).  One spec per
twin function, each relating `Arena/Core.lean`'s function to con-leche's at
`pureFns .verified eager env F`, with the frame (`CheckOK`, `Ext`, pins) and the pure
answer at some fuel (`Ev`, `DqPost`: `Arms/DefeqBase.lean`):

| twin function | spec | module |
|---|---|---|
| `quickDefEq` (∀ and λ arms: `defeqBinders`) | `quickDefEq_spec` (`defeqBinders_spec`) | `Arms/DefeqLazy.lean` (`Arms/DefeqBinders.lean`) |
| `isNatZero`, `natPred?`, `defeqOffset` | `isNatZero_spec`, `natPred?_spec`, `defeqOffset_spec` | `Arms/DefeqLazy.lean` |
| `headIsProj`, `tryUnfoldProjApp` | `headIsProj_spec`, `tryUnfoldProjApp_spec` | `Arms/DefeqLazy.lean` |
| `deltaQuick`, `lazyDeltaStep` | `deltaQuick_spec`, `lazyDeltaStep_spec` | `Arms/DefeqLazy.lean` |
| `lazyDeltaReduction` (induction on the budget) | `lazyDeltaReduction_spec` | `Arms/DefeqLazy.lean` |
| `defeqStuck` | `defeqStuck_spec` | `Arms/DefeqStuck.lean` |
| `lazyDeltaProjReduction` (induction on the budget) | `lazyDeltaProjReduction_spec` | here, §2 |
| `defeqProjPair` | `defeqProjPair_spec` | here, §2 |
| `defeqBody` | `defeqBody_spec` (via `defeqBody_at`) | here, §3 |

The pure side of `defeqBody` is §1: one equation per exit of con-leche's
body, each under the facts the exit has established (`defeqBody_quick` …
`defeqBody_restart`).  The projection rule of `lazyDeltaProjReduction` is
`Walks/ProjCore.lean`'s `reduceProjCore_spec`.

## The binder-telescope congruence

`quickDefEq`'s `.forallE` and `.lam` arms are con-leche's `defeqBinders`
(the official `is_def_eq_binding` shape), run level by level by the twin as
well; the twin keeps the variables in a push-order vector and opens each
domain and the two innermost bodies with ONE `instantiateList` over it.  Its
spec is `Arms/DefeqBinders.lean`'s `defeqBinders_spec`.
-/
module

public import ConRon.Bridge.Core.Arms.DefeqLazy
import ConRon.Bridge.Core.Arms.DefeqStuck
import ConRon.Bridge.Core.Walks.ProjCore
import ConRon.Bridge.Core.Walks.Guards
import ConRon.Bridge.ExprOps.Ranges
import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.Core.Walks.Owed
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.ExprOps.Spine
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Specs
import ConRon.Bridge.Core.Arms.DefeqBinders -- shake: keep (`#print axioms` names it; no proof term does)

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool} {env : Env}

/-! ## 1. The pure side of `defeqBody`, exit by exit -/

section PureBody

variable {F d : Nat} {x y x' y' : Expr}

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — **the
syntactic fast path**. -/
theorem defeqBody_syntactic (h : (x == y) = true) :
    ConLeche.defeqBody mode eager (ConLeche.pureFns mode eager env F) env d x y = .ok true := by
  rw [ConLeche.defeqBody]
  simp only [h, ite_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1842-1884 defeqBody — **the constructor
shortcut at a target on the right**, its three exits: the left side's normal
form `w` headed by the target continues with the lazy comparison of `w`. -/
theorem defeqBody_rightT {cn : Name} {w : Expr} (hab : (x == y) = false)
    (ht : ConLeche.ctorTargetFor env eager x y = some cn)
    (hw : ConLeche.whnf mode eager env F d x = .ok w)
    (ho : ConLeche.ctorHeadAgainst env cn w = some true) :
    ConLeche.defeqBody mode eager (ConLeche.pureFns mode eager env F) env d x y =
      ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d w y := by
  rw [ConLeche.defeqBody]
  simp only [hab, Bool.false_eq_true, ite_false, ht, ConLeche.whnf_def, hw, ho, bind,
    Except.bind]

/-- con-leche: ConLeche/Kernel/Core.lean:1842-1884 defeqBody — another
constructor's head: `false`. -/
theorem defeqBody_rightF {cn : Name} {w : Expr} (hab : (x == y) = false)
    (ht : ConLeche.ctorTargetFor env eager x y = some cn)
    (hw : ConLeche.whnf mode eager env F d x = .ok w)
    (ho : ConLeche.ctorHeadAgainst env cn w = some false) :
    ConLeche.defeqBody mode eager (ConLeche.pureFns mode eager env F) env d x y = .ok false := by
  rw [ConLeche.defeqBody]
  simp only [hab, Bool.false_eq_true, ite_false, ht, ConLeche.whnf_def, hw, ho, bind,
    Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1842-1884 defeqBody — any other head:
the lazy comparison of the original pair. -/
theorem defeqBody_rightN {cn : Name} {w : Expr} (hab : (x == y) = false)
    (ht : ConLeche.ctorTargetFor env eager x y = some cn)
    (hw : ConLeche.whnf mode eager env F d x = .ok w)
    (ho : ConLeche.ctorHeadAgainst env cn w = none) :
    ConLeche.defeqBody mode eager (ConLeche.pureFns mode eager env F) env d x y =
      ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x y := by
  rw [ConLeche.defeqBody]
  simp only [hab, Bool.false_eq_true, ite_false, ht, ConLeche.whnf_def, hw, ho, bind,
    Except.bind]

/-- con-leche: ConLeche/Kernel/Core.lean:1842-1884 defeqBody — **the constructor
shortcut at a target on the left** (no target on the right): the right side's
normal form headed by the target continues with the lazy comparison. -/
theorem defeqBody_leftT {cn : Name} {w : Expr} (hab : (x == y) = false)
    (ht0 : ConLeche.ctorTargetFor env eager x y = none)
    (ht : ConLeche.ctorTargetFor env eager y x = some cn)
    (hw : ConLeche.whnf mode eager env F d y = .ok w)
    (ho : ConLeche.ctorHeadAgainst env cn w = some true) :
    ConLeche.defeqBody mode eager (ConLeche.pureFns mode eager env F) env d x y =
      ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x w := by
  rw [ConLeche.defeqBody]
  simp only [hab, Bool.false_eq_true, ite_false, ht0, ht, ConLeche.whnf_def, hw, ho, bind,
    Except.bind]

/-- con-leche: ConLeche/Kernel/Core.lean:1842-1884 defeqBody — the left
target against another constructor: `false`. -/
theorem defeqBody_leftF {cn : Name} {w : Expr} (hab : (x == y) = false)
    (ht0 : ConLeche.ctorTargetFor env eager x y = none)
    (ht : ConLeche.ctorTargetFor env eager y x = some cn)
    (hw : ConLeche.whnf mode eager env F d y = .ok w)
    (ho : ConLeche.ctorHeadAgainst env cn w = some false) :
    ConLeche.defeqBody mode eager (ConLeche.pureFns mode eager env F) env d x y = .ok false := by
  rw [ConLeche.defeqBody]
  simp only [hab, Bool.false_eq_true, ite_false, ht0, ht, ConLeche.whnf_def, hw, ho, bind,
    Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1842-1884 defeqBody — the left
target against any other head: the lazy comparison of the original pair. -/
theorem defeqBody_leftN {cn : Name} {w : Expr} (hab : (x == y) = false)
    (ht0 : ConLeche.ctorTargetFor env eager x y = none)
    (ht : ConLeche.ctorTargetFor env eager y x = some cn)
    (hw : ConLeche.whnf mode eager env F d y = .ok w)
    (ho : ConLeche.ctorHeadAgainst env cn w = none) :
    ConLeche.defeqBody mode eager (ConLeche.pureFns mode eager env F) env d x y =
      ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x y := by
  rw [ConLeche.defeqBody]
  simp only [hab, Bool.false_eq_true, ite_false, ht0, ht, ConLeche.whnf_def, hw, ho, bind,
    Except.bind]

/-- con-leche: ConLeche/Kernel/Core.lean:1842-1884 defeqBody — no target on
either side: the lazy comparison. -/
theorem defeqBody_lazy (hab : (x == y) = false)
    (ht0 : ConLeche.ctorTargetFor env eager x y = none)
    (ht1 : ConLeche.ctorTargetFor env eager y x = none) :
    ConLeche.defeqBody mode eager (ConLeche.pureFns mode eager env F) env d x y =
      ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x y := by
  rw [ConLeche.defeqBody]
  simp only [hab, Bool.false_eq_true, ite_false, ht0, ht1]

/-- con-leche: ConLeche/Kernel/Core.lean:1789-1840 defeqLazy — the lazy
comparison: `quickDefEq` and proof irrelevance on the UNREDUCED pair, then
the cheap head normal forms and what follows. -/
theorem defeqLazy_pre0 :
    ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x y =
      (ConLeche.quickDefEq mode (ConLeche.pureFns mode eager env F) d x y >>= fun o =>
        match o with
        | some v => pure v
        | none => do
          if ← ConLeche.propIrrel (ConLeche.pureFns mode eager env F) env d x y then
            pure true else
          let x' ← (ConLeche.pureFns mode eager env F).whnfCore true d x
          let y' ← (ConLeche.pureFns mode eager env F).whnfCore true d y
          match ← ConLeche.quickDefEq mode (ConLeche.pureFns mode eager env F) d x' y' with
          | some v => pure v
          | none =>
          match ← ConLeche.lazyDeltaReduction mode eager (ConLeche.pureFns mode eager env F)
              env d ConLeche.defeqLoopFuel x' y' with
          | .verdict v => pure v
          | .unknown a₁ b₁ =>
          if ← ConLeche.defeqProjPair mode (ConLeche.pureFns mode eager env F) env d a₁ b₁
            then pure true else
          if !a₁.headIsProj && !b₁.headIsProj then
            ConLeche.defeqStuck mode (ConLeche.pureFns mode eager env F) env d a₁ b₁ else
          let a₂ ← (ConLeche.pureFns mode eager env F).whnfCore false d a₁
          let b₂ ← (ConLeche.pureFns mode eager env F).whnfCore false d b₁
          if a₂ == a₁ && b₂ == b₁ then
            ConLeche.defeqStuck mode (ConLeche.pureFns mode eager env F) env d a₁ b₁
          else (ConLeche.pureFns mode eager env F).defeq d a₂ b₂) := by
  rw [ConLeche.defeqLazy]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1789-1840 defeqLazy — the easy
cases decide on the UNREDUCED pair. -/
theorem defeqLazy_quick0 {v : Bool}
    (hq : ConLeche.quickDefEq mode (ConLeche.pureFns mode eager env F) d x y
      = .ok (some v)) :
    ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x y = .ok v := by
  rw [defeqLazy_pre0, hq]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1789-1840 defeqLazy — **proof
irrelevance**, on the UNREDUCED pair (con-leche task #333). -/
theorem defeqLazy_propIrrel
    (hq : ConLeche.quickDefEq mode (ConLeche.pureFns mode eager env F) d x y = .ok none)
    (hpi : ConLeche.propIrrel (ConLeche.pureFns mode eager env F) env d x y = .ok true) :
    ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x y = .ok true := by
  rw [defeqLazy_pre0, hq]
  simp only [bind, Except.bind, hpi]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1789-1840 defeqLazy — **the prefix
every later exit has run**, at one fuel: no easy case and no proof
irrelevance on the unreduced pair, the two cheap head normal forms. -/
structure DbPre (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat)
    (x y x' y' : Expr) : Prop where
  hq0 : ConLeche.quickDefEq mode (ConLeche.pureFns mode eager env F) d x y = .ok none
  hpi0 : ConLeche.propIrrel (ConLeche.pureFns mode eager env F) env d x y = .ok false
  ha : ConLeche.whnfCore mode eager env F d x true = .ok x'
  hb : ConLeche.whnfCore mode eager env F d y true = .ok y'

/-- con-leche: ConLeche/Kernel/Core.lean:1789-1840 defeqLazy — past the
prefix: `quickDefEq` on the cheap head normal forms and what follows. -/
theorem defeqLazy_pre (h : DbPre mode eager env F d x y x' y') :
    ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x y =
      (ConLeche.quickDefEq mode (ConLeche.pureFns mode eager env F) d x' y' >>= fun o =>
        match o with
        | some v => pure v
        | none => do
          match ← ConLeche.lazyDeltaReduction mode eager (ConLeche.pureFns mode eager env F)
              env d ConLeche.defeqLoopFuel x' y' with
          | .verdict v => pure v
          | .unknown a₁ b₁ =>
          if ← ConLeche.defeqProjPair mode (ConLeche.pureFns mode eager env F) env d a₁ b₁
            then pure true else
          if !a₁.headIsProj && !b₁.headIsProj then
            ConLeche.defeqStuck mode (ConLeche.pureFns mode eager env F) env d a₁ b₁ else
          let a₂ ← (ConLeche.pureFns mode eager env F).whnfCore false d a₁
          let b₂ ← (ConLeche.pureFns mode eager env F).whnfCore false d b₁
          if a₂ == a₁ && b₂ == b₁ then
            ConLeche.defeqStuck mode (ConLeche.pureFns mode eager env F) env d a₁ b₁
          else (ConLeche.pureFns mode eager env F).defeq d a₂ b₂) := by
  rw [defeqLazy_pre0, h.hq0]
  simp only [bind, Except.bind, h.hpi0, Bool.false_eq_true, ite_false,
    ConLeche.whnfCore_def, h.ha, h.hb]

/-- con-leche: ConLeche/Kernel/Core.lean:1789-1840 defeqLazy — the easy
cases decide. -/
theorem defeqLazy_quick {v : Bool} (h : DbPre mode eager env F d x y x' y')
    (hq : ConLeche.quickDefEq mode (ConLeche.pureFns mode eager env F) d x' y'
      = .ok (some v)) :
    ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x y = .ok v := by
  rw [defeqLazy_pre h, hq]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1789-1840 defeqLazy — the facts
past the lazy-delta loop that the last four exits share. -/
structure DbMid (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat)
    (x' y' : Expr) (r : LazyRes) : Prop where
  hq : ConLeche.quickDefEq mode (ConLeche.pureFns mode eager env F) d x' y' = .ok none
  hl : ConLeche.lazyDeltaReduction mode eager (ConLeche.pureFns mode eager env F) env d
    ConLeche.defeqLoopFuel x' y' = .ok r

/-- con-leche: ConLeche/Kernel/Core.lean:1789-1840 defeqLazy — **the
lazy-delta loop decides**. -/
theorem defeqLazy_verdict {v : Bool} (h : DbPre mode eager env F d x y x' y')
    (hm : DbMid mode eager env F d x' y' (.verdict v)) :
    ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x y = .ok v := by
  rw [defeqLazy_pre h, hm.hq]
  simp only [bind, Except.bind, hm.hl]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1789-1840 defeqLazy — past the
loop's `unknown`: the proj/proj check and what follows. -/
theorem defeqLazy_unknown {a₁ b₁ : Expr} (h : DbPre mode eager env F d x y x' y')
    (hm : DbMid mode eager env F d x' y' (.unknown a₁ b₁)) :
    ConLeche.defeqLazy mode eager (ConLeche.pureFns mode eager env F) env d x y =
      (ConLeche.defeqProjPair mode (ConLeche.pureFns mode eager env F) env d a₁ b₁ >>=
        fun pp => if pp = true then pure true else
          if (!a₁.headIsProj && !b₁.headIsProj) = true then
            ConLeche.defeqStuck mode (ConLeche.pureFns mode eager env F) env d a₁ b₁ else
          (ConLeche.whnfCore mode eager env F d a₁ false >>= fun a₂ =>
            ConLeche.whnfCore mode eager env F d b₁ false >>= fun b₂ =>
            if (a₂ == a₁ && b₂ == b₁) = true then
              ConLeche.defeqStuck mode (ConLeche.pureFns mode eager env F) env d a₁ b₁
            else ConLeche.isDefEqCore mode eager env F d a₂ b₂)) := by
  rw [defeqLazy_pre h, hm.hq]
  simp only [bind, Except.bind, hm.hl]
  rfl

end PureBody

/-! ## 2. The proj/proj check: `lazyDeltaProjReduction`, `defeqProjPair` -/

section ProjPair

variable {fe : IFEnv} {fuel : Nat}

/-- con-leche: ConLeche/Kernel/Core.lean:1743-1779 lazyDeltaProjReduction —
the loop's tail once the step found the scrutinees different or stuck, for a
BARE pair: the projection on both, and the fields, or else the scrutinees,
compared. -/
def ldprTail (r : CoreFns CheckM) (env : Env) (d : Nat)
    (sn : Name) (i : Nat) (a b : Expr) : CheckM Bool := do
  match ← ConLeche.reduceProjCore .verified r env d sn i a with
  | some x =>
    match ← ConLeche.reduceProjCore .verified r env d sn i b with
    | some y => r.defeq d x y
    | none => r.defeq d a b
  | none => r.defeq d a b

/-- con-leche: ConLeche/Kernel/Core.lean:1743-1779 lazyDeltaProjReduction —
**the tail on the twin side**, against `ldprTail`. -/
theorem ldprTail_spec (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (d : Nat) (sn : NIdx) (nm : Name)
    (i : Nat) {s₀ s₁ : AState} (a b : EIdx) (x y : Expr)
    (hok : CheckOK eager env fe s₁) (hx₁ : Ext s₀.store s₁.store)
    (hp₁ : s₁.pins = s₀.pins) (hsn : denoteN s₁.store.ns sn = some nm)
    (hx : denoteE s₁.store a = some x) (hy : denoteE s₁.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y)
    (G : Nat → Bool → Prop)
    (hG : Ev (fun F => ∀ r, ldprTail (ConLeche.pureFns .verified eager env F) env d nm i
      x y = .ok r → G F r)) :
    ⦃fun s => s = s₁⦄
      (do
        match ← ConRon.Arena.reduceProjCore .verified (coreKnot .verified eager fe id fuel) fe d sn i a with
        | some p =>
          match ← ConRon.Arena.reduceProjCore .verified (coreKnot .verified eager fe id fuel) fe d sn i b with
          | some q => (coreKnot .verified eager fe id fuel).defeq d p q
          | none => (coreKnot .verified eager fe id fuel).defeq d a b
        | none => (coreKnot .verified eager fe id fuel).defeq d a b)
    ⦃fun r s' => DqPost eager env fe s₀ G r s'; ⊤⦄ := by
  refine triple_seq (reduceProjCore_spec henv hsim s₁ d sn i a nm x hok hsn hx hwx) ?_
  rintro o1 s2 ⟨hok2, hx2, hp2, v1, hv1, hwv1, F1, hF1⟩
  have hR1 : Ev (fun F => ConLeche.reduceProjCore .verified (ConLeche.pureFns .verified eager env F)
      env d nm i x = .ok v1) :=
    Ev.of_mono (fun hle h => reduceProjCoreFueled_mono hle h) ⟨F1, hF1⟩
  have hx12 := hx₁.trans hx2
  have hp12 : s2.pins = s₀.pins := hp2.trans hp₁
  cases o1 with
  | none =>
    obtain rfl := denoteEO_none_inv hv1
    exact dq_defeq_exit hsim a b x y hok2 hx12 hp12 (denote_ext hx hx2)
      (denote_ext hy hx2) hwx hwy ((hG.and hR1).imp fun F ⟨h, h1⟩ r hr => h r (by
        unfold ldprTail; simp only [h1, bind, Except.bind]; exact hr))
  | some p =>
    obtain ⟨px, rfl, hdp⟩ := denoteEO_some_inv hv1
    dsimp only
    refine triple_seq (reduceProjCore_spec henv hsim s2 d sn i b nm y hok2
      (denoteN_ext hsn hx2) (denote_ext hy hx2) hwy) ?_
    rintro o2 s3 ⟨hok3, hx3, hp3, v2, hv2, hwv2, F2, hF2⟩
    have hR2 : Ev (fun F => ConLeche.reduceProjCore .verified (ConLeche.pureFns .verified eager env F)
        env d nm i y = .ok v2) :=
      Ev.of_mono (fun hle h => reduceProjCoreFueled_mono hle h) ⟨F2, hF2⟩
    have hx13 := hx12.trans hx3
    have hp13 : s3.pins = s₀.pins := hp3.trans hp12
    cases o2 with
    | none =>
      obtain rfl := denoteEO_none_inv hv2
      exact dq_defeq_exit hsim a b x y hok3 hx13 hp13 (denote_ext hx (hx2.trans hx3))
        (denote_ext hy (hx2.trans hx3)) hwx hwy
        (((hG.and hR1).and hR2).imp fun F ⟨⟨h, h1⟩, h2⟩ r hr => h r (by
          unfold ldprTail; simp only [h1, h2, bind, Except.bind]; exact hr))
    | some q =>
      obtain ⟨qy, rfl, hdq⟩ := denoteEO_some_inv hv2
      exact dq_defeq_exit hsim p q px qy hok3 hx13 hp13 (denote_ext hdp hx3) hdq
        (hwv1 px rfl) (hwv2 qy rfl)
        (((hG.and hR1).and hR2).imp fun F ⟨⟨h, h1⟩, h2⟩ r hr => h r (by
          unfold ldprTail; simp only [h1, h2, bind, Except.bind]; exact hr))

/-- con-leche: none — a handle list and its denotation are empty together. -/
theorem isEmpty_of_denoteEList {st : EStore} {hs : List EIdx} {xs : List Expr}
    (h : Frontend.denoteEList st hs = some xs) : xs.isEmpty = hs.isEmpty := by
  have hl := denoteEList_len h
  cases hs <;> cases xs <;> simp_all

/-- con-leche: ConLeche/Kernel/Core.lean:1743-1779 lazyDeltaProjReduction —
**the tail of an applied or bare pair**: `ldprTail` when both argument lists
are empty, `false` otherwise, on both sides. -/
theorem ldprTailL_spec (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (d : Nat) (sn : NIdx) (nm : Name)
    (i : Nat) {s₀ s₁ : AState} (as bs : List EIdx) (xs ys : List Expr) (a b : EIdx) (x y : Expr)
    (hok : CheckOK eager env fe s₁) (hx₁ : Ext s₀.store s₁.store)
    (hp₁ : s₁.pins = s₀.pins) (hsn : denoteN s₁.store.ns sn = some nm)
    (hxs : Frontend.denoteEList s₁.store as = some xs)
    (hys : Frontend.denoteEList s₁.store bs = some ys)
    (hx : denoteE s₁.store a = some x) (hy : denoteE s₁.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y)
    (G : Nat → Bool → Prop)
    (hG : Ev (fun F => ∀ r, (if xs.isEmpty && ys.isEmpty then
      ldprTail (ConLeche.pureFns .verified eager env F) env d nm i x y else pure false) = .ok r →
        G F r)) :
    ⦃fun s => s = s₁⦄
      (if as.isEmpty && bs.isEmpty then do
        match ← ConRon.Arena.reduceProjCore .verified (coreKnot .verified eager fe id fuel) fe d sn i a with
        | some p =>
          match ← ConRon.Arena.reduceProjCore .verified (coreKnot .verified eager fe id fuel) fe d sn i b with
          | some q => (coreKnot .verified eager fe id fuel).defeq d p q
          | none => (coreKnot .verified eager fe id fuel).defeq d a b
        | none => (coreKnot .verified eager fe id fuel).defeq d a b
      else pure false)
    ⦃fun r s' => DqPost eager env fe s₀ G r s'; ⊤⦄ := by
  rw [← isEmpty_of_denoteEList hxs, ← isEmpty_of_denoteEList hys]
  split
  · rename_i hE
    exact ldprTail_spec henv hsim d sn nm i a b x y hok hx₁ hp₁ hsn hx hy hwx hwy G
      (hG.imp fun _ h r hr => h r (by rw [ite_eq_left hE]; exact hr))
  · rename_i hE
    exact triple_pure_post ⟨hok, hx₁, hp₁, Ev.exists (hG.imp fun _ h =>
      h false (by rw [ite_eq_right hE]; rfl))⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1743-1779 lazyDeltaProjReduction —
**THEOREM 1 for the projection loop**, at every budget, by induction on it:
one `lazyDeltaStep` on the scrutinees, whose `cont` is the next iteration,
whose `eq` compares the reversed argument lists (`defEqList_spec`), and whose
`diff`/`unknown` hand over to `ldprTailL_spec`. -/
theorem lazyDeltaProjReduction_spec (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (d : Nat) (sn : NIdx) (nm : Name)
    (i : Nat) (as bs : List EIdx) (xs ys : List Expr)
    (hwxs : ∀ z ∈ xs, Expr.WScoped d z) (hwys : ∀ z ∈ ys, Expr.WScoped d z) :
    ∀ (n : Nat) (s₀ : AState) (a b : EIdx) (x y : Expr),
      CheckOK eager env fe s₀ → denoteN s₀.store.ns sn = some nm →
      Frontend.denoteEList s₀.store as = some xs → Frontend.denoteEList s₀.store bs = some ys →
      denoteE s₀.store a = some x → denoteE s₀.store b = some y →
      Expr.WScoped d x → Expr.WScoped d y →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.lazyDeltaProjReduction .verified (coreKnot .verified eager fe id fuel) fe d sn i
          as bs n a b
      ⦃fun r s' => DqPost eager env fe s₀ (fun F r =>
          ConLeche.lazyDeltaProjReduction .verified (ConLeche.pureFns .verified eager env F) env d
            nm i xs ys n x y = .ok r) r s'; ⊤⦄
  | 0, s₀, a, b, x, y, _, _, _, _, _, _, _, _ => by
    rw [ConRon.Arena.lazyDeltaProjReduction]
    exact triple_fail
  | n + 1, s₀, a, b, x, y, hok, hsn, hxs, hys, hx, hy, hwx, hwy => by
    rw [ConRon.Arena.lazyDeltaProjReduction]
    refine triple_seq (lazyDeltaStep_spec henv hsim d s₀ a b x y hok hx hy hwx hwy) ?_
    rintro st s1 ⟨hok1, hx1, hp1, w, hr, hS⟩
    have hstep : ∀ F, ConLeche.lazyDeltaStep .verified (ConLeche.pureFns .verified eager env F) env d
        x y = .ok w →
        ConLeche.lazyDeltaProjReduction .verified (ConLeche.pureFns .verified eager env F) env d nm i
          xs ys (n + 1) x y =
        (match w with
          | .cont a' b' => ConLeche.lazyDeltaProjReduction .verified
              (ConLeche.pureFns .verified eager env F) env d nm i xs ys n a' b'
          | .eq => ConLeche.defEqList (ConLeche.pureFns .verified eager env F) env d
              xs.reverse ys.reverse
          | .diff => if xs.isEmpty && ys.isEmpty then
              ldprTail (ConLeche.pureFns .verified eager env F) env d nm i x y else pure false
          | .unknown => if xs.isEmpty && ys.isEmpty then
              ldprTail (ConLeche.pureFns .verified eager env F) env d nm i x y else pure false) := by
      intro F h
      rw [ConLeche.lazyDeltaProjReduction]
      simp only [bind, Except.bind, h]
      cases w <;> rfl
    have hP := hS.imp fun F h => hstep F h
    have hsn1 := denoteN_ext hsn hx1
    have hxs1 := denoteEList_ext hx1 _ _ hxs
    have hys1 := denoteEList_ext hx1 _ _ hys
    rcases st with ⟨a', b'⟩ | _ | _ | _ <;> rcases w with ⟨x', y'⟩ | _ | _ | _ <;>
      simp only [DSRel] at hr
    · -- `cont`: the next iteration
      obtain ⟨ha', hb', hwx', hwy'⟩ := hr
      refine triple_mono (lazyDeltaProjReduction_spec henv hsim d sn nm i as bs xs ys hwxs hwys n
        s1 a' b' x' y' hok1 hsn1 hxs1 hys1 ha' hb' hwx' hwy') ?_
      rintro r s2 ⟨hok2, hx2, hp2, F2, hF2⟩
      have hL : Ev (fun F => ConLeche.lazyDeltaProjReduction .verified
          (ConLeche.pureFns .verified eager env F) env d nm i xs ys n x' y' = .ok r) :=
        Ev.of_mono (fun hle h => lazyDeltaProjReductionFueled_mono hle h) ⟨F2, hF2⟩
      exact ⟨hok2, hx1.trans hx2, hp2.trans hp1,
        Ev.exists ((hP.and hL).imp fun _ ⟨h1, h2⟩ => h1.trans h2)⟩
    · -- `eq`: the argument lists, last to first
      have hrx : Frontend.denoteEList s1.store as.reverse = some xs.reverse := by
        rw [denoteEList_reverse_eq, hxs1]; rfl
      have hry : Frontend.denoteEList s1.store bs.reverse = some ys.reverse := by
        rw [denoteEList_reverse_eq, hys1]; rfl
      refine triple_mono (defEqList_spec hsim s1 d as.reverse bs.reverse xs.reverse ys.reverse
        hok1 hrx hry (fun z hz => hwxs z (List.mem_reverse.mp hz))
        (fun z hz => hwys z (List.mem_reverse.mp hz))) ?_
      rintro r s2 ⟨hok2, hx2, hp2, F2, hF2⟩
      have hL : Ev (fun F => ConLeche.defEqList (ConLeche.pureFns .verified eager env F) env d
          xs.reverse ys.reverse = .ok r) :=
        Ev.of_mono (fun hle h => defEqListFueled_mono hle h) ⟨F2, hF2⟩
      exact ⟨hok2, hx1.trans hx2, hp2.trans hp1,
        Ev.exists ((hP.and hL).imp fun _ ⟨h1, h2⟩ => h1.trans h2)⟩
    · -- `diff`
      exact ldprTailL_spec henv hsim d sn nm i as bs xs ys a b x y hok1 hx1 hp1 hsn1 hxs1 hys1
        (denote_ext hx hx1) (denote_ext hy hx1) hwx hwy _
        (hP.imp fun _ h r hr => h.trans hr)
    · -- `unknown`
      exact ldprTailL_spec henv hsim d sn nm i as bs xs ys a b x y hok1 hx1 hp1 hsn1 hxs1 hys1
        (denote_ext hx hx1) (denote_ext hy hx1) hwx hwy _
        (hP.imp fun _ h r hr => h.trans hr)

/-- con-leche: ConLeche/Kernel/Core.lean:1781-1793 defeqProjPair — a pair whose
spine heads are not two projections answers `false`. -/
theorem defeqProjPair_not {r : CoreFns CheckM} {d : Nat} {x y : Expr}
    (h : ¬ (exprTag x.getAppFn = ETag.proj ∧ exprTag y.getAppFn = ETag.proj)) :
    ConLeche.defeqProjPair mode r env d x y = pure false := by
  unfold ConLeche.defeqProjPair
  split
  · rename_i hx hy
    exfalso; exact h ⟨by rw [hx]; rfl, by rw [hy]; rfl⟩
  · rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1781-1793 defeqProjPair — **THEOREM 1
for the proj/proj check**: the spine heads' tag tests are con-leche's
constructor match on `getAppFn`, handle equality of the structure names is name
equality, the handle lists' lengths are the denoted spines', and the scrutinees
go through `lazyDeltaProjReduction_spec` at the shared budget. -/
theorem defeqProjPair_spec (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (d : Nat) (s₀ : AState) (a b : EIdx)
    (x y : Expr) (hok : CheckOK eager env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.defeqProjPair .verified (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => DqPost eager env fe s₀ (fun F r =>
        ConLeche.defeqProjPair .verified (ConLeche.pureFns .verified eager env F) env d x y = .ok r)
        r s'; ⊤⦄ := by
  have hwf := hok.state.wf
  have hfalse : ¬ (exprTag x.getAppFn = ETag.proj ∧ exprTag y.getAppFn = ETag.proj) →
      DqPost eager env fe s₀ (fun F r =>
        ConLeche.defeqProjPair .verified (ConLeche.pureFns .verified eager env F) env d x y = .ok r)
        false s₀ := fun hpp =>
    ⟨hok, Ext.refl _, rfl, 0, show ConLeche.defeqProjPair _ _ _ _ _ _ = _ by rw [defeqProjPair_not hpp]; rfl⟩
  unfold ConRon.Arena.defeqProjPair
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ a hok.state (by rw [hx]; rfl)) ?_
  rintro ha s1 ⟨hs1, hra⟩
  subst s1
  have hfa := hra x hx
  try dsimp only
  rw [tag_of_denote hwf hfa]
  split
  · rename_i hta
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ b hok.state (by rw [hy]; rfl)) ?_
    rintro hb s2 ⟨hs2, hrb⟩
    subst s2
    have hfb := hrb y hy
    try dsimp only
    rw [tag_of_denote hwf hfb]
    split
    · rename_i htb
      have hwga : Expr.WScoped d x.getAppFn := Expr.WScoped.getAppFn hwx
      have hwgb : Expr.WScoped d y.getAppFn := Expr.WScoped.getAppFn hwy
      have hpure : ∀ F, ConLeche.defeqProjPair .verified (ConLeche.pureFns .verified eager env F)
          env d x y =
          (match x.getAppFn, y.getAppFn with
            | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ =>
              if s₁ == s₂ && i₁ == i₂ && x.getAppArgs.length == y.getAppArgs.length then
                ConLeche.lazyDeltaProjReduction .verified (ConLeche.pureFns .verified eager env F)
                  env d s₁ i₁ x.getAppArgs y.getAppArgs ConLeche.defeqLoopFuel e₁ e₂
              else pure false
            | _, _ => pure false) := fun F => by
        unfold ConLeche.defeqProjPair; rfl
      have hwas := Expr.WScoped.getAppArgs hwx
      have hwbs := Expr.WScoped.getAppArgs hwy
      generalize hxa : x.getAppArgs = xs at hpure hwas
      generalize hya : y.getAppArgs = ys at hpure hwbs
      generalize x.getAppFn = gx at hfa hwga hta hpure
      generalize y.getAppFn = gy at hfb hwgb htb hpure
      obtain ⟨va, hva⟩ := denoteE_view hfa
      obtain ⟨vb, hvb⟩ := denoteE_view hfb
      refine view_bind_triple hva ?_
      refine view_bind_triple hvb ?_
      have hA := VD.of_view hwf hva hfa
      have hB := VD.of_view hwf hvb hfb
      rcases hA with _ | _ | _ | _ | _ | _ | _ | _ | _ |
        ⟨pn1, pi1, ps1, pnm1, pes1, hpn1, hps1⟩
      case proj =>
        rcases hB with _ | _ | _ | _ | _ | _ | _ | _ | _ |
          ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
        case proj =>
          try simp only []
          have hbeq : (pn1 == pn2 && pi1 == pi2) = (pnm1 == pnm2 && pi1 == pi2) := by
            rw [beq_handle_eq hwf hpn1 hpn2]
          have hw1 : Expr.WScoped d pes1 := by simpa [Expr.WScoped] using hwga
          have hw2 : Expr.WScoped d pes2 := by simpa [Expr.WScoped] using hwgb
          split
          · rename_i hc
            rw [hbeq] at hc
            simp only [beq_iff_eq, Bool.and_eq_true] at hc
            obtain ⟨rfl, rfl⟩ := hc
            refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ a hok.state
              (by rw [hx]; rfl)) ?_
            rintro las s3 ⟨hs3, hras⟩
            subst s3
            refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ b hok.state
              (by rw [hy]; rfl)) ?_
            rintro lbs s4 ⟨hs4, hrbs⟩
            subst s4
            have hxs : Frontend.denoteEList s₀.store las = some xs := hxa ▸ hras x hx
            have hys : Frontend.denoteEList s₀.store lbs = some ys := hya ▸ hrbs y hy
            have hlen : (las.length == lbs.length) = (xs.length == ys.length) := by
              rw [denoteEList_len hxs, denoteEList_len hys]
            try dsimp only
            rw [hlen]
            split
            · rename_i hl
              refine triple_mono (lazyDeltaProjReduction_spec henv hsim d pn1 pnm1 pi1 las lbs xs ys
                hwas hwbs ConRon.Arena.defeqLoopFuel s₀ ps1 ps2 pes1 pes2 hok hpn1 hxs hys hps1
                hps2 hw1 hw2) ?_
              rintro r s' ⟨hok', hx', hp', F, hF⟩
              refine ⟨hok', hx', hp', F, show ConLeche.defeqProjPair _ _ _ _ _ _ = _ from ?_⟩
              rw [hpure F]; dsimp only
              rw [ite_eq_left (by simp_all), ← defeqLoopFuel_eq]
              exact hF
            · rename_i hl
              exact triple_pure_post ⟨hok, Ext.refl _, rfl, 0, show ConLeche.defeqProjPair _ _ _ _ _ _ = _ by
                rw [hpure]; dsimp only; rw [ite_eq_right (by simp_all)]; rfl⟩
          · rename_i hc
            rw [hbeq] at hc
            exact triple_pure_post ⟨hok, Ext.refl _, rfl, 0, show ConLeche.defeqProjPair _ _ _ _ _ _ = _ by
              rw [hpure]; dsimp only; rw [ite_eq_right (by simp_all)]; rfl⟩
        all_goals
          exact absurd htb (by simp only [exprTag]; decide)
      all_goals
        exact absurd hta (by simp only [exprTag]; decide)
    · rename_i htb
      exact triple_pure_post (hfalse fun ⟨_, h⟩ => htb (by simp [h]))
  · rename_i hta
    exact triple_pure_post (hfalse fun ⟨h, _⟩ => hta (by simp [h]))

end ProjPair

/-! ## 3. The body -/

section Body

variable {fe : IFEnv} {fuel : Nat}

/-- con-leche: ConLeche/Kernel/Core.lean:1789-1840 defeqLazy
con-leche: ConLeche/Cached/CoreC.lean:1933-1955 defeqLazyI — **THEOREM 1 for
the lazy comparison at FIXED denotations of its two subjects**, stage by stage:
`quickDefEq` and proof irrelevance on the unreduced pair (con-leche task #333),
the cheap head normal forms, `quickDefEq` again, the lazy-delta loop, the
proj/proj check, and — only at a projection-headed side — the full `whnfCore`
and either the stuck comparison or a restart through the knot. -/
theorem defeqLazy_at (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (d : Nat) (s₀ : AState) (a b : EIdx)
    (x y : Expr) (hok : CheckOK eager env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄ defeqLazy .verified eager (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => DqPost eager env fe s₀ (fun F r =>
        ConLeche.defeqLazy .verified eager (ConLeche.pureFns .verified eager env F) env d x y
          = .ok r) r s'; ⊤⦄ := by
  unfold ConRon.Arena.defeqLazy
  -- the easy cases on the UNREDUCED pair (con-leche task #333)
  refine triple_seq (quickDefEq_spec hsim d s₀ a b x y hok hx hy hwx hwy) ?_
  rintro q0 t1 ⟨hokt1, hxt1, hpt1, hq0⟩
  have hx0t1 := hxt1
  have hp0t1 : t1.pins = s₀.pins := hpt1
  cases q0 with
  | some v =>
    exact triple_pure_post ⟨hokt1, hx0t1, hp0t1,
      Ev.exists (hq0.imp fun _ h2 => defeqLazy_quick0 h2)⟩
  | none =>
  dsimp only
  -- proof irrelevance on the UNREDUCED pair
  refine triple_seq (propIrrel_spec hsim t1 d a b x y hokt1 (denote_ext hx hx0t1)
    (denote_ext hy hx0t1) hwx hwy) ?_
  rintro pir0 t2 ⟨hokt2, hxt2, hpt2, hpiF0⟩
  have hpi0 : Ev (fun F => ConLeche.propIrrel (ConLeche.pureFns .verified eager env F) env d x y
      = .ok pir0) :=
    Ev.of_mono (p := fun F => ConLeche.propIrrel (ConLeche.pureFns .verified eager env F) env d
      x y = .ok pir0) (fun hle h => propIrrelFueled_mono hle h) hpiF0
  have hx0t2 := hx0t1.trans hxt2
  have hp0t2 : t2.pins = s₀.pins := hpt2.trans hp0t1
  cases pir0
  case true =>
    simp only [ite_true]
    exact triple_pure_post ⟨hokt2, hx0t2, hp0t2,
      Ev.exists ((hq0.and hpi0).imp fun _ ⟨h2, h3⟩ =>
        defeqLazy_propIrrel h2 h3)⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- the two cheap head normal forms
  refine triple_seq (hsim.whnfCore (c := true) t2 d a x hokt2 (denote_ext hx hx0t2)
    hwx) ?_
  rintro a' s4 ⟨hok4, hx4, hp4, x', hdx', hwx', F4, hF4⟩
  have hx04 := hx0t2.trans hx4
  refine triple_seq (hsim.whnfCore (c := true) s4 d b y hok4 (denote_ext hy hx04)
    hwy) ?_
  rintro b' s5 ⟨hok5, hx5, hp5, y', hdy', hwy', F5, hF5⟩
  have hx05 := hx04.trans hx5
  have hp05 : s5.pins = s₀.pins := hp5.trans (hp4.trans hp0t2)
  have hdx5 := denote_ext hdx' hx5
  have ha : Ev (fun F => ConLeche.whnfCore .verified eager env F d x true = .ok x') :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F4, hF4⟩
  have hb : Ev (fun F => ConLeche.whnfCore .verified eager env F d y true = .ok y') :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F5, hF5⟩
  have hpre : Ev (fun F => DbPre .verified eager env F d x y x' y') :=
    (((hq0.and hpi0).and ha).and hb).imp
      fun _ ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ => ⟨h2, h3, h4, h5⟩
  -- the easy cases on the reducts
  refine triple_seq (quickDefEq_spec hsim d s5 a' b' x' y' hok5 hdx5 hdy' hwx'
    hwy') ?_
  rintro q s6 ⟨hok6, hx6, hp6, hq⟩
  have hx06 := hx05.trans hx6
  have hp06 : s6.pins = s₀.pins := hp6.trans hp05
  cases q with
  | some v =>
    exact triple_pure_post ⟨hok6, hx06, hp06,
      Ev.exists ((hpre.and hq).imp fun _ ⟨h1, h2⟩ => defeqLazy_quick h1 h2)⟩
  | none =>
  dsimp only
  have hdx6 := denote_ext hdx5 hx6
  have hdy6 := denote_ext hdy' hx6
  -- the lazy-delta loop
  refine triple_seq (lazyDeltaReduction_spec henv hsim d ConRon.Arena.defeqLoopFuel s6
    a' b' x' y' hok6 hdx6 hdy6 hwx' hwy') ?_
  rintro lr s8 ⟨hok8, hx8, hp8, w, hrw, hL⟩
  rw [defeqLoopFuel_eq] at hL
  have hx08 := hx06.trans hx8
  have hp08 : s8.pins = s₀.pins := hp8.trans hp06
  have hmid : ∀ w', w = w' → Ev (fun F => DbPre .verified eager env F d x y x' y' ∧
      DbMid .verified eager env F d x' y' w') := fun w' hw' =>
    ((hpre.and hq).and hL).imp fun _ ⟨⟨h1, h2⟩, h4⟩ =>
      ⟨h1, ⟨h2, hw' ▸ h4⟩⟩
  rcases lr with v | ⟨a₁, b₁⟩ <;> rcases w with v' | ⟨x₁, y₁⟩ <;>
    simp only [LRRel] at hrw
  · subst hrw
    exact triple_pure_post ⟨hok8, hx08, hp08,
      Ev.exists ((hmid _ rfl).imp fun _ ⟨h1, h2⟩ => defeqLazy_verdict h1 h2)⟩
  obtain ⟨ha₁, hb₁, hwx₁, hwy₁⟩ := hrw
  have hU := hmid _ rfl
  dsimp only
  -- the proj/proj check
  refine triple_seq (defeqProjPair_spec henv hsim d s8 a₁ b₁ x₁ y₁ hok8 ha₁ hb₁
    hwx₁ hwy₁) ?_
  rintro pp s9 ⟨hok9, hx9, hp9, F9, hF9⟩
  have hPP : Ev (fun F => ConLeche.defeqProjPair .verified (ConLeche.pureFns .verified eager env F)
      env d x₁ y₁ = .ok pp) :=
    Ev.of_mono (fun hle h => defeqProjPairF_mono hle h) ⟨F9, hF9⟩
  have hx09 := hx08.trans hx9
  have hp09 : s9.pins = s₀.pins := hp9.trans hp08
  have hU' : Ev (fun F => ConLeche.defeqLazy .verified eager (ConLeche.pureFns .verified eager env F) env
      d x y =
      (if pp = true then pure true else
          if (!x₁.headIsProj && !y₁.headIsProj) = true then
            ConLeche.defeqStuck .verified (ConLeche.pureFns .verified eager env F) env d x₁ y₁ else
          (ConLeche.whnfCore .verified eager env F d x₁ false >>= fun a₂ =>
            ConLeche.whnfCore .verified eager env F d y₁ false >>= fun b₂ =>
            if (a₂ == x₁ && b₂ == y₁) = true then
              ConLeche.defeqStuck .verified (ConLeche.pureFns .verified eager env F) env d x₁ y₁
            else ConLeche.isDefEqCore .verified eager env F d a₂ b₂))) :=
    (hU.and hPP).imp fun _ ⟨⟨h1, h2⟩, h3⟩ => by
      rw [defeqLazy_unknown h1 h2, h3]; rfl
  cases pp
  case true =>
    simp only [ite_true]
    exact triple_pure_post ⟨hok9, hx09, hp09, Ev.exists (hU'.imp fun _ h => by
      dsimp only; rw [h]; rfl)⟩
  simp only [Bool.false_eq_true, ↓reduceIte] at hU' ⊢
  have hdx₁ := denote_ext ha₁ hx9
  have hdy₁ := denote_ext hb₁ hx9
  -- the two projection-head tests
  refine triple_seq (headIsProj_spec s9 a₁ x₁ hok9 hdx₁) ?_
  rintro pa s10 ⟨hs10, rfl⟩
  subst s10
  refine triple_seq (headIsProj_spec s9 b₁ y₁ hok9 hdy₁) ?_
  rintro pb s10 ⟨hs10, rfl⟩
  subst s10
  split
  · -- neither side is projection-headed: the stuck comparison
    rename_i hnp
    exact defeqStuck_spec henv hsim d s₀ s9 a₁ b₁ x₁ y₁ hok9 hx09 hp09 hdx₁ hdy₁
      hwx₁ hwy₁ _ (hU'.imp fun _ h r hr => by rw [h, ite_eq_left hnp]; exact hr)
  rename_i hnp
  -- the full `whnfCore` of both sides
  refine triple_seq (hsim.whnfCore (c := false) s9 d a₁ x₁ hok9 hdx₁ hwx₁) ?_
  rintro a₂ s10 ⟨hok10, hx10, hp10, x₂, hdx₂, hwx₂, F10, hF10⟩
  refine triple_seq (hsim.whnfCore (c := false) s10 d b₁ y₁ hok10
    (denote_ext hdy₁ hx10) hwy₁) ?_
  rintro b₂ s11 ⟨hok11, hx11, hp11, y₂, hdy₂, hwy₂, F11, hF11⟩
  have hW1 : Ev (fun F => ConLeche.whnfCore .verified eager env F d x₁ false = .ok x₂) :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F10, hF10⟩
  have hW2 : Ev (fun F => ConLeche.whnfCore .verified eager env F d y₁ false = .ok y₂) :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F11, hF11⟩
  have hx011 := (hx09.trans hx10).trans hx11
  have hp011 : s11.pins = s₀.pins := hp11.trans (hp10.trans hp09)
  have hwf11 := hok11.state.wf
  have hdx₂' := denote_ext hdx₂ hx11
  have hdx₁' := denote_ext hdx₁ (hx10.trans hx11)
  have hdy₁' := denote_ext hdy₁ (hx10.trans hx11)
  have heq : (a₂ == a₁ && b₂ == b₁) = (x₂ == x₁ && y₂ == y₁) := by
    rw [beq_of_denoteE hwf11 hdx₂' hdx₁', beq_of_denoteE hwf11 hdy₂ hdy₁']
  rw [heq]
  split
  · -- both unchanged: the stuck comparison
    rename_i hun
    exact defeqStuck_spec henv hsim d s₀ s11 a₁ b₁ x₁ y₁ hok11 hx011 hp011 hdx₁'
      hdy₁' hwx₁ hwy₁ _ (((hU'.and hW1).and hW2).imp fun _ ⟨⟨h, h1⟩, h2⟩ r hr => by
        rw [h, ite_eq_right hnp]
        simp only [h1, h2, bind, Except.bind, hun, ite_true]
        exact hr)
  · -- a restart through the knot
    rename_i hun
    exact dq_defeq_exit hsim a₂ b₂ x₂ y₂ hok11 hx011 hp011 hdx₂' hdy₂ hwx₂ hwy₂
      (((hU'.and hW1).and hW2).imp fun _ ⟨⟨h, h1⟩, h2⟩ r hr => by
        rw [h, ite_eq_right hnp]
        simp only [h1, h2, bind, Except.bind, hun, Bool.false_eq_true, ite_false]
        exact hr)

/-- con-leche: ConLeche/Kernel/Core.lean:1842-1884 defeqBody
con-leche: ConLeche/Cached/CoreC.lean:1957-1977 defeqBodyI — **THEOREM 1 for
the body at FIXED denotations of its two subjects**: the syntactic fast path;
the constructor shortcut — the target on the right first (`ctorTargetFor_spec`),
the other side's `whnf`, its head against the target (`ctorHeadAgainst_spec`),
then `false` or the lazy comparison of the normal form or of the original
pair; the same with the sides swapped; otherwise the lazy comparison
(`defeqLazy_at`). -/
theorem defeqBody_at (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (d : Nat) (s₀ : AState) (a b : EIdx)
    (x y : Expr) (hok : CheckOK eager env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄ defeqBody .verified eager (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => DqPost eager env fe s₀ (fun F r =>
        ConLeche.defeqBody .verified eager (ConLeche.pureFns .verified eager env F) env d x y = .ok r)
        r s'; ⊤⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.defeqBody
  split
  · -- the syntactic fast path
    rename_i hab
    rw [beq_of_denoteE hwf hx hy] at hab
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, 0, defeqBody_syntactic hab⟩
  rename_i hab
  rw [beq_of_denoteE hwf hx hy] at hab
  simp only [Bool.not_eq_true] at hab
  -- the lazy comparison at a later state, read back into `defeqBody`
  have hlazy : ∀ (s : AState) (p q : EIdx) (u w : Expr), CheckOK eager env fe s →
      Ext s₀.store s.store → s.pins = s₀.pins →
      denoteE s.store p = some u → denoteE s.store q = some w →
      Expr.WScoped d u → Expr.WScoped d w → ∀ (P : Nat → Prop),
      Ev P → (∀ F r, P F → ConLeche.defeqLazy .verified eager
          (ConLeche.pureFns .verified eager env F) env d u w = .ok r →
          ConLeche.defeqBody .verified eager (ConLeche.pureFns .verified eager env F) env d x y
            = .ok r) →
      ⦃fun s' => s' = s⦄ defeqLazy .verified eager (coreKnot .verified eager fe id fuel) fe d p q
      ⦃fun r s' => DqPost eager env fe s₀ (fun F r =>
          ConLeche.defeqBody .verified eager (ConLeche.pureFns .verified eager env F) env d x y
            = .ok r) r s'; ⊤⦄ := by
    intro s p q u w hoks hxs hps hp hq hwu hww P hP hPL
    refine triple_mono (defeqLazy_at henv hsim d s p q u w hoks hp hq hwu hww) ?_
    rintro r s' ⟨h1, h2, h3, F2, hF2⟩
    have hL : Ev (fun F => ConLeche.defeqLazy .verified eager
        (ConLeche.pureFns .verified eager env F) env d u w = .ok r) :=
      Ev.of_mono (fun hle h => defeqLazyFueled_mono hle h) ⟨F2, hF2⟩
    exact ⟨h1, hxs.trans h2, h3.trans hps,
      Ev.exists ((hP.and hL).imp fun F ⟨hp1, hp2⟩ => hPL F r hp1 hp2)⟩
  refine triple_seq (ctorTargetFor_spec s₀ eager a b x y hok hx hy) ?_
  rintro t1 s1 ⟨hok1, hst1, hp1, ht1⟩
  have hx1 : Ext s₀.store s1.store := by rw [hst1]; exact Ext.refl _
  have hx1' : denoteE s1.store a = some x := by rw [hst1]; exact hx
  have hy1' : denoteE s1.store b = some y := by rw [hst1]; exact hy
  cases t1 with
  | some c =>
    obtain ⟨cn, hcn, htgt⟩ : ∃ cn, denoteN s₀.store.ns c = some cn ∧
        ConLeche.ctorTargetFor env eager x y = some cn := by
      simp only [OptNRel, Option.map_some] at ht1
      cases h : ConLeche.ctorTargetFor env eager x y with
      | none => rw [h] at ht1; simp at ht1
      | some cn => rw [h] at ht1; simp at ht1; exact ⟨cn, ht1, rfl⟩
    dsimp only
    refine triple_seq (hsim.whnf s1 d a x hok1 hx1' hwx) ?_
    rintro w s2 ⟨hok2, hx2, hp2, v, hv, hwv, F1, hF1⟩
    have hW : Ev (fun F => ConLeche.whnf .verified eager env F d x = .ok v) :=
      Ev.of_mono (fun hle h => ConLeche.whnf_mono hle h) ⟨F1, hF1⟩
    have hx02 := hx1.trans hx2
    have hp02 : s2.pins = s₀.pins := hp2.trans hp1
    refine triple_seq (ctorHeadAgainst_spec s2 c cn w v hok2 (denoteN_ext hcn hx02) hv) ?_
    rintro o s3 ⟨hs3, ho⟩
    rw [hs3]
    rcases o with _ | _ | _
    · exact hlazy s2 a b x y hok2 hx02 hp02 (denote_ext hx hx02) (denote_ext hy hx02) hwx hwy
        _ hW (fun F r hF h => by rw [defeqBody_rightN hab htgt hF ho.symm]; exact h)
    · exact triple_pure_post ⟨hok2, hx02, hp02,
        Ev.exists (hW.imp fun F hF => defeqBody_rightF hab htgt hF ho.symm)⟩
    · exact hlazy s2 w b v y hok2 hx02 hp02 hv (denote_ext hy hx02) hwv hwy
        _ hW (fun F r hF h => by rw [defeqBody_rightT hab htgt hF ho.symm]; exact h)
  | none =>
    have htgt0 : ConLeche.ctorTargetFor env eager x y = none := by
      simp only [OptNRel, Option.map_none] at ht1
      cases h : ConLeche.ctorTargetFor env eager x y with
      | none => rfl
      | some _ => rw [h] at ht1; simp at ht1
    dsimp only
    refine triple_seq (ctorTargetFor_spec s1 eager b a y x hok1 hy1' hx1') ?_
    rintro t2 s4 ⟨hok4, hst4, hp4, ht2⟩
    have hx4 : Ext s₀.store s4.store := by rw [hst4, hst1]; exact Ext.refl _
    have hp04 : s4.pins = s₀.pins := hp4.trans hp1
    cases t2 with
    | some c =>
      obtain ⟨cn, hcn, htgt⟩ : ∃ cn, denoteN s1.store.ns c = some cn ∧
          ConLeche.ctorTargetFor env eager y x = some cn := by
        simp only [OptNRel, Option.map_some] at ht2
        cases h : ConLeche.ctorTargetFor env eager y x with
        | none => rw [h] at ht2; simp at ht2
        | some cn => rw [h] at ht2; simp at ht2; exact ⟨cn, ht2, rfl⟩
      dsimp only
      refine triple_seq (hsim.whnf s4 d b y hok4 (denote_ext hy hx4) hwy) ?_
      rintro w s2 ⟨hok2, hx2, hp2, v, hv, hwv, F1, hF1⟩
      have hW : Ev (fun F => ConLeche.whnf .verified eager env F d y = .ok v) :=
        Ev.of_mono (fun hle h => ConLeche.whnf_mono hle h) ⟨F1, hF1⟩
      have hx02 := hx4.trans hx2
      have hp02 : s2.pins = s₀.pins := hp2.trans hp04
      refine triple_seq (ctorHeadAgainst_spec s2 c cn w v hok2
        (denoteN_ext hcn ((by rw [hst4]; exact Ext.refl _ : Ext s1.store s4.store).trans hx2))
        hv) ?_
      rintro o s3 ⟨hs3, ho⟩
      rw [hs3]
      rcases o with _ | _ | _
      · exact hlazy s2 a b x y hok2 hx02 hp02 (denote_ext hx hx02) (denote_ext hy hx02) hwx hwy
          _ hW (fun F r hF h => by rw [defeqBody_leftN hab htgt0 htgt hF ho.symm]; exact h)
      · exact triple_pure_post ⟨hok2, hx02, hp02,
          Ev.exists (hW.imp fun F hF => defeqBody_leftF hab htgt0 htgt hF ho.symm)⟩
      · exact hlazy s2 a w x v hok2 hx02 hp02 (denote_ext hx hx02) hv hwx hwv
          _ hW (fun F r hF h => by rw [defeqBody_leftT hab htgt0 htgt hF ho.symm]; exact h)
    | none =>
      have htgt1 : ConLeche.ctorTargetFor env eager y x = none := by
        simp only [OptNRel, Option.map_none] at ht2
        cases h : ConLeche.ctorTargetFor env eager y x with
        | none => rfl
        | some _ => rw [h] at ht2; simp at ht2
      dsimp only
      exact hlazy s4 a b x y hok4 hx4 hp04 (denote_ext hx hx4) (denote_ext hy hx4) hwx hwy
        (fun _ => True) (Ev.const trivial)
        (fun F r _ h => by rw [defeqBody_lazy hab htgt0 htgt1]; exact h)

/-- con-leche: ConLeche/Verify/Cached/DiscC5.lean defeqBodyC_sim — **THEOREM 1
for `defeqBody`**: `defeqBody_at` at the two subjects' denotations, one fuel
up (`isDefEqCore_succ`). -/
theorem defeqBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) :
    BodySpecV eager env fe (defeqBody .verified eager (coreKnot .verified eager fe id fuel) fe)
      (ConLeche.isDefEqCore .verified eager env) := by
  intro s₀ d i j a b hok hda hdb hwa hwb
  refine triple_mono (defeqBody_at henv hsim d s₀ i j a b hok hda hdb hwa hwb) ?_
  rintro r s' ⟨hok', hx', hp', F, hF⟩
  exact ⟨hok', hx', hp', F + 1, by rw [ConLeche.isDefEqCore_succ]; exact hF⟩

end Body

/-! ## 4. The axiom census -/

section Census

#print axioms defeqBinders_spec
#print axioms quickDefEq_spec
#print axioms defeqOffset_spec
#print axioms tryUnfoldProjApp_spec
#print axioms lazyDeltaStep_spec
#print axioms lazyDeltaReduction_spec
#print axioms defeqStuck_spec
#print axioms lazyDeltaProjReduction_spec
#print axioms defeqProjPair_spec
#print axioms defeqLazy_at
#print axioms defeqBody_at
#print axioms defeqBody_spec

end Census

end ConRon.Bridge.Core
