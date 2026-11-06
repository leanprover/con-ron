/-
# `ConRon.Bridge.Core.Walks.Former` — the walk to a family's sort, at use

con-leche task #480 computes a family's sort where it is asked
(`ConLeche/Kernel/Core.lean:462-511`): `formerSortLoop` walks `n` binders of
the instantiated stored type down by the knot's `whnf`, `formerNeverZeroAt`
reads the answer (or the stored type's own sort, `formerNeverZero`), and the ι
case split asks it at the rule's comparand levels (`iotaCase3At`).  The
projection guard's sort (`projGuardSort`) is the same walk with another
reading.  This module is Theorem 1 for those four.

Each answer is a named predicate over the denotation term (`SortLoopAns`,
`NZAns`, `C3Ans`, `GuardSortAns`), with the pure side's exits as `grind`
lemmas over the head-normal form's projections (`fsl_zero`, `fsl_pi`, …),
the fuel merged by `Walks/Mono.lean`'s `…Fueled_mono`.
-/
module

public import ConRon.Bridge.Core.Walks.IotaLeaves
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Core.Walks.Nat
public import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.ExprOps.Owed
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

/-! ## 1. `formerSortLoop` -/

/-- con-leche: none — an `fvar` node's denotation at its annotation's (the arm
of `denoteEView` that would otherwise reach `grind` as an `Option.map`). -/
@[expose] def optFVar (k : Nat) : Option Expr → Option Expr
  | some t => some (.fvar k t)
  | none => none

/-- con-leche: none — `optFVar` at a present annotation. -/
@[bridge_grind =] theorem optFVar_some (k : Nat) (t : Expr) :
    optFVar k (some t) = some (.fvar k t) := rfl

/-- con-leche: none — `denoteEView` at an `fvar` view. -/
@[bridge_grind =] theorem denoteEView_fvar_eq (st : EStore) (k : Nat) (ty : EIdx) :
    denoteEView st (.fvar k ty) = optFVar k (denoteE st ty) := by
  simp only [denoteEView]; cases denoteE st ty <;> rfl

grind_pattern [bridge_grind] viewOK_fvar => st.ViewOK (.fvar k ty)

/-- con-leche: none — `instantiate1`'s answer at two optional subjects. -/
@[expose] def Inst1Rel : Option Expr → Option Expr → Option Expr → Prop
  | some w, some b, o => o = some (b.instantiate1 w)
  | _, _, _ => True

/-- con-leche: none — `Inst1Rel` at two denoting subjects. -/
@[bridge_grind =] theorem Inst1Rel.some_eq (w b : Expr) (o : Option Expr) :
    Inst1Rel (some w) (some b) o = (o = some (b.instantiate1 w)) := rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:176-178 instantiate1Fast — the
substitution's answer as `Inst1Rel` on the three denotation terms. -/
theorem instantiate1Fast_specR (s₀ : AState) (b w : EIdx) (hok : CheckOK eager env fe s₀)
    (hdb : (denoteE s₀.store b).isSome = true) (hdw : (denoteE s₀.store w).isSome = true) :
    ⦃fun s => s = s₀⦄ instantiate1Fast coreWalkFuel b w 0
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ Inst1Rel (denoteE s₀.store w) (denoteE s₀.store b) (denoteE s'.store r); ⊤⦄ := by
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp hdb
  obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp hdw
  rw [hB, hW]
  exact instantiate1Fast_ok_spec s₀ b w B W hok hB hW



/-- con-leche: ConLeche/Kernel/Core.lean:462-473 formerSortLoop — **the walk's
answer at a subject**: the level handle denotes what the pure walk answers at
some fuel. -/
@[expose] def SortLoop (eager : Bool) (env : Env) (d n : Nat) (x : Expr) (st : EStore)
    (r : Option LIdx) : Prop :=
  ∃ v, denoteLO st r = some v ∧
    ∃ F, formerSortLoop (pureFns .verified eager env F).whnf d n x = .ok v

/-- con-leche: none — `SortLoop` at an optional subject (the walk's answer
shape: the subject's denotation is a term). -/
@[expose] def SortLoopAns (eager : Bool) (env : Env) (d n : Nat) (st : EStore)
    (r : Option LIdx) : Option Expr → Prop
  | some x => SortLoop eager env d n x st r
  | none => True

/-- con-leche: none — `SortLoopAns` at a denoting subject. -/
@[bridge_grind =] theorem SortLoopAns.some_eq (d n : Nat) (st : EStore) (r : Option LIdx)
    (x : Expr) : SortLoopAns eager env d n st r (some x) = SortLoop eager env d n x st r := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:462-473 formerSortLoop — the last
binder: the head-normal form is a sort, or the walk answers `none`. -/
theorem fsl_zero {F d : Nat} {x w : Expr} {st : EStore} {r : Option LIdx}
    (hw : ConLeche.whnf .verified eager env F d x = .ok w)
    (hr : denoteLO st r =
      some (if exprTag w = ETag.sort then some (exprSort w) else none)) :
    SortLoop eager env d 0 x st r := by
  refine ⟨_, hr, F, ?_⟩
  have e1 : (pureFns .verified eager env F).whnf d x = .ok w := hw
  simp only [ConLeche.formerSortLoop, e1, bind, Except.bind]
  cases w <;> rfl
grind_pattern [bridge_grind] fsl_zero =>
  SortLoop eager env d 0 x st r, ConLeche.whnf .verified eager env F d x, exprTag w

/-- con-leche: ConLeche/Kernel/Core.lean:462-473 formerSortLoop — a binder to
open, but the head-normal form is not a `∀`. -/
theorem fsl_nopi {F d n : Nat} {x w : Expr} {st : EStore}
    (hw : ConLeche.whnf .verified eager env F d x = .ok w)
    (ht : exprTag w ≠ ETag.forallE) :
    SortLoop eager env d (n + 1) x st none := by
  refine ⟨none, rfl, F, ?_⟩
  have e1 : (pureFns .verified eager env F).whnf d x = .ok w := hw
  simp only [ConLeche.formerSortLoop, e1, bind, Except.bind]
  cases w <;> first | rfl | exact absurd rfl ht
grind_pattern [bridge_grind] fsl_nopi =>
  SortLoop eager env d (n + 1) x st none, ConLeche.whnf .verified eager env F d x, exprTag w

/-- con-leche: ConLeche/Kernel/Core.lean:462-473 formerSortLoop — a `∀`: the
walk continues one binder down at the opened body. -/
theorem fsl_pi {F d n : Nat} {x w : Expr} {st : EStore} {r : Option LIdx}
    (hw : ConLeche.whnf .verified eager env F d x = .ok w)
    (ht : exprTag w = ETag.forallE)
    (hr : SortLoop eager env (d + 1) n
      ((exprBody w).instantiate1 (.fvar d (exprBinderType w))) st r) :
    SortLoop eager env d (n + 1) x st r := by
  obtain ⟨v, hv, F₂, hF₂⟩ := hr
  refine ⟨v, hv, F + F₂, ?_⟩
  have e1 : (pureFns .verified eager env (F + F₂)).whnf d x = .ok w :=
    ConLeche.whnf_mono (by omega) hw
  rw [exprTag_forallE ht] at e1
  simp only [ConLeche.formerSortLoop, e1, bind, Except.bind]
  exact formerSortLoopFueled_mono (by omega) hF₂
grind_pattern [bridge_grind] fsl_pi =>
  SortLoop eager env d (n + 1) x st r, ConLeche.whnf .verified eager env F d x,
  SortLoop eager env (d + 1) n ((exprBody w).instantiate1 (.fvar d (exprBinderType w))) st r

/-- con-leche: none — `SortLoop` survives a store extension. -/
theorem SortLoop.ext {d n : Nat} {x : Expr} {st st' : EStore} {r : Option LIdx}
    (h : SortLoop eager env d n x st r) (hx : Ext st st') : SortLoop eager env d n x st' r := by
  obtain ⟨v, hv, F, hF⟩ := h
  refine ⟨v, ?_, F, hF⟩
  cases r with
  | none => exact hv
  | some j =>
    simp only [denoteLO, Option.map_eq_some_iff] at hv ⊢
    obtain ⟨l, hl, rfl⟩ := hv
    exact ⟨l, denoteL_ext hl hx, rfl⟩

/-- con-leche: ConLeche/Verify/Shift.lean:220 WScoped.instantiate1 — a `∀`'s
body, opened at the next free variable, is scoped one deeper. -/
theorem wscoped_open_body {d : Nat} {w : Expr} (h : Expr.WScoped d w)
    (ht : exprTag w = ETag.forallE) :
    Expr.WScoped (d + 1) ((exprBody w).instantiate1 (.fvar d (exprBinderType w))) := by
  rw [exprTag_forallE ht] at h
  simp only [Expr.WScoped] at h
  exact Expr.WScoped.instantiate1 h.1 0 h.2
grind_pattern [bridge_grind] wscoped_open_body => Expr.WScoped d w, exprTag w

/-- con-leche: ConLeche/Kernel/Core.lean:462-473 formerSortLoop
con-leche: ConLeche/Cached/CoreC.lean:424-437 formerSortLoopI — **THEOREM 1 for
`formerSortLoop`**: `n` binders down by the knot's `whnf`, then a sort. -/
theorem formerSortLoop_spec {fuel : Nat} (hsim : KnotSpec eager env fe fuel) :
    ∀ (n d : Nat) (s₀ : AState) (e : EIdx), CheckOK eager env fe s₀ →
      DenWS d (denoteE s₀.store e) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.formerSortLoop (coreKnot .verified eager fe id fuel) d n e
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
          SortLoopAns eager env d n s'.store r (denoteE s₀.store e); ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro d s₀ e hok hw
    cases hd : denoteE s₀.store e with
    | none => rw [hd] at hw; exact hw.elim
    | some x =>
    rw [hd] at hw
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.formerSortLoop, KnotSpec.whnfS hsim] <;> finish
  | succ n ih =>
    intro d s₀ e hok hw
    cases hd : denoteE s₀.store e with
    | none => rw [hd] at hw; exact hw.elim
    | some x =>
    rw [hd] at hw
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.formerSortLoop, KnotSpec.whnfS hsim,
        internE_specC (eager := eager) (env := env) (fe := fe),
        instantiate1Fast_specR (eager := eager) (env := env) (fe := fe), ih] <;>
        -- `gen := 16`: the opened body is four derived steps from the head-normal form (its
        -- view, the fvar's denotation, the substitution, the recursive call's subject)
        finish (gen := 16)

end ConRon.Bridge.Core
