/-
# `ConRon.Refine2.Core.LS.PrimsC1` — region C1's primitive pairs

Task #97-P5-Core round 5, region C1 (the certificates: `iotaCerts`,
`defEqList`, `iotaIndexOk`, `proofIrrel`, `propIrrel`, the structure-eta and
unit certificates, `etaCert`, `stuckIrrel`).  The `@[lockstep]` pairs those
bodies step through that no earlier file supplies: Rust-only mode gates, the
state-free vector helpers, and the store reads.
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PC1

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## Bridges between the two `Vec<EIdx>` readings -/

@[lockstep_simp] theorem exprOps_absEIdxList_eq (v : alloc.vec.Vec arena.handle.EIdx) :
    ExprOps.absEIdxList v = absEIdxList v := rfl

@[lockstep_simp] theorem absEIdxListFrom_zero (v : alloc.vec.Vec arena.handle.EIdx) :
    absEIdxListFrom v 0#usize = absEIdxList v := by
  simp [absEIdxListFrom, absEIdxList]

/-! ## `drop_eidx_from` / `drop_eidx_n_from` / `drop_eidx_n` (the twin's `List.drop`) -/

theorem drop_eidx_from_aux (n : Nat) :
    ∀ (xs : alloc.vec.Vec arena.handle.EIdx) (k : Std.Usize)
      (out r : alloc.vec.Vec arena.handle.EIdx),
      xs.val.length - k.val = n → arena.core.drop_eidx_from xs k out = ok r →
      r.val = out.val ++ xs.val.drop k.val := by
  induction n with
  | zero =>
    intro xs k out r hn h
    rw [arena.core.drop_eidx_from] at h
    rw [if_pos (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]; simp
  | succ m ih =>
    intro xs k out r hn h
    rw [arena.core.drop_eidx_from] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt he
    have hd := dupId_eidx _ _ he1
    have hp := ConRon.Refine.vec_push_val ho1
    have hk := ConRon.Refine.Nat.uadd_val hk1
    rw [ih xs k1 o1 r (by simp at hk; omega) h, hp, hd, ← hx, hk]
    rw [List.drop_eq_getElem_cons hb, List.append_assoc]; rfl

@[lockstep] theorem drop_eidx_from_ls (xs : alloc.vec.Vec arena.handle.EIdx) (k : Std.Usize)
    (out : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.core.drop_eidx_from xs k out)
      (fun r => r.val = out.val ++ xs.val.drop k.val) :=
  fun r h => drop_eidx_from_aux _ xs k out r rfl h

theorem drop_eidx_n_from_aux (m : Nat) :
    ∀ (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) (i : Std.Usize)
      (r : alloc.vec.Vec arena.handle.EIdx),
      n.val = m → arena.core.drop_eidx_n_from xs n i = ok r →
      r.val = xs.val.drop (i.val + n.val) := by
  induction m with
  | zero =>
    intro xs n i r hn h
    rw [arena.core.drop_eidx_n_from] at h
    rw [if_pos (by scalar_tac)] at h
    rw [drop_eidx_from_aux _ xs i _ r rfl h, hn]; simp
  | succ m ih =>
    intro xs n i r hn h
    rw [arena.core.drop_eidx_n_from] at h
    rw [if_neg (by scalar_tac)] at h
    dsimp only at h
    split at h
    · cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h1 := ConRon.Refine.Nat.usub_val hn1
      have h2 := ConRon.Refine.Nat.uadd_val hi1
      rw [ih xs n1 i1 r (by simp at h1; omega) h]
      congr 1; simp at h1 h2; omega

@[lockstep] theorem drop_eidx_n_ls (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) :
    LSP (arena.core.drop_eidx_n xs n)
      (fun r => absEIdxList r = (absEIdxList xs).drop (absU n)) := by
  intro r h
  rw [arena.core.drop_eidx_n] at h
  have := drop_eidx_n_from_aux _ xs n 0#usize r rfl h
  simp only [absEIdxList, this, List.map_drop, absU]
  simp

/-! ## Rust-only mode and `PropWhen` gates -/

@[lockstep] theorem is_never_ls (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.prop_when.is_never pw)
      (fun b => b = ConLeche.PropWhen.isNever (ConRon.Refine.absPropWhen pw)) :=
  fun _ h => ConRon.Refine.PropWhen.is_never_refines h

@[lockstep] theorem certs_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.certs m) (fun b => b = (ConRon.Refine.absMode m).certs) := by
  intro b h
  cases m <;> (simp only [kernel.env.certs, Result.ok.injEq] at h; rw [← h]; rfl)

@[lockstep] theorem tt_checks_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.tt_checks m) (fun b => b = (ConRon.Refine.absMode m).ttChecks) :=
  by
  intro b h
  cases m <;> (simp only [kernel.env.tt_checks, Result.ok.injEq] at h; rw [← h]; rfl)

@[lockstep] theorem verified_checks_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.verified_checks m)
      (fun b => b = (ConRon.Refine.absMode m).verifiedChecks) :=
  by
  intro b h
  cases m <;> (simp only [kernel.env.verified_checks, Result.ok.injEq] at h; rw [← h]; rfl)

attribute [lockstep_simp] ConRon.Refine.absBinderMeta

/-! ## `PropWhen` comparison and the binder datum's well-formedness -/

/-- `prop_when::beq` against the twin's `==` on the abstraction: exact on
well-formed data (`Refine/PropWhen.lean`'s `beq_refines`). -/
@[lockstep] theorem prop_when_beq_ls (a b : kernel.prop_when.PropWhen)
    (ha : ConRon.Refine.PropWhenWF a) (hb : ConRon.Refine.PropWhenWF b) :
    LSP (kernel.prop_when.beq a b)
      (fun c => c = (ConRon.Refine.absPropWhen a == ConRon.Refine.absPropWhen b)) :=
  fun _ h => ConRon.Refine.PropWhen.beq_refines ha hb h

/-- `view_bind` with the datum's well-formedness (`AStateInv`'s `bms` clause)
carried in the answer relation.  Not `@[lockstep]`: a body that needs the
fact takes it as a local hypothesis, which `lockstep` tries first. -/
theorem view_bind_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx)
    (hbind : ETag.isBind (absEIdx h).tag = true) :
    LSV pers (fun a b => (∀ t, a = some t → ConRon.Refine.PropWhenWF t.2.2.pw) ∧
        b = Option.map absBindM a)
      (arena.monad.view_bind pers st h) st lst (Arena.viewBind (absEIdx h)) := by
  intro o hrun
  obtain ⟨b, lst', hx, hR, h1, h2⟩ := view_bind_ls hrel hinv h hbind o hrun
  refine ⟨b, lst', hx, ⟨fun t ht => ?_, hR⟩, h1, h2⟩
  subst ht
  obtain ⟨ty, bo, m⟩ := t
  exact view_bind_meta_wf hinv hrun

/-- `view_bind_wf_ls` as a proposition, for a body to take into its context
(`have hvb := viewBindWF_holds pers; unfold ViewBindWF at hvb`). -/
def ViewBindWF (pers : arena.store.PersTier) : Prop :=
  ∀ {st : arena.monad.AState} {lst : AState}, AStateRel₀ pers st lst → AStateInv pers st →
    ∀ (h : arena.handle.EIdx), ETag.isBind (absEIdx h).tag = true →
    LSV pers (fun a b => (∀ t, a = some t → ConRon.Refine.PropWhenWF t.2.2.pw) ∧
        b = Option.map absBindM a)
      (arena.monad.view_bind pers st h) st lst (Arena.viewBind (absEIdx h))

theorem viewBindWF_holds (pers : arena.store.PersTier) : ViewBindWF pers :=
  fun hrel hinv h hb => view_bind_wf_ls hrel hinv h hb

/-! ## Interns -/

@[lockstep] theorem intern_e_fvar_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (i : Std.U64) (ty : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_fvar pers st i ty) lst
      (Arena.internFVarE (absU i) (absEIdx ty)) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

/-! ## Twin-side shapes -/

/-- The twin's `if ← x then pure true else pure false` is `x`: the port tail-calls. -/
@[lockstep_simp] theorem bind_if_pure_true_false (x : AM Bool) :
    (x >>= fun b => if b = true then pure true else pure false) = x := by
  conv => rhs; rw [← bind_pure x]
  congr 1; funext b; cases b <;> rfl

end ConRon.Refine2.Lockstep.PC1
