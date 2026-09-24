/-
# `ConRon.Refine2.Core.LS.PrimsG2` — the binder data's well-formedness for the annotation pass

Task #97-P5-Core round 5, region G2.  The annotation bodies intern binders
(`intern_e_lam` / `intern_e_forall_e`) whose datum must be `PropWhenWF` (the
`bms` key's canonical form) for the proved intern pairs
`intern_e_{lam,forall_e}_wf_ls`.  Every such datum is a representation fact
about a Rust value:

* read out of the Rust store by `view` / `view_bind` (`bms`' `TblInv`, part of
  `AStateInv`) — `view_wf_ls` / `view_bind_wf_ls`, restated here from region
  E's `PrimsE` (importing `PrimsE` into the annotation file would bring in its
  global `lockstep_simp` set, which changes how the `Proj` arm's handle
  comparison normalises);
* computed by `zeroness_of` (`zeroness_of_refines`), or `subst_pw` of a
  well-formed datum (`subst_pw_refines`);
* answered by the `prop_read` walks `type_sort_pw` / `proof_pw`, whose answers
  are only ever one of the above.  `ExprOpsHyp`'s `typeSortPW` / `proofPW`
  fields say nothing of the answer's well-formedness, so the two facts are
  proved here directly on the Rust (`type_sort_pw_optWF` / `proof_pw_optWF`)
  and paired with the `ExprOpsHyp` lockstep lemmas (`*_wf_ls`).

The `*_wf_ls` lemmas are NOT registered: the proofs that need the WF take
them as local hypotheses, which `lockstep` tries before the registered pairs.
-/
import ConRon.Refine2.Core.LS.Prims
import ConRon.Refine2.Core.LS.PrimsA1
import ConRon.Refine2.Core.LS.PrimsB

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg ConRon.Refine2.Lockstep.PB.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

-- `PrimsB`/`PrimsE` unfold the record abstraction only locally now (the
-- Checker lane reads it folded); the Core region files read it unfolded
attribute [local lockstep_simp] ConRon.Refine2.absIConstantVal

namespace ConRon.Refine2.Lockstep.PG2

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## The well-formedness predicates -/

/-- The binder datum of a `view_bind` answer is well formed. -/
def optBindWF : Option (arena.handle.EIdx × arena.handle.EIdx × kernel.expr.BinderMeta) → Prop
  | some (_, _, m) => ConRon.Refine.PropWhenWF m.pw
  | none => True

/-- The binder datum of a `view` answer is well formed. -/
def viewWF : arena.store.ENodeView → Prop
  | .Lam _ _ m => ConRon.Refine.PropWhenWF m.pw
  | .ForallE _ _ m => ConRon.Refine.PropWhenWF m.pw
  | _ => True

/-- A `prop_read` answer is well formed. -/
def optPwWF : Option kernel.prop_when.PropWhen → Prop
  | some p => ConRon.Refine.PropWhenWF p
  | none => True

attribute [local lockstep_simp] optBindWF viewWF optPwWF

/-! ## Store reads carrying the datum's well-formedness (after `PrimsE`) -/

theorem estore_view_bind_optWF {pers rs} (hinv : StoreInv pers rs) {i : arena.handle.EIdx} {o}
    (h : arena.store.EStore.view_bind rs pers i = ok o) : optBindWF o := by
  rw [arena.store.EStore.view_bind] at h
  obtain ⟨q, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases q with
  | none => cases Result.ok_injective h; trivial
  | some tt =>
    obtain ⟨ty, bo, mi⟩ := tt
    obtain ⟨u, hu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases u with
    | none => cases Result.ok_injective h; trivial
    | some mm =>
      cases Result.ok_injective h
      exact estore_view_bm_wf hinv hu mm rfl

theorem view_bind_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx)
    (hbind : ETag.isBind (absEIdx h).tag = true) :
    LSV pers (fun a b => optBindWF a ∧ b = Option.map absBindM a)
      (arena.monad.view_bind pers st h) st lst (Arena.viewBind (absEIdx h)) := by
  intro o hrun
  obtain ⟨b, lst', hx, hR, h1, h2⟩ := view_bind_ls hrel hinv h hbind o hrun
  rw [arena.monad.view_bind] at hrun
  exact ⟨b, lst', hx, ⟨estore_view_bind_optWF hinv.store hrun, hR.2⟩, h1, h2⟩

theorem view_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSR pers (fun a b => viewWF a ∧ b = absENodeView a) (arena.monad.view pers st h) st lst
      (Arena.view (absEIdx h)) := by
  intro o hrun
  have H := view_ls hrel hinv h o hrun
  cases o with
  | Err e => exact H
  | Ok ev =>
    obtain ⟨b, lst', hx, hR, h1, h2⟩ := H
    refine ⟨b, lst', hx, ⟨?_, hR.2⟩, h1, h2⟩
    have hwf : ∀ {ty b : arena.handle.EIdx} {m : kernel.expr.BinderMeta},
        ev = .Lam ty b m ∨ ev = .ForallE ty b m → ConRon.Refine.PropWhenWF m.pw := by
      intro ty b m hv
      rw [arena.monad.view] at hrun
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases hqc : q with
      | none =>
        rw [hqc] at hrun
        obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [arena.monad.fail] at hrun
        cases Result.ok_injective hrun
      | some v =>
        rw [hqc] at hrun hq
        have := Result.ok_injective hrun
        simp only [core.result.Result.Ok.injEq] at this
        subst this
        exact estore_view_bind_wf (ty := ty) (b := b) hrel.store hinv.store hq
          (by rcases hv with hv | hv
              · exact Or.inl (by rw [hv])
              · exact Or.inr (by rw [hv]))
    cases ev with
    | Lam ty b m => exact hwf (Or.inl rfl)
    | ForallE ty b m => exact hwf (Or.inr rfl)
    | _ => trivial

/-! ## The `prop_read` answers are well formed -/

theorem view_ok_wf {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {h : arena.handle.EIdx} {ev} (hrun : arena.monad.view pers st h = ok (.Ok ev)) :
    viewWF ev := by
  obtain ⟨_, _, -, ⟨hw, -⟩, -, -⟩ := view_wf_ls hrel hinv h _ hrun
  exact hw

theorem fail_dangling_e_not_ok {T : Type} {o} (h : arena.monad.fail_dangling_e T = ok o) :
    ∀ p, o ≠ .Ok p := by
  rw [arena.monad.fail_dangling_e] at h
  obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [arena.monad.fail] at h
  cases Result.ok_injective h
  intro p hp; cases hp

theorem fail_dangling_ls_not_ok {T : Type} {o} (h : arena.monad.fail_dangling_ls T = ok o) :
    ∀ p, o ≠ .Ok p := by
  rw [arena.monad.fail_dangling_ls] at h
  obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [arena.monad.fail] at h
  cases Result.ok_injective h
  intro p hp; cases hp

/-- `read_level`'s answer is well formed (`denote_l_wf`). -/
theorem read_level_wf {pers st} (hinv : AStateInv pers st) {h : arena.handle.LIdx} {l}
    (hrun : arena.monad.read_level pers st h = ok (.Ok l)) : ConRon.Refine.LevelWF l := by
  rw [arena.monad.read_level] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ls] at hn
  have hn2 : n = st.store.lss.ls := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hdw := denote_l_wf hinv.store.lss.lvl hv
  cases v with
  | none =>
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    simp at hrun
  | some x =>
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hrun
    subst hrun
    exact hdw x rfl

theorem never_wf {pw} (h : kernel.prop_when.never = ok pw) : ConRon.Refine.PropWhenWF pw :=
  ConRon.Refine.PropWhenWF.never h

theorem residual_pw_wf {pers st} (hinv : AStateInv pers st) {res o}
    (h : arena.prop_read.residual_pw pers st res = ok o) :
    ∀ p, o = .Ok (some p) → ConRon.Refine.PropWhenWF p := by
  intro p hp
  subst hp
  unfold arena.prop_read.residual_pw at h
  cases res with
  | none => simp at h
  | some r =>
    obtain ⟨i, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    split at h
    · obtain ⟨o1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases o1 with
      | none => exact absurd rfl (fail_dangling_e_not_ok h _)
      | some u =>
        obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        cases r1 with
        | Err e => simp at h
        | Ok l =>
          obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Option.some.injEq] at h
          subst h
          exact (ConRon.Refine.ExprOps.zeroness_of_refines (read_level_wf hinv hr1) _ hpw).2
    · simp at h

/-- The constant-head arm's parameter substitution: a well-formed datum stays
well formed. -/
theorem subst_tail_wf {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {lps : alloc.vec.Vec arena.handle.NIdx} {us : arena.handle.LsIdx}
    {pw : kernel.prop_when.PropWhen} (hpw : ConRon.Refine.PropWhenWF pw) {p st'}
    (h : (do
      let (r3, st2) ← arena.monad.read_names_m pers st lps
      match r3 with
      | core.result.Result.Ok ks =>
        let (r4, st3) ← arena.monad.read_levels_m pers st2 us
        match r4 with
        | core.result.Result.Ok vs =>
          let pw1 ← kernel.level.subst_pw ks vs pw
          ok (core.result.Result.Ok (some pw1), st3)
        | core.result.Result.Err e1 => ok (core.result.Result.Err e1, st3)
      | core.result.Result.Err e1 => ok (core.result.Result.Err e1, st2) :
        Result ((core.result.Result (Option kernel.prop_when.PropWhen)
          kernel.core_types.CheckError) × arena.monad.AState)) =
      ok (.Ok (some p), st')) :
    ConRon.Refine.PropWhenWF p := by
  obtain ⟨⟨r3, st2⟩, hr3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r3 with
  | Err e => simp at h
  | Ok ks =>
    have hks := (PA1.read_names_m_wf₀ hrel hinv hr3).1 ks rfl
    obtain ⟨_, lst2, -, -, hrel2, hinv2⟩ := PA1.read_names_m_ls hrel hinv lps _ _ hr3
    obtain ⟨⟨r4, st3⟩, hr4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r4 with
    | Err e => simp at h
    | Ok vs =>
      have hvs := (read_levels_m_wf hinv2 hr4).1 vs rfl
      obtain ⟨pw1, hpw1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq,
        Option.some.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact (ConRon.Refine.ExprOps.subst_pw_refines hks hvs hpw hpw1).2

theorem head_type_pw_wf {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {vis fe h n o st'} (hrun : arena.prop_read.head_type_pw pers vis st fe h n = ok (o, st')) :
    ∀ p, o = .Ok (some p) → ConRon.Refine.PropWhenWF p := by
  intro p hp
  subst hp
  unfold arena.prop_read.head_type_pw at hrun
  obtain ⟨r, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  cases r with
  | Err e => simp at hrun
  | Ok ev =>
    cases ev with
    | FVar _ ty =>
      obtain ⟨r1, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases r1 with
      | Err e => simp at hrun
      | Ok res =>
        obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        simp only [Result.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact residual_pw_wf hinv hr2 p rfl
    | Const i us =>
      obtain ⟨oc, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases oc with
      | none => simp at hrun
      | some ci =>
        obtain ⟨b, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        split at hrun
        · simp at hrun
        obtain ⟨⟨r1, e⟩, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases r1 with
        | Err e1 => simp at hrun
        | Ok cv =>
          obtain ⟨_, lst1, -, -, hrel1, hinv1⟩ :=
            PB.i_constant_info_to_constant_val_ls hrel hinv ci _ _ hr1
          obtain ⟨o1, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          cases o1 with
          | none =>
            obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            simp only [Result.ok.injEq, Prod.mk.injEq] at hrun
            exact absurd hrun.1 (fail_dangling_ls_not_ok hr2 _)
          | some usl =>
            dsimp only at hrun
            split at hrun
            · obtain ⟨r2, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              cases r2 with
              | Err e1 => simp at hrun
              | Ok res =>
                obtain ⟨r3, hr3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                cases r3 with
                | Err e1 => simp at hrun
                | Ok o2 =>
                  cases o2 with
                  | none => simp at hrun
                  | some pw =>
                    have hpw := residual_pw_wf hinv1 hr3 pw rfl
                    obtain ⟨b1, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                    split at hrun
                    · exact subst_tail_wf hrel1 hinv1 hpw hrun
                    · simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq,
                        Option.some.injEq] at hrun
                      obtain ⟨rfl, -⟩ := hrun
                      exact hpw
            · simp at hrun
    | _ => simp at hrun

/-- A `type_sort_pw` answer is well formed. -/
theorem type_sort_pw_optWF {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {vis fe fuel t o st'}
    (hrun : arena.prop_read.type_sort_pw pers vis st fe fuel t = ok (o, st')) :
    ∀ p, o = .Ok (some p) → ConRon.Refine.PropWhenWF p := by
  intro p hp
  subst hp
  unfold arena.prop_read.type_sort_pw at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  cases r with
  | Err e => simp at hrun
  | Ok ev =>
    have hvw := view_ok_wf hrel hinv hr
    cases ev with
    | «Sort» _ =>
      obtain ⟨pw, hpw, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq,
        Option.some.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact never_wf hpw
    | ForallE _ _ m =>
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq,
        Option.some.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact hvw
    | _ =>
      obtain ⟨r1, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases r1 with
      | Err e => simp at hrun
      | Ok fnh =>
        obtain ⟨r2, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases r2 with
        | Err e => simp at hrun
        | Ok n => exact head_type_pw_wf hrel hinv hrun p rfl

theorem head_proof_pw_wf {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    {fuel h o st'}
    (hrun : arena.prop_read.head_proof_pw pers vis st fe fuel h = ok (o, st')) :
    ∀ p, o = .Ok (some p) → ConRon.Refine.PropWhenWF p := by
  intro p hp
  subst hp
  unfold arena.prop_read.head_proof_pw at hrun
  obtain ⟨r, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  cases r with
  | Err e => simp at hrun
  | Ok ev =>
    cases ev with
    | FVar _ ty => exact type_sort_pw_optWF hrel hinv hrun p rfl
    | Const c us =>
      obtain ⟨oc, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases oc with
      | none => simp at hrun
      | some ci =>
        obtain ⟨b, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        split at hrun
        · simp at hrun
        obtain ⟨⟨r1, e⟩, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases r1 with
        | Err e1 => simp at hrun
        | Ok cv =>
          obtain ⟨_, lst1, -, -, hrel1, hinv1⟩ :=
            PB.i_constant_info_to_constant_val_ls hrel hinv ci _ _ hr1
          obtain ⟨o1, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          cases o1 with
          | none =>
            obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            simp only [Result.ok.injEq, Prod.mk.injEq] at hrun
            exact absurd hrun.1 (fail_dangling_ls_not_ok hr2 _)
          | some usl =>
            dsimp only at hrun
            split at hrun
            · obtain ⟨⟨r2, st1⟩, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              cases r2 with
              | Err e1 => simp at hrun
              | Ok o2 =>
                cases o2 with
                | none => simp at hrun
                | some pw =>
                  have hpw := type_sort_pw_optWF hrel1 hinv1 hr2 pw rfl
                  obtain ⟨_, lst2, -, -, hrel2, hinv2⟩ :=
                    type_sort_pw_ls hx hrel1 hinv1 hctx _ _ _ _ hr2
                  obtain ⟨b1, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                  split at hrun
                  · exact subst_tail_wf hrel2 hinv2 hpw hrun
                  · simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq,
                      Option.some.injEq] at hrun
                    obtain ⟨rfl, -⟩ := hrun
                    exact hpw
            · simp at hrun
    | «Sort» _ | ForallE _ _ _ | Lit _ =>
      obtain ⟨pw, hpw, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq,
        Option.some.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact never_wf hpw
    | _ => simp at hrun

/-- A `proof_pw` answer is well formed. -/
theorem proof_pw_optWF {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    {fuel a o st'} (hrun : arena.prop_read.proof_pw pers vis st fe fuel a = ok (o, st')) :
    ∀ p, o = .Ok (some p) → ConRon.Refine.PropWhenWF p := by
  intro p hp
  subst hp
  unfold arena.prop_read.proof_pw at hrun
  obtain ⟨i, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  split at hrun
  · obtain ⟨ob, hob, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.view_bind] at hob
    have hw := estore_view_bind_optWF hinv.store hob
    cases ob with
    | none =>
      obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      simp only [Result.ok.injEq, Prod.mk.injEq] at hrun
      exact absurd hrun.1 (fail_dangling_e_not_ok hr _)
    | some t =>
      obtain ⟨ty, bo, m⟩ := t
      dsimp only at hrun
      have hh := Result.ok_injective hrun
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq, Option.some.injEq] at hh
      obtain ⟨rfl, -⟩ := hh
      exact hw
  · obtain ⟨r, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases r with
    | Err e => simp at hrun
    | Ok fnh => exact head_proof_pw_wf hx hrel hinv hctx hrun p rfl

/-! ## The lockstep pairs with the answer's well-formedness (local candidates) -/

theorem type_sort_pw_wf_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel t) :
    LS pers (fun a b => optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.type_sort_pw pers vis st fe fuel t)
      lst (typeSortPW lfe (absU fuel) (absEIdx t)) := by
  intro o st' hrun
  have H := type_sort_pw_ls hx hrel hinv hctx fuel t o st' hrun
  have W := type_sort_pw_optWF hrel hinv hrun
  cases o with
  | Err e => exact H
  | Ok a =>
    obtain ⟨b, lst', h1, hR, h2, h3⟩ := H
    refine ⟨b, lst', h1, ⟨?_, hR⟩, h2, h3⟩
    cases a with
    | none => trivial
    | some p => exact W p rfl

theorem proof_pw_wf_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel a) :
    LS pers (fun a b => optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.proof_pw pers vis st fe fuel a)
      lst (proofPW lfe (absU fuel) (absEIdx a)) := by
  intro o st' hrun
  have H := proof_pw_ls hx hrel hinv hctx fuel a o st' hrun
  have W := proof_pw_optWF hx hrel hinv hctx hrun
  cases o with
  | Err e => exact H
  | Ok a =>
    obtain ⟨b, lst', h1, hR, h2, h3⟩ := H
    refine ⟨b, lst', h1, ⟨?_, hR⟩, h2, h3⟩
    cases a with
    | none => trivial
    | some p => exact W p rfl

/-! ## The binder stack -/

/-- Pushing a well-formed binder keeps the stack well formed. -/
theorem stk_push_wf {stk stk1 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {x : arena.handle.EIdx × kernel.expr.BinderMeta} (h : stk1.val = stk.val ++ [x])
    (hs : ∀ p ∈ stk.val, ConRon.Refine.PropWhenWF p.2.pw) (hx : ConRon.Refine.PropWhenWF x.2.pw) :
    ∀ p ∈ stk1.val, ConRon.Refine.PropWhenWF p.2.pw := by
  intro p hp
  rw [h] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hs p hp
  · rw [List.mem_singleton.mp hp]; exact hx

@[local lockstep_simp] theorem stk_new_wf :
    (∀ p ∈ (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)).val,
      ConRon.Refine.PropWhenWF p.2.pw) = True := by
  simp [alloc.vec.Vec.new]

/-- An entry the Rust reads off a well-formed binder stack is well formed. -/
theorem stk_index_wf (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (i : Std.Usize) (hs : ∀ p ∈ v.val, ConRon.Refine.PropWhenWF p.2.pw) :
    LSP (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        (arena.handle.EIdx × kernel.expr.BinderMeta)) v i)
      (fun x => ConRon.Refine.PropWhenWF x.2.pw) := by
  intro x h
  obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt h
  apply hs
  rw [← hx]; exact List.getElem_mem hb

/-- The recursive call's datum premise at a written / an unwritten datum. -/
@[local lockstep_simp] theorem forall_some_eq_imp {α : Type} (a : α) (P : α → Prop) :
    (∀ p, some a = some p → P p) = P a := by simp

@[local lockstep_simp] theorem forall_none_eq_imp {α : Type} (P : α → Prop) :
    (∀ p, (none : Option α) = some p → P p) = True := by simp

end ConRon.Refine2.Lockstep.PG2

/-! The region's `lockstep_simp` rules, registered `scoped` (task #97-P5-Core
round 5): active under `open scoped ConRon.Refine2.Lockstep.PG2.CoreLSReg` only, so that they
stay out of the other tiers' `lockstep` runs (the Checker lane imports the
knot since task #97-T2-LOCKSTEP lane Checker DeclCheck). -/
namespace ConRon.Refine2.Lockstep.PG2.CoreLSReg
open Aeneas Aeneas.Std Result
open ConRon.Generated
open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep
attribute [scoped lockstep_simp] optBindWF viewWF optPwWF stk_new_wf forall_some_eq_imp forall_none_eq_imp
end ConRon.Refine2.Lockstep.PG2.CoreLSReg
