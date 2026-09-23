/-
# `ConRon.Bridge.ExprOps.TagFirst` — the tag-first twins' projections, as views

Task #97-T2-LOCKSTEP (lane ExprOps) made the `ExprOps` twins that the port
reads tag-first (`is_lam`, `lam_pw`, `forall_pw`, `strip_lams`, `strip_pis`,
`pi_arity`, `fvar_type_d`, the telescope instantiations, `pis_to_lams`,
`replace_pi_body`, `rec_rule_plain`, and `Frontend.lamBody`) test the handle's
TAG and then read the typed projection the port reads (`viewBind`,
`viewFVarTy`), where they used to `match ← view h`.  A Theorem-1 proof of one
of them meets `(h.tag == ETag.C) = true` and an equation on `st.viewC h`
where it used to meet `st.view h = some …`; these lemmas give the `view`
fact back, and they are `@[grind →]` (as `Bridge/Rel.lean`'s group of the same
shape is) so that the arm closers derive it themselves.
-/
import ConRon.Bridge.Specs

open ConRon.Arena ConLeche

namespace ConRon.Bridge

/-- con-leche: none — the `fvar` type projection read means the index
projection reads too (one row of the `fvar` array). -/
theorem viewFVarIdx_of_viewFVarTy {st : EStore} {i ty : EIdx}
    (h : st.viewFVarTy i = some ty) : ∃ k, st.viewFVarIdx i = some k := by
  unfold EStore.viewFVarTy at h
  unfold EStore.viewFVarIdx EStore.persGetFVarIdx
  unfold EStore.persGetFVarTy at h
  split at h
  · simp only [ETables.getFVarTy, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, -⟩ := h
    exact ⟨r.idx, by simp [*, ETables.getFVarIdx]⟩
  · split at h
    · simp only [ETables.getFVarTy, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, -⟩ := h
      exact ⟨r.idx, by simp [*, ETables.getFVarIdx]⟩
    · cases h

/-- con-leche: none — `fvarTypeD`'s projection at an `fvar`-tagged handle is
its view. -/
@[grind →] theorem view_of_viewFVarTy_tag {st : EStore} {i ty : EIdx}
    (htg : (i.tag == ETag.fvar) = true) (hty : st.viewFVarTy i = some ty) :
    ∃ k, st.view i = some (.fvar k ty) := by
  obtain ⟨k, hk⟩ := viewFVarIdx_of_viewFVarTy hty
  exact ⟨k, view_of_viewFVar_tag htg hk hty⟩

/-- con-leche: none — `viewBind` at a λ-tagged handle is its view. -/
@[grind →] theorem view_of_viewBind_tag_lam {st : EStore} {i ty b : EIdx}
    {m : ConLeche.BinderMeta} (htg : (i.tag == ETag.lam) = true)
    (h : st.viewBind i = some (ty, b, m)) : st.view i = some (.lam ty b m) := by
  unfold EStore.viewBind at h
  cases h1 : st.viewBindI i with
  | none => rw [h1] at h; cases h
  | some p =>
    obtain ⟨ty', b', mi⟩ := p
    rw [h1] at h
    dsimp only at h
    cases h2 : st.viewBM mi with
    | none => rw [h2] at h; cases h
    | some m' =>
      rw [h2] at h
      cases h
      exact view_of_viewBindI_lam (by simpa using htg) h1 h2

/-- con-leche: none — and at a `∀`-tagged handle. -/
@[grind →] theorem view_of_viewBind_tag_forallE {st : EStore} {i ty b : EIdx}
    {m : ConLeche.BinderMeta} (htg : (i.tag == ETag.forallE) = true)
    (h : st.viewBind i = some (ty, b, m)) : st.view i = some (.forallE ty b m) := by
  unfold EStore.viewBind at h
  cases h1 : st.viewBindI i with
  | none => rw [h1] at h; cases h
  | some p =>
    obtain ⟨ty', b', mi⟩ := p
    rw [h1] at h
    dsimp only at h
    cases h2 : st.viewBM mi with
    | none => rw [h2] at h; cases h
    | some m' =>
      rw [h2] at h
      cases h
      exact view_of_viewBindI_forallE (by simpa using htg) h1 h2

/-- con-leche: none — **the `else` arm of a tag-first twin**: a handle that
denotes and whose tag is not `t` views to a node whose tag is not `t`. -/
theorem view_ne_of_tag {st : EStore} {h : EIdx} (hd : (denoteE st h).isSome = true)
    {t : UInt32} (ht : ¬ (h.tag == t) = true) : ∃ v, st.view h = some v ∧ v.tagOf ≠ t := by
  obtain ⟨v, hv⟩ := view_of_denote_isSome hd
  exact ⟨v, hv, view_tagOf_ne hv ht⟩

end ConRon.Bridge
