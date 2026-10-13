/-
# `ConRon.Bridge.StoreBind` — `internBind`'s store spec

`EStore.internBind` (and its two `@[inline]` faces `internLam` /
`internForallE`) is the `intern` the REBUILDING WALKS call — they take a
binder apart with `viewBind` and put it back with this.  Since task #119 (the
binder datum is gone from con-leche's `Expr`, so from the arena) it is
literally `intern` at the binder view its tag spells
(`Arena/WFProofs.lean`'s `EStore.internBind_eq_intern`), and its spec is
`EStore.intern_spec` read through that equation.
-/
import ConRon.Bridge.Rel

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The tag, and the two shapes `eBindView` puts it in

Everything below is the same two-case split — `ETag.isBind` names exactly the
two tags `eBindView` dispatches on — so it is taken once, here, and the shape
lemmas that follow are `rfl` at each case. -/

/-- con-leche: none — arena infrastructure; `ETag.isBind` is the disjunction
it is defined as, read as an equation on the tag. -/
theorem ETag.isBind_eq {tag : UInt32} (h : ETag.isBind tag = true) :
    tag = ETag.lam ∨ tag = ETag.forallE := by
  simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at h
  exact h

/-- con-leche: none — arena infrastructure; a binder view's expression
children are its two handles, whichever of the two tags it carries. -/
theorem ENodeView.echildren_eBindView {tag : UInt32} {ty b : EIdx}
    (htag : ETag.isBind tag = true) :
    (eBindView tag ty b).echildren = [ty, b] := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-- con-leche: none — arena infrastructure; a binder view names no name
handle. -/
theorem ENodeView.nchildren_eBindView {tag : UInt32} {ty b : EIdx}
    (htag : ETag.isBind tag = true) :
    (eBindView tag ty b).nchildren = [] := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-- con-leche: none — arena infrastructure; a binder view names no level
handle. -/
theorem ENodeView.lchildren_eBindView {tag : UInt32} {ty b : EIdx}
    (htag : ETag.isBind tag = true) :
    (eBindView tag ty b).lchildren = [] := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-- con-leche: none — arena infrastructure; a binder view names no
level-list handle. -/
theorem ENodeView.lschildren_eBindView {tag : UInt32} {ty b : EIdx}
    (htag : ETag.isBind tag = true) :
    (eBindView tag ty b).lschildren = [] := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-- con-leche: none — arena infrastructure; `bindSizeOf tag` IS `sizeOf` of
the view that tag builds, so `internBind`'s capacity test is `intern`'s. -/
theorem ETables.sizeOf_eBindView (t : ETables) {tag : UInt32} {ty b : EIdx}
    (htag : ETag.isBind tag = true) :
    t.sizeOf (eBindView tag ty b) = t.bindSizeOf tag := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-! ## `internBind` IS `intern` -/

/-- con-leche: none — arena infrastructure; `intern`'s scratch flag. -/
theorem EStore.scratchOn_intern (st : EStore) (w : ENodeView) :
    (st.intern w).1.scratchOn = st.scratchOn := by
  rcases EStore.intern_cases st w with he | he | he <;> rw [he]

/-- con-leche: none — arena infrastructure; a binder cons hit names a node
whose view is the binder view the tag spells.  `StoreWF`'s own
`consP`/`consS` clause read left to right — no capacity in it, which is the
point of probing first. -/
theorem EStore.view_of_findBind {st : EStore} {tag : UInt32} {ty b : EIdx}
    {i : EIdx} (h : StoreWF st) (htag : ETag.isBind tag = true)
    (hf : st.findBind tag ty b = some i) :
    st.view i = some (eBindView tag ty b) :=
  EStore.view_of_find h
    ((EStore.findBind_eq_find st tag ty b (ETag.isBind_eq htag)).symm.trans hf)

/-- con-leche: none — arena infrastructure; the binder `intern` preserves the
store, extends it, and its handle decodes to the binder view the tag
spells. -/
theorem EStore.internBind_spec {st : EStore} {tag : UInt32} {ty b : EIdx}
    (h : StoreWF st) (htag : ETag.isBind tag = true)
    (hty : (st.view ty).isSome = true) (hb : (st.view b).isSome = true)
    (hcap : (if st.scratchOn then st.scr.bindSizeOf tag
              else st.pers.bindSizeOf tag) < Idx.idxCap) :
    StoreWF (st.internBind tag ty b).1 ∧
      Ext st (st.internBind tag ty b).1 ∧
      (st.internBind tag ty b).1.lss = st.lss ∧
      (st.internBind tag ty b).1.scratchOn = st.scratchOn ∧
      (st.internBind tag ty b).1.view (st.internBind tag ty b).2 =
        some (eBindView tag ty b) ∧
      denoteE (st.internBind tag ty b).1 (st.internBind tag ty b).2 =
        denoteEView (st.internBind tag ty b).1 (eBindView tag ty b) := by
  rw [EStore.internBind_eq_intern st tag ty b (ETag.isBind_eq htag)]
  have hv : st.ViewOK (eBindView tag ty b) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ENodeView.echildren_eBindView htag]
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hty
      · exact hb
    · rw [ENodeView.nchildren_eBindView htag]; intro c hc; exact absurd hc (by simp)
    · rw [ENodeView.lchildren_eBindView htag]; intro c hc; exact absurd hc (by simp)
    · rw [ENodeView.lschildren_eBindView htag]; intro c hc; exact absurd hc (by simp)
  have hcap' : st.capOK (eBindView tag ty b) := by
    simp only [EStore.capOK]
    rw [ETables.sizeOf_eBindView _ htag, ETables.sizeOf_eBindView _ htag]
    exact hcap
  obtain ⟨h1, h2, h3, h4⟩ := EStore.intern_spec h hv hcap'
  exact ⟨h1, h2, EStore.lss_intern st _, EStore.scratchOn_intern st _, h3, h4⟩

end ConRon.Bridge
