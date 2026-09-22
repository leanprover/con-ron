/-
# `ConRon.Bridge.StoreBind` — `internBindI`'s store spec

The second obligation task #97a's frozen API does not cover, and the one task
#97-P6-16 added: `EStore.internBindI` (and its two `@[inline]` faces
`internLamI` / `internForallEI`) is the `intern` the REBUILDING WALKS call —
they take a binder apart with `viewBindI` and put it back with this, so the
datum is never decoded on the way through — and `Arena/WFProofs.lean` proves
nothing about it.  `EStore.intern` has `intern_spec`; `internAt` has
`internAt_wf_view` and `internAt_isPersistent_of_off`; `internBindI` has
neither.

**What it is, and why the proof is short.**  `internBindI tag ty b mi` and
`internAt (eBindView tag ty b m) mi` are the SAME store operation whenever
`st.viewBM mi = some m`:

* the cons probe is literally the same — `ETables.find? (.lam ty b _) mi` is
  `t.lams.find? ⟨ty, b, mi⟩` (`Store.lean:1021`) and
  `ETables.findBind ETag.lam ⟨ty, b, mi⟩` is the same expression
  (`Store.lean:~1104`);
* the append is the same — `ETables.push` at a binder arm pushes
  `⟨ty, b, mi⟩` into the same array as `ETables.pushBind`, and the derived
  word agrees by `Store.lean:1381`'s own stated obligation
  "`derOfBindAtI … mi = derOfBindAt … m`", which `EWFAt.bmDerExact` supplies.

So the route is: prove `internBindI_eq_internAt`, then quote
`EStore.internAt_wf_view` and `EStore.internAt_isPersistent_of_off`.  Its
three side conditions are all available at the call site:
`ENodeView.BMOK st.viewBM (eBindView tag ty b m) mi` is `hbm` itself,
and `st.findBMOfView (eBindView tag ty b m) = some mi` is
`EWFAt.findBM_of_viewBM`.

**`mi.tag = 0` is a HYPOTHESIS, not a derivation** (task #97-P3-0's finding;
the note this file shipped with claimed otherwise).  `EStore.viewBM` reads the
datum array at the handle's INDEX under the handle's TIER bit and never looks
at its tag — the datum store has one constructor, so there is no tag dispatch
to give the tag back (`WF.lean`'s own "Why the three binder-datum clauses say
`tag = 0`").  So `st.viewBM mi = some m` holds of every handle differing from
the real one only in bits 31…28: with the datum at `Idx.mk 0 0 0` (word `0`),
the handle `Idx.mk 1 0 0` (word `2^28`) has the same tier and the same index
and decodes to the same datum.  `EWFAt.bmChildOK`'s third conjunct demands
`mi.tag = 0` of the handle a binder RECORD stores, so pushing such a handle
produces a store that is genuinely not well formed — the spec is false
without the hypothesis, and neither `bmConsP` nor `findBM_of_viewBM` can
supply it (`findBM_of_viewBM` *assumes* it).  Every producer establishes it
instead: `ETables.pushBM` builds `Idx.mk 0 tier _`, `bmConsP`/`bmConsS` carry
it for whatever `findBM` answers, and `bmChildOK` carries it for whatever
`viewBindI` answers — so a rebuilding walk, which got `mi` from `viewBindI`,
has it in hand.
-/
import ConRon.Bridge.StoreBM

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
    {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true) :
    (eBindView tag ty b m).echildren = [ty, b] := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-- con-leche: none — arena infrastructure; a binder view names no name
handle. -/
theorem ENodeView.nchildren_eBindView {tag : UInt32} {ty b : EIdx}
    {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true) :
    (eBindView tag ty b m).nchildren = [] := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-- con-leche: none — arena infrastructure; a binder view names no level
handle. -/
theorem ENodeView.lchildren_eBindView {tag : UInt32} {ty b : EIdx}
    {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true) :
    (eBindView tag ty b m).lchildren = [] := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-- con-leche: none — arena infrastructure; a binder view names no
level-list handle. -/
theorem ENodeView.lschildren_eBindView {tag : UInt32} {ty b : EIdx}
    {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true) :
    (eBindView tag ty b m).lschildren = [] := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-- con-leche: none — arena infrastructure; `bindSizeOf tag` IS `sizeOf` of
the view that tag builds, so `internBindI`'s capacity test is `internAt`'s. -/
theorem ETables.sizeOf_eBindView (t : ETables) {tag : UInt32} {ty b : EIdx}
    {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true) :
    t.sizeOf (eBindView tag ty b m) = t.bindSizeOf tag := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-! ## `internBindI` IS `internAt` at the view the datum spells out

The three components of the module note's step 1: the cons probe, the append,
and the derived word. -/

/-- con-leche: none — arena infrastructure; the cons probe at a binder
RECORD is the cons probe at the VIEW that record spells out — the same
`Tbl.find?` at the same key, by definition of both. -/
theorem ETables.findBind_eq_find? (t : ETables) {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true) :
    t.findBind tag ⟨ty, b, mi⟩ = t.find? (eBindView tag ty b m) mi := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-- con-leche: none — arena infrastructure; and the append at a binder RECORD
is the append at that VIEW: the same array, the same record, the same
handle. -/
theorem ETables.pushBind_eq_push (t : ETables) {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {m : ConLeche.BinderMeta} (d : UInt64) (tier : UInt32)
    (htag : ETag.isBind tag = true) :
    t.pushBind tag ⟨ty, b, mi⟩ d tier = t.push (eBindView tag ty b m) d mi tier := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · rfl
  · rfl

/-- con-leche: none — arena infrastructure; `Store.lean:1381`'s own stated
obligation: the derived word computed off the datum's HANDLE is the one
computed off its value, because the datum store's derived column is the
datum's hash and its record carries the has-a-parameter bit
(`EWFAt.bmDerExact`). -/
theorem EStore.derOfBindAtI_eq_derOfView {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true)
    (hder : st.bmDer mi = (hash m.pw, m.pw.hasParams)) :
    st.derOfBindAtI (if tag == ETag.lam then 19 else 23) ty b mi
      = st.derOfView (eBindView tag ty b m) := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · show st.derOfBindAtI 19 ty b mi = st.derOfBindAt 19 ty b m
    simp only [EStore.derOfBindAtI, EStore.derOfBindAt, hder]
  · show st.derOfBindAtI 23 ty b mi = st.derOfBindAt 23 ty b m
    simp only [EStore.derOfBindAtI, EStore.derOfBindAt, hder]

/-- con-leche: none — arena infrastructure; **`internBindI` is `internAt`**:
the binder `intern` over a datum HANDLE is the ordinary `intern` at the node
view that handle decodes to.  Both probes are the same `Tbl.find?` at the same
key, both appends push the same record into the same array, and the derived
words agree by `derOfBindAtI_eq_derOfView`. -/
theorem EStore.internBindI_eq_internAt {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true)
    (hder : st.bmDer mi = (hash m.pw, m.pw.hasParams)) :
    st.internBindI tag ty b mi = st.internAt (eBindView tag ty b m) mi := by
  simp only [EStore.internBindI, EStore.internAt,
    EStore.derOfBindAtI_eq_derOfView htag hder,
    ETables.findBind_eq_find? (m := m) _ htag,
    ETables.pushBind_eq_push (m := m) _ _ _ htag]

/-! ## `internAt`'s scratch flag

`Ext` for the node half is `Arena/WFProofs.lean`'s own
`EStore.internAt_ext` (task #97a follow-up 4); the flag is still this
file's. -/

/-- con-leche: none — arena infrastructure; the node half of `intern` leaves
the scratch flag alone, in all three of its branches. -/
theorem EStore.scratchOn_internAt (st : EStore) (w : ENodeView) (mi : BMIdx) :
    (st.internAt w mi).1.scratchOn = st.scratchOn := by
  rcases EStore.internAt_cases st w mi with he | he | he <;> rw [he]

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the binder
`intern` over a datum HANDLE preserves the store, extends it, and its handle
decodes to the binder view the datum spells out.

`hmi0` is the one hypothesis the frozen statement did not carry and cannot
derive; the module note says why, and why every caller has it. -/
theorem EStore.internBindI_spec {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {m : ConLeche.BinderMeta} (h : StoreWF st)
    (htag : ETag.isBind tag = true) (hbm : st.viewBM mi = some m)
    (hmi0 : mi.tag = 0)
    (hty : (st.view ty).isSome = true) (hb : (st.view b).isSome = true)
    (hcap : (if st.scratchOn then st.scr.bindSizeOf tag
              else st.pers.bindSizeOf tag) < Idx.idxCap) :
    StoreWF (st.internBindI tag ty b mi).1 ∧
      Ext st (st.internBindI tag ty b mi).1 ∧
      BMExt st (st.internBindI tag ty b mi).1 ∧
      (st.internBindI tag ty b mi).1.lss = st.lss ∧
      (st.internBindI tag ty b mi).1.scratchOn = st.scratchOn ∧
      (st.internBindI tag ty b mi).1.view (st.internBindI tag ty b mi).2 =
        some (eBindView tag ty b m) ∧
      denoteE (st.internBindI tag ty b mi).1 (st.internBindI tag ty b mi).2 =
        denoteEView (st.internBindI tag ty b mi).1 (eBindView tag ty b m) := by
  obtain ⟨rk, hwf⟩ := h
  -- the two operations are one
  rw [EStore.internBindI_eq_internAt htag (hwf.bmDerExact mi m hbm)]
  -- `internAt_wf_view`'s side conditions
  have hv : st.ViewOK (eBindView tag ty b m) := by
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
  have hcap' : (if st.scratchOn then st.scr.sizeOf (eBindView tag ty b m)
      else st.pers.sizeOf (eBindView tag ty b m)) < Idx.idxCap := by
    rw [ETables.sizeOf_eBindView (m := m) _ htag,
      ETables.sizeOf_eBindView (m := m) _ htag]
    exact hcap
  have hbmok : ENodeView.BMOK st.viewBM (eBindView tag ty b m) mi := by
    intro m' hm'
    rw [ENodeView.bmOf_eBindView] at hm'
    have hmm : m' = m := (Option.some.inj hm').symm
    subst hmm
    exact hbm
  have hfov : st.findBMOfView (eBindView tag ty b m) = some mi := by
    rw [EStore.findBMOfView_eq_findBM _ (ENodeView.bmOf_eBindView tag ty b m)]
    exact hwf.findBM_of_viewBM hmi0 hbm
  obtain ⟨hwf', hview'⟩ :=
    EStore.internAt_wf_view hwf hwf.scratchSync hv hcap' hmi0 hbmok hfov
  obtain ⟨rk', hwf''⟩ := hwf'
  exact ⟨⟨rk', hwf''⟩, EStore.internAt_ext st _ mi, BMExt.internAt st _ mi,
    EStore.lss_internAt st _ mi, EStore.scratchOn_internAt st _ mi, hview',
    denoteE_unfold hwf'' hview'⟩

#print axioms EStore.internBindI_spec

end ConRon.Bridge
