/-
# The skipped persistent probe changes nothing at a well-formed store (task #97-T2-LOCKSTEP D2)

The Rust's `EStore::intern_*` paths skip the PERSISTENT cons probe when the
scratch tier is on and the node record has a scratch child
(`e_view_has_scratch_child`, the per-path `sk`).  The twin now skips exactly
there too (`EStore.persFindMaybe` / `EStore.persFindBindMaybe` in
`Arena/Store.lean`).  This file is the one Theorem-1 fact that costs:
under `StoreWF` a node with a scratch child is in no persistent cons table
(`childOK`'s *persistent parents have persistent children*, `bmKeyP` +
`bmConsP` for the datum handle), so the skipping probe IS the unconditional
one:

* `EStore.persFindMaybe_eq` : `st.persFindMaybe v mi = st.pers.find? v mi`

plus three unconditional rewrites (scratch tier off, persistent probe
`none`, persistent probe `some`) for proofs that carry no `StoreWF`.
-/
import ConRon.Arena.WF

namespace ConRon.Arena

open ConLeche

/-! ## Unconditional rewrites -/

theorem EStore.pers_find_of_persFindMaybe {st : EStore} {v : ENodeView} {mi : BMIdx}
    {j : EIdx} (h : st.persFindMaybe v mi = some j) : st.pers.find? v mi = some j := by
  revert h; simp only [EStore.persFindMaybe]; split <;> (try split) <;> simp

/-- The skip spelled with the Rust's own `sk` flag: once a proof knows the
port's `sk` is the twin's test, the twin's probe is `if sk then none else …`. -/
theorem EStore.persFindMaybe_eq_sk {st : EStore} {v : ENodeView} {mi : BMIdx} {sk : Bool}
    (hsk : sk = if st.scratchOn then EStore.eRecHasScratchChild v mi else false) :
    st.persFindMaybe v mi = if sk then none else st.pers.find? v mi := by
  subst hsk; rfl

theorem EStore.persFindBindMaybe_eq_sk {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {sk : Bool}
    (hsk : sk = if st.scratchOn then EStore.bindHasScratchChild ty b mi else false) :
    st.persFindBindMaybe tag ⟨ty, b, mi⟩
      = if sk then none else st.pers.findBind tag ⟨ty, b, mi⟩ := by
  subst hsk; rfl

/-- Where the test cannot fire (`bvar`, `lit`), the probe is unconditional. -/
theorem EStore.persFindMaybe_of_noskip {st : EStore} {v : ENodeView} {mi : BMIdx}
    (h : EStore.eRecHasScratchChild v mi = false) :
    st.persFindMaybe v mi = st.pers.find? v mi := by
  simp [EStore.persFindMaybe, h]

/-! ## Finding 14's first half: a scratch child keeps a view out of the persistent table

Moved from `Refine2/Specs.lean` (task #97-P5-Specs round 3 §2). -/

/-- **Finding 14's first half, at an expression child.**  A view one of whose
EXPRESSION children is scratch is not in the persistent cons table. -/
theorem persFind?_none_of_echild {st : EStore} (hwf : StoreWF st)
    {v : ENodeView} {c : EIdx} (hc : c ∈ v.echildren)
    (hcs : c.isPersistent = false) : st.persFind? v = none := by
  obtain ⟨rk, hw⟩ := hwf
  cases hf : st.persFind? v with
  | none => rfl
  | some i =>
    exact absurd ((hw.childOK i v ((hw.consP v i).mp hf).1 c hc).2.2
      ((hw.consP v i).mp hf).2) (by rw [hcs]; simp)

/-- Finding 14's first half, at a NAME child (`const` and `proj`). -/
theorem persFind?_none_of_nchild {st : EStore} (hwf : StoreWF st)
    {v : ENodeView} {c : NIdx} (hc : c ∈ v.nchildren)
    (hcs : c.isPersistent = false) : st.persFind? v = none := by
  obtain ⟨rk, hw⟩ := hwf
  cases hf : st.persFind? v with
  | none => rfl
  | some i =>
    exact absurd ((hw.nchildOK i v ((hw.consP v i).mp hf).1 c hc).2
      ((hw.consP v i).mp hf).2) (by rw [hcs]; simp)

/-- Finding 14's first half, at a LEVEL child (`sort`). -/
theorem persFind?_none_of_lchild {st : EStore} (hwf : StoreWF st)
    {v : ENodeView} {c : LIdx} (hc : c ∈ v.lchildren)
    (hcs : c.isPersistent = false) : st.persFind? v = none := by
  obtain ⟨rk, hw⟩ := hwf
  cases hf : st.persFind? v with
  | none => rfl
  | some i =>
    exact absurd ((hw.lchildOK i v ((hw.consP v i).mp hf).1 c hc).2
      ((hw.consP v i).mp hf).2) (by rw [hcs]; simp)

/-- Finding 14's first half, at a LEVEL-LIST child (`const`). -/
theorem persFind?_none_of_lschild {st : EStore} (hwf : StoreWF st)
    {v : ENodeView} {c : LsIdx} (hc : c ∈ v.lschildren)
    (hcs : c.isPersistent = false) : st.persFind? v = none := by
  obtain ⟨rk, hw⟩ := hwf
  cases hf : st.persFind? v with
  | none => rfl
  | some i =>
    exact absurd ((hw.lschildOK i v ((hw.consP v i).mp hf).1 c hc).2
      ((hw.consP v i).mp hf).2) (by rw [hcs]; simp)

/-- The VIEW test (`EStore.eViewHasScratchChild`, the Rust's function) answers `true`
only at a view the persistent cons table does not hold. -/
theorem persFind?_none_of_eViewHasScratchChild {st : EStore} (hwf : StoreWF st)
    {v : ENodeView} (h : EStore.eViewHasScratchChild v = true) : st.persFind? v = none := by
  cases v with
  | bvar _ => simp [EStore.eViewHasScratchChild] at h
  | lit _ => simp [EStore.eViewHasScratchChild] at h
  | fvar idx ty =>
    exact persFind?_none_of_echild hwf (c := ty) (by simp [ENodeView.echildren])
      (by simpa [EStore.eViewHasScratchChild] using h)
  | sort u =>
    exact persFind?_none_of_lchild hwf (c := u) (by simp [ENodeView.lchildren])
      (by simpa [EStore.eViewHasScratchChild] using h)
  | const n us =>
    simp only [EStore.eViewHasScratchChild] at h
    cases hn : n.isPersistent
    · exact persFind?_none_of_nchild hwf (c := n) (by simp [ENodeView.nchildren]) hn
    · rw [hn] at h
      exact persFind?_none_of_lschild hwf (c := us) (by simp [ENodeView.lschildren])
        (by simpa using h)
  | app f a =>
    simp only [EStore.eViewHasScratchChild] at h
    cases hf : f.isPersistent
    · exact persFind?_none_of_echild hwf (c := f) (by simp [ENodeView.echildren]) hf
    · rw [hf] at h
      exact persFind?_none_of_echild hwf (c := a) (by simp [ENodeView.echildren])
        (by simpa using h)
  | lam ty b m =>
    simp only [EStore.eViewHasScratchChild] at h
    cases ht : ty.isPersistent
    · exact persFind?_none_of_echild hwf (c := ty) (by simp [ENodeView.echildren]) ht
    · rw [ht] at h
      exact persFind?_none_of_echild hwf (c := b) (by simp [ENodeView.echildren])
        (by simpa using h)
  | forallE ty b m =>
    simp only [EStore.eViewHasScratchChild] at h
    cases ht : ty.isPersistent
    · exact persFind?_none_of_echild hwf (c := ty) (by simp [ENodeView.echildren]) ht
    · rw [ht] at h
      exact persFind?_none_of_echild hwf (c := b) (by simp [ENodeView.echildren])
        (by simpa using h)
  | letE ty val b =>
    simp only [EStore.eViewHasScratchChild] at h
    cases ht : ty.isPersistent
    · exact persFind?_none_of_echild hwf (c := ty) (by simp [ENodeView.echildren]) ht
    · rw [ht] at h
      cases hv : val.isPersistent
      · exact persFind?_none_of_echild hwf (c := val) (by simp [ENodeView.echildren]) hv
      · rw [hv] at h
        exact persFind?_none_of_echild hwf (c := b) (by simp [ENodeView.echildren])
          (by simpa using h)
  | proj n i e =>
    simp only [EStore.eViewHasScratchChild] at h
    cases hn : n.isPersistent
    · exact persFind?_none_of_nchild hwf (c := n) (by simp [ENodeView.nchildren]) hn
    · rw [hn] at h
      exact persFind?_none_of_echild hwf (c := e) (by simp [ENodeView.echildren])
        (by simpa using h)

/-- At a binder record: a persistent binder node names a persistent datum
(`bmKeyP` + `bmConsP`), and its view is `persFind?`'s at the datum the key
names. -/
theorem pers_find_bind_none_of_skip {st : EStore} (hwf : StoreWF st)
    {ty b : EIdx} {m0 : ConLeche.BinderMeta} {mi : BMIdx} {v : ENodeView}
    (hv : v = .lam ty b m0 ∨ v = .forallE ty b m0)
    (h : EStore.bindHasScratchChild ty b mi = true) : st.pers.find? v mi = none := by
  cases hj : st.pers.find? v mi with
  | none => rfl
  | some j =>
    obtain ⟨rk, hw⟩ := id hwf
    have hbmv : v.bmOf = some m0 := by rcases hv with rfl | rfl <;> rfl
    rcases hw.bmKeyP v mi j hj with hn | ⟨m, hm⟩
    · rw [hbmv] at hn; cases hn
    have hmiP : mi.isPersistent = true := ((hw.bmConsP m mi).mp hm).2.1
    -- the same key at the datum `m` the table names
    let v' : ENodeView := match v with
      | .lam _ _ _ => .lam ty b m
      | _ => .forallE ty b m
    have hv'j : st.pers.find? v' mi = some j := by
      rcases hv with rfl | rfl <;> exact hj
    have hfb : st.findBMOfView v' = some mi := by
      have : st.findBM m = some mi := by
        simp only [EStore.findBM, EStore.persFindBM, hm]
      rcases hv with rfl | rfl <;> exact this
    have hpf : st.persFind? v' = some j := by
      simp only [EStore.persFind?, hfb, hv'j]
    have hch : EStore.eViewHasScratchChild v' = true := by
      simp only [EStore.bindHasScratchChild, hmiP] at h
      rcases hv with rfl | rfl <;> simpa [v', EStore.eViewHasScratchChild] using h
    rw [persFind?_none_of_eViewHasScratchChild hwf hch] at hpf
    cases hpf

/-- The RECORD test (`EStore.eRecHasScratchChild`, the Rust's per-path `sk`) answers
`true` only at a key the persistent cons table does not hold. -/
theorem pers_find_none_of_eRecHasScratchChild {st : EStore} (hwf : StoreWF st)
    {v : ENodeView} {mi : BMIdx} (h : EStore.eRecHasScratchChild v mi = true) :
    st.pers.find? v mi = none := by
  cases v with
  | lam ty b m => exact pers_find_bind_none_of_skip hwf (Or.inl rfl) h
  | forallE ty b m => exact pers_find_bind_none_of_skip hwf (Or.inr rfl) h
  | bvar i => exact persFind?_none_of_eViewHasScratchChild (v := .bvar i) hwf h
  | fvar i ty => exact persFind?_none_of_eViewHasScratchChild (v := .fvar i ty) hwf h
  | sort u => exact persFind?_none_of_eViewHasScratchChild (v := .sort u) hwf h
  | const n us => exact persFind?_none_of_eViewHasScratchChild (v := .const n us) hwf h
  | app f a => exact persFind?_none_of_eViewHasScratchChild (v := .app f a) hwf h
  | letE ty val b =>
    exact persFind?_none_of_eViewHasScratchChild (v := .letE ty val b) hwf h
  | lit l => exact persFind?_none_of_eViewHasScratchChild (v := .lit l) hwf h
  | proj n i e => exact persFind?_none_of_eViewHasScratchChild (v := .proj n i e) hwf h

/-! ## The two equations -/

/-- **D2's equation at the view probe**: under `StoreWF` the skipping
persistent probe is the unconditional one, so `findAt`, `internAt`, `find?`
and `intern` compute as they did before the skip. -/
theorem EStore.persFindMaybe_eq {st : EStore} (hwf : StoreWF st) (v : ENodeView)
    (mi : BMIdx) : st.persFindMaybe v mi = st.pers.find? v mi := by
  simp only [EStore.persFindMaybe]
  cases st.scratchOn <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  cases hr : EStore.eRecHasScratchChild v mi
  · simp
  · simp [pers_find_none_of_eRecHasScratchChild hwf hr]

end ConRon.Arena
