import ConRon.Arena
import Std.Tactic.Do

namespace ConRon.Bridge.Grouping

open ConRon.Arena

/-- All four scratch flags up. -/
def AllOn (st : EStore) : Prop :=
  st.scratchOn = true ∧ st.lss.scratchOn = true ∧ st.lss.ls.scratchOn = true ∧
    st.lss.ls.ns.scratchOn = true

/-- A store step that kept the persistent tiers and the scratch flags. -/
def Fr (st st' : EStore) : Prop := AllOn st' ∧ st'.enableScratch = st.enableScratch

theorem NStore.intern_frame (st : NStore) (v : NNodeView) (h : st.scratchOn = true) :
    (st.intern v).1.scratchOn = true ∧ (st.intern v).1.enableScratch = st.enableScratch := by
  unfold NStore.intern
  split
  · exact ⟨h, rfl⟩
  · simp only [h, if_true]
    split <;> simp_all [NStore.enableScratch]

theorem LStore.intern_frame (st : LStore) (v : LNodeView) (h : st.scratchOn = true) :
    (st.intern v).1.scratchOn = true ∧ (st.intern v).1.ns = st.ns ∧
      (st.intern v).1.enableScratch = st.enableScratch := by
  unfold LStore.intern
  split
  · exact ⟨h, rfl, rfl⟩
  · simp only [h, if_true]
    split <;> simp_all [LStore.enableScratch]

theorem LsStore.intern_frame (st : LsStore) (v : LsNodeView) (h : st.scratchOn = true) :
    (st.intern v).1.scratchOn = true ∧ (st.intern v).1.ls = st.ls ∧
      (st.intern v).1.enableScratch = st.enableScratch := by
  unfold LsStore.intern
  split
  · exact ⟨h, rfl, rfl⟩
  · simp only [h, if_true]
    split <;> simp_all [LsStore.enableScratch]

theorem Fr.refl {st : EStore} (h : AllOn st) : Fr st st := ⟨h, rfl⟩

theorem Fr.trans {a b c : EStore} (h₁ : Fr a b) (h₂ : Fr b c) : Fr a c :=
  ⟨h₂.1, h₂.2.trans h₁.2⟩

theorem internName_frame (st : EStore) (v : NNodeView) (h : AllOn st) :
    Fr st (st.internName v).1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have := NStore.intern_frame st.lss.ls.ns v h4
  simp only [EStore.internName, LsStore.internName, LStore.internName, Fr, AllOn,
    EStore.enableScratch, LsStore.enableScratch, LStore.enableScratch] at this ⊢
  refine ⟨⟨h1, h2, h3, this.1⟩, ?_⟩
  rw [this.2]

theorem internLevel_frame (st : EStore) (v : LNodeView) (h : AllOn st) :
    Fr st (st.internLevel v).1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have := LStore.intern_frame st.lss.ls v h3
  simp only [EStore.internLevel, LsStore.internLevel, Fr, AllOn,
    EStore.enableScratch, LsStore.enableScratch] at this ⊢
  refine ⟨⟨h1, h2, this.1, by rw [this.2.1]; exact h4⟩, ?_⟩
  rw [this.2.2]

theorem internLevels_frame (st : EStore) (v : LsNodeView) (h : AllOn st) :
    Fr st (st.internLevels v).1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have := LsStore.intern_frame st.lss v h2
  simp only [EStore.internLevels, Fr, AllOn, EStore.enableScratch] at this ⊢
  refine ⟨⟨h1, this.1, by rw [this.2.1]; exact h3, by rw [this.2.1]; exact h4⟩, ?_⟩
  rw [this.2.2]

theorem internBM_frame (st : EStore) (m : ConLeche.BinderMeta) (h : AllOn st) :
    Fr st (st.internBM m).1 := by
  unfold EStore.internBM
  obtain ⟨h1, h2, h3, h4⟩ := h
  repeat' split
  all_goals simp_all [Fr, AllOn, EStore.enableScratch]

theorem internAt_frame (st : EStore) (v : ENodeView) (mi : BMIdx) (h : AllOn st) :
    Fr st (st.internAt v mi).1 := by
  unfold EStore.internAt
  obtain ⟨h1, h2, h3, h4⟩ := h
  repeat' split
  all_goals simp_all [Fr, AllOn, EStore.enableScratch]

theorem internBMOfView_frame (st : EStore) (v : ENodeView) (h : AllOn st) :
    Fr st (st.internBMOfView v).1 := by
  unfold EStore.internBMOfView
  split
  · exact internBM_frame st _ h
  · exact internBM_frame st _ h
  · exact Fr.refl h

theorem intern_frame (st : EStore) (v : ENodeView) (h : AllOn st) :
    Fr st (st.intern v).1 := by
  have h1 := internBMOfView_frame st v h
  exact h1.trans (internAt_frame _ v _ h1.1)

theorem internBindI_frame (st : EStore) (tag : UInt32) (ty b : EIdx) (mi : BMIdx)
    (h : AllOn st) : Fr st (st.internBindI tag ty b mi).1 := by
  have h1 := h.1
  unfold EStore.internBindI
  simp only
  cases hp : st.persFindBindMaybe tag ⟨ty, b, mi⟩ with
  | some _ => exact Fr.refl h
  | none =>
    simp only [h1, if_true]
    cases hs : st.scr.findBind tag ⟨ty, b, mi⟩ with
    | some _ => exact Fr.refl h
    | none => exact ⟨⟨rfl, h.2⟩, rfl⟩

end ConRon.Bridge.Grouping

namespace ConRon.Bridge.Grouping
open ConRon.Arena

/-! Simp forms of the frame lemmas. -/

@[simp] theorem allOn_internName {st : EStore} {v} (h : AllOn st) :
    AllOn (st.internName v).1 := (internName_frame st v h).1
@[simp] theorem en_internName {st : EStore} {v} (h : AllOn st) :
    (st.internName v).1.enableScratch = st.enableScratch := (internName_frame st v h).2
@[simp] theorem allOn_internLevel {st : EStore} {v} (h : AllOn st) :
    AllOn (st.internLevel v).1 := (internLevel_frame st v h).1
@[simp] theorem en_internLevel {st : EStore} {v} (h : AllOn st) :
    (st.internLevel v).1.enableScratch = st.enableScratch := (internLevel_frame st v h).2
@[simp] theorem allOn_internLevels {st : EStore} {v} (h : AllOn st) :
    AllOn (st.internLevels v).1 := (internLevels_frame st v h).1
@[simp] theorem en_internLevels {st : EStore} {v} (h : AllOn st) :
    (st.internLevels v).1.enableScratch = st.enableScratch := (internLevels_frame st v h).2
@[simp] theorem allOn_internBM {st : EStore} {m} (h : AllOn st) :
    AllOn (st.internBM m).1 := (internBM_frame st m h).1
@[simp] theorem en_internBM {st : EStore} {m} (h : AllOn st) :
    (st.internBM m).1.enableScratch = st.enableScratch := (internBM_frame st m h).2
@[simp] theorem allOn_intern {st : EStore} {v} (h : AllOn st) :
    AllOn (st.intern v).1 := (intern_frame st v h).1
@[simp] theorem en_intern {st : EStore} {v} (h : AllOn st) :
    (st.intern v).1.enableScratch = st.enableScratch := (intern_frame st v h).2
@[simp] theorem allOn_internBindI {st : EStore} {tag ty b mi} (h : AllOn st) :
    AllOn (st.internBindI tag ty b mi).1 := (internBindI_frame st tag ty b mi h).1
@[simp] theorem en_internBindI {st : EStore} {tag ty b mi} (h : AllOn st) :
    (st.internBindI tag ty b mi).1.enableScratch = st.enableScratch :=
  (internBindI_frame st tag ty b mi h).2
@[simp] theorem allOn_internLamI {st : EStore} {ty b mi} (h : AllOn st) :
    AllOn (st.internLamI ty b mi).1 := (internBindI_frame st _ ty b mi h).1
@[simp] theorem en_internLamI {st : EStore} {ty b mi} (h : AllOn st) :
    (st.internLamI ty b mi).1.enableScratch = st.enableScratch :=
  (internBindI_frame st _ ty b mi h).2
@[simp] theorem allOn_internForallEI {st : EStore} {ty b mi} (h : AllOn st) :
    AllOn (st.internForallEI ty b mi).1 := (internBindI_frame st _ ty b mi h).1
@[simp] theorem en_internForallEI {st : EStore} {ty b mi} (h : AllOn st) :
    (st.internForallEI ty b mi).1.enableScratch = st.enableScratch :=
  (internBindI_frame st _ ty b mi h).2

end ConRon.Bridge.Grouping
