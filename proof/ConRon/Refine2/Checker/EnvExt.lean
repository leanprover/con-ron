/-
# `ConRon.Refine2.Checker.EnvExt` — what a phase-A step does to the twin's index

A block job reads the frozen base below the block's counter, and the twin's job reads
the environment the block found.  The two answer alike because **phase A extends
the index and overwrites no row**: a value kind's name is checked free, a pinned
install checks each of its names, a block's names are checked free as a whole, and the
promotion does not move a name.  `EnvExt a b` is that fact: a statement about twin
environments, proved here per arm of the install, and carried by the fold's relation
(`Refine2/Checker/Top.lean`).
-/
import ConRon.Arena.Checker

open ConRon.Arena

namespace ConRon.Refine2

/-- **What every phase-A environment satisfies**: no row at or past the counter, and
every table's structure has a row. -/
structure EnvOK (f : IFEnv) : Prop where
  rows : ∀ (n : NIdx) (r : Nat × IConstantInfo), f.idx[n]? = some r → r.1 < f.visibleBelow
  tblRow : ∀ (T : NIdx) (t : IProjTable), f.tbls[T]? = some t → (f.idx[T]?).isSome

/-- **`b` extends `a`**: constants and tables pushed, whose names `a` does not hold;
`a`'s rows and tables still there, unmoved; and every other row at or past `a`'s
counter. -/
structure EnvExt (a b : IFEnv) : Prop where
  newC : ∃ new, b.env.consts = new ++ a.env.consts ∧
    new.length = b.visibleBelow - a.visibleBelow ∧ ∀ c ∈ new, a.idx[c.name]? = none
  newT : ∃ newT, b.env.tables = newT ++ a.env.tables ∧
    ∀ t ∈ newT, a.idx[t.structName]? = none
  vb : a.visibleBelow ≤ b.visibleBelow
  idxOld : ∀ (n : NIdx) (r : Nat × IConstantInfo), a.idx[n]? = some r → b.idx[n]? = some r
  idxNew : ∀ (n : NIdx) (r : Nat × IConstantInfo), b.idx[n]? = some r → a.idx[n]? = none → a.visibleBelow ≤ r.1
  tblOld : ∀ (T : NIdx) (t : IProjTable), a.tbls[T]? = some t → b.tbls[T]? = some t
  tblNew : ∀ (T : NIdx) (t : IProjTable), b.tbls[T]? = some t → a.tbls[T]? = none → a.idx[T]? = none
  ok : EnvOK b

theorem EnvExt.refl {a : IFEnv} (h : EnvOK a) : EnvExt a a :=
  ⟨⟨[], by simp, by simp, by simp⟩, ⟨[], by simp, by simp⟩, Nat.le_refl _,
    fun _ _ h => h, fun n r h h' => by simp [h'] at h,
    fun _ _ h => h, fun T t h h' => by simp [h'] at h, h⟩

theorem EnvExt.trans {a b c : IFEnv} (h₁ : EnvExt a b) (h₂ : EnvExt b c) : EnvExt a c := by
  obtain ⟨n₁, e₁, l₁, f₁⟩ := h₁.newC
  obtain ⟨n₂, e₂, l₂, f₂⟩ := h₂.newC
  obtain ⟨t₁, g₁, q₁⟩ := h₁.newT
  obtain ⟨t₂, g₂, q₂⟩ := h₂.newT
  have hback : ∀ n : NIdx, b.idx[n]? = none → a.idx[n]? = none := by
    intro n hn
    cases ha : a.idx[n]? with
    | none => rfl
    | some r => rw [h₁.idxOld n r ha] at hn; cases hn
  refine ⟨⟨n₂ ++ n₁, by rw [e₂, e₁, List.append_assoc], ?_, ?_⟩, ⟨t₂ ++ t₁, by
      rw [g₂, g₁, List.append_assoc], ?_⟩, Nat.le_trans h₁.vb h₂.vb,
    fun n r h => h₂.idxOld n r (h₁.idxOld n r h), ?_,
    fun T t h => h₂.tblOld T t (h₁.tblOld T t h), ?_, h₂.ok⟩
  · have := h₁.vb; have := h₂.vb; simp only [List.length_append]; omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hback _ (f₂ x hx)
    · exact f₁ x hx
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hback _ (q₂ x hx)
    · exact q₁ x hx
  · intro n r hc ha
    cases hb : b.idx[n]? with
    | none => exact Nat.le_trans h₁.vb (h₂.idxNew n r hc hb)
    | some r' =>
      rw [h₂.idxOld n r' hb] at hc
      cases hc
      exact h₁.idxNew n _ hb ha
  · intro T t hc ha
    cases hb : b.tbls[T]? with
    | none => exact hback _ (h₂.tblNew T t hc hb)
    | some t' => exact h₁.tblNew T t' hb ha

/-- A name the later environment's lookup misses, the earlier one's row misses. -/
theorem EnvExt.free_back {a b : IFEnv} (h : EnvExt a b) (ha : EnvOK a) {n : NIdx}
    (hf : b.find? n = none) : a.idx[n]? = none := by
  cases hr : a.idx[n]? with
  | none => rfl
  | some r =>
    have hb := h.idxOld n r hr
    have hlt := Nat.lt_of_lt_of_le (ha.rows n r hr) h.vb
    obtain ⟨c, ci⟩ := r
    simp only [IFEnv.find?, hb] at hf
    rw [ite_eq_left hlt] at hf
    cases hf

/-- A free name, at the environment's own row. -/
theorem EnvOK.free {a : IFEnv} (ha : EnvOK a) {n : NIdx} (hf : a.find? n = none) :
    a.idx[n]? = none :=
  (EnvExt.refl ha).free_back ha hf

/-- **A push of a name `a` does not hold.** -/
theorem EnvExt.push {a b : IFEnv} (h : EnvExt a b) {ci : IConstantInfo}
    (hfree : a.idx[ci.name]? = none) : EnvExt a (b.push ci) := by
  obtain ⟨n₁, e₁, l₁, f₁⟩ := h.newC
  have hvb := h.vb
  refine ⟨⟨ci :: n₁, by simp [IFEnv.push, e₁], by simp [IFEnv.push, l₁]; omega, ?_⟩, ?_, ?_,
    ?_, ?_, h.tblOld, h.tblNew, ⟨?_, ?_⟩⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hfree
    · exact f₁ x hx
  · obtain ⟨t₁, g₁, q₁⟩ := h.newT
    exact ⟨t₁, by simpa [IFEnv.push] using g₁, q₁⟩
  · simp only [IFEnv.push]; omega
  · intro n r hr
    have hne : (ci.name == n) = false := by
      rw [beq_eq_false_iff_ne]
      rintro rfl
      rw [hfree] at hr; cases hr
    simp only [IFEnv.push, Std.HashMap.getElem?_insert, hne, ite_false, Bool.false_eq_true]
    exact h.idxOld n r hr
  · intro n r hr ha
    simp only [IFEnv.push, Std.HashMap.getElem?_insert] at hr
    split at hr
    · cases hr; exact hvb
    · exact h.idxNew n r hr ha
  · intro n r hr
    simp only [IFEnv.push, Std.HashMap.getElem?_insert] at hr
    split at hr
    · cases hr; simp [IFEnv.push]
    · have := h.ok.rows n r hr; simp only [IFEnv.push]; omega
  · intro T t ht
    have := h.ok.tblRow T t ht
    simp only [IFEnv.push, Std.HashMap.getElem?_insert]
    split <;> simp_all

/-- **A table pushed at a structure `a` does not hold and `b` does.** -/
theorem EnvExt.pushTable {a b : IFEnv} (h : EnvExt a b) (ha : EnvOK a) {t : IProjTable}
    (hfree : a.idx[t.structName]? = none) (hrow : (b.idx[t.structName]?).isSome) :
    EnvExt a (b.pushTable t) := by
  obtain ⟨t₁, g₁, q₁⟩ := h.newT
  refine ⟨?_, ⟨t :: t₁, by simp [IFEnv.pushTable, g₁], ?_⟩, h.vb, h.idxOld, h.idxNew, ?_, ?_,
    ⟨h.ok.rows, ?_⟩⟩
  · obtain ⟨n₁, e₁, l₁, f₁⟩ := h.newC
    exact ⟨n₁, by simpa [IFEnv.pushTable] using e₁, l₁, f₁⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hfree
    · exact q₁ x hx
  · intro T x hx
    have hne : (t.structName == T) = false := by
      rw [beq_eq_false_iff_ne]
      rintro rfl
      have := ha.tblRow _ x hx
      rw [hfree] at this
      cases this
    simp only [IFEnv.pushTable, Std.HashMap.getElem?_insert, hne, ite_false, Bool.false_eq_true]
    exact h.tblOld T x hx
  · intro T x hx hn
    simp only [IFEnv.pushTable, Std.HashMap.getElem?_insert] at hx
    split at hx
    · rename_i he
      rw [← eq_of_beq he]; exact hfree
    · exact h.tblNew T x hx hn
  · intro T x hx
    simp only [IFEnv.pushTable, Std.HashMap.getElem?_insert] at hx
    split at hx
    · rename_i he
      rw [← eq_of_beq he]; exact hrow
    · exact h.ok.tblRow T x hx

theorem envOK_empty : EnvOK (mkIFEnv IEnv.empty) :=
  ⟨fun n r h => by simp [mkIFEnv, mkIFEnvGo, IEnv.empty] at h,
   fun T t h => by simp [mkIFEnv, mkIFEnvTblsGo, IEnv.empty] at h⟩

end ConRon.Refine2
