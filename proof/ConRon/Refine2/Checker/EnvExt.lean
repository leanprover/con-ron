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
    ∀ t ∈ newT, a.idx[t.structName]? = none ∧ (b.idx[t.structName]?).isSome
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
    · exact ⟨hback _ (q₂ x hx).1, (q₂ x hx).2⟩
    · refine ⟨(q₁ x hx).1, ?_⟩
      have := (q₁ x hx).2
      cases hb : b.idx[x.structName]? with
      | none => rw [hb] at this; cases this
      | some r => rw [h₂.idxOld _ r hb]; rfl
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
    refine ⟨t₁, by simpa [IFEnv.push] using g₁, fun x hx => ⟨(q₁ x hx).1, ?_⟩⟩
    have := (q₁ x hx).2
    simp only [IFEnv.push, Std.HashMap.getElem?_insert]
    split <;> simp_all
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
    · exact ⟨hfree, hrow⟩
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

/-! ## The arms of a step

A small Hoare logic over `AM`: what an accepting run answers.  Nothing of the state is
needed, since each guard reads the environment, and a guard that does not bear on the
result is `Post.any`. -/

/-- `m`'s answers satisfy `Q`, at every state it accepts from. -/
def Post {α : Type} (m : AM α) (Q : α → Prop) : Prop :=
  ∀ s r s', m s = .ok (r, s') → Q r

theorem Post.any {α : Type} (m : AM α) : Post m (fun _ => True) := fun _ _ _ _ => trivial

theorem Post.pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    Post (Pure.pure a : AM α) Q := by
  intro s r s' hr
  cases hr
  exact h

theorem Post.bind {α β : Type} {m : AM α} {k : α → AM β} {P : α → Prop} {Q : β → Prop}
    (hm : Post m P) (hk : ∀ a, P a → Post (k a) Q) : Post (m >>= k) Q := by
  intro s r s' hr
  cases hms : m s with
  | error e =>
    have hr' : (m s >>= fun p => k p.1 p.2) = .ok (r, s') := hr
    rw [hms] at hr'
    cases hr'
  | ok p =>
    have hr' : (m s >>= fun p => k p.1 p.2) = .ok (r, s') := hr
    rw [hms] at hr'
    exact hk p.1 (hm s p.1 p.2 hms) p.2 r s' hr'

theorem Post.fail {α : Type} {e : CheckError} {Q : α → Prop} :
    Post (Arena.fail e : AM α) Q := by
  intro s r s' hr
  cases hr

theorem Post.ite {α : Type} {c : Prop} [Decidable c] {a b : AM α} {Q : α → Prop}
    (ha : c → Post a Q) (hb : ¬ c → Post b Q) : Post (if c then a else b) Q := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

/-- A failure, whatever follows it. -/
theorem Post.fail_bind {α β : Type} {e : CheckError} {k : α → AM β} {Q : β → Prop} :
    Post (Arena.fail e >>= k) Q :=
  Post.bind (P := fun _ => False) Post.fail (fun _ h => h.elim)

/-- Walk a `do` block whose guards do not bear on `Q`: a bind's left side is forgotten,
a join point inlined, an `if` or a `match` split, a failure discharged.  What is left
is the block's `pure`s. -/
macro "post_walk" : tactic =>
  `(tactic| repeat' (first
    | exact Post.fail
    | exact Post.fail_bind
    | exact Post.pure rfl
    | exact Post.pure (by assumption)
    | (refine Post.bind (Post.any _) (fun _ _ => ?_))
    | split
    | (dsimp only; done)
    | (show Post _ _; dsimp only)))

/-- A name's guard: `installHeader` answers only at a free name. -/
theorem installHeader_free (fe : IFEnv) (cv : IConstantVal) :
    Post (installHeader fe cv) (fun _ => fe.find? cv.name = none) := by
  rw [installHeader]
  by_cases hf : (fe.find? cv.name).isSome = true
  · rw [ite_eq_left hf]
    exact Post.fail_bind
  · rw [ite_eq_right hf]
    intro s r s' _
    simpa using hf

/-- `checkConstantVal` likewise. -/
theorem checkConstantVal_free (mode : ConLeche.CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    Post (checkConstantVal mode fe cv) (fun _ => fe.find? cv.name = none) := by
  rw [checkConstantVal]
  by_cases hf : (fe.find? cv.name).isSome = true
  · rw [ite_eq_left hf]
    exact Post.fail_bind
  · rw [ite_eq_right hf]
    intro s r s' _
    simpa using hf

theorem checkDefnVal_result (mode : ConLeche.CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (v : EIdx) (hint : ConLeche.ReducibilityHint) :
    Post (checkDefnVal mode fe cv v hint) (· = fe.push (.defnInfo cv v hint)) := by
  rw [checkDefnVal]
  post_walk

theorem checkThmVal_result (mode : ConLeche.CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (v : EIdx) : Post (checkThmVal mode fe cv v) (· = fe.push (.thmInfo cv)) := by
  rw [checkThmVal]
  post_walk

theorem checkOpaqueVal_result (mode : ConLeche.CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (v : EIdx) : Post (checkOpaqueVal mode fe cv v) (· = fe.push (.axiomInfo cv)) := by
  rw [checkOpaqueVal]
  post_walk

/-- A pinned install: every name checked at the environment it is pushed on. -/
theorem installBasisDecls_ext {A : IFEnv} (hA : EnvOK A) :
    ∀ (L : List IConstantInfo) (b : IFEnv), EnvExt A b →
      Post (installBasisDecls b L) (EnvExt A)
  | [], _, h => by
    rw [installBasisDecls]
    exact Post.pure h
  | ci :: cs, b, h => by
    rw [installBasisDecls]
    refine Post.bind (P := EnvExt A) ?_ (fun b' h' => installBasisDecls_ext hA cs b' h')
    rw [installBasisDecl]
    dsimp only
    split
    · rename_i hf
      have : b.find? ci.name = none := by simpa using hf
      exact Post.bind (Post.any _) fun _ _ => Post.pure (h.push (h.free_back hA this))
    · exact Post.fail_bind

theorem checkBasisDecl_ext {A : IFEnv} (hA : EnvOK A) (kind : ConLeche.BasisKind) :
    Post (checkBasisDecl A kind) (EnvExt A) := by
  rw [checkBasisDecl]
  post_walk
  all_goals exact installBasisDecls_ext hA _ A (EnvExt.refl hA)

/-- **`checkDecl` on what phase A sends it**, every kind but a block. -/
theorem checkDecl_ext {A : IFEnv} (hA : EnvOK A) (mode : ConLeche.CheckMode)
    (pins : List INatOpPinSet) (d : IDeclaration) (hd : ∀ b n, d ≠ .indDecl b n) :
    Post (checkDecl mode pins A d) (EnvExt A) := by
  have h0 := EnvExt.refl hA
  cases d with
  | indDecl b n => exact absurd rfl (hd b n)
  | defnDecl cv v hint =>
    simp only [checkDecl]
    refine Post.bind (checkConstantVal_free mode A cv) fun _ hf => ?_
    refine Post.bind (checkDefnVal_result mode A cv v hint) fun _ hr => ?_
    subst hr
    have h1 := h0.push (ci := .defnInfo cv v hint) (hA.free hf)
    post_walk
  | thmDecl cv v =>
    simp only [checkDecl]
    refine Post.bind (checkConstantVal_free mode A cv) fun _ hf => ?_
    have h1 := h0.push (ci := .thmInfo cv) (hA.free hf)
    intro s r s' hr
    rw [checkThmVal_result mode A cv v s r s' hr]
    exact h1
  | opaqueDecl cv v =>
    simp only [checkDecl]
    refine Post.bind (checkConstantVal_free mode A cv) fun _ hf => ?_
    refine Post.bind (checkOpaqueVal_result mode A cv v) fun _ hr => ?_
    subst hr
    have h1 := h0.push (ci := .axiomInfo cv) (hA.free hf)
    post_walk
  | axiomDecl cv =>
    simp only [checkDecl]
    refine Post.bind (Post.any _) fun _ _ => ?_
    split
    · post_walk
    · refine Post.bind (checkConstantVal_free mode A cv) fun _ hf => ?_
      have h1 := h0.push (ci := .axiomInfo cv) (hA.free hf)
      post_walk
  | basisDecl kind => exact checkBasisDecl_ext hA kind
  | quotDecl k cv =>
    simp only [checkDecl]
    refine Post.bind (Post.any _) fun _ _ => ?_
    split
    · split
      · exact checkBasisDecl_ext hA .quotK
      all_goals exact Post.pure h0
    · exact Post.fail

/-- **`installStepGo`, before the promotion**, on what phase A sends it. -/
theorem installStepGo_ext {A : IFEnv} (hA : EnvOK A) (mode : ConLeche.CheckMode)
    (pins : List INatOpPinSet) (d : IDeclaration) (hd : ∀ b n, d ≠ .indDecl b n) :
    Post (installStepGo mode pins A d) (fun p => EnvExt A p.1) := by
  have h0 := EnvExt.refl hA
  have hod : ∀ d' : IDeclaration, (∀ b n, d' ≠ .indDecl b n) →
      Post (do pure (← checkDecl mode pins A d', (none : Option ValueGroup)))
        (fun p => EnvExt A p.1) := fun d' h' =>
    Post.bind (checkDecl_ext hA mode pins d' h') fun _ h => Post.pure h
  cases d with
  | indDecl b n => exact absurd rfl (hd b n)
  | defnDecl cv v hint =>
    simp only [installStepGo]
    refine Post.bind (Post.any _) fun _ _ => ?_
    refine Post.bind (Post.any _) fun _ _ => ?_
    split
    · exact hod _ hd
    · refine Post.bind (installHeader_free A cv) fun _ hf => ?_
      refine Post.bind (Post.any _) fun _ _ => ?_
      exact Post.pure (h0.push (hA.free hf))
  | thmDecl cv v =>
    simp only [installStepGo]
    refine Post.bind (installHeader_free A cv) fun _ hf => ?_
    exact Post.pure (h0.push (hA.free hf))
  | opaqueDecl cv v =>
    simp only [installStepGo]
    refine Post.bind (Post.any _) fun _ _ => ?_
    split
    · exact hod _ hd
    · refine Post.bind (installHeader_free A cv) fun _ hf => ?_
      refine Post.bind (Post.any _) fun _ _ => ?_
      exact Post.pure (h0.push (hA.free hf))
  | axiomDecl cv => exact hod _ hd
  | basisDecl kind => exact hod _ hd
  | quotDecl k cv => exact hod _ hd

end ConRon.Refine2
