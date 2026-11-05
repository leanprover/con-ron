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

/-! ## A block read as stored -/

theorem Post.scratchRun {α : Type} {c : AM α} {Q : α → Prop} (h : Post c Q) :
    Post (Arena.scratchRun c) Q := by
  intro s r s' hr
  unfold Arena.scratchRun at hr
  cases hc : c s with
  | error e => simp [hc] at hr
  | ok p =>
    obtain ⟨a, s1⟩ := p
    simp only [hc] at hr
    split at hr
    · cases hr; exact h s _ s1 hc
    · cases hr

theorem storedTry_post {α β : Type} {run : AM α} {keep : α → AM β} {Q : β → Prop}
    (hk : ∀ a, Post (keep a) Q) :
    Post (storedTry run keep) (fun o => ∀ b, o = some b → Q b) := by
  unfold storedTry
  refine Post.bind (Post.any _) fun _ _ => ?_
  refine Post.bind (Post.any _) fun _ _ => ?_
  intro s r s' hr
  dsimp only at hr
  split at hr
  · refine Post.bind (hk _) (fun b hb => Post.bind (Post.any _) fun _ _ =>
      Post.pure (Q := fun o => ∀ b', o = some b' → Q b') ?_) _ r s' hr
    intro b' h
    cases h
    exact hb
  · refine Post.bind (Post.any _) (fun _ _ =>
      Post.pure (Q := fun o => ∀ b', o = some b' → Q b') ?_) _ r s' hr
    intro b' h
    cases h

/-- A former read keeps its record's name. -/
theorem storedTele_name (mode : ConLeche.CheckMode) (fe : IFEnv) (cv : IConstantVal) (n : Nat) :
    Post (storedTele mode fe cv n) (fun o => ∀ x, o = some x → x.1.name = cv.name) := by
  have hslow : Post (storedTry (storedTeleRun mode fe cv n) fun q => do
        let (m, ty) ← promoteE PMemo.empty coreWalkFuel q.1
        let (_, s) ← promoteL m coreWalkFuel q.2
        pure (({ cv with type := ty } : IConstantVal), s))
      (fun o => ∀ x, o = some x → x.1.name = cv.name) :=
    storedTry_post (Q := fun x : IConstantVal × LIdx => x.1.name = cv.name) (by
      intro q
      refine Post.bind (Post.any _) fun p _ => ?_
      obtain ⟨m, ty⟩ := p
      refine Post.bind (Post.any _) fun p' _ => ?_
      obtain ⟨_, s⟩ := p'
      exact Post.pure rfl)
  unfold storedTele
  dsimp only
  refine Post.bind (Post.any _) fun o _ => ?_
  split
  · split
    · refine Post.bind (Post.any _) fun v _ => ?_
      split
      · exact Post.fail
      · exact Post.pure (by intro x h; cases h; rfl)
    · exact hslow
  · exact hslow

/-- The formers read carry the members' names, in order. -/
theorem storedFormers_names (mode : ConLeche.CheckMode) (fe : IFEnv) (nP : Nat) :
    ∀ (ms : List MemberShape) (i : Nat) (out : List IConstantVal) (s0 : LIdx),
      Post (storedFormers mode fe nP ms i out s0)
        (fun r => r.1.map (·.name) = out.reverse.map (·.name) ++ ms.map (·.cvT.name))
  | [], _, out, _ => by
    rw [storedFormers]
    exact Post.pure (by simp)
  | m :: rest, i, out, s0 => by
    rw [storedFormers]
    refine Post.bind (storedTele_name mode fe m.cvT _) fun o ho => ?_
    split
    · rename_i cv s
      refine fun st r st' hr => ?_
      have := storedFormers_names mode fe nP rest _ _ _ st r st' hr
      dsimp only at this ⊢
      rw [this]
      have hn : cv.name = m.cvT.name := ho (cv, s) rfl
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, hn]
    · refine fun st r st' hr => ?_
      have := storedFormers_names mode fe nP rest _ _ _ st r st' hr
      dsimp only at this ⊢
      rw [this]
      simp

/-- **Past the names' test**: an extension of `A`, whose structures have their rows. -/
structure ExtR (A : IFEnv) (T0 : List NIdx) (b : IFEnv) : Prop where
  ext : EnvExt A b
  rows : ∀ T ∈ T0, (b.idx[T]?).isSome

theorem ExtR.push {A : IFEnv} {T0 : List NIdx} {b : IFEnv} (h : ExtR A T0 b) {ci : IConstantInfo}
    (hfree : A.idx[ci.name]? = none) : ExtR A T0 (b.push ci) := by
  refine ⟨h.ext.push hfree, fun T hT => ?_⟩
  have := h.rows T hT
  simp only [IFEnv.push, Std.HashMap.getElem?_insert]
  split <;> simp_all

theorem consBlockInds_ext {A : IFEnv} (p : BlockShape) (isRec : Bool) :
    ∀ (cvs : List IConstantVal) (i : Nat) (T0 : List NIdx) (b : IFEnv), ExtR A T0 b →
      (∀ cv ∈ cvs, A.idx[cv.name]? = none) →
      Post (consBlockInds p isRec cvs i b) (ExtR A (cvs.map (·.name) ++ T0))
  | [], _, _, b, h, _ => by
    rw [consBlockInds]
    exact Post.pure h
  | cv :: rest, i, T0, b, h, hf => by
    rw [consBlockInds]
    refine Post.bind (Post.any _) fun caps _ => ?_
    have h1 : ExtR A (cv.name :: T0) (b.push (.indInfo cv caps)) := by
      refine ⟨h.ext.push (hf cv (by simp)), fun T hT => ?_⟩
      rcases List.mem_cons.mp hT with rfl | hT
      · have hn : (IConstantInfo.indInfo cv caps).name = cv.name := rfl
        simp [IFEnv.push, hn]
      · exact (h.push (ci := .indInfo cv caps) (hf cv (by simp))).rows T hT
    refine fun st r st' hr => ?_
    have h2 := consBlockInds_ext p isRec rest (i + 1) _ _ h1
      (fun c hc => hf c (List.mem_cons_of_mem _ hc)) st r st' hr
    refine ⟨h2.ext, fun T hT => h2.rows T ?_⟩
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hT ⊢
    grind

theorem consSumCtors_ext {A : IFEnv} {T0 : List NIdx} (nP : Nat) :
    ∀ (cs : List (IConstantVal × Nat)) (b : IFEnv), ExtR A T0 b →
      (∀ c ∈ cs, A.idx[c.1.name]? = none) → ExtR A T0 (consSumCtors nP cs b)
  | [], _, h, _ => h
  | c :: cs, b, h, hf =>
    consSumCtors_ext nP cs _ (h.push (ci := .ctorInfo c.1 nP c.2) (hf c (by simp)))
      (fun x hx => hf x (List.mem_cons_of_mem _ hx))

theorem storedCtors_ext {A : IFEnv} {T0 : List NIdx} (nP : Nat) :
    ∀ (ms : List MemberShape) (b : IFEnv), ExtR A T0 b →
      (∀ m ∈ ms, ∀ c ∈ m.ctors, A.idx[c.1.name]? = none) → ExtR A T0 (storedCtors nP ms b)
  | [], _, h, _ => h
  | m :: rest, b, h, hf =>
    storedCtors_ext nP rest _ (consSumCtors_ext nP m.ctors b h (hf m (by simp)))
      (fun x hx => hf x (List.mem_cons_of_mem _ hx))

theorem storedRecs_ext {A : IFEnv} {T0 : List NIdx} (vis₂ : Nat) (p : BlockShape) :
    ∀ (rcs : List RecShape) (r : Nat) (b : IFEnv), ExtR A T0 b →
      (∀ rc ∈ rcs, A.idx[rc.cvR.name]? = none) →
      Post (storedRecs vis₂ p r rcs b) (ExtR A T0)
  | [], _, _, h, _ => by
    rw [storedRecs]
    exact Post.pure h
  | rc :: rest, r, b, h, hf => by
    rw [storedRecs]
    have hfr := hf rc (by simp)
    have hfs : ∀ x ∈ rest, A.idx[x.cvR.name]? = none :=
      fun x hx => hf x (List.mem_cons_of_mem _ hx)
    refine Post.bind (Post.any _) fun _ _ => ?_
    split
    · exact storedRecs_ext vis₂ p rest _ _ (h.push hfr) hfs
    · refine Post.bind (Post.any _) fun rules _ => ?_
      exact storedRecs_ext vis₂ p rest _ _ (h.push hfr) hfs

theorem storedTables_ext {A : IFEnv} {T0 : List NIdx} (hA : EnvOK A) (p : BlockShape) :
    ∀ (ms : List MemberShape) (gs : List (List LIdx)) (b : IFEnv), ExtR A T0 b →
      (∀ m ∈ ms, m.cvT.name ∈ T0 ∧ A.idx[m.cvT.name]? = none) →
      Post (storedTables p ms gs b) (ExtR A T0)
  | [], _, _, h, _ => by
    rw [storedTables]
    exact Post.pure h
  | m :: rest, gs, b, h, hf => by
    rw [storedTables]
    have hfs : ∀ x ∈ rest, x.cvT.name ∈ T0 ∧ A.idx[x.cvT.name]? = none :=
      fun x hx => hf x (List.mem_cons_of_mem _ hx)
    obtain ⟨hm, hfm⟩ := hf m (by simp)
    split
    · split
      · refine Post.bind (Post.any _) fun _ _ => ?_
        split
        · exact storedTables_ext hA p rest _ _
            ⟨h.ext.pushTable hA hfm (h.rows _ hm), h.rows⟩ hfs
        · exact storedTables_ext hA p rest _ _ h hfs
      · exact storedTables_ext hA p rest _ _ h hfs
    · exact storedTables_ext hA p rest _ _ h hfs

/-- **What a block's names' test gives**: every name it pushes free in `A`. -/
structure BlockFree (A : IFEnv) (p : BlockShape) : Prop where
  members : ∀ m ∈ p.members, A.idx[m.cvT.name]? = none
  ctors : ∀ m ∈ p.members, ∀ c ∈ m.ctors, A.idx[c.1.name]? = none
  recs : ∀ rc ∈ p.recs, A.idx[rc.cvR.name]? = none

/-- The pushes of `storedTail`, before its promotion. -/
theorem storedTail_pushes {A : IFEnv} (hA : EnvOK A) (p : BlockShape) (guards : List (List LIdx))
    (hf : BlockFree A p) {fe₁ : IFEnv} (h : ExtR A (p.members.map (·.cvT.name)) fe₁) :
    Post (do
        let fe₂ := storedCtors p.nP p.members fe₁
        let vis₂ := fe₂.visibleBelow
        let fe₃ ← storedRecs vis₂ p 0 p.recs fe₂
        storedTables p p.members guards fe₃ : AM IFEnv)
      (ExtR A (p.members.map (·.cvT.name))) := by
  dsimp only
  refine Post.bind (storedRecs_ext _ p p.recs 0 _ (storedCtors_ext p.nP p.members fe₁ h hf.ctors)
    hf.recs) fun _ h' => ?_
  exact storedTables_ext hA p p.members guards _ h'
    (fun m hm => ⟨List.mem_map_of_mem hm, hf.members m hm⟩)

/-! ## The promotion, at a name that does not move

The twin's `promoteNew` re-keys what it promotes, under the promoted names.  The fact
that those are the names it started from is the Rust's (`index_promoted`,
`promote_installed_tables` assert it), so it is a hypothesis here, which the lockstep
theorem of each bracket discharges. -/

theorem eraseInstalled_get (n : NIdx) : ∀ (cs : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)),
    (∀ c ∈ cs, c.name ≠ n) → (eraseInstalled idx cs)[n]? = idx[n]?
  | [], _, _ => rfl
  | c :: cs, idx, h => by
    simp only [eraseInstalled]
    rw [eraseInstalled_get n cs _ (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      Std.HashMap.getElem?_erase]
    have : (c.name == n) = false := by
      rw [beq_eq_false_iff_ne]; exact h c (by simp)
    simp [this]

theorem indexPromoted_other (n : NIdx) : ∀ (L : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (c : Nat),
    (∀ x ∈ L, x.name ≠ n) → (indexPromoted idx c L)[n]? = idx[n]?
  | [], _, _, _ => rfl
  | x :: xs, idx, c, h => by
    simp only [indexPromoted]
    rw [indexPromoted_other n xs _ _ (fun y hy => h y (List.mem_cons_of_mem _ hy)),
      Std.HashMap.getElem?_insert]
    have : (x.name == n) = false := by
      rw [beq_eq_false_iff_ne]; exact h x (by simp)
    simp [this]

theorem indexPromoted_mem (n : NIdx) : ∀ (L : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (c : Nat), L.length ≤ c →
    (∃ x ∈ L, x.name = n) →
      ((indexPromoted idx c L)[n]?).isSome ∧
      ∀ r, (indexPromoted idx c L)[n]? = some r → c - L.length ≤ r.1 ∧ r.1 < c
  | [], _, _, _, ⟨_, hx, _⟩ => by simp at hx
  | x :: xs, idx, c, hl, hm => by
    simp only [indexPromoted]
    simp only [List.length_cons] at hl ⊢
    by_cases hin : ∃ y ∈ xs, y.name = n
    · obtain ⟨h1, h2⟩ := indexPromoted_mem n xs (idx.insert x.name (c - 1, x)) (c - 1)
        (by omega) hin
      exact ⟨h1, fun r hr => by have := h2 r hr; omega⟩
    · have hne : ∀ y ∈ xs, y.name ≠ n := fun y hy he => hin ⟨y, hy, he⟩
      have hxn : x.name = n := by
        obtain ⟨y, hy, he⟩ := hm
        rcases List.mem_cons.mp hy with rfl | hy
        · exact he
        · exact absurd he (hne y hy)
      rw [indexPromoted_other n xs _ _ hne, hxn, Std.HashMap.getElem?_insert_self]
      refine ⟨rfl, fun r hr => ?_⟩
      cases hr
      simp only
      omega

theorem eraseInstalledTables_get (n : NIdx) : ∀ (ts : List IProjTable)
    (tb : Std.HashMap NIdx IProjTable),
    (∀ t ∈ ts, t.structName ≠ n) → (eraseInstalledTables tb ts)[n]? = tb[n]?
  | [], _, _ => rfl
  | t :: ts, tb, h => by
    simp only [eraseInstalledTables]
    rw [eraseInstalledTables_get n ts _ (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      Std.HashMap.getElem?_erase]
    have : (t.structName == n) = false := by
      rw [beq_eq_false_iff_ne]; exact h t (by simp)
    simp [this]

theorem indexPromotedTables_other (n : NIdx) : ∀ (L : List IProjTable)
    (tb : Std.HashMap NIdx IProjTable),
    (∀ x ∈ L, x.structName ≠ n) → (indexPromotedTables tb L)[n]? = tb[n]?
  | [], _, _ => rfl
  | x :: xs, tb, h => by
    simp only [indexPromotedTables, Std.HashMap.getElem?_insert]
    have : (x.structName == n) = false := by
      rw [beq_eq_false_iff_ne]; exact h x (by simp)
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact indexPromotedTables_other n xs tb (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- What `promoteNewConsts` does to an environment that pushed `new` above `below`. -/
theorem promoteNewConsts_shape {m : PMemo} {fuel k : Nat} {b : IFEnv}
    {new below : List IConstantInfo} (he : b.env.consts = new ++ below) (hl : new.length = k) :
    Post (promoteNewConsts m fuel k b) (fun p =>
      ∃ inst : List IConstantInfo,
        p.2.env.consts = inst ++ below ∧ p.2.env.tables = b.env.tables ∧
        p.2.visibleBelow = b.visibleBelow ∧ p.2.tbls = b.tbls ∧
        (new = [] ∧ inst = [] ∧ p.2.idx = b.idx ∨
          p.2.idx = indexPromoted (eraseInstalled b.idx new) b.visibleBelow inst)) := by
  obtain ⟨⟨consts, tables⟩, idx, vb, tbls⟩ := b
  dsimp only at he
  subst he
  rw [promoteNewConsts]
  by_cases h0 : k = 0
  · subst h0
    have hn : new = [] := List.eq_nil_of_length_eq_zero hl
    subst hn
    simp only [BEq.rfl, ↓reduceIte]
    exact Post.pure ⟨[], by simp, rfl, rfl, rfl, Or.inl (by simp)⟩
  · have hk : (k == 0) = false := by simpa using h0
    simp only [hk, Bool.false_eq_true, ↓reduceIte]
    have ht : (new ++ below).take k = new := by
      rw [← hl]; simp
    have hd : (new ++ below).drop k = below := by
      rw [← hl]; simp
    rw [ht, hd]
    refine Post.bind (Post.any _) fun q _ => ?_
    obtain ⟨m', inst⟩ := q
    exact Post.pure ⟨inst, rfl, rfl, rfl, rfl, Or.inr rfl⟩

/-- What `promoteNewTables` does likewise. -/
theorem promoteNewTables_shape {m : PMemo} {fuel k : Nat} {b : IFEnv}
    {new below : List IProjTable} (he : b.env.tables = new ++ below) (hl : new.length = k) :
    Post (promoteNewTables m fuel k b) (fun p =>
      ∃ inst : List IProjTable,
        p.2.env.tables = inst ++ below ∧ p.2.env.consts = b.env.consts ∧
        p.2.visibleBelow = b.visibleBelow ∧ p.2.idx = b.idx ∧
        (new = [] ∧ inst = [] ∧ p.2.tbls = b.tbls ∨
          p.2.tbls = indexPromotedTables (eraseInstalledTables b.tbls new) inst)) := by
  obtain ⟨⟨consts, tables⟩, idx, vb, tbls⟩ := b
  dsimp only at he
  subst he
  rw [promoteNewTables]
  by_cases h0 : k = 0
  · subst h0
    have hn : new = [] := List.eq_nil_of_length_eq_zero hl
    subst hn
    simp only [BEq.rfl, ↓reduceIte]
    exact Post.pure ⟨[], by simp, rfl, rfl, rfl, Or.inl (by simp)⟩
  · have hk : (k == 0) = false := by simpa using h0
    simp only [hk, Bool.false_eq_true, ↓reduceIte]
    have ht : (new ++ below).take k = new := by
      rw [← hl]; simp
    have hd : (new ++ below).drop k = below := by
      rw [← hl]; simp
    rw [ht, hd]
    refine Post.bind (Post.any _) fun q _ => ?_
    obtain ⟨m', inst⟩ := q
    exact Post.pure ⟨inst, rfl, rfl, rfl, rfl, Or.inr rfl⟩

/-- **The promotion keeps the extension**, at names that did not move. -/
theorem EnvExt.promoteNew {a b c : IFEnv} (h : EnvExt a b) (ha : EnvOK a) {m m' : PMemo}
    {fuel k kt : Nat} {s s' : AState}
    (hk : k = b.visibleBelow - a.visibleBelow)
    (hkt : kt = b.env.tables.length - a.env.tables.length)
    (hrun : Arena.promoteNew m fuel k kt b s = .ok ((m', c), s'))
    (hnc : c.env.consts.map (·.name) = b.env.consts.map (·.name))
    (hnt : c.env.tables.map (·.structName) = b.env.tables.map (·.structName)) :
    EnvExt a c := by
  obtain ⟨new, e₁, l₁, f₁⟩ := h.newC
  obtain ⟨newT, g₁, q₁⟩ := h.newT
  have hlT : newT.length = kt := by
    rw [hkt, g₁]; simp
  have hrun' : (Arena.promoteNewConsts m fuel k b >>= fun p =>
      Arena.promoteNewTables p.1 fuel kt p.2) s = .ok ((m', c), s') := by
    have := hrun
    rw [Arena.promoteNew] at this
    exact this
  -- the two stages
  have hstage : ∃ b' : IFEnv, ∃ m₁ s₁,
      Arena.promoteNewConsts m fuel k b s = .ok ((m₁, b'), s₁) ∧
      Arena.promoteNewTables m₁ fuel kt b' s₁ = .ok ((m', c), s') := by
    cases h1 : Arena.promoteNewConsts m fuel k b s with
    | error e =>
      have hx : (Arena.promoteNewConsts m fuel k b s >>= fun p =>
          Arena.promoteNewTables p.1.1 fuel kt p.1.2 p.2) = .ok ((m', c), s') := hrun'
      rw [h1] at hx; cases hx
    | ok p =>
      obtain ⟨⟨m₁, b'⟩, s₁⟩ := p
      have hx : (Arena.promoteNewConsts m fuel k b s >>= fun p =>
          Arena.promoteNewTables p.1.1 fuel kt p.1.2 p.2) = .ok ((m', c), s') := hrun'
      rw [h1] at hx
      exact ⟨b', m₁, s₁, rfl, hx⟩
  obtain ⟨b', m₁, s₁, h1, h2⟩ := hstage
  obtain ⟨inst, c1, c2, c3, c4, c5⟩ :=
    promoteNewConsts_shape e₁ (by rw [hk, l₁]) _ _ _ h1
  dsimp only at c1 c2 c3 c4 c5
  obtain ⟨instT, d1, d2, d3, d4, d5⟩ :=
    promoteNewTables_shape (b := b') (by rw [c2]; exact g₁) hlT _ _ _ h2
  dsimp only at d1 d2 d3 d4 d5
  have hinst : inst.map (·.name) = new.map (·.name) := by
    have := hnc
    rw [d2, c1, e₁, List.map_append, List.map_append] at this
    exact List.append_cancel_right this
  have hinstT : instT.map (·.structName) = newT.map (·.structName) := by
    have := hnt
    rw [d1, g₁, List.map_append, List.map_append] at this
    exact List.append_cancel_right this
  have hmemN : ∀ n : NIdx, (∃ x ∈ inst, x.name = n) ↔ (∃ x ∈ new, x.name = n) := by
    intro n
    have e : ∀ L : List IConstantInfo, (∃ x ∈ L, x.name = n) ↔ n ∈ L.map (·.name) := by
      intro L; simp
    rw [e, e, hinst]
  have hmemT : ∀ n : NIdx, (∃ x ∈ instT, x.structName = n) ↔ (∃ x ∈ newT, x.structName = n) := by
    intro n
    have e : ∀ L : List IProjTable, (∃ x ∈ L, x.structName = n) ↔ n ∈ L.map (·.structName) := by
      intro L; simp
    rw [e, e, hinstT]
  -- the index, row by row
  have hother : ∀ n : NIdx, (∀ x ∈ new, x.name ≠ n) → c.idx[n]? = b.idx[n]? := by
    intro n hn
    rw [d4]
    rcases c5 with ⟨-, -, hi⟩ | hi
    · rw [hi]
    · rw [hi, indexPromoted_other n inst _ _ (fun x hx he =>
        (by obtain ⟨y, hy, hyn⟩ := (hmemN n).mp ⟨x, hx, he⟩; exact hn y hy hyn)),
        eraseInstalled_get n new _ hn]
  have hlen : new.length ≤ b.visibleBelow := by rw [l₁]; omega
  have hmem : ∀ n : NIdx, (∃ x ∈ new, x.name = n) →
      (c.idx[n]?).isSome ∧ ∀ r, c.idx[n]? = some r →
        a.visibleBelow ≤ r.1 ∧ r.1 < b.visibleBelow := by
    intro n hn
    rw [d4]
    rcases c5 with ⟨hnil, -, -⟩ | hi
    · subst hnil; obtain ⟨_, hx, _⟩ := hn; simp at hx
    · have hil : inst.length = new.length := by
        have := congrArg List.length hinst; simpa using this
      rw [hi]
      obtain ⟨h3, h4⟩ := indexPromoted_mem n inst (eraseInstalled b.idx new) b.visibleBelow
        (by omega) ((hmemN n).mpr hn)
      refine ⟨h3, fun r hr => ?_⟩
      have := h4 r hr
      have hvb := h.vb
      omega
  have hisSome : ∀ n : NIdx, (b.idx[n]?).isSome → (c.idx[n]?).isSome := by
    intro n hn
    by_cases hm : ∃ x ∈ new, x.name = n
    · exact (hmem n hm).1
    · rw [hother n (fun x hx he => hm ⟨x, hx, he⟩)]; exact hn
  -- the tables, row by row
  have htother : ∀ n : NIdx, (∀ x ∈ newT, x.structName ≠ n) → c.tbls[n]? = b.tbls[n]? := by
    intro n hn
    rcases d5 with ⟨-, -, hi⟩ | hi
    · rw [hi, c4]
    · rw [hi, indexPromotedTables_other n instT _ (fun x hx he =>
        (by obtain ⟨y, hy, hyn⟩ := (hmemT n).mp ⟨x, hx, he⟩; exact hn y hy hyn)),
        eraseInstalledTables_get n newT _ hn, c4]
  have hvbc : c.visibleBelow = b.visibleBelow := by rw [d3, c3]
  have hfreeN : ∀ n : NIdx, (∃ x ∈ new, x.name = n) → a.idx[n]? = none := by
    rintro n ⟨x, hx, rfl⟩; exact f₁ x hx
  have hfreeT : ∀ n : NIdx, (∃ x ∈ newT, x.structName = n) →
      a.idx[n]? = none ∧ (c.idx[n]?).isSome := by
    rintro n ⟨x, hx, rfl⟩
    exact ⟨(q₁ x hx).1, hisSome _ (q₁ x hx).2⟩
  refine ⟨⟨inst, by rw [d2, c1], ?_, ?_⟩, ⟨instT, d1, ?_⟩, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · have := congrArg List.length hinst
    simp only [List.length_map] at this
    rw [this, l₁, hvbc]
  · intro x hx
    exact hfreeN _ ((hmemN _).mp ⟨x, hx, rfl⟩)
  · intro x hx
    exact hfreeT _ ((hmemT _).mp ⟨x, hx, rfl⟩)
  · rw [hvbc]; exact h.vb
  · intro n r hr
    rw [hother n (fun x hx he => by
      have := f₁ x hx; rw [he, hr] at this; cases this)]
    exact h.idxOld n r hr
  · intro n r hr hn
    by_cases hm : ∃ x ∈ new, x.name = n
    · exact ((hmem n hm).2 r hr).1
    · rw [hother n (fun x hx he => hm ⟨x, hx, he⟩)] at hr
      exact h.idxNew n r hr hn
  · intro T t ht
    rw [htother T (fun x hx he => by
      have h3 := (q₁ x hx).1
      have h4 := ha.tblRow T t ht
      rw [he, h3] at *
      cases h4)]
    exact h.tblOld T t ht
  · intro T t ht hn
    by_cases hm : ∃ x ∈ newT, x.structName = T
    · exact (hfreeT T hm).1
    · rw [htother T (fun x hx he => hm ⟨x, hx, he⟩)] at ht
      exact h.tblNew T t ht hn
  · intro n r hr
    rw [hvbc]
    by_cases hm : ∃ x ∈ new, x.name = n
    · exact ((hmem n hm).2 r hr).2
    · rw [hother n (fun x hx he => hm ⟨x, hx, he⟩)] at hr
      exact h.ok.rows n r hr
  · intro T t ht
    by_cases hm : ∃ x ∈ newT, x.structName = T
    · exact (hfreeT T hm).2
    · rw [htother T (fun x hx he => hm ⟨x, hx, he⟩)] at ht
      exact hisSome T (h.ok.tblRow T t ht)

end ConRon.Refine2
