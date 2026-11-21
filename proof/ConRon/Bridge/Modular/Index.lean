/-
# `ConRon.Bridge.Modular.Index` — the name index and its clashes, Theorem 1 (task #166)

The pure parts of the worker's reads: **the twin's name index is upstream's**, read back
(`nameIndexOf_rel`), and so are the doubly held names with their copies (`clashCopies_rel`): the
twin lists each name's entry by its position in its list, upstream keeps a table of the copies
beside the names' order (`ccOrderStep`), and both list the names in the order of their second
copies.  `denoteN` is injective on a well formed store, so a lookup by handle answers as the
lookup by name (`HMRel.get`).  Plain list and fold induction, not `vcgen`.
-/
module

public import ConRon.Bridge.Modular.ReadsParts
import Std.Data.HashMap.Lemmas

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConLeche.Frontend.Olean (Copy)

/-- A fold over related lists, from related starts, by related steps. -/
theorem foldl_rel {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {f : γ → α → γ}
    {g : δ → β → δ} (hstep : ∀ a b x y, R a b → S x y → S (f x a) (g y b)) :
    ∀ {l : List α} {l' : List β}, ListRel R l l' → ∀ x y, S x y → S (l.foldl f x) (l'.foldl g y)
  | _, _, .nil, _, _, h => h
  | _, _, .cons hr t, x, y, h => foldl_rel hstep t _ _ (hstep _ _ x y hr h)

theorem _root_.ConRon.Bridge.Frontend.Olean.HMRel.empty' {α : Type} (st : EStore) (n : Nat) :
    HMRel (· = ·) st ({} : Std.HashMap NIdx α)
      (Std.HashMap.emptyWithCapacity n : Std.HashMap ConLeche.Name α) :=
  ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩

/-- A membership test answers alike. -/
theorem _root_.ConRon.Bridge.Frontend.Olean.HMRel.contains_eq {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap NIdx α} {MC : Std.HashMap ConLeche.Name β} (h : HMRel R st M MC) {x : NIdx}
    {n : ConLeche.Name} (hd : denoteN st.ns x = some n) : M.contains x = MC.contains n := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?]
  rcases optRel_cases (h.get hw hd) with ⟨h1, h2⟩ | ⟨a, b, h1, h2, -⟩
  · simp [h1, h2]
  · simp [h1, h2]

theorem _root_.ConRon.Bridge.Frontend.Olean.HMRel.ext' {α β : Type} {R : α → β → Prop} {st st' : EStore} {M : Std.HashMap NIdx α}
    {MC : Std.HashMap ConLeche.Name β} (h : HMRel R st M MC) (hx : Ext st st') : HMRel R st' M MC :=
  h.ext hx (fun _ _ h => h)

theorem IndexRel.ext' {st st' : EStore} {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (h : IndexRel st ix ixC) (hx : Ext st st') :
    IndexRel st' ix ixC :=
  ⟨listRel_ext (fun _ _ hp => hp.ext hx) h.parts, h.first.ext' hx,
    listRel_ext (fun _ _ hq => ⟨denoteN_ext hq.1 hx, hq.2⟩) h.more⟩

/-- con-leche: none — one later copy read back. -/
@[expose] def MoreR (st : EStore) (a : NIdx × Copy) (b : ConLeche.Name × Copy) : Prop :=
  denoteN st.ns a.1 = some b.1 ∧ a.2 = b.2

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:55-66 nameIndexOf — the twin's inner step. -/
@[expose] def twinIxInner (i : Nat) (acc : Std.HashMap NIdx Copy × Array (NIdx × Copy) × Nat)
    (q : ConRon.Arena.Frontend.Olean.NamePosition) : Std.HashMap NIdx Copy × Array (NIdx × Copy) × Nat :=
  if acc.1.contains q.name then (acc.1, acc.2.1.push (q.name, ⟨i, acc.2.2⟩), acc.2.2 + 1)
  else (acc.1.insert q.name ⟨i, acc.2.2⟩, acc.2.1, acc.2.2 + 1)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:55-66 nameIndexOf — the twin's outer step. -/
@[expose] def twinIxOuter (acc : Std.HashMap NIdx Copy × Array (NIdx × Copy) × Nat)
    (p : ConRon.Arena.Frontend.Olean.NamePositions) : Std.HashMap NIdx Copy × Array (NIdx × Copy) × Nat :=
  let r := p.consts.toList.foldl (twinIxInner acc.2.2) (acc.1, acc.2.1, 0)
  (r.1, r.2.1, acc.2.2 + 1)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:55-66 nameIndexOf — upstream's inner step. -/
@[expose] def upIxInner (i : Nat)
    (acc : Std.HashMap ConLeche.Name Copy × Array (ConLeche.Name × Copy) × Nat)
    (q : ConLeche.Frontend.Olean.NamePosition) :
    Std.HashMap ConLeche.Name Copy × Array (ConLeche.Name × Copy) × Nat :=
  match acc.1[q.name]? with
  | none => (acc.1.insert q.name ⟨i, acc.2.2⟩, acc.2.1, acc.2.2 + 1)
  | some _ => (acc.1, acc.2.1.push (q.name, ⟨i, acc.2.2⟩), acc.2.2 + 1)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:55-66 nameIndexOf — upstream's outer step. -/
@[expose] def upIxOuter (acc : Std.HashMap ConLeche.Name Copy × Array (ConLeche.Name × Copy) × Nat)
    (p : ConLeche.Frontend.Olean.NamePositions) :
    Std.HashMap ConLeche.Name Copy × Array (ConLeche.Name × Copy) × Nat :=
  let r := p.consts.toList.foldl (upIxInner acc.2.2) (acc.1, acc.2.1, 0)
  (r.1, r.2.1, acc.2.2 + 1)

theorem nameIndexOf_eq (ps : Array ConRon.Arena.Frontend.Olean.NamePositions) :
    ConRon.Arena.Frontend.Olean.nameIndexOf ps =
      { parts := ps, first := (ps.toList.foldl twinIxOuter ({}, #[], 0)).1,
        more := (ps.toList.foldl twinIxOuter ({}, #[], 0)).2.1 } := by
  unfold ConRon.Arena.Frontend.Olean.nameIndexOf
  simp only [← Array.foldl_toList]
  delta twinIxOuter twinIxInner
  rfl

theorem nameIndexOf_eqC (ps : Array ConLeche.Frontend.Olean.NamePositions) :
    ConLeche.Frontend.Olean.nameIndexOf ps =
      { parts := ps, first := (ps.toList.foldl upIxOuter
          (Std.HashMap.emptyWithCapacity (ps.toList.foldl (fun n p => n + p.consts.size) 0), #[], 0)).1,
        more := (ps.toList.foldl upIxOuter
          (Std.HashMap.emptyWithCapacity (ps.toList.foldl (fun n p => n + p.consts.size) 0), #[], 0)).2.1 } := by
  unfold ConLeche.Frontend.Olean.nameIndexOf
  simp only [← Array.foldl_toList]
  delta upIxOuter upIxInner
  rfl

/-- con-leche: none — the index's fold states, the twin's against upstream's. -/
@[expose] def IxS (st : EStore) (x : Std.HashMap NIdx Copy × Array (NIdx × Copy) × Nat)
    (y : Std.HashMap ConLeche.Name Copy × Array (ConLeche.Name × Copy) × Nat) : Prop :=
  HMRel (· = ·) st x.1 y.1 ∧ ListRel (MoreR st) x.2.1.toList y.2.1.toList ∧ x.2.2 = y.2.2

theorem ixInner_step {st : EStore} (hw : NStoreWF st.ns) (i : Nat)
    {q : ConRon.Arena.Frontend.Olean.NamePosition} {qC : ConLeche.Frontend.Olean.NamePosition}
    {a : Std.HashMap NIdx Copy × Array (NIdx × Copy) × Nat}
    {b : Std.HashMap ConLeche.Name Copy × Array (ConLeche.Name × Copy) × Nat}
    (hq : NPRel st q qC) (hab : IxS st a b) : IxS st (twinIxInner i a q) (upIxInner i b qC) := by
  obtain ⟨g1, g2, g3⟩ := hab
  have hc := g1.contains_eq hw hq.name
  unfold twinIxInner upIxInner
  cases hfc : b.1[qC.name]? with
  | none =>
    have : a.1.contains q.name = false := by
      rw [hc, Std.HashMap.contains_eq_isSome_getElem?, hfc]; rfl
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact ⟨g1.insert hw hq.name (by rw [g3]), g2, by simp [g3]⟩
  | some _ =>
    have : a.1.contains q.name = true := by
      rw [hc, Std.HashMap.contains_eq_isSome_getElem?, hfc]; rfl
    simp only [this, ↓reduceIte]
    refine ⟨g1, ?_, by simp [g3]⟩
    show ListRel (MoreR st) (a.2.1.push (q.name, ⟨i, a.2.2⟩)).toList
      (b.2.1.push (qC.name, ⟨i, b.2.2⟩)).toList
    rw [Array.toList_push, Array.toList_push, g3]
    exact listRel_append g2 (.cons ⟨hq.name, rfl⟩ .nil)

theorem ixOuter_step {st : EStore} (hw : NStoreWF st.ns)
    {p : ConRon.Arena.Frontend.Olean.NamePositions} {pC : ConLeche.Frontend.Olean.NamePositions}
    {x : Std.HashMap NIdx Copy × Array (NIdx × Copy) × Nat}
    {y : Std.HashMap ConLeche.Name Copy × Array (ConLeche.Name × Copy) × Nat}
    (hp : NPsRel st p pC) (hxy : IxS st x y) : IxS st (twinIxOuter x p) (upIxOuter y pC) := by
  obtain ⟨h1, h2, h3⟩ := hxy
  unfold twinIxOuter upIxOuter
  rw [h3]
  have hin := foldl_rel (S := IxS st) (f := twinIxInner y.2.2) (g := upIxInner y.2.2)
    (fun q qC a b hq hab => ixInner_step hw y.2.2 hq hab) hp.consts (x.1, x.2.1, 0) (y.1, y.2.1, 0)
    ⟨h1, h2, rfl⟩
  exact ⟨hin.1, hin.2.1, rfl⟩

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:55-66 nameIndexOf — **the twin's index of some
name positions is upstream's**, read back. -/
theorem nameIndexOf_rel {st : EStore} (hw : NStoreWF st.ns)
    {ps : Array ConRon.Arena.Frontend.Olean.NamePositions}
    {psC : Array ConLeche.Frontend.Olean.NamePositions}
    (h : ListRel (NPsRel st) ps.toList psC.toList) :
    IndexRel st (ConRon.Arena.Frontend.Olean.nameIndexOf ps)
      (ConLeche.Frontend.Olean.nameIndexOf psC) := by
  rw [nameIndexOf_eq, nameIndexOf_eqC]
  have hfold := foldl_rel (S := IxS st) (f := twinIxOuter) (g := upIxOuter)
    (fun p pC x y hp hxy => ixOuter_step hw hp hxy) h ({}, #[], 0)
    (Std.HashMap.emptyWithCapacity (psC.toList.foldl (fun n p => n + p.consts.size) 0), #[], 0)
    ⟨HMRel.empty' st _, .nil, rfl⟩
  exact ⟨h, hfold.1, hfold.2.1⟩

/-! ## The doubly held names -/

theorem listRel_of_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length →
      (∀ (j : Nat) (a : α) (b : β), l[j]? = some a → l'[j]? = some b → R a b) → ListRel R l l'
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', h, hr =>
    .cons (hr 0 a b rfl rfl) (listRel_of_getElem? (by simpa using h)
      fun j x y hx hy => hr (j + 1) x y (by simpa using hx) (by simpa using hy))

theorem length_filterMap_all {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome = true) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a List.mem_cons_self)
    rw [List.filterMap_cons, hb]
    simp [length_filterMap_all (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem filterMap_getElem?' {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome = true) → ∀ j : Nat,
      (l.filterMap f)[j]? = (l[j]?).bind f
  | [], _, j => by simp
  | a :: l, h, j => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a List.mem_cons_self)
    rw [List.filterMap_cons, hb]
    cases j with
    | zero => simp [hb]
    | succ j => simpa using filterMap_getElem?' (fun x hx => h x (List.mem_cons_of_mem _ hx)) j

/-- con-leche: none — one doubly held name with its copies, read back. -/
@[expose] def CCR (st : EStore) (a : NIdx × Array Copy) (b : ConLeche.Name × Array Copy) : Prop :=
  denoteN st.ns a.1 = some b.1 ∧ a.2 = b.2

/-- `clashCopies`' fold state, the twin's against upstream's: the list's entries are the names'
order with their copies in the table, and the twin's index of its list is the list's. -/
structure CCInv (st : EStore) (at_ : Std.HashMap NIdx Nat) (out : Array (NIdx × Array Copy))
    (m : Std.HashMap ConLeche.Name (Array Copy)) (order : Array ConLeche.Name) : Prop where
  size : out.size = order.size
  row : ∀ (j : Nat) (a : NIdx × Array Copy), out[j]? = some a → ∃ n, order[j]? = some n ∧
    denoteN st.ns a.1 = some n ∧ m[n]? = some a.2
  nodup : order.toList.Nodup
  table : ∀ n, m.contains n = true → n ∈ order.toList
  atRow : ∀ (h : NIdx) (k : Nat), at_[h]? = some k → ∃ a, out[k]? = some a ∧ a.1 = h
  atAll : ∀ (j : Nat) (a : NIdx × Array Copy), out[j]? = some a → at_[a.1]? = some j

theorem CCInv.empty (st : EStore) : CCInv st {} #[] {} #[] :=
  ⟨rfl, fun _ _ h => by simp at h, List.nodup_nil, fun _ h => by simp at h,
    fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩

theorem CCInv.step {st : EStore} (hw : NStoreWF st.ns) {first : Std.HashMap NIdx Copy}
    {firstC : Std.HashMap ConLeche.Name Copy} (hf : HMRel (· = ·) st first firstC)
    {at_ : Std.HashMap NIdx Nat} {out : Array (NIdx × Array Copy)}
    {m : Std.HashMap ConLeche.Name (Array Copy)} {order : Array ConLeche.Name}
    (hi : CCInv st at_ out m order) {h : NIdx} {n : ConLeche.Name} {c : Copy}
    (hd : denoteN st.ns h = some n) :
    CCInv st
      (match at_[h]? with
        | some _ => at_
        | none => at_.insert h out.size)
      (match at_[h]? with
        | some k => out.modify k fun (p : NIdx × Array Copy) => (p.1, p.2.push c)
        | none => out.push (h, #[(first[h]?).getD c, c]))
      (ConLeche.Frontend.Olean.ccStep firstC m (n, c))
      (if m.contains n then order else order.push n) := by
  unfold ConLeche.Frontend.Olean.ccStep
  dsimp only
  cases hat : at_[h]? with
  | some k =>
    -- the name has an entry: its copies grow, in the list and in the table
    obtain ⟨a, ha, rfl⟩ := hi.atRow _ _ hat
    obtain ⟨n', hn', hd', hm'⟩ := hi.row k a ha
    have e : n' = n := Option.some.inj (hd'.symm.trans hd)
    rw [e] at hn' hm'
    have hc : m.contains n = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, hm']; rfl
    simp only [hc, ↓reduceIte]
    refine ⟨by simp [hi.size], fun j b hb => ?_, hi.nodup, fun q hq => ?_, fun h' k' hk' => ?_,
      fun j b hb => ?_⟩
    · rw [Array.getElem?_modify] at hb
      split at hb
      · rename_i hkj
        subst hkj
        rw [ha] at hb
        simp only [Option.map_some, Option.some.injEq] at hb
        subst hb
        refine ⟨n, hn', hd, ?_⟩
        simp [hm']
      · rename_i hkj
        obtain ⟨q, hq, hdq, hmq⟩ := hi.row j b hb
        refine ⟨q, hq, hdq, ?_⟩
        have hqn : (n == q) = false := by
          rw [beq_eq_false_iff_ne]
          intro he
          subst he
          exact hkj (by
            have e : order.toList[k]? = order.toList[j]? := by
              simp only [Array.getElem?_toList]; rw [hn', hq]
            have hk : k < order.toList.length := by
              have := (Array.getElem?_eq_some_iff.mp hn').1; simpa using this
            exact hi.nodup.eq_of_getElem?_eq hk e)
        simp [Std.HashMap.getElem?_alter, hqn, hmq]
    · rw [Std.HashMap.contains_alter] at hq
      by_cases he : n = q
      · subst he; exact (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hn'))
      · simp only [beq_iff_eq, he, ↓reduceIte] at hq
        exact hi.table q hq
    · obtain ⟨b, hb, rfl⟩ := hi.atRow _ _ hk'
      rw [Array.getElem?_modify]
      split
      · rename_i hkj; subst hkj; rw [hb]; exact ⟨_, rfl, rfl⟩
      · exact ⟨b, hb, rfl⟩
    · rw [Array.getElem?_modify] at hb
      split at hb
      · rename_i hkj
        subst hkj
        rw [ha] at hb
        simp only [Option.map_some, Option.some.injEq] at hb
        subst hb
        exact hat
      · exact hi.atAll j b hb
  | none =>
    -- a new name: its first copy and this one, at the end of both
    have hnot : ∀ (j : Nat) (a : NIdx × Array Copy), out[j]? = some a → a.1 ≠ h := fun j a hj he => by
      have := hi.atAll j a hj
      rw [he, hat] at this
      cases this
    have hnm : m.contains n = false := by
      cases hc : m.contains n with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem (hi.table n hc)
        have hjo : j < out.size := by rw [hi.size]; simpa using hj
        obtain ⟨q, hq, hdq, -⟩ := hi.row j out[j] (by simp [hjo])
        have : q = n := by
          rw [Array.getElem?_toList.symm, List.getElem?_eq_getElem hj, hjn] at hq
          exact (Option.some.inj hq).symm
        rw [this] at hdq
        exact hnot j out[j] (by simp [hjo]) (denoteN_inj hw hdq hd)
    have hget : m[n]? = none := by
      rw [Std.HashMap.contains_eq_isSome_getElem?] at hnm
      cases hx : m[n]? with
      | none => rfl
      | some _ => rw [hx] at hnm; cases hnm
    simp only [hnm, Bool.false_eq_true, ↓reduceIte]
    have hfirst : (first[h]?).getD c = (firstC[n]?).getD c := by rw [hf.get_eq hw hd]
    refine ⟨by simp [hi.size], fun j b hb => ?_, ?_, fun q hq => ?_, fun h' k' hk' => ?_,
      fun j b hb => ?_⟩
    · rw [Array.getElem?_push] at hb
      split at hb
      · rename_i hj
        subst hj
        simp only [Option.some.injEq] at hb
        subst hb
        refine ⟨n, by simp [hi.size], hd, ?_⟩
        simp [hget, hfirst]
      · obtain ⟨q, hq, hdq, hmq⟩ := hi.row j b hb
        refine ⟨q, by rw [Array.getElem?_push]; simp [show ¬ j = order.size by
          rw [← hi.size]; exact fun e => by subst e; simp at hb]; exact hq, hdq, ?_⟩
        have hqn : (n == q) = false := by
          rw [beq_eq_false_iff_ne]
          rintro rfl
          rw [hget] at hmq; cases hmq
        simp [Std.HashMap.getElem?_alter, hqn, hmq]
    · simp only [Array.toList_push]
      refine List.nodup_append.mpr ⟨hi.nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      rintro rfl
      obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem ha
      have hjo : j < out.size := by rw [hi.size]; simpa using hj
      obtain ⟨q, hq, hdq, hmq⟩ := hi.row j out[j] (by simp [hjo])
      have : q = a := by
        rw [Array.getElem?_toList.symm, List.getElem?_eq_getElem hj, hjn] at hq
        exact (Option.some.inj hq).symm
      rw [this] at hmq
      rw [hget] at hmq; cases hmq
    · rw [Std.HashMap.contains_alter] at hq
      simp only [Array.toList_push, List.mem_append, List.mem_singleton]
      by_cases he : n = q
      · exact .inr he.symm
      · simp only [beq_iff_eq, he, ↓reduceIte] at hq
        exact .inl (hi.table q hq)
    · rw [Std.HashMap.getElem?_insert] at hk'
      split at hk'
      · rename_i he
        simp only [beq_iff_eq] at he
        subst he
        simp only [Option.some.injEq] at hk'
        subst hk'
        exact ⟨(h, #[(first[h]?).getD c, c]), by simp, rfl⟩
      · obtain ⟨b, hb, rfl⟩ := hi.atRow _ _ hk'
        refine ⟨b, ?_, rfl⟩
        rw [Array.getElem?_push]
        have : k' < out.size := by
          rcases Array.getElem?_eq_some_iff.mp hb with ⟨hk, -⟩; exact hk
        simp [show ¬ k' = out.size by omega, hb]
    · rw [Array.getElem?_push] at hb
      rw [Std.HashMap.getElem?_insert]
      split at hb
      · rename_i hj
        subst hj
        simp only [Option.some.injEq] at hb
        subst hb
        simp
      · have hne : (h == b.1) = false := by
          rw [beq_eq_false_iff_ne]
          exact fun he => hnot j b hb he.symm
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        exact hi.atAll j b hb

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:179-185 clashCopies — the twin's step. -/
@[expose] def twinCC (ix : ConRon.Arena.Frontend.Olean.NameIndex)
    (acc : Std.HashMap NIdx Nat × Array (NIdx × Array Copy)) (x : NIdx × Copy) :
    Std.HashMap NIdx Nat × Array (NIdx × Array Copy) :=
  match acc.1[x.1]? with
  | some k => (acc.1, acc.2.modify k fun (p : NIdx × Array Copy) => (p.1, p.2.push x.2))
  | none => (acc.1.insert x.1 acc.2.size, acc.2.push (x.1, #[(ix.first[x.1]?).getD x.2, x.2]))

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:179-185 clashCopies — **the twin's doubly held
names are upstream's, in the same order, each with the same copies**. -/
theorem clashCopies_rel {st : EStore} (hw : NStoreWF st.ns)
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    (h : IndexRel st ix ixC) :
    ListRel (CCR st) (ConRon.Arena.Frontend.Olean.clashCopies ix).toList
      (ConLeche.Frontend.Olean.clashCopies ixC).toList := by
  have heq : ConRon.Arena.Frontend.Olean.clashCopies ix =
      (ix.more.toList.foldl (twinCC ix) ({}, #[])).2 := by
    unfold ConRon.Arena.Frontend.Olean.clashCopies
    rw [← Array.foldl_toList]
    rfl
  have heqC : ConLeche.Frontend.Olean.clashCopies ixC =
      ((ixC.more.toList.foldl (ConLeche.Frontend.Olean.ccOrderStep ixC.first) ({}, #[])).2.filterMap
        fun n => ((ixC.more.toList.foldl (ConLeche.Frontend.Olean.ccOrderStep ixC.first)
          ({}, #[])).1[n]?).map (n, ·)) := by
    unfold ConLeche.Frontend.Olean.clashCopies
    rw [← Array.foldl_toList]
  rw [heq, heqC]
  have hfold := foldl_rel
    (S := fun (x : Std.HashMap NIdx Nat × Array (NIdx × Array Copy))
      (y : Std.HashMap ConLeche.Name (Array Copy) × Array ConLeche.Name) => CCInv st x.1 x.2 y.1 y.2)
    (f := twinCC ix) (g := ConLeche.Frontend.Olean.ccOrderStep ixC.first)
    (fun x y acc accC hxy hacc => by
      obtain ⟨at_, out⟩ := acc
      obtain ⟨n, c⟩ := x
      obtain ⟨nC, c'⟩ := y
      obtain ⟨hd, rfl⟩ := hxy
      have := CCInv.step (c := c) hw h.first hacc hd
      unfold ConLeche.Frontend.Olean.ccOrderStep
      unfold twinCC
      dsimp only at this ⊢
      cases hat : at_[n]? <;> simp only [hat] at this ⊢ <;> exact this)
    h.more ({}, #[]) ({}, #[]) (CCInv.empty st)
  generalize ix.more.toList.foldl (twinCC ix) ({}, #[]) = acc at hfold ⊢
  generalize ixC.more.toList.foldl (ConLeche.Frontend.Olean.ccOrderStep ixC.first) ({}, #[]) = accC at hfold ⊢
  obtain ⟨at_, out⟩ := acc
  obtain ⟨m, order⟩ := accC
  dsimp only at hfold ⊢
  -- every name of the order is in the table: the filter keeps every one
  have hrow : ∀ j (hj : j < order.size), ∃ a, out[j]? = some a ∧
      denoteN st.ns a.1 = some order[j] ∧ m[order[j]]? = some a.2 := by
    intro j hj
    have hjo : j < out.size := by rw [hfold.size]; exact hj
    obtain ⟨q, hq, hdq, hmq⟩ := hfold.row j out[j] (by simp [hjo])
    have : q = order[j] := by simp [hj] at hq; exact hq.symm
    rw [this] at hdq hmq
    exact ⟨out[j], by simp [hjo], hdq, hmq⟩
  have hsome : ∀ n ∈ order.toList, ((m[n]?).map (n, ·)).isSome = true := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn
    obtain ⟨a, -, -, hm⟩ := hrow j (by simpa using hj)
    simp only [Array.getElem_toList] at hm ⊢
    rw [hm]; rfl
  refine listRel_of_getElem? ?_ fun j a b ha hb => ?_
  · rw [Array.toList_filterMap, length_filterMap_all hsome]
    simp [hfold.size]
  · rw [Array.toList_filterMap, filterMap_getElem?' hsome] at hb
    have hj : j < order.size := by
      have : j < out.size := (Array.getElem?_eq_some_iff.mp (by simpa using ha)).1
      rw [← hfold.size]; exact this
    obtain ⟨a', ha', hd, hm⟩ := hrow j hj
    rw [Array.getElem?_toList] at ha
    rw [ha] at ha'
    cases ha'
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hj, Option.bind_some, hm,
      Option.map_some, Option.some.injEq] at hb
    subst hb
    exact ⟨hd, rfl⟩

/-! ## The two checks over the index -/

theorem find?_none_rel {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {l : List α} {l' : List β}, ListRel R l l' → l.find? p = none → l'.find? q = none
  | _, _, .nil, _ => rfl
  | _, _, @ListRel.cons _ _ _ a b _ _ hr t, h => by
    rw [List.find?_cons] at h ⊢
    rw [← hpq _ _ hr]
    cases hpa : p a with
    | true => rw [hpa] at h; cases h
    | false => exact find?_none_rel hpq t (by simpa [hpa] using h)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:137-146 importsModulesOk — **the twin's accept
is upstream's**, at loads, an index and imports read back. -/
theorem importsModulesOk_run {st : EStore} {m : NIdx} {mC : ConLeche.Name} {isM : Bool}
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    {imps : Array (ConLeche.Frontend.Olean.ImportF NIdx)} {impsC : Array ConLeche.Frontend.Olean.ImportRec}
    (hld : LoadsRel st ld ldC) (hix : IndexRel st ix ixC) (hi : ImpsD st imps impsC)
    {s s' : AState}
    (h : ConRon.Arena.Frontend.Olean.importsModulesOk m isM ld ix imps s = .ok ((), s')) :
    s' = s ∧ ConLeche.Frontend.Olean.importsModulesOk mC isM ldC ixC impsC = .ok () := by
  unfold ConLeche.Frontend.Olean.importsModulesOk
  cases isM with
  | false =>
    unfold ConRon.Arena.Frontend.Olean.importsModulesOk at h
    exact ⟨(AM.pure_ok h).2, rfl⟩
  | true =>
  generalize hP : ConRon.Arena.Frontend.Olean.importsModulesOk m true ld ix imps = P at h
  unfold ConRon.Arena.Frontend.Olean.importsModulesOk at hP
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hP ⊢
  split at hP
  · subst hP
    obtain ⟨e, s₁, -, h⟩ := AM.bind_ok h
    obtain ⟨e', s₂, -, h⟩ := AM.bind_ok h
    exact (AM.fail_ok h).elim
  · rename_i hf
    subst hP
    refine ⟨(AM.pure_ok h).2, ?_⟩
    have hparts : ∀ k : Nat, (ix.parts[k]?).any (fun (p : ConRon.Arena.Frontend.Olean.NamePositions) =>
        p.header.isModule) = (ixC.parts[k]?).any (fun (p : ConLeche.Frontend.Olean.NamePositions) =>
        p.header.isModule) := by
      intro k
      rw [← Array.getElem?_toList, ← Array.getElem?_toList]
      rcases optRel_cases (listRel_getElem? hix.parts k) with ⟨h1, h2⟩ | ⟨a, b, h1, h2, h3⟩
      · simp [h1, h2]
      · rw [h1, h2]; simp [h3.isModule]
    have hnone := find?_none_rel (R := fun (i : ConLeche.Frontend.Olean.ImportF NIdx) (iC : ConLeche.Frontend.Olean.ImportRec) =>
        denoteImport st i = some iC)
      (p := fun i => match ld.index[i.module]? with
        | some k => !((ix.parts[k]?).any (·.header.isModule))
        | none => false)
      (q := fun i => match ldC.index[i.module]? with
        | some k => !((ixC.parts[k]?).any (·.header.isModule))
        | none => false)
      (fun i iC hd => by
        obtain ⟨y, hy, rfl⟩ := denoteImport_eq hd
        dsimp only
        rw [hld.index _ _ hy]
        split <;> simp [hparts])
      (listRel_of_mapM hi) (by rw [← Array.find?_toList] at hf; exact hf)
    try rw [← Array.find?_toList]
    split
    · rename_i i heq
      exact absurd (List.find?_some heq) (List.find?_eq_none.mp hnone _ (List.mem_of_find?_eq_some heq))
    · rfl

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:129-135 freshOk — **the twin's accept is
upstream's**. -/
theorem freshOk_run {pk : ConRon.Arena.Frontend.Olean.OleanPins} {st : EStore} (hw : NStoreWF st.ns)
    {m : NIdx} {mC : ConLeche.Name}
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    {own : ConRon.Arena.Frontend.Olean.NamePositions} {ownC : ConLeche.Frontend.Olean.NamePositions}
    (hix : IndexRel st ix ixC) (ho : NPsRel st own ownC) {s s' : AState}
    (h : ConRon.Arena.Frontend.Olean.freshOk pk m ld ix own s = .ok ((), s')) :
    s' = s ∧ ConLeche.Frontend.Olean.freshOk mC ldC ixC ownC = .ok () := by
  generalize hP : ConRon.Arena.Frontend.Olean.freshOk pk m ld ix own = P at h
  unfold ConRon.Arena.Frontend.Olean.freshOk at hP
  unfold ConLeche.Frontend.Olean.freshOk
  split at hP
  · rename_i hf
    subst hP
    refine ⟨(AM.pure_ok h).2, ?_⟩
    have hnone := find?_none_rel (R := NPRel st)
      (p := fun (q : ConRon.Arena.Frontend.Olean.NamePosition) => ix.first.contains q.name)
      (q := fun (q : ConLeche.Frontend.Olean.NamePosition) => ixC.first.contains q.name)
      (fun q qC hq => hix.first.contains_eq hw hq.name)
      ho.consts (by rw [← Array.find?_toList] at hf; exact hf)
    rw [← Array.find?_toList, hnone]
    rfl
  · subst hP
    obtain ⟨a, s₁, -, h⟩ := AM.bind_ok h
    obtain ⟨b, s₂, -, h⟩ := AM.bind_ok h
    obtain ⟨c, s₃, -, h⟩ := AM.bind_ok h
    exact (AM.fail_ok h).elim

end ConRon.Bridge.Modular
