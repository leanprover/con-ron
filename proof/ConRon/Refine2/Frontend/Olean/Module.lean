/-
# `ConRon.Refine2.Frontend.Olean.Module` — `olean/module.rs` against `Arena/Frontend/Olean/Module.lean`

**Task #142, Theorem 2.**  The comparisons of two stored constants are pure, and `BT` is the
judgement of one: whatever the Rust's test answers is the twin's boolean.  Handles compare
by `absNIdx`/`absEIdx`, strings by `name::str_eq` with `StrWF`.
-/
import ConRon.Refine2.Frontend.Olean.View
import ConRon.Refine2.Frontend.Olean.Spec
import ConRon.Arena.Frontend.Olean.Module

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.module (hints_eq rules_eq rules_eq_loop nidx_list_eq nidx_list_eq_loop
  u64_list_eq u64_list_eq_loop kinds_same entry_same hidden_kind expo_of priv_loc_of
  priv_loc_of_loop priv_idx_of priv_idx_of_loop)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConLeche.Frontend.Olean (CKindF CEntryF Expo hintsEq)
open ConRon.Arena
open ConRon.Arena.Frontend.Olean (rulesEq entrySame expoOf expoStep expoLoop expoOfParts nameP entryAt)
open ConRon.Refine (StrWF)

/-! ## `BT`: a test -/

/-- **A Rust test answers the twin's boolean.** -/
def BT (f : Result Bool) (t : Bool) : Prop := ∀ b, f = ok b → b = t

theorem BT.dec {c : Prop} [Decidable c] {t : Bool} (hc : c ↔ t = true) : BT (ok (decide c)) t := by
  intro b h
  cases Result.ok_injective h
  by_cases hd : c
  · simp [hd, hc.mp hd]
  · have : ¬ t = true := fun e => hd (hc.mpr e)
    simp [hd, this]

theorem BT.false : BT (ok false) false := fun _ h => (Result.ok_injective h).symm

theorem BT.of_eq {f : Result Bool} {t u : Bool} (h : BT f t) (e : u = t) : BT f u := by
  rw [e]; exact h

/-- The Rust's `f && g`, where `f` runs. -/
theorem BT.and {f g : Result Bool} {t u : Bool} (hf : BT f t) (hg : BT g u) :
    BT (Std.bind f fun b => if b = true then g else ok Bool.false) (t && u) := by
  intro b h
  obtain ⟨b1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← hf b1 h1]
  cases b1 with
  | true => simpa using hg b h
  | false =>
    rw [ite_eq_right (by simp)] at h
    exact (Result.ok_injective h).symm

/-- The Rust's `c && g`, for a pure `c`. -/
theorem BT.andc {c : Prop} [Decidable c] {g : Result Bool} {t u : Bool} (hc : c ↔ t = true)
    (hg : BT g u) : BT (if c then g else ok Bool.false) (t && u) := by
  intro b h
  by_cases hd : c
  · rw [ite_eq_left hd] at h
    simp [hc.mp hd, hg b h]
  · rw [ite_eq_right hd] at h
    have : ¬ t = true := fun e => hd (hc.mpr e)
    simp [this, (Result.ok_injective h).symm]

theorem u64_iff (a b : Std.U64) : a = b ↔ (a.val == b.val) = true := by
  rw [beq_iff_eq]
  exact ⟨fun h => by rw [h], fun h => UScalar.eq_of_val_eq h⟩

theorem bool_iff (a b : Bool) : a = b ↔ (a == b) = true := by
  rw [beq_iff_eq]

theorem BT.nidx (a b : arena.handle.NIdx) :
    BT (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b) (absNIdx a == absNIdx b) :=
  fun _ h => nidx_eq2_abs h

theorem BT.eidx (a b : arena.handle.EIdx) :
    BT (arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b) (absEIdx a == absEIdx b) :=
  fun _ h => eidx_eq2_abs h

/-! ## The list comparisons -/

theorem drop_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.drop_eq_getElem_cons hi

/-- **The walk of two vectors of one length**, as the list comparison `R` it runs:
the loop's body has `hL`'s shape. -/
theorem loop_beq {α : Type} {R : List α → List α → Bool} {test : α → α → Bool}
    (hnil : R [] [] = true) (hcons : ∀ x xs y ys, R (x :: xs) (y :: ys) = (test x y && R xs ys))
    {a b : List α} (hlen : a.length = b.length) {L : Std.Usize → Result Bool}
    (hL : ∀ i r, L i = ok r → (a.length ≤ i.val ∧ r = true) ∨
      ∃ x y, a[i.val]? = some x ∧ b[i.val]? = some y ∧
        ((test x y = Bool.false ∧ r = Bool.false) ∨
          (test x y = true ∧ ∃ j : Std.Usize, j.val = i.val + 1 ∧ L j = ok r)))
    (n : Nat) : ∀ i r, a.length - i.val ≤ n → L i = ok r → r = R (a.drop i.val) (b.drop i.val) := by
  induction n with
  | zero =>
    intro i r hn h
    rcases hL i r h with ⟨_, rfl⟩ | ⟨x, y, hx, _, _⟩
    · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega), hnil]
    · have := (List.getElem?_eq_some_iff.mp hx).1
      omega
  | succ n ih =>
    intro i r hn h
    rcases hL i r h with ⟨_, rfl⟩ | ⟨x, y, hx, hy, h2⟩
    · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega), hnil]
    · rw [drop_of_getElem? hx, drop_of_getElem? hy, hcons]
      rcases h2 with ⟨ht, rfl⟩ | ⟨ht, j, hj, hl⟩
      · rw [ht]; rfl
      · rw [ht, Bool.true_and, ← hj]
        exact ih j r (by omega) hl

/-- The length test before a walk. -/
theorem len_walk {α : Type} {a b : alloc.vec.Vec α} {W : Result Bool} {t : Bool}
    (hW : a.val.length = b.val.length → BT W t) (hne : a.val.length ≠ b.val.length → t = Bool.false) :
    BT (if (alloc.vec.Vec.len a != alloc.vec.Vec.len b) = true then ok Bool.false else W) t := by
  intro o h
  by_cases hl : a.val.length = b.val.length
  · have : ¬ (alloc.vec.Vec.len a != alloc.vec.Vec.len b) = true := by
      simp only [bne_iff_ne]
      intro hn
      exact hn (UScalar.eq_of_val_eq (by simpa using hl))
    rw [ite_eq_right this] at h
    exact hW hl o h
  · have : (alloc.vec.Vec.len a != alloc.vec.Vec.len b) = true := by
      simp only [bne_iff_ne]
      intro he
      apply hl
      have := congrArg (fun x : Std.Usize => x.val) he
      simpa using this
    rw [ite_eq_left this] at h
    rw [hne hl]
    exact (Result.ok_injective h).symm

theorem add_one_val {i j : Std.Usize} (h : i + 1#usize = ok j) : j.val = i.val + 1 := by
  rw [ConRon.Refine.HashMap.uscalar_add_eq h]; rfl

theorem bt_of_loop {α : Type} {R : List α → List α → Bool} {test : α → α → Bool}
    (hnil : R [] [] = true) (hcons : ∀ x xs y ys, R (x :: xs) (y :: ys) = (test x y && R xs ys))
    {a b : alloc.vec.Vec α} (hlen : a.val.length = b.val.length) {L : Std.Usize → Result Bool}
    (hL : ∀ i r, L i = ok r → (a.val.length ≤ i.val ∧ r = true) ∨
      ∃ x y, a.val[i.val]? = some x ∧ b.val[i.val]? = some y ∧
        ((test x y = Bool.false ∧ r = Bool.false) ∨
          (test x y = true ∧ ∃ j : Std.Usize, j.val = i.val + 1 ∧ L j = ok r))) :
    BT (L 0#usize) (R a.val b.val) := by
  intro r h
  simpa using loop_beq hnil hcons hlen hL _ 0#usize r (Nat.le_refl _) h

/-- **`nidx_list_eq` is `==` of the handles.** -/
theorem nidx_list_eq_bt (a b : alloc.vec.Vec arena.handle.NIdx) :
    BT (nidx_list_eq a b) (a.val.map absNIdx == b.val.map absNIdx) := by
  refine len_walk (fun hl => bt_of_loop (R := fun l l' => l.map absNIdx == l'.map absNIdx)
      (test := fun x y => absNIdx x == absNIdx y) rfl (by simp) hl ?_) ?_
  · intro i r h
    rw [nidx_list_eq_loop] at h
    by_cases hc : i < alloc.vec.Vec.len a
    · rw [ite_eq_left hc] at h
      peel h as x, hx
      peel h as y, hy
      peel h as b1, hb
      refine Or.inr ⟨x, y, ConRon.Refine.ExprOps.vec_index_getElem? hx,
        ConRon.Refine.ExprOps.vec_index_getElem? hy, ?_⟩
      have e := nidx_eq2_abs hb
      cases b1 with
      | true =>
        rw [ite_eq_left rfl] at h
        peel h as j, hj
        exact Or.inr ⟨e.symm, j, add_one_val hj, h⟩
      | false =>
        rw [ite_eq_right (by simp)] at h
        exact Or.inl ⟨e.symm, (Result.ok_injective h).symm⟩
    · rw [ite_eq_right hc] at h
      refine Or.inl ⟨?_, (Result.ok_injective h).symm⟩
      have : ¬ i.val < a.val.length := by simpa [UScalar.lt_equiv] using hc
      omega
  · intro hne
    rw [Bool.eq_false_iff]
    intro he
    exact hne (by simpa using List.length_eq_of_beq he)

/-- **`u64_list_eq` is `==` of the words.** -/
theorem u64_list_eq_bt (a b : alloc.vec.Vec Std.U64) :
    BT (u64_list_eq a b) (a.val.map absWord == b.val.map absWord) := by
  refine len_walk (fun hl => bt_of_loop (R := fun l l' => l.map absWord == l'.map absWord)
      (test := fun x y => absWord x == absWord y) rfl (by simp) hl ?_) ?_
  · intro i r h
    rw [u64_list_eq_loop] at h
    by_cases hc : i < alloc.vec.Vec.len a
    · rw [ite_eq_left hc] at h
      peel h as x, hx
      peel h as y, hy
      refine Or.inr ⟨x, y, ConRon.Refine.ExprOps.vec_index_getElem? hx,
        ConRon.Refine.ExprOps.vec_index_getElem? hy, ?_⟩
      by_cases hxy : x = y
      · subst hxy
        rw [ite_eq_right (by simp)] at h
        peel h as j, hj
        exact Or.inr ⟨by simp, j, add_one_val hj, h⟩
      · rw [ite_eq_left (by simpa using hxy)] at h
        refine Or.inl ⟨?_, (Result.ok_injective h).symm⟩
        simpa using fun e => hxy (absWord_inj e)
    · rw [ite_eq_right hc] at h
      refine Or.inl ⟨?_, (Result.ok_injective h).symm⟩
      have : ¬ i.val < a.val.length := by simpa [UScalar.lt_equiv] using hc
      omega
  · intro hne
    rw [Bool.eq_false_iff]
    intro he
    exact hne (by simpa using List.length_eq_of_beq he)

/-- A rule, as the twin's. -/
@[reducible] def absRule (r : arena.handle.NIdx × Std.U64 × arena.handle.EIdx) :
    NIdx × Nat × EIdx := (absNIdx r.1, r.2.1.val, absEIdx r.2.2)

theorem rulesEq_len : ∀ {l l' : List (NIdx × Nat × EIdx)}, rulesEq l l' = true → l.length = l'.length
  | [], [], _ => rfl
  | (_, _, _) :: _, [], h => by simp [rulesEq] at h
  | [], (_, _, _) :: _, h => by simp [rulesEq] at h
  | (_, _, _) :: _, (_, _, _) :: _, h => by
    simp only [rulesEq, Bool.and_eq_true] at h
    simpa using rulesEq_len h.2

/-- **`rules_eq` is `rulesEq`.** -/
theorem rules_eq_bt (a b : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)) :
    BT (rules_eq a b) (rulesEq (a.val.map absRule) (b.val.map absRule)) := by
  refine len_walk (fun hl => bt_of_loop (R := fun l l' => rulesEq (l.map absRule) (l'.map absRule))
      (test := fun x y => absNIdx x.1 == absNIdx y.1 && x.2.1.val == y.2.1.val && absEIdx x.2.2 == absEIdx y.2.2)
      rfl (by intros; simp [rulesEq, Bool.and_assoc]) hl ?_) ?_
  · intro i r h
    rw [rules_eq_loop] at h
    by_cases hc : i < alloc.vec.Vec.len a
    · rw [ite_eq_left hc] at h
      peel h as ⟨n, u, e⟩, hx
      peel h as ⟨n1, u1, e1⟩, hy
      refine Or.inr ⟨(n, u, e), (n1, u1, e1), ConRon.Refine.ExprOps.vec_index_getElem? hx,
        ConRon.Refine.ExprOps.vec_index_getElem? hy, ?_⟩
      dsimp only at h ⊢
      peel h as b1, hb
      have e1' := nidx_eq2_abs hb
      cases b1 with
      | false =>
        rw [ite_eq_right (by simp)] at h
        exact Or.inl ⟨by simp [← e1'], (Result.ok_injective h).symm⟩
      | true =>
        rw [ite_eq_left rfl] at h
        by_cases hu : u = u1
        · rw [ite_eq_left hu] at h
          peel h as b2, hb2
          have e2' := eidx_eq2_abs hb2
          cases b2 with
          | false =>
            rw [ite_eq_right (by simp)] at h
            exact Or.inl ⟨by simp [← e2'], (Result.ok_injective h).symm⟩
          | true =>
            rw [ite_eq_left rfl] at h
            peel h as j, hj
            exact Or.inr ⟨by simp [← e1', ← e2', hu], j, add_one_val hj, h⟩
        · rw [ite_eq_right hu] at h
          refine Or.inl ⟨?_, (Result.ok_injective h).symm⟩
          have : ¬ u.val = u1.val := fun e => hu (UScalar.eq_of_val_eq e)
          simp [this]
    · rw [ite_eq_right hc] at h
      refine Or.inl ⟨?_, (Result.ok_injective h).symm⟩
      have : ¬ i.val < a.val.length := by simpa [UScalar.lt_equiv] using hc
      omega
  · intro hne
    rw [Bool.eq_false_iff]
    intro he
    exact hne (by simpa using rulesEq_len he)

/-! ## The kinds -/

/-- **`hints_eq` is `hintsEq`.** -/
theorem hints_eq_bt (a b : frontend.scan_types.HintsRec) :
    BT (hints_eq a b) (hintsEq (absHintsRec a) (absHintsRec b)) := by
  cases a <;> cases b <;>
    first
    | exact BT.false
    | exact fun _ h => (Result.ok_injective h).symm
    | exact BT.dec (u64_iff _ _)

/-- `name::str_eq` is `==` of the strings, on well-formed strings. -/
theorem str_eq_bt {s t : alloc.vec.Vec Std.U32} (hs : StrWF s) (ht : StrWF t) :
    BT (kernel.name.str_eq s t) (ConRon.Refine.absString s == ConRon.Refine.absString t) := by
  intro b h
  cases b with
  | true => rw [ConRon.Refine.Name.str_eq_eq h]; simp
  | false =>
    symm
    rw [Bool.eq_false_iff]
    intro he
    have e := ConRon.Refine.Name.absString_inj hs ht (by simpa using he)
    subst e
    rw [ConRon.Refine.Name.str_eq_refl] at h
    cases Result.ok_injective h

/-- The `match` of `entrySame`. -/
def kindsSameT : CKindF NIdx EIdx → CKindF NIdx EIdx → Bool
  | .ax u, .ax u' => u == u'
  | .defn v h s, .defn v' h' s' => v == v' && hintsEq h h' && s == s'
  | .thm v al, .thm v' al' => v == v' && al == al'
  | .opaq v u, .opaq v' u' => v == v' && u == u'
  | .quot k, .quot k' => k == k'
  | .induct a b c d e f g h, .induct a' b' c' d' e' f' g' h' =>
    a == a' && b == b' && c == c' && d == d' && e == e' && f == f' && g == g' && h == h'
  | .ctor a b c d e, .ctor a' b' c' d' e' =>
    a == a' && b == b' && c == c' && d == d' && e == e'
  | .recur a b c d e f g h, .recur a' b' c' d' e' f' g' h' =>
    a == a' && b == b' && c == c' && d == d' && e == e' && rulesEq f f' && g == g' && h == h'
  | _, _ => false

/-- A stored constant's kind, as the twin's relation asks. -/
abbrev KRel := KindRel (N := arena.handle.NIdx) (E := arena.handle.EIdx) absNIdx absEIdx ValRel

theorem rules_abs_map {r : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)}
    {r' : List (NIdx × Nat × EIdx)} (h : List.Forall₂ (RuleRel absNIdx absEIdx ValRel) r.val r') :
    r' = r.val.map absRule := by
  generalize r.val = l at h
  induction h with
  | nil => rfl
  | @cons a b _ _ hab _ ih =>
    obtain ⟨h1, h2, h3⟩ := hab
    obtain ⟨b1, b2, b3⟩ := b
    simp only at h1 h2 h3
    rw [ih, List.map_cons]
    subst h1 h2 h3
    rfl

/-- **`kinds_same` is the `match` of `entrySame`.** -/
theorem kinds_same_bt {a b : frontend.olean.spec.CKindF arena.handle.NIdx arena.handle.EIdx}
    {a' b' : CKindF NIdx EIdx} (ha : KRel a a') (hb : KRel b b') :
    BT (kinds_same a b) (kindsSameT a' b') := by
  cases a <;> cases a' <;> try exact False.elim ha
  all_goals cases b <;> cases b' <;> try first | exact False.elim hb | exact BT.false
  · obtain rfl := ha
    obtain rfl := hb
    exact BT.dec (bool_iff _ _)
  · obtain ⟨rfl, rfl, rfl, h1⟩ := ha
    obtain ⟨rfl, rfl, rfl, h2⟩ := hb
    exact (BT.and (BT.eidx _ _) (BT.and (hints_eq_bt _ _) (str_eq_bt h1 h2))).of_eq
      (Bool.and_assoc _ _ _)
  · obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := hb
    exact BT.and (BT.eidx _ _) (nidx_list_eq_bt _ _)
  · obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := hb
    exact BT.and (BT.eidx _ _) (BT.dec (bool_iff _ _))
  · obtain ⟨rfl, h1⟩ := ha
    obtain ⟨rfl, h2⟩ := hb
    exact str_eq_bt h1 h2
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
    exact (BT.andc (u64_iff _ _) <| BT.andc (u64_iff _ _) <| BT.and (nidx_list_eq_bt _ _) <|
      BT.and (nidx_list_eq_bt _ _) <| BT.andc (u64_iff _ _) <| BT.andc (bool_iff _ _) <|
      BT.andc (bool_iff _ _) <| BT.dec (bool_iff _ _)).of_eq (by simp only [kindsSameT, Bool.and_assoc])
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hb
    exact (BT.and (BT.nidx _ _) <| BT.andc (u64_iff _ _) <| BT.andc (u64_iff _ _) <|
      BT.andc (u64_iff _ _) <| BT.dec (bool_iff _ _)).of_eq (by simp only [kindsSameT, Bool.and_assoc])
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, h1, rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl, rfl, rfl, rfl, h2, rfl, rfl⟩ := hb
    rw [rules_abs_map h1, rules_abs_map h2]
    exact (BT.and (nidx_list_eq_bt _ _) <| BT.andc (u64_iff _ _) <| BT.andc (u64_iff _ _) <|
      BT.andc (u64_iff _ _) <| BT.andc (u64_iff _ _) <| BT.and (rules_eq_bt _ _) <|
      BT.andc (bool_iff _ _) <| BT.dec (bool_iff _ _)).of_eq (by simp only [kindsSameT, Bool.and_assoc])

theorem entrySame_eq (a b : CEntryF NIdx EIdx) :
    entrySame a b = (a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
      kindsSameT a.kind b.kind) := rfl

/-- **`entry_same` is `entrySame`.** -/
theorem entry_same_bt {a b : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    {a' b' : CEntryF NIdx EIdx} (ha : ERel a a') (hb : ERel b b') :
    BT (entry_same a b) (entrySame a' b') := by
  rw [entrySame_eq, ← ha.name, ← hb.name, ← ha.type, ← hb.type, ← ha.levelParams, ← hb.levelParams]
  exact (BT.and (BT.nidx _ _) <| BT.and (nidx_list_eq_bt _ _) <| BT.and (BT.eidx _ _) <|
    kinds_same_bt ha.kind hb.kind).of_eq (by simp only [Bool.and_assoc])

/-- The twin's test of a hidden value: the `match` of `expoStep`, and of `expoOf` with its
arguments swapped. -/
def hiddenT {N E N2 E2 : Type} : CKindF N E → CKindF N2 E2 → Bool
  | .ax u, .defn _ _ s => u == (s != "safe")
  | .ax u, .thm .. => !u
  | .ax u, .opaq _ u' => u == u'
  | _, _ => false

theorem hidden_safe {u b1 : Bool} {s : String} (e : b1 = true ↔ s = "safe") :
    decide ((u = true) = ¬ b1 = true) = (u == (s != "safe")) := by
  by_cases he : s = "safe"
  · have : b1 = true := e.mpr he
    subst he this
    cases u <;> simp
  · have : b1 = false := by
      cases b1
      · rfl
      · exact absurd (e.mp rfl) he
    subst this
    have hne : (s != "safe") = true := by simpa using he
    rw [hne]
    cases u <;> simp

/-- **`hidden_kind` is `hiddenT`.** -/
theorem hidden_kind_bt {N N' E E' N2 N2' E2 E2' : Type} {AN : N → N'} {AE : E → E'} {RN : NatRel}
    {AN2 : N2 → N2'} {AE2 : E2 → E2'} {RN2 : NatRel}
    {a : frontend.olean.spec.CKindF N E} {b : frontend.olean.spec.CKindF N2 E2}
    {a' : CKindF N' E'} {b' : CKindF N2' E2'} (ha : KindRel AN AE RN a a') (hb : KindRel AN2 AE2 RN2 b b') :
    BT (hidden_kind a b) (hiddenT a' b') := by
  cases a <;> cases a' <;> try exact False.elim ha
  all_goals try exact BT.false
  cases b <;> cases b' <;> try first | exact False.elim hb | exact BT.false
  · obtain rfl := ha
    obtain ⟨-, -, rfl, h1⟩ := hb
    intro o h
    delta hidden_kind at h
    dsimp only at h
    simp only [lift, bind_ok] at h
    peel h as b1, hb1
    cases Result.ok_injective h
    have hv : (Std.Array.to_slice frontend.olean.module.hidden_kind.S_SAFE).val
        = [115#u32, 97#u32, 102#u32, 101#u32] := by
      unfold frontend.olean.module.hidden_kind.S_SAFE; rfl
    refine hidden_safe ?_
    rw [ConRon.Refine2.Frontend.cps_beq_str h1 (by rw [hv]; decide) hb1, hv]
    rfl
  · obtain rfl := ha
    cases ‹Bool› <;> exact fun _ h => (Result.ok_injective h).symm
  · obtain rfl := ha
    obtain ⟨-, rfl⟩ := hb
    exact BT.dec (bool_iff _ _)

/-! ## `expo_of` -/

/-- `module::Expo`, as upstream's. -/
def absExpo : frontend.olean.module.Expo → Expo
  | .Same => .same
  | .Hidden => .hidden
  | .Absent => .absent

theorem expoOf_eq (p e : CEntryF NIdx EIdx) :
    expoOf p e = if entrySame p e then some .same
      else if (p.name == e.name && p.levelParams == e.levelParams && p.type == e.type) then
        (if hiddenT e.kind p.kind then some .hidden else none) else none := by
  unfold expoOf
  refine ite_congr rfl (fun _ => rfl) fun _ => ite_congr rfl (fun _ => ?_) fun _ => rfl
  generalize p.kind = a
  generalize e.kind = b
  cases a <;> cases b <;> simp [hiddenT]

/-- The Rust's `f && g` of a test before an `Option`, against the twin's `if`. -/
theorem chain_none {γ δ : Type} {A : γ → δ} {f : Result Bool} {g : Result (Option γ)} {t : Bool}
    {y : Option δ} (hf : BT f t) (hg : ∀ o, g = ok o → o.map A = y) :
    ∀ o, (Std.bind f fun b => if b = true then g else ok none) = ok o →
      o.map A = if t then y else none := by
  intro o h
  peel h as b, hb
  rw [← hf b hb]
  cases b with
  | true =>
    rw [ite_eq_left rfl] at h
    simpa using hg o h
  | false =>
    rw [ite_eq_right (by simp)] at h
    cases Result.ok_injective h
    simp

theorem if_and3 {δ : Type} (a b c : Bool) (y : Option δ) :
    (if (a && b && c) = true then y else none) =
      if a = true then (if b = true then (if c = true then y else none) else none) else none := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **`expo_of` is `expoOf`.** -/
theorem expo_of_eq {p e : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    {p' e' : CEntryF NIdx EIdx} (hp : ERel p p') (he : ERel e e')
    {o} (h : expo_of p e = ok o) : o.map absExpo = expoOf p' e' := by
  rw [expoOf_eq, ← hp.name, ← he.name, ← hp.type, ← he.type, ← hp.levelParams, ← he.levelParams,
    if_and3]
  rw [expo_of] at h
  peel h as b, hb
  rw [← entry_same_bt hp he b hb]
  cases b with
  | true =>
    rw [ite_eq_left rfl] at h
    cases Result.ok_injective h
    rfl
  | false =>
    rw [ite_eq_right (by simp)] at h ⊢
    refine chain_none (BT.nidx _ _) (fun o1 h1 => chain_none (nidx_list_eq_bt _ _)
      (fun o2 h2 => chain_none (BT.eidx _ _) (fun o3 h3 => ?_) o2 h2) o1 h1) o h
    peel h3 as b4, hb4
    rw [← hidden_kind_bt he.kind hp.kind b4 hb4]
    cases b4 with
    | true =>
      rw [ite_eq_left rfl] at h3
      cases Result.ok_injective h3
      rfl
    | false =>
      rw [ite_eq_right (by simp)] at h3 ⊢
      cases Result.ok_injective h3
      rfl

/-! ## The tables of the private constants -/

open ConRon.Refine.HashMap2 (Inv RelOn toFun KeysOk)

/-- The table of keys to their last positions, one key at a time. -/
def posMap {K : Type} [BEq K] [Hashable K] (ks : List K) : Nat → Std.HashMap K Nat
  | 0 => {}
  | i + 1 =>
    match ks[i]? with
    | some k => (posMap ks i).insert k i
    | none => posMap ks i

/-- **A table of positions**: `m` is `t`, with the positions below `n`. -/
structure PosRel {K K' : Type} [DecidableEq K] [BEq K'] [Hashable K']
    (H : ron.hashmap.Hashable K) (A : K → K') (m : ron.hashmap2.HashMap2 K Std.U64)
    (t : Std.HashMap K' Nat) (n : Nat) : Prop where
  inv : Inv H m
  rel : RelOn (fun _ => True) m t A (fun v => v.val)
  lt : ∀ k v, toFun m k = some v → v.val < n

/-- **The loop that numbers a vector's keys.** -/
theorem pos_loop {K K' : Type} [DecidableEq K] [BEq K'] [LawfulBEq K'] [Hashable K'] [LawfulHashable K']
    {H : ron.hashmap.Hashable K} {E : ron.hashmap.Eq2 K}
    (heq : ConRon.Refine.HashMap.Eq2Fwd E (fun _ : K => True)) {A : K → K'}
    (hinj : ∀ a b, A a = A b → a = b) {ks : List K}
    {L : Std.Usize → ron.hashmap2.HashMap2 K Std.U64 → Result (ron.hashmap2.HashMap2 K Std.U64)}
    (hL : ∀ i m r, L i m = ok r → (ks.length ≤ i.val ∧ r = m) ∨
      ∃ k old m' j, ks[i.val]? = some k ∧
        ron.hashmap2.HashMap2.insert H E m k (UScalar.cast .U64 i) = ok (old, m') ∧
        j.val = i.val + 1 ∧ L j m' = ok r)
    (n : Nat) : ∀ i m r, ks.length - i.val ≤ n → i.val ≤ ks.length →
      PosRel H A m (posMap (ks.map A) i.val) i.val → L i m = ok r →
      PosRel H A r (posMap (ks.map A) ks.length) ks.length := by
  induction n with
  | zero =>
    intro i m r hn hle hm h
    rcases hL i m r h with ⟨_, rfl⟩ | ⟨k, _, _, _, hk, _⟩
    · have : i.val = ks.length := by omega
      rwa [this] at hm
    · have := (List.getElem?_eq_some_iff.mp hk).1
      omega
  | succ n ih =>
    intro i m r hn hle hm h
    rcases hL i m r h with ⟨hge, rfl⟩ | ⟨k, old, m', j, hk, hins, hj, hl⟩
    · have : i.val = ks.length := by omega
      rwa [this] at hm
    · have hlt := (List.getElem?_eq_some_iff.mp hk).1
      refine ih j m' r (by omega) (by omega) ?_ hl
      have hkeys : KeysOk (fun _ => True) m := fun _ _ => trivial
      obtain ⟨hinv', -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_wf heq hm.inv hkeys trivial hins
      obtain ⟨hr, -⟩ := ConRon.Refine.HashMap2.Rel_insert_wf heq (fun a b _ _ e => hinj a b e) hm.inv hkeys
        hm.rel trivial hins
      have hv : (UScalar.cast UScalarTy.U64 i).val = i.val := cast_u64_usize i
      refine ⟨hinv', ?_, ?_⟩
      · rw [hj]
        have e : posMap (ks.map A) (i.val + 1) = (posMap (ks.map A) i.val).insert (A k) i.val := by
          rw [posMap, List.getElem?_map, hk]
          rfl
        rw [e]
        rw [hv] at hr
        exact hr
      · intro k' v hv'
        rw [hupd, Function.update_apply] at hv'
        rw [hj]
        split at hv'
        · cases hv'
          omega
        · have := hm.lt k' v hv'
          omega

/-- `posMap` is the first `i` steps of the twin's `foldl`. -/
theorem posMap_foldl {K : Type} [BEq K] [Hashable K] (ks : List K) :
    (ks.foldl (fun (x : Std.HashMap K Nat × Nat) c => (x.1.insert c x.2, x.2 + 1)) ({}, 0)).1 =
      posMap ks ks.length := by
  have key : ∀ (rest pre : List K), pre ++ rest = ks →
      rest.foldl (fun (x : Std.HashMap K Nat × Nat) c => (x.1.insert c x.2, x.2 + 1))
        (posMap ks pre.length, pre.length) =
      (posMap ks ks.length, ks.length) := by
    intro rest
    induction rest with
    | nil =>
      intro pre h
      simp only [List.append_nil] at h
      subst h
      rfl
    | cons c rest ih =>
      intro pre h
      have hc : ks[pre.length]? = some c := by rw [← h]; simp
      have e := ih (pre ++ [c]) (by simpa using h)
      simp only [List.length_append, List.length_singleton] at e
      rw [List.foldl_cons]
      have e2 : posMap ks (pre.length + 1) = (posMap ks pre.length).insert c pre.length := by
        rw [posMap, hc]
      rw [e2] at e
      exact e
  have := key ks [] rfl
  simpa [posMap] using congrArg Prod.fst this

/-- `posMap` is the twin's `Nat.fold` over an array. -/
theorem posMap_fold {α K : Type} [BEq K] [Hashable K] (cs : Array α) (f : α → K) :
    (cs.size.fold (init := ({} : Std.HashMap K Nat)) fun i h acc => acc.insert (f cs[i]) i) =
      posMap (cs.toList.map f) cs.size := by
  have key : ∀ n (hn : n ≤ cs.size),
      (n.fold (init := ({} : Std.HashMap K Nat)) fun i h acc => acc.insert (f (cs[i]'(by omega))) i) =
        posMap (cs.toList.map f) n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hlt : n < cs.size := by omega
      have e : (cs.toList.map f)[n]? = some (f cs[n]) := by simp [hlt]
      rw [Nat.fold_succ, ih (by omega), posMap, e]
  exact key _ (Nat.le_refl _)

theorem pos_empty {K K' : Type} [DecidableEq K] [BEq K'] [Hashable K'] [LawfulBEq K']
    {H : ron.hashmap.Hashable K} {A : K → K'} {c : Std.Usize} {ks : List K'}
    {m : ron.hashmap2.HashMap2 K Std.U64}
    (h : ron.hashmap2.HashMap2.with_capacity K Std.U64 c = ok m) : PosRel H A m (posMap ks 0) 0 := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.with_capacity_refines (HashableInst := H) h
  refine ⟨hinv, ConRon.Refine.HashMap2.RelOn_empty hnone, ?_⟩
  intro k v hk
  rw [hnone] at hk
  cases hk

/-- **`priv_loc_of` is the twin's `foldl`.** -/
theorem priv_loc_of_rel {consts : alloc.vec.Vec Std.U64} {o} (h : priv_loc_of consts = ok o) :
    PosRel hU64 (fun x : Std.U64 => x.val) o
      ((consts.val.map (fun x : Std.U64 => x.val)).foldl
        (fun (x : Std.HashMap Nat Nat × Nat) c => (x.1.insert c x.2, x.2 + 1)) ({}, 0)).1
      consts.val.length := by
  rw [posMap_foldl, List.length_map]
  rw [priv_loc_of] at h
  peel h as m, hm
  refine pos_loop (E := U64.Insts.Con_ron_coreRonHashmapEq2) u64Eq2Fwd
    (fun _ _ e => UScalar.eq_of_val_eq e) (L := fun i m => priv_loc_of_loop consts m i) ?_ _
    0#usize m o (Nat.le_refl _) (by simp) (pos_empty hm) h
  intro i m r h
  rw [priv_loc_of_loop] at h
  by_cases hc : i < alloc.vec.Vec.len consts
  · rw [ite_eq_left hc] at h
    simp only [lift, bind_ok] at h
    peel h as k, hk
    peel h as ⟨old, m'⟩, hins
    peel h as j, hj
    exact Or.inr ⟨k, old, m', j, ConRon.Refine.ExprOps.vec_index_getElem? hk, hins, add_one_val hj, h⟩
  · rw [ite_eq_right hc] at h
    refine Or.inl ⟨?_, (Result.ok_injective h).symm⟩
    have : ¬ i.val < consts.val.length := by simpa [UScalar.lt_equiv] using hc
    omega

theorem entry_names_map {cs : List (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {cs' : List (CEntryF NIdx EIdx)} (h : List.Forall₂ ERel cs cs') :
    (cs.map (fun c => c.name)).map absNIdx = cs'.map (fun c => c.name) := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, ih, hab.name]

/-- **`priv_idx_of` is the twin's `Nat.fold`.** -/
theorem priv_idx_of_rel {cs : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {cs' : Array (CEntryF NIdx EIdx)} (hcs : List.Forall₂ ERel cs.val cs'.toList) {o}
    (h : priv_idx_of cs = ok o) :
    PosRel arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable absNIdx o
      (cs'.size.fold (init := {}) fun i _ acc => acc.insert cs'[i].name i) cs.val.length := by
  have hlen : cs'.size = (cs.val.map (fun c => c.name)).length := by
    simpa using hcs.length_eq.symm
  rw [posMap_fold cs' (fun c => c.name), ← entry_names_map hcs, hlen]
  have hl2 : cs.val.length = (cs.val.map (fun c => c.name)).length := by simp
  rw [hl2]
  rw [priv_idx_of] at h
  peel h as m, hm
  refine pos_loop (E := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2) nidx_eq2
    (fun _ _ e => absNIdx_inj e) (L := fun i m => priv_idx_of_loop cs m i) ?_ _
    0#usize m o (Nat.le_refl _) (by simp) (pos_empty hm) h
  intro i m r h
  rw [priv_idx_of_loop] at h
  by_cases hc : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hc] at h
    simp only [lift, bind_ok] at h
    peel h as k, hk
    peel h as n, hn
    obtain rfl := nidx_dup2_ok hn
    peel h as ⟨old, m'⟩, hins
    peel h as j, hj
    refine Or.inr ⟨k.name, old, m', j, ?_, hins, add_one_val hj, h⟩
    rw [List.getElem?_map, ConRon.Refine.ExprOps.vec_index_getElem? hk]
    rfl
  · rw [ite_eq_right hc] at h
    refine Or.inl ⟨?_, (Result.ok_injective h).symm⟩
    have : ¬ i.val < cs.val.length := by simpa [UScalar.lt_equiv] using hc
    simp only [List.length_map]
    omega

/-! ## The vector of levels -/

theorem expo_fill_loop_val {e : frontend.olean.module.Expo} {n : Std.Usize} (N : Nat) :
    ∀ (out r : alloc.vec.Vec frontend.olean.module.Expo) (i : Std.Usize), n.val - i.val ≤ N →
      frontend.olean.module.expo_fill_loop n e out i = ok r →
      r.val = out.val ++ List.replicate (n.val - i.val) e := by
  induction N with
  | zero =>
    intro out r i hN h
    rw [frontend.olean.module.expo_fill_loop] at h
    have hc : ¬ i < n := by
      have : ¬ i.val < n.val := by omega
      simpa [UScalar.lt_equiv] using this
    rw [ite_eq_right hc] at h
    cases Result.ok_injective h
    have : n.val - i.val = 0 := by omega
    simp [this]
  | succ N ih =>
    intro out r i hN h
    rw [frontend.olean.module.expo_fill_loop] at h
    by_cases hc : i < n
    · rw [ite_eq_left hc] at h
      have hlt : i.val < n.val := hc
      peel h as e1, he1
      have ee : e1 = e := by cases e <;> exact (Result.ok_injective he1).symm
      subst ee
      peel h as o1, ho1
      peel h as j, hj
      have hjv := add_one_val hj
      rw [ih o1 r j (by omega) h, ConRon.Refine.vec_push_val ho1, hjv]
      have : n.val - i.val = (n.val - (i.val + 1)) + 1 := by omega
      rw [this, List.replicate_succ]
      simp
    · rw [ite_eq_right hc] at h
      cases Result.ok_injective h
      have : ¬ i.val < n.val := hc
      have : n.val - i.val = 0 := by omega
      simp [this]

/-- `expo_fill` is `n` copies of its value. -/
theorem expo_fill_val {e : frontend.olean.module.Expo} {n : Std.Usize} {r}
    (h : frontend.olean.module.expo_fill n e = ok r) : r.val = List.replicate n.val e := by
  rw [frontend.olean.module.expo_fill] at h
  simpa using expo_fill_loop_val _ _ r 0#usize (Nat.le_refl _) h

/-- **The twin's array of levels.** -/
@[reducible] def ExpoRel (v : alloc.vec.Vec frontend.olean.module.Expo) (v' : Array Expo) : Prop :=
  v.val.map absExpo = v'.toList

/-- `expo_fill` against the twin's `cs.map fun _ => x`. -/
theorem expo_fill_rel {α : Type} {cs : Array α} {e : frontend.olean.module.Expo} {n : Std.Usize} {r}
    (hn : n.val = cs.size) (h : frontend.olean.module.expo_fill n e = ok r) :
    ExpoRel r (cs.map fun _ => absExpo e) := by
  rw [ExpoRel, expo_fill_val h, hn]
  simp

/-- **A write of the vector of levels** against `Array.set!`. -/
theorem expo_set_rel {v : alloc.vec.Vec frontend.olean.module.Expo} {v' : Array Expo}
    (hv : ExpoRel v v') {i : Std.Usize} {a : frontend.olean.module.Expo} {f}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice frontend.olean.module.Expo) v i
      = ok (a, f)) (x : frontend.olean.module.Expo) :
    ExpoRel (f x) (v'.set! i.val (absExpo x)) := by
  rw [ConRon.Refine2.Frontend.idt_index_mut_back h, ExpoRel]
  have e : (alloc.vec.Vec.set v i x).val = v.val.set i.val x := by simp
  rw [e, List.map_set, hv]
  simp

/-! ## The result channel of `expo_of_parts` -/

/-- **What the outcome of `expo_step`, `expo_loop`, `expo_of_parts` claims of a twin run**:
`ExpoErr::Msg` is the twin's `.ok (.error _)`, `ExpoErr::Err` a throw at the same kind. -/
def ExOut {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (st' : arena.monad.AState) (o : core.result.Result α frontend.olean.module.ExpoErr)
    (y : Except Arena.CheckError (Except String β × AState)) : Prop :=
  match o with
  | .Ok a => ∃ b lst', y = .ok (.ok b, lst') ∧ R a b ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st'
  | .Err (.Msg _) => ∃ m lst', y = .ok (.error m, lst') ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st'
  | .Err (.Err e) => AErrSim e y

/-- A message path of `expo_step`: pure steps, ending in `msg_err`. -/
def MsgLeaf {α γ : Type} (ar : γ)
    (m : Result (core.result.Result α frontend.olean.module.ExpoErr × γ)) : Prop :=
  ∀ o s', m = ok (o, s') → (∃ t, o = .Err (.Msg t)) ∧ s' = ar

theorem MsgLeaf.done {α γ : Type} {ar : γ} (v : alloc.vec.Vec Std.U32) :
    MsgLeaf (α := α) ar (Std.bind (frontend.olean.module.msg_err α v) fun r => ok (r, ar)) := by
  intro o s' h
  simp only [frontend.olean.module.msg_err, bind_ok] at h
  cases Result.ok_injective h
  exact ⟨⟨v, rfl⟩, rfl⟩

theorem MsgLeaf.step {α γ δ : Type} {ar : γ} {f : Result δ}
    {k : δ → Result (core.result.Result α frontend.olean.module.ExpoErr × γ)}
    (h : ∀ a, MsgLeaf ar (k a)) : MsgLeaf ar (Std.bind f k) := by
  intro o s' hm
  obtain ⟨a, _, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a o s' h2

/-- A message path. -/
macro "msg_leaf" : tactic =>
  `(tactic| repeat' first | exact MsgLeaf.done _ | refine MsgLeaf.step fun _ => ?_)

/-- `read_name` on a related store: `readName`, which leaves the state. -/
theorem read_name_step {pers st lst} (hrel : AStateRel₀ pers st lst) {n : arena.handle.NIdx} {o}
    (h : arena.env.read_name pers st.store n = ok o) :
    match o with
    | .Ok _ => ∃ x, (readName (absNIdx n)).run lst = .ok (x, lst)
    | .Err e => AErrSim e ((readName (absNIdx n)).run lst) := by
  have hR := env_read_name_abs hrel.store h
  have hrun : (readName (absNIdx n)).run lst =
      match denoteN lst.store.ns (absNIdx n) with
      | some x => .ok (x, lst)
      | none => .error (.internal "arena: dangling name handle") := by
    unfold readName
    show (match denoteN lst.store.ns (absNIdx n) with
      | some x => (pure x : AM ConLeche.Name)
      | none => Arena.fail (.internal "arena: dangling name handle")).run lst = _
    cases denoteN lst.store.ns (absNIdx n) <;> rfl
  rw [hrun]
  revert hR
  cases denoteN lst.store.ns (absNIdx n) with
  | none =>
    rintro ⟨e, rfl, hk⟩
    exact AErrSim.mk rfl (by rw [hk]; rfl)
  | some x =>
    rintro ⟨y, rfl, -⟩
    exact ⟨x, rfl⟩

theorem ite_and_tail {α : Type} (b s : Prop) [Decidable b] [Decidable s] (H T : α) :
    (if b then (if s then H else T) else T) = if b ∧ s then H else T := by
  by_cases hb : b <;> by_cases hs : s <;> simp [hb, hs]

/-- A message path against the twin's `pure (.error _)`. -/
theorem ExOut.of_msg {α β γ : Type} {pers st lst} {R : α → β → Prop} {ar : arena.store.EStore} {e0 : γ}
    {m : Result (core.result.Result α frontend.olean.module.ExpoErr × arena.store.EStore × γ)}
    {o s' v'} (hm : MsgLeaf (ar, e0) m) (h : m = ok (o, s', v'))
    (hrel : AStateRel₀ pers (withStore st ar) lst) (hinv : AStateInv pers (withStore st ar))
    (t : String) : ExOut pers R (withStore st s') o (.ok (.error t, lst)) := by
  obtain ⟨⟨u, rfl⟩, e⟩ := hm o (s', v') h
  cases e
  exact ⟨t, lst, rfl, hrel, hinv⟩

theorem and_left_eq {M b s : Bool} (h : M = b) : (M && s) = (b && s) := by rw [h]

/-- A position of the twin's array, through the relation of its list. -/
theorem arr_get_map {α β : Type} {l : List α} {f : α → β} {a : Array β} (h : l.map f = a.toList)
    (i : Nat) : a[i]? = l[i]?.map f := by
  rw [← List.getElem?_map, h, Array.getElem?_toList]

/-- **`expo_step` is `expoStep`.** -/
theorem expo_step_refines {pk bs r pers st lst} {c : Std.U64} {priv_idx priv_locs}
    {cs : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {expo : alloc.vec.Vec frontend.olean.module.Expo} {t' : Std.HashMap NIdx Nat} {locs' : Array Nat}
    {cs' : Array (CEntryF NIdx EIdx)} {expo' : Array Expo}
    (hE : ∀ st lst, RS pers ERel st lst (frontend.olean.reads.entry_at pk pers st.store bs r c)
      (entryAt (absPins pk) (absRegion bs r) c.val))
    (hr : RegionFits bs r)
    (hidx : PosRel arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable absNIdx priv_idx t' cs.val.length)
    (hlocs : priv_locs.val.map (fun x : Std.U64 => x.val) = locs'.toList)
    (hcs : List.Forall₂ ERel cs.val cs'.toList) (hexpo : ExpoRel expo expo')
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) {o s' v'}
    (h : frontend.olean.module.expo_step pk pers st.store bs r c priv_idx priv_locs cs expo = ok (o, s', v')) :
    ExOut pers (fun (_ : Unit) b => ExpoRel v' b) (withStore st s') o
      ((expoStep (absPins pk) (absRegion bs r) t' locs' cs' expo' c.val).run lst) := by
  rw [frontend.olean.module.expo_step] at h
  unfold expoStep
  peel h as o0, ho0
  have hs0 := const_skel_eq ho0
  clear ho0
  revert hs0
  generalize ConLeche.Frontend.Olean.constSkel (absRegion bs r) c.val = y0
  intro hs0
  cases hs0 with
  | none => exact ExOut.of_msg (by msg_leaf) h hrel hinv _
  | @some sk se hsk =>
    dsimp only at h ⊢
    peel h as ⟨r1, ar1⟩, hn
    have hN := name_p_refines (pk := pk) (v := sk.name) hr hrel hinv r1 ar1 hn
    rw [hsk.name] at hN
    cases r1 with
    | Err e =>
      cases e with
      | Bad =>
        obtain ⟨lst1, hx, hrel1, hinv1⟩ := hN
        rw [am_bind_ok hx]
        exact ExOut.of_msg (by msg_leaf) h hrel1 hinv1 _
      | Err e =>
        cases Result.ok_injective h
        show AErrSim e _
        rw [StateT.run_bind]
        exact AErrSim.bind hN _
    | Ok n =>
      obtain ⟨_, lst1, hx, rfl, hrel1, hinv1⟩ := hN
      rw [am_bind_ok hx]
      dsimp only at h ⊢
      peel h as r2, hr2
      have hRd := read_name_step (st := withStore st ar1) hrel1 hr2
      cases r2 with
      | Err e =>
        cases Result.ok_injective h
        show AErrSim e _
        rw [StateT.run_bind]
        exact AErrSim.bind hRd _
      | Ok nm =>
        obtain ⟨x, hx2⟩ := hRd
        rw [am_bind_ok hx2]
        dsimp only at h ⊢
        peel h as _en_text, _
        peel h as o1, ho1
        have hg := hidx.rel n trivial
        rw [← nidx_get hidx.inv ho1] at hg
        rw [← hg]
        cases o1 with
        | none => exact ExOut.of_msg (by msg_leaf) h hrel1 hinv1 _
        | some i =>
          have hlt := hidx.lt n i (nidx_get hidx.inv ho1).symm
          rw [Option.map_some]
          dsimp only at h ⊢
          simp only [lift, bind_ok] at h
          have hcsl : cs.val.length ≤ Std.Usize.max := by scalar_tac
          have hiu : (UScalar.cast .Usize i).val = i.val :=
            ConRon.Refine.ExprOps.u64_cast_usize_val (by omega)
          generalize UScalar.cast .Usize i = iu at h hiu
          by_cases hc : iu < alloc.vec.Vec.len priv_locs
          · rw [ite_eq_left hc] at h
            peel h as i2, hi2
            have e : locs'[i.val]? = some i2.val := by
              rw [arr_get_map hlocs, ← hiu, ConRon.Refine.ExprOps.vec_index_getElem? hi2]
              rfl
            rw [e, Option.bind_some]
            peel h as o2, ho2
            have hs2 := const_skel_eq ho2
            clear ho2
            revert hs2
            generalize ConLeche.Frontend.Olean.constSkel (absRegion bs r) i2.val = y2
            intro hs2
            cases hs2 with
            | none => exact ExOut.of_msg (by msg_leaf) h hrel1 hinv1 _
            | @some sk1 sp hsk1 =>
              dsimp only at h ⊢
              peel h as same, hsame
              have e1 : same = (se.type == sp.type && se.levelParams == sp.levelParams) := by
                rw [← hsk.type, ← hsk1.type, ← hsk.levelParams, ← hsk1.levelParams]
                exact BT.andc ⟨fun e => by rw [e]; simp, fun e => absWord_inj (by simpa using e)⟩
                  (u64_list_eq_bt _ _) same hsame
              peel h as b, hb
              have e2 := hidden_kind_bt hsk.kind hsk1.kind b hb
              rw [← e1, and_left_eq (b := b) (s := same) ?hk]
              case hk =>
                rw [e2]
                generalize se.kind = a
                generalize sp.kind = c
                cases a <;> cases c <;> rfl
              rw [ite_and_tail] at h
              by_cases hh : b = true ∧ same = true
              · rw [ite_eq_left hh] at h
                rw [ite_eq_left (by simp [hh])]
                peel h as ⟨_, back⟩, hm
                cases Result.ok_injective h
                exact ⟨_, lst1, rfl, hiu ▸ expo_set_rel hexpo hm .Hidden, hrel1, hinv1⟩
              · rw [ite_eq_right hh] at h
                rw [ite_eq_right (by simpa using hh)]
                peel h as ⟨r3, ar2⟩, he
                have hEn := hE (withStore st ar1) lst1 hrel1 hinv1 r3 ar2 he
                cases r3 with
                | Err e =>
                  cases e with
                  | Bad =>
                    obtain ⟨lst2, hx3, hrel2, hinv2⟩ := hEn
                    rw [am_bind_ok hx3]
                    exact ExOut.of_msg (by msg_leaf) h hrel2 hinv2 _
                  | Err e =>
                    cases Result.ok_injective h
                    show AErrSim e _
                    rw [StateT.run_bind]
                    exact AErrSim.bind hEn _
                | Ok ent =>
                  obtain ⟨ent', lst2, hx3, hRe, hrel2, hinv2⟩ := hEn
                  rw [am_bind_ok hx3]
                  dsimp only
                  replace h : (if iu ≥ alloc.vec.Vec.len cs then _ else _) = ok (o, s', v') := h
                  by_cases hge : iu ≥ alloc.vec.Vec.len cs
                  · rw [ite_eq_left hge] at h
                    have hge' : cs.val.length ≤ iu.val := by simpa [UScalar.le_equiv] using hge
                    have e3 : cs'[i.val]? = none := by
                      rw [← Array.getElem?_toList, List.getElem?_eq_none_iff, ← hcs.length_eq]
                      omega
                    rw [e3]
                    exact ExOut.of_msg (by msg_leaf) h hrel2 hinv2 _
                  · rw [ite_eq_right hge] at h
                    peel h as cf, hcf
                    obtain ⟨pc, hpc, hRc⟩ := f2_get hcs (ConRon.Refine.ExprOps.vec_index_getElem? hcf)
                    have e3 : cs'[i.val]? = some pc := by
                      rw [← Array.getElem?_toList, ← hiu, hpc]
                    rw [e3]
                    dsimp only
                    peel h as o3, ho3
                    rw [← expo_of_eq hRc hRe ho3]
                    cases o3 with
                    | none => exact ExOut.of_msg (by msg_leaf) h hrel2 hinv2 _
                    | some ex =>
                      dsimp only at h
                      peel h as ⟨_, back⟩, hm
                      cases Result.ok_injective h
                      exact ⟨_, lst2, rfl, hiu ▸ expo_set_rel hexpo hm ex, hrel2, hinv2⟩
          · rw [ite_eq_right hc] at h
            have hge' : priv_locs.val.length ≤ iu.val := by
              have : ¬ iu.val < priv_locs.val.length := by simpa [UScalar.lt_equiv] using hc
              omega
            have e : locs'[i.val]? = none := by
              rw [arr_get_map hlocs, ← hiu, List.getElem?_eq_none_iff.mpr hge']
              rfl
            rw [e, Option.bind_none]
            exact ExOut.of_msg (by msg_leaf) h hrel1 hinv1 _

/-- **`expo_loop` is `expoLoop`.** -/
theorem expo_loop_loop_refines {pk bs r pers} {e_consts : alloc.vec.Vec Std.U64} {priv_loc priv_idx priv_locs}
    {cs : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {tl : Std.HashMap Nat Nat} {nl : Nat} {t' : Std.HashMap NIdx Nat} {locs' : Array Nat}
    {cs' : Array (CEntryF NIdx EIdx)}
    (hE : ∀ c st lst, RS pers ERel st lst (frontend.olean.reads.entry_at pk pers st.store bs r c)
      (entryAt (absPins pk) (absRegion bs r) c.val))
    (hr : RegionFits bs r) (hloc : PosRel hU64 (fun x : Std.U64 => x.val) priv_loc tl nl) (hnl : nl ≤ Std.Usize.max)
    (hidx : PosRel arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable absNIdx priv_idx t' cs.val.length)
    (hlocs : priv_locs.val.map (fun x : Std.U64 => x.val) = locs'.toList)
    (hcs : List.Forall₂ ERel cs.val cs'.toList) (N : Nat) :
    ∀ (k : Std.Usize) (st : arena.monad.AState) (lst : AState) expo (expo' : Array Expo) o s' v',
      e_consts.val.length - k.val ≤ N → ExpoRel expo expo' → AStateRel₀ pers st lst → AStateInv pers st →
      frontend.olean.module.expo_loop_loop pk pers st.store bs r e_consts priv_loc priv_idx priv_locs cs expo k
        = ok (o, s', v') →
      ExOut pers (fun (_ : Unit) b => ExpoRel v' b) (withStore st s') o
        ((expoLoop (absPins pk) (absRegion bs r) tl t' locs' cs'
          ((e_consts.val.drop k.val).map (fun x : Std.U64 => x.val)) expo').run lst) := by
  induction N with
  | zero =>
    intro k st lst expo expo' o s' v' hN hexpo hrel hinv h
    rw [frontend.olean.module.expo_loop_loop] at h
    have hc : ¬ k < alloc.vec.Vec.len e_consts := by
      have : ¬ k.val < e_consts.val.length := by omega
      simpa [UScalar.lt_equiv] using this
    rw [ite_eq_right hc] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]
    exact ⟨expo', lst, rfl, hexpo, hrel, hinv⟩
  | succ N ih =>
    intro k st lst expo expo' o s' v' hN hexpo hrel hinv h
    rw [frontend.olean.module.expo_loop_loop] at h
    by_cases hc : k < alloc.vec.Vec.len e_consts
    · rw [ite_eq_left hc] at h
      have hlt : k.val < e_consts.val.length := by simpa [UScalar.lt_equiv] using hc
      peel h as c, hcv
      rw [drop_of_getElem? (ConRon.Refine.ExprOps.vec_index_getElem? hcv), List.map_cons]
      rw [expoLoop]
      peel h as o1, ho1
      have hget := ConRon.Refine.HashMap2.get_refines_gen (P := fun _ => True) u64Eq2Fwd hloc.inv
        (fun _ _ => trivial) trivial ho1
      have hg := hloc.rel c trivial
      rw [← hget] at hg
      rw [← hg]
      cases o1 with
      | some i =>
        have hilt := hloc.lt c i hget.symm
        rw [Option.map_some]
        dsimp only at h ⊢
        simp only [lift, bind_ok] at h
        have hiu : (UScalar.cast .Usize i).val = i.val :=
          ConRon.Refine.ExprOps.u64_cast_usize_val (by omega)
        peel h as ⟨_, back⟩, hm
        peel h as j, hj
        have hset := expo_set_rel hexpo hm .Same
        rw [hiu] at hset
        have := ih j st lst (back .Same) (expo'.set! i.val .same) o s' v'
          (by have := add_one_val hj; omega) hset hrel hinv h
        rwa [add_one_val hj] at this
      | none =>
        rw [Option.map_none]
        dsimp only at h ⊢
        peel h as ⟨r1, ar1, expo1⟩, hstep
        have hS := expo_step_refines (hE c) hr hidx hlocs hcs hexpo hrel hinv hstep
        cases r1 with
        | Ok u =>
          obtain ⟨b, lst1, hy, hb, hrel1, hinv1⟩ := hS
          rw [am_bind_ok hy]
          dsimp only at h ⊢
          peel h as j, hj
          have := ih j (withStore st ar1) lst1 expo1 b o s' v' (by have := add_one_val hj; omega) hb hrel1 hinv1 h
          rwa [add_one_val hj] at this
        | Err ee =>
          cases Result.ok_injective h
          cases ee with
          | Msg t =>
            obtain ⟨m, lst1, hy, hrel1, hinv1⟩ := hS
            rw [am_bind_ok hy]
            exact ⟨m, lst1, rfl, hrel1, hinv1⟩
          | Err e =>
            show AErrSim e _
            rw [StateT.run_bind]
            exact AErrSim.bind hS _
    · rw [ite_eq_right hc] at h
      cases Result.ok_injective h
      have : ¬ k.val < e_consts.val.length := by simpa [UScalar.lt_equiv] using hc
      rw [List.drop_eq_nil_of_le (by omega)]
      exact ⟨expo', lst, rfl, hexpo, hrel, hinv⟩

/-- A message path of `expo_of_parts`. -/
theorem ExOut.of_msg2 {α β : Type} {pers st lst} {R : α → β → Prop} {ar : arena.store.EStore}
    {m : Result (core.result.Result α frontend.olean.module.ExpoErr × arena.store.EStore)}
    {o s'} (hm : MsgLeaf ar m) (h : m = ok (o, s'))
    (hrel : AStateRel₀ pers (withStore st ar) lst) (hinv : AStateInv pers (withStore st ar))
    (t : String) : ExOut pers R (withStore st s') o (.ok (.error t, lst)) := by
  obtain ⟨⟨u, rfl⟩, e⟩ := hm o s' h
  cases e
  exact ⟨t, lst, rfl, hrel, hinv⟩

/-- **`expo_of_parts` is `expoOfParts`.** -/
theorem expo_of_parts_refines {pk bs r pers st lst} {priv_addr exp_addr : Std.U64}
    {cs : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {cs' : Array (CEntryF NIdx EIdx)}
    (hE : ∀ c st lst, RS pers ERel st lst (frontend.olean.reads.entry_at pk pers st.store bs r c)
      (entryAt (absPins pk) (absRegion bs r) c.val))
    (hr : RegionFits bs r) (hcs : List.Forall₂ ERel cs.val cs'.toList)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) {o s'}
    (h : frontend.olean.module.expo_of_parts pk pers st.store bs r priv_addr exp_addr cs = ok (o, s')) :
    ExOut pers ExpoRel (withStore st s') o
      ((expoOfParts (absPins pk) (absRegion bs r) (absWord priv_addr) (absWord exp_addr) cs').run lst) := by
  rw [frontend.olean.module.expo_of_parts] at h
  unfold expoOfParts
  peel h as o0, ho0
  have hs0 := module_skel_eq hr ho0
  clear ho0
  revert hs0
  generalize ConLeche.Frontend.Olean.moduleSkel (absRegion bs r) (absWord priv_addr) = y0
  intro hs0
  cases hs0 with
  | none => exact ExOut.of_msg2 (by msg_leaf) h hrel hinv _
  | @some sk skP hP =>
    dsimp only at h ⊢
    peel h as o1, ho1
    have hs1 := module_skel_eq hr ho1
    clear ho1
    revert hs1
    generalize ConLeche.Frontend.Olean.moduleSkel (absRegion bs r) (absWord exp_addr) = y1
    intro hs1
    cases hs1 with
    | none => exact ExOut.of_msg2 (by msg_leaf) h hrel hinv _
    | @some sk1 skE hE1 =>
      dsimp only at h ⊢
      peel h as priv_loc, hpl
      have hL := priv_loc_of_rel hpl
      peel h as priv_idx, hpi
      have hI := priv_idx_of_rel hcs hpi
      peel h as ex0, hex
      have hX := expo_fill_rel (cs := cs') (by simpa using hcs.length_eq) hex
      peel h as ⟨r1, ar1, expo1⟩, hloop
      rw [frontend.olean.module.expo_loop] at hloop
      have hlocs : sk.consts.val.map (fun x : Std.U64 => x.val) = skP.consts.toArray.toList := by
        rw [List.toList_toArray]
        exact hP.consts
      have hnl : sk.consts.val.length ≤ Std.Usize.max := by scalar_tac
      have hS := expo_loop_loop_refines hE hr hL hnl hI hlocs hcs _ 0#usize st lst ex0 _ r1 ar1 expo1
        (Nat.le_refl _) hX hrel hinv hloop
      have e1 : ((sk1.consts.val.drop (0#usize : Std.Usize).val).map (fun x : Std.U64 => x.val)) = skE.consts := by
        simpa using hE1.consts
      rw [e1, hP.consts] at hS
      cases r1 with
      | Ok u =>
        cases Result.ok_injective h
        exact hS
      | Err ee =>
        cases Result.ok_injective h
        cases ee <;> exact hS

/-! ## `check_views` -/

/-- A `bad_module` path: pure steps, ending in the error. -/
def CeLeaf {α : Type}
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore)) : Prop :=
  ∀ o s', m = ok (o, s') → ∃ ce, o = .Err ce ∧ absAErrKind ce = some .internal

theorem bad_module_kind {pers ar m what ce} (h : frontend.olean.module.bad_module pers ar m what = ok ce) :
    absAErrKind ce = some .internal := by
  rw [frontend.olean.module.bad_module] at h
  simp only [lift, bind_ok] at h
  peel h as _, _
  peel h as _, _
  peel h as _, _
  peel h as _, _
  peel h as _, _
  peel h as _, _
  rw [kernel.core_types.internal] at h
  cases Result.ok_injective h
  rfl

theorem CeLeaf.done {α : Type} {pers ar m} (v : alloc.vec.Vec Std.U32) :
    CeLeaf (α := α) (Std.bind (frontend.olean.module.bad_module pers ar m v) fun ce => ok (.Err ce, ar)) := by
  intro o s' h
  peel h as ce, hce
  cases Result.ok_injective h
  exact ⟨ce, rfl, bad_module_kind hce⟩

theorem CeLeaf.step {α δ : Type} {f : Result δ}
    {k : δ → Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore)}
    (h : ∀ a, CeLeaf (k a)) : CeLeaf (Std.bind f k) := by
  intro o s' hm
  obtain ⟨a, _, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a o s' h2

/-- A `bad_module` path. -/
macro "ce_leaf" : tactic =>
  `(tactic| repeat' first | exact CeLeaf.done _ | refine CeLeaf.step fun _ => ?_)

/-- A `bad_module` path `h` against the twin's `.internal`. -/
macro "ce_close " h:ident : tactic =>
  `(tactic| (obtain ⟨ce, e, hk⟩ := (show CeLeaf _ by ce_leaf) _ _ $h:ident
             subst e
             exact ConRon.Refine2.AErrSim.of_kind rfl hk rfl))

/-- **`check_views_module` is the module-system arm of `checkViews`.** -/
theorem check_views_module_refines {pk pers st lst} {m : arena.handle.NIdx} {f v s p} {m' : ConLeche.Name}
    {f' : ConLeche.Frontend.Olean.ModFiles} {v' : Arena.Frontend.Olean.AllViews} {s' p'}
    (hE : ∀ bs r c st lst, RS pers ERel st lst (frontend.olean.reads.entry_at pk pers st.store bs r c)
      (entryAt (absPins pk) (absRegion bs r) c.val))
    (hf : ModFilesRel f f') (hv : AllViewsRel v v') (hs : f.server = some s) (hp : f.private_part = some p)
    (hs' : f'.server = some s') (hp' : f'.private = some p') (hmod : f'.isModule = true) :
    CS pers ExpoRel st lst (frontend.olean.module.check_views_module pk pers st.store m f v s p)
      (Arena.Frontend.Olean.checkViews (absPins pk) m' f' v') := by
  intro hrel hinv o s1 h
  have es : s' = absPart s := by simpa [hs] using hs'.symm.trans hf.server
  have ep : p' = absPart p := by simpa [hp] using hp'.symm.trans hf.private
  subst es ep
  unfold Arena.Frontend.Olean.checkViews
  rw [hs', hp', hmod, hf.exported]
  dsimp only
  rw [ite_eq_left rfl]
  simp only [am_pure_bind]
  rw [frontend.olean.module.check_views_module] at h
  peel h as r0, hr0
  have e0 := region_of_parts3_eq hf.fitsE (hf.fitsS s hs) (hf.fitsP p hp) hr0
  cases r0 with
  | Err e =>
    cases Result.ok_injective h
    obtain ⟨hk, t, em⟩ := e0
    rw [em]
    exact ConRon.Refine2.AErrSim.of_kind rfl hk rfl
  | Ok b =>
    obtain ⟨em, hfit⟩ := e0
    rw [em]
    dsimp only at h ⊢
    rw [← hv.server.isModule, ← hv.private.isModule]
    have hcs := hv.private.constants
    by_cases h1 : v.server.is_module = true
    · rw [ite_eq_left h1] at h ⊢
      by_cases h2 : v.private_part.is_module = true
      · rw [ite_eq_left h2] at h ⊢
        peel h as ap, hap
        have eap := part_module_data_addr_eq hap
        peel h as i, hi
        have ei := part_module_data_addr_eq hi
        rw [← eap, ← ei]
        peel h as ⟨r1, ar1⟩, he1
        have hS1 := expo_of_parts_refines (hE _ _) hfit hcs hrel hinv he1
        cases r1 with
        | Ok x =>
          obtain ⟨b1, lst1, hy1, hb1, hrel1, hinv1⟩ := hS1
          rw [am_bind_ok hy1]
          peel h as i1, hi1
          rw [← part_module_data_addr_eq hi1]
          peel h as ⟨r2, ar2⟩, he2
          have hS2 := expo_of_parts_refines (st := withStore st ar1) (hE _ _) hfit hcs hrel1 hinv1 he2
          cases r2 with
          | Ok y =>
            obtain ⟨b2, lst2, hy2, -, hrel2, hinv2⟩ := hS2
            rw [am_bind_ok hy2]
            cases Result.ok_injective h
            exact ⟨b1, lst2, rfl, hb1, hrel2, hinv2⟩
          | Err ee =>
            cases ee with
            | Msg t =>
              obtain ⟨m2, lst2, hy2, -, -⟩ := hS2
              rw [am_bind_ok hy2]
              ce_close h
            | Err e =>
              cases Result.ok_injective h
              show AErrSim e _
              rw [StateT.run_bind]
              exact AErrSim.bind hS2 _
        | Err ee =>
          cases ee with
          | Err e =>
            cases Result.ok_injective h
            show AErrSim e _
            rw [StateT.run_bind]
            exact AErrSim.bind hS1 _
          | Msg t =>
            obtain ⟨m1, lst1, hy1, hrel1, hinv1⟩ := hS1
            rw [am_bind_ok hy1]
            peel h as i1, hi1
            rw [← part_module_data_addr_eq hi1]
            peel h as ⟨r2, ar2⟩, he2
            have hS2 := expo_of_parts_refines (st := withStore st ar1) (hE _ _) hfit hcs hrel1 hinv1 he2
            cases r2 with
            | Ok y =>
              obtain ⟨b2, lst2, hy2, -, -, -⟩ := hS2
              rw [am_bind_ok hy2]
              ce_close h
            | Err ee =>
              cases ee with
              | Msg t2 =>
                obtain ⟨m2, lst2, hy2, -, -⟩ := hS2
                rw [am_bind_ok hy2]
                ce_close h
              | Err e =>
                cases Result.ok_injective h
                show AErrSim e _
                rw [StateT.run_bind]
                exact AErrSim.bind hS2 _
      · rw [ite_eq_right h2] at h ⊢
        ce_close h
    · rw [ite_eq_right h1] at h ⊢
      ce_close h

/-- `expo_fill` at the private constants: the twin's `.same` for each. -/
theorem expo_same {v v'} (hv : AllViewsRel v v') {r}
    (h : frontend.olean.module.expo_fill (alloc.vec.Vec.len v.private_part.constants)
      frontend.olean.module.Expo.Same = ok r) :
    ExpoRel r (v'.private.constants.map fun _ => Expo.same) :=
  expo_fill_rel (by simpa using hv.private.constants.length_eq) h

/-- **`check_views` is `checkViews`.** -/
theorem check_views_refines {pk pers st lst} {m : arena.handle.NIdx} {f v} {m' : ConLeche.Name}
    {f' : ConLeche.Frontend.Olean.ModFiles} {v' : Arena.Frontend.Olean.AllViews}
    (hE : ∀ bs r c st lst, RS pers ERel st lst (frontend.olean.reads.entry_at pk pers st.store bs r c)
      (entryAt (absPins pk) (absRegion bs r) c.val))
    (hf : ModFilesRel f f') (hv : AllViewsRel v v') :
    CS pers ExpoRel st lst (frontend.olean.module.check_views pk pers st.store m f v)
      (Arena.Frontend.Olean.checkViews (absPins pk) m' f' v') := by
  intro hrel hinv o s1 h
  rw [frontend.olean.module.check_views] at h
  have es := hf.server
  have ep := hf.private
  cases hs : f.server with
  | none =>
    rw [hs] at h es
    dsimp only at h
    peel h as r, hr
    cases Result.ok_injective h
    unfold Arena.Frontend.Olean.checkViews
    simp only [es, Option.map_none]
    exact ⟨_, lst, rfl, expo_same hv hr, hrel, hinv⟩
  | some s =>
    rw [hs] at h es
    dsimp only at h
    cases hp : f.private_part with
    | none =>
      rw [hp] at h ep
      dsimp only at h
      peel h as r, hr
      cases Result.ok_injective h
      unfold Arena.Frontend.Olean.checkViews
      simp only [es, ep, Option.map_none, Option.map_some]
      exact ⟨_, lst, rfl, expo_same hv hr, hrel, hinv⟩
    | some p =>
      rw [hp] at h ep
      dsimp only at h
      peel h as b, hb
      have e := mod_files_is_module_eq hf hb
      cases b with
      | true =>
        rw [ite_eq_left rfl] at h
        exact check_views_module_refines hE hf hv hs hp (es.trans rfl) (ep.trans rfl) e.symm hrel hinv o s1 h
      | false =>
        rw [ite_eq_right (by simp)] at h
        peel h as r, hr
        cases Result.ok_injective h
        unfold Arena.Frontend.Olean.checkViews
        simp only [es, ep, Option.map_some, ← e]
        exact ⟨_, lst, rfl, expo_same hv hr, hrel, hinv⟩

end ConRon.Refine2.Frontend.Olean
