/-
# `ConRon.Refine2.Frontend.Olean.Module` — `olean/module.rs` against `Arena/Frontend/Olean/Module.lean`

**Task #142, Theorem 2.**  The comparisons of two stored constants are pure, and `BT` is the
judgement of one: whatever the Rust's test answers is the twin's boolean.  Handles compare
by `absNIdx`/`absEIdx`, strings by `name::str_eq` with `StrWF`.
-/
import ConRon.Refine2.Frontend.Olean.Skel
import ConRon.Arena.Frontend.Olean.Module

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.module (hints_eq rules_eq rules_eq_loop nidx_list_eq nidx_list_eq_loop
  u64_list_eq u64_list_eq_loop kinds_same entry_same hidden_kind expo_of)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConLeche.Frontend.Olean (CKindF CEntryF Expo hintsEq)
open ConRon.Arena
open ConRon.Arena.Frontend.Olean (rulesEq entrySame expoOf)
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

theorem rules_map {r : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)}
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
    rw [rules_map h1, rules_map h2]
    exact (BT.and (nidx_list_eq_bt _ _) <| BT.andc (u64_iff _ _) <| BT.andc (u64_iff _ _) <|
      BT.andc (u64_iff _ _) <| BT.andc (u64_iff _ _) <| BT.and (rules_eq_bt _ _) <|
      BT.andc (bool_iff _ _) <| BT.dec (bool_iff _ _)).of_eq (by simp only [kindsSameT, Bool.and_assoc])

/-- A stored constant, as the twin's. -/
abbrev ERel := EntryRel (N := arena.handle.NIdx) (E := arena.handle.EIdx) absNIdx absEIdx ValRel

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

end ConRon.Refine2.Frontend.Olean
