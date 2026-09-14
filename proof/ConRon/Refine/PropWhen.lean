/-
`ConRon.Refine.PropWhen` -- the refinement lemmas of
`crates/con-ron-core/src/kernel/prop_when.rs` against
`ConLeche/Kernel/PropWhen.lean` (DESIGN.md §3.5; P3.3 of §5, task #17).

**The sealed datum, refined through its public API.**  con-leche's `PropWhen`
is a one-field `structure` whose constructor *and* field are `private`,
wrapping an equally `private inductive PropWhenRepr`
(`ConLeche/Kernel/PropWhen.lean:378-413`): outside that module the type can be
held and passed but neither built nor matched.  The port seals its `enum`
the same way (Rust module privacy is Lean's `private`, task #9).

`ConRon/Refine/Abs.lean`'s `absPropWhen` therefore goes through the *public*
smart constructors `never` and `ifAllZero`, which by `PropWhen.casesZ`
(`:645-661`) name every value of the type: `Never ↦ never`,
`Always ↦ ifAllZero []`, `One`/`Two`/`Many ↦ ifAllZero` of the parameter list.
**No `import all ConLeche.Kernel.PropWhen` was needed** -- neither for the
abstraction nor for any proof here.  The exported equation battery
(`toList_ifAllZero`, `holds_ifAllZero`, `inter_ifAllZero`, `bindZ_ifAllZero`,
`ifAllZero_eq_iff`, `ifAllZero_ne_never`, `canon_eq_self`, `sorted_merge`,
`sorted_ext`, …) is exactly what the refinement needs, so the encapsulation
the module was designed for holds against this proof too.  The one place a
*definition* is unfolded is the sorted-list layer (`PropWhen.merge`,
`PropWhen.canon`, `PropWhen.bindZ.go`), whose bodies are ordinary public
`def`s with usable equation lemmas -- the `PropWhenRepr` matches never are.

**What canonicity costs and buys.**  `PropWhenWF` (`Abs.lean`) is the task-#5
style inductive predicate whose constructors are the port's four public
producers.  `wf_shape` turns a derivation into `WFShape`: well-formed names, a
strictly ascending abstracted parameter list (con-leche's `PropWhen.Sorted`),
and a `Many` that really holds more than two names.  That invariant is what
makes `to_list`, `has_params` and `beq` *exact* rather than
membership-correct, and it is established by tracing `if_all_zero` through
`canon`/`merge`/`of_sorted` -- which is why `prop_when::name_cmp` has to refine
`ConLeche.Name.cmp` (`:75-85`) first, and why *that* needs the code-point walk
`str_compare` to refine Lean's `compare : String → String → Ordering`
(`Init/Data/Ord/String.lean:35`, i.e. `compareOfLessAndEq` over
`List.Lex (· < ·)` on the character lists).

Shape, as fixed by task #5: **exact result on success**.  The two higher-order
arguments (`holds`'s valuation `φ : Name → Nat` and `bindZ`'s substitution
`f : Name → PropWhen`) are one-method trait dictionaries in the port (task #9,
pattern 1), so their lemmas carry a hypothesis relating the dictionary to the
Lean function.  `hash_pw` gets no lemma: DESIGN.md §3.2 -- `mixHash` is opaque
in the proofs and hash values only move memo entries between buckets.
-/
import ConRon.Refine.Name

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.PropWhen

/-! ## The code-point walk: `str_compare` against Lean's `Ord String` -/

def chr (c : Std.U32) : Char := Char.ofNat c.val

theorem chr_toNat {c : Std.U32} (h : Nat.isValidChar c.val) : (chr c).toNat = c.val := by
  simp [chr, Char.ofNat, Char.ofNatAux, Char.toNat, h]

theorem char_lt_iff (a b : Char) : a < b ↔ a.toNat < b.toNat := by
  show a.val < b.val ↔ _
  rw [UInt32.lt_iff_toNat_lt]
  rfl

theorem ofList_lt_ofList {l m : List Char} : String.ofList l < String.ofList m ↔ l < m := by
  show (String.ofList l).toList < (String.ofList m).toList ↔ l < m
  simp

theorem cmp_ofList (l m : List Char) :
    compare (String.ofList l) (String.ofList m) =
      if l < m then .lt else if l = m then .eq else .gt := by
  show String.compare _ _ = _
  rw [String.compare, compareOfLessAndEq]
  simp only [ofList_lt_ofList, String.ofList_inj]

theorem cmp_nil_nil : compare (String.ofList []) (String.ofList []) = .eq := by
  rw [cmp_ofList]; simp

theorem cmp_nil_cons (c : Char) (m : List Char) :
    compare (String.ofList []) (String.ofList (c :: m)) = .lt := by
  rw [cmp_ofList]; simp

theorem cmp_cons_nil (c : Char) (l : List Char) :
    compare (String.ofList (c :: l)) (String.ofList []) = .gt := by
  rw [cmp_ofList]; simp

theorem cmp_cons_lt {c d : Char} (h : c < d) (l m : List Char) :
    compare (String.ofList (c :: l)) (String.ofList (d :: m)) = .lt := by
  rw [cmp_ofList, if_pos (List.cons_lt_cons_iff.mpr (Or.inl h))]

theorem cmp_cons_gt {c d : Char} (h : d < c) (l m : List Char) :
    compare (String.ofList (c :: l)) (String.ofList (d :: m)) = .gt := by
  have hn := (char_lt_iff _ _).mp h
  have hne : c ≠ d := by rintro rfl; exact absurd hn (Nat.lt_irrefl _)
  rw [cmp_ofList, if_neg, if_neg]
  · simp [hne]
  · rw [List.cons_lt_cons_iff]
    rintro (h1 | ⟨rfl, _⟩)
    · exact Nat.lt_asymm hn ((char_lt_iff _ _).mp h1)
    · exact absurd hn (Nat.lt_irrefl _)

theorem cmp_cons_cons (c : Char) (l m : List Char) :
    compare (String.ofList (c :: l)) (String.ofList (c :: m))
      = compare (String.ofList l) (String.ofList m) := by
  rw [cmp_ofList, cmp_ofList]
  simp only [List.cons_lt_cons_self, List.cons.injEq, true_and]

theorem chr_lt {c d : Std.U32} (hc : Nat.isValidChar c.val) (hd : Nat.isValidChar d.val)
    (h : c.val < d.val) : chr c < chr d := by
  rw [char_lt_iff, chr_toNat hc, chr_toNat hd]; exact h

theorem chr_eq {c d : Std.U32} (h : c = d) : chr c = chr d := by rw [h]

theorem str_compare_from_refines {a b : alloc.vec.Vec Std.U32}
    (ha : StrWF a) (hb : StrWF b) :
    ∀ k (i : Std.Usize), a.length - i.val ≤ k → ∀ o : prop_when.Ordering,
      prop_when.str_compare_from a b i = ok o →
      compare (String.ofList ((a.val.drop i.val).map chr))
              (String.ofList ((b.val.drop i.val).map chr)) = absOrdering o := by
  intro k
  induction k with
  | zero =>
    intro i hk o h
    rw [prop_when.str_compare_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
    rw [List.drop_eq_nil_of_le (show a.val.length ≤ i.val by scalar_tac)]
    by_cases hbl : i.val ≥ b.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
      simp only [Result.ok.injEq] at h; subst h
      rw [List.drop_eq_nil_of_le (show b.val.length ≤ i.val by scalar_tac)]
      simp only [List.map_nil, absOrdering]
      exact cmp_nil_nil
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
      rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      simp only [Result.ok.injEq] at h; subst h
      rw [List.drop_eq_getElem_cons (show i.val < b.val.length by scalar_tac)]
      simp only [List.map_nil, List.map_cons, absOrdering]
      exact cmp_nil_cons _ _
  | succ k ih =>
    intro i hk o h
    rw [prop_when.str_compare_from.eq_def] at h; simp only [] at h
    by_cases hal : i.val ≥ a.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      rw [List.drop_eq_nil_of_le (show a.val.length ≤ i.val by scalar_tac)]
      by_cases hbl : i.val ≥ b.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
        simp only [Result.ok.injEq] at h; subst h
        rw [List.drop_eq_nil_of_le (show b.val.length ≤ i.val by scalar_tac)]
        simp only [List.map_nil, absOrdering]
        exact cmp_nil_nil
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
        rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
        simp only [Result.ok.injEq] at h; subst h
        rw [List.drop_eq_getElem_cons (show i.val < b.val.length by scalar_tac)]
        simp only [List.map_nil, List.map_cons, absOrdering]
        exact cmp_nil_cons _ _
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      have hai : i.val < a.val.length := by scalar_tac
      rw [List.drop_eq_getElem_cons hai]
      by_cases hbl : i.val ≥ b.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
        simp only [Result.ok.injEq] at h; subst h
        rw [List.drop_eq_nil_of_le (show b.val.length ≤ i.val by scalar_tac)]
        simp only [List.map_nil, List.map_cons, absOrdering]
        exact cmp_cons_nil _ _
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
        have hbi : i.val < b.val.length := by scalar_tac
        rw [List.drop_eq_getElem_cons hbi]
        have hva : Nat.isValidChar a.val[i.val].val := ha _ (List.getElem_mem hai)
        have hvb : Nat.isValidChar b.val[i.val].val := hb _ (List.getElem_mem hbi)
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec a i hai)
        obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b i hbi)
        subst hyv; subst hzv
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz,
          Result.ok.injEq, exists_eq_left'] at h
        split at h
        · rename_i hlt
          simp only [Result.ok.injEq] at h; subst h
          simp only [List.map_cons, absOrdering]
          exact cmp_cons_lt (chr_lt hva hvb (by scalar_tac)) _ _
        · split at h
          · rename_i hgt
            simp only [Result.ok.injEq] at h; subst h
            simp only [List.map_cons, absOrdering]
            exact cmp_cons_gt (chr_lt hvb hva (by scalar_tac)) _ _
          · rename_i hnlt hngt
            have heq : a.val[i.val] = b.val[i.val] := by scalar_tac
            have hmax : i.val + 1 ≤ Std.Usize.max := by have := a.slice.property; scalar_tac
            obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
            simp only [hw, bind_tc_ok] at h
            simp only [List.map_cons]
            rw [chr_eq heq, cmp_cons_cons, ← hwv]
            exact ih w (by scalar_tac) o h

theorem absString_eq (s : alloc.vec.Vec Std.U32) :
    absString s = String.ofList (s.val.map chr) := rfl

theorem str_compare_refines {a b : alloc.vec.Vec Std.U32} (ha : StrWF a) (hb : StrWF b)
    {o : prop_when.Ordering} (h : prop_when.str_compare a b = ok o) :
    compare (absString a) (absString b) = absOrdering o := by
  rw [prop_when.str_compare] at h
  have hc := str_compare_from_refines ha hb a.length 0#usize (by scalar_tac) o h
  rw [absString_eq, absString_eq]
  simpa only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] using hc

theorem cmp_nat (m n : Nat) : compare m n = if m < n then .lt else if m = n then .eq else .gt :=
  rfl

theorem nat_compare_refines {m n : Std.U64} {o : prop_when.Ordering}
    (h : prop_when.nat_compare m n = ok o) : compare m.val n.val = absOrdering o := by
  rw [prop_when.nat_compare] at h
  rw [cmp_nat]
  split at h
  · rename_i hlt
    simp only [Result.ok.injEq] at h; subst h
    rw [if_pos (show m.val < n.val by scalar_tac)]; rfl
  · split at h
    · rename_i hgt
      simp only [Result.ok.injEq] at h; subst h
      rw [if_neg (show ¬ m.val < n.val by scalar_tac),
        if_neg (show ¬ m.val = n.val by scalar_tac)]; rfl
    · rename_i hnlt hngt
      simp only [Result.ok.injEq] at h; subst h
      rw [if_neg (show ¬ m.val < n.val by scalar_tac),
        if_pos (show m.val = n.val by scalar_tac)]; rfl

theorem ord_then_refines {x y : prop_when.Ordering} {o : prop_when.Ordering}
    (h : prop_when.ord_then x y = ok o) :
    (absOrdering x).then (absOrdering y) = absOrdering o := by
  cases x <;> rw [prop_when.ord_then] at h <;> simp only [Result.ok.injEq] at h <;>
    subst h <;> rfl

theorem name_cmp_refines_aux {a : name.Name} (ha : NameWF a) :
    ∀ b, NameWF b → ∀ o : prop_when.Ordering, prop_when.name_cmp a b = ok o →
      ConLeche.Name.cmp (absName a) (absName b) = absOrdering o := by
  induction ha with
  | @anonymous n h =>
    rw [name_anonymous_inv h]
    intro b hb o hc
    rw [prop_when.name_cmp.eq_def] at hc
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb with
    | Anonymous =>
      simp only [arc_deref_eq, bind_tc_ok, name.Name._0._simpLemma_,
        name.NameNode.kind._simpLemma_, Result.ok.injEq] at hc
      subst hc; simp [ConLeche.Name.cmp, absOrdering]
    | Str q t =>
      simp only [arc_deref_eq, bind_tc_ok, name.Name._0._simpLemma_,
        name.NameNode.kind._simpLemma_, Result.ok.injEq] at hc
      subst hc; simp [ConLeche.Name.cmp, absOrdering]
    | Num q k =>
      simp only [arc_deref_eq, bind_tc_ok, name.Name._0._simpLemma_,
        name.NameNode.kind._simpLemma_, Result.ok.injEq] at hc
      subst hc; simp [ConLeche.Name.cmp, absOrdering]
  | @str pre s n hpre hs hmk ih =>
    obtain ⟨hh, rfl⟩ := mk_str_inv hmk
    intro b hb o hc
    rw [prop_when.name_cmp.eq_def] at hc
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb with
    | Anonymous =>
      simp only [arc_deref_eq, bind_tc_ok, name.Name._0._simpLemma_,
        name.NameNode.kind._simpLemma_, Result.ok.injEq] at hc
      subst hc; simp [ConLeche.Name.cmp, absOrdering]
    | Num q k =>
      simp only [arc_deref_eq, bind_tc_ok, name.Name._0._simpLemma_,
        name.NameNode.kind._simpLemma_, Result.ok.injEq] at hc
      subst hc; simp [ConLeche.Name.cmp, absOrdering]
    | Str q t =>
      simp only [arc_deref_eq, bind_tc_ok, name.Name._0._simpLemma_,
        name.NameNode.kind._simpLemma_, bind_eq_ok_iff] at hc
      obtain ⟨o1, ho1, o2, ho2, hthen⟩ := hc
      obtain ⟨hq, ht, hqt⟩ : NameWF q ∧ StrWF t ∧ True := by
        cases hb with
        | @anonymous n' h' => have hx := name_anonymous_inv h'; simp at hx
        | @str p' s' n' hp' hs' h' =>
          obtain ⟨hh', he⟩ := mk_str_inv h'
          rw [name.Name.mk.injEq, name.NameNode.mk.injEq] at he
          obtain ⟨-, he2⟩ := he
          rw [name.NameKind.Str.injEq] at he2
          obtain ⟨rfl, rfl⟩ := he2
          exact ⟨hp', hs', trivial⟩
        | @num p' m' n' hp' h' =>
          obtain ⟨hh', he⟩ := mk_num_inv h'
          rw [name.Name.mk.injEq, name.NameNode.mk.injEq] at he
          simp at he
      rw [absName_mk, absName_mk, absNameKind, absNameKind, ConLeche.Name.cmp,
        ih q hq o1 ho1, str_compare_refines hs ht ho2]
      exact ord_then_refines hthen
  | @num pre m n hpre hmk ih =>
    obtain ⟨hh, rfl⟩ := mk_num_inv hmk
    intro b hb o hc
    rw [prop_when.name_cmp.eq_def] at hc
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb with
    | Anonymous =>
      simp only [arc_deref_eq, bind_tc_ok, name.Name._0._simpLemma_,
        name.NameNode.kind._simpLemma_, Result.ok.injEq] at hc
      subst hc; simp [ConLeche.Name.cmp, absOrdering]
    | Str q t =>
      simp only [arc_deref_eq, bind_tc_ok, name.Name._0._simpLemma_,
        name.NameNode.kind._simpLemma_, Result.ok.injEq] at hc
      subst hc; simp [ConLeche.Name.cmp, absOrdering]
    | Num q k =>
      simp only [arc_deref_eq, bind_tc_ok, name.Name._0._simpLemma_,
        name.NameNode.kind._simpLemma_, bind_eq_ok_iff] at hc
      obtain ⟨o1, ho1, o2, ho2, hthen⟩ := hc
      have hq : NameWF q := by
        cases hb with
        | @anonymous n' h' => have hx := name_anonymous_inv h'; simp at hx
        | @str p' s' n' hp' hs' h' =>
          obtain ⟨hh', he⟩ := mk_str_inv h'
          rw [name.Name.mk.injEq, name.NameNode.mk.injEq] at he
          simp at he
        | @num p' m' n' hp' h' =>
          obtain ⟨hh', he⟩ := mk_num_inv h'
          rw [name.Name.mk.injEq, name.NameNode.mk.injEq] at he
          obtain ⟨-, he2⟩ := he
          rw [name.NameKind.Num.injEq] at he2
          obtain ⟨rfl, rfl⟩ := he2
          exact hp'
      rw [absName_mk, absName_mk, absNameKind, absNameKind, ConLeche.Name.cmp,
        ih q hq o1 ho1, nat_compare_refines ho2]
      exact ord_then_refines hthen

/-- `ConLeche/Kernel/PropWhen.lean:75-85` -- `prop_when::name_cmp` refines
`ConLeche.Name.cmp`, the strict total order the canonical form is canonical
for.  Well-formedness is needed on both sides: `absString` is order-preserving
only where every stored code point is a valid `Char` (`StrWF`). -/
theorem name_cmp_refines {a b : name.Name} (ha : NameWF a) (hb : NameWF b)
    {o : prop_when.Ordering} (h : prop_when.name_cmp a b = ok o) :
    ConLeche.Name.cmp (absName a) (absName b) = absOrdering o :=
  name_cmp_refines_aux ha b hb o h

/-! ## The sorted-list layer -/

theorem merge_lt {x y : ConLeche.Name} {A B : List ConLeche.Name}
    (h : ConLeche.Name.cmp x y = .lt) :
    ConLeche.PropWhen.merge (x :: A) (y :: B) = x :: ConLeche.PropWhen.merge A (y :: B) := by
  rw [ConLeche.PropWhen.merge]; simp [h]

theorem merge_eq {x y : ConLeche.Name} {A B : List ConLeche.Name}
    (h : ConLeche.Name.cmp x y = .eq) :
    ConLeche.PropWhen.merge (x :: A) (y :: B) = x :: ConLeche.PropWhen.merge A B := by
  rw [ConLeche.PropWhen.merge]; simp [h]

theorem merge_gt {x y : ConLeche.Name} {A B : List ConLeche.Name}
    (h : ConLeche.Name.cmp x y = .gt) :
    ConLeche.PropWhen.merge (x :: A) (y :: B) = y :: ConLeche.PropWhen.merge (x :: A) B := by
  rw [ConLeche.PropWhen.merge]; simp [h]

theorem append_from_val (xs : alloc.vec.Vec name.Name) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec name.Name),
      xs.length - i.val ≤ k → prop_when.append_from xs i out = ok v →
      v.val = out.val ++ xs.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [prop_when.append_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
    simp only [Result.ok.injEq] at h; subst h
    rw [List.drop_eq_nil_of_le (show xs.val.length ≤ i.val by scalar_tac)]
    simp
  | succ k ih =>
    intro i out v hk h
    rw [prop_when.append_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ xs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      simp only [Result.ok.injEq] at h; subst h
      rw [List.drop_eq_nil_of_le (show xs.val.length ≤ i.val by scalar_tac)]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      have hi : i.val < xs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := xs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec xs i hi)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw, name_dup_eq,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨out1, hout1, h⟩ := h
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1,
        List.drop_eq_getElem_cons hi, hwv]
      simp

theorem names_copy_val {xs v : alloc.vec.Vec name.Name}
    (h : prop_when.names_copy xs = ok v) : v.val = xs.val := by
  rw [prop_when.names_copy] at h
  have hv := append_from_val xs xs.length 0#usize _ v (by scalar_tac) h
  simpa [alloc.vec.Vec.new] using hv

theorem merge_from_abs {as_ bs : alloc.vec.Vec name.Name}
    (has : NamesWF as_) (hbs : NamesWF bs) :
    ∀ k : Nat, ∀ (i j : Std.Usize) (out v : alloc.vec.Vec name.Name),
      (as_.length - i.val) + (bs.length - j.val) ≤ k → NamesWF out →
      prop_when.merge_from as_ i bs j out = ok v →
      absNames v = absNames out ++
        ConLeche.PropWhen.merge ((as_.val.drop i.val).map absName)
                                ((bs.val.drop j.val).map absName)
      ∧ NamesWF v := by
  have hnames : ∀ (out xs : alloc.vec.Vec name.Name) (i : Std.Usize)
      (v : alloc.vec.Vec name.Name), NamesWF out → NamesWF xs →
      v.val = out.val ++ xs.val.drop i.val → NamesWF v := by
    intro out xs i v hout hxs hv n hn
    rw [hv, List.mem_append] at hn
    exact hn.elim (hout n) (fun hd => hxs n (List.mem_of_mem_drop hd))
  intro k
  induction k with
  | zero =>
    intro i j out v hk hout h
    rw [prop_when.merge_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len as_ by scalar_tac)] at h
    have hv := append_from_val bs bs.length j out v (by scalar_tac) h
    refine ⟨?_, hnames out bs j v hout hbs hv⟩
    rw [absNames, absNames, hv,
      List.drop_eq_nil_of_le (show as_.val.length ≤ i.val by scalar_tac)]
    simp
  | succ k ih =>
    intro i j out v hk hout h
    rw [prop_when.merge_from.eq_def] at h; simp only [] at h
    by_cases hal : i.val ≥ as_.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len as_ by scalar_tac)] at h
      have hv := append_from_val bs bs.length j out v (by scalar_tac) h
      refine ⟨?_, hnames out bs j v hout hbs hv⟩
      rw [absNames, absNames, hv,
        List.drop_eq_nil_of_le (show as_.val.length ≤ i.val by scalar_tac)]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len as_ by scalar_tac)] at h
      have hai : i.val < as_.val.length := by scalar_tac
      by_cases hbl : j.val ≥ bs.val.length
      · rw [if_pos (show j ≥ alloc.vec.Vec.len bs by scalar_tac)] at h
        have hv := append_from_val as_ as_.length i out v (by scalar_tac) h
        refine ⟨?_, hnames out as_ i v hout has hv⟩
        rw [absNames, absNames, hv,
          List.drop_eq_nil_of_le (show bs.val.length ≤ j.val by scalar_tac)]
        simp
      · rw [if_neg (show ¬ j ≥ alloc.vec.Vec.len bs by scalar_tac)] at h
        have hbj : j.val < bs.val.length := by scalar_tac
        have hwfa : NameWF as_.val[i.val] := has _ (List.getElem_mem hai)
        have hwfb : NameWF bs.val[j.val] := hbs _ (List.getElem_mem hbj)
        have hmaxi : i.val + 1 ≤ Std.Usize.max := by have := as_.slice.property; scalar_tac
        have hmaxj : j.val + 1 ≤ Std.Usize.max := by have := bs.slice.property; scalar_tac
        obtain ⟨wi, hwi, hwiv⟩ := usize_add_ok hmaxi
        obtain ⟨wj, hwj, hwjv⟩ := usize_add_ok hmaxj
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec as_ i hai)
        obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec bs j hbj)
        subst hyv; subst hzv
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz,
          Result.ok.injEq, exists_eq_left', name_dup_eq, hwi, hwj] at h
        obtain ⟨o, ho, h⟩ := h
        have hcmp := name_cmp_refines hwfa hwfb ho
        rw [List.drop_eq_getElem_cons hai, List.drop_eq_getElem_cons hbj,
          List.map_cons, List.map_cons]
        cases o with
        | Lt =>
          simp only [bind_eq_ok_iff, bind_tc_ok] at h
          obtain ⟨out1, hout1, h⟩ := h
          have hout1WF : NamesWF out1 := by
            intro n hn
            rw [vec_push_val hout1, List.mem_append, List.mem_singleton] at hn
            exact hn.elim (hout n) (fun he => he ▸ hwfa)
          obtain ⟨hrec, hvWF⟩ := ih wi j out1 v (by scalar_tac) hout1WF h
          refine ⟨?_, hvWF⟩
          rw [hrec, merge_lt (by simpa [absOrdering] using hcmp), absNames, absNames,
            vec_push_val hout1, hwiv, List.drop_eq_getElem_cons hbj, List.map_cons]
          simp
        | Eq =>
          simp only [bind_eq_ok_iff, bind_tc_ok] at h
          obtain ⟨out1, hout1, h⟩ := h
          have hout1WF : NamesWF out1 := by
            intro n hn
            rw [vec_push_val hout1, List.mem_append, List.mem_singleton] at hn
            exact hn.elim (hout n) (fun he => he ▸ hwfa)
          obtain ⟨hrec, hvWF⟩ := ih wi wj out1 v (by scalar_tac) hout1WF h
          refine ⟨?_, hvWF⟩
          rw [hrec, merge_eq (by simpa [absOrdering] using hcmp), absNames, absNames,
            vec_push_val hout1, hwiv, hwjv]
          simp
        | Gt =>
          simp only [bind_eq_ok_iff, bind_tc_ok] at h
          obtain ⟨out1, hout1, h⟩ := h
          have hout1WF : NamesWF out1 := by
            intro n hn
            rw [vec_push_val hout1, List.mem_append, List.mem_singleton] at hn
            exact hn.elim (hout n) (fun he => he ▸ hwfb)
          obtain ⟨hrec, hvWF⟩ := ih i wj out1 v (by scalar_tac) hout1WF h
          refine ⟨?_, hvWF⟩
          rw [hrec, merge_gt (by simpa [absOrdering] using hcmp), absNames, absNames,
            vec_push_val hout1, hwjv, List.drop_eq_getElem_cons hai, List.map_cons]
          simp

theorem merge_abs {as_ bs v : alloc.vec.Vec name.Name}
    (has : NamesWF as_) (hbs : NamesWF bs) (h : prop_when.merge as_ bs = ok v) :
    absNames v = ConLeche.PropWhen.merge (absNames as_) (absNames bs) ∧ NamesWF v := by
  rw [prop_when.merge] at h
  obtain ⟨he, hwf⟩ := merge_from_abs has hbs (as_.length + bs.length) 0#usize 0#usize
    _ v (by scalar_tac) (by intro n hn; simp [alloc.vec.Vec.new] at hn) h
  refine ⟨?_, hwf⟩
  simpa [absNames, alloc.vec.Vec.new,
    show (0#usize : Std.Usize).val = 0 from rfl] using he

theorem canon_from_abs {ps : alloc.vec.Vec name.Name} (hps : NamesWF ps) :
    ∀ k : Nat, ∀ (i : Std.Usize) (v : alloc.vec.Vec name.Name),
      ps.length - i.val ≤ k → prop_when.canon_from ps i = ok v →
      absNames v = ConLeche.PropWhen.canon ((ps.val.drop i.val).map absName) ∧ NamesWF v := by
  intro k
  induction k with
  | zero =>
    intro i v hk h
    rw [prop_when.canon_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
    simp only [Result.ok.injEq] at h; subst h
    rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
    exact ⟨by simp [absNames, alloc.vec.Vec.new], by intro n hn; simp [alloc.vec.Vec.new] at hn⟩
  | succ k ih =>
    intro i v hk h
    rw [prop_when.canon_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ ps.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      simp only [Result.ok.injEq] at h; subst h
      rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
      exact ⟨by simp [absNames, alloc.vec.Vec.new], by intro n hn; simp [alloc.vec.Vec.new] at hn⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      have hi : i.val < ps.val.length := by scalar_tac
      have hwf : NameWF ps.val[i.val] := hps _ (List.getElem_mem hi)
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hi)
      subst hyv
      simp only [hw, bind_tc_ok, alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy] at h
      obtain ⟨rest, hrest, sg, hsg, hmg⟩ := h
      obtain ⟨hrestE, hrestWF⟩ := ih w rest (by scalar_tac) hrest
      have hsgV : sg.val = [ps.val[i.val]] := by
        simp only [name.singleton, bind_eq_ok_iff, name_dup_eq, Result.ok.injEq,
          exists_eq_left'] at hsg
        rw [vec_push_val hsg]; simp [alloc.vec.Vec.new]
      have hsgE : absNames sg = [absName ps.val[i.val]] := by
        rw [absNames, hsgV]; simp
      have hsgWF : NamesWF sg := by
        intro n hn
        rw [hsgV, List.mem_singleton] at hn
        exact hn ▸ hwf
      obtain ⟨hmE, hmWF⟩ := merge_abs hsgWF hrestWF hmg
      refine ⟨?_, hmWF⟩
      rw [hmE, hsgE, hrestE, hwv, List.drop_eq_getElem_cons hi, List.map_cons,
        ConLeche.PropWhen.canon_cons]

theorem canon_abs {ps v : alloc.vec.Vec name.Name} (hps : NamesWF ps)
    (h : prop_when.canon ps = ok v) :
    absNames v = ConLeche.PropWhen.canon (absNames ps) ∧ NamesWF v := by
  rw [prop_when.canon] at h
  obtain ⟨he, hwf⟩ := canon_from_abs hps ps.length 0#usize v (by scalar_tac) h
  exact ⟨by simpa [absNames, show (0#usize : Std.Usize).val = 0 from rfl] using he, hwf⟩

/-! ## The sealed representation -/

theorem list_len_one {α : Type} {l : List α} (h : l.length = 1) : ∃ a, l = [a] := by
  match l, h with
  | [a], _ => exact ⟨a, rfl⟩

theorem list_len_two {α : Type} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- The parameter list a Rust representation holds -- what `to_list` returns. -/
def reprList : prop_when.PropWhenRepr → List name.Name
  | .Never => []
  | .Always => []
  | .One p => [p]
  | .Two pq => [pq.1, pq.2]
  | .Many ps => ps.val

@[simp] theorem of_repr_eq (r : prop_when.PropWhenRepr) :
    prop_when.of_repr r = ok { repr := r } := rfl

/-- `prop_when::dup` is the identity in the model: every arm either rebuilds a
payload-free constructor, `dup`s a `Name`, or clones a handle -- and
`Arc::clone` is the identity (DESIGN.md §3.2).  Since task #90 the `Two` and
`Many` payloads sit *behind* the handle, so both are one `ptr::clone` and the
old `names_copy` spine walk of the `Many` arm is gone. -/
theorem dup_eq {pw c : prop_when.PropWhen} (h : prop_when.dup pw = ok c) : c = pw := by
  obtain ⟨r⟩ := pw
  cases r <;>
    simp only [prop_when.dup, of_repr_eq, name_dup_eq, ptr_clone_eq, bind_tc_ok,
      Result.ok.injEq] at h <;>
    exact h.symm

theorem to_list_val {pw : prop_when.PropWhen} {v : alloc.vec.Vec name.Name}
    (h : prop_when.to_list pw = ok v) : v.val = reprList pw.repr := by
  obtain ⟨r⟩ := pw
  cases r with
  | Never =>
    simp only [prop_when.to_list, Result.ok.injEq] at h
    rw [← h]; simp [reprList, alloc.vec.Vec.new]
  | Always =>
    simp only [prop_when.to_list, Result.ok.injEq] at h
    rw [← h]; simp [reprList, alloc.vec.Vec.new]
  | One p =>
    simp only [prop_when.to_list, name.singleton, bind_eq_ok_iff, name_dup_eq,
      Result.ok.injEq, exists_eq_left'] at h
    rw [vec_push_val h]; simp [reprList, alloc.vec.Vec.new]
  | Two pq =>
    obtain ⟨p, q⟩ := pq
    simp only [prop_when.to_list, bind_arc_deref, uncurry_apply_pair, bind_eq_ok_iff,
      name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨w, hw, h⟩ := h
    rw [vec_push_val h, vec_push_val hw]; simp [reprList, alloc.vec.Vec.new]
  | Many ps =>
    simp only [prop_when.to_list, bind_arc_deref] at h
    rw [names_copy_val h]; simp [reprList]

/-- The abstraction, read off the representation: away from `Never` every
datum abstracts to `ifAllZero` of its parameter list.  No well-formedness
needed -- `ifAllZero` normalizes. -/
theorem absPropWhen_eq_ifAllZero {pw : prop_when.PropWhen} (h : pw.repr ≠ .Never) :
    absPropWhen pw = .ifAllZero ((reprList pw.repr).map absName) := by
  obtain ⟨r⟩ := pw
  cases r <;> simp_all [absPropWhen, absPropWhenRepr, reprList, absNames]

theorem absPropWhen_never {pw : prop_when.PropWhen} (h : pw.repr = .Never) :
    absPropWhen pw = .never := by
  obtain ⟨r⟩ := pw; cases r <;> simp_all [absPropWhen, absPropWhenRepr]

theorem repr_never_of_abs_never {pw : prop_when.PropWhen}
    (h : absPropWhen pw = .never) : pw.repr = .Never := by
  obtain ⟨r⟩ := pw
  cases r
  · rfl
  all_goals
    exfalso
    simp only [absPropWhen, absPropWhenRepr] at h
    exact ConLeche.PropWhen.ifAllZero_ne_never _ h

/-! ## The canonical shape of a well-formed datum

`PropWhenWF` says "built by the port's own producers"; `WFShape` is what that
buys, and it is the only thing the refinement lemmas below use: the
representation's parameter list carries well-formed names, is strictly
ascending under `ConLeche.Name.cmp` once abstracted (which is con-leche's
`PropWhen.Sorted`, the representation invariant of `PropWhen.lean:360-384`),
and a `Many` really holds more than two of them. -/
def WFShape (pw : prop_when.PropWhen) : Prop :=
  (∀ n ∈ reprList pw.repr, NameWF n) ∧
  ConLeche.PropWhen.Sorted ((reprList pw.repr).map absName) ∧
  (∀ ps, pw.repr = .Many ps → 2 < ps.val.length)

theorem WFShape.namesWF {pw} (h : WFShape pw) : ∀ n ∈ reprList pw.repr, NameWF n := h.1

theorem WFShape.sorted {pw} (h : WFShape pw) :
    ConLeche.PropWhen.Sorted ((reprList pw.repr).map absName) := h.2.1

/-- The payoff: a well-formed datum's `to_list` is exactly con-leche's
`toList` of its abstraction. -/
theorem wfShape_toList {pw} (h : WFShape pw) :
    (absPropWhen pw).toList = (reprList pw.repr).map absName := by
  by_cases hn : pw.repr = .Never
  · rw [absPropWhen_never hn, ConLeche.PropWhen.toList_never, hn]; simp [reprList]
  · rw [absPropWhen_eq_ifAllZero hn, ConLeche.PropWhen.toList_ifAllZero,
      ConLeche.PropWhen.canon_eq_self h.sorted]

theorem never_shape {pw} (h : prop_when.never = ok pw) : WFShape pw ∧ pw.repr = .Never := by
  rw [prop_when.never, of_repr_eq, Result.ok.injEq] at h
  subst h
  exact ⟨⟨by simp [reprList], by simp [reprList, ConLeche.PropWhen.Sorted],
    by intro ps hps; simp at hps⟩, rfl⟩

/-- `prop_when::of_sorted` hands its argument straight through: the
representation's parameter list *is* the list it was given.  Unconditional --
the caller owes the sortedness (`PropWhen.lean:480-487`). -/
theorem of_sorted_reprList {qs : alloc.vec.Vec name.Name} {pw : prop_when.PropWhen}
    (h : prop_when.of_sorted qs = ok pw) :
    reprList pw.repr = qs.val ∧ pw.repr ≠ .Never ∧
      (∀ ps, pw.repr = .Many ps → 2 < ps.val.length) := by
  rw [prop_when.of_sorted.eq_def] at h; simp only [] at h
  by_cases h0 : qs.val.length = 0
  · rw [if_pos (show alloc.vec.Vec.len qs = 0#usize by scalar_tac), of_repr_eq,
      Result.ok.injEq] at h
    subst h
    refine ⟨?_, by simp, by intro ps hps; simp at hps⟩
    rw [reprList]
    exact (List.eq_nil_iff_length_eq_zero.mpr h0).symm
  · rw [if_neg (show ¬ alloc.vec.Vec.len qs = 0#usize by scalar_tac)] at h
    by_cases h1 : qs.val.length = 1
    · rw [if_pos (show alloc.vec.Vec.len qs = 1#usize by scalar_tac)] at h
      obtain ⟨x, hx⟩ := list_len_one h1
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec qs 0#usize (by scalar_tac))
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, name_dup_eq,
        of_repr_eq, Result.ok.injEq, exists_eq_left'] at h
      subst h
      refine ⟨?_, by simp, by intro ps hps; simp at hps⟩
      rw [reprList, hyv]
      simp [hx]
    · rw [if_neg (show ¬ alloc.vec.Vec.len qs = 1#usize by scalar_tac)] at h
      by_cases h2 : qs.val.length = 2
      · rw [if_pos (show alloc.vec.Vec.len qs = 2#usize by scalar_tac)] at h
        obtain ⟨x, x', hx⟩ := list_len_two h2
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec qs 0#usize (by scalar_tac))
        obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec qs 1#usize (by scalar_tac))
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz, name_dup_eq,
          ptr_new_eq, of_repr_eq, Result.ok.injEq, exists_eq_left'] at h
        subst h
        refine ⟨?_, by simp, by intro ps hps; simp at hps⟩
        rw [reprList, hyv, hzv]
        simp [hx]
      · rw [if_neg (show ¬ alloc.vec.Vec.len qs = 2#usize by scalar_tac)] at h
        simp only [ptr_new_eq, bind_tc_ok, of_repr_eq, Result.ok.injEq] at h
        subst h
        refine ⟨rfl, by simp, ?_⟩
        intro ps hps
        simp only [prop_when.PropWhenRepr.Many.injEq] at hps
        subst hps
        omega

theorem of_sorted_shape {qs : alloc.vec.Vec name.Name} {pw : prop_when.PropWhen}
    (hqs : NamesWF qs) (hsorted : ConLeche.PropWhen.Sorted (absNames qs))
    (h : prop_when.of_sorted qs = ok pw) :
    WFShape pw ∧ pw.repr ≠ .Never ∧ reprList pw.repr = qs.val := by
  obtain ⟨hl, hne, hmany⟩ := of_sorted_reprList h
  exact ⟨⟨by rw [hl]; exact hqs, by rw [hl]; exact hsorted, hmany⟩, hne, hl⟩

theorem of_sorted_abs {qs : alloc.vec.Vec name.Name} {pw : prop_when.PropWhen}
    (h : prop_when.of_sorted qs = ok pw) :
    absPropWhen pw = .ifAllZero (absNames qs) := by
  obtain ⟨hl, hne, -⟩ := of_sorted_reprList h
  rw [absPropWhen_eq_ifAllZero hne, hl, absNames]

/-! ## The smart constructors -/

theorem sorted_nil : ConLeche.PropWhen.Sorted ([] : List ConLeche.Name) := by
  simp [ConLeche.PropWhen.Sorted]

theorem sorted_one (x : ConLeche.Name) : ConLeche.PropWhen.Sorted [x] := by
  simp [ConLeche.PropWhen.Sorted]

theorem sorted_two {x y : ConLeche.Name} (h : ConLeche.Name.cmp x y = .lt) :
    ConLeche.PropWhen.Sorted [x, y] := by
  simp [ConLeche.PropWhen.Sorted, List.pairwise_cons, ConLeche.Name.lt_def, h]

/-- `ConLeche/Kernel/PropWhen.lean:489-495` -- `prop_when::two_prime` refines
`PropWhen.two'`: the ordered pair datum, one comparison and no list cell.  The
fourth conjunct is `PropWhen.toList_two'`, which `to_list`/`inter` need. -/
theorem two_prime_shape {p q : name.Name} {pw : prop_when.PropWhen}
    (hp : NameWF p) (hq : NameWF q) (h : prop_when.two_prime p q = ok pw) :
    WFShape pw ∧ pw.repr ≠ .Never ∧
      absPropWhen pw = .ifAllZero [absName p, absName q] ∧
      (reprList pw.repr).map absName
        = ConLeche.PropWhen.merge [absName p] [absName q] := by
  rw [prop_when.two_prime] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  have hcmp := name_cmp_refines hp hq ho
  cases o with
  | Lt =>
    simp only [name_dup_eq, ptr_new_eq, bind_tc_ok, of_repr_eq, Result.ok.injEq] at h
    subst h
    have hlt : ConLeche.Name.cmp (absName p) (absName q) = .lt := by
      simpa [absOrdering] using hcmp
    refine ⟨⟨?_, ?_, ?_⟩, by simp, ?_, ?_⟩
    · intro n hn; rw [reprList] at hn; simp at hn; rcases hn with rfl | rfl <;> assumption
    · simpa [reprList] using sorted_two hlt
    · intro ps hps; simp at hps
    · simp [absPropWhen, absPropWhenRepr]
    · simp only [reprList, List.map_cons, List.map_nil]
      rw [merge_lt hlt, ConLeche.PropWhen.nil_merge]
  | Eq =>
    simp only [name_dup_eq, bind_tc_ok, of_repr_eq, Result.ok.injEq] at h
    subst h
    have heq : absName p = absName q :=
      ConLeche.Name.eq_of_cmp (by simpa [absOrdering] using hcmp)
    refine ⟨⟨?_, ?_, ?_⟩, by simp, ?_, ?_⟩
    · intro n hn; rw [reprList] at hn; simp at hn; rw [hn]; exact hp
    · simp [reprList, ConLeche.PropWhen.Sorted]
    · intro ps hps; simp at hps
    · simp only [absPropWhen, absPropWhenRepr]
      refine (ConLeche.PropWhen.ifAllZero_eq_iff _ _).mpr ?_
      intro n; simp [heq]
    · rw [reprList, List.map_cons, List.map_nil, ← heq,
        merge_eq (ConLeche.Name.cmp_self (absName p)), ConLeche.PropWhen.nil_merge]
  | Gt =>
    simp only [name_dup_eq, ptr_new_eq, bind_tc_ok, of_repr_eq, Result.ok.injEq] at h
    subst h
    have hgt : ConLeche.Name.cmp (absName p) (absName q) = .gt := by
      simpa [absOrdering] using hcmp
    have hlt : ConLeche.Name.cmp (absName q) (absName p) = .lt := ConLeche.Name.lt_of_gt hgt
    refine ⟨⟨?_, ?_, ?_⟩, by simp, ?_, ?_⟩
    · intro n hn; rw [reprList] at hn; simp at hn; rcases hn with rfl | rfl <;> assumption
    · simpa [reprList] using sorted_two hlt
    · intro ps hps; simp at hps
    · simp only [absPropWhen, absPropWhenRepr]
      refine (ConLeche.PropWhen.ifAllZero_eq_iff _ _).mpr ?_
      intro n; simp; tauto
    · simp only [reprList, List.map_cons, List.map_nil]
      rw [merge_gt hgt, ConLeche.PropWhen.merge_nil]

/-- `ConLeche/Kernel/PropWhen.lean:497-507` -- `prop_when::if_all_zero` refines
the smart constructor `PropWhen.ifAllZero`, normalization included: the result
is the canonical representative of the *set* of `ps`. -/
theorem if_all_zero_shape {ps : alloc.vec.Vec name.Name} {pw : prop_when.PropWhen}
    (hps : NamesWF ps) (h : prop_when.if_all_zero ps = ok pw) :
    WFShape pw ∧ pw.repr ≠ .Never ∧ absPropWhen pw = .ifAllZero (absNames ps) := by
  rw [prop_when.if_all_zero.eq_def] at h; simp only [] at h
  by_cases h0 : ps.val.length = 0
  · rw [if_pos (show alloc.vec.Vec.len ps = 0#usize by scalar_tac), of_repr_eq,
      Result.ok.injEq] at h
    subst h
    have hnil : ps.val = [] := List.eq_nil_iff_length_eq_zero.mpr h0
    refine ⟨⟨by simp [reprList], by simp [reprList, ConLeche.PropWhen.Sorted],
      by intro qs hqs; simp at hqs⟩, by simp, ?_⟩
    simp [absPropWhen, absPropWhenRepr, absNames, hnil]
  · rw [if_neg (show ¬ alloc.vec.Vec.len ps = 0#usize by scalar_tac)] at h
    by_cases h1 : ps.val.length = 1
    · rw [if_pos (show alloc.vec.Vec.len ps = 1#usize by scalar_tac)] at h
      obtain ⟨x, hx⟩ := list_len_one h1
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec ps 0#usize (by scalar_tac))
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, name_dup_eq,
        of_repr_eq, Result.ok.injEq, exists_eq_left'] at h
      subst h
      have hxWF : NameWF x := hps x (by rw [hx]; simp)
      have hyx : y = x := by rw [hyv]; simp [hx]
      subst hyx
      refine ⟨⟨?_, ?_, ?_⟩, by simp, ?_⟩
      · intro n hn; rw [reprList] at hn; simp at hn; rw [hn]; exact hxWF
      · simp [reprList, ConLeche.PropWhen.Sorted]
      · intro qs hqs; simp at hqs
      · simp [absPropWhen, absPropWhenRepr, absNames, hx]
    · rw [if_neg (show ¬ alloc.vec.Vec.len ps = 1#usize by scalar_tac)] at h
      by_cases h2 : ps.val.length = 2
      · rw [if_pos (show alloc.vec.Vec.len ps = 2#usize by scalar_tac)] at h
        obtain ⟨x, x', hx⟩ := list_len_two h2
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec ps 0#usize (by scalar_tac))
        obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec ps 1#usize (by scalar_tac))
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz,
          Result.ok.injEq, exists_eq_left'] at h
        have hyx : y = x := by rw [hyv]; simp [hx]
        have hzx : z = x' := by rw [hzv]; simp [hx]
        subst hyx; subst hzx
        have hxWF : NameWF y := hps y (by rw [hx]; simp)
        have hzWF : NameWF z := hps z (by rw [hx]; simp)
        obtain ⟨hsh, hne, habs, -⟩ := two_prime_shape hxWF hzWF h
        refine ⟨hsh, hne, ?_⟩
        rw [habs, absNames, hx]
        simp
      · rw [if_neg (show ¬ alloc.vec.Vec.len ps = 2#usize by scalar_tac)] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨v, hv, h⟩ := h
        obtain ⟨hvE, hvWF⟩ := canon_abs hps hv
        have hvS : ConLeche.PropWhen.Sorted (absNames v) := by
          rw [hvE]; exact ConLeche.PropWhen.sorted_canon _
        obtain ⟨hsh, hne, -⟩ := of_sorted_shape hvWF hvS h
        refine ⟨hsh, hne, ?_⟩
        rw [of_sorted_abs h, hvE, ConLeche.PropWhen.ifAllZero_canon]

/-! ## `prop_when::inter`

Charon expands the Lean's two-scrutinee `match` into a 5x5 nest (task #5's
"match explosion", item 2), so the proof is five leaf lemmas plus a
`cases <;> cases <;> first` that dispatches the 25 arms onto them. -/

theorem abs_ne_never {pw : prop_when.PropWhen} (h : pw.repr ≠ .Never) :
    absPropWhen pw ≠ .never := by
  rw [absPropWhen_eq_ifAllZero h]; exact ConLeche.PropWhen.ifAllZero_ne_never _

theorem inter_case_never_l {b c : prop_when.PropWhen} (h : prop_when.never = ok c) :
    WFShape c ∧ absPropWhen c = ConLeche.PropWhen.inter
      (absPropWhen (⟨.Never⟩ : prop_when.PropWhen)) (absPropWhen b) := by
  obtain ⟨hsh, hrn⟩ := never_shape h
  exact ⟨hsh, by rw [absPropWhen_never hrn,
    absPropWhen_never (pw := (⟨.Never⟩ : prop_when.PropWhen)) rfl,
    ConLeche.PropWhen.inter_never_left]⟩

theorem inter_case_never_r {a c : prop_when.PropWhen} (h : prop_when.never = ok c) :
    WFShape c ∧ absPropWhen c = ConLeche.PropWhen.inter
      (absPropWhen a) (absPropWhen (⟨.Never⟩ : prop_when.PropWhen)) := by
  obtain ⟨hsh, hrn⟩ := never_shape h
  exact ⟨hsh, by rw [absPropWhen_never hrn,
    absPropWhen_never (pw := (⟨.Never⟩ : prop_when.PropWhen)) rfl,
    ConLeche.PropWhen.inter_never_right]⟩

theorem inter_case_always_l {b c : prop_when.PropWhen} (hb : WFShape b)
    (h : prop_when.dup b = ok c) :
    WFShape c ∧ absPropWhen c = ConLeche.PropWhen.inter
      (absPropWhen (⟨.Always⟩ : prop_when.PropWhen)) (absPropWhen b) := by
  obtain rfl := dup_eq h
  refine ⟨hb, ?_⟩
  rw [show absPropWhen (⟨.Always⟩ : prop_when.PropWhen)
        = ConLeche.PropWhen.ifAllZero [] from rfl, ConLeche.PropWhen.nil_inter]

theorem inter_case_always_r {a c : prop_when.PropWhen} (ha : WFShape a)
    (h : prop_when.dup a = ok c) :
    WFShape c ∧ absPropWhen c = ConLeche.PropWhen.inter
      (absPropWhen a) (absPropWhen (⟨.Always⟩ : prop_when.PropWhen)) := by
  obtain rfl := dup_eq h
  refine ⟨ha, ?_⟩
  rw [show absPropWhen (⟨.Always⟩ : prop_when.PropWhen)
        = ConLeche.PropWhen.ifAllZero [] from rfl, ConLeche.PropWhen.inter_nil]

theorem inter_case_one_one {x y : name.Name} {c : prop_when.PropWhen}
    (ha : WFShape (⟨.One x⟩ : prop_when.PropWhen))
    (hb : WFShape (⟨.One y⟩ : prop_when.PropWhen))
    (h : prop_when.two_prime x y = ok c) :
    WFShape c ∧ absPropWhen c = ConLeche.PropWhen.inter
      (absPropWhen (⟨.One x⟩ : prop_when.PropWhen))
      (absPropWhen (⟨.One y⟩ : prop_when.PropWhen)) := by
  have hx : NameWF x := ha.1 x (by simp [reprList])
  have hy : NameWF y := hb.1 y (by simp [reprList])
  obtain ⟨hsh, hne, habs, -⟩ := two_prime_shape hx hy h
  refine ⟨hsh, ?_⟩
  rw [habs, show absPropWhen (⟨.One x⟩ : prop_when.PropWhen)
        = ConLeche.PropWhen.ifAllZero [absName x] from rfl,
    show absPropWhen (⟨.One y⟩ : prop_when.PropWhen)
        = ConLeche.PropWhen.ifAllZero [absName y] from rfl,
    ConLeche.PropWhen.inter_ifAllZero]
  rfl

theorem inter_case_generic {a b c : prop_when.PropWhen} (ha : WFShape a) (hb : WFShape b)
    (hane : a.repr ≠ .Never) (hbne : b.repr ≠ .Never)
    (h : (do let v ← prop_when.to_list a
             let v1 ← prop_when.to_list b
             let v2 ← prop_when.merge v v1
             prop_when.of_sorted v2) = ok c) :
    WFShape c ∧ absPropWhen c
      = ConLeche.PropWhen.inter (absPropWhen a) (absPropWhen b) := by
  simp only [bind_eq_ok_iff] at h
  obtain ⟨v, hv, v1, hv1, v2, hv2, h⟩ := h
  have hvv : v.val = reprList a.repr := to_list_val hv
  have hv1v : v1.val = reprList b.repr := to_list_val hv1
  have hvWF : NamesWF v := by rw [NamesWF, hvv]; exact ha.1
  have hv1WF : NamesWF v1 := by rw [NamesWF, hv1v]; exact hb.1
  have hvS : ConLeche.PropWhen.Sorted (absNames v) := by
    rw [absNames, hvv]; exact ha.sorted
  have hv1S : ConLeche.PropWhen.Sorted (absNames v1) := by
    rw [absNames, hv1v]; exact hb.sorted
  obtain ⟨hv2E, hv2WF⟩ := merge_abs hvWF hv1WF hv2
  have hv2S : ConLeche.PropWhen.Sorted (absNames v2) := by
    rw [hv2E]; exact ConLeche.PropWhen.sorted_merge hvS hv1S
  obtain ⟨hsh, hne, -⟩ := of_sorted_shape hv2WF hv2S h
  refine ⟨hsh, ?_⟩
  rw [of_sorted_abs h, hv2E,
    ConLeche.PropWhen.inter_eq_toList (abs_ne_never hane) (abs_ne_never hbne),
    wfShape_toList ha, wfShape_toList hb]
  refine (ConLeche.PropWhen.ifAllZero_eq_iff _ _).mpr ?_
  intro n
  rw [ConLeche.PropWhen.mem_merge, List.mem_append, absNames, absNames, hvv, hv1v]

/-- `ConLeche/Kernel/PropWhen.lean:861-874` -- `prop_when::inter` refines
`PropWhen.inter`, and preserves the canonical shape. -/
theorem inter_shape {a b c : prop_when.PropWhen} (ha : WFShape a) (hb : WFShape b)
    (h : prop_when.inter a b = ok c) :
    WFShape c ∧ absPropWhen c
      = ConLeche.PropWhen.inter (absPropWhen a) (absPropWhen b) := by
  obtain ⟨ra⟩ := a
  obtain ⟨rb⟩ := b
  cases ra <;> cases rb <;> simp only [prop_when.inter] at h <;>
    first
      | exact inter_case_never_l h
      | exact inter_case_never_r h
      | exact inter_case_always_l hb h
      | exact inter_case_always_r ha h
      | exact inter_case_one_one ha hb h
      | exact inter_case_generic ha hb (by simp) (by simp) h

/-! ## `prop_when::bind_z`

`bindZ`'s `f : Name → PropWhen` argument is a one-method trait dictionary in
the port (task #9, pattern 1); the hypothesis `hf` is what relates the
dictionary to the Lean function `Φ`. -/

theorem bind_z_go_from_shape {F : Type} {inst : prop_when.NameToPw F} {f : F}
    {ps : alloc.vec.Vec name.Name} (hps : NamesWF ps)
    (Φ : ConLeche.Name → ConLeche.PropWhen)
    (hf : ∀ n, NameWF n → ∀ r, inst.apply f n = ok r →
      WFShape r ∧ absPropWhen r = Φ (absName n)) :
    ∀ k : Nat, ∀ (i : Std.Usize) (c : prop_when.PropWhen), ps.length - i.val ≤ k →
      prop_when.bind_z_go_from inst f ps i = ok c →
      WFShape c ∧ absPropWhen c
        = ConLeche.PropWhen.bindZ.go Φ ((ps.val.drop i.val).map absName) := by
  intro k
  induction k with
  | zero =>
    intro i c hk h
    rw [prop_when.bind_z_go_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
    obtain ⟨hsh, hne, habs⟩ := if_all_zero_shape
      (by intro n hn; simp [alloc.vec.Vec.new] at hn) h
    refine ⟨hsh, ?_⟩
    rw [habs, List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
    simp only [List.map_nil, ConLeche.PropWhen.bindZ_go_nil]
    simp [absNames, alloc.vec.Vec.new]
  | succ k ih =>
    intro i c hk h
    rw [prop_when.bind_z_go_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ ps.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      obtain ⟨hsh, hne, habs⟩ := if_all_zero_shape
        (by intro n hn; simp [alloc.vec.Vec.new] at hn) h
      refine ⟨hsh, ?_⟩
      rw [habs, List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
      simp only [List.map_nil, ConLeche.PropWhen.bindZ_go_nil]
      simp [absNames, alloc.vec.Vec.new]
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      have hi : i.val < ps.val.length := by scalar_tac
      have hwf : NameWF ps.val[i.val] := hps _ (List.getElem_mem hi)
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hi)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨r, hr, c1, hc1, h⟩ := h
      obtain ⟨hrsh, hrabs⟩ := hf _ hwf r hr
      obtain ⟨hc1sh, hc1abs⟩ := ih w c1 (by scalar_tac) hc1
      obtain ⟨hsh, habs⟩ := inter_shape hrsh hc1sh h
      refine ⟨hsh, ?_⟩
      rw [habs, hrabs, hc1abs, hwv, List.drop_eq_getElem_cons hi, List.map_cons,
        ConLeche.PropWhen.bindZ.go]

/-- `ConLeche/Kernel/PropWhen.lean:943-955` -- `prop_when::bind_z` refines
`PropWhen.bindZ`. -/
theorem bind_z_shape {F : Type} {inst : prop_when.NameToPw F} {f : F}
    {pw c : prop_when.PropWhen} (hpw : WFShape pw)
    (Φ : ConLeche.Name → ConLeche.PropWhen)
    (hf : ∀ n, NameWF n → ∀ r, inst.apply f n = ok r →
      WFShape r ∧ absPropWhen r = Φ (absName n))
    (h : prop_when.bind_z inst f pw = ok c) :
    WFShape c ∧ absPropWhen c = ConLeche.PropWhen.bindZ Φ (absPropWhen pw) := by
  obtain ⟨r⟩ := pw
  cases r with
  | Never =>
    simp only [prop_when.bind_z] at h
    obtain ⟨hsh, hrn⟩ := never_shape h
    refine ⟨hsh, ?_⟩
    rw [absPropWhen_never hrn,
      absPropWhen_never (pw := (⟨.Never⟩ : prop_when.PropWhen)) rfl,
      ConLeche.PropWhen.bindZ_never]
  | Always =>
    simp only [prop_when.bind_z] at h
    obtain ⟨hsh, hne, habs⟩ := if_all_zero_shape
      (by intro n hn; simp [alloc.vec.Vec.new] at hn) h
    refine ⟨hsh, ?_⟩
    rw [habs, show absPropWhen (⟨.Always⟩ : prop_when.PropWhen)
          = ConLeche.PropWhen.ifAllZero [] from rfl,
      ConLeche.PropWhen.bindZ_ifAllZero, ConLeche.PropWhen.bindZ_go_nil]
    simp [absNames, alloc.vec.Vec.new]
  | One p =>
    simp only [prop_when.bind_z] at h
    have hp : NameWF p := hpw.1 p (by simp [reprList])
    obtain ⟨hsh, habs⟩ := hf p hp c h
    refine ⟨hsh, ?_⟩
    rw [habs, show absPropWhen (⟨.One p⟩ : prop_when.PropWhen)
          = ConLeche.PropWhen.ifAllZero [absName p] from rfl,
      ConLeche.PropWhen.bindZ_ifAllZero, ConLeche.PropWhen.bindZ.go,
      ConLeche.PropWhen.bindZ_go_nil, ConLeche.PropWhen.inter_nil]
  | Two pq =>
    obtain ⟨p, q⟩ := pq
    simp only [prop_when.bind_z, bind_arc_deref, uncurry_apply_pair, bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, r2, hr2, h⟩ := h
    have hp : NameWF p := hpw.1 p (by simp [reprList])
    have hq : NameWF q := hpw.1 q (by simp [reprList])
    obtain ⟨h1sh, h1abs⟩ := hf p hp r1 hr1
    obtain ⟨h2sh, h2abs⟩ := hf q hq r2 hr2
    obtain ⟨hsh, habs⟩ := inter_shape h1sh h2sh h
    refine ⟨hsh, ?_⟩
    rw [habs, h1abs, h2abs, show absPropWhen (⟨.Two (p, q)⟩ : prop_when.PropWhen)
          = ConLeche.PropWhen.ifAllZero [absName p, absName q] from rfl,
      ConLeche.PropWhen.bindZ_ifAllZero, ConLeche.PropWhen.bindZ.go,
      ConLeche.PropWhen.bindZ.go, ConLeche.PropWhen.bindZ_go_nil,
      ConLeche.PropWhen.inter_nil]
  | Many ps =>
    simp only [prop_when.bind_z, bind_arc_deref, prop_when.bind_z_go] at h
    have hps : NamesWF ps := by intro n hn; exact hpw.1 n (by simpa [reprList] using hn)
    obtain ⟨hsh, habs⟩ := bind_z_go_from_shape hps Φ hf ps.length 0#usize c
      (by scalar_tac) h
    refine ⟨hsh, ?_⟩
    rw [habs, show absPropWhen (⟨.Many ps⟩ : prop_when.PropWhen)
          = ConLeche.PropWhen.ifAllZero (absNames ps) from rfl,
      ConLeche.PropWhen.bindZ_ifAllZero]
    simp [absNames, show (0#usize : Std.Usize).val = 0 from rfl]

theorem u64_zero_decide (m : Std.U64) : decide (m = 0#u64) = ((m.val : Nat) == 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
  exact ⟨fun h => by rw [h]; rfl,
    fun h => Std.UScalar.val_eq_imp_iff.mpr (by simpa using h)⟩

theorem u64_zero_true {m : Std.U64} (h : m = 0#u64) : ((m.val : Nat) == 0) = true := by
  rw [h]; rfl

theorem u64_zero_false {m : Std.U64} (h : ¬ m = 0#u64) : ((m.val : Nat) == 0) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  exact fun hc => h (Std.UScalar.val_eq_imp_iff.mpr (by simpa using hc))

/-! ## `to_list` / `to_list_opt` -- the views -/

/-- `ConLeche/Kernel/PropWhen.lean:509-518` -- `prop_when::to_list` refines
`PropWhen.toList`.  This is where canonicity is *used*: without the
`WFShape`'s sortedness the Rust list is only membership-equal to
con-leche's. -/
theorem to_list_shape {pw : prop_when.PropWhen} {v : alloc.vec.Vec name.Name}
    (hpw : WFShape pw) (h : prop_when.to_list pw = ok v) :
    absNames v = (absPropWhen pw).toList := by
  rw [absNames, to_list_val h, wfShape_toList hpw]

/-- `ConLeche/Kernel/PropWhen.lean:520-525` -- `prop_when::to_list_opt`
refines `PropWhen.toList?`. -/
theorem to_list_opt_shape {pw : prop_when.PropWhen} {o : Option (alloc.vec.Vec name.Name)}
    (hpw : WFShape pw) (h : prop_when.to_list_opt pw = ok o) :
    o.map absNames = (absPropWhen pw).toList? := by
  obtain ⟨r⟩ := pw
  cases r
  case Never =>
    simp only [prop_when.to_list_opt, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_never rfl, ConLeche.PropWhen.toList?_never]
    rfl
  all_goals
    simp only [prop_when.to_list_opt, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, hv, rfl⟩ := h
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.toList?_ifAllZero,
      ConLeche.PropWhen.canon_eq_self hpw.sorted, Option.map_some]
    rw [absNames, to_list_val hv]

/-! ## `is_never` and `has_params` -/

/-- `ConLeche/Kernel/PropWhen.lean:716-738` -- `prop_when::is_never` refines
`PropWhen.isNever`.  No well-formedness needed: `ifAllZero` is never `never`. -/
theorem is_never_shape {pw : prop_when.PropWhen} {b : Bool}
    (h : prop_when.is_never pw = ok b) : b = ConLeche.PropWhen.isNever (absPropWhen pw) := by
  obtain ⟨r⟩ := pw
  cases r
  case Never =>
    simp only [prop_when.is_never, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_never rfl, ConLeche.PropWhen.isNever_never]
  all_goals
    simp only [prop_when.is_never, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.isNever_ifAllZero]

/-- `ConLeche/Kernel/PropWhen.lean:751-759` -- `prop_when::has_params` refines
`PropWhen.hasParams`.  The `Many` arm is where `WFShape`'s length clause is
needed: `hasParams (ifAllZero ps) = !ps.isEmpty`, and a `Many` that held the
empty list would read `true` in Rust and `false` in con-leche. -/
theorem has_params_shape {pw : prop_when.PropWhen} {b : Bool} (hpw : WFShape pw)
    (h : prop_when.has_params pw = ok b) :
    b = ConLeche.PropWhen.hasParams (absPropWhen pw) := by
  obtain ⟨r⟩ := pw
  cases r with
  | Never =>
    simp only [prop_when.has_params, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_never rfl, ConLeche.PropWhen.hasParams_never]
  | Always =>
    simp only [prop_when.has_params, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.hasParams_ifAllZero]
    simp [reprList]
  | One p =>
    simp only [prop_when.has_params, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.hasParams_ifAllZero]
    simp [reprList]
  | Two pq =>
    simp only [prop_when.has_params, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.hasParams_ifAllZero]
    simp [reprList]
  | Many ps =>
    simp only [prop_when.has_params, Result.ok.injEq] at h
    subst h
    have hlen := hpw.2.2 ps rfl
    have hne : ps.val ≠ [] := by intro hc; rw [hc] at hlen; simp at hlen
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.hasParams_ifAllZero]
    simp [reprList, hne]

/-! ## `holds` -- the readout, and its `Valuation` dictionary

`holds (φ : Name → Nat)` takes a *function*; the port takes a one-method trait
dictionary (task #9, pattern 1), so the statement carries the hypothesis `hφ`
that relates the dictionary to `φ`. -/

theorem all_zero_from_refines {V : Type} {inst : prop_when.Valuation V} {phi : V}
    (φ : ConLeche.Name → Nat)
    (hφ : ∀ n, NameWF n → ∀ m : Std.U64, inst.value_at phi n = ok m → φ (absName n) = m.val)
    {ps : alloc.vec.Vec name.Name} (hps : NamesWF ps) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool), ps.length - i.val ≤ k →
      prop_when.all_zero_from inst phi ps i = ok b →
      b = ((ps.val.drop i.val).map absName).all (fun n => φ n == 0) := by
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [prop_when.all_zero_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
    simp
  | succ k ih =>
    intro i b hk h
    rw [prop_when.all_zero_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ ps.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      have hi : i.val < ps.val.length := by scalar_tac
      have hwf : NameWF ps.val[i.val] := hps _ (List.getElem_mem hi)
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hi)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨m, hm, h⟩ := h
      have hval := hφ _ hwf m hm
      rw [List.drop_eq_getElem_cons hi, List.map_cons, List.all_cons, hval]
      split at h
      · rename_i hz
        simp only [bind_tc_ok] at h
        rw [u64_zero_true hz, Bool.true_and, ← hwv]
        exact ih w b (by scalar_tac) h
      · rename_i hz
        simp only [Result.ok.injEq] at h
        subst h
        rw [u64_zero_false hz, Bool.false_and]

/-- `ConLeche/Kernel/PropWhen.lean:691-700` -- `prop_when::holds` refines
`PropWhen.holds`, exactly. -/
theorem holds_shape {V : Type} {inst : prop_when.Valuation V} {phi : V}
    (φ : ConLeche.Name → Nat)
    (hφ : ∀ n, NameWF n → ∀ m : Std.U64, inst.value_at phi n = ok m → φ (absName n) = m.val)
    {pw : prop_when.PropWhen} {b : Bool} (hpw : WFShape pw)
    (h : prop_when.holds inst phi pw = ok b) :
    b = ConLeche.PropWhen.holds φ (absPropWhen pw) := by
  obtain ⟨r⟩ := pw
  cases r with
  | Never =>
    simp only [prop_when.holds, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_never rfl, ConLeche.PropWhen.holds_never]
  | Always =>
    simp only [prop_when.holds, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.holds_ifAllZero]
    simp [reprList]
  | One p =>
    simp only [prop_when.holds, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨m, hm, rfl⟩ := h
    have hp : NameWF p := hpw.1 p (by simp [reprList])
    have hval := hφ p hp m hm
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.holds_ifAllZero]
    simp only [reprList, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true, hval]
    exact u64_zero_decide m
  | Two pq =>
    obtain ⟨p, q⟩ := pq
    simp only [prop_when.holds, bind_arc_deref, uncurry_apply_pair, bind_eq_ok_iff] at h
    obtain ⟨m, hm, h⟩ := h
    have hp : NameWF p := hpw.1 p (by simp [reprList])
    have hq : NameWF q := hpw.1 q (by simp [reprList])
    have hval := hφ p hp m hm
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.holds_ifAllZero]
    simp only [reprList, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true, hval]
    split at h
    · rename_i hz
      simp only [bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨m1, hm1, rfl⟩ := h
      have hval1 := hφ q hq m1 hm1
      rw [hval1, u64_zero_true hz, Bool.true_and]
      exact u64_zero_decide m1
    · rename_i hz
      simp only [Result.ok.injEq] at h
      subst h
      rw [u64_zero_false hz, Bool.false_and]
  | Many ps =>
    simp only [prop_when.holds, bind_arc_deref] at h
    have hps : NamesWF ps := by intro n hn; exact hpw.1 n (by simpa [reprList] using hn)
    have hrec := all_zero_from_refines φ hφ hps ps.length 0#usize b (by scalar_tac) h
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.holds_ifAllZero]
    simpa [reprList, show (0#usize : Std.Usize).val = 0 from rfl] using hrec

/-! ## `params_defined` -/

theorem all_contained_from_refines {params ps : alloc.vec.Vec name.Name}
    (hpar : NamesWF params) (hps : NamesWF ps) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool), ps.length - i.val ≤ k →
      prop_when.all_contained_from params ps i = ok b →
      b = ((ps.val.drop i.val).map absName).all (absNames params).contains := by
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [prop_when.all_contained_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
    simp
  | succ k ih =>
    intro i b hk h
    rw [prop_when.all_contained_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ ps.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac)]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      have hi : i.val < ps.val.length := by scalar_tac
      have hwf : NameWF ps.val[i.val] := hps _ (List.getElem_mem hi)
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hi)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b1, hb1, h⟩ := h
      have hc := Name.contains_refines hpar hwf hb1
      rw [List.drop_eq_getElem_cons hi, List.map_cons, List.all_cons, ← hc]
      split at h
      · rename_i hz
        subst hz
        simp only [bind_tc_ok] at h
        rw [Bool.true_and, ← hwv]
        exact ih w b (by scalar_tac) h
      · rename_i hz
        simp only [Result.ok.injEq] at h
        subst h
        rw [show b1 = false by simpa using hz, Bool.false_and]

/-- `ConLeche/Kernel/PropWhen.lean:778-789` -- `prop_when::params_defined`
refines `PropWhen.paramsDefined`. -/
theorem params_defined_shape {params : alloc.vec.Vec name.Name}
    {pw : prop_when.PropWhen} {b : Bool} (hpar : NamesWF params) (hpw : WFShape pw)
    (h : prop_when.params_defined params pw = ok b) :
    b = ConLeche.PropWhen.paramsDefined (absNames params) (absPropWhen pw) := by
  obtain ⟨r⟩ := pw
  cases r with
  | Never =>
    simp only [prop_when.params_defined, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_never rfl, ConLeche.PropWhen.paramsDefined_never]
  | Always =>
    simp only [prop_when.params_defined, Result.ok.injEq] at h
    subst h
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.paramsDefined_ifAllZero]
    simp [reprList]
  | One p =>
    simp only [prop_when.params_defined] at h
    have hp : NameWF p := hpw.1 p (by simp [reprList])
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.paramsDefined_ifAllZero]
    simp only [reprList, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true]
    exact Name.contains_refines hpar hp h
  | Two pq =>
    obtain ⟨p, q⟩ := pq
    simp only [prop_when.params_defined, bind_arc_deref, uncurry_apply_pair,
      bind_eq_ok_iff] at h
    obtain ⟨b1, hb1, h⟩ := h
    have hp : NameWF p := hpw.1 p (by simp [reprList])
    have hq : NameWF q := hpw.1 q (by simp [reprList])
    have hc1 := Name.contains_refines hpar hp hb1
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.paramsDefined_ifAllZero]
    simp only [reprList, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true, ← hc1]
    split at h
    · rename_i hz
      subst hz
      rw [Bool.true_and]
      exact Name.contains_refines hpar hq h
    · rename_i hz
      simp only [Result.ok.injEq] at h
      subst h
      rw [show b1 = false by simpa using hz, Bool.false_and]
  | Many ps =>
    simp only [prop_when.params_defined, bind_arc_deref] at h
    have hps : NamesWF ps := by intro n hn; exact hpw.1 n (by simpa [reprList] using hn)
    have hrec := all_contained_from_refines hpar hps ps.length 0#usize b (by scalar_tac) h
    rw [absPropWhen_eq_ifAllZero (by simp), ConLeche.PropWhen.paramsDefined_ifAllZero]
    simpa [reprList, show (0#usize : Std.Usize).val = 0 from rfl] using hrec

/-! ## `beq` -- exact under well-formedness

`equiv_r` compares constructor-wise through `name::beq`; `absPropWhen` is
injective on well-formed data (that is what canonicity buys), so the `Bool`
the Rust returns decides equality of the abstractions.  Charon expands the
two-scrutinee `match` again, so this is another 25-arm dispatch. -/

theorem names_map_inj : ∀ {l m : List name.Name}, (∀ n ∈ l, NameWF n) →
    (∀ n ∈ m, NameWF n) → l.map absName = m.map absName → l = m
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: l, y :: m, hl, hm, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Name.absName_injective (hl x (by simp)) (hm y (by simp)) h.1,
      names_map_inj (l := l) (m := m) (fun n hn => hl n (by simp [hn]))
        (fun n hn => hm n (by simp [hn])) h.2]

theorem abs_eq_iff_reprList {a b : prop_when.PropWhen} (ha : WFShape a) (hb : WFShape b)
    (hane : a.repr ≠ .Never) (hbne : b.repr ≠ .Never) :
    absPropWhen a = absPropWhen b ↔ reprList a.repr = reprList b.repr := by
  constructor
  · intro he
    refine names_map_inj ha.1 hb.1 ?_
    rw [← wfShape_toList ha, ← wfShape_toList hb, he]
  · intro he
    rw [absPropWhen_eq_ifAllZero hane, absPropWhen_eq_ifAllZero hbne, he]

theorem abs_ne_of_reprList {a b : prop_when.PropWhen} (ha : WFShape a) (hb : WFShape b)
    (hane : a.repr ≠ .Never) (hbne : b.repr ≠ .Never)
    (hl : ¬ reprList a.repr = reprList b.repr) : ¬ absPropWhen a = absPropWhen b :=
  fun he => hl ((abs_eq_iff_reprList ha hb hane hbne).mp he)

theorem never_ne_other {r : prop_when.PropWhenRepr} (h : r ≠ .Never) :
    ¬ absPropWhen (⟨.Never⟩ : prop_when.PropWhen) = absPropWhen ⟨r⟩ := by
  rw [absPropWhen_never rfl]
  exact fun hc => abs_ne_never (pw := ⟨r⟩) h hc.symm

theorem other_ne_never {r : prop_when.PropWhenRepr} (h : r ≠ .Never) :
    ¬ absPropWhen (⟨r⟩ : prop_when.PropWhen) = absPropWhen (⟨.Never⟩ : prop_when.PropWhen) :=
  fun hc => never_ne_other h hc.symm

theorem names_beq_from_refines {ps qs : alloc.vec.Vec name.Name}
    (hps : NamesWF ps) (hqs : NamesWF qs) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool), ps.length - i.val ≤ k →
      prop_when.names_beq_from ps qs i = ok b →
      (b = true ↔ ps.val.drop i.val = qs.val.drop i.val) := by
  have hboth : ∀ (i : Std.Usize), ps.val.length ≤ i.val → qs.val.length ≤ i.val →
      (true = true ↔ ps.val.drop i.val = qs.val.drop i.val) := by
    intro i hp hq
    rw [List.drop_eq_nil_of_le hp, List.drop_eq_nil_of_le hq]
    simp
  have hpnil : ∀ (i : Std.Usize), ps.val.length ≤ i.val → ¬ qs.val.length ≤ i.val →
      (false = true ↔ ps.val.drop i.val = qs.val.drop i.val) := by
    intro i hp hq
    simp only [Bool.false_eq_true, false_iff]
    intro hc
    rw [List.drop_eq_nil_of_le hp] at hc
    exact hq (List.drop_eq_nil_iff.mp hc.symm)
  have hqnil : ∀ (i : Std.Usize), ¬ ps.val.length ≤ i.val → qs.val.length ≤ i.val →
      (false = true ↔ ps.val.drop i.val = qs.val.drop i.val) := by
    intro i hp hq
    simp only [Bool.false_eq_true, false_iff]
    intro hc
    rw [List.drop_eq_nil_of_le hq] at hc
    exact hp (List.drop_eq_nil_iff.mp hc)
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [prop_when.names_beq_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
    by_cases hq : i.val ≥ qs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len qs by scalar_tac), Result.ok.injEq] at h
      subst h
      exact hboth i (by scalar_tac) (by scalar_tac)
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len qs by scalar_tac),
        if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
      subst h
      exact hpnil i (by scalar_tac) (by scalar_tac)
  | succ k ih =>
    intro i b hk h
    rw [prop_when.names_beq_from.eq_def] at h; simp only [] at h
    by_cases hp : i.val ≥ ps.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      by_cases hq : i.val ≥ qs.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len qs by scalar_tac), Result.ok.injEq] at h
        subst h
        exact hboth i (by scalar_tac) (by scalar_tac)
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len qs by scalar_tac),
          if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
        subst h
        exact hpnil i (by scalar_tac) (by scalar_tac)
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac),
        if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      have hpi : i.val < ps.val.length := by scalar_tac
      by_cases hq : i.val ≥ qs.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len qs by scalar_tac), Result.ok.injEq] at h
        subst h
        exact hqnil i (by scalar_tac) (by scalar_tac)
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len qs by scalar_tac)] at h
        have hqi : i.val < qs.val.length := by scalar_tac
        rw [List.drop_eq_getElem_cons hpi, List.drop_eq_getElem_cons hqi]
        have hwfp : NameWF ps.val[i.val] := hps _ (List.getElem_mem hpi)
        have hwfq : NameWF qs.val[i.val] := hqs _ (List.getElem_mem hqi)
        have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
        obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hpi)
        obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec qs i hqi)
        subst hyv; subst hzv
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz, hw,
          Result.ok.injEq, exists_eq_left'] at h
        obtain ⟨b1, hb1, h⟩ := h
        have e1 := Name.name_beq_exact' hwfp hwfq hb1
        split at h
        · rename_i hbt
          have heq : ps.val[i.val] = qs.val[i.val] :=
            Name.absName_injective hwfp hwfq (of_decide_eq_true (e1.symm.trans hbt))
          simp only [bind_tc_ok] at h
          rw [← hwv, ih w b (by scalar_tac) h]
          simp [heq]
        · rename_i hbf
          simp only [Result.ok.injEq] at h
          subst h
          have hne : ¬ absName ps.val[i.val] = absName qs.val[i.val] :=
            of_decide_eq_false (e1.symm.trans (by simpa using hbf))
          simp only [Bool.false_eq_true, false_iff, List.cons.injEq, not_and]
          exact fun hc _ => hne (by rw [hc])

theorem beq_iff {a b : prop_when.PropWhen} (ha : WFShape a) (hb : WFShape b) {c : Bool}
    (h : prop_when.beq a b = ok c) : c = true ↔ absPropWhen a = absPropWhen b := by
  obtain ⟨ra⟩ := a
  obtain ⟨rb⟩ := b
  cases ra with
  | Never =>
    cases rb with
    | Never =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp
    | Always =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      exact fun he => never_ne_other (by simp) he
    | One y =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      exact fun he => never_ne_other (by simp) he
    | Two y =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      exact fun he => never_ne_other (by simp) he
    | Many qs =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      exact fun he => never_ne_other (by simp) he
  | Always =>
    cases rb with
    | Never =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      exact fun he => other_ne_never (by simp) he
    | Always =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp
    | One y =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      simp [reprList]
    | Two y =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      simp [reprList]
    | Many qs =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      have h9 := hb.2.2 qs rfl
      simp only [reprList]
      intro hc
      rw [← hc] at h9
      simp at h9
  | One x =>
    cases rb with
    | Never =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      exact fun he => other_ne_never (by simp) he
    | Always =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      simp [reprList]
    | One y =>
      simp only [prop_when.beq, prop_when.equiv_r] at h
      have hx : NameWF x := ha.1 x (by simp [reprList])
      have hy : NameWF y := hb.1 y (by simp [reprList])
      rw [Name.name_beq_exact' hx hy h, abs_eq_iff_reprList ha hb (by simp) (by simp)]
      simp only [reprList, decide_eq_true_eq, List.cons.injEq, and_true]
      exact ⟨fun he => Name.absName_injective hx hy he, fun he => by rw [he]⟩
    | Two y =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      simp [reprList]
    | Many qs =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      have h9 := hb.2.2 qs rfl
      simp only [reprList]
      intro hc
      rw [← hc] at h9
      simp at h9
  | Two xq =>
    obtain ⟨x, x2⟩ := xq
    cases rb with
    | Never =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      exact fun he => other_ne_never (by simp) he
    | Always =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      simp [reprList]
    | One y =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      simp [reprList]
    | Two yq =>
      obtain ⟨y, y2⟩ := yq
      simp only [prop_when.beq, prop_when.equiv_r, bind_arc_deref, uncurry_apply_pair,
        bind_eq_ok_iff] at h
      obtain ⟨b1, hb1, h⟩ := h
      have hx : NameWF x := ha.1 x (by simp [reprList])
      have hx2 : NameWF x2 := ha.1 x2 (by simp [reprList])
      have hy : NameWF y := hb.1 y (by simp [reprList])
      have hy2 : NameWF y2 := hb.1 y2 (by simp [reprList])
      have e1 := Name.name_beq_exact' hx hy hb1
      rw [abs_eq_iff_reprList ha hb (by simp) (by simp)]
      simp only [reprList, List.cons.injEq, and_true]
      split at h
      · rename_i hz
        have hxy : x = y :=
          Name.absName_injective hx hy (of_decide_eq_true (e1.symm.trans hz))
        rw [Name.name_beq_exact' hx2 hy2 h, decide_eq_true_eq]
        exact ⟨fun he => ⟨hxy, Name.absName_injective hx2 hy2 he⟩, fun he => by rw [he.2]⟩
      · rename_i hz
        simp only [Result.ok.injEq] at h
        subst h
        have hne : ¬ absName x = absName y :=
          of_decide_eq_false (e1.symm.trans (by simpa using hz))
        simp only [Bool.false_eq_true, false_iff]
        exact fun hc => hne (by rw [hc.1])
    | Many qs =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      have h9 := hb.2.2 qs rfl
      simp only [reprList]
      intro hc
      rw [← hc] at h9
      simp at h9
  | Many ps =>
    cases rb with
    | Never =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      exact fun he => other_ne_never (by simp) he
    | Always =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      have h9 := ha.2.2 ps rfl
      simp only [reprList]
      intro hc
      rw [hc] at h9
      simp at h9
    | One y =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      have h9 := ha.2.2 ps rfl
      simp only [reprList]
      intro hc
      rw [hc] at h9
      simp at h9
    | Two y =>
      simp only [prop_when.beq, prop_when.equiv_r, Result.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, false_iff]
      refine abs_ne_of_reprList ha hb (by simp) (by simp) ?_
      have h9 := ha.2.2 ps rfl
      simp only [reprList]
      intro hc
      rw [hc] at h9
      simp at h9
    | Many qs =>
      simp only [prop_when.beq, prop_when.equiv_r, bind_arc_deref, prop_when.names_beq] at h
      have hps : NamesWF ps := by intro n hn; exact ha.1 n (by simpa [reprList] using hn)
      have hqs : NamesWF qs := by intro n hn; exact hb.1 n (by simpa [reprList] using hn)
      have hrec := names_beq_from_refines hps hqs ps.length 0#usize c (by scalar_tac) h
      rw [abs_eq_iff_reprList ha hb (by simp) (by simp)]
      simp only [reprList]
      simpa [show (0#usize : Std.Usize).val = 0 from rfl] using hrec

/-- `ConLeche/Kernel/PropWhen.lean:449-455` -- `prop_when::beq` (and with it
the `Eq2` dictionary `PropWhen::eq2`) decides equality of the abstracted data,
**exactly**.  `hash_pw` needs no lemma: DESIGN.md §3.2 -- `mixHash` is opaque
and hash values only move memo entries between buckets. -/
theorem beq_shape {a b : prop_when.PropWhen} (ha : WFShape a) (hb : WFShape b) {c : Bool}
    (h : prop_when.beq a b = ok c) : c = decide (absPropWhen a = absPropWhen b) := by
  have hiff := beq_iff ha hb h
  cases c
  · simp only [Bool.false_eq_true, false_iff] at hiff
    simp [hiff]
  · simp only [true_iff] at hiff
    simp [hiff]

/-! ## `PropWhenWF` gives the canonical shape

The predicate's four constructors are the port's four public producers; each
case of this induction is one of the shape lemmas above.  `bind_z` needs a
shape-only twin of `bind_z_go_from_shape` (the induction hypothesis it gets
here carries no valuation). -/

theorem bind_z_go_from_wf {F : Type} {inst : prop_when.NameToPw F} {f : F}
    {ps : alloc.vec.Vec name.Name} (hps : NamesWF ps)
    (hf : ∀ n, NameWF n → ∀ r, inst.apply f n = ok r → WFShape r) :
    ∀ k : Nat, ∀ (i : Std.Usize) (c : prop_when.PropWhen), ps.length - i.val ≤ k →
      prop_when.bind_z_go_from inst f ps i = ok c → WFShape c := by
  intro k
  induction k with
  | zero =>
    intro i c hk h
    rw [prop_when.bind_z_go_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
    exact (if_all_zero_shape (by intro n hn; simp [alloc.vec.Vec.new] at hn) h).1
  | succ k ih =>
    intro i c hk h
    rw [prop_when.bind_z_go_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ ps.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      exact (if_all_zero_shape (by intro n hn; simp [alloc.vec.Vec.new] at hn) h).1
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      have hi : i.val < ps.val.length := by scalar_tac
      have hwf : NameWF ps.val[i.val] := hps _ (List.getElem_mem hi)
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hi)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨r, hr, c1, hc1, h⟩ := h
      exact (inter_shape (hf _ hwf r hr) (ih w c1 (by scalar_tac) hc1) h).1

theorem bind_z_wf {F : Type} {inst : prop_when.NameToPw F} {f : F}
    {pw c : prop_when.PropWhen} (hpw : WFShape pw)
    (hf : ∀ n, NameWF n → ∀ r, inst.apply f n = ok r → WFShape r)
    (h : prop_when.bind_z inst f pw = ok c) : WFShape c := by
  obtain ⟨r⟩ := pw
  cases r with
  | Never =>
    simp only [prop_when.bind_z] at h
    exact (never_shape h).1
  | Always =>
    simp only [prop_when.bind_z] at h
    exact (if_all_zero_shape (by intro n hn; simp [alloc.vec.Vec.new] at hn) h).1
  | One p =>
    simp only [prop_when.bind_z] at h
    exact hf p (hpw.1 p (by simp [reprList])) c h
  | Two pq =>
    obtain ⟨p, q⟩ := pq
    simp only [prop_when.bind_z, bind_arc_deref, uncurry_apply_pair, bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, r2, hr2, h⟩ := h
    exact (inter_shape (hf p (hpw.1 p (by simp [reprList])) r1 hr1)
      (hf q (hpw.1 q (by simp [reprList])) r2 hr2) h).1
  | Many ps =>
    simp only [prop_when.bind_z, bind_arc_deref, prop_when.bind_z_go] at h
    exact bind_z_go_from_wf
      (by intro n hn; exact hpw.1 n (by simpa [reprList] using hn)) hf
      ps.length 0#usize c (by scalar_tac) h

/-- Every well-formed datum has the canonical shape. -/
theorem wf_shape {pw : prop_when.PropWhen} (h : PropWhenWF pw) : WFShape pw := by
  induction h with
  | never h => exact (never_shape h).1
  | if_all_zero hps h => exact (if_all_zero_shape hps h).1
  | inter _ _ h iha ihb => exact (inter_shape iha ihb h).1
  | bind_z hf _ h ihf ihpw => exact bind_z_wf ihpw (fun n hn r hr => ihf n hn r hr) h

/-! ## Reflexivity (task #20)

`kernel::expr`'s `beq` keeps a pointer fast path at every level of the descent,
and DESIGN.md §3.2's transparency obligation for it is that the model's walk is
*reflexive*.  A `lam`/`forallE` node's `BinderMeta` is one of that descent's
leaves, so `prop_when::beq` owes the same lemma. -/

theorem names_beq_from_refl {ps : alloc.vec.Vec name.Name} (hps : NamesWF ps) :
    ∀ k : Nat, ∀ i : Std.Usize, ps.val.length - i.val ≤ k →
      prop_when.names_beq_from ps ps i = ok true := by
  intro k
  induction k with
  | zero =>
    intro i hk
    rw [prop_when.names_beq_from.eq_def]
    simp only []
    rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac),
      if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)]
  | succ k ih =>
    intro i hk
    rw [prop_when.names_beq_from.eq_def]
    simp only []
    by_cases hi : i.val ≥ ps.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac),
        if_pos (show i ≥ alloc.vec.Vec.len ps by scalar_tac)]
    · have hlt : i.val < ps.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hlt)
      subst hyv
      rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac),
        if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac),
        if_neg (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)]
      simp only [alloc.vec.Vec.index_slice_index, hy, hw, bind_tc_ok,
        Name.name_beq_refl (hps _ (List.getElem_mem hlt)), if_true]
      exact ih w (by scalar_tac)

/-- `prop_when::beq` is reflexive on well-formed data. -/
theorem beq_refl {pw : prop_when.PropWhen} (h : PropWhenWF pw) :
    prop_when.beq pw pw = ok true := by
  have hs := wf_shape h
  obtain ⟨r⟩ := pw
  rw [prop_when.beq]
  cases r with
  | Never => rfl
  | Always => rfl
  | One p =>
    exact Name.name_beq_refl (hs.namesWF p (by simp [reprList]))
  | Two pq =>
    obtain ⟨p, q⟩ := pq
    simp only [prop_when.equiv_r, bind_arc_deref, uncurry_apply_pair,
      Name.name_beq_refl (hs.namesWF p (by simp [reprList])), bind_tc_ok, if_true]
    exact Name.name_beq_refl (hs.namesWF q (by simp [reprList]))
  | Many ps =>
    simp only [prop_when.equiv_r, bind_arc_deref, prop_when.names_beq]
    exact names_beq_from_refl (fun n hn => hs.namesWF n (by simpa [reprList] using hn))
      ps.val.length 0#usize (by scalar_tac)

/-! ## `absPropWhen` is injective on well-formed data (task #20)

`kernel::expr` needs it: a `lam`/`forallE` node stores a `BinderMeta`, so
`absExpr`'s injectivity -- and through it `expr::beq`'s exactness, which rests
on the stored hash word being a function of the abstraction -- comes down to
this.  The proof is `wfShape_toList` plus the fact that among the four
non-`Never` representations the parameter list determines the constructor
(which is what the `Many` length clause of `WFShape` is for). -/

theorem names_list_inj {l m : List name.Name} (hl : ∀ n ∈ l, NameWF n)
    (hm : ∀ n ∈ m, NameWF n) (h : l.map absName = m.map absName) : l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp_all
  | cons x xs ih =>
    cases m with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [Name.absName_injective (hl x (by simp)) (hm y (by simp)) h.1,
        ih (fun n hn => hl n (by simp [hn])) (fun n hn => hm n (by simp [hn])) h.2]

theorem absPropWhen_injective {a b : prop_when.PropWhen}
    (ha : PropWhenWF a) (hb : PropWhenWF b) (hab : absPropWhen a = absPropWhen b) :
    a = b := by
  obtain ⟨ra⟩ := a
  obtain ⟨rb⟩ := b
  have sa := wf_shape ha
  have sb := wf_shape hb
  by_cases hna : ra = .Never
  · have hnb : rb = .Never := by
      apply repr_never_of_abs_never
      rw [← hab, absPropWhen_never (by simpa using hna)]
    rw [hna, hnb]
  · have hnb : rb ≠ .Never := by
      intro hc
      exact hna (repr_never_of_abs_never (by rw [hab, absPropWhen_never (by simpa using hc)]))
    have hlists : reprList ra = reprList rb :=
      names_list_inj sa.namesWF sb.namesWF (by
        have h1 := wfShape_toList sa
        have h2 := wfShape_toList sb
        simp only [] at h1 h2
        rw [← h1, ← h2, hab])
    have hmanya := sa.2.2
    have hmanyb := sb.2.2
    simp only [prop_when.PropWhen.mk.injEq]
    cases ra <;> cases rb <;>
      simp_all [reprList, prop_when.PropWhenRepr.Many.injEq]
    all_goals
      first
      | exact alloc.vec.Vec.ext _ _ hlists
      | exact Prod.ext_iff.mpr hlists
      | (rw [← hlists] at hmanyb; simp at hmanyb)

/-! ## The refinement statements, under the `ConRon/Refine/README.md` names

`ConRon.Generated.kernel.prop_when.<fn>` is refined by
`ConRon.Refine.PropWhen.<fn>_refines`.  All hypotheses are well-formedness
facts plus, for `holds`/`bind_z`, the relation between the port's trait
dictionary and con-leche's function argument; every conclusion is exact. -/

theorem never_wf {pw} (h : prop_when.never = ok pw) : PropWhenWF pw := PropWhenWF.never h

theorem if_all_zero_wf {ps pw} (hps : NamesWF ps) (h : prop_when.if_all_zero ps = ok pw) :
    PropWhenWF pw := PropWhenWF.if_all_zero hps h

/-- `prop_when::never` refines `PropWhen.never`. -/
theorem never_refines {pw} (h : prop_when.never = ok pw) :
    absPropWhen pw = ConLeche.PropWhen.never := absPropWhen_never (never_shape h).2

/-- `prop_when::if_all_zero` refines the smart constructor `PropWhen.ifAllZero`. -/
theorem if_all_zero_refines {ps pw} (hps : NamesWF ps)
    (h : prop_when.if_all_zero ps = ok pw) :
    absPropWhen pw = ConLeche.PropWhen.ifAllZero (absNames ps) :=
  (if_all_zero_shape hps h).2.2

/-- `prop_when::name_cmp` refines `ConLeche.Name.cmp` (`PropWhen.lean:75-85`). -/
theorem name_cmp_refines' {a b : name.Name} (ha : NameWF a) (hb : NameWF b)
    {o : prop_when.Ordering} (h : prop_when.name_cmp a b = ok o) :
    ConLeche.Name.cmp (absName a) (absName b) = absOrdering o := name_cmp_refines ha hb h

/-- `prop_when::to_list` refines `PropWhen.toList`. -/
theorem to_list_refines {pw v} (hpw : PropWhenWF pw) (h : prop_when.to_list pw = ok v) :
    absNames v = (absPropWhen pw).toList := to_list_shape (wf_shape hpw) h

/-- `prop_when::to_list_opt` refines `PropWhen.toList?`. -/
theorem to_list_opt_refines {pw o} (hpw : PropWhenWF pw)
    (h : prop_when.to_list_opt pw = ok o) : o.map absNames = (absPropWhen pw).toList? :=
  to_list_opt_shape (wf_shape hpw) h

/-- `prop_when::is_never` refines `PropWhen.isNever`. -/
theorem is_never_refines {pw b} (h : prop_when.is_never pw = ok b) :
    b = ConLeche.PropWhen.isNever (absPropWhen pw) := is_never_shape h

/-- `prop_when::has_params` refines `PropWhen.hasParams`. -/
theorem has_params_refines {pw b} (hpw : PropWhenWF pw)
    (h : prop_when.has_params pw = ok b) :
    b = ConLeche.PropWhen.hasParams (absPropWhen pw) := has_params_shape (wf_shape hpw) h

/-- `prop_when::holds` refines `PropWhen.holds`.  `hφ` is the hypothesis that
the port's `Valuation` dictionary computes con-leche's `φ : Name → Nat`. -/
theorem holds_refines {V : Type} {inst : prop_when.Valuation V} {phi : V}
    (φ : ConLeche.Name → Nat)
    (hφ : ∀ n, NameWF n → ∀ m : Std.U64, inst.value_at phi n = ok m → φ (absName n) = m.val)
    {pw b} (hpw : PropWhenWF pw) (h : prop_when.holds inst phi pw = ok b) :
    b = ConLeche.PropWhen.holds φ (absPropWhen pw) := holds_shape φ hφ (wf_shape hpw) h

/-- `prop_when::params_defined` refines `PropWhen.paramsDefined`. -/
theorem params_defined_refines {params pw b} (hpar : NamesWF params) (hpw : PropWhenWF pw)
    (h : prop_when.params_defined params pw = ok b) :
    b = ConLeche.PropWhen.paramsDefined (absNames params) (absPropWhen pw) :=
  params_defined_shape hpar (wf_shape hpw) h

/-- `prop_when::inter` refines `PropWhen.inter`, and preserves well-formedness. -/
theorem inter_refines {a b c} (ha : PropWhenWF a) (hb : PropWhenWF b)
    (h : prop_when.inter a b = ok c) :
    absPropWhen c = ConLeche.PropWhen.inter (absPropWhen a) (absPropWhen b) ∧ PropWhenWF c :=
  ⟨(inter_shape (wf_shape ha) (wf_shape hb) h).2, PropWhenWF.inter ha hb h⟩

/-- `prop_when::bind_z` refines `PropWhen.bindZ`.  `hf` is the hypothesis that
the port's `NameToPw` dictionary computes con-leche's `Φ : Name → PropWhen`. -/
theorem bind_z_refines {F : Type} {inst : prop_when.NameToPw F} {f : F} {pw c}
    (Φ : ConLeche.Name → ConLeche.PropWhen)
    (hf : ∀ n, NameWF n → ∀ r, inst.apply f n = ok r →
      absPropWhen r = Φ (absName n) ∧ PropWhenWF r)
    (hpw : PropWhenWF pw) (h : prop_when.bind_z inst f pw = ok c) :
    absPropWhen c = ConLeche.PropWhen.bindZ Φ (absPropWhen pw) ∧ PropWhenWF c :=
  ⟨(bind_z_shape (wf_shape hpw) Φ
      (fun n hn r hr => ⟨wf_shape (hf n hn r hr).2, (hf n hn r hr).1⟩) h).2,
   PropWhenWF.bind_z (fun n hn r hr => (hf n hn r hr).2) hpw h⟩

/-- `prop_when::beq` -- and the `Eq2` dictionary that *is* it -- decides
equality of the abstracted data exactly. -/
theorem beq_refines {a b c} (ha : PropWhenWF a) (hb : PropWhenWF b)
    (h : prop_when.beq a b = ok c) : c = decide (absPropWhen a = absPropWhen b) :=
  beq_shape (wf_shape ha) (wf_shape hb) h

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing from Aeneas's library, nothing from the `Arc` models, no `sorry`, and
**no `import all`**: `absPropWhen` and every statement here go through
con-leche's public `never`/`ifAllZero`/`toList` API. -/

/--
info: 'ConRon.Refine.PropWhen.inter_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inter_refines

/--
info: 'ConRon.Refine.PropWhen.bind_z_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bind_z_refines

/--
info: 'ConRon.Refine.PropWhen.beq_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beq_refines

end ConRon.Refine.PropWhen
