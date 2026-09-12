/-
`ConRon.Refine.Name` -- the refinement lemmas of `crates/con-ron-core/src/name.rs`
against `ConLeche/Kernel/Name.lean` (DESIGN.md §3.5; P3.3 of §5).

Ported at task #17 from `ConRon/Spike/LevelName/Refine.lean` (task #5).  The
crate's `name.rs` differs from the spike's only by the two `crate::hashmap`
dictionaries and the unit tests it gained at task #9, neither of which changes
a generated function body: all 63 `name.*`/`level.*` definitions of
`ConRon/Generated/Funs.lean` are byte-identical to the spike's modulo the
`level_name.` prefix.  The proof scripts below are therefore the spike's,
unchanged.

Shape, as fixed by task #5: **exact result on success** -- a Rust function
that returns `ok y` computes exactly what con-leche computes on the abstracted
inputs, and nothing is claimed when the Rust side fails.  `ptr_eq` is `false`
in the model (DESIGN.md §3.2), so the reflexivity lemmas `str_eq_refl` /
`name_beq_refl` are what make the real program's fast path agree.
-/
import ConRon.Refine.Abs

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Name

/-! ## `absString` and `absName` are injective on well-formed input -/


theorem absString_inj {s t : alloc.vec.Vec Std.U32}
    (hs : StrWF s) (ht : StrWF t) (h : absString s = absString t) : s = t := by
  simp only [absString, String.ofList_inj] at h
  apply alloc.vec.Vec.ext
  have : ∀ (l : List Std.U32), (∀ c ∈ l, Nat.isValidChar c.val) →
      l.map (fun c => (Char.ofNat c.val).toNat) = l.map (fun c => c.val) := by
    intro l hl
    apply List.map_congr_left
    intro c hc
    simp [Char.ofNat, Char.ofNatAux, Char.toNat, hl c hc]
  have h2 := congrArg (List.map Char.toNat) h
  simp only [List.map_map, Function.comp_def] at h2
  rw [this _ hs, this _ ht] at h2
  have : ∀ (l m : List Std.U32), l.map (fun c => c.val) = m.map (fun c => c.val) → l = m := by
    intro l m hlm
    apply List.map_injective_iff.mpr ?_ hlm
    intro a b hab
    exact Std.UScalar.val_eq_imp_iff.mpr hab
  exact this _ _ h2

theorem absName_injective {a b : name.Name} (ha : NameWF a) (hb : NameWF b) :
    absName a = absName b → a = b := by
  induction ha generalizing b with
  | @anonymous n h =>
    rw [name_anonymous_inv h]
    intro hab
    cases hb with
    | @anonymous n' h' => rw [name_anonymous_inv h']
    | @str p' s' n' hp' hs' h' => obtain ⟨hh, rfl⟩ := mk_str_inv h'; simp at hab
    | @num p' m' n' hp' h' => obtain ⟨hh, rfl⟩ := mk_num_inv h'; simp at hab
  | @str pre s n hpre hs hmk ih =>
    obtain ⟨hh, rfl⟩ := mk_str_inv hmk
    intro hab
    cases hb with
    | @anonymous n' h' => rw [name_anonymous_inv h'] at hab; simp at hab
    | @str p' s' n' hp' hs' h' =>
      obtain ⟨hh', rfl⟩ := mk_str_inv h'
      simp at hab
      obtain ⟨hab1, hab2⟩ := hab
      have hp : pre = p' := ih hp' hab1
      have hss : s = s' := absString_inj hs hs' hab2
      subst hp; subst hss
      exact Result.ok_injective (hmk.symm.trans h')
    | @num p' m' n' hp' h' => obtain ⟨hh', rfl⟩ := mk_num_inv h'; simp at hab
  | @num pre m n hpre hmk ih =>
    obtain ⟨hh, rfl⟩ := mk_num_inv hmk
    intro hab
    cases hb with
    | @anonymous n' h' => rw [name_anonymous_inv h'] at hab; simp at hab
    | @str p' s' n' hp' hs' h' => obtain ⟨hh', rfl⟩ := mk_str_inv h'; simp at hab
    | @num p' m' n' hp' h' =>
      obtain ⟨hh', rfl⟩ := mk_num_inv h'
      simp at hab
      obtain ⟨hab1, hab2⟩ := hab
      have hp : pre = p' := ih hp' hab1
      have : m = m' := Std.UScalar.val_eq_imp_iff.mpr hab2
      subst hp; subst this
      exact Result.ok_injective (hmk.symm.trans h')


/-! ## `name::str_eq` -- the code-point walk of DESIGN.md §3.3

Every `*_from` index loop costs one induction on `len - i`, with the
conclusion stated on `List.drop i` so that `i = 0` collapses to the whole
list (task #5). -/

theorem str_eq_from_refl (s : alloc.vec.Vec Std.U32) :
    ∀ n (i : Std.Usize), s.length - i.val ≤ n → name.str_eq_from s s i = ok true := by
  intro n
  induction n with
  | zero =>
    intro i h
    rw [name.str_eq_from.eq_def]; simp only []
    rw [if_pos (by scalar_tac)]
  | succ n ih =>
    intro i h
    rw [name.str_eq_from.eq_def]; simp only []
    split
    · rfl
    · rename_i hlt
      have hb : i.val < s.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := s.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      simp [hw]
      obtain ⟨y, hy, _⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec s i hb)
      exact ⟨y, hy, y, hy, by simp [ih w (by scalar_tac)]⟩

theorem str_eq_refl (s : alloc.vec.Vec Std.U32) : name.str_eq s s = ok true := by
  simp [name.str_eq]
  exact str_eq_from_refl s s.length 0#usize (by scalar_tac)

theorem str_eq_from_eq {a b : alloc.vec.Vec Std.U32} (hlen : a.length = b.length) :
    ∀ n (i : Std.Usize), a.length - i.val ≤ n → name.str_eq_from a b i = ok true →
      a.val.drop i.val = b.val.drop i.val := by
  intro n
  induction n with
  | zero =>
    intro i h _
    rw [List.drop_eq_nil_of_le (by scalar_tac), List.drop_eq_nil_of_le (by scalar_tac)]
  | succ n ih =>
    intro i h he
    rw [name.str_eq_from.eq_def] at he; simp only [] at he
    split at he
    · rw [List.drop_eq_nil_of_le (by scalar_tac), List.drop_eq_nil_of_le (by scalar_tac)]
    · rename_i hlt
      have hb : i.val < a.length := by scalar_tac
      have hb' : i.val < b.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := a.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec a i hb)
      obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b i hb')
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hw, hy, hz] at he
      obtain ⟨y', hy', z', hz', he⟩ := he
      simp only [Result.ok.injEq] at hy' hz'
      subst hy'; subst hz'
      split at he
      · simp at he
      · rename_i hne
        simp only [bind_tc_ok] at he
        rw [List.drop_eq_getElem_cons hb, List.drop_eq_getElem_cons hb']
        have : a.val[i.val] = b.val[i.val] := by
          rw [← hyv, ← hzv]
          simp at hne
          exact Std.UScalar.val_eq_imp_iff.mpr (by simpa using hne)
        rw [this, ← hwv]
        exact congrArg _ (ih w (by scalar_tac) he)

theorem str_eq_eq {a b : alloc.vec.Vec Std.U32} (h : name.str_eq a b = ok true) : a = b := by
  rw [name.str_eq] at h
  split at h
  · simp at h
  · rename_i hlen
    have hlen' : a.length = b.length := by scalar_tac
    apply alloc.vec.Vec.ext
    have := str_eq_from_eq hlen' a.length 0#usize (by scalar_tac) h
    simpa using this

/-! ## `name::beq` -- reflexivity, soundness, exactness -/

theorem name_beq_refl {a : name.Name} (h : NameWF a) : name.beq a a = ok true := by
  induction h with
  | @anonymous n h =>
    rw [name_anonymous_inv h, name.beq.eq_def]
    simp [name.ptr_eq, name.hash_data]
  | @str pre s n hpre hs hmk ih =>
    obtain ⟨hh, rfl⟩ := mk_str_inv hmk
    rw [name.beq.eq_def]
    simp [name.ptr_eq, name.hash_data, ih, str_eq_refl]
  | @num pre m n hpre hmk ih =>
    obtain ⟨hh, rfl⟩ := mk_num_inv hmk
    rw [name.beq.eq_def]
    simp [name.ptr_eq, name.hash_data, ih]

theorem name_beq_abs {a : name.Name} (ha : NameWF a) :
    ∀ b, name.beq a b = ok true → absName a = absName b := by
  induction ha with
  | @anonymous n h =>
    rw [name_anonymous_inv h]
    intro b hb
    rw [name.beq.eq_def] at hb
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb <;> simp [name.ptr_eq, name.hash_data] at hb ⊢
  | @str pre s n hpre hs hmk ih =>
    obtain ⟨hh, rfl⟩ := mk_str_inv hmk
    intro b hb
    rw [name.beq.eq_def] at hb
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb with
    | Anonymous => simp [name.ptr_eq, name.hash_data] at hb
    | Num q k => simp [name.ptr_eq, name.hash_data] at hb
    | Str q t =>
      simp [name.ptr_eq, name.hash_data] at hb
      split at hb
      case isFalse => simp at hb
      case isTrue =>
        simp only [bind_eq_ok_iff] at hb
        obtain ⟨y, hy, hb⟩ := hb
        cases y
        · simp at hb
        · have h1 := ih q hy
          have h2 := str_eq_eq (by simpa using hb)
          subst h2
          simp [h1]
  | @num pre m n hpre hmk ih =>
    obtain ⟨hh, rfl⟩ := mk_num_inv hmk
    intro b hb
    rw [name.beq.eq_def] at hb
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb with
    | Anonymous => simp [name.ptr_eq, name.hash_data] at hb
    | Str q t => simp [name.ptr_eq, name.hash_data] at hb
    | Num q k =>
      simp [name.ptr_eq, name.hash_data] at hb
      split at hb
      case isFalse => simp at hb
      case isTrue =>
        simp only [bind_eq_ok_iff] at hb
        obtain ⟨y, hy, hb⟩ := hb
        cases y
        · simp at hb
        · have h1 := ih q hy
          have h2 : m = k := by simpa using hb
          subst h2
          simp [h1]

theorem name_beq_exact' {a b : name.Name} (ha : NameWF a) (hb : NameWF b) {c : Bool}
    (h : name.beq a b = ok c) : c = decide (absName a = absName b) := by
  cases c
  · symm; simp only [decide_eq_false_iff_not]
    intro heq
    have hab : a = b := absName_injective ha hb heq
    subst hab
    rw [name_beq_refl ha] at h
    simp at h
  · symm; simp only [decide_eq_true_eq]
    exact name_beq_abs ha b h

/-! ## `name::contains` and `name::singleton` -- the `Vec<Name>` helpers

`name::contains` is what `prop_when::params_defined` decides with, so its
exactness is what `ConRon/Refine/PropWhen.lean` needs; con-leche spells it
`params.contains p`, i.e. `List.contains` at the `LawfulBEq Name` instance
(`ConLeche/Kernel/Name.lean:88-93`). -/

theorem contains_from_refines {ns : alloc.vec.Vec name.Name} {n : name.Name}
    (hns : NamesWF ns) (hn : NameWF n) :
    ∀ k (i : Std.Usize), ns.length - i.val ≤ k → ∀ c : Bool,
      name.contains_from ns i n = ok c →
      c = decide (absName n ∈ (ns.val.drop i.val).map absName) := by
  intro k
  induction k with
  | zero =>
    intro i h c hc
    rw [name.contains_from.eq_def] at hc; simp only [] at hc
    rw [if_pos (by scalar_tac)] at hc
    rw [List.drop_eq_nil_of_le (by scalar_tac)]
    simp only [List.map_nil, List.not_mem_nil, decide_false]
    simpa using hc.symm
  | succ k ih =>
    intro i h c hc
    rw [name.contains_from.eq_def] at hc; simp only [] at hc
    split at hc
    · rw [List.drop_eq_nil_of_le (by scalar_tac)]
      simp only [List.map_nil, List.not_mem_nil, decide_false]
      simpa using hc.symm
    · rename_i hlt
      have hb : i.val < ns.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ns.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ns i hb)
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw] at hc
      obtain ⟨y', hy', b, hb', hc⟩ := hc
      simp only [Result.ok.injEq] at hy'
      subst hy'
      subst hyv
      have hyWF : NameWF ns.val[i.val] := hns _ (List.getElem_mem hb)
      have hbeq := name_beq_exact' hyWF hn hb'
      rw [List.drop_eq_getElem_cons hb]
      simp only [List.map_cons, List.mem_cons]
      cases b with
      | true =>
        have heq : absName ns.val[i.val] = absName n := of_decide_eq_true hbeq.symm
        simp only [reduceIte, Result.ok.injEq] at hc
        subst hc
        simp [heq.symm]
      | false =>
        have hne : ¬ absName ns.val[i.val] = absName n := of_decide_eq_false hbeq.symm
        simp only [Bool.false_eq_true, reduceIte, bind_tc_ok] at hc
        have hih := ih w (by scalar_tac) c hc
        rw [hwv] at hih
        rw [hih]
        simp only [decide_eq_decide]
        exact ⟨Or.inr, fun hm => hm.resolve_left fun he => hne he.symm⟩

/-- `ConLeche/Kernel/Name.lean` -- `name::contains` refines `List.contains`. -/
theorem contains_refines {ns : alloc.vec.Vec name.Name} {n : name.Name} {c : Bool}
    (hns : NamesWF ns) (hn : NameWF n) (h : name.contains ns n = ok c) :
    c = (absNames ns).contains (absName n) := by
  rw [name.contains] at h
  have hc := contains_from_refines hns hn ns.length 0#usize (by scalar_tac) c h
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hc
  rw [hc, absNames, Bool.eq_iff_iff, decide_eq_true_iff, List.contains_iff_mem]

/-- `name::singleton` is con-leche's one-element list. -/
theorem singleton_refines {n : name.Name} {v : alloc.vec.Vec name.Name}
    (h : name.singleton n = ok v) : absNames v = [absName n] := by
  simp only [name.singleton, bind_eq_ok_iff, name_dup_eq, Result.ok.injEq,
    exists_eq_left'] at h
  rw [absNames, vec_push_val h]
  simp [alloc.vec.Vec.new]

/-! ## The task-#5 statements, under the `ConRon/Refine/README.md` names

`ConRon.Generated.name.<fn>` is refined by `ConRon.Refine.Name.<fn>_refines`;
`<fn>_wf` is the well-formedness half (which, by the §3.5 convention, is
literally a `NameWF` constructor). -/

/-- `ConLeche/Kernel/Name.lean:26-45` -- `name::anonymous` builds a well-formed
name. -/
theorem anonymous_wf {n : name.Name} : name.anonymous = ok n → NameWF n :=
  NameWF.anonymous

/-- `ConLeche/Kernel/Name.lean:26-45` -- `name::anonymous` refines
`Name.anonymous`. -/
theorem anonymous_refines {n : name.Name} (h : name.anonymous = ok n) :
    absName n = .anonymous := by rw [name_anonymous_inv h]; simp

/-- `name::mk_str` builds a well-formed name. -/
theorem mk_str_wf {pre s n} (hpre : NameWF pre) (hs : StrWF s) :
    name.mk_str pre s = ok n → NameWF n := NameWF.str hpre hs

/-- `ConLeche/Kernel/Name.lean:26-45` -- `name::mk_str` refines `Name.str`. -/
theorem mk_str_refines {pre s n} (h : name.mk_str pre s = ok n) :
    absName n = .str (absName pre) (absString s) := by
  obtain ⟨hh, rfl⟩ := mk_str_inv h; simp

/-- `name::mk_num` builds a well-formed name. -/
theorem mk_num_wf {pre m n} (hpre : NameWF pre) :
    name.mk_num pre m = ok n → NameWF n := NameWF.num hpre

/-- `ConLeche/Kernel/Name.lean:26-45` -- `name::mk_num` refines `Name.num`. -/
theorem mk_num_refines {pre m n} (h : name.mk_num pre m = ok n) :
    absName n = .num (absName pre) m.val := by
  obtain ⟨hh, rfl⟩ := mk_num_inv h; simp

/-- `name::dup` is the identity in the model (DESIGN.md §3.2: `Rc::clone`). -/
theorem dup_refines {n m : name.Name} (h : name.dup n = ok m) :
    absName m = absName n := by rw [name_dup_eq] at h; rw [← Result.ok_injective h]

/-- `name::str_eq` decides equality of the abstracted strings, exactly. -/
theorem str_eq_refines {a b : alloc.vec.Vec Std.U32} {c : Bool}
    (ha : StrWF a) (hb : StrWF b) (h : name.str_eq a b = ok c) :
    c = decide (absString a = absString b) := by
  cases c
  · symm; simp only [decide_eq_false_iff_not]
    intro heq
    rw [absString_inj ha hb heq, str_eq_refl] at h
    simp at h
  · symm; simp only [decide_eq_true_eq, str_eq_eq h]

/-- `ConLeche/Kernel/Name.lean:70-74` -- `name::beq` decides equality of the
abstracted names, **exactly**: the `Bool` the Rust returns is the `Bool`
con-leche's `Name.beq` returns (`= decide (· = ·)`, `Name.lean:74`). -/
theorem beq_refines {a b : name.Name} {c : Bool} (ha : NameWF a) (hb : NameWF b)
    (h : name.beq a b = ok c) : c = decide (absName a = absName b) :=
  name_beq_exact' ha hb h

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing from Aeneas's library, nothing from the `Rc` models, nothing from
con-leche beyond Lean's own three. -/

/--
info: 'ConRon.Refine.Name.beq_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms beq_refines

/--
info: 'ConRon.Refine.Name.contains_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms contains_refines

/--
info: 'ConRon.Refine.Name.str_eq_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms str_eq_refines

end ConRon.Refine.Name
