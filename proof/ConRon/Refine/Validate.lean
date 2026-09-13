import ConRon.Refine.CheckerDecl

/-! # `kernel::validate` — the input validation pass is sound (task #73)

The maintainer's ruling of 2026-09-13: `Refine/Main.lean`'s last input
hypothesis, `hds : ∀ d ∈ ds.val, DeclCWF d`, goes away by being **checked**.
`crates/con-ron-core/src/kernel/validate.rs` is the check — it runs at the
entry of `cached::installed::check_decls` and declines a malformed declaration
with `CheckError::Native` — and this file is what that check buys: one
soundness lemma per validator function, of the shape

```lean
validate_expr m e = ok (true, m') → ExprWF e
```

and, at the top, `validate_decls_sound : validate_decls m ds = ok (true, m') →
∀ d ∈ ds.val, DeclCWF d`, which `Refine/Installed.lean` applies at the accept
of the pass.

## Why the statements come out this easy

The `*WF` predicates are DESIGN.md §3.5's inductives whose constructors **are**
the port's own smart constructors (`ExprWF.app : ExprWF f → ExprWF a →
expr.app f a = ok e → ExprWF e`).  The validator *rebuilds* rather than
recomputes: it calls the smart constructor on the node's own children and
compares the stored word with the rebuilt node's.  So at the point the walk
accepts a node, the context already holds

* `expr.app f a = ok e'` — the rebuild's own Rust equation, and
* `e.data = e'.data` — the word comparison,

and the `*_inv` shape lemmas of `Refine/Expr.lean` say `e' = .mk (.mk d'
(.App f a))` while the case analysis says `e = .mk (.mk d (.App f a))`.  One
`u64` equality later `e' = e`, the equation is about `e`, and the constructor
applies.  That is the whole proof, ten times for `Expr`, five for `Level`,
three for `Name`.

## The memo is invisible

`validate_expr` carries a visited set keyed by the node's stored word, with
`ron::ptr::ptr_eq` verifying a candidate — the shape of `expr::beq`'s pair
memo (DESIGN.md §3.2, task #38).  `ptr_eq` is `false` in the model, so
`seen_hit` is `false` at *every* probe (`seen_hit_false` below, the twin of
`Refine/Expr.lean`'s `probe_hit_false`): the model writes the table and never
reads it.  Nothing here needs a memo invariant, and no lemma below mentions
the table except to thread it.

## `PropWhen`, the one that is not a stored word

`PropWhen` has a sealed representation and no derived word, so the validator
rebuilds it through the public view: `to_list_opt` (`none` exactly at `never`)
hands out the parameter list, `if_all_zero` normalises it back, and
`prop_when::beq` — con-leche's `equivR`, i.e. representation equality —
compares.  `equiv_r_exact` below is what turns that `true` into an equality of
data: on representations whose stored names are well formed, `equivR` *is*
equality.  The names on the left are the ones the pass has just validated; the
names on the right come out of `PropWhen.wf_shape` applied to the datum
`if_all_zero` built.

## `sorry` count in this file: 0
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine

namespace ConRon.Refine.Validate

open ConRon.Refine.CheckerDecl (absDeclC DeclCWF)

/-! ## The visited set is written and never read

The model half of the module note's trust argument, and the twin of
`Refine/Expr.lean`'s `pair_is_false`/`probe_hit_from_false`/`probe_hit_false`:
a probe verifies its candidate by identity, `ron::ptr::ptr_eq` is `false`, so
every probe answers `false` whatever the table holds — in particular without
any fact about `ron::HashMap` at all. -/

/-- The bucket scan never hits: every candidate is tested by `expr::ptr_eq`,
which is `false` in the model, so the scan runs off the end.  The measure
induction every index recursion in this development uses (DESIGN.md §3.5). -/
theorem seen_hit_from_false {e : expr.Expr} {es : alloc.vec.Vec expr.Expr} :
    ∀ k : Nat, ∀ (i : Std.Usize) (r : Bool),
      es.val.length - i.val ≤ k → validate.seen_hit_from es i e = ok r →
      r = false := by
  intro k
  induction k with
  | zero =>
    intro i r hk h
    rw [validate.seen_hit_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
    exact h.symm
  | succ k ih =>
    intro i r hk h
    rw [validate.seen_hit_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ es.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
      exact h.symm
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len es by scalar_tac)] at h
      have hlt : i.val < es.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := es.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff] at h
      obtain ⟨x, -, c, hc, h⟩ := h
      rw [Expr.ptr_eq_eq] at hc
      rw [← Result.ok_injective hc] at h
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, hw,
        Result.ok.injEq, exists_eq_left'] at h
      exact ih w r (by scalar_tac) h

/-- A probe of the visited set never hits in the model.  Note what the
statement does *not* assume: nothing at all about the table, in particular not
`ron::HashMap`'s invariant. -/
theorem seen_hit_false {m : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    {key : Std.U64} {e : expr.Expr} {r : Bool}
    (h : validate.seen_hit m key e = ok r) : r = false := by
  rw [validate.seen_hit] at h
  obtain ⟨o, -, h⟩ := bind_eq_ok_iff.mp h
  cases o with
  | none => simpa using h.symm
  | some es => exact seen_hit_from_false es.val.length 0#usize r (by scalar_tac) h

/-! ## Strings and bignums

`StrWF` is the one clause of the `*WF` family that no smart-constructor
equation supplies (`Refine/Abs.lean`), and `Nat.NatWF` the one invariant that
belongs to the port's own bignum rather than to a con-leche computed field. -/

/-- `validate::is_valid_char` decides `Nat.isValidChar` on a stored code
point: the two constants are `0xD800` and `0xDFFF`/`0x110000` spelled in
decimal, as `kernel::pins_decode::is_valid_char` spells them. -/
theorem is_valid_char_sound {c : Std.U32} (h : validate.is_valid_char c = ok true) :
    Nat.isValidChar c.val := by
  rw [validate.is_valid_char] at h
  unfold Nat.isValidChar
  by_cases hc : c < 55296#u32
  · left; scalar_tac
  · rw [if_neg hc] at h
    by_cases hd : c > 57343#u32
    · rw [if_pos hd, Result.ok.injEq] at h
      right; refine ⟨by scalar_tac, ?_⟩
      have : c < 1114112#u32 := by simpa using h.symm
      scalar_tac
    · rw [if_neg hd] at h; simp at h

/-- The string walk from `i` on: every code point from `i` to the end is a
valid `Char`.  The measure induction of `Refine/Expr.lean`'s index
recursions. -/
theorem validate_str_from_sound {s : alloc.vec.Vec Std.U32} :
    ∀ k : Nat, ∀ i : Std.Usize,
      s.val.length - i.val ≤ k → validate.validate_str_from s i = ok true →
      ∀ c ∈ s.val.drop i.val, Nat.isValidChar c.val := by
  intro k
  induction k with
  | zero =>
    intro i hk _
    rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i hk h
    by_cases hi : i.val ≥ s.val.length
    · rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · have hlt : i.val < s.val.length := by scalar_tac
      rw [validate.validate_str_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len s by scalar_tac)] at h
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := s.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec s i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b, hb, h⟩ := h
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
      | true =>
        simp only [if_true, bind_eq_ok_iff, hw, Result.ok.injEq, exists_eq_left'] at h
        rw [List.drop_eq_getElem_cons hlt]
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact is_valid_char_sound hb
        · exact ih w (by scalar_tac) h c (by rw [hwv]; exact hc)

/-- `validate::validate_str` establishes `StrWF`. -/
theorem validate_str_sound {s : alloc.vec.Vec Std.U32}
    (h : validate.validate_str s = ok true) : StrWF s := by
  rw [validate.validate_str] at h
  intro c hc
  exact validate_str_from_sound s.val.length 0#usize (by scalar_tac) h c (by simpa using hc)

/-- `validate::validate_nat` establishes `ron::nat`'s normalisation invariant:
the limb vector has no trailing zero limb. -/
theorem validate_nat_sound {n : ron.nat.Nat}
    (h : validate.validate_nat n = ok true) : Nat.NatWF n := by
  rw [validate.validate_nat] at h
  intro x hx
  by_cases h0 : alloc.vec.Vec.len n.limbs = 0#usize
  · exfalso
    have hnil : n.limbs.val = [] := by
      have : n.limbs.val.length = 0 := by
        have := congrArg Std.UScalar.val h0; simpa using this
      exact List.eq_nil_of_length_eq_zero this
    rw [hnil] at hx; simp at hx
  · rw [if_neg h0] at h
    have hpos : 0 < n.limbs.val.length := by
      rcases Nat.eq_zero_or_pos n.limbs.val.length with he | hp
      · exact absurd (show alloc.vec.Vec.len n.limbs = 0#usize by scalar_tac) h0
      · exact hp
    obtain ⟨w, hw, hwv⟩ :=
      usize_sub_ok (i := alloc.vec.Vec.len n.limbs) (show 1 ≤ (alloc.vec.Vec.len n.limbs).val
        by scalar_tac)
    have hlt : w.val < n.limbs.val.length := by scalar_tac
    obtain ⟨y, hy, hyv⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec n.limbs w hlt)
    subst hyv
    simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hw, hy,
      Result.ok.injEq, exists_eq_left', bne_iff_ne, ne_eq] at h
    have hlast : n.limbs.val.getLast? = some (n.limbs.val[w.val]) := by
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (show n.limbs.val.length - 1 < n.limbs.val.length by omega)]
      congr 1
      scalar_tac
    rw [hlast, Option.some.injEq] at hx
    subst hx
    intro hz; exact h (by scalar_tac)


/-! ## Names and levels

Three cases and five, each the same three moves: the case analysis says what
the node's kind is, the walk's own equations say the children validated and
what the rebuilt node is, and `Refine/Abs.lean`'s `*_inv` shape lemma plus the
stored-word comparison say the rebuilt node *is* this one. -/

/-- The stored word of a node, as a `rust_reduce` head rule: the walks all
compare `hash_data` of a node they have just built with `hash_data` of the one
they were given, and both sides are a projection. -/
@[simp, rust_reduce] theorem name_hash_data_mk (h : Std.U64) (k : name.NameKind) :
    name.hash_data (.mk (.mk h k)) = ok h := by simp [name.hash_data]

/-- The three `NameWF` constructors with the **Rust equation first**, the task
#71 keying rule: `→` takes its patterns from the propositional hypotheses in
order, so `NameWF.str`'s `NameWF pre` would make it fire at every well-formed
name.  `Refine/Level.lean` has the five `Level` ones already. -/
theorem name_anonymous_wf' {n : name.Name} (h : name.anonymous = ok n) : NameWF n :=
  NameWF.anonymous h

theorem name_str_wf' {pre n : name.Name} {s : alloc.vec.Vec Std.U32}
    (h : name.mk_str pre s = ok n) (hp : NameWF pre) (hs : StrWF s) : NameWF n :=
  NameWF.str hp hs h

theorem name_num_wf' {pre n : name.Name} {m : Std.U64}
    (h : name.mk_num pre m = ok n) (hp : NameWF pre) : NameWF n := NameWF.num hp h

section NameIdiom
attribute [local grind →] name_anonymous_wf' name_str_wf' name_num_wf'
  validate_str_sound Expr.str_copy_eq name_anonymous_inv mk_str_inv mk_num_inv
attribute [local grind =] name_hash_data_mk

/-- `validate::validate_name` establishes `NameWF`. -/
theorem validate_name_sound : ∀ n : name.Name,
    validate.validate_name n = ok true → NameWF n := by
  intro n
  induction n using Name.ind' with
  | anonymous hh =>
    intro hv; rw [validate.validate_name.eq_def] at hv; rust_norm hv
    all_goals rust_grind
  | str hh pre str ih =>
    intro hv; rw [validate.validate_name.eq_def] at hv; rust_norm hv
    all_goals rust_grind
  | num hh pre k ih =>
    intro hv; rw [validate.validate_name.eq_def] at hv; rust_norm hv
    all_goals rust_grind
end NameIdiom

/-- The `Level` twin of `name_hash_data_mk`. -/
@[simp, rust_reduce] theorem level_hash_data_mk (h : Std.U64) (k : level.LevelKind) :
    level.hash_data (.mk (.mk h k)) = ok h := by simp [level.hash_data]

section LevelIdiom
attribute [local grind →] Level.zero_wf' Level.succ_wf' Level.max_wf' Level.imax_wf'
  Level.param_wf' validate_name_sound level_zero_inv level_succ_inv level_max_inv
  level_imax_inv level_param_inv
attribute [local grind =] level_hash_data_mk

/-- `validate::validate_level` establishes `LevelWF`. -/
theorem validate_level_sound : ∀ u : level.Level,
    validate.validate_level u = ok true → LevelWF u := by
  intro u
  induction u using Level.ind' with
  | zero hh =>
    intro hv; rw [validate.validate_level.eq_def] at hv; rust_norm hv
    all_goals rust_grind
  | succ hh a ih =>
    intro hv; rw [validate.validate_level.eq_def] at hv; rust_norm hv
    all_goals rust_grind
  | max hh a b iha ihb =>
    intro hv; rw [validate.validate_level.eq_def] at hv; rust_norm hv
    all_goals rust_grind
  | imax hh a b iha ihb =>
    intro hv; rw [validate.validate_level.eq_def] at hv; rust_norm hv
    all_goals rust_grind
  | param hh n =>
    intro hv; rw [validate.validate_level.eq_def] at hv; rust_norm hv
    all_goals rust_grind
end LevelIdiom

/-! ## The name and level vectors

Index recursions, so measure inductions (DESIGN.md §3.5: induct on the
argument, not on the function), in the shape of `Refine/Env.lean`'s
`levels_copy_from_val`.  These are list folds, which `Refine/README.md` puts
outside the task-#71 idiom's scope; they are hand proofs. -/

/-- The name walk from `i` on. -/
theorem validate_names_from_sound {ns : alloc.vec.Vec name.Name} :
    ∀ k : Nat, ∀ i : Std.Usize,
      ns.val.length - i.val ≤ k → validate.validate_names_from ns i = ok true →
      ∀ n ∈ ns.val.drop i.val, NameWF n := by
  intro k
  induction k with
  | zero => intro i hk _; rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i hk h
    by_cases hi : i.val ≥ ns.val.length
    · rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · have hlt : i.val < ns.val.length := by scalar_tac
      rw [validate.validate_names_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len ns by scalar_tac)] at h
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ns.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ns i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b, hb, h⟩ := h
      cases b with
      | false => simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
      | true =>
        simp only [if_true, bind_eq_ok_iff, hw, Result.ok.injEq, exists_eq_left'] at h
        rw [List.drop_eq_getElem_cons hlt]
        intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact validate_name_sound _ hb
        · exact ih w (by scalar_tac) h n (by rw [hwv]; exact hn)

/-- `validate::validate_names` establishes `NamesWF`. -/
theorem validate_names_sound {ns : alloc.vec.Vec name.Name}
    (h : validate.validate_names ns = ok true) : NamesWF ns := by
  rw [validate.validate_names] at h
  intro n hn
  exact validate_names_from_sound ns.val.length 0#usize (by scalar_tac) h n (by simpa using hn)

/-- The level walk from `i` on. -/
theorem validate_levels_from_sound {us : alloc.vec.Vec level.Level} :
    ∀ k : Nat, ∀ i : Std.Usize,
      us.val.length - i.val ≤ k → validate.validate_levels_from us i = ok true →
      ∀ u ∈ us.val.drop i.val, LevelWF u := by
  intro k
  induction k with
  | zero => intro i hk _; rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i hk h
    by_cases hi : i.val ≥ us.val.length
    · rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · have hlt : i.val < us.val.length := by scalar_tac
      rw [validate.validate_levels_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len us by scalar_tac)] at h
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := us.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec us i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b, hb, h⟩ := h
      cases b with
      | false => simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
      | true =>
        simp only [if_true, bind_eq_ok_iff, hw, Result.ok.injEq, exists_eq_left'] at h
        rw [List.drop_eq_getElem_cons hlt]
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact validate_level_sound _ hb
        · exact ih w (by scalar_tac) h u (by rw [hwv]; exact hu)

/-- `validate::validate_levels` establishes `LevelsWF`. -/
theorem validate_levels_sound {us : alloc.vec.Vec level.Level}
    (h : validate.validate_levels us = ok true) : LevelsWF us := by
  rw [validate.validate_levels] at h
  intro u hu
  exact validate_levels_from_sound us.val.length 0#usize (by scalar_tac) h u (by simpa using hu)

/-! ## The sealed zero-ness datum

`PropWhen` is the one type with no stored word, so the validator rebuilds it
through the public view and compares with `prop_when::beq` — which *is*
con-leche's `equivR`, the representation comparison.  `equiv_r_exact` is what
turns that `true` into an equality of representations: on representations
whose stored names are well formed, `equivR` is equality.  (`PropWhen.beq_iff`
will not do: it wants `WFShape` on *both* sides, and the left one is the datum
whose well-formedness is being established.) -/

/-- `name::beq` is exact on well-formed names (`Refine/Name.lean`'s
`beq_refines` with the abstraction's injectivity). -/
private theorem name_beq_true {a b : name.Name} (ha : NameWF a) (hb : NameWF b)
    (h : name.beq a b = ok true) : a = b :=
  Name.absName_injective ha hb (of_decide_eq_true (Name.beq_refines ha hb h).symm)

/-- `prop_when::names_beq` is exact on well-formed name vectors. -/
private theorem names_beq_true {ps qs : alloc.vec.Vec name.Name}
    (hps : NamesWF ps) (hqs : NamesWF qs) (h : prop_when.names_beq ps qs = ok true) :
    ps = qs := by
  rw [prop_when.names_beq] at h
  have := (PropWhen.names_beq_from_refines hps hqs ps.length 0#usize true
    (by scalar_tac) h).mp rfl
  exact alloc.vec.Vec.ext _ _ (by simpa using this)

/-- **`equivR` is equality** on representations whose stored names are well
formed: five diagonal cases, twenty `ok false`s. -/
theorem equiv_r_exact {ra rb : prop_when.PropWhenRepr}
    (ha : ∀ n ∈ PropWhen.reprList ra, NameWF n)
    (hb : ∀ n ∈ PropWhen.reprList rb, NameWF n)
    (h : prop_when.equiv_r ra rb = ok true) : ra = rb := by
  cases ra <;> cases rb <;>
    simp only [prop_when.equiv_r] at h <;>
    first
      | rfl
      | (simp only [Result.ok.injEq] at h; exact absurd h Bool.false_ne_true)
      | skip
  · -- One / One
    rw [name_beq_true (ha _ (by simp [PropWhen.reprList]))
      (hb _ (by simp [PropWhen.reprList])) h]
  · -- Two / Two
    rename_i a b c d
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    cases b1 with
    | false => simp at h
    | true =>
      simp only [if_true] at h
      rw [name_beq_true (ha a (by simp [PropWhen.reprList]))
            (hb c (by simp [PropWhen.reprList])) hb1,
          name_beq_true (ha b (by simp [PropWhen.reprList]))
            (hb d (by simp [PropWhen.reprList])) h]
  · -- Many / Many
    rename_i ps qs
    rw [names_beq_true (fun n hn => ha n (by simpa [PropWhen.reprList] using hn))
      (fun n hn => hb n (by simpa [PropWhen.reprList] using hn)) h]

/-- `prop_when::to_list_opt` reads the representation's parameter list out,
and is `none` exactly at `Never`. -/
private theorem to_list_opt_val {pw : prop_when.PropWhen}
    {o : Option (alloc.vec.Vec name.Name)} (h : prop_when.to_list_opt pw = ok o) :
    (o = none ∧ pw.repr = .Never) ∨
      (∃ v, o = some v ∧ v.val = PropWhen.reprList pw.repr) := by
  obtain ⟨r⟩ := pw
  cases r with
  | Never =>
    left; simp only [prop_when.to_list_opt, Result.ok.injEq] at h
    exact ⟨h.symm, rfl⟩
  | Always =>
    right; simp only [prop_when.to_list_opt, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, hv, rfl⟩ := h; exact ⟨v, rfl, PropWhen.to_list_val hv⟩
  | One p =>
    right; simp only [prop_when.to_list_opt, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, hv, rfl⟩ := h; exact ⟨v, rfl, PropWhen.to_list_val hv⟩
  | Two p q =>
    right; simp only [prop_when.to_list_opt, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, hv, rfl⟩ := h; exact ⟨v, rfl, PropWhen.to_list_val hv⟩
  | Many ps =>
    right; simp only [prop_when.to_list_opt, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, hv, rfl⟩ := h; exact ⟨v, rfl, PropWhen.to_list_val hv⟩

/-- `validate::validate_prop_when` establishes `PropWhenWF`. -/
theorem validate_prop_when_sound {pw : prop_when.PropWhen}
    (h : validate.validate_prop_when pw = ok true) : PropWhenWF pw := by
  rw [validate.validate_prop_when] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  rcases to_list_opt_val ho with ⟨rfl, hrep⟩ | ⟨ps, rfl, hlist⟩
  · -- `never`: the representation *is* what `prop_when::never` builds
    refine PropWhenWF.never ?_
    rw [prop_when.never, PropWhen.of_repr_eq, ← hrep]
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases b with
    | false => simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    | true =>
      simp only [if_true, bind_eq_ok_iff] at h
      obtain ⟨pw2, hpw2, h⟩ := h
      have hps : NamesWF ps := validate_names_sound hb
      have hwf2 : PropWhenWF pw2 := PropWhen.if_all_zero_wf hps hpw2
      have hsh2 := PropWhen.wf_shape hwf2
      rw [prop_when.beq] at h
      have hre : pw.repr = pw2.repr :=
        equiv_r_exact (fun n hn => hps n (by rw [hlist]; exact hn)) hsh2.1 h
      have : pw = pw2 := by
        obtain ⟨ra⟩ := pw; obtain ⟨rb⟩ := pw2; simp only [] at hre; rw [hre]
      rw [this]; exact hwf2

/-- `validate::validate_binder_meta` establishes `BinderMetaWF`. -/
theorem validate_binder_meta_sound {m : expr.BinderMeta}
    (h : validate.validate_binder_meta m = ok true) : BinderMetaWF m := by
  rw [validate.validate_binder_meta] at h
  simp only [arc_deref_eq, bind_tc_ok] at h
  exact validate_prop_when_sound h

/-- `validate::validate_literal` establishes `LiteralWF`. -/
theorem validate_literal_sound {l : expr.Literal}
    (h : validate.validate_literal l = ok true) : LiteralWF l := by
  rw [validate.validate_literal.eq_def] at h
  cases l with
  | NatVal n =>
    simp only [arc_deref_eq, bind_tc_ok] at h
    exact validate_nat_sound h
  | StrVal s =>
    simp only [arc_deref_eq, bind_tc_ok] at h
    exact validate_str_sound h

/-! ## Terms

The walk's frame — probe, arm, record — is peeled once (`expr_peel`), exactly
as `Refine/Expr.lean` peels `beq_go`'s frame off `beq_arm`, and what is left is
a ten-case constructor induction on the term.  `Expr.ind'` is the structural
recursor with the `Arc` and node layers skipped, the `Expr` twin of
`Refine/Abs.lean`'s `Level.ind'`/`Name.ind'`. -/

/-- Structural induction on the port's `Expr` tree. -/
@[elab_as_elim] theorem Expr.ind' {motive : expr.Expr → Prop}
    (bvar : ∀ d i, motive (.mk (.mk d (.Bvar i))))
    (fvar : ∀ d i ty, motive ty → motive (.mk (.mk d (.Fvar i ty))))
    (sort : ∀ d u, motive (.mk (.mk d (.«Sort» u))))
    (mk_const : ∀ d n us, motive (.mk (.mk d (.Const n us))))
    (app : ∀ d f a, motive f → motive a → motive (.mk (.mk d (.App f a))))
    (lam : ∀ d ty b m, motive ty → motive b → motive (.mk (.mk d (.Lam ty b m))))
    (forall_e : ∀ d ty b m, motive ty → motive b → motive (.mk (.mk d (.ForallE ty b m))))
    (let_e : ∀ d ty v b, motive ty → motive v → motive b →
      motive (.mk (.mk d (.LetE ty v b))))
    (lit : ∀ d l, motive (.mk (.mk d (.Lit l))))
    (proj : ∀ d s i x, motive x → motive (.mk (.mk d (.Proj s i x)))) :
    ∀ e, motive e :=
  fun e => expr.Expr.rec
    (motive_1 := fun k => ∀ d, motive (.mk (.mk d k)))
    (motive_2 := fun nd => motive (.mk nd))
    (motive_3 := motive)
    (fun i d => bvar d i)
    (fun i ty hty d => fvar d i ty hty)
    (fun u d => sort d u)
    (fun n us d => mk_const d n us)
    (fun f a hf ha d => app d f a hf ha)
    (fun ty b m hty hb d => lam d ty b m hty hb)
    (fun ty b m hty hb d => forall_e d ty b m hty hb)
    (fun ty v b hty hv hb d => let_e d ty v b hty hv hb)
    (fun l d => lit d l)
    (fun s i x hx d => proj d s i x hx)
    (fun d _k hk => hk d)
    (fun _ hnd => hnd)
    e

/-- The stored word of a node, the `Expr` twin of `name_hash_data_mk`. -/
@[simp, rust_reduce] theorem expr_data_mk (d : Std.U64) (k : expr.ExprKind) :
    expr.data (.mk (.mk d k)) = ok d := by simp [expr.data]

/-- **The memo frame peeled**: a term the walk accepted was accepted by the
arm.  The probe never hits in the model (`seen_hit_false`), so the hit branch
is unreachable and the write-back changes the table and never the verdict. -/
theorem expr_peel {e : expr.Expr}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_expr m e = ok (true, r)) :
    ∃ hm, validate.validate_expr_arm m e = ok (true, hm) := by
  rw [validate.validate_expr.eq_def] at h
  obtain ⟨key, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  rw [seen_hit_false hb] at h
  simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
  obtain ⟨p, hp, h⟩ := h
  obtain ⟨b1, hm⟩ := p
  cases b1 with
  | false => simp at h
  | true => exact ⟨hm, hp⟩

/-- Two subterms in sequence: both were accepted. -/
theorem expr2_split {a b : expr.Expr}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_expr2 m a b = ok (true, r)) :
    (∃ r1, validate.validate_expr m a = ok (true, r1)) ∧
      (∃ m1 r2, validate.validate_expr m1 b = ok (true, r2)) := by
  rw [validate.validate_expr2] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b1, hm⟩ := p
  cases b1 with
  | false => simp at h
  | true => exact ⟨⟨hm, hp⟩, ⟨hm, r, h⟩⟩

/-- Three subterms in sequence (`.letE`). -/
theorem expr3_split {a b c : expr.Expr}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_expr3 m a b c = ok (true, r)) :
    (∃ r1, validate.validate_expr m a = ok (true, r1)) ∧
      (∃ m1 r2, validate.validate_expr m1 b = ok (true, r2)) ∧
      (∃ m2 r3, validate.validate_expr m2 c = ok (true, r3)) := by
  rw [validate.validate_expr3] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b1, hm⟩ := p
  cases b1 with
  | false => simp at h
  | true =>
    obtain ⟨h1, h2⟩ := expr2_split hp
    exact ⟨h1, h2, ⟨hm, r, h⟩⟩

/-! The ten smart constructors' shapes, trimmed to what this file needs: the
node, without `Refine/Expr.lean`'s packed-word clauses (a `grind` rule's
conclusion is internalised at every instance, and the bit clauses are dead
weight here). -/

theorem bvar_node {i : Std.U64} {e : expr.Expr} (h : expr.bvar i = ok e) :
    ∃ d, e = .mk (.mk d (.Bvar i)) := let ⟨d, hd, _⟩ := Expr.bvar_inv h; ⟨d, hd⟩

theorem fvar_node {i : Std.U64} {ty e : expr.Expr} (h : expr.fvar i ty = ok e) :
    ∃ d, e = .mk (.mk d (.Fvar i ty)) := let ⟨d, hd, _⟩ := Expr.fvar_inv h; ⟨d, hd⟩

theorem sort_node {u : level.Level} {e : expr.Expr} (h : expr.sort u = ok e) :
    ∃ d, e = .mk (.mk d (.«Sort» u)) := let ⟨d, _, _, hd, _⟩ := Expr.sort_inv h; ⟨d, hd⟩

theorem mk_const_node {n : name.Name} {us : alloc.vec.Vec level.Level} {e : expr.Expr}
    (h : expr.mk_const n us = ok e) : ∃ d, e = .mk (.mk d (.Const n us)) :=
  let ⟨d, _, _, hd, _⟩ := Expr.mk_const_inv h; ⟨d, hd⟩

theorem app_node {f a e : expr.Expr} (h : expr.app f a = ok e) :
    ∃ d, e = .mk (.mk d (.App f a)) := let ⟨d, hd, _⟩ := Expr.app_inv h; ⟨d, hd⟩

theorem lam_node {ty bo e : expr.Expr} {m : expr.BinderMeta} (h : expr.lam ty bo m = ok e) :
    ∃ d, e = .mk (.mk d (.Lam ty bo m)) := let ⟨d, hd, _⟩ := Expr.lam_inv h; ⟨d, hd⟩

theorem forall_e_node {ty bo e : expr.Expr} {m : expr.BinderMeta}
    (h : expr.forall_e ty bo m = ok e) : ∃ d, e = .mk (.mk d (.ForallE ty bo m)) :=
  let ⟨d, hd, _⟩ := Expr.forall_e_inv h; ⟨d, hd⟩

theorem let_e_node {ty v bo e : expr.Expr} (h : expr.let_e ty v bo = ok e) :
    ∃ d, e = .mk (.mk d (.LetE ty v bo)) := let ⟨d, hd, _⟩ := Expr.let_e_inv h; ⟨d, hd⟩

theorem lit_node {l : expr.Literal} {e : expr.Expr} (h : expr.lit l = ok e) :
    ∃ d, e = .mk (.mk d (.Lit l)) := let ⟨d, hd, _⟩ := Expr.lit_inv h; ⟨d, hd⟩

theorem proj_node {s : name.Name} {i : Std.U64} {x e : expr.Expr}
    (h : expr.proj s i x = ok e) : ∃ d, e = .mk (.mk d (.Proj s i x)) :=
  let ⟨d, hd, _⟩ := Expr.proj_inv h; ⟨d, hd⟩

section ExprIdiom
attribute [local grind →] ExprWF.bvar Expr.fvar_wf' Expr.sort_wf' Expr.mk_const_wf'
  Expr.app_wf' Expr.lam_wf' Expr.forall_e_wf' Expr.let_e_wf' Expr.lit_wf' Expr.proj_wf'
  bvar_node fvar_node sort_node mk_const_node app_node lam_node forall_e_node
  let_e_node lit_node proj_node
  expr_peel expr2_split expr3_split
  validate_name_sound validate_level_sound validate_levels_sound
  validate_literal_sound validate_binder_meta_sound
  Env.levels_copy_refines Expr.literal_dup_eq Expr.binder_meta_dup_eq
attribute [local grind =] expr_data_mk

/-- `validate::validate_expr` establishes `ExprWF`.  The frame is peeled by
`expr_peel` and the ten arms are the task-#71 idiom. -/
theorem validate_expr_sound : ∀ e : expr.Expr,
    ∀ m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr),
      validate.validate_expr m e = ok (true, r) → ExprWF e := by
  intro e
  induction e using Expr.ind' with
  | bvar d i =>
    intro m r h
    obtain ⟨hm, ha⟩ := expr_peel h
    rw [validate.validate_expr_arm.eq_def] at ha; rust_norm ha
    all_goals rust_grind
  | fvar d i ty ih =>
    intro m r h
    obtain ⟨hm, ha⟩ := expr_peel h
    rw [validate.validate_expr_arm.eq_def] at ha; rust_norm ha
    all_goals rust_grind
  | sort d u =>
    intro m r h
    obtain ⟨hm, ha⟩ := expr_peel h
    rw [validate.validate_expr_arm.eq_def] at ha; rust_norm ha
    all_goals rust_grind
  | mk_const d n us =>
    intro m r h
    obtain ⟨hm, ha⟩ := expr_peel h
    rw [validate.validate_expr_arm.eq_def] at ha; rust_norm ha
    all_goals rust_grind
  | app d f a ihf iha =>
    intro m r h
    obtain ⟨hm, ha⟩ := expr_peel h
    rw [validate.validate_expr_arm.eq_def] at ha; rust_norm ha
    all_goals rust_grind
  | lam d ty b bm ihty ihb =>
    intro m r h
    obtain ⟨hm, ha⟩ := expr_peel h
    rw [validate.validate_expr_arm.eq_def] at ha; rust_norm ha
    all_goals rust_grind
  | forall_e d ty b bm ihty ihb =>
    intro m r h
    obtain ⟨hm, ha⟩ := expr_peel h
    rw [validate.validate_expr_arm.eq_def] at ha; rust_norm ha
    all_goals rust_grind
  | let_e d ty v b ihty ihv ihb =>
    intro m r h
    obtain ⟨hm, ha⟩ := expr_peel h
    rw [validate.validate_expr_arm.eq_def] at ha; rust_norm ha
    all_goals rust_grind
  | lit d l =>
    intro m r h
    obtain ⟨hm, ha⟩ := expr_peel h
    rw [validate.validate_expr_arm.eq_def] at ha; rust_norm ha
    all_goals rust_grind
  | proj d s i x ihx =>
    intro m r h
    obtain ⟨hm, ha⟩ := expr_peel h
    rw [validate.validate_expr_arm.eq_def] at ha; rust_norm ha
    all_goals rust_grind
end ExprIdiom

/-! ## The term vector

The last index recursion, and the only one that threads the visited set: the
set goes into the next entry's walk, which is what makes the pass linear in
the stream's distinct nodes rather than in each declaration's. -/

/-- The term walk from `i` on. -/
theorem validate_exprs_from_sound {es : alloc.vec.Vec expr.Expr} :
    ∀ k : Nat, ∀ (i : Std.Usize)
      (m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)),
      es.val.length - i.val ≤ k → validate.validate_exprs_from m es i = ok (true, r) →
      ∀ e ∈ es.val.drop i.val, ExprWF e := by
  intro k
  induction k with
  | zero => intro i m r hk _; rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i m r hk h
    by_cases hi : i.val ≥ es.val.length
    · rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · have hlt : i.val < es.val.length := by scalar_tac
      rw [validate.validate_exprs_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len es by scalar_tac)] at h
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := es.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec es i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨p, hp, h⟩ := h
      obtain ⟨b, hm⟩ := p
      cases b with
      | false => simp at h
      | true =>
        have h2 : (do let i2 ← i + 1#usize
                      validate.validate_exprs_from hm es i2) = ok (true, r) := h
        rw [hw] at h2; simp only [bind_tc_ok] at h2
        rw [List.drop_eq_getElem_cons hlt]
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact validate_expr_sound _ m hm hp
        · exact ih w hm r (by scalar_tac) h2 e (by rw [hwv]; exact he)

/-- `validate::validate_exprs` establishes `ExprsWF`. -/
theorem validate_exprs_sound {es : alloc.vec.Vec expr.Expr}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_exprs m es = ok (true, r)) : ExprsWF es := by
  rw [validate.validate_exprs] at h
  intro e he
  exact validate_exprs_from_sound es.val.length 0#usize m r (by scalar_tac) h e
    (by simpa using he)

/-! ## The stored-constant records and the declarations

`kernel::env`'s records carry no derived data of their own (`Refine/Abs.lean`),
so each predicate is the conjunction of its fields' and each validator is a
chain of guards: the task-#71 idiom with the walks' soundness lemmas as `→`
rules and the predicates themselves unfolded. -/

section RecordIdiom
attribute [local grind →] validate_name_sound validate_names_sound
  validate_level_sound validate_levels_sound validate_expr_sound
  validate_exprs_sound validate_prop_when_sound
attribute [local grind] ConstantValWF ProjTableWF IndCapsWF RecRuleWF RecRuleFireWF

/-- `validate::validate_constant_val` establishes `ConstantValWF`. -/
theorem validate_constant_val_sound {cv : env.ConstantVal}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_constant_val m cv = ok (true, r)) : ConstantValWF cv := by
  rw [validate.validate_constant_val] at h; rust_norm h
  all_goals rust_grind

/-- `validate::validate_proj_table` establishes `ProjTableWF`. -/
theorem validate_proj_table_sound {t : env.ProjTable}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_proj_table m t = ok (true, r)) : ProjTableWF t := by
  rw [validate.validate_proj_table] at h; rust_norm h
  all_goals rust_grind

/-- `validate::validate_ind_caps` establishes `IndCapsWF`. -/
theorem validate_ind_caps_sound {c : env.IndCaps}
    (h : validate.validate_ind_caps c = ok true) : IndCapsWF c := by
  rw [validate.validate_ind_caps] at h; rust_norm h
  all_goals rust_grind

/-- `validate::validate_rec_rule_fire` establishes `RecRuleFireWF`. -/
theorem validate_rec_rule_fire_sound {f : env.RecRuleFire}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_rec_rule_fire m f = ok (true, r)) : RecRuleFireWF f := by
  rw [validate.validate_rec_rule_fire.eq_def] at h; rust_norm h
  all_goals rust_grind

attribute [local grind →] validate_rec_rule_fire_sound

/-- `validate::validate_rec_rule` establishes `RecRuleWF`. -/
theorem validate_rec_rule_sound {rr : env.RecRule}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_rec_rule m rr = ok (true, r)) : RecRuleWF rr := by
  rw [validate.validate_rec_rule] at h; rust_norm h
  all_goals rust_grind
end RecordIdiom

/-! ## The rule vector, the stored constants and the declarations

The remaining three index recursions and the two constructor dispatches.  Each
step has the same shape — `let (b, hm) ← …; if b then … else ok (false, hm)` —
so each inversion is the same four lines: invert the bind, destructure the
pair, and the `false` branch contradicts `ok (true, r)`. -/

/-- The rule walk from `i` on. -/
theorem validate_rec_rules_from_sound {rs : alloc.vec.Vec env.RecRule} :
    ∀ k : Nat, ∀ (i : Std.Usize)
      (m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)),
      rs.val.length - i.val ≤ k →
      validate.validate_rec_rules_from m rs i = ok (true, r) →
      ∀ x ∈ rs.val.drop i.val, RecRuleWF x := by
  intro k
  induction k with
  | zero => intro i m r hk _; rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i m r hk h
    by_cases hi : i.val ≥ rs.val.length
    · rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · have hlt : i.val < rs.val.length := by scalar_tac
      rw [validate.validate_rec_rules_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len rs by scalar_tac)] at h
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := rs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨p, hp, h⟩ := h
      obtain ⟨b, hm⟩ := p
      cases b with
      | false => simp at h
      | true =>
        have h2 : (do let i2 ← i + 1#usize
                      validate.validate_rec_rules_from hm rs i2) = ok (true, r) := h
        rw [hw] at h2; simp only [bind_tc_ok] at h2
        rw [List.drop_eq_getElem_cons hlt]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact validate_rec_rule_sound hp
        · exact ih w hm r (by scalar_tac) h2 x (by rw [hwv]; exact hx)

/-- `validate::validate_rec_rules` establishes `RecRulesWF`. -/
theorem validate_rec_rules_sound {rs : alloc.vec.Vec env.RecRule}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_rec_rules m rs = ok (true, r)) : RecRulesWF rs := by
  rw [validate.validate_rec_rules] at h
  intro x hx
  exact validate_rec_rules_from_sound rs.val.length 0#usize m r (by scalar_tac) h x
    (by simpa using hx)

/-- `validate::validate_constant_info` establishes `ConstantInfoWF`. -/
theorem validate_constant_info_sound {c : env.ConstantInfo}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_constant_info m c = ok (true, r)) : ConstantInfoWF c := by
  rw [validate.validate_constant_info.eq_def] at h
  cases c with
  | AxiomInfo cv => exact validate_constant_val_sound h
  | CtorInfo cv a b => exact validate_constant_val_sound h
  | ProjInfo t => exact validate_proj_table_sound h
  | DefnInfo cv v hint =>
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hm⟩ := p
    cases b with
    | false => simp at h
    | true => exact ⟨validate_constant_val_sound hp, validate_expr_sound _ hm r h⟩
  | ThmInfo cv v =>
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hm⟩ := p
    cases b with
    | false => simp at h
    | true => exact ⟨validate_constant_val_sound hp, validate_expr_sound _ hm r h⟩
  | IndInfo cv caps =>
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hm⟩ := p
    cases b with
    | false => simp at h
    | true =>
      have h2 : (do let b1 ← validate.validate_ind_caps caps
                    ok (b1, hm)) = ok (true, r) := h
      obtain ⟨b1, hb1, h2⟩ := bind_eq_ok_iff.mp h2
      simp only [Result.ok.injEq, Prod.mk.injEq] at h2
      rw [h2.1] at hb1
      exact ⟨validate_constant_val_sound hp, validate_ind_caps_sound hb1⟩
  | RecInfo cv a b rs =>
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨bb, hm⟩ := p
    cases bb with
    | false => simp at h
    | true => exact ⟨validate_constant_val_sound hp, validate_rec_rules_sound h⟩

/-- The stored-constant walk from `i` on. -/
theorem validate_constant_infos_from_sound {cs : alloc.vec.Vec env.ConstantInfo} :
    ∀ k : Nat, ∀ (i : Std.Usize)
      (m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)),
      cs.val.length - i.val ≤ k →
      validate.validate_constant_infos_from m cs i = ok (true, r) →
      ∀ c ∈ cs.val.drop i.val, ConstantInfoWF c := by
  intro k
  induction k with
  | zero => intro i m r hk _; rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i m r hk h
    by_cases hi : i.val ≥ cs.val.length
    · rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · have hlt : i.val < cs.val.length := by scalar_tac
      rw [validate.validate_constant_infos_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len cs by scalar_tac)] at h
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := cs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨p, hp, h⟩ := h
      obtain ⟨b, hm⟩ := p
      cases b with
      | false => simp at h
      | true =>
        have h2 : (do let i2 ← i + 1#usize
                      validate.validate_constant_infos_from hm cs i2) = ok (true, r) := h
        rw [hw] at h2; simp only [bind_tc_ok] at h2
        rw [List.drop_eq_getElem_cons hlt]
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact validate_constant_info_sound hp
        · exact ih w hm r (by scalar_tac) h2 c (by rw [hwv]; exact hc)

/-- `validate::validate_constant_infos` establishes `ConstantInfosWF`. -/
theorem validate_constant_infos_sound {cs : alloc.vec.Vec env.ConstantInfo}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_constant_infos m cs = ok (true, r)) : ConstantInfosWF cs := by
  rw [validate.validate_constant_infos] at h
  intro c hc
  exact validate_constant_infos_from_sound cs.val.length 0#usize m r (by scalar_tac) h c
    (by simpa using hc)

/-- `validate::validate_decl` establishes `DeclCWF`. -/
theorem validate_decl_sound {d : parsed_c.DeclC}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_decl m d = ok (true, r)) : DeclCWF d := by
  rw [validate.validate_decl.eq_def] at h
  cases d with
  | AxiomDecl cv => exact validate_constant_val_sound h
  | BasisDecl k => exact trivial
  | IndDecl block n_p => exact validate_constant_infos_sound h
  | DefnDecl cv v hint =>
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hm⟩ := p
    cases b with
    | false => simp at h
    | true => exact ⟨validate_constant_val_sound hp, validate_expr_sound _ hm r h⟩
  | ThmDecl cv v =>
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hm⟩ := p
    cases b with
    | false => simp at h
    | true => exact ⟨validate_constant_val_sound hp, validate_expr_sound _ hm r h⟩
  | OpaqueDecl cv v =>
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hm⟩ := p
    cases b with
    | false => simp at h
    | true => exact ⟨validate_constant_val_sound hp, validate_expr_sound _ hm r h⟩

/-- The declaration walk from `i` on. -/
theorem validate_decls_from_sound {ds : alloc.vec.Vec parsed_c.DeclC} :
    ∀ k : Nat, ∀ (i : Std.Usize)
      (m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)),
      ds.val.length - i.val ≤ k →
      validate.validate_decls_from m ds i = ok (true, r) →
      ∀ d ∈ ds.val.drop i.val, DeclCWF d := by
  intro k
  induction k with
  | zero => intro i m r hk _; rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i m r hk h
    by_cases hi : i.val ≥ ds.val.length
    · rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · have hlt : i.val < ds.val.length := by scalar_tac
      rw [validate.validate_decls_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len ds by scalar_tac)] at h
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ds.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ds i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨p, hp, h⟩ := h
      obtain ⟨b, hm⟩ := p
      cases b with
      | false => simp at h
      | true =>
        have h2 : (do let i2 ← i + 1#usize
                      validate.validate_decls_from hm ds i2) = ok (true, r) := h
        rw [hw] at h2; simp only [bind_tc_ok] at h2
        rw [List.drop_eq_getElem_cons hlt]
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact validate_decl_sound hp
        · exact ih w hm r (by scalar_tac) h2 d (by rw [hwv]; exact hd)

/-- **The pass is sound**: what `cached::installed::check_decls` applies at the
accept of its first step, and what `Refine/Installed.lean` uses to discharge
task #60's `hds`. -/
theorem validate_decls_sound {ds : alloc.vec.Vec parsed_c.DeclC}
    {m r : ron.hashmap.HashMap Std.U64 (alloc.vec.Vec expr.Expr)}
    (h : validate.validate_decls m ds = ok (true, r)) :
    ∀ d ∈ ds.val, DeclCWF d := by
  rw [validate.validate_decls] at h
  intro d hd
  exact validate_decls_from_sound ds.val.length 0#usize m r (by scalar_tac) h d
    (by simpa using hd)

/-! ## The gate at the entry of `check_decls`

`cached::installed::check_decls` is the validation pass followed by
`check_decls_go`, the cited fold's body (task #73 split them so that this
lemma can name what follows the pass without spelling the fold out).  On the
pass's reject the outcome is the port's own `Native` decline — `ErrSimPos`
claims nothing about it — and on its accept `hds` falls out and the run is the
fold's own. -/

theorem check_decls_gate {mode : env.CheckMode}
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {ds : alloc.vec.Vec parsed_c.DeclC}
    {out : core.result.Result env.Env (core_types.CheckError × Std.U64)}
    (h : cached.installed.check_decls mode pins ds = ok out) :
    (∃ msg, out = .Err (.Native msg, 0#u64)) ∨
      ((∀ d ∈ ds.val, DeclCWF d) ∧
        cached.installed.check_decls_go mode pins ds = ok out) := by
  rw [cached.installed.check_decls] at h
  obtain ⟨m0, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hval, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨vb, vm⟩ := v
  cases vb with
  | true => exact Or.inr ⟨validate_decls_sound hval, h⟩
  | false =>
    left
    have h2 : (do let v ← cached.installed.validate_reject_message
                  let ce ← core_types.native v
                  ok (core.result.Result.Err (ce, 0#u64))) = ok out := h
    obtain ⟨msg, -, h2⟩ := bind_eq_ok_iff.mp h2
    obtain ⟨ce, hce, h2⟩ := bind_eq_ok_iff.mp h2
    rw [core_types.native, Result.ok.injEq] at hce
    rw [← Result.ok_injective h2, ← hce]
    exact ⟨msg, rfl⟩

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing here evaluates anything: every lemma is about an arbitrary term, so the
census is con-leche's own three axioms. -/

/-- info: 'ConRon.Refine.Validate.validate_decls_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validate_decls_sound

/-- info: 'ConRon.Refine.Validate.validate_expr_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validate_expr_sound

end ConRon.Refine.Validate
