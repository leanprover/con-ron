/-
`ConRon.Refine.Levels` -- the refinement lemmas of
`crates/con-ron-core/src/kernel/levels.rs` (task #93).

`Expr.const`'s `List Level` is not a `Vec<Level>` in the port any more: it is
the canonical three-constructor `Levels`, which spends a tag and one word and
allocates **nothing** for the empty and singleton lists almost every constant
reference carries (`levels.rs`'s module note, DESIGN.md §3.2).  The Lean model
of it is an ordinary inductive, so the abstraction is `absConstLevels`
(`Refine/Abs.lean`) and the invariant is `ConstLevelsWF` -- whose second
clause, "`Many` never holds fewer than two", is the canonical form the Rust
`beq`, `len` and `head_d` all read off the constructor.

Two *pure* functions carry the whole file: `ofVec`, the `Levels` that
`levels::of_vec` builds from a list, and `vecOf`, the list behind a canonical
`Levels`.  They are inverse under `ConstLevelsWF`, both commute with the
abstraction, and `levels.of_vec us = ok (ofVec us)` is a `simp` lemma -- which
is why `expr.mk_const` keeps the *shape* of its task-#38 refinement lemmas
(`Refine/Expr.lean`'s `mk_const_inv`, `mk_const_wf`, `mk_const_refines`): the
node it builds is `.Const n (ofVec us)` where it used to be `.Const n us`, and
`absConstLevels (ofVec us) = absLevels us` closes the difference at every one
of the 141 sites that invert it.

`vec_index_getElem?` moved here from `Refine/ExprOps.lean` (which now
`export`s it under its old name, so its 110 call sites are unchanged): this
file is below `ExprOps.lean` and `vec_copy_from_val` needs it.
-/
import ConRon.Refine.Level
import ConRon.Refine.HashMap

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

/-- `Vec::index` without an `Inhabited` instance on the element type (the
`getElem!` form of `HashMap.vec_index_eq` is unavailable for `expr::Expr`).
Task #93 moved it here from `Refine/ExprOps.lean`, which now `export`s it. -/
theorem vec_index_getElem? {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    exact congrArg some (Result.ok_injective h)

/-- The converse: reading an index that is there. -/
theorem vec_index_of_getElem? {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : v.val[i.val]? = some x) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    show v[i.val]? = v.val[i.val]? from rfl, h]

end ConRon.Refine

namespace ConRon.Refine.Levels

/-! ## The two pure functions -/

/-- The `Levels` that `levels::of_vec` builds: the narrowest constructor that
holds the list.  Pure, because `of_vec` cannot fail -- it allocates and dups,
and both are the identity in the model. -/
def ofVec (us : alloc.vec.Vec level.Level) : levels.Levels :=
  match us.val with
  | [] => .Zero
  | [u] => .One u
  | _ => .Many us

/-- The `Vec<Level>` behind a `Levels`: the list it stands for.  The inverse
of `ofVec` on the canonical forms (`ofVec_vecOf`), and the witness that turns
a `mk_const_levels` obligation into a `mk_const` one. -/
def vecOf : levels.Levels → alloc.vec.Vec level.Level
  | .Zero => alloc.vec.Vec.new level.Level
  | .One u => alloc.vec.Vec.from [u] (by simp; scalar_tac)
  | .Many us => us

@[simp] theorem vecOf_Zero_val : (vecOf .Zero).val = [] := rfl
@[simp] theorem vecOf_One_val (u : level.Level) : (vecOf (.One u)).val = [u] := rfl
@[simp] theorem vecOf_Many (us : alloc.vec.Vec level.Level) : vecOf (.Many us) = us := rfl

theorem len_eq_one_iff {us : alloc.vec.Vec level.Level} :
    alloc.vec.Vec.len us = 1#usize ↔ us.val.length = 1 := by
  constructor
  · intro h
    have h1 : (alloc.vec.Vec.len us).val = 1 := by rw [h]; rfl
    rw [alloc.vec.Vec.len_val] at h1; exact h1
  · intro h
    have h1 : (alloc.vec.Vec.len us).val = 1 := by rw [alloc.vec.Vec.len_val]; exact h
    scalar_tac

/-- The index of a one-element vector. -/
theorem index_zero_of_singleton {us : alloc.vec.Vec level.Level} {u : level.Level}
    (hv : us.val = [u]) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice level.Level) us 0#usize = ok u :=
  vec_index_of_getElem? (by rw [show (0#usize : Std.Usize).val = 0 from rfl, hv]; rfl)

/-! ## `level::levels_have_param` at the two short lists -/

theorem levels_have_param_nil {us : alloc.vec.Vec level.Level} (hv : us.val = []) :
    level.levels_have_param us = ok false := by
  rw [level.levels_have_param, level.levels_have_param_from.eq_def]
  have hge : ((0#usize : Std.Usize) ≥ alloc.vec.Vec.len us) := by
    rw [HashMap.vec_len_eq_zero_iff.mpr hv]
  simp [hge]

/-- `x >>= (if · then ok true else ok false) = x`: the shape the tail of
`levels_have_param_from` takes once the rest of the list is known empty. -/
theorem bind_ite_self (m : Result Bool) :
    (do let b ← m; if b then (ok true : Result Bool) else ok false) = m := by
  have hf : (fun b : Bool => if b then (ok true : Result Bool) else ok false) = pure := by
    funext b; cases b <;> rfl
  rw [show (do let b ← m; if b then (ok true : Result Bool) else ok false)
      = m >>= (fun b : Bool => if b then (ok true : Result Bool) else ok false) from rfl, hf]
  exact bind_pure m

theorem levels_have_param_singleton {us : alloc.vec.Vec level.Level} {u : level.Level}
    (hv : us.val = [u]) : level.levels_have_param us = level.level_has_param u := by
  have hlen : (alloc.vec.Vec.len us).val = 1 := by simp [hv]
  have hnext : level.levels_have_param_from us 1#usize = ok false := by
    rw [level.levels_have_param_from.eq_def]
    have hge : ((1#usize : Std.Usize) ≥ alloc.vec.Vec.len us) := by scalar_tac
    simp [hge]
  have hadd : ((0#usize : Std.Usize) + 1#usize) = ok 1#usize := by
    obtain ⟨w, hw, hwv⟩ := usize_add_ok (i := (0#usize : Std.Usize)) (by scalar_tac)
    rw [hw, show w = 1#usize by scalar_tac]
  rw [level.levels_have_param, level.levels_have_param_from.eq_def]
  have hlt : ¬ ((0#usize : Std.Usize) ≥ alloc.vec.Vec.len us) := by scalar_tac
  simp only [hlt, if_false, index_zero_of_singleton hv, bind_tc_ok, hadd, hnext]
  exact bind_ite_self _

/-! ## `of_vec`, and the abstraction -/

@[simp] theorem levels_of_vec_eq (us : alloc.vec.Vec level.Level) :
    levels.of_vec us = ok (ofVec us) := by
  rw [levels.of_vec, ofVec]
  rcases hv : us.val with _ | ⟨u, rest⟩
  · simp only [HashMap.vec_len_eq_zero_iff.mpr hv, if_pos]
  · have hne : ¬ (alloc.vec.Vec.len us = 0#usize) := by
      intro hc; rw [HashMap.vec_len_eq_zero_iff.mp hc] at hv; simp at hv
    rcases rest with _ | ⟨u2, rest2⟩
    · have h1 : alloc.vec.Vec.len us = 1#usize := len_eq_one_iff.mpr (by rw [hv]; rfl)
      simp [h1, index_zero_of_singleton hv]
    · have h1 : ¬ (alloc.vec.Vec.len us = 1#usize) := by
        intro hc; have := len_eq_one_iff.mp hc; rw [hv] at this; simp at this
      simp [hne, h1]

@[simp] theorem absConstLevels_ofVec (us : alloc.vec.Vec level.Level) :
    absConstLevels (ofVec us) = absLevels us := by
  rw [ofVec]
  rcases hv : us.val with _ | ⟨u, rest⟩
  · simp [absConstLevels, absLevels, hv]
  · rcases rest with _ | ⟨u2, rest2⟩
    · simp [absConstLevels, absLevels, hv]
    · simp [absConstLevels]

@[simp] theorem absLevels_vecOf (ls : levels.Levels) :
    absLevels (vecOf ls) = absConstLevels ls := by
  cases ls with
  | Zero => rfl
  | One u => simp [absLevels, absConstLevels]
  | Many us => rfl

theorem constLevelsWF_ofVec {us : alloc.vec.Vec level.Level} (h : LevelsWF us) :
    ConstLevelsWF (ofVec us) := by
  rw [ofVec]
  rcases hv : us.val with _ | ⟨u, rest⟩
  · exact trivial
  · rcases rest with _ | ⟨u2, rest2⟩
    · exact h u (by rw [hv]; simp)
    · refine ⟨h, ?_⟩
      rw [hv]; simp

theorem levelsWF_vecOf {ls : levels.Levels} (h : ConstLevelsWF ls) : LevelsWF (vecOf ls) := by
  cases ls with
  | Zero => intro u hu; simp [vecOf, alloc.vec.Vec.new] at hu
  | One u => intro v hv; simp only [vecOf_One_val, List.mem_singleton] at hv; subst hv; exact h
  | Many us => exact h.1

theorem ofVec_vecOf {ls : levels.Levels} (h : ConstLevelsWF ls) : ofVec (vecOf ls) = ls := by
  cases ls with
  | Zero => rfl
  | One u => rfl
  | Many us =>
    have h2 : 2 ≤ (us : alloc.vec.Vec level.Level).val.length := h.2
    rw [vecOf_Many, ofVec]
    split
    · rename_i heq; rw [heq] at h2; simp at h2
    · rename_i heq; rw [heq] at h2; simp at h2
    · rfl

/-! ## The operations -/

@[simp] theorem levels_dup_eq (ls : levels.Levels) : levels.dup ls = ok ls := by
  cases ls <;> simp [levels.dup]

@[simp] theorem levels_len_ofVec (us : alloc.vec.Vec level.Level) :
    levels.len (ofVec us) = ok (alloc.vec.Vec.len us) := by
  rw [ofVec]
  rcases hv : us.val with _ | ⟨u, rest⟩
  · rw [show (alloc.vec.Vec.len us) = 0#usize from HashMap.vec_len_eq_zero_iff.mpr hv]
    simp [levels.len]
  · rcases rest with _ | ⟨u2, rest2⟩
    · rw [show (alloc.vec.Vec.len us) = 1#usize from len_eq_one_iff.mpr (by rw [hv]; rfl)]
      simp [levels.len]
    · simp [levels.len]

@[simp] theorem levels_have_param_ofVec (us : alloc.vec.Vec level.Level) :
    levels.have_param (ofVec us) = level.levels_have_param us := by
  rw [ofVec]
  rcases hv : us.val with _ | ⟨u, rest⟩
  · rw [levels_have_param_nil hv]; simp [levels.have_param]
  · rcases rest with _ | ⟨u2, rest2⟩
    · rw [levels_have_param_singleton hv]; simp [levels.have_param]
    · simp [levels.have_param]

/-! ## `to_vec` -/

/-- The index recursion behind `levels::vec_copy`: the entries from `i` on,
appended to the accumulator.  The same walk as `ExprOps.levels_copy_from_val`,
which this file is below. -/
theorem vec_copy_from_val (N : Nat) :
    ∀ (us : alloc.vec.Vec level.Level) (i : Std.Usize)
      (out r : alloc.vec.Vec level.Level),
      us.val.length - i.val = N →
      levels.vec_copy_from us i out = ok r →
      r.val = out.val ++ us.val.drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro us i out r hN h
    rw [levels.vec_copy_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : us.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val us; scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]
      simp
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, c, hdup, out1, hpush, i2, hi2, hrec⟩ := h
      have hg := vec_index_getElem? hidx
      have hlt : i.val < us.val.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
      have hx : us.val[i.val] = x := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hcx : c = x := Result.ok_injective (hdup.symm.trans (level_dup_eq x))
      subst hcx
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      rw [ih (us.val.length - i2.val) (by omega) us i2 out1 r rfl hrec,
        vec_push_val hpush, hi2v,
        List.drop_eq_getElem_cons hlt, hx]
      simp

theorem vec_copy_val {us r : alloc.vec.Vec level.Level}
    (h : levels.vec_copy us = ok r) : r.val = us.val := by
  rw [levels.vec_copy] at h
  rw [vec_copy_from_val _ us 0#usize _ r rfl h]
  simp [alloc.vec.Vec.with_capacity, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- `levels::to_vec` hands back the list the `Levels` stands for. -/
theorem to_vec_val {ls : levels.Levels} {v : alloc.vec.Vec level.Level}
    (h : levels.to_vec ls = ok v) : v.val = (vecOf ls).val := by
  cases ls with
  | Zero => simp only [levels.to_vec, Result.ok.injEq] at h; rw [← h]; rfl
  | One u =>
    simp only [levels.to_vec, level_dup_eq, bind_tc_ok, levels.one_vec] at h
    rw [vec_push_val h]
    simp [alloc.vec.Vec.with_capacity]
  | Many us =>
    simp only [levels.to_vec, arc_deref_eq, bind_tc_ok] at h
    rw [vec_copy_val h]; rfl

/-! ## The task-#5 statements -/

theorem to_vec_refines {ls : levels.Levels} {v : alloc.vec.Vec level.Level}
    (h : levels.to_vec ls = ok v) : absLevels v = absConstLevels ls := by
  rw [absLevels, to_vec_val h, ← absLevels, absLevels_vecOf]

theorem to_vec_wf {ls : levels.Levels} {v : alloc.vec.Vec level.Level}
    (hwf : ConstLevelsWF ls) (h : levels.to_vec ls = ok v) : LevelsWF v := by
  intro u hu
  refine levelsWF_vecOf hwf u ?_
  rw [← to_vec_val h]; exact hu

/-- The length of a `Levels`' abstraction, off the list behind it. -/
theorem absConstLevels_length (ls : levels.Levels) :
    (absConstLevels ls).length = (vecOf ls).val.length := by
  rw [← absLevels_vecOf, absLevels, List.length_map]

/-- `levels::len` is the length of the list. -/
theorem len_refines {ls : levels.Levels} {k : Std.Usize} (h : levels.len ls = ok k) :
    k.val = (absConstLevels ls).length := by
  cases ls with
  | Zero => simp only [levels.len, Result.ok.injEq] at h; rw [← h]; rfl
  | One u => simp only [levels.len, Result.ok.injEq] at h; rw [← h]; rfl
  | Many us =>
    simp only [levels.len, arc_deref_eq, bind_tc_ok, Result.ok.injEq] at h
    rw [← h, absConstLevels, absLevels]
    simp

/-- `levels::have_param` is `levelsHaveParam`. -/
theorem have_param_refines {ls : levels.Levels} {b : Bool}
    (h : levels.have_param ls = ok b) : b = ConLeche.levelsHaveParam (absConstLevels ls) := by
  rw [← absLevels_vecOf]
  refine Level.levels_have_param_refines ?_
  cases ls with
  | Zero => rw [levels_have_param_nil (us := vecOf (levels.Levels.Zero)) rfl]; exact h
  | One u => rw [levels_have_param_singleton (us := vecOf (levels.Levels.One u)) rfl]; exact h
  | Many us => simpa only [levels.have_param, arc_deref_eq, bind_tc_ok, vecOf_Many] using h

/-- `levels::head_d` on the singleton the two call sites have guarded for. -/
theorem head_d_one {ls : levels.Levels} {u : level.Level}
    (hlen : levels.len ls = ok 1#usize) (h : levels.head_d ls = ok u) :
    absConstLevels ls = [absLevel u] := by
  cases ls with
  | Zero => simp [levels.len] at hlen
  | One v =>
    simp only [levels.head_d, level_dup_eq, Result.ok.injEq] at h
    rw [absConstLevels, ← h]
  | Many us =>
    have hl : (alloc.vec.Vec.len us) = 1#usize := by
      simp only [levels.len, arc_deref_eq, bind_tc_ok, Result.ok.injEq] at hlen
      exact hlen
    have hone : us.val.length = 1 := len_eq_one_iff.mp hl
    obtain ⟨v, hv⟩ : ∃ v, us.val = [v] := by
      match hm : us.val with
      | [] => rw [hm] at hone; simp at hone
      | [v] => exact ⟨v, rfl⟩
      | a :: b :: r => rw [hm] at hone; simp at hone
    simp only [levels.head_d, arc_deref_eq, bind_tc_ok, index_zero_of_singleton hv,
      level_dup_eq, Result.ok.injEq] at h
    rw [absConstLevels, absLevels, hv, ← h]
    simp

theorem head_d_wf {ls : levels.Levels} {u : level.Level}
    (hwf : ConstLevelsWF ls) (h : levels.head_d ls = ok u) : LevelWF u := by
  cases ls with
  | Zero =>
    simp only [levels.head_d] at h
    exact LevelWF.zero h
  | One v =>
    simp only [levels.head_d, level_dup_eq, Result.ok.injEq] at h
    rw [← h]; exact hwf
  | Many us =>
    simp only [levels.head_d, arc_deref_eq, bind_tc_ok] at h
    obtain ⟨x, hidx, hdup⟩ := (bind_eq_ok_iff ..).mp h
    have hg := vec_index_getElem? hidx
    have hx : x ∈ us.val := List.mem_of_getElem? hg
    simp only [level_dup_eq, Result.ok.injEq] at hdup
    rw [← hdup]
    exact hwf.1 x hx

end ConRon.Refine.Levels
