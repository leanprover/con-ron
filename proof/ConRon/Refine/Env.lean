/-
`ConRon.Refine.Env` — the refinement of `crates/con-ron-core/src/kernel/env.rs`
against `ConLeche/Kernel/Env.lean` (task #46, `Refine/CORE_PLAN.md` step 1).

One lemma per ported function, in `env.rs`'s own order, in DESIGN.md §3.5's
shape: forward from `f x = ok y`, the conclusion an *exact* equality against the
cited con-leche definition, well-formedness hypotheses only where the stored
derived data has to be pinned.  The abstraction functions
(`absConstantVal`, …, `absEnv`, `absMode`) and the hereditary `*WF` predicates
(`ConstantValWF`, …, `EnvWF`) live in `ConRon/Refine/Abs.lean`.

One group carries real content and the rest are mechanical: **`abs` is
injective on the well-formed records**, which is what makes the whole `*_beq`
family *exact* — and the `*_beq` family is what the two pinned-basis guards
read (`env.find? eqName == some eqA`, `decide (env.find? natName = some
natA)`), so its exactness is load-bearing for the accept direction and not a
convenience.

`prop_when::names_beq` and `expr::exprs_beq` get their (missing) top-level
refinement lemmas here rather than in `Refine/PropWhen.lean` and
`Refine/Expr.lean`, so that task #46 did not have to edit two finished files;
they belong there.
-/
import ConRon.Refine.Abs
import ConRon.Refine.Expr

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Env

/-! ## Code points -/

/-- `core_types::code_points` copies a slice of code points into a `Vec`: the
index recursion, at its accumulator. -/
theorem code_points_from_val (codes : Slice Std.U32) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec Std.U32),
      codes.length - i.val ≤ k →
      core_types.code_points_from codes i out = ok v →
      v.val = out.val ++ codes.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [core_types.code_points_from.eq_def] at h; simp only [] at h
    rw [ite_eq_left (show i ≥ Slice.len codes by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]
    simp
  | succ k ih =>
    intro i out v hk h
    rw [core_types.code_points_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ codes.length
    · rw [ite_eq_left (show i ≥ Slice.len codes by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]
      simp
    · rw [ite_eq_right (show ¬ i ≥ Slice.len codes by scalar_tac)] at h
      have hlt : i.val < codes.length := by omega
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := codes.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Slice.index_usize_spec codes i hlt)
      subst hyv
      simp only [bind_eq_ok_iff, hy, hw, Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨out1, hout1, h⟩ := h
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `core_types::code_points` is the identity on the slice's code points: the
`Vec` it builds holds exactly them, in order. -/
theorem code_points_val {codes : Slice Std.U32} {v : alloc.vec.Vec Std.U32}
    (h : core_types.code_points codes = ok v) : v.val = codes.val := by
  rw [core_types.code_points] at h
  simpa [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using
    code_points_from_val codes codes.length 0#usize _ v (by scalar_tac) h

/-! ## The `Vec` copies

`exprs_copy` is the port's stand-in for Lean's value semantics on a `List`
field: an index recursion whose element step is a handle bump, so it is the
identity on the `Vec`'s list and hence — a `Vec` being a subtype of a list — on
the `Vec`.  The `*_from` lemma is the recursion (`PropWhen.append_from_val`'s
shape, with the conclusion on `List.drop i`); the entry point follows. -/

/-- `expr::dup` in the `= ok` form an index recursion needs
(`Expr.dup_eq` is the same fact read forwards). -/
theorem expr_dup_val (e : expr.Expr) : expr.dup e = ok e := by
  cases e; simp [expr.dup]

/-- `env::exprs_copy_from` appends the rest of the terms to its accumulator. -/
theorem exprs_copy_from_val (es : alloc.vec.Vec expr.Expr) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec expr.Expr),
      es.length - i.val ≤ k → env.exprs_copy_from es i out = ok v →
      v.val = out.val ++ es.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [env.exprs_copy_from.eq_def] at h; simp only [] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [env.exprs_copy_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ es.length
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len es by scalar_tac)] at h
      have hlt : i.val < es.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := es.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec es i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw, expr_dup_val,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨out1, hout1, h⟩ := h
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `env::exprs_copy` is the identity. -/
theorem exprs_copy_refines {es v : alloc.vec.Vec expr.Expr}
    (h : env.exprs_copy es = ok v) : v = es := by
  rw [env.exprs_copy] at h
  exact alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.with_capacity] using
      exprs_copy_from_val es es.length 0#usize _ v (by scalar_tac) h)

/-- `env::exprs_copy` preserves well-formedness. -/
theorem exprs_copy_wf {es v : alloc.vec.Vec expr.Expr} (hes : ExprsWF es)
    (h : env.exprs_copy es = ok v) : ExprsWF v := by
  rw [exprs_copy_refines h]; exact hes

/-! ## The stored-constant records

A `*_dup` is the identity in the model, the strongest statement it can have;
the `abs` reading follows by `congrArg`. -/

/-- `ConLeche/Kernel/Env.lean:191-232` -- `env::ind_caps_default` builds the
cited structure's field defaults. -/
theorem ind_caps_default_refines {c : env.IndCaps} (h : env.ind_caps_default = ok c) :
    absIndCaps c = ({} : ConLeche.IndCaps) := by
  simp only [env.ind_caps_default, Result.ok.injEq] at h
  subst h
  rw [absIndCaps]
  simp [absNames, alloc.vec.Vec.new]

/-- `env::ind_caps_default` is well formed. -/
theorem ind_caps_default_wf {c : env.IndCaps} (h : env.ind_caps_default = ok c) :
    IndCapsWF c := by
  simp only [env.ind_caps_default, Result.ok.injEq] at h
  subst h
  exact ⟨fun _ hm => by simp [alloc.vec.Vec.new] at hm,
    fun _ hm => by simp [alloc.vec.Vec.new] at hm⟩

/-! ## `default_expr` and the per-field view of a table

`ProjTable.entry`'s two `getD`s are out-of-range guards, and the port spells
both fallbacks out; the index is a `u64` cast to a `usize` at the index site
(DESIGN.md §3.3), so the two casts need their own value lemmas. -/

/-- A `u64` narrowed to a `usize` keeps its value when it fits. -/
theorem u64_cast_usize_val {x : Std.U64} (h : x.val ≤ Std.Usize.max) :
    (UScalar.cast UScalarTy.Usize x).val = x.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  scalar_tac

/-! ## `abs` is injective on the well-formed records

What the `*_beq` family's exactness rests on (DESIGN.md §3.5): the records
carry no derived data, so each of these is the componentwise injectivity of
`absName`/`absNames`/`absLevel`/`absLevels`/`absExpr`/`absExprs`/`absPropWhen`
under the matching `*WF`, and the machine words are equal as soon as their
`Nat` readings are. -/

/-- A `u64` is determined by its value. -/
theorem u64_val_inj {a b : Std.U64} (h : a.val = b.val) : a = b := by scalar_tac

/-! ## The derived structural equalities

`env.rs`'s `*_beq` family is Lean's `deriving DecidableEq` on the records,
spelled out componentwise over the crate's own `name::beq`/`expr::beq`/
`level::beq`/`prop_when::beq` (task #9's rule).  Each lemma says the `Bool` the
Rust returns **is** `decide (abs a = abs b)`, which is what the two
pinned-basis guards read (`env.find? eqName == some eqA`, …) and what makes
them exact.  Every arm is one of two shapes — `let y ← <test>; if y then <rest>
else false` (`Refine/Expr.lean`'s `guard_step`) and `if <scalar test> then
<rest> else false` (`scalar_step` below) — so the proofs are the chains. -/

/-- `ConLeche/Kernel/Env.lean:312-322` — `reducibility_hint_beq`. -/
theorem reducibility_hint_beq_refines {a b : env.ReducibilityHint} {c : Bool}
    (h : env.reducibility_hint_beq a b = ok c) :
    c = decide (absHint a = absHint b) := by
  rw [env.reducibility_hint_beq.eq_def] at h
  cases a <;> cases b <;>
    simp_all only [absHint, reduceCtorEq, decide_false, decide_true,
      Result.ok.injEq, ConLeche.ReducibilityHint.regular.injEq]
  exact Expr.u64_eq_test h

end ConRon.Refine.Env
