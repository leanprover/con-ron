/-
`ConRon.Refine.Env` — the refinement of `crates/con-ron-core/src/kernel/env.rs`
against `ConLeche/Kernel/Env.lean` (task #46, `Refine/CORE_PLAN.md` step 1).

One lemma per ported function, in `env.rs`'s own order, in DESIGN.md §3.5's
shape: forward from `f x = ok y`, the conclusion an *exact* equality against the
cited con-leche definition, well-formedness hypotheses only where the stored
derived data has to be pinned.  The abstraction functions
(`absConstantVal`, …, `absEnv`, `absMode`) and the hereditary `*WF` predicates
(`ConstantValWF`, …, `EnvWF`) live in `ConRon/Refine/Abs.lean`.

Three groups carry real content and the rest are mechanical:

* **the reserved names** — `proj_fn_name`/`proj_table_name` are the port's only
  string *literals* below the basis, and the refinement has to read them:
  `core_types::code_points` of `env::PROJ_STR` really is `"proj"`, and every one
  of its code points is a `Char` (`StrWF`, without which `absString` is not
  injective);
* **`abs` is injective on the well-formed records**, which is what makes the
  whole `*_beq` family *exact* — and the `*_beq` family is what the two
  pinned-basis guards read (`env.find? eqName == some eqA`,
  `decide (env.find? natName = some natA)`), so its exactness is load-bearing
  for the accept direction and not a convenience;
* **`find`/`find_proj`** — the linear search over `Env.consts` in its
  newest-first order, `= Env.find?`/`Env.findProj?` on the nose, plus the fact
  a lookup hands its caller a well-formed record (`find_wf`), which is what the
  knot's induction consumes.

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

/-! ## The reserved names -/

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
    rw [if_pos (show i ≥ Slice.len codes by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]
    simp
  | succ k ih =>
    intro i out v hk h
    rw [core_types.code_points_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ codes.length
    · rw [if_pos (show i ≥ Slice.len codes by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]
      simp
    · rw [if_neg (show ¬ i ≥ Slice.len codes by scalar_tac)] at h
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

/-- The `"proj"` literal: `env::PROJ_STR`'s code points really do abstract to
the Lean string `projFnName` appends, and every one of them is a `Char`. -/
theorem proj_str_abs {v : alloc.vec.Vec Std.U32}
    (h : core_types.code_points (Array.to_slice env.PROJ_STR) = ok v) :
    absString v = "proj" ∧ StrWF v := by
  have hv : v.val = [112#u32, 114#u32, 111#u32, 106#u32] := by
    rw [code_points_val h, Array.val_to_slice, env.PROJ_STR, Array.make_val]
  refine ⟨?_, ?_⟩
  · rw [absString, hv]; rfl
  · intro c hc; rw [hv] at hc; fin_cases hc <;> decide

/-- The `"projTable"` literal (see `proj_str_abs`). -/
theorem proj_table_str_abs {v : alloc.vec.Vec Std.U32}
    (h : core_types.code_points (Array.to_slice env.PROJ_TABLE_STR) = ok v) :
    absString v = "projTable" ∧ StrWF v := by
  have hv : v.val = [112#u32, 114#u32, 111#u32, 106#u32, 84#u32, 97#u32,
      98#u32, 108#u32, 101#u32] := by
    rw [code_points_val h, Array.val_to_slice, env.PROJ_TABLE_STR, Array.make_val]
  refine ⟨?_, ?_⟩
  · rw [absString, hv]; rfl
  · intro c hc; rw [hv] at hc; fin_cases hc <;> decide

/-- `ConLeche/Kernel/Env.lean:596` — `env::proj_fn_name` refines `projFnName`:
the public projection-function name `(T.str "proj").num i`. -/
theorem proj_fn_name_refines {t r : name.Name} {i : Std.U64}
    (h : env.proj_fn_name t i = ok r) :
    absName r = ConLeche.projFnName (absName t) i.val := by
  rw [env.proj_fn_name] at h
  simp only [name_dup_eq, lift_eq, bind_eq_ok_iff, Result.ok.injEq,
    exists_eq_left'] at h
  obtain ⟨v, hv, n1, hn1, h⟩ := h
  rw [ConLeche.projFnName, Name.mk_num_refines h, Name.mk_str_refines hn1,
    (proj_str_abs hv).1]

/-- `env::proj_fn_name` builds a well-formed name. -/
theorem proj_fn_name_wf {t r : name.Name} {i : Std.U64} (ht : NameWF t)
    (h : env.proj_fn_name t i = ok r) : NameWF r := by
  rw [env.proj_fn_name] at h
  simp only [name_dup_eq, lift_eq, bind_eq_ok_iff, Result.ok.injEq,
    exists_eq_left'] at h
  obtain ⟨v, hv, n1, hn1, h⟩ := h
  exact Name.mk_num_wf (Name.mk_str_wf ht (proj_str_abs hv).2 hn1) h

/-- `ConLeche/Kernel/Env.lean:602` — `env::proj_table_name` refines
`projTableName`: `(T.str "projTable").num 0`. -/
theorem proj_table_name_refines {t r : name.Name}
    (h : env.proj_table_name t = ok r) :
    absName r = ConLeche.projTableName (absName t) := by
  rw [env.proj_table_name] at h
  simp only [name_dup_eq, lift_eq, bind_eq_ok_iff, Result.ok.injEq,
    exists_eq_left'] at h
  obtain ⟨v, hv, n1, hn1, h⟩ := h
  rw [ConLeche.projTableName, Name.mk_num_refines h, Name.mk_str_refines hn1,
    (proj_table_str_abs hv).1]
  rfl

/-- `env::proj_table_name` builds a well-formed name. -/
theorem proj_table_name_wf {t r : name.Name} (ht : NameWF t)
    (h : env.proj_table_name t = ok r) : NameWF r := by
  rw [env.proj_table_name] at h
  simp only [name_dup_eq, lift_eq, bind_eq_ok_iff, Result.ok.injEq,
    exists_eq_left'] at h
  obtain ⟨v, hv, n1, hn1, h⟩ := h
  exact Name.mk_num_wf (Name.mk_str_wf ht (proj_table_str_abs hv).2 hn1) h

/-! ## The check mode

`ConLeche.CheckMode`'s six accessors are constant functions of the
constructor, so each refinement is one `simp` per mode. -/

/-- `ConLeche/Kernel/Env.lean:69-72` -- `env::check_mode_dup` is the identity on
a two-constructor enum, which is the strongest form its refinement takes. -/
theorem check_mode_dup_refines {m m' : env.CheckMode}
    (h : env.check_mode_dup m = ok m') : m' = m := by
  cases m <;> simp only [env.check_mode_dup, Result.ok.injEq] at h <;> exact h.symm

/-- `ConLeche/Kernel/Env.lean:80-81` -- `env::tt_checks` refines
`CheckMode.ttChecks`, constantly `false` at both modes. -/
theorem tt_checks_refines {m : env.CheckMode} {b : Bool}
    (h : env.tt_checks m = ok b) : b = (absMode m).ttChecks := by
  cases m <;> (simp only [env.tt_checks, Result.ok.injEq] at h; rw [← h]; rfl)

/-- `ConLeche/Kernel/Env.lean:92-94` -- `env::verified_checks` refines
`CheckMode.verifiedChecks`, the λ-codomain check's gate. -/
theorem verified_checks_refines {m : env.CheckMode} {b : Bool}
    (h : env.verified_checks m = ok b) : b = (absMode m).verifiedChecks := by
  cases m <;> (simp only [env.verified_checks, Result.ok.injEq] at h; rw [← h]; rfl)

/-- `ConLeche/Kernel/Env.lean:119-121` -- `env::beta_gate` refines
`CheckMode.betaGate`. -/
theorem beta_gate_refines {m : env.CheckMode} {b : Bool}
    (h : env.beta_gate m = ok b) : b = (absMode m).betaGate := by
  cases m <;> (simp only [env.beta_gate, Result.ok.injEq] at h; rw [← h]; rfl)

/-- `ConLeche/Kernel/Env.lean:141-142` -- `env::io_gate` refines
`CheckMode.ioGate`, constantly `true`. -/
theorem io_gate_refines {m : env.CheckMode} {b : Bool}
    (h : env.io_gate m = ok b) : b = (absMode m).ioGate := by
  cases m <;> (simp only [env.io_gate, Result.ok.injEq] at h; rw [← h]; rfl)

/-- `ConLeche/Kernel/Env.lean:173-175` -- `env::certs` refines
`CheckMode.certs`, the certificate-family switch. -/
theorem certs_refines {m : env.CheckMode} {b : Bool}
    (h : env.certs m = ok b) : b = (absMode m).certs := by
  cases m <;> (simp only [env.certs, Result.ok.injEq] at h; rw [← h]; rfl)

/-- `ConLeche/Kernel/Env.lean:184-185` -- `env::beta_skip` refines
`CheckMode.betaSkip`.  No `PropWhenWF` is needed: `prop_when::is_never` reads
the sealed representation's tag alone (`PropWhen.is_never_refines`). -/
theorem beta_skip_refines {m : env.CheckMode} {pw : prop_when.PropWhen} {b : Bool}
    (h : env.beta_skip m pw = ok b) : b = (absMode m).betaSkip (absPropWhen pw) := by
  cases m
  · simp only [env.beta_skip, env.certs, env.beta_gate, bind_tc_ok, reduceIte] at h
    rw [PropWhen.is_never_refines h]; rfl
  · simp only [env.beta_skip, env.certs, bind_tc_ok, Bool.false_eq_true, if_false,
      Result.ok.injEq] at h
    rw [← h]; rfl

/-- `ConLeche/Kernel/Env.lean:193-194` -- `env::io_skip` refines
`CheckMode.ioSkip`.  As for `beta_skip`, no well-formedness is needed. -/
theorem io_skip_refines {m : env.CheckMode} {pw : prop_when.PropWhen} {b : Bool}
    (h : env.io_skip m pw = ok b) : b = (absMode m).ioSkip (absPropWhen pw) := by
  cases m
  · simp only [env.io_skip, env.certs, bind_tc_ok, reduceIte] at h
    rw [PropWhen.is_never_refines h]; rfl
  · simp only [env.io_skip, env.certs, bind_tc_ok, Bool.false_eq_true, if_false,
      Result.ok.injEq] at h
    rw [← h]; rfl

/-! ## The `Vec` copies

`levels_copy`, `exprs_copy`, `rec_rules_copy` and `constant_infos_copy` are the
port's stand-ins for Lean's value semantics on a `List`/`Array` field; each is
an index recursion whose element step is a handle bump, so each is the identity
on the `Vec`'s list and hence — a `Vec` being a subtype of a list — on the
`Vec`.  The `*_from` lemmas are the recursion (`PropWhen.append_from_val`'s
shape, with the conclusion on `List.drop i`); the entry points follow. -/

/-- `expr::dup` in the `= ok` form an index recursion needs
(`Expr.dup_eq` is the same fact read forwards). -/
theorem expr_dup_val (e : expr.Expr) : expr.dup e = ok e := by
  cases e; simp [expr.dup]

/-- `env::levels_copy_from` appends the rest of the levels to its accumulator. -/
theorem levels_copy_from_val (us : alloc.vec.Vec level.Level) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec level.Level),
      us.length - i.val ≤ k → env.levels_copy_from us i out = ok v →
      v.val = out.val ++ us.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [env.levels_copy_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len us by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [env.levels_copy_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ us.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len us by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len us by scalar_tac)] at h
      have hlt : i.val < us.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := us.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec us i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw, level_dup_eq,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨out1, hout1, h⟩ := h
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `env::levels_copy_from` at its own statement, for `i` inside the vector. -/
theorem levels_copy_from_refines {us out v : alloc.vec.Vec level.Level}
    {i : Std.Usize} (h : env.levels_copy_from us i out = ok v) :
    v.val = out.val ++ us.val.drop i.val :=
  levels_copy_from_val us us.length i out v (by scalar_tac) h

/-- `env::levels_copy` is the identity: the copy is the very same `Vec`. -/
theorem levels_copy_refines {us v : alloc.vec.Vec level.Level}
    (h : env.levels_copy us = ok v) : v = us := by
  rw [env.levels_copy] at h
  exact alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.with_capacity] using
      levels_copy_from_val us us.length 0#usize _ v (by scalar_tac) h)

/-- `env::levels_copy` preserves well-formedness — trivially, being the
identity. -/
theorem levels_copy_wf {us v : alloc.vec.Vec level.Level} (hus : LevelsWF us)
    (h : env.levels_copy us = ok v) : LevelsWF v := by
  rw [levels_copy_refines h]; exact hus

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
    rw [if_pos (show i ≥ alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [env.exprs_copy_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ es.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len es by scalar_tac)] at h
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

/-- `env::exprs_copy_from` at its own statement. -/
theorem exprs_copy_from_refines {es out v : alloc.vec.Vec expr.Expr}
    {i : Std.Usize} (h : env.exprs_copy_from es i out = ok v) :
    v.val = out.val ++ es.val.drop i.val :=
  exprs_copy_from_val es es.length i out v (by scalar_tac) h

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

Every `*_dup` is the identity in the model: a `Name`/`Expr`/`PropWhen` copy is
an `Arc::clone` (DESIGN.md §3.2) and a `Vec` copy is the `Vec` (above).  The
identity is the strongest statement each can have, and the `abs` reading of
each follows by `congrArg`. -/

/-- `ConLeche/Kernel/Env.lean:197-201` -- `env::constant_val_dup` is the
identity on the record. -/
theorem constant_val_dup_refines {cv cv' : env.ConstantVal}
    (h : env.constant_val_dup cv = ok cv') : cv' = cv := by
  simp only [env.constant_val_dup, bind_eq_ok_iff, name_dup_eq, expr_dup_val,
    Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨v, hv, rfl⟩ := h
  rw [alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv)]

/-- `ConLeche/Kernel/Env.lean:243-247` -- `env::rec_rule_fire_dup` is the
identity. -/
theorem rec_rule_fire_dup_refines {f f' : env.RecRuleFire}
    (h : env.rec_rule_fire_dup f = ok f') : f' = f := by
  cases f with
  | Inert => simp only [env.rec_rule_fire_dup, Result.ok.injEq] at h; exact h.symm
  | Plain => simp only [env.rec_rule_fire_dup, Result.ok.injEq] at h; exact h.symm
  | Nested lvls pins =>
    simp only [env.rec_rule_fire_dup, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨us, hus, es, hes, rfl⟩ := h
    rw [levels_copy_refines hus, exprs_copy_refines hes]

/-- `ConLeche/Kernel/Env.lean:259-292` -- `env::rec_rule_dup` is the
identity. -/
theorem rec_rule_dup_refines {r r' : env.RecRule}
    (h : env.rec_rule_dup r = ok r') : r' = r := by
  simp only [env.rec_rule_dup, bind_eq_ok_iff, name_dup_eq, expr_dup_val,
    Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨f, hf, rfl⟩ := h
  rw [rec_rule_fire_dup_refines hf]

/-- `ConLeche/Kernel/Env.lean:259-292` -- `env::rec_rule_parsed` builds the
cited structure at its *field defaults*: `ctorParams := 0`, `fire := .inert`,
`k := eta := paramsBlind := false`. -/
theorem rec_rule_parsed_refines {ctor : name.Name} {nfields : Std.U64}
    {rhs : expr.Expr} {r : env.RecRule}
    (h : env.rec_rule_parsed ctor nfields rhs = ok r) :
    absRecRule r =
      ⟨absName ctor, nfields.val, 0, .inert, absExpr rhs, false, false, false⟩ := by
  simp only [env.rec_rule_parsed, Result.ok.injEq] at h
  rw [← h]; rfl

/-- `env::rec_rule_parsed` is well formed as soon as its two term arguments
are. -/
theorem rec_rule_parsed_wf {ctor : name.Name} {nfields : Std.U64}
    {rhs : expr.Expr} {r : env.RecRule} (hc : NameWF ctor) (hr : ExprWF rhs)
    (h : env.rec_rule_parsed ctor nfields rhs = ok r) : RecRuleWF r := by
  simp only [env.rec_rule_parsed, Result.ok.injEq] at h
  rw [← h]; exact ⟨hc, trivial, hr⟩

/-- `ConLeche/Kernel/Env.lean:298-301` -- `env::rec_rule_compare_params`
refines `RecRule.compareParams`. -/
theorem rec_rule_compare_params_refines {rl : env.RecRule} {b : Bool}
    (h : env.rec_rule_compare_params rl = ok b) :
    b = (absRecRule rl).compareParams := by
  rw [env.rec_rule_compare_params] at h
  rw [ConLeche.RecRule.compareParams, absRecRule]
  cases hf : rl.fire <;> rw [hf] at h <;>
    simp only [Result.ok.injEq] at h <;> simp [← h, absFire]

/-- `ConLeche/Kernel/Env.lean:318-322` -- `env::reducibility_hint_dup` is the
identity. -/
theorem reducibility_hint_dup_refines {h1 h2 : env.ReducibilityHint}
    (h : env.reducibility_hint_dup h1 = ok h2) : h2 = h1 := by
  cases h1 <;> simp only [env.reducibility_hint_dup, Result.ok.injEq] at h <;>
    exact h.symm

/-- `ConLeche/Kernel/Env.lean:329-334` -- `env::reducibility_hint_lt` refines
`ReducibilityHint.lt`.  The cited arms overlap, so the port matches on `h₂`
first and the check is a nine-case one. -/
theorem reducibility_hint_lt_refines {h1 h2 : env.ReducibilityHint} {b : Bool}
    (h : env.reducibility_hint_lt h1 h2 = ok b) :
    b = ConLeche.ReducibilityHint.lt (absHint h1) (absHint h2) := by
  cases h2 <;> cases h1 <;>
    simp_all [env.reducibility_hint_lt, ConLeche.ReducibilityHint.lt, absHint]

/-- A `u64`'s equality is its value's: the abstraction casts a stored word to a
`Nat`, so con-leche's `==` on the cast is the port's own comparison. -/
theorem u64_decide_eq_val (a b : Std.U64) :
    ((a.val : Nat) == b.val) = decide (a = b) := by
  by_cases hab : a = b
  · subst hab; simp
  · simp only [hab, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro hv; exact hab (by scalar_tac)

/-- `ConLeche/Kernel/Env.lean:344-346` -- `env::reducibility_hint_same_regular`
refines `ReducibilityHint.sameRegular`. -/
theorem reducibility_hint_same_regular_refines {h1 h2 : env.ReducibilityHint}
    {b : Bool} (h : env.reducibility_hint_same_regular h1 h2 = ok b) :
    b = ConLeche.ReducibilityHint.sameRegular (absHint h1) (absHint h2) := by
  cases h1 <;> cases h2 <;>
    simp_all [env.reducibility_hint_same_regular, ConLeche.ReducibilityHint.sameRegular,
      absHint, u64_decide_eq_val]

/-- `ConLeche/Kernel/Env.lean:352-354` -- `env::basis_kind_dup` is the
identity. -/
theorem basis_kind_dup_refines {k k' : env.BasisKind}
    (h : env.basis_kind_dup k = ok k') : k' = k := by
  cases k <;> simp only [env.basis_kind_dup, Result.ok.injEq] at h <;> exact h.symm

/-- `ConLeche/Kernel/Env.lean:362-384` -- `env::ind_caps_default` builds the
cited structure's field defaults, whose one non-obvious member is
`sortZ := .ifAllZero []`. -/
theorem ind_caps_default_refines {c : env.IndCaps} (h : env.ind_caps_default = ok c) :
    absIndCaps c = ({} : ConLeche.IndCaps) := by
  simp only [env.ind_caps_default, bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, pw, hpw, rfl⟩ := h
  rw [absIndCaps]
  simp only [Name.anonymous_refines hn,
    PropWhen.if_all_zero_refines (fun _ hm => by simp [alloc.vec.Vec.new] at hm) hpw,
    absNames]
  simp [alloc.vec.Vec.new]

/-- `env::ind_caps_default` is well formed. -/
theorem ind_caps_default_wf {c : env.IndCaps} (h : env.ind_caps_default = ok c) :
    IndCapsWF c := by
  simp only [env.ind_caps_default, bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, pw, hpw, rfl⟩ := h
  exact ⟨Name.anonymous_wf hn,
    PropWhen.if_all_zero_wf (fun _ hm => by simp [alloc.vec.Vec.new] at hm) hpw⟩

/-- `ConLeche/Kernel/Env.lean:362-384` -- `env::ind_caps_dup` is the
identity. -/
theorem ind_caps_dup_refines {c c' : env.IndCaps}
    (h : env.ind_caps_dup c = ok c') : c' = c := by
  simp only [env.ind_caps_dup, bind_eq_ok_iff, name_dup_eq, Result.ok.injEq,
    exists_eq_left'] at h
  obtain ⟨pw, hpw, rfl⟩ := h
  rw [PropWhen.dup_eq hpw]

/-- `ConLeche/Kernel/Env.lean:411-441` -- `env::proj_table_dup` is the
identity. -/
theorem proj_table_dup_refines {t t' : env.ProjTable}
    (h : env.proj_table_dup t = ok t') : t' = t := by
  simp only [env.proj_table_dup, bind_eq_ok_iff, name_dup_eq, level_dup_eq,
    Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨v, hv, es, hes, us, hus, rfl⟩ := h
  rw [alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv), exprs_copy_refines hes,
    levels_copy_refines hus]

/-! ## `default_expr` and the per-field view of a table

`ProjTable.entry`'s two `getD`s are out-of-range guards, and the port spells
both fallbacks out; the index is a `u64` cast to a `usize` at the index site
(DESIGN.md §3.3), so the two casts need their own value lemmas. -/

/-- A `usize` widened to a `u64` keeps its value (`Usize.numBits ≤ 64`). -/
theorem usize_cast_u64_val (x : Std.Usize) :
    (UScalar.cast UScalarTy.U64 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  show UScalarTy.Usize.numBits ≤ UScalarTy.U64.numBits
  simp only [UScalarTy.numBits]
  cases System.Platform.numBits_eq with
  | inl hp => omega
  | inr hp => omega

/-- A `u64` narrowed to a `usize` keeps its value when it fits. -/
theorem u64_cast_usize_val {x : Std.U64} (h : x.val ≤ Std.Usize.max) :
    (UScalar.cast UScalarTy.Usize x).val = x.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  scalar_tac

/-- `ConLeche/Kernel/Expr.lean:403` -- `env::default_expr` is `default : Expr`,
Lean's derived `Inhabited Expr` being the first constructor at its argument's
own default, `.bvar 0`. -/
theorem default_expr_refines {e : expr.Expr} (h : env.default_expr = ok e) :
    absExpr e = (default : ConLeche.Expr) := by
  rw [env.default_expr] at h
  rw [Expr.bvar_refines h]; rfl

/-- `env::default_expr` is well formed. -/
theorem default_expr_wf {e : expr.Expr} (h : env.default_expr = ok e) : ExprWF e := by
  rw [env.default_expr] at h; exact Expr.bvar_wf h

/-- `proj_table_entry`'s body slot: con-leche's `bodies.getD i default`, and
well formed when the table's bodies are. -/
theorem entry_body_slot {es : alloc.vec.Vec expr.Expr} {i : Std.U64} {y : expr.Expr}
    (hy : (if i < UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len es)
            then (do let e ← alloc.vec.Vec.index_usize es (UScalar.cast UScalarTy.Usize i)
                     ok e)
            else env.default_expr) = ok y) :
    absExpr y = (absExprs es).toArray.getD i.val default ∧ (ExprsWF es → ExprWF y) := by
  have hc := usize_cast_u64_val (alloc.vec.Vec.len es)
  by_cases hlt : i < UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len es)
  · rw [if_pos hlt, bind_eq_ok_iff] at hy
    have hi : i.val < es.val.length := by scalar_tac
    have hcu : (UScalar.cast UScalarTy.Usize i).val = i.val :=
      u64_cast_usize_val (by scalar_tac)
    obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec es (UScalar.cast UScalarTy.Usize i) (by scalar_tac))
    rw [hz] at hy
    simp only [Result.ok.injEq, exists_eq_left'] at hy
    subst hy
    exact ⟨by simp [absExprs, hzv, hcu, hi],
      fun hes => hes _ (by rw [hzv]; exact List.getElem_mem _)⟩
  · rw [if_neg hlt] at hy
    have hi : es.val.length ≤ i.val := by scalar_tac
    exact ⟨by rw [default_expr_refines hy]; simp [absExprs, hi],
      fun _ => default_expr_wf hy⟩

/-- `proj_table_entry`'s guard slot: con-leche's `guards.getD i .zero`, and well
formed when the table's guards are. -/
theorem entry_guard_slot {us : alloc.vec.Vec level.Level} {i : Std.U64}
    {y : level.Level}
    (hy : (if i < UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len us)
            then (do let l ← alloc.vec.Vec.index_usize us (UScalar.cast UScalarTy.Usize i)
                     ok l)
            else level.zero) = ok y) :
    absLevel y = (absLevels us).getD i.val ConLeche.Level.zero ∧
      (LevelsWF us → LevelWF y) := by
  have hc := usize_cast_u64_val (alloc.vec.Vec.len us)
  by_cases hlt : i < UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len us)
  · rw [if_pos hlt, bind_eq_ok_iff] at hy
    have hi : i.val < us.val.length := by scalar_tac
    have hcu : (UScalar.cast UScalarTy.Usize i).val = i.val :=
      u64_cast_usize_val (by scalar_tac)
    obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec us (UScalar.cast UScalarTy.Usize i) (by scalar_tac))
    rw [hz] at hy
    simp only [Result.ok.injEq, exists_eq_left'] at hy
    subst hy
    exact ⟨by simp [absLevels, hzv, hcu, hi],
      fun hus => hus _ (by rw [hzv]; exact List.getElem_mem _)⟩
  · rw [if_neg hlt] at hy
    have hi : us.val.length ≤ i.val := by scalar_tac
    exact ⟨by rw [Level.zero_refines hy]; simp [absLevels, hi],
      fun _ => Level.zero_wf hy⟩

/-- `ConLeche/Kernel/Env.lean:466-468` -- `env::proj_table_entry` refines
`ProjTable.entry`, both `getD` fallbacks included. -/
theorem proj_table_entry_refines {tbl : env.ProjTable} {i : Std.U64}
    {e : env.ProjEntry} (h : env.proj_table_entry tbl i = ok e) :
    absProjEntry e = (absProjTable tbl).entry i.val := by
  rw [env.proj_table_entry] at h
  simp only [lift_eq, alloc.vec.Vec.index_slice_index, bind_tc_ok, bind_eq_ok_iff,
    name_dup_eq, level_dup_eq, expr_dup_val, Result.ok.injEq] at h
  obtain ⟨y, hy, y1, hy1, y2, hy2, rfl⟩ := h
  rw [absProjEntry, alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hy2)]
  simp only [ConLeche.ProjTable.entry, absProjTable, (entry_body_slot hy).1,
    (entry_guard_slot hy1).1]

/-- `env::proj_table_entry`'s view is well formed when the table is. -/
theorem proj_table_entry_wf {tbl : env.ProjTable} {i : Std.U64}
    {e : env.ProjEntry} (ht : ProjTableWF tbl)
    (h : env.proj_table_entry tbl i = ok e) : ProjEntryWF e := by
  obtain ⟨hn, hlp, hc, hss, hb, hg⟩ := ht
  rw [env.proj_table_entry] at h
  simp only [lift_eq, alloc.vec.Vec.index_slice_index, bind_tc_ok, bind_eq_ok_iff,
    name_dup_eq, level_dup_eq, expr_dup_val, Result.ok.injEq] at h
  obtain ⟨y, hy, y1, hy1, y2, hy2, rfl⟩ := h
  refine ⟨hn, ?_, hc, (entry_body_slot hy).2 hb, (entry_guard_slot hy1).2 hg, hss⟩
  rw [alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hy2)]; exact hlp


/-! ## `RecRule` and `ConstantInfo` copies

`env::constant_info_share` and `env::constant_info_rc_dup` are `ron::ptr`
calls, hence the identity in the model (DESIGN.md §3.2); their `= ok` readings
are what the two `ConstantInfo` loops below need, so they come first. -/

/-- `env::constant_info_share` is the identity: `ron::ptr::new` is. -/
theorem constant_info_share_val (c : env.ConstantInfo) :
    env.constant_info_share c = ok c := by simp [env.constant_info_share]

/-- `env::constant_info_rc_dup` is the identity: `ron::ptr::clone` is. -/
theorem constant_info_rc_dup_val (c : env.ConstantInfo) :
    env.constant_info_rc_dup c = ok c := by simp [env.constant_info_rc_dup]

/-- `env::rec_rules_copy_from` appends the rest of the rules to its
accumulator. -/
theorem rec_rules_copy_from_val (rs : alloc.vec.Vec env.RecRule) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec env.RecRule),
      rs.length - i.val ≤ k → env.rec_rules_copy_from rs i out = ok v →
      v.val = out.val ++ rs.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [env.rec_rules_copy_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [env.rec_rules_copy_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ rs.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac)] at h
      have hlt : i.val < rs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := rs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨r1, hr1, out1, hout1, h⟩ := h
      rw [rec_rule_dup_refines hr1] at hout1
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `env::rec_rules_copy_from` at its own statement. -/
theorem rec_rules_copy_from_refines {rs out v : alloc.vec.Vec env.RecRule}
    {i : Std.Usize} (h : env.rec_rules_copy_from rs i out = ok v) :
    v.val = out.val ++ rs.val.drop i.val :=
  rec_rules_copy_from_val rs rs.length i out v (by scalar_tac) h

/-- `env::rec_rules_copy` is the identity. -/
theorem rec_rules_copy_refines {rs v : alloc.vec.Vec env.RecRule}
    (h : env.rec_rules_copy rs = ok v) : v = rs := by
  rw [env.rec_rules_copy] at h
  exact alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.with_capacity] using
      rec_rules_copy_from_val rs rs.length 0#usize _ v (by scalar_tac) h)

/-- `ConLeche/Kernel/Env.lean:471-496` -- `env::constant_info_dup` is the
identity on a stored constant. -/
theorem constant_info_dup_refines {c c' : env.ConstantInfo}
    (h : env.constant_info_dup c = ok c') : c' = c := by
  cases c with
  | AxiomInfo v =>
    simp only [env.constant_info_dup, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    rw [constant_val_dup_refines hcv]
  | DefnInfo v value hint =>
    simp only [env.constant_info_dup, bind_eq_ok_iff, expr_dup_val, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨cv, hcv, hint', hhint, rfl⟩ := h
    rw [constant_val_dup_refines hcv, reducibility_hint_dup_refines hhint]
  | ThmInfo v value =>
    simp only [env.constant_info_dup, bind_eq_ok_iff, expr_dup_val, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    rw [constant_val_dup_refines hcv]
  | IndInfo v caps =>
    simp only [env.constant_info_dup, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv, hcv, ic, hic, rfl⟩ := h
    rw [constant_val_dup_refines hcv, ind_caps_dup_refines hic]
  | CtorInfo v np nf =>
    simp only [env.constant_info_dup, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    rw [constant_val_dup_refines hcv]
  | RecInfo v mi rp rules =>
    simp only [env.constant_info_dup, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv, hcv, rs, hrs, rfl⟩ := h
    rw [constant_val_dup_refines hcv, rec_rules_copy_refines hrs]
  | ProjInfo tbl =>
    simp only [env.constant_info_dup, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨t, ht, rfl⟩ := h
    rw [proj_table_dup_refines ht]

/-- `env::constant_infos_copy_from` appends the rest of the stored constants to
its accumulator. -/
theorem constant_infos_copy_from_val (cs : alloc.vec.Vec env.ConstantInfo) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec env.ConstantInfo),
      cs.length - i.val ≤ k → env.constant_infos_copy_from cs i out = ok v →
      v.val = out.val ++ cs.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [env.constant_infos_copy_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [env.constant_infos_copy_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ cs.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      have hlt : i.val < cs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := cs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        constant_info_rc_dup_val, Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨out1, hout1, h⟩ := h
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `env::constant_infos_copy_from` at its own statement. -/
theorem constant_infos_copy_from_refines {cs out v : alloc.vec.Vec env.ConstantInfo}
    {i : Std.Usize} (h : env.constant_infos_copy_from cs i out = ok v) :
    v.val = out.val ++ cs.val.drop i.val :=
  constant_infos_copy_from_val cs cs.length i out v (by scalar_tac) h

/-- `env::constant_infos_copy` is the identity. -/
theorem constant_infos_copy_refines {cs v : alloc.vec.Vec env.ConstantInfo}
    (h : env.constant_infos_copy cs = ok v) : v = cs := by
  rw [env.constant_infos_copy] at h
  exact alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.with_capacity] using
      constant_infos_copy_from_val cs cs.length 0#usize _ v (by scalar_tac) h)

/-! ## The presented declarations -/

/-- `ConLeche/Kernel/Env.lean:533-535` -- `env::declaration_name` refines
`Declaration.name`. -/
theorem declaration_name_refines {d : env.Declaration} {n : name.Name}
    (h : env.declaration_name d = ok n) :
    absName n = ConLeche.Declaration.name (absDeclaration d) := by
  cases d with
  | AxiomDecl v =>
    simp only [env.declaration_name, name_dup_eq, Result.ok.injEq] at h
    rw [← h]; rfl
  | DefnDecl v value hint =>
    simp only [env.declaration_name, name_dup_eq, Result.ok.injEq] at h
    rw [← h]; rfl
  | ThmDecl v value =>
    simp only [env.declaration_name, name_dup_eq, Result.ok.injEq] at h
    rw [← h]; rfl
  | OpaqueDecl v value =>
    simp only [env.declaration_name, name_dup_eq, Result.ok.injEq] at h
    rw [← h]; rfl
  | BasisDecl k =>
    rw [env.declaration_name] at h
    rw [Name.anonymous_refines h]; rfl
  | IndDecl block nP =>
    rw [env.declaration_name] at h
    rw [Name.anonymous_refines h]; rfl


/-! ## The declared-parameter-count check

`pi_sort_tele_len` is the one *real* induction of this file: Aeneas's
`partial_fixpoint` definitions carry no recursor, so the recursion has to be
carried by the argument, and the argument's induction principle here is the
`ExprWF` derivation (task #5's shape).  The ten kinds' inversion lemmas are
`ConRon/Refine/Expr.lean`'s `bvar_inv`, `forall_e_inv`, … -/

/-- `ConLeche/Kernel/Env.lean:550-553` -- `env::pi_sort_tele_len` refines
`Expr.piSortTeleLen?`.  §3.3: the port's `n + 1` is checked `u64` arithmetic, so
an overflow is a Rust failure, which the forward shape covers. -/
theorem pi_sort_tele_len_refines {e : expr.Expr} (hwf : ExprWF e) :
    ∀ {o : Option Std.U64}, env.pi_sort_tele_len e = ok o →
      o.map Std.UScalar.val = ConLeche.Expr.piSortTeleLen? (absExpr e) := by
  induction hwf with
  | bvar hb =>
    intro o h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv hb
    rw [env.pi_sort_tele_len.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.piSortTeleLen?]
  | fvar hty hf _ihty =>
    intro o h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv hf
    rw [env.pi_sort_tele_len.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.piSortTeleLen?]
  | sort hu hs =>
    intro o h
    obtain ⟨d, -, -, rfl, -, -, -⟩ := Expr.sort_inv hs
    rw [env.pi_sort_tele_len.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.piSortTeleLen?]
  | mk_const hn hus hc =>
    intro o h
    obtain ⟨d, -, -, rfl, -, -, -⟩ := Expr.mk_const_inv hc
    rw [env.pi_sort_tele_len.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.piSortTeleLen?]
  | app hf ha ha' _ihf _iha =>
    intro o h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv ha'
    rw [env.pi_sort_tele_len.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.piSortTeleLen?]
  | lam hty hb hm hl _ihty _ihb =>
    intro o h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv hl
    rw [env.pi_sort_tele_len.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.piSortTeleLen?]
  | forall_e hty hbo hm hfa _ihty ihbo =>
    intro o h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv hfa
    rw [env.pi_sort_tele_len.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_, bind_eq_ok_iff] at h
    obtain ⟨o', ho', h⟩ := h
    have ih := ihbo ho'
    cases o' with
    | none =>
      simp only [Result.ok.injEq] at h
      simp only [Option.map_none] at ih
      rw [← h]; simp [ConLeche.Expr.piSortTeleLen?, ← ih]
    | some n =>
      simp only [bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨i, hi, rfl⟩ := h
      simp only [Option.map_some] at ih
      have hiv : i.val = n.val + (1#u64).val := Nat.uadd_val hi
      simp [ConLeche.Expr.piSortTeleLen?, ← ih, hiv]
  | let_e hty hv hbo hle _ihty _ihv _ihbo =>
    intro o h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv hle
    rw [env.pi_sort_tele_len.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.piSortTeleLen?]
  | lit hl hli =>
    intro o h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv hli
    rw [env.pi_sort_tele_len.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.piSortTeleLen?]
  | proj hs hx hp _ihx =>
    intro o h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv hp
    rw [env.pi_sort_tele_len.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.piSortTeleLen?]

/-- The predicate con-leche's `indParamsOk` hands to `List.all`
(`ConLeche/Kernel/Env.lean:581-588`), named so that the port's
`ind_params_ok_one` -- which is exactly that predicate, spelled out -- has
something to refine. -/
def indParamsOkOne (nP : Nat) (ci : ConLeche.ConstantInfo) : Bool :=
  match ci with
  | .indInfo cvT _ =>
    match cvT.type.piSortTeleLen? with
    | some n => decide (nP ≤ n)
    | none => true
  | .ctorInfo _ nPc _ => nPc == nP
  | _ => true

/-- `indParamsOk` is the `List.all` of that predicate. -/
theorem indParamsOk_eq (nP : Nat) (block : List ConLeche.ConstantInfo) :
    ConLeche.indParamsOk nP block = block.all (indParamsOkOne nP) := rfl

/-- `ConLeche/Kernel/Env.lean:581-588` -- `env::ind_params_ok_one` refines the
cited `List.all`'s predicate at one member. -/
theorem ind_params_ok_one_refines {n_p : Std.U64} {ci : env.ConstantInfo} {b : Bool}
    (hci : ConstantInfoWF ci) (h : env.ind_params_ok_one n_p ci = ok b) :
    b = indParamsOkOne n_p.val (absConstantInfo ci) := by
  cases ci with
  | IndInfo cv caps =>
    obtain ⟨⟨-, -, hty⟩, -⟩ := hci
    simp only [env.ind_params_ok_one, bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    have ih := pi_sort_tele_len_refines hty ho
    cases o with
    | none =>
      simp only [Result.ok.injEq] at h
      simp only [Option.map_none] at ih
      rw [← h]
      simp [indParamsOkOne, absConstantInfo, absConstantVal, ← ih]
    | some n =>
      simp only [Result.ok.injEq] at h
      simp only [Option.map_some] at ih
      rw [← h]
      simp [indParamsOkOne, absConstantInfo, absConstantVal, ← ih]
  | CtorInfo cv np nf =>
    simp only [env.ind_params_ok_one, Result.ok.injEq] at h
    rw [← h]; simp [indParamsOkOne, absConstantInfo, u64_decide_eq_val]
  | AxiomInfo cv =>
    simp only [env.ind_params_ok_one, Result.ok.injEq] at h
    rw [← h]; rfl
  | DefnInfo cv v hint =>
    simp only [env.ind_params_ok_one, Result.ok.injEq] at h
    rw [← h]; rfl
  | ThmInfo cv v =>
    simp only [env.ind_params_ok_one, Result.ok.injEq] at h
    rw [← h]; rfl
  | RecInfo cv mi rp rs =>
    simp only [env.ind_params_ok_one, Result.ok.injEq] at h
    rw [← h]; rfl
  | ProjInfo tbl =>
    simp only [env.ind_params_ok_one, Result.ok.injEq] at h
    rw [← h]; rfl

/-- The abstracted block's tail at `i`, as a cons: the shape every index
recursion over `Env.consts`' order needs. -/
theorem absConstantInfos_drop_cons {cs : alloc.vec.Vec env.ConstantInfo} {i : Nat}
    (hlt : i < cs.val.length) :
    (absConstantInfos cs).drop i
      = absConstantInfo cs.val[i] :: (absConstantInfos cs).drop (i + 1) := by
  rw [absConstantInfos, ← List.map_drop, ← List.map_drop,
    List.drop_eq_getElem_cons hlt, List.map_cons]

/-- Past the end, the abstracted block's tail is empty. -/
theorem absConstantInfos_drop_nil {cs : alloc.vec.Vec env.ConstantInfo} {i : Nat}
    (hge : cs.val.length ≤ i) : (absConstantInfos cs).drop i = [] := by
  rw [absConstantInfos, ← List.map_drop, List.drop_eq_nil_of_le hge, List.map_nil]

/-- `ConLeche/Kernel/Env.lean:581-588` -- `env::ind_params_ok_from` is the cited
`List.all` over `block[i..]`. -/
theorem ind_params_ok_from_val {n_p : Std.U64} {block : alloc.vec.Vec env.ConstantInfo}
    (hwf : ConstantInfosWF block) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool),
      block.length - i.val ≤ k → env.ind_params_ok_from n_p block i = ok b →
      b = ((absConstantInfos block).drop i.val).all (indParamsOkOne n_p.val) := by
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [env.ind_params_ok_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
    rw [← h, absConstantInfos_drop_nil (by scalar_tac)]; rfl
  | succ k ih =>
    intro i b hk h
    rw [env.ind_params_ok_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ block.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
      rw [← h, absConstantInfos_drop_nil (by scalar_tac)]; rfl
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
      have hlt : i.val < block.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := block.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec block i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b1, hb1, h⟩ := h
      have hone := ind_params_ok_one_refines (hwf _ (List.getElem_mem hlt)) hb1
      rw [absConstantInfos_drop_cons hlt, List.all_cons, ← hone]
      cases b1 with
      | true =>
        simp only [reduceIte, bind_tc_ok] at h
        rw [ih w b (by scalar_tac) h, hwv]
        simp
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h]; simp

/-- `env::ind_params_ok_from` at its own statement. -/
theorem ind_params_ok_from_refines {n_p : Std.U64}
    {block : alloc.vec.Vec env.ConstantInfo} {i : Std.Usize} {b : Bool}
    (hwf : ConstantInfosWF block) (h : env.ind_params_ok_from n_p block i = ok b) :
    b = ((absConstantInfos block).drop i.val).all (indParamsOkOne n_p.val) :=
  ind_params_ok_from_val hwf block.length i b (by scalar_tac) h

/-- `ConLeche/Kernel/Env.lean:581-588` -- `env::ind_params_ok` refines
`indParamsOk`. -/
theorem ind_params_ok_refines {n_p : Std.U64} {block : alloc.vec.Vec env.ConstantInfo}
    {b : Bool} (hwf : ConstantInfosWF block)
    (h : env.ind_params_ok n_p block = ok b) :
    b = ConLeche.indParamsOk n_p.val (absConstantInfos block) := by
  rw [env.ind_params_ok] at h
  rw [indParamsOk_eq]
  simpa using ind_params_ok_from_val hwf block.length 0#usize b (by scalar_tac) h


/-! ## `ConstantInfo`'s accessors

`to_constant_val` and `constant_info_name` reach `env::proj_table_name` on the
`.ProjInfo` arm, through `proj_table_name_refines` above;
`constant_info_type` does not (a table's header type is the closed `Sort 1`, so
the reserved name is not read there). -/

/-- `ConLeche/Kernel/Env.lean:606-609` -- `env::to_constant_val` refines
`ConstantInfo.toConstantVal`. -/
theorem to_constant_val_refines
    {c : env.ConstantInfo} {r : env.ConstantVal}
    (h : env.to_constant_val c = ok r) :
    absConstantVal r = ConLeche.ConstantInfo.toConstantVal (absConstantInfo c) := by
  cases c with
  | AxiomInfo v => rw [env.to_constant_val] at h; rw [constant_val_dup_refines h]; rfl
  | DefnInfo v val hint =>
    rw [env.to_constant_val] at h; rw [constant_val_dup_refines h]; rfl
  | ThmInfo v val => rw [env.to_constant_val] at h; rw [constant_val_dup_refines h]; rfl
  | IndInfo v caps => rw [env.to_constant_val] at h; rw [constant_val_dup_refines h]; rfl
  | CtorInfo v np nf =>
    rw [env.to_constant_val] at h; rw [constant_val_dup_refines h]; rfl
  | RecInfo v mi rp rs =>
    rw [env.to_constant_val] at h; rw [constant_val_dup_refines h]; rfl
  | ProjInfo tbl =>
    simp only [env.to_constant_val, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨n, hn, v, hv, l, hl, l1, hl1, e, he, rfl⟩ := h
    rw [absConstantVal, proj_table_name_refines hn,
      alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv),
      Expr.sort_refines he, Level.succ_refines hl1, Level.zero_refines hl]
    rfl

/-- `ConLeche/Kernel/Env.lean:611` -- `env::constant_info_name` refines
`ConstantInfo.name`, spelled as a direct match (the port does not copy the
record on a lookup). -/
theorem constant_info_name_refines
    {c : env.ConstantInfo} {n : name.Name}
    (h : env.constant_info_name c = ok n) :
    absName n = ConLeche.ConstantInfo.name (absConstantInfo c) := by
  cases c with
  | AxiomInfo v =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h; rw [← h]; rfl
  | DefnInfo v val hint =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h; rw [← h]; rfl
  | ThmInfo v val =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h; rw [← h]; rfl
  | IndInfo v caps =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h; rw [← h]; rfl
  | CtorInfo v np nf =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h; rw [← h]; rfl
  | RecInfo v mi rp rs =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h; rw [← h]; rfl
  | ProjInfo tbl =>
    rw [env.constant_info_name] at h; rw [proj_table_name_refines h]; rfl

/-- `ConLeche/Kernel/Env.lean:616-618` -- `env::is_tower_entry` refines
`ConstantInfo.isTowerEntry`: a projection table is a table, not a term. -/
theorem is_tower_entry_refines {c : env.ConstantInfo} {b : Bool}
    (h : env.is_tower_entry c = ok b) :
    b = ConLeche.ConstantInfo.isTowerEntry (absConstantInfo c) := by
  cases c <;>
    (simp only [env.is_tower_entry, Result.ok.injEq] at h; rw [← h]; rfl)

/-- `ConLeche/Kernel/Env.lean:620` -- `env::constant_info_type` refines
`ConstantInfo.type`.  Unlike `to_constant_val` and `constant_info_name` this one
needs *no* `proj_table_name` hypothesis: a table's header carries the closed
dummy type `Sort 1`, and the reserved name is not read. -/
theorem constant_info_type_refines
    {c : env.ConstantInfo} {t : expr.Expr}
    (h : env.constant_info_type c = ok t) :
    absExpr t = ConLeche.ConstantInfo.type (absConstantInfo c) := by
  cases c with
  | AxiomInfo v =>
    simp only [env.constant_info_type, expr_dup_val, Result.ok.injEq] at h; rw [← h]; rfl
  | DefnInfo v val hint =>
    simp only [env.constant_info_type, expr_dup_val, Result.ok.injEq] at h; rw [← h]; rfl
  | ThmInfo v val =>
    simp only [env.constant_info_type, expr_dup_val, Result.ok.injEq] at h; rw [← h]; rfl
  | IndInfo v caps =>
    simp only [env.constant_info_type, expr_dup_val, Result.ok.injEq] at h; rw [← h]; rfl
  | CtorInfo v np nf =>
    simp only [env.constant_info_type, expr_dup_val, Result.ok.injEq] at h; rw [← h]; rfl
  | RecInfo v mi rp rs =>
    simp only [env.constant_info_type, expr_dup_val, Result.ok.injEq] at h; rw [← h]; rfl
  | ProjInfo tbl =>
    simp only [env.constant_info_type, bind_eq_ok_iff] at h
    obtain ⟨l, hl, l1, hl1, he⟩ := h
    rw [Expr.sort_refines he, Level.succ_refines hl1, Level.zero_refines hl]
    rfl

/-! ## The environment -/

/-- `ConLeche/Kernel/Env.lean:627-629` -- `env::env_dup` is the identity. -/
theorem env_dup_refines {e e' : env.Env} (h : env.env_dup e = ok e') : e' = e := by
  simp only [env.env_dup, bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨v, hv, rfl⟩ := h
  rw [constant_infos_copy_refines hv]

/-- `ConLeche/Kernel/Env.lean:634` -- `env::empty` refines `Env.empty`. -/
theorem empty_refines {e : env.Env} (h : env.empty = ok e) :
    absEnv e = ConLeche.Env.empty := by
  rw [env.empty, Result.ok.injEq] at h
  rw [← h, absEnv, absConstantInfos]
  simp [alloc.vec.Vec.new, ConLeche.Env.empty]

/-- `env::empty` is well formed: there is nothing in it. -/
theorem empty_wf {e : env.Env} (h : env.empty = ok e) : EnvWF e := by
  rw [env.empty, Result.ok.injEq] at h
  rw [← h]
  intro c hc
  simp [alloc.vec.Vec.new] at hc

/-- `env::constant_info_share` is the identity (`ron::ptr::new`, §3.2). -/
theorem constant_info_share_refines {c p : env.ConstantInfo}
    (h : env.constant_info_share c = ok p) : p = c := by
  rw [constant_info_share_val, Result.ok.injEq] at h; exact h.symm

/-- `env::constant_info_rc_dup` is the identity (`ron::ptr::clone`, §3.2). -/
theorem constant_info_rc_dup_refines {c p : env.ConstantInfo}
    (h : env.constant_info_rc_dup c = ok p) : p = c := by
  rw [constant_info_rc_dup_val, Result.ok.injEq] at h; exact h.symm

/-- `env::env_of_from` shares the rest of the records onto its accumulator. -/
theorem env_of_from_val (cs : alloc.vec.Vec env.ConstantInfo) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec env.ConstantInfo),
      cs.length - i.val ≤ k → env.env_of_from cs i out = ok v →
      v.val = out.val ++ cs.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [env.env_of_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [env.env_of_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ cs.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      have hlt : i.val < cs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := cs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        constant_info_share_val, Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨c1, hc1, out1, hout1, h⟩ := h
      rw [constant_info_dup_refines hc1] at hout1
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `env::env_of_from` at its own statement. -/
theorem env_of_from_refines {cs out v : alloc.vec.Vec env.ConstantInfo}
    {i : Std.Usize} (h : env.env_of_from cs i out = ok v) :
    v.val = out.val ++ cs.val.drop i.val :=
  env_of_from_val cs cs.length i out v (by scalar_tac) h

/-- `ConLeche/Kernel/Env.lean:627-629` -- `env::env_of` is the Lean's `⟨cs⟩`. -/
theorem env_of_refines {cs : alloc.vec.Vec env.ConstantInfo} {e : env.Env}
    (h : env.env_of cs = ok e) : absEnv e = ⟨absConstantInfos cs⟩ := by
  simp only [env.env_of, bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨v, hv, rfl⟩ := h
  have hvv : v = cs := alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.with_capacity] using
      env_of_from_val cs cs.length 0#usize _ v (by scalar_tac) hv)
  rw [absEnv, hvv]

/-- `env::env_of` is well formed when its records are. -/
theorem env_of_wf {cs : alloc.vec.Vec env.ConstantInfo} {e : env.Env}
    (hcs : ConstantInfosWF cs) (h : env.env_of cs = ok e) : EnvWF e := by
  simp only [env.env_of, bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨v, hv, rfl⟩ := h
  have hvv : v = cs := alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.with_capacity] using
      env_of_from_val cs cs.length 0#usize _ v (by scalar_tac) hv)
  rw [show EnvWF { consts := v } = ConstantInfosWF v from rfl, hvv]
  exact hcs

/-! ## The block's recursor suffix, decided on the tags -/

/-- `ConLeche/Kernel/Env.lean:666-668` -- `env::is_rec_info` refines
`ConstantInfo.isRecInfo`. -/
theorem is_rec_info_refines {c : env.ConstantInfo} {b : Bool}
    (h : env.is_rec_info c = ok b) :
    b = ConLeche.ConstantInfo.isRecInfo (absConstantInfo c) := by
  cases c <;> (simp only [env.is_rec_info, Result.ok.injEq] at h; rw [← h]; rfl)

/-- `ConLeche/Kernel/Env.lean:671-675` -- `env::all_rec_info_from` is the cited
`rest.all ConstantInfo.isRecInfo` over `block[i..]`. -/
theorem all_rec_info_from_val (block : alloc.vec.Vec env.ConstantInfo) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool),
      block.length - i.val ≤ k → env.all_rec_info_from block i = ok b →
      b = ((absConstantInfos block).drop i.val).all ConLeche.ConstantInfo.isRecInfo := by
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [env.all_rec_info_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
    rw [← h, absConstantInfos_drop_nil (by scalar_tac)]; rfl
  | succ k ih =>
    intro i b hk h
    rw [env.all_rec_info_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ block.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
      rw [← h, absConstantInfos_drop_nil (by scalar_tac)]; rfl
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
      have hlt : i.val < block.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := block.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec block i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b1, hb1, h⟩ := h
      rw [absConstantInfos_drop_cons hlt, List.all_cons, ← is_rec_info_refines hb1]
      cases b1 with
      | true =>
        simp only [reduceIte, bind_tc_ok] at h
        rw [ih w b (by scalar_tac) h, hwv]
        simp
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h]; simp

/-- `env::all_rec_info_from` at its own statement. -/
theorem all_rec_info_from_refines {block : alloc.vec.Vec env.ConstantInfo}
    {i : Std.Usize} {b : Bool} (h : env.all_rec_info_from block i = ok b) :
    b = ((absConstantInfos block).drop i.val).all ConLeche.ConstantInfo.isRecInfo :=
  all_rec_info_from_val block block.length i b (by scalar_tac) h

/-- `ConLeche/Kernel/Env.lean:671-675` -- `env::recs_form_suffix_from` refines
`recsFormSuffix` over `block[i..]`. -/
theorem recs_form_suffix_from_val (block : alloc.vec.Vec env.ConstantInfo) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool),
      block.length - i.val ≤ k → env.recs_form_suffix_from block i = ok b →
      b = ConLeche.recsFormSuffix ((absConstantInfos block).drop i.val) := by
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [env.recs_form_suffix_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
    rw [← h, absConstantInfos_drop_nil (by scalar_tac)]; rfl
  | succ k ih =>
    intro i b hk h
    rw [env.recs_form_suffix_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ block.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
      rw [← h, absConstantInfos_drop_nil (by scalar_tac)]; rfl
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
      have hlt : i.val < block.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := block.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec block i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b1, hb1, h⟩ := h
      rw [absConstantInfos_drop_cons hlt, ConLeche.recsFormSuffix,
        ← is_rec_info_refines hb1]
      cases b1 with
      | true =>
        simp only [reduceIte, bind_tc_ok] at h
        rw [all_rec_info_from_val block block.length w b (by scalar_tac) h, hwv]
        simp
      | false =>
        simp only [Bool.false_eq_true, if_false, bind_tc_ok] at h
        rw [ih w b (by scalar_tac) h, hwv]
        simp

/-- `env::recs_form_suffix_from` at its own statement. -/
theorem recs_form_suffix_from_refines {block : alloc.vec.Vec env.ConstantInfo}
    {i : Std.Usize} {b : Bool} (h : env.recs_form_suffix_from block i = ok b) :
    b = ConLeche.recsFormSuffix ((absConstantInfos block).drop i.val) :=
  recs_form_suffix_from_val block block.length i b (by scalar_tac) h

/-- `ConLeche/Kernel/Env.lean:671-675` -- `env::recs_form_suffix` refines
`recsFormSuffix`. -/
theorem recs_form_suffix_refines {block : alloc.vec.Vec env.ConstantInfo} {b : Bool}
    (h : env.recs_form_suffix block = ok b) :
    b = ConLeche.recsFormSuffix (absConstantInfos block) := by
  rw [env.recs_form_suffix] at h
  simpa using recs_form_suffix_from_val block block.length 0#usize b (by scalar_tac) h

/-- `ConLeche/Kernel/Env.lean:736-742` -- `env::block_rec_suffix_ok` is the
substituted decision behind `blockRecSuffixDec`, i.e. the tag pass. -/
theorem block_rec_suffix_ok_refines {block : alloc.vec.Vec env.ConstantInfo} {b : Bool}
    (h : env.block_rec_suffix_ok block = ok b) :
    b = ConLeche.recsFormSuffix (absConstantInfos block) := by
  rw [env.block_rec_suffix_ok] at h; exact recs_form_suffix_refines h

/-! ## `abs` is injective on the well-formed records

What the `*_beq` family's exactness rests on (DESIGN.md §3.5): the records
carry no derived data, so each of these is the componentwise injectivity of
`absName`/`absNames`/`absLevel`/`absLevels`/`absExpr`/`absExprs`/`absPropWhen`
under the matching `*WF`, and the machine words are equal as soon as their
`Nat` readings are. -/

/-- A `u64` is determined by its value. -/
theorem u64_val_inj {a b : Std.U64} (h : a.val = b.val) : a = b := by scalar_tac

theorem absNames_inj {xs ys : alloc.vec.Vec name.Name} (hx : NamesWF xs)
    (hy : NamesWF ys) (h : absNames xs = absNames ys) : xs = ys :=
  alloc.vec.Vec.ext _ _ (PropWhen.names_list_inj hx hy h)

theorem exprs_list_inj {l m : List expr.Expr} (hl : ∀ e ∈ l, ExprWF e)
    (hm : ∀ e ∈ m, ExprWF e) (h : l.map absExpr = m.map absExpr) : l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp_all
  | cons x l' ih =>
    cases m with
    | nil => simp at h
    | cons y m' =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [Expr.absExpr_injective (hl x (by simp)) (hm y (by simp)) h.1,
        ih (fun e he => hl e (by simp [he])) (fun e he => hm e (by simp [he])) h.2]

theorem absExprs_inj {xs ys : alloc.vec.Vec expr.Expr} (hx : ExprsWF xs)
    (hy : ExprsWF ys) (h : absExprs xs = absExprs ys) : xs = ys :=
  alloc.vec.Vec.ext _ _ (exprs_list_inj hx hy h)

theorem absConstantVal_inj {a b : env.ConstantVal} (ha : ConstantValWF a)
    (hb : ConstantValWF b) (h : absConstantVal a = absConstantVal b) : a = b := by
  obtain ⟨n1, ps1, t1⟩ := a
  obtain ⟨n2, ps2, t2⟩ := b
  obtain ⟨hn1, hps1, ht1⟩ := ha
  obtain ⟨hn2, hps2, ht2⟩ := hb
  simp only [absConstantVal, ConLeche.ConstantVal.mk.injEq] at h
  simp only [env.ConstantVal.mk.injEq]
  exact ⟨Name.absName_injective hn1 hn2 h.1, absNames_inj hps1 hps2 h.2.1,
    Expr.absExpr_injective ht1 ht2 h.2.2⟩

theorem absHint_inj {a b : env.ReducibilityHint} (h : absHint a = absHint b) :
    a = b := by
  cases a <;> cases b <;> simp_all [absHint]
  exact u64_val_inj h

theorem absFire_inj {a b : env.RecRuleFire} (ha : RecRuleFireWF a)
    (hb : RecRuleFireWF b) (h : absFire a = absFire b) : a = b := by
  cases a <;> cases b <;> simp_all only [absFire, RecRuleFireWF, reduceCtorEq,
    ConLeche.RecRuleFire.nested.injEq, env.RecRuleFire.Nested.injEq]
  exact ⟨Expr.absLevels_inj ha.1 hb.1 h.1, absExprs_inj ha.2 hb.2 h.2⟩

theorem absRecRule_inj {a b : env.RecRule} (ha : RecRuleWF a) (hb : RecRuleWF b)
    (h : absRecRule a = absRecRule b) : a = b := by
  obtain ⟨c1, nf1, cp1, f1, r1, k1, e1, pb1⟩ := a
  obtain ⟨c2, nf2, cp2, f2, r2, k2, e2, pb2⟩ := b
  obtain ⟨hc1, hf1, hr1⟩ := ha
  obtain ⟨hc2, hf2, hr2⟩ := hb
  simp only [absRecRule, ConLeche.RecRule.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [env.RecRule.mk.injEq]
  exact ⟨Name.absName_injective hc1 hc2 h1, u64_val_inj h2, u64_val_inj h3,
    absFire_inj hf1 hf2 h4, Expr.absExpr_injective hr1 hr2 h5, h6, h7, h8⟩

theorem absRecRules_list_inj {l m : List env.RecRule} (hl : ∀ r ∈ l, RecRuleWF r)
    (hm : ∀ r ∈ m, RecRuleWF r) (h : l.map absRecRule = m.map absRecRule) :
    l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp_all
  | cons x l' ih =>
    cases m with
    | nil => simp at h
    | cons y m' =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [absRecRule_inj (hl x (by simp)) (hm y (by simp)) h.1,
        ih (fun r hr => hl r (by simp [hr])) (fun r hr => hm r (by simp [hr])) h.2]

theorem absRecRules_inj {xs ys : alloc.vec.Vec env.RecRule} (hx : RecRulesWF xs)
    (hy : RecRulesWF ys) (h : absRecRules xs = absRecRules ys) : xs = ys :=
  alloc.vec.Vec.ext _ _ (absRecRules_list_inj hx hy h)

theorem absIndCaps_inj {a b : env.IndCaps} (ha : IndCapsWF a) (hb : IndCapsWF b)
    (h : absIndCaps a = absIndCaps b) : a = b := by
  obtain ⟨e1, ec1, ep1, ef1, u1, up1, k1, z1⟩ := a
  obtain ⟨e2, ec2, ep2, ef2, u2, up2, k2, z2⟩ := b
  obtain ⟨hec1, hz1⟩ := ha
  obtain ⟨hec2, hz2⟩ := hb
  simp only [absIndCaps, ConLeche.IndCaps.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [env.IndCaps.mk.injEq]
  exact ⟨h1, Name.absName_injective hec1 hec2 h2, u64_val_inj h3, u64_val_inj h4,
    h5, u64_val_inj h6, h7, PropWhen.absPropWhen_injective hz1 hz2 h8⟩

theorem absProjTable_inj {a b : env.ProjTable} (ha : ProjTableWF a)
    (hb : ProjTableWF b) (h : absProjTable a = absProjTable b) : a = b := by
  obtain ⟨s1, lp1, np1, c1, nf1, ss1, bo1, g1, o1⟩ := a
  obtain ⟨s2, lp2, np2, c2, nf2, ss2, bo2, g2, o2⟩ := b
  obtain ⟨hs1, hlp1, hc1, hss1, hbo1, hg1⟩ := ha
  obtain ⟨hs2, hlp2, hc2, hss2, hbo2, hg2⟩ := hb
  simp only [absProjTable, ConLeche.ProjTable.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have h7' : absExprs bo1 = absExprs bo2 := by
    simpa using congrArg Array.toList h7
  simp only [env.ProjTable.mk.injEq]
  exact ⟨Name.absName_injective hs1 hs2 h1, absNames_inj hlp1 hlp2 h2,
    u64_val_inj h3, Name.absName_injective hc1 hc2 h4, u64_val_inj h5,
    Level.absLevel_injective hss1 hss2 h6, absExprs_inj hbo1 hbo2 h7',
    Expr.absLevels_inj hg1 hg2 h8, u64_val_inj h9⟩

/-- `absConstantInfo` is injective on well-formed stored constants — the fact
`constant_info_beq`'s exactness rests on. -/
theorem absConstantInfo_injective {a b : env.ConstantInfo}
    (ha : ConstantInfoWF a) (hb : ConstantInfoWF b)
    (h : absConstantInfo a = absConstantInfo b) : a = b := by
  cases a <;> cases b <;>
    simp_all only [absConstantInfo, ConstantInfoWF, reduceCtorEq,
      ConLeche.ConstantInfo.axiomInfo.injEq, ConLeche.ConstantInfo.defnInfo.injEq,
      ConLeche.ConstantInfo.thmInfo.injEq, ConLeche.ConstantInfo.indInfo.injEq,
      ConLeche.ConstantInfo.ctorInfo.injEq, ConLeche.ConstantInfo.recInfo.injEq,
      ConLeche.ConstantInfo.projInfo.injEq, env.ConstantInfo.AxiomInfo.injEq,
      env.ConstantInfo.DefnInfo.injEq, env.ConstantInfo.ThmInfo.injEq,
      env.ConstantInfo.IndInfo.injEq, env.ConstantInfo.CtorInfo.injEq,
      env.ConstantInfo.RecInfo.injEq, env.ConstantInfo.ProjInfo.injEq]
  case AxiomInfo.AxiomInfo => exact absConstantVal_inj ha hb h
  case DefnInfo.DefnInfo =>
    exact ⟨absConstantVal_inj ha.1 hb.1 h.1,
      Expr.absExpr_injective ha.2 hb.2 h.2.1, absHint_inj h.2.2⟩
  case ThmInfo.ThmInfo =>
    exact ⟨absConstantVal_inj ha.1 hb.1 h.1, Expr.absExpr_injective ha.2 hb.2 h.2⟩
  case IndInfo.IndInfo =>
    exact ⟨absConstantVal_inj ha.1 hb.1 h.1, absIndCaps_inj ha.2 hb.2 h.2⟩
  case CtorInfo.CtorInfo =>
    exact ⟨absConstantVal_inj ha hb h.1, u64_val_inj h.2.1, u64_val_inj h.2.2⟩
  case RecInfo.RecInfo =>
    exact ⟨absConstantVal_inj ha.1 hb.1 h.1, u64_val_inj h.2.1,
      u64_val_inj h.2.2.1, absRecRules_inj ha.2 hb.2 h.2.2.2⟩
  case ProjInfo.ProjInfo => exact absProjTable_inj ha hb h

/-! ## Two list equalities the `*_beq` family needs

`prop_when::names_beq` and `expr::exprs_beq` are the `List Name` and
`List Expr` equalities of the derived instances; neither had a top-level
refinement lemma yet (`Refine/PropWhen.lean` proves the loop,
`Refine/Expr.lean` proves `levels_beq`).  They belong in those files and are
here only so that task #46 does not edit them. -/

/-- `prop_when::names_beq` decides equality of the abstracted name lists. -/
theorem names_beq_refines {ps qs : alloc.vec.Vec name.Name} {c : Bool}
    (hps : NamesWF ps) (hqs : NamesWF qs)
    (h : prop_when.names_beq ps qs = ok c) :
    c = decide (absNames ps = absNames qs) := by
  rw [prop_when.names_beq] at h
  have hfrom := PropWhen.names_beq_from_refines hps hqs ps.val.length 0#usize c
    (by scalar_tac) h
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [h0, List.drop_zero, List.drop_zero] at hfrom
  cases c
  · refine (decide_eq_false ?_).symm
    intro hc
    exact absurd (PropWhen.names_list_inj hps hqs hc) (by simpa using hfrom)
  · refine (decide_eq_true ?_).symm
    rw [absNames, absNames, hfrom.mp rfl]

/-- The index recursion behind `expr::exprs_beq`; `hlen` is the length test the
entry point has already made. -/
theorem exprs_beq_from_refines {xs ys : alloc.vec.Vec expr.Expr}
    (hx : ExprsWF xs) (hy : ExprsWF ys) (hlen : xs.val.length = ys.val.length) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool), xs.val.length - i.val ≤ k →
      expr.exprs_beq_from xs ys i = ok b →
      (b = true ↔ (xs.val.drop i.val).map absExpr = (ys.val.drop i.val).map absExpr) := by
  have hnil : ∀ (i : Std.Usize), xs.val.length ≤ i.val →
      ((xs.val.drop i.val).map absExpr = (ys.val.drop i.val).map absExpr) := by
    intro i hi
    rw [List.drop_eq_nil_of_le hi, List.drop_eq_nil_of_le (by omega)]
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [expr.exprs_beq_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [← h]
    exact iff_of_true rfl (hnil i (by scalar_tac))
  | succ k ih =>
    intro i b hk h
    rw [expr.exprs_beq_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ xs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
      rw [← h]
      exact iff_of_true rfl (hnil i (by scalar_tac))
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      have hl : i.val < xs.val.length := by scalar_tac
      have hr : i.val < ys.val.length := by omega
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := xs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy2, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec xs i hl)
      obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ys i hr)
      subst hyv; subst hzv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy2, hz,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b0, hb0, h⟩ := h
      have hb0' := Expr.beq_refines (hx _ (List.getElem_mem hl))
        (hy _ (List.getElem_mem hr)) hb0
      rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons hr,
        List.map_cons, List.map_cons, List.cons.injEq]
      cases hc : b0
      · rw [hc] at hb0' h
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        have hne := of_decide_eq_false hb0'.symm
        rw [← h]
        simp only [Bool.false_eq_true, false_iff, not_and]
        intro hhd; exact absurd hhd hne
      · rw [hc] at hb0' h
        simp only [if_true, bind_eq_ok_iff, hw, Result.ok.injEq, exists_eq_left'] at h
        have heq := of_decide_eq_true hb0'.symm
        have hrec := ih w b (by scalar_tac) h
        rw [hwv] at hrec
        rw [hrec]
        simp only [heq, true_and]

/-- `expr::exprs_beq` decides equality of the abstracted term lists, exactly. -/
theorem exprs_beq_refines {xs ys : alloc.vec.Vec expr.Expr} {c : Bool}
    (hx : ExprsWF xs) (hy : ExprsWF ys) (h : expr.exprs_beq xs ys = ok c) :
    c = decide (absExprs xs = absExprs ys) := by
  rw [expr.exprs_beq.eq_def] at h; simp only [] at h
  by_cases hlen : xs.val.length = ys.val.length
  · rw [if_pos (show alloc.vec.Vec.len xs = alloc.vec.Vec.len ys by scalar_tac)] at h
    have hfrom := exprs_beq_from_refines hx hy hlen xs.val.length 0#usize c
      (by scalar_tac) h
    have h0 : (0#usize : Std.Usize).val = 0 := rfl
    rw [h0, List.drop_zero, List.drop_zero] at hfrom
    cases c
    · refine (decide_eq_false ?_).symm
      simp only [absExprs]
      intro hcc
      simpa using hfrom.mpr hcc
    · refine (decide_eq_true ?_).symm
      simp only [absExprs]
      exact hfrom.mp rfl
  · rw [if_neg (show ¬ alloc.vec.Vec.len xs = alloc.vec.Vec.len ys by
      intro hc; exact hlen (by scalar_tac)), Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    simp only [absExprs]
    intro hc
    exact hlen (by simpa using congrArg List.length hc)

/-! ## The derived structural equalities

`env.rs`'s `*_beq` family is Lean's `deriving DecidableEq` on the records,
spelled out componentwise over the crate's own `name::beq`/`expr::beq`/
`level::beq`/`prop_when::beq` (task #9's rule).  Each lemma says the `Bool` the
Rust returns **is** `decide (abs a = abs b)`, which is what the two
pinned-basis guards read (`env.find? eqName == some eqA`, …) and what makes
them exact.  Every arm is one of two shapes — `let y ← <test>; if y then <rest>
else false` (`Refine/Expr.lean`'s `guard_step`) and `if <scalar test> then
<rest> else false` (`scalar_step` below) — so the proofs are the chains. -/

/-- The arm shape whose test is a *decidable proposition* rather than a call:
the scalar and `Bool` field comparisons the generated code emits as a plain
`if` (`rec_rule_beq`'s `nfields`, `ind_caps_beq`'s `eta`, …). -/
theorem scalar_step {P Q : Prop} [Decidable P] [Decidable Q] {c : Bool}
    {rest : Result Bool} (hrest : ∀ y, rest = ok y → y = decide Q)
    (h : (if P then rest else ok false) = ok c) : c = decide (P ∧ Q) := by
  by_cases hp : P
  · rw [if_pos hp] at h; rw [hrest c h]; simp [hp]
  · rw [if_neg hp, Result.ok.injEq] at h; rw [← h]; simp [hp]

/-- The last arm: the generated code answers `ok (decide P)` outright. -/
theorem final_step {P : Prop} [Decidable P] {c : Bool}
    (h : (ok (decide P) : Result Bool) = ok c) : c = decide P :=
  (Result.ok_injective h).symm

/-- `ConLeche/Kernel/Env.lean:196-201` — `constant_val_beq` is
`decide (· = ·)` on the abstracted records. -/
theorem constant_val_beq_refines {a b : env.ConstantVal} {c : Bool}
    (ha : ConstantValWF a) (hb : ConstantValWF b)
    (h : env.constant_val_beq a b = ok c) :
    c = decide (absConstantVal a = absConstantVal b) := by
  rw [env.constant_val_beq] at h
  rw [Expr.guard_step (fun y hy => Name.beq_refines ha.1 hb.1 hy)
    (fun y hy => Expr.guard_step (fun z hz => names_beq_refines ha.2.1 hb.2.1 hz)
      (fun z hz => Expr.beq_refines ha.2.2 hb.2.2 hz) hy) h]
  exact decide_eq_decide.mpr (by simp [absConstantVal])

/-- `ConLeche/Kernel/Env.lean:312-322` — `reducibility_hint_beq`. -/
theorem reducibility_hint_beq_refines {a b : env.ReducibilityHint} {c : Bool}
    (h : env.reducibility_hint_beq a b = ok c) :
    c = decide (absHint a = absHint b) := by
  rw [env.reducibility_hint_beq.eq_def] at h
  cases a <;> cases b <;>
    simp_all only [absHint, reduceCtorEq, decide_false, decide_true,
      Result.ok.injEq, ConLeche.ReducibilityHint.regular.injEq]
  exact Expr.u64_eq_test h

/-- `ConLeche/Kernel/Env.lean:203-247` — `rec_rule_fire_beq`. -/
theorem rec_rule_fire_beq_refines {a b : env.RecRuleFire} {c : Bool}
    (ha : RecRuleFireWF a) (hb : RecRuleFireWF b)
    (h : env.rec_rule_fire_beq a b = ok c) :
    c = decide (absFire a = absFire b) := by
  rw [env.rec_rule_fire_beq.eq_def] at h
  cases a <;> cases b <;>
    simp_all only [absFire, RecRuleFireWF, reduceCtorEq, decide_false, decide_true,
      Result.ok.injEq, ConLeche.RecRuleFire.nested.injEq]
  rw [Expr.guard_step (fun y hy => Expr.levels_beq_refines ha.1 hb.1 hy)
    (fun y hy => exprs_beq_refines ha.2 hb.2 hy) h]

/-- `ConLeche/Kernel/Env.lean:249-292` — `rec_rule_beq`, the five
install-computed fields included: the guard compares the *stored* rule. -/
theorem rec_rule_beq_refines {a b : env.RecRule} {c : Bool}
    (ha : RecRuleWF a) (hb : RecRuleWF b) (h : env.rec_rule_beq a b = ok c) :
    c = decide (absRecRule a = absRecRule b) := by
  rw [env.rec_rule_beq] at h
  rw [Expr.guard_step (fun y hy => Name.beq_refines ha.1 hb.1 hy)
    (fun y hy => scalar_step (fun z hz => scalar_step
      (fun w hw => Expr.guard_step
        (fun u hu => rec_rule_fire_beq_refines ha.2.1 hb.2.1 hu)
        (fun u hu => Expr.guard_step
          (fun v hv => Expr.beq_refines ha.2.2 hb.2.2 hv)
          (fun v hv => scalar_step (fun t ht => scalar_step
            (fun s hs => final_step hs) ht) hv) hu) hw) hz) hy) h]
  refine decide_eq_decide.mpr ?_
  simp only [absRecRule, ConLeche.RecRule.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, by rw [h2], by rw [h3], h4, h5, h6, h7, h8⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, u64_val_inj h2, u64_val_inj h3, h4, h5, h6, h7, h8⟩

/-- The index recursion behind `rec_rules_beq`; `hlen` is the length test the
entry point has already made. -/
theorem rec_rules_beq_from_refines {xs ys : alloc.vec.Vec env.RecRule}
    (hx : RecRulesWF xs) (hy : RecRulesWF ys)
    (hlen : xs.val.length = ys.val.length) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool), xs.val.length - i.val ≤ k →
      env.rec_rules_beq_from xs ys i = ok b →
      (b = true ↔ (xs.val.drop i.val).map absRecRule
        = (ys.val.drop i.val).map absRecRule) := by
  have hnil : ∀ (i : Std.Usize), xs.val.length ≤ i.val →
      ((xs.val.drop i.val).map absRecRule = (ys.val.drop i.val).map absRecRule) := by
    intro i hi
    rw [List.drop_eq_nil_of_le hi, List.drop_eq_nil_of_le (by omega)]
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [env.rec_rules_beq_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [← h]
    exact iff_of_true rfl (hnil i (by scalar_tac))
  | succ k ih =>
    intro i b hk h
    rw [env.rec_rules_beq_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ xs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
      rw [← h]
      exact iff_of_true rfl (hnil i (by scalar_tac))
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      have hl : i.val < xs.val.length := by scalar_tac
      have hr : i.val < ys.val.length := by omega
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := xs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy2, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec xs i hl)
      obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ys i hr)
      subst hyv; subst hzv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy2, hz,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b0, hb0, h⟩ := h
      have hb0' := rec_rule_beq_refines (hx _ (List.getElem_mem hl))
        (hy _ (List.getElem_mem hr)) hb0
      rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons hr,
        List.map_cons, List.map_cons, List.cons.injEq]
      cases hc : b0
      · rw [hc] at hb0' h
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        have hne := of_decide_eq_false hb0'.symm
        rw [← h]
        simp only [Bool.false_eq_true, false_iff, not_and]
        intro hhd; exact absurd hhd hne
      · rw [hc] at hb0' h
        simp only [if_true, bind_eq_ok_iff, hw, Result.ok.injEq, exists_eq_left'] at h
        have heq := of_decide_eq_true hb0'.symm
        have hrec := ih w b (by scalar_tac) h
        rw [hwv] at hrec
        rw [hrec]
        simp only [heq, true_and]

/-- `ConLeche/Kernel/Env.lean:249-292` — `rec_rules_beq`, the `List.beq` over
`BEq RecRule` of `recInfo`'s `rules` field. -/
theorem rec_rules_beq_refines {xs ys : alloc.vec.Vec env.RecRule} {c : Bool}
    (hx : RecRulesWF xs) (hy : RecRulesWF ys)
    (h : env.rec_rules_beq xs ys = ok c) :
    c = decide (absRecRules xs = absRecRules ys) := by
  rw [env.rec_rules_beq.eq_def] at h; simp only [] at h
  by_cases hlen : xs.val.length = ys.val.length
  · rw [if_pos (show alloc.vec.Vec.len xs = alloc.vec.Vec.len ys by scalar_tac)] at h
    have hfrom := rec_rules_beq_from_refines hx hy hlen xs.val.length 0#usize c
      (by scalar_tac) h
    have h0 : (0#usize : Std.Usize).val = 0 := rfl
    rw [h0, List.drop_zero, List.drop_zero] at hfrom
    cases c
    · refine (decide_eq_false ?_).symm
      simp only [absRecRules]
      intro hcc
      simpa using hfrom.mpr hcc
    · refine (decide_eq_true ?_).symm
      simp only [absRecRules]
      exact hfrom.mp rfl
  · rw [if_neg (show ¬ alloc.vec.Vec.len xs = alloc.vec.Vec.len ys by
      intro hc; exact hlen (by scalar_tac)), Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    simp only [absRecRules]
    intro hc
    exact hlen (by simpa using congrArg List.length hc)

/-- `ConLeche/Kernel/Env.lean:357-384` — `ind_caps_beq`, the result-sort
zero-ness datum through `prop_when::beq`. -/
theorem ind_caps_beq_refines {a b : env.IndCaps} {c : Bool}
    (ha : IndCapsWF a) (hb : IndCapsWF b) (h : env.ind_caps_beq a b = ok c) :
    c = decide (absIndCaps a = absIndCaps b) := by
  rw [env.ind_caps_beq] at h
  rw [scalar_step (fun y hy => Expr.guard_step
    (fun z hz => Name.beq_refines ha.1 hb.1 hz)
    (fun z hz => scalar_step (fun w hw => scalar_step (fun u hu =>
      scalar_step (fun v hv => scalar_step (fun t ht => scalar_step
        (fun s hs => PropWhen.beq_refines ha.2 hb.2 hs) ht) hv) hu) hw) hz) hy) h]
  refine decide_eq_decide.mpr ?_
  simp only [absIndCaps, ConLeche.IndCaps.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, by rw [h3], by rw [h4], h5, by rw [h6], h7, h8⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, u64_val_inj h3, u64_val_inj h4, h5, u64_val_inj h6, h7, h8⟩

/-- `ConLeche/Kernel/Env.lean:386-441` — `proj_table_beq`, componentwise in the
cited field order (`bodies` before `guards`, `off` last). -/
theorem proj_table_beq_refines {a b : env.ProjTable} {c : Bool}
    (ha : ProjTableWF a) (hb : ProjTableWF b)
    (h : env.proj_table_beq a b = ok c) :
    c = decide (absProjTable a = absProjTable b) := by
  rw [env.proj_table_beq] at h
  rw [Expr.guard_step (fun y hy => Name.beq_refines ha.1 hb.1 hy)
    (fun y hy => Expr.guard_step (fun z hz => names_beq_refines ha.2.1 hb.2.1 hz)
      (fun z hz => scalar_step (fun w hw => Expr.guard_step
        (fun u hu => Name.beq_refines ha.2.2.1 hb.2.2.1 hu)
        (fun u hu => scalar_step (fun v hv => Expr.guard_step
          (fun t ht => Level.beq_refines ha.2.2.2.1 hb.2.2.2.1 ht)
          (fun t ht => Expr.guard_step
            (fun s hs => exprs_beq_refines ha.2.2.2.2.1 hb.2.2.2.2.1 hs)
            (fun s hs => Expr.guard_step
              (fun q hq => Expr.levels_beq_refines ha.2.2.2.2.2 hb.2.2.2.2.2 hq)
              (fun q hq => final_step hq) hs) ht) hv) hu) hw) hz) hy) h]
  refine decide_eq_decide.mpr ?_
  simp only [absProjTable, ConLeche.ProjTable.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h2, by rw [h3], h4, by rw [h5], h6, by rw [h7], h8, by rw [h9]⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h2, u64_val_inj h3, h4, u64_val_inj h5, h6,
      by simpa using congrArg Array.toList h7, h8, u64_val_inj h9⟩

/-- `ConLeche/Kernel/Env.lean:470-496` — **the equality the two pinned-basis
guards read** (`env.find? eqName == some eqA`,
`decide (env.find? natName = some natA)`): `constant_info_beq` is
`decide (· = ·)` on the abstracted stored constants.  Different constructors
are unequal because `absConstantInfo` maps the seven Rust constructors onto the
seven con-leche ones; each diagonal arm is its record's own `*_beq`. -/
theorem constant_info_beq_refines {a b : env.ConstantInfo} {c : Bool}
    (ha : ConstantInfoWF a) (hb : ConstantInfoWF b)
    (h : env.constant_info_beq a b = ok c) :
    c = decide (absConstantInfo a = absConstantInfo b) := by
  cases a <;> cases b <;> simp only [env.constant_info_beq] at h <;>
    simp only [absConstantInfo, reduceCtorEq, decide_false,
      ConLeche.ConstantInfo.axiomInfo.injEq, ConLeche.ConstantInfo.defnInfo.injEq,
      ConLeche.ConstantInfo.thmInfo.injEq, ConLeche.ConstantInfo.indInfo.injEq,
      ConLeche.ConstantInfo.ctorInfo.injEq, ConLeche.ConstantInfo.recInfo.injEq,
      ConLeche.ConstantInfo.projInfo.injEq]
  all_goals try exact (Result.ok_injective h).symm
  case AxiomInfo.AxiomInfo => exact constant_val_beq_refines ha hb h
  case DefnInfo.DefnInfo =>
    exact Expr.guard_step (fun y hy => constant_val_beq_refines ha.1 hb.1 hy)
      (fun y hy => Expr.guard_step (fun z hz => Expr.beq_refines ha.2 hb.2 hz)
        (fun z hz => reducibility_hint_beq_refines hz) hy) h
  case ThmInfo.ThmInfo =>
    exact Expr.guard_step (fun y hy => constant_val_beq_refines ha.1 hb.1 hy)
      (fun y hy => Expr.beq_refines ha.2 hb.2 hy) h
  case IndInfo.IndInfo =>
    exact Expr.guard_step (fun y hy => constant_val_beq_refines ha.1 hb.1 hy)
      (fun y hy => ind_caps_beq_refines ha.2 hb.2 hy) h
  case CtorInfo.CtorInfo =>
    exact Expr.guard_step (fun y hy => constant_val_beq_refines ha hb hy)
      (fun y hy => Expr.guard_step (fun z hz => Expr.u64_eq_test hz)
        (fun z hz => Expr.u64_eq_test hz) hy) h
  case RecInfo.RecInfo =>
    exact Expr.guard_step (fun y hy => constant_val_beq_refines ha.1 hb.1 hy)
      (fun y hy => Expr.guard_step (fun z hz => Expr.u64_eq_test hz)
        (fun z hz => Expr.guard_step (fun w hw => Expr.u64_eq_test hw)
          (fun w hw => rec_rules_beq_refines ha.2 hb.2 hw) hz) hy) h
  case ProjInfo.ProjInfo => exact proj_table_beq_refines ha hb h

/-! ## `ConstantInfo`'s name, and the lookup -/

/-- `constant_info_name` answers a well-formed name. -/
theorem constant_info_name_wf {c : env.ConstantInfo} {n : name.Name}
    (hc : ConstantInfoWF c) (h : env.constant_info_name c = ok n) : NameWF n := by
  cases c <;>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h
  case AxiomInfo v => rw [← h]; exact hc.1
  case DefnInfo v _ _ => rw [← h]; exact hc.1.1
  case ThmInfo v _ => rw [← h]; exact hc.1.1
  case IndInfo v _ => rw [← h]; exact hc.1.1
  case CtorInfo v _ _ => rw [← h]; exact hc.1
  case RecInfo v _ _ _ => rw [← h]; exact hc.1.1
  case ProjInfo tbl => exact proj_table_name_wf hc.1 h

/-- The index recursion behind `find`: `find_from cs i n` is `List.find?` over
`cs[i..]`, in the cited (newest-first) order. -/
theorem find_from_refines {cs : alloc.vec.Vec env.ConstantInfo} {n : name.Name}
    (hcs : ConstantInfosWF cs) (hn : NameWF n) :
    ∀ k : Nat, ∀ (i : Std.Usize) (o : Option env.ConstantInfo),
      cs.val.length - i.val ≤ k → env.find_from cs i n = ok o →
      o.map absConstantInfo = List.find? (fun ci => ci.name == absName n)
        ((cs.val.drop i.val).map absConstantInfo) := by
  intro k
  induction k with
  | zero =>
    intro i o hk h
    rw [env.find_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]
    simp
  | succ k ih =>
    intro i o hk h
    rw [env.find_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ cs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      have hl : i.val < cs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := cs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hl)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, arc_deref_eq,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨n1, hn1, b, hb, h⟩ := h
      have hwfc := hcs _ (List.getElem_mem hl)
      have hb' := Name.beq_refines (constant_info_name_wf hwfc hn1) hn hb
      rw [constant_info_name_refines hn1] at hb'
      rw [List.drop_eq_getElem_cons hl, List.map_cons, List.find?_cons]
      cases hc : b
      · rw [hc] at hb' h
        simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, hw,
          Result.ok.injEq, exists_eq_left'] at h
        have hne := of_decide_eq_false hb'.symm
        rw [show ((absConstantInfo cs.val[i.val]).name == absName n) = false from
          by simpa using hne]
        have hrec := ih w o (by scalar_tac) h
        rw [hwv] at hrec
        exact hrec
      · rw [hc] at hb' h
        simp only [if_true, bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
        have heq := of_decide_eq_true hb'.symm
        rw [show ((absConstantInfo cs.val[i.val]).name == absName n) = true from
          by simpa using heq, ← h]
        simp

/-- `ConLeche/Kernel/Env.lean:636-637` — `env::find` refines `Env.find?`: the
linear search over `consts` in its newest-first order, so the newest binding of
a name wins. -/
theorem find_refines {e : env.Env} {n : name.Name} {o : Option env.ConstantInfo}
    (he : EnvWF e) (hn : NameWF n) (h : env.find e n = ok o) :
    o.map absConstantInfo = (absEnv e).find? (absName n) := by
  rw [env.find] at h
  have hfrom := find_from_refines he hn e.consts.val.length 0#usize o
    (by scalar_tac) h
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [h0, List.drop_zero] at hfrom
  rw [hfrom, ConLeche.Env.find?, absEnv, absConstantInfos]

/-- `env::find` answers a well-formed stored constant. -/
theorem find_wf {e : env.Env} {n : name.Name} {o : Option env.ConstantInfo}
    (he : EnvWF e) (h : env.find e n = ok o) :
    ∀ c, o = some c → ConstantInfoWF c := by
  have key : ∀ k : Nat, ∀ (i : Std.Usize) (o : Option env.ConstantInfo),
      e.consts.val.length - i.val ≤ k → env.find_from e.consts i n = ok o →
      ∀ c, o = some c → ConstantInfoWF c := by
    intro k
    induction k with
    | zero =>
      intro i o hk h c hc
      rw [env.find_from.eq_def] at h; simp only [] at h
      rw [if_pos (show i ≥ alloc.vec.Vec.len e.consts by scalar_tac),
        Result.ok.injEq] at h
      rw [← h] at hc; simp at hc
    | succ k ih =>
      intro i o hk h c hc
      rw [env.find_from.eq_def] at h; simp only [] at h
      by_cases hi : i.val ≥ e.consts.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len e.consts by scalar_tac),
          Result.ok.injEq] at h
        rw [← h] at hc; simp at hc
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len e.consts by scalar_tac)] at h
        have hl : i.val < e.consts.val.length := by scalar_tac
        have hmax : i.val + 1 ≤ Std.Usize.max := by
          have := e.consts.slice.property; scalar_tac
        obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
        obtain ⟨y, hy, hyv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec e.consts i hl)
        subst hyv
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, arc_deref_eq,
          Result.ok.injEq, exists_eq_left'] at h
        obtain ⟨n1, hn1, b, hb, h⟩ := h
        cases hcb : b
        · rw [hcb] at h
          simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, hw,
            Result.ok.injEq, exists_eq_left'] at h
          exact ih w o (by scalar_tac) h c hc
        · rw [hcb] at h
          simp only [if_true, bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
          rw [← h, Option.some.injEq] at hc
          rw [← hc]
          exact he _ (List.getElem_mem hl)
  rw [env.find] at h
  exact key e.consts.val.length 0#usize o (by scalar_tac) h

/-! ## The projection lookup -/

/-- `ConLeche/Kernel/Env.lean:642-645` — `env::find_proj` refines
`Env.findProj?`: the structure's table under `proj_table_name T`, viewed at
field `i`, and `none` beyond the table's field count. -/
theorem find_proj_refines {e : env.Env} {t : name.Name} {i : Std.U64}
    {o : Option env.ProjEntry} (he : EnvWF e) (ht : NameWF t)
    (h : env.find_proj e t i = ok o) :
    o.map absProjEntry = (absEnv e).findProj? (absName t) i.val := by
  rw [env.find_proj] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, oc, hoc, h⟩ := h
  have hfind := find_refines he (proj_table_name_wf ht hn) hoc
  rw [proj_table_name_refines hn] at hfind
  rw [ConLeche.Env.findProj?, ← hfind]
  cases oc with
  | none => simp only [Option.map_none] at hfind ⊢; simpa using h.symm
  | some ci =>
    have hwf := find_wf he hoc ci rfl
    cases ci <;> simp only [] at h <;>
      simp only [Option.map_some, absConstantInfo] <;>
      try simpa using h.symm
    case ProjInfo tbl =>
      by_cases hlt : i.val < tbl.num_fields.val
      · rw [if_pos (show i < tbl.num_fields by scalar_tac), bind_eq_ok_iff] at h
        obtain ⟨pe, hpe, h⟩ := h
        rw [if_pos (show i.val < (absProjTable tbl).numFields from hlt),
          ← Result.ok_injective h]
        simp only [Option.map_some, Option.some.injEq]
        exact proj_table_entry_refines hpe
      · rw [if_neg (show ¬ i < tbl.num_fields by scalar_tac), Result.ok.injEq] at h
        rw [if_neg (show ¬ i.val < (absProjTable tbl).numFields from hlt), ← h]
        simp

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing but Lean's own three axioms: no `sorry`, nothing from the `Arc`/`P`
models, and — in particular — nothing reaches
`ConRon.Generated.kernel.pins_text.PINS_TEXT`, whose string constant carries a
`native_decide` axiom (task #43). -/

/--
info: 'ConRon.Refine.Env.constant_info_beq_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms constant_info_beq_refines

/--
info: 'ConRon.Refine.Env.find_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms find_refines

/--
info: 'ConRon.Refine.Env.find_proj_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms find_proj_refines

/--
info: 'ConRon.Refine.Env.absConstantInfo_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms absConstantInfo_injective

/--
info: 'ConRon.Refine.Env.proj_table_name_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms proj_table_name_refines

/--
info: 'ConRon.Refine.Env.ind_params_ok_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ind_params_ok_refines

end ConRon.Refine.Env
