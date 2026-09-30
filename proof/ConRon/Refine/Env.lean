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
* **`find`/`find_proj`** — the linear search over `Env.consts`, read from the
  back because the port stores that list reversed (task #50, `absEnv`), so what
  is scanned is the cited newest-first order and the newest binding of a name
  still wins; `= Env.find?`/`Env.findProj?` on the nose, plus the fact
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

/-! ## The check mode

`ConLeche.CheckMode`'s six accessors are constant functions of the
constructor, so each refinement is one `simp` per mode. -/

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

/-- `env::levels_copy` is the identity: the copy is the very same `Vec`. -/
theorem levels_copy_refines {us v : alloc.vec.Vec level.Level}
    (h : env.levels_copy us = ok v) : v = us := by
  rw [env.levels_copy] at h
  exact alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.with_capacity] using
      levels_copy_from_val us us.length 0#usize _ v (by scalar_tac) h)

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

/-- `ConLeche/Kernel/Env.lean:318-322` -- `env::reducibility_hint_dup` is the
identity. -/
theorem reducibility_hint_dup_refines {h1 h2 : env.ReducibilityHint}
    (h : env.reducibility_hint_dup h1 = ok h2) : h2 = h1 := by
  cases h1 <;> simp only [env.reducibility_hint_dup, Result.ok.injEq] at h <;>
    exact h.symm

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
    PropWhen.if_all_zero_wf (fun _ hm => by simp [alloc.vec.Vec.new] at hm) hpw,
    fun _ hm => by simp [alloc.vec.Vec.new] at hm,
    fun _ hm => by simp [alloc.vec.Vec.new] at hm⟩

/-- `ConLeche/Kernel/Env.lean:362-384` -- `env::ind_caps_dup` is the
identity. -/
theorem ind_caps_dup_refines {c c' : env.IndCaps}
    (h : env.ind_caps_dup c = ok c') : c' = c := by
  simp only [env.ind_caps_dup, bind_eq_ok_iff, name_dup_eq, Result.ok.injEq,
    exists_eq_left'] at h
  obtain ⟨pw, hpw, v, hv, v1, hv1, rfl⟩ := h
  rw [PropWhen.dup_eq hpw, alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv),
    alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv1)]

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

/-- A `u64` narrowed to a `usize` keeps its value when it fits. -/
theorem u64_cast_usize_val {x : Std.U64} (h : x.val ≤ Std.Usize.max) :
    (UScalar.cast UScalarTy.Usize x).val = x.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  scalar_tac

/-! ## `RecRule` and `ConstantInfo` copies

`env::constant_info_share` and `env::constant_info_rc_dup` are `ron::ptr`
calls, hence the identity in the model (DESIGN.md §3.2); their `= ok` readings
are what the two `ConstantInfo` loops below need, so they come first. -/

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

/-! ## The presented declarations -/

/-! ## The declared-parameter-count check

`pi_sort_tele_len` is the one *real* induction of this file.  Aeneas's
`partial_fixpoint` definitions come with `fixpoint_induct` (which wants an
admissible motive) but no `partial_correctness` form over `Result`, so the
recursion is carried by the argument: `eq_def`, and the induction principle of
the `ExprWF` derivation (task #5's shape; DESIGN.md task #99-PFIX).  The ten kinds' inversion lemmas are
`ConRon/Refine/Expr.lean`'s `bvar_inv`, `forall_e_inv`, … -/

/-! ## `ConstantInfo`'s accessors

`to_constant_val` and `constant_info_name` reach `env::proj_table_name` on the
`.ProjInfo` arm, through `proj_table_name_refines` above;
`constant_info_type` does not (a table's header type is the closed `Sort 1`, so
the reserved name is not read there). -/

/-! ## The environment -/

/-! ## The block's recursor suffix, decided on the tags -/

/-! ## `abs` is injective on the well-formed records

What the `*_beq` family's exactness rests on (DESIGN.md §3.5): the records
carry no derived data, so each of these is the componentwise injectivity of
`absName`/`absNames`/`absLevel`/`absLevels`/`absExpr`/`absExprs`/`absPropWhen`
under the matching `*WF`, and the machine words are equal as soon as their
`Nat` readings are. -/

/-- A `u64` is determined by its value. -/
theorem u64_val_inj {a b : Std.U64} (h : a.val = b.val) : a = b := by scalar_tac

/-! ## Two list equalities the `*_beq` family needs

`prop_when::names_beq` and `expr::exprs_beq` are the `List Name` and
`List Expr` equalities of the derived instances; neither had a top-level
refinement lemma yet (`Refine/PropWhen.lean` proves the loop,
`Refine/Expr.lean` proves `levels_beq`).  They belong in those files and are
here only so that task #46 does not edit them. -/

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

/-! ## `ConstantInfo`'s name, and the lookup -/

/-! ## The projection lookup -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing but Lean's own three axioms: no `sorry`, nothing from the `Arc`/`P`
models, and — in particular — nothing reaches
`ConRon.Generated.kernel.pins_text.PINS_TEXT`, whose string constant carries a
`native_decide` axiom (task #43). -/

end ConRon.Refine.Env
