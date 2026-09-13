/-
`CORE_PLAN.md` step 4 (task #49), one of the `CoreK*` family: the **syntactic
readers, shape guards and owning environment probes** of
`crates/con-ron-core/src/kernel/core_k.rs`, against `ConLeche/Kernel/Core.lean`
(with `ConLeche/Kernel/FEnv.lean` supplying the indexed environment and
`ConLeche/Cached/StateC.lean` the `*C` twins, which are the *same* functions on
`ExprC` and are named in each doc comment rather than stated twice).

Twenty-seven functions, in three groups:

* the five **environment probes** (`defn_probe`, `ctor_probe`, `ind_probe`,
  `rec_probe`, `lp_empty`) -- task #14's rule that the index's borrow dies at
  the call boundary, so each is Lean's `ConstantInfo` destructuring returning
  *owned copies*.  Their lemmas therefore carry `FindWF` and conclude the
  well-formedness of what comes back;
* the **guards** that read the environment (`is_ctor_app`, `is_unit_like_ty`
  with `is_punit_ind`/`is_punit_rec_shape`, `unfoldable_head`, `head_hint`,
  `str_expansion_fires`);
* the **pure readers** (`pi_result_is_prop`, `pi_result_z`,
  `pi_result_never_zero`, `caps_never_zero`, `same_const_heads`, `quick_pair`
  with `is_sort`/`is_lit`/`is_forall`/`is_lam_k`, `pw_written`,
  `annot_binder_meta`, `beta_gate_fires`, `fire_is_inert`, `rec_rule_k`).

Four things are worth recording.

**(1) `Env` versus `FEnv`.**  The cited `Core.lean` guards read `env.find?` on
an `Env`; the port reads `fenv::find` on the index (module note deviation 3),
and `CoreKBase.lean`'s `FindAgree` is *find-agreement only* -- it says nothing
about `lfe.env`.  So every environment-reading guard here is stated against the
cited definition's body with `lfe.find?` in place of `env.find?`, spelled out in
the statement: exactly the transposition `FEnv.lean` itself performs for
`natOpGuardF`/`strLitSupportedF` and `Cached/StateC.lean` for
`isCtorAppC`/`headHintC`/`unfoldableHeadC`/`isUnitLikeTyC`.  Nothing is
weakened: those matches *are* the cited functions once `Env.find?` is replaced
by the index lookup they agree with (`mkFEnv_find?`).

**(2) The `env`-module copies.**  A probe's result goes through
`env::constant_val_dup`, `env::ind_caps_dup`, `env::reducibility_hint_dup`,
`env::rec_rules_copy` and `env::to_constant_val`, none of which has a
refinement yet (task #46 owns `Refine/Env.lean`), and neither has
`env::beta_gate`.  The ten lemmas they need are proved locally in the first
section below and **belong in `Refine/Env.lean` on merge**; `reducibility_hint_dup` and `ind_caps_dup` turn out to be the
identity in the model, the other three only preserve the abstraction and the
well-formedness.

**(3) `wf_const_inv`.**  Casing on a node's *kind* (which is what a guard's
`match &f.0.kind` forces) loses the `ExprWF` derivation, so the `.const` arms
need "a well-formed `Const` node has a well-formed name and levels" as a
separate inversion.  It belongs in `Refine/Expr.lean` beside the other
`*_inv`s.

**(4) Pinned names and `str_lit_supported` are hypotheses.**  `punit_name`,
`punit_rec_name` and `string_of_list_name` are being proved in
`CoreKGuards`'s sibling `CoreKNames.lean`, and `core_k::str_lit_supported`
belongs to another agent's file; each is taken here as an explicit hypothesis
of the lemma that needs it, listed in its doc comment, for the parent agent to
discharge at merge.
-/
import ConRon.Refine.CoreKBase

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

/-! ## The `env`-module plumbing the probes need

Ten lemmas about `kernel/env.rs`'s copies and `beta_gate`.  **To be moved to
task #46's `Refine/Env.lean`** (see the file note, point 2). -/

/-- `env::levels_copy` copies a `Vec<Level>`: the same list.  (`expr_ops` has
its own copy loop, already refined; this is `env.rs`'s.) -/
theorem env_levels_copy_from_val (N : Nat) :
    ∀ (us : alloc.vec.Vec level.Level) (i : Std.Usize)
      (out r : alloc.vec.Vec level.Level),
      us.val.length - i.val = N →
      env.levels_copy_from us i out = ok r →
      r.val = out.val ++ us.val.drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro us i out r hN h
    rw [env.levels_copy_from.eq_def] at h
    dsimp only at h
    split at h
    · have hlen : us.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val us; scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]; simp
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, c, hdup, out1, hpush, i2, hi2, hrec⟩ := h
      have hg := ExprOps.vec_index_getElem? hidx
      have hlt : i.val < us.val.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
      have hx : us.val[i.val] = x := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hcx : c = x := Result.ok_injective (hdup.symm.trans (level_dup_eq x))
      subst hcx
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      rw [ih (us.val.length - i2.val) (by omega) us i2 out1 r rfl hrec,
        vec_push_val hpush, hi2v, List.drop_eq_getElem_cons hlt, hx]
      simp

theorem env_levels_copy_val {us r : alloc.vec.Vec level.Level}
    (h : env.levels_copy us = ok r) : r.val = us.val := by
  rw [env.levels_copy] at h
  rw [env_levels_copy_from_val _ us 0#usize _ r rfl h]
  simp [alloc.vec.Vec.with_capacity, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- `env::exprs_copy` copies a `Vec<Expr>`: the same list. -/
theorem env_exprs_copy_from_val (N : Nat) :
    ∀ (es : alloc.vec.Vec expr.Expr) (i : Std.Usize)
      (out r : alloc.vec.Vec expr.Expr),
      es.val.length - i.val = N →
      env.exprs_copy_from es i out = ok r →
      r.val = out.val ++ es.val.drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro es i out r hN h
    rw [env.exprs_copy_from.eq_def] at h
    dsimp only at h
    split at h
    · have hlen : es.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val es; scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]; simp
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, c, hdup, out1, hpush, i2, hi2, hrec⟩ := h
      have hg := ExprOps.vec_index_getElem? hidx
      have hlt : i.val < es.val.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
      have hx : es.val[i.val] = x := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hcx : c = x := Expr.dup_eq hdup
      subst hcx
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      rw [ih (es.val.length - i2.val) (by omega) es i2 out1 r rfl hrec,
        vec_push_val hpush, hi2v, List.drop_eq_getElem_cons hlt, hx]
      simp

theorem env_exprs_copy_val {es r : alloc.vec.Vec expr.Expr}
    (h : env.exprs_copy es = ok r) : r.val = es.val := by
  rw [env.exprs_copy] at h
  rw [env_exprs_copy_from_val _ es 0#usize _ r rfl h]
  simp [alloc.vec.Vec.with_capacity, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- `env::reducibility_hint_dup` is the identity in the model (the `Regular`
arm returns the argument itself). -/
theorem reducibility_hint_dup_eq {h1 r : env.ReducibilityHint}
    (h : env.reducibility_hint_dup h1 = ok r) : r = h1 := by
  cases h1 <;> simp only [env.reducibility_hint_dup, Result.ok.injEq] at h <;>
    exact h.symm

/-- `env::ind_caps_dup` is the identity in the model: `name::dup` and
`prop_when::dup` both are. -/
theorem ind_caps_dup_eq {c r : env.IndCaps} (h : env.ind_caps_dup c = ok r) :
    r = c := by
  rw [env.ind_caps_dup] at h
  simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨pw, hpw, hr⟩ := h
  rw [PropWhen.dup_eq hpw] at hr
  rw [← Result.ok_injective hr]

/-- `env::constant_val_dup` preserves the abstraction and well-formedness. -/
theorem constant_val_dup_abs {cv r : env.ConstantVal}
    (h : env.constant_val_dup cv = ok r) :
    absConstantVal r = absConstantVal cv ∧ (ConstantValWF cv → ConstantValWF r) := by
  rw [env.constant_val_dup] at h
  simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨v, hv, e, he, hr⟩ := h
  have hvv := PropWhen.names_copy_val hv
  have hee := Expr.dup_eq he
  subst hee
  rw [← Result.ok_injective hr]
  refine ⟨?_, ?_⟩
  · simp only [absConstantVal, absNames, hvv]
  · intro ⟨h1, h2, h3⟩
    exact ⟨h1, by intro n hn; exact h2 n (by rw [hvv] at hn; exact hn), h3⟩

/-- `env::rec_rule_fire_dup` preserves the abstraction and well-formedness. -/
theorem rec_rule_fire_dup_abs {f r : env.RecRuleFire}
    (h : env.rec_rule_fire_dup f = ok r) :
    absFire r = absFire f ∧ (RecRuleFireWF f → RecRuleFireWF r) := by
  cases f with
  | Inert => simp only [env.rec_rule_fire_dup, Result.ok.injEq] at h
             subst h; exact ⟨rfl, id⟩
  | Plain => simp only [env.rec_rule_fire_dup, Result.ok.injEq] at h
             subst h; exact ⟨rfl, id⟩
  | Nested lvls pins =>
    simp only [env.rec_rule_fire_dup, bind_eq_ok_iff] at h
    obtain ⟨v, hv, v1, hv1, hr⟩ := h
    have hvv := env_levels_copy_val hv
    have hv1v := env_exprs_copy_val hv1
    rw [← Result.ok_injective hr]
    refine ⟨by simp only [absFire, absLevels, absExprs, hvv, hv1v], ?_⟩
    intro ⟨h1, h2⟩
    exact ⟨by intro u hu; exact h1 u (by rw [hvv] at hu; exact hu),
      by intro e he; exact h2 e (by rw [hv1v] at he; exact he)⟩

/-- `env::rec_rule_dup` preserves the abstraction and well-formedness. -/
theorem rec_rule_dup_abs {rl r : env.RecRule} (h : env.rec_rule_dup rl = ok r) :
    absRecRule r = absRecRule rl ∧ (RecRuleWF rl → RecRuleWF r) := by
  rw [env.rec_rule_dup] at h
  simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨rrf, hrrf, e, he, hr⟩ := h
  obtain ⟨hfabs, hfwf⟩ := rec_rule_fire_dup_abs hrrf
  have hee := Expr.dup_eq he
  subst hee
  rw [← Result.ok_injective hr]
  refine ⟨by simp only [absRecRule, hfabs], ?_⟩
  intro ⟨h1, h2, h3⟩
  exact ⟨h1, hfwf h2, h3⟩

/-- The index recursion behind `env::rec_rules_copy`. -/
theorem rec_rules_copy_from_abs (N : Nat) :
    ∀ (rs : alloc.vec.Vec env.RecRule) (i : Std.Usize)
      (out r : alloc.vec.Vec env.RecRule),
      rs.val.length - i.val = N →
      env.rec_rules_copy_from rs i out = ok r →
      r.val.map absRecRule
          = out.val.map absRecRule ++ (rs.val.drop i.val).map absRecRule ∧
        (RecRulesWF rs → RecRulesWF out → RecRulesWF r) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro rs i out r hN h
    rw [env.rec_rules_copy_from.eq_def] at h
    dsimp only at h
    split at h
    · have hlen : rs.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val rs; scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]
      exact ⟨by simp, fun _ hout => hout⟩
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, c, hdup, out1, hpush, i2, hi2, hrec⟩ := h
      have hg := ExprOps.vec_index_getElem? hidx
      have hlt : i.val < rs.val.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
      have hx : rs.val[i.val] = x := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      obtain ⟨hcabs, hcwf⟩ := rec_rule_dup_abs hdup
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨hrabs, hrwf⟩ :=
        ih (rs.val.length - i2.val) (by omega) rs i2 out1 r rfl hrec
      refine ⟨?_, ?_⟩
      · rw [hrabs, vec_push_val hpush, hi2v, List.drop_eq_getElem_cons hlt, hx]
        simp [hcabs]
      · intro hrs hout
        refine hrwf hrs ?_
        intro w hw
        rw [vec_push_val hpush] at hw
        rcases List.mem_append.mp hw with hw1 | hw1
        · exact hout w hw1
        · have : w = c := by simpa using hw1
          subst this
          exact hcwf (hrs x (by rw [← hx]; exact List.getElem_mem hlt))

/-- `env::rec_rules_copy` preserves the rule list's abstraction and
well-formedness. -/
theorem rec_rules_copy_abs {rs r : alloc.vec.Vec env.RecRule}
    (h : env.rec_rules_copy rs = ok r) :
    absRecRules r = absRecRules rs ∧ (RecRulesWF rs → RecRulesWF r) := by
  rw [env.rec_rules_copy] at h
  obtain ⟨habs, hwf⟩ := rec_rules_copy_from_abs _ rs 0#usize _ r rfl h
  refine ⟨?_, fun hrs => hwf hrs ?_⟩
  · rw [absRecRules, habs]
    simp [alloc.vec.Vec.with_capacity, absRecRules,
      show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
  · intro w hw; simp [alloc.vec.Vec.with_capacity] at hw

/-- `env::to_constant_val`, in the one component every caller here reads: the
level-parameter list.  (The `name`/`ty` components need
`CoreKBase.proj_table_name_refines` and hence `NameWF`; nothing below asks for
them, so this WF-free half is all that is stated.) -/
theorem to_constant_val_lp {ci : env.ConstantInfo} {cv : env.ConstantVal}
    (h : env.to_constant_val ci = ok cv) :
    absNames cv.level_params = (absConstantInfo ci).toConstantVal.levelParams := by
  cases ci with
  | AxiomInfo v | DefnInfo v _ _ | ThmInfo v _ | IndInfo v _ | CtorInfo v _ _
  | RecInfo v _ _ _ =>
    rw [env.to_constant_val] at h
    have := (constant_val_dup_abs h).1
    simpa [absConstantInfo, absConstantVal, ConLeche.ConstantInfo.toConstantVal]
      using congrArg ConLeche.ConstantVal.levelParams this
  | ProjInfo tbl =>
    rw [env.to_constant_val] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨n, -, v, hv, l, -, l1, -, e, -, hcv⟩ := h
    rw [← Result.ok_injective hcv]
    simp only [absConstantInfo, absProjTable, ConLeche.ConstantInfo.toConstantVal,
      absNames, PropWhen.names_copy_val hv]

/-- `env::beta_gate` refines `CheckMode.betaGate` (`Env.lean:119`). -/
theorem beta_gate_refines {m : env.CheckMode} {b : Bool}
    (h : env.beta_gate m = ok b) : b = (absMode m).betaGate := by
  cases m <;> simp only [env.beta_gate, Result.ok.injEq] at h <;>
    rw [← h] <;> rfl

/-! ## A missing `Expr` inversion

**To be moved to `Refine/Expr.lean`** beside the other `*_inv` lemmas (see the
file note, point 3). -/

/-- A well-formed `Const` node has a well-formed name and level list: the
inversion a `match &f.0.kind` arm needs, since casing on the kind throws the
`ExprWF` derivation away. -/
theorem wf_const_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {n : name.Name} {us : alloc.vec.Vec level.Level}
    (hk : e = .mk (.mk d (.Const n us))) : NameWF n ∧ LevelsWF us := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u _ _ h1 => obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; simp at hk
  | @mk_const n1 us1 _ hn hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.Const.injEq] at hk
    obtain ⟨-, rfl, rfl⟩ := hk
    exact ⟨hn, hus⟩
  | @app f a _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp at hk
  | @lam ty bo m _ _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; simp at hk
  | @forall_e ty bo m _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; simp at hk
  | @let_e ty v bo _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk


/-- A well-formed `Sort` node has a well-formed level. -/
theorem wf_sort_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64} {u : level.Level}
    (hk : e = .mk (.mk d (.Sort u))) : LevelWF u := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u1 _ hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.Sort.injEq] at hk
    obtain ⟨-, rfl⟩ := hk
    exact hu
  | @mk_const n1 us1 _ _ _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; simp at hk
  | @app f a _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp at hk
  | @lam ty bo m _ _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; simp at hk
  | @forall_e ty bo m _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; simp at hk
  | @let_e ty v bo _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk

/-- A well-formed `App` node has well-formed parts. -/
theorem wf_app_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64} {f a : expr.Expr}
    (hk : e = .mk (.mk d (.App f a))) : ExprWF f ∧ ExprWF a := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u1 _ _ h1 => obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; simp at hk
  | @mk_const n1 us1 _ _ _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; simp at hk
  | @app f1 a1 _ hf ha h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.App.injEq] at hk
    obtain ⟨-, rfl, rfl⟩ := hk
    exact ⟨hf, ha⟩
  | @lam ty bo m _ _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; simp at hk
  | @forall_e ty bo m _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; simp at hk
  | @let_e ty v bo _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk

/-! ## The four owning environment probes (`Core.lean`'s `ConstantInfo` destructurings)

Task #14's probe rule: the index's borrow dies at the call boundary, so each
probe returns *owned copies* of the pattern variables Lean's value semantics
hands its `match`.  Each lemma therefore takes `FindWF` and concludes the
well-formedness of what came back.  The Lean side is the destructuring itself,
named below. -/

/-- `some (.defnInfo cv value hint)`, as a function of the lookup. -/
def defnOf : Option ConLeche.ConstantInfo →
    Option (ConLeche.ConstantVal × ConLeche.Expr × ConLeche.ReducibilityHint)
  | some (.defnInfo cv v h) => some (cv, v, h)
  | _ => none

/-- `some (.ctorInfo cv cnP cnF)`, as a function of the lookup. -/
def ctorOf : Option ConLeche.ConstantInfo →
    Option (ConLeche.ConstantVal × Nat × Nat)
  | some (.ctorInfo cv nP nF) => some (cv, nP, nF)
  | _ => none

/-- `some (.indInfo cvT caps)`, as a function of the lookup. -/
def indOf : Option ConLeche.ConstantInfo →
    Option (ConLeche.ConstantVal × ConLeche.IndCaps)
  | some (.indInfo cv c) => some (cv, c)
  | _ => none

/-- `some (.recInfo cv mI rP rules)`, as a function of the lookup. -/
def recOf : Option ConLeche.ConstantInfo →
    Option (ConLeche.ConstantVal × Nat × Nat × List ConLeche.RecRule)
  | some (.recInfo cv mI rP rs) => some (cv, mI, rP, rs)
  | _ => none

/-- **`core_k::defn_probe`** (`Core.lean:208-227 unfoldDefinition`,
`:244-253 headHint`): the `some (.defnInfo cv value hint)` destructuring of the
indexed lookup, with owned copies. -/
theorem defn_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {o : Option (env.ConstantVal × expr.Expr × env.ReducibilityHint)}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (hn : NameWF n)
    (h : core_k.defn_probe fe n = ok o) :
    o.map (fun t => (absConstantVal t.1, absExpr t.2.1, absHint t.2.2))
        = defnOf (lfe.find? (absName n)) ∧
      ∀ cv v hint, o = some (cv, v, hint) → ConstantValWF cv ∧ ExprWF v := by
  rw [core_k.defn_probe] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ov, hov, h⟩ := h
  cases ov with
  | none =>
    rw [hfe.find_none hn hov]
    simp only [Result.ok.injEq] at h; subst h
    exact ⟨rfl, by simp⟩
  | some ci =>
    have hlf := hfe.find_some hn hov
    have hciwf := hwf n ci hn hov
    cases ci with
    | DefnInfo cv v hint =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨cv1, hcv1, e, he, rh, hrh, ho⟩ := h
      obtain ⟨hcvabs, hcvwf⟩ := constant_val_dup_abs hcv1
      have hee := Expr.dup_eq he
      have hrr := reducibility_hint_dup_eq hrh
      subst hee; subst hrr
      rw [← Result.ok_injective ho, hlf]
      obtain ⟨hw1, hw2⟩ := hciwf
      refine ⟨by simp [defnOf, absConstantInfo, hcvabs], ?_⟩
      intro cv2 v2 h2 heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, -⟩ := heq
      exact ⟨hcvwf hw1, hw2⟩
    | AxiomInfo _ | ThmInfo _ _ | IndInfo _ _ | CtorInfo _ _ _
    | RecInfo _ _ _ _ | ProjInfo _ =>
      simp only [Result.ok.injEq] at h; subst h
      rw [hlf]; exact ⟨rfl, by simp⟩

/-- **`core_k::ctor_probe`** (`Core.lean:1274-1456 majorToCtor`,
`:1029-1101 structEtaCertWith`): the `some (.ctorInfo cv cnP cnF)`
destructuring. -/
theorem ctor_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {o : Option (env.ConstantVal × Std.U64 × Std.U64)}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (hn : NameWF n)
    (h : core_k.ctor_probe fe n = ok o) :
    o.map (fun t => (absConstantVal t.1, t.2.1.val, t.2.2.val))
        = ctorOf (lfe.find? (absName n)) ∧
      ∀ cv nP nF, o = some (cv, nP, nF) → ConstantValWF cv := by
  rw [core_k.ctor_probe] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ov, hov, h⟩ := h
  cases ov with
  | none =>
    rw [hfe.find_none hn hov]
    simp only [Result.ok.injEq] at h; subst h
    exact ⟨rfl, by simp⟩
  | some ci =>
    have hlf := hfe.find_some hn hov
    have hciwf := hwf n ci hn hov
    cases ci with
    | CtorInfo cv nP nF =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨cv1, hcv1, ho⟩ := h
      obtain ⟨hcvabs, hcvwf⟩ := constant_val_dup_abs hcv1
      rw [← Result.ok_injective ho, hlf]
      refine ⟨by simp [ctorOf, absConstantInfo, hcvabs], ?_⟩
      intro cv2 a b heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, -, -⟩ := heq
      exact hcvwf hciwf
    | AxiomInfo _ | DefnInfo _ _ _ | ThmInfo _ _ | IndInfo _ _
    | RecInfo _ _ _ _ | ProjInfo _ =>
      simp only [Result.ok.injEq] at h; subst h
      rw [hlf]; exact ⟨rfl, by simp⟩

/-- **`core_k::ind_probe`** (`Core.lean:1274-1456 majorToCtor`,
`:1029-1101 structEtaCertWith`): the `some (.indInfo cvT caps)`
destructuring. -/
theorem ind_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {o : Option (env.ConstantVal × env.IndCaps)}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (hn : NameWF n)
    (h : core_k.ind_probe fe n = ok o) :
    o.map (fun t => (absConstantVal t.1, absIndCaps t.2))
        = indOf (lfe.find? (absName n)) ∧
      ∀ cv c, o = some (cv, c) → ConstantValWF cv ∧ IndCapsWF c := by
  rw [core_k.ind_probe] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ov, hov, h⟩ := h
  cases ov with
  | none =>
    rw [hfe.find_none hn hov]
    simp only [Result.ok.injEq] at h; subst h
    exact ⟨rfl, by simp⟩
  | some ci =>
    have hlf := hfe.find_some hn hov
    have hciwf := hwf n ci hn hov
    cases ci with
    | IndInfo cv caps =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨cv1, hcv1, ic, hic, ho⟩ := h
      obtain ⟨hcvabs, hcvwf⟩ := constant_val_dup_abs hcv1
      have hicc := ind_caps_dup_eq hic
      subst hicc
      rw [← Result.ok_injective ho, hlf]
      obtain ⟨hw1, hw2⟩ := hciwf
      refine ⟨by simp [indOf, absConstantInfo, hcvabs], ?_⟩
      intro cv2 c2 heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨hcvwf hw1, hw2⟩
    | AxiomInfo _ | DefnInfo _ _ _ | ThmInfo _ _ | CtorInfo _ _ _
    | RecInfo _ _ _ _ | ProjInfo _ =>
      simp only [Result.ok.injEq] at h; subst h
      rw [hlf]; exact ⟨rfl, by simp⟩

/-- **`core_k::rec_probe`** (`Core.lean:1682-1795 iotaRec`,
`:975-998 structEtaProjCerts`): the `some (.recInfo cv mI rP rules)`
destructuring, with the rule list copied spine-wise. -/
theorem rec_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {o : Option (env.ConstantVal × Std.U64 × Std.U64 × alloc.vec.Vec env.RecRule)}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (hn : NameWF n)
    (h : core_k.rec_probe fe n = ok o) :
    o.map (fun t => (absConstantVal t.1, t.2.1.val, t.2.2.1.val, absRecRules t.2.2.2))
        = recOf (lfe.find? (absName n)) ∧
      ∀ cv mI rP rs, o = some (cv, mI, rP, rs) → ConstantValWF cv ∧ RecRulesWF rs := by
  rw [core_k.rec_probe] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ov, hov, h⟩ := h
  cases ov with
  | none =>
    rw [hfe.find_none hn hov]
    simp only [Result.ok.injEq] at h; subst h
    exact ⟨rfl, by simp⟩
  | some ci =>
    have hlf := hfe.find_some hn hov
    have hciwf := hwf n ci hn hov
    cases ci with
    | RecInfo cv mI rP rules =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨cv1, hcv1, v, hv, ho⟩ := h
      obtain ⟨hcvabs, hcvwf⟩ := constant_val_dup_abs hcv1
      obtain ⟨hrabs, hrwf⟩ := rec_rules_copy_abs hv
      rw [← Result.ok_injective ho, hlf]
      obtain ⟨hw1, hw2⟩ := hciwf
      refine ⟨by simpa [recOf, absConstantInfo, hcvabs, absRecRules] using hrabs, ?_⟩
      intro cv2 a b rs2 heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, -, -, rfl⟩ := heq
      exact ⟨hcvwf hw1, hrwf hw2⟩
    | AxiomInfo _ | DefnInfo _ _ _ | ThmInfo _ _ | IndInfo _ _
    | CtorInfo _ _ _ | ProjInfo _ =>
      simp only [Result.ok.injEq] at h; subst h
      rw [hlf]; exact ⟨rfl, by simp⟩

/-- **`core_k::lp_empty`** (`Core.lean:656-672 natOpGuard`,
`FEnv.lean:132-145 natOpGuardF`): the level-monomorphism test
`match fe.find? n with | some ci => ci.toConstantVal.levelParams.isEmpty
| none => false`, as its own function so the index's borrow ends there.
No `FindWF` is needed -- the only component read is the level-parameter list,
which `env::to_constant_val` copies verbatim at every arm. -/
theorem lp_empty_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {b : Bool} (hfe : FindAgree fe lfe) (hn : NameWF n)
    (h : core_k.lp_empty fe n = ok b) :
    b = (match lfe.find? (absName n) with
         | some ci => ci.toConstantVal.levelParams.isEmpty
         | none => false) := by
  rw [core_k.lp_empty] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ov, hov, h⟩ := h
  cases ov with
  | none =>
    rw [hfe.find_none hn hov]
    simp only [Result.ok.injEq] at h; exact h.symm
  | some ci =>
    rw [hfe.find_some hn hov]
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv, hcv, hb⟩ := h
    have hlp := to_constant_val_lp hcv
    rw [← hb]
    have hlen : (absConstantInfo ci).toConstantVal.levelParams.length
        = cv.level_params.val.length := by
      rw [← hlp]; simp [absNames]
    have hiff : (absConstantInfo ci).toConstantVal.levelParams.isEmpty
        = decide (cv.level_params.val.length = 0) := by
      rw [← hlen]
      rcases (absConstantInfo ci).toConstantVal.levelParams with _ | ⟨x, xs⟩ <;> simp
    simp only [hiff]
    have hv := alloc.vec.Vec.len_val cv.level_params
    simp only [decide_eq_decide]
    constructor <;> intro hz <;> scalar_tac


/-! ## The one-constructor tests and `quick_pair` (`Core.lean:531-543`)

`Expr.quickPair` is the only cited definition here: Rust has no `.sort _`
pattern outside a `match`, so each slot of the cited pair is a named function
(`Core.lean`'s note).  Each therefore gets the arm of `quickPair` it computes. -/

/-- **`core_k::is_sort`** (`Core.lean:531-543 Expr.quickPair`). -/
theorem is_sort_refines {e : expr.Expr} {b : Bool} (h : core_k.is_sort e = ok b) :
    b = (match absExpr e with | .sort _ => true | _ => false) := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [core_k.is_sort.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
  cases k <;> simp only [Result.ok.injEq] at h <;> rw [← h] <;> simp

/-- **`core_k::is_lit`** (`Core.lean:531-543 Expr.quickPair`). -/
theorem is_lit_refines {e : expr.Expr} {b : Bool} (h : core_k.is_lit e = ok b) :
    b = (match absExpr e with | .lit _ => true | _ => false) := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [core_k.is_lit.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
  cases k <;> simp only [Result.ok.injEq] at h <;> rw [← h] <;> simp

/-- **`core_k::is_forall`** (`Core.lean:531-543 Expr.quickPair`). -/
theorem is_forall_refines {e : expr.Expr} {b : Bool} (h : core_k.is_forall e = ok b) :
    b = (match absExpr e with | .forallE .. => true | _ => false) := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [core_k.is_forall.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
  cases k <;> simp only [Result.ok.injEq] at h <;> rw [← h] <;> simp

/-- **`core_k::is_lam_k`** (`Core.lean:531-543 Expr.quickPair`).  (`is_lam_k`,
not `is_lam`: `expr_ops::is_lam` is `Expr.isLam`, a different declaration.) -/
theorem is_lam_k_refines {e : expr.Expr} {b : Bool} (h : core_k.is_lam_k e = ok b) :
    b = (match absExpr e with | .lam .. => true | _ => false) := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [core_k.is_lam_k.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
  cases k <;> simp only [Result.ok.injEq] at h <;> rw [← h] <;> simp

/-- **`core_k::quick_pair` refines `Expr.quickPair`** (`Core.lean:531-543`).
Charon expands the cited wildcard arm (task #11's note), so the port's first
`match` has all ten arms; four of them delegate to the one-constructor tests
above. -/
theorem quick_pair_refines {a b : expr.Expr} {c : Bool}
    (h : core_k.quick_pair a b = ok c) :
    c = ConLeche.Expr.quickPair (absExpr a) (absExpr b) := by
  obtain ⟨⟨d, k⟩⟩ := a
  rw [core_k.quick_pair.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
  cases k with
  | «Sort» u =>
    rw [is_sort_refines h]
    simp only [absExpr_mk, absExprKind]
    generalize absExpr b = x
    cases x <;> simp [ConLeche.Expr.quickPair]
  | Lit l =>
    rw [is_lit_refines h]
    simp only [absExpr_mk, absExprKind]
    generalize absExpr b = x
    cases x <;> simp [ConLeche.Expr.quickPair]
  | ForallE ty bo m =>
    rw [is_forall_refines h]
    simp only [absExpr_mk, absExprKind]
    generalize absExpr b = x
    cases x <;> simp [ConLeche.Expr.quickPair]
  | Lam ty bo m =>
    rw [is_lam_k_refines h]
    simp only [absExpr_mk, absExprKind]
    generalize absExpr b = x
    cases x <;> simp [ConLeche.Expr.quickPair]
  | _ =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    simp only [absExpr_mk, absExprKind]
    generalize absExpr b = x
    cases x <;> simp [ConLeche.Expr.quickPair]

/-! ## The remaining pure readers -/

/-- **`core_k::rec_rule_k` refines `recRuleK`** (`Core.lean:1612-1619`): the
stored `k` bit of the recursor's single rule.  The cited `[rl]` pattern is
`rules.len() == 1`. -/
theorem rec_rule_k_refines {rules : alloc.vec.Vec env.RecRule} {b : Bool}
    (h : core_k.rec_rule_k rules = ok b) :
    b = ConLeche.recRuleK (absRecRules rules) := by
  rw [core_k.rec_rule_k] at h
  have hv := alloc.vec.Vec.len_val rules
  split at h
  · rename_i hlen
    have hl : rules.val.length = 1 := by scalar_tac
    obtain ⟨r0, hrv⟩ := List.length_eq_one_iff.mp hl
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨rr, hidx, hb⟩ := h
    have hg := ExprOps.vec_index_getElem? hidx
    rw [hrv] at hg
    simp only [show ((0#usize : Std.Usize)).val = 0 from rfl,
      List.getElem?_cons_zero, Option.some.injEq] at hg
    rw [← hb, ← hg]
    simp [absRecRules, hrv, ConLeche.recRuleK, absRecRule]
  · rename_i hlen
    have hl : rules.val.length ≠ 1 := by
      intro hc; exact hlen (by scalar_tac)
    rw [← Result.ok_injective h]
    rcases hrv : rules.val with _ | ⟨x, xs⟩
    · simp [absRecRules, hrv, ConLeche.recRuleK]
    · rcases xs with _ | ⟨y, ys⟩
      · rw [hrv] at hl; simp at hl
      · simp [absRecRules, hrv, ConLeche.recRuleK]

/-- **`core_k::fire_is_inert`** (`Env.lean:203-247 RecRuleFire`,
`Core.lean:1682-1795 iotaRec`): the cited `rl.fire = .inert` test.  §3.4 keeps
`derive` off the core types, so the port has no equality on the enum and the
test is a one-arm match. -/
theorem fire_is_inert_refines {f : env.RecRuleFire} {b : Bool}
    (h : core_k.fire_is_inert f = ok b) :
    b = (match absFire f with | .inert => true | _ => false) := by
  cases f <;> simp only [core_k.fire_is_inert, Result.ok.injEq] at h <;>
    rw [← h] <;> rfl

/-- **`core_k::beta_gate_fires` refines `betaGateFires`**
(`Core.lean:1859-1891`) -- the β site's gate, mode and datum only.
**Deliberately dead but ported** (the `whnfCore` β arm reads the gate through
`cached/core_c.rs`), so this lemma has no consumer either; the port carries it
so the provenance gate stays in step with its source. -/
theorem beta_gate_fires_refines {mode : env.CheckMode} {pw : prop_when.PropWhen}
    {b : Bool} (h : core_k.beta_gate_fires mode pw = ok b) :
    b = ConLeche.betaGateFires (absMode mode) (absPropWhen pw) := by
  rw [core_k.beta_gate_fires] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨bg, hbg, h⟩ := h
  rw [ConLeche.betaGateFires, ← beta_gate_refines hbg]
  split at h
  · rename_i hc
    rw [PropWhen.is_never_refines h, hc]
    simp
  · rename_i hc
    simp only [Bool.not_eq_true] at hc
    rw [← Result.ok_injective h, hc]
    simp

/-- **`core_k::pw_written` refines `pwWritten`** (`Core.lean:2676-2677`): is
this datum a real (non-placeholder) input annotation?  The cited `!pw.isNever`
is an `if` nest -- a `!` in a *value* position is Lean's propositional `¬` in
the model (the port's note on `defeq_lits`). -/
theorem pw_written_refines {pw : prop_when.PropWhen} {b : Bool}
    (h : core_k.pw_written pw = ok b) :
    b = ConLeche.pwWritten (absPropWhen pw) := by
  rw [core_k.pw_written] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨c, hc, h⟩ := h
  rw [ConLeche.pwWritten, ← PropWhen.is_never_refines hc]
  split at h
  · rename_i hc2
    rw [← Result.ok_injective h, hc2]; simp
  · rename_i hc2
    simp only [Bool.not_eq_true] at hc2
    rw [← Result.ok_injective h, hc2]; simp


/-! ## The `piResult` readers (`Core.lean:127-167`)

All three read the *syntactic* pi telescope through `expr_ops::pi_result`, whose
refinement (`ExprOpsSpine.lean`) supplies both the abstraction and the result's
well-formedness -- which is what the `Sort` arms' `LevelWF` comes from. -/

/-- **`core_k::pi_result_is_prop` refines `piResultIsProp`**
(`Core.lean:127-134`): does the syntactic pi telescope end in a normalized
`Prop`?  The cited `Level.isEquiv u .zero == some true` is the port's
three-arm match on the `Option Bool`. -/
theorem pi_result_is_prop_refines {e : expr.Expr} {b : Bool} (he : ExprWF e)
    (h : core_k.pi_result_is_prop e = ok b) :
    b = ConLeche.piResultIsProp (absExpr e) := by
  rw [core_k.pi_result_is_prop] at h
  simp only [arc_deref_eq, bind_tc_ok] at h
  obtain ⟨pr, hpr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hprwf⟩ := ExprOps.pi_result_refines he hpr
  rw [ConLeche.piResultIsProp, ← habs]
  obtain ⟨⟨d, k⟩⟩ := pr
  simp only [ExprOps.node_kind] at h
  cases k with
  | «Sort» u =>
    have huwf : LevelWF u := wf_sort_inv hprwf rfl
    simp only [bind_eq_ok_iff] at h
    obtain ⟨l, hl, o, ho, h⟩ := h
    have hlwf : LevelWF l := LevelWF.zero hl
    have heq := Level.is_equiv_refines huwf hlwf ho
    rw [Level.zero_refines hl] at heq
    simp only [absExpr_mk, absExprKind, heq]
    cases o with
    | none => simp only [Result.ok.injEq] at h; rw [← h]; simp
    | some bo =>
      cases bo <;> simp only [Bool.false_eq_true, if_false, if_true,
        Result.ok.injEq] at h <;> rw [← h] <;> simp
  | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp

/-- **`core_k::pi_result_z` refines `piResultZ`** (`Core.lean:136-144`): the
result-sort zero-ness datum of an inductive's type (`IndCaps.sortZ`).  A
telescope that does not end in a sort gets `ifAllZero []`. -/
theorem pi_result_z_refines {e : expr.Expr} {r : prop_when.PropWhen} (he : ExprWF e)
    (h : core_k.pi_result_z e = ok r) :
    absPropWhen r = ConLeche.piResultZ (absExpr e) ∧ PropWhenWF r := by
  rw [core_k.pi_result_z] at h
  simp only [arc_deref_eq, bind_tc_ok] at h
  obtain ⟨pr, hpr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hprwf⟩ := ExprOps.pi_result_refines he hpr
  rw [ConLeche.piResultZ, ← habs]
  obtain ⟨⟨d, k⟩⟩ := pr
  simp only [ExprOps.node_kind] at h
  have hnew : NamesWF (alloc.vec.Vec.new name.Name) := by
    intro n hn; simp [alloc.vec.Vec.new] at hn
  cases k with
  | «Sort» u =>
    have huwf : LevelWF u := wf_sort_inv hprwf rfl
    obtain ⟨hz, hzwf⟩ := ExprOps.zeroness_of_refines huwf r h
    exact ⟨by simp only [absExpr_mk, absExprKind]; exact hz, hzwf⟩
  | _ =>
    refine ⟨?_, PropWhen.if_all_zero_wf hnew h⟩
    rw [PropWhen.if_all_zero_refines hnew h]
    simp [absNames, alloc.vec.Vec.new]

/-- **`core_k::pi_result_never_zero` refines `piResultNeverZero`**
(`Core.lean:146-154`) -- the dead *specification* of `caps_never_zero`: the walk
down the family's type that the stored datum replaces.  Nothing executable calls
it; it is ported so the provenance gate stays in step with its source (task
#11's `beqRecursive` rule). -/
theorem pi_result_never_zero_refines {lps : alloc.vec.Vec name.Name}
    {us : alloc.vec.Vec level.Level} {e : expr.Expr} {b : Bool}
    (hlps : NamesWF lps) (hus : LevelsWF us) (he : ExprWF e)
    (h : core_k.pi_result_never_zero lps us e = ok b) :
    b = ConLeche.piResultNeverZero (absNames lps) (absLevels us) (absExpr e) := by
  rw [core_k.pi_result_never_zero] at h
  simp only [arc_deref_eq, bind_tc_ok] at h
  obtain ⟨pr, hpr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hprwf⟩ := ExprOps.pi_result_refines he hpr
  rw [ConLeche.piResultNeverZero, ← habs]
  obtain ⟨⟨d, k⟩⟩ := pr
  simp only [ExprOps.node_kind] at h
  cases k with
  | «Sort» u =>
    have huwf : LevelWF u := wf_sort_inv hprwf rfl
    simp only [bind_eq_ok_iff] at h
    obtain ⟨l, hl, hb⟩ := h
    obtain ⟨hlabs, -⟩ := Level.subst_refines huwf hlps hus hl
    rw [Level.is_never_zero_refines hb, hlabs]
    simp [absExpr_mk, absExprKind, absNames, absLevels]
  | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp

/-- **`core_k::caps_never_zero` refines `capsNeverZero`**
(`Core.lean:156-167`): is a stored inductive's result sort, at the given level
instantiation, provably nonzero?  Read off the stored datum. -/
theorem caps_never_zero_refines {lps : alloc.vec.Vec name.Name}
    {us : alloc.vec.Vec level.Level} {caps : env.IndCaps} {b : Bool}
    (hlps : NamesWF lps) (hus : LevelsWF us) (hc : IndCapsWF caps)
    (h : core_k.caps_never_zero lps us caps = ok b) :
    b = ConLeche.capsNeverZero (absNames lps) (absLevels us) (absIndCaps caps) := by
  rw [core_k.caps_never_zero] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨pw, hpw, h⟩ := h
  obtain ⟨hpwabs, -⟩ := ExprOps.subst_pw_refines hlps hus hc.2 hpw
  rw [PropWhen.is_never_refines h, hpwabs, ConLeche.capsNeverZero]
  rfl

/-- **`core_k::same_const_heads` refines `sameConstHeads`**
(`Core.lean:255-264`; `Cached/StateC.lean:89-96 sameConstHeadsC` is the same
function on `ExprC`): the lazy-delta same-head short-circuit.  Both sides must
actually be applications. -/
theorem same_const_heads_refines {a b : expr.Expr} {c : Bool}
    (ha : ExprWF a) (hb : ExprWF b) (h : core_k.same_const_heads a b = ok c) :
    c = ConLeche.sameConstHeads (absExpr a) (absExpr b) := by
  obtain ⟨⟨da, ka⟩⟩ := a
  obtain ⟨⟨db, kb⟩⟩ := b
  rw [core_k.same_const_heads.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
  cases ka with
  | App f1 a1 =>
    cases kb with
    | App f2 a2 =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨g1, hg1, g2, hg2, h⟩ := h
      obtain ⟨hf1, -⟩ := wf_app_inv ha rfl
      obtain ⟨hf2, -⟩ := wf_app_inv hb rfl
      obtain ⟨habs1, hw1⟩ := ExprOps.get_app_fn_refines hf1 hg1
      obtain ⟨habs2, hw2⟩ := ExprOps.get_app_fn_refines hf2 hg2
      simp only [absExpr_mk, absExprKind, ConLeche.sameConstHeads, ← habs1, ← habs2]
      obtain ⟨⟨d1, k1⟩⟩ := g1
      obtain ⟨⟨d2, k2⟩⟩ := g2
      simp only [ExprOps.node_kind] at h
      cases k1 with
      | Const n1 us1 =>
        cases k2 with
        | Const n2 us2 =>
          rw [Name.beq_refines (wf_const_inv hw1 rfl).1 (wf_const_inv hw2 rfl).1 h]
          by_cases hne : absName n1 = absName n2 <;> simp [hne]
        | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
      | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
    | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.sameConstHeads]
  | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.sameConstHeads]

/-- **`core_k::annot_binder_meta` refines `annotBinderMeta`**
(`Core.lean:2679-2685`; `Cached/CoreC.lean:1643-1647 annotBinderMetaI` is the
same function under a `pure`): the datum a rebuilt binder ends up with -- the
one threaded in from the node below, unless it carries a real input annotation.
Nothing in `core_k.rs` calls it; the interned pass is its consumer. -/
theorem annot_binder_meta_refines {pw : Option prop_when.PropWhen}
    {mb r : expr.BinderMeta} (hpw : ∀ p, pw = some p → PropWhenWF p)
    (hmb : BinderMetaWF mb) (h : core_k.annot_binder_meta pw mb = ok r) :
    absBinderMeta r = ConLeche.annotBinderMeta (pw.map absPropWhen) (absBinderMeta mb)
      ∧ BinderMetaWF r := by
  rw [core_k.annot_binder_meta.eq_def] at h
  cases pw with
  | none =>
    rw [expr.binder_meta_dup] at h
    simp only [ptr_clone_eq, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]
    exact ⟨rfl, hmb⟩
  | some p =>
    simp only [arc_deref_eq, bind_tc_ok, bind_eq_ok_iff] at h
    obtain ⟨bw, hbw, h⟩ := h
    rw [ConLeche.annotBinderMeta.eq_def]
    simp only [Option.map_some, absBinderMeta, ← pw_written_refines hbw]
    split at h
    · rename_i hc
      rw [expr.binder_meta_dup] at h
      simp only [ptr_clone_eq, bind_tc_ok, Result.ok.injEq] at h
      rw [← h, hc]
      exact ⟨by simp, hmb⟩
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      rw [ExprOps.binder_meta_eq] at h
      rw [← Result.ok_injective h, hc]
      exact ⟨by simp, hpw p rfl⟩


/-! ## The environment-reading guards

Each is stated against the cited `Core.lean` definition's body with `lfe.find?`
in place of `env.find?` (file note, point 1); the `Cached/StateC.lean` twin
named in each doc comment is that same body on `ExprC`. -/

/-- **`core_k::is_ctor_app` refines `isCtorApp`** (`Core.lean:118-125`;
`Cached/StateC.lean:62-69 isCtorAppC` is the same function on `ExprC`): is the
expression headed by a stored constructor? -/
theorem is_ctor_app_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {e : expr.Expr}
    {b : Bool} (hfe : FindAgree fe lfe) (he : ExprWF e)
    (h : core_k.is_ctor_app fe e = ok b) :
    b = (match (absExpr e).getAppFn with
         | .const c _ =>
           (match lfe.find? c with
            | some (.ctorInfo _ _ _) => true
            | _ => false)
         | _ => false) := by
  rw [core_k.is_ctor_app] at h
  simp only [arc_deref_eq, bind_tc_ok] at h
  obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hfwf⟩ := ExprOps.get_app_fn_refines he hf
  rw [← habs]
  obtain ⟨⟨d, k⟩⟩ := f
  simp only [ExprOps.node_kind] at h
  cases k with
  | Const c us =>
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hcwf := (wf_const_inv hfwf rfl).1
    simp only [absExpr_mk, absExprKind]
    cases o with
    | none =>
      rw [hfe.find_none hcwf ho]
      simp only [Result.ok.injEq] at h
      rw [← h]
    | some ci =>
      rw [hfe.find_some hcwf ho]
      cases ci <;>
        simp only [core_k.is_ctor_info, Result.ok.injEq] at h <;>
        rw [← h] <;> simp [absConstantInfo]
  | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp

/-- **`core_k::unfoldable_head` refines `unfoldableHead`**
(`Core.lean:229-242`; `Cached/StateC.lean:80-87 unfoldableHeadC` is the same
function on `ExprC`): may the delta step unfold `e`'s head?  The *decision* the
lazy delta step takes. -/
theorem unfoldable_head_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {e : expr.Expr} {b : Bool} (hfe : FindAgree fe lfe) (he : ExprWF e)
    (h : core_k.unfoldable_head fe e = ok b) :
    b = (match (absExpr e).getAppFn with
         | .const n us =>
           (match lfe.find? n with
            | some (.defnInfo cv _ _) => us.length == cv.levelParams.length
            | _ => false)
         | _ => false) := by
  rw [core_k.unfoldable_head] at h
  simp only [arc_deref_eq, bind_tc_ok] at h
  obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hfwf⟩ := ExprOps.get_app_fn_refines he hf
  rw [← habs]
  obtain ⟨⟨d, k⟩⟩ := f
  simp only [ExprOps.node_kind] at h
  cases k with
  | Const n us =>
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hcwf := (wf_const_inv hfwf rfl).1
    simp only [absExpr_mk, absExprKind]
    cases o with
    | none =>
      rw [hfe.find_none hcwf ho]
      simp only [Result.ok.injEq] at h
      rw [← h]
    | some ci =>
      rw [hfe.find_some hcwf ho]
      cases ci with
      | DefnInfo cv v hint =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        simp only [absConstantInfo, absConstantVal, absLevels, absNames, List.length_map]
        have hv1 := alloc.vec.Vec.len_val us
        have hv2 := alloc.vec.Vec.len_val cv.level_params
        by_cases hq : us.val.length = cv.level_params.val.length
        · have he1 : alloc.vec.Vec.len us = alloc.vec.Vec.len cv.level_params := by
            scalar_tac
          rw [he1]; simp [hq]
        · have he1 : alloc.vec.Vec.len us ≠ alloc.vec.Vec.len cv.level_params := by
            intro hc; exact hq (by scalar_tac)
          simp [he1, hq]
      | _ =>
        simp only [Result.ok.injEq] at h
        rw [← h]; simp [absConstantInfo]
  | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp

/-- The cited `headHint`'s inner match, named so the statement of
`head_hint_refines` can be read off `Core.lean:244-253` without repeating it. -/
def hintOf : Option ConLeche.ConstantInfo → ConLeche.ReducibilityHint
  | some (.defnInfo _ _ hint) => hint
  | _ => .opaque

/-- `hintOf` through `defnOf`: what `defn_probe_refines` hands over. -/
theorem hintOf_defnOf (X : Option ConLeche.ConstantInfo) :
    hintOf X = ((defnOf X).map (fun t => t.2.2)).getD .opaque := by
  rcases X with _ | ci
  · rfl
  · cases ci <;> rfl

/-- **`core_k::head_hint` refines `headHint`** (`Core.lean:244-253`;
`Cached/StateC.lean:71-78 headHintC` is the same function on `ExprC`): the
reducibility hint of the constant at the head of `e`, `opaque` when the head is
not a stored definition (a theorem included).  `FindWF` is here only because the
port routes the lookup through `defn_probe`, whose lemma concludes the copies'
well-formedness; a `ReducibilityHint` itself holds no term. -/
theorem head_hint_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {e : expr.Expr}
    {r : env.ReducibilityHint} (hfe : FindAgree fe lfe) (hwf : FindWF fe)
    (he : ExprWF e) (h : core_k.head_hint fe e = ok r) :
    absHint r = (match (absExpr e).getAppFn with
                 | .const n _ => hintOf (lfe.find? n)
                 | _ => .opaque) := by
  rw [core_k.head_hint] at h
  simp only [arc_deref_eq, bind_tc_ok] at h
  obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hfwf⟩ := ExprOps.get_app_fn_refines he hf
  rw [← habs]
  obtain ⟨⟨d, k⟩⟩ := f
  simp only [ExprOps.node_kind] at h
  cases k with
  | Const n us =>
    obtain ⟨o, hop, h⟩ := bind_eq_ok_iff.mp h
    have hcwf := (wf_const_inv hfwf rfl).1
    obtain ⟨habsp, -⟩ := defn_probe_refines hfe hwf hcwf hop
    simp only [absExpr_mk, absExprKind]
    rw [hintOf_defnOf, ← habsp]
    cases o with
    | none => simp only [Result.ok.injEq] at h; rw [← h]; simp [absHint]
    | some t =>
      obtain ⟨cv, v, hint⟩ := t
      obtain rfl : r = hint := by simpa using h.symm
      simp
  | _ =>
    simp only [Result.ok.injEq] at h; rw [← h]; simp [absHint]

/-- **`core_k::is_punit_ind`** (`Core.lean:169-206 isUnitLikeTy`): the cited
`match env.find? punitName with | some (.indInfo _ _) => true | _ => false`,
factored out (task #14's probe rule).

Hypothesis to discharge at merge: `hpu` -- `basis_names::punit_name` refines
`ConLeche.punitName` (`CoreKNames.lean`). -/
theorem is_punit_ind_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hpu : ∀ n, basis_names.punit_name = ok n →
      absName n = ConLeche.punitName ∧ NameWF n)
    (hfe : FindAgree fe lfe) (h : core_k.is_punit_ind fe = ok b) :
    b = (match lfe.find? ConLeche.punitName with
         | some (.indInfo _ _) => true
         | _ => false) := by
  rw [core_k.is_punit_ind] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, h⟩ := h
  obtain ⟨hnabs, hnwf⟩ := hpu n hn
  rw [← hnabs]
  cases o with
  | none =>
    rw [hfe.find_none hnwf ho]
    simp only [Result.ok.injEq] at h; rw [← h]
  | some ci =>
    rw [hfe.find_some hnwf ho]
    cases ci <;> simp only [Result.ok.injEq] at h <;> rw [← h] <;>
      simp [absConstantInfo]

/-- **`core_k::is_punit_rec_shape`** (`Core.lean:169-206 isUnitLikeTy`): the
cited `match env.find? punitRecName with | some (.recInfo _ mI rP [r]) =>
mI == rP && r.nfields == 0 | _ => false`, factored out.  The cited `[r]` is
`rules.len() == 1` and the `&&` cascade an `if` nest.

Hypothesis to discharge at merge: `hpur` -- `basis_names::punit_rec_name`
refines `ConLeche.punitRecName` (`CoreKNames.lean`). -/
theorem is_punit_rec_shape_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {b : Bool}
    (hpur : ∀ n, basis_names.punit_rec_name = ok n →
      absName n = ConLeche.punitRecName ∧ NameWF n)
    (hfe : FindAgree fe lfe) (h : core_k.is_punit_rec_shape fe = ok b) :
    b = (match lfe.find? ConLeche.punitRecName with
         | some (.recInfo _ mI rP [r]) => (mI == rP) && (r.nfields == 0)
         | _ => false) := by
  rw [core_k.is_punit_rec_shape] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := hpur n hn
  rw [← hnabs]
  cases o with
  | none =>
    rw [hfe.find_none hnwf ho]
    simp only [Result.ok.injEq] at h; rw [← h]
  | some ci =>
    rw [hfe.find_some hnwf ho]
    cases ci with
    | RecInfo cv mi rp rules =>
      have hv := alloc.vec.Vec.len_val rules
      simp only [] at h
      by_cases hlen : alloc.vec.Vec.len rules = 1#usize
      · rw [if_pos hlen] at h
        have hl : rules.val.length = 1 := by scalar_tac
        obtain ⟨r0, hrv⟩ := List.length_eq_one_iff.mp hl
        simp only [absConstantInfo, hrv, List.map_cons, List.map_nil]
        by_cases hmi : mi = rp
        · rw [if_pos hmi] at h
          obtain ⟨rr, hidx, hb⟩ := bind_eq_ok_iff.mp h
          have hg := ExprOps.vec_index_getElem? hidx
          rw [hrv] at hg
          simp only [show ((0#usize : Std.Usize)).val = 0 from rfl,
            List.getElem?_cons_zero, Option.some.injEq] at hg
          rw [← Result.ok_injective hb, ← hg, hmi]
          simp only [absRecRule, beq_self_eq_true, Bool.true_and]
          by_cases hz : r0.nfields = 0#u64
          · simp [hz]
          · have hzz : r0.nfields.val ≠ 0 := by
              intro hc; exact hz (Std.UScalar.eq_of_val_eq (by rw [hc]; rfl))
            simp [hz, hzz]
        · rw [if_neg hmi] at h
          rw [← Result.ok_injective h]
          have hne : mi.val ≠ rp.val := by
            intro hc; exact hmi (Std.UScalar.eq_of_val_eq hc)
          simp [absRecRule, hne]
      · rw [if_neg hlen] at h
        have hl : rules.val.length ≠ 1 := by intro hc; exact hlen (by scalar_tac)
        rw [← Result.ok_injective h]
        rcases hrv : rules.val with _ | ⟨x, xs⟩
        · simp [absConstantInfo, hrv]
        · rcases xs with _ | ⟨y, ys⟩
          · rw [hrv] at hl; simp at hl
          · simp [absConstantInfo, hrv]
    | _ =>
      simp only [Result.ok.injEq] at h; rw [← h]; simp [absConstantInfo]

/-- **`core_k::is_unit_like_ty` refines `isUnitLikeTy`** (`Core.lean:169-206`;
`Cached/StateC.lean:48-60 isUnitLikeTyC` is the same function on `ExprC`): is
this (whnf'd) type expression a unit-like inductive type?  con-leche's task #161
item C1 computation downgrade -- the head-name comparison against the single pin
that can pass (`PUnit`) comes first, then the two stored-shape checks
specialised to it, licensed by `unitLike_eq_punit`.

Hypotheses to discharge at merge: `hpu`/`hpur` -- `basis_names::punit_name` and
`basis_names::punit_rec_name` refine `ConLeche.punitName`/`punitRecName`
(`CoreKNames.lean`). -/
theorem is_unit_like_ty_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {e : expr.Expr} {b : Bool}
    (hpu : ∀ n, basis_names.punit_name = ok n →
      absName n = ConLeche.punitName ∧ NameWF n)
    (hpur : ∀ n, basis_names.punit_rec_name = ok n →
      absName n = ConLeche.punitRecName ∧ NameWF n)
    (hfe : FindAgree fe lfe) (he : ExprWF e)
    (h : core_k.is_unit_like_ty fe e = ok b) :
    b = (match absExpr e with
         | .const c _ =>
           (c == ConLeche.punitName) &&
           (match lfe.find? ConLeche.punitName with
            | some (.indInfo _ _) => true
            | _ => false) &&
           (match lfe.find? ConLeche.punitRecName with
            | some (.recInfo _ mI rP [r]) => (mI == rP) && (r.nfields == 0)
            | _ => false)
         | _ => false) := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [core_k.is_unit_like_ty.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
  cases k with
  | Const c us =>
    have hcwf := (wf_const_inv he rfl).1
    simp only [bind_eq_ok_iff] at h
    obtain ⟨n, hn, bb, hbb, h⟩ := h
    obtain ⟨hnabs, hnwf⟩ := hpu n hn
    have hbeq := Name.beq_refines hcwf hnwf hbb
    simp only [absExpr_mk, absExprKind]
    split at h
    · rename_i hc
      rw [hc] at hbeq
      have hce : absName c = ConLeche.punitName := by
        rw [← hnabs]; simpa using hbeq.symm
      simp only [hce, beq_self_eq_true, Bool.true_and]
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      rw [← is_punit_ind_refines hpu hfe hb1]
      by_cases hc1 : b1 = true
      · rw [if_pos hc1] at h
        rw [← is_punit_rec_shape_refines hpur hfe h, hc1]
        simp
      · rw [if_neg hc1] at h
        simp only [Bool.not_eq_true] at hc1
        rw [← Result.ok_injective h, hc1]
        simp
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      rw [hc] at hbeq
      have hce : absName c ≠ ConLeche.punitName := by
        rw [← hnabs]
        intro hq; rw [hq] at hbeq; simp at hbeq
      simp only [Result.ok.injEq] at h
      rw [← h]
      simp [hce]
  | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp

/-- **`core_k::str_expansion_fires`** (`Core.lean:2371-2631 defeqStep`): the
cited `cO = stringOfListName ∧ usO = [] ∧ strLitSupported env` guard of the
string-literal expansion arms -- the reference kernels'
`tryStringLitExpansion`, firing exactly when the other side's function part is
the bare `String.ofList` constant.  Stated with `strLitSupportedF`
(`FEnv.lean:120-130`), the index twin of the cited `strLitSupported`.

Hypotheses to discharge at merge: `hsol` -- `basis_names::string_of_list_name`
refines `ConLeche.stringOfListName` (`CoreKNames.lean`); `hsup` --
`core_k::str_lit_supported` refines `strLitSupportedF` (another agent's file). -/
theorem str_expansion_fires_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {f : expr.Expr} {b : Bool}
    (hsol : ∀ n, basis_names.string_of_list_name = ok n →
      absName n = ConLeche.stringOfListName ∧ NameWF n)
    (hsup : ∀ c, core_k.str_lit_supported fe = ok c →
      c = ConLeche.strLitSupportedF lfe)
    (hf : ExprWF f) (h : core_k.str_expansion_fires fe f = ok b) :
    b = (match absExpr f with
         | .const cO usO =>
           decide (cO = ConLeche.stringOfListName) && decide (usO = []) &&
             ConLeche.strLitSupportedF lfe
         | _ => false) := by
  obtain ⟨⟨d, k⟩⟩ := f
  rw [core_k.str_expansion_fires.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
  cases k with
  | Const c us =>
    have hcwf := (wf_const_inv hf rfl).1
    have hv := alloc.vec.Vec.len_val us
    simp only [absExpr_mk, absExprKind]
    simp only [] at h
    by_cases hlen : alloc.vec.Vec.len us = 0#usize
    · rw [if_pos hlen] at h
      have hu : us.val = [] :=
        List.eq_nil_iff_length_eq_zero.mpr (by scalar_tac)
      have hnil : absLevels us = [] := by simp [absLevels, hu]
      simp only [hnil, decide_true, Bool.and_true]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨n, hn, bb, hbb, h⟩ := h
      obtain ⟨hnabs, hnwf⟩ := hsol n hn
      have hbeq := Name.beq_refines hcwf hnwf hbb
      by_cases hc : bb = true
      · rw [if_pos hc] at h
        rw [hc] at hbeq
        have hce : absName c = ConLeche.stringOfListName := by
          rw [← hnabs]; simpa using hbeq.symm
        rw [hsup b h, hce]
        simp
      · rw [if_neg hc] at h
        simp only [Bool.not_eq_true] at hc
        rw [hc] at hbeq
        have hce : absName c ≠ ConLeche.stringOfListName := by
          rw [← hnabs]
          intro hq; rw [hq] at hbeq; simp at hbeq
        rw [← Result.ok_injective h]
        simp [hce]
    · rw [if_neg hlen] at h
      have hne : us.val ≠ [] := by
        intro hq
        have h0 : us.val.length = 0 := by rw [hq]; rfl
        exact hlen (by scalar_tac)
      have hnn : absLevels us ≠ [] := by simp [absLevels, hne]
      rw [← Result.ok_injective h]
      simp [hnn]
  | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.CoreK.is_unit_like_ty_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms is_unit_like_ty_refines

end ConRon.Refine.CoreK
