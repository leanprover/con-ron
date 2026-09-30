/-
Part of task #21 (`ConRon/Refine/ExprOps.lean`'s group): the *metadata* half of
`crates/con-ron-core/src/kernel/expr_ops.rs` -- the two node-keyed memoized
walks (`reset_meta`, `rename_consts`), the level-parameter substitution
(`levels_subst`, `instantiate_level_params`, with the `level::zeroness_of` and
`level::subst_pw` bridge task #13 added to `level.rs`), and the leaf readers
(`is_lam`, `lam_pw`, `forall_pw`, `has_level_param`, `expr_ptr_beq`,
`fvar_leaves`).

Statements are against the **logical** con-leche definitions, exact result on
success, abstraction equation first and well-formedness second, exactly as
`ConRon/Refine/ExprOps.lean`'s `instantiate1_refines`.  The two walks here are
keyed by the *node alone*, so they instantiate the foundation's `MemoInv` at
`KWF := ExprWF`, `absK := absExpr`, `A := ConLeche.Expr` and use
`expr_key_exact`/`memo_e_get_hit`.

Three things cost time and are worth recording.  (1) `reset_meta_go`'s
memo-skipping leaves are `Bvar`/`Sort`/`Const`/`Lit` -- **`Fvar` is a
*memoized* case here**, because the walk descends into the annotation, unlike
`instantiate1`'s; the same is true of `rename_consts_go`, where `Const` is the
interesting case and therefore not a leaf.  (2) The higher-order arguments are
one-method dictionaries (task #9's pattern 1): `expr_ops::NameToName` and
`level::SubstZ`, so their lemmas carry a hypothesis relating the dictionary to
the Lean function, as `Refine/PropWhen.lean` does for `bind_z`.  (3)
`has_level_param` is *not* a walk in the port: it is the `O(1)` packed-word
read, so its lemma is task #20's `Expr.has_lp_refines` composed with
con-leche's `Expr.hasLP_eq` (`ExprOps.lean:2538`) -- the `@[csimp]`-free member
of the family.
-/
import ConRon.Refine.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps

/-! ## `resetMeta` (`ExprOps.lean:540-692`) -/

/-! ## `renameConsts` (`ExprOps.lean:930-1116`)

`levels_copy` is the port's stand-in for "the `us` a rebuilt `.const` node
carries over unchanged"; in the model a `Vec` copy is the *same list*, because
`level::dup` is the identity (`Rc::clone`, DESIGN.md §3.2), so its helper is an
equation between vectors rather than a refinement lemma; it lives in the
foundation (`ExprOps.lean`'s `levels_copy_from_val`/`levels_copy_val`), which is
where the spine group needs it too. -/

/-! ## The `Level`-to-`PropWhen` bridge (`level.rs`, task #13)

`level::zeroness_of` and `level::subst_pw` were filled into `level.rs` at task
#13 (the two blocks task #3 deferred until `PropWhen` existed).  Their lemmas
live *here*, next to their one consumer `instantiate_level_params`, rather than
in `ConRon/Refine/Level.lean`: `zeronessOf` produces a `PropWhen`, so the proof
needs `Refine/PropWhen.lean`, which `Refine/Level.lean` does not import. -/

/-- The `Level` twin of the foundation's `node_kind`. -/
theorem level_node_kind (h : Std.U64) (k : level.LevelKind) :
    (level.Level.mk (level.LevelNode.mk h k))._0.kind = k := rfl

/-- **`level::zeroness_of` refines `Level.zeronessOf`**
(`ConLeche/Kernel/Level.lean:185-195`). -/
theorem zeroness_of_refines {l : level.Level} (hl : LevelWF l) :
    ∀ pw, level.zeroness_of l = ok pw →
      absPropWhen pw = ConLeche.Level.zeronessOf (absLevel l) ∧ PropWhenWF pw := by
  induction hl with
  | @zero u h1 =>
    have hu := level_zero_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, level_node_kind] at h
    refine ⟨?_, PropWhen.if_all_zero_wf (fun n hn => by simp at hn) h⟩
    rw [PropWhen.if_all_zero_refines (fun n hn => by simp at hn) h]
    simp [ConLeche.Level.zeronessOf, absNames, alloc.vec.Vec.new]
  | @succ a u ha h1 _ =>
    obtain ⟨hh, hu⟩ := level_succ_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, level_node_kind] at h
    exact ⟨by rw [PropWhen.never_refines h]; simp [ConLeche.Level.zeronessOf],
      PropWhen.never_wf h⟩
  | @max a b u ha hb h1 iha ihb =>
    obtain ⟨hh, hu⟩ := level_max_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, level_node_kind, bind_eq_ok_iff] at h
    obtain ⟨pa, hpa, pb, hpb, hinter⟩ := h
    obtain ⟨habsa, hwfa⟩ := iha pa hpa
    obtain ⟨habsb, hwfb⟩ := ihb pb hpb
    obtain ⟨habs, hwf⟩ := PropWhen.inter_refines hwfa hwfb hinter
    exact ⟨by rw [habs, habsa, habsb]; simp [ConLeche.Level.zeronessOf], hwf⟩
  | @imax a b u ha hb h1 _ ihb =>
    obtain ⟨hh, hu⟩ := level_imax_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, level_node_kind] at h
    obtain ⟨habsb, hwfb⟩ := ihb pw h
    exact ⟨by rw [habsb]; simp [ConLeche.Level.zeronessOf], hwfb⟩
  | @param n u hn h1 =>
    obtain ⟨hh, hu⟩ := level_param_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, level_node_kind, bind_eq_ok_iff, name_dup_eq] at h
    obtain ⟨ps, hps, h⟩ := h
    have hpsv : ps.val = [n] := by
      rw [vec_push_val hps]; simp [alloc.vec.Vec.new]
    have hnames : NamesWF ps := by
      intro k hk; rw [hpsv] at hk; simp at hk; rw [hk]; exact hn
    refine ⟨?_, PropWhen.if_all_zero_wf hnames h⟩
    rw [PropWhen.if_all_zero_refines hnames h]
    have : absNames ps = [absName n] := by unfold absNames; rw [hpsv]; simp
    rw [this]
    simp [ConLeche.Level.zeronessOf]

/-- **`level::subst_pw` refines `Level.substPW`**
(`ConLeche/Kernel/Level.lean:197-207`): `prop_when::bind_z` at the dictionary
`level::SubstZ`, whose `apply` is `zeroness_of ∘ subst_go` -- exactly the
closure con-leche writes.  The `Φ` of `PropWhen.bind_z_refines` is therefore
`fun n => zeronessOf (Level.subst.go ks vs n)`, and `hf` is
`Level.subst_go_refines` followed by `zeroness_of_refines`. -/
theorem subst_pw_refines {ks : alloc.vec.Vec name.Name} {vs : alloc.vec.Vec level.Level}
    {pw r : prop_when.PropWhen} (hks : NamesWF ks) (hvs : LevelsWF vs)
    (hpw : PropWhenWF pw) (h : level.subst_pw ks vs pw = ok r) :
    absPropWhen r = ConLeche.Level.substPW (absNames ks) (absLevels vs) (absPropWhen pw)
      ∧ PropWhenWF r := by
  rw [level.subst_pw] at h
  have hf : ∀ n, NameWF n → ∀ c,
      (prop_when.NameToPw.apply
        level.SubstZ.Insts.Con_ron_coreKernelProp_whenNameToPw) { ks := ks, vs := vs } n
        = ok c →
      absPropWhen c =
        ConLeche.Level.zeronessOf
          (ConLeche.Level.subst.go (absNames ks) (absLevels vs) (absName n)) ∧
        PropWhenWF c := by
    intro n hn c hc
    have hc' : (do
          let l ← level.subst_go ks vs 0#usize n
          level.zeroness_of l) = ok c := hc
    obtain ⟨u, hu, hz⟩ := bind_eq_ok_iff.mp hc'
    obtain ⟨habsu, hwfu⟩ := Level.subst_go_refines hks hvs hn ks.length 0#usize
      (by scalar_tac) u hu
    obtain ⟨habsc, hwfc⟩ := zeroness_of_refines hwfu c hz
    refine ⟨?_, hwfc⟩
    have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
    rw [habsc, habsu, h0]
    simp only [List.drop_zero]
    rfl
  obtain ⟨habs, hwf⟩ := PropWhen.bind_z_refines
    (fun n => ConLeche.Level.zeronessOf
      (ConLeche.Level.subst.go (absNames ks) (absLevels vs) n)) hf hpw h
  exact ⟨by rw [habs, ConLeche.Level.substPW], hwf⟩

/-! ## `instantiateLevelParams` (`Kernel/Level.lean:232-249`, memoized at
`ExprOps.lean:2564-2724`)

`levels_subst` is `vs.map (Level.subst ks us)`, the closure DESIGN.md §3.4
forbids, as an index recursion; the `absLevels` of the result is therefore the
`List.map` con-leche writes. -/

/-! ## The leaf readers

`is_lam`, `lam_pw` and `forall_pw` need no well-formedness: they read the
node's kind, and a `PropWhen` they hand out is the node's own (`prop_when::dup`
is the identity), so its `PropWhenWF` is not a *new* obligation -- a caller who
has `ExprWF e` gets it by inverting that derivation.  The statements are
therefore plain abstraction equations, `Option.map`-shaped where the result is
an `Option`. -/

/-! ## `fvarLeaves` (`ExprOps.lean:823`)

The result is a `Vec<(u64, Expr)>` where con-leche has a `List (Nat × Expr)`,
so the abstraction is the pointwise one; the port accumulates where Lean `++`s
(task #13's deviation 3), which is what the `*_go` lemma's `out ++` shape
records. -/

/-! ## `allLevelParamsDefined` (`Kernel/Level.lean:251-268`, memoized at `:299`)

The last family of `expr_ops.rs`: the specification walk, its two `Vec` loops,
and the node-keyed memoized walk that con-leche's `@[csimp]` equation
(`Level.lean:409-412`) swaps in.  `level::all_params_defined` belongs to
`level.rs` and has no lemma there; its only caller is this family, so its
refinement is stated here, exactly as task #13 put `level::zeroness_of` and
`level::subst_pw` in this file.

`bool_and`/`bool_and3` are the port's `&&` *as a call* (task #18's rule: a
gated result whose arms rejoin must become a call, or Aeneas cannot match the
contexts), so they are total and get plain equations rather than
`ok`-hypothesis lemmas. -/

/-- `expr_ops::bool_and` is `&&`. -/
@[simp] theorem bool_and_val (a b : Bool) : expr_ops.bool_and a b = ok (a && b) := by
  rw [expr_ops.bool_and]; cases a <;> simp

/-- `expr_ops::bool_and3` is `&&` at three operands, left-associated as Lean's
`a && b && c` is. -/
@[simp] theorem bool_and3_val (a b c : Bool) :
    expr_ops.bool_and3 a b c = ok (a && b && c) := by
  rw [expr_ops.bool_and3]; simp

/-- `level::all_params_defined` refines `Level.allParamsDefined`
(`Kernel/Level.lean:39-44`).  The `.param` arm is `name::contains`, which is
exact only on well-formed names, hence the `LevelWF` hypothesis. -/
theorem all_params_defined_refines {params : alloc.vec.Vec name.Name}
    (hpar : NamesWF params) :
    ∀ (u : level.Level), LevelWF u → ∀ b,
      level.all_params_defined params u = ok b →
      b = ConLeche.Level.allParamsDefined (absNames params) (absLevel u) := by
  intro u
  induction u using Level.ind' with
  | zero h =>
    intro hu b hb
    rw [level.all_params_defined.eq_def] at hb
    simp only [arc_deref_eq, bind_tc_ok, level_node_kind, Result.ok.injEq] at hb
    rw [← hb]; simp [ConLeche.Level.allParamsDefined]
  | param h n =>
    intro hu b hb
    rw [level.all_params_defined.eq_def] at hb
    simp only [arc_deref_eq, bind_tc_ok, level_node_kind] at hb
    rw [Name.contains_refines hpar (Level.LevelWF.param_inv hu) hb]
    simp [ConLeche.Level.allParamsDefined]
  | succ h x ih =>
    intro hu b hb
    rw [level.all_params_defined.eq_def] at hb
    simp only [arc_deref_eq, bind_tc_ok, level_node_kind] at hb
    rw [ih (Level.LevelWF.succ_inv hu) b hb]
    simp [ConLeche.Level.allParamsDefined]
  | max h x y ih1 ih2 =>
    intro hu b hb
    rw [level.all_params_defined.eq_def] at hb
    simp only [arc_deref_eq, bind_tc_ok, level_node_kind] at hb
    obtain ⟨hx, hy⟩ := Level.LevelWF.max_inv hu
    obtain ⟨b1, hb1, hb⟩ := bind_eq_ok_iff.mp hb
    cases b1 with
    | false =>
      simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at hb
      have e1 := ih1 hx false hb1
      simp [ConLeche.Level.allParamsDefined, ← e1, ← hb]
    | true =>
      simp only [if_true] at hb
      have e1 := ih1 hx true hb1
      have e2 := ih2 hy b hb
      simp [ConLeche.Level.allParamsDefined, ← e1, e2]
  | imax h x y ih1 ih2 =>
    intro hu b hb
    rw [level.all_params_defined.eq_def] at hb
    simp only [arc_deref_eq, bind_tc_ok, level_node_kind] at hb
    obtain ⟨hx, hy⟩ := Level.LevelWF.imax_inv hu
    obtain ⟨b1, hb1, hb⟩ := bind_eq_ok_iff.mp hb
    cases b1 with
    | false =>
      simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at hb
      have e1 := ih1 hx false hb1
      simp [ConLeche.Level.allParamsDefined, ← e1, ← hb]
    | true =>
      simp only [if_true] at hb
      have e1 := ih1 hx true hb1
      have e2 := ih2 hy b hb
      simp [ConLeche.Level.allParamsDefined, ← e1, e2]

end ConRon.Refine.ExprOps

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`instantiate_level_params_refines` is the deepest chain in this part -- the
node-keyed memo, `levels_subst`, `level::subst_pw` through `PropWhen.bindZ`,
and the `hasLP` cutoff -- so it is the one worth pinning. -/

