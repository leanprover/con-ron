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
    simp only [arc_deref_eq, bind_ok, level_node_kind] at h
    refine ⟨?_, PropWhen.if_all_zero_wf (fun n hn => by simp [alloc.vec.Vec.new] at hn) h⟩
    rw [PropWhen.if_all_zero_refines h]
    simp [ConLeche.Level.zeronessOf, absNames, alloc.vec.Vec.new]
  | @succ a u ha h1 _ =>
    obtain ⟨hh, hu⟩ := level_succ_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [arc_deref_eq, bind_ok, level_node_kind] at h
    exact ⟨by rw [PropWhen.never_refines h]; simp [ConLeche.Level.zeronessOf],
      PropWhen.never_wf h⟩
  | @max a b u ha hb h1 iha ihb =>
    obtain ⟨hh, hu⟩ := level_max_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [arc_deref_eq, bind_ok, level_node_kind, bind_eq_ok_iff] at h
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
    simp only [arc_deref_eq, bind_ok, level_node_kind] at h
    obtain ⟨habsb, hwfb⟩ := ihb pw h
    exact ⟨by rw [habsb]; simp [ConLeche.Level.zeronessOf], hwfb⟩
  | @param n u hn h1 =>
    obtain ⟨hh, hu⟩ := level_param_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [arc_deref_eq, bind_ok, level_node_kind, bind_eq_ok_iff, name_dup_eq] at h
    obtain ⟨ps, hps, h⟩ := h
    have hpsv : ps.val = [n] := by
      rw [vec_push_val hps]; simp [alloc.vec.Vec.new]
    have hnames : NamesWF ps := by
      intro k hk; rw [hpsv] at hk; simp at hk; rw [hk]; exact hn
    refine ⟨?_, PropWhen.if_all_zero_wf hnames h⟩
    rw [PropWhen.if_all_zero_refines h]
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

/-! ## `allLevelParamsDefined` (`Kernel/Level.lean:251-268`, memoized at `:299`)

`level::all_params_defined` belongs to `level.rs` and has no lemma there; its
refinement is stated here, as task #13 put `level::zeroness_of` and
`level::subst_pw` in this file.  (The `expr_ops.rs` walks that called it went
with the `Expr`-tree reference code, task #105.) -/

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
    simp only [arc_deref_eq, bind_ok, level_node_kind, Result.ok.injEq] at hb
    rw [← hb]; simp [ConLeche.Level.allParamsDefined]
  | param h n =>
    intro hu b hb
    rw [level.all_params_defined.eq_def] at hb
    simp only [arc_deref_eq, bind_ok, level_node_kind] at hb
    rw [Name.contains_refines hpar (Level.LevelWF.param_inv hu) hb]
    simp [ConLeche.Level.allParamsDefined]
  | succ h x ih =>
    intro hu b hb
    rw [level.all_params_defined.eq_def] at hb
    simp only [arc_deref_eq, bind_ok, level_node_kind] at hb
    rw [ih (Level.LevelWF.succ_inv hu) b hb]
    simp [ConLeche.Level.allParamsDefined]
  | max h x y ih1 ih2 =>
    intro hu b hb
    rw [level.all_params_defined.eq_def] at hb
    simp only [arc_deref_eq, bind_ok, level_node_kind] at hb
    obtain ⟨hx, hy⟩ := Level.LevelWF.max_inv hu
    obtain ⟨b1, hb1, hb⟩ := bind_eq_ok_iff.mp hb
    cases b1 with
    | false =>
      simp only [Bool.false_eq_true, ite_false, Result.ok.injEq] at hb
      have e1 := ih1 hx false hb1
      simp [ConLeche.Level.allParamsDefined, ← e1, ← hb]
    | true =>
      simp only [ite_true] at hb
      have e1 := ih1 hx true hb1
      have e2 := ih2 hy b hb
      simp [ConLeche.Level.allParamsDefined, ← e1, e2]
  | imax h x y ih1 ih2 =>
    intro hu b hb
    rw [level.all_params_defined.eq_def] at hb
    simp only [arc_deref_eq, bind_ok, level_node_kind] at hb
    obtain ⟨hx, hy⟩ := Level.LevelWF.imax_inv hu
    obtain ⟨b1, hb1, hb⟩ := bind_eq_ok_iff.mp hb
    cases b1 with
    | false =>
      simp only [Bool.false_eq_true, ite_false, Result.ok.injEq] at hb
      have e1 := ih1 hx false hb1
      simp [ConLeche.Level.allParamsDefined, ← e1, ← hb]
    | true =>
      simp only [ite_true] at hb
      have e1 := ih1 hx true hb1
      have e2 := ih2 hy b hb
      simp [ConLeche.Level.allParamsDefined, ← e1, e2]

/-! ## The zero-ness tests at use (`level.rs`, upstream task #480)

`is_always_zero` and `zero_where_zero` read two zero-ness data where the stored
guards used to; `names_all_in_from` is `List.all` of `List.contains`. -/

/-- `level::names_all_in_from`: every name of `qs` from `i` on is in `ps`. -/
theorem names_all_in_from_refines {qs ps : alloc.vec.Vec name.Name}
    (hqs : NamesWF qs) (hps : NamesWF ps) :
    ∀ k : Nat, ∀ (i : Std.Usize) (c : Bool), qs.length - i.val ≤ k →
      level.names_all_in_from qs ps i = ok c →
      c = ((absNames qs).drop i.val).all (absNames ps).contains := by
  intro k
  induction k with
  | zero =>
    intro i c hk h
    rw [level.names_all_in_from.eq_def] at h; simp only [] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len qs by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by simp [absNames]; scalar_tac)]; rfl
  | succ k ih =>
    intro i c hk h
    rw [level.names_all_in_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ qs.length
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len qs by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by simp [absNames]; scalar_tac)]; rfl
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len qs by scalar_tac)] at h
      have hlt : i.val < qs.val.length := by scalar_tac
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec qs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_ok] at h
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      have hyw : NameWF qs.val[i.val] := hqs _ (List.getElem_mem hlt)
      have hbv := Name.contains_refines hps hyw hb
      have hdrop : (absNames qs).drop i.val = absName qs.val[i.val] ::
          (absNames qs).drop (i.val + 1) := by
        simp only [absNames]
        rw [← List.map_drop, List.drop_eq_getElem_cons hlt, List.map_cons, List.map_drop]
      rw [hdrop, List.all_cons]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ite_false, Result.ok.injEq] at h
        rw [← h, ← hbv]; rfl
      | true =>
        simp only [ite_true] at h
        have hmax : i.val + 1 ≤ Std.Usize.max := by have := qs.slice.property; scalar_tac
        obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
        rw [hw, bind_ok] at h
        rw [← hbv, ih w c (by scalar_tac) h, hwv]; rfl

/-- **`level::is_always_zero` refines `Level.isAlwaysZero`**: the datum is
`ifAllZero []`. -/
theorem is_always_zero_refines {s : level.Level} (hs : LevelWF s) {b : Bool}
    (h : level.is_always_zero s = ok b) :
    b = ConLeche.Level.isAlwaysZero (absLevel s) := by
  rw [level.is_always_zero] at h
  obtain ⟨pw, hpw, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨apw, -⟩ := zeroness_of_refines hs pw hpw
  rw [ConLeche.Level.isAlwaysZero, ← apw]
  cases pw with
  | Never => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | IfAllZero ps =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    cases hp : ps.val with
    | nil =>
      have : ps.len = 0#usize := by
        apply Std.UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len, hp]
      rw [this]
      simp [absPropWhen, absNames, hp]
    | cons x r =>
      have : ps.len ≠ 0#usize := by
        intro hc; have := congrArg Std.UScalar.val hc; simp [alloc.vec.Vec.len, hp] at this
      rw [decide_eq_false this]
      simp [absPropWhen, absNames, hp]

/-- **`level::zero_where_zero` refines `Level.zeroWhereZero`**. -/
theorem zero_where_zero_refines {s u : level.Level} (hs : LevelWF s) (hu : LevelWF u)
    {b : Bool} (h : level.zero_where_zero s u = ok b) :
    b = ConLeche.Level.zeroWhereZero (absLevel s) (absLevel u) := by
  rw [level.zero_where_zero] at h
  obtain ⟨zs, hzs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨zu, hzu, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨aS, ws⟩ := zeroness_of_refines hs zs hzs
  obtain ⟨au, wu⟩ := zeroness_of_refines hu zu hzu
  rw [ConLeche.Level.zeroWhereZero, ← aS, ← au]
  cases zs with
  | Never => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | IfAllZero ps =>
    cases zu with
    | Never => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | IfAllZero qs =>
      simp only [] at h
      have hc := names_all_in_from_refines wu ws qs.length 0#usize b (by scalar_tac) h
      simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hc
      rw [hc]; rfl

end ConRon.Refine.ExprOps

