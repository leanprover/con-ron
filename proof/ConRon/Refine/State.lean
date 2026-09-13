/-
Step 2 of `ConRon/Refine/CORE_PLAN.md`: the **state** half of
`cached::state_c`'s refinement — the fourteen memo tables of
`cached::state_c::CState` against con-leche's `ConLeche.Cached.CState`
(`ConLeche/Cached/StateC.lean:131-156`).

What is here: the key and value abstractions with their well-formedness
predicates (task #17's hereditary style), the eight `Eq2Fwd` facts the memo
keys need, the two relations `StateRel`/`StateWF`, the fresh state
(`cstate_new`), the flush (`flushed`), and one `get`/`insert` lemma per map —
the nine `*_probe` functions of `state_c.rs` and the six memos `core_c.rs`
reads off the state inline.

`Refine/HashMapWF.lean` is what carries the tables: its `Eq2Fwd` is the
*forward, key-restricted* `eq2` hypothesis that a port `beq_refines` lemma
actually gives, and its `RelOn` the correspondingly key-restricted bridge to
`Std.HashMap`.  Everything below is those two lemmas (`Rel_get_wf`,
`Rel_insert_wf`) with the key facts supplied: `Eq2Fwd` and injectivity of the
key abstraction under the key's `*WF`, bundled here as `KeyOk`.

What is **not** here: the `*M` wrappers (`simplify_l_m`, `const_ty_at_m`,
`stored_ty_idx_m`, `inst_list_m`, …) and with them the `instC` entry cap
(`inst_c_cap_c`, con-leche's `instListM` clear-on-cap).  Those are step 5 of
the plan, `Refine/StateC.lean`; only the relation is wanted here.

`LawfulHashable` on the con-leche key types is *not* taken from
`ConLeche/Verify/…` (the proof tier, which this file deliberately does not
import): Lean's own `instLawfulHashableOfLawfulBEq` derives it from the
`LawfulBEq` instances con-leche exports (`Kernel/Name.lean:91`,
`Kernel/Expr.lean:89,986`), and `Prod`/`List` lift both, so the pattern of
`Verify/Cached/SimC.lean:89` and `Verify/Cached/OpsC.lean:63` need not be
reproduced at all.
-/
import ConRon.Refine.HashMapWF
import ConRon.Refine.Expr
import ConLeche.Cached.StateC

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.State

/-! ## The dictionaries, abbreviated

The eight `Hashable`/`Eq2` pairs the fourteen tables are built on.  Each is
`@[reducible]` in `Generated/Funs.lean`, so these abbreviations unify with the
generated call sites. -/

/-- The `ienv` key's `Hashable` dictionary. -/
abbrev hName := name.Name.Insts.Con_ron_coreRonHashmapHashable
/-- The `ienv` key's `Eq2` dictionary: `name::beq`. -/
abbrev eName := name.Name.Insts.Con_ron_coreRonHashmapEq2
/-- The `lsimpC`/`lnzC` key's `Hashable` dictionary. -/
abbrev hLevel := level.Level.Insts.Con_ron_coreRonHashmapHashable
/-- The `lsimpC`/`lnzC` key's `Eq2` dictionary: `level::beq`. -/
abbrev eLevel := level.Level.Insts.Con_ron_coreRonHashmapEq2
/-- The `Expr`-keyed memos' `Hashable` dictionary (the cached word). -/
abbrev hExpr := expr.Expr.Insts.Con_ron_coreRonHashmapHashable
/-- The `Expr`-keyed memos' `Eq2` dictionary: `expr::beq`. -/
abbrev eExpr := expr.Expr.Insts.Con_ron_coreRonHashmapEq2
/-- The `constTyAt`/`constValAt` key's `Hashable` dictionary. -/
abbrev hNameLevels := PairNameVecLevel.Insts.Con_ron_coreRonHashmapHashable
/-- The `constTyAt`/`constValAt` key's `Eq2` dictionary. -/
abbrev eNameLevels := PairNameVecLevel.Insts.Con_ron_coreRonHashmapEq2
/-- The `ruleRhsAt` key's `Hashable` dictionary. -/
abbrev hNameNameLevels := TupleNameNameVecLevel.Insts.Con_ron_coreRonHashmapHashable
/-- The `ruleRhsAt` key's `Eq2` dictionary. -/
abbrev eNameNameLevels := TupleNameNameVecLevel.Insts.Con_ron_coreRonHashmapEq2
/-- The `defeqC` key's `Hashable` dictionary. -/
abbrev hExprPair := PairExprExpr.Insts.Con_ron_coreRonHashmapHashable
/-- The `defeqC` key's `Eq2` dictionary. -/
abbrev eExprPair := PairExprExpr.Insts.Con_ron_coreRonHashmapEq2
/-- The `eqvC` key's `Hashable` dictionary. -/
abbrev hLevelPair := PairLevelLevel.Insts.Con_ron_coreRonHashmapHashable
/-- The `eqvC` key's `Eq2` dictionary. -/
abbrev eLevelPair := PairLevelLevel.Insts.Con_ron_coreRonHashmapEq2
/-- The `instC` key's `Hashable` dictionary. -/
abbrev hInstKey := TupleExprVecExprU64.Insts.Con_ron_coreRonHashmapHashable
/-- The `instC` key's `Eq2` dictionary. -/
abbrev eInstKey := TupleExprVecExprU64.Insts.Con_ron_coreRonHashmapEq2

/-- `expr::dup` is the identity in the model, in the `simp` shape `level_dup_eq`
and `name_dup_eq` have in `Refine/Abs.lean` (the probes answer a copy). -/
@[local simp] theorem expr_dup_eq (e : expr.Expr) : expr.dup e = ok e := by
  obtain ⟨r⟩ := e; simp [expr.dup]

/-! ## The abstractions and their well-formedness predicates -/

/-- `ConLeche/Cached/StateC.lean:122-126` — one `ienv` entry: the stored
constant's tagged type and optional tagged value (`ExprC` is `Expr`). -/
def absCConstE (c : cached.state_c.CConstE) : ConLeche.Cached.CConstE :=
  { tyE := absExpr c.ty_e, ty := absExpr c.ty,
    val := c.val.map fun p => (absExpr p.1, absExpr p.2) }

/-- The `constTyAt`/`constValAt` key `(Name, List Level)`. -/
def absNameLevels (k : name.Name × alloc.vec.Vec level.Level) :
    ConLeche.Name × List ConLeche.Level := (absName k.1, absLevels k.2)

/-- The `ruleRhsAt` key `(Name, Name, List Level)`. -/
def absNameNameLevels
    (k : name.Name × name.Name × alloc.vec.Vec level.Level) :
    ConLeche.Name × ConLeche.Name × List ConLeche.Level :=
  (absName k.1, absName k.2.1, absLevels k.2.2)

/-- The `defeqC` key `(ExprC × ExprC)`. -/
def absExprPair (k : expr.Expr × expr.Expr) : ConLeche.Expr × ConLeche.Expr :=
  (absExpr k.1, absExpr k.2)

/-- The `eqvC` key `(Level × Level)`. -/
def absLevelPair (k : level.Level × level.Level) :
    ConLeche.Level × ConLeche.Level := (absLevel k.1, absLevel k.2)

/-- The `instC` key `(ExprC, List ExprC, Nat)`; the cursor is a `u64` in the
port and a `Nat` in con-leche (DESIGN.md §3.3). -/
def absInstKey (k : expr.Expr × alloc.vec.Vec expr.Expr × Std.U64) :
    ConLeche.Expr × List ConLeche.Expr × Nat :=
  (absExpr k.1, absExprs k.2.1, k.2.2.val)

/-- An `ienv` entry is well formed when its three terms are. -/
def CConstEWF (c : cached.state_c.CConstE) : Prop :=
  ExprWF c.ty_e ∧ ExprWF c.ty ∧ ∀ p, c.val = some p → ExprWF p.1 ∧ ExprWF p.2

/-- The `constTyAt`/`constValAt` key, componentwise. -/
def NameLevelsWF (k : name.Name × alloc.vec.Vec level.Level) : Prop :=
  NameWF k.1 ∧ LevelsWF k.2

/-- The `ruleRhsAt` key, componentwise. -/
def NameNameLevelsWF
    (k : name.Name × name.Name × alloc.vec.Vec level.Level) : Prop :=
  NameWF k.1 ∧ NameWF k.2.1 ∧ LevelsWF k.2.2

/-- The `defeqC` key, componentwise. -/
def ExprPairWF (k : expr.Expr × expr.Expr) : Prop := ExprWF k.1 ∧ ExprWF k.2

/-- The `eqvC` key, componentwise. -/
def LevelPairWF (k : level.Level × level.Level) : Prop :=
  LevelWF k.1 ∧ LevelWF k.2

/-- The `instC` key; the `u64` cursor carries no invariant. -/
def InstKeyWF (k : expr.Expr × alloc.vec.Vec expr.Expr × Std.U64) : Prop :=
  ExprWF k.1 ∧ ExprsWF k.2.1

/-! ## `abs` is injective on well-formed keys

The componentwise injectivity of `Refine/{Name,Level,Expr}.lean`'s, with
`decide`-level equality of the machine words where there is one.  `exprs_list_inj`
is `Refine/Env.lean`'s, repeated here because `State.lean` sits beside that file
rather than above it. -/

/-- A `u64` is determined by its value. -/
theorem u64_val_inj {a b : Std.U64} (h : a.val = b.val) : a = b := by scalar_tac

/-- `absExpr` is injective on a list of well-formed terms. -/
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

/-- `absExprs` is injective on a well-formed `Vec<Expr>`. -/
theorem absExprs_inj {xs ys : alloc.vec.Vec expr.Expr} (hx : ExprsWF xs)
    (hy : ExprsWF ys) (h : absExprs xs = absExprs ys) : xs = ys :=
  alloc.vec.Vec.ext _ _ (exprs_list_inj hx hy h)

/-! ## `state_c::exprs_beq`

The `instC` key's `List ExprC` equality.  A different Rust function from
`expr::exprs_beq` with the same body, so this is `Refine/Env.lean`'s proof at
the `!=` length test `state_c`'s entry point uses. -/

/-- The index recursion behind `state_c::exprs_beq`; `hlen` is the length test
the entry point has already made. -/
theorem exprs_beq_from_refines {xs ys : alloc.vec.Vec expr.Expr}
    (hx : ExprsWF xs) (hy : ExprsWF ys) (hlen : xs.val.length = ys.val.length) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool), xs.val.length - i.val ≤ k →
      cached.state_c.exprs_beq_from xs ys i = ok b →
      (b = true ↔
        (xs.val.drop i.val).map absExpr = (ys.val.drop i.val).map absExpr) := by
  have hnil : ∀ (i : Std.Usize), xs.val.length ≤ i.val →
      ((xs.val.drop i.val).map absExpr = (ys.val.drop i.val).map absExpr) := by
    intro i hi
    rw [List.drop_eq_nil_of_le hi, List.drop_eq_nil_of_le (by omega)]
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [cached.state_c.exprs_beq_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [← h]
    exact iff_of_true rfl (hnil i (by scalar_tac))
  | succ k ih =>
    intro i b hk h
    rw [cached.state_c.exprs_beq_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ xs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
      rw [← h]
      exact iff_of_true rfl (hnil i (by scalar_tac))
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      have hl : i.val < xs.val.length := by scalar_tac
      have hr : i.val < ys.val.length := by omega
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := xs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy2, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec xs i hl)
      obtain ⟨z, hz, hzv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ys i hr)
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
        simp only [if_true, bind_eq_ok_iff, hw, Result.ok.injEq,
          exists_eq_left'] at h
        have heq := of_decide_eq_true hb0'.symm
        have hrec := ih w b (by scalar_tac) h
        rw [hwv] at hrec
        rw [hrec]
        simp only [heq, true_and]

/-- `state_c::exprs_beq` decides equality of the abstracted term lists,
exactly. -/
theorem exprs_beq_refines {xs ys : alloc.vec.Vec expr.Expr} {c : Bool}
    (hx : ExprsWF xs) (hy : ExprsWF ys)
    (h : cached.state_c.exprs_beq xs ys = ok c) :
    c = decide (absExprs xs = absExprs ys) := by
  rw [cached.state_c.exprs_beq.eq_def] at h; simp only [] at h
  by_cases hlen : xs.val.length = ys.val.length
  · rw [if_neg (show ¬ (alloc.vec.Vec.len xs != alloc.vec.Vec.len ys) by
      simp only [bne_iff_ne, ne_eq, not_not]; scalar_tac)] at h
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
  · rw [if_pos (show (alloc.vec.Vec.len xs != alloc.vec.Vec.len ys) by
      simp only [bne_iff_ne, ne_eq]; intro hc; exact hlen (by scalar_tac)),
      Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    simp only [absExprs]
    intro hc
    exact hlen (by simpa using congrArg List.length hc)

/-! ## The eight key dictionaries

`Eq2Fwd` for each: the dictionary's `eq2` *is* the port's `beq` (by `rfl`, as
`Refine/Expr.lean`'s `eq2_eq`), the `*_refines` lemma turns the returned `Bool`
into `decide (abs a = abs b)`, and injectivity of `abs` **under the key's
`*WF`** turns that into `decide (a = b)`.  That last step is why the hypothesis
has to be the key-restricted one: `absName`/`absExpr` are injective only on
well-formed input. -/

/-- Componentwise exactness, transported along an iff — the step from "the
components' abstractions agree" to "the keys are equal". -/
theorem decide_of_iff {P Q : Prop} [Decidable P] [Decidable Q] {c : Bool}
    (h : c = decide P) (hiff : P ↔ Q) : c = decide Q := by
  rw [h]; exact decide_eq_decide.mpr hiff

/-- The `ienv` key: `name::beq` never lies about well-formed names. -/
theorem nameEq2Fwd : HashMap.Eq2Fwd eName NameWF := by
  intro a b c ha hb h
  rw [show eName.eq2 a b = name.beq a b from rfl] at h
  rw [Name.beq_refines ha hb h]
  exact decide_eq_decide.mpr
    ⟨fun hc => Name.absName_injective ha hb hc, fun hc => by rw [hc]⟩

/-- The level memos' key: `level::beq` never lies about well-formed
levels. -/
theorem levelEq2Fwd : HashMap.Eq2Fwd eLevel LevelWF := by
  intro a b c ha hb h
  rw [show eLevel.eq2 a b = level.beq a b from rfl] at h
  rw [Level.beq_refines ha hb h]
  exact decide_eq_decide.mpr
    ⟨fun hc => Level.absLevel_injective ha hb hc, fun hc => by rw [hc]⟩

/-- The `Expr`-keyed memos' key: `expr::beq` never lies about well-formed
terms (`Refine/Expr.lean`'s `eq2_refines`). -/
theorem exprEq2Fwd : HashMap.Eq2Fwd eExpr ExprWF := by
  intro a b c ha hb h
  rw [show eExpr.eq2 a b = expr.beq a b from rfl] at h
  rw [Expr.beq_refines ha hb h]
  exact decide_eq_decide.mpr
    ⟨fun hc => Expr.absExpr_injective ha hb hc, fun hc => by rw [hc]⟩

/-- The `constTyAt`/`constValAt` key, componentwise through `name::beq` and
`expr::levels_beq`. -/
theorem nameLevelsEq2Fwd : HashMap.Eq2Fwd eNameLevels NameLevelsWF := by
  intro a b c ha hb h
  obtain ⟨n, v⟩ := a
  obtain ⟨n1, v1⟩ := b
  rw [show eNameLevels.eq2 (n, v) (n1, v1)
      = (do let b ← name.beq n n1
            if b then expr.levels_beq v v1 else ok false) from rfl] at h
  refine decide_of_iff (Expr.guard_step
    (fun y hy => Name.beq_refines ha.1 hb.1 hy)
    (fun y hy => Expr.levels_beq_refines ha.2 hb.2 hy) h) ?_
  constructor
  · intro hc
    rw [Prod.mk.injEq]
    exact ⟨Name.absName_injective ha.1 hb.1 hc.1,
      Expr.absLevels_inj ha.2 hb.2 hc.2⟩
  · intro hc
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨rfl, rfl⟩

/-- The `ruleRhsAt` key; a Lean triple is `(a, (b, c))`, so the guard chain is
right-nested. -/
theorem nameNameLevelsEq2Fwd :
    HashMap.Eq2Fwd eNameNameLevels NameNameLevelsWF := by
  intro a b c ha hb h
  obtain ⟨n, n1, v⟩ := a
  obtain ⟨n2, n3, v1⟩ := b
  rw [show eNameNameLevels.eq2 (n, n1, v) (n2, n3, v1)
      = (do let b ← name.beq n n2
            if b then
              (do let b1 ← name.beq n1 n3
                  if b1 then expr.levels_beq v v1 else ok false)
            else ok false) from rfl] at h
  refine decide_of_iff (Expr.guard_step
    (fun y hy => Name.beq_refines ha.1 hb.1 hy)
    (fun y hy => Expr.guard_step
      (fun z hz => Name.beq_refines ha.2.1 hb.2.1 hz)
      (fun z hz => Expr.levels_beq_refines ha.2.2 hb.2.2 hz) hy) h) ?_
  constructor
  · intro hc
    simp only [Prod.mk.injEq]
    exact ⟨Name.absName_injective ha.1 hb.1 hc.1,
      Name.absName_injective ha.2.1 hb.2.1 hc.2.1,
      Expr.absLevels_inj ha.2.2 hb.2.2 hc.2.2⟩
  · intro hc
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨rfl, rfl, rfl⟩

/-- The `defeqC` key, `expr::beq` on both components. -/
theorem exprPairEq2Fwd : HashMap.Eq2Fwd eExprPair ExprPairWF := by
  intro a b c ha hb h
  obtain ⟨e, e1⟩ := a
  obtain ⟨e2, e3⟩ := b
  rw [show eExprPair.eq2 (e, e1) (e2, e3)
      = (do let b ← expr.beq e e2
            if b then expr.beq e1 e3 else ok false) from rfl] at h
  refine decide_of_iff (Expr.guard_step
    (fun y hy => Expr.beq_refines ha.1 hb.1 hy)
    (fun y hy => Expr.beq_refines ha.2 hb.2 hy) h) ?_
  constructor
  · intro hc
    rw [Prod.mk.injEq]
    exact ⟨Expr.absExpr_injective ha.1 hb.1 hc.1,
      Expr.absExpr_injective ha.2 hb.2 hc.2⟩
  · intro hc
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨rfl, rfl⟩

/-- The `eqvC` key, `level::beq` on both components. -/
theorem levelPairEq2Fwd : HashMap.Eq2Fwd eLevelPair LevelPairWF := by
  intro a b c ha hb h
  obtain ⟨l, l1⟩ := a
  obtain ⟨l2, l3⟩ := b
  rw [show eLevelPair.eq2 (l, l1) (l2, l3)
      = (do let b ← level.beq l l2
            if b then level.beq l1 l3 else ok false) from rfl] at h
  refine decide_of_iff (Expr.guard_step
    (fun y hy => Level.beq_refines ha.1 hb.1 hy)
    (fun y hy => Level.beq_refines ha.2 hb.2 hy) h) ?_
  constructor
  · intro hc
    rw [Prod.mk.injEq]
    exact ⟨Level.absLevel_injective ha.1 hb.1 hc.1,
      Level.absLevel_injective ha.2 hb.2 hc.2⟩
  · intro hc
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨rfl, rfl⟩

/-- The `instC` key: `expr::beq`, `state_c::exprs_beq`, and `==` on the `u64`
cursor. -/
theorem instKeyEq2Fwd : HashMap.Eq2Fwd eInstKey InstKeyWF := by
  intro a b c ha hb h
  obtain ⟨e, v, i⟩ := a
  obtain ⟨e1, v1, i1⟩ := b
  rw [show eInstKey.eq2 (e, v, i) (e1, v1, i1)
      = (do let b ← expr.beq e e1
            if b then
              (do let b1 ← cached.state_c.exprs_beq v v1
                  if b1 then ok (decide (i = i1)) else ok false)
            else ok false) from rfl] at h
  refine decide_of_iff (Expr.guard_step
    (fun y hy => Expr.beq_refines ha.1 hb.1 hy)
    (fun y hy => Expr.guard_step
      (fun z hz => exprs_beq_refines ha.2 hb.2 hz)
      (fun z hz => (Result.ok_injective hz).symm) hy) h) ?_
  constructor
  · intro hc
    simp only [Prod.mk.injEq]
    exact ⟨Expr.absExpr_injective ha.1 hb.1 hc.1,
      absExprs_inj ha.2 hb.2 hc.2.1, hc.2.2⟩
  · intro hc
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨rfl, rfl, rfl⟩

/-! ## What a memo key type has to satisfy

`KeyOk` bundles the two facts every `get`/`insert` lemma below needs of its key
type, and `get_step`/`insert_step` are `HashMapWF`'s `Rel_get_wf`/
`Rel_insert_wf` with them supplied plus the stored values' invariant threaded
through — which is what makes a memo *hit* hand its caller a well-formed
term. -/

/-- The key facts: `eq2` is exact on `P`-keys, and `absK` is injective on
them. -/
structure KeyOk {K K' : Type} [DecidableEq K] (P : K → Prop)
    (Eq2Inst : ron.hashmap.Eq2 K) (absK : K → K') : Prop where
  eq2 : HashMap.Eq2Fwd Eq2Inst P
  inj : ∀ a b, P a → P b → absK a = absK b → a = b

/-- The `ienv` key. -/
theorem nameKey : KeyOk NameWF eName absName :=
  ⟨nameEq2Fwd, fun _ _ ha hb h => Name.absName_injective ha hb h⟩

/-- The level memos' key. -/
theorem levelKey : KeyOk LevelWF eLevel absLevel :=
  ⟨levelEq2Fwd, fun _ _ ha hb h => Level.absLevel_injective ha hb h⟩

/-- The `Expr`-keyed memos' key. -/
theorem exprKey : KeyOk ExprWF eExpr absExpr :=
  ⟨exprEq2Fwd, fun _ _ ha hb h => Expr.absExpr_injective ha hb h⟩

/-- The `constTyAt`/`constValAt` key. -/
theorem nameLevelsKey : KeyOk NameLevelsWF eNameLevels absNameLevels := by
  refine ⟨nameLevelsEq2Fwd, ?_⟩
  intro a b ha hb h
  simp only [absNameLevels, Prod.mk.injEq] at h
  rw [Prod.ext_iff]
  exact ⟨Name.absName_injective ha.1 hb.1 h.1,
    Expr.absLevels_inj ha.2 hb.2 h.2⟩

/-- The `ruleRhsAt` key. -/
theorem nameNameLevelsKey :
    KeyOk NameNameLevelsWF eNameNameLevels absNameNameLevels := by
  refine ⟨nameNameLevelsEq2Fwd, ?_⟩
  intro a b ha hb h
  simp only [absNameNameLevels, Prod.mk.injEq] at h
  rw [Prod.ext_iff, Prod.ext_iff]
  exact ⟨Name.absName_injective ha.1 hb.1 h.1,
    Name.absName_injective ha.2.1 hb.2.1 h.2.1,
    Expr.absLevels_inj ha.2.2 hb.2.2 h.2.2⟩

/-- The `defeqC` key. -/
theorem exprPairKey : KeyOk ExprPairWF eExprPair absExprPair := by
  refine ⟨exprPairEq2Fwd, ?_⟩
  intro a b ha hb h
  simp only [absExprPair, Prod.mk.injEq] at h
  rw [Prod.ext_iff]
  exact ⟨Expr.absExpr_injective ha.1 hb.1 h.1,
    Expr.absExpr_injective ha.2 hb.2 h.2⟩

/-- The `eqvC` key. -/
theorem levelPairKey : KeyOk LevelPairWF eLevelPair absLevelPair := by
  refine ⟨levelPairEq2Fwd, ?_⟩
  intro a b ha hb h
  simp only [absLevelPair, Prod.mk.injEq] at h
  rw [Prod.ext_iff]
  exact ⟨Level.absLevel_injective ha.1 hb.1 h.1,
    Level.absLevel_injective ha.2 hb.2 h.2⟩

/-- The `instC` key. -/
theorem instKeyKey : KeyOk InstKeyWF eInstKey absInstKey := by
  refine ⟨instKeyEq2Fwd, ?_⟩
  intro a b ha hb h
  simp only [absInstKey, Prod.mk.injEq] at h
  rw [Prod.ext_iff, Prod.ext_iff]
  exact ⟨Expr.absExpr_injective ha.1 hb.1 h.1,
    absExprs_inj ha.2 hb.2 h.2.1, u64_val_inj h.2.2⟩

section Generic

variable {K V K' V' : Type} [DecidableEq K] [BEq K'] [Hashable K']
  {HashableInst : ron.hashmap.Hashable K} {Eq2Inst : ron.hashmap.Eq2 K}
  {P : K → Prop} {Q : V → Prop} {absK : K → K'} {absV : V → V'}
  {m m' : ron.hashmap.HashMap K V} {s : _root_.Std.HashMap K' V'}

/-- **One memo probe.**  The abstract lookup agrees, and a hit is a stored
value, hence well formed. -/
theorem get_step (hkey : KeyOk P Eq2Inst absK) (hinv : HashMap.Inv HashableInst m)
    (hkeys : HashMap.KeysOk P m) (hvals : ∀ p ∈ HashMap.al_v m, Q p.2)
    (hrel : HashMap.RelOn P m s absK absV) {k : K} (hk : P k) {o : Option V}
    (h : ron.hashmap.HashMap.get HashableInst Eq2Inst m k = ok o) :
    o.map absV = s[absK k]? ∧ ∀ r, o = some r → Q r := by
  refine ⟨HashMap.Rel_get_wf hkey.eq2 hinv hkeys hrel hk h, ?_⟩
  intro r hr
  have ho : (some r : Option V) = HashMap.lookupK (HashMap.al_v m) k := by
    rw [← hr]; exact HashMap.get_refines_wf hkey.eq2 hinv hkeys hk h
  exact hvals (k, r) (HashMap.lookupK_mem ho.symm)

/-- **One memo insert.**  The table invariant, the key restriction, the stored
values' invariant and the abstract map all survive. -/
theorem insert_step [LawfulBEq K'] [LawfulHashable K'] (hkey : KeyOk P Eq2Inst absK)
    (hinv : HashMap.Inv HashableInst m) (hkeys : HashMap.KeysOk P m)
    (hvals : ∀ p ∈ HashMap.al_v m, Q p.2)
    (hrel : HashMap.RelOn P m s absK absV) {k : K} {v : V} (hk : P k) (hv : Q v)
    {old : Option V}
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m')) :
    HashMap.Inv HashableInst m' ∧ HashMap.KeysOk P m' ∧
      (∀ p ∈ HashMap.al_v m', Q p.2) ∧
      HashMap.RelOn P m' (s.insert (absK k) (absV v)) absK absV := by
  obtain ⟨hinv', -, hupd, -⟩ :=
    HashMap.insert_refines_wf hkey.eq2 hinv hkeys hk h
  obtain ⟨hrel', hkeys'⟩ :=
    HashMap.Rel_insert_wf hkey.eq2 hkey.inj hinv hkeys hrel hk h
  refine ⟨hinv', hkeys', ?_, hrel'⟩
  intro p hp
  have hlk : HashMap.toFun m' p.1 = some p.2 :=
    HashMap.lookupK_eq_some_of_mem hinv'.nodup hp
  rw [hupd, Function.update_apply] at hlk
  by_cases hpk : p.1 = k
  · rw [if_pos hpk, Option.some.injEq] at hlk
    rw [← hlk]; exact hv
  · rw [if_neg hpk] at hlk
    exact hvals p (HashMap.lookupK_mem hlk)

/-! ### A fresh table

`ron::HashMap::new`'s three conclusions, split so that each clause of
`StateRel`/`StateWF` can be filled in where the goal fixes the implicits. -/

/-- A fresh table satisfies the `ron::HashMap` invariant. -/
theorem new_inv (h : ron.hashmap.HashMap.new K V = ok m) :
    HashMap.Inv HashableInst m := (HashMap.new_refines h).1

omit [DecidableEq K] in
/-- A fresh table holds nothing.  Proved from `new`'s record rather than
through `new_refines`, whose `Inv` clause would drag in a `Hashable`
dictionary these three conclusions do not mention. -/
theorem new_alv (h : ron.hashmap.HashMap.new K V = ok m) :
    HashMap.al_v m = [] := by
  have hm := Result.ok_injective h
  have hs : m.slots.val = [] := by rw [← hm]; rfl
  simp [HashMap.al_v, hs]

omit [DecidableEq K] in
/-- A fresh table's keys are (vacuously) restricted. -/
theorem new_keys (h : ron.hashmap.HashMap.new K V = ok m) :
    HashMap.KeysOk P m := by
  intro p hp; rw [new_alv h] at hp; simp at hp

omit [DecidableEq K] in
/-- A fresh table's values are (vacuously) well formed. -/
theorem new_vals (h : ron.hashmap.HashMap.new K V = ok m) :
    ∀ p ∈ HashMap.al_v m, Q p.2 := by
  intro p hp; rw [new_alv h] at hp; simp at hp

/-- A fresh table denotes con-leche's empty `Std.HashMap`. -/
theorem new_rel (h : ron.hashmap.HashMap.new K V = ok m) :
    HashMap.RelOn P m (∅ : _root_.Std.HashMap K' V') absK absV := by
  refine HashMap.RelOn_empty (fun k => ?_)
  show HashMap.lookupK (HashMap.al_v m) k = none
  rw [new_alv h]; rfl

/-- **One memo insert, on the count.**  The port's entry count follows
con-leche's `size` through an insert: both grow by one exactly when the key was
absent, and `RelOn` at the key is what makes "absent" the same question on the
two sides. -/
theorem insert_size_step [LawfulBEq K'] [LawfulHashable K']
    (hkey : KeyOk P Eq2Inst absK) (hinv : HashMap.Inv HashableInst m)
    (hkeys : HashMap.KeysOk P m) (hrel : HashMap.RelOn P m s absK absV)
    {k : K} {v : V} (hk : P k) {old : Option V}
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m'))
    (hsz : (HashMap.al_v m).length = s.size) :
    (HashMap.al_v m').length = (s.insert (absK k) (absV v)).size := by
  obtain ⟨hinv', -, hupd, hkeys'⟩ :=
    HashMap.insert_refines_wf hkey.eq2 hinv hkeys hk h
  -- the two sides' counts are the two key sets' cardinalities
  have hcard : (HashMap.al_v m').length = (HashMap.support m').card :=
    (HashMap.card_support hinv').symm
  have hcard0 : (HashMap.al_v m).length = (HashMap.support m).card :=
    (HashMap.card_support hinv).symm
  -- `support m' = insert k (support m)`
  have hsupp : HashMap.support m' = Insert.insert k (HashMap.support m) := by
    apply Finset.ext
    intro k'
    rw [HashMap.mem_support_iff, Finset.mem_insert, HashMap.mem_support_iff, hupd,
      Function.update_apply]
    by_cases hkk : k' = k
    · simp [hkk]
    · simp [hkk]
  -- "the key was absent" is the same question on the two sides
  have habs : (absK k ∈ s) ↔ k ∈ HashMap.support m := by
    have hlk := hrel k hk
    rw [HashMap.mem_support_iff, _root_.Std.HashMap.mem_iff_contains,
      _root_.Std.HashMap.contains_eq_isSome_getElem?, ← hlk]
    cases HashMap.toFun m k <;> simp
  rw [hcard, hsupp, _root_.Std.HashMap.size_insert]
  by_cases hmem : k ∈ HashMap.support m
  · rw [Finset.insert_eq_self.mpr hmem, if_pos (habs.mpr hmem), ← hcard0, hsz]
  · rw [Finset.card_insert_of_notMem hmem, if_neg (fun hc => hmem (habs.mp hc)),
      ← hcard0, hsz]

end Generic

/-! ## The two relations

`StateRel` is one `HashMap.RelOn` clause per map, in `CState`'s field order;
`StateWF` is, per map, the table invariant, the key restriction and — where the
values are terms — their well-formedness.  The last is what the knot's
induction needs: a memo hit must hand its caller an `ExprWF`/`LevelWF`
result. -/

/-- `ConLeche/Cached/StateC.lean:131-156` — the fourteen tables denote
con-leche's fourteen `Std.HashMap`s, key by key. -/
structure StateRel (st : cached.state_c.CState)
    (lst : ConLeche.Cached.CState) : Prop where
  ienv : HashMap.RelOn NameWF st.ienv lst.ienv absName absCConstE
  constTyAt : HashMap.RelOn NameLevelsWF st.const_ty_at lst.constTyAt
    absNameLevels absExpr
  constValAt : HashMap.RelOn NameLevelsWF st.const_val_at lst.constValAt
    absNameLevels absExpr
  ruleRhsAt : HashMap.RelOn NameNameLevelsWF st.rule_rhs_at lst.ruleRhsAt
    absNameNameLevels absExpr
  whnfCoreC : HashMap.RelOn ExprWF st.whnf_core_c lst.whnfCoreC absExpr absExpr
  whnfC : HashMap.RelOn ExprWF st.whnf_c lst.whnfC absExpr absExpr
  inferC : HashMap.RelOn ExprWF st.infer_c lst.inferC absExpr absExpr
  inferIOC : HashMap.RelOn ExprWF st.infer_io_c lst.inferIOC absExpr absExpr
  defeqC : HashMap.RelOn ExprPairWF st.defeq_c lst.defeqC absExprPair id
  annotC : HashMap.RelOn ExprWF st.annot_c lst.annotC absExpr absExpr
  lsimpC : HashMap.RelOn LevelWF st.lsimp_c lst.lsimpC absLevel absLevel
  lnzC : HashMap.RelOn LevelWF st.lnz_c lst.lnzC absLevel id
  eqvC : HashMap.RelOn LevelPairWF st.eqv_c lst.eqvC absLevelPair id
  instC : HashMap.RelOn InstKeyWF st.inst_c lst.instC absInstKey absExpr
  /-- The `instC` table's **entry count**, which the other thirteen clauses do
  not need: `StateRel` is a lookup agreement and a lookup agreement does not
  bound the Lean map's size.  `cached::state_c::inst_list_m` is the one
  operation that reads a count — the `instC` entry cap, `inst_c.len() <
  inst_c_cap_c` against `mp.size < instCCapC` (`StateC.lean:186-199`) — so
  without this clause the two sides can disagree about whether the table is
  full.  Task #61 folded it in (`Refine/StateC.lean` had it as a free-standing
  `InstCSize` hypothesis that nothing could discharge). -/
  instCSize : (HashMap.al_v st.inst_c).length = lst.instC.size

/-- The port-side invariant of the fourteen tables: each is a well-formed
`ron::HashMap` (task #16's `Inv`) holding only well-formed keys and — where the
values are terms — only well-formed values. -/
structure StateWF (st : cached.state_c.CState) : Prop where
  ienvInv : HashMap.Inv hName st.ienv
  ienvKeys : HashMap.KeysOk NameWF st.ienv
  ienvVals : ∀ p ∈ HashMap.al_v st.ienv, CConstEWF p.2
  constTyAtInv : HashMap.Inv hNameLevels st.const_ty_at
  constTyAtKeys : HashMap.KeysOk NameLevelsWF st.const_ty_at
  constTyAtVals : ∀ p ∈ HashMap.al_v st.const_ty_at, ExprWF p.2
  constValAtInv : HashMap.Inv hNameLevels st.const_val_at
  constValAtKeys : HashMap.KeysOk NameLevelsWF st.const_val_at
  constValAtVals : ∀ p ∈ HashMap.al_v st.const_val_at, ExprWF p.2
  ruleRhsAtInv : HashMap.Inv hNameNameLevels st.rule_rhs_at
  ruleRhsAtKeys : HashMap.KeysOk NameNameLevelsWF st.rule_rhs_at
  ruleRhsAtVals : ∀ p ∈ HashMap.al_v st.rule_rhs_at, ExprWF p.2
  whnfCoreCInv : HashMap.Inv hExpr st.whnf_core_c
  whnfCoreCKeys : HashMap.KeysOk ExprWF st.whnf_core_c
  whnfCoreCVals : ∀ p ∈ HashMap.al_v st.whnf_core_c, ExprWF p.2
  whnfCInv : HashMap.Inv hExpr st.whnf_c
  whnfCKeys : HashMap.KeysOk ExprWF st.whnf_c
  whnfCVals : ∀ p ∈ HashMap.al_v st.whnf_c, ExprWF p.2
  inferCInv : HashMap.Inv hExpr st.infer_c
  inferCKeys : HashMap.KeysOk ExprWF st.infer_c
  inferCVals : ∀ p ∈ HashMap.al_v st.infer_c, ExprWF p.2
  inferIOCInv : HashMap.Inv hExpr st.infer_io_c
  inferIOCKeys : HashMap.KeysOk ExprWF st.infer_io_c
  inferIOCVals : ∀ p ∈ HashMap.al_v st.infer_io_c, ExprWF p.2
  defeqCInv : HashMap.Inv hExprPair st.defeq_c
  defeqCKeys : HashMap.KeysOk ExprPairWF st.defeq_c
  annotCInv : HashMap.Inv hExpr st.annot_c
  annotCKeys : HashMap.KeysOk ExprWF st.annot_c
  annotCVals : ∀ p ∈ HashMap.al_v st.annot_c, ExprWF p.2
  lsimpCInv : HashMap.Inv hLevel st.lsimp_c
  lsimpCKeys : HashMap.KeysOk LevelWF st.lsimp_c
  lsimpCVals : ∀ p ∈ HashMap.al_v st.lsimp_c, LevelWF p.2
  lnzCInv : HashMap.Inv hLevel st.lnz_c
  lnzCKeys : HashMap.KeysOk LevelWF st.lnz_c
  eqvCInv : HashMap.Inv hLevelPair st.eqv_c
  eqvCKeys : HashMap.KeysOk LevelPairWF st.eqv_c
  instCInv : HashMap.Inv hInstKey st.inst_c
  instCKeys : HashMap.KeysOk InstKeyWF st.inst_c
  instCVals : ∀ p ∈ HashMap.al_v st.inst_c, ExprWF p.2

/-! ## The full outcome

DESIGN.md §3's ruling of 2026-09-13 (task #67): a refinement lemma is stated
over the Rust computation's *whole* outcome, not only its successes.

* `.Ok r` — con-leche's run ends `.ok` at the abstracted value, with the two
  states related and the port's state and result well-formed.  This is the
  accept-direction statement §3.5 had, unchanged.
* `.Err e` with `e` one of the three **mirrored** constructors — con-leche's
  run ends `.error` at the *same kind* (`Refine/Abs.lean`'s `ErrSim`;
  messages are never compared).  Nothing is claimed about the port's state
  after a failure, and nothing needs to be: con-leche's `Except` discards its
  state on a throw, so the only caller that continues past an error — the
  Nat-op pin loop — continues from a *pre-attempt* snapshot, which is related
  by the hypothesis rather than the conclusion.
* `.Err e` with `e` the port's own `Native` — nothing is claimed
  (`absErrKind` sends it to `none`, so `ErrSim` is vacuous).
* an Aeneas `fail`/`div` — nothing is claimed, since the hypothesis of every
  lemma is `f st = ok (…)`.

`Out` takes the con-leche side already `run`, as an `Except`, so that the
definition has no monad plumbing in it and `ErrSim`'s lemmas apply directly. -/

/-- The obligation a Rust outcome puts on con-leche's. -/
def Out {α β : Type} (A : α → β) (WF : α → Prop)
    (o : core.result.Result α kernel.core_types.CheckError)
    (st' : cached.state_c.CState)
    (x : Except ConLeche.CheckError (β × ConLeche.Cached.CState)) : Prop :=
  match o with
  | .Ok r => ∃ lst', x = .ok (A r, lst') ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r
  | .Err e => ErrSim e x

/-- The success half, as an introduction rule. -/
theorem Out.ok {α β : Type} {A : α → β} {WF : α → Prop} {r : α}
    {st' : cached.state_c.CState} {lst' : ConLeche.Cached.CState}
    {x : Except ConLeche.CheckError (β × ConLeche.Cached.CState)}
    (hx : x = .ok (A r, lst')) (hrel : StateRel st' lst') (hwf : StateWF st')
    (hr : WF r) : Out A WF (.Ok r) st' x :=
  ⟨lst', hx, hrel, hwf, hr⟩

/-- The failure half, as an introduction rule. -/
theorem Out.err {α β : Type} {A : α → β} {WF : α → Prop}
    {e : kernel.core_types.CheckError} {st' : cached.state_c.CState}
    {x : Except ConLeche.CheckError (β × ConLeche.Cached.CState)}
    (h : ErrSim e x) : Out A WF (.Err e) st' x := h

/-- The port's own failure claims nothing. -/
theorem Out.native {α β : Type} {A : α → β} {WF : α → Prop}
    {st' : cached.state_c.CState}
    {x : Except ConLeche.CheckError (β × ConLeche.Cached.CState)} (m) :
    Out A WF (.Err (.Native m)) st' x := ErrSim.native m

/-- What the success half gives at a call site. -/
theorem Out.dest {α β : Type} {A : α → β} {WF : α → Prop} {r : α}
    {st' : cached.state_c.CState}
    {x : Except ConLeche.CheckError (β × ConLeche.Cached.CState)}
    (h : Out A WF (.Ok r) st' x) :
    ∃ lst', x = .ok (A r, lst') ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r := h

/-- What the failure half gives at a call site. -/
theorem Out.destErr {α β : Type} {A : α → β} {WF : α → Prop}
    {e : kernel.core_types.CheckError} {st' : cached.state_c.CState}
    {x : Except ConLeche.CheckError (β × ConLeche.Cached.CState)}
    (h : Out A WF (.Err e) st' x) : ErrSim e x := h

/-- **Error propagation**: an outcome that failed makes every continuation of
it fail, on both sides.  The move every `do` block's error arm makes. -/
theorem Out.bind {α α' β δ : Type} {A : α → β} {WF : α → Prop}
    {e : kernel.core_types.CheckError} {st' : cached.state_c.CState}
    {x : Except ConLeche.CheckError (β × ConLeche.Cached.CState)}
    (h : Out A WF (.Err e) st' x)
    (f : β × ConLeche.Cached.CState →
      Except ConLeche.CheckError (δ × ConLeche.Cached.CState))
    {st'' : cached.state_c.CState} {B : α' → δ} {WF' : α' → Prop} :
    Out B WF' (.Err e) st'' (x >>= f) := ErrSim.bind h f


/-! ## The fresh state and the flush -/

/-- `ConLeche/Cached/StateC.lean:158` — `state_c::cstate_new` is the cited
`instance : Inhabited CState := ⟨{}⟩`: fourteen fresh tables, relating to
con-leche's fourteen empty ones. -/
theorem cstate_new_refines {st : cached.state_c.CState}
    (h : cached.state_c.cstate_new = ok st) :
    StateRel st ({} : ConLeche.Cached.CState) ∧ StateWF st := by
  rw [cached.state_c.cstate_new] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨m0, h0, m1, h1, m2, h2, m3, h3, m4, h4, m5, h5, m6, h6, m7, h7,
    m8, h8, hst⟩ := h
  subst hst
  exact ⟨⟨new_rel h0, new_rel h1, new_rel h1, new_rel h2, new_rel h3,
      new_rel h3, new_rel h3, new_rel h3, new_rel h4, new_rel h3, new_rel h5,
      new_rel h6, new_rel h7, new_rel h8,
      by show (HashMap.al_v m8).length = _; rw [new_alv h8]; simp⟩,
    ⟨new_inv h0, new_keys h0, new_vals h0,
      new_inv h1, new_keys h1, new_vals h1,
      new_inv h1, new_keys h1, new_vals h1,
      new_inv h2, new_keys h2, new_vals h2,
      new_inv h3, new_keys h3, new_vals h3,
      new_inv h3, new_keys h3, new_vals h3,
      new_inv h3, new_keys h3, new_vals h3,
      new_inv h3, new_keys h3, new_vals h3,
      new_inv h4, new_keys h4,
      new_inv h3, new_keys h3, new_vals h3,
      new_inv h5, new_keys h5, new_vals h5,
      new_inv h6, new_keys h6,
      new_inv h7, new_keys h7,
      new_inv h8, new_keys h8, new_vals h8⟩⟩

/-- `ConLeche/Cached/StateC.lean:394` — `state_c::flushed` refines
`CState.flushed`: the ten environment-dependent tables become fresh, and the
four environment-independent ones (`ienv` and the three level memos)
survive. -/
theorem flushed_refines {st st' : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} (hrel : StateRel st lst) (hwf : StateWF st)
    (h : cached.state_c.flushed st = ok st') :
    StateRel st' lst.flushed ∧ StateWF st' := by
  rw [cached.state_c.flushed] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨m0, h0, m1, h1, m2, h2, m3, h3, m4, h4, hst⟩ := h
  subst hst
  exact ⟨⟨hrel.ienv, new_rel h0, new_rel h0, new_rel h1, new_rel h2,
      new_rel h2, new_rel h2, new_rel h2, new_rel h3, new_rel h2,
      hrel.lsimpC, hrel.lnzC, hrel.eqvC, new_rel h4,
      by
        show (HashMap.al_v m4).length = _
        rw [new_alv h4]
        simp [ConLeche.Cached.CState.flushed]⟩,
    ⟨hwf.ienvInv, hwf.ienvKeys, hwf.ienvVals,
      new_inv h0, new_keys h0, new_vals h0,
      new_inv h0, new_keys h0, new_vals h0,
      new_inv h1, new_keys h1, new_vals h1,
      new_inv h2, new_keys h2, new_vals h2,
      new_inv h2, new_keys h2, new_vals h2,
      new_inv h2, new_keys h2, new_vals h2,
      new_inv h2, new_keys h2, new_vals h2,
      new_inv h3, new_keys h3,
      new_inv h2, new_keys h2, new_vals h2,
      hwf.lsimpCInv, hwf.lsimpCKeys, hwf.lsimpCVals,
      hwf.lnzCInv, hwf.lnzCKeys,
      hwf.eqvCInv, hwf.eqvCKeys,
      new_inv h4, new_keys h4, new_vals h4⟩⟩

/-! ## The probes

The nine `*_probe` functions of `state_c.rs`, then the six memos the knot
reads (`cached::core_c`'s own `whnf_core_probe`, `whnf_probe`, `infer_probe`,
`infer_io_probe`, `defeq_probe`, `annot_probe`, whose bodies are a `get` on the
state field and a copy) — those six are stated over the field directly, which
is the ingredient `Refine/Core/*` needs.  Each says: what the Rust hands back
is the abstract lookup, and — where the value is a term — it is well formed.
The probes that answer a *copy* (`level::dup`, `expr::dup`) are the identity in
the model (DESIGN.md §3.2). -/

/-- `ConLeche/Cached/StateC.lean:312-320` — `state_c::ienv_ty_probe` is the
cited `s.ienv[n]?` at the entry's type half. -/
theorem ienv_ty_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {n : name.Name}
    {o : Option (expr.Expr × expr.Expr)} (hrel : StateRel st lst)
    (hwf : StateWF st) (hn : NameWF n)
    (h : cached.state_c.ienv_ty_probe st n = ok o) :
    o.map (fun p => (absExpr p.1, absExpr p.2))
        = (lst.ienv[absName n]?).map (fun c => (c.tyE, c.ty)) ∧
      ∀ p, o = some p → ExprWF p.1 ∧ ExprWF p.2 := by
  rw [cached.state_c.ienv_ty_probe] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hr, hv⟩ := get_step nameKey hwf.ienvInv hwf.ienvKeys hwf.ienvVals
    hrel.ienv hn hget
  cases o' with
  | none =>
    simp only [Option.map_none, Result.ok.injEq] at h hr
    subst h
    exact ⟨by rw [← hr]; rfl, by simp⟩
  | some ent =>
    simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    subst h
    obtain ⟨hty_e, hty, -⟩ := hv ent rfl
    refine ⟨by rw [← hr]; rfl, ?_⟩
    intro p hp
    simp only [Option.some.injEq] at hp
    subst hp
    exact ⟨hty_e, hty⟩

/-- `ConLeche/Cached/StateC.lean:322-330` — `state_c::ienv_val_probe` is the
cited `s.ienv[n]?` at the entry's *value* half (`none` where the entry carries
no value). -/
theorem ienv_val_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {n : name.Name}
    {o : Option (expr.Expr × expr.Expr)} (hrel : StateRel st lst)
    (hwf : StateWF st) (hn : NameWF n)
    (h : cached.state_c.ienv_val_probe st n = ok o) :
    o.map (fun p => (absExpr p.1, absExpr p.2))
        = (lst.ienv[absName n]?).bind (fun c => c.val) ∧
      ∀ p, o = some p → ExprWF p.1 ∧ ExprWF p.2 := by
  rw [cached.state_c.ienv_val_probe] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hr, hv⟩ := get_step nameKey hwf.ienvInv hwf.ienvKeys hwf.ienvVals
    hrel.ienv hn hget
  cases o' with
  | none =>
    simp only [Option.map_none, Result.ok.injEq] at h hr
    subst h
    exact ⟨by rw [← hr]; rfl, by simp⟩
  | some ent =>
    obtain ⟨-, -, hval⟩ := hv ent rfl
    simp only [] at h
    split at h
    · rename_i hc
      simp only [Result.ok.injEq] at h
      subst h
      refine ⟨?_, by simp⟩
      rw [← hr]
      simp [absCConstE, hc]
    · rename_i q hc
      obtain ⟨q1, q2⟩ := q
      have h2 : (do let e2 ← expr.dup q1
                    let e3 ← expr.dup q2
                    ok (some (e2, e3))) = ok o := h
      simp only [expr_dup_eq, bind_tc_ok, Result.ok.injEq] at h2
      subst h2
      obtain ⟨hq1, hq2⟩ := hval (q1, q2) hc
      refine ⟨?_, ?_⟩
      · rw [← hr]
        simp [absCConstE, hc]
      · intro p hp
        simp only [Option.some.injEq] at hp
        subst hp
        exact ⟨hq1, hq2⟩

/-- `ConLeche/Cached/StateC.lean:332-349` — `state_c::const_ty_at_probe` is the
cited `s.constTyAt[(n, us)]?`. -/
theorem const_ty_at_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState}
    {k : name.Name × alloc.vec.Vec level.Level} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (hk : NameLevelsWF k)
    (h : cached.state_c.const_ty_at_probe st k = ok o) :
    o.map absExpr = lst.constTyAt[absNameLevels k]? ∧
      ∀ r, o = some r → ExprWF r := by
  rw [cached.state_c.const_ty_at_probe] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hr, hv⟩ := get_step nameLevelsKey hwf.constTyAtInv
    hwf.constTyAtKeys hwf.constTyAtVals hrel.constTyAt hk hget
  cases o' with
  | none => simp only [Result.ok.injEq] at h; subst h; exact ⟨hr, by simp⟩
  | some r =>
    simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    subst h
    exact ⟨hr, fun r' hr' => by
      simp only [Option.some.injEq] at hr'; subst hr'; exact hv r rfl⟩

/-- `ConLeche/Cached/StateC.lean:351-367` — `state_c::const_val_at_probe`. -/
theorem const_val_at_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState}
    {k : name.Name × alloc.vec.Vec level.Level} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (hk : NameLevelsWF k)
    (h : cached.state_c.const_val_at_probe st k = ok o) :
    o.map absExpr = lst.constValAt[absNameLevels k]? ∧
      ∀ r, o = some r → ExprWF r := by
  rw [cached.state_c.const_val_at_probe] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hr, hv⟩ := get_step nameLevelsKey hwf.constValAtInv
    hwf.constValAtKeys hwf.constValAtVals hrel.constValAt hk hget
  cases o' with
  | none => simp only [Result.ok.injEq] at h; subst h; exact ⟨hr, by simp⟩
  | some r =>
    simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    subst h
    exact ⟨hr, fun r' hr' => by
      simp only [Option.some.injEq] at hr'; subst hr'; exact hv r rfl⟩

/-- `ConLeche/Cached/StateC.lean:369-388` — `state_c::rule_rhs_at_probe`. -/
theorem rule_rhs_at_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState}
    {k : name.Name × name.Name × alloc.vec.Vec level.Level}
    {o : Option expr.Expr} (hrel : StateRel st lst) (hwf : StateWF st)
    (hk : NameNameLevelsWF k)
    (h : cached.state_c.rule_rhs_at_probe st k = ok o) :
    o.map absExpr = lst.ruleRhsAt[absNameNameLevels k]? ∧
      ∀ r, o = some r → ExprWF r := by
  rw [cached.state_c.rule_rhs_at_probe] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hr, hv⟩ := get_step nameNameLevelsKey hwf.ruleRhsAtInv
    hwf.ruleRhsAtKeys hwf.ruleRhsAtVals hrel.ruleRhsAt hk hget
  cases o' with
  | none => simp only [Result.ok.injEq] at h; subst h; exact ⟨hr, by simp⟩
  | some r =>
    simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    subst h
    exact ⟨hr, fun r' hr' => by
      simp only [Option.some.injEq] at hr'; subst hr'; exact hv r rfl⟩

/-- `ConLeche/Cached/StateC.lean:240-248` — `state_c::lsimp_probe` is the cited
`s.lsimpC[u]?`, answering a `level::dup` of the hit. -/
theorem lsimp_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {u : level.Level} {o : Option level.Level}
    (hrel : StateRel st lst) (hwf : StateWF st) (hu : LevelWF u)
    (h : cached.state_c.lsimp_probe st u = ok o) :
    o.map absLevel = lst.lsimpC[absLevel u]? ∧ ∀ r, o = some r → LevelWF r := by
  rw [cached.state_c.lsimp_probe] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hr, hv⟩ := get_step levelKey hwf.lsimpCInv hwf.lsimpCKeys
    hwf.lsimpCVals hrel.lsimpC hu hget
  cases o' with
  | none => simp only [Result.ok.injEq] at h; subst h; exact ⟨hr, by simp⟩
  | some r =>
    simp only [level_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    subst h
    exact ⟨hr, fun r' hr' => by
      simp only [Option.some.injEq] at hr'; subst hr'; exact hv r rfl⟩

/-- `ConLeche/Cached/StateC.lean:251-259` — `state_c::lnz_probe` is the cited
`s.lnzC[u]?`. -/
theorem lnz_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {u : level.Level} {o : Option Bool}
    (hrel : StateRel st lst) (hwf : StateWF st) (hu : LevelWF u)
    (h : cached.state_c.lnz_probe st u = ok o) :
    o = lst.lnzC[absLevel u]? := by
  rw [cached.state_c.lnz_probe] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  have hr := (get_step (Q := fun _ => True) levelKey hwf.lnzCInv hwf.lnzCKeys
    (fun _ _ => trivial) hrel.lnzC hu hget).1
  cases o' with
  | none => simp only [Result.ok.injEq] at h; subst h; simpa using hr
  | some b => simp only [Result.ok.injEq] at h; subst h; simpa using hr

/-- `ConLeche/Cached/StateC.lean:270-298` — `state_c::eqv_probe` is the cited
`s.eqvC[(l, r)]?`. -/
theorem eqv_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {k : level.Level × level.Level}
    {o : Option Bool} (hrel : StateRel st lst) (hwf : StateWF st)
    (hk : LevelPairWF k) (h : cached.state_c.eqv_probe st k = ok o) :
    o = lst.eqvC[absLevelPair k]? := by
  rw [cached.state_c.eqv_probe] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  have hr := (get_step (Q := fun _ => True) levelPairKey hwf.eqvCInv
    hwf.eqvCKeys (fun _ _ => trivial) hrel.eqvC hk hget).1
  cases o' with
  | none => simp only [Result.ok.injEq] at h; subst h; simpa using hr
  | some b => simp only [Result.ok.injEq] at h; subst h; simpa using hr

/-- `ConLeche/Cached/StateC.lean:186-199` — `state_c::inst_c_probe` is the
cited `s.instC[(e, vs, d)]?`. -/
theorem inst_c_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState}
    {k : expr.Expr × alloc.vec.Vec expr.Expr × Std.U64} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (hk : InstKeyWF k)
    (h : cached.state_c.inst_c_probe st k = ok o) :
    o.map absExpr = lst.instC[absInstKey k]? ∧ ∀ r, o = some r → ExprWF r := by
  rw [cached.state_c.inst_c_probe] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hr, hv⟩ := get_step instKeyKey hwf.instCInv hwf.instCKeys
    hwf.instCVals hrel.instC hk hget
  cases o' with
  | none => simp only [Result.ok.injEq] at h; subst h; exact ⟨hr, by simp⟩
  | some r =>
    simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    subst h
    exact ⟨hr, fun r' hr' => by
      simp only [Option.some.injEq] at hr'; subst hr'; exact hv r rfl⟩

/-- The `whnfCoreC` memo lookup behind `core_c::whnf_core_probe`. -/
theorem whnf_core_c_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e : expr.Expr} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (he : ExprWF e)
    (h : ron.hashmap.HashMap.get hExpr eExpr st.whnf_core_c e = ok o) :
    o.map absExpr = lst.whnfCoreC[absExpr e]? ∧ ∀ r, o = some r → ExprWF r :=
  get_step exprKey hwf.whnfCoreCInv hwf.whnfCoreCKeys hwf.whnfCoreCVals
    hrel.whnfCoreC he h

/-- The `whnfC` memo lookup behind `core_c::whnf_probe`. -/
theorem whnf_c_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e : expr.Expr} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (he : ExprWF e)
    (h : ron.hashmap.HashMap.get hExpr eExpr st.whnf_c e = ok o) :
    o.map absExpr = lst.whnfC[absExpr e]? ∧ ∀ r, o = some r → ExprWF r :=
  get_step exprKey hwf.whnfCInv hwf.whnfCKeys hwf.whnfCVals hrel.whnfC he h

/-- The `inferC` memo lookup behind `core_c::infer_probe`. -/
theorem infer_c_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e : expr.Expr} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (he : ExprWF e)
    (h : ron.hashmap.HashMap.get hExpr eExpr st.infer_c e = ok o) :
    o.map absExpr = lst.inferC[absExpr e]? ∧ ∀ r, o = some r → ExprWF r :=
  get_step exprKey hwf.inferCInv hwf.inferCKeys hwf.inferCVals hrel.inferC he h

/-- The `inferIOC` memo lookup behind `core_c::infer_io_probe` (the io-grade
inference memo, kept apart from `inferC` per con-leche's task-#170 ruling). -/
theorem infer_io_c_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e : expr.Expr} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (he : ExprWF e)
    (h : ron.hashmap.HashMap.get hExpr eExpr st.infer_io_c e = ok o) :
    o.map absExpr = lst.inferIOC[absExpr e]? ∧ ∀ r, o = some r → ExprWF r :=
  get_step exprKey hwf.inferIOCInv hwf.inferIOCKeys hwf.inferIOCVals
    hrel.inferIOC he h

/-- The `annotC` memo lookup behind `core_c::annot_probe`. -/
theorem annot_c_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e : expr.Expr} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (he : ExprWF e)
    (h : ron.hashmap.HashMap.get hExpr eExpr st.annot_c e = ok o) :
    o.map absExpr = lst.annotC[absExpr e]? ∧ ∀ r, o = some r → ExprWF r :=
  get_step exprKey hwf.annotCInv hwf.annotCKeys hwf.annotCVals hrel.annotC he h

/-- The `defeqC` memo lookup behind `core_c::defeq_probe`; its value is a
`Bool`, so there is nothing to be well formed. -/
theorem defeq_c_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {k : expr.Expr × expr.Expr}
    {o : Option Bool} (hrel : StateRel st lst) (hwf : StateWF st)
    (hk : ExprPairWF k)
    (h : ron.hashmap.HashMap.get hExprPair eExprPair st.defeq_c k = ok o) :
    o = lst.defeqC[absExprPair k]? := by
  have hr := (get_step (Q := fun _ => True) exprPairKey hwf.defeqCInv
    hwf.defeqCKeys (fun _ _ => trivial) hrel.defeqC hk h).1
  simpa using hr

/-! ## The inserts

One per map: the table the Rust writes, together with con-leche's
`Std.HashMap.insert` at the abstracted key and value, is again a
`StateRel`/`StateWF` pair.  Each is `insert_step` at the map's `KeyOk`, and the
other thirteen clauses of both records are carried over unchanged. -/

/-- `ConLeche/Cached/StateC.lean:455-460` — `recordCConst`'s `ienv` insert. -/
theorem ienv_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {n : name.Name}
    {c : cached.state_c.CConstE} {old : Option cached.state_c.CConstE}
    {m' : ron.hashmap.HashMap name.Name cached.state_c.CConstE}
    (hrel : StateRel st lst) (hwf : StateWF st) (hn : NameWF n)
    (hc : CConstEWF c)
    (h : ron.hashmap.HashMap.insert hName eName st.ienv n c = ok (old, m')) :
    StateRel { st with ienv := m' }
        { lst with ienv := lst.ienv.insert (absName n) (absCConstE c) } ∧
      StateWF { st with ienv := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step nameKey hwf.ienvInv hwf.ienvKeys
    hwf.ienvVals hrel.ienv hn hc h
  exact ⟨{ hrel with ienv := h4 },
    { hwf with ienvInv := h1, ienvKeys := h2, ienvVals := h3 }⟩

/-- `ConLeche/Cached/StateC.lean:332-349` — `constTyAtM`'s insert. -/
theorem const_ty_at_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState}
    {k : name.Name × alloc.vec.Vec level.Level} {v : expr.Expr}
    {old : Option expr.Expr}
    {m' : ron.hashmap.HashMap (name.Name × alloc.vec.Vec level.Level) expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (hk : NameLevelsWF k)
    (hv : ExprWF v)
    (h : ron.hashmap.HashMap.insert hNameLevels eNameLevels st.const_ty_at k v
      = ok (old, m')) :
    StateRel { st with const_ty_at := m' }
        { lst with constTyAt :=
            lst.constTyAt.insert (absNameLevels k) (absExpr v) } ∧
      StateWF { st with const_ty_at := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step nameLevelsKey hwf.constTyAtInv
    hwf.constTyAtKeys hwf.constTyAtVals hrel.constTyAt hk hv h
  exact ⟨{ hrel with constTyAt := h4 },
    { hwf with constTyAtInv := h1, constTyAtKeys := h2, constTyAtVals := h3 }⟩

/-- `ConLeche/Cached/StateC.lean:351-367` — `constValAtM`'s insert. -/
theorem const_val_at_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState}
    {k : name.Name × alloc.vec.Vec level.Level} {v : expr.Expr}
    {old : Option expr.Expr}
    {m' : ron.hashmap.HashMap (name.Name × alloc.vec.Vec level.Level) expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (hk : NameLevelsWF k)
    (hv : ExprWF v)
    (h : ron.hashmap.HashMap.insert hNameLevels eNameLevels st.const_val_at k v
      = ok (old, m')) :
    StateRel { st with const_val_at := m' }
        { lst with constValAt :=
            lst.constValAt.insert (absNameLevels k) (absExpr v) } ∧
      StateWF { st with const_val_at := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step nameLevelsKey hwf.constValAtInv
    hwf.constValAtKeys hwf.constValAtVals hrel.constValAt hk hv h
  exact ⟨{ hrel with constValAt := h4 },
    { hwf with constValAtInv := h1, constValAtKeys := h2,
               constValAtVals := h3 }⟩

/-- `ConLeche/Cached/StateC.lean:369-388` — `ruleRhsAtM`'s insert. -/
theorem rule_rhs_at_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState}
    {k : name.Name × name.Name × alloc.vec.Vec level.Level} {v : expr.Expr}
    {old : Option expr.Expr}
    {m' : ron.hashmap.HashMap
      (name.Name × name.Name × alloc.vec.Vec level.Level) expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (hk : NameNameLevelsWF k)
    (hv : ExprWF v)
    (h : ron.hashmap.HashMap.insert hNameNameLevels eNameNameLevels
      st.rule_rhs_at k v = ok (old, m')) :
    StateRel { st with rule_rhs_at := m' }
        { lst with ruleRhsAt :=
            lst.ruleRhsAt.insert (absNameNameLevels k) (absExpr v) } ∧
      StateWF { st with rule_rhs_at := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step nameNameLevelsKey hwf.ruleRhsAtInv
    hwf.ruleRhsAtKeys hwf.ruleRhsAtVals hrel.ruleRhsAt hk hv h
  exact ⟨{ hrel with ruleRhsAt := h4 },
    { hwf with ruleRhsAtInv := h1, ruleRhsAtKeys := h2, ruleRhsAtVals := h3 }⟩

/-- The `whnfCoreC` memo insert. -/
theorem whnf_core_c_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e v : expr.Expr} {old : Option expr.Expr}
    {m' : ron.hashmap.HashMap expr.Expr expr.Expr} (hrel : StateRel st lst)
    (hwf : StateWF st) (he : ExprWF e) (hv : ExprWF v)
    (h : ron.hashmap.HashMap.insert hExpr eExpr st.whnf_core_c e v
      = ok (old, m')) :
    StateRel { st with whnf_core_c := m' }
        { lst with whnfCoreC :=
            lst.whnfCoreC.insert (absExpr e) (absExpr v) } ∧
      StateWF { st with whnf_core_c := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step exprKey hwf.whnfCoreCInv
    hwf.whnfCoreCKeys hwf.whnfCoreCVals hrel.whnfCoreC he hv h
  exact ⟨{ hrel with whnfCoreC := h4 },
    { hwf with whnfCoreCInv := h1, whnfCoreCKeys := h2, whnfCoreCVals := h3 }⟩

/-- The `whnfC` memo insert. -/
theorem whnf_c_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e v : expr.Expr} {old : Option expr.Expr}
    {m' : ron.hashmap.HashMap expr.Expr expr.Expr} (hrel : StateRel st lst)
    (hwf : StateWF st) (he : ExprWF e) (hv : ExprWF v)
    (h : ron.hashmap.HashMap.insert hExpr eExpr st.whnf_c e v = ok (old, m')) :
    StateRel { st with whnf_c := m' }
        { lst with whnfC := lst.whnfC.insert (absExpr e) (absExpr v) } ∧
      StateWF { st with whnf_c := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step exprKey hwf.whnfCInv hwf.whnfCKeys
    hwf.whnfCVals hrel.whnfC he hv h
  exact ⟨{ hrel with whnfC := h4 },
    { hwf with whnfCInv := h1, whnfCKeys := h2, whnfCVals := h3 }⟩

/-- The `inferC` memo insert. -/
theorem infer_c_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e v : expr.Expr} {old : Option expr.Expr}
    {m' : ron.hashmap.HashMap expr.Expr expr.Expr} (hrel : StateRel st lst)
    (hwf : StateWF st) (he : ExprWF e) (hv : ExprWF v)
    (h : ron.hashmap.HashMap.insert hExpr eExpr st.infer_c e v = ok (old, m')) :
    StateRel { st with infer_c := m' }
        { lst with inferC := lst.inferC.insert (absExpr e) (absExpr v) } ∧
      StateWF { st with infer_c := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step exprKey hwf.inferCInv hwf.inferCKeys
    hwf.inferCVals hrel.inferC he hv h
  exact ⟨{ hrel with inferC := h4 },
    { hwf with inferCInv := h1, inferCKeys := h2, inferCVals := h3 }⟩

/-- The `inferIOC` memo insert. -/
theorem infer_io_c_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e v : expr.Expr} {old : Option expr.Expr}
    {m' : ron.hashmap.HashMap expr.Expr expr.Expr} (hrel : StateRel st lst)
    (hwf : StateWF st) (he : ExprWF e) (hv : ExprWF v)
    (h : ron.hashmap.HashMap.insert hExpr eExpr st.infer_io_c e v
      = ok (old, m')) :
    StateRel { st with infer_io_c := m' }
        { lst with inferIOC := lst.inferIOC.insert (absExpr e) (absExpr v) } ∧
      StateWF { st with infer_io_c := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step exprKey hwf.inferIOCInv
    hwf.inferIOCKeys hwf.inferIOCVals hrel.inferIOC he hv h
  exact ⟨{ hrel with inferIOC := h4 },
    { hwf with inferIOCInv := h1, inferIOCKeys := h2, inferIOCVals := h3 }⟩

/-- The `defeqC` memo insert; the value is a `Bool`. -/
theorem defeq_c_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {k : expr.Expr × expr.Expr} {b : Bool}
    {old : Option Bool}
    {m' : ron.hashmap.HashMap (expr.Expr × expr.Expr) Bool}
    (hrel : StateRel st lst) (hwf : StateWF st) (hk : ExprPairWF k)
    (h : ron.hashmap.HashMap.insert hExprPair eExprPair st.defeq_c k b
      = ok (old, m')) :
    StateRel { st with defeq_c := m' }
        { lst with defeqC := lst.defeqC.insert (absExprPair k) b } ∧
      StateWF { st with defeq_c := m' } := by
  obtain ⟨h1, h2, -, h4⟩ := insert_step (Q := fun _ => True) exprPairKey
    hwf.defeqCInv hwf.defeqCKeys (fun _ _ => trivial) hrel.defeqC hk trivial h
  exact ⟨{ hrel with defeqC := h4 },
    { hwf with defeqCInv := h1, defeqCKeys := h2 }⟩

/-- The `annotC` memo insert. -/
theorem annot_c_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e v : expr.Expr} {old : Option expr.Expr}
    {m' : ron.hashmap.HashMap expr.Expr expr.Expr} (hrel : StateRel st lst)
    (hwf : StateWF st) (he : ExprWF e) (hv : ExprWF v)
    (h : ron.hashmap.HashMap.insert hExpr eExpr st.annot_c e v = ok (old, m')) :
    StateRel { st with annot_c := m' }
        { lst with annotC := lst.annotC.insert (absExpr e) (absExpr v) } ∧
      StateWF { st with annot_c := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step exprKey hwf.annotCInv hwf.annotCKeys
    hwf.annotCVals hrel.annotC he hv h
  exact ⟨{ hrel with annotC := h4 },
    { hwf with annotCInv := h1, annotCKeys := h2, annotCVals := h3 }⟩

/-- `ConLeche/Cached/StateC.lean:240-248` — `simplifyLM`'s `lsimpC` insert. -/
theorem lsimp_c_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {u v : level.Level}
    {old : Option level.Level}
    {m' : ron.hashmap.HashMap level.Level level.Level}
    (hrel : StateRel st lst) (hwf : StateWF st) (hu : LevelWF u)
    (hv : LevelWF v)
    (h : ron.hashmap.HashMap.insert hLevel eLevel st.lsimp_c u v
      = ok (old, m')) :
    StateRel { st with lsimp_c := m' }
        { lst with lsimpC := lst.lsimpC.insert (absLevel u) (absLevel v) } ∧
      StateWF { st with lsimp_c := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step levelKey hwf.lsimpCInv hwf.lsimpCKeys
    hwf.lsimpCVals hrel.lsimpC hu hv h
  exact ⟨{ hrel with lsimpC := h4 },
    { hwf with lsimpCInv := h1, lsimpCKeys := h2, lsimpCVals := h3 }⟩

/-- `ConLeche/Cached/StateC.lean:251-259` — `isNonZeroLM`'s `lnzC` insert. -/
theorem lnz_c_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {u : level.Level} {b : Bool}
    {old : Option Bool} {m' : ron.hashmap.HashMap level.Level Bool}
    (hrel : StateRel st lst) (hwf : StateWF st) (hu : LevelWF u)
    (h : ron.hashmap.HashMap.insert hLevel eLevel st.lnz_c u b
      = ok (old, m')) :
    StateRel { st with lnz_c := m' }
        { lst with lnzC := lst.lnzC.insert (absLevel u) b } ∧
      StateWF { st with lnz_c := m' } := by
  obtain ⟨h1, h2, -, h4⟩ := insert_step (Q := fun _ => True) levelKey
    hwf.lnzCInv hwf.lnzCKeys (fun _ _ => trivial) hrel.lnzC hu trivial h
  exact ⟨{ hrel with lnzC := h4 }, { hwf with lnzCInv := h1, lnzCKeys := h2 }⟩

/-- `ConLeche/Cached/StateC.lean:270-298` — `isEquivLM`'s `eqvC` insert. -/
theorem eqv_c_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {k : level.Level × level.Level} {b : Bool}
    {old : Option Bool}
    {m' : ron.hashmap.HashMap (level.Level × level.Level) Bool}
    (hrel : StateRel st lst) (hwf : StateWF st) (hk : LevelPairWF k)
    (h : ron.hashmap.HashMap.insert hLevelPair eLevelPair st.eqv_c k b
      = ok (old, m')) :
    StateRel { st with eqv_c := m' }
        { lst with eqvC := lst.eqvC.insert (absLevelPair k) b } ∧
      StateWF { st with eqv_c := m' } := by
  obtain ⟨h1, h2, -, h4⟩ := insert_step (Q := fun _ => True) levelPairKey
    hwf.eqvCInv hwf.eqvCKeys (fun _ _ => trivial) hrel.eqvC hk trivial h
  exact ⟨{ hrel with eqvC := h4 }, { hwf with eqvCInv := h1, eqvCKeys := h2 }⟩

/-- `ConLeche/Cached/StateC.lean:186-199` — `instListM`'s `instC` insert.  The
entry cap the cited function applies *before* the insert is out of scope here
(`Refine/StateC.lean`); this is the insert itself. -/
theorem inst_c_insert_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState}
    {k : expr.Expr × alloc.vec.Vec expr.Expr × Std.U64} {v : expr.Expr}
    {old : Option expr.Expr}
    {m' : ron.hashmap.HashMap
      (expr.Expr × alloc.vec.Vec expr.Expr × Std.U64) expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (hk : InstKeyWF k)
    (hv : ExprWF v)
    (h : ron.hashmap.HashMap.insert hInstKey eInstKey st.inst_c k v
      = ok (old, m')) :
    StateRel { st with inst_c := m' }
        { lst with instC := lst.instC.insert (absInstKey k) (absExpr v) } ∧
      StateWF { st with inst_c := m' } := by
  obtain ⟨h1, h2, h3, h4⟩ := insert_step instKeyKey hwf.instCInv hwf.instCKeys
    hwf.instCVals hrel.instC hk hv h
  refine ⟨{ hrel with instC := h4, instCSize := ?_ },
    { hwf with instCInv := h1, instCKeys := h2, instCVals := h3 }⟩
  exact insert_size_step instKeyKey hwf.instCInv hwf.instCKeys hrel.instC hk h
    hrel.instCSize

end ConRon.Refine.State

/-! ## Axiom census

Lean's own three, `Classical.choice` among them: `DecidableEq` on the
generated key types is classical (`Refine/Abs.lean`), which is what every
`decide (a = b)` inside `Eq2Fwd`, `toFun` and `RelOn` goes through.  Nothing
reaches `kernel::pins_text::PINS_TEXT`'s `native_decide` (task #43). -/

/-- info: 'ConRon.Refine.State.cstate_new_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.State.cstate_new_refines

/-- info: 'ConRon.Refine.State.flushed_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.State.flushed_refines

/-- info: 'ConRon.Refine.State.lsimp_probe_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.State.lsimp_probe_refines

/-- info: 'ConRon.Refine.State.whnf_core_c_insert_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.State.whnf_core_c_insert_refines
