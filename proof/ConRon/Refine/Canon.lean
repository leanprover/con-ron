/-
`kernel::canon`, refined (DESIGN.md §3.5, task #83).

`crates/con-ron-core/src/kernel/canon.rs` is the port of
`vendor/con-leche/ConLeche/Kernel/Canon.lean`: the level-parameter canonical
form the pinned basis blocks are matched up to.

**Why `canon` exists at all.**  Lean's exporter picks binder names, binder
annotations and level-parameter names freely, so a stream's `Nat` block is the
checker's pinned one only *up to* renaming level parameters and erasing binder
metadata.  `canonExpr`/`ConstantInfo.canon` are that renaming, and everything
in this file is about deciding equality of two canonical forms.

**Why the port carries the `Fast` walks and not the specifications.**
con-leche spells each comparison twice: `ConstantVal.canonEq`,
`ConstantInfo.canonEq` and `canonEqList` are `decide (canon x = canon y)` --
the SPECIFICATIONS -- and `canonExprEqFast`, `ConstantVal.canonEqFast`,
`canonRulesEqFast`, `ConstantInfo.canonEqFast`, `canonEqListFast` are lockstep
twins that descend the two terms **together** and stop at the first
disagreement; `@[csimp]` swaps each pair.  Building `canon` of the *stream*
side rebuilds every node, which unshares its DAG:
`vendor/con-leche/tests/e2e/tower_quot.ndjson` is a depth-60 shared tower
(`2^60` nodes unshared) and the specification exhausts memory on it.  The port
therefore carries only the twins, and the refinement route is the same shape:
the Rust walk refines the Lean `*Fast` walk by structural induction, and
con-leche's own `canonExprEqFast_iff` / `ConstantVal.canonEqFast_iff` /
`ConstantInfo.canonEqFast_iff` / `canonEqListFast_iff` carry that to the
specification, which is what the rest of the tier reads
(`basisPinHit`/`quotPinHit`, `ConRon/Refine/BasisRaw.lean`).

These are *pure* functions: there is no `CheckError` here, only Aeneas's
`Result`, so task #67's full-outcome convention does not apply and nothing
below claims anything about a `fail`.
-/
import ConRon.Generated
import ConRon.Refine.Abs
import ConRon.Refine.Name
import ConRon.Refine.Level
import ConRon.Refine.Levels
import ConRon.Refine.Expr
import ConRon.Refine.ExprOps
import ConRon.Refine.Env
import ConLeche.Kernel.Canon

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Canon

/-! ## `canon_name_map`: the renaming a level-parameter list induces -/

/-- The index recursion: from `i` on, the port scans `ps` for `n` and returns
`⟨i + j⟩` at the first hit.  `canonNameMap` is the `i = 0` instance. -/
theorem canon_name_map_from_aux {ps : alloc.vec.Vec name.Name} {n : name.Name}
    (hps : NamesWF ps) (hn : NameWF n) :
    ∀ (k : Nat) (i : Std.Usize) (r : name.Name), ps.val.length - i.val ≤ k →
      canon.canon_name_map_from ps n i = ok r →
      absName r = (match ((ps.val.drop i.val).map absName).findIdx?
            (fun p => p == absName n) with
        | some j => .num .anonymous (i.val + j)
        | none => absName n) := by
  have hnil : ∀ (i : Std.Usize) (r : name.Name), ps.val.length ≤ i.val →
      canon.canon_name_map_from ps n i = ok r → absName r = absName n := by
    intro i r hi h
    rw [canon.canon_name_map_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len ps by scalar_tac)] at h
    exact Name.dup_refines h
  intro k
  induction k with
  | zero =>
    intro i r hk h
    rw [List.drop_eq_nil_of_le (by omega), List.map_nil, List.findIdx?_nil]
    exact hnil i r (by omega) h
  | succ k ih =>
    intro i r hk h
    by_cases hi : ps.val.length ≤ i.val
    · rw [List.drop_eq_nil_of_le (by omega), List.map_nil, List.findIdx?_nil]
      exact hnil i r hi h
    · have hl : i.val < ps.val.length := by omega
      rw [canon.canon_name_map_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len ps by scalar_tac)] at h
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hl)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b0, hb0, h⟩ := h
      have hb0' := Name.beq_refines (hps _ (List.getElem_mem hl)) hn hb0
      rw [List.drop_eq_getElem_cons hl, List.map_cons, List.findIdx?_cons]
      cases hc : b0
      · rw [hc] at hb0' h
        simp only [Bool.false_eq_true, if_false] at h
        have hne : ¬ (absName ps.val[i.val] = absName n) := of_decide_eq_false hb0'.symm
        simp only [beq_iff_eq, hne, if_false]
        have hmax : i.val + 1 ≤ Std.Usize.max := by
          have := ps.slice.property; scalar_tac
        obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
        simp only [hw, bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
        have hrec := ih w r (by omega) h
        rw [hwv] at hrec
        rw [hrec]
        cases hf : ((ps.val.drop (i.val + 1)).map absName).findIdx?
            (fun p => p == absName n) with
        | none => simp
        | some j => simp only [Option.map_some]; congr 1; omega
      · rw [hc] at hb0' h
        have heq : absName ps.val[i.val] = absName n := of_decide_eq_true hb0'.symm
        simp only [beq_iff_eq, heq, if_true]
        simp only [if_true, bind_eq_ok_iff, lift_eq, Result.ok.injEq,
          exists_eq_left'] at h
        obtain ⟨a, ha, h⟩ := h
        rw [Name.mk_num_refines h, Name.anonymous_refines ha,
          Env.usize_cast_u64_val]
        simp

theorem canon_name_map_refines {ps : alloc.vec.Vec name.Name} {n r : name.Name}
    (hps : NamesWF ps) (hn : NameWF n) (h : canon.canon_name_map ps n = ok r) :
    absName r = ConLeche.canonNameMap (absNames ps) (absName n) := by
  rw [canon.canon_name_map] at h
  have hfrom := canon_name_map_from_aux hps hn ps.val.length 0#usize r (by omega) h
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [h0, List.drop_zero] at hfrom
  rw [hfrom, ConLeche.canonNameMap, absNames]
  cases (ps.val.map absName).findIdx? (fun p => p == absName n) <;> simp

/-- The renamed name is well formed: either `⟨i⟩` or `n` itself.  The port's
`i as u64` cast is invisible here, `NameWF.num` being indifferent to it. -/
theorem canon_name_map_from_wf {ps : alloc.vec.Vec name.Name} {n : name.Name} (hn : NameWF n) :
    ∀ (k : Nat) (i : Std.Usize) (r : name.Name), ps.val.length - i.val ≤ k →
      canon.canon_name_map_from ps n i = ok r → NameWF r := by
  have hnil : ∀ (i : Std.Usize) (r : name.Name), ps.val.length ≤ i.val →
      canon.canon_name_map_from ps n i = ok r → NameWF r := by
    intro i r hi h
    rw [canon.canon_name_map_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len ps by scalar_tac), name_dup_eq,
      Result.ok.injEq] at h
    exact h ▸ hn
  intro k
  induction k with
  | zero => intro i r hk h; exact hnil i r (by omega) h
  | succ k ih =>
    intro i r hk h
    by_cases hi : ps.val.length ≤ i.val
    · exact hnil i r hi h
    · have hl : i.val < ps.val.length := by omega
      rw [canon.canon_name_map_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len ps by scalar_tac)] at h
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hl)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b0, _, h⟩ := h
      cases b0
      · simp only [Bool.false_eq_true, if_false] at h
        have hmax : i.val + 1 ≤ Std.Usize.max := by
          have := ps.slice.property; scalar_tac
        obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
        simp only [hw, bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
        exact ih w r (by omega) h
      · simp only [if_true, bind_eq_ok_iff, lift_eq, Result.ok.injEq,
          exists_eq_left'] at h
        obtain ⟨a, ha, h⟩ := h
        exact NameWF.num (NameWF.anonymous ha) h

theorem canon_name_map_wf {ps : alloc.vec.Vec name.Name} {n r : name.Name}
    (hn : NameWF n) (h : canon.canon_name_map ps n = ok r) : NameWF r := by
  rw [canon.canon_name_map] at h
  exact canon_name_map_from_wf hn ps.val.length 0#usize r (by omega) h

/-! ## `canon_level`: the renaming, applied to a level

A `Level` is a handful of nodes, so the port renames one outright rather than
comparing in lockstep (`canon.rs`'s module note); the two `*Fast` arms that
need a level compare *built* canonical levels.  The walk therefore has to
deliver a well-formed result as well as the right one: `level::beq` is exact
only on well-formed arguments. -/

/-- The renamed level *is* con-leche's, and is well formed. -/
theorem canon_level_aux {ps : alloc.vec.Vec name.Name} (hps : NamesWF ps) :
    ∀ (l : level.Level), LevelWF l → ∀ r : level.Level, canon.canon_level ps l = ok r →
      absLevel r = ConLeche.canonLevel (ConLeche.canonNameMap (absNames ps)) (absLevel l)
        ∧ LevelWF r := by
  intro l hl
  induction l, hl using LevelWF.ind_node with
  | zero h w =>
    intro r hr
    rw [canon.canon_level.eq_def] at hr
    simp only [arc_deref_eq, bind_tc_ok, level.Level._0._simpLemma_,
      level.LevelNode.kind._simpLemma_] at hr
    exact ⟨by rw [Level.zero_refines hr]; simp [ConLeche.canonLevel], LevelWF.zero hr⟩
  | succ h a w ih =>
    intro r hr
    rw [canon.canon_level.eq_def] at hr
    simp only [arc_deref_eq, bind_tc_ok, level.Level._0._simpLemma_,
      level.LevelNode.kind._simpLemma_, bind_eq_ok_iff] at hr
    obtain ⟨x, hx, hr⟩ := hr
    obtain ⟨hxa, hxw⟩ := ih (Level.LevelWF.succ_inv w) x hx
    exact ⟨by rw [Level.succ_refines hr, hxa]; simp [ConLeche.canonLevel],
      LevelWF.succ hxw hr⟩
  | max h a b w iha ihb =>
    intro r hr
    rw [canon.canon_level.eq_def] at hr
    simp only [arc_deref_eq, bind_tc_ok, level.Level._0._simpLemma_,
      level.LevelNode.kind._simpLemma_, bind_eq_ok_iff] at hr
    obtain ⟨x, hx, y, hy, hr⟩ := hr
    obtain ⟨hxa, hxw⟩ := iha (Level.LevelWF.max_inv w).1 x hx
    obtain ⟨hya, hyw⟩ := ihb (Level.LevelWF.max_inv w).2 y hy
    exact ⟨by rw [Level.max_refines hr, hxa, hya]; simp [ConLeche.canonLevel],
      LevelWF.max hxw hyw hr⟩
  | imax h a b w iha ihb =>
    intro r hr
    rw [canon.canon_level.eq_def] at hr
    simp only [arc_deref_eq, bind_tc_ok, level.Level._0._simpLemma_,
      level.LevelNode.kind._simpLemma_, bind_eq_ok_iff] at hr
    obtain ⟨x, hx, y, hy, hr⟩ := hr
    obtain ⟨hxa, hxw⟩ := iha (Level.LevelWF.imax_inv w).1 x hx
    obtain ⟨hya, hyw⟩ := ihb (Level.LevelWF.imax_inv w).2 y hy
    exact ⟨by rw [Level.imax_refines hr, hxa, hya]; simp [ConLeche.canonLevel],
      LevelWF.imax hxw hyw hr⟩
  | param h n w =>
    intro r hr
    rw [canon.canon_level.eq_def] at hr
    simp only [arc_deref_eq, bind_tc_ok, level.Level._0._simpLemma_,
      level.LevelNode.kind._simpLemma_, bind_eq_ok_iff] at hr
    obtain ⟨x, hx, hr⟩ := hr
    have hn := Level.LevelWF.param_inv w
    exact ⟨by rw [Level.param_refines hr, canon_name_map_refines hps hn hx];
              simp [ConLeche.canonLevel],
      LevelWF.param (canon_name_map_wf hn hx) hr⟩

theorem canon_level_refines {ps : alloc.vec.Vec name.Name} {l r : level.Level}
    (hps : NamesWF ps) (hl : LevelWF l) (h : canon.canon_level ps l = ok r) :
    absLevel r = ConLeche.canonLevel (ConLeche.canonNameMap (absNames ps)) (absLevel l) :=
  (canon_level_aux hps l hl r h).1

theorem canon_level_wf {ps : alloc.vec.Vec name.Name} {l r : level.Level}
    (hps : NamesWF ps) (hl : LevelWF l) (h : canon.canon_level ps l = ok r) : LevelWF r :=
  (canon_level_aux hps l hl r h).2

/-! ## `canon_level_list`: `us.map (canonLevel m)`, the `.const` arm's list

The index recursion of `canon.rs`'s `canon_level_list_from` (§3.4 forbids
closures and loops); the accumulator is a `Vec`, so the invariant is
`out ++ …` (task #13's deviation 3: a `Vec` has no shared tail). -/

theorem canon_level_list_from_aux (N : Nat) :
    ∀ (ps : alloc.vec.Vec name.Name) (ls : alloc.vec.Vec level.Level)
      (i : Std.Usize) (out r : alloc.vec.Vec level.Level),
      NamesWF ps → LevelsWF ls → LevelsWF out → ls.val.length - i.val = N →
      canon.canon_level_list_from ps ls i out = ok r →
      absLevels r = absLevels out ++
          ((absLevels ls).drop i.val).map
            (ConLeche.canonLevel (ConLeche.canonNameMap (absNames ps)))
        ∧ LevelsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ps ls i out r hps hls hout hN h
    rw [canon.canon_level_list_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : (absLevels ls).length ≤ i.val := by
        have := alloc.vec.Vec.len_val ls; simp only [absLevels, List.length_map]; scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]
      exact ⟨by simp, hout⟩
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, c, hc, out1, hpush, i2, hi2, hrec⟩ := h
      have hg := ExprOps.vec_index_getElem? hidx
      have hlt : i.val < ls.val.length := by
        have := alloc.vec.Vec.len_val ls; scalar_tac
      have hx : ls.val[i.val] = x := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hxwf : LevelWF x := hls x (by rw [← hx]; exact List.getElem_mem hlt)
      obtain ⟨hcabs, hcwf⟩ := canon_level_aux hps x hxwf c hc
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hout1 : LevelsWF out1 := by
        intro y hy
        rw [vec_push_val hpush] at hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hout y hy
        · rw [List.mem_singleton.mp hy]; exact hcwf
      obtain ⟨hrabs, hrwf⟩ :=
        ih (ls.val.length - i2.val) (by omega) ps ls i2 out1 r hps hls hout1 rfl hrec
      refine ⟨?_, hrwf⟩
      rw [hrabs, hi2v]
      simp only [absLevels, vec_push_val hpush, List.map_append, List.map_cons,
        List.map_nil, hcabs]
      rw [show (ls.val.map absLevel).drop i.val
          = absLevel x :: (ls.val.map absLevel).drop (i.val + 1) from by
        rw [List.drop_eq_getElem_cons (by simpa using hlt), List.getElem_map, hx]]
      simp

/-- `canon::canon_level_list` is con-leche's `us.map (canonLevel m)`. -/
theorem canon_level_list_refines {ps : alloc.vec.Vec name.Name}
    {ls r : alloc.vec.Vec level.Level} (hps : NamesWF ps) (hls : LevelsWF ls)
    (h : canon.canon_level_list ps ls = ok r) :
    absLevels r =
        (absLevels ls).map (ConLeche.canonLevel (ConLeche.canonNameMap (absNames ps)))
      ∧ LevelsWF r := by
  rw [canon.canon_level_list] at h
  obtain ⟨habs, hwf⟩ :=
    canon_level_list_from_aux _ ps ls 0#usize (alloc.vec.Vec.new level.Level) r hps hls
      (by intro y hy; simp [alloc.vec.Vec.new] at hy) rfl h
  refine ⟨?_, hwf⟩
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [habs, h0, List.drop_zero]
  simp [absLevels, alloc.vec.Vec.new]

/-! ## `canon_expr_eq_fast`: the lockstep descent

The port's walk against con-leche's `canonExprEqFast`, by structural induction
on the left argument (`ExprWF.ind_node`) with the right one destructured in
each arm.  Ten constructors against ten: the ninety off-diagonal pairs are
`ok false` on the Rust side and the catch-all `_, _ => false` on the Lean's,
because `absExpr` maps the port's ten kinds onto con-leche's ten
constructors. -/

/-- Every `&&` of the descent, as the generated code spells it: run the test,
and on `true` run the rest.  Both sides are `Bool`s here, not `decide`s of
`Prop`s — the recursive calls return con-leche `Bool`s — so this is the `Bool`
twin of `Refine/Expr.lean`'s `guard_step`. -/
theorem and_step {c p q : Bool} {test rest : Result Bool}
    (htest : ∀ y, test = ok y → y = p) (hrest : ∀ y, rest = ok y → y = q)
    (h : (do let y ← test; if y = true then rest else ok false) = ok c) :
    c = (p && q) := by
  obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
  have e := htest y hy
  cases y with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h, ← e]; simp
  | true =>
    simp only [if_true] at h
    rw [hrest c h, ← e]; simp

/-- `==` at a `DecidableEq` type is `decide (· = ·)`: the refinement lemmas of
the tier speak `decide`, con-leche's `canonExprEqFast` speaks `==`. -/
theorem beq_eq_decide {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (x y : α) :
    (x == y) = decide (x = y) := by
  cases h : (x == y) <;> simp_all

theorem canon_expr_eq_fast_aux {ps ps2 : alloc.vec.Vec name.Name}
    (hps : NamesWF ps) (hps2 : NamesWF ps2) :
    ∀ (a : expr.Expr), ExprWF a → ∀ (b : expr.Expr), ExprWF b → ∀ c : Bool,
      canon.canon_expr_eq_fast ps ps2 a b = ok c →
      c = ConLeche.canonExprEqFast (ConLeche.canonNameMap (absNames ps))
        (ConLeche.canonNameMap (absNames ps2)) (absExpr a) (absExpr b) := by
  intro a ha
  induction a, ha using ExprWF.ind_node with
  | bvar d i w =>
    intro b hb c h
    obtain ⟨⟨d2, k2⟩⟩ := b
    rw [canon.canon_expr_eq_fast.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_] at h
    cases k2
    case Bvar j => rw [Expr.u64_eq_test h]; simp [ConLeche.canonExprEqFast, beq_eq_decide]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.canonExprEqFast])
  | fvar d idx ty w ih =>
    intro b hb c h
    obtain ⟨⟨d2, k2⟩⟩ := b
    rw [canon.canon_expr_eq_fast.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_] at h
    cases k2
    case Fvar j t2 =>
      rw [and_step (fun y hy => Expr.u64_eq_test hy)
        (fun y hy => ih (ExprWF.fvar_kids w) _ (ExprWF.fvar_kids hb) y hy) h]
      simp [ConLeche.canonExprEqFast, beq_eq_decide]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.canonExprEqFast])
  | sort d u w =>
    intro b hb c h
    obtain ⟨⟨d2, k2⟩⟩ := b
    rw [canon.canon_expr_eq_fast.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_] at h
    cases k2
    case «Sort» v =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨l1, hl1, l2, hl2, h⟩ := h
      obtain ⟨hab1, hwf1⟩ := canon_level_aux hps u (ExprWF.sort_kids w) l1 hl1
      obtain ⟨hab2, hwf2⟩ := canon_level_aux hps2 v (ExprWF.sort_kids hb) l2 hl2
      rw [Level.beq_refines hwf1 hwf2 h, hab1, hab2]
      simp [ConLeche.canonExprEqFast, beq_eq_decide]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.canonExprEqFast])
  | mk_const d n us w =>
    intro b hb c h
    obtain ⟨⟨d2, k2⟩⟩ := b
    rw [canon.canon_expr_eq_fast.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_] at h
    cases k2
    case Const n2 us2 =>
      obtain ⟨hn, hus⟩ := ExprWF.const_kids w
      obtain ⟨hn2, hus2⟩ := ExprWF.const_kids hb
      -- task #93: each side goes through `levels::to_vec` first, which is
      -- the list the `Levels` stands for.
      rw [and_step (fun y hy => Name.beq_refines hn hn2 hy) (fun y hy => by
        simp only [bind_eq_ok_iff] at hy
        obtain ⟨w1, hw1, v1, hv1, w2, hw2, v3, hv3, hy⟩ := hy
        obtain ⟨hab1, hwf1⟩ :=
          canon_level_list_refines hps (Levels.to_vec_wf hus hw1) hv1
        obtain ⟨hab2, hwf2⟩ :=
          canon_level_list_refines hps2 (Levels.to_vec_wf hus2 hw2) hv3
        rw [Expr.levels_beq_refines hwf1 hwf2 hy, hab1, hab2,
          Levels.to_vec_refines hw1, Levels.to_vec_refines hw2]) h]
      simp [ConLeche.canonExprEqFast, beq_eq_decide, absLevels]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.canonExprEqFast])
  | app d f x w ihf ihx =>
    intro b hb c h
    obtain ⟨⟨d2, k2⟩⟩ := b
    rw [canon.canon_expr_eq_fast.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_] at h
    cases k2
    case App f2 x2 =>
      rw [and_step (fun y hy => ihf (ExprWF.app_kids w).1 _ (ExprWF.app_kids hb).1 y hy)
        (fun y hy => ihx (ExprWF.app_kids w).2 _ (ExprWF.app_kids hb).2 y hy) h]
      simp [ConLeche.canonExprEqFast]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.canonExprEqFast])
  | lam d ty bo m w ihty ihbo =>
    intro b hb c h
    obtain ⟨⟨d2, k2⟩⟩ := b
    rw [canon.canon_expr_eq_fast.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_] at h
    cases k2
    case Lam ty2 bo2 m2 =>
      rw [and_step (fun y hy => ihty (ExprWF.lam_kids w).1 _ (ExprWF.lam_kids hb).1 y hy)
        (fun y hy => ihbo (ExprWF.lam_kids w).2.1 _ (ExprWF.lam_kids hb).2.1 y hy) h]
      simp [ConLeche.canonExprEqFast]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.canonExprEqFast])
  | forall_e d ty bo m w ihty ihbo =>
    intro b hb c h
    obtain ⟨⟨d2, k2⟩⟩ := b
    rw [canon.canon_expr_eq_fast.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_] at h
    cases k2
    case ForallE ty2 bo2 m2 =>
      rw [and_step
        (fun y hy => ihty (ExprWF.forall_e_kids w).1 _ (ExprWF.forall_e_kids hb).1 y hy)
        (fun y hy => ihbo (ExprWF.forall_e_kids w).2.1 _ (ExprWF.forall_e_kids hb).2.1 y hy) h]
      simp [ConLeche.canonExprEqFast]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.canonExprEqFast])
  | let_e d ty v bo w ihty ihv ihbo =>
    intro b hb c h
    obtain ⟨⟨d2, k2⟩⟩ := b
    rw [canon.canon_expr_eq_fast.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_] at h
    cases k2
    case LetE ty2 v2 bo2 =>
      rw [and_step (fun y hy => ihty (ExprWF.let_e_kids w).1 _ (ExprWF.let_e_kids hb).1 y hy)
        (fun y hy => and_step
          (fun z hz => ihv (ExprWF.let_e_kids w).2.1 _ (ExprWF.let_e_kids hb).2.1 z hz)
          (fun z hz => ihbo (ExprWF.let_e_kids w).2.2 _ (ExprWF.let_e_kids hb).2.2 z hz) hy) h]
      simp [ConLeche.canonExprEqFast, Bool.and_assoc]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.canonExprEqFast])
  | lit d l w =>
    intro b hb c h
    obtain ⟨⟨d2, k2⟩⟩ := b
    rw [canon.canon_expr_eq_fast.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_] at h
    cases k2
    case Lit l2 =>
      rw [Expr.literal_beq_refines (ExprWF.lit_kids w) (ExprWF.lit_kids hb) h]
      simp [ConLeche.canonExprEqFast, beq_eq_decide]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.canonExprEqFast])
  | proj d s i x w ihx =>
    intro b hb c h
    obtain ⟨⟨d2, k2⟩⟩ := b
    rw [canon.canon_expr_eq_fast.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
      expr.ExprNode.kind._simpLemma_] at h
    cases k2
    case Proj s2 i2 x2 =>
      rw [and_step
        (fun y hy => Name.beq_refines (ExprWF.proj_kids w).1 (ExprWF.proj_kids hb).1 hy)
        (fun y hy => and_step (fun z hz => Expr.u64_eq_test hz)
          (fun z hz => ihx (ExprWF.proj_kids w).2 _ (ExprWF.proj_kids hb).2 z hz) hy) h]
      simp [ConLeche.canonExprEqFast, Bool.and_assoc, beq_eq_decide]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.canonExprEqFast])

/-- `canon::canon_expr_eq_fast` refines con-leche's lockstep twin. -/
theorem canon_expr_eq_fast_refines {ps ps2 : alloc.vec.Vec name.Name}
    {a b : expr.Expr} {c : Bool} (hps : NamesWF ps) (hps2 : NamesWF ps2)
    (ha : ExprWF a) (hb : ExprWF b)
    (h : canon.canon_expr_eq_fast ps ps2 a b = ok c) :
    c = ConLeche.canonExprEqFast (ConLeche.canonNameMap (absNames ps))
      (ConLeche.canonNameMap (absNames ps2)) (absExpr a) (absExpr b) :=
  canon_expr_eq_fast_aux hps hps2 a ha b hb c h

/-! ## The rule lists

`canonRulesEqFast` compares a recursor's iota rules through the canonical form
of each rule's right-hand side; every other field is compared verbatim, which
is what `canon::rec_rule_eq_but_rhs` spells out. -/

/-- The generated `if P then rest else ok false` where the rest is a `Bool`,
not a `decide` of a `Prop` (the `Bool` twin of `Refine/Env.lean`'s
`scalar_step`). -/
theorem if_step {c q : Bool} {P : Prop} [Decidable P] {rest : Result Bool}
    (hrest : ∀ y, rest = ok y → y = q)
    (h : (if P then rest else ok false) = ok c) : c = (decide P && q) := by
  by_cases hp : P
  · rw [if_pos hp] at h; rw [hrest c h]; simp [hp]
  · rw [if_neg hp, Result.ok.injEq] at h; rw [← h]; simp [hp]

/-- `{ r with rhs := .bvar 0 } == { r' with rhs := .bvar 0 }`: con-leche's
spelling of "every field but `rhs`", which the port compares field by
field. -/
theorem rec_rule_eq_but_rhs_refines {r r2 : env.RecRule} {c : Bool}
    (hr : RecRuleWF r) (hr2 : RecRuleWF r2)
    (h : canon.rec_rule_eq_but_rhs r r2 = ok c) :
    c = (({ absRecRule r with rhs := .bvar 0 } : ConLeche.RecRule)
      == { absRecRule r2 with rhs := .bvar 0 }) := by
  rw [canon.rec_rule_eq_but_rhs] at h
  rw [Expr.guard_step (fun y hy => Name.beq_refines hr.1 hr2.1 hy)
    (fun y hy => Env.scalar_step (fun z hz => Env.scalar_step
      (fun u hu => Expr.guard_step
        (fun v hv => Env.rec_rule_fire_beq_refines hr.2.1 hr2.2.1 hv)
        (fun v hv => Env.scalar_step (fun t ht => Env.scalar_step
          (fun s hs => Env.final_step hs) ht) hv) hu) hz) hy) h]
  rw [beq_eq_decide]
  refine decide_eq_decide.mpr ?_
  simp only [absRecRule, ConLeche.RecRule.mk.injEq, true_and]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, by rw [h2], by rw [h3], h4, h5, h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, Env.u64_val_inj h2, Env.u64_val_inj h3, h4, h5, h6, h7⟩

theorem canon_rules_eq_fast_from_aux {ps ps2 : alloc.vec.Vec name.Name}
    (hps : NamesWF ps) (hps2 : NamesWF ps2) {rs rs2 : alloc.vec.Vec env.RecRule}
    (hrs : RecRulesWF rs) (hrs2 : RecRulesWF rs2) :
    ∀ (k : Nat) (i : Std.Usize) (c : Bool), rs.val.length - i.val ≤ k →
      canon.canon_rules_eq_fast_from ps ps2 rs rs2 i = ok c →
      c = ConLeche.canonRulesEqFast (ConLeche.canonNameMap (absNames ps))
        (ConLeche.canonNameMap (absNames ps2))
        ((rs.val.map absRecRule).drop i.val) ((rs2.val.map absRecRule).drop i.val) := by
  have hbase : ∀ (i : Std.Usize) (c : Bool), rs.val.length ≤ i.val →
      canon.canon_rules_eq_fast_from ps ps2 rs rs2 i = ok c →
      c = ConLeche.canonRulesEqFast (ConLeche.canonNameMap (absNames ps))
        (ConLeche.canonNameMap (absNames ps2))
        ((rs.val.map absRecRule).drop i.val) ((rs2.val.map absRecRule).drop i.val) := by
    intro i c hi h
    rw [canon.canon_rules_eq_fast_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len rs by scalar_tac)] at h
    rw [List.drop_eq_nil_of_le (show (rs.val.map absRecRule).length ≤ i.val by simpa using hi)]
    by_cases h2 : rs2.val.length ≤ i.val
    · rw [if_pos (show i >= alloc.vec.Vec.len rs2 by scalar_tac), Result.ok.injEq] at h
      rw [← h,
        List.drop_eq_nil_of_le (show (rs2.val.map absRecRule).length ≤ i.val by simpa using h2)]
      rfl
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len rs2 by scalar_tac),
        if_pos (show i >= alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
      rw [← h]
      have hne : (rs2.val.map absRecRule).drop i.val ≠ [] := by
        rw [ne_eq, List.drop_eq_nil_iff, List.length_map]; omega
      cases hd : (rs2.val.map absRecRule).drop i.val with
      | nil => exact absurd hd hne
      | cons x xs => rfl
  intro k
  induction k with
  | zero => intro i c hk h; exact hbase i c (by omega) h
  | succ k ih =>
    intro i c hk h
    by_cases hi : rs.val.length ≤ i.val
    · exact hbase i c hi h
    · have hlt : i.val < rs.val.length := by omega
      rw [canon.canon_rules_eq_fast_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len rs by scalar_tac),
        if_neg (show ¬ i >= alloc.vec.Vec.len rs by scalar_tac)] at h
      by_cases h2 : rs2.val.length ≤ i.val
      · rw [if_pos (show i >= alloc.vec.Vec.len rs2 by scalar_tac), Result.ok.injEq] at h
        rw [← h,
          List.drop_eq_nil_of_le (show (rs2.val.map absRecRule).length ≤ i.val by simpa using h2)]
        cases hd : (rs.val.map absRecRule).drop i.val with
        | nil =>
          exact absurd hd (by rw [List.drop_eq_nil_iff, List.length_map]; omega)
        | cons x xs => rfl
      · have hlt2 : i.val < rs2.val.length := by omega
        rw [if_neg (show ¬ i >= alloc.vec.Vec.len rs2 by scalar_tac)] at h
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rs i hlt)
        obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rs2 i hlt2)
        subst hyv; subst hzv
        simp only [alloc.vec.Vec.index_slice_index, hy, hz, bind_tc_ok] at h
        have hwf1 : RecRuleWF rs.val[i.val] := hrs _ (List.getElem_mem hlt)
        have hwf2 : RecRuleWF rs2.val[i.val] := hrs2 _ (List.getElem_mem hlt2)
        have hmax : i.val + 1 ≤ Std.Usize.max := by have := rs.slice.property; scalar_tac
        obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
        rw [and_step (fun u hu => rec_rule_eq_but_rhs_refines hwf1 hwf2 hu)
          (fun u hu => and_step
            (fun v hv => canon_expr_eq_fast_refines hps hps2 hwf1.2.2 hwf2.2.2 hv)
            (fun v hv => by
              simp only [hw, bind_tc_ok] at hv
              have hrec := ih w v (by omega) hv
              rwa [hwv] at hrec) hu) h]
        rw [show (rs.val.map absRecRule).drop i.val
            = absRecRule rs.val[i.val] :: (rs.val.map absRecRule).drop (i.val + 1) from by
          rw [List.drop_eq_getElem_cons (by simpa using hlt), List.getElem_map]]
        rw [show (rs2.val.map absRecRule).drop i.val
            = absRecRule rs2.val[i.val] :: (rs2.val.map absRecRule).drop (i.val + 1) from by
          rw [List.drop_eq_getElem_cons (by simpa using hlt2), List.getElem_map]]
        simp [ConLeche.canonRulesEqFast, Bool.and_assoc, absRecRule]

/-- `canon::canon_rules_eq_fast` refines `canonRulesEqFast`. -/
theorem canon_rules_eq_fast_refines {ps ps2 : alloc.vec.Vec name.Name}
    {rs rs2 : alloc.vec.Vec env.RecRule} {c : Bool} (hps : NamesWF ps) (hps2 : NamesWF ps2)
    (hrs : RecRulesWF rs) (hrs2 : RecRulesWF rs2)
    (h : canon.canon_rules_eq_fast ps ps2 rs rs2 = ok c) :
    c = ConLeche.canonRulesEqFast (ConLeche.canonNameMap (absNames ps))
      (ConLeche.canonNameMap (absNames ps2)) (absRecRules rs) (absRecRules rs2) := by
  rw [canon.canon_rules_eq_fast] at h
  have hfrom := canon_rules_eq_fast_from_aux hps hps2 hrs hrs2 rs.val.length 0#usize c
    (by omega) h
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  rwa [h0, List.drop_zero, List.drop_zero] at hfrom

/-! ## `ConstantVal`, `ConstantInfo` and the block

Each of the three ends at con-leche's *specification* — `decide (canon x =
canon y)` — through the `@[csimp]` lemma that identifies it with the lockstep
twin the port carries. -/

theorem constant_val_canon_eq_fast_refines {cv cv2 : env.ConstantVal} {c : Bool}
    (hcv : ConstantValWF cv) (hcv2 : ConstantValWF cv2)
    (h : canon.constant_val_canon_eq cv cv2 = ok c) :
    c = ConLeche.ConstantVal.canonEqFast (absConstantVal cv) (absConstantVal cv2) := by
  rw [canon.constant_val_canon_eq] at h
  have hlen : (alloc.vec.Vec.len cv.level_params = alloc.vec.Vec.len cv2.level_params)
      ↔ (cv.level_params.val.length = cv2.level_params.val.length) := by
    constructor <;> intro hh <;> scalar_tac
  rw [and_step (fun y hy => Name.beq_refines hcv.1 hcv2.1 hy)
    (fun y hy => if_step
      (fun z hz => canon_expr_eq_fast_refines hcv.2.1 hcv2.2.1 hcv.2.2 hcv2.2.2 hz) hy) h]
  simp [ConLeche.ConstantVal.canonEqFast, absConstantVal, absNames, Bool.and_assoc,
    beq_eq_decide, hlen]

/-- **The `ConstantVal` comparison**, at con-leche's specification. -/
theorem constant_val_canon_eq_refines {cv cv2 : env.ConstantVal} {c : Bool}
    (hcv : ConstantValWF cv) (hcv2 : ConstantValWF cv2)
    (h : canon.constant_val_canon_eq cv cv2 = ok c) :
    c = ConLeche.ConstantVal.canonEq (absConstantVal cv) (absConstantVal cv2) := by
  rw [constant_val_canon_eq_fast_refines hcv hcv2 h,
    ConLeche.ConstantVal.canonEq_eq_canonEqFast]

theorem constant_info_canon_eq_fast_refines {ci ci2 : env.ConstantInfo} {c : Bool}
    (ha : ConstantInfoWF ci) (hb : ConstantInfoWF ci2)
    (h : canon.constant_info_canon_eq ci ci2 = ok c) :
    c = ConLeche.ConstantInfo.canonEqFast (absConstantInfo ci) (absConstantInfo ci2) := by
  cases ci <;> cases ci2 <;> simp only [canon.constant_info_canon_eq] at h <;>
    simp only [absConstantInfo, ConLeche.ConstantInfo.canonEqFast]
  all_goals try exact (Result.ok_injective h).symm
  case AxiomInfo.AxiomInfo => exact constant_val_canon_eq_fast_refines ha hb h
  case DefnInfo.DefnInfo cv v hint cv2 v2 hint2 =>
    rw [and_step (fun y hy => constant_val_canon_eq_fast_refines ha.1 hb.1 hy)
      (fun y hy => and_step
        (fun z hz => canon_expr_eq_fast_refines ha.1.2.1 hb.1.2.1 ha.2 hb.2 hz)
        (fun z hz => Env.reducibility_hint_beq_refines hz) hy) h]
    simp [absConstantVal, Bool.and_assoc, beq_eq_decide]
  case ThmInfo.ThmInfo cv v cv2 v2 =>
    rw [and_step (fun y hy => constant_val_canon_eq_fast_refines ha.1 hb.1 hy)
      (fun y hy => canon_expr_eq_fast_refines ha.1.2.1 hb.1.2.1 ha.2 hb.2 hy) h]
    simp [absConstantVal]
  case IndInfo.IndInfo => exact constant_val_canon_eq_fast_refines ha.1 hb.1 h
  case CtorInfo.CtorInfo =>
    rw [and_step (fun y hy => constant_val_canon_eq_fast_refines ha hb hy)
      (fun y hy => and_step (fun z hz => Expr.u64_eq_test hz)
        (fun z hz => Expr.u64_eq_test hz) hy) h]
    simp [Bool.and_assoc, beq_eq_decide]
  case RecInfo.RecInfo cv mi rp rls cv2 mi2 rp2 rls2 =>
    rw [and_step (fun y hy => constant_val_canon_eq_fast_refines ha.1 hb.1 hy)
      (fun y hy => and_step (fun z hz => Expr.u64_eq_test hz)
        (fun z hz => and_step (fun u hu => Expr.u64_eq_test hu)
          (fun u hu => canon_rules_eq_fast_refines ha.1.2.1 hb.1.2.1 ha.2 hb.2 hu) hz) hy) h]
    simp [absConstantVal, absRecRules, Bool.and_assoc, beq_eq_decide]
  case ProjInfo.ProjInfo =>
    rw [Env.proj_table_beq_refines ha hb h]; simp [beq_eq_decide]

/-- **The `ConstantInfo` comparison**, at con-leche's specification. -/
theorem constant_info_canon_eq_refines {ci ci2 : env.ConstantInfo} {c : Bool}
    (ha : ConstantInfoWF ci) (hb : ConstantInfoWF ci2)
    (h : canon.constant_info_canon_eq ci ci2 = ok c) :
    c = ConLeche.ConstantInfo.canonEq (absConstantInfo ci) (absConstantInfo ci2) := by
  rw [constant_info_canon_eq_fast_refines ha hb h,
    ConLeche.ConstantInfo.canonEq_eq_canonEqFast]

/-- `canon_eq_list` takes two *slices* (`&[ConstantInfo]`), so its statement is
about `Slice.val`; the `Vec` form the pin match uses is below. -/
theorem canon_eq_list_from_aux {xs ys : Slice env.ConstantInfo}
    (hxs : ∀ x ∈ xs.val, ConstantInfoWF x) (hys : ∀ y ∈ ys.val, ConstantInfoWF y) :
    ∀ (k : Nat) (i : Std.Usize) (c : Bool), xs.val.length - i.val ≤ k →
      canon.canon_eq_list_from xs ys i = ok c →
      c = ConLeche.canonEqListFast ((xs.val.map absConstantInfo).drop i.val)
        ((ys.val.map absConstantInfo).drop i.val) := by
  have hbase : ∀ (i : Std.Usize) (c : Bool), xs.val.length ≤ i.val →
      canon.canon_eq_list_from xs ys i = ok c →
      c = ConLeche.canonEqListFast ((xs.val.map absConstantInfo).drop i.val)
        ((ys.val.map absConstantInfo).drop i.val) := by
    intro i c hi h
    rw [canon.canon_eq_list_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= Slice.len xs by scalar_tac)] at h
    rw [List.drop_eq_nil_of_le
      (show (xs.val.map absConstantInfo).length ≤ i.val by simpa using hi)]
    by_cases h2 : ys.val.length ≤ i.val
    · rw [if_pos (show i >= Slice.len ys by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le
        (show (ys.val.map absConstantInfo).length ≤ i.val by simpa using h2)]
      rfl
    · rw [if_neg (show ¬ i >= Slice.len ys by scalar_tac),
        if_pos (show i >= Slice.len xs by scalar_tac), Result.ok.injEq] at h
      rw [← h]
      have hne : (ys.val.map absConstantInfo).drop i.val ≠ [] := by
        rw [ne_eq, List.drop_eq_nil_iff, List.length_map]; omega
      cases hd : (ys.val.map absConstantInfo).drop i.val with
      | nil => exact absurd hd hne
      | cons x xs' => rfl
  intro k
  induction k with
  | zero => intro i c hk h; exact hbase i c (by omega) h
  | succ k ih =>
    intro i c hk h
    by_cases hi : xs.val.length ≤ i.val
    · exact hbase i c hi h
    · have hlt : i.val < xs.val.length := by omega
      rw [canon.canon_eq_list_from.eq_def] at h; simp only [] at h
      rw [if_neg (show ¬ i >= Slice.len xs by scalar_tac),
        if_neg (show ¬ i >= Slice.len xs by scalar_tac)] at h
      by_cases h2 : ys.val.length ≤ i.val
      · rw [if_pos (show i >= Slice.len ys by scalar_tac), Result.ok.injEq] at h
        rw [← h, List.drop_eq_nil_of_le
          (show (ys.val.map absConstantInfo).length ≤ i.val by simpa using h2)]
        cases hd : (xs.val.map absConstantInfo).drop i.val with
        | nil =>
          exact absurd hd (by rw [List.drop_eq_nil_iff, List.length_map]; omega)
        | cons x xs' => rfl
      · have hlt2 : i.val < ys.val.length := by omega
        rw [if_neg (show ¬ i >= Slice.len ys by scalar_tac)] at h
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Slice.index_usize_spec xs i hlt)
        obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (Slice.index_usize_spec ys i hlt2)
        subst hyv; subst hzv
        simp only [hy, hz, bind_tc_ok] at h
        have hwf1 : ConstantInfoWF xs.val[i.val] := hxs _ (List.getElem_mem hlt)
        have hwf2 : ConstantInfoWF ys.val[i.val] := hys _ (List.getElem_mem hlt2)
        have hmax : i.val + 1 ≤ Std.Usize.max := by have := xs.property; scalar_tac
        obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
        rw [and_step (fun u hu => constant_info_canon_eq_fast_refines hwf1 hwf2 hu)
          (fun u hu => by
            simp only [hw, bind_tc_ok] at hu
            have hrec := ih w u (by omega) hu
            rwa [hwv] at hrec) h]
        rw [show (xs.val.map absConstantInfo).drop i.val
            = absConstantInfo xs.val[i.val] :: (xs.val.map absConstantInfo).drop (i.val + 1)
          from by rw [List.drop_eq_getElem_cons (by simpa using hlt), List.getElem_map]]
        rw [show (ys.val.map absConstantInfo).drop i.val
            = absConstantInfo ys.val[i.val] :: (ys.val.map absConstantInfo).drop (i.val + 1)
          from by rw [List.drop_eq_getElem_cons (by simpa using hlt2), List.getElem_map]]
        rfl

/-- **The block comparison**, at con-leche's specification. -/
theorem canon_eq_list_refines {xs ys : Slice env.ConstantInfo} {c : Bool}
    (hxs : ∀ x ∈ xs.val, ConstantInfoWF x) (hys : ∀ y ∈ ys.val, ConstantInfoWF y)
    (h : canon.canon_eq_list xs ys = ok c) :
    c = ConLeche.canonEqList (xs.val.map absConstantInfo) (ys.val.map absConstantInfo) := by
  rw [canon.canon_eq_list] at h
  have hfrom := canon_eq_list_from_aux hxs hys xs.val.length 0#usize c (by omega) h
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [h0, List.drop_zero, List.drop_zero] at hfrom
  rw [hfrom, ConLeche.canonEqList_eq_canonEqListFast]

/-- `Vec::deref` is the identity on the underlying list. -/
theorem deref_val {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val :=
  Slice.from_val _ _

/-- The form the pin match uses: the two blocks are `Vec`s, dereferenced to
slices at the call (`basis_raw::basis_pin_hit_from`). -/
theorem canon_eq_list_deref_refines {xs ys : alloc.vec.Vec env.ConstantInfo} {c : Bool}
    (hxs : ConstantInfosWF xs) (hys : ConstantInfosWF ys)
    (h : canon.canon_eq_list (alloc.vec.Vec.deref xs) (alloc.vec.Vec.deref ys) = ok c) :
    c = ConLeche.canonEqList (absConstantInfos xs) (absConstantInfos ys) := by
  have hx : ∀ x ∈ (alloc.vec.Vec.deref xs).val, ConstantInfoWF x := by
    rw [deref_val]; exact hxs
  have hy : ∀ y ∈ (alloc.vec.Vec.deref ys).val, ConstantInfoWF y := by
    rw [deref_val]; exact hys
  have := canon_eq_list_refines hx hy h
  rwa [deref_val, deref_val, ← absConstantInfos, ← absConstantInfos] at this

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.Canon.canon_eq_list_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms canon_eq_list_refines

end ConRon.Refine.Canon
