/-
The refinement of `crates/con-ron-core/src/cached/expr_ops_c.rs` (task #26) on
its generated model `ConRon.Generated.cached.expr_ops_c.*` (DESIGN.md §3.5,
`Refine/CORE_PLAN.md` step 3, second half; task #51).

**What the statements are against.**  This module is the *executed* syntactic
tier: `ConLeche/Cached/ExprOpsC.lean`'s memoised walks on the term DAG, as
opposed to `kernel/expr_ops.rs`' structural specifications (task #47's
`Refine/ExprOps*.lean`).  Every lemma here is therefore stated against the
**cited `ExprOpsC.lean` definition** -- `ConLeche.Cached.ExprC.instantiate1`,
`ExprC.abstract1`, `ExprC.wscopedB`, … -- and never against the `ConLeche.Expr`
counterpart directly.  The bridge from the one to the other is con-leche's own
`ConLeche/Verify/Cached/OpsC.lean` and `…/GuardsC.lean`: one `*_spec` equation
per function (`instantiate1_spec`, `abstractRange_spec`, `leafGuard_spec`, …),
which is exactly the theorem DESIGN.md §3.1 pointed at when it made the two
memo policies binding.  So each proof here has two halves: the port's walk
against `ConLeche.Expr`'s logical function, in task #47's shape, and then the
cited `*_spec` to land on the `ExprC` definition the checker's callers name.

**The three differences from `expr_ops`**, all reproduced by the port and all
visible in the proofs:

1. **A derived-field cutoff at the head of every walk** (`bvarB ≤ d`,
   `fvarB ≤ d`, `fvarB == 0`, `!hasLP`) returns the node itself.  Each such
   branch is one `*_cutoff` lemma off `ExprOpsFields.lean`'s `bvar_b_refines` /
   `fvar_b_refines` and con-leche's `*_of_*_le` identities -- task #47 already
   needed three of them (`abstract1_cutoff`, `lower_bvars_cutoff`,
   `instantiate1_lift_cutoff`) and they are reused verbatim where the `Q` of the
   memo agrees.
2. **Only compound nodes are memoised in the substitution walks**, and every
   node kind is memoised in `instLevelParamsGo`/`wscopedBGo`/`leavesSubGo`/
   `allLevelParamsDefinedGo`.  The `MemoInv` of task #47 (`Refine/ExprOps.lean`)
   is policy-agnostic -- "every recorded answer is the real one" -- so the same
   `MemoInv.hit`/`MemoInv.set` pair serves both shapes; what changes is only
   *where* in the generated body the probe sits.
3. **The bulk key carries no live prefix**, and the `bvar` arm's re-entry runs
   under a fresh table.  That re-entry is a recursion of `instantiate_list_go`
   at a strictly smaller prefix, so its lemma is a strong induction on the
   prefix *outside* the induction on the `ExprWF` derivation, exactly as task
   #47's `instantiate_list_refines_aux` is.

**Every memo here is local** (`HashMap::new` per call, dropped on return): the
module adds no field to `cached::state_c`, so no `StateRel` appears in this
file.  That is the module's own note ("none of them lives in `CState`") and it
is why these lemmas are pure equations rather than state relations.

This file holds the `O(1)` field reads, the spine readers, the `Vec` helper
with no Lean counterpart, the two extra memo probes and the leaf-membership
walk; the walks themselves are in the three themed siblings
`ExprOpsCSubst.lean`, `ExprOpsCAbs.lean` and `ExprOpsCGuards.lean`.
-/
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsMeta
import ConLeche.Verify.Cached.OpsC
import ConLeche.Verify.Cached.GuardsC

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOpsC

open ConRon.Refine.ExprOps

/-! ## `ExprC.lean`'s one executed function, and the `O(1)` scope read

Both are the packed word's range fields, read through
`ExprOpsFields.lean`'s `fvar_b_refines`/`bvar_b_refines` -- the two lemmas that
carry the saturated branch's fall-back to the exact memoised walk. -/

/-- **`expr_ops_c::has_fvar` refines `ExprC.hasFvar`**
(`Cached/ExprC.lean:113-115`): the `fvarB != 0` field read.  It is
`expr_ops::has_fvar`'s body character for character and a *different*
declaration, because `ParsedC.lean`'s guard names `ExprC.hasFvar` outright
(the port's own module note), so it gets its own lemma against its own
citation. -/
theorem has_fvar_refines {e : expr.Expr} {b : Bool} (he : ExprWF e)
    (h : cached.expr_ops_c.has_fvar e = ok b) :
    b = ConLeche.Cached.ExprC.hasFvar (absExpr e) := by
  rw [cached.expr_ops_c.has_fvar] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  have hiv : i.val = (absExpr e).fvarB := fvar_b_refines he hi
  rw [← Result.ok_injective h, ConLeche.Cached.ExprC.hasFvar, ← hiv]
  by_cases hc : i.val = 0
  · have h0 : i = 0#u64 := Std.UScalar.eq_of_val_eq (by rw [hc, Expr.val_zero])
    have hl : (i != 0#u64) = false := by simp [h0]
    have hr : ((i.val : Nat) != 0) = false := by simp [hc]
    rw [hl, hr]
  · have hne : i ≠ 0#u64 := fun hcc => hc (by rw [hcc, Expr.val_zero])
    have hl : (i != 0#u64) = true := by simp only [bne_iff_ne, ne_eq]; exact hne
    have hr : ((i.val : Nat) != 0) = true := by simp only [bne_iff_ne, ne_eq]; exact hc
    rw [hl, hr]

/-- **`expr_ops_c::loose_bvars_bounded` refines `ExprC.looseBVarsBounded`**
(`ExprOpsC.lean:646-648`): `O(1)`, because the cached bound is the *least* such
`k` (`looseBVarsBounded_spec`, `Verify/Cached/OpsC.lean:131`). -/
theorem loose_bvars_bounded_refines {e : expr.Expr} {k : Std.U64} {b : Bool}
    (he : ExprWF e) (h : cached.expr_ops_c.loose_bvars_bounded k e = ok b) :
    b = ConLeche.Cached.ExprC.looseBVarsBounded k.val (absExpr e) := by
  rw [cached.expr_ops_c.loose_bvars_bounded] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  have hiv : i.val = (absExpr e).bvarB := bvar_b_refines he hi
  rw [← Result.ok_injective h, ConLeche.Cached.ExprC.looseBVarsBounded, ← hiv]
  by_cases hc : i.val ≤ k.val
  · have : (i ≤ k) := by scalar_tac
    simp [this, hc]
  · have : ¬ (i ≤ k) := by scalar_tac
    simp [this, hc]

/-! ## The spines (`ExprOpsC.lean:63-81`)

Bodies identical to `expr_ops`', separate declarations because the cited Lean
declares them separately; the proofs are task #47's, with the citation moved to
`ExprOpsC.lean` and the `*_spec` equation appended. -/

/-- **`expr_ops_c::get_app_fn` refines `ExprC.getAppFn`**
(`ExprOpsC.lean:65-68`). -/
theorem get_app_fn_refines {e r : expr.Expr} (he : ExprWF e)
    (h : cached.expr_ops_c.get_app_fn e = ok r) :
    absExpr r = ConLeche.Cached.ExprC.getAppFn (absExpr e) ∧ ExprWF r := by
  rw [ConLeche.Cached.ExprC.getAppFn_spec]
  induction he generalizing r with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    rw [cached.expr_ops_c.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.bvar h1⟩
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    rw [cached.expr_ops_c.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.fvar hty h1⟩
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    rw [cached.expr_ops_c.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.sort hu h1⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    rw [cached.expr_ops_c.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.mk_const hn hus h1⟩
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    rw [cached.expr_ops_c.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨habs, hwf⟩ := ihf h
    exact ⟨by rw [habs]; simp [ConLeche.Expr.getAppFn], hwf⟩
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    rw [cached.expr_ops_c.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.lam hty hbo hm h1⟩
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    rw [cached.expr_ops_c.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.forall_e hty hbo hm h1⟩
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    rw [cached.expr_ops_c.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.let_e hty hw hbo h1⟩
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    rw [cached.expr_ops_c.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.lit hl h1⟩
  | @proj s i x e hs hx h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    rw [cached.expr_ops_c.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.proj hs hx h1⟩

/-- **`expr_ops_c::get_app_args_acc` refines `ExprC.getAppArgsAcc`**
(`ExprOpsC.lean:70-73`) *with the accumulator at the other end*: the cited
`a :: acc` is a front cons, which a `Vec` cannot do in `O(1)`, so the port
pushes after the recursive call and the lemma carries `absExprs acc ++ …`.
The two agree at `acc = []`, which is the only way the cited code calls it
(`getAppArgsAcc_spec`: `getAppArgsAcc e acc = Expr.getAppArgs e ++ acc`). -/
theorem get_app_args_acc_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ (acc r : alloc.vec.Vec expr.Expr), ExprsWF acc →
      cached.expr_ops_c.get_app_args_acc e acc = ok r →
      absExprs r = absExprs acc ++ ConLeche.Expr.getAppArgs (absExpr e) ∧ ExprsWF r := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro acc r hacc h
    rw [cached.expr_ops_c.get_app_args_acc.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hacc⟩
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro acc r hacc h
    rw [cached.expr_ops_c.get_app_args_acc.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hacc⟩
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro acc r hacc h
    rw [cached.expr_ops_c.get_app_args_acc.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hacc⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro acc r hacc h
    rw [cached.expr_ops_c.get_app_args_acc.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hacc⟩
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    intro acc r hacc h
    rw [cached.expr_ops_c.get_app_args_acc.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨out2, hrec, c, hdup, hpush⟩ := h
    obtain ⟨habs, hwf⟩ := ihf acc out2 hacc hrec
    rw [Expr.dup_eq hdup] at hpush
    refine ⟨?_, exprsWF_push hwf ha hpush⟩
    rw [absExprs_push hpush, habs, List.append_assoc]
    simp [ConLeche.Expr.getAppArgs]
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro acc r hacc h
    rw [cached.expr_ops_c.get_app_args_acc.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hacc⟩
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro acc r hacc h
    rw [cached.expr_ops_c.get_app_args_acc.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hacc⟩
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro acc r hacc h
    rw [cached.expr_ops_c.get_app_args_acc.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hacc⟩
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro acc r hacc h
    rw [cached.expr_ops_c.get_app_args_acc.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hacc⟩
  | @proj s i x e hs hx h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro acc r hacc h
    rw [cached.expr_ops_c.get_app_args_acc.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hacc⟩

/-- **`expr_ops_c::get_app_args` refines `ExprC.getAppArgs`**
(`ExprOpsC.lean:75-76`): the `acc = []` wrapper, where the port's push order
and the cited front cons agree. -/
theorem get_app_args_refines {e : expr.Expr} {r : alloc.vec.Vec expr.Expr}
    (he : ExprWF e) (h : cached.expr_ops_c.get_app_args e = ok r) :
    absExprs r = ConLeche.Cached.ExprC.getAppArgs (absExpr e) ∧ ExprsWF r := by
  rw [cached.expr_ops_c.get_app_args] at h
  obtain ⟨habs, hwf⟩ := get_app_args_acc_refines he _ r exprsWF_new h
  rw [ConLeche.Cached.ExprC.getAppArgs_spec]
  exact ⟨by rw [habs]; simp, hwf⟩

/-- **`expr_ops_c::mk_app_n_from` refines `ExprC.mkAppN`**
(`ExprOpsC.lean:78-81`) at the arguments from `i` on; the induction is on the
`Nat` measure `args.length - i`, the generated function being a
`partial_fixpoint`. -/
theorem mk_app_n_from_refines (N : Nat) :
    ∀ (f : expr.Expr) (args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (r : expr.Expr),
      args.val.length - i.val = N → ExprWF f → ExprsWF args →
      cached.expr_ops_c.mk_app_n_from f args i = ok r →
      absExpr r = ConLeche.Cached.ExprC.mkAppN (absExpr f) ((absExprs args).drop i.val) ∧
        ExprWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro f args i r hN hf hargs h
    rw [ConLeche.Cached.ExprC.mkAppN_spec]
    rw [cached.expr_ops_c.mk_app_n_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : args.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      rw [← Result.ok_injective h]
      refine ⟨?_, hf⟩
      rw [List.drop_eq_nil_of_le (by simpa [absExprs] using hlen)]
      simp [ConLeche.Expr.mkAppN]
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, c, hdup, a2, happ, i2, hi2, hrec⟩ := h
      obtain ⟨hlt, hxwf, hdrop⟩ := vec_index_expr hargs hidx
      rw [Expr.dup_eq hdup] at happ
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨habs, hwf⟩ := ih (args.val.length - i2.val) (by omega) a2 args i2 r rfl
        (Expr.app_wf hf hxwf happ) hargs hrec
      refine ⟨?_, hwf⟩
      rw [ConLeche.Cached.ExprC.mkAppN_spec] at habs
      rw [habs, Expr.app_refines happ, hi2v, hdrop]
      simp [ConLeche.Expr.mkAppN]

/-- **`expr_ops_c::mk_app_n` refines `ExprC.mkAppN`** (`ExprOpsC.lean:78-81`):
the `i = 0` wrapper. -/
theorem mk_app_n_refines {f : expr.Expr} {args : alloc.vec.Vec expr.Expr}
    {r : expr.Expr} (hf : ExprWF f) (hargs : ExprsWF args)
    (h : cached.expr_ops_c.mk_app_n f args = ok r) :
    absExpr r = ConLeche.Cached.ExprC.mkAppN (absExpr f) (absExprs args) ∧ ExprWF r := by
  rw [cached.expr_ops_c.mk_app_n] at h
  obtain ⟨habs, hwf⟩ := mk_app_n_from_refines _ f args 0#usize r rfl hf hargs h
  refine ⟨?_, hwf⟩
  rw [habs, show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]

/-! ## The `Vec` reversal with no Lean counterpart

`rev_append_exprs out xs k` is `out ++ xs.reverse` written as the downward index
recursion `xs[k-1]`, `xs[k-2]`, …: a `Vec` reversal copies the spine, as Lean's
`List.reverse` allocates.  Its lemma is therefore a *raw* `Vec` equation, like
task #47's `levels_copy_val` and `cons_expr_val` -- there is nothing to abstract
it against. -/

/-- `expr_ops_c::rev_append_exprs` appends the first `k` entries of `xs`, in
reverse, to `out`.  The guard `k > xs.len()` is what makes the statement need
`k.val ≤ xs.val.length`; at the two call sites `k` *is* the length. -/
theorem rev_append_exprs_val (N : Nat) :
    ∀ (out xs r : alloc.vec.Vec expr.Expr) (k : Std.Usize),
      k.val = N → k.val ≤ xs.val.length →
      cached.expr_ops_c.rev_append_exprs out xs k = ok r →
      r.val = out.val ++ (xs.val.take k.val).reverse := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro out xs r k hN hle h
    rw [cached.expr_ops_c.rev_append_exprs.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hz
      rw [← Result.ok_injective h, hz]
      simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
    · rename_i hz
      have hkpos : 0 < k.val := by
        have : k.val ≠ 0 := fun hc =>
          hz (Std.UScalar.eq_of_val_eq (by rw [hc]; symm; scalar_tac))
        omega
      split at h
      · rename_i hgt
        have := alloc.vec.Vec.len_val xs
        exact absurd hle (by scalar_tac)
      · simp only [bind_eq_ok_iff] at h
        obtain ⟨i1, hi1, x, hidx, c, hdup, out1, hpush, hrec⟩ := h
        have hi1v : i1.val = k.val - 1 := HashMap.uscalar_sub_eq hi1
        have hlt : i1.val < xs.val.length := by omega
        have hx : xs.val[i1.val]? = some x := vec_index_getElem? hidx
        rw [Expr.dup_eq hdup] at hpush
        rw [ih i1.val (by omega) out1 xs r i1 rfl (by omega) hrec,
          vec_push_val hpush]
        have hsplit : xs.val.take k.val = xs.val.take i1.val ++ [x] := by
          have : k.val = i1.val + 1 := by omega
          rw [this, List.take_add_one, hx]
          rfl
        rw [hsplit, List.reverse_append]
        simp

/-! ## The two extra memo probes

`memo_b1_get` and `seen_get` are `expr_ops::memo_b_get`'s siblings at the
`(node, cursor)` key with `Bool` values and at the node key with `Unit` values:
a `match memo[k]?` whose borrow must end before the miss branch mutates the
table (task #13's pattern 1).  Their lemmas say the same thing its does -- a hit
is a real `HashMap.get` hit -- with nothing claimed on a miss. -/

/-- A `memo_b1_get` hit is a `HashMap.get` hit. -/
theorem memo_b1_get_hit {m : ron.hashmap.HashMap expr_ops.ExprNatKey Bool}
    {k : expr_ops.ExprNatKey} {r : Bool}
    (h : cached.expr_ops_c.memo_b1_get m k = ok (some r)) :
    ron.hashmap.HashMap.get expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapHashable
      expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapEq2 m k = ok (some r) := by
  rw [cached.expr_ops_c.memo_b1_get] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, h⟩ := h
  cases o with
  | none => simp at h
  | some w => simp only [Result.ok.injEq, Option.some.injEq] at h; rw [hget, h]

/-- A `seen_get` hit is a `HashMap.get` hit (the value is `Unit`, so the hit
carries no information beyond "this node has been visited"). -/
theorem seen_get_hit {m : ron.hashmap.HashMap expr.Expr Unit} {k : expr.Expr}
    (h : cached.expr_ops_c.seen_get m k = ok (some ())) :
    ∃ u, ron.hashmap.HashMap.get expr.Expr.Insts.Con_ron_coreRonHashmapHashable
      expr.Expr.Insts.Con_ron_coreRonHashmapEq2 m k = ok (some u) := by
  rw [cached.expr_ops_c.seen_get] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, h⟩ := h
  cases o with
  | none => simp at h
  | some w => exact ⟨w, hget⟩

/-- A `seen_get` miss is a `HashMap.get` miss. -/
theorem seen_get_miss {m : ron.hashmap.HashMap expr.Expr Unit} {k : expr.Expr}
    (h : cached.expr_ops_c.seen_get m k = ok none) :
    ron.hashmap.HashMap.get expr.Expr.Insts.Con_ron_coreRonHashmapHashable
      expr.Expr.Insts.Con_ron_coreRonHashmapEq2 m k = ok none := by
  rw [cached.expr_ops_c.seen_get] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, h⟩ := h
  cases o with
  | none => rw [hget]
  | some w => simp at h

/-! ## `leafMem` (`ExprOpsC.lean:709-714`)

The membership test behind the fabrication leaf guard.  The port walks the
`Vec` by an index, so its lemma is at `(absLeaves bl).drop i`, and the
annotation comparison is `expr::beq` -- exact on well-formed nodes
(`Expr.beq_refines`), which is why `LeavesWF` is a hypothesis. -/

/-- Indexing a well-formed leaf list: the entry's expression is well formed,
and the abstracted list's `drop` peels the pair off. -/
theorem drop_absLeaves {bl : alloc.vec.Vec (Std.U64 × expr.Expr)} {i : Std.Usize}
    {x : Std.U64 × expr.Expr} (hbl : LeavesWF bl)
    (h : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice (Std.U64 × expr.Expr)) bl i = ok x) :
    i.val < bl.val.length ∧ ExprWF x.2 ∧
      (absLeaves bl).drop i.val
        = (x.1.val, absExpr x.2) :: (absLeaves bl).drop (i.val + 1) := by
  have hg := vec_index_getElem? h
  have hlt : i.val < bl.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : bl.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  refine ⟨hlt, hbl x (by rw [← hx]; exact List.getElem_mem hlt), ?_⟩
  rw [absLeaves, List.drop_eq_getElem_cons (by simpa using hlt), List.getElem_map, hx]

/-- **`expr_ops_c::leaf_mem_from` refines `ExprC.leafMem`**
(`ExprOpsC.lean:709-714`) at the entries from `i` on.  Deviation: the cited
`(i == idx && t == ty) || leafMem rest idx ty` is an `if` nest (task #3's
pattern 9), which is the same `Bool`. -/
theorem leaf_mem_from_refines (N : Nat) :
    ∀ (bl : alloc.vec.Vec (Std.U64 × expr.Expr)) (i : Std.Usize) (idx : Std.U64)
      (ty : expr.Expr) (b : Bool),
      bl.val.length - i.val = N → LeavesWF bl → ExprWF ty →
      cached.expr_ops_c.leaf_mem_from bl i idx ty = ok b →
      b = ConLeche.Cached.ExprC.leafMem ((absLeaves bl).drop i.val) idx.val
        (absExpr ty) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro bl i idx ty b hN hbl hty h
    rw [cached.expr_ops_c.leaf_mem_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : bl.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val bl; scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [absLeaves] using hlen)]
      rfl
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, h⟩ := h
      obtain ⟨hlt, hxwf, hdrop⟩ := drop_absLeaves hbl hidx
      obtain ⟨xi, xe⟩ := x
      dsimp only at hdrop hxwf
      -- the generated body destructures the indexed pair in a `let`, which
      -- `split` does not see through; naming the iota-reduced form does.
      have h2 : (if xi = idx then
            do
            let c ← expr.beq xe ty
            if c = true then ok true
            else do
              let i3 ← i + 1#usize
              cached.expr_ops_c.leaf_mem_from bl i3 idx ty
          else do
            let i3 ← i + 1#usize
            cached.expr_ops_c.leaf_mem_from bl i3 idx ty) = ok b := h
      clear h
      rw [hdrop, ConLeche.Cached.ExprC.leafMem]
      split at h2
      · rename_i heq
        have heqv : xi.val = idx.val := by rw [heq]
        obtain ⟨c, hbeq, h2⟩ := bind_eq_ok_iff.mp h2
        have hc : c = decide (absExpr xe = absExpr ty) :=
          Expr.beq_refines hxwf hty hbeq
        cases c with
        | true =>
          have habs : absExpr xe = absExpr ty := of_decide_eq_true hc.symm
          simp only [if_true, Result.ok.injEq] at h2
          rw [← h2]
          simp [heqv, habs]
        | false =>
          have hne : absExpr xe ≠ absExpr ty := of_decide_eq_false hc.symm
          simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h2
          obtain ⟨i3, hi3, hrec⟩ := h2
          have hi3v : i3.val = i.val + 1 := HashMap.uscalar_add_eq hi3
          rw [ih (bl.val.length - i3.val) (by omega) bl i3 idx ty b rfl hbl hty hrec,
            hi3v]
          simp [hne]
      · rename_i hne
        have hnev : xi.val ≠ idx.val := fun hc => hne (Std.UScalar.eq_of_val_eq hc)
        simp only [bind_eq_ok_iff] at h2
        obtain ⟨i3, hi3, hrec⟩ := h2
        have hi3v : i3.val = i.val + 1 := HashMap.uscalar_add_eq hi3
        rw [ih (bl.val.length - i3.val) (by omega) bl i3 idx ty b rfl hbl hty hrec,
          hi3v]
        simp [hnev]

/-- **`expr_ops_c::leaf_mem` refines `ExprC.leafMem`**
(`ExprOpsC.lean:709-714`): the `i = 0` wrapper. -/
theorem leaf_mem_refines {bl : alloc.vec.Vec (Std.U64 × expr.Expr)} {idx : Std.U64}
    {ty : expr.Expr} {b : Bool} (hbl : LeavesWF bl) (hty : ExprWF ty)
    (h : cached.expr_ops_c.leaf_mem bl idx ty = ok b) :
    b = ConLeche.Cached.ExprC.leafMem (absLeaves bl) idx.val (absExpr ty) := by
  rw [cached.expr_ops_c.leaf_mem] at h
  rw [leaf_mem_from_refines _ bl 0#usize idx ty b rfl hbl hty h,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]

end ConRon.Refine.ExprOpsC
