/-
`CORE_PLAN.md` step 4 (task #49), the `prop_read` slice: the refinement of all
eleven `pub fn` of `crates/con-ron-core/src/kernel/prop_read.rs` against
`vendor/con-leche/ConLeche/Kernel/PropRead.lean` (con-leche's task #168), on
the generated model `ConRon.Generated.kernel.prop_read.*`.

The module is two three-valued readers -- "is this type a proposition?"
(`typeSortPW`) and "is this term a proof?" (`proofPW`) -- off the head symbol,
the arity and the validated `pw` annotations, plus the four small pieces they
share (`peelNeverPis`, `numArgs`, `residualPW`, `isProp`) and the two Boolean
verdicts (`notProofFast`, `isProofFast`).  Statements are
exact-result-on-success (DESIGN.md §3.5): an `Option`-returning reader gets an
`Option.map absPropWhen` equation -- so the `none` ("unknown, fall back to
inference") case is a claim too -- plus `PropWhenWF` of the datum, which the
callers store.

**The one standing deviation** (the Rust module note): the cited Lean abstracts
every reader over `find? : Name → Option ConstantInfo` so that the pure
`Env.find?` and the interned `FEnv.find?` share one body.  The port has a
single environment on the checker's path, `fe: &FEnv` with `fenv::find`, so
every reader that takes `fe` is stated with `(hfe : FindAgree fe lfe)` (and
`(hwf : FindWF fe)`, because what a lookup hands back is used as a term) and
against the cited Lean **instantiated at `lfe.find?`**.

Three things shaped the proofs:

* `peel_never_pis` is a `u64`-counted recursion under `partial_fixpoint`, which
  gives no induction principle, so it is the task-#5 shape: a `(N : Nat)`
  lemma with `k.val = N`, inducted on `k` (`Nat.strong_induction_on`), and the
  wrapper is the corollary.  Every other reader here is structurally flat --
  one `match` on the head node -- so its proof is a `cases` on the `ExprWF`
  derivation, not an induction.
* `stored_cv_at` is a *port-invented factorization*: it is the `some ci => if
  ci.isTowerEntry then none else …` prefix that `headTypePW` and `headProofPW`
  both open with, pulled out as a probe (task #14's rule).  It has no cited
  Lean definition of its own, so `storedCVAt` below is that prefix written out
  once on the con-leche side, and the two head readers rewrite with it.
* `env::is_tower_entry` and `env::to_constant_val` belong to `kernel::env`
  (task #46's `Refine/Env.lean`), but `stored_cv_at` cannot be stated without
  them; they are proved here, locally, and should move.  `to_constant_val`'s
  refinement is stated on `absConstantVal` rather than on the `ConstantVal`
  record itself: the port's `ProjInfo` arm *builds* a value where Lean shares
  one, and the `Vec<Name>` copy of the other arms is equal only up to `.val`.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.PropRead

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.PropRead


/-! ## `kernel::env`'s two `ConstantInfo` readers (they belong to task #46) -/

/-- `env::is_tower_entry` refines `ConstantInfo.isTowerEntry`
(`ConLeche/Kernel/Env.lean:616-618`). -/
theorem is_tower_entry_refines {ci : env.ConstantInfo} {b : Bool}
    (h : env.is_tower_entry ci = ok b) :
    b = (absConstantInfo ci).isTowerEntry := by
  rw [env.is_tower_entry.eq_def] at h
  cases ci <;> simp_all [absConstantInfo, ConLeche.ConstantInfo.isTowerEntry]

/-- `env::constant_val_dup` copies: the abstraction is unchanged and
well-formedness is preserved (the `Vec<Name>` copy is equal only up to
`.val`, which is all `absNames` reads). -/
theorem constant_val_dup_refines {cv c : env.ConstantVal} (hcv : ConstantValWF cv)
    (h : env.constant_val_dup cv = ok c) :
    absConstantVal c = absConstantVal cv ∧ ConstantValWF c := by
  rw [env.constant_val_dup] at h
  simp only [name_dup_eq, bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨v, hv, e, he, hc⟩ := h
  obtain ⟨hn, hps, hty⟩ := hcv
  have hvv : v.val = cv.level_params.val := PropWhen.names_copy_val hv
  rw [Expr.dup_eq he] at hc
  subst hc
  refine ⟨?_, hn, ?_, hty⟩
  · simp only [absConstantVal, absNames, hvv]
  · intro n hn2; exact hps n (by rw [hvv] at hn2; exact hn2)

/-- `env::to_constant_val` refines `ConstantInfo.toConstantVal`
(`ConLeche/Kernel/Env.lean:606-609`).  The `ProjInfo` arm is the interesting
one: con-leche *shares* `tbl.levelParams` and writes the reserved name and
`Sort 1` inline, the port builds all three (task #14's note). -/
theorem to_constant_val_refines {ci : env.ConstantInfo} {cv : env.ConstantVal}
    (hci : ConstantInfoWF ci) (h : env.to_constant_val ci = ok cv) :
    absConstantVal cv = (absConstantInfo ci).toConstantVal ∧ ConstantValWF cv := by
  rw [env.to_constant_val.eq_def] at h
  cases ci with
  | ProjInfo tbl =>
    obtain ⟨hsn, hlp, -, -, -, -⟩ := hci
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨n, hn, v, hv, l, hl, l1, hl1, e, he, hcv⟩ := h
    obtain ⟨hnabs, hnwf⟩ := proj_table_name_refines hsn hn
    have hvv : v.val = tbl.level_params.val := PropWhen.names_copy_val hv
    have hlwf : LevelWF l1 := Level.succ_wf (Level.zero_wf hl) hl1
    subst hcv
    refine ⟨?_, hnwf, ?_, Expr.sort_wf hlwf he⟩
    · simp only [absConstantVal, absNames, hvv, hnabs, absConstantInfo,
        ConLeche.ConstantInfo.toConstantVal, absProjTable,
        Expr.sort_refines he, Level.succ_refines hl1, Level.zero_refines hl]
    · intro m hm; exact hlp m (by rw [hvv] at hm; exact hm)
  | AxiomInfo v =>
    obtain ⟨habs, hwf⟩ := constant_val_dup_refines hci h
    exact ⟨by rw [habs]; rfl, hwf⟩
  | DefnInfo v x hint =>
    obtain ⟨habs, hwf⟩ := constant_val_dup_refines hci.1 h
    exact ⟨by rw [habs]; rfl, hwf⟩
  | ThmInfo v x =>
    obtain ⟨habs, hwf⟩ := constant_val_dup_refines hci.1 h
    exact ⟨by rw [habs]; rfl, hwf⟩
  | IndInfo v c =>
    obtain ⟨habs, hwf⟩ := constant_val_dup_refines hci.1 h
    exact ⟨by rw [habs]; rfl, hwf⟩
  | CtorInfo v np nf =>
    obtain ⟨habs, hwf⟩ := constant_val_dup_refines hci h
    exact ⟨by rw [habs]; rfl, hwf⟩
  | RecInfo v mi rp rs =>
    obtain ⟨habs, hwf⟩ := constant_val_dup_refines hci.1 h
    exact ⟨by rw [habs]; rfl, hwf⟩

/-! ## `stored_cv_at`, the shared prefix of the two head readers -/

/-- The `some ci => if ci.isTowerEntry then none else let cv := ci.toConstantVal;
if us.length = cv.levelParams.length …` prefix that both `headTypePW`
(`PropRead.lean:73-90`) and `headProofPW` (`PropRead.lean:105-122`) open with,
written out once: `prop_read::stored_cv_at` is the port's name for it
(a probe, per task #14's rule), so this is what its refinement is stated
against, and the two head readers rewrite the prefix of their cited body with
`storedCVAt` before appealing to it. -/
def storedCVAt (find? : ConLeche.Name → Option ConLeche.ConstantInfo)
    (n : ConLeche.Name) (nUs : Nat) : Option ConLeche.ConstantVal :=
  match find? n with
  | some ci =>
    if ci.isTowerEntry then none else
    let cv := ci.toConstantVal
    if nUs = cv.levelParams.length then some cv else none
  | none => none

/-- `storedCVAt`'s three arms, in the shape the proofs below use them. -/
theorem storedCVAt_miss {find? : ConLeche.Name → Option ConLeche.ConstantInfo}
    {n : ConLeche.Name} {nUs : Nat} (h : find? n = none) :
    storedCVAt find? n nUs = none := by simp [storedCVAt, h]

theorem storedCVAt_tower {find? : ConLeche.Name → Option ConLeche.ConstantInfo}
    {n : ConLeche.Name} {nUs : Nat} {ci : ConLeche.ConstantInfo} (h : find? n = some ci)
    (ht : ci.isTowerEntry = true) : storedCVAt find? n nUs = none := by
  simp [storedCVAt, h, ht]

theorem storedCVAt_hit {find? : ConLeche.Name → Option ConLeche.ConstantInfo}
    {n : ConLeche.Name} {nUs : Nat} {ci : ConLeche.ConstantInfo} (h : find? n = some ci)
    (ht : ci.isTowerEntry = false) :
    storedCVAt find? n nUs =
      (if nUs = ci.toConstantVal.levelParams.length then some ci.toConstantVal
       else none) := by
  simp [storedCVAt, h, ht]

/-- `prop_read::stored_cv_at` refines `storedCVAt` at `lfe.find?` (the module
deviation).  `FindWF` is what makes the record it hands back usable as a term. -/
theorem stored_cv_at_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {n_us : Std.Usize} {r : Option env.ConstantVal}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (hn : NameWF n)
    (h : prop_read.stored_cv_at fe n n_us = ok r) :
    r.map absConstantVal = storedCVAt lfe.find? (absName n) n_us.val ∧
      ∀ cv ∈ r, ConstantValWF cv := by
  rw [prop_read.stored_cv_at] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  cases o with
  | none =>
    simp only [Result.ok.injEq] at h
    rw [← h, storedCVAt_miss (hfe.find_none hn ho)]
    exact ⟨by simp, by simp⟩
  | some ci =>
    have hfind := hfe.find_some hn ho
    have hciwf := hwf n ci hn ho
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbabs := is_tower_entry_refines hb
    split at h
    · rename_i hbt
      simp only [Result.ok.injEq] at h
      rw [← h, storedCVAt_tower hfind (by rw [← hbabs, hbt])]
      exact ⟨by simp, by simp⟩
    · rename_i hbf
      have hbf' : (absConstantInfo ci).isTowerEntry = false := by
        rw [← hbabs]; exact Bool.eq_false_iff.mpr hbf
      simp only [bind_eq_ok_iff] at h
      obtain ⟨cv, hcv, h⟩ := h
      obtain ⟨hcvabs, hcvwf⟩ := to_constant_val_refines hciwf hcv
      have hlen : ((absConstantInfo ci).toConstantVal).levelParams.length
          = cv.level_params.val.length := by
        rw [← hcvabs]; simp [absConstantVal, absNames]
      rw [storedCVAt_hit hfind hbf']
      split at h
      · rename_i heq
        have heqv : n_us.val = cv.level_params.val.length := by rw [heq]; simp
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine ⟨?_, ?_⟩
        · rw [Option.map_some, hcvabs, if_pos (by rw [hlen]; exact heqv)]
        · intro x hx; rw [Option.mem_def, Option.some.injEq] at hx; rw [← hx]; exact hcvwf
      · rename_i hne
        have hnev : n_us.val ≠ cv.level_params.val.length := fun hc =>
          hne (Std.UScalar.eq_of_val_eq (by rw [hc]; simp))
        simp only [Result.ok.injEq] at h
        rw [← h, if_neg (by rw [hlen]; exact hnev)]
        exact ⟨by simp, by simp⟩

/-! ## `peel_never_pis` and `num_args` -/

/-- `prop_read::peel_never_pis` refines `Expr.peelNeverPis`
(`PropRead.lean:44-56`), in the task-#5 shape for a `u64`-counted recursion:
`partial_fixpoint` gives no induction principle, so the lemma is parametrised
by `N = k.val` and inducted on `N`. -/
theorem peel_never_pis_refines_aux (N : Nat) :
    ∀ (k : Std.U64) (e : expr.Expr) (r : Option expr.Expr),
      k.val = N → ExprWF e → prop_read.peel_never_pis k e = ok r →
      r.map absExpr = ConLeche.Expr.peelNeverPis k.val (absExpr e) ∧
        ∀ x ∈ r, ExprWF x := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k e r hN he h
    rw [prop_read.peel_never_pis.eq_def] at h
    split at h
    · rename_i hk0
      have hkv : k.val = 0 := by rw [hk0]; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr, hkv]
      exact ⟨by simp [ConLeche.Expr.peelNeverPis], by
        intro x hx; rw [Option.mem_def, Option.some.injEq] at hx; rw [← hx]; exact he⟩
    · rename_i hk0
      obtain ⟨m, hm⟩ : ∃ m, k.val = m + 1 := by
        have : k.val ≠ 0 := fun hc => hk0 (Std.UScalar.eq_of_val_eq (by rw [hc]; scalar_tac))
        exact ⟨k.val - 1, by omega⟩
      cases he with
      | @bvar i e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hm]
        exact ⟨by simp [ConLeche.Expr.peelNeverPis], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hm]
        exact ⟨by simp [ConLeche.Expr.peelNeverPis], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hm]
        exact ⟨by simp [ConLeche.Expr.peelNeverPis], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hm]
        exact ⟨by simp [ConLeche.Expr.peelNeverPis], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hm]
        exact ⟨by simp [ConLeche.Expr.peelNeverPis], by simp⟩
      | @lam ty bo mt e hty hbo hmt h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hm]
        exact ⟨by simp [ConLeche.Expr.peelNeverPis], by simp⟩
      | @forall_e ty bo mt e hty hbo hmt h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
        obtain ⟨b1, hb1, h⟩ := h
        have hb1abs := PropWhen.is_never_refines hb1
        split at h
        · rename_i hb1t
          simp only [bind_eq_ok_iff] at h
          obtain ⟨i, hi, hrec⟩ := h
          have hiv : i.val = m := by rw [HashMap.uscalar_sub_eq hi, hm]; scalar_tac
          obtain ⟨habs, hwf⟩ := ih m (by omega) i bo r hiv hbo hrec
          refine ⟨?_, hwf⟩
          rw [habs, hiv, hm]
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.peelNeverPis,
            absBinderMeta, if_pos (by rw [← hb1abs, hb1t] : (absPropWhen mt.pw).isNever = true)]
        · rename_i hb1f
          have hb1f' : (absPropWhen mt.pw).isNever = false := by
            rw [← hb1abs]; exact Bool.eq_false_iff.mpr hb1f
          rw [← Result.ok_injective h, hm]
          refine ⟨?_, by simp⟩
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.peelNeverPis,
            absBinderMeta, hb1f']
          simp
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hm]
        exact ⟨by simp [ConLeche.Expr.peelNeverPis], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hm]
        exact ⟨by simp [ConLeche.Expr.peelNeverPis], by simp⟩
      | @proj sn i x e hsn hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hm]
        exact ⟨by simp [ConLeche.Expr.peelNeverPis], by simp⟩

/-- `prop_read::peel_never_pis` refines `Expr.peelNeverPis`
(`PropRead.lean:44-56`): the `N = k.val` corollary. -/
theorem peel_never_pis_refines {k : Std.U64} {e : expr.Expr} {r : Option expr.Expr}
    (he : ExprWF e) (h : prop_read.peel_never_pis k e = ok r) :
    r.map absExpr = ConLeche.Expr.peelNeverPis k.val (absExpr e) ∧ ∀ x ∈ r, ExprWF x :=
  peel_never_pis_refines_aux _ k e r rfl he h

/-- `prop_read::num_args` refines `Expr.numArgs` (`PropRead.lean:58-61`).  A
`u64` result, so the equation is on `.val`; nothing is claimed when the count
overflows (exact-result-on-success). -/
theorem num_args_refines {e : expr.Expr} {r : Std.U64} (he : ExprWF e)
    (h : prop_read.num_args e = ok r) : r.val = ConLeche.Expr.numArgs (absExpr e) := by
  induction he generalizing r with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    rw [prop_read.num_args.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.numArgs]
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    rw [prop_read.num_args.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.numArgs]
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    rw [prop_read.num_args.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.numArgs]
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    rw [prop_read.num_args.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.numArgs]
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    rw [prop_read.num_args.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    obtain ⟨i, hi, hr⟩ := bind_eq_ok_iff.mp h
    rw [HashMap.uscalar_add_eq hr, ihf hi]
    simp [ConLeche.Expr.numArgs]
  | @lam ty bo mt e hty hbo hmt h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    rw [prop_read.num_args.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.numArgs]
  | @forall_e ty bo mt e hty hbo hmt h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    rw [prop_read.num_args.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.numArgs]
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    rw [prop_read.num_args.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.numArgs]
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    rw [prop_read.num_args.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.numArgs]
  | @proj sn i x e hsn hx h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    rw [prop_read.num_args.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.numArgs]

/-! ## `residual_pw` and `head_type_pw` -/

/-- `prop_read::residual_pw` refines `residualPW` (`PropRead.lean:65-71`).  The
argument is taken by value in the port -- it is always a fresh
`peel_never_pis` result -- so the hypothesis is `ExprWF` of what it holds. -/
theorem residual_pw_refines {e : Option expr.Expr} {r : Option prop_when.PropWhen}
    (he : ∀ x ∈ e, ExprWF x) (h : prop_read.residual_pw e = ok r) :
    r.map absPropWhen = ConLeche.residualPW (e.map absExpr) ∧ ∀ pw ∈ r, PropWhenWF pw := by
  rw [prop_read.residual_pw.eq_def] at h
  cases e with
  | none =>
    simp only [Result.ok.injEq] at h
    rw [← h]; exact ⟨by simp [ConLeche.residualPW], by simp⟩
  | some x =>
    have hx : ExprWF x := he x rfl
    cases hx with
    | @sort u e hu h1 =>
      obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff,
        Result.ok.injEq] at h
      obtain ⟨pw, hpw, hr⟩ := h
      obtain ⟨habs, hwf⟩ := ExprOps.zeroness_of_refines hu pw hpw
      rw [← hr]
      refine ⟨?_, ?_⟩
      · simp only [Option.map_some, habs, absExpr_mk, absExprKind]
        simp [ConLeche.residualPW]
      · intro q hq; rw [Option.mem_def, Option.some.injEq] at hq; rw [← hq]; exact hwf
    | @bvar i e h1 =>
      obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [ConLeche.residualPW], by simp⟩
    | @fvar idx ty e hty h1 =>
      obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [ConLeche.residualPW], by simp⟩
    | @mk_const n us e hn hus h1 =>
      obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [ConLeche.residualPW], by simp⟩
    | @app f a e hf ha h1 =>
      obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [ConLeche.residualPW], by simp⟩
    | @lam ty bo mt e hty hbo hmt h1 =>
      obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [ConLeche.residualPW], by simp⟩
    | @forall_e ty bo mt e hty hbo hmt h1 =>
      obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [ConLeche.residualPW], by simp⟩
    | @let_e ty w bo e hty hw hbo h1 =>
      obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [ConLeche.residualPW], by simp⟩
    | @lit l e hl h1 =>
      obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [ConLeche.residualPW], by simp⟩
    | @proj sn i x e hsn hx2 h1 =>
      obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [ConLeche.residualPW], by simp⟩

/-- The cited `headTypePW`'s constant arm, refactored through `storedCVAt`: this
is the equation that lines the cited body up with the port's two-function
split. -/
theorem headTypePW_const (find? : ConLeche.Name → Option ConLeche.ConstantInfo)
    (I : ConLeche.Name) (us : List ConLeche.Level) (n : Nat) :
    ConLeche.headTypePW find? (.const I us) n =
      (storedCVAt find? I us.length).bind (fun cv =>
        (ConLeche.residualPW (ConLeche.Expr.peelNeverPis n cv.type)).map
          (ConLeche.Level.substPW cv.levelParams us)) := by
  rw [ConLeche.headTypePW, storedCVAt]
  cases hf : find? I with
  | none => simp
  | some ci =>
    by_cases ht : ci.isTowerEntry
    · simp [ht]
    · by_cases hl : us.length = ci.toConstantVal.levelParams.length
      · simp [ht, hl]
      · simp [ht, hl]

/-- `prop_read::head_type_pw` refines `headTypePW` at `lfe.find?`
(`PropRead.lean:73-90`).  The cited `Option.map` is an explicit `match` in the
port (§3.4 forbids closures), and the level-parameter probe is
`stored_cv_at`. -/
theorem head_type_pw_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {e : expr.Expr}
    {n : Std.U64} {r : Option prop_when.PropWhen}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (he : ExprWF e)
    (h : prop_read.head_type_pw fe e n = ok r) :
    r.map absPropWhen = ConLeche.headTypePW lfe.find? (absExpr e) n.val ∧
      ∀ pw ∈ r, PropWhenWF pw := by
  rw [prop_read.head_type_pw.eq_def] at h
  cases he with
  | @fvar idx ty e hty h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨o, ho, hres⟩ := h
    obtain ⟨hoabs, howf⟩ := peel_never_pis_refines hty ho
    obtain ⟨habs, hrwf⟩ := residual_pw_refines howf hres
    refine ⟨?_, hrwf⟩
    rw [habs, hoabs]
    simp [ConLeche.headTypePW]
  | @mk_const c us e hc hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    obtain ⟨hoabs, howf⟩ := stored_cv_at_refines hfe hwf hc ho
    have hst : storedCVAt lfe.find? (absName c) (absLevels us).length
        = o.map absConstantVal := by
      rw [show (absLevels us).length = (alloc.vec.Vec.len us).val by simp [absLevels]]
      exact hoabs.symm
    simp only [absExpr_mk, absExprKind, headTypePW_const, hst]
    cases o with
    | none =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact ⟨by simp, by simp⟩
    | some cv =>
      obtain ⟨hcvn, hcvp, hcvty⟩ := howf cv rfl
      simp only [bind_eq_ok_iff] at h
      obtain ⟨o1, ho1, o2, ho2, h⟩ := h
      obtain ⟨ho1abs, ho1wf⟩ := peel_never_pis_refines hcvty ho1
      obtain ⟨ho2abs, ho2wf⟩ := residual_pw_refines ho1wf ho2
      rw [ho1abs] at ho2abs
      have htype : (absConstantVal cv).type = absExpr cv.ty := rfl
      have hlp : (absConstantVal cv).levelParams = absNames cv.level_params := rfl
      simp only [Option.map_some, Option.bind_some, htype, hlp]
      cases o2 with
      | none =>
        simp only [Result.ok.injEq] at h
        rw [← h, ← ho2abs]
        exact ⟨by simp, by simp⟩
      | some pw =>
        simp only [bind_eq_ok_iff, Result.ok.injEq] at h
        obtain ⟨pw1, hpw1, hr⟩ := h
        obtain ⟨hpwabs, hpwwf⟩ := ExprOps.subst_pw_refines hcvp hus (ho2wf pw rfl) hpw1
        rw [← hr]
        refine ⟨?_, ?_⟩
        · rw [Option.map_some, hpwabs, ← ho2abs]
          simp
        · intro q hq; rw [Option.mem_def, Option.some.injEq] at hq; rw [← hq]; exact hpwwf
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headTypePW], by simp⟩
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headTypePW], by simp⟩
  | @app f a e hf ha h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headTypePW], by simp⟩
  | @lam ty bo mt e hty hbo hmt h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headTypePW], by simp⟩
  | @forall_e ty bo mt e hty hbo hmt h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headTypePW], by simp⟩
  | @let_e ty w bo e hty hw hbo h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headTypePW], by simp⟩
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headTypePW], by simp⟩
  | @proj sn i x e hsn hx h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headTypePW], by simp⟩

/-! ## `type_sort_pw` -/

/-- `prop_read::type_sort_pw` refines `typeSortPW` at `lfe.find?`
(`PropRead.lean:92-103`): a ∀ carries the datum on its binder, a sort's sort is
never zero, and everything else goes through the spine (`get_app_fn`,
`num_args`) into `head_type_pw`. -/
theorem type_sort_pw_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {t : expr.Expr}
    {r : Option prop_when.PropWhen}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ht : ExprWF t)
    (h : prop_read.type_sort_pw fe t = ok r) :
    r.map absPropWhen = ConLeche.typeSortPW lfe.find? (absExpr t) ∧
      ∀ pw ∈ r, PropWhenWF pw := by
  rw [prop_read.type_sort_pw.eq_def] at h
  cases ht with
  | @forall_e ty bo mt e hty hbo hmt h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨pw, hpw, hr⟩ := h
    rw [PropWhen.dup_eq hpw] at hr
    rw [← hr]
    refine ⟨?_, ?_⟩
    · simp [ConLeche.typeSortPW, absBinderMeta]
    · intro q hq; rw [Option.mem_def, Option.some.injEq] at hq; rw [← hq]; exact hmt
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨pw, hpw, hr⟩ := h
    rw [← hr]
    refine ⟨?_, ?_⟩
    · simp [ConLeche.typeSortPW, PropWhen.never_refines hpw]
    · intro q hq; rw [Option.mem_def, Option.some.injEq] at hq
      rw [← hq]; exact PropWhen.never_wf hpw
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, m, hm, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.bvar h1) hf
    obtain ⟨habs, hrwf⟩ := head_type_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs, num_args_refines (ExprWF.bvar h1) hm]
    simp [ConLeche.typeSortPW]
  | @fvar idx ty e hty h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, m, hm, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.fvar hty h1) hf
    obtain ⟨habs, hrwf⟩ := head_type_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs, num_args_refines (ExprWF.fvar hty h1) hm]
    simp [ConLeche.typeSortPW]
  | @mk_const c us e hc hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, m, hm, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.mk_const hc hus h1) hf
    obtain ⟨habs, hrwf⟩ := head_type_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs, num_args_refines (ExprWF.mk_const hc hus h1) hm]
    simp [ConLeche.typeSortPW]
  | @app f a e hf2 ha h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨g, hg, m, hm, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.app hf2 ha h1) hg
    obtain ⟨habs, hrwf⟩ := head_type_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs, num_args_refines (ExprWF.app hf2 ha h1) hm]
    simp [ConLeche.typeSortPW]
  | @lam ty bo mt e hty hbo hmt h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, m, hm, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.lam hty hbo hmt h1) hf
    obtain ⟨habs, hrwf⟩ := head_type_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs, num_args_refines (ExprWF.lam hty hbo hmt h1) hm]
    simp [ConLeche.typeSortPW]
  | @let_e ty w bo e hty hw hbo h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, m, hm, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.let_e hty hw hbo h1) hf
    obtain ⟨habs, hrwf⟩ := head_type_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs, num_args_refines (ExprWF.let_e hty hw hbo h1) hm]
    simp [ConLeche.typeSortPW]
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, m, hm, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.lit hl h1) hf
    obtain ⟨habs, hrwf⟩ := head_type_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs, num_args_refines (ExprWF.lit hl h1) hm]
    simp [ConLeche.typeSortPW]
  | @proj sn i x e hsn hx h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, m, hm, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.proj hsn hx h1) hf
    obtain ⟨habs, hrwf⟩ := head_type_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs, num_args_refines (ExprWF.proj hsn hx h1) hm]
    simp [ConLeche.typeSortPW]

/-! ## `head_proof_pw`, `proof_pw` and the two verdicts -/

/-- The cited `headProofPW`'s constant arm, refactored through `storedCVAt`
(the same equation as `headTypePW_const`, one reader up). -/
theorem headProofPW_const (find? : ConLeche.Name → Option ConLeche.ConstantInfo)
    (c : ConLeche.Name) (us : List ConLeche.Level) :
    ConLeche.headProofPW find? (.const c us) =
      (storedCVAt find? c us.length).bind (fun cv =>
        (ConLeche.typeSortPW find? cv.type).map
          (ConLeche.Level.substPW cv.levelParams us)) := by
  rw [ConLeche.headProofPW, storedCVAt]
  cases hf : find? c with
  | none => simp
  | some ci =>
    by_cases ht : ci.isTowerEntry
    · simp [ht]
    · by_cases hl : us.length = ci.toConstantVal.levelParams.length
      · simp [ht, hl]
      · simp [ht, hl]

/-- `prop_read::head_proof_pw` refines `headProofPW` at `lfe.find?`
(`PropRead.lean:105-122`): prop-ness is invariant under application, so a
constant head answers from its stored type at any arity; sorts, ∀s and literals
are never proofs. -/
theorem head_proof_pw_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {e : expr.Expr}
    {r : Option prop_when.PropWhen}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (he : ExprWF e)
    (h : prop_read.head_proof_pw fe e = ok r) :
    r.map absPropWhen = ConLeche.headProofPW lfe.find? (absExpr e) ∧
      ∀ pw ∈ r, PropWhenWF pw := by
  rw [prop_read.head_proof_pw.eq_def] at h
  cases he with
  | @fvar idx ty e hty h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    obtain ⟨habs, hrwf⟩ := type_sort_pw_refines hfe hwf hty h
    refine ⟨?_, hrwf⟩
    rw [habs]
    simp [ConLeche.headProofPW]
  | @mk_const c us e hc hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    obtain ⟨hoabs, howf⟩ := stored_cv_at_refines hfe hwf hc ho
    have hst : storedCVAt lfe.find? (absName c) (absLevels us).length
        = o.map absConstantVal := by
      rw [show (absLevels us).length = (alloc.vec.Vec.len us).val by simp [absLevels]]
      exact hoabs.symm
    simp only [absExpr_mk, absExprKind, headProofPW_const, hst]
    cases o with
    | none =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact ⟨by simp, by simp⟩
    | some cv =>
      obtain ⟨hcvn, hcvp, hcvty⟩ := howf cv rfl
      simp only [bind_eq_ok_iff] at h
      obtain ⟨o1, ho1, h⟩ := h
      obtain ⟨ho1abs, ho1wf⟩ := type_sort_pw_refines hfe hwf hcvty ho1
      have htype : (absConstantVal cv).type = absExpr cv.ty := rfl
      have hlp : (absConstantVal cv).levelParams = absNames cv.level_params := rfl
      simp only [Option.map_some, Option.bind_some, htype, hlp]
      cases o1 with
      | none =>
        simp only [Result.ok.injEq] at h
        rw [← h, ← ho1abs]
        exact ⟨by simp, by simp⟩
      | some pw =>
        simp only [bind_eq_ok_iff, Result.ok.injEq] at h
        obtain ⟨pw1, hpw1, hr⟩ := h
        obtain ⟨hpwabs, hpwwf⟩ := ExprOps.subst_pw_refines hcvp hus (ho1wf pw rfl) hpw1
        rw [← hr]
        refine ⟨?_, ?_⟩
        · rw [Option.map_some, hpwabs, ← ho1abs]
          simp
        · intro q hq; rw [Option.mem_def, Option.some.injEq] at hq; rw [← hq]; exact hpwwf
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨pw, hpw, hr⟩ := h
    rw [← hr]
    refine ⟨by simp [ConLeche.headProofPW, PropWhen.never_refines hpw], ?_⟩
    intro q hq; rw [Option.mem_def, Option.some.injEq] at hq
    rw [← hq]; exact PropWhen.never_wf hpw
  | @forall_e ty bo mt e hty hbo hmt h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨pw, hpw, hr⟩ := h
    rw [← hr]
    refine ⟨by simp [ConLeche.headProofPW, PropWhen.never_refines hpw], ?_⟩
    intro q hq; rw [Option.mem_def, Option.some.injEq] at hq
    rw [← hq]; exact PropWhen.never_wf hpw
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨pw, hpw, hr⟩ := h
    rw [← hr]
    refine ⟨by simp [ConLeche.headProofPW, PropWhen.never_refines hpw], ?_⟩
    intro q hq; rw [Option.mem_def, Option.some.injEq] at hq
    rw [← hq]; exact PropWhen.never_wf hpw
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headProofPW], by simp⟩
  | @app f a e hf ha h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headProofPW], by simp⟩
  | @lam ty bo mt e hty hbo hmt h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headProofPW], by simp⟩
  | @let_e ty w bo e hty hw hbo h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headProofPW], by simp⟩
  | @proj sn i x e hsn hx h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.headProofPW], by simp⟩

/-- `prop_read::proof_pw` refines `proofPW` at `lfe.find?`
(`PropRead.lean:124-134`): an unapplied λ answers from its own datum, everything
else from its spine head. -/
theorem proof_pw_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {a : expr.Expr}
    {r : Option prop_when.PropWhen}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ha : ExprWF a)
    (h : prop_read.proof_pw fe a = ok r) :
    r.map absPropWhen = ConLeche.proofPW lfe.find? (absExpr a) ∧
      ∀ pw ∈ r, PropWhenWF pw := by
  rw [prop_read.proof_pw.eq_def] at h
  cases ha with
  | @lam ty bo mt e hty hbo hmt h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨pw, hpw, hr⟩ := h
    rw [PropWhen.dup_eq hpw] at hr
    rw [← hr]
    refine ⟨by simp [ConLeche.proofPW, absBinderMeta], ?_⟩
    intro q hq; rw [Option.mem_def, Option.some.injEq] at hq; rw [← hq]; exact hmt
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.bvar h1) hf
    obtain ⟨habs, hrwf⟩ := head_proof_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs]; simp [ConLeche.proofPW]
  | @fvar idx ty e hty h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.fvar hty h1) hf
    obtain ⟨habs, hrwf⟩ := head_proof_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs]; simp [ConLeche.proofPW]
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.sort hu h1) hf
    obtain ⟨habs, hrwf⟩ := head_proof_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs]; simp [ConLeche.proofPW]
  | @mk_const c us e hc hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.mk_const hc hus h1) hf
    obtain ⟨habs, hrwf⟩ := head_proof_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs]; simp [ConLeche.proofPW]
  | @app f a e hf2 ha2 h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨g, hg, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.app hf2 ha2 h1) hg
    obtain ⟨habs, hrwf⟩ := head_proof_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs]; simp [ConLeche.proofPW]
  | @forall_e ty bo mt e hty hbo hmt h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.forall_e hty hbo hmt h1) hf
    obtain ⟨habs, hrwf⟩ := head_proof_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs]; simp [ConLeche.proofPW]
  | @let_e ty w bo e hty hw hbo h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.let_e hty hw hbo h1) hf
    obtain ⟨habs, hrwf⟩ := head_proof_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs]; simp [ConLeche.proofPW]
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.lit hl h1) hf
    obtain ⟨habs, hrwf⟩ := head_proof_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs]; simp [ConLeche.proofPW]
  | @proj sn i x e hsn hx h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f, hf, hhead⟩ := h
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines (ExprWF.proj hsn hx h1) hf
    obtain ⟨habs, hrwf⟩ := head_proof_pw_refines hfe hwf hfwf hhead
    refine ⟨?_, hrwf⟩
    rw [habs, hfabs]; simp [ConLeche.proofPW]

/-- `prop_read::is_prop` refines `PropWhen.isProp` (`PropRead.lean:136-139`):
the cited `pw == (.ifAllZero [])` goes through the port's `prop_when::beq`,
whose exactness on well-formed data is `PropWhen.beq_refines`. -/
theorem is_prop_refines {pw : prop_when.PropWhen} {b : Bool} (hpw : PropWhenWF pw)
    (h : prop_read.is_prop pw = ok b) :
    b = ConLeche.PropWhen.isProp (absPropWhen pw) := by
  rw [prop_read.is_prop] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨pw1, hpw1, hb⟩ := h
  have hnames : NamesWF (alloc.vec.Vec.new name.Name) := by
    intro q hq; simp [alloc.vec.Vec.new] at hq
  have hbeq : ∀ x y : ConLeche.PropWhen, decide (x = y) = (x == y) := by
    intro x y; rw [Bool.eq_iff_iff]; simp
  rw [PropWhen.beq_refines hpw (PropWhen.if_all_zero_wf hnames hpw1) hb,
    PropWhen.if_all_zero_refines hnames hpw1]
  simp [ConLeche.PropWhen.isProp, absNames, alloc.vec.Vec.new, hbeq]

/-- `prop_read::not_proof_fast` refines `notProofFast` at `lfe.find?`
(`PropRead.lean:141-146`).  The cited `!pw.isProp` is an `if` nest in the port:
a `!` in a *value* position comes out of Aeneas as a branch
(`core_k::defeq_lits`' note). -/
theorem not_proof_fast_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {a : expr.Expr}
    {c : Bool} (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ha : ExprWF a)
    (h : prop_read.not_proof_fast fe a = ok c) :
    c = ConLeche.notProofFast lfe.find? (absExpr a) := by
  rw [prop_read.not_proof_fast] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  obtain ⟨hoabs, howf⟩ := proof_pw_refines hfe hwf ha ho
  rw [ConLeche.notProofFast, ← hoabs]
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; simp
  | some pw =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbabs := is_prop_refines (howf pw rfl) hb
    split at h
    · rename_i hbt
      simp only [Result.ok.injEq] at h
      rw [← h, Option.map_some]
      simp [← hbabs, hbt]
    · rename_i hbf
      simp only [Result.ok.injEq] at h
      rw [← h, Option.map_some]
      simp [← hbabs, Bool.eq_false_iff.mpr hbf]

/-- `prop_read::is_proof_fast` refines `isProofFast` at `lfe.find?`
(`PropRead.lean:148-153`): the yes arm, the one the squash-regime licence of
`ConLeche/Model/Rules/DefEqSoundKit.lean` reads. -/
theorem is_proof_fast_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {a : expr.Expr}
    {c : Bool} (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ha : ExprWF a)
    (h : prop_read.is_proof_fast fe a = ok c) :
    c = ConLeche.isProofFast lfe.find? (absExpr a) := by
  rw [prop_read.is_proof_fast] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  obtain ⟨hoabs, howf⟩ := proof_pw_refines hfe hwf ha ho
  rw [ConLeche.isProofFast, ← hoabs]
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; simp
  | some pw =>
    rw [is_prop_refines (howf pw rfl) h, Option.map_some]

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`is_proof_fast_refines` is the top of the file: it depends on every lemma here
except `not_proof_fast_refines`, on `FindAgree`/`FindWF` from `CoreKBase.lean`, and
on the `Expr`/`Level`/`PropWhen` tiers underneath.  No `sorry`, nothing from
Aeneas's library beyond the pointer model, no `import all`. -/

/--
info: 'ConRon.Refine.PropRead.is_proof_fast_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms is_proof_fast_refines

end ConRon.Refine.PropRead
