import ConRon.Refine.TypeChecker
import ConRon.Refine.CoreKSupport
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKPinned
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.ExprOps
import ConLeche.Kernel.DeclCheck

/-! # `kernel::checker`, the value declarations (task #56)

`kernel/checker.rs` lines 92-363 — `ConLeche/Kernel/Checker.lean:26-116`:
`installBasisDecl`, `checkDefnVal`, `checkThmVal`, `checkOpaqueVal` and
`certifyNatEqs`.  The pin family (`Checker.lean:118-418`) is
`Refine/CheckerPins.lean` and the `checkDecl` dispatch and fold are
`Refine/CheckerDecl.lean`.

## Which spelling each lemma is stated against

The port has one environment spelling, the index (task #18 deviation 3), so a
lemma is stated against the **`F`-twin** where con-leche has one:

| Rust | con-leche |
|---|---|
| `install_basis_decl` | `installBasisDeclF` (`DeclCheck.lean:855-859`), = `installBasisDecl` (`Checker.lean:26-30`) |
| `check_defn_val` + `check_defn_val_after_annot` | `checkDefnValF` (`DeclCheck.lean:838-853`) |
| `check_thm_val` + `_witness` + `_checked` | `checkThmVal` (`Checker.lean:52-82`) |
| `check_opaque_val` + `_after_annot` | `checkOpaqueVal` (`Checker.lean:84-107`) |
| `certify_nat_eqs` + `_from` | `certifyNatEqs` (`Checker.lean:108-116`) |

`checkThmVal`/`checkOpaqueVal`/`certifyNatEqs` have **no** `F`-twin in
`DeclCheck.lean` (only `checkDefnValF`, `installBasisDeclF` and
`checkDivModCertsF` are spelled there), so their statements take the Lean's
`Env` argument together with the agreement `∀ n, lfe.find? n = lenv.find? n`
— which at every call site is `FEnvRel`'s own first clause, and which
`Refine/CoreKSupport.lean`'s `consts_resolve_refines` already requires for
`Expr.constsResolve`.  (`checkDefnValF` uses `Expr.constsResolveF fe` instead;
that walk is `consts_resolve_f_step` below.)  Task #58 additionally had to give
the three `Env`-reading value lemmas the hypothesis `lenv = lfe.env`: they
return an environment, and without it they are false — see the section note at
"The theorem and the opaque".

## The splits at the annotation

Task #24 point 7: a long `do` block with an annotation in the middle is split
at the annotation so the state-threading call is a tail call.  Each split pair
refines **one** cited definition, and the tail's lemma is stated at an
arbitrary post-annotation value so that head and tail compose — the shape
`Refine/CheckerSplit.lean` uses for `check_value_group`.

## `certifyNatEqs`' `Env` argument is universally quantified, on purpose

`checkDecl` hands `certifyNatEqs` the **pre-insertion** environment while the
port hands it the index restricted to the pre-insertion *bound* (task #24's
note "The pre-insertion environment is a visibility bound, not a value").
That is sound exactly because `certifyNatEqs` only ever calls `ops.isDefEq env
2 …` and every `sharedOpsC` slot ignores its `Env` argument
(`Refine/TypeChecker.lean`'s five `sharedOpsC_*` `rfl`s).  So
`certify_nat_eqs_refines` is stated at an **arbitrary** `lenv`, and that is
what discharges the deviation in `Refine/CheckerDecl.lean`'s `check_decl`
lemma.  Stating it at one particular `lenv` would hide the point.

`sorry` count in this file: 0 (task #58 closed the five task-#56 ones).
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Checker

/-! ## The two error-side shapes every arm below travels through -/

/-- `liftFueled`'s throw is the same on both sides of the `StateT`: what the
pure spelling (`Refine/CoreKVec.lean`'s `lift_fueled_err`) throws, the cached
one throws at every state. -/
private theorem checkM_throw_eq {β : Type} (le : ConLeche.CheckError) :
    (throw le : ConLeche.CheckM β) = Except.error le := rfl

private theorem lift_fueled_run_err {α : Type} {o : Option α} {what : String}
    {le : ConLeche.CheckError} {lst : ConLeche.Cached.CState}
    (h : ConLeche.liftFueled (m := ConLeche.CheckM) what o = .error le) :
    (ConLeche.liftFueled (m := ConLeche.Cached.CheckCM) what o).run lst = .error le := by
  cases o with
  | none =>
    have hle : ConLeche.CheckError.internal s!"fuel exhausted: {what}" = le := by
      simpa [ConLeche.liftFueled, checkM_throw_eq] using h
    rw [← hle, ConLeche.liftFueled]
    rfl
  | some a =>
    simp only [ConLeche.liftFueled, Pure.pure, Except.pure] at h
    exact absurd h (by simp)

/-- The port's `Err` value at a mirrored `throw` arm: `core_types::invalid` is
the `Invalid` constructor (`Refine/TypeChecker.lean` does the same
bookkeeping). -/
private theorem invalid_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v :=
  (Result.ok_injective (by rw [core_types.invalid] at h; exact h)).symm

/-- **`throw` in `CheckCM`**: the plumbing `simp` set carries no
`MonadExcept` instance, so `simp` would otherwise leave a con-leche `throw`
arm un-run.  Stated on the *applied* form. -/
private theorem checkCM_throw_apply {β : Type}
    (le : ConLeche.CheckError) (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM β) lst = .error le := rfl

attribute [local simp] checkCM_throw_apply

/-! ## The basis install -/

/-- A well-formed stored constant has a well-formed name. -/
theorem constant_info_name_wf {ci : env.ConstantInfo} {n : name.Name}
    (hci : ConstantInfoWF ci) (h : env.constant_info_name ci = ok n) : NameWF n := by
  cases ci with
  | AxiomInfo v =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h
    rw [← h]; exact hci.1
  | DefnInfo v _ _ | ThmInfo v _ | IndInfo v _ | RecInfo v _ _ _ =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h
    rw [← h]; exact hci.1.1
  | CtorInfo v _ _ =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h
    rw [← h]; exact hci.1
  | ProjInfo t =>
    -- `ConstantInfo.name` of a projection table is the reserved name
    simp only [env.constant_info_name] at h
    exact Env.proj_table_name_wf hci.1 h

/-- **`checker::install_basis_decl` refines `installBasisDeclF`**
(`ConLeche/Kernel/DeclCheck.lean:855-859`, the index twin of
`Checker.lean:26-30 installBasisDecl`): install one pinned basis declaration,
duplicate-checked, returning the pushed index.

The **unrestricted-canonical pair** rides through (task #59): the success
branch is one `fenv::push`, so `FEnv.push_canon` carries it.
`Refine/IndSpec.lean`'s header says why the checker tier needs the pair. -/
theorem install_basis_decl_refines {fe : fenv.FEnv} {ci : env.ConstantInfo}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hfw : FEnvWF fe) (hci : ConstantInfoWF ci)
    (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (h : kernel.checker.install_basis_decl fe ci = ok out) :
    ∀ lfe, FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        FEnvRel fe' (lfe.push (absConstantInfo ci)) ∧ FEnvWF fe'
          ∧ (lfe.find? (absConstantInfo ci).name).isNone
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err ce =>
        ErrSim ce (ConLeche.installBasisDeclF (m := ConLeche.CheckM) lfe
          (absConstantInfo ci)) := by
  intro lfe hfr
  rw [kernel.checker.install_basis_decl] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hnm := Env.constant_info_name_refines hn
  have hnw := constant_info_name_wf hci hn
  have hfind := find_refines hfr hfw hnw ho
  cases o with
  | some c =>
    -- `checker.rs:102` ← `Checker.lean:29` / `DeclCheck.lean:857`
    simp only [core.option.Option.is_some] at h
    simp at h
    obtain ⟨v, -, ce, hce, rfl⟩ := h
    have hfd : lfe.find? (absConstantInfo ci).name = some (absConstantInfo c) := by
      rw [← hnm, ← hfind]; rfl
    show ErrSim ce _
    rw [invalid_err hce]
    refine ErrSim.invalid
      (s := s!"duplicate declaration {(absConstantInfo ci).name}") ?_
    rw [ConLeche.installBasisDeclF]
    simp only [hfd, Option.isNone_some, Bool.false_eq_true, if_false]
    rfl
  | none =>
    -- the `if` and the `Option.is_some` are iota, which only the unifier sees
    -- through here (task #16's hard spot 1)
    have h2 : (do let f ← fenv.push fe ci
                  ok (core.result.Result.Ok f)) = ok out := h
    obtain ⟨f, hpush, h3⟩ := bind_eq_ok_iff.mp h2
    have hout : out = core.result.Result.Ok f := by simpa using h3.symm
    subst hout
    show FEnvRel f _ ∧ _
    obtain ⟨hrel', hwf'⟩ := push_refines hfr hfw hci hpush
    obtain ⟨hcan', hfull'⟩ := push_canon hfw hci hcan hfull hpush
    exact ⟨hrel', hwf', by rw [← hnm, ← hfind]; rfl, hcan', hfull'⟩

/-- The success half of `install_basis_decl_refines`, at the pre-task-#67
statement. -/
theorem install_basis_decl_refines_ok {fe fe' : fenv.FEnv} {ci : env.ConstantInfo}
    (hfw : FEnvWF fe) (hci : ConstantInfoWF ci)
    (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (h : kernel.checker.install_basis_decl fe ci = ok (.Ok fe')) :
    ∀ lfe, FEnvRel fe lfe →
      FEnvRel fe' (lfe.push (absConstantInfo ci)) ∧ FEnvWF fe'
        ∧ (lfe.find? (absConstantInfo ci).name).isNone
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  install_basis_decl_refines hfw hci hcan hfull h

/-! ## Two shapes every `do`-block lemma below travels through -/

/-- `Except.ok` at a `bind`.  `rfl`, but the default `simp` set has no lemma
for it, and every entry-point rewrite below produces one (`StateT.run_bind`
turns a `do` into an `Except` bind whose head the entry point's own equation
then makes an `Except.ok`). -/
private theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

/-- The same at the `pure` spelling, which is what a `StateT.run_pure` leaves
behind. -/
private theorem except_pure_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (pure a : Except ε α) >>= f = f a := rfl

/-! ## `Expr.constsResolveF`, one repeated step

`core_k::consts_resolve` is the port's single spelling of **both**
`Expr.constsResolve` (`Core.lean:307-332`, which `Refine/CoreKSupport.lean`
refines under an explicit `FEnv.find? = Env.find?` bridge) and
`Expr.constsResolveF` (`DeclCheck.lean:37-58`, the same clauses at the index),
which is what `checkDefnValF` reads.  The indexed reading is *not* derivable
from the `Env` one: an arbitrary index answers lookups no `Env`'s `find?` need
reproduce, so there is no `lenv` to instantiate the bridge at.  The walk is
therefore repeated here, deliberately, exactly as `Refine/CheckerPins.lean`'s
`one_level_step` repeats a step rather than importing a sibling —
`Refine/DeclCheck.lean` has the same lemma as `consts_resolve_f_refines`, and
importing it from here is not open because `Refine/CheckerDecl.lean`, which it
feeds, imports this file. -/

/-- `ConLeche/Kernel/DeclCheck.lean:37-58 Expr.constsResolveF` —
`core_k::consts_resolve` at the *indexed* reading, no `Env` in sight. -/
private theorem consts_resolve_f_step {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ c, core_k.consts_resolve fe e = ok c →
      c = ConLeche.Expr.constsResolveF lfe (absExpr e) := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.constsResolveF]
  | @sort u e hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.constsResolveF]
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨o, ho, h⟩ := h
    rw [← h, CoreK.find_isSome hfe hn ho]
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [ih c h]; simp [ConLeche.Expr.constsResolveF]
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    cases l with
    | NatVal k =>
      rw [CoreK.nat_trio_stored_refines hp hfe h]
      simp only [absExpr, absExprNode, absExprKind, absLiteral,
        ConLeche.Expr.constsResolveF]
    | StrVal sv =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b, hb, h⟩ := h
      have g1 := CoreK.nat_trio_stored_refines hp hfe hb
      simp only [absExpr, absExprNode, absExprKind, absLiteral,
        ConLeche.Expr.constsResolveF]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← g1]; simp
      | true =>
        simp only [if_true] at h
        rw [CoreK.str_support_stored_refines hp hfe h, ← g1]; simp
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (ihf b1 hb1) h (fun c' h' => iha c' h')
  | @lam ty bo m e hty hbo hm h1 iht ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (iht b1 hb1) h (fun c' h' => ihb c' h')
  | @forall_e ty bo m e hty hbo hm h1 iht ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (iht b1 hb1) h (fun c' h' => ihb c' h')
  | @let_e ty v bo e hty hv hbo h1 iht ihv ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF,
      Bool.and_assoc]
    refine CoreK.and_step (iht b1 hb1) h ?_
    intro c' h'
    obtain ⟨b2, hb2, h'⟩ := bind_eq_ok_iff.mp h'
    exact CoreK.and_step (ihv b2 hb2) h' (fun c'' h'' => ihb c'' h'')
  | @proj sn i x e hs hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (by rw [CoreK.find_isSome hfe hs ho]) h (fun c' h' => ih c' h')

/-! ## The value declarations -/

/-! ### The tail, once, with its three failure continuations abstract

`checkDefnValF`'s tail past the annotation is read twice: by
`check_defn_val_after_annot_refines` (against the cited tail, whose failure
arms are `throw`s) and by `check_defn_val_refines` (against `checkDefnValF`
itself, whose failure arms are what the `do` elaborator leaves behind — a
`throw` *bound* to a copy of the continuation).  The two differ only there, and
the argument does not look at a failure arm at all: the Rust hypothesis pins
every guard to `true`.  So the tail is proved once with the three arms
universally quantified, and each reading is one instance.  This is what makes
the split at the annotation (task #24 point 7) compose without repeating the
argument. -/

/-- The tail of `checkDefnValF` past the annotation, at arbitrary failure
continuations `k1`/`k2`/`k3`: the level-parameter and resolution guards, the
value's inferred type against the declared one, and the push. -/
private theorem defn_after_annot_core {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value_a : expr.Expr} {hint : env.ReducibilityHint}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value_a)
    (h : kernel.checker.check_defn_val_after_annot mode st fe cv value_a hint
        = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst',
          StateRel st' lst' ∧ StateWF st' ∧ FEnvWF fe'
          ∧ FEnvRel fe' (lfe.push (.defnInfo (absConstantVal cv) (absExpr value_a)
              (absHint hint)))
          ∧ ∀ k1 k2 k3 : ConLeche.Cached.CheckCM ConLeche.FEnv,
            (if (absExpr value_a).allLevelParamsDefined (absConstantVal cv).levelParams = true then
            (if (absExpr value_a).constsResolveF lfe = true then
              (do
                let vtype ← (TypeChecker.lops mode lfe).inferType lfe.env 0 (absExpr value_a)
                let okv ← (TypeChecker.lops mode lfe).isDefEq lfe.env 0 vtype
                  (absConstantVal cv).type
                if okv = true then
                  pure (lfe.push (.defnInfo (absConstantVal cv) (absExpr value_a)
                    (absHint hint)))
                else k3)
            else k2)
          else k1).run lst
              = .ok (lfe.push (.defnInfo (absConstantVal cv) (absExpr value_a)
                  (absHint hint)), lst')
      | .Err ce =>
        ∀ k1 k2 k3 : ConLeche.Cached.CheckCM ConLeche.FEnv,
          (∀ l, ∃ s, k1.run l = .error (.invalid s)) →
          (∀ l, ∃ s, k2.run l = .error (.invalid s)) →
          (∀ l, ∃ s, k3.run l = .error (.invalid s)) →
          ErrSim ce ((if (absExpr value_a).allLevelParamsDefined (absConstantVal cv).levelParams = true then
            (if (absExpr value_a).constsResolveF lfe = true then
              (do
                let vtype ← (TypeChecker.lops mode lfe).inferType lfe.env 0 (absExpr value_a)
                let okv ← (TypeChecker.lops mode lfe).isDefEq lfe.env 0 vtype
                  (absConstantVal cv).type
                if okv = true then
                  pure (lfe.push (.defnInfo (absConstantVal cv) (absExpr value_a)
                    (absHint hint)))
                else k3)
            else k2)
          else k1).run lst) := by
  intro lst lfe hsr hfr
  rw [kernel.checker.check_defn_val_after_annot] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = (absExpr value_a).allLevelParamsDefined (absConstantVal cv).levelParams :=
    ExprOps.all_level_params_defined_fast_refines hcv.2.1 hv hb
  cases b with
  | false =>
    -- `checker.rs:146` ← `Checker.lean:44` / `DeclCheck.lean:846`
    simp at h
    obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
    intro k1 k2 k3 hk1 hk2 hk3
    rw [invalid_err hce, if_neg (by rw [← hbv]; simp)]
    obtain ⟨s, hs⟩ := hk1 lst
    exact ErrSim.invalid hs
  | true =>
    simp only [if_true] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = (absExpr value_a).constsResolveF lfe :=
      consts_resolve_f_step hp (FindAgree.of_rel hfr hfw) hv b1 hb1
    cases b1 with
    | false =>
      -- `checker.rs:148` ← `Checker.lean:46`
      simp at h
      obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
      intro k1 k2 k3 hk1 hk2 hk3
      rw [invalid_err hce, if_pos hbv.symm, if_neg (by rw [← hb1v]; simp)]
      obtain ⟨s, hs⟩ := hk2 lst
      exact ErrSim.invalid hs
    | true =>
      simp only [if_true] at h
      obtain ⟨p, hinf, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err e =>
        -- the inference threw; con-leche's `do` fails at the same step
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        intro k1 k2 k3 hk1 hk2 hk3
        rw [if_pos hbv.symm, if_pos hb1v.symm]
        exact ErrSim.bindCM
          ((TypeChecker.infer_type_core_refines hfuel hk).err st fe 0#u64 value_a e st1
            hsw hfw hv hinf lst lfe hsr hfr)
      | Ok vtype =>
        obtain ⟨lst1, hrun1, hsr1, hsw1, hvw⟩ :=
          (TypeChecker.infer_type_core_refines hfuel hk).ok st fe 0#u64 value_a vtype st1
            hsw hfw hv hinf lst lfe hsr hfr
        have hr1 : (ConLeche.Cached.opE (absMode mode) lfe (·.infer) 0
            (absExpr value_a)).run lst = .ok (absExpr vtype, lst1) := hrun1
        obtain ⟨q, hdef, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r1, st2⟩ := q
        cases r1 with
        | Err e =>
          -- the conversion threw
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          intro k1 k2 k3 hk1 hk2 hk3
          rw [if_pos hbv.symm, if_pos hb1v.symm]
          refine ErrSim.of_eq (x := ((TypeChecker.lops mode lfe).isDefEq lfe.env 0
            (absExpr vtype) (absConstantVal cv).type >>= fun okv =>
              if okv = true then
                pure (lfe.push (.defnInfo (absConstantVal cv) (absExpr value_a)
                  (absHint hint)))
              else k3).run lst1) (ErrSim.bindCM
                ((TypeChecker.is_def_eq_core_refines hfuel hk).err st1 fe 0#u64 vtype cv.ty
                  e st2 hsw1 hfw hvw hcv.2.2 hdef lst1 lfe hsr1 hfr)) ?_
          simp only [StateT.run_bind, TypeChecker.sharedOpsC_inferType, hr1,
            except_ok_bind]
        | Ok okv =>
          obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
            (TypeChecker.is_def_eq_core_refines hfuel hk).ok st1 fe 0#u64 vtype cv.ty okv st2
              hsw1 hfw hvw hcv.2.2 hdef lst1 lfe hsr1 hfr
          have hr2 : (ConLeche.Cached.opB (absMode mode) lfe 0 (absExpr vtype)
              (absConstantVal cv).type).run lst1 = .ok (okv, lst2) := hrun2
          cases okv with
          | false =>
            -- `checker.rs:165` ← `Checker.lean:49`
            simp at h
            obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
            intro k1 k2 k3 hk1 hk2 hk3
            rw [invalid_err hce, if_pos hbv.symm, if_pos hb1v.symm]
            obtain ⟨s, hs⟩ := hk3 lst2
            refine ErrSim.invalid (s := s) ?_
            simp only [StateT.run_bind, TypeChecker.sharedOpsC_inferType,
              TypeChecker.sharedOpsC_isDefEq, except_ok_bind, hr1, hr2,
              Bool.false_eq_true, if_false]
            exact hs
          | true =>
            obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨rh, hrh, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
            rw [Env.constant_val_dup_refines hcv1] at hpush
            rw [Env.reducibility_hint_dup_refines hrh] at hpush
            obtain ⟨rfl, rfl⟩ : core.result.Result.Ok f = out ∧ st2 = st' := by
              simpa using h
            obtain ⟨hrel', hwf'⟩ :=
              push_refines hfr hfw (show ConstantInfoWF (.DefnInfo cv value_a hint) from
                ⟨hcv, hv⟩) hpush
            refine ⟨lst2, hsr2, hsw2, hwf', hrel', ?_⟩
            intro k1 k2 k3
            rw [if_pos hbv.symm, if_pos hb1v.symm]
            simp only [StateT.run_bind, TypeChecker.sharedOpsC_inferType,
              TypeChecker.sharedOpsC_isDefEq, except_ok_bind, hr1, hr2]
            rfl

/-- **`checker::check_defn_val` refines `checkDefnValF`**
(`ConLeche/Kernel/DeclCheck.lean:838-853`): the two scope guards and the
annotation of the value; the tail is `check_defn_val_after_annot_refines`
(shared through `defn_after_annot_core`, below). -/
theorem check_defn_val_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr} {hint : env.ReducibilityHint}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_defn_val mode st fe cv value hint = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.checkDefnValF (TypeChecker.lops mode lfe) lfe (absConstantVal cv)
              (absExpr value) (absHint hint)).run lst = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
      | .Err ce =>
        ErrSim ce ((ConLeche.checkDefnValF (TypeChecker.lops mode lfe) lfe
          (absConstantVal cv) (absExpr value) (absHint hint)).run lst) := by
  intro lst lfe hsr hfr
  rw [kernel.checker.check_defn_val] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = (absExpr value).looseBVarsBounded 0 :=
    ExprOps.loose_bvars_bounded_refines hv hb
  cases b with
  | false =>
    -- `checker.rs:122` ← `Checker.lean:39` / `DeclCheck.lean:841`
    simp at h
    obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
    show ErrSim ce _
    rw [invalid_err hce, ConLeche.checkDefnValF, if_neg (by rw [← hbv]; simp)]
    exact ErrSim.invalid
      (s := s!"loose bound variable in value of {(absConstantVal cv).name}") rfl
  | true =>
    simp only [if_true] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = (absExpr value).hasFvar := ExprOps.has_fvar_refines hv hb1
    cases b1 with
    | true =>
      -- `checker.rs:124` ← `Checker.lean:41` / `DeclCheck.lean:843`
      simp at h
      obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
      show ErrSim ce _
      rw [invalid_err hce, ConLeche.checkDefnValF, if_pos hbv.symm,
        if_pos (by rw [← hb1v])]
      exact ErrSim.invalid
        (s := s!"unexpected free variable in value of {(absConstantVal cv).name}") rfl
    | false =>
      obtain ⟨p, hann, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err e =>
        -- the annotation threw
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        show ErrSim e _
        rw [ConLeche.checkDefnValF, if_pos hbv.symm, if_neg (by rw [← hb1v]; simp)]
        exact ErrSim.bindCM
          ((TypeChecker.annotate_core_refines hfuel hk).err st fe 0#u64 value e st1
            hsw hfw hv hann lst lfe hsr hfr)
      | Ok value_a =>
        obtain ⟨lst1, hruna, hsr1, hsw1, hvaw⟩ :=
          (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 value value_a st1
            hsw hfw hv hann lst lfe hsr hfr
        have hcore :=
          defn_after_annot_core hfuel hk hp hsw1 hfw hcv hvaw h lst1 lfe hsr1 hfr
        have hra : (ConLeche.Cached.opE (absMode mode) lfe (·.annotate) 0
            (absExpr value)).run lst = .ok (absExpr value_a, lst1) := hruna
        cases out with
        | Ok fe' =>
          obtain ⟨lst', hsr', hsw', hwf', hrel', hrun⟩ := hcore
          refine ⟨lst', _, ?_, hsr', hsw', hrel', hwf'⟩
          rw [ConLeche.checkDefnValF, if_pos hbv.symm, if_neg (by rw [← hb1v]; simp)]
          simp only [StateT.run_bind, TypeChecker.sharedOpsC_annotate, hra,
            except_ok_bind]
          exact hrun _ _ _
        | Err ce =>
          show ErrSim ce _
          rw [ConLeche.checkDefnValF, if_pos hbv.symm, if_neg (by rw [← hb1v]; simp)]
          simp only [StateT.run_bind, TypeChecker.sharedOpsC_annotate, hra,
            except_ok_bind]
          exact hcore _ _ _ (fun _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩)

/-- The success half of `check_defn_val_refines`, at the pre-task-#67
statement. -/
theorem check_defn_val_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr} {hint : env.ReducibilityHint}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_defn_val mode st fe cv value hint = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.checkDefnValF (TypeChecker.lops mode lfe) lfe (absConstantVal cv)
            (absExpr value) (absHint hint)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' :=
  check_defn_val_refines hfuel hk hp hsw hfw hcv hv h

/-- **The tail of `checkDefnValF` past the annotation**: the level-parameter
and resolution guards, the value's inferred type against the declared one, and
the push.  Stated at an arbitrary annotated `value_a`, which is what makes the
split compose.  `defn_after_annot_core` at the cited `throw`s. -/
theorem check_defn_val_after_annot_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value_a : expr.Expr} {hint : env.ReducibilityHint}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value_a)
    (h : kernel.checker.check_defn_val_after_annot mode st fe cv value_a hint
        = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (do
          let lv := absExpr value_a
          if ¬ lv.allLevelParamsDefined (absConstantVal cv).levelParams then
            throw (ConLeche.CheckError.invalid "undeclared universe parameter")
          else if ¬ lv.constsResolveF lfe then
            throw (ConLeche.CheckError.invalid "unknown constant")
          else do
            let vtype ← (TypeChecker.lops mode lfe).inferType lfe.env 0 lv
            let okv ← (TypeChecker.lops mode lfe).isDefEq lfe.env 0 vtype
              (absConstantVal cv).type
            if okv then
              pure (lfe.push (.defnInfo (absConstantVal cv) lv (absHint hint)))
            else throw (ConLeche.CheckError.invalid "type mismatch")).run lst
            = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
      | .Err ce =>
        ErrSim ce ((do
          let lv := absExpr value_a
          if ¬ lv.allLevelParamsDefined (absConstantVal cv).levelParams then
            throw (ConLeche.CheckError.invalid "undeclared universe parameter")
          else if ¬ lv.constsResolveF lfe then
            throw (ConLeche.CheckError.invalid "unknown constant")
          else do
            let vtype ← (TypeChecker.lops mode lfe).inferType lfe.env 0 lv
            let okv ← (TypeChecker.lops mode lfe).isDefEq lfe.env 0 vtype
              (absConstantVal cv).type
            if okv then
              pure (lfe.push (.defnInfo (absConstantVal cv) lv (absHint hint)))
            else throw (ConLeche.CheckError.invalid "type mismatch")).run lst) := by
  intro lst lfe hsr hfr
  have hcore := defn_after_annot_core hfuel hk hp hsw hfw hcv hv h lst lfe hsr hfr
  cases out with
  | Ok fe' =>
    obtain ⟨lst', hsr', hsw', hwf', hrel', hrun⟩ := hcore
    exact ⟨lst', _, by
      simpa only [ite_not] using hrun
        (throw (ConLeche.CheckError.invalid "undeclared universe parameter"))
        (throw (ConLeche.CheckError.invalid "unknown constant"))
        (throw (ConLeche.CheckError.invalid "type mismatch")),
      hsr', hsw', hrel', hwf'⟩
  | Err ce =>
    exact by
      simpa only [ite_not] using hcore
        (throw (ConLeche.CheckError.invalid "undeclared universe parameter"))
        (throw (ConLeche.CheckError.invalid "unknown constant"))
        (throw (ConLeche.CheckError.invalid "type mismatch"))
        (fun _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩)

/-- The success half of `check_defn_val_after_annot_refines`, at the
pre-task-#67 statement. -/
theorem check_defn_val_after_annot_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value_a : expr.Expr} {hint : env.ReducibilityHint}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value_a)
    (h : kernel.checker.check_defn_val_after_annot mode st fe cv value_a hint
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (do
          let lv := absExpr value_a
          if ¬ lv.allLevelParamsDefined (absConstantVal cv).levelParams then
            throw (ConLeche.CheckError.invalid "undeclared universe parameter")
          else if ¬ lv.constsResolveF lfe then
            throw (ConLeche.CheckError.invalid "unknown constant")
          else do
            let vtype ← (TypeChecker.lops mode lfe).inferType lfe.env 0 lv
            let okv ← (TypeChecker.lops mode lfe).isDefEq lfe.env 0 vtype
              (absConstantVal cv).type
            if okv then
              pure (lfe.push (.defnInfo (absConstantVal cv) lv (absHint hint)))
            else throw (ConLeche.CheckError.invalid "type mismatch")).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' :=
  check_defn_val_after_annot_refines hfuel hk hp hsw hfw hcv hv h

/-! ## The theorem and the opaque

### Why these three take `lenv = lfe.env` (task #58)

`checkThmVal`/`checkOpaqueVal` have no `F`-twin, so — the module note above —
their statements read an `Env`.  Their *result* is an `Env` too, `⟨ci ::
lenv.consts⟩`, and the conclusion asks for it to be `lfe'.env` for an `lfe'`
with `FEnvRel fe' lfe'`.  `FEnvRel`'s first clause is an equation, `absEnv
fe'.env = lfe'.env`, and the port's `fe'` is `fenv::push fe ci`, so `lfe'.env`
is forced to be `⟨absConstantInfo ci :: (absEnv fe.env).consts⟩` — that is,
`⟨… :: lfe.env.consts⟩`.  The three statements are therefore **false** at an
`lenv` whose constants are not `lfe`'s, and each gains the hypothesis `lenv =
lfe.env`.  Nothing else changes: `lenv = lfe.env` is exactly what the module
note already says every call site passes, and the find-agreement hypothesis
`∀ n, lfe.find? n = lenv.find? n` (which the index does *not* imply, and which
`Expr.constsResolve` needs) stays as it was.

`certifyNatEqs`' `Env` argument is *not* affected and stays universally
quantified: it returns a `Bool`, not an environment.

### The checked half, with its failure continuations abstract

Same device as `defn_after_annot_core`: `check_thm_val_checked`'s reading is
needed twice, inside `checkThmVal` and inside the witness half's statement, and
the two differ only in the failure arms the `do` elaborator leaves behind. -/

/-- `checker::check_thm_val_checked` against `checkThmVal`'s post-annotation
tail, at arbitrary failure continuations.  **A theorem is stored by its
statement**: the pushed record keeps the *raw* `value`, not the annotated
`jv` that was checked. -/
private theorem thm_checked_core {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value jv : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (hjv : ExprWF jv)
    (h : kernel.checker.check_thm_val_checked mode st fe cv value jv
        = ok (out, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) → lenv = lfe.env →
      match out with
      | .Ok fe' =>
        ∃ lst',
          StateRel st' lst' ∧ StateWF st' ∧ FEnvWF fe'
          ∧ FEnvRel fe' (lfe.push (.thmInfo (absConstantVal cv) (absExpr value)))
          ∧ ∀ k1 k2 k3 : ConLeche.Cached.CheckCM ConLeche.Env,
            (if (absExpr jv).allLevelParamsDefined (absConstantVal cv).levelParams = true then
            (if (absExpr jv).constsResolve lenv = true then
              (do
                let vtype ← (TypeChecker.lops mode lfe).inferType lenv 0 (absExpr jv)
                let okv ← (TypeChecker.lops mode lfe).isDefEq lenv 0 vtype
                  (absConstantVal cv).type
                if okv = true then
                  pure (⟨ConLeche.ConstantInfo.thmInfo (absConstantVal cv) (absExpr value)
                    :: lenv.consts⟩ : ConLeche.Env)
                else k3)
            else k2)
          else k1).run lst
              = .ok ((lfe.push (.thmInfo (absConstantVal cv) (absExpr value))).env, lst')
      | .Err ce =>
        ∀ k1 k2 k3 : ConLeche.Cached.CheckCM ConLeche.Env,
          (∀ l, ∃ s, k1.run l = .error (.invalid s)) →
          (∀ l, ∃ s, k2.run l = .error (.invalid s)) →
          (∀ l, ∃ s, k3.run l = .error (.invalid s)) →
          ErrSim ce ((if (absExpr jv).allLevelParamsDefined (absConstantVal cv).levelParams = true then
            (if (absExpr jv).constsResolve lenv = true then
              (do
                let vtype ← (TypeChecker.lops mode lfe).inferType lenv 0 (absExpr jv)
                let okv ← (TypeChecker.lops mode lfe).isDefEq lenv 0 vtype
                  (absConstantVal cv).type
                if okv = true then
                  pure (⟨ConLeche.ConstantInfo.thmInfo (absConstantVal cv) (absExpr value)
                    :: lenv.consts⟩ : ConLeche.Env)
                else k3)
            else k2)
          else k1).run lst) := by
  intro lst lfe lenv hsr hfr henv hlenv
  subst hlenv
  rw [kernel.checker.check_thm_val_checked] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = (absExpr jv).allLevelParamsDefined (absConstantVal cv).levelParams :=
    ExprOps.all_level_params_defined_fast_refines hcv.2.1 hjv hb
  cases b with
  | false =>
    -- `checker.rs:240` ← `Checker.lean:76`
    simp at h
    obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
    intro k1 k2 k3 hk1 hk2 hk3
    rw [invalid_err hce, if_neg (by rw [← hbv]; simp)]
    obtain ⟨s, hs⟩ := hk1 lst
    exact ErrSim.invalid hs
  | true =>
    simp only [if_true] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = (absExpr jv).constsResolve lfe.env :=
      CoreK.consts_resolve_refines hp (FindAgree.of_rel hfr hfw) henv hjv b1 hb1
    cases b1 with
    | false =>
      -- `checker.rs:242` ← `Checker.lean:78`
      simp at h
      obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
      intro k1 k2 k3 hk1 hk2 hk3
      rw [invalid_err hce, if_pos hbv.symm, if_neg (by rw [← hb1v]; simp)]
      obtain ⟨s, hs⟩ := hk2 lst
      exact ErrSim.invalid hs
    | true =>
      simp only [if_true] at h
      obtain ⟨p, hinf, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err e =>
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        intro k1 k2 k3 hk1 hk2 hk3
        rw [if_pos hbv.symm, if_pos hb1v.symm]
        exact ErrSim.bindCM
          ((TypeChecker.infer_type_core_refines hfuel hk).err st fe 0#u64 jv e st1
            hsw hfw hjv hinf lst lfe hsr hfr)
      | Ok vtype =>
        obtain ⟨lst1, hrun1, hsr1, hsw1, hvw⟩ :=
          (TypeChecker.infer_type_core_refines hfuel hk).ok st fe 0#u64 jv vtype st1
            hsw hfw hjv hinf lst lfe hsr hfr
        have hr1 : (ConLeche.Cached.opE (absMode mode) lfe (·.infer) 0
            (absExpr jv)).run lst = .ok (absExpr vtype, lst1) := hrun1
        obtain ⟨q, hdef, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r1, st2⟩ := q
        cases r1 with
        | Err e =>
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          intro k1 k2 k3 hk1 hk2 hk3
          rw [if_pos hbv.symm, if_pos hb1v.symm]
          refine ErrSim.of_eq (x := ((TypeChecker.lops mode lfe).isDefEq lfe.env 0
            (absExpr vtype) (absConstantVal cv).type >>= fun okv =>
              if okv = true then
                pure (⟨ConLeche.ConstantInfo.thmInfo (absConstantVal cv) (absExpr value)
                  :: lfe.env.consts⟩ : ConLeche.Env)
              else k3).run lst1) (ErrSim.bindCM
                ((TypeChecker.is_def_eq_core_refines hfuel hk).err st1 fe 0#u64 vtype cv.ty
                  e st2 hsw1 hfw hvw hcv.2.2 hdef lst1 lfe hsr1 hfr)) ?_
          simp only [StateT.run_bind, TypeChecker.sharedOpsC_inferType, hr1,
            except_ok_bind]
        | Ok okv =>
          obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
            (TypeChecker.is_def_eq_core_refines hfuel hk).ok st1 fe 0#u64 vtype cv.ty okv st2
              hsw1 hfw hvw hcv.2.2 hdef lst1 lfe hsr1 hfr
          have hr2 : (ConLeche.Cached.opB (absMode mode) lfe 0 (absExpr vtype)
              (absConstantVal cv).type).run lst1 = .ok (okv, lst2) := hrun2
          cases okv with
          | false =>
            -- `checker.rs:258` ← `Checker.lean:81`
            simp at h
            obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
            intro k1 k2 k3 hk1 hk2 hk3
            rw [invalid_err hce, if_pos hbv.symm, if_pos hb1v.symm]
            obtain ⟨s, hs⟩ := hk3 lst2
            refine ErrSim.invalid (s := s) ?_
            simp only [StateT.run_bind, TypeChecker.sharedOpsC_inferType,
              TypeChecker.sharedOpsC_isDefEq, except_ok_bind, hr1, hr2,
              Bool.false_eq_true, if_false]
            exact hs
          | true =>
            obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
            rw [Env.constant_val_dup_refines hcv1, Expr.dup_eq he1] at hpush
            obtain ⟨rfl, rfl⟩ : core.result.Result.Ok f = out ∧ st2 = st' := by
              simpa using h
            obtain ⟨hrel', hwf'⟩ :=
              push_refines hfr hfw (show ConstantInfoWF (.ThmInfo cv value) from
                ⟨hcv, hv⟩) hpush
            refine ⟨lst2, hsr2, hsw2, hwf', hrel', ?_⟩
            intro k1 k2 k3
            rw [if_pos hbv.symm, if_pos hb1v.symm]
            simp only [StateT.run_bind, TypeChecker.sharedOpsC_inferType,
              TypeChecker.sharedOpsC_isDefEq, except_ok_bind, hr1, hr2]
            rfl

/-- `checker::check_thm_val_witness` against `checkThmVal`'s post-gate tail, at
arbitrary failure continuations: the value's two scope guards, its annotation,
and `thm_checked_core`. -/
private theorem thm_witness_core {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_thm_val_witness mode st fe cv value = ok (out, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) → lenv = lfe.env →
      match out with
      | .Ok fe' =>
        ∃ lst',
          StateRel st' lst' ∧ StateWF st' ∧ FEnvWF fe'
          ∧ FEnvRel fe' (lfe.push (.thmInfo (absConstantVal cv) (absExpr value)))
          ∧ ∀ (k1 k2 : ConLeche.Cached.CheckCM ConLeche.Env)
              (k3 k4 k5 : ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Env),
            (if (absExpr value).looseBVarsBounded 0 = true then
            (if (absExpr value).hasFvar = true then k2
            else do
              let jv ← (TypeChecker.lops mode lfe).annotate lenv 0 (absExpr value)
              if jv.allLevelParamsDefined (absConstantVal cv).levelParams = true then
                (if jv.constsResolve lenv = true then
                  (do
                    let vtype ← (TypeChecker.lops mode lfe).inferType lenv 0 jv
                    let okv ← (TypeChecker.lops mode lfe).isDefEq lenv 0 vtype
                      (absConstantVal cv).type
                    if okv = true then
                      pure (⟨ConLeche.ConstantInfo.thmInfo (absConstantVal cv)
                        (absExpr value) :: lenv.consts⟩ : ConLeche.Env)
                    else k5 jv)
                else k4 jv)
              else k3 jv)
          else k1).run lst
              = .ok ((lfe.push (.thmInfo (absConstantVal cv) (absExpr value))).env, lst')
      | .Err ce =>
        ∀ (k1 k2 : ConLeche.Cached.CheckCM ConLeche.Env)
            (k3 k4 k5 : ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Env),
          (∀ l, ∃ s, k1.run l = .error (.invalid s)) →
          (∀ l, ∃ s, k2.run l = .error (.invalid s)) →
          (∀ e l, ∃ s, (k3 e).run l = .error (.invalid s)) →
          (∀ e l, ∃ s, (k4 e).run l = .error (.invalid s)) →
          (∀ e l, ∃ s, (k5 e).run l = .error (.invalid s)) →
          ErrSim ce ((if (absExpr value).looseBVarsBounded 0 = true then
            (if (absExpr value).hasFvar = true then k2
            else do
              let jv ← (TypeChecker.lops mode lfe).annotate lenv 0 (absExpr value)
              if jv.allLevelParamsDefined (absConstantVal cv).levelParams = true then
                (if jv.constsResolve lenv = true then
                  (do
                    let vtype ← (TypeChecker.lops mode lfe).inferType lenv 0 jv
                    let okv ← (TypeChecker.lops mode lfe).isDefEq lenv 0 vtype
                      (absConstantVal cv).type
                    if okv = true then
                      pure (⟨ConLeche.ConstantInfo.thmInfo (absConstantVal cv)
                        (absExpr value) :: lenv.consts⟩ : ConLeche.Env)
                    else k5 jv)
                else k4 jv)
              else k3 jv)
          else k1).run lst) := by
  intro lst lfe lenv hsr hfr henv hlenv
  subst hlenv
  rw [kernel.checker.check_thm_val_witness] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = (absExpr value).looseBVarsBounded 0 :=
    ExprOps.loose_bvars_bounded_refines hv hb
  cases b with
  | false =>
    -- `checker.rs:216` ← `Checker.lean:71`
    simp at h
    obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
    intro k1 k2 k3 k4 k5 hk1 hk2 hk3 hk4 hk5
    rw [invalid_err hce, if_neg (by rw [← hbv]; simp)]
    obtain ⟨s, hs⟩ := hk1 lst
    exact ErrSim.invalid hs
  | true =>
    simp only [if_true] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = (absExpr value).hasFvar := ExprOps.has_fvar_refines hv hb1
    cases b1 with
    | true =>
      -- `checker.rs:218` ← `Checker.lean:73`
      simp at h
      obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
      intro k1 k2 k3 k4 k5 hk1 hk2 hk3 hk4 hk5
      rw [invalid_err hce, if_pos hbv.symm, if_pos (by rw [← hb1v])]
      obtain ⟨s, hs⟩ := hk2 lst
      exact ErrSim.invalid hs
    | false =>
      obtain ⟨p, hann, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err e =>
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        intro k1 k2 k3 k4 k5 hk1 hk2 hk3 hk4 hk5
        rw [if_pos hbv.symm, if_neg (by rw [← hb1v]; simp)]
        exact ErrSim.bindCM
          ((TypeChecker.annotate_core_refines hfuel hk).err st fe 0#u64 value e st1
            hsw hfw hv hann lst lfe hsr hfr)
      | Ok jv =>
        obtain ⟨lst1, hruna, hsr1, hsw1, hjvw⟩ :=
          (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 value jv st1
            hsw hfw hv hann lst lfe hsr hfr
        have hcore :=
          thm_checked_core hfuel hk hp hsw1 hfw hcv hv hjvw h lst1 lfe lfe.env hsr1 hfr
            henv rfl
        have hra : (ConLeche.Cached.opE (absMode mode) lfe (·.annotate) 0
            (absExpr value)).run lst = .ok (absExpr jv, lst1) := hruna
        cases out with
        | Ok fe' =>
          obtain ⟨lst', hsr', hsw', hwf', hrel', hrun⟩ := hcore
          refine ⟨lst', hsr', hsw', hwf', hrel', ?_⟩
          intro k1 k2 k3 k4 k5
          rw [if_pos hbv.symm, if_neg (by rw [← hb1v]; simp)]
          simp only [StateT.run_bind, TypeChecker.sharedOpsC_annotate, hra,
            except_ok_bind]
          exact hrun _ _ _
        | Err ce =>
          intro k1 k2 k3 k4 k5 hk1 hk2 hk3 hk4 hk5
          rw [if_pos hbv.symm, if_neg (by rw [← hb1v]; simp)]
          simp only [StateT.run_bind, TypeChecker.sharedOpsC_annotate, hra,
            except_ok_bind]
          exact hcore _ _ _ (hk3 (absExpr jv)) (hk4 (absExpr jv)) (hk5 (absExpr jv))

/-- **`checker::check_thm_val` refines `checkThmVal`**
(`ConLeche/Kernel/Checker.lean:52-82`): the statement's sort and the
is-a-proposition gate; the witness half is
`check_thm_val_witness_refines`.  **A theorem is stored by its statement** —
the constant keeps the record's own raw value as an unread datum and the
annotated value is a realizability witness, checked and discarded.

`hlenv` is task #58's added hypothesis; see the section note. -/
theorem check_thm_val_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_thm_val mode st fe cv value = ok (out, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) → lenv = lfe.env →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.checkThmVal (TypeChecker.lops mode lfe) lenv (absConstantVal cv)
              (absExpr value)).run lst = .ok (lfe'.env, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
      | .Err ce =>
        ErrSim ce ((ConLeche.checkThmVal (TypeChecker.lops mode lfe) lenv
          (absConstantVal cv) (absExpr value)).run lst) := by
  intro lst lfe lenv hsr hfr henv hlenv
  subst hlenv
  rw [kernel.checker.check_thm_val] at h
  obtain ⟨p, hinf, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := p
  cases r with
  | Err e =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    show ErrSim e _
    rw [ConLeche.checkThmVal]
    exact ErrSim.bindCM
      ((TypeChecker.infer_type_core_refines hfuel hk).err st fe 0#u64 cv.ty e st1
        hsw hfw hcv.2.2 hinf lst lfe hsr hfr)
  | Ok stype =>
    obtain ⟨lst1, hrun1, hsr1, hsw1, hstw⟩ :=
      (TypeChecker.infer_type_core_refines hfuel hk).ok st fe 0#u64 cv.ty stype st1
        hsw hfw hcv.2.2 hinf lst lfe hsr hfr
    have hr1 : (ConLeche.Cached.opE (absMode mode) lfe (·.infer) 0
        (absConstantVal cv).type).run lst = .ok (absExpr stype, lst1) := hrun1
    obtain ⟨q, hsort, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st2⟩ := q
    cases r1 with
    | Err e =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      show ErrSim e _
      rw [ConLeche.checkThmVal]
      simp only [StateT.run_bind]
      rw [TypeChecker.sharedOpsC_inferType, hr1]
      simp only [except_ok_bind]
      exact ErrSim.bind
        ((TypeChecker.ensure_sort_core_refines hfuel hk).err st1 fe 0#u64 stype e st2
          hsw1 hfw hstw hsort lst1 lfe hsr1 hfr) _
    | Ok u =>
      obtain ⟨lst2, hrun2, hsr2, hsw2, huw⟩ :=
        (TypeChecker.ensure_sort_core_refines hfuel hk).ok st1 fe 0#u64 stype u st2
          hsw1 hfw hstw hsort lst1 lfe hsr1 hfr
      have hr2 : (ConLeche.Cached.opS (absMode mode) lfe 0
          (absExpr stype)).run lst1 = .ok (absLevel u, lst2) := hrun2
      obtain ⟨l, hl0, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, hiso, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r2, hlf, h⟩ := bind_eq_ok_iff.mp h
      have hequiv : ConLeche.Level.isEquiv (absLevel u) ConLeche.Level.zero = o := by
        rw [← Level.zero_refines hl0]
        exact Level.is_equiv_refines huw (Level.zero_wf hl0) hiso
      -- the head of the cited `do`, down to the level comparison: the two entry
      -- points are rewritten by hand, not by `simp only`, because the witness
      -- block still ahead has an `inferType` of its own
      have hhead : ∀ (γ : Type) (f : Bool → ConLeche.Cached.CheckCM γ),
          (do
            let stype ← (TypeChecker.lops mode lfe).inferType lfe.env 0
              (absConstantVal cv).type
            let u ← (TypeChecker.lops mode lfe).ensureSort lfe.env 0 stype
            let b ← ConLeche.liftFueled (m := ConLeche.Cached.CheckCM) "level comparison"
              (ConLeche.Level.isEquiv u ConLeche.Level.zero)
            f b).run lst
          = (ConLeche.liftFueled (m := ConLeche.Cached.CheckCM) "level comparison" o
              >>= f).run lst2 := by
        intro γ f
        simp only [StateT.run_bind]
        rw [TypeChecker.sharedOpsC_inferType, hr1]
        simp only [except_ok_bind]
        rw [TypeChecker.sharedOpsC_ensureSort, hr2]
        simp only [except_ok_bind, hequiv, StateT.run_bind]
      cases r2 with
      | Err e =>
        -- `core_k::lift_fueled`'s own mirrored `internal` (`Core.lean:111`)
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        show ErrSim e _
        rw [ConLeche.checkThmVal, hhead]
        exact ErrSim.bindCM (ErrSim.trans (CoreK.lift_fueled_err hlf)
          (fun le hle => lift_fueled_run_err hle))
      | Ok is_prop =>
        -- `lift_fueled` succeeded, so the level comparison did not run out of fuel
        have hsome : o = some is_prop := by
          have hlift := CoreK.lift_fueled_refines hlf
          cases o with
          | none => simp [ConLeche.liftFueled] at hlift
          | some a =>
            have h2 : (Except.ok a : ConLeche.CheckM Bool) = Except.ok is_prop := hlift
            have ha : a = is_prop := by simpa using h2
            rw [ha]
        cases is_prop with
        | false =>
          -- the port's `checker.rs:197` is the cited `Checker.lean:69`
          simp at h
          obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
          show ErrSim ce _
          rw [invalid_err hce, ConLeche.checkThmVal, hhead, hsome]
          refine ErrSim.invalid
            (s := s!"type of theorem {(absConstantVal cv).name} is not a proposition") ?_
          rfl
        | true =>
          have hcore :=
            thm_witness_core hfuel hk hp hsw2 hfw hcv hv h lst2 lfe lfe.env hsr2 hfr
              henv rfl
          cases out with
          | Ok fe' =>
            obtain ⟨lst', hsr', hsw', hwf', hrel', hrun⟩ := hcore
            refine ⟨lst', _, ?_, hsr', hsw', hrel', hwf'⟩
            rw [ConLeche.checkThmVal, hhead, hsome]
            simp only [StateT.run_bind]
            rw [show (ConLeche.liftFueled (m := ConLeche.Cached.CheckCM)
              "level comparison" (some true)).run lst2 = Except.ok (true, lst2) from rfl]
            simp only [except_ok_bind]
            rw [if_pos trivial]
            exact hrun _ _ _ _ _
          | Err ce =>
            show ErrSim ce _
            rw [ConLeche.checkThmVal, hhead, hsome]
            simp only [StateT.run_bind]
            rw [show (ConLeche.liftFueled (m := ConLeche.Cached.CheckCM)
              "level comparison" (some true)).run lst2 = Except.ok (true, lst2) from rfl]
            simp only [except_ok_bind]
            rw [if_pos trivial]
            exact hcore _ _ _ _ _ (fun _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩)
              (fun _ _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩)

/-- The success half of `check_thm_val_refines`, at the pre-task-#67
statement. -/
theorem check_thm_val_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_thm_val mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) → lenv = lfe.env →
      ∃ lst' lfe',
        (ConLeche.checkThmVal (TypeChecker.lops mode lfe) lenv (absConstantVal cv)
            (absExpr value)).run lst = .ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' :=
  check_thm_val_refines hfuel hk hp hsw hfw hcv hv h

/-- **The witness half of `checkThmVal`**: the value's syntactic guards and its
annotation.  Split off so the is-a-proposition gate is a tail call (task #24
point 7).  `thm_witness_core` at the cited `throw`s.

`hlenv` is task #58's added hypothesis; see the section note. -/
theorem check_thm_val_witness_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_thm_val_witness mode st fe cv value = ok (out, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) → lenv = lfe.env →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (do
            let lv := absExpr value
            if ¬ lv.looseBVarsBounded 0 then
              throw (ConLeche.CheckError.invalid "loose bound variable in value")
            else if lv.hasFvar then
              throw (ConLeche.CheckError.invalid "unexpected free variable in value")
            else do
              let jv ← (TypeChecker.lops mode lfe).annotate lenv 0 lv
              if ¬ jv.allLevelParamsDefined (absConstantVal cv).levelParams then
                throw (ConLeche.CheckError.invalid "undeclared universe parameter")
              else if ¬ jv.constsResolve lenv then
                throw (ConLeche.CheckError.invalid "unknown constant")
              else do
                let vtype ← (TypeChecker.lops mode lfe).inferType lenv 0 jv
                let okv ← (TypeChecker.lops mode lfe).isDefEq lenv 0 vtype
                  (absConstantVal cv).type
                if okv then
                  pure (⟨ConLeche.ConstantInfo.thmInfo (absConstantVal cv) lv
                    :: lenv.consts⟩ : ConLeche.Env)
                else throw (ConLeche.CheckError.invalid "type mismatch")).run lst
            = .ok (lfe'.env, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
      | .Err ce =>
        ErrSim ce ((do
            let lv := absExpr value
            if ¬ lv.looseBVarsBounded 0 then
              throw (ConLeche.CheckError.invalid "loose bound variable in value")
            else if lv.hasFvar then
              throw (ConLeche.CheckError.invalid "unexpected free variable in value")
            else do
              let jv ← (TypeChecker.lops mode lfe).annotate lenv 0 lv
              if ¬ jv.allLevelParamsDefined (absConstantVal cv).levelParams then
                throw (ConLeche.CheckError.invalid "undeclared universe parameter")
              else if ¬ jv.constsResolve lenv then
                throw (ConLeche.CheckError.invalid "unknown constant")
              else do
                let vtype ← (TypeChecker.lops mode lfe).inferType lenv 0 jv
                let okv ← (TypeChecker.lops mode lfe).isDefEq lenv 0 vtype
                  (absConstantVal cv).type
                if okv then
                  pure (⟨ConLeche.ConstantInfo.thmInfo (absConstantVal cv) lv
                    :: lenv.consts⟩ : ConLeche.Env)
                else throw (ConLeche.CheckError.invalid "type mismatch")).run lst) := by
  intro lst lfe lenv hsr hfr henv hlenv
  have hcore :=
    thm_witness_core hfuel hk hp hsw hfw hcv hv h lst lfe lenv hsr hfr henv hlenv
  cases out with
  | Ok fe' =>
    obtain ⟨lst', hsr', hsw', hwf', hrel', hrun⟩ := hcore
    exact ⟨lst', _, by
      simpa only [ite_not] using hrun
        (throw (ConLeche.CheckError.invalid "loose bound variable in value"))
        (throw (ConLeche.CheckError.invalid "unexpected free variable in value"))
        (fun _ => throw (ConLeche.CheckError.invalid "undeclared universe parameter"))
        (fun _ => throw (ConLeche.CheckError.invalid "unknown constant"))
        (fun _ => throw (ConLeche.CheckError.invalid "type mismatch")),
      hsr', hsw', hrel', hwf'⟩
  | Err ce =>
    exact by
      simpa only [ite_not] using hcore
        (throw (ConLeche.CheckError.invalid "loose bound variable in value"))
        (throw (ConLeche.CheckError.invalid "unexpected free variable in value"))
        (fun _ => throw (ConLeche.CheckError.invalid "undeclared universe parameter"))
        (fun _ => throw (ConLeche.CheckError.invalid "unknown constant"))
        (fun _ => throw (ConLeche.CheckError.invalid "type mismatch"))
        (fun _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩)
        (fun _ _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩)

/-- The success half of `check_thm_val_witness_refines`, at the pre-task-#67
statement. -/
theorem check_thm_val_witness_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_thm_val_witness mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) → lenv = lfe.env →
      ∃ lst' lfe',
        (do
          let lv := absExpr value
          if ¬ lv.looseBVarsBounded 0 then
            throw (ConLeche.CheckError.invalid "loose bound variable in value")
          else if lv.hasFvar then
            throw (ConLeche.CheckError.invalid "unexpected free variable in value")
          else do
            let jv ← (TypeChecker.lops mode lfe).annotate lenv 0 lv
            if ¬ jv.allLevelParamsDefined (absConstantVal cv).levelParams then
              throw (ConLeche.CheckError.invalid "undeclared universe parameter")
            else if ¬ jv.constsResolve lenv then
              throw (ConLeche.CheckError.invalid "unknown constant")
            else do
              let vtype ← (TypeChecker.lops mode lfe).inferType lenv 0 jv
              let okv ← (TypeChecker.lops mode lfe).isDefEq lenv 0 vtype
                (absConstantVal cv).type
              if okv then
                pure (⟨ConLeche.ConstantInfo.thmInfo (absConstantVal cv) lv
                  :: lenv.consts⟩ : ConLeche.Env)
              else throw (ConLeche.CheckError.invalid "type mismatch")).run lst
          = .ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' :=
  check_thm_val_witness_refines hfuel hk hp hsw hfw hcv hv h

/-- **`checker::check_opaque_val` refines `checkOpaqueVal`**
(`ConLeche/Kernel/Checker.lean:84-107`): exactly the theorem check without the
is-a-proposition requirement, and the result is stored as an `axiomInfo` —
the checked value is a realizability witness, and the official kernel's
`is_delta` never unfolds an opaque.

`hlenv` is task #58's added hypothesis; see the section note. -/
theorem check_opaque_val_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_opaque_val mode st fe cv value = ok (out, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) → lenv = lfe.env →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.checkOpaqueVal (TypeChecker.lops mode lfe) lenv (absConstantVal cv)
              (absExpr value)).run lst = .ok (lfe'.env, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
      | .Err ce =>
        ErrSim ce ((ConLeche.checkOpaqueVal (TypeChecker.lops mode lfe) lenv
          (absConstantVal cv) (absExpr value)).run lst) := by
  intro lst lfe lenv hsr hfr henv hlenv
  subst hlenv
  rw [kernel.checker.check_opaque_val] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = (absExpr value).looseBVarsBounded 0 :=
    ExprOps.loose_bvars_bounded_refines hv hb
  cases b with
  | false =>
    -- `checker.rs:288` ← `Checker.lean:96`
    simp at h
    obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
    show ErrSim ce _
    rw [invalid_err hce, ConLeche.checkOpaqueVal, if_neg (by rw [← hbv]; simp)]
    exact ErrSim.invalid
      (s := s!"loose bound variable in value of {(absConstantVal cv).name}") rfl
  | true =>
    simp only [if_true] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = (absExpr value).hasFvar := ExprOps.has_fvar_refines hv hb1
    cases b1 with
    | true =>
      -- `checker.rs:290` ← `Checker.lean:98`
      simp at h
      obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
      show ErrSim ce _
      rw [invalid_err hce, ConLeche.checkOpaqueVal, if_pos hbv.symm,
        if_pos (by rw [← hb1v])]
      exact ErrSim.invalid
        (s := s!"unexpected free variable in value of {(absConstantVal cv).name}") rfl
    | false =>
      obtain ⟨p, hann, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err e =>
        -- the annotation threw
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        show ErrSim e _
        rw [ConLeche.checkOpaqueVal, if_pos hbv.symm, if_neg (by rw [← hb1v]; simp)]
        exact ErrSim.bindCM
          ((TypeChecker.annotate_core_refines hfuel hk).err st fe 0#u64 value e st1
            hsw hfw hv hann lst lfe hsr hfr)
      | Ok value_a =>
        obtain ⟨lst1, hruna, hsr1, hsw1, hvaw⟩ :=
          (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 value value_a st1
            hsw hfw hv hann lst lfe hsr hfr
        have hra : (ConLeche.Cached.opE (absMode mode) lfe (·.annotate) 0
            (absExpr value)).run lst = .ok (absExpr value_a, lst1) := hruna
        -- the cited `do` past the annotation, at an arbitrary tail: every arm
        -- of `check_opaque_val_after_annot` below travels through it
        have hhead : ∀ f : ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Env,
            ((TypeChecker.lops mode lfe).annotate lfe.env 0 (absExpr value)
                >>= f).run lst = (f (absExpr value_a)).run lst1 := by
          intro f
          simp only [StateT.run_bind, TypeChecker.sharedOpsC_annotate, hra,
            except_ok_bind]
        have h : kernel.checker.check_opaque_val_after_annot mode st1 fe cv value_a
            = ok (out, st') := h
        rw [kernel.checker.check_opaque_val_after_annot] at h
        obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
        have hb2v : b2 = (absExpr value_a).allLevelParamsDefined
            (absConstantVal cv).levelParams :=
          ExprOps.all_level_params_defined_fast_refines hcv.2.1 hvaw hb2
        cases b2 with
        | false =>
          -- `checker.rs:310` ← `Checker.lean:101`
          simp at h
          obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
          show ErrSim ce _
          rw [invalid_err hce, ConLeche.checkOpaqueVal, if_pos hbv.symm,
            if_neg (by rw [← hb1v]; simp), hhead, if_neg (by rw [← hb2v]; simp)]
          exact ErrSim.invalid
            (s := s!"undeclared universe parameter in value of {(absConstantVal cv).name}")
            rfl
        | true =>
          simp only [if_true] at h
          obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
          have hb3v : b3 = (absExpr value_a).constsResolve lfe.env :=
            CoreK.consts_resolve_refines hp (FindAgree.of_rel hfr hfw) henv hvaw b3 hb3
          cases b3 with
          | false =>
            -- `checker.rs:312` ← `Checker.lean:103`
            simp at h
            obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
            show ErrSim ce _
            rw [invalid_err hce, ConLeche.checkOpaqueVal, if_pos hbv.symm,
              if_neg (by rw [← hb1v]; simp), hhead, if_pos hb2v.symm,
              if_neg (by rw [← hb3v]; simp)]
            exact ErrSim.invalid
              (s := s!"unknown constant in value of {(absConstantVal cv).name}") rfl
          | true =>
            simp only [if_true] at h
            obtain ⟨q, hinf, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨r1, st2⟩ := q
            cases r1 with
            | Err e =>
              -- the inference threw
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              show ErrSim e _
              rw [ConLeche.checkOpaqueVal, if_pos hbv.symm,
                if_neg (by rw [← hb1v]; simp), hhead, if_pos hb2v.symm,
                if_pos hb3v.symm]
              exact ErrSim.bindCM
                ((TypeChecker.infer_type_core_refines hfuel hk).err st1 fe 0#u64 value_a
                  e st2 hsw1 hfw hvaw hinf lst1 lfe hsr1 hfr)
            | Ok vtype =>
              obtain ⟨lst2, hrun2, hsr2, hsw2, hvw⟩ :=
                (TypeChecker.infer_type_core_refines hfuel hk).ok st1 fe 0#u64 value_a vtype st2
                  hsw1 hfw hvaw hinf lst1 lfe hsr1 hfr
              have hr2 : (ConLeche.Cached.opE (absMode mode) lfe (·.infer) 0
                  (absExpr value_a)).run lst1 = .ok (absExpr vtype, lst2) := hrun2
              have hinfer : ∀ f : ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Env,
                  ((TypeChecker.lops mode lfe).inferType lfe.env 0 (absExpr value_a)
                      >>= f).run lst1 = (f (absExpr vtype)).run lst2 := by
                intro f
                simp only [StateT.run_bind, TypeChecker.sharedOpsC_inferType, hr2,
                  except_ok_bind]
              obtain ⟨q2, hdef, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r2, st3⟩ := q2
              cases r2 with
              | Err e =>
                -- the conversion threw
                simp at h
                obtain ⟨rfl, rfl⟩ := h
                show ErrSim e _
                rw [ConLeche.checkOpaqueVal, if_pos hbv.symm,
                  if_neg (by rw [← hb1v]; simp), hhead, if_pos hb2v.symm,
                  if_pos hb3v.symm, hinfer]
                exact ErrSim.bindCM
                  ((TypeChecker.is_def_eq_core_refines hfuel hk).err st2 fe 0#u64 vtype
                    cv.ty e st3 hsw2 hfw hvw hcv.2.2 hdef lst2 lfe hsr2 hfr)
              | Ok okv =>
                obtain ⟨lst3, hrun3, hsr3, hsw3⟩ :=
                  (TypeChecker.is_def_eq_core_refines hfuel hk).ok st2 fe 0#u64 vtype cv.ty
                    okv st3 hsw2 hfw hvw hcv.2.2 hdef lst2 lfe hsr2 hfr
                have hr3 : (ConLeche.Cached.opB (absMode mode) lfe 0 (absExpr vtype)
                    (absConstantVal cv).type).run lst2 = .ok (okv, lst3) := hrun3
                have hdefeq : ∀ f : Bool → ConLeche.Cached.CheckCM ConLeche.Env,
                    ((TypeChecker.lops mode lfe).isDefEq lfe.env 0 (absExpr vtype)
                        (absConstantVal cv).type >>= f).run lst2 = (f okv).run lst3 := by
                  intro f
                  simp only [StateT.run_bind, TypeChecker.sharedOpsC_isDefEq, hr3,
                    except_ok_bind]
                cases okv with
                | false =>
                  -- `checker.rs:325` ← `Checker.lean:106`
                  simp at h
                  obtain ⟨v, -, ce, hce, rfl, rfl⟩ := h
                  show ErrSim ce _
                  rw [invalid_err hce, ConLeche.checkOpaqueVal, if_pos hbv.symm,
                    if_neg (by rw [← hb1v]; simp), hhead, if_pos hb2v.symm,
                    if_pos hb3v.symm, hinfer, hdefeq]
                  simp only [Bool.false_eq_true, if_false]
                  exact ErrSim.invalid
                    (s := s!"type mismatch in opaque {(absConstantVal cv).name}") rfl
                | true =>
                  obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
                  rw [Env.constant_val_dup_refines hcv1] at hpush
                  obtain ⟨rfl, rfl⟩ : core.result.Result.Ok f = out ∧ st3 = st' := by
                    simpa using h
                  obtain ⟨hrel', hwf'⟩ :=
                    push_refines hfr hfw (show ConstantInfoWF (.AxiomInfo cv) from hcv)
                      hpush
                  refine ⟨lst3, _, ?_, hsr3, hsw3, hrel', hwf'⟩
                  rw [ConLeche.checkOpaqueVal, if_pos hbv.symm,
                    if_neg (by rw [← hb1v]; simp), hhead, if_pos hb2v.symm,
                    if_pos hb3v.symm, hinfer, hdefeq]
                  rfl

/-- The success half of `check_opaque_val_refines`, at the pre-task-#67
statement. -/
theorem check_opaque_val_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_opaque_val mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) → lenv = lfe.env →
      ∃ lst' lfe',
        (ConLeche.checkOpaqueVal (TypeChecker.lops mode lfe) lenv (absConstantVal cv)
            (absExpr value)).run lst = .ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' :=
  check_opaque_val_refines hfuel hk hp hsw hfw hcv hv h


/-! ## The structural-`Nat` certification

`certifyNatEqs` (`Checker.lean:108-116`) is a `List` recursion; the port is an
index recursion over the `Vec` (task #3's pattern), so the statement is about
the list's `drop i`.  The `Env` argument is **universally quantified** — see
the module note; that is what carries `checkDecl`'s pre-insertion deviation. -/

/-- The tail fold with an explicit bound to recurse on.  The outcome is an
explicit argument (the recursion instantiates it at each step), so the
pre-task-#67 statement lives on as `certify_nat_eqs_from_refines_ok`. -/
theorem certify_nat_eqs_val {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {fe : fenv.FEnv} {eqs : alloc.vec.Vec (expr.Expr × expr.Expr)}
    (hfw : FEnvWF fe) (heq : ∀ p ∈ eqs.val, ExprWF p.1 ∧ ExprWF p.2) (n : Nat) :
    ∀ (st st' : cached.state_c.CState) (i : Std.Usize)
      (o : core.result.Result Bool core_types.CheckError),
      eqs.val.length - i.val ≤ n → StateWF st →
      kernel.checker.certify_nat_eqs_from mode st fe eqs i = ok (o, st') →
      ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
        match o with
        | .Ok b =>
          ∃ lst',
            (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
                ((eqs.val.drop i.val).map (fun p => (absExpr p.1, absExpr p.2)))).run lst
              = .ok (b, lst')
            ∧ StateRel st' lst' ∧ StateWF st'
        | .Err ce =>
          ErrSim ce ((ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
            ((eqs.val.drop i.val).map (fun p => (absExpr p.1, absExpr p.2)))).run lst) := by
  induction n with
  | zero =>
    intro st st' i o hb hsw h lst lfe lenv hsr hfr
    rw [kernel.checker.certify_nat_eqs_from] at h
    rw [if_pos (show i >= alloc.vec.Vec.len eqs by
      have := alloc.vec.Vec.len_val eqs; scalar_tac)] at h
    have hbs : core.result.Result.Ok true = o ∧ st = st' := by simpa using h
    obtain ⟨rfl, rfl⟩ := hbs
    refine ⟨lst, ?_, hsr, hsw⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ n ih =>
    intro st st' i o hb hsw h lst lfe lenv hsr hfr
    rw [kernel.checker.certify_nat_eqs_from] at h
    by_cases hge : i.val >= eqs.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len eqs by
        have := alloc.vec.Vec.len_val eqs; scalar_tac)] at h
      have hbs : core.result.Result.Ok true = o ∧ st = st' := by simpa using h
      obtain ⟨rfl, rfl⟩ := hbs
      refine ⟨lst, ?_, hsr, hsw⟩
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
    · rw [if_neg (show ¬ (i >= alloc.vec.Vec.len eqs) by
        have := alloc.vec.Vec.len_val eqs; scalar_tac)] at h
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e1, e2⟩ := q
      have hmem : (e1, e2) ∈ eqs.val :=
        List.mem_of_getElem? (ExprOps.vec_index_getElem? hq)
      obtain ⟨hw1, hw2⟩ := heq (e1, e2) hmem
      have hlen : i.val < eqs.val.length := by omega
      have hdrop : eqs.val.drop i.val = (e1, e2) :: eqs.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlen]
        congr 1
        have h1 : eqs.val[i.val]? = some (e1, e2) := ExprOps.vec_index_getElem? hq
        rw [List.getElem?_eq_getElem hlen] at h1
        exact Option.some_inj.mp h1
      obtain ⟨q2, hdef, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := q2
      cases r with
      | Err e =>
        -- the conversion threw; con-leche's `do` fails at the same step
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        show ErrSim e _
        rw [hdrop]
        simp only [List.map_cons, ConLeche.certifyNatEqs,
          TypeChecker.sharedOpsC_isDefEq]
        exact ErrSim.bindCM
          ((TypeChecker.is_def_eq_core_refines hfuel hk).err st fe 2#u64 e1 e2 e st1
            hsw hfw hw1 hw2 hdef lst lfe hsr hfr)
      | Ok ok1 =>
        obtain ⟨lst1, hrun, hsr1, hsw1⟩ :=
          (TypeChecker.is_def_eq_core_refines hfuel hk).ok st fe 2#u64 e1 e2 ok1 st1
            hsw hfw hw1 hw2 hdef lst lfe hsr hfr
        have hrun2 : (ConLeche.Cached.opB (absMode mode) lfe 2
            (absExpr e1) (absExpr e2)).run lst = .ok (ok1, lst1) := hrun
        have hstep : (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
              ((eqs.val.drop i.val).map (fun p => (absExpr p.1, absExpr p.2)))).run lst
            = (if ok1 then
                (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
                  ((eqs.val.drop (i.val + 1)).map (fun p => (absExpr p.1, absExpr p.2)))).run lst1
              else .ok (false, lst1)) := by
          simp only [hdrop, List.map_cons, ConLeche.certifyNatEqs, StateT.run_bind,
            TypeChecker.sharedOpsC_isDefEq, hrun2]
          cases ok1 <;> simp [List.map_drop] <;> rfl
        cases ok1 with
        | false =>
          have hbs : core.result.Result.Ok false = o ∧ st1 = st' := by simpa using h
          obtain ⟨rfl, rfl⟩ := hbs
          exact ⟨lst1, by rw [hstep]; simp, hsr1, hsw1⟩
        | true =>
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := by
            have he := Std.UScalar.add_equiv i 1#usize
            rw [hi2] at he
            simpa using he.2.1
          have hih := ih st1 st' i2 o (by omega) hsw1 h lst1 lfe lenv hsr1 hfr
          cases o with
          | Ok b =>
            obtain ⟨lst', hrun', hsr', hsw'⟩ := hih
            rw [hi2v] at hrun'
            exact ⟨lst', by rw [hstep]; simpa using hrun', hsr', hsw'⟩
          | Err ce =>
            show ErrSim ce _
            have hih' : ErrSim ce ((ConLeche.certifyNatEqs (TypeChecker.lops mode lfe)
                lenv ((eqs.val.drop i2.val).map
                  (fun p => (absExpr p.1, absExpr p.2)))).run lst1) := hih
            rw [hi2v] at hih'
            rw [hstep]
            simpa using hih'

/-- **`checker::certify_nat_eqs_from` refines `certifyNatEqs` on the tail**:
certify the equations from position `i` by definitional equality at depth 2
(the equations' variables are `fvar 0`/`fvar 1`).  Exact in both directions of
the Boolean, which is what `checkDecl`'s `unless ok` branches on. -/
theorem certify_nat_eqs_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {eqs : alloc.vec.Vec (expr.Expr × expr.Expr)} {i : Std.Usize}
    {out : core.result.Result Bool core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe)
    (heq : ∀ p ∈ eqs.val, ExprWF p.1 ∧ ExprWF p.2)
    (h : kernel.checker.certify_nat_eqs_from mode st fe eqs i = ok (out, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok b =>
        ∃ lst',
          (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
              ((eqs.val.drop i.val).map (fun p => (absExpr p.1, absExpr p.2)))).run lst
            = .ok (b, lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err ce =>
        ErrSim ce ((ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
          ((eqs.val.drop i.val).map (fun p => (absExpr p.1, absExpr p.2)))).run lst) := by
  intro lst lfe lenv hsr hfr
  -- the hypothesis `h` mentions `out`, so this statement's `match` is the
  -- *dependent* one; `certify_nat_eqs_val`'s is not, and the two agree only
  -- once `out` is a constructor
  have hval := certify_nat_eqs_val hfuel hk hfw heq eqs.val.length st st' i out
    (by omega) hsw h lst lfe lenv hsr hfr
  cases out with
  | Ok b => exact hval
  | Err ce => exact hval

/-- The success half of `certify_nat_eqs_from_refines`, at the pre-task-#67
statement. -/
theorem certify_nat_eqs_from_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {eqs : alloc.vec.Vec (expr.Expr × expr.Expr)} {i : Std.Usize} {b : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe)
    (heq : ∀ p ∈ eqs.val, ExprWF p.1 ∧ ExprWF p.2)
    (h : kernel.checker.certify_nat_eqs_from mode st fe eqs i = ok (.Ok b, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
            ((eqs.val.drop i.val).map (fun p => (absExpr p.1, absExpr p.2)))).run lst
          = .ok (b, lst')
        ∧ StateRel st' lst' ∧ StateWF st' :=
  certify_nat_eqs_from_refines hfuel hk hsw hfw heq h

/-- **`checker::certify_nat_eqs` refines `certifyNatEqs`**
(`Checker.lean:108-116`), the whole list.  `certify_nat_eqs_from_refines` at
`i = 0`. -/
theorem certify_nat_eqs_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {eqs : alloc.vec.Vec (expr.Expr × expr.Expr)}
    {out : core.result.Result Bool core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe)
    (heq : ∀ p ∈ eqs.val, ExprWF p.1 ∧ ExprWF p.2)
    (h : kernel.checker.certify_nat_eqs mode st fe eqs = ok (out, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok b =>
        ∃ lst',
          (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
              (eqs.val.map (fun p => (absExpr p.1, absExpr p.2)))).run lst = .ok (b, lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err ce =>
        ErrSim ce ((ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
          (eqs.val.map (fun p => (absExpr p.1, absExpr p.2)))).run lst) := by
  intro lst lfe lenv hsr hfr
  rw [kernel.checker.certify_nat_eqs] at h
  have hfrom := certify_nat_eqs_from_refines hfuel hk hsw hfw heq h lst lfe lenv hsr hfr
  cases out with
  | Ok b =>
    obtain ⟨lst', hrun, rest⟩ := hfrom
    exact ⟨lst', by simpa using hrun, rest⟩
  | Err ce =>
    show ErrSim ce _
    have hfrom' : ErrSim ce ((ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
        ((eqs.val.drop (0#usize).val).map
          (fun p => (absExpr p.1, absExpr p.2)))).run lst) := hfrom
    simpa using hfrom'

/-- The success half of `certify_nat_eqs_refines`, at the pre-task-#67
statement. -/
theorem certify_nat_eqs_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {eqs : alloc.vec.Vec (expr.Expr × expr.Expr)} {b : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe)
    (heq : ∀ p ∈ eqs.val, ExprWF p.1 ∧ ExprWF p.2)
    (h : kernel.checker.certify_nat_eqs mode st fe eqs = ok (.Ok b, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
            (eqs.val.map (fun p => (absExpr p.1, absExpr p.2)))).run lst = .ok (b, lst')
        ∧ StateRel st' lst' ∧ StateWF st' :=
  certify_nat_eqs_refines hfuel hk hsw hfw heq h


/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing from Aeneas's library, nothing from the `Arc` models, no `sorry`: the
three standard Lean axioms only. -/

/-- info: 'ConRon.Refine.Checker.check_defn_val_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_defn_val_refines

/-- info: 'ConRon.Refine.Checker.check_thm_val_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_thm_val_refines

/-- info: 'ConRon.Refine.Checker.check_opaque_val_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_opaque_val_refines

end ConRon.Refine.Checker
