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
`Expr.constsResolve`.  (`checkDefnValF` uses `Expr.constsResolveF fe`
instead; a `constsResolveF` refinement — the same walk at the index — is owed
and noted at `check_defn_val_after_annot_refines`.)

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

`sorry` count in this file: 5.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Checker

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
duplicate-checked, returning the pushed index. -/
theorem install_basis_decl_refines {fe fe' : fenv.FEnv} {ci : env.ConstantInfo}
    (hfw : FEnvWF fe) (hci : ConstantInfoWF ci)
    (h : kernel.checker.install_basis_decl fe ci = ok (.Ok fe')) :
    ∀ lfe, FEnvRel fe lfe →
      FEnvRel fe' (lfe.push (absConstantInfo ci)) ∧ FEnvWF fe'
        ∧ (lfe.find? (absConstantInfo ci).name).isNone := by
  intro lfe hfr
  rw [kernel.checker.install_basis_decl] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hnm := Env.constant_info_name_refines hn
  have hnw := constant_info_name_wf hci hn
  have hfind := find_refines hfr hfw hnw ho
  cases o with
  | some c => simp [core.option.Option.is_some] at h
  | none =>
    -- the `if` and the `Option.is_some` are iota, which only the unifier sees
    -- through here (task #16's hard spot 1)
    have h2 : (do let f ← fenv.push fe ci
                  ok (core.result.Result.Ok f)) = ok (core.result.Result.Ok fe') := h
    obtain ⟨f, hpush, h3⟩ := bind_eq_ok_iff.mp h2
    have hfe' : f = fe' := by simpa using h3
    subst hfe'
    obtain ⟨hrel', hwf'⟩ := push_refines hfr hfw hci hpush
    exact ⟨hrel', hwf', by rw [← hnm, ← hfind]; rfl⟩

/-! ## The value declarations -/

/-- **`checker::check_defn_val` refines `checkDefnValF`**
(`ConLeche/Kernel/DeclCheck.lean:838-853`): the two scope guards and the
annotation of the value; the tail is `check_defn_val_after_annot_refines`.

`sorry`: `Refine/ExprOpsFields.lean`'s
`loose_bvars_bounded_refines`/`has_fvar_refines`,
`Refine/TypeChecker.lean`'s `annotate_core_refines`, then the tail. -/
theorem check_defn_val_refines {mode : env.CheckMode} {fuel : Std.U64}
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
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- **The tail of `checkDefnValF` past the annotation**: the level-parameter
and resolution guards, the value's inferred type against the declared one, and
the push.  Stated at an arbitrary annotated `value_a`, which is what makes the
split compose.

`sorry`: `all_level_params_defined_fast_refines`, a `constsResolveF`
refinement (the index walk of `Expr.constsResolve`, owed —
`Refine/CoreKSupport.lean` has the `Env` reading), `infer_type_core_refines`,
`is_def_eq_core_refines` and `Refine/FEnv.lean`'s `push_refines`. -/
theorem check_defn_val_after_annot_refines {mode : env.CheckMode} {fuel : Std.U64}
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
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- **`checker::check_thm_val` refines `checkThmVal`**
(`ConLeche/Kernel/Checker.lean:52-82`): the statement's sort and the
is-a-proposition gate; the witness half is
`check_thm_val_witness_refines`.  **A theorem is stored by its statement** —
the constant keeps the record's own raw value as an unread datum and the
annotated value is a realizability witness, checked and discarded.

`sorry`: `infer_type_core_refines`, `ensure_sort_core_refines`, then
`Refine/CoreKVec.lean`'s `lift_fueled_refines` over `Refine/Level.lean`'s
`is_equiv_refines`, then the witness half. -/
theorem check_thm_val_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_thm_val mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) →
      ∃ lst' lfe',
        (ConLeche.checkThmVal (TypeChecker.lops mode lfe) lenv (absConstantVal cv)
            (absExpr value)).run lst = .ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- **The witness half of `checkThmVal`**: the value's syntactic guards and its
annotation.  Split off so the is-a-proposition gate is a tail call (task #24
point 7).

`sorry`: the two scope guards and `annotate_core_refines`, then
`check_thm_val_checked_refines`. -/
theorem check_thm_val_witness_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_thm_val_witness mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) →
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
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- **`checker::check_opaque_val` refines `checkOpaqueVal`**
(`ConLeche/Kernel/Checker.lean:84-107`): exactly the theorem check without the
is-a-proposition requirement, and the result is stored as an `axiomInfo` —
the checked value is a realizability witness, and the official kernel's
`is_delta` never unfolds an opaque.

`sorry`: the two scope guards, `annotate_core_refines`, then the tail. -/
theorem check_opaque_val_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_opaque_val mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) →
      ∃ lst' lfe',
        (ConLeche.checkOpaqueVal (TypeChecker.lops mode lfe) lenv (absConstantVal cv)
            (absExpr value)).run lst = .ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-! ## The structural-`Nat` certification

`certifyNatEqs` (`Checker.lean:108-116`) is a `List` recursion; the port is an
index recursion over the `Vec` (task #3's pattern), so the statement is about
the list's `drop i`.  The `Env` argument is **universally quantified** — see
the module note; that is what carries `checkDecl`'s pre-insertion deviation. -/

/-- The tail fold with an explicit bound to recurse on. -/
theorem certify_nat_eqs_val {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {fe : fenv.FEnv} {eqs : alloc.vec.Vec (expr.Expr × expr.Expr)}
    (hfw : FEnvWF fe) (heq : ∀ p ∈ eqs.val, ExprWF p.1 ∧ ExprWF p.2) (n : Nat) :
    ∀ (st st' : cached.state_c.CState) (i : Std.Usize) (b : Bool),
      eqs.val.length - i.val ≤ n → StateWF st →
      kernel.checker.certify_nat_eqs_from mode st fe eqs i = ok (.Ok b, st') →
      ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
        ∃ lst',
          (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
              ((eqs.val.drop i.val).map (fun p => (absExpr p.1, absExpr p.2)))).run lst
            = .ok (b, lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  induction n with
  | zero =>
    intro st st' i b hb hsw h lst lfe lenv hsr hfr
    rw [kernel.checker.certify_nat_eqs_from] at h
    rw [if_pos (show i >= alloc.vec.Vec.len eqs by
      have := alloc.vec.Vec.len_val eqs; scalar_tac)] at h
    have hbs : b = true ∧ st = st' := by simpa using h
    obtain ⟨rfl, rfl⟩ := hbs
    refine ⟨lst, ?_, hsr, hsw⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ n ih =>
    intro st st' i b hb hsw h lst lfe lenv hsr hfr
    rw [kernel.checker.certify_nat_eqs_from] at h
    by_cases hge : i.val >= eqs.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len eqs by
        have := alloc.vec.Vec.len_val eqs; scalar_tac)] at h
      have hbs : b = true ∧ st = st' := by simpa using h
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
      obtain ⟨q2, hdef, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := q2
      cases r with
      | Err e => simp at h
      | Ok ok1 =>
        obtain ⟨lst1, hrun, hsr1, hsw1⟩ :=
          TypeChecker.is_def_eq_core_refines hfuel hk st fe 2#u64 e1 e2 ok1 st1
            hsw hfw hw1 hw2 hdef lst lfe hsr hfr
        have hrun2 : (ConLeche.Cached.opB (absMode mode) lfe 2
            (absExpr e1) (absExpr e2)).run lst = .ok (ok1, lst1) := hrun
        have hlen : i.val < eqs.val.length := by omega
        have hdrop : eqs.val.drop i.val = (e1, e2) :: eqs.val.drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons hlen]
          congr 1
          have h1 : eqs.val[i.val]? = some (e1, e2) := ExprOps.vec_index_getElem? hq
          rw [List.getElem?_eq_getElem hlen] at h1
          exact Option.some_inj.mp h1
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
          have hbs : b = false ∧ st1 = st' := by simpa using h
          obtain ⟨rfl, rfl⟩ := hbs
          exact ⟨lst1, by rw [hstep]; simp, hsr1, hsw1⟩
        | true =>
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := by
            have he := Std.UScalar.add_equiv i 1#usize
            rw [hi2] at he
            simpa using he.2.1
          obtain ⟨lst', hrun', hsr', hsw'⟩ :=
            ih st1 st' i2 b (by omega) hsw1 h lst1 lfe lenv hsr1 hfr
          rw [hi2v] at hrun'
          exact ⟨lst', by rw [hstep]; simpa using hrun', hsr', hsw'⟩

/-- **`checker::certify_nat_eqs_from` refines `certifyNatEqs` on the tail**:
certify the equations from position `i` by definitional equality at depth 2
(the equations' variables are `fvar 0`/`fvar 1`).  Exact in both directions of
the Boolean, which is what `checkDecl`'s `unless ok` branches on. -/
theorem certify_nat_eqs_from_refines {mode : env.CheckMode} {fuel : Std.U64}
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
  certify_nat_eqs_val hfuel hk hfw heq eqs.val.length st st' i b (by omega) hsw h

/-- **`checker::certify_nat_eqs` refines `certifyNatEqs`**
(`Checker.lean:108-116`), the whole list.  `certify_nat_eqs_from_refines` at
`i = 0`. -/
theorem certify_nat_eqs_refines {mode : env.CheckMode} {fuel : Std.U64}
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
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe lenv hsr hfr
  rw [kernel.checker.certify_nat_eqs] at h
  obtain ⟨lst', hrun, rest⟩ :=
    certify_nat_eqs_from_refines hfuel hk hsw hfw heq h lst lfe lenv hsr hfr
  exact ⟨lst', by simpa using hrun, rest⟩

end ConRon.Refine.Checker
