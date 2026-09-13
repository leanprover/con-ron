/-
# `kernel::inductives::native_install` refined (task #57)

`CORE_PLAN.md` step 7.  The direct (fixpoint) route's **install stages**
(`crates/con-ron-core/src/kernel/inductives/native_install.rs`, 45 items)
against `ConLeche/Kernel/Inductives/NativeInstall.lean` and its index twin
`NativeInstallF.lean`.  Task #25's deviation 1 is that the port has *one*
function per `Env`/index pair carrying both citations, so every statement here
is against the `*F` spelling — the one the executable runs, and the one
`Cached/CheckerC.lean`'s drivers call.

| group | items |
|---|---|
| the capability record | `native_caps_at`, `NativeCapsAt::caps_of`, `native_is_rec`, `native_is_rec_from`, `kinds_any_rec_from`, `native_caps`, `native_raw_rec`, `dom_mentions_from` |
| `Expr.mentionsFvar` | `mentions_fvar_spec`, `leaves_any_from`, `mentions_fvar_ins`, `mentions_fvar_go`, `mentions_fvar_node`, `mentions_fvar` |
| the kinds re-checked | `all_resolve_from`, `all_annots_resolve_from`, `no_later_mentions_from`, `native_opened_recursive`, `native_opened_reflexive`, `native_opened_fields_from`, `native_opened_ok`, `native_fields_ok`, `native_fields_ok_from` |
| the recursor stage | `term_scoped`, `check_native_rules`, `check_native_rec`, `check_native_rec_rules`, `check_native_table` |
| the pass | `rec_ctor_kinds_all`, `kinds_any_from`, `kind_list_any_from`, `classify_fix_kinds`, `check_native_pass`, **`check_native_pass_former`**, **`check_native_pass_ctors`** |
| the tail | `check_native_tail`, `elim_restriction_violated`, **`check_native_tail_guards`**, **`check_native_cons`**, **`check_native_install`** |
| the driver | `check_native`, **`ctor_names`**, `ctor_names_from` |

The five **bold** stages plus `ctor_names`, `native_raw_rec` and
`native_is_rec` are what `Refine/IndC.lean`'s three `*_s` driver lemmas
consume.

## The three deviations this file had to reason about

* **`NativePass` loses Lean's type parameter.**  `NativePass (E : Type)` is
  `Env` at the pure install and `FEnv` at the cached mirror; deviation 1
  leaves one record, whose `env1` field is an `FEnv`.  `IndAbs.NativePassRel`
  is therefore a *relation* (a record storing an `FEnv` cannot abstract by a
  function) and `IndAbs.NativePassWF` its invariant; every statement below
  that produces or consumes a pass is stated relationally.

* **Three stages are split so the cached driver's `flushC` lands exactly
  where con-leche's does**, with one body serving both spellings:
  `check_native_pass` → `check_native_pass_former` + `check_native_pass_ctors`
  (the flush sits between `checkSumIndF` and `checkSumCtorsF`,
  `CheckerC.lean:178-183`), and `check_native_tail` →
  `check_native_tail_guards` + `check_native_cons` + `check_native_install`
  (the flush sits after `consSumCtorsF` and before `checkNativeRecF`,
  `CheckerC.lean:194-211`).  con-leche writes both bodies inline inside
  `checkNativePassS`/`checkNativeTailS`, so this file *names* the four halves
  — `checkNativePassFormerF` (the cited `:178-181`), `checkNativePassCtorsF`
  (`:182-190`), `checkNativeTailGuardsF` (`:194-207`) and
  `checkNativeInstallF` (`:209-215`) — and carries an identity
  (`checkNativePassS_eq`, `checkNativeTailS_eq`) saying that the cited driver
  *is* the two halves around `flushC`, in the style `Refine/StateC.lean` uses
  for `eqvStep`.

* **`native_install::NativeCapsAt` is the one implementation of
  `sum_install::CapsOf`** (task #9's pattern 1: the closure
  `fun p₁ => nativeCapsAt p₁ isRec` becomes a dictionary with the captured
  `isRec` as its field).  `caps_of_refines` below is its dictionary
  refinement, which is exactly the hypothesis the sibling `check_sum_ind`
  lemma takes.

## A finding: three items are dead in the shipped binary

`check_native_pass`, `check_native_tail` and `check_native` are the *pure*
route's spelling — the cited `checkNativePass`/`checkNativeTail`/`checkNative`
at the index (deviation 1), i.e. the `*S` drivers **minus every `flushC`**.
`inductives_c::check_native_s` does not call them: it calls the five halves
directly, with the flushes between, and nothing else in the crate calls them
either — dead exactly as `core_k::beta_gate_fires` is
(`Refine/CoreKGuards.lean`).  `NativeInstallF.lean` stops at
`checkNativeTableF`, so con-leche writes no index twin of the three; the
statements below are against `checkNativePassI`/`checkNativeTailI`/
`checkNativeI`, this file's transcriptions of the cited pure bodies with
`Env` replaced by the index — the same transcription move `Refine/IndC.lean`
makes for `checkIndDeclStructS`.

## `Expr.mentionsFvar`, the fourth `@[csimp]` family

The port implements the `*Fast` member and cites the `*Go` walk, the logical
`def` and the `@[csimp]` lemma (`NativeInstall.lean:139-141`, `:221-257`,
`:379-386`).  The statement is against the cited **`def`**
(`e.fvarLeaves.any (·.1 == q)`) and the proof goes through con-leche's own
`mentionsFvar_eq_mentionsFvarFast`; unlike `mentionsConstGo` this walk **does**
short-circuit (`| (true, memo) => (true, memo)`) and the port keeps that, so
the memo the two branches hand back differs and only the `Bool` plus the memo
invariant are claimed.

## What this file does not own

The knot is assumed (task #55 proves its arms): every lemma below a `core_c`
wrapper takes `hw : Core.Wrappers mode IndAbs.checkFuelU` and reaches the core
only through `IndAbs.ops_*`.  Sibling facts travel as named `Prop`
ingredients, in the exact-result shape, with a doc comment naming the file
that owns each — nothing is weakened this way.

## What is proved

Twenty-one items are proved outright: `native_caps_at`'s default arm and the
whole `caps_of` dictionary bridge on top of it, the five `Bool` index
recursions of the capability record (`kinds_any_rec_from`,
`native_is_rec_from`, `native_is_rec`, `native_caps`, `dom_mentions_from`),
`leaves_any_from` and `mentions_fvar_spec`, `mentions_fvar_ins`'s memo
preservation and `mentions_fvar` (modulo the walk), the three `all`/`any`
loops of the opened re-check (`all_resolve_from`, `all_annots_resolve_from`,
`no_later_mentions_from`), `term_scoped`, `kind_list_any_from`,
`kinds_any_from`, `elim_restriction_violated`, `check_native_cons`,
`ctor_names_from`/`ctor_names`, `level::name_nodup`, and the two compositions
`check_native_pass` / `check_native_tail` (each from its halves).

## `sorry` count

23 `sorry`s, each noted at its site: `native_caps_at`'s one-constructor arm,
`native_raw_rec`, the memoized `mentionsFvar` walk's mutual pair
(`mentions_fvar_go`, `mentions_fvar_node`), the six opened-re-check stages
above the three proved loops (`native_opened_recursive`,
`native_opened_reflexive`, `native_opened_fields_from`, `native_opened_ok`,
`native_fields_ok_from`, `native_fields_ok`), the recursor stage's four
(`check_native_rules`, `check_native_rec_rules`, `check_native_rec`,
`check_native_table`), `rec_ctor_kinds_all` and `classify_fix_kinds`, the four
split halves (`check_native_pass_former`, `check_native_pass_ctors`,
`check_native_tail_guards`, `check_native_install`), `check_native`, and the
two `do`-block identities (`checkNativePassS_eq`, `checkNativeTailS_eq`),
whose two sides differ only by `bind_assoc` across a `throw`-carrying `if`.
Every statement is the exact-result one and nothing is weakened.

One `sorry` hides a **missing bridge rather than missing work**:
`check_native_pass_former` copies the index with `fenv::dup`, and
`Refine/FEnv.lean`'s `dup_refines` relates the copy to
`(mkFEnv (absEnv fe.env)).restrictTo fe.visible_below.val`, not to the `lfe`
the caller holds — con-leche's `checkNativePassS` passes its own `fe`, which is
persistent, so the composition needs `FEnvRel fe lfe → FEnvRel (dup fe) lfe`.
`check_native_rec_rules` has the same shape.  That lemma belongs in
`Refine/FEnv.lean`.
-/
import ConRon.Refine.IndAbs
import ConRon.Refine.IndSumParts
import ConRon.Refine.IndStructInstall
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.CoreKVec
import ConLeche.Verify.Cached.WalkersC

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.NativeInstall

/-! ## Two abstractions this file needs (**to be unified into
`Refine/Abs.lean`**) -/

/-- `nativeCtors4`'s output: the recursor generator's per-constructor view
(name, field count, stored type, recursive-field indices). -/
def absCtors4
    (cs : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × alloc.vec.Vec Std.U64)) :
    List (ConLeche.Name × Nat × ConLeche.Expr × List Nat) :=
  cs.val.map (fun c => (absName c.1, c.2.1.val, absExpr c.2.2.1,
    c.2.2.2.val.map (fun i => i.val)))

/-- Every stored name and type of a `nativeCtors4` view is well formed. -/
def Ctors4WF
    (cs : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × alloc.vec.Vec Std.U64)) :
    Prop :=
  ∀ c ∈ cs.val, NameWF c.1 ∧ ExprWF c.2.2.1

/-! ## The ingredients this file does not own

Each is the exact-result refinement of one sibling's item, named here so that
the conclusions below stay exact under an explicit hypothesis
(`Refine/StateC.lean`'s `InstantiateListRefines` is the pattern).  The two
`StructInstall.*` ingredients are reused from `Refine/IndStructInstall.lean`
rather than respelled.  Each `mode`-indexed one is discharged by its owner
from `Core.Wrappers mode IndAbs.checkFuelU`. -/

section Ingredients

variable (mode : env.CheckMode)

/-- `struct_parts::mentions_const` refines `Expr.mentionsConst`
(`StructParts.lean:775-780`, the `@[csimp]`'d `*Fast` member).
**Owned by `Refine/IndStructParts.lean`.** -/
def MentionsConstRefines : Prop :=
  ∀ (t : name.Name) (e : expr.Expr) (b : Bool), NameWF t → ExprWF e →
    inductives.struct_parts.mentions_const t e = ok b →
    b = (absExpr e).mentionsConst (absName t)

/-- `struct_parts::params_of` is `lps.map .param` (`StructParts.lean:85`).
**Owned by `Refine/IndStructParts.lean`.** -/
def ParamsOfRefines : Prop :=
  ∀ (lps : alloc.vec.Vec name.Name) (us : alloc.vec.Vec level.Level),
    NamesWF lps → inductives.struct_parts.params_of lps = ok us →
    absLevels us = (absNames lps).map ConLeche.Level.param ∧ LevelsWF us

/-- `struct_parts::struct_proj_guards` refines `structProjGuards`
(`StructParts.lean:649-656`).  **Owned by `Refine/IndStructParts.lean`.** -/
def StructProjGuardsRefines : Prop :=
  ∀ (cty : expr.Expr) (n_p n_f : Std.U64) (sorts g : alloc.vec.Vec level.Level),
    ExprWF cty → LevelsWF sorts →
    inductives.struct_parts.struct_proj_guards cty n_p n_f sorts = ok g →
    absLevels g
        = ConLeche.structProjGuards (absExpr cty) n_p.val n_f.val (absLevels sorts)
      ∧ LevelsWF g

/-- `native_parts::rec_field_kind_beq` is `BEq` on `RecFieldKind`
(`NativeParts.lean:60-76`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def RecFieldKindBeqRefines : Prop :=
  ∀ (a b : inductives.native_parts.RecFieldKind) (c : Bool),
    inductives.native_parts.rec_field_kind_beq a b = ok c →
    c = (IndAbs.absRecFieldKind a == IndAbs.absRecFieldKind b)

/-- `native_parts::kind_get_d` is `ks.getD i .ordinary`
(`NativeInstallF.lean:31`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def KindGetDRefines : Prop :=
  ∀ (ks : alloc.vec.Vec inductives.native_parts.RecFieldKind) (i : Std.U64)
    (k : inductives.native_parts.RecFieldKind),
    inductives.native_parts.kind_get_d ks i = ok k →
    IndAbs.absRecFieldKind k = (IndAbs.absRecFieldKinds ks).getD i.val .ordinary

/-- `native_parts::pi_binders` refines `Expr.piBinders`
(`NativeParts.lean:150-154`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def PiBindersRefines : Prop :=
  ∀ (e : expr.Expr) (q : (alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr),
    ExprWF e → inductives.native_parts.pi_binders e = ok q →
    (ExprOps.absBinders q.1, absExpr q.2) = (absExpr e).piBinders
      ∧ ExprOps.BindersWF q.1 ∧ ExprWF q.2

/-- `native_parts::rec_ctor_kinds` refines `recCtorKinds`
(`NativeParts.lean:134-148`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def RecCtorKindsRefines : Prop :=
  ∀ (t : name.Name) (lps : alloc.vec.Vec name.Name) (n_p n_idx : Std.U64)
    (c : env.ConstantVal × Std.U64)
    (o : Option (alloc.vec.Vec inductives.native_parts.RecFieldKind)),
    NameWF t → NamesWF lps → ConstantValWF c.1 →
    inductives.native_parts.rec_ctor_kinds t lps n_p n_idx c = ok o →
    o.map IndAbs.absRecFieldKinds
      = ConLeche.recCtorKinds (absName t) (absNames lps) n_p.val n_idx.val
          (absConstantVal c.1, c.2.val)

/-- `native_parts::complete` refines `NativeParts.complete`
(`NativeParts.lean:198-199`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def CompleteRefines : Prop :=
  ∀ (p0 : inductives.native_parts.NativeParts)
    (p1 : inductives.sum_parts.InductiveShape)
    (p : inductives.native_parts.NativeParts),
    IndAbs.NativePartsWF p0 → IndAbs.InductiveShapeWF p1 →
    inductives.native_parts.complete p0 p1 = ok p →
    IndAbs.absNativeParts p
        = (IndAbs.absNativeParts p0).complete (IndAbs.absInductiveShape p1)
      ∧ IndAbs.NativePartsWF p

/-- `native_parts::with_kinds` refines `NativeParts.withKinds`
(`NativeParts.lean:620-622`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def WithKindsRefines : Prop :=
  ∀ (p : inductives.native_parts.NativeParts)
    (ks : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind))
    (p' : inductives.native_parts.NativeParts),
    IndAbs.NativePartsWF p →
    inductives.native_parts.with_kinds p ks = ok p' →
    IndAbs.absNativeParts p'
        = (IndAbs.absNativeParts p).withKinds (IndAbs.absKindss ks)
      ∧ IndAbs.NativePartsWF p'

/-- `native_parts::native_ctors4` refines `nativeCtors4`
(`NativeParts.lean:390-392`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def NativeCtors4Refines : Prop :=
  ∀ (ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64))
    (kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind))
    (r : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × alloc.vec.Vec Std.U64)),
    (∀ c ∈ ctors_a.val, ConstantValWF c.1) →
    inductives.native_parts.native_ctors4 ctors_a kinds = ok r →
    absCtors4 r = ConLeche.nativeCtors4 (IndAbs.absCtors ctors_a)
        (IndAbs.absKindss kinds)
      ∧ Ctors4WF r

/-- `native_parts::struct_rec_ty_r` refines `structRecTyR`
(`NativeParts.lean:349-366`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def StructRecTyRRefines : Prop :=
  ∀ (t : name.Name) (lps : alloc.vec.Vec name.Name) (elim : name.Name)
    (large : Bool) (n_p n_idx : Std.U64) (tty : expr.Expr)
    (ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × alloc.vec.Vec Std.U64))
    (o : Option expr.Expr),
    NameWF t → NamesWF lps → NameWF elim → ExprWF tty → Ctors4WF ctors →
    inductives.native_parts.struct_rec_ty_r t lps elim large n_p n_idx tty ctors
        = ok o →
    o.map absExpr = ConLeche.structRecTyR (absName t) (absNames lps) (absName elim)
        large n_p.val n_idx.val (absExpr tty) (absCtors4 ctors)
      ∧ ∀ e, o = some e → ExprWF e

/-- `native_parts::struct_rec_rhs_r` refines `structRecRhsR`
(`NativeParts.lean:368-388`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def StructRecRhsRRefines : Prop :=
  ∀ (t : name.Name) (lps : alloc.vec.Vec name.Name) (elim : name.Name)
    (large : Bool) (n_p n_idx : Std.U64) (tty : expr.Expr)
    (ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × alloc.vec.Vec Std.U64))
    (rec_c : name.Name) (rlvls : alloc.vec.Vec level.Level) (j : Std.U64)
    (o : Option expr.Expr),
    NameWF t → NamesWF lps → NameWF elim → ExprWF tty → Ctors4WF ctors →
    NameWF rec_c → LevelsWF rlvls →
    inductives.native_parts.struct_rec_rhs_r t lps elim large n_p n_idx tty ctors
        rec_c rlvls j = ok o →
    o.map absExpr = ConLeche.structRecRhsR (absName t) (absNames lps) (absName elim)
        large n_p.val n_idx.val (absExpr tty) (absCtors4 ctors) (absName rec_c)
        (absLevels rlvls) j.val
      ∧ ∀ e, o = some e → ExprWF e

/-- `native_parts::native_rules_ok` refines `nativeRulesOk`
(`NativeParts.lean:460-470`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def NativeRulesOkRefines : Prop :=
  ∀ (rec_c : name.Name) (rlvls : alloc.vec.Vec level.Level)
    (pw : prop_when.PropWhen) (n_p n : Std.U64)
    (cs : alloc.vec.Vec (env.ConstantVal × Std.U64))
    (kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind))
    (rhss : alloc.vec.Vec expr.Expr) (rec_ty : expr.Expr) (b : Bool),
    NameWF rec_c → LevelsWF rlvls → PropWhenWF pw →
    (∀ c ∈ cs.val, ConstantValWF c.1) → ExprsWF rhss → ExprWF rec_ty →
    inductives.native_parts.native_rules_ok rec_c rlvls pw n_p n cs kinds rhss
        rec_ty = ok b →
    b = ConLeche.nativeRulesOk (absName rec_c) (absLevels rlvls) (absPropWhen pw)
      n_p.val n.val (IndAbs.absCtors cs) (IndAbs.absKindss kinds) (absExprs rhss)
      (absExpr rec_ty)

/-- `native_parts::native_rec_lps_ok` refines `nativeRecLpsOk`
(`NativeParts.lean:558-560`).  **Owned by `Refine/IndNativeParts.lean`.** -/
def NativeRecLpsOkRefines : Prop :=
  ∀ (p : inductives.sum_parts.InductiveShape) (b : Bool),
    IndAbs.InductiveShapeWF p →
    inductives.native_parts.native_rec_lps_ok p = ok b →
    b = ConLeche.nativeRecLpsOk (IndAbs.absInductiveShape p)

/-- `checker_base::open_pis_at_fvars_f` refines `openPisAtFvars`
(`CheckerBase.lean:111-118`; the port runs the accumulating `*F` member, equal
to the spec by con-leche's own lemma).  **Owned by the checker-base tier**
(`kernel/checker_base.rs`, task #27). -/
def OpenPisAtFvarsFRefines : Prop :=
  ∀ (n : Std.U64) (e : expr.Expr) (i : Std.U64)
    (o : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
    ExprWF e → kernel.checker_base.open_pis_at_fvars_f n e i = ok o →
    o.map (fun q => (absExprs q.1, absExpr q.2))
        = ConLeche.openPisAtFvars n.val (absExpr e) i.val
      ∧ ∀ q, o = some q → ExprsWF q.1 ∧ ExprWF q.2

/-- `checker_base::check_constant_val` refines `checkConstantValF`
(`DeclCheck.lean:464`).  **Owned by the checker-base tier**
(`kernel/checker_base.rs`, task #27). -/
def CheckConstantValRefines : Prop :=
  ∀ (st st' : cached.state_c.CState) (fe : fenv.FEnv) (cv cv' : env.ConstantVal),
    StateWF st → FEnvWF fe → ConstantValWF cv →
    kernel.checker_base.check_constant_val mode st fe cv = ok (.Ok cv', st') →
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.checkConstantValF (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
            lfe (absConstantVal cv)).run lst = .ok (absConstantVal cv', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv'

/-- `sum_install::check_sum_ind` refines `checkSumIndF`
(`SumInstallF.lean:33-44`) at **any** implementation of the `CapsOf`
dictionary whose `caps_of` refines the Lean closure the cited code passes.
**Owned by `Refine/IndSumInstall.lean`.** -/
def CheckSumIndRefines : Prop :=
  ∀ {C : Type} (inst : inductives.sum_install.CapsOf C) (d : C)
    (capsOf : ConLeche.InductiveShape → ConLeche.IndCaps),
    (∀ p c, IndAbs.InductiveShapeWF p → inst.caps_of d p = ok c →
      absIndCaps c = capsOf (IndAbs.absInductiveShape p) ∧ IndCapsWF c) →
    ∀ (st st' : cached.state_c.CState) (fe : fenv.FEnv)
      (p : inductives.sum_parts.InductiveShape)
      (r : fenv.FEnv × env.ConstantVal × inductives.sum_parts.InductiveShape),
      StateWF st → FEnvWF fe → IndAbs.InductiveShapeWF p →
      inductives.sum_install.check_sum_ind inst mode st fe p d = ok (.Ok r, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst' lfe',
          (ConLeche.checkSumIndF (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
              lfe (IndAbs.absInductiveShape p) capsOf).run lst
            = .ok ((lfe', absConstantVal r.2.1,
                IndAbs.absInductiveShape r.2.2), lst')
          ∧ StateRel st' lst' ∧ FEnvRel r.1 lfe' ∧ StateWF st' ∧ FEnvWF r.1
          ∧ ConstantValWF r.2.1 ∧ IndAbs.InductiveShapeWF r.2.2

/-- `sum_install::check_sum_ctors` refines `checkSumCtorsF`
(`SumInstallF.lean:131-141`) at its entry reading — index `0`, both
accumulators empty, which is the only one `check_native_pass_ctors` spells.
**Owned by `Refine/IndSumInstall.lean`.** -/
def CheckSumCtorsRefines : Prop :=
  ∀ (st st' : cached.state_c.CState) (fe0 fe : fenv.FEnv) (t : name.Name)
    (lps : alloc.vec.Vec name.Name) (n_p n_idx : Std.U64) (res_sort : level.Level)
    (is_prop large : Bool) (cv_ta : env.ConstantVal)
    (cs : alloc.vec.Vec (env.ConstantVal × Std.U64))
    (r : (alloc.vec.Vec (env.ConstantVal × Std.U64))
      × (alloc.vec.Vec (alloc.vec.Vec level.Level))),
    StateWF st → FEnvWF fe0 → FEnvWF fe → NameWF t → NamesWF lps →
    LevelWF res_sort → ConstantValWF cv_ta → (∀ c ∈ cs.val, ConstantValWF c.1) →
    inductives.sum_install.check_sum_ctors mode st fe0 fe t lps n_p n_idx res_sort
        is_prop large cv_ta cs 0#usize
        (alloc.vec.Vec.new (env.ConstantVal × Std.U64))
        (alloc.vec.Vec.new (alloc.vec.Vec level.Level)) = ok (.Ok r, st') →
    ∀ lst lfe0 lfe, StateRel st lst → FEnvRel fe0 lfe0 → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.checkSumCtorsF (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
            lfe0 lfe (absName t) (absNames lps) n_p.val n_idx.val
            (absLevel res_sort) is_prop large (absConstantVal cv_ta)
            (IndAbs.absCtors cs)).run lst
          = .ok ((IndAbs.absCtors r.1, IndAbs.absLevelss r.2), lst')
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ (∀ c ∈ r.1.val, ConstantValWF c.1) ∧ (∀ us ∈ r.2.val, LevelsWF us)

/-- `sum_install::check_struct_field_sorts_i` refines `checkStructFieldSortsIF`
(`SumInstallF.lean:46-64`).  **Owned by `Refine/IndSumInstall.lean`.** -/
def CheckStructFieldSortsIRefines : Prop :=
  ∀ (st st' : cached.state_c.CState) (fe : fenv.FEnv) (is_prop large : Bool)
    (s : level.Level) (n_p : Std.U64) (fvs idx_args : alloc.vec.Vec expr.Expr)
    (j : Std.U64) (r : alloc.vec.Vec level.Level),
    StateWF st → FEnvWF fe → LevelWF s → ExprsWF fvs → ExprsWF idx_args →
    inductives.sum_install.check_struct_field_sorts_i mode st fe is_prop large s
        n_p fvs idx_args j = ok (.Ok r, st') →
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.checkStructFieldSortsIF
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe is_prop large
            (absLevel s) n_p.val (absExprs fvs) (absExprs idx_args) j.val).run lst
          = .ok (absLevels r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ LevelsWF r

/-- `sum_install::cons_sum_ctors` refines `consSumCtorsF`
(`SumInstallF.lean:143-145`), from index `i`.
**Owned by `Refine/IndSumInstall.lean`.** -/
def ConsSumCtorsRefines : Prop :=
  ∀ (n_p : Std.U64) (cs : alloc.vec.Vec (env.ConstantVal × Std.U64))
    (i : Std.Usize) (fe fe' : fenv.FEnv) (lfe : ConLeche.FEnv),
    FEnvWF fe → (∀ c ∈ cs.val, ConstantValWF c.1) → FEnvRel fe lfe →
    inductives.sum_install.cons_sum_ctors n_p cs i fe = ok fe' →
    FEnvRel fe' (ConLeche.consSumCtorsF n_p.val ((IndAbs.absCtors cs).drop i.val) lfe)
      ∧ FEnvWF fe'

/-- `sum_install::sum_rules` refines `sumRules` at the index's `find?`
(`SumInstall.lean:281-290`).  **Owned by `Refine/IndSumInstall.lean`.** -/
def SumRulesRefines : Prop :=
  ∀ (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (rec_name : name.Name)
    (n_p m_i r_p : Std.U64) (rec_ty : expr.Expr)
    (cs : alloc.vec.Vec (env.ConstantVal × Std.U64))
    (rhss : alloc.vec.Vec expr.Expr) (r : alloc.vec.Vec env.RecRule),
    FEnvRel fe lfe → FEnvWF fe → NameWF rec_name → ExprWF rec_ty →
    (∀ c ∈ cs.val, ConstantValWF c.1) → ExprsWF rhss →
    inductives.sum_install.sum_rules fe rec_name n_p m_i r_p rec_ty cs rhss = ok r →
    absRecRules r = ConLeche.sumRules lfe.find? (absName rec_name) n_p.val m_i.val
        r_p.val (absExpr rec_ty) (IndAbs.absCtors cs) (absExprs rhss)
      ∧ RecRulesWF r

end Ingredients

/-! ## The capability record (`NativeInstall.lean:57-140`) -/

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:59-98` — `native_caps_at`
refines `nativeCapsAt`: at a one-constructor block the η / unit-like / rule-K
record at the given `is_rec` verdict, at any other block the default one.
The port reads `p.ctors.len() == 1` and indexes, where con-leche matches
`| [c] =>`; the two meet at `IndAbs.absCtors`. -/
theorem native_caps_at_refines {p : inductives.sum_parts.InductiveShape}
    {is_rec : Bool} {c : env.IndCaps} (hp : IndAbs.InductiveShapeWF p)
    (h : inductives.native_install.native_caps_at p is_rec = ok c) :
    absIndCaps c = ConLeche.nativeCapsAt (IndAbs.absInductiveShape p) is_rec
      ∧ IndCapsWF c := by
  rw [inductives.native_install.native_caps_at] at h
  split at h
  · -- the one-constructor arm: the two `n_idx == 0` tests, the field count,
    -- `name::dup` and `level::zeroness_of`, against the cited record literal
    sorry
  · -- any other block: the default record
    rename_i hlen
    have hne : p.ctors.val.length ≠ 1 := by
      have := alloc.vec.Vec.len_val p.ctors; scalar_tac
    have habs : ConLeche.nativeCapsAt (IndAbs.absInductiveShape p) is_rec
        = ({} : ConLeche.IndCaps) := by
      rw [ConLeche.nativeCapsAt]
      rcases hl : (IndAbs.absInductiveShape p).ctors with _ | ⟨a, rest⟩
      · rfl
      · rcases rest with _ | ⟨b, bs⟩
        · exfalso
          apply hne
          have hone : (IndAbs.absInductiveShape p).ctors.length = 1 := by rw [hl]; simp
          simpa [IndAbs.absInductiveShape, IndAbs.absCtors] using hone
        · rfl
    rw [habs]
    exact ⟨Env.ind_caps_default_refines h, Env.ind_caps_default_wf h⟩

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:59-98` — **the dictionary
refinement**: `NativeCapsAt { is_rec }`'s `caps_of` is the closure
`fun p₁ => nativeCapsAt p₁ isRec` that `checkSumIndF` takes.  This is exactly
the hypothesis `CheckSumIndRefines` asks for, and `check_native_pass_former`
below is its one consumer. -/
theorem caps_of_refines {is_rec : Bool}
    {p : inductives.sum_parts.InductiveShape} {c : env.IndCaps}
    (hp : IndAbs.InductiveShapeWF p)
    (h : (inductives.native_install.NativeCapsAt.Insts.Con_ron_coreKernelInductivesSum_installCapsOf).caps_of
        { is_rec } p = ok c) :
    absIndCaps c
        = (fun p₁ => ConLeche.nativeCapsAt p₁ is_rec) (IndAbs.absInductiveShape p)
      ∧ IndCapsWF c :=
  native_caps_at_refines hp h

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:100-103` —
`kinds_any_rec_from` refines the inner
`ks.any fun k => k == .recursive || k == .reflexive`, from index `i`. -/
theorem kinds_any_rec_from_refines
    {ks : alloc.vec.Vec inductives.native_parts.RecFieldKind} {i : Std.Usize}
    {b : Bool} (hbeq : RecFieldKindBeqRefines)
    (h : inductives.native_install.kinds_any_rec_from ks i = ok b) :
    b = ((IndAbs.absRecFieldKinds ks).drop i.val).any
      (fun k => k == .recursive || k == .reflexive) := by
  generalize hd : ks.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.native_install.kinds_any_rec_from] at h
    split at h
    · rename_i hge
      have hnil : (IndAbs.absRecFieldKinds ks).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [IndAbs.absRecFieldKinds, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : i.val < ks.val.length := by
        have := alloc.vec.Vec.len_val ks; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ks i hlt')
      subst hyv
      have hlt2 : i.val < (IndAbs.absRecFieldKinds ks).length := by
        simpa [IndAbs.absRecFieldKinds] using hlt'
      have hcons : (IndAbs.absRecFieldKinds ks).drop i.val
          = IndAbs.absRecFieldKind ks.val[i.val]
              :: (IndAbs.absRecFieldKinds ks).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [IndAbs.absRecFieldKinds]
      rw [hcons, List.any_cons]
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := hbeq _ _ _ hb1
      split at h
      · rename_i hr
        rw [hb1v] at hr
        have heq : IndAbs.absRecFieldKind ks.val[i.val]
            = ConLeche.RecFieldKind.recursive := by
          simpa [IndAbs.absRecFieldKind] using hr
        rw [← Result.ok_injective h, heq]
        simp
      · rename_i hr
        simp only [Bool.not_eq_true] at hr
        rw [hb1v] at hr
        have hne1 : IndAbs.absRecFieldKind ks.val[i.val]
            ≠ ConLeche.RecFieldKind.recursive := by
          simpa [IndAbs.absRecFieldKind] using hr
        obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
        have hb2v := hbeq _ _ _ hb2
        split at h
        · rename_i hr2
          rw [hb2v] at hr2
          have heq2 : IndAbs.absRecFieldKind ks.val[i.val]
              = ConLeche.RecFieldKind.reflexive := by
            simpa [IndAbs.absRecFieldKind] using hr2
          rw [← Result.ok_injective h, heq2]
          simp
        · rename_i hr2
          simp only [Bool.not_eq_true] at hr2
          rw [hb2v] at hr2
          have hne2 : IndAbs.absRecFieldKind ks.val[i.val]
              ≠ ConLeche.RecFieldKind.reflexive := by
            simpa [IndAbs.absRecFieldKind] using hr2
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hiv : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
          have hrec := ih (ks.length - (i.val + 1)) (by scalar_tac) (i := i2) (b := b) h
            (by rw [hiv])
          rw [hrec, hiv]
          simp [hne1, hne2]

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:100-103` —
`native_is_rec_from` refines the outer `kinds.any`, from index `j`. -/
theorem native_is_rec_from_refines
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {j : Std.Usize} {b : Bool} (hbeq : RecFieldKindBeqRefines)
    (h : inductives.native_install.native_is_rec_from kinds j = ok b) :
    b = ((IndAbs.absKindss kinds).drop j.val).any
      (fun ks => ks.any (fun k => k == .recursive || k == .reflexive)) := by
  generalize hd : kinds.length - j.val = d
  induction d using Nat.strong_induction_on generalizing j b with
  | _ d ih =>
    rw [inductives.native_install.native_is_rec_from] at h
    split at h
    · rename_i hge
      have hnil : (IndAbs.absKindss kinds).drop j.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [IndAbs.absKindss, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : j.val < kinds.val.length := by
        have := alloc.vec.Vec.len_val kinds; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec kinds j hlt')
      subst hyv
      have hlt2 : j.val < (IndAbs.absKindss kinds).length := by
        simpa [IndAbs.absKindss] using hlt'
      have hcons : (IndAbs.absKindss kinds).drop j.val
          = IndAbs.absRecFieldKinds kinds.val[j.val]
              :: (IndAbs.absKindss kinds).drop (j.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [IndAbs.absKindss]
      rw [hcons, List.any_cons]
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := kinds_any_rec_from_refines hbeq hb1
      simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hb1v
      split at h
      · rename_i hr
        rw [hb1v] at hr
        rw [← Result.ok_injective h, hr]
        simp
      · rename_i hr
        simp only [Bool.not_eq_true] at hr
        rw [hb1v] at hr
        obtain ⟨j2, hj2, h⟩ := bind_eq_ok_iff.mp h
        have hjv : j2.val = j.val + 1 := HashMap.uscalar_add_eq hj2
        have hrec := ih (kinds.length - (j.val + 1)) (by scalar_tac) (j := j2) (b := b) h
          (by rw [hjv])
        rw [hr, hrec, hjv]
        simp

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:100-103` — `native_is_rec`
refines `nativeIsRec`: some field of some constructor is recursive or
reflexive. -/
theorem native_is_rec_refines
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {b : Bool} (hbeq : RecFieldKindBeqRefines)
    (h : inductives.native_install.native_is_rec kinds = ok b) :
    b = ConLeche.nativeIsRec (IndAbs.absKindss kinds) := by
  rw [inductives.native_install.native_is_rec] at h
  have := native_is_rec_from_refines hbeq h
  simpa [ConLeche.nativeIsRec] using this

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:105-108` — `native_caps`
refines `nativeCaps`: the record at the classified kinds. -/
theorem native_caps_refines {p : inductives.native_parts.NativeParts}
    {c : env.IndCaps} (hbeq : RecFieldKindBeqRefines)
    (hp : IndAbs.NativePartsWF p)
    (h : inductives.native_install.native_caps p = ok c) :
    absIndCaps c = ConLeche.nativeCaps (IndAbs.absNativeParts p) ∧ IndCapsWF c := by
  rw [inductives.native_install.native_caps] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := native_caps_at_refines hp h
  refine ⟨?_, hwf⟩
  rw [habs, native_is_rec_refines hbeq hb, ConLeche.nativeCaps]
  rfl

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:110-128` —
`dom_mentions_from` refines `(cbs.drop nP).any fun b => b.1.mentionsConst T`,
from index `i`. -/
theorem dom_mentions_from_refines {t : name.Name}
    {cbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {i : Std.Usize} {b : Bool}
    (hmc : MentionsConstRefines) (ht : NameWF t) (hcbs : ExprOps.BindersWF cbs)
    (h : inductives.native_install.dom_mentions_from t cbs i = ok b) :
    b = ((ExprOps.absBinders cbs).drop i.val).any
      (fun p => p.1.mentionsConst (absName t)) := by
  generalize hd : cbs.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.native_install.dom_mentions_from] at h
    split at h
    · rename_i hge
      have hnil : (ExprOps.absBinders cbs).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [ExprOps.absBinders, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : i.val < cbs.val.length := by
        have := alloc.vec.Vec.len_val cbs; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cbs i hlt')
      subst hyv
      have hlt2 : i.val < (ExprOps.absBinders cbs).length := by
        simpa [ExprOps.absBinders] using hlt'
      have hcons : (ExprOps.absBinders cbs).drop i.val
          = (absExpr cbs.val[i.val].1, absBinderMeta cbs.val[i.val].2)
              :: (ExprOps.absBinders cbs).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [ExprOps.absBinders]
      rw [hcons, List.any_cons]
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hew : ExprWF cbs.val[i.val].1 := (hcbs _ (List.getElem_mem hlt')).1
      have hb1v := hmc _ _ _ ht hew hb1
      split at h
      · rename_i hr
        rw [hb1v] at hr
        rw [← Result.ok_injective h, hr]
        simp
      · rename_i hr
        simp only [Bool.not_eq_true] at hr
        rw [hb1v] at hr
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hrec := ih (cbs.length - (i.val + 1)) (by scalar_tac) (i := i2) (b := b) h
          (by rw [hiv])
        rw [hr, hrec, hiv]
        simp

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:110-128` — `native_raw_rec`
refines `nativeRawRec`: **the syntactic reading of `is_rec`**, read only where
the record depends on it — one constructor — as `nativeCapsAt` does. -/
theorem native_raw_rec_refines {p : inductives.native_parts.NativeParts}
    {b : Bool} (hmc : MentionsConstRefines) (hp : IndAbs.NativePartsWF p)
    (h : inductives.native_install.native_raw_rec p = ok b) :
    b = ConLeche.nativeRawRec (IndAbs.absNativeParts p) := by
  -- the `len == 1` / `| [c] =>` meeting point, `expr_ops::strip_pis`, then
  -- `dom_mentions_from_refines` at the `nP` cursor
  sorry

/-! ## `Expr.mentionsFvar` and its memoized walk
(`NativeInstall.lean:139-141`, `:214-257`, `:379-386`) -/

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:139-141` —
`leaves_any_from` refines `e.fvarLeaves.any fun l => l.1 == q`, from index
`i`. -/
theorem leaves_any_from_refines
    {leaves : alloc.vec.Vec (Std.U64 × expr.Expr)} {q : Std.U64} {i : Std.Usize}
    {b : Bool} (h : inductives.native_install.leaves_any_from leaves q i = ok b) :
    b = ((ExprOps.absLeaves leaves).drop i.val).any (fun l => l.1 == q.val) := by
  generalize hd : leaves.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.native_install.leaves_any_from] at h
    split at h
    · rename_i hge
      have hnil : (ExprOps.absLeaves leaves).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [ExprOps.absLeaves, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : i.val < leaves.val.length := by
        have := alloc.vec.Vec.len_val leaves; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec leaves i hlt')
      subst hyv
      have hlt2 : i.val < (ExprOps.absLeaves leaves).length := by
        simpa [ExprOps.absLeaves] using hlt'
      rcases hpe : leaves.val[i.val] with ⟨u, ex⟩
      have hcons : (ExprOps.absLeaves leaves).drop i.val
          = (u.val, absExpr ex) :: (ExprOps.absLeaves leaves).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [ExprOps.absLeaves, hpe]
      rw [hcons, List.any_cons]
      simp only [alloc.vec.Vec.index_slice_index, hy, hpe, bind_tc_ok] at h
      simp at h
      split at h
      · rename_i hr
        rw [← Result.ok_injective h]
        have hq : u.val = q.val := by scalar_tac
        simp [hq]
      · rename_i hr
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hrec := ih (leaves.length - (i.val + 1)) (by scalar_tac) (i := i2)
          (b := b) h (by rw [hiv])
        have hne : ¬ (u.val = q.val) := by scalar_tac
        rw [hrec, hiv]
        simp [hne]

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:139-141` —
`mentions_fvar_spec` refines **the logical `Expr.mentionsFvar`**: the leaf
list, scanned. -/
theorem mentions_fvar_spec_refines {q : Std.U64} {e : expr.Expr} {b : Bool}
    (he : ExprWF e)
    (h : inductives.native_install.mentions_fvar_spec q e = ok b) :
    b = (absExpr e).mentionsFvar q.val := by
  rw [inductives.native_install.mentions_fvar_spec] at h
  obtain ⟨leaves, hl, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, -⟩ := ExprOps.fvar_leaves_refines he hl
  have hany := leaves_any_from_refines h
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hany
  rw [hany, habs, ConLeche.Expr.mentionsFvar]

/-- The memo's `Q` for this walk: "every recorded answer is the real one",
con-leche's `MentionsFvarMemoInv` (`NativeInstall.lean:190-212`) on the port's
table. -/
def MFQ (q : Nat) : ConLeche.Expr → Bool → Prop :=
  fun k r => r = k.mentionsFvar q

/-- `struct_parts::memo_eb_get` is `HashMap.get` with a `dup` on the hit, so a
hit is a recorded answer and a miss says nothing (**to be unified into
`Refine/IndStructParts.lean`**, which owns `struct_parts`). -/
theorem memo_eb_get_hit {m : ron.hashmap.HashMap expr.Expr Bool}
    {k : expr.Expr} {r : Bool}
    (h : inductives.struct_parts.memo_eb_get m k = ok (some r)) :
    ron.hashmap.HashMap.get expr.Expr.Insts.Con_ron_coreRonHashmapHashable
      expr.Expr.Insts.Con_ron_coreRonHashmapEq2 m k = ok (some r) := by
  rw [inductives.struct_parts.memo_eb_get] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, h⟩ := h
  cases o with
  | none => simp at h
  | some r' =>
    simp only [Result.ok.injEq, Option.some.injEq] at h
    subst h
    exact hget

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:214-219` —
`mentions_fvar_ins` refines `Expr.mentionsFvarIns`: recording a correct answer
keeps the invariant (`MentionsFvarMemoInv.insert`). -/
theorem mentions_fvar_ins_pres {q : Std.U64}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {e : expr.Expr} {r : Bool}
    (hm : ExprOps.MemoInv ExprWF absExpr (MFQ q.val) memo) (he : ExprWF e)
    (hr : r = (absExpr e).mentionsFvar q.val)
    (h : inductives.native_install.mentions_fvar_ins memo e r = ok memo') :
    ExprOps.MemoInv ExprWF absExpr (MFQ q.val) memo' := by
  rw [inductives.native_install.mentions_fvar_ins] at h
  obtain ⟨ed, hed, h⟩ := bind_eq_ok_iff.mp h
  rw [Expr.dup_eq hed] at h
  obtain ⟨pr, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨oldv, mm⟩ := pr
  have hmm : mm = memo' := by simpa using h
  subst hmm
  exact ExprOps.MemoInv.set ExprOps.expr_key_exact hm he hr hins

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:221-257` —
`mentions_fvar_go` refines `Expr.mentionsFvarGo`, stated against the logical
`Expr.mentionsFvar` as con-leche's own `mentionsFvarGo_spec` is: the four leaf
arms (`bvar`/`sort`/`const`/`lit`) answer before the probe, every other node
is probed, walked and recorded.  **This walk short-circuits** (`| (true, memo)
=> (true, memo)`) and the port keeps that, so only the `Bool` and the
invariant are claimed — the memo the two branches hand back is not the same
table. -/
theorem mentions_fvar_go_refines {q : Std.U64} {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool) (r : Bool),
      ExprOps.MemoInv ExprWF absExpr (MFQ q.val) memo →
      inductives.native_install.mentions_fvar_go q memo e = ok (r, memo') →
      r = (absExpr e).mentionsFvar q.val
        ∧ ExprOps.MemoInv ExprWF absExpr (MFQ q.val) memo' := by
  -- the induction on the `ExprWF` derivation, ten arms, `MemoInv.hit` at the
  -- probe and `mentions_fvar_ins_pres` at the write-back; mutual with
  -- `mentions_fvar_node_refines`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:221-257` —
`mentions_fvar_node` refines the miss branch's inner `match e with`, split off
so the probe's borrow dies before the descent mutates the memo (task #14's
rule).  The last arm is the cited unreachable one. -/
theorem mentions_fvar_node_refines {q : Std.U64} {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool) (r : Bool),
      ExprOps.MemoInv ExprWF absExpr (MFQ q.val) memo →
      inductives.native_install.mentions_fvar_node q memo e = ok (r, memo') →
      r = (absExpr e).mentionsFvar q.val
        ∧ ExprOps.MemoInv ExprWF absExpr (MFQ q.val) memo' := by
  -- proved with `mentions_fvar_go_refines` in one mutual induction
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:379-386` — **the executed
`mentionsFvar`**: `mentions_fvar` refines the logical `Expr.mentionsFvar`,
which is the content of con-leche's `@[csimp]`
`Expr.mentionsFvar_eq_mentionsFvarFast`. -/
theorem mentions_fvar_refines {q : Std.U64} {e : expr.Expr} {b : Bool}
    (he : ExprWF e)
    (h : inductives.native_install.mentions_fvar q e = ok b) :
    b = (absExpr e).mentionsFvar q.val := by
  rw [inductives.native_install.mentions_fvar] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b0, memo'⟩ := p
  have hb : b0 = b := by simpa using h
  subst hb
  exact (mentions_fvar_go_refines he memo memo' b0 (ExprOps.new_memo_inv hnew) hgo).1

/-! ## The kinds re-checked on the annotated constructors
(`NativeInstall.lean:388-445` / `NativeInstallF.lean:22-69`) -/

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:29`,`:37`,`:53` —
`all_resolve_from` refines `es.all (w.resolve fe₀)` at `StructWalkers.plain`,
from index `i`. -/
theorem all_resolve_from_refines {fe0 : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {es : alloc.vec.Vec expr.Expr} {i : Std.Usize} {b : Bool}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hrel : FEnvRel fe0 lfe0) (hfe : FEnvWF fe0) (hes : ExprsWF es)
    (h : inductives.native_install.all_resolve_from fe0 es i = ok b) :
    b = ((absExprs es).drop i.val).all (fun e => e.constsResolveF lfe0) := by
  generalize hd : es.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.native_install.all_resolve_from] at h
    split at h
    · rename_i hge
      have hnil : (absExprs es).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absExprs, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : i.val < es.val.length := by
        have := alloc.vec.Vec.len_val es; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec es i hlt')
      subst hyv
      have hew : ExprWF es.val[i.val] := hes _ (List.getElem_mem hlt')
      have hlt2 : i.val < (absExprs es).length := by simpa [absExprs] using hlt'
      have hcons : (absExprs es).drop i.val
          = absExpr es.val[i.val] :: (absExprs es).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absExprs]
      rw [hcons, List.all_cons]
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := hres fe0 lfe0 _ b1 hrel hfe hew hb1
      split at h
      · rename_i hr
        rw [hb1v] at hr
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hrec := ih (es.length - (i.val + 1)) (by scalar_tac) (i := i2) (b := b) h
          (by rw [hiv])
        rw [hrec, hiv, hr]
        simp
      · rename_i hr
        simp only [Bool.not_eq_true] at hr
        rw [hb1v] at hr
        rw [← Result.ok_injective h, hr]
        simp

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:49` —
`all_annots_resolve_from` refines
`afvs.all (fun a => w.resolve fe₀ a.fvarTypeD)`, from index `i`. -/
theorem all_annots_resolve_from_refines {fe0 : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {fvs : alloc.vec.Vec expr.Expr} {i : Std.Usize} {b : Bool}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hrel : FEnvRel fe0 lfe0) (hfe : FEnvWF fe0) (hfvs : ExprsWF fvs)
    (h : inductives.native_install.all_annots_resolve_from fe0 fvs i = ok b) :
    b = ((absExprs fvs).drop i.val).all
      (fun a => a.fvarTypeD.constsResolveF lfe0) := by
  generalize hd : fvs.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.native_install.all_annots_resolve_from] at h
    split at h
    · rename_i hge
      have hnil : (absExprs fvs).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absExprs, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : i.val < fvs.val.length := by
        have := alloc.vec.Vec.len_val fvs; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec fvs i hlt')
      subst hyv
      have hew : ExprWF fvs.val[i.val] := hfvs _ (List.getElem_mem hlt')
      have hlt2 : i.val < (absExprs fvs).length := by simpa [absExprs] using hlt'
      have hcons : (absExprs fvs).drop i.val
          = absExpr fvs.val[i.val] :: (absExprs fvs).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absExprs]
      rw [hcons, List.all_cons]
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨dom, hdom, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hdabs, hdwf⟩ := ExprOps.fvar_type_d_refines hew hdom
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := hres fe0 lfe0 dom b1 hrel hfe hdwf hb1
      rw [hdabs] at hb1v
      split at h
      · rename_i hr
        rw [hb1v] at hr
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hrec := ih (fvs.length - (i.val + 1)) (by scalar_tac) (i := i2) (b := b) h
          (by rw [hiv])
        rw [hrec, hiv, hr]
        simp
      · rename_i hr
        simp only [Bool.not_eq_true] at hr
        rw [hb1v] at hr
        rw [← Result.ok_injective h, hr]
        simp

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:38`,`:54` —
`no_later_mentions_from` refines
`!(xFvs.drop (i+1)).any (fun y => y.fvarTypeD.mentionsFvar q)`, from index `i`
(the port's `i` is the cited `i + 1`, so the two read the same suffix). -/
theorem no_later_mentions_from_refines {x_fvs : alloc.vec.Vec expr.Expr}
    {q : Std.U64} {i : Std.Usize} {b : Bool} (hx : ExprsWF x_fvs)
    (h : inductives.native_install.no_later_mentions_from x_fvs q i = ok b) :
    b = !((absExprs x_fvs).drop i.val).any
      (fun y => y.fvarTypeD.mentionsFvar q.val) := by
  generalize hd : x_fvs.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.native_install.no_later_mentions_from] at h
    split at h
    · rename_i hge
      have hnil : (absExprs x_fvs).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absExprs, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : i.val < x_fvs.val.length := by
        have := alloc.vec.Vec.len_val x_fvs; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec x_fvs i hlt')
      subst hyv
      have hew : ExprWF x_fvs.val[i.val] := hx _ (List.getElem_mem hlt')
      have hlt2 : i.val < (absExprs x_fvs).length := by simpa [absExprs] using hlt'
      have hcons : (absExprs x_fvs).drop i.val
          = absExpr x_fvs.val[i.val] :: (absExprs x_fvs).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absExprs]
      rw [hcons, List.any_cons]
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨dom, hdom, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hdabs, hdwf⟩ := ExprOps.fvar_type_d_refines hew hdom
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := mentions_fvar_refines hdwf hb1
      rw [hdabs] at hb1v
      split at h
      · rename_i hr
        rw [hb1v] at hr
        rw [← Result.ok_injective h, hr]
        simp
      · rename_i hr
        simp only [Bool.not_eq_true] at hr
        rw [hb1v] at hr
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hrec := ih (x_fvs.length - (i.val + 1)) (by scalar_tac) (i := i2) (b := b) h
          (by rw [hiv])
        rw [hrec, hiv, hr]
        simp

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:33-39` —
`native_opened_recursive` refines the `.recursive` arm of `nativeOpenedOkF`'s
per-field match: the field's domain is the family at the opened parameter
variables followed by `nIdx` index expressions resolving in `env₀`, and the
variable occurs in no later field's domain nor in the residual. -/
theorem native_opened_recursive_refines {fe0 : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {t : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_idx i : Std.U64}
    {fvs_p x_fvs : alloc.vec.Vec expr.Expr} {xrest dom : expr.Expr} {b : Bool}
    (hres : StructInstall.ConstsResolveFFastRefines) (hpo : ParamsOfRefines)
    (hrel : FEnvRel fe0 lfe0) (hfe : FEnvWF fe0) (ht : NameWF t)
    (hlps : NamesWF lps) (hfp : ExprsWF fvs_p) (hx : ExprsWF x_fvs)
    (hxr : ExprWF xrest) (hdom : ExprWF dom)
    (h : inductives.native_install.native_opened_recursive fe0 t lps n_p n_idx
        fvs_p x_fvs xrest i dom = ok b) :
    b = ((absExpr dom).getAppFn
          == ConLeche.Expr.const (absName t) ((absNames lps).map .param) &&
        ((absExpr dom).getAppArgs.take n_p.val == absExprs fvs_p) &&
        ((absExpr dom).getAppArgs.length == n_p.val + n_idx.val) &&
        ((absExpr dom).getAppArgs.drop n_p.val).all
          (fun e => e.constsResolveF lfe0) &&
        !((absExprs x_fvs).drop (i.val + 1)).any
          (fun y => y.fvarTypeD.mentionsFvar (n_p.val + i.val)) &&
        !(absExpr xrest).mentionsFvar (n_p.val + i.val)) := by
  -- `get_app_fn`, `expr::mk_const`/`params_of`, `expr::beq`, `take_exprs`,
  -- `exprs_beq`, the length test, `core_k::drop_exprs`, `all_resolve_from`,
  -- `no_later_mentions_from`, `mentions_fvar`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:40-56` —
`native_opened_reflexive` refines the `.reflexive` arm: the field's own
telescope, opened at variables at the field's depth, its domains resolving in
`env₀`, its body the family at the parameter variables. -/
theorem native_opened_reflexive_refines {fe0 : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {t : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_idx i : Std.U64}
    {fvs_p x_fvs : alloc.vec.Vec expr.Expr} {xrest dom : expr.Expr} {b : Bool}
    (hres : StructInstall.ConstsResolveFFastRefines) (hpo : ParamsOfRefines)
    (hpb : PiBindersRefines) (hop : OpenPisAtFvarsFRefines)
    (hrel : FEnvRel fe0 lfe0) (hfe : FEnvWF fe0) (ht : NameWF t)
    (hlps : NamesWF lps) (hfp : ExprsWF fvs_p) (hx : ExprsWF x_fvs)
    (hxr : ExprWF xrest) (hdom : ExprWF dom)
    (h : inductives.native_install.native_opened_reflexive fe0 t lps n_p n_idx
        fvs_p x_fvs xrest i dom = ok b) :
    b = (match ConLeche.openPisAtFvars ((absExpr dom).piBinders).1.length
            (absExpr dom) (n_p.val + i.val) with
        | some (afvs, body) =>
          (afvs.length != 0) &&
          afvs.all (fun a => a.fvarTypeD.constsResolveF lfe0) &&
          (body.getAppFn
            == ConLeche.Expr.const (absName t) ((absNames lps).map .param)) &&
          (body.getAppArgs.take n_p.val == absExprs fvs_p) &&
          (body.getAppArgs.length == n_p.val + n_idx.val) &&
          (body.getAppArgs.drop n_p.val).all (fun e => e.constsResolveF lfe0) &&
          !((absExprs x_fvs).drop (i.val + 1)).any
            (fun y => y.fvarTypeD.mentionsFvar (n_p.val + i.val)) &&
          !(absExpr xrest).mentionsFvar (n_p.val + i.val)
        | none => false) := by
  -- `pi_binders`, `open_pis_at_fvars_f`, `all_annots_resolve_from`, then the
  -- `.recursive` arm's chain
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:30-57` —
`native_opened_fields_from` refines `nativeOpenedOkF`'s `(List.range nF).all`,
from index `i`: one clause per field kind. -/
theorem native_opened_fields_from_refines {fe0 : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {t : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_idx n_f i : Std.U64}
    {fvs_p x_fvs : alloc.vec.Vec expr.Expr} {xrest : expr.Expr}
    {ks : alloc.vec.Vec inductives.native_parts.RecFieldKind} {b : Bool}
    (hres : StructInstall.ConstsResolveFFastRefines) (hpo : ParamsOfRefines)
    (hpb : PiBindersRefines) (hop : OpenPisAtFvarsFRefines)
    (hkg : KindGetDRefines)
    (hrel : FEnvRel fe0 lfe0) (hfe : FEnvWF fe0) (ht : NameWF t)
    (hlps : NamesWF lps) (hfp : ExprsWF fvs_p) (hx : ExprsWF x_fvs)
    (hxr : ExprWF xrest)
    (h : inductives.native_install.native_opened_fields_from fe0 t lps n_p n_idx
        fvs_p x_fvs xrest ks n_f i = ok b) :
    b = (List.range' i.val (n_f.val - i.val)).all (fun j =>
      match (absExprs x_fvs)[j]?, (IndAbs.absRecFieldKinds ks).getD j .ordinary with
      | some x, .ordinary => x.fvarTypeD.constsResolveF lfe0
      | some x, .recursive =>
        (x.fvarTypeD.getAppFn
          == ConLeche.Expr.const (absName t) ((absNames lps).map .param)) &&
        (x.fvarTypeD.getAppArgs.take n_p.val == absExprs fvs_p) &&
        (x.fvarTypeD.getAppArgs.length == n_p.val + n_idx.val) &&
        (x.fvarTypeD.getAppArgs.drop n_p.val).all (fun e => e.constsResolveF lfe0) &&
        !((absExprs x_fvs).drop (j + 1)).any
          (fun y => y.fvarTypeD.mentionsFvar (n_p.val + j)) &&
        !(absExpr xrest).mentionsFvar (n_p.val + j)
      | some x, .reflexive =>
        (match ConLeche.openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD
            (n_p.val + j) with
        | some (afvs, body) =>
          (afvs.length != 0) &&
          afvs.all (fun a => a.fvarTypeD.constsResolveF lfe0) &&
          (body.getAppFn
            == ConLeche.Expr.const (absName t) ((absNames lps).map .param)) &&
          (body.getAppArgs.take n_p.val == absExprs fvs_p) &&
          (body.getAppArgs.length == n_p.val + n_idx.val) &&
          (body.getAppArgs.drop n_p.val).all (fun e => e.constsResolveF lfe0) &&
          !((absExprs x_fvs).drop (j + 1)).any
            (fun y => y.fvarTypeD.mentionsFvar (n_p.val + j)) &&
          !(absExpr xrest).mentionsFvar (n_p.val + j)
        | none => false)
      | _, _ => false) := by
  -- the `i`-counting recursion, `n_f - i` decreasing, one kind arm a step
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59` — `native_opened_ok`
refines `nativeOpenedOkF` at `StructWalkers.plain`: the constructor type
opened at the parameters and then at the fields, the residual's index
expressions resolving, and the per-field clauses. -/
theorem native_opened_ok_refines {fe0 : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {t : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_idx n_f : Std.U64}
    {cty : expr.Expr} {ks : alloc.vec.Vec inductives.native_parts.RecFieldKind}
    {b : Bool}
    (hres : StructInstall.ConstsResolveFFastRefines) (hpo : ParamsOfRefines)
    (hpb : PiBindersRefines) (hop : OpenPisAtFvarsFRefines)
    (hkg : KindGetDRefines)
    (hrel : FEnvRel fe0 lfe0) (hfe : FEnvWF fe0) (ht : NameWF t)
    (hlps : NamesWF lps) (hcty : ExprWF cty)
    (h : inductives.native_install.native_opened_ok fe0 t lps n_p n_idx cty n_f ks
        = ok b) :
    b = ConLeche.nativeOpenedOkF ConLeche.StructWalkers.plain lfe0 (absName t)
      (absNames lps) n_p.val n_idx.val (absExpr cty) n_f.val
      (IndAbs.absRecFieldKinds ks) := by
  -- the two `open_pis_at_fvars_f`s, `all_resolve_from` on the residual, then
  -- `native_opened_fields_from_refines` at `i = 0`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:62-69` —
`native_fields_ok_from` refines `nativeFieldsOkF`'s
`(List.range ctorsA.length).all`, from index `j`. -/
theorem native_fields_ok_from_refines {fe0 : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {t : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {j : Std.Usize} {b : Bool}
    (hres : StructInstall.ConstsResolveFFastRefines) (hpo : ParamsOfRefines)
    (hpb : PiBindersRefines) (hop : OpenPisAtFvarsFRefines)
    (hkg : KindGetDRefines)
    (hrel : FEnvRel fe0 lfe0) (hfe : FEnvWF fe0) (ht : NameWF t)
    (hlps : NamesWF lps) (hca : ∀ c ∈ ctors_a.val, ConstantValWF c.1)
    (h : inductives.native_install.native_fields_ok_from fe0 t lps n_p n_idx
        ctors_a kinds j = ok b) :
    b = (List.range' j.val ((IndAbs.absCtors ctors_a).length - j.val)).all (fun k =>
      match (IndAbs.absCtors ctors_a)[k]?, (IndAbs.absKindss kinds)[k]? with
      | some cA, some ks =>
        (ks.length == cA.2) &&
        ConLeche.nativeOpenedOkF ConLeche.StructWalkers.plain lfe0 (absName t)
          (absNames lps) n_p.val n_idx.val cA.1.type cA.2 ks
      | _, _ => false) := by
  -- the index recursion on `ctors_a.len() - j`, one `native_opened_ok` a step
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:61-69` — `native_fields_ok`
refines `nativeFieldsOkF` at `StructWalkers.plain`: the kinds, re-checked on
every annotated constructor. -/
theorem native_fields_ok_refines {fe0 : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {t : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {b : Bool}
    (hres : StructInstall.ConstsResolveFFastRefines) (hpo : ParamsOfRefines)
    (hpb : PiBindersRefines) (hop : OpenPisAtFvarsFRefines)
    (hkg : KindGetDRefines)
    (hrel : FEnvRel fe0 lfe0) (hfe : FEnvWF fe0) (ht : NameWF t)
    (hlps : NamesWF lps) (hca : ∀ c ∈ ctors_a.val, ConstantValWF c.1)
    (h : inductives.native_install.native_fields_ok fe0 t lps n_p n_idx ctors_a
        kinds = ok b) :
    b = ConLeche.nativeFieldsOkF ConLeche.StructWalkers.plain lfe0 (absName t)
      (absNames lps) n_p.val n_idx.val (IndAbs.absCtors ctors_a)
      (IndAbs.absKindss kinds) := by
  -- the `ctorsA.length == kinds.length` test, then
  -- `native_fields_ok_from_refines` at `j = 0`
  sorry

/-! ## The recursor stage (`NativeInstall.lean:447-519` /
`NativeInstallF.lean:71-126`) -/

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:80-81`,`:104-105` —
`term_scoped` refines the scoping guard both recursor stages spell,
`e.allLevelParamsDefined lps && w.resolve fe e && e.looseBVarsBounded 0 &&
!e.hasFvar`.  Its own function because the conjunction borrows the index and
the term and both arms of the `unless` read them again (task #14's rule). -/
theorem term_scoped_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {lps : alloc.vec.Vec name.Name} {e : expr.Expr} {b : Bool}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe) (hlps : NamesWF lps) (he : ExprWF e)
    (h : inductives.native_install.term_scoped fe lps e = ok b) :
    b = ((absExpr e).allLevelParamsDefined (absNames lps)
      && (absExpr e).constsResolveF lfe && (absExpr e).looseBVarsBounded 0
      && !(absExpr e).hasFvar) := by
  rw [inductives.native_install.term_scoped] at h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
  have hb1v := ExprOps.all_level_params_defined_fast_refines hlps he hb1
  split at h
  · rename_i h1
    rw [hb1v] at h1
    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
    have hb2v := hres fe lfe e b2 hrel hfe he hb2
    split at h
    · rename_i h2
      rw [hb2v] at h2
      obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
      have hb3v := ExprOps.loose_bvars_bounded_refines he hb3
      simp only [show (0#u64 : Std.U64).val = 0 from rfl] at hb3v
      split at h
      · rename_i h3
        rw [hb3v] at h3
        obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
        have hb4v := ExprOps.has_fvar_refines he hb4
        rw [← Result.ok_injective h, hb4v, h1, h2, h3]
        simp
      · rename_i h3
        simp only [Bool.not_eq_true] at h3
        rw [hb3v] at h3
        rw [← Result.ok_injective h, h1, h2, h3]
        simp
    · rename_i h2
      simp only [Bool.not_eq_true] at h2
      rw [hb2v] at h2
      rw [← Result.ok_injective h, h1, h2]
      simp
  · rename_i h1
    simp only [Bool.not_eq_true] at h1
    rw [hb1v] at h1
    rw [← Result.ok_injective h, h1]
    simp

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:71-85` —
`check_native_rules` refines `checkNativeRulesF` at `StructWalkers.plain`: the
generated rules for constructors `j, j+1, …` (`k` of them), each scoped at the
environment holding the recursor's constant.  The port accumulates on the way
*in* where con-leche conses on the way *out* (task #13's pattern 3), so the
statement carries the accumulator in front. -/
theorem check_native_rules_refines {fe_r : fenv.FEnv} {lfe_r : ConLeche.FEnv}
    {rlps lps : alloc.vec.Vec name.Name} {t elim rec_c : name.Name} {large : Bool}
    {n_p n_idx k j : Std.U64} {tty : expr.Expr}
    {ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × alloc.vec.Vec Std.U64)}
    {rlvls : alloc.vec.Vec level.Level} {out r : alloc.vec.Vec expr.Expr}
    (hres : StructInstall.ConstsResolveFFastRefines) (hrhs : StructRecRhsRRefines)
    (hrel : FEnvRel fe_r lfe_r) (hfe : FEnvWF fe_r) (hrlps : NamesWF rlps)
    (ht : NameWF t) (hlps : NamesWF lps) (helim : NameWF elim) (htty : ExprWF tty)
    (hctors : Ctors4WF ctors) (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls)
    (hout : ExprsWF out)
    (h : inductives.native_install.check_native_rules fe_r rlps t lps elim large
        n_p n_idx tty ctors rec_c rlvls k j out = ok (.Ok r)) :
    (∀ lst, (ConLeche.checkNativeRulesF (m := ConLeche.Cached.CheckCM)
        ConLeche.StructWalkers.plain lfe_r (absNames rlps) (absName t)
        (absNames lps) (absName elim) large n_p.val n_idx.val (absExpr tty)
        (absCtors4 ctors) (absName rec_c) (absLevels rlvls) k.val j.val).run lst
      = .ok ((absExprs r).drop (absExprs out).length, lst))
    ∧ absExprs r = absExprs out ++ (absExprs r).drop (absExprs out).length
    ∧ ExprsWF r := by
  -- the `k`-counting recursion, one `struct_rec_rhs_r` and one `term_scoped`
  -- a step
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:111-115` —
`check_native_rec_rules` refines the tail of `checkNativeRecF`: the annotated
recursor constant, the **ruleless** provisioning of the index the rules are
scoped at (`fe.push (.recInfo cvRa p.majorIdx p.rulePrefix [])`) and the
rules.  This is where the module note's second `fenv::dup` happens. -/
theorem check_native_rec_rules_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {p : inductives.native_parts.NativeParts} {cv_ta : env.ConstantVal}
    {ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × alloc.vec.Vec Std.U64)}
    {rec_ty : expr.Expr} {r : env.ConstantVal × alloc.vec.Vec expr.Expr}
    (hres : StructInstall.ConstsResolveFFastRefines) (hrhs : StructRecRhsRRefines)
    (hpo : ParamsOfRefines)
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe) (hp : IndAbs.NativePartsWF p)
    (hcv : ConstantValWF cv_ta) (hctors : Ctors4WF ctors) (hrt : ExprWF rec_ty)
    (h : inductives.native_install.check_native_rec_rules fe p cv_ta ctors rec_ty
        = ok (.Ok r)) :
    ∃ lrhss,
      (∀ lst, (ConLeche.checkNativeRulesF (m := ConLeche.Cached.CheckCM)
          ConLeche.StructWalkers.plain
          (lfe.push (.recInfo ⟨absName p.shape.cv_r.name,
              absNames p.shape.cv_r.level_params, absExpr rec_ty⟩
            (IndAbs.absNativeParts p).majorIdx (IndAbs.absNativeParts p).rulePrefix
            []))
          (absNames p.shape.cv_r.level_params) (absName p.shape.cv_t.name)
          (absNames p.shape.cv_t.level_params) (absName p.shape.elim)
          p.shape.large p.shape.n_p.val p.shape.n_idx.val (absExpr cv_ta.ty)
          (absCtors4 ctors) (absName p.shape.cv_r.name)
          ((absNames p.shape.cv_r.level_params).map .param)
          (absCtors4 ctors).length 0).run lst = .ok (lrhss, lst))
      ∧ absConstantVal r.1 = ⟨absName p.shape.cv_r.name,
          absNames p.shape.cv_r.level_params, absExpr rec_ty⟩
      ∧ absExprs r.2 = lrhss ∧ ConstantValWF r.1 ∧ ExprsWF r.2 := by
  -- `fenv::push`, `major_idx`/`rule_prefix`, `params_of`, and
  -- `check_native_rules_refines` at `j = 0`, `out = []`; blocked on the same
  -- `fenv::dup` bridge as `check_native_pass_former` (module note)
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115` —
`check_native_rec` refines `checkNativeRecF` at `StructWalkers.plain`:
**stage 3, the recursor generated and compared**.  The recursor PIN
(con-leche task #220) is thrown here: a record naming something other than the
generated `T.rec`, or contradicting it in its level parameters or its
argument sums and rules, is INVALID INPUT. -/
theorem check_native_rec_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {p : inductives.native_parts.NativeParts} {cv_ta : env.ConstantVal}
    {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {r : env.ConstantVal × alloc.vec.Vec expr.Expr}
    (hres : StructInstall.ConstsResolveFFastRefines) (hrhs : StructRecRhsRRefines)
    (hty : StructRecTyRRefines) (hc4 : NativeCtors4Refines)
    (hlpsok : NativeRecLpsOkRefines) (hcvr : CheckConstantValRefines mode)
    (hpo : ParamsOfRefines)
    (hst : StateWF st) (hfe : FEnvWF fe) (hp : IndAbs.NativePartsWF p)
    (hcvta : ConstantValWF cv_ta) (hca : ∀ c ∈ ctors_a.val, ConstantValWF c.1)
    (h : inductives.native_install.check_native_rec mode st fe p cv_ta ctors_a
        = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.checkNativeRecF (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
            ConLeche.StructWalkers.plain lfe (IndAbs.absNativeParts p)
            (absConstantVal cv_ta) (IndAbs.absCtors ctors_a)).run lst
          = .ok ((absConstantVal r.1, absExprs r.2), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF r.1 ∧ ExprsWF r.2 := by
  -- the three pin guards (`name::mk_str`/`name::beq`, `native_rec_lps_ok`,
  -- `rec_pinned`), `check_constant_val`, `native_ctors4`, `struct_rec_ty_r`,
  -- `term_scoped`, `ops_infer`, `ops_ensure_sort`, `ops_defeq`, then
  -- `check_native_rec_rules_refines`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstallF.lean:117-126` —
`check_native_table` refines `checkNativeTableF` at `StructWalkers.plain`:
**stage 4, the projection table** at a structure-like block — one
constructor, no index — at the tagged tower's projection offset `1`; nothing
at any other block. -/
theorem check_native_table_refines {p : inductives.native_parts.NativeParts}
    {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {sortss : alloc.vec.Vec (alloc.vec.Vec level.Level)} {fe fe' : fenv.FEnv}
    {lfe : ConLeche.FEnv}
    (hbodies : StructInstall.StructProjBodiesRefines)
    (hres : StructInstall.ConstsResolveFFastRefines) (hg : StructProjGuardsRefines)
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe) (hp : IndAbs.NativePartsWF p)
    (hca : ∀ c ∈ ctors_a.val, ConstantValWF c.1)
    (hss : ∀ us ∈ sortss.val, LevelsWF us)
    (h : inductives.native_install.check_native_table p ctors_a sortss fe
        = ok (.Ok fe')) :
    ∃ lfe',
      (∀ lst, (ConLeche.checkNativeTableF (m := ConLeche.Cached.CheckCM)
          ConLeche.StructWalkers.plain (IndAbs.absNativeParts p)
          (IndAbs.absCtors ctors_a) (IndAbs.absLevelss sortss) lfe).run lst
        = .ok (lfe', lst))
      ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  -- the two `len == 1` tests against `| [cA], [sorts] =>`, the `n_idx == 0`
  -- guard, `struct_proj_guards` and
  -- `StructInstall.check_struct_proj_table_refines`
  sorry

/-! ## The pass (`NativeInstall.lean:521-574` / `CheckerC.lean:177-190`) -/

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:539-554` —
`rec_ctor_kinds_all` refines `ctorsA.mapM (recCtorKinds T lps nP nIdx)` at the
`Option` monad, as an index recursion accumulating on the way in: the first
`none` is the whole `none`. -/
theorem rec_ctor_kinds_all_refines {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)} {i : Std.Usize}
    {out : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {res : Option (alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind))}
    (hrck : RecCtorKindsRefines) (ht : NameWF t) (hlps : NamesWF lps)
    (hca : ∀ c ∈ ctors_a.val, ConstantValWF c.1)
    (h : inductives.native_install.rec_ctor_kinds_all t lps n_p n_idx ctors_a i out
        = ok res) :
    res.map IndAbs.absKindss
      = (((IndAbs.absCtors ctors_a).drop i.val).mapM
          (ConLeche.recCtorKinds (absName t) (absNames lps) n_p.val n_idx.val)).map
            (fun ks => IndAbs.absKindss out ++ ks) := by
  -- the index recursion on `ctors_a.len() - i`, the accumulator in front
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:539-554` —
`kind_list_any_from` refines the inner `ks.any (· == k)`, from index `i`. -/
theorem kind_list_any_from_refines
    {ks : alloc.vec.Vec inductives.native_parts.RecFieldKind}
    {k : inductives.native_parts.RecFieldKind} {i : Std.Usize} {b : Bool}
    (hbeq : RecFieldKindBeqRefines)
    (h : inductives.native_install.kind_list_any_from ks k i = ok b) :
    b = ((IndAbs.absRecFieldKinds ks).drop i.val).any
      (fun x => x == IndAbs.absRecFieldKind k) := by
  generalize hd : ks.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.native_install.kind_list_any_from] at h
    split at h
    · rename_i hge
      have hnil : (IndAbs.absRecFieldKinds ks).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [IndAbs.absRecFieldKinds, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : i.val < ks.val.length := by
        have := alloc.vec.Vec.len_val ks; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ks i hlt')
      subst hyv
      have hlt2 : i.val < (IndAbs.absRecFieldKinds ks).length := by
        simpa [IndAbs.absRecFieldKinds] using hlt'
      have hcons : (IndAbs.absRecFieldKinds ks).drop i.val
          = IndAbs.absRecFieldKind ks.val[i.val]
              :: (IndAbs.absRecFieldKinds ks).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [IndAbs.absRecFieldKinds]
      rw [hcons, List.any_cons]
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := hbeq _ _ _ hb1
      split at h
      · rename_i hr
        rw [hb1v] at hr
        have heq : IndAbs.absRecFieldKind ks.val[i.val] = IndAbs.absRecFieldKind k := by
          simpa using hr
        rw [← Result.ok_injective h, heq]
        simp
      · rename_i hr
        simp only [Bool.not_eq_true] at hr
        rw [hb1v] at hr
        have hne : IndAbs.absRecFieldKind ks.val[i.val] ≠ IndAbs.absRecFieldKind k := by
          simpa using hr
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hrec := ih (ks.length - (i.val + 1)) (by scalar_tac) (i := i2) (b := b) h
          (by rw [hiv])
        rw [hrec, hiv]
        simp [hne]

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:539-554` — `kinds_any_from`
refines `kinds.any (fun ks => ks.any (· == k))`, from index `j`. -/
theorem kinds_any_from_refines
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {k : inductives.native_parts.RecFieldKind} {j : Std.Usize} {b : Bool}
    (hbeq : RecFieldKindBeqRefines)
    (h : inductives.native_install.kinds_any_from kinds k j = ok b) :
    b = ((IndAbs.absKindss kinds).drop j.val).any
      (fun ks => ks.any (fun x => x == IndAbs.absRecFieldKind k)) := by
  generalize hd : kinds.length - j.val = d
  induction d using Nat.strong_induction_on generalizing j b with
  | _ d ih =>
    rw [inductives.native_install.kinds_any_from] at h
    split at h
    · rename_i hge
      have hnil : (IndAbs.absKindss kinds).drop j.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [IndAbs.absKindss, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : j.val < kinds.val.length := by
        have := alloc.vec.Vec.len_val kinds; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec kinds j hlt')
      subst hyv
      have hlt2 : j.val < (IndAbs.absKindss kinds).length := by
        simpa [IndAbs.absKindss] using hlt'
      have hcons : (IndAbs.absKindss kinds).drop j.val
          = IndAbs.absRecFieldKinds kinds.val[j.val]
              :: (IndAbs.absKindss kinds).drop (j.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [IndAbs.absKindss]
      rw [hcons, List.any_cons]
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := kind_list_any_from_refines hbeq hb1
      simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hb1v
      split at h
      · rename_i hr
        rw [hb1v] at hr
        rw [← Result.ok_injective h, hr]
        simp
      · rename_i hr
        simp only [Bool.not_eq_true] at hr
        rw [hb1v] at hr
        obtain ⟨j2, hj2, h⟩ := bind_eq_ok_iff.mp h
        have hjv : j2.val = j.val + 1 := HashMap.uscalar_add_eq hj2
        have hrec := ih (kinds.length - (j.val + 1)) (by scalar_tac) (j := j2) (b := b) h
          (by rw [hjv])
        rw [hr, hrec, hjv]
        simp

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:539-554` —
`classify_fix_kinds` refines `classifyFixKinds`: **the fields' kinds,
classified at install** on the stored constructors; a negative kind is
`.invalid`, an unsupported one `.notImplemented`. -/
theorem classify_fix_kinds_refines {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    (hrck : RecCtorKindsRefines) (hbeq : RecFieldKindBeqRefines)
    (ht : NameWF t) (hlps : NamesWF lps)
    (hca : ∀ c ∈ ctors_a.val, ConstantValWF c.1)
    (h : inductives.native_install.classify_fix_kinds t lps n_p n_idx ctors_a
        = ok (.Ok kinds)) :
    ∀ lst, (ConLeche.classifyFixKinds (m := ConLeche.Cached.CheckCM) (absName t)
        (absNames lps) n_p.val n_idx.val (IndAbs.absCtors ctors_a)).run lst
      = .ok (IndAbs.absKindss kinds, lst) := by
  -- `rec_ctor_kinds_all_refines` at `i = 0`, then the two `kinds_any_from`
  -- guards
  sorry

/-! ### The pass's two halves, named

con-leche writes both inline inside `checkNativePassS`
(`Cached/CheckerC.lean:177-190`); the port splits them so that the driver's
`flushC` lands exactly between them. -/

/-- `ConLeche/Cached/CheckerC.lean:178-181` — the **former's half** of one
pass: `checkSumIndF` at the capability record the verdict names, and the
record the classification must reproduce. -/
def checkNativePassFormerF (mode : ConLeche.CheckMode) (fe : ConLeche.FEnv)
    (p₀ : ConLeche.NativeParts) (isRec : Bool) :
    ConLeche.Cached.CheckCM
      (ConLeche.FEnv × ConLeche.ConstantVal × ConLeche.InductiveShape
        × ConLeche.IndCaps) := do
  let (fe₁, cvTa, p₁) ← ConLeche.checkSumIndF (ConLeche.Cached.sharedOpsC mode fe) fe
    p₀.toInductiveShape (fun p₁ => ConLeche.nativeCapsAt p₁ isRec)
  pure (fe₁, cvTa, p₁, ConLeche.nativeCapsAt p₁ isRec)

/-- `ConLeche/Cached/CheckerC.lean:182-190` — the **constructors' half** of one
pass: the constructors at the former's index, the kinds classified on those
constructors, the record completed with them, and the verdict's
confirmation. -/
def checkNativePassCtorsF (mode : ConLeche.CheckMode) (fe₁ : ConLeche.FEnv)
    (cvTa : ConLeche.ConstantVal) (p₁ : ConLeche.InductiveShape)
    (p₀ : ConLeche.NativeParts) (expected : ConLeche.IndCaps) :
    ConLeche.Cached.CheckCM (ConLeche.NativePass ConLeche.FEnv × Bool) := do
  let pC := p₀.complete p₁
  let (ctorsA, sortss) ← ConLeche.checkSumCtorsF
    (ConLeche.Cached.sharedOpsC mode fe₁) fe₁ fe₁ pC.cvT.name pC.cvT.levelParams
    pC.nP pC.nIdx pC.resSort pC.isProp pC.large cvTa pC.ctors
  let kinds ← ConLeche.classifyFixKinds (m := ConLeche.Cached.CheckCM) pC.cvT.name
    pC.cvT.levelParams pC.nP pC.nIdx ctorsA
  let p := pC.withKinds kinds
  pure (⟨fe₁, cvTa, p, ctorsA, sortss⟩, ConLeche.nativeCaps p == expected)

/-- **The cited driver is the two halves around `flushC`.**  The identity that
justifies the split (`Refine/StateC.lean`'s `eqvStep` is the pattern); the two
sides differ only by `bind_assoc` across the do-block's join points. -/
theorem checkNativePassS_eq (mode : ConLeche.CheckMode) (fe : ConLeche.FEnv)
    (p₀ : ConLeche.NativeParts) (isRec : Bool) :
    ConLeche.Cached.checkNativePassS mode fe p₀ isRec
      = (do
          let q ← checkNativePassFormerF mode fe p₀ isRec
          ConLeche.Cached.flushC
          checkNativePassCtorsF mode q.1 q.2.1 q.2.2.1 p₀ q.2.2.2) := by
  -- the do-block's join points, `bind_assoc` in `StateT CState CheckM`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:178-181` — `check_native_pass_former`
refines `checkNativePassFormerF`.  The pre-block index is copied
(`fenv::dup`, the module note) and the shape duplicated
(`sum_parts::inductive_shape_dup`, an identity), so the Lean argument is the
unchanged one; `caps_of_refines` is what discharges `checkSumIndF`'s closure
argument. -/
theorem check_native_pass_former_refines {mode : env.CheckMode}
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {p0 : inductives.native_parts.NativeParts} {is_rec : Bool}
    {r : fenv.FEnv × env.ConstantVal × inductives.sum_parts.InductiveShape
      × env.IndCaps}
    (hsi : CheckSumIndRefines mode)
    (hst : StateWF st) (hfe : FEnvWF fe) (hp0 : IndAbs.NativePartsWF p0)
    (h : inductives.native_install.check_native_pass_former mode st fe p0 is_rec
        = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe₁,
        (checkNativePassFormerF (absMode mode) lfe (IndAbs.absNativeParts p0)
            is_rec).run lst
          = .ok ((lfe₁, absConstantVal r.2.1, IndAbs.absInductiveShape r.2.2.1,
              absIndCaps r.2.2.2), lst')
        ∧ StateRel st' lst' ∧ FEnvRel r.1 lfe₁ ∧ StateWF st' ∧ FEnvWF r.1
        ∧ ConstantValWF r.2.1 ∧ IndAbs.InductiveShapeWF r.2.2.1
        ∧ IndCapsWF r.2.2.2 := by
  -- `inductive_shape_dup`, `check_sum_ind` at the `NativeCapsAt` dictionary
  -- (`caps_of_refines`), then `native_caps_at`; blocked on the `fenv::dup`
  -- bridge `FEnvRel fe lfe → FEnvRel (dup fe) lfe` (module note)
  sorry

/-- `ConLeche/Cached/CheckerC.lean:182-190` — `check_native_pass_ctors`
refines `checkNativePassCtorsF`: the constructors at the former's index, the
kinds, the completed record, and the `env::ind_caps_beq` verdict. -/
theorem check_native_pass_ctors_refines {mode : env.CheckMode}
    {st st' : cached.state_c.CState} {fe1 : fenv.FEnv} {cv_ta : env.ConstantVal}
    {p1 : inductives.sum_parts.InductiveShape}
    {p0 : inductives.native_parts.NativeParts} {expected : env.IndCaps}
    {q : inductives.native_install.NativePass × Bool}
    (hcc : CheckSumCtorsRefines mode) (hcomp : CompleteRefines)
    (hwk : WithKindsRefines) (hrck : RecCtorKindsRefines)
    (hbeq : RecFieldKindBeqRefines)
    (hst : StateWF st) (hfe : FEnvWF fe1) (hcv : ConstantValWF cv_ta)
    (hp1 : IndAbs.InductiveShapeWF p1) (hp0 : IndAbs.NativePartsWF p0)
    (hexp : IndCapsWF expected)
    (h : inductives.native_install.check_native_pass_ctors mode st fe1 cv_ta p1 p0
        expected = ok (.Ok q, st')) :
    ∀ lst lfe₁, StateRel st lst → FEnvRel fe1 lfe₁ →
      ∃ lst' lq,
        (checkNativePassCtorsF (absMode mode) lfe₁ (absConstantVal cv_ta)
            (IndAbs.absInductiveShape p1) (IndAbs.absNativeParts p0)
            (absIndCaps expected)).run lst = .ok ((lq, q.2), lst')
        ∧ StateRel st' lst' ∧ IndAbs.NativePassRel q.1 lq ∧ StateWF st'
        ∧ IndAbs.NativePassWF q.1 := by
  -- `complete`, `check_sum_ctors`, `classify_fix_kinds`, `with_kinds`,
  -- `native_caps` and `env::ind_caps_beq`'s exactness
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:556-574` — the cited
`checkNativePass` at the index: the two halves composed **without** a flush.
Dead in the shipped binary (the module note). -/
def checkNativePassI (mode : ConLeche.CheckMode) (fe : ConLeche.FEnv)
    (p₀ : ConLeche.NativeParts) (isRec : Bool) :
    ConLeche.Cached.CheckCM (ConLeche.NativePass ConLeche.FEnv × Bool) := do
  let q ← checkNativePassFormerF mode fe p₀ isRec
  checkNativePassCtorsF mode q.1 q.2.1 q.2.2.1 p₀ q.2.2.2

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:556-574` —
`check_native_pass` refines `checkNativePassI`. -/
theorem check_native_pass_refines {mode : env.CheckMode}
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {p0 : inductives.native_parts.NativeParts} {is_rec : Bool}
    {q : inductives.native_install.NativePass × Bool}
    (hsi : CheckSumIndRefines mode) (hcc : CheckSumCtorsRefines mode)
    (hcomp : CompleteRefines) (hwk : WithKindsRefines)
    (hrck : RecCtorKindsRefines) (hbeq : RecFieldKindBeqRefines)
    (hst : StateWF st) (hfe : FEnvWF fe) (hp0 : IndAbs.NativePartsWF p0)
    (h : inductives.native_install.check_native_pass mode st fe p0 is_rec
        = ok (.Ok q, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lq,
        (checkNativePassI (absMode mode) lfe (IndAbs.absNativeParts p0)
            is_rec).run lst = .ok ((lq, q.2), lst')
        ∧ StateRel st' lst' ∧ IndAbs.NativePassRel q.1 lq ∧ StateWF st'
        ∧ IndAbs.NativePassWF q.1 := by
  intro lst lfe hrel hfer
  rw [inductives.native_install.check_native_pass] at h
  obtain ⟨pq, hformer, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨res, st1⟩ := pq
  cases res with
  | Err err => simp at h
  | Ok r =>
    obtain ⟨lst1, lfe₁, hrun1, hrel1, hfrel1, hwf1, hfwf1, hcvwf, hiswf, hcapwf⟩ :=
      check_native_pass_former_refines hsi hst hfe hp0 hformer lst lfe hrel hfer
    obtain ⟨lst', lq, hrun2, hrel2, hqrel, hwf2, hqwf⟩ :=
      check_native_pass_ctors_refines hcc hcomp hwk hrck hbeq hwf1 hfwf1 hcvwf
        hiswf hp0 hcapwf h lst1 lfe₁ hrel1 hfrel1
    refine ⟨lst', lq, ?_, hrel2, hqrel, hwf2, hqwf⟩
    rw [checkNativePassI]
    simp only [StateT.run_bind, hrun1]
    exact hrun2

/-! ## The tail (`NativeInstall.lean:576-611` / `CheckerC.lean:192-215`) -/

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:576-611` —
`elim_restriction_violated` refines **official's
`elim_only_at_universe_zero`**: a large eliminator on a block whose sort may
be `Prop` is `.invalid` at two or more constructors.  Its own function because
the cited `if`'s condition borrows the record and both arms read it again
(task #14's rule). -/
theorem elim_restriction_violated_refines
    {p : inductives.native_parts.NativeParts} {b : Bool}
    (h : inductives.native_install.elim_restriction_violated p = ok b) :
    b = ((IndAbs.absNativeParts p).large
      && !(IndAbs.absNativeParts p).resSort.isNeverZero
      && decide (2 ≤ (IndAbs.absNativeParts p).ctors.length)) := by
  rw [inductives.native_install.elim_restriction_violated] at h
  simp only [IndAbs.absNativeParts, IndAbs.absInductiveShape]
  split at h
  · rename_i hlarge
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := Level.is_never_zero_refines' p.shape.res_sort b1 hb1
    split at h
    · rename_i hnz
      rw [hb1v] at hnz
      rw [← Result.ok_injective h, hnz]
      simp
    · rename_i hnz
      simp only [Bool.not_eq_true] at hnz
      rw [hb1v] at hnz
      rw [← Result.ok_injective h, hlarge, hnz]
      have hlv := alloc.vec.Vec.len_val p.shape.ctors
      simp only [Bool.not_false, Bool.true_and, IndAbs.absCtors, List.length_map,
        decide_eq_decide]
      constructor
      · intro hh; scalar_tac
      · intro hh; scalar_tac
  · rename_i hlarge
    simp only [Bool.not_eq_true] at hlarge
    rw [← Result.ok_injective h, hlarge]
    simp

/-! ### The tail's three parts, named

con-leche writes all three inline inside `checkNativeTailS`
(`Cached/CheckerC.lean:192-215`); the port splits them so that the driver's
`flushC` lands after `consSumCtorsF` and before `checkNativeRecF`, exactly
where the cited one is. -/

/-- `ConLeche/Cached/CheckerC.lean:194-207` — the **guard half** of the tail:
the elimination restriction, the index binders' sorts (read, not compared),
the kinds re-checked, and the stream's rules against the generated ones. -/
def checkNativeTailGuardsF (mode : ConLeche.CheckMode) (fe : ConLeche.FEnv)
    (q : ConLeche.NativePass ConLeche.FEnv) : ConLeche.Cached.CheckCM Unit := do
  let p := q.p
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  let tq ← ConLeche.unwrapOr (ConLeche.openPisAtFvars (p.nP + p.nIdx) q.cvTa.type 0)
    (.internal "direct rec: type former telescope")
  let _isorts ← ConLeche.checkStructFieldSortsIF
    (ConLeche.Cached.sharedOpsC mode q.env₁) q.env₁ true false p.resSort p.nP
    (tq.1.drop p.nP) [] p.nIdx
  unless ConLeche.nativeFieldsOkF ConLeche.Cached.structWalkersC fe p.cvT.name
      p.cvT.levelParams p.nP p.nIdx q.ctorsA p.kinds do
    throw (.internal "direct rec: field kinds")
  unless ConLeche.nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP
      p.ctors.length q.ctorsA p.kinds p.rhss p.cvR.type do
    throw (.invalid "direct rec: recursor rules are not the generated ones")

/-- `ConLeche/Cached/CheckerC.lean:209-215` — the **installing tail**: the
recursor generated, its rules stored, and the projection table. -/
def checkNativeInstallF (mode : ConLeche.CheckMode) (fe₂ : ConLeche.FEnv)
    (p : ConLeche.NativeParts) (cvTa : ConLeche.ConstantVal)
    (ctorsA : List (ConLeche.ConstantVal × Nat))
    (sortss : List (List ConLeche.Level)) :
    ConLeche.Cached.CheckCM ConLeche.FEnv := do
  let (cvRa, rhss) ← ConLeche.checkNativeRecF
    (ConLeche.Cached.sharedOpsC mode fe₂) ConLeche.Cached.structWalkersC fe₂ p cvTa
    ctorsA
  ConLeche.checkNativeTableF (m := ConLeche.Cached.CheckCM)
    ConLeche.Cached.structWalkersC p ctorsA sortss
    (fe₂.push (.recInfo cvRa p.majorIdx p.rulePrefix
      (ConLeche.sumRules fe₂.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type
        ctorsA rhss)))

/-- **The cited driver is the three parts around `flushC`.**  `consSumCtorsF`
is pure, so it may sit on either side; the flush is between it and
`checkNativeRecF`, exactly where `check_native_cons` and
`check_native_install` put it. -/
theorem checkNativeTailS_eq (mode : ConLeche.CheckMode) (fe : ConLeche.FEnv)
    (q : ConLeche.NativePass ConLeche.FEnv) :
    ConLeche.Cached.checkNativeTailS mode fe q
      = (do
          checkNativeTailGuardsF mode fe q
          let fe₂ := ConLeche.consSumCtorsF q.p.nP q.ctorsA q.env₁
          ConLeche.Cached.flushC
          checkNativeInstallF mode fe₂ q.p q.cvTa q.ctorsA q.sortss) := by
  -- the do-block's join points, `bind_assoc` in `StateT CState CheckM`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:194-207` — `check_native_tail_guards`
refines `checkNativeTailGuardsF`.  `structWalkersC` is `StructWalkers.plain`
by con-leche's own `structWalkersC_eq_plain`, which is what lets
`native_fields_ok_refines` be read at the driver's record. -/
theorem check_native_tail_guards_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {q : inductives.native_install.NativePass}
    (hres : StructInstall.ConstsResolveFFastRefines) (hpo : ParamsOfRefines)
    (hpb : PiBindersRefines) (hop : OpenPisAtFvarsFRefines)
    (hkg : KindGetDRefines) (hro : NativeRulesOkRefines)
    (hfs : CheckStructFieldSortsIRefines mode)
    (hst : StateWF st) (hfe : FEnvWF fe) (hq : IndAbs.NativePassWF q)
    (h : inductives.native_install.check_native_tail_guards mode st fe q
        = ok (.Ok (), st')) :
    ∀ lst lfe lq, StateRel st lst → FEnvRel fe lfe →
      IndAbs.NativePassRel q lq →
      ∃ lst',
        (checkNativeTailGuardsF (absMode mode) lfe lq).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `elim_restriction_violated`, `open_pis_at_fvars_f`, `core_k::drop_exprs`,
  -- `check_struct_field_sorts_i`, `native_fields_ok` (through
  -- `ConLeche.structWalkersC_eq_plain`), `params_of`, `prop_when::never`,
  -- `native_rules_ok`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:208` — `check_native_cons` refines
`let fe₂ := consSumCtorsF p.nP q.ctorsA q.env₁`: the pass's record taken apart
and the constructors consed onto the former's index.  Its own function because
the cached driver's `flushC` sits between it and the recursor's stage. -/
theorem check_native_cons_refines {q : inductives.native_install.NativePass}
    {r : fenv.FEnv × inductives.native_parts.NativeParts × env.ConstantVal
      × (alloc.vec.Vec (env.ConstantVal × Std.U64))
      × (alloc.vec.Vec (alloc.vec.Vec level.Level))}
    (hcons : ConsSumCtorsRefines) (hq : IndAbs.NativePassWF q)
    (h : inductives.native_install.check_native_cons q = ok r) :
    ∀ lq, IndAbs.NativePassRel q lq →
      FEnvRel r.1 (ConLeche.consSumCtorsF lq.p.nP lq.ctorsA lq.env₁)
      ∧ IndAbs.absNativeParts r.2.1 = lq.p
      ∧ absConstantVal r.2.2.1 = lq.cvTa
      ∧ IndAbs.absCtors r.2.2.2.1 = lq.ctorsA
      ∧ IndAbs.absLevelss r.2.2.2.2 = lq.sortss
      ∧ FEnvWF r.1 ∧ IndAbs.NativePartsWF r.2.1 ∧ ConstantValWF r.2.2.1
      ∧ (∀ c ∈ r.2.2.2.1.val, ConstantValWF c.1)
      ∧ (∀ us ∈ r.2.2.2.2.val, LevelsWF us) := by
  intro lq hrel
  obtain ⟨henv, hcvta, hp, hctors, hss⟩ := hrel
  obtain ⟨hwenv, hwcv, hwp, hwctors, hwss⟩ := hq
  rw [inductives.native_install.check_native_cons] at h
  obtain ⟨fe2, hfe2, h⟩ := bind_eq_ok_iff.mp h
  have hrq : r = (fe2, q.p, q.cv_ta, q.ctors_a, q.sortss) :=
    (Result.ok_injective h).symm
  subst hrq
  obtain ⟨hrel2, hwf2⟩ := hcons q.p.shape.n_p q.ctors_a 0#usize q.env1 fe2 lq.env₁
    hwenv hwctors henv hfe2
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hrel2
  refine ⟨?_, hp, hcvta, hctors, hss, hwf2, hwp, hwcv, hwctors, hwss⟩
  have hnp : q.p.shape.n_p.val = lq.p.nP := by
    rw [← hp]; rfl
  rw [← hctors, ← hnp]
  exact hrel2

/-- `ConLeche/Cached/CheckerC.lean:209-215` — `check_native_install` refines
`checkNativeInstallF`: the recursor, its stored rules, and the projection
table. -/
theorem check_native_install_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe2 fe' : fenv.FEnv}
    {p : inductives.native_parts.NativeParts} {cv_ta : env.ConstantVal}
    {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {sortss : alloc.vec.Vec (alloc.vec.Vec level.Level)}
    (hres : StructInstall.ConstsResolveFFastRefines) (hrhs : StructRecRhsRRefines)
    (hty : StructRecTyRRefines) (hc4 : NativeCtors4Refines)
    (hlpsok : NativeRecLpsOkRefines) (hcvr : CheckConstantValRefines mode)
    (hpo : ParamsOfRefines) (hsr : SumRulesRefines)
    (hbodies : StructInstall.StructProjBodiesRefines) (hg : StructProjGuardsRefines)
    (hst : StateWF st) (hfe : FEnvWF fe2) (hp : IndAbs.NativePartsWF p)
    (hcv : ConstantValWF cv_ta) (hca : ∀ c ∈ ctors_a.val, ConstantValWF c.1)
    (hss : ∀ us ∈ sortss.val, LevelsWF us)
    (h : inductives.native_install.check_native_install mode st fe2 p cv_ta ctors_a
        sortss = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst' lfe',
        (checkNativeInstallF (absMode mode) lfe (IndAbs.absNativeParts p)
            (absConstantVal cv_ta) (IndAbs.absCtors ctors_a)
            (IndAbs.absLevelss sortss)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `check_native_rec`, `major_idx`/`rule_prefix`, `sum_rules`, `fenv::push`,
  -- `check_native_table`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:576-611` — the cited
`checkNativeTail` at the index: the three parts composed **without** a flush.
Dead in the shipped binary (the module note). -/
def checkNativeTailI (mode : ConLeche.CheckMode) (fe : ConLeche.FEnv)
    (q : ConLeche.NativePass ConLeche.FEnv) :
    ConLeche.Cached.CheckCM ConLeche.FEnv := do
  checkNativeTailGuardsF mode fe q
  let fe₂ := ConLeche.consSumCtorsF q.p.nP q.ctorsA q.env₁
  checkNativeInstallF mode fe₂ q.p q.cvTa q.ctorsA q.sortss

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:576-611` —
`check_native_tail` refines `checkNativeTailI`. -/
theorem check_native_tail_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {q : inductives.native_install.NativePass}
    (hres : StructInstall.ConstsResolveFFastRefines) (hpo : ParamsOfRefines)
    (hpb : PiBindersRefines) (hop : OpenPisAtFvarsFRefines)
    (hkg : KindGetDRefines) (hro : NativeRulesOkRefines)
    (hfs : CheckStructFieldSortsIRefines mode) (hcons : ConsSumCtorsRefines)
    (hrhs : StructRecRhsRRefines) (hty : StructRecTyRRefines)
    (hc4 : NativeCtors4Refines) (hlpsok : NativeRecLpsOkRefines)
    (hcvr : CheckConstantValRefines mode) (hsr : SumRulesRefines)
    (hbodies : StructInstall.StructProjBodiesRefines) (hg : StructProjGuardsRefines)
    (hst : StateWF st) (hfe : FEnvWF fe) (hq : IndAbs.NativePassWF q)
    (h : inductives.native_install.check_native_tail mode st fe q
        = ok (.Ok fe', st')) :
    ∀ lst lfe lq, StateRel st lst → FEnvRel fe lfe → IndAbs.NativePassRel q lq →
      ∃ lst' lfe',
        (checkNativeTailI (absMode mode) lfe lq).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  intro lst lfe lq hrel hfer hqrel
  rw [inductives.native_install.check_native_tail] at h
  obtain ⟨pq, hguards, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨res, st1⟩ := pq
  cases res with
  | Err err => simp at h
  | Ok u =>
    cases u
    obtain ⟨lst1, hrun1, hrel1, hwf1⟩ :=
      check_native_tail_guards_refines hw hres hpo hpb hop hkg hro hfs hst hfe hq
        hguards lst lfe lq hrel hfer hqrel
    obtain ⟨cq, hcq, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hcrel, hcp, hccv, hcctors, hcss, hcwf, hcpwf, hccvwf, hcawf, hsswf⟩ :=
      check_native_cons_refines hcons hq hcq lq hqrel
    obtain ⟨lst', lfe', hrun2, hrel2, hfrel2, hwf2, hfwf2⟩ :=
      check_native_install_refines hw hres hrhs hty hc4 hlpsok hcvr hpo hsr hbodies
        hg hwf1 hcwf hcpwf hccvwf hcawf hsswf h lst1
        (ConLeche.consSumCtorsF lq.p.nP lq.ctorsA lq.env₁) hrel1 hcrel
    refine ⟨lst', lfe', ?_, hrel2, hfrel2, hwf2, hfwf2⟩
    rw [checkNativeTailI]
    rw [hcp, hccv, hcctors, hcss] at hrun2
    simp only [StateT.run_bind, hrun1]
    exact hrun2

/-! ## The driver (`NativeInstall.lean:613-640`) -/

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:613-640` —
`ctor_names_from` appends `cs.map (·.1.name)` from index `i` to its
accumulator (the port's pattern 3, where the cited code is a plain `map`). -/
theorem ctor_names_from_val (cs : alloc.vec.Vec (env.ConstantVal × Std.U64)) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec name.Name),
      cs.length - i.val ≤ k →
      inductives.native_install.ctor_names_from cs i out = ok v →
      v.val = out.val ++ (cs.val.drop i.val).map (fun c => c.1.name) := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [inductives.native_install.ctor_names_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [inductives.native_install.ctor_names_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ cs.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      have hlt : i.val < cs.val.length := by scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok, name_dup_eq] at h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
      have hwv : w.val = i.val + 1 := HashMap.uscalar_add_eq hw
      have hlm : i.val < (cs.val.map (fun c => c.1.name)).length := by simpa using hlt
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv]
      simp [List.drop_eq_getElem_cons hlm]

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:613-640` — `ctor_names`
refines `p₀.ctors.map (·.1.name)`, whose `Nodup` the front guard decides. -/
theorem ctor_names_refines {cs : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {v : alloc.vec.Vec name.Name}
    (h : inductives.native_install.ctor_names cs = ok v) :
    absNames v = (IndAbs.absCtors cs).map (fun c => c.1.name) := by
  rw [inductives.native_install.ctor_names] at h
  have hv := ctor_names_from_val cs cs.length 0#usize _ v (by scalar_tac) h
  simp only [alloc.vec.Vec.new, show (0#usize : Std.Usize).val = 0 from rfl,
    List.drop_zero] at hv
  rw [absNames, hv, IndAbs.absCtors]
  simp [absConstantVal]

/-- `level::name_nodup`, from index `i`, refines `List.Nodup`'s decision on the
names (`kernel/level.rs`, task #13's port of `Name.nodup`).  **To be unified
into `Refine/Level.lean`**, which owns `kernel::level`; `check_native`'s front
guard is its first consumer. -/
theorem name_nodup_from_refines {ns : alloc.vec.Vec name.Name} (hns : NamesWF ns) :
    ∀ (i : Std.Usize) (b : Bool),
      level.name_nodup_from ns i = ok b →
      b = decide ((absNames ns).drop i.val).Nodup := by
  intro i b h
  generalize hd : ns.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [level.name_nodup_from] at h
    split at h
    · rename_i hge
      have hnil : (absNames ns).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absNames, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : i.val < ns.val.length := by
        have := alloc.vec.Vec.len_val ns; scalar_tac
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ns i hlt')
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hnw : NameWF ns.val[i.val] := hns _ (List.getElem_mem hlt')
      have hb1v := Name.contains_from_refines hns hnw ns.length i2 (by scalar_tac) b1 hb1
      rw [hiv] at hb1v
      have hlt2 : i.val < (absNames ns).length := by
        simpa [absNames] using hlt'
      have hcons : (absNames ns).drop i.val
          = absName ns.val[i.val] :: (absNames ns).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absNames]
      have hmem : ((ns.val.drop (i.val + 1)).map absName)
          = (absNames ns).drop (i.val + 1) := by
        simp [absNames]
      rw [hmem] at hb1v
      simp only [hcons, List.nodup_cons]
      split at h
      · rename_i hr
        rw [hb1v] at hr
        rw [← Result.ok_injective h]
        symm
        simp only [decide_eq_false_iff_not]
        rintro ⟨hn, -⟩
        exact absurd (of_decide_eq_true hr) hn
      · rename_i hr
        simp only [Bool.not_eq_true] at hr
        rw [hb1v] at hr
        have hnot : absName ns.val[i.val] ∉ (absNames ns).drop (i.val + 1) :=
          of_decide_eq_false hr
        have hrec := ih (ns.length - (i.val + 1)) (by scalar_tac) (i := i2) (b := b) h
          (by rw [hiv])
        rw [hrec, hiv]
        simp [hnot]

/-- `level::name_nodup` at its entry (**to be unified into
`Refine/Level.lean`**). -/
theorem name_nodup_refines {ns : alloc.vec.Vec name.Name} {b : Bool}
    (hns : NamesWF ns) (h : level.name_nodup ns = ok b) :
    b = decide (absNames ns).Nodup := by
  rw [level.name_nodup] at h
  have hb := name_nodup_from_refines hns 0#usize b h
  simpa using hb

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:613-640` — the cited
`checkNative` at the index: the distinct constructor names, the pass at the
syntactic `is_rec` reading, again at the classified verdict where the reading
overshot, and the install after it — **without** the driver's three flushes.
Dead in the shipped binary (the module note). -/
def checkNativeI (mode : ConLeche.CheckMode) (fe : ConLeche.FEnv)
    (p₀ : ConLeche.NativeParts) : ConLeche.Cached.CheckCM ConLeche.FEnv := do
  unless (p₀.ctors.map (·.1.name)).Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  let (q, settled) ← checkNativePassI mode fe p₀ (ConLeche.nativeRawRec p₀)
  if settled then checkNativeTailI mode fe q
  else do
    let (q', settled') ← checkNativePassI mode fe p₀ (ConLeche.nativeIsRec q.p.kinds)
    unless settled' do
      throw (.internal "direct rec: the capability record did not settle")
    checkNativeTailI mode fe q'

/-- `ConLeche/Kernel/Inductives/NativeInstall.lean:613-640` — `check_native`
refines `checkNativeI`.  The two-pass shape is the cited one: `nativeRawRec`
is a superset of official's `is_rec`, strict exactly when a redex over the
block reduces away; there the block is passed again at the classified verdict,
which then stands. -/
theorem check_native_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {p0 : inductives.native_parts.NativeParts}
    (hsi : CheckSumIndRefines mode) (hcc : CheckSumCtorsRefines mode)
    (hcomp : CompleteRefines) (hwk : WithKindsRefines)
    (hrck : RecCtorKindsRefines) (hbeq : RecFieldKindBeqRefines)
    (hmc : MentionsConstRefines)
    (hres : StructInstall.ConstsResolveFFastRefines) (hpo : ParamsOfRefines)
    (hpb : PiBindersRefines) (hop : OpenPisAtFvarsFRefines)
    (hkg : KindGetDRefines) (hro : NativeRulesOkRefines)
    (hfs : CheckStructFieldSortsIRefines mode) (hcons : ConsSumCtorsRefines)
    (hrhs : StructRecRhsRRefines) (hty : StructRecTyRRefines)
    (hc4 : NativeCtors4Refines) (hlpsok : NativeRecLpsOkRefines)
    (hcvr : CheckConstantValRefines mode) (hsr : SumRulesRefines)
    (hbodies : StructInstall.StructProjBodiesRefines) (hg : StructProjGuardsRefines)
    (hst : StateWF st) (hfe : FEnvWF fe) (hp0 : IndAbs.NativePartsWF p0)
    (h : inductives.native_install.check_native mode st fe p0 = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (checkNativeI (absMode mode) lfe (IndAbs.absNativeParts p0)).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `ctor_names`, `name_nodup`, `native_raw_rec`, the two `check_native_pass`es
  -- and `check_native_tail`
  sorry

end ConRon.Refine.NativeInstall
