/-
# `kernel::inductives::inductives_c` refined — the two routes' drivers (task #57)

`CORE_PLAN.md` step 7, the top of the inductive tier.
`crates/con-ron-core/src/kernel/inductives/inductives_c.rs` is the *cached*
driver of each route — the stages of `ConLeche/Cached/CheckerC.lean` that the
shipped binary runs on an inductive block — and the two entry points it ends
in, `check_native_s` and `check_ind_decl_s`, are what `checker.rs`'s `.indDecl`
arm calls.  `Refine/IndSpec.lean`'s `IndRoutesSpec` is the `Prop` the checker
tier (task #56) consumes; `ind_routes_spec` at the bottom of this file produces
it.

| group | items |
|---|---|
| the modeled route | `check_ind_member_s`, `check_ind_members_s`, `provision_recs_s`, `check_ind_recs_s`, `install_proj_fn_step_s`, `install_proj_fns_s`, `check_ind_decl_struct_s`, **`check_ind_decl_s`** |
| the direct route | `check_native_pass_s`, `check_native_tail_s`, **`check_native_s`** |

## What this file is *about*: the flush policy

The cited stages "mirror their `ConLeche/Kernel/Checker.lean` counterparts
clause by clause; the differences are exactly: `flushC` at environment
transitions, `FEnv.push` maintaining the index, and *every* environment lookup
routed through the index".  The port has one spelling of the index already
(task #25's deviation 1), so what `inductives_c.rs` adds is the **flush
policy** — the one thing DESIGN.md §3.1 insists must be mirrored, because a
flush changes the memo hit/miss pattern.  Three stages were *split* in
`native_install`/`modeled` so that the flush lands exactly where the cited
`flushC` does, with one body serving both the pure and the cached spelling;
composing those halves around `Refine/StateC.lean`'s `flush_c_refines` is this
file's work, and it is why the statements below are against the `*S` drivers
rather than against the stages.

`checkIndDeclStructS` transcribes `checkIndDeclSF`'s single-type-former,
single-constructor arm, which con-leche writes inline inside a `match`; it is
an internal helper of this file only — the **entry-point** lemmas
`check_ind_decl_s_refines` and `check_native_s_refines` are stated against
con-leche's own `checkIndDeclSF`/`checkNativeS`, unmodified.

## The knot

Every lemma takes `hw : Core.Wrappers mode IndAbs.checkFuelU` — the routes
reach the core only through `sharedOpsC`, which ties `coreKnotI` at exactly
`core_k::check_fuel()` (`Refine/IndAbs.lean`).  Task #55 proves the knot's
arms; this file assumes them.

## `sorry` count

9 `sorry`s: the nine driver lemmas that reach a stage.  The two index folds
(`check_ind_members_s`, `install_proj_fns_s`) are proved from the step lemmas
above them.  Each remaining one waits on its sibling module's stage
refinement (`Refine/IndModeled.lean`, `Refine/IndNativeInstall.lean`), which is
being written concurrently.  The statements are the exact-result ones and
nothing below is weakened.  The two `#print axioms` censuses at the bottom are
machine-checked with `#guard_msgs`: `sorryAx` leaving them is the gate that
says the inductive tier is closed.
-/
import ConRon.Refine.IndSpec
import ConRon.Refine.IndStructInstall
import ConRon.Refine.IndSumParts
import ConRon.Refine.StateC

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.InductivesC

/-! ## Two abstractions this file needs (**to be unified into
`Refine/Abs.lean`**) -/

/-- `provisionRecsS`' output list: the provisional recursors, each with its two
argument sums and the stream's rules. -/
def absCheckedRecs
    (cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)) :
    List (ConLeche.ConstantVal × Nat × Nat × List ConLeche.RecRule) :=
  cs.val.map (fun c =>
    (absConstantVal c.1, c.2.1.val, c.2.2.1.val, absRecRules c.2.2.2))

/-- `CheckerC.lean:233-268` — the single-type-former, single-constructor arm of
`checkIndDeclSF`, transcribed (con-leche writes it inline inside the `match`).
An internal helper: the entry-point lemma is against `checkIndDeclSF` itself. -/
def checkIndDeclStructS (mode : ConLeche.CheckMode) (lfe : ConLeche.FEnv)
    (blockNames : List ConLeche.Name)
    (nonrecs recs : List ConLeche.ConstantInfo)
    (cvT cvC : ConLeche.ConstantVal) (nP nF : Nat) :
    ConLeche.Cached.CheckCM ConLeche.FEnv := do
  let caps ← pure (ConLeche.indBlockCapsF mode lfe cvT cvC nP nF)
  let fe₂ ← nonrecs.foldlM (ConLeche.Cached.checkIndMemberS mode blockNames caps) lfe
  let fe₃ ← ConLeche.Cached.checkIndRecsS mode blockNames fe₂ recs
  unless ConLeche.ctorResidualOkF mode fe₃ cvT.name cvC.name cvT.levelParams nP nF
      caps.eta do
    throw (.notImplemented "modeled structure: eta constructor residual")
  unless (List.range nF).all (fun j => (fe₃.find? (ConLeche.projFnName cvT.name j)).isNone) do
    throw (.invalid "projection name family taken")
  if ConLeche.ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF then
    (List.range nF).foldlM
      (ConLeche.Cached.installProjFnStepS mode cvT.name cvC.name cvT.levelParams nP nF)
      fe₃
  else pure fe₃

section Drivers

variable {mode : env.CheckMode} (hw : Core.Wrappers mode IndAbs.checkFuelU)

include hw

/-! ## The modeled route -/

/-- `ConLeche/Cached/CheckerC.lean:105-113` — `check_ind_member_s` refines
`checkIndMemberS`: **one flush entering the member's environment**, then
`checkIndMember`'s body. -/
theorem check_ind_member_s_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {caps : env.IndCaps} {fe fe' : fenv.FEnv} {ci : env.ConstantInfo}
    (hst : StateWF st) (hfe : FEnvWF fe) (hbn : NamesWF block_names)
    (hcaps : IndCapsWF caps) (hci : ConstantInfoWF ci)
    (h : inductives.inductives_c.check_ind_member_s mode st block_names caps fe ci
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkIndMemberS (absMode mode) (absNames block_names)
            (absIndCaps caps) lfe (absConstantInfo ci)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `StateC.flush_c_refines` then `IndModeled`'s `check_ind_member` stage
  sorry

/-- `ConLeche/Cached/CheckerC.lean:233-268` — `check_ind_members_s` refines
`nonrecs.foldlM (checkIndMemberS mode blockNames caps) fe`, as an index
recursion over the filtered members. -/
theorem check_ind_members_s_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {caps : env.IndCaps} {fe fe' : fenv.FEnv}
    {nonrecs : alloc.vec.Vec env.ConstantInfo} {i : Std.Usize}
    (hst : StateWF st) (hfe : FEnvWF fe) (hbn : NamesWF block_names)
    (hcaps : IndCapsWF caps) (hnr : ConstantInfosWF nonrecs)
    (h : inductives.inductives_c.check_ind_members_s mode st block_names caps fe
        nonrecs i = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (((absConstantInfos nonrecs).drop i.val).foldlM
            (ConLeche.Cached.checkIndMemberS (absMode mode) (absNames block_names)
              (absIndCaps caps)) lfe).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  generalize hd : nonrecs.length - i.val = d
  induction d using Nat.strong_induction_on generalizing st fe i with
  | _ d ih =>
    intro lst lfe hrel hfer
    rw [inductives.inductives_c.check_ind_members_s] at h
    split at h
    · -- the index is past the end: the fold is over the empty list
      rename_i hge
      have hnil : (absConstantInfos nonrecs).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absConstantInfos, List.length_map]
        scalar_tac
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lst, lfe, by
        simp only [hnil, List.foldlM_nil, StateT.run, Pure.pure, StateT.pure]
        rfl, hrel, hfer, hst, hfe⟩
    · rename_i hlt
      have hlt' : i.val < nonrecs.val.length := by
        have := alloc.vec.Vec.len_val nonrecs; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec nonrecs i hlt')
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨p, hstep, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err e => simp at h
      | Ok fe2 =>
        obtain ⟨i2, hi2, h⟩ := by simpa using bind_eq_ok_iff.mp (by simpa using h)
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hciwf : ConstantInfoWF nonrecs.val[i.val] := hnr _ (List.getElem_mem hlt')
        obtain ⟨lst1, lfe1, hrun1, hrel1, hfer1, hwf1, hfew1⟩ :=
          check_ind_member_s_refines hw hst hfe hbn hcaps hciwf hstep lst lfe hrel hfer
        obtain ⟨lst', lfe', hrunr, hrelr, hferr, hwfr, hfewr⟩ :=
          ih (nonrecs.length - i2.val) (by scalar_tac) hwf1 hfew1 h rfl lst1 lfe1
            hrel1 hfer1
        refine ⟨lst', lfe', ?_, hrelr, hferr, hwfr, hfewr⟩
        have hlt2 : i.val < (absConstantInfos nonrecs).length := by
          simpa [absConstantInfos] using hlt'
        have hcons : (absConstantInfos nonrecs).drop i.val
            = absConstantInfo nonrecs.val[i.val]
              :: (absConstantInfos nonrecs).drop i2.val := by
          rw [List.drop_eq_getElem_cons hlt2, hi2v]
          simp [absConstantInfos]
        rw [hcons, List.foldlM_cons]
        simp only [StateT.run, Bind.bind, StateT.bind, Except.bind] at hrun1 hrunr ⊢
        rw [hrun1]
        exact hrunr

/-- `ConLeche/Cached/CheckerC.lean:115-129` — `provision_recs_s` refines
`provisionRecsS`: **one flush per recursor** before its constant is checked,
then `provisionRecs`' step.  The port accumulates the checked recursors on the
way *in* where con-leche conses them on the way *out*, so the statement carries
the accumulator in front. -/
theorem provision_recs_s_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe_acc : fenv.FEnv} {recs : alloc.vec.Vec env.ConstantInfo} {i : Std.Usize}
    {out : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)}
    {q : fenv.FEnv × alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)}
    (hst : StateWF st) (hfe : FEnvWF fe_acc) (hbn : NamesWF block_names)
    (hrecs : ConstantInfosWF recs)
    (h : inductives.inductives_c.provision_recs_s mode st block_names fe_acc recs
        i out = ok (.Ok q, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe_acc lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.provisionRecsS (absMode mode) (absNames block_names) lfe
            ((absConstantInfos recs).drop i.val)).run lst
          = .ok ((lfe', absCheckedRecs q.2 |>.drop (absCheckedRecs out).length),
              lst')
        ∧ absCheckedRecs q.2 = absCheckedRecs out
            ++ (absCheckedRecs q.2).drop (absCheckedRecs out).length
        ∧ StateRel st' lst' ∧ FEnvRel q.1 lfe' ∧ StateWF st' ∧ FEnvWF q.1 := by
  -- the index recursion over `recs`, one flush plus `provision_recs_step` a step
  sorry

/-- `ConLeche/Cached/CheckerC.lean:131-151` — `check_ind_recs_s` refines
`checkIndRecsS`: **all iota-rule checks run at `envSelf`** — one flush entering
the phase, none inside the fold — and the ruled recursors are installed on the
`env₂` snapshot of the index.  The two `fenv::dup`s are `FEnv.dup_refines`. -/
theorem check_ind_recs_s_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe2 fe' : fenv.FEnv} {recs : alloc.vec.Vec env.ConstantInfo}
    (hst : StateWF st) (hfe : FEnvWF fe2) (hbn : NamesWF block_names)
    (hrecs : ConstantInfosWF recs)
    (h : inductives.inductives_c.check_ind_recs_s mode st block_names fe2 recs
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkIndRecsS (absMode mode) (absNames block_names) lfe
            (absConstantInfos recs)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- the `eqA` pin guard, the two dups, `provision_recs_s`, the flush, the fold
  sorry

/-- `ConLeche/Cached/CheckerC.lean:168-175` — `install_proj_fn_step_s` refines
`installProjFnStepS`: **one flush** before the projection's own checks, and
nothing at all where the model's projection artifact is absent. -/
theorem install_proj_fn_step_s_refines
    {st st' : cached.state_c.CState} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f i : Std.U64} {fe fe' : fenv.FEnv}
    (hst : StateWF st) (hfe : FEnvWF fe) (ht : NameWF t) (hc : NameWF ctor_name)
    (hlps : NamesWF lps)
    (h : inductives.inductives_c.install_proj_fn_step_s mode st t ctor_name lps
        n_p n_f fe i = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.installProjFnStepS (absMode mode) (absName t)
            (absName ctor_name) (absNames lps) n_p.val n_f.val lfe i.val).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `CoreK.proj_model_name_refines` and `FEnv.find_refines` for the artifact
  -- probe, then the flush and `IndModeled`'s `check_proj_fn` stage
  sorry

/-- `ConLeche/Cached/CheckerC.lean:233-268` — `install_proj_fns_s` refines
`(List.range nF).foldlM (installProjFnStepS …) fe₃`, as an index recursion. -/
theorem install_proj_fns_s_refines
    {st st' : cached.state_c.CState} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f i : Std.U64} {fe fe' : fenv.FEnv}
    (hst : StateWF st) (hfe : FEnvWF fe) (ht : NameWF t) (hc : NameWF ctor_name)
    (hlps : NamesWF lps)
    (h : inductives.inductives_c.install_proj_fns_s mode st t ctor_name lps n_p
        n_f fe i = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        ((List.range' i.val (n_f.val - i.val)).foldlM
            (ConLeche.Cached.installProjFnStepS (absMode mode) (absName t)
              (absName ctor_name) (absNames lps) n_p.val n_f.val) lfe).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  generalize hd : n_f.val - i.val = d
  induction d using Nat.strong_induction_on generalizing st fe i with
  | _ d ih =>
    intro lst lfe hrel hfer
    rw [inductives.inductives_c.install_proj_fns_s] at h
    split at h
    · rename_i hge
      have hz : d = 0 := by rw [← hd]; scalar_tac
      subst hz
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lst, lfe, by
        simp only [List.range'_zero, List.foldlM_nil, StateT.run, Pure.pure,
          StateT.pure]
        rfl, hrel, hfer, hst, hfe⟩
    · rename_i hlt
      obtain ⟨p, hstep, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err e => simp at h
      | Ok fe2 =>
        obtain ⟨i1, hi1, h⟩ := by simpa using bind_eq_ok_iff.mp (by simpa using h)
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        obtain ⟨lst1, lfe1, hrun1, hrel1, hfer1, hwf1, hfew1⟩ :=
          install_proj_fn_step_s_refines hw hst hfe ht hc hlps hstep lst lfe hrel hfer
        have hsplit : d = (n_f.val - i1.val) + 1 := by rw [← hd]; scalar_tac
        subst hsplit
        obtain ⟨lst', lfe', hrunr, hrelr, hferr, hwfr, hfewr⟩ :=
          ih (n_f.val - i1.val) (by omega) hwf1 hfew1 h rfl lst1 lfe1 hrel1 hfer1
        refine ⟨lst', lfe', ?_, hrelr, hferr, hwfr, hfewr⟩
        rw [List.range'_succ, List.foldlM_cons, ← hi1v]
        simp only [StateT.run, Bind.bind, StateT.bind, Except.bind] at hrun1 hrunr ⊢
        rw [hrun1]
        exact hrunr

/-- `ConLeche/Cached/CheckerC.lean:233-268` — `check_ind_decl_struct_s` refines
the single-type-former, single-constructor arm of `checkIndDeclSF`: the
capability record, the members, the recursors, the eta constructor residual,
the projection name family's freshness and — at a structure-like block — the
projection functions. -/
theorem check_ind_decl_struct_s_refines
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {block_names : alloc.vec.Vec name.Name}
    {nonrecs recs : alloc.vec.Vec env.ConstantInfo}
    {cv_t cv_c : env.ConstantVal} {n_p n_f : Std.U64}
    (hst : StateWF st) (hfe : FEnvWF fe) (hbn : NamesWF block_names)
    (hnr : ConstantInfosWF nonrecs) (hrecs : ConstantInfosWF recs)
    (hct : ConstantValWF cv_t) (hcc : ConstantValWF cv_c)
    (h : inductives.inductives_c.check_ind_decl_struct_s mode st fe block_names
        nonrecs recs cv_t cv_c n_p n_f = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (checkIndDeclStructS (absMode mode) lfe (absNames block_names)
            (absConstantInfos nonrecs) (absConstantInfos recs)
            (absConstantVal cv_t) (absConstantVal cv_c) n_p.val n_f.val).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `ind_block_caps`, the two folds above, `ctor_residual_ok`,
  -- `StructInstall.proj_fn_family_free_refines`, `ctor_targets_fam`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:233-268` — **`check_ind_decl_s` refines
`checkIndDeclSF`**: the modeled inductive block, returning the extended index.
One of the two entry points `checker.rs`'s `.indDecl` arm calls. -/
theorem check_ind_decl_s_refines
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {block : alloc.vec.Vec env.ConstantInfo}
    (hst : StateWF st) (hfe : FEnvWF fe) (hblock : ConstantInfosWF block)
    (h : inductives.inductives_c.check_ind_decl_s mode st fe block
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkIndDeclSF (absMode mode) lfe
            (absConstantInfos block)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `filter_recs`, `Env.block_rec_suffix_ok_refines`, `block_names_of`,
  -- `single_ind_ctor`, then the struct arm above or the general one
  sorry

/-! ## The direct route -/

/-- `ConLeche/Cached/CheckerC.lean:177-190` — `check_native_pass_s` refines
`checkNativePassS`: **one flush per environment transition**, between the
former's stage and the constructors'.  `native_install`'s split into
`check_native_pass_former` and `check_native_pass_ctors` puts it exactly
there, so no memo policy differs from the cited code (DESIGN.md §3.1). -/
theorem check_native_pass_s_refines
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {p0 : inductives.native_parts.NativeParts} {is_rec : Bool}
    {q : inductives.native_install.NativePass × Bool}
    (hst : StateWF st) (hfe : FEnvWF fe) (hp0 : IndAbs.NativePartsWF p0)
    (h : inductives.inductives_c.check_native_pass_s mode st fe p0 is_rec
        = ok (.Ok q, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lq,
        (ConLeche.Cached.checkNativePassS (absMode mode) lfe
            (IndAbs.absNativeParts p0) is_rec).run lst = .ok ((lq, q.2), lst')
        ∧ StateRel st' lst' ∧ IndAbs.NativePassRel q.1 lq
        ∧ StateWF st' ∧ IndAbs.NativePassWF q.1 := by
  -- `check_native_pass_former`, `flush_c_refines`, `check_native_pass_ctors`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:192-215` — `check_native_tail_s` refines
`checkNativeTailS`: **one flush entering the recursor's environment**, after
`consSumCtorsF` and before `checkNativeRecF`, which is where
`native_install`'s three-way split puts it. -/
theorem check_native_tail_s_refines
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {q : inductives.native_install.NativePass}
    (hst : StateWF st) (hfe : FEnvWF fe) (hq : IndAbs.NativePassWF q)
    (h : inductives.inductives_c.check_native_tail_s mode st fe q
        = ok (.Ok fe', st')) :
    ∀ lst lfe lq, StateRel st lst → FEnvRel fe lfe →
      IndAbs.NativePassRel q lq →
      ∃ lst' lfe',
        (ConLeche.Cached.checkNativeTailS (absMode mode) lfe lq).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `check_native_tail_guards`, `check_native_cons`, `flush_c_refines`,
  -- `check_native_install`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:217-231` — **`check_native_s` refines
`checkNativeS`**: the distinct constructor names, one flush, the pass at the
syntactic `is_rec` reading, again at the classified verdict where the reading
overshot, and the install after it.  The other entry point `checker.rs`'s
`.indDecl` arm calls. -/
theorem check_native_s_refines
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {p0 : inductives.native_parts.NativeParts}
    (hst : StateWF st) (hfe : FEnvWF fe) (hp0 : IndAbs.NativePartsWF p0)
    (h : inductives.inductives_c.check_native_s mode st fe p0
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkNativeS (absMode mode) lfe
            (IndAbs.absNativeParts p0)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `ctor_names`, `level::name_nodup`, the flush, the two passes and the tail
  sorry

end Drivers

/-! ## The seam with the checker tier

`IndRoutesSpec` (`Refine/IndSpec.lean`) is what task #56's checker tier
consumes.  It is exactly the two entry-point lemmas, bundled. -/

/-- **The two inductive routes, refined**, under the knot at
`core_k::check_fuel()` (task #55). -/
theorem ind_routes_spec {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) : IndRoutesSpecP mode where
  checkNative := fun _ _ _ _ _ hst hfe hp0 h lst lfe hrel hfer =>
    check_native_s_refines hk.1 hst hfe hp0 h lst lfe hrel hfer
  checkIndDecl := fun _ _ _ _ _ hst hfe hb h lst lfe hrel hfer =>
    check_ind_decl_s_refines hk.1 hst hfe hb h lst lfe hrel hfer

/-! ## The axiom census

DESIGN.md §5's P3 gate on the two entry points.  While the tier is open the
census carries `sorryAx`, and it is machine-checked: `sorryAx` leaving these
two lines is the gate that says the inductive routes are closed. -/

/-- info: 'ConRon.Refine.InductivesC.check_native_s_refines' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_native_s_refines

/-- info: 'ConRon.Refine.InductivesC.check_ind_decl_s_refines' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_ind_decl_s_refines

end ConRon.Refine.InductivesC
