/-
`CORE_PLAN.md` step 4 (task #49): the **pure inference clauses** of
`crates/con-ron-core/src/kernel/core_k.rs` -- the seven state-free functions
the cited `inferBody`/`annotateBody` arms of `ConLeche/Kernel/Core.lean` are
factored into, i.e. everything those arms compute without touching the
checker's recursive knot:

* `infer_lit_nat` (`:2424`) and `infer_lit_str` (`:2441`) -- the two literal
  arms of `inferBody` (`Core.lean:2039-2204`; the twin `inferBodyIO`
  `:2206-2334` has the same two arms);
* `infer_fvar` (`:2460`) -- the `.fvar` arm's scope check;
* `proj_entry_type_at` (`:2335`) -- `ProjEntry.typeAt` (`Core.lean:1797-1806`;
  twin `Cached/ExprOpsC.lean:623-642 ProjEntry.typeAtI`), the only one of the
  seven that returns a bare `Expr`;
* `proj_type_at_checked` (`:2479`) and `infer_proj_at` (`:2516`) -- the `.proj`
  arm of `inferBody`, split at the table lookup;
* `annotate_proj_entry` (`:2640`) -- the `.proj` arm of `annotateBody`
  (`Core.lean:2736-2856`).

## What carries the proofs

**Nothing below the `Expr` layer is re-walked.**  `proj_entry_type_at` is one
`instantiate_level_params` (`Refine/ExprOpsMeta.lean`), one spine reversal and
one `instantiate_list_fast` (`Refine/ExprOpsSubst.lean`); `infer_proj_at` adds
`get_app_fn`/`get_app_args` (`Refine/ExprOpsSpine.lean`) and `find_proj`
(`Refine/CoreKProj.lean`, which this file imports for `find_proj_refines` and
for the `ProjEntryWF` that lemma hands back with the entry).

**The cited arms are transcribed, not applied.**  `inferBody` and
`annotateBody` are open-recursion bodies over a `CoreFns m` record: their
`.proj` arms call `r.whnf`/`r.infer`, so there is no way to *apply* them to
abstracted arguments at this granularity, and the three `*L` definitions below
are verbatim transcriptions of the cited arms' state-free parts with the
recursive results (`te`, `e'`) as parameters -- exactly the factoring the Rust
doc comments describe.  `projPropGuard_eq` discharges the one step of the
transcription that is not literal: the cited `.proj` arm *inlines*
`ProjEntry.fireOk`'s body (`Core.lean:1250-1253`) as an `if`/`unless` pair
where the port calls the function, and that lemma proves the two agree.  Error
*messages* are carried in the transcriptions for readability only -- DESIGN.md
§3.1 does not require them to match, and no lemma here claims anything about a
failure arm.

**Five facts are hypotheses**, each owned by a sibling agent of this task and
stated in exactly the shape that agent proves, so that discharging it at merge
is one `exact`:

| hypothesis | what discharges it |
|---|---|
| `hnat` | `Refine/CoreKNames.lean`'s `nat_name_refines` |
| `hstr` | `Refine/CoreKNames.lean`'s `string_name_refines` |
| `hnls` | `core_k::nat_lit_supported`'s refinement (`Refine/CoreKSupport.lean`) |
| `hsls` | `core_k::str_lit_supported`'s refinement (`Refine/CoreKSupport.lean`) |
| `hfire` (`ProjEntryFireOk`) | `proj_entry_fire_ok`'s refinement (`Refine/CoreKGuards.lean`) |
| `hrev` (`RevAppendExprs`) | `Refine/CoreKVec.lean`'s `rev_append_exprs_refines` |

`constKind_wf_inv` belongs in `Refine/Expr.lean` beside the `*_inv` family;
`Refine/CoreKLits.lean` has the same lemma under the name `const_wf_inv`, so
one of the two goes at merge.  `levelsWF_empty` likewise duplicates a one-liner
several `CoreK*` files carry.
-/
import ConRon.Refine.CoreKProj
import ConLeche.Kernel.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK


/-! ## The two literal arms of `inferBody` -/

/-- The port's `Vec::new` of levels is well formed (its abstraction is `[]`,
which is `rfl`).  A one-liner several `CoreK*` files carry; see the module
note. -/
theorem levelsWF_empty : LevelsWF (alloc.vec.Vec.new level.Level) := by
  intro l hl; simp at hl

/-- `ConLeche/Kernel/Core.lean:2039-2204 inferBody`, the `.lit (.natVal _)`
arm -- **`core_k::infer_lit_nat`**.  (`:2206-2334 inferBodyIO` has the same
arm.)  `hnls` is `core_k::nat_lit_supported`'s refinement against
`FEnv.natLitSupportedF` (`Kernel/FEnv.lean:117`, the indexed twin of the cited
`natLitSupported`) and `hnat` is `basis_names::nat_name`'s; both belong to
sibling agents (module note). -/
theorem infer_lit_nat_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {r : expr.Expr}
    (hnls : ∀ c : Bool, core_k.nat_lit_supported fe = ok c →
      c = ConLeche.natLitSupportedF lfe)
    (hnat : ∀ n : name.Name, basis_names.nat_name = ok n →
      absName n = ConLeche.natName ∧ NameWF n)
    (h : core_k.infer_lit_nat fe = ok (.Ok r)) :
    (if ConLeche.natLitSupportedF lfe then .ok (.const ConLeche.natName [])
     else .error (.invalid "Nat literal without the Nat basis declarations"))
      = (.ok (absExpr r) : ConLeche.CheckM ConLeche.Expr) ∧ ExprWF r := by
  rw [core_k.infer_lit_nat] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  have hbv := hnls b hb
  split at h
  · rename_i hbt
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨n, hn, e, hmk, he⟩ := h
    obtain ⟨hnabs, hnwf⟩ := hnat n hn
    cases he
    rw [if_pos (show ConLeche.natLitSupportedF lfe = true by rw [← hbv]; exact hbt)]
    refine ⟨?_, Expr.mk_const_wf hnwf levelsWF_empty hmk⟩
    rw [Expr.mk_const_refines hmk, hnabs]
    rfl
  · rename_i hbf
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨_, -, _, -, _, -, hcontra⟩ := h
    exact absurd hcontra (by simp)

/-- `ConLeche/Kernel/Core.lean:2039-2204 inferBody`, the `.lit (.strVal _)`
arm -- **`core_k::infer_lit_str`**.  As for `Nat`, with
`FEnv.strLitSupportedF` (`Kernel/FEnv.lean:122`) and `basis_names::string_name`
as the two hypotheses; the missing-support verdict is a decline, not a
reject. -/
theorem infer_lit_str_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {r : expr.Expr}
    (hsls : ∀ c : Bool, core_k.str_lit_supported fe = ok c →
      c = ConLeche.strLitSupportedF lfe)
    (hstr : ∀ n : name.Name, basis_names.string_name = ok n →
      absName n = ConLeche.stringName ∧ NameWF n)
    (h : core_k.infer_lit_str fe = ok (.Ok r)) :
    (if ConLeche.strLitSupportedF lfe then .ok (.const ConLeche.stringName [])
     else .error (.notImplemented
       "string literals before the String support declarations"))
      = (.ok (absExpr r) : ConLeche.CheckM ConLeche.Expr) ∧ ExprWF r := by
  rw [core_k.infer_lit_str] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  have hbv := hsls b hb
  split at h
  · rename_i hbt
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨n, hn, e, hmk, he⟩ := h
    obtain ⟨hnabs, hnwf⟩ := hstr n hn
    cases he
    rw [if_pos (show ConLeche.strLitSupportedF lfe = true by rw [← hbv]; exact hbt)]
    refine ⟨?_, Expr.mk_const_wf hnwf levelsWF_empty hmk⟩
    rw [Expr.mk_const_refines hmk, hnabs]
    rfl
  · simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨_, -, _, -, _, -, hcontra⟩ := h
    exact absurd hcontra (by simp)

/-! ## The `.fvar` arm -/

/-- `ConLeche/Kernel/Core.lean:2039-2204 inferBody`, the `.fvar` arm --
**`core_k::infer_fvar`**: the `O(1)` scope check at a leaf of a traversal that
happens anyway.  `annotateBody`'s `.fvar` arm (`:2751-2755`) is the same test,
returning the node instead of its type. -/
theorem infer_fvar_refines {idx depth : Std.U64} {ty r : expr.Expr} (hty : ExprWF ty)
    (h : core_k.infer_fvar idx ty depth = ok (.Ok r)) :
    (if idx.val < depth.val then .ok (absExpr ty)
     else .error (.invalid "free variable out of scope"))
      = (.ok (absExpr r) : ConLeche.CheckM ConLeche.Expr) ∧ ExprWF r := by
  rw [core_k.infer_fvar] at h
  split at h
  · rename_i hlt
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨e, hdup, he⟩ := h
    cases he
    rw [if_pos (show idx.val < depth.val by scalar_tac), Expr.dup_eq hdup]
    exact ⟨rfl, hty⟩
  · simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨_, -, _, -, _, -, hcontra⟩ := h
    exact absurd hcontra (by simp)

/-! ## `ProjEntry.typeAt` -/

/-- Exactly what `Refine/CoreKVec.lean`'s `rev_append_exprs_refines` proves of
`core_k::rev_append_exprs` (`Core.lean:1797-1806`'s `targs.reverse`, as the
port's downward index recursion). -/
def RevAppendExprs : Prop :=
  ∀ (out targs r : alloc.vec.Vec expr.Expr), ExprsWF out → ExprsWF targs →
    core_k.rev_append_exprs out targs (alloc.vec.Vec.len targs) = ok r →
    absExprs r = absExprs out ++ (absExprs targs).reverse ∧ ExprsWF r

/-- `ConLeche/Kernel/Core.lean:1797-1806 ProjEntry.typeAt` (twin
`Cached/ExprOpsC.lean:623-642 ProjEntry.typeAtI`) -- **`core_k::proj_entry_type_at`**:
the stored body level-instantiated at the subject type's levels, then the
subject and the subject type's arguments substituted for its `numParams + 1`
loose variables in ONE `instantiateList`.  The port builds the cited
`pe :: targs.reverse` as a `Vec` (module deviation), which is `hrev`. -/
theorem proj_entry_type_at_refines {entry : env.ProjEntry}
    {us : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr} {pe r : expr.Expr}
    (hrev : RevAppendExprs) (hent : ProjEntryWF entry) (hus : LevelsWF us)
    (htargs : ExprsWF targs) (hpe : ExprWF pe)
    (h : core_k.proj_entry_type_at entry us targs pe = ok r) :
    absExpr r = (absProjEntry entry).typeAt (absLevels us) (absExprs targs) (absExpr pe)
      ∧ ExprWF r := by
  obtain ⟨-, hlp, -, hbody, -, -⟩ := hent
  rw [core_k.proj_entry_type_at] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨body, hbd, e, hdup, vs, hpush, vs1, hrv, hins⟩ := h
  obtain ⟨hbdabs, hbdwf⟩ := ExprOps.instantiate_level_params_refines hlp hus hbody hbd
  rw [Expr.dup_eq hdup] at hpush
  have hvsabs : absExprs vs = [absExpr pe] := by
    rw [ExprOps.absExprs_push hpush]; rfl
  have hvswf : ExprsWF vs := ExprOps.exprsWF_push ExprOps.exprsWF_new hpe hpush
  obtain ⟨hv1abs, hv1wf⟩ := hrev vs targs vs1 hvswf htargs hrv
  obtain ⟨habs, hwf⟩ := ExprOps.instantiate_list_fast_refines hbdwf hv1wf hins
  refine ⟨?_, hwf⟩
  rw [habs, hv1abs, hvsabs, hbdabs, show ((0#u64 : Std.U64)).val = 0 from rfl]
  rfl

/-! ## The `.proj` arm of `inferBody` -/

/-- Exactly what `Refine/CoreKGuards.lean` proves of
`core_k::proj_entry_fire_ok` against `ProjEntry.fireOk`
(`ConLeche/Kernel/Core.lean:1250-1253`). -/
def ProjEntryFireOk : Prop :=
  ∀ (entry : env.ProjEntry) (us : alloc.vec.Vec level.Level) (c : Bool),
    ProjEntryWF entry → LevelsWF us → core_k.proj_entry_fire_ok entry us = ok c →
    c = (absProjEntry entry).fireOk (absLevels us)

/-- **The transcription's one non-literal step.**  `inferBody`'s `.proj` arm
inlines `ProjEntry.fireOk`'s body (`Core.lean:1250-1253`) as
`if <struct sort is Prop> then unless <field sort is Prop> do throw`, while the
port calls `proj_entry_fire_ok`; the two guards pick the same branch. -/
theorem projPropGuard_eq {α : Type} (entry : ConLeche.ProjEntry)
    (us : List ConLeche.Level) (a b : α) :
    (if (ConLeche.Level.isEquiv entry.structSort .zero == some true) then
        (if (ConLeche.Level.isEquiv
              (ConLeche.Level.subst entry.levelParams us entry.fieldSort) .zero
                == some true) then a else b)
      else a)
      = (if entry.fireOk us then a else b) := by
  simp only [ConLeche.ProjEntry.fireOk]
  by_cases h1 : (ConLeche.Level.isEquiv entry.structSort .zero == some true) = true <;>
    simp [h1]

/-- `ConLeche/Kernel/Core.lean:2163-2189` -- the cited `.proj` arm's checks and
value, transcribed as a function of the abstracted arguments (module note), with
`ProjEntry.fireOk` in place of its inlined body (`projPropGuard_eq`). -/
def projTypeAtCheckedL (entry : ConLeche.ProjEntry) (sn T : ConLeche.Name)
    (us : List ConLeche.Level) (targs : List ConLeche.Expr) (pe : ConLeche.Expr) :
    ConLeche.CheckM ConLeche.Expr :=
  if T = sn ∧ targs.length = entry.numParams ∧ us.length = entry.levelParams.length then
    (if entry.fireOk us then .ok (entry.typeAt us targs pe)
     else .error (.invalid
       "projection from a propositional structure must be a proposition"))
  else .error (.notImplemented "projection without a native entry")

/-- **`core_k::proj_type_at_checked` refines the cited `.proj` arm's checks**
(`ConLeche/Kernel/Core.lean:2039-2204 inferBody`, `:2163-2189`; twin
`:2206-2334 inferBodyIO`): on success all three shape tests and the possibly-`Prop`
guard pass in the Lean too, and the value is `ProjEntry.typeAt`'s. -/
theorem proj_type_at_checked_refines {entry : env.ProjEntry} {sn t : name.Name}
    {us : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr} {pe r : expr.Expr}
    (hrev : RevAppendExprs) (hfire : ProjEntryFireOk) (hent : ProjEntryWF entry)
    (hsn : NameWF sn) (ht : NameWF t) (hus : LevelsWF us) (htargs : ExprsWF targs)
    (hpe : ExprWF pe)
    (h : core_k.proj_type_at_checked entry sn t us targs pe = ok (.Ok r)) :
    projTypeAtCheckedL (absProjEntry entry) (absName sn) (absName t) (absLevels us)
        (absExprs targs) (absExpr pe) = .ok (absExpr r) ∧ ExprWF r := by
  rw [core_k.proj_type_at_checked] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  have hbv : b = decide (absName t = absName sn) := Name.beq_refines ht hsn hb
  split at h
  case isFalse => simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, reduceCtorEq,
      and_false, exists_false] at h
  rename_i hbt
  have hname : absName t = absName sn := by
    rw [hbv] at hbt; exact of_decide_eq_true hbt
  simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
  split at h
  case isTrue => simp only [bind_eq_ok_iff, Result.ok.injEq, reduceCtorEq, and_false,
      exists_false] at h
  rename_i hnp
  have hnpv : (absExprs targs).length = (absProjEntry entry).numParams := by
    have hc : (Std.UScalar.cast .U64 (alloc.vec.Vec.len targs) : Std.U64).val
        = targs.val.length := by
      rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hnp
    rw [hnp] at hc
    simp only [absExprs, List.length_map, absProjEntry]
    exact hc.symm
  split at h
  case isTrue => simp only [bind_eq_ok_iff, Result.ok.injEq, reduceCtorEq, and_false,
      exists_false] at h
  rename_i hlp
  have hlpv : (absLevels us).length = (absProjEntry entry).levelParams.length := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlp
    have h1 : (alloc.vec.Vec.len us).val = us.val.length := alloc.vec.Vec.len_val us
    have h2 : (alloc.vec.Vec.len entry.level_params).val
        = entry.level_params.val.length := alloc.vec.Vec.len_val entry.level_params
    have h3 : (alloc.vec.Vec.len us).val
        = (alloc.vec.Vec.len entry.level_params).val := by rw [hlp]
    simp only [absLevels, absProjEntry, absNames, List.length_map]
    omega
  simp only [bind_eq_ok_iff] at h
  obtain ⟨c, hc, h⟩ := h
  have hcv := hfire entry us c hent hus hc
  split at h
  case isFalse => simp only [bind_eq_ok_iff, Result.ok.injEq, reduceCtorEq, and_false,
      exists_false] at h
  rename_i hct
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨e, he, hr⟩ := h
  cases hr
  obtain ⟨habs, hwf⟩ := proj_entry_type_at_refines hrev hent hus htargs hpe he
  refine ⟨?_, hwf⟩
  rw [projTypeAtCheckedL, if_pos ⟨hname, hnpv, hlpv⟩,
    if_pos (show (absProjEntry entry).fireOk (absLevels us) = true by
      rw [← hcv]; exact hct), habs]

/-- **`ExprWF` inverted at a `Const` node**: the head name and the level list
are well formed.  Belongs in `Refine/Expr.lean` beside the `*_inv` family
(module note). -/
theorem constKind_wf_inv {e : expr.Expr} (he : ExprWF e) :
    ∀ {d : Std.U64} {c : name.Name} {us : alloc.vec.Vec level.Level},
      e = .mk (.mk d (.Const c us)) → NameWF c ∧ LevelsWF us := by
  cases he with
  | @bvar i e h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; intros; simp_all
  | @fvar idx ty e _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; intros; simp_all
  | @sort u e _ h1 => obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1; intros; simp_all
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro d c us' hk
    cases hk
    exact ⟨hn, hus⟩
  | @app f a e _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; intros; simp_all
  | @lam ty b m e _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; intros; simp_all
  | @forall_e ty b m e _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; intros; simp_all
  | @let_e ty v b e _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; intros; simp_all
  | @lit l e _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; intros; simp_all
  | @proj s i x e _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; intros; simp_all

/-- `ConLeche/Kernel/Core.lean:2155-2192` -- the cited `.proj` arm of
`inferBody` below its two recursive calls, transcribed: the reduced subject type
`te` is a parameter, and the arm is the head-shape match, the table lookup and
`projTypeAtCheckedL`. -/
def inferProjAtL (lfe : ConLeche.FEnv) (sn : ConLeche.Name) (i : Nat)
    (pe te : ConLeche.Expr) : ConLeche.CheckM ConLeche.Expr :=
  match te.getAppFn with
  | .const T us =>
    match lfe.findProj? T i with
    | some entry => projTypeAtCheckedL entry sn T us te.getAppArgs pe
    | none => .error (.notImplemented "projection without a native entry")
  | _ => .error (.notImplemented "projection without a native entry")

/-- **`core_k::infer_proj_at` refines the cited `.proj` arm of `inferBody`**
(`ConLeche/Kernel/Core.lean:2039-2204`, `:2155-2192`; twin `:2206-2334
inferBodyIO` -- the arm is byte-identical in the two bodies, which is why the
port has one function).  The environment read is `fenv::find_proj`, through
`Refine/CoreKProj.lean`'s `find_proj_refines`, so this takes both `FindAgree` and
`FindWF`. -/
theorem infer_proj_at_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {sn : name.Name}
    {i : Std.U64} {pe te r : expr.Expr}
    (hrev : RevAppendExprs) (hfire : ProjEntryFireOk)
    (hrel : FindAgree fe lfe) (hfwf : FindWF fe)
    (hsn : NameWF sn) (hpe : ExprWF pe) (hte : ExprWF te)
    (h : core_k.infer_proj_at fe sn i pe te = ok (.Ok r)) :
    inferProjAtL lfe (absName sn) i.val (absExpr pe) (absExpr te) = .ok (absExpr r)
      ∧ ExprWF r := by
  rw [core_k.infer_proj_at] at h
  simp only [bind_eq_ok_iff, arc_deref_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨f, hf, h⟩ := h
  obtain ⟨hfabs, hfnwf⟩ := ExprOps.get_app_fn_refines hte hf
  obtain ⟨⟨fd, fk⟩⟩ := f
  cases fk
  case Const t us' =>
    simp only [ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    obtain ⟨hnwf, huswf⟩ := constKind_wf_inv hfnwf rfl
    obtain ⟨hoabs, howf⟩ := find_proj_refines hrel hfwf hnwf ho
    have hgf : (absExpr te).getAppFn = .const (absName t) (absLevels us') := by
      rw [← hfabs]; rfl
    cases o with
    | none =>
      simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, reduceCtorEq,
        and_false, exists_false] at h
    | some entry =>
      simp only [Option.map_some] at hoabs
      simp only [bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨targs, hta, h⟩ := h
      obtain ⟨htabs, htawf⟩ := ExprOps.get_app_args_refines hte hta
      obtain ⟨hres, hrwf⟩ := proj_type_at_checked_refines hrev hfire (howf entry rfl)
        hsn hnwf huswf htawf hpe h
      refine ⟨?_, hrwf⟩
      simp only [inferProjAtL, hgf, ← hoabs, ← htabs]
      exact hres
  all_goals
    simp only [ExprOps.node_kind, bind_eq_ok_iff, lift_eq, Result.ok.injEq,
      reduceCtorEq, and_false, exists_false] at h

/-! ## The `.proj` arm of `annotateBody` -/

/-- `ConLeche/Kernel/Core.lean:2819-2854` -- the cited `.proj` arm of
`annotateBody` below its recursive calls, transcribed: the annotated subject
`e2` and the reduced subject type's head `T` and arguments are parameters, and
the arm is the table lookup and its three verdicts. -/
def annotateProjEntryL (lfe : ConLeche.FEnv) (sn T : ConLeche.Name) (i : Nat)
    (e2 : ConLeche.Expr) (targs : List ConLeche.Expr) : ConLeche.CheckM ConLeche.Expr :=
  match lfe.findProj? T i with
  | some entry =>
    if T = sn then
      (if targs.length = entry.numParams then .ok (.proj T i e2)
       else .error (.invalid "projection parameter mismatch"))
    else .error (.invalid "invalid projection: the node names another structure")
  | none =>
    .error (if (lfe.findProj? T 0).isSome then
        ConLeche.CheckError.invalid "projection index out of range"
      else .notImplemented "projection on a non-structure-like type")

/-- **`core_k::annotate_proj_entry` refines the cited `.proj` arm of
`annotateBody`** (`ConLeche/Kernel/Core.lean:2736-2856`, `:2819-2854`): on
success the node names the subject type's head, the parameter count matches,
and the value is the normalized `.proj T i e'`. -/
theorem annotate_proj_entry_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {sn t : name.Name} {i : Std.U64} {e2 r : expr.Expr}
    {targs : alloc.vec.Vec expr.Expr}
    (hrel : FindAgree fe lfe) (hfwf : FindWF fe)
    (hsn : NameWF sn) (ht : NameWF t) (he2 : ExprWF e2)
    (h : core_k.annotate_proj_entry fe sn t i e2 targs = ok (.Ok r)) :
    annotateProjEntryL lfe (absName sn) (absName t) i.val (absExpr e2) (absExprs targs)
      = .ok (absExpr r) ∧ ExprWF r := by
  rw [core_k.annotate_proj_entry] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  obtain ⟨hoabs, howf⟩ := find_proj_refines hrel hfwf ht ho
  cases o with
  | none =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨o1, ho1, h⟩ := h
    split at h
    all_goals
      simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, reduceCtorEq, and_false,
        exists_false] at h
  | some entry =>
    simp only [Option.map_some] at hoabs
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbv : b = decide (absName t = absName sn) := Name.beq_refines ht hsn hb
    split at h
    case isFalse => simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, reduceCtorEq,
        and_false, exists_false] at h
    rename_i hbt
    have hname : absName t = absName sn := by
      rw [hbv] at hbt; exact of_decide_eq_true hbt
    simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
    split at h
    case isTrue => simp only [bind_eq_ok_iff, Result.ok.injEq, reduceCtorEq, and_false,
        exists_false] at h
    rename_i hnp
    have hnpv : (absExprs targs).length = (absProjEntry entry).numParams := by
      have hc : (Std.UScalar.cast .U64 (alloc.vec.Vec.len targs) : Std.U64).val
          = targs.val.length := by
        rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hnp
      rw [hnp] at hc
      simp only [absExprs, List.length_map, absProjEntry]
      exact hc.symm
    simp only [name_dup_eq, bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨e, hdup, e1, hproj, hr⟩ := h
    cases hr
    rw [Expr.dup_eq hdup] at hproj
    refine ⟨?_, Expr.proj_wf ht he2 hproj⟩
    rw [annotateProjEntryL, ← hoabs]
    simp only [if_pos hname, if_pos hnpv, Expr.proj_refines hproj]

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.CoreK.infer_proj_at_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms infer_proj_at_refines

end ConRon.Refine.CoreK
