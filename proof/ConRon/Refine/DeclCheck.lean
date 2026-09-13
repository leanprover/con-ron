import ConRon.Refine.TypeChecker
import ConRon.Refine.CoreKProj
import ConRon.Refine.CoreKSupport
import ConRon.Refine.CoreKNames
import ConRon.Refine.CoreKShapes
import ConRon.Refine.CoreKPinned
import ConRon.Refine.CheckerBase
import ConRon.Refine.BasisPins
import ConRon.Refine.StateCResolve
import ConLeche.Kernel.DeclCheck
import ConLeche.Verify.FastOps

/-! # `kernel::decl_check` — the memoized `constsResolveF` walk (tasks #56, #58)

`CORE_PLAN.md` step 7.  `ConLeche/Kernel/DeclCheck.lean` (937 lines, 40
declarations) is the `FEnv`-indexed mirror of the whole declaration-level
checker, and **task #24's third deviation is the one that matters here**: the
port has *one* environment spelling, the index (task #18 deviation 3), so an
`F`-mirror and its generic twin are **one Rust function carrying both
citations**.  That collapses 21 of the file's 40 declarations into functions
that live elsewhere, `domsMatchAuxA` into `domsMatchAux`, and
`Env.findCV?`/`FEnv.findCV?` into one `find_cv`.

Every lemma below is therefore stated against the **`F`-twin** — that is the
spelling `Cached/CheckerC.lean`'s drivers call, and the one the port computes.

## What `kernel::decl_check` is, after task #58

**Only the memoized `constsResolveF` walk**: `consts_resolve_f_go` and
`consts_resolve_f_fast` (`DeclCheck.lean:60-204`), which nine call sites in
`checker_base`, `parsed_c` and the four inductive install modules consume.
That is the whole module.

Task #56 found that `decl_check.rs` also carried a **second, dead copy** of
`DeclCheck.lean`'s structure-artifact / member / projection-lookup family —
`checkEtaThmF`, `checkUnitThmF`, `indBlockCapsF`, `checkMemberValF`,
`checkProjLookupsF` and their helpers — duplicating task #25's
`kernel::inductives::modeled` under the *same* con-leche citations, which is
a DESIGN.md §3.1 one-to-one violation (two Rust functions per cited Lean
declaration).  `modeled`'s copies are the ones the install routes actually
call, so **task #58 deleted `decl_check.rs`'s**, and with them the lemmas
this file used to state about them.  `ConLeche/Kernel/DeclCheck.lean`'s
artifact/member/projection family is therefore ported in
`kernel::inductives::modeled`, and `ctorResidualOkF` is
`modeled::ctor_residual_ok`.

## Which Rust function carries which pair of citations

| con-leche `F`-mirror | its generic twin | the one Rust function |
|---|---|---|
| `Expr.constsResolveF` (`:37-58`) | `Expr.constsResolve` (`Core.lean:307-332`) | `core_k::consts_resolve` |
| `Expr.constsResolveFGo` (`:89-124`), `Expr.constsResolveFFast` (`:197-204`) | — | `decl_check::consts_resolve_f_go`, `consts_resolve_f_fast` |
| `natOpCodF` (`:210`), `natOpTyPinnedF` (`:220`), `natOpStoredOkF` (`:234`) | `natOpCod`, `natOpTyPinned`, `natOpStoredOk` | `core_k::nat_op_cod`, `nat_op_ty_pinned`, `nat_op_stored_ok` |
| `stdAxiomOkF` (`:241`) | `stdAxiomOk` | `std_axioms::std_axiom_ok` |
| `trustCompilerOkF` (`:273`), `reduceStoredOkF` (`:283`), `reduceElemOkF` (`:289`), `ofReduceAxOkF` (`:297`), `reducePinGuardF` (`:305`) | their `TrustAxioms.lean` twins | `trust_axioms::*` |
| `FEnv.findCV?` (`:34`) | `Env.findCV?` | `checker_base::find_cv` |
| `checkConstantValF` (`:464`), `checkProjRuleF` (`:764`) | `checkConstantVal`, `checkProjRule` | `checker_base::check_constant_val`, `check_proj_rule` |
| the `divMod*F`/`checkDivMod*F` family (`:311`-`:339`, `:862`-`:914`), `checkReducePinF` (`:915`), `checkDefnValF` (`:839`), `installBasisDeclF` (`:856`) | their `Checker.lean` twins | `checker::*` |
| `domsMatchAuxA` (`CheckerBase.lean`) | `domsMatchAux` | `checker_base::doms_match_aux` |
| `checkEtaThmF` (`:345`), `checkUnitThmF` (`:385`), `indBlockCapsF` (`:431`), `checkMemberValF` (`:488`), `checkProjLookupsF` (`:730`), `checkProjTyF` (`:749`), `checkProjIotaF` (`:798`) | their `Kernel/Inductives/Modeled.lean` twins | `inductives::modeled::*` |

The lemmas for a twin that lives in another module are in that module's
`Refine/` file; what is stated *here* is (a) both public functions of
`kernel/decl_check.rs`, and (b) the member check and the projection chain —
the seam task #57's inductive routes consume (`Refine/IndSpec.lean` is the
other half of that seam).  The §2 lemmas are about `inductives::modeled::*`
and `checker_base::*`, and are stated here because **the citation they carry
is `DeclCheck.lean`'s**, which is the pair this file records; the *rest* of
`modeled.rs` — the iota-theorem family proper (`checkIotaThmF` and friends)
and the install routes — is task #57's (`Refine/Ind*.lean`), as are the
`modeled.rs` facts §2 proves here as steps (see below).

## What `decl_check.rs` does not port

`checkIotaThmF` (`:508`), `nestedRuleShapeF` (`:576`), `checkIotaThmNF`
(`:602`), `checkIotaRuleF` (`:688`), `checkIotaRulesF` (`:719`) and
`ctorResidualOkF` (`:419`) stand on `ConLeche/Kernel/Inductives/*` and are task
#57's (`inductives::modeled`).  `CRFMemoInv` (`:71`) and its two lemmas are
`Prop`s — Charon erases them; the port's restatement of the memo invariant is
`Refine/StateCResolve.lean`'s `StateC.MemoBOk`, which this file reuses.

## The knot, and the two hypotheses that travel

Everything with a `CState` runs the core, so it takes
`core_k.check_fuel = ok fuel` and `Core.Wrappers mode fuel`
(`Refine/TypeChecker.lean`'s rule); task #55 discharges them.  Nothing here
proves anything about `cached::core_c`.

## What is proved and what is stated

Proved, with nothing left open: `core_k::consts_resolve` at its
`constsResolveF` citation, `expr_ops::memo_b_get`, the memoized walk
`consts_resolve_f_go` and its wrapper `consts_resolve_f_fast` (which
discharges `Refine/CheckerBase.lean`'s `ConstsResolveFSpec` —
`constsResolveFSpec` below), `modeled::model_str`/`model_of`/`BlockRename`,
`level::name_is_model_suffix`, `check_member_val`, `check_proj_lookups`
(whose pinned-`Eq` conjunct is `Refine/BasisPins.lean`'s, restated here at the
weaker `FindAgree`/`FindWF` environment hypotheses this file carries),
`check_proj_shape`, `check_proj_rule`, `check_proj_ty` and `check_proj_iota`.

## The `modeled.rs` steps

The last two stand on ten facts about `kernel::inductives::modeled` and one
about `checker_base`, all of which belong to task #57 and none of which was
in `proof/`; they are proved here **as steps**, in the sense of
`Refine/CheckerPins.lean`'s `one_level_step` and `Refine/TrustAxioms.lean`'s
copies, because the two statements cannot be discharged without them and this
file may not import a sibling that does not exist yet:

* the renaming dictionaries — `find_proj_model_slot`, `find_proj_fn_slot`
  (index recursions extracted `partial_fixpoint`, so each is a strong
  induction on `n_f - j` through the unfolding equation), `ProjBack` and
  `ProjFwd` against the cited `projBack`/`projFwd` closures;
* `checker_base::doms_match_aux` at a **general** `DomView` — the same
  induction `Refine/CheckerBase.lean` has pinned to `DomIdent`, re-derived
  over the dictionary because `checkProjIotaF` is the one call site that
  views through a renaming (`modeled::DomProjFwd`);
* the iota seam's readers — `thm_probe`, `proj_iota_name`, `arg_get_d`,
  `struct_parts::params_of`/`struct_ps_at`/`field_spine` — and
  `check_iota_sides_ty` and `check_proj_iota_body`.

When task #57 lands these should move to `Refine/Ind*.lean` (and
`Refine/CheckerBase.lean`'s `doms_match_aux_from_refines` should be
generalised to `doms_match_aux_from_view` and recover its `DomIdent` version
as the instance).

## The one hypothesis a statement gained

`check_proj_iota_refines` and `check_proj_iota_body_refines` take
`absName cvj.name = absName ctor_name`.  The cited `checkProjIotaF` builds
the redex head from `ctorName.str "_model"`; the port's
`check_proj_iota_body` is handed `cvj` and not `ctor_name` and spells it
`model_of(&cvj.name)`.  The two agree exactly when `cvj.name = ctorName` —
which every call site guarantees (`cvj` is what `checkProjLookupsF` read out
of `fe.find? ctorName`) but which `ConstantValWF cvj` does not give, so the
statement is **false** without it.  The faithful repair is for
`modeled::check_proj_iota_body` to take `ctor_name`; that is `modeled.rs`'s,
task #57's.

`sorry` count in this file: 0.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.DeclCheck

open ConRon.Refine.CoreK

/-- The port decides a comparison, the cited Lean writes `==`; under
`LawfulBEq` (which con-leche proves of `Name`, `Level` and `Expr`) the two
`Bool`s are the same one.  The bridge every `*_beq_refines` needs to land on a
cited `&&` cascade. -/
theorem decide_eq_beq {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    decide (a = b) = (a == b) := by
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab]

/-! ### The full outcome's small change (task #67)

DESIGN.md §3's ruling of 2026-09-13: every `*_refines` below is stated over the
Rust computation's whole outcome.  Every `CheckError` site of
`kernel::decl_check` and of the `modeled`/`checker_base` functions this file
refines is **mirrored** (DESIGN.md's task-#67 census), so each failure arm ends
in `ErrSim.notImplemented` / `.invalid` / `.internal` at the cited `throw`, and
no `Native` arm appears.  These four are the vocabulary that turns the port's
`Err` value into the constructor it is, and runs con-leche's `throw`. -/

/-- `core_types::invalid v = ok ce → ce = .Invalid v`. -/
private theorem invalid_inv {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v := by
  rw [core_types.invalid] at h; exact (Result.ok_injective h).symm

/-- `core_types::not_implemented v = ok ce → ce = .NotImplemented v`. -/
private theorem not_implemented_inv {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.not_implemented v = ok ce) :
    ce = .NotImplemented v := by
  rw [core_types.not_implemented] at h; exact (Result.ok_injective h).symm

/-- `core_types::internal v = ok ce → ce = .Internal v`. -/
private theorem internal_inv {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.internal v = ok ce) :
    ce = .Internal v := by
  rw [core_types.internal] at h; exact (Result.ok_injective h).symm

/-- `throw` in `CheckCM`, at the *applied* form: the plumbing `simp` set
carries `StateT.run` but no `MonadExcept` instance, so a `throw` arm would
otherwise be left un-run. -/
private theorem throw_apply {β : Type} (le : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM β) lst = .error le := rfl

/-- A mirrored `throw` at `notImplemented`: the port's error came out of
`core_types::not_implemented`, so its kind is con-leche's `.notImplemented`,
and the cited side has been rewritten down to its `throw`. -/
private theorem errSim_notImplemented {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce ce1 : core_types.CheckError} {x : Except ConLeche.CheckError γ} {ls : String}
    (hce : core_types.not_implemented v = ok ce1) (heq : ce1 = ce)
    (hx : x = .error (.notImplemented ls)) : ErrSim ce x := by
  rw [← heq, not_implemented_inv hce]; exact ErrSim.notImplemented hx

/-- A mirrored `throw` at `invalid`, the same bookkeeping. -/
private theorem errSim_invalid {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce ce1 : core_types.CheckError} {x : Except ConLeche.CheckError γ} {ls : String}
    (hce : core_types.invalid v = ok ce1) (heq : ce1 = ce)
    (hx : x = .error (.invalid ls)) : ErrSim ce x := by
  rw [← heq, invalid_inv hce]; exact ErrSim.invalid hx

/-- The port's `Err` return, read off (the state-carrying shape). -/
private theorem err_outS {α : Type} {ce : core_types.CheckError}
    {st1 st' : cached.state_c.CState}
    {out : core.result.Result α core_types.CheckError}
    (h : (ok (core.result.Result.Err ce, st1) :
      Result ((core.result.Result α core_types.CheckError) × cached.state_c.CState))
      = ok (out, st')) : out = .Err ce ∧ st' = st1 := by
  have h1 := Result.ok_injective h
  exact ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩

/-- The port's `Ok` return, read off (the state-carrying shape). -/
private theorem ok_outS {α : Type} {r : α} {st1 st' : cached.state_c.CState}
    {out : core.result.Result α core_types.CheckError}
    (h : (ok (core.result.Result.Ok r, st1) :
      Result ((core.result.Result α core_types.CheckError) × cached.state_c.CState))
      = ok (out, st')) : out = .Ok r ∧ st' = st1 := by
  have h1 := Result.ok_injective h
  exact ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩

/-- A mirrored `throw` at `internal`, the same bookkeeping. -/
private theorem errSim_internal {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce ce1 : core_types.CheckError} {x : Except ConLeche.CheckError γ} {ls : String}
    (hce : core_types.internal v = ok ce1) (heq : ce1 = ce)
    (hx : x = .error (.internal ls)) : ErrSim ce x := by
  rw [← heq, internal_inv hce]; exact ErrSim.internal hx

/-! ## 1. `Expr.constsResolveF` and its memoized walk (`DeclCheck.lean:37-204`)

`core_k::consts_resolve` is the port's single spelling of `Expr.constsResolve`
*and* of `Expr.constsResolveF`: the two Lean definitions have the same clauses
with `env.find?` replaced by `fe.find?`, and the port only ever had the index.
`Refine/CoreKSupport.lean` refines it against the `Env` reading (under an
explicit `FEnv.find? = Env.find?` bridge); this is the same induction against
the *indexed* reading, which needs no bridge and is what everything downstream
actually wants. -/

/-- `ConLeche/Kernel/DeclCheck.lean:37-58 Expr.constsResolveF` —
**`core_k::consts_resolve` refines the indexed walk**, with no `Env` in sight.
The second citation of `Refine/CoreKSupport.lean`'s `consts_resolve_refines`. -/
theorem consts_resolve_f_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hp : PinnedBasisNames) (hfe : FindAgree fe lfe)
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
    rw [← h, find_isSome hfe hn ho]
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
      rw [nat_trio_stored_refines hp hfe h]
      simp only [absExpr, absExprNode, absExprKind, absLiteral,
        ConLeche.Expr.constsResolveF]
    | StrVal sv =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b, hb, h⟩ := h
      have g1 := nat_trio_stored_refines hp hfe hb
      simp only [absExpr, absExprNode, absExprKind, absLiteral,
        ConLeche.Expr.constsResolveF]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← g1]; simp
      | true =>
        simp only [if_true] at h
        rw [str_support_stored_refines hp hfe h, ← g1]; simp
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact and_step (ihf b1 hb1) h (fun c' h' => iha c' h')
  | @lam ty bo m e hty hbo hm h1 iht ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact and_step (iht b1 hb1) h (fun c' h' => ihb c' h')
  | @forall_e ty bo m e hty hbo hm h1 iht ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact and_step (iht b1 hb1) h (fun c' h' => ihb c' h')
  | @let_e ty v bo e hty hv hbo h1 iht ihv ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF,
      Bool.and_assoc]
    refine and_step (iht b1 hb1) h ?_
    intro c' h'
    obtain ⟨b2, hb2, h'⟩ := bind_eq_ok_iff.mp h'
    exact and_step (ihv b2 hb2) h' (fun c'' h'' => ihb c'' h'')
  | @proj sn i x e hs hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact and_step (by rw [find_isSome hfe hs ho]) h (fun c' h' => ih c' h')

/-- `ConLeche/Kernel/DeclCheck.lean:99` — `expr_ops::memo_b_get` is the cited
`memo[e]?` (the same owning probe as `cached::state_c::memo_b_get`, whose
relation `StateC.MemoBOk` this file reuses). -/
theorem memo_b_get_refines {memo : ron.hashmap.HashMap expr.Expr Bool}
    {lmemo : _root_.Std.HashMap ConLeche.Expr Bool} {e : expr.Expr}
    {o : Option Bool} (hm : StateC.MemoBOk memo lmemo) (he : ExprWF e)
    (h : expr_ops.memo_b_get memo e = ok o) : o = lmemo[absExpr e]? := by
  rw [expr_ops.memo_b_get] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  have hr := (get_step (Q := fun _ => True) exprKey hm.inv hm.keys
    (fun _ _ => trivial) hm.rel he hget).1
  cases o' with
  | none => simp only [Result.ok.injEq] at h; subst h; simpa using hr
  | some b => simp only [Result.ok.injEq] at h; subst h; simpa using hr

/-- `ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo` —
**the memoized walk refines the cited one**: the same answer, and the memo it
hands back still relates.  `decl_check::consts_resolve_f_go`.

One induction on the `ExprWF` derivation, exactly
`Refine/StateCResolve.lean`'s `consts_resolve_fc_go_refines` but with the four
leaf arms *outside* the memo probe (the cited clauses answer them through the
spec walk, so those four are `consts_resolve_f_refines` and leave the memo
alone) and with the cited walk's **non**-short-circuiting `&&`, which the port
spells `expr_ops::bool_and` on two already-computed operands. -/
theorem consts_resolve_f_go_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hp : PinnedBasisNames) (hfe : FindAgree fe lfe)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool)
      (lmemo : _root_.Std.HashMap ConLeche.Expr Bool) (b : Bool),
      StateC.MemoBOk memo lmemo →
      decl_check.consts_resolve_f_go fe memo e = ok (b, memo') →
      ∃ lmemo', ConLeche.Expr.constsResolveFGo lfe lmemo (absExpr e)
          = (b, lmemo') ∧ StateC.MemoBOk memo' lmemo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' lmemo b hm h
    rw [decl_check.consts_resolve_f_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨r, hr, h⟩ := h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lmemo, ?_, hm⟩
    rw [consts_resolve_f_refines hp hfe hwfe _ hr]
    simp only [absExpr_mk, absExprKind]
    rw [ConLeche.Expr.constsResolveFGo]
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' lmemo b hm h
    rw [decl_check.consts_resolve_f_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨r, hr, h⟩ := h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lmemo, ?_, hm⟩
    rw [consts_resolve_f_refines hp hfe hwfe _ hr]
    simp only [absExpr_mk, absExprKind]
    rw [ConLeche.Expr.constsResolveFGo]
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' lmemo b hm h
    rw [decl_check.consts_resolve_f_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨r, hr, h⟩ := h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lmemo, ?_, hm⟩
    rw [consts_resolve_f_refines hp hfe hwfe _ hr]
    simp only [absExpr_mk, absExprKind]
    rw [ConLeche.Expr.constsResolveFGo]
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' lmemo b hm h
    rw [decl_check.consts_resolve_f_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨r, hr, h⟩ := h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lmemo, ?_, hm⟩
    rw [consts_resolve_f_refines hp hfe hwfe _ hr]
    simp only [absExpr_mk, absExprKind]
    rw [ConLeche.Expr.constsResolveFGo]
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' lmemo b hm h
    rw [decl_check.consts_resolve_f_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hlk := memo_b_get_refines hm hwfe ho
    simp only [absExpr_mk, absExprKind] at hlk ⊢
    rw [ConLeche.Expr.constsResolveFGo, ← hlk]
    cases o with
    | some r =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lmemo, rfl, hm⟩
    | none =>
      obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := p
      obtain ⟨q, hq, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨r1, memo2⟩ := q
      simp at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      obtain ⟨lm1, hl1, hm1⟩ := ih memo _ lmemo _ hm hq
      simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok] at h
      obtain ⟨s, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨old, memo3⟩ := s
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lm1.insert (ConLeche.Expr.fvar idx (absExpr ty)) r1, ?_,
        ?_⟩
      · simp only [hl1]
      · have := StateC.memo_b_insert hm1 hwfe hins
        simpa only [absExpr_mk, absExprKind] using this
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' lmemo b hm h
    rw [decl_check.consts_resolve_f_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hlk := memo_b_get_refines hm hwfe ho
    simp only [absExpr_mk, absExprKind] at hlk ⊢
    rw [ConLeche.Expr.constsResolveFGo, ← hlk]
    cases o with
    | some r =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lmemo, rfl, hm⟩
    | none =>
      obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := p
      obtain ⟨q1, hq1, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨b1, memoA⟩ := q1
      obtain ⟨q2, hq2, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨b2, memoB⟩ := q2
      simp [ExprOps.bool_and_val] at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      obtain ⟨lm1, hl1, hm1⟩ := ihf memo _ lmemo _ hm hq1
      obtain ⟨lm2, hl2, hm2⟩ := iha memoA _ lm1 _ hm1 hq2
      simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok] at h
      obtain ⟨s, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨old, memo3⟩ := s
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lm2.insert (ConLeche.Expr.app (absExpr f) (absExpr a)) (b1 && b2),
        ?_, ?_⟩
      · simp only [hl1, hl2]
      · have := StateC.memo_b_insert hm2 hwfe hins
        simpa only [absExpr_mk, absExprKind] using this
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' lmemo b hm h
    rw [decl_check.consts_resolve_f_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hlk := memo_b_get_refines hm hwfe ho
    simp only [absExpr_mk, absExprKind] at hlk ⊢
    rw [ConLeche.Expr.constsResolveFGo, ← hlk]
    cases o with
    | some r =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lmemo, rfl, hm⟩
    | none =>
      obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := p
      obtain ⟨q1, hq1, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨b1, memoA⟩ := q1
      obtain ⟨q2, hq2, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨b2, memoB⟩ := q2
      simp [ExprOps.bool_and_val] at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      obtain ⟨lm1, hl1, hm1⟩ := ihty memo _ lmemo _ hm hq1
      obtain ⟨lm2, hl2, hm2⟩ := ihbo memoA _ lm1 _ hm1 hq2
      simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok] at h
      obtain ⟨s, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨old, memo3⟩ := s
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lm2.insert
        (ConLeche.Expr.lam (absExpr ty) (absExpr bo) (absBinderMeta m)) (b1 && b2),
        ?_, ?_⟩
      · simp only [hl1, hl2]
      · have := StateC.memo_b_insert hm2 hwfe hins
        simpa only [absExpr_mk, absExprKind] using this
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' lmemo b hm h
    rw [decl_check.consts_resolve_f_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hlk := memo_b_get_refines hm hwfe ho
    simp only [absExpr_mk, absExprKind] at hlk ⊢
    rw [ConLeche.Expr.constsResolveFGo, ← hlk]
    cases o with
    | some r =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lmemo, rfl, hm⟩
    | none =>
      obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := p
      obtain ⟨q1, hq1, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨b1, memoA⟩ := q1
      obtain ⟨q2, hq2, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨b2, memoB⟩ := q2
      simp [ExprOps.bool_and_val] at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      obtain ⟨lm1, hl1, hm1⟩ := ihty memo _ lmemo _ hm hq1
      obtain ⟨lm2, hl2, hm2⟩ := ihbo memoA _ lm1 _ hm1 hq2
      simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok] at h
      obtain ⟨s, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨old, memo3⟩ := s
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lm2.insert
        (ConLeche.Expr.forallE (absExpr ty) (absExpr bo) (absBinderMeta m))
        (b1 && b2), ?_, ?_⟩
      · simp only [hl1, hl2]
      · have := StateC.memo_b_insert hm2 hwfe hins
        simpa only [absExpr_mk, absExprKind] using this
  | @let_e ty v bo e hty hv hbo h1 ihty ihv ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hv hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' lmemo b hm h
    rw [decl_check.consts_resolve_f_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hlk := memo_b_get_refines hm hwfe ho
    simp only [absExpr_mk, absExprKind] at hlk ⊢
    rw [ConLeche.Expr.constsResolveFGo, ← hlk]
    cases o with
    | some r =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lmemo, rfl, hm⟩
    | none =>
      obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := p
      obtain ⟨q1, hq1, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨b1, memoA⟩ := q1
      obtain ⟨q2, hq2, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨b2, memoB⟩ := q2
      obtain ⟨q3, hq3, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨b3, memoC⟩ := q3
      simp [ExprOps.bool_and3_val] at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      obtain ⟨lm1, hl1, hm1⟩ := ihty memo _ lmemo _ hm hq1
      obtain ⟨lm2, hl2, hm2⟩ := ihv memoA _ lm1 _ hm1 hq2
      obtain ⟨lm3, hl3, hm3⟩ := ihbo memoB _ lm2 _ hm2 hq3
      simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok] at h
      obtain ⟨s, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨old, memo3⟩ := s
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lm3.insert
        (ConLeche.Expr.letE (absExpr ty) (absExpr v) (absExpr bo))
        (b1 && b2 && b3), ?_, ?_⟩
      · simp only [hl1, hl2, hl3]
      · have := StateC.memo_b_insert hm3 hwfe hins
        simpa only [absExpr_mk, absExprKind] using this
  | @proj sn i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' lmemo b hm h
    rw [decl_check.consts_resolve_f_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hlk := memo_b_get_refines hm hwfe ho
    simp only [absExpr_mk, absExprKind] at hlk ⊢
    rw [ConLeche.Expr.constsResolveFGo, ← hlk]
    cases o with
    | some r =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lmemo, rfl, hm⟩
    | none =>
      obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := p
      obtain ⟨q1, hq1, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨b1, memoA⟩ := q1
      obtain ⟨of, hof, hnd⟩ := bind_eq_ok_iff.mp hnd
      have hofv : of.isSome = (lfe.find? (absName sn)).isSome := by
        rw [← option_is_some of]; exact find_isSome hfe hs hof
      simp [ExprOps.bool_and_val] at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      obtain ⟨lm1, hl1, hm1⟩ := ih memo _ lmemo _ hm hq1
      simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok] at h
      obtain ⟨s, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨old, memo3⟩ := s
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lm1.insert
        (ConLeche.Expr.proj (absName sn) i.val (absExpr x))
        ((lfe.find? (absName sn)).isSome && b1), ?_, ?_⟩
      · simp only [hl1, hofv]
      · rw [← hofv]
        have := StateC.memo_b_insert hm1 hwfe hins
        simpa only [absExpr_mk, absExprKind] using this

/-- `ConLeche/Kernel/DeclCheck.lean:197-199 Expr.constsResolveFFast`
(`:200-204` is its `@[csimp]` equation with the spec) —
**`decl_check::consts_resolve_f_fast` refines `Expr.constsResolveF`**, which is
what the nine call sites in `checker_base`, `parsed_c` and the four inductive
install modules consume. -/
theorem consts_resolve_f_fast_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hp : PinnedBasisNames) (hfe : FindAgree fe lfe)
    {e : expr.Expr} {b : Bool} (he : ExprWF e)
    (h : decl_check.consts_resolve_f_fast fe e = ok b) :
    b = ConLeche.Expr.constsResolveF lfe (absExpr e) := by
  rw [decl_check.consts_resolve_f_fast] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b0, memo'⟩ := p
  have hb : b0 = b := by simpa using h
  subst hb
  obtain ⟨lmemo', hl, -⟩ :=
    consts_resolve_f_go_refines hp hfe he memo memo' ∅ b0 (StateC.memo_b_new hnew) hgo
  have hspec := (ConLeche.Expr.constsResolveFGo_spec (fe := lfe) (absExpr e) ∅
    ConLeche.CRFMemoInv.empty).1
  rw [hl] at hspec
  exact hspec

/-- **What `Refine/CheckerBase.lean` was owed.**  That file may not import this
one (this one imports it), so it names `decl_check::consts_resolve_f_fast`'s
refinement as a `Prop` and takes it as a hypothesis; here is its proof, which
every `checker_base` restatement below feeds back in. -/
theorem constsResolveFSpec : CheckerBase.ConstsResolveFSpec :=
  fun _ lfe _ _ hrel hwf he h =>
    consts_resolve_f_fast_refines (lfe := lfe) CoreK.pinnedBasisNames
      (FindAgree.of_rel hrel hwf) he h

/-! ## 2. The member check and the projection chain — the task-#57 seam

`Cached/CheckerC.lean`'s projection route is

```text
let (cvj, mcv) ← checkProjLookupsF fe T ctorName lps nP nF i
let pty        ← checkProjTyF fe T ctorName lps mcv.type nP nF
checkProjShape pty cvj.type nP nF
let rhsA       ← checkProjRuleF (sharedOpsC mode fe) fe pty cvj lps nP nF i
checkProjIotaF mode (sharedOpsC mode fe) fe T ctorName lps cvj nP nF i
```

and `checkMemberValF` is the modeled route's per-member check.  All of them
are stated here, exactly, so that task #57's `IndRoutesSpec` can be proved
against them; every one is a Rust function of another module (`checker_base`
or `inductives::modeled`), and they are stated here at their
**`DeclCheck.lean` citation**, which is the pair this file is responsible for
recording.  Each is DESIGN.md §3.5's shape: exact result on success, nothing
on failure.

Task #58 deleted `decl_check.rs`'s dead second copy of `check_member_val` and
`check_proj_lookups`, so what used to be two lemmas each (`<f>_refines` and
`modeled_<f>_refines`, the same statement twice) is now one, at the plain
name. -/

/-! ### The model-companion name, and the block renaming

`DeclCheck.lean` spells `n.str "_model"` a dozen times and never names it; the
port does (DESIGN.md §3.3 forbids a `&str` parameter, so the literal is a
`const [u32; N]`).  Task #24's deviation 9 turns `checkMemberValF`'s local
`fun n => if blockNames.contains n then n.str "_model" else n` into a
one-method dictionary struct (`modeled::BlockRename` over
`expr_ops::NameToName`), because §3.4 forbids the closure. -/

/-- The Lean literal `modeled::model_str` spells as six code points. -/
theorem model_str_refines {v : alloc.vec.Vec Std.U32}
    (h : inductives.modeled.model_str = ok v) : absString v = "_model" := by
  rw [inductives.modeled.model_str] at h
  obtain ⟨s, hs, hv⟩ := bind_eq_ok_iff.mp h
  simp only [lift_eq, Result.ok.injEq] at hs
  subst hs
  have hvv : v.val = [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32] := by
    rw [code_points_val hv, Array.val_to_slice,
      inductives.modeled.model_str.MODEL, Array.make_val]
  rw [absString_eq, hvv]
  rfl

/-- `ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal` —
`modeled::model_of` is the cited `n.str "_model"`. -/
theorem model_of_refines {n r : name.Name} (hn : NameWF n)
    (h : inductives.modeled.model_of n = ok r) :
    absName r = (absName n).str "_model" ∧ NameWF r := by
  rw [inductives.modeled.model_of] at h
  simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨v, hv, hmk⟩ := h
  rw [inductives.modeled.model_str] at hv
  obtain ⟨s, hs, hv⟩ := bind_eq_ok_iff.mp hv
  simp only [lift_eq, Result.ok.injEq] at hs
  subst hs
  have hvv : v.val = [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32] := by
    rw [code_points_val hv, Array.val_to_slice,
      inductives.modeled.model_str.MODEL, Array.make_val]
  refine ⟨?_, NameWF.str hn ?_ hmk⟩
  · rw [Name.mk_str_refines hmk, absString_eq, hvv]; rfl
  · intro c hc; rw [hvv] at hc; fin_cases hc <;> decide

/-- A model list of six entries, listed out (the `Refine/CoreKShapes.lean`
`len_eq_four`/`len_eq_nine` pattern at the `"_model"` literal's length). -/
theorem len_eq_six {α : Type} {l : List α} (h : l.length = 6) :
    ∃ a0 a1 a2 a3 a4 a5, l = [a0, a1, a2, a3, a4, a5] := by
  rcases l with _ | ⟨a0, l⟩; · simp at h
  rcases l with _ | ⟨a1, l⟩; · simp at h
  rcases l with _ | ⟨a2, l⟩; · simp at h
  rcases l with _ | ⟨a3, l⟩; · simp at h
  rcases l with _ | ⟨a4, l⟩; · simp at h
  rcases l with _ | ⟨a5, l⟩; · simp at h
  rcases l with _ | ⟨a6, l⟩
  · exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩
  · simp at h

/-- `level::is_model_str` is the code-point list of `"_model"`. -/
theorem is_model_str_refines {s : alloc.vec.Vec Std.U32} {b : Bool}
    (h : level.is_model_str s = ok b) :
    b = decide (s.val = [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32]) := by
  rw [level.is_model_str] at h
  split at h
  · rename_i h6
    have hl : s.val.length = 6 := by have := alloc.vec.Vec.len_val s; scalar_tac
    obtain ⟨a0, a1, a2, a3, a4, a5, hs⟩ := len_eq_six hl
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
      show ∀ i : Nat, s[i]? = (s.val)[i]? from fun _ => rfl, hs,
      show ((0#usize : Std.Usize)).val = 0 from rfl,
      show ((1#usize : Std.Usize)).val = 1 from rfl,
      show ((2#usize : Std.Usize)).val = 2 from rfl,
      show ((3#usize : Std.Usize)).val = 3 from rfl,
      show ((4#usize : Std.Usize)).val = 4 from rfl,
      show ((5#usize : Std.Usize)).val = 5 from rfl,
      List.getElem?_cons_zero, List.getElem?_cons_succ, bind_tc_ok] at h
    rw [hs]
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
  · rename_i h6
    simp only [Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    intro hc
    have hv : (alloc.vec.Vec.len s).val = s.val.length := alloc.vec.Vec.len_val s
    rw [hc] at hv
    simp only [List.length_cons, List.length_nil] at hv
    exact h6 (by scalar_tac)

/-- `Name.isModelSuffix` at a `.str _ s` node, as a `Bool` test on the
payload. -/
theorem isModelSuffix_str (p : ConLeche.Name) (str : String) :
    ConLeche.Name.isModelSuffix (.str p str) = decide (str = "_model") := by
  unfold ConLeche.Name.isModelSuffix
  split <;> simp_all

/-- `ConLeche/Kernel/Level.lean:218-221 Name.isModelSuffix` —
**`level::name_is_model_suffix` refines it**: the cited `.str _ "_model"`
pattern, spelled over code points (DESIGN.md §3.3). -/
theorem name_is_model_suffix_refines {n : name.Name} {b : Bool} (hn : NameWF n)
    (h : level.name_is_model_suffix n = ok b) :
    b = ConLeche.Name.isModelSuffix (absName n) := by
  cases hn with
  | @anonymous n ha =>
    rw [name_anonymous_inv ha] at h ⊢
    rw [level.name_is_model_suffix] at h
    simp only [arc_deref_eq, name_node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h, absName_mk, absNameKind]
    rfl
  | @str pre s n hpre hs hmk =>
    obtain ⟨hh, rfl⟩ := mk_str_inv hmk
    rw [level.name_is_model_suffix] at h
    simp only [arc_deref_eq, name_node_kind, bind_tc_ok] at h
    have hp : (absString s = "_model") ↔
        s.val = [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32] := by
      rw [show ("_model" : String)
        = absCodes [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32] from rfl]
      exact absString_eq_codes hs (by decide) (by scalar_tac)
    simp only [absName_mk, absNameKind, isModelSuffix_str, hp]
    exact is_model_str_refines h
  | @num pre m n hpre hmk =>
    obtain ⟨hh, rfl⟩ := mk_num_inv hmk
    rw [level.name_is_model_suffix] at h
    simp only [arc_deref_eq, name_node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h, absName_mk, absNameKind]
    rfl

/-- The cited closure of `ConLeche/Kernel/DeclCheck.lean:489-490`. -/
def modelRename (bns : List ConLeche.Name) (n : ConLeche.Name) : ConLeche.Name :=
  if bns.contains n then n.str "_model" else n

/-- `ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF` —
**`BlockRename`'s one method is the cited local `f`**, which is what
`ExprOpsMeta.rename_consts_refines` consumes at `checkMemberValF`'s one call
site. -/
theorem block_rename_refines {bns : alloc.vec.Vec name.Name} (hbns : NamesWF bns) :
    ∀ n, NameWF n → ∀ r,
      (inductives.modeled.BlockRename.Insts.Con_ron_coreKernelExpr_opsNameToName).rename
          { block_names := bns } n = ok r →
        absName r = modelRename (absNames bns) (absName n) ∧ NameWF r := by
  intro n hn r h
  -- the dictionary's projection only reduces through the unifier
  have h2 : (do let b ← name.contains bns n
                if b then inductives.modeled.model_of n else name.dup n) = ok r := h
  clear h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h2
  have hbv := Name.contains_refines hbns hn hb
  rw [modelRename, ← hbv]
  cases b with
  | true => simp only [if_true] at h ⊢; exact model_of_refines hn h
  | false =>
    simp only [Bool.false_eq_true, if_false] at h ⊢
    rw [name_dup_eq] at h
    rw [← Result.ok_injective h]
    exact ⟨rfl, hn⟩

/-- `defnOf` is injective on hits: the probe's answer pins the lookup. -/
theorem defnOf_eq_some {x : Option ConLeche.ConstantInfo}
    {cvm : ConLeche.ConstantVal} {v : ConLeche.Expr}
    {hint : ConLeche.ReducibilityHint} (heq : defnOf x = some (cvm, v, hint)) :
    x = some (.defnInfo cvm v hint) := by
  unfold defnOf at heq
  split at heq <;> simp_all

open ConLeche.Cached in
/-- `ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF` at a run whose
`checkConstantValF` succeeded and whose three guards held: it is that run. -/
theorem checkMemberValF_run {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {bns : List ConLeche.Name}
    {cv cvA cvm : ConLeche.ConstantVal} {mval : ConLeche.Expr}
    {hint : ConLeche.ReducibilityHint} {lst lst1 : CState}
    (h0 : (ConLeche.checkConstantValF ops lfe cv).run lst = .ok (cvA, lst1))
    (h1 : cvA.name.isModelSuffix = false)
    (h2 : lfe.find? (cvA.name.str "_model") = some (.defnInfo cvm mval hint))
    (h3 : cvm.levelParams = cvA.levelParams)
    (h4 : (cvA.type.renameConsts (modelRename bns) == cvm.type) = true) :
    (ConLeche.checkMemberValF ops bns lfe cv).run lst = .ok (cvA, lst1) := by
  have hf : modelRename bns = fun n => if bns.contains n then n.str "_model" else n :=
    rfl
  rw [ConLeche.checkMemberValF]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure]
  rw [show (ConLeche.checkConstantValF ops lfe cv) lst = Except.ok (cvA, lst1)
    from h0]
  rw [hf] at h4
  simp only [h1, h2, h3, h4, Bool.false_eq_true, if_false, if_true]
  rfl

open ConLeche.Cached in
/-- `checkMemberValF` passes on what `checkConstantValF` threw. -/
theorem checkMemberValF_cv_err {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {bns : List ConLeche.Name} {cv : ConLeche.ConstantVal}
    {lst : CState} {le : ConLeche.CheckError}
    (h0 : (ConLeche.checkConstantValF ops lfe cv).run lst = .error le) :
    (ConLeche.checkMemberValF ops bns lfe cv).run lst = .error le := by
  rw [ConLeche.checkMemberValF]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ConLeche.checkConstantValF ops lfe cv) lst = Except.error le from h0]

open ConLeche.Cached in
/-- `checkMemberValF`'s model-shaped-name `throw` (`DeclCheck.lean:494`), the
one `invalid` of the cited function. -/
theorem checkMemberValF_model_name {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {bns : List ConLeche.Name}
    {cv cvA : ConLeche.ConstantVal} {lst lst1 : CState}
    (h0 : (ConLeche.checkConstantValF ops lfe cv).run lst = .ok (cvA, lst1))
    (h1 : cvA.name.isModelSuffix = true) :
    ∃ s, (ConLeche.checkMemberValF ops bns lfe cv).run lst
      = .error (.invalid s) := by
  rw [ConLeche.checkMemberValF]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ConLeche.checkConstantValF ops lfe cv) lst = Except.ok (cvA, lst1)
    from h0]
  simp only [h1, if_true]
  exact ⟨_, rfl⟩

open ConLeche.Cached in
/-- `checkMemberValF`'s no-route `throw` (`DeclCheck.lean:496-499`). -/
theorem checkMemberValF_no_route {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {bns : List ConLeche.Name}
    {cv cvA : ConLeche.ConstantVal} {lst lst1 : CState}
    (h0 : (ConLeche.checkConstantValF ops lfe cv).run lst = .ok (cvA, lst1))
    (h1 : cvA.name.isModelSuffix = false)
    (h2 : defnOf (lfe.find? (cvA.name.str "_model")) = none) :
    ∃ s, (ConLeche.checkMemberValF ops bns lfe cv).run lst
      = .error (.notImplemented s) := by
  rw [ConLeche.checkMemberValF]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ConLeche.checkConstantValF ops lfe cv) lst = Except.ok (cvA, lst1)
    from h0]
  simp only [h1, Bool.false_eq_true, if_false]
  cases hx : lfe.find? (cvA.name.str "_model") with
  | none => exact ⟨_, rfl⟩
  | some ci =>
    rw [hx] at h2
    cases ci with
    | axiomInfo _ => exact ⟨_, rfl⟩
    | defnInfo _ _ _ => simp [defnOf] at h2
    | thmInfo _ _ => exact ⟨_, rfl⟩
    | indInfo _ _ => exact ⟨_, rfl⟩
    | ctorInfo _ _ _ => exact ⟨_, rfl⟩
    | recInfo _ _ _ _ => exact ⟨_, rfl⟩
    | projInfo _ => exact ⟨_, rfl⟩

open ConLeche.Cached in
/-- `checkMemberValF`'s model-level `throw` (`DeclCheck.lean:501`). -/
theorem checkMemberValF_lps {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {bns : List ConLeche.Name}
    {cv cvA cvm : ConLeche.ConstantVal} {mval : ConLeche.Expr}
    {hint : ConLeche.ReducibilityHint} {lst lst1 : CState}
    (h0 : (ConLeche.checkConstantValF ops lfe cv).run lst = .ok (cvA, lst1))
    (h1 : cvA.name.isModelSuffix = false)
    (h2 : lfe.find? (cvA.name.str "_model") = some (.defnInfo cvm mval hint))
    (h3 : cvm.levelParams ≠ cvA.levelParams) :
    ∃ s, (ConLeche.checkMemberValF ops bns lfe cv).run lst
      = .error (.notImplemented s) := by
  rw [ConLeche.checkMemberValF]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ConLeche.checkConstantValF ops lfe cv) lst = Except.ok (cvA, lst1)
    from h0]
  simp only [h1, h2, Bool.false_eq_true, if_false]
  rw [if_neg h3]
  exact ⟨_, rfl⟩

open ConLeche.Cached in
/-- `checkMemberValF`'s model-type `throw` (`DeclCheck.lean:503-505`). -/
theorem checkMemberValF_ty {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {bns : List ConLeche.Name}
    {cv cvA cvm : ConLeche.ConstantVal} {mval : ConLeche.Expr}
    {hint : ConLeche.ReducibilityHint} {lst lst1 : CState}
    (h0 : (ConLeche.checkConstantValF ops lfe cv).run lst = .ok (cvA, lst1))
    (h1 : cvA.name.isModelSuffix = false)
    (h2 : lfe.find? (cvA.name.str "_model") = some (.defnInfo cvm mval hint))
    (h3 : cvm.levelParams = cvA.levelParams)
    (h4 : (cvA.type.renameConsts (modelRename bns) == cvm.type) = false) :
    ∃ s, (ConLeche.checkMemberValF ops bns lfe cv).run lst
      = .error (.notImplemented s) := by
  have hf : modelRename bns = fun n => if bns.contains n then n.str "_model" else n :=
    rfl
  rw [ConLeche.checkMemberValF]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ConLeche.checkConstantValF ops lfe cv) lst = Except.ok (cvA, lst1)
    from h0]
  rw [hf] at h4
  simp only [h1, h2, h3, h4, Bool.false_eq_true, if_false, if_true]
  exact ⟨_, rfl⟩

/-- `ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF` —
**`inductives::modeled::check_member_val`**: the common `checkConstantVal`, no
model-shaped name of its own, and the model companion the in-process modeller
generated — same level parameters, and a type that is this member's with the
block's names renamed to their companions'. -/
theorem check_member_val_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe : fenv.FEnv} {cv : env.ConstantVal}
    {out : core.result.Result env.ConstantVal core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hbn : NamesWF block_names)
    (hcv : ConstantValWF cv)
    (h : inductives.modeled.check_member_val mode st block_names fe cv
      = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok cv' =>
        ∃ lst', (ConLeche.checkMemberValF (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
              (absNames block_names) lfe (absConstantVal cv)).run lst
            = .ok (absConstantVal cv', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv'
      | .Err e =>
        ErrSim e ((ConLeche.checkMemberValF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
            (absNames block_names) lfe (absConstantVal cv)).run lst) := by
  intro lst lfe hsr hfr
  rw [inductives.modeled.check_member_val] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err er =>
    -- `checker_base::check_constant_val` threw, and the cited `do` passes it on
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    exact ErrSim.trans
      (CheckerBase.check_constant_val_refines hfuel hk constsResolveFSpec hsw hfw
        hcv hq lst lfe hsr hfr)
      (fun le hle => checkMemberValF_cv_err hle)
  | Ok cv_a =>
    obtain ⟨lst1, hrun1, hsr1, hsw1, hcaw⟩ :=
      CheckerBase.check_constant_val_refines hfuel hk constsResolveFSpec hsw hfw
        hcv hq lst lfe hsr hfr
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbabs := name_is_model_suffix_refines hcaw.1 hb
    split at h
    · -- `modeled.rs:1625` ← `DeclCheck.lean:494`
      rename_i hbt
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      obtain ⟨ls, hls⟩ := checkMemberValF_model_name (bns := absNames block_names)
        hrun1 (by rw [show (absConstantVal cv_a).name = absName cv_a.name from rfl,
          ← hbabs]; exact hbt)
      exact errSim_invalid hce rfl hls
    · rename_i hbf
      simp only [Bool.not_eq_true] at hbf
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hnabs, hnwf⟩ := model_of_refines hcaw.1 hn
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hoabs, howf⟩ := defn_probe_refines (FindAgree.of_rel hfr hfw)
        (FindWF.of_wf hfw) hnwf ho
      have hmodelName : (absConstantVal cv_a).name.isModelSuffix = false := by
        rw [show (absConstantVal cv_a).name = absName cv_a.name from rfl, ← hbabs]
        exact hbf
      have hnameEq : absName n = (absConstantVal cv_a).name.str "_model" := by
        rw [hnabs]; rfl
      cases o with
      | none =>
        -- `modeled.rs:1629` ← `DeclCheck.lean:496`
        obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        obtain ⟨ls, hls⟩ := checkMemberValF_no_route (bns := absNames block_names)
          hrun1 hmodelName (by rw [← hnameEq]; simpa using hoabs.symm)
        exact errSim_notImplemented hce rfl hls
      | some dq =>
        obtain ⟨cv1, v1, hint1⟩ := dq
        obtain ⟨hcv1wf, -⟩ := howf cv1 v1 hint1 rfl
        have hfind : lfe.find? ((absConstantVal cv_a).name.str "_model")
            = some (.defnInfo (absConstantVal cv1) (absExpr v1) (absHint hint1)) := by
          rw [show (absConstantVal cv_a).name.str "_model" = absName n by
            rw [hnabs]; rfl]
          exact defnOf_eq_some hoabs.symm
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1abs := names_beq_refines hcv1wf.2.1 hcaw.2.1 hb1
        split at h
        · rename_i hb1t
          subst hb1t
          obtain ⟨renamed, hren, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hrabs, hrwf⟩ := ExprOps.rename_consts_refines
            (modelRename (absNames block_names)) (block_rename_refines hbn)
            hcaw.2.2 hren
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2abs := Expr.beq_refines hrwf hcv1wf.2.2 hb2
          split at h
          · rename_i hb2t
            subst hb2t
            obtain ⟨hout, rfl⟩ := ok_outS h
            subst hout
            refine ⟨lst1, ?_, hsr1, hsw1, hcaw⟩
            refine checkMemberValF_run hrun1 ?_ hfind ?_ ?_
            · exact hmodelName
            · show absNames cv1.level_params = absNames cv_a.level_params
              simpa using hb1abs.symm
            · rw [show (absConstantVal cv_a).type = absExpr cv_a.ty from rfl,
                show (absConstantVal cv1).type = absExpr cv1.ty from rfl,
                ← hrabs, ← decide_eq_beq]
              exact hb2abs.symm
          · -- `modeled.rs:1639` ← `DeclCheck.lean:503`
            rename_i hb2f
            obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, -⟩ := err_outS h
            subst hout
            obtain ⟨ls, hls⟩ := checkMemberValF_ty (bns := absNames block_names)
              hrun1 hmodelName hfind
              (by show absNames cv1.level_params = absNames cv_a.level_params
                  simpa using hb1abs.symm)
              (by rw [show (absConstantVal cv_a).type = absExpr cv_a.ty from rfl,
                    show (absConstantVal cv1).type = absExpr cv1.ty from rfl,
                    ← hrabs, ← decide_eq_beq, ← hb2abs]
                  simpa using hb2f)
            exact errSim_notImplemented hce rfl hls
        · -- `modeled.rs:1634` ← `DeclCheck.lean:501`
          rename_i hb1f
          obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          obtain ⟨ls, hls⟩ := checkMemberValF_lps (bns := absNames block_names)
            hrun1 hmodelName hfind
            (by show absNames cv1.level_params ≠ absNames cv_a.level_params
                simpa [hb1abs] using hb1f)
          exact errSim_notImplemented hce rfl hls

/-! ### The projection lookups (`DeclCheck.lean:729-746`)

Three small bridges first: two `ite` eliminators that work up to definitional
equality (the port's tuple-pattern binders defeat `split`), the `ctorOf`
inversion, and `Refine/BasisPins.lean`'s pinned-`Eq` guard at this section's
environment hypotheses. -/

/-- An `if` taken on the left, eliminated **up to definitional equality**.
Charon puts a tuple-pattern binder (`let (cv, i1, i2) := cq`) between the
equation and the `if`, and neither `split` nor `simp`'s matcher reduction sees
through it while unification does; the elimination therefore has to go through
an `exact`, which is what these two are for. -/
theorem ite_pos_eq {α : Type} {c : Prop} [Decidable c] {a b x : α}
    (hc : c) (h : (if c then a else b) = x) : a = x := by
  rw [if_pos hc] at h; exact h

/-- The other side of `ite_pos_eq`. -/
theorem ite_neg_eq {α : Type} {c : Prop} [Decidable c] {a b x : α}
    (hc : ¬ c) (h : (if c then a else b) = x) : b = x := by
  rw [if_neg hc] at h; exact h

/-- `ctorOf` is injective on hits: the probe's answer pins the lookup. -/
theorem ctorOf_eq_some {x : Option ConLeche.ConstantInfo}
    {cvj : ConLeche.ConstantVal} {nP nF : Nat}
    (heq : ctorOf x = some (cvj, nP, nF)) :
    x = some (.ctorInfo cvj nP nF) := by
  unfold ctorOf at heq
  split at heq <;> simp_all

/-- `Refine/BasisPins.lean`'s `eq_basis_pinned_refines`, at the *find*
hypotheses this section's statements carry (`FindAgree`/`FindWF` instead of
task #46's `FEnvRel`/`FEnvWF`): `basis_pins::eq_basis_pinned` reads the index
through `fenv::find` alone, which is all its proof needs. -/
theorem eq_basis_pinned_find_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {b : Bool} (hfe : FindAgree fe lfe) (hwf : FindWF fe)
    (h : basis_pins.eq_basis_pinned fe = ok b) :
    b = decide (lfe.find? ConLeche.eqName = some ConLeche.eqA) := by
  rw [basis_pins.eq_basis_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, hfind, h⟩ := h
  obtain ⟨hname, hnwf⟩ := BasisNames.eq_name_refines hn
  have hf := hfe n o hnwf hfind
  rw [hname] at hf
  cases o with
  | none =>
    simp only [Option.map_none] at hf
    rw [← hf]
    simp only [Result.ok.injEq] at h
    simp [← h]
  | some ci =>
    simp only [Option.map_some] at hf
    rw [← hf, BasisPins.is_pinned_eq_basis_refines (hwf n ci hnwf hfind) h]
    simp

open ConLeche.Cached in
/-- `ConLeche/Kernel/DeclCheck.lean:729-746 checkProjLookupsF` at a run whose
seven lookups and guards all held: it is that run, and it leaves the state
where it found it (the cited Lean is `ops`-free). -/
theorem checkProjLookupsF_run {lfe : ConLeche.FEnv} {T ctorName : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nF i : Nat} {cvj mcv : ConLeche.ConstantVal}
    {mval : ConLeche.Expr} {hint : ConLeche.ReducibilityHint} {lst : CState}
    (h1 : lfe.find? ctorName = some (.ctorInfo cvj nP nF))
    (h2 : lfe.find? (ConLeche.projModelName T i) = some (.defnInfo mcv mval hint))
    (h3 : mcv.levelParams = lps)
    (h4 : (lfe.find? (ConLeche.projFnName T i)).isNone = true)
    (h5 : (lfe.find? T).isSome = true)
    (h6 : lfe.find? ConLeche.eqName = some ConLeche.eqA) :
    (ConLeche.checkProjLookupsF (m := CheckCM) lfe T ctorName lps nP nF i).run lst
      = .ok ((cvj, mcv), lst) := by
  rw [ConLeche.checkProjLookupsF]
  simp only [h1, h2, h3, h4, h5, h6, StateT.run, Bind.bind, Pure.pure,
    StateT.pure, Except.pure, and_self, if_true]

open ConLeche.Cached in
/-- `checkProjLookupsF`'s first `throw` (`DeclCheck.lean:732`): the
constructor is not stored (or is stored as something else). -/
theorem checkProjLookupsF_ctor_none {lfe : ConLeche.FEnv} {T ctorName : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nF i : Nat} {lst : CState}
    (h1 : ctorOf (lfe.find? ctorName) = none) :
    (ConLeche.checkProjLookupsF (m := CheckCM) lfe T ctorName lps nP nF i).run lst
      = .error (.notImplemented "projection constructor not stored") := by
  rw [ConLeche.checkProjLookupsF]
  simp only [StateT.run, Bind.bind]
  cases hx : lfe.find? ctorName with
  | none => rfl
  | some ci =>
    rw [hx] at h1
    cases ci with
    | axiomInfo _ => rfl
    | defnInfo _ _ _ => rfl
    | thmInfo _ _ => rfl
    | indInfo _ _ => rfl
    | ctorInfo _ _ _ => simp [ctorOf] at h1
    | recInfo _ _ _ _ => rfl
    | projInfo _ => rfl

open ConLeche.Cached in
/-- `checkProjLookupsF`'s arity `throw` (`DeclCheck.lean:734`), which the port
splits into two `else if` arms carrying the same message (task #67's census:
two Rust sites, one cited `throw`, the same kind). -/
theorem checkProjLookupsF_arity {lfe : ConLeche.FEnv} {T ctorName : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nF cnP cnF i : Nat} {cvj : ConLeche.ConstantVal}
    {lst : CState} (h1 : lfe.find? ctorName = some (.ctorInfo cvj cnP cnF))
    (h2 : ¬ (cnP = nP ∧ cnF = nF)) :
    (ConLeche.checkProjLookupsF (m := CheckCM) lfe T ctorName lps nP nF i).run lst
      = .error (.notImplemented "projection constructor arity mismatch") := by
  rw [ConLeche.checkProjLookupsF]
  simp only [h1, StateT.run, Bind.bind]
  rw [if_neg h2]
  rfl

open ConLeche.Cached in
/-- `checkProjLookupsF`'s missing-model `throw` (`DeclCheck.lean:737`). -/
theorem checkProjLookupsF_model_none {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name} {nP nF i : Nat}
    {cvj : ConLeche.ConstantVal} {lst : CState}
    (h1 : lfe.find? ctorName = some (.ctorInfo cvj nP nF))
    (h2 : defnOf (lfe.find? (ConLeche.projModelName T i)) = none) :
    (ConLeche.checkProjLookupsF (m := CheckCM) lfe T ctorName lps nP nF i).run lst
      = .error (.notImplemented "missing projection model") := by
  rw [ConLeche.checkProjLookupsF]
  simp only [h1, StateT.run, Bind.bind, and_self,
    if_true]
  cases hx : lfe.find? (ConLeche.projModelName T i) with
  | none => rfl
  | some ci =>
    rw [hx] at h2
    cases ci with
    | axiomInfo _ => rfl
    | defnInfo _ _ _ => simp [defnOf] at h2
    | thmInfo _ _ => rfl
    | indInfo _ _ => rfl
    | ctorInfo _ _ _ => rfl
    | recInfo _ _ _ _ => rfl
    | projInfo _ => rfl

open ConLeche.Cached in
/-- `checkProjLookupsF`'s model-level `throw` (`DeclCheck.lean:739`). -/
theorem checkProjLookupsF_lps {lfe : ConLeche.FEnv} {T ctorName : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nF i : Nat} {cvj mcv : ConLeche.ConstantVal}
    {mval : ConLeche.Expr} {hint : ConLeche.ReducibilityHint} {lst : CState}
    (h1 : lfe.find? ctorName = some (.ctorInfo cvj nP nF))
    (h2 : lfe.find? (ConLeche.projModelName T i) = some (.defnInfo mcv mval hint))
    (h3 : mcv.levelParams ≠ lps) :
    (ConLeche.checkProjLookupsF (m := CheckCM) lfe T ctorName lps nP nF i).run lst
      = .error (.notImplemented "projection model level mismatch") := by
  rw [ConLeche.checkProjLookupsF]
  simp only [h1, h2, StateT.run, Bind.bind, and_self,
    if_true]
  rw [if_neg h3]
  rfl

open ConLeche.Cached in
/-- `checkProjLookupsF`'s taken-name `throw` (`DeclCheck.lean:741`), the one
`invalid` of the cited function. -/
theorem checkProjLookupsF_name_taken {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name} {nP nF i : Nat}
    {cvj mcv : ConLeche.ConstantVal} {mval : ConLeche.Expr}
    {hint : ConLeche.ReducibilityHint} {lst : CState}
    (h1 : lfe.find? ctorName = some (.ctorInfo cvj nP nF))
    (h2 : lfe.find? (ConLeche.projModelName T i) = some (.defnInfo mcv mval hint))
    (h3 : mcv.levelParams = lps)
    (h4 : (lfe.find? (ConLeche.projFnName T i)).isNone = false) :
    (ConLeche.checkProjLookupsF (m := CheckCM) lfe T ctorName lps nP nF i).run lst
      = .error (.invalid "projection name taken") := by
  rw [ConLeche.checkProjLookupsF]
  simp only [h1, h2, h3, h4, StateT.run, Bind.bind, StateT.bind, Except.bind,
    and_self, if_true, Bool.false_eq_true, if_false]
  rfl

open ConLeche.Cached in
/-- `checkProjLookupsF`'s missing-parent `throw` (`DeclCheck.lean:743`). -/
theorem checkProjLookupsF_parent {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name} {nP nF i : Nat}
    {cvj mcv : ConLeche.ConstantVal} {mval : ConLeche.Expr}
    {hint : ConLeche.ReducibilityHint} {lst : CState}
    (h1 : lfe.find? ctorName = some (.ctorInfo cvj nP nF))
    (h2 : lfe.find? (ConLeche.projModelName T i) = some (.defnInfo mcv mval hint))
    (h3 : mcv.levelParams = lps)
    (h4 : (lfe.find? (ConLeche.projFnName T i)).isNone = true)
    (h5 : (lfe.find? T).isSome = false) :
    (ConLeche.checkProjLookupsF (m := CheckCM) lfe T ctorName lps nP nF i).run lst
      = .error (.notImplemented "projection parent not stored") := by
  rw [ConLeche.checkProjLookupsF]
  simp only [h1, h2, h3, h4, h5, StateT.run, Bind.bind, StateT.bind, Except.bind,
    and_self, if_true, Bool.false_eq_true, if_false]
  rfl

open ConLeche.Cached in
/-- `checkProjLookupsF`'s pinned-`Eq` `throw` (`DeclCheck.lean:745`). -/
theorem checkProjLookupsF_eq_pin {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name} {nP nF i : Nat}
    {cvj mcv : ConLeche.ConstantVal} {mval : ConLeche.Expr}
    {hint : ConLeche.ReducibilityHint} {lst : CState}
    (h1 : lfe.find? ctorName = some (.ctorInfo cvj nP nF))
    (h2 : lfe.find? (ConLeche.projModelName T i) = some (.defnInfo mcv mval hint))
    (h3 : mcv.levelParams = lps)
    (h4 : (lfe.find? (ConLeche.projFnName T i)).isNone = true)
    (h5 : (lfe.find? T).isSome = true)
    (h6 : lfe.find? ConLeche.eqName ≠ some ConLeche.eqA) :
    (ConLeche.checkProjLookupsF (m := CheckCM) lfe T ctorName lps nP nF i).run lst
      = .error (.notImplemented
          "projection iota requires the pinned Eq basis") := by
  rw [ConLeche.checkProjLookupsF]
  simp only [h1, h2, h3, h4, h5, StateT.run, Bind.bind,
    and_self, if_true]
  rw [if_neg h6]
  rfl

/-- `ConLeche/Kernel/DeclCheck.lean:729-746 checkProjLookupsF` —
**`inductives::modeled::check_proj_lookups`**: the projection install's five
environment lookups — the stored constructor at the expected arity, the
field's projection model companion at the block's level parameters, a free
projection-function name, the stored parent, and the pinned `Eq` basis.  No
state: the cited Lean is `ops`-free, so the run leaves `lst` alone. -/
theorem check_proj_lookups_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f i : Std.U64}
    {out : core.result.Result (env.ConstantVal × env.ConstantVal)
      core_types.CheckError}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : inductives.modeled.check_proj_lookups fe t ctor_name lps n_p n_f i
      = ok out) :
    ∀ lst : ConLeche.Cached.CState,
      match out with
      | .Ok (cvj, mcv) =>
        (ConLeche.checkProjLookupsF (m := ConLeche.Cached.CheckCM) lfe
            (absName t) (absName ctor_name) (absNames lps)
            n_p.val n_f.val i.val).run lst
          = .ok ((absConstantVal cvj, absConstantVal mcv), lst)
        ∧ ConstantValWF cvj ∧ ConstantValWF mcv
      | .Err e =>
        ErrSim e ((ConLeche.checkProjLookupsF (m := ConLeche.Cached.CheckCM) lfe
            (absName t) (absName ctor_name) (absNames lps)
            n_p.val n_f.val i.val).run lst) := by
  intro lst
  rw [inductives.modeled.check_proj_lookups] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ctor_probe_refines hfe hwf hc ho
  cases o with
  | none =>
    -- `modeled.rs:1894` ← `DeclCheck.lean:732`
    simp only [bind_eq_ok_iff] at h
    obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
    cases out with
    | Ok q => simp at h
    | Err e =>
      exact errSim_notImplemented hce (by simpa using h)
        (checkProjLookupsF_ctor_none (by simpa using hoabs.symm))
  | some cq =>
    obtain ⟨cv, cn_p, cn_f⟩ := cq
    have hcvwf := howf cv cn_p cn_f rfl
    have hctor : lfe.find? (absName ctor_name)
        = some (.ctorInfo (absConstantVal cv) cn_p.val cn_f.val) :=
      ctorOf_eq_some hoabs.symm
    by_cases hp : cn_p.val = n_p.val
    case neg =>
      -- `modeled.rs:1898`, the first of the two arms the port splits the
      -- cited `unless cnP = nP ∧ cnF = nF` into
      replace h := ite_pos_eq (c := ((cn_p != n_p) = true))
        (by simp only [bne_iff_ne, ne_eq]; scalar_tac) h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
      cases out with
      | Ok q => simp at h
      | Err e =>
        exact errSim_notImplemented hce (by simpa using h)
          (checkProjLookupsF_arity hctor (fun hq => hp hq.1))
    by_cases hf : cn_f.val = n_f.val
    case neg =>
      -- `modeled.rs:1898`, the second arm, at the same cited `throw`
      replace h := ite_neg_eq (c := ((cn_p != n_p) = true))
        (by simp only [bne_iff_ne, ne_eq, Decidable.not_not]; scalar_tac) h
      replace h := ite_pos_eq (c := ((cn_f != n_f) = true))
        (by simp only [bne_iff_ne, ne_eq]; scalar_tac) h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
      cases out with
      | Ok q => simp at h
      | Err e =>
        exact errSim_notImplemented hce (by simpa using h)
          (checkProjLookupsF_arity hctor (fun hq => hf hq.2))
    rw [hp, hf] at hctor
    replace h := ite_neg_eq (c := ((cn_p != n_p) = true))
      (by simp only [bne_iff_ne, ne_eq, Decidable.not_not]; scalar_tac) h
    replace h := ite_neg_eq (c := ((cn_f != n_f) = true))
      (by simp only [bne_iff_ne, ne_eq, Decidable.not_not]; scalar_tac) h
    obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hnabs, hnwf⟩ := proj_model_name_refines ht hn
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho1abs, ho1wf⟩ := defn_probe_refines hfe hwf hnwf ho1
    cases o1 with
    | none =>
      -- `modeled.rs:1903` ← `DeclCheck.lean:737`
      simp only [bind_eq_ok_iff] at h
      obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
      cases out with
      | Ok q => simp at h
      | Err e =>
        exact errSim_notImplemented hce (by simpa using h)
          (checkProjLookupsF_model_none hctor
            (by rw [← hnabs]; simpa using ho1abs.symm))
    | some dq =>
      obtain ⟨cv1, v1, hint1⟩ := dq
      obtain ⟨hcv1wf, -⟩ := ho1wf cv1 v1 hint1 rfl
      have hmodel : lfe.find? (ConLeche.projModelName (absName t) i.val)
          = some (.defnInfo (absConstantVal cv1) (absExpr v1)
              (absHint hint1)) := by
        rw [← hnabs]; exact defnOf_eq_some ho1abs.symm
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      have hbabs := names_beq_refines hcv1wf.2.1 hlps hb
      split at h
      · rename_i hbt
        subst hbt
        have hlpseq : (absConstantVal cv1).levelParams = absNames lps := by
          show absNames cv1.level_params = absNames lps
          simpa using hbabs.symm
        obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hn1abs, hn1wf⟩ := proj_fn_name_refines ht hn1
        obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
        have ho2abs := find_isSome hfe hn1wf ho2
        rw [hn1abs] at ho2abs
        by_cases ho2f : core.option.Option.is_some o2 = true
        · -- `modeled.rs:1911` ← `DeclCheck.lean:741`, the one `invalid`
          replace h := ite_pos_eq (c := (core.option.Option.is_some o2 = true))
            ho2f h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
          cases out with
          | Ok q => simp at h
          | Err e =>
            refine errSim_invalid hce (by simpa using h)
              (checkProjLookupsF_name_taken hctor hmodel hlpseq ?_)
            have hs : (lfe.find? (ConLeche.projFnName (absName t) i.val)).isSome
                = true := by rw [← ho2abs]; exact ho2f
            cases hx : lfe.find? (ConLeche.projFnName (absName t) i.val) with
            | none => rw [hx] at hs; simp at hs
            | some ci => simp
        · replace h := ite_neg_eq (c := (core.option.Option.is_some o2 = true))
            ho2f h
          have hnone : (lfe.find? (ConLeche.projFnName (absName t) i.val)).isNone
              = true := by
            have hs : (lfe.find? (ConLeche.projFnName (absName t) i.val)).isSome
                = false := by rw [← ho2abs]; simpa using ho2f
            cases hx : lfe.find? (ConLeche.projFnName (absName t) i.val) with
            | none => simp
            | some ci => rw [hx] at hs; simp at hs
          obtain ⟨o3, ho3, h⟩ := bind_eq_ok_iff.mp h
          have ho3abs := find_isSome hfe ht ho3
          by_cases ho3f : core.option.Option.is_none o3 = true
          · -- `modeled.rs:1915` ← `DeclCheck.lean:743`
            replace h := ite_pos_eq
              (c := (core.option.Option.is_none o3 = true)) ho3f h
            simp only [bind_eq_ok_iff] at h
            obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
            cases out with
            | Ok q => simp at h
            | Err e =>
              refine errSim_notImplemented hce (by simpa using h)
                (checkProjLookupsF_parent hctor hmodel hlpseq hnone ?_)
              rw [← ho3abs]
              cases o3 with
              | none => simp [core.option.Option.is_some]
              | some ci => simp [core.option.Option.is_none] at ho3f
          · replace h := ite_neg_eq
              (c := (core.option.Option.is_none o3 = true)) ho3f h
            have hsome : (lfe.find? (absName t)).isSome = true := by
              rw [← ho3abs]
              cases o3 with
              | none => simp [core.option.Option.is_none] at ho3f
              | some ci => simp
            obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
            have hb3abs := eq_basis_pinned_find_refines hfe hwf hb3
            split at h
            · rename_i hb3t
              subst hb3t
              simp only [Result.ok.injEq] at h
              subst h
              exact ⟨checkProjLookupsF_run hctor hmodel hlpseq hnone hsome
                (by simpa using hb3abs.symm), hcvwf, hcv1wf⟩
            · -- `modeled.rs:1919` ← `DeclCheck.lean:745`
              rename_i hb3f
              simp only [bind_eq_ok_iff] at h
              obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
              cases out with
              | Ok q => simp at h
              | Err e =>
                exact errSim_notImplemented hce (by simpa using h)
                  (checkProjLookupsF_eq_pin hctor hmodel hlpseq hnone hsome
                    (by simpa [hb3abs] using hb3f))
      · -- `modeled.rs:1907` ← `DeclCheck.lean:739`
        rename_i hbf
        simp only [bind_eq_ok_iff] at h
        obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
        cases out with
        | Ok q => simp at h
        | Err e =>
          refine errSim_notImplemented hce (by simpa using h)
            (checkProjLookupsF_lps hctor hmodel ?_)
          show absNames cv1.level_params ≠ absNames lps
          simpa [hbabs] using hbf

/-! ### The two projection renaming dictionaries, as steps

`ConLeche/Kernel/Inductives/Modeled.lean:457-473`'s `projBack` and `projFwd`
are two `Name → Name` closures; §3.4 forbids a closure, so the port has a
one-method dictionary for each (`modeled::ProjBack`, `modeled::ProjFwd` over
`expr_ops::NameToName`), and the cited `(List.range nF).find? …` is an index
recursion (`find_proj_model_slot`, `find_proj_fn_slot`).  The four lemmas are
`kernel::inductives::modeled`'s, i.e. task #57's; they are proved **here as
steps**, the way `Refine/CheckerPins.lean`'s `one_level_step` and
`Refine/TrustAxioms.lean`'s copies are, because `check_proj_ty_refines` below
cannot be stated without them and this file may not import a sibling that
does not exist yet.

Charon extracts both finders `partial_fixpoint`, so neither has an induction
principle (task #20's ruling); each is a strong induction on the `Nat` measure
`n_f - j` through the unfolding equation, the `Refine/ExprOpsSpine.lean`
`mk_app_n_from_refines` shape. -/

/-- `ConLeche/Kernel/Inductives/Modeled.lean:461` —
**`modeled::find_proj_model_slot` is the cited
`(List.range nF).find? (fun j => n == projModelName T j)` resumed at `j`.** -/
theorem find_proj_model_slot_step (N : Nat) :
    ∀ (t n : name.Name) (n_f j : Std.U64) (o : Option Std.U64),
      n_f.val - j.val = N → NameWF t → NameWF n →
      inductives.modeled.find_proj_model_slot t n_f n j = ok o →
      o.map (·.val) = (List.range' j.val (n_f.val - j.val)).find?
        (fun k => absName n == ConLeche.projModelName (absName t) k) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t n n_f j o hN ht hn h
    rw [inductives.modeled.find_proj_model_slot.eq_def] at h
    split at h
    · rename_i hge
      have hz : n_f.val - j.val = 0 := by scalar_tac
      rw [hz]
      simp only [Result.ok.injEq] at h
      rw [← h]
      simp
    · rename_i hge
      have hlt : j.val < n_f.val := by scalar_tac
      obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hn1abs, hn1wf⟩ := proj_model_name_refines ht hn1
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      have hbabs := Name.name_beq_exact' hn hn1wf hb
      rw [hn1abs] at hbabs
      have hpj : (absName n == ConLeche.projModelName (absName t) j.val) = b := by
        rw [← decide_eq_beq]; exact hbabs.symm
      have hr : n_f.val - j.val = (n_f.val - (j.val + 1)) + 1 := by omega
      rw [hr, List.range'_succ]
      cases b with
      | true =>
        have ho : o = some j := (Result.ok_injective h).symm
        subst ho
        simp [hpj]
      | false =>
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        have hi1v : i1.val = j.val + 1 := HashMap.uscalar_add_eq hi1
        have hrec := ih (n_f.val - i1.val) (by omega) t n n_f i1 o rfl ht hn h
        rw [hi1v] at hrec
        simp [hpj, hrec]

/-- `ConLeche/Kernel/Inductives/Modeled.lean:461` — the `j = 0` wrapper. -/
theorem find_proj_model_slot_refines {t n : name.Name} {n_f : Std.U64}
    {o : Option Std.U64} (ht : NameWF t) (hn : NameWF n)
    (h : inductives.modeled.find_proj_model_slot t n_f n 0#u64 = ok o) :
    o.map (·.val) = (List.range n_f.val).find?
      (fun k => absName n == ConLeche.projModelName (absName t) k) := by
  have hs := find_proj_model_slot_step _ t n n_f 0#u64 o rfl ht hn h
  simpa [List.range_eq_range'] using hs

/-- `ConLeche/Kernel/Inductives/Modeled.lean:470` —
**`modeled::find_proj_fn_slot` is the cited
`(List.range nF).find? (fun j => n == projFnName T j)` resumed at `j`.** -/
theorem find_proj_fn_slot_step (N : Nat) :
    ∀ (t n : name.Name) (n_f j : Std.U64) (o : Option Std.U64),
      n_f.val - j.val = N → NameWF t → NameWF n →
      inductives.modeled.find_proj_fn_slot t n_f n j = ok o →
      o.map (·.val) = (List.range' j.val (n_f.val - j.val)).find?
        (fun k => absName n == ConLeche.projFnName (absName t) k) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t n n_f j o hN ht hn h
    rw [inductives.modeled.find_proj_fn_slot.eq_def] at h
    split at h
    · rename_i hge
      have hz : n_f.val - j.val = 0 := by scalar_tac
      rw [hz]
      simp only [Result.ok.injEq] at h
      rw [← h]
      simp
    · rename_i hge
      have hlt : j.val < n_f.val := by scalar_tac
      obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hn1abs, hn1wf⟩ := proj_fn_name_refines ht hn1
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      have hbabs := Name.name_beq_exact' hn hn1wf hb
      rw [hn1abs] at hbabs
      have hpj : (absName n == ConLeche.projFnName (absName t) j.val) = b := by
        rw [← decide_eq_beq]; exact hbabs.symm
      have hr : n_f.val - j.val = (n_f.val - (j.val + 1)) + 1 := by omega
      rw [hr, List.range'_succ]
      cases b with
      | true =>
        have ho : o = some j := (Result.ok_injective h).symm
        subst ho
        simp [hpj]
      | false =>
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        have hi1v : i1.val = j.val + 1 := HashMap.uscalar_add_eq hi1
        have hrec := ih (n_f.val - i1.val) (by omega) t n n_f i1 o rfl ht hn h
        rw [hi1v] at hrec
        simp [hpj, hrec]

/-- `ConLeche/Kernel/Inductives/Modeled.lean:470` — the `j = 0` wrapper. -/
theorem find_proj_fn_slot_refines {t n : name.Name} {n_f : Std.U64}
    {o : Option Std.U64} (ht : NameWF t) (hn : NameWF n)
    (h : inductives.modeled.find_proj_fn_slot t n_f n 0#u64 = ok o) :
    o.map (·.val) = (List.range n_f.val).find?
      (fun k => absName n == ConLeche.projFnName (absName t) k) := by
  have hs := find_proj_fn_slot_step _ t n n_f 0#u64 o rfl ht hn h
  simpa [List.range_eq_range'] using hs

/-- `ConLeche/Kernel/Inductives/Modeled.lean:457-464 projBack` —
**`ProjBack`'s one method is the cited closure**, in the form
`ExprOpsMeta.rename_consts_refines` consumes. -/
theorem proj_back_rename_step {t ctor : name.Name} {n_f : Std.U64}
    (ht : NameWF t) (hc : NameWF ctor) :
    ∀ n, NameWF n → ∀ r,
      (inductives.modeled.ProjBack.Insts.Con_ron_coreKernelExpr_opsNameToName).rename
          { t := t, ctor := ctor, n_f := n_f } n = ok r →
        absName r
            = ConLeche.projBack (absName t) (absName ctor) n_f.val (absName n)
          ∧ NameWF r := by
  intro n hn r h
  -- the dictionary's projection only reduces through the unifier
  have h2 : (do let n1 ← inductives.modeled.model_of t
                let b ← name.beq n n1
                if b then name.dup t
                else do
                  let n2 ← inductives.modeled.model_of ctor
                  let b1 ← name.beq n n2
                  if b1 then name.dup ctor
                  else do
                    let o ← inductives.modeled.find_proj_model_slot t n_f n 0#u64
                    match o with
                    | none => name.dup n
                    | some j => env.proj_fn_name t j) = ok r := h
  clear h
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h2
  obtain ⟨hn1abs, hn1wf⟩ := model_of_refines ht hn1
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbabs := Name.name_beq_exact' hn hn1wf hb
  rw [hn1abs] at hbabs
  simp only [ConLeche.projBack]
  cases b with
  | true =>
    simp only [if_true] at h
    rw [name_dup_eq] at h
    rw [← Result.ok_injective h, if_pos (by simpa using hbabs.symm)]
    exact ⟨rfl, ht⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    rw [if_neg (by simpa using hbabs.symm)]
    obtain ⟨n2, hn2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hn2abs, hn2wf⟩ := model_of_refines hc hn2
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := Name.name_beq_exact' hn hn2wf hb1
    rw [hn2abs] at hb1abs
    cases b1 with
    | true =>
      simp only [if_true] at h
      rw [name_dup_eq] at h
      rw [← Result.ok_injective h, if_pos (by simpa using hb1abs.symm)]
      exact ⟨rfl, hc⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      rw [if_neg (by simpa using hb1abs.symm)]
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hslot := find_proj_model_slot_refines ht hn ho
      rw [← hslot]
      cases o with
      | none =>
        rw [name_dup_eq] at h
        rw [← Result.ok_injective h]
        exact ⟨rfl, hn⟩
      | some j =>
        obtain ⟨habs, hwf⟩ := proj_fn_name_refines ht h
        exact ⟨by rw [habs]; rfl, hwf⟩

/-- `ConLeche/Kernel/Inductives/Modeled.lean:466-473 projFwd` —
**`ProjFwd`'s one method is the cited closure**, the roundtrip's half. -/
theorem proj_fwd_rename_step {t ctor : name.Name} {n_f : Std.U64}
    (ht : NameWF t) (hc : NameWF ctor) :
    ∀ n, NameWF n → ∀ r,
      (inductives.modeled.ProjFwd.Insts.Con_ron_coreKernelExpr_opsNameToName).rename
          { t := t, ctor := ctor, n_f := n_f } n = ok r →
        absName r
            = ConLeche.projFwd (absName t) (absName ctor) n_f.val (absName n)
          ∧ NameWF r := by
  intro n hn r h
  -- the dictionary's projection only reduces through the unifier
  have h2 : (do let b ← name.beq n t
                if b then inductives.modeled.model_of t
                else do
                  let b1 ← name.beq n ctor
                  if b1 then inductives.modeled.model_of ctor
                  else do
                    let o ← inductives.modeled.find_proj_fn_slot t n_f n 0#u64
                    match o with
                    | none => name.dup n
                    | some j => core_k.proj_model_name t j) = ok r := h
  clear h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h2
  have hbabs := Name.name_beq_exact' hn ht hb
  simp only [ConLeche.projFwd]
  cases b with
  | true =>
    simp only [if_true] at h
    rw [if_pos (by simpa using hbabs.symm)]
    obtain ⟨habs, hwf⟩ := model_of_refines ht h
    exact ⟨habs, hwf⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    rw [if_neg (by simpa using hbabs.symm)]
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := Name.name_beq_exact' hn hc hb1
    cases b1 with
    | true =>
      simp only [if_true] at h
      rw [if_pos (by simpa using hb1abs.symm)]
      obtain ⟨habs, hwf⟩ := model_of_refines hc h
      exact ⟨habs, hwf⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      rw [if_neg (by simpa using hb1abs.symm)]
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hslot := find_proj_fn_slot_refines ht hn ho
      rw [← hslot]
      cases o with
      | none =>
        rw [name_dup_eq] at h
        rw [← Result.ok_injective h]
        exact ⟨rfl, hn⟩
      | some j =>
        obtain ⟨habs, hwf⟩ := proj_model_name_refines ht h
        exact ⟨by rw [habs]; rfl, hwf⟩

open ConLeche.Cached in
/-- `ConLeche/Kernel/DeclCheck.lean:748-761 checkProjTyF` at a run whose four
guards held: it is that run, and it leaves the state where it found it (the
cited Lean is `ops`-free). -/
theorem checkProjTyF_run {lfe : ConLeche.FEnv} {T ctorName : ConLeche.Name}
    {lps : List ConLeche.Name} {mty : ConLeche.Expr} {nP nF : Nat} {lst : CState}
    (h1 : ((mty.renameConsts (ConLeche.projBack T ctorName nF)).renameConsts
        (ConLeche.projFwd T ctorName nF) == mty) = true)
    (h2 : (mty.renameConsts (ConLeche.projBack T ctorName nF)).constsResolveF lfe
        = true)
    (h3 : ((mty.renameConsts (ConLeche.projBack T ctorName nF)).looseBVarsBounded 0
        && !(mty.renameConsts (ConLeche.projBack T ctorName nF)).hasFvar
        && (mty.renameConsts (ConLeche.projBack T ctorName nF)).allLevelParamsDefined
              lps) = true)
    (h4 : ((mty.renameConsts (ConLeche.projBack T ctorName nF)).stripPis
        (nP + 1)).isSome = true) :
    (ConLeche.checkProjTyF (m := CheckCM) lfe T ctorName lps mty nP nF).run lst
      = .ok (mty.renameConsts (ConLeche.projBack T ctorName nF), lst) := by
  rw [ConLeche.checkProjTyF]
  simp only [h1, h2, h3, h4, StateT.run, Bind.bind, Pure.pure, StateT.pure,
    Except.pure, if_true]

open ConLeche.Cached in
/-- `checkProjTyF`'s roundtrip `throw` (`DeclCheck.lean:752`). -/
theorem checkProjTyF_roundtrip {lfe : ConLeche.FEnv} {T ctorName : ConLeche.Name}
    {lps : List ConLeche.Name} {mty : ConLeche.Expr} {nP nF : Nat} {lst : CState}
    (h1 : ((mty.renameConsts (ConLeche.projBack T ctorName nF)).renameConsts
        (ConLeche.projFwd T ctorName nF) == mty) = false) :
    (ConLeche.checkProjTyF (m := CheckCM) lfe T ctorName lps mty nP nF).run lst
      = .error (.notImplemented "projection type roundtrip") := by
  rw [ConLeche.checkProjTyF]
  simp only [h1, StateT.run, Bind.bind, Bool.false_eq_true, if_false]
  rfl

open ConLeche.Cached in
/-- `checkProjTyF`'s resolution `throw` (`DeclCheck.lean:754`). -/
theorem checkProjTyF_resolve {lfe : ConLeche.FEnv} {T ctorName : ConLeche.Name}
    {lps : List ConLeche.Name} {mty : ConLeche.Expr} {nP nF : Nat} {lst : CState}
    (h1 : ((mty.renameConsts (ConLeche.projBack T ctorName nF)).renameConsts
        (ConLeche.projFwd T ctorName nF) == mty) = true)
    (h2 : (mty.renameConsts (ConLeche.projBack T ctorName nF)).constsResolveF lfe
        = false) :
    (ConLeche.checkProjTyF (m := CheckCM) lfe T ctorName lps mty nP nF).run lst
      = .error (.notImplemented "projection type resolution") := by
  rw [ConLeche.checkProjTyF]
  simp only [h1, h2, StateT.run, Bind.bind, if_true, Bool.false_eq_true, if_false]
  rfl

open ConLeche.Cached in
/-- `checkProjTyF`'s well-formedness `throw` (`DeclCheck.lean:758`). -/
theorem checkProjTyF_wf {lfe : ConLeche.FEnv} {T ctorName : ConLeche.Name}
    {lps : List ConLeche.Name} {mty : ConLeche.Expr} {nP nF : Nat} {lst : CState}
    (h1 : ((mty.renameConsts (ConLeche.projBack T ctorName nF)).renameConsts
        (ConLeche.projFwd T ctorName nF) == mty) = true)
    (h2 : (mty.renameConsts (ConLeche.projBack T ctorName nF)).constsResolveF lfe
        = true)
    (h3 : ((mty.renameConsts (ConLeche.projBack T ctorName nF)).looseBVarsBounded 0
        && !(mty.renameConsts (ConLeche.projBack T ctorName nF)).hasFvar
        && (mty.renameConsts (ConLeche.projBack T ctorName nF)).allLevelParamsDefined
              lps) = false) :
    (ConLeche.checkProjTyF (m := CheckCM) lfe T ctorName lps mty nP nF).run lst
      = .error (.notImplemented "projection type wellformedness") := by
  rw [ConLeche.checkProjTyF]
  simp only [h1, h2, h3, StateT.run, Bind.bind, if_true, Bool.false_eq_true,
    if_false]
  rfl

open ConLeche.Cached in
/-- `checkProjTyF`'s telescope `throw` (`DeclCheck.lean:760`). -/
theorem checkProjTyF_telescope {lfe : ConLeche.FEnv} {T ctorName : ConLeche.Name}
    {lps : List ConLeche.Name} {mty : ConLeche.Expr} {nP nF : Nat} {lst : CState}
    (h1 : ((mty.renameConsts (ConLeche.projBack T ctorName nF)).renameConsts
        (ConLeche.projFwd T ctorName nF) == mty) = true)
    (h2 : (mty.renameConsts (ConLeche.projBack T ctorName nF)).constsResolveF lfe
        = true)
    (h3 : ((mty.renameConsts (ConLeche.projBack T ctorName nF)).looseBVarsBounded 0
        && !(mty.renameConsts (ConLeche.projBack T ctorName nF)).hasFvar
        && (mty.renameConsts (ConLeche.projBack T ctorName nF)).allLevelParamsDefined
              lps) = true)
    (h4 : ((mty.renameConsts (ConLeche.projBack T ctorName nF)).stripPis
        (nP + 1)).isSome = false) :
    (ConLeche.checkProjTyF (m := CheckCM) lfe T ctorName lps mty nP nF).run lst
      = .error (.notImplemented "projection type telescope") := by
  rw [ConLeche.checkProjTyF]
  simp only [h1, h2, h3, h4, StateT.run, Bind.bind, if_true, Bool.false_eq_true,
    if_false]
  rfl

/-- `ConLeche/Kernel/DeclCheck.lean:748-761 checkProjTyF` (and
`Inductives/Modeled.lean:497-511 checkProjTy`, the generic twin) —
**`inductives::modeled::check_proj_ty`**: the public projection type is the
model's renamed back, pinned by the renaming roundtrip, resolving, scoped, and
parameter-led.

The four `modeled.rs` steps above carry the two renamings; the rest is
`consts_resolve_f_fast_refines`, `ExprOps.loose_bvars_bounded_refines`,
`ExprOps.has_fvar_refines`, `ExprOps.all_level_params_defined_fast_refines`,
`ExprOps.strip_pis_refines` and `Expr.beq_refines`. -/
theorem check_proj_ty_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name} {mty : expr.Expr}
    {n_p n_f : Std.U64}
    {out : core.result.Result expr.Expr core_types.CheckError}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps) (hmty : ExprWF mty)
    (h : inductives.modeled.check_proj_ty fe t ctor_name lps mty n_p n_f
      = ok out) :
    ∀ lst : ConLeche.Cached.CState,
      match out with
      | .Ok pty =>
        (ConLeche.checkProjTyF (m := ConLeche.Cached.CheckCM) lfe
            (absName t) (absName ctor_name) (absNames lps) (absExpr mty)
            n_p.val n_f.val).run lst
          = .ok (absExpr pty, lst)
        ∧ ExprWF pty
      | .Err e =>
        ErrSim e ((ConLeche.checkProjTyF (m := ConLeche.Cached.CheckCM) lfe
            (absName t) (absName ctor_name) (absNames lps) (absExpr mty)
            n_p.val n_f.val).run lst) := by
  -- `hwf` is carried for the seam's uniformity (every statement of this
  -- section takes it); this route reads the index only through `FindAgree`.
  have _ : FindWF fe := hwf
  intro lst
  rw [inductives.modeled.check_proj_ty] at h
  obtain ⟨pty0, hpty, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hptyabs, hptywf⟩ := ExprOps.rename_consts_refines
    (ConLeche.projBack (absName t) (absName ctor_name) n_f.val)
    (proj_back_rename_step ht hc) hmty hpty
  obtain ⟨round, hround, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hroundabs, hroundwf⟩ := ExprOps.rename_consts_refines
    (ConLeche.projFwd (absName t) (absName ctor_name) n_f.val)
    (proj_fwd_rename_step ht hc) hptywf hround
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbabs := Expr.beq_refines hroundwf hmty hb
  split at h
  · rename_i hbt
    subst hbt
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := consts_resolve_f_fast_refines CoreK.pinnedBasisNames hfe
      hptywf hb1
    split at h
    · rename_i hb1t
      subst hb1t
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2abs := ExprOps.loose_bvars_bounded_refines hptywf hb2
      rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hb2abs
      obtain ⟨wfb, hwfb, h⟩ := bind_eq_ok_iff.mp h
      have hwfabs : wfb = ((absExpr pty0).looseBVarsBounded 0
          && !(absExpr pty0).hasFvar
          && (absExpr pty0).allLevelParamsDefined (absNames lps)) := by
        cases b2 with
        | false =>
          simp only [Bool.false_eq_true, if_false] at hwfb
          rw [← Result.ok_injective hwfb, ← hb2abs]
          simp
        | true =>
          simp only [if_true] at hwfb
          obtain ⟨b3, hb3, hwfb⟩ := bind_eq_ok_iff.mp hwfb
          have hb3abs := ExprOps.has_fvar_refines hptywf hb3
          cases b3 with
          | true =>
            simp only [if_true] at hwfb
            rw [← Result.ok_injective hwfb, ← hb3abs]
            simp
          | false =>
            simp only [Bool.false_eq_true, if_false] at hwfb
            rw [ExprOps.all_level_params_defined_fast_refines hlps hptywf hwfb,
              ← hb2abs, ← hb3abs]
            simp
      split at h
      · rename_i hwft
        subst hwft
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        have hi1v : i1.val = n_p.val + 1 := HashMap.uscalar_add_eq hi1
        obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hoabs, -⟩ := ExprOps.strip_pis_refines hptywf ho
        rw [hi1v] at hoabs
        have hround : ((absExpr mty).renameConsts
              (ConLeche.projBack (absName t) (absName ctor_name) n_f.val)).renameConsts
              (ConLeche.projFwd (absName t) (absName ctor_name) n_f.val)
            == absExpr mty := by
          rw [← hptyabs, ← hroundabs, ← decide_eq_beq]; exact hbabs.symm
        have hres : ((absExpr mty).renameConsts
              (ConLeche.projBack (absName t) (absName ctor_name) n_f.val)).constsResolveF
              lfe = true := by
          rw [← hptyabs]; exact hb1abs.symm
        have hwfc : (((absExpr mty).renameConsts
                (ConLeche.projBack (absName t) (absName ctor_name) n_f.val)).looseBVarsBounded 0
              && !((absExpr mty).renameConsts
                (ConLeche.projBack (absName t) (absName ctor_name) n_f.val)).hasFvar
              && ((absExpr mty).renameConsts
                (ConLeche.projBack (absName t) (absName ctor_name) n_f.val)).allLevelParamsDefined
                  (absNames lps)) = true := by
          rw [← hptyabs]; exact hwfabs.symm
        by_cases hon : core.option.Option.is_none o = true
        · -- `modeled.rs` ← `DeclCheck.lean:760`
          replace h := ite_pos_eq (c := (core.option.Option.is_none o = true)) hon h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
          cases out with
          | Ok q => simp at h
          | Err e =>
            refine errSim_notImplemented hce (by simpa using h)
              (checkProjTyF_telescope hround hres hwfc ?_)
            rw [← hptyabs, ← hoabs]
            cases o with
            | none => simp
            | some q => simp [core.option.Option.is_none] at hon
        · replace h := ite_neg_eq (c := (core.option.Option.is_none o = true)) hon h
          simp only [Result.ok.injEq] at h
          subst h
          refine ⟨?_, hptywf⟩
          rw [hptyabs]
          refine checkProjTyF_run hround hres hwfc ?_
          rw [← hptyabs, ← hoabs]
          cases o with
          | none => simp [core.option.Option.is_none] at hon
          | some q => simp
      · -- `modeled.rs` ← `DeclCheck.lean:758`
        rename_i hwff
        simp only [bind_eq_ok_iff] at h
        obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
        cases out with
        | Ok q => simp at h
        | Err e =>
          refine errSim_notImplemented hce (by simpa using h)
            (checkProjTyF_wf ?_ ?_ ?_)
          · rw [← hptyabs, ← hroundabs, ← decide_eq_beq]; exact hbabs.symm
          · rw [← hptyabs]; exact hb1abs.symm
          · rw [← hptyabs, ← hwfabs]; simpa using hwff
    · -- `modeled.rs` ← `DeclCheck.lean:754`
      rename_i hb1f
      simp only [bind_eq_ok_iff] at h
      obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
      cases out with
      | Ok q => simp at h
      | Err e =>
        refine errSim_notImplemented hce (by simpa using h)
          (checkProjTyF_resolve ?_ ?_)
        · rw [← hptyabs, ← hroundabs, ← decide_eq_beq]; exact hbabs.symm
        · rw [← hptyabs, ← hb1abs]; simpa using hb1f
  · -- `modeled.rs` ← `DeclCheck.lean:752`
    rename_i hbf
    simp only [bind_eq_ok_iff] at h
    obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
    cases out with
    | Ok q => simp at h
    | Err e =>
      refine errSim_notImplemented hce (by simpa using h)
        (checkProjTyF_roundtrip ?_)
      rw [← hptyabs, ← hroundabs, ← decide_eq_beq, ← hbabs]
      simpa using hbf

/-- `ConLeche/Kernel/CheckerBase.lean:235-250 checkProjShape` —
**`checker_base::check_proj_shape`**: the projection type's parameter prefix
and the constructor's `nP + nF` telescope, plus the residual pin.  Operation-
and state-free, so the run leaves `lst` alone.

`Refine/CheckerBase.lean` owns the proof; it is restated here because the
projection route (`Cached/CheckerC.lean:160`) calls it between `checkProjTyF`
and `checkProjRuleF`, and task #57 consumes the whole chain. -/
theorem check_proj_shape_refines {pty ctor_ty : expr.Expr} {n_p n_f : Std.U64}
    {out : core.result.Result Unit core_types.CheckError}
    (hp : ExprWF pty) (hct : ExprWF ctor_ty)
    (h : checker_base.check_proj_shape pty ctor_ty n_p n_f = ok out) :
    ∀ lst : ConLeche.Cached.CState,
      match out with
      | .Ok _ =>
        (ConLeche.checkProjShape (m := ConLeche.Cached.CheckCM)
          (absExpr pty) (absExpr ctor_ty) n_p.val n_f.val).run lst
        = .ok ((), lst)
      | .Err e =>
        ErrSim e ((ConLeche.checkProjShape (m := ConLeche.Cached.CheckCM)
          (absExpr pty) (absExpr ctor_ty) n_p.val n_f.val).run lst) :=
  CheckerBase.check_proj_shape_refines hp hct h

/-- `ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF` (and
`CheckerBase.lean:252-290 checkProjRule`, the generic twin) —
**`checker_base::check_proj_rule`**: the projection function's right-hand side
built from the constructor's telescope, annotated, scope- and level-checked,
its domains compared with the constructor's, and its type inferred.

`Refine/CheckerBase.lean` owns the proof (it carries `ConstsResolveFSpec`,
which `constsResolveFSpec` above discharges); restated here at the `F`
citation for the task-#57 chain. -/
theorem check_proj_rule_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {pty : expr.Expr}
    {cvj : env.ConstantVal} {lps : alloc.vec.Vec name.Name}
    {n_p n_f i : Std.U64}
    {out : core.result.Result expr.Expr core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hpty : ExprWF pty)
    (hcvj : ConstantValWF cvj) (hlps : NamesWF lps)
    (h : checker_base.check_proj_rule mode st fe pty cvj lps n_p n_f i
      = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok rhs_a =>
        ∃ lst', (ConLeche.checkProjRuleF (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe (absExpr pty)
              (absConstantVal cvj) (absNames lps) n_p.val n_f.val i.val).run lst
            = .ok (absExpr rhs_a, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF rhs_a
      | .Err e =>
        ErrSim e ((ConLeche.checkProjRuleF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe (absExpr pty)
            (absConstantVal cvj) (absNames lps) n_p.val n_f.val i.val).run lst) :=
  CheckerBase.check_proj_rule_refines hfuel hk constsResolveFSpec hsw hfw hpty
    hcvj hlps h

/-! ### The iota seam's small readers, as steps

`check_proj_iota` is the head of `modeled.rs`'s iota family, task #57's; the
readers it opens with are proved here as steps, the way
`Refine/CheckerPins.lean`'s `one_level_step` is, because the statement below
cannot be discharged without them and this file may not import a sibling that
does not exist yet. -/

/-- The `some (.thmInfo tcv _)` reading of a lookup, as a function (the
`thmInfo` twin of `Refine/CoreKGuards.lean`'s `defnOf`/`ctorOf`/`indOf`). -/
def thmOf : Option ConLeche.ConstantInfo → Option ConLeche.ConstantVal
  | some (.thmInfo cv _) => some cv
  | _ => none

/-- `thmOf` is injective on hits: the probe's answer pins the lookup. -/
theorem thmOf_eq_some {x : Option ConLeche.ConstantInfo}
    {cv : ConLeche.ConstantVal} (heq : thmOf x = some cv) :
    ∃ v, x = some (.thmInfo cv v) := by
  unfold thmOf at heq
  split at heq <;> simp_all

/-- `ConLeche/Kernel/DeclCheck.lean:800` — **`modeled::thm_probe`**: the
`some (.thmInfo tcv _)` destructuring of the indexed lookup, with an owned
copy (task #14's rule: the index's borrow dies at the call boundary). -/
theorem thm_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {o : Option env.ConstantVal} (hfe : FindAgree fe lfe) (hwf : FindWF fe)
    (hn : NameWF n) (h : inductives.modeled.thm_probe fe n = ok o) :
    o.map absConstantVal = thmOf (lfe.find? (absName n)) ∧
      ∀ cv, o = some cv → ConstantValWF cv := by
  rw [inductives.modeled.thm_probe] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ov, hov, h⟩ := h
  cases ov with
  | none =>
    rw [hfe.find_none hn hov]
    simp only [Result.ok.injEq] at h; subst h
    exact ⟨rfl, by simp⟩
  | some ci =>
    have hlf := hfe.find_some hn hov
    have hciwf := hwf n ci hn hov
    cases ci with
    | ThmInfo cv v =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨cv1, hcv1, ho⟩ := h
      obtain ⟨hcvabs, hcvwf⟩ := constant_val_dup_abs hcv1
      rw [← Result.ok_injective ho, hlf]
      obtain ⟨hw1, -⟩ := hciwf
      refine ⟨by simp [thmOf, absConstantInfo, hcvabs], ?_⟩
      intro cv2 heq
      simp only [Option.some.injEq] at heq
      subst heq
      exact hcvwf hw1
    | AxiomInfo _ | DefnInfo _ _ _ | IndInfo _ _ | CtorInfo _ _ _
    | RecInfo _ _ _ _ | ProjInfo _ =>
      simp only [Result.ok.injEq] at h; subst h
      rw [hlf]; exact ⟨rfl, by simp⟩

/-- `ConLeche/Kernel/DeclCheck.lean:800` — `modeled::proj_iota_name` is the
cited `(projModelName T i).str "iota"`. -/
theorem proj_iota_name_refines {t r : name.Name} {i : Std.U64} (ht : NameWF t)
    (h : inductives.modeled.proj_iota_name t i = ok r) :
    absName r = (ConLeche.projModelName (absName t) i.val).str "iota"
      ∧ NameWF r := by
  rw [inductives.modeled.proj_iota_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hnabs, hnwf⟩ := proj_model_name_refines ht hn
  obtain ⟨h1, h1wf⟩ := str_lit_step hnwf hs hv hmk
    (L := [105#u32, 111#u32, 116#u32, 97#u32])
    (by rw [inductives.modeled.proj_iota_name.IOTA, Array.make_val]) (by decide)
  exact ⟨by rw [h1, hnabs]; rfl, h1wf⟩

/-- `struct_parts::params_of_from` is the cited `lps.map .param` from `i`. -/
theorem params_of_from_refines {lps : alloc.vec.Vec name.Name}
    (hlps : NamesWF lps) (N : Nat) :
    ∀ (i : Std.Usize) (out r : alloc.vec.Vec level.Level),
      lps.val.length - i.val = N → LevelsWF out →
      inductives.struct_parts.params_of_from lps i out = ok r →
      absLevels r = absLevels out
          ++ ((absNames lps).drop i.val).map ConLeche.Level.param ∧ LevelsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i out r hN hout h
    rw [inductives.struct_parts.params_of_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : lps.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val lps; scalar_tac
      rw [← Result.ok_injective h, absNames, ← List.map_drop,
        List.drop_eq_nil_of_le (by simpa using hlen)]
      exact ⟨by simp, hout⟩
    · rename_i hge
      simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨x, hidx, u, hu, out1, hpush, i2, hi2, hrec⟩ := h
      have hlt : i.val < lps.val.length := by
        have := alloc.vec.Vec.len_val lps; scalar_tac
      have hx : lps.val[i.val] = x := by
        have hg := ExprOps.vec_index_getElem? hidx
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hxwf : NameWF x := by rw [← hx]; exact hlps _ (List.getElem_mem hlt)
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hout1 : LevelsWF out1 := by
        intro w hw
        rw [vec_push_val hpush] at hw
        rcases List.mem_append.1 hw with h1 | h1
        · exact hout w h1
        · simp only [List.mem_singleton] at h1; rw [h1]; exact LevelWF.param hxwf hu
      obtain ⟨habs, hwf⟩ := ih (lps.val.length - i2.val) (by omega) i2 out1 r rfl hout1 hrec
      refine ⟨?_, hwf⟩
      have h1 : absLevels out1 = absLevels out ++ [ConLeche.Level.param (absName x)] := by
        rw [absLevels, absLevels, vec_push_val hpush]
        simp [Level.param_refines hu]
      rw [habs, h1, hi2v, List.append_assoc]
      congr 1
      rw [absNames, ← List.map_drop, ← List.map_drop,
        List.drop_eq_getElem_cons hlt, hx]
      simp

/-- `ConLeche/Kernel/Inductives/StructParts.lean:48` —
`struct_parts::params_of` is the cited `lps.map .param`. -/
theorem params_of_refines {lps : alloc.vec.Vec name.Name}
    {r : alloc.vec.Vec level.Level} (hlps : NamesWF lps)
    (h : inductives.struct_parts.params_of lps = ok r) :
    absLevels r = (absNames lps).map ConLeche.Level.param ∧ LevelsWF r := by
  rw [inductives.struct_parts.params_of] at h
  obtain ⟨habs, hwf⟩ :=
    params_of_from_refines hlps _ 0#usize _ r rfl CoreK.levelsWF_new h
  refine ⟨?_, hwf⟩
  rw [habs]
  simp [absLevels, alloc.vec.Vec.new]

/-- `struct_parts::struct_ps_at_from` is the cited parameter spine from `k`. -/
theorem struct_ps_at_from_refines (N : Nat) :
    ∀ (o n_p k : Std.U64) (out r : alloc.vec.Vec expr.Expr),
      n_p.val - k.val = N → ExprsWF out →
      inductives.struct_parts.struct_ps_at_from o n_p k out = ok r →
      absExprs r = absExprs out
          ++ ((List.range n_p.val).drop k.val).map
              (fun j => ConLeche.Expr.bvar (o.val + n_p.val - 1 - j)) ∧ ExprsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro o n_p k out r hN hout h
    rw [inductives.struct_parts.struct_ps_at_from.eq_def] at h
    split at h
    · rename_i hge
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simp; scalar_tac)]
      exact ⟨by simp, hout⟩
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i0, hi0, i1, hi1, i2, hi2, e, he, out1, hpush, k2, hk2, hrec⟩ := h
      have hlt : k.val < (List.range n_p.val).length := by
        rw [List.length_range]; scalar_tac
      have hi0v : i0.val = o.val + n_p.val := HashMap.uscalar_add_eq hi0
      have hi1v : i1.val = i0.val - 1 := Level.u64_sub_val hi1
      have hi2v : i2.val = i1.val - k.val := Level.u64_sub_val hi2
      have hk2v : k2.val = k.val + 1 := HashMap.uscalar_add_eq hk2
      have hewf : ExprWF e := ExprWF.bvar he
      have hout1 : ExprsWF out1 := by
        intro w hw
        rw [vec_push_val hpush] at hw
        rcases List.mem_append.1 hw with h1 | h1
        · exact hout w h1
        · simp only [List.mem_singleton] at h1; rw [h1]; exact hewf
      obtain ⟨habs, hwf⟩ :=
        ih (n_p.val - k2.val) (by clear hlt; scalar_tac) o n_p k2 out1 r rfl hout1 hrec
      refine ⟨?_, hwf⟩
      have h1 : absExprs out1
          = absExprs out ++ [ConLeche.Expr.bvar (o.val + n_p.val - 1 - k.val)] := by
        rw [absExprs, absExprs, vec_push_val hpush]
        simp [Expr.bvar_refines he, hi2v, hi1v, hi0v]
      rw [habs, h1, hk2v, List.append_assoc]
      congr 1
      rw [List.drop_eq_getElem_cons hlt]
      simp

/-- `ConLeche/Kernel/Inductives/StructParts.lean:134-137 structPsAt` —
`struct_parts::struct_ps_at` is the cited
`(List.range nP).map fun k => Expr.bvar (o + nP - 1 - k)`. -/
theorem struct_ps_at_refines {o n_p : Std.U64} {r : alloc.vec.Vec expr.Expr}
    (h : inductives.struct_parts.struct_ps_at o n_p = ok r) :
    absExprs r = (List.range n_p.val).map
        (fun j => ConLeche.Expr.bvar (o.val + n_p.val - 1 - j))
      ∧ ExprsWF r := by
  rw [inductives.struct_parts.struct_ps_at] at h
  obtain ⟨habs, hwf⟩ :=
    struct_ps_at_from_refines _ o n_p 0#u64 _ r rfl ExprOps.exprsWF_new h
  refine ⟨?_, hwf⟩
  rw [habs]
  simp [absExprs, alloc.vec.Vec.new]

/-- `struct_parts::field_spine_from` is the cited field spine from `k`. -/
theorem field_spine_from_refines (N : Nat) :
    ∀ (m k : Std.U64) (out r : alloc.vec.Vec expr.Expr),
      m.val - k.val = N → ExprsWF out →
      inductives.struct_parts.field_spine_from m k out = ok r →
      absExprs r = absExprs out
          ++ ((List.range m.val).drop k.val).map
              (fun j => ConLeche.Expr.bvar (m.val - 1 - j)) ∧ ExprsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro m k out r hN hout h
    rw [inductives.struct_parts.field_spine_from.eq_def] at h
    split at h
    · rename_i hge
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simp; scalar_tac)]
      exact ⟨by simp, hout⟩
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i0, hi0, i1, hi1, e, he, out1, hpush, k2, hk2, hrec⟩ := h
      have hlt : k.val < (List.range m.val).length := by
        rw [List.length_range]; scalar_tac
      have hi0v : i0.val = m.val - 1 := Level.u64_sub_val hi0
      have hi1v : i1.val = i0.val - k.val := Level.u64_sub_val hi1
      have hk2v : k2.val = k.val + 1 := HashMap.uscalar_add_eq hk2
      have hewf : ExprWF e := ExprWF.bvar he
      have hout1 : ExprsWF out1 := by
        intro w hw
        rw [vec_push_val hpush] at hw
        rcases List.mem_append.1 hw with h1 | h1
        · exact hout w h1
        · simp only [List.mem_singleton] at h1; rw [h1]; exact hewf
      obtain ⟨habs, hwf⟩ :=
        ih (m.val - k2.val) (by clear hlt; scalar_tac) m k2 out1 r rfl hout1 hrec
      refine ⟨?_, hwf⟩
      have h1 : absExprs out1
          = absExprs out ++ [ConLeche.Expr.bvar (m.val - 1 - k.val)] := by
        rw [absExprs, absExprs, vec_push_val hpush]
        simp [Expr.bvar_refines he, hi1v, hi0v]
      rw [habs, h1, hk2v, List.append_assoc]
      congr 1
      rw [List.drop_eq_getElem_cons hlt]
      simp

/-- `ConLeche/Kernel/Inductives/StructParts.lean:88-94 structCtorSpine` —
`struct_parts::field_spine` is the cited
`(List.range m).map fun k => Expr.bvar (m - 1 - k)`. -/
theorem field_spine_refines {m : Std.U64} {r : alloc.vec.Vec expr.Expr}
    (h : inductives.struct_parts.field_spine m = ok r) :
    absExprs r = (List.range m.val).map
        (fun j => ConLeche.Expr.bvar (m.val - 1 - j))
      ∧ ExprsWF r := by
  rw [inductives.struct_parts.field_spine] at h
  obtain ⟨habs, hwf⟩ :=
    field_spine_from_refines _ m 0#u64 _ r rfl ExprOps.exprsWF_new h
  refine ⟨?_, hwf⟩
  rw [habs]
  simp [absExprs, alloc.vec.Vec.new]

/-- `ConLeche/Kernel/DeclCheck.lean:833-835` — `modeled::arg_get_d` is the
cited `args.getD k (.bvar 0)`. -/
theorem arg_get_d_refines {args : alloc.vec.Vec expr.Expr} {k : Std.Usize}
    {r : expr.Expr} (hargs : ExprsWF args)
    (h : inductives.modeled.arg_get_d args k = ok r) :
    absExpr r = (absExprs args).getD k.val (ConLeche.Expr.bvar 0) ∧ ExprWF r := by
  rw [inductives.modeled.arg_get_d] at h
  split at h
  · rename_i hlt
    have hltv : k.val < args.val.length := by
      have := alloc.vec.Vec.len_val args; scalar_tac
    obtain ⟨x, hidx, hdup⟩ := bind_eq_ok_iff.mp h
    have hg := ExprOps.vec_index_getElem? hidx
    have hx : args.val[k.val] = x := by
      rw [List.getElem?_eq_getElem hltv] at hg; exact Option.some_injective _ hg
    have hxwf : ExprWF x := by rw [← hx]; exact hargs _ (List.getElem_mem hltv)
    rw [Expr.dup_eq hdup]
    refine ⟨?_, hxwf⟩
    rw [List.getD_eq_getElem?_getD, absExprs, List.getElem?_map, hg]
    rfl
  · rename_i hge
    have hgev : args.val.length ≤ k.val := by
      have := alloc.vec.Vec.len_val args; scalar_tac
    refine ⟨?_, ExprWF.bvar h⟩
    rw [Expr.bvar_refines h, List.getD_eq_getElem?_getD, absExprs,
      List.getElem?_map, List.getElem?_eq_none (by simpa using hgev)]
    rfl

/-! ### `domsMatchAux` at a general binder view, as a step

`Refine/CheckerBase.lean`'s `doms_match_aux_from_refines` is this same
induction pinned to the identity dictionary `DomIdent`, which is what its own
four call sites pass.  `checkProjIotaF` is the one site that views the right
side through a renaming (`modeled::DomProjFwd`), so the induction is
re-derived here over the `DomView` dictionary — the only line that changes is
the one that reads the view.  (When task #57 lands, `Refine/CheckerBase.lean`
should be generalised to this and its `DomIdent` version recovered as the
instance.) -/

/-- The cited `(List.range n).all` body, at a general view. -/
def domsStepV (g : Nat → ConLeche.Expr → ConLeche.Expr)
    (bs₁ bs₂ : List (ConLeche.Expr × ConLeche.BinderMeta)) (o₁ o₂ i : Nat) : Bool :=
  match bs₁[o₁ + i]?, bs₂[o₂ + i]? with
  | some b₁, some b₂ => b₁.1 == g i b₂.1
  | _, _ => false

/-- `domsMatchAux` *is* `domsStepV`'s `List.range` fold. -/
theorem domsMatchAux_eq_all (g : Nat → ConLeche.Expr → ConLeche.Expr)
    (bs₁ bs₂ : List (ConLeche.Expr × ConLeche.BinderMeta)) (o₁ o₂ n : Nat) :
    ConLeche.domsMatchAux g bs₁ bs₂ o₁ o₂ n
      = (List.range n).all (domsStepV g bs₁ bs₂ o₁ o₂) := rfl

/-- `ConLeche/Kernel/CheckerBase.lean:99-106 domsMatchAux` — the index
recursion behind `checker_base::doms_match_aux`, at the positions from `i` on,
over an arbitrary `DomView` dictionary whose method refines `g`. -/
theorem doms_match_aux_from_view {G : Type}
    {inst : checker_base.DomView G} {dict : G}
    {g : Nat → ConLeche.Expr → ConLeche.Expr}
    {bs1 bs2 : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (hb1 : ExprOps.BindersWF bs1) (hb2 : ExprOps.BindersWF bs2)
    (hview : ∀ (i : Std.U64) (e r : expr.Expr), ExprWF e →
      inst.view dict i e = ok r → absExpr r = g i.val (absExpr e) ∧ ExprWF r) :
    ∀ (N : Nat) (o1 o2 n i : Std.U64), n.val - i.val ≤ N → ∀ b : Bool,
      checker_base.doms_match_aux_from inst dict bs1 bs2 o1 o2 n i = ok b →
      b = (List.range' i.val (n.val - i.val)).all
            (domsStepV g (ExprOps.absBinders bs1) (ExprOps.absBinders bs2)
              o1.val o2.val) := by
  have hlen1 : (ExprOps.absBinders bs1).length = bs1.val.length := by
    simp [ExprOps.absBinders]
  have hlen2 : (ExprOps.absBinders bs2).length = bs2.val.length := by
    simp [ExprOps.absBinders]
  intro N
  induction N with
  | zero =>
    intro o1 o2 n i hN b h
    rw [checker_base.doms_match_aux_from.eq_def] at h
    simp only [] at h
    rw [if_pos (by scalar_tac)] at h
    rw [show n.val - i.val = 0 by omega]
    simpa using h.symm
  | succ N ih =>
    intro o1 o2 n i hN b h
    rw [checker_base.doms_match_aux_from.eq_def] at h
    simp only [] at h
    split at h
    · rw [show n.val - i.val = 0 by scalar_tac]
      simpa using h.symm
    · rename_i hlt
      have hltv : i.val < n.val := by scalar_tac
      simp only [lift_eq, bind_tc_ok] at h
      obtain ⟨j1, hj1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j2, hj2, h⟩ := bind_eq_ok_iff.mp h
      have hj1v : j1.val = o1.val + i.val := HashMap.uscalar_add_eq hj1
      have hj2v : j2.val = o2.val + i.val := HashMap.uscalar_add_eq hj2
      have hc1 : (Std.UScalar.cast .U64 (alloc.vec.Vec.len bs1) : Std.U64).val
          = bs1.val.length := by rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      have hc2 : (Std.UScalar.cast .U64 (alloc.vec.Vec.len bs2) : Std.U64).val
          = bs2.val.length := by rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      rw [show n.val - i.val = (n.val - i.val - 1) + 1 by omega, List.range'_succ,
        List.all_cons]
      split at h
      · rename_i hge
        have hnone : (ExprOps.absBinders bs1)[o1.val + i.val]? = none :=
          List.getElem?_eq_none (by rw [hlen1]; scalar_tac)
        simp only [domsStepV, hnone]
        simpa using h.symm
      · rename_i hlt1
        split at h
        · rename_i hge
          have hnone : (ExprOps.absBinders bs2)[o2.val + i.val]? = none :=
            List.getElem?_eq_none (by rw [hlen2]; scalar_tac)
          simp only [domsStepV, hnone]
          rcases hs : (ExprOps.absBinders bs1)[o1.val + i.val]? with _ | q <;>
            simpa using h.symm
        · rename_i hlt2
          obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e2, m2⟩ := p2
          obtain ⟨viewed, hviewr, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e1, m1⟩ := p1
          obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
          have hi5 : ((Std.UScalar.cast .Usize j2 : Std.Usize)).val = j2.val :=
            ExprOps.u64_cast_usize_val_of_lt (n := bs2.val.length)
              (by have := bs2.slice.property; scalar_tac) (by scalar_tac)
          have hi6 : ((Std.UScalar.cast .Usize j1 : Std.Usize)).val = j1.val :=
            ExprOps.u64_cast_usize_val_of_lt (n := bs1.val.length)
              (by have := bs1.slice.property; scalar_tac) (by scalar_tac)
          obtain ⟨hw2, hg2⟩ := CheckerBase.vec_index_binder hb2 hp2
          obtain ⟨hw1, hg1⟩ := CheckerBase.vec_index_binder hb1 hp1
          rw [hi5, hj2v] at hg2
          rw [hi6, hj1v] at hg1
          obtain ⟨hvabs, hvwf⟩ := hview i e2 viewed hw2 hviewr
          have hcv := Expr.beq_refines hw1 hvwf hc
          rw [hvabs] at hcv
          simp only [domsStepV, hg1, hg2, ← CheckerBase.decide_eq_beq_expr, ← hcv]
          cases c with
          | false =>
            simp only [Bool.false_eq_true, if_false] at h
            simpa using h.symm
          | true =>
            simp only [reduceIte] at h
            obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
            have hi7v : i7.val = i.val + 1 := HashMap.uscalar_add_eq hi7
            have hih := ih o1 o2 n i7 (by omega) b h
            rw [hi7v, show n.val - (i.val + 1) = n.val - i.val - 1 by omega] at hih
            simpa using hih

/-- `ConLeche/Kernel/CheckerBase.lean:99-106 domsMatchAux` — the wrapper, at a
general view. -/
theorem doms_match_aux_view {G : Type}
    {inst : checker_base.DomView G} {dict : G}
    {g : Nat → ConLeche.Expr → ConLeche.Expr}
    {bs1 bs2 : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {o1 o2 n : Std.U64} {b : Bool}
    (hb1 : ExprOps.BindersWF bs1) (hb2 : ExprOps.BindersWF bs2)
    (hview : ∀ (i : Std.U64) (e r : expr.Expr), ExprWF e →
      inst.view dict i e = ok r → absExpr r = g i.val (absExpr e) ∧ ExprWF r)
    (h : checker_base.doms_match_aux inst dict bs1 bs2 o1 o2 n = ok b) :
    b = ConLeche.domsMatchAux g
      (ExprOps.absBinders bs1) (ExprOps.absBinders bs2) o1.val o2.val n.val := by
  rw [checker_base.doms_match_aux] at h
  have hh := doms_match_aux_from_view hb1 hb2 hview n.val o1 o2 n 0#u64
    (by scalar_tac) b h
  rw [domsMatchAux_eq_all, List.range_eq_range']
  simpa using hh

/-- `ConLeche/Kernel/DeclCheck.lean:805-807` — **`DomProjFwd`'s one method is
the cited `fun _ e => e.renameConsts (projFwd T ctorName nF)`**. -/
theorem dom_proj_fwd_view_refines {t ctor : name.Name} {n_f : Std.U64}
    (ht : NameWF t) (hc : NameWF ctor) :
    ∀ (i : Std.U64) (e r : expr.Expr), ExprWF e →
      (inductives.modeled.DomProjFwd.Insts.Con_ron_coreKernelChecker_baseDomView).view
          { t := t, ctor := ctor, n_f := n_f } i e = ok r →
      absExpr r = (fun (_ : Nat) (x : ConLeche.Expr) =>
          x.renameConsts (ConLeche.projFwd (absName t) (absName ctor) n_f.val))
        i.val (absExpr e) ∧ ExprWF r := by
  intro i e r he h
  -- the dictionary's projection only reduces through the unifier
  have h2 : expr_ops.rename_consts
      inductives.modeled.ProjFwd.Insts.Con_ron_coreKernelExpr_opsNameToName
      { t := t, ctor := ctor, n_f := n_f } e = ok r := h
  exact ExprOps.rename_consts_refines
    (ConLeche.projFwd (absName t) (absName ctor) n_f.val)
    (proj_fwd_rename_step ht hc) he h2

/-! ### `checkIotaSidesTy`, as a step

The two side certificates of every iota theorem
(`ConLeche/Kernel/Inductives/Modeled.lean:40-53 checkIotaSidesTy`): the
equation's two sides infer to the type slot, and — in the TT lane only — the
slot itself is a sort at the statement's level.  Four core calls at
`Verified`, six at `Trusted`; the knot hypotheses are
`Refine/TypeChecker.lean`'s rule. -/

/-- One `do` step of the cached checker's monad, run: the state threading of
`StateT CState (Except CheckError)`, as a rewrite. -/
theorem run_bind {α β : Type} {x : ConLeche.Cached.CheckCM α}
    {f : α → ConLeche.Cached.CheckCM β} {s s' : ConLeche.Cached.CState} {a : α}
    (h : x.run s = .ok (a, s')) : (x >>= f).run s = (f a).run s' := by
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show x s = Except.ok (a, s') from h]

/-- The `pure ()` step of a `do` block, run: what a passed `unless` guard
leaves behind. -/
theorem run_pure_bind {α : Type} {f : Unit → ConLeche.Cached.CheckCM α}
    {s : ConLeche.Cached.CState} :
    ((pure () : ConLeche.Cached.CheckCM Unit) >>= f).run s = (f ()).run s := rfl

/-- The failing twin of `run_bind` (task #67's move 1, spelled as a rewrite):
a step that threw makes the rest of the `do` block throw, at its error. -/
theorem run_bind_err {α β : Type} {x : ConLeche.Cached.CheckCM α}
    {f : α → ConLeche.Cached.CheckCM β} {s : ConLeche.Cached.CState}
    {le : ConLeche.CheckError} (h : x.run s = .error le) :
    (x >>= f).run s = .error le := by
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show x s = Except.error le from h]

/-- The Rust reads the fuel constant and hands it to the wrapper; this is the
`type_checker::infer_type_core` spelling `Refine/TypeChecker.lean` refines. -/
theorem infer_at_fuel {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) {st st' : cached.state_c.CState}
    {fe : fenv.FEnv} {d : Std.U64} {e : expr.Expr}
    {r : core.result.Result expr.Expr core_types.CheckError}
    (h : cached.core_c.infer mode fuel st fe d e = ok (r, st')) :
    type_checker.infer_type_core mode st fe d e = ok (r, st') := by
  rw [type_checker.infer_type_core, hfuel]; simpa using h

/-- The `defeq` twin of `infer_at_fuel`. -/
theorem defeq_at_fuel {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) {st st' : cached.state_c.CState}
    {fe : fenv.FEnv} {d : Std.U64} {a b : expr.Expr}
    {r : core.result.Result Bool core_types.CheckError}
    (h : cached.core_c.defeq mode fuel st fe d a b = ok (r, st')) :
    type_checker.is_def_eq_core mode st fe d a b = ok (r, st') := by
  rw [type_checker.is_def_eq_core, hfuel]; simpa using h

open ConLeche.Cached in
/-- `ConLeche/Kernel/Inductives/Modeled.lean:40-47` — `checkIotaSidesTy` at a
run whose two side certificates passed, in the **`Verified` lane** (no
TT-check). -/
theorem checkIotaSidesTy_run_ff {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS tl tr : ConLeche.Expr} {lA : ConLeche.Level}
    {nm : ConLeche.Name} {lst lst1 lst2 lst3 lst4 : CState}
    (htt : mode'.ttChecks = false)
    (h1 : (ops.inferType lenv depth lhsS).run lst = .ok (tl, lst1))
    (h2 : (ops.isDefEq lenv depth tl alphaS).run lst1 = .ok (true, lst2))
    (h3 : (ops.inferType lenv depth rhsS).run lst2 = .ok (tr, lst3))
    (h4 : (ops.isDefEq lenv depth tr alphaS).run lst3 = .ok (true, lst4)) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .ok ((), lst4) := by
  rw [ConLeche.checkIotaSidesTy, run_bind h1, run_bind h2]
  simp only [reduceIte]
  rw [run_bind h3, run_bind h4]
  simp only [reduceIte, htt, Bool.false_eq_true, if_false]
  rfl

open ConLeche.Cached in
/-- `ConLeche/Kernel/Inductives/Modeled.lean:40-53` — the same in the
**`Trusted` lane**, where the slot-sort certificate (task #146) also runs. -/
theorem checkIotaSidesTy_run_tt {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS tl tr ta : ConLeche.Expr} {lA : ConLeche.Level}
    {nm : ConLeche.Name} {lst lst1 lst2 lst3 lst4 lst5 lst6 : CState}
    (htt : mode'.ttChecks = true)
    (h1 : (ops.inferType lenv depth lhsS).run lst = .ok (tl, lst1))
    (h2 : (ops.isDefEq lenv depth tl alphaS).run lst1 = .ok (true, lst2))
    (h3 : (ops.inferType lenv depth rhsS).run lst2 = .ok (tr, lst3))
    (h4 : (ops.isDefEq lenv depth tr alphaS).run lst3 = .ok (true, lst4))
    (h5 : (ops.inferType lenv depth alphaS).run lst4 = .ok (ta, lst5))
    (h6 : (ops.isDefEq lenv depth ta (.sort lA)).run lst5 = .ok (true, lst6)) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .ok ((), lst6) := by
  rw [ConLeche.checkIotaSidesTy, run_bind h1, run_bind h2]
  simp only [reduceIte]
  rw [run_bind h3, run_bind h4]
  simp only [reduceIte, htt]
  rw [run_bind h5, run_bind h6]
  simp only [reduceIte]
  rfl

/-! The six operation calls of `checkIotaSidesTy` and its three `throw`s, as
the nine failure arms of the lemma below (task #67).  The `throw` messages are
the cited ones verbatim: `ErrSim` never compares them, but spelling them out
keeps the closing `simp` off a metavariable. -/

open ConLeche.Cached in
/-- `checkIotaSidesTy` passes on what the left side's inference threw. -/
theorem checkIotaSidesTy_err_lhs_infer {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS : ConLeche.Expr} {lA : ConLeche.Level} {nm : ConLeche.Name}
    {lst : CState} {le : ConLeche.CheckError}
    (h1 : (ops.inferType lenv depth lhsS).run lst = .error le) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .error le := by
  rw [ConLeche.checkIotaSidesTy]; exact run_bind_err h1

open ConLeche.Cached in
/-- `checkIotaSidesTy` passes on what the left side's comparison threw. -/
theorem checkIotaSidesTy_err_lhs_defeq {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS tl : ConLeche.Expr} {lA : ConLeche.Level} {nm : ConLeche.Name}
    {lst lst1 : CState} {le : ConLeche.CheckError}
    (h1 : (ops.inferType lenv depth lhsS).run lst = .ok (tl, lst1))
    (h2 : (ops.isDefEq lenv depth tl alphaS).run lst1 = .error le) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .error le := by
  rw [ConLeche.checkIotaSidesTy, run_bind h1]; exact run_bind_err h2

open ConLeche.Cached in
/-- `checkIotaSidesTy`'s left-side `throw` (`Modeled.lean:43`). -/
theorem checkIotaSidesTy_lhs_mismatch {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS tl : ConLeche.Expr} {lA : ConLeche.Level} {nm : ConLeche.Name}
    {lst lst1 lst2 : CState}
    (h1 : (ops.inferType lenv depth lhsS).run lst = .ok (tl, lst1))
    (h2 : (ops.isDefEq lenv depth tl alphaS).run lst1 = .ok (false, lst2)) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .error (.notImplemented s!"iota statement lhs type for {nm}") := by
  rw [ConLeche.checkIotaSidesTy, run_bind h1, run_bind h2]
  simp only
  exact run_bind_err (throw_apply _ _)

open ConLeche.Cached in
/-- `checkIotaSidesTy` passes on what the right side's inference threw. -/
theorem checkIotaSidesTy_err_rhs_infer {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS tl : ConLeche.Expr} {lA : ConLeche.Level} {nm : ConLeche.Name}
    {lst lst1 lst2 : CState} {le : ConLeche.CheckError}
    (h1 : (ops.inferType lenv depth lhsS).run lst = .ok (tl, lst1))
    (h2 : (ops.isDefEq lenv depth tl alphaS).run lst1 = .ok (true, lst2))
    (h3 : (ops.inferType lenv depth rhsS).run lst2 = .error le) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .error le := by
  rw [ConLeche.checkIotaSidesTy, run_bind h1, run_bind h2]
  simp only [reduceIte]
  exact run_bind_err h3

open ConLeche.Cached in
/-- `checkIotaSidesTy` passes on what the right side's comparison threw. -/
theorem checkIotaSidesTy_err_rhs_defeq {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS tl tr : ConLeche.Expr} {lA : ConLeche.Level}
    {nm : ConLeche.Name} {lst lst1 lst2 lst3 : CState} {le : ConLeche.CheckError}
    (h1 : (ops.inferType lenv depth lhsS).run lst = .ok (tl, lst1))
    (h2 : (ops.isDefEq lenv depth tl alphaS).run lst1 = .ok (true, lst2))
    (h3 : (ops.inferType lenv depth rhsS).run lst2 = .ok (tr, lst3))
    (h4 : (ops.isDefEq lenv depth tr alphaS).run lst3 = .error le) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .error le := by
  rw [ConLeche.checkIotaSidesTy, run_bind h1, run_bind h2]
  simp only [reduceIte]
  rw [run_bind h3]
  exact run_bind_err h4

open ConLeche.Cached in
/-- `checkIotaSidesTy`'s right-side `throw` (`Modeled.lean:46`). -/
theorem checkIotaSidesTy_rhs_mismatch {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS tl tr : ConLeche.Expr} {lA : ConLeche.Level}
    {nm : ConLeche.Name} {lst lst1 lst2 lst3 lst4 : CState}
    (h1 : (ops.inferType lenv depth lhsS).run lst = .ok (tl, lst1))
    (h2 : (ops.isDefEq lenv depth tl alphaS).run lst1 = .ok (true, lst2))
    (h3 : (ops.inferType lenv depth rhsS).run lst2 = .ok (tr, lst3))
    (h4 : (ops.isDefEq lenv depth tr alphaS).run lst3 = .ok (false, lst4)) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .error (.notImplemented s!"iota statement rhs type for {nm}") := by
  rw [ConLeche.checkIotaSidesTy, run_bind h1, run_bind h2]
  simp only [reduceIte]
  rw [run_bind h3, run_bind h4]
  exact run_bind_err (throw_apply _ _)

open ConLeche.Cached in
/-- `checkIotaSidesTy` passes on what the slot's inference threw (TT lane). -/
theorem checkIotaSidesTy_err_slot_infer {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS tl tr : ConLeche.Expr} {lA : ConLeche.Level}
    {nm : ConLeche.Name} {lst lst1 lst2 lst3 lst4 : CState}
    {le : ConLeche.CheckError} (htt : mode'.ttChecks = true)
    (h1 : (ops.inferType lenv depth lhsS).run lst = .ok (tl, lst1))
    (h2 : (ops.isDefEq lenv depth tl alphaS).run lst1 = .ok (true, lst2))
    (h3 : (ops.inferType lenv depth rhsS).run lst2 = .ok (tr, lst3))
    (h4 : (ops.isDefEq lenv depth tr alphaS).run lst3 = .ok (true, lst4))
    (h5 : (ops.inferType lenv depth alphaS).run lst4 = .error le) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .error le := by
  rw [ConLeche.checkIotaSidesTy, run_bind h1, run_bind h2]
  simp only [reduceIte]
  rw [run_bind h3, run_bind h4]
  simp only [reduceIte, htt]
  exact run_bind_err h5

open ConLeche.Cached in
/-- `checkIotaSidesTy` passes on what the slot's comparison threw (TT lane). -/
theorem checkIotaSidesTy_err_slot_defeq {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS tl tr ta : ConLeche.Expr} {lA : ConLeche.Level}
    {nm : ConLeche.Name} {lst lst1 lst2 lst3 lst4 lst5 : CState}
    {le : ConLeche.CheckError} (htt : mode'.ttChecks = true)
    (h1 : (ops.inferType lenv depth lhsS).run lst = .ok (tl, lst1))
    (h2 : (ops.isDefEq lenv depth tl alphaS).run lst1 = .ok (true, lst2))
    (h3 : (ops.inferType lenv depth rhsS).run lst2 = .ok (tr, lst3))
    (h4 : (ops.isDefEq lenv depth tr alphaS).run lst3 = .ok (true, lst4))
    (h5 : (ops.inferType lenv depth alphaS).run lst4 = .ok (ta, lst5))
    (h6 : (ops.isDefEq lenv depth ta (.sort lA)).run lst5 = .error le) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .error le := by
  rw [ConLeche.checkIotaSidesTy, run_bind h1, run_bind h2]
  simp only [reduceIte]
  rw [run_bind h3, run_bind h4]
  simp only [reduceIte, htt]
  rw [run_bind h5]
  exact run_bind_err h6

open ConLeche.Cached in
/-- `checkIotaSidesTy`'s slot-sort `throw` (`Modeled.lean:52`, TT lane). -/
theorem checkIotaSidesTy_slot_mismatch {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env} {depth : Nat}
    {alphaS lhsS rhsS tl tr ta : ConLeche.Expr} {lA : ConLeche.Level}
    {nm : ConLeche.Name} {lst lst1 lst2 lst3 lst4 lst5 lst6 : CState}
    (htt : mode'.ttChecks = true)
    (h1 : (ops.inferType lenv depth lhsS).run lst = .ok (tl, lst1))
    (h2 : (ops.isDefEq lenv depth tl alphaS).run lst1 = .ok (true, lst2))
    (h3 : (ops.inferType lenv depth rhsS).run lst2 = .ok (tr, lst3))
    (h4 : (ops.isDefEq lenv depth tr alphaS).run lst3 = .ok (true, lst4))
    (h5 : (ops.inferType lenv depth alphaS).run lst4 = .ok (ta, lst5))
    (h6 : (ops.isDefEq lenv depth ta (.sort lA)).run lst5 = .ok (false, lst6)) :
    (ConLeche.checkIotaSidesTy mode' ops lenv depth alphaS lhsS rhsS lA nm).run lst
      = .error (.notImplemented
          s!"iota statement type slot sort for {nm}") := by
  rw [ConLeche.checkIotaSidesTy, run_bind h1, run_bind h2]
  simp only [reduceIte]
  rw [run_bind h3, run_bind h4]
  simp only [reduceIte, htt]
  rw [run_bind h5, run_bind h6]
  exact throw_apply _ _

/-- `ConLeche/Kernel/Inductives/Modeled.lean:40-53 checkIotaSidesTy` —
**`modeled::check_iota_sides_ty` refines it**: the two sides' inferred types
are the slot, and in the TT lane the slot is a sort at the head's level.  The
cited `cvName` argument only names the error, so it is universally
quantified. -/
theorem check_iota_sides_ty_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {depth : Std.U64}
    {alpha_s lhs_s rhs_s : expr.Expr} {l_a : level.Level}
    {out : core.result.Result Unit core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (ha : ExprWF alpha_s)
    (hl : ExprWF lhs_s) (hr : ExprWF rhs_s) (hla : LevelWF l_a)
    (h : inductives.modeled.check_iota_sides_ty mode st fe depth alpha_s lhs_s
      rhs_s l_a = ok (out, st')) :
    ∀ (lst : ConLeche.Cached.CState) (lfe : ConLeche.FEnv) (nm : ConLeche.Name),
      StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok _ =>
        ∃ lst', (ConLeche.checkIotaSidesTy (absMode mode)
              (TypeChecker.lops mode lfe) lfe.env depth.val (absExpr alpha_s)
              (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a) nm).run lst
            = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err e =>
        ErrSim e ((ConLeche.checkIotaSidesTy (absMode mode)
            (TypeChecker.lops mode lfe) lfe.env depth.val (absExpr alpha_s)
            (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a) nm).run lst) := by
  intro lst lfe nm hsr hfr
  rw [inductives.modeled.check_iota_sides_ty] at h
  replace h := TypeChecker.at_check_fuel hfuel h
  obtain ⟨q1, hq1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r1, st1⟩ := q1
  cases r1 with
  | Err e1 =>
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    exact ErrSim.trans
      ((TypeChecker.infer_type_core_refines hfuel hk).err st fe depth lhs_s e1 st1
        hsw hfw hl (infer_at_fuel hfuel hq1) lst lfe hsr hfr)
      (fun le hle => checkIotaSidesTy_err_lhs_infer hle)
  | Ok tl =>
    obtain ⟨lst1, hrun1, hsr1, hsw1, htlwf⟩ :=
      (TypeChecker.infer_type_core_refines hfuel hk).ok st fe depth lhs_s tl st1
        hsw hfw hl (infer_at_fuel hfuel hq1) lst lfe hsr hfr
    have e1 : ((TypeChecker.lops mode lfe).inferType lfe.env depth.val
        (absExpr lhs_s)).run lst = .ok (absExpr tl, lst1) := by
      rw [TypeChecker.sharedOpsC_inferType]; exact hrun1
    obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r2, st2⟩ := q2
    cases r2 with
    | Err e2 =>
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      exact ErrSim.trans
        ((TypeChecker.is_def_eq_core_refines hfuel hk).err st1 fe depth tl alpha_s
          e2 st2 hsw1 hfw htlwf ha (defeq_at_fuel hfuel hq2) lst1 lfe hsr1 hfr)
        (fun le hle => checkIotaSidesTy_err_lhs_defeq e1 hle)
    | Ok b =>
      obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
        (TypeChecker.is_def_eq_core_refines hfuel hk).ok st1 fe depth tl alpha_s b st2
          hsw1 hfw htlwf ha (defeq_at_fuel hfuel hq2) lst1 lfe hsr1 hfr
      have e2 : ((TypeChecker.lops mode lfe).isDefEq lfe.env depth.val
          (absExpr tl) (absExpr alpha_s)).run lst1 = .ok (b, lst2) := by
        rw [TypeChecker.sharedOpsC_isDefEq]; exact hrun2
      cases b with
      | false =>
        -- `modeled.rs:288` ← `Modeled.lean:43`
        simp only at h
        obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        exact errSim_notImplemented hce rfl (checkIotaSidesTy_lhs_mismatch e1 e2)
      | true =>
        simp only at h
        obtain ⟨q3, hq3, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r3, st3⟩ := q3
        cases r3 with
        | Err e3 =>
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          exact ErrSim.trans
            ((TypeChecker.infer_type_core_refines hfuel hk).err st2 fe depth rhs_s
              e3 st3 hsw2 hfw hr (infer_at_fuel hfuel hq3) lst2 lfe hsr2 hfr)
            (fun le hle => checkIotaSidesTy_err_rhs_infer e1 e2 hle)
        | Ok tr =>
          obtain ⟨lst3, hrun3, hsr3, hsw3, htrwf⟩ :=
            (TypeChecker.infer_type_core_refines hfuel hk).ok st2 fe depth rhs_s tr st3
              hsw2 hfw hr (infer_at_fuel hfuel hq3) lst2 lfe hsr2 hfr
          have e3 : ((TypeChecker.lops mode lfe).inferType lfe.env depth.val
              (absExpr rhs_s)).run lst2 = .ok (absExpr tr, lst3) := by
            rw [TypeChecker.sharedOpsC_inferType]; exact hrun3
          obtain ⟨q4, hq4, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨r4, st4⟩ := q4
          cases r4 with
          | Err e4 =>
            obtain ⟨hout, -⟩ := err_outS h
            subst hout
            exact ErrSim.trans
              ((TypeChecker.is_def_eq_core_refines hfuel hk).err st3 fe depth tr
                alpha_s e4 st4 hsw3 hfw htrwf ha (defeq_at_fuel hfuel hq4) lst3 lfe
                hsr3 hfr)
              (fun le hle => checkIotaSidesTy_err_rhs_defeq e1 e2 e3 hle)
          | Ok b1 =>
            obtain ⟨lst4, hrun4, hsr4, hsw4⟩ :=
              (TypeChecker.is_def_eq_core_refines hfuel hk).ok st3 fe depth tr alpha_s
                b1 st4 hsw3 hfw htrwf ha (defeq_at_fuel hfuel hq4) lst3 lfe hsr3 hfr
            have e4 : ((TypeChecker.lops mode lfe).isDefEq lfe.env depth.val
                (absExpr tr) (absExpr alpha_s)).run lst3 = .ok (b1, lst4) := by
              rw [TypeChecker.sharedOpsC_isDefEq]; exact hrun4
            cases b1 with
            | false =>
              -- `modeled.rs:292` ← `Modeled.lean:46`
              simp only at h
              obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hout, -⟩ := err_outS h
              subst hout
              exact errSim_notImplemented hce rfl
                (checkIotaSidesTy_rhs_mismatch e1 e2 e3 e4)
            | true =>
              simp only at h
              obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
              have hb2abs := Env.tt_checks_refines hb2
              cases b2 with
              | false =>
                simp only [Bool.false_eq_true, if_false] at h
                obtain ⟨hout, rfl⟩ := ok_outS h
                subst hout
                exact ⟨lst4, checkIotaSidesTy_run_ff (by rw [← hb2abs]) e1 e2 e3 e4,
                  hsr4, hsw4⟩
              | true =>
                have htt : (absMode mode).ttChecks = true := by rw [← hb2abs]
                simp only [reduceIte] at h
                obtain ⟨q5, hq5, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨r5, st5⟩ := q5
                cases r5 with
                | Err e5 =>
                  obtain ⟨hout, -⟩ := err_outS h
                  subst hout
                  exact ErrSim.trans
                    ((TypeChecker.infer_type_core_refines hfuel hk).err st4 fe depth
                      alpha_s e5 st5 hsw4 hfw ha (infer_at_fuel hfuel hq5) lst4 lfe
                      hsr4 hfr)
                    (fun le hle =>
                      checkIotaSidesTy_err_slot_infer htt e1 e2 e3 e4 hle)
                | Ok ta =>
                  obtain ⟨lst5, hrun5, hsr5, hsw5, htawf⟩ :=
                    (TypeChecker.infer_type_core_refines hfuel hk).ok st4 fe depth
                      alpha_s ta st5 hsw4 hfw ha (infer_at_fuel hfuel hq5) lst4
                      lfe hsr4 hfr
                  have e5 : ((TypeChecker.lops mode lfe).inferType lfe.env depth.val
                      (absExpr alpha_s)).run lst4 = .ok (absExpr ta, lst5) := by
                    rw [TypeChecker.sharedOpsC_inferType]; exact hrun5
                  simp only [level_dup_eq, bind_tc_ok] at h
                  obtain ⟨se, hse, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨q6, hq6, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨r6, st6⟩ := q6
                  cases r6 with
                  | Err e6 =>
                    obtain ⟨hout, -⟩ := err_outS h
                    subst hout
                    have hsim := (TypeChecker.is_def_eq_core_refines hfuel hk).err st5
                      fe depth ta se e6 st6 hsw5 hfw htawf (Expr.sort_wf hla hse)
                      (defeq_at_fuel hfuel hq6) lst5 lfe hsr5 hfr
                    rw [Expr.sort_refines hse] at hsim
                    exact ErrSim.trans hsim
                      (fun le hle =>
                        checkIotaSidesTy_err_slot_defeq htt e1 e2 e3 e4 e5 hle)
                  | Ok b3 =>
                    obtain ⟨lst6, hrun6, hsr6, hsw6⟩ :=
                      (TypeChecker.is_def_eq_core_refines hfuel hk).ok st5 fe depth ta
                        se b3 st6 hsw5 hfw htawf (Expr.sort_wf hla hse)
                        (defeq_at_fuel hfuel hq6) lst5 lfe hsr5 hfr
                    rw [Expr.sort_refines hse] at hrun6
                    have e6 : ((TypeChecker.lops mode lfe).isDefEq lfe.env depth.val
                        (absExpr ta) (ConLeche.Expr.sort (absLevel l_a))).run lst5
                        = .ok (b3, lst6) := by
                      rw [TypeChecker.sharedOpsC_isDefEq]; exact hrun6
                    cases b3 with
                    | false =>
                      -- `modeled.rs:296` ← `Modeled.lean:52`
                      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
                      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
                      obtain ⟨hout, -⟩ := err_outS h
                      subst hout
                      exact errSim_notImplemented hce rfl
                        (checkIotaSidesTy_slot_mismatch htt e1 e2 e3 e4 e5 e6)
                    | true =>
                      obtain ⟨hout, rfl⟩ := ok_outS h
                      subst hout
                      exact ⟨lst6, checkIotaSidesTy_run_tt htt e1 e2 e3 e4 e5 e6,
                        hsr6, hsw6⟩

/-! ### The iota body and the spine shape

`checkProjIotaF` reads the statement's body through the cited nested-`app`
pattern `.app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC`; the port reads
it through `get_app_fn`/`get_app_args` and an arity test, which is the same
thing for any expression (`spine_eq`).  The `do` is split at the domain check
(task #24's rule 7), so the tail gets a `def` here that is the cited fragment
verbatim, and `check_proj_iota_refines` is stated against the cited
`checkProjIotaF` itself. -/

/-- A model list of three entries, listed out. -/
theorem len_eq_three {α : Type} {l : List α} (h : l.length = 3) :
    ∃ a0 a1 a2, l = [a0, a1, a2] := by
  rcases l with _ | ⟨a0, l⟩; · simp at h
  rcases l with _ | ⟨a1, l⟩; · simp at h
  rcases l with _ | ⟨a2, l⟩; · simp at h
  rcases l with _ | ⟨a3, l⟩
  · exact ⟨a0, a1, a2, rfl⟩
  · simp at h

/-- `mkAppN` over an append. -/
theorem mkAppN_append (xs : List ConLeche.Expr) :
    ∀ (f : ConLeche.Expr) (bs : List ConLeche.Expr),
      ConLeche.Expr.mkAppN f (xs ++ bs)
        = ConLeche.Expr.mkAppN (ConLeche.Expr.mkAppN f xs) bs := by
  induction xs with
  | nil => intro f bs; simp [ConLeche.Expr.mkAppN]
  | cons a ys ih => intro f bs; simp [ConLeche.Expr.mkAppN, ih]

/-- **An expression is its spine**: `mkAppN e.getAppFn e.getAppArgs = e`. -/
theorem spine_eq : ∀ e : ConLeche.Expr,
    ConLeche.Expr.mkAppN e.getAppFn e.getAppArgs = e := by
  intro e
  induction e with
  | app f a ihf _ =>
    show ConLeche.Expr.mkAppN f.getAppFn (f.getAppArgs ++ [a]) = _
    rw [mkAppN_append, ihf]
    simp [ConLeche.Expr.mkAppN]
  | _ => rfl

/-- The cited three-argument pattern, from the port's spine reading. -/
theorem app3_of_spine {e g a0 a1 a2 : ConLeche.Expr}
    (hfn : e.getAppFn = g) (hargs : e.getAppArgs = [a0, a1, a2]) :
    e = .app (.app (.app g a0) a1) a2 := by
  have hs := spine_eq e
  rw [hfn, hargs] at hs
  rw [← hs]
  simp [ConLeche.Expr.mkAppN]

/-- The cited three-argument pattern's arguments, read back. -/
theorem getAppArgs_app3_const (c : ConLeche.Name) (lu : ConLeche.Level)
    (t a b : ConLeche.Expr) :
    (ConLeche.Expr.app (.app (.app (.const c [lu]) t) a) b).getAppArgs
      = [t, a, b] := by
  simp [ConLeche.Expr.getAppArgs]

/-- The cited three-argument pattern's head, read back. -/
theorem getAppFn_app3_const (c : ConLeche.Name) (lu : ConLeche.Level)
    (t a b : ConLeche.Expr) :
    (ConLeche.Expr.app (.app (.app (.const c [lu]) t) a) b).getAppFn
      = .const c [lu] := by
  simp [ConLeche.Expr.getAppFn]

/-- `isEqHead` accepted: the head *is* the pinned equality former at one
level (`CheckerBase.lean:186-189`). -/
theorem isEqHead_inv {e : ConLeche.Expr} (h : ConLeche.isEqHead e = true) :
    ∃ l, e = .const ConLeche.eqName [l] := by
  unfold ConLeche.isEqHead at h
  split at h
  · rename_i c l; exact ⟨l, by simp_all⟩
  · simp at h

open ConLeche.Cached in
/-- The tail of `checkProjIotaF` past the domain check
(`ConLeche/Kernel/DeclCheck.lean:812-836`), written out because the port
splits the `do` there (task #24's deviation 7). -/
def projIotaTail (mode' : ConLeche.CheckMode) (ops : ConLeche.CheckerOps CheckCM)
    (lenv : ConLeche.Env) (T ctorName : ConLeche.Name)
    (cvj : ConLeche.ConstantVal) (lps : List ConLeche.Name) (nP nF i : Nat)
    (tcvTy sbody : ConLeche.Expr) : CheckCM Unit := do
  let depth := nP + nF
  let pArgs := (List.range nP).map fun k => ConLeche.Expr.bvar (depth - 1 - k)
  let xArgs := (List.range nF).map fun k => ConLeche.Expr.bvar (nF - 1 - k)
  let mkSpine := ConLeche.Expr.mkAppN
    (.const (ctorName.str "_model") (cvj.levelParams.map .param)) (pArgs ++ xArgs)
  let lhsS := ConLeche.Expr.mkAppN
    (.const (ConLeche.projModelName T i) (lps.map .param)) (pArgs ++ [mkSpine])
  match sbody with
  | .app (.app (.app (.const c [_l]) _tySlot) lhsC) rhsC =>
    unless c = ConLeche.eqName do
      throw (.notImplemented "projection iota head")
    unless lhsC == lhsS do
      throw (.notImplemented "projection iota redex mismatch")
    unless rhsC == ConLeche.Expr.bvar (nF - 1 - i) do
      throw (.notImplemented "projection iota field mismatch")
  | _ => throw (.notImplemented "projection iota body shape")
  let (_, sbodyO) ← ConLeche.unwrapOr (ConLeche.openPisAtFvars depth tcvTy 0)
    (.notImplemented "projection iota telescope")
  let targsO := sbodyO.getAppArgs
  ConLeche.checkIotaSidesTy mode' ops lenv depth (targsO.getD 0 (.bvar 0))
    (targsO.getD 1 (.bvar 0)) (targsO.getD 2 (.bvar 0))
    (ConLeche.eqHeadLevel sbody.getAppFn) (ConLeche.projModelName T i)

open ConLeche.Cached in
/-- `projIotaTail` with the body pattern already destructured: the same `do`
with the cited `match` gone, so that the guards are reachable by `rw`. -/
def projIotaTailAt (mode' : ConLeche.CheckMode) (ops : ConLeche.CheckerOps CheckCM)
    (lenv : ConLeche.Env) (T ctorName : ConLeche.Name)
    (cvj : ConLeche.ConstantVal) (lps : List ConLeche.Name) (nP nF i : Nat)
    (tcvTy : ConLeche.Expr) (c : ConLeche.Name) (lu : ConLeche.Level)
    (lhsC rhsC : ConLeche.Expr) : CheckCM Unit := do
  let depth := nP + nF
  let pArgs := (List.range nP).map fun k => ConLeche.Expr.bvar (depth - 1 - k)
  let xArgs := (List.range nF).map fun k => ConLeche.Expr.bvar (nF - 1 - k)
  let mkSpine := ConLeche.Expr.mkAppN
    (.const (ctorName.str "_model") (cvj.levelParams.map .param)) (pArgs ++ xArgs)
  let lhsS := ConLeche.Expr.mkAppN
    (.const (ConLeche.projModelName T i) (lps.map .param)) (pArgs ++ [mkSpine])
  unless c = ConLeche.eqName do
    throw (.notImplemented "projection iota head")
  unless lhsC == lhsS do
    throw (.notImplemented "projection iota redex mismatch")
  unless rhsC == ConLeche.Expr.bvar (nF - 1 - i) do
    throw (.notImplemented "projection iota field mismatch")
  let (_, sbodyO) ← ConLeche.unwrapOr (ConLeche.openPisAtFvars depth tcvTy 0)
    (.notImplemented "projection iota telescope")
  let targsO := sbodyO.getAppArgs
  ConLeche.checkIotaSidesTy mode' ops lenv depth (targsO.getD 0 (.bvar 0))
    (targsO.getD 1 (.bvar 0)) (targsO.getD 2 (.bvar 0))
    (ConLeche.eqHeadLevel (.const c [lu])) (ConLeche.projModelName T i)

open ConLeche.Cached in
/-- The cited `match` on a body of the accepted shape *is* its first arm. -/
theorem projIotaTail_at {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {T ctorName : ConLeche.Name} {cvj : ConLeche.ConstantVal}
    {lps : List ConLeche.Name} {nP nF i : Nat} {tcvTy tslot lhsC rhsC : ConLeche.Expr}
    {c : ConLeche.Name} {lu : ConLeche.Level} :
    projIotaTail mode' ops lenv T ctorName cvj lps nP nF i tcvTy
        (.app (.app (.app (.const c [lu]) tslot) lhsC) rhsC)
      = projIotaTailAt mode' ops lenv T ctorName cvj lps nP nF i tcvTy c lu
          lhsC rhsC := rfl

open ConLeche.Cached in
/-- `projIotaTail` at a run whose body pattern matched and whose three body
guards held. -/
theorem projIotaTail_run {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {T ctorName : ConLeche.Name} {cvj : ConLeche.ConstantVal}
    {lps : List ConLeche.Name} {nP nF i : Nat}
    {tcvTy sbody tslot lhsC rhsC sbodyO : ConLeche.Expr} {lu : ConLeche.Level}
    {fvs : List ConLeche.Expr} {lst lst' : CState}
    (hshape : sbody
        = .app (.app (.app (.const ConLeche.eqName [lu]) tslot) lhsC) rhsC)
    (h7 : (lhsC == ConLeche.Expr.mkAppN
        (.const (ConLeche.projModelName T i) (lps.map .param))
        (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
          ++ [ConLeche.Expr.mkAppN
              (.const (ctorName.str "_model") (cvj.levelParams.map .param))
              (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
                ++ ((List.range nF).map fun k =>
                      ConLeche.Expr.bvar (nF - 1 - k)))])) = true)
    (h8 : (rhsC == ConLeche.Expr.bvar (nF - 1 - i)) = true)
    (h9 : ConLeche.openPisAtFvars (nP + nF) tcvTy 0 = some (fvs, sbodyO))
    (h10 : (ConLeche.checkIotaSidesTy mode' ops lenv (nP + nF)
        (sbodyO.getAppArgs.getD 0 (.bvar 0)) (sbodyO.getAppArgs.getD 1 (.bvar 0))
        (sbodyO.getAppArgs.getD 2 (.bvar 0))
        (ConLeche.eqHeadLevel (.const ConLeche.eqName [lu]))
        (ConLeche.projModelName T i)).run lst = .ok ((), lst')) :
    (projIotaTail mode' ops lenv T ctorName cvj lps nP nF i tcvTy sbody).run lst
      = .ok ((), lst') := by
  subst hshape
  rw [projIotaTail_at, projIotaTailAt]
  simp only [h7, h8, h9, ConLeche.unwrapOr, reduceIte]
  exact h10

open ConLeche.Cached in
/-- `projIotaTail`'s off-shape `throw` (`DeclCheck.lean:825`): the statement's
body is not the cited three-argument application of a one-level constant. -/
theorem projIotaTail_shape {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {T ctorName : ConLeche.Name} {cvj : ConLeche.ConstantVal}
    {lps : List ConLeche.Name} {nP nF i : Nat} {tcvTy sbody : ConLeche.Expr}
    {lst : CState}
    (hs : ∀ (c : ConLeche.Name) (lu : ConLeche.Level) (t a b : ConLeche.Expr),
      sbody ≠ .app (.app (.app (.const c [lu]) t) a) b) :
    (projIotaTail mode' ops lenv T ctorName cvj lps nP nF i tcvTy sbody).run lst
      = .error (.notImplemented "projection iota body shape") := by
  rw [projIotaTail]
  · exact run_bind_err (throw_apply _ _)
  · intro c lu t a b heq
    exact hs c lu t a b heq

open ConLeche.Cached in
/-- `projIotaTail`'s head `throw` (`DeclCheck.lean:818`). -/
theorem projIotaTail_head {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {T ctorName : ConLeche.Name} {cvj : ConLeche.ConstantVal}
    {lps : List ConLeche.Name} {nP nF i : Nat}
    {tcvTy sbody tslot lhsC rhsC : ConLeche.Expr} {c : ConLeche.Name}
    {lu : ConLeche.Level} {lst : CState}
    (hshape : sbody = .app (.app (.app (.const c [lu]) tslot) lhsC) rhsC)
    (hc : c ≠ ConLeche.eqName) :
    (projIotaTail mode' ops lenv T ctorName cvj lps nP nF i tcvTy sbody).run lst
      = .error (.notImplemented "projection iota head") := by
  subst hshape
  rw [projIotaTail_at, projIotaTailAt]
  simp only [if_neg hc]
  exact run_bind_err (throw_apply _ _)

open ConLeche.Cached in
/-- `projIotaTail`'s redex `throw` (`DeclCheck.lean:820`). -/
theorem projIotaTail_redex {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {T ctorName : ConLeche.Name} {cvj : ConLeche.ConstantVal}
    {lps : List ConLeche.Name} {nP nF i : Nat}
    {tcvTy sbody tslot lhsC rhsC : ConLeche.Expr} {lu : ConLeche.Level}
    {lst : CState}
    (hshape : sbody
        = .app (.app (.app (.const ConLeche.eqName [lu]) tslot) lhsC) rhsC)
    (h7 : (lhsC == ConLeche.Expr.mkAppN
        (.const (ConLeche.projModelName T i) (lps.map .param))
        (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
          ++ [ConLeche.Expr.mkAppN
              (.const (ctorName.str "_model") (cvj.levelParams.map .param))
              (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
                ++ ((List.range nF).map fun k =>
                      ConLeche.Expr.bvar (nF - 1 - k)))])) = false) :
    (projIotaTail mode' ops lenv T ctorName cvj lps nP nF i tcvTy sbody).run lst
      = .error (.notImplemented "projection iota redex mismatch") := by
  subst hshape
  rw [projIotaTail_at, projIotaTailAt]
  simp only [h7, reduceIte, Bool.false_eq_true, if_false, run_pure_bind]
  exact run_bind_err (throw_apply _ _)

open ConLeche.Cached in
/-- `projIotaTail`'s field `throw` (`DeclCheck.lean:822`). -/
theorem projIotaTail_field {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {T ctorName : ConLeche.Name} {cvj : ConLeche.ConstantVal}
    {lps : List ConLeche.Name} {nP nF i : Nat}
    {tcvTy sbody tslot lhsC rhsC : ConLeche.Expr} {lu : ConLeche.Level}
    {lst : CState}
    (hshape : sbody
        = .app (.app (.app (.const ConLeche.eqName [lu]) tslot) lhsC) rhsC)
    (h7 : (lhsC == ConLeche.Expr.mkAppN
        (.const (ConLeche.projModelName T i) (lps.map .param))
        (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
          ++ [ConLeche.Expr.mkAppN
              (.const (ctorName.str "_model") (cvj.levelParams.map .param))
              (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
                ++ ((List.range nF).map fun k =>
                      ConLeche.Expr.bvar (nF - 1 - k)))])) = true)
    (h8 : (rhsC == ConLeche.Expr.bvar (nF - 1 - i)) = false) :
    (projIotaTail mode' ops lenv T ctorName cvj lps nP nF i tcvTy sbody).run lst
      = .error (.notImplemented "projection iota field mismatch") := by
  subst hshape
  rw [projIotaTail_at, projIotaTailAt]
  simp only [h7, h8, reduceIte, Bool.false_eq_true, if_false, run_pure_bind]
  exact run_bind_err (throw_apply _ _)

open ConLeche.Cached in
/-- `projIotaTail`'s telescope `throw` (`DeclCheck.lean:824`). -/
theorem projIotaTail_telescope {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {T ctorName : ConLeche.Name} {cvj : ConLeche.ConstantVal}
    {lps : List ConLeche.Name} {nP nF i : Nat}
    {tcvTy sbody tslot lhsC rhsC : ConLeche.Expr} {lu : ConLeche.Level}
    {lst : CState}
    (hshape : sbody
        = .app (.app (.app (.const ConLeche.eqName [lu]) tslot) lhsC) rhsC)
    (h7 : (lhsC == ConLeche.Expr.mkAppN
        (.const (ConLeche.projModelName T i) (lps.map .param))
        (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
          ++ [ConLeche.Expr.mkAppN
              (.const (ctorName.str "_model") (cvj.levelParams.map .param))
              (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
                ++ ((List.range nF).map fun k =>
                      ConLeche.Expr.bvar (nF - 1 - k)))])) = true)
    (h8 : (rhsC == ConLeche.Expr.bvar (nF - 1 - i)) = true)
    (h9 : ConLeche.openPisAtFvars (nP + nF) tcvTy 0 = none) :
    (projIotaTail mode' ops lenv T ctorName cvj lps nP nF i tcvTy sbody).run lst
      = .error (.notImplemented "projection iota telescope") := by
  subst hshape
  rw [projIotaTail_at, projIotaTailAt]
  simp only [h7, h8, h9, ConLeche.unwrapOr, reduceIte, run_pure_bind]
  exact run_bind_err (throw_apply _ _)

open ConLeche.Cached in
/-- `projIotaTail` passes on what the two side certificates threw. -/
theorem projIotaTail_sides_err {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {T ctorName : ConLeche.Name} {cvj : ConLeche.ConstantVal}
    {lps : List ConLeche.Name} {nP nF i : Nat}
    {tcvTy sbody tslot lhsC rhsC sbodyO : ConLeche.Expr} {lu : ConLeche.Level}
    {fvs : List ConLeche.Expr} {lst : CState} {le : ConLeche.CheckError}
    (hshape : sbody
        = .app (.app (.app (.const ConLeche.eqName [lu]) tslot) lhsC) rhsC)
    (h7 : (lhsC == ConLeche.Expr.mkAppN
        (.const (ConLeche.projModelName T i) (lps.map .param))
        (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
          ++ [ConLeche.Expr.mkAppN
              (.const (ctorName.str "_model") (cvj.levelParams.map .param))
              (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
                ++ ((List.range nF).map fun k =>
                      ConLeche.Expr.bvar (nF - 1 - k)))])) = true)
    (h8 : (rhsC == ConLeche.Expr.bvar (nF - 1 - i)) = true)
    (h9 : ConLeche.openPisAtFvars (nP + nF) tcvTy 0 = some (fvs, sbodyO))
    (h10 : (ConLeche.checkIotaSidesTy mode' ops lenv (nP + nF)
        (sbodyO.getAppArgs.getD 0 (.bvar 0)) (sbodyO.getAppArgs.getD 1 (.bvar 0))
        (sbodyO.getAppArgs.getD 2 (.bvar 0))
        (ConLeche.eqHeadLevel (.const ConLeche.eqName [lu]))
        (ConLeche.projModelName T i)).run lst = .error le) :
    (projIotaTail mode' ops lenv T ctorName cvj lps nP nF i tcvTy sbody).run lst
      = .error le := by
  subst hshape
  rw [projIotaTail_at, projIotaTailAt]
  simp only [h7, h8, h9, ConLeche.unwrapOr, reduceIte]
  exact h10

/-- The port's head-shape test, inverted: an abstracted head that is a
one-level `.const` has a `Const` node kind at a one-element level vector, which
is what `check_proj_iota_body`'s shape `match` answers `true` on. -/
private theorem const_kind_of_abs {e : expr.Expr} {c : ConLeche.Name}
    {lu : ConLeche.Level} (h : absExpr e = .const c [lu]) :
    ∃ (n : name.Name) (us : alloc.vec.Vec level.Level),
      e._0.kind = .Const n us ∧ us.val.length = 1 := by
  rw [absExpr_kind] at h
  cases hk : e._0.kind with
  | Const n us =>
    refine ⟨n, us, rfl, ?_⟩
    rw [hk] at h
    simp only [absExprKind, ConLeche.Expr.const.injEq] at h
    have hl := congrArg List.length h.2
    simpa [absLevels] using hl
  | Bvar _ => rw [hk] at h; simp [absExprKind] at h
  | Fvar _ _ => rw [hk] at h; simp [absExprKind] at h
  | «Sort» _ => rw [hk] at h; simp [absExprKind] at h
  | App _ _ => rw [hk] at h; simp [absExprKind] at h
  | Lam _ _ _ => rw [hk] at h; simp [absExprKind] at h
  | ForallE _ _ _ => rw [hk] at h; simp [absExprKind] at h
  | LetE _ _ _ => rw [hk] at h; simp [absExprKind] at h
  | Lit _ => rw [hk] at h; simp [absExprKind] at h
  | Proj _ _ _ => rw [hk] at h; simp [absExprKind] at h

open ConLeche.Cached in
/-- `ConLeche/Kernel/DeclCheck.lean:797-836 checkProjIotaF` — the cited
function *is* its prefix guards followed by `projIotaTail`. -/
theorem checkProjIotaF_at_tail {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name}
    {cvj tcv : ConLeche.ConstantVal} {nP nF i : Nat} {tval : ConLeche.Expr}
    {sbinders cbindersR : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {sbody cbody : ConLeche.Expr}
    (h1 : lfe.find? ((ConLeche.projModelName T i).str "iota")
        = some (.thmInfo tcv tval))
    (h2 : tcv.levelParams = lps)
    (h3 : tcv.type.stripPis (nP + nF) = some (sbinders, sbody))
    (h4 : cvj.type.stripPis (nP + nF) = some (cbindersR, cbody))
    (h5 : ConLeche.domsMatchAux
        (fun _ e => e.renameConsts (ConLeche.projFwd T ctorName nF))
        sbinders cbindersR 0 0 (nP + nF) = true) :
    ConLeche.checkProjIotaF mode' ops lfe T ctorName lps cvj nP nF i
      = projIotaTail mode' ops lfe.env T ctorName cvj lps nP nF i tcv.type sbody := by
  rw [ConLeche.checkProjIotaF]
  simp only [h1, h2, h3, h4, h5, reduceIte]
  rfl

open ConLeche.Cached in
/-- `checkProjIotaF`'s missing-theorem `throw` (`DeclCheck.lean:801`). -/
theorem checkProjIotaF_thm_none {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name}
    {cvj : ConLeche.ConstantVal} {nP nF i : Nat} {lst : CState}
    (h1 : thmOf (lfe.find? ((ConLeche.projModelName T i).str "iota")) = none) :
    (ConLeche.checkProjIotaF mode' ops lfe T ctorName lps cvj nP nF i).run lst
      = .error (.notImplemented "missing projection iota theorem") := by
  rw [ConLeche.checkProjIotaF]
  cases hx : lfe.find? ((ConLeche.projModelName T i).str "iota") with
  | none => rfl
  | some ci =>
    rw [hx] at h1
    cases ci with
    | axiomInfo _ => rfl
    | defnInfo _ _ _ => rfl
    | thmInfo _ _ => simp [thmOf] at h1
    | indInfo _ _ => rfl
    | ctorInfo _ _ _ => rfl
    | recInfo _ _ _ _ => rfl
    | projInfo _ => rfl

open ConLeche.Cached in
/-- `checkProjIotaF`'s level `throw` (`DeclCheck.lean:803`). -/
theorem checkProjIotaF_lps {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name}
    {cvj tcv : ConLeche.ConstantVal} {tval : ConLeche.Expr} {nP nF i : Nat}
    {lst : CState}
    (h1 : lfe.find? ((ConLeche.projModelName T i).str "iota")
        = some (.thmInfo tcv tval))
    (h2 : tcv.levelParams ≠ lps) :
    (ConLeche.checkProjIotaF mode' ops lfe T ctorName lps cvj nP nF i).run lst
      = .error (.notImplemented "projection iota level mismatch") := by
  rw [ConLeche.checkProjIotaF]
  simp only [h1, if_neg h2]
  rfl

open ConLeche.Cached in
/-- `checkProjIotaF`'s statement-telescope `throw` (`DeclCheck.lean:805`). -/
theorem checkProjIotaF_thm_tele {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name}
    {cvj tcv : ConLeche.ConstantVal} {tval : ConLeche.Expr} {nP nF i : Nat}
    {lst : CState}
    (h1 : lfe.find? ((ConLeche.projModelName T i).str "iota")
        = some (.thmInfo tcv tval))
    (h2 : tcv.levelParams = lps)
    (h3 : tcv.type.stripPis (nP + nF) = none) :
    (ConLeche.checkProjIotaF mode' ops lfe T ctorName lps cvj nP nF i).run lst
      = .error (.notImplemented "projection iota telescope") := by
  rw [ConLeche.checkProjIotaF]
  simp only [h1, h2, h3, reduceIte]
  rfl

open ConLeche.Cached in
/-- `checkProjIotaF`'s constructor-telescope `throw` (`DeclCheck.lean:807`). -/
theorem checkProjIotaF_ctor_tele {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name}
    {cvj tcv : ConLeche.ConstantVal} {tval sbody : ConLeche.Expr}
    {sbinders : List (ConLeche.Expr × ConLeche.BinderMeta)} {nP nF i : Nat}
    {lst : CState}
    (h1 : lfe.find? ((ConLeche.projModelName T i).str "iota")
        = some (.thmInfo tcv tval))
    (h2 : tcv.levelParams = lps)
    (h3 : tcv.type.stripPis (nP + nF) = some (sbinders, sbody))
    (h4 : cvj.type.stripPis (nP + nF) = none) :
    (ConLeche.checkProjIotaF mode' ops lfe T ctorName lps cvj nP nF i).run lst
      = .error (.notImplemented "projection constructor telescope") := by
  rw [ConLeche.checkProjIotaF]
  simp only [h1, h2, h3, h4, reduceIte]
  rfl

open ConLeche.Cached in
/-- `checkProjIotaF`'s domain `throw` (`DeclCheck.lean:811`). -/
theorem checkProjIotaF_doms {mode' : ConLeche.CheckMode}
    {ops : ConLeche.CheckerOps CheckCM} {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name}
    {cvj tcv : ConLeche.ConstantVal} {tval sbody cbody : ConLeche.Expr}
    {sbinders cbindersR : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {nP nF i : Nat} {lst : CState}
    (h1 : lfe.find? ((ConLeche.projModelName T i).str "iota")
        = some (.thmInfo tcv tval))
    (h2 : tcv.levelParams = lps)
    (h3 : tcv.type.stripPis (nP + nF) = some (sbinders, sbody))
    (h4 : cvj.type.stripPis (nP + nF) = some (cbindersR, cbody))
    (h5 : ConLeche.domsMatchAux
        (fun _ e => e.renameConsts (ConLeche.projFwd T ctorName nF))
        sbinders cbindersR 0 0 (nP + nF) = false) :
    (ConLeche.checkProjIotaF mode' ops lfe T ctorName lps cvj nP nF i).run lst
      = .error (.notImplemented "projection iota domain mismatch") := by
  rw [ConLeche.checkProjIotaF]
  simp only [h1, h2, h3, h4, h5, reduceIte, Bool.false_eq_true, if_false]
  rfl

/-- `ConLeche/Kernel/DeclCheck.lean:812-836` —
**`inductives::modeled::check_proj_iota_body` refines the cited tail.**

**One hypothesis the cited function does not need.**  The cited `mkSpine` is
`.const (ctorName.str "_model") …`; the port's `check_proj_iota_body` is
handed `cvj` and not `ctorName`, and spells it `model_of(&cvj.name)`.  The two
agree exactly when `cvj.name = ctorName`, which every call site guarantees
(`cvj` is what `checkProjLookupsF` read out of `fe.find? ctorName`) but which
is *not* a consequence of `ConstantValWF cvj` — so the statement below is
**false** without `hcn`, and takes it.  (The faithful repair is for
`modeled::check_proj_iota_body` to take `ctor_name`, which is task #57's.) -/
theorem check_proj_iota_body_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {t ctor_name : name.Name}
    {cvj tcv : env.ConstantVal} {lps : alloc.vec.Vec name.Name}
    {n_p n_f i : Std.U64} {sbody : expr.Expr}
    {out : core.result.Result Unit core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (ht : NameWF t)
    (hcvj : ConstantValWF cvj) (hlps : NamesWF lps) (htcv : ConstantValWF tcv)
    (hsb : ExprWF sbody) (hcn : absName cvj.name = absName ctor_name)
    (h : inductives.modeled.check_proj_iota_body mode st fe t cvj lps n_p n_f i
      tcv sbody = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok _ =>
        ∃ lst', (projIotaTail (absMode mode) (TypeChecker.lops mode lfe) lfe.env
              (absName t) (absName ctor_name) (absConstantVal cvj) (absNames lps)
              n_p.val n_f.val i.val (absExpr tcv.ty) (absExpr sbody)).run lst
            = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err e =>
        ErrSim e ((projIotaTail (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (absName t) (absName ctor_name) (absConstantVal cvj) (absNames lps)
            n_p.val n_f.val i.val (absExpr tcv.ty) (absExpr sbody)).run lst) := by
  intro lst lfe hsr hfr
  rw [inductives.modeled.check_proj_iota_body] at h
  obtain ⟨depth, hdepth, h⟩ := bind_eq_ok_iff.mp h
  have hdv : depth.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hdepth
  obtain ⟨p_args, hpa, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpaabs, hpawf⟩ := struct_ps_at_refines hpa
  rw [show n_f.val + n_p.val = n_p.val + n_f.val by omega] at hpaabs
  obtain ⟨x_args, hxa, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hxaabs, hxawf⟩ := field_spine_refines hxa
  obtain ⟨spine, hsp, h⟩ := bind_eq_ok_iff.mp h
  have hspe : spine = p_args := Env.exprs_copy_refines hsp
  rw [hspe] at h
  obtain ⟨spine1, hsp1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hsp1abs, hsp1wf⟩ := CoreK.append_exprs_refines hpawf hxawf hsp1
  obtain ⟨mn, hmn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hmnabs, hmnwf⟩ := model_of_refines hcvj.1 hmn
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hvabs, hvwf⟩ := params_of_refines hcvj.2.1 hv
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨mk_spine, hms, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hmsabs, hmswf⟩ :=
    ExprOps.mk_app_n_refines (Expr.mk_const_wf hmnwf hvwf he) hsp1wf hms
  rw [Expr.mk_const_refines he, hmnabs, hcn, hvabs, hsp1abs, hpaabs, hxaabs]
    at hmsabs
  obtain ⟨largs, hla, h⟩ := bind_eq_ok_iff.mp h
  have hlaval : largs.val = p_args.val ++ [mk_spine] := vec_push_val hla
  have hlaabs : absExprs largs
      = absExprs p_args ++ [absExpr mk_spine] := by
    rw [absExprs, absExprs, hlaval]; simp
  have hlawf : ExprsWF largs := by
    intro w hw
    rw [hlaval] at hw
    rcases List.mem_append.1 hw with h1 | h1
    · exact hpawf w h1
    · simp only [List.mem_singleton] at h1; rw [h1]; exact hmswf
  obtain ⟨pn, hpn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpnabs, hpnwf⟩ := proj_model_name_refines ht hpn
  obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hv1abs, hv1wf⟩ := params_of_refines hlps hv1
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨lhs_s, hls, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlsabs, hlswf⟩ :=
    ExprOps.mk_app_n_refines (Expr.mk_const_wf hpnwf hv1wf he1) hlawf hls
  rw [Expr.mk_const_refines he1, hpnabs, hv1abs, hlaabs, hpaabs, hmsabs] at hlsabs
  obtain ⟨head, hhd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hhdabs, hhdwf⟩ := ExprOps.get_app_fn_refines hsb hhd
  obtain ⟨args, harg, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hargabs, hargwf⟩ := ExprOps.get_app_args_refines hsb harg
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨head1, shaped⟩ := q
  by_cases hl3 : alloc.vec.Vec.len args = 3#usize
  case neg =>
    -- `modeled.rs:2129` ← `DeclCheck.lean:825`: a spine of other than three
    -- arguments is not the cited body pattern
    replace hq := ite_neg_eq (c := (alloc.vec.Vec.len args = 3#usize)) hl3 hq
    simp only [Result.ok.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    refine errSim_notImplemented hce rfl (projIotaTail_shape ?_)
    intro c lu t0 a0 b0 hcon
    have hlen : args.val.length = 3 := by
      have hl : (absExpr sbody).getAppArgs = [t0, a0, b0] := by
        rw [hcon]; exact getAppArgs_app3_const _ _ _ _ _
      have hL := congrArg List.length (hargabs.trans hl)
      simpa [absExprs] using hL
    exact hl3 (by have := alloc.vec.Vec.len_val args; scalar_tac)
  replace hq := ite_pos_eq (c := (alloc.vec.Vec.len args = 3#usize)) hl3 hq
  obtain ⟨en, hen, hq⟩ := bind_eq_ok_iff.mp hq
  obtain ⟨bsh, hbsh, hq⟩ := bind_eq_ok_iff.mp hq
  simp only [Result.ok.injEq, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  have hargslen : args.val.length = 3 := by
    have := alloc.vec.Vec.len_val args; scalar_tac
  obtain ⟨x0, x1, x2, hxs⟩ := len_eq_three hargslen
  have hargabs3 : (absExpr sbody).getAppArgs
      = [absExpr x0, absExpr x1, absExpr x2] := by
    rw [← hargabs, absExprs, hxs]; simp
  by_cases hshd : bsh = true
  case neg =>
    -- `modeled.rs:2129` ← `DeclCheck.lean:825`: a head that is not a
    -- one-level constant is not the cited body pattern either
    replace h := ite_neg_eq (c := (bsh = true)) hshd h
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    refine errSim_notImplemented hce rfl (projIotaTail_shape ?_)
    intro c lu t0 a0 b0 hcon
    obtain ⟨n, us, hkind, huslen⟩ :=
      const_kind_of_abs (e := head) (c := c) (lu := lu)
        (by rw [hhdabs, hcon]; exact getAppFn_app3_const _ _ _ _ _)
    have hene : en = head._0 := (Result.ok_injective hen).symm
    rw [hene, hkind] at hbsh
    have hbv : bsh = decide (alloc.vec.Vec.len us = 1#usize) := by
      simpa using hbsh.symm
    refine hshd ?_
    rw [hbv]
    have := alloc.vec.Vec.len_val us
    simp only [decide_eq_true_eq]
    scalar_tac
  replace h := ite_pos_eq (c := (bsh = true)) hshd h
  obtain ⟨beq, hbeq, h⟩ := bind_eq_ok_iff.mp h
  have hbeqabs := CheckerBase.is_eq_head_refines hhdwf hbeq
  split at h
  case isFalse =>
    -- `modeled.rs:2133` ← `DeclCheck.lean:818` (or `:825`, off shape: the two
    -- cited `throw`s the port's one arm covers are the same kind)
    rename_i hbeqf
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    by_cases hpat : ∃ (c : ConLeche.Name) (lu : ConLeche.Level)
        (t0 a0 b0 : ConLeche.Expr),
        absExpr sbody = .app (.app (.app (.const c [lu]) t0) a0) b0
    · obtain ⟨c, lu, t0, a0, b0, hpat⟩ := hpat
      refine errSim_notImplemented hce rfl (projIotaTail_head hpat ?_)
      intro hceq
      subst hceq
      refine hbeqf ?_
      rw [hbeqabs, hhdabs, hpat, getAppFn_app3_const]
      simp [ConLeche.isEqHead]
    · refine errSim_notImplemented hce rfl (projIotaTail_shape ?_)
      intro c lu t0 a0 b0 hcon
      exact hpat ⟨c, lu, t0, a0, b0, hcon⟩
  rename_i hbeqt
  rw [hbeqt, hhdabs] at hbeqabs
  obtain ⟨lu, hlu⟩ := isEqHead_inv hbeqabs.symm
  have hshape : absExpr sbody
      = .app (.app (.app (.const ConLeche.eqName [lu]) (absExpr x0))
          (absExpr x1)) (absExpr x2) :=
    app3_of_spine hlu hargabs3
  obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
  have he2v : e2 = x1 := by
    have hg := ExprOps.vec_index_getElem? he2
    rw [hxs] at hg; simpa using hg.symm
  have hx1wf : ExprWF e2 := hargwf e2 (by rw [he2v, hxs]; simp)
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
  have hb1abs := Expr.beq_refines hx1wf hlswf hb1
  rw [he2v] at hb1abs
  split at h
  case isFalse =>
    -- `modeled.rs:2141` ← `DeclCheck.lean:820`
    rename_i hb1f
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    refine errSim_notImplemented hce rfl
      (projIotaTail_redex (lu := lu) (tslot := absExpr x0) hshape ?_)
    rw [← CheckerBase.decide_eq_beq_expr,
      show (absConstantVal cvj).levelParams = absNames cvj.level_params from rfl,
      ← hlsabs, ← hb1abs]
    simpa using hb1f
  rename_i hb1t
  obtain ⟨e3, he3, h⟩ := bind_eq_ok_iff.mp h
  have he3v : e3 = x2 := by
    have hg := ExprOps.vec_index_getElem? he3
    rw [hxs] at hg; simpa using hg.symm
  have hx2wf : ExprWF e3 := hargwf e3 (by rw [he3v, hxs]; simp)
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  have hi2v : i2.val = 1 + i.val := HashMap.uscalar_add_eq hi2
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
  have hi3v : i3.val = n_f.val - 1 - i.val := by
    rw [ExprOps.sub_nat_val hi3, hi2v]; omega
  obtain ⟨e4, he4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
  have hb2abs := Expr.beq_refines hx2wf (Expr.bvar_wf he4) hb2
  rw [Expr.bvar_refines he4, hi3v, he3v] at hb2abs
  split at h
  case isFalse =>
    -- `modeled.rs:2137` ← `DeclCheck.lean:822`
    rename_i hb2f
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    refine errSim_notImplemented hce rfl
      (projIotaTail_field (lu := lu) (tslot := absExpr x0) hshape ?_ ?_)
    · rw [← CheckerBase.decide_eq_beq_expr,
        show (absConstantVal cvj).levelParams = absNames cvj.level_params from rfl,
        ← hlsabs, ← hb1abs]
      exact hb1t
    · rw [← CheckerBase.decide_eq_beq_expr, ← hb2abs]
      simpa using hb2f
  rename_i hb2t
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := CheckerBase.open_pis_at_fvars_f_refines htcv.2.2 ho
  rw [show ((0#u64 : Std.U64)).val = 0 from rfl, hdv,
    ConLeche.openPisAtFvarsF_eq] at hoabs
  cases o with
  | none =>
    -- `modeled.rs:2145` ← `DeclCheck.lean:824`
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    refine errSim_notImplemented hce rfl
      (projIotaTail_telescope (lu := lu) (tslot := absExpr x0) hshape ?_ ?_ ?_)
    · rw [← CheckerBase.decide_eq_beq_expr,
        show (absConstantVal cvj).levelParams = absNames cvj.level_params from rfl,
        ← hlsabs, ← hb1abs]
      exact hb1t
    · rw [← CheckerBase.decide_eq_beq_expr, ← hb2abs]
      exact hb2t
    · simpa using hoabs.symm
  | some oq =>
    obtain ⟨fvs, sbodyO⟩ := oq
    obtain ⟨hfvswf, hsbowf⟩ := howf (fvs, sbodyO) rfl
    obtain ⟨targs_o, hto, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨htoabs, htowf⟩ := ExprOps.get_app_args_refines hsbowf hto
    obtain ⟨alpha, hal, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨halabs, halwf⟩ := arg_get_d_refines htowf hal
    obtain ⟨lhs2, hl2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hl2abs, hl2wf⟩ := arg_get_d_refines htowf hl2
    obtain ⟨rhs2, hr2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hr2abs, hr2wf⟩ := arg_get_d_refines htowf hr2
    obtain ⟨la, hla2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hlaabs2, hlawf2⟩ := CheckerBase.eq_head_level_refines hhdwf hla2
    have hres := check_iota_sides_ty_refines hfuel hk hsw hfw halwf hl2wf hr2wf
      hlawf2 h lst lfe (ConLeche.projModelName (absName t) i.val) hsr hfr
    rw [hhdabs, hlu] at hlaabs2
    cases out with
    | Ok u =>
      obtain ⟨lst', hrun, hsr', hsw'⟩ := hres
      refine ⟨lst', ?_, hsr', hsw'⟩
      rw [hdv, halabs, hl2abs, hr2abs, htoabs] at hrun
      rw [hlaabs2] at hrun
      refine projIotaTail_run (lu := lu) (tslot := absExpr x0)
        (fvs := absExprs fvs) (sbodyO := absExpr sbodyO) hshape ?_ ?_ ?_ hrun
      · rw [← CheckerBase.decide_eq_beq_expr,
          show (absConstantVal cvj).levelParams = absNames cvj.level_params from rfl,
          ← hlsabs, ← hb1abs]
        exact hb1t
      · rw [← CheckerBase.decide_eq_beq_expr, ← hb2abs]
        exact hb2t
      · simpa using hoabs.symm
    | Err e =>
      refine ErrSim.trans hres (fun le hle => ?_)
      rw [hdv, halabs, hl2abs, hr2abs, htoabs, hlaabs2] at hle
      refine projIotaTail_sides_err (lu := lu) (tslot := absExpr x0)
        (fvs := absExprs fvs) (sbodyO := absExpr sbodyO) hshape ?_ ?_ ?_ hle
      · rw [← CheckerBase.decide_eq_beq_expr,
          show (absConstantVal cvj).levelParams = absNames cvj.level_params from rfl,
          ← hlsabs, ← hb1abs]
        exact hb1t
      · rw [← CheckerBase.decide_eq_beq_expr, ← hb2abs]
        exact hb2t
      · simpa using hoabs.symm

/-- `ConLeche/Kernel/DeclCheck.lean:797-836 checkProjIotaF` (and
`Inductives/Modeled.lean:513-563 checkProjIota`, the generic twin) —
**`inductives::modeled::check_proj_iota`**: the model's `proj_i.iota` theorem
pins the rule — the statement's telescope domains are the constructor's
renamed to the model side, its body equates the projected constructor spine
with field `i`, and the two side certificates are run.

**The two index views.**  The cited `F`-mirror passes one `fe`; the port
passes `fe2` and `fe_self` (`kernel::checker`'s module note 1: the
pre-insertion view is a *visibility bound*, not a value, and the port lowers
and restores it rather than holding two indices).  Under
`Refine/FEnv.lean`'s `restrict_to_refines` both views relate to the same
`lfe`, which is why the statement takes two relations — exactly the shape the
cited `checkProjIota mode ops env env …` has.

**One hypothesis the cited function does not need**, `hcn`: see
`check_proj_iota_body_refines` — the port's body spells the cited
`ctorName.str "_model"` as `model_of(&cvj.name)`, so the two agree exactly
when `cvj.name = ctorName`, which every call site guarantees and
`ConstantValWF cvj` does not.  Without it the statement is **false**.

Stated here (and proved on `modeled.rs`'s iota-family steps above) so that
task #57's `IndRoutesSpec` has the modeled clause at its `DeclCheck.lean`
citation. -/
theorem check_proj_iota_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {cvj : env.ConstantVal} {n_p n_f i : Std.U64}
    {out : core.result.Result Unit core_types.CheckError}
    (hsw : StateWF st) (hfw2 : FEnvWF fe2) (hfws : FEnvWF fe_self)
    (ht : NameWF t) (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (hcvj : ConstantValWF cvj) (hcn : absName cvj.name = absName ctor_name)
    (h : inductives.modeled.check_proj_iota mode st fe2 fe_self t ctor_name lps
      cvj n_p n_f i = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe → FEnvRel fe_self lfe →
      match out with
      | .Ok _ =>
        ∃ lst', (ConLeche.checkProjIotaF (absMode mode)
              (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe
              (absName t) (absName ctor_name) (absNames lps)
              (absConstantVal cvj) n_p.val n_f.val i.val).run lst
            = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err e =>
        ErrSim e ((ConLeche.checkProjIotaF (absMode mode)
            (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe
            (absName t) (absName ctor_name) (absNames lps)
            (absConstantVal cvj) n_p.val n_f.val i.val).run lst) := by
  intro lst lfe hsr hfr2 hfrs
  rw [inductives.modeled.check_proj_iota] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := proj_iota_name_refines ht hn
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := thm_probe_refines (FindAgree.of_rel hfr2 hfw2)
    (FindWF.of_wf hfw2) hnwf ho
  cases o with
  | none =>
    -- `modeled.rs:2044` ← `DeclCheck.lean:801`
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    exact errSim_notImplemented hce rfl
      (checkProjIotaF_thm_none (by rw [← hnabs]; simpa using hoabs.symm))
  | some tcv =>
    have htcv : ConstantValWF tcv := howf tcv rfl
    obtain ⟨tval, hfind⟩ := thmOf_eq_some hoabs.symm
    rw [hnabs] at hfind
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbabs := names_beq_refines htcv.2.1 hlps hb
    split at h
    case isFalse =>
      -- `modeled.rs:2048` ← `DeclCheck.lean:803`
      rename_i hbf
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      refine errSim_notImplemented hce rfl (checkProjIotaF_lps hfind ?_)
      show absNames tcv.level_params ≠ absNames lps
      simpa [hbabs] using hbf
    rename_i hbt
    subst hbt
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    have hi1v : i1.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hi1
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_pis_refines htcv.2.2 ho1
    have hlpseq : (absConstantVal tcv).levelParams = absNames lps := by
      show absNames tcv.level_params = absNames lps
      simpa using hbabs.symm
    cases o1 with
    | none =>
      -- `modeled.rs:2052` ← `DeclCheck.lean:805`
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      refine errSim_notImplemented hce rfl
        (checkProjIotaF_thm_tele hfind hlpseq ?_)
      rw [show (absConstantVal tcv).type = absExpr tcv.ty from rfl, ← hi1v]
      simpa using ho1abs.symm
    | some sq =>
      obtain ⟨sbinders, sbody⟩ := sq
      obtain ⟨hsbwf, hsbowf⟩ := ho1wf (sbinders, sbody) rfl
      obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ho2abs, ho2wf⟩ := ExprOps.strip_pis_refines hcvj.2.2 ho2
      have hsbeq : (absConstantVal tcv).type.stripPis (n_p.val + n_f.val)
          = some (ExprOps.absBinders sbinders, absExpr sbody) := by
        rw [show (absConstantVal tcv).type = absExpr tcv.ty from rfl, ← hi1v]
        simpa using ho1abs.symm
      cases o2 with
      | none =>
        -- `modeled.rs:2056` ← `DeclCheck.lean:807`
        obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        refine errSim_notImplemented hce rfl
          (checkProjIotaF_ctor_tele hfind hlpseq hsbeq ?_)
        rw [show (absConstantVal cvj).type = absExpr cvj.ty from rfl, ← hi1v]
        simpa using ho2abs.symm
      | some cq =>
        obtain ⟨cbinders, cbody⟩ := cq
        obtain ⟨hcbwf, -⟩ := ho2wf (cbinders, cbody) rfl
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1abs := doms_match_aux_view
          (g := fun _ e => ConLeche.Expr.renameConsts
            (ConLeche.projFwd (absName t) (absName ctor_name) n_f.val) e)
          hsbwf hcbwf (dom_proj_fwd_view_refines (n_f := n_f) ht hc) hb1
        have hcbeq : (absConstantVal cvj).type.stripPis (n_p.val + n_f.val)
            = some (ExprOps.absBinders cbinders, absExpr cbody) := by
          rw [show (absConstantVal cvj).type = absExpr cvj.ty from rfl, ← hi1v]
          simpa using ho2abs.symm
        by_cases hb1t : b1 = true
        case neg =>
          -- `modeled.rs:2061` ← `DeclCheck.lean:811`
          replace h := ite_neg_eq (c := (b1 = true)) hb1t h
          obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨vv, hvv, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          refine errSim_notImplemented hce rfl
            (checkProjIotaF_doms hfind hlpseq hsbeq hcbeq ?_)
          rw [← hi1v]
          exact hb1abs.symm.trans (by simpa using hb1t)
        replace h := ite_pos_eq (c := (b1 = true)) hb1t h
        have hdoms : ConLeche.domsMatchAux
            (fun _ e => ConLeche.Expr.renameConsts
              (ConLeche.projFwd (absName t) (absName ctor_name) n_f.val) e)
            (ExprOps.absBinders sbinders) (ExprOps.absBinders cbinders) 0 0
            (n_p.val + n_f.val) = true := by
          rw [← hi1v, ← hb1t]; exact hb1abs.symm
        have heq := checkProjIotaF_at_tail (mode' := absMode mode)
          (ops := ConLeche.Cached.sharedOpsC (absMode mode) lfe) (tval := tval)
          (sbinders := ExprOps.absBinders sbinders)
          (cbindersR := ExprOps.absBinders cbinders) (cbody := absExpr cbody)
          hfind hlpseq hsbeq hcbeq hdoms
        have hres := check_proj_iota_body_refines hfuel hk hsw hfws ht hcvj hlps
          htcv hsbowf hcn h lst lfe hsr hfrs
        cases out with
        | Ok u =>
          obtain ⟨lst', hrun, hsr', hsw'⟩ := hres
          exact ⟨lst', by rw [heq]; exact hrun, hsr', hsw'⟩
        | Err e => rw [heq]; exact hres

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing from Aeneas's library, nothing from the `Arc` models, no `sorry` of
this file's own: the three standard Lean axioms only.  One lemma is not
listed: `check_proj_lookups_refines`, whose pinned-`Eq` conjunct reaches
`Refine/Pins.lean`'s two open statements (`pins_decode_refines`,
`pins_text_decodes` — task #43's, deferred there with reasons) through
`basis_pins::eq_basis_pinned`, and so still shows `sorryAx` until those
land. -/

/-- info: 'ConRon.Refine.DeclCheck.consts_resolve_f_go_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms consts_resolve_f_go_refines

/-- info: 'ConRon.Refine.DeclCheck.constsResolveFSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms constsResolveFSpec

/-- info: 'ConRon.Refine.DeclCheck.check_member_val_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_member_val_refines

/-- info: 'ConRon.Refine.DeclCheck.check_proj_iota_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_proj_iota_refines

/-- info: 'ConRon.Refine.DeclCheck.check_proj_ty_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_proj_ty_refines

/-- info: 'ConRon.Refine.DeclCheck.check_proj_rule_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_proj_rule_refines

end ConRon.Refine.DeclCheck
