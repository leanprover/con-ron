import ConRon.Refine.TypeChecker
import ConRon.Refine.CoreKProj
import ConRon.Refine.CoreKSupport
import ConRon.Refine.CoreKNames
import ConRon.Refine.CoreKShapes
import ConRon.Refine.StateCResolve
import ConLeche.Kernel.DeclCheck

/-! # `kernel::decl_check` — the declaration checker through the index (task #56)

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

## Which Rust function carries which pair of citations

| con-leche `F`-mirror | its generic twin | the one Rust function |
|---|---|---|
| `Expr.constsResolveF` (`:37-58`) | `Expr.constsResolve` (`Core.lean:307-332`) | `core_k::consts_resolve` |
| `natOpCodF` (`:210`), `natOpTyPinnedF` (`:220`), `natOpStoredOkF` (`:234`) | `natOpCod`, `natOpTyPinned`, `natOpStoredOk` | `core_k::nat_op_cod`, `nat_op_ty_pinned`, `nat_op_stored_ok` |
| `stdAxiomOkF` (`:241`) | `stdAxiomOk` | `std_axioms::std_axiom_ok` |
| `trustCompilerOkF` (`:273`), `reduceStoredOkF` (`:283`), `reduceElemOkF` (`:289`), `ofReduceAxOkF` (`:297`), `reducePinGuardF` (`:305`) | their `TrustAxioms.lean` twins | `trust_axioms::*` |
| `FEnv.findCV?` (`:34`) | `Env.findCV?` | `checker_base::find_cv` |
| `checkConstantValF` (`:464`), `checkProjRuleF` (`:764`) | `checkConstantVal`, `checkProjRule` | `checker_base::check_constant_val`, `check_proj_rule` |
| the `divMod*F`/`checkDivMod*F` family (`:311`-`:339`, `:862`-`:914`), `checkReducePinF` (`:915`), `checkDefnValF` (`:839`), `installBasisDeclF` (`:856`) | their `Checker.lean` twins | `checker::*` |
| `domsMatchAuxA` (`CheckerBase.lean`) | `domsMatchAux` | `checker_base::doms_match_aux` |
| `checkEtaThmF` (`:345`), `checkUnitThmF` (`:385`), `indBlockCapsF` (`:431`), `checkMemberValF` (`:488`), `checkProjLookupsF` (`:730`), `checkProjTyF` (`:749`), `checkProjIotaF` (`:798`) | their `Kernel/Inductives/Modeled.lean` twins | `inductives::modeled::*` — **and** `kernel::decl_check::*` (see the duplication note) |

The lemmas for a twin that lives in another module are in that module's
`Refine/` file; what is stated *here* is (a) every public function of
`kernel/decl_check.rs`, and (b) the projection family and the member check —
the seam task #57's inductive routes consume (`Refine/IndSpec.lean` is the
other half of that seam).

## The duplication this file found (not recorded in DESIGN.md)

`kernel/decl_check.rs`'s **artifact and member family is dead code**.  Task
#25's `kernel/inductives/modeled.rs` re-ported `checkEtaThmF`, `checkUnitThmF`,
`indBlockCapsF`, `checkMemberValF`, `checkProjLookupsF` and the
`some (.thmInfo tcv _)` probe under the *same* `DeclCheck.lean` citations, and
it is `modeled`'s copies that the executed checker runs
(`inductives_c` calls `modeled::ind_block_caps`).  Nothing outside
`decl_check.rs` calls any of `check_eta_thm`, `check_unit_thm`,
`ind_block_caps`, `check_member_val`, `check_proj_lookups`, `thm_probe`,
`eq_spine3`, `eta_*`, `unit_*`, `model_app`, `desc_bvars*`, `lp_params*`,
`model_name`, `eta_thm_name`, `unit_thm_name` or `ModelRename`; the only live
items are `consts_resolve_f_go`/`consts_resolve_f_fast`, which nine call sites
use.  §3.1's one-to-one rule wants one Rust function per Lean declaration, so
one of the two copies should go (the `modeled` one is the executed one, and
the shapes there are factored differently — `check_eta_thm_shape` versus
`eta_telescope_ok`).  Nothing below hides it: the two copies get **separate**
lemmas, `<f>_refines` for this module's and `modeled_<f>_refines` for the
executed twin, and they are the same statement.

## What `decl_check.rs` does not port

`checkIotaThmF` (`:508`), `nestedRuleShapeF` (`:576`), `checkIotaThmNF`
(`:602`), `checkIotaRuleF` (`:688`), `checkIotaRulesF` (`:719`) and
`ctorResidualOkF` (`:419`) stand on `ConLeche/Kernel/Inductives/*` and are task
#57's (`inductives::modeled`).  `CRFMemoInv` (`:71`) and its two lemmas are
`Prop`s — Charon erases them; the port's restatement of the memo invariant is
`Refine/StateCResolve.lean`'s `StateC.MemoBOk`, which this file reuses.
`checkProjTyF` and `checkProjIotaF` *are* ported, in `inductives::modeled`
(the module doc of `decl_check.rs` predates task #25 and still says they are
not — a stale note).

## The knot, and the two hypotheses that travel

Everything with a `CState` runs the core, so it takes
`core_k.check_fuel = ok fuel` and `Core.Wrappers mode fuel`
(`Refine/TypeChecker.lean`'s rule); task #55 discharges them.  Nothing here
proves anything about `cached::core_c`.

`sorry` count in this file: 21.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.DeclCheck

open ConRon.Refine.CoreK

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

`sorry`: one induction on the `ExprWF` derivation, exactly
`Refine/StateCResolve.lean`'s `consts_resolve_fc_go_refines` but with the four
leaf arms *outside* the memo probe (the cited clauses answer them through the
spec walk) and with the cited walk's **non**-short-circuiting `&&`, which the
port spells `expr_ops::bool_and` on two already-computed operands. -/
theorem consts_resolve_f_go_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hp : PinnedBasisNames) (hfe : FindAgree fe lfe)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool)
      (lmemo : _root_.Std.HashMap ConLeche.Expr Bool) (b : Bool),
      StateC.MemoBOk memo lmemo →
      decl_check.consts_resolve_f_go fe memo e = ok (b, memo') →
      ∃ lmemo', ConLeche.Expr.constsResolveFGo lfe lmemo (absExpr e)
          = (b, lmemo') ∧ StateC.MemoBOk memo' lmemo' := by
  sorry

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
  have hb : b0 = b := congrArg Prod.fst (Result.ok_injective (α := Bool × _) h)
  subst hb
  obtain ⟨lmemo', hl, -⟩ :=
    consts_resolve_f_go_refines hp hfe he memo memo' ∅ b (StateC.memo_b_new hnew) hgo
  have hspec := (ConLeche.Expr.constsResolveFGo_spec (absExpr e) ∅
    ConLeche.CRFMemoInv.empty).1
  rw [hl] at hspec
  exact hspec

/-! ## 2. The model-companion names (`n.str "_model"` and its two suffixes)

`DeclCheck.lean` spells `n.str "_model"` a dozen times and never names it; the
port does (DESIGN.md §3.3 forbids a `&str` parameter, so the literal is a
`const [u32; N]`).  Each of the four is a `str_lit_step`. -/

/-- The Lean literal the port spells as six code points. -/
theorem model_suffix_refines {v : alloc.vec.Vec Std.U32}
    (h : decl_check.model_suffix = ok v) : absString v = "_model" := by
  rw [decl_check.model_suffix] at h
  obtain ⟨s, hs, hv⟩ := bind_eq_ok_iff.mp h
  simp only [lift_eq, Result.ok.injEq] at hs
  subst hs
  rw [absString_eq, code_points_val hv]
  rfl

/-- `ConLeche/Kernel/DeclCheck.lean:345-382` etc. — `decl_check::model_name`
is the cited `n.str "_model"`. -/
theorem model_name_refines {n r : name.Name} (hn : NameWF n)
    (h : decl_check.model_name n = ok r) :
    absName r = (absName n).str "_model" ∧ NameWF r := by
  rw [decl_check.model_name] at h
  simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨v, hv, hmk⟩ := h
  rw [decl_check.model_suffix] at hv
  obtain ⟨s, hs, hv⟩ := bind_eq_ok_iff.mp hv
  simp only [lift_eq, Result.ok.injEq] at hs
  subst hs
  have hvv : v.val = [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32] := by
    rw [code_points_val hv]; simp
  refine ⟨?_, NameWF.str hn ?_ hmk⟩
  · rw [Name.mk_str_refines hmk, absString_eq, hvv]; rfl
  · rw [hvv]; decide

/-- `ConLeche/Kernel/DeclCheck.lean:345-382 checkEtaThmF` —
`decl_check::eta_thm_name` is the cited `(T.str "_model").str "eta"`. -/
theorem eta_thm_name_refines {t r : name.Name} (ht : NameWF t)
    (h : decl_check.eta_thm_name t = ok r) :
    absName r = ((absName t).str "_model").str "eta" ∧ NameWF r := by
  rw [decl_check.eta_thm_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := model_name_refines ht hn
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [101#u32, 116#u32, 97#u32]) (by simp) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/DeclCheck.lean:384-414 checkUnitThmF` —
`decl_check::unit_thm_name` is the cited `(T.str "_model").str "unitlike"`. -/
theorem unit_thm_name_refines {t r : name.Name} (ht : NameWF t)
    (h : decl_check.unit_thm_name t = ok r) :
    absName r = ((absName t).str "_model").str "unitlike" ∧ NameWF r := by
  rw [decl_check.unit_thm_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := model_name_refines ht hn
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [117#u32, 110#u32, 105#u32, 116#u32, 108#u32, 105#u32, 107#u32, 101#u32])
    (by simp) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-! ## 3. `checkMemberValF`'s local `f : Name → Name`

Task #24's deviation 9: the cited
`fun n => if blockNames.contains n then n.str "_model" else n` is a
one-method dictionary struct (`decl_check::ModelRename` over
`expr_ops::NameToName`), because §3.4 forbids the closure. -/

/-- The cited closure of `ConLeche/Kernel/DeclCheck.lean:489-490`. -/
def modelRename (bns : List ConLeche.Name) (n : ConLeche.Name) : ConLeche.Name :=
  if bns.contains n then n.str "_model" else n

/-- `ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF` —
**`ModelRename`'s one method is the cited local `f`**, which is what
`ExprOpsMeta.rename_consts_refines` consumes at `checkMemberValF`'s one call
site. -/
theorem model_rename_refines {bns : alloc.vec.Vec name.Name} (hbns : NamesWF bns) :
    ∀ n, NameWF n → ∀ r,
      (decl_check.ModelRename.Insts.Con_ron_coreKernelExpr_opsNameToName).rename
          { block_names := bns } n = ok r →
        absName r = modelRename (absNames bns) (absName n) ∧ NameWF r := by
  intro n hn r h
  rw [decl_check.ModelRename.Insts.Con_ron_coreKernelExpr_opsNameToName,
    decl_check.ModelRename.Insts.Con_ron_coreKernelExpr_opsNameToName.rename] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := Name.contains_refines hbns hn hb
  rw [modelRename, ← hbv]
  cases b with
  | true => simp only [if_true] at h ⊢; exact model_name_refines hn h
  | false =>
    simp only [Bool.false_eq_true, if_false] at h ⊢
    rw [name_dup_eq] at h
    rw [← Result.ok_injective h]
    exact ⟨rfl, hn⟩

/-! ## 4. The little `List`-over-`Vec` builders the shape predicates need

`lps.map .param` and `(List.range nP).map fun k => Expr.bvar (off - k)` are
closures (§3.4), so the port has an index recursion for each.  Both are exact
on success: the port's `off - k` is a `u64` subtraction that *fails* on
underflow where Lean's `Nat` truncates, and a success means no underflow. -/

/-- `decl_check::lp_params_from` is the cited `lps.map .param` from `i`. -/
theorem lp_params_from_refines {lps : alloc.vec.Vec name.Name}
    (hlps : NamesWF lps) :
    ∀ (N : Nat) (i : Std.Usize) (out r : alloc.vec.Vec level.Level),
      lps.val.length - i.val ≤ N → LevelsWF out →
      decl_check.lp_params_from lps i out = ok r →
      absLevels r = absLevels out
          ++ ((absNames lps).drop i.val).map ConLeche.Level.param ∧ LevelsWF r := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:345-382` etc. — `decl_check::lp_params` is
the cited `lps.map .param`. -/
theorem lp_params_refines {lps : alloc.vec.Vec name.Name}
    {r : alloc.vec.Vec level.Level} (hlps : NamesWF lps)
    (h : decl_check.lp_params lps = ok r) :
    absLevels r = (absNames lps).map ConLeche.Level.param ∧ LevelsWF r := by
  sorry

/-- `decl_check::desc_bvars_from` is the cited descending spine from `k`. -/
theorem desc_bvars_from_refines :
    ∀ (N : Nat) (n off k : Std.U64) (out r : alloc.vec.Vec expr.Expr),
      n.val - k.val ≤ N → ExprsWF out →
      decl_check.desc_bvars_from n off k out = ok r →
      absExprs r = absExprs out
          ++ ((List.range n.val).drop k.val).map
              (fun j => ConLeche.Expr.bvar (off.val - j)) ∧ ExprsWF r := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:345-382` etc. — `decl_check::desc_bvars` is
the cited `(List.range nP).map fun k => Expr.bvar (off - k)`. -/
theorem desc_bvars_refines {n off : Std.U64} {r : alloc.vec.Vec expr.Expr}
    (h : decl_check.desc_bvars n off = ok r) :
    absExprs r = (List.range n.val).map (fun j => ConLeche.Expr.bvar (off.val - j))
      ∧ ExprsWF r := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:345-382` etc. — `decl_check::model_app` is
the cited `mkAppN (.const (T.str "_model") (lps.map .param))
((List.range nP).map fun k => Expr.bvar (off - k))`, written four times in the
two artifact predicates. -/
theorem model_app_refines {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p off : Std.U64} {r : expr.Expr} (ht : NameWF t) (hlps : NamesWF lps)
    (h : decl_check.model_app t lps n_p off = ok r) :
    absExpr r = ConLeche.Expr.mkAppN
        (.const ((absName t).str "_model") ((absNames lps).map ConLeche.Level.param))
        ((List.range n_p.val).map (fun j => ConLeche.Expr.bvar (off.val - j)))
      ∧ ExprWF r := by
  sorry

/-! ## 5. The structure artifacts' shape predicates (`DeclCheck.lean:344-441`)

`checkEtaThmF` and `checkUnitThmF` are one long `&&` cascade each under a
four-way (resp. three-way) simultaneous `match` on environment lookups.  The
port has them as a cascade of owning probes with the `&&` chain an `if` nest
(task #24, `check_eta_thm`'s own note), split at each `match` so that no
borrow crosses a branch: `check_eta_thm` → `eta_telescope_ok` → `eta_body_ok`,
and `check_unit_thm` → `unit_telescope_ok` → `unit_body_ok`.  Each split point
gets its own lemma against the cited *fragment*, named `*L` below. -/

/-- The `some (.thmInfo tcv _)` reading of a lookup, as a function (the `thmInfo`
twin of `Refine/CoreKGuards.lean`'s `defnOf`/`ctorOf`/`indOf`). -/
def thmOf : Option ConLeche.ConstantInfo → Option ConLeche.ConstantVal
  | some (.thmInfo cv _) => some cv
  | _ => none

/-- `ConLeche/Kernel/DeclCheck.lean:348-350` (and `:388-389`) —
**`decl_check::thm_probe`**: the `some (.thmInfo tcv _)` destructuring of the
indexed lookup that both artifact predicates open with, with an owned copy
(task #14's rule: the index's borrow dies at the call boundary). -/
theorem thm_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {o : Option env.ConstantVal} (hfe : FindAgree fe lfe) (hwf : FindWF fe)
    (hn : NameWF n) (h : decl_check.thm_probe fe n = ok o) :
    o.map absConstantVal = thmOf (lfe.find? (absName n)) ∧
      ∀ cv, o = some cv → ConstantValWF cv := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:355-358` — the cited per-field
model-companion level check of `checkEtaThmF`, from field `j`. -/
def projModelsLeveledL (lfe : ConLeche.FEnv) (T : ConLeche.Name)
    (lps : List ConLeche.Name) (nF j : Nat) : Bool :=
  ((List.range nF).drop j).all (fun k =>
    match lfe.find? (ConLeche.projModelName T k) with
    | some (.defnInfo cvmj _ _) => cvmj.levelParams == lps
    | _ => false)

/-- `ConLeche/Kernel/DeclCheck.lean:355-358 checkEtaThmF` —
**`decl_check::proj_models_leveled`** is the cited `(List.range nF).all …`,
started at `j`. -/
theorem proj_models_leveled_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {t : name.Name} {lps : alloc.vec.Vec name.Name} {n_f j : Std.U64} {b : Bool}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ht : NameWF t) (hlps : NamesWF lps)
    (h : decl_check.proj_models_leveled fe t lps n_f j = ok b) :
    b = projModelsLeveledL lfe (absName t) (absNames lps) n_f.val j.val := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:365-371` — the cited
`(List.range nF).map fun j => mkAppN (.const (projModelName T j) …)
(params ++ [bvar 0])`, from field `j`. -/
def etaProjAppsL (T : ConLeche.Name) (lps : List ConLeche.Name) (nP nF j : Nat) :
    List ConLeche.Expr :=
  ((List.range nF).drop j).map (fun k => ConLeche.Expr.mkAppN
    (.const (ConLeche.projModelName T k) (lps.map ConLeche.Level.param))
    (((List.range nP).map fun i => ConLeche.Expr.bvar (nP - i))
      ++ [ConLeche.Expr.bvar 0]))

/-- `ConLeche/Kernel/DeclCheck.lean:365-371 checkEtaThmF` —
**`decl_check::eta_proj_apps`** is that list, accumulated. -/
theorem eta_proj_apps_refines {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f j : Std.U64} {out r : alloc.vec.Vec expr.Expr}
    (ht : NameWF t) (hlps : NamesWF lps) (hout : ExprsWF out)
    (h : decl_check.eta_proj_apps t lps n_p n_f j out = ok r) :
    absExprs r = absExprs out
        ++ etaProjAppsL (absName t) (absNames lps) n_p.val n_f.val j.val
      ∧ ExprsWF r := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:362-371 checkEtaThmF` —
**`decl_check::eta_rhs`** is the cited η right-hand side: the constructor's
model companion at the parameters and at every field's projection companion. -/
theorem eta_rhs_refines {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f : Std.U64} {r : expr.Expr}
    (ht : NameWF t) (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : decl_check.eta_rhs t ctor_name lps n_p n_f = ok r) :
    absExpr r = ConLeche.Expr.mkAppN
        (.const ((absName ctor_name).str "_model")
          ((absNames lps).map ConLeche.Level.param))
        (((List.range n_p.val).map fun i => ConLeche.Expr.bvar (n_p.val - i))
          ++ etaProjAppsL (absName t) (absNames lps) n_p.val n_f.val 0)
      ∧ ExprWF r := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:360` (and `:399`) — the cited
`.app (.app (.app (.const c [ℓA]) tySlot) lhsC) rhsC` pattern **with**
`c == eqName`, which both artifact predicates open their body test with. -/
def eqSpine3L : ConLeche.Expr →
    Option (ConLeche.Level × ConLeche.Expr × ConLeche.Expr × ConLeche.Expr)
  | .app (.app (.app (.const c [lA]) tySlot) lhsC) rhsC =>
    if c = ConLeche.eqName then some (lA, tySlot, lhsC, rhsC) else none
  | _ => none

/-- `ConLeche/Kernel/DeclCheck.lean:360, :399` — **`decl_check::eq_spine3`** is
that reading, with owned copies of the three arguments. -/
theorem eq_spine3_refines {e : expr.Expr}
    {o : Option (level.Level × expr.Expr × expr.Expr × expr.Expr)}
    (he : ExprWF e) (h : decl_check.eq_spine3 e = ok o) :
    o.map (fun q => (absLevel q.1, absExpr q.2.1, absExpr q.2.2.1, absExpr q.2.2.2))
        = eqSpine3L (absExpr e) ∧
      ∀ q, o = some q →
        LevelWF q.1 ∧ ExprWF q.2.1 ∧ ExprWF q.2.2.1 ∧ ExprWF q.2.2.2 := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:359-378` — the cited body test of
`checkEtaThmF`, given the statement's body and the model's telescope body. -/
def etaBodyOkL (mode : ConLeche.CheckMode) (T ctorName : ConLeche.Name)
    (lps : List ConLeche.Name) (nP nF : Nat) (sbody tbodyM : ConLeche.Expr) : Bool :=
  match eqSpine3L sbody with
  | none => false
  | some (lA, tySlot, lhsC, rhsC) =>
    lhsC == ConLeche.Expr.bvar 0 &&
    tySlot == ConLeche.Expr.mkAppN
      (.const (T.str "_model") (lps.map ConLeche.Level.param))
      ((List.range nP).map fun k => ConLeche.Expr.bvar (nP - k)) &&
    rhsC == ConLeche.Expr.mkAppN
      (.const (ctorName.str "_model") (lps.map ConLeche.Level.param))
      (((List.range nP).map fun k => ConLeche.Expr.bvar (nP - k))
        ++ etaProjAppsL T lps nP nF 0) &&
    (!mode.ttChecks || tbodyM == ConLeche.Expr.sort lA)

/-- `ConLeche/Kernel/DeclCheck.lean:359-378 checkEtaThmF` —
**`decl_check::eta_body_ok`** is that test (the `c == eqName` conjunct lives in
`eq_spine3`, which is where the port put it). -/
theorem eta_body_ok_refines {mode : env.CheckMode} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f : Std.U64} {sbody tbody_m : expr.Expr}
    {b : Bool} (ht : NameWF t) (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (hs : ExprWF sbody) (htb : ExprWF tbody_m)
    (h : decl_check.eta_body_ok mode t ctor_name lps n_p n_f sbody tbody_m = ok b) :
    b = etaBodyOkL (absMode mode) (absName t) (absName ctor_name) (absNames lps)
      n_p.val n_f.val (absExpr sbody) (absExpr tbody_m) := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:352-378` — the cited
`match tcv.type.stripPis (nP + 1), cvmT.type.stripPis nP with` stage of
`checkEtaThmF`: the parameter domains, the structure binder, and the body. -/
def etaTelescopeOkL (mode : ConLeche.CheckMode) (T ctorName : ConLeche.Name)
    (lps : List ConLeche.Name) (nP nF : Nat)
    (tcv cvmT : ConLeche.ConstantVal) : Bool :=
  match tcv.type.stripPis (nP + 1), cvmT.type.stripPis nP with
  | some (sbinders, sbody), some (tbindersM, tbodyM) =>
    ConLeche.domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
    (match sbinders[nP]? with
     | some (xdom, _) =>
       xdom == ConLeche.Expr.mkAppN
         (.const (T.str "_model") (lps.map ConLeche.Level.param))
         ((List.range nP).map fun k => ConLeche.Expr.bvar (nP - 1 - k))
     | none => false) &&
    etaBodyOkL mode T ctorName lps nP nF sbody tbodyM
  | _, _ => false

/-- `ConLeche/Kernel/DeclCheck.lean:352-378 checkEtaThmF` —
**`decl_check::eta_telescope_ok`** is that stage.  `sorry`: the cited
`domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP` is
`checker_base::doms_match_aux` at the `DomIdent` view, whose refinement is
`Refine/CheckerBase.lean`'s — a sibling task-#56 file this one may not import,
so the proof waits for the merge. -/
theorem eta_telescope_ok_refines {mode : env.CheckMode} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f : Std.U64}
    {tcv cvm_t : env.ConstantVal} {b : Bool}
    (ht : NameWF t) (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (htcv : ConstantValWF tcv) (hcvm : ConstantValWF cvm_t)
    (h : decl_check.eta_telescope_ok mode t ctor_name lps n_p n_f tcv cvm_t = ok b) :
    b = etaTelescopeOkL (absMode mode) (absName t) (absName ctor_name)
      (absNames lps) n_p.val n_f.val (absConstantVal tcv) (absConstantVal cvm_t) := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF` —
**`decl_check::check_eta_thm` refines `checkEtaThmF`**: the stored
`T._model.eta` theorem, the two model companions, the pinned `Eq` basis, the
level agreements, the per-field companions, and the statement's telescope.

`sorry`: the cited `eqStored == eqA` conjunct is `basis_pins::eq_basis_pinned`,
refined in `Refine/BasisPins.lean` (a sibling task-#56 file). -/
theorem check_eta_thm_refines {mode : env.CheckMode} {fe : fenv.FEnv}
    {lfe : ConLeche.FEnv} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f : Std.U64} {b : Bool}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : decl_check.check_eta_thm mode fe t ctor_name lps n_p n_f = ok b) :
    b = ConLeche.checkEtaThmF (absMode mode) lfe (absName t) (absName ctor_name)
      (absNames lps) n_p.val n_f.val := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:398-411` — the cited body test of
`checkUnitThmF`. -/
def unitBodyOkL (mode : ConLeche.CheckMode) (T : ConLeche.Name)
    (lps : List ConLeche.Name) (nP : Nat) (sbody tbodyM : ConLeche.Expr) : Bool :=
  match eqSpine3L sbody with
  | none => false
  | some (lA, tySlot, lhsC, rhsC) =>
    lhsC == ConLeche.Expr.bvar 1 && rhsC == ConLeche.Expr.bvar 0 &&
    tySlot == ConLeche.Expr.mkAppN
      (.const (T.str "_model") (lps.map ConLeche.Level.param))
      ((List.range nP).map fun k => ConLeche.Expr.bvar (nP + 1 - k)) &&
    (!mode.ttChecks || tbodyM == ConLeche.Expr.sort lA)

/-- `ConLeche/Kernel/DeclCheck.lean:398-411 checkUnitThmF` —
**`decl_check::unit_body_ok`** is that test. -/
theorem unit_body_ok_refines {mode : env.CheckMode} {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p : Std.U64} {sbody tbody_m : expr.Expr}
    {b : Bool} (ht : NameWF t) (hlps : NamesWF lps)
    (hs : ExprWF sbody) (htb : ExprWF tbody_m)
    (h : decl_check.unit_body_ok mode t lps n_p sbody tbody_m = ok b) :
    b = unitBodyOkL (absMode mode) (absName t) (absNames lps) n_p.val
      (absExpr sbody) (absExpr tbody_m) := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:392-411` — the cited
`match tcv.type.stripPis (nP + 2), cvmT.type.stripPis nP with` stage of
`checkUnitThmF`: the parameter domains, the **two** structure binders, and the
body. -/
def unitTelescopeOkL (mode : ConLeche.CheckMode) (T : ConLeche.Name)
    (lps : List ConLeche.Name) (nP : Nat) (tcv cvmT : ConLeche.ConstantVal) : Bool :=
  match tcv.type.stripPis (nP + 2), cvmT.type.stripPis nP with
  | some (sbinders, sbody), some (tbindersM, tbodyM) =>
    ConLeche.domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
    (match sbinders[nP]? with
     | some (xdom, _) =>
       xdom == ConLeche.Expr.mkAppN
         (.const (T.str "_model") (lps.map ConLeche.Level.param))
         ((List.range nP).map fun k => ConLeche.Expr.bvar (nP - 1 - k))
     | none => false) &&
    (match sbinders[nP + 1]? with
     | some (ydom, _) =>
       ydom == ConLeche.Expr.mkAppN
         (.const (T.str "_model") (lps.map ConLeche.Level.param))
         ((List.range nP).map fun k => ConLeche.Expr.bvar (nP - k))
     | none => false) &&
    unitBodyOkL mode T lps nP sbody tbodyM
  | _, _ => false

/-- `ConLeche/Kernel/DeclCheck.lean:392-411 checkUnitThmF` —
**`decl_check::unit_telescope_ok`** is that stage.  `sorry`: as
`eta_telescope_ok_refines`, the `domsMatchAux` conjunct waits for
`Refine/CheckerBase.lean`. -/
theorem unit_telescope_ok_refines {mode : env.CheckMode} {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p : Std.U64}
    {tcv cvm_t : env.ConstantVal} {b : Bool}
    (ht : NameWF t) (hlps : NamesWF lps)
    (htcv : ConstantValWF tcv) (hcvm : ConstantValWF cvm_t)
    (h : decl_check.unit_telescope_ok mode t lps n_p tcv cvm_t = ok b) :
    b = unitTelescopeOkL (absMode mode) (absName t) (absNames lps) n_p.val
      (absConstantVal tcv) (absConstantVal cvm_t) := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:384-414 checkUnitThmF` —
**`decl_check::check_unit_thm` refines `checkUnitThmF`**.  `sorry`: the pinned
`Eq` basis conjunct is `Refine/BasisPins.lean`'s. -/
theorem check_unit_thm_refines {mode : env.CheckMode} {fe : fenv.FEnv}
    {lfe : ConLeche.FEnv} {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p : Std.U64} {b : Bool}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ht : NameWF t) (hlps : NamesWF lps)
    (h : decl_check.check_unit_thm mode fe t lps n_p = ok b) :
    b = ConLeche.checkUnitThmF (absMode mode) lfe (absName t) (absNames lps)
      n_p.val := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:430-441 indBlockCapsF` (with `:443-446
indBlockCapsF_sortZ`, the field equation the record satisfies by
construction) — **`decl_check::ind_block_caps` refines `indBlockCapsF`**: the
capability record recorded at a modeled structure-like block's install.

`sorry`: composes `check_eta_thm_refines`, `check_unit_thm_refines`,
`Refine/CoreKGuards.lean`'s `pi_result_is_prop_refines`/`pi_result_z_refines`
and `Refine/Env.lean`'s `names_beq_refines`. -/
theorem ind_block_caps_refines {mode : env.CheckMode} {fe : fenv.FEnv}
    {lfe : ConLeche.FEnv} {cv_t cv_c : env.ConstantVal} {n_p n_f : Std.U64}
    {c : env.IndCaps} (hfe : FindAgree fe lfe) (hwf : FindWF fe)
    (hcvt : ConstantValWF cv_t) (hcvc : ConstantValWF cv_c)
    (h : decl_check.ind_block_caps mode fe cv_t cv_c n_p n_f = ok c) :
    absIndCaps c = ConLeche.indBlockCapsF (absMode mode) lfe
        (absConstantVal cv_t) (absConstantVal cv_c) n_p.val n_f.val
      ∧ IndCapsWF c := by
  sorry

/-! ## 6. The member check and the projection lookups — the task-#57 seam

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
against them; three are Rust functions of another module (`checker_base`,
`inductives::modeled`), and they are stated here at their **`DeclCheck.lean`
citation**, which is the pair this file is responsible for recording.  Each is
DESIGN.md §3.5's shape: exact result on success, nothing on failure. -/

/-- `ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF` —
**`decl_check::check_member_val`**: the common `checkConstantVal`, no
model-shaped name of its own, and the model companion the in-process modeller
generated — same level parameters, and a type that is this member's with the
block's names renamed to their companions'.

`sorry`: `checker_base::check_constant_val`'s refinement is
`Refine/CheckerBase.lean`'s (a sibling task-#56 file); the rest is
`model_name_refines`, `model_rename_refines`,
`ExprOpsMeta.rename_consts_refines` and `Expr.beq_refines`. -/
theorem check_member_val_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe : fenv.FEnv} {cv cv' : env.ConstantVal}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hbn : NamesWF block_names)
    (hcv : ConstantValWF cv)
    (h : decl_check.check_member_val mode st block_names fe cv = ok (.Ok cv', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkMemberValF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
            (absNames block_names) lfe (absConstantVal cv)).run lst
          = .ok (absConstantVal cv', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv' := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF` — **the executed
twin**, `inductives::modeled::check_member_val` (the duplication note): the
same statement about the function task #57's modeled route actually calls.

`sorry`: as `check_member_val_refines`. -/
theorem modeled_check_member_val_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe : fenv.FEnv} {cv cv' : env.ConstantVal}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hbn : NamesWF block_names)
    (hcv : ConstantValWF cv)
    (h : inductives.modeled.check_member_val mode st block_names fe cv
      = ok (.Ok cv', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkMemberValF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
            (absNames block_names) lfe (absConstantVal cv)).run lst
          = .ok (absConstantVal cv', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv' := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:729-746 checkProjLookupsF` —
**`decl_check::check_proj_lookups`**: the projection install's five
environment lookups — the stored constructor at the expected arity, the
field's projection model companion at the block's level parameters, a free
projection-function name, the stored parent, and the pinned `Eq` basis.  No
state: the cited Lean is `ops`-free, so the run leaves `lst` alone.

`sorry`: the pinned `Eq` conjunct is `Refine/BasisPins.lean`'s; the rest is
`ctor_probe_refines`, `defn_probe_refines`, `proj_model_name_refines`,
`Env.proj_fn_name_refines` and `find_refines`. -/
theorem check_proj_lookups_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f i : Std.U64} {cvj mcv : env.ConstantVal}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : decl_check.check_proj_lookups fe t ctor_name lps n_p n_f i
      = ok (.Ok (cvj, mcv))) :
    ∀ lst : ConLeche.Cached.CState,
      (ConLeche.checkProjLookupsF (m := ConLeche.Cached.CheckCM) lfe
          (absName t) (absName ctor_name) (absNames lps)
          n_p.val n_f.val i.val).run lst
        = .ok ((absConstantVal cvj, absConstantVal mcv), lst)
      ∧ ConstantValWF cvj ∧ ConstantValWF mcv := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:729-746 checkProjLookupsF` — **the executed
twin**, `inductives::modeled::check_proj_lookups` (the duplication note).

`sorry`: as `check_proj_lookups_refines`. -/
theorem modeled_check_proj_lookups_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f i : Std.U64} {cvj mcv : env.ConstantVal}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : inductives.modeled.check_proj_lookups fe t ctor_name lps n_p n_f i
      = ok (.Ok (cvj, mcv))) :
    ∀ lst : ConLeche.Cached.CState,
      (ConLeche.checkProjLookupsF (m := ConLeche.Cached.CheckCM) lfe
          (absName t) (absName ctor_name) (absNames lps)
          n_p.val n_f.val i.val).run lst
        = .ok ((absConstantVal cvj, absConstantVal mcv), lst)
      ∧ ConstantValWF cvj ∧ ConstantValWF mcv := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:748-761 checkProjTyF` (and
`Inductives/Modeled.lean:497-511 checkProjTy`, the generic twin) —
**`inductives::modeled::check_proj_ty`**: the public projection type is the
model's renamed back, pinned by the renaming roundtrip, resolving, scoped, and
parameter-led.

`sorry`: needs `ProjBack`/`ProjFwd`'s dictionary lemmas (task #57's), then
`consts_resolve_f_fast_refines`, `Refine/ExprOpsFields.lean`'s
`loose_bvars_bounded`/`has_fvar`, `Refine/ExprOpsMeta.lean`'s
`all_level_params_defined_fast` and `ExprOpsSpine.strip_pis_refines`. -/
theorem check_proj_ty_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name} {mty : expr.Expr}
    {n_p n_f : Std.U64} {pty : expr.Expr}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps) (hmty : ExprWF mty)
    (h : inductives.modeled.check_proj_ty fe t ctor_name lps mty n_p n_f
      = ok (.Ok pty)) :
    ∀ lst : ConLeche.Cached.CState,
      (ConLeche.checkProjTyF (m := ConLeche.Cached.CheckCM) lfe
          (absName t) (absName ctor_name) (absNames lps) (absExpr mty)
          n_p.val n_f.val).run lst
        = .ok (absExpr pty, lst)
      ∧ ExprWF pty := by
  sorry

/-- `ConLeche/Kernel/CheckerBase.lean:235-250 checkProjShape` —
**`checker_base::check_proj_shape`**: the projection type's parameter prefix
and the constructor's `nP + nF` telescope, plus the residual pin.  Operation-
and state-free, so the run leaves `lst` alone.

`sorry`: `Refine/CheckerBase.lean` (a sibling task-#56 file) owns the proof; it
is restated here because the projection route (`Cached/CheckerC.lean:160`)
calls it between `checkProjTyF` and `checkProjRuleF`, and task #57 consumes
the whole chain. -/
theorem check_proj_shape_refines {pty ctor_ty : expr.Expr} {n_p n_f : Std.U64}
    (hp : ExprWF pty) (hct : ExprWF ctor_ty)
    (h : checker_base.check_proj_shape pty ctor_ty n_p n_f = ok (.Ok ())) :
    ∀ lst : ConLeche.Cached.CState,
      (ConLeche.checkProjShape (m := ConLeche.Cached.CheckCM)
        (absExpr pty) (absExpr ctor_ty) n_p.val n_f.val).run lst
      = .ok ((), lst) := by
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF` (and
`CheckerBase.lean:252-290 checkProjRule`, the generic twin) —
**`checker_base::check_proj_rule`**: the projection function's right-hand side
built from the constructor's telescope, annotated, scope- and level-checked,
its domains compared with the constructor's, and its type inferred.

`sorry`: `Refine/CheckerBase.lean` owns the proof; restated here at the `F`
citation for the task-#57 chain. -/
theorem check_proj_rule_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {pty : expr.Expr}
    {cvj : env.ConstantVal} {lps : alloc.vec.Vec name.Name}
    {n_p n_f i : Std.U64} {rhs_a : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hpty : ExprWF pty)
    (hcvj : ConstantValWF cvj) (hlps : NamesWF lps)
    (h : checker_base.check_proj_rule mode st fe pty cvj lps n_p n_f i
      = ok (.Ok rhs_a, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkProjRuleF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe (absExpr pty)
            (absConstantVal cvj) (absNames lps) n_p.val n_f.val i.val).run lst
          = .ok (absExpr rhs_a, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF rhs_a := by
  sorry

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

`sorry`: task #57's; stated here so `IndRoutesSpec`'s modeled clause has it. -/
theorem check_proj_iota_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {cvj : env.ConstantVal} {n_p n_f i : Std.U64}
    (hsw : StateWF st) (hfw2 : FEnvWF fe2) (hfws : FEnvWF fe_self)
    (ht : NameWF t) (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (hcvj : ConstantValWF cvj)
    (h : inductives.modeled.check_proj_iota mode st fe2 fe_self t ctor_name lps
      cvj n_p n_f i = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe → FEnvRel fe_self lfe →
      ∃ lst', (ConLeche.checkProjIotaF (absMode mode)
            (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe
            (absName t) (absName ctor_name) (absNames lps)
            (absConstantVal cvj) n_p.val n_f.val i.val).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  sorry

end ConRon.Refine.DeclCheck
