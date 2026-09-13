/-
# `kernel::inductives::modeled` refined — the modeled install route (task #57)

`CORE_PLAN.md` step 7.  `crates/con-ron-core/src/kernel/inductives/modeled.rs`
(2952 lines, 66 items) against `ConLeche/Kernel/Inductives/Modeled.lean` and,
per task #25's deviation 1, the `*F` twin of `ConLeche/Kernel/DeclCheck.lean`
that the executable actually runs: the port has **one** function per
`Env`/index pair carrying both citations, so every statement below is against
the index spelling (`checkMemberValF`, `checkIotaThmF`, `checkIotaThmNF`,
`checkIotaRuleF`, `checkIotaRulesF`, `checkProjLookupsF`, `checkProjTyF`,
`checkProjIotaF`, `checkEtaThmF`, `checkUnitThmF`, `ctorResidualOkF`,
`indBlockCapsF`, `nestedRuleShapeF`), which is the one the cached drivers of
`Cached/CheckerC.lean` call.

| group | items |
|---|---|
| the name maps | `model_str`, `model_of`, `BlockRename::rename`, `find_proj_model_slot`, `ProjBack::rename`, `find_proj_fn_slot`, `ProjFwd::rename`, `DomProjFwd::view`, `DomIdent::view` |
| the small readers | `iota_thm_name`, `proj_iota_name`, `eta_thm_name`, `unit_thm_name`, `thm_probe`, `arg_get_d`, `arg_get_last_d` |
| the side certificates | `check_iota_sides_ty` |
| the canonical iota statement | `iota_stmt_open`, `iota_lhs_prefix_ok`, `check_iota_thm`, `check_iota_thm_ctor`, `check_iota_thm_frames` |
| the nested shape | `lower_all`, `lift_all_0`, `pins_wf_from`, `nested_rule_shape` |
| the nested iota statement | `inst_pins_renamed`, `inst_pins_plain`, `check_iota_thm_n`, `check_iota_thm_n_ctor`, `check_iota_thm_n_frames` |
| the rules | `check_iota_rule`, `check_iota_rule_fire`, `iota_rule_stored`, `check_iota_rules` |
| the members | `check_member_val`, `check_ind_member`, `provision_recs_step`, `provision_recs`, `check_ind_recs_fold`, `check_ind_recs` |
| the projection functions | `check_proj_lookups`, `check_proj_ty`, `check_proj_iota`, `check_proj_iota_body`, `check_proj_fn`, `install_proj_fn_step` |
| the capability artifacts | `proj_models_at_lps_from`, `eta_rhs`, `eta_projs_from`, `check_eta_thm_shape`, `check_eta_thm`, `check_unit_thm_shape`, `check_unit_thm`, `ind_block_caps`, `ctor_residual_ok`, `ctor_targets_fam` |
| the block split | `filter_recs(_from)`, `block_names_of(_from)`, `single_ind_ctor(_from)` |

## The four `Name → Name` dictionaries

§3.4 forbids closures, so con-leche's four `Name → Name` arguments are
`expr_ops::NameToName` dictionaries (task #9/#13's pattern 1) and
`domsMatchAux`'s `g : Nat → Expr → Expr` is a `checker_base::DomView` one.
Each gets a `rename`/`view` lemma in exactly the shape
`ExprOps.rename_consts_refines` consumes — "the dictionary computes the
closure, and its answer is well formed" — and the consumers use *that lemma*,
never the dictionary's body:

| dictionary | the closure it stands for |
|---|---|
| `BlockRename { block_names }` | `blockRename`, i.e. `fun n => if blockNames.contains n then n.str "_model" else n` (`checkMemberVal`, `checkIndRecs`) |
| `ProjBack { t, ctor, n_f }` | `ConLeche.projBack T ctor nF` |
| `ProjFwd { t, ctor, n_f }` | `ConLeche.projFwd T ctor nF` |
| `DomProjFwd { t, ctor, n_f }` | `fun _ e => e.renameConsts (projFwd T ctor nF)` |
| `checker_base::DomIdent` | `fun _ e => e` |

`blockRename` is the only one of the five that con-leche does not name; it is
written out twice there (`Modeled.lean:379-380`, `:439-440`) and once in
`DeclCheck.lean:489-490`, identically, so it is transcribed once below.

## The three stages the cached driver splits

`provision_recs` is `provision_recs_step` plus a fold, and `check_ind_recs` is
`check_ind_recs_fold` plus its head, so that `inductives_c`'s `flushC` lands
exactly where `provisionRecsS`/`checkIndRecsS` put it with **one** body serving
both spellings (`Refine/IndC.lean` composes the halves).  The Lean side of a
half is a transcription in the `Stages` section below, each doc-commented with
the cited lines it covers; nothing is weakened by the split — the composition
of the two halves is the cited body, which is what `IndC.lean` proves.

Likewise `check_ind_member`, `install_proj_fn_step` and `check_proj_fn` are
the cited `*S` stages **minus the leading `flushC`**; `check_proj_fn` has no
flush of its own and is therefore stated against `checkProjFnS` unmodified.

## `fenv::dup` at the recursor group

`checkIndRecs` holds three views of the index at once — the block-member index
`env₂` (where every iota check's `env'` lookups go), the fully provisioned
`envSelf` that `provisionRecs` built on top of it, and the fold's accumulator,
which starts as `env₂`.  con-leche's index is persistent; the port threads
linearly (task #14) and takes two `fenv::dup`s.  `Refine/FEnv.lean`'s
`dup_refines` is what says a dup is the same index again.

## Deviations found while writing this file

1. `nested_rule_shape`'s artifact probe is `fenv::find(fe₂, iotaThmName).is_some()`
   where con-leche writes `(fe'.findCV? …).isSome`.  `FEnv.findCV?` is
   `(fe.find? n).map (·.toConstantVal)` (`DeclCheck.lean:33-35`), so the two
   `isSome`s are the same `Bool` — recorded, not repaired.
2. `check_member_val`'s type-mismatch message drops con-leche's `reprStr` dump
   of both sides (§3.1 drops interpolation); only the message differs.
3. `check_proj_iota_body` decides con-leche's
   `.app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC` pattern by the
   *spine* (`getAppArgs.length = 3` and a one-level `.const` head) instead of
   by four nested `.app` matches.  The two agree on every `Expr`, because
   `getAppFn`/`getAppArgs` decompose exactly that spine.
4. `ind_block_caps` short-circuits: con-leche's `(cvC.levelParams = cvT.levelParams) && checkEtaThmF …`
   is an `if`, and `nF == 0 && piResultIsProp cvT.type` likewise.  `&&` is
   already short-circuiting in Lean, so the two are the same `Bool`.
5. `iota_stmt_open` opens the statement's telescope with the one-pass
   `checker_base::open_pis_at_fvars_f`, where `checkIotaThmF`/`checkIotaThmNF`
   write `openPisAtFvars`; con-leche's own `openPisAtFvarsF_eq` says the two
   are the same function (`checkProjRuleF` already uses the `F` spelling).

## Ingredients this file does not own

`kernel/checker_base.rs` (task #24's tier, unified into the routes at task
#25's `checker_local`) has no refinement file yet, and the modeled route calls
eleven of its items; `struct_parts`' `struct_fam` and the three spine builders
are the sibling `Refine/IndStructParts.lean`'s, and
`decl_check::consts_resolve_f_fast` is the checker tier's (named in
`Refine/IndStructInstall.lean`).  Each travels as a named `Prop` in the exact
result shape — `CheckerBaseSpec`, `StructFamRefines`, `StructSpinesRefine`,
`StructInstall.ConstsResolveFFastRefines` — so that the statements below keep
their exact conclusions under an explicit hypothesis and nothing is weakened;
the same device `Refine/StateC.lean` uses for `InstantiateListRefines`.

## `sorry` count

43 `sorry`s out of 65 lemmas — one per item that reaches the knot, the shared
checker base, or a `partial_fixpoint` index recursion this file has no
foundation for yet.  Every item's statement is the exact-result one of
DESIGN.md §3.5 and **none is weakened**; each `sorry` carries a one-line note
naming the pieces its proof composes.

Proved outright (22): the whole name-map group — `model_str`, `model_of`, the
four `NameToName`/`DomView` dictionaries against `blockRename`, `projBack`,
`projFwd` and `projFwd`-as-a-binder-view, `DomIdent`'s identity view, and the
two `find?` slot searches `find_proj_model_slot`/`find_proj_fn_slot` — the four
pinned suffix names `iota_thm_name`/`proj_iota_name`/`eta_thm_name`/
`unit_thm_name`, the readers `thm_probe`/`arg_get_d`/`arg_get_last_d`, and the
block split's `filter_recs`/`block_names_of` with their index recursions.
-/
import ConRon.Refine.IndAbs
import ConRon.Refine.IndSumParts
import ConRon.Refine.IndStructInstall
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.CoreKBase
import ConRon.Refine.CoreKNames

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Modeled

/-! ## The block renaming, as a closure

con-leche writes it out three times and never names it
(`Modeled.lean:379-380`, `Modeled.lean:439-440`, `DeclCheck.lean:489-490`);
`BlockRename` is its dictionary. -/

/-- `ConLeche/Kernel/Inductives/Modeled.lean:379-380` — the group-local
renaming `fun n => if blockNames.contains n then n.str "_model" else n`. -/
def blockRename (blockNames : List ConLeche.Name) :
    ConLeche.Name → ConLeche.Name :=
  fun n => if blockNames.contains n then n.str "_model" else n

/-! ## The name maps (`Modeled.lean:457-473`, `DeclCheck.lean:487-489`) -/

/-- `modeled::model_str` is the code-point spelling of the string literal
`"_model"` (§3.3: a Lean string literal is a `const [u32; N]` plus a copy). -/
theorem model_str_refines {v : alloc.vec.Vec Std.U32}
    (h : inductives.modeled.model_str = ok v) :
    absString v = "_model" ∧ StrWF v := by
  rw [inductives.modeled.model_str] at h
  obtain ⟨s, hs, hv⟩ := bind_eq_ok_iff.mp h
  simp only [lift_eq, Result.ok.injEq] at hs
  subst hs
  have hvv : v.val = [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32] := by
    rw [code_points_val hv, Array.val_to_slice]
    simp [inductives.modeled.model_str.MODEL]
  refine ⟨?_, ?_⟩
  · rw [absString_eq, hvv]; rfl
  · intro c hc; rw [hvv] at hc; fin_cases hc <;> decide

/-- `modeled::model_of` refines `n.str "_model"`, the model companion's
name. -/
theorem model_of_refines {n r : name.Name} (hn : NameWF n)
    (h : inductives.modeled.model_of n = ok r) :
    absName r = (absName n).str "_model" ∧ NameWF r := by
  rw [inductives.modeled.model_of] at h
  simp only [name_dup_eq, bind_tc_ok] at h
  obtain ⟨v, hv, hmk⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := model_str_refines hv
  exact ⟨by rw [Name.mk_str_refines hmk, habs], NameWF.str hn hwf hmk⟩


/-- `ConLeche/Kernel/Inductives/Modeled.lean:379-380` — the `BlockRename`
dictionary computes `blockRename blockNames`, in exactly the shape
`ExprOps.rename_consts_refines` consumes. -/
theorem block_rename_rename_refines {bn : alloc.vec.Vec name.Name}
    (hbn : NamesWF bn) :
    ∀ n, NameWF n → ∀ r,
      inductives.modeled.BlockRename.Insts.Con_ron_coreKernelExpr_opsNameToName.rename
          { block_names := bn } n = ok r →
        absName r = blockRename (absNames bn) (absName n) ∧ NameWF r := by
  intro n hn r h
  rw [inductives.modeled.BlockRename.Insts.Con_ron_coreKernelExpr_opsNameToName.rename] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = (absNames bn).contains (absName n) := Name.contains_refines hbn hn hb
  rw [blockRename]
  split at h
  · rename_i hbt
    rw [hbt] at hbv
    rw [if_pos (by rw [← hbv])]
    exact model_of_refines hn h
  · rename_i hbf
    simp only [Bool.not_eq_true] at hbf
    rw [hbf] at hbv
    rw [if_neg (by rw [← hbv]; simp)]
    simp only [name_dup_eq, Result.ok.injEq] at h
    subst h
    exact ⟨rfl, hn⟩

/-- `ConLeche/Kernel/Inductives/Modeled.lean:462` — `find_proj_model_slot`
refines `(List.range nF).find? (fun j => n == projModelName T j)` from index
`j` (task #3's index-recursion pattern). -/
theorem find_proj_model_slot_refines {t n : name.Name} {n_f j : Std.U64}
    {o : Option Std.U64} (ht : NameWF t) (hn : NameWF n)
    (h : inductives.modeled.find_proj_model_slot t n_f n j = ok o) :
    o.map (fun k => k.val)
      = (List.range' j.val (n_f.val - j.val)).find?
          (fun k => absName n == ConLeche.projModelName (absName t) k) := by
  generalize hd : n_f.val - j.val = d
  induction d using Nat.strong_induction_on generalizing j o with
  | _ d ih =>
    rw [inductives.modeled.find_proj_model_slot] at h
    split at h
    · have hz : d = 0 := by rw [← hd]; scalar_tac
      subst hz
      rw [← Result.ok_injective h]; simp
    · rename_i hge
      have hlt' : j.val < n_f.val := by scalar_tac
      obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨habs, hwf⟩ := CoreK.proj_model_name_refines ht hn1
      have hbv : b = decide (absName n = absName n1) := Name.beq_refines hn hwf hb
      have hkey : (absName n == ConLeche.projModelName (absName t) j.val) = b := by
        rw [hbv, ← habs]
        by_cases he : absName n = absName n1 <;> simp [he]
      have hsplit : d = (n_f.val - (j.val + 1)) + 1 := by rw [← hd]; omega
      subst hsplit
      rw [List.range'_succ, List.find?_cons]
      split at h
      · rename_i hbt
        rw [hbt] at hkey
        rw [hkey, ← Result.ok_injective h]
        rfl
      · rename_i hbf
        simp only [Bool.not_eq_true] at hbf
        rw [hbf] at hkey
        rw [hkey]
        obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i.val = j.val + 1 := HashMap.uscalar_add_eq hi
        have hrec := ih (n_f.val - (j.val + 1)) (by omega) (j := i) h (by rw [hiv])
        rw [hiv] at hrec
        exact hrec

/-- `ConLeche/Kernel/Inductives/Modeled.lean:471` — `find_proj_fn_slot`
refines `(List.range nF).find? (fun j => n == projFnName T j)` from `j`. -/
theorem find_proj_fn_slot_refines {t n : name.Name} {n_f j : Std.U64}
    {o : Option Std.U64} (ht : NameWF t) (hn : NameWF n)
    (h : inductives.modeled.find_proj_fn_slot t n_f n j = ok o) :
    o.map (fun k => k.val)
      = (List.range' j.val (n_f.val - j.val)).find?
          (fun k => absName n == ConLeche.projFnName (absName t) k) := by
  generalize hd : n_f.val - j.val = d
  induction d using Nat.strong_induction_on generalizing j o with
  | _ d ih =>
    rw [inductives.modeled.find_proj_fn_slot] at h
    split at h
    · have hz : d = 0 := by rw [← hd]; scalar_tac
      subst hz
      rw [← Result.ok_injective h]; simp
    · rename_i hge
      have hlt' : j.val < n_f.val := by scalar_tac
      obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      have habs : absName n1 = ConLeche.projFnName (absName t) j.val :=
        Env.proj_fn_name_refines hn1
      have hwf : NameWF n1 := Env.proj_fn_name_wf ht hn1
      have hbv : b = decide (absName n = absName n1) := Name.beq_refines hn hwf hb
      have hkey : (absName n == ConLeche.projFnName (absName t) j.val) = b := by
        rw [hbv, ← habs]
        by_cases he : absName n = absName n1 <;> simp [he]
      have hsplit : d = (n_f.val - (j.val + 1)) + 1 := by rw [← hd]; omega
      subst hsplit
      rw [List.range'_succ, List.find?_cons]
      split at h
      · rename_i hbt
        rw [hbt] at hkey
        rw [hkey, ← Result.ok_injective h]
        rfl
      · rename_i hbf
        simp only [Bool.not_eq_true] at hbf
        rw [hbf] at hkey
        rw [hkey]
        obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i.val = j.val + 1 := HashMap.uscalar_add_eq hi
        have hrec := ih (n_f.val - (j.val + 1)) (by omega) (j := i) h (by rw [hiv])
        rw [hiv] at hrec
        exact hrec



/-- `ConLeche/Kernel/Inductives/Modeled.lean:457-464` — the `ProjBack`
dictionary computes `projBack T ctor nF`. -/
theorem proj_back_rename_refines {t c : name.Name} {n_f : Std.U64}
    (ht : NameWF t) (hc : NameWF c) :
    ∀ n, NameWF n → ∀ r,
      inductives.modeled.ProjBack.Insts.Con_ron_coreKernelExpr_opsNameToName.rename
          { t := t, ctor := c, n_f := n_f } n = ok r →
        absName r
            = ConLeche.projBack (absName t) (absName c) n_f.val (absName n)
          ∧ NameWF r := by
  intro n hn r h
  rw [inductives.modeled.ProjBack.Insts.Con_ron_coreKernelExpr_opsNameToName.rename] at h
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs1, hwf1⟩ := model_of_refines ht hn1
  have hbv : b = decide (absName n = absName n1) := Name.beq_refines hn hwf1 hb
  rw [ConLeche.projBack]
  split at h
  · rename_i hbt
    rw [hbt] at hbv
    rw [if_pos (by rw [← habs1]; exact of_decide_eq_true hbv.symm)]
    simp only [name_dup_eq, Result.ok.injEq] at h
    subst h
    exact ⟨rfl, ht⟩
  · rename_i hbf
    simp only [Bool.not_eq_true] at hbf
    rw [hbf] at hbv
    rw [if_neg (by rw [← habs1]; exact of_decide_eq_false hbv.symm)]
    obtain ⟨n2, hn2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨habs2, hwf2⟩ := model_of_refines hc hn2
    have hbv1 : b1 = decide (absName n = absName n2) := Name.beq_refines hn hwf2 hb1
    split at h
    · rename_i hbt1
      rw [hbt1] at hbv1
      rw [if_pos (by rw [← habs2]; exact of_decide_eq_true hbv1.symm)]
      simp only [name_dup_eq, Result.ok.injEq] at h
      subst h
      exact ⟨rfl, hc⟩
    · rename_i hbf1
      simp only [Bool.not_eq_true] at hbf1
      rw [hbf1] at hbv1
      rw [if_neg (by rw [← habs2]; exact of_decide_eq_false hbv1.symm)]
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hfind := find_proj_model_slot_refines ht hn ho
      simp only [show (0#u64 : Std.U64).val = 0 from rfl, Nat.sub_zero,
        ← List.range_eq_range'] at hfind
      rw [← hfind]
      cases o with
      | none =>
        simp only [name_dup_eq, Result.ok.injEq] at h
        subst h
        exact ⟨rfl, hn⟩
      | some j =>
        exact ⟨Env.proj_fn_name_refines h, Env.proj_fn_name_wf ht h⟩

/-- `ConLeche/Kernel/Inductives/Modeled.lean:466-473` — the `ProjFwd`
dictionary computes `projFwd T ctor nF`. -/
theorem proj_fwd_rename_refines {t c : name.Name} {n_f : Std.U64}
    (ht : NameWF t) (hc : NameWF c) :
    ∀ n, NameWF n → ∀ r,
      inductives.modeled.ProjFwd.Insts.Con_ron_coreKernelExpr_opsNameToName.rename
          { t := t, ctor := c, n_f := n_f } n = ok r →
        absName r
            = ConLeche.projFwd (absName t) (absName c) n_f.val (absName n)
          ∧ NameWF r := by
  intro n hn r h
  rw [inductives.modeled.ProjFwd.Insts.Con_ron_coreKernelExpr_opsNameToName.rename] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = decide (absName n = absName t) := Name.beq_refines hn ht hb
  rw [ConLeche.projFwd]
  split at h
  · rename_i hbt
    rw [hbt] at hbv
    rw [if_pos (of_decide_eq_true hbv.symm)]
    exact model_of_refines ht h
  · rename_i hbf
    simp only [Bool.not_eq_true] at hbf
    rw [hbf] at hbv
    rw [if_neg (of_decide_eq_false hbv.symm)]
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hbv1 : b1 = decide (absName n = absName c) := Name.beq_refines hn hc hb1
    split at h
    · rename_i hbt1
      rw [hbt1] at hbv1
      rw [if_pos (of_decide_eq_true hbv1.symm)]
      exact model_of_refines hc h
    · rename_i hbf1
      simp only [Bool.not_eq_true] at hbf1
      rw [hbf1] at hbv1
      rw [if_neg (of_decide_eq_false hbv1.symm)]
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hfind := find_proj_fn_slot_refines ht hn ho
      simp only [show (0#u64 : Std.U64).val = 0 from rfl, Nat.sub_zero,
        ← List.range_eq_range'] at hfind
      rw [← hfind]
      cases o with
      | none =>
        simp only [name_dup_eq, Result.ok.injEq] at h
        subst h
        exact ⟨rfl, hn⟩
      | some j => exact CoreK.proj_model_name_refines ht h

/-- `ConLeche/Kernel/Inductives/Modeled.lean:513-563` — the `DomProjFwd`
`DomView` dictionary computes `checkProjIota`'s binder view
`fun _ e => e.renameConsts (projFwd T ctorName nF)`, the one non-identity
binder view in the port. -/
theorem dom_proj_fwd_view_refines {t c : name.Name} {n_f : Std.U64}
    (ht : NameWF t) (hc : NameWF c) :
    ∀ (i : Std.U64) (e : expr.Expr), ExprWF e → ∀ r,
      inductives.modeled.DomProjFwd.Insts.Con_ron_coreKernelChecker_baseDomView.view
          { t := t, ctor := c, n_f := n_f } i e = ok r →
        absExpr r
            = ConLeche.Expr.renameConsts
                (ConLeche.projFwd (absName t) (absName c) n_f.val) (absExpr e)
          ∧ ExprWF r := by
  intro i e he r h
  rw [inductives.modeled.DomProjFwd.Insts.Con_ron_coreKernelChecker_baseDomView.view] at h
  exact ExprOps.rename_consts_refines _ (proj_fwd_rename_refines ht hc) he h

/-- `checker_base::DomIdent`'s `DomView` is the identity binder view
`fun _ e => e` that `checkEtaThmF`/`checkUnitThmF` pass to `domsMatchAux`.  The
type is `kernel/checker_base.rs`'s; the lemma is here because the modeled
route is its only caller in this directory. -/
theorem dom_ident_view_refines :
    ∀ (i : Std.U64) (e r : expr.Expr),
      checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView.view
          () i e = ok r → r = e := by
  intro i e r h
  rw [checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView.view] at h
  simpa using (Result.ok_injective (by simpa [expr_dup_eq] using h)).symm



/-! ## The small readers (`Modeled.lean:55-149`, `:513-563`, `:586-680`) -/

/-- `ConLeche/Kernel/Inductives/Modeled.lean:76-77` (`DeclCheck.lean:512-513`)
— `iota_thm_name` refines `(cvName.str "_model").str s!"iota_{j}"`.  The
decimal rendering is `core_k::nat_to_dec`, i.e. `Nat.toString` (task #18's
deviation 7; `Refine/CoreKNames.lean`'s `nat_to_dec_refines`). -/
theorem iota_thm_name_refines {cv_name n : name.Name} {j : Std.U64}
    (hcv : NameWF cv_name) (h : inductives.modeled.iota_thm_name cv_name j = ok n) :
    absName n = ((absName cv_name).str "_model").str ("iota_" ++ toString j.val)
      ∧ NameWF n := by
  rw [inductives.modeled.iota_thm_name] at h
  simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨head, hhead, s1, hs1, dgs, hdgs, s3, hs3, hmk⟩ := h
  obtain ⟨hh1, hh2⟩ := model_of_refines hcv hhead
  obtain ⟨hdg, hdgwf⟩ := CoreK.nat_to_dec_refines hdgs
  have hs1v : s1.val = [105#u32, 111#u32, 116#u32, 97#u32, 95#u32] := by
    rw [code_points_val hs1, Array.val_to_slice]
    simp [inductives.modeled.iota_thm_name.IOTA_]
  have hs3v : s3.val = s1.val ++ dgs.val := by
    rw [code_points_from_val _ (alloc.vec.Vec.deref dgs) 0#usize s1 s3 rfl hs3]
    simp [alloc.vec.Vec.deref]
  have hs3wf : StrWF s3 := by
    intro cc hcc
    rw [hs3v, hs1v] at hcc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcc
    rcases hcc with (rfl | rfl | rfl | rfl | rfl) | hcc
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact hdgwf cc hcc
  refine ⟨?_, NameWF.str hh2 hs3wf hmk⟩
  rw [Name.mk_str_refines hmk, hh1, absString_eq, hs3v, CoreK.absCodes_append,
    hs1v, hdg]
  rfl

/-- `ConLeche/Kernel/Inductives/Modeled.lean:525` (`DeclCheck.lean:800`) —
`proj_iota_name` refines `(projModelName T i).str "iota"`. -/
theorem proj_iota_name_refines {t n : name.Name} {i : Std.U64}
    (ht : NameWF t) (h : inductives.modeled.proj_iota_name t i = ok n) :
    absName n = (ConLeche.projModelName (absName t) i.val).str "iota"
      ∧ NameWF n := by
  rw [inductives.modeled.proj_iota_name] at h
  simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨head, hhead, v, hv, hmk⟩ := h
  obtain ⟨hh1, hh2⟩ := CoreK.proj_model_name_refines ht hhead
  obtain ⟨h1, h1wf⟩ := str_lit_step hh2 rfl hv hmk
    (L := [105#u32, 111#u32, 116#u32, 97#u32])
    (by simp [inductives.modeled.proj_iota_name.IOTA]) (by decide)
  exact ⟨by rw [h1, hh1]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Inductives/Modeled.lean:598` (`DeclCheck.lean:347`) —
`eta_thm_name` refines `(T.str "_model").str "eta"`. -/
theorem eta_thm_name_refines {t n : name.Name} (ht : NameWF t)
    (h : inductives.modeled.eta_thm_name t = ok n) :
    absName n = ((absName t).str "_model").str "eta" ∧ NameWF n := by
  rw [inductives.modeled.eta_thm_name] at h
  simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨head, hhead, v, hv, hmk⟩ := h
  obtain ⟨hh1, hh2⟩ := model_of_refines ht hhead
  obtain ⟨h1, h1wf⟩ := str_lit_step hh2 rfl hv hmk
    (L := [101#u32, 116#u32, 97#u32])
    (by simp [inductives.modeled.eta_thm_name.ETA]) (by decide)
  exact ⟨by rw [h1, hh1]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Inductives/Modeled.lean:656` (`DeclCheck.lean:387`) —
`unit_thm_name` refines `(T.str "_model").str "unitlike"`. -/
theorem unit_thm_name_refines {t n : name.Name} (ht : NameWF t)
    (h : inductives.modeled.unit_thm_name t = ok n) :
    absName n = ((absName t).str "_model").str "unitlike" ∧ NameWF n := by
  rw [inductives.modeled.unit_thm_name] at h
  simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨head, hhead, v, hv, hmk⟩ := h
  obtain ⟨hh1, hh2⟩ := model_of_refines ht hhead
  obtain ⟨h1, h1wf⟩ := str_lit_step hh2 rfl hv hmk
    (L := [117#u32, 110#u32, 105#u32, 116#u32, 108#u32, 105#u32, 107#u32, 101#u32])
    (by simp [inductives.modeled.unit_thm_name.UL]) (by decide)
  exact ⟨by rw [h1, hh1]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Inductives/Modeled.lean:525`, `:600` — `thm_probe` is the
`some (.thmInfo tcv _)` destructuring of an index lookup, as an owning probe
(task #18's deviation 8: the index's borrow dies at the call boundary). -/
theorem thm_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {o : Option env.ConstantVal} (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe)
    (hn : NameWF n) (h : inductives.modeled.thm_probe fe n = ok o) :
    o.map absConstantVal
        = (match lfe.find? (absName n) with
           | some (.thmInfo tcv _) => some tcv
           | _ => none)
      ∧ ∀ cv, o = some cv → ConstantValWF cv := by
  rw [inductives.modeled.thm_probe] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  have hfind : q.map absConstantInfo = lfe.find? (absName n) :=
    FEnv.find_refines hrel hfe hn hq
  have hqwf := FEnv.find_wf hfe hn hq
  rw [← hfind]
  cases q with
  | none => simp only [Result.ok.injEq] at h; subst h; simp
  | some ci =>
    have hciwf : ConstantInfoWF ci := hqwf ci rfl
    cases ci with
    | ThmInfo cv val =>
      obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
      have heq : cv1 = cv := Env.constant_val_dup_refines hcv1
      simp only [Result.ok.injEq] at h
      subst h
      rw [heq]
      refine ⟨rfl, ?_⟩
      intro c hc
      simp only [Option.some.injEq] at hc
      subst hc
      exact hciwf.1
    | AxiomInfo cv =>
      simp only [Result.ok.injEq] at h; subst h; exact ⟨rfl, by simp⟩
    | DefnInfo cv val hint =>
      simp only [Result.ok.injEq] at h; subst h; exact ⟨rfl, by simp⟩
    | IndInfo cv caps =>
      simp only [Result.ok.injEq] at h; subst h; exact ⟨rfl, by simp⟩
    | CtorInfo cv a b =>
      simp only [Result.ok.injEq] at h; subst h; exact ⟨rfl, by simp⟩
    | RecInfo cv a b c =>
      simp only [Result.ok.injEq] at h; subst h; exact ⟨rfl, by simp⟩
    | ProjInfo tbl =>
      simp only [Result.ok.injEq] at h; subst h; exact ⟨rfl, by simp⟩

/-- `arg_get_d` refines `args.getD k (.bvar 0)` — the out-of-range fallback the
equation readers spell at every argument read (`Expr.bvar 0` is Lean's
`default : Expr`, `env::default_expr`). -/
theorem arg_get_d_refines {args : alloc.vec.Vec expr.Expr} {k : Std.Usize}
    {r : expr.Expr} (hargs : ExprsWF args)
    (h : inductives.modeled.arg_get_d args k = ok r) :
    absExpr r = (absExprs args).getD k.val (.bvar 0) ∧ ExprWF r := by
  rw [inductives.modeled.arg_get_d] at h
  have hlen := alloc.vec.Vec.len_val args
  split at h
  · rename_i hlt
    have hlt' : k.val < args.val.length := by scalar_tac
    obtain ⟨y, hy, hyv⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec args k hlt')
    subst hyv
    simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok, expr_dup_eq,
      Result.ok.injEq] at h
    subst h
    refine ⟨?_, hargs _ (List.getElem_mem hlt')⟩
    have : k.val < (absExprs args).length := by simpa [absExprs] using hlt'
    rw [List.getD_eq_getElem _ _ this]
    simp [absExprs]
  · rename_i hge
    have hge' : (absExprs args).length ≤ k.val := by
      simp only [absExprs, List.length_map]; scalar_tac
    rw [List.getD_eq_default _ _ hge']
    exact ⟨Expr.bvar_refines h, Expr.bvar_wf h⟩

/-- `arg_get_last_d` refines `largs.getLastD (.bvar 0)` — the major premise is
the statement's spine's last argument. -/
theorem arg_get_last_d_refines {args : alloc.vec.Vec expr.Expr} {r : expr.Expr}
    (hargs : ExprsWF args)
    (h : inductives.modeled.arg_get_last_d args = ok r) :
    absExpr r = (absExprs args).getLastD (.bvar 0) ∧ ExprWF r := by
  rw [inductives.modeled.arg_get_last_d] at h
  have hlen := alloc.vec.Vec.len_val args
  split at h
  · rename_i hz
    have : args.val = [] := by
      have : args.val.length = 0 := by scalar_tac
      exact List.eq_nil_of_length_eq_zero this
    rw [show (absExprs args) = [] by simp [absExprs, this]]
    exact ⟨Expr.bvar_refines h, Expr.bvar_wf h⟩
  · rename_i hz
    have hpos : 0 < args.val.length := by
      rcases Nat.eq_zero_or_pos args.val.length with hc | hc
      · exact absurd (by scalar_tac : alloc.vec.Vec.len args = 0#usize) hz
      · exact hc
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = args.val.length - 1 := by
      have := HashMap.uscalar_sub_eq hi2
      scalar_tac
    have hlt' : i2.val < args.val.length := by omega
    obtain ⟨y, hy, hyv⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec args i2 hlt')
    subst hyv
    simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok, expr_dup_eq,
      Result.ok.injEq] at h
    subst h
    refine ⟨?_, hargs _ (List.getElem_mem hlt')⟩
    have hl : (absExprs args).length = args.val.length := by simp [absExprs]
    have hidx : (absExprs args).length - 1 = i2.val := by rw [hl, hi2v]
    have hlt2 : i2.val < (absExprs args).length := by rw [hl]; omega
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hidx,
      List.getElem?_eq_getElem hlt2, Option.getD_some]
    simp [absExprs]



/-! ## The ingredients this file does not own

`kernel/checker_base.rs` is task #24's tier (unified into the routes at task
#25's `checker_local`) and has no refinement file yet.  The modeled route calls
eleven of its items; each is stated here in the exact-result shape of
DESIGN.md §3.5 and bundled into one hypothesis, so that every statement below
keeps its exact conclusion under an explicit ingredient and nothing is
weakened.  **Owned by the coming `Refine/CheckerBase.lean`.** -/

/-- `kernel::checker_base`'s eleven items, refined — the hypothesis every stage
of this file that reaches the shared checker base carries. -/
structure CheckerBaseSpec (mode : env.CheckMode) : Prop where
  /-- `checker_base::check_constant_val` refines `checkConstantValF`. -/
  checkConstantVal :
    ∀ st fe cv r st', StateWF st → FEnvWF fe → ConstantValWF cv →
      checker_base.check_constant_val mode st fe cv = ok (.Ok r, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst',
          (ConLeche.checkConstantValF (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
              lfe (absConstantVal cv)).run lst = .ok (absConstantVal r, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF r
  /-- `checker_base::open_pis_at_fvars_f` refines `openPisAtFvarsF`. -/
  openPisAtFvarsF :
    ∀ (n : Std.U64) (e : expr.Expr) (i : Std.U64) o, ExprWF e →
      checker_base.open_pis_at_fvars_f n e i = ok o →
      o.map (fun q => (absExprs q.1, absExpr q.2))
          = ConLeche.openPisAtFvarsF n.val (absExpr e) i.val
        ∧ ∀ q, o = some q → ExprsWF q.1 ∧ ExprWF q.2
  /-- `checker_base::doms_match_aux` refines `domsMatchAux` at any `DomView`
  dictionary that computes the binder view `gl`. -/
  domsMatchAux :
    ∀ {G : Type} (inst : checker_base.DomView G) (g : G)
      (gl : Nat → ConLeche.Expr → ConLeche.Expr),
      (∀ (i : Std.U64) (e : expr.Expr), ExprWF e → ∀ r,
          inst.view g i e = ok r → absExpr r = gl i.val (absExpr e) ∧ ExprWF r) →
      ∀ bs1 bs2 (o1 o2 n : Std.U64) b,
        ExprOps.BindersWF bs1 → ExprOps.BindersWF bs2 →
        checker_base.doms_match_aux inst g bs1 bs2 o1 o2 n = ok b →
        b = ConLeche.domsMatchAux gl (ExprOps.absBinders bs1)
              (ExprOps.absBinders bs2) o1.val o2.val n.val
  /-- `checker_base::check_def_eq_list` refines `checkDefEqList`. -/
  checkDefEqList :
    ∀ st fe (d : Std.U64) xs ys st', StateWF st → FEnvWF fe →
      ExprsWF xs → ExprsWF ys →
      checker_base.check_def_eq_list mode st fe d xs ys = ok (.Ok (), st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst',
          (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe.env d.val
              (absExprs xs) (absExprs ys)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
  /-- `checker_base::check_annot_list` refines `checkAnnotList`. -/
  checkAnnotList :
    ∀ st fe (d : Std.U64) xs st', StateWF st → FEnvWF fe → ExprsWF xs →
      checker_base.check_annot_list mode st fe d xs = ok (.Ok (), st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst',
          (ConLeche.checkAnnotList (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe.env d.val
              (absExprs xs)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
  /-- `checker_base::check_typed_list` refines `checkTypedList`. -/
  checkTypedList :
    ∀ st fe (d : Std.U64) xs ts st', StateWF st → FEnvWF fe →
      ExprsWF xs → ExprsWF ts →
      checker_base.check_typed_list mode st fe d xs ts = ok (.Ok (), st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst',
          (ConLeche.checkTypedList (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe.env d.val
              (absExprs xs) (absExprs ts)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
  /-- `checker_base::is_eq_head` refines `isEqHead`. -/
  isEqHead :
    ∀ e b, ExprWF e → checker_base.is_eq_head e = ok b →
      b = ConLeche.isEqHead (absExpr e)
  /-- `checker_base::eq_head_level` refines `eqHeadLevel`. -/
  eqHeadLevel :
    ∀ e u, ExprWF e → checker_base.eq_head_level e = ok u →
      absLevel u = ConLeche.eqHeadLevel (absExpr e) ∧ LevelWF u
  /-- `checker_base::find_cv` refines `FEnv.findCV?`. -/
  findCv :
    ∀ fe lfe n o, FEnvRel fe lfe → FEnvWF fe → NameWF n →
      checker_base.find_cv fe n = ok o →
      o.map absConstantVal = lfe.findCV? (absName n)
        ∧ ∀ cv, o = some cv → ConstantValWF cv
  /-- `checker_base::fvar_types` refines `·.map Expr.fvarTypeD`. -/
  fvarTypes :
    ∀ fvs r, ExprsWF fvs → checker_base.fvar_types fvs = ok r →
      absExprs r = (absExprs fvs).map ConLeche.Expr.fvarTypeD ∧ ExprsWF r
  /-- `checker_base::check_proj_shape` refines `checkProjShape`. -/
  checkProjShape :
    ∀ pty cty (n_p n_f : Std.U64), ExprWF pty → ExprWF cty →
      checker_base.check_proj_shape pty cty n_p n_f = ok (.Ok ()) →
      (ConLeche.checkProjShape (m := ConLeche.Cached.CheckCM) (absExpr pty)
        (absExpr cty) n_p.val n_f.val) = pure ()
  /-- `checker_base::check_proj_rule` refines `checkProjRuleF`. -/
  checkProjRule :
    ∀ st fe pty cvj lps (n_p n_f i : Std.U64) r st',
      StateWF st → FEnvWF fe → ExprWF pty → ConstantValWF cvj → NamesWF lps →
      checker_base.check_proj_rule mode st fe pty cvj lps n_p n_f i
          = ok (.Ok r, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst',
          (ConLeche.checkProjRuleF (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
              lfe (absExpr pty) (absConstantVal cvj) (absNames lps) n_p.val
              n_f.val i.val).run lst = .ok (absExpr r, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r



/-! ## The cited bodies the port splits (**transcriptions**)

§3.4 caps a Rust function's guard nest, and the cached driver's `flushC` must
land where `Cached/CheckerC.lean` puts it, so nine cited bodies are split in
the port.  Each half is transcribed here from the cited lines, verbatim, so
that the composition of the halves *is* the cited body; the doc comment on
each says which lines it covers.  Nothing is weakened: `Refine/IndC.lean`
composes them back. -/

section Transcriptions

open ConLeche ConLeche.Cached

variable (mode : ConLeche.CheckMode)

/-- `DeclCheck.lean:512-528` — `checkIotaThmF`'s **statement head**: the
model's iota theorem looked up, its level parameters pinned, its telescope
opened at `rP + cnF` variables, and its body read as an equation at one
level.  `checkIotaThmNF:610-625` spells it identically. -/
def iotaStmtOpen (fe' : FEnv) (cvName : Name) (lps : List Name)
    (rP cnF j : Nat) : CheckCM (List Expr × List Expr × Level) := do
  let cvt ← unwrapOr (fe'.findCV? ((cvName.str "_model").str s!"iota_{j}"))
    (.notImplemented s!"missing iota theorem for {cvName}")
  unless cvt.levelParams = lps do
    throw (.notImplemented s!"iota theorem level mismatch for {cvName}")
  let (fvs, tbody) ← unwrapOr (openPisAtFvars (rP + cnF) cvt.type 0)
    (.notImplemented s!"iota statement shape mismatch for {cvName}")
  let targs := tbody.getAppArgs
  unless isEqHead tbody.getAppFn do
    throw (.notImplemented s!"iota statement not an equation for {cvName}")
  unless targs.length = 3 do
    throw (.notImplemented s!"iota statement not an equation for {cvName}")
  pure (fvs, targs, eqHeadLevel tbody.getAppFn)

/-- `DeclCheck.lean:529-534` — `checkIotaThmF`'s left-side **head, arity and
prefix** pins, as one `Bool` (`checkIotaThmNF:629-634` spells them
identically). -/
def iotaLhsPrefixOk (f : Name → Name) (cvName : Name) (lps : List Name)
    (mI rP : Nat) (fvs : List Expr) (lhsS : Expr) (largs : List Expr) : Bool :=
  (lhsS.getAppFn == Expr.const (f cvName) (lps.map .param))
    && (largs.length == mI + 1)
    && (largs.take rP == fvs.take rP)

/-- `DeclCheck.lean:556-572` — `checkIotaThmF`'s **public-frame** half: the
rule's λ-domains are the public recursor prefix and constructor field domains,
the right side is definitionally the rule's applied rhs, and both sides
inhabit the equation's type slot. -/
def checkIotaThmFrames (feSelf : FEnv) (f : Name → Name) (cvName : Name)
    (tyA : Expr) (rP : Nat) (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr)
    (fvs targs : List Expr) (lhsS rhsS : Expr) (lA : Level) : CheckCM Unit := do
  let ops := sharedOpsC mode feSelf
  let (fvsP, _) ← unwrapOr (openPisAtFvars rP tyA 0)
    (.notImplemented s!"iota recursor telescope for {cvName}")
  let (cdomsP, crestP) ← unwrapOr (Expr.instPisAt (fvsP.take cnP) cvj.type)
    (.notImplemented s!"iota constructor telescope for {cvName}")
  checkDefEqList ops feSelf.env (rP + cnF)
    ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP
  let (xFvsP, _) ← unwrapOr (openPisAtFvars cnF crestP rP)
    (.notImplemented s!"iota constructor telescope for {cvName}")
  let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA)
    (.notImplemented s!"rule shape mismatch for {cvName}")
  checkDefEqList ops feSelf.env (rP + cnF) ((fvsP ++ xFvsP).map Expr.fvarTypeD)
    ldoms
  let rhsApplied := Expr.mkAppN (rhsA.renameConsts f) fvs
  unless ← ops.isDefEq feSelf.env (rP + cnF) rhsS rhsApplied do
    throw (.notImplemented s!"iota statement mismatch for {cvName}")
  checkIotaSidesTy mode ops feSelf.env (rP + cnF) (targs.getD 0 (.bvar 0)) lhsS
    rhsS lA cvName

/-- `DeclCheck.lean:540-555` — `checkIotaThmF`'s **constructor-telescope**
half: the constructor's telescope (renamed) instantiated at the major's
arguments gives the field domains and the canonical index tuple, both compared
definitionally; then the statement's prefix domains against the recursor's. -/
def checkIotaThmCtor (feSelf : FEnv) (f : Name → Name) (cvName : Name)
    (tyA : Expr) (mI rP : Nat) (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr)
    (fvs xFvs largs targs : List Expr) (lhsS rhsS : Expr) (lA : Level) :
    CheckCM Unit := do
  let ops := sharedOpsC mode feSelf
  unless (cvj.type.stripPis (cnP + cnF)).isSome do
    throw (.notImplemented s!"iota constructor telescope for {cvName}")
  let (cdoms, cres) ← unwrapOr
    (Expr.instPisAt (fvs.take cnP ++ xFvs) (cvj.type.renameConsts f))
    (.notImplemented s!"iota constructor telescope for {cvName}")
  unless cres.getAppArgs.length = cnP + (mI - rP) do
    throw (.notImplemented s!"iota constructor indices for {cvName}")
  checkDefEqList ops feSelf.env (rP + cnF) ((largs.drop rP).take (mI - rP))
    (cres.getAppArgs.drop cnP)
  checkDefEqList ops feSelf.env (rP + cnF) (xFvs.map Expr.fvarTypeD)
    (cdoms.drop cnP)
  let (rdoms, _) ← unwrapOr (Expr.instPisAt (fvs.take rP) (tyA.renameConsts f))
    (.notImplemented s!"iota recursor telescope for {cvName}")
  checkDefEqList ops feSelf.env (rP + cnF) ((fvs.take rP).map Expr.fvarTypeD)
    rdoms
  checkIotaThmFrames mode feSelf f cvName tyA rP cvj cnP cnF rhsA fvs targs lhsS
    rhsS lA

/-- `DeclCheck.lean:661-684` — `checkIotaThmNF`'s **public-frame** half: the
instantiated pins are fixed points of the annotation pass and inhabit the
constructor's parameter domains, the auxiliary constructor's residual applies
the family to its parameters and the canonical index tuple, and the rule's
lambda-domains fit. -/
def checkIotaThmNFrames (feSelf : FEnv) (f : Name → Name) (cvName : Name)
    (tyA : Expr) (rP : Nat) (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr)
    (fvs targs : List Expr) (lhsS rhsS : Expr) (lA : Level) (lvls : List Level)
    (pins : List Expr) (mI : Nat) : CheckCM Unit := do
  let ops := sharedOpsC mode feSelf
  let (fvsP, _) ← unwrapOr (openPisAtFvars rP tyA 0)
    (.notImplemented s!"iota recursor telescope for {cvName}")
  let pinsP := pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p
  checkAnnotList ops feSelf.env (rP + cnF) pinsP
  let (cdomsP, crestP) ← unwrapOr (Expr.instPisAt pinsP
      (cvj.type.instantiateLevelParams cvj.levelParams lvls))
    (.notImplemented s!"iota constructor telescope for {cvName}")
  checkTypedList ops feSelf.env (rP + cnF) pinsP cdomsP
  let (xFvsP, crest2P) ← unwrapOr (openPisAtFvars cnF crestP rP)
    (.notImplemented s!"iota constructor telescope for {cvName}")
  unless crest2P.getAppArgs.length == cnP + (mI - rP) do
    throw (.notImplemented s!"iota constructor arity for {cvName}")
  let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA)
    (.notImplemented s!"rule shape mismatch for {cvName}")
  checkDefEqList ops feSelf.env (rP + cnF) ((fvsP ++ xFvsP).map Expr.fvarTypeD)
    ldoms
  let rhsApplied := Expr.mkAppN (rhsA.renameConsts f) fvs
  unless ← ops.isDefEq feSelf.env (rP + cnF) rhsS rhsApplied do
    throw (.notImplemented s!"iota statement mismatch for {cvName}")
  checkIotaSidesTy mode ops feSelf.env (rP + cnF) (targs.getD 0 (.bvar 0)) lhsS
    rhsS lA cvName

/-- `DeclCheck.lean:648-660` — `checkIotaThmNF`'s **constructor-telescope**
half: the constructor's telescope at the stored level instantiations (renamed),
instantiated at the major's arguments, then the statement's prefix domains
against the recursor's. -/
def checkIotaThmNCtor (feSelf : FEnv) (f : Name → Name) (cvName : Name)
    (tyA : Expr) (mI rP : Nat) (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr)
    (fvs xFvs largs targs : List Expr) (lhsS rhsS : Expr) (lA : Level)
    (lvls : List Level) (pins pinsF : List Expr) : CheckCM Unit := do
  let ops := sharedOpsC mode feSelf
  let (cdoms, cres) ← unwrapOr
    (Expr.instPisAt (pinsF ++ xFvs)
      ((cvj.type.instantiateLevelParams cvj.levelParams lvls).renameConsts f))
    (.notImplemented s!"iota constructor telescope for {cvName}")
  unless cres.getAppArgs.length = cnP + (mI - rP) do
    throw (.notImplemented s!"iota constructor indices for {cvName}")
  checkDefEqList ops feSelf.env (rP + cnF) ((largs.drop rP).take (mI - rP))
    (cres.getAppArgs.drop cnP)
  checkDefEqList ops feSelf.env (rP + cnF) (xFvs.map Expr.fvarTypeD)
    (cdoms.drop cnP)
  let (rdoms, _) ← unwrapOr (Expr.instPisAt (fvs.take rP) (tyA.renameConsts f))
    (.notImplemented s!"iota recursor telescope for {cvName}")
  checkDefEqList ops feSelf.env (rP + cnF) ((fvs.take rP).map Expr.fvarTypeD)
    rdoms
  checkIotaThmNFrames mode feSelf f cvName tyA rP cvj cnP cnF rhsA fvs targs
    lhsS rhsS lA lvls pins mI

/-- `DeclCheck.lean:706-716` — `checkIotaRuleF`'s **firing-mode decision and
stored rule**, split off so that the guard nest above stays inside §3.4's cap
(and because Aeneas rejects the join of the two arms; task #18's rule). -/
def checkIotaRuleFire (fe2 feSelf : FEnv) (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule)
    (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr) : CheckCM RecRule := do
  let fire ← if Expr.recRulePlain tyA mI rP cnP then do
      checkIotaThmF mode (sharedOpsC mode feSelf) fe2 feSelf f cvName lps tyA mI
        rP j r cvj cnP cnF rhsA
      pure RecRuleFire.plain
    else
      checkIotaThmNF mode (sharedOpsC mode feSelf) fe2 feSelf f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA
  pure (recRuleBits fe2.find? cvName
    { r with rhs := rhsA, ctorParams := cnP, fire := fire,
             paramsBlind := false })

/-- `DeclCheck.lean:816-836` — `checkProjIotaF`'s **body pin** and the two side
certificates: the statement's body is
`Eq _ (T._model.proj_i ps (C._model ps fs)) f_i`. -/
def checkProjIotaBody (feSelf : FEnv) (T : Name) (cvj : ConstantVal)
    (lps : List Name) (nP nF i : Nat) (tcv : ConstantVal) (sbody : Expr) :
    CheckCM Unit := do
  let depth := nP + nF
  let pArgs := (List.range nP).map fun k => Expr.bvar (depth - 1 - k)
  let xArgs := (List.range nF).map fun k => Expr.bvar (nF - 1 - k)
  let mkSpine := Expr.mkAppN
    (.const (cvj.name.str "_model") (cvj.levelParams.map .param))
    (pArgs ++ xArgs)
  let lhsS := Expr.mkAppN
    (.const (projModelName T i) (lps.map .param)) (pArgs ++ [mkSpine])
  match sbody with
  | .app (.app (.app (.const c [_l]) _tySlot) lhsC) rhsC =>
    unless c = eqName do
      throw (.notImplemented "projection iota head")
    unless lhsC == lhsS do
      throw (.notImplemented "projection iota redex mismatch")
    unless rhsC == Expr.bvar (nF - 1 - i) do
      throw (.notImplemented "projection iota field mismatch")
  | _ => throw (.notImplemented "projection iota body shape")
  let (_, sbodyO) ← unwrapOr (openPisAtFvars depth tcv.type 0)
    (.notImplemented "projection iota telescope")
  let targsO := sbodyO.getAppArgs
  checkIotaSidesTy mode (sharedOpsC mode feSelf) feSelf.env depth
    (targsO.getD 0 (.bvar 0)) (targsO.getD 1 (.bvar 0))
    (targsO.getD 2 (.bvar 0)) (eqHeadLevel sbody.getAppFn) (projModelName T i)

/-- `DeclCheck.lean:359-381` — `checkEtaThmF`'s **statement-shape** half: the
parameter telescope against the constructor model's, the subject binder's
domain, and the equation (the type slot pinned to the family application and
its sort to the statement's own `Eq` level, a TT-lane check). -/
def checkEtaThmShape (T ctorName : Name) (lps : List Name) (nP nF : Nat)
    (tty ttyM : Expr) : Bool :=
  match tty.stripPis (nP + 1), ttyM.stripPis nP with
  | some (sbinders, sbody), some (tbindersM, tbodyM) =>
    domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
    (match sbinders[nP]? with
     | some (xdom, _) =>
       xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
         ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
     | none => false) &&
    (match sbody with
     | .app (.app (.app (.const c [lA]) tySlot) lhsC) rhsC =>
       c == eqName && lhsC == Expr.bvar 0 &&
       tySlot == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
         ((List.range nP).map fun k => Expr.bvar (nP - k)) &&
       rhsC == Expr.mkAppN
         (.const (ctorName.str "_model") (lps.map .param))
         (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
          (List.range nF).map fun j => Expr.mkAppN
            (.const (projModelName T j) (lps.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
             [Expr.bvar 0])) &&
       (!mode.ttChecks || tbodyM == Expr.sort lA)
     | _ => false)
  | _, _ => false

/-- `DeclCheck.lean:403-413` — `checkUnitThmF`'s **statement-shape** half. -/
def checkUnitThmShape (T : Name) (lps : List Name) (nP : Nat)
    (tty ttyM : Expr) : Bool :=
  match tty.stripPis (nP + 2), ttyM.stripPis nP with
  | some (sbinders, sbody), some (tbindersM, tbodyM) =>
    domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
    (match sbinders[nP]? with
     | some (xdom, _) =>
       xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
         ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
     | none => false) &&
    (match sbinders[nP + 1]? with
     | some (ydom, _) =>
       ydom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
         ((List.range nP).map fun k => Expr.bvar (nP - k))
     | none => false) &&
    (match sbody with
     | .app (.app (.app (.const c [lA]) tySlot) lhsC) rhsC =>
       c == eqName && lhsC == Expr.bvar 1 && rhsC == Expr.bvar 0 &&
       tySlot == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
         ((List.range nP).map fun k => Expr.bvar (nP + 1 - k)) &&
       (!mode.ttChecks || tbodyM == Expr.sort lA)
     | _ => false)
  | _, _ => false

/-! ### The three stages the cached driver's `flushC` splits -/

/-- `Cached/CheckerC.lean:105-113` **minus the leading `flushC`** — the body of
`checkIndMemberS`, which is what `modeled::check_ind_member` is; the flush is
`inductives_c::check_ind_member_s`'s. -/
def checkIndMemberN (blockNames : List Name) (caps : IndCaps) (fe : FEnv)
    (ci : ConstantInfo) : CheckCM FEnv := do
  let cvA ← checkMemberValF (sharedOpsC mode fe) blockNames fe ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (fe.push (.indInfo cvA caps))
  | .ctorInfo _ nP nF => pure (fe.push (.ctorInfo cvA nP nF))
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- `Cached/CheckerC.lean:120-127` **minus the `flushC`** — one step of
`provisionRecsS`: the recursor's constant checked and provisioned rule-less. -/
def provisionRecsStepN (blockNames : List Name) (feAcc : FEnv)
    (ci : ConstantInfo) :
    CheckCM (FEnv × ConstantVal × Nat × Nat × List RecRule) :=
  match ci with
  | .recInfo _ mI rP rules => do
    let cvA ← checkMemberValF (sharedOpsC mode feAcc) blockNames feAcc
      ci.toConstantVal
    pure (feAcc.push (.recInfo cvA mI rP []), cvA, mI, rP, rules)
  | _ => throw (.notImplemented "recursor before other block members")

/-- `Cached/CheckerC.lean:116-129` **minus the per-recursor `flushC`** — the
fold of `provisionRecsS` over the block's recursors. -/
def provisionRecsN (blockNames : List Name) :
    FEnv → List ConstantInfo →
    CheckCM (FEnv × List (ConstantVal × Nat × Nat × List RecRule))
  | feAcc, [] => pure (feAcc, [])
  | feAcc, ci :: rest => do
    let q ← provisionRecsStepN mode blockNames feAcc ci
    let r ← provisionRecsN blockNames q.1 rest
    pure (r.1, (q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2) :: r.2)

/-- `Cached/CheckerC.lean:146-151` — `checkIndRecsS`' `checked.foldlM`: every
recursor's rules checked at `envSelf` with the `env'` lookups in `env₂`, and
the ruled recursor pushed onto the accumulator. -/
def checkIndRecsFoldN (fe2 feSelf : FEnv) (f : Name → Name)
    (checked : List (ConstantVal × Nat × Nat × List RecRule)) (acc : FEnv) :
    CheckCM FEnv :=
  checked.foldlM (fun (acc : FEnv) c => do
      let rules2 ← checkIotaRulesF mode (sharedOpsC mode feSelf) fe2 feSelf f
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
      pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules2))) acc

/-- `Cached/CheckerC.lean:136-151` **minus every `flushC`** — the recursor
group as `modeled::check_ind_recs` runs it. -/
def checkIndRecsN (blockNames : List Name) (fe2 : FEnv)
    (recs : List ConstantInfo) : CheckCM FEnv := do
  if recs.isEmpty then
    pure fe2
  else do
    unless fe2.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let q ← provisionRecsN mode blockNames fe2 recs
    checkIndRecsFoldN mode fe2 q.1 (Modeled.blockRename blockNames) q.2 fe2

/-- `Cached/CheckerC.lean:171-175` **minus the `flushC`** — one
projection-function install step, skipped where the model's projection
artifact is absent. -/
def installProjFnStepN (T ctorName : Name) (lps : List Name) (nP nF : Nat)
    (fe : FEnv) (i : Nat) : CheckCM FEnv :=
  if (fe.find? (projModelName T i)).isSome then
    checkProjFnS mode fe T ctorName lps nP nF i
  else pure fe

end Transcriptions



/-! ## Two abstractions the recursor group needs (**to be unified into
`Refine/Abs.lean`**) -/

/-- `provisionRecs`' output list: the provisional recursors, each with its two
argument sums and the stream's rules.  `Refine/IndC.lean` spells the same
abstraction for the cached driver. -/
def absCheckedRecs
    (cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)) :
    List (ConLeche.ConstantVal × Nat × Nat × List ConLeche.RecRule) :=
  cs.val.map (fun c =>
    (absConstantVal c.1, c.2.1.val, c.2.2.1.val, absRecRules c.2.2.2))

/-- "the `BlockRename` dictionary `f` computes the closure `g`" — the shape
`ExprOpsMeta.rename_consts_refines` consumes, carried by every stage that
renames through the block. -/
def RenamesTo (f : inductives.modeled.BlockRename)
    (g : ConLeche.Name → ConLeche.Name) : Prop :=
  ∀ n, NameWF n → ∀ r,
    inductives.modeled.BlockRename.Insts.Con_ron_coreKernelExpr_opsNameToName.rename
        f n = ok r →
      absName r = g (absName n) ∧ NameWF r

/-- The dictionary built from a block's names computes `blockRename`. -/
theorem block_rename_renames {bn : alloc.vec.Vec name.Name} (hbn : NamesWF bn) :
    RenamesTo { block_names := bn } (blockRename (absNames bn)) :=
  block_rename_rename_refines hbn

section Stages

variable {mode : env.CheckMode} (hw : Core.Wrappers mode IndAbs.checkFuelU)
  (hcb : CheckerBaseSpec mode)

include hw hcb

/-! ## The side certificates (`Modeled.lean:31-53`) -/

/-- `ConLeche/Kernel/Inductives/Modeled.lean:31-53` — `check_iota_sides_ty`
refines `checkIotaSidesTy`: both sides of a modeled iota equation inhabit the
equation's type, and (in the TT lane) the type slot inhabits the sort the
statement's own `Eq.{ℓA}` names.  The cited function takes the constant's name
for its messages only, so the conclusion holds at *every* name. -/
theorem check_iota_sides_ty_refines
    {st st' : cached.state_c.CState} {fe_self : fenv.FEnv} {depth : Std.U64}
    {alpha_s lhs_s rhs_s : expr.Expr} {l_a : level.Level}
    (hst : StateWF st) (hfe : FEnvWF fe_self) (ha : ExprWF alpha_s)
    (hl : ExprWF lhs_s) (hr : ExprWF rhs_s) (hla : LevelWF l_a)
    (h : inductives.modeled.check_iota_sides_ty mode st fe_self depth alpha_s
        lhs_s rhs_s l_a = ok (.Ok (), st')) :
    ∀ lst lfe lcvName, StateRel st lst → FEnvRel fe_self lfe →
      ∃ lst',
        (ConLeche.checkIotaSidesTy (m := ConLeche.Cached.CheckCM) (absMode mode)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe.env depth.val
            (absExpr alpha_s) (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a)
            lcvName).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `IndAbs.ops_infer` twice, `IndAbs.ops_defeq` twice, then the `ttChecks`
  -- arm's third pair
  sorry

/-! ## The canonical iota statement (`Modeled.lean:55-149`,
`DeclCheck.lean:507-573`) -/

/-- `ConLeche/Kernel/DeclCheck.lean:512-528` — `iota_stmt_open` refines
`checkIotaThmF`'s statement head (`iotaStmtOpen`).  It touches no state, so the
conclusion is an equation in `CheckCM` at *every* state.

Deviation: the port opens the telescope with the one-pass
`checker_base::open_pis_at_fvars_f`, where the cited body writes
`openPisAtFvars`; con-leche's own `openPisAtFvarsF_eq` says the two are the
same function. -/
theorem iota_stmt_open_refines
    {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv} {cv_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {r_p cn_f j : Std.U64}
    {q : alloc.vec.Vec expr.Expr × alloc.vec.Vec expr.Expr × level.Level}
    (hrel : FEnvRel fe2 lfe) (hfe : FEnvWF fe2) (hcv : NameWF cv_name)
    (hlps : NamesWF lps)
    (h : inductives.modeled.iota_stmt_open fe2 cv_name lps r_p cn_f j
        = ok (.Ok q)) :
    (∀ lst, (iotaStmtOpen lfe (absName cv_name) (absNames lps) r_p.val cn_f.val
        j.val).run lst
          = .ok ((absExprs q.1, absExprs q.2.1, absLevel q.2.2), lst))
      ∧ ExprsWF q.1 ∧ ExprsWF q.2.1 ∧ LevelWF q.2.2 := by
  -- `iota_thm_name_refines`, the `findCv` ingredient, `openPisAtFvarsF`,
  -- `get_app_fn`/`get_app_args` and the two `isEqHead` guards
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:529-534` — `iota_lhs_prefix_ok` refines the
left side's head, arity and prefix pins (`iotaLhsPrefixOk`). -/
theorem iota_lhs_prefix_ok_refines
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name} {m_i r_p : Std.U64}
    {fvs largs : alloc.vec.Vec expr.Expr} {lhs_s : expr.Expr} {b : Bool}
    (hf : RenamesTo f g) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hfvs : ExprsWF fvs) (hlargs : ExprsWF largs) (hlhs : ExprWF lhs_s)
    (h : inductives.modeled.iota_lhs_prefix_ok f cv_name lps m_i r_p fvs lhs_s
        largs = ok b) :
    b = iotaLhsPrefixOk g (absName cv_name) (absNames lps) m_i.val r_p.val
      (absExprs fvs) (absExpr lhs_s) (absExprs largs) := by
  -- `ExprOpsSpine.get_app_fn_refines`, `Expr.beq` exactly, `take_exprs`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:556-572` — `check_iota_thm_frames` refines
`checkIotaThmFrames`: the rule's λ-domains are the public recursor prefix and
constructor field domains, the right side is definitionally the rule's applied
rhs, and both sides inhabit the equation's type slot. -/
theorem check_iota_thm_frames_refines
    {st st' : cached.state_c.CState} {fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {ty_a rhs_a lhs_s rhs_s : expr.Expr} {r_p cn_p cn_f : Std.U64}
    {cvj : env.ConstantVal} {fvs targs : alloc.vec.Vec expr.Expr}
    {l_a : level.Level}
    (hf : RenamesTo f g) (hst : StateWF st) (hfe : FEnvWF fe_self)
    (hty : ExprWF ty_a) (hcvj : ConstantValWF cvj) (hrhs : ExprWF rhs_a)
    (hfvs : ExprsWF fvs) (htargs : ExprsWF targs) (hl : ExprWF lhs_s)
    (hr : ExprWF rhs_s) (hla : LevelWF l_a)
    (h : inductives.modeled.check_iota_thm_frames mode st fe_self f ty_a r_p cvj
        cn_p cn_f rhs_a fvs targs lhs_s rhs_s l_a = ok (.Ok (), st')) :
    ∀ lst lfe lcvName, StateRel st lst → FEnvRel fe_self lfe →
      ∃ lst',
        (checkIotaThmFrames (absMode mode) lfe g lcvName (absExpr ty_a) r_p.val
            (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
            (absExprs fvs) (absExprs targs) (absExpr lhs_s) (absExpr rhs_s)
            (absLevel l_a)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- the two telescope opens, `inst_pis_at`/`inst_lams_at`, three
  -- `checkDefEqList`s, `IndAbs.ops_defeq` and `check_iota_sides_ty_refines`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:540-555` — `check_iota_thm_ctor` refines
`checkIotaThmCtor`: the constructor's telescope (renamed) instantiated at the
major's arguments gives the field domains and the canonical index tuple, both
compared definitionally; then the statement's prefix domains against the
recursor's. -/
theorem check_iota_thm_ctor_refines
    {st st' : cached.state_c.CState} {fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {ty_a rhs_a lhs_s rhs_s : expr.Expr} {m_i r_p cn_p cn_f : Std.U64}
    {cvj : env.ConstantVal}
    {fvs x_fvs largs targs : alloc.vec.Vec expr.Expr} {l_a : level.Level}
    (hf : RenamesTo f g) (hst : StateWF st) (hfe : FEnvWF fe_self)
    (hty : ExprWF ty_a) (hcvj : ConstantValWF cvj) (hrhs : ExprWF rhs_a)
    (hfvs : ExprsWF fvs) (hxfvs : ExprsWF x_fvs) (hlargs : ExprsWF largs)
    (htargs : ExprsWF targs) (hl : ExprWF lhs_s) (hr : ExprWF rhs_s)
    (hla : LevelWF l_a)
    (h : inductives.modeled.check_iota_thm_ctor mode st fe_self f ty_a m_i r_p
        cvj cn_p cn_f rhs_a fvs x_fvs largs targs lhs_s rhs_s l_a
        = ok (.Ok (), st')) :
    ∀ lst lfe lcvName, StateRel st lst → FEnvRel fe_self lfe →
      ∃ lst',
        (checkIotaThmCtor (absMode mode) lfe g lcvName (absExpr ty_a) m_i.val
            r_p.val (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
            (absExprs fvs) (absExprs x_fvs) (absExprs largs) (absExprs targs)
            (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a)).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `strip_pis`, `rename_consts`, `inst_pis_at`, two `checkDefEqList`s and
  -- `check_iota_thm_frames_refines`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:507-573` — **`check_iota_thm` refines
`checkIotaThmF`**: a canonical recursor rule's `iota_j` theorem, checked
semantically. -/
theorem check_iota_thm_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {ty_a rhs_a : expr.Expr} {m_i r_p j cn_p cn_f : Std.U64}
    {r : env.RecRule} {cvj : env.ConstantVal}
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hty : ExprWF ty_a) (hr : RecRuleWF r) (hcvj : ConstantValWF cvj)
    (hrhs : ExprWF rhs_a)
    (h : inductives.modeled.check_iota_thm mode st fe2 fe_self f cv_name lps
        ty_a m_i r_p j r cvj cn_p cn_f rhs_a = ok (.Ok (), st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 → FEnvRel fe_self lfe →
      ∃ lst',
        (ConLeche.checkIotaThmF (absMode mode)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
            (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
            j.val (absRecRule r) (absConstantVal cvj) cn_p.val cn_f.val
            (absExpr rhs_a)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `iota_stmt_open_refines`, `iota_lhs_prefix_ok_refines`, the major pin and
  -- `check_iota_thm_ctor_refines`
  sorry

/-! ## The nested-auxiliary shape (`Modeled.lean:151-190`,
`DeclCheck.lean:575-599`) -/

/-- `ConLeche/Kernel/DeclCheck.lean:585` — `lower_all` refines
`(args.take cnP).map (Expr.lowerBVars k 0)` from index `i`, accumulating on the
way in. -/
theorem lower_all_refines {k : Std.U64} {args out v : alloc.vec.Vec expr.Expr}
    {cn_p i : Std.Usize} (hargs : ExprsWF args) (hout : ExprsWF out)
    (h : inductives.modeled.lower_all k args cn_p i out = ok v) :
    absExprs v = absExprs out
        ++ (((absExprs args).take cn_p.val).drop i.val).map
            (ConLeche.Expr.lowerBVars k.val 0)
      ∧ ExprsWF v := by
  -- the index recursion on `cn_p - i`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:587` — `lift_all_0` refines
`pins.map (Expr.liftLooseBVars k 0)`, the lift-back roundtrip that certifies
that no index variable occurs in a pin. -/
theorem lift_all_0_refines {k : Std.U64} {pins out v : alloc.vec.Vec expr.Expr}
    {i : Std.Usize} (hpins : ExprsWF pins) (hout : ExprsWF out)
    (h : inductives.modeled.lift_all_0 k pins i out = ok v) :
    absExprs v = absExprs out
        ++ ((absExprs pins).drop i.val).map
            (ConLeche.Expr.liftLooseBVars k.val 0)
      ∧ ExprsWF v := by
  -- the index recursion on `pins.len() - i`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:590-591` — `pins_wf_from` refines
`nestedRuleShapeF`'s `pins.all` conjunct from index `i`: closed, bounded by the
prefix telescope, constants resolving, levels declared — the facts `EnvWF`
records for the stored rule. -/
theorem pins_wf_from_refines {fe_self : fenv.FEnv} {lfe : ConLeche.FEnv}
    {lps : alloc.vec.Vec name.Name} {r_p : Std.U64}
    {pins : alloc.vec.Vec expr.Expr} {i : Std.Usize} {b : Bool}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hrel : FEnvRel fe_self lfe) (hfe : FEnvWF fe_self) (hlps : NamesWF lps)
    (hpins : ExprsWF pins)
    (h : inductives.modeled.pins_wf_from fe_self lps r_p pins i = ok b) :
    b = ((absExprs pins).drop i.val).all (fun p =>
      !p.hasFvar && p.looseBVarsBounded r_p.val && p.constsResolveF lfe
        && p.allLevelParamsDefined (absNames lps)) := by
  -- the index recursion on `pins.len() - i`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:575-599` — `nested_rule_shape` refines
`nestedRuleShapeF`: the constructor's level and parameter instantiations, read
off the recursor type's major-premise domain, or `none` where the rule stays
inert.

Deviation: the artifact probe is `fenv::find(fe₂, iotaThmName).is_some()` where
con-leche writes `(fe'.findCV? …).isSome`; `FEnv.findCV?` is
`(fe.find? n).map (·.toConstantVal)`, so the two `Bool`s are the same. -/
theorem nested_rule_shape_refines
    {fe2 fe_self : fenv.FEnv} {lfe2 lfe : ConLeche.FEnv} {cv_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {ty_a : expr.Expr}
    {m_i r_p cn_p j : Std.U64}
    {o : Option (alloc.vec.Vec level.Level × alloc.vec.Vec expr.Expr)}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hrel2 : FEnvRel fe2 lfe2) (hfe2 : FEnvWF fe2)
    (hrel : FEnvRel fe_self lfe) (hfe : FEnvWF fe_self) (hcv : NameWF cv_name)
    (hlps : NamesWF lps) (hty : ExprWF ty_a)
    (h : inductives.modeled.nested_rule_shape fe2 fe_self cv_name lps ty_a m_i
        r_p cn_p j = ok o) :
    o.map (fun q => (absLevels q.1, absExprs q.2))
        = ConLeche.nestedRuleShapeF lfe2 lfe (absName cv_name) (absNames lps)
            (absExpr ty_a) m_i.val r_p.val cn_p.val j.val
      ∧ ∀ q, o = some q → LevelsWF q.1 ∧ ExprsWF q.2 := by
  -- `iota_thm_name_refines`, `strip_pis`, the `.forallE` read, `lower_all`,
  -- `lift_all_0`, `pins_wf_from` and `level::all_params_defined`
  sorry

/-! ## The nested iota statement (`Modeled.lean:192-317`,
`DeclCheck.lean:601-685`) -/

/-- `ConLeche/Kernel/DeclCheck.lean:627-628` — `inst_pins_renamed` refines
`pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)`. -/
theorem inst_pins_renamed_refines
    {pins pfx out v : alloc.vec.Vec expr.Expr} {r_p : Std.U64}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {i : Std.Usize} (hf : RenamesTo f g) (hpins : ExprsWF pins)
    (hpfx : ExprsWF pfx) (hout : ExprsWF out)
    (h : inductives.modeled.inst_pins_renamed pins pfx r_p f i out = ok v) :
    absExprs v = absExprs out
        ++ ((absExprs pins).drop i.val).map (fun p =>
            ConLeche.Expr.instSpine ((absExprs pfx).take r_p.val) (r_p.val - 1)
              (p.renameConsts g))
      ∧ ExprsWF v := by
  -- the index recursion on `pins.len() - i`, one `rename_consts_refines` and
  -- one `inst_spine_refines` a step
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:666-667` — `inst_pins_plain` refines
`pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p`, the *public*
spelling.

Deviation: con-leche writes one `map` whose function either renames or does
not; the port has two functions, because a single one would take the renaming
as `Option<&BlockRename>` and Aeneas rejects a nested borrow. -/
theorem inst_pins_plain_refines
    {pins pfx out v : alloc.vec.Vec expr.Expr} {r_p : Std.U64} {i : Std.Usize}
    (hpins : ExprsWF pins) (hpfx : ExprsWF pfx) (hout : ExprsWF out)
    (h : inductives.modeled.inst_pins_plain pins pfx r_p i out = ok v) :
    absExprs v = absExprs out
        ++ ((absExprs pins).drop i.val).map (fun p =>
            ConLeche.Expr.instSpine ((absExprs pfx).take r_p.val) (r_p.val - 1) p)
      ∧ ExprsWF v := by
  -- the index recursion on `pins.len() - i`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:661-684` — `check_iota_thm_n_frames`
refines `checkIotaThmNFrames`. -/
theorem check_iota_thm_n_frames_refines
    {st st' : cached.state_c.CState} {fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {ty_a rhs_a lhs_s rhs_s : expr.Expr} {r_p cn_p cn_f m_i : Std.U64}
    {cvj : env.ConstantVal} {fvs targs pins : alloc.vec.Vec expr.Expr}
    {lvls : alloc.vec.Vec level.Level} {l_a : level.Level}
    (hf : RenamesTo f g) (hst : StateWF st) (hfe : FEnvWF fe_self)
    (hty : ExprWF ty_a) (hcvj : ConstantValWF cvj) (hrhs : ExprWF rhs_a)
    (hfvs : ExprsWF fvs) (htargs : ExprsWF targs) (hl : ExprWF lhs_s)
    (hr : ExprWF rhs_s) (hla : LevelWF l_a) (hlvls : LevelsWF lvls)
    (hpins : ExprsWF pins)
    (h : inductives.modeled.check_iota_thm_n_frames mode st fe_self f ty_a r_p
        cvj cn_p cn_f rhs_a fvs targs lhs_s rhs_s l_a lvls pins m_i
        = ok (.Ok (), st')) :
    ∀ lst lfe lcvName, StateRel st lst → FEnvRel fe_self lfe →
      ∃ lst',
        (checkIotaThmNFrames (absMode mode) lfe g lcvName (absExpr ty_a) r_p.val
            (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
            (absExprs fvs) (absExprs targs) (absExpr lhs_s) (absExpr rhs_s)
            (absLevel l_a) (absLevels lvls) (absExprs pins) m_i.val).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `inst_pins_plain_refines`, `checkAnnotList`, `checkTypedList`, the two
  -- telescope opens, `IndAbs.ops_defeq` and `check_iota_sides_ty_refines`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:648-660` — `check_iota_thm_n_ctor` refines
`checkIotaThmNCtor`. -/
theorem check_iota_thm_n_ctor_refines
    {st st' : cached.state_c.CState} {fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {ty_a rhs_a lhs_s rhs_s : expr.Expr} {m_i r_p cn_p cn_f : Std.U64}
    {cvj : env.ConstantVal}
    {fvs x_fvs largs targs pins pins_f : alloc.vec.Vec expr.Expr}
    {lvls : alloc.vec.Vec level.Level} {l_a : level.Level}
    (hf : RenamesTo f g) (hst : StateWF st) (hfe : FEnvWF fe_self)
    (hty : ExprWF ty_a) (hcvj : ConstantValWF cvj) (hrhs : ExprWF rhs_a)
    (hfvs : ExprsWF fvs) (hxfvs : ExprsWF x_fvs) (hlargs : ExprsWF largs)
    (htargs : ExprsWF targs) (hl : ExprWF lhs_s) (hr : ExprWF rhs_s)
    (hla : LevelWF l_a) (hlvls : LevelsWF lvls) (hpins : ExprsWF pins)
    (hpinsf : ExprsWF pins_f)
    (h : inductives.modeled.check_iota_thm_n_ctor mode st fe_self f ty_a m_i r_p
        cvj cn_p cn_f rhs_a fvs x_fvs largs targs lhs_s rhs_s l_a lvls pins
        pins_f = ok (.Ok (), st')) :
    ∀ lst lfe lcvName, StateRel st lst → FEnvRel fe_self lfe →
      ∃ lst',
        (checkIotaThmNCtor (absMode mode) lfe g lcvName (absExpr ty_a) m_i.val
            r_p.val (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
            (absExprs fvs) (absExprs x_fvs) (absExprs largs) (absExprs targs)
            (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a) (absLevels lvls)
            (absExprs pins) (absExprs pins_f)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `instantiate_level_params`, `rename_consts`, `inst_pis_at`, two
  -- `checkDefEqList`s and `check_iota_thm_n_frames_refines`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:601-685` — **`check_iota_thm_n` refines
`checkIotaThmNF`**: the generalization of `checkIotaThmF` to rules whose
constructor parameters and levels are fixed instantiations.  A rule with no
certifiable shape is stored inert. -/
theorem check_iota_thm_n_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {ty_a rhs_a : expr.Expr} {m_i r_p j cn_p cn_f : Std.U64}
    {r : env.RecRule} {cvj : env.ConstantVal} {fire : env.RecRuleFire}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hty : ExprWF ty_a) (hrw : RecRuleWF r) (hcvj : ConstantValWF cvj)
    (hrhs : ExprWF rhs_a)
    (h : inductives.modeled.check_iota_thm_n mode st fe2 fe_self f cv_name lps
        ty_a m_i r_p j r cvj cn_p cn_f rhs_a = ok (.Ok fire, st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 → FEnvRel fe_self lfe →
      ∃ lst',
        (ConLeche.checkIotaThmNF (absMode mode)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
            (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
            j.val (absRecRule r) (absConstantVal cvj) cn_p.val cn_f.val
            (absExpr rhs_a)).run lst = .ok (absFire fire, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRuleFireWF fire := by
  -- `nested_rule_shape_refines`, `iota_stmt_open_refines`,
  -- `inst_pins_renamed_refines`, the major pin, the residual-head read and
  -- `check_iota_thm_n_ctor_refines`
  sorry

/-! ## The rules (`Modeled.lean:319-371`, `DeclCheck.lean:687-727`) -/

/-- `ConLeche/Kernel/DeclCheck.lean:713-716` — `iota_rule_stored` refines
`recRuleBits fe'.find? cvName { r with rhs := rhsA, ctorParams := cnP,
fire := fire, paramsBlind := false }`. -/
theorem iota_rule_stored_refines
    {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv} {cv_name : name.Name}
    {r r' : env.RecRule} {cn_p : Std.U64} {fire : env.RecRuleFire}
    {rhs_a : expr.Expr}
    (hrel : FEnvRel fe2 lfe) (hfe : FEnvWF fe2) (hcv : NameWF cv_name)
    (hr : RecRuleWF r) (hfire : RecRuleFireWF fire) (hrhs : ExprWF rhs_a)
    (h : inductives.modeled.iota_rule_stored fe2 cv_name r cn_p fire rhs_a
        = ok r') :
    absRecRule r' = ConLeche.recRuleBits lfe.find? (absName cv_name)
        { absRecRule r with
            rhs := absExpr rhs_a, ctorParams := cn_p.val,
            fire := absFire fire, paramsBlind := false }
      ∧ RecRuleWF r' := by
  -- `CoreKShapes.rec_rule_bits_refines` at the rebuilt record
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:706-716` — `check_iota_rule_fire` refines
`checkIotaRuleFire`: the firing-mode decision and the stored rule. -/
theorem check_iota_rule_fire_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {ty_a rhs_a : expr.Expr} {m_i r_p j cn_p cn_f : Std.U64}
    {r r' : env.RecRule} {cvj : env.ConstantVal}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hty : ExprWF ty_a) (hrw : RecRuleWF r) (hcvj : ConstantValWF cvj)
    (hrhs : ExprWF rhs_a)
    (h : inductives.modeled.check_iota_rule_fire mode st fe2 fe_self f cv_name
        lps ty_a m_i r_p j r cvj cn_p cn_f rhs_a = ok (.Ok r', st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 → FEnvRel fe_self lfe →
      ∃ lst',
        (checkIotaRuleFire (absMode mode) lfe2 lfe g (absName cv_name)
            (absNames lps) (absExpr ty_a) m_i.val r_p.val j.val (absRecRule r)
            (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)).run lst
          = .ok (absRecRule r', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRuleWF r' := by
  -- `ExprOpsSpine.rec_rule_plain_refines`, then `check_iota_thm_refines` or
  -- `check_iota_thm_n_refines`, then `iota_rule_stored_refines`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:687-716` — **`check_iota_rule` refines
`checkIotaRuleF`**: generic well-formedness of the right-hand side, then the
model's `iota_j` theorem. -/
theorem check_iota_rule_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name} {ty_a : expr.Expr}
    {m_i r_p j : Std.U64} {r r' : env.RecRule}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hty : ExprWF ty_a) (hrw : RecRuleWF r)
    (h : inductives.modeled.check_iota_rule mode st fe2 fe_self f cv_name lps
        ty_a m_i r_p j r = ok (.Ok r', st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 → FEnvRel fe_self lfe →
      ∃ lst',
        (ConLeche.checkIotaRuleF (absMode mode)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
            (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
            j.val (absRecRule r)).run lst = .ok (absRecRule r', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRuleWF r' := by
  -- `CoreKGuards.ctor_probe_refines`, the four syntactic guards,
  -- `IndAbs.ops_annotate`, `IndAbs.ops_infer` and `check_iota_rule_fire_refines`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:718-727` — `check_iota_rules` refines
`checkIotaRulesF`, the per-rule fold.  The port accumulates on the way *in*
where con-leche conses on the way out, so the accumulator is carried in
front. -/
theorem check_iota_rules_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name} {ty_a : expr.Expr}
    {m_i r_p j : Std.U64} {rules out v : alloc.vec.Vec env.RecRule}
    {i : Std.Usize}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hty : ExprWF ty_a) (hrules : RecRulesWF rules) (hout : RecRulesWF out)
    (h : inductives.modeled.check_iota_rules mode st fe2 fe_self f cv_name lps
        ty_a m_i r_p j rules i out = ok (.Ok v, st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 → FEnvRel fe_self lfe →
      ∃ lst',
        (ConLeche.checkIotaRulesF (absMode mode)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
            (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
            j.val ((absRecRules rules).drop i.val)).run lst
          = .ok ((absRecRules v).drop (absRecRules out).length, lst')
        ∧ absRecRules v
            = absRecRules out ++ (absRecRules v).drop (absRecRules out).length
        ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRulesWF v := by
  -- the index recursion over `rules`, one `check_iota_rule_refines` a step
  sorry

/-! ## The members (`Modeled.lean:373-455`, `DeclCheck.lean:487-505`) -/

/-- `ConLeche/Kernel/DeclCheck.lean:487-505` — **`check_member_val` refines
`checkMemberValF`**: `checkConstantVal`, the member may not itself be
model-shaped, and its type is the model's under the block renaming —
structurally.

Deviation: the cited type-mismatch message dumps both sides with `reprStr`;
§3.1 drops the interpolation, so only the message differs. -/
theorem check_member_val_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe2 : fenv.FEnv} {cv cv_a : env.ConstantVal}
    (hst : StateWF st) (hfe : FEnvWF fe2) (hbn : NamesWF block_names)
    (hcv : ConstantValWF cv)
    (h : inductives.modeled.check_member_val mode st block_names fe2 cv
        = ok (.Ok cv_a, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst',
        (ConLeche.checkMemberValF
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
            (absNames block_names) lfe (absConstantVal cv)).run lst
          = .ok (absConstantVal cv_a, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_a := by
  -- the `checkConstantVal` ingredient, `level::name_is_model_suffix`,
  -- `CoreKGuards.defn_probe_refines` and `rename_consts_refines` at
  -- `block_rename_renames`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:105-113` (minus the flush) — **the
`check_ind_member` stage**: one non-recursor member checked against its
`_model` counterpart and pushed with the block's capability record.
`Refine/IndC.lean`'s `check_ind_member_s_refines` composes it with
`StateC.flush_c_refines`. -/
theorem check_ind_member_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {caps : env.IndCaps} {fe2 fe' : fenv.FEnv} {ci : env.ConstantInfo}
    (hst : StateWF st) (hfe : FEnvWF fe2) (hbn : NamesWF block_names)
    (hcaps : IndCapsWF caps) (hci : ConstantInfoWF ci)
    (h : inductives.modeled.check_ind_member mode st block_names caps fe2 ci
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst' lfe',
        (checkIndMemberN (absMode mode) (absNames block_names)
            (absIndCaps caps) lfe (absConstantInfo ci)).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `Env.to_constant_val_refines`, `check_member_val_refines`, the three-arm
  -- match and `FEnv.push_refines`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:120-127` (minus the flush) — **the
`provision_recs_step` stage**: one recursor's constant checked and provisioned
rule-less on top of the previous ones. -/
theorem provision_recs_step_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe_acc : fenv.FEnv} {ci : env.ConstantInfo}
    {q : fenv.FEnv × env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule}
    (hst : StateWF st) (hfe : FEnvWF fe_acc) (hbn : NamesWF block_names)
    (hci : ConstantInfoWF ci)
    (h : inductives.modeled.provision_recs_step mode st block_names fe_acc ci
        = ok (.Ok q, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe_acc lfe →
      ∃ lst' lfe',
        (provisionRecsStepN (absMode mode) (absNames block_names) lfe
            (absConstantInfo ci)).run lst
          = .ok ((lfe', absConstantVal q.2.1, q.2.2.1.val, q.2.2.2.1.val,
              absRecRules q.2.2.2.2), lst')
        ∧ StateRel st' lst' ∧ FEnvRel q.1 lfe' ∧ StateWF st' ∧ FEnvWF q.1
        ∧ ConstantValWF q.2.1 ∧ RecRulesWF q.2.2.2.2 := by
  -- the `.recInfo` arm, `env::rec_rules_copy`, `check_member_val_refines` and
  -- `FEnv.push_refines` of the rule-less recursor
  sorry

/-- `ConLeche/Cached/CheckerC.lean:116-129` (minus the flushes) —
`provision_recs` refines `provisionRecsN`, the fold over the block's
recursors.  The port accumulates the checked recursors on the way *in* where
con-leche conses them on the way out, so the accumulator is carried in
front. -/
theorem provision_recs_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe_acc : fenv.FEnv} {recs : alloc.vec.Vec env.ConstantInfo}
    {i : Std.Usize}
    {out : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)}
    {q : fenv.FEnv × alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)}
    (hst : StateWF st) (hfe : FEnvWF fe_acc) (hbn : NamesWF block_names)
    (hrecs : ConstantInfosWF recs)
    (h : inductives.modeled.provision_recs mode st block_names fe_acc recs i out
        = ok (.Ok q, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe_acc lfe →
      ∃ lst' lfe',
        (provisionRecsN (absMode mode) (absNames block_names) lfe
            ((absConstantInfos recs).drop i.val)).run lst
          = .ok ((lfe',
              (absCheckedRecs q.2).drop (absCheckedRecs out).length), lst')
        ∧ absCheckedRecs q.2
            = absCheckedRecs out
              ++ (absCheckedRecs q.2).drop (absCheckedRecs out).length
        ∧ StateRel st' lst' ∧ FEnvRel q.1 lfe' ∧ StateWF st' ∧ FEnvWF q.1 := by
  -- the index recursion over `recs`, one `provision_recs_step_refines` a step
  sorry

/-- `ConLeche/Cached/CheckerC.lean:146-151` — **the `check_ind_recs_fold`
stage**: `checkIndRecsS`' `checked.foldlM`, every recursor's rules checked at
`envSelf` with the `env'` lookups in `env₂` and the ruled recursor pushed onto
the accumulator. -/
theorem check_ind_recs_fold_refines
    {st st' : cached.state_c.CState} {fe2 fe_self acc fe' : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {checked : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)} {i : Std.Usize}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hacc : FEnvWF acc)
    (hchecked : ∀ c ∈ checked.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2)
    (h : inductives.modeled.check_ind_recs_fold mode st fe2 fe_self f checked i
        acc = ok (.Ok fe', st')) :
    ∀ lst lfe2 lfe lacc, StateRel st lst → FEnvRel fe2 lfe2 →
      FEnvRel fe_self lfe → FEnvRel acc lacc →
      ∃ lst' lfe',
        (checkIndRecsFoldN (absMode mode) lfe2 lfe g
            ((absCheckedRecs checked).drop i.val) lacc).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- the index recursion over `checked`, one `check_iota_rules_refines` and one
  -- `FEnv.push_refines` a step
  sorry

/-- `ConLeche/Cached/CheckerC.lean:136-151` (minus every flush) —
`check_ind_recs` refines `checkIndRecsN`: the block's recursors as a *group*.

Deviation: the port takes two `fenv::dup`s, because it threads the index
linearly (task #14) where con-leche's is persistent and holds three views at
once — `env₂`, the fully provisioned `envSelf`, and the fold's accumulator.
`Refine/FEnv.lean`'s `dup_refines` is what says a dup is the same index. -/
theorem check_ind_recs_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe2 fe' : fenv.FEnv} {recs : alloc.vec.Vec env.ConstantInfo}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hst : StateWF st) (hfe : FEnvWF fe2) (hbn : NamesWF block_names)
    (hrecs : ConstantInfosWF recs)
    (h : inductives.modeled.check_ind_recs mode st block_names fe2 recs
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst' lfe',
        (checkIndRecsN (absMode mode) (absNames block_names) lfe
            (absConstantInfos recs)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- the emptiness test, `basis_pins::eq_basis_pinned`, the two `fenv::dup`s,
  -- `provision_recs_refines` and `check_ind_recs_fold_refines`
  sorry

/-! ## The projection functions (`Modeled.lean:475-584`,
`DeclCheck.lean:729-836`) -/

/-- `ConLeche/Kernel/DeclCheck.lean:729-746` — `check_proj_lookups` refines
`checkProjLookupsF`: the stored constants the projection depends on.  It
touches no state. -/
theorem check_proj_lookups_refines
    {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f i : Std.U64}
    {q : env.ConstantVal × env.ConstantVal}
    (hrel : FEnvRel fe2 lfe) (hfe : FEnvWF fe2) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : inductives.modeled.check_proj_lookups fe2 t ctor_name lps n_p n_f i
        = ok (.Ok q)) :
    (∀ lst, (ConLeche.checkProjLookupsF (m := ConLeche.Cached.CheckCM) lfe
        (absName t) (absName ctor_name) (absNames lps) n_p.val n_f.val
        i.val).run lst
          = .ok ((absConstantVal q.1, absConstantVal q.2), lst))
      ∧ ConstantValWF q.1 ∧ ConstantValWF q.2 := by
  -- `CoreKGuards.ctor_probe`/`defn_probe`, `CoreK.proj_model_name_refines`,
  -- `Env.proj_fn_name_refines` and `basis_pins::eq_basis_pinned`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:748-761` — `check_proj_ty` refines
`checkProjTyF`: the public projection type is the model's, renamed back
(pinned by the renaming roundtrip), well-formed and parameter-led. -/
theorem check_proj_ty_refines
    {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {mty pty : expr.Expr} {n_p n_f : Std.U64}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hrel : FEnvRel fe2 lfe) (hfe : FEnvWF fe2) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps) (hmty : ExprWF mty)
    (h : inductives.modeled.check_proj_ty fe2 t ctor_name lps mty n_p n_f
        = ok (.Ok pty)) :
    (∀ lst, (ConLeche.checkProjTyF (m := ConLeche.Cached.CheckCM) lfe
        (absName t) (absName ctor_name) (absNames lps) (absExpr mty) n_p.val
        n_f.val).run lst = .ok (absExpr pty, lst))
      ∧ ExprWF pty := by
  -- `rename_consts_refines` at `proj_back_rename_refines`/`proj_fwd_…`, the
  -- roundtrip `Expr.beq`, and the four syntactic guards
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:816-836` — `check_proj_iota_body` refines
`checkProjIotaBody`.

Deviation: the port decides con-leche's
`.app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC` pattern by the *spine*
(`getAppArgs.length = 3` and a one-level `.const` head) rather than by four
nested `.app` matches; `getAppFn`/`getAppArgs` decompose exactly that spine, so
the two agree on every `Expr`. -/
theorem check_proj_iota_body_refines
    {st st' : cached.state_c.CState} {fe_self : fenv.FEnv} {t : name.Name}
    {cvj tcv : env.ConstantVal} {lps : alloc.vec.Vec name.Name}
    {n_p n_f i : Std.U64} {sbody : expr.Expr}
    (hst : StateWF st) (hfe : FEnvWF fe_self) (ht : NameWF t)
    (hcvj : ConstantValWF cvj) (hlps : NamesWF lps) (htcv : ConstantValWF tcv)
    (hsb : ExprWF sbody)
    (h : inductives.modeled.check_proj_iota_body mode st fe_self t cvj lps n_p
        n_f i tcv sbody = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe_self lfe →
      ∃ lst',
        (checkProjIotaBody (absMode mode) lfe (absName t) (absConstantVal cvj)
            (absNames lps) n_p.val n_f.val i.val (absConstantVal tcv)
            (absExpr sbody)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `struct_parts::struct_ps_at`/`field_spine`, `mk_app_n`, the three pins,
  -- `open_pis_at_fvars_f` and `check_iota_sides_ty_refines`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:797-836` — **`check_proj_iota` refines
`checkProjIotaF`**: the model's `proj_i.iota` theorem pins the rule. -/
theorem check_proj_iota_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {cvj : env.ConstantVal} {n_p n_f i : Std.U64}
    (hst : StateWF st) (hfe2 : FEnvWF fe2) (hfe : FEnvWF fe_self)
    (ht : NameWF t) (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (hcvj : ConstantValWF cvj)
    (h : inductives.modeled.check_proj_iota mode st fe2 fe_self t ctor_name lps
        cvj n_p n_f i = ok (.Ok (), st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 →
      FEnvRel fe_self lfe → lfe2 = lfe →
      ∃ lst',
        (ConLeche.checkProjIotaF (absMode mode)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 (absName t)
            (absName ctor_name) (absNames lps) (absConstantVal cvj) n_p.val
            n_f.val i.val).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `proj_iota_name_refines`, `thm_probe_refines`, two `strip_pis`, the
  -- `domsMatchAux` ingredient at `dom_proj_fwd_view_refines`, then
  -- `check_proj_iota_body_refines`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:153-166` — **`check_proj_fn` refines
`checkProjFnS`**: the public projection function for field `i`, stored as a
degenerate recursor carrying one rule.  The cited stage has no flush of its
own, so this statement is against `checkProjFnS` unmodified. -/
theorem check_proj_fn_refines
    {st st' : cached.state_c.CState} {fe2 fe' : fenv.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f i : Std.U64}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hst : StateWF st) (hfe : FEnvWF fe2) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : inductives.modeled.check_proj_fn mode st fe2 t ctor_name lps n_p n_f i
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkProjFnS (absMode mode) lfe (absName t)
            (absName ctor_name) (absNames lps) n_p.val n_f.val i.val).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `check_proj_lookups_refines`, `check_proj_ty_refines`, the
  -- `checkProjShape`/`checkProjRule` ingredients, `check_proj_iota_refines`,
  -- `CoreKShapes.proj_fn_rule_refines` and `FEnv.push_refines`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:171-175` (minus the flush) — **the
`install_proj_fn_step` stage**: one projection install, skipped where the
model's projection artifact is absent. -/
theorem install_proj_fn_step_refines
    {st st' : cached.state_c.CState} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f i : Std.U64} {fe2 fe' : fenv.FEnv}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hst : StateWF st) (hfe : FEnvWF fe2) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : inductives.modeled.install_proj_fn_step mode st t ctor_name lps n_p n_f
        fe2 i = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst' lfe',
        (installProjFnStepN (absMode mode) (absName t) (absName ctor_name)
            (absNames lps) n_p.val n_f.val lfe i.val).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' := by
  -- `CoreK.proj_model_name_refines`, `FEnv.find_refines` and
  -- `check_proj_fn_refines`
  sorry

end Stages



/-! ## The capability artifacts (`Modeled.lean:586-779`,
`DeclCheck.lean:344-441`) -/

/-- `struct_parts::struct_fam` refines `structFam`, the constructor residual
`T p⃗` an index-free single-constructor family targets.  **Owned by
`Refine/IndStructParts.lean`**; named here so that `ctor_targets_fam` and
`ctor_residual_ok` keep their exact conclusions under an explicit
ingredient. -/
def StructFamRefines : Prop :=
  ∀ (t : name.Name) (lps : alloc.vec.Vec name.Name) (n_p o : Std.U64)
    (e : expr.Expr), NameWF t → NamesWF lps →
    inductives.struct_parts.struct_fam t lps n_p o = ok e →
    absExpr e = ConLeche.structFam (absName t) (absNames lps) n_p.val o.val
      ∧ ExprWF e

/-- `struct_parts`' three spine builders — `params_of` (`lps.map .param`),
`struct_proj_ps` (the parameter `bvar` spine) and `field_spine`/`struct_ps_at`
(the field and parameter spines `checkProjIota`/`checkEtaThm` write out).
**Owned by `Refine/IndStructParts.lean`.** -/
def StructSpinesRefine : Prop :=
  (∀ (lps : alloc.vec.Vec name.Name) (v : alloc.vec.Vec level.Level),
      NamesWF lps → inductives.struct_parts.params_of lps = ok v →
      absLevels v = (absNames lps).map ConLeche.Level.param ∧ LevelsWF v)
  ∧ (∀ (n_p : Std.U64) (v : alloc.vec.Vec expr.Expr),
      inductives.struct_parts.struct_proj_ps n_p = ok v →
      absExprs v
          = (List.range n_p.val).map (fun k => ConLeche.Expr.bvar (n_p.val - k))
        ∧ ExprsWF v)

/-- `ConLeche/Kernel/DeclCheck.lean:355-358` — `proj_models_at_lps_from`
refines `checkEtaThmF`'s `(List.range nF).all` conjunct from index `j`: the
projection models exist at the family's level parameters. -/
theorem proj_models_at_lps_from_refines
    {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv} {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_f j : Std.U64} {b : Bool}
    (hrel : FEnvRel fe2 lfe) (hfe : FEnvWF fe2) (ht : NameWF t)
    (hlps : NamesWF lps)
    (h : inductives.modeled.proj_models_at_lps_from fe2 t lps n_f j = ok b) :
    b = (List.range' j.val (n_f.val - j.val)).all (fun k =>
      match lfe.find? (ConLeche.projModelName (absName t) k) with
      | some (.defnInfo cvmj _ _) => cvmj.levelParams == absNames lps
      | _ => false) := by
  -- the index recursion on `n_f - j`, `CoreK.proj_model_name_refines` and
  -- `CoreKGuards.defn_probe_refines` a step
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:375-381` — `eta_projs_from` refines the
`(List.range nF).map` of the eta statement's right-hand side: each field's
projection model applied to the parameters and the subject. -/
theorem eta_projs_from_refines
    {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {ps out v : alloc.vec.Vec expr.Expr} {n_f j : Std.U64}
    (hspines : StructSpinesRefine) (ht : NameWF t) (hlps : NamesWF lps)
    (hps : ExprsWF ps) (hout : ExprsWF out)
    (h : inductives.modeled.eta_projs_from t lps ps n_f j out = ok v) :
    absExprs v = absExprs out
        ++ (List.range' j.val (n_f.val - j.val)).map (fun k =>
            ConLeche.Expr.mkAppN
              (.const (ConLeche.projModelName (absName t) k)
                ((absNames lps).map .param))
              (absExprs ps ++ [ConLeche.Expr.bvar 0]))
      ∧ ExprsWF v := by
  -- the index recursion on `n_f - j`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:373-381` — `eta_rhs` refines the eta
statement's right-hand side
`C._model p⃗ (T._model.proj_0 p⃗ x) … (T._model.proj_{nF-1} p⃗ x)`, with the
parameters at `bvar (nP - k)` and the subject at `bvar 0`. -/
theorem eta_rhs_refines
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f : Std.U64} {e : expr.Expr}
    (hspines : StructSpinesRefine) (ht : NameWF t) (hc : NameWF ctor_name)
    (hlps : NamesWF lps)
    (h : inductives.modeled.eta_rhs t ctor_name lps n_p n_f = ok e) :
    absExpr e = ConLeche.Expr.mkAppN
        (.const ((absName ctor_name).str "_model") ((absNames lps).map .param))
        (((List.range n_p.val).map fun k => ConLeche.Expr.bvar (n_p.val - k)) ++
         (List.range n_f.val).map fun j => ConLeche.Expr.mkAppN
           (.const (ConLeche.projModelName (absName t) j)
             ((absNames lps).map .param))
           (((List.range n_p.val).map fun k => ConLeche.Expr.bvar (n_p.val - k))
            ++ [ConLeche.Expr.bvar 0]))
      ∧ ExprWF e := by
  -- `struct_proj_ps`, `eta_projs_from_refines`, `model_of_refines`,
  -- `params_of` and `mk_app_n`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:359-381` — `check_eta_thm_shape` refines
`checkEtaThmShape`, the statement-shape half of `checkEtaThmF`. -/
theorem check_eta_thm_shape_refines {mode : env.CheckMode}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f : Std.U64} {tty tty_m : expr.Expr} {b : Bool}
    (hcb : CheckerBaseSpec mode) (hspines : StructSpinesRefine)
    (ht : NameWF t) (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (htty : ExprWF tty) (httym : ExprWF tty_m)
    (h : inductives.modeled.check_eta_thm_shape mode t ctor_name lps n_p n_f tty
        tty_m = ok b) :
    b = checkEtaThmShape (absMode mode) (absName t) (absName ctor_name)
      (absNames lps) n_p.val n_f.val (absExpr tty) (absExpr tty_m) := by
  -- two `strip_pis`, the `domsMatchAux` ingredient at `dom_ident_view_refines`,
  -- the subject binder's domain, the equation's four pins and `eta_rhs_refines`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:344-382` — **`check_eta_thm` refines
`checkEtaThmF`**: does the model document structural eta for this
single-constructor block?  `Bool`-valued: an absent or differently shaped
artifact just means no capability. -/
theorem check_eta_thm_refines {mode : env.CheckMode}
    {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f : Std.U64} {b : Bool}
    (hcb : CheckerBaseSpec mode) (hspines : StructSpinesRefine)
    (hrel : FEnvRel fe2 lfe) (hfe : FEnvWF fe2) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : inductives.modeled.check_eta_thm mode fe2 t ctor_name lps n_p n_f
        = ok b) :
    b = ConLeche.checkEtaThmF (absMode mode) lfe (absName t)
      (absName ctor_name) (absNames lps) n_p.val n_f.val := by
  -- `eta_thm_name_refines`, `thm_probe_refines`, the two `defn_probe`s, the
  -- `eqA` pin, `proj_models_at_lps_from_refines` and the shape half
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:403-413` — `check_unit_thm_shape` refines
`checkUnitThmShape`, the statement-shape half of `checkUnitThmF`. -/
theorem check_unit_thm_shape_refines {mode : env.CheckMode}
    {t : name.Name} {lps : alloc.vec.Vec name.Name} {n_p : Std.U64}
    {tty tty_m : expr.Expr} {b : Bool}
    (hcb : CheckerBaseSpec mode) (hspines : StructSpinesRefine)
    (ht : NameWF t) (hlps : NamesWF lps) (htty : ExprWF tty)
    (httym : ExprWF tty_m)
    (h : inductives.modeled.check_unit_thm_shape mode t lps n_p tty tty_m
        = ok b) :
    b = checkUnitThmShape (absMode mode) (absName t) (absNames lps) n_p.val
      (absExpr tty) (absExpr tty_m) := by
  -- two `strip_pis`, the `domsMatchAux` ingredient, the two subject binders'
  -- domains and the equation's four pins
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:384-414` — **`check_unit_thm` refines
`checkUnitThmF`**: does the model document unit-likeness for this block? -/
theorem check_unit_thm_refines {mode : env.CheckMode}
    {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv} {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p : Std.U64} {b : Bool}
    (hcb : CheckerBaseSpec mode) (hspines : StructSpinesRefine)
    (hrel : FEnvRel fe2 lfe) (hfe : FEnvWF fe2) (ht : NameWF t)
    (hlps : NamesWF lps)
    (h : inductives.modeled.check_unit_thm mode fe2 t lps n_p = ok b) :
    b = ConLeche.checkUnitThmF (absMode mode) lfe (absName t) (absNames lps)
      n_p.val := by
  -- `unit_thm_name_refines`, `thm_probe_refines`, the `defn_probe`, the `eqA`
  -- pin and the shape half
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:430-441` — **`ind_block_caps` refines
`indBlockCapsF`**: the capabilities recorded for a single-constructor modeled
block.  The K flag is computed from shape exactly as the official kernel does,
and the reduction site carries the semantic load, so no model theorem backs
it.

Deviation: con-leche's `(cvC.levelParams = cvT.levelParams) && checkEtaThmF …`
and `nF == 0 && piResultIsProp cvT.type` are `if`s in the port; `&&` is
already short-circuiting, so the two are the same `Bool`. -/
theorem ind_block_caps_refines {mode : env.CheckMode}
    {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv} {cv_t cv_c : env.ConstantVal}
    {n_p n_f : Std.U64} {caps : env.IndCaps}
    (hcb : CheckerBaseSpec mode) (hspines : StructSpinesRefine)
    (hrel : FEnvRel fe2 lfe) (hfe : FEnvWF fe2) (hct : ConstantValWF cv_t)
    (hcc : ConstantValWF cv_c)
    (h : inductives.modeled.ind_block_caps mode fe2 cv_t cv_c n_p n_f
        = ok caps) :
    absIndCaps caps = ConLeche.indBlockCapsF (absMode mode) lfe
        (absConstantVal cv_t) (absConstantVal cv_c) n_p.val n_f.val
      ∧ IndCapsWF caps := by
  -- `prop_when::names_beq`, `check_eta_thm_refines`, `check_unit_thm_refines`,
  -- `CoreKGuards.pi_result_is_prop_refines` and `pi_result_z_refines`
  sorry

/-- `ConLeche/Kernel/DeclCheck.lean:416-428` — **`ctor_residual_ok` refines
`ctorResidualOkF`** (task #136): an eta-capable family's constructor returns
the family applied to its parameters.  The subject is the **stored** constant —
what `checkMemberVal` stored — and the capability guard is not cosmetic.  A
TT-lane check: trivially true unless `mode.ttChecks`. -/
theorem ctor_residual_ok_refines {mode : env.CheckMode}
    {fe3 : fenv.FEnv} {lfe : ConLeche.FEnv} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f : Std.U64} {eta b : Bool}
    (hfam : StructFamRefines)
    (hrel : FEnvRel fe3 lfe) (hfe : FEnvWF fe3) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : inductives.modeled.ctor_residual_ok mode fe3 t ctor_name lps n_p n_f
        eta = ok b) :
    b = ConLeche.ctorResidualOkF (absMode mode) lfe (absName t)
      (absName ctor_name) (absNames lps) n_p.val n_f.val eta := by
  -- `env::tt_checks`, `CoreKGuards.ctor_probe_refines`,
  -- `ExprOpsSpine.strip_pis_refines`, `struct_fam` and `Expr.beq` exactly
  sorry

/-- `ConLeche/Kernel/Inductives/Modeled.lean:682-710` — **`ctor_targets_fam`
refines `ctorTargetsFam`**: official's structure-likeness, read off the block's
*incoming* constructor type (one constructor and no indices), so the decision
is a function of the block.  A gate, not a pin. -/
theorem ctor_targets_fam_refines
    {ctor_ty : expr.Expr} {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f : Std.U64} {b : Bool}
    (hfam : StructFamRefines) (hcty : ExprWF ctor_ty) (ht : NameWF t)
    (hlps : NamesWF lps)
    (h : inductives.modeled.ctor_targets_fam ctor_ty t lps n_p n_f = ok b) :
    b = ConLeche.ctorTargetsFam (absExpr ctor_ty) (absName t) (absNames lps)
      n_p.val n_f.val := by
  -- `ExprOpsSpine.strip_pis_refines`, `struct_fam` and `Expr.beq` exactly
  sorry

/-! ## The block split (`Modeled.lean:781-834`, `CheckerC.lean:233-268`) -/

/-- `ConLeche/Cached/CheckerC.lean:234-237` — `filter_recs_from` refines
`block.filter (fun ci => ci.isRecInfo == keep)` over `block[i..]`, accumulating
on the way in.  At `keep = true` it is `checkIndDeclSF`'s `recs`, at
`keep = false` its `nonrecs`. -/
theorem filter_recs_from_val (block : alloc.vec.Vec env.ConstantInfo)
    (hblock : ConstantInfosWF block) (keep : Bool) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec env.ConstantInfo),
      block.length - i.val ≤ k → ConstantInfosWF out →
      inductives.modeled.filter_recs_from block keep i out = ok v →
      absConstantInfos v = absConstantInfos out
          ++ ((absConstantInfos block).drop i.val).filter
              (fun ci => ci.isRecInfo == keep)
        ∧ ConstantInfosWF v := by
  intro k
  induction k with
  | zero =>
    intro i out v hk hout h
    rw [inductives.modeled.filter_recs_from] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac),
      Result.ok.injEq] at h
    subst h
    refine ⟨?_, hout⟩
    have hnil : (absConstantInfos block).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absConstantInfos, List.length_map]
      scalar_tac
    rw [hnil]
    simp
  | succ k ih =>
    intro i out v hk hout h
    rw [inductives.modeled.filter_recs_from] at h
    by_cases hi : i.val ≥ block.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac),
        Result.ok.injEq] at h
      subst h
      refine ⟨?_, hout⟩
      have hnil : (absConstantInfos block).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absConstantInfos, List.length_map]
        scalar_tac
      rw [hnil]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
      have hlt : i.val < block.val.length := by
        have := alloc.vec.Vec.len_val block; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨isrec, hisrec, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hciwf : ConstantInfoWF block.val[i.val] :=
        hblock _ (List.getElem_mem hlt)
      have hisrecv : isrec
          = ConLeche.ConstantInfo.isRecInfo (absConstantInfo block.val[i.val]) :=
        Env.is_rec_info_refines hisrec
      have hlt2 : i.val < (absConstantInfos block).length := by
        simpa [absConstantInfos] using hlt
      have hcons : (absConstantInfos block).drop i.val
          = absConstantInfo block.val[i.val]
            :: (absConstantInfos block).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absConstantInfos]
      have hout1v : absConstantInfos out1 = absConstantInfos out
            ++ (if isrec = keep then [absConstantInfo block.val[i.val]] else [])
          ∧ ConstantInfosWF out1 := by
        by_cases hb : isrec = keep
        · rw [if_pos hb] at hout1 ⊢
          obtain ⟨ci1, hci1, hpush⟩ := bind_eq_ok_iff.mp hout1
          have hci1e : ci1 = block.val[i.val] :=
            Env.constant_info_dup_refines hci1
          subst hci1e
          refine ⟨?_, ?_⟩
          · rw [absConstantInfos, vec_push_val hpush, List.map_append]; rfl
          · intro x hx
            rw [vec_push_val hpush, List.mem_append] at hx
            cases hx with
            | inl hx => exact hout x hx
            | inr hx => rw [List.mem_singleton.mp hx]; exact hciwf
        · rw [if_neg hb] at hout1 ⊢
          rw [Result.ok.injEq] at hout1
          subst hout1
          exact ⟨by simp, hout⟩
      obtain ⟨hout1e, hout1wf⟩ := hout1v
      obtain ⟨hrec, hrecwf⟩ := ih i2 out1 v (by scalar_tac) hout1wf h
      rw [hi2v] at hrec
      refine ⟨?_, hrecwf⟩
      rw [hrec, hout1e, hcons, List.filter_cons, ← hisrecv, List.append_assoc]
      by_cases hb : isrec = keep
      · simp [hb]
      · simp [hb]

/-- `filter_recs_from` at its own statement. -/
theorem filter_recs_from_refines {block out v : alloc.vec.Vec env.ConstantInfo}
    {keep : Bool} {i : Std.Usize} (hblock : ConstantInfosWF block)
    (hout : ConstantInfosWF out)
    (h : inductives.modeled.filter_recs_from block keep i out = ok v) :
    absConstantInfos v = absConstantInfos out
        ++ ((absConstantInfos block).drop i.val).filter
            (fun ci => ci.isRecInfo == keep)
      ∧ ConstantInfosWF v :=
  filter_recs_from_val block hblock keep block.length i out v (by scalar_tac)
    hout h

/-- `ConLeche/Cached/CheckerC.lean:234-237` — **`filter_recs` refines the
block's two filters**: `keep = true` is `recs`, `keep = false` is
`nonrecs`. -/
theorem filter_recs_refines {block v : alloc.vec.Vec env.ConstantInfo}
    {keep : Bool} (hblock : ConstantInfosWF block)
    (h : inductives.modeled.filter_recs block keep = ok v) :
    absConstantInfos v
        = (absConstantInfos block).filter (fun ci => ci.isRecInfo == keep)
      ∧ ConstantInfosWF v := by
  rw [inductives.modeled.filter_recs] at h
  have hout : ConstantInfosWF (alloc.vec.Vec.new env.ConstantInfo) := by
    intro c hc; simp [alloc.vec.Vec.new] at hc
  obtain ⟨h1, h2⟩ := filter_recs_from_refines hblock hout h
  exact ⟨by simpa [absConstantInfos, alloc.vec.Vec.new] using h1, h2⟩

/-- `ConLeche/Cached/CheckerC.lean:241` — `block_names_of_from` refines
`block.map (·.name)` over `block[i..]`, accumulating on the way in. -/
theorem block_names_of_from_val (block : alloc.vec.Vec env.ConstantInfo)
    (hblock : ConstantInfosWF block) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec name.Name),
      block.length - i.val ≤ k → NamesWF out →
      inductives.modeled.block_names_of_from block i out = ok v →
      absNames v = absNames out
          ++ ((absConstantInfos block).drop i.val).map
              ConLeche.ConstantInfo.name
        ∧ NamesWF v := by
  intro k
  induction k with
  | zero =>
    intro i out v hk hout h
    rw [inductives.modeled.block_names_of_from] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac),
      Result.ok.injEq] at h
    subst h
    refine ⟨?_, hout⟩
    have hnil : (absConstantInfos block).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absConstantInfos, List.length_map]
      scalar_tac
    rw [hnil]
    simp
  | succ k ih =>
    intro i out v hk hout h
    rw [inductives.modeled.block_names_of_from] at h
    by_cases hi : i.val ≥ block.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac),
        Result.ok.injEq] at h
      subst h
      refine ⟨?_, hout⟩
      have hnil : (absConstantInfos block).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absConstantInfos, List.length_map]
        scalar_tac
      rw [hnil]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
      have hlt : i.val < block.val.length := by
        have := alloc.vec.Vec.len_val block; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hciwf : ConstantInfoWF block.val[i.val] :=
        hblock _ (List.getElem_mem hlt)
      have hnwf : NameWF n := Env.constant_info_name_wf hciwf hn
      have hnv : absName n
          = ConLeche.ConstantInfo.name (absConstantInfo block.val[i.val]) :=
        Env.constant_info_name_refines hn
      have hout1wf : NamesWF out1 := by
        intro x hx
        rw [vec_push_val hout1, List.mem_append] at hx
        cases hx with
        | inl hx => exact hout x hx
        | inr hx => rw [List.mem_singleton.mp hx]; exact hnwf
      obtain ⟨hrec, hrecwf⟩ := ih i2 out1 v (by scalar_tac) hout1wf h
      rw [hi2v] at hrec
      have hlt2 : i.val < (absConstantInfos block).length := by
        simpa [absConstantInfos] using hlt
      have hcons : (absConstantInfos block).drop i.val
          = absConstantInfo block.val[i.val]
            :: (absConstantInfos block).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absConstantInfos]
      refine ⟨?_, hrecwf⟩
      rw [hrec, hcons, List.map_cons, absNames, vec_push_val hout1,
        List.map_append, List.append_assoc, ← hnv]
      rfl

/-- `ConLeche/Cached/CheckerC.lean:241` — **`block_names_of` refines
`block.map (·.name)`**, the block's names the renaming reads. -/
theorem block_names_of_refines {block : alloc.vec.Vec env.ConstantInfo}
    {v : alloc.vec.Vec name.Name} (hblock : ConstantInfosWF block)
    (h : inductives.modeled.block_names_of block = ok v) :
    absNames v = (absConstantInfos block).map ConLeche.ConstantInfo.name
      ∧ NamesWF v := by
  rw [inductives.modeled.block_names_of] at h
  have hout : NamesWF (alloc.vec.Vec.new name.Name) := by
    intro c hc; simp [alloc.vec.Vec.new] at hc
  obtain ⟨h1, h2⟩ :=
    block_names_of_from_val block hblock block.length 0#usize _ v
      (by scalar_tac) hout h
  exact ⟨by simpa [absNames, alloc.vec.Vec.new] using h1, h2⟩

/-- `ConLeche/Cached/CheckerC.lean:242-247` — `single_ind_ctor_from` counts the
two filters of `checkIndDeclSF`'s `match` over `block[i..]` and remembers their
first element, which is what the two one-element list patterns decide. -/
theorem single_ind_ctor_from_refines
    {block : alloc.vec.Vec env.ConstantInfo} {i : Std.Usize}
    {t : Option env.ConstantVal}
    {c : Option (env.ConstantVal × Std.U64 × Std.U64)} {n_ind n_ctor : Std.U64}
    {q : (Option env.ConstantVal) × (Option (env.ConstantVal × Std.U64 × Std.U64))
      × Std.U64 × Std.U64}
    (hblock : ConstantInfosWF block)
    (h : inductives.modeled.single_ind_ctor_from block i t c n_ind n_ctor
        = ok q) :
    q.1.map absConstantVal
        = (t.map absConstantVal).orElse (fun _ =>
            ((absConstantInfos block).drop i.val).findSome? (fun ci =>
              match ci with | .indInfo cv _ => some cv | _ => none))
      ∧ q.2.1.map (fun p => (absConstantVal p.1, p.2.1.val, p.2.2.val))
          = (c.map (fun p => (absConstantVal p.1, p.2.1.val, p.2.2.val))).orElse
              (fun _ => ((absConstantInfos block).drop i.val).findSome?
                (fun ci => match ci with
                  | .ctorInfo cv nP nF => some (cv, nP, nF) | _ => none))
      ∧ q.2.2.1.val = n_ind.val
          + (((absConstantInfos block).drop i.val).filter
              (fun ci => match ci with | .indInfo _ _ => true | _ => false)).length
      ∧ q.2.2.2.val = n_ctor.val
          + (((absConstantInfos block).drop i.val).filter
              (fun ci => match ci with
                | .ctorInfo _ _ _ => true | _ => false)).length := by
  -- the index recursion over `block`
  sorry

/-- `ConLeche/Cached/CheckerC.lean:242-247` — **`single_ind_ctor` refines
`checkIndDeclSF`'s two one-element list patterns**: the block's single type
former and single constructor, if it has exactly one of each. -/
theorem single_ind_ctor_refines {block : alloc.vec.Vec env.ConstantInfo}
    {o : Option (env.ConstantVal × env.ConstantVal × Std.U64 × Std.U64)}
    (hblock : ConstantInfosWF block)
    (h : inductives.modeled.single_ind_ctor block = ok o) :
    o.map (fun q => (absConstantVal q.1, absConstantVal q.2.1, q.2.2.1.val,
        q.2.2.2.val))
      = (match (absConstantInfos block).filter
            (fun ci => match ci with | .indInfo _ _ => true | _ => false),
          (absConstantInfos block).filter
            (fun ci => match ci with | .ctorInfo _ _ _ => true | _ => false) with
         | [.indInfo cvT _], [.ctorInfo cvC nP nF] => some (cvT, cvC, nP, nF)
         | _, _ => none) := by
  -- `single_ind_ctor_from_refines` at `i = 0`, then the two length-one reads
  sorry


end ConRon.Refine.Modeled
