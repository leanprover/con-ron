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

## Ingredients this file does not own

`kernel/checker_base.rs` (task #24's tier, unified at task #25's
`checker_local`) has no refinement file yet, and the modeled route calls nine
of its items.  Each travels as a named `Prop` in the exact-result shape, so
that the statements below keep their exact conclusions under an explicit
hypothesis and nothing is weakened — the same device `Refine/StateC.lean` uses
for `InstantiateListRefines` and `Refine/IndStructInstall.lean` for
`StructProjBodiesRefines`.

## `sorry` count

53 `sorry`s.  Every item's statement is the exact-result one of DESIGN.md §3.5
and none is weakened; what is proved outright is the name-map group (the four
dictionaries, the two slot searches, the four pinned suffix names), the small
readers, `ctor_targets_fam`, `ctor_residual_ok`, `ind_block_caps`, and the
block-split group.  The remaining `sorry`s are the `partial_fixpoint` index
recursions and the long guard nests over the knot, each noted at its site.
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


end ConRon.Refine.Modeled
