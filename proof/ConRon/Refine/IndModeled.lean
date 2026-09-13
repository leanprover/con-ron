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

Task #59 added three imports, all of them already-committed siblings and none
of them a new ingredient: `Refine/CoreKGuards.lean` (`defn_probe`/`ctor_probe`
and `defnOf`/`ctorOf`), `Refine/BasisPins.lean` (`eq_basis_pinned`) and
con-leche's own `ConLeche/Verify/FastOps.lean` (`openPisAtFvarsF_eq`, which
deviation 5 cites).

6. `inst_pins_renamed`/`inst_pins_plain` (task #59) carry one **added
   hypothesis** each, `pfx.length ≤ rP`: the walk hands `pfx` to
   `expr_ops::inst_spine` whole, and `Expr.instSpine` consumes its whole
   argument list (its `t - 1` is truncated, so an argument past index `t` is
   still instantiated at `bvar 0`).  The cited `fvs.take rP` spelling is
   therefore the port's answer exactly when `pfx` is already that prefix, and
   the statement is *false* without the bound.  Both call sites build `pfx`
   with `expr_ops::take_exprs (·) rP` (`modeled.rs:1030`, `:1248`), so the
   caller discharges it from `ExprOps.take_exprs_val`.

## `sorry` count

26 `sorry`s out of 65 lemmas (43 at task #57; task #59 closed seventeen) — one
per item that still reaches the knot, the shared checker base, or an
ingredient this file does not own.  Every item's statement is the exact-result
one of DESIGN.md §3.5 and **none is weakened**; each `sorry` carries a one-line
note naming the pieces its proof composes.

Proved outright (39).  Task #57's 22: the whole name-map group — `model_str`,
`model_of`, the four `NameToName`/`DomView` dictionaries against `blockRename`,
`projBack`, `projFwd` and `projFwd`-as-a-binder-view, `DomIdent`'s identity
view, and the two `find?` slot searches
`find_proj_model_slot`/`find_proj_fn_slot` — the four pinned suffix names
`iota_thm_name`/`proj_iota_name`/`eta_thm_name`/`unit_thm_name`, the readers
`thm_probe`/`arg_get_d`/`arg_get_last_d`, and the block split's
`filter_recs`/`block_names_of` with their index recursions.

Task #59's 17, in the order they were closed: the five index recursions
`lower_all`, `lift_all_0`, `pins_wf_from`, `inst_pins_renamed` and
`inst_pins_plain`; the two `n_f - j` recursions `eta_projs_from` and
`proj_models_at_lps_from`; the block split's `single_ind_ctor_from` and
`single_ind_ctor`; the capability artifacts `eta_rhs`, `ind_block_caps`,
`ctor_residual_ok` and `ctor_targets_fam`; the projection functions'
`check_proj_lookups` and `check_proj_ty`; and the two statement heads
`check_iota_sides_ty` (the knot's `inferType`/`isDefEq` pairs, both lanes) and
`iota_stmt_open`.

Three shapes carried the work and are worth reusing: an index recursion goes by
`induction` on a `Nat` bound with the `partial_fixpoint` equation rewritten in
each branch (`lower_all_val` is the smallest example); a `core::result`
`match` is peeled with `cases` on the `Result` and `bind_eq_ok_iff.mp` *through*
the unreduced tuple `let` — never `rw [if_pos]`, whose pattern would mention
the match's shadowed binder; and a `CheckCM` run equation is assembled by
`simp` from the operation lemmas' `.run` facts, or, when the cited body's
string interpolation gets in the way, by a local `*_run` lemma stated at the
facts the success path pins (`iotaStmtOpen_run`).
-/
import ConRon.Refine.IndAbs
import ConRon.Refine.IndSumParts
import ConRon.Refine.IndStructInstall
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.CoreKBase
import ConRon.Refine.CoreKNames
import ConRon.Refine.CoreKGuards
import ConRon.Refine.CoreKVec
import ConRon.Refine.BasisPins
import ConLeche.Verify.FastOps

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
  ∧ (∀ (m : Std.U64) (v : alloc.vec.Vec expr.Expr),
      inductives.struct_parts.field_spine m = ok v →
      absExprs v
          = (List.range m.val).map (fun j => ConLeche.Expr.bvar (m.val - 1 - j))
        ∧ ExprsWF v)

section Stages

variable {mode : env.CheckMode} (hw : Core.Wrappers mode IndAbs.checkFuelU)
  (hcb : CheckerBaseSpec mode)

include hw hcb

/-! ## The side certificates (`Modeled.lean:31-53`) -/

set_option linter.unusedSectionVars false in
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
  intro lst lfe lcvName hrel hfer
  rw [inductives.modeled.check_iota_sides_ty] at h
  simp only [IndAbs.check_fuel_eq, bind_tc_ok] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := p
  cases r with
  | Err err => simp at h
  | Ok tl =>
  obtain ⟨lst1, hrun1, hrel1, hwf1, htlwf⟩ :=
    IndAbs.ops_infer hw hst hfe hl hp lst lfe hrel hfer
  obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r2, st2⟩ := p2
  cases r2 with
  | Err err => simp at h
  | Ok b =>
  obtain ⟨lst2, hrun2, hrel2, hwf2⟩ :=
    IndAbs.ops_defeq hw hwf1 hfe htlwf ha hp2 lst1 lfe hrel1 hfer
  cases b with
  | false => simp at h
  | true =>
  obtain ⟨p3, hp3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r3, st3⟩ := p3
  cases r3 with
  | Err err => simp at h
  | Ok tr =>
  obtain ⟨lst3, hrun3, hrel3, hwf3, htrwf⟩ :=
    IndAbs.ops_infer hw hwf2 hfe hr hp3 lst2 lfe hrel2 hfer
  obtain ⟨p4, hp4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r4, st4⟩ := p4
  cases r4 with
  | Err err => simp at h
  | Ok b1 =>
  obtain ⟨lst4, hrun4, hrel4, hwf4⟩ :=
    IndAbs.ops_defeq hw hwf3 hfe htrwf ha hp4 lst3 lfe hrel3 hfer
  cases b1 with
  | false => simp at h
  | true =>
  obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
  have hb2v : b2 = (absMode mode).ttChecks := Env.tt_checks_refines hb2
  have henv : absEnv fe_self.env = lfe.env := hfer.1
  rw [henv] at hrun1 hrun2 hrun3 hrun4
  cases hb2t : b2 with
  | false =>
    rw [hb2t] at h hb2v
    rw [if_neg (by simp), Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨lst4, ?_, hrel4, hwf4⟩
    simp only [StateT.run] at hrun1 hrun2 hrun3 hrun4
    rw [ConLeche.checkIotaSidesTy]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hrun2, hrun3, hrun4, ← hb2v]
  | true =>
  rw [hb2t] at h hb2v
  obtain ⟨p5, hp5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r5, st5⟩ := p5
  cases r5 with
  | Err err => simp at h
  | Ok talpha =>
  obtain ⟨lst5, hrun5, hrel5, hwf5, htawf⟩ :=
    IndAbs.ops_infer hw hwf4 hfe ha hp5 lst4 lfe hrel4 hfer
  rw [henv] at hrun5
  obtain ⟨l, hlq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨srt, hsrt, h⟩ := bind_eq_ok_iff.mp h
  have hlv : l = l_a := by
    rw [level_dup_eq] at hlq; exact (Result.ok_injective hlq).symm
  have hsrtv : absExpr srt = ConLeche.Expr.sort (absLevel l_a) := by
    rw [Expr.sort_refines hsrt, hlv]
  have hsrtwf : ExprWF srt := ExprWF.sort (by rw [hlv]; exact hla) hsrt
  obtain ⟨p6, hp6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r6, st6⟩ := p6
  cases r6 with
  | Err err => simp at h
  | Ok b3 =>
  obtain ⟨lst6, hrun6, hrel6, hwf6⟩ :=
    IndAbs.ops_defeq hw hwf5 hfe htawf hsrtwf hp6 lst5 lfe hrel5 hfer
  rw [henv, hsrtv] at hrun6
  cases b3 with
  | false => simp at h
  | true =>
  have h6 : (ok (core.result.Result.Ok (), st6)
      : Result ((core.result.Result Unit core_types.CheckError)
        × cached.state_c.CState)) = ok (.Ok (), st') := h
  rw [Result.ok.injEq, Prod.mk.injEq] at h6
  obtain ⟨-, rfl⟩ := h6
  refine ⟨lst6, ?_, hrel6, hwf6⟩
  simp only [StateT.run] at hrun1 hrun2 hrun3 hrun4 hrun5 hrun6
  rw [ConLeche.checkIotaSidesTy]
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, hrun1, hrun2, hrun3, hrun4, hrun5, hrun6,
    ← hb2v]

/-! ## The canonical iota statement (`Modeled.lean:55-149`,
`DeclCheck.lean:507-573`) -/

omit hw hcb in
/-- `iotaStmtOpen`'s run, at the five facts the port's success path pins. -/
theorem iotaStmtOpen_run {lfe : ConLeche.FEnv} {cvName : ConLeche.Name}
    {lps : List ConLeche.Name} {rP cnF j : Nat} {cvt : ConLeche.ConstantVal}
    {fvs : List ConLeche.Expr} {tb : ConLeche.Expr}
    {lst : ConLeche.Cached.CState}
    (h1 : lfe.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (h2 : cvt.levelParams = lps)
    (h3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (h4 : ConLeche.isEqHead tb.getAppFn = true)
    (h5 : tb.getAppArgs.length = 3) :
    (iotaStmtOpen lfe cvName lps rP cnF j).run lst
      = .ok ((fvs, tb.getAppArgs, ConLeche.eqHeadLevel tb.getAppFn), lst) := by
  rw [iotaStmtOpen, h1]
  simp [ConLeche.unwrapOr, h2, h3, h4, h5, StateT.run, Bind.bind,
    StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]

set_option linter.unusedSectionVars false in
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
  rw [inductives.modeled.iota_stmt_open] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnv, hnwf⟩ := iota_thm_name_refines hcv hn
  obtain ⟨hoabs, howf⟩ := hcb.findCv fe2 lfe n o hrel hfe hnwf ho
  rw [hnv] at hoabs
  cases o with
  | none => simp at h
  | some cvt =>
  have hcvtwf : ConstantValWF cvt := howf cvt rfl
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = decide (absNames cvt.level_params = absNames lps) :=
    Env.names_beq_refines hcvtwf.2.1 hlps hb
  cases b with
  | false => simp at h
  | true =>
  have hlpseq : (absConstantVal cvt).levelParams = absNames lps := by
    simpa [absConstantVal] using (of_decide_eq_true hbv.symm)
  obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  have hkv : k.val = r_p.val + cn_f.val := HashMap.uscalar_add_eq hk
  obtain ⟨ho1abs, ho1wf⟩ := hcb.openPisAtFvarsF k cvt.ty 0#u64 o1 hcvtwf.2.2 ho1
  rw [hkv, show ((0#u64 : Std.U64)).val = 0 from rfl,
    ConLeche.openPisAtFvarsF_eq] at ho1abs
  cases o1 with
  | none => simp at h
  | some z =>
  obtain ⟨fvs, tb⟩ := z
  obtain ⟨hfvswf, htbwf⟩ := ho1wf _ rfl
  simp only [Option.map_some] at ho1abs
  obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨targs, htargs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hheadv, hheadwf⟩ := ExprOps.get_app_fn_refines htbwf hhead
  obtain ⟨htargsv, htargswf⟩ := ExprOps.get_app_args_refines htbwf htargs
  have hb1v : b1 = ConLeche.isEqHead (absExpr head) :=
    hcb.isEqHead head b1 hheadwf hb1
  cases b1 with
  | false => simp at h
  | true =>
  by_cases hlen : (alloc.vec.Vec.len targs) != 3#usize
  · rw [if_pos hlen] at h; simp at h
  · rw [if_neg hlen] at h
    obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hlv, hlwf⟩ := hcb.eqHeadLevel head l hheadwf hl
    rw [Result.ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    have hlenv : (ConLeche.Expr.getAppArgs (absExpr tb)).length = 3 := by
      rw [← htargsv]
      simp only [absExprs, List.length_map]
      have := alloc.vec.Vec.len_val targs
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
      scalar_tac
    simp only [Option.map_some] at hoabs
    rw [show ("iota_" ++ toString j.val)
        = (toString "iota_" ++ toString j.val) from rfl] at hoabs
    refine ⟨?_, hfvswf, htargswf, hlwf⟩
    intro lst
    rw [show absExpr cvt.ty = (absConstantVal cvt).type from rfl] at ho1abs
    have h4 : ConLeche.isEqHead (absExpr tb).getAppFn = true := by
      rw [← hheadv]; exact hb1v.symm
    rw [iotaStmtOpen_run hoabs.symm hlpseq ho1abs.symm h4 hlenv, ← htargsv,
      ← hheadv, ← hlv]

set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:529-534` — `iota_lhs_prefix_ok` refines the
left side's head, arity and prefix pins (`iotaLhsPrefixOk`).

`hrp` (added at task #59, the sanctioned `Refine/Scalars.lean` case): the two
`take_exprs` calls index at `rP as usize`, and Aeneas models that cast as
`rP.val % 2 ^ Usize.numBits`, so on a 32-bit target with `rP.val > Usize.max`
the port takes a *wrapped* prefix where the cited `largs.take rP` takes the
whole list — the statement is false without the bound.  Callers have it:
`fvs` is `openPisAtFvars rP tyA 0`, whose length is `rP`, so
`Scalars.u64_le_usize_max_of_le_len` discharges it. -/
theorem iota_lhs_prefix_ok_refines
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name} {m_i r_p : Std.U64}
    {fvs largs : alloc.vec.Vec expr.Expr} {lhs_s : expr.Expr} {b : Bool}
    (hspines : StructSpinesRefine)
    (hf : RenamesTo f g) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hfvs : ExprsWF fvs) (hlargs : ExprsWF largs) (hlhs : ExprWF lhs_s)
    (hrp : r_p.val ≤ Std.Usize.max)
    (h : inductives.modeled.iota_lhs_prefix_ok f cv_name lps m_i r_p fvs lhs_s
        largs = ok b) :
    b = iotaLhsPrefixOk g (absName cv_name) (absNames lps) m_i.val r_p.val
      (absExprs fvs) (absExpr lhs_s) (absExprs largs) := by
  rw [inductives.modeled.iota_lhs_prefix_ok] at h
  obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨expected, hexp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hheadv, hheadwf⟩ := ExprOps.get_app_fn_refines hlhs hhead
  obtain ⟨hnmv, hnmwf⟩ := hf cv_name hcv nm hnm
  obtain ⟨husv, huswf⟩ := hspines.1 lps us hlps hus
  have hexpv : absExpr expected
      = ConLeche.Expr.const (g (absName cv_name))
          ((absNames lps).map ConLeche.Level.param) := by
    rw [Expr.mk_const_refines hexp, hnmv, husv]
  have hexpwf : ExprWF expected := ExprWF.mk_const hnmwf huswf hexp
  have hb0v : b0 = decide (absExpr head = absExpr expected) :=
    Expr.beq_refines hheadwf hexpwf hb0
  rw [iotaLhsPrefixOk, ← hheadv, ← hexpv,
    show ((absExpr head == absExpr expected) : Bool) = b0 by
      rw [hb0v, Bool.eq_iff_iff]; simp]
  by_cases hb0t : b0 = true
  · rw [if_pos hb0t] at h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    simp only [lift_eq, Result.ok.injEq] at hi1
    subst hi1
    have hi1v : (Std.UScalar.cast .U64 (alloc.vec.Vec.len largs) : Std.U64).val
        = largs.val.length := by
      rw [ExprOps.usize_cast_u64_val]
      have := alloc.vec.Vec.len_val largs
      scalar_tac
    have hi2v : i2.val = m_i.val + 1 := HashMap.uscalar_add_eq hi2
    have hlenv : (absExprs largs).length = largs.val.length := by
      simp [absExprs]
    by_cases hne :
        (Std.UScalar.cast .U64 (alloc.vec.Vec.len largs) : Std.U64) != i2
    · rw [if_pos hne, Result.ok.injEq] at h
      rw [← h, hb0t]
      simp only [bne_iff_ne, ne_eq] at hne
      rw [show (((absExprs largs).length == m_i.val + 1) : Bool) = false by
        simp only [beq_eq_false_iff_ne, ne_eq, hlenv]
        intro hc; exact hne (by scalar_tac)]
      simp
    · rw [if_neg hne] at h
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
      rw [show (((absExprs largs).length == m_i.val + 1) : Bool) = true by
        rw [hlenv, ← hi1v, hne, hi2v]; simp]
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
      simp only [lift_eq, Result.ok.injEq] at hi3 hi4
      have hcast : (Std.UScalar.cast .Usize r_p : Std.Usize).val = r_p.val :=
        ExprOps.u64_cast_usize_val hrp
      obtain ⟨hv1v, hv1wf⟩ := ExprOps.take_exprs_refines hlargs hv1
      obtain ⟨hv2v, hv2wf⟩ := ExprOps.take_exprs_refines hfvs hv2
      rw [← hi3, hcast] at hv1v
      rw [← hi4, hcast] at hv2v
      rw [Env.exprs_beq_refines hv1wf hv2wf h, hv1v, hv2v, hb0t,
        Bool.eq_iff_iff]
      simp
  · simp only [Bool.not_eq_true] at hb0t
    rw [if_neg (by simp [hb0t]), Result.ok.injEq] at h
    rw [← h, hb0t]
    simp

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

omit hw hcb in
/-- `lower_all`'s index recursion on `args.len() - i`, in the shape the
`partial_fixpoint` equation is usable in. -/
theorem lower_all_val (k : Std.U64) (args : alloc.vec.Vec expr.Expr)
    (hargs : ExprsWF args) (cn_p : Std.Usize) :
    ∀ n : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec expr.Expr),
      args.length - i.val ≤ n → ExprsWF out →
      inductives.modeled.lower_all k args cn_p i out = ok v →
      absExprs v = absExprs out
          ++ (((absExprs args).take cn_p.val).drop i.val).map
              (ConLeche.Expr.lowerBVars k.val 0)
        ∧ ExprsWF v := by
  intro n
  induction n with
  | zero =>
    intro i out v hk hout h
    rw [inductives.modeled.lower_all] at h
    have hnil : ((absExprs args).take cn_p.val).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absExprs, List.length_take, List.length_map]
      have := alloc.vec.Vec.len_val args
      scalar_tac
    split at h
    · rw [Result.ok.injEq] at h; subst h
      exact ⟨by rw [hnil]; simp, hout⟩
    · rw [if_pos (show i ≥ alloc.vec.Vec.len args by
        have := alloc.vec.Vec.len_val args; scalar_tac), Result.ok.injEq] at h
      subst h
      exact ⟨by rw [hnil]; simp, hout⟩
  | succ n ih =>
    intro i out v hk hout h
    rw [inductives.modeled.lower_all] at h
    by_cases hcp : i.val ≥ cn_p.val
    · rw [if_pos (show i ≥ cn_p by scalar_tac), Result.ok.injEq] at h
      subst h
      have hnil : ((absExprs args).take cn_p.val).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absExprs, List.length_take, List.length_map]
        scalar_tac
      exact ⟨by rw [hnil]; simp, hout⟩
    · rw [if_neg (show ¬ i ≥ cn_p by scalar_tac)] at h
      by_cases hi : i.val ≥ args.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len args by
          have := alloc.vec.Vec.len_val args; scalar_tac), Result.ok.injEq] at h
        subst h
        have hnil : ((absExprs args).take cn_p.val).drop i.val = [] := by
          apply List.drop_eq_nil_of_le
          simp only [absExprs, List.length_take, List.length_map]
          scalar_tac
        exact ⟨by rw [hnil]; simp, hout⟩
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len args by
          have := alloc.vec.Vec.len_val args; scalar_tac)] at h
        have hlt : i.val < args.val.length := by
          have := alloc.vec.Vec.len_val args; scalar_tac
        obtain ⟨y, hy, hyv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec args i hlt)
        subst hyv
        simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
        obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hewf : ExprWF args.val[i.val] := hargs _ (List.getElem_mem hlt)
        obtain ⟨he1v, he1wf⟩ := ExprOps.lower_bvars_refines hewf he1
        have hout1wf : ExprsWF out1 := by
          intro x hx
          rw [vec_push_val hout1, List.mem_append] at hx
          cases hx with
          | inl hx => exact hout x hx
          | inr hx => rw [List.mem_singleton.mp hx]; exact he1wf
        obtain ⟨hrec, hrecwf⟩ := ih i2 out1 v (by scalar_tac) hout1wf h
        rw [hi2v] at hrec
        have hlt2 : i.val < ((absExprs args).take cn_p.val).length := by
          simp only [absExprs, List.length_take, List.length_map]
          scalar_tac
        have hcons : ((absExprs args).take cn_p.val).drop i.val
            = absExpr args.val[i.val]
              :: ((absExprs args).take cn_p.val).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons hlt2]
          congr 1
          simp [absExprs]
        refine ⟨?_, hrecwf⟩
        rw [hrec, hcons, List.map_cons, absExprs, vec_push_val hout1,
          List.map_append, List.append_assoc]
        simp [absExprs, he1v]

set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:585` — `lower_all` refines
`(args.take cnP).map (Expr.lowerBVars k 0)` from index `i`, accumulating on the
way in.  (The knot hypotheses stay on the statement even though the walk does
not reach the core, so that the section's shape is uniform.) -/
theorem lower_all_refines {k : Std.U64} {args out v : alloc.vec.Vec expr.Expr}
    {cn_p i : Std.Usize} (hargs : ExprsWF args) (hout : ExprsWF out)
    (h : inductives.modeled.lower_all k args cn_p i out = ok v) :
    absExprs v = absExprs out
        ++ (((absExprs args).take cn_p.val).drop i.val).map
            (ConLeche.Expr.lowerBVars k.val 0)
      ∧ ExprsWF v :=
  lower_all_val k args hargs cn_p args.length i out v (by scalar_tac) hout h

omit hw hcb in
/-- `lift_all_0`'s index recursion on `pins.len() - i`. -/
theorem lift_all_0_val (k : Std.U64) (pins : alloc.vec.Vec expr.Expr)
    (hpins : ExprsWF pins) :
    ∀ n : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec expr.Expr),
      pins.length - i.val ≤ n → ExprsWF out →
      inductives.modeled.lift_all_0 k pins i out = ok v →
      absExprs v = absExprs out
          ++ ((absExprs pins).drop i.val).map
              (ConLeche.Expr.liftLooseBVars k.val 0)
        ∧ ExprsWF v := by
  intro n
  induction n with
  | zero =>
    intro i out v hk hout h
    rw [inductives.modeled.lift_all_0] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len pins by
      have := alloc.vec.Vec.len_val pins; scalar_tac), Result.ok.injEq] at h
    subst h
    have hnil : (absExprs pins).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absExprs, List.length_map]
      scalar_tac
    exact ⟨by rw [hnil]; simp, hout⟩
  | succ n ih =>
    intro i out v hk hout h
    rw [inductives.modeled.lift_all_0] at h
    by_cases hi : i.val ≥ pins.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len pins by
        have := alloc.vec.Vec.len_val pins; scalar_tac), Result.ok.injEq] at h
      subst h
      have hnil : (absExprs pins).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absExprs, List.length_map]
        scalar_tac
      exact ⟨by rw [hnil]; simp, hout⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len pins by
        have := alloc.vec.Vec.len_val pins; scalar_tac)] at h
      have hlt : i.val < pins.val.length := by
        have := alloc.vec.Vec.len_val pins; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec pins i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hewf : ExprWF pins.val[i.val] := hpins _ (List.getElem_mem hlt)
      obtain ⟨he1v, he1wf⟩ := ExprOps.lift_loose_bvars_refines hewf he1
      have hout1wf : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hout1, List.mem_append] at hx
        cases hx with
        | inl hx => exact hout x hx
        | inr hx => rw [List.mem_singleton.mp hx]; exact he1wf
      obtain ⟨hrec, hrecwf⟩ := ih i2 out1 v (by scalar_tac) hout1wf h
      rw [hi2v] at hrec
      have hlt2 : i.val < (absExprs pins).length := by
        simpa [absExprs] using hlt
      have hcons : (absExprs pins).drop i.val
          = absExpr pins.val[i.val] :: (absExprs pins).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absExprs]
      refine ⟨?_, hrecwf⟩
      rw [hrec, hcons, List.map_cons, absExprs, vec_push_val hout1,
        List.map_append, List.append_assoc]
      simp [absExprs, he1v]

set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:587` — `lift_all_0` refines
`pins.map (Expr.liftLooseBVars k 0)`, the lift-back roundtrip that certifies
that no index variable occurs in a pin. -/
theorem lift_all_0_refines {k : Std.U64} {pins out v : alloc.vec.Vec expr.Expr}
    {i : Std.Usize} (hpins : ExprsWF pins) (hout : ExprsWF out)
    (h : inductives.modeled.lift_all_0 k pins i out = ok v) :
    absExprs v = absExprs out
        ++ ((absExprs pins).drop i.val).map
            (ConLeche.Expr.liftLooseBVars k.val 0)
      ∧ ExprsWF v :=
  lift_all_0_val k pins hpins pins.length i out v (by scalar_tac) hout h

omit hw hcb in
/-- `pins_wf_from`'s index recursion on `pins.len() - i`. -/
theorem pins_wf_from_val {fe_self : fenv.FEnv} {lfe : ConLeche.FEnv}
    {lps : alloc.vec.Vec name.Name} {r_p : Std.U64}
    {pins : alloc.vec.Vec expr.Expr}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hrel : FEnvRel fe_self lfe) (hfe : FEnvWF fe_self) (hlps : NamesWF lps)
    (hpins : ExprsWF pins) :
    ∀ n : Nat, ∀ (i : Std.Usize) (b : Bool),
      pins.length - i.val ≤ n →
      inductives.modeled.pins_wf_from fe_self lps r_p pins i = ok b →
      b = ((absExprs pins).drop i.val).all (fun p =>
        !p.hasFvar && p.looseBVarsBounded r_p.val && p.constsResolveF lfe
          && p.allLevelParamsDefined (absNames lps)) := by
  intro n
  induction n with
  | zero =>
    intro i b hk h
    rw [inductives.modeled.pins_wf_from] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len pins by
      have := alloc.vec.Vec.len_val pins; scalar_tac), Result.ok.injEq] at h
    subst h
    have hnil : (absExprs pins).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absExprs, List.length_map]
      scalar_tac
    rw [hnil]; simp
  | succ n ih =>
    intro i b hk h
    rw [inductives.modeled.pins_wf_from] at h
    by_cases hi : i.val ≥ pins.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len pins by
        have := alloc.vec.Vec.len_val pins; scalar_tac), Result.ok.injEq] at h
      subst h
      have hnil : (absExprs pins).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absExprs, List.length_map]
        scalar_tac
      rw [hnil]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len pins by
        have := alloc.vec.Vec.len_val pins; scalar_tac)] at h
      have hlt : i.val < pins.val.length := by
        have := alloc.vec.Vec.len_val pins; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec pins i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      have hewf : ExprWF pins.val[i.val] := hpins _ (List.getElem_mem hlt)
      have hlt2 : i.val < (absExprs pins).length := by
        simpa [absExprs] using hlt
      have hcons : (absExprs pins).drop i.val
          = absExpr pins.val[i.val] :: (absExprs pins).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absExprs]
      rw [hcons, List.all_cons]
      obtain ⟨bf, hbf, h⟩ := bind_eq_ok_iff.mp h
      have hbfv : bf = (absExpr pins.val[i.val]).hasFvar :=
        ExprOps.has_fvar_refines hewf hbf
      by_cases hbf1 : bf = true
      · rw [if_pos hbf1, Result.ok.injEq] at h
        subst h
        rw [hbf1] at hbfv
        simp [← hbfv]
      · rw [if_neg hbf1] at h
        simp only [Bool.not_eq_true] at hbf1
        rw [hbf1] at hbfv
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1v : b1 = (absExpr pins.val[i.val]).looseBVarsBounded r_p.val :=
          ExprOps.loose_bvars_bounded_refines hewf hb1
        by_cases hb1t : b1 = true
        · rw [if_pos hb1t] at h
          rw [hb1t] at hb1v
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2v : b2 = (absExpr pins.val[i.val]).constsResolveF lfe :=
            hres fe_self lfe _ b2 hrel hfe hewf hb2
          by_cases hb2t : b2 = true
          · rw [if_pos hb2t] at h
            rw [hb2t] at hb2v
            obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
            have hb3v : b3
                = (absExpr pins.val[i.val]).allLevelParamsDefined
                    (absNames lps) :=
              ExprOps.all_level_params_defined_fast_refines hlps hewf hb3
            by_cases hb3t : b3 = true
            · rw [if_pos hb3t] at h
              rw [hb3t] at hb3v
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
              have := ih i2 b (by scalar_tac) h
              rw [hi2v] at this
              rw [this, ← hbfv, ← hb1v, ← hb2v, ← hb3v]
              simp
            · simp only [Bool.not_eq_true] at hb3t
              rw [if_neg (by simp [hb3t]), Result.ok.injEq] at h
              subst h
              rw [hb3t] at hb3v
              simp [← hb3v]
          · simp only [Bool.not_eq_true] at hb2t
            rw [if_neg (by simp [hb2t]), Result.ok.injEq] at h
            subst h
            rw [hb2t] at hb2v
            simp [← hb2v]
        · simp only [Bool.not_eq_true] at hb1t
          rw [if_neg (by simp [hb1t]), Result.ok.injEq] at h
          subst h
          rw [hb1t] at hb1v
          simp [← hb1v]

set_option linter.unusedSectionVars false in
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
        && p.allLevelParamsDefined (absNames lps)) :=
  pins_wf_from_val hres hrel hfe hlps hpins pins.length i b (by scalar_tac) h

/-- `ConLeche/Kernel/DeclCheck.lean:575-599` — `nested_rule_shape` refines
`nestedRuleShapeF`: the constructor's level and parameter instantiations, read
off the recursor type's major-premise domain, or `none` where the rule stays
inert.

Deviation: the artifact probe is `fenv::find(fe₂, iotaThmName).is_some()` where
con-leche writes `(fe'.findCV? …).isSome`; `FEnv.findCV?` is
`(fe.find? n).map (·.toConstantVal)`, so the two `Bool`s are the same.

`hcnp` (added at task #59, the sanctioned `Refine/Scalars.lean` case): the
three `cn_p as usize` casts are `cn_p.val % 2 ^ Usize.numBits`, so without the
bound a 32-bit target splits the argument list at a wrapped index where the
cited `args.take cnP`/`args.drop cnP` do not.  The caller has it — `cnP` is the
constructor's stored parameter count. -/
theorem nested_rule_shape_refines
    {fe2 fe_self : fenv.FEnv} {lfe2 lfe : ConLeche.FEnv} {cv_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {ty_a : expr.Expr}
    {m_i r_p cn_p j : Std.U64}
    {o : Option (alloc.vec.Vec level.Level × alloc.vec.Vec expr.Expr)}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    (hrel2 : FEnvRel fe2 lfe2) (hfe2 : FEnvWF fe2)
    (hrel : FEnvRel fe_self lfe) (hfe : FEnvWF fe_self) (hcv : NameWF cv_name)
    (hlps : NamesWF lps) (hty : ExprWF ty_a) (hcnp : cn_p.val ≤ Std.Usize.max)
    (h : inductives.modeled.nested_rule_shape fe2 fe_self cv_name lps ty_a m_i
        r_p cn_p j = ok o) :
    o.map (fun q => (absLevels q.1, absExprs q.2))
        = ConLeche.nestedRuleShapeF lfe2 lfe (absName cv_name) (absNames lps)
            (absExpr ty_a) m_i.val r_p.val cn_p.val j.val
      ∧ ∀ q, o = some q → LevelsWF q.1 ∧ ExprsWF q.2 := by
  rw [inductives.modeled.nested_rule_shape] at h
  obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨oc, hoc, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnmv, hnmwf⟩ := iota_thm_name_refines hcv hnm
  have hocabs := FEnv.find_refines hrel2 hfe2 hnmwf hoc
  rw [hnmv, show ("iota_" ++ toString j.val)
      = (toString "iota_" ++ toString j.val) from rfl] at hocabs
  have hsome : (core.option.Option.is_some oc)
      = (lfe2.findCV? (((absName cv_name).str "_model").str
          (toString "iota_" ++ toString j.val))).isSome := by
    rw [ConLeche.FEnv.findCV?, ← hocabs]
    cases oc <;> rfl
  obtain ⟨gate, hgate, h⟩ := bind_eq_ok_iff.mp h
  have hgatev : gate = ((lfe2.findCV? (((absName cv_name).str "_model").str
        (toString "iota_" ++ toString j.val))).isSome
      && decide (r_p.val ≤ m_i.val)) := by
    by_cases hs : (core.option.Option.is_some oc) = true
    · rw [if_pos hs, Result.ok.injEq] at hgate
      rw [hs] at hsome
      rw [← hgate, ← hsome]
      simp only [Bool.true_and, decide_eq_decide]
      constructor <;> intro hc <;> scalar_tac
    · simp only [Bool.not_eq_true] at hs
      rw [if_neg (by rw [hs]; simp), Result.ok.injEq] at hgate
      rw [hs] at hsome
      rw [← hgate, ← hsome]
      simp
  have hnew : absExprs (alloc.vec.Vec.new expr.Expr) = [] := by
    simp [absExprs, alloc.vec.Vec.new]
  rw [ConLeche.nestedRuleShapeF]
  by_cases hgt : gate = true
  case neg =>
    simp only [Bool.not_eq_true] at hgt
    rw [if_neg (by simp [hgt]), Result.ok.injEq] at h
    rw [hgt] at hgatev
    rw [if_neg (by
      have hg := hgatev.symm
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hg
      rcases hg with h' | h'
      · intro hc; rw [hc.1] at h'; simp at h'
      · intro hc; exact h' hc.2)]
    rw [← h]
    simp
  rw [if_pos hgt] at h
  rw [hgt] at hgatev
  rw [if_pos (by
    have hg := hgatev.symm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg)]
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_pis_refines hty ho1
  cases o1 with
  | none =>
    simp only [Option.map_none] at ho1abs
    rw [← ho1abs]
    simp only [Result.ok.injEq] at h
    rw [← h]
    simp
  | some tq =>
  obtain ⟨tbs, e⟩ := tq
  obtain ⟨htbswf, hewf⟩ := ho1wf _ rfl
  simp only [Option.map_some] at ho1abs
  rw [← ho1abs]
  obtain ⟨en, hen, h⟩ := bind_eq_ok_iff.mp h
  rw [arc_deref_eq, Result.ok.injEq] at hen
  subst hen
  obtain ⟨⟨d, k⟩⟩ := e
  cases k
  case ForallE =>
    obtain ⟨hdomwf, -, -⟩ := CoreK.ExprWF.forallE_children hewf rfl
    simp only [ExprOps.node_kind] at h
    obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hheadv, hheadwf⟩ := ExprOps.get_app_fn_refines hdomwf hhead
    obtain ⟨en1, hen1, h⟩ := bind_eq_ok_iff.mp h
    rw [arc_deref_eq, Result.ok.injEq] at hen1
    subst hen1
    obtain ⟨⟨d1, k1⟩⟩ := head
    simp only [absExpr_mk, absExprKind]
    rw [← hheadv]
    cases k1
    case Const =>
      obtain ⟨-, hlvlswf⟩ := CoreK.ExprWF.const_children hheadwf rfl
      simp only [ExprOps.node_kind] at h
      simp only [absExpr_mk, absExprKind]
      obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hargsv, hargswf⟩ := ExprOps.get_app_args_refines hdomwf hargs
      rw [← hargsv]
      obtain ⟨kk, hkk, h⟩ := bind_eq_ok_iff.mp h
      have hkkv : kk.val = m_i.val - r_p.val := HashMap.uscalar_sub_eq hkk
      obtain ⟨ii, hii, h⟩ := bind_eq_ok_iff.mp h
      simp only [lift_eq, Result.ok.injEq] at hii
      have hcast : (Std.UScalar.cast .Usize cn_p : Std.Usize).val = cn_p.val :=
        ExprOps.u64_cast_usize_val hcnp
      obtain ⟨pins, hpins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hpinsv, hpinswf⟩ :=
        lower_all_refines hw hcb hargswf ExprOps.exprsWF_new hpins
      rw [← hii, hcast, show ((0#usize : Std.Usize)).val = 0 from rfl,
        List.drop_zero, hkkv, hnew, List.nil_append] at hpinsv
      rw [← hpinsv]
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      simp only [lift_eq, Result.ok.injEq] at hi2
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      have hi3v : i3.val = cn_p.val + kk.val := HashMap.uscalar_add_eq hi3
      have hi2v : i2.val = args.val.length := by
        rw [← hi2, ExprOps.usize_cast_u64_val]
        have := alloc.vec.Vec.len_val args
        scalar_tac
      have hargslen : (absExprs args).length = args.val.length := by
        simp [absExprs]
      by_cases hne : i2 != i3
      · rw [if_pos hne, Result.ok.injEq] at h
        simp only [bne_iff_ne, ne_eq] at hne
        rw [if_neg (by
          rintro ⟨hA, -⟩
          rw [hargslen, ← hkkv] at hA
          exact hne (by scalar_tac)), ← h]
        simp
      · rw [if_neg hne] at h
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
        have hA : (absExprs args).length = cn_p.val + (m_i.val - r_p.val) := by
          rw [hargslen, ← hi2v, hne, hi3v, hkkv]
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        simp only [lift_eq, Result.ok.injEq] at hi4
        obtain ⟨hvv, hvwf⟩ := ExprOps.take_exprs_refines hargswf hv
        obtain ⟨hv1v, hv1wf⟩ :=
          lift_all_0_refines hw hcb hpinswf ExprOps.exprsWF_new hv1
        rw [← hi4, hcast] at hvv
        rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero,
          hkkv, hnew, List.nil_append] at hv1v
        have hb1v : b1 = decide (absExprs v = absExprs v1) :=
          Env.exprs_beq_refines hvwf hv1wf hb1
        rw [hvv, hv1v] at hb1v
        by_cases hb1t : b1 = true
        · rw [if_pos hb1t] at h
          rw [hb1t] at hb1v
          have hB : (((absExprs args).take cn_p.val ==
              (absExprs pins).map
                (ConLeche.Expr.liftLooseBVars (m_i.val - r_p.val) 0)) : Bool)
              = true := by
            rw [Bool.eq_iff_iff]
            simp only [beq_iff_eq, iff_true]
            exact of_decide_eq_true hb1v.symm
          obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v3, hv3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          simp only [lift_eq, Result.ok.injEq] at hi5
          obtain ⟨hv2v, hv2wf⟩ := CoreK.drop_exprs_refines hargswf hv2
          obtain ⟨hv3v, hv3wf⟩ := hspines.2.2 kk v3 hv3
          rw [← hi5, hcast] at hv2v
          rw [hkkv] at hv3v
          have hb2v : b2 = decide (absExprs v2 = absExprs v3) :=
            Env.exprs_beq_refines hv2wf hv3wf hb2
          rw [hv2v, hv3v] at hb2v
          by_cases hb2t : b2 = true
          · rw [if_pos hb2t] at h
            rw [hb2t] at hb2v
            have hC : (((absExprs args).drop cn_p.val ==
                (List.range (m_i.val - r_p.val)).map
                  (fun i => ConLeche.Expr.bvar
                    (m_i.val - r_p.val - 1 - i))) : Bool) = true := by
              rw [Bool.eq_iff_iff]
              simp only [beq_iff_eq, iff_true]
              exact of_decide_eq_true hb2v.symm
            obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
            have hb3v :=
              pins_wf_from_refines hw hcb hres hrel hfe hlps hpinswf hb3
            rw [show ((0#usize : Std.Usize)).val = 0 from rfl,
              List.drop_zero] at hb3v
            by_cases hb3t : b3 = true
            · rw [if_pos hb3t] at h
              rw [hb3t] at hb3v
              obtain ⟨v4, hv4, h⟩ := bind_eq_ok_iff.mp h
              rw [arc_deref_eq, Result.ok.injEq] at hv4
              subst hv4
              obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
              have hb4v := ExprOps.levels_all_params_defined_refines hlps
                hlvlswf _ 0#usize b4 le_rfl hb4
              rw [show ((0#usize : Std.Usize)).val = 0 from rfl,
                List.drop_zero] at hb4v
              by_cases hb4t : b4 = true
              · rw [if_pos hb4t] at h
                rw [hb4t] at hb4v
                obtain ⟨v5, hv5, h⟩ := bind_eq_ok_iff.mp h
                have hv5e := Env.levels_copy_refines hv5
                rw [Result.ok.injEq] at h
                subst h
                rw [if_pos ⟨hA, hB, hC, hb3v.symm, hb4v.symm⟩]
                refine ⟨?_, ?_⟩
                · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
                    hv5e]
                  exact ⟨rfl, rfl⟩
                · intro q hq
                  rw [Option.some.injEq] at hq
                  subst hq
                  exact ⟨by rw [hv5e]; exact hlvlswf, hpinswf⟩
              · simp only [Bool.not_eq_true] at hb4t
                rw [if_neg (by simp [hb4t]), Result.ok.injEq] at h
                rw [hb4t] at hb4v
                rw [if_neg (by
                  rintro ⟨-, -, -, -, hE⟩
                  rw [← hb4v] at hE
                  simp at hE), ← h]
                simp
            · simp only [Bool.not_eq_true] at hb3t
              rw [if_neg (by simp [hb3t]), Result.ok.injEq] at h
              rw [hb3t] at hb3v
              rw [if_neg (by
                rintro ⟨-, -, -, hD, -⟩
                rw [← hb3v] at hD
                simp at hD), ← h]
              simp
          · simp only [Bool.not_eq_true] at hb2t
            rw [if_neg (by simp [hb2t]), Result.ok.injEq] at h
            rw [hb2t] at hb2v
            rw [if_neg (by
              rintro ⟨-, -, hC, -, -⟩
              simp only [beq_iff_eq] at hC
              rw [hC] at hb2v
              simp at hb2v), ← h]
            simp
        · simp only [Bool.not_eq_true] at hb1t
          rw [if_neg (by simp [hb1t]), Result.ok.injEq] at h
          rw [hb1t] at hb1v
          rw [if_neg (by
            rintro ⟨-, hB, -, -, -⟩
            simp only [beq_iff_eq] at hB
            rw [hB] at hb1v
            simp at hb1v), ← h]
          simp
    all_goals
      simp only [ExprOps.node_kind] at h
      simp only [Result.ok.injEq] at h
      rw [← h]
      simp
  all_goals
    simp only [ExprOps.node_kind] at h
    simp only [Result.ok.injEq] at h
    rw [← h]
    simp


/-! ## The nested iota statement (`Modeled.lean:192-317`,
`DeclCheck.lean:601-685`) -/

omit hw hcb in
/-- `inst_pins_renamed`'s index recursion on `pins.len() - i`. -/
theorem inst_pins_renamed_val {pins pfx : alloc.vec.Vec expr.Expr}
    {r_p : Std.U64} {f : inductives.modeled.BlockRename}
    {g : ConLeche.Name → ConLeche.Name} (hf : RenamesTo f g)
    (hpins : ExprsWF pins) (hpfx : ExprsWF pfx) (hlen : pfx.length ≤ r_p.val) :
    ∀ n : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec expr.Expr),
      pins.length - i.val ≤ n → ExprsWF out →
      inductives.modeled.inst_pins_renamed pins pfx r_p f i out = ok v →
      absExprs v = absExprs out
          ++ ((absExprs pins).drop i.val).map (fun p =>
              ConLeche.Expr.instSpine ((absExprs pfx).take r_p.val)
                (r_p.val - 1) (p.renameConsts g))
        ∧ ExprsWF v := by
  have htake : List.take r_p.val (List.map absExpr pfx.val)
      = List.map absExpr pfx.val := by
    apply List.take_of_length_le
    simpa using hlen
  intro n
  induction n with
  | zero =>
    intro i out v hk hout h
    rw [inductives.modeled.inst_pins_renamed] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len pins by
      have := alloc.vec.Vec.len_val pins; scalar_tac), Result.ok.injEq] at h
    subst h
    have hnil : (absExprs pins).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absExprs, List.length_map]
      scalar_tac
    exact ⟨by rw [hnil]; simp, hout⟩
  | succ n ih =>
    intro i out v hk hout h
    rw [inductives.modeled.inst_pins_renamed] at h
    by_cases hi : i.val ≥ pins.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len pins by
        have := alloc.vec.Vec.len_val pins; scalar_tac), Result.ok.injEq] at h
      subst h
      have hnil : (absExprs pins).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absExprs, List.length_map]
        scalar_tac
      exact ⟨by rw [hnil]; simp, hout⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len pins by
        have := alloc.vec.Vec.len_val pins; scalar_tac)] at h
      have hlt : i.val < pins.val.length := by
        have := alloc.vec.Vec.len_val pins; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec pins i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      have hi3v : i3.val = i.val + 1 := HashMap.uscalar_add_eq hi3
      have hewf : ExprWF pins.val[i.val] := hpins _ (List.getElem_mem hlt)
      obtain ⟨hpv, hpwf⟩ :=
        ExprOps.rename_consts_refines
          (inst := inductives.modeled.BlockRename.Insts.Con_ron_coreKernelExpr_opsNameToName)
          (f := f) g hf hewf hp
      have htv : t.val = r_p.val - 1 := by
        rw [ExprOps.sub_nat_val ht]; scalar_tac
      obtain ⟨he1v, he1wf⟩ := ExprOps.inst_spine_refines hpwf hpfx he1
      have hout1wf : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hout1, List.mem_append] at hx
        cases hx with
        | inl hx => exact hout x hx
        | inr hx => rw [List.mem_singleton.mp hx]; exact he1wf
      obtain ⟨hrec, hrecwf⟩ := ih i3 out1 v (by scalar_tac) hout1wf h
      rw [hi3v] at hrec
      have hlt2 : i.val < (absExprs pins).length := by
        simpa [absExprs] using hlt
      have hcons : (absExprs pins).drop i.val
          = absExpr pins.val[i.val] :: (absExprs pins).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absExprs]
      refine ⟨?_, hrecwf⟩
      rw [hrec, hcons, List.map_cons, absExprs, vec_push_val hout1,
        List.map_append, List.append_assoc]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        he1v, hpv, htv, htake, absExprs]

set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:627-628` — `inst_pins_renamed` refines
`pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)`.

`hlen` (added at task #59): the walk passes `pfx` to `expr_ops::inst_spine`
whole, and `Expr.instSpine` consumes its whole argument list (`t - 1` is
truncated), so the cited `fvs.take rP` spelling is the port's answer only when
`pfx` is already that prefix.  Both call sites build it with
`expr_ops::take_exprs (·) rP` (`modeled.rs:1030`, `:1248`), so the caller
discharges `hlen` from `ExprOps.take_exprs_val`. -/
theorem inst_pins_renamed_refines
    {pins pfx out v : alloc.vec.Vec expr.Expr} {r_p : Std.U64}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {i : Std.Usize} (hf : RenamesTo f g) (hpins : ExprsWF pins)
    (hpfx : ExprsWF pfx) (hout : ExprsWF out) (hlen : pfx.length ≤ r_p.val)
    (h : inductives.modeled.inst_pins_renamed pins pfx r_p f i out = ok v) :
    absExprs v = absExprs out
        ++ ((absExprs pins).drop i.val).map (fun p =>
            ConLeche.Expr.instSpine ((absExprs pfx).take r_p.val) (r_p.val - 1)
              (p.renameConsts g))
      ∧ ExprsWF v :=
  inst_pins_renamed_val hf hpins hpfx hlen pins.length i out v (by scalar_tac)
    hout h

omit hw hcb in
/-- `inst_pins_plain`'s index recursion on `pins.len() - i`. -/
theorem inst_pins_plain_val {pins pfx : alloc.vec.Vec expr.Expr} {r_p : Std.U64}
    (hpins : ExprsWF pins) (hpfx : ExprsWF pfx) (hlen : pfx.length ≤ r_p.val) :
    ∀ n : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec expr.Expr),
      pins.length - i.val ≤ n → ExprsWF out →
      inductives.modeled.inst_pins_plain pins pfx r_p i out = ok v →
      absExprs v = absExprs out
          ++ ((absExprs pins).drop i.val).map (fun p =>
              ConLeche.Expr.instSpine ((absExprs pfx).take r_p.val)
                (r_p.val - 1) p)
        ∧ ExprsWF v := by
  have htake : List.take r_p.val (List.map absExpr pfx.val)
      = List.map absExpr pfx.val := by
    apply List.take_of_length_le
    simpa using hlen
  intro n
  induction n with
  | zero =>
    intro i out v hk hout h
    rw [inductives.modeled.inst_pins_plain] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len pins by
      have := alloc.vec.Vec.len_val pins; scalar_tac), Result.ok.injEq] at h
    subst h
    have hnil : (absExprs pins).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absExprs, List.length_map]
      scalar_tac
    exact ⟨by rw [hnil]; simp, hout⟩
  | succ n ih =>
    intro i out v hk hout h
    rw [inductives.modeled.inst_pins_plain] at h
    by_cases hi : i.val ≥ pins.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len pins by
        have := alloc.vec.Vec.len_val pins; scalar_tac), Result.ok.injEq] at h
      subst h
      have hnil : (absExprs pins).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absExprs, List.length_map]
        scalar_tac
      exact ⟨by rw [hnil]; simp, hout⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len pins by
        have := alloc.vec.Vec.len_val pins; scalar_tac)] at h
      have hlt : i.val < pins.val.length := by
        have := alloc.vec.Vec.len_val pins; scalar_tac
      obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec pins i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      have hi3v : i3.val = i.val + 1 := HashMap.uscalar_add_eq hi3
      have hewf : ExprWF pins.val[i.val] := hpins _ (List.getElem_mem hlt)
      have htv : t.val = r_p.val - 1 := by
        rw [ExprOps.sub_nat_val ht]; scalar_tac
      obtain ⟨he1v, he1wf⟩ := ExprOps.inst_spine_refines hewf hpfx he1
      have hout1wf : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hout1, List.mem_append] at hx
        cases hx with
        | inl hx => exact hout x hx
        | inr hx => rw [List.mem_singleton.mp hx]; exact he1wf
      obtain ⟨hrec, hrecwf⟩ := ih i3 out1 v (by scalar_tac) hout1wf h
      rw [hi3v] at hrec
      have hlt2 : i.val < (absExprs pins).length := by
        simpa [absExprs] using hlt
      have hcons : (absExprs pins).drop i.val
          = absExpr pins.val[i.val] :: (absExprs pins).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absExprs]
      refine ⟨?_, hrecwf⟩
      rw [hrec, hcons, List.map_cons, absExprs, vec_push_val hout1,
        List.map_append, List.append_assoc]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        he1v, htv, htake, absExprs]

set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:666-667` — `inst_pins_plain` refines
`pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p`, the *public*
spelling.

Deviation: con-leche writes one `map` whose function either renames or does
not; the port has two functions, because a single one would take the renaming
as `Option<&BlockRename>` and Aeneas rejects a nested borrow.

`hlen` (added at task #59): as in `inst_pins_renamed_refines` — `inst_spine`
gets `pfx` whole and `Expr.instSpine` consumes its whole list, so the cited
`fvsP.take rP` spelling is the port's answer exactly when `pfx` is already that
prefix; the one call site builds it with `expr_ops::take_exprs (·) rP`
(`modeled.rs:1248`). -/
theorem inst_pins_plain_refines
    {pins pfx out v : alloc.vec.Vec expr.Expr} {r_p : Std.U64} {i : Std.Usize}
    (hpins : ExprsWF pins) (hpfx : ExprsWF pfx) (hout : ExprsWF out)
    (hlen : pfx.length ≤ r_p.val)
    (h : inductives.modeled.inst_pins_plain pins pfx r_p i out = ok v) :
    absExprs v = absExprs out
        ++ ((absExprs pins).drop i.val).map (fun p =>
            ConLeche.Expr.instSpine ((absExprs pfx).take r_p.val) (r_p.val - 1) p)
      ∧ ExprsWF v :=
  inst_pins_plain_val hpins hpfx hlen pins.length i out v (by scalar_tac) hout h

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

omit hw hcb in
/-- `CoreK.ctorOf`'s inversion: a `some` answer pins the stored constant. -/
theorem ctorOf_inv {X : Option ConLeche.ConstantInfo}
    {cv : ConLeche.ConstantVal} {nP nF : Nat}
    (h : CoreK.ctorOf X = some (cv, nP, nF)) :
    X = some (.ctorInfo cv nP nF) := by
  cases X with
  | none => simp [CoreK.ctorOf] at h
  | some ci => cases ci <;> simp_all [CoreK.ctorOf]

omit hw hcb in
/-- `CoreK.defnOf`'s inversion: a `some` answer pins the stored constant. -/
theorem defnOf_inv {X : Option ConLeche.ConstantInfo}
    {cv : ConLeche.ConstantVal} {v : ConLeche.Expr}
    {hint : ConLeche.ReducibilityHint}
    (h : CoreK.defnOf X = some (cv, v, hint)) :
    X = some (.defnInfo cv v hint) := by
  cases X with
  | none => simp [CoreK.defnOf] at h
  | some ci => cases ci <;> simp_all [CoreK.defnOf]

set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:729-746` — `check_proj_lookups` refines
`checkProjLookupsF`: the stored constants the projection depends on.  It
touches no state, and so needs neither the knot nor the checker base; the two
stay on the statement so that the section's shape is uniform. -/
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
  rw [inductives.modeled.check_proj_lookups] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ :=
    CoreK.ctor_probe_refines (FindAgree.of_rel hrel hfe) (FindWF.of_wf hfe) hc ho
  cases o with
  | none => simp at h
  | some cq =>
    obtain ⟨cv, np1, nf1⟩ := cq
    have hcvwf : ConstantValWF cv := howf cv np1 nf1 rfl
    have hfindc : lfe.find? (absName ctor_name)
        = some (.ctorInfo (absConstantVal cv) np1.val nf1.val) :=
      ctorOf_inv (by simpa using hoabs.symm)
    simp at h
    by_cases hnp : np1.val = n_p.val
    · rw [if_pos hnp] at h
      by_cases hnf : nf1.val = n_f.val
      · rw [if_pos hnf] at h
        obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hnmv, hnmwf⟩ := CoreK.proj_model_name_refines ht hnm
        obtain ⟨ho1abs, ho1wf⟩ :=
          CoreK.defn_probe_refines (FindAgree.of_rel hrel hfe) (FindWF.of_wf hfe)
            hnmwf ho1
        rw [hnmv] at ho1abs
        cases o1 with
        | none => simp at h
        | some dq =>
          obtain ⟨mcv, mv, mhint⟩ := dq
          have hmcvwf : ConstantValWF mcv := (ho1wf mcv mv mhint rfl).1
          have hfindm : lfe.find? (ConLeche.projModelName (absName t) i.val)
              = some (.defnInfo (absConstantVal mcv) (absExpr mv)
                  (absHint mhint)) :=
            defnOf_inv (by simpa using ho1abs.symm)
          simp at h
          obtain ⟨hb, n1, hn1, o2, ho2, h⟩ := h
          have hbv : (true : Bool)
              = decide (absNames mcv.level_params = absNames lps) :=
            Env.names_beq_refines hmcvwf.2.1 hlps hb
          have hlpseq : (absConstantVal mcv).levelParams = absNames lps := by
            simpa [absConstantVal] using (of_decide_eq_true hbv.symm)
          have hn1v : absName n1 = ConLeche.projFnName (absName t) i.val :=
            Env.proj_fn_name_refines hn1
          have hn1wf : NameWF n1 := Env.proj_fn_name_wf ht hn1
          have ho2abs := find_refines hrel hfe hn1wf ho2
          rw [hn1v] at ho2abs
          cases o2 with
          | some ci2 => simp at h
          | none =>
            simp only [Option.map_none] at ho2abs
            simp at h
            obtain ⟨o3, ho3, h⟩ := h
            have ho3abs := find_refines hrel hfe ht ho3
            cases o3 with
            | none => simp at h
            | some ci3 =>
              simp only [Option.map_some] at ho3abs
              simp at h
              obtain ⟨hb3, h⟩ := h
              have hb3v := BasisPins.eq_basis_pinned_refines hrel hfe hb3
              have heqpin : lfe.find? ConLeche.eqName = some ConLeche.eqA :=
                of_decide_eq_true hb3v.symm
              subst h
              refine ⟨?_, hcvwf, hmcvwf⟩
              intro lst
              rw [ConLeche.checkProjLookupsF, hfindc]
              simp [hnp, hnf, hfindm, hlpseq, ← ho2abs, ← ho3abs, heqpin]
              rfl
      · rw [if_neg hnf] at h; simp at h
    · rw [if_neg hnp] at h; simp at h

set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:748-761` — `check_proj_ty` refines
`checkProjTyF`: the public projection type is the model's, renamed back
(pinned by the renaming roundtrip), well-formed and parameter-led.  It is
purely syntactic: the knot and the checker base stay on the statement only so
that the section's shape is uniform. -/
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
  rw [inductives.modeled.check_proj_ty] at h
  obtain ⟨pty0, hpty0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨round, hround, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpv, hpwf⟩ :=
    ExprOps.rename_consts_refines _ (proj_back_rename_refines ht hc) hmty hpty0
  obtain ⟨hrv, hrwf⟩ :=
    ExprOps.rename_consts_refines _ (proj_fwd_rename_refines ht hc) hpwf hround
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = decide (absExpr round = absExpr mty) :=
    Expr.beq_refines hrwf hmty hb
  by_cases hbt : b = true
  · rw [if_pos hbt] at h
    rw [hbt] at hbv
    have hround' : (absExpr pty0).renameConsts
        (ConLeche.projFwd (absName t) (absName ctor_name) n_f.val)
        = absExpr mty := by
      rw [← hrv]; exact of_decide_eq_true hbv.symm
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = (absExpr pty0).constsResolveF lfe :=
      hres fe2 lfe pty0 b1 hrel hfe hpwf hb1
    by_cases hb1t : b1 = true
    · rw [if_pos hb1t] at h
      rw [hb1t] at hb1v
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2v : b2 = (absExpr pty0).looseBVarsBounded 0 :=
        ExprOps.loose_bvars_bounded_refines hpwf hb2
      obtain ⟨wf, hwf, h⟩ := bind_eq_ok_iff.mp h
      have hwfv : wf = ((absExpr pty0).looseBVarsBounded 0
          && !(absExpr pty0).hasFvar
          && (absExpr pty0).allLevelParamsDefined (absNames lps)) := by
        by_cases hb2t : b2 = true
        · rw [if_pos hb2t] at hwf
          rw [hb2t] at hb2v
          obtain ⟨b3, hb3, hwf⟩ := bind_eq_ok_iff.mp hwf
          have hb3v : b3 = (absExpr pty0).hasFvar :=
            ExprOps.has_fvar_refines hpwf hb3
          by_cases hb3t : b3 = true
          · rw [if_pos hb3t, Result.ok.injEq] at hwf
            rw [hb3t] at hb3v
            rw [← hwf, ← hb2v, ← hb3v]; simp
          · simp only [Bool.not_eq_true] at hb3t
            rw [if_neg (by simp [hb3t])] at hwf
            rw [hb3t] at hb3v
            rw [ExprOps.all_level_params_defined_fast_refines hlps hpwf hwf,
              ← hb2v, ← hb3v]
            simp
        · simp only [Bool.not_eq_true] at hb2t
          rw [if_neg (by simp [hb2t]), Result.ok.injEq] at hwf
          rw [hb2t] at hb2v
          rw [← hwf, ← hb2v]; simp
      by_cases hwft : wf = true
      · rw [if_pos hwft] at h
        rw [hwft] at hwfv
        obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
        have hkv : k.val = n_p.val + 1 := HashMap.uscalar_add_eq hk
        obtain ⟨hoabs, -⟩ := ExprOps.strip_pis_refines hpwf ho
        rw [hkv] at hoabs
        cases o with
        | none =>
          simp at h
        | some z =>
          rw [if_neg (show ¬ (core.option.Option.is_none (some z)) = true from
            by simp [core.option.Option.is_none]), Result.ok.injEq,
            core.result.Result.Ok.injEq] at h

          subst h
          refine ⟨?_, hpwf⟩
          have hres1 : (absExpr pty0).constsResolveF lfe = true := hb1v.symm
          have hwf3 : ((absExpr pty0).looseBVarsBounded 0) = true
              ∧ ((absExpr pty0).hasFvar) = false
              ∧ ((absExpr pty0).allLevelParamsDefined (absNames lps)) = true := by
            revert hwfv
            cases (absExpr pty0).looseBVarsBounded 0 <;>
              cases (absExpr pty0).hasFvar <;>
              cases (absExpr pty0).allLevelParamsDefined (absNames lps) <;> simp
          intro lst
          rw [ConLeche.checkProjTyF, ← hpv]
          simp only [Option.map_some] at hoabs
          simp [hround', hres1, hwf3.1, hwf3.2.1, hwf3.2.2, ← hoabs]
          rfl
      · simp only [Bool.not_eq_true] at hwft
        rw [if_neg (by simp [hwft])] at h; simp at h
    · simp only [Bool.not_eq_true] at hb1t
      rw [if_neg (by simp [hb1t])] at h; simp at h
  · simp only [Bool.not_eq_true] at hbt
    rw [if_neg (by simp [hbt])] at h; simp at h

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

/-- The `defnInfo` match of `checkEtaThmF`'s conjunct, read through
`CoreK.defnOf` — which is the shape `CoreK.defn_probe_refines` hands over. -/
theorem defn_lps_match_step (x : Option ConLeche.ConstantInfo)
    (lps : List ConLeche.Name) :
    (match x with
     | some (.defnInfo cvmj _ _) => cvmj.levelParams == lps
     | _ => false)
      = (match CoreK.defnOf x with
         | some (cv, _, _) => cv.levelParams == lps
         | none => false) := by
  cases x with
  | none => rfl
  | some ci => cases ci <;> rfl

/-- `proj_models_at_lps_from`'s index recursion on `n_f - j`. -/
theorem proj_models_at_lps_from_val {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv}
    {t : name.Name} {lps : alloc.vec.Vec name.Name}
    (hfa : FindAgree fe2 lfe) (hfw : FindWF fe2) (ht : NameWF t)
    (hlps : NamesWF lps) :
    ∀ N : Nat, ∀ (n_f j : Std.U64) (b : Bool), n_f.val - j.val ≤ N →
      inductives.modeled.proj_models_at_lps_from fe2 t lps n_f j = ok b →
      b = (List.range' j.val (n_f.val - j.val)).all (fun k =>
        match lfe.find? (ConLeche.projModelName (absName t) k) with
        | some (.defnInfo cvmj _ _) => cvmj.levelParams == absNames lps
        | _ => false) := by
  intro N
  induction N with
  | zero =>
    intro n_f j b hk h
    rw [inductives.modeled.proj_models_at_lps_from,
      if_pos (show j ≥ n_f by scalar_tac), Result.ok.injEq] at h
    rw [← h, show n_f.val - j.val = 0 by omega]
    rfl
  | succ N ih =>
    intro n_f j b hk h
    rw [inductives.modeled.proj_models_at_lps_from] at h
    by_cases hj : j.val ≥ n_f.val
    · rw [if_pos (show j ≥ n_f by scalar_tac), Result.ok.injEq] at h
      rw [← h, show n_f.val - j.val = 0 by omega]
      rfl
    · rw [if_neg (show ¬ j ≥ n_f by scalar_tac)] at h
      obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hnmv, hnmwf⟩ := CoreK.proj_model_name_refines ht hnm
      obtain ⟨hoabs, howf⟩ := CoreK.defn_probe_refines hfa hfw hnmwf ho
      rw [hnmv] at hoabs
      have hrange : List.range' j.val (n_f.val - j.val)
          = j.val :: List.range' (j.val + 1) (n_f.val - (j.val + 1)) := by
        rw [show n_f.val - j.val = (n_f.val - (j.val + 1)) + 1 by omega]
        rfl
      rw [hrange, List.all_cons, defn_lps_match_step, ← hoabs]
      cases o with
      | none =>
        simp only [Result.ok.injEq] at h
        rw [← h]; simp
      | some p =>
        obtain ⟨cvmj, v0, hint0⟩ := p
        have hcvwf : ConstantValWF cvmj := (howf cvmj v0 hint0 rfl).1
        simp only [] at h
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1v : b1 = ((absConstantVal cvmj).levelParams == absNames lps) := by
          rw [Env.names_beq_refines hcvwf.2.1 hlps hb1, Bool.eq_iff_iff]
          simp [absConstantVal]
        simp only [Option.map_some]
        refine CoreK.and_step hb1v h ?_
        intro c1 h1
        obtain ⟨j2, hj2, hrec⟩ := bind_eq_ok_iff.mp h1
        have hj2val : j2.val = j.val + 1 := HashMap.uscalar_add_eq hj2
        rw [ih n_f j2 c1 (by scalar_tac) hrec, hj2val]

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
      | _ => false) :=
  proj_models_at_lps_from_val (FindAgree.of_rel hrel hfe) (FindWF.of_wf hfe) ht
    hlps (n_f.val - j.val) n_f j b le_rfl h

/-- `eta_projs_from`'s index recursion on `n_f - j`. -/
theorem eta_projs_from_val {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {ps : alloc.vec.Vec expr.Expr} {n_f : Std.U64}
    (hspines : StructSpinesRefine) (ht : NameWF t) (hlps : NamesWF lps)
    (hps : ExprsWF ps) :
    ∀ n : Nat, ∀ (j : Std.U64) (out v : alloc.vec.Vec expr.Expr),
      n_f.val - j.val ≤ n → ExprsWF out →
      inductives.modeled.eta_projs_from t lps ps n_f j out = ok v →
      absExprs v = absExprs out
          ++ (List.range' j.val (n_f.val - j.val)).map (fun k =>
              ConLeche.Expr.mkAppN
                (.const (ConLeche.projModelName (absName t) k)
                  ((absNames lps).map .param))
                (absExprs ps ++ [ConLeche.Expr.bvar 0]))
        ∧ ExprsWF v := by
  intro n
  induction n with
  | zero =>
    intro j out v hk hout h
    rw [inductives.modeled.eta_projs_from,
      if_pos (show j ≥ n_f by scalar_tac), Result.ok.injEq] at h
    subst h
    refine ⟨?_, hout⟩
    rw [show n_f.val - j.val = 0 by omega]
    simp
  | succ n ih =>
    intro j out v hk hout h
    rw [inductives.modeled.eta_projs_from] at h
    by_cases hj : j.val ≥ n_f.val
    · rw [if_pos (show j ≥ n_f by scalar_tac), Result.ok.injEq] at h
      subst h
      refine ⟨?_, hout⟩
      rw [show n_f.val - j.val = 0 by omega]
      simp
    · rw [if_neg (show ¬ j ≥ n_f by scalar_tac)] at h
      obtain ⟨pargs, hpargs, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨pargs1, hpargs1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j1, hj1, h⟩ := bind_eq_ok_iff.mp h
      have hj1v : j1.val = j.val + 1 := HashMap.uscalar_add_eq hj1
      rw [Env.exprs_copy_refines hpargs] at hpargs1
      have hewf : ExprWF e := ExprWF.bvar he
      have hev : absExpr e = ConLeche.Expr.bvar 0 := by
        rw [Expr.bvar_refines he]; rfl
      have hpargs1v : List.map absExpr pargs1.val
          = List.map absExpr ps.val ++ [ConLeche.Expr.bvar 0] := by
        rw [vec_push_val hpargs1, List.map_append]
        simp [hev]
      have hpargs1wf : ExprsWF pargs1 := by
        intro x hx
        rw [vec_push_val hpargs1, List.mem_append] at hx
        cases hx with
        | inl hx => exact hps x hx
        | inr hx => rw [List.mem_singleton.mp hx]; exact hewf
      obtain ⟨hnmv, hnmwf⟩ := CoreK.proj_model_name_refines ht hnm
      obtain ⟨husv, huswf⟩ := hspines.1 lps us hlps hus
      have he1v : absExpr e1
          = ConLeche.Expr.const (ConLeche.projModelName (absName t) j.val)
              ((absNames lps).map ConLeche.Level.param) := by
        rw [Expr.mk_const_refines he1, hnmv, husv]
      have he1wf : ExprWF e1 := ExprWF.mk_const hnmwf huswf he1
      obtain ⟨he2v, he2wf⟩ := ExprOps.mk_app_n_refines he1wf hpargs1wf he2
      have hout1wf : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hout1, List.mem_append] at hx
        cases hx with
        | inl hx => exact hout x hx
        | inr hx => rw [List.mem_singleton.mp hx]; exact he2wf
      obtain ⟨hrec, hrecwf⟩ := ih j1 out1 v (by scalar_tac) hout1wf h
      rw [hj1v] at hrec
      refine ⟨?_, hrecwf⟩
      have hrange : List.range' j.val (n_f.val - j.val)
          = j.val :: List.range' (j.val + 1) (n_f.val - (j.val + 1)) := by
        rw [show n_f.val - j.val = (n_f.val - (j.val + 1)) + 1 by omega]
        rfl
      rw [hrec, hrange, List.map_cons, absExprs, vec_push_val hout1,
        List.map_append, List.append_assoc]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        he2v, he1v, hpargs1v, absExprs]

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
      ∧ ExprsWF v :=
  eta_projs_from_val hspines ht hlps hps (n_f.val - j.val) j out v le_rfl hout h

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
  rw [inductives.modeled.eta_rhs] at h
  obtain ⟨ps, hps, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨args1, hargs1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e0, he0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpsv, hpswf⟩ := hspines.2.1 n_p ps hps
  rw [Env.exprs_copy_refines hargs] at hargs1
  obtain ⟨hargs1v, hargs1wf⟩ :=
    eta_projs_from_refines hspines ht hlps hpswf hpswf hargs1
  obtain ⟨hnmv, hnmwf⟩ := model_of_refines hc hnm
  obtain ⟨husv, huswf⟩ := hspines.1 lps us hlps hus
  have he0v : absExpr e0
      = ConLeche.Expr.const ((absName ctor_name).str "_model")
          ((absNames lps).map ConLeche.Level.param) := by
    rw [Expr.mk_const_refines he0, hnmv, husv]
  have he0wf : ExprWF e0 := ExprWF.mk_const hnmwf huswf he0
  obtain ⟨hev, hewf⟩ := ExprOps.mk_app_n_refines he0wf hargs1wf h
  refine ⟨?_, hewf⟩
  rw [hev, he0v, hargs1v, hpsv,
    show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero,
    ← List.range_eq_range']

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
  rw [inductives.modeled.ind_block_caps] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨eta, heta, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨rk, hrk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨u, hu, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pw, hpw, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = decide (absNames cv_c.level_params = absNames cv_t.level_params) :=
    Env.names_beq_refines hcc.2.1 hct.2.1 hb
  have hetav : eta
      = ((decide ((absConstantVal cv_c).levelParams
              = (absConstantVal cv_t).levelParams))
        && ConLeche.checkEtaThmF (absMode mode) lfe (absConstantVal cv_t).name
            (absConstantVal cv_c).name (absConstantVal cv_t).levelParams
            n_p.val n_f.val) := by
    by_cases hbt : b = true
    · rw [if_pos hbt] at heta
      rw [hbt] at hbv
      rw [check_eta_thm_refines hcb hspines hrel hfe hct.1 hcc.1 hct.2.1 heta,
        show (decide ((absConstantVal cv_c).levelParams
            = (absConstantVal cv_t).levelParams)) = true from hbv.symm]
      simp [absConstantVal]
    · simp only [Bool.not_eq_true] at hbt
      rw [if_neg (by simp [hbt]), Result.ok.injEq] at heta
      rw [hbt] at hbv
      rw [← heta,
        show (decide ((absConstantVal cv_c).levelParams
            = (absConstantVal cv_t).levelParams)) = false from hbv.symm]
      simp
  have hrkv : rk = ((n_f.val == 0)
      && ConLeche.piResultIsProp (absConstantVal cv_t).type) := by
    by_cases hnf : n_f = 0#u64
    · rw [if_pos hnf] at hrk
      rw [CoreK.pi_result_is_prop_refines hct.2.2 hrk,
        show (n_f.val == 0) = true by rw [hnf]; rfl]
      simp [absConstantVal]
    · rw [if_neg hnf, Result.ok.injEq] at hrk
      rw [← hrk, show (n_f.val == 0) = false by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro hc'
        exact hnf (by scalar_tac)]
      simp
  have huv : u = ConLeche.checkUnitThmF (absMode mode) lfe
      (absConstantVal cv_t).name (absConstantVal cv_t).levelParams n_p.val :=
    check_unit_thm_refines hcb hspines hrel hfe hct.1 hct.2.1 hu
  obtain ⟨hpwv, hpwwf⟩ := CoreK.pi_result_z_refines hct.2.2 hpw
  have hnmv : nm = cv_c.name := by
    rw [name_dup_eq] at hnm; exact (Result.ok_injective hnm).symm
  rw [Result.ok.injEq] at h
  subst h
  refine ⟨?_, ?_⟩
  · rw [ConLeche.indBlockCapsF]
    simp only [absIndCaps, hetav, hrkv, huv, hnmv, hpwv, absConstantVal]
  · exact ⟨by rw [hnmv]; exact hcc.1, hpwwf⟩

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
  rw [inductives.modeled.ctor_residual_ok] at h
  obtain ⟨tt, htt, h⟩ := bind_eq_ok_iff.mp h
  have httv : tt = (absMode mode).ttChecks := Env.tt_checks_refines htt
  rw [ConLeche.ctorResidualOkF, ← httv]
  by_cases htt1 : tt = true
  · rw [if_pos htt1] at h
    rw [htt1]
    by_cases heta : eta = true
    · rw [if_pos heta] at h
      rw [heta]
      simp only [Bool.not_true, Bool.false_or]
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hoabs, howf⟩ :=
        CoreK.ctor_probe_refines (FindAgree.of_rel hrel hfe)
          (FindWF.of_wf hfe) hc ho
      cases o with
      | none =>
        simp only [Option.map_none] at hoabs
        simp only [Result.ok.injEq] at h
        revert hoabs
        cases hx : lfe.find? (absName ctor_name) with
        | none => intro _; simp [← h]
        | some ci => cases ci <;> intro hy <;> simp_all [CoreK.ctorOf]
      | some cq =>
        obtain ⟨cvca, np1, nf1⟩ := cq
        have hcvwf : ConstantValWF cvca := howf cvca np1 nf1 rfl
        have hfindc : lfe.find? (absName ctor_name)
            = some (.ctorInfo (absConstantVal cvca) np1.val nf1.val) :=
          ctorOf_inv (by simpa using hoabs.symm)
        rw [hfindc]
        simp at h
        obtain ⟨k, hk, o1, ho1, h⟩ := h
        have hkv : k.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hk
        obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_pis_refines hcvwf.2.2 ho1
        rw [hkv] at ho1abs
        simp only []
        rw [show (absConstantVal cvca).type = absExpr cvca.ty from rfl,
          ← ho1abs]
        cases o1 with
        | none =>
          simp only [Result.ok.injEq] at h
          simp [← h]
        | some z =>
          obtain ⟨bs, e⟩ := z
          have hewf : ExprWF e := (ho1wf _ rfl).2
          simp at h
          obtain ⟨e1, he1, h⟩ := h
          obtain ⟨he1v, he1wf⟩ := hfam t lps n_p n_f e1 ht hlps he1
          simp only [Option.map_some]
          rw [Expr.beq_refines hewf he1wf h, he1v, Bool.eq_iff_iff]
          simp
    · simp only [Bool.not_eq_true] at heta
      rw [if_neg (by simp [heta]), Result.ok.injEq] at h
      rw [← h, heta]
      simp
  · simp only [Bool.not_eq_true] at htt1
    rw [if_neg (by simp [htt1]), Result.ok.injEq] at h
    rw [← h, htt1]
    simp

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
  rw [inductives.modeled.ctor_targets_fam] at h
  obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hkv : k.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hk
  obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines hcty ho
  rw [hkv] at hoabs
  rw [ConLeche.ctorTargetsFam, ← hoabs]
  cases o with
  | none =>
    simp only [Result.ok.injEq] at h
    simp [← h]
  | some z =>
    obtain ⟨bs, e⟩ := z
    have hewf : ExprWF e := (howf _ rfl).2
    simp at h
    obtain ⟨e1, he1, h⟩ := h
    obtain ⟨he1v, he1wf⟩ := hfam t lps n_p n_f e1 ht hlps he1
    simp only [Option.map_some]
    rw [Expr.beq_refines hewf he1wf h, he1v, Bool.eq_iff_iff]
    simp

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
theorem single_ind_ctor_from_val (block : alloc.vec.Vec env.ConstantInfo) :
    ∀ k : Nat, ∀ (i : Std.Usize) (t : Option env.ConstantVal)
      (c : Option (env.ConstantVal × Std.U64 × Std.U64)) (n_ind n_ctor : Std.U64)
      (q : (Option env.ConstantVal)
        × (Option (env.ConstantVal × Std.U64 × Std.U64)) × Std.U64 × Std.U64),
      block.length - i.val ≤ k →
      inductives.modeled.single_ind_ctor_from block i t c n_ind n_ctor = ok q →
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
  intro k
  induction k with
  | zero =>
    intro i t c n_ind n_ctor q hk h
    rw [inductives.modeled.single_ind_ctor_from,
      if_pos (show i ≥ alloc.vec.Vec.len block by
        have := alloc.vec.Vec.len_val block; scalar_tac), Result.ok.injEq] at h
    subst h
    have hnil : (absConstantInfos block).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absConstantInfos, List.length_map]
      scalar_tac
    rw [hnil]
    cases t <;> cases c <;> simp [Option.orElse]
  | succ k ih =>
    intro i t c n_ind n_ctor q hk h
    rw [inductives.modeled.single_ind_ctor_from] at h
    by_cases hi : i.val ≥ block.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len block by
        have := alloc.vec.Vec.len_val block; scalar_tac), Result.ok.injEq] at h
      subst h
      have hnil : (absConstantInfos block).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absConstantInfos, List.length_map]
        scalar_tac
      rw [hnil]
      cases t <;> cases c <;> simp [Option.orElse]
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by
        have := alloc.vec.Vec.len_val block; scalar_tac)] at h
      have hlt : i.val < block.val.length := by
        have := alloc.vec.Vec.len_val block; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      have hlt2 : i.val < (absConstantInfos block).length := by
        simpa [absConstantInfos] using hlt
      have hcons : (absConstantInfos block).drop i.val
          = absConstantInfo block.val[i.val]
            :: (absConstantInfos block).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absConstantInfos]
      rw [hcons]
      -- the five inert kinds, then the two that record
      cases hci : block.val[i.val] with
      | AxiomInfo cv =>
        rw [hci] at h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨h1, h2, h3, h4⟩ := ih i2 t c n_ind n_ctor q (by scalar_tac) h
        rw [hi2v] at h1 h2 h3 h4
        exact ⟨by rw [h1]; simp [absConstantInfo],
          by rw [h2]; simp [absConstantInfo],
          by rw [h3]; simp [absConstantInfo],
          by rw [h4]; simp [absConstantInfo]⟩
      | DefnInfo cv v hint =>
        rw [hci] at h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨h1, h2, h3, h4⟩ := ih i2 t c n_ind n_ctor q (by scalar_tac) h
        rw [hi2v] at h1 h2 h3 h4
        exact ⟨by rw [h1]; simp [absConstantInfo],
          by rw [h2]; simp [absConstantInfo],
          by rw [h3]; simp [absConstantInfo],
          by rw [h4]; simp [absConstantInfo]⟩
      | ThmInfo cv v =>
        rw [hci] at h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨h1, h2, h3, h4⟩ := ih i2 t c n_ind n_ctor q (by scalar_tac) h
        rw [hi2v] at h1 h2 h3 h4
        exact ⟨by rw [h1]; simp [absConstantInfo],
          by rw [h2]; simp [absConstantInfo],
          by rw [h3]; simp [absConstantInfo],
          by rw [h4]; simp [absConstantInfo]⟩
      | RecInfo cv mi rp rs =>
        rw [hci] at h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨h1, h2, h3, h4⟩ := ih i2 t c n_ind n_ctor q (by scalar_tac) h
        rw [hi2v] at h1 h2 h3 h4
        exact ⟨by rw [h1]; simp [absConstantInfo],
          by rw [h2]; simp [absConstantInfo],
          by rw [h3]; simp [absConstantInfo],
          by rw [h4]; simp [absConstantInfo]⟩
      | ProjInfo tb =>
        rw [hci] at h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨h1, h2, h3, h4⟩ := ih i2 t c n_ind n_ctor q (by scalar_tac) h
        rw [hi2v] at h1 h2 h3 h4
        exact ⟨by rw [h1]; simp [absConstantInfo],
          by rw [h2]; simp [absConstantInfo],
          by rw [h3]; simp [absConstantInfo],
          by rw [h4]; simp [absConstantInfo]⟩
      | IndInfo cv caps =>
        rw [hci] at h
        obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hi3v : i3.val = n_ind.val + 1 := HashMap.uscalar_add_eq hi3
        obtain ⟨h1, h2, h3, h4⟩ :=
          ih i2 (some cv1) c i3 n_ctor q (by scalar_tac) h
        rw [hi2v] at h1 h2 h3 h4
        have hcv1v : absConstantVal cv1
            = (t.map absConstantVal).getD (absConstantVal cv) := by
          cases t with
          | none =>
            simp only [Option.map_none, Option.getD_none]
            simp only [] at hcv1
            rw [Env.constant_val_dup_refines hcv1]
          | some old =>
            simp only [Option.map_some, Option.getD_some]
            simp only [Result.ok.injEq] at hcv1
            rw [hcv1]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h1]
          cases t with
          | none =>
            simp only [Option.map_none, Option.getD_none] at hcv1v
            simp [absConstantInfo, hcv1v, Option.orElse]
          | some old =>
            simp only [Option.map_some, Option.getD_some] at hcv1v
            simp [absConstantInfo, hcv1v, Option.orElse]
        · rw [h2]; simp [absConstantInfo]
        · rw [h3, hi3v]; simp [absConstantInfo]; omega
        · rw [h4]; simp [absConstantInfo]
      | CtorInfo cv n_p n_f =>
        rw [hci] at h
        obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hi3v : i3.val = n_ctor.val + 1 := HashMap.uscalar_add_eq hi3
        obtain ⟨h1, h2, h3, h4⟩ :=
          ih i2 t (some t1) n_ind i3 q (by scalar_tac) h
        rw [hi2v] at h1 h2 h3 h4
        have ht1v : (absConstantVal t1.1, t1.2.1.val, t1.2.2.val)
            = (c.map (fun p => (absConstantVal p.1, p.2.1.val, p.2.2.val))).getD
                (absConstantVal cv, n_p.val, n_f.val) := by
          cases c with
          | none =>
            simp only [Option.map_none, Option.getD_none]
            simp only [bind_eq_ok_iff, Result.ok.injEq] at ht1
            obtain ⟨cv1, hcv1, ht1⟩ := ht1
            rw [← ht1, Env.constant_val_dup_refines hcv1]
          | some old =>
            simp only [Option.map_some, Option.getD_some]
            simp only [Result.ok.injEq] at ht1
            rw [ht1]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h1]; simp [absConstantInfo]
        · rw [h2]
          cases c with
          | none =>
            simp only [Option.map_none, Option.getD_none] at ht1v
            simp [absConstantInfo, ht1v, Option.orElse]
          | some old =>
            simp only [Option.map_some, Option.getD_some] at ht1v
            simp [absConstantInfo, ht1v, Option.orElse]
        · rw [h3]; simp [absConstantInfo]
        · rw [h4, hi3v]; simp [absConstantInfo]; omega

set_option linter.unusedVariables false in
/-- `single_ind_ctor_from` at its own statement.  (`hblock` stays on the
statement for uniformity with the rest of the block split; the count and the
two `findSome?`s do not read the entries' well-formedness.) -/
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
                | .ctorInfo _ _ _ => true | _ => false)).length :=
  single_ind_ctor_from_val block block.length i t c n_ind n_ctor q
    (by scalar_tac) h

/-- A `findSome?` whose partial function succeeds exactly where a filter keeps
an element reads that filter's head. -/
theorem findSome?_eq_head?_bind {α β : Type} (f : α → Option β) (p : α → Bool)
    (hp : ∀ x, (f x).isSome = p x) (L : List α) :
    L.findSome? f = (L.filter p).head?.bind f := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have hx := hp x
    cases hfx : f x with
    | some v =>
      rw [hfx] at hx
      have hpx : p x = true := by simpa using hx.symm
      rw [List.filter_cons, if_pos hpx]
      simp [hfx]
    | none =>
      rw [hfx] at hx
      have hpx : p x = false := by simpa using hx.symm
      rw [List.filter_cons, if_neg (by simp [hpx])]
      simp [hfx, ih]

theorem indP_isSome (x : ConLeche.ConstantInfo) :
    ((match x with | .indInfo cv _ => some cv | _ => none) : Option _).isSome
      = (match x with | .indInfo _ _ => true | _ => false) := by
  cases x <;> rfl

theorem ctorP_isSome (x : ConLeche.ConstantInfo) :
    ((match x with
        | .ctorInfo cv nP nF => some (cv, nP, nF) | _ => none) : Option _).isSome
      = (match x with | .ctorInfo _ _ _ => true | _ => false) := by
  cases x <;> rfl

theorem filter_ind_shape {L : List ConLeche.ConstantInfo}
    {x : ConLeche.ConstantInfo}
    (h : x ∈ L.filter (fun ci => match ci with | .indInfo _ _ => true | _ => false)) :
    ∃ cv caps, x = .indInfo cv caps := by
  have hx := (List.mem_filter.mp h).2
  cases x <;> simp at hx
  exact ⟨_, _, rfl⟩

theorem filter_ctor_shape {L : List ConLeche.ConstantInfo}
    {x : ConLeche.ConstantInfo}
    (h : x ∈ L.filter
      (fun ci => match ci with | .ctorInfo _ _ _ => true | _ => false)) :
    ∃ cv nP nF, x = .ctorInfo cv nP nF := by
  have hx := (List.mem_filter.mp h).2
  cases x <;> simp at hx
  exact ⟨_, _, _, rfl⟩

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
  rw [inductives.modeled.single_ind_ctor] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o0, o1, nI, nC⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := single_ind_ctor_from_refines hblock hp
  simp only [] at h1 h2 h3 h4
  simp at h
  rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at h1 h2 h3 h4
  rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at h3 h4
  simp only [Option.map_none, Nat.zero_add] at h1 h2 h3 h4
  simp only [Option.orElse] at h1 h2
  rw [findSome?_eq_head?_bind _ _ indP_isSome] at h1
  rw [findSome?_eq_head?_bind _ _ ctorP_isSome] at h2
  -- the two filters, read as lists
  cases hfi : (absConstantInfos block).filter
      (fun ci => match ci with | .indInfo _ _ => true | _ => false) with
  | nil =>
    rw [hfi] at h1 h3
    rw [if_neg (show ¬ nI = 1#u64 by
      intro hc; rw [hc] at h3; simp at h3), Result.ok.injEq] at h
    rw [← h]; rfl
  | cons x xs =>
    obtain ⟨cvT, caps, rfl⟩ := filter_ind_shape (by rw [hfi]; exact List.mem_cons_self)
    cases xs with
    | cons y ys =>
      rw [hfi] at h3
      rw [if_neg (show ¬ nI = 1#u64 by
        intro hc; rw [hc] at h3; simp at h3), Result.ok.injEq] at h
      rw [← h]; rfl
    | nil =>
      rw [hfi] at h1 h3
      simp only [List.head?_cons, Option.bind_some] at h1
      rw [if_pos (show nI = 1#u64 by
        have : nI.val = 1 := by rw [h3]; rfl
        scalar_tac)] at h
      cases hfc : (absConstantInfos block).filter
          (fun ci => match ci with | .ctorInfo _ _ _ => true | _ => false) with
      | nil =>
        rw [hfc] at h4
        rw [if_neg (show ¬ nC = 1#u64 by
          intro hc; rw [hc] at h4; simp at h4), Result.ok.injEq] at h
        rw [← h]; rfl
      | cons z zs =>
        obtain ⟨cvC, nP, nF, rfl⟩ :=
          filter_ctor_shape (by rw [hfc]; exact List.mem_cons_self)
        cases zs with
        | cons w ws =>
          rw [hfc] at h4
          rw [if_neg (show ¬ nC = 1#u64 by
            intro hc; rw [hc] at h4; simp at h4), Result.ok.injEq] at h
          rw [← h]; rfl
        | nil =>
          rw [hfc] at h2 h4
          simp only [List.head?_cons, Option.bind_some] at h2
          rw [if_pos (show nC = 1#u64 by
            have : nC.val = 1 := by rw [h4]; rfl
            scalar_tac)] at h
          cases o0 with
          | none => simp at h1
          | some cvt0 =>
            cases o1 with
            | none => simp at h2
            | some cq =>
              obtain ⟨cvc0, np0, nf0⟩ := cq
              simp at h
              simp only [Option.map_some, Option.some.injEq] at h1 h2
              subst h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
              refine ⟨h1, ?_, ?_, ?_⟩
              · exact congrArg (fun r => r.1) h2
              · exact congrArg (fun r => r.2.1) h2
              · exact congrArg (fun r => r.2.2) h2


end ConRon.Refine.Modeled
