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
6. **One added hypothesis, `pfx.length ≤ rP` on
   `inst_pins_renamed`/`inst_pins_plain`** — `Refine/Scalars.lean`'s
   `instSpine` twin, needed and discharged at the call site.  The walk hands
   `pfx` to `expr_ops::inst_spine` whole, and `Expr.instSpine` consumes its
   whole argument list (its `t - 1` is truncated, so an argument past index
   `t` is still instantiated at `bvar 0`), so the cited `fvs.take rP` spelling
   is the port's answer exactly when `pfx` is already that prefix.  Both call
   sites build `pfx` with `core_k::take_exprs_n (·) rP` (`modeled.rs:1030`,
   `:1248`), so `CoreK.take_exprs_n_val` discharges it.

   Task #59 needed **three more**, all `≤ Std.Usize.max` bounds, and all of
   them are **gone at task #62**: `iota_lhs_prefix_ok`'s `rP ≤ Usize.max`,
   `nested_rule_shape`'s and `check_iota_thm_frames`' `cnP ≤ Usize.max`, and
   the `nP ≤ Usize.max` that `check_eta_thm_shape`/`check_unit_thm_shape`
   cascaded out through `check_eta_thm`, `check_unit_thm` and
   `ind_block_caps` to `Refine/IndC.lean`.  All of them were bought by
   `u64 → usize` casts in `modeled.rs`, which the port no longer has: the
   `Vec` splits are `core_k::take_exprs_n` / `drop_exprs_n`, `lower_all`
   counts a `u64` down instead of stopping at a `usize` bound, and the subject
   binder is read with `expr_ops::dom_at_n`.  Nothing is weakened by their
   removal — the statements are simply true on every target now.
7. Two more **statement changes** in the member/recursor chain (task #59), both
   facts the caller already holds rather than new assumptions:
   - `check_ind_recs` takes `hcan : FEnv.FEnvCanon fe2`.  It runs the
     provisioning fold on a `fenv::dup` of its index and then the rule fold
     against *both* views, so the copy has to be the same index again;
     `FEnv.dup_rel` is what says so and it needs `FEnvCanon`.
     `Refine/IndNativeInstall.lean` takes it the same way, and
     `Refine/IndC.lean` discharges it at the driver.
   - `provision_recs` takes `hout`, the entry-wise well-formedness of its
     accumulator, and **also concludes it of the answer**.  The conclusion is
     what `check_ind_recs_fold` needs of `checked` (`provision_recs_step`
     proves it one entry at a time but the fold had nowhere to put it); the
     hypothesis is the same fact at the accumulator, and the one call site
     starts from `Vec::new`.

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

Task #59 added six imports, all of them already-committed siblings and none of
them a new ingredient: `Refine/CoreKGuards.lean` (`defn_probe`/`ctor_probe` and
`defnOf`/`ctorOf`), `Refine/CoreKVec.lean` (`drop_exprs`),
`Refine/CoreKPinned.lean` (`CoreK.envFacts`, which discharges `EnvFacts` for
`rec_rule_bits`), `Refine/BasisPins.lean` (`eq_basis_pinned`) and con-leche's
own `ConLeche/Verify/FastOps.lean` (`openPisAtFvarsF_eq`, deviation 5) and
`ConLeche/Verify/InferLemmas.lean` (`Expr.mkAppN_getApp`, which is what
deviation 3's spine test needs; `expr_app3_of_spine` below packages it).

Task #59 also gave `StructSpinesRefine` **two more conjuncts**:
`struct_parts::field_spine` against
`(List.range m).map (fun j => .bvar (m - 1 - j))`, which `nested_rule_shape`
reads the major premise's index spine with, and `struct_parts::struct_ps_at`
against `ConLeche.structPsAt`, which the two `*_thm_shape` halves read the
subject binder's domain and the type slot with.  `StructSpinesRefine` is the
only route this file has to `struct_parts`;
`IndIngredients.structSpinesRefine` discharges both from
`StructParts.field_spine_refines` / `struct_ps_at_refines`.

## `sorry` count

**0** out of 65 lemmas (43 at task #57; task #59 closed thirty-eight, task #62
the last five).  Every item's statement is the exact-result one of
DESIGN.md §3.5 and **none is weakened** — the five that closed last lost
hypotheses rather than gaining any.

Task #57's 22: the whole name-map group — `model_str`,
`model_of`, the four `NameToName`/`DomView` dictionaries against `blockRename`,
`projBack`, `projFwd` and `projFwd`-as-a-binder-view, `DomIdent`'s identity
view, and the two `find?` slot searches
`find_proj_model_slot`/`find_proj_fn_slot` — the four pinned suffix names
`iota_thm_name`/`proj_iota_name`/`eta_thm_name`/`unit_thm_name`, the readers
`thm_probe`/`arg_get_d`/`arg_get_last_d`, and the block split's
`filter_recs`/`block_names_of` with their index recursions.

Task #59's 38: the five index recursions `lower_all`, `lift_all_0`,
`pins_wf_from`, `inst_pins_renamed` and `inst_pins_plain`; the two `nF - j`
recursions `eta_projs_from` and `proj_models_at_lps_from`; the block split's
`single_ind_ctor_from` and `single_ind_ctor`; the nested shape's
`nested_rule_shape`; the canonical statement's `iota_stmt_open`,
`iota_lhs_prefix_ok` and `check_iota_sides_ty` (the knot's
`inferType`/`isDefEq` pairs, both lanes); the rules' `iota_rule_stored`; the
capability artifacts `eta_rhs`, `check_eta_thm`, `check_unit_thm`,
`ind_block_caps`, `ctor_residual_ok` and `ctor_targets_fam`; and the
projection functions' `check_proj_lookups` and `check_proj_ty`; the rules' `iota_rule_stored`; and
the **whole member/recursor chain** — `level::is_model_str` and
`name_is_model_suffix` (the two `Refine/Level.lean` readings `checkMemberValF`
needs, proved here because this is their only caller), `check_member_val`,
`check_ind_member`, `provision_recs_step`, `provision_recs`,
`check_ind_recs_fold` and `check_ind_recs`, which is what `Refine/IndC.lean`'s
`check_ind_member_s` / `provision_recs_s` / `check_ind_recs_s` drivers sit on;
the two statement-shape halves `check_unit_thm_shape` and
`check_eta_thm_shape`, the first consumers of deviation 3's spine bridge; and
the **whole projection-function group** — `check_proj_iota_body`,
`check_proj_iota`, `check_proj_fn` and `install_proj_fn_step`; the rules'
`check_iota_rule_fire`, `check_iota_rule` and `check_iota_rules`, the last an
index recursion that carries the accumulator in front of con-leche's cons; and
the iota statement's `check_iota_thm_frames`.

Task #62's five: the canonical iota statement's `check_iota_thm` and
`check_iota_thm_ctor`, and the nested one's `check_iota_thm_n`,
`check_iota_thm_n_ctor` and `check_iota_thm_n_frames`.

Task #59 left them open and named the cause: **a port bug, not missing work**.
Each of them split or indexed a `Vec<Expr>` at a `u64 → usize` cast where the
cited body splits at a `Nat` — `core_k::drop_exprs fvs (r_p as usize)`,
`expr_ops::take_exprs fvs (cn_p as usize)` and four more like them — which is
`Refine/Scalars.lean`'s hazard (the cast's model is
`i.val % 2 ^ System.Platform.numBits`), so on a 32-bit target the statements
were **false** as written.  A `r_p ≤ Usize.max` hypothesis could have
travelled, but a `cn_p ≤ Usize.max` one could not: `check_iota_rule` reads
`cn_p` out of its own `core_k::ctor_probe`, so it is in scope at no caller.

Task #62 landed the Rust fix DESIGN.md §3.3 calls for — a `u64` count is
consumed by a counting recursion rather than cast.  `modeled.rs` now calls
`core_k::take_exprs_n` / `drop_exprs_n` (task #61's twins) at all 27 sites,
`lower_all` counts a `u64` down instead of stopping at a `usize` bound, and
`expr_ops::dom_at_n` reads the subject binder.  The five statements became
unconditionally true, `check_iota_thm_frames` and `iota_lhs_prefix_ok` lost
the bounds they had been carrying, and the `nP`/`cnP` cascade out to
`Refine/IndC.lean` went with them.

Two composition helpers carry the last two proofs, because con-leche does
**not** split `checkIotaThmF`/`checkIotaThmNF` the way the port splits
`check_iota_thm`: `iotaStmtOpen_inv` inverts a successful `iotaStmtOpen` run
back into the five facts the rest of the cited body is guarded by, and
`checkIotaThmF_run`/`checkIotaThmNF_run` compose the port's halves back into
the one cited body.  `bind_iteC` and `run_seq_pure` are what let the nested
one's trailing `pure (.nested lvls pins)` be pushed to the leaves so that the
two normalise together.

`dom_at_n_from_val`/`dom_at_n_refines` are proved here because
`check_eta_thm_shape` and `check_unit_thm_shape` are `expr_ops::dom_at_n`'s
only callers so far; they belong in `Refine/ExprOps*.lean` and should move
there on merge.

`check_iota_thm`, `check_iota_thm_n` and the five stages between them and
`check_ind_recs` now take `hspines : StructSpinesRefine` — `iota_lhs_prefix_ok`
and the major pin read `struct_parts::params_of`, and this file's only route to
`struct_parts` is that ingredient.  `Refine/IndC.lean` discharges it from
`IndIngredients.structSpinesRefine`, exactly as it already does for
`ind_block_caps`.

The projection group's one statement question, settled at task #59: the port's
iota body builds the constructor spine head from `cvj.name`
(`modeled.rs:2149`) where `checkProjIotaF` writes `ctorName`, and the indexed
reading cannot see that the two are the same name.  So
`check_proj_iota_refines` takes `hcname : absName cvj.name = absName
ctor_name` — false without it, since `cvj` is a *parameter* there — and
`check_proj_fn_refines`, the only caller, discharges it from `FEnvCanon fe2`
(also new on its statement, and on `install_proj_fn_step_refines`) through
`FEnv.canon_find_name`, applied to a conjunct added to
`check_proj_lookups_refines`' conclusion (a strengthening: the constant it
returns is the one stored under `ctorName`).  `StructSpinesRefine` travels
with the group for the same reason it travels with `check_unit_thm_shape`:
`Refine/IndStructParts.lean` owns the spine builders, and
`IndIngredients.structSpinesRefine` discharges it at the driver.

Five shapes carried the work and are worth reusing.
* An index recursion goes by `induction` on a `Nat` bound with the
  `partial_fixpoint` equation rewritten in each branch (`lower_all_val` is the
  smallest example).
* A `core::result` `match` is peeled with `cases` on the `Result` and
  `bind_eq_ok_iff.mp` *through* the unreduced tuple `let` — never
  `rw [if_pos]`, whose pattern would mention the match's shadowed binder.  Past
  the second nested `let`, a full `simp at h` turns the rest of the body into
  an explicit disjunction of `(guard = ok false ∧ b = false)` cases, which
  `rcases` reads off directly (`check_unit_thm_refines`).
* A `CheckCM` run equation is assembled by `simp` from the operation lemmas'
  `.run` facts, or — when the cited body's string interpolation gets in the way
  — by a local `*_run` lemma stated at the facts the success path pins
  (`iotaStmtOpen_run`).
* A `Bool` guard cascade that the cited body writes as one multi-scrutinee
  `match` is re-read through the port's owning probes first
  (`unitThmF_read`/`etaThmF_read`), by nested `cases` on each `find?` with
  `try rfl`; a 7^k blow-up of `cases ci₁ <;> cases ci₂ <;> …` does not
  elaborate, the nested form does.
* A transcription's own `match` on an abstracted record (`checkIndMemberN`,
  `provisionRecsStepN`) will not reduce by `rw`/`simp [absConstantInfo]`: the
  matcher's motive depends on the scrutinee, so neither can rewrite it.  Either
  destructure with plain `cases ci` (which substitutes in the hypotheses too,
  so `absConstantInfo` unfolds on both sides), or — when that is not enough —
  state a `*_rec`-style run lemma at a *literal* constructor and apply it up to
  defeq (`provisionRecsStepN_rec`).
* An `Expr` node is decomposed as `obtain ⟨⟨d, k⟩⟩ := e; cases k` with
  `absExpr_mk`/`absExprKind` on the goal and `ExprOps.node_kind` on the
  hypothesis; **do not name the constructor fields in `case`** — `cases` on a
  kind under reverted hypotheses shifts the names, so refer to the children
  only through `CoreK.ExprWF.forallE_children`/`const_children` and the
  refinement equations (`nested_rule_shape_refines`).
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
import ConRon.Refine.CoreKPinned
import ConRon.Refine.BasisPins
import ConLeche.Verify.FastOps
import ConLeche.Verify.InferLemmas

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

/-- `DomIdent`'s view in the shape `CheckerBaseSpec.domsMatchAux` consumes: the
field asks for the `gl`-valued reading with the `ExprWF` bookkeeping, where
`dom_ident_view_refines` above is the sharper `r = e`.  (`Refine/CheckerBase.lean`
carries the same adapter as `dom_ident_view_gl` for its own corollary; it is
repeated here so that this file does not import the checker-base tier for three
lines.) -/
theorem dom_ident_view_gl :
    ∀ (i : Std.U64) (e : expr.Expr), ExprWF e → ∀ r,
      checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView.view
          () i e = ok r →
      absExpr r = (fun _ e => e) i.val (absExpr e) ∧ ExprWF r := by
  intro i e he r hr
  rw [dom_ident_view_refines i e r hr]
  exact ⟨rfl, he⟩



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
  /-- **Task #67's failure halves.**  `kernel/checker_base.rs` has no `Native`
  site either, so each of the six `CheckM` items above throws only where the
  cited body throws.  Each of the six fields below is the `.Err` half of the
  very same `Refine/CheckerBase.lean` lemma — that lemma's full-outcome
  statement instantiated at `.Err ce`, where its `match` reduces — so
  `Refine/IndIngredients.lean` discharges it from exactly the term it already
  uses for the accept half.

  `checker_base::check_constant_val`'s failure half. -/
  checkConstantValErr :
    ∀ st fe cv ce st', StateWF st → FEnvWF fe → ConstantValWF cv →
      checker_base.check_constant_val mode st fe cv = ok (.Err ce, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ErrSim ce ((ConLeche.checkConstantValF
          (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe
          (absConstantVal cv)).run lst)
  /-- `checker_base::check_def_eq_list`'s failure half. -/
  checkDefEqListErr :
    ∀ st fe (d : Std.U64) xs ys ce st', StateWF st → FEnvWF fe →
      ExprsWF xs → ExprsWF ys →
      checker_base.check_def_eq_list mode st fe d xs ys = ok (.Err ce, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ErrSim ce ((ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
          (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe.env d.val
          (absExprs xs) (absExprs ys)).run lst)
  /-- `checker_base::check_annot_list`'s failure half. -/
  checkAnnotListErr :
    ∀ st fe (d : Std.U64) xs ce st', StateWF st → FEnvWF fe → ExprsWF xs →
      checker_base.check_annot_list mode st fe d xs = ok (.Err ce, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ErrSim ce ((ConLeche.checkAnnotList (m := ConLeche.Cached.CheckCM)
          (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe.env d.val
          (absExprs xs)).run lst)
  /-- `checker_base::check_typed_list`'s failure half. -/
  checkTypedListErr :
    ∀ st fe (d : Std.U64) xs ts ce st', StateWF st → FEnvWF fe →
      ExprsWF xs → ExprsWF ts →
      checker_base.check_typed_list mode st fe d xs ts = ok (.Err ce, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ErrSim ce ((ConLeche.checkTypedList (m := ConLeche.Cached.CheckCM)
          (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe.env d.val
          (absExprs xs) (absExprs ts)).run lst)
  /-- `checker_base::check_proj_shape`'s failure half. -/
  checkProjShapeErr :
    ∀ pty cty (n_p n_f : Std.U64) ce, ExprWF pty → ExprWF cty →
      checker_base.check_proj_shape pty cty n_p n_f = ok (.Err ce) →
      ∀ lst : ConLeche.Cached.CState,
        ErrSim ce ((ConLeche.checkProjShape (m := ConLeche.Cached.CheckCM)
          (absExpr pty) (absExpr cty) n_p.val n_f.val).run lst)
  /-- `checker_base::check_proj_rule`'s failure half. -/
  checkProjRuleErr :
    ∀ st fe pty cvj lps (n_p n_f i : Std.U64) ce st',
      StateWF st → FEnvWF fe → ExprWF pty → ConstantValWF cvj → NamesWF lps →
      checker_base.check_proj_rule mode st fe pty cvj lps n_p n_f i
          = ok (.Err ce, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ErrSim ce ((ConLeche.checkProjRuleF
          (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe (absExpr pty)
          (absConstantVal cvj) (absNames lps) n_p.val n_f.val i.val).run lst)



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
  ∧ (∀ (o n_p : Std.U64) (v : alloc.vec.Vec expr.Expr),
      inductives.struct_parts.struct_ps_at o n_p = ok v →
      absExprs v = ConLeche.structPsAt o.val n_p.val ∧ ExprsWF v)

/-- The three-argument spine, backwards: `getAppFn`/`getAppArgs` decompose
exactly the nested `.app` the cited bodies pattern-match on, so deviation 3's
spine test and their four nested matches agree on every `Expr`.  con-leche's
own `Expr.mkAppN_getApp` (`Verify/InferLemmas.lean:648`) is what says it. -/
theorem expr_app3_of_spine {e hd a b c : ConLeche.Expr}
    (hfn : e.getAppFn = hd) (hargs : e.getAppArgs = [a, b, c]) :
    e = .app (.app (.app hd a) b) c := by
  conv_lhs => rw [← ConLeche.Expr.mkAppN_getApp e]
  rw [hfn, hargs]
  rfl

/-! ## Task #67's failure-half vocabulary

The `*_refines` lemmas below are stated over the Rust computation's **whole**
inner outcome (`Refine/README.md`, "the full-outcome convention"), so every
mirrored `CheckError` site in `modeled.rs` — all 69 of them; the module has no
`Native` — needs a con-leche `throw` beside it.  These four are the local
plumbing that every such arm uses. -/

/-- **`throw` in `CheckCM`**: the monad-plumbing `simp` set carries no
`MonadExcept` instance, so `simp` would otherwise leave con-leche's `throw`
arms un-run (`Refine/IndAbs.lean` and `Refine/IndStructInstall.lean` declare
the same lemma — `attribute [local simp]` does not travel across files). -/
private theorem checkCM_throw_apply {b : Type} (le : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM b) lst = .error le := rfl

attribute [local simp] checkCM_throw_apply

/-- The port's `Err` value at a mirrored `throw` arm: `core_types::internal`
*is* the `Internal` constructor. -/
private theorem internal_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.internal v = ok ce) :
    ce = .Internal v :=
  (Result.ok_injective (by rw [core_types.internal] at h; exact h)).symm

/-- The same for `core_types::invalid`. -/
private theorem invalid_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v :=
  (Result.ok_injective (by rw [core_types.invalid] at h; exact h)).symm

/-- The same for `core_types::not_implemented`. -/
private theorem not_implemented_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.not_implemented v = ok ce) :
    ce = .NotImplemented v :=
  (Result.ok_injective (by rw [core_types.not_implemented] at h; exact h)).symm

/-- Move 2, packaged: the port threw `not_implemented` and con-leche's run
ends at a `notImplemented` throw.  The message is never compared. -/
private theorem errSim_notImplemented {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} {x : Except ConLeche.CheckError γ} (s : String)
    (hce : core_types.not_implemented v = ok ce) (hx : x = .error (.notImplemented s)) :
    ErrSim ce x := by
  rw [not_implemented_err hce]; exact ErrSim.notImplemented hx

/-- The same where the cited body's message depends on *which* of several
guards the port's single `Bool` collapsed (`iotaLhsPrefixOk` is three con-leche
`unless`es): the kind is all that is compared, so the message is existential. -/
private theorem errSim_notImplemented' {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} {x : Except ConLeche.CheckError γ}
    (hce : core_types.not_implemented v = ok ce)
    (hx : ∃ s, x = .error (.notImplemented s)) : ErrSim ce x := by
  obtain ⟨s, hs⟩ := hx
  exact errSim_notImplemented s hce hs

/-- The same at `core_types::invalid`. -/
private theorem errSim_invalid {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} {x : Except ConLeche.CheckError γ} (s : String)
    (hce : core_types.invalid v = ok ce) (hx : x = .error (.invalid s)) :
    ErrSim ce x := by
  rw [invalid_err hce]; exact ErrSim.invalid hx

/-- The same at `core_types::internal`. -/
private theorem errSim_internal {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} {x : Except ConLeche.CheckError γ} (s : String)
    (hce : core_types.internal v = ok ce) (hx : x = .error (.internal s)) :
    ErrSim ce x := by
  rw [internal_err hce]; exact ErrSim.internal hx

section Stages

variable {mode : env.CheckMode} (hw : Core.Wrappers mode IndAbs.checkFuelU)
  (hcb : CheckerBaseSpec mode)

include hw hcb

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


/-! ## The side certificates (`Modeled.lean:31-53`) -/

set_option linter.unusedSimpArgs false in
set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/Inductives/Modeled.lean:31-53` — `check_iota_sides_ty`
refines `checkIotaSidesTy`: both sides of a modeled iota equation inhabit the
equation's type, and (in the TT lane) the type slot inhabits the sort the
statement's own `Eq.{ℓA}` names.  The cited function takes the constant's name
for its messages only, so the conclusion holds at *every* name. -/
theorem check_iota_sides_ty_refines
    {st st' : cached.state_c.CState} {fe_self : fenv.FEnv} {depth : Std.U64}
    {alpha_s lhs_s rhs_s : expr.Expr} {l_a : level.Level}
    {out : core.result.Result Unit core_types.CheckError}
    (hst : StateWF st) (hfe : FEnvWF fe_self) (ha : ExprWF alpha_s)
    (hl : ExprWF lhs_s) (hr : ExprWF rhs_s) (hla : LevelWF l_a)
    (h : inductives.modeled.check_iota_sides_ty mode st fe_self depth alpha_s
        lhs_s rhs_s l_a = ok (out, st')) :
    ∀ lst lfe lcvName, StateRel st lst → FEnvRel fe_self lfe →
      match out with
      | .Ok _ =>
        ∃ lst',
          (ConLeche.checkIotaSidesTy (m := ConLeche.Cached.CheckCM) (absMode mode)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe.env depth.val
              (absExpr alpha_s) (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a)
              lcvName).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err e =>
        ErrSim e
          ((ConLeche.checkIotaSidesTy (m := ConLeche.Cached.CheckCM) (absMode mode)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe.env depth.val
              (absExpr alpha_s) (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a)
              lcvName).run lst) := by
  intro lst lfe lcvName hrel hfer
  have henv : absEnv fe_self.env = lfe.env := hfer.1
  rw [inductives.modeled.check_iota_sides_ty] at h
  simp only [IndAbs.check_fuel_eq, bind_tc_ok] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := p
  cases r with
  | Err err =>
    -- move 1: `core_c::infer` threw, and the cited body's first bind carries it
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr := IndAbs.ops_infer_err hw hst hfe hl hp lst lfe hrel hfer
    rw [henv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    simp only [StateT.run] at hle ⊢
    rw [ConLeche.checkIotaSidesTy]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hle]
  | Ok tl =>
  obtain ⟨lst1, hrun1, hrel1, hwf1, htlwf⟩ :=
    IndAbs.ops_infer hw hst hfe hl hp lst lfe hrel hfer
  rw [henv] at hrun1
  obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r2, st2⟩ := p2
  cases r2 with
  | Err err =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr := IndAbs.ops_defeq_err hw hwf1 hfe htlwf ha hp2 lst1 lfe hrel1 hfer
    rw [henv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    simp only [StateT.run] at hrun1 hle ⊢
    rw [ConLeche.checkIotaSidesTy]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hle]
  | Ok b =>
  obtain ⟨lst2, hrun2, hrel2, hwf2⟩ :=
    IndAbs.ops_defeq hw hwf1 hfe htlwf ha hp2 lst1 lfe hrel1 hfer
  rw [henv] at hrun2
  cases b with
  | false =>
    -- move 2: the lhs type mismatch (`Modeled.lean:44`), both sides `notImplemented`
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    refine errSim_notImplemented s!"iota statement lhs type for {lcvName}" hce ?_
    simp only [StateT.run] at hrun1 hrun2 ⊢
    rw [ConLeche.checkIotaSidesTy]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hrun2]
  | true =>
  obtain ⟨p3, hp3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r3, st3⟩ := p3
  cases r3 with
  | Err err =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr := IndAbs.ops_infer_err hw hwf2 hfe hr hp3 lst2 lfe hrel2 hfer
    rw [henv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    simp only [StateT.run] at hrun1 hrun2 hle ⊢
    rw [ConLeche.checkIotaSidesTy]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hrun2, hle]
  | Ok tr =>
  obtain ⟨lst3, hrun3, hrel3, hwf3, htrwf⟩ :=
    IndAbs.ops_infer hw hwf2 hfe hr hp3 lst2 lfe hrel2 hfer
  rw [henv] at hrun3
  obtain ⟨p4, hp4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r4, st4⟩ := p4
  cases r4 with
  | Err err =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr := IndAbs.ops_defeq_err hw hwf3 hfe htrwf ha hp4 lst3 lfe hrel3 hfer
    rw [henv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    simp only [StateT.run] at hrun1 hrun2 hrun3 hle ⊢
    rw [ConLeche.checkIotaSidesTy]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hrun2, hrun3, hle]
  | Ok b1 =>
  obtain ⟨lst4, hrun4, hrel4, hwf4⟩ :=
    IndAbs.ops_defeq hw hwf3 hfe htrwf ha hp4 lst3 lfe hrel3 hfer
  rw [henv] at hrun4
  cases b1 with
  | false =>
    -- the rhs type mismatch (`Modeled.lean:47`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    refine errSim_notImplemented s!"iota statement rhs type for {lcvName}" hce ?_
    simp only [StateT.run] at hrun1 hrun2 hrun3 hrun4 ⊢
    rw [ConLeche.checkIotaSidesTy]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hrun2, hrun3, hrun4]
  | true =>
  obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
  have hb2v : b2 = (absMode mode).ttChecks := Env.tt_checks_refines hb2
  cases hb2t : b2 with
  | false =>
    rw [hb2t] at h hb2v
    rw [if_neg (by simp), Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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
  | Err err =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr := IndAbs.ops_infer_err hw hwf4 hfe ha hp5 lst4 lfe hrel4 hfer
    rw [henv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    simp only [StateT.run] at hrun1 hrun2 hrun3 hrun4 hle ⊢
    rw [ConLeche.checkIotaSidesTy]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hrun2, hrun3, hrun4, hle, ← hb2v]
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
  | Err err =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr := IndAbs.ops_defeq_err hw hwf5 hfe htawf hsrtwf hp6 lst5 lfe hrel5 hfer
    rw [henv, hsrtv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    simp only [StateT.run] at hrun1 hrun2 hrun3 hrun4 hrun5 hle ⊢
    rw [ConLeche.checkIotaSidesTy]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hrun2, hrun3, hrun4, hrun5, hle, ← hb2v]
  | Ok b3 =>
  obtain ⟨lst6, hrun6, hrel6, hwf6⟩ :=
    IndAbs.ops_defeq hw hwf5 hfe htawf hsrtwf hp6 lst5 lfe hrel5 hfer
  rw [henv, hsrtv] at hrun6
  cases b3 with
  | false =>
    -- the TT-lane type-slot sort mismatch (`Modeled.lean:53`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    refine errSim_notImplemented
      s!"iota statement type slot sort for {lcvName}" hce ?_
    simp only [StateT.run] at hrun1 hrun2 hrun3 hrun4 hrun5 hrun6 ⊢
    rw [ConLeche.checkIotaSidesTy]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hrun2, hrun3, hrun4, hrun5, hrun6,
      ← hb2v]
  | true =>
  have h6 : (ok (core.result.Result.Ok (), st6)
      : Result ((core.result.Result Unit core_types.CheckError)
        × cached.state_c.CState)) = ok (out, st') := h
  rw [Result.ok.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  refine ⟨lst6, ?_, hrel6, hwf6⟩
  simp only [StateT.run] at hrun1 hrun2 hrun3 hrun4 hrun5 hrun6
  rw [ConLeche.checkIotaSidesTy]
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, hrun1, hrun2, hrun3, hrun4, hrun5, hrun6,
    ← hb2v]

/-- `check_iota_sides_ty_refines` at a success, the pre-#67 statement. -/
theorem check_iota_sides_ty_refines_ok
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
        ∧ StateRel st' lst' ∧ StateWF st' :=
  check_iota_sides_ty_refines hw hcb hst hfe ha hl hr hla h

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

omit hw hcb in
/-- `iotaStmtOpen`'s four `throw`s (`DeclCheck.lean:513-528`), as runs: the
missing theorem, the level-parameter mismatch, the telescope that will not
open, and the body that is not a three-argument equation.  Task #67's failure
half of `iota_stmt_open_refines` is these four and nothing else. -/
theorem iotaStmtOpen_miss {lfe : ConLeche.FEnv} {cvName : ConLeche.Name}
    {lps : List ConLeche.Name} {rP cnF j : Nat} {lst : ConLeche.Cached.CState}
    (h1 : lfe.findCV? ((cvName.str "_model").str s!"iota_{j}") = none) :
    (iotaStmtOpen lfe cvName lps rP cnF j).run lst
      = .error (.notImplemented s!"missing iota theorem for {cvName}") := by
  rw [iotaStmtOpen, h1]
  simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind, Except.bind]

omit hw hcb in
/-- The level-parameter mismatch. -/
theorem iotaStmtOpen_lps {lfe : ConLeche.FEnv} {cvName : ConLeche.Name}
    {lps : List ConLeche.Name} {rP cnF j : Nat} {cvt : ConLeche.ConstantVal}
    {lst : ConLeche.Cached.CState}
    (h1 : lfe.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (h2 : ¬ cvt.levelParams = lps) :
    (iotaStmtOpen lfe cvName lps rP cnF j).run lst
      = .error (.notImplemented s!"iota theorem level mismatch for {cvName}") := by
  rw [iotaStmtOpen, h1]
  simp [ConLeche.unwrapOr, h2, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]

omit hw hcb in
/-- The telescope that will not open. -/
theorem iotaStmtOpen_shape {lfe : ConLeche.FEnv} {cvName : ConLeche.Name}
    {lps : List ConLeche.Name} {rP cnF j : Nat} {cvt : ConLeche.ConstantVal}
    {lst : ConLeche.Cached.CState}
    (h1 : lfe.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (h2 : cvt.levelParams = lps)
    (h3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = none) :
    (iotaStmtOpen lfe cvName lps rP cnF j).run lst
      = .error (.notImplemented s!"iota statement shape mismatch for {cvName}") := by
  rw [iotaStmtOpen, h1]
  simp [ConLeche.unwrapOr, h2, h3, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure]

omit hw hcb in
/-- The body whose head is not `Eq`. -/
theorem iotaStmtOpen_noteq {lfe : ConLeche.FEnv} {cvName : ConLeche.Name}
    {lps : List ConLeche.Name} {rP cnF j : Nat} {cvt : ConLeche.ConstantVal}
    {fvs : List ConLeche.Expr} {tb : ConLeche.Expr}
    {lst : ConLeche.Cached.CState}
    (h1 : lfe.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (h2 : cvt.levelParams = lps)
    (h3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (h4 : ConLeche.isEqHead tb.getAppFn = false) :
    (iotaStmtOpen lfe cvName lps rP cnF j).run lst
      = .error (.notImplemented s!"iota statement not an equation for {cvName}") := by
  rw [iotaStmtOpen, h1]
  simp [ConLeche.unwrapOr, h2, h3, h4, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure]

omit hw hcb in
/-- The equation body whose spine is not three arguments long. -/
theorem iotaStmtOpen_arity {lfe : ConLeche.FEnv} {cvName : ConLeche.Name}
    {lps : List ConLeche.Name} {rP cnF j : Nat} {cvt : ConLeche.ConstantVal}
    {fvs : List ConLeche.Expr} {tb : ConLeche.Expr}
    {lst : ConLeche.Cached.CState}
    (h1 : lfe.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (h2 : cvt.levelParams = lps)
    (h3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (h4 : ConLeche.isEqHead tb.getAppFn = true)
    (h5 : ¬ tb.getAppArgs.length = 3) :
    (iotaStmtOpen lfe cvName lps rP cnF j).run lst
      = .error (.notImplemented s!"iota statement not an equation for {cvName}") := by
  rw [iotaStmtOpen, h1]
  simp [ConLeche.unwrapOr, h2, h3, h4, h5, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure]

omit hw hcb in
/-- `iotaStmtOpen`'s run, **inverted**: a successful run is exactly the five
facts `iotaStmtOpen_run` builds it from.  `check_iota_thm` and
`check_iota_thm_n` need this because con-leche does *not* split
`checkIotaThmF`/`checkIotaThmNF`: the composition of the port's halves has to
be re-read against the one cited body, and the statement head's facts are what
the rest of that body is guarded by. -/
theorem iotaStmtOpen_inv {lfe : ConLeche.FEnv} {cvName : ConLeche.Name}
    {lps : List ConLeche.Name} {rP cnF j : Nat}
    {fvs targs : List ConLeche.Expr} {lA : ConLeche.Level}
    {lst : ConLeche.Cached.CState}
    (h : (iotaStmtOpen lfe cvName lps rP cnF j).run lst
      = .ok ((fvs, targs, lA), lst)) :
    ∃ cvt tb, lfe.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt
      ∧ cvt.levelParams = lps
      ∧ ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb)
      ∧ ConLeche.isEqHead tb.getAppFn = true
      ∧ tb.getAppArgs.length = 3
      ∧ targs = tb.getAppArgs
      ∧ lA = ConLeche.eqHeadLevel tb.getAppFn := by
  have hthrow : ∀ {b : Type} (le : ConLeche.CheckError)
      (s : ConLeche.Cached.CState),
      (throw le : ConLeche.Cached.CheckCM b) s = .error le := fun _ _ => rfl
  cases hf : lfe.findCV? ((cvName.str "_model").str s!"iota_{j}") with
  | none =>
    rw [iotaStmtOpen, hf] at h
    simp [hthrow, ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
      Except.bind] at h
  | some cvt =>
  rw [iotaStmtOpen, hf] at h
  by_cases h2 : cvt.levelParams = lps
  · cases ho : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 with
    | none =>
      simp [hthrow, ConLeche.unwrapOr, h2, ho, StateT.run, Bind.bind, StateT.bind,
        Except.bind, Pure.pure, StateT.pure, Except.pure] at h
    | some q =>
    obtain ⟨fvs', tb⟩ := q
    by_cases h4 : ConLeche.isEqHead tb.getAppFn = true
    · by_cases h5 : tb.getAppArgs.length = 3
      · simp [ConLeche.unwrapOr, h2, ho, h4, h5, StateT.run, Bind.bind,
          StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure] at h
        refine ⟨cvt, tb, rfl, h2, ?_, h4, h5, ?_, ?_⟩ <;> simp_all
      · simp [hthrow, ConLeche.unwrapOr, h2, ho, h4, h5, StateT.run, Bind.bind,
          StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure] at h
    · simp only [Bool.not_eq_true] at h4
      simp [hthrow, ConLeche.unwrapOr, h2, ho, h4, StateT.run, Bind.bind,
        StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure] at h
  · simp [hthrow, ConLeche.unwrapOr, h2, StateT.run, Bind.bind, StateT.bind,
      Except.bind, Pure.pure, StateT.pure, Except.pure] at h

set_option linter.unusedSimpArgs false in
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
    {out : core.result.Result
      (alloc.vec.Vec expr.Expr × alloc.vec.Vec expr.Expr × level.Level)
      core_types.CheckError}
    (hrel : FEnvRel fe2 lfe) (hfe : FEnvWF fe2) (hcv : NameWF cv_name)
    (hlps : NamesWF lps)
    (h : inductives.modeled.iota_stmt_open fe2 cv_name lps r_p cn_f j
        = ok out) :
    match out with
    | .Ok q =>
      (∀ lst, (iotaStmtOpen lfe (absName cv_name) (absNames lps) r_p.val cn_f.val
          j.val).run lst
            = .ok ((absExprs q.1, absExprs q.2.1, absLevel q.2.2), lst))
        ∧ ExprsWF q.1 ∧ ExprsWF q.2.1 ∧ LevelWF q.2.2
    | .Err e =>
      ∀ lst, ErrSim e ((iotaStmtOpen lfe (absName cv_name) (absNames lps)
        r_p.val cn_f.val j.val).run lst) := by
  rw [inductives.modeled.iota_stmt_open] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnv, hnwf⟩ := iota_thm_name_refines hcv hn
  obtain ⟨hoabs, howf⟩ := hcb.findCv fe2 lfe n o hrel hfe hnwf ho
  rw [hnv, show ("iota_" ++ toString j.val)
      = (toString "iota_" ++ toString j.val) from rfl] at hoabs
  cases o with
  | none =>
    -- the missing iota theorem (`DeclCheck.lean:513`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl⟩ := h
    intro lst
    simp only [Option.map_none] at hoabs
    exact errSim_notImplemented
      s!"missing iota theorem for {absName cv_name}" hce
      (iotaStmtOpen_miss hoabs.symm)
  | some cvt =>
  have hcvtwf : ConstantValWF cvt := howf cvt rfl
  simp only [Option.map_some] at hoabs
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = decide (absNames cvt.level_params = absNames lps) :=
    Env.names_beq_refines hcvtwf.2.1 hlps hb
  cases b with
  | false =>
    -- the level-parameter mismatch (`DeclCheck.lean:515`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl⟩ := h
    intro lst
    have hne : ¬ (absConstantVal cvt).levelParams = absNames lps := by
      simpa [absConstantVal] using (of_decide_eq_false hbv.symm)
    exact errSim_notImplemented
      s!"iota theorem level mismatch for {absName cv_name}" hce
      (iotaStmtOpen_lps hoabs.symm hne)
  | true =>
  have hlpseq : (absConstantVal cvt).levelParams = absNames lps := by
    simpa [absConstantVal] using (of_decide_eq_true hbv.symm)
  obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  have hkv : k.val = r_p.val + cn_f.val := HashMap.uscalar_add_eq hk
  obtain ⟨ho1abs, ho1wf⟩ := hcb.openPisAtFvarsF k cvt.ty 0#u64 o1 hcvtwf.2.2 ho1
  rw [hkv, show ((0#u64 : Std.U64)).val = 0 from rfl,
    ConLeche.openPisAtFvarsF_eq,
    show absExpr cvt.ty = (absConstantVal cvt).type from rfl] at ho1abs
  cases o1 with
  | none =>
    -- the telescope that will not open (`DeclCheck.lean:519`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl⟩ := h
    intro lst
    simp only [Option.map_none] at ho1abs
    exact errSim_notImplemented
      s!"iota statement shape mismatch for {absName cv_name}" hce
      (iotaStmtOpen_shape hoabs.symm hlpseq ho1abs.symm)
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
  | false =>
    -- the body that is not an equation (`DeclCheck.lean:523`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl⟩ := h
    intro lst
    have h4 : ConLeche.isEqHead (absExpr tb).getAppFn = false := by
      rw [← hheadv]; exact hb1v.symm
    exact errSim_notImplemented
      s!"iota statement not an equation for {absName cv_name}" hce
      (iotaStmtOpen_noteq hoabs.symm hlpseq ho1abs.symm h4)
  | true =>
  have h4 : ConLeche.isEqHead (absExpr tb).getAppFn = true := by
    rw [← hheadv]; exact hb1v.symm
  by_cases hlen : (alloc.vec.Vec.len targs) != 3#usize
  · -- the equation body of the wrong arity (`DeclCheck.lean:525`)
    rw [if_pos hlen] at h
    simp at h
    obtain ⟨v, hv, ce, hce, rfl⟩ := h
    intro lst
    have h5 : ¬ (ConLeche.Expr.getAppArgs (absExpr tb)).length = 3 := by
      have hl3 := alloc.vec.Vec.len_val targs
      simp only [bne_iff_ne, ne_eq] at hlen
      rw [← htargsv]
      simp only [absExprs, List.length_map]
      intro hc
      exact hlen (Std.UScalar.eq_of_val_eq (by rw [hl3]; exact hc))
    exact errSim_notImplemented
      s!"iota statement not an equation for {absName cv_name}" hce
      (iotaStmtOpen_arity hoabs.symm hlpseq ho1abs.symm h4 h5)
  · rw [if_neg hlen] at h
    obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hlv, hlwf⟩ := hcb.eqHeadLevel head l hheadwf hl
    rw [Result.ok.injEq] at h
    subst h
    have hlenv : (ConLeche.Expr.getAppArgs (absExpr tb)).length = 3 := by
      have hl3 := alloc.vec.Vec.len_val targs
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
      rw [hlen] at hl3
      rw [← htargsv]
      simp only [absExprs, List.length_map]
      exact hl3.symm
    refine ⟨?_, hfvswf, htargswf, hlwf⟩
    intro lst
    rw [iotaStmtOpen_run hoabs.symm hlpseq ho1abs.symm h4 hlenv, ← htargsv,
      ← hheadv, ← hlv]

/-- `iota_stmt_open_refines` at a success, the pre-#67 statement. -/
theorem iota_stmt_open_refines_ok
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
      ∧ ExprsWF q.1 ∧ ExprsWF q.2.1 ∧ LevelWF q.2.2 :=
  iota_stmt_open_refines hw hcb hrel hfe hcv hlps h

set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:529-534` — `iota_lhs_prefix_ok` refines the
left side's head, arity and prefix pins (`iotaLhsPrefixOk`).

Task #59 needed `hrp : r_p.val ≤ Std.Usize.max` here, because the two prefix
pins were `expr_ops::take_exprs (·) (r_p as usize)` and a `u64 → usize` cast
wraps on a 32-bit target.  Task #62 swept `modeled.rs` onto the counting twin
`core_k::take_exprs_n`, which walks the `u64` down without casting, so the
bound is gone from the statement and `CoreK.take_exprs_n_refines` is what the
proof reads the two pins with. -/
theorem iota_lhs_prefix_ok_refines
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name} {m_i r_p : Std.U64}
    {fvs largs : alloc.vec.Vec expr.Expr} {lhs_s : expr.Expr} {b : Bool}
    (hspines : StructSpinesRefine)
    (hf : RenamesTo f g) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hfvs : ExprsWF fvs) (hlargs : ExprsWF largs) (hlhs : ExprWF lhs_s)
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
      obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hv1v, hv1wf⟩ := CoreK.take_exprs_n_refines hlargs hv1
      obtain ⟨hv2v, hv2wf⟩ := CoreK.take_exprs_n_refines hfvs hv2
      rw [Env.exprs_beq_refines hv1wf hv2wf h, hv1v, hv2v, hb0t,
        Bool.eq_iff_iff]
      simp
  · simp only [Bool.not_eq_true] at hb0t
    rw [if_neg (by simp [hb0t]), Result.ok.injEq] at h
    rw [← h, hb0t]
    simp

omit hw hcb in
/-- `checkIotaThmFrames`' success path down to its **tail call** (task #67):
the recursor telescope, the constructor telescope instantiated at the
parameter head, the three frame comparisons and the rule's own applied
right-hand side all succeed, and what is left is exactly `checkIotaSidesTy`
at the state they reached.  Stating the prefix this way gives the accept half
(`checkIotaThmFrames_run` below) and the failure half of the tail at once. -/
theorem checkIotaThmFrames_tail {lmode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {tyA rhsA lhsS rhsS : ConLeche.Expr}
    {rP cnP cnF : Nat} {cvj : ConLeche.ConstantVal}
    {fvs targs : List ConLeche.Expr} {lA : ConLeche.Level}
    {fvsP tyRest cdomsP crestP xFvsP xrest ldoms lrest : _}
    {lst lst1 lst2 lst3 : ConLeche.Cached.CState}
    (h1 : ConLeche.openPisAtFvars rP tyA 0 = some (fvsP, tyRest))
    (h2 : ConLeche.Expr.instPisAt (fvsP.take cnP) cvj.type
      = some (cdomsP, crestP))
    (h3 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((fvsP.take cnP).map ConLeche.Expr.fvarTypeD) cdomsP).run lst
      = .ok ((), lst1))
    (h4 : ConLeche.openPisAtFvars cnF crestP rP = some (xFvsP, xrest))
    (h5 : ConLeche.Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (h6 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((fvsP ++ xFvsP).map ConLeche.Expr.fvarTypeD) ldoms).run lst1
      = .ok ((), lst2))
    (h7 : ((ConLeche.Cached.sharedOpsC lmode lfe).isDefEq lfe.env (rP + cnF)
        rhsS (ConLeche.Expr.mkAppN (rhsA.renameConsts g) fvs)).run lst2
      = .ok (true, lst3)) :
    (checkIotaThmFrames lmode lfe g cvName tyA rP cvj cnP cnF rhsA fvs targs
        lhsS rhsS lA).run lst
      = (ConLeche.checkIotaSidesTy (m := ConLeche.Cached.CheckCM) lmode
          (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
          (targs.getD 0 (.bvar 0)) lhsS rhsS lA cvName).run lst3 := by
  rw [checkIotaThmFrames]
  simp only [StateT.run] at h3 h6 h7 ⊢
  simp only [List.map_take, List.map_append] at h3 h6
  simp only [List.getD_eq_getElem?_getD]
  simp [Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, ConLeche.unwrapOr, h1, h2, h3, h4, h5, h6, h7]

omit hw hcb in
/-- `checkIotaThmFrames`' success path, run: `checkIotaThmFrames_tail` composed
with a `checkIotaSidesTy` that also succeeded. -/
theorem checkIotaThmFrames_run {lmode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {tyA rhsA lhsS rhsS : ConLeche.Expr}
    {rP cnP cnF : Nat} {cvj : ConLeche.ConstantVal}
    {fvs targs : List ConLeche.Expr} {lA : ConLeche.Level}
    {fvsP tyRest cdomsP crestP xFvsP xrest ldoms lrest : _}
    {lst lst1 lst2 lst3 lst4 : ConLeche.Cached.CState}
    (h1 : ConLeche.openPisAtFvars rP tyA 0 = some (fvsP, tyRest))
    (h2 : ConLeche.Expr.instPisAt (fvsP.take cnP) cvj.type
      = some (cdomsP, crestP))
    (h3 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((fvsP.take cnP).map ConLeche.Expr.fvarTypeD) cdomsP).run lst
      = .ok ((), lst1))
    (h4 : ConLeche.openPisAtFvars cnF crestP rP = some (xFvsP, xrest))
    (h5 : ConLeche.Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (h6 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((fvsP ++ xFvsP).map ConLeche.Expr.fvarTypeD) ldoms).run lst1
      = .ok ((), lst2))
    (h7 : ((ConLeche.Cached.sharedOpsC lmode lfe).isDefEq lfe.env (rP + cnF)
        rhsS (ConLeche.Expr.mkAppN (rhsA.renameConsts g) fvs)).run lst2
      = .ok (true, lst3))
    (h8 : (ConLeche.checkIotaSidesTy (m := ConLeche.Cached.CheckCM) lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        (targs.getD 0 (.bvar 0)) lhsS rhsS lA cvName).run lst3
      = .ok ((), lst4)) :
    (checkIotaThmFrames lmode lfe g cvName tyA rP cvj cnP cnF rhsA fvs targs
        lhsS rhsS lA).run lst = .ok ((), lst4) :=
  (checkIotaThmFrames_tail h1 h2 h3 h4 h5 h6 h7).trans h8

set_option linter.unusedSimpArgs false in
/-- `ConLeche/Kernel/DeclCheck.lean:556-572` — `check_iota_thm_frames` refines
`checkIotaThmFrames`: the rule's λ-domains are the public recursor prefix and
constructor field domains, the right side is definitionally the rule's applied
rhs, and both sides inhabit the equation's type slot.

Task #59 carried `hcnp : cn_p.val ≤ Std.Usize.max` here, because the parameter
head was `expr_ops::take_exprs fvsP (cn_p as usize)`.  Task #62's sweep made
it `core_k::take_exprs_n fvsP cn_p`, which counts the `u64` down instead of
casting it, so the bound is gone and `CoreK.take_exprs_n_refines` reads the
head. -/
theorem check_iota_thm_frames_refines
    {st st' : cached.state_c.CState} {fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {ty_a rhs_a lhs_s rhs_s : expr.Expr} {r_p cn_p cn_f : Std.U64}
    {cvj : env.ConstantVal} {fvs targs : alloc.vec.Vec expr.Expr}
    {l_a : level.Level}
    {out : core.result.Result Unit core_types.CheckError}
    (hf : RenamesTo f g) (hst : StateWF st) (hfe : FEnvWF fe_self)
    (hty : ExprWF ty_a) (hcvj : ConstantValWF cvj) (hrhs : ExprWF rhs_a)
    (hfvs : ExprsWF fvs) (htargs : ExprsWF targs) (hl : ExprWF lhs_s)
    (hr : ExprWF rhs_s) (hla : LevelWF l_a)
    (h : inductives.modeled.check_iota_thm_frames mode st fe_self f ty_a r_p cvj
        cn_p cn_f rhs_a fvs targs lhs_s rhs_s l_a = ok (out, st')) :
    ∀ lst lfe lcvName, StateRel st lst → FEnvRel fe_self lfe →
      match out with
      | .Ok _ =>
        ∃ lst',
          (checkIotaThmFrames (absMode mode) lfe g lcvName (absExpr ty_a) r_p.val
              (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
              (absExprs fvs) (absExprs targs) (absExpr lhs_s) (absExpr rhs_s)
              (absLevel l_a)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err e =>
        ErrSim e
          ((checkIotaThmFrames (absMode mode) lfe g lcvName (absExpr ty_a) r_p.val
              (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
              (absExprs fvs) (absExprs targs) (absExpr lhs_s) (absExpr rhs_s)
              (absLevel l_a)).run lst) := by
  intro lst lfe lcvName hrel hfer
  rw [inductives.modeled.check_iota_thm_frames] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ :=
    hcb.openPisAtFvarsF r_p ty_a 0#u64 o hty ho
  rw [show ((0#u64 : Std.U64)).val = 0 from rfl,
    ConLeche.openPisAtFvarsF_eq] at hoabs
  cases o with
  | none =>
    -- the recursor telescope (`DeclCheck.lean:557`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [Option.map_none] at hoabs
    refine errSim_notImplemented
      s!"iota recursor telescope for {lcvName}" hce ?_
    rw [checkIotaThmFrames]
    simp only [StateT.run]
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs]
  | some pq =>
  obtain ⟨fvsP, tyRest⟩ := pq
  obtain ⟨hfvsPwf, htyRestwf⟩ := howf _ rfl
  simp only [Option.map_some] at hoabs
  obtain ⟨pHead, hpHead, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpHeadv, hpHeadwf⟩ := CoreK.take_exprs_n_refines hfvsPwf hpHead
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho1abs, ho1wf⟩ :=
    ExprOps.inst_pis_at_refines hcvj.2.2 hpHeadwf ho1
  rw [hpHeadv, show absExpr cvj.ty = (absConstantVal cvj).type from rfl] at ho1abs
  cases o1 with
  | none =>
    -- the constructor telescope (`DeclCheck.lean:559`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [Option.map_none] at ho1abs
    refine errSim_notImplemented
      s!"iota constructor telescope for {lcvName}" hce ?_
    rw [checkIotaThmFrames]
    simp only [StateT.run]
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, ← ho1abs]
  | some cq =>
  obtain ⟨cdomsP, crestP⟩ := cq
  obtain ⟨hcdomswf, hcrestwf⟩ := ho1wf _ rfl
  simp only [Option.map_some] at ho1abs
  obtain ⟨pDoms, hpDoms, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpDomsv, hpDomswf⟩ := hcb.fvarTypes pHead pDoms hpHeadwf hpDoms
  rw [hpHeadv] at hpDomsv
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = r_p.val + cn_f.val := HashMap.uscalar_add_eq hi1
  obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r1, st1⟩ := p1
  cases r1 with
  | Err err =>
    -- move 1: the parameter-domain comparison threw
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr :=
      hcb.checkDefEqListErr st fe_self i1 pDoms cdomsP err st1 hst hfe hpDomswf
        hcdomswf hp1 lst lfe hrel hfer
    rw [hi1v, hpDomsv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    rw [checkIotaThmFrames]
    simp only [StateT.run] at hle ⊢
    simp only [List.map_take] at hle
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, ← ho1abs, hle]
  | Ok u1 =>
  cases u1
  obtain ⟨lst1, hrun1, hrel1, hwf1⟩ :=
    hcb.checkDefEqList st fe_self i1 pDoms cdomsP st1 hst hfe hpDomswf
      hcdomswf hp1 lst lfe hrel hfer
  rw [hi1v, hpDomsv] at hrun1
  obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho2abs, ho2wf⟩ :=
    hcb.openPisAtFvarsF cn_f crestP r_p o2 hcrestwf ho2
  rw [ConLeche.openPisAtFvarsF_eq] at ho2abs
  cases o2 with
  | none =>
    -- the constructor telescope again (`DeclCheck.lean:563`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [Option.map_none] at ho2abs
    refine errSim_notImplemented
      s!"iota constructor telescope for {lcvName}" hce ?_
    rw [checkIotaThmFrames]
    simp only [StateT.run] at hrun1 ⊢
    simp only [List.map_take] at hrun1
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, ← ho1abs, hrun1, ← ho2abs]
  | some xq =>
  obtain ⟨xFvsP, xrest⟩ := xq
  obtain ⟨hxFvswf, hxrestwf⟩ := ho2wf _ rfl
  simp only [Option.map_some] at ho2abs
  obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
  have hv2e : v2 = fvsP := Env.exprs_copy_refines hv2
  obtain ⟨frame, hframe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hframev, hframewf⟩ :=
    CoreK.append_exprs_refines (by rw [hv2e]; exact hfvsPwf) hxFvswf hframe
  rw [hv2e] at hframev
  obtain ⟨o3, ho3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho3abs, ho3wf⟩ :=
    ExprOps.inst_lams_at_refines hrhs hframewf ho3
  rw [hframev] at ho3abs
  cases o3 with
  | none =>
    -- the rule shape (`DeclCheck.lean:565`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [Option.map_none] at ho3abs
    refine errSim_notImplemented s!"rule shape mismatch for {lcvName}" hce ?_
    rw [checkIotaThmFrames]
    simp only [StateT.run] at hrun1 ⊢
    simp only [List.map_take] at hrun1
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, ← ho1abs, hrun1, ← ho2abs, ← ho3abs]
  | some lq =>
  obtain ⟨ldoms, lrest⟩ := lq
  obtain ⟨hldomswf, hlrestwf⟩ := ho3wf _ rfl
  simp only [Option.map_some] at ho3abs
  obtain ⟨fDoms, hfDoms, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hfDomsv, hfDomswf⟩ := hcb.fvarTypes frame fDoms hframewf hfDoms
  rw [hframev] at hfDomsv
  obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r2, st2⟩ := p2
  cases r2 with
  | Err err =>
    -- move 1: the frame-domain comparison threw
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr :=
      hcb.checkDefEqListErr st1 fe_self i1 fDoms ldoms err st2 hwf1 hfe hfDomswf
        hldomswf hp2 lst1 lfe hrel1 hfer
    rw [hi1v, hfDomsv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    rw [checkIotaThmFrames]
    simp only [StateT.run] at hrun1 hle ⊢
    simp only [List.map_take] at hrun1
    simp only [List.map_append] at hle
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, ← ho1abs, hrun1, ← ho2abs, ← ho3abs, hle]
  | Ok u2 =>
  cases u2
  obtain ⟨lst2, hrun2, hrel2, hwf2⟩ :=
    hcb.checkDefEqList st1 fe_self i1 fDoms ldoms st2 hwf1 hfe hfDomswf
      hldomswf hp2 lst1 lfe hrel1 hfer
  rw [hi1v, hfDomsv] at hrun2
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨he1v, he1wf⟩ :=
    ExprOps.rename_consts_refines _ (fun n hn r hr => hf n hn r hr) hrhs he1
  obtain ⟨applied, happlied, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨happliedv, happliedwf⟩ :=
    ExprOps.mk_app_n_refines he1wf hfvs happlied
  rw [he1v] at happliedv
  simp only [IndAbs.check_fuel_eq, bind_tc_ok] at h
  obtain ⟨p3, hp3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r3, st3⟩ := p3
  cases r3 with
  | Err err =>
    -- move 1: `core_c::defeq` threw
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr :=
      IndAbs.ops_defeq_err hw hwf2 hfe hr happliedwf hp3 lst2 lfe hrel2 hfer
    rw [hi1v, happliedv, hfer.1] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    rw [checkIotaThmFrames]
    simp only [StateT.run] at hrun1 hrun2 hle ⊢
    simp only [List.map_take] at hrun1
    simp only [List.map_append] at hrun2
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, ← ho1abs, hrun1, ← ho2abs, ← ho3abs, hrun2, hle]
  | Ok b =>
  obtain ⟨lst3, hrun3, hrel3, hwf3⟩ :=
    IndAbs.ops_defeq hw hwf2 hfe hr happliedwf hp3 lst2 lfe hrel2 hfer
  rw [hi1v, happliedv, hfer.1] at hrun3
  by_cases hbt : b = true
  · subst hbt
    simp at h
    obtain ⟨alpha, halpha, h⟩ := h
    obtain ⟨halphav, halphawf⟩ := arg_get_d_refines htargs halpha
    rw [show ((0#usize : Std.Usize)).val = 0 from rfl] at halphav
    have hsides :=
      check_iota_sides_ty_refines hw hcb hwf3 hfe halphawf hl hr hla h lst3
        lfe lcvName hrel3 hfer
    have htail := checkIotaThmFrames_tail (cvName := lcvName) (targs := absExprs targs)
      (lhsS := absExpr lhs_s) (lA := absLevel l_a)
      hoabs.symm ho1abs.symm hrun1 ho2abs.symm ho3abs.symm hrun2 hrun3
    rw [hi1v, halphav] at hsides
    cases out with
    | Ok u =>
      obtain ⟨lst4, hrun4, hrel4, hwf4⟩ := hsides
      exact ⟨lst4, htail.trans hrun4, hrel4, hwf4⟩
    | Err e => exact ErrSim.of_eq hsides htail
  · -- the statement mismatch (`DeclCheck.lean:570`)
    simp only [Bool.not_eq_true] at hbt
    subst hbt
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    refine errSim_notImplemented s!"iota statement mismatch for {lcvName}" hce ?_
    rw [checkIotaThmFrames]
    simp only [StateT.run] at hrun1 hrun2 hrun3 ⊢
    simp only [List.map_take] at hrun1
    simp only [List.map_append] at hrun2
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, ← ho1abs, hrun1, ← ho2abs, ← ho3abs, hrun2, hrun3]

/-- `check_iota_thm_frames_refines` at a success, the pre-#67 statement. -/
theorem check_iota_thm_frames_refines_ok
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
        ∧ StateRel st' lst' ∧ StateWF st' :=
  check_iota_thm_frames_refines hw hcb hf hst hfe hty hcvj hrhs hfvs htargs hl
    hr hla h

omit hw hcb in
/-- `checkIotaThmCtor`'s success path down to its **tail call** (task #67): the
constructor telescope instantiated at the major's arguments, its index tuple
against the statement's, the field domains and the recursor prefix domains all
succeed, and what is left is exactly `checkIotaThmFrames` at the state they
reached. -/
theorem checkIotaThmCtor_tail {lmode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {tyA rhsA lhsS rhsS : ConLeche.Expr}
    {mI rP cnP cnF : Nat} {cvj : ConLeche.ConstantVal}
    {fvs xFvs largs targs : List ConLeche.Expr} {lA : ConLeche.Level}
    {cdoms cres rdoms rrest : _}
    {lst lst1 lst2 lst3 : ConLeche.Cached.CState}
    (h1 : (ConLeche.Expr.stripPis (cnP + cnF) cvj.type).isSome = true)
    (h2 : ConLeche.Expr.instPisAt (fvs.take cnP ++ xFvs)
      (ConLeche.Expr.renameConsts g cvj.type) = some (cdoms, cres))
    (h3 : (ConLeche.Expr.getAppArgs cres).length = cnP + (mI - rP))
    (h4 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((largs.drop rP).take (mI - rP))
        ((ConLeche.Expr.getAppArgs cres).drop cnP)).run lst = .ok ((), lst1))
    (h5 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        (xFvs.map ConLeche.Expr.fvarTypeD) (cdoms.drop cnP)).run lst1
      = .ok ((), lst2))
    (h6 : ConLeche.Expr.instPisAt (fvs.take rP)
      (ConLeche.Expr.renameConsts g tyA) = some (rdoms, rrest))
    (h7 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((fvs.take rP).map ConLeche.Expr.fvarTypeD) rdoms).run lst2
      = .ok ((), lst3))
    :
    (checkIotaThmCtor lmode lfe g cvName tyA mI rP cvj cnP cnF rhsA fvs xFvs
        largs targs lhsS rhsS lA).run lst
      = (checkIotaThmFrames lmode lfe g cvName tyA rP cvj cnP cnF rhsA fvs
          targs lhsS rhsS lA).run lst3 := by
  rw [checkIotaThmCtor]
  simp only [StateT.run] at h4 h5 h7 ⊢
  simp only [List.map_take] at h7
  simp [Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, ConLeche.unwrapOr, h1, h2, h3, h4, h5, h6, h7]

omit hw hcb in
/-- `checkIotaThmCtor`'s success path, run: `checkIotaThmCtor_tail` composed
with a `checkIotaThmFrames` that also succeeded. -/
theorem checkIotaThmCtor_run {lmode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {tyA rhsA lhsS rhsS : ConLeche.Expr}
    {mI rP cnP cnF : Nat} {cvj : ConLeche.ConstantVal}
    {fvs xFvs largs targs : List ConLeche.Expr} {lA : ConLeche.Level}
    {cdoms cres rdoms rrest : _}
    {lst lst1 lst2 lst3 lst4 : ConLeche.Cached.CState}
    (h1 : (ConLeche.Expr.stripPis (cnP + cnF) cvj.type).isSome = true)
    (h2 : ConLeche.Expr.instPisAt (fvs.take cnP ++ xFvs)
      (ConLeche.Expr.renameConsts g cvj.type) = some (cdoms, cres))
    (h3 : (ConLeche.Expr.getAppArgs cres).length = cnP + (mI - rP))
    (h4 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((largs.drop rP).take (mI - rP))
        ((ConLeche.Expr.getAppArgs cres).drop cnP)).run lst = .ok ((), lst1))
    (h5 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        (xFvs.map ConLeche.Expr.fvarTypeD) (cdoms.drop cnP)).run lst1
      = .ok ((), lst2))
    (h6 : ConLeche.Expr.instPisAt (fvs.take rP)
      (ConLeche.Expr.renameConsts g tyA) = some (rdoms, rrest))
    (h7 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((fvs.take rP).map ConLeche.Expr.fvarTypeD) rdoms).run lst2
      = .ok ((), lst3))
    (h8 : (checkIotaThmFrames lmode lfe g cvName tyA rP cvj cnP cnF rhsA fvs
        targs lhsS rhsS lA).run lst3 = .ok ((), lst4)) :
    (checkIotaThmCtor lmode lfe g cvName tyA mI rP cvj cnP cnF rhsA fvs xFvs
        largs targs lhsS rhsS lA).run lst = .ok ((), lst4) :=
  (checkIotaThmCtor_tail h1 h2 h3 h4 h5 h6 h7).trans h8

set_option linter.unusedSimpArgs false in
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
    {out : core.result.Result Unit core_types.CheckError}
    (hf : RenamesTo f g) (hst : StateWF st) (hfe : FEnvWF fe_self)
    (hty : ExprWF ty_a) (hcvj : ConstantValWF cvj) (hrhs : ExprWF rhs_a)
    (hfvs : ExprsWF fvs) (hxfvs : ExprsWF x_fvs) (hlargs : ExprsWF largs)
    (htargs : ExprsWF targs) (hl : ExprWF lhs_s) (hr : ExprWF rhs_s)
    (hla : LevelWF l_a)
    (h : inductives.modeled.check_iota_thm_ctor mode st fe_self f ty_a m_i r_p
        cvj cn_p cn_f rhs_a fvs x_fvs largs targs lhs_s rhs_s l_a
        = ok (out, st')) :
    ∀ lst lfe lcvName, StateRel st lst → FEnvRel fe_self lfe →
      match out with
      | .Ok _ =>
        ∃ lst',
          (checkIotaThmCtor (absMode mode) lfe g lcvName (absExpr ty_a) m_i.val
              r_p.val (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
              (absExprs fvs) (absExprs x_fvs) (absExprs largs) (absExprs targs)
              (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a)).run lst
            = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err e =>
        ErrSim e
          ((checkIotaThmCtor (absMode mode) lfe g lcvName (absExpr ty_a) m_i.val
              r_p.val (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
              (absExprs fvs) (absExprs x_fvs) (absExprs largs) (absExprs targs)
              (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a)).run lst) := by
  -- `strip_pis`, `rename_consts`, `inst_pis_at`, two `checkDefEqList`s and
  -- `check_iota_thm_frames_refines`.  Task #59 left this `sorry` because the
  -- five `Vec` splits below were `u64 → usize` casts; task #62 swept them onto
  -- `core_k::take_exprs_n` / `drop_exprs_n`, and with the casts gone the
  -- statement is unconditionally true and the proof is the plain peel.
  intro lst lfe lcvName hrel hfer
  rw [inductives.modeled.check_iota_thm_ctor] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  have hiv : i.val = cn_p.val + cn_f.val := HashMap.uscalar_add_eq hi
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, -⟩ := ExprOps.strip_pis_refines hcvj.2.2 ho
  rw [hiv] at hoabs
  cases o with
  | none =>
    -- the constructor telescope will not strip (`DeclCheck.lean:541`)
    simp [core.option.Option.is_none, bind_eq_ok_iff] at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    have hnone : (ConLeche.Expr.stripPis (cn_p.val + cn_f.val)
        (absConstantVal cvj).type).isSome = false := by
      rw [show (absConstantVal cvj).type = absExpr cvj.ty from rfl, ← hoabs]
      simp
    refine errSim_notImplemented
      s!"iota constructor telescope for {lcvName}" hce ?_
    rw [checkIotaThmCtor]
    simp only [StateT.run]
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, hnone]
  | some sq =>
  simp only [core.option.Option.is_none] at h
  have hisome : (ConLeche.Expr.stripPis (cn_p.val + cn_f.val)
      (absConstantVal cvj).type).isSome = true := by
    rw [show (absConstantVal cvj).type = absExpr cvj.ty from rfl, ← hoabs]
    simp
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hvv, hvwf⟩ := CoreK.take_exprs_n_refines hfvs hv
  obtain ⟨spine, hspine, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hspinev, hspinewf⟩ := CoreK.append_exprs_refines hvwf hxfvs hspine
  rw [hvv] at hspinev
  obtain ⟨renamed, hren, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrenv, hrenwf⟩ :=
    ExprOps.rename_consts_refines _ (fun n hn r hr => hf n hn r hr) hcvj.2.2 hren
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho1abs, ho1wf⟩ := ExprOps.inst_pis_at_refines hrenwf hspinewf ho1
  rw [hspinev, hrenv,
    show absExpr cvj.ty = (absConstantVal cvj).type from rfl] at ho1abs
  cases o1 with
  | none =>
    -- the constructor telescope will not instantiate (`DeclCheck.lean:543`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [Option.map_none] at ho1abs
    refine errSim_notImplemented
      s!"iota constructor telescope for {lcvName}" hce ?_
    rw [checkIotaThmCtor]
    simp only [StateT.run]
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, hisome, ← ho1abs]
  | some cq =>
  obtain ⟨cdoms, cres⟩ := cq
  obtain ⟨hcdomswf, hcreswf⟩ := ho1wf _ rfl
  simp only [Option.map_some] at ho1abs
  obtain ⟨cresArgs, hca, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hcav, hcawf⟩ := ExprOps.get_app_args_refines hcreswf hca
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  simp only [lift_eq, Result.ok.injEq] at hi2
  subst hi2
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
  have hi3v : i3.val = m_i.val - r_p.val := ExprOps.sub_nat_val hi3
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
  have hi4v : i4.val = cn_p.val + i3.val := HashMap.uscalar_add_eq hi4
  have hi2v : (Std.UScalar.cast .U64 (alloc.vec.Vec.len cresArgs) : Std.U64).val
      = cresArgs.val.length := by
    rw [ExprOps.usize_cast_u64_val]
    have := alloc.vec.Vec.len_val cresArgs
    scalar_tac
  by_cases hne :
      (Std.UScalar.cast .U64 (alloc.vec.Vec.len cresArgs) : Std.U64) != i4
  · -- the constructor index tuple is the wrong length (`DeclCheck.lean:546`)
    rw [if_pos hne] at h
    simp [bind_eq_ok_iff] at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [bne_iff_ne, ne_eq] at hne
    have hidx : ¬ (ConLeche.Expr.getAppArgs (absExpr cres)).length
        = cn_p.val + (m_i.val - r_p.val) := by
      rw [← hcav]
      simp only [absExprs, List.length_map]
      intro hc
      exact hne (Std.UScalar.eq_of_val_eq (by rw [hi2v, hc, hi4v, hi3v]))
    refine errSim_notImplemented
      s!"iota constructor indices for {lcvName}" hce ?_
    rw [checkIotaThmCtor]
    simp only [StateT.run]
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, hisome, ← ho1abs, hidx]
  · rw [if_neg hne] at h
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    have hidx : (ConLeche.Expr.getAppArgs (absExpr cres)).length
        = cn_p.val + (m_i.val - r_p.val) := by
      rw [← hcav]
      simp only [absExprs, List.length_map]
      rw [← hi2v, hne, hi4v, hi3v]
    obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hv2v, hv2wf⟩ := CoreK.drop_exprs_n_refines hlargs hv2
    obtain ⟨stmtIdx, hsi, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hsiv, hsiwf⟩ := CoreK.take_exprs_n_refines hv2wf hsi
    rw [hv2v, hi3v] at hsiv
    obtain ⟨ctorIdx, hci, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hciv, hciwf⟩ := CoreK.drop_exprs_n_refines hcawf hci
    rw [hcav] at hciv
    obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
    have hi5v : i5.val = r_p.val + cn_f.val := HashMap.uscalar_add_eq hi5
    obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st1⟩ := p1
    cases r1 with
    | Err e =>
      -- move 1: the index-tuple comparison threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have herr :=
        hcb.checkDefEqListErr st fe_self i5 stmtIdx ctorIdx e st1 hst hfe hsiwf
          hciwf hp1 lst lfe hrel hfer
      rw [hi5v, hsiv, hciv] at herr
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [checkIotaThmCtor]
      simp only [StateT.run] at hle ⊢
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, hisome, ← ho1abs, hidx, hle]
    | Ok u1 =>
    cases u1
    obtain ⟨lst1, hrun1, hrel1, hwf1⟩ :=
      hcb.checkDefEqList st fe_self i5 stmtIdx ctorIdx st1 hst hfe hsiwf hciwf
        hp1 lst lfe hrel hfer
    rw [hi5v, hsiv, hciv] at hrun1
    obtain ⟨xDoms, hxd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hxdv, hxdwf⟩ := hcb.fvarTypes x_fvs xDoms hxfvs hxd
    obtain ⟨cDoms, hcd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hcdv, hcdwf⟩ := CoreK.drop_exprs_n_refines hcdomswf hcd
    obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r2, st2⟩ := p2
    cases r2 with
    | Err e =>
      -- move 1: the field-domain comparison threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have herr :=
        hcb.checkDefEqListErr st1 fe_self i5 xDoms cDoms e st2 hwf1 hfe hxdwf
          hcdwf hp2 lst1 lfe hrel1 hfer
      rw [hi5v, hxdv, hcdv] at herr
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [checkIotaThmCtor]
      simp only [StateT.run] at hrun1 hle ⊢
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, hisome, ← ho1abs, hidx, hrun1, hle]
    | Ok u2 =>
    cases u2
    obtain ⟨lst2, hrun2, hrel2, hwf2⟩ :=
      hcb.checkDefEqList st1 fe_self i5 xDoms cDoms st2 hwf1 hfe hxdwf hcdwf
        hp2 lst1 lfe hrel1 hfer
    rw [hi5v, hxdv, hcdv] at hrun2
    obtain ⟨tyRenamed, htr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨htrv, htrwf⟩ :=
      ExprOps.rename_consts_refines _ (fun n hn r hr => hf n hn r hr) hty htr
    obtain ⟨pfx, hpfx, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hpfxv, hpfxwf⟩ := CoreK.take_exprs_n_refines hfvs hpfx
    obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho2abs, ho2wf⟩ := ExprOps.inst_pis_at_refines htrwf hpfxwf ho2
    rw [hpfxv, htrv] at ho2abs
    cases o2 with
    | none =>
      -- the recursor telescope will not instantiate (`DeclCheck.lean:551`)
      simp at h
      obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
      simp only [Option.map_none] at ho2abs
      refine errSim_notImplemented
        s!"iota recursor telescope for {lcvName}" hce ?_
      rw [checkIotaThmCtor]
      simp only [StateT.run] at hrun1 hrun2 ⊢
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, hisome, ← ho1abs, hidx, hrun1, hrun2, ← ho2abs]
    | some rq =>
    obtain ⟨rdoms, rrest⟩ := rq
    obtain ⟨hrdomswf, hrrestwf⟩ := ho2wf _ rfl
    simp only [Option.map_some] at ho2abs
    obtain ⟨pDoms, hpd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hpdv, hpdwf⟩ := hcb.fvarTypes pfx pDoms hpfxwf hpd
    rw [hpfxv] at hpdv
    obtain ⟨p3, hp3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r3, st3⟩ := p3
    cases r3 with
    | Err e =>
      -- move 1: the recursor prefix-domain comparison threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have herr :=
        hcb.checkDefEqListErr st2 fe_self i5 pDoms rdoms e st3 hwf2 hfe hpdwf
          hrdomswf hp3 lst2 lfe hrel2 hfer
      rw [hi5v, hpdv] at herr
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [checkIotaThmCtor]
      simp only [StateT.run] at hrun1 hrun2 hle ⊢
      simp only [List.map_take] at hle
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, hisome, ← ho1abs, hidx, hrun1, hrun2, ← ho2abs, hle]
    | Ok u3 =>
    cases u3
    obtain ⟨lst3, hrun3, hrel3, hwf3⟩ :=
      hcb.checkDefEqList st2 fe_self i5 pDoms rdoms st3 hwf2 hfe hpdwf hrdomswf
        hp3 lst2 lfe hrel2 hfer
    rw [hi5v, hpdv] at hrun3
    have hframes :=
      check_iota_thm_frames_refines hw hcb hf hwf3 hfe hty hcvj hrhs hfvs
        htargs hl hr hla h lst3 lfe lcvName hrel3 hfer
    have htail := checkIotaThmCtor_tail (cvName := lcvName) (rhsA := absExpr rhs_a)
      (targs := absExprs targs) (lhsS := absExpr lhs_s) (rhsS := absExpr rhs_s)
      (lA := absLevel l_a)
      hisome ho1abs.symm hidx hrun1 hrun2 ho2abs.symm hrun3
    cases out with
    | Ok u =>
      obtain ⟨lst4, hrun4, hrel4, hwf4⟩ := hframes
      exact ⟨lst4, htail.trans hrun4, hrel4, hwf4⟩
    | Err e => exact ErrSim.of_eq hframes htail

/-- `check_iota_thm_ctor_refines` at a success, the pre-#67 statement. -/
theorem check_iota_thm_ctor_refines_ok
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
        ∧ StateRel st' lst' ∧ StateWF st' :=
  check_iota_thm_ctor_refines hw hcb hf hst hfe hty hcvj hrhs hfvs hxfvs hlargs
    htargs hl hr hla h


omit hw hcb in
/-- **The statement head's four `throw`s, carried into the unsplit body**
(task #67): `checkIotaThmF` opens with exactly `iotaStmtOpen`'s body
(`DeclCheck.lean:512-528`), so whatever the port's `iota_stmt_open` threw, the
cited body throws at the same point. -/
theorem checkIotaThmF_stmt_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name} {tyA rhsA : ConLeche.Expr}
    {mI rP j cnP cnF : Nat} {r : ConLeche.RecRule} {cvj : ConLeche.ConstantVal}
    {lst : ConLeche.Cached.CState} {le : ConLeche.CheckError}
    (hle : (iotaStmtOpen lfe2 cvName lps rP cnF j).run lst = .error le) :
    (ConLeche.checkIotaThmF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = .error le := by
  rw [iotaStmtOpen] at hle
  rw [ConLeche.checkIotaThmF]
  cases hfd : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") with
  | none =>
    rw [hfd] at hle
    simpa [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure] using hle
  | some cvt =>
  rw [hfd] at hle
  by_cases h2 : cvt.levelParams = lps
  · cases ho : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 with
    | none =>
      simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, ho] at hle ⊢
      exact hle
    | some q =>
    obtain ⟨fvs, tb⟩ := q
    by_cases h4 : ConLeche.isEqHead tb.getAppFn = true
    · by_cases h5 : tb.getAppArgs.length = 3
      · simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, ho, h4, h5] at hle
      · simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, ho, h4, h5] at hle ⊢
        exact hle
    · simp only [Bool.not_eq_true] at h4
      simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, ho, h4] at hle ⊢
      exact hle
  · simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2] at hle ⊢
    exact hle

omit hw hcb in
/-- **The left side's three `throw`s, as one** (task #67): the port collapses
`checkIotaThmF`'s head, arity and prefix `unless`es into the single `Bool`
`iota_lhs_prefix_ok` with one `throw`, so a `false` there is one of the three
cited throws — all `notImplemented`, which is all `ErrSim` compares. -/
theorem checkIotaThmF_lhs_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA tb : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj cvt : ConLeche.ConstantVal}
    {fvs : List ConLeche.Expr} {lst : ConLeche.Cached.CState}
    (h1 : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (h2 : cvt.levelParams = lps)
    (h3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (h4 : ConLeche.isEqHead tb.getAppFn = true)
    (h5 : tb.getAppArgs.length = 3)
    (h6 : iotaLhsPrefixOk g cvName lps mI rP fvs
        (tb.getAppArgs.getD 1 (.bvar 0))
        (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs = false) :
    ∃ s, (ConLeche.checkIotaThmF lmode (ConLeche.Cached.sharedOpsC lmode lfe)
        lfe2 lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = .error (.notImplemented s) := by
  rw [ConLeche.checkIotaThmF, h1]
  simp only [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, h3, h4, h5, beq_iff_eq, if_true]
  by_cases c1 : (tb.getAppArgs.getD 1 (ConLeche.Expr.bvar 0)).getAppFn
      = ConLeche.Expr.const (g cvName) (lps.map ConLeche.Level.param)
  · rw [if_pos c1]
    by_cases c2 : (tb.getAppArgs.getD 1 (ConLeche.Expr.bvar 0)).getAppArgs.length
        = mI + 1
    · rw [if_pos c2]
      have c3 : ¬ ((tb.getAppArgs.getD 1 (ConLeche.Expr.bvar 0)).getAppArgs.take rP
          = fvs.take rP) := by
        intro hc
        rw [iotaLhsPrefixOk, c1, c2, hc] at h6
        simp at h6
      rw [if_neg c3]
      exact ⟨_, rfl⟩
    · rw [if_neg c2]
      exact ⟨_, rfl⟩
  · rw [if_neg c1]
    exact ⟨_, rfl⟩

omit hw hcb in
/-- The major premise's `throw` (`DeclCheck.lean:537`). -/
theorem checkIotaThmF_major_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA tb : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj cvt : ConLeche.ConstantVal}
    {fvs : List ConLeche.Expr} {lst : ConLeche.Cached.CState}
    (h1 : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (h2 : cvt.levelParams = lps)
    (h3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (h4 : ConLeche.isEqHead tb.getAppFn = true)
    (h5 : tb.getAppArgs.length = 3)
    (h6 : iotaLhsPrefixOk g cvName lps mI rP fvs
        (tb.getAppArgs.getD 1 (.bvar 0))
        (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs = true)
    (h7 : ((tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs.getLastD (.bvar 0)
        == ConLeche.Expr.mkAppN
            (.const (g r.ctor) (cvj.levelParams.map .param))
            (fvs.take cnP ++ fvs.drop rP)) = false) :
    (ConLeche.checkIotaThmF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = .error (.notImplemented s!"iota statement major mismatch for {cvName}") := by
  rw [ConLeche.checkIotaThmF, h1]
  simp only [iotaLhsPrefixOk, Bool.and_eq_true, beq_iff_eq] at h6
  obtain ⟨⟨hhd, har⟩, hpx⟩ := h6
  have h7' : ¬ ((tb.getAppArgs.getD 1 (ConLeche.Expr.bvar 0)).getAppArgs.getLastD
      (ConLeche.Expr.bvar 0) = ConLeche.Expr.mkAppN
        (.const (g r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP)) := by
    intro hc; rw [hc] at h7; simp at h7
  simp only [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, h3, h4, h5, hhd, har, hpx, beq_iff_eq,
    if_true]
  rw [if_neg h7']
  rfl

omit hw hcb in
/-- `checkIotaThmF`'s success path, run: the cited body is **not** split in
con-leche, so this is where the port's four halves — `iota_stmt_open`,
`iota_lhs_prefix_ok`, the major pin and `check_iota_thm_ctor` — are composed
back into it. -/
theorem checkIotaThmF_tail {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA tb : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj cvt : ConLeche.ConstantVal}
    {fvs : List ConLeche.Expr} {lst : ConLeche.Cached.CState}
    (h1 : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (h2 : cvt.levelParams = lps)
    (h3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (h4 : ConLeche.isEqHead tb.getAppFn = true)
    (h5 : tb.getAppArgs.length = 3)
    (h6 : iotaLhsPrefixOk g cvName lps mI rP fvs
        (tb.getAppArgs.getD 1 (.bvar 0))
        (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs = true)
    (h7 : ((tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs.getLastD (.bvar 0)
        == ConLeche.Expr.mkAppN
            (.const (g r.ctor) (cvj.levelParams.map .param))
            (fvs.take cnP ++ fvs.drop rP)) = true) :
    (ConLeche.checkIotaThmF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = (checkIotaThmCtor lmode lfe g cvName tyA mI rP cvj cnP cnF rhsA fvs
          (fvs.drop rP) (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs tb.getAppArgs
          (tb.getAppArgs.getD 1 (.bvar 0)) (tb.getAppArgs.getD 2 (.bvar 0))
          (ConLeche.eqHeadLevel tb.getAppFn)).run lst := by
  rw [ConLeche.checkIotaThmF, h1]
  simp only [checkIotaThmCtor, checkIotaThmFrames]
  simp only [iotaLhsPrefixOk, Bool.and_eq_true, beq_iff_eq] at h6
  obtain ⟨⟨hhd, har⟩, hpx⟩ := h6
  simp only [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, h3, h4, h5, hhd,
    har, hpx, h7, beq_self_eq_true, if_true]
  rfl

omit hw hcb in
/-- `checkIotaThmF`'s success path, run: `checkIotaThmF_tail` composed with a
`checkIotaThmCtor` that also succeeded. -/
theorem checkIotaThmF_run {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA tb : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj cvt : ConLeche.ConstantVal}
    {fvs : List ConLeche.Expr} {lst lst' : ConLeche.Cached.CState}
    (h1 : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (h2 : cvt.levelParams = lps)
    (h3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (h4 : ConLeche.isEqHead tb.getAppFn = true)
    (h5 : tb.getAppArgs.length = 3)
    (h6 : iotaLhsPrefixOk g cvName lps mI rP fvs
        (tb.getAppArgs.getD 1 (.bvar 0))
        (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs = true)
    (h7 : ((tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs.getLastD (.bvar 0)
        == ConLeche.Expr.mkAppN
            (.const (g r.ctor) (cvj.levelParams.map .param))
            (fvs.take cnP ++ fvs.drop rP)) = true)
    (h8 : (checkIotaThmCtor lmode lfe g cvName tyA mI rP cvj cnP cnF rhsA fvs
        (fvs.drop rP) (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs tb.getAppArgs
        (tb.getAppArgs.getD 1 (.bvar 0)) (tb.getAppArgs.getD 2 (.bvar 0))
        (ConLeche.eqHeadLevel tb.getAppFn)).run lst = .ok ((), lst')) :
    (ConLeche.checkIotaThmF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = .ok ((), lst') :=
  (checkIotaThmF_tail h1 h2 h3 h4 h5 h6 h7).trans h8

set_option linter.unusedSimpArgs false in
/-- `ConLeche/Kernel/DeclCheck.lean:507-573` — **`check_iota_thm` refines
`checkIotaThmF`**: a canonical recursor rule's `iota_j` theorem, checked
semantically. -/
theorem check_iota_thm_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {ty_a rhs_a : expr.Expr} {m_i r_p j cn_p cn_f : Std.U64}
    {r : env.RecRule} {cvj : env.ConstantVal}
    {out : core.result.Result Unit core_types.CheckError}
    (hspines : StructSpinesRefine)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hty : ExprWF ty_a) (hr : RecRuleWF r) (hcvj : ConstantValWF cvj)
    (hrhs : ExprWF rhs_a)
    (h : inductives.modeled.check_iota_thm mode st fe2 fe_self f cv_name lps
        ty_a m_i r_p j r cvj cn_p cn_f rhs_a = ok (out, st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 → FEnvRel fe_self lfe →
      match out with
      | .Ok _ =>
        ∃ lst',
          (ConLeche.checkIotaThmF (absMode mode)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
              (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
              j.val (absRecRule r) (absConstantVal cvj) cn_p.val cn_f.val
              (absExpr rhs_a)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err e =>
        ErrSim e
          ((ConLeche.checkIotaThmF (absMode mode)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
              (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
              j.val (absRecRule r) (absConstantVal cvj) cn_p.val cn_f.val
              (absExpr rhs_a)).run lst) := by
  -- `iota_stmt_open_refines`, `iota_lhs_prefix_ok_refines`, the major pin and
  -- `check_iota_thm_ctor_refines`, composed back into the *unsplit* cited body
  -- by `checkIotaThmF_run`.  Task #59 left this `sorry` because `x_fvs` and
  -- the major's parameter prefix were `u64 → usize` casts; task #62 made them
  -- `core_k::drop_exprs_n` / `take_exprs_n`.
  intro lst lfe2 lfe hrel hr2 hrS
  rw [inductives.modeled.check_iota_thm] at h
  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
  cases r1 with
  | Err err =>
    -- move 1: `iota_stmt_open` threw, and the unsplit body throws at the same
    -- guard (`DeclCheck.lean:512-528`)
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ErrSim.trans
      (iota_stmt_open_refines hw hcb hr2 hfe2 hcv hlps hr1 lst)
      (fun le hle => checkIotaThmF_stmt_err hle)
  | Ok oq =>
  obtain ⟨fvs, targs, l_a⟩ := oq
  obtain ⟨hopen, hfvswf, htargswf, hlawf⟩ :=
    iota_stmt_open_refines hw hcb hr2 hfe2 hcv hlps hr1
  obtain ⟨cvt, tb, k1, k2, k3, k4, k5, k6, k7⟩ := iotaStmtOpen_inv (hopen lst)
  obtain ⟨lhs_s, hlhs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlhsv, hlhswf⟩ := arg_get_d_refines htargswf hlhs
  obtain ⟨rhs_s, hrhss, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrhssv, hrhsswf⟩ := arg_get_d_refines htargswf hrhss
  rw [show ((1#usize : Std.Usize)).val = 1 from rfl, k6] at hlhsv
  rw [show ((2#usize : Std.Usize)).val = 2 from rfl, k6] at hrhssv
  obtain ⟨x_fvs, hxfvs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hxfvsv, hxfvswf⟩ := CoreK.drop_exprs_n_refines hfvswf hxfvs
  obtain ⟨largs, hlargs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlargsv, hlargswf⟩ := ExprOps.get_app_args_refines hlhswf hlargs
  rw [hlhsv] at hlargsv
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := iota_lhs_prefix_ok_refines hw hcb hspines hf hcv hlps hfvswf
    hlargswf hlhswf hb
  rw [hlhsv, hlargsv] at hbv
  by_cases hbt : b = true
  · rw [if_pos hbt] at h
    rw [hbt] at hbv
    obtain ⟨major, hmaj, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hmajv, hmajwf⟩ := arg_get_last_d_refines hlargswf hmaj
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hvv, hvwf⟩ := CoreK.take_exprs_n_refines hfvswf hv
    obtain ⟨spine, hspine, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hspinev, hspinewf⟩ := CoreK.append_exprs_refines hvwf hxfvswf hspine
    rw [hvv, hxfvsv] at hspinev
    obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hnmv, hnmwf⟩ := hf r.ctor hr.1 nm hnm
    obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨husv, huswf⟩ := hspines.1 cvj.level_params us hcvj.2.1 hus
    obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
    have hev : absExpr e = ConLeche.Expr.const (g (absName r.ctor))
        ((absNames cvj.level_params).map ConLeche.Level.param) := by
      rw [Expr.mk_const_refines he, hnmv, husv]
    have hewf : ExprWF e := ExprWF.mk_const hnmwf huswf he
    obtain ⟨expMajor, hem, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hemv, hemwf⟩ := ExprOps.mk_app_n_refines hewf hspinewf hem
    rw [hev, hspinev] at hemv
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = decide (absExpr major = absExpr expMajor) :=
      Expr.beq_refines hmajwf hemwf hb1
    rw [hmajv, hemv, hlargsv] at hb1v
    by_cases hb1t : b1 = true
    · rw [if_pos hb1t] at h
      rw [hb1t] at hb1v
      have hctor :=
        check_iota_thm_ctor_refines hw hcb hf hst hfe hty hcvj hrhs hfvswf
          hxfvswf hlargswf htargswf hlhswf hrhsswf hlawf h lst lfe
          (absName cv_name) hrel hrS
      rw [hxfvsv, hlargsv, k6, hlhsv, hrhssv, k7] at hctor
      have htail := checkIotaThmF_tail (lmode := absMode mode) (lfe2 := lfe2)
        (lfe := lfe) (lst := lst) (tyA := absExpr ty_a)
        (rhsA := absExpr rhs_a) (j := j.val) (r := absRecRule r)
        (cnP := cn_p.val) (cvj := absConstantVal cvj)
        k1 k2 k3 k4 k5 hbv.symm
        (by simpa [absRecRule, absConstantVal] using of_decide_eq_true hb1v.symm)
      cases out with
      | Ok u =>
        obtain ⟨lst', hrun, hrel', hwf'⟩ := hctor
        exact ⟨lst', htail.trans hrun, hrel', hwf'⟩
      | Err e => exact ErrSim.of_eq hctor htail
    · -- the major premise mismatch (`DeclCheck.lean:537`)
      simp only [Bool.not_eq_true] at hb1t
      rw [if_neg (by simp [hb1t])] at h
      simp [bind_eq_ok_iff] at h
      obtain ⟨v1, hv1, ce, hce, rfl, rfl⟩ := h
      rw [hb1t] at hb1v
      exact errSim_notImplemented
        s!"iota statement major mismatch for {absName cv_name}" hce
        (checkIotaThmF_major_err (lmode := absMode mode) (lfe2 := lfe2)
          (lfe := lfe) (lst := lst) (tyA := absExpr ty_a)
          (rhsA := absExpr rhs_a) (j := j.val) (r := absRecRule r)
          (cnP := cn_p.val) (cvj := absConstantVal cvj)
          k1 k2 k3 k4 k5 hbv.symm
          (by simpa [absRecRule, absConstantVal] using
            of_decide_eq_false hb1v.symm))
  · -- the left side's head, arity or prefix (`DeclCheck.lean:529-533`)
    simp only [Bool.not_eq_true] at hbt
    rw [if_neg (by simp [hbt])] at h
    simp [bind_eq_ok_iff] at h
    obtain ⟨v1, hv1, ce, hce, rfl, rfl⟩ := h
    rw [hbt] at hbv
    exact errSim_notImplemented' hce
      (checkIotaThmF_lhs_err (lmode := absMode mode) (lfe2 := lfe2)
        (lfe := lfe) (lst := lst) (tyA := absExpr ty_a)
        (rhsA := absExpr rhs_a) (j := j.val) (r := absRecRule r)
        (cnP := cn_p.val) (cvj := absConstantVal cvj)
        k1 k2 k3 k4 k5 hbv.symm)

/-- `check_iota_thm_refines` at a success, the pre-#67 statement. -/
theorem check_iota_thm_refines_ok
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {ty_a rhs_a : expr.Expr} {m_i r_p j cn_p cn_f : Std.U64}
    {r : env.RecRule} {cvj : env.ConstantVal}
    (hspines : StructSpinesRefine)
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
        ∧ StateRel st' lst' ∧ StateWF st' :=
  check_iota_thm_refines hw hcb hspines hf hst hfe2 hfe hcv hlps hty hr hcvj
    hrhs h


/-! ## The nested-auxiliary shape (`Modeled.lean:151-190`,
`DeclCheck.lean:575-599`) -/

omit hw hcb in
/-- `lower_all`'s index recursion on the `u64` count `n`, in the shape the
`partial_fixpoint` equation is usable in.

Task #62 turned the bound into a count: `lower_all` used to take a `usize`
stop index `cn_p` and test `i >= cn_p`, which the one call site reached
through a `cn_p as usize` cast; it now decrements a `u64` `n` and stops at
`n == 0`, so the walk is `(args.drop i).take n` with no cast anywhere. -/
theorem lower_all_val (k : Std.U64) (args : alloc.vec.Vec expr.Expr)
    (hargs : ExprsWF args) :
    ∀ N : Nat, ∀ (n : Std.U64) (i : Std.Usize) (out v : alloc.vec.Vec expr.Expr),
      n.val ≤ N → ExprsWF out →
      inductives.modeled.lower_all k args n i out = ok v →
      absExprs v = absExprs out
          ++ (((absExprs args).drop i.val).take n.val).map
              (ConLeche.Expr.lowerBVars k.val 0)
        ∧ ExprsWF v := by
  intro N
  induction N with
  | zero =>
    intro n i out v hN hout h
    have hn0 : n.val = 0 := by omega
    rw [inductives.modeled.lower_all, if_pos (show n = 0#u64 by scalar_tac),
      Result.ok.injEq] at h
    subst h
    exact ⟨by rw [hn0]; simp, hout⟩
  | succ N ih =>
    intro n i out v hN hout h
    rw [inductives.modeled.lower_all] at h
    by_cases hn0 : n = 0#u64
    · rw [if_pos hn0, Result.ok.injEq] at h
      subst h
      have hnv : n.val = 0 := by rw [hn0]; rfl
      exact ⟨by rw [hnv]; simp, hout⟩
    · rw [if_neg hn0] at h
      have hnv : n.val ≠ 0 := fun hc => hn0 (by scalar_tac)
      by_cases hi : i.val ≥ args.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len args by
          have := alloc.vec.Vec.len_val args; scalar_tac), Result.ok.injEq] at h
        subst h
        have hnil : (absExprs args).drop i.val = [] := by
          apply List.drop_eq_nil_of_le
          simp only [absExprs, List.length_map]
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
        obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        have hn1v : n1.val = n.val - 1 :=
          (ConRon.Refine.Nat.usub_val hn1).2.trans (by simp)
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        have hewf : ExprWF args.val[i.val] := hargs _ (List.getElem_mem hlt)
        obtain ⟨he1v, he1wf⟩ := ExprOps.lower_bvars_refines hewf he1
        have hout1wf : ExprsWF out1 := by
          intro x hx
          rw [vec_push_val hout1, List.mem_append] at hx
          cases hx with
          | inl hx => exact hout x hx
          | inr hx => rw [List.mem_singleton.mp hx]; exact he1wf
        obtain ⟨hrec, hrecwf⟩ := ih n1 i1 out1 v (by omega) hout1wf h
        rw [hi1v, hn1v] at hrec
        have hlt2 : i.val < (absExprs args).length := by
          simp only [absExprs, List.length_map]; scalar_tac
        have hcons : (absExprs args).drop i.val
            = absExpr args.val[i.val] :: (absExprs args).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons hlt2]
          congr 1
          simp [absExprs]
        refine ⟨?_, hrecwf⟩
        rw [hrec, hcons, show n.val = (n.val - 1) + 1 by omega,
          List.take_succ_cons, List.map_cons, absExprs, vec_push_val hout1,
          List.map_append, List.append_assoc]
        simp [absExprs, he1v]

set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:585` — `lower_all` refines
`(args.drop i).take n` mapped by `Expr.lowerBVars k 0`, accumulating on the
way in.  (The knot hypotheses stay on the statement even though the walk does
not reach the core, so that the section's shape is uniform.) -/
theorem lower_all_refines {k n : Std.U64} {args out v : alloc.vec.Vec expr.Expr}
    {i : Std.Usize} (hargs : ExprsWF args) (hout : ExprsWF out)
    (h : inductives.modeled.lower_all k args n i out = ok v) :
    absExprs v = absExprs out
        ++ (((absExprs args).drop i.val).take n.val).map
            (ConLeche.Expr.lowerBVars k.val 0)
      ∧ ExprsWF v :=
  lower_all_val k args hargs n.val n i out v le_rfl hout h

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

Task #59 needed `hcnp : cn_p.val ≤ Std.Usize.max` for the three `cn_p as
usize` casts here (`lower_all`'s bound and the two `Vec` splits).  Task #62
removed all three: `lower_all` counts a `u64` down, and the splits are
`core_k::take_exprs_n`/`drop_exprs_n`, so the bound is off the statement. -/
theorem nested_rule_shape_refines
    {fe2 fe_self : fenv.FEnv} {lfe2 lfe : ConLeche.FEnv} {cv_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {ty_a : expr.Expr}
    {m_i r_p cn_p j : Std.U64}
    {o : Option (alloc.vec.Vec level.Level × alloc.vec.Vec expr.Expr)}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    (hrel2 : FEnvRel fe2 lfe2) (hfe2 : FEnvWF fe2)
    (hrel : FEnvRel fe_self lfe) (hfe : FEnvWF fe_self) (hcv : NameWF cv_name)
    (hlps : NamesWF lps) (hty : ExprWF ty_a)
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
      obtain ⟨pins, hpins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hpinsv, hpinswf⟩ :=
        lower_all_refines hw hcb hargswf ExprOps.exprsWF_new hpins
      rw [show ((0#usize : Std.Usize)).val = 0 from rfl,
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
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hvv, hvwf⟩ := CoreK.take_exprs_n_refines hargswf hv
        obtain ⟨hv1v, hv1wf⟩ :=
          lift_all_0_refines hw hcb hpinswf ExprOps.exprsWF_new hv1
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
          obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v3, hv3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hv2v, hv2wf⟩ := CoreK.drop_exprs_n_refines hargswf hv2
          obtain ⟨hv3v, hv3wf⟩ := hspines.2.2.1 kk v3 hv3
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
                · simp only [Option.map_some, hv5e]
                · intro q hq
                  rw [Option.some.injEq] at hq
                  subst hq
                  exact ⟨by rw [hv5e]; exact hlvlswf, hpinswf⟩
              · simp only [Bool.not_eq_true] at hb4t
                rw [if_neg (by simp [hb4t]), Result.ok.injEq] at h
                rw [hb4t] at hb4v
                rw [if_neg (by
                  rintro ⟨-, -, -, -, hE⟩
                  simp only [absLevels] at hE
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

omit hw hcb in
/-- `checkIotaThmNFrames`' success path down to its **tail call** (task #67). -/
theorem checkIotaThmNFrames_tail {lmode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {tyA rhsA lhsS rhsS : ConLeche.Expr}
    {rP cnP cnF mI : Nat} {cvj : ConLeche.ConstantVal}
    {fvs targs pins : List ConLeche.Expr} {lvls : List ConLeche.Level}
    {lA : ConLeche.Level}
    {fvsP tyRest cdomsP crestP xFvsP crest2P ldoms lrest : _}
    {lst lst1 lst2 lst3 lst4 : ConLeche.Cached.CState}
    (h1 : ConLeche.openPisAtFvars rP tyA 0 = some (fvsP, tyRest))
    (h2 : (ConLeche.checkAnnotList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        (pins.map fun p =>
          ConLeche.Expr.instSpine (fvsP.take rP) (rP - 1) p)).run lst
      = .ok ((), lst1))
    (h3 : ConLeche.Expr.instPisAt
        (pins.map fun p => ConLeche.Expr.instSpine (fvsP.take rP) (rP - 1) p)
        (cvj.type.instantiateLevelParams cvj.levelParams lvls)
      = some (cdomsP, crestP))
    (h4 : (ConLeche.checkTypedList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        (pins.map fun p =>
          ConLeche.Expr.instSpine (fvsP.take rP) (rP - 1) p) cdomsP).run lst1
      = .ok ((), lst2))
    (h5 : ConLeche.openPisAtFvars cnF crestP rP = some (xFvsP, crest2P))
    (h6 : crest2P.getAppArgs.length = cnP + (mI - rP))
    (h7 : ConLeche.Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (h8 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((fvsP ++ xFvsP).map ConLeche.Expr.fvarTypeD) ldoms).run lst2
      = .ok ((), lst3))
    (h9 : ((ConLeche.Cached.sharedOpsC lmode lfe).isDefEq lfe.env (rP + cnF)
        rhsS (ConLeche.Expr.mkAppN (rhsA.renameConsts g) fvs)).run lst3
      = .ok (true, lst4))
    :
    (checkIotaThmNFrames lmode lfe g cvName tyA rP cvj cnP cnF rhsA fvs targs
        lhsS rhsS lA lvls pins mI).run lst
      = (ConLeche.checkIotaSidesTy (m := ConLeche.Cached.CheckCM) lmode
          (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
          (targs.getD 0 (.bvar 0)) lhsS rhsS lA cvName).run lst4 := by
  rw [checkIotaThmNFrames]
  simp only [StateT.run] at h2 h4 h8 h9 ⊢
  simp only [List.map_append] at h8
  simp only [List.getD_eq_getElem?_getD]
  simp [Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, ConLeche.unwrapOr, h1, h2, h3, h4, h5, h6, h7,
    h8, h9]

omit hw hcb in
/-- `checkIotaThmNFrames`' success path, run: `checkIotaThmNFrames_tail`
composed with a `checkIotaSidesTy` that also succeeded. -/
theorem checkIotaThmNFrames_run {lmode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {tyA rhsA lhsS rhsS : ConLeche.Expr}
    {rP cnP cnF mI : Nat} {cvj : ConLeche.ConstantVal}
    {fvs targs pins : List ConLeche.Expr} {lvls : List ConLeche.Level}
    {lA : ConLeche.Level}
    {fvsP tyRest cdomsP crestP xFvsP crest2P ldoms lrest : _}
    {lst lst1 lst2 lst3 lst4 lst5 : ConLeche.Cached.CState}
    (h1 : ConLeche.openPisAtFvars rP tyA 0 = some (fvsP, tyRest))
    (h2 : (ConLeche.checkAnnotList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        (pins.map fun p =>
          ConLeche.Expr.instSpine (fvsP.take rP) (rP - 1) p)).run lst
      = .ok ((), lst1))
    (h3 : ConLeche.Expr.instPisAt
        (pins.map fun p => ConLeche.Expr.instSpine (fvsP.take rP) (rP - 1) p)
        (cvj.type.instantiateLevelParams cvj.levelParams lvls)
      = some (cdomsP, crestP))
    (h4 : (ConLeche.checkTypedList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        (pins.map fun p =>
          ConLeche.Expr.instSpine (fvsP.take rP) (rP - 1) p) cdomsP).run lst1
      = .ok ((), lst2))
    (h5 : ConLeche.openPisAtFvars cnF crestP rP = some (xFvsP, crest2P))
    (h6 : crest2P.getAppArgs.length = cnP + (mI - rP))
    (h7 : ConLeche.Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (h8 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((fvsP ++ xFvsP).map ConLeche.Expr.fvarTypeD) ldoms).run lst2
      = .ok ((), lst3))
    (h9 : ((ConLeche.Cached.sharedOpsC lmode lfe).isDefEq lfe.env (rP + cnF)
        rhsS (ConLeche.Expr.mkAppN (rhsA.renameConsts g) fvs)).run lst3
      = .ok (true, lst4))
    (h10 : (ConLeche.checkIotaSidesTy (m := ConLeche.Cached.CheckCM) lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        (targs.getD 0 (.bvar 0)) lhsS rhsS lA cvName).run lst4
      = .ok ((), lst5)) :
    (checkIotaThmNFrames lmode lfe g cvName tyA rP cvj cnP cnF rhsA fvs targs
        lhsS rhsS lA lvls pins mI).run lst = .ok ((), lst5) :=
  (checkIotaThmNFrames_tail h1 h2 h3 h4 h5 h6 h7 h8 h9).trans h10

set_option linter.unusedSimpArgs false in
/-- `ConLeche/Kernel/DeclCheck.lean:661-684` — `check_iota_thm_n_frames`
refines `checkIotaThmNFrames`. -/
theorem check_iota_thm_n_frames_refines
    {st st' : cached.state_c.CState} {fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {ty_a rhs_a lhs_s rhs_s : expr.Expr} {r_p cn_p cn_f m_i : Std.U64}
    {cvj : env.ConstantVal} {fvs targs pins : alloc.vec.Vec expr.Expr}
    {lvls : alloc.vec.Vec level.Level} {l_a : level.Level}
    {out : core.result.Result Unit core_types.CheckError}
    (hf : RenamesTo f g) (hst : StateWF st) (hfe : FEnvWF fe_self)
    (hty : ExprWF ty_a) (hcvj : ConstantValWF cvj) (hrhs : ExprWF rhs_a)
    (hfvs : ExprsWF fvs) (htargs : ExprsWF targs) (hl : ExprWF lhs_s)
    (hr : ExprWF rhs_s) (hla : LevelWF l_a) (hlvls : LevelsWF lvls)
    (hpins : ExprsWF pins)
    (h : inductives.modeled.check_iota_thm_n_frames mode st fe_self f ty_a r_p
        cvj cn_p cn_f rhs_a fvs targs lhs_s rhs_s l_a lvls pins m_i
        = ok (out, st')) :
    ∀ lst lfe lcvName, StateRel st lst → FEnvRel fe_self lfe →
      match out with
      | .Ok _ =>
        ∃ lst',
          (checkIotaThmNFrames (absMode mode) lfe g lcvName (absExpr ty_a) r_p.val
              (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
              (absExprs fvs) (absExprs targs) (absExpr lhs_s) (absExpr rhs_s)
              (absLevel l_a) (absLevels lvls) (absExprs pins) m_i.val).run lst
            = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err e =>
        ErrSim e
          ((checkIotaThmNFrames (absMode mode) lfe g lcvName (absExpr ty_a) r_p.val
              (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
              (absExprs fvs) (absExprs targs) (absExpr lhs_s) (absExpr rhs_s)
              (absLevel l_a) (absLevels lvls) (absExprs pins) m_i.val).run lst) := by
  -- `inst_pins_plain_refines`, `checkAnnotList`, `checkTypedList`, the two
  -- telescope opens, `IndAbs.ops_defeq` and `check_iota_sides_ty_refines`.
  -- Task #59 left this `sorry` because the public prefix was
  -- `expr_ops::take_exprs (·) (r_p as usize)`; task #62 made it
  -- `core_k::take_exprs_n (·) r_p`, so `inst_pins_plain_refines`' `hlen` comes
  -- straight off `CoreK.take_exprs_n_val` and nothing is cast.
  intro lst lfe lcvName hrel hfer
  rw [inductives.modeled.check_iota_thm_n_frames] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := hcb.openPisAtFvarsF r_p ty_a 0#u64 o hty ho
  rw [show ((0#u64 : Std.U64)).val = 0 from rfl,
    ConLeche.openPisAtFvarsF_eq] at hoabs
  cases o with
  | none =>
    -- the recursor telescope (`DeclCheck.lean:662`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [Option.map_none] at hoabs
    refine errSim_notImplemented
      s!"iota recursor telescope for {lcvName}" hce ?_
    rw [checkIotaThmNFrames]
    simp only [StateT.run]
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs]
  | some pq =>
  obtain ⟨fvsP, tyRest⟩ := pq
  obtain ⟨hfvsPwf, htyRestwf⟩ := howf _ rfl
  simp only [Option.map_some] at hoabs
  obtain ⟨pfx, hpfx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpfxv, hpfxwf⟩ := CoreK.take_exprs_n_refines hfvsPwf hpfx
  have hpfxlen : pfx.length ≤ r_p.val := by
    have hv := CoreK.take_exprs_n_val hpfx
    have := alloc.vec.Vec.len_val pfx
    have hl : pfx.val.length ≤ r_p.val := by
      rw [hv]; simp
    scalar_tac
  obtain ⟨pinsP, hpinsP, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpinsPv, hpinsPwf⟩ :=
    inst_pins_plain_refines hw hcb hpins hpfxwf ExprOps.exprsWF_new hpfxlen
      hpinsP
  rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero, hpfxv,
    List.take_take, Nat.min_self,
    show absExprs (alloc.vec.Vec.new expr.Expr) = [] by
      simp [absExprs, alloc.vec.Vec.new],
    List.nil_append] at hpinsPv
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = r_p.val + cn_f.val := HashMap.uscalar_add_eq hi1
  obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r1, st1⟩ := p1
  cases r1 with
  | Err err =>
    -- move 1: the pin annotation pass threw
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr :=
      hcb.checkAnnotListErr st fe_self i1 pinsP err st1 hst hfe hpinsPwf hp1
        lst lfe hrel hfer
    rw [hi1v, hpinsPv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    rw [checkIotaThmNFrames]
    simp only [StateT.run] at hle ⊢
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, hle]
  | Ok u1 =>
  cases u1
  obtain ⟨lst1, hrun1, hrel1, hwf1⟩ :=
    hcb.checkAnnotList st fe_self i1 pinsP st1 hst hfe hpinsPwf hp1 lst lfe
      hrel hfer
  rw [hi1v, hpinsPv] at hrun1
  obtain ⟨instTy, hinst, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hinstv, hinstwf⟩ :=
    ExprOps.instantiate_level_params_refines hcvj.2.1 hlvls hcvj.2.2 hinst
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho1abs, ho1wf⟩ := ExprOps.inst_pis_at_refines hinstwf hpinsPwf ho1
  rw [hpinsPv, hinstv,
    show absExpr cvj.ty = (absConstantVal cvj).type from rfl,
    show absNames cvj.level_params = (absConstantVal cvj).levelParams from
      rfl] at ho1abs
  cases o1 with
  | none =>
    -- the constructor telescope (`DeclCheck.lean:667`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [Option.map_none] at ho1abs
    refine errSim_notImplemented
      s!"iota constructor telescope for {lcvName}" hce ?_
    rw [checkIotaThmNFrames]
    simp only [StateT.run] at hrun1 ⊢
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, hrun1, ← ho1abs]
  | some cq =>
  obtain ⟨cdomsP, crestP⟩ := cq
  obtain ⟨hcdomswf, hcrestwf⟩ := ho1wf _ rfl
  simp only [Option.map_some] at ho1abs
  obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r2, st2⟩ := p2
  cases r2 with
  | Err err =>
    -- move 1: the pin typing pass threw
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr :=
      hcb.checkTypedListErr st1 fe_self i1 pinsP cdomsP err st2 hwf1 hfe
        hpinsPwf hcdomswf hp2 lst1 lfe hrel1 hfer
    rw [hi1v, hpinsPv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    rw [checkIotaThmNFrames]
    simp only [StateT.run] at hrun1 hle ⊢
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, hrun1, ← ho1abs, hle]
  | Ok u2 =>
  cases u2
  obtain ⟨lst2, hrun2, hrel2, hwf2⟩ :=
    hcb.checkTypedList st1 fe_self i1 pinsP cdomsP st2 hwf1 hfe hpinsPwf
      hcdomswf hp2 lst1 lfe hrel1 hfer
  rw [hi1v, hpinsPv] at hrun2
  obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho2abs, ho2wf⟩ := hcb.openPisAtFvarsF cn_f crestP r_p o2 hcrestwf ho2
  rw [ConLeche.openPisAtFvarsF_eq] at ho2abs
  cases o2 with
  | none =>
    -- the constructor telescope again (`DeclCheck.lean:671`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [Option.map_none] at ho2abs
    refine errSim_notImplemented
      s!"iota constructor telescope for {lcvName}" hce ?_
    rw [checkIotaThmNFrames]
    simp only [StateT.run] at hrun1 hrun2 ⊢
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, hrun1, ← ho1abs, hrun2, ← ho2abs]
  | some xq =>
  obtain ⟨xFvsP, crest2P⟩ := xq
  obtain ⟨hxFvswf, hcrest2wf⟩ := ho2wf _ rfl
  simp only [Option.map_some] at ho2abs
  obtain ⟨resid, hresid, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hresidv, hresidwf⟩ := ExprOps.get_app_args_refines hcrest2wf hresid
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  simp only [lift_eq, Result.ok.injEq] at hi2
  subst hi2
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
  have hi3v : i3.val = m_i.val - r_p.val := ExprOps.sub_nat_val hi3
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
  have hi4v : i4.val = cn_p.val + i3.val := HashMap.uscalar_add_eq hi4
  have hi2v : (Std.UScalar.cast .U64 (alloc.vec.Vec.len resid) : Std.U64).val
      = resid.val.length := by
    rw [ExprOps.usize_cast_u64_val]
    have := alloc.vec.Vec.len_val resid
    scalar_tac
  by_cases hne :
      (Std.UScalar.cast .U64 (alloc.vec.Vec.len resid) : Std.U64) != i4
  · -- the auxiliary constructor's residual arity (`DeclCheck.lean:673`)
    rw [if_pos hne] at h
    simp [bind_eq_ok_iff] at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [bne_iff_ne, ne_eq] at hne
    have hlen : ¬ ((ConLeche.Expr.getAppArgs (absExpr crest2P)).length
        = cn_p.val + (m_i.val - r_p.val)) := by
      rw [← hresidv]
      simp only [absExprs, List.length_map]
      intro hc
      exact hne (Std.UScalar.eq_of_val_eq (by rw [hi2v, hc, hi4v, hi3v]))
    refine errSim_notImplemented
      s!"iota constructor arity for {lcvName}" hce ?_
    rw [checkIotaThmNFrames]
    simp only [StateT.run] at hrun1 hrun2 ⊢
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, hrun1, ← ho1abs, hrun2, ← ho2abs, hlen]
  · rw [if_neg hne] at h
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    have hlen : (ConLeche.Expr.getAppArgs (absExpr crest2P)).length
        = cn_p.val + (m_i.val - r_p.val) := by
      rw [← hresidv]
      simp only [absExprs, List.length_map]
      rw [← hi2v, hne, hi4v, hi3v]
    obtain ⟨v3, hv3, h⟩ := bind_eq_ok_iff.mp h
    have hv3e : v3 = fvsP := Env.exprs_copy_refines hv3
    obtain ⟨frame, hframe, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hframev, hframewf⟩ :=
      CoreK.append_exprs_refines (by rw [hv3e]; exact hfvsPwf) hxFvswf hframe
    rw [hv3e] at hframev
    obtain ⟨o3, ho3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho3abs, ho3wf⟩ := ExprOps.inst_lams_at_refines hrhs hframewf ho3
    rw [hframev] at ho3abs
    cases o3 with
    | none =>
      -- the rule shape (`DeclCheck.lean:676`)
      simp at h
      obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
      simp only [Option.map_none] at ho3abs
      refine errSim_notImplemented s!"rule shape mismatch for {lcvName}" hce ?_
      rw [checkIotaThmNFrames]
      simp only [StateT.run] at hrun1 hrun2 ⊢
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, ← hoabs, hrun1, ← ho1abs, hrun2, ← ho2abs, hlen, ← ho3abs]
    | some lq =>
    obtain ⟨ldoms, lrest⟩ := lq
    obtain ⟨hldomswf, hlrestwf⟩ := ho3wf _ rfl
    simp only [Option.map_some] at ho3abs
    obtain ⟨fDoms, hfDoms, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hfDomsv, hfDomswf⟩ := hcb.fvarTypes frame fDoms hframewf hfDoms
    rw [hframev] at hfDomsv
    obtain ⟨p3, hp3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r3, st3⟩ := p3
    cases r3 with
    | Err err =>
      -- move 1: the frame-domain comparison threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have herr :=
        hcb.checkDefEqListErr st2 fe_self i1 fDoms ldoms err st3 hwf2 hfe
          hfDomswf hldomswf hp3 lst2 lfe hrel2 hfer
      rw [hi1v, hfDomsv] at herr
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [checkIotaThmNFrames]
      simp only [StateT.run] at hrun1 hrun2 hle ⊢
      simp only [List.map_append] at hle
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, ← hoabs, hrun1, ← ho1abs, hrun2, ← ho2abs, hlen, ← ho3abs, hle]
    | Ok u3 =>
    cases u3
    obtain ⟨lst3, hrun3, hrel3, hwf3⟩ :=
      hcb.checkDefEqList st2 fe_self i1 fDoms ldoms st3 hwf2 hfe hfDomswf
        hldomswf hp3 lst2 lfe hrel2 hfer
    rw [hi1v, hfDomsv] at hrun3
    obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨he2v, he2wf⟩ :=
      ExprOps.rename_consts_refines _ (fun n hn r hr => hf n hn r hr) hrhs he2
    obtain ⟨applied, happlied, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨happliedv, happliedwf⟩ :=
      ExprOps.mk_app_n_refines he2wf hfvs happlied
    rw [he2v] at happliedv
    simp only [IndAbs.check_fuel_eq, bind_tc_ok] at h
    obtain ⟨p4, hp4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r4, st4⟩ := p4
    cases r4 with
    | Err err =>
      -- move 1: `core_c::defeq` threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have herr :=
        IndAbs.ops_defeq_err hw hwf3 hfe hr happliedwf hp4 lst3 lfe hrel3 hfer
      rw [hi1v, happliedv, hfer.1] at herr
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [checkIotaThmNFrames]
      simp only [StateT.run] at hrun1 hrun2 hrun3 hle ⊢
      simp only [List.map_append] at hrun3
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, ← hoabs, hrun1, ← ho1abs, hrun2, ← ho2abs, hlen, ← ho3abs,
        hrun3, hle]
    | Ok b =>
    obtain ⟨lst4, hrun4, hrel4, hwf4⟩ :=
      IndAbs.ops_defeq hw hwf3 hfe hr happliedwf hp4 lst3 lfe hrel3 hfer
    rw [hi1v, happliedv, hfer.1] at hrun4
    by_cases hbt : b = true
    · subst hbt
      simp at h
      obtain ⟨alpha, halpha, h⟩ := h
      obtain ⟨halphav, halphawf⟩ := arg_get_d_refines htargs halpha
      rw [show ((0#usize : Std.Usize)).val = 0 from rfl] at halphav
      have hsides :=
        check_iota_sides_ty_refines hw hcb hwf4 hfe halphawf hl hr hla h lst4
          lfe lcvName hrel4 hfer
      rw [hi1v, halphav] at hsides
      have htail := checkIotaThmNFrames_tail (cvName := lcvName)
        (targs := absExprs targs) (lhsS := absExpr lhs_s) (lA := absLevel l_a)
        hoabs.symm hrun1 ho1abs.symm hrun2 ho2abs.symm hlen ho3abs.symm hrun3
        hrun4
      cases out with
      | Ok u =>
        obtain ⟨lst5, hrun5, hrel5, hwf5⟩ := hsides
        exact ⟨lst5, htail.trans hrun5, hrel5, hwf5⟩
      | Err e => exact ErrSim.of_eq hsides htail
    · -- the statement mismatch (`DeclCheck.lean:682`)
      simp only [Bool.not_eq_true] at hbt
      subst hbt
      simp at h
      obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
      refine errSim_notImplemented s!"iota statement mismatch for {lcvName}" hce ?_
      rw [checkIotaThmNFrames]
      simp only [StateT.run] at hrun1 hrun2 hrun3 hrun4 ⊢
      simp only [List.map_append] at hrun3
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, ← hoabs, hrun1, ← ho1abs, hrun2, ← ho2abs, hlen, ← ho3abs,
        hrun3, hrun4]

/-- `check_iota_thm_n_frames_refines` at a success, the pre-#67 statement. -/
theorem check_iota_thm_n_frames_refines_ok
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
        ∧ StateRel st' lst' ∧ StateWF st' :=
  check_iota_thm_n_frames_refines hw hcb hf hst hfe hty hcvj hrhs hfvs htargs
    hl hr hla hlvls hpins h


omit hw hcb in
/-- `checkIotaThmNCtor`'s success path down to its **tail call** (task #67). -/
theorem checkIotaThmNCtor_tail {lmode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {tyA rhsA lhsS rhsS : ConLeche.Expr}
    {mI rP cnP cnF : Nat} {cvj : ConLeche.ConstantVal}
    {fvs xFvs largs targs pins pinsF : List ConLeche.Expr}
    {lvls : List ConLeche.Level} {lA : ConLeche.Level}
    {cdoms cres rdoms rrest : _}
    {lst lst1 lst2 lst3 : ConLeche.Cached.CState}
    (h1 : ConLeche.Expr.instPisAt (pinsF ++ xFvs)
      (ConLeche.Expr.renameConsts g
        (cvj.type.instantiateLevelParams cvj.levelParams lvls))
      = some (cdoms, cres))
    (h2 : (ConLeche.Expr.getAppArgs cres).length = cnP + (mI - rP))
    (h3 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((largs.drop rP).take (mI - rP))
        ((ConLeche.Expr.getAppArgs cres).drop cnP)).run lst = .ok ((), lst1))
    (h4 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        (xFvs.map ConLeche.Expr.fvarTypeD) (cdoms.drop cnP)).run lst1
      = .ok ((), lst2))
    (h5 : ConLeche.Expr.instPisAt (fvs.take rP)
      (ConLeche.Expr.renameConsts g tyA) = some (rdoms, rrest))
    (h6 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((fvs.take rP).map ConLeche.Expr.fvarTypeD) rdoms).run lst2
      = .ok ((), lst3))
    :
    (checkIotaThmNCtor lmode lfe g cvName tyA mI rP cvj cnP cnF rhsA fvs xFvs
        largs targs lhsS rhsS lA lvls pins pinsF).run lst
      = (checkIotaThmNFrames lmode lfe g cvName tyA rP cvj cnP cnF rhsA fvs
          targs lhsS rhsS lA lvls pins mI).run lst3 := by
  rw [checkIotaThmNCtor]
  simp only [StateT.run] at h3 h4 h6 ⊢
  simp only [List.map_take] at h6
  simp [Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, ConLeche.unwrapOr, h1, h2, h3, h4, h5, h6]

omit hw hcb in
/-- `checkIotaThmNCtor`'s success path, run: `checkIotaThmNCtor_tail` composed
with a `checkIotaThmNFrames` that also succeeded. -/
theorem checkIotaThmNCtor_run {lmode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {tyA rhsA lhsS rhsS : ConLeche.Expr}
    {mI rP cnP cnF : Nat} {cvj : ConLeche.ConstantVal}
    {fvs xFvs largs targs pins pinsF : List ConLeche.Expr}
    {lvls : List ConLeche.Level} {lA : ConLeche.Level}
    {cdoms cres rdoms rrest : _}
    {lst lst1 lst2 lst3 lst4 : ConLeche.Cached.CState}
    (h1 : ConLeche.Expr.instPisAt (pinsF ++ xFvs)
      (ConLeche.Expr.renameConsts g
        (cvj.type.instantiateLevelParams cvj.levelParams lvls))
      = some (cdoms, cres))
    (h2 : (ConLeche.Expr.getAppArgs cres).length = cnP + (mI - rP))
    (h3 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((largs.drop rP).take (mI - rP))
        ((ConLeche.Expr.getAppArgs cres).drop cnP)).run lst = .ok ((), lst1))
    (h4 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        (xFvs.map ConLeche.Expr.fvarTypeD) (cdoms.drop cnP)).run lst1
      = .ok ((), lst2))
    (h5 : ConLeche.Expr.instPisAt (fvs.take rP)
      (ConLeche.Expr.renameConsts g tyA) = some (rdoms, rrest))
    (h6 : (ConLeche.checkDefEqList (m := ConLeche.Cached.CheckCM)
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe.env (rP + cnF)
        ((fvs.take rP).map ConLeche.Expr.fvarTypeD) rdoms).run lst2
      = .ok ((), lst3))
    (h7 : (checkIotaThmNFrames lmode lfe g cvName tyA rP cvj cnP cnF rhsA fvs
        targs lhsS rhsS lA lvls pins mI).run lst3 = .ok ((), lst4)) :
    (checkIotaThmNCtor lmode lfe g cvName tyA mI rP cvj cnP cnF rhsA fvs xFvs
        largs targs lhsS rhsS lA lvls pins pinsF).run lst = .ok ((), lst4) :=
  (checkIotaThmNCtor_tail h1 h2 h3 h4 h5 h6).trans h7

set_option linter.unusedSimpArgs false in
/-- `ConLeche/Kernel/DeclCheck.lean:648-660` — `check_iota_thm_n_ctor` refines
`checkIotaThmNCtor`. -/
theorem check_iota_thm_n_ctor_refines
    {st st' : cached.state_c.CState} {fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {ty_a rhs_a lhs_s rhs_s : expr.Expr} {m_i r_p cn_p cn_f : Std.U64}
    {cvj : env.ConstantVal}
    {fvs x_fvs largs targs pins pins_f : alloc.vec.Vec expr.Expr}
    {lvls : alloc.vec.Vec level.Level} {l_a : level.Level}
    {out : core.result.Result Unit core_types.CheckError}
    (hf : RenamesTo f g) (hst : StateWF st) (hfe : FEnvWF fe_self)
    (hty : ExprWF ty_a) (hcvj : ConstantValWF cvj) (hrhs : ExprWF rhs_a)
    (hfvs : ExprsWF fvs) (hxfvs : ExprsWF x_fvs) (hlargs : ExprsWF largs)
    (htargs : ExprsWF targs) (hl : ExprWF lhs_s) (hr : ExprWF rhs_s)
    (hla : LevelWF l_a) (hlvls : LevelsWF lvls) (hpins : ExprsWF pins)
    (hpinsf : ExprsWF pins_f)
    (h : inductives.modeled.check_iota_thm_n_ctor mode st fe_self f ty_a m_i r_p
        cvj cn_p cn_f rhs_a fvs x_fvs largs targs lhs_s rhs_s l_a lvls pins
        pins_f = ok (out, st')) :
    ∀ lst lfe lcvName, StateRel st lst → FEnvRel fe_self lfe →
      match out with
      | .Ok _ =>
        ∃ lst',
          (checkIotaThmNCtor (absMode mode) lfe g lcvName (absExpr ty_a) m_i.val
              r_p.val (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
              (absExprs fvs) (absExprs x_fvs) (absExprs largs) (absExprs targs)
              (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a) (absLevels lvls)
              (absExprs pins) (absExprs pins_f)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err e =>
        ErrSim e
          ((checkIotaThmNCtor (absMode mode) lfe g lcvName (absExpr ty_a) m_i.val
              r_p.val (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)
              (absExprs fvs) (absExprs x_fvs) (absExprs largs) (absExprs targs)
              (absExpr lhs_s) (absExpr rhs_s) (absLevel l_a) (absLevels lvls)
              (absExprs pins) (absExprs pins_f)).run lst) := by
  -- `instantiate_level_params`, `rename_consts`, `inst_pis_at`, two
  -- `checkDefEqList`s and `check_iota_thm_n_frames_refines`.  Task #59 left
  -- this `sorry` because the five `Vec` splits below were `u64 → usize` casts;
  -- task #62 swept them onto `core_k::take_exprs_n` / `drop_exprs_n`.
  intro lst lfe lcvName hrel hfer
  rw [inductives.modeled.check_iota_thm_n_ctor] at h
  obtain ⟨instTy, hinst, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hinstv, hinstwf⟩ :=
    ExprOps.instantiate_level_params_refines hcvj.2.1 hlvls hcvj.2.2 hinst
  obtain ⟨renamed, hren, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrenv, hrenwf⟩ :=
    ExprOps.rename_consts_refines _ (fun n hn r hr => hf n hn r hr) hinstwf hren
  rw [hinstv] at hrenv
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  have hve : v = pins_f := Env.exprs_copy_refines hv
  obtain ⟨spine, hspine, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hspinev, hspinewf⟩ :=
    CoreK.append_exprs_refines (by rw [hve]; exact hpinsf) hxfvs hspine
  rw [hve] at hspinev
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ExprOps.inst_pis_at_refines hrenwf hspinewf ho
  rw [hspinev, hrenv,
    show absExpr cvj.ty = (absConstantVal cvj).type from rfl,
    show absNames cvj.level_params = (absConstantVal cvj).levelParams from
      rfl] at hoabs
  cases o with
  | none =>
    -- the constructor telescope (`DeclCheck.lean:651`)
    simp at h
    obtain ⟨v1, hv1, ce, hce, rfl, rfl⟩ := h
    simp only [Option.map_none] at hoabs
    refine errSim_notImplemented
      s!"iota constructor telescope for {lcvName}" hce ?_
    rw [checkIotaThmNCtor]
    simp only [StateT.run]
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs]
  | some cq =>
  obtain ⟨cdoms, cres⟩ := cq
  obtain ⟨hcdomswf, hcreswf⟩ := howf _ rfl
  simp only [Option.map_some] at hoabs
  obtain ⟨cresArgs, hca, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hcav, hcawf⟩ := ExprOps.get_app_args_refines hcreswf hca
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  simp only [lift_eq, Result.ok.injEq] at hi1
  subst hi1
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  have hi2v : i2.val = m_i.val - r_p.val := ExprOps.sub_nat_val hi2
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
  have hi3v : i3.val = cn_p.val + i2.val := HashMap.uscalar_add_eq hi3
  have hi1v : (Std.UScalar.cast .U64 (alloc.vec.Vec.len cresArgs) : Std.U64).val
      = cresArgs.val.length := by
    rw [ExprOps.usize_cast_u64_val]
    have := alloc.vec.Vec.len_val cresArgs
    scalar_tac
  by_cases hne :
      (Std.UScalar.cast .U64 (alloc.vec.Vec.len cresArgs) : Std.U64) != i3
  · -- the constructor index tuple is the wrong length (`DeclCheck.lean:653`)
    rw [if_pos hne] at h
    simp [bind_eq_ok_iff] at h
    obtain ⟨v1, hv1, ce, hce, rfl, rfl⟩ := h
    simp only [bne_iff_ne, ne_eq] at hne
    have hidx : ¬ ((ConLeche.Expr.getAppArgs (absExpr cres)).length
        = cn_p.val + (m_i.val - r_p.val)) := by
      rw [← hcav]
      simp only [absExprs, List.length_map]
      intro hc
      exact hne (Std.UScalar.eq_of_val_eq (by rw [hi1v, hc, hi3v, hi2v]))
    refine errSim_notImplemented
      s!"iota constructor indices for {lcvName}" hce ?_
    rw [checkIotaThmNCtor]
    simp only [StateT.run]
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, ConLeche.unwrapOr, ← hoabs, hidx]
  · rw [if_neg hne] at h
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    have hidx : (ConLeche.Expr.getAppArgs (absExpr cres)).length
        = cn_p.val + (m_i.val - r_p.val) := by
      rw [← hcav]
      simp only [absExprs, List.length_map]
      rw [← hi1v, hne, hi3v, hi2v]
    obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hv2v, hv2wf⟩ := CoreK.drop_exprs_n_refines hlargs hv2
    obtain ⟨stmtIdx, hsi, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hsiv, hsiwf⟩ := CoreK.take_exprs_n_refines hv2wf hsi
    rw [hv2v, hi2v] at hsiv
    obtain ⟨ctorIdx, hci, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hciv, hciwf⟩ := CoreK.drop_exprs_n_refines hcawf hci
    rw [hcav] at hciv
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v : i4.val = r_p.val + cn_f.val := HashMap.uscalar_add_eq hi4
    obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st1⟩ := p1
    cases r1 with
    | Err e =>
      -- move 1: the index-tuple comparison threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have herr :=
        hcb.checkDefEqListErr st fe_self i4 stmtIdx ctorIdx e st1 hst hfe hsiwf
          hciwf hp1 lst lfe hrel hfer
      rw [hi4v, hsiv, hciv] at herr
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [checkIotaThmNCtor]
      simp only [StateT.run] at hle ⊢
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, ← hoabs, hidx, hle]
    | Ok u1 =>
    cases u1
    obtain ⟨lst1, hrun1, hrel1, hwf1⟩ :=
      hcb.checkDefEqList st fe_self i4 stmtIdx ctorIdx st1 hst hfe hsiwf hciwf
        hp1 lst lfe hrel hfer
    rw [hi4v, hsiv, hciv] at hrun1
    obtain ⟨xDoms, hxd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hxdv, hxdwf⟩ := hcb.fvarTypes x_fvs xDoms hxfvs hxd
    obtain ⟨cDoms, hcd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hcdv, hcdwf⟩ := CoreK.drop_exprs_n_refines hcdomswf hcd
    obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r2, st2⟩ := p2
    cases r2 with
    | Err e =>
      -- move 1: the field-domain comparison threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have herr :=
        hcb.checkDefEqListErr st1 fe_self i4 xDoms cDoms e st2 hwf1 hfe hxdwf
          hcdwf hp2 lst1 lfe hrel1 hfer
      rw [hi4v, hxdv, hcdv] at herr
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [checkIotaThmNCtor]
      simp only [StateT.run] at hrun1 hle ⊢
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, ← hoabs, hidx, hrun1, hle]
    | Ok u2 =>
    cases u2
    obtain ⟨lst2, hrun2, hrel2, hwf2⟩ :=
      hcb.checkDefEqList st1 fe_self i4 xDoms cDoms st2 hwf1 hfe hxdwf hcdwf
        hp2 lst1 lfe hrel1 hfer
    rw [hi4v, hxdv, hcdv] at hrun2
    obtain ⟨tyRenamed, htr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨htrv, htrwf⟩ :=
      ExprOps.rename_consts_refines _ (fun n hn r hr => hf n hn r hr) hty htr
    obtain ⟨pfx, hpfx, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hpfxv, hpfxwf⟩ := CoreK.take_exprs_n_refines hfvs hpfx
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho1abs, ho1wf⟩ := ExprOps.inst_pis_at_refines htrwf hpfxwf ho1
    rw [hpfxv, htrv] at ho1abs
    cases o1 with
    | none =>
      -- the recursor telescope (`DeclCheck.lean:658`)
      simp at h
      obtain ⟨v1, hv1, ce, hce, rfl, rfl⟩ := h
      simp only [Option.map_none] at ho1abs
      refine errSim_notImplemented
        s!"iota recursor telescope for {lcvName}" hce ?_
      rw [checkIotaThmNCtor]
      simp only [StateT.run] at hrun1 hrun2 ⊢
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, ← hoabs, hidx, hrun1, hrun2, ← ho1abs]
    | some rq =>
    obtain ⟨rdoms, rrest⟩ := rq
    obtain ⟨hrdomswf, hrrestwf⟩ := ho1wf _ rfl
    simp only [Option.map_some] at ho1abs
    obtain ⟨pDoms, hpd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hpdv, hpdwf⟩ := hcb.fvarTypes pfx pDoms hpfxwf hpd
    rw [hpfxv] at hpdv
    obtain ⟨p3, hp3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r3, st3⟩ := p3
    cases r3 with
    | Err e =>
      -- move 1: the recursor prefix-domain comparison threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have herr :=
        hcb.checkDefEqListErr st2 fe_self i4 pDoms rdoms e st3 hwf2 hfe hpdwf
          hrdomswf hp3 lst2 lfe hrel2 hfer
      rw [hi4v, hpdv] at herr
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [checkIotaThmNCtor]
      simp only [StateT.run] at hrun1 hrun2 hle ⊢
      simp only [List.map_take] at hle
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, ConLeche.unwrapOr, ← hoabs, hidx, hrun1, hrun2, ← ho1abs, hle]
    | Ok u3 =>
    cases u3
    obtain ⟨lst3, hrun3, hrel3, hwf3⟩ :=
      hcb.checkDefEqList st2 fe_self i4 pDoms rdoms st3 hwf2 hfe hpdwf hrdomswf
        hp3 lst2 lfe hrel2 hfer
    rw [hi4v, hpdv] at hrun3
    have hframes :=
      check_iota_thm_n_frames_refines hw hcb hf hwf3 hfe hty hcvj hrhs hfvs
        htargs hl hr hla hlvls hpins h lst3 lfe lcvName hrel3 hfer
    have htail := checkIotaThmNCtor_tail (cvName := lcvName)
      (rhsA := absExpr rhs_a) (targs := absExprs targs)
      (lhsS := absExpr lhs_s) (rhsS := absExpr rhs_s) (lA := absLevel l_a)
      (pins := absExprs pins)
      hoabs.symm hidx hrun1 hrun2 ho1abs.symm hrun3
    cases out with
    | Ok u =>
      obtain ⟨lst4, hrun4, hrel4, hwf4⟩ := hframes
      exact ⟨lst4, htail.trans hrun4, hrel4, hwf4⟩
    | Err e => exact ErrSim.of_eq hframes htail

/-- `check_iota_thm_n_ctor_refines` at a success, the pre-#67 statement. -/
theorem check_iota_thm_n_ctor_refines_ok
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
        ∧ StateRel st' lst' ∧ StateWF st' :=
  check_iota_thm_n_ctor_refines hw hcb hf hst hfe hty hcvj hrhs hfvs hxfvs
    hlargs htargs hl hr hla hlvls hpins hpinsf h


omit hw hcb in
/-- A monadic `if` distributes over a following bind.  con-leche's `do`
elaborator already duplicates the continuation into both arms, so this is what
lets a trailing `pure` be pushed to the leaves of a transcription. -/
theorem bind_iteC {a1 b1 : Type} (c : Prop) [Decidable c]
    (A B : ConLeche.Cached.CheckCM a1) (k : a1 -> ConLeche.Cached.CheckCM b1) :
    ((if c then A else B) >>= k) = if c then A >>= k else B >>= k := by
  split <;> rfl

omit hw hcb in
/-- A run that ends in a constant `pure`.  `checkIotaThmNF` closes with
`pure (.nested lvls pins)` where `checkIotaThmNCtor` closes with `()`, so the
two have to be normalised together for the composition to land. -/
theorem run_seq_pure {a1 b1 : Type} {m : ConLeche.Cached.CheckCM a1} {a : a1}
    {v : b1} {lst lst' : ConLeche.Cached.CState}
    (h : m.run lst = .ok (a, lst')) :
    ((m >>= fun _ => pure v : ConLeche.Cached.CheckCM b1)).run lst
      = .ok (v, lst') := by
  simp only [StateT.run] at h
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, h]

omit hw hcb in
/-- `run_seq_pure`'s failure twin: the sequenced action threw. -/
theorem run_seq_pure_err {a1 b1 : Type} {m : ConLeche.Cached.CheckCM a1}
    {v : b1} {lst : ConLeche.Cached.CState} {le : ConLeche.CheckError}
    (h : m.run lst = .error le) :
    ((m >>= fun _ => pure v : ConLeche.Cached.CheckCM b1)).run lst
      = .error le := by
  simp only [StateT.run] at h
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, h]

omit hw hcb in
/-- **The nested statement head's four `throw`s** (task #67): past the shape
probe, `checkIotaThmNF` opens with exactly `iotaStmtOpen`'s body. -/
theorem checkIotaThmNF_stmt_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj : ConLeche.ConstantVal}
    {pins : List ConLeche.Expr} {lvls : List ConLeche.Level}
    {lst : ConLeche.Cached.CState} {le : ConLeche.CheckError}
    (hn : ConLeche.nestedRuleShapeF lfe2 lfe cvName lps tyA mI rP cnP j
      = some (lvls, pins))
    (hle : (iotaStmtOpen lfe2 cvName lps rP cnF j).run lst = .error le) :
    (ConLeche.checkIotaThmNF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = .error le := by
  rw [iotaStmtOpen] at hle
  rw [ConLeche.checkIotaThmNF, hn]
  cases hfd : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") with
  | none =>
    rw [hfd] at hle
    simpa [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure] using hle
  | some cvt =>
  rw [hfd] at hle
  by_cases h2 : cvt.levelParams = lps
  · cases ho : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 with
    | none =>
      simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, ho] at hle ⊢
      exact hle
    | some q =>
    obtain ⟨fvs, tb⟩ := q
    by_cases h4 : ConLeche.isEqHead tb.getAppFn = true
    · by_cases h5 : tb.getAppArgs.length = 3
      · simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, ho, h4, h5] at hle
      · simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, ho, h4, h5] at hle ⊢
        exact hle
    · simp only [Bool.not_eq_true] at h4
      simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2, ho, h4] at hle ⊢
      exact hle
  · simp [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, h2] at hle ⊢
    exact hle

omit hw hcb in
/-- The nested left side's three `throw`s, as the port's one `Bool`. -/
theorem checkIotaThmNF_lhs_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA tb : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj cvt : ConLeche.ConstantVal}
    {fvs pins : List ConLeche.Expr}
    {lvls : List ConLeche.Level} {lst : ConLeche.Cached.CState}
    (hn : ConLeche.nestedRuleShapeF lfe2 lfe cvName lps tyA mI rP cnP j
      = some (lvls, pins))
    (k1 : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (k2 : cvt.levelParams = lps)
    (k3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (k4 : ConLeche.isEqHead tb.getAppFn = true)
    (k5 : tb.getAppArgs.length = 3)
    (h6 : iotaLhsPrefixOk g cvName lps mI rP fvs
        (tb.getAppArgs.getD 1 (.bvar 0))
        (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs = false) :
    ∃ s, (ConLeche.checkIotaThmNF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = .error (.notImplemented s) := by
  rw [ConLeche.checkIotaThmNF, hn, k1]
  simp only [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, k2, k3, k4, k5, beq_iff_eq, if_true]
  by_cases c1 : (tb.getAppArgs.getD 1 (ConLeche.Expr.bvar 0)).getAppFn
      = ConLeche.Expr.const (g cvName) (lps.map ConLeche.Level.param)
  · rw [if_pos c1]
    by_cases c2 : (tb.getAppArgs.getD 1 (ConLeche.Expr.bvar 0)).getAppArgs.length
        = mI + 1
    · rw [if_pos c2]
      have c3 : ¬ ((tb.getAppArgs.getD 1 (ConLeche.Expr.bvar 0)).getAppArgs.take rP
          = fvs.take rP) := by
        intro hc
        rw [iotaLhsPrefixOk, c1, c2, hc] at h6
        simp at h6
      rw [if_neg c3]
      exact ⟨_, rfl⟩
    · rw [if_neg c2]
      exact ⟨_, rfl⟩
  · rw [if_neg c1]
    exact ⟨_, rfl⟩

omit hw hcb in
/-- The nested major premise's `throw`. -/
theorem checkIotaThmNF_major_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA tb : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj cvt : ConLeche.ConstantVal}
    {fvs pins : List ConLeche.Expr}
    {lvls : List ConLeche.Level} {lst : ConLeche.Cached.CState}
    (hn : ConLeche.nestedRuleShapeF lfe2 lfe cvName lps tyA mI rP cnP j
      = some (lvls, pins))
    (k1 : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (k2 : cvt.levelParams = lps)
    (k3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (k4 : ConLeche.isEqHead tb.getAppFn = true)
    (k5 : tb.getAppArgs.length = 3)
    (h6 : iotaLhsPrefixOk g cvName lps mI rP fvs
        (tb.getAppArgs.getD 1 (.bvar 0))
        (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs = true)
    (h7 : ((tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs.getLastD (.bvar 0)
        == ConLeche.Expr.mkAppN (.const (g r.ctor) lvls)
            ((pins.map fun p => ConLeche.Expr.instSpine (fvs.take rP) (rP - 1)
              (p.renameConsts g)) ++ fvs.drop rP)) = false) :
    (ConLeche.checkIotaThmNF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = .error (.notImplemented s!"iota statement major mismatch for {cvName}") := by
  rw [ConLeche.checkIotaThmNF, hn, k1]
  simp only [iotaLhsPrefixOk, Bool.and_eq_true, beq_iff_eq] at h6
  obtain ⟨⟨hhd, har⟩, hpx⟩ := h6
  have h7' : ¬ ((tb.getAppArgs.getD 1 (ConLeche.Expr.bvar 0)).getAppArgs.getLastD
      (ConLeche.Expr.bvar 0) = ConLeche.Expr.mkAppN (.const (g r.ctor) lvls)
        ((pins.map fun p => ConLeche.Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts g)) ++ fvs.drop rP)) := by
    intro hc; rw [hc] at h7; simp at h7
  simp only [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, k2, k3, k4, k5, hhd, har, hpx, beq_iff_eq, if_true]
  rw [if_neg h7']
  rfl

omit hw hcb in
/-- The nested constructor telescope's `throw`. -/
theorem checkIotaThmNF_ctele_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA tb : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj cvt : ConLeche.ConstantVal}
    {fvs pins : List ConLeche.Expr}
    {lvls : List ConLeche.Level} {lst : ConLeche.Cached.CState}
    (hn : ConLeche.nestedRuleShapeF lfe2 lfe cvName lps tyA mI rP cnP j
      = some (lvls, pins))
    (k1 : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (k2 : cvt.levelParams = lps)
    (k3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (k4 : ConLeche.isEqHead tb.getAppFn = true)
    (k5 : tb.getAppArgs.length = 3)
    (h6 : iotaLhsPrefixOk g cvName lps mI rP fvs
        (tb.getAppArgs.getD 1 (.bvar 0))
        (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs = true)
    (h7 : ((tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs.getLastD (.bvar 0)
        == ConLeche.Expr.mkAppN (.const (g r.ctor) lvls)
            ((pins.map fun p => ConLeche.Expr.instSpine (fvs.take rP) (rP - 1)
              (p.renameConsts g)) ++ fvs.drop rP)) = true)
    (h8 : ConLeche.Expr.stripPis (cnP + cnF) cvj.type = none) :
    (ConLeche.checkIotaThmNF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = .error (.notImplemented s!"iota constructor telescope for {cvName}") := by
  rw [ConLeche.checkIotaThmNF, hn, k1]
  simp only [iotaLhsPrefixOk, Bool.and_eq_true, beq_iff_eq] at h6
  obtain ⟨⟨hhd, har⟩, hpx⟩ := h6
  simp only [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, k2, k3, k4, k5, hhd, har, hpx, h7, h8,
    beq_self_eq_true, if_true]
  rfl

omit hw hcb in
/-- The nested residual head's `throw`. -/
theorem checkIotaThmNF_rhead_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA tb cbody0 : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj cvt : ConLeche.ConstantVal}
    {fvs pins : List ConLeche.Expr}
    {cb : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {lvls : List ConLeche.Level} {lst : ConLeche.Cached.CState}
    (hn : ConLeche.nestedRuleShapeF lfe2 lfe cvName lps tyA mI rP cnP j
      = some (lvls, pins))
    (k1 : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (k2 : cvt.levelParams = lps)
    (k3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (k4 : ConLeche.isEqHead tb.getAppFn = true)
    (k5 : tb.getAppArgs.length = 3)
    (h6 : iotaLhsPrefixOk g cvName lps mI rP fvs
        (tb.getAppArgs.getD 1 (.bvar 0))
        (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs = true)
    (h7 : ((tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs.getLastD (.bvar 0)
        == ConLeche.Expr.mkAppN (.const (g r.ctor) lvls)
            ((pins.map fun p => ConLeche.Expr.instSpine (fvs.take rP) (rP - 1)
              (p.renameConsts g)) ++ fvs.drop rP)) = true)
    (h8 : ConLeche.Expr.stripPis (cnP + cnF) cvj.type = some (cb, cbody0))
    (h9 : ∀ c us, cbody0.getAppFn ≠ ConLeche.Expr.const c us) :
    (ConLeche.checkIotaThmNF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = .error (.notImplemented s!"iota constructor residual head for {cvName}") := by
  rw [ConLeche.checkIotaThmNF, hn, k1]
  simp only [iotaLhsPrefixOk, Bool.and_eq_true, beq_iff_eq] at h6
  obtain ⟨⟨hhd, har⟩, hpx⟩ := h6
  simp only [ConLeche.unwrapOr, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, k2, k3, k4, k5, hhd, har, hpx, h7, h8,
    beq_self_eq_true, if_true]
  cases hg : cbody0.getAppFn
  case const c us => exact absurd hg (h9 c us)
  all_goals rfl

omit hw hcb in
/-- `checkIotaThmNF`'s success path down to its **tail call** (task #67): the
cited body reaches `checkIotaThmNCtor`, and returns `.nested lvls pins`. -/
theorem checkIotaThmNF_tail {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA tb cbody0 : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj cvt : ConLeche.ConstantVal}
    {fvs pins : List ConLeche.Expr}
    {cb : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {lvls : List ConLeche.Level} {lst : ConLeche.Cached.CState}
    (hn : ConLeche.nestedRuleShapeF lfe2 lfe cvName lps tyA mI rP cnP j
      = some (lvls, pins))
    (k1 : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (k2 : cvt.levelParams = lps)
    (k3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (k4 : ConLeche.isEqHead tb.getAppFn = true)
    (k5 : tb.getAppArgs.length = 3)
    (h6 : iotaLhsPrefixOk g cvName lps mI rP fvs
        (tb.getAppArgs.getD 1 (.bvar 0))
        (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs = true)
    (h7 : ((tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs.getLastD (.bvar 0)
        == ConLeche.Expr.mkAppN (.const (g r.ctor) lvls)
            ((pins.map fun p => ConLeche.Expr.instSpine (fvs.take rP) (rP - 1)
              (p.renameConsts g)) ++ fvs.drop rP)) = true)
    (h8 : ConLeche.Expr.stripPis (cnP + cnF) cvj.type = some (cb, cbody0))
    (h9 : ∃ c us, cbody0.getAppFn = .const c us) :
    (ConLeche.checkIotaThmNF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = ((checkIotaThmNCtor lmode lfe g cvName tyA mI rP cvj cnP cnF rhsA fvs
          (fvs.drop rP) (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs tb.getAppArgs
          (tb.getAppArgs.getD 1 (.bvar 0)) (tb.getAppArgs.getD 2 (.bvar 0))
          (ConLeche.eqHeadLevel tb.getAppFn) lvls pins
          (pins.map fun p => ConLeche.Expr.instSpine (fvs.take rP) (rP - 1)
            (p.renameConsts g)))
        >>= fun _ => (pure (.nested lvls pins) :
          ConLeche.Cached.CheckCM ConLeche.RecRuleFire)).run lst := by
  obtain ⟨c, us, hc⟩ := h9
  rw [ConLeche.checkIotaThmNF, hn, k1]
  simp only [iotaLhsPrefixOk, Bool.and_eq_true, beq_iff_eq] at h6
  obtain ⟨⟨hhd, har⟩, hpx⟩ := h6
  simp only [ConLeche.unwrapOr, pure_bind, k2, k3, k4, k5, hhd, har, hpx, h7,
    h8, hc, beq_self_eq_true, if_true]
  refine congrArg (fun x => StateT.run x lst) ?_
  simp only [checkIotaThmNCtor, checkIotaThmNFrames, bind_assoc, bind_iteC,
    ConLeche.unwrapOr, pure_bind]

omit hw hcb in
/-- `checkIotaThmNF`'s success path, run.  Like `checkIotaThmF_run` this is
where the port's halves — `nested_rule_shape`, `iota_stmt_open`,
`inst_pins_renamed`, the major pin, the residual-head read and
`check_iota_thm_n_ctor` — are composed back into the unsplit cited body. -/
theorem checkIotaThmNF_run {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA tb cbody0 : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj cvt : ConLeche.ConstantVal}
    {fvs pins : List ConLeche.Expr}
    {cb : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {lvls : List ConLeche.Level}
    {lst lst' : ConLeche.Cached.CState}
    (hn : ConLeche.nestedRuleShapeF lfe2 lfe cvName lps tyA mI rP cnP j
      = some (lvls, pins))
    (k1 : lfe2.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt)
    (k2 : cvt.levelParams = lps)
    (k3 : ConLeche.openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tb))
    (k4 : ConLeche.isEqHead tb.getAppFn = true)
    (k5 : tb.getAppArgs.length = 3)
    (h6 : iotaLhsPrefixOk g cvName lps mI rP fvs
        (tb.getAppArgs.getD 1 (.bvar 0))
        (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs = true)
    (h7 : ((tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs.getLastD (.bvar 0)
        == ConLeche.Expr.mkAppN (.const (g r.ctor) lvls)
            ((pins.map fun p => ConLeche.Expr.instSpine (fvs.take rP) (rP - 1)
              (p.renameConsts g)) ++ fvs.drop rP)) = true)
    (h8 : ConLeche.Expr.stripPis (cnP + cnF) cvj.type = some (cb, cbody0))
    (h9 : ∃ c us, cbody0.getAppFn = .const c us)
    (h10 : (checkIotaThmNCtor lmode lfe g cvName tyA mI rP cvj cnP cnF rhsA fvs
        (fvs.drop rP) (tb.getAppArgs.getD 1 (.bvar 0)).getAppArgs tb.getAppArgs
        (tb.getAppArgs.getD 1 (.bvar 0)) (tb.getAppArgs.getD 2 (.bvar 0))
        (ConLeche.eqHeadLevel tb.getAppFn) lvls pins
        (pins.map fun p => ConLeche.Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts g))).run lst = .ok ((), lst')) :
    (ConLeche.checkIotaThmNF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r cvj cnP cnF rhsA).run lst
      = .ok (.nested lvls pins, lst') := by
  obtain ⟨c, us, hc⟩ := h9
  rw [ConLeche.checkIotaThmNF, hn, k1]
  simp only [iotaLhsPrefixOk, Bool.and_eq_true, beq_iff_eq] at h6
  obtain ⟨⟨hhd, har⟩, hpx⟩ := h6
  simp only [ConLeche.unwrapOr, pure_bind, k2, k3, k4, k5, hhd, har, hpx, h7,
    h8, hc, beq_self_eq_true, if_true]
  refine Eq.trans (congrArg (fun x => StateT.run x lst) ?_)
    (run_seq_pure (v := ConLeche.RecRuleFire.nested lvls pins) h10)
  simp only [checkIotaThmNCtor, checkIotaThmNFrames, bind_assoc, bind_iteC,
    ConLeche.unwrapOr, pure_bind]

set_option linter.unusedSimpArgs false in
/-- `ConLeche/Kernel/DeclCheck.lean:601-685` — **`check_iota_thm_n` refines
`checkIotaThmNF`**: the generalization of `checkIotaThmF` to rules whose
constructor parameters and levels are fixed instantiations.  A rule with no
certifiable shape is stored inert. -/
theorem check_iota_thm_n_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {ty_a rhs_a : expr.Expr} {m_i r_p j cn_p cn_f : Std.U64}
    {r : env.RecRule} {cvj : env.ConstantVal}
    {out : core.result.Result env.RecRuleFire core_types.CheckError}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hty : ExprWF ty_a) (hrw : RecRuleWF r) (hcvj : ConstantValWF cvj)
    (hrhs : ExprWF rhs_a)
    (h : inductives.modeled.check_iota_thm_n mode st fe2 fe_self f cv_name lps
        ty_a m_i r_p j r cvj cn_p cn_f rhs_a = ok (out, st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 → FEnvRel fe_self lfe →
      match out with
      | .Ok fire =>
        ∃ lst',
          (ConLeche.checkIotaThmNF (absMode mode)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
              (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
              j.val (absRecRule r) (absConstantVal cvj) cn_p.val cn_f.val
              (absExpr rhs_a)).run lst = .ok (absFire fire, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRuleFireWF fire
      | .Err e =>
        ErrSim e
          ((ConLeche.checkIotaThmNF (absMode mode)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
              (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
              j.val (absRecRule r) (absConstantVal cvj) cn_p.val cn_f.val
              (absExpr rhs_a)).run lst) := by
  -- `nested_rule_shape_refines`, `iota_stmt_open_refines`,
  -- `inst_pins_renamed_refines`, the major pin, the residual-head read and
  -- `check_iota_thm_n_ctor_refines`, composed back into the *unsplit* cited
  -- body by `checkIotaThmNF_run`.  Task #59 left this `sorry` because `x_fvs`
  -- and the pin prefix were `u64 -> usize` casts; task #62 made them
  -- `core_k::drop_exprs_n` / `take_exprs_n`.
  intro lst lfe2 lfe hrel hr2 hrS
  rw [inductives.modeled.check_iota_thm_n] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ :=
    nested_rule_shape_refines hw hcb hres hspines hr2 hfe2 hrS hfe hcv hlps
      hty ho
  cases o with
  | none =>
    simp only [Option.map_none] at hoabs
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lst, ?_, hrel, hst, trivial⟩
    rw [ConLeche.checkIotaThmNF, ← hoabs]
    simp [absFire, StateT.run, Pure.pure, StateT.pure, Except.pure]
  | some sq =>
  obtain ⟨lvls, pins⟩ := sq
  obtain ⟨hlvlswf, hpinswf⟩ := howf _ rfl
  simp only [Option.map_some] at hoabs
  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
  cases r1 with
  | Err err =>
    -- move 1: `iota_stmt_open` threw, and the unsplit nested body throws at
    -- the same guard (`DeclCheck.lean:608-625`)
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ErrSim.trans
      (iota_stmt_open_refines hw hcb hr2 hfe2 hcv hlps hr1 lst)
      (fun le hle => checkIotaThmNF_stmt_err hoabs.symm hle)
  | Ok oq =>
  obtain ⟨fvs, targs, l_a⟩ := oq
  obtain ⟨hopen, hfvswf, htargswf, hlawf⟩ :=
    iota_stmt_open_refines hw hcb hr2 hfe2 hcv hlps hr1
  obtain ⟨cvt, tb, k1, k2, k3, k4, k5, k6, k7⟩ := iotaStmtOpen_inv (hopen lst)
  obtain ⟨lhs_s, hlhs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlhsv, hlhswf⟩ := arg_get_d_refines htargswf hlhs
  obtain ⟨rhs_s, hrhss, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrhssv, hrhsswf⟩ := arg_get_d_refines htargswf hrhss
  rw [show ((1#usize : Std.Usize)).val = 1 from rfl, k6] at hlhsv
  rw [show ((2#usize : Std.Usize)).val = 2 from rfl, k6] at hrhssv
  obtain ⟨x_fvs, hxfvs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hxfvsv, hxfvswf⟩ := CoreK.drop_exprs_n_refines hfvswf hxfvs
  obtain ⟨pfx, hpfx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpfxv, hpfxwf⟩ := CoreK.take_exprs_n_refines hfvswf hpfx
  have hpfxlen : pfx.length ≤ r_p.val := by
    have hv := CoreK.take_exprs_n_val hpfx
    have := alloc.vec.Vec.len_val pfx
    have hl : pfx.val.length ≤ r_p.val := by
      rw [hv]; simp
    scalar_tac
  obtain ⟨pins_f, hpinsf, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpinsfv, hpinsfwf⟩ :=
    inst_pins_renamed_refines hw hcb hf hpinswf hpfxwf ExprOps.exprsWF_new
      hpfxlen hpinsf
  rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero, hpfxv,
    List.take_take, Nat.min_self,
    show absExprs (alloc.vec.Vec.new expr.Expr) = [] by
      simp [absExprs, alloc.vec.Vec.new],
    List.nil_append] at hpinsfv
  obtain ⟨largs, hlargs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlargsv, hlargswf⟩ := ExprOps.get_app_args_refines hlhswf hlargs
  rw [hlhsv] at hlargsv
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := iota_lhs_prefix_ok_refines hw hcb hspines hf hcv hlps hfvswf
    hlargswf hlhswf hb
  rw [hlhsv, hlargsv] at hbv
  by_cases hbt : b = true
  · rw [if_pos hbt] at h
    rw [hbt] at hbv
    obtain ⟨major, hmaj, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hmajv, hmajwf⟩ := arg_get_last_d_refines hlargswf hmaj
    rw [hlargsv] at hmajv
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    have hve : v = pins_f := Env.exprs_copy_refines hv
    obtain ⟨spine, hspine, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hspinev, hspinewf⟩ :=
      CoreK.append_exprs_refines (by rw [hve]; exact hpinsfwf) hxfvswf hspine
    rw [hve, hpinsfv, hxfvsv] at hspinev
    obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hnmv, hnmwf⟩ := hf r.ctor hrw.1 nm hnm
    obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
    have huse : us = lvls := Env.levels_copy_refines hus
    obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
    have hev : absExpr e
        = ConLeche.Expr.const (g (absName r.ctor)) (absLevels lvls) := by
      rw [Expr.mk_const_refines he, hnmv, huse]
    have hewf : ExprWF e :=
      ExprWF.mk_const hnmwf (by rw [huse]; exact hlvlswf) he
    obtain ⟨expMajor, hem, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hemv, hemwf⟩ := ExprOps.mk_app_n_refines hewf hspinewf hem
    rw [hev, hspinev] at hemv
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = decide (absExpr major = absExpr expMajor) :=
      Expr.beq_refines hmajwf hemwf hb1
    rw [hmajv, hemv] at hb1v
    by_cases hb1t : b1 = true
    · rw [if_pos hb1t] at h
      rw [hb1t] at hb1v
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = cn_p.val + cn_f.val := HashMap.uscalar_add_eq hi
      obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_pis_refines hcvj.2.2 ho1
      rw [hiv] at ho1abs
      cases o1 with
      | none =>
        -- the constructor telescope will not strip (`DeclCheck.lean:641`)
        simp at h
        obtain ⟨v1, hv1, ce, hce, rfl, rfl⟩ := h
        simp only [Option.map_none] at ho1abs
        exact errSim_notImplemented
          s!"iota constructor telescope for {absName cv_name}" hce
          (checkIotaThmNF_ctele_err (lmode := absMode mode) (lfe2 := lfe2) (lfe := lfe)
          (lst := lst) (tyA := absExpr ty_a) (rhsA := absExpr rhs_a)
          (j := j.val) (r := absRecRule r) (cnP := cn_p.val)
          (cvj := absConstantVal cvj)
            hoabs.symm k1 k2 k3 k4 k5 hbv.symm
            (by simpa [absRecRule] using of_decide_eq_true hb1v.symm)
            ho1abs.symm)
      | some bq =>
      obtain ⟨cbs, e1⟩ := bq
      obtain ⟨hcbswf, he1wf⟩ := ho1wf _ rfl
      simp only [Option.map_some] at ho1abs
      obtain ⟨rhead, hrhead, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hrheadv, hrheadwf⟩ := ExprOps.get_app_fn_refines he1wf hrhead
      obtain ⟨en, hen, h⟩ := bind_eq_ok_iff.mp h
      rw [arc_deref_eq, Result.ok.injEq] at hen
      subst hen
      obtain ⟨⟨dd, kk⟩⟩ := rhead
      cases kk
      case Const cn cus =>
        simp only [ExprOps.node_kind] at h
        have hconst : ∃ c cu, ConLeche.Expr.getAppFn (absExpr e1)
            = .const c cu := by
          rw [← hrheadv]
          simp only [absExpr_mk, absExprKind]
          exact ⟨_, _, rfl⟩
        have htail := checkIotaThmNF_tail (lmode := absMode mode) (lfe2 := lfe2) (lfe := lfe)
          (lst := lst) (tyA := absExpr ty_a) (rhsA := absExpr rhs_a)
          (j := j.val) (r := absRecRule r) (cnP := cn_p.val)
          (cvj := absConstantVal cvj)
          hoabs.symm k1 k2 k3 k4 k5 hbv.symm
          (by simpa [absRecRule] using of_decide_eq_true hb1v.symm)
          ho1abs.symm hconst
        obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r2, st1⟩ := p1
        have hctor :=
          check_iota_thm_n_ctor_refines hw hcb hf hst hfe hty hcvj hrhs hfvswf
            hxfvswf hlargswf htargswf hlhswf hrhsswf hlawf hlvlswf hpinswf
            hpinsfwf hp1 lst lfe (absName cv_name) hrel hrS
        rw [hxfvsv, hlargsv, k6, hlhsv, hrhssv, k7, hpinsfv] at hctor
        cases r2 with
        | Err e2 =>
          -- move 1: the constructor half threw
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact ErrSim.trans hctor
            (fun le hle => htail.trans (run_seq_pure_err hle))
        | Ok u2 =>
        cases u2
        obtain ⟨lst', hrun, hrel', hwf'⟩ := hctor
        have hx := Result.ok_injective h
        have hst1 : st1 = st' := congrArg Prod.snd hx
        have hfire : core.result.Result.Ok (env.RecRuleFire.Nested lvls pins)
            = out := congrArg Prod.fst hx
        subst hst1
        subst hfire
        refine ⟨lst', ?_, hrel', hwf', hlvlswf, hpinswf⟩
        rw [show absFire (env.RecRuleFire.Nested lvls pins)
            = ConLeche.RecRuleFire.nested (absLevels lvls) (absExprs pins)
            from rfl]
        exact htail.trans (run_seq_pure hrun)
      -- the nine other residual heads (`DeclCheck.lean:643`)
      all_goals simp only [ExprOps.node_kind] at h
      all_goals simp [bind_eq_ok_iff] at h
      all_goals obtain ⟨v1, hv1, ce, hce, rfl, rfl⟩ := h
      all_goals
        refine errSim_notImplemented
          s!"iota constructor residual head for {absName cv_name}" hce
          (checkIotaThmNF_rhead_err (lmode := absMode mode) (lfe2 := lfe2) (lfe := lfe)
          (lst := lst) (tyA := absExpr ty_a) (rhsA := absExpr rhs_a)
          (j := j.val) (r := absRecRule r) (cnP := cn_p.val)
          (cvj := absConstantVal cvj)
            hoabs.symm k1 k2 k3 k4 k5 hbv.symm
            (by simpa [absRecRule] using of_decide_eq_true hb1v.symm)
            ho1abs.symm (fun c us hc => ?_))
      all_goals rw [← hrheadv] at hc
      all_goals simp only [absExpr_mk, absExprKind] at hc
      all_goals exact ConLeche.Expr.noConfusion hc
    · -- the major premise mismatch (`DeclCheck.lean:638`)
      simp only [Bool.not_eq_true] at hb1t
      rw [if_neg (by simp [hb1t])] at h
      simp [bind_eq_ok_iff] at h
      obtain ⟨v1, hv1, ce, hce, rfl, rfl⟩ := h
      rw [hb1t] at hb1v
      exact errSim_notImplemented
        s!"iota statement major mismatch for {absName cv_name}" hce
        (checkIotaThmNF_major_err (lmode := absMode mode) (lfe2 := lfe2) (lfe := lfe)
          (lst := lst) (tyA := absExpr ty_a) (rhsA := absExpr rhs_a)
          (j := j.val) (r := absRecRule r) (cnP := cn_p.val)
          (cvj := absConstantVal cvj)
          hoabs.symm k1 k2 k3 k4 k5 hbv.symm
          (by simpa [absRecRule] using of_decide_eq_false hb1v.symm))
  · -- the left side head, arity or prefix (`DeclCheck.lean:630-634`)
    simp only [Bool.not_eq_true] at hbt
    rw [if_neg (by simp [hbt])] at h
    simp [bind_eq_ok_iff] at h
    obtain ⟨v1, hv1, ce, hce, rfl, rfl⟩ := h
    rw [hbt] at hbv
    exact errSim_notImplemented' hce
      (checkIotaThmNF_lhs_err (lmode := absMode mode) (lfe2 := lfe2) (lfe := lfe)
          (lst := lst) (tyA := absExpr ty_a) (rhsA := absExpr rhs_a)
          (j := j.val) (r := absRecRule r) (cnP := cn_p.val)
          (cvj := absConstantVal cvj)
        hoabs.symm k1 k2 k3 k4 k5 hbv.symm)

/-- `check_iota_thm_n_refines` at a success, the pre-#67 statement. -/
theorem check_iota_thm_n_refines_ok
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {ty_a rhs_a : expr.Expr} {m_i r_p j cn_p cn_f : Std.U64}
    {r : env.RecRule} {cvj : env.ConstantVal} {fire : env.RecRuleFire}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
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
        ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRuleFireWF fire :=
  check_iota_thm_n_refines hw hcb hres hspines hf hst hfe2 hfe hcv hlps hty hrw
    hcvj hrhs h


/-! ## The rules (`Modeled.lean:319-371`, `DeclCheck.lean:687-727`) -/

set_option linter.unusedSectionVars false in
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
  rw [inductives.modeled.iota_rule_stored] at h
  obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
  have hnmv : nm = r.ctor := by
    rw [name_dup_eq] at hnm; exact (Result.ok_injective hnm).symm
  rw [hnmv] at h
  have hrl : RecRuleWF
      { r with
        ctor := r.ctor, ctor_params := cn_p, fire := fire, rhs := rhs_a,
        params_blind := false } :=
    ⟨hr.1, hfire, hrhs⟩
  obtain ⟨habs, hwf⟩ :=
    CoreK.rec_rule_bits_refines CoreK.envFacts (FindAgree.of_rel hrel hfe)
      (FindWF.of_wf hfe) hcv hrl h
  refine ⟨?_, hwf⟩
  rw [habs]
  rfl

omit hw hcb in
/-- `checkIotaRuleFire`'s plain arm, run. -/
theorem checkIotaRuleFire_plain_run {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA : ConLeche.Expr} {mI rP j cnP cnF : Nat} {r : ConLeche.RecRule}
    {cvj : ConLeche.ConstantVal} {lst lst1 : ConLeche.Cached.CState}
    (hp : ConLeche.Expr.recRulePlain tyA mI rP cnP = true)
    (h1 : (ConLeche.checkIotaThmF lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe2 lfe g cvName lps tyA mI rP
        j r cvj cnP cnF rhsA).run lst = .ok ((), lst1)) :
    (checkIotaRuleFire lmode lfe2 lfe g cvName lps tyA mI rP j r cvj cnP cnF
        rhsA).run lst
      = .ok (ConLeche.recRuleBits lfe2.find? cvName
          { r with rhs := rhsA, ctorParams := cnP,
                   fire := ConLeche.RecRuleFire.plain,
                   paramsBlind := false }, lst1) := by
  rw [checkIotaRuleFire]
  simp only [StateT.run] at h1
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, hp, h1]

omit hw hcb in
/-- `checkIotaRuleFire`'s nested arm, run. -/
theorem checkIotaRuleFire_nested_run {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA : ConLeche.Expr} {mI rP j cnP cnF : Nat} {r : ConLeche.RecRule}
    {cvj : ConLeche.ConstantVal} {fire : ConLeche.RecRuleFire}
    {lst lst1 : ConLeche.Cached.CState}
    (hp : ConLeche.Expr.recRulePlain tyA mI rP cnP = false)
    (h1 : (ConLeche.checkIotaThmNF lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe2 lfe g cvName lps tyA mI rP
        j r cvj cnP cnF rhsA).run lst = .ok (fire, lst1)) :
    (checkIotaRuleFire lmode lfe2 lfe g cvName lps tyA mI rP j r cvj cnP cnF
        rhsA).run lst
      = .ok (ConLeche.recRuleBits lfe2.find? cvName
          { r with rhs := rhsA, ctorParams := cnP, fire := fire,
                   paramsBlind := false }, lst1) := by
  rw [checkIotaRuleFire]
  simp only [StateT.run] at h1
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, hp, h1]

omit hw hcb in
/-- `checkIotaRuleFire`'s two arms at a `throw` (task #67): whichever of the
two iota checks the firing-mode decision selected, its error is the whole
block's. -/
theorem checkIotaRuleFire_plain_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA : ConLeche.Expr} {mI rP j cnP cnF : Nat} {r : ConLeche.RecRule}
    {cvj : ConLeche.ConstantVal} {lst : ConLeche.Cached.CState}
    {le : ConLeche.CheckError}
    (hp : ConLeche.Expr.recRulePlain tyA mI rP cnP = true)
    (h1 : (ConLeche.checkIotaThmF lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe2 lfe g cvName lps tyA mI rP
        j r cvj cnP cnF rhsA).run lst = .error le) :
    (checkIotaRuleFire lmode lfe2 lfe g cvName lps tyA mI rP j r cvj cnP cnF
        rhsA).run lst = .error le := by
  rw [checkIotaRuleFire]
  simp only [StateT.run] at h1
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, hp, h1]

omit hw hcb in
/-- The same in the nested arm. -/
theorem checkIotaRuleFire_nested_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA : ConLeche.Expr} {mI rP j cnP cnF : Nat} {r : ConLeche.RecRule}
    {cvj : ConLeche.ConstantVal} {lst : ConLeche.Cached.CState}
    {le : ConLeche.CheckError}
    (hp : ConLeche.Expr.recRulePlain tyA mI rP cnP = false)
    (h1 : (ConLeche.checkIotaThmNF lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe2 lfe g cvName lps tyA mI rP
        j r cvj cnP cnF rhsA).run lst = .error le) :
    (checkIotaRuleFire lmode lfe2 lfe g cvName lps tyA mI rP j r cvj cnP cnF
        rhsA).run lst = .error le := by
  rw [checkIotaRuleFire]
  simp only [StateT.run] at h1
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, hp, h1]

set_option linter.unusedSimpArgs false in
/-- `ConLeche/Kernel/DeclCheck.lean:706-716` — `check_iota_rule_fire` refines
`checkIotaRuleFire`: the firing-mode decision and the stored rule. -/
theorem check_iota_rule_fire_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {ty_a rhs_a : expr.Expr} {m_i r_p j cn_p cn_f : Std.U64}
    {r : env.RecRule} {cvj : env.ConstantVal}
    {out : core.result.Result env.RecRule core_types.CheckError}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hty : ExprWF ty_a) (hrw : RecRuleWF r) (hcvj : ConstantValWF cvj)
    (hrhs : ExprWF rhs_a)
    (h : inductives.modeled.check_iota_rule_fire mode st fe2 fe_self f cv_name
        lps ty_a m_i r_p j r cvj cn_p cn_f rhs_a = ok (out, st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 → FEnvRel fe_self lfe →
      match out with
      | .Ok r' =>
        ∃ lst',
          (checkIotaRuleFire (absMode mode) lfe2 lfe g (absName cv_name)
              (absNames lps) (absExpr ty_a) m_i.val r_p.val j.val (absRecRule r)
              (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)).run lst
            = .ok (absRecRule r', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRuleWF r'
      | .Err e =>
        ErrSim e
          ((checkIotaRuleFire (absMode mode) lfe2 lfe g (absName cv_name)
              (absNames lps) (absExpr ty_a) m_i.val r_p.val j.val (absRecRule r)
              (absConstantVal cvj) cn_p.val cn_f.val (absExpr rhs_a)).run lst) := by
  intro lst lfe2 lfe hrel hr2 hrS
  rw [inductives.modeled.check_iota_rule_fire] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := ExprOps.rec_rule_plain_refines hty hb
  by_cases hbt : b = true
  · rw [if_pos hbt] at h
    rw [hbt] at hbv
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st1⟩ := p
    cases r1 with
    | Err err =>
      -- move 1: the canonical iota check threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ErrSim.trans
        (check_iota_thm_refines hw hcb hspines hf hst hfe2 hfe hcv hlps hty hrw
          hcvj hrhs hp lst lfe2 lfe hrel hr2 hrS)
        (fun le hle => checkIotaRuleFire_plain_err hbv.symm hle)
    | Ok u =>
    cases u
    obtain ⟨lst1, hrun1, hrel1, hwf1⟩ :=
      check_iota_thm_refines hw hcb hspines hf hst hfe2 hfe hcv hlps hty hrw
        hcvj hrhs
        hp lst lfe2 lfe hrel hr2 hrS
    obtain ⟨rr, hrr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hrrv, hrrwf⟩ :=
      iota_rule_stored_refines hw hcb hr2 hfe2 hcv hrw
        (show RecRuleFireWF env.RecRuleFire.Plain from trivial) hrhs hrr
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lst1, ?_, hrel1, hwf1, hrrwf⟩
    rw [hrrv]
    exact checkIotaRuleFire_plain_run hbv.symm hrun1
  · simp only [Bool.not_eq_true] at hbt
    rw [if_neg (by simp [hbt])] at h
    rw [hbt] at hbv
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st1⟩ := p
    cases r1 with
    | Err err =>
      -- move 1: the nested iota check threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ErrSim.trans
        (check_iota_thm_n_refines hw hcb hres hspines hf hst hfe2 hfe hcv hlps
          hty hrw hcvj hrhs hp lst lfe2 lfe hrel hr2 hrS)
        (fun le hle => checkIotaRuleFire_nested_err hbv.symm hle)
    | Ok fr =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hfrwf⟩ :=
      check_iota_thm_n_refines hw hcb hres hspines hf hst hfe2 hfe hcv hlps hty hrw
        hcvj hrhs hp lst lfe2 lfe hrel hr2 hrS
    obtain ⟨rr, hrr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hrrv, hrrwf⟩ :=
      iota_rule_stored_refines hw hcb hr2 hfe2 hcv hrw hfrwf hrhs hrr
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lst1, ?_, hrel1, hwf1, hrrwf⟩
    rw [hrrv]
    exact checkIotaRuleFire_nested_run hbv.symm hrun1

/-- `check_iota_rule_fire_refines` at a success, the pre-#67 statement. -/
theorem check_iota_rule_fire_refines_ok
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {ty_a rhs_a : expr.Expr} {m_i r_p j cn_p cn_f : Std.U64}
    {r r' : env.RecRule} {cvj : env.ConstantVal}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
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
        ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRuleWF r' :=
  check_iota_rule_fire_refines hw hcb hres hspines hf hst hfe2 hfe hcv hlps hty
    hrw hcvj hrhs h


omit hw hcb in
/-- `checkIotaRuleF`'s head discharged: past the constructor lookup, the four
syntactic guards, the annotation and the residual `inferType`, the cited body
*is* `checkIotaRuleFire` (the port's split point). -/
theorem checkIotaRuleF_tail {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA rhsTy : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r : ConLeche.RecRule} {cvj : ConLeche.ConstantVal}
    {bs : List (ConLeche.Expr × ConLeche.BinderMeta)} {bd : ConLeche.Expr}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (hfind : lfe2.find? r.ctor = some (.ctorInfo cvj cnP cnF))
    (hnf : r.nfields = cnF)
    (hbv : r.rhs.looseBVarsBounded 0 = true)
    (hfv : r.rhs.hasFvar = false)
    (hann : ((ConLeche.Cached.sharedOpsC lmode lfe).annotate lfe.env 0
        r.rhs).run lst = .ok (rhsA, lst1))
    (hlp : ConLeche.Expr.allLevelParamsDefined lps rhsA = true)
    (hcr : rhsA.constsResolveF lfe = true)
    (hsl : rhsA.stripLams (rP + cnF) = some (bs, bd))
    (hinf : ((ConLeche.Cached.sharedOpsC lmode lfe).inferType lfe.env 0
        rhsA).run lst1 = .ok (rhsTy, lst2)) :
    (ConLeche.checkIotaRuleF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r).run lst
      = (checkIotaRuleFire lmode lfe2 lfe g cvName lps tyA mI rP j r cvj
          cnP cnF rhsA).run lst2 := by
  rw [ConLeche.checkIotaRuleF, checkIotaRuleFire]
  simp only [StateT.run] at hann hinf ⊢
  simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, hfind,
    hnf, hbv, hfv, hann, hlp, hcr, hsl, hinf]

omit hw hcb in
/-- `checkIotaRuleF`'s success path, run: `checkIotaRuleF_tail` composed with a
`checkIotaRuleFire` that also succeeded. -/
theorem checkIotaRuleF_run {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name}
    {tyA rhsA rhsTy : ConLeche.Expr} {mI rP j cnP cnF : Nat}
    {r r' : ConLeche.RecRule} {cvj : ConLeche.ConstantVal}
    {bs : List (ConLeche.Expr × ConLeche.BinderMeta)} {bd : ConLeche.Expr}
    {lst lst1 lst2 lst3 : ConLeche.Cached.CState}
    (hfind : lfe2.find? r.ctor = some (.ctorInfo cvj cnP cnF))
    (hnf : r.nfields = cnF)
    (hbv : r.rhs.looseBVarsBounded 0 = true)
    (hfv : r.rhs.hasFvar = false)
    (hann : ((ConLeche.Cached.sharedOpsC lmode lfe).annotate lfe.env 0
        r.rhs).run lst = .ok (rhsA, lst1))
    (hlp : ConLeche.Expr.allLevelParamsDefined lps rhsA = true)
    (hcr : rhsA.constsResolveF lfe = true)
    (hsl : rhsA.stripLams (rP + cnF) = some (bs, bd))
    (hinf : ((ConLeche.Cached.sharedOpsC lmode lfe).inferType lfe.env 0
        rhsA).run lst1 = .ok (rhsTy, lst2))
    (hfire : (checkIotaRuleFire lmode lfe2 lfe g cvName lps tyA mI rP j r cvj
        cnP cnF rhsA).run lst2 = .ok (r', lst3)) :
    (ConLeche.checkIotaRuleF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r).run lst = .ok (r', lst3) :=
  (checkIotaRuleF_tail hfind hnf hbv hfv hann hlp hcr hsl hinf).trans hfire

omit hw hcb in
/-- `checkIotaRuleF`'s **first** `throw` (task #67): the rule's constructor is
not a stored `ctorInfo`, which is exactly what `core_k::ctor_probe` answering
`None` says (`CoreK.ctorOf` is its reading). -/
theorem checkIotaRuleF_ctor_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name} {tyA : ConLeche.Expr}
    {mI rP j : Nat} {r : ConLeche.RecRule} {lst : ConLeche.Cached.CState}
    (hfind : CoreK.ctorOf (lfe2.find? r.ctor) = none) :
    (ConLeche.checkIotaRuleF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j r).run lst
      = .error (.invalid s!"iota rule constructor {r.ctor} not stored") := by
  rw [ConLeche.checkIotaRuleF]
  cases hx : lfe2.find? r.ctor with
  | none => rfl
  | some ci =>
    rw [hx] at hfind
    cases ci <;> first | rfl | simp [CoreK.ctorOf] at hfind

set_option linter.unusedSimpArgs false in
/-- `ConLeche/Kernel/DeclCheck.lean:687-716` — **`check_iota_rule` refines
`checkIotaRuleF`**: generic well-formedness of the right-hand side, then the
model's `iota_j` theorem. -/
theorem check_iota_rule_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name} {ty_a : expr.Expr}
    {m_i r_p j : Std.U64} {r : env.RecRule}
    {out : core.result.Result env.RecRule core_types.CheckError}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hty : ExprWF ty_a) (hrw : RecRuleWF r)
    (h : inductives.modeled.check_iota_rule mode st fe2 fe_self f cv_name lps
        ty_a m_i r_p j r = ok (out, st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 → FEnvRel fe_self lfe →
      match out with
      | .Ok r' =>
        ∃ lst',
          (ConLeche.checkIotaRuleF (absMode mode)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
              (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
              j.val (absRecRule r)).run lst = .ok (absRecRule r', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRuleWF r'
      | .Err e =>
        ErrSim e
          ((ConLeche.checkIotaRuleF (absMode mode)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
              (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
              j.val (absRecRule r)).run lst) := by
  intro lst lfe2 lfe hrel hr2 hrS
  rw [inductives.modeled.check_iota_rule] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ :=
    CoreK.ctor_probe_refines (FindAgree.of_rel hr2 hfe2) (FindWF.of_wf hfe2)
      hrw.1 ho
  cases o with
  | none =>
    -- the rule's constructor is not stored (`DeclCheck.lean:690`)
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    simp only [Option.map_none] at hoabs
    exact errSim_invalid
      s!"iota rule constructor {absName r.ctor} not stored" hce
      (checkIotaRuleF_ctor_err hoabs.symm)
  | some cq =>
  obtain ⟨cvj, cn_p, cn_f⟩ := cq
  have hcvjwf : ConstantValWF cvj := howf cvj cn_p cn_f rfl
  simp only [Option.map_some] at hoabs
  have hfind : lfe2.find? (absName r.ctor)
      = some (.ctorInfo (absConstantVal cvj) cn_p.val cn_f.val) :=
    ctorOf_inv (by simpa using hoabs.symm)
  have hctor : (absRecRule r).ctor = absName r.ctor := rfl
  have hrhsr : (absRecRule r).rhs = absExpr r.rhs := rfl
  have hnfr : (absRecRule r).nfields = r.nfields.val := rfl
  have hzero : ((0#u64 : Std.U64)).val = 0 := rfl
  simp at h
  by_cases hnf : r.nfields.val = cn_f.val
  · rw [if_pos hnf] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbv := ExprOps.loose_bvars_bounded_refines hrw.2.2 hb
    rw [hzero] at hbv
    by_cases hbt : b = true
    · rw [if_pos hbt] at h
      rw [hbt] at hbv
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := ExprOps.has_fvar_refines hrw.2.2 hb1
      by_cases hb1t : b1 = true
      · -- the free variable (`DeclCheck.lean:695`)
        rw [if_pos hb1t] at h
        simp at h
        obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
        rw [hb1t] at hb1v
        refine errSim_invalid
          s!"free variable in rule of {absName cv_name}" hce ?_
        rw [ConLeche.checkIotaRuleF]
        simp [StateT.run, Bind.bind, StateT.bind, Except.bind,
          Pure.pure, StateT.pure, Except.pure, hctor, hrhsr, hnfr,
          hzero,
          hfind, hnf, hbv.symm, hb1v.symm]
      · simp only [Bool.not_eq_true] at hb1t
        rw [hb1t] at hb1v
        rw [if_neg (by simp [hb1t])] at h
        obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r1, st1⟩ := p
        cases r1 with
        | Err err =>
          -- move 1: `core_c::annotate` threw
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          have herr :=
            IndAbs.ops_annotate_err hw hst hfe hrw.2.2 hp lst lfe hrel hrS
          rw [hrS.1] at herr
          refine ErrSim.trans herr (fun le hle => ?_)
          rw [ConLeche.checkIotaRuleF]
          simp only [StateT.run, hzero] at hle ⊢
          simp [StateT.run, Bind.bind, StateT.bind, Except.bind,
            Pure.pure, StateT.pure, Except.pure, hctor, hrhsr, hnfr,
            hzero,
            hfind, hnf, hbv.symm, hb1v.symm, hle]
        | Ok rhs_a =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, hrhswf⟩ :=
          IndAbs.ops_annotate hw hst hfe hrw.2.2 hp lst lfe hrel hrS
        rw [hrS.1] at hrun1
        obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
        have hb2v :=
          ExprOps.all_level_params_defined_fast_refines hlps hrhswf hb2
        by_cases hb2t : b2 = true
        · rw [if_pos hb2t] at h
          rw [hb2t] at hb2v
          obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
          have hb3v := hres fe_self lfe rhs_a b3 hrS hfe hrhswf hb3
          by_cases hb3t : b3 = true
          · rw [if_pos hb3t] at h
            rw [hb3t] at hb3v
            obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
            have hi1v : i1.val = r_p.val + cn_f.val := HashMap.uscalar_add_eq hi1
            obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_lams_refines hrhswf ho1
            rw [hi1v] at ho1abs
            cases o1 with
            | none =>
              -- the rule shape (`DeclCheck.lean:702`)
              simp at h
              obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
              simp only [Option.map_none] at ho1abs
              refine errSim_notImplemented
                s!"rule shape mismatch for {absName cv_name}" hce ?_
              rw [ConLeche.checkIotaRuleF]
              simp only [StateT.run, hzero] at hrun1 ⊢
              simp [StateT.run, Bind.bind, StateT.bind, Except.bind,
                Pure.pure, StateT.pure, Except.pure, hctor, hrhsr, hnfr,
                hzero,
                hfind, hnf, hbv.symm, hb1v.symm, hrun1, hb2v.symm, hb3v.symm, ← ho1abs]
            | some sq =>
            obtain ⟨bs, bd⟩ := sq
            simp only [Option.map_some] at ho1abs
            rw [if_neg (by simp)] at h
            obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨r2, st2⟩ := p2
            cases r2 with
            | Err err =>
              -- move 1: `core_c::infer` threw
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              have herr :=
                IndAbs.ops_infer_err hw hwf1 hfe hrhswf hp2 lst1 lfe hrel1 hrS
              rw [hrS.1] at herr
              refine ErrSim.trans herr (fun le hle => ?_)
              rw [ConLeche.checkIotaRuleF]
              simp only [StateT.run, hzero] at hrun1 hle ⊢
              simp [StateT.run, Bind.bind, StateT.bind, Except.bind,
                Pure.pure, StateT.pure, Except.pure, hctor, hrhsr, hnfr,
                hzero,
                hfind, hnf, hbv.symm, hb1v.symm, hrun1, hb2v.symm, hb3v.symm, ← ho1abs, hle]
            | Ok rhsTy =>
            obtain ⟨lst2, hrun2, hrel2, hwf2, hrhsTywf⟩ :=
              IndAbs.ops_infer hw hwf1 hfe hrhswf hp2 lst1 lfe hrel1 hrS
            rw [hrS.1] at hrun2
            have hfire :=
              check_iota_rule_fire_refines hw hcb hres hspines hf hwf2 hfe2 hfe hcv
                hlps hty hrw hcvjwf hrhswf h lst2 lfe2 lfe hrel2 hr2 hrS
            have htail := checkIotaRuleF_tail (lmode := absMode mode)
              (lfe2 := lfe2) (lfe := lfe) (lst := lst) (g := g)
              (cvName := absName cv_name) (lps := absNames lps)
              (tyA := absExpr ty_a) (mI := m_i.val) (rP := r_p.val)
              (j := j.val) (r := absRecRule r)
              hfind (by rw [hnfr]; exact hnf) hbv.symm hb1v.symm hrun1
              hb2v.symm hb3v.symm ho1abs.symm hrun2
            cases out with
            | Ok r' =>
              obtain ⟨lst3, hrun3, hrel3, hwf3, hr'wf⟩ := hfire
              exact ⟨lst3, htail.trans hrun3, hrel3, hwf3, hr'wf⟩
            | Err e => exact ErrSim.of_eq hfire htail

          · -- the unresolved constant (`DeclCheck.lean:700`)
            simp only [Bool.not_eq_true] at hb3t
            rw [if_neg (by simp [hb3t])] at h
            simp at h
            obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
            rw [hb3t] at hb3v
            refine errSim_invalid
              s!"unknown constant in rule of {absName cv_name}" hce ?_
            rw [ConLeche.checkIotaRuleF]
            simp only [StateT.run, hzero] at hrun1 ⊢
            simp [StateT.run, Bind.bind, StateT.bind, Except.bind,
              Pure.pure, StateT.pure, Except.pure, hctor, hrhsr, hnfr,
              hzero,
              hfind, hnf, hbv.symm, hb1v.symm, hrun1, hb2v.symm, hb3v.symm]
        · -- the undeclared universe parameter (`DeclCheck.lean:698`)
          simp only [Bool.not_eq_true] at hb2t
          rw [if_neg (by simp [hb2t])] at h
          simp at h
          obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
          rw [hb2t] at hb2v
          refine errSim_invalid
            s!"undeclared universe parameter in rule of {absName cv_name}" hce ?_
          rw [ConLeche.checkIotaRuleF]
          simp only [StateT.run, hzero] at hrun1 ⊢
          simp [StateT.run, Bind.bind, StateT.bind, Except.bind,
            Pure.pure, StateT.pure, Except.pure, hctor, hrhsr, hnfr,
            hzero,
            hfind, hnf, hbv.symm, hb1v.symm, hrun1, hb2v.symm]
    · -- the loose bound variable (`DeclCheck.lean:693`)
      simp only [Bool.not_eq_true] at hbt
      rw [if_neg (by simp [hbt])] at h
      simp at h
      obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
      rw [hbt] at hbv
      refine errSim_invalid
        s!"loose bound variable in rule of {absName cv_name}" hce ?_
      rw [ConLeche.checkIotaRuleF]
      simp [StateT.run, Bind.bind, StateT.bind, Except.bind,
        Pure.pure, StateT.pure, Except.pure, hctor, hrhsr, hnfr,
        hzero,
        hfind, hnf, hbv.symm]
  · -- the field count (`DeclCheck.lean:691`)
    rw [if_neg hnf] at h
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    refine errSim_invalid "rule field count mismatch" hce ?_
    rw [ConLeche.checkIotaRuleF]
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind,
      Pure.pure, StateT.pure, Except.pure, hctor, hrhsr, hnfr, hzero,
      hfind, hnf]


/-- `check_iota_rule_refines` at a success, the pre-#67 statement. -/
theorem check_iota_rule_refines_ok
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name} {ty_a : expr.Expr}
    {m_i r_p j : Std.U64} {r r' : env.RecRule}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
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
        ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRuleWF r' :=
  check_iota_rule_refines hw hcb hres hspines hf hst hfe2 hfe hcv hlps hty hrw h

omit hw hcb in
/-- `checkIotaRulesF`'s cons step, run: one rule checked, the tail folded. -/
theorem checkIotaRulesF_cons {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name} {tyA : ConLeche.Expr}
    {mI rP j : Nat} {r r' : ConLeche.RecRule}
    {rest rest' : List ConLeche.RecRule}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (h1 : (ConLeche.checkIotaRuleF lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe2 lfe g cvName lps tyA mI rP
        j r).run lst = .ok (r', lst1))
    (h2 : (ConLeche.checkIotaRulesF lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe2 lfe g cvName lps tyA mI rP
        (j + 1) rest).run lst1 = .ok (rest', lst2)) :
    (ConLeche.checkIotaRulesF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j (r :: rest)).run lst
      = .ok (r' :: rest', lst2) := by
  rw [ConLeche.checkIotaRulesF]
  simp only [StateT.run] at h1 h2
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, h1, h2]

omit hw hcb in
/-- `checkIotaRulesF` at a cons whose **head** threw (task #67). -/
theorem checkIotaRulesF_head_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name} {tyA : ConLeche.Expr}
    {mI rP j : Nat} {r : ConLeche.RecRule} {rest : List ConLeche.RecRule}
    {lst : ConLeche.Cached.CState} {le : ConLeche.CheckError}
    (h1 : (ConLeche.checkIotaRuleF lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe2 lfe g cvName lps tyA mI rP
        j r).run lst = .error le) :
    (ConLeche.checkIotaRulesF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j (r :: rest)).run lst = .error le := by
  rw [ConLeche.checkIotaRulesF]
  simp only [StateT.run] at h1
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, h1]

omit hw hcb in
/-- `checkIotaRulesF` at a cons whose **tail** threw. -/
theorem checkIotaRulesF_tail_err {lmode : ConLeche.CheckMode}
    {lfe2 lfe : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {cvName : ConLeche.Name} {lps : List ConLeche.Name} {tyA : ConLeche.Expr}
    {mI rP j : Nat} {r r' : ConLeche.RecRule} {rest : List ConLeche.RecRule}
    {lst lst1 : ConLeche.Cached.CState} {le : ConLeche.CheckError}
    (h1 : (ConLeche.checkIotaRuleF lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe2 lfe g cvName lps tyA mI rP
        j r).run lst = .ok (r', lst1))
    (h2 : (ConLeche.checkIotaRulesF lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe2 lfe g cvName lps tyA mI rP
        (j + 1) rest).run lst1 = .error le) :
    (ConLeche.checkIotaRulesF lmode (ConLeche.Cached.sharedOpsC lmode lfe) lfe2
        lfe g cvName lps tyA mI rP j (r :: rest)).run lst = .error le := by
  rw [ConLeche.checkIotaRulesF]
  simp only [StateT.run] at h1 h2
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, h1, h2]

/-- `check_iota_rules`' index recursion on `rules.len() - i`. -/
theorem check_iota_rules_val
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    (hf : RenamesTo f g) {fe2 fe_self : fenv.FEnv} (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) {cv_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {ty_a : expr.Expr} {m_i r_p : Std.U64}
    (hcv : NameWF cv_name) (hlps : NamesWF lps) (hty : ExprWF ty_a)
    {rules : alloc.vec.Vec env.RecRule} (hrules : RecRulesWF rules) :
    ∀ n : Nat, ∀ (st st' : cached.state_c.CState) (j : Std.U64)
      (i : Std.Usize) (out : alloc.vec.Vec env.RecRule)
      (o : core.result.Result (alloc.vec.Vec env.RecRule)
        core_types.CheckError),
      rules.length - i.val ≤ n → StateWF st → RecRulesWF out →
      inductives.modeled.check_iota_rules mode st fe2 fe_self f cv_name lps
        ty_a m_i r_p j rules i out = ok (o, st') →
      ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 →
        FEnvRel fe_self lfe →
        match o with
        | .Ok v =>
          ∃ lst',
            (ConLeche.checkIotaRulesF (absMode mode)
                (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
                (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
                j.val ((absRecRules rules).drop i.val)).run lst
              = .ok ((absRecRules v).drop (absRecRules out).length, lst')
            ∧ absRecRules v
                = absRecRules out ++ (absRecRules v).drop (absRecRules out).length
            ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRulesWF v
        | .Err e =>
          ErrSim e
            ((ConLeche.checkIotaRulesF (absMode mode)
                (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
                (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
                j.val ((absRecRules rules).drop i.val)).run lst) := by
  intro n
  induction n with
  | zero =>
    intro st st' j i out o hk hst hout h lst lfe2 lfe hrel hr2 hrS
    rw [inductives.modeled.check_iota_rules,
      if_pos (show i ≥ alloc.vec.Vec.len rules by
        have := alloc.vec.Vec.len_val rules; scalar_tac), Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hnil : (absRecRules rules).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absRecRules, List.length_map]
      scalar_tac
    refine ⟨lst, ?_, ?_, hrel, hst, hout⟩
    · rw [hnil, ConLeche.checkIotaRulesF]
      simp [StateT.run, Pure.pure, StateT.pure, Except.pure]
    · simp
  | succ n ih =>
    intro st st' j i out o hk hst hout h lst lfe2 lfe hrel hr2 hrS
    rw [inductives.modeled.check_iota_rules] at h
    by_cases hi : i.val ≥ rules.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len rules by
        have := alloc.vec.Vec.len_val rules; scalar_tac), Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hnil : (absRecRules rules).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absRecRules, List.length_map]
        scalar_tac
      refine ⟨lst, ?_, ?_, hrel, hst, hout⟩
      · rw [hnil, ConLeche.checkIotaRulesF]
        simp [StateT.run, Pure.pure, StateT.pure, Except.pure]
      · simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len rules by
        have := alloc.vec.Vec.len_val rules; scalar_tac)] at h
      have hlt : i.val < rules.val.length := by
        have := alloc.vec.Vec.len_val rules; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rules i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      have hrrwf : RecRuleWF rules.val[i.val] := hrules _ (List.getElem_mem hlt)
      obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r0, st1⟩ := p
      have hcons : (absRecRules rules).drop i.val
          = absRecRule rules.val[i.val] :: (absRecRules rules).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa [absRecRules] using hlt)]
        simp [absRecRules]
      cases r0 with
      | Err err =>
        -- move 1: the rule at the cursor threw
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hcons]
        exact ErrSim.trans
          (check_iota_rule_refines hw hcb hres hspines hf hst hfe2 hfe hcv hlps
            hty hrrwf hp lst lfe2 lfe hrel hr2 hrS)
          (fun le hle => checkIotaRulesF_head_err hle)
      | Ok r2 =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, hr2wf⟩ :=
        check_iota_rule_refines hw hcb hres hspines hf hst hfe2 hfe hcv hlps
          hty hrrwf
          hp lst lfe2 lfe hrel hr2 hrS
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j2, hj2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      have hj2v : j2.val = j.val + 1 := HashMap.uscalar_add_eq hj2
      have hi3v : i3.val = i.val + 1 := HashMap.uscalar_add_eq hi3
      have hout1v : absRecRules out1 = absRecRules out ++ [absRecRule r2] := by
        rw [absRecRules, absRecRules, vec_push_val hout1, List.map_append]
        rfl
      have hout1wf : RecRulesWF out1 := by
        intro x hx
        rw [vec_push_val hout1] at hx
        rcases List.mem_append.mp hx with hx1 | hx1
        · exact hout x hx1
        · simp only [List.mem_singleton] at hx1; rw [hx1]; exact hr2wf
      have hrec :=
        ih st1 st' j2 i3 out1 o (by omega) hwf1 hout1wf h lst1 lfe2 lfe hrel1
          hr2 hrS
      cases o with
      | Err e =>
        -- move 1: the tail fold threw
        rw [hi3v, hj2v] at hrec
        rw [hcons]
        exact ErrSim.trans hrec (fun le hle => checkIotaRulesF_tail_err hrun1 hle)
      | Ok v =>
      obtain ⟨lst', hrunT, hvsplit, hrel', hwf', hvwf⟩ := hrec
      rw [hi3v, hj2v, hout1v] at hrunT
      rw [hout1v] at hvsplit
      have hlen : ((absRecRules out) ++ [absRecRule r2]).length
          = (absRecRules out).length + 1 := by simp
      rw [hlen] at hrunT hvsplit
      have hdrop : (absRecRules v).drop (absRecRules out).length
          = absRecRule r2 :: (absRecRules v).drop ((absRecRules out).length + 1) := by
        conv_lhs => rw [hvsplit]
        rw [List.append_assoc]
        rw [show (absRecRules out).length
            = (absRecRules out).length from rfl]
        simp
      refine ⟨lst', ?_, ?_, hrel', hwf', hvwf⟩
      · rw [hcons, hdrop]
        exact checkIotaRulesF_cons hrun1 hrunT
      · rw [hdrop]
        simpa using hvsplit

/-- `ConLeche/Kernel/DeclCheck.lean:718-727` — `check_iota_rules` refines
`checkIotaRulesF`, the per-rule fold.  The port accumulates on the way *in*
where con-leche conses on the way out, so the accumulator is carried in
front. -/
theorem check_iota_rules_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name} {ty_a : expr.Expr}
    {m_i r_p j : Std.U64} {rules out : alloc.vec.Vec env.RecRule}
    {i : Std.Usize}
    {o : core.result.Result (alloc.vec.Vec env.RecRule) core_types.CheckError}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hcv : NameWF cv_name) (hlps : NamesWF lps)
    (hty : ExprWF ty_a) (hrules : RecRulesWF rules) (hout : RecRulesWF out)
    (h : inductives.modeled.check_iota_rules mode st fe2 fe_self f cv_name lps
        ty_a m_i r_p j rules i out = ok (o, st')) :
    ∀ lst lfe2 lfe, StateRel st lst → FEnvRel fe2 lfe2 → FEnvRel fe_self lfe →
      match o with
      | .Ok v =>
        ∃ lst',
          (ConLeche.checkIotaRulesF (absMode mode)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
              (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
              j.val ((absRecRules rules).drop i.val)).run lst
            = .ok ((absRecRules v).drop (absRecRules out).length, lst')
          ∧ absRecRules v
              = absRecRules out ++ (absRecRules v).drop (absRecRules out).length
          ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRulesWF v
      | .Err e =>
        ErrSim e
          ((ConLeche.checkIotaRulesF (absMode mode)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe2 lfe g
              (absName cv_name) (absNames lps) (absExpr ty_a) m_i.val r_p.val
              j.val ((absRecRules rules).drop i.val)).run lst) := by
  intro lst lfe2 lfe hrel hr2 hrS
  have hkey := check_iota_rules_val hw hcb hres hspines hf hfe2 hfe hcv hlps hty
    hrules rules.length st st' j i out o (by scalar_tac) hst hout h lst lfe2 lfe
    hrel hr2 hrS
  cases o with
  | Ok v => exact hkey
  | Err e => exact hkey

/-- `check_iota_rules_refines` at a success, the pre-#67 statement. -/
theorem check_iota_rules_refines_ok
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    {cv_name : name.Name} {lps : alloc.vec.Vec name.Name} {ty_a : expr.Expr}
    {m_i r_p j : Std.U64} {rules out v : alloc.vec.Vec env.RecRule}
    {i : Std.Usize}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
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
        ∧ StateRel st' lst' ∧ StateWF st' ∧ RecRulesWF v :=
  check_iota_rules_refines hw hcb hres hspines hf hst hfe2 hfe hcv hlps hty
    hrules hout h

/-! ## The members (`Modeled.lean:373-455`, `DeclCheck.lean:487-505`) -/

omit hw hcb in
/-- `"_model"`'s code points as a `Vec<u32>`, the witness `absString`'s
injectivity needs to read `level::is_model_str` backwards. -/
theorem modelStr_witness :
    ∃ v : alloc.vec.Vec Std.U32,
      v.val = [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32]
        ∧ StrWF v ∧ absString v = "_model" := by
  refine ⟨alloc.vec.Vec.from [95#u32, 109#u32, 111#u32, 100#u32, 101#u32,
    108#u32] (by simp only [List.length_cons, List.length_nil]; scalar_tac),
    ?_, ?_, ?_⟩
  · exact alloc.vec.Vec.from_val _ _
  · intro c hc
    rw [alloc.vec.Vec.from_val] at hc
    fin_cases hc <;> decide
  · rw [absString_eq, alloc.vec.Vec.from_val]; rfl

omit hw hcb in
/-- `ConLeche/Kernel/Level.lean:219 Name.isModelSuffix` — `level::is_model_str`
decides `absString s = "_model"`.  (`Refine/Level.lean`'s in spirit; it is here
because `check_member_val` is its only caller in this directory.) -/
theorem is_model_str_refines {s : alloc.vec.Vec Std.U32} (hs : StrWF s)
    {b : Bool} (h : level.is_model_str s = ok b) :
    b = decide (absString s = "_model") := by
  obtain ⟨w, hwv, hwwf, hwabs⟩ := modelStr_witness
  have hiff : absString s = "_model" ↔ s.val = w.val := by
    constructor
    · intro hstr
      rw [Name.absString_inj hs hwwf (by rw [hstr, hwabs])]
    · intro hval
      rw [absString_eq, hval, ← absString_eq, hwabs]
  have hgoal : decide (absString s = "_model") = decide (s.val = w.val) := by
    rw [Bool.eq_iff_iff]
    simpa using hiff
  rw [hgoal, hwv]
  have hgi : ∀ (i : Std.Usize) (x : Std.U32), i.val < s.val.length →
      s.val[i.val]? = some x →
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32) s i
        = ok x := by
    intro i x hi hx
    obtain ⟨y, hy, hyv⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec s i hi)
    subst hyv
    rw [alloc.vec.Vec.index_slice_index, hy]
    rw [List.getElem?_eq_getElem hi] at hx
    congr 1
    exact Option.some_inj.mp hx
  rw [level.is_model_str] at h
  by_cases hlen : s.val.length = 6
  · rw [if_pos (show alloc.vec.Vec.len s = 6#usize by
      have := alloc.vec.Vec.len_val s; scalar_tac)] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, hval⟩ :
        ∃ a0 a1 a2 a3 a4 a5 : Std.U32, s.val = [a0, a1, a2, a3, a4, a5] := by
      rcases hl : s.val with _ | ⟨a0, l1⟩
      · rw [hl] at hlen; simp at hlen
      rcases l1 with _ | ⟨a1, l2⟩
      · rw [hl] at hlen; simp at hlen
      rcases l2 with _ | ⟨a2, l3⟩
      · rw [hl] at hlen; simp at hlen
      rcases l3 with _ | ⟨a3, l4⟩
      · rw [hl] at hlen; simp at hlen
      rcases l4 with _ | ⟨a4, l5⟩
      · rw [hl] at hlen; simp at hlen
      rcases l5 with _ | ⟨a5, l6⟩
      · rw [hl] at hlen; simp at hlen
      rcases l6 with _ | ⟨a6, l7⟩
      · exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩
      · rw [hl] at hlen; simp at hlen
    rw [hval]
    rw [hgi 0#usize a0 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok] at h
    by_cases hc0 : a0 = 95#u32
    case neg => rw [if_neg hc0, Result.ok.injEq] at h; simp [← h, hc0]
    rw [if_pos hc0] at h
    rw [hgi 1#usize a1 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok] at h
    by_cases hc1 : a1 = 109#u32
    case neg => rw [if_neg hc1, Result.ok.injEq] at h; simp [← h, hc1]
    rw [if_pos hc1] at h
    rw [hgi 2#usize a2 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok] at h
    by_cases hc2 : a2 = 111#u32
    case neg => rw [if_neg hc2, Result.ok.injEq] at h; simp [← h, hc2]
    rw [if_pos hc2] at h
    rw [hgi 3#usize a3 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok] at h
    by_cases hc3 : a3 = 100#u32
    case neg => rw [if_neg hc3, Result.ok.injEq] at h; simp [← h, hc3]
    rw [if_pos hc3] at h
    rw [hgi 4#usize a4 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok] at h
    by_cases hc4 : a4 = 101#u32
    case neg => rw [if_neg hc4, Result.ok.injEq] at h; simp [← h, hc4]
    rw [if_pos hc4] at h
    rw [hgi 5#usize a5 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok, Result.ok.injEq] at h
    rw [← h, hc0, hc1, hc2, hc3, hc4]
    simp
  · rw [if_neg (show ¬ alloc.vec.Vec.len s = 6#usize by
      have := alloc.vec.Vec.len_val s
      intro hc; apply hlen; scalar_tac), Result.ok.injEq] at h
    rw [← h]
    have hne : s.val ≠ [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32] := by
      intro hc; apply hlen; rw [hc]; rfl
    simp [hne]

omit hw hcb in
/-- `ConLeche/Kernel/Level.lean:219` — `Name.isModelSuffix` at a `.str`
node. -/
theorem isModelSuffix_str (p : ConLeche.Name) (x : String) :
    ConLeche.Name.isModelSuffix (.str p x) = decide (x = "_model") := by
  by_cases hx : x = "_model"
  · subst hx; rfl
  · simp only [ConLeche.Name.isModelSuffix, hx, decide_false]
    split <;> simp_all

omit hw hcb in
/-- `ConLeche/Kernel/Level.lean:219` — `level::name_is_model_suffix` refines
`Name.isModelSuffix`. -/
theorem name_is_model_suffix_refines {n : name.Name} (hn : NameWF n) {b : Bool}
    (h : level.name_is_model_suffix n = ok b) :
    b = (absName n).isModelSuffix := by
  cases hn with
  | @anonymous n' hmk =>
    rw [name_anonymous_inv hmk] at h ⊢
    rw [level.name_is_model_suffix] at h
    simp at h
    subst h
    rfl
  | @str pre str n' hpre hstr hmk =>
    obtain ⟨hh, rfl⟩ := mk_str_inv hmk
    rw [level.name_is_model_suffix] at h
    simp only [arc_deref_eq, bind_tc_ok] at h
    rw [is_model_str_refines hstr h, absName_mk, absNameKind,
      isModelSuffix_str]
  | @num pre m n' hpre hmk =>
    obtain ⟨hh, rfl⟩ := mk_num_inv hmk
    rw [level.name_is_model_suffix] at h
    simp at h
    subst h
    rfl

set_option linter.unusedSimpArgs false in
omit hw hcb in
/-- `checkMemberValF`'s **no-model** `throw` (task #67): past a
`checkConstantValF` that succeeded and a member name that is not itself
model-shaped, `core_k::defn_probe` answering `None` is exactly "the index has
no `_model` definition under that name", which is the cited `let some
(.defnInfo …) := … | throw` (`DeclCheck.lean:493-496`).  The message names the
block, so it is existential. -/
theorem checkMemberValF_route_err {lmode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {blockNames : List ConLeche.Name}
    {cv cvA : ConLeche.ConstantVal} {lst lst1 : ConLeche.Cached.CState}
    (hrun1 : (ConLeche.checkConstantValF
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe cv).run lst
      = .ok (cvA, lst1))
    (hbm : cvA.name.isModelSuffix = false)
    (hnone : CoreK.defnOf (lfe.find? (cvA.name.str "_model")) = none) :
    (ConLeche.checkMemberValF (ConLeche.Cached.sharedOpsC lmode lfe)
        blockNames lfe cv).run lst
      = .error (.notImplemented
          s!"no install route for inductive block \
            {blockNames.headD cvA.name}: no direct route recognises it and no \
            model for {cvA.name} was generated") := by
  rw [ConLeche.checkMemberValF]
  simp only [StateT.run] at hrun1
  cases hx : lfe.find? (cvA.name.str "_model") with
  | none =>
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, hbm, hx]
  | some ci =>
    rw [hx] at hnone
    cases ci
    case defnInfo => simp [CoreK.defnOf] at hnone
    all_goals
      simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
        StateT.pure, Except.pure, hrun1, hbm, hx]

set_option linter.unusedSimpArgs false in
set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:487-505` — **`check_member_val` refines
`checkMemberValF`**: `checkConstantVal`, the member may not itself be
model-shaped, and its type is the model's under the block renaming —
structurally.

Deviation: the cited type-mismatch message dumps both sides with `reprStr`;
§3.1 drops the interpolation, so only the message differs. -/
theorem check_member_val_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe2 : fenv.FEnv} {cv : env.ConstantVal}
    {out : core.result.Result env.ConstantVal core_types.CheckError}
    (hst : StateWF st) (hfe : FEnvWF fe2) (hbn : NamesWF block_names)
    (hcv : ConstantValWF cv)
    (h : inductives.modeled.check_member_val mode st block_names fe2 cv
        = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      match out with
      | .Ok cv_a =>
        ∃ lst',
          (ConLeche.checkMemberValF
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
              (absNames block_names) lfe (absConstantVal cv)).run lst
            = .ok (absConstantVal cv_a, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_a
      | .Err e =>
        ErrSim e
          ((ConLeche.checkMemberValF
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe)
              (absNames block_names) lfe (absConstantVal cv)).run lst) := by
  intro lst lfe hrel hfer
  rw [inductives.modeled.check_member_val] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err err =>
    -- move 1: `checker_base::check_constant_val` threw
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    refine ErrSim.trans
      (hcb.checkConstantValErr st fe2 cv err st1 hst hfe hcv hq lst lfe hrel
        hfer) (fun le hle => ?_)
    rw [ConLeche.checkMemberValF]
    simp only [StateT.run] at hle ⊢
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, hle]
  | Ok cva =>
  obtain ⟨lst1, hrun1, hrel1, hwf1, hcvawf⟩ :=
    hcb.checkConstantVal st fe2 cv cva st1 hst hfe hcv hq lst lfe hrel hfer
  obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
  have hbmv : bm = (absConstantVal cva).name.isModelSuffix :=
    name_is_model_suffix_refines hcvawf.1 hbm
  by_cases hbmt : bm = true
  · -- the member is itself model-shaped (`DeclCheck.lean:492`)
    rw [if_pos hbmt] at h
    simp at h
    obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
    rw [hbmt] at hbmv
    refine errSim_invalid
      s!"model-shaped member name {(absConstantVal cva).name}" hce ?_
    rw [ConLeche.checkMemberValF]
    simp only [StateT.run] at hrun1 ⊢
    simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
      Except.pure, hrun1, hbmv.symm]
  · rw [if_neg hbmt] at h
    simp only [Bool.not_eq_true] at hbmt
    rw [hbmt] at hbmv
    obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hnmv, hnmwf⟩ := model_of_refines hcvawf.1 hnm
    obtain ⟨hoabs, howf⟩ :=
      CoreK.defn_probe_refines (FindAgree.of_rel hfer hfe) (FindWF.of_wf hfe)
        hnmwf ho
    rw [hnmv] at hoabs
    cases o with
    | none =>
      -- there is no `_model` definition for this member (`DeclCheck.lean:493`)
      simp at h
      obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
      simp only [Option.map_none] at hoabs
      exact errSim_notImplemented _ hce
        (checkMemberValF_route_err hrun1 hbmv.symm
          (by
            show CoreK.defnOf (lfe.find? ((absName cva.name).str "_model"))
              = none
            exact hoabs.symm))
    | some dq =>
    obtain ⟨cvm, mv, mhint⟩ := dq
    have hcvmwf : ConstantValWF cvm := (howf cvm mv mhint rfl).1
    have hfindm : lfe.find? ((absConstantVal cva).name.str "_model")
        = some (.defnInfo (absConstantVal cvm) (absExpr mv) (absHint mhint)) := by
      show lfe.find? ((absName cva.name).str "_model") = _
      exact defnOf_inv (by simpa using hoabs.symm)
    have hfun : (fun n : ConLeche.Name =>
        if n ∈ absNames block_names then n.str "_model" else n)
        = blockRename (absNames block_names) := by
      funext n
      rw [blockRename]
      by_cases hc : n ∈ absNames block_names
      · rw [if_pos hc, if_pos (by simpa using hc)]
      · rw [if_neg hc, if_neg (by simpa using hc)]
    simp at h
    simp only [StateT.run] at hrun1
    rcases h with ⟨hb1, v, hv, ce, hce, rfl, rfl⟩
      | ⟨hb1, nm2, hren, (⟨hbeq, v, hv, ce, hce, rfl, rfl⟩ | ⟨hbeq, rfl, rfl⟩)⟩
    · -- the model's level parameters disagree (`DeclCheck.lean:497`)
      have hlpsne : ¬ ((absConstantVal cvm).levelParams
          = (absConstantVal cva).levelParams) :=
        of_decide_eq_false
          (Env.names_beq_refines hcvmwf.2.1 hcvawf.2.1 hb1).symm
      refine errSim_notImplemented
        s!"model level parameters mismatch for {(absConstantVal cva).name}"
        hce ?_
      rw [ConLeche.checkMemberValF]
      simp only [StateT.run]
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
        Except.pure, hrun1, hbmv.symm, hfindm, hlpsne]
    · -- the renamed member type is not the model's (`DeclCheck.lean:499`)
      obtain ⟨hrenv, hrenwf⟩ :=
        ExprOps.rename_consts_refines
          (inst := inductives.modeled.BlockRename.Insts.Con_ron_coreKernelExpr_opsNameToName)
          (f := { block_names := block_names }) _ (block_rename_renames hbn)
          hcvawf.2.2 hren
      have hlpseq : (absConstantVal cvm).levelParams
          = (absConstantVal cva).levelParams :=
        of_decide_eq_true
          (Env.names_beq_refines hcvmwf.2.1 hcvawf.2.1 hb1).symm
      have htyne : ¬ (ConLeche.Expr.renameConsts
          (fun n => if n ∈ absNames block_names then n.str "_model" else n)
          (absConstantVal cva).type = (absConstantVal cvm).type) := by
        rw [hfun]
        show ¬ (ConLeche.Expr.renameConsts (blockRename (absNames block_names))
          (absExpr cva.ty) = absExpr cvm.ty)
        rw [← hrenv]
        exact of_decide_eq_false
          (Expr.beq_refines hrenwf hcvmwf.2.2 hbeq).symm
      refine errSim_notImplemented' hce ?_
      rw [ConLeche.checkMemberValF]
      simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
        StateT.pure, Except.pure, hrun1, hbmv.symm, hfindm, hlpseq, htyne]
    · obtain ⟨hrenv, hrenwf⟩ :=
        ExprOps.rename_consts_refines
          (inst := inductives.modeled.BlockRename.Insts.Con_ron_coreKernelExpr_opsNameToName)
          (f := { block_names := block_names }) _ (block_rename_renames hbn)
          hcvawf.2.2 hren
      have hlpseq : (absConstantVal cvm).levelParams
          = (absConstantVal cva).levelParams :=
        of_decide_eq_true
          (Env.names_beq_refines hcvmwf.2.1 hcvawf.2.1 hb1).symm
      have htyeq : ConLeche.Expr.renameConsts
          (fun n => if n ∈ absNames block_names then n.str "_model" else n)
          (absConstantVal cva).type = (absConstantVal cvm).type := by
        rw [hfun]
        show ConLeche.Expr.renameConsts (blockRename (absNames block_names))
          (absExpr cva.ty) = absExpr cvm.ty
        rw [← hrenv]
        exact of_decide_eq_true
          (Expr.beq_refines hrenwf hcvmwf.2.2 hbeq).symm
      refine ⟨lst1, ?_, hrel1, hwf1, hcvawf⟩
      rw [ConLeche.checkMemberValF]
      simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
        StateT.pure, Except.pure, hrun1, hbmv.symm, hfindm, hlpseq, htyeq]

/-- `check_member_val_refines` at a success, the pre-#67 statement. -/
theorem check_member_val_refines_ok
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
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_a :=
  check_member_val_refines hw hcb hst hfe hbn hcv h

set_option linter.unusedSimpArgs false in
/-- `ConLeche/Cached/CheckerC.lean:105-113` (minus the flush) — **the
`check_ind_member` stage**: one non-recursor member checked against its
`_model` counterpart and pushed with the block's capability record.
`Refine/IndC.lean`'s `check_ind_member_s_refines` composes it with
`StateC.flush_c_refines`. -/
theorem check_ind_member_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {caps : env.IndCaps} {fe2 : fenv.FEnv} {ci : env.ConstantInfo}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hst : StateWF st) (hfe : FEnvWF fe2) (hbn : NamesWF block_names)
    (hcaps : IndCapsWF caps) (hci : ConstantInfoWF ci)
    (h : inductives.modeled.check_ind_member mode st block_names caps fe2 ci
        = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (checkIndMemberN (absMode mode) (absNames block_names)
              (absIndCaps caps) lfe (absConstantInfo ci)).run lst
            = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
      | .Err e =>
        ErrSim e
          ((checkIndMemberN (absMode mode) (absNames block_names)
              (absIndCaps caps) lfe (absConstantInfo ci)).run lst) := by
  intro lst lfe hrel hfer
  rw [inductives.modeled.check_ind_member] at h
  obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
  have hcvv : absConstantVal cv
      = ConLeche.ConstantInfo.toConstantVal (absConstantInfo ci) :=
    Env.to_constant_val_refines hcv
  have hcvwf : ConstantValWF cv := StateC.to_constant_val_wf hci hcv
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err err =>
    -- move 1: `check_member_val` threw
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have herr :=
      check_member_val_refines hw hcb hst hfe hbn hcvwf hq lst lfe hrel hfer
    rw [hcvv] at herr
    refine ErrSim.trans herr (fun le hle => ?_)
    rw [checkIndMemberN]
    simp only [StateT.run] at hle ⊢
    simp [Bind.bind, StateT.bind, Except.bind, hle]
  | Ok cva =>
  obtain ⟨lst1, hrun1, hrel1, hwf1, hcvawf⟩ :=
    check_member_val_refines hw hcb hst hfe hbn hcvwf hq lst lfe hrel hfer
  rw [hcvv] at hrun1
  simp only [StateT.run] at hrun1
  rw [checkIndMemberN]
  -- **plain `cases`**, not `cases hcase : ci`: task #67's `match out` motive
  -- carries the `= ok (out, st')` hypothesis, which mentions `ci`, so
  -- generalizing `ci` under an equation is not type correct.
  cases ci
  case IndInfo =>
    simp only [absConstantInfo] at hrun1
    obtain ⟨ic, hic, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨fnew, hpush, h⟩ := bind_eq_ok_iff.mp h
    rw [Env.ind_caps_dup_refines hic] at hpush
    obtain ⟨hprel, hpwf⟩ :=
      FEnv.push_refines hfer hfe (by exact ⟨hcvawf, hcaps⟩) hpush
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lst1, _, ?_, hrel1, hprel, hwf1, hpwf⟩
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, absConstantInfo]
  case CtorInfo =>
    simp only [absConstantInfo] at hrun1
    obtain ⟨fnew, hpush, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hprel, hpwf⟩ :=
      FEnv.push_refines hfer hfe (by exact hcvawf) hpush
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lst1, _, ?_, hrel1, hprel, hwf1, hpwf⟩
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, absConstantInfo]
  -- the six non-inductive members (`Modeled.lean`'s `M_NONIND`)
  all_goals simp at h
  all_goals obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
  all_goals
    refine errSim_invalid
      s!"non-inductive member {(absConstantVal cva).name} in block" hce ?_
  all_goals simp only [absConstantInfo] at hrun1
  all_goals
    simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, hrun1, absConstantInfo]

/-- `check_ind_member_refines` at a success, the pre-#67 statement. -/
theorem check_ind_member_refines_ok
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
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe' :=
  check_ind_member_refines hw hcb hst hfe hbn hcaps hci h


omit hw hcb in
/-- `provisionRecsStepN`'s run at a `.recInfo`: the one arm the port's success
path takes.  Stated at a literal `.recInfo` so that the transcription's `match`
reduces — `absConstantInfo (.RecInfo …)` *is* that constructor, so the caller
applies it up to defeq without rewriting a dependent matcher's scrutinee. -/
theorem provisionRecsStepN_rec {lmode : ConLeche.CheckMode}
    {blockNames : List ConLeche.Name} {feAcc : ConLeche.FEnv}
    {cv cvA : ConLeche.ConstantVal} {mI rP : Nat}
    {rules : List ConLeche.RecRule} {lst lst1 : ConLeche.Cached.CState}
    (h1 : (ConLeche.checkMemberValF (ConLeche.Cached.sharedOpsC lmode feAcc)
        blockNames feAcc
        (ConLeche.ConstantInfo.recInfo cv mI rP rules).toConstantVal).run lst
      = .ok (cvA, lst1)) :
    (provisionRecsStepN lmode blockNames feAcc
        (ConLeche.ConstantInfo.recInfo cv mI rP rules)).run lst
      = .ok ((feAcc.push (.recInfo cvA mI rP []), cvA, mI, rP, rules), lst1) := by
  rw [provisionRecsStepN]
  simp only [StateT.run] at h1
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, h1]

omit hw hcb in
/-- `provisionRecsStepN`'s failure twin at a `.recInfo` (task #67): the member
check threw, and the step's only bind carries it. -/
theorem provisionRecsStepN_rec_err {lmode : ConLeche.CheckMode}
    {blockNames : List ConLeche.Name} {feAcc : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {mI rP : Nat}
    {rules : List ConLeche.RecRule} {lst : ConLeche.Cached.CState}
    {le : ConLeche.CheckError}
    (h1 : (ConLeche.checkMemberValF (ConLeche.Cached.sharedOpsC lmode feAcc)
        blockNames feAcc
        (ConLeche.ConstantInfo.recInfo cv mI rP rules).toConstantVal).run lst
      = .error le) :
    (provisionRecsStepN lmode blockNames feAcc
        (ConLeche.ConstantInfo.recInfo cv mI rP rules)).run lst = .error le := by
  rw [provisionRecsStepN]
  simp only [StateT.run] at h1
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, h1]

/-- `ConLeche/Cached/CheckerC.lean:120-127` (minus the flush) — **the
`provision_recs_step` stage**: one recursor's constant checked and provisioned
rule-less on top of the previous ones. -/
theorem provision_recs_step_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe_acc : fenv.FEnv} {ci : env.ConstantInfo}
    {out : core.result.Result (fenv.FEnv × env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule) core_types.CheckError}
    (hst : StateWF st) (hfe : FEnvWF fe_acc) (hbn : NamesWF block_names)
    (hci : ConstantInfoWF ci)
    (h : inductives.modeled.provision_recs_step mode st block_names fe_acc ci
        = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe_acc lfe →
      match out with
      | .Ok q =>
        ∃ lst' lfe',
          (provisionRecsStepN (absMode mode) (absNames block_names) lfe
              (absConstantInfo ci)).run lst
            = .ok ((lfe', absConstantVal q.2.1, q.2.2.1.val, q.2.2.2.1.val,
                absRecRules q.2.2.2.2), lst')
          ∧ StateRel st' lst' ∧ FEnvRel q.1 lfe' ∧ StateWF st' ∧ FEnvWF q.1
          ∧ ConstantValWF q.2.1 ∧ RecRulesWF q.2.2.2.2
      | .Err e =>
        ErrSim e
          ((provisionRecsStepN (absMode mode) (absNames block_names) lfe
              (absConstantInfo ci)).run lst) := by
  intro lst lfe hrel hfer
  rw [inductives.modeled.provision_recs_step.eq_def] at h
  cases ci
  case RecInfo =>
    obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨rules2, hrules2, h⟩ := bind_eq_ok_iff.mp h
    have hcvv : absConstantVal cv
        = ConLeche.ConstantInfo.toConstantVal (absConstantInfo _) :=
      Env.to_constant_val_refines hcv
    have hcvwf : ConstantValWF cv := StateC.to_constant_val_wf hci hcv
    rw [Env.rec_rules_copy_refines hrules2] at h
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r, st1⟩ := p
    cases r with
    | Err err =>
      -- move 1: `check_member_val` threw
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have herr :=
        check_member_val_refines hw hcb hst hfe hbn hcvwf hp lst lfe hrel hfer
      rw [hcvv] at herr
      exact ErrSim.trans herr (fun le hle => provisionRecsStepN_rec_err hle)
    | Ok cva =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hcvawf⟩ :=
      check_member_val_refines hw hcb hst hfe hbn hcvwf hp lst lfe hrel hfer
    rw [hcvv] at hrun1
    obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
    rw [Env.constant_val_dup_refines hcv1] at h
    obtain ⟨fnew, hpush, h⟩ := bind_eq_ok_iff.mp h
    have hnilwf : RecRulesWF (alloc.vec.Vec.new env.RecRule) := by
      intro x hx; simp [alloc.vec.Vec.new] at hx
    obtain ⟨hprel, hpwf⟩ :=
      FEnv.push_refines hfer hfe (by exact ⟨hcvawf, hnilwf⟩) hpush
    simp at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨lst1, _, ?_, hrel1, hprel, hwf1, hpwf, hcvawf, hci.2⟩
    exact provisionRecsStepN_rec hrun1
  -- a non-recursor reached the provisioning fold (`CheckerC.lean:120`)
  all_goals simp at h
  all_goals obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
  all_goals
    refine errSim_notImplemented "recursor before other block members" hce ?_
  all_goals simp [provisionRecsStepN, StateT.run, absConstantInfo]

/-- `provision_recs_step_refines` at a success, the pre-#67 statement. -/
theorem provision_recs_step_refines_ok
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
        ∧ ConstantValWF q.2.1 ∧ RecRulesWF q.2.2.2.2 :=
  provision_recs_step_refines hw hcb hst hfe hbn hci h


omit hw hcb in
/-- `provisionRecsN` at a cons: the step then the tail. -/
theorem provisionRecsN_cons {lmode : ConLeche.CheckMode}
    {blockNames : List ConLeche.Name} {feAcc fe1 fe2 : ConLeche.FEnv}
    {ci : ConLeche.ConstantInfo} {rest : List ConLeche.ConstantInfo}
    {cv : ConLeche.ConstantVal} {mI rP : Nat} {rules : List ConLeche.RecRule}
    {tail : List (ConLeche.ConstantVal × Nat × Nat × List ConLeche.RecRule)}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (h1 : (provisionRecsStepN lmode blockNames feAcc ci).run lst
      = .ok ((fe1, cv, mI, rP, rules), lst1))
    (h2 : (provisionRecsN lmode blockNames fe1 rest).run lst1
      = .ok ((fe2, tail), lst2)) :
    (provisionRecsN lmode blockNames feAcc (ci :: rest)).run lst
      = .ok ((fe2, (cv, mI, rP, rules) :: tail), lst2) := by
  rw [provisionRecsN]
  simp only [StateT.run] at h1 h2
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, h1, h2]

omit hw hcb in
/-- `provisionRecsN` at a cons whose **head** threw (task #67). -/
theorem provisionRecsN_head_err {lmode : ConLeche.CheckMode}
    {blockNames : List ConLeche.Name} {feAcc : ConLeche.FEnv}
    {ci : ConLeche.ConstantInfo} {rest : List ConLeche.ConstantInfo}
    {lst : ConLeche.Cached.CState} {le : ConLeche.CheckError}
    (h1 : (provisionRecsStepN lmode blockNames feAcc ci).run lst = .error le) :
    (provisionRecsN lmode blockNames feAcc (ci :: rest)).run lst
      = .error le := by
  rw [provisionRecsN]
  simp only [StateT.run] at h1
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, h1]

omit hw hcb in
/-- `provisionRecsN` at a cons whose **tail** threw. -/
theorem provisionRecsN_tail_err {lmode : ConLeche.CheckMode}
    {blockNames : List ConLeche.Name} {feAcc fe1 : ConLeche.FEnv}
    {ci : ConLeche.ConstantInfo} {rest : List ConLeche.ConstantInfo}
    {cv : ConLeche.ConstantVal} {mI rP : Nat} {rules : List ConLeche.RecRule}
    {lst lst1 : ConLeche.Cached.CState} {le : ConLeche.CheckError}
    (h1 : (provisionRecsStepN lmode blockNames feAcc ci).run lst
      = .ok ((fe1, cv, mI, rP, rules), lst1))
    (h2 : (provisionRecsN lmode blockNames fe1 rest).run lst1 = .error le) :
    (provisionRecsN lmode blockNames feAcc (ci :: rest)).run lst
      = .error le := by
  rw [provisionRecsN]
  simp only [StateT.run] at h1 h2
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, h1, h2]

/-- `provision_recs`'s index recursion on `recs.len() - i`. -/
theorem provision_recs_val {block_names : alloc.vec.Vec name.Name}
    (hbn : NamesWF block_names) {recs : alloc.vec.Vec env.ConstantInfo}
    (hrecs : ConstantInfosWF recs) :
    ∀ n : Nat, ∀ (st st' : cached.state_c.CState) (fe_acc : fenv.FEnv)
      (i : Std.Usize)
      (out : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
        × alloc.vec.Vec env.RecRule))
      (q : fenv.FEnv × alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
        × alloc.vec.Vec env.RecRule)),
      recs.length - i.val ≤ n → StateWF st → FEnvWF fe_acc →
      (∀ c ∈ out.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2) →
      inductives.modeled.provision_recs mode st block_names fe_acc recs i out
        = ok (.Ok q, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe_acc lfe →
        ∃ lst' lfe',
          (provisionRecsN (absMode mode) (absNames block_names) lfe
              ((absConstantInfos recs).drop i.val)).run lst
            = .ok ((lfe',
                (absCheckedRecs q.2).drop (absCheckedRecs out).length), lst')
          ∧ absCheckedRecs q.2
              = absCheckedRecs out
                ++ (absCheckedRecs q.2).drop (absCheckedRecs out).length
          ∧ StateRel st' lst' ∧ FEnvRel q.1 lfe' ∧ StateWF st' ∧ FEnvWF q.1
          ∧ (∀ c ∈ q.2.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2) := by
  intro n
  induction n with
  | zero =>
    intro st st' fe_acc i out q hk hst hfe hout h lst lfe hrel hfer
    rw [inductives.modeled.provision_recs,
      if_pos (show i ≥ alloc.vec.Vec.len recs by
        have := alloc.vec.Vec.len_val recs; scalar_tac), Result.ok.injEq,
      Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hnil : (absConstantInfos recs).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absConstantInfos, List.length_map]
      scalar_tac
    refine ⟨lst, lfe, ?_, by simp, hrel, hfer, hst, hfe, hout⟩
    rw [hnil, provisionRecsN]
    simp [StateT.run, Pure.pure, StateT.pure, Except.pure]
  | succ n ih =>
    intro st st' fe_acc i out q hk hst hfe hout h lst lfe hrel hfer
    rw [inductives.modeled.provision_recs] at h
    by_cases hi : i.val ≥ recs.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len recs by
        have := alloc.vec.Vec.len_val recs; scalar_tac), Result.ok.injEq,
        Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hnil : (absConstantInfos recs).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absConstantInfos, List.length_map]
        scalar_tac
      refine ⟨lst, lfe, ?_, by simp, hrel, hfer, hst, hfe, hout⟩
      rw [hnil, provisionRecsN]
      simp [StateT.run, Pure.pure, StateT.pure, Except.pure]
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len recs by
        have := alloc.vec.Vec.len_val recs; scalar_tac)] at h
      have hlt : i.val < recs.val.length := by
        have := alloc.vec.Vec.len_val recs; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec recs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      have hciwf : ConstantInfoWF recs.val[i.val] :=
        hrecs _ (List.getElem_mem hlt)
      obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err err => simp at h
      | Ok q0 =>
      obtain ⟨fe1, cv, mi, rp, rules⟩ := q0
      obtain ⟨lst1, lfe1, hrun1, hrel1, hprel1, hwf1, hpwf1, hcvwf, hruleswf⟩ :=
        provision_recs_step_refines hw hcb hst hfe hbn hciwf hp lst lfe hrel hfer
      simp at h
      obtain ⟨out1, hout1, i4, hi4, h⟩ := h
      have hi4v : i4.val = i.val + 1 := HashMap.uscalar_add_eq hi4
      have hout1wf : ∀ c ∈ out1.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2 := by
        intro c hc
        rw [vec_push_val hout1, List.mem_append] at hc
        cases hc with
        | inl hc => exact hout c hc
        | inr hc => rw [List.mem_singleton.mp hc]; exact ⟨hcvwf, hruleswf⟩
      obtain ⟨lst', lfe', hrunT, hdrop, hrel', hprel', hwf', hpwf', hqwf⟩ :=
        ih st1 st' fe1 i4 out1 q (by scalar_tac) hwf1 hpwf1 hout1wf h lst1 lfe1
          hrel1 hprel1
      rw [hi4v] at hrunT
      have hout1v : absCheckedRecs out1
          = absCheckedRecs out
            ++ [(absConstantVal cv, mi.val, rp.val, absRecRules rules)] := by
        rw [absCheckedRecs, vec_push_val hout1, List.map_append]
        rfl
      have hlt2 : i.val < (absConstantInfos recs).length := by
        simpa [absConstantInfos] using hlt
      have hcons : (absConstantInfos recs).drop i.val
          = absConstantInfo recs.val[i.val]
            :: (absConstantInfos recs).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absConstantInfos]
      rw [hout1v] at hdrop hrunT
      simp only [List.length_append, List.length_cons, List.length_nil] at hdrop hrunT
      have hkey : (absCheckedRecs q.2).drop (absCheckedRecs out).length
          = (absConstantVal cv, mi.val, rp.val, absRecRules rules)
            :: (absCheckedRecs q.2).drop ((absCheckedRecs out).length + 1) := by
        conv_lhs => rw [hdrop]
        rw [show (absCheckedRecs out).length
            = (absCheckedRecs out
              ++ [(absConstantVal cv, mi.val, rp.val,
                  absRecRules rules)]).length - 1 by simp]
        simp
      refine ⟨lst', lfe', ?_, ?_, hrel', hprel', hwf', hpwf', hqwf⟩
      · rw [hcons, hkey]
        exact provisionRecsN_cons hrun1 hrunT
      · rw [hkey]
        conv_lhs => rw [hdrop]
        simp

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
    (hout : ∀ c ∈ out.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2)
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
        ∧ StateRel st' lst' ∧ FEnvRel q.1 lfe' ∧ StateWF st' ∧ FEnvWF q.1
        ∧ (∀ c ∈ q.2.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2) :=
  provision_recs_val hw hcb hbn hrecs recs.length st st' fe_acc i out q
    (by scalar_tac) hst hfe hout h

omit hw hcb in
set_option linter.unusedSimpArgs false in
/-- `checkIndRecsFoldN` at a cons: one `checkIotaRulesF` then the tail. -/
theorem checkIndRecsFoldN_cons {lmode : ConLeche.CheckMode}
    {lfe2 lfeS : ConLeche.FEnv} {g : ConLeche.Name → ConLeche.Name}
    {c : ConLeche.ConstantVal × Nat × Nat × List ConLeche.RecRule}
    {rest : List (ConLeche.ConstantVal × Nat × Nat × List ConLeche.RecRule)}
    {lacc lacc' : ConLeche.FEnv} {rules2 : List ConLeche.RecRule}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (h1 : (ConLeche.checkIotaRulesF lmode
        (ConLeche.Cached.sharedOpsC lmode lfeS) lfe2 lfeS g c.1.name
        c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2).run lst
      = .ok (rules2, lst1))
    (h2 : (checkIndRecsFoldN lmode lfe2 lfeS g rest
        (lacc.push (.recInfo c.1 c.2.1 c.2.2.1 rules2))).run lst1
      = .ok (lacc', lst2)) :
    (checkIndRecsFoldN lmode lfe2 lfeS g (c :: rest) lacc).run lst
      = .ok (lacc', lst2) := by
  rw [checkIndRecsFoldN] at h2 ⊢
  rw [List.foldlM_cons]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure] at h1 h2
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, h1, h2]

/-- `check_ind_recs_fold`'s index recursion on `checked.len() - i`.

The accumulator's **unrestricted-canonical pair** rides along (task #59): each
step is one `fenv::push` onto it, which is `FEnv.push_canon`.  The checker
tier's declaration fold needs the pair back out of the modeled route, because
the index an `.indDecl` step returns is the next step's input. -/
theorem check_ind_recs_fold_val
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    {f : inductives.modeled.BlockRename} {g : ConLeche.Name → ConLeche.Name}
    (hf : RenamesTo f g) {fe2 fe_self : fenv.FEnv} (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self)
    {checked : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)}
    (hchecked : ∀ c ∈ checked.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2) :
    ∀ n : Nat, ∀ (st st' : cached.state_c.CState) (acc fe' : fenv.FEnv)
      (i : Std.Usize),
      checked.length - i.val ≤ n → StateWF st → FEnvWF acc →
      FEnv.FEnvCanon acc → FEnv.FEnvFull acc →
      inductives.modeled.check_ind_recs_fold mode st fe2 fe_self f checked i acc
        = ok (.Ok fe', st') →
      ∀ lst lfe2 lfe lacc, StateRel st lst → FEnvRel fe2 lfe2 →
        FEnvRel fe_self lfe → FEnvRel acc lacc →
        ∃ lst' lfe',
          (checkIndRecsFoldN (absMode mode) lfe2 lfe g
              ((absCheckedRecs checked).drop i.val) lacc).run lst
            = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  intro n
  induction n with
  | zero =>
    intro st st' acc fe' i hk hst hacc hacan hafull h lst lfe2 lfe lacc hrel hr2
      hrS hra
    rw [inductives.modeled.check_ind_recs_fold,
      if_pos (show i ≥ alloc.vec.Vec.len checked by
        have := alloc.vec.Vec.len_val checked; scalar_tac), Result.ok.injEq,
      Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hnil : (absCheckedRecs checked).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp only [absCheckedRecs, List.length_map]
      scalar_tac
    refine ⟨lst, lacc, ?_, hrel, hra, hst, hacc, hacan, hafull⟩
    rw [hnil, checkIndRecsFoldN]
    simp [StateT.run, Pure.pure, StateT.pure, Except.pure]
  | succ n ih =>
    intro st st' acc fe' i hk hst hacc hacan hafull h lst lfe2 lfe lacc hrel hr2
      hrS hra
    rw [inductives.modeled.check_ind_recs_fold] at h
    by_cases hi : i.val ≥ checked.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len checked by
        have := alloc.vec.Vec.len_val checked; scalar_tac), Result.ok.injEq,
        Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hnil : (absCheckedRecs checked).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absCheckedRecs, List.length_map]
        scalar_tac
      refine ⟨lst, lacc, ?_, hrel, hra, hst, hacc, hacan, hafull⟩
      rw [hnil, checkIndRecsFoldN]
      simp [StateT.run, Pure.pure, StateT.pure, Except.pure]
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len checked by
        have := alloc.vec.Vec.len_val checked; scalar_tac)] at h
      have hlt : i.val < checked.val.length := by
        have := alloc.vec.Vec.len_val checked; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec checked i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨hcvwf, hruleswf⟩ := hchecked _ (List.getElem_mem hlt)
      obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err err => simp at h
      | Ok rules2 =>
      have hnewwf : RecRulesWF (alloc.vec.Vec.new env.RecRule) := by
        intro x hx; simp [alloc.vec.Vec.new] at hx
      obtain ⟨lst1, hrun1, hdrop1, hrel1, hwf1, hr2wf⟩ :=
        check_iota_rules_refines hw hcb hres hspines hf hst hfe2 hfe hcvwf.1
          hcvwf.2.1 hcvwf.2.2 hruleswf hnewwf hp lst lfe2 lfe hrel hr2 hrS
      obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
      rw [Env.constant_val_dup_refines hcv1] at h
      obtain ⟨acc2, hpush, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
      have hi4v : i4.val = i.val + 1 := HashMap.uscalar_add_eq hi4
      obtain ⟨hprel, hpwf⟩ :=
        FEnv.push_refines hra hacc (by exact ⟨hcvwf, hr2wf⟩) hpush
      obtain ⟨hpcan, hpfull⟩ :=
        FEnv.push_canon hacc (by exact ⟨hcvwf, hr2wf⟩) hacan hafull hpush
      obtain ⟨lst', lfe', hrunT, hrel', hprel', hwf', hpwf', hpcan', hpfull'⟩ :=
        ih st1 st' acc2 fe' i4 (by omega) hwf1 hpwf hpcan hpfull h lst1 lfe2 lfe
          (lacc.push (absConstantInfo
            (.RecInfo checked.val[i.val].1 checked.val[i.val].2.1
              checked.val[i.val].2.2.1 rules2))) hrel1 hr2 hrS hprel
      rw [hi4v] at hrunT
      have hlt2 : i.val < (absCheckedRecs checked).length := by
        simpa [absCheckedRecs] using hlt
      have hcons : (absCheckedRecs checked).drop i.val
          = (absConstantVal checked.val[i.val].1,
              checked.val[i.val].2.1.val, checked.val[i.val].2.2.1.val,
              absRecRules checked.val[i.val].2.2.2)
            :: (absCheckedRecs checked).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absCheckedRecs]
      refine ⟨lst', lfe', ?_, hrel', hprel', hwf', hpwf', hpcan', hpfull'⟩
      rw [hcons]
      exact checkIndRecsFoldN_cons (lst1 := lst1) (rules2 := absRecRules rules2)
        hrun1 hrunT

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
    (hspines : StructSpinesRefine)
    (hf : RenamesTo f g) (hst : StateWF st) (hfe2 : FEnvWF fe2)
    (hfe : FEnvWF fe_self) (hacc : FEnvWF acc)
    (hacan : FEnv.FEnvCanon acc) (hafull : FEnv.FEnvFull acc)
    (hchecked : ∀ c ∈ checked.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2)
    (h : inductives.modeled.check_ind_recs_fold mode st fe2 fe_self f checked i
        acc = ok (.Ok fe', st')) :
    ∀ lst lfe2 lfe lacc, StateRel st lst → FEnvRel fe2 lfe2 →
      FEnvRel fe_self lfe → FEnvRel acc lacc →
      ∃ lst' lfe',
        (checkIndRecsFoldN (absMode mode) lfe2 lfe g
            ((absCheckedRecs checked).drop i.val) lacc).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_ind_recs_fold_val hw hcb hres hspines hf hfe2 hfe hchecked
    checked.length st st'
    acc fe' i (by scalar_tac) hst hacc hacan hafull h

/-! ### The recursor group's two steps -/

omit hw hcb in
/-- `checkIndRecsN`'s non-empty branch: the `Eq` pin, the provisioning fold and
the rule fold. -/
theorem checkIndRecsN_step {lmode : ConLeche.CheckMode}
    {blockNames : List ConLeche.Name} {lfe fe1 fe' : ConLeche.FEnv}
    {recs : List ConLeche.ConstantInfo}
    {checked : List (ConLeche.ConstantVal × Nat × Nat × List ConLeche.RecRule)}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (hne : recs.isEmpty = false)
    (heq : lfe.find? ConLeche.eqName = some ConLeche.eqA)
    (h1 : (provisionRecsN lmode blockNames lfe recs).run lst
      = .ok ((fe1, checked), lst1))
    (h2 : (checkIndRecsFoldN lmode lfe fe1 (blockRename blockNames) checked
        lfe).run lst1 = .ok (fe', lst2)) :
    (checkIndRecsN lmode blockNames lfe recs).run lst = .ok (fe', lst2) := by
  rw [checkIndRecsN]
  simp only [StateT.run] at h1 h2
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, hne, heq, h1, h2]

/-- `ConLeche/Cached/CheckerC.lean:136-151` (minus every flush) —
`check_ind_recs` refines `checkIndRecsN`: the block's recursors as a *group*.

Deviation: the port takes two `fenv::dup`s, because it threads the index
linearly (task #14) where con-leche's is persistent and holds three views at
once — `env₂`, the fully provisioned `envSelf`, and the fold's accumulator.
`Refine/FEnv.lean`'s `dup_refines` is what says a dup is the same index.

`hcan` (added at task #59): `check_ind_recs` takes a `fenv::dup` of its
index and runs the provisioning fold on the copy, so the copy has to be the
*same* index again — `FEnv.dup_rel` needs `FEnvCanon`, exactly as
`Refine/IndNativeInstall.lean` takes it.  `Refine/IndC.lean` discharges it at
the driver from `dup_canon`/`mk_fenv_canon`. -/
theorem check_ind_recs_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe2 fe' : fenv.FEnv} {recs : alloc.vec.Vec env.ConstantInfo}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    (hst : StateWF st) (hfe : FEnvWF fe2) (hcan : FEnv.FEnvCanon fe2)
    (hfull : FEnv.FEnvFull fe2)
    (hbn : NamesWF block_names) (hrecs : ConstantInfosWF recs)
    (h : inductives.modeled.check_ind_recs mode st block_names fe2 recs
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst' lfe',
        (checkIndRecsN (absMode mode) (absNames block_names) lfe
            (absConstantInfos recs)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  intro lst lfe hrel hfer
  rw [inductives.modeled.check_ind_recs] at h
  by_cases hemp : alloc.vec.Vec.len recs = 0#usize
  · rw [if_pos hemp, Result.ok.injEq, Prod.mk.injEq,
      core.result.Result.Ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hnil : absConstantInfos recs = [] := by
      have := alloc.vec.Vec.len_val recs
      have hz : recs.val.length = 0 := by scalar_tac
      simp only [absConstantInfos, List.map_eq_nil_iff]
      exact List.eq_nil_of_length_eq_zero hz
    refine ⟨lst, lfe, ?_, hrel, hfer, hst, hfe, hcan, hfull⟩
    rw [checkIndRecsN, hnil]
    simp [StateT.run, Pure.pure, StateT.pure, Except.pure]
  · rw [if_neg hemp] at h
    have hnotnil : (absConstantInfos recs).isEmpty = false := by
      have := alloc.vec.Vec.len_val recs
      rcases hl : absConstantInfos recs with _ | ⟨x, xs⟩
      · exfalso
        apply hemp
        have hz : recs.val.length = 0 := by
          have : (absConstantInfos recs).length = 0 := by rw [hl]; rfl
          simpa [absConstantInfos] using this
        scalar_tac
      · rfl
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbv := BasisPins.eq_basis_pinned_refines hfer hfe hb
    by_cases hbt : b = true
    · rw [if_pos hbt] at h
      rw [hbt] at hbv
      have heqp : lfe.find? ConLeche.eqName = some ConLeche.eqA :=
        of_decide_eq_true hbv.symm
      obtain ⟨feD, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hdrel, hdwf, hdcan⟩ := FEnv.dup_rel hfe hcan hfer hdup
      obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err err => simp at h
      | Ok pq =>
      obtain ⟨feSelf, checkedv⟩ := pq
      have hnewwf : ∀ c ∈ (alloc.vec.Vec.new (env.ConstantVal × Std.U64
          × Std.U64 × alloc.vec.Vec env.RecRule)).val,
          ConstantValWF c.1 ∧ RecRulesWF c.2.2.2 := by
        intro c hc; simp [alloc.vec.Vec.new] at hc
      obtain ⟨lst1, lfe1, hrun1, hdrop1, hrel1, hprel1, hwf1, hpwf1,
        hcheckedwf⟩ :=
        provision_recs_refines hw hcb hst hdwf hbn hrecs hnewwf hp lst lfe hrel
          hdrel
      simp only [show ((0#usize : Std.Usize)).val = 0 from rfl,
        List.drop_zero] at hrun1
      have hnewabs : absCheckedRecs (alloc.vec.Vec.new (env.ConstantVal
          × Std.U64 × Std.U64 × alloc.vec.Vec env.RecRule)) = [] := by
        simp [absCheckedRecs, alloc.vec.Vec.new]
      rw [hnewabs] at hrun1
      simp only [List.length_nil, List.drop_zero] at hrun1
      obtain ⟨lst', lfe', hrunT, hrel', hprel', hwf', hpwf', hpcan', hpfull'⟩ :=
        check_ind_recs_fold_refines hw hcb hres hspines (block_rename_renames hbn)
          hwf1
          hdwf hpwf1 hfe hcan hfull hcheckedwf h lst1 lfe lfe1 lfe hrel1 hdrel
          hprel1 hfer
      simp only [show ((0#usize : Std.Usize)).val = 0 from rfl,
        List.drop_zero] at hrunT
      exact ⟨lst', lfe', checkIndRecsN_step hnotnil heqp hrun1 hrunT, hrel',
        hprel', hwf', hpwf', hpcan', hpfull'⟩
    · simp only [Bool.not_eq_true] at hbt
      rw [if_neg (by simp [hbt])] at h
      simp at h

/-! ## The projection functions (`Modeled.lean:475-584`,
`DeclCheck.lean:729-836`) -/

set_option linter.unusedSimpArgs false in
set_option linter.unusedSectionVars false in
/-- `ConLeche/Kernel/DeclCheck.lean:729-746` — `check_proj_lookups` refines
`checkProjLookupsF`: the stored constants the projection depends on.  It
touches no state, and so needs neither the knot nor the checker base; the two
stay on the statement so that the section's shape is uniform.

The last conjunct (added at task #59) is a *strengthening*, not a weakening:
the cited body reads `cvj` out of `fe.find? ctorName`, so the answer is the
constant stored under `ctorName`.  `check_proj_fn_refines` needs exactly that
to discharge `check_proj_iota_refines`' `hcname` through
`FEnv.canon_find_name`. -/
theorem check_proj_lookups_refines
    {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f i : Std.U64}
    {out : core.result.Result (env.ConstantVal × env.ConstantVal)
      core_types.CheckError}
    (hrel : FEnvRel fe2 lfe) (hfe : FEnvWF fe2) (ht : NameWF t)
    (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : inductives.modeled.check_proj_lookups fe2 t ctor_name lps n_p n_f i
        = ok out) :
    match out with
    | .Ok q =>
      (∀ lst, (ConLeche.checkProjLookupsF (m := ConLeche.Cached.CheckCM) lfe
          (absName t) (absName ctor_name) (absNames lps) n_p.val n_f.val
          i.val).run lst
            = .ok ((absConstantVal q.1, absConstantVal q.2), lst))
        ∧ ConstantValWF q.1 ∧ ConstantValWF q.2
        ∧ lfe.find? (absName ctor_name)
            = some (.ctorInfo (absConstantVal q.1) n_p.val n_f.val)
    | .Err e =>
      ∀ lst, ErrSim e ((ConLeche.checkProjLookupsF
        (m := ConLeche.Cached.CheckCM) lfe (absName t) (absName ctor_name)
        (absNames lps) n_p.val n_f.val i.val).run lst) := by
  rw [inductives.modeled.check_proj_lookups] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ :=
    CoreK.ctor_probe_refines (FindAgree.of_rel hrel hfe) (FindWF.of_wf hfe) hc ho
  cases o with
  | none =>
    -- move 2: `DeclCheck.lean:733`, the constructor is not stored
    obtain ⟨s, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain rfl : out = .Err ce := (Result.ok_injective h).symm
    have hX : CoreK.ctorOf (lfe.find? (absName ctor_name)) = none := by
      simpa using hoabs.symm
    intro lst
    refine errSim_notImplemented "projection constructor not stored" hce ?_
    rw [ConLeche.checkProjLookupsF]
    cases hfx : lfe.find? (absName ctor_name) with
    | none => rfl
    | some ci =>
      rw [hfx] at hX
      cases ci <;> first | rfl | simp [CoreK.ctorOf] at hX
  | some cq =>
    obtain ⟨cv, np1, nf1⟩ := cq
    have hcvwf : ConstantValWF cv := howf cv np1 nf1 rfl
    have hfindc : lfe.find? (absName ctor_name)
        = some (.ctorInfo (absConstantVal cv) np1.val nf1.val) :=
      ctorOf_inv (by simpa using hoabs.symm)
    -- the cited `unless cnP = nP ∧ cnF = nF do throw` is **one** site; §3.4
    -- splits it into the two `else if` arms `modeled.rs:1928`/`:1931`, which
    -- carry the same message and land on this run
    have harity : ∀ lst : ConLeche.Cached.CState,
        ¬ (np1.val = n_p.val ∧ nf1.val = n_f.val) →
        (ConLeche.checkProjLookupsF (m := ConLeche.Cached.CheckCM) lfe
            (absName t) (absName ctor_name) (absNames lps) n_p.val n_f.val
            i.val).run lst
          = .error (.notImplemented
              "projection constructor arity mismatch") := by
      intro lst hne
      rw [ConLeche.checkProjLookupsF, hfindc]
      simp [hne, StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
        StateT.pure, Except.pure]
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
        | none =>
          -- move 2: `DeclCheck.lean:736`, no projection model
          simp at h
          obtain ⟨v, hv, ce, hce, rfl⟩ := h
          have hX : CoreK.defnOf
              (lfe.find? (ConLeche.projModelName (absName t) i.val)) = none := by
            simpa using ho1abs.symm
          intro lst
          refine errSim_notImplemented "missing projection model" hce ?_
          rw [ConLeche.checkProjLookupsF, hfindc]
          cases hfx : lfe.find? (ConLeche.projModelName (absName t) i.val) with
          | none =>
            simp [hnp, hnf, StateT.run, Bind.bind, StateT.bind, Except.bind,
              Pure.pure, StateT.pure, Except.pure]
          | some ci =>
            rw [hfx] at hX
            cases ci <;>
              first
                | (simp [CoreK.defnOf] at hX; done)
                | simp [hnp, hnf, StateT.run, Bind.bind, StateT.bind,
                    Except.bind, Pure.pure, StateT.pure, Except.pure]
        | some dq =>
          obtain ⟨mcv, mv, mhint⟩ := dq
          have hmcvwf : ConstantValWF mcv := (ho1wf mcv mv mhint rfl).1
          have hfindm : lfe.find? (ConLeche.projModelName (absName t) i.val)
              = some (.defnInfo (absConstantVal mcv) (absExpr mv)
                  (absHint mhint)) :=
            defnOf_inv (by simpa using ho1abs.symm)
          obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
          have hbv : b = decide (absNames mcv.level_params = absNames lps) :=
            Env.names_beq_refines hmcvwf.2.1 hlps hb
          by_cases hbt : b = true
          · rw [if_pos hbt] at h
            rw [hbt] at hbv
            have hlpseq : (absConstantVal mcv).levelParams = absNames lps := by
              simpa [absConstantVal] using (of_decide_eq_true hbv.symm)
            obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
            have hn1v : absName n1 = ConLeche.projFnName (absName t) i.val :=
              Env.proj_fn_name_refines hn1
            have hn1wf : NameWF n1 := Env.proj_fn_name_wf ht hn1
            have ho2abs := find_refines hrel hfe hn1wf ho2
            rw [hn1v] at ho2abs
            cases o2 with
            | some ci2 =>
              -- move 2: `DeclCheck.lean:740`, the public name is taken
              simp only [Option.map_some] at ho2abs
              simp at h
              obtain ⟨v, hv, ce, hce, rfl⟩ := h
              intro lst
              refine errSim_invalid "projection name taken" hce ?_
              rw [ConLeche.checkProjLookupsF, hfindc]
              simp [hnp, hnf, hfindm, hlpseq, ← ho2abs, StateT.run, Bind.bind,
                StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
            | none =>
              simp only [Option.map_none] at ho2abs
              simp at h
              obtain ⟨o3, ho3, h⟩ := h
              have ho3abs := find_refines hrel hfe ht ho3
              cases o3 with
              | none =>
                -- move 2: `DeclCheck.lean:742`, the parent is not stored
                simp only [Option.map_none] at ho3abs
                simp at h
                obtain ⟨v, hv, ce, hce, rfl⟩ := h
                intro lst
                refine errSim_notImplemented "projection parent not stored" hce ?_
                rw [ConLeche.checkProjLookupsF, hfindc]
                simp [hnp, hnf, hfindm, hlpseq, ← ho2abs, ← ho3abs, StateT.run,
                  Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
                  Except.pure]
              | some ci3 =>
                simp only [Option.map_some] at ho3abs
                simp at h
                rcases h with ⟨hb3, v, hv, ce, hce, rfl⟩ | ⟨hb3, rfl⟩
                · -- move 2: `DeclCheck.lean:744`, the pinned `Eq` basis
                  have hb3v := BasisPins.eq_basis_pinned_refines hrel hfe hb3
                  have hne : lfe.find? ConLeche.eqName ≠ some ConLeche.eqA :=
                    of_decide_eq_false hb3v.symm
                  intro lst
                  refine errSim_notImplemented
                    "projection iota requires the pinned Eq basis" hce ?_
                  rw [ConLeche.checkProjLookupsF, hfindc]
                  simp [hnp, hnf, hfindm, hlpseq, ← ho2abs, ← ho3abs, hne,
                    StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
                    StateT.pure, Except.pure]
                · have hb3v := BasisPins.eq_basis_pinned_refines hrel hfe hb3
                  have heqpin : lfe.find? ConLeche.eqName = some ConLeche.eqA :=
                    of_decide_eq_true hb3v.symm
                  refine ⟨?_, hcvwf, hmcvwf, by simpa [hnp, hnf] using hfindc⟩
                  intro lst
                  rw [ConLeche.checkProjLookupsF, hfindc]
                  simp [hnp, hnf, hfindm, hlpseq, ← ho2abs, ← ho3abs, heqpin]
                  rfl
          · -- move 2: `DeclCheck.lean:738`, the model's level parameters
            simp only [Bool.not_eq_true] at hbt
            rw [if_neg (by simp [hbt])] at h
            rw [hbt] at hbv
            have hne : (absConstantVal mcv).levelParams ≠ absNames lps := by
              simpa [absConstantVal] using of_decide_eq_false hbv.symm
            simp at h
            obtain ⟨v, hv, ce, hce, rfl⟩ := h
            intro lst
            refine errSim_notImplemented "projection model level mismatch" hce ?_
            rw [ConLeche.checkProjLookupsF, hfindc]
            simp [hnp, hnf, hfindm, hne, StateT.run, Bind.bind, StateT.bind,
              Except.bind, Pure.pure, StateT.pure, Except.pure]
      · rw [if_neg hnf] at h
        simp at h
        obtain ⟨v, hv, ce, hce, rfl⟩ := h
        intro lst
        exact errSim_notImplemented "projection constructor arity mismatch" hce
          (harity lst (by simp [hnf]))
    · rw [if_neg hnp] at h
      simp at h
      obtain ⟨v, hv, ce, hce, rfl⟩ := h
      intro lst
      exact errSim_notImplemented "projection constructor arity mismatch" hce
        (harity lst (by simp [hnp]))

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

omit hw hcb in
/-- `checkProjIotaBody`'s success path, run: the body matched at the spine, the
head pinned to `Eq`, the two `==` pins discharged, the telescope opened, and
the side certificates' own run supplied.  `check_proj_iota_body_refines`
assembles the port's answers into exactly these. -/
theorem checkProjIotaBody_run {lmode : ConLeche.CheckMode}
    {lfeS : ConLeche.FEnv} {T : ConLeche.Name} {cvj tcv : ConLeche.ConstantVal}
    {lps : List ConLeche.Name} {nP nF i : Nat} {c : ConLeche.Name}
    {la : ConLeche.Level} {tySlot lhsC rhsC sbodyO : ConLeche.Expr}
    {fvs : List ConLeche.Expr} {lst lst' : ConLeche.Cached.CState}
    (hc : c = ConLeche.eqName)
    (hlhs : (lhsC == ConLeche.Expr.mkAppN
        (.const (ConLeche.projModelName T i) (lps.map .param))
        (((List.range nP).map fun k => ConLeche.Expr.bvar (nP + nF - 1 - k))
          ++ [ConLeche.Expr.mkAppN
                (.const (cvj.name.str "_model") (cvj.levelParams.map .param))
                (((List.range nP).map fun k =>
                    ConLeche.Expr.bvar (nP + nF - 1 - k))
                  ++ (List.range nF).map fun k =>
                       ConLeche.Expr.bvar (nF - 1 - k))])) = true)
    (hrhs : (rhsC == ConLeche.Expr.bvar (nF - 1 - i)) = true)
    (hopen : ConLeche.openPisAtFvars (nP + nF) tcv.type 0 = some (fvs, sbodyO))
    (hside : (ConLeche.checkIotaSidesTy (m := ConLeche.Cached.CheckCM) lmode
        (ConLeche.Cached.sharedOpsC lmode lfeS) lfeS.env (nP + nF)
        (sbodyO.getAppArgs.getD 0 (.bvar 0))
        (sbodyO.getAppArgs.getD 1 (.bvar 0))
        (sbodyO.getAppArgs.getD 2 (.bvar 0))
        (ConLeche.eqHeadLevel (ConLeche.Expr.const c [la]))
        (ConLeche.projModelName T i)).run lst = .ok ((), lst')) :
    (checkProjIotaBody lmode lfeS T cvj lps nP nF i tcv
        (.app (.app (.app (.const c [la]) tySlot) lhsC) rhsC)).run lst
      = .ok ((), lst') := by
  rw [checkProjIotaBody]
  simp only [ConLeche.Expr.getAppFn, ConLeche.unwrapOr, hopen, hc, hlhs, hrhs,
    StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
    Except.pure, ite_true]
  exact hside

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
    (hspines : StructSpinesRefine)
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
  intro lst lfe hrel hfer
  rw [inductives.modeled.check_proj_iota_body] at h
  obtain ⟨depth, hdepth, h⟩ := bind_eq_ok_iff.mp h
  have hdepthv : depth.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hdepth
  obtain ⟨pargs, hpargs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpav, hpawf⟩ := hspines.2.2.2 n_f n_p pargs hpargs
  have hpav' : absExprs pargs
      = (List.range n_p.val).map
          (fun k => ConLeche.Expr.bvar (n_p.val + n_f.val - 1 - k)) := by
    rw [hpav, ConLeche.structPsAt, Nat.add_comm n_f.val n_p.val]
  obtain ⟨xargs, hxargs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hxav, hxawf⟩ := hspines.2.2.1 n_f xargs hxargs
  obtain ⟨spine, hsp, h⟩ := bind_eq_ok_iff.mp h
  have hspv : absExprs spine = absExprs pargs := by
    rw [Env.exprs_copy_refines hsp]
  have hspwf : ExprsWF spine := Env.exprs_copy_wf hpawf hsp
  obtain ⟨spine1, hsp1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hsp1v, hsp1wf⟩ := CoreK.append_exprs_refines hspwf hxawf hsp1
  obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnmv, hnmwf⟩ := model_of_refines hcvj.1 hnm
  obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨husv, huswf⟩ := hspines.1 cvj.level_params us hcvj.2.1 hus
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  have hev : absExpr e = ConLeche.Expr.const ((absName cvj.name).str "_model")
      ((absNames cvj.level_params).map ConLeche.Level.param) := by
    rw [Expr.mk_const_refines he, hnmv, husv]
  have hewf : ExprWF e := ExprWF.mk_const hnmwf huswf he
  obtain ⟨mkspine, hmk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hmkv, hmkwf⟩ := ExprOps.mk_app_n_refines hewf hsp1wf hmk
  obtain ⟨largs, hlargs, h⟩ := bind_eq_ok_iff.mp h
  have hlargsv : absExprs largs = absExprs spine ++ [absExpr mkspine] :=
    ExprOps.absExprs_push hlargs
  have hlargswf : ExprsWF largs := ExprOps.exprsWF_push hspwf hmkwf hlargs
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hn1v, hn1wf⟩ := CoreK.proj_model_name_refines ht hn1
  obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hv1v, hv1wf⟩ := hspines.1 lps v1 hlps hv1
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  have he1v : absExpr e1
      = ConLeche.Expr.const (ConLeche.projModelName (absName t) i.val)
          ((absNames lps).map ConLeche.Level.param) := by
    rw [Expr.mk_const_refines he1, hn1v, hv1v]
  have he1wf : ExprWF e1 := ExprWF.mk_const hn1wf hv1wf he1
  obtain ⟨lhss, hlhss, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlhssv, hlhsswf⟩ := ExprOps.mk_app_n_refines he1wf hlargswf hlhss
  obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hheadv, hheadwf⟩ := ExprOps.get_app_fn_refines hsb hhead
  obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hargsv, hargswf⟩ := ExprOps.get_app_args_refines hsb hargs
  -- the shape probe: three arguments and a one-level `.const` head
  obtain ⟨pq, hpq, hz⟩ := bind_eq_ok_iff.mp h
  obtain ⟨head1, shaped⟩ := pq
  by_cases hlen : alloc.vec.Vec.len args = 3#usize
  · rw [if_pos hlen] at hpq
    obtain ⟨⟨d0, k0⟩⟩ := head
    cases k0
    case Const =>
      rename_i n0 us0 _
      obtain ⟨hn0wf, hus0wf⟩ := CoreK.ExprWF.const_children hheadwf rfl
      simp only [ExprOps.node_kind, arc_deref_eq, bind_tc_ok, Result.ok.injEq,
        Prod.mk.injEq] at hpq
      obtain ⟨rfl, rfl⟩ := hpq
      simp at hz
      split at hz
      · rename_i hus1
        have hlen3 : args.val.length = 3 := by
          have := alloc.vec.Vec.len_val args; scalar_tac
        have hus0len : us0.val.length = 1 := by
          have := alloc.vec.Vec.len_val us0; scalar_tac
        obtain ⟨l0, hl0⟩ : ∃ l0, us0.val = [l0] := by
          rcases hl : us0.val with _ | ⟨x, xs⟩
          · rw [hl] at hus0len; simp at hus0len
          · rcases xs with _ | ⟨y, ys⟩
            · exact ⟨x, rfl⟩
            · rw [hl] at hus0len; simp at hus0len
        have hheadabs : absExpr (expr.Expr.mk (expr.ExprNode.mk d0
            (expr.ExprKind.Const n0 us0)))
            = ConLeche.Expr.const (absName n0) [absLevel l0] := by
          simp only [absExpr_mk, absExprKind, absLevels, hl0]
          rfl
        obtain ⟨a0, a1, a2, hav⟩ : ∃ a0 a1 a2, args.val = [a0, a1, a2] := by
          rcases hl : args.val with _ | ⟨a0, l1⟩
          · rw [hl] at hlen3; simp at hlen3
          rcases l1 with _ | ⟨a1, l2⟩
          · rw [hl] at hlen3; simp at hlen3
          rcases l2 with _ | ⟨a2, l3⟩
          · rw [hl] at hlen3; simp at hlen3
          rcases l3 with _ | ⟨a3, l4⟩
          · exact ⟨a0, a1, a2, rfl⟩
          · rw [hl] at hlen3; simp at hlen3
        have hargidx : ∀ (j : Std.Usize) (hj : j.val < args.val.length),
            alloc.vec.Vec.index_usize args j = ok (args.val[j.val]'hj) := by
          intro j hj
          obtain ⟨y0, hy0, hy0v⟩ :=
            WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec args j hj)
          subst hy0v
          exact hy0
        have hspine : absExpr sbody
            = .app (.app (.app (.const (absName n0) [absLevel l0])
                (absExpr a0)) (absExpr a1)) (absExpr a2) := by
          refine expr_app3_of_spine ?_ ?_
          · rw [← hheadv, hheadabs]
          · rw [← hargsv, absExprs, hav]; rfl
        have ha0wf : ExprWF a0 := hargswf a0 (by rw [hav]; simp)
        have ha1wf : ExprWF a1 := hargswf a1 (by rw [hav]; simp)
        have ha2wf : ExprWF a2 := hargswf a2 (by rw [hav]; simp)
        obtain ⟨b, hb, hz⟩ := bind_eq_ok_iff.mp hz
        have hbv : b = ConLeche.isEqHead (absExpr (expr.Expr.mk
            (expr.ExprNode.mk d0 (expr.ExprKind.Const n0 us0)))) :=
          hcb.isEqHead _ b hheadwf hb
        rw [hheadabs] at hbv
        by_cases hbt : b = true
        · rw [if_pos hbt] at hz
          rw [hbt] at hbv
          have hceq : absName n0 = ConLeche.eqName := by
            have hx := hbv.symm
            simp only [ConLeche.isEqHead] at hx
            exact of_decide_eq_true (by simpa using hx)
          obtain ⟨e2, he2, hz⟩ := bind_eq_ok_iff.mp hz
          obtain ⟨b1, hb1, hz⟩ := bind_eq_ok_iff.mp hz
          have he2v : e2 = a1 := by
            have hx := hargidx 1#usize (by rw [hav]; norm_num)
            rw [he2, Result.ok.injEq] at hx
            rw [hx]; simp [hav]
          have hb1v : b1 = decide (absExpr e2 = absExpr lhss) :=
            Expr.beq_refines (by rw [he2v]; exact ha1wf) hlhsswf hb1
          by_cases hb1t : b1 = true
          · rw [if_pos hb1t] at hz
            rw [hb1t] at hb1v
            obtain ⟨e3, he3, hz⟩ := bind_eq_ok_iff.mp hz
            obtain ⟨i2, hi2, hz⟩ := bind_eq_ok_iff.mp hz
            obtain ⟨i3, hi3, hz⟩ := bind_eq_ok_iff.mp hz
            obtain ⟨e4, he4, hz⟩ := bind_eq_ok_iff.mp hz
            obtain ⟨b2, hb2, hz⟩ := bind_eq_ok_iff.mp hz
            have hi2v : i2.val = 1 + i.val := HashMap.uscalar_add_eq hi2
            have hi3v : i3.val = n_f.val - 1 - i.val := by
              rw [ExprOps.sub_nat_val hi3, hi2v]; omega
            have he4v : absExpr e4
                = ConLeche.Expr.bvar (n_f.val - 1 - i.val) := by
              rw [Expr.bvar_refines he4, hi3v]
            have he3v : e3 = a2 := by
              have hx := hargidx 2#usize (by rw [hav]; norm_num)
              rw [he3, Result.ok.injEq] at hx
              rw [hx]; simp [hav]
            have hb2v : b2 = decide (absExpr e3 = absExpr e4) :=
              Expr.beq_refines (by rw [he3v]; exact ha2wf) (ExprWF.bvar he4) hb2
            by_cases hb2t : b2 = true
            · rw [if_pos hb2t] at hz
              rw [hb2t] at hb2v
              obtain ⟨o, ho, hz⟩ := bind_eq_ok_iff.mp hz
              obtain ⟨hoabs, howf⟩ :=
                hcb.openPisAtFvarsF depth tcv.ty 0#u64 o htcv.2.2 ho
              cases o with
              | none => simp at hz
              | some oq =>
              obtain ⟨fvs, e5⟩ := oq
              obtain ⟨hfvswf, he5wf⟩ := howf _ rfl
              simp only [Option.map_some] at hoabs
              rw [hdepthv, show ((0#u64 : Std.U64)).val = 0 from rfl,
                ConLeche.openPisAtFvarsF_eq] at hoabs
              obtain ⟨targs, htargs, hz⟩ := bind_eq_ok_iff.mp hz
              obtain ⟨htargsv, htargswf⟩ :=
                ExprOps.get_app_args_refines he5wf htargs
              obtain ⟨alpha, halpha, hz⟩ := bind_eq_ok_iff.mp hz
              obtain ⟨lft, hlft, hz⟩ := bind_eq_ok_iff.mp hz
              obtain ⟨rgt, hrgt, hz⟩ := bind_eq_ok_iff.mp hz
              obtain ⟨la, hla, hz⟩ := bind_eq_ok_iff.mp hz
              obtain ⟨halphav, halphawf⟩ := arg_get_d_refines htargswf halpha
              obtain ⟨hlftv, hlftwf⟩ := arg_get_d_refines htargswf hlft
              obtain ⟨hrgtv, hrgtwf⟩ := arg_get_d_refines htargswf hrgt
              obtain ⟨hlav, hlawf⟩ := hcb.eqHeadLevel _ la hheadwf hla
              rw [hheadabs] at hlav
              obtain ⟨lst', hrun, hrel', hwf'⟩ :=
                check_iota_sides_ty_refines hw hcb hst hfe halphawf hlftwf
                  hrgtwf hlawf hz lst lfe
                  (ConLeche.projModelName (absName t) i.val) hrel hfer
              refine ⟨lst', ?_, hrel', hwf'⟩
              rw [hspine]
              have heqa1 : absExpr a1 = absExpr lhss := by
                rw [← he2v]; exact of_decide_eq_true hb1v.symm
              have heqa2 : absExpr a2
                  = ConLeche.Expr.bvar (n_f.val - 1 - i.val) := by
                rw [← he4v, ← he3v]; exact of_decide_eq_true hb2v.symm
              have hlhstarget : absExpr lhss = ConLeche.Expr.mkAppN
                  (.const (ConLeche.projModelName (absName t) i.val)
                    ((absNames lps).map ConLeche.Level.param))
                  (((List.range n_p.val).map fun k =>
                      ConLeche.Expr.bvar (n_p.val + n_f.val - 1 - k))
                    ++ [ConLeche.Expr.mkAppN
                          (.const ((absName cvj.name).str "_model")
                            ((absNames cvj.level_params).map
                              ConLeche.Level.param))
                          (((List.range n_p.val).map fun k =>
                              ConLeche.Expr.bvar (n_p.val + n_f.val - 1 - k))
                            ++ (List.range n_f.val).map fun k =>
                                 ConLeche.Expr.bvar (n_f.val - 1 - k))]) := by
                rw [hlhssv, he1v, hlargsv, hmkv, hev, hsp1v, hspv, hpav', hxav]
              have hside : (ConLeche.checkIotaSidesTy
                  (m := ConLeche.Cached.CheckCM) (absMode mode)
                  (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe.env
                  (n_p.val + n_f.val)
                  ((absExpr e5).getAppArgs.getD 0 (.bvar 0))
                  ((absExpr e5).getAppArgs.getD 1 (.bvar 0))
                  ((absExpr e5).getAppArgs.getD 2 (.bvar 0))
                  (ConLeche.eqHeadLevel
                    (ConLeche.Expr.const (absName n0) [absLevel l0]))
                  (ConLeche.projModelName (absName t) i.val)).run lst
                  = .ok ((), lst') := by
                rw [show ((0#usize : Std.Usize)).val = 0 from rfl] at halphav
                rw [show ((1#usize : Std.Usize)).val = 1 from rfl] at hlftv
                rw [show ((2#usize : Std.Usize)).val = 2 from rfl] at hrgtv
                rw [← hdepthv, ← htargsv, ← halphav, ← hlftv, ← hrgtv, ← hlav]
                exact hrun
              exact checkProjIotaBody_run (fvs := absExprs fvs)
                (sbodyO := absExpr e5) hceq
                (by rw [heqa1, hlhstarget]; simp [absConstantVal])
                (by rw [heqa2]; simp)
                (by simpa [absConstantVal] using hoabs.symm) hside
            · simp only [Bool.not_eq_true] at hb2t
              rw [if_neg (by simp [hb2t])] at hz; simp at hz
          · simp only [Bool.not_eq_true] at hb1t
            rw [if_neg (by simp [hb1t])] at hz; simp at hz
        · simp only [Bool.not_eq_true] at hbt
          rw [if_neg (by simp [hbt])] at hz; simp at hz
      · simp at hz
    all_goals simp only [ExprOps.node_kind, arc_deref_eq, bind_tc_ok,
      Result.ok.injEq, Prod.mk.injEq] at hpq
    all_goals rw [← hpq.2] at hz
    all_goals simp at hz
  · rw [if_neg hlen, Result.ok.injEq, Prod.mk.injEq] at hpq
    rw [← hpq.2] at hz
    simp at hz

omit hw hcb in
/-- `thm_probe`'s inversion: a `some` answer pins the stored constant to a
theorem record, which is what the cited `let some (.thmInfo tcv _) := …`
pattern reads.  The twin of `ctorOf_inv`/`defnOf_inv`. -/
theorem thmOf_inv {X : Option ConLeche.ConstantInfo}
    {cv : ConLeche.ConstantVal}
    (h : (match X with
          | some (.thmInfo tcv _) => some tcv
          | _ => none) = some cv) :
    ∃ v, X = some (.thmInfo cv v) := by
  cases X with
  | none => simp at h
  | some ci =>
    cases ci
    case thmInfo cv0 v0 =>
      simp only [Option.some.injEq] at h
      exact ⟨v0, by rw [h]⟩
    all_goals simp at h

omit hw hcb in
/-- `checkProjIotaF`'s pins discharged: past the `.thmInfo` lookup, the level
pin and the two telescopes, the cited body *is* `checkProjIotaBody` — at the
stored constant's own name, which is the name it was found under
(`FEnv.canon_find_name`), so the two spine heads are one. -/
theorem checkProjIotaF_run {lmode : ConLeche.CheckMode} {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name}
    {cvj tcv : ConLeche.ConstantVal} {nP nF i : Nat} {rh : ConLeche.Expr}
    {sbs cbs : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {sbody cbody : ConLeche.Expr} {lst lst' : ConLeche.Cached.CState}
    (hname : cvj.name = ctorName)
    (hfind : lfe.find? ((ConLeche.projModelName T i).str "iota")
      = some (.thmInfo tcv rh))
    (hlp : tcv.levelParams = lps)
    (hsp : tcv.type.stripPis (nP + nF) = some (sbs, sbody))
    (hcp : cvj.type.stripPis (nP + nF) = some (cbs, cbody))
    (hdm : ConLeche.domsMatchAux
        (fun _ e => ConLeche.Expr.renameConsts
          (ConLeche.projFwd T ctorName nF) e) sbs cbs 0 0 (nP + nF) = true)
    (hbody : (checkProjIotaBody lmode lfe T cvj lps nP nF i tcv sbody).run lst
      = .ok ((), lst')) :
    (ConLeche.checkProjIotaF (m := ConLeche.Cached.CheckCM) lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe T ctorName lps cvj nP nF
        i).run lst = .ok ((), lst') := by
  subst hname
  have key : ConLeche.checkProjIotaF (m := ConLeche.Cached.CheckCM) lmode
      (ConLeche.Cached.sharedOpsC lmode lfe) lfe T cvj.name lps cvj nP nF i
      = checkProjIotaBody lmode lfe T cvj lps nP nF i tcv sbody := by
    rw [ConLeche.checkProjIotaF, checkProjIotaBody.eq_def]
    simp only [hfind, hlp, hsp, hcp, hdm, if_true, pure_bind]
    split
    · rfl
    · rename_i hne
      split
      · exact ((hne _ _ _ _ _) rfl).elim
      · rfl
  rw [key]
  exact hbody

/-- `ConLeche/Kernel/DeclCheck.lean:797-836` — **`check_proj_iota` refines
`checkProjIotaF`**: the model's `proj_i.iota` theorem pins the rule.

`hcname` (added at task #59) — the statement is **false** without it.  The
port's body (`modeled.rs:2149`) builds the constructor spine head from the
*passed* `cvj.name`, where the cited `checkProjIotaF` writes the *looked-up*
`ctorName`; here `cvj` is a parameter, so nothing ties the two together.  The
only caller, `check_proj_fn_refines`, discharges it: its `cvj` comes out of
`check_proj_lookups`' `fe.find? ctorName`, and a canonical index answers under
the name it stores (`FEnv.canon_find_name`), which is why `FEnvCanon fe2`
appears there rather than here. -/
theorem check_proj_iota_refines
    {st st' : cached.state_c.CState} {fe2 fe_self : fenv.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {cvj : env.ConstantVal} {n_p n_f i : Std.U64}
    (hspines : StructSpinesRefine)
    (hcname : absName cvj.name = absName ctor_name)
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
  intro lst lfe2 lfe hrel hr2 hrS heq
  subst heq
  rw [inductives.modeled.check_proj_iota] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnv, hnwf⟩ := proj_iota_name_refines ht hn
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := thm_probe_refines hr2 hfe2 hnwf ho
  rw [hnv] at hoabs
  cases o with
  | none => simp at h
  | some tcv =>
  have htcvwf : ConstantValWF tcv := howf tcv rfl
  simp only [Option.map_some] at hoabs
  obtain ⟨rh, hfind⟩ := thmOf_inv hoabs.symm
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := Env.names_beq_refines htcvwf.2.1 hlps hb
  by_cases hbt : b = true
  · rw [if_pos hbt] at h
    rw [hbt] at hbv
    have hlpseq : absNames tcv.level_params = absNames lps :=
      of_decide_eq_true hbv.symm
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    have hi1v : i1.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hi1
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_pis_refines htcvwf.2.2 ho1
    rw [hi1v] at ho1abs
    cases o1 with
    | none => simp at h
    | some sq =>
    obtain ⟨sbs, sbody⟩ := sq
    obtain ⟨hsbswf, hsbodywf⟩ := ho1wf _ rfl
    simp only [Option.map_some] at ho1abs
    obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho2abs, ho2wf⟩ := ExprOps.strip_pis_refines hcvj.2.2 ho2
    rw [hi1v] at ho2abs
    cases o2 with
    | none => simp at h
    | some cq =>
    obtain ⟨cbs, cbody⟩ := cq
    obtain ⟨hcbswf, hcbodywf⟩ := ho2wf _ rfl
    simp only [Option.map_some] at ho2abs
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := hcb.domsMatchAux
      inductives.modeled.DomProjFwd.Insts.Con_ron_coreKernelChecker_baseDomView
      { t := t, ctor := ctor_name, n_f := n_f }
      (fun _ e => ConLeche.Expr.renameConsts
        (ConLeche.projFwd (absName t) (absName ctor_name) n_f.val) e)
      (dom_proj_fwd_view_refines ht hc) sbs cbs 0#u64 0#u64 i1 b1 hsbswf hcbswf
      hb1
    rw [hi1v, show ((0#u64 : Std.U64)).val = 0 from rfl] at hb1v
    by_cases hb1t : b1 = true
    · rw [if_pos hb1t] at h
      rw [hb1t] at hb1v
      obtain ⟨lst', hrun, hrel', hwf'⟩ :=
        check_proj_iota_body_refines hw hcb hspines hst hfe ht hcvj hlps htcvwf
          hsbodywf h lst lfe2 hrel hrS
      refine ⟨lst', ?_, hrel', hwf'⟩
      exact checkProjIotaF_run (rh := rh) (cbody := absExpr cbody) hcname hfind
        hlpseq ho1abs.symm ho2abs.symm hb1v.symm hrun
    · simp only [Bool.not_eq_true] at hb1t
      rw [if_neg (by simp [hb1t])] at h; simp at h
  · simp only [Bool.not_eq_true] at hbt
    rw [if_neg (by simp [hbt])] at h; simp at h

omit hw hcb in
/-- `checkProjFnS`' success path, run: the two lookups (both state-neutral),
the shape pin, the index bound and the two stateful stages, composed into the
cited stage's own run.  `check_proj_fn_refines` supplies each from the port's
answer. -/
theorem checkProjFnS_run {lmode : ConLeche.CheckMode} {lfe : ConLeche.FEnv}
    {T ctorName : ConLeche.Name} {lps : List ConLeche.Name} {nP nF i : Nat}
    {cvj mcv : ConLeche.ConstantVal} {pty rhsA : ConLeche.Expr}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (h1 : (ConLeche.checkProjLookupsF (m := ConLeche.Cached.CheckCM) lfe T
        ctorName lps nP nF i).run lst = .ok ((cvj, mcv), lst))
    (h2 : (ConLeche.checkProjTyF (m := ConLeche.Cached.CheckCM) lfe T ctorName
        lps mcv.type nP nF).run lst = .ok (pty, lst))
    (h3 : ConLeche.checkProjShape (m := ConLeche.Cached.CheckCM) pty cvj.type
        nP nF = pure ())
    (h4 : i < nF)
    (h5 : (ConLeche.checkProjRuleF (ConLeche.Cached.sharedOpsC lmode lfe) lfe
        pty cvj lps nP nF i).run lst = .ok (rhsA, lst1))
    (h6 : (ConLeche.checkProjIotaF (m := ConLeche.Cached.CheckCM) lmode
        (ConLeche.Cached.sharedOpsC lmode lfe) lfe T ctorName lps cvj nP nF
        i).run lst1 = .ok ((), lst2)) :
    (ConLeche.Cached.checkProjFnS lmode lfe T ctorName lps nP nF i).run lst
      = .ok (lfe.push (.recInfo ⟨ConLeche.projFnName T i, lps, pty⟩ nP nP
          [ConLeche.projFnRule lfe.find? T ctorName pty nP nF i rhsA]),
        lst2) := by
  rw [ConLeche.Cached.checkProjFnS]
  simp only [StateT.run] at h1 h2 h5 h6
  simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure, h1, h2, h3, h4, h5, h6]

/-- `ConLeche/Cached/CheckerC.lean:153-166` — **`check_proj_fn` refines
`checkProjFnS`**: the public projection function for field `i`, stored as a
degenerate recursor carrying one rule.  The cited stage has no flush of its
own, so this statement is against `checkProjFnS` unmodified.

`hcan` (added at task #59): the stage feeds its looked-up `cvj` to
`check_proj_iota_refines`, whose `hcname` needs the index to answer under the
name it stores.  `FEnv.canon_find_name` is what says that, and it holds of
every canonical view; `Refine/IndC.lean` discharges it at the driver from
`dup_canon`/`mk_fenv_canon`, exactly as it already does for
`check_ind_recs_refines`. -/
theorem check_proj_fn_refines
    {st st' : cached.state_c.CState} {fe2 fe' : fenv.FEnv}
    {t ctor_name : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f i : Std.U64}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    (hst : StateWF st) (hfe : FEnvWF fe2) (hcan : FEnv.FEnvCanon fe2)
    (hfull : FEnv.FEnvFull fe2)
    (ht : NameWF t) (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : inductives.modeled.check_proj_fn mode st fe2 t ctor_name lps n_p n_f i
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkProjFnS (absMode mode) lfe (absName t)
            (absName ctor_name) (absNames lps) n_p.val n_f.val i.val).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  intro lst lfe hrel hfer
  rw [inductives.modeled.check_proj_fn] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok lq =>
  obtain ⟨cvj, mcv⟩ := lq
  obtain ⟨hlk, hcvjwf, hmcvwf, hfindc⟩ :=
    check_proj_lookups_refines hw hcb hfer hfe ht hc hlps hr
  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
  cases r1 with
  | Err e => simp at h
  | Ok pty =>
  obtain ⟨hty, hptywf⟩ :=
    check_proj_ty_refines hw hcb hres hfer hfe ht hc hlps hmcvwf.2.2 hr1
  obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
  cases r2 with
  | Err e => simp at h
  | Ok u =>
  cases u
  have hshape := hcb.checkProjShape pty cvj.ty n_p n_f hptywf hcvjwf.2.2 hr2
  by_cases hge : i ≥ n_f
  · rw [if_pos hge] at h; simp at h
  · rw [if_neg hge] at h
    have hlt : i.val < n_f.val := by scalar_tac
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r3, st1⟩ := p
    cases r3 with
    | Err e => simp at h
    | Ok rhs_a =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hrhswf⟩ :=
      hcb.checkProjRule st fe2 pty cvj lps n_p n_f i rhs_a st1 hst hfe hptywf
        hcvjwf hlps hp lst lfe hrel hfer
    obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r4, st2⟩ := p2
    cases r4 with
    | Err e => simp at h
    | Ok u2 =>
    cases u2
    have hcname : absName cvj.name = absName ctor_name := by
      exact FEnv.canon_find_name hcan hfer hc hfindc
    obtain ⟨lst2, hrun2, hrel2, hwf2⟩ :=
      check_proj_iota_refines hw hcb hspines hcname hwf1 hfe hfe ht hc hlps
        hcvjwf hp2 lst1 lfe lfe hrel1 hfer hfer rfl
    obtain ⟨rr, hrr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hrrv, hrrwf⟩ :=
      CoreK.proj_fn_rule_refines CoreK.envFacts
        (FindAgree.of_rel hfer hfe) (FindWF.of_wf hfe) ht hc hptywf hrhswf hrr
    obtain ⟨rules, hrules, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
    have hnmv : absName nm = ConLeche.projFnName (absName t) i.val :=
      Env.proj_fn_name_refines hnm
    have hnmwf : NameWF nm := Env.proj_fn_name_wf ht hnm
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    have hvv : absNames v = absNames lps := by
      rw [absNames, absNames, PropWhen.names_copy_val hv]
    have hvwf : NamesWF v := by
      intro x hx; exact hlps x (by rwa [PropWhen.names_copy_val hv] at hx)
    obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
    have hcivwf : ConstantInfoWF (env.ConstantInfo.RecInfo
        { «name» := nm, level_params := v, ty := pty } n_p n_p rules) := by
      refine ⟨⟨hnmwf, hvwf, hptywf⟩, ?_⟩
      intro x hx
      rw [vec_push_val hrules] at hx
      simp at hx
      rw [hx]; exact hrrwf
    obtain ⟨hprel, hpwf⟩ := FEnv.push_refines hfer hfe hcivwf hf
    obtain ⟨hpcan, hpfull⟩ := FEnv.push_canon hfe hcivwf hcan hfull hf
    simp only [Result.ok.injEq, Prod.mk.injEq,
      core.result.Result.Ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hrulesv : (rules.val.map absRecRule) = [absRecRule rr] := by
      rw [vec_push_val hrules]
      simp [alloc.vec.Vec.new]
    refine ⟨lst2, lfe.push (.recInfo ⟨ConLeche.projFnName (absName t) i.val,
      absNames lps, absExpr pty⟩ n_p.val n_p.val
      [ConLeche.projFnRule lfe.find? (absName t) (absName ctor_name)
        (absExpr pty) n_p.val n_f.val i.val (absExpr rhs_a)]), ?_, hrel2, ?_,
      hwf2, hpwf, hpcan, hpfull⟩
    · exact checkProjFnS_run (hlk lst) (hty lst) hshape hlt hrun1 hrun2
    · have hci : absConstantInfo (env.ConstantInfo.RecInfo
          { «name» := nm, level_params := v, ty := pty } n_p n_p rules)
          = .recInfo ⟨ConLeche.projFnName (absName t) i.val, absNames lps,
              absExpr pty⟩ n_p.val n_p.val
              [ConLeche.projFnRule lfe.find? (absName t) (absName ctor_name)
                (absExpr pty) n_p.val n_f.val i.val (absExpr rhs_a)] := by
        simp only [absConstantInfo, absConstantVal, hnmv, hvv, hrulesv, hrrv]
      rw [← hci]
      exact hprel

/-- `ConLeche/Cached/CheckerC.lean:171-175` (minus the flush) — **the
`install_proj_fn_step` stage**: one projection install, skipped where the
model's projection artifact is absent.

`hcan` and `hspines` are here only to be handed to `check_proj_fn_refines`;
see its note. -/
theorem install_proj_fn_step_refines
    {st st' : cached.state_c.CState} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f i : Std.U64} {fe2 fe' : fenv.FEnv}
    (hres : StructInstall.ConstsResolveFFastRefines)
    (hspines : StructSpinesRefine)
    (hst : StateWF st) (hfe : FEnvWF fe2) (hcan : FEnv.FEnvCanon fe2)
    (hfull : FEnv.FEnvFull fe2)
    (ht : NameWF t) (hc : NameWF ctor_name) (hlps : NamesWF lps)
    (h : inductives.modeled.install_proj_fn_step mode st t ctor_name lps n_p n_f
        fe2 i = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst' lfe',
        (installProjFnStepN (absMode mode) (absName t) (absName ctor_name)
            (absNames lps) n_p.val n_f.val lfe i.val).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  intro lst lfe hrel hfer
  rw [inductives.modeled.install_proj_fn_step] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := CoreK.proj_model_name_refines ht hn
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hoabs : o.map absConstantInfo
      = lfe.find? (ConLeche.projModelName (absName t) i.val) := by
    rw [← hnabs]; exact FEnv.find_refines hfer hfe hnwf ho
  have hsome : (core.option.Option.is_some o)
      = (lfe.find? (ConLeche.projModelName (absName t) i.val)).isSome := by
    rw [← hoabs]; cases o <;> rfl
  rw [installProjFnStepN]
  -- the `let b := …` Aeneas emits for the `is_some` test is not a monadic
  -- bind, so it goes by ascription before `split` can fire
  replace h : (if (core.option.Option.is_some o) = true then
        inductives.modeled.check_proj_fn mode st fe2 t ctor_name lps n_p n_f i
      else ok (.Ok fe2, st))
      = (ok (.Ok fe', st') : Result ((core.result.Result _ core_types.CheckError)
          × cached.state_c.CState)) := h
  split at h
  · rename_i hb
    rw [if_pos (by rw [← hsome]; exact hb)]
    exact check_proj_fn_refines hw hcb hres hspines hst hfe hcan hfull ht hc hlps
      h lst lfe hrel hfer
  · rename_i hb
    rw [if_neg (by rw [← hsome]; exact hb)]
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lst, lfe, rfl, hrel, hfer, hst, hfe, hcan, hfull⟩

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

/-- The index recursion behind `expr_ops::dom_at_n`: `j` walks the `Vec` while
`i` counts down, so the answer is the binder `i` slots past `j`.

This lemma and the next belong in `Refine/ExprOps*.lean` — `dom_at_n` is an
`expr_ops` function — and should move there on merge; they live here because
`check_eta_thm_shape` and `check_unit_thm_shape`, added by task #62's sweep,
are `dom_at_n`'s only callers so far. -/
theorem dom_at_n_from_val (N : Nat) :
    ∀ (doms : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) (i : Std.U64)
      (j : Std.Usize) (o : Option expr.Expr),
      i.val = N →
      expr_ops.dom_at_n_from doms i j = ok o →
      o = (doms.val[j.val + i.val]?).map Prod.fst := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro doms i j o hN h
    rw [expr_ops.dom_at_n_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : doms.val.length ≤ j.val := by
        have := alloc.vec.Vec.len_val doms; scalar_tac
      rw [← Result.ok_injective h, List.getElem?_eq_none (by omega)]
      rfl
    · rename_i hge
      have hlt : j.val < doms.val.length := by
        have := alloc.vec.Vec.len_val doms; scalar_tac
      split at h
      · rename_i hz
        have hiz : i.val = 0 := by rw [hz]; rfl
        obtain ⟨y, hy, hyv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec doms j hlt)
        subst hyv
        simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
        obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
        rw [Expr.dup_eq he1] at h
        rw [← Result.ok_injective h, hiz, Nat.add_zero,
          List.getElem?_eq_getElem hlt]
        rfl
      · rename_i hz
        have hiz : i.val ≠ 0 := fun hc => hz (by scalar_tac)
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, i3, hi3, hrec⟩ := h
        have hi2v : i2.val = i.val - 1 :=
          (ConRon.Refine.Nat.usub_val hi2).2.trans (by simp)
        have hi3v : i3.val = j.val + 1 := HashMap.uscalar_add_eq hi3
        rw [ih i2.val (by omega) doms i2 i3 o rfl hrec, hi3v, hi2v,
          show j.val + 1 + (i.val - 1) = j.val + i.val by omega]

/-- `expr_ops::dom_at_n` is `doms[i]?`, read for its domain: the `i`-th
binder's domain, or `none` when the telescope is shorter.  The `u64` index
never crosses to `usize` (task #62), so there is no `≤ Usize.max` side
condition.  Stated in the two halves the `match` consumers peel. -/
theorem dom_at_n_refines {doms : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {i : Std.U64} {o : Option expr.Expr} (hdoms : ExprOps.BindersWF doms)
    (h : expr_ops.dom_at_n doms i = ok o) :
    (o = none → (ExprOps.absBinders doms)[i.val]? = none)
      ∧ ∀ e, o = some e →
          (∃ m, (ExprOps.absBinders doms)[i.val]? = some (absExpr e, m))
            ∧ ExprWF e := by
  rw [expr_ops.dom_at_n] at h
  have hv := dom_at_n_from_val i.val doms i 0#usize o rfl h
  rw [show ((0#usize : Std.Usize)).val = 0 from rfl, Nat.zero_add] at hv
  constructor
  · intro hn
    rw [hn] at hv
    rw [ExprOps.absBinders, List.getElem?_map]
    cases hx : doms.val[i.val]? with
    | none => rfl
    | some p => rw [hx] at hv; simp at hv
  · intro e he
    rw [he] at hv
    cases hx : doms.val[i.val]? with
    | none => rw [hx] at hv; simp at hv
    | some p =>
      rw [hx] at hv
      simp only [Option.map_some, Option.some.injEq] at hv
      subst hv
      exact ⟨⟨absBinderMeta p.2, by
        rw [ExprOps.absBinders, List.getElem?_map, hx]; rfl⟩,
        (hdoms p (List.mem_of_getElem? hx)).1⟩

/-- `Expr`'s `BEq` is its `decide`, as `Refine/Expr.lean`'s `beq_refines`
states it. -/
theorem beq_eq_decide_expr (a b : ConLeche.Expr) :
    (a == b) = decide (a = b) := by
  rw [Bool.eq_iff_iff]; simp

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
  rw [inductives.modeled.check_eta_thm_shape] at h
  rw [checkEtaThmShape]
  obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
  have hkv : k.val = n_p.val + 1 := HashMap.uscalar_add_eq hk
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines htty ho
  rw [hkv] at hoabs
  rw [← hoabs]
  cases o with
  | none => simp only [Option.map_none]; simp at h; simp [← h]
  | some sq =>
  obtain ⟨sbs, sbody⟩ := sq
  obtain ⟨hsbswf, hsbodywf⟩ := howf _ rfl
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_pis_refines httym ho1
  rw [← ho1abs]
  cases o1 with
  | none => simp only [Option.map_none, Option.map_some]; simp at h; simp [← h]
  | some mq =>
  obtain ⟨tbs, tbody⟩ := mq
  obtain ⟨htbswf, htbodywf⟩ := ho1wf _ rfl
  simp only [Option.map_some]
  simp at h
  have hz : ((0#u64 : Std.U64)).val = 0 := rfl
  have hEq_inv : ∀ (e : ConLeche.Expr), ConLeche.isEqHead e = true →
      ∃ c lA, e = .const c [lA] := by
    intro e he
    cases e with
    | const c us =>
      cases us with
      | nil => simp [ConLeche.isEqHead] at he
      | cons l ls =>
        cases ls with
        | nil => exact ⟨c, l, rfl⟩
        | cons _ _ => simp [ConLeche.isEqHead] at he
    | _ => simp [ConLeche.isEqHead] at he
  rcases h with ⟨hbd, rfl⟩ | ⟨hbd, h⟩
  · have hbdv := hcb.domsMatchAux _ () (fun _ e => e) dom_ident_view_gl sbs tbs
      0#u64 0#u64 n_p false hsbswf htbswf hbd
    rw [hz] at hbdv
    rw [← hbdv]
    simp
  · have hbdv := hcb.domsMatchAux _ () (fun _ e => e) dom_ident_view_gl sbs tbs
      0#u64 0#u64 n_p true hsbswf htbswf hbd
    rw [hz] at hbdv
    obtain ⟨nm, hnm, us, hus, fam, hfam, v3, hv3, xdom, hxdom, o2, ho2, h⟩ := h
    obtain ⟨hnmv, hnmwf⟩ := model_of_refines ht hnm
    obtain ⟨husv, huswf⟩ := hspines.1 lps us hlps hus
    have hfamv : absExpr fam
        = ConLeche.Expr.const ((absName t).str "_model")
            ((absNames lps).map ConLeche.Level.param) := by
      rw [Expr.mk_const_refines hfam, hnmv, husv]
    have hfamwf : ExprWF fam := ExprWF.mk_const hnmwf huswf hfam
    obtain ⟨hv3v, hv3wf⟩ := hspines.2.2.2 0#u64 n_p v3 hv3
    obtain ⟨hxdomv, hxdomwf⟩ := ExprOps.mk_app_n_refines hfamwf hv3wf hxdom
    obtain ⟨ho2none, ho2some⟩ := dom_at_n_refines hsbswf ho2
    have hxtarget : absExpr xdom
        = ConLeche.Expr.mkAppN
            (.const ((absName t).str "_model")
              ((absNames lps).map ConLeche.Level.param))
            ((List.range n_p.val).map
              (fun k => ConLeche.Expr.bvar (n_p.val - 1 - k))) := by
      rw [hxdomv, hfamv, hv3v, ConLeche.structPsAt]
      simp
    rw [← hbdv]
    cases o2 with
    | none =>
      rw [ho2none rfl]
      simp at h
      subst h
      simp
    | some e3 =>
      obtain ⟨⟨bm3, he3idx⟩, he3wf⟩ := ho2some e3 rfl
      simp at h
      rw [he3idx]
      rcases h with ⟨hb1, rfl⟩ | ⟨hb1, head, hhead, args, hargs, h⟩
      · have hb1v : (false : Bool) = decide (absExpr e3 = absExpr xdom) :=
          Expr.beq_refines he3wf hxdomwf hb1
        have hne : absExpr e3 ≠ absExpr xdom := of_decide_eq_false hb1v.symm
        rw [hxtarget] at hne
        simp [hne]
      · have hb1v : (true : Bool) = decide (absExpr e3 = absExpr xdom) :=
          Expr.beq_refines he3wf hxdomwf hb1
        have heq1 : absExpr e3 = absExpr xdom := of_decide_eq_true hb1v.symm
        rw [hxtarget] at heq1
        rw [heq1]
        simp only [beq_self_eq_true, Bool.true_and]
        obtain ⟨hheadv, hheadwf⟩ := ExprOps.get_app_fn_refines hsbodywf hhead
        obtain ⟨hargsv, hargswf⟩ := ExprOps.get_app_args_refines hsbodywf hargs
        by_cases hlen3 : args.val.length = 3
        · rw [if_pos hlen3] at h
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2v : b2 = ConLeche.isEqHead (absExpr head) :=
            hcb.isEqHead head b2 hheadwf hb2
          by_cases hb2t : b2 = true
          · rw [if_pos hb2t] at h
            rw [hb2t] at hb2v
            obtain ⟨c, lA, hheadc⟩ := hEq_inv _ hb2v.symm
            obtain ⟨a0, a1, a2, hav⟩ : ∃ a0 a1 a2, args.val = [a0, a1, a2] := by
              rcases hl : args.val with _ | ⟨a0, l1⟩
              · rw [hl] at hlen3; simp at hlen3
              rcases l1 with _ | ⟨a1, l2⟩
              · rw [hl] at hlen3; simp at hlen3
              rcases l2 with _ | ⟨a2, l3⟩
              · rw [hl] at hlen3; simp at hlen3
              rcases l3 with _ | ⟨a3, l4⟩
              · exact ⟨a0, a1, a2, rfl⟩
              · rw [hl] at hlen3; simp at hlen3
            have hargidx : ∀ (j : Std.Usize) (hj : j.val < args.val.length),
                alloc.vec.Vec.index_usize args j = ok (args.val[j.val]'hj) := by
              intro j hj
              obtain ⟨y0, hy0, hy0v⟩ :=
                WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec args j hj)
              subst hy0v
              exact hy0
            have hspine : absExpr sbody
                = .app (.app (.app (.const c [lA]) (absExpr a0))
                    (absExpr a1)) (absExpr a2) := by
              refine expr_app3_of_spine ?_ ?_
              · rw [← hheadv, hheadc]
              · rw [← hargsv, absExprs, hav]; rfl
            have hceq : (c == ConLeche.eqName) = true := by
              have hx := hb2v.symm
              rw [hheadc] at hx
              simpa [ConLeche.isEqHead] using hx
            rw [hspine]
            simp only []
            rw [hceq]
            obtain ⟨e4, he4, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨e5, he5, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
            have he4v : e4 = a1 := by
              have hx := hargidx 1#usize (by rw [hav]; norm_num)
              rw [he4, Result.ok.injEq] at hx
              rw [hx]; simp [hav]
            have he5v : absExpr e5 = ConLeche.Expr.bvar 0 := by
              rw [Expr.bvar_refines he5]; rfl
            have ha1wf : ExprWF a1 := hargswf a1 (by rw [hav]; simp)
            have hb3v : b3 = decide (absExpr e4 = absExpr e5) :=
              Expr.beq_refines (by rw [he4v]; exact ha1wf) (ExprWF.bvar he5) hb3
            rw [he4v, he5v] at hb3v
            by_cases hb3t : b3 = true
            · rw [if_pos hb3t] at h
              rw [hb3t] at hb3v
              rw [of_decide_eq_true hb3v.symm]
              simp only [beq_self_eq_true, Bool.true_and]
              obtain ⟨fam2, hfam2, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v4, hv4, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨slot, hslot, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨e7, he7, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
              have hfam2v : absExpr fam2
                  = ConLeche.Expr.const ((absName t).str "_model")
                      ((absNames lps).map ConLeche.Level.param) := by
                rw [Expr.mk_const_refines hfam2, hnmv, husv]
              have hfam2wf : ExprWF fam2 := ExprWF.mk_const hnmwf huswf hfam2
              obtain ⟨hv4v, hv4wf⟩ := hspines.2.1 n_p v4 hv4
              obtain ⟨hslotv, hslotwf⟩ :=
                ExprOps.mk_app_n_refines hfam2wf hv4wf hslot
              have hstarget : absExpr slot
                  = ConLeche.Expr.mkAppN
                      (.const ((absName t).str "_model")
                        ((absNames lps).map ConLeche.Level.param))
                      ((List.range n_p.val).map
                        (fun k => ConLeche.Expr.bvar (n_p.val - k))) := by
                rw [hslotv, hfam2v, hv4v]
              have he7v : e7 = a0 := by
                have hx := hargidx 0#usize (by rw [hav]; norm_num)
                rw [he7, Result.ok.injEq] at hx
                rw [hx]; simp [hav]
              have ha0wf : ExprWF a0 := hargswf a0 (by rw [hav]; simp)
              have hb4v : b4 = decide (absExpr e7 = absExpr slot) :=
                Expr.beq_refines (by rw [he7v]; exact ha0wf) hslotwf hb4
              rw [he7v, hstarget] at hb4v
              by_cases hb4t : b4 = true
              · rw [if_pos hb4t] at h
                rw [hb4t] at hb4v
                rw [of_decide_eq_true hb4v.symm]
                simp only [beq_self_eq_true, Bool.true_and]
                obtain ⟨e8, he8, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨e9, he9, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨he9v, he9wf⟩ := eta_rhs_refines hspines ht hc hlps he9
                have he8v : e8 = a2 := by
                  have hx := hargidx 2#usize (by rw [hav]; norm_num)
                  rw [he8, Result.ok.injEq] at hx
                  rw [hx]; simp [hav]
                have ha2wf : ExprWF a2 := hargswf a2 (by rw [hav]; simp)
                have hb5v : b5 = decide (absExpr e8 = absExpr e9) :=
                  Expr.beq_refines (by rw [he8v]; exact ha2wf) he9wf hb5
                rw [he8v, he9v] at hb5v
                by_cases hb5t : b5 = true
                · rw [if_pos hb5t] at h
                  rw [hb5t] at hb5v
                  rw [of_decide_eq_true hb5v.symm]
                  simp only [beq_self_eq_true, Bool.true_and]
                  obtain ⟨b6, hb6, h⟩ := bind_eq_ok_iff.mp h
                  have hb6v : b6 = (absMode mode).ttChecks :=
                    Env.tt_checks_refines hb6
                  by_cases hb6t : b6 = true
                  · rw [if_pos hb6t] at h
                    rw [hb6t] at hb6v
                    obtain ⟨la, hla, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨srt, hsrt, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨hlav, hlawf⟩ := hcb.eqHeadLevel head la hheadwf hla
                    rw [hheadc] at hlav
                    have hsrtv : absExpr srt = ConLeche.Expr.sort lA := by
                      rw [Expr.sort_refines hsrt, hlav]; rfl
                    have hsrtwf : ExprWF srt := ExprWF.sort hlawf hsrt
                    rw [Expr.beq_refines htbodywf hsrtwf h, hsrtv, ← hb6v]
                    simp [beq_eq_decide_expr]
                  · simp only [Bool.not_eq_true] at hb6t
                    rw [if_neg (by simp [hb6t]), Result.ok.injEq] at h
                    rw [hb6t] at hb6v
                    rw [← h, ← hb6v]
                    simp
                · simp only [Bool.not_eq_true] at hb5t
                  rw [if_neg (by simp [hb5t]), Result.ok.injEq] at h
                  rw [hb5t] at hb5v
                  rw [← h]
                  have hne : absExpr a2 ≠ _ := of_decide_eq_false hb5v.symm
                  simp [hne]
              · simp only [Bool.not_eq_true] at hb4t
                rw [if_neg (by simp [hb4t]), Result.ok.injEq] at h
                rw [hb4t] at hb4v
                rw [← h]
                have hne : absExpr a0 ≠ _ := of_decide_eq_false hb4v.symm
                simp [hne]
            · simp only [Bool.not_eq_true] at hb3t
              rw [if_neg (by simp [hb3t]), Result.ok.injEq] at h
              rw [hb3t] at hb3v
              rw [← h]
              have hne : absExpr a1 ≠ ConLeche.Expr.bvar 0 :=
                of_decide_eq_false hb3v.symm
              simp [hne]
          · simp only [Bool.not_eq_true] at hb2t
            rw [if_neg (by simp [hb2t]), Result.ok.injEq] at h
            rw [hb2t] at hb2v
            rw [← h]
            split
            · rename_i c lA tS lC rC hpat
              have hfn : (absExpr sbody).getAppFn = .const c [lA] := by
                rw [hpat]; rfl
              rw [hheadv, hfn] at hb2v
              simp only [ConLeche.isEqHead] at hb2v
              simp [← hb2v]
            · rfl
        · rw [if_neg hlen3, Result.ok.injEq] at h
          rw [← h]
          split
          · rename_i c lA tS lC rC hpat
            exfalso
            apply hlen3
            have hga : (absExpr sbody).getAppArgs = [tS, lC, rC] := by
              rw [hpat]; simp [ConLeche.Expr.getAppArgs]
            rw [← hargsv] at hga
            have hx := congrArg List.length hga
            simpa [absExprs] using hx
          · rfl

/-- `ConstantInfo`'s `BEq` is its `decide`; the cited body writes `==` where
`basis_pins::eq_basis_pinned` is stated with `decide`. -/
theorem beq_eq_decide_ci (x y : ConLeche.ConstantInfo) :
    (x == y) = decide (x = y) := by
  rw [Bool.eq_iff_iff]; simp

/-- `checkEtaThmF` re-read through the three owning probes, as `unitThmF_read`
does for `checkUnitThmF`. -/
theorem etaThmF_read (lmode : ConLeche.CheckMode) (lfe : ConLeche.FEnv)
    (t ctorName : ConLeche.Name) (lps : List ConLeche.Name) (n_p n_f : Nat) :
    ConLeche.checkEtaThmF lmode lfe t ctorName lps n_p n_f
      = (match (match lfe.find? ((t.str "_model").str "eta") with
                | some (.thmInfo tcv _) => some tcv
                | _ => none),
               (CoreK.defnOf (lfe.find? (t.str "_model"))).map Prod.fst,
               (CoreK.defnOf
                 (lfe.find? (ctorName.str "_model"))).map Prod.fst with
         | some tcv, some cvmT, some cvmC =>
           decide (lfe.find? ConLeche.eqName = some ConLeche.eqA)
             && (tcv.levelParams == lps) && (cvmT.levelParams == lps)
             && (cvmC.levelParams == lps)
             && (List.range n_f).all (fun j =>
                  match lfe.find? (ConLeche.projModelName t j) with
                  | some (.defnInfo cvmj _ _) => cvmj.levelParams == lps
                  | _ => false)
             && checkEtaThmShape lmode t ctorName lps n_p n_f tcv.type
                  cvmT.type
         | _, _, _ => false) := by
  rw [ConLeche.checkEtaThmF]
  simp only [CoreK.defnOf]
  cases hf1 : lfe.find? ((t.str "_model").str "eta") with
  | none => rfl
  | some ci1 =>
  cases ci1 <;> try rfl
  cases hf2 : lfe.find? (t.str "_model") with
  | none => rfl
  | some ci2 =>
  cases ci2 <;> try rfl
  cases hf3 : lfe.find? (ctorName.str "_model") with
  | none => rfl
  | some ci3 =>
  cases ci3 <;> try rfl
  cases hf4 : lfe.find? ConLeche.eqName with
  | none => rfl
  | some ci4 =>
  simp only [beq_eq_decide_ci, Option.some.injEq]
  rfl

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
  rw [inductives.modeled.check_eta_thm] at h
  obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnmv, hnmwf⟩ := eta_thm_name_refines ht hnm
  obtain ⟨hoabs, howf⟩ := thm_probe_refines hrel hfe hnmwf ho
  rw [hnmv] at hoabs
  rw [etaThmF_read, ← hoabs]
  cases o with
  | none =>
    simp only [Option.map_none, Result.ok.injEq] at h ⊢
    rw [← h]
  | some tcv =>
  have htcvwf : ConstantValWF tcv := howf tcv rfl
  obtain ⟨nm1, hnm1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnm1v, hnm1wf⟩ := model_of_refines ht hnm1
  obtain ⟨ho1abs, ho1wf⟩ :=
    CoreK.defn_probe_refines (FindAgree.of_rel hrel hfe) (FindWF.of_wf hfe)
      hnm1wf ho1
  rw [hnm1v] at ho1abs
  rw [← ho1abs]
  cases o1 with
  | none =>
    simp only [Option.map_none, Option.map_some, Result.ok.injEq] at h ⊢
    rw [← h]
  | some dt =>
  obtain ⟨cvm, mv, mhint⟩ := dt
  have hcvmwf : ConstantValWF cvm := (ho1wf cvm mv mhint rfl).1
  obtain ⟨nm2, hnm2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnm2v, hnm2wf⟩ := model_of_refines hc hnm2
  obtain ⟨ho2abs, ho2wf⟩ :=
    CoreK.defn_probe_refines (FindAgree.of_rel hrel hfe) (FindWF.of_wf hfe)
      hnm2wf ho2
  rw [hnm2v] at ho2abs
  rw [← ho2abs]
  cases o2 with
  | none =>
    simp only [Option.map_none, Option.map_some, Result.ok.injEq] at h ⊢
    rw [← h]
  | some dc =>
  obtain ⟨cvc, cv2, chint⟩ := dc
  have hcvcwf : ConstantValWF cvc := (ho2wf cvc cv2 chint rfl).1
  simp only [Option.map_some]
  simp at h
  rcases h with ⟨hbp, rfl⟩ | ⟨hbp, h⟩
  · have hbpv := BasisPins.eq_basis_pinned_refines hrel hfe hbp
    have hne : lfe.find? ConLeche.eqName ≠ some ConLeche.eqA :=
      of_decide_eq_false hbpv.symm
    simp [hne]
  · have hbpv := BasisPins.eq_basis_pinned_refines hrel hfe hbp
    have heqp : lfe.find? ConLeche.eqName = some ConLeche.eqA :=
      of_decide_eq_true hbpv.symm
    rcases h with ⟨hb1, rfl⟩ | ⟨hb1, h⟩
    · have hb1v : (false : Bool)
          = decide (absNames tcv.level_params = absNames lps) :=
        Env.names_beq_refines htcvwf.2.1 hlps hb1
      have hb1ne : absNames tcv.level_params ≠ absNames lps :=
        of_decide_eq_false hb1v.symm
      simp [heqp, absConstantVal, hb1ne]
    · have hb1v : (true : Bool)
          = decide (absNames tcv.level_params = absNames lps) :=
        Env.names_beq_refines htcvwf.2.1 hlps hb1
      have hb1eq : absNames tcv.level_params = absNames lps :=
        of_decide_eq_true hb1v.symm
      rcases h with ⟨hb2, rfl⟩ | ⟨hb2, h⟩
      · have hb2v : (false : Bool)
            = decide (absNames cvm.level_params = absNames lps) :=
          Env.names_beq_refines hcvmwf.2.1 hlps hb2
        have hb2ne : absNames cvm.level_params ≠ absNames lps :=
          of_decide_eq_false hb2v.symm
        simp [heqp, absConstantVal, hb1eq, hb2ne]
      · have hb2v : (true : Bool)
            = decide (absNames cvm.level_params = absNames lps) :=
          Env.names_beq_refines hcvmwf.2.1 hlps hb2
        have hb2eq : absNames cvm.level_params = absNames lps :=
          of_decide_eq_true hb2v.symm
        rcases h with ⟨hb3, rfl⟩ | ⟨hb3, h⟩
        · have hb3v : (false : Bool)
              = decide (absNames cvc.level_params = absNames lps) :=
            Env.names_beq_refines hcvcwf.2.1 hlps hb3
          have hb3ne : absNames cvc.level_params ≠ absNames lps :=
            of_decide_eq_false hb3v.symm
          simp [heqp, absConstantVal, hb1eq, hb2eq, hb3ne]
        · have hb3v : (true : Bool)
              = decide (absNames cvc.level_params = absNames lps) :=
            Env.names_beq_refines hcvcwf.2.1 hlps hb3
          have hb3eq : absNames cvc.level_params = absNames lps :=
            of_decide_eq_true hb3v.symm
          rcases h with ⟨hb4, rfl⟩ | ⟨hb4, h⟩
          · have hb4v := proj_models_at_lps_from_refines hrel hfe ht hlps hb4
            rw [show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero,
              ← List.range_eq_range'] at hb4v
            simp [heqp, absConstantVal, hb1eq, hb2eq, hb3eq, ← hb4v]
          · have hb4v := proj_models_at_lps_from_refines hrel hfe ht hlps hb4
            rw [show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero,
              ← List.range_eq_range'] at hb4v
            rw [check_eta_thm_shape_refines hcb hspines ht hc hlps htcvwf.2.2
              hcvmwf.2.2 h]
            simp [heqp, absConstantVal, hb1eq, hb2eq, hb3eq, ← hb4v]

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
  rw [inductives.modeled.check_unit_thm_shape] at h
  rw [checkUnitThmShape]
  obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
  have hkv : k.val = n_p.val + 2 := HashMap.uscalar_add_eq hk
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines htty ho
  rw [hkv] at hoabs
  rw [← hoabs]
  cases o with
  | none => simp only [Option.map_none]; simp at h; simp [← h]
  | some sq =>
  obtain ⟨sbs, sbody⟩ := sq
  obtain ⟨hsbswf, hsbodywf⟩ := howf _ rfl
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_pis_refines httym ho1
  rw [← ho1abs]
  cases o1 with
  | none => simp only [Option.map_none, Option.map_some]; simp at h; simp [← h]
  | some mq =>
  obtain ⟨tbs, tbody⟩ := mq
  obtain ⟨htbswf, htbodywf⟩ := ho1wf _ rfl
  simp only [Option.map_some]
  simp at h
  have hz : ((0#u64 : Std.U64)).val = 0 := rfl
  rcases h with ⟨hbd, rfl⟩ | ⟨hbd, h⟩
  · have hbdv := hcb.domsMatchAux _ () (fun _ e => e) dom_ident_view_gl sbs tbs
      0#u64 0#u64 n_p false hsbswf htbswf hbd
    rw [hz] at hbdv
    rw [← hbdv]
    simp
  · have hbdv := hcb.domsMatchAux _ () (fun _ e => e) dom_ident_view_gl sbs tbs
      0#u64 0#u64 n_p true hsbswf htbswf hbd
    rw [hz] at hbdv
    have hEq_inv : ∀ (e : ConLeche.Expr), ConLeche.isEqHead e = true →
        ∃ c lA, e = .const c [lA] := by
      intro e he
      cases e with
      | const c us =>
        cases us with
        | nil => simp [ConLeche.isEqHead] at he
        | cons l ls =>
          cases ls with
          | nil => exact ⟨c, l, rfl⟩
          | cons _ _ => simp [ConLeche.isEqHead] at he
      | _ => simp [ConLeche.isEqHead] at he
    obtain ⟨nm, hnm, us, hus, fam, hfam, v3, hv3, xdom, hxdom, v4, hv4,
      ydom, hydom, o2, ho2, h⟩ := h
    obtain ⟨hnmv, hnmwf⟩ := model_of_refines ht hnm
    obtain ⟨husv, huswf⟩ := hspines.1 lps us hlps hus
    have hfamv : absExpr fam
        = ConLeche.Expr.const ((absName t).str "_model")
            ((absNames lps).map ConLeche.Level.param) := by
      rw [Expr.mk_const_refines hfam, hnmv, husv]
    have hfamwf : ExprWF fam := ExprWF.mk_const hnmwf huswf hfam
    obtain ⟨hv3v, hv3wf⟩ := hspines.2.2.2 0#u64 n_p v3 hv3
    obtain ⟨hxdomv, hxdomwf⟩ := ExprOps.mk_app_n_refines hfamwf hv3wf hxdom
    obtain ⟨hv4v, hv4wf⟩ := hspines.2.1 n_p v4 hv4
    obtain ⟨hydomv, hydomwf⟩ := ExprOps.mk_app_n_refines hfamwf hv4wf hydom
    have hxtarget : absExpr xdom
        = ConLeche.Expr.mkAppN
            (.const ((absName t).str "_model")
              ((absNames lps).map ConLeche.Level.param))
            ((List.range n_p.val).map
              (fun k => ConLeche.Expr.bvar (n_p.val - 1 - k))) := by
      rw [hxdomv, hfamv, hv3v, ConLeche.structPsAt]
      simp
    have hytarget : absExpr ydom
        = ConLeche.Expr.mkAppN
            (.const ((absName t).str "_model")
              ((absNames lps).map ConLeche.Level.param))
            ((List.range n_p.val).map
              (fun k => ConLeche.Expr.bvar (n_p.val - k))) := by
      rw [hydomv, hfamv, hv4v]
    obtain ⟨ho2none, ho2some⟩ := dom_at_n_refines hsbswf ho2
    rw [← hbdv]
    cases o2 with
    | none =>
      rw [ho2none rfl]
      simp at h
      subst h
      simp
    | some e3 =>
      obtain ⟨⟨bm3, he3idx⟩, he3wf⟩ := ho2some e3 rfl
      simp at h
      obtain ⟨y2, hy2, o3, ho3, h⟩ := h
      have hy2v : y2.val = n_p.val + 1 := HashMap.uscalar_add_eq hy2
      obtain ⟨ho3none, ho3some⟩ := dom_at_n_refines hsbswf ho3
      rw [hy2v] at ho3none ho3some
      rw [he3idx]
      cases o3 with
      | none =>
        rw [ho3none rfl]
        simp at h
        subst h
        simp
      | some e4 =>
        obtain ⟨⟨bm4, he4idx⟩, he4wf⟩ := ho3some e4 rfl
        simp at h
        rw [he4idx]
        rcases h with ⟨hb1, rfl⟩ | ⟨hb1, h⟩
        · have hb1v : (false : Bool) = decide (absExpr e3 = absExpr xdom) :=
            Expr.beq_refines he3wf hxdomwf hb1
          have hne : absExpr e3 ≠ absExpr xdom := of_decide_eq_false hb1v.symm
          rw [hxtarget] at hne
          simp [hne]
        · have hb1v : (true : Bool) = decide (absExpr e3 = absExpr xdom) :=
            Expr.beq_refines he3wf hxdomwf hb1
          have heq1 : absExpr e3 = absExpr xdom := of_decide_eq_true hb1v.symm
          rw [hxtarget] at heq1
          rw [heq1]
          rcases h with ⟨hb2, rfl⟩ | ⟨hb2, head, hhead, args, hargs, h⟩
          · have hb2v : (false : Bool) = decide (absExpr e4 = absExpr ydom) :=
              Expr.beq_refines he4wf hydomwf hb2
            have hne : absExpr e4 ≠ absExpr ydom := of_decide_eq_false hb2v.symm
            rw [hytarget] at hne
            simp [hne]
          · have hb2v : (true : Bool) = decide (absExpr e4 = absExpr ydom) :=
              Expr.beq_refines he4wf hydomwf hb2
            have heq2 : absExpr e4 = absExpr ydom := of_decide_eq_true hb2v.symm
            rw [hytarget] at heq2
            rw [heq2]
            simp only [beq_self_eq_true, Bool.true_and, Bool.and_true]
            obtain ⟨hheadv, hheadwf⟩ := ExprOps.get_app_fn_refines hsbodywf hhead
            obtain ⟨hargsv, hargswf⟩ :=
              ExprOps.get_app_args_refines hsbodywf hargs
            by_cases hlen3 : args.val.length = 3
            · rw [if_pos hlen3] at h
              obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
              have hb3v : b3 = ConLeche.isEqHead (absExpr head) :=
                hcb.isEqHead head b3 hheadwf hb3
              by_cases hb3t : b3 = true
              · rw [if_pos hb3t] at h
                rw [hb3t] at hb3v
                obtain ⟨c, lA, hheadc⟩ := hEq_inv _ hb3v.symm
                obtain ⟨a0, a1, a2, hav⟩ :
                    ∃ a0 a1 a2, args.val = [a0, a1, a2] := by
                  rcases hl : args.val with _ | ⟨a0, l1⟩
                  · rw [hl] at hlen3; simp at hlen3
                  rcases l1 with _ | ⟨a1, l2⟩
                  · rw [hl] at hlen3; simp at hlen3
                  rcases l2 with _ | ⟨a2, l3⟩
                  · rw [hl] at hlen3; simp at hlen3
                  rcases l3 with _ | ⟨a3, l4⟩
                  · exact ⟨a0, a1, a2, rfl⟩
                  · rw [hl] at hlen3; simp at hlen3
                have hargidx : ∀ (j : Std.Usize) (hj : j.val < args.val.length),
                    alloc.vec.Vec.index_usize args j
                      = ok (args.val[j.val]'hj) := by
                  intro j hj
                  obtain ⟨y0, hy0, hy0v⟩ :=
                    WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec args j hj)
                  subst hy0v
                  exact hy0
                have hawf : ∀ x ∈ args.val, ExprWF x := hargswf
                have hspine : absExpr sbody
                    = .app (.app (.app (.const c [lA]) (absExpr a0))
                        (absExpr a1)) (absExpr a2) := by
                  refine expr_app3_of_spine ?_ ?_
                  · rw [← hheadv, hheadc]
                  · rw [← hargsv, absExprs, hav]; rfl
                rw [hspine]
                simp only []
                obtain ⟨e5, he5, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨e6, he6, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
                have he5v : e5 = a1 := by
                  have := hargidx 1#usize (by rw [hav]; norm_num)
                  rw [he5, Result.ok.injEq] at this
                  rw [this]
                  simp [hav]
                have he6v : absExpr e6 = ConLeche.Expr.bvar 1 := by
                  rw [Expr.bvar_refines he6]; rfl
                have ha1wf : ExprWF a1 := hawf a1 (by rw [hav]; simp)
                have he6wf : ExprWF e6 := ExprWF.bvar he6
                have hb4v : b4 = decide (absExpr e5 = absExpr e6) :=
                  Expr.beq_refines (by rw [he5v]; exact ha1wf) he6wf hb4
                rw [he5v, he6v] at hb4v
                have hceq : (c == ConLeche.eqName) = true := by
                  have := hb3v.symm
                  rw [hheadc] at this
                  simpa [ConLeche.isEqHead] using this
                rw [hceq]
                by_cases hb4t : b4 = true
                · rw [if_pos hb4t] at h
                  rw [hb4t] at hb4v
                  rw [of_decide_eq_true hb4v.symm]
                  obtain ⟨e7, he7, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨e8, he8, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
                  have he7v : e7 = a2 := by
                    have := hargidx 2#usize (by rw [hav]; norm_num)
                    rw [he7, Result.ok.injEq] at this
                    rw [this]
                    simp [hav]
                  have he8v : absExpr e8 = ConLeche.Expr.bvar 0 := by
                    rw [Expr.bvar_refines he8]; rfl
                  have ha2wf : ExprWF a2 := hawf a2 (by rw [hav]; simp)
                  have hb5v : b5 = decide (absExpr e7 = absExpr e8) :=
                    Expr.beq_refines (by rw [he7v]; exact ha2wf)
                      (ExprWF.bvar he8) hb5
                  rw [he7v, he8v] at hb5v
                  by_cases hb5t : b5 = true
                  · rw [if_pos hb5t] at h
                    rw [hb5t] at hb5v
                    rw [of_decide_eq_true hb5v.symm]
                    simp only [beq_self_eq_true, Bool.true_and]
                    obtain ⟨v5, hv5, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨slot, hslot, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨e9, he9, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨b6, hb6, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨hv5v, hv5wf⟩ := hspines.2.2.2 2#u64 n_p v5 hv5
                    obtain ⟨hslotv, hslotwf⟩ :=
                      ExprOps.mk_app_n_refines hfamwf hv5wf hslot
                    have hstarget : absExpr slot
                        = ConLeche.Expr.mkAppN
                            (.const ((absName t).str "_model")
                              ((absNames lps).map ConLeche.Level.param))
                            ((List.range n_p.val).map
                              (fun k => ConLeche.Expr.bvar
                                (n_p.val + 1 - k))) := by
                      rw [hslotv, hfamv, hv5v, ConLeche.structPsAt]
                      have : ∀ k, (2#u64 : Std.U64).val + n_p.val - 1 - k
                          = n_p.val + 1 - k := by intro k; simp; omega
                      simp only [this]
                    have he9v : e9 = a0 := by
                      have := hargidx 0#usize (by rw [hav]; norm_num)
                      rw [he9, Result.ok.injEq] at this
                      rw [this]
                      simp [hav]
                    have ha0wf : ExprWF a0 := hawf a0 (by rw [hav]; simp)
                    have hb6v : b6 = decide (absExpr e9 = absExpr slot) :=
                      Expr.beq_refines (by rw [he9v]; exact ha0wf) hslotwf hb6
                    rw [he9v, hstarget] at hb6v
                    by_cases hb6t : b6 = true
                    · rw [if_pos hb6t] at h
                      rw [hb6t] at hb6v
                      rw [of_decide_eq_true hb6v.symm]
                      simp only [beq_self_eq_true, Bool.true_and]
                      obtain ⟨b7, hb7, h⟩ := bind_eq_ok_iff.mp h
                      have hb7v : b7 = (absMode mode).ttChecks :=
                        Env.tt_checks_refines hb7
                      by_cases hb7t : b7 = true
                      · rw [if_pos hb7t] at h
                        rw [hb7t] at hb7v
                        obtain ⟨la, hla, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨srt, hsrt, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨hlav, hlawf⟩ :=
                          hcb.eqHeadLevel head la hheadwf hla
                        rw [hheadc] at hlav
                        have hsrtv : absExpr srt
                            = ConLeche.Expr.sort lA := by
                          rw [Expr.sort_refines hsrt, hlav]; rfl
                        have hsrtwf : ExprWF srt := ExprWF.sort hlawf hsrt
                        rw [Expr.beq_refines htbodywf hsrtwf h, hsrtv, ← hb7v]
                        simp [beq_eq_decide_expr]
                      · simp only [Bool.not_eq_true] at hb7t
                        rw [if_neg (by simp [hb7t]), Result.ok.injEq] at h
                        rw [hb7t] at hb7v
                        rw [← h, ← hb7v]
                        simp
                    · simp only [Bool.not_eq_true] at hb6t
                      rw [if_neg (by simp [hb6t]), Result.ok.injEq] at h
                      rw [hb6t] at hb6v
                      rw [← h]
                      have : absExpr a0 ≠ _ := of_decide_eq_false hb6v.symm
                      simp [this]
                  · simp only [Bool.not_eq_true] at hb5t
                    rw [if_neg (by simp [hb5t]), Result.ok.injEq] at h
                    rw [hb5t] at hb5v
                    rw [← h]
                    have : absExpr a2 ≠ ConLeche.Expr.bvar 0 :=
                      of_decide_eq_false hb5v.symm
                    simp [this]
                · simp only [Bool.not_eq_true] at hb4t
                  rw [if_neg (by simp [hb4t]), Result.ok.injEq] at h
                  rw [hb4t] at hb4v
                  rw [← h]
                  have : absExpr a1 ≠ ConLeche.Expr.bvar 1 :=
                    of_decide_eq_false hb4v.symm
                  simp [this]
              · simp only [Bool.not_eq_true] at hb3t
                rw [if_neg (by simp [hb3t]), Result.ok.injEq] at h
                rw [hb3t] at hb3v
                rw [← h]
                split
                · rename_i c lA tS lC rC hpat
                  have hfn : (absExpr sbody).getAppFn = .const c [lA] := by
                    rw [hpat]; rfl
                  rw [hheadv, hfn] at hb3v
                  simp only [ConLeche.isEqHead] at hb3v
                  simp [← hb3v]
                · rfl
            · rw [if_neg hlen3, Result.ok.injEq] at h
              rw [← h]
              split
              · rename_i c lA tS lC rC hpat
                exfalso
                apply hlen3
                have hga : (absExpr sbody).getAppArgs = [tS, lC, rC] := by
                  rw [hpat]; simp [ConLeche.Expr.getAppArgs]
                rw [← hargsv] at hga
                have := congrArg List.length hga
                simpa [absExprs] using this
              · rfl


/-- `checkUnitThmF` re-read through the two owning probes the port uses: the
`.thmInfo` match `thm_probe` answers, `CoreK.defnOf`'s `.defnInfo` match, and
the `Eq` pin as `basis_pins::eq_basis_pinned`'s `decide`.  The cited three-way
match and this two-way one agree on every index: a missing `eqName` makes both
`false`. -/
theorem unitThmF_read (lmode : ConLeche.CheckMode) (lfe : ConLeche.FEnv)
    (t : ConLeche.Name) (lps : List ConLeche.Name) (n_p : Nat) :
    ConLeche.checkUnitThmF lmode lfe t lps n_p
      = (match (match lfe.find? ((t.str "_model").str "unitlike") with
                | some (.thmInfo tcv _) => some tcv
                | _ => none),
               (CoreK.defnOf (lfe.find? (t.str "_model"))).map Prod.fst with
         | some tcv, some cvmT =>
           decide (lfe.find? ConLeche.eqName = some ConLeche.eqA)
             && (tcv.levelParams == lps) && (cvmT.levelParams == lps)
             && checkUnitThmShape lmode t lps n_p tcv.type cvmT.type
         | _, _ => false) := by
  rw [ConLeche.checkUnitThmF]
  rcases hf1 : lfe.find? ((t.str "_model").str "unitlike") with _ | ci1 <;>
    rcases hf2 : lfe.find? (t.str "_model") with _ | ci2 <;>
    rcases hf3 : lfe.find? ConLeche.eqName with _ | ci3 <;>
    simp only [CoreK.defnOf] <;>
    first
      | rfl
      | (cases ci1 <;> cases ci2 <;>
          (try simp only [beq_eq_decide_ci, Option.some.injEq]) <;> rfl)
      | (cases ci1 <;> rfl)

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
  rw [inductives.modeled.check_unit_thm] at h
  obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnmv, hnmwf⟩ := unit_thm_name_refines ht hnm
  obtain ⟨hoabs, howf⟩ := thm_probe_refines hrel hfe hnmwf ho
  rw [hnmv] at hoabs
  rw [unitThmF_read, ← hoabs]
  cases o with
  | none =>
    simp only [Option.map_none, Result.ok.injEq] at h ⊢
    rw [← h]
  | some tcv =>
  have htcvwf : ConstantValWF tcv := howf tcv rfl
  obtain ⟨nm1, hnm1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnm1v, hnm1wf⟩ := model_of_refines ht hnm1
  obtain ⟨ho1abs, ho1wf⟩ :=
    CoreK.defn_probe_refines (FindAgree.of_rel hrel hfe) (FindWF.of_wf hfe)
      hnm1wf ho1
  rw [hnm1v] at ho1abs
  rw [← ho1abs]
  cases o1 with
  | none =>
    simp only [Option.map_none, Option.map_some, Result.ok.injEq] at h ⊢
    rw [← h]
  | some dt =>
  obtain ⟨cvm, mv, mhint⟩ := dt
  have hcvmwf : ConstantValWF cvm := (ho1wf cvm mv mhint rfl).1
  simp only [Option.map_some]
  simp at h
  rcases h with ⟨hbp, rfl⟩ | ⟨hbp, h⟩
  · have hbpv := BasisPins.eq_basis_pinned_refines hrel hfe hbp
    have hne : lfe.find? ConLeche.eqName ≠ some ConLeche.eqA :=
      of_decide_eq_false hbpv.symm
    simp [hne]
  · have hbpv := BasisPins.eq_basis_pinned_refines hrel hfe hbp
    have heqp : lfe.find? ConLeche.eqName = some ConLeche.eqA :=
      of_decide_eq_true hbpv.symm
    rcases h with ⟨hb1, rfl⟩ | ⟨hb1, h⟩
    · have hb1v : (false : Bool)
          = decide (absNames tcv.level_params = absNames lps) :=
        Env.names_beq_refines htcvwf.2.1 hlps hb1
      have hb1ne : absNames tcv.level_params ≠ absNames lps :=
        of_decide_eq_false hb1v.symm
      simp [heqp, absConstantVal, hb1ne]
    · have hb1v : (true : Bool)
          = decide (absNames tcv.level_params = absNames lps) :=
        Env.names_beq_refines htcvwf.2.1 hlps hb1
      have hb1eq : absNames tcv.level_params = absNames lps :=
        of_decide_eq_true hb1v.symm
      rcases h with ⟨hb2, rfl⟩ | ⟨hb2, h⟩
      · have hb2v : (false : Bool)
            = decide (absNames cvm.level_params = absNames lps) :=
          Env.names_beq_refines hcvmwf.2.1 hlps hb2
        have hb2ne : absNames cvm.level_params ≠ absNames lps :=
          of_decide_eq_false hb2v.symm
        simp [heqp, absConstantVal, hb1eq, hb2ne]
      · have hb2v : (true : Bool)
            = decide (absNames cvm.level_params = absNames lps) :=
          Env.names_beq_refines hcvmwf.2.1 hlps hb2
        have hb2eq : absNames cvm.level_params = absNames lps :=
          of_decide_eq_true hb2v.symm
        rw [check_unit_thm_shape_refines hcb hspines ht hlps htcvwf.2.2
          hcvmwf.2.2 h]
        simp [heqp, absConstantVal, hb1eq, hb2eq]


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
      rw [check_eta_thm_refines hcb hspines hrel hfe hct.1 hcc.1 hct.2.1
          heta,
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
