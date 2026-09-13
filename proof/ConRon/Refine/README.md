# `ConRon.Refine` — naming rule for the refinement tier

This directory holds the refinement lemmas of DESIGN.md §3.5 / plan phase P3,
stated about the *generated* model of `crates/con-ron-core` rather than about
the task-#3 spike.  `ConRon/Spike/LevelName/` stays where it is: it is task
#3/#5's recorded evidence and is never moved or edited.

## The rule

| thing | where it lives | how it is named |
|---|---|---|
| a ported Rust function `<module>::<fn>` | generated, `ConRon/Generated/Funs.lean` | `ConRon.Generated.<dir>.<module>.<fn>` |
| a ported Rust type `<module>::<Type>` | generated, `ConRon/Generated/Types.lean` | `ConRon.Generated.<module>.<Type>` |
| its refinement lemma | `ConRon/Refine/<Module>.lean` | `ConRon.Refine.<Module>.<fn>_refines` |
| the abstraction function for `<module>::<Type>` | `ConRon/Refine/Abs.lean` (P3) | `abs<Type>` |
| the well-formedness predicate for `<module>::<Type>` | `ConRon/Refine/Abs.lean` (P3) | `<Type>WF` |

`<Module>` is the Rust module name in `UpperCamelCase` (`level` → `Level`,
`prop_when` → `PropWhen`), so `ConRon.Generated.kernel.level.simplify` is refined by
`ConRon.Refine.Level.simplify_refines` in `ConRon/Refine/Level.lean`.  Helper
lemmas that are not *the* refinement of a function keep a descriptive name
(`level_zero_inv`, `str_eq_refl`, …), exactly as in the spike.

Both halves of the name come from `scripts/extract.sh`'s flags and are stable:
`-namespace ConRon.Generated` puts every generated definition in
`ConRon.Generated`, and Aeneas keeps the Rust module path as the prefix of the
definition name (`level.zero`, not `Level.zero`).  A generated name therefore
never collides with a hand-written one.

## The spike's conventions port unchanged

`ConRon/Spike/LevelName/Refine.lean` fixed three conventions (task #5); each
carries over to `ConRon.Generated` by renaming `level_name.` to
`ConRon.Generated.` and nothing else:

* **exact-result refinement on success** — `rust_f x = ok y →
  lean_f (abs x) = abs y` (since task #67 this is the `.Ok` half of the
  full-outcome statement below, and the failure half is no longer empty);
* **`NameWF` / `LevelWF` / `NodeWF` as inductive predicates whose
  constructors are the port's own smart constructors**, which is what pins the
  stored hash word and makes `abs` injective and `beq` exact;
* **`ptr_eq` is `false` in the model**, with `*_beq_refl` reflexivity lemmas
  standing in for the real program's fast path.

The types the predicates are written over are *definitionally the same shape*
in both places (`Name.mk : Arc NameNode → Name`, `NameNode.mk : U64 →
NameKind → NameNode`, the five `LevelKind` constructors), and both sit on the
same hand-written pointer model, so the statements and the proof scripts transfer
verbatim -- `Name.lean` and `Level.lean` are the spike's `Refine.lean` with
`level_name.` dropped and the four `Name` helpers qualified, and nothing
else.  (Task #12's two-lemma `Smoke.lean` was folded into `Level.lean`'s
`zero_refines` / `succ_refines` at task #17 and deleted.)

## The full-outcome convention (task #67, DESIGN.md §3's ruling of 2026-09-13)

Every refinement lemma is stated over the Rust computation's **whole**
outcome, not only its successes.  A Rust function in the checker returns
`Result (core.result.Result α CheckError × CState)`: the outer `Result` is
Aeneas's failure monad (a panic, an overflow, a failed index — *nothing* is
ever claimed about it, since every lemma's hypothesis is `f … = ok …`), and
the inner one is con-leche's `Except`.  The inner outcome is claimed exactly:

| Rust outcome | what the lemma claims about con-leche |
|---|---|
| `.Ok r` | `.ok` at `abs r`, states related, `StateWF`/`WF r` |
| `.Err (.NotImplemented _ \| .Invalid _ \| .Internal _)` | `.error` **at the same kind** — messages are never compared |
| `.Err (.Native _)` | nothing |
| Aeneas `fail`/`div` | nothing |

The vocabulary is in `Abs.lean` and `State.lean`:

* `ErrKind` — con-leche's three constructors without their messages;
  `lErrKind : ConLeche.CheckError → ErrKind`.
* `absErrKind : CheckError → Option ErrKind` — the port's error as the kind it
  stands for, `none` for the port's own `Native`.
* `ErrSim e x : Prop` — *"if the port's error has a kind, con-leche's
  `Except` `x` throws at that kind"*.  `Native` makes it vacuous, which is how
  "claims nothing" is spelled without a second definition.
* `OutP A WF o x` (pure tier, `Abs.lean`) and `Out A WF o st' x`
  (cached tier, `State.lean`) — the two halves as one `match`.
* `Core/Statements.lean`'s `RefinesE`/`RefinesB` and `Core/Arms/Shape.lean`'s
  `Sim`/`SimS` are stated with `Out`.

**Using a lemma is unchanged.**  `SimS.apply`, `Sim.apply`, `RefinesE.ok` and
`RefinesB.ok` have exactly the pre-#67 statements, so a call site that knows
its callee succeeded reads as it did.  What is new is `SimS.apply_err`,
`Sim.apply_err`, `RefinesE.err`, `RefinesB.err`.

**Proving a lemma** adds the error half of each case.  Three moves cover
almost all of it:

1. *a bind whose sub-computation threw* — `…apply_err` gives
   `ErrSim e (sub.run lst)`, and `ErrSim.bind` (or `Out.bind`) carries it
   through the rest of con-leche's `do` block.  One line per bind.
2. *an explicit `throw` arm* — the guard has already been shown to agree in
   the accept direction, so rewrite the con-leche side down to its `throw` and
   close with `ErrSim.invalid` / `.internal` / `.notImplemented`.
3. *a `Native` arm* — `ErrSim.native` (or `ErrSim.of_none`) closes it without
   naming the con-leche side at all.

`SimS.mk'` / `Sim.mk''` split a proof into its two halves where they do not
share a case analysis; where they do (the usual case), intro the outcome `o`
and case on it inside the existing structure.

**A strengthening that turns out false is a port bug.**  The accept direction
could not see a Rust guard that throws where con-leche does not, or that
throws a *different kind*; the full-outcome statement can.  Fix the Rust (as
tasks #58/#61 did) and record it in DESIGN.md — do not weaken the statement.
The port's own failures are exactly the `Native` sites of the census in
DESIGN.md's task #67 section, and adding a new one is a deliberate,
documented accept-direction deviation, not a way out of a proof.

## What is here (tasks #17, #20 and #47, P3.3)
## What is here (tasks #17, #20, #22 and #46)

| file | contents |
|---|---|
| `Abs.lean` | the plumbing `simp` set, `absString`/`absName`/`absLevel`/`absNames`/`absLevels`/`absOrdering`/`absPropWhen`/`absLiteral`/`absBinderMeta`/`absExpr`, the `*_inv` smart-constructor shapes, `StrWF`/`NameWF`/`LevelWF`/`NamesWF`/`PropWhenWF`/`LevelsWF`/`LiteralWF`/`BinderMetaWF`/`ExprWF`, and `Level.ind'`/`Name.ind'` |
| `Name.lean` | `absString`/`absName` injectivity, `str_eq`, `beq`, `contains`, `singleton` |
| `Level.lean` | the task-#5 development: `absLevel` injectivity, `beq`, `level_has_param`, `subst`, `is_never_zero`, `simplify`, and the `leq_core`/`rest`/`imax_rules`/`by_cases`/`leq`/`is_equiv` cascade |
| `PropWhen.lean` | `name_cmp` (through `str_compare`/`nat_compare`/`ord_then`), `merge`/`canon`, the smart constructors, `to_list`/`to_list_opt`, `is_never`/`has_params`/`holds`/`params_defined`, `inter`, `bind_z`, `beq`, and (task #20) `absPropWhen`'s injectivity and `beq`'s reflexivity |
| `Nat.lean` | `ron::nat` (task #15), plus (task #20) `cmp`/`beq` reflexivity |
| `HashMap.lean` | `ron::hashmap` (task #16) |
| `Expr.lean` | `kernel::expr` (task #20): the packed word (`pack_bits`, the `*_val` readings, `wf_data`), the ten smart constructors, the three exact accessors, `beq_recursive`, `levels_beq`, the copies, `absExpr`'s injectivity, and `beq`'s reflexivity and exactness |
| `ExprOps.lean` | `kernel::expr_ops`'s **foundation** (tasks #21/#47): the memo facts (`get_mem`, `insert_pres`, `MemoInv` and its `empty`/`hit`/`set`), the two key types and their `KeyExact`, the four owning probes, the shared `Vec`/scalar plumbing and `Vec` copies, and `instantiate1` |
| `ExprOpsFields.lean` | the derived fields: `size_b`/`size_f`, `wscoped_b`, the `bvar_bound`/`fvar_range` spec walks and their memoized twins, the exact accessors `bvar_b`/`fvar_b`, `loose_bvars_bounded`, `has_fvar`, `abstract_range` and `lift_loose_bvars` |
| `ExprOpsSubst.lean` | the substitutions: `instantiate_list` (spec, memoized walk and `*_fast`), `take_exprs`, `abstract1`, `lower_bvars`, `instantiate1_lift` and `inst_pis_at_lift` |
| `ExprOpsSpine.lean` | the spine and the telescopes: `get_app_fn`/`get_app_args`/`mk_app_n`, `pi_result`/`pi_arity`/`result_sort`/`fvar_type_d`, `strip_pis`/`strip_lams`, the `inst_pis_at`/`inst_lams_at`/`inst_spine` cascade and its one-pass `*_f` twins, `rec_rule_plain`, `pis_to_lams`, `replace_pi_body` |
| `ExprOpsMeta.lean` | the metadata: `reset_meta`, `rename_consts`, the `level::zeroness_of`/`level::subst_pw` bridge, `levels_subst`/`instantiate_level_params`, the leaf readers (`is_lam`, `lam_pw`, `forall_pw`, `has_level_param`, `expr_ptr_beq`), `fvar_leaves`, and the `all_level_params_defined` family |

| `BasisTables.lean` | `kernel::basis_tables` (task #22): the generated basis tables are the value they were generated from |
| `HashMapWF.lean` | task #16's deferred `Eq2` generalisation, written for its first client (task #46): the bucket walks and the `Std.HashMap` bridge under a *forward*, key-restricted exactness hypothesis (`Eq2Fwd`) instead of `Eq2Spec` |
| `Env.lean` | `kernel::env` (task #46): the mode accessors, the `Vec` copies and the `*_dup` identities, `rec_rule_parsed`/`ind_caps_default`/`default_expr` (the Lean's field defaults), `proj_table_entry`, `pi_sort_tele_len`, `ind_params_ok`, the reserved names `proj_fn_name`/`proj_table_name`, `abs`'s injectivity on the well-formed records, the whole `*_beq` family exactly, the accessors, and `find`/`find_proj` |
| `FEnv.lean` | `kernel::fenv` (task #46, completed by #50): `FEnvRel`/`FEnvWF`, `mk_fenv_go`/`mk_fenv`, `find`/`find_proj`, `restrict_to`, `dup`, and `push` — `push_refines` was task #46's one `sorry` because the Aeneas model of `Vec::insert` is `List.set`; task #50 removed that call from the port (`Env.consts` is stored reversed) and proved it |
| `State.lean` | `cached::state_c` (task #46): `StateRel`/`StateWF` over the fourteen memo maps (task #61 added `StateRel.instCSize`, the `instC` entry count, and `insert_size_step`), the fresh state, `flushed`, and the memo probe/insert lemmas |
| `StateC.lean` | `cached::state_c`'s **operations** (task #52, CORE_PLAN step 5): the pure `*M` wrappers, the three level memos (`simplify_l_m`, `is_non_zero_l_m`, `is_equiv_l_m`, `is_equiv_list_l_m`), `inst_list_m` with the `instC` entry cap and `InstCSize`, the two `ienv` pointer-identity sites (`stored_ty_idx_m`/`stored_val_idx_m`), the three level-instantiated readers and their `fe.find?` probes, `subst_level_trees`, `flush_c` and `record_c_const` |
| `StateCResolve.lean` | `cached::state_c::consts_resolve_fc` (task #52): the memoized `ExprC` DAG walk of the parsed-index driver, over the call-local memo relation `MemoBOk` |
| `ExprOpsC.lean` | `cached::expr_ops_c`'s **foundation** (task #51): the module note for all four `ExprOpsC*` files, the `O(1)` field reads (`has_fvar`, `loose_bvars_bounded`), the spine readers, `rev_append_exprs`, the two extra memo probes and `leaf_mem` |
| `ExprOpsCSubst.lean` | the cached substitutions (task #51): `instantiate1`, the three-layer `instantiate1Lift` (cutoff, budgeted descent, memoised walk) and the statements of the two bulk walks `instantiateList`/`instantiateRev` |
| `ExprOpsCAbs.lean` | the cached abstractions and level substitution (task #51): `abstract1`, `abstractRange`, `instLevelParams` (the one walk whose probe sits *before* the match) and `ProjEntry.typeAtI` |
| `ExprOpsCGuards.lean` | the cached scope queries, leaf guard, telescopes and definedness (task #51): `wscopedB` proved, and the statements of `fvarLeaves`, `leafGuard`, `instSpine`, `piResidual`, `allLevelParamsDefined` |

| `CoreKBase.lean` | task #49's shared foundation (`CORE_PLAN.md` step 4): `core_types::code_points` and the `str_lit_step`/`num_lit_step` packaging of a pinned name's body, `PinnedName`/`PinnedNames`, the three paired `kernel::env` readings, and `FindAgree`/`FindWF` — the *find-agreement* projection of `FEnv.FEnvRel`/`FEnv.FEnvWF` that `core_k.rs`/`prop_read.rs` read, with the two bridge lemmas |
| `CoreKProj.lean` | the `findProj?` reading over that weaker hypothesis: `find_proj`, and `fenv::tower_slots_all_f`/`rec_slots_all_f` (which `Refine/FEnv.lean` leaves to step 4) |
| `BasisNames.lean` | `kernel::basis_names` (task #49): all 26 pinned names, `rec_of` and `reserved_basis_names` |
| `CoreKNames.lean` | `core_k.rs`'s pinned `Nat`/`Bool` names and name tables (task #49): the eighteen names, `nat_op_names`/`nat_div_mod_names`/`nat_op_wf_names`/`nat_op_deps`, `is_nat_bin_op`, and `nat_to_dec`/`proj_model_name` (`Nat.toString` on a `u64`) |
| `CoreKVec.lean` | `core_k.rs`'s `Vec`/list plumbing (task #49): `drop_exprs`/`append_exprs`/`rev_append_exprs`/`expr_singleton`, `leaf_contains`/`fvar_leaves_subset`, `get_d_expr`/`rules_find`, `pi_residual`, `subst_const0`/`subst_const_all`, `lift_fueled` and the four loop budgets |
| `CoreKLits.lean` | literal reduction (task #49): `nat_lit_to_constructor`, `raw_nat_lit`, `lit_to_ctor_if_nat`, `str_lit_to_constructor`, `succ_of`, the equation table `nat_op_equations` and **`nat_op_result`**, the arithmetic fast path |
| `CoreKSupport.lean` | the literal-support guards (task #49): the `nat_*_ok`/`*_ty_ok` stored-shape family, `nat_lit_supported`, `str_lit_supported`, and the dead `Expr.constsResolve` |
| `CoreKGuards.lean` | `core_k.rs`'s readers, shape guards and owning probes (task #49): `defn_probe`/`ctor_probe`/`ind_probe`/`rec_probe`/`lp_empty`, `is_ctor_app`, `unfoldable_head`, `head_hint`, `is_unit_like_ty`, `same_const_heads`, `pi_result_*`, `caps_never_zero`, the leaf kind tests, `pw_written`, `annot_binder_meta`, `rec_rule_k`, `fire_is_inert`, `str_expansion_fires` and the dead `beta_gate_fires` |
| `CoreKNatOps.lean` | the `Nat`-operation pinning guards (task #49): `nat_op_guard`, `nat_op_stored`/`nat_op_stored_ok`, `nat_op_ty_pinned`, `nat_op_cod`, `bool_stored_ok`, `defn_lp_empty`, `deps_all_stored` |
| `CoreKShapes.lean` | the install-time rule bits and the certificate shape conjunctions (task #49): `struct_eta_shape_ok`, `eta_ctor_shape`, `unit_shape_ok`, the dead `eta_projs*`/`eta_fab_args*`, `proj_entry_fire_ok`, the `And`-rescue slots, `fab_scope_ok`, `rec_rule_k_of`/`rec_rule_eta_of`/`rec_rule_bits`/`proj_fn_rule`, `proj_fire_shape_ok` |
| `CoreKInfer.lean` | the pure inference clauses (task #49): `infer_lit_nat`, `infer_lit_str`, `infer_fvar`, `proj_entry_type_at`, `proj_type_at_checked`, `infer_proj_at`, `annotate_proj_entry` |
| `CoreKPinned.lean` | task #49's closing file: every hypothesis the eleven parallel files import — the pinned names, `NatOpPinned`, `PinnedBasisNames`, `VecFacts`, `EnvFacts`, the four `*Spec`s — discharged from the lemmas that prove them |
| `PropRead.lean` | `kernel::prop_read` (task #49): all eleven readers of the fast prop-ness path, each against the cited Lean instantiated at `lfe.find?` |

## The inductive routes (task #57, `CORE_PLAN.md` step 7)

`kernel::inductives` — the two install routes for an inductive block (task
#25) — refined against `ConLeche/Kernel/Inductives/*.lean` and the cached
drivers of `Cached/CheckerC.lean`.  Every lemma of this group **assumes the
knot** (`Core.KnotSpec mode IndAbs.checkFuelU`, task #55) and reaches the core
only through `IndAbs`'s five operation lemmas.

| file | contents |
|---|---|
| `IndAbs.lean` | the group's foundation: `checkFuelU` (`core_k::check_fuel()` as a value) and its two identities, the record abstractions `absRecFieldKind`/`absRecFieldKinds`/`absKindss`/`absCtors`/`absLevelss`/`absInductiveShape`/`absNativeParts`/`absStructParts` and the *relation* `NativePassRel`, the `*WF` predicates for all four records (all marked "to be unified into `Abs.lean`"), and the five `sharedOpsC` operations `ops_whnf`/`ops_infer`/`ops_annotate`/`ops_defeq`/`ops_ensure_sort` |
| `IndStructParts.lean` | `kernel::inductives::struct_parts` — the structure recogniser, its three `@[csimp]` walkers and the projection-body builder |
| `IndSumParts.lean` | `kernel::inductives::sum_parts` — the block-shape record, its copies (as identities), the member split `sum_split`, and `with_sort`/`rule_prefix`/`major_idx` |
| `IndNativeParts.lean` | `kernel::inductives::native_parts` — the **generated recursor**: every generator against its cited construction, node for node |
| `IndStructInstall.lean` | `kernel::inductives::struct_install` — the binder-domain comparison, the projection table's two guards and the table itself, against the `*F` spelling |
| `IndSumInstall.lean` | `kernel::inductives::sum_install` — the direct route's shared stages, parametric in the `CapsOf` dictionary |
| `IndNativeInstall.lean` | `kernel::inductives::native_install` — the direct route's pass and tail, split at the cached driver's two flush points |
| `IndModeled.lean` | `kernel::inductives::modeled` — the modeled route: the member checks, the recursor group and the projection functions |
| `IndSpec.lean` | `IndRoutesSpec`, the one `Prop` the checker tier (task #56) consumes: the two entry points `check_native_s`/`check_ind_decl_s` against `checkNativeS`/`checkIndDeclSF` |
| `IndC.lean` | `kernel::inductives::inductives_c` — the two routes' cached drivers, i.e. the **flush policy**, `ind_routes_spec` and (task #59) the bridge `ind_routes_spec_of_p` |
| `IndIngredients.lean` | task #59: the tier's **leaf** — the ~38 ingredient `Prop`s task #57's parallel files carried as hypotheses, each discharged from the file that owns it (`CheckerBaseSpec` from `Refine/CheckerBase.lean` under the knot, `structGens` from `Refine/IndStructParts.lean`, the install modules' `*Refines` from their owners) |
| `Scalars.lean` | task #59: the `u64 → usize` index cast in one place — the two cast-value lemmas and the discharges that close `i.val ≤ Std.Usize.max` from the `Vec` a counter came from.  **No platform axiom**: where the bound cannot be discharged it is a hypothesis, because the port's guards compare the *cast* |

## The top of the tower (task #60, `CORE_PLAN.md` steps 7's top and 8)

| file | contents |
|---|---|
| `Installed.lean` | `cached::installed` — **the declaration fold**: `absPendingCheck`/`absPendingChecks`/`PendingCheckWF` (marked "to be unified into `Abs.lean`"), the two install halves and their tails, the four-way phase-A dispatch and its three pushes, `annot_decl_step`, phase B's `check_pending` family with its fresh `CState`, both index recursions, `leanCheckDecls` and **`check_decls_refines`** |
| `Main.lean` | the capstone: `check_decls_verified_refines`, `conron.model_exists` and `conron.no_proof_of_False` from `ConLeche.MainTheorem`, each with a `#guard_msgs`-checked axiom census |

### How the tower composes, and what is still owed

Read bottom-up, `check_decls_refines` is the composition of every file above
it, and **exactly four hypotheses survive to the top** — the same four that
`Refine/Main.lean`'s two theorems carry, and no others:

| hypothesis | who discharges it |
|---|---|
| `hk : Core.KnotSpec mode IndAbs.checkFuelU` — the six core wrappers and bodies refine `coreKnotI` at `checkFuel` | **task #55** (`Refine/Core/Arms/*`, `Refine/Core/Knot.lean`); `Refine/Core/Statements.lean` is the statement it is proving |
| `hind : IndRoutesSpec mode` — the two inductive install routes | **task #59** (`IndC.ind_routes_spec_of_p`, the recogniser bridge task #57 owed); the tier is `sorry`-free since task #67 fixed `modeled.rs`'s `u64 → usize` casts |
| `hvar : CheckerPins.PinsWF pins` — every node of every pin is what the port's own smart constructor built | the same construction argument as `hds` (task #58 added it: `hpins` alone does not give it, since two pin lists can abstract to `natOpPinSets` with one carrying a stored hash word that makes `expr::beq` inexact).  Task #66 has a partial by-construction proof from `decode_embedded` |
| `hpins : absPins pins = ConLeche.natOpPinSets` — the port's pin list is the global the pinned con-leche bakes into `checkDeclStepC` | `Refine/Pins.lean`'s `check_decls_pins_refines` (open on that file's two statements, task #43), **or** the `pins-param` submodule bump, which deletes the hypothesis: `Installed.leanCheckDecls` is the one line that changes |
| `hds : ∀ d ∈ ds.val, DeclCWF d` — the parsed input is well formed | the parser, by construction (the `*WF` predicates of §3.5 are the port's own smart constructors) |

Everything else is *internal* and already discharged where it is used: task
#56's four cross-file `Spec`s in `CheckerPinned.lean`, task #49's in
`CoreKPinned.lean`, and the `FindAgree`/`FindWF` projections in
`CoreKBase.lean`.  The `sorry`s that remain below the top are arm-level bulk
(`CheckerSplit` 4, `CheckerDecl` 9, `DeclCheck` 14, `CheckerPins` 8,
`Checker` 5, `CheckerSplit`/`BasisPins`/`Pins` the rest — **`Installed` 0 since
task #62**); every one of them is a *guard cascade or a core call*, none is a
design question, and the axiom censuses in `Installed.lean` and `Main.lean` are
what will say so: `sorryAx` leaving `conron.model_exists` is the P3 gate.
`Installed.lean` itself is now `sorry`-free, so the only door `sorryAx` takes
into `check_decls_refines` is `annot_step_other_c_refines` →
`CheckerDecl.check_decl_step_c_refines`.

## Not yet here

`cached::core_c` (the knot's six wrappers and their bodies): `Refine/Core/`
holds `CORE_PLAN.md` step 6's statements (task #53) and its arms are task #55's.
Task #46's four files are steps 1 and 2, task #51's four `ExprOpsC*` files the
second half of step 3, task #49's twelve `CoreK*`/`BasisNames`/`PropRead` files
step 4, task #52's two `StateC*` files step 5, and task #57's ten `Ind*` files
the second half of step 7; `Refine/Checker.lean` and `Refine/DeclCheck.lean`
(step 7's first half) are task #56's.

## The knot (`Core/`, `CORE_PLAN.md` step 6)

| file | contents |
|---|---|
| `Core/Statements.lean` | the twelve statements as one proposition per fuel: `RefinesE`/`RefinesB`, `Wrappers`, `Bodies`, `KnotSpec` (Fable) |
| `Core/Knot.lean` | task #53's skeleton: `wrappers_zero`, `wrappers_succ`, `knot_induction`, the `memoEI`/`memoBI` run lemmas and the six probe lemmas |
| `Core/Arms/Shape.lean` | task #55's shared shape: `Sim`/`SimS`/`SimP`, the bridges to `RefinesE`/`RefinesB`, the six wrappers at one call site, and `knotV` (the io grade as a flag) |
| `Core/Arms/Bridge.lean` | `StateC`'s two named ingredients (`InstantiateListRefines`, `InstLevelParamsRefines`), discharged from task #54 |
| `Core/Arms/*.lean` | one file per group of `cached/core_c.rs`'s 120-function block, partitioned by which body reaches which helper: `Shared`, `Lits`, `Certs`, `Iota`, `Major`, `App`, `WhnfCore`, `Whnf`, `InferSpine`, `InferTele`, `Infer`, `InferSpineIO`, `InferIO`, `DefEqStruct`, `DefEq`, `Annotate` |
| `Core/Arms/Arms.lean` | the `Deps` discharges, `arms` and `knot_spec`, with the axiom census |

**The knot is closed** (task #61): `#print axioms knot_spec` is
`[propext, Classical.choice, Quot.sound]`, and so is every one of the six
`*_body_sim`.  Task #55 left nineteen `sorry`s across eight of these files —
four port deviations it found, `StateRel`'s missing `instC` entry-count
clause, two packaging cycles of its own fan-out and two unfinished literal
arms; task #61 fixed the Rust where the Rust was wrong, folded `InstCSize`
into `Refine/State.lean`'s `StateRel`, split `WhnfCoreDeps` by the budget and
`DefEqDeps`/`DefEqStructDeps` along the call order, and proved the rest.

## Not yet here

Everything *above* the knot: `Refine/CORE_PLAN.md` steps 7 and 8 — the
declaration fold, phase A and B, and `Refine/Main.lean`'s capstones.  Task #46's four
files are its steps 1 and 2, task #51's four `ExprOpsC*` files the second half
of its step 3, task #49's twelve `CoreK*`/`BasisNames`/`PropRead` files its
step 4, and task #52's two `StateC*` files its step 5; step 6 is the
induction.
(step 7's first half) are task #56's, and task #60's two files above are its
top and step 8.

## The pins (`Pins*`, task #64)

`kernel::pins_decode` — the verified reader of the embedded `con-ron-pins/1`
text (task #43) — against `ConRon.Dump.parsePins`, and the closed computation
that says what the embedded text decodes to.  Eight files, because the two
programs do not have the same shape: the port walks a byte slice with an index,
the reader splits a `String` into lines and each line into space-separated
tokens.

| file | contents |
|---|---|
| `PinsDec.lean` | the **byte-level reference decoder**: `kernel::pins_decode` function for function in Lean, over a `List Nat` *suffix* with `Option` for failure and con-leche values in the tables.  It is the joint the whole proof turns on, and its module note is the map |
| `PinsAbs.lean` | `absText`/`absNatOpPinSet`/`absPins` and the `absText_toStr` bridge (task #43's, moved here), plus `bytesOf` and `absTables` |
| `PinsBytes.lean` | **(A)** the model's scalars, escape and references against `PinsDec`'s: "the model's reader at `(t, i)` is `PinsDec`'s at `bytesFrom t i`" |
| `PinsRecords.lean` | **(A)** the `N`/`L`/`W`/`E` records, one smart-constructor lemma each |
| `PinsRun.lean` | **(A)** the `S` record and the pass, where the byte index becomes `PinsDec.runRecords`' fuel; `decode_refines` is (A)'s product |
| `PinsAscii.lean` | every byte the decoder accepts is ASCII — one `Consumes` predicate and one lemma per reader, which is what makes `absText` (a UTF-8 *decode*) readable character for character without a second walk over the port |
| `PinsSplit.lean` | **(B)** `String.splitOn` at a one-character separator, the two facts the tokenizer bridge rests on, and `absText` on an ASCII text |
| `PinsRead.lean` | **(B)** `PinsDec` against `parsePins`: the line invariant and the field invariant, per reader and per record; `parsePins_of_decode` is (B)'s product |
| `Pins.lean` | the statements: `pins_decode_refines` (proved, no axiom), `pins_closed` (the closed computation), `pins_text_decodes`, `check_decls_pins_refines` |

## Where the native-decide axiom lives

**In exactly one lemma, `ConRon.Refine.pins_closed`**, and in nothing else the
port proves.

`pins_closed` says that the text `kernel::pins_text::PINS_TEXT` embeds decodes,
under `ConRon.Dump.parsePins`, to con-leche's own `ConLeche.natOpPinSets`.  It
is **one closed computation on static data** — a fact about two committed
constants, and about no input the binary will ever be given.  Task #43 measured
why the Lean kernel cannot check it and none of the three reasons is a matter
of patience: the reference decoder is a well-founded recursion and does not
whnf; a 532 KB string literal expands quadratically in the kernel (27 s for
1 KB, over 300 s for 8 KB); and the round-trip route needs the same literal
equality plus a `Std.HashMap` in the kernel.  The maintainer's decision (task
#64) is to take it by `native_decide` **as an interim**, and spike #63 is the
attempt to remove it — a format whose decoding the kernel *can* check.

What that costs, exactly, is two axioms and they are both in the census:

* `pins_closed._native.native_decide.ax_…` — Lean 4.33 does **not** emit
  `Lean.ofReduceBool` for `native_decide`.  `Lean/Meta/Native.lean` compiles the
  proposition, runs it, and seals the result into a *fresh axiom named after the
  theorem*, asserting precisely `decide (parsePins … = .ok natOpPinSets) = true`
  and nothing else.  That is a strictly narrower trust assumption than
  `ofReduceBool`, and it says in its own name who spends it.  (The older
  spelling, `of_decide_eq_true (Lean.ofReduceBool …)` written by hand, is not an
  option here: the interpreter then has to evaluate `absText PINS_TEXT` — a
  532 K-element `List U8` — rather than the string literal, and does not
  finish.)
* `pins_text.PINS_TEXT._native.decide.ax_1` — **not ours**: Aeneas renders a
  `&str` constant as `toStr "…"` and discharges `toStr`'s bound
  `s.toByteArray.size ≤ U32.max` with its own default argument
  `by decide +native` (`Aeneas/Std/String.lean`, whose own comment says it
  should not).  Every extracted string constant carries it, before any proof of
  ours.  It is Aeneas's to fix, and `AENEAS_FINDINGS.md` records it.

**The decoder refinement itself spends neither.**  `pins_decode_refines` is a
theorem about every byte string, so nothing is ever evaluated, and its census is
con-leche's own three axioms.

**Both the general and the embedded capstones are kept.**
`Refine/Main.lean`'s `conron.model_exists'` / `conron.no_proof_of_False'` are
general in `pins` and carry `hpins : absPins pins = ConLeche.natOpPinSets`;
they do not mention the embedded text and nothing native-decide-shaped is in
their closure.  `conron.model_exists_embedded` /
`conron.no_proof_of_False_embedded` are the same theorems at the pin list the
binary actually folds with (`kernel::pins_decode::decode_embedded()`, what
`con_ron::driver::pins_for_run` passes by default), so they carry neither `hk`
nor `hpins` — and they carry the two axioms above.  Every one of those censuses
is pinned with `#guard_msgs in #print axioms`, which is what keeps the boundary
honest.

**`hoe` is gone for good.**  Tasks #24/#56/#58 carried two `orElse`
hypotheses to the capstones (`OrElseErrorStateSound`, `OrElseErrorDeclines`,
bundled as `CheckerDecl.DivModOrElse`); task #65 deleted them by making a
thrown pin attempt the verdict, and task #67 — which put the cited recovery
back — **proves** what they assumed rather than restoring them
(`CheckerPins.check_div_mod_pin_at_err` and `State.dup_state_eq`).  The
capstones' hypothesis list is the five rows above and nothing else.

**What is still owed on the pins: `hvar : CheckerPins.PinsWF pins`.**  The
`_embedded` corollaries discharge the pins' *value* and not their *well
formedness*.  `PinsWF` is `ExprWF` for each of the eight pinned expressions and
each certificate list, so discharging it from `decode_embedded` means threading
a full well-formedness invariant — names, levels, prop-whens and expressions —
through `PinsBytes` and `PinsRecords`.  It is cheap in kind and not in bulk:
`ExprWF`'s constructors *are* the port's smart constructors and every record
already applies exactly one, but every reader lemma in half (A) gains a
hypothesis and a conjunct.  Task #64 drafted that invariant (`TablesWF`) for the
`Name` half and then removed it when the `W` record turned out not to need it;
the full version is the next step.
