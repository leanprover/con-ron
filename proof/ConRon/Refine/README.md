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
  lean_f (abs x) = abs y`, nothing claimed when Rust fails;
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
| `State.lean` | `cached::state_c` (task #46): `StateRel`/`StateWF` over the fourteen memo maps, the fresh state, `flushed`, and the memo probe/insert lemmas |
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
| `IndC.lean` | `kernel::inductives::inductives_c` — the two routes' cached drivers, i.e. the **flush policy**, and `ind_routes_spec` |

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

The `annotate` body is closed (`#print axioms annotate_body_sim` is the three
standard axioms); `whnf`, `infer` and `infer_io` are assembled and name their
gaps; `whnf_core` and `defeq` wait on the two integration items DESIGN.md's
task #55 entry records.

## Not yet here

Everything *above* the knot: `Refine/CORE_PLAN.md` steps 7 and 8 — the
declaration fold, phase A and B, and `Refine/Main.lean`'s capstones.  Task #46's four
files are its steps 1 and 2, task #51's four `ExprOpsC*` files the second half
of its step 3, task #49's twelve `CoreK*`/`BasisNames`/`PropRead` files its
step 4, and task #52's two `StateC*` files its step 5; step 6 is the
induction.
