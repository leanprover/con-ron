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

## Not yet here

`kernel::env`, `kernel::fenv` and everything above them.
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

## Not yet here

`cached::core_k`, `cached::state_c`'s `*M` wrappers, `cached::core_c` and
everything above them: `Refine/CORE_PLAN.md` is the design for the rest, task
#46's four files are its steps 1 and 2, and task #51's four `ExprOpsC*` files
are the second half of its step 3.
