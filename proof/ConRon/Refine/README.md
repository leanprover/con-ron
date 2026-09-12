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
| `BasisTables.lean` | `kernel::basis_tables` (task #22): the generated basis tables are the value they were generated from |
| `HashMapWF.lean` | task #16's deferred `Eq2` generalisation, written for its first client (task #46): the bucket walks and the `Std.HashMap` bridge under a *forward*, key-restricted exactness hypothesis (`Eq2Fwd`) instead of `Eq2Spec` |
| `Env.lean` | `kernel::env` (task #46): the mode accessors, the `Vec` copies and the `*_dup` identities, `rec_rule_parsed`/`ind_caps_default`/`default_expr` (the Lean's field defaults), `proj_table_entry`, `pi_sort_tele_len`, `ind_params_ok`, the reserved names `proj_fn_name`/`proj_table_name`, `abs`'s injectivity on the well-formed records, the whole `*_beq` family exactly, the accessors, and `find`/`find_proj` |
| `FEnv.lean` | `kernel::fenv` (task #46): `FEnvRel`/`FEnvWF`, `mk_fenv_go`/`mk_fenv`, `find`/`find_proj`, `restrict_to`, `dup`, and `push`'s two sound clauses (`push_refines` itself is the tier's one `sorry`: the Aeneas model of `Vec::insert` is `List.set`, see the file) |
| `State.lean` | `cached::state_c` (task #46): `StateRel`/`StateWF` over the fourteen memo maps, the fresh state, `flushed`, and the memo probe/insert lemmas |

## Not yet here

`level::zeroness_of` and `level::subst_pw` (added at task #13, the
`Level`-to-`PropWhen` bridge), `kernel::expr_ops` and everything above the
state: `Refine/CORE_PLAN.md` is the design for the rest, and tasks #46's four
files are its steps 1 and 2.
