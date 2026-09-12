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

## What is here (tasks #17 and #20, P3.3)

| file | contents |
|---|---|
| `Abs.lean` | the plumbing `simp` set, `absString`/`absName`/`absLevel`/`absNames`/`absLevels`/`absOrdering`/`absPropWhen`/`absLiteral`/`absBinderMeta`/`absExpr`, the `*_inv` smart-constructor shapes, `StrWF`/`NameWF`/`LevelWF`/`NamesWF`/`PropWhenWF`/`LevelsWF`/`LiteralWF`/`BinderMetaWF`/`ExprWF`, and `Level.ind'`/`Name.ind'` |
| `Name.lean` | `absString`/`absName` injectivity, `str_eq`, `beq`, `contains`, `singleton` |
| `Level.lean` | the task-#5 development: `absLevel` injectivity, `beq`, `level_has_param`, `subst`, `is_never_zero`, `simplify`, and the `leq_core`/`rest`/`imax_rules`/`by_cases`/`leq`/`is_equiv` cascade |
| `PropWhen.lean` | `name_cmp` (through `str_compare`/`nat_compare`/`ord_then`), `merge`/`canon`, the smart constructors, `to_list`/`to_list_opt`, `is_never`/`has_params`/`holds`/`params_defined`, `inter`, `bind_z`, `beq`, and (task #20) `absPropWhen`'s injectivity and `beq`'s reflexivity |
| `Nat.lean` | `ron::nat` (task #15), plus (task #20) `cmp`/`beq` reflexivity |
| `HashMap.lean` | `ron::hashmap` (task #16) |
| `Expr.lean` | `kernel::expr` (task #20): the packed word (`pack_bits`, the `*_val` readings, `wf_data`), the ten smart constructors, the three exact accessors, `beq_recursive`, `levels_beq`, the copies, `absExpr`'s injectivity, and `beq`'s reflexivity and exactness |

## Not yet here

`level::zeroness_of` and `level::subst_pw` (added at task #13, the
`Level`-to-`PropWhen` bridge), `kernel::expr_ops`, `kernel::env`,
`kernel::fenv` and everything above them.
