# The refinement of the core: statements and order (P3, Fable, 2026-09-12)

This is the design for the proof tier above the leaves (`Nat`, `HashMap`,
`Name`, `Level`, `PropWhen`, `Expr`, the basis tables are done).  It fixes
the *shape* of every remaining lemma so that the tasks are mechanical.

## Relations, not functions, for states and environments

`absExpr`/`absLevel`/`absName`/`absPropWhen` are functions (the Rust value
determines the Lean value).  Two things cannot be abstracted by a function:

* **`CState`** holds fourteen `ron::HashMap`s; con-leche's `CState` holds
  `Std.HashMap`s, whose internal layout no function of ours can reproduce.
  So `StateRel (st : Generated.CState) (lst : ConLeche.CState) : Prop` says,
  per map, `HashMap.Rel` of task #16: every lookup agrees under the key and
  value abstractions (`absExpr`, `absLevel`, `absName`, tuples thereof).
* **`FEnv`** likewise (`idx : Std.HashMap`), plus con-leche reads the
  environment only through `FEnv.find?`/`findProj?` (`coreKnotI_congr`):
  `FEnvRel (fe : Generated.FEnv) (lfe : ConLeche.FEnv)` says `find` agrees
  (`absConstantInfo` on the result), `visible_below` agrees, and the
  `Env` list agrees (`absEnv fe.env = lfe.env`, a function: `Env` is a list).

Well-formedness: `StateWF st` (every stored `Expr`/`Level`/`Name` in every
map is `ExprWF`/…; the pointer fast paths need it), `FEnvWF fe`
(every stored `ConstantInfo` is WF), `ExprWF` on inputs — all hereditary,
in the task #5/#17 style.

## The lemma shape for a knot wrapper (six of them)

For `W ∈ {whnf_core, whnf, infer, defeq, annotate, infer_io}` and the
Lean field `W'` of `CoreFnsI`:

```lean
theorem W_refines (mode) (fuel : U64) (st : CState) (fe : FEnv) (d : U64) (e : Expr)
    (r : Expr) (st' : CState)
    (hst : StateWF st) (hfe : FEnvWF fe) (he : ExprWF e)
    (h : Generated.cached.core_c.W mode fuel st fe d e = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', ((ConLeche.Cached.coreKnotI (absMode mode) lfe fuel.val).W' d.val (absExpr e)).run lst
                = .ok (absExpr r, lst')
            ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r
```

(`defeq` returns `Bool`, no `ExprWF r`.)  Exact result on success; nothing
on failure (§3.5).  The Rust wrapper at `fuel` corresponds to
`coreKnotI … fuel` (the Rust probes, then runs the body at `fuel - 1`,
then inserts, exactly `memoEI`; task #23).

## Bodies

`W_body_i` (the `CoreC.lean` twins, `cached/core_c.rs`) are stated the same
way against the Lean body applied to the record `coreKnotI … fuel`:

```lean
theorem whnf_body_i_refines … (h : Generated.cached.core_c.whnf_body_i mode fuel st fe d e = ok (.Ok r, st')) :
    ∀ lst lfe, … → ∃ lst', (ConLeche.Cached.whnfBodyI (coreKnotI (absMode mode) lfe fuel.val) d.val (absExpr e)).run lst = .ok (absExpr r, lst') ∧ …
```

and every helper the bodies call (the `core_k.rs` readers, guards, literal
reduction, `state_c.rs` wrappers such as `inst_list_m`, `const_ty_at_m`) gets
its own exact-result lemma against its cited Lean definition, with `StateRel`
in and out where it touches the state and plain equalities where it does not.

## The induction

One theorem per wrapper and per body, proved **together by induction on
`fuel`** (`Nat.rec` on `fuel.val`, or strong induction), the same way task
#5 proved `leq_core`/`rest`/`by_cases`: at `fuel = 0` every wrapper fails
(nothing to prove); at `fuel + 1` a wrapper's memo probe either hits (the
`Rel` lemma gives the Lean lookup, the invariant `StateWF` gives WF of the
result) or misses and the body lemma at `fuel` applies; a body's recursive
calls are wrappers at the *same* `fuel` (the decrement is in the wrapper),
so the body lemma at `fuel` uses the wrapper lemmas at `fuel`.  Hence the
statement to induct on is the conjunction of all twelve at a fixed `fuel`,
and the wrapper lemmas at `fuel + 1` follow from the body lemmas at `fuel`.
Split the bodies' cases into helper lemmas per arm (as `rest_refines` was),
each a separate file under `Refine/Core/`, so that many agents can work in
parallel on arms once the statements are in place.

## Order of work

1. `Refine/Abs.lean`: `absConstantVal`, `absConstantInfo` (move task #22's
   `T22` copies here), `absEnv`, `absMode`; `Refine/Env.lean`: `env.rs`
   refinements (`find`, `constant_info_beq` exact, …).
2. `Refine/State.lean`: `StateRel`, `StateWF`, the fourteen maps' `Rel`
   instances, `flushed`/`new`; `Refine/FEnv.lean`: `FEnvRel`, `FEnvWF`,
   `find`/`find_proj`/`push`/`restrict_to`/`mk_fenv`.
3. `Refine/ExprOps.lean` (resume the parked branch `parked/task-21-exprops-refine`
   after the `Arc` rename), then `Refine/ExprOpsC.lean` (the memoised twins:
   the same statements with `StateRel`).
4. `Refine/CoreK/*.lean`: the state-free leaves of `core_k.rs` (literal
   reduction, `nat_op_result` via `Refine/Nat`, guards, readers).
5. `Refine/StateC.lean`: the `*M` wrappers and `inst_list_m`.
6. `Refine/Core/Statements.lean`: the twelve statements as one `structure`
   of propositions indexed by `fuel`; `Refine/Core/Arms/*.lean`: one file
   per body arm; `Refine/Core/Knot.lean`: the induction.
7. `Refine/Checker.lean`, `Refine/DeclCheck.lean`, `Refine/Inductives/*`,
   `Refine/Installed.lean`: the fold, phase A and B, `check_decls_refines`.
8. `Refine/Main.lean`: `conron.model_exists`, `conron.no_proof_of_False`,
   axiom census.
