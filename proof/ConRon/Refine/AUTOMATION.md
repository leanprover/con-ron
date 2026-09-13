# Automating the refinement proofs: a study (task #69, Fable, 2026-09-13)

**Question** (the maintainer): the simulation proofs are mechanical — could
they be `some induction <;> grind [function_of_interest]`?

**Answer**: nearly.  Three representative lemmas of the tower — a state-free
case analysis with an induction hypothesis, a memoised `Expr` walk, a knot arm
with two wrapper calls — each go through with **one idiom**,

```lean
⟨shape⟩ ; rust_inv h ; all_goals grind [⟨lemma set⟩]
```

and the proof text shrinks by an order of magnitude.  What it costs is a fixed
list of *statement-shape* rules (below), one shape line per constructor in an
induction, and roughly 5× the elaboration time.  The evidence is
`Automation/Study.lean` (builds, no `sorry`, default heartbeats); nothing in
the tower was changed.

| lemma | hand proof | automatic | elaboration (hand → auto) |
|---|---|---|---|
| `Level.rest_refines_aux` (25 cases, IH) | 268 lines | 10 lines + 12 one-line arm equations | 1.5 s → 6.5 s |
| `ExprOps.instantiate1_go_refines` (10 cases, memo) | 340 lines | 10 shape lines + a 9-line closing macro + 8 one-line wrappers | 0.65 s → 5.3 s |
| `Core.reduce_nat_lits_i_refines` (`lits_replay`, 2 wrapper calls) | 79 lines | 5 lines + 3 `use`/plumbing lemmas | 0.2 s → 1.0 s |

Times are single `lake env lean` runs on the shared machine, import cost
subtracted; treat them as ratios.

## The idiom

1. **Shape.**  Destructure what the generated body matches on: the two
   `Level`s (`obtain ⟨⟨h, k⟩⟩ := l`) and `cases kl <;> cases kr`, or, under an
   `ExprWF` induction, the constructor's inversion lemma (`obtain ⟨d1, rfl, -,
   -, -⟩ := Expr.app_inv h1`).  This line is mechanical but *per constructor*:
   the fully uniform `induction he <;> …` does not work, because the body
   matches on `e._0.kind` and neither `simp` nor `grind` reduces that while
   `e` is a variable.
2. **`rust_inv h`** (`Study.lean`): `repeat' (first | split at h | simp at h
   | obtain ⟨_, h⟩ := h)`.  `simp` knows `bind_eq_ok_iff` and `Prod.exists`,
   so it inverts the binds and splits the pairs; `obtain` peels one `∃`/`∧`
   layer; `split` opens the `match`/`if` that guards the rest; `simp` closes
   the branches it refutes (`ok (.Err e, s) = ok (.Ok r, s')`).  What is left
   is one goal per reachable success path with plain equations in context.
   `grind` can do all of this itself — but on a deep chain it spends its
   budget on junk instances first (see "what does not work").
3. **`grind [lemma set]`**, where the set is:
   * the induction/wrapper hypothesis **as a predicate with a `use` lemma
     whose first hypothesis is the Rust success equation**
     (`LeqCoreSpec.use`, `Inst1Spec.use`, `Wrappers.whnf_use`), given with
     `→`;
   * the con-leche **arm-selection equations without side conditions**
     (`rest_max_zero`, … — one per constructor pair, each a one-liner);
   * the constructors' abstraction and WF facts as **forward lemmas
     triggered by the smart-constructor equation** (`→ Expr.app_refines`,
     `→ app_wf'`), the abstraction reductions (`absExpr_mk`, `absExprKind`,
     `absLevel_mk`), the scalar value lemmas (`→ i64_add_val`,
     `→ HashMap.uscalar_sub_eq`), and `bind_eq_ok_iff`;
   * for a knot arm: the con-leche monad plumbing as **unconditional
     equations** (`run_bind_eq`, `except_bind_ok`, `run_pure_eq`) and the
     statement in **`RunOk` form** (below), with `(gen := 24)`.

## What does not work, and why

* **Local `∀` hypotheses as the IH.**  `grind` uses them, but infers their
  patterns from the *conclusion* (`leqCore ↑fuel (absLevel l) (absLevel r)
  ↑d`), which never appears once `absLevel ⟨_, .Succ t⟩` has become `.succ
  (absLevel t)`; and `grind [→ hQ]` is rejected ("redundant parameter,
  `grind` uses local hypotheses automatically").  Hence the `Spec` predicate
  + `use` lemma packaging — which is also the natural way to state the knot
  (`Wrappers`/`Bodies` already are such predicates).
* **`→` takes its patterns from the propositional hypotheses in order.**
  `Expr.app_wf hf ha : expr.app f a = ok e → ExprWF e` has `ExprWF f`,
  `ExprWF a` first, so `→ Expr.app_wf` instantiates at *every pair of
  well-formed terms* (quadratic junk; the real instance never came).  The
  study reorders (`app_wf'`); the library should adopt the order "Rust
  equation first" for every `_wf`/`_refines` lemma.  `grind_pattern` cannot
  substitute: an `Eq` is not an admissible pattern ("(non-forbidden)
  application expected").  An equation hypothesis is in fact matched as the
  *pair* of its sides, so a `→` lemma fires whenever both `f x` and `ok y`
  are present — harmless extra instances as implications.
* **Side conditions of the form `∀ s, r ≠ .succ s`** (`Level.rest_max`,
  `rest_imax_r`, `rest_r_succ`) make `grind` diverge (a `whnf` timeout at
  any budget: the instantiated side condition becomes an E-matching theorem
  of its own).  One specialisation per constructor pair, no hypothesis, is
  the fix — twelve one-liners for `rest`.
* **Existential conclusions.**  `Sim`/`SimS` end in `∃ lst', g.run lst = .ok
  (A r, lst') ∧ …`; `grind` negates this into `∀ lst', …` whose body is not
  in the E-graph, so the facts it derives about `g.run lst` never reach it.
  `RunOk (g.run lst) P` (`Study.lean`) is the same claim as a predicate on
  the run result; `Sim.ofRun` converts.  If the tower is ever restated, this
  is the shape to use.
* **Conditional rewrites with free variables on the right** (`Lits.runBind`:
  `x.run lst = ok (a, lst') → (x >>= f).run lst = (f a).run lst'`) never
  fire — `a`, `lst'` are not in the pattern.  `run_bind_eq` (unconditional,
  `rfl`) plus `except_bind_ok` do the same job.
* **`Membership` on `Option`** (`∀ m ∈ o, NatWF m`): `grind` does not unfold
  it; state `∀ m, o = some m → …`.
* **Term-generation limit.**  A two-wrapper arm needs `grind (gen := 24)`;
  the default `gen := 8` stops one rewrite short (the diagnostics say so:
  `maximum term generation has been reached`).
* **The pattern-`let` for pairs** (`let (f2, memo2) ← …`, task #16's trap)
  stays folded under the next bind after one `simp at h`; `rust_inv`'s loop
  is what unfolds it level by level.

## What it would mean for the tower

* **Task #67 (full-outcome restatement)** is the moment to adopt this: every
  lemma is being restated anyway.  Per file, the work is (i) the arm-selection
  equations and `use` lemmas — a few one-liners each, once — and (ii)
  replacing the proof bodies by the idiom.  Expect the ~105 k proof lines to
  drop by 5–10× where the idiom applies (the leaves and walks: `Level`,
  `Name`, `Expr`, `ExprOps*`, `CoreK*`, the arms), and the `lake build` time
  of those files to grow by a similar factor (from seconds to tens of
  seconds per lemma; `Level.lean` and `ExprOps.lean` would go from ~1 min to
  several).  The knot arms in `Sim` form need the `RunOk` restatement first,
  which is a change to `Shape.lean` and mechanical everywhere else.
* **con-leche bumps** become cheaper in proportion: a moved arm or a renamed
  field changes the shape line and the arm equations, not a 300-line proof.
* **Not covered by this study**: the `HashMap`/`Nat` library proofs
  (genuinely mathematical, `omega`/`scalar_tac` heavy), the pins decoder
  (`Pins*`, byte-level), and the inductive routes (`Ind*`, list folds) — those
  are not simulation proofs of the shape studied.  Also untested: whether the
  idiom holds at the *largest* arms (`defeq_body_i`, ~1 500-line files),
  where `grind`'s budget may need tuning per lemma.

## Recommendation

Adopt the idiom for the task #67 campaign in the leaf and walk tiers first
(`Level`, `ExprOps*`, `CoreK*`), with the library-side changes it needs made
once: `use` lemmas beside every `Spec` predicate, equation-first argument
order on `_wf`/`_refines` lemmas, arm-selection equations per constructor
pair, and `RunOk` as the conclusion shape of `SimS`.  Keep `rust_inv` in
`Refine/Abs.lean`.  Measure the build time after the first file and stop if
it exceeds 5× the hand proofs.
