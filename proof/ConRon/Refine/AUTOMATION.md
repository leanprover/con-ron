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
subtracted; treat them as ratios.  **Task #70 (§"Cost, and the tuned idiom"
below) explains the 5× and brings it to 1.2–3.8× with the same idiom tuned.**

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

## Cost, and the tuned idiom (task #70, Fable, 2026-09-13)

The maintainer held adoption on the elaboration cost above: 4–8× the hand
proofs.  This section says where the time went, what removes it, what the
three additions to the question (a one-line induction, `grind cases`/`grind
ext` on the node types, `grind =>`/`sym =>` doing the inversion itself) turned
out to be worth, and ends with the idiom as it should be adopted.  All the
evidence is in `Automation/Study.lean` §"Task #70" and `Automation/SimpSets.lean`;
the numbers are net of the 1.9 s import, the minimum of two `lake env lean`
runs on the shared machine, ±0.1 s.

### Where the time went

| | `Level.rest_refines_aux` | `ExprOps.instantiate1_go_refines` | `Core.reduce_nat_lits_i_refines` |
|---|---|---|---|
| hand proof | 2.0 s | 0.65 s | 0.16 s |
| task #69 idiom | 6.9 s | 4.7 s | 0.84 s |
| … of which the normaliser `rust_inv` | 1.6 s | 2.5 s | 0.34 s |
| … of which elaborating the `grind [thirty lemmas]` list, once per goal | 3.9 s | 0.8 s | 0.1 s |
| … of which `grind` proper (E-matching, its simp, the solvers) | 0.4 s | 0.25 s | 0.08 s |
| … of which `grind`'s per-call internalisation of the context (typeclass probing above all) | 1.0 s | 1.2 s | 0.3 s |
| lemma set as `attribute [local grind …]` | 3.0 s | 3.9 s | 0.72 s |
| + registered simp sets, `obtain`/`split`/`simp` loop order | 2.3 s | 2.5 s | 0.6 s |
| + pre-order head reduction (= `rust_norm`) | **2.3 s** | **2.2 s** | **0.6 s** |
| + `-ring -linarith -order -lia` (not taken) | 2.2 s | 2.1 s | 0.5 s |
| tuned / hand | **1.15×** | **3.4×** | **3.8×** |

It is not E-matching: `grind`'s own categories are 5–10 % of the idiom's
time, and no lemma has bad activation (the instance counts are single
digits; the `diagnostics` show the `→` lemmas firing once each).  Four things
cost, in this order:

1. **The lemma list is elaborated at every `grind` call**, and `all_goals`
   makes 25 calls for `rest`.  Thirty names, each turned into an E-matching
   theorem with pattern inference, is ~150 ms; times 25.  Fix: the set as
   `attribute [local grind =]`/`[local grind →]` in a section, elaborated
   once.  (A bare `attribute [grind]` on an equation prints a "try these"
   suggestion per use; `grind =` is the silent spelling.)
2. **`rust_inv` runs the default simp set on the whole unfolded body**, and
   its `repeat' (first | split | simp | obtain)` order retries `simp` on an
   unchanged hypothesis after every `obtain` — ~60 ms a call, mostly
   Mathlib's `Filter.bind_def`/`List.bind_eq_flatMap`/`Part.bind_eq_bind`
   failing to unify at every `bind` node (the `diagnostics` list them).
   Three fixes, together 2.5 s → 0.9 s on the walk:
   * two registered simp sets (`SimpSets.lean`: `rust_reduce` for the head —
     the erased pointer operations, the `dup`s, and the node projections
     `Expr._0`/`ExprNode.kind`/… which Aeneas defines by `match`, so `simp`'s
     own projection reduction never sees them; `rust_invert` for the bind
     inversion and the pair/injectivity/`∃` cleanup).  `simp only [thirty
     names]` re-elaborates its list at every call (~25 ms); a registered set
     is elaborated once;
   * the loop ordered `obtain` / `split` / `simp`, so the cheap peel runs first
     and `simp` only sees a hypothesis that changed shape;
   * the head reduced in **pre-order** (`↓bind_arc_deref`, `↓` on the
     projection lemmas): `arc_deref_eq` is a post-order rewrite, so `simp`
     visited every dead arm of the generated `match` (ten arms, each with a
     nested ten-arm `match`) before the bind at the top reduced and the
     `match` on the known node collapsed.
3. **`grind`'s round limit.**  With the splits done outside, the Option-monad
   plumbing of `rest` needs more than the default five E-matching rounds
   (`[limit] maximum number of E-matching rounds`, no other threshold), and
   a two-wrapper arm one more term generation than `gen := 8`.  `(ematch :=
   12) (gen := 24)` passes all six lemmas of this section; it is the closing
   macro's fixed configuration, so no lemma tunes a budget.
4. **What remains is `grind`'s per-call internalisation**, ~100 ms a goal in
   the walks: a trivial goal in the same file costs 1.5 ms, so it is the
   context, not a start-up cost.  The `synthInstance` trace of one walk shows
   ~110 instance problems per call, half of them the arithmetic modules
   asking whether `ℤ`, `ℕ` and `Result Expr` are ordered rings
   (`Lean.Grind.CommRing (Result expr.Expr)` ×13, `OfNat ℤ 0` ×70, …);
   `-ring -linarith -order -lia` buys 10–15 % and is not worth the coupling.
   The rest is proportional to the hypotheses in scope.  This is the floor
   of the approach: `all_goals grind` builds one E-graph per branch, and
   nothing in Lean 4.33's `grind` shares that work between goals.

### The three additions

* **One line per lemma, no shape line per constructor: yes.**  The standard
  `induction he` leaves `e` a variable with `expr.app f a = ok e` as a
  hypothesis, and the body's `match e._0.kind` is stuck until that equation
  has been inverted — which is the per-constructor line.  `ExprWF.ind_node`
  (`Study.lean`) is the induction principle with the motive stated on `.mk
  (.mk d k)`: the inversion happens once, inside the principle, and
  `induction e, he using ExprWF.ind_node <;> close` is the whole lemma.  The
  motive has to depend on the derivation (`motive e he`, both targets
  explicit — the non-dependent forms are rejected as "too many targets" or
  make the WF hypothesis an alternative), so the induction hypotheses come
  out as `∀ h, motive f h`; `grind` uses them like any local implication,
  and the `use`-lemma packaging of the IH needs no change.  The children's
  well-formedness comes from one forward lemma per kind
  (`ExprWF.app_kids`, from `CoreK.ExprWF.children`).  `instantiate1_go`
  and `reset_meta_go` are each one line; `Level`/`Name` walks would need the
  same principle on `LevelWF`/`NameWF` (5 and 3 cases, mechanical).
* **`grind cases` / `grind ext` on the node types: no.**  `grind ext` is
  rejected outright (`expr.Expr` "is neither tagged with `[ext]` nor is a
  structure": the three-type mutual inductive is not a `structure`), and
  `attribute [grind cases] expr.ExprKind` is accepted but is about
  case-splitting *hypotheses* of an inductive predicate; a variable
  discriminant `e._0.kind` is not a hypothesis.  Measured anyway
  (`induction he <;> …` with the inversion lemmas as `→` rules, `grind
  cases` on the kind, and the tuned macros): 49 s and 75 failures — `grind`
  has to open the whole body itself, which is the next point.
* **`grind =>` / `sym =>` doing the bind inversion: no.**  `sym =>` (4.33's
  symbolic-simulation mode: `intro`/`internalize`/`simp` on the target only,
  `cases_next`, `finish`) on the smallest lemma, with the Rust equation
  reverted into the target: `intro hok; finish` runs 8.5 s and fails at a
  case depth of 24; a plain `grind` on the same goal (it splits `match`es
  itself) is identical, 8.6 s and the same failure; `sym => simp […]` on the
  target first, 4.5 s and a failure.  The reason is structural: the whole
  generated body is internalised into the E-graph before the first split and
  every branch carries it, where the normaliser shrinks the hypothesis to
  the reachable arm *before* anything else runs (one `simp only` pass with
  the pre-order head rules, ~20 ms).  `sym`'s `simp` cannot do that job in
  its place because it works on the target and does not split; and sharing
  the E-graph across branches, the point of the suggestion, is exactly what
  makes it slow — the branches are only cheap when they are small.

### One more lemma of each kind

| lemma | hand | tuned | text |
|---|---|---|---|
| `Level.by_cases_refines_aux` (singleton vectors, `subst`/`simplify` twice, IH) | 75 lines, 0.44 s | 0.8 s (1.8×) | 5 lines + six one-line `use`/WF lemmas |
| `ExprOpsMeta.reset_meta_go_refines` (memoised walk, `Expr`-keyed memo) | 330 lines, 0.62 s | 2.0 s (3.3×) | 1 line + a 5-line macro + `Spec`/`use`/`iff` (12 lines) |
| `Lits.reduce_nat_bin_i_refines` (arm with an inlined fragment, `natOpResult`) | 73 lines on `lits_replay` (75), not timed apart | 0.5 s | 4 lines + `natBinI_eq` (16) + three `use` lemmas |

The first two went through unchanged.  The arm taught two more
**statement-shape rules** (in `Study.lean` beside the lemma):

* a fragment con-leche inlines under a different continuation
  (`natBinI` vs `natLitsI`) needs one equation `natBinI … = natLitsI … >>= k`
  (monad laws, `rfl` per branch) where the hand proof quantified the
  continuation (`lits_replay`);
* **quantified clauses inside a `Spec` do not fire.**  `OpSpec`'s `∀ e, o =
  some e → …` takes its E-matching pattern from its conclusion (`absExpr e`)
  and instantiates at every expression in sight but the right one; a WF
  clause `∀ p, o = some p → NatWF p.1 ∧ …` instantiates at the pair and
  leaves `(fst, snd).1` unreduced.  Both become `use` lemmas keyed on the
  Rust equation *with the constructor in it* (`nat_op_some_use : nat_op_result
  c a b = ok (.Ok (some e)) → …`) or quantified over the components (`∀ m n,
  o = some (m, n) → …`);
* and one normaliser rule: the `let (n, n1) := val` a Rust `Some((n, n1))`
  pattern produces is a one-alternative `match` that neither `split` nor
  `simp` opens while `val` is a variable; `rust_norm` ends with
  `rust_pairs`, a syntactic scan that `cases` every pair in the context.
  (Not `obtain ⟨_, _⟩ := ‹_ × _›`: elaborating that unifies every hypothesis
  type with `?a × ?b`, unfolds the `Wrappers`/`Spec` predicates on the way,
  and times out.)

### The idiom, as it should be adopted

```lean
-- once per file: the lemma set, as attributes (silent, elaborated once)
attribute [local grind →] Inst1Spec.use Expr.app_refines app_wf' hit' set' …   -- Rust equation first
attribute [local grind =]  KeyWF_mk absKey_mk Inst1Q_iff absExpr_mk bind_eq_ok_iff …
attribute [local grind]    ConLeche.Expr.instantiate1 absExprKind             -- the definitions to unfold

-- once per walk: the closing tactic (the Spec's binders, the unfolding, the idiom)
macro "inst1_close" : tactic => `(tactic| (
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    rust_norm h
    all_goals rust_grind))

-- the lemma
theorem instantiate1_go_refines … (he : ExprWF e) : Inst1Spec v e := by
  have hx := key_exact
  induction e, he using ExprWF.ind_node <;> inst1_close
```

`rust_norm h` = `simp only [↓head rules, rust_reduce] at h`, then `repeat'
(first | obtain ⟨_, h⟩ := h | split at h | simp only [rust_invert, …] at h |
rust_pairs)`; `rust_grind` = `grind (ematch := 12) (gen := 24)`.  Leaves and
arms are the same two lines after their own shape step (`obtain ⟨⟨_, k⟩⟩ :=
l` for a `Level`, `Sim.ofRun` + `unfold` for an arm; `split` does the
`cases`).  The library-side changes of the task #69 recommendation stand
(`use` lemmas beside every `Spec`, equation-first argument order, per-pair arm
equations, `RunOk` as `SimS`'s conclusion), plus the two shape rules above,
`ExprWF.ind_node` (and its `LevelWF`/`NameWF` twins) in `Refine/Expr.lean`,
`SimpSets.lean` and the two macros in `Refine/Abs.lean`.

### Limits, plainly

* **Cost: 1.2–1.8× the hand proof on the leaves, 3.3–3.8× on the walks and
  arms** — the maintainer's "within ~2×" is met on the leaves only.  What is
  left is `grind`'s per-goal internalisation of the context, and it is
  proportional to the context: a walk's goal carries the memo invariant, the
  key-exactness fact and the induction hypotheses.  Two things would move it
  and were not done: stating the `Spec` so that fewer hypotheses are in scope
  when `grind` runs (`clear` in the macro is not robust), and a future `grind`
  that caches instance probing across calls.  Per file this is a build-time
  growth of ~2–3× (`Level.lean`, `ExprOps.lean` from about a minute to two or
  three), against 5–10× fewer lines.
* **Every lemma needs its `use` lemmas keyed the right way**, and the
  failure mode when one is keyed wrong is a `grind` failure with a
  multi-screen diagnostic, not a hint.  The three rules above (equation
  first; constructor in the equation for optional clauses; components, not
  pairs) cover everything met in six lemmas; the next kind of lemma may add
  one.
* **Not exercised**: the largest arms (`defeq_body_i`, ~1 500-line files),
  where the context is larger and the per-goal cost will be too; `HashMap`/
  `Nat` (mathematical), `Pins*` (byte-level), `Ind*` (list folds) remain out
  of scope.
* **`(ematch := 12) (gen := 24)`** is one configuration for six lemmas;
  a lemma that needs more will say so with the `[limit]` line in its
  diagnostics, and raising the macro's default is the answer, not a
  per-lemma override.

**Recommendation: adopt with the tuning** — the tuned idiom (`rust_norm`,
`rust_grind`, attribute-registered lemma sets, `ExprWF.ind_node`), during the
task #67 restatement, leaves and walks first, measuring the first file's
build time against its hand version and stopping at 3×.
