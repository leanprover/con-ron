# What con-ron learned about Charon and Aeneas

A report *for the Charon and Aeneas maintainers*, collected from con-ron's task log
(`DESIGN.md`; entries cited as "#N").  con-ron is a ~42 000-line Rust transliteration of
the con-leche Lean kernel, translated by Charon + Aeneas to ~52 500 lines of Lean and
partly proved to refine the Lean original.  As far as we know it is the largest single
crate to have been through this pipeline: one `mutual` block of 84 functions, 415
`partial_fixpoint`s, `.llbc` files up to 179 MB.

Each finding gives the Rust shape that triggers it and the workaround we shipped, marked
**[bug]** (looks like a defect), **[limitation]** (a gap, documented or not) or
**[surprise]** (works as designed but cost us time).  The headline is positive: the tool
carried a 42k-line crate with 18 error-driven fixes, and the generated Lean reads like the
Rust.

## 1. Versions and pins

| | |
|---|---|
| Aeneas | `AeneasVerif/aeneas` **505b6ca35217e7be5c96c3e2f8045edfbdf47291** (2026-09-08); translator and `backends/lean` from the same rev |
| Charon | `aeneasverif/charon` **b104e24fea7d721b71e6c39fd70f26ff20bc0980**, via Aeneas's own flake input |
| Rust toolchain | the nightly Charon pins, **nightly-2026-08-18** |
| Lean (our proof project *and* con-leche) | **leanprover/lean4:v4.33.0** + Mathlib `v4.33.0` |
| Lean the Aeneas library wants | v4.31.0 — reconciled by our 375-line `spikes/toolchain/aeneas-433.patch` (§3.1) |
| CLI | `charon cargo --preset=aeneas --dest-file <abs>.llbc`; `aeneas -backend lean -split-files -loops-to-rec -dest … -subdir ConRon/Generated -namespace ConRon.Generated -no-progress-bar` |

The Rust subset we hold ourselves to (`DESIGN.md` §3.4, enforced by a lint script): no
closures, no `?`, no `loop`/`while`, no `std::collections`, no `unsafe`, no
`#[derive(Debug)]` on recursive types, `&mut` only for the state parameter, `Rc` API
limited to `new`/`clone`/`deref`/`ptr_eq`.  Almost every finding below is a rule that
subset exists to encode.

## 2. Translator findings

### 2.1 What made Aeneas fail

**F1. A container borrow held across a branch that touches the container.** **[bug]** —
*the commonest failure: 14 of our 18 Aeneas errors.*  Rust shape:
`let ok = match &block[i] { … }; if ok { recurse } else { … }`, or a memo probe
`match s.map.get(k) { Some(r) => …, None => { s.map.insert(…) } }` with `s: &mut CState`.
Aeneas says *"Could not match the contexts"* or, about as often, *"Internal error, please
file an issue"* / *"Unreachable"*.  Fix: lift the *test* into its own function, so the borrow
dies at the call boundary and the caller reads `if helper(…) { … } else { … }`.  We did this
21 times; the rule is "never hold a container's borrow across a branch that touches the
container".  #14 (5 errors), #23 (2), #24 (2), #25 (5), #30 (1).  Every fix was an
improvement on its own terms — the factored predicate is usually something the Lean source
already names — but the diagnostics never point at the join, and "Internal error, please file
an issue" for a shape the tool simply cannot handle is the part worth fixing.

**F2. A gated computation whose two arms rejoin.** **[bug/limitation]** Rust shape:
`if gate { Ok(x) } else { let y = state_touching(…); Ok(y) }`, whose result is then
matched.  *"Could not match the contexts"*.  Factoring the gate into a `Result<bool>` does
**not** help — the *join* is the problem, not the borrow's scope.  Fix: two tail calls, each
arm a whole function returning the final result, nothing joining; the price is the result
expression written twice.  Five witnesses: #18 (`infer_app_io`), #23 (three), #25
(`check_iota_rule_fire`).  We ended up applying it prophylactically — "a long `do` block with
a state-touching call in the middle is split at that call" (#24) — a real cost in the
readability of the port.

**F3. A `&mut`-threaded `match` arm that ends in a branch.** **[bug]** Rust shape: a
memoized walk, `match e { App(f,a) => { let b1 = go(memo,f); let b2 = go(memo,a); b1 && b2
} … }` followed by `memo.insert(…)` — `&&` short-circuits, so the arm ends in two borrow
contexts that merge with the other arms at the insert.  Rewriting `&&` as an `if` nest does
not help.  Fix (#24): a helper `bool_and(b1, b2)`, so the arm is one call; where the Lean
*short-circuits* and `bool_and` would change memo policy, lift the whole branching arm into
a one-line callee instead (#26, twelve of them).  Rule: **a memoized walk's arm must end in
a call or a constructor, never in a branch.**  Applied a priori, this is why #26 got zero
errors on ~1 000 lines of `&mut`-threaded walks.  Cost: the lifted callees genuinely join
their walk's SCC, taking `Funs.lean` from 8 `mutual` blocks to 14.

**F4. `Option<&T>`.** **[limitation, honestly reported]** `fn f(r: Option<&BlockRename>)`
gives *"Nested borrows are not supported yet"*.  Fix: two monomorphic functions (#25).

**F5. Internal error in `simplify_let_branching`.** **[bug]** `let rm = <a match returning
a tuple>; if rm.0 { … }` in a by-value-threaded memo walk (#30).  Fix: a tail call to a
function taking the two components as separate parameters.

**F6. A trait impl mutually recursive with a function.** **[limitation]** *"mixed-recursive
declaration groups"*, first hit in the `spikes/rc-fuel` spike (#1) — also triggered by
`#[derive(Debug)]` on a recursive type, whose impl joins the type's recursion group.  This
decided a whole design: con-leche's checker is written against a record of closures (a
"knot"), and the obvious Rust rendering — bodies generic over a `CoreFns` trait, the memo
wrappers implementing it — is *ruled out*.  We tied the knot textually instead (bodies call
the wrapper functions by name), which works, but a tool that accepted trait-in-recursion
would have let us mirror the source more closely.

**F7. `&'static str` in a data type.** **[bug]** `enum CheckError { Invalid(&'static str) }`
translates as a *type* (`Str → Err`) but Aeneas fails to build the **constructor**: *"There
should be no bottoms in the value"*, and the constructor comes out `sorry` (#14, measured
in a throwaway crate).  We represent every string in the core as `Vec<u32>` code points.

### 2.2 External holes we did not want, and how each was avoided

Our standing gate is that `*External_Template.lean` contains **exactly one type and four
functions** — the `Rc` model.  Four constructs quietly tried to add a fifth; each is a
missing std model.  **[limitation]** throughout.

| construct | hole emitted | our replacement | task |
|---|---|---|---|
| `String::from("…")` / `String::new()` | `alloc.string.String…from`, `…String.new` | `Vec<u32>` code points from a `const [u32; N]` | #14 |
| `Vec::is_empty` | `alloc.vec.Vec.is_empty` | `xs.len() == 0` | #18 |
| `vec![65, 66, 67]` | `core::mem::maybe_uninit::MaybeUninit` (the macro expands through it) | `const S: [u32; N]` + a slice walk | #24 |
| `Rc<T>` (no model at all) | four axioms | `@[reducible] def Rc T := T`, `new`/`deref`/`clone` = `ok x`, `ptr_eq` = `ok false` | #1, #4 |

Other std gaps we designed around rather than modelled: `Vec` has no `pop`, `truncate`,
`remove` or `toList` (so our bignum's normalisation *copies*, and our hash map's buckets are an
`AList` enum rather than `Vec<Vec<_>>` — #6, #7); `usize::next_power_of_two` is not modelled (a
fuel-carrying doubling recursion instead — #7); `Ord`/`max` on `UInt64` is out of subset (#11).
`Vec::clone`, `wrapping_add`/`wrapping_mul`, `overflowing_add`/`overflowing_sub`,
`core::mem::replace` and the scalar casts *are* modelled and cost nothing.

A pleasant negative result: con-leche's structural-equality memo is keyed by **addresses**,
which Aeneas cannot model, and we budgeted a fifth, opaque hole for it.  We did not need one:
keying by the two nodes' stored hash words and verifying a candidate by `ptr_eq` (which the
model answers `false`) puts the whole memo inside the subset as ordinary verified Rust — the
model writes the table and never reads it (#30, #38).  So `ptr_eq`-as-`false` is enough to
model a real pointer-keyed cache.

### 2.3 Charon findings

**F8. `--dest` / `--dest-file` resolves a relative path against the cargo *workspace*
root**, not the crate directory, and then **silently writes nothing where you asked**.
**[bug]** Fix: always pass an absolute path.  (`--dest` is also deprecated in favour of
`--dest-file`, which `--help` does not make obvious.)  #12

**F9. `charon cargo` is a no-op when cargo's cache is warm.** **[surprise]** The `.llbc` is
written only when rustc actually runs, so an extraction script must `cargo clean` (or touch
every source file) first — and the `.llbc` lands at the *workspace* root, following cargo.  A
trap for our `scripts/extract.sh`.  #7, #12

**F10. The `.llbc` is not byte-stable** — it records the absolute output path, so the same
crate extracted to two directories gives two different `.llbc`s.  **[surprise]** The *Lean* is
byte-identical, including from a different working directory, so our freshness gate diffs the
Lean and never the `.llbc`.  #12

**F11. Charon expands short-circuits and wildcards multiplicatively.** **[surprise, but the
dominant size and proof-cost driver]** `if a && b && c` becomes a four-way `if` nest with the
`else` branch duplicated three times; a single `_ => false` arm in a ten-constructor pairwise
`match` becomes 90 explicit `ok false` arms (78 Rust lines → 181 Lean lines).  A 5×5 `match`
is 25 arms in the model and 25 cases in the proof; two 10×10 tables are 52 % of one of our
proof files (#20).  Our style rule is to write the `if` nest explicitly so the shape is
predictable, but the duplication is not avoidable from the Rust side.  #3, #5, #11, #17, #20,
#26.  One mitigation that worked: factoring a constructor-pair match into its own function
*halved* the generated Lean for `beq`, because Aeneas otherwise duplicates the whole match
once per branch of the enclosing `if` (#30).

**F12. Charon OOMs on one large generated function.** **[bug/limitation]** We tried
encoding con-leche's Nat-op pin sets as generated Rust: one `fn(...) -> Vec<Expr>` with
**20 183** `let`-bound smart-constructor calls (21 920 lines, 1.48 MB).  `rustc` needs
`RUST_MIN_STACK=256M` to avoid SIGSEGV and then takes 73 s; `charon cargo` is **SIGKILLed
(OOM) after ~30 s at both 128 MB and 512 MB `RUST_MIN_STACK`, on a 125 GB / 96-core
machine**.  Aeneas was never reached.  Our fallback estimate was "split into functions of
≤ 1 500 nodes"; in the end the pin sets became runtime data.  A 192-node table of the same
shape (796 lines) costs +1 s of Charon+Aeneas and +0.3 s of Lean elaboration, i.e. it is
free at that size.  #22

### 2.4 Naming and packaging

**F13. Aeneas prints every reference unqualified inside the crate's Lean namespace, so a
Rust local shadows a module.** **[bug]** A field or parameter named `env`, `name` or `expr`
made `env.Env.find` elaborate as a *projection off the parameter* `env`.  Fix: nest every
Rust module one level (`kernel::name`, `cached::state_c`, `ron::nat`) so that every
generated reference starts with a segment no local is ever called.  **Aeneas could qualify
with `_root_` or with the namespace it was given.**  #14, `DESIGN.md` §3.6

**F14. Two copies of a hand-written external model cannot coexist in one Lean import
graph.** **[limitation]** `alloc.rc.Rc` is a top-level name — it has to be, since generated
code refers to it unqualified from inside its own namespace — so importing two extracted
crates that each carry their own `Rc` model gives `environment already contains
'alloc.rc.Rc'`.  Fix: a second `lean_lib` root with a disjoint import graph.  Any project
that extracts two crates hits this.  #12

**F15. `-subdir` is exactly right and we nearly missed it.** **[surprise, positive]**
`-dest proof -subdir ConRon/Generated` sets both the output path *and* the import prefix,
so no `sed` of import lines is needed; `-namespace` is a separate knob for the Lean
namespace.  Aeneas keeps the Rust module path as the definition-name prefix and does not
capitalise it, so `kernel::level::leq_core` becomes
`ConRon.Generated.kernel.level.leq_core` — which is what made our proof tier survive a
module reorganisation by changing *one `open` line per file* (#17).  Worth documenting more
prominently.  #12

### 2.5 Translation quality, for calibration

* **Zero iterations on six modules** written to the subset (#3, #6, #7, #9, #11, #13); across
  the whole port Charon failed exactly never (except F12), Aeneas 18 times in 42k lines.
* **`&mut` parameters become threaded returns**, precisely con-leche's own `StateT CState`
  shape — the generated signatures are the source's, not an artefact (#13, #18).  Region-
  parameterised dictionary structs (our stand-in for a Lean function argument) translate with
  no complaint, five of them (#13, #25); so do tuples, private items, erased `Prop` fields and
  `Unit` map values (#6, #9, #26).
* **The SCC decomposition is correct and informative.**  Aeneas put our checker core in one
  84-function `mutual` block and `annotate` in a separate 5-function one — a *fact about
  con-leche* (nothing in the reduction/inference/equality cycle calls `annotate`) we learned
  from the output.  Nothing new ever joined the big knot (#18, #23, #25, #26).
* Aeneas's tutorial hash map (`tests/src/hashmap.rs` + `tests/lean/Hashmap/Properties.lean`)
  was the most useful document we had — as a **specification** (the `al_v` / `slot_t_inv`
  strategy transferred completely), not as a proof library (§3.3).  #7, #16

## 3. Lean-library findings

### 3.1 The 4.33 patch, and the two `backward.*` options

The Aeneas Lean library builds on `leanprover/lean4:v4.33.0` with Mathlib `v4.33.0` after a
**375-line patch to ten files** (`spikes/toolchain/aeneas-433.patch`, against 505b6ca3).
Clean rebuild of the package: 146 s, 2 037 jobs, Mathlib from the olean cache.  The patch
is:

* **two `leanOptions`** in `lakefile.lean` — `backward.isDefEq.respectTransparency := false`
  (4.33 made `isDefEq` respect transparency for implicit arguments, which stopped hundreds
  of `simp`/`rfl`/`rw` steps over the semireducible `Result`/`Post`/`CoIndN` from closing;
  the flag restores every one with **zero proof edits**) and `backward.do.legacy := true`
  (one `do` block in `Step.lean`);
* six genuine API moves: `Lean.Elab.Tactic.BVDecide.Frontend.*` → `Lean.Meta.Tactic.BVDecide.*`
  with three getters now private (needing `open private … from`), one `Option` coercion in
  `AeneasMeta/Simp`, the `NPow`/`Monoid.toNPow` class change in `ReduceZMod`, three name
  collisions with new core `Array`/`Vector` lemmas (`getElem!_set!_ne`, `getElem_set!`,
  `getElem_set!_ne` — renamed with a prime, and the `simp_lists` calls given explicit lemmas),
  and two `#guard_msgs` texts that gained a "Hint:" line.

Mathlib is load-bearing for the library (`Data.BitVec`, `ZMod`, ordered-algebra lemmas), not
only for its tactics.  Upstream state at the time: the last toolchain bump was to v4.31.0
(2026-07-06); **PR AeneasVerif/aeneas#1283 "Upgrade to lean 4.33.1"** (opened 2026-08-22, 58
files, proper proof fixes rather than the `backward.*` flags) was open but stale and
conflicting with master.  We carry the patch and will switch when #1283 or a successor lands.
If useful, the patch is a mechanical 10-file stopgap that gets 4.33 working today, and its six
API moves are probably a subset of what #1283 already does.

**The trap the two options set, and it cost us real work.** **[bug]** The `leanOptions` are
the **`aeneas` package's**, so they do **not** reach a downstream project.  Without them,
`step` cannot apply a single `@[step]` lemma — *"could not find a local assumption or a
theorem to apply"*, even on a verbatim copy of Aeneas's own `Step/Tests` examples, which
pass inside the Aeneas package.  The underlying symptom is a `Post α` vs `α → Prop`
mismatch under `implicit` transparency; setting the two options per file makes `step` work
immediately.  **Consequence: every proof we wrote before task #22 is a hand-written
`simp`/`obtain` script and contains no `⦃ ⦄` at all, because the project's main proof tactic
had been silently unavailable for eight tasks.**  If the flags are load-bearing for `step`,
they belong in whatever a downstream `require` inherits — or `step` should diagnose the
transparency mismatch rather than reporting "no lemma applies".  #2, #22

### 3.2 `Result` is an `ITree`, so a closed term does not evaluate

**[limitation, and the one that changed a design decision]** We needed
`absBasisDecls k = ok (ConLeche.BasisKind.declsA k)` for a 192-node generated table.  In this
version `Result α` is `ITree RustEffect α` (`Aeneas/Std/Primitives.lean:81`), its `bind` is
`ITree.bind` — a `partial_fixpoint` over a CCPO (`Aeneas/Data/Coinductive/ITree.lean:160`) —
`ITree.cases` is a tactic-built proof term, and `alloc.vec.Vec.push` is `@[irreducible]`.
Measured on a **two-declaration** block: `rfl` fails in 1.3 s ("not definitionally equal"), on
the `Result.match` form too; `decide` has no instance (`Result` has no `DecidableEq`); and full
`simp` with the call graph unfolded **diverges** at 2 000 000 heartbeats and 20 000 000 simp
steps (looping-`simp` warnings on the index recursions, then a `whnf` timeout).
`bind (ok x) f = f x` is a `simp` lemma, never a reduction.  With the `backward.*` options set,
`step` does the job: a specification tier of 40 `⦃ ⦄` lemmas for the smart constructors
(`unfold f; step*`, one line each), then one `step` per interned node, then one `simp_all` —
631 lines, 66 s to elaborate.

The downstream consequence is larger than the tactic cost.  The same obstruction is why we
could not discharge "this embedded data table abstracts to con-leche's value" for a 20 183-node
table read at runtime, and therefore why that table is *unverified driver data* rather than part
of the verified core.  **A way to evaluate a closed `Result` term — `DecidableEq` on `Result`, a
`norm_result`-style evaluator, or a non-`ITree` `Result` for the first-order fragment — would
move that boundary.**  #22

### 3.3 `⦃ ⦄`/`step` and forward refinement are two different proof styles

**[surprise]** Our lemmas have the shape *exact result on success*:
`h : rust_fn x = ok y ⊢ lean_fn (abs x) = abs y`.  That is forward reasoning from a
hypothesis; `step` wants a `⦃ ⦄` goal.  So `step` was never usable for the refinement tier
even once the flags were set, and our bridge is `WP.spec_imp_exists`, which turns a `⦃ ⦄`
spec (`Vec.index_usize_spec`, `Vec.push_spec`, `Usize.add_spec`) into the forward
`∃ y, f x = ok y ∧ P y` form.  We need the `spec` lemmas only as a source of "this call
succeeds and returns *that*".  Recorded at #5, re-confirmed at #16: the tutorial's proofs
are in the `⦃ ⦄`/`step`/`grind` idiom and **not one proof script transferred**, though the
strategy transferred completely.  A documented `spec`→forward-equation bridge — or a
`step`-like tactic that consumes an `= ok` hypothesis — would be worth a lot to anyone doing
refinement rather than verification-from-spec.

Related: `partial_fixpoint` definitions carry **no induction principle**, so every
structural refinement is an induction on the *argument* (we hand-rolled `Level.ind'` /
`Name.ind'`, 12 lines each) or on a `Nat` measure using the function's own `.eq_def`.  Our
17 index-carrying loop helpers are all one skeleton: induction on a fuel `d` with
`n.val - i.val ≤ d`.  We never needed `dspec` or admissibility reasoning anywhere (#5, #15,
#16, #22).

### 3.4 The tuple-`let` trap, and its escape

**[bug — worth a library lemma or an emitter change]** After one `bind_eq_ok_iff` rewrite, a
hypothesis about a `&mut`-carrying call reads `(let (a, index_mut_back) := p; …) = ok v`.
`simp only [bind_eq_ok_iff]`, `dsimp only`, `split`, `simp only [Function.uncurry]` and
`beta_reduce` **all fail**: the equation's LHS is the `let`, not the `bind`, and the
pattern-`let` Aeneas emits is not iota-reducible by any of them — only *definitionally*
reducible.  The escape, and the pattern to reuse: **apply the lemma as a term**,
`replace h := bind_eq_ok_iff.mp h`, because the *unifier* whnf's through the `let` where `simp`
will not.  Same trick for `Result.ok_injective h`; where several pattern-`let`s stack,
`have h2 : <the reduced form, spelled out> := h` works, since a matcher on a constructor is
definitionally the body.  The term form peels exactly **one** bind, where
`simp only [bind_eq_ok_iff]` peels all of them up to the first pattern-`let`.  About an hour
the first time, and it recurs in every `&mut`-carrying function.  #16

The same from the other side: **tuple-returning `core` intrinsics defeat `simp only`** (#15).
Charon turns `let (s, c) = x.overflowing_add(y)` into `bind e (fun p => match p with | (s, c)
=> …)`; the matcher's scrutinee is a *variable* and nothing reduces it.  Two escapes: unfold
the `UScalar` definition first (`Std.core.num.U64.overflowing_add`,
`Std.UScalar.overflowing_add`), so the pair becomes a literal constructor; or the
`replace h : <body> := h` ascription.  Our own recommendation became "prefer a `struct` return
over a Rust tuple in new code" — a real expressiveness tax.

### 3.5 Lemma gaps in the scalar model

All **[limitation]**, all cheap to fix upstream:

* **`UScalar.*_equiv` lemmas are stated over `(x + y).match`**, so `rw [h]` fails when
  `h : x * y = ok z` (the lemma is about `UScalar.mul x y`); `rw [show UScalar.mul x y = ok z
  from h]` fixes it.  And **`UScalar.div` has no `_equiv` at all** — only `div_bv_spec`, the
  existence direction; we proved `uscalar_div_eq` by hand via the `y.bv = 0` split.  #16
* **`Vec::push` can fail** (capacity), so our `push_eq_ok_iff` is an `iff` whose left conjunct
  is the capacity disjunction — keeping it an `iff` is what lets one `simp only` unfold a whole
  loop body.  The residual side goal is `3 < Usize.max`, which needs `Usize.bounds_eq` because
  `Usize.max` is platform-dependent and **`scalar_tac` does not case on it**.  #15, #22
* **Machine-word literals defeat `omega`.**  Five one-line `@[simp]` lemmas naming the `u64`
  literals' `.val` (`val_2_32`, `val_2_16`, …) were needed before `omega` would treat
  `h.val * (4294967296#u64).val` as linear rather than as a product of two unknowns.  Two hours
  of one task, the single most useful thing we learned about the scalar model, and they belong
  in the library.  #20
* `Aeneas.Std.lift` wrapping pure operations (`wrapping_mul`, `^^^`, `UScalar.cast`) needs its
  own `@[simp]` unfolding; `alloc.vec.Vec` has no `toList` (its list projection is `.val`, now
  our convention for every `Vec` refinement statement); and `have i1 := v.len; if …` hoists
  `Vec::len` into a `let_fun`, which **blocks `split`** — `simp only [] at h` first, hit in
  three separate tasks.  `#setup_aeneas_simps` was never needed.  #5, #15

### 3.6 `@[reducible]` is load-bearing on an external type alias

**[surprise — worth a line in the docs]** With the literal `def alloc.rc.Rc (T : Type) := T`,
`Types.lean` fails with `failed to generate `SizeOf` instance for `NameKind`: type mismatch`
for every mutually recursive node type behind the `Rc`.  The mutual inductive *itself* is
accepted — Lean unfolds the alias to find the recursive occurrence — but the automatic
`SizeOf` derivation will not, and builds an ill-typed instance.  `@[reducible] def` fixes it
with no other change (`abbrev` and a one-field `structure` work too).  This is the
**opposite** of the advice in Aeneas's own `Vec` (`Aeneas/Std/Vec.lean:22`, "we *do not* want
to mark `Vec` as reducible"): `Vec` wraps a `Slice` and positivity is the problem there,
whereas for an identity alias the reducibility is the point.  It pays off later, too:
`Rc<ConstantInfo>` inside a `Vec` and a `HashMap` abstracted exactly as `ConstantInfo` did,
so a substantial performance refactor needed **zero** proof changes (#34).  #4

### 3.7 Smaller Lean-side notes

* A **multi-field structure literal inside a `do` block inside a hypothesis type is a parse
  error** in this Lean (`unexpected identifier; expected '}'` at the last field), while the same
  literal at top level parses fine.  And `Result.ok_injective h : (old, X) = (old', m')` with
  `X` a structure literal: `congrArg Prod.fst` leaves an unreduced `(old, m').1` that `rw`
  cannot use — always give the projection a **type ascription**, forcing the defeq check.  #16
* Generated accessors are deref-then-project, so a `match` on one needs *both*
  `Expr._0._simpLemma_` **and** `ExprNode.kind._simpLemma_` before it reduces.  #20
* `lake build` of a project that `require`s the Aeneas library is **not** warning-free: the
  replayed library modules emit `linter.dupNamespace`, `linter.ambiguousOpen` and
  `linter.defProp`.  Our gate is therefore "every *con-ron* file elaborates with zero output
  under `lake env lean`".  Also: Lake puts *git* dependencies under the **root** package's
  `.lake/packages`, so a downstream project `require`ing a path copy of the Aeneas library
  clones and builds its **own** Mathlib beside it — symlinking `proof/.lake/packages` at the
  Aeneas copy's makes one checkout and one set of oleans serve both.  #4, #12
* Our whole model is **axiom-free**: the four `Rc` holes are `def`s, and every proof's
  `#print axioms` is exactly `[propext, Classical.choice, Quot.sound]`, nothing from the Aeneas
  library.  We pin that with `#guard_msgs in #print axioms` per file.  #4, #5, #15, #16, #20

### 3.8 A `&str` constant carries `decide +native` (task #43)

A Rust `const TEXT: &str = "…"` extracts to one Lean string literal
wrapped by the library's `toStr`, whose bound is discharged with
`decide +native`; `#print axioms` on the constant therefore lists the
native-decide axiom (`Lean.ofReduceBool`), before any proof touches it.
For a project that pins its axiom footprint this makes every string
constant unusable in a theorem statement.  A `b"…"` constant avoids it
but becomes a 532 456-element array literal (Aeneas 169 s, Lean out of
memory).  Separately, Lean's kernel reduces string literals
quadratically (27 s at 1 KB, >300 s at 8 KB), so a closed computation
over an embedded text of any real size is out of reach with or without
the axiom.  Ask: discharge `toStr`'s bound without `decide +native`
(a `by decide` with the length as a literal, or an `ofNat` proof term).

## 4. Scale numbers

Data points on a crate an order of magnitude larger than the test suite.  One machine (96
cores, 125 GB), Mathlib and Aeneas prebuilt.

| | |
|---|---|
| Rust, verified core | **41 523** lines, 1 395 functions, 2 022 Charon-visible items |
| generated Lean, committed | **52 574** lines — `Funs.lean` 51 665, `Types.lean` 736, hand-written externals 94, templates 79 |
| ratios | Lean → Rust 2.5× (#3); Rust → generated Lean 1.5×–3.7× per module, ≈1.3× overall |
| `.llbc` size | 33 MB at 8 600 generated lines → **179 MB** at 51 500 |
| `charon cargo --preset=aeneas` | 0.2 s at 1.4k generated lines → **3.9 s** at 51k |
| `aeneas -backend lean -split-files -loops-to-rec` | 1.1 s → **33 s** (self-reported 12.7 → 33.3 s); ~15 ms per function throughout, i.e. **linear** |
| `partial_fixpoint` definitions | **415** |
| `mutual` blocks | **14** in `Funs.lean`, 3 in `Types.lean`; largest is the checker knot, **84 functions / 6 379 lines** |
| external holes | **1 type + 4 functions**, unchanged from the first spike to 42k lines |
| Lean elaboration of `Funs.lean` at 3 318 lines | 2.57 s net = **0.77 ms/line** (profiler: import 0.93 s, "process pre-definitions" 0.21 s for 64 `partial_fixpoint`s, type checking 0.06 s) |
| … at 12 416 lines | 11.6 s = 0.94 ms/line |
| … at 51 665 lines | **101 s** = ~2.0 ms/line — mildly superlinear at this scale, and the 84-function knot is *still* not where the time goes |
| whole `proof/` `lake build` (2 115 jobs, con-leche + Aeneas replayed) | 179–324 s |
| per-file import tax (Aeneas + Mathlib oleans) | ≈1.2 s |

So **`partial_fixpoint` at scale was not the risk we feared**: our design doc listed "Lean
elaborating a `partial_fixpoint` mutual block much larger than 8 functions" as the project's
top risk, and an 84-function block elaborates inside a file whose cost is essentially linear
in its line count.  The per-file import tax is the larger practical cost.

Proof-tier ratios, for anyone estimating an Aeneas refinement proof: **11 557 lines of proof
for 123 `_refines` lemmas** so far.  Per Rust code line — **2.2** on a branchy pure module
(#5), **5.1** on a bignum (#15), **5.9** on our own hash map (#16: no upstream counterpart to
refine against, so it carries its own abstract theory), **5.3** on a module with a sealed
canonical representation (#17), **6.2** on `Expr` (#20).  The trend is an artefact of
**arity**, not depth: strip two 10×10 constructor tables from the `Expr` file and the rest is
3.0.  Our rule became *≈3 proof lines per Rust code line, plus ≈1 line per ordered pair of
constructors matched on two scrutinees at once* — i.e. F11's match expansion drives the proof
cost too.

## 5. What we would ask for upstream

In rough order of value to us:

1. **Qualified names in generated code** — `_root_.env.Env.find`, or qualification by the
   `-namespace` argument.  Today a Rust local named like a module silently shadows it, and the
   only defence is a naming convention in the *source* crate (F13, #14).
2. **An `Rc`/`Arc` builtin, modelled as `Box` already is.**  `new`, `deref`, `clone` are the
   same three `ok x` definitions as `Box`'s, and `ptr_eq` as `ok false` is sound for any client
   that treats it as a fast path (which then owes one reflexivity lemma per site).  We wrote
   all four by hand, and the `@[reducible]` requirement (§3.6) is a trap a builtin would
   remove.  A shared *module* for such models would also fix F14, provided the
   `@[rust_type]`/`@[rust_fun]` coverage check follows imports.
3. **A model for `Vec::is_empty`, `Vec::pop`/`truncate`, and `vec![…]`.**  `is_empty` is one
   line and we hit it immediately; `vec![]` dragging in `MaybeUninit` is a trap for every new
   user, since it is the *natural* spelling; `pop`/`truncate` shaped two of our data structures.
4. **A way to evaluate a closed `Result` term** — `DecidableEq` on `Result` for the first-order
   fragment, a `norm_result` evaluator, or a non-`ITree` `Result` where coinduction is not
   needed.  This decides whether a generated data table can be *proved* equal to a reference
   value or has to become untrusted runtime data (§3.2, #22).
5. **The `backward.*` options (or whatever replaces them) must reach downstream packages**, or
   `step` should diagnose the transparency mismatch instead of reporting "no lemma applies".
   Eight of our tasks were written without the project's main tactic and did not know it
   (§3.1, #22).
6. **Small library additions:** the `.val`-of-scalar-literal `simp` lemmas (#20), a
   `UScalar.div_equiv`, `*_equiv` stated over `= ok` rather than `.match`, and a documented
   `spec`→forward-equation bridge for refinement proofs (§3.3, §3.5).
7. **Better diagnostics for the borrow-join failures of §2.1** — one naming the join point and
   the loan still live would have saved most of the 18 fixes' debugging time.  And if the
   *shape* can be supported — an `if`/`match` inside a `&mut`-threaded arm whose branches
   rejoin — that is the single biggest expressiveness win available, because it is what forces
   the port to split functions and duplicate expressions.
