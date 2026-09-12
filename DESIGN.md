# con-ron — a Rust port of con-leche, proven to refine it

con-ron ("CON-leche, RON — the Rust one") is a port of the
[con-leche](https://github.com/leanprover/con-leche) Lean checker to Rust,
together with a Lean proof that the Rust program refines the Lean one: every
export the Rust checker accepts, con-leche's `checkDecls` accepts too, so
con-leche's main theorem (`model_exists` / `no_proof_of_False`) carries over
to the Rust binary — without the Lean runtime (reference counting, GMP, the
compiler's code generator) in the trusted base.

This document is the design record and the work log.  The opening sections
are kept current; the task log at the end is append-only.  It is maintained
by the agents that work on the project (the pattern is borrowed from
con-leche's `DESIGN.md`).

**Status (2026-09-12): design draft for discussion with the maintainer.  P0 is
done (spikes through Charon and Aeneas, the `proof/` project elaborating); P1
has started — `crates/con-ron-core` holds the first real module, `nat` (task
#6).**

## 1. The goal, precisely

Let `checkDecls : CheckMode → List DeclC → Except (CheckError × Nat) Env` be
con-leche's declaration fold (`ConLeche/Cached/Installed.lean`), the function
its main theorem is about.  The Rust crate `con-ron-core` has a function
`check_decls(ds: Vec<DeclC>) -> Result<Env, CheckError>` written to mirror it
line by line.  Aeneas translates that crate to a Lean model
`conron.check_decls : Vec DeclC → Result (core.result.Result Env CheckError)`.
A hand-written abstraction `abs` maps every Rust data type to its con-leche
counterpart (`abs : conron.Expr → ConLeche.Expr`, `abs : conron.DeclC →
ConLeche.DeclC`, `abs : conron.Env → ConLeche.Env`; it forgets machine-word
representations, `Vec` becomes `List`, the bignum becomes `Nat`).  The
theorems to prove are

```lean
theorem check_decls_refines (ds : Vec conron.DeclC) (env : conron.Env)
    (h : conron.check_decls ds = ok (.Ok env)) :
    ConLeche.checkDecls .verified (ds.toList.map abs) = .ok (abs env)

theorem conron.model_exists (V) [SetTheory V] … (h : conron.check_decls ds = ok (.Ok env)) :
    Nonempty (Model V (abs env))          -- from ConLeche.model_exists

theorem conron.no_proof_of_False … (h : conron.check_decls ds = ok (.Ok env)) :
    ¬ ∃ c ∈ (abs env).consts, c.toConstantVal.type = .const falseName []
```

**Accept-direction only.**  The refinement is one-directional, exactly like
con-leche's own cached-to-pure simulation: whatever Rust accepts, Lean
accepts.  The converse ("whatever Lean accepts, Rust accepts") is false in
principle (a `usize` overflow makes the Rust model fail where `Nat` does not)
and unnecessary for consistency; it is covered empirically by differential
testing against con-leche's fixture corpus and Mathlib.

**What is and is not covered**, mirroring con-leche's own list: the theorem is
about `check_decls` on an already-parsed list; the Rust parser, the frontend
rewrites (prelude, Nat-op reordering, projection rewrite, the mutual/nested
inductive modeller), the CLI, and the thread pool are outside it, as they are
in con-leche.  Porting them is required for a usable binary; proving them is
a cherry on top (§7, phase P4).

## 2. Why Aeneas (and what else was considered)

The proof must live in Lean and connect to con-leche's theorem, so the tool
must produce a *Lean model of the Rust program*.  Aeneas (with Charon) is the
only mature tool that does this:

* Rust → MIR → LLBC (Charon) → pure Lean (Aeneas).  Functions land in a
  `Result` monad (`ok` / `fail` for panics, overflow, out-of-bounds / `div`);
  `&mut` parameters become state in/out; recursion becomes `partial_fixpoint`
  (no termination proof required); the output reads like hand-written Lean
  (see `spikes/rc-fuel/lean/Funs.lean`).
* It is actively maintained (last commit 2026-09-08), ships a Nix flake that
  pins Charon and the Rust nightly, and its Lean library carries a proof
  toolkit (`step`, `spec` notation, `scalar_tac`, `dspec`/admissibility for
  `partial_fixpoint` induction).
* The Aeneas Lean backend is pinned to Lean v4.31.0 and depends on Mathlib;
  con-leche is on v4.33.0.  Reconciling the two toolchains is an open item
  (task #2 below).

Alternatives and why not:

| tool | verdict |
|---|---|
| **Verus / Creusot / Prusti / Kani** | prove Rust against specs in their own logic; no way to connect to con-leche's Lean theorem short of re-stating the whole set-theoretic model. |
| **hax** (Cryspen) | same architecture as Aeneas with an experimental Lean backend; less mature on `&mut` state and recursion; Aeneas is the safer bet.  Could be revisited if Aeneas hits a wall. |
| **CakeML** | the strongest trust story (verified compiler *and* runtime incl. bignums), but proofs are in HOL4; would mean redoing con-leche, not porting it. |
| **Lean → Rust extraction** | a Lean metaprogram emitting Rust from con-leche's definitions.  Cheap to build, but the extractor would be unverified and the output as trusted as the Lean compiler we are trying to escape. |
| **Port without proof** | differential testing only.  This is phase P1's deliverable anyway and the fallback if the proof effort stalls; it already buys implementation diversity. |

**What the Rust binary's trusted base becomes**: rustc + LLVM + the parts of
`std` we use (`Vec`, `Rc`, `String`), Charon, Aeneas and its hand-written
`std` models (`Vec`, scalars), our own three external models (§3.2), the
Lean kernel checking the proof, and the unverified Rust frontend.  Out: the
Lean runtime, GMP, Lean's compiler.  Aeneas itself is not verified (its
metatheory is on paper); the model-to-binary correspondence is a reviewed
claim, as the Lean-compiler correspondence is for con-leche.  The point is
diversity with a proof on each side, not a smaller absolute base.

## 3. Design decisions

### 3.1 Mirror the Lean code one-to-one

The Rust port is a *transliteration* of con-leche's implementation modules
(`ConLeche/Kernel/*`, `ConLeche/Cached/*`; about 12k lines on the hot path,
~19k with the inductive routes and pins).  One Rust module per Lean file,
functions in the same order with the same names (snake_case), each with a
doc comment naming its source (`ConLeche/Kernel/Core.lean:1234`).  The same
fuel parameters, decremented at the same points; the same memo tables with
the same keys, inserted and cleared at the same points (including the 32M
entry cap on `instC`); the same `CheckMode`; the same error kinds (message
strings need not match — the theorem never reads them).

Rationale: the proof of `f_refines` is then a functional induction that
follows both definitions in lock step, with no algorithmic reasoning — the
memo soundness, fuel agreement and everything hard is already proved on the
Lean side by con-leche's `Verify/Cached/*`.  Any deviation in memo behaviour
(a hit where Lean misses) would force us to redo that tier.  Deviations are
allowed only where they are *semantically transparent by a local lemma*
(§3.2, pointer fast paths).

**Cached, not pure — and why (maintainer's question, 2026-09-12).**  The
alternative was to port the *pure* fueled checker and prove whatever
caching the Rust does sound in the Rust world.  That decouples Rust
performance work from con-leche's memo policy, but it re-proves con-leche's
hardest tier (memo soundness at every fuel, the install/check phase split
with prefix views; ≈ 8–15k lines of genuinely hard proof) before the first
Rust-side theorem exists.  The cached port reuses that tier through the
exact-state relation `abs st' = lean st'` at the price of mirroring
con-leche's memo *policy* (tables, keys, flush points, the 32M cap) — a
Rust caching change that alters the hit/miss pattern must be mirrored
upstream.  What the constraint does **not** forbid, because the relation
is on abstract state: pointer fast paths (§3.2), hash-consing/interning
(structural equality O(1), a memo keyed by node id behaves exactly like a
structurally keyed one), arenas, non-atomic `Rc`, a better hash map,
parallel phase B.  What neither option allows is the C++ kernel's
address-keyed caches: Aeneas has no addresses, so such a cache cannot be
modeled at all; interning is the modelable substitute under both options.
So the pure port mostly buys policy freedom, a smaller prize than it looks.

**Keep the door open: bodies over wrappers.**  The pure checker
(`Kernel/Core.lean`) is written against a record of closures (`CoreFns`,
the "knot"); the cached checker ties it with memo wrappers
(`CoreFnsI`/`coreKnotI`, `memoEI`/`memoBI`).  The port keeps that split
*textually*, not parametrically: the bodies are ported from
`Kernel/Core.lean` as plain functions `whnf_core_body(fuel, st, fe, e)`
that call the *wrapper* functions by name, and the wrappers
(`whnf_core(fuel, …)`: fuel check, memo probe, call the body at
`fuel - 1`, memo insert) are ported from `Cached/CoreC.lean` into a
separate module — one mutually recursive block of plain functions.  A
trait-based knot (bodies generic over a `CoreFns` trait, the wrapper
struct implementing it) is ruled out: Aeneas rejects a function mutually
recursive with a trait implementation ("mixed-recursive declaration
groups", seen in the task #1 spike), and closures are out by §3.4.  A later move to
Rust-native caching is then one new wrapper layer plus a Rust-world proof
"wrappers refine the pure bodies", with the bodies, their lemmas and the
provenance untouched; the pure-level main theorem it needs
(`model_exists` for `checkDeclsPure`) is a small upstream addition, since
`no_proof_of_False_pure` already exists.  The refinement lemma for a
wrapper is stated against `(coreKnotI mode fe fuel).whnf` etc., which
unfolds one level per fuel step.

### 3.2 Terms are `Rc` trees, modeled as their contents

con-leche's terms are persistent trees with sharing (a DAG through the Lean
runtime's reference counting); every hot path relies on O(1) sharing.  The
options were an index arena (fully inside Aeneas's subset, but every lemma
then carries an arena and its monotonicity, and `abs` depends on state) or
`Rc<Node>` with a hand-written model.  Decision: **`Rc<Node>`**, with the
external models

```lean
@[reducible] def alloc.rc.Rc (T : Type) := T     -- TypesExternal.lean
def alloc.rc.Rc.new  (x : T) : Result (Rc T) := ok x
def alloc.rc.Rc.deref (x : Rc T) : Result T   := ok x
def alloc.rc.Rc.clone (x : Rc T) : Result (Rc T) := ok x
def alloc.rc.Rc.ptr_eq (a b : Rc T) : Result Bool := ok false
```

`@[reducible]` is load-bearing: without it Lean's automatic `SizeOf`
derivation for the mutually recursive node types does not unfold the alias
and fails (task #4).

The first four are the same model Aeneas already uses for `Box`; they are
faithful because the port never uses `Rc::get_mut`, `make_mut`, weak
pointers or interior mutability (a `grep` gate enforces this).

**`ptr_eq` is modeled as `false`**, so the model always takes the slow path.
The real program may take the fast path; the two agree iff every walk that
uses `ptr_eq` as a shortcut is *reflexive* (`walk a a = true`), which is
proved as an ordinary lemma about the model for each such walk.  This is
Lean's own `withPtrEq` discipline (`h : x = y → k () = true`), made
explicit.  con-leche's address-keyed structural-equality memo (`BeqMap`)
and the `beqBudget` are **not** ported initially: the Rust `beq` is
pointer-fast-path → data-word compare → structural descent.  If measurement
shows the pair memo is needed, it is added as one opaque function with a
one-paragraph trust argument (the memo stores only proven-equal pairs, so a
hit repeats a deterministic result).

The packed data word (`hash32 | bvarB | fvarB | hasLP`) is a stored field of
`Node`, computed by smart constructors exactly as con-leche's
`@[computed_field] data`.  `mixHash` is opaque in Lean, so the proofs never
see hash bits; `abs` forgets the word, and a hereditary invariant
`NodeWF` (the bound bits equal those of `abs e`) is what `looseBVarsBounded`
and friends need.  Hash bits only affect memo bucket placement, which the
abstract-map relation (§3.3) does not see.

### 3.3 Own hash map, own bignum

Aeneas has no model of `std::collections::HashMap` (and modeling std's
`Hasher` state machine is awkward) and none of arbitrary-precision integers.
Both are written in the crate and verified:

* `ron::HashMap<K, V>` — open addressing or chained buckets over `Vec`,
  with a `trait Hashable { fn hash64(&self) -> u64 }` (the stored hash for
  terms, names and levels) and `PartialEq`.  Spec: an abstract partial map
  (`Std.HashMap` on the Lean side, related by "same lookup function").
  The Aeneas tutorial's verified hash map is the template.
* `ron::Nat` — a single `Vec<u64>` of little-endian limbs, normalised (no
  trailing zero limb; `0` is the empty vector), **not** the
  `Small(u64) | Big(Vec<u64>)` enum this section first proposed: one
  representation means one algorithm and one induction per operation instead
  of four representation cases, and one invariant instead of two (task #6).
  Operations needed (`Kernel/Core.lean:628-655`): `pred, add, sub, mul, pow
  (exponent ≤ 2^24), div, mod, gcd, land, lor, xor, shiftLeft, shiftRight,
  beq, ble`.  Spec: `toNat : ron.Nat → Nat` is a homomorphism.  Shift-subtract
  long division (easy proof); Knuth D only if a profile demands it.  This
  discharges con-leche's "verified bignum" wish list item for the Rust side.

Indices that are `Nat` in con-leche but never large (`bvar i`, `fvar idx`,
`Name.num n`, level params, positions) are `u64`; `abs` casts, and an
overflow is a Rust failure, harmless for the accept-direction.  `Literal.natVal`
and the Nat-op fast path use `ron::Nat`.

Strings (`Name.str`, `Literal.strVal`) are stored as `Vec<u32>` code points
in the core (Aeneas's `String` support is thin and con-leche only needs
equality, hashing and `String.toList`/`Char.ofNat` for literal reduction);
`abs` rebuilds a Lean `String`.

### 3.4 Rust style rules (Aeneas-friendliness), enforced by a lint script

* No `#[derive(Debug)]` on the core types (mixed type/trait recursion
  groups); no closures; no `?` in the core (explicit `match` keeps the
  generated Lean shaped like con-leche's `do` blocks); no `loop`/`while`
  except in leaf helpers (Aeneas `-loops-to-rec`); no generic instantiated
  with `&mut`; no `unsafe`; no `std::collections`; no `Rc` API beyond
  `new/clone/deref/ptr_eq`; `&mut` only for the state parameter.
* Recursion carries the same explicit fuel as the Lean side.
* Errors: `enum CheckError { NotImplemented(..), Invalid(..), Internal(..) }`
  in `Result<T, CheckError>`; panics are never used for control flow.
* Small files (`-split-files`), one Lean file per Rust module; generated
  Lean is committed under `proof/Generated/` and regenerated by
  `scripts/extract.sh`, with a CI gate that the committed output is fresh.

### 3.5 The proof project layout

```
crates/con-ron-core/     the verified core (checkDecls and below)
  src/kernel/*.rs        one module per ConLeche/Kernel/*.lean
  src/cached/*.rs        one module per ConLeche/Cached/*.lean
  src/ron/*.rs           nat, hashmap — replacements for runtime primitives
crates/con-ron/          CLI, parser, frontend rewrites, thread pool
proof/                   Lake project: requires con-leche + aeneas (task #4)
  lakefile.toml          two path `require`s; `lean_lib ConRon` and a second
                         root `lean_lib ConRonSpike` (task #12)
  ConRon.lean            the library root, imports everything below
  ConRon/
    Generated.lean       the module root of the extracted crate
    Generated/           Aeneas output (committed, regenerated by
                         scripts/extract.sh; namespace `ConRon.Generated`)
      Types.lean         generated — never edit
      Funs.lean          generated — never edit
      TypesExternal.lean       hand-written: the `Rc` model of §3.2
      FunsExternal.lean        hand-written: `new`/`deref`/`clone`/`ptr_eq`
      *_Template.lean    regenerated statement of which holes exist; not
                         imported (they declare the same names as `axiom`s)
    Refine/              abstraction functions, the `*WF` invariants, and one
                         lemma per ported function (README.md fixes the
                         naming rule; Smoke.lean is the task-#12 smoke test)
    Main.lean            check_decls_refines, conron.no_proof_of_False
    Dump/                the `DeclC` dump of §3.6 (task #10)
    Spike/LevelName/     the task-#3 spike, elaborated (task #4), a *second*
                         library root: it carries its own copy of the `Rc`
                         model, and two top-level `alloc.rc.Rc` cannot live
                         in one import graph
vendor/con-leche         submodule, pinned (3e004805)
vendor/aeneas            submodule, pinned (505b6ca3) — same rev as flake.nix
_tmp/aeneas-lean/        gitignored: vendor/aeneas/backends/lean + the v4.33
                         patch, built; produced by setup-aeneas-lean.sh, and
                         `require`d by path from proof/
spikes/                  feasibility experiments, kept as evidence
scripts/                 gates.sh (run it before every commit), extract.sh,
                         setup-aeneas-lean.sh, lint-rust-style.sh,
                         provenance.py, dump-fixtures.sh, diff-test
```

**`scripts/gates.sh` is the one command every task runs before committing**
(task #12): `cargo build`, `cargo test`, `lint-rust-style.sh`,
`provenance.py check`, `extract.sh --check`, `cd proof && lake build`, one
OK/FAIL line each, stopping at the first failure.

Refinement lemma shape — **exact result on success** (task #5): a Rust
function that returns `ok y` computes *exactly* what the Lean function
computes on the abstracted inputs; nothing is claimed when Rust fails.
Exactness is needed because Boolean and `Option Bool` outcomes feed
branches on both sides; the accept-direction statement of §1 is a corollary
of exactness at every level.  Stored derived data (hash words) is governed
by a hereditary well-formedness predicate (`NameWF`, `LevelWF`, `NodeWF`),
under which `abs` is injective and `beq` is exact.  **Such a predicate is
written as an *inductive* one whose constructors are the port's own smart
constructors** (task #5): `NameWF.str : NameWF pre → StrWF s →
name.mk_str pre s = ok n → NameWF n`, and so on.  It says "this node is
what the smart constructor built", which pins the stored word to the
children without the proofs ever naming a hash formula, makes the
constructor-preservation lemmas literally the constructors, and gives
injectivity of `abs` from the fact that a smart constructor is a function.
The one extra clause is the one no equation supplies: every code point
stored in a `Str` node is a valid `Char` (`Nat.isValidChar`), without which
`absString` is not injective.  Forward reasoning from `ok`:

```lean
theorem whnf_refines (fuel st e st' r) (hwf : StateWF st)
    (h : conron.whnf fuel st e = ok (.Ok r, st')) :
    ((coreKnotI mode (abs fe) fuel).whnf (abs e)).run (abs st)
      = .ok (abs r, abs st') ∧ StateWF st'
```

proved by induction on `fuel` over the whole mutual block, inverting each
bind in the Rust model and rewriting the Lean side.

### 3.6 Differential testing before any proof

A Lean executable in `proof/` (importing con-leche's frontend) dumps the
parsed `List DeclC` of any export in a simple text format; the Rust core
reads it and runs `check_decls`.  Verdicts (and, for definitions, the stored
annotated terms) are compared against con-leche on its full fixture corpus
(`tests/e2e`, `tests/arena`, `tests/annot`; 348 streams) and on a Mathlib
export.  This decouples the core port from the Rust parser and catches port
mistakes at the function they happen in; a finer oracle (dumping
`whnf`/`infer` call pairs from con-leche) is added if debugging demands it.

**The tool is `lake exe con-ron-dump`** (task #10), root
`proof/ConRon/Dump/Main.lean`, with the writer in `ConRon/Dump/Write.lean`,
the Lean reader in `ConRon/Dump/Read.lean` and the format specified in
`proof/ConRon/Dump/FORMAT.md` (`con-ron-decls/1`: line-oriented text, one
dense id space per node kind so the term DAG is written once, in the spirit
of `lean4export`'s records).  It runs con-leche's frontend exactly as
`vendor/con-leche/Main.lean` does — `Frontend.builtinPreludeE` then
`Frontend.parseExportStreamD` with the in-process modeller on — writes the
dump, reads it back **in Lean**, and checks structural equality of the two
declaration lists, byte-identity of a re-dump, and agreement of
`checkDecls .verified` on both.  `scripts/dump-fixtures.sh` sweeps the whole
corpus and additionally compares each verdict against con-leche's pinned
`tests/{arena,e2e,annot}-expected.txt`.

**Module nesting is load-bearing (task #14 follow-up).**  Aeneas prints
every reference unqualified inside the crate's Lean namespace, so a Rust
*local* — a field or a parameter — named like a module (`env`, `name`,
`expr`) shadows the module in the generated Lean (`env.Env.find` became a
projection off the parameter `env`).  Nesting the modules one level
(`kernel::name`, `cached::state_c`, `ron::nat`) makes every generated
reference start with a segment no local is ever called, and mirrors
con-leche's directory tree.  Generated names are therefore
`ConRon.Generated.kernel.level.leq_core`; the refinement tier follows
(`ConRon/Refine/README.md`).  Worth an upstream report: Aeneas could
qualify with `_root_` or the namespace.

### 3.7 Provenance: keeping the port in sync with con-leche

con-leche keeps moving.  The proofs catch drift eventually — a changed
Lean function breaks its `_refines` lemma — but only for the verified
core, only after a full proof build, and without saying *which* Rust
function to look at.  The port therefore carries its own provenance,
checked by a gate in the spirit of con-leche's `tests/overview-links.sh`:
the cited text becomes a committed fact, and a change to it is an alert
naming the consumer.

**The annotation.**  Every Rust item Charon sees (`fn`, `struct`, `enum`,
`impl` block, `const`) carries at least one doc line of the form

```
/// con-leche: ConLeche/Kernel/Level.lean:82-89 leqCore
```

— the file, the line range at the pinned submodule commit, and the Lean
declaration the range holds.  Several lines are allowed when a Rust item merges or splits Lean ones
(a `*_from` index helper cites the `List` recursion it replaces; the
four-function `imax_rules` cascade all cite `imaxRules`).  A Rust item
with no Lean counterpart says so and why:

```
/// con-leche: none — replaces the runtime's `Nat`; spec in proof/…/NatSpec.lean
```

Deliberate deviations from the cited code (task #3's seven patterns, a
closed knot, an omitted pair memo) are described in the doc comment
below the citation, so a reader of the Rust sees the delta without
opening the Lean.

**The gate**, `scripts/provenance.py`, is a pure source-tree check
(milliseconds, no build) with three modes:

* `check` — every annotation's range exists in `vendor/con-leche` at the
  pinned commit and its first non-attribute line declares the named Lean
  constant; every Charon-visible Rust item in `crates/*/src` (outside
  `#[cfg(test)]`) carries an annotation; and no `CHANGED` marker line
  (below) is left in the tree.  Fails naming the offenders.  Runs in CI
  and before every commit of a port task.
* `update [--old <commit>]` — the bump workflow.  After the submodule
  moves, for every annotation: take the cited text at the *old* pin
  (`git show <old>:<path>` at the cited range) and the block located by
  name in the file at the *new* pin (a top-level block from its
  `def`/`theorem`/`inductive`/`structure`/`instance`/… keyword,
  attributes included, to the next column-0 declaration).  Identical →
  rewrite the line numbers in place, silently, and report *moved*.
  Different → rewrite the range to the located block, insert right after
  the citation the marker line

  ```
  /// con-leche: CHANGED since <oldcommit> — re-port, re-test, re-prove <item>_refines, then delete this line
  ```

  and print the unified diff old→new headed `CHANGED <path> <decl> →
  re-port <rust item>, re-run differential tests, re-prove <rust
  item>_refines`.  Not found → *gone*, with a marker too.  `<old>`
  defaults to the submodule commit recorded in `HEAD` when the bump is
  uncommitted, else must be given.

  Reconciliation is deleting the marker line — there is no `accept`
  mode.  `check` stays red while any marker remains, so a bump cannot
  land half-reconciled.
* `coverage` — the port ledger: every top-level definition in con-leche's
  implementation modules (`ConLeche/Kernel/**`, `ConLeche/Cached/**`;
  later `Frontend/**`, `Main.lean`) that no annotation cites, per file
  with counts, and the total covered/uncovered.  Printed, not committed
  (it churns); task-log entries quote the totals as progress.

**Why no hashes.**  The pin is the single source of truth: a citation is
`(path, range, name)` and the text it denotes is fixed by the submodule
commit; `update` diffs pins, and the only churn is line numbers on moved
items, rewritten mechanically, plus marker lines exactly where work is
owed.

**What it does not do.**  It does not judge whether the port still
matches — that is the differential tests and the proofs; it says *what
moved and what changed*, and for the unverified frontend it is the only
sync signal there is.

**Implementation notes** (task #8).  `--roots DIR…` overrides the
default `crates/con-ron-core/src spikes/level-name/src`; the default
list is a constant at the top of the script.  Three details the design
above leaves open, settled by the implementation:

* *Name resolution.*  A citation's `<decl>` may be spelled with or
  without the namespace the Lean file opens (`Level.leqCore` ≍
  `leqCore`), and a `where` clause is cited as the dotted child of its
  parent (`subst.go` resolves to `subst`'s block, which contains it).
  The locator therefore runs three passes — exact, then namespace-suffix,
  then parent-prefix — rather than one loose match: a single pass lets
  `Name.beqPtr` bind to the `Name` inductive, which is wrong and was the
  first bug the spike conversion found.
* *Block boundaries.*  Beyond the design's stopper list, `mutual`,
  `open`, `variable`, `attribute` and `/-!` at column 0 also end a
  block; trailing blank lines are trimmed.  `instance : C T := …` has no
  name to cite, so the decl `_` skips the name check (the range still
  pins the text).
* *What counts as a Rust item.*  Items nested inside a function body
  belong to that function and are not separately required to cite;
  `#[cfg(test)]` and `mod tests` blocks are skipped by brace depth, as
  in `scripts/lint-rust-style.sh`.
* *`update` is idempotent.*  Its comparison is "old pin's cited range vs
  new pin's located block", so a second run for the same bump would see
  ranges it has already rewritten.  When that comparison fails it falls
  back to the old pin's block *for the same declaration*; that can only
  turn a spurious `CHANGED` into a `MOVED` (if the text really changed,
  neither text matches), and it never adds a second marker to a citation
  that already carries one.

## 4. Sizing

From the census of con-leche at 3e004805 (implementation only):

| group | Lean lines |
|---|---|
| `Kernel/` core (`Core`, `ExprOps`, `PropWhen`, `Level`, …) | 7 639 |
| `Kernel/` types (`Expr`, `Env`, `FEnv`, `Name`) | 2 052 |
| `Kernel/` declaration checking | 2 662 |
| `Kernel/Inductives/` (native + struct + sum) | 3 983 |
| `Kernel/Basis*`, Nat-op pin sets | 1 215 |
| `Cached/` | 4 653 |
| **verified core total** | **≈ 22 000** |
| `Frontend/` implementation (parser, InModel, NatOpGround, ProjRec, Prelude) | ≈ 8 600 |
| `Main.lean` | 1 183 |

Expect ~1.2× that in Rust, ~2–3× in generated Lean, and a proof tier of the
same order as con-leche's `Verify/Cached/*` (≈ 20k lines).

**Measured (P0, tasks #3–#10):** Lean → Rust 2.5×, Rust → generated Lean
2.6×; Charon + Aeneas about 1.5 s per 1 000 Rust lines, zero iterations
on four crates written to §3.4; Lean elaboration of generated code ≈ 1 ms
per line; proofs ≈ 2.2 lines per Rust line, i.e. 20–60 lines per
single-scrutinee function and 60–270 for two-scrutinee matches (task #5),
so **8–20k proof lines** for the 22k-line core, tail risk in `defEq` and
the inductive routes.  The build-time
pins (basis blocks after annotation, Nat-op pin sets from `pins/*.json`)
become static Rust tables generated by a Lean script from con-leche's own
values.

## 5. Plan

Each phase ends at a gate; nothing in a later phase starts before the gate
is green.  "Fable" tasks are design/spec/theorem-statement work; everything
marked "Opus" is mechanical and delegated.

**P0 — infrastructure and spikes** (Fable; **done 2026-09-12**, tasks #1–#5, #8)
1. flake + direnv devshell with Charon's nightly, Charon, Aeneas.  ✔
2. Spike: `Rc` tree, fuel recursion, `&mut` state through Charon/Aeneas.  ✔
3. Spike: Aeneas Lean library on v4.33.0 — builds with an 80-line patch (task #2).  ✔
4. Spike: the `proof/` project, the `Rc` models, the lemma shape on the
   `Name`/`Level` port — 27 lemmas proved, axiom census pinned (tasks #4, #5).  ✔
5. Spike: scale — `Name`+`Level` through Charon/Aeneas with numbers (task #3).  ✔
6. The provenance gate (task #8).  ✔
   Gate: met; numbers in §4.

**P1 — the verified core in Rust, differentially tested** (Opus, parallel
by module once types exist; **in progress**)
1. `ron::Nat`, `ron::HashMap` with unit tests (tasks #6, #7).  ✔
2. Types: `Name`, `Level`, `PropWhen`, `Expr`/`Node` + smart constructors,
   `Literal`, `Env`/`FEnv`/`ConstantInfo`, `CState`, `DeclC`.
3. `ExprOps`, `Level` ops, `PropWhen` ops.
4. `Core` (whnfCore/whnf/infer/defeq/annotate knot) + `Cached/CoreC` memos.
5. `Checker`/`DeclCheck`, `StdAxioms`, `TrustAxioms`, Nat-op pins, basis
   tables (generated), `Inductives/*`, `Installed` (`check_decls`).
6. `con-ron-dump` (Lean, task #10 ✔) + Rust reader (task #19 ✔,
   `crates/con-ron-dump`); differential test runner.
   Gate: every fixture verdict identical to con-leche; Mathlib export
   accepted; style lint clean.

**P2 — extraction** (Opus; **done 2026-09-12**, task #12)
1. `scripts/extract.sh`; `proof/` Lake project builds the generated Lean
   with the `Rc` models; freshness gate (`extract.sh --check`) in
   `scripts/gates.sh`.  ✔
   Gate: met — `lake build` of `ConRon.Generated` green and warning-free at
   3 615 generated lines; timings in the task-#12 log.  The pipeline reruns
   at every crate change and its gate is part of `scripts/gates.sh`, so P2
   stays green rather than being a one-off.

**P3 — the refinement proof** (Fable states; Opus proves, bottom-up)
1. `abs` functions, `NodeWF`, `StateWF`; `Nat`/`HashMap` specs.
2. Reflexivity lemmas for every `ptr_eq` site.
3. `ExprOps`, `Level`, `PropWhen` refinements.
4. The knot: mutual induction on fuel.
5. Declaration checking, inductives, pins, `check_decls_refines`.
6. `conron.model_exists`, `conron.no_proof_of_False`; axiom pin
   (`#print axioms` = the three standard ones + nothing from Aeneas beyond
   its own sorry-free library).
   Gate: main theorems sorry-free; axiom census pinned.

**P4 — cherries** (Opus)
1. Rust parser (NDJSON, streaming), prelude, Nat-op reordering, projection
   rewrite, in-process inductive modeller, CLI with con-leche's exit codes,
   thread pool for the check phase.
2. Perf comparison against con-leche and the official kernel (PERF.md).
3. Optional: parser refinement against con-leche's naive reference parser.

## 6. Risks

1. **Scale of Aeneas.**  Nothing this size (~25k Rust lines, a mutual block
   of hundreds of functions) has been through it; translation blow-ups or
   slow Lean elaboration of `partial_fixpoint` blocks are plausible.
   Mitigation: P0.5 measures early; small files; the knot can be split into
   several mutual blocks at fuel boundaries if needed.
2. **Toolchain reconciliation** (Aeneas lib on 4.31 + Mathlib vs con-leche
   on 4.33).  Mitigation: P0.3; worst case pin con-leche's proof project to
   whichever toolchain Aeneas supports and rebuild con-leche there.
3. **Proof volume.**  Same order as con-leche's cached tier; the one-to-one
   mirroring rule is what keeps it mechanical.  Watch for places where the
   Lean code's structure is not expressible in Aeneas's subset (closures,
   monad-polymorphic bodies) and record each deviation with its lemma.
4. **Performance of the Rust port** (own hash map, `Rc` traffic, no
   pair-memo for `beq`).  Mitigation: measure on Mathlib in P1; the
   optimisations that break mirroring are opt-in and documented.
5. **Aeneas/Charon bugs** surfacing mid-port.  Mitigation: keep to the
   plainest subset; report upstream; keep spikes as regression tests.

## 7. Iteration protocol

* Work in small tasks numbered `#N`; each lands with its tests (Rust unit
  tests, differential fixtures, or Lean lemmas) and a section appended to
  the task log below: what was decided, what was measured, what is left.
* Design decisions go in §3 (kept current); the log keeps history.
* `cargo build` and `cargo test` warning-free; `scripts/lint-rust-style.sh`
  clean; `proof/` builds sorry-free on master (no `sorry`, no new axioms
  beyond Aeneas's library, whose axiom footprint is pinned).
* Commit often.  The maintainer pushes and opens PRs (see `CLAUDE.md`).
* Fable designs and states theorems and reviews; Opus agents port, extract,
  prove and measure.  Delegate anything mechanical.
* Large artifacts (exports, builds) go to `_tmp/` (gitignored).

## Task log

### Task #1 — Feasibility, design, infrastructure (2026-09-12, Fable)

* Surveyed con-leche (implementation ≈ 30k lines without the parser's
  equivalence proofs; hot path ≈ 12k) and Aeneas (Lean backend on v4.31.0 +
  Mathlib; `partial_fixpoint` recursion; no `Rc`/`HashMap`/bignum models;
  `-split-files`; `step`/`spec`/`dspec` toolkit).
* Built Charon and Aeneas from Aeneas's flake (from source, ~25 min on this
  machine); `flake.nix` consumes `aeneas`, `aeneas/charon#charon` and
  `aeneas/charon#rustToolchain` (nightly-2026-08-18).
* Spike `spikes/rc-fuel`: an `Rc<Node>` DAG with a packed data word, a
  fuel-indexed mutual recursion threading a `&mut Memo`, checked `u64`
  arithmetic.  First attempt failed on `#[derive(Debug)]` ("mixed-recursive
  declaration groups") and on a closure through `Option::and_then`; without
  those it translates completely (`spikes/rc-fuel/lean/`).  `Rc` surfaces as
  an external type with `new`, `deref`, `clone`, `ptr_eq` holes — the hook
  §3.2 builds on.
* Decisions §3.1–3.6 taken; plan §5.  Open: toolchain (task #2), lemma
  shape (task #3), scale numbers (task #4).

### Task #3 — Scale spike: `Name` and `Level` through Aeneas (2026-09-12, Opus)

P0.5 of §5: `ConLeche/Kernel/Name.lean`, the `Level` part of
`ConLeche/Kernel/Expr.lean` (lines 40-139) and `ConLeche/Kernel/Level.lean`
(lines 24-232) ported for real in the §3.1-§3.4 style, extracted, measured.
`spikes/level-name/`; generated Lean left in `spikes/level-name/lean/`
(not elaborated — the Aeneas Lean library is not built yet, task #2).

**Numbers.**

| | |
|---|---|
| Lean ported (raw / code lines) | 366 / 197 |
| Rust port `src/name.rs` + `src/level.rs` (raw / code) | 702 / 502 (**2.5×** the Lean) |
| Rust tests `src/lib.rs` (13 tests, not extracted) | 200 |
| generated `lean/Types.lean` | 122 |
| generated `lean/Funs.lean` | 1 354 (**2.6×** the Rust, 6.9× the Lean) |
| generated `lean/TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 |
| `charon cargo --preset=aeneas` wall | **0.20 s** (incl. the `cargo` rebuild) |
| `aeneas -backend lean -split-files -loops-to-rec` wall | **1.14 s** (0.96 s self-reported) |
| items translated | 63 transparent fns, 18 opaque, 4 trait decls, 4 trait impls |
| `partial_fixpoint` | **25** |
| `mutual` blocks | 1 in `Funs.lean` (8 fns: `leq_core`, `rest`, `imax_rules`, `by_cases_left/right`, `imax_rules_distrib`, `imax_rules_distrib_right`, `by_cases`; 313 lines), 2 in `Types.lean` (3 types each) |
| external holes | exactly the four `Rc` axioms of §3.2 — `new`, `clone`, `deref`, `ptr_eq`.  Nothing else is opaque. |

`cargo build`/`cargo test` warning-free, 13/13 green;
`scripts/lint-rust-style.sh spikes/level-name/src` clean.

**Charon and Aeneas both succeeded on the first run, with no iteration.**
That is the headline: the subset was known from `spikes/rc-fuel` (task #1) and
staying inside it was a matter of writing the port a certain way.  The
adjustments below are therefore *a-priori* transliteration choices, not
error-driven fixes; each is a place where the Lean cannot be written down
literally in Rust.

**Constructs that do not survive transliteration, and their replacements.**

1. **Nested constructor patterns through an `Rc`.**  `Level.imaxRules` matches
   `.imax _ (.param p)`; Rust cannot pattern-match through `Rc` (or through the
   `Level(Rc<LevelNode>)` newtype), and `if let` chains are not in edition 2021.
   Replaced by a predicate `is_imax_param` plus re-destructuring helpers.  The
   Lean arms also *interleave* the two scrutinees (`_, .imax _ (.param p)` comes
   before `.imax a (.imax x y), _`), so a single nested `match` would silently
   reorder them: `imaxRules` became a four-function cascade
   (`imax_rules` → `by_cases_left` / `by_cases_right` / `imax_rules_distrib` →
   `imax_rules_distrib_right`) that preserves the Lean arm order exactly.  The
   helpers' unreachable arms return `None`, which is Lean's own fall-through.
   This is the only structural deviation in the port.
2. **Recursion over a Lean `List`.**  `Vec` has no cons pattern; every
   list recursion became an index-carrying helper (`*_from(xs, i, …)`) with the
   public function as the `i = 0` wrapper: `str_hash`, `str_eq`, `contains`,
   `levels_have_param`, `levels_hash`, `subst.go`, `isEquivList`, `Name.nodup`.
3. **`do`-notation over `Option`** (`if ← leqCore …`) → an explicit three-way
   `match` on `None` / `Some(false)` / `Some(true)`.  §3.4 forbids `?`, and the
   explicit match is what keeps the generated Lean shaped like the source.
4. **Decidable equality against a literal constructor** (`ls = .zero`,
   `ls = .succ .zero`, `simplify l = .zero`) → constructor predicates
   `is_zero_kind` / `is_one_kind`; building the right-hand side would allocate.
5. **String literals in patterns** (`.str _ "_model"`, `.num (.str _ "proj") _`)
   → explicit code-point comparisons (`s.len() == 6 && s[0] == 95 && …`), since
   strings are `Vec<u32>` (§3.3) and the subset has no literal for that.
6. **`mixHash`** is Lean's runtime `lean_uint64_mix_hash`
   (`~/.elan/toolchains/…/include/lean/lean.h:2036`, a MurmurHash2 mix step),
   transliterated with `wrapping_mul`, which Aeneas models
   (`Std/Scalar/WrappingOps/Mul.lean`).  **`hash : String → UInt64`** could not
   be: `lean_string_hash` is only *declared* in the shipped header and hashes
   UTF-8 bytes, which `Vec<u32>` code points are not.  Ours is a `mix_hash` fold
   over code points.  Verdict-neutral by §3.2 (`mixHash` is opaque in the
   proofs, the hash guard in `beq` is provably redundant, and hash values only
   move memo entries between buckets) — but it means the Rust and Lean hash
   *values* differ, so no differential test may compare them.
7. **Ownership.**  Lean's value semantics vs Rust's: the port takes its tree
   arguments by shared reference and returns owned trees ("borrow in, own out"),
   with an explicit `dup` (= `Rc::clone`) wherever Lean returns a subterm
   (`subst.go`, `combining`).  A function cannot return a borrowed subterm
   because it lives behind the `Rc`.
8. `vec![x]` (a macro that expands through `box`) avoided in favour of
   `Vec::new()` + `push` (`name::singleton`, `level::singleton`).
9. **`&&` in a condition is expanded by Charon** into nested `if`s: `leq_core`'s
   `is_zero_kind(l) && diff >= 0` became a four-way `if` nest in `Funs.lean`,
   duplicating the `else` branch three times.  Harmless but noisy, and it grows
   multiplicatively with the number of conjuncts.

**Deliberately not ported** (recorded so the next task does not re-derive it):
`Name.ofLeanName` (frontend), `Name.toString` (error messages only — §3.1 says
strings need not match), `Level.zeronessOf` / `Level.substPW` (need `PropWhen`),
and everything from `Level.lean:234` on (`Expr.instantiateLevelParams`,
`Expr.allLevelParamsDefined` and its memoized twin — need `Expr`).

**Proposed additions to §3.4** (all exercised here):

* Every `List` recursion becomes `Vec` + an index-carrying `*_from` helper; the
  public function is the `i = 0` wrapper.  The refinement lemma is then an
  induction on `len - i`.
* Nested constructor patterns through an `Rc` become a predicate plus a
  re-destructuring helper.  When the Lean arms interleave two scrutinees, the
  cascade must preserve the Lean arm order, and each helper's impossible arms
  return the Lean fall-through value.
* Comparison against a literal constructor is a constructor predicate, never a
  rebuilt right-hand side.
* Lean string literals in patterns become explicit code-point tests.
* "Borrow in, own out", with an explicit `dup` for every `Rc::clone`.
* Prefer an explicit `if` nest over an `&&`/`||` chain wherever the Lean has a
  nest: Charon expands the short-circuit anyway, and the explicit form keeps the
  generated Lean aligned with the source.
* `#[cfg(test)]` modules are exempt from the style rules — Charon never sees
  them.  `scripts/lint-rust-style.sh` now stops at the first `#[cfg(test)]`, and
  its closure regex no longer fires on `||` (it required only *some* text
  between the bars; a closure has at least one parameter character).

**Assessment.**  Aeneas is at ~15 ms per function and produces Lean that reads
like the Rust (same names, same branch structure, `Result`-monadic binds).
Linear extrapolation of these ratios to the ≈22k-line verified core: ≈55k Rust
lines and ≈145k generated Lean lines, with Aeneas itself well under a minute —
so §6's risk 1 is not about Aeneas's throughput.  What is still untested is
Lean *elaborating* a `partial_fixpoint` mutual block much larger than the
8-function one here; that is task #2/#4's business, and the fallback (splitting
the knot at fuel boundaries, §6) stays on the table.

The port was mechanical.  Roughly 80% of it is a direct one-to-one rewrite; the
remaining 20% is the seven patterns above, each applied the same way every time.
A second agent given these rules should be able to port a module without design
decisions.

### Task #2 — Toolchain: the Aeneas Lean library on v4.33.0 (2026-09-12, Opus under Fable)

**Result: it builds** on `leanprover/lean4:v4.33.0` with Mathlib `v4.33.0`
after a ~80-line patch to ten files, kept at
`spikes/toolchain/aeneas-433.patch` (against `vendor/aeneas` at 505b6ca3,
`backends/lean/`).  Clean rebuild of the package: 146 s, 2037 jobs,
Mathlib from the olean cache (`~/.cache/mathlib` persists on this machine).

What the patch is: two `leanOptions` —
`backward.isDefEq.respectTransparency := false` (4.33 made `isDefEq`
respect transparency for implicit arguments, which stopped hundreds of
`simp`/`rfl`/`rw` steps over the semireducible `Result`/`Post`/`CoIndN`
from closing; the flag restores every one with zero proof edits) and
`backward.do.legacy := true` (one `do` block in `Step.lean`) — plus six
genuine API moves (`BVDecide` namespaces and now-private getters via
`open private`, one `Option` coercion, the `NPow` class in `ReduceZMod`,
three name collisions with new core `Array`/`Vector` lemmas, two
`#guard_msgs` texts).  Mathlib is load-bearing for the library
(`Data.BitVec`, `ZMod`, ordered-algebra lemmas), not only tactics, so it
stays.

Upstream: the last toolchain bump was to v4.31.0 (2026-07-06); PR
AeneasVerif/aeneas#1283 "Upgrade to lean 4.33.1" (opened 2026-08-22, 58
files, proper proof fixes instead of the `backward.*` flags) is open but
stale and conflicting with master.  **Decision:** stay on the pinned
Aeneas commit (translator and library must match) at con-leche's exact
toolchain v4.33.0, carry the patch, and switch to upstream when #1283 or
its successor lands.  The patched library is produced by
`scripts/setup-aeneas-lean.sh` (copy + `patch`) into a gitignored
location the proof project `require`s by path; a fork carrying the patch
would be the tidier long-term home if the stopgap outlives a month.

### Task #4 — The `proof/` project scaffold; `Level`/`Name` generated code elaborates (2026-09-12, Opus under Fable)

P0.4 of §5, and the second half of what task #2 left open: a Lake project
that `require`s both con-leche and the patched Aeneas library, with the
task-#3 spike's generated Lean brought in, the `Rc` holes of §3.2 filled and
the first two abstraction functions written.  **Everything elaborates**,
sorry-free, with **no axioms beyond `propext`/`Classical.choice`/`Quot.sound`
— the four `Rc` holes are now `def`s, so the generated model is axiom-free.**

**`scripts/setup-aeneas-lean.sh`** produces `_tmp/aeneas-lean/`: a copy of
`vendor/aeneas/backends/lean` with `spikes/toolchain/aeneas-433.patch`
applied and `lake update` run.  Idempotent by a fingerprint stamp over every
source byte plus the patch, and it keeps the existing `.lake/` across a
re-run (rebuilding Mathlib's dependents is minutes).  `patch --dry-run`
first: if the submodule ever moves under the patch the script exits non-zero
with "does not apply cleanly" rather than producing a half-patched tree.
The existing `_tmp/aeneas-lean-433/` from task #2 was verified byte-identical
to a fresh copy+patch and moved into place, so no Mathlib rebuild was needed.

**The `require` lines that worked** (`proof/lakefile.toml`; Lake accepts a
relative path pointing outside the workspace, and the `_tmp` gitignore is
irrelevant to it — no `proof/.aeneas-lean/` fallback was needed):

```toml
[[require]]
name = "con-leche"
path = "../vendor/con-leche"

[[require]]
name = "aeneas"
path = "../_tmp/aeneas-lean"
```

(The package name really is `con-leche`; Lake writes it back into the
manifest as `«con-leche»`.)  One `lean_lib ConRon` with `roots = ["ConRon"]`.

**One trick worth keeping.**  Lake puts *git* dependencies under the **root**
package's `.lake/packages`, so a naive `proof/` would clone and build its own
Mathlib beside the one task #2 already built for `_tmp/aeneas-lean`.  Step 5
of the setup script makes `proof/.lake/packages` a symlink to
`_tmp/aeneas-lean/.lake/packages`; both roots resolve Mathlib to the same rev
(the `v4.33.0` tag the patched lakefile asks for), so one checkout and one set
of oleans serve both.  `lake update` in `proof/` then downloaded nothing
("No files to download") and `lake build` replayed all 2037 Aeneas jobs from
the existing build tree.  `proof/lake-manifest.json` is committed.

**What the generated files needed.**  `Types.lean` and `Funs.lean` are the
task-#3 output verbatim except for the `import` lines (`LevelName.Types` →
`ConRon.Spike.LevelName.Types`); a `diff` modulo those is empty.  The Aeneas
`namespace level_name` is kept as generated.  No Aeneas CLI flag had to be
added and `aeneas` was not re-run.

**The one place §3.2's model needed more: `@[reducible]`.**  With the
literal `def alloc.rc.Rc (T : Type) := T`, `Types.lean` fails with

```
failed to generate `SizeOf` instance for `NameKind`: type mismatch
failed to generate `SizeOf` instance for `LevelKind`: type mismatch
```

The mutual inductive itself is accepted — Lean unfolds the alias to find the
recursive occurrence behind `alloc.rc.Rc name.NameNode` — but the automatic
`SizeOf` derivation will not, and builds an ill-typed instance.  `@[reducible]
def` fixes it with no other change; `abbrev` and a one-field `structure` were
both checked and work too, and the reducible `def` is the smallest edit to
§3.2 (and the only one that keeps `Rc T` *definitionally* `T`, so `absName`
can pattern-match straight through it).  Note this is the opposite of the
advice in Aeneas's own `Vec` (`Aeneas/Std/Vec.lean:22`, "we *do not* want to
mark `Vec` as reducible"): `Vec` wraps a `Slice` and the positivity checker is
the problem there; here the alias is the point.  **§3.2 is amended to
`@[reducible] def alloc.rc.Rc (T : Type) : Type := T`.**  The other three
models are exactly as §3.2 writes them (`new`/`deref`/`clone` = `ok x`,
`ptr_eq _ _ = ok false`); the `@[rust_type]`/`@[rust_fun]` attributes the
templates carry are kept — they are ordinary attributes of the Aeneas Lean
library and need no extraction machinery.

**`ConRon/Spike/LevelName/Abs.lean`** defines `absString`, `absName`,
`absLevel` (each a three-way `mutual` over the `Kind`/`Node`/wrapper triple
the port's `Rc` tree is; structural recursion goes through the reducible `Rc`
without help) and `absLevels`.  It forgets the `Rc`, the cached hash word,
and the machine-word representations: `Vec<u32>` code points become a
`String` by `String.ofList ∘ map Char.ofNat` (`List.asString` is deprecated in
4.33) and a `u64` index becomes a `Nat` by Aeneas's `UScalar.val`.
Definitions only; the theorems are Fable's next task.

**Numbers** (this machine, Mathlib and Aeneas already built):

| | |
|---|---|
| `lake build`, everything warm (no-op) | **3.4 s** |
| `lake build` after `rm -rf proof/.lake/build` | **9.6 s** |
| `lake build` after also `rm -rf vendor/con-leche/.lake/build` | **11.2 s** (6 con-leche modules: `Kernel.Name` 0.33 s, `PropWhen` 1.1 s, `Expr` 1.7 s, `Level` 3.5 s) |
| `Types.lean` (122 lines) | 1.4 s |
| `TypesExternal.lean` / `FunsExternal.lean` | 1.2 s each |
| **`Funs.lean` (1 354 lines, 25 `partial_fixpoint`, one 8-function `mutual`)** | **2.4 s** |
| ... of which loading the Aeneas + Mathlib oleans | 1.2 s (a file with only `Funs.lean`'s three imports takes 1.19 s) |
| ... so net elaboration of `Funs.lean` | **≈ 1.2 s** |
| `Abs.lean` | 1.2 s |

Lean's own profiler on `Funs.lean`: import 0.95 s, "process pre-definitions"
(the `partial_fixpoint` machinery) 0.33 s, type checking 0.19 s, typeclass
inference 0.17 s, compilation (LCNF, three passes) 0.29 s, elaboration
0.05 s.  **That is ~0.9 ms of net elaboration per generated line**, and the
`partial_fixpoint` block is not where the time goes.  A naive linear
extrapolation of §4's ≈145k generated Lean lines gives ~2 minutes of pure
elaboration for the whole core, plus a ~1.2 s import tax per file — so
**§6's risk 1 looks like a file-count problem, not an elaboration-cost
problem**, as long as the mutual blocks stay near this size.  The one number
this task still does not have is a `partial_fixpoint` block of hundreds of
functions; the knot (P1.4) is where that gets measured, and splitting it at
fuel boundaries stays the fallback.

**Two small 4.33 frictions in hand-written code** (neither touches the
generated files): `⟨cs⟩` no longer builds a `String` from a `List Char` (the
constructor is `String.ofByteArray` now), and `List.asString` is deprecated in
favour of `String.ofList`.

**Left for next time.** `scripts/extract.sh` does not exist yet, so the
import-line rewrite from `spikes/level-name/lean/` into
`proof/ConRon/Spike/LevelName/` was done by hand (a two-line `sed`; the
script will own it in P2).  There is no freshness gate on the committed
generated Lean yet, and no `#print axioms` gate — but the census above is
clean today and is the baseline for that gate.

### Task #6 — `ron::Nat`, the bignum (2026-09-12, Opus under Fable)

P1.1 (first half): `crates/con-ron-core/src/nat.rs`, the arbitrary-precision
natural that replaces Lean's runtime `Nat` (GMP behind a small-int fast path,
none of which con-ron trusts).  Charon and Aeneas **both succeeded on the
first run with zero errors and zero iteration**; the generated Lean is in
`_tmp/nat-lean/` (gitignored, not elaborated — that is P2's business).

**Design choice: a single `Vec<u64>` of little-endian limbs, normalised** —
§3.3's `Small(u64) | Big(Vec<u64>)` was rejected and §3.3 is amended.  The
reason is proof volume, not code volume:

* the abstraction is one recursive function over one list, with no case
  analysis and no "does it fit a word" side condition;
* every operation is *one* algorithm, so every homomorphism lemma is one
  induction.  The enum gives each binary operation four representation cases,
  each of which must additionally re-establish the right tag: ~4× the lemma
  count for nothing the model can see;
* normalisation is the single predicate "the last limb is not `0`".  The enum
  needs that *and* "`Big` only when it does not fit a word" — a second
  invariant every operation must preserve — to keep structural equality equal
  to numeric equality, which is what `beq` and (task #7) the hash map want.

The price is a heap allocation for small values.  That is a performance
decision, revisitable in P1.6 as a `Small` fast path proved equal to these
same functions, which is a far smaller proof than starting from the enum.
### Task #7 — `ron::HashMap` (2026-09-12, Opus under Fable)

P1.1 of §5: `crates/con-ron-core/src/hashmap.rs`, the chained-bucket hash map
that replaces `Std.HashMap` in the port (§3.3).  Charon and Aeneas both
succeeded on the **first** run; the only iteration was a Rust-side one (stack
depth, below), not a translation failure.

**Design.**  The Aeneas tutorial's *verified* hash map
(`vendor/aeneas/tests/src/hashmap.rs`, proofs in
`vendor/aeneas/tests/lean/Hashmap/Properties.lean`) is the template, kept
close enough that its `slot_t_inv` / `al_v` / `lookup` development transfers:
buckets are an association-list enum `AList<K, V> = Cons(K, V, Box<AList>) |
Nil` over a `Vec<AList<K, V>>`, beside `num_entries`, a `max_load` threshold
and a `saturated` flag.  Bucket counts are powers of two starting at 32,
doubling when `num_entries > max_load` with `max_load = capacity / 4 * 3`
(dividing first is exact and cannot overflow, so the load factor costs no
proof obligation).  `Vec<Vec<(K, V)>>` was rejected: Aeneas models `Vec::push`
and indexing but not `Vec::remove`/`pop`, so removal would need a new external
hole; on the `AList` it is a structural recursion.

Keys go through two traits *of our own*, `Hashable { fn hash64(&self) -> u64 }`
and `Eq2 { fn eq2(&self, other: &Self) -> bool }`.

**`Eq2` vs `PartialEq`, measured.**  A throwaway spike (two identical list
searches, one bounded by a user trait, one by `PartialEq`; `_tmp/eqspike/`)
put the two side by side in generated Lean:

| | user trait | `PartialEq` |
|---|---|---|
| trait structure | `structure Eq2 (Self : Type)`, one field `eq2` | `core.cmp.PartialEq (Self Rhs : Type)`, fields `eq` **and** `ne` (`Aeneas/Std/Core/Cmp.lean:12`) |
| dictionary in every signature | `(Eq2Inst : hashmap.Eq2 K)` | `(corecmpPartialEqInst : core.cmp.PartialEq K K)` |
| extra items per key type | none | a `core::marker::StructuralPartialEq` instance from `#[derive]` |
| the `eq` we get | ours, so the §3.2 pointer/hash fast paths are *in* it | `derive`d structural equality, which for the real key types descends into `Rc` and `Vec` through std impls we would then have to model (`alloc.vec.partial_eq.PartialEqVec.eq`) |

`Eq2` wins on all four counts, and the last one is decisive: `ExprC` keys are
`Rc` trees whose equality must be the fast-path one.  **Decision: `Eq2`.**
(`derive(PartialEq)` on a plain struct does flatten nicely into a single
`if`-chain — that was worth checking — but it is the wrong `eq` for us.)

**Numbers.**

| | |
|---|---|
| `src/nat.rs` port (raw / code lines) | 671 / 439 |
| tests in the same file (9 tests, not extracted) | 314 |
| Rust functions | 48 (26 `pub`) |
| generated `Types.lean` / `Funs.lean` | 35 / **737** (1.7× the Rust code) |
| generated external templates | **none** |
| `charon cargo --preset=aeneas` wall (after `cargo clean`) | **0.19 s** |
| `aeneas -backend lean -split-files -loops-to-rec` wall | **0.74 s** (0.58 s self-reported) |
| items translated | 48 transparent fns, 13 opaque, 4 trait decls, 7 trait impls (1 of each emitted) |
| **`partial_fixpoint`** | **21** |
| `mutual` blocks | **0** (every recursion is self-recursion) |
| external holes | **none** — the crate still has only §3.2's four `Rc` axioms, and this module adds nothing |

`cargo build`/`cargo test` warning-free, 9/9 green;
`scripts/lint-rust-style.sh crates/con-ron-core/src` clean.  The `.llbc`
lands at the *workspace* root (`con_ron_core.llbc`), not in the crate
directory — `charon cargo` follows cargo's workspace root; `*.llbc` is
gitignored.  Note that `charon cargo` is a no-op when cargo's cache is warm:
the llbc is written only when rustc actually runs, so `cargo clean` (or a
touch of every source file) has to come first.  That is a trap for P2's
`scripts/extract.sh`.

**The 13 opaque functions are all `core`/`alloc` primitives Aeneas already
models**, and they are the complete list of what this module asks of the std
model: `alloc.vec.Vec::{new, push, len, index}` (with
`core.slice.index.SliceIndexUsizeSlice`) and `core.num.U64::{overflowing_add,
overflowing_sub, wrapping_mul}`.  Aeneas's `Vec` model has no `pop` and no
`truncate`, which is the one thing that shaped the code: `norm` trims trailing
zero limbs by *copying*, and every operation builds its result with
`new`/`push` only.

**Constructs that do not survive transliteration, and their replacements**
(all of them a-priori choices, as in task #3 — nothing here was error-driven):

1. **Loops over limbs** → index-carrying `*_from` helpers, the public function
   being the `i = 0` wrapper (the task-#3 pattern); 22 of them.
2. **A mutable output buffer.**  §3.4 reserves `&mut` for the state parameter,
   so accumulators are passed **by value and returned**: `out: Vec<u64>` in,
   `Vec<u64>` out, with a local `let mut o = out; o.push(x);` at the one point
   that mutates.  Aeneas sees a plain value-passing recursion; no `&mut`
   parameter occurs in the module.  This also rules out `IndexMut`: `mul` is
   written as shift-and-add (`Σ_i (a * b[i]) << 64i`) rather than as an
   in-place accumulation into a pre-sized buffer, which keeps the `Vec` API to
   four functions and makes the homomorphism one induction with the invariant
   `toNat acc = toNat a * toNat b[0..i]`.
3. **`u64` → `usize` casts** (a shift's whole-word part becoming a limb index)
   are *avoided entirely*, because their model depends on
   `System.Platform.numBits`: a `u64` count is consumed by a counting
   recursion instead (`push_zeros` for left shifts, `skip_index` for right
   shifts).  The only casts in the module are `u64 → u128` and back, in the
   one multiply-accumulate step, where the `u128` product provably cannot
   overflow (`(2^64-1)^2 + (2^64-1) < 2^128`) and the truncating cast back is
   exactly the low half.  They come out as `lift (UScalar.cast .U128 x)` /
   `lift (UScalar.cast .U64 t)`, which are total.
4. **Variable-width shifts.**  Rust's `<<`/`>>` panic when the amount reaches
   the word width and Aeneas models them as `fail`, so `shift_left` and
   `shift_right` split off `bits == 0` before touching `64 - bits`, and the
   division's bit counter runs `j : 1..=64` so that `j - 1` is always legal.
5. **A three-way comparison instead of `Ord`.**  `pub enum Cmp { Lt, Eq, Gt }`
   with `beq`/`ble`/`blt` reading it off — one lemma about `cmp` instead of
   three.  Deriving `PartialEq`/`Ord` would drag std trait instances into the
   model for no gain.
6. **`#[derive(Clone)]` was measured, not assumed**: it translates fine
   (Aeneas models `Vec::clone` as `alloc.vec.CloneVec.clone`, so it is *not*
   an external hole), but it adds a `core::clone::Clone` declaration and
   instance and 14 lines to `Funs.lean`.  Dropped in favour of an explicit
   limb copy, which is also what the module's free-function API wants.
7. **`mod` is a Rust keyword** → the function is `modulo`.  `div` and `modulo`
   are wrappers around one `div_mod` returning a pair (Aeneas handles tuples).
8. **`pow` is square-and-multiply**, not repeated multiplication: the caller
   enforces con-leche's `ReducePowMaxExp` (`e ≤ 2^24`,
   `Kernel/Core.lean:639`), and 2^24 bignum multiplications is not a viable
   implementation.  The proof cost is one strong induction on `e` through
   `x^e = (x^(e/2))^2 * x^(e%2)` instead of a one-line induction.
9. **Division is restoring shift-subtract**, one bit at a time from the top
   (§3.3): `rem := 2*rem + bit; if rem ≥ b then rem -= b`.  Knuth D stays out.
   The quotient limbs come out most-significant-first, so `div_mod` reverses
   them (`rev_copy_from`) — the representation is little-endian.

**`hash64`** is FNV-1a over whole limbs (`h₀ = 0xcbf29ce484222325`,
`h_{i+1} = (h_i ⊕ limbs[i]) * 0x100000001b3`, wrapping).  As with task #3's
string hash this is *not* Lean's `Nat` hash and nothing may compare the two;
it only has to be a function of the *value*, which is exactly what the
normalisation invariant buys (see `hash64_congr` below).

**Tests** (`#[cfg(test)]`, invisible to Charon, so loops and closures are
allowed there): a 2 000-round differential test against `u128` for every
operation on operands below 2^127 (drawn by a 12-line xorshift, with every
fourth round narrowed to 1–70 bits so that the 0/1/one-limb boundaries are hit
often), which also asserts that every result is normalised; plus hand-picked
multi-limb cases — carries and borrows across 3–4 limbs, `sub` truncating to
zero, 200 random divisions by 3-limb divisors checked as `a = q·b + r ∧ r < b`
(and the `a/0 = 0`, `a%0 = a` convention), `3^200` against repeated
multiplication *and* against wrapping `u64` arithmetic in its low limb,
`2^200` as an explicit limb pattern, shifts by 0…256 with round-trips and
against `b · 2^k`, and gcd of Fibonacci numbers up to `F(180)`
(`gcd(F(n),F(n+1)) = 1`, `gcd(F(m),F(n)) = F(gcd(m,n))`).

**Proposed proof spec** (P3.1; the files to write are
`proof/ConRon/Abs/Nat.lean` and `proof/ConRon/Refine/Nat.lean`).  The
abstraction and the invariant:

```lean
/-- The value of a limb list, little-endian. -/
def limbsToNat : List Std.U64 → ℕ
  | []     => 0
  | x :: r => x.val + 2 ^ 64 * limbsToNat r

/-- `abs : con_ron_core.nat.Nat → ℕ`. -/
def toNat (a : nat.Nat) : ℕ := limbsToNat a.limbs.val

/-- Normalisation: no trailing zero limb. -/
def WF (a : nat.Nat) : Prop :=
  ∀ h : a.limbs.val ≠ [], a.limbs.val.getLast h ≠ 0#u64
```

Two structural lemmas carry the representation choice:

```lean
theorem toNat_lt (a) : toNat a < 2 ^ (64 * a.limbs.val.length)
theorem toNat_inj {a b} (ha : WF a) (hb : WF b) (h : toNat a = toNat b) : a = b
```

`toNat_inj` is what makes structural equality numeric equality; it is the
lemma `beq` and task #7's hash map both need, and `hash64_congr` (below) is an
immediate corollary, so hashing needs no spec of its own.

Every operation then gets one lemma in §3.5's exact-result-on-success shape —
nothing is claimed when the Rust model fails, and `WF` is threaded:

```lean
theorem add_spec {a b c} (ha : WF a) (hb : WF b) (h : nat.add a b = ok c) :
    toNat c = toNat a + toNat b ∧ WF c
```

and the same for, in the module's order (`F` is the `ℕ` operation named):

| Rust | `F` |
|---|---|
| `zero` / `one` / `from_u64 x` | `0` / `1` / `x.val` |
| `to_u64` | `= some x → toNat a = x.val`; `= none → 2^64 ≤ toNat a` |
| `is_zero` | `= true ↔ toNat a = 0` |
| `norm v` | `toNat c = limbsToNat v.val ∧ WF c` (the only lemma whose input is unnormalised) |
| `clone` | `toNat c = toNat a ∧ WF c` |
| `cmp a b` | `= Cmp.Lt ↔ toNat a < toNat b`, and the two siblings; `beq`/`ble`/`blt` are corollaries |
| `add` / `sub` / `pred` | `+` / `-` (Lean's truncating `Nat` subtraction, so no side condition) / `- 1` |
| `mul` / `pow a e` | `*` / `toNat a ^ e.val` |
| `div_mod a b` | `toNat q = toNat a / toNat b ∧ toNat r = toNat a % toNat b` — Lean's own `x/0 = 0`, `x%0 = x` make this unconditional, matching `Kernel/Core.lean:643-644` |
| `gcd` | `Nat.gcd` |
| `land` / `lor` / `xor` | `Nat.land` / `Nat.lor` / `Nat.xor` |
| `shift_left a k` / `shift_right a k` | `Nat.shiftLeft (toNat a) k.val` / `Nat.shiftRight (toNat a) k.val` |
| `hash64` | `hash64_congr : WF a → WF b → toNat a = toNat b → nat.hash64 a = nat.hash64 b` (from `toNat_inj`) |

Under each of those sits one auxiliary lemma per `*_from` helper, all of the
same shape — a statement about the suffix `i..` of the limb list, proved by
induction on `length - i`, e.g.

```lean
theorem add_from_spec (a b out : List Std.U64) (i n : ℕ) (carry : Std.U64) … :
    limbsToNat result
      = limbsToNat out
        + 2 ^ (64 * out.length) * (limbsFrom a i + limbsFrom b i + carry.val)
```

with `limbsFrom l i = limbsToNat (l.drop i)`.  The 21 `partial_fixpoint`s mean
every one of these is an admissibility-style induction (`dspec`) rather than a
structural one; `pow` and `gcd` additionally need a strong induction, on `e`
resp. on `toNat a` (Lean's own `Nat.gcd` is well-founded in the same argument,
so the two recursions line up arm for arm).

**Totality is deliberately not proved.**  The accept-direction (§1) claims
nothing when the Rust model fails, and this module *can* fail: `push` fails
past `Usize.max` limbs and `mul`'s shift counter is an overflow-checked `u64`
addition.  Both are "the machine ran out", which is exactly the class of
divergence §1 allows.
| Rust `src/hashmap.rs`, extracted part (raw / code) | 405 / 241 |
| Rust `#[cfg(test)]` part (9 tests, raw / code) | 311 / 265 |
| generated `lean/Types.lean` | 49 |
| generated `lean/Funs.lean` | **408** (1.7× the extracted Rust) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | **not emitted — no external holes** |
| `charon cargo --preset=aeneas` wall | 0.14 s |
| `aeneas -backend lean -split-files -loops-to-rec` wall | 0.54 s (0.38 s self-reported) |
| items | 28 transparent fns, 14 opaque, 5 globals, 6 trait decls (3 translated), 10 trait impls (3 translated) |
| `partial_fixpoint` | **8** (`pow2_at_least`, `list_get`, `list_insert`, `list_remove`, `allocate_slots`, `clear_slots`, `move_elements`, `move_elements_from_list`) |
| `mutual` blocks | **0** |

The 14 opaque functions are all Aeneas builtins (`Vec::push`/`with_capacity`/
`len`/`index`/`index_mut`, `core::mem::replace`, the scalar casts): this module
adds **no** external model of its own, unlike `Rc` in task #3.

`cargo build`/`cargo test` warning-free, 9/9 green;
`scripts/lint-rust-style.sh crates/con-ron-core/src` clean.  The generated
Lean was *not* elaborated (that is P2's business).

**Constructs that do not survive transliteration, and their replacements.**
The tutorial's file is written with `while`/`loop` throughout and extracted
with `-loops-to-rec`; §3.4 wants the recursion written out, which is where
most of these come from.

1. **Every loop → explicit recursion.**  `allocate_slots`, `clear`,
   `insert_in_list`, `move_elements`, `move_elements_from_list`,
   `contains_key_in_list`, `get_in_list`, `get_mut_in_list` and
   `remove_from_list` are the tutorial's loops; ours are named recursive
   functions, so the generated Lean has *named* `partial_fixpoint` definitions
   instead of Aeneas's anonymous `loop` functions — which is also why there is
   one `partial_fixpoint` per source function and no `mutual` block.
2. **The three walks over the slot vector split their index range in half**
   (`allocate_slots(n) = allocate_slots(n/2); allocate_slots(n - n/2)`;
   `clear_slots(lo, hi)` and `move_elements(lo, hi)` recurse on `[lo, mid)`
   and `[mid, hi)`).  **This was the one real iteration in the task**: the
   obvious `i → i+1` recursion is linear in the bucket count and the
   differential test blew the 2 MiB test-thread stack at ~16k buckets — a
   32M-entry `instC` wants 2^26 buckets, so a linear walk is not merely
   inelegant, it is unshippable in an unoptimised build.  Halving makes them
   `log2 n` deep (≤ 64) at no cost in the model; the refinement lemma becomes
   an induction on `hi - lo` instead of on `len - i`.  The per-bucket
   recursions stay linear in the bucket length, which is O(1) under any hash
   that spreads (`differential_constant_hash` is the degenerate case and is
   deliberately kept small).
3. **`remove_from_list` is by value**, `AList<K,V> → (AList<K,V>, Option<V>)`,
   not the tutorial's `&mut` walk: that one needs `std::mem::replace` plus an
   `unreachable!()` in an arm the borrow checker cannot see is impossible, and
   §3.4 forbids `unreachable!`.  By value it is a pure list function — the
   nicest `partial_fixpoint` in the file — at the cost of rebuilding the
   `Box` spine up to the removed entry.
4. **`next_power_of_two` → `pow2_at_least(n, cap, fuel)`**, a fuel-carrying
   doubling recursion (fuel 64) that saturates rather than overflowing.
   Intrinsics like `usize::next_power_of_two` are not modeled.
5. **The bucket index is computed in `u64`**: `((h % (n as u64)) as usize)`
   rather than `(h as usize) % n`.  Both casts are then exact and the model
   reads `h % n` over the naturals; the other order would need "`n` is a power
   of two dividing `2^usize::BITS`" to say the same thing.  Cost: one extra
   `UScalar.cast` in the Lean, which is total.
6. **`&&` avoided**, per task #3: `if self.num_entries > self.max_load { if
   !self.saturated { … } }` instead of the tutorial's `&&`.
7. **Hold the slot borrow across the call.**  `remove`'s first draft wrote
   `mem::replace(&mut self.slots[i], Nil)` and later `self.slots[i] = rest`,
   which generates *two* `Vec.index_mut` round trips; binding
   `let slot = &mut self.slots[i]` once and using `*slot = rest` generates
   one.  Worth doing everywhere a slot is read and written in one function.
8. `#[derive(Clone, Copy)]` on key types is confined to `#[cfg(test)]`; the
   extracted part derives nothing at all.

**No iteration API, verified.**  `grep -n "fold\|toList\|keys\|forM"
vendor/con-leche/ConLeche/Cached/*.lean vendor/con-leche/ConLeche/Kernel/FEnv.lean`
(`FEnv.lean` does not exist — `FEnv` lives in `Cached/StateC.lean`) returns
only `foldlM`s over `List DeclC` / `Array PendingCheck` / `List Level`,
`Array.toList` on the pending array, and prose containing "unfold"/"fold" —
**not one iteration of a `Std.HashMap`**.  A census of every memo field
(`ienv`, `constTyAt`, `constValAt`, `ruleRhsAt`, `whnfCoreC`, `whnfC`,
`inferC`, `inferIOC`, `defeqC`, `annotC`, `lsimpC`, `lnzC`, `eqvC`, `instC`)
finds exactly `getElem?`, `insert`, one `size` (`Cached/StateC.lean:197`, the
32M `instCCapC` cap) and resets to `{}`.  So `get` + `insert` + `len` +
`clear` is the whole surface con-leche needs; `remove`, `contains_key`,
`is_empty` and `with_capacity` are there for the frontend and for a complete,
testable API.  **If a later module needs to iterate, that is a design change
to bring back here, not an API to bolt on.**

**Tests** (`#[cfg(test)]`, exempt from §3.4).  A `Vec<(u64,u64)>`
association-list oracle and a xorshift64 PRNG drive four randomized
differential runs — 20 000 operations each over dense keys, over sparse keys
(forcing ~9 growths), and with periodic `clear`s, plus 8 000 over a key whose
hash has only four values and 4 000 over a key whose `hash64` is **constant
zero** (the whole map in one bucket, rehashed into one bucket on every
growth).  Each step compares `insert`/`remove`/`get`/`contains_key`/`len`/
`is_empty` against the oracle and every run ends with a full key-space sweep.
Plus `basic_ops` (replace semantics, reuse after `clear`),
`with_capacity_rounds_up_to_a_power_of_two`,
`growth_rehashes_and_keeps_every_binding` and
`remove_then_reinsert_across_a_growth`.

**Proposed proof spec** (P2; the abstract-map relation to `Std.HashMap`).
The model is the tutorial's, generalised to a generic key:

```lean
def AList.v      : hashmap.AList K V → List (K × V)
def HashMap.v    (m : hashmap.HashMap K V) : List (List (K × V)) := m.slots.val.map AList.v
def HashMap.al_v (m) : List (K × V) := m.v.flatten
def HashMap.toFun (m) (k : K) : Option V :=              -- THE abstract map
  ((m.slots.val[hash_mod_key k m.slots.val.length]!).v).lookupBy E.eq k
```

with an invariant `inv m` transliterated from `Hashmap/Properties.lean`:
`0 < m.slots.val.length`; every key sits in the bucket its hash selects
(`slot_t_inv`); keys pairwise distinct up to `eq2` (`distinct_keys`);
`m.num_entries.val = m.al_v.length`; and `inv_load` (`max_load = capacity / 4
* 3`, `capacity` a power of two `≥ 32`) — the load part is needed only to
discharge the arithmetic and to preserve `inv`, it never enters the laws.

Side conditions on the two dictionaries, as hypotheses (`Eq2Spec`,
`HashableSpec`): `eq2` never fails and decides a given equivalence
(`eq2 k k' = ok true ↔ absK k = absK k'`, plus reflexivity, symmetry,
transitivity), and `hash64` never fails.  **Nothing else is assumed about
`hash64`** — the laws hold for *any* hash function, the constant one included,
because `inv` records which bucket a key is in.  That is what makes §3.2's
"our `mixHash`/string hash differs from Lean's" verdict-neutral for the memo
tables.

The laws, in the exact-result-on-success shape of task #5 (`ok` on the Rust
side implies the equation; a `fail` claims nothing — the accept-direction of
§1):

```lean
theorem new_spec           : HashMap.new K V = ok m → inv m ∧ m.toFun = fun _ => none ∧ m.al_v = []
theorem with_capacity_spec : HashMap.with_capacity K V c = ok m → inv m ∧ m.toFun = fun _ => none
theorem len_spec           : inv m → HashMap.len m = ok n → n.val = m.al_v.length
theorem is_empty_spec      : inv m → HashMap.is_empty m = ok b → (b ↔ m.toFun = fun _ => none)
theorem get_spec           : inv m → HashMap.get … m k = ok r → r = m.toFun k
theorem contains_key_spec  : inv m → HashMap.contains_key … m k = ok b → b = (m.toFun k).isSome
theorem insert_spec        : inv m → HashMap.insert … m k v = ok (old, m') →
                               inv m' ∧ old = m.toFun k ∧
                               (∀ k', m'.toFun k' = if E.eq k k' then some v else m.toFun k') ∧
                               m'.al_v.length = m.al_v.length + (if old.isSome then 0 else 1)
theorem remove_spec        : inv m → HashMap.remove … m k = ok (old, m') →
                               inv m' ∧ old = m.toFun k ∧
                               (∀ k', m'.toFun k' = if E.eq k k' then none else m.toFun k') ∧
                               m'.al_v.length = m.al_v.length - (if old.isSome then 1 else 0)
theorem clear_spec         : inv m → HashMap.clear m = ok m' → inv m' ∧ m'.toFun = fun _ => none
```

and the bridge to con-leche, which is all the rest of the port ever uses:

```lean
def Rel (m : hashmap.HashMap K V) (M : Std.HashMap K' V') : Prop :=
  ∀ k, (m.toFun k).map absV = M[absK k]?

theorem Rel_new    : HashMap.new K V = ok m → Rel m {}
theorem Rel_get    : Rel m M → HashMap.get … m k = ok r → r.map absV = M[absK k]?
theorem Rel_insert : Rel m M → HashMap.insert … m k v = ok (old, m') → Rel m' (M.insert (absK k) (absV v))
theorem Rel_remove : Rel m M → HashMap.remove … m k = ok (old, m') → Rel m' (M.erase (absK k))
theorem Rel_clear  : Rel m M → HashMap.clear m = ok m' → Rel m' {}
theorem Rel_len    : Rel m M → inv m → HashMap.len m = ok n → n.val = M.size
```

`Rel_len` additionally needs `absK` injective on the keys in play (§3.5's
`NameWF`/`NodeWF` hypotheses already give that); every other law is free of
it.  The first block's proofs are the tutorial's, edited for the generic key
and the halved slot walks; the second block is then bookkeeping against
`Std.HashMap.getElem?_insert` / `getElem?_erase` / `size_insert`.

**Open items.**  (a) The workspace has no `[profile.release] overflow-checks =
true`; the Aeneas model treats every `+`/`-`/`*` as checked, so the release
binary must too, or the model does not describe it.  One line in the workspace
`Cargo.toml`, to land with the first release build.  (b) `saturated` is never
exercised — a table that big cannot be allocated on this machine — so its
branch is covered only by the `pow2_at_least` unit assertions.  (c) The four
per-bucket recursions are still linear in the bucket length; a pathological
bucket would show up as a stack overflow, not a wrong answer.
### Task #8 — The provenance gate (2026-09-12, Opus under Fable)

**What landed.**  `scripts/provenance.py` (§3.7), python3 stdlib only, no
build, ~0.3 s over the whole con-leche tree.  `check` / `update [--old]` /
`coverage`, all taking `--roots DIR…`; exit 0 clean, 1 findings, 2 usage or
IO.  CLAUDE.md now names it beside the style lint.  The spike's 69
Charon-visible items in `spikes/level-name/src` carry 56 citations and 15
`none —` lines; `check` is green and `update` is a no-op against the pin.

**How the conversion went.**  The spike's old `/// ConLeche/Kernel/X.lean:NNN
— …` lines became citations of whole declaration blocks, located by name with
the script's own locator.  Two things fell out of it:

* the three-pass locator (§3.7 implementation notes): with one loose
  match, `Name.beqPtr` and `Level.beqPtr` bound to the `Name`/`Level`
  inductives, because a `where`-clause rule that lets `subst` answer to
  `subst.go` also lets `Name` answer to `Name.beqPtr`;
* the rewrite makes the *deviation* the body of each doc comment.  The
  citation carries the location, so the prose no longer repeats it and says
  only what differs from the Lean — "Deviation: Lean's `fuel + 1` pattern is
  the `fuel == 0` test plus `fuel - 1`, and its `diff : Int` is an `i64`".

The bump workflow was exercised for real by checking the submodule out at
`41b3bfdb` (two commits back, where `Level.lean` sits 4 lines earlier and
`Expr.lean` 1) and running `update --old <pin>`: 45 *moved* (rewritten
silently), 10 already at the right lines, 0 *gone*.  A hand-edited
`defaultFuel` then produced the *changed* alert with its unified diff and the
marker line in `level.rs`; `check` went red naming that line, and green again
when the line was deleted.  Re-running `update` twice more changed nothing
and added no second marker.  Restored afterwards.

**Coverage baseline (P1 ledger, con-leche 3e004805).**

| tree | files | covered | uncovered |
|---|---|---|---|
| `ConLeche/Kernel/**` | 42 | 29 | 774 |
| `ConLeche/Cached/**` | 7 | 0 | 215 |
| **total** | **49** | **29 / 1018 (2.8 %)** | **989** |

The 29 are `Name.lean` 3/5, `Expr.lean` 8/42 (the `Level` half only) and
`Level.lean` 18/25 — exactly the spike's scope.  The uncovered remainder in
those three files is precisely the spike's own "Not ported here" lists
(`ofLeanName`, `toString`, `zeronessOf`, `substPW`, the four
`Expr.*LevelParams*` and `LPMemoInv`), so the ledger agrees with the prose.

**Limitations of the locator, noticed while building it.**

* It finds a declaration by *name*, so a rename reads as *gone* and a
  rename-plus-move cannot be distinguished from a deletion — the operator
  re-points the citation by hand.  Two declarations of the same name in one
  file (a `private` shadow, or the same name in two `namespace` blocks) bind
  to the first.
* Block extension is column-0 lexical, not syntactic: a declaration whose
  body contains a column-0 line (a multi-line `/- … -/` whose interior
  starts at column 0, a `deriving` continuation) can end early, and a
  `mutual` block's members are cited individually (each stops at the next
  `/--`), which is what the spike wants but means the `mutual`/`end` frame
  itself belongs to no citation.
* A citation to an anonymous `instance : C T` has no name to relocate by;
  `_` as the decl silences the name check but `update` cannot move it.
* Because there is no hash, `check` cannot see a *changed* declaration on
  its own — only `update`, run at the bump, can.  The gate's guarantee is
  therefore "every bump goes through `update`", which is a workflow rule,
  not something the source can enforce.  What `check` does enforce is that
  no bump lands half-reconciled: a `CHANGED` marker is a hard failure.
* `coverage` counts `def`/`abbrev`/`inductive`/`structure`/`class`/
  `instance`/`opaque` and skips `theorem`/`lemma`/`example`, so an
  implementation written as a `theorem` (none today) would be invisible to
  the ledger; anonymous instances need a `_` citation to be marked.
* The Rust scanner is a brace counter over `//`- and literal-stripped
  lines.  It has no idea about `/* … */` block comments containing braces
  or about macro bodies; neither appears in the port today, and both would
  show up as a wrong item list rather than silently.

### Task #9 — `Name`/`Level` into the crate; `PropWhen` (2026-09-12, Opus under Fable)

P1.2 (first half).  `spikes/level-name/src/{name,level}.rs` copied into
`crates/con-ron-core/src/` — the spike directory is untouched, it is task
#3's recorded evidence; the crate copies are the living code — and
`ConLeche/Kernel/PropWhen.lean` ported as `src/prop_when.rs`.  Charon and
Aeneas both succeeded on the **first** run again, with zero iteration; the
generated Lean is in `_tmp/core-lean/` (gitignored, not elaborated — P2).

**What the two moved modules gained.**  `pub mod name; pub mod level;` in
`lib.rs` and its module-map table, plus the four `crate::hashmap`
dictionaries the memo tables will key with: `impl Hashable for Name`
(`Name.hashData`, the stored word), `impl Eq2 for Name` (`Name.beq`, with
its pointer and hash fast paths), and the same two for `Level` — citing
con-leche's own `instance : Hashable Name` (`Name.lean:47-49`),
`instance : BEq Name` (`:88`) and their `Level` twins (`Expr.lean:55-57`,
`:86`).  This is where task #7's `Eq2`-over-`PartialEq` decision pays: the
instance *is* `beq`, so the §3.2 fast paths are inside the map's key
equality rather than beside it.  The spike's 13 unit tests came along,
split by subject (1 in `name.rs`, 12 in `level.rs`) and joined by one new
test per module that the dictionaries are exactly `hash_data` and `beq`.

**The representation decision: mirror all five constructors.**
`PropWhen.lean` seals a five-constructor `private inductive PropWhenRepr`
(`never | always | one p | two p q (p < q) | many ps (Sorted ps ∧ 2 <
ps.length)`) inside a one-field `structure PropWhen` whose constructor and
field are `private`.  The port does the same: a module-private
`enum PropWhenRepr` inside a `pub struct PropWhen` with a private field.
Rust's module privacy is exactly Lean's seal — outside `prop_when` the type
can be held and passed but neither built nor matched, so the smart
constructor `if_all_zero` is the only way in and the canonical-form
invariant cannot be dodged.

The alternative the task offered — `Never | Always | Params(Vec<Name>)`
with the sorted invariant — was rejected because it does not keep the
*operations* one-to-one, which is what §3.1 buys and what the refinement
proof spends its budget on.  Each of `holds`, `inter`, `bind_z`,
`params_defined`, `to_list`, `has_params`, `hash_repr` and `equiv_r`
dispatches on the five constructors in the Lean's own arm order, so each
Rust arm refines one Lean arm by `rfl`.  Collapsing to one list
constructor turns every one of those five-way matches into a `List.all` /
`merge` computation that is merely *provably* equal to the arm it stands
for: about five lemmas per operation, some thirty in all, bought for
nothing.  It would also discard what the constructors are *for* —
con-leche's census (`PropWhen.lean:360`) found 605 492 data with no
parameter, 123 332 with one, 16 with two and **none** longer, so
`always`/`one`/`two` are 100 % of the real traffic and touch no list cell at
all.  The proof-carrying fields are erased, as every Lean proof field is
under Charon; they come back as the Lean-side well-formedness predicate
§3.5 already uses for `NameWF`/`NodeWF`, under which `to_list` is the
canonical representative of the parameter set and `beq` is equality.

**Name ordering, as asked: it is con-leche's own.**  `Name.cmp` is defined
*in* `PropWhen.lean` (`:75-85`, there is no order on `Name` elsewhere in the
tree): the structural lexicographic order, constructor order `anonymous <
str < num`, then the prefix, then the payload with the core `Ord` instances.
Ported literally, nine arms for nine arms, with `Ordering.then` as
`ord_then`, `compare : String → String → Ordering` as `str_compare` (Lean's
`String.compare` is `compareOfLessAndEq`, i.e. the lexicographic order of the
code-point lists, `Init/Data/Ord/String.lean:32` — so on the `Vec<u32>` of
§3.3 it is a first-difference walk in which a proper prefix is smaller) and
`compare : Nat → Nat → Ordering` as `nat_compare` on the `u64` payload.  A
unit test pins irreflexivity, asymmetry, transitivity, trichotomy,
`cmp a b = .eq ↔ Name.beq a b` and the three ordering clauses.

**Numbers.**

| | |
|---|---|
| Lean ported (`PropWhen.lean`, 1 094 lines): 24 cited blocks | 232 raw / **114 code** |
| `src/prop_when.rs`, extracted part (raw / code) | 670 / **361** (3.2× the Lean code) |
| `src/prop_when.rs`, `#[cfg(test)]` part (7 tests) | 282 / 222 |
| `src/name.rs` (extracted raw / test raw) | 231 / 34 |
| `src/level.rs` (extracted raw / test raw) | 620 / 191 |
| generated `_tmp/core-lean/Types.lean` (whole crate) | 203 (41 of them `prop_when`) |
| generated `_tmp/core-lean/Funs.lean` (whole crate) | **3 318** (805 of them `prop_when`, 2.2× its Rust code) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 |
| `charon cargo --preset=aeneas` wall (after `cargo clean`) | **0.30 s** |
| `aeneas -backend lean -dest _tmp/core-lean -split-files -loops-to-rec` | **1.38 s** (1.20 s self-reported) |
| items translated (whole crate) | 182 transparent fns, 25 opaque, 5 globals, 11 trait decls (8 emitted), 22 trait impls (12 emitted) |
| `partial_fixpoint` (whole crate / `prop_when`) | **64** / **10** |
| `mutual` blocks | 1 in `Funs.lean` (task #3's 8-function `leq_core` knot, 313 lines), 2 in `Types.lean` — `prop_when` adds **none**, every recursion is self-recursion |
| external holes | **exactly the four `Rc` axioms of §3.2** — `new`, `clone`, `deref`, `ptr_eq`.  `prop_when` adds nothing; the 25 opaque functions are all `core`/`alloc` primitives Aeneas already models |

`cargo build`/`cargo test` warning-free, **40/40** green (13 moved from the
spike + 2 new dictionary tests + 7 new `prop_when` tests + the 18 of tasks
#6/#7); `scripts/lint-rust-style.sh crates/con-ron-core/src`
clean; `scripts/provenance.py check` green — 282 items, 154 citations, all
current at pin 3e004805.

**Constructs that do not survive transliteration, and their replacements**
(all a-priori, as in tasks #3, #6 and #7 — nothing was error-driven).

1. **A Lean function *argument*.**  `holds (φ : Name → Nat)` and
   `bindZ (f : Name → PropWhen)` take functions; §3.4 forbids closures.  Each
   becomes a one-method trait the caller implements — `trait Valuation { fn
   value_at(&self, n: &Name) -> u64 }` and `trait NameToPw { fn apply(&self,
   n: &Name) -> PropWhen }` — i.e. task #7's `Eq2`/`Hashable` pattern, which
   Aeneas renders as a `structure` with one field and threads as a dictionary.
   `Level.substPW` (`Level.lean:205`, not ported yet) will be the one
   `NameToPw` implementation the checker needs.  **This is the pattern for
   every higher-order argument in the rest of the port**, including the
   `CoreFns` knot of §3.1.
2. **A sealed representation.**  Lean's `private inductive` + `private
   ofRepr ::` is Rust's module-private `enum` + private struct field.  No
   ceremony needed, and Charon translates private items fine (they are in the
   `.llbc` and in `Funs.lean`, `of_repr` and `equiv_r` included).
3. **Proof fields are erased.**  `two p q (h : p < q)` becomes `Two(Name,
   Name)`; the invariant is owed by the smart constructors and stated on the
   Lean side.  `name_lt` is ported anyway (from the `LT Name` instance) —
   nothing executed calls it, but the invariant is written with it.
4. **`List` recursion → index-carrying `*_from` helpers** (the task-#3
   pattern), 8 of them: `str_compare_from`, `append_from`, `merge_from`,
   `canon_from`, `names_beq_from`, `names_hash_from`, `all_zero_from`,
   `all_contained_from`.  `merge` needs *two* indices and an accumulator,
   because it walks two lists at once and conses on the way out; the
   accumulator is passed by value and returned (task #6's rule — §3.4
   reserves `&mut` for the state parameter).  `canon`'s `List.foldr` is the
   recursion that merges `ps[i]` into the canonical form of `ps[i+1..]`.
5. **Lean's sharing costs a copy.**  `merge`'s `| [], bs => bs` hands back a
   list; a `Vec` has to copy the tail (`append_from`), and `to_list` of a
   `many` returns an owned copy rather than the list it holds.  The `Name`s
   themselves are still shared (`name::dup` is an `Rc` bump).
6. **List patterns over a `Vec`.**  `ofSorted`/`ifAllZero` dispatch on `[]`,
   `[p]`, `[p, q]`, longer; Rust cannot pattern-match a `Vec`, so they are
   `ps.len() == 0/1/2` `if` chains.  A list that is *consumed* into a datum is
   taken by value (so `of_sorted`'s `many` arm **moves** the vector instead of
   re-consing it); a list that is only *read* comes in by reference.
7. **`hash'` is the derived `Hashable PropWhenRepr`**, which is "the
   constructor index, then `mixHash` folded over the fields"
   (`Lean/Elab/Deriving/Hashable.lean:50`; checked against the real elaborator
   output on v4.33.0).  Two deviations, both free by §3.2: the derived
   instance also folds the *erased proof* fields (verified: it really does
   emit `hash h` for `h : p < q`), which do not exist here, and `List.hash`'s
   seed and fold (`foldl mixHash 7`, `Init/Data/Hashable.lean:37`) are
   transliterated over our own name hashes, which already differ from Lean's.
   What the hash must be is a function of the *value* — which canonicity makes
   a function of the parameter *set*, and that is what the test asserts.
8. **`two'` has no Rust spelling** for the prime: `two_prime`.
   `PropWhen.hash'` is `hash_pw`, and `toList?` is `to_list_opt` (`?` is not a
   Rust identifier character either).
9. **`Ordering` is our own three-value enum**, a sibling of `nat::Cmp` rather
   than the same type: they are two different Lean types (`Ordering` vs. the
   `beq`/`ble`/`blt` triple of §3.3's bignum) and they never meet.

**Deliberately not ported** (recorded so the next task does not re-derive
it): `PropWhen.Sorted` (`:201`, a `Prop` — the representation invariant; it
is *cited* on `PropWhenRepr`, where it belongs, and is destined for the
Lean-side `PropWhenWF`), `casesZ` (`:651`, a dependent eliminator: proof
machinery with no executable content), `reprPrec'` and its `Repr` instance
(`:672`, rendering only — §3.1 says message strings need not match), the
`Inhabited` instance (`:475`), and every `theorem` — the whole law battery
from `:992` on, which is the *spec* this port will be proved against.

**Tests** (`#[cfg(test)]`, invisible to Charon, so closures and loops are
allowed).  Seven, one per group of laws con-leche's own docstrings state,
each checked over a fixed 5-7 element battery of data that covers all five
constructors: `Name.cmp` is a strict total order and agrees with `Name.beq`
at `.eq` (`:159-186`); `canon` sorts, deduplicates and is idempotent
(`canon_canon`), and `toList (ifAllZero ps) = canon ps`; **canonicity** —
membership-equal lists give `beq`-equal data with equal hashes
(`ifAllZero_eq_iff`, `eq_iff_holds`); `holds` on `never`/`always`/parameter
sets plus `isNever`/`hasParams` (`:702-780`); `inter` is commutative,
idempotent, associative, has `ifAllZero []` as a two-sided unit, is absorbed
by `never`, and satisfies `holds_inter` at every pair of the battery
(`:876-1047`); `paramsDefined_inter_of`; and `bindZ` — `bindZ_unit`
(`n ↦ ifAllZero [n]` reproduces the datum, the datum half of
`Level.substPW_self`), `bindZ_inter`, `bindZ_go_append`, and a substitution
to `never` propagating.

**Coverage** (`scripts/provenance.py coverage | tail -3`), con-leche
3e004805: **TOTAL 51/1018 covered (5.0 %), 967 uncovered** — up from task
#8's 29/1018 (2.8 %).  Per file: `Name.lean` 3/5, `Expr.lean` 8/42,
`Level.lean` 18/25, **`PropWhen.lean` 22/24** — the two uncovered being
exactly `casesZ` and `reprPrec'` above, so the ledger again agrees with the
prose.

**Note for P2.**  `_tmp/core-lean/` is now the *whole crate* in four files
(`Types.lean` 203, `Funs.lean` 3 318, two templates).  `charon cargo` is
still a no-op on a warm cargo cache (task #7), so `cargo clean` comes first;
the `.llbc` still lands at the workspace root.

### Task #5 — Lemma-shape spike: `Level`/`Name` refinement proved (2026-09-12, Opus under Fable)

P0.4's second half and the dry run for P3: the 27 `sorry`s Fable left in
`proof/ConRon/Spike/LevelName/Refine.lean` are gone.  Every statement she
wrote is proved, with the conclusions verbatim; the three changes to
*hypotheses* are listed below.  `lake build` is clean of errors **and
warnings**, and

```lean
#guard_msgs in #print axioms leq_refines        -- propext, Classical.choice, Quot.sound
#guard_msgs in #print axioms simplify_refines   -- idem
#guard_msgs in #print axioms level_beq_exact    -- idem
```

is a committed gate at the end of the file.  Nothing from Aeneas's library,
nothing from the `Rc` models.

**Size.**

| | |
|---|---|
| `Refine.lean` before (statements only) | 111 |
| `Refine.lean` after | **1 830** |
| ... signature/statement lines | 323 |
| ... tactic lines | 1 378 |
| ... declarations | 108 |
| Rust ported (`src/name.rs` + `src/level.rs`, code lines, task #3) | 502 |
| generated `Funs.lean` | 1 354 |
| Lean ported from con-leche (code lines) | 197 |
| `lake build` of `Refine.lean`, cold | **5.5 s** (whole project from scratch: 14 s) |

So the proof is **3.6× the Rust code, 1.35× the generated Lean, 9× the
con-leche source** — but that ratio is the wrong one to extrapolate (below).

**Section split.** Lines 1–601 are *one-off infrastructure*: the monadic
plumbing, the smart-constructor inversion lemmas, `NameWF`/`LevelWF`,
`absString`/`absName`/`absLevel` injectivity, `str_eq`, `beq` (reflexivity,
soundness, exactness) and two hand-rolled structural induction principles.
Lines 602–1717 are the actual per-function refinements; 1718–1830 restate
them under Fable's names and run the axiom census.  The largest single
proofs: `rest_refines_aux` 268 lines, `absLevel_injective` 115,
`level_beq_abs` 108, `leq_core_refines_aux` 74, `subst_go_refines` 65,
`combining_refines` 64, `simplify_refines'` 60, `by_cases_refines_aux` 57.

**Changes to the statements** (conclusions untouched):

1. **`NameWF`/`LevelWF` are inductive predicates, not `def`s**, and they say
   "this node is what the port's own smart constructor built" rather than
   "the stored word equals *this formula*".  See the §3.5 amendment above.
   The pay-off: `level_zero_wf … level_param_wf` are *literally the five
   constructors*, `absLevel_injective`'s hash argument is
   `Result.ok_injective (h₁.symm.trans h₂)`, and `name.mix_hash` never
   appears in a proof — no totality lemma for it was needed at all.
2. **`subst_refines` needs `hks : ∀ k ∈ ks.val, NameWF k`.**  Fable's version
   only assumed the *values* well-formed.  It is not provable as written, and
   not for a technical reason: `subst_go` decides which value to take with
   `name.beq ks[i] n`, whose exactness needs the *key*'s hash word correct.
   An ill-formed key with a wrong stored hash makes the Rust walk skip a
   substitution con-leche performs.
3. **`vs.toList` → `vs.val`** (and `ks.toList` → `ks.val`).  Aeneas's
   `alloc.vec.Vec` has no `toList`; its list projection is `Vec.val`.  A
   convention for §3.5: refinement statements about `Vec` arguments quantify
   over `.val`.

Plus one non-change worth recording: `rest_refines`, `by_cases_refines` and
`leq_core_refines` are stated *without* an induction hypothesis, exactly as
Fable wrote them.  Internally they are corollaries of one
`leq_core_refines_aux (N : Nat) : ∀ fuel, fuel.val = N → LeqCoreSpec fuel`
proved by strong induction on `N`, where `abbrev LeqCoreSpec fuel` packages
the `leq_core` statement at one fuel value.  The cascade
`rest → imax_rules → by_cases_left/right → by_cases`, and
`imax_rules → imax_rules_distrib → imax_rules_distrib_right`, has **no cycle
inside one fuel step**, so those seven are plain lemmas taking
`hQ : LeqCoreSpec fuel` as an argument and composing in dependency order; only
`leq_core` itself consumes the induction, at `fuel - 1`.  No `dspec`, no
admissibility, no `partial_fixpoint` reasoning anywhere.

**What carried the weight.**

* **A five-lemma local `simp` set is the single highest-leverage thing in the
  file**: `bind_eq_ok_iff` (`(do let x ← e; f x) = ok v ↔ ∃ y, e = ok y ∧
  f y = ok v`, proved in four lines by `cases` on the ITree and marked
  `@[simp]`), plus `ok`-equations for the four `Rc` models, `Aeneas.Std.lift`,
  `level.dup` and `name.dup`.  With them, `rw [f.eq_def] at h; simp at h`
  turns an entire Rust function body into a nest of existentials and
  disjunctions in one step — including the `if`/`match` splits.  This belongs
  in a shared `ConRon/Refine/Basic.lean` for the real port.
* **Lean's own equation lemmas carry the arm-order side conditions.**  For a
  definition with overlapping `match` patterns (`ConLeche.Level.rest`,
  `imaxRules`, `subst.go`), `rw [ConLeche.Level.rest]` picks the first
  matching arm *and emits "the earlier patterns do not match" as extra
  goals*, which `simp_all` discharges.  That made 13 `rest` arm-selection
  lemmas and 5 `imaxRules` arm-selection lemmas one-liners each, and it is
  why the arm-order deviation of task #3 (`imaxRules` as a four-function
  cascade) costs almost nothing to prove: the Rust cascade's guards are
  exactly those side conditions.  **Recommended pattern: for every con-leche
  function with overlapping patterns, write its arm-selection lemmas first,
  as `rw [f] <;> simp_all` one-liners, then do the Rust-side case analysis
  against them.**
* `scalar_tac` for every index, fuel and `diff` bound (never `omega` on a
  scalar goal; the file's single `omega` is on a pure `Nat` subtraction).
* `WP.spec_imp_exists` to turn Aeneas's `⦃ ⦄` specs (`Vec.index_usize_spec`,
  `Vec.push_spec`, `Usize.add_spec`, `U64.sub_spec`) into the forward
  `∃ y, f x = ok y ∧ P y` form.  **`step` was never usable**: it wants a
  `⦃ ⦄` goal, and these proofs are forward from a hypothesis
  `h : rust … = ok o` towards `lean … = o`.  The `⦃ ⦄`/`step` tier and the
  refinement tier are two different proof styles; ours needs the `spec`
  lemmas only as a source of "this call succeeds and returns *that*".
* `IScalar.add_equiv`/`sub_equiv` and `UScalar.sub_equiv` for `diff ± 1` and
  `fuel - 1`: from `x + y = ok z` they give `z.val = x.val + y.val`, which is
  all the overflow reasoning the refinement needs (overflow makes the
  hypothesis false, so there is nothing to prove).
* Hand-rolled structural induction principles `Level.ind'` / `Name.ind'`
  (12 lines each) over the port's three-type `Kind`/`Node`/wrapper mutual
  inductive, so that `induction u using Level.ind'` skips the `Rc` and the
  node layer.  Aeneas's `partial_fixpoint` definitions give no induction
  principle of their own, so **every structural refinement is an induction on
  the argument, not on the function** — either on this recursor or on the
  `LevelWF` derivation when the proof needs the WF hypotheses in step.
* `#setup_aeneas_simps` was *not* needed (no `getElem!` in this code).

**What was awkward in the generated code.**

1. **`&&` expansion (task #3, item 9) shows up as duplicated proof
   obligations.**  `rest`'s `Imax`/`Imax` arm is `beq a x && beq b y &&
   diff ≥ 0` in the Lean and a four-way `if` nest in `Funs.lean`; after
   `simp` the hypothesis is a three-way disjunction in which
   `level.imax_rules … = ok o` appears *three times*.  Harmless but it
   triples that arm.  Confirms the §3.4 advice to write the `if` nest
   explicitly — it does not remove the duplication, but it keeps the shape
   predictable.
2. **The 5×5 `match` explosion.**  `level.beq`, `level.rest` and
   `level.combining` each translate to 25 arms because Charon expands nested
   matches, and the proofs mirror that one-for-one: `rest_refines_aux` is 268
   lines for 25 cases (generated by a script with seven distinct case
   bodies), `level_beq_abs` 108 lines.  This is the dominant cost driver and
   it is *structural*, not accidental.
3. `have i1 := s.len; if … ` — Aeneas hoists `Vec::len` into a `let_fun`,
   which blocks `split`.  `simp only []` first.
4. `Aeneas.Std.lift` wrapping pure operations (`wrapping_mul`, `^^^`,
   `UScalar.cast`) needs its own `@[simp]` unfolding, and `alloc.vec.Vec`
   has no `toList`.
5. Every `*_from` index loop (§3.4's `Vec` convention) costs one induction on
   `len - i`, with the conclusion stated on `List.drop i` so that `i = 0`
   collapses to the whole list.  `str_eq` needed two (reflexivity and
   soundness), `subst_go` one.  Reusable shape, ~20–65 lines each.

**Assessment of the per-function proof cost for the full port.**  Three
numbers, in increasing order of usefulness:

* Naive: 1.35 proof lines per generated Lean line ⇒ ~190k lines for §4's
  ≈145k generated lines.  This is wrong: a third of this file is one-off.
* Marginal, by line: 1 117 lines of actual per-function refinement for 502
  Rust code lines ⇒ **≈ 2.2 proof lines per Rust line**, ≈ 55k Rust lines
  in §4's extrapolation ⇒ **~120k**.  Still pessimistic, because `Level` is
  unusually branchy (three 5×5 matches in 500 lines).
* By function: 40 refinement lemmas, median **~20 lines**, and the
  distribution is bimodal — a structurally recursive function over one
  scrutinee costs 20–60 lines (`level_has_param` 25, `is_never_zero` 17,
  `simplify` 60, `subst` 46), a function matching on *two* scrutinees costs
  60–270 (`combining` 64, `beq` 108, `rest` 268).  con-leche's hot path has
  far fewer two-scrutinee matches per line than `Level.lean` does
  (`whnfCore`/`infer` branch on one expression at a time; `defEq` is the
  exception and it is exactly the place to watch).

My estimate for the ≈22k-line verified core is therefore **8–20k proof
lines**, i.e. the same order as con-leche's own `Verify/Cached/*` tier
(§4's guess) — *provided* the one-to-one mirroring rule holds and the memo
tier's hard work stays on the con-leche side.  The tail risk is concentrated
in `defEq` and the inductive routes, where two-scrutinee matches are the norm.
The infrastructure this task built (the simp set, the WF pattern, the
induction principles, the arm-selection-lemma technique, the index-loop
shape) is written once and reused, and a second agent given those five
patterns should be able to prove a module without design decisions — the same
claim task #3 made for the porting side, and it held here.

**Left for next time.**  The `ConRon/Refine/Basic.lean` factoring (today the
simp set lives at the top of `Refine.lean`); a `Vec.toList`-style convention
note in §3.4; and `is_equiv_list`, `is_zero`, `is_non_zero`,
`all_params_defined`, `name_nodup`, `levels_hash`, `levels_have_param` and the
three string-shape predicates are ported but unproved — Fable did not state
them, and they are all instances of the patterns above.
### Task #10 — The `DeclC` dump (`con-ron-decls/1`) (2026-09-12, Opus under Fable)

P1.6's Lean half (§3.6, now updated to name the tool): con-leche's own
frontend produces the `List DeclC` that `checkDecls` consumes, and this task
gives that list a file format, a writer, a Lean reader and a round-trip
harness — so the Rust core can be exercised without a Rust parser and without
a Rust reimplementation of the frontend's rewrites.

**What landed.**  `proof/ConRon/Dump/FORMAT.md` (the specification),
`Write.lean` (`dumpDecls : List DeclC → String`), `Read.lean`
(`parseDecls : String → Except String (List DeclC)`), `Main.lean` +
`[[lean_exe]] con-ron-dump`, and `scripts/dump-fixtures.sh` (the corpus
sweep).  `lake build` is clean and the format's string codec carries its own
`#guard` self-tests.

**The format**, in one paragraph.  Line-oriented ASCII, first line
`con-ron-decls/1`, last line `end <declCount>`, fields separated by one
space.  **Nine id spaces** — `N` name, `L` level, `W` propwhen, `E` expr, `V`
constval, `R` recrule, `C` indcaps, `P` projtable, `I` constinfo — each dense
from `0`, each record's id equal to the number of records of its kind already
seen, every reference pointing backwards.  A reader is therefore one forward
pass pushing onto nine `Vec`s, with no fixups: that is the property the Rust
side is being handed.  `N`/`L`/`W`/`E` are *interned* (a hash map from value
to id), which is what keeps con-leche's term DAG a DAG instead of exploding
into a tree; the other five are merely numbered.  `D` records carry no id —
their order is the payload.  Nats are decimal and unbounded, bools are
`0`/`1`, strings are a code-point count plus a text in which every code point
outside printable non-backslash ASCII is `\<lowercase-hex>;` — one escape
form, no spaces in the result, so a record still splits on spaces and the
empty string is a trailing space.  The dump is the *value*, not the
representation: the three `@[computed_field]`s (`Name.hashData`,
`Level.hashData`, `Expr.data`) are never written, and the Rust reader
recomputes them.

**Fixture results** (`scripts/dump-fixtures.sh`, the enumeration of
`vendor/con-leche/tests/arena.sh` — the three expectation files, the gzipped
e2e streams gunzipped, the arena tarball extracted to `_tmp/arena-tests`):

| | |
|---|---|
| fixtures (arena 138 + e2e 195 + annot 15) | **348** |
| round trip exact (structural equality, byte-identical re-dump, same `checkDecls .verified` verdict on both lists) | **315** |
| round trip failures | **0** |
| no declaration list (frontend declines 9, rejects 23, one truncated stream) | 33 |
| `verdict-exit` vs `tests/{arena,e2e,annot}-expected.txt` | **348 agree, 0 differ** |
| whole sweep, two `checkDecls` runs per fixture | **24.6 s** wall |
| total dump bytes | 6 905 866 |
| declarations / names / levels / propwhens / expr nodes, summed | 12 397 / 18 530 / 2 265 / 668 / 332 140 |

The 33 fixtures with no declaration list are exactly the streams con-leche
itself never folds — the arena `bad/tutorial/0{48..55,59,71},1{16,17,38}`
inductive-validation rejects, the e2e `ind_*_bad` redundant-field rejects, the
`ind_nest_*`/`tower_*`/`ind_unsafe` declines and `malformed_midstream` — and
each is reported with its frontend reason, never hidden.

**Scale** (the two large arena fixtures `arena.sh` does not itself run, plus
the largest e2e stream):

| input | bytes in | decls | expr nodes | dump bytes | parse | **write** | read | `checkDecls` |
|---|---|---|---|---|---|---|---|---|
| `good/perf/grind-ring-5` | 10 184 724 | 2 212 | 182 307 | 4 265 323 | 34 ms | **55 ms** | 148 ms | 114 ms |
| `good/init-prelude` | 3 714 854 | 1 803 | 55 862 | 1 293 237 | 14 ms | **19 ms** | 48 ms | 25 ms |
| `e2e/presieve_ofarrows_cone` | 1 272 397 | 534 | 20 792 | 455 885 | 7 ms | **7 ms** | 17 ms | 9 ms |
| `good/perf/app-lam` (the deep-term workload) | 1 276 513 | 27 | 24 446 | 479 915 | 5 ms | **6 ms** | 16 ms | 9 ms |

So the dump is **0.35–0.42×** the NDJSON it comes from, and **`String`
concatenation is fast enough**: the writer is an `Array String` line buffer
joined by a left fold, which is amortized linear because Lean's
`lean_string_append` grows a uniquely-referenced string in place (~78 MB/s
here).  No `ByteArray` writer and no handle writer was needed.  Reading is the
slow half (2.7× the write), which is `String.splitOn` allocating a token list
per line; a Rust reader will not have that problem.

**What surprised us about `DeclC`** — the list the Rust port must not get
wrong:

1. **`ExprC` *is* `ConLeche.Expr`** (con-leche tasks #172 B3a / #198): the
   cached tier's second expression type and the separate `ConstantValC` are
   both gone.  One node type, one `BEq`, one `Hashable` — and §3.1's "one Rust
   module per Lean file" must not be read as licensing a second.
2. **`indDecl` carries the *installed* `ConstantInfo`**, not a parse-level
   type, so a parsed declaration transitively contains `IndCaps`, `RecRule`
   (with `RecRuleFire`) and `ProjTable`.  Five `RecRule` fields —
   `ctorParams`, `fire`, `k`, `eta`, `paramsBlind` — are *install*-computed
   and carry parse placeholders.  The census over all 348 fixtures confirms
   it: every one of the 2 715 parsed rules has `ctorParams = 0`,
   `fire = .inert`, `k = eta = paramsBlind = false`, and every one of the
   1 917 parsed `IndCaps` is the all-default record.  **The dump writes them
   anyway**, because a dump is a `List DeclC` and nothing below it may assume
   the frontend's habits.
3. **The parsed sub-language is a strict subset, and that is a testing gap,
   not a licence.**  Over 332 140 expression nodes the corpus produces **zero
   `fvar`** nodes, and over 6 514 `ConstantInfo`s **zero** `axiomInfo`,
   `defnInfo`, `thmInfo` or `projInfo` inside an `indDecl` block (only
   `indInfo` 1 917, `ctorInfo` 2 645, `recInfo` 1 952) — so `ProjTable` never
   appears in a dump at all.  The Rust reader must still implement them: they
   are constructors of the type `check_decls` takes.
4. **`BinderMeta` has exactly one field**, `pw : PropWhen`; the display
   `BinderInfo` was deleted (con-leche task #205).  A Rust `Binder` struct
   with a binder-info field would be a silent divergence in hashing and
   equality.
5. **`PropWhen` is opaque *and* canonical.**  Its representation is `private`
   (`never | always | one | two | many`, the last two carrying sortedness
   proofs) and the only public producers are `never` and `ifAllZero`, which
   **sort and deduplicate by `Name.cmp`** — a structural lexicographic order
   (`anonymous < str < num`, prefix first, then the payload) defined in
   `Kernel/PropWhen.lean` and nowhere else in the tree.  The dump goes through
   `toList?`/`ifAllZero`, and the Rust port must implement `Name.cmp` and
   normalise in its own constructor: equality *and hashing* of the datum are
   equality of the parameter set, and a non-canonical value breaks both.
6. **`IndCaps.sortZ` defaults to `ifAllZero []`**, which reads "zero at every
   valuation", not to `never`.  A Rust `Default` that picks the other one
   changes the structure-η rescue's guard.
7. **Unbounded `Nat`s reach the term layer**: `Literal.natVal` obviously, and
   `Name.num`'s component in principle (as for the `bvar`/`fvar`/`proj`
   indices).  §3.3's split — `ron::Nat` for the literal, `u64` for the indices
   — is what the reader has to implement, with an overflow a Rust-side
   failure.
8. **`ProjTable.bodies` is an `Array Expr` while `guards` is a `List Level`**;
   the format writes both as counted lists, and the Rust struct should not
   inherit the asymmetry.
9. **The taint-skip decline lives *above* `checkDecls`.**  Three fixtures
   (`sorry_use`, `tolerated_axiom_use`, `taint_skip_continue`) are pinned at
   exit 2 while `checkDecls .verified` *accepts*: con-leche's driver declines
   after an accepting fold when the frontend skipped a declaration for a
   tolerated axiom (`Main.lean`, the `taintSkipped.isEmpty` branch).  The
   harness reproduces that rule to keep its `verdict-exit` comparable; the
   Rust CLI (P4) will have to as well, and the *core* must not.

**Two implementation notes.**  The writer's `Expr` walk is an explicit
worklist (`Array (Expr × Bool)`, visit/emit), not recursion: `app-lam` reaches
term depths in the thousands and a recursive writer is a stack overflow
waiting for a bigger export.  And the round-trip comparison goes through
`BEq Expr` — con-leche's `Expr.beq`, which `@[csimp]` substitutes by the
memoised pointer-and-hash-guarded `Expr.beqMemo` — never through the derived
`DecidableEq`, which is an `O(tree)` walk on a shared DAG; `DeclC` derives no
equality at all, so `ConRon/Dump/Main.lean` spells one out structurally.

**Left for next time.**  No Mathlib-scale export was run (there is none in the
tree); the numbers above extrapolate to roughly 1 s of writing per 100 MB of
NDJSON.  The Rust reader is P1.6's other half, and `ConRon/Dump/FORMAT.md` §6
is its checklist.
### Task #11 — `Expr` (2026-09-12, Opus under Fable)

P1.2 (second half).  `ConLeche/Kernel/Expr.lean` from `BinderMeta` on —
the `Level` half (`:35-139`) was task #3's and lives in `src/level.rs` —
ported as `crates/con-ron-core/src/expr.rs`.  Charon and Aeneas both
succeeded on the **first** run again, with zero iteration and zero errors;
the generated Lean is in `_tmp/core-lean/` (gitignored, not elaborated —
P2).

**What is in it.**  `BinderMeta` and `Literal` with their `deriving`
instances spelled out; the seven data-word helpers (`satRange`, `packData`,
`hashOfData`, `bvarOfData`, `fvarOfData`, `lpOfData`, `hash32`, `satSucc`,
`satPred`); the ten-constructor `Expr` with its `@[computed_field] data`
formula as ten smart constructors; the four packed-word accessors (`hash`,
`hasLP`, `bvarBRaw`, `fvarBRaw`); `beqRecursive`; the structural equality;
`bvarPoolSize`/`mkBvar`; and the `Hashable`/`Eq2` dictionaries that make an
`Expr` a hash-map key.  26 cited blocks, 346 raw / **214 code** Lean lines.

**The data word is bit-exact, and that decided the arithmetic.**
`packData`'s `h * 2^32 + b * 2^16 + f * 2 + lp` is Lean `UInt64`
arithmetic, i.e. *wrapping*; Rust's `*`/`+` are checked, and Aeneas models a
checked overflow as `fail`.  The port therefore uses `wrapping_mul` /
`wrapping_add` (`core.num.U64.wrapping_add` is the one std primitive this
module adds to the crate's list, and Aeneas models it —
`Std/Scalar/WrappingOps/Add.lean`).  `satSucc` is the one helper that is
*not* a literal transliteration: Lean's `min (n + 1) satRange` is on a
`Nat`, and on the `u64` of §3.3 the `n + 1` would overflow at `u64::MAX`, so
the saturation test comes first (`if n >= 32766 then 32767 else n + 1`) —
the same function of the same value for every `u64`, and one that cannot
fail.  Everything else (`/ 4294967296`, `/ 65536 % 32768`, `% 2 == 1`) is
the Lean character for character; the tests pin the roundtrip and the
reserved bit 31.

**`bvarPool`: not ported, and the deviation is free.**  `bvarPool` is a
closed top-level `def : Array Expr` that Lean's runtime builds once at
module initialization and marks persistent (`lean_mark_persistent`), so
`mkBvar i` hands out a borrowed pooled node below 4 096.  Rust has no such
thing inside the Aeneas subset: a `static`/`const` cannot allocate an `Rc`
tree, and the lazy alternatives (`OnceLock`, `lazy_static`, an `unsafe`
mutable `static`) are all outside §3.4 — and Charon would in any case have
to model a global whose value is an allocation performed before `main`.
Threading a pool through the checker's state instead would change every
signature below it for a pure allocation win.  con-leche's own
`mkBvar_eq` (`:1033`, `@[simp]`) is the transparency argument that makes
dropping it free: `mkBvar i = .bvar i`, so the pooled and the fresh node are
the same *value* and no statement anywhere changes.  `mk_bvar` is therefore
`bvar`, citing `bvarPool`, `mkBvar` and `mkBvar_eq` together, and
`bvar_pool_size` is kept for the record.  The saving can come back in P1.6
as a Rust-side arena without touching the model, because the model is
`.bvar i` either way.

**`beq`: the pointer/word/descent triple, without the pair memo** — §3.2's
standing ruling, now cashed in.  `beqGo`'s memo apparatus (`EqPair`,
`EqPair.dflt`, `BeqMap`, `beqKey`, `beqBudget`, `BeqRes`, `BeqOut`,
`BeqOut.mk`, `withAddr`, `ptrDec`, `probeHit`, `beqDec` — 12 declarations)
is **not** ported, and with it go the `fuel`/`map` parameters, the
`Squash` quotient and the `Decidable`-valued result; `beqMemo` and `beq`
collapse into one `beq` over one `beq_go`.  What is left is exactly what
§3.2 licenses and what the official kernel's `expr_eq_fn` does without a
cache: `Rc::ptr_eq` → the computed-word compare → the constructor descent in
the cited arm order, with the pointer fast path kept at *every* level as in
`name::beq` and `level::beq`.  Aeneas has no addresses, so the memo is not
merely inconvenient but unmodelable; if measurement wants it back it returns
as one opaque function with a trust argument, not as this function's
parameters.  `beqRecursive` is ported anyway (nine lines, nothing calls it)
so that the gate stays in step with its source.

**Constructs that do not survive transliteration, and their replacements**
(all a-priori, as in tasks #3, #6, #7 and #9 — nothing was error-driven).

1. **`const` is a Rust keyword**, so the `.const` smart constructor is
   `mk_const`; the other nine keep their constructor's name.  (Task #6's
   `modulo` rule.)
2. **`max` on `UInt64`.**  Lean's `max` goes through `Ord UInt64`, which is
   not in the subset; `max_u64` is the two-line `if`.  It appears seven
   times in the `data` formula.
3. **The `@[computed_field]` is the smart constructors' business**, as for
   `Name` and `Level` (§3.2): each of the ten writes its own arm of the
   cited `data` equation into `ExprNode::data`, and nothing else ever does.
4. **Two `List` recursions** became index-carrying `*_from` helpers (the
   task-#3 pattern): `levels_beq_from` (the `us == vs` of the `.const` arm —
   `Level.isEquivList` is the *equivalence*, not this) and `str_copy_from`
   (a `Vec<u32>` copy, with the accumulator passed by value and returned per
   task #6's rule).
5. **`deriving DecidableEq`/`Hashable` are spelled out.**  `binder_meta_beq`
   goes through `PropWhen.decEq` rather than a derived structural walk, and
   `literal_hash` is the derived shape (constructor index, then `mixHash`
   folded over the fields — `Lean/Elab/Deriving/Hashable.lean:50`, task #9's
   reading) over the crate's own `Nat` and string hashes, which already
   differ from Lean's.  §3.2 makes that free.
6. **Charon expands the wildcard arm.**  `beq_go`'s single `_ => false`
   becomes nine explicit `ok false` arms inside each of the ten
   constructor matches, so 78 lines of Rust come out as 181 lines of Lean.
   Harmless, and the same phenomenon as task #3's `&&` expansion — but it
   means a ten-constructor pairwise match is the module's whole size story.

**Numbers.**

| | |
|---|---|
| Lean ported (26 cited blocks of `Expr.lean`) | 346 raw / **214 code** |
| `src/expr.rs`, extracted part (raw / code) | 709 / **404** (1.9× the Lean code) |
| `src/expr.rs`, `#[cfg(test)]` part (13 tests) | 449 / 375 |
| generated `_tmp/core-lean/Types.lean` (whole crate) | 269 (76 of them `expr`) |
| generated `_tmp/core-lean/Funs.lean` (whole crate) | **4 045** (727 of them `expr`, 1.8× its Rust code) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 |
| `charon cargo --preset=aeneas` wall (after `cargo clean`) | **0.34 s** |
| `aeneas -backend lean -dest _tmp/core-lean -split-files -loops-to-rec` | **1.95 s** (1.76 s self-reported) |
| items translated (whole crate) | 226 transparent fns, 26 opaque, 5 globals, 11 trait decls (8 emitted), 24 trait impls (14 emitted) |
| `partial_fixpoint` (whole crate / `expr`) | **67** / **3** (`beq_go`, `levels_beq_from`, `str_copy_from`) |
| `mutual` blocks | 1 in `Funs.lean` (still task #3's 8-function `leq_core` knot, 313 lines) — `expr` adds **none**; 3 in `Types.lean`, of which `expr` adds one (`ExprKind`/`ExprNode`/`Expr`) |
| external holes | **exactly the four `Rc` axioms of §3.2** — `new`, `clone`, `deref`, `ptr_eq`.  The 26 opaque functions are all `core`/`alloc` primitives Aeneas already models; `expr` adds one to the list, `core.num.U64.wrapping_add` |

`cargo build`/`cargo test` warning-free, **53/53** green (40 from tasks
#6-#9 + 13 new); `scripts/lint-rust-style.sh crates/con-ron-core/src`
clean; `scripts/provenance.py check` green — 333 items, 200 citations, all
current at pin 3e004805.

**Tests** (`#[cfg(test)]`, invisible to Charon).  Thirteen: the packed
word's roundtrip over 6 × 6 × 6 × 2 field combinations, with bit 31
asserted clear and `hashOfData ∘ packData = hash32` checked against a
too-wide hash; `satSucc`/`satPred` at 0, 1, 32 764-32 767, 10^6 and
`u64::MAX`, with every stored range asserted `< 2^15`; **`bvarB` saturation**
— exact at 0, 4 095, 32 765, pinned at 32 766 and above, and a `lam` over a
saturated body staying saturated while a `lam` over `.bvar 5`/`​.bvar 0`
gives 5/0 (and the `fvar` range doing the same without descending into the
annotation); the range and `hasLP` recurrences constructor by constructor;
**`beq` on shared and on unshared-but-equal DAGs** — every term of a
14-element battery against its own `dup` (pointer path) and against a
from-scratch rebuild of the whole battery (14 × 14, equal exactly on the
diagonal), plus a self-sharing DAG against its fully expanded tree and
three one-node perturbations of it; `beq` separating every constructor and
every field, including `lam` vs `forallE` at identical fields and a
`const`'s level list by length and by entry; **hash equality of
structurally equal terms built separately** — the battery's `data`, `hash`,
`hasLP` and both ranges pairwise equal, no collision within the battery, and
a shared subterm's word equal to its rebuilt twin's; the `Hashable`/`Eq2`
dictionaries being `hash` and `beq`; `beqRecursive`'s six constructors;
`mkBvar = bvar` at 0, 1, 4 095, 4 096, 10^5; and the `BinderMeta`/`Literal`
helpers (canonicity makes `{u,v}` and `{v,u}` one datum with one hash).

**Deliberately not ported** (recorded so the next task does not re-derive
it): the twelve memo declarations above; every `theorem` — the packing
roundtrip (`:210-283`), the constructor-wise range and `hasLP` equations
(`:450-675`), `beqMemo_eq` (`:965`), `mkBvar_eq` (`:1033`) — plus the
`@[csimp]` lemma `beq_eq_beqMemo` (`:980`) and the `LawfulBEq Expr` instance
(`:986`), which are the *spec* this port will be proved against; `deriving
Repr` and the `Repr` instances (rendering only, §3.1); `deriving Inhabited`
on `Expr` and `instance : Inhabited BinderMeta` (`:106`), since `Vec`
indexing is checked in the model and the port needs no `Array.get!` default.
Note that `Expr.bvarB`/`Expr.fvarB` (the *exact* accessors, which fall back
to a memoized walk on the saturated branch) and the whole `isApp`/`getAppFn`
family are **not in this file** — they live in `ConLeche/Kernel/ExprOps.lean`
(82 declarations, 0 covered), a later task.

**Coverage** (`scripts/provenance.py coverage | tail -3`), con-leche
3e004805: **TOTAL 73/1018 covered (7.2 %), 945 uncovered** — up from task
#9's 51/1018 (5.0 %).  `Expr.lean` goes 8/42 → **30/42**, and the twelve
uncovered are exactly the memo apparatus listed above, so the ledger agrees
with the prose once more.

### Task #12 — Extraction pipeline and gates (2026-09-12, Opus under Fable)

P2 of §5: `crates/con-ron-core` now becomes committed, building Lean under
`proof/ConRon/Generated/` by one script, with a freshness gate, and
`scripts/gates.sh` is the single command a task runs before committing.

**The flags, and the one that mattered.**

```sh
# in crates/con-ron-core
charon cargo --preset=aeneas --dest-file <abs>/con_ron_core.llbc
aeneas -backend lean -split-files -loops-to-rec \
  -dest <work>/lean -subdir ConRon/Generated -namespace ConRon.Generated \
  -no-progress-bar <abs>/con_ron_core.llbc
```

**`-subdir` is the answer to "how do the files import each other as
`ConRon.Generated.*`": no `sed` post-processing is needed.**  It sets both the
output sub-path and the import prefix, so with `-dest proof -subdir
ConRon/Generated` Aeneas writes `proof/ConRon/Generated/Funs.lean` containing
`import ConRon.Generated.Types`.  `-namespace ConRon.Generated` is a separate
knob — it names the *Lean namespace* of the definitions, so a ported Rust
function `level::zero` is `ConRon.Generated.level.zero` (Aeneas keeps the Rust
module path as the definition-name prefix; it does not capitalise it).  Two
smaller findings: `charon cargo --dest` is deprecated in favour of
`--dest-file`, and **the destination must be absolute** — a relative one is
resolved against the workspace root rather than the crate directory, and
charon then silently writes nothing where you asked.

**Determinism and idempotence, measured, not assumed.**  Two full runs produce
byte-identical `Types.lean`/`Funs.lean`/templates (`md5sum -c` after a second
`extract.sh`), and a run from a *different* working directory produces the
same Lean as well.  The intermediate `.llbc` is **not** byte-stable — it
records the absolute output path, so the same crate extracted to two
directories gives two different `.llbc` files — but the Lean it produces is
identical, which is what is committed.  That is why the freshness gate diffs
the Lean and never the `.llbc`.

**What is generated and what is hand-written.**  `extract.sh` overwrites
exactly four files — `Types.lean`, `Funs.lean`, `TypesExternal_Template.lean`,
`FunsExternal_Template.lean` — and never touches `TypesExternal.lean` /
`FunsExternal.lean`, the four `Rc` models of §3.2 (copied from
`ConRon/Spike/LevelName/*External.lean`, three lines changed: the header
comment, `import ConRon.Generated.Types`, `open ConRon.Generated`).  The
script **fails if a template declares an external the hand-written file does
not model**, comparing the `@[rust_type "..."]` / `@[rust_fun "..."]`
attribute arguments as sets.  Two wrinkles in that comparison, both real bugs
the first time round: the attribute is sometimes *wrapped over two lines*
(`@[rust_fun\n  "alloc::rc::{core::ops::deref::…}::deref"]`), so the file is
flattened with `tr` first; and the hand-written `Rc` type carries
`@[reducible, rust_type "alloc::rc::Rc"]`, so the pattern must not anchor on
`@[`.  Both negative cases were exercised: renaming one modeled external makes
the script exit 1 with "does not model the external …", and appending a line
to `Funs.lean` makes `--check` exit 1 with the diff.

**The freshness gate.**  `scripts/extract.sh --check` regenerates into
`_tmp/extract-check/` and diffs against the committed tree; non-zero on any
difference, with the first 40 lines of each diff.  That is the CI rule
*committed generated code matches the crate*.  Cost: ≈2 s.

**Wiring it into the build cost a lakefile change.**  `ConRon/Generated.lean`
imports `Types` and `Funs`; `ConRon.lean` imports `ConRon.Generated`,
`ConRon.Refine.Smoke` and `ConRon.Dump.Read`.  It can **not** also import the
spike:

```
error: import ConRon.Spike.LevelName.TypesExternal failed, environment already
       contains 'alloc.rc.Rc' from ConRon.Generated.TypesExternal
```

Both trees carry their own copy of the §3.2 `Rc` model, and `alloc.rc.Rc` is a
top-level name (it has to be: Aeneas's generated code refers to it unqualified
from inside its own namespace).  The spike is therefore a **second library
root** — `lean_lib ConRonSpike` with `roots = ["ConRon.Spike.LevelName"]`,
`defaultTargets = ["ConRon", "ConRonSpike"]` — so a plain `lake build` still
elaborates both, in separate import graphs.  Nothing was moved out of
`ConRon/Spike/`.  The `*_Template.lean` files are committed but deliberately
*not* imported: they declare the same names as `axiom`s.  (A `lean_lib` builds
its roots' import closure, not every file under the directory, so they are
never elaborated.)

**Numbers** (this machine, Mathlib/Aeneas/con-leche already built).

| | |
|---|---|
| `charon cargo --preset=aeneas` wall | **0.30 s** (it drives rustc itself, so it recompiles every run — no `cargo clean` needed) |
| `aeneas` wall / self-reported | **1.4 s** / 1.22 s |
| `scripts/extract.sh` end to end | **1.7 s** |
| `scripts/extract.sh --check` | **2 s** |
| generated `Types.lean` / `Funs.lean` | 203 / **3 318** lines |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 |
| hand-written `TypesExternal.lean` / `FunsExternal.lean` | 36 / 58 |
| **total committed under `ConRon/Generated/`** | **3 692 lines** |
| items translated | 182 transparent fns, 25 opaque, 5 globals, 11 trait decls (8 emitted), 22 trait impls (12 emitted) |
| external holes | **exactly the four `Rc` axioms of §3.2** |

Lean, `lake build` of the whole `ConRon` tree from scratch (con-leche and
Aeneas oleans present): **14.3 s**, of which

| module | lines | `lake build` |
|---|---|---|
| `ConRon.Generated.TypesExternal` (hand-written) | 36 | 1.2 s |
| `ConRon.Generated.Types` | 203 | 1.6 s |
| `ConRon.Generated.FunsExternal` (hand-written) | 58 | 1.2 s |
| **`ConRon.Generated.Funs`** | **3 318** | **3.0–3.9 s** |
| `ConRon.Generated` (the root) | 17 | 1.2 s |
| `ConRon.Refine.Smoke` | 106 | 1.3 s |
| `ConRon.Spike.LevelName.*` (unchanged, second root) | — | 1.2–5.6 s |

**≈1 ms/line: confirmed, and if anything conservative.**  Against a three-line
baseline file carrying `Funs.lean`'s own imports (1.84 s of pure import under
`lake env lean`), `Funs.lean` takes 4.41 s — **2.57 s net over 3 318 lines,
0.77 ms/line**.  `Types.lean` is 0.31 s net over 203 lines (1.5 ms/line —
mutual inductives with their `SizeOf` and `_simpLemma_` boilerplate are the
expensive kind).  The whole generated crate is ≈2.9 s of net elaboration.
Task #4's spike measured 0.9 ms/line on 1 354 lines; at 2.7× the size the
figure did not move, so the cost is linear in generated lines at this scale.
Lean's profiler on `Funs.lean`: import 0.93 s, "process pre-definitions" (the
`partial_fixpoint` machinery, 64 of them) 0.21 s in total, type checking
0.06 s, LCNF compilation 0.02 s — again *not* where the time goes.
Extrapolating §4's ≈145k generated lines: ~2 minutes of elaboration plus the
~1.2 s per-file import tax, i.e. §6's risk 1 remains a file-count question.

**`ConRon/Refine/`, and that the spike's conventions really do port.**
`README.md` fixes the naming rule — a generated function is
`ConRon.Generated.<module>.<fn>`, its refinement lemma is
`ConRon.Refine.<Module>.<fn>_refines` in `ConRon/Refine/<Module>.lean` — and
records that all three task-#5 conventions (exact result on success; `NameWF`/
`LevelWF` as inductive predicates whose constructors are the port's own smart
constructors; `ptr_eq = false` plus `*_beq_refl`) carry over by renaming
`level_name.` to `ConRon.Generated.` and nothing else.  `Smoke.lean` proves
that end to end on the *generated crate code*: the spike's `absString` /
`absName` / `absLevel` verbatim except for the namespace, three plumbing
lemmas (`bind_eq_ok_iff`, `rc_new_eq`, `rc_deref_eq`), and

```lean
theorem level_zero_refines {u} (h : level.zero = ok u) : absLevel u = .zero
theorem level_succ_refines {a u} (h : level.succ a = ok u) :
    absLevel u = .succ (absLevel a)
```

with the spike's proof scripts unchanged (`simp [level.succ, level.hash_data]
at h; obtain ⟨_, _, rfl⟩ := h; rw [absLevel, absLevelNode, absLevelKind]`).
`level_succ_refines` is the one that goes through `level.hash_data`,
`name.mix_hash` and the `Rc` model, so it exercises the whole pipeline.  Two
lemmas on purpose; the real abstraction tier is P3.1.  Nothing was moved out
of `ConRon/Spike/` — it stays as task #3/#5's evidence.

**`scripts/gates.sh`.**  The one command every task runs before committing
(§3.5, `CLAUDE.md`), in order, stopping at the first failure, one OK/FAIL line
each, full logs in `_tmp/gates/`:

```
OK   cargo-build            (0s)     RUSTFLAGS=-D warnings
OK   cargo-test             (4s)     40/40
OK   lint-rust              (0s)     scripts/lint-rust-style.sh
OK   provenance             (0s)     282 items, 154 citations, pin 3e004805
OK   extract-check          (2s)     scripts/extract.sh --check
OK   lake-build             (1s)     cd proof && lake build
gates: all 6 OK                      7 s total
```

`cargo` is run with `RUSTFLAGS="-D warnings"` because §7's "warning-free" is
not something `cargo build` enforces on its own.

**Surprises worth keeping.**

1. `-subdir` exists and does exactly the right thing; the task's fallback
   (`sed` the import lines) was not needed.
2. `charon cargo --dest`/`--dest-file` silently ignores a path given relative
   to the crate — it is resolved against the workspace root.
3. The `.llbc` is path-dependent and therefore not a suitable gate artifact;
   the Lean is.
4. Two copies of the `Rc` model cannot coexist in one Lean import graph.  This
   is a standing constraint: the moment a second crate is extracted it needs
   its own library root, or the models need to be factored into one module
   that both `*External.lean` files import (which would, in turn, need the
   `@[rust_type]`/`@[rust_fun]` coverage check to follow imports).
5. `lake build` is *not* warning-free overall — the replayed Aeneas library
   modules emit `linter.dupNamespace` / `linter.ambiguousOpen` /
   `linter.defProp` warnings of their own, as they did at task #4.  Every
   con-ron file (generated and hand-written) elaborates with **zero** output
   under `lake env lean`, which is the property the gate is really about.

**Left for next time.**  No CI configuration exists yet (there is no workflow
file in the tree); `scripts/gates.sh` is the whole gate and a CI job is one
line calling it.  The `#print axioms` census of tasks #4/#5 is still checked
by hand rather than by a `#guard_msgs` in a file `lake build` elaborates — the
generated model is axiom-free today, and that is the baseline for such a gate.
### Task #14 — Environment and state types (2026-09-12, Opus under Fable)

P1.2's second half: the *types* the checker is written against, and their
small operations.  Five new modules — `core_types`, `env`, `fenv`,
`state_c`, `parsed_c` — covering `ConLeche/Kernel/Core.lean:45-59`, all of
`Kernel/Env.lean`, all of `Kernel/FEnv.lean`, the state half of
`Cached/StateC.lean`, and the three declaration records
(`Cached/ParsedC.lean`'s `DeclC`, `Kernel/CheckerSplit.lean`'s
`ValueKind`/`ValueGroup`, `Cached/Installed.lean`'s `PendingCheck`).  Charon
succeeded on the first run; **Aeneas did not**, for the first time in the
port — five errors, all borrow-shaped, all fixed by a-priori-legal
restructuring (below).  The generated Lean is in `_tmp/core-lean/`
(gitignored, not elaborated — P2).

**The `String` decision, measured** (`_tmp/strspike`, a throwaway crate run
through `charon`+`aeneas`).  `CheckError`'s three payloads are `Vec<u32>`
code points, as DESIGN.md §3.3 has every other string in the core.  The task
asked for the comparison rather than the assumption, and it is decisive:

| payload | `Types.lean` | constructing it |
|---|---|---|
| `String` | `String → ErrS` — Lean's own `String`, fine | `String::from("…")` emits the axiom `alloc.string.String.Insts.CoreConvertFromShared0Str.from : Str → Result String`; `String::new()` emits `alloc.string.String.new` — **a fifth external hole either way** |
| `&'static str` | `Str → ErrR`, fine | Aeneas **fails**: *"There should be no bottoms in the value"*, and the constructor comes out `sorry` |
| `Vec<u32>` | `alloc.vec.Vec Std.U32 → ErrV` | `Vec::new`, a `[u32; N]` const, `Array.to_slice` and a slice walk: **no hole at all** |

§3.2's standing gate is that the external templates hold exactly the four
`Rc` axioms, so a string-shaped fifth is not free — and §3.1 already says
message strings need not match, because the theorem never reads them.  So
the idiom for a throw site is a `const M_…: [u32; N]` of ASCII code points
beside it and `core_types::code_points(&M_…)`; the same helper is how the
port spells *any* Lean string literal, `env::proj_fn_name`'s `"proj"`
included.  `CheckM α = Except CheckError` is `Result<T, CheckError>`
(`pub type CheckM<T>`, erased before Charon), `CheckCM α = StateT CState
CheckM α` is `fn(…, &mut CState) -> CheckCM<A>`, and `x ← m; k x` is an
explicit `match` because §3.4 forbids `?`.

**The `FEnv` sharing decision: linear threading, not `Rc`.**  In the Lean,
`restrictTo` is `{ fe with visibleBelow := k }` and `push` a three-field
rebuild; both are `O(1)` *because the runtime shares the `Std.HashMap`
field*, and both leave their argument intact.  Three options were on the
table.

1. `idx: Rc<HashMap<…>>` — `restrict_to` is then two `Rc::clone`s, but
   `push` has no way to mutate the map: `Rc::get_mut`/`make_mut`/
   `try_unwrap` are all outside §3.4's `Rc` whitelist, and `env: Env` would
   need its own `Rc` too or the `Vec<ConstantInfo>` copy defeats the point.
2. `restrict_to(&mut FEnv, k)` — `O(1)` and minimal, but §3.4 reserves
   `&mut` for the state parameter and an `FEnv` is not state.
3. **Both by value, returned** — `restrict_to(fe: FEnv, k) -> FEnv` and
   `push(fe: FEnv, ci) -> FEnv`.  This is literally the cited record update
   (a move plus one field), `O(1)`, no clone, no `Rc`, no `&mut`, and it is
   task #6's own rule for accumulators.

**(3) is what landed.**  The *semantics* are the Lean's exactly —
`find(&restrict_to(fe, k), n) = (fe.restrictTo k).find? n` — and what
changes is only that the caller no longer holds the pre-restriction value
and must restore the bound instead of keeping two views.  That is enough
here because of §1/§3.6's phase split: in the Rust port phase A is
*finished* before any check runs, so pushes and restrictions never
interleave, and phase B needs exactly one view at a time (it lowers the
bound for a record and raises it back).  The one design this forecloses is
the *parallel* phase B §3.1 contemplates, where several workers hold
different views of one index at once; that is a one-field change when it
comes (`idx: Rc<HashMap<…>>`, with `push` moving to an install-phase type
that owns the map outright) and it does not touch the model, because `abs`
reads the index through `find` either way.  A separate `fenv::dup` exists
for the harness and the tests, and rebuilds the index with `mk_fenv_go`
rather than copying it entry by entry — `crate::hashmap` has no iteration
API by design, and the rebuild *is* the definition of the counters.

**Lookups return a borrow.**  `Env.find?`/`FEnv.find?` are
`Option<&ConstantInfo>`, not `Option<ConstantInfo>`: Lean shares the stored
record, and a Rust copy would be `O(size)` per lookup (task #9's "Lean's
sharing costs a copy").  For the same reason `ConstantInfo.name` and
`.type` are spelled as direct matches instead of going through
`toConstantVal`, which is ported faithfully but copies a `Vec<Name>`.

**Constructs that do not survive transliteration, and their replacements.**

1. **`type` is a Rust keyword**, so `ConstantVal.type` is `ConstantVal.ty`
   (task #6's modulo rule).  `opaque`/`abbrev`, which the Lean writes in
   `«»`, are ordinary Rust identifiers and keep their names.
2. **Field defaults do not exist in Rust.**  `RecRule`'s five
   install-computed fields and all eight of `IndCaps`' become explicit
   constructors, `env::rec_rule_parsed` and `env::ind_caps_default` — which
   is also where the two task-#10 surprises are pinned in code and in a
   test: every parsed rule is `ctorParams = 0`, `fire = .inert`,
   `k = eta = paramsBlind = false`, and `IndCaps.sortZ` defaults to
   `ifAllZero []` ("zero at every valuation"), **not** `.never`.
3. **`default : Expr`.**  `ProjTable.entry`'s `bodies.getD i default` needs
   the value task #11 deliberately did not port; `env::default_expr` is the
   derived `Inhabited` (`Expr.lean:403`), i.e. the first constructor at its
   arguments' defaults, `.bvar 0`.  `guards.getD i .zero` is the other
   `getD`.
4. **Six `List` recursions became index-carrying helpers** (task #3's
   pattern): `find_from` (the `List.find?` with its predicate inlined),
   `ind_params_ok_from`, `recs_form_suffix_from`/`all_rec_info_from`,
   `mk_fenv_go`, `tower_slots_all_f_from`/`rec_slots_all_f_from` (the
   `(List.range nF).all`s), `subst_level_trees_from`
   (`is_equiv_list_l_m_from` is the seventh, see 7 below).  Five `*_copy`
   helpers stand for what Lean's value semantics gives free:
   `levels_copy`, `exprs_copy`, `rec_rules_copy`, `constant_infos_copy`,
   `core_types::code_points`.
5. **`Env.consts` is a `Vec` in the Lean's own newest-first order**, so
   `push`'s `ci :: fe.env.consts` is a front insertion, `O(n)` where Lean's
   is `O(1)`.  Deliberate and documented: the list is on no hot path (every
   lookup goes through the index; `consts` is read by `mk_fenv` and by the
   driver's final environment), and keeping the order is what makes an
   index counter "the position counted from the bottom".
6. **Tuple memo keys carry hand-written derived instances.**  Five
   `Hashable`/`Eq2` pairs — `(Name, Vec<Level>)`, `(Name, Name,
   Vec<Level>)`, `(Expr, Expr)`, `(Level, Level)`, `(Expr, Vec<Expr>,
   u64)` — spelling Lean's derived ones: `Hashable (α × β)` is
   `mixHash (hash a) (hash b)` (`Init/Data/Hashable.lean:18`) and a Lean
   triple is `(a, (b, c))`, so a three-component key hashes **right-nested**,
   not as a flat fold; `Hashable (List α)` is `foldl mixHash 7` (`:37`),
   which is emphatically *not* con-leche's own `levelsHash` (seed 13, right
   fold — that one hashes a `.const` node's level list, the memo key uses
   the derived instance); `Hashable Nat` is `UInt64.ofNat`, i.e. exactly
   `hashmap.rs`'s identity `impl Hashable for u64`.  A unit test pins the
   two fold shapes and asserts `levels_list_hash ≠ levelsHash`.
7. **`isEquivListLM`'s arm order is load-bearing.**  The cited three-arm
   `List` recursion answers `some false` on a length mismatch only *after*
   walking the common prefix, so a `none` from an earlier pair still wins;
   a length pre-check would be a different function.  The index version
   tests `i >= ls.len() && i >= rs.len()` / both in range / else.
8. **con-leche's linear-update discipline has no Rust counterpart.**  `let
   mp := s.instC; let s := { s with instC := {} }; … mp.insert …` detaches a
   component so Lean's runtime sees a unique reference; `s.inst_c.insert(…)`
   on a `&mut CState` *is* that in-place update, so the dance is dropped and
   the insertions kept.  `CState.flushed` is `&mut` for the same reason
   (`CState` is the state parameter §3.4 reserves it for) and uses
   `HashMap::clear`, which task #7 documented as exactly this `{ s with … :=
   {} }`, keeping the bucket allocation.
9. **A `CheckCM` action whose body is `pure e` is the plain Rust function
   `e`** — the state argument would be dead weight and dead Lean.  That is
   `peel_fuel` (= `peelFuel` and `peelFuelM`) and `subst_level_trees`
   (= `substLevelTreesM`).

**Aeneas needed three iterations' worth of restructuring — the first
error-driven change in the port.**  The first run gave five errors in five
functions, two distinct: *"Could not match the contexts"* and *"Internal
error, please file an issue"*.  All five shared one shape — **a borrow taken
from a shared structure, consumed into a scalar, and then joined with a
branch that re-borrows or mutates the same structure**:

* `env::ind_params_ok_from` and `fenv::rec_slots_all_f_from` computed `let
  ok = match &block[i] { … }` / `let ok = match find(fe, …) { … }` and then
  branched on `ok` before recursing.  Fix: lift the per-element test into
  its own function (`ind_params_ok_one`, `rec_slot_ok`) and make the caller
  `if helper(…) { recurse } else { false }`, so the borrow dies inside the
  callee.  `rec_slot_ok` also stopped matching `Some(ConstantInfo::RecInfo
  (..))` through the `Option<&…>` and calls `env::is_rec_info` instead,
  which is the cited arm anyway.
* `state_c::simplify_l_m`, `is_non_zero_l_m` and `is_equiv_l_m` probed the
  memo with `match s.<map>.get(k) { Some(r) => Some(dup(r)), None => None }`
  where `s : &mut CState`, then wrote to `s` in the miss branch.  Fix: three
  probe functions over a **shared** state borrow (`lsimp_probe`,
  `lnz_probe`, `eqv_probe`), so the map's borrow ends at the call boundary.

Both fixes are improvements on their own terms — the probe functions are the
Lean's `s.lsimpC[u]?` as a named thing, and the per-element tests are the
`List.all` predicate as a named thing — so nothing was contorted to please
the tool.  After them: **zero errors, zero warnings.**  Worth recording for
the next porter: this is the first module set in which a `&mut`-threaded
state meets a `&`-returning container API, and the rule that came out of it
is *never hold a container's borrow across a branch that touches the
container* — factor the probe.
### Task #13 — `ExprOps` (2026-09-12, Opus under Fable)

P1.3.  `ConLeche/Kernel/ExprOps.lean` (2 753 lines, 82 declarations, 0
covered) ported as `crates/con-ron-core/src/expr_ops.rs`.  Charon and Aeneas
both succeeded on the **first** run again, with zero iteration and zero
errors; the generated Lean is in `_tmp/core-lean/` (gitignored, not
elaborated — P2).

**What is in it.**  All **70** executable `def`s of the file, as 87 Rust
functions: the three substitution walks (`instantiate1`, `instantiateList`,
`instantiate1Lift`), the two shift walks (`liftLooseBVars`, `lowerBVars`),
`resetMeta`, `renameConsts`, the two abstraction walks (`abstract1`,
`abstractRange`), the spine and telescope family (`getAppFn`, `getAppArgs`,
`mkAppN`, `stripLams`/`stripPis`, `piResult`, `instPis`,
`instPisAt`/`instLamsAt` and their one-pass `*F` twins, `fvarTypeD`,
`instSpine`, `recRulePlain`, `pisToLams`, `replacePiBody`, `piArity`,
`resultSort`, `instPisAtLift`), the leaf predicates (`sizeB`, `sizeF`,
`fvarLeaves`, `wscopedB`, `isLam`, `lamPw`, `forallPw`, `exprPtrBEq`), and
the derived-field block — `bvarBound`, `fvarRange`, their memoized twins
`bvarBoundGo`/`bvarBoundMemo` and `fvarRangeGo`/`fvarRangeMemo`, and the
exact accessors `bvarB`/`fvarB` with `looseBVarsBounded`/`hasFvar` reading
them.

**The `@[csimp]` families are one Rust function each, and the lemma is the
transparency argument.**  con-leche writes eleven of these walks twice — a
plain structural `def` that every proof consumes, and a memoized
`*Go`/`*Fast` pair that a `@[csimp]` lemma substitutes into compiled code.
The port implements the **`*Fast`** member, because that is what con-leche
*executes* (§3.1 is about the executed program), and each such Rust item
carries three or four citations: the `*Go` walk it transliterates, the
logical `def` it stands for, the `*Fast` wrapper, and the `@[csimp]` lemma.
That lemma is exactly the deviation note's argument: it is a kernel-checked
equation `@f = @fFast`, so the Rust function refines the logical definition
by the same equation and no proof downstream ever sees the memo.  Two of the
eleven — `hasFvar` and `looseBVarsBounded` — have a `*Fast` member that is
not a walk at all but the `O(1)` packed-word read, `fvarB != 0` and
`bvarB ≤ k`; those are one-line Rust functions whose citations are the walk,
the field read and the lemma chain (`bvarB_eq`, `looseBVarsBounded_iff`).

**Memos are `&mut` parameters, and that is what makes the generated Lean
match.**  Every memo in `ExprOps.lean` is *local*: created empty inside the
`*Fast` wrapper and dropped on return, because the answer also depends on
parameters that are not in the key (`v`, `vs`, `amount`, `d`, `f`,
`ks`/`us`).  The port creates a `crate::hashmap::HashMap` in the wrapper and
hands it down as `&mut`.  §3.4 reserves `&mut` for the state parameter — and
the memo *is* this walk's state; more to the point, Aeneas's back-end
translates a `&mut` parameter into a threaded return, so
`instantiate1_go (v memo e d) : Result (Expr × HashMap …)` comes out with
con-leche's own signature `instantiate1Go v memo e d : Expr × Std.HashMap …`
rather than an `&mut`-shaped artefact.  No memo in this file lives in
`CState`; those are `ConLeche/Cached/*`'s business (`ExprOpsC.lean`, 0/37
covered, a later task).

The key type `(Expr × Nat)` becomes a two-field `ExprNatKey` with its own
`Hashable`/`Eq2` dictionaries (task #7's traits), standing for Lean's derived
`instHashableProd`/`instBEqProd`; the node half of the equality is
`Expr.beq`, so §3.2's pointer and packed-word fast paths sit inside the
memo's key comparison, as they do for `Name` and `Level`.

**`bvarB`/`fvarB`: the saturation boundary is the whole point.**
`Expr.bvarBRaw`/`fvarBRaw` (task #11) are 15-bit fields that saturate at
`satRange = 32767`; `bvarB`/`fvarB` stay *exact* by falling back, on the
saturated branch alone, to a memoized recomputation of the same recurrence.
The port is the cited `if r == satRange then memo else r` character for
character, so nothing downstream grows a saturation guard — `bvarB_eq` and
`fvarB_eq` remain plain equations with the spec functions.  The spec
functions `bvarBound`/`fvarRange` are ported too, unmemoized and uncalled,
so that the gate stays in step with their source (task #11's `beqRecursive`
rule).  Their `body.bvarBound - 1` is Lean's *truncated* `Nat` subtraction,
which on `u64` would underflow into an Aeneas `fail`: hence the module's one
new helper, `sub_nat`.  It is used in exactly three places — that `- 1`,
`instSpine`'s `t - 1` and `recRulePlain`'s `mI - 1 - k`; everywhere else the
Lean arm carries a guard (`i > d`, `i ≥ c + amount`, `j - d ≥ vs.length`)
that makes the direct subtraction safe, and the port subtracts directly.

**`instantiateLevelParams` came with it, and three `Level.lean` gaps closed.**
`Expr.instLPGo`/`instLPFast` are *in* `ExprOps.lean`, but the logical
definition they replace (`Expr.instantiateLevelParams`) is spelled in
`Kernel/Level.lean:232-249` for import order, and it needs
`Level.zeronessOf` (`:185`) and `Level.substPW` (`:197`) — the two blocks
task #3 deferred *only* because `PropWhen` did not exist yet.  Rather than
port half a family, the task filled those two into `src/level.rs`, where
their file belongs, and put the `Expr` operation in `expr_ops.rs`.
`substPW`'s function argument is task #9's pattern again: a one-method
`NameToPw` dictionary, here `level::SubstZ<'a>` holding `ks`/`vs` by shared
reference — **the first region-parameterised dictionary struct in the crate,
and Aeneas translated it with no complaint** (it appears in `Types.lean` as
an ordinary two-field structure).  `renameConsts`'s `f : Name → Name` is the
same pattern, `expr_ops::NameToName`.  `Level.hasParam` (`:2399`) is not a
new function — it is the spec recurrence of `Expr.levelHasParam`, which task
#3 already ported as `level::level_has_param`, so it gained a second
citation there rather than a duplicate.  Still owed to a `Level.lean`
completion task: `Expr.allLevelParamsDefined` (`:256`) with its `LPMemoInv`,
`*Go` and `*Fast` (4 declarations).

**Constructs that do not survive transliteration, and their replacements**
(all a-priori, as in tasks #3, #6, #7, #9 and #11 — nothing was
error-driven).

1. **`match memo[k]? with` needs an owning probe.**  Rust's borrow checker
   keeps the map borrowed for the whole `match` when the scrutinee is
   `memo.get(&k)`, and every `none` arm needs the map *mutably*.  The three
   `memo*_get` helpers return an owned `Option<Expr>`/`Option<u64>` (an `Rc`
   bump for a hit), which ends the borrow at the probe.  A Rust artefact with
   no Lean content; the generated Lean is the cited `getElem?` either way.
2. **Identity arms return an `Rc` bump.**  `| .fvar idx ty => (.fvar idx ty,
   memo)` *rebuilds* a node in Lean; the port returns `expr::dup(e)`.  The
   same value, because `expr.rs`'s smart constructors are functions — and it
   is what keeps the DAG shared, which is why these walks are memoized at
   all.
3. **Lean's cons, three ways.**  `stripLams`/`stripPis`/`instPisAt`/
   `instLamsAt` cons the binder on the way *out* of the recursion; a `Vec`
   has no cons, so the port accumulates on the way *in* and gets the same
   outermost-first list.  `getAppArgs`'s `getAppArgs f ++ [a]` becomes a
   push *after* the recursive call — same order, one pass instead of a list
   per spine node.  `fvarLeaves`'s `++` becomes the same accumulator.  Only
   `instPisAtFGo`/`instLamsAtFGo` genuinely need a *front* cons (`a :: acc`,
   and `acc`'s order is what `instantiateList` reads), so `cons_expr`
   rebuilds the accumulator: `O(|acc|)` pointer copies per binder against
   Lean's `O(1)`, on a list with one entry per telescope binder.  The `*F`
   walks' actual point — one *tree* traversal per domain instead of one per
   argument — is untouched.
4. **`instantiateList`'s pure walk is genuinely called**, so both members of
   that family are ported: `instantiateListGo`'s `.bvar` arm defers to it,
   and its `vs.take (j - d)` is a `Vec` copy (`take_exprs`).
5. **`Option.map` over a closure** (`(stripLams k b).map fun (bs, e) => …`,
   and the same in `stripPis`, `instPisAt`, `instLamsAt`, `instPisAtFGo`,
   `instLamsAtFGo`, `pisToLams`, `replacePiBody`) → an explicit
   `match … { Some(r) => …, None => None }`.  §3.4 forbids closures;
   `pisToLams` and `replacePiBody` keep the build-on-the-way-out shape,
   because there is nothing to accumulate.
6. **`recRulePlain`'s list comparison.**  `dom.getAppArgs.take cnP ==
   (List.range cnP).map (fun k => .bvar (mI - 1 - k))` is a closure, a
   `take`, a `range` and a list `==`; it becomes one index recursion
   (`rec_rule_args_eq`) whose "ran out of arguments" arm reproduces the
   length mismatch a short `List.take` would produce.  Its `&&` cascade
   becomes an `if` nest (task #3's pattern 9), as do `wscopedB`'s.
7. **`withPtrEq`** in `exprPtrBEq` → `ptr_eq` then `beq`, with `ptr_eq`
   modeled as `false` (§3.2).  The obligation is `Expr.beq`'s reflexivity,
   which is what con-leche's own `(fun h => by subst h; simp)` discharges.
8. **A `Vec<(u64, Expr)>` for `List (Nat × Expr)`** (`fvarLeaves`) and
   `Vec<(Expr, BinderMeta)>` for the binder lists; Charon translates the
   tuples as ordinary products.

**Numbers.**

| | |
|---|---|
| Lean ported (64 cited blocks over 7 files) | 432 raw / **398 code** |
| — `Kernel/Core.lean` 1 block / `Kernel/Env.lean` 37 / `Kernel/FEnv.lean` 9 | 15 / 259 / 34 raw |
| — `Cached/StateC.lean` 13 / `Cached/ParsedC.lean` 1 / `CheckerSplit.lean` 2 / `Installed.lean` 1 | 104 / 7 / 9 / 4 raw |
| `src/core_types.rs` extracted (raw / code) | 167 / **58** |
| `src/env.rs` extracted (raw / code) | 890 / **555** |
| `src/fenv.rs` extracted (raw / code) | 250 / **117** |
| `src/state_c.rs` extracted (raw / code) | 569 / **294** |
| `src/parsed_c.rs` extracted (raw / code) | 91 / **36** |
| the five together, extracted / `#[cfg(test)]` | 1 967 / 795 raw; **1 060 code** (2.7× the Lean code) |
| generated `Types.lean` (whole crate) | **506** (253 of them this task's: `env` 150, `parsed_c` 53, `state_c` 33, `core_types` 9, `fenv` 8) |
| generated `Funs.lean` (whole crate) | **5 693** (1 650 of them this task's: `env` 735, `state_c` 652, `fenv` 162, `core_types` 91, `parsed_c` 10) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 — **unchanged** |
| `charon cargo --preset=aeneas` wall (after `cargo clean`) | **0.45 s** |
| `aeneas -backend lean -dest _tmp/core-lean -split-files -loops-to-rec` | **2.22 s** (2.01 s self-reported) |
| items translated (whole crate) | 408 declarations, 333 transparent fns, 31 opaque, 7 globals, 11 trait decls (8 emitted), 35 trait impls (24 emitted) |
| `partial_fixpoint` (whole crate / this task) | **85** / **18** (`env` 9, `state_c` 5, `fenv` 3, `core_types` 1) |
| `mutual` blocks | 1 in `Funs.lean` (still task #3's 8-function `leq_core` knot), 3 in `Types.lean` — this task adds **none**; every recursion is self-recursion and every new type is a flat record or enum |
| external holes | **exactly the four `Rc` axioms of §3.2** — `new`, `clone`, `deref`, `ptr_eq`, plus the `Rc` type axiom.  Nothing `String`-shaped; the 31 opaque functions are all `core`/`alloc` primitives Aeneas already models, and this task adds none |

`cargo build`/`cargo test` warning-free, **75/75** green (53 from tasks
#6-#11 + 22 new); `scripts/lint-rust-style.sh crates/con-ron-core/src`
clean; `scripts/provenance.py check` green — 472 items, 325 citations, all
current at pin 3e004805.

**Tests** (22, `#[cfg(test)]`, invisible to Charon).  `core_types`: the
code-point copy, `beq` separating kind from payload, and the `CheckM`
convention as a worked `Ok`/`Err` function.  `env`: the five mode accessors
at both constructors (and that `certs`, `verifiedChecks` and `betaGate`
agree everywhere, `Env.lean:97-101`) plus `betaSkip`/`ioSkip` at a `.never`
and a non-`.never` datum; `ReducibilityHint.lt` as the order `opaque <
regular h < abbrev` with its overlapping arms checked in both directions,
and `sameRegular` only at equal heights; `piSortTeleLen?` at 0/1/2 binders
and at a non-sort residual; `indParamsOk`'s one-sidedness (a too-short
telescope rejects, a constructor's declared count must match, an unfoldable
residual passes); the reserved names distinct and both of the shape
`Name.isProjFnShape` rejects; `Env.find?` newest-first and the two direct
accessors agreeing with `toConstantVal`; `ProjTable.entry` in range and at
both `getD` defaults, `findProj?` keyed on `projTableName` and `none` beyond
`numFields`, and a table's header being `Sort 1` under the reserved name;
`recsFormSuffix` on four tag patterns; and the `dup`s, including the two
task-#10 placeholder facts.  `fenv`: `mkFEnv` hiding nothing and agreeing
with `Env.find?`; push/restrict — three pushes, `mkFEnv_push` (pushing is
building afresh), the prefix views at `k = 0, 2, 3`, the bound restored, and
`dup` preserving bound and answers; **shadowing** — the newest binding wins
in the index as in the list, and the shadowed one is what the prefix view
hides; `findProj?`/`towerSlotsAllF`/`recSlotsAllF` at and beyond their
counts.  `state_c`: a **tuple-key map round trip on all five key shapes**
(structurally equal keys hit, component-permuted and truncated ones miss,
the `instC` depth is part of the key); the derived list hash being the
seed-7 left fold and differing from `levelsHash`; **`CState.flushed`** —
all ten environment-dependent maps emptied, `ienv` and the three
level-operation memos surviving with their entries intact; and the level
memo wrappers agreeing with `level::simplify`/`is_non_zero`/`is_equiv`/
`is_equiv_list`, hitting on the second call, and `l == r` answering `some
true` **without writing a cache entry**.  `parsed_c`: a `DeclC` list whose
`indDecl` block satisfies `recsFormSuffix` and `indParamsOk`, and a
`PendingCheck` carrying the seam.

**Skipped, "needs expr_ops"** (they read `ConLeche/Kernel/ExprOps.lean`,
which a concurrent task is porting as `src/expr_ops.rs`): `StateC.lean`'s seven
environment-index guards `isUnitLikeTyC`, `isCtorAppC`, `headHintC`,
`unfoldableHeadC`, `sameConstHeadsC`, `rawNatLitC?`, `etaCtorShapeC`
(`ExprC.getAppFn`, `Expr.getAppArgs`, and the pinned basis names of
`Kernel/Basis.lean`); `bvarBoundM` (`Expr.bvarB`, the *exact* accessor);
the nine syntactic wrappers `inst1M`, `instListM`, `instListRevM`,
`abstract1M`, `abstractRangeM`, `mkAppNM`, `instSpineM`, `piResidualM`,
`instLevelParamsM`; the two lazy stored-constant conversions `storedTyIdxM`
and `storedValIdxM` (`Expr.exprPtrBEq`) and, through them, `constTyAtM`,
`constValAtM`, `ruleRhsAtM`; and the memoized DAG walk
`constsResolveFCGo`/`constsResolveFC`.  `instCCapC` and the `instC` map
*are* here, because they are state.  From `FEnv.lean`: `andRescueSlotsF`
(`andRescueSlotsOf`, `Kernel/Core.lean`) and the four indexed guard twins
`natLitSupportedF`, `strLitSupportedF`, `natOpGuardF`, `natOpStoredF`
(`natIndOk`, `stringTyOk`, … and the pinned names, `Kernel/Basis.lean`).

**Deliberately not ported** (recorded so the next task does not re-derive
it): `Env.lean`'s `blockRecSuffixDec` (`:737`, the substituted `Decidable`
instance — the tag pass `recsFormSuffix` it delegates to *is* ported) and
its three `theorem`s (`compareParams_plain`, `compareParams_nested`, the
`recsFormSuffix_iff` pair) — the spec this port will be proved against;
`Core.lean`'s `instance : ToString CheckError` (`:53-57`, rendering only)
and `CoreFns`/`CoreFns.ioView` (`:61-96`, the record of closures — §3.1 ties
that knot with a mutually recursive block of wrappers, so it is not a type
this task can carry); `CheckerSplit.lean`'s `ValueKind.word` (`:45-48`,
a message string); every `deriving Repr`, `Inhabited` and `DecidableEq` on
the `Env.lean` records — con-leche uses the derived equality only in `Prop`s
and in the decision it substitutes away, and the executable comparisons the
checker does (`Name.beq`, `Expr.beq`, `sameRegular`'s `==`) are ported.
`DeclC` derives nothing in con-leche either, deliberately (task #10).

**Coverage** (`scripts/provenance.py coverage | tail -3`), con-leche
3e004805: **TOTAL 139/1018 covered (13.7 %), 879 uncovered** — up from task
#11's 73/1018 (7.2 %), the largest single jump so far.  Per file:
**`Env.lean` 37/38** (the one uncovered is exactly `blockRecSuffixDec`),
`FEnv.lean` 9/14 (the five needing `Core`/`Basis`), `StateC.lean` 12/38
(the 26 needing `ExprOps`/`Basis`), `CheckerSplit.lean` 2/6,
`ParsedC.lean` 1/10, `Installed.lean` 1/21, `Core.lean` 2/130 — so the
ledger agrees with the prose in every file.
| Lean ported: 70 cited `def` blocks of `ExprOps.lean` | 972 raw / **746 code** |
| plus 3 blocks of `Level.lean` (`zeronessOf`, `substPW`, `instantiateLevelParams`) | 40 raw / **25 code** |
| `src/expr_ops.rs`, extracted part (raw / code) | 1 913 / **1 348** (1.7× the Lean code) |
| `src/expr_ops.rs`, `#[cfg(test)]` part (18 tests) | 573 / 477 |
| `src/level.rs` delta (`zeronessOf`, `substPW`, `SubstZ`, one citation) | +64 / −5 |
| generated `_tmp/core-lean/Types.lean` (whole crate) | 289 (14 of them `expr_ops`) |
| generated `_tmp/core-lean/Funs.lean` (whole crate) | **9 096** (5 007 of them `expr_ops`, 3.7× its Rust code) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 |
| `charon cargo --preset=aeneas` wall (after `cargo clean`) | **0.47 s** |
| `aeneas -backend lean -dest _tmp/core-lean -split-files -loops-to-rec` | **4.49 s** (4.23 s self-reported) |
| items translated (whole crate) | 314 transparent fns, 26 opaque, 5 globals, 12 trait decls (9 emitted), 27 trait impls (17 emitted) |
| `partial_fixpoint` (whole crate / `expr_ops`) | **109** / **41** |
| `mutual` blocks | 1 in `Funs.lean` (still task #3's 8-function `leq_core` knot, 313 lines) — `expr_ops` adds **none**, every recursion is self-recursion; 3 in `Types.lean`, `expr_ops` adds none |
| external holes | **exactly the four `Rc` axioms of §3.2** — `new`, `clone`, `deref`, `ptr_eq`.  The 26 opaque functions are all `core`/`alloc` primitives Aeneas already models; `expr_ops` adds nothing to the list |

`cargo build`/`cargo test` warning-free, **71/71** green (53 from tasks
#6-#11 + 18 new); `scripts/lint-rust-style.sh crates/con-ron-core/src`
clean; `scripts/provenance.py check` green — 428 items, 309 citations, all
current at pin 3e004805.

The 3.7× Rust→Lean line ratio (against 1.8× for `expr.rs`) is task #11's
ten-constructor `match` phenomenon, squared: each of the eight memoized
walks matches on ten constructors *twice* — once for the memo-skipping
leaves, once inside the `none` branch — and Charon expands every wildcard
arm, so a 60-line Rust walk comes out as roughly 300 lines of Lean.  It is
mechanical noise, not complexity: the `partial_fixpoint` count (41 for 87
functions) and the absence of any new `mutual` block say the knot did not
grow.

**Tests** (`#[cfg(test)]`, invisible to Charon, so closures and loops are
allowed).  Eighteen.  `instantiate1` at, above and below the cursor and
under a binder; **an `instantiate1`/`abstract1` round trip on a DAG whose
`shared` subterm occurs three times** (so the memo is exercised), checked
back to the original term and with `hasFvar` true on the opened form and
false on the closed one; `instantiateList` as the fold of `instantiate1`,
with the pure and the memoized walk agreeing; `abstractRange` closing a
two-variable block outermost-first, bumping the cursor under a binder and
leaving an out-of-range index alone; `liftLooseBVars`/`lowerBVars` inverse
outside the window; `instantiate1Lift` shifting an *open* replacement where
`instantiate1` would not.  **The saturation boundary on synthetic data
words** — `expr.rs`'s smart constructors cannot produce a saturated word
without 32 767 real binders, so the tests build `ExprNode`s with a
hand-packed word: 32 766 still reads as the field, 32 767 sends `bvarB` to
the memoized walk and comes back with the *exact* answer (5 for `bvar 4`, 7
for `fvar 6`), and a saturated `lam` over a saturated `bvar 9` descends
correctly; an eleven-term battery has `bvarBoundMemo = bvarBound`,
`fvarRangeMemo = fvarRange` and both field reads equal to their spec.
**`hasLooseBVar` under binders** — `looseBVarsBounded` at `bvar 0`/`bvar 1`
under zero, one and two binders, with a binder's *domain* correctly outside
the binder, `letE` binding only its body, `proj` binding nothing, and closed
terms bounded by 0.  **`getAppFn`/`getAppArgs` on a five-argument
application**, with `mkAppN` rebuilding the spine and a non-application
giving itself and an empty list.  Telescopes: `stripPis` at the right and
the wrong arity, `piResult`, `piArity`, `instPis`/`instPisAt`/`instPisAtF`
agreeing on the same three arguments, `instLamsAt`/`instLamsAtF` agreeing
and both failing (through the sequential fall-back) on too many arguments,
`pisToLams` and `replacePiBody` round-tripped through
`stripLams`/`piResult`, `resultSort`.  `instSpine`, `fvarTypeD`, `sub_nat`'s
truncation, and `recRulePlain` on a canonical rule, a non-canonical one and
both arity guards.  `renameConsts` renaming through `fvar` annotations and
binders but **not** a `.proj`'s structure name; `resetMeta` clearing every
binder datum; `instantiateLevelParams` substituting a sort, a constant's
level list *and* a binder's prop-ness datum (`zeronessOf 1 = never`),
leaving a `hasLP`-negative term untouched, with `hasLevelParam` agreeing
with the flag throughout; `sizeB`/`sizeF` differing exactly on `fvar`
annotations, `fvarLeaves` hereditary, `wscopedB` on an index and on an
annotation's index, `isLam`/`lamPw`/`forallPw`, and `exprPtrBEq` on shared,
rebuilt and different terms.

**Deliberately not ported** (recorded so the next task does not re-derive
it): the **eleven memo invariants** — `Inst1MemoInv` (`:61`), `InstLMemoInv`
(`:248`), `LiftMemoInv` (`:411`), `ResetMemoInv` (`:562`), `RenameMemoInv`
(`:981`), `MemoBInv` (`:1495`), `MemoFInv` (`:1616`), `Abs1MemoInv`
(`:1770`), `LowerMemoInv` (`:1993`), `Inst1LMemoInv` (`:2203`), `ILPMemoInv`
(`:2544`) — and their `empty`/`insert` lemmas: they are `Prop`s ("every
recorded answer is the real one"), Charon erases `Prop`s, and they are
exactly the invariants the Rust-side refinement proof will restate about
`crate::hashmap` memos; and **every `theorem`** — the eleven `*Go_spec`
soundness lemmas, the eleven `@[csimp]` equations (each *cited* on the item
it licenses), `sizeB_instantiate1`, `looseBVarsBounded_iff`,
`hasFvar_eq_false_iff`, `fvarRange_bne_zero`, `bvarBRaw_exact`,
`fvarBRaw_exact`, `bvarB_eq`/`fvarB_eq`, the three `*_of_*_le` cutoff
lemmas, and the `Level`/`PropWhen`/`Expr` has-param shortcut lemmas at
`:2408-2727`.  These are the *spec* this port will be proved against.

**Coverage** (`scripts/provenance.py coverage | tail -3`), con-leche
3e004805: **TOTAL 146/1018 covered (14.3 %), 872 uncovered** — up from task
#11's 73/1018 (7.2 %), the biggest single jump so far.  `ExprOps.lean` goes
0/82 → **70/82**; the twelve uncovered are the eleven memo invariants above
plus one **ledger false positive**: `install` at `:964` is the phrase
"inductive install" inside a column-0 `/-!` module docstring, which
`top_level_decls` reads as a declaration.  (Worth a one-line fix in
`scripts/provenance.py` when someone is next in there; it is cosmetic and
affects no `check`.)  `Level.lean` goes 18/25 → **21/25**, the four
remaining being `Expr.allLevelParamsDefined` and its memoized twin.

### Task #17 — `Name`/`Level`/`PropWhen` refined on the crate (2026-09-12, Opus under Fable)

P3.3's first part: the task-#5 spike proofs are now stated and proved against
the *crate's* generated model, and `PropWhen` is refined on top of them.  Four
files under `proof/ConRon/Refine/`, all `sorry`-free and all elaborating with
**zero output** under `lake env lean`; `scripts/gates.sh` green.  `master` was
merged mid-task (the module nesting of task #14/#15), and the nesting cost
exactly **one line per file**.

**Size.**

| file | lines | `lake build` | declarations |
|---|---|---|---|
| `Refine/Abs.lean` | 326 | 1.6 s | 41 |
| `Refine/Name.lean` | 396 | 2.1 s | 21 |
| `Refine/Level.lean` | 1 504 | 5.0 s | 74 |
| `Refine/PropWhen.lean` | **1 904** | 4.7 s | 98 |
| total | **4 130** | 13 s (whole `ConRon` tree: 9.7 s wall, parallel) | 234 |

For comparison: the spike's `Refine.lean` is 1 830 lines, the crate's
`kernel/{name,level,prop_when}.rs` are 264/864/951 raw lines (of `prop_when.rs`
281 are `#[cfg(test)]`), and the generated model is ≈1 150 lines of
`kernel.level` and ≈771 of `kernel.prop_when` inside an 11 516-line
`Funs.lean`.

**How much of the spike ported by renaming: all of it, and the rename is one
line.**  Because Aeneas keeps the Rust module path as the definition-name
prefix, the nesting of task #14 made the generated names
`ConRon.Generated.kernel.level.leq_core` — so adding

```lean
open ConRon.Generated ConRon.Generated.kernel
```

restores every `level.*`/`name.*`/`prop_when.*` spelling the spike used.  A
mechanical diff confirms the rename is *all* that changed: all **63**
generated `name.*`/`level.*` definitions are token-identical to the spike's
modulo the prefix (only their line *wrapping* differs, because the longer
names re-flow Aeneas's pretty-printer).  The four remaining edits were
bookkeeping, not proof work:

1. the file split — `Abs.lean` takes the plumbing `simp` set, the `abs`
   functions, the `*_inv` smart-constructor shapes, `StrWF`/`NameWF`/`LevelWF`
   and `Level.ind'`/`Name.ind'`; `Name.lean` takes `absString_inj`,
   `absName_injective`, `str_eq`, `beq`; `Level.lean` the rest;
2. four identifiers qualified as `Name.…` in `Level.lean` (`absName_injective`,
   `name_beq_refl`, `name_beq_abs`, `name_beq_exact'`) — the only cross-file
   references the split created;
3. the README's naming rule applied to the public statements
   (`level_zero_abs` → `zero_refines`, `level_beq_exact` → `beq_refines`, …);
4. `vec_singleton` hoisted from `Level.lean` into `Abs.lean` (`PropWhen` needs
   it too), and the two induction principles de-duplicated.

**Not one tactic line of the 1 378 changed.**  That is the claim
`ConRon/Refine/README.md` made at task #12, now verified at full scale rather
than on two smoke lemmas — and those two smoke lemmas (`Smoke.lean`) were
folded into `Level.lean`'s `zero_refines`/`succ_refines` and the file deleted.

New in `Name.lean` beyond the spike: `contains_refines`
(`name::contains` refines `List.contains` at con-leche's `LawfulBEq Name`) and
`singleton_refines`, both of which `PropWhen` needs.

**`PropWhen`: the `import all` decision — not taken, and it did not need to
be.**  con-leche's datum is sealed twice over: `PropWhenRepr` is a `private
inductive` and `PropWhen` is a one-field structure whose constructor *and*
field are `private` (`PropWhen.lean:378-413`), and the module is `public
section` **without** `@[expose]`, so no importer can reduce through a body.
`absPropWhen` is therefore built from the two *public* producers, which
`PropWhen.casesZ` (`:645-661`) guarantees name every value:

```lean
def absPropWhenRepr : prop_when.PropWhenRepr → ConLeche.PropWhen
  | .Never    => .never
  | .Always   => .ifAllZero []
  | .One p    => .ifAllZero [absName p]
  | .Two p q  => .ifAllZero [absName p, absName q]
  | .Many ps  => .ifAllZero (absNames ps)
```

and every *proof* went through the exported equation battery
(`toList_ifAllZero`, `holds_ifAllZero`, `inter_ifAllZero`, `bindZ_ifAllZero`,
`inter_eq_toList`, `ifAllZero_eq_iff`, `ifAllZero_ne_never`, `ifAllZero_canon`,
`canon_eq_self`, `sorted_canon`, `sorted_merge`, `sorted_ext`,
`isNever_ifAllZero`, `hasParams_ifAllZero`, `paramsDefined_ifAllZero`,
`toList?_ifAllZero`, `nil_inter`/`inter_nil`, `inter_never_left`/`_right`,
`bindZ_never`, `bindZ_go_nil`).  **So `import all ConLeche.Kernel.PropWhen`
was never needed** — the encapsulation the module was designed for holds
against an external refinement proof, which is a real (and pleasant) result
about that design.  One nuance worth recording: *definitions* whose body does
not mention the private representation are still unfoldable from outside —
`rw [ConLeche.PropWhen.merge]` works without `@[expose]`, because equation
lemmas are ordinary theorems.  That is what made the sorted-list layer
(`merge`, `canon`, `bindZ.go`) tractable; had `merge` been sealed as well, the
proof would have had to go through `mem_merge`/`sorted_merge`/`sorted_ext`
only, and `to_list`'s exactness would have cost a good deal more.

**`PropWhen`'s hard spots**, in the order they bit.

1. **`str_compare` against Lean's `Ord String`** (≈110 lines, the single
   biggest new block).  `Name.cmp`'s `str` arm is `compare s t`, i.e.
   `String.compare = compareOfLessAndEq` over `instLTString`, i.e.
   `List.Lex (· < ·)` on the character lists (`Init/Data/Ord/String.lean:35`,
   `Init/Data/List/Basic.lean:247`).  The port compares a `Vec<u32>` of code
   points by a first-difference index walk, so the refinement needs six
   arm-selection lemmas for `compare (String.ofList l) (String.ofList m)`
   (`cmp_nil_nil`, `cmp_nil_cons`, `cmp_cons_nil`, `cmp_cons_lt`,
   `cmp_cons_gt`, `cmp_cons_cons`), each one `rw [cmp_ofList]` plus a
   `List.Lex` lemma, and it needs `StrWF` on **both** sides: `Char.ofNat`
   clamps an invalid code point to `'\0'`, so `absString` is order-preserving
   only where every stored word is a valid `Char`.  This is the same
   `StrWF` clause task #5 introduced for injectivity, now doing a second job.
2. **`&&`-expansion doubles the index walks.**  `str_compare_from` and
   `names_beq_from` both begin `if i >= a.len() && i >= b.len()`, which Charon
   turns into a nested `if` whose *both* branches contain the whole rest of the
   body (task #5's finding 1, at 2× rather than 3×).  Every one of those walks
   is therefore written twice; it is mechanical, and the four
   `rw [if_pos …]`/`rw [if_neg …]` with `by scalar_tac` side conditions handle
   it, but it is the reason `str_compare_from_refines` is 60 lines of proof for
   a 15-line Rust function.
3. **The 5×5 `match` explosion, twice** — `inter` and `equiv_r` each expand to
   25 arms.  The pattern that worked: **factor the distinct leaves into
   standalone lemmas and dispatch with
   `cases ra <;> cases rb <;> simp only [f] at h <;> first | exact …`**.
   `inter_shape` needs five leaves (`never` on either side, `dup` on either
   side, `two_prime`, and the generic
   `of_sorted (merge (to_list a) (to_list b))`) and is 25 arms in six lines.
   `beq_iff` could not use that trick — its arms differ in what they *prove*,
   not just in which lemma applies — so its 25 arms are generated from seven
   templates and spelled out (≈150 lines).
4. **`inter` and `bind_z` are producers, so `PropWhenWF` needs four
   constructors, not two.**  The first draft had only `never` and
   `if_all_zero`; then `inter`'s output is `of_sorted (merge …)` or
   `two_prime …`, which is *not* syntactically a smart-constructor
   application, and `bind_z_go` folds `inter` — so closure under the two
   derived producers is not provable from the two primitive ones without
   re-deriving `canon`-idempotence *inside the Rust model*.  The fix keeps the
   §3.5 convention (constructors are the port's own producers) and simply adds
   the two: `PropWhenWF.inter` and `PropWhenWF.bind_z`, the latter quantifying
   over the dictionary type `F` of task #9's pattern 1.  **General rule for the
   rest of the port: a `*WF` predicate's constructors are the module's whole
   set of *public* producers, not just its primitive ones.**
5. **A separate `WFShape` invariant is what the lemmas actually use.**
   `PropWhenWF` is an inductive derivation; the refinement lemmas need a
   *statement*: `WFShape pw` says the representation's parameter list carries
   well-formed names, is strictly ascending after abstraction (con-leche's
   `PropWhen.Sorted`) and, if it is a `Many`, holds more than two names.
   `wf_shape : PropWhenWF pw → WFShape pw` is one induction with one shape
   lemma per constructor (`never_shape`, `if_all_zero_shape`, `inter_shape`,
   `bind_z_wf`), and `wfShape_toList : (absPropWhen pw).toList = …` is the
   payoff that makes `to_list`, `to_list_opt`, `has_params` and `beq` exact
   instead of merely membership-correct.  Cost: `bind_z` needs its shape-only
   induction (`bind_z_go_from_wf`) *and* its abstraction induction
   (`bind_z_go_from_shape`) separately, because `wf_shape`'s induction
   hypothesis carries no valuation — ≈25 duplicated lines.
6. **The `Many` length clause is not decoration.**  `hasParams (ifAllZero ps)
   = !ps.isEmpty`, and a `Many` holding the empty list would read `true` in
   Rust and `false` in con-leche.  `of_sorted` only emits `Many` in its
   `len ≥ 3` branch, so the clause is free — but it has to be *in* the
   invariant, and it is the one clause the erased `Sorted ps ∧ 2 < ps.length`
   proof field of `PropWhenRepr` still owes.
7. `holds`'s and `bind_z`'s higher-order arguments are trait dictionaries, so
   their statements carry a relating hypothesis, exactly as task #9 predicted:
   `hφ : ∀ n, NameWF n → ∀ m, inst.value_at phi n = ok m → φ (absName n) = m.val`
   and `hf : ∀ n, NameWF n → ∀ r, inst.apply f n = ok r →
   absPropWhen r = Φ (absName n) ∧ PropWhenWF r`.  Neither needed anything
   clever; **this is the shape every higher-order argument in the rest of the
   port will take**, `CoreFns` included.
8. `hash_pw` gets no lemma, by §3.2 (`mixHash` is opaque, hash values only
   move memo entries between buckets); `prop_when::dup` gets `dup_eq : dup pw
   = ok pw`, which is what makes `inter`'s `Always` arms one-liners.
9. Two Lean-side annoyances worth a note for the next agent: `rw` fails with
   "motive is not type correct" whenever the rewritten term sits under a
   `decide`/`getElem` whose instance or proof depends on it (use `simp only`
   there), and `List.drop_eq_getElem_cons` makes `simp` emit a stray
   `i < l.length` side goal — state the "one side exhausted" cases with
   `List.drop_eq_nil_iff` instead.

**The lemma inventory** (`_refines`-named, per `ConRon/Refine/README.md`):
`Name` — `anonymous`, `mk_str`, `mk_num`, `dup`, `str_eq`, `beq`, `contains`,
`singleton` (plus `*_wf`); `Level` — `zero`, `succ`, `max`, `imax`, `param`,
`beq`, `level_has_param`, `subst`, `is_never_zero`, `simplify`, `leq_core`,
`rest`, `by_cases`, `leq`, `is_equiv` (plus `*_wf`); `PropWhen` — `never`,
`if_all_zero`, `name_cmp`, `to_list`, `to_list_opt`, `is_never`, `has_params`,
`holds`, `params_defined`, `inter`, `bind_z`, `beq`.  Each file ends with
`#guard_msgs in #print axioms` on two or three of its main lemmas
(`Name`: `beq_refines`, `contains_refines`, `str_eq_refines`; `Level`:
`leq_refines`, `simplify_refines`, `beq_refines`; `PropWhen`:
`inter_refines`, `bind_z_refines`, `beq_refines`) — `propext`,
`Classical.choice`, `Quot.sound` and nothing else, checked by the build.

**Extrapolation, updated.**  Task #5 estimated ≈2.2 proof lines per Rust line
from a module (`Level`) that is unusually branchy.  `prop_when` is the first
independent data point: 1 904 proof lines for 670 raw / ≈361 code Rust lines
is **5.3 proof lines per Rust code line** — worse, and the reason is
identifiable and *not* general: 110 of those lines are the one-off
`Ord String` bridge, ≈300 are the two 25-arm `match` expansions, and ≈250 are
the canonical-form machinery (`merge`/`canon`/`of_sorted`/`WFShape`) that
exists because this one module carries a representation invariant.  A module
without a sealed canonical representation should stay near task #5's figure;
the ones that *do* carry an invariant (`Expr`'s `BeqMap`, the memo tiers)
should be budgeted at this ratio.

**Not done, and named so the next task does not look for it.**
`level::zeroness_of` and `level::subst_pw` (task #13's `Level`→`PropWhen`
bridge) are ported in Rust but unproved: they are the natural first consumers
of `bind_z_refines` and `inter_refines` and belong with the `Level`/`PropWhen`
bridge lemmas of `ConLeche/Verify/PropWhen.lean`, not with either module
alone.  `name_lt`, `hash_pw`, `names_hash_from`, `hash_repr` and `equiv_r`'s
`names_beq` wrapper have no refinement statements (nothing executed decides on
them, or §3.2 exempts them).  The spike's eight unproved leftovers
(`is_equiv_list`, `is_zero`, `is_non_zero`, `all_params_defined`, `name_nodup`,
`levels_hash`, `levels_have_param`, the three string-shape predicates) are
still unproved — they were not stated at task #5 either, and they are all
instances of the patterns above.

### Task #19 — The Rust reader for `con-ron-decls/1` (2026-09-12, Opus under Fable)

P1.6's Rust half.  Task #10 gave the `DeclC` dump a format, a Lean writer, a
Lean reader and a corpus sweep; this task gives it the reader the Rust side
actually needs, in a **new, unverified** crate `crates/con-ron-dump`
(`parse_decls`, plus a writer and a `con-ron-dump-check` binary), added to the
workspace `members`.  With it, `crates/con-ron-core`'s types can be populated
from exactly the declarations con-leche's checker sees, with no Rust parser and
no reimplementation of the frontend's rewrites (§3.6).

**What landed** (2 535 lines, `crates/con-ron-dump/`):

| file | what |
|---|---|
| `src/lib.rs` | `parse_decls : &str -> Result<Vec<DeclC>, String>`, `parse_decls_counted`, the string codec (`unescape`, `is_valid_char`), `Counts`, and the crate's tests |
| `src/write.rs` | `dump_decls : &[DeclC] -> String` — a transliteration of `Write.lean`, emission order included, so the round trip is *byte*-exact |
| `src/natdec.rs` | decimal ↔ `ron::Nat`, the one scalar the core has no codec for |
| `src/dag.rs` | `census` — how many *distinct* heap nodes a declaration list reaches |
| `src/bin/con-ron-dump-check.rs` | the checker: parse, DAG census, optional `--roundtrip`, counts, non-zero exit on any failure |
| `scripts/dump-check-fixtures.sh` | run it over every dump `scripts/dump-fixtures.sh` produced |

**The crate is outside the verified core, and says so.**  Charon never sees it,
no refinement lemma mentions it, and §3.4's Aeneas subset does not apply — it
uses `for`/`while`, `?`, `std::collections`, closures and `derive(Debug)`
freely.  `scripts/lint-rust-style.sh` is invoked on `crates/con-ron-core/src`
only, `scripts/provenance.py`'s `DEFAULT_ROOTS` is the same path, and
`scripts/extract.sh` names `crates/con-ron-core` explicitly, so all three gates
were already scoped away from it and needed no change.  `scripts/gates.sh`
needed none either: its `cargo build`/`cargo test` run at the workspace
manifest, so the new member is covered by the existing two gates (a separate
`cargo test -p con-ron-dump` would be redundant).  What the crate does *not*
use is `unsafe` — there is none; `dag.rs` hashes and compares `Rc::as_ptr`
values but never dereferences one.

**Nothing was added to `con-ron-core`.**  The core's public API turned out to
be exactly sufficient: every node is built through `name::{anonymous, mk_str,
mk_num}`, `level::{zero, succ, max, imax, param}`, `prop_when::{never,
if_all_zero}`, `expr::{mk_bvar, fvar, sort, mk_const, app, lam, forall_e,
let_e, lit, proj}`, the `env` records are plain `pub` structs and enums, and
the `*_dup` family supplies the `Rc` clone at every backward reference.  For
the writer's interning tables the core's own dictionary API was enough too —
`name::hash_data`/`name::beq`, `level::hash_data`/`level::beq`,
`expr::hash`/`expr::beq`, `prop_when::hash_pw`/`prop_when::beq` — wrapped in
four one-line newtypes so `std::collections::HashMap` can use the *core's*
notion of equality, which is what makes the interning agree with
`Write.lean`'s `Std.HashMap`.  `ron::Nat` has no decimal parser and did not get
one: `natdec` works on `Nat::limbs` (`pub`) with `u128` intermediates, nineteen
digits at a time, and re-enters the core only at `nat::norm`.

**The two properties FORMAT.md §6 asks for, and how they are pinned.**

1. *The DAG stays a DAG.*  The reader is nine `Vec`s that only ever grow by
   one; each `N`/`L`/`W`/`E` record allocates once and every later reference is
   a cloned `Rc` handle.  A byte-identical re-dump does **not** prove this —
   `write.rs` interns by value, so it would collapse a tree expansion back into
   the same bytes — so `dag::census` counts distinct `Rc::as_ptr` values
   reachable from the declarations and `con-ron-dump-check` requires that to
   equal the file's `N`/`L`/`E` record counts.  It does, on all 318 dumps read.
2. *Computed fields are recomputed.*  The smart constructors are the only way a
   node is made here, so `NameNode::hash`, `LevelNode::hash` and
   `ExprNode::data` come from the children by the port's own recurrences.  The
   hash bits of `data` differ from Lean's by design (task #3, note 6) and
   nothing compares them.

**Fixture results** (`scripts/dump-check-fixtures.sh`, over the 315 dumps
`scripts/dump-fixtures.sh` writes; the other 33 fixtures have no declaration
list, task #10):

| | |
|---|---|
| dumps read | **315** |
| parse failures | **0** |
| DAG exact (distinct nodes == record counts) | **315 / 315** |
| re-dump byte-identical to the input | **315 / 315** |
| total bytes | 6 905 866 |
| declarations | **12 397** (axiom 36, defn 5 851, thm 2 718, opaque 12, basis 1 890, ind 1 890; 6 514 block `ConstantInfo`s) |
| interned N / L / W / E | **18 530 / 2 265 / 668 / 332 140** |
| numbered V / R / C / P / I | 15 131 / 2 715 / 1 917 / **0** / 6 514 |
| parse time, all 315 | **0.07 s** |
| re-dump time, all 315 | 0.09 s |
| wall, whole sweep | **0.20 s** |

Every one of those counts is **identical to task #10's Lean-side census**,
which is the real content of the table: two independently written readers agree
on the id-space sizes of 6.9 MB of dumps, and the Rust one reproduces the
writer's bytes.  `P = 0` confirms task #10's surprise 3 — no `ProjTable`
reaches a dump — so the `P` record and the `projInfo`/`axiomInfo`/`defnInfo`/
`thmInfo` block constructors, plus `fvar`, `RecRuleFire.plain`/`.nested`,
`natVal` bignums and non-placeholder `RecRule` fields, are covered by a
hand-built *kitchen sink* unit test instead (every `DeclC` constructor, every
`ConstantInfo` constructor, every `ExprKind`, every `LevelKind`, both
`Literal`s, all three hints, all three fires, all six basis kinds), which
round-trips byte-for-byte twice over.

**Scale** (the three fixtures `arena.sh` does not itself run; the Lean column
is task #10's `read`, re-measured here on the same machine):

| dump | bytes | E nodes | Lean read | **Rust parse** | Rust re-dump |
|---|---|---|---|---|---|
| `good/perf/grind-ring-5` | 4 265 323 | 182 307 | 149 ms | **32.6 ms** | 51.3 ms |
| `good/init-prelude` | 1 293 237 | 55 862 | 48 ms | **11.7 ms** | 15.6 ms |
| `good/perf/app-lam` | 479 915 | 24 446 | 16 ms | **3.1 ms** | 5.1 ms |

So the Rust reader is **4.1–5.1× faster** than the Lean one and runs at roughly
**130 MB/s**, which retires task #10's note that "reading is the slow half": at
that rate a Mathlib-scale dump is seconds, not minutes, and reading will not be
what bounds the differential test runner.  A `String` allocation per token is
what Lean was paying; `str::split(' ')` over a borrowed line pays nothing.

**Five notes for whoever wires the core's `check_decls` to this.**

1. **The reader needs no worklist.**  FORMAT.md §2's invariant — every
   reference strictly backwards — means the `E` records arrive topologically
   sorted, so the reader is a flat loop with no recursion over the term at all.
   Only the *writer* needs task #10's explicit stack, and `write.rs` reproduces
   it exactly (`(e, false)` visit / `(e, true)` emit, children pushed in
   constructor order so the last child is emitted first) because a single
   deviation there changes every `E` id and the round trip stops being
   byte-exact.  That fragility is the point: it is what makes the round trip a
   test of the *whole* format rather than of parsing alone.
2. **`if_all_zero` on a canonical list is the identity** — task #9's
   normalisation and FORMAT.md §4's "`ps` is already canonical" do not fight.
   Checked directly (`canonical_list_renormalises_to_itself`): a list out of
   `to_list` is strictly sorted under `name_lt`, duplicate-free, and feeding it
   back gives a datum equal under `beq` with the same `hash_pw`.  Also pinned
   there: `never` is **not** `if_all_zero []` (task #10, surprise 6).
3. **Unbounded vs machine-word `Nat`s split exactly where §3.3 says.**  Only
   `Literal.natVal` is read as a `ron::Nat`; the `bvar`/`fvar`/`proj` indices,
   `Name.num`'s component and every count are `u64`, and an overflow is a
   *reader* failure naming its line ("does not fit a 64-bit index"), never a
   silent truncation.  A test pins both halves of that on the same 23-digit
   literal.
4. **Two deliberate departures from `Read.lean`**, both tested: a literal byte
   inside a string field must be printable non-backslash ASCII (the Lean reader
   accepts any non-`\` character there; the format never emits one, so
   rejecting it is FORMAT.md §6's loud failure), while the degenerate escape
   `\;` — no hex digits, i.e. `U+0000` — is accepted exactly as `Read.lean`
   accepts it, to avoid inventing a stricter dialect than the format's own
   validator.
5. **`DeclC` derives nothing**, `Debug` included (task #10's note), so
   `Result::unwrap_err`/`expect_err` are unavailable on a parse result; the
   tests use a hand-written `perr` helper.  Any future assertion over a `DeclC`
   has to go through a structural comparison the consumer spells out itself, as
   `ConRon/Dump/Main.lean` does on the Lean side.

**Left for next time.**  The differential runner itself — feeding the parsed
list to `check_decls` and comparing verdicts with con-leche — waits on
P1.4/P1.5, which are not ported yet; `con-ron-dump-check` is deliberately
verdict-free and says only "the bytes and the graph are right".  No
Mathlib-scale dump exists in the tree to read (task #10's gap, unchanged).  And
`scripts/dump-check-fixtures.sh` is *not* in `scripts/gates.sh`: it needs the
`proof/` Lean build and the arena tarball, which the gate deliberately does not
require — it is the P1.6 gate's script, run by hand until the verdict
comparison joins it.

**Time.** ~25 min wall.  The single longest step was the Lean build of `lake
exe con-ron-dump` (~8 min, after pointing the worktree's `proof/.lake/packages`
at the main checkout's mathlib tree and copying its `vendor/con-leche/.lake`
build, without which it is a mathlib clone away); `scripts/dump-fixtures.sh
--no-check` took 45 s and the Rust sweep 0.2 s.  The Rust compiled
warning-free on the first `cargo build`; one real bug showed up in testing — a
missing `i += 1` in `unescape`'s literal-byte branch, an infinite loop that the
string-codec round-trip test caught as a 4 GiB allocation — and nothing else.
`scripts/gates.sh`: all 6 OK.

### Task #16 — `ron::HashMap` proved (2026-09-12, Opus under Fable)

P3.1's first half: `proof/ConRon/Refine/HashMap.lean` proves the abstract-map
specification of task #7 on the generated model
`ConRon.Generated.ron.hashmap.*`.  Generic in `K V`, with the generated
class dictionaries `HashableInst`/`Eq2Inst` as ordinary parameters, **no
`sorry`, no Rust change**, `scripts/gates.sh` all 6 OK, the file warning-free
under `lake env lean`.  (This task merged `master` — the `ron::`/`kernel::`
module nesting of commits 3051ebe/d22d956 — and retargeted every statement to
`ron.hashmap.*`; the generated tree came from the merge unchanged and
`extract.sh --check` passes.)

**Size.**

| | |
|---|---|
| `ConRon/Refine/HashMap.lean` | **1 428** lines (44 of them the header rationale) |
| declarations | 79 (10 `@[local simp]`) |
| Rust `src/ron/hashmap.rs`, extracted part (code lines, task #7) | 241 |
| generated `ron.hashmap.*` in `Funs.lean` | ≈360 (plus 30 in `Types.lean`) |
| `lake env lean` on the file (cold, oleans present) | **6 s** |
| largest proofs | `insert_no_resize_spec` 135, `move_elements_spec` 116, `remove_refines` 114, `clear_slots_spec` 57, `move_elements_from_list_spec` 49, `try_resize_spec` 48 |

So **≈5.9 proof lines per extracted Rust line** — well above task #5's 2.2 for
`Level`/`Name`, and the reason is structural: this file has no con-leche
counterpart to refine *against*, so it carries its own abstract theory (an
association-list layer, a permutation layer, a `Vec`/`slotsFlat` layer) before
the first law.  Lines 1–415 are that reusable infrastructure; the nine public
laws plus growth are lines 415–1400.

**Two departures from the tutorial** (`vendor/aeneas/tests/lean/Hashmap/
Properties.lean`), both of which paid for themselves:

1. **`toFun` is hash-free.**  The tutorial's `lookup` *is* the bucket lookup
   (`slots[hash k % len].lookup k`), which forces every law to carry the hash
   computation.  Ours is `toFun m k = lookupK (al_v m) k`, the lookup in the
   flattened list of all buckets; `Inv.slot_inv` is the only place the hash
   appears, and `toFun_eq_bucket` (12 lines) is the single bridge between the
   two views.  Consequence: **not one hypothesis about `hash64` anywhere** —
   it may fail and it may be constant.  `bucketAt` is never computed with;
   the only property used is that it is a *function* (`Result.ok_injective`
   on two calls at the same key), which is why §3.2's hash divergence is
   verdict-neutral for the memo tables.  `Inv.slot_inv` is phrased in the
   only direction needed — "if the computed bucket of `k` is `i`, and `k`
   lives in bucket `j`, then `i.val = j`" — so no `Usize` is ever built from
   a `Nat` index and **the file contains no arithmetic about `bucket_index`
   at all** (no `UScalar.cast`, no `%`, no "power of two divides `2^bits`").
2. **The bucket/rest decomposition is by permutation, not by position.**
   `al_v_perm_rest : (s.map alv).flatten ~ alv s[i]! ++ restOf s i` and
   `al_v_set_perm_rest` for the table with bucket `i` replaced, where
   `restOf s i = ((s.map alv).set i []).flatten`.  Because keys are `Nodup`,
   `lookupK` is permutation-invariant (`lookupK_perm`), so **one permutation
   carries lookup, length and nodup simultaneously**.  `insert`/`remove` then
   reduce to `alv a ↦ alv a ++ [(k,v)]` resp. `alv a ↦ eraseK (alv a) k` on
   one bucket, against an untouched `restOf`.  The tutorial instead threads
   four separate `∀ key v, … lookup … = some v → …` implications through
   every lemma; the permutation formulation is what shrank
   `move_elements_from_list` from the tutorial's 90 lines to 49 and
   `move_elements` from its ~120 to 116 *including* the halving walk.

**What is proved.**  `Inv` (capacity a power of two `≥ 32`; every key in the
bucket its hash selects; keys globally `Nodup`; `num_entries = |al_v|`) and:
`new_refines`, `with_capacity_refines`, `len_refines` (both as `|al_v m|` and
as `(support m).card`, with `mem_support_iff : k ∈ support m ↔ (toFun m k).isSome`),
`is_empty_refines`, `get_refines`, `contains_key_refines`, `insert_refines`
(`toFun m' = Function.update (toFun m) k (some v) ∧ old = toFun m k`),
`remove_refines` (the same with `none`), `clear_refines`; plus the private
helpers `list_{get,insert,remove}_spec`, `allocate_slots_spec`,
`pow2_at_least_spec`, `clear_slots_spec`, `insert_no_resize_spec`,
`move_elements_from_list_spec`, `move_elements_spec`, `try_resize_spec`.
Naming: the nine public entry points are `<fn>_refines` per
`ConRon/Refine/README.md`; the private Rust helpers are `<fn>_spec`.
The bridge `Rel m s absK absV := ∀ k, (toFun m k).map absV = s[absK k]?` has
`Rel_empty` / `Rel_get` / `Rel_insert` / `Rel_remove` against Lean core's
`Std.HashMap.getElem?_{empty,insert,erase}`, needing `Function.Injective absK`
and `LawfulBEq K'` for the two updating ones and nothing for the others.
`#guard_msgs in #print axioms insert_refines` / `get_refines` closes the file:
`[propext, Classical.choice, Quot.sound]`, nothing else.

**Hard spots, in order of pain.**

1. **The generated `let (a, index_mut_back) ← Vec::index_mut …` blocks `simp`.**
   After one `bind_eq_ok_iff` rewrite the hypothesis is `(let (a,b) := p; …) =
   ok v`; `simp only [bind_eq_ok_iff]`, `dsimp only`, `split`,
   `simp only [Function.uncurry]` and `beta_reduce` *all* fail on it — the
   equation's LHS is the `let`, not the `bind`, and the pattern-`let` Aeneas
   emits is not iota-reducible by any of them (it is reducible only
   definitionally).  **The fix, and the pattern to reuse: apply the lemma as a
   term, `replace h := bind_eq_ok_iff.mp h`** — the *unifier* whnf's through
   the `let` where `simp` will not.  Same trick for `Result.ok_injective h`,
   and a `have h2 : <explicitly written reduced form> := h` where several
   pattern-`let`s stack (`move_elements`' `core.mem.replace`).  Note the
   term-level form peels exactly **one** bind, so a run of `let x ← e` needs
   one `obtain` per level, whereas `simp only [bind_eq_ok_iff]` peels all of
   them up to the first pattern-`let`.  This cost about an hour and will
   recur in every `&mut`-carrying function in the port; it belongs in the
   planned `ConRon/Refine/Basic.lean`.
2. **Extracting the result fields.**  `Result.ok_injective h : (old, X) =
   (old', m')` with `X` a structure literal: `congrArg Prod.fst` leaves an
   unreduced `(old, m').1`, so `rw` cannot use it.  Always give the projection
   a type ascription — `have e1 : old = old0 := (congrArg Prod.fst e).symm`,
   `have es : m'.slots = … := (congrArg (fun z => (Prod.snd z).slots) e).symm`
   — which forces the defeq check and yields a usable equation.  Writing the
   structure literal itself is best avoided: a multi-field
   `{ num_entries := …, …, slots := … }` inside a `do` block inside a
   hypothesis type is a **parse error** in this Lean (`unexpected identifier;
   expected '}'` at the last field), while the same literal at top level
   parses fine.
3. **`subst` eats the wrong variable.**  `subst (h : old = old0)` eliminates
   `old0` or `old` depending on which is the more recent fvar; twice it removed
   the *statement's* variable and made the goal unmentionable.  Cheap to
   recover from but worth knowing: prefer `rw [e1, e2]` on the goal.
4. **The halving walks are genuinely easier than the linear ones.**  Task #7
   worried that `allocate_slots`/`clear_slots`/`move_elements` splitting their
   index range in half would complicate the proofs.  It does not: each is one
   `Nat.strong_induction_on` on `hi - lo`, and the frame condition
   ("`slots'` agrees with `slots` outside `[lo,hi)`") composes trivially
   across the two halves, where the tutorial's `i → i+1` loop needs a
   `∀ j < i, slots[j] = Nil` accumulator threaded through.  `slotsFlat s lo n
   = (((s.drop lo).take n).map alv).flatten` with `List.take_add` gives the
   range split in one `rw`.
5. **`UScalar` forward lemmas.**  Aeneas's `*_equiv` lemmas are stated over
   `(x + y).match`, so `rw [h]` fails when `h : x * y = ok z` (the lemma says
   `UScalar.mul x y`); `rw [show UScalar.mul x y = ok z from h]` fixes it.
   `UScalar.div` has no `_equiv` at all — only `div_bv_spec`, which is the
   *existence* direction — so `uscalar_div_eq` is proved by hand via the
   `y.bv = 0` case split.  Four such lemmas (`add`/`sub`/`mul`/`div`) are all
   the scalar reasoning the module needs, and `max_load` was **dropped from
   `Inv`** once it became clear nothing depends on it (the resize threshold
   only decides *whether* to grow, never what the map means), which removed
   `max_load_for` from the proof burden entirely.

**The `Eq2` hypothesis, and its generalisation.**  `Eq2Spec Eq2Inst := ∀ a b,
Eq2Inst.eq2 a b = ok (decide (a = b))` — `eq2` is decidable equality on `K`.
That is what the `u64`-keyed memo tables of `Cached/StateC.lean` need.  The
`ExprC`-keyed ones will want the abstract version, "`eq2 a b = ok (decide
(absK a = absK b))` for an abstraction `absK`": every proof below goes through
with `=` replaced by the kernel of `absK` at the cost of carrying a setoid
instead of `[DecidableEq K]`, and the header records this.  Doing it now would
have bought nothing testable, so it is deferred to the first client.

**How much of the tutorial transferred.**  The *strategy* transferred
completely — `AList.v`/`al_v`, `slot_t_inv`, "the table is one association
list", the order of the lemmas — and reading it first was worth several hours.
Not one *proof script* transferred: the tutorial is written in Aeneas's
`⦃ ⦄`/`step`/`grind` idiom and ours reasons forward from `f x = ok y`, exactly
the split task #5 recorded ("the `⦃ ⦄`/`step` tier and the refinement tier are
two different proof styles").  So: **the tutorial is a specification document
for us, not a proof library.**  Its `Properties.lean` is 1 086 lines for a
`Usize`-keyed map with a `&mut`-walking `remove`; ours is 1 428 for a generic
key with two trait dictionaries, an extra `with_capacity`/`is_empty`, a
by-value `remove`, the `Std.HashMap` bridge and an axiom gate — i.e. the same
order, which is the useful calibration for the rest of P3.

**Left for next time.**  `ConRon/Refine/Basic.lean` now has a clear charter:
`bind_eq_ok_iff` plus the four `uscalar_*_eq` lemmas plus the
`bind_eq_ok_iff.mp`-as-a-term idiom of hard spot 1 are needed by every module
and are currently duplicated between `Refine/HashMap.lean` and (in part)
`Spike/LevelName/Refine.lean`.  `Rel_len` (task #7's list) is *not* provable
from `Rel` alone — `Rel` constrains `s` only on the image of `absK`, so
`s.size` is not determined; a client that needs it must relate the key sets,
and that is the right place to state it.  `is_empty`, `contains_key` and
`support` are proved but unused.  `saturated` *is* covered — `insert`'s
"overloaded and saturated" arm and `try_resize`'s "cannot double" arm both
preserve `Inv` and `toFun` — but it remains unexercised at runtime (task #7's
open item (b)), so nothing checks that the two agree on a real table.
### Task #15 — `ron::Nat` proved (2026-09-12, Opus under Fable)

P3.1's first half: `proof/ConRon/Refine/Nat.lean` proves the bignum of task
#6 correct against Lean's `Nat`, on the *generated* model
(`ConRon.Generated.ron.nat.*`).  Every operation con-leche's `natOpResult`
and `natOpBody` need (`Kernel/Core.lean:628-655`) has an exact-result lemma,
plus `beq`/`ble`/`blt`/`is_zero`/`to_u64`/`from_u64`/`clone`, the
normalisation invariant and its injectivity.  `lake build` is clean of errors
**and warnings**, `scripts/gates.sh` is green, and no `sorry` is left.

**Sizes.**

| | |
|---|---|
| `Refine/Nat.lean` | **2 261** lines, 110 declarations, 19 `*_refines` on public ops |
| Rust proved (`src/ron/nat.rs`, code lines before `mod tests`) | 439 |
| generated Lean for `ron::nat` (48 `def`s in `Funs.lean`) | ≈ 420 |
| `lake env lean ConRon/Refine/Nat.lean`, warm | **8 s** |

So **≈ 5.1 proof lines per Rust line**, more than task #5's 2.2 — the bignum
is arithmetic-heavy rather than branchy, and the cost sits in the `Nat`
lemmas, not in the monadic plumbing.

**The statements.**  `limbsToNat : List U64 → Nat` is the little-endian
value, `toNat a = limbsToNat a.limbs.val`, and the invariant is a plain
`Prop`, **not** an inductive:

```lean
def LimbsWF (l : List U64) : Prop := ∀ x, l.getLast? = some x → x.val ≠ 0
def NatWF (a : ron.nat.Nat) : Prop := LimbsWF a.limbs.val
theorem toNat_inj : NatWF a → NatWF b → toNat a = toNat b → a = b
```

Task #5 made `NameWF`/`LevelWF` *inductive* (constructors = the port's smart
constructors) because a stored hash word has no equation of its own.  `Nat`
has no stored derived data, so the invariant is the single equation "no
trailing zero limb", and the `Prop` form is strictly better: it is preserved
by `norm`, which is the only place that re-establishes it, and `toNat_inj` is
a two-line induction rather than a constructor argument.  **Amendment to
§3.5**: the inductive-WF rule is about *stored derived data*; for a type
whose invariant is an equation on the representation, a `Prop` is right.

Every operation lemma has the §3.5 shape, e.g.

```lean
theorem add_refines (h : ron.nat.add a b = ok c) :
    toNat c = toNat a + toNat b ∧ NatWF c
theorem div_refines (ha : NatWF a) (hb : NatWF b) (h : ron.nat.div a b = ok c) :
    toNat c = toNat a / toNat b ∧ NatWF c
theorem land_refines (h : ron.nat.land a b = ok c) :
    toNat c = Nat.land (toNat a) (toNat b) ∧ NatWF c
```

`add`/`mul`/`pow`/`lor`/`xor`/`shift_left`/`shift_right`/`land` need **no**
`NatWF` hypothesis (they are value-level); `sub`/`pred`/`cmp`/`beq`/`ble`/
`blt`/`div`/`modulo`/`gcd`/`is_zero`/`to_u64` do, because they branch on limb
*length*, and length only decides the numeric order under normalisation.
Lean's zero-divisor conventions come out for free: `div_mod`'s early exit
returns `(zero, clone a)`, which is `a / 0 = 0` and `a % 0 = a`.  Committed
gate at the end of the file: `#guard_msgs in #print axioms` for
`add_refines`, `div_refines`, `land_refines` — `[propext, Classical.choice,
Quot.sound]` and nothing else.

**What carried the proofs.**

* **One loop shape, seventeen times.**  Every `*_from` helper is proved as
  `∀ (d : Nat) (i : Usize) …, n.val - i.val ≤ d → f … = ok w → <invariant>`
  by induction on the *fuel* `d`, with the `i ≥ n` case factored out as a
  local `have base : …` used by both the `zero` case and the `¬ i < n` branch
  of the `succ` case.  That is the reusable skeleton; `copy_from`, `sig_len`,
  `add_from`, `sub_from`, `and_from`, `or_from`, `xor_from`, `push_zeros`,
  `shl_bits_from`, `shr_bits_from`, `skip_index`, `shl1_from`,
  `mul_u64_from`, `mul_from`, `rev_copy_from`, `dm_bits`, `dm_limbs` are all
  instances, 20–90 lines each.
* **`seg v i n = limbsToNat ((v.drop i).take (n - i))`**, the value of the
  limb window the loop still has to consume, with three lemmas
  (`seg_of_le`, `seg_succ`, `seg_full`) and two more for the `0`-based case
  (`seg_zero_succ`, `seg_zero_mod`).  Because `nat::limb` reads `0` past the
  end, `seg` needs no length side condition, and `seg_full` collapses the
  top-level call to `toNat a` given a single `≤`.
* **The `*_step_arith` trick.**  Each induction step is one equation in `Nat`
  whose only content is "the word-level fact, scaled by `2^(64 |out|)`".
  `linarith` cannot scale a hypothesis by a *variable* coefficient, so each
  family gets a three-line pure-arithmetic lemma (`add_step_arith`,
  `sub_step_arith`, `shl_step_arith` — the last reused for `mul_u64_from` and
  `shl1_from`) proved by a `calc` of `ring` steps with one `rw [hw]` in the
  middle.  This is the single highest-leverage idea in the file: it turns
  every loop step into `exact shl_step_arith _ … hIH hword`.
* **The bit operations are one lemma.**  `bitwise_block` — for any `f` with
  `f false false = false`, `Nat.bitwise f (x + 2^m * A) (y + 2^m * B) =
  Nat.bitwise f x y + 2^m * Nat.bitwise f A B` given `x, y < 2^m` — is five
  lines from `Nat.eq_of_testBit_eq`, `Nat.testBit_bitwise` and
  `Nat.testBit_two_pow_mul_add`, and `land`/`lor`/`xor` are its three
  instances at `m = 64`, *by definitional unfolding* (`Nat.land = bitwise
  and`).  The same lemma, at `m = bits` and `m = 64 - bits`, gives the
  `lo ||| hi = lo + hi` disjointness both shift loops need (`lor_disjoint`,
  `lor_disjoint'`), and `lor_one_of_even` for the quotient-bit accumulator.
  Only `land` needs more: its window is the *shorter* operand, so
  `land_mod_two_pow` ("the bits above the window are `0` on one side") plus
  `seg_zero_mod` bridge it.  `bv_decide`/`bv_tac` were never used.
* **Shifts are arithmetic, not bits.**  `Nat.shiftLeft a k = a * 2^k` and
  `Nat.shiftRight a k = a / 2^k`, so the only bit-level facts are the
  per-limb `shl_word` / `shr_word` (`x * 2^bits % 2^64` and `x / 2^bits`
  reassembled), six lines each from `two_pow_split` +
  `Nat.mul_mod_mul_left` + `Nat.mod_add_div`.
* **Division is the standard restoring invariant, stated twice.**  `dm_bits`
  carries `ql = (qacc·2^j + (rem·2^j + x % 2^j) / b) % 2^64 ∧
  r = (rem·2^j + x % 2^j) % b` — the `% 2^64` absorbs the wrapping
  `qacc <<< 1`, the only place a machine word would overflow — and
  `dm_limbs` carries `rem = (a / 2^(64 i)) % b` plus "the quotient limbs
  produced so far are `(a / b) % 2^(64 i)`, most significant first".  The two
  glue facts are `a / 2^(64 (i-1)) = a[i-1] + 2^64 · (a / 2^(64 i))` (from
  `limbsToNat_drop`) and `(a/b)/2^k = (a/2^k)/b` (`Nat.div_div_eq_div_mul`
  twice); `Nat.mod_mul` (`n % (a*b) = n % a + a * (n / a % b)`) does the
  limb-assembly bookkeeping.  `sub_from`'s invariant is existential in the
  *borrow out* (`∃ bo ≤ 1, W + P·(Sb + borrow) = O + P·(Sa + 2^(64(n-i))·bo)`)
  so that no case analysis is needed inside the loop; `sub` then kills
  `bo = 1` from `limbsToNat w < 2^(64 |w|)`.
* **`pow` and `gcd` are strong induction on a `Nat` measure**, not on the
  function: `pow` on `e.val` (via `e / 2 < e`), `gcd` on `toNat a` (via
  `toNat b % toNat a < toNat a`, which needs `modulo_refines` first — so the
  file order is `div_mod → div/modulo → gcd`).  No `dspec`, no
  admissibility, no `partial_fixpoint` reasoning anywhere, exactly as in
  task #5.

**What was awkward in the generated code.**

1. **Tuple-returning `core` intrinsics defeat `simp only`.**  Charon turns
   `let (s, c) = x.overflowing_add(y)` into
   `bind e (fun p => match p with | (s, c) => …)`.  `bind_eq_ok_iff` fires
   once and then `simp only` is stuck: the matcher's scrutinee is a
   *variable*, and neither `simp only []` nor `dsimp only` nor `split at h`
   reduces it.  Two escapes, both used:
   * for `overflowing_add`/`overflowing_sub`, **unfold the `UScalar`
     definition first** (`simp only [Std.core.num.U64.overflowing_add,
     Std.UScalar.overflowing_add] at h`) — the pair becomes a literal
     constructor, and a subsequent *full* `simp at h` reduces the whole body
     to the bit-vector level, where `add_carry_word` / `sub_borrow_word`
     absorb it in ten lines each;
   * for the port's own tuple returns (`dm_bits`, `dm_limbs`, `div_mod`),
     `obtain ⟨p, hp, h⟩ := h; obtain ⟨ql, r⟩ := p` and then **`replace h :
     <the body, spelled out> := h`** — the matcher on a constructor is
     *definitionally* the body, so a type ascription passes.  Three lines per
     tuple bind, completely predictable.

   Recommendation for the rest of the port: prefer a `struct` return over a
   Rust tuple in new code; where a tuple is natural (`div_mod`), the
   `replace` idiom is the fix.
2. **`Vec::push` can fail** (capacity check), so `push_eq_ok_iff` is an `iff`
   whose left conjunct is the capacity disjunction.  Keeping it an `iff`
   (rather than a one-directional lemma) is what lets one `simp only` unfold
   a whole loop body; the conjunct is discarded with `⟨-, hout1⟩` in every
   use.
3. **`have i1 := v.len; if …` blocks `split`** — task #5's item 3, hit again
   in `skip_index` and `rev_copy_from`; `simp only [] at h` first.
4. `simp` *re-folds* `l.take n ++ [l[n]]` into `l.take (n+1)`, so
   `rev_copy_from`'s last step has to finish with an explicit
   `rw [List.reverse_append, List.reverse_singleton, List.singleton_append]`
   instead of `simp`.
5. `Nat.land`/`Nat.lor`/`Nat.xor` are *definitionally* `_ &&& _` and friends,
   but `Nat.testBit_and` etc. are stated about the notation, so `simp` needs
   a `nat_land_eq : Nat.land x y = x &&& y := rfl` bridge to see them — and
   `ring` treats the two forms as different atoms.

**No Rust change was needed.**  `crates/` is untouched and
`scripts/extract.sh --check` passes unchanged.  The one thing that would have
made the proof shorter is item 1 (u128 arithmetic instead of
`overflowing_add`, as `mul_u64_from` already does), and it was deliberately
*not* done: the current code is proved, and changing it would cost a
regeneration for a cosmetic gain.

**Merged `master`** (nested crate modules, 3051ebe/d22d956) into this
worktree before finishing.  The generated model came from `master` already,
so retargeting the proof was `nat.` → `ron.nat.` in `Refine/Nat.lean` and
nothing else — the same "renaming alone" claim `ConRon/Refine/README.md`
makes for the spike.

**Left for next time.**  `hash64` has no lemma (verdict-neutral, §3.2), and
`one`/`zero`/`cmp_from`/`norm` are proved but only used internally.  The
`*_step_arith` + fuel-induction skeleton, `push_eq_ok_iff`/`lift_eq_ok_iff`
and `bitwise_block` belong in the shared `ConRon/Refine/Basic.lean` that task
#5 asked for; `ron::HashMap` (the other half of P3.1) will want the same loop
skeleton.
### Task #18 — `Core.lean`: the bodies and the knot (2026-09-12, Opus under Fable)

P1.4's first half: `ConLeche/Kernel/Core.lean` (2 906 lines, 130 top-level
declarations, 2 covered) ported as `crates/con-ron-core/src/kernel/core_k.rs`,
and **the knot closed** — the six memoizing wrappers of
`ConLeche/Cached/CoreC.lean` (`memoEI`, `memoBI`, `coreKnotI`) as
`src/cached/core_c.rs`.  The crate now has a runnable checker core: `whnf`,
`whnfCore`, `infer`, `inferIO`, `defeq`, `annotate`.

Two dependency files came with it rather than half a family (task #13's rule):
`ConLeche/Kernel/PropRead.lean` as `src/kernel/prop_read.rs` (11 declarations —
`propIrrel`'s and the annotation pass's head-symbol readers are its only
consumers) and `ConLeche/Kernel/Basis/Names.lean` as
`src/kernel/basis_names.rs` (25 pinned names, which every literal guard, the
`PUnit` unit-like pin, the `And`-only η rescue and the `reservedBasisNames`
exclusions read).

**The module is `core_k`, not `core`** (the task offered either): `core` is a
Rust prelude crate name, so `crate::kernel::core` would shadow it for every
`use` inside the crate.  The `k` is for *kernel*, con-leche's
`ConLeche.Kernel.Core`.

#### The knot, concretely

`Kernel/Core.lean` writes every core function *once*, as a non-recursive body
over a record `CoreFns m` of the six entry points; `coreKnot` (`:2866`) and
`coreKnotI` (`CoreC.lean:1916`) tie it with fuel.  §3.1's "bodies over
wrappers" ruling is now cashed in, and it is exactly as cheap as the design
claimed:

* a body drops the record and gains `fuel: u64`;
  `whnf_core_body(mode, fuel, st, fe, d, e)` is the Lean body applied to
  `coreKnot … fuel`;
* where the Lean writes `r.whnf d x`, the Rust writes
  `core_c::whnf(mode, fuel, st, fe, d, &x)` — the **wrapper, by name**;
* a wrapper is `fuel = 0 → .internal "fuel exhausted: …"`, else memo probe,
  else the body at `fuel - 1`, then the memo insert.  So the Rust's `fuel`
  *is* the Lean's knot level, and `coreKnotI`'s `fuel + 1` arm is the
  `fuel - 1` in the wrapper.

Aeneas put the whole thing in **one `mutual` block of 75 functions** (3 940
lines of `Funs.lean`) plus a second, 5-function one for `annotate` — which is
the correct SCC decomposition and a fact worth recording: `annotate` *calls*
`infer`/`defeq` but nothing in the reduction/inference/equality cycle calls
`annotate` (only `isPropType` does, and that is the driver's entry, not the
knot's).  No trait and no closure is in the recursion, so the spike's
"mixed-recursive declaration groups" failure never arose.

Four global deviations follow from the closed knot; they are recorded once, in
the module doc, rather than on 200 items.

1. **`mode: &CheckMode` is threaded explicitly.**  The Lean knot closes over
   the mode, so a body that reads no mode takes none; the Rust wrappers are
   plain functions, so every function that (transitively) calls one carries
   `mode` — `reduce_nat`, `iota_certs`, `def_eq_list` included.
2. **`st: &mut CState` is threaded through bodies that touch no memo.**  The
   maps are the wrappers' business; a body needs `st` only to hand it on.
   Aeneas turns the `&mut` into a threaded return, so the generated Lean
   carries con-leche's own `StateT CState` shape.
3. **The environment is the index.**  `Kernel/Core.lean`'s bodies take
   `env : Env`; the executed checker reads through `FEnv` and con-leche writes
   five `F`-twins for exactly that (`FEnv.lean:98-153`).  The port has one
   spelling, `fe: &FEnv` with `fenv::find`/`fenv::find_proj`, so
   `natLitSupported`/`natLitSupportedF`, `strLitSupported`/`strLitSupportedF`,
   `natOpGuard`/`natOpGuardF`, `natOpStoredOk`/`natOpStoredF` and
   `andRescueSlotsOf`/`andRescueSlots`/`andRescueSlotsF` are **one Rust
   function with two or three citations** each.  `FEnv.lean` therefore goes
   9/14 → **14/14** without a line of new code in `fenv.rs` beyond two extra
   citations (`towerSlotsAll`, `recSlotsAll`, whose F-twins task #14 already
   ported).
4. **`CoreFns.ioView` is a `bool` flag.**  `inferBodyIO` recurses through
   `r.infer`, which the knot binds to the *io* slot (`coreKnot`'s
   `CoreFns.ioView`).  The two inference bodies are byte-identical except in
   the λ and application clauses, so the port shares the other clauses and
   passes the grade as `io: bool` to `infer_at`, which is `core_c::infer_io`
   or `core_c::infer`.  That flag is the port's `ioView`.

**Which bodies the wrappers tie.**  The wrappers memoize `core_k`'s bodies,
i.e. `Kernel/Core.lean`'s.  con-leche's executed checker memoizes
`CoreC.lean`'s *interned* twins (`whnfCoreBodyI` … `annotateBodyI`), which
also swap `Level.isEquiv` for the `eqvC`-memoized `isEquivLM`, `instantiate1`
for `inst1M`, and so on.  Those are task #19's, and the swap is a change of
six call sites in `core_c.rs`; until then the level-operation memos
(`lsimpC`/`lnzC`/`eqvC`) stay untouched by the core, which is a *memo-policy*
deviation from the executed Lean and is the one thing §3.1 asks to be flagged:
it must be reconciled when `CoreC.lean`'s bodies land, before any
`whnf_refines` is stated against `coreKnotI`.

#### The one Aeneas error, and the one Lean error

Charon succeeded on the first run.  Aeneas gave **one** error, and `lake
build` then gave **one**; both were a-priori-legal shapes elsewhere in the
port, and both fixes are improvements.

* **Aeneas: *"Could not match the contexts"* in `infer_app_io`** — the io
  application site, `unless mt.pw.isNever do (let ta ← r.infer a; unless ←
  r.defeq ta ty do throw); pure (body.instantiate1 a)`.  The guard is a branch
  whose two arms carry different borrow contexts (one binds `ta` and threads
  the state, the other does neither) and then *join* on the shared reduct.
  Factoring the certificate into a `CheckM<bool>` — task #14's fix — was **not
  enough**: the join is the problem, not the borrow's scope.  What works is
  the shape con-leche's own `betaGateFires` docstring asks for, a **pure early
  return**: the skip arm returns `body.instantiate1 a` directly and the
  certifying arm is a whole function (`infer_app_cert`) that returns the
  reduct itself.  Nothing joins.  The price is the reduct written twice — and
  `whnf_core_app` already has that duplication for the β gate, where the Lean
  spells the early return itself.  Rule for the next porter: *a gated
  certificate whose two arms rejoin on a shared result must be split into two
  tail calls, not two `Bool`s.*
* **Lean: `failed to synthesize Decidable closed`** in `defeq_lits`.  A `!` in
  a **value** position comes out of Aeneas as Lean's *propositional* `¬`
  (`b : Bool` coerces to `b = true`), which is fine when it is immediately
  the result of a `Bool`-typed function (the `decide` coercion finds its
  instance) but not when it is `let`-bound and a later `if` reads it — there
  the binding's type is inferred as `Prop`.  `let closed = !a'.hasFvar &&
  !b'.hasFvar` was the only such site; it is an `if` nest now, and
  `pw_written` and `prop_read::not_proof_fast` were converted too so that no
  `¬` from this task's code reaches the model.  (One `¬` remains in
  `Funs.lean`, from `env::rec_rule_compare_params`, where it is a return
  value and elaborates.)
* **A fifth external hole, caught and removed.**  `Vec::is_empty` has no
  Aeneas model and emitted `alloc.vec.Vec.is_empty` into
  `FunsExternal_Template.lean`.  Every `xs.is_empty()` in the new code is
  `xs.len() == 0`, and §3.2's standing gate holds: the templates are **exactly
  the four `Rc` axioms and the `Rc` type**.  (`Option::is_some` is modeled and
  costs nothing.)

#### Constructs that do not survive transliteration, and their replacements

Beyond the four global ones above, and all a-priori except where noted:

1. **`liftFueled` is monomorphic at `Option Bool`.**  Every one of its call
   sites lifts a `Level.isEquiv`/`isEquivList`, and every one passes the same
   `what = "level comparison"`, so both the type parameter and the string
   argument are gone.
2. **`whnfStep`/`defeqStep`'s continuation is the loop's step budget.**  The
   Lean abstracts `k : Expr → m Expr` (resp. `Bool → Expr → Expr → m Bool`) so
   that the body's lemma is proven once; §3.4 forbids closures.  The port
   takes the continuation's *budget* `n` and spells `k x` as
   `whnf_loop(…, n, x)` — which is precisely what
   `whnfLoop (n+1) = whnfStep … (whnfLoop … n)` passes.  **Both functions
   survive**, and so does the loop/step split the refinement bridge reasons
   about.
3. **`defeqStep`'s twenty-deep `if … else` nest is five functions**
   (`defeq_step` → `defeq_after_whnf` → `defeq_lits` → `defeq_delta` →
   `defeq_delta_both`/`defeq_unfold_both` → `defeq_struct`), one per cited
   stage, so every `else` arm stays a tail position.  `structEtaCertWith`,
   `majorToCtor` and `iotaRec` are split the same way (`*_shape_ok` for the
   syntactic conjunction block, `*_steps`/`*_checks` for the state-touching
   cascade).  The arm *order* is preserved everywhere — it is load-bearing in
   `defeqStep`'s structural match (literal-versus-constructor-form before the
   general stuck arms, the one-sided λ η arms after the binder congruences)
   and in `iotaCerts`/`isEquivListLM`.
4. **`defeqStep`'s structural match is one `match` on the constructor pair**,
   as `expr::beq_go` is; the two `.lit … , .app …` arms read their inner
   `match nn, f with | k+1, .const c [] => …` through `succ_of`, and the two
   string arms their `cO = stringOfListName ∧ usO = [] ∧ strLitSupported`
   through `str_expansion_fires`.
5. **`natOpEquations`' four local lambdas** (`s`, `ap1`, `ap2`, and the `let`
   block's `x`/`y`/`z`/`bT`/`bF`) are three named builder functions plus
   locals: `nat_eq_s`, `nat_eq_ap1`, `nat_eq_ap2`.
6. **`natOpResult` on `ron::Nat`.**  `pow`'s `b > 16777216` blow-up bound is
   the audit's S2 mirror, and the port narrows the exponent to `u64` *behind*
   the bound (`nat::pow` takes a machine exponent).  `shiftLeft`/`shiftRight`
   answer `None` when the shift amount exceeds `u64` — Lean would compute and
   die; declining where Lean succeeds can only make the Rust *reject*, which
   is sound for the accept direction (§1).
7. **`projModelName`'s `toString i`** needs a decimal rendering of a `Nat`,
   which the runtime supplies in Lean: `nat_to_dec` is the two-arm recursion
   that produces it (`0` → `"0"`, most significant digit first).
8. **Five owning environment probes** (`defn_probe`, `ctor_probe`,
   `ind_probe`, `rec_probe`, `lp_empty`) stand for the Lean's
   `some (.defnInfo cv v hint)` / `.ctorInfo` / `.indInfo` / `.recInfo`
   destructurings.  They are task #14's rule made routine: the index's borrow
   dies at the call boundary and the caller works on the copies Lean's value
   semantics hands its pattern variables.  `rec_probe` copies the rule list
   spine-wise, because `iotaRec` reads it after several state-touching calls.
9. **`majorToCtor`'s `_recName` is dropped** — it is unused in the Lean too
   (hence its underscore), so `prepare_major` passes one argument fewer.
10. **`Nat` `def`s are Rust `fn`s.**  Every pinned name (`natName`,
    `natPredName`, `boolTrueName`, the 25 of `Basis/Names.lean`) is a closed
    top-level value Lean builds once at module initialization and marks
    persistent; the Aeneas subset has no such thing (task #11's `bvarPool`
    note), so each is a function that rebuilds its `Name` — the same value at
    one `Rc` allocation per call.  A pinned-name table in `CState` can buy it
    back in P1.6 without touching the model.
11. **`List` → `Vec` with `*_from` helpers**, as ever: `iota_certs`,
    `def_eq_list`, `pi_residual`, `struct_eta_proj_certs`, `eta_projs`,
    `and_rescue_slots`, `nat_op_deps`, `rules_find`, `params_subst`,
    `pins_subst`, `str_lit_cons` (the `foldr` of `strLitToConstructor`, walked
    downwards from the end), `nat_to_dec`, `fvar_leaves_subset`.
    `List.take`/`.drop`/`++`/`.reverse` copy a `Vec` spine (`drop_exprs`,
    `append_exprs`, `rev_append_exprs`, `expr_singleton`, and `expr_ops`'s
    `take_exprs`).
12. **`match memo[k]?` is an owning probe** in `core_c` too (task #13's
    pattern): six of them, one per `CState` map, over a *shared* state borrow.
    con-leche's linear-update dance (`let mp := get' st; let st := set' st ∅;
    set' st (mp.insert e r)`) is dropped, as task #14 ruled: `st.<map>.insert`
    on a `&mut CState` *is* that in-place update.
13. **`ProjEntry.fireOk` is called where the Lean inlines it.**  `inferBody`'s
    and `inferBodyIO`'s `.proj` clauses spell the two tests of `fireOk`
    (`if structSort is Prop then the field must be too`) out again; the port
    calls `proj_entry_fire_ok`, which is the same `Bool`, and throws exactly
    where it is `false`.

#### Numbers

| | |
|---|---|
| Lean ported: 123 cited blocks of `Kernel/Core.lean` | 2 611 raw / **1 361 code** |
| plus `Kernel/PropRead.lean` 10 blocks / `Kernel/Basis/Names.lean` 25 | 99 / 68 raw |
| plus `Cached/CoreC.lean` 3 blocks (`memoEI`, `memoBI`, `coreKnotI`) | 104 raw / **52 code** |
| `src/kernel/core_k.rs`, extracted part (raw / code) | 5 883 / **4 520** (3.3× the Lean code) |
| `src/kernel/core_k.rs`, `#[cfg(test)]` part (8 tests) | 494 / 425 |
| `src/cached/core_c.rs` (raw / code) | 325 / **220** |
| `src/kernel/prop_read.rs` extracted / tests | 205 / 123 · 125 / 103 |
| `src/kernel/basis_names.rs` extracted / tests | 240 / 126 · 34 / 26 |
| generated `Types.lean` | **583 — unchanged**; the four new modules declare no type |
| generated `Funs.lean` | 11 516 → **21 205** (+9 689: `core_k` 8 615, `basis_names` 411, `core_c` 386, `prop_read` 285) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 — **unchanged** |
| `charon cargo --preset=aeneas` wall (after `cargo clean`) | **1.13 s** (the `.llbc` is 33 MB) |
| `aeneas -backend lean -split-files -loops-to-rec` | **13.98 s** (13.51 s self-reported) |
| `partial_fixpoint` (whole crate / this task) | 127 → **226** (+99: `core_k` 91, `core_c` 6, `prop_read` 2) |
| `mutual` blocks in `Funs.lean` | 1 → **3**: task #3's 8-function `leq_core` knot (328 lines), **the core knot — 75 functions, 3 940 lines**, and `annotate`'s 5-function block (284 lines) |
| `mutual` blocks in `Types.lean` | 3 — unchanged |
| `lake build` of `ConRon.Generated.Funs` (from scratch) | **38 s** |
| external holes | **exactly the four `Rc` axioms of §3.2** — `new`, `clone`, `deref`, `ptr_eq`, plus the `Rc` type.  `Vec::is_empty` briefly made a fifth; see above |

`cargo build`/`cargo test` warning-free, **105/105** green (93 from tasks
#6-#14 + 12 new); `scripts/lint-rust-style.sh crates/con-ron-core/src` clean;
`scripts/provenance.py check` green — 835 items, 732 citations, all current at
pin 3e004805; `scripts/gates.sh` all six OK.

The 3.3× Rust→Lean code ratio is a third messages, a third `if` nests and a
third the wrapper plumbing: 37 throw sites carry their message as a
`const […]: [u32; N]` of code points (task #14's idiom, ~150 lines), every
`∧`/`&&` conjunction is an `if` nest (task #3's pattern 9), and every wrapper
call is an explicit `match` on `Result` because §3.4 forbids `?`.  The
generated Lean is 1.9× the Rust code, well below `expr_ops`' 3.7× — the
constructor-pair matches that inflated that module appear here only in
`defeq_struct`.

#### Tests

Twelve (`#[cfg(test)]`, invisible to Charon).  All environments are built by
hand from **axioms and `Sort`/Π/λ/app terms** — a `Nat`-like inductive is far
too big for a unit test, and none of these paths needs one.

`core_k` (8): **β** — `whnf` of `(λ (x : A). x) a` with the per-redex
certificate actually running (the λ's datum is not `.never`, so
`betaGateFires` is false and `inferIO a ≡ A` is checked), the same reduct with
the gate firing, and `whnfCore` alone doing it (β is not delta).  **`infer` of
a λ is a Π** — `λ (x : Sort 1). x` gives `∀ (_ : Sort 1), Sort 1` with the
`.never` datum validated at the innermost binder, a wrong datum *declining*
(`notImplemented`, never a reject), and `Sort 1 : Sort 2`.  **η** — `defeq`
equates `λ (x : A). f x` with `f` in both directions, separates two distinct
axioms, and takes the syntactic fast path on a repeated term.  **Fuel zero** —
all six wrappers throw `.internal`, `defeq` too (not even a syntactic hit
answers), nothing is cached on the way, and a β redex at `fuel = 2` exhausts
*inside*.  **The memo** — after one `whnf` the `whnfC`/`whnfCoreC` maps are
non-empty, a second call answers the same term and **writes nothing** (all
five map sizes unchanged), and the same for `defeqC` under `memoBI`'s pair
key.  **`annotate`** — the placeholder `.never` is recomputed to the real
datum, `infer` then validates the pass's own output, and a genuine
`ifAllZero` input annotation survives (`pwWritten`).  **The syntactic
readers** — nothing unfolds without a stored definition, the literal guards
fail without the basis, `Bool.true` is the *bare* constant (a levelled one is
not), `quickPair` at the four same-constructor pairs and two negatives,
`sameConstHeads` needing applications on both sides, the three op-name tables'
sizes, `natOpDeps` reflexive and empty off the sixteen, `natOpEquations`'
four `beq` equations, `nat_to_dec` at 0 and 1207, and the four fuel constants.
**The `Nat` fast path end to end** — with `Nat`, `Nat.zero`, `Nat.succ` and a
stored `Nat.add`, `whnf` folds `Nat.add 2 3` to the literal `5` and packs
`Nat.succ (lit 4)` to `lit 5`; `natLitSupported`, `natOpStored`, `natOpGuard`
and `natOpStoredOk` all pass on that environment; `rawNatLit?` reads a literal
and `Nat.zero` and nothing else; `natLitToConstructor` at both arms; a literal
types as `Nat`; and `pow` at exponent `2^24 + 1` declines instead of
computing.

`prop_read` (2): `peelNeverPis` passing a `.never` binder and blocked by a
non-`.never` one, `numArgs` on a spine, and the readers separating `h : P`
with `P : Sort 0` (definitely a proof) from `a : A` with `A : Sort 1`
(definitely not), with an unknown constant answering neither, a ∀'s datum read
off its binder, a sort's `.never`, an unapplied λ's own datum, and the probe's
level-count mismatch.

`basis_names` (2): the nineteen reserved names pairwise distinct, and the
shapes the pins rely on (`punitRecName = rec_of punitName`, distinct heads,
structural rebuild equality).

#### Deliberately not ported

`Core.lean` goes 2/130 → **129/130**.  The one uncovered declaration is
`CoreFns.ioView` (`:94`), and it is uncovered *because* §3.1's knot has no
record to view: its content is the `io: bool` flag of `infer_at` (deviation 4
above), which cites `CoreFns` itself.  Also skipped, and recorded so the next
task does not re-derive it:

* `instance : ToString CheckError` (`:53-57`) — rendering only; task #14
  already recorded it with the `CheckError` half of the file.
* `structure CoreFns` (`:66-92`) — cited, not ported as a type: §3.1 ties the
  knot with plain mutually recursive functions.
* `coreKnot` (`:2866-2900`) — cited on `core_c.rs`'s six wrappers, which are
  `coreKnotI`'s.
* the twelve `@[simp] theorem`s about `recRuleBits` (`:1545-1586`) and
  `projFnRule` (`:1596-1613`) — field-projection equations, i.e. the *spec*
  this port will be proved against.

Everything else executable in the file is ported, the eleven functions nothing
in the core calls included (`piResultNeverZero`, `etaFabArgs`, `natOpNames`,
`natOpGuard`, `natOpStoredOk`, `natOpEquations`, `substConst0`,
`substConstAll`, `whnfCoreLoopFuel`, `annotBinderMeta`, `projModelName`), so
that the provenance gate stays in step with its source (task #11's
`beqRecursive` rule) and so that the install path (`Kernel/Checker.lean`,
which is what calls most of them) finds them waiting.

#### Coverage

`scripts/provenance.py coverage | tail -3`, con-leche 3e004805: **TOTAL
382/1018 covered (37.5 %), 636 uncovered** — up from **212/1018 (20.8 %)** at
this branch's merge base, the largest single jump in the port so far (+170).
Per file: **`Core.lean` 129/130**, **`FEnv.lean` 14/14**, **`PropRead.lean`
10/10**, **`Basis/Names.lean` 25/25**, `CoreC.lean` 0/80 → **3/80** (the three
knot declarations), `StateC.lean` 14/38, everything else unchanged.  So the
ledger agrees with the prose in every file.

**Note for task #19.**  `CoreC.lean`'s remaining 77 declarations are the
interned bodies and their telescope loops; the six wrappers are already here
and they are the only place that names a body, so the swap is six call sites.
The memo-policy reconciliation of the level operations (above) belongs to that
task, and so does `whnfCoreLoopFuel`'s only consumer.
