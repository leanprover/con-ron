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
(`CoreFnsI`/`coreKnotI`, `memoEI`/`memoBI`).  The port keeps that split:
the *bodies* are ported from `Kernel/Core.lean` as functions taking the
recursive calls as an explicit parameter set (Rust has no cheap closures
under Aeneas, so the knot is closed by a mutually recursive block of
wrappers that carry the fuel and the memo lookups), and the memo wrappers
are ported from `Cached/CoreC.lean` as a separate layer.  A later move to
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
crates/con-ron/          CLI, parser, frontend rewrites, thread pool
proof/                   Lake project: requires con-leche + aeneas (task #4)
  lakefile.toml          two path `require`s; one `lean_lib ConRon`
  ConRon.lean            the library root, imports everything below
  ConRon/
    Generated/           Aeneas output (committed, regenerated)
    Models/              TypesExternal.lean, FunsExternal.lean (Rc, ...)
    Abs/                 abstraction functions + NodeWF invariant
    Refine/              one lemma per ported function, same file split
    Main.lean            check_decls_refines, conron.no_proof_of_False
    Spike/LevelName/     the task-#3 spike, elaborated (task #4)
vendor/con-leche         submodule, pinned (3e004805)
vendor/aeneas            submodule, pinned (505b6ca3) — same rev as flake.nix
_tmp/aeneas-lean/        gitignored: vendor/aeneas/backends/lean + the v4.33
                         patch, built; produced by setup-aeneas-lean.sh, and
                         `require`d by path from proof/
spikes/                  feasibility experiments, kept as evidence
scripts/                 setup-aeneas-lean.sh, extract.sh, lint-rust-style.sh,
                         dump-decls, diff-test
```

Refinement lemma shape — **exact result on success** (task #5): a Rust
function that returns `ok y` computes *exactly* what the Lean function
computes on the abstracted inputs; nothing is claimed when Rust fails.
Exactness is needed because Boolean and `Option Bool` outcomes feed
branches on both sides; the accept-direction statement of §1 is a corollary
of exactness at every level.  Stored derived data (hash words) is governed
by a hereditary well-formedness predicate (`NameWF`, `LevelWF`, `NodeWF`:
the word equals the model's own hash formula of the children, code points
are valid `Char`s), preserved by every constructor, under which `abs` is
injective and `beq` is exact.  Forward reasoning from `ok`:

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
parsed `List DeclC` of any export in a simple binary format; the Rust core
reads it and runs `check_decls`.  Verdicts (and, for definitions, the stored
annotated terms) are compared against con-leche on its full fixture corpus
(`tests/e2e`, `tests/arena`, `tests/annot`; 225 streams) and on a Mathlib
export.  This decouples the core port from the Rust parser and catches port
mistakes at the function they happen in; a finer oracle (dumping
`whnf`/`infer` call pairs from con-leche) is added if debugging demands it.

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
same order as con-leche's `Verify/Cached/*` (≈ 20k lines).  The build-time
pins (basis blocks after annotation, Nat-op pin sets from `pins/*.json`)
become static Rust tables generated by a Lean script from con-leche's own
values.

## 5. Plan

Each phase ends at a gate; nothing in a later phase starts before the gate
is green.  "Fable" tasks are design/spec/theorem-statement work; everything
marked "Opus" is mechanical and delegated.

**P0 — infrastructure and spikes** (Fable, mostly done)
1. flake + direnv devshell with Charon's nightly, Charon, Aeneas.  ✔
2. Spike: `Rc` tree, fuel recursion, `&mut` state through Charon/Aeneas.  ✔
3. Spike: Aeneas Lean library on v4.33.0 (running).  Decide the toolchain.
4. Spike: compile the spike's generated Lean with the `Rc` models and prove
   `beq_refl` + one `size_refines`-style lemma, to fix the lemma shape.
5. Spike: scale — port `Kernel/Level.lean` + `Kernel/Name.lean` (~500 lines)
   for real, extract, measure Aeneas and Lean elaboration time.
   Gate: P0 spikes committed with numbers; DESIGN.md decisions confirmed.

**P1 — the verified core in Rust, differentially tested** (Opus, parallel
by module once types exist)
1. `ron::Nat`, `ron::HashMap` with unit tests.
2. Types: `Name`, `Level`, `PropWhen`, `Expr`/`Node` + smart constructors,
   `Literal`, `Env`/`FEnv`/`ConstantInfo`, `CState`, `DeclC`.
3. `ExprOps`, `Level` ops, `PropWhen` ops.
4. `Core` (whnfCore/whnf/infer/defeq/annotate knot) + `Cached/CoreC` memos.
5. `Checker`/`DeclCheck`, `StdAxioms`, `TrustAxioms`, Nat-op pins, basis
   tables (generated), `Inductives/*`, `Installed` (`check_decls`).
6. `scripts/dump-decls` (Lean) + Rust reader; differential test runner.
   Gate: every fixture verdict identical to con-leche; Mathlib export
   accepted; style lint clean.

**P2 — extraction** (Opus)
1. `scripts/extract.sh`; `proof/` Lake project builds the generated Lean
   with the `Rc` models; freshness gate in CI.
   Gate: `lake build` of `proof/Generated` green; timings recorded.

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
