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

**The pair memo, as it actually landed (task #30).**  Measurement demanded it
(task #28: eight fixtures do not finish), and it turned out **not** to need an
opaque function, hence not the fifth external hole this section budgeted for.
The memo is a plain `ron::HashMap<u64, Vec<(Expr, Expr)>>` whose key is a mix
of the two *stored hash words* — a field read each, where con-leche mixes the
two addresses — and whose stored pairs are verified on a probe by `ptr_eq` on
both components, exactly as con-leche's `probeHit` does.  **A key holds a
bucket of pairs and not one pair** (task #38, found by task #37): a hash key
collides precisely on the structurally equal, pointer-distinct objects the
memo exists for, so one slot per key let a node compared against two partners
in turn evict its own entry on every visit, and con-leche's own fixture for
that shape (`tests/e2e/tower_beqpair.ndjson`) went from `O(DAG)` to `3^n`.
Since `ptr_eq` is `false`
here, **the model writes the table and never reads it**: `beq_go` is the plain
structural descent, and the refinement proof needs two extra lemmas
(`probe_hit_false` and the bucket scan behind it) and no fact about the table
at all — not even `ron::HashMap`'s invariant.  In the binary a probe hits only when the stored
pair *is* the two objects being compared (the entry holds them, so their
identity stays theirs) and only completed `true`s are stored, so a hit repeats
an answer this same deterministic walk already produced for that pair.  That
is the same argument that makes the pointer fast path transparent, and it is
written out in `kernel/expr.rs`'s module note.  `beqBudget` is still not
ported: `beq`'s two guards run before the table is allocated, so a comparison
decided by identity or by the word allocates nothing (task #30 measured the
result: `Init`-scale cost unchanged).

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
  The Aeneas tutorial's verified hash map is the template.  **`new` allocates
  no buckets at all**, and the first `insert` allocates `MIN_CAPACITY` of them
  (task #35): the checker makes thousands of memo tables per declaration that
  never see an insert, and a table's capacity is invisible to the abstract map
  it refines, so the invariant merely gained an unallocated case.
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
  src/frontend/*.rs      one module per ConLeche/Frontend/*.lean (task #37),
                         plus basis_raw.rs — the *raw* pins the frontend
                         matches a stream against (task #37 deviation 4)
  src/bin/con-ron.rs     Main.lean: the driver and its exit codes
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
    Gen/                 the build-time table generator (task #22): the
                         `con-ron-gen-tables` exe that writes
                         `crates/con-ron-core/src/kernel/basis_tables.rs`
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
                         provenance.py, dump-fixtures.sh, diff-fixtures.sh,
                         diff-frontend.sh (the frontend's byte-exact oracle)
                         and diff-e2e.sh (the whole binary), task #37
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
`tests/{arena,e2e,annot}-expected.txt`, and writes the corpus's one pin dump
(`lake exe con-ron-dump-pins`, root `ConRon/Dump/Pins.lean`, format
`con-ron-pins/1`) that `scripts/diff-fixtures.sh` passes to every
`con-ron-check` run.

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

**The Nat-op pin sets are runtime data (decision, task #22; landed end to
end in task #31).**  Encoding the ~26.5k-node pin sets as generated Rust
overwhelms rustc and Charon, and the alternative hypothesis
`abs tables = natOpPinSets` cannot be discharged without `native_decide`.
Neither is needed: con-leche checks every pin by `isDefEq` against the
stream's own definition and checks the certificate proofs as theorems
against the hand-pinned `divModCertStmts` (149 nodes, generated source,
proved), so the pin list is a *hint* that affects completeness, never
soundness.  The Rust `check_decls` therefore takes the pin list as a
parameter, threaded from `cached::installed::check_decls` through
`annotDeclStep`/`checkDeclC` to `checker::check_div_mod_pin_loop`
(`kernel/nat_op_pins.rs` declares the record and nothing else — there is no
`nat_op_pin_sets()` constant, §3.4), and the unverified driver reads
con-leche's own `natOpPinSets` out of a **`con-ron-pins/1` dump**, a sibling
of `con-ron-decls/1` written by `lake exe con-ron-dump-pins` and specified in
`proof/ConRon/Dump/FORMAT.md` §7 (`con-ron-check --pins FILE`).  The theorem
is stated against a con-leche `checkDecls` that takes the same parameter —
which asks for a small upstream change: make `natOpPinSets` an argument of
`checkDecls` (`checkDecls mode pins ds`, with the shipped
`checkDecls mode ds := checkDecls mode natOpPinSets ds`) and check that
`model_exists` is parametric in it.  Until that lands, the pin-loop
refinement is stated with `abs pins = natOpPinSets` as a hypothesis and
the corollary is conditional; the basis blocks are *not* hints (their
denotations are pinned by the model), so they stay generated source
(`kernel/basis_tables.rs`, proved in `Refine/BasisTables.lean`).

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
  with counts, and the total covered/uncovered/skipped.  Printed, not
  committed (it churns); task-log entries quote the totals as progress.
  The denominator is *what is to be ported*: the declarations
  `scripts/provenance-skip.txt` lists as deliberately not ported are
  counted and reported separately (see **The deliberate skips** below).
* `locate <path> <decl>…` — print the canonical citation body
  (`<path>:<a>-<b> <decl>`) of each named declaration, i.e. the block
  `update` would relocate to.  It exists so that a *generator* can write
  citations no hand ever edits: `proof/ConRon/Gen/Main.lean` asks it for
  the raw pins each generated basis block is computed from, so the
  emitted `/// con-leche:` ranges are the gate's own and regeneration is
  a fixed point (task #33).

**Module-level annotations** (task #8 for `none`, task #22 for the citation
form).  A `//!` line covers the whole file and exempts every item in it from
the per-item requirement.  Two forms:

```
//! con-leche: none — replaces the runtime's `Nat`; spec in proof/…/NatSpec.lean
//! con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
```

The first is a module with no Lean counterpart (`ron/nat.rs`,
`ron/hashmap.rs`).  The second is a **generated** module that *is* one Lean
declaration's value (`kernel/basis_tables.rs`): repeating the same citation on
each of its seven functions would be noise, and `update` would have to rewrite
seven identical lines.  A module-level citation is checked exactly like an
item's — the range must exist at the pin and its first line must declare the
named constant — and it counts in the `coverage` ledger; what the module form
adds is only the exemption.  `update` rewrites it in place (a `Cite` remembers
whether it came from `///` or `//!`, so a moved range and a `CHANGED` marker
both keep the right comment form).

**What is not a declaration.**  `coverage`'s scan of con-leche skips lines
inside `/- … -/` block comments, `/-!` module docstrings included.  Without
that, a column-0 *phrase* in prose reads as a definition — `ExprOps.lean`'s
"inductive install" became a `def install` in the ledger (task #13 noted it);
twelve such phantoms across `Kernel/` disappeared when the skip went in, taking
the declaration total from 1 018 to 1 006.

**The deliberate skips** (task #33).  A con-leche declaration the port will
*never* have is not a hole in the ledger, but it must be *named* as such:
`scripts/provenance-skip.txt` is the allowlist, one line per declaration,

```
<con-leche path> <declaration> <reason>
```

with `*` as the declaration for a whole file, and the reason mandatory (a skip
with no reason is reported `MALFORMED`).  `coverage` subtracts the skips from
the denominator and reports them separately — `TOTAL 906/906 covered
(100.0 %), 0 uncovered, 100 deliberately skipped` — and `scripts/progress.py`
does the same in Lean lines, with a `skipped` column.  The list cannot rot
quietly: a skip that names no declaration of its file is `STALE`, one whose
declaration *is* cited after all is `REDUNDANT`, and either makes `coverage`
exit non-zero.  What is neither cited nor listed is still `uncovered`, which
is the ledger's only honest resting state for work that is owed.

Those two findings are checked for **every** entry, including the ones whose
file lies outside `COVERAGE_GLOBS` — `Main.lean` and `ConLeche/Frontend/**`,
the *cherries*, whose ledger is `scripts/progress.py`'s second table.  An
entry the walk did not reach is validated against the file it names instead
(task #40): the printed `TOTAL` stays the verified core's, and the list is
checked wherever it points, which is where it is longest.

Five kinds of thing are on the list, and each entry says which: elaboration-time
meta code (`BasisGen.lean`'s `#annotate_basis`, `trustPinEnv` — the Rust core
has no elaborator, so it carries the *results*); the proof-tier and mode-gated
variants of bodies the port has once (`CoreGated`, `CheckerGated`, `CoreIO`,
`pureFns`, `CoreC.lean`'s seven `*PC`/`*TC` instantiations); `Prop`s and
proof-carrying apparatus (the sixteen `*MemoInv`s, `Installed.lean`'s
`InstallRun`/`GroupChecked`/`collectChecks` family, `PropWhen.casesZ`);
the address-keyed apparatus of `Expr.beq` that §3.2's pointer axioms replace;
and driver-only rendering (`msSecs`, `declCLabel`, `ValueKind.word`,
`divModAttemptReason`, `Name.toString`, `reprPrec'` — §3.1: the theorem never
reads a message).  The long argument for each lives in the Rust module note of
the module that would have held it; the skip file is the machine-readable index
of those notes.

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

**What of the core is actually to be ported** (task #33).  Of the 1 006
top-level definitions of `Kernel/` and `Cached/` — 14 350 Lean lines of
definitional blocks — **906 (13 694 lines) are to be ported and are, 100 %**;
the remaining **100 (656 lines) are deliberately not ported**, each named with
its reason in `scripts/provenance-skip.txt` (§3.7): elaboration-time meta
code, the proof-tier and mode-gated variants of bodies the port has once,
`Prop`s and proof-carrying apparatus, the address-keyed `Expr.beq` apparatus
§3.2 replaces, and driver-only message rendering.  So the port's remaining
work on the core is the *proofs* (900 of those lines are covered by a
`_refines` lemma), not the translation.

**Measured (P0, tasks #3–#10):** Lean → Rust 2.5×, Rust → generated Lean
2.6×; Charon + Aeneas about 1.5 s per 1 000 Rust lines, zero iterations
on four crates written to §3.4; Lean elaboration of generated code ≈ 1 ms
per line; proofs ≈ 2.2 lines per Rust line, i.e. 20–60 lines per
single-scrutinee function and 60–270 for two-scrutinee matches (task #5),
so **8–20k proof lines** for the 22k-line core, tail risk in `defEq` and
the inductive routes.  The build-time
pins split (task #22): the **basis blocks after annotation** (192 interned
nodes) become a static Rust table generated by a Lean script from con-leche's
own value (`ConRon/Gen`, `kernel/basis_tables.rs`) and proved equal to it
(`ConRon/Refine/BasisTables.lean`), and so will `divModCertStmts`
(149 nodes); the **Nat-op pin sets** (20 183 nodes per
toolchain) do not — Charon is OOM-killed on one generated function that size —
and become runtime data in the unverified driver, which is sound because the
install gate re-checks every pin against the stream's own value and every
certificate against the pinned statements (see the task-#22 entry for the
measurements and the one con-leche-side generalisation it asks for).

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
4. `Core` (whnfCore/whnf/infer/defeq/annotate knot) + `Cached/CoreC` memos
   (tasks #18, #23).  ✔
5. `Checker`/`DeclCheck`, `StdAxioms`, `TrustAxioms`, Nat-op pins, basis
   tables (generated), `Inductives/*`, `Installed` (`check_decls`).
6. `con-ron-dump` (Lean, task #10 ✔) + Rust reader (task #19 ✔,
   `crates/con-ron-dump`); differential test runner.
   Gate: every fixture verdict identical to con-leche; Mathlib export
   accepted; style lint clean.

**Priority ruling (maintainer, 2026-09-12): translation to 100 % and the
checker running on the fixture corpus come first; the proof tier (P3)
waits.**  *"No point starting the proof effort when we can find behavioral
divergences another way (or before we find out if the performance is
acceptable)."*  Consequences: items 7–8 below are the critical path; the
`ExprOps` refinement (task #21) is parked on branch
`parked/task-21-exprops-refine` with its WIP; no new P3 task is started
until the differential run is green and Mathlib-scale performance is
measured.

7. `Installed.lean` (`check_decls`, the install and check phases) and a
   `con-ron-check` binary (unverified crate) that reads a dump and prints
   con-leche's verdict line with its exit codes; `scripts/diff-fixtures.sh`
   compares every fixture's verdict (and error position) with con-leche's
   expectation files (task #28).  ✔ — **298 of the 315** fixtures with a
   declaration list at con-leche's exit code, no wrong verdict, whole sweep in
   4 s (task #30 landed the pair memo and the eight towers with it); the 17
   left are the empty `Nat`-op pin table (data owed by task #22/#29).  The
   expectation files pin the exit code alone, so there is no error position to
   compare.
8. Performance: a Mathlib export (`lean4export` at the project toolchain),
   con-leche and con-ron side by side — instructions (`perf stat`), wall
   time, peak RSS; then the `beq` pair memo and other opt-ins of §3.2 only
   if measurement demands them.  **The corpus and con-leche's half of the
   comparison are done** (task #29, `scripts/corpus.sh`): three exports
   (`Init`, `Init Std Lean`, `Mathlib`), their `con-ron-decls/1` dumps and
   con-leche's verdicts and costs, in `_tmp/corpus/`; the number to beat is
   **12.8 T instructions:u and 8.6 GB for Mathlib**.
   if measurement demands them.  **Measurement demanded the `beq` pair memo
   and task #30 landed it** — hash-keyed and pointer-verified, so inside the
   Aeneas subset and with *no* new external hole; the eight tower fixtures
   accept in under a second and `Init`-scale cost is unchanged (±0.1 %).  The
   Mathlib comparison itself still needs the `Nat`-op pin data before
   `con-ron-check` gets past `Init`'s fold position 221.

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

**P4 — cherries** (Opus; **in progress**)
1. Rust parser (NDJSON, streaming), prelude, Nat-op reordering, projection
   rewrite, in-process inductive modeller, CLI with con-leche's exit codes,
   thread pool for the check phase.  **The parser, the prelude, the hoist, the
   projection rewrite and the CLI landed as `crates/con-ron` (task #37); the
   in-process modeller as `crates/con-ron/src/in_model` (task #39)**: the dump
   of the parsed list, generated `_model` records included, is byte-identical
   to the Lean frontend's on all 315 fixtures that have one and on
   `_tmp/corpus/{init,core}.ndjson`, with 0 differing, and the binary's exit
   code agrees with con-leche's expectation on 348 of 348.  **Task #40 closed
   the ledger**: the `--progress` heartbeat, the thirteen retired-flag
   rejections, `--no-mark-persistent`, the OOM/exit-code conventions and the
   taint-skip rule are ported, `con_ron::driver` is the one driver both
   binaries run, and the cherries read **100 % of what is to be ported**
   (7 647 of 7 647 Lean lines).  What is left of this item is the **thread
   pool**, which is `scripts/provenance-skip.txt`'s only owed entry and waits
   on the `Rc`/`Arc` decision.
2. Perf comparison against con-leche and the official kernel (PERF.md).
3. Optional: parser refinement against con-leche's naive reference parser.
   Task #37 wrote the statement down: every item of `frontend::scan_fast`
   cites the `Scan/Naive.lean` declaration that specifies it.

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
* `scripts/progress.py [--md]` is the standing quantitative report: per
  con-leche implementation file, Lean lines to translate (definitional
  blocks, minus the deliberate skips of `scripts/provenance-skip.txt`),
  translated (the blocks of the declarations a Rust item cites), verified
  (those cited by a Rust item that has its `_refines` lemma) and skipped,
  plus the sizes of the Rust, the generated Lean and the proofs.  The unit
  is a *declaration*, as in `provenance.py coverage`, and the line counts
  weight it by the size of its block (task #33 made the two agree: a
  citation that names a declaration credits the whole declaration, so a
  narrow range on a long doc comment no longer reads as a gap).  Task-log
  entries quote its totals.
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
`#guard_msgs` texts).  **The two `leanOptions` are the `aeneas` *package*'s,
so they do not reach `proof/`** — and task #22 found out the hard way that
without them Aeneas's `step` tactic cannot apply a single `@[step]` lemma in
our own files; set them per file (or, better, in `proof/lakefile.toml`) in any
file that uses `step`.  Mathlib is load-bearing for the library
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

### Task #20 — `Expr` refined (2026-09-12, Opus under Fable)

P3.3's second part: `crates/con-ron-core/src/kernel/expr.rs` is refined on its
generated model, in `proof/ConRon/Refine/Expr.lean`.  Every ported item of the
module has a lemma except the three hash producers and the `Hashable`
dictionary, which §3.2 exempts (see below).  `sorry`-free, elaborating with
**zero output** under `lake env lean`, `scripts/gates.sh` green, **no Rust
change** (`crates/` untouched, `extract.sh --check` passes unchanged).

**Size.**

| file | lines | declarations | `lake env lean` |
|---|---|---|---|
| `Refine/Expr.lean` | **2 509** | 104 | 9.4 s |
| `Refine/Abs.lean` | 435 (+88) | 53 | 1.7 s |
| `Refine/Level.lean` | 1 560 (+56) | 76 | 5.3 s |
| `Refine/PropWhen.lean` | 2 013 (+109) | 102 | 5.0 s |
| `Refine/Nat.lean` | 2 307 (+47) | 108 | — |

For comparison: `kernel/expr.rs` is 1 158 raw lines (709 extracted, 449
`#[cfg(test)]` — 404 code lines by task #11's count) and the generated
`kernel.expr` part of `Funs.lean` is ≈757 lines.  So **6.2 proof lines per Rust
code line** — above `prop_when`'s 5.3 (task #17) and for the same identifiable,
non-general reason: *two* 10×10 case analyses (below).

**The data word, and why the observed bits are provable.**  This is the one
module where the port's stored word and con-leche's `@[computed_field] data`
must agree bit for bit, and only on the **non-hash** bits: `mixHash` is opaque
in Lean and the port hashes its own bignums and strings anyway (§3.2).  The
proof never looks at a hash value; it goes by the *shape* of `packData`, which
is the same arithmetic on both sides:

* `pack_val` puts the port's `wrapping_mul`/`wrapping_add` chain in normal form
  (`h % 2^32 * 2^32 + b * 2^16 + f * 2 + lp`) and `pack_bits` reads the three
  observed fields back out of it — `b`, `f`, `lp` whenever the two range fields
  fit in 15 bits, **whatever `h` is**.  That is con-leche's
  `bvarOfData_pack`/`fvarOfData_pack`/`lpOfData_pack` on the other side.
* `wf_data : ExprWF e → bvarBits e = (absExpr e).bvarBRaw ∧ fvarBits e =
  (absExpr e).fvarBRaw ∧ lpBit e = (absExpr e).hasLP` then runs the two
  recurrences in lock step over the `ExprWF` derivation: ten cases, each one
  `pack_bits` beside the matching one of con-leche's thirty `@[simp]`
  constructor equations (`bvarBRaw_app`, `hasLP_lam`, …).  Those equations are
  *public and already proved* upstream, which is what made this cheap (72
  lines); had they not existed the same 30 facts would have had to be
  re-derived through `packData` here.
* the three observed readers are then one line each:
  `bvar_b_raw_refines : ExprWF e → expr.bvar_b_raw e = ok r → r.val =
  (absExpr e).bvarBRaw`, and the same for `fvar_b_raw` and `has_lp`.
  `expr::hash` gets **no** lemma, by §3.2.

Three port-side lemmas carry the arithmetic and are worth reusing:
`wrapping_mul_val`/`wrapping_add_val` (`.val = … % 2^64`, via
`UScalar.wrapping_*_bv_eq` and `BitVec.toNat_*`), and **five one-line
`@[simp]` lemmas naming the `u64` literals' `.val`** (`val_2_32`, `val_2_16`,
…).  Without those, `omega` sees `h.val * (4294967296#u64).val` as a *product
of two unknowns* and fails; with them every packing goal is linear and `omega`
closes it.  That is the single most useful thing this task learned about the
scalar model.

**`absExpr`'s injectivity is what makes `beq` exact, and it needs the whole
word.**  `absExpr` drops the `data` field, so the completeness half of
`beq_exact` — the word guard `data a ≠ data b → false` must not reject an
abs-equal pair — needs the *hash* bits too to be a function of the
abstraction.  They are, for §3.5's reason and with no hash formula in sight: a
well-formed node *is* what a smart constructor built from its children, a
smart constructor is a function, so equal children give an equal node
(`Result.ok_injective`).  `beq_go_data_ne` is that argument, discharged **once**
rather than in each of the hundred arms.

**Cost driver: the two 10×10 case analyses.**  `absExpr_injective` (394 lines)
and `beq_go_abs` (918) are 100 constructor pairs each and together are **52 %
of the file**; both were generated from a table by a Python script with ten
distinct diagonal bodies and one off-diagonal body.  The pattern that made the
off-diagonals free:

* injectivity: `obtain ⟨d2, rfl, …⟩ := <c>_inv h2; simp at hab` — `absExpr`
  maps the ten kinds onto ten *different* con-leche constructors, so `simp`
  closes the goal by constructor disjointness;
* `beq_go`: both branches of the word guard yield `ok false` once the kinds are
  concrete, so `simp only [… , ite_self, Result.ok.injEq] at h; rw [← h]; simp`
  is the whole arm.

For the ten diagonals, **`guard_step` is the leverage**: every arm of
`beq_go`'s descent has the shape `let y ← <test>; if y then <rest> else false`,
and

```lean
theorem guard_step (htest : ∀ y, test = ok y → y = decide P)
    (hrest : ∀ y, rest = ok y → y = decide Q)
    (h : (do let y ← test; if y = true then rest else ok false) = ok c) :
    c = decide (P ∧ Q)
```

turns each into one term, nested twice for `lam`/`forallE`/`letE`/`proj`.  Its
conclusion lands on con-leche's `<ctor>.injEq` verbatim for seven of the ten;
`lam`/`forallE` need `decide_eq_decide` + `tauto` because con-leche orders the
conjuncts `type ∧ body ∧ m` while the port tests `m` first.  **Recommendation
for `defEq` and the other two-scrutinee walks: write `guard_step` (or its
`Option`/state-monad analogue) before the case table, not after.**

**Reflexivity, and what it cost elsewhere.**  §3.2's transparency obligation
for the pointer fast path is `beq e e = ok true` *in the model* — a totality
claim, not a corollary of exactness — so it needs the same for every leaf of
the descent.  `level::beq` and `name::beq` already had theirs (task #5); this
task added `ron::nat`'s (`limb_ok`, `cmp_from_refl`, `cmp_refl`, `beq_refl`,
47 lines in `Refine/Nat.lean`) and `prop_when::beq`'s (`names_beq_from_refl`,
`beq_refl`, in `Refine/PropWhen.lean`), plus `levels_beq_refl` and
`literal_beq_refl` here.  Exactness, by contrast, needs **no** reflexivity
anywhere: the false direction goes through injectivity, not through "beq a a".

**Three additions outside `Refine/Expr.lean`**, each a fact about its own
module and put where the README's naming rule says it belongs:

1. `Refine/Level.lean`: `levels_have_param_refines` (+ its `*_from` loop) —
   listed as an unproved leftover by tasks #5 and #17, and needed because a
   `.const` node's level-param bit *is* `levelsHaveParam us`.
2. `Refine/PropWhen.lean`: `absPropWhen_injective` (+ `names_list_inj`) —
   a `lam` node stores a `BinderMeta`, so `absExpr`'s injectivity reduces to
   it.  The proof is `wfShape_toList` plus "among the four non-`Never`
   representations the parameter list determines the constructor", which is
   exactly what task #17's `Many` length clause was for; 22 of the 25 cases go
   by `simp_all`, the other three by the list length or `Vec.ext`.
3. `Refine/Nat.lean` and `Refine/PropWhen.lean`: the reflexivity lemmas above.

**Hard spots, in the order they bit.**

1. **`omega` and machine-word literals** — the `val_*` lemmas above.  Two
   hours of the task; the symptom is a counterexample listing
   `g := ↑↑h * ↑↑4294967296#u64` as an atom.
2. **`rcases`'s `-` pattern *clears* a hypothesis and cascades.**  Discarding a
   generated-code binder's *value* with `-` silently removed the `pack_data`
   equation that depended on it (`Unknown identifier hd` at the next line).
   **Rule for the rest of the port: in an `obtain` over a generated function
   body, use `_` for witnesses and `-` only for proofs.**
3. **The `if`-under-`max` bound.**  `satPred`'s `if b = satRange then …` sits
   inside a `max`, where neither `split` nor `split_ifs` reaches it; the fix is
   a standalone `satPred_lt` lemma stated with `ConLeche.satRange` *unexpanded*
   so that the atom `omega` sees matches on both sides.  Expanding `satRange`
   to `32767` in one place and not the other is what made the first three
   attempts fail — and it is also task #17's item 9 ("`rw` fails under
   `decide`") in a new costume: `rw [if_pos]` on a `Nat` equality whose
   `Decidable` instance still mentions `satRange` is a motive error.
4. **`level_has_param`/`levels_have_param` are called *unconditionally* but
   `has_params` is not.**  `sort_inv`/`mk_const_inv` can therefore hand out the
   leaf call as an existential, while `lam_inv`/`forall_e_inv` must take it as
   a hypothesis (`∀ hp, has_params m.pw = ok hp → lpBit e = …`) because the
   port's `||` chain short-circuits and never calls it when the type or the
   body already has a level param.  `has_params_ok` (a five-arm `match`, hence
   total) is what supplies the witness in `wf_data`.
5. `expr::beq_recursive` needed `expr.Expr._0._simpLemma_` *and*
   `expr.ExprNode.kind._simpLemma_` before the match would reduce; the
   deref-then-project idiom of every generated accessor needs both.

**The lemma inventory** (`_refines`-named per `ConRon/Refine/README.md`):
`bvar`, `fvar`, `sort`, `mk_const`, `app`, `lam`, `forall_e`, `let_e`, `lit`,
`proj` (each with `*_wf` and `*_inv`), `mk_bvar`, `bvar_pool_size`, `has_lp`,
`bvar_b_raw`, `fvar_b_raw`, `beq_recursive`, `levels_beq` (+ `*_from`),
`literal_beq`, `binder_meta_beq`, `beq` (`beq_refines` = `beq_exact`),
`eq2`; plus `data_eq`, `dup_eq`, `ptr_eq_eq`, `str_copy_eq`/`str_copy_from_val`,
`literal_dup_eq`, `binder_meta_dup_eq`, the word helpers' `*_val` lemmas,
`wf_data`, `absExpr_injective`, `absLiteral_inj`, `absBinderMeta_inj`,
`absLevels_inj`, and the reflexivity chain.  No lemma, by §3.2: `expr::hash`,
`binder_meta_hash`, `literal_hash` and the `Hashable` dictionary — a hash value
only picks a memo bucket, which §3.3's abstract-map relation does not see.
`#guard_msgs in #print axioms` on `app_refines`, `beq_exact` and
`bvar_b_raw_refines` is the committed gate at the end of the file: `propext`,
`Classical.choice`, `Quot.sound` and nothing else.

**Extrapolation, updated.**  Task #5 said 2.2 proof lines per Rust line, task
#17 measured 5.3 on `prop_when`, this task 6.2 on `expr` — but the trend is an
artefact of *arity*, not of depth: strip the two 10×10 tables (1 312 lines) and
the rest of `Expr.lean` is 1 197 lines for 404 Rust code lines, i.e. **3.0** —
in task #5's range.  The practical rule this suggests for §4's estimate: budget
a module at ≈3 proof lines per Rust code line **plus ≈1 line per ordered pair
of constructors it matches on two scrutinees at once**.  `defEq` remains the
place to watch, and it now has `guard_step` and a working recipe for a
hundred-arm table waiting for it.

**Left for next time.**  `expr::beq_recursive` is proved but nothing calls it
(as in Rust); `bvar_pool_size` likewise.  `levels_hash`, `name_lt` and the
other hash producers stay unproved by §3.2.  The shared
`ConRon/Refine/Basic.lean` that tasks #5 and #15 asked for is still not
factored out — `bind_eq_ok_iff` and friends now live in three places
(`Abs.lean` globally, `Nat.lean` and `HashMap.lean` locally), and `guard_step`,
`node_bits`, the `val_*` literals and the `*_from`-loop skeleton all belong in
it; that is a 30-minute task and the next module to need them is
`kernel::expr_ops` (82 declarations, the `isApp`/`getAppFn` family and the
exact `bvarB`/`fvarB` accessors that fall back to a memoised walk — the first
consumers of `wf_data`).
### Task #24 — The declaration checker (2026-09-12, Opus under Fable)

P1.5.  The declaration-checking family of `ConLeche/Kernel/` ported as nine
new modules: `checker_base.rs` (`CheckerBase.lean`, 292 lines), `checker.rs`
(`Checker.lean`, 569), `decl_check.rs` (`DeclCheck.lean`, 937),
`checker_split.rs` (`CheckerSplit.lean`, 121), `type_checker.rs`
(`TypeChecker.lean`, 60), `std_axioms.rs` (`StdAxioms.lean`, 375),
`trust_axioms.rs` (`TrustAxioms.lean`, 218), `trust_pins.rs`
(`TrustPins.lean`, 48) and `cached/checker_c.rs` (`Cached/CheckerC.lean`,
270), plus three dependency modules the family cannot be written without —
`basis_builder.rs` (`Kernel/Basis/Builder.lean`, the raw-pin DSL),
`nat_op_pins.rs` (`NatOpPinSet.lean` + `NatOpPins.lean`) and `basis_pins.rs`
(a stub for `BasisA.lean`; below).  `checkDecl` and `checkDeclsPure` now
exist in the crate, over the closed knot of task #18.

#### The `CheckerOps` collapse

`ConLeche/Kernel/CheckerBase.lean:30-53` writes the whole declaration checker
*once*, monad-polymorphically, against a record `ops : CheckerOps m` of the
core's five entry points plus `orElse`, and instantiates it twice:
`fueledOps`/`pureOps` (the pure knot, the verification's subject) and
`Cached/CheckerC.lean`'s `sharedOpsC` (the memoized knot the binary runs).
§3.1's knot ruling applies to it unchanged — **no trait in the recursion, no
closures** — so the record parameter is *dropped* and its slots are called by
name.  Three consequences:

1. **`kernel/type_checker.rs` is the one place the knot is named.**
   `TypeChecker.lean`'s seven entry points (`whnfCore`, `whnf`,
   `inferTypeCore`, `inferTypeIO`, `isDefEqCore`, `annotateCore`,
   `ensureSortCore`) become seven six-line functions over `core_c`/`core_k` at
   `core_k::check_fuel()`, and they are simultaneously `fueledOps`, `pureOps`
   and `sharedOpsC`'s five core slots — each carries all three citations.
   `pureFns` (`:24`) has no Rust spelling: §3.1's "bodies over wrappers" gives
   the port **one** knot, the cached one, so a refinement lemma about any of
   these is stated against `coreKnotI`, as §3.5 already writes it.
   `opE`/`opB`/`opS` (`CheckerC.lean:68-79`) collapse with it — `opE fe pick
   d e` is a *slot selector* passed as a function into a record projection,
   and there is no record to project.
2. **`orElse` is the one thing `CheckerC.lean` leaves standing**, and it is
   `cached/checker_c.rs`'s only item.  Ported exactly as `sharedOpsC` writes
   it, as a three-way `OrElseStep`: `.ok (true, s')` is `Matched`, `.ok
   (false, s')` is `Continue none`, `.error e` is `Continue (some e)`.  The
   **continuation** is a closure §3.4 forbids, so it stays at the one call
   site (`checker::check_div_mod_pin_loop`'s own tail call — task #18's
   treatment of `whnfStep`'s continuation), and the outcome the combinator
   delivers is carried in the enum, because that is what makes this the
   checker's only error-recovery point.  Recorded in the module doc, with the
   one memo-policy deviation it forces (below).
3. **Every `ops`-taking function takes `(mode, st, fe, …)`**, and the
   `FEnv`-indexed `F`-twins of `DeclCheck.lean` are the *same* Rust functions
   with a second citation (task #18's deviation 3: the port has one
   environment spelling, the index).  That collapses 21 of `DeclCheck.lean`'s
   40 declarations into their generic twins, `domsMatchAuxA` into
   `domsMatchAux`, and `Env.findCV?`/`FEnv.findCV?` into one `find_cv`.

#### The pre-insertion environment is a visibility bound, not a value

`checkDecl`'s `defn` and `opaque` arms hold **two** environments at once:
`env`, the pre-insertion one every certificate check runs in, and `env2`, the
extended one the guards read (`natOpGuard env2`, `env2.find? c`,
`divModEnvGuard env2`, `reduceStoredOk env2`).  Lean can, because its
environments are persistent; task #14 ruled that the port threads the index
*linearly*.  The resolution is con-leche's own `FEnv`: an entry carries its
installation counter and `FEnv.restrictTo k` lowers the visibility bound in
`O(1)` (con-leche task #108).  So the two views are **one index at two
bounds** — `k = fe.visibleBelow` is read off before the push, and a function
that needs the pre-insertion view takes the index by value, restricts,
checks, and restores the bound before handing it back.  That is §3.5's "phase
B needs exactly one view at a time — it lowers the bound for a record and
raises it back" made concrete, with no `fenv::dup` (which rebuilds the index)
anywhere on the path.  It changes two signatures: `check_div_mod_pin` and
`check_reduce_pin` return the index where the Lean returns `Unit`.

#### `matchesPin` is compared against the RAW pins, and that is exact

`StdAxioms.lean` and `TrustAxioms.lean` write their pins twice: the *raw*
ones, hand-written with `Basis/Builder.lean`'s DSL, and the *annotated* ones
(`iffA`, `propextA`, `choiceA`, `reduceNatCvA`, `ofReduceNatA`, …) computed
from them at elaboration time by `#annotate_basis`/`#annotate_pins`.  A grep
of the implementation modules settles how the annotated forms are consumed:
**every** use goes through `ConstantVal.matchesPin`, whose type test is
`a.erasePw == b.erasePw`, i.e. up to every binder's prop-ness datum — and
`annotateBody` (`Core.lean:2746`) changes *nothing else* in a `letE`-free
term, which no pin is.  So

```text
matchesPin cv (annotate pin) = matchesPin cv pin
```

and the port compares against the raw pin, which it can write down, with the
annotated twin cited on the same item.  A unit test pins the argument: the
pins match themselves, a wrong type does not, and a pin whose binder data has
been rewritten still matches while `Expr.beq` says the terms differ.  **Task
#22 therefore owes this task no pin table for the axioms at all** — with two
exceptions, below.

`Expr.erasePw`/`matchesPin` (the specification) and
`Expr.erasePwEq`/`matchesPinFast` (the executed lockstep descent, `@[csimp]`)
are both ported, as task #13's `@[csimp]` rule asks; a test checks they agree
on all 100 pairs the ten pins form.

#### The three stubs, and why each is sound

* **`kernel/nat_op_pins.rs`: `nat_op_pin_sets()` is empty.**  In con-leche the
  variant list is spliced from the committed `pins/*.json` dumps by
  `#load_natop_pins`; generating it is task #22's.  `checkDivModPinLoop` on an
  empty list is its `[]` arm — the decline con-leche itself gives a stream
  matching no variant — so the loop is exercised with zero pins, and the only
  effect is that `Nat.div`/`Nat.mod` streams decline.
* **`kernel/basis_pins.rs` is new, and task #22 should delete it.**  Two of
  the nineteen annotated basis pins are consumed by an **exact**
  `ConstantInfo` equality rather than through `matchesPin` — `env.find? eqName
  = some eqA` and `env.find? natName = some natA` — so the erase-`pw`
  argument does not cover them.  They are spelled there as predicates on the
  stored constant (`is_pinned_eq_basis`, `is_pinned_nat_basis`) plus
  `BasisKind.declsA`, and the stubs answer `false` / the empty block.  A
  `false` declines, which is the verdict con-leche gives a stream that never
  installed the pinned basis; an empty block installs nothing, so a later
  declaration mentioning a basis constant fails `constsResolve`.  Both are
  declines, never accepts (§1).
* **`checkDecl`'s `.indDecl` arm declines past the parameter check.**
  `indParamsOk` runs first and for both routes, as con-leche task #228
  insists (a wrong `nparams` is a *reject*); the dispatch itself —
  `nativeParts?`, `checkNative`, `checkModeled` — is
  `ConLeche/Kernel/Inductives/*`, a family this task does not port.

#### The two Aeneas errors, and the one external hole

Charon succeeded on the first run.  Aeneas gave **two** errors, both the same
shape, and both in a *newly written memoized walk*
(`expr_ops::all_level_params_defined_go`, `decl_check::consts_resolve_f_go`):
*"Could not match the contexts"* at the arm's last expression.

* **The cause is a branch inside an arm of a `&mut`-threaded `match` that then
  joins on the memo insert.**  The Lean arm is `let (b₁, memo) := go f; let
  (b₂, memo) := go a; (b₁ && b₂, memo)`, and the obvious transliteration `b1
  && b2` is a *branch* (`&&` short-circuits), so the arm ends in two borrow
  contexts that merge with the other arms at `memo.insert`.  Rewriting it as
  an `if` nest (§3.4's pattern 9) does **not** help — the `if` is the problem.
  What works is task #14's fix: **lift the join into a call**,
  `expr_ops::bool_and(b1, b2)` / `bool_and3(b1, b2, b3)`, so the branch lives
  inside a callee where no `&mut` is live and every arm is one straight-line
  expression (this is the shape `rename_consts_go` and
  `instantiate_level_params_go` already had, which is why they never failed).
  Both operands are still computed before the call, which matters: a
  short-circuit would be a *memo-policy* deviation — fewer entries written —
  not just a shape one.  **Rule for the next porter: a memoized walk's arm
  must end in a call or a constructor, never in a branch.**
* **A fifth external hole, caught and removed.**  `vec![65, 66, 67]` — the
  natural spelling for a pinned name's code points — emits
  `core::mem::maybe_uninit::MaybeUninit` into `TypesExternal_Template.lean`.
  Every one of the 23 non-test `vec!` literals is now task #14's idiom, a
  `const S: [u32; N]` plus `core_types::code_points(&S)`, and §3.2's standing
  gate holds: the templates are **exactly the four `Rc` axioms and the `Rc`
  type**.

#### Constructs that do not survive transliteration

Beyond the collapses above, and all a-priori except the `bool_and` one:

1. **`domsMatchAux` is monomorphic at the identity view.**  Its `g : Nat →
   Expr → Expr` is `fun _ e => e` at every call site in this scope; the one
   renaming site (`checkProjIotaF`) is the inductive family's, and the
   abstraction returns with it (task #18's `liftFueled` rule).
2. **`Basis/Builder.lean`'s binder-name arguments are gone.**  `pi "a" ty b`
   takes the `Init.Prelude` spelling for the reader only — `Expr` has no
   binder name — so `pi`/`piI`/`piA` are one Rust function with three
   citations and `lm`/`lmI` one with two.  A `&str` parameter would also be
   the one shape task #14 measured Aeneas failing on.  `BasisDSL.rule` **is**
   `env::rec_rule_parsed`, which gained a second citation rather than a twin.
3. **`divModCertStmts`' thirteen local builders are named functions**
   (`cert_ble2`, `cert_eq_b`, `cert_eq_n`, `cert_op2`, `cert_sub2`,
   `cert_mod2`, `cert_div2`, `cert_add2`, `cert_mul2`, `cert_one`, `cert_two`,
   `cert_rec_rhs`, `cert_base_rhs`), as `natOpEquations`' four were at task
   #18; `core_k::nat_eq_ap2` is already the binary-application builder and is
   reused.  The eight branches keep their arm order and their comments.
4. **`divModAttemptReason` and the `tried : List String` accumulator are not
   ported.**  They render the per-variant decline text; §3.1 says message
   strings need not match, and the decline is a fixed message.  The *outcome*
   still flows (`or_else_step`'s payload), because that is the combinator.
5. **Two-list recursions become one index recursion** with three arms — both
   exhausted, both in range, or the arity throw (task #14's point 7):
   `check_typed_list`, `check_def_eq_list`, `check_div_mod_certs`.  A `zip`
   (`divModCertsGuard`) stops at the shorter list, so its bound is the
   minimum.
6. **`fv :: fvs` is a front `Vec::insert`** in `openPisAtFvars` and
   `openPisAtFvarsFGo`, `O(width)` where Lean's cons is `O(1)` — deliberate
   and bounded by the telescope width (task #14's point 5 for `Env.consts`).
7. **A long `do` block with an annotation in the middle is split at the
   annotation**, so the state-threading call is a tail call and the guard
   groups never join on a borrowed state: `check_constant_val` →
   `check_constant_val_after_annot`, and the same for `check_defn_val`,
   `check_thm_val` (three functions: the is-a-proposition gate, the witness
   guards, the comparison), `check_opaque_val`, `check_proj_rule` (four:
   syntactic, well-formedness, shape, the definitional pins) and
   `check_value_group`.  This is task #18's rule for a gated certificate whose
   arms rejoin, applied prophylactically — and given the two errors above,
   worth applying.
8. **`Expr.allLevelParamsDefined` came with the task.**  `checkConstantVal`
   asks it of every declaration's type, and task #13 had left it owed ("the
   `Level.lean` completion task"): the spec walk, the memoized `*Go` and the
   executed `*Fast` are now in `expr_ops.rs` beside
   `instantiate_level_params`, where task #13 put the other `Expr` operation
   `Kernel/Level.lean` spells for import order.  `level.rs`'s "not ported
   here" note is updated.
9. **`checkMemberValF`'s local `f : Name → Name` is a dictionary struct**
   (`decl_check::ModelRename`, task #9's pattern 1), over
   `expr_ops::NameToName`.
10. **`ValueKind`/`ValueGroup` were already ported** (task #14 took the three
    seam records); `checker_split.rs` holds only the three functions, and
    `ValueKind.word` stays unported (message rendering).
### Task #23 — `CoreC.lean`: the cached bodies and level memos; the knot ties them (2026-09-12, Opus under Fable)

P1.4's second half, and the reconciliation task #18 flagged: the rest of
`ConLeche/Cached/CoreC.lean` (2 091 lines, 80 declarations, 3 covered) ported
into `crates/con-ron-core/src/cached/core_c.rs`, the `Cached/StateC.lean`
leftovers of task #14 closed in `cached/state_c.rs`, and **the knot re-pointed
at the cached bodies**.  The crate's executed checker core is now the one
con-leche executes, memo policy included.

#### The reconciliation, concretely

Task #18 tied `CoreC.lean`'s six wrappers to `Kernel/Core.lean`'s bodies.
Those bodies compare levels with `Level.isEquiv`, instantiate stored constants
with `instantiateLevelParams` and substitute with `instantiate1` — so
`lsimpC`, `lnzC`, `eqvC`, `instC`, `ienv`, `constTyAt`, `constValAt` and
`ruleRhsAt` stayed **empty however much work the checker did**.  §3.1 forbids
exactly that ("the same memo tables with the same keys, inserted and cleared
at the same points"), and task #18 recorded it as the port's one memo-policy
deviation.  It is gone.  Per map, who writes it now:

| map | written by |
|---|---|
| `whnfCoreC` `whnfC` `inferC` `inferIOC` `annotC` `defeqC` | the six wrappers (`memoEI`, `memoBI`) — unchanged |
| `lsimpC` `lnzC` `eqvC` | `state_c::is_equiv_l_m`/`simplify_l_m`/`is_non_zero_l_m`, reached from every `isEquivLM`/`isEquivListLM` site in `core_c` |
| `instC` | `state_c::inst_list_m`, reached from `iota_certs_i_aux` and `beta_peel_i` — the two bulk-substitution sites.  The four telescope loops use `instListRevM`, which the Lean leaves **unmemoized on purpose**, so they write nothing here |
| `ienv` `constTyAt` `constValAt` `ruleRhsAt` | `state_c::const_ty_at_m`/`const_val_at_m`/`rule_rhs_at_m`, reached from every stored-constant read |

Two `Level.isEquiv` sites stay **deliberately unmemoized because the Lean's
are**: `inferBodyI`'s `.proj` clause (`CoreC.lean:1370-1377`) and
`ProjEntry.fireOk`.  Keeping them off `eqvC` *is* the policy.  A unit test
pins the reconciliation directly (`the_level_memos_are_written_by_the_core`):
one `defeq` of `Sort (max u u)` against `Sort u` fills `eqvC` and `lsimpC`,
and the second comparison of the same pair writes nothing.

#### The dead-code decision: the pure bodies left the crate

`CoreC.lean` has its own twin of **every** `Kernel/Core.lean` block that makes
up the knot, and it is the twins the executed checker runs.  So
every `Core.lean` body the twins supersede is **no longer in the crate**: 84
functions (the 77 that threaded `&mut CState` plus `unfold_definition`,
`infer_const`, `infer_forall_check`, `params_subst(_from)`, `pins_subst_from`
and `rec_fire_comparands`) were deleted from `core_k.rs`, and their
`Core.lean` citations are now the **second `con-leche:` line** on the twin in
`core_c.rs`.  The rule, and why it is not task #18's "port the dead leaves
anyway":

> a superseded body *threads the same knot*, so keeping it would put a second
> copy of the whole mutually recursive block into `Funs.lean` — 84 more
> `partial_fixpoint` definitions and ~6 000 more generated lines for
> functions nothing executes.  A superseded **pure leaf** costs one small
> definition, so those stay, exactly as task #18's eleven do.

Four such leaves are dead and kept: `beta_gate_fires` (the pure β gate; the
cached sites read `mode.betaSkip`), `eta_projs`/`eta_projs_from` (superseded
by `proj_apps_i`, but `etaFabArgs`/`etaFabArgsE` are written against them and
are dead in the Lean too) and `consts_resolve` (whose memoized `ExprC` twin is
`state_c::consts_resolve_fc`).  What stays in `core_k.rs` is everything the
cached bodies *call*: the syntactic readers, the pinned name tables and
`Nat`-op pin sets, the install-time rule bits, the shape conjunctions
(`struct_eta_shape_ok`, `unit_shape_ok`, `proj_fire_shape_ok`, `fab_scope_ok`),
the pure inference-clause pieces, the four loop budgets, the `Vec` helpers and
the owning environment probes.  `core_k.rs` therefore went **5 883 → 2 714**
extracted lines, and `Kernel/Core.lean` stayed **130/130 covered** — better
than task #18's 129/130, because `core_c::infer_at_i` now cites `CoreFns` and
`CoreFns.ioView` as well as their `I`-twins.

#### Where the cached bodies are a different *algorithm*

Most twins are the spec body with the operations swapped.  Five are not, and
the port follows `CoreC.lean` rather than `Core.lean`:

1. **Bulk beta** (`whnf_app_i`/`beta_peel_i`, con-leche's task #50): the
   argument loop consumes the whole spine, batching consecutive λ binders into
   **one** `instListM` instead of a chained `instantiate1` per redex.
2. **The head-normalization loop** (`whnf_core_step_i`/`whnf_core_loop_i`,
   task #106): every *reduction* step is iteration on the loop's own budget
   (`whnfCoreLoopFuel`, whose only consumer task #18 left waiting), so a chain
   no longer charges the shared recursion-depth budget one unit per step.  A
   unit test pins it: `(λ x. (λ y. y) x) a` head-normalizes at `fuel = 3`.
3. **Bulk telescope consumption** (`infer_spine_i`/`infer_spine_io_i`, task
   #50): the Π-telescope is walked against the whole spine with deferred
   substitution.  This replaces task #18's `infer_app`/`infer_app_io`/
   `infer_app_cert` split.
4. **Binder-telescope loops** (`infer_lams_i`/`infer_pis_i`,
   `annotate_lams_i`/`annotate_pis_i`, task #72): a whole binder chain is
   peeled with only the domains substituted on the way in, the leaf is
   inferred or annotated once on the bulk-opened body, and the chain is
   rebuilt with one `abstractRangeM` per domain.  The λ *annotation* loop is
   taken only on a bvar-closed node (`bvarBoundM e = 0`); otherwise the spec's
   chained clause runs, which is `annotate_lam_chain_i`.
5. **`ensureSortI` returns the level** and `iotaRecI` reads its rule's
   right-hand side through `ruleRhsAtM` rather than instantiating it.

`inferBodyIOI` keeps the **chained** ∀/λ clauses on purpose (looping the io
lane would owe con-leche's whole loop-identification walk family a second,
io-graded instance), so the io body overrides exactly three clauses and
delegates the rest to `inferBodyI` — which is why `infer_body_i` carries the
`io: bool` grade flag that *is* `CoreFnsI.ioView`.

#### Constructs that do not survive transliteration

Beyond task #18's four global deviations (all still in force; `&mut CState`
now appears in no `core_k` function at all, which is the measure of what
moved):

1. **`certAtI`/`certUnlessI` are spelled out at their sites.**  Both take the
   certificate as a `CheckCM Bool` *argument*, i.e. a closure (§3.4); each
   site is `if env::certs(mode) { <the certificate> } else { Ok(true) }`
   (resp. `if env::certs(mode) || keep`), which is the cited `@[inline] def`
   after inlining.  There are **nine** such sites, and per `CoreC.lean`'s own
   docstring that list *is* what the trusted core omits beyond group A: the
   two in `struct_eta_cert_steps_i`, one in `struct_unit_steps_i`, three in
   the `majorToCtorI` branches, one in `k_type_and_irrel_i`, and the parameter
   comparison and the ι certificate family in `iota_rec_checks_i` /
   `iota_rec_telescopes_i`.  This is also a *behavioural* difference from the
   `Core.lean` bodies, which ran several of those certificates
   unconditionally.
2. **`annotateBindersOutI`'s `mk` node constructor is an `is_forall` flag**,
   as task #18's `annotate_binder` already had it, and `pw?.map (fun _ => …)`
   is `annot_pw_thread_i`.
3. **`List` accumulators are `Vec`s.**  `iotaCertsIAux`'s and `betaPeelI`'s
   `arg :: acc` is `expr_ops::cons_expr`, an `O(n)` copy where Lean's cons is
   `O(1)`; the list's *value* — which is what the `instC` key is — is the
   cited one.  The `Array` accumulators (`inferSpineI`, the telescope loops)
   are `Vec`s taken by value and pushed, as in the Lean.  A `List` stack
   becomes a `Vec` whose **last** element is the innermost binder, walked
   downwards by a remaining-entry count `p`.
4. **`Tn`/`T` and `_nI`/`_cI`/`_jI` collapse to one parameter.**  They are the
   retired arena's interned/raw name split, which con-leche's task #198
   collapsed but left in the signatures (`let Tn ← pure T`, `_nI` with a
   leading underscore).  `projAppsI`, `constTyAtM`, `constValAtM` and
   `ruleRhsAtM` each lose one or two arguments.
5. **The seven named concrete cores are not ported, and that is not an
   omission.**  `whnfCoreBodyPC`…`defeqBodyTC` are *definitions, not clones*:
   each is one of the bodies at a literal mode.  The port's mode is a runtime
   `&CheckMode`, so `whnf_core_body_i(&CheckMode::Verified, …)` **is**
   `whnfCoreBodyPC`; a Rust alias per mode would be seven dead functions with
   no content.  That is the whole of `CoreC.lean`'s 73/80.

#### `StateC.lean` completed: 14/38 → 38/38

Task #14 left five groups "needs `expr_ops` or `Kernel/Basis`".  All are
closed, but not all in `state_c.rs`, and the split is a finding:

* **the seven `*C` index guards** (`isUnitLikeTyC`, `isCtorAppC`, `headHintC`,
  `unfoldableHeadC`, `sameConstHeadsC`, `rawNatLitC?`, `etaCtorShapeC`) are
  *the same function* as `Kernel/Core.lean`'s originals, because the port
  already reads the environment through `FEnv` (task #18's deviation 3).  They
  are `core_k`'s, with a second citation there.  So are `litToCtorIfNatI` and
  `annotBinderMetaI`, whose twins are the spec's under a `pure`, and
  `ProjEntry.typeAtI`, which is `typeAt`'s formula verbatim.  Duplicating any
  of them would have been gratuitous — one spelling, two citations, §3.1.
* **`bvarBoundM` and eight of the nine `*M` wrappers** are
  `pure (<a syntactic operation>)`.  Task #14's rule 9 says such an action is
  "the plain Rust function"; the *reason* it gives is the dead state
  parameter, so they are named, state-free functions here forwarding to
  `expr_ops` — `CoreC.lean` calls them by these names and the refinement tier
  wants one lemma per name.  One of the eight is not an alias at all:
  `inst_list_rev_m` reverses the accumulator, because `instantiateRevGo`'s
  `vs[vs.size - 1 - (i - d)]` is `instantiateListGo`'s `vs[i - d]` on the
  reversed array, at every depth including its own `bvar` re-entry.  Both bulk
  wrappers run the *executed* walk, `instantiate_list_fast` (`ExprOps.lean`'s
  `@[csimp]`-identified memoized DAG pass), not the pure `instantiate_list`
  beside it.
* **`instListM` is the one genuinely stateful wrapper**: it owns `instC` and
  the 32 000 000-entry cap.  The cap decision is `inst_list_m_reset_at(s,
  cap)`, with `inst_list_m_reset` passing `instCCapC` — the bound is a
  parameter *so the reset has a unit test* without allocating 32M entries.
* **`piResidualM` — the tenth wrapper — lives in `core_c.rs`**, at its one
  call site: the operation it wraps is `Core.lean`'s `piResidual` (whose
  `ExprOpsC` twin `piResidualAcc` is the bulk form of the same function), so a
  `state_c` wrapper would have to reach back into `core_k`.
* `storedTyIdxM`/`storedValIdxM`/`constTyAtM`/`constValAtM`/`ruleRhsAtM` and
  the memoized DAG walk `constsResolveFCGo`/`constsResolveFC` are here, with
  their probes.

`Cached/ExprOpsC.lean` is **not** ported (its `Kernel/ExprOps.lean` original
is, as `expr_ops`): the twins compute the same values, differing by memoising
the DAG walk, which `expr_ops`' own `*_go` memo tables already do.
con-leche's `ExprOpsC` docstrings say exactly this ("not as a
*computation*").  Two of its declarations are cited anyway, on the two Rust
items that *are* their port (`ProjEntry.typeAtI`, `instantiateRev`), so the
file reads 2/37 rather than 0/37.

#### The pointer-identity sites (§3.2)

`CConstE`'s tag validation is the one new family.  `storedTyIdxM` and
`storedValIdxM` validate with `Expr.exprPtrBEq`, which is *structural*
equality with a physical-equality shortcut (`ExprOps.lean:2382-2388`), and
`expr_ops::expr_ptr_beq` is that composition with the shortcut modeled `false`
(§3.2's standing treatment, discharged there by the reflexivity of
`Expr.beq`).  So the model takes the `beq` branch and answers exactly what the
program answers — and the branch is unobservable anyway: `ent.ty` is by
construction the conversion of `ent.tyE`, and `ExprC = Expr` since con-leche's
task #198, so the conversion is the identity and both arms return the same
value.  A unit test pins all three outcomes (validating tag, structurally
equal rebuilt tag, different value).  Nothing else in this task reads pointer
identity: the memo keys go through `expr::beq`, whose own fast path §3.2
already covers, and `beqPtr` on `Name`/`Level` is untouched.

#### The six Aeneas errors, and the two rules they confirm

Charon succeeded on the first run.  Aeneas gave **four** errors, then two
more after the first round of fixes — all six the two shapes the port already
knows, and all six fixed by a-priori-legal restructuring:

* **A borrow from the index, consumed into a scalar, then joined with a
  branch that touches the state** (task #14's rule) — `proj_cert_i`'s
  `.ctorInfo` test and `infer_const_i`'s two-field read, *"Internal error,
  please file an issue"*.  Fixed by lifting each into its own function
  (`is_ctor_stored_i`, `const_shape_probe_i`), where the borrow dies at the
  call boundary.
* **A gated certificate whose two arms rejoin** (task #18's rule, met three
  times) — `infer_spine_io_i`'s `mode.ioSkip` gate in *both* its arms, and
  `annotate_binders_out_i`'s `pw?.map` and `mk` node choice, all *"Could not
  match the contexts"*.  The `mk` choice and the `map` became their own
  functions (`annot_node_i`, `annot_pw_thread_i`); the io gate became **two
  tail calls**, the skip arm continuing the walk directly and the certifying
  arm continuing it behind the certificate.  The duplication is the price
  task #18 already paid in `infer_app_io`, and here it is a *better* reading
  of the Lean: the skip arm never builds `dom'`, which is the point of the
  licence.

Rule for the next porter, now with five witnesses: **any `if <gate> { Ok(x) }
else { <state-touching call> }` whose result is then matched must be two tail
calls.** `lake build` gave no error at all this time — task #18's `¬`-in-value
lesson held.
### Task #25 — The inductive routes (2026-09-12, Opus under Fable)

P1.5.  All ten files of `ConLeche/Kernel/Inductives/` (3 983 lines, 152
top-level declarations, 0 covered) ported as
`crates/con-ron-core/src/kernel/inductives/`, plus the inductive-route stages
of `ConLeche/Cached/CheckerC.lean` — which is what the shipped binary runs on
an inductive block.  The crate now has **both** install routes for an
inductive declaration: the *direct* (fixpoint) route, which checks a block
against the reference kernels' own inductive-declaration checks and
**generates** its recursor, and the *modeled* route, which checks every member
against the in-process modeller's `_model` artifacts.

**Nine modules, one per Lean file** (`kernel/inductives/mod.rs` lists them):
`struct_parts`, `sum_parts`, `native_parts` (the pure recognition and
generation layer), `struct_install`, `sum_install`, `native_install` (the
direct route's stages), `modeled` (the modeled route), `inductives_c` (the two
cached drivers), and `checker_local` (see below).  The three `*InstallF.lean`
files have **no module of their own** — deviation 1 below.

#### Three deviations that apply to the whole directory

They are recorded once in `mod.rs` rather than on 300 items.

1. **One spelling of the environment: `fe: &FEnv`** — task #18's deviation 3,
   now cashed in at scale.  con-leche writes each install stage *twice*, over
   `Env` (`*Install.lean`, the pure fueled checker the verification tier
   reasons about) and over the index (`*InstallF.lean`, what the executable
   runs); the two differ only in `env.find?` versus `fe.find?` and in
   `⟨ci :: env.consts⟩` versus `fe.push ci`.  The port has **one function per
   pair, carrying both citations**, so `StructInstallF`, `SumInstallF` and
   `NativeInstallF` are covered 5/5, 8/8 and 5/5 without a Rust file, and
   `Modeled.lean`'s stages carry their `Kernel/DeclCheck.lean` `*F` twin as a
   second citation.  That is 18 Lean declarations the next task does not have
   to port.
2. **`CheckerOps` is dissolved into direct wrapper calls.**  The whole
   declaration checker is written once against a record of five closures plus
   the `orElse` combinator; §3.4 forbids closures and §3.1's knot rule forbids
   a trait in a recursion, so `ops.whnf env d e` is
   `core_c::whnf(mode, core_k::check_fuel(), st, fe, d, &e)` — the wrapper, by
   name, at exactly the fuel `sharedOpsC` passes (`coreKnotI mode fe
   checkFuel`).  `ops.ensureSort` is `core_k::ensure_sort`; `orElse` is not
   reached from these routes (its one caller is the Nat-op pin gate).
3. **`StructWalkers` is dissolved too.**  `StructInstallF.lean:50-71` passes
   the direct install's two whole-tree traversals as a record of closures so
   that the cached driver can supply memoised twins
   (`Cached/CheckerC.lean:52` `structWalkersC`).  Both walkers the port has
   *are* memoised — `core_k::consts_resolve` is the one spelling of
   `Expr.constsResolve`/`constsResolveF`/`constsResolveFC`, and
   `struct_parts::struct_proj_bodies` of
   `structProjBodies`/`structProjBodiesC` — and con-leche's own
   `structWalkersC_eq_plain` says the record is the specification.  So the
   record is gone, the walkers are called by name, and because their memos are
   per-call and local **no memo policy is touched**.

#### `checker_local`: what a route needs from the checker family

The install routes sit *on top of* `Kernel/CheckerBase.lean` and
`Kernel/DeclCheck.lean`, which are task #24's `kernel/checker*.rs`.  Rather
than stub anything, this task put **exactly what an inductive route needs, and
nothing else**, into `kernel/inductives/checker_local.rs`, each item with its
citation: `unwrapOr`, `openPisAtFvars`/`openPisAtFvarsF`, `domsMatchAux` (with
the `DomView` dictionary its `g` argument becomes), `checkConstantVal`,
`checkTypedList`/`checkAnnotList`/`checkDefEqList`, `isEqHead`/`eqHeadLevel`,
`Env.findCV?`, `checkProjShape`, `checkProjRule`, and the derived
`DecidableEq`s of `Kernel/Env.lean`'s stored-constant records.  Task #24's
unification is a move plus a `use`; no caller spells a body.

Two items are owed elsewhere and say so:

* **`Expr.allLevelParamsDefined`** (`Kernel/Level.lean:256-339`, the fourth
  `@[csimp]` family of the port) belongs in `kernel/level.rs` — task #13
  recorded it as still owed and this task is its first consumer, so it lives
  in `checker_local` for now.
* **`eqA`**, the annotated pinned equality former, is task #22's
  `kernel/basis_tables.rs`.  Four sites need the guard
  `env.find? eqName = some eqA` (`checkIndRecs`, `checkProjLookups`,
  `checkEtaThm`, `checkUnitThm`), two of them in a pure `Bool`, so a monadic
  "run the annotation pass now" is not available.  The pin is therefore spelled
  out — and **`eqA = eqRaw`, which is a fact, not an assumption**: `eqA` is
  `#annotate_basis`'s output, i.e. `annotateCore .verified` applied to
  `eqRaw`'s type, and every binder of `∀ {α : Sort u} (a b : α), Prop` has a
  codomain that is a `Sort` or a `∀` whose datum is already `.never`, so
  `annotPwPi`'s head-symbol reader answers `.never` at all three — the parse
  placeholder the raw pin carries.  A **test** runs `core_c::annotate` on the
  pin and compares, so a change upstream breaks a test rather than a verdict.

#### The generated recursor, built in the cited order node for node

`checkNativeRec` generates the recursor's type and compares it with the
stream's by one closed `isDefEq`; `nativeRulesOk` compares the stream's rule
*bodies* with the generated ones by **structural equality**.  So a deviation in
`native_parts`' generators would not merely change a term the refinement proof
has to relate — it would change a *verdict*.  Every generator therefore
reproduces con-leche's construction order exactly: the same `liftLooseBVars`
amounts and cutoffs at the same points, the same binder data
(`Level.zeronessOf ℓ` on every generated binder, `.never` on the motive's own),
the same append order in every argument spine.  Lean's truncated `Nat`
subtraction is `expr_ops::sub_nat` at every `nF - 1 - i`, using
`(a - b) - c = a - (b + c)`.

One consequence worth recording: **the annotation pass is the identity on the
generated recursor type**, which is why the `isDefEq` against the stream's
annotated recursor takes the syntactic fast path.  `pwWritten` is "not
`.never`", so every binder the generator datums with `zeronessOf ℓ` is *kept*
by `checkConstantVal`'s `annotate`, and the two `.never` binders
(`structMotiveTyI`'s own `(t : T p⃗ ı⃗)`, whose codomain is a `Sort`) are
recomputed to `.never`.  The `check_native_installs_a_nat_like_block` test is
that fact end to end.

**The two higher-order arguments are monomorphised** (task #18's pattern 1):
`structIhApp`, `structRuleBodyR`, `structIhPis`, `structMinorTyR` and
`structRecRhsR` take `teleOf : Nat → List (Expr × BinderMeta)` and
`idxOf : Nat → List Expr`, and *every* con-leche call site passes
`structFieldTeleOf cty nP nF` / `structFieldIdxOf cty nP nF` — the same three
values the caller already holds.  The port passes those three and calls the two
readers by name; a one-method trait would put a dictionary inside the
generators' recursion for no gain.  `checkSumInd`'s `capsOf : InductiveShape →
IndCaps`, by contrast, *is* a one-method trait (`sum_install::CapsOf`, with
`native_install::NativeCapsAt { is_rec }` its one implementation), because it
is not in a recursion and because the parametricity is what the verification
tier uses.

#### `fenv::dup`: four copies of the index, per block

con-leche's index is persistent — `fe.push` and `fe.restrictTo` leave their
argument intact because the runtime shares the `Std.HashMap` field — and task
#14 chose linear threading instead (by value, returned), which is exact and
`O(1)` wherever a caller needs *one* view at a time.  Four sites in these
routes need **two** views at once, and they are the only ones in the
directory:

* `check_native_pass` hands an index to `check_sum_ind` (which pushes the
  former onto it) while `check_native` keeps the pre-block index for the second
  pass and for `check_native_tail`;
* `check_native_rec` builds `feR = fe.push (.recInfo cvRa … [])` — a
  *temporary* view in which the generated rules are scope-checked — while
  `check_native_tail` keeps `fe₂` for the rules and the table;
* `check_ind_recs` holds **three** views: the block-member environment `env₂`
  that every iota check's `env'` lookups go to, the fully provisioned
  `envSelf` that `provisionRecs` built on top of it, and the fold's
  accumulator, which starts as `env₂` and grows.

Each takes `fenv::dup` (task #14's copy: the index is rebuilt with
`mk_fenv_go`, the constants themselves stay shared).  That is `O(|env|)` **two
to four times per inductive block**, not per term — it is the price task #14's
option 3 named, and the `Rc<HashMap>` index it foreclosed removes it without
touching the model, because `abs` reads the index through `find` either way.

#### The `flushC` policy is exact

`Cached/CheckerC.lean`'s inductive stages "mirror their
`Kernel/Checker.lean` counterparts clause by clause; the differences are
exactly: `flushC` at environment transitions, `FEnv.push` maintaining the
index, and *every* environment lookup routed through the index".  The port has
one spelling of the index already (deviation 1), so what `inductives_c.rs`
adds is the **flush policy** — the one thing §3.1 insists must be mirrored,
because a flush changes the memo hit/miss pattern.  Three stages were *split*
in `native_install`/`modeled` so that the flush lands exactly where the cited
`flushC` does, with one body serving both the pure and the cached spelling:

* `check_native_pass` → `check_native_pass_former` + `check_native_pass_ctors`
  (the flush is between `checkSumIndF` and `checkSumCtorsF`);
* `check_native_tail` → `check_native_tail_guards` + `check_native_cons` +
  `check_native_install` (the flush is after `consSumCtorsF`, before
  `checkNativeRecF`);
* `provision_recs` → `provision_recs_step` + the fold (the flush is per
  recursor).

So **no memo policy differs from the executed Lean** in this task, and the
task-#18 note owed to `CoreC.lean`'s interned bodies stays the only open one.

#### Constructs that do not survive transliteration

Beyond the three global ones, and all a-priori except the six in the next
section:

1. **The three `@[csimp]` families of `StructParts.lean` are one Rust function
   each** (task #13's pattern), and so is `NativeInstall.lean`'s fourth
   (`Expr.mentionsFvar`) and `Level.lean`'s fifth
   (`Expr.allLevelParamsDefined`): the port implements the `*Fast` member and
   cites the `*Go` walk, the logical `def` and the `@[csimp]` lemma.  The
   plain `def`s are ported too, unmemoized and uncalled
   (`has_loose_bvar`, `has_loose_bvar_b_spec`, `mentions_const_spec`,
   `mentions_fvar_spec`, `all_level_params_defined_spec`,
   `open_pis_at_fvars_spec`), so the gate stays in step with their source
   (task #11's `beqRecursive` rule) and so the tests can compare the two.
   Each memo is a `&mut HashMap` created in the wrapper, as in task #13; each
   walk's miss branch is a *second* function (`*_node`), because the probe's
   borrow has to die before the descent mutates the map (task #14's rule).
   **`mentionsConstGo` and `allLevelParamsDefinedGo` do not short-circuit** —
   the cited code walks both children even when the first answers, so that the
   memo it hands back holds both answers — and the port keeps that;
   `mentionsFvarGo` and `hasLooseBVarBGo` *do*, and the port keeps that too.
2. **`structProjGuards` is implemented as `structProjGuardsFast`**: the `nF`
   `structUsedLater` answers first, through one shared `hasLooseBVarBGo` memo,
   then the fold — O(nF) telescope walks where the pure definition asks once
   per pair `j < i < nF`.  The `@[csimp]` lemma is what lets the port do that
   and still refine the definition the model's stage tables consume.
3. **`NativeParts` spells Lean's `extends InductiveShape` as a field `shape`.**
   Lean's structure extension gives a `toInductiveShape` projection; the port
   has a field and every reader goes through it (`p.shape.cv_t` for `p.cvT`).
4. **`NativePass (E : Type)` loses its type parameter** — it is `Env` at the
   pure install and `FEnv` at the cached mirror, and deviation 1 leaves one.
5. **The four `Name → Name` arguments are `NameToName` dictionaries**
   (task #9's pattern, task #13's `expr_ops::NameToName`): `BlockRename`
   (`fun n => if blockNames.contains n then n.str "_model" else n`, shared by
   `checkMemberVal` and `checkIndRecs`), `ProjBack`, `ProjFwd`, and
   `domsMatchAux`'s `g` as `DomIdent`/`DomProjFwd`.  All four capture their
   Lean closure's captured values by shared reference, and three of them are
   region-parameterised structs — the second, third and fourth in the crate
   after task #13's `level::SubstZ`, and Aeneas translated all of them without
   complaint.
6. **`sumSplit` is one flat five-component tuple** instead of Lean's nested
   `Option (List _ × ConstantVal × Nat × Nat × List RecRule)`, and it is an
   *index* recursion over the block, which is what lets `nativeShape?` and
   `nativeRecPinOk` spell `sumSplit rest` as `sum_split_from(block, 1, …)`
   with no tail copy.
7. **The two one-element list patterns of `checkModeled`** (`match
   block.filter indInfo, block.filter ctorInfo with | [.indInfo cvT _],
   [.ctorInfo cvC nP nF] =>`) become `single_ind_ctor`, one pass that counts
   both kinds and remembers the first of each: a `Vec` has no such pattern and
   two `filter`s would copy the block twice.
8. **`inst_pins` is two functions.**  con-leche writes one `map` whose
   function either applies the block renaming or does not; a single Rust
   function would take it as `Option<&BlockRename>` and Aeneas rejects a
   nested borrow outright (*"Nested borrows are not supported yet"*), so the
   port has `inst_pins_renamed` and `inst_pins_plain`.
9. **`Array` twins are the same function.**  `checkStructDomsAtFA`,
   `checkStructFieldSortsIFA` and `domsMatchAuxA` exist because positional
   `List` indexing is linear per access; the port has one list type, so each
   is its list twin with a second citation (their `*_eq` lemmas at
   `List.toArray` are the licence).
10. **`List` → `Vec` with `*_from` helpers**, as ever, and every `&&`/`∧`
    cascade is an `if` nest (task #3's pattern 9).  The cited *arm order* is
    preserved everywhere it is load-bearing — `recPositivity`'s
    negative-before-unsupported cascade, `nativeOpenedOk`'s per-kind match,
    `checkIotaThm`'s pin sequence, and `structPartsCore?`'s
    large-before-small eliminator reading.

#### The seven Aeneas errors, and their fixes

Charon succeeded on the first run (2.14 s from a clean build; the `.llbc` is
88 MB).  Aeneas gave **six** errors on the first run and **one** more after the
first round of fixes; all seven are task #14's single shape — *a borrow taken
from a shared structure, consumed into a scalar or a monadic value, and then
joined with a branch that re-borrows or mutates the same structure* — and all
seven fixes are the rule task #14 wrote down: **never hold a container's
borrow across a branch that touches the container; factor the test.**

| where | Aeneas said | the factored test |
|---|---|---|
| `native_parts::native_shape` | *Could not match the contexts* | `native_shape_names_ok` (the three reserved-name exclusions and the constructors' guard) |
| `native_parts::native_shape` (round 2) | *Could not match the contexts* | `struct_parts::level_is_prop` (`Level.isEquiv s .zero == some true`), now the one spelling for all three recognisers |
| `struct_parts::struct_parts_core` | *Internal error, please file an issue* | `struct_parts_small_ok` (the small-eliminator branch's guard, `struct_parts_large`'s twin) |
| `native_install::check_native_tail_guards` | *Unreachable* | `elim_restriction_violated` (official's `elim_only_at_universe_zero`) |
| `native_install::check_native_rec` | *Could not match the contexts* | `term_scoped` (`allLevelParamsDefined && resolve && looseBVarsBounded 0 && !hasFvar`), now shared with `check_native_rules` |
| `modeled::check_iota_rule_fire` | *Internal error, please file an issue* | task #18's rule: the two firing branches **tail-call** `iota_rule_stored` instead of joining on a `CheckM RecRuleFire` |
| `modeled::inst_pins` | *Nested borrows are not supported yet* | deviation 8 above |

Every one of the fixes is an improvement on its own terms — each factored test
is a named thing the Lean already names — so nothing was contorted to please
the tool.  After them: **zero errors, zero warnings.**

#### Numbers

| | |
|---|---|
| Lean ported: 9 files, 2 890 lines; plus `Basis/Builder.lean` 125, `NatOpPinSet.lean` 51, `Level.lean:251-412` | |
| the nine modules + 3 dependency modules, extracted part (raw / code) | **4 854 / 3 213** |
| `#[cfg(test)]` part (12 tests in 4 modules) | 673 / 545 |
| `expr_ops.rs` (the `allLevelParamsDefined` family + `bool_and`) | 2 485 → **2 661** |
| generated `Types.lean` | 583 → **621** (+38: `OrElseStep`, `NatOpPinSet`, `ModelRename`) |
| generated `Funs.lean` | 21 205 → **28 743** (+7 538: `checker` 2 274, `decl_check` 1 305, `checker_base` 1 292, `std_axioms` 855, `trust_axioms` 495, `checker_split` 390, `basis_builder` 167, `type_checker` 85, `trust_pins` 34, `basis_pins` 23, `checker_c` 15, `nat_op_pins` 7, `expr_ops` +596) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 — **unchanged** |
| `charon cargo --preset=aeneas` wall | **~2 s** (the `.llbc` is 71 MB, was 33 MB) |
| `aeneas -backend lean -split-files -loops-to-rec` | **16.4 s** (was 13.98 s) |
| `partial_fixpoint` (whole crate / this task) | 226 → **252** (+26: `checker` 9, `checker_base` 7, `decl_check` 5, `std_axioms` 2, `expr_ops` +3) |
| `mutual` blocks in `Funs.lean` / `Types.lean` | **3 / 3 — unchanged**: nothing new joins the core knot, because the declaration checker calls *into* it and nothing in it calls back |
| `cd proof && lake build` after the regeneration (`gates.sh`, 2 040 jobs) | **64 s** |
| external holes | **exactly the four `Rc` axioms and the `Rc` type**; `MaybeUninit` briefly made a fifth (above) |

`cargo build`/`cargo test` warning-free, **117/117** green (105 from tasks
#6-#18 + 12 new); `scripts/lint-rust-style.sh crates/con-ron-core/src` clean;
`scripts/provenance.py check` green — 1 066 items, 1 001 citations, all
current at pin 3e004805; `scripts/gates.sh` all six OK.

#### Tests

Twelve, in four modules, all environments hand-built from axioms and
`Sort`/Π/λ terms as `core_k`'s are.

`checker_base` (4): **the duplicate-name guard** — `checkConstantVal` on a
stored name is `.invalid` (not a decline), the same header under a fresh name
checks with its type annotated and its sort run, a reserved basis name is
`.invalid`, and a type mentioning an unstored constant throws.  The equality
head readers (`isEqHead` accepts `Eq` at *one* level and nothing else,
`eqHeadLevel` reads it and answers `.zero` off shape) and `piResultSort`.
`openPisAtFvars` and its one-pass twin opening the same two-binder telescope
to the same fvars, both refusing a telescope that is too short, and both the
identity at `n = 0`.  `checkDefEqList` throwing on a length difference, and
`domsMatchAux` at two offsets, out of range, and at zero positions.

`checker` (4): **a `defn` whose value has the wrong type is rejected** —
`d : A := Sort 1` passes every syntactic guard and then `Sort 2 ≢ A` makes it
`.invalid`, with `d : A := a` as the positive control (installed as a
`defnInfo`, visibility bound advanced by exactly one) and a duplicate header
rejected before the value is looked at.  **The axiom pin** — a `propext`
(resp. `Classical.choice`) with a non-pinned type is a positive decline at the
pinned-name branch, never an install; a non-standard axiom declines;
`sorryAx` is *tolerated*, i.e. checked and **not** stored, with the
environment coming back unchanged; and the pin comparison is asserted directly
(reflexive, false on a wrong type, blind to the binder datum).  The pinned
certificate statements — three for `Nat.div`/`Nat.mod` (the recursive step
under two `Nat.ble` guards, two base cases) and two for each of the six
others, the `div`/`mod` base values, the open form over `fvar 0`/`fvar 1`, and
`divModCertApplied` at one and two hypotheses.  The pin loop declining on the
empty variant table, and `checkDeclsPure` on the empty stream.

`std_axioms` (2): the lockstep comparison agreeing with the specification on
all 100 pairs the ten pins form, reflexive, blind to a rewritten `pw` and not
blind to anything else; the families' sizes and the guards' arity tests (a
stored `Iff.intro` at the wrong arity fails even with the pinned type).

`checker_c` (1): **`orElse`'s three outcomes** — a matched attempt is the
whole, a `false` continues with no diagnosis, and a *thrown error* continues
carrying the error instead of propagating, for an `internal` error as much as
for a `notImplemented` one.

#### The one deviation that is owed upstream

`sharedOpsC.orElse`'s error arm is `k (some e) s` — the **pre-attempt** state:
"the memo entries the failed attempt wrote are discarded with it".  The port's
state is a `&mut CState`, so those writes are in place when `or_else_step`
sees the `Err` and the continuation runs on the post-attempt state.  Every
entry is a correct answer, so no verdict changes, but it is a *hit where the
Lean misses*, which §3.1 asks to be flagged rather than taken silently.
Reconciling it is either a `CState` snapshot in `cached::state_c` or an
upstream note, and it must happen before any `check_decl_refines` is stated
against `checkDeclsPure`.  Flagged in `checker_c.rs`'s module doc.

#### Deliberately not ported

* `structure CheckerOps` (`CheckerBase.lean:30-53`) and `pureFns`
  (`TypeChecker.lean:24`) — cited, not ported: §3.1 ties the knot with plain
  functions, and the port has one knot.
* **`CheckerGated.lean` (42 lines) is proof-tier only** — the task asked for a
  verdict, and this is it.  `fueledOpsGated`/`pureOpsGated` are `fueledOps`'
  twin over the *gated* knot (`Kernel/CoreGated.lean`); the file's own header
  says "nothing here is reachable from `Main.lean`'s import closure: the
  executable is byte-identical to master", and the declaration checker it
  instantiates is not duplicated (that is the whole point of `CheckerOps`).
  Porting it would mean porting `CoreGated.lean` — a second copy of the whole
  core — for a lane the binary never runs.  0/2 covered, on purpose.
* `divModAttemptReason` (`Checker.lean:333`), `ValueKind.word`
  (`CheckerSplit.lean:45`) — message rendering (§3.1).
* `CRFMemoInv` (`DeclCheck.lean:71`), `LPMemoInv` (`Level.lean:280`) and their
  `empty`/`insert` lemmas — `Prop`s; Charon erases them, and they are exactly
  the invariants the Rust-side refinement proof will restate about
  `crate::ron::hashmap` memos (task #13's ruling).
* `trustPinEnv` (`TrustAxioms.lean:133`) — the environment `#annotate_pins`
  computes over; part of the generator, not of the checker.
* **Eight `DeclCheck.lean` mirrors that stand on `Kernel/Inductives/*`**:
  `ctorResidualOkF` (`:419`, needs `structFam`), `checkIotaThmF` (`:508`),
  `nestedRuleShapeF` (`:576`), `checkIotaThmNF` (`:602`), `checkIotaRuleF`
  (`:688`), `checkIotaRulesF` (`:719`), `checkProjTyF` (`:749`),
  `checkProjIotaF` (`:798`) — they need `checkIotaSidesTy`,
  `projFwd`/`projBack` or `structFam`, and two of them need the **two** index
  views the Lean passes (`fe'` and `feSelf`), which the port spells as one
  index at two visibility bounds; the function that threads those bounds is
  their caller's.  Recorded in `decl_check.rs`'s module doc, with the table of
  what *did* collapse.
* **Sixteen of `CheckerC.lean`'s seventeen declarations** — the
  per-declaration phase drivers (`checkIndMemberS`, `provisionRecsS`,
  `checkIndRecsS`, `checkProjFnS`, `installProjFnStepS`, `checkNativePassS`,
  `checkNativeTailS`, `checkNativeS`, `checkIndDeclSF`) and the four memoised
  direct-install walkers (`instPisAtLiftC`, `structProjBodiesGoC`,
  `structProjBodiesC`, `structWalkersC`), all on the same family; listed in
  `checker_c.rs` so the next porter does not re-derive them.  `opE`/`opB`/`opS`
  are the collapse, above.
| Lean ported: 64 cited blocks of `Cached/CoreC.lean` | 1 655 raw / **1 411 code** |
| plus 16 blocks of `Cached/StateC.lean` | 151 raw / **140 code** |
| `src/cached/core_c.rs`, extracted part (raw / code) | 325 → **5 176 / 3 965** (2.8× the Lean code) |
| `src/cached/core_c.rs`, `#[cfg(test)]` part (8 tests) | 0 → **393 / 296** |
| `src/cached/state_c.rs`, extracted / tests | 574 → **1 107 / 611** · 225 → 231 |
| `src/kernel/core_k.rs`, extracted / tests | 5 883 → **2 714 / 1 886** · 494 → 498 |
| generated `Types.lean` | 583 → **583** — no type added or removed; the 83 changed lines are Aeneas reordering the declarations because the module dependency graph moved (the two new `abbrev`s, `InferLamEntry` and `AnnotBinderEntry`, are erased) |
| generated `Funs.lean` | 21 205 → **24 896** (+3 691) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 — **unchanged** |
| `charon cargo --preset=aeneas` wall | **1.32 s** (the `.llbc` is 42 MB) |
| `aeneas -backend lean -split-files -loops-to-rec` | **16.8 s** (16.2 s self-reported) |
| `partial_fixpoint` (whole crate) | 226 → **251** (+25) |
| `mutual` blocks in `Funs.lean` | 3 → **4**: task #3's 8-function `leq_core` knot (328 lines), **the core knot — 84 functions, 6 324 lines**, the annotation telescope block (11 functions, 493 lines) and `consts_resolve_fc_go` (2 functions, 85 lines) |
| `mutual` blocks in `Types.lean` | 3 — unchanged |
| `lake build` of `ConRon.Generated.Funs` (from scratch) | **61 s** (38 s at task #18) |
| external holes | **exactly the four `Rc` axioms of §3.2** and the `Rc` type |

The core knot's SCC grew from 75 to **84** functions while `Funs.lean` grew
only 18 %: the cached bodies are longer than the pure ones but there is now
only *one* copy of them.  `annotate`'s block grew 5 → 11 functions — the four
annotation telescope loops joined it — and it is still a separate SCC, which
remains the correct decomposition (nothing in the reduction/inference/equality
cycle calls `annotate`).

`cargo build`/`cargo test` warning-free, **113/113** green (105 from tasks
#6-#18 + 8 new); `scripts/lint-rust-style.sh crates/con-ron-core/src` clean;
`scripts/provenance.py check` green — 903 items, 892 citations, all current at
pin 3e004805; `scripts/gates.sh` all six OK.

#### Tests

Eight new (`#[cfg(test)]` in `core_c.rs`, invisible to Charon), on the same
hand-built axiom environment `core_k`'s eight use (`A : Sort 1`, `a : A`,
`f : ∀ (_ : A), A`).  **One per new map, each checking a write *and* a hit**:
`lsimpC`/`eqvC` (the reconciliation's headline, above), `instC` written by a β
step and hit by the same `(body, args, cursor)` triple, `constTyAt` written by
`infer` of a constant and hit by a second `constTyAtM` (with the unknown-name
`.internal` throw writing nothing), and `ienv` with its three tag outcomes.
Plus the `instC` **cap reset** through `inst_list_m_reset_at` at a small bound
(under it the memo survives, at it the map is dropped whole, and the
production bound is still `instCCapC`); the five expression memos still
hitting and `inferIOC` still kept apart from `inferC`; the fuel-zero throws of
all six wrappers with nothing cached on the way; and the two new algorithms —
the head-normalization loop reducing a two-redex chain in one knot level, and
the binder-telescope loops peeling and rebuilding `λ (x : A). λ (y : A). y`
into `∀ (_ : A), ∀ (_ : A), A`.

The eight `core_k` tests of task #18 are unchanged and still green, which is
the strongest single signal here: they drive `whnf`, `whnfCore`, `infer`,
`defeq` and `annotate` end to end through the wrappers, and the wrappers now
call entirely different bodies.  One line of them moved —
`core_k::unfold_definition` is `core_c::unfold_definition_i`.
| Lean ported: all ten `Inductives/*.lean` | **3 983** lines, **152** declarations |
| plus the inductive stages of `Cached/CheckerC.lean` | 9 blocks |
| plus what `CheckerBase.lean`/`DeclCheck.lean`/`Level.lean` owe (`checker_local`) | 30 blocks |
| Rust, extracted part (raw / code) | **10 272 / 8 033** (2.0× the Lean's 3 983) |
| — `native_parts` / `modeled` / `native_install` | 1 667 / 2 770 / 1 409 raw |
| — `struct_parts` / `checker_local` / `sum_install` | 1 273 / 1 340 / 939 raw |
| — `inductives_c` / `struct_install` / `sum_parts` / `mod` | 419 / 207 / 174 / 74 raw |
| Rust, `#[cfg(test)]` part (16 tests) | 892 raw |
| Rust items Charon sees | **319** (306 `fn`, 6 `struct`, 2 `enum`, 3 `trait`, 2 `impl`) |
| generated `Types.lean` | 583 → **698** (+115: `InductiveShape`, `StructParts`, `NativeParts`, `NativePass`, `RecFieldKind` and the five dictionaries) |
| generated `Funs.lean` | 21 213 → **34 601** (+13 388) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 — **unchanged**: exactly the four `Rc` axioms and the `Rc` type (§3.2's standing gate) |
| `charon cargo --preset=aeneas` wall (clean build) | **2.14 s** (the `.llbc` is 88 MB) |
| `aeneas -backend lean -split-files -loops-to-rec` | **22.95 s** wall (22.18 s self-reported) |
| `partial_fixpoint` (whole crate / this task) | 226 → **336** (+110) |
| `mutual` blocks in `Funs.lean` | 3 → **7**: the four new ones are the four memoized walks' `*_go`/`*_node` pairs (2 functions each, 130-191 lines).  **The install stages are in none of them** — the routes are a chain, not a cycle, and Aeneas's SCC decomposition says so |
| `mutual` blocks in `Types.lean` | 3 — unchanged |
| `lake build` of `ConRon.Generated.Funs` | **61 s** (from scratch; 38 s at task #18) |
| `cargo test` | 105 → **121** green, warning-free |
| `scripts/provenance.py check` | green — **1 161** items, **1 126** citations, all current at pin 3e004805 |

The 2.0× Rust→Lean code ratio is the best in the port so far (task #18's
`core_k` was 3.3×, task #13's `expr_ops` 3.7×): these files are mostly
*syntactic* — `if` nests over `Expr` shapes and `Vec` index recursions — so
the two things that inflated the earlier modules, `const […]: [u32; N]`
messages and explicit `match` on every `Result`, are diluted by real content.
The generated Lean is 1.3× the Rust code.

#### Tests

Sixteen (`#[cfg(test)]`, invisible to Charon), all environments hand-built.

`native_install` (6).  **The `Nat`-like block, end to end**: `N : Sort 1`,
`Nz : N`, `Ns : N → N` and the *generated* `N.rec` at a fresh elimination
parameter — which is what an export carries, since the elaborator generated it
— installs, with the former, both constructors and the ruled recursor stored,
the rules `plain` and `paramsBlind`, and no projection table (two constructors
is not structure-like).  That one test exercises the whole route: the
recogniser, `nativeCounts?`, the former's telescope, the constructors with
official's positivity walk as a normalisation, the classification, the
recursor generated and `isDefEq`'d against the stream's, `nativeRulesOk`'s
structural comparison of the rule bodies, and `nativeRulePrefixOk`'s
comparison of the rule's λ prefix against the stream's own recursor type.
**The classification** reads `[[], [.recursive]]` off that block and
`nativeIsRec` reads `true` off that.  **The `Eq`-like indexed family**:
`Q : A → Prop` with `Qmk : ∀ (a : A), Q a` installs — one constructor, one
index, a `Prop` result and a large eliminator, i.e. the subsingleton case where
a non-propositional field is admitted *exactly because it is one of the
residual's index expressions* (`Eq`'s rule, `checkStructFieldSortsI`) — and
earns no capability and no table, because an index is not structure-like.
**A non-positive occurrence is rejected, not declined**: `W` with a
constructor field `(W → W) → W` comes out `.invalid`, from `normPosDom`,
before the recursor stage would look at the stub recursor the block carries —
which is con-leche task #220's point, that the type and the constructors are
checked first.  **A mutual block is not this route's**: two type formers, and
separately two recursors, are refused by `sumSplit` outright (and so is a
block not headed by a type former), which is what routes them to the modeled
path.  **`mentionsFvar`** agrees with its `fvarLeaves` specification through
annotations, binders and a `.proj`.

`struct_parts` (3).  The three de Bruijn spines at the indices the cited
definitions name (`structPsAt`, the field spine, `structProjPs`), with
`structCtorSpine = structCtorSpineAt` at `o = 1` and `structElimLevel` at both
eliminators.  The two memoized walks against their specifications on a term
with sharing, binders and a `.proj`, and `replacePisPw`/`pisToLamsPw` keeping
the domain and resetting the datum.  **The projection table's bodies and
guards** for `C : ∀ (p : A) (f0 : p) (f1 : f0), T p`: the bodies are the field
domains with the earlier fields replaced by the subject's projections
(`bodies[1] = .proj T 0 (bvar 0)`), field `0` *is* used later and field `1` is
not, and field `1`'s guard is its own sort joined with field `0`'s.

`modeled` (3).  The public↔model renaming is a bijection on the block's names
— which is what `checkProjTy`'s roundtrip pin turns into a check — and fixes
everything else, including a projection index past `nF`.  Official's
structure-likeness gate (`ctorTargetsFam`) accepts `T p⃗` and rejects `T p⃗ i⃗`
(the `SigmaHom` ruling).  The four model-artifact names
(`R._model.iota_12`, `R._model.proj_0.iota`, `R._model.eta`,
`R._model.unitlike`) and the block filters `checkIndDeclSF` reads, including
`single_ind_ctor` falling to the general arm at a second constructor.

`checker_local` (4).  **`eqA` really is `eqRaw`** (above): the annotation pass
is the identity on the pin, and `eq_basis_pinned` accepts the pin, rejects the
same constant without its K capability, and rejects an empty environment.
`openPisAtFvars` opens a two-binder telescope at `0`/`1` with each fvar
carrying its instantiated domain, declines a short one, and agrees with the
specification walk.  `allLevelParamsDefined` reads the *binder data* too, as
the cited definition does.

#### Deliberately not ported

`Inductives/*` goes 0/152 → **147/152**.  The five uncovered are:

* `MentionsFvarMemoInv` (`NativeInstall.lean:195`), `LooseBVarMemoInv`
  (`StructParts.lean:416`) and `MentionsMemoInv` (`StructParts.lean:796`) —
  the three memos' `Prop`-valued invariants, which are proof-only: they are
  the *specification* the `@[csimp]` lemma is proved against, and the port
  implements the `*Fast` member the lemma licenses;
* `StructParts.lean:23`, which the coverage locator reads as a declaration
  named `declaration,` — a line of the module docstring, not a declaration;
* and that is all: every executable `def` of all ten files is ported,
  including the ones nothing on the shipped path calls (`Expr.hasLooseBVar`,
  `structParts`/`structShape`/`structPartsCore?` — whose simple-structure
  route con-leche deleted at its task #210 Part C and whose one reader is the
  out-of-core in-process modeller — `structProjResidP`, `sumSplit`'s pure
  form, `structRuleBody`, `mentionsConst`'s and `mentionsFvar`'s plain
  walks), so that the gate stays in step with its source and the next task
  finds them waiting.

The 20 `@[simp]` projection equations of `InductiveShape.withSort`,
`NativeParts.complete` and `NativeParts.withKinds`, `withSort_self`,
`nativeCaps_sortZ`, `indBlockCaps_sortZ`, `structUsedLaterGo_spec`,
`structUsedLaterList_spec`, `foldlCongrMem`, the six `Expr.mentionsFvar_*`
congruences and the `*Go_spec`/`*_eq_*Fast` theorems are cited on the items
they govern rather than ported: they are the spec this port will be proved
against.

#### Coverage

`scripts/provenance.py coverage | tail -3`, con-leche 3e004805: **TOTAL
543/1018 covered (53.3 %), 475 uncovered** — up from **382/1018 (37.5 %)** at
this branch's merge base (+161).  Per file: **`StdAxioms.lean` 25/25**,
**`TrustPins.lean` 2/2**, **`NatOpPinSet.lean` 1/1**, **`BasisA.lean` 1/1**,
`TrustAxioms.lean` **26/27**, `Level.lean` 21/25 → **24/25**,
`Basis/Builder.lean` **20/21**, `Checker.lean` **20/21**, `CheckerBase.lean`
**19/20**, `TypeChecker.lean` **7/8**, `CheckerSplit.lean` 2/6 → **5/6**,
`DeclCheck.lean` **28/40**, `CheckerC.lean` **1/17**, `CheckerGated.lean`
0/2.  So the ledger agrees with the prose in every file.

**Note for task #22.**  This task needs *no* pin table for the standard and
compiler-trust axioms — the erase-`pw` argument above makes the raw pins exact
— and exactly three stubs from it: `eqA` and `natA` as predicates, and
`BasisKind.declsA`, all in `kernel/basis_pins.rs`, which should be folded into
`kernel/basis_tables.rs` and deleted.  `nat_op_pin_sets()` lives in
`kernel/nat_op_pins.rs` beside the `NatOpPinSet` record it returns.

**Note for task #25.**  `checkDecl`'s `.indDecl` arm and the eight
`DeclCheck.lean` mirrors above are the seam.  Everything the inductive
installs call *below* `CheckerOps` is already here: `checkConstantVal`,
`checkMemberVal`, `checkProjRule`, `checkProjLookups`, `checkProjShape`,
`checkEtaThm`, `checkUnitThm`, `indBlockCaps`, `openPisAtFvars(F)`,
`domsMatchAux`, `checkTypedList`, `checkAnnotList`, `checkDefEqList`,
`unwrapOr`, `isEqHead`, `eqHeadLevel`, `piResultSort`, `findCV`.
479/1018 covered (47.1 %), 539 uncovered** — up from **382/1018 (37.5 %)**.
Per file: **`CoreC.lean` 3/80 → 73/80**, **`StateC.lean` 14/38 → 38/38**,
**`Core.lean` 129/130 → 130/130**, `ExprOpsC.lean` 0/37 → 2/37, everything
else unchanged.

`CoreC.lean`'s seven uncovered declarations are exactly the named concrete
cores (`whnfCoreBodyPC`, `inferBodyPC`, `defeqBodyPC`, `annotateBodyPC`,
`whnfCoreBodyTC`, `inferBodyTC`, `defeqBodyTC`) — mode instantiations of
bodies that are ported, with a runtime mode parameter, as §5 above explains.
Everything else executable in the file is ported, including `certAtI`/
`certUnlessI` (spelled out at their nine sites, cited there) and the four
`@[simp]` theorems about them, which are spec.

**Note for the next task.**  The knot is now complete and faithful, so
`whnf_refines` can be stated against `coreKnotI mode (abs fe) fuel` with no
memo-policy caveat.  The two `Level.isEquiv` sites that stay off `eqvC` are
the only thing a memo-policy lemma has to special-case, and both are the
Lean's own.  `Cached/ExprOpsC.lean` (37 declarations) is the next
`Cached/` file with real content; its `Kernel` original is ported, so the work
there is the identification lemmas, not a port.

### Task #22 — Basis tables generated; the pin-set strategy (2026-09-12, Opus under Fable)

P1.5's design half.  con-leche builds two families of tables while it
*elaborates*, and the Rust core can build neither: the **annotated basis
blocks** (`BasisKind.declsA`, `ConLeche/Kernel/BasisA.lean:50-57`, produced by
`#annotate_basis` running the checker's own annotation pass over the raw pins
in `Kernel/Basis/*.lean`) and the **Nat-op pin variants** (`natOpPinSets`,
`Kernel/NatOpPins.lean:61`, spliced from `pins/<toolchain>.json` by
`#load_natop_pins`), plus the small hand-pinned `divModCertStmts`
(`Kernel/Checker.lean:155`).  This task built the generator, landed the basis
half, measured both candidate encodings, and settled the pins.

**What landed.**

| file | what |
|---|---|
| `proof/ConRon/Gen/Emit.lean` | the emitter: a con-leche value → a Rust function body, interning `Name`/`Level`/`PropWhen`/`Expr` by value, one `let` per distinct node in dependency order (the task-#10 dump writer's worklist order), every node a call to the port's own smart constructor and every use a `dup`.  Handles every `Expr` constructor, every `ConstantInfo` constructor and unbounded `Nat` literals (`nat::from_u64`, or `nat::norm` of little-endian limbs) — so it already covers the pins |
| `proof/ConRon/Gen/Main.lean` + `[[lean_exe]] con-ron-gen-tables` | `lake exe con-ron-gen-tables` writes the file; `--stdout`, `--count` (the DAG census), `--pins <i> <out>` (the sizing spike, `_tmp/` only) |
| `crates/con-ron-core/src/kernel/basis_tables.rs` | **generated**, 622 lines: `basis_decls_{eq,nat,punit,empty,false,quot}` and the `basis_decls_a` dispatcher |
| `proof/ConRon/Refine/BasisTables.lean` | the abs tier this needs (`absExpr` and the `env` records — *temporary*, namespace `T22`, to be deleted when task #20's land in `Abs.lean`), `absBasisDecls`, the dispatcher lemmas, and a precise account of what the equality lemma is blocked on |
| `scripts/provenance.py` | module-level *citations* (§3.7), and the ledger no longer reads prose in `/-!` docstrings as declarations |

**Encoding A (generated Rust source) — the basis, measured.**  The DAG census
(`lake exe con-ron-gen-tables --count`) is what the sizing rests on: a node is
a `let`.

| block | names | levels | propwhens | exprs | **total** | Rust lines |
|---|---|---|---|---|---|---|
| `Eq` (3 decls) | 6 | 3 | 3 | 42 | **54** | 96 |
| `Nat` (4) | 6 | 3 | 3 | 36 | **48** | 95 |
| `PUnit` (3) | 6 | 2 | 3 | 14 | **25** | 71 |
| `Empty` (2) | 4 | 3 | 3 | 9 | **19** | 44 |
| `False` (2) | 4 | 2 | 3 | 9 | **18** | 43 |
| `Quot` (5) | 9 | 3 | 4 | 82 | **98** | 169 |
| all six, interned together | 23 | 5 | 5 | 159 | **192** | — |

Per-block interning (each function independent) costs 262 `let`s against 192
shared; the six functions are kept separate so that nothing outside the
dispatcher can be affected by another block.  Through the pipeline:

| stage | before | after | delta |
|---|---|---|---|
| `cargo build` | — | — | no measurable change |
| `scripts/extract.sh` (Charon + Aeneas, whole crate) | ≈13 s | **14.1 s** (Aeneas 12.7 s) | +1 s |
| `ConRon/Generated/Funs.lean` | 11 516 lines | **12 416** | +900 |
| Lean elaboration of `Funs.lean` | 11.32 s | **11.63 s** | **+0.31 s** (≈0.35 ms per generated line, in line with §4's 1 ms/line) |

So the generated Lean model is a clean `do` chain of constructor calls, exactly
as designed, and it is free.  The Rust side satisfies `lint-rust-style.sh` with
no exemption: `Vec::new` + `push` (no `vec!`, which Charon does not see
through), no loops, no closures, no `?`.

**The equality proof: `step`, and the two settings that were switching it
off.**  `absBasisDecls k = ok (ConLeche.BasisKind.declsA k)` cannot be closed
by *evaluation* in this Aeneas version: `Result α` is `ITree RustEffect α`
(`Aeneas/Std/Primitives.lean:81`), its `bind` is `ITree.bind`, a
`partial_fixpoint` over a CCPO (`Aeneas/Data/Coinductive/ITree.lean:160`),
`ITree.cases` is a tactic-built proof term and `alloc.vec.Vec.push` is
`@[irreducible]`.  Measured: `rfl` fails in 1.3 s ("not definitionally
equal"), on the `Result.match` form too; `decide` has no instance (`Result`
has no `DecidableEq`); and full `simp` with the call graph unfolded diverges
on the *two-declaration* `False` block (looping-`simp` warnings on the index
recursions, then a `whnf` timeout inside `prop_when.if_all_zero`) at 2 000 000
heartbeats and 20 000 000 simp steps.  `bind (ok x) f = f x` is a `simp`
lemma, never a reduction.

The tool for this is Aeneas's `step`, and **`step` did not work anywhere in
`proof/`** — it reported "could not find a local assumption or a theorem to
apply" even on a verbatim copy of Aeneas's own `Step/Tests` examples, which
pass inside the Aeneas package.  The cause: task #2's patch gives the
*`aeneas` package* two Lean options that `proof` does not set,

```
leanOptions := #[⟨`backward.isDefEq.respectTransparency, false⟩,
                 ⟨`backward.do.legacy, true⟩]
```

and without them a `⦃ ⦄` goal does not unify with a `@[step]` lemma (the
symptom is a `Post α` vs `α → Prop` mismatch under `implicit` transparency).
Setting the two per file makes `step` work immediately.  That is why every
`ConRon/Refine/*` proof written before this task is a hand-written
`simp`/`obtain` script and why none of them contains a `⦃ ⦄`: the project's
main proof tactic had been silently unavailable.  **Recommendation: hoist the
two options into `proof/lakefile.toml`'s package section**; this task sets
them per file to avoid changing elaboration under the other in-flight tasks.

With `step` working, the six lemmas are **proved**, `sorry`-free, at
`propext + Classical.choice + Quot.sound` and nothing else:

| | |
|---|---|
| `basis_decls_{eq,nat,punit,empty,false,quot}_refines` | `basis_decls_a k ⦃ v => absConstantInfos v = declsA (absBasisKind k) ⦄` |
| `basis_decls_a_refines` | the six, by cases on the kind |
| `absBasisDecls_eq` | the `Result`-level equation, via `WP.spec_imp_exists` |
| `proof/ConRon/Refine/BasisTables.lean` | **631 lines**, elaborates in **66 s** |

The shape is: a *specification* tier for the port's smart constructors (the
project's first `⦃ ⦄` lemmas — 40 of them, ~330 lines), then one `step` per
interned node driven by `step*`, then one `simp_all` that evaluates `abs` on
the reconstructed nodes and compares.  The tier is where the work is, and it
divides into three kinds:

* **Node constructors** get the shape with the hash *existentially
  quantified* (`name.mk_str pre s ⦃ n => ∃ h, n = .mk (.mk h (.Str pre s)) ⦄`),
  so no proof ever names a hash formula — `abs` forgets the word anyway.  Each
  is one line: `unfold f; step*`.
* **Hash and index helpers** get `⦃ _ => True ⦄`: totality and no more.  The
  six index recursions (`name.str_hash_from`, `level.levels_hash_from`,
  `level.levels_have_param_from`, `prop_when.names_hash_from`, and
  `level.level_has_param`) are `partial_fixpoint`s with no induction
  principle, so each is a `Nat` induction on `length - i` (or `Level.ind'`)
  using the function's own `.eq_def` — ~15 lines each, and `step*` closes both
  branches once the IH is in context.
* **`prop_when.if_all_zero`** is the only interesting one.  It decides the
  `0`/`1`/`2`-element cases inline and reaches `canon`/`merge`/`name_cmp`
  only at three or more, so the two shapes a basis block uses need no
  canonicalisation lemma and no `NameWF` — the length hypothesis picks the
  branch.  That is also why the generator was changed to stop *interning*
  `PropWhen`s: a shared datum would be handed out with `prop_when::dup`,
  whose `Many` case is the one that would drag the whole comparison
  machinery in.  Fresh producer calls cost 7 `let`s across the six blocks
  (622 → 796 generated lines) and buy the whole proof.

The residual side goals are only the `Vec::push` bounds — `3 < Usize.max`,
which needs `Usize.bounds_eq` because `Usize.max` is platform-dependent and
`scalar_tac` does not case on it — and the one-element list equations.  The
closing tactic is packaged as a `basis_block` macro, so each of the six
theorems is three lines.

**Encoding A at pin scale — it does not reach Aeneas.**  The v4.33.0 variant's
DAG:

| pin set | names | levels | propwhens | exprs | **total** |
|---|---|---|---|---|---|
| `leanprover/lean4:v4.33.0` | 188 | 3 | 1 | 19 991 | **20 183** |
| `leanprover/lean4:v4.34.0-rc2` | 188 | 3 | 1 | 19 991 | **20 183** |
| `leanprover/lean4-nightly:nightly-2026-09-10` | 193 | 3 | 1 | 21 506 | **21 703** |
| all three interned together | 200 | 3 | 1 | 26 512 | **26 716** |
| of which the eight *pins* alone (v4.33.0) | 83 | 2 | 1 | 477 | **563** |

The certificate blobs are 97 % of it, and as a *tree* the v4.33.0 variant is
5.1 M nodes (app 2 413 383, const 1 928 145, bvar 222 532, lit.nat 401 258,
lam 124 666, forallE 17 377, sort 3 517, proj 471) — a 250× DAG compression,
which is exactly why the `let`-sharing encoding is the only one worth trying.
The two releases share almost everything; the nightly adds 1 515 nodes.  What
happened when we tried it (`_tmp/t22`, one `fn nat_op_pins_v0() -> Vec<Expr>`
holding the eight pins and all eighteen blobs):

| stage | result |
|---|---|
| generation | **2.7 s**, 21 920 lines, 1.48 MB |
| `rustc` (default 8 MB stack) | **SIGSEGV** — stack overflow in rustc |
| `rustc` with `RUST_MIN_STACK=256M` | compiles, **73 s** |
| `charon cargo --preset=aeneas`, `RUST_MIN_STACK` 128 MB and 512 MB | **SIGKILL (OOM), ~30 s**, both times, on a 125 GB / 96-core machine |
| Aeneas, Lean | never reached |

`divModCertStmts`, by contrast, is **149 nodes / 264 Rust lines** for all eight
operations — encoding A, trivially, and it must be A (see below).

**Encoding B (runtime-loaded data) — and why the honest answer is not "a
hypothesis we cannot discharge".**  As the task framed it, B embeds the tables
as a `con-ron-decls/1`-style dump and takes `abs tables = ConLeche.natOpPinSets`
as a hypothesis.  That hypothesis is **not** dischargeable in Lean without
`native_decide`: it would need the task-#19 reader's *Lean* twin evaluated on a
~700 KB string, and the obstruction above is the same one — a `decide` over a
`Result`-monadic reader does not reduce at all, let alone at that size.  So if
the hypothesis were needed, B would be a trust gap and A the only sound option.

**It is not needed.**  con-leche's own `NatOpPinSet` docstring
(`Kernel/NatOpPinSet.lean:26-49`) settles it: *"The record is data the checker
reads; the model never inspects a pin or a proof blob (the certificate
statements it consumes are hand-pinned in `Checker.lean` and shared by every
variant)."*  `checkDivModPinAt` (`Kernel/Checker.lean:321`) annotates the
variant's pin, compares it to **the stream's own stored value** by `isDefEq`,
and only then kernel-checks that variant's proof terms against
`divModCertStmts`; `checkDivModPinLoop` tries the variants in order and the
stream **declines** when none matches.  A pin list is a *hint list*: a wrong,
stale or corrupted one can cost a decline and nothing else.  The basis blocks
are the opposite — `installBasisDecl` *stores* them and the model proofs read
them — which is why they must be pinned in the verified core and proved.

**Recommendation.**

1. **Basis blocks → encoding A.**  Landed **and proved**: 192 nodes, 796
   generated Rust lines, +0.3 s of extracted-Lean elaboration, and a 631-line
   proof that elaborates in 66 s.
2. **`divModCertStmts` → encoding A.**  149 nodes; it is the trusted half of
   the pin gate and lives in `Checker.lean`, so it belongs to that module's
   port rather than to a table file.
3. **`natOpPinSets` → encoding B**, as data in the unverified driver
   (`crates/con-ron-dump`'s reader, `include_str!`), with **no equality
   hypothesis at all**.  What this needs is one con-leche-side change to ask
   for: `checkDivModPin` reads the *global* `natOpPinSets`, so today the
   refinement theorem cannot be stated about the Rust core's own list.  Make
   the pin list a parameter of `checkDecls` (or state the lemma that the
   accepted set does not depend on it beyond the checks `checkDivModPinAt`
   already performs) and the Rust side may carry any list it likes, including
   one read at startup.  This is the smallest change that keeps the trusted
   base honest, and it removes 20 183 nodes per toolchain from the verified
   core.
4. **Fallback, if con-leche will not generalise:** encoding A restricted to the
   v4.33.0 variant (the toolchain we target), *split into at least sixteen
   functions of ≤ 1 500 nodes* — Charon OOMs on one big one — and the other
   two toolchains deferred.  That is ~20 000 proof steps and a 1.5 MB generated
   file for something the install gate re-checks anyway; it is the option of
   last resort.

**The `provenance.py` work.**  Two changes, both small.  *Module-level
citations* (§3.7): `//! con-leche: <path>:<range> <decl>` is now accepted
alongside `//! con-leche: none`, is checked exactly like an item citation, is
rewritten in place by `update` (a `Cite` remembers its `///`/`//!` form, and so
does a `CHANGED` marker), and exempts the file's items from the per-item
requirement — which is what a generated file wants: `basis_tables.rs` carries
one citation for seven functions.  *The ledger's `/-!` false positive* (task
#13): `coverage`'s declaration scan now skips lines inside `/- … -/` blocks.
Twelve phantoms disappeared — `install` (`ExprOps.lean:964`, the one task #13
named), and also `and`, `natively`, `constructor`, `to`, `proposition`,
`proposition).`, `eta`, `route's`, `declaration,`, `must` in ten other files —
taking the declaration total from 1 018 to 1 006 and nothing else.

**Coverage** (`scripts/provenance.py coverage | tail -3`), con-leche
3e004805: **TOTAL 213/1006 covered (21.2 %), 793 uncovered** — the count moved
because of the false-positive fix (212/1018 before) and `BasisA.lean` went
**0/1 → 1/1**.

**Left for next time.**  Hoist the two `backward.*` options into
`proof/lakefile.toml` and revisit the earlier `Refine/*` files with `step`
available — that is likely to shorten them substantially.  Move the `T22`
abstraction functions into `Abs.lean` on merge with task #20, and the
specification tier into a file of its own once a second consumer appears
(`env`'s own functions will want all forty).  Then `divModCertStmts` when
`Kernel/Checker.lean` is ported, and the con-leche request in
recommendation 3.  The emitter needs nothing further: it already handles
`fvar`, `letE`, `proj`, both literal kinds, `RecRuleFire.nested`, `ProjTable`
and `defnInfo`/`thmInfo`/`projInfo`, none of which the basis blocks use.
577/1018 covered (56.7 %), 441 uncovered** — up from **382/1018 (37.5 %)**,
+195.  Per file: **`Inductives/Modeled.lean` 23/23**,
**`Inductives/NativeParts.lean` 34/34**,
**`Inductives/NativeInstall.lean` 20/21**,
**`Inductives/NativeInstallF.lean` 5/5**,
**`Inductives/StructParts.lean` 33/36**,
**`Inductives/StructInstall.lean` 2/2**,
**`Inductives/StructInstallF.lean` 5/5**,
**`Inductives/SumInstall.lean` 14/14**,
**`Inductives/SumInstallF.lean` 8/8**,
**`Inductives/SumParts.lean` 3/3**; and the three files this task borrowed
from moved too — `CheckerBase.lean`, `DeclCheck.lean` and `Cached/CheckerC.lean`
each gained the blocks `checker_local`/`modeled`/`inductives_c` cite.

#### Notes for the neighbouring tasks

* **Task #24** (`kernel/checker*.rs`, `cached/checker_c.rs`): the `*F` twins of
  `Kernel/DeclCheck.lean` that belong to the modeled route are **already
  ported**, in `kernel/inductives/modeled.rs`, each as the second citation of
  its `Modeled.lean` twin — `checkMemberValF`, `checkIotaThmF`,
  `nestedRuleShapeF`, `checkIotaThmNF`, `checkIotaRuleF`, `checkIotaRulesF`,
  `checkProjLookupsF`, `checkProjTyF`, `checkProjIotaF`, `checkEtaThmF`,
  `checkUnitThmF`, `ctorResidualOkF`, `indBlockCapsF` — and so are
  `checkConstantValF` and `checkProjRuleF` (in `checker_local`).  What that
  task owes the routes is the *unification*: move `checker_local`'s 40 items
  into its own modules and turn `checker_local` into a set of `use`s.  Its
  entry points into this directory are `inductives_c::check_native_s` (a
  recognised direct block, `Cached/ParsedC.lean:239`) and
  `inductives_c::check_ind_decl_s` (everything else).
* **Task #22** (`kernel/basis_tables.rs`): `checker_local::eq_a` is the
  annotated `Eq` pin spelled by hand, with a test that the annotation pass
  reproduces it.  When `basisA` lands, `eq_a` becomes a `use` and the test
  moves with it.
* **Task #13's leftover**: `Expr.allLevelParamsDefined` and its `*Go`/`*Fast`
  are now ported (in `checker_local`); `Expr.allLevelParamsDefined`'s
  `LPMemoInv` stays uncovered as the other memo invariants do.  Moving them to
  `kernel/level.rs` closes the `Level.lean` gap task #13 recorded.

### Task #26 — `ExprOpsC` and the parsed-declaration checker (2026-09-12, Opus under Fable)

P1.5's cached half, and the last implementation file of the `Cached/` tier
that was not ported: `ConLeche/Cached/ExprOpsC.lean` (832 lines, **37/37**
declarations) as `crates/con-ron-core/src/cached/expr_ops_c.rs`, and the
executable body of `ConLeche/Cached/ParsedC.lean` (264 lines, **8/10**) added
to `cached/parsed_c.rs`, whose `DeclC` task #14 had already taken.
`checkDeclC` and `checkDeclStepC` now exist in the crate, over the closed knot
of tasks #18 and #23, the declaration checker of task #24 and the inductive
routes of task #25 — so the cached lane has a complete per-declaration step
with **no placeholder anywhere in it**.

Charon and Aeneas both succeeded on the **first** run — zero Aeneas errors —
and the reason is recorded below, because it was not luck.

#### Two tiers of the same walks, and the memo policy is the difference

`Kernel/ExprOps.lean` (task #13) is the tier the semantic verification
reasons about; `Cached/ExprOpsC.lean` is what `Cached/CoreC.lean`,
`Cached/StateC.lean`, `Cached/CheckerC.lean` and `Cached/ParsedC.lean`
actually call, with `ConLeche/Verify/Cached/OpsC.lean` proving each function
equal to its `ConLeche.Expr` counterpart.  §3.1 makes the differences
binding, and there are exactly four:

1. **A derived-field cutoff at the head of every walk** — `bvarB ≤ d`,
   `fvarB ≤ d`, `fvarB == 0`, `!hasLP` — returning the node **itself**, so
   the result shares memory with the input and a later `ptr_eq` on it is
   `O(1)`.  `expr_ops`' twins have no such cutoff.  (This is the retired
   arena's "return the same index", and it is why `instantiate1` is `O(1)`
   on a subterm closed at the cursor.)
2. **Only compound nodes are memoised, and the key is built once**
   (con-leche task #177): the probe and the insert sit *inside* the
   `app`/`lam`/`forallE`/`letE`/`proj` arms, and an atom — the loose `bvar`s
   above all, the most numerous nodes a substitution touches — is answered on
   the spot, because recording a one-word answer under a two-word key was
   pure loss.  The exceptions prove the rule: four walks probe *before* the
   match (`instLevelParamsGo`, `wscopedBGo`, `leavesSubGo`,
   `allLevelParamsDefinedGo`), and there every node kind does get an entry.
   The port follows **each function's own shape**: a probe or an insert the
   Lean does not do is exactly what §3.1 forbids, in either direction.
3. **The bulk key carries no live prefix.**  `instantiateListGo`'s and
   `instantiateRevGo`'s key is `(node, cursor)`, not `(node, cursor,
   prefix)`: `k` is invariant over the life of one table, and the `bvar`
   arm's re-entry — the one place it shrinks — runs under a **fresh** table.
   So `instantiate_list_go` and `instantiate_rev_go` allocate a table in that
   arm and nowhere else, and the arm's two guards (`j = 0`, or the
   replacement closed at the cursor) mean the common case — the checker
   substitutes `fvar`s — allocates none.
4. **Short-circuiting *is* memo policy.**  `wscopedBGo`, `leavesSubGo` and
   `allLevelParamsDefinedGo` stop at the first `false` and therefore write
   *fewer* entries than an unconditional `&&` would.

#### The `bool_and` rule, refined — and why Aeneas was silent

Task #24's rule was "a memoized walk's arm must end in a call or a
constructor, never in a branch", and its fix was `expr_ops::bool_and(b1,
b2)`, which **computes both operands**.  Three of this file's walks
short-circuit, so `bool_and` would have written memo entries the Lean does
not — a *hit where the Lean misses*, the one deviation §3.1 says would force
redoing con-leche's memo-soundness tier.  The refinement that lands here:

> **Lift the branching arm into a one-line callee.**  The arm becomes
> `wscoped_b_pair(memo, d, x, y)` — a single call, so no two borrow contexts
> join at the insert — and the branch lives inside that callee, where the
> outer `&mut memo` is not live at a join.  Same branch, same entries, one
> more stack frame.

Twelve such callees carry it: `wscoped_b_fvar`/`_pair`/`_triple`,
`leaves_sub_fvar`/`_pair`/`_triple`, `alpd_pair`/`_binder`/`_triple`,
`instantiate1_lift_b_compound`, `instantiate_list_bvar`,
`instantiate_rev_bvar`.  Where the Lean has *already* computed both sides —
`allLevelParamsDefinedGo`'s binder arms, `(rb && m.pw.paramsDefined params,
memo)` — `expr_ops::bool_and` is used, exactly as task #24 asks.  Applied a
priori, this is why Aeneas gave no error on a thousand lines of
`&mut`-threaded walks: **`bool_and` is for a conjunction the Lean evaluates
eagerly; a callee is for one it short-circuits.**

The visible price is in the SCC decomposition: `Funs.lean` goes from **8
`mutual` blocks to 14**, the six new ones being exactly these lifted pairs —
`instantiate_rev_go`+`_bvar` (2 fns, 487 lines),
`instantiate_list_go`+`_bvar` (2, 484), `instantiate1_lift_b`+`_compound`
(2, 162), `all_level_params_defined_go`+3 (4, 123), `leaves_sub_go`+3
(4, 104), `wscoped_b_go`+3 (4, 101).  That is the *correct* decomposition — a
callee that recurses back into its walk genuinely is in its SCC — and the
fact worth recording is what did **not** happen: none of them joins the
84-function core knot, because the declaration checker and the syntactic
passes call *into* the knot and nothing in it calls back.

#### `ExprC` is `Expr`, so there is no `expr_c.rs`

`Cached/ExprC.lean` retired the second expression inductive at con-leche task
#172 B3a (`abbrev ExprC := ConLeche.Expr`, under the user's
`@[computed_field]` ruling), and its ten smart constructors are `@[inline]`
aliases with `mkApp_eq` and nine siblings the `rfl` equations.  So
`ExprC.mkApp` is `expr::app`, `ExprC.mkBVar` is `expr::mk_bvar`, and the file
needs no type and no module of its own — `ExprC.lean` stays 1/12 covered on
purpose (its eleven `mk*`/`ExprC` declarations are cited nowhere because they
*are* the constructors `expr.rs` already carries).

The one exception is its single executed *function*, `ExprC.hasFvar`
(`:113-115`), which **is** ported, duplicating `expr_ops::has_fvar`'s body
character for character.  That is deliberate: the two are different Lean
declarations — `ExprC.hasFvar` is the `O(1)` field read, `Expr.hasFvar` the
walk its `@[csimp]` twin replaces — and `ParsedC.lean`'s own docstring turns
on the distinction ("the two `hasFvar`s differ … which is why the guard below
names `ExprC.hasFvar` outright").  A single Rust function with two citations
would have erased the reason `ParsedC` writes the name out.

#### The parsed-declaration checker, against `kernel::checker`

`checkDeclC` mirrors `Kernel/Checker.lean`'s `checkDecl` branch by branch,
and the differences are exactly three — recorded once in `parsed_c.rs`'s
module doc rather than on fourteen items:

1. **The syntactic guards are the cached ones.**  `ExprC.looseBVarsBounded`,
   `ExprC.hasFvar`, `ExprC.allLevelParamsDefined` and `constsResolveFC`
   replace their `Expr`-level namesakes; the first three are
   `cached::expr_ops_c`'s, the fourth `cached::state_c`'s (task #23).
2. **Every accepted constant is recorded in `ienv`.**  `recordCConst` runs
   between the resolution guard and the inference for a definition, theorem
   or opaque, and before each axiom install — tagged with the very `Expr`
   objects about to be pushed, because that entry is what the cached lazy
   accessors (`constTyAtM`, `constValAtM`) read.  A definition's entry
   carries the value pair (`vE := jv`, both components that node); a
   theorem's and an opaque's carry `none`; the tolerated `sorryAx` gets none
   at all, as the cited `pure fe` arm has it.
3. **The pinned-name tests come before the push.**  `checkDeclC`'s `defn`
   and `opaque` arms branch first and hand `fe` to `push` unshared —
   con-leche's own RC-linearity rule, with the comment in `checkDeclC` itself
   ("with `fe` still live after the push … `checkOpaqueValC`'s `fe.push`
   copied the whole index on EVERY opaque install").  The port threads the
   index by value (task #14), so the same branch is what keeps the common arm
   one tail call.

Everything else is *shared*, and that is the `CheckerOps` collapse of task
#24 paying a second dividend: the pin gates (`checker::check_defn_pins`,
`check_reduce_pin`), the axiom pins (`std_axioms`, `trust_axioms`) and the
basis install (`checker::check_basis_decl`) are the `FEnv`-indexed twins the
port already spells **once** (task #18's deviation 3), so `check_defn_pins_c`
and `check_basis_decl_c` are three-line wrappers carrying the `ParsedC`
citation and nothing else.  `sharedOpsC mode fe`, the record the cited code
passes them, has no Rust spelling at all: there is no record, and its five
core slots are `kernel::type_checker`'s by name.  `opSIxC` is one more of
those — `ensureSortI (coreKnotI mode fe checkFuel)` is
`type_checker::ensure_sort_core`.

#### The `.indDecl` arm dispatches; nothing here is stubbed

The arm is **ONE ROUTE, dispatched by the recogniser alone** (con-leche tasks
#210 and #219), which is what task #25's `inductives_c` module note said this
call site would be:

```rust
if env::ind_params_ok(n_p, block) {
    match native_parts::native_parts(n_p, block) {
        Some(p) => inductives_c::check_native_s(mode, st, &fe, &p),
        None => inductives_c::check_ind_decl_s(mode, st, fe, block),
    }
} else { Err(…"number of parameters mismatch") }
```

`indParamsOk` runs **first and for both routes** (con-leche task #228:
official reads `nparams` off the declaration, so a `false` is official's own
*reject*, not a decline), and the two drivers' signatures differ in one way
worth recording: `check_native_s` takes the index **by reference** and
`fenv::dup`s it internally (`native_install::check_native_pass_former`), so
the extended index it returns *is* the arm's result and the caller's `fe` is
consumed by being dropped; `check_ind_decl_s` takes it by value, as the
port's other install paths do.  Three lines, no adapter, no deviation.

#### Three reconciliations the merge with tasks #23 and #25 made possible

This task landed after the three concurrent ones, and finishing it meant
retiring three notes that were true only while `ExprOpsC` was unported.  All
three are *memo-policy* corrections, i.e. exactly what §3.1 does not let a
port leave open.

1. **`Cached/StateC.lean`'s nine `*M` wrappers now wrap the `ExprC` twins.**
   Task #23 wrote them against `kernel::expr_ops` with an explicit note
   ("`Cached/ExprOpsC.lean` … is **not** ported … the twins compute the same
   values"), which was the right call then and is wrong now: the twins do
   compute the same values — that is `Verify/Cached/OpsC.lean`'s subject —
   but not by the same policy, and con-leche's own `ExprOpsC` docstring is
   emphatic that the difference is a *computation* and not a value.  So
   `inst1_m`, `inst_list_m`, `inst_list_rev_m`, `abstract1_m`,
   `abstract_range_m`, `mk_app_n_m`, `inst_spine_m` and `inst_level_params_m`
   call `cached::expr_ops_c` now, each with the `ExprOpsC` block as a second
   citation, and `inst_list_m` keeps the `instC` memo and its 32 000 000-entry
   bound around `expr_ops_c::instantiate_list`.  `bvarBoundM` is untouched
   (it is `Expr.bvarB`, an `O(1)` field read either way).  Two helpers went
   with the change: `state_c::rev_exprs`/`rev_exprs_from`, which existed only
   to reverse the spine for `instListRevM` because `ExprC.instantiateRev`'s
   end-indexing had no Rust spelling — it has one now
   (`expr_ops_c::instantiate_rev`), and the `Vec` copy per call that the
   cited code does not make is gone with them.
2. **`core_c::pi_residual_m` wraps the bulk form.**  `piResidualM` is
   `pure (ExprC.piResidual e args)`, and `Cached/ExprOpsC`'s `piResidualAcc`
   peels the whole argument list and substitutes **once**, where
   `core_k::pi_residual` — the `Core.lean` original, still ported and still
   the spec — peels and instantiates one binder at a time.  One call site.
3. **`constsResolveFC` is called by name.**  While task #23 was in flight
   this module called `decl_check::consts_resolve_f_fast`, the `Expr`-level
   memoised walk, and flagged the difference (the C twin probes before the
   match, so it records the four atom kinds too; the port therefore *missed*
   where the Lean hit, on an `O(1)` leaf answer — the safe direction, but a
   deviation).  `state_c::consts_resolve_fc` exists now, and the four call
   sites in `check_constant_val_c_after_annot`,
   `check_defn_val_c_after_annot`, `check_thm_val_c_checked` and
   `check_opaque_val_c_after_annot` use it.  **The note is retired.**

**One reconciliation is still owed, and it is not this task's to make.**
`core_k::proj_entry_type_at` carries the `ProjEntry.typeAtI` citation task
#23 gave it and is what `core_k::infer_proj_at` — the shared `.proj` clause
of both inference bodies — still calls, so the executed `.proj` type is the
`Expr`-level formula: the same value, one memo policy short of the cited one
(and that policy is the subject of the `typeAtI` docstring's own
affine-frontier paragraph).  `expr_ops_c::proj_entry_type_at_i` is the
faithful spelling and is ported; retargeting the one call site is two lines,
but it would make `kernel::core_k` depend on `crate::cached`, which task #23
deliberately kept it free of ("its syntactic layer"), so it belongs with
whoever next owns that seam.  Flagged in `expr_ops_c.rs` on the item.

#### Constructs that do not survive transliteration

Beyond the memo-policy points above, and all a priori:

1. **The three `abbrev` memo tables are Rust type aliases** — `MemoN`,
   `MemoNL` (the same type, kept as two names because `MemoLInv ws k memo` is
   stated of the second) and `Memo0`.  Erased before Charon, as
   `core_types::CheckM` and `state_c::CheckCM` are; they are there so a
   ported signature says what con-leche says.  The key *dictionaries* are
   reused, not re-derived: `expr_ops::ExprNatKey`'s `Hashable`/`Eq2` are
   Lean's derived instances on `(ExprC × Nat)` at the same components (task
   #14's point 6).
2. **The cited dependent `if _h : i - d < k`** (`instantiateListGo`,
   `instantiateRevGo`) is an ordinary `if`: its only purpose is to put
   `i - d < k` in scope for the `termination_by (k, sizeOf e)` obligation,
   and Aeneas's `partial_fixpoint` carries no measure, so neither the
   dependent `if` nor the `decreasing_by` block has a counterpart.  Same for
   `piResidualAcc`'s `(as.length, acc.length)`.
3. **`instantiate1LiftB`'s clause order.**  The cited `match fuel, e with`
   puts the atom arms *before* `| 0, _ => (none, 0)`, so they answer at an
   exhausted budget too; the port matches on the node first and tests the
   budget only on the compound kinds, which is the same clause order.  The
   `| r => r` forwarding arms are `(None, fuel)` spelled out, there being no
   pair to forward.  The budget is the cited 4096.
4. **`fvarLeavesGo`'s `seen` set is a `HashMap<Expr, ()>`** — Lean's
   `Std.HashMap ExprC Unit`, and Aeneas translated the `Unit` value type
   without complaint (`ron.hashmap.HashMap kernel.expr.Expr Unit`, and
   `insert … e ()` in `Funs.lean`).  Its accumulator is threaded by value and
   the cited `(idx, ty) :: acc` front cons becomes a push, so the list comes
   out reversed; the only consumer is `leafMem`, a membership test, and the
   `seen` set makes the list duplicate-free, so the *set* the cited
   `leafGuard` reads is the same set.  Documented on the item.
5. **`args.reverse`/`targs.reverse` is a local `rev_append_exprs`** — the
   same downward index recursion `core_k::rev_append_exprs` is for
   `Core.lean`'s own `ProjEntry.typeAt`, cited `none` here because the Lean
   text it stands for is `instSpine`'s and `typeAtI`'s.
6. **`leafMem`'s `(i == idx && t == ty) || rest` and `abstractRangeGo`'s
   `d ≤ idx ∧ idx < d + k`** are `if` nests (task #3's pattern 9); the
   `i - d = 0 || w.bvarB ≤ d` disjunction likewise.
7. **`piResidualAcc`'s `a :: acc` is a genuine front cons**
   (`expr_ops::cons_expr`): the accumulator's order is what
   `instantiateList` reads.  `getAppArgsAcc`'s is not — pushing after the
   recursive call gives the same list in one pass (task #13's deviation 3).
8. **Every `(d : Nat := 0)` / `(k : Nat := 0)` default is an explicit
   argument** (task #14's point 2: Rust has no parameter defaults).
9. **The long `do` blocks are split at the annotation**, as task #24's
   deviation 7 does it prophylactically: `check_constant_val_c` →
   `_after_annot`, and the same for `check_defn_val_c`, `check_thm_val_c`
   (three functions: the is-a-proposition gate, the witness guards, the
   comparison) and `check_opaque_val_c`; `checkDeclC`'s six arms are six
   functions, so every one of them is a tail call.
10. **`liftFueled "level comparison"` is `core_k::lift_fueled`** —
    monomorphic and stringless (task #18's deviation 1).
### Task #27 — Wiring: basis tables, `ConstantInfo` equality, `checker_local` unified (2026-09-12, Opus under Fable)

P1.5's wiring task: the three loose ends tasks #22, #24 and #25 left for each
other, closed.  No new con-leche file is ported; what changes is that the
crate now has **one** spelling of everything those three tasks needed from one
another, and the pinned basis actually installs.

#### 1. The basis stub is gone: `basis_pins.rs` is the two exactly-compared pins

Task #24's `kernel/basis_pins.rs` was a stub — `decls_a` returned the empty
block and `is_pinned_eq_basis`/`is_pinned_nat_basis` answered `false` (sound,
because both are declines, but the `.basisDecl` arm installed nothing).  Task
#22 then generated the table.  The split that landed is the one `BasisA.lean`
itself has:

* **`BasisKind.declsA` is `basis_tables::basis_decls_a`** — generated, proved
  (`Refine/BasisTables.lean`), and now what `checker::check_basis_decl` folds
  `installBasisDecl` over.  `basis_pins::decls_a` is deleted.
* **`kernel/basis_pins.rs` survives, non-stub**, as the *hand-written*
  consumer layer of that table: `eq_a`/`nat_a` (the pins, read off the head of
  their block — `declsA` fixes the install order, `.eqK => [eqA, eqReflA,
  eqRecA]`), the two predicates, and the two environment-level guards
  `eq_basis_pinned`/`nat_basis_pinned`.  It is not folded into
  `basis_tables.rs`, because that file is regenerated by `lake exe
  con-ron-gen-tables` and hand-written items in it would be overwritten.
* `std_axioms::eq_basis_pinned` moves there too (it was the same lookup),
  taking its `stdAxiomOk`/`stdAxiomOkF` citations with it, and
  `trust_axioms::reduce_elem_ok`'s `Nat` branch is now
  `basis_pins::nat_basis_pinned`.  Twelve call sites across
  `checker`/`decl_check`/`trust_axioms`/`modeled`/`inductives_c` go through
  the one function.

**The comparison is the derived structural one, and that was checked, not
assumed.**  Every kernel site spells `==` or `decide (… = some eqA)` on
`ConstantInfo`; `ConstantInfo.canonEq`/`canonEqFast` (`Frontend/Export.lean:279`),
which canonicalises level-parameter *names*, is used by
`Frontend/ExportC.lean` alone and never below it.  So the port needs Lean's
`deriving DecidableEq` written out, and `kernel/env.rs` now has it:
`constant_info_beq` over `constant_val_beq`, `rec_rule_fire_beq`,
`rec_rule_beq`/`rec_rules_beq`, `reducibility_hint_beq`, `ind_caps_beq` and
`proj_table_beq` — componentwise in the cited field order, over the crate's
own `name::beq`/`expr::beq`/`level::beq`/`prop_when::beq` with their pointer
fast paths (§3.2).  `env.rs`'s module note, which said "no derived equality",
is corrected to name its two executable consumers: these guards and
`blockRecSuffixDec`.

A `Vec<Expr>` equality was needed and existed twice already
(`inductives::struct_parts::exprs_beq` and `cached::state_c::exprs_beq`, the
latter cited to `CState`'s own `BEq (List ExprC)`).  `expr::exprs_beq` is now
the one for the kernel, beside `expr::levels_beq` where it belongs; the
`struct_parts` copy is deleted and its five callers point at it.  The
`state_c` one keeps its distinct citation.

`eqA = eqRaw` stays a **fact with a test**: `basis_pins::eq_a` carries the
`Basis/Eq.lean:22-28 eqRaw` citation task #25 wrote, and
`eq_a_is_annotated` runs the port's own `core_c::annotate` on the *table's*
value and compares — so an upstream change to the raw pin, or a
re-generation that moves the annotated one, breaks a test rather than a
verdict.

#### 2. `checker_local` is unified away — no function exists twice

Task #25's `kernel/inductives/checker_local.rs` (1 469 lines, ~40 cited items
"to be unified by task #24 with a move plus a `use`") is **deleted**.  Item by
item:

| checker_local | now |
|---|---|
| `checkConstantVal`, `checkTypedList`/`checkAnnotList`/`checkDefEqList` (+ `*_from`), `isEqHead`, `eqHeadLevel`, `Env.findCV?`, `unwrapOr`, `checkProjShape`, `checkProjRule`, `fvar_types_of` | deleted — `kernel::checker_base` had all of them |
| `open_pis_at_fvars_spec` / `open_pis_at_fvars_f_go` / `open_pis_at_fvars` | `checker_base::open_pis_at_fvars` / `…_f_go` / `…_f`.  The local module had *renamed* the pair (its `open_pis_at_fvars` was the one-pass `openPisAtFvarsF`), so every caller moved to the `_f` name; `checker_base`'s `*_f_go` is also the faithful one — it instantiates with `instantiate_list_fast`, the executed `instantiateList`, where the local copy used the pure walk |
| `DomView` / `DomIdent` / `doms_match_aux` / `doms_match_aux_from` | **moved into `checker_base`, and the abstraction won**: task #24 had made `domsMatchAux` monomorphic at the identity view because its own call sites all pass `fun _ e => e`, and task #25 needed the renaming view (`modeled::DomProjFwd`, `checkProjIotaF`).  `checker_base::doms_match_aux` is now generic over `DomView` again, as the cited `g : Nat → Expr → Expr` is, and `checker_base`/`decl_check`'s three call sites pass `DomIdent` |
| `all_level_params_defined_spec` / `levels_defined_from` / `*_go` / `*_node` / `all_level_params_defined` | deleted — `expr_ops::all_level_params_defined` (spec), `levels_all_params_defined`, `all_level_params_defined_go`, `all_level_params_defined_fast`.  Task #24 had closed task #13's leftover in `expr_ops`, and its `*_go` needs no probe/descent split because its arms end in `bool_and`/`bool_and3` calls, which is why the pair `*_go`/`*_node` — **a `mutual` block in the generated Lean** — disappears |
| the nine derived `*_beq`s and `block_rec_suffix_ok` | `kernel::env` (above) |
| `eq_a`, `eq_basis_pinned` | `kernel::basis_pins` (above) |

Two things were *fixed* rather than merely moved, both in the surviving
`checker_base` copy, both faithfulness:

* **`nF - 1 - i` is `expr_ops::sub_nat(n_f, 1 + i)`** in `check_proj_rule` and
  `check_proj_rule_shape`.  Lean's `Nat` subtraction truncates; a `u64`
  subtraction is a Rust overflow (an Aeneas `fail`, so still sound for the
  accept direction, §1) where the Lean returns `bvar 0`.  This is task #25's
  rule applied to task #24's file, using `(a - b) - c = a - (b + c)`.
* Task #25's `checkProjRuleF` used the *non*-`F` walkers (`instPisAt`,
  `instLamsAt`, `openPisAtFvars`); the cited executed mirror
  (`DeclCheck.lean:763-795`) calls `instPisAtF`/`instLamsAtF`/`openPisAtFvarsF`,
  which is what `checker_base`'s copy already did.  The surviving spelling is
  the executed one.

`inductives/mod.rs`'s "`checker_local` is owed to task #24" section becomes a
table of where a route now gets each piece.

#### 3. The end-to-end sanity test

`crates/con-ron-core/tests/basis_install.rs` (167 lines, 4 tests) — the first
integration test in the crate, because it crosses five modules and belongs to
none of them (`tests/` is outside `lint-rust-style.sh`'s and
`provenance.py`'s roots, as it is outside Charon's).  From an **empty** `FEnv`
it installs all six pinned blocks through `checker::check_basis_decl`
(`Eq` first — the quotient block's guard requires it) and then asserts:

* all **19** constants of the six blocks are stored, each equal to the
  table's entry under `env::constant_info_beq`;
* `False`, `Eq` and `Nat` are found by name and stored as `indInfo`s, with
  `Eq` carrying one level parameter and `ruleK`, `False`/`Nat` none; a name
  never installed is not found;
* `basis_pins::is_pinned_eq_basis` is **true on the stored constant** and
  **false on a perturbed copy** — the same `ConstantVal` with `ruleK` dropped
  (which `ConstantVal.matchesPin` would not even see) and one with the level
  parameter dropped — and an environment holding the perturbed `Eq` makes
  `check_basis_decl .quotK` decline rather than install;
* installing a block twice is `installBasisDecl`'s duplicate rejection.

This is what `Cached/Installed.lean`'s stream will drive once it is ported;
until then it is the only thing that runs the `.basisDecl` arm end to end.

#### Numbers

| | |
|---|---|
| Lean ported: `Cached/ExprOpsC.lean`, 37 cited blocks (all 37 declarations) | 701 raw / **660 code** |
| plus `Cached/ParsedC.lean` 8 cited blocks (7 new; `DeclC` was task #14's) | 181 raw / **163 code** |
| plus `Cached/ExprC.lean` 1 block (`hasFvar`) | 3 raw / 2 code |
| `src/cached/expr_ops_c.rs`, extracted part (raw / code) | 1 453 / **1 009** (1.5× the Lean code) |
| `src/cached/expr_ops_c.rs`, `#[cfg(test)]` part (2 tests) | 189 / 139 |
| `src/cached/parsed_c.rs`, extracted part (raw / code) | 748 / **506** (was 91 / 36) |
| `src/cached/parsed_c.rs`, `#[cfg(test)]` part (5 tests, 3 new) | 362 / 286 |
| generated `Types.lean` | **736 — unchanged**; neither module declares a type (the three memo `abbrev`s are erased aliases) |
| generated `Funs.lean` | 46 776 → **51 552** (+4 776: `expr_ops_c` 3 774, `parsed_c` 1 045, the reconciliations −43) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 — **unchanged**, byte for byte |
| `charon cargo --preset=aeneas` wall (after `cargo clean`) | **3.77 s** (the `.llbc` is 179 MB, was 71 MB at task #24) |
| `aeneas -backend lean -split-files -loops-to-rec` | **33.3 s** self-reported |
| `partial_fixpoint` (whole crate / this task) | 387 → **417** (+30: `expr_ops_c` 31, `parsed_c` 0 — the parsed checker is a fold of tail calls, not a recursion — and `state_c` −1, the retired `rev_exprs_from`) |
| `mutual` blocks in `Funs.lean` | 8 → **14**: the six new ones are the lifted short-circuit callees above, 1 461 lines between them; **the 84-function core knot is untouched** |
| `mutual` blocks in `Types.lean` | 3 — unchanged |
| `cd proof && lake build` after the regeneration (`gates.sh`) | **179 s (2 108 jobs)** |
| external holes | **exactly the four `Rc` axioms and the `Rc` type** |

`cargo build`/`cargo test` warning-free, **146/146** green (141 from tasks
#6-#25 + 5 new); `scripts/lint-rust-style.sh crates/con-ron-core/src` clean;
`scripts/provenance.py check` green — 1 547 items, 1 649 citations,
all current at pin 3e004805; `scripts/gates.sh` all 6 OK.  The progress lines
it prints:

```
Verified core (ConLeche/Kernel, ConLeche/Cached)           to translate  13987  translated  12952 (92%)  verified    498 (3%)
Cherries (ConLeche/Frontend without Scan/Equiv, Main.lean) to translate   8132  translated      0 (0%)  verified      0 (0%)
Rust core 40442 lines (1372 fns) | unverified crates 2471 | generated Lean 52461 | proofs 11247 (121 _refines) | pin 3e004805
```

The 1.5× Rust→Lean-code ratio on `expr_ops_c` is the lowest of any walk-heavy
module so far (`expr_ops` was 1.7×, `core_k` 3.3×) and the 3.7×
Rust→generated ratio is task #13's ten-constructor-`match` phenomenon again:
each memoised walk matches on ten constructors twice, once for the
cutoff/atom arms and once inside the miss branch, and Charon expands every
wildcard.

#### Tests

Five new, all `#[cfg(test)]` and invisible to Charon.

`expr_ops_c` (2).  **The memo hit, asserted on the table and not on the
answer**: the subject is `f s s` with one *shared* `s = λ (_ : A). bvar 1`
occurring twice, and after one `instantiate1_go` the table holds **exactly
three** entries — the outer `.app`, the inner `.app`, and `s` once, the second
occurrence being the hit — while `A`, `f` and the `.bvar`s, being atoms or
below the cutoff, are never recorded (module note 2 in code).  A second walk
on a fresh table writes the same three (the count is a property of the term,
not of the history); a second walk on the *same* table writes nothing more and
answers the same term; and a term closed at the cursor comes back **itself**,
with no table allocated at all.  **The cached walks against the
specifications** on that same shared-DAG term: `instantiate1`,
`instantiateList`, `instantiate1Lift`, `abstract1`, `abstractRange`,
`instSpine`, `instLevelParams` and `allLevelParamsDefined` each agree with
`expr_ops`' twin — which is what `Verify/Cached/OpsC.lean` proves in general —
with `instantiateRev` on a one-element array agreeing with `instantiateList`,
`abstractRange` at `k = 0` the identity, the `O(1)` scope reads agreeing with
the walks at and off the bound, `fvarLeaves` finding the one leaf, `leafGuard`
passing a fabrication over the subject's own leaves and refusing a foreign
one, `piResidual` peeling a one-binder telescope and declining a
non-telescope, and `instLevelParams` leaving a `hasLP`-negative term
untouched.

`parsed_c` (3 new).  **`checkConstantValC`'s rejects** — a stored name is
`.invalid` before anything is annotated, a type with a loose bound variable is
`.invalid` (and the guard is asserted directly to be the cached bound read
answering `false` at 0), a reserved basis name is `.invalid`, and the positive
control comes back with its type **annotated** and paired with itself.
**`checkDefnValC` accepts `(λ x : Sort 1. x) : Sort 1 → Sort 1`** — built from
`Sort`/Π/λ terms over the empty index as `core_k`'s tests build theirs; it
installs as a `defnInfo` holding the annotated value, the visibility bound
advances by exactly one, and **the `ienv` entry is asserted**, with its value
pair present, because writing it is this file's deviation 2.  The negative
control is the same header at value `Sort 1`, the one *reject* the value check
can produce.  **`checkDeclStepC` flushes first and then dispatches** — the
flush is asserted through a step whose check fails at `checkConstantValC`'s
*first* guard (a duplicate name), so nothing downstream annotates anything and
what is left in `annot_c` is exactly what the flush left, while the
self-certified `ienv` survives; then the `.indDecl` arm is shown to reach task
#25's routes (a `T : Sort 0` block the recogniser refuses and the modeller has
no `_model` for is refused from *inside* the modeled route) and to **reject** a
declared `nparams` the block cannot satisfy; and a non-standard axiom declines
at its own record through the same fold.

#### Deliberately not ported

* `ParsedC.lean`'s `msSecs` (`:247`) and `declCLabel` (`:251`) — the driver's
  progress-line rendering, `String`-valued and on no verdict path (§3.1:
  message strings need not match).  `ParsedC.lean` is therefore **8/10** and
  stays there.
* `ExprC.lean`'s `ExprC` (`:109`) and its ten `mk*` constructors
  (`:127-149`) — cited nowhere because they *are* `expr.rs`'s constructors,
  with the file's own `mkApp_eq` &c. the `rfl` equations (above).  Its ten
  `@[simp] theorem`s likewise: they are the spec.
* `ExprOpsC.lean` has **nothing** unported — no `theorem` and no memo
  invariant of its own; the `*_spec` equations with `ConLeche.Expr`'s
  operations live in `ConLeche/Verify/Cached/OpsC.lean` and are the
  specification this port will be proved against (task #13's ruling).

#### Coverage

`scripts/provenance.py coverage | tail -3`, con-leche 3e004805: **TOTAL
843/1006 covered (83.8 %), 163 uncovered** — up from **800/1006 (79.5 %)** at
this branch's merge base (+43).  Per file: **`Cached/ExprOpsC.lean` 2/37 →
37/37**, `Cached/ParsedC.lean` 1/10 → **8/10**, `Cached/ExprC.lean` 0/12 →
**1/12**; everything else unchanged.  So the ledger agrees with the prose in
every file, and **every implementation file of `ConLeche/Cached/` except
`Installed.lean` is now ported**.

**Note for the next task.**  `cached::state_c` gained no field from this task,
because every memo in `ExprOpsC.lean` is local (`{}` per call): `StateC.lean`'s
nine `*M` wrappers are `pure (ExprC.…)`-bodied, so the port's callers call
`cached::expr_ops_c`'s functions directly (task #14's point 9) and there is
nothing to store.  What is left of the `Cached/` tier is
`Cached/Installed.lean` — the declaration fold `checkDecls`/`checkPending`
that `checkDeclStepC` is the step of, and the install/check phase split whose
two seam records (`PendingCheck`, `ValueGroup`) are already here.
| `kernel/inductives/checker_local.rs` | 1 469 → **deleted** |
| `kernel/env.rs` (extracted / tests) | 1 152 → **1 461** (1 200 / 261) |
| `kernel/basis_pins.rs` (extracted / tests) | 70 → **272** (126 / 146) |
| `kernel/checker_base.rs` | 871 → **905** |
| `kernel/expr.rs` (`exprs_beq`) | 1 158 → **1 184** |
| `crates/con-ron-core/tests/basis_install.rs` | 0 → **167** (4 tests) |
| generated `Types.lean` | **736 → 736** — no type added or removed; 60 changed lines, all `DomView`/`DomIdent` moving namespace from `kernel.inductives.checker_local` to `kernel.checker_base` |
| generated `Funs.lean` | 46 776 → **45 241** (**−1 535**: the ~40 duplicated bodies) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 — **unchanged**, still **exactly the four `Rc` axioms and the `Rc` type** |
| `partial_fixpoint` | 387 → **376** (−11) |
| `mutual` blocks in `Funs.lean` / `Types.lean` | 8 / 3 → **7 / 3** — the block that goes is `all_level_params_defined_go`/`_node`, the probe/descent pair the local copy needed and `expr_ops`' `bool_and` version does not |
| `charon cargo --preset=aeneas` | **3.5 s** |
| `aeneas -backend lean -split-files -loops-to-rec` | **30.0 s**, **zero errors, zero warnings** (first run) |
| `cargo test` | **146/146** green (142 unit + 4 integration), warning-free at `-D warnings` |
| `scripts/provenance.py check` | green — 1 379 items, 1 485 citations (was 1 405 / 1 516) at pin 3e004805 |
| `scripts/provenance.py coverage` | **800/1006 (79.5 %) — unchanged**, byte-identical to the pre-task ledger |

#### Left for next time

* `cached::state_c::exprs_beq` is still a second `Vec<Expr>` equality; it
  carries its own `Cached/StateC.lean:131-156 CState` citation (the memo key's
  derived `BEq`), so collapsing it into `expr::exprs_beq` is a `CoreC`-side
  call, not this task's.
* `struct_parts::memo_eb_get` and `expr_ops::memo_b_get` are the same probe
  helper twice, both cited `none`; same call.
* `kernel::nat_op_pins`' `nat_op_pin_sets()` is still the empty stub — task
  #22's recommendation 3 (encoding B, in the unverified driver) plus the
  con-leche request to make the pin list a parameter of `checkDecls`.
* `Expr.allLevelParamsDefined` lives in `expr_ops` rather than `level.rs`;
  task #24 put it beside `instantiate_level_params` for import order and
  `level.rs`'s note says so.  Nothing is owed, but the `Level.lean` ledger
  entry reads `expr_ops`.
### Task #29 — The scale corpus: prelude and Mathlib exports, dumps, con-leche baseline (2026-09-12, Opus under Fable)

P1.8's preparation, and everything in it that does not need the Rust checker.
The priority ruling puts performance on the critical path (§5: no proof work
"before we find out if the performance is acceptable"), but nothing of con-ron
can be measured until `check_decls` lands (P1.7).  Everything *around* that
measurement can exist now: the exports, the `con-ron-decls/1` dumps they
become, and con-leche's own verdicts and costs on the same streams — so that
the day `check_decls` runs, the baseline is already on disk and the only new
number is con-ron's.

**What landed.**  `scripts/corpus.sh` — four idempotent steps (build the
exporter and export; run con-leche; dump and read the dumps back in Rust;
rebuild three reports from whatever is on disk), each step skipped when its
output is there, every exporter/checker/dump run under `timeout` and
`ulimit -v 22000000` — and one flag in `proof/ConRon/Dump/Main.lean`:
**`--write-only`**, with a streaming writer behind it.  The corpus itself is
**not committed**: 7.16 GB of export and 3.57 GB of dump live in
`_tmp/corpus/`, with `README.md` (the exports), `baseline.md` (con-leche) and
`dumps.md` (the dumps) generated beside them.

**The exporter.**  `leanprover/lean4export` @ **`15f6055`**, which is both the
`chore: bump toolchain to v4.33.0 (#44)` commit *and* the repo's `v4.33.0`
tag — so con-leche's task-#199 recipe (walk `git log -- lean-toolchain`, take
the newest commit whose file equals ours) and "check out the tag that matches
the toolchain" pick the same commit here; `corpus.sh` implements the former,
because the toolchain file and not the tag is what the format tracks.  Stream
header: `lean4export 3.1.0`, format 3.1.0, Lean 4.33.0 (`d8b18978`) — the same
exporter con-leche's own self-check used.  `--export-unsafe` and
`--export-mdata` stay off (the defaults), so no `unsafe` declaration and no
`.mdata` node is in any of these streams.  Build: `lake build`, 4 s.

**The exports.**  `lake env` is the whole `LEAN_PATH` story: the two core
exports run from the exporter's own package (whose toolchain carries `Init`,
`Std` and `Lean`), and Mathlib is exported from the tree that already has it
built at v4.33.0, `_tmp/aeneas-lean`, naming the exporter by absolute path.
Nothing had to be assembled by hand, and Mathlib needed neither a raised
timeout nor more than 15 GB of the 22 GB cap.

| export | roots | bytes | records | declarations | instructions:u | wall | peak RSS |
|---|---|---|---|---|---|---|---|
| `init.ndjson` | `Init` | 347 714 179 | 6 490 422 | 57 977 | 117.6 G | 11.8 s | 985 MB |
| `core.ndjson` | `Init Std Lean` | 747 809 047 | 13 229 044 | 163 396 | 248.7 G | 25.4 s | 2.20 GB |
| `mathlib.ndjson` | `Mathlib` | 6 067 502 440 | 107 794 484 | 691 128 | 2 067.3 G | 288.6 s | 14.7 GB |

Declarations by kind (the record census, `<name>.counts`):

| export | axiom | def | thm | opaque | inductive | quot |
|---|---|---|---|---|---|---|
| `init` | 7 | 15 189 | 41 896 | 266 | 615 | 4 |
| `core` | 7 | 78 903 | 79 196 | 2 463 | 2 823 | 4 |
| `mathlib` | 7 | 176 986 | 504 824 | 2 587 | 6 720 | 4 |

Four things in that table are worth keeping.  **`Init` alone is 58 k
declarations** — the "prelude" rung is not a toy but a third of core and a
twelfth of Mathlib, and it is the right rung for a first `check_decls` run.
**The seven axioms and the four `Quot` constants are the same in all three**
(`Classical.choice`, `Lean.ofReduceBool`, `Lean.ofReduceNat`,
`Lean.trustCompiler`, `Quot.sound`, `propext`, `sorryAx`; `Quot`, `Quot.mk`,
`Quot.lift`, `Quot.ind`), so the corpus exercises `StdAxioms`/`TrustAxioms`
identically at every scale and **no fixture taints a run** — con-leche reports
no taint-skip on any of the three.  **Mathlib is 691 128 declaration records in
6.07 GB**, against the 670 982 in 5.71 GB con-leche measured at Lean 4.29.1
(its task #199 ladder): +3 % in declarations and +6 % in bytes over four
toolchain releases, so its published Mathlib numbers and ours are comparable.
And **the exporter is not the bottleneck anywhere** — 288 s and 2.07 T
instructions for Mathlib, a sixth of what checking it costs.

**con-leche's baseline**, at the pinned submodule `3e00480`, `--verified`,
under `timeout 4h` and `ulimit -v 22000000`:

| export | jobs | verdict | instructions:u | wall | peak RSS |
|---|---|---|---|---|---|
| `init` | 1 | accepted 57 972 | 586.2 G | 59.4 s | 481 MB |
| `init` | 8 | accepted 57 972 | 587.5 G | 12.4 s | 711 MB |
| `core` | 1 | accepted 163 391 | 1 179.7 G | 149.6 s | 1.24 GB |
| `core` | 8 | accepted 163 391 | 1 182.7 G | 43.4 s | 1.39 GB |
| `mathlib` | 1 | accepted 691 123 | **12 816.5 G** | 1 228.4 s | 8.60 GB |
| `mathlib` | 8 | accepted 691 123 | 12 842.9 G | 337.0 s | 9.12 GB |
| `init` | default (96) | **exit 134**: `lean::exception: failed to create thread` | (54.8 G) | 15.5 s | 409 MB |

**That is the number con-ron has to beat: 12.8 T instructions:u and 8.6 GB
for Mathlib in the verified mode**, 18.5 M instructions per declaration
(core 7.2 M, init 10.1 M), 2.11 G per MB of stream.

**Why `instructions:u` is the measurement of record, demonstrated.**  Going
from one worker to eight moves the instruction count by **+0.21 %** (`init`),
**+0.26 %** (`core`) and **+0.21 %** (`mathlib`) while wall time falls 4.8×,
3.4× and 3.6× — the counter measures the *work*, and is immune both to the
thread count and to whatever else this shared machine is doing.  Wall time is
recorded beside it and believed to an order of magnitude, no further.

**The `--jobs` default cannot run under the cap, and that is a measurement,
not an assumption.**  con-leche's default is one worker per hardware thread;
this machine has 96, each worker reserves ~1 GiB of address space, and
`ulimit -v 22000000` is the house rule — so the default run aborts after 15 s
with `libc++abi: terminating due to uncaught exception of type
lean::exception: failed to create thread` (exit 134), on the *smallest*
export.  con-leche's own `scripts/selfcheck.sh` passes `--jobs=8` for exactly
this reason, so **`--jobs=8` is what the parallel row measures** (`JOBS_PAR`
is the knob), and the probe itself is a step of `corpus.sh` so the finding
stays reproducible rather than becoming folklore.

**The dumps.**  `con-ron-dump` writes the `List DeclC` con-leche's frontend
produced (§3.6, task #10); two flags now drop work in the order its cost
grows.  `--no-check` drops the two `checkDecls` runs and keeps the Lean round
trip; the new **`--write-only`** drops the round trip too *and* replaces the
buffered writer with `dumpStream`, which runs `wDecl` one declaration at a
time and flushes `WState.buf` after each.

| dump | flag | bytes | declarations | N | L | W | E | lines | parse | write | wall | peak RSS |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `init.decls` | `--no-check` | 165 127 796 | 58 002 | 68 651 | 581 | 3 | 6 137 917 | 6 328 142 | 1.3 s | 3.7 s | 18.7 s | 2.43 GB |
| `core.decls` | `--no-check` | 344 024 887 | 165 449 | 200 801 | 1 218 | 4 | 12 273 572 | 12 834 606 | 3.7 s | 8.8 s | 43.7 s | 4.78 GB |
| `mathlib.decls` | `--write-only` | 3 056 189 546 | 693 195 | 803 303 | 43 003 | 4 | 103 099 223 | 105 390 278 | 31.2 s | 104.2 s | 158.0 s | **12.52 GB** |

**`--write-only` alone was not enough, and the streaming writer is the task's
one real code change.**  The first Mathlib attempt — buffered writer, round
trip skipped — died at **`INTERNAL PANIC: out of memory`, 18.87 GB RSS,
136.7 s, zero bytes written**: 105 M lines of `Array String` plus the joined
copy do not fit beside a 103 M-node `Expr` DAG inside 22 GB.  Streaming keeps
one declaration's lines live at a time, at the cost of one buffered `putStr`
per declaration, and the result is **byte-identical** (checked against the
buffered writer on a fixture and on the whole 165 MB `init` dump, `cmp`-clean)
at **12.52 GB and no slower** (`init` write 3 662 ms streamed vs 3 664 ms
buffered).  A dump is therefore 0.46–0.50× its NDJSON at every scale, and
task #10's "1 s of writing per 100 MB of NDJSON" extrapolation held: 104 s for
6.07 GB.

**The Rust reader on all three** (`con-ron-dump-check --roundtrip`, task #19):

| dump | verdict | parse | re-dump | wall | peak RSS |
|---|---|---|---|---|---|
| `init.decls` | DAG exact, round trip EXACT | 1.26 s | 3.56 s | 6.0 s | 1.02 GB |
| `core.decls` | DAG exact, round trip EXACT | 3.11 s | 7.94 s | 13.9 s | 2.08 GB |
| `mathlib.decls` | **DAG exact, round trip EXACT** | 31.5 s | 109.6 s | 178.9 s | 17.46 GB |

So **the format survives Mathlib**: 693 195 declarations and 103 099 223
interned expression nodes read by the Rust reader with the distinct-`Rc`-node
count equal to the file's record counts (task #19's DAG property, now at 310×
the fixture corpus's 332 140 nodes), and the re-dump byte-identical — which is
the stronger statement, because `--write-only` gave up the *Lean* round trip
on this dump and the Rust one replaces it.  Parsing runs at **131 MB/s** when
the reader is not also holding a re-dump (23.3 s for the 3.06 GB dump, in the
parse-only run this table's 31.5 s replaced) and at 97 MB/s when it is — task
#19's fixture-scale rate either way, so reading will not bound the
differential runner.
Peak RSS is the one number close to the wall: 17.46 GB of the 22 GB cap, ~5.7×
the dump, which is why `corpus.sh` takes `RT_MAX` (default 4 GB of dump) and
falls back to parse + DAG census above it.

**Three small facts the corpus pinned, for whoever wires `check_decls` to it.**

1. **Dump declarations = con-leche's accepted count + the in-process model's
   generated records**, exactly, at all three scales: 57 972 + 30 = 58 002,
   163 391 + 2 058 = 165 449, 691 123 + 2 072 = 693 195.  A Rust verdict line
   that compares *counts* with con-leche's must add the models back, and
   `dumpStream`'s `nD` is the right number to compare against `check_decls`.
2. **All three frontend rewrites fire at Mathlib scale, and only there in
   force**: 49 inductive blocks modelled in-process (1 in `init`, 45 in
   `core`), 62 projection functions of non-direct structure-likes rewritten to
   recursor form, and 2 declarations hoisted ahead of the pinned Nat
   operations (`Nat.mul._f`, `Nat.mul`).  That is §3.6's argument in numbers:
   a Rust reimplementation of the frontend would have to reproduce all three
   before the first Mathlib verdict could be compared, and the dump means it
   does not have to.
3. **`P = 0` still holds at Mathlib scale** — 803 303 names, 43 003 levels,
   4 propwhens (!), 710 364 constvals, 10 350 recrules, 6 846 indcaps, 23 988
   block `ConstantInfo`s and **no `ProjTable` record at all**, as on the 348
   fixtures (task #10's surprise 3, task #19's `P = 0`).  The four propwhens
   are the whole of Mathlib's zero-ness data: `PropWhen` interning is doing
   its job, and the pin-set work (task #22) is unaffected by scale.

**Left for next time.**  `check_decls` (P1.7) is the missing half: the moment
it runs, `corpus.sh` gains a fifth step and `baseline.md` a con-ron column.
The corpus deliberately has no *slice* rung between `core` (748 MB) and
`mathlib` (6.07 GB) — con-leche's ladder has one and ours can be cut the same
way if Mathlib turns out too coarse for bisecting a divergence.  And nothing
here runs `--trusted`: the theorem is about `--verified`, so that is the only
mode measured.

**Time.** ~65 min wall, almost all of it waiting: the Mathlib export 4.8 min,
con-leche's seven runs 31 min (Mathlib at `--jobs=1` alone is 20.5 min), the
three dumps 3.7 min (plus the 2.3 min the buffered attempt burned before its
panic), the Rust reader 3.3 min, and the two Lean builds (`con-leche` and
`con-ron-dump`, a few minutes each on top of the main tree's copied `.lake`)
that must not run *concurrently* — they share the con-leche package's build
directory, and the first attempt at building both at once died in `clang` with
a half-written `.o`.  One other stumble worth recording: editing
`scripts/corpus.sh` while a run of it was in flight broke that run — bash
reads a script incrementally.  `scripts/gates.sh`: all 6 OK.
### Task #28 — `Installed.lean`; the checker runs the fixture corpus (2026-09-12, Opus under Fable)

P1.7, and with it the last implementation file of `ConLeche/Cached/`:
`cached/installed.rs` (`ConLeche/Cached/Installed.lean`, 522 lines) — **the
declaration fold `check_decls`** — plus the driver that runs it on a dump
(`crates/con-ron-dump/src/bin/con-ron-check.rs`, an unverified binary) and the
differential sweep that compares every fixture's verdict with con-leche's
pinned expectation (`scripts/diff-fixtures.sh`).  The port now answers
`accepted` / `rejected` / `declined` on real export streams, and **290 of the
315 fixtures that have a declaration list give con-leche's exit code** — the
other 25 in two classes, both already-recorded deviations, neither a wrong
verdict (§5).

#### 1. The fold, and the twelve declarations that are evidence

`checkDecls` is two phases (con-leche task #253's install/check seam): phase A
folds `annotDeclStep` — annotate-and-install for `defn`/`opaque`, install **by
statement** for `thm` (its header alone is annotated; phase A never enters a
theorem's body), the ordinary `checkDeclStepC` for everything else, including
the pinned `Nat`-operation and `reduce*` branches whose checks are not
separable from their installs — and records a `PendingCheck` per separable
declaration; phase B checks each record against the prefix view
`fe.restrictTo pc.vis` **from a fresh `CState`**.  All of that is ported: nine
cited blocks, 24 functions.

**Twelve of the file's 21 declarations are deliberately not ported**, and the
module note says so item by item: `InstallRun`, `InstalledEnv`(`.env`),
`GroupChecked`, `FullyChecked`(`.assemble`/`.env`), `checkRecord`,
`CheckedRecord`, `RecordResult`, `checkRecordResult`, `collectChecks`, plus
the ten theorems.  Every one of them is indexed by a `Prop` or returns one
(`PLift (GroupChecked …)`), i.e. it is the *parallel driver's evidence
plumbing*: `checkRecord` computes `checkPending` and throws the value away for
a proof, `collectChecks` walks a table of such proofs.  Rust has no `Prop`; and
the thing they decide — "the first failing record in fold order" — **is**
`checkPendingList`, which is ported and is what `check_decls` runs.  A parallel
phase B (P4) re-derives the plumbing in the Rust world against `check_pending`;
the verdict it must agree with is this file's.  So `Cached/Installed.lean` reads
**9/21** in the ledger and is complete.

Five deviations, all in the module note: the accumulator is a flat 3-tuple with
`u64` positions; **the index is threaded by value** — a copy is not an option,
because `fenv::dup` rebuilds the whole index and a copy per record would make
phase B quadratic where con-leche's `restrictTo` is an `O(1)` field update, so
`check_pending` takes the index at the installed bound, restricts it, and hands
it back there (`checker::check_div_mod_pin`'s shape); the two folds are index
recursions (§3.4); `check_decls` takes the pin list (§2); the message strings
are `parsed_c`'s.

#### 2. `check_decls` takes the pins, and the threading is still owed

Per §3.6's task-#22 ruling the signature is final:

```rust
pub fn check_decls(mode: &CheckMode, pins: &Vec<NatOpPinSet>, ds: &Vec<DeclC>)
    -> Result<Env, (CheckError, u64)>
```

(`&Vec` and not `&[_]`: the crate's convention, 627 sites to 7.)  The parameter
is **not yet threaded** to `checker::check_div_mod_pin_loop`, which still reads
`kernel::nat_op_pins`' empty stub.  The chain runs through ten functions in
`parsed_c` and `kernel::checker`, but the decisive point is that there is
**nothing to thread yet**: con-leche's variants live in
`vendor/con-leche/pins/*.json` in the `con-leche-natop-pins/3` share-table
format, 660 KB each, and neither a Rust reader for that nor a Lean dumper
emitting them in a format the task-#19 reader understands exists (task #22's
and task #29's work).  So the flag exists (`con-ron-check --pins FILE`), warns
loudly, and runs the empty list; the API does not move when the data arrives.
This costs 17 fixture verdicts (§5b).

#### 3. `con-ron-check`: con-leche's verdict line, and the driver rule above the fold

```text
con-ron-check [--verified|--trusted] [--pins FILE] [--taint-skipped N]
              [--stats] [--quiet] FILE.decls
```

`Main.lean:48-51`'s exit codes exactly (`notImplemented` 2, `invalid` 1,
`internal` 3, accept 0) and `OVERVIEW.md` §0's verdict words; the accept line on
stdout, everything else on stderr, each line naming the mode as con-leche's do,
and a failure carrying the **fold position** `check_decls` returns beside the
error (`Main.lean:786-788` prints it too; the expectation files do not record
it, so nothing compares it).  The fold runs on a thread with a **1 GiB stack**,
which is what con-leche reserves per checking worker.

Two rules of con-leche's driver live in the binary and **must not** live in the
core:

* **The taint-skip decline** (`Main.lean:637-645,749-753`): a clean fold over a
  stream whose frontend skipped declarations for a tolerated axiom is still a
  decline — "uses of tolerated axioms are never accepted".
  `res.taintSkipped.size` is frontend state and is not in the dump (task #10's
  surprise 9), so it is the `--taint-skipped N` parameter, and
  `diff-fixtures.sh` supplies it for the three fixtures that have skips.  It is
  load-bearing: `tolerated_axiom_use` and `taint_skip_continue` *accept* the
  fold and are pinned at 2, so without the rule they would be mismatches.
  (`sorry_use`, the third, currently declines earlier inside the fold, for the
  empty pin table.)
* **`N` counts declaration records.**  con-leche subtracts its built-in prelude
  and the generated inductive model records from `decls.size`; the dump has
  already absorbed the prelude, so the two `N`s differ by it.  Nothing compares
  them — the expectation files pin the exit code alone.

`--stats` prints the 14 `CState` map sizes after phase A and the record count,
by running the phase boundary explicitly; that path *is* `check_decls`' body, so
the flag changes no verdict.

#### 4. `scripts/diff-fixtures.sh`

For every line of `vendor/con-leche/tests/{arena,e2e,annot}-expected.txt`
("`<exit-code> <fixture>`", `#` comments — the exit code is the *whole*
expectation; there is no declaration name and no fold position in them) it finds
the dump task #10's sweep wrote
(`_tmp/dump-fixtures/<suite>/<label with / as _>.decls`), runs `con-ron-check`,
and compares the exit code.  `--trusted` applies `tests/trusted-expected.txt`'s
overrides the way `tests/arena.sh` does; `--only=REGEX` narrows;
`--timeout=SECS` bounds each run; `--stats` passes the flag through.  It runs
`dump-fixtures.sh --no-check` itself if the dumps are missing, logs every run to
`_tmp/diff-fixtures.log`, prints one line per mismatch with the verdict line
that produced it, and exits non-zero on any mismatch or timeout.  Like
`dump-check-fixtures.sh` it is **not** in `scripts/gates.sh`: it needs the Lean
build and the arena tarball (task #19's reasoning).

A fixture with no dump is **skipped with a note**: those are the 33 streams
con-leche's own frontend declines or rejects before the fold (task #10), so there
is no declaration list and nothing about the port is being tested.

#### 5. The run, and the three divergence classes it found

`scripts/diff-fixtures.sh --timeout=60`, `--verified`, all 348 fixtures:
**290 agree, 17 differ, 8 do not finish, 33 skipped**, 485 s wall (480 s of it
the eight that do not finish).  Every one of the 25 is one of two known
deviations, and **no fixture gives a wrong verdict for any other reason**: no
`good` stream is rejected, no `bad` stream accepted, every reject lands on
con-leche's exit code.

**(a) A port bug, found and fixed: the `.proj` clause typed nodes through
`ProjEntry.typeAt`.**  `tests/e2e/proj_share.ndjson` — raw `.proj` nodes on a
structure whose parameter is a 27-node DAG with a 2^27-node tree — did not
finish in 300 s; con-leche accepts it in milliseconds.  `perf` put 15 % of the
cycles in `expr_ops::instantiate_list`, the *spec* walk, under a storm of
`expr::app` allocations, which named the site exactly: task #26 had flagged it
as an **owed reconciliation** —

> `core_k::proj_entry_type_at` carries this same citation and is what
> `core_k::infer_proj_at` — the shared `.proj` clause of both inference bodies —
> still calls.  Retargeting that one call site here is a two-line change, but it
> would make `kernel::core_k` depend on `crate::cached` …

The port's `instantiate_list_go` defers to the spec at a `.bvar` (faithfully:
`ExprOps.lean` does), and the spec re-traverses the replacement, so every
occurrence of the subject and of each parameter came back as a fresh *tree* copy
of a DAG — con-leche's own "affine frontier" out-of-memory, and the reason its
executed clause calls `typeAtI`.  The fix keeps `core_k` free of
`crate::cached`: `cached::core_c` gets the two twins the cached lane needs,
`infer_proj_at_i` and `proj_type_at_checked_i` (cited
`CoreC.lean:1292-1389 inferBodyI` + `Core.lean:2039-2204 inferBody` +
`ExprOpsC.lean:623-642 ProjEntry.typeAtI`), identical to `core_k`'s except that
the type is `expr_ops_c::proj_entry_type_at_i`, and `infer_proj_i` calls them.
That is what `inferBodyI` itself does, so the fix **removes** a memo-policy
deviation rather than adding one.  `proj_share`: 300 s+ → **1 ms**, accepted.
`core_k::infer_proj_at`/`proj_type_at_checked` stay as the pure lane's, which is
what `checkDeclsPure` and the `model_exists` capstone need.

**(b) The `Nat`-operation pin table is empty — 17 fixtures.**  All 17
mismatches are the same line, `declined: unsupported Nat.div/mod spelling: no
pin variant matched`, from `kernel::nat_op_pins`' stub (task #24's stub 1):
`nat_div_declined`, `nat_divmod_ok`, `nat_gcd_ok`, `nat_land_ok`,
`nat_land_cone`, `nat_lor_ok`, `nat_xor_ok`, `nat_shiftleft_ok`,
`nat_shiftright_ok`, `nat_log2_ok`, `natop_order`, `natop_before_eq`,
`natop_before_ble`, `let_rec_rhs`, `str_lit`, `str_proj`,
`presieve_ofarrows_cone` — all pinned at 0, all declined at the record that
defines `Nat.div`.  This is **data, not code**: §3.6 ruled the pin sets runtime
data precisely because generating them as Rust overwhelms rustc and Charon, and
the decline is the verdict con-leche itself gives a stream matching no variant,
so it is sound for the accept direction (§1).  It closes when a pins dump and
its reader exist (§2).

**(c) `beq` has no pair memo — the eight tower fixtures are the measurement
§3.2 asked for.**  `tower_thm`, `tower_struct`, `tower_proj`,
`tower_usedlater`, `tower_beqpair`, `tower_recfield`, `tower_mutual` and
`tower_nested` do not finish in 60 s.  `perf` puts **72 % of the cycles in
`expr::beq_go` and 28 % in `prop_when::beq`**, with no allocation traffic at
all: a memo-free structural descent over two structurally equal,
pointer-distinct depth-60 towers, i.e. `O(tree)` on 2^60 nodes.  The shared-tower
fixtures of the same family — `dag_tower`, `dag_tower_unfold`, `budget_model`,
`budget_block` — all accept, because there the pointer fast path hits; the eight
that do not finish are the ones where an install rebuilds the tower (a field
type, a recursor motive) and the comparison is then between two distinct copies.
These fixtures exist upstream for exactly this — "what they gate is that every
walk the frontend and the install run stays DAG-safe, since an unmemoized one
does not finish on such a tower" (`tests/e2e-expected.txt:1147-1154`) — and
con-leche's `beqBudget` note says why its own descent is safe: "beyond the
budget the term is big enough that `O(tree)` is the real risk, and from there on
every completed pair is recorded" (`Kernel/Expr.lean:767-773`).

§3.2's decision not to port `BeqMap`/`beqBudget` was explicit and conditional:
*"If measurement shows the pair memo is needed, it is added as one opaque
function with a one-paragraph trust argument."*  **The measurement is now in,
and the work is P1.8's, not this task's**, for a concrete reason: the memo
cannot be written inside the Aeneas subset — it is keyed by *addresses*, and a
structurally keyed pair memo would need structural key equality, which is the
thing being computed — so §3.2's route is an opaque function, i.e. a **fifth
external hole**, where this task's standing gate is that the templates stay
exactly the four `Rc` axioms and the `Rc` type.  Adding that hole is a design
step with its own trust argument and its own gate change.  (The other §3.1-licensed
route, hash-consing, would make `beq` `O(1)` outright and is the same size of
decision.)  Until one of them lands, a stream with a rebuilt shared tower deeper
than ~30 does not finish; nothing else in the corpus is affected.

#### Numbers

Measured against this branch's merge base (`f69be81`, i.e. after task #27), not
against the numbers other worktrees' entries quote.

| | |
|---|---|
| Lean ported: `Cached/Installed.lean`, 9 cited blocks of 21 declarations | 522 raw / 223 definitional / **109 translated (48 %)** — the other 114 are the twelve `Prop`-indexed evidence declarations and the ten theorems (§1) |
| `src/cached/installed.rs`, extracted part (raw / code) | 736 / **470** (4.3× the Lean code: the `do`-block splits, the tuple plumbing and the copies Lean's sharing gives away) |
| `src/cached/installed.rs`, `#[cfg(test)]` part (6 tests) | 210 / 163 |
| `src/cached/core_c.rs` | +100 raw (the two `.proj` twins, §5a) |
| `crates/con-ron-dump/src/bin/con-ron-check.rs` (unverified) | 365 |
| `scripts/diff-fixtures.sh` | 149 |
| generated `Types.lean` | **736 — unchanged**; `installed` declares no type (the three seam records are `parsed_c`'s; they only *move* in the file, ahead of their new user) |
| generated `Funs.lean` | 50 017 → **50 944** (+927) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 — **unchanged**, still exactly the four `Rc` axioms and the `Rc` type |
| `partial_fixpoint` | 406 → **408** (+2: the two index recursions, `annot_decl_fold_from` and `check_pending_list_from`) |
| `mutual` blocks in `Funs.lean` / `Types.lean` | **13 / 3 — unchanged**; the fold is tail calls, not recursion |
| `charon cargo --preset=aeneas` | **3.9 s** |
| `aeneas -backend lean -split-files -loops-to-rec` | **39.7 s**, **zero errors, zero warnings** (first run) |
| `cd proof && lake build` | **2 115 jobs, zero errors**; `ConRon.Generated.Funs` alone **101 s** |
| `cargo test` | **167/167** green (153 unit + 4 integration + 10 in `con-ron-dump`), warning-free at `-D warnings` |
| `scripts/provenance.py check` | green — 1 478 items, 1 592 citations (was 1 452 / 1 562) at pin 3e004805 |
| `scripts/provenance.py coverage` | **851/1006 (84.6 %)**, from 843/1006 (83.8 %): `Cached/Installed.lean` 1/21 → **9/21** |
| `scripts/diff-fixtures.sh --timeout=60` | 348 fixtures: **290 agree, 17 differ (§5b), 8 do not finish (§5c), 33 skipped**, 485 s |

`scripts/lint-rust-style.sh crates/con-ron-core/src` clean; `scripts/gates.sh`
all 6 OK.  The progress lines it prints:

```
Verified core (ConLeche/Kernel, ConLeche/Cached)           to translate  13987  translated  13049 (93%)  verified    498 (3%)
Cherries (ConLeche/Frontend without Scan/Equiv, Main.lean) to translate   8132  translated      0 (0%)  verified      0 (0%)
Rust core 40596 lines (1372 fns) | unverified crates 3003 | generated Lean 51853 | proofs 11247 (121 _refines) | pin 3e004805
```

**Every implementation file of `ConLeche/Kernel/` and `ConLeche/Cached/` that
the fold reaches is now ported.**  What is left of the 15 % uncovered is
specification (`*MemoInv`, `*_spec`), `Repr`/`toString` rendering, the raw
basis pins that the generated tables replace, and the frontend (P4).

#### Tests

Six new unit tests in `cached::installed`, and every one of them is built out of
**sorts alone**: in the empty environment `Sort 0 : Sort 1` is the only
judgement available — an axiom would need one of con-leche's pins
(`checkAxiomDeclC`) and an honest proposition an inductive block — which is
itself a reminder of why the fixture corpus is the real test.

* the empty stream accepts at the empty environment (both folds run zero steps);
* `def b : Type := Prop`, `def c : Type := b` accepts, the second reading the
  first through the prefix view, and the environment holds them newest-first;
* **phase B is what catches a bad definition**: `def c : Prop := Prop` passes
  phase A (the value is annotated and the constant pushed) and is rejected in
  phase B at its **fold position**, 1 — not at its index among the records;
* a duplicate fails in **phase A**, at the fold position of the second one;
* **a theorem installs by statement**: `theorem t : Type := b` passes phase A
  (the header alone is annotated, the raw value stored and never entered) and is
  rejected in phase B, where a theorem's statement is tested for being a
  proposition;
* **the records carry the position and the bound**: three definitions give
  records at positions 0, 1, 2 and bounds 0, 1, 2, so a record never sees the
  constant it is about to justify, nor any later one.

Plus the corpus itself — 290 fixture verdicts, the first end-to-end test the
port has had.

#### Left for next time

* **The `beq` pair memo** (P1.8, §5 item 8): eight tower fixtures, a fifth
  external hole with a trust argument, or hash-consing; a design step (§5c).
* **The pin data** (task #22 / task #29): a dump of `natOpPinSets` the task-#19
  reader can read, then `con-ron-check --pins` and the threading of
  `check_decls`' `pins` parameter through `parsed_c`/`kernel::checker` to
  `check_div_mod_pin_loop` — 17 fixtures (§5b).
* **Mathlib scale** (P1.8 proper): the corpus is 12 397 declarations across 315
  streams and the whole sweep is 5 s of checking outside the eight blow-ups;
  `con-ron-check --stats` is the instrument, and a Mathlib export is the next
  input.
* A `--trusted` sweep: the mode and its expectation overrides are implemented
  and spot-checked, but the full sweep has not been run.

### Task #31 — Nat-op pins as runtime data, end to end (2026-09-12, Opus under Fable)

P1.8's data half.  §3.6 ruled the `Nat`-operation pin sets *runtime data* in
task #22, and task #28 left three halves missing: no dump con-leche could
write, no Rust reader, and `check_decls`' `pins` parameter not threaded to the
pin loop.  All three land here, and **the 17 fixtures that declined for the
empty pin table now give con-leche's exit code**: 290 agree → **307**, 17
differ → **0**.

#### 1. A sibling format, `con-ron-pins/1`, not a record of `con-ron-decls/1`

The choice was this task's to make, and it is a sibling file
(`proof/ConRon/Dump/FORMAT.md` §7).  Three reasons, in order of weight:

* **A pin variant describes a toolchain, not a stream.**  The same three
  variants apply to all 348 fixtures.  As a record of the declaration dump
  their 26 512 `E` records would be copied into *every* fixture dump — 348 ×
  532 KB of identical bytes — and re-parsed before every verdict, including on
  the 331 streams that never mention `Nat.div`.
* **The driver already takes them separately.**  `con-ron-check --pins FILE`
  is task #28's flag; a file argument is exactly what it wants.
* **`con-ron-decls/1` does not move.**  Task #10's byte-identity round trip
  over the whole corpus stays valid as it stands, and so do the 315 committed
  dumps.

What the two files share is the *record grammar*, verbatim: the same
`E`/`N`/`L`/`W` records, the same interning, the same escape, the same
"ids are dense and backward-only" invariant, the same footer rule.  Both
readers are therefore **one function with a payload flag** — `RState.pins` in
Lean, `Reader::pins` in Rust — which swaps the payload record (`S` for `D`)
and what the footer counts, and makes the *wrong* payload record an error
rather than a silently ignored line.  An `S` record carries no id, for `D`'s
reason: the record **is** the payload, and its position in the file is its
position in `natOpPinSets`, which is the order the install gate tries the
variants in.

```
S <len> <text> <expr>×8 (<k> <expr>*)×8
    toolchain  the eight pins  the eight proof lists
```

| what | where |
|---|---|
| writer | `ConRon/Dump/Write.lean` (`pinsHeader`, `wPinSet`, `dumpPins`) |
| Lean reader | `ConRon/Dump/Read.lean` (`RState.pinSets`/`.pins`, the `S` arm, `parsePins`) |
| harness | `ConRon/Dump/Pins.lean` + `[[lean_exe]] con-ron-dump-pins` |
| Rust reader | `crates/con-ron-dump/src/lib.rs` (`parse_pins`; `run_lines` is now shared with `parse_decls`) |
| Rust writer | `crates/con-ron-dump/src/write.rs` (`dump_pins`) — for the byte-identity test |
| consumers | `con-ron-check --pins FILE`, `con-ron-dump-check --roundtrip` |

#### 2. The threading, and the deleted stub

`kernel/nat_op_pins.rs`' `nat_op_pin_sets()` stub (task #24's stub 1) is
**gone**; the module declares the record and nothing else — §3.4 forbids the
global and the data is not code.  `pins : &Vec<NatOpPinSet>` now runs,
immediately after `mode`, through the whole chain:

```
installed::check_decls → annot_decl_fold_from → annot_decl_step → annot_step_c
  → annot_step_{defn,opaque,other}_c → parsed_c::check_decl_step_c
  → check_decl_c → check_defn_decl_c → check_defn_pins_c
  → checker::check_defn_pins → check_defn_div_mod_pin → check_div_mod_pin
  → check_div_mod_pin_loop          (variants := pins)
```

and through the pure lane too (`checker::check_decl`, `check_defn_decl`,
`check_decls_pure{,_from}`), which `checkDeclsPure` and the `model_exists`
capstone need.  Fourteen signatures grew one argument; **no body moved**.  The
deviation note §3.6 asks for sits on `check_div_mod_pin`, where the global was
read, and is referred to from each function above it: con-leche bakes
`natOpPinSets` (`Kernel/NatOpPins.lean:61`) into `checkDivModPin`, the port
takes it as a parameter because the table cannot be generated as Rust
(task #22: Charon OOMs) and does not have to be — every pin is re-checked by
`isDefEq` against the stream's own stored value and every certificate against
the hand-pinned `div_mod_cert_stmts`, so a wrong list costs a decline and
never an accept.  The upstream ask is unchanged: `checkDecls mode pins ds`.

#### 3. The dump, measured

`lake exe con-ron-dump-pins _tmp/dump-fixtures/pins.dump`:

| | |
|---|---|
| `S` records | 3 — `lean4:v4.33.0`, `lean4:v4.34.0-rc2`, `lean4-nightly:nightly-2026-09-10` |
| `N` / `L` / `W` / `E` records | 200 / 3 / 1 / **26 512** — task #22's interned census, to the node |
| proof blobs per variant | 3 div, 3 mod, 2 each for `gcd`/`land`/`lor`/`xor`/`shiftLeft`/`shiftRight` |
| lines / bytes | 26 721 / **532 456** |
| Lean write / read-back | **10 ms** / **18 ms**; round trip exact (structural through `Expr.beqMemo`, and a byte-identical re-dump) |
| Rust `parse_pins` / `dump_pins` | **20.9 ms** / 37.5 ms; the re-dump is **byte-identical to Lean's file**, and the DAG is **exact** (26 512 distinct heap nodes for 26 512 `E` records) |
| `con-ron-check --pins`, per run | **5 ms** (265 of 288 runs; 6 ms ×16, 7 ms ×7) |
| two consecutive `con-ron-dump-pins` runs | byte-identical (the format is deterministic, §1) |

The DAG check is where the pins earn their own census function
(`dag::census_pins`): as a *tree* the v4.33.0 variant is 5.1 M nodes against
20 183 in the DAG (task #22), so a reader that lost the sharing would be
caught here and nowhere else — a byte-identical re-dump would not catch it,
because the writer re-interns by value.

5 ms per run is 3 % of the 315-fixture sweep's checking time; it is paid once
per `con-ron-check` invocation, not per declaration, and it is why the
per-fixture dumps stay pin-free (§1).

#### 4. The sweep

`scripts/dump-fixtures.sh` writes the pin dump once, up front, and **fails the
run** if it cannot: every verdict below would then be taken against the wrong
pin list.  `scripts/diff-fixtures.sh` passes `--pins $OUT/pins.dump` to every
`con-ron-check` run, and `--no-pins` reproduces task #28's numbers.

```
scripts/diff-fixtures.sh --timeout=60, --verified, all 348 fixtures:

diff-fixtures (--verified, with pins): 348 fixtures, 307 agree, 0 differ,
  33 skipped (no declaration list), 8 timed out, 490s
```

**The 17 are closed.**  `nat_div_declined`, `nat_divmod_ok`, `nat_gcd_ok`,
`nat_land_ok`, `nat_land_cone`, `nat_lor_ok`, `nat_xor_ok`,
`nat_shiftleft_ok`, `nat_shiftright_ok`, `nat_log2_ok`, `natop_order`,
`natop_before_eq`, `natop_before_ble`, `let_rec_rhs`, `str_lit`, `str_proj`
and `presieve_ofarrows_cone` all accept, as con-leche does.  The only streams
that still print "no pin variant matched" are the seven `nat_*_perturbed`
ones, **pinned at 2 precisely because no variant may match them** — so the pin
loop's `[]` arm is still exercised, on the streams it exists for.

The 8 remaining non-finishers are the `tower_*` fixtures of task #28 §5c —
`beq` with no pair memo, untouched by this task, and still the *only* thing in
the corpus that does not finish.

One knock-on worth recording: `sorry_use` used to decline *inside* the fold
for the empty pin table, so only two of the three taint fixtures actually
depended on the driver's taint-skip rule.  Its fold now accepts and the rule
is what declines it — all three do, which is `diff-fixtures.sh`' comment
corrected.

One infrastructure fix the concurrent worktrees forced: `diff-fixtures.sh`
reads each run's exit code back out of its log, so two sweeps sharing one
`_tmp` (sibling git worktrees do, when `_tmp` is a symlink) can each read the
other's line.  The log path is now `LOG`-overridable and the numbers above are
from a run with a private one.

#### Numbers

| | |
|---|---|
| `kernel/nat_op_pins.rs` | the stub deleted, the record kept: 64 lines, all of it the record and the parameter note |
| threading | 14 functions in `kernel/checker.rs`, `cached/parsed_c.rs`, `cached/installed.rs`, one parameter each |
| `proof/ConRon/Dump/Write.lean` / `Read.lean` | +63 / +56 |
| `proof/ConRon/Dump/Pins.lean` (new) | 122 |
| `proof/ConRon/Dump/FORMAT.md` | +71 (the §7 specification) |
| `crates/con-ron-dump` (unverified) | +218 `lib.rs` (reader + 3 tests), +72 `write.rs`, +32 `dag.rs`, +86 `con-ron-dump-check.rs`, +38 `con-ron-check.rs` |
| generated `Types.lean` | **736 — unchanged**; `NatOpPinSet` only *moves*, ahead of its new users |
| generated `Funs.lean` | 50 944 → **50 970** (+26: fourteen signatures one argument wider, one stub gone) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 — **unchanged**, still exactly the four `Rc` axioms and the `Rc` type |
| `partial_fixpoint` | **408 — unchanged** |
| `mutual` blocks in `Funs.lean` / `Types.lean` | **13 / 3 — unchanged** |
| `charon cargo --preset=aeneas` | **3.9 s** |
| `aeneas -backend lean -split-files -loops-to-rec` | **33.2 s, zero errors, zero warnings** |
| `cd proof && lake build` | **2 115 jobs, zero errors** |
| `cargo test` | **170/170** green (153 unit + 4 integration + 13 in `con-ron-dump`), warning-free at `-D warnings` |
| `scripts/provenance.py check` | green — 1 546 items, 1 647 citations at pin 3e004805 (was 1 478 / 1 592 before task #30's and this task's work) |
| `scripts/provenance.py coverage` | **851/1006 (84.6 %) — unchanged**: the stub's citation goes, the record's stays |
| `scripts/diff-fixtures.sh --timeout=60` | 348 fixtures: **307 agree, 0 differ, 8 do not finish (task #28 §5c), 33 skipped**, 490 s |

`scripts/lint-rust-style.sh crates/con-ron-core/src` clean; `scripts/gates.sh`
all 6 OK.  The progress lines it prints:

```
Verified core (ConLeche/Kernel, ConLeche/Cached)           to translate  13987  translated  13049 (93%)  verified    498 (3%)
Cherries (ConLeche/Frontend without Scan/Equiv, Main.lean) to translate   8132  translated      0 (0%)  verified      0 (0%)
Rust core 40655 lines (1371 fns) | unverified crates 3421 | generated Lean 51879 | proofs 11247 (121 _refines) | pin 3e004805
```

**`differ` is now zero.**  For the first time every fixture that has a
declaration list and finishes gives con-leche's own exit code.

#### Tests

* Three new Rust unit tests in `con_ron_dump` (10 → 13): a two-variant pin
  dump round-trips *and* re-dumps byte-identically *and* keeps its sharing
  (`dag::census_pins` against the record count); the empty pin list is
  `"con-ron-pins/1\nend 0\n"`; and the two payloads do not mix — an `S` in a
  declaration dump, a `D` in a pin dump, each reader on the other's header,
  and a footer count that disagrees, all rejected with the line number.
  (`unwrap_err` is unavailable — neither `DeclC` nor `NatOpPinSet` derives
  `Debug`, §3.4 — so the tests go through a small `*_err` helper.)
* `con-ron-dump-check` now reads a `con-ron-pins/1` file too, recognised by
  its header: that is the cross-check of the Rust reader against Lean's writer
  on the real 532 KB file, and it is exact.
* `lake exe con-ron-dump-pins` is the Lean round trip over
  `ConLeche.natOpPinSets` itself, which is the "check equality with the value"
  half.
* The corpus: 307 fixture verdicts, 17 of them new.

#### Left for next time

* **The `beq` pair memo** (§5c): the eight tower fixtures are now the *only*
  divergence class left — a fifth external hole with a trust argument, or
  hash-consing.  A design step.
* **The upstream ask** is now concrete and minimal: `checkDecls mode pins ds`
  with the shipped `checkDecls mode ds := checkDecls mode natOpPinSets ds`,
  and `model_exists` parametric in `pins`.  Until it lands the pin-loop
  refinement carries `abs pins = natOpPinSets` as a hypothesis (§3.6) and the
  corollary is conditional.
* **A freshness gate** in the spirit of con-leche's `tests/pindump.sh`:
  `con-ron-dump-pins` prints the per-variant blob counts and the record
  census, which is the datum such a check would compare after a submodule
  bump.
* A `--trusted` sweep with the pins in, and Mathlib scale (P1.8 proper).
### Task #30 — The `beq` pair memo, hash-keyed and pointer-verified (2026-09-12, Opus under Fable)

P1.8, and the cash-in of §3.2's standing conditional.  Task #28 measured what
that section asked for — eight "tower" fixtures do not finish in 300 s, 72 % of
the cycles in `expr::beq_go` — and expected the fix to cost a **fifth external
hole**, because con-leche keys its structural-equality memo by *addresses*,
which Aeneas cannot model.  It does not: the memo landed as ordinary verified
Rust, and the external holes are still exactly the four `Rc` axioms.  The eight
fixtures now accept in under a second, the whole 348-fixture sweep runs in
**4 s**, and `Init`-scale cost is unchanged.  Two bugs were found on the way,
both of the "the port calls the *spec* where con-leche calls the memoised
twin" class that task #28 §5a opened.

#### 1. The design: key by the hash words, verify by identity

con-leche's memo (`Kernel/Expr.lean:739-949`) keys a table by a mix of the two
objects' *addresses* and then verifies the candidate entry by **pointer
identity** on both components, storing only pairs a completed descent proved
equal.  The port keeps every part of that except the key:

* `expr::beq_key(ha, hb) = ha ^^^ (hb *w 0x9E3779B97F4A7C15)` — the cited
  `beqKey` with the two **stored hash words** (a field read each, §3.2's packed
  `data`) in place of the two addresses, and without the `&&& 0x3FFF…` mask
  that exists so Lean gets a tagged `Nat`.  Any mixing would do: the key is a
  *filter*, and a collision between distinct pairs costs an entry, never an
  answer.
* `expr::BeqMap = ron::HashMap<u64, (Expr, Expr)>` — one slot per key, last
  write wins, as the cited `Std.HashMap` is; `ron::HashMap` is the crate's own
  table, verified at task #16.  `expr::EqPair = (Expr, Expr)` is con-leche's
  entry minus the two addresses (the key does that job now) and minus the
  proof (Rust has no `Prop`).
* `expr::probe_hit` reads the slot and tests **`ptr_eq` on both components**,
  which is the cited `probeHit`'s verification step verbatim; holding the pair
  is what keeps the two `Rc`s alive and their identity theirs.
* the write-back is con-leche's `finish`: a completed `true` at a
  `beq_recursive` node, under that node's own key.  A `false` aborts the
  comparison at every level, so **only proved-equal pairs are ever stored** —
  the official kernel's `expr_eq_fn` rule.

**The trust argument** (§3.2's paragraph, and the module note of
`kernel/expr.rs`).  In the *model* `ptr_eq` is `false`, so `probe_hit` is
`false` at every probe whatever the table holds: the memo is state that is
written and never read, and the model's `beq` is the plain structural descent
`Refine/Expr.lean` proves exact.  In the *binary* a probe hits only when the
stored pair is the very two objects being compared, and that entry was written
by a completed `true` of this same deterministic walk on those same two
objects; so a hit repeats an answer the walk has already produced for that
pair, and binary and model agree.  It is the same shape of argument as the
pointer fast path's, and it needs no new axiom — which is the whole point of
keying by the hash words rather than by addresses.

**`beqBudget` is not ported**, and the numbers below are why.  con-leche
materialises the table only after 4 096 nodes because in Lean the allocation
and its reference-count traffic cost "a third of `init-prelude`" on the
comparisons that the pointer test or the computed word decides outright.  Here
`beq` runs those two guards *before* it allocates (which is exactly the cited
`beqMemo = withPtrEq a b (fun _ => a.data == b.data && …)`), so a
decided-outright comparison allocates no table and the budget has nothing left
to buy: 6.1 M interning probes at `Init` scale cost **0.02 % less** than before.

#### 2. What the Aeneas subset made of it: four helper functions

The memo is threaded **by value** (`beq_go(m: BeqMap, …) -> (bool, BeqMap)`),
as con-leche threads its `map` and as task #6's accumulator rule says.  A
`&mut BeqMap` generates the identical Lean (`Result (Bool × BeqMap)` either
way) but Aeneas rejected it, and the by-value form does not fix that by
itself — three shapes had to change, each measured, each recorded in the doc
comments:

1. **"Could not match the contexts"** on the `fvar` arm: Aeneas cannot join the
   two branches of an `if` inside an arm of the *pair* match when one branch
   consumes the memo through a call taking borrows out of both `a` and `b` and
   the other does not.  The fix is that the arms are now single expressions
   over five small helpers — `beq_when` (`.fvar`/`.proj`), `beq_both` (`.app`),
   `beq_both_when` (`.lam`/`.forallE`), `beq_three` (`.letE`), plus the two
   stateless conjunctions `const_beq` and `proj_head_beq` — whose children are
   plain parameters, so the join is between two `(bool, BeqMap)`s with no loan
   tree of `a` or `b` live.  (`state_c::consts_resolve_fc_node` is the
   single-scrutinee precedent that *does* work.)
2. **An internal error in Aeneas's `simplify_let_branching`** on `let rm = <the
   match>; if rm.0 …`: the write-back is a tail call `beq_finish(…)` instead.
3. **A pattern-matching `let` on a tuple parameter** (`let (r, m) = rm;`) comes
   out as a `match` in the generated Lean that no `simp` set sees through, so
   `beq_finish` takes the decision and the table as two parameters.

Shape 1 bought something else: the ten constructor pairs live in their own
function, `expr::beq_arm`, which *halves* the generated Lean (Aeneas otherwise
duplicates the whole match, once per branch of `if rec`) and is what makes the
proof cheap (§3).

#### 3. The proof: one lemma for the memo, and the hundred cases unchanged

`Refine/Expr.lean`'s `beq` section is 632 lines changed for 496 — and **not
one of the hundred constructor-pair cases changed its argument**.  The new
shape:

* `probe_hit_false` — a probe returns `false`, from `ptr_eq_eq` alone.  It
  assumes **nothing about the table**, in particular not `ron::HashMap`'s
  invariant, because both branches of the probe answer `false` whatever `get`
  returned.  This is the model half of §1's trust argument, and it is why
  threading the memo cost no invariant bookkeeping.
* `beq_finish_fst` — the write-back changes the table, never the decision.
* `beq_go_arm` — **the frame peeled once**: on a pair with equal stored words,
  `beq_go` is `beq_arm`'s own decision (identity `false`, word guard passes,
  probe misses, write-back transparent).  Every group preamble of
  `beq_go_abs` now peels the frame with it and the hundred cases are about
  `beq_arm`, the memo-free descent — word for word task #20's proof, with the
  table carried along as state no case looks at.
* `pure_step`, `when_step`, `both_step`, `both_when_step`, `three_step` — the
  state-threaded twins of task #20's `guard_step`, one per helper of §2, so
  each of the ten diagonal cases is still `rw [<one step lemma>]; simp only
  [absExpr_mk, absExprKind, <ctor>.injEq]`.
* `beq_go_data_ne`, `beq_refines`, `beq_exact`, `eq2_refines` keep their
  statements; the four public names of `ConRon/Refine/README.md` are unchanged
  except for reflexivity, below.  `beq_exact`'s axiom census is unchanged:
  `[propext, Classical.choice, Quot.sound]`, no `sorry`, nothing from the `Rc`
  models.

**One statement is weaker, deliberately.**  `beq_refl`/`beq_go_refl`/`eq2_refl`
used to read `expr.beq e e = ok true`, which also asserts that the model's
descent **cannot fail**.  With the memo inside it, that now additionally
asserts that `ron::HashMap`'s `get` and `insert` cannot fail — the *totality*
half of task #16, which this forward-style development does not have for any
function (task #5's shape is "exact result **on success**", and every
`*_refines` in `proof/` reasons from `f x = ok y`).  So reflexivity is now
`expr.beq e e = ok c → c = true`, which is what §3.2's transparency obligation
needs and is a corollary of `beq_refines` rather than a second hundred-case
induction.  Nothing else in `proof/` used the strong form (checked).  Proving
`ron::HashMap` total is the obvious follow-up and would restore it verbatim.

#### 4. Two port bugs the memo uncovered: the resolution walk was the *spec*

With `expr::beq_go` fixed, six of the eight towers still did not finish, and
`perf` named a single site both times: `core_k::consts_resolve`, the
**unmemoised `Expr` tree walk**, reached from `check_constant_val_after_annot`
and from the inductive-install routes.  Both are the same mistake as task #28
§5a — the port calling the specification where con-leche's *executed* code
calls the `@[csimp]`-swapped memoised twin — and both are one-line fixes:

* `checker_base::check_constant_val_after_annot` now calls
  `decl_check::consts_resolve_f_fast`, because its second citation
  (`DeclCheck.lean:463-485 checkConstantValF`) says `type.constsResolveF fe`
  and `constsResolveF` is `@[csimp]`-equal to `constsResolveFFast`
  (`DeclCheck.lean:197-204`).  `decl_check`'s own doc comment already named
  con-leche task #215's `tower_struct` as the reason that twin exists.
* the nine call sites in `kernel/inductives/{struct,sum,native}_install.rs` and
  `modeled.rs` likewise.  Task #25's module note *claimed* they were memoised —
  "Both walkers the port has *are* memoised — `core_k::consts_resolve` is the
  one spelling of `Expr.constsResolve`/`constsResolveF`/`constsResolveFC`" —
  and that sentence was simply wrong: `core_k::consts_resolve` is the `Expr`
  tree walk, i.e. the spec.  The note and `struct_install`'s walkers paragraph
  are corrected in place.

Both swaps are semantically free by con-leche's own kernel-checked equations
(`constsResolveF_eq_constsResolveFFast`, `structWalkersC_eq_plain`) and the
`FEnv`-vs-`Env` agreement the port already collapses (task #18's deviation 3).
`core_k::consts_resolve` stays as the **spec** and as what `kernel::checker`'s
pure lane calls — `Kernel/Checker.lean` and `Kernel/CheckerSplit.lean` say
`constsResolve env` there, so those call sites are *correct* as they stand, and
so is `trust_axioms`'s pin guard.

#### 5. Numbers

Measured against this branch's merge base (`7cbfe83`).

| | before | after |
|---|---|---|
| `scripts/diff-fixtures.sh --timeout=60`, 348 fixtures | 290 agree, 17 differ, **8 do not finish**, 33 skipped, 485 s | **298 agree, 17 differ, 0 timeouts**, 33 skipped, **4 s** |
| `tower_{thm,struct,proj,usedlater,beqpair,recfield,mutual,nested}` | all 8 > 300 s | **≤ 1 s each**, all `accepted` |
| `con-ron-dump-check --roundtrip _tmp/corpus/init.decls` (6 137 917 interned `Expr`s, i.e. 6.1 M `expr::beq` probes at `Init` scale) | 50 256 173 826 instructions:u | **50 245 258 610** (−0.02 %) |
| `con-ron-check --verified _tmp/corpus/init.decls` | 19 166 185 039 instructions:u | 19 187 551 804 (+0.11 %) |
| `crates/con-ron-core/src/kernel/expr.rs` (raw / code) | 1 184 total — 709 / 404 extracted | 1 520 total — **972 / 493** extracted, 549 / 446 tests |
| generated `Funs.lean` | 50 944 | **51 108** (+164) |
| generated `Types.lean` | 736 | **736 — unchanged** (the memo adds no type; the two aliases are erased) |
| `TypesExternal_Template.lean` / `FunsExternal_Template.lean` | 25 / 54 | **25 / 54 — unchanged, still exactly the four `Rc` axioms and the `Rc` type.  That is the point of the design.** |
| `partial_fixpoint` / `mutual` blocks in `Funs.lean` | 408 / 13 | **413 / 14** (`beq_go`, `beq_arm` and the four helpers are one mutual group) |
| `ConRon/Refine/Expr.lean` | 2 509 | **2 645** (+632/−496) |
| `charon cargo --preset=aeneas` | | **3.9 s** |
| `aeneas -backend lean -split-files -loops-to-rec` | | **33 s, zero errors, zero warnings** |
| `cd proof && lake build` | | **2 108 jobs, zero errors, zero `ConRon` warnings** |
| `cargo test` | 167/167 | **170/170** (3 new) |
| `scripts/provenance.py check` | | green — 1 560 items, 1 662 citations at pin 3e004805 |
| `scripts/provenance.py coverage` | 851/1006 (84.6 %) | **856/1006 (85.1 %)**; `Kernel/Expr.lean` 30/42 → **35/42** |

`scripts/gates.sh`: all 6 OK.  The `Init` row is the one measurement that is
*not* yet meaningful: with the pin table empty the fold declines at position
221 after 0.019 s, so those 19 G instructions are the parser, and con-leche's
586 G baseline for `Init` cannot be compared until task #31's pin data lands.
The roundtrip row is the honest `Init`-scale proxy — it interns 6.1 M
expressions through `expr::beq` (the `Eq2` dictionary), which is exactly the
traffic a memo allocation per comparison would have taxed.

#### 6. Tests

Three new unit tests in `kernel::expr`, and the first of them is the fixture
family in one line:

* **`beq_on_two_rebuilt_dag_towers_is_memoised`** — `d 0 = bvar 0`,
  `d (k+1) = app (d k) (d k)` with one `Rc` per level, built **twice**, so the
  two towers are pointer-distinct at every level and `d 60` is `2^60` nodes as
  a tree.  `beq` says `true` (and so does the `Eq2` dictionary); without the
  memo the test does not finish.  Plus a perturbation at the root (rejected by
  the word) and one at the bottom (the descent aborts at the first mismatching
  child, which is why `false` needs no memo).
* **`probe_hit_verifies_by_identity_not_by_structure`** — §1's trust argument
  as a test: an entry is read back for the very objects it was stored for, and
  a structurally equal but pointer-distinct rebuild does **not** hit (which is
  why the model, where `ptr_eq` is `false`, never reads the table); ordered
  pairs; a foreign key; `beq_key` mixing its two arguments distinguishably.
* **`beq_go_records_only_recursive_nodes_and_only_true`** — a leaf pair is
  never recorded, an `app` pair is recorded once (not its leaves), and a
  completed `false` stores nothing.

#### 7. Left for next time

* **`ron::HashMap` totality** (`get`/`insert` cannot fail under `Inv`), which
  would restore the strong `beq_refl` of §3 and is the same lemma every future
  memo-table refinement in `cached/` will want.
* **The pin data** (task #22 / #29 / #31) — still the 17 fixture verdicts, and
  still what blocks the `Init`/`Mathlib` instruction comparison.
* **Mathlib scale** (P1.8 proper), which is now unblocked on the `beq` side.
* A `--trusted` sweep.

### Task #32 — Why `Init` blew up: memo policy and environment copies (2026-09-12, Opus under Fable)

The first scale run (P1.8) aborted: `con-ron-check --pins … init.decls`
died with `memory allocation of 72 bytes failed` at the 22 GB address-space
cap after 159 s and 953 G instructions, max RSS 21.0 GB, where con-leche
accepts the same export in 586 G / 59 s / 481 MB.  Four causes, each found
by measurement, each fixed; `Init` is now **accepted** at 933 G / 108 s /
1.06 GB (1.59× con-leche's instructions, 2.2× its RSS), and `core`
(Init+Std+Lean, 165 449 records) at 2 202 G / 488 s / 2.71 GB (1.87× /
2.18×).

#### 0. The instrument: `--stats-every N`

`con-ron-check --stats` printed the 14 `CState` map sizes once, after phase
A.  It now takes `--stats-every N` as well, which spells out
`check_decls`' two folds in the driver — `installed::annot_decl_step` per
record in phase A, `installed::check_pending` from a fresh `CState` per
record in phase B — and prints, every `N` records, the 14 map sizes, the
`FEnv` sizes (`idx`, `consts`, `visible_below`), the pending count and the
process's RSS (`/proc/self/statm`).  It is the same body as
`installed::check_decls` (`Installed.lean:407-411`) step for step, so the
flag changes no verdict; the *iterative* spelling is also what first showed
where the memory went (§1).

**The memo policy was already exact, and that is the first finding.**  The
periodic report over all 58 002 records shows only the tables
`CState.flushed` (`StateC.lean:394-398`) *keeps* growing — `ienv` to
57 384, `lsimpC`/`eqvC` to 89/82 — while the ten environment-dependent ones
never hold more than a few thousand entries and are empty at almost every
sample.  Phase A runs one `CState` across all records with `flushC` exactly
where `Installed.lean:126,154,240`, `ParsedC.lean:261`,
`CheckerC.lean:108-227` put it; phase B takes a fresh `{}` per record.  So
no map grows where con-leche's does not, and the 40× memory was **not** a
memo-policy bug.

#### 1. Phase B kept every record's `CState` alive (21.0 GB → 1.2 GB)

`checkPendingList` (`Installed.lean:398-403`) is

```lean
| pc :: rest => match checkPending mode fe pc {} with
  | .ok _ => checkPendingList fe rest
  | .error e => .error (e, pc.pos)
```

— the `{}` is consumed by the run and the run's state is **dropped** before
the walk continues.  The port's `check_pending_list_from` had

```rust
let mut st: CState = state_c::cstate_new();
match check_pending(mode, &mut st, fe, &pend[i]) {
    Ok(fe2) => check_pending_list_from(mode, fe2, pend, i + 1),  // st still owned here
```

and in Rust the frame owns `st` *across* that recursive call: all 57 362
per-record memo states — their `Expr` keys and the freshly instantiated
terms they memoize — stayed alive until the whole of phase B was over.
That is the 21 GB, and it is why the driver's iterative fold (which drops
its state each iteration) finished the very same computation in 1.21 GB.

Fix: `installed::check_pending_fresh(mode, fe, pc)` owns the fresh
`CState`, so it is dropped when that function returns — the Lean's lifetime
exactly — and the walk calls it.  No policy changes: the state is fresh per
record either way.  A one-function change, and `Init` completes.

Instructions were unaffected (1 091 G both ways): the cost was ownership,
not work.

#### 2. `flushC` walked the bucket array (1 091 G → 954 G)

`CState.flushed` is ten `:= {}`.  The port wrote ten `HashMap::clear()`
calls, documented as "same state transformer, no reallocation" — but
`clear` is `O(capacity)`: it walks every bucket.  Phase A's single `CState`
keeps whatever capacity the hardest declaration so far forced
(`whnfCoreC`), and **every later flush pays it again**; with a flush per
declaration and per environment transition inside one,
`HashMap<Expr, Expr>::clear_slots` was the single hottest function in the
`Init` profile (6.6% of cycles), with two more `clear_slots`
instantiations behind it (8.1% together).

Fix: `state_c::flushed` assigns `HashMap::new()` to each of the ten fields,
which is the cited `{}` *literally* — a fresh empty table, the old one
dropped — and allocates nothing to walk.  Same for the `instC` cap
(`StateC.lean:186-199`, `inst_list_m_reset_at`), where the Lean is
`if mp.size < instCCapC then mp else {}`.  −12.5% of `Init`'s
instructions.  `ron::hashmap`'s `clear` keeps its implementation and its
proof (`clear_refines`); it simply has no caller in the core any more.

#### 3. The copy helpers reallocated while they grew (954 G → 933 G, and −165 MB)

Every `*_copy`/`code_points` entry point started its accumulator at
`Vec::new()` and pushed, so a copy of *n* elements cost `log2 n`
reallocations: `realloc` was 2.5% and `memmove` 2.2% of `Init`'s
instructions.  Nine entry points now start at `Vec::with_capacity(len)` —
`core_types::code_points`/`str_copy`, `env::levels_copy`/`exprs_copy`/
`rec_rules_copy`/`constant_infos_copy`, `expr_ops::take_exprs`/`cons_expr`/
`levels_copy` — which is what `ron::hashmap`'s own table allocation already
did and is the same resulting `Vec`.  −3.2% on the 20 000-record prefix.

The driver also held the 165 MB dump text alive through the fold, for
nothing: the records own every `Name`, `Level` and `Expr` the reader built.
`drop(text)` after `parse_decls` took `Init`'s peak from 1.24 GB to
1.06 GB.

Measured and **rejected**: `MIN_CAPACITY` 32 → 8 in `ron::hashmap` (Lean's
`Std.HashMap.empty` is 8 buckets) costs 0.5% *more* — fewer buckets, more
collisions; and glibc malloc tuning (`MALLOC_TRIM_THRESHOLD_`,
`MALLOC_TOP_PAD_`, `MALLOC_ARENA_MAX=1`) buys 6% of wall time and 0.2% of
instructions, i.e. it moves cache behaviour, not work.

#### 4. The cached tier ran the *pure* tier's scope guard (core: 3 014 G → 2 202 G)

`Init`'s profile does not show it, but `core`'s does: `core_k::fab_scope_ok`
13.5% and `expr_ops::fvar_leaves_go` 12.7% — 26% of the run in the
stuck-major rescue's scope guard.  The three rescue branches of
`core_c::major_to_ctor_*_i` called `core_k::fab_scope_ok`, which is the port
of the **pure** guard (`Kernel/Core.lean:1274-1456`,
`fab.wscopedB depth && fab.looseBVarsBounded 0 &&
fab.fvarLeaves.all (major.fvarLeaves.contains ·)`).  The cached twin
`majorToCtorI` (`CoreC.lean:543-670`) runs

```lean
ExprC.wscopedB depth fab && ExprC.looseBVarsBounded 0 fab
  && ExprC.leafGuard fab major
```

where every member is `ExprOpsC`'s: `wscopedB` is one **memoized** DAG walk
(`ExprOpsC.lean:652-679`) and `leafGuard` (`:747-748`) short-circuits on
`!fab.hasFvar`, collects the base leaves through a `seen` map and memoizes
the subset test itself (`:717-742`).  A memo the cited code has and the port
did not is exactly what DESIGN.md §3.1 forbids.

The port already *had* both twins in `cached::expr_ops_c` (task #26 ported
them) — they had no caller.  `core_c::fab_scope_ok_i` is now the cited
conjunction, and the three branches call it; `core_k::fab_scope_ok` stays as
the pure tier's port.  `core` drops 27% of its instructions and 0.7 GB.
`Init` is unchanged to 0.02% — the rescue barely fires there, which is why
the first corpus run did not show the mistake.

#### The numbers

`perf stat -e instructions:u`, `/usr/bin/time -v`, `ulimit -v 22000000`,
release build with `overflow-checks`, artefacts in `_tmp/corpus/cr-{init,core}-j1-t32.*`
and `_tmp/t32/`.

| `init` (58 002 records) | verdict | instructions:u | wall | peak RSS |
|---|---|---|---|---|
| before (task #29's binary) | **abort** at the 22 GB cap | 953 G | 159 s | 21.0 GB |
| §1 phase-B state dropped | accepted | 1 091 G | 119 s | 1.23 GB |
| §2 `flushC` = fresh tables | accepted | 954 G | 108 s | 1.24 GB |
| §3 `with_capacity`, text dropped | accepted | 933 G | 108 s | 1.06 GB |
| §4 cached scope guard | accepted | **933 G** | **110 s** | **1.06 GB** |
| con-leche `--jobs=1` | accepted | 586 G | 59 s | 0.48 GB |

| `core` (165 449 records) | verdict | instructions:u | wall | peak RSS |
|---|---|---|---|---|
| after §1-§3 | accepted | 3 014 G | 520 s | 3.40 GB |
| after §4 | accepted | **2 202 G** | **488 s** | **2.71 GB** |
| con-leche `--jobs=1` | accepted | 1 180 G | 150 s | 1.24 GB |

Both targets are met: instructions within 2× of con-leche (1.59× on `init`,
1.87× on `core`), RSS within 4× (2.2× on both).  Mathlib was not run.

#### What the profile still says, in order

`perf record -e instructions:u` on `core` after the four fixes
(`_tmp/t32/core-fix4.idata`):

* **glibc malloc/free, ~33%** (`__libc_malloc2` 13.7%, `_int_free_chunk`
  10.4%, `_int_malloc` 3.2%, `malloc_consolidate` 2.4%, …).  Lean allocates
  small objects from its own free lists; we go to `malloc` for every `Expr`
  node, every `AList` cons and every memo table.  The port cannot change
  the *count* much without changing con-leche's policy, so the lever is the
  allocator — a `#[global_allocator]` in the unverified binary crate, which
  would need a vendored allocator (the workspace has zero dependencies
  today).
* **`expr::beq_go` 14.2%** — structural equality on memo keys.  This is
  task #30's `beq` pair memo / hash-consing lane; it is the biggest single
  function left.
* **`HashMap::allocate_slots` 6.3%** — the per-call memo tables
  (`instantiate1`, `instantiateList`, `abstract1`, … each take a fresh `{}`,
  as con-leche does).  Ours costs one 1 280-byte allocation plus a 63-call
  halving recursion pushing 32 `Nil`s; Lean's `{}` is one 8-slot array.  A
  leaf `while` loop (§3.4 permits one) or a lazily allocated table would
  take most of it, at the price of re-proving `allocate_slots_spec` (26
  lines) or relaxing `Inv.min_cap` (a redesign of the proved map).
* **The two `fenv::dup`s, ~10% and growing with `|env|`.**
  `native_install`'s module note names them: `check_native_pass_former` and
  `check_native_rec_rules` each need a *second* view of the index, and the
  port's linear `FEnv` gives it by rebuilding the whole index —
  `O(|env|)` twice per inductive block.  At 176 130 constants that is
  `mk_fenv_go` 0.9% + the index map's `move_elements_from_list` 2.8% +
  `insert_no_resize` 1.5% + `insert` 0.8% + `constant_info_dup` 1.2% +
  `constant_info_name` 0.9% + `prop_when::append_from` 1.6%, and it is why
  `core`'s ratio to con-leche (1.87×) is worse than `init`'s (1.59×):
  con-leche needs 7.1 M instructions per declaration on `core` against
  10.1 M on `init`, we need 13.3 M against 16.1 M.  The fix task #14
  foresaw is `idx: Rc<HashMap<…>>` with `push` moving to an install-phase
  type that owns the map; it does not touch the model (`abs` reads the index
  through `find` either way) but it does change `FEnv`'s API, so it is a
  design step, not a patch.
* `fenv::push`'s `consts.insert(0, ci)` is `O(|env|)` too, but
  `__memmove_avx512` is 8.3% *including* every `Vec` copy in the run, so the
  newest-first list is not worth a representation change yet.
* **Memory**: the driver materialises all 165 449 records before checking,
  so `core`'s 2.71 GB is mostly the parsed `Expr` DAG (6.1 M nodes for
  `init` alone).  con-leche's frontend streams.  A streaming reader is a
  driver change, invisible to the core.

#### Tests

No new unit tests: every change is either a lifetime (§1), a spelling of
`{}` (§2), a capacity hint (§3) or a rewiring to functions task #26 already
tested (§4).  The evidence is the corpus and the existing 170:

| gate | result |
|---|---|
| `cargo test` | 170/170 (153 unit + 4 integration + 13 in `con-ron-dump`), warning-free at `-D warnings` |
| `scripts/lint-rust-style.sh` | clean |
| `scripts/provenance.py check` | green — 1 548 items, 1 651 citations at pin 3e004805 (one new item, `core_c::fab_scope_ok_i`, with three citations) |
| `scripts/extract.sh --check` | fresh; externals still exactly **1 type, 4 `Rc` fns** |
| `cd proof && lake build` | 2 115 jobs, zero errors — no proof needed a change |
| `scripts/diff-fixtures.sh --timeout=60` | 307 agree, **0 differ**, 8 do not finish, 33 skipped |
| `init`, `core` | accepted, at the numbers above |

#### Left for next time

* **The `Rc<HashMap>` index** (the ~10% above, growing with `|env|`): the
  one remaining *superlinear* item, and the reason `core` is relatively
  worse than `init`.
* **`beq_go`** (14%) — task #30.
* **The allocator** (~33%): a vendored `#[global_allocator]` for the
  unverified binary, or a lazily allocated `ron::HashMap` table.
* Mathlib (691 123 declarations, con-leche 12 817 G / 1 228 s / 8.6 GB):
  at `core`'s ratio that is ~24 T instructions and ~19 GB, i.e. the address
  cap is the binding constraint — run it only after the index change.

### Task #33 — The ledger closed: citations completed, deliberate skips listed (2026-09-12, Opus under Fable)

P1's closing task.  The port ledger read **906/1 006 declarations, 93 % of the
core's Lean lines translated**; the gap was not missing code but missing
*bookkeeping* — declarations the Rust does translate without saying so, and
declarations the port will never have without anyone having written down why.
Both halves are now closed, and the two reports agree.

#### 1. The four families that were translated but uncited

| family | where it was | how it is cited now |
|---|---|---|
| the **raw basis pins** — `Basis/{Eq,Nat,PUnit,Empty,False,Quot}.lean`, 34 declarations, 0 % covered | implemented by the *generated* `kernel/basis_tables.rs`, whose only citation was the module-level `BasisA.lean:50-57 BasisKind.declsA` | the generator emits them: `proof/ConRon/Gen/Main.lean` now carries, per block, the `*A` names and the raw declarations `#annotate_basis` computes them from, and writes one `/// con-leche:` line per raw declaration on the block function |
| `Cached/ExprC.lean`'s `ExprC` + ten `mk*` aliases (11) | `abbrev ExprC := ConLeche.Expr` and ten `@[inline]` constructor aliases — literally `kernel/expr.rs`'s constructors | a second citation on each of the ten (`ExprKind`/`ExprNode`/`Expr` cite the `abbrev`), plus a module-note paragraph saying the file *is* this file |
| `Cached/CheckerC.lean`'s `instPisAtLiftC`, `structProjBodiesGoC` (2) | the same walks at `ExprC.instantiate1Lift`, which since con-leche's task #172 B3a *is* `Expr.instantiate1Lift` | second citations on `expr_ops::inst_pis_at_lift{,_from}` and `struct_parts::struct_proj_bodies_go`, following `struct_proj_bodies`' existing precedent |
| `Cached/CheckerC.lean`'s `opE`, `opB`, `opS` (3) | collapsed into `kernel/type_checker.rs`: `opE` is higher-order in its `pick` (§3.4 forbids the closure), so the port has it four times over, once per pick | `opE` on `whnf_core`/`whnf`/`infer_type_core`/`annotate_core`, `opB` on `is_def_eq_core`, `opS` on `ensure_sort_core`, with the reckoning in the module note |

Nothing in class (c) — **no executable code was found missing**.  The 50
declarations these citations cover were all already ported; what was missing
was the line saying so.

**The generator asks the gate where the lines are.**  A generated file must
not carry hand-maintained line numbers: `provenance.py update` would rewrite
them and the next regeneration would revert it.  So `provenance.py` grew a
fourth mode, `locate <path> <decl>…`, which prints the canonical citation body
(`<path>:<a>-<b> <decl>`) — the same block `update` relocates to, from the same
locator — and `Gen/Main.lean` shells out to it while emitting.  Regeneration is
therefore a **fixed point** (verified: two runs byte-identical, and again after
the `extend_block` fix below), and a con-leche bump is reconciled for this file
by re-running `lake exe con-ron-gen-tables`.

#### 2. `scripts/provenance-skip.txt`: 100 declarations, each with its reason

The allowlist is `<con-leche path> <declaration> <reason>` lines, `*` for a
whole file, reason mandatory (§3.7).  `coverage` subtracts them from the
denominator and reports them separately; it also reports a skip that names no
declaration (`STALE`), one whose declaration is cited after all (`REDUNDANT`)
and one with no reason (`MALFORMED`), and exits non-zero on any of the three —
so the list cannot rot quietly.  `check`'s semantics are untouched.

| group | n | why |
|---|---:|---|
| elaboration-time meta code | 34 | `BasisGen.lean`'s `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations (33, one `*` entry), `TrustAxioms.trustPinEnv`.  The Rust core has no elaborator; it carries the *results* (`basis_tables.rs`, the annotated pins) |
| proof-tier and mode-gated variants | 22 | `CoreGated` (9), `CoreIO` (3), `CheckerGated` (2) as `*` entries; `TypeChecker.pureFns`; `CoreC.lean`'s seven `*PC`/`*TC` bodies, which are the port's runtime-`&CheckMode` bodies at a literal mode |
| `Prop`s and proof-carrying apparatus | 29 | the sixteen `*MemoInv`s (`ExprOps` 11, `Level`, `DeclCheck`, `NativeInstall`, `StructParts` 2), `Installed.lean`'s twelve-member `InstallRun`/`GroupChecked`/`FullyChecked`/`collectChecks` family, `PropWhen.casesZ` |
| the address-keyed `Expr.beq` apparatus | 7 | `EqPair.dflt`, `beqBudget`, `BeqRes`, `BeqOut`, `BeqOut.mk`, `withAddr`, `ptrDec` — superseded by task #30's hash-keyed, pointer-verified memo and §3.2's `Rc` axioms |
| driver-only rendering | 6 | `msSecs`, `declCLabel`, `ValueKind.word`, `divModAttemptReason`, `Name.toString`, `PropWhen.reprPrec'` — `String`-valued, on no verdict path (§3.1) |
| host bridge, and one dead declaration | 2 | `Name.ofLeanName` (no `Lean.Name` in Rust); `BasisKind.decls`, the RAW block dispatcher, which **nothing** in con-leche's `Kernel/`/`Cached/` reads — the installation stores `declsA` |

Every entry's long argument already lived in the Rust module note of the
module that would have held it; the file is the machine-readable index of
those notes, and §3.7 now says so.

#### 3. The two reports made to agree

`coverage` counts *declarations*; `progress.py` counted *lines inside cited
ranges*, and the two disagreed badly — `Env.lean` was 38/38 declarations but
60 % of lines, because a citation names a declaration's code and not its
40-line doc comment.  `progress.py` now uses `coverage`'s own predicate per
declaration and weights it by the whole block: a named declaration credits its
whole block.  That is what closes the last 7 % of the core, and it is the
honest measure — the ledger's unit is a declaration, the lines are its weight.
Two consequences: `verified` rose too (632 → **900** lines), and
`CORE_EXCLUDE` is gone, its four files being `*` entries in the skip file.

One locator bug fell out of the audit: `extend_block`'s backward walk over a
closing `-/` looked for a `/--` opener and walked *through* a `/-! … -/`
section header, swallowing the previous declaration's doc comment — two blocks
overlapped (`Frontend/InModel/Kit.lean`'s `sortOf`/`sortCeil`).  Fixed by
stopping at `/-!`; no core file was affected (the cherry total drops 8 135 →
8 093), no citation moved, and the generated citations are unchanged.

#### Numbers

| gate | result |
|---|---|
| `scripts/provenance.py check` | green — **1 561 items, 1 728 citations** (was 1 548 / 1 651) at pin 3e004805 |
| `scripts/provenance.py coverage` | **TOTAL 906/906 covered (100.0 %), 0 uncovered, 100 deliberately skipped** (was 856/1 006, 85.1 %) |
| `scripts/progress.py`, verified core | to translate **13 694**, translated **13 694 (100 %)**, verified **900 (6 %)**, skipped **656** — was 13 987 / 13 085 (93 %) / 632 (4 %) |
| per-file | **every file of `Kernel/` and `Cached/` is 100 % translated**; `Basis/{Eq,Nat,PUnit,Empty,False,Quot}.lean` are also 100 % *verified* (`BasisTables.lean`'s six `basis_decls_*_refines`) |
| `cargo test` | **173/173** (156 unit + 4 integration + 13 in `con-ron-dump`), warning-free at `-D warnings` |
| `scripts/lint-rust-style.sh` | clean (the generated file needed no exemption) |
| `scripts/extract.sh --check` | fresh after regeneration; the diff is **only `Source:` line comments** (101 lines) — no model changed, externals still exactly 1 type + 4 `Rc` fns |
| `cd proof && lake build` | green, 324 s |
| `scripts/diff-fixtures.sh --timeout=60` | **315 agree, 0 differ**, 33 skipped |
| `lake exe con-ron-gen-tables` | `basis_tables.rs` +77/−6 lines: **41 `/// con-leche:` citation lines** (one `BasisKind.declsA` plus the raw pins, per block) and their prose; byte-identical on re-run |

#### Left for next time

* The ledger is now a *proof* ledger: the core is 100 % translated and 6 %
  verified, so `progress.py`'s `verified` column is the only one with room
  left.  The 1 384 Rust functions carry 123 `_refines` lemmas.
* `Frontend/` and `Main.lean` (8 093 lines to translate, 0 % — the cherries of
  §5 P4) have no skip entries yet; when they are ported, the driver-only
  rules the core deliberately refuses (`Main.lean`'s taint-skip decline,
  `cached/installed.rs`'s note) belong in the same file.
* `coverage`'s non-zero exit on a rotten skip list is not in
  `scripts/gates.sh`; adding it is a one-line change once the list has
  survived a con-leche bump.

### Task #34 — O(1) environment views: what the profile actually asked for (2026-09-12, Opus under Fable)

The brief was to make `FEnv`'s views `O(1)` as con-leche's are: share the
index through `Rc`, keep phase A's `push` on an owned `FEnv`, and hand phase B
a shared view whose `restrict_to` is a struct copy.  **The first thing task
#34 found is that the premise does not hold**, in two ways, and the second is
what the measurement says to do instead.

#### 0. Phase B is already `O(1)`; the two `dup`s are in phase A

`installed::check_pending` threads the index linearly — it takes the value at
the installed bound, calls `fenv::restrict_to`, and hands it back at the bound
it came in at — so phase B's per-record view *is* the cited field update and
has been since task #14.  There is nothing at the phase boundary to win.

The `fenv::dup`s task #32's profile named are in **phase A**: they are inside
the inductive install routes, which run from `annot_decl_step` →
`parsed_c::check_decl_step_c`.  There are six call sites and they belong to
the two routes' recursor/former stages —
`native_install::check_native_pass_former` and `check_native_rec_rules`,
`modeled::check_ind_recs` and its cached twin `inductives_c::check_ind_recs_s`
— each needing a *second* (in `check_ind_recs` a second and a third) view of
one index while the fold's accumulator grows.  So "share only at the phase
boundary" would have left the cost exactly where it was: pushes and second
views interleave, per inductive block, throughout phase A.

#### 1. The measurement that rules out every shared-index design

Instrumented counters on `Init` (58 002 records, 59 967 constants):

| on `Init` | count |
|---|---|
| `fenv::dup` calls | **1 22x** (the last report before the run ended is `dups=1220`) |
| index entries those `dup`s rebuild | **13.6 M** |
| `fenv::find` calls | **~80 M** (7.3 M in phase A, the rest in phase B) |

`find` is **six times** the traffic of the whole index-rebuild bill.  That
settles the design question the brief left open:

* `idx: Rc<HashMap<…>>` cannot work at all inside §3.2's four-hole budget —
  `Rc::get_mut`/`make_mut` are outside the allowed API, so a shared map can
  never be extended, and `push` would have to copy it (`O(n)` **per
  constant**, worse than today by a factor of the constant count).
* Every design that *does* give `O(1)` sharing puts something in front of
  `find`: an overlay (`Rc`-shared base + owned top) makes `find` two probes
  and grows the overlay without bound unless it is consolidated, and
  consolidating is the `O(n)` rebuild again; a level chain (`split` moving the
  owner's map into an `Rc` and starting a fresh top) grows one level per
  inductive block, so `find` walks 1 200 maps; the logarithmic-method fix for
  that leaves `O(log n)` ≈ 16 probes.  At 80 M calls, adding ~50 instructions
  to `find` costs 4 G instructions — as much as the entire remaining `dup`
  bill.  A persistent hash trie is the same trade with a nicer constant and a
  new proved container.

So **the flat owned map stays**, and what task #34 did is make the copied
entry cheap and the copy itself unavoidable-but-small.

#### 2. What landed: the stored record is shared, and the index build is pre-sized

1. **`Rc<ConstantInfo>` in both `Env.consts` and `FEnv.idx`** (`env::Env`'s
   new deviation note).  con-leche's `FEnv.push` is
   `⟨⟨ci :: fe.env.consts⟩, fe.idx.insert ci.name (fe.visibleBelow, ci), …⟩` —
   *one* `ci`, reached from the list and from the index, because the runtime
   shares the object.  The port stored it twice and paid a
   `env::constant_info_dup` for the second copy (task #14 recorded that as a
   deviation).  Now `fenv::push` calls `env::constant_info_share`
   (`Rc::new`) once and `env::constant_info_rc_dup` (`Rc::clone`) for the
   index, `mk_fenv_go` clones the pointer, and `env_dup` (i.e.
   `constant_infos_copy`) is `n` reference bumps instead of `n` record copies.
   `fenv::find` reaches the record through `Rc`'s `deref`.

   **This removes a deviation rather than adding one.**  §3.2's model has
   `Rc T` *reducible to* `T`, so the generated Lean's
   `Vec (Rc ConstantInfo)` and `HashMap Name (U64 × Rc ConstantInfo)` abstract
   exactly as `Vec ConstantInfo` and `HashMap Name (U64 × ConstantInfo)` did;
   `abs` is unchanged, the four `Rc` holes are unchanged (the extraction still
   reports "1 type, 4 fns"), and no proof needed a line.
2. **`mk_fenv_go` pre-sizes the table**: its base case is
   `HashMap::with_capacity(cs.len())` where it was `HashMap::new()`.  That is
   the same `∅` — task #7 fixed that a `ron::HashMap`'s capacity is invisible
   to the abstract map it refines, and task #32 already used
   `Vec::with_capacity` the same way — but an index build no longer rehashes
   its way up through `log n` capacities.  `HashMap<Name, …>::
   move_elements_from_list` was the single biggest item of the index path,
   0.54 % of `Init`; it is now 0.04 %.
3. A new `env::env_of` (an index recursion over a plain record list) is how
   the tests and the basis paths build an `Env` now that the list holds
   shared records; `Env { consts: … }` outside `env.rs`/`fenv.rs` is gone.

**Deliberately *not* done**, and why: the `Env.consts` order flip the brief
contemplated ("store newest-last, search `find` from the end").  Once the
element is an `Rc`, `Vec::insert(0, rc)` moves eight bytes per constant, which
does not show in the profile; and the flip would cost the faithfulness the
newest-first order buys — con-leche's `Env.consts` *is* newest-first, `abs`
maps it to the Lean list with no `reverse`, and `FEnv`'s counters are
positions from the bottom of exactly that list.  The `Vec` is essentially
"only ever read through the index" (the second half of the brief's own
condition): `mk_fenv`, `dup` and the driver's final environment are its only
readers.

#### 3. The numbers

`perf stat -e instructions:u`, `/usr/bin/time -v`, release build with
`overflow-checks`, `--pins _tmp/dump-fixtures/pins.dump`, artefacts in
`_tmp/t34/`.  A Mathlib run of the *previous* binary was occupying one core
throughout, which is why instructions, not wall time, is the measure.

| `init` (58 002 records) | verdict | instructions:u | wall | peak RSS |
|---|---|---|---|---|
| before (task #33's binary) | accepted | 802.2 G | 108 s | 1 055.7 MB |
| after (task #34) | accepted | **769.5 G** | **96 s** | **1 033.8 MB** |
| con-leche `--jobs=1` (task #29) | accepted | 586 G | 59 s | 481 MB |

**−4.1 % instructions, −11 % wall, −2 % RSS**, and the ratio to con-leche on
`init` goes 1.37× → 1.31×.  The index path in the `perf` profile:

| symbol | before | after |
|---|---|---|
| `HashMap<Name, (U64, …)>::move_elements_from_list` | 0.54 % | 0.04 % |
| `…::allocate_slots` (the pre-sized table) | 0.00 % | 0.29 % |
| `…::insert` + `insert_no_resize` + `list_insert` | 0.33 % | 0.17 % |
| `env::constant_info_dup` | 0.12 % | — |
| `env::rec_rules_copy_from` (inside it) | 0.10 % | — |
| `env::constant_infos_copy_from` (in `env_dup`) | 0.09 % | 0.09 % |
| `fenv::mk_fenv_go` | 0.15 % | 0.04 % |
| index path, direct (all of the above plus the `AList` drop glue and `constant_info_name`) | **1.49 %** | **0.78 %** |

The remaining 3.4 points of the 4.1 % are the allocator, which the 13.6 M
record copies and their `Vec<Name>`s were feeding: `__libc_malloc2` 15.88 % →
15.10 % and `_int_free_chunk` 13.19 % → 11.73 % *of a total that itself fell*,
i.e. −9 % and −15 % in absolute instructions.

#### Gates

| gate | result |
|---|---|
| `scripts/gates.sh` | all 6 OK (`cargo build`, `cargo test`, lint, provenance, `extract.sh --check`, `lake build`) |
| `cargo test` | 173/173 (156 unit + 4 integration + 13 in `con-ron-dump`), warning-free |
| `scripts/provenance.py check` | green — 1 565 items, 1 730 citations at pin 3e004805 |
| `scripts/extract.sh` | zero Aeneas errors, zero warnings; externals still exactly **1 type, 4 `Rc` fns**, both templates byte-identical |
| `cd proof && lake build` | 2 108 jobs, zero errors — **no proof changed**, `Refine/*` untouched |
| `scripts/diff-fixtures.sh --timeout=60` | **315 agree, 0 differ**, 0 timed out, 33 skipped |
| `init` | accepted at the numbers above |

`core` and Mathlib were not re-run: the maintainer's Mathlib run held the
machine, and the brief scoped the measurement to `init` and the fixtures.  On
`core` the same change should be worth more than on `init` — task #32 measured
the index path at ~10 % there, against ~1.4 % here, because `dup`'s bill grows
with `blocks × |env|`.

#### Left for next time

* **The `dup`s themselves are still `O(|env|)`** — smaller by 2-3×, not gone,
  and still the port's only superlinear term.  The one design that removes
  them without touching `find` is to stop asking the install routes for a
  second *owned* view: an `FEnv` view that **borrows** the installed index and
  carries the block's own pushes as a short overlay, with the block returning
  its constants as a *delta* that the owner folds in at `O(block)`.  That is a
  change to `native_install`/`modeled`/`sum_install`'s shape (and a lifetime
  inside `FEnv`, which task #14's `&'static str` experience says Aeneas may
  refuse), so it is a design step of its own, not a patch to `fenv.rs`.
  A cheaper down payment: `check_native_rec_rules`' `dup` — the one site whose
  second view is exactly `fe` plus a single push — can go away exactly, with a
  `push`/`pop` pair that remembers the entry the push displaced
  (`ron::HashMap::insert` already returns it) and the local law
  `pop (push fe ci) = fe`.  That kills one of the native route's two `dup`s.
* **`HashMap::allocate_slots`, ~17 % of `Init`** (8.8 % for the
  `u64 → (Expr, Expr)` `beq` table, 6.9 % for `ExprNatKey`, 1.8 % for
  `Expr → Expr`, 0.6 % for `Expr → Bool`): the per-call memo
  tables con-leche allocates as `{}`.  This is now much the largest single
  item in the profile — bigger than task #32's estimate from `core` — and the
  lever is the one task #32 named: a lazily allocated `ron::HashMap` table, at
  the price of relaxing `Inv.min_cap` in the proved map.
* `expr::beq_go` + `beq` + `beq_record`, 3.5 % on `init` (14 % on `core`) —
  task #30's lane.
* The allocator, ~33 % (a vendored `#[global_allocator]` in the unverified
  binary crate).

### Task #35 — Lazy memo allocation and the allocator (2026-09-12, Opus under Fable)

Task #34's "left for next time" named the two largest items of `Init`'s
profile — `ron::HashMap::allocate_slots` at ~17 % and glibc `malloc`/`free` at
~33 % — and this task took both.  Together they are **−22.0 % of `Init`'s
instructions and −37 % of its wall time**, which puts con-ron within 2.4 % of
con-leche's instruction count on `Init` (600.1 G against 586 G) where task #34
left it 31 % behind.

#### 1. `ron::HashMap::new` allocates nothing

con-leche's memo tables are `{}`, i.e. `Std.HashMap.empty`, and the port's
`ron::HashMap::new` answered that with `MIN_CAPACITY` = 32 `AList::Nil`
buckets: one `Vec::with_capacity(32)` plus the `log2 32`-deep `allocate_slots`
recursion that pushes them.  The checker makes one such table **per call** in
several places — the `*Fast` walks' `seen` maps, `beq`'s pair memo
(`kernel::expr`, task #30), the per-record `CState`s — and the overwhelming
majority never see an insert, so 32 buckets were allocated, walked and dropped
for nothing.

`new` now builds `HashMap { num_entries: 0, max_load: 0, saturated: false,
slots: Vec::new() }` — no allocation at all — and one new private function,
`ensure_slots`, gives an unallocated table its `MIN_CAPACITY` buckets on the
first `insert`.  `get`, `contains_key` and `remove` carry a
`self.slots.len() == 0` guard (they must: `bucket_index` would divide by
zero), `len`, `is_empty` and `clear` were already correct on an empty `slots`,
and `with_capacity` is unchanged — task #34's pre-sized `mk_fenv` table still
allocates eagerly, which is what it wants.

**This is not a memo-policy change in the sense of §3.1.**  The abstract map
of a fresh table is `∅` whether or not buckets are allocated, so the table the
port creates is still exactly the one con-leche's `{}` denotes; no probe that
hit before misses now and none that missed hits.  It is the same argument that
made task #34's `with_capacity` pre-sizing free, in the other direction.
What it *does* change is the **model**, because the generated Lean changed.

#### 2. What the proof needed (`proof/ConRon/Refine/HashMap.lean`, task #16)

`slots = []` is now a reachable state, so `Inv` has a case for it.  Of the
five fields, only the two capacity ones needed anything: they became
conditional,

```lean
  pow2    : 0 < m.slots.val.length → ∃ e, m.slots.val.length = 2 ^ e
  min_cap : 0 < m.slots.val.length → 32 ≤ m.slots.val.length
```

and the other three hold on the unallocated table *as they stand* —
`slot_inv` is vacuous (`m.slots.val[j]!` is the default `Nil` for every `j`,
the new `alv_default` simp lemma), `al_v m` is `[]`, `num_entries` is `0`.
The implication form (rather than a disjunction, or a two-case `Inv`) is what
kept the churn mechanical: every consumer that *preserves* the length —
`clear_refines`, `insert_no_resize_spec`, `remove_refines`,
`Inv_of_slots_eq` — still discharges its two goals with the unchanged
`rw [hlen]; exact hinv.pow2`.

Five items are new or changed, and nothing else in the file moved:

| item | what |
|---|---|
| `vec_len_eq_zero_iff` | `Vec.len v = 0#usize ↔ v.val = []` — the guards test the left side, the proofs want the right |
| `unallocated_inv` | `slots = [] → num_entries = 0 → Inv ∧ al_v = [] ∧ toFun = ∅`; `new_refines` is two `rfl`s on top of it |
| `ensure_slots_spec` | `Inv`, **`0 < slots.length`**, and `al_v`/`num_entries`/`saturated` unchanged |
| `try_resize_spec` | gained the hypothesis `0 < m.slots.val.length` — it is the one operation that needs the table allocated, since `0` doubled is `0`.  `insert_refines` supplies it from `ensure_slots_spec` |
| `get_refines`, `remove_refines` | each opens with the guard branch: an unallocated table denotes `∅`, so `None` is the right answer and `Function.update (fun _ => none) k none` is `fun _ => none` |

`insert_refines` threads `ensure_slots_spec` first and rewrites its `toFun`
through `htf0 : toFun m0 = toFun m`.  **No `sorry`, and no lemma weakened**:
the axiom census at the bottom of the file is unchanged (`propext`,
`Classical.choice`, `Quot.sound`), and it is a `#guard_msgs`, so a `sorryAx`
sneaking in is a build error rather than a silent regression.  Total: +140/−13
lines in `Refine/HashMap.lean`, about an hour, and no other proof file
mentions `ron::HashMap` yet (the memo proofs that will are P3's).

#### 3. The allocator: `mimalloc`, in the unverified crate only

`#[global_allocator]` now sits in `crates/con-ron-dump/src/lib.rs`, so the two
binaries that link it (`con-ron-check`, `con-ron-dump-check`) get it and
nothing else does.  **The model is untouched by the allocator, and this is not
a hole**: Charon extracts `crates/con-ron-core` alone and the allocator is not
an item of that crate; the Aeneas model has no heap at all (`Rc`, `Box` and
`Vec` are modeled by their contents, §3.2), so `proof/ConRon/Generated/*` is
byte-identical whichever allocator is linked.  Nor can it change a verdict:
an allocator decides only *where* bytes go, and the core reads no address —
`ptr_eq` compares identity, not order, and is modeled as `false` anyway.

Both candidates were available over the network (`cargo add` works in this
sandbox) and both were measured.  `mimalloc` is the default;
`--no-default-features` gives glibc `malloc` back and
`--no-default-features --features jemalloc` selects `tikv-jemallocator`.
`ALLOCATOR` is a `pub const` naming the choice so a measurement can be traced
to a build.

This is the same lever task #32 measured as *worthless* — glibc's tunables
(`MALLOC_TRIM_THRESHOLD_`, `MALLOC_TOP_PAD_`, `MALLOC_ARENA_MAX=1`) bought
0.2 % of instructions — and the difference is the point: the win is not in
glibc's *policy* but in its `malloc`/`free` fast path, which a
size-class-and-free-list allocator replaces outright.

#### 4. The numbers

`perf stat -e instructions:u`, `/usr/bin/time -v`, release build with
`overflow-checks`, `--pins _tmp/dump-fixtures/pins.dump`, artefacts in
`_tmp/t35/`.  The maintainer's Mathlib run held one core throughout, which is
why instructions, not wall time, is the measure (as in task #34).

| `init` (58 002 records) | verdict | instructions:u | wall | peak RSS |
|---|---|---|---|---|
| before (task #34's binary) | accepted | 769.5 G | 96 s | 1 032.9 MB |
| + lazy slots | accepted | 722.1 G | 92 s | 1 021.0 MB |
| + `mimalloc` (**the default**) | accepted | **600.1 G** | **60 s** | **1 006.0 MB** |
| + `jemalloc` instead | accepted | 604.9 G | 58 s | 1 010.8 MB |
| con-leche `--jobs=1` (task #29) | accepted | 586 G | 59 s | 481 MB |

Lazy slots alone are **−6.2 %**; the allocator on top is another **−16.9 %**;
together **−22.0 %** instructions, −37 % wall, −2.6 % RSS.  The ratio to
con-leche on `init` goes 1.31× → **1.024×** in instructions and 1.63× → 1.02×
in wall time.  `jemalloc` is 0.8 % more instructions and 4.8 MB more RSS than
`mimalloc` but 2 s less wall; instructions decided it, and the feature is
there for the other choice.

The `perf record -e instructions:u` profiles of the same three binaries
(`_tmp/t35/prof-{base,lazy,mi}.data`), as a share of each run and as absolute
instructions (share × that run's total), which is the only way a shrinking
denominator can be read:

| group | before | + lazy slots | + `mimalloc` |
|---|---|---|---|
| `HashMap::*::allocate_slots` (4 instantiations) | 19.1 % / 147 G | 15.7 % / 113 G | 19.4 % / 116 G |
| the allocator (`malloc`/`free`/`mi_*` and their helpers) | 41.8 % / **322 G** | 43.5 % / 314 G | 19.6 % / **118 G** |
| all of `ron::hashmap` | 34.8 % / 268 G | 31.6 % / 228 G | 42.7 % / 256 G |
| `expr::beq*` | 3.9 % / 30 G | 4.4 % / 32 G | 5.2 % / 31 G |

Two readings, and one caveat.

* **Lazy slots** took `allocate_slots` from 147 G to 113 G (−23 %) and all of
  `ron::hashmap` from 268 G to 228 G: the extra 6 G beyond the direct saving is
  the allocator traffic and the `AList` drop glue the dead tables were
  generating.
* **`mimalloc`** took the allocator path from 314 G to 118 G, **−63 %** — by
  far the largest single change either task has produced.
* The caveat: symbol shares are *not* comparable across the allocator switch.
  `mimalloc`'s fast path inlines into its callers, so work that glibc booked
  under `__libc_malloc2` is booked under `ron::hashmap::*` and the drop glue
  instead; that, not a regression, is why "all of `ron::hashmap`" reads higher
  in the last column.  The totals in the previous table are the honest
  measure.

**`allocate_slots` is still the biggest core item** — 116 G, 19.4 % — and it
is no longer the *dead* tables: it is the 32 `Vec::push`es a table that really
does get an insert pays on its first one.  Task #32 measured `MIN_CAPACITY`
32 → 8 as 0.5 % *worse*, but it measured it when every table paid the
allocation whether it was used or not; now that only used tables allocate, and
now that `ExprNatKey`'s and the pair memo's tables are 15 of those 19 points,
that trade deserves re-measuring (it costs `Inv.min_cap`'s `32` and
`new_refines`' exponent, nothing structural).

#### 5. What was *not* measured, and why

`core.decls` was skipped: `pgrep -x con-ron-check` found the maintainer's
Mathlib run still going at the one check the brief allows, and the brief says
not to wait.  Both changes should be worth *more* there than on `init` —
`core`'s profile has the same two items with bigger shares — so the `init`
numbers are the conservative half of the story.

A note on the memory cap.  `ulimit -v` limits *address space*, not RSS, and
`init`'s 1.03 GB peak RSS needs ~2.2 GB of address space (glibc's freed-but-
retained arenas): the pre-change binary dies at `ulimit -v 1500000` and at
`-v 2000000` with `memory allocation of 64 bytes failed`.  All the runs above
therefore used `ulimit -v 3000000`, which is still well under the brief's own
4 GB cap for the much larger `core`, and the figure the 3×-of-con-leche budget
is about — peak RSS, 1.006 GB against con-leche's 481 MB — is met with room to
spare and *improved* by this task.  Worth pinning down when the `core` and
Mathlib caps are next set: the two units are not interchangeable.

#### Gates

| gate | result |
|---|---|
| `scripts/gates.sh` | all 6 OK (`cargo build`, `cargo test`, lint, provenance, `extract.sh --check`, `lake build`) |
| `cargo test` | 174/174 (157 unit + 4 integration + 13 in `con-ron-dump`), warning-free — one new test, `new_allocates_nothing_and_insert_allocates` |
| `scripts/provenance.py check` | green — 1 566 items, 1 730 citations at pin 3e004805 (`ensure_slots` is covered by `ron/hashmap.rs`'s `//! con-leche: none`) |
| `scripts/extract.sh` | zero Aeneas errors, zero warnings; externals still exactly **1 type, 4 `Rc` fns**, both templates byte-identical |
| `cd proof && lake build` | 2 108 jobs, zero errors, no `ConRon` warning; `Refine/HashMap.lean` re-proved, axiom census unchanged |
| `scripts/diff-fixtures.sh --timeout=60` | **315 agree, 0 differ**, 0 timed out, 33 skipped, 9 s |
| `init` | accepted at the numbers above |

#### Left for next time

* **`allocate_slots` and the allocator are now tied at ~19 % each**, and both
  are the same phenomenon: memo tables being born and dying.  Two levers, in
  order of cheapness: re-measure `MIN_CAPACITY` 32 → 8 (see the profile note
  above), and cut the *number* of tables — `ExprNatKey`'s table and `beq`'s
  pair memo together are 15 of the 19 points, and both are per-call tables
  con-leche creates as `{}`, so making them longer-lived is a §3.1 memo-policy
  question for upstream, not a Rust-side one.
* **The allocation traffic itself**: arena/interning for `ExprNode` (§3.2
  lists hash-consing as allowed by the exact-state relation) and the
  `Vec<Name>`/`Vec<Level>` copies the `dup`s still make.
* **`fenv::dup`'s `O(|env|)`** — task #34's borrow-the-index design, unchanged
  in priority.
* `expr::beq_go` + `beq` + `beq_record`, task #30's lane.
* `core.decls` and Mathlib at these numbers, once the machine is free.

### Task #36 — The dump reader at Mathlib scale (2026-09-12, Opus under Fable)

P1.8's memory half.  Task #29 gave con-ron a Mathlib-sized corpus and task #19
the reader that eats it; the first full Mathlib run then sat at **17.1 GB of
RSS with phase A barely started** (the maintainer's `--stats-every 50000` log,
`fenv … rss=17142396KB` at `[A 500000/693195]`), and `con-ron-dump-check
--roundtrip` peaked at 17.5 GB.  con-leche's *whole* run peaks at 8.6 GB, so
under §7's 3× rule (26 GB) the checker had no headroom left before it had done
anything.  This task measured where those bytes were and took the ones that
were waste: **the Mathlib parse now peaks at 9.20 GB instead of 13.83 GB and
takes 13.1 s instead of ~24 s**, and the 3 GB of dump text is never in memory
at all.  Only `crates/con-ron-dump` and this file changed — the verified core,
its model and the proof are untouched.

#### 1. What one node weighs (`con-ron-dump-check --sizes`)

New in the crate: `node_sizes`, `expr_node_bytes`, `peak_rss_kb`, and the test
`the_node_sizes_are_what_the_accounting_assumes` that pins them.  `RcBlock<T>`
is a `#[repr(C)]` *model* of `alloc::rc::RcInner` — two counts in front of the
value — so the heap column is what one `Rc::new` really costs; nothing is
allocated through it and no pointer is cast to it (still no `unsafe`).

| type | `size_of` | heap block |
|---|---|---|
| `ExprNode` (`data: u64` + `kind`) | 56 | **72** |
| ` ExprKind` | 48 | — |
| `  app` payload `(Expr, Expr)` | **16** | — |
| `  const` payload `(Name, Vec<Level>)` | 32 | — |
| `  lit` payload `Literal` | 32 | — |
| `  lam`/`forallE` payload `(Expr, Expr, BinderMeta)` | **40** | — |
| `NameNode` | 40 | 56 |
| `LevelNode` | 32 | 48 |
| `PropWhen` (inline, in every binder) | **24** | — |
| `Vec<u32>` (a string), `Nat` (limbs) | 24 | — |
| `DeclC` | 64 | — |
| `ConstantInfo` / `ConstantVal` | 120 / 40 | — |
| `Expr` / `Name` / `Level` handle | 8 | — |

The 72 is the whole story at scale: 103 099 223 `E` records × 72 B = **7.42
GB**, and it is set by the *widest* variant, `lam`/`forallE`, because a
`BinderMeta` is a `PropWhen` **by value** and `PropWhenRepr::Many(Vec<Name>)`
is 24 bytes (the other four arms hide in the `Vec`'s niche).  85 % of the
nodes are `app`, which needs 16.

#### 2. The accounting, before and after (Mathlib, 3 056 189 546 B)

The census is 103 099 223 `E`, 803 303 `N`, 43 003 `L`, 4 `W`, 710 364 `V`,
10 350 `R`, 6 846 `C`, 23 988 `I`, 693 195 `D` — 105 390 276 record lines.

| the reader's structures | before | after |
|---|---|---|
| the dump text (`fs::read_to_string`) | 3.06 GB | **0** |
| the line index `Vec<&str>` (105.4 M × 16 B, `Vec` capacity 134.2 M) | 2.15 GB | **0** |
| the per-line `Vec<&str>` of tokens | one allocation per line | **0** (one reused span buffer) |
| `E` heap nodes (103.1 M × 72 B) | 7.42 GB | 7.42 GB |
| the `E` id table (`Vec<Expr>`, capacity 134.2 M × 8 B) | 1.07 GB | 1.07 GB |
| `N` nodes + their `Vec<u32>` strings | 0.07 GB | 0.07 GB |
| `L`/`W`/`V`/`R`/`C`/`I` tables and `DeclC`s | 0.10 GB | 0.10 GB |
| **accounted total** | **13.87 GB** | **8.66 GB** |
| **measured peak RSS** | **13.83 GB** | **9.20 GB** |

The two columns' agreement is the point: the accounting is not a guess, and
after the change the reader's resident set *is* the terms plus their id tables
plus one 1 MB read buffer, to within mimalloc's page overhead (0.5 GB).  The
17.5 GB quoted at the top is the same 13.83 GB plus `--roundtrip`'s 3.06 GB
re-dump string and `dag::census`'s pointer set; the 17.1 GB is it plus 500 000
declarations of phase A.

#### 3. What was waste, and what it took to remove it

**(a) The text.**  `run_lines` took a `&str`, so every caller had to hold the
whole dump — 3.06 GB for Mathlib.  The format does not need it: every
reference is *backward* and every record is one line (FORMAT.md §2, task #10),
so a single forward pass over a `BufRead` suffices.  The obstacle was purely a
borrow one, `Reader<'a>` holding `toks: Vec<&'a str>` into the input, and it is
now split in two:

* `Tables` — the nine id `Vec`s, the payload and the `pins` flag, **with no
  lifetime at all**, so it outlives every line buffer;
* `Rec<'s, 'l>` — one record's cursor: `&'s mut Tables`, the line `&'l str`,
  the span slice, `pos`, `line_no`.  All forty-odd record functions moved to it
  unchanged but for `self.x` → `self.st.x`.

`next_tok` copies `self.line` into a local `&'l str` *before* indexing, so the
token it returns outlives the `&mut self` borrow and the record functions can
still match on a token while they push — the one trick the whole refactor
needed.

**(b) The line index.**  `let rest: Vec<&str> = lines.collect()` was 2.15 GB
of Mathlib's peak for nothing: the pass is forward and needs one line at a
time.  Gone in both drivers.

**(c) The per-line token `Vec`.**  `line.split(' ').collect()` allocated a
`Vec<&str>` per record — 105 M allocations.  `split_spans` writes `(u32, u32)`
byte spans into **one** buffer instead; spans carry no lifetime, which is
exactly why the buffer can be reused across a `read_line` that refills the
line.

The driver is now `Session::feed(line, line_no)` per line, with two loops over
it: `run_lines_str` (a `&str`, for the round-trip tests and the pin reader) and
`run_lines_read` (any `BufRead`).  They share every record function, and they
are held to the same *messages and line numbers* by
`the_streaming_driver_agrees_with_the_string_one`, which runs thirteen inputs —
the kitchen sink, empty files, a missing footer, a bad header, a wrong footer
count, content after the footer — through both and asserts `Result` equality.
The one subtlety is that a file ending in `'\n'` has one more `'\n'`-separated
piece than it has lines, which the missing-footer message's line number is
computed from, so the streaming driver counts that phantom piece too.

**(d) Two copies of anything?  No.**  The id tables hold 8-byte `Rc` handles,
never second copies — that is what `con-ron-dump-check`'s DAG census has been
asserting since task #19 (reached nodes == record counts, on all 315 fixtures
and on Mathlib) — and they are dropped the moment the parse returns
(`parse_decls_*` moves `decls` out of `Tables` and drops the rest).  They
cannot be dropped *earlier*: `V`, `I` and `D` records reference `E` and `N` ids
to the very last line of the file, so no prefix of the stream lets the reader
conclude that a kind is finished.  Shrinking them is not worth it either — the
non-`E` tables together are 0.02 GB; `E`'s 1.07 GB is 0.25 GB of `Vec`
doubling slack over the 0.82 GB it must hold, and a chunked table would buy
back that 3 % at the price of an indirection in the hottest loop of the parse.

#### 4. What the reader pays that is *not* the reader's to fix

7.42 GB of the 8.66 is `ExprNode` heap blocks, and every byte of it is decided
by core types this crate may not touch (§3.4, and the brief).  For the record,
with the numbers a repacking would buy at Mathlib scale:

| change | `ExprNode` | block | Mathlib saving |
|---|---|---|---|
| today | 56 | 72 | — |
| `BinderMeta`'s `PropWhen` behind a handle (`lam`/`forallE` payload 40 → 24, so `const`/`lit`'s 32 sets the width) | 48 | 64 | **0.82 GB** |
| that, plus `const` and `lit` payloads behind a handle (`app`'s 16 sets the width) | 32 | 48 | **2.47 GB** |

Lean pays 8 bytes of object header plus the fields, so con-leche's `app` node
is ~32 B against con-ron's 72; the second row would put the *terms themselves*
within 1.5× of con-leche, which is what §7's rule asks of the whole run.  Both
rows change `Expr`'s shape and therefore the model and the refinement proof —
a §3.1/§3.2 question for the core, not a tooling one — and neither is needed
for the 3× budget now that the parse is 9.2 GB of 26.

#### 5. The two RSS readings the brief asked for

`con-ron-check` now prints, on every run,

```
  peak RSS after parse 8989 MB, after check … MB  (VmHWM)
```

from `/proc/self/status`, and `--parse-only` stops after the reader and prints
the first of them alone — the parse half of the budget, measurable without a
checker run.  `con-ron-dump-check` gained `--parse-only` (stream the file, no
DAG census, no re-dump: the *measurement* mode) and `--sizes` (§1's table),
and ends every report with the run's `VmHWM`.  `--parse-only` and
`--roundtrip` are exclusive, and a `con-ron-pins/1` file (tiny, no streaming
driver) falls back to the in-memory path.  The fixture gate still runs the
default mode, because the DAG census and the byte-exact round trip are the
properties FORMAT.md §6 asks for.

#### 6. Before and after, measured

`/usr/bin/env time -v`, `ulimit -v` per the brief (3 GB `init`, 5 GB `core`,
26 GB Mathlib), one process at a time; "before" is the task-#35 binary built
from the same tree (`_tmp/task36/before-*`).  Maximum RSS as `time -v` reports
it, its kbytes read as decimal MB/GB the way this log's earlier entries do —
the binaries' own `VmHWM` line divides by 1024 instead, so `time -v`'s
9 204 MB and the binary's `8989 MB` are the same number.

| run | before | after |
|---|---|---|
| `dump-check --quiet` `init` (in-memory, with census) | 861 MB, parse 1.03 s | 832 MB, parse 0.63 s |
| `dump-check --parse-only` `init` | — | **562 MB**, parse 0.72 s |
| `dump-check --quiet` `core` (in-memory, with census) | 1 733 MB, parse 2.31 s | 1 587 MB, parse 1.45 s |
| `dump-check --parse-only` `core` | — | **1 135 MB**, parse 1.52 s |
| `con-ron-check --pins` `init` (full run) | 1 004 MB, 64.9 s | 1 007 MB, 61.2 s |
| … of which the parse | ~861 MB | **549 MB** (check 983 MB) |
| `con-ron-check` Mathlib, parse | **13 827 MB**, ~24 s of its 26.9 s | **9 204 MB**, parse 13.1 s |
| `dump-check --parse-only` Mathlib | — | 9 204 MB, parse 22.4 s |

`init`'s and `core`'s accounting checks out the same way as Mathlib's: 6 137
917 `E` × 72 B + a 67 MB table + 13 MB of the rest = 522 MB against 562 MB
measured (`init`), and 12 273 572 × 72 + 134 MB + 37 MB = 1 055 MB against
1 135 MB (`core`).  `init`'s *end-to-end* peak does not move, and that is
expected: its parse was never the peak — the fold is, at 983 MB — which is
also why task #32's "drop the text before the fold" was enough at `Init` scale
and stopped being enough at Mathlib's.  The parse also got **1.6× to 2.4×
faster** everywhere, from not touching 3 GB twice and not allocating 105 M
token vectors.
### Task #37 — The Rust frontend: parser and stream transformations (2026-09-12, Opus under Fable)

P4.1's first half.  con-ron was a checker without a front door: every
declaration it had ever seen came out of a `con-ron-decls/1` dump that
con-leche's own Lean frontend had produced (tasks #10, #19).  This task gives
it the frontend — the lean4export NDJSON recogniser and the pure stream
transformations `Main.lean` runs before `checkDecls` — in a **new, unverified
crate `crates/con-ron`** (library + the `con-ron` binary), so the binary reads
a raw export and prints con-leche's verdict.  §1 puts every one of those
pieces outside the main theorem, and they stay outside it.

**What landed** (8 055 lines, `crates/con-ron/`):

| file | con-leche | lines |
|---|---|---|
| `src/frontend/scan_types.rs` | `Frontend/Scan/Types.lean` (414) | 419 |
| `src/frontend/scan_fast.rs` | `Frontend/Scan/Fast.lean` (2 637), spec `Scan/Naive.lean` | 2 848 |
| `src/frontend/export.rs` | `Frontend/Export.lean` (425) | 386 |
| `src/frontend/basis_raw.rs` | `Kernel/Basis{,/Eq,/Nat,/PUnit,/Empty,/False,/Quot}.lean` | 802 |
| `src/frontend/proj_rec.rs` | `Frontend/ProjRec.lean` (373) | 643 |
| `src/frontend/nat_op_ground.rs` | `Frontend/NatOpGround.lean` (164) | 488 |
| `src/frontend/export_c.rs` | `Frontend/ExportC.lean` (1 006) | 1 573 |
| `src/frontend/prelude.rs` | `Frontend/Prelude.lean` (74) | 119 |
| `src/bin/con-ron.rs` | `Main.lean` (1 183) | 718 |

plus `scripts/diff-frontend.sh` (the byte-exact oracle), `scripts/diff-e2e.sh`
(the whole-binary differential) and two one-line root additions
(`provenance.py`'s `DEFAULT_ROOTS`, `progress.py`'s `RUST_ROOTS`).

#### The oracle, and what it found

`scripts/diff-frontend.sh` runs `con-ron --dump-decls OUT FILE.ndjson` on every
fixture and demands **byte identity** with the dump con-leche's Lean frontend
wrote for it (`_tmp/dump-fixtures/**/*.decls`, task #10).  That is a strong
test, not a smoke test: the dump's nine id spaces are dense and assigned in the
writer's own walk order, so one divergence anywhere — one interning decision,
one binder's `pw`, one `IndCaps` default, one hoist tie-break, one prelude
dedupe, one `Name.cmp` inside `PropWhen` — moves every later id and the files
differ from that byte on.

| | |
|---|---|
| rows (348 fixtures + `_tmp/corpus/init.ndjson`) | **349** |
| **byte-identical to the Lean dump** | **289** |
| **differing** | **0** |
| needs the in-process modeller (task #38) | 26 |
| no Lean dump to compare (con-leche's own frontend declines or rejects them) | 33 |
| timed out (`tower_beqpair`, the finding below) | 1 |
| bytes compared / wall | 4 990 283 / 47 s |

`scripts/diff-e2e.sh` then runs the *binary* — parse, prelude, hoist, rewrite,
fold, verdict, exit code — against `tests/{arena,e2e,annot}-expected.txt`:

| | |
|---|---|
| fixtures | **348** |
| **exit code agrees with con-leche's expectation** | **324** |
| **differs** | **0** |
| needs the modeller (task #38) | 23 |
| timed out (`tower_beqpair`) | 1 |
| wall, whole sweep | 70 s |

The 23 are the 26 above less the three whose *expectation* is 2 anyway, where
con-ron's decline agrees with con-leche by accident of the exit code.  This
sweep supersedes `diff-fixtures.sh` on two counts (which is why it is a
separate script rather than a flag): the taint-skip decline is now the
frontend's own datum instead of a hand-maintained `taint_of` table, and the 33
fixtures with no declaration list are *checked* instead of skipped.

#### The finding: `expr::beq`'s memo key is exponential on `tower_beqpair`

One fixture does not finish, and the reason is in **`con-ron-core`**, not in
the frontend.  `tests/e2e/tower_beqpair.ndjson` (con-leche task #240) carries a
shared ternary tower `S = g S S S` and an alternating pair `P = g P Q P` /
`Q = g Q P Q`; all three are structurally equal, so `Expr.hash` is the same at
every level.  Task #11's one deviation in the `beq` pair memo — the key mixes
the two nodes' **hash words**, because Aeneas cannot model addresses, where
con-leche mixes their **addresses** — therefore gives all three pairings ONE
key per level.  `probe_hit` verifies the stored pair by identity, misses, and
the walk is re-done: three full sub-walks per level.  Measured
(`beq_on_the_tower_pair_is_exponential`, an `#[ignore]`d test in
`nat_op_ground.rs` that builds the towers and times `expr::beq`):

| depth | 6 | 8 | 10 | 12 | 14 |
|---|---|---|---|---|---|
| `expr::beq` | 22 µs | 137 µs | 1.09 ms | 9.5 ms | 90.8 ms |

a clean **×2.9 per level**, i.e. `3^depth`; the fixture's depth is 60.  Task
#11's note says a key collision "costs an entry, never an answer" — it costs
the answer's *time*, and here unboundedly.

**Why no earlier task saw it, and why this one does.**  Every `Expr` con-ron
had ever been handed came out of a `con-ron-decls/1` dump, and the Lean writer
**interns by value**, so `S`, `P` and `Q` arrive as ONE node and the pairing
never happens; task #30's "eight tower fixtures accept in under a second" was
measured on exactly those collapsed dumps.  A Rust frontend builds the
stream's own DAG, in which they are three distinct nodes — which is what
con-leche's frontend builds too.  So this is a real divergence from con-leche's
behaviour on a real input, found the first time the port was given an input
con-leche's frontend had not pre-chewed.  It is out of this task's scope
(`con-ron-core` is off limits here); it is the first item of "left for next
time", and `crates/con-ron`'s test module `beq_pair_finding` carries the
demonstration so a fix has something to point at.

The same shape bit the frontend once, and there the fix was local: a
`HashSet<ExprKey>` keyed by VALUE (con-leche's `Std.HashSet ExprC`) calls
`Expr.beq` on every probe whose truncated hash matches, so it puts `beq` on
pairs that are *not* equal — and an unequal comparison is never memoised at
all.  `nat_op_ground::ExprKey` is therefore keyed by the node's **address**
(hashed and compared, never dereferenced, no `unsafe`), which is a strictly
coarser dedupe of a DAG whose nodes are distinct objects by construction; its
doc comment carries the argument.  That is what `used_consts_go` and
`occurs_const_go` use.

#### Structure, and the five deviations worth naming

1. **`keyAt` is a slice compare.**  `Fast.lean` classifies a key by its first
   byte and its length and then compares the rest with an unrolled chain of
   byte literals (`lit1`…`lit10`, con-leche task #264) because a Lean string
   literal in that position is a heap object.  Rust has no such cost, so
   `key_at` matches the key's byte slice against `b"…"` patterns — which is
   `keyOf`/`keyTable` of `Naive.lean` at `Fast.lean`'s speed — and carries the
   citations of `keyAt` and of all ten `litN` helpers.
2. **The slot loop is factored out once** (`next_member`), as `naiveObjLoop`
   factors it in the *specification*, instead of being written out per object
   as `Fast.lean` does; and the four `[{…}, …]` list loops are one generic
   `scan_obj_list_loop`, as `naiveListLoop` is.  Each `scan_*_loop` is still
   its own function with its own `seen` bits and its own required mask, so it
   lines up with its Lean twin key for key.  `Scan/Naive.lean` is the
   specification of the whole module and every item cites its `naive*`
   counterpart beside its `Fast` one.
3. **Numbers are `u64`.**  `readNat`/`readNat64`/`readNatAt` collapse into one
   `read_nat_at` that fails with a new `ErrTag::IndexOverflow` rather than
   growing into a bignum; only `natVal` is unbounded, and it keeps its decimal
   digits through the syntax record and becomes a `ron::Nat` in `export_c`
   through `con_ron_dump::natdec`.  That is task #19's split, one layer earlier.
4. **The raw basis pins are in this crate** (`basis_raw.rs`).  con-ron-core
   carries the *annotated* blocks (`basis_tables`, task #22) and those are the
   wrong ones to match a stream against: `ConstantInfo.canon` resets binder
   metadata and `IndCaps` but compares a recursor rule's install-computed
   fields verbatim, and the annotated `Nat.rec` rule carries `ctorParams = 2`,
   `k = true`, `paramsBlind = true` where a parsed one carries the
   placeholders.  A stream's `Nat` block would never match its pin — a verdict
   divergence, not a cosmetic one.  The module's test asserts exactly that: the
   six blocks have the annotated tables' member names in the same order, and
   four of the six fail `canonEq` against them.  con-leche splits the same two
   modules for the same reason (`Kernel/Basis.lean` sits *below* `TypeChecker`,
   `Kernel/BasisA.lean` above).  Should a later task need the raw pins inside
   the verified core, the module moves there unchanged.
5. **`M (StateD ⊕ RecordVerdict)` becomes `Result<(), LineErr>`** over a
   `&mut StateD`: one error channel with two arms instead of a monad over a
   sum, and the state threaded by mutable reference instead of returned.
   con-leche threads it linearly for the reason Rust's `&mut` gives for free
   (`ExportC.lean`'s task-#78 note: a handler that closes over the state holds
   it at RC 2 and every insert inside copies it).

#### What is skipped, and where the skip is

**The in-process modeller** (`Frontend/InModel/*`, 2 440 lines) is task #38.
`export_c::process_ind_decl_d` reaches exactly the point where con-leche calls
`InModel.generate` — the `InModel.wants` test, ported as `in_model_wants` off
the scan records (its two fields, `types.length` and `numNested`, are the scan
record's own, so neither `BlockRec` nor `blockRecOf` is needed yet) — and
declines with `in-process model of <T>: the in-process modeller is not ported
(con-ron task #38); the block is mutual or nested`.  Nothing is silent:

* such a stream exits 2 with that message, and both differential scripts count
  it in its own `INMODEL` row;
* `CON_LECHE_INMODEL_CENSUS=1` still works and is how to enumerate the blocks
  a stream needs #38 for — `init.ndjson` has 1 (`Lean.Syntax`), `core.ndjson`
  has 45;
* `CON_LECHE_INMODEL=0` means what it means in con-leche: the block is pushed
  bare and the *fold* declines it at the install, having found no route.

`init.ndjson` is therefore an `INMODEL` row rather than an accept: con-leche's
own dump of it contains `Lean.Syntax`'s 30 generated `_model` records, so byte
identity is not even askable before #38.  The fixture rows prove the parse on
289 streams instead.

Four `StateD` fields exist only to feed the modeller and are **not** ported:
`constTypes` and `heights` (the sort inferer's and the generated definitions'
hint source), `indBlocks` (the nested rung's container shapes) and `inModelGen`
(`CON_LECHE_INMODEL_DUMP`'s debug gate); `noteDecl` and `blockRecOf` exist only
to fill them and are not ported either.  They have no other reader anywhere in
con-leche, so nothing in this task's scope changes, and keeping them would hold
every declaration's type in a hash map for the whole run — at Mathlib scale,
for nothing.  `pushGenD`, `noteGen` and `noteProjIota` ARE ported, because they
are the modeller's *interface* to the parse state and #38 should only have to
call them.

**`Frontend/ExportWrite.lean` is not needed** and is the one source file on the
task's list that got no port: it is the checker's own *annotated* NDJSON
writer, the output path `lake exe con-leche-annot` uses to produce the
`tests/annot` fixtures, not something a checker reads.  con-ron reads those
fixtures like any other stream — all 15 of them are byte-identical rows above.

**`ProjRec.lean` is ported but cannot fire yet**, and that is con-leche's own
rule rather than a shortcut.  The rewrite needs the field's elimination level,
which is not syntactic in the projection's codomain: it is read off the
artifact `T._model.proj_i.iota`, and since con-leche task #219 the ONLY source
of that artifact is the in-process modeller.  So `proj_levels` is empty until
#38 and `proj_rewrite_d` always answers `None` — "no artifact, no rewrite", the
declaration stays as parsed and declines as before.  What *does* run on every
inductive record of every stream is the owner census (`proj_rec_owners`, with
`occurs_const_fast` over every constructor binder domain), and its recognisers
are unit-tested.

**Two Rust-side deliberate absences in the binary**: `--jobs=<n>` is validated
exactly as con-leche validates it and then **ignored** — the check phase is
sequential, and a run says so on stderr rather than letting a log mistake it
for a pooled one — and the `Prop`-indexed driver evidence (`InstallRun`,
`GroupChecked`, `FullyChecked`) that `checkDeclsIO` carries is not ported,
which is §3.7's existing skip for that family.  Two flags are con-ron's own:
`--pins FILE` (§3.6's pin-list parameter, task #31, because con-leche computes
`natOpPinSets` at elaboration time and the port takes it as data) and
`--dump-decls OUT` (the oracle above).

#### Scale

`CON_LECHE_INMODEL_CENSUS=1` stops after the parse, which is how the parse is
timed on a stream whose blocks the modeller would want.  Under
`ulimit -v 2600000`/`5000000` (1 GiB of that is the thread's stack
reservation), on a machine with another agent's Mathlib run on it:

| export | bytes | lines | decl records | parse | peak RSS | con-leche's whole run (`_tmp/corpus/baseline.md`) |
|---|---|---|---|---|---|---|
| `init.ndjson` | 347 714 179 | 6 490 422 | 57 977 | **1.29 s** | 587 MB | 59.4 s, 481 MB |
| `core.ndjson` | 747 809 047 | 13 229 044 | 163 396 | **3.07 s** | 1 183 MB | 149.6 s, 1 243 MB |

So the recogniser runs at **250–270 MB/s** and the resident set is the parsed
`DeclC` graph, not a copy of the input: the reader asks the handle for 4 MiB at
a time, carries at most one incomplete line into the next chunk, and never
seeks, re-opens or asks for the file's size — so the source may be a pipe, and
con-leche task #180's "no temporary files, anywhere" holds.
`chunking_does_not_change_the_parse` pins the chunk boundary at chunk sizes 1,
2, 7, 8, 13 and 64 bytes.  For comparison, the Lean frontend needs 18.7 s and
2 425 MB to parse and write `init` (task #29's `dumps.md`), and con-leche's
whole `init` run fits in 481 MB — so the parse is inside CLAUDE.md's 3× budget
on both rows.

Mathlib's 6 GB export was **not** parsed: another agent's Mathlib measurement
had the machine, and CLAUDE.md allows one heavy run at a time.  It is the third
item of "left for next time".

#### Two notes for whoever continues

1. **The prelude is the frontend's own integration test, and it passed
   first.**  `frontend::prelude`'s two tests parse the committed
   `pins/leanprover-lean4-v4.33.0.prelude.ndjson` through the whole chain and
   assert that all six pinned basis blocks came out as `basisDecl`s and that
   `Bool` and `And` came out as ordinary inductive records.  That exercises the
   byte recogniser, the index tables, the smart constructors, `canonEq` and
   `basis_raw` together, and it was green before any fixture was run — which is
   why the first fixture compared byte-identical on the first try.
2. **`scripts/gates.sh` needed no change.**  `cargo build`/`cargo test` run at
   the workspace manifest, so the new member is covered; `lint-rust-style.sh`
   is invoked on `crates/con-ron-core/src` only and `extract.sh` names that
   crate explicitly, so both are already scoped away from the unverified
   frontend.  What DID change is the two citation roots — `provenance.py`'s
   `DEFAULT_ROOTS` and `progress.py`'s `RUST_ROOTS` — because §3.7's `update`
   mode is the only sync signal the frontend will ever have.  The cherries
   table consequently starts counting: **5 525 of 8 093 Lean lines translated
   (68 %)**, the residue being `InModel/*` (2 057), `ExportWrite` (169),
   `Scan/Naive`'s reference-only half (164) and `Main.lean`'s pool (86).
   One more thing needed saying out loud: `con-ron` declares no
   `#[global_allocator]`, because it links `con-ron-dump` (for the dump writer
   and the pin reader) and that crate already declares task #35's mimalloc —
   two in one program is a hard link error, which is how this was found.

#### Gates

| gate | result |
|---|---|
| `scripts/gates.sh` | all 6 OK (`cargo build`, `cargo test`, lint, provenance, `extract.sh --check`, `lake build`) |
| `cargo test` | 176/176 (157 unit + 4 integration + **15** in `con-ron-dump`), warning-free — two new tests |
| `scripts/provenance.py check`, `lint-rust-style.sh` | green, and untouched: both are scoped to `crates/con-ron-core/src` (task #19) |
| `scripts/extract.sh --check` | trivially green — the core and its model are byte-identical |
| `scripts/diff-fixtures.sh --timeout=60` | **315 agree, 0 differ**, 0 timed out, 33 skipped |
| `scripts/dump-check-fixtures.sh` | 315 dumps, 0 failures, DAG exact 315/315, round trip byte-identical 315/315 |

#### Left for next time

* **The full Mathlib run**, now that the parse leaves 17 GB of the 26 GB
  budget to the fold; the maintainer's run died in phase A at 17.7 GB.
* **`ExprNode`'s 72 bytes** — §4's table, in the core, with the model and the
  refinement proof behind it.  It is the only item left in the reader's
  accounting, it is 86 % of it, and the `BinderMeta` row is nearly free (a
  `PropWhen` handle, no change to any operation's arm structure).
* The `E` id table's 0.25 GB of `Vec` slack, if a chunked table ever measures
  free in the parse loop.
* `con-ron-check --stats-every`'s `rss_kb` still reads *current* RSS from
  `/proc/self/statm` (the periodic column wants that); the two new numbers are
  `VmHWM` from `peak_rss_kb`.  Two functions, on purpose.
| `cargo build` (`-D warnings`) | clean |
| `cargo test` (`-D warnings`) | 207 pass, 1 ignored (the exponential measurement), 0 fail; 33 of them new |
| `scripts/lint-rust-style.sh` | clean (scoped to `con-ron-core`) |
| `scripts/provenance.py check` | 1 828 items, 2 035 citations, all current at the pin |
| `scripts/extract.sh --check` | clean (`con-ron-core` untouched) |
| `cd proof && lake build` | clean |
| `scripts/diff-frontend.sh --corpus` | **289 byte-identical, 0 differ**, 26 INMODEL, 33 no dump, 1 timeout |
| `scripts/diff-e2e.sh` | **324 agree, 0 differ**, 23 INMODEL, 1 timeout |

Neither differential script is in `scripts/gates.sh`, for the reason
`dump-check-fixtures.sh` and `diff-fixtures.sh` are not (tasks #19, #28): both
need the Lean dumps and the arena tarball, which the gate deliberately does not
require.

#### Left for next time

* **`expr::beq_key`'s hash-word key is exponential on `tower_beqpair`** (the
  finding above).  The fix is in `con-ron-core` and has to stay inside the
  Aeneas subset, so it is not "use the address": the honest options are a memo
  entry that holds a *list* of pairs per key (so a probe miss does not evict
  the entry that would have hit) or recording completed `false`s as well —
  both are §3.1 memo-policy questions with a `Refine/Expr.lean` obligation
  attached.  Until then `tower_beqpair` is the port's one known
  non-terminating fixture, and both differential scripts report it as a
  timeout rather than hiding it.
* **The in-process modeller** (task #38): `InModel/{Kit,Mutual,Nested}.lean`,
  2 440 Lean lines, the 26 INMODEL fixtures and `init.ndjson` as its gate.  The
  four state fields and two functions it needs are named above.
* **Mathlib's parse**, and then the whole binary on Mathlib against
  `_tmp/corpus/baseline.md`'s 12.8 T instructions — which is the P4.2
  comparison and wants the machine to itself.
* **The thread pool** for the check phase (`--jobs`), P4.1's last piece.
* **The parser's refinement against `Scan/Naive.lean`** (P4.3, optional): every
  item of `scan_fast` already cites its `naive*` specification, so the
  statement to prove is written down.

### Milestone — Mathlib accepted by the Rust checker (2026-09-12, Fable)

`con-ron-check --pins … _tmp/corpus/mathlib.decls` at master `b72b734`
(tasks #1–#37: after the reader streaming of #36, before the node
repacking of #38), release build with mimalloc, `ulimit -v 26 GB`
(3× con-leche), one thread:

| Mathlib, `--verified` | con-leche `-j1` | con-ron |
|---|---:|---:|
| verdict | accepted 691 123 | accepted 693 195 |
| `instructions:u` | 12 816 G | **12 410 G** (0.97×) |
| wall | 1 228 s | 1 947 s (1.59×) |
| max RSS | 8.60 GB | 18.78 GB (2.18×) |

Same verdict on all of Mathlib.  The count differs by exactly the 2 072
in-process model records: the dump carries them as fold declarations
indistinguishable from stream records (task #29's census), and the verdict
line counts stream records; the standalone `con-ron` binary (task #37)
has the distinction.  Fewer instructions than con-leche but 1.6× the wall
time at equal instruction count is memory traffic: the 72-byte term node
(task #36's accounting; task #38 repacks it to 48) and the reader's tables.
The earlier 90-minute timeout was the pre-#34 binary under a buffered
stdout; `--stats-every` output now flushes.

Wall-time ranking for the next steps: node size (#38), then the
`allocate_slots`/memo-table churn (#35's remaining 113 G), then the
parallel check phase (con-leche's `--jobs=8` is 337 s), which needs a
decision on `Rc` vs `Arc` in the core (§3.2: `Rc` is not `Send`; con-leche
sidesteps atomic counts by marking the installed environment persistent).

### Task #38 — 48-byte term nodes (2026-09-12, Opus under Fable)

P1.8's last reader item, and the one task #36 left as *the* core-type
question: `ExprNode`'s heap block was **72 bytes**, 7.42 GB of Mathlib's
9.20 GB parse peak, and 85 % of the nodes that pay it are `app`s that need
16.  The block is now **56 bytes** — the `init` parse peaks at 476 MB instead
of 548, `core` at 924 instead of 1 108, `init` end to end at 839 MB instead
of 977 and `core` at 2 175 instead of 2 506 — and `Refine/Abs.lean` is
**byte-identical**, because `Rc<T>` erases to `T` (§3.2) and every handle this
task added is erased with it.

It is 56 and not the 48 the brief asked for, and §3 says exactly why: three
`ExprKind` arms are 24 bytes for reasons no handle removes cheaply.  Task
#36's §4 table, which promised 48, had forgotten that `letE` and `proj` are
24-byte arms too; the honest saving of this repacking is 16 bytes a node, not
24.

A **second, unrelated change rode along** at the coordinator's request, in the
same file: task #37 found that the `beq` pair memo (task #30) does not work on
the one fixture con-leche wrote for it, because the port keys it on hash words
where con-leche keys on addresses.  §7 below is that fix — a bucket per key —
reported separately because it is a correctness change, not a layout one.

#### 1. The layout, before and after

Three payloads were wider than the three-handle arms and so set `ExprKind`'s
width for all ten; each went behind an `Rc`, which is one word:

| `ExprKind` arm | payload before | payload after |
|---|---|---|
| `bvar(u64)`, `sort(Level)` | 8 | 8 |
| `fvar(u64, Expr)`, `app(Expr, Expr)` | 16 | 16 |
| **`const(Name, Vec<Level>)`** | **32** | **16** — `Rc<Vec<Level>>` |
| **`lit(Literal)`** | **32** | **16** — `Rc<Nat>`/`Rc<Vec<u32>>` inside |
| **`lam`/`forallE(Expr, Expr, BinderMeta)`** | **40** | **24** — `Rc<PropWhen>` |
| `letE(Expr, Expr, Expr)` | 24 | 24 |
| `proj(Name, u64, Expr)` | 24 | 24 |
| `BinderMeta` | 24 | 8 |
| `Literal` | 32 | 16 |
| `ExprKind` (widest arm + discriminant) | 48 | **32** |
| `ExprNode` (`data: u64` + `kind`) | 56 | **40** |
| its `Rc` block (+ two counts) | 72 | **56** |

Three things did *not* change, on purpose: the packed `data` word and every
accessor's semantics (the smart constructors changed internally only), the
**arm structure** — `ExprKind::Const(n, us)` is still a two-field pattern,
because the handle is around the `Vec` and not around the pair, and `us`
derefs to a `&Vec<Level>` at each of the port's 106 read sites — and the
nested literal patterns, `ExprKind::Lit(Literal::NatVal(n))` still binding
because the handles are *inside* `Literal`.  That is what kept the proof diff
at one `Rc` step per unfolded constructor: boxing the whole `Literal` would
have forced `match &**l` inside `core_c`'s pair matches and restructured the
generated match trees.

`literal_dup` and `binder_meta_dup` are now reference bumps (`Rc::clone`)
where they were a limb copy, a `Vec<u32>` copy and a `PropWhen` copy —
cheaper in the binary *and* one step shorter in the model, where `Rc::clone`
is the identity outright.  Building a datum goes through three new
constructors, `expr::binder_meta`, `expr::literal_nat` and
`expr::literal_str`, which is where the handles are taken.

#### 2. The reader shares the binder data (`con-ron-dump`)

A handle is only free if the datum behind it is shared, and for
`lam`/`forallE` it is: the dump's `W` id space holds **3 records for `init`, 4
for Mathlib**, so `Reader::bm_ref` hands every binder an `Rc::clone` of one of
a handful of entries and the parse allocates no `PropWhen` at all.
`Tables::pws` is a `Vec<BinderMeta>` now; `pw_ref` — which a `V` record's
`sortZ` still wants by value — copies out of the handle, on the rare side
(710 364 `V` records against 13.4 M binders at Mathlib scale).
`node_sizes()` and `the_node_sizes_are_what_the_accounting_assumes` were
updated to the real arm types, and gained the `letE`/`proj` rows that would
have caught task #36's arithmetic slip.

#### 3. The accounting, and why 56 and not 48

`awk '$1=="E"{c[$3]++}'` over the three dumps, with the `E` totals task #36
quotes:

| kind | `init` | `core` | Mathlib |
|---|---|---|---|
| `app` | 5 223 210 | 9 585 883 | 88 022 053 |
| `lam` | 539 042 | 1 534 956 | 8 069 579 |
| `forallE` | 301 502 | 906 103 | 5 327 163 |
| `const` | 57 033 | 162 407 | 1 391 293 |
| `letE` | 11 372 | 53 995 | 228 415 |
| `proj` | 3 412 | 16 256 | 34 867 |
| `lit` (str + nat) | 2 081 | 13 360 | 23 766 |
| `sort`, `bvar`, `fvar` | 265 | 612 | 2 087 |
| **total `E`** | **6 137 917** | **12 273 572** | **103 099 223** |

so the ledger is 16 bytes off every node, against one 40-byte `Rc` block per
`const` node (a `Vec` header and two counts) and one per literal payload:

| | `init` | `core` | Mathlib |
|---|---|---|---|
| nodes, −16 B each | −98.2 MB | −196.4 MB | −1 649.6 MB |
| `const` level lists, +40 B each | +2.3 MB | +6.5 MB | +55.7 MB |
| literal payloads, +40 B each | +0.1 MB | +0.5 MB | +1.0 MB |
| binder data (3, 4, 4 of them, shared) | ~0 | ~0 | ~0 |
| **predicted** | **−95.8 MB** | **−189.4 MB** | **−1 592.9 MB** |
| **measured** (`--parse-only` peak, ×3 runs, identical) | **−72 MB** | **−184 MB** | not run |

`core`'s columns agree; `init`'s measured saving is 24 MB short of the
accounting, which is mimalloc keeping slack per page and not the terms (the
accounting is the payload, and 56-byte blocks pack differently from 72-byte
ones).  Mathlib was not run — the maintainer's is in progress — so its column
is a projection: a parse peak of **7.6 GB** instead of 9.20.

**Why the last 8 bytes are not worth taking.**  `ExprNode` is 40 = 8 (`data`)
+ 8 (discriminant) + 24 (widest arm), and *three* arms are that 24:
`lam`/`forallE` (two handles and the datum's), `letE` (three handles) and
`proj` (a name, a `u64`, a handle).  Rust gives an enum with ten
data-carrying variants a full 8-byte tag — there is no niche to fill — so a
48-byte block means a handle for those three arms too.  At Mathlib scale that
buys 8 B × 103.1 M = 825 MB and costs a 40-byte block per binder
(13 396 742 of them, 536 MB), per `letE` (9 MB) and per `proj` (1.4 MB):
**net 278 MB**, 3 % of the parse peak, in exchange for a pointer chase on the
checker's hottest arm and for changing `ExprKind`'s arm structure — which is
the abstraction, 187 binder pattern sites in the port and a constructor case
in every `beq`/`ExprOps` proof.  That is the trade this task declines.

#### 4. Measured

`/usr/bin/env time -v` and `perf stat -e instructions:u`, `ulimit -v` per the
brief (3 GB `init`, 5 GB `core`), `--pins _tmp/dump-fixtures/pins.dump`,
"before" being the task-#36 binary built from the same tree
(`_tmp/task38/before-*`).  **The machine was busy throughout** with the
maintainer's Mathlib run, so wall times are not comparable between columns
and instructions are the measurement of record (§7).

| run | before | after |
|---|---|---|
| `dump-check --parse-only` `init` | 548 MB | **476 MB** |
| `dump-check --parse-only` `core` | 1 108 MB | **924 MB** |
| `con-ron-check` `init`, peak after parse | 549 MB | **476 MB** |
| `con-ron-check` `init`, peak after check | 977 MB | **839 MB** |
| `con-ron-check` `init`, instructions | 596.94 G | 617.19 G (+3.4 %) |
| `con-ron-check` `core`, peak after parse | 1 106 MB | **925 MB** |
| `con-ron-check` `core`, peak after check | 2 506 MB | **2 175 MB** |
| `con-ron-check` `core`, instructions | 1 215.55 G | 1 284.55 G (+5.7 %) |

Both runs still **accept** (58 002 and 165 449 declarations, `--verified`).
`core`'s end-to-end peak is 1.75× con-leche's 1 243 MB and `init`'s 1.74×
its 481 MB, both well inside §7's 3×.  The instruction rise splits in two,
and §7 owns the larger half: the **repacking** alone is +1.2 % on `init`
(604.08 G) and +0.5 % on `core` (1 221.47 G), measured on the same binaries
before the memo change — the extra `Rc::new` the checker's own `mk_const`
does, and one load on each `us`/`m.pw` read, against `binder_meta_dup` and
`literal_dup` no longer copying — and the **memo's bucket** is the other
+2.2 % and +5.2 %.

#### 5. What it took in the model and the proof

* **`Refine/Abs.lean`: no change at all.**  `alloc.rc.Rc T` is a
  `@[reducible] def` for `T` (§3.2), so `BinderMeta.pw : Rc PropWhen` *is* a
  `PropWhen`, `Const`'s second field is a `Vec Level` and
  `Literal.NatVal`'s is a `Nat`.  `absBinderMeta`, `absExprKind`,
  `absLiteral`, `BinderMetaWF`, `LiteralWF` and every `ExprWF` constructor are
  the same text.
* **`Refine/Expr.lean`: one `Rc` step per unfolded constructor.**
  `mk_const_inv` gained one existential (`Rc::new(us)`, consumed as `rfl`);
  `lam_inv` and `forall_e_inv` gained the `m.pw` deref (one pair, `rfl`, and
  `rc_deref_eq` in their `simp only` set, without which the equation is not
  an equation yet); `literal_beq_refines`, `binder_meta_beq_refines`,
  `literal_beq_refl` and `binder_meta_beq_refl` gained
  `rc_deref_eq, bind_tc_ok` in theirs; `literal_dup_eq` and
  `binder_meta_dup_eq` got *shorter* (`rc_clone_eq, bind_tc_ok` and
  `exact h.symm`, where they used to identify a copy through
  `Nat.clone_refines`/`str_copy_eq`/`PropWhen.dup_eq`).
  **No lemma is weakened and nothing is `sorry`ed**: every statement is the
  one that was there before, and `beq_exact`/`bvar_b_raw_refines` still
  `#guard_msgs` their axiom census as `[propext, Classical.choice,
  Quot.sound]`.
* **`Refine/BasisTables.lean`: one `@[local step]` spec**,
  `expr_binder_meta_spec`, because the generated table now builds a datum
  through a function rather than with a struct literal.  Everything else
  discharged itself: its `rc_new_spec`/`rc_deref_spec`/`rc_clone_spec` steps
  already cover the new `Rc` traffic.
* `expr::str_copy`/`str_copy_from` and their two lemmas stay, though
  `literal_dup` no longer calls them: they are the crate's `Vec<u32>` copy and
  the walk is proved.

#### 6. The generator

`basis_tables.rs` is generated (§3.7, task #22), so the two constructor
spellings moved in `proof/ConRon/Gen/Emit.lean` instead:
`BinderMeta { pw: … }` → `expr::binder_meta(…)` and
`Literal::NatVal/StrVal(…)` → `expr::literal_nat/str(…)`, 84 lines of the
generated file, plus one dropped `use` in `Gen/Main.lean`'s preamble (the file
no longer names the type).  Regeneration is still a fixed point.

#### 7. The `beq` pair memo needed a bucket (folded in from task #37)

Task #37 found, while wiring the `.ndjson` frontend, that the pair memo task
#30 landed does not *work* on the one fixture con-leche wrote for it:
`vendor/con-leche/tests/e2e/tower_beqpair.ndjson` does not terminate.  The
cause is the port's one deviation from con-leche's memo, and §3.2 states it:
the key mixes the two **stored hash words**, where con-leche mixes the two
**addresses**.  A hash key collides exactly on structurally equal,
pointer-distinct objects — which is to say on the objects the memo exists
for — so with one pair per key a node compared against two partners in turn
evicts its own entry on every visit.  con-leche's fixture is built to do
precisely that (`scripts/mk_tower_fixtures.py`'s `mk_beqpair`, whose note
explains why it takes **three** arguments to bite): a shared tower
`S_{k+1} = g S_k S_k S_k` against an alternating pair
`P_{k+1} = g P_k Q_k P_k`, `Q_{k+1} = g Q_k P_k Q_k` asks `(S,P)`, `(S,Q)`,
`(S,P)` one level down, and the third query finds the entry the second wrote.
`3^n`, at n = 40.

**The fix is a bucket**, inside the Aeneas subset, with §3.2's argument
untouched:

* `BeqMap` is `ron::HashMap<u64, Vec<(Expr, Expr)>>`.  `probe_hit` walks the
  key's bucket (`probe_hit_from`, an index recursion like every other list
  walk in the port) and verifies each candidate with `pair_is` — `ptr_eq` on
  both components, exactly as before and exactly as `probeHit` does.
* `beq_record` **inserts first and extends second**: `insert` hands back what
  the key held, so the common case — a key with no bucket yet, which is nearly
  every write, since a bucket of two needs two proved-equal pairs of distinct
  objects whose hash words agree — is *one* table operation, as it was before
  the bucket, and only a real collision runs `beq_extend`.  The
  `remove`-then-`insert` spelling this replaced cost **11 % of `core`'s
  instructions** (1 355.57 G against 1 221.47 G), because
  `ron::HashMap::remove` rebuilds its chain; the shipped one costs 2.2 % on
  `init`.  The memo is still local to the top-level `beq`, whose two guards
  run before any table exists.
* **The trust argument does not move**, because what an entry *means* has not
  changed: in the model `ptr_eq` is `false`, so every candidate misses and the
  table is written and never read; in the binary a candidate is accepted only
  when it *is* the two objects being compared, and only completed `true`s are
  appended.  A bucket cannot outgrow the walk that fills it — an entry is one
  proved-equal pair of distinct objects whose hash words agree — so the memo
  stays bounded by the comparisons the descent has completed.
* In the proof `probe_hit_false` keeps its statement *verbatim* and is proved
  through two new lemmas: `pair_is_false` (one candidate misses, `ptr_eq`
  being `false`) and `probe_hit_from_false` (the scan misses for **any**
  bucket, by the measure induction the port's index recursions all use).  No
  fact about the table is needed, still not even `ron::HashMap`'s invariant,
  and `beq_arm`, `beq_go_arm`, `beq_finish_fst` and the hundred-case
  constructor induction are untouched.

`beq_on_the_beqpair_towers_is_memoised` is the fixture as a unit test: it
builds `S`, `P`, `Q` at depth 40 and asserts both orientations of `beq`, and
it does not finish before the change (measured: still running after 60 s)
against under a millisecond after it.
`probe_hit_verifies_by_identity_not_by_structure` gained the bucket half (a
second pair under the same key displaces nothing, and both are found).  The
*dumped* form of the fixture cannot show the bug and never could: the Lean
writer interns `E` records by value, so the three towers collapse to one id
and the reader hands out one shared object — which is why this is task #37's
find, and why the end-to-end confirmation belongs to its `.ndjson` route
(`scripts/diff-e2e.sh`, not in this worktree).

#### Gates

| gate | result |
|---|---|
| `scripts/gates.sh` | all 6 OK (`cargo build`, `cargo test`, lint, provenance, `extract.sh --check`, `lake build`) |
| `cargo test` | 177/177, warning-free — one new test |
| `scripts/lint-rust-style.sh` | green — no `Rc` API beyond §3.2's four, the new derefs being coercions |
| `scripts/provenance.py check` | 1 573 items, 1 737 citations, all current at pin `3e004805` (seven new items: the three constructors, `BeqBucket`, `pair_is`, `probe_hit_from`, `beq_extend`) |
| `scripts/extract.sh` | `Types.lean` +20/−20 (three types gained a handle), `Funs.lean` one `deref`/`new` step per site; **externals still exactly 1 type and 4 fns** |
| zero Aeneas errors | yes (`extract.sh` is clean, and `lake build` elaborates the output) |
| `scripts/diff-fixtures.sh --timeout=60` | **315 agree, 0 differ**, 0 timed out, 33 skipped |
| `scripts/dump-check-fixtures.sh` | 316 dumps, 0 failures, DAG exact, round trip byte-identical |

#### Left for next time

* **The full Mathlib run** — the parse should now peak at 7.6 GB of the 26 GB
  budget, leaving the fold 18 GB.
* The last 8 bytes of the node, if §3's 278 MB ever outweighs the arm
  structure.
* The memo's remaining 2.2 %: the bucket's first pair could live *inline* in
  the entry (`(EqPair, Vec<EqPair>)`), which would take the `Vec`'s allocation
  out of the common write.  Three more lines of Lean, and no change to any
  statement.
* The `E` id table's 0.25 GB of `Vec` slack (task #36's item, untouched).

### Task #39 — The in-process modeller (2026-09-12, Opus under Fable)

P4.1's second half, and the last piece of the frontend.  Task #37 gave con-ron
a front door but stopped at one door inside it: at the point con-leche calls
`InModel.generate` — the `InModel.wants` test on a **mutual or nested**
inductive block — the port declined the stream, naming the block.  That
decline is gone.  `crates/con-ron/src/in_model/` is the port of
`ConLeche/Frontend/InModel{,/Kit,/Mutual,/Nested}.lean` (2 436 Lean lines, all
`partial def`s; the construction is a port of lean-inductive-models), and
`frontend::export_c` now generates, pushes and books the `_model` family of
every such block, so the block installs through the modeled route as it does
in con-leche.

**What landed** (6 096 lines of code + 322 of tests, `crates/con-ron/`):

| file | con-leche | Lean | Rust |
|---|---|---|---|
| `src/in_model/mod.rs` | `Frontend/InModel.lean` | 48 | 56 |
| `src/in_model/kit.rs` | `Frontend/InModel/Kit.lean` | 613 | 1 000 |
| `src/in_model/mutual.rs` | `Frontend/InModel/Mutual.lean` | 456 | 1 098 |
| `src/in_model/nested.rs` | `Frontend/InModel/Nested.lean` | 1 319 | 3 942 |

plus the wiring in `frontend/export_c.rs`: the three `StateD` fields task #37
left out (`const_types`, `heights`, `ind_blocks`), `note_decl` (with
`note_decl_entries`/`note_entries`), `block_rec_of`, `note_gen_names`, and the
generator call at `process_line_core_d`'s modeller point.  `InModelDump.lean`
is **not** ported and needs no successor: it is `CON_LECHE_INMODEL_DUMP`'s
debug splice, written through `Frontend/ExportWrite.lean`'s `ExportWriter` —
the one source file task #37 deliberately left out, an output format rather
than something a checker reads.  `StateD.inModelGen`, which exists only to
feed it, stays unported with it.

#### The oracle: it is byte identity again, and it held at once

The generated model terms have to be *structurally identical* to con-leche's,
and the frontend oracle says so directly: `--dump-decls` writes the whole
declaration list, generated records included, and its nine id spaces are dense
and assigned in the writer's walk order, so one differing binder anywhere
moves every later id.

| | task #37 | now |
|---|---|---|
| fixtures | 348 | 348 |
| **byte-identical to the Lean dump** | 289 | **315** |
| **differing** | 0 | **0** |
| needed the modeller | 26 | **0** |
| no Lean dump (con-leche's own frontend declines or rejects them) | 33 | 33 |
| timed out | 1 | **0** (task #38 fixed it) |
| bytes compared | 4 990 283 | **6 905 866** |

315 is every fixture that *has* a dump to compare.  `scripts/diff-e2e.sh`, the
whole-binary differential, is likewise complete: **348 of 348 exit codes
agree, 0 differ**, where #37 had 324 agreeing and 23 declined for the missing
modeller.

The scale corpus is the same test at three orders of magnitude, and
`--corpus` now runs both rows (it used to run `init` alone, since `core` could
not be compared before the modeller either):

| stream | bytes compared | blocks modelled | generated records | dump |
|---|---|---|---|---|
| `_tmp/corpus/init.ndjson` | 165 127 796 | 1 (`Lean.Syntax`) | 30 | **byte-identical** |
| `_tmp/corpus/core.ndjson` | 344 024 887 | 45 | 2 058 | **byte-identical** |

Two rungs, two fixtures, two first tries: the ten mutual fixtures compared
byte-identical the first time `gen_mutual` compiled, and the fifteen nested
ones the first time `gen_nested` did.  That is not luck but the shape of the
task — everything the generator emits is `Expr` arithmetic over de Bruijn
frames, so a frame off by one shows up on the first fixture and a frame that
is right is right everywhere.

#### End to end, and what the modeller costs

`con-ron --verified --jobs=1 --pins …`, under `ulimit -v 2600000`/`5000000`,
on a machine with another agent's work on it:

| export | verdict | con-leche's verdict | parse+model | check | total | peak RSS | con-leche's total / RSS |
|---|---|---|---|---|---|---|---|
| `init` | accepted **57972** declarations | accepted 57972 | 1.051 s | 58.674 s | 59.729 s | 886 MB | 59.36 s / 481 MB |
| `core` | accepted **163391** declarations | accepted 163391 | 2.567 s | 154.965 s | 157.536 s | 2 414 MB | 149.64 s / 1 243 MB |

The declaration counts are `_tmp/corpus/baseline.md`'s to the digit, and they
are the first end-to-end *accepts* con-ron has produced on the scale corpus
from a raw export: #37 could only decline these two streams.  RSS is 1.84× and
1.94× con-leche's, inside CLAUDE.md's 3× budget.

The modeller's own share is small, and `CON_LECHE_INMODEL_CENSUS=1` (which
stops after the parse) against `CON_LECHE_INMODEL=0 CON_LECHE_INMODEL_CENSUS=1`
(which stops after the parse *without* modelling) measures it:

| export | parse | parse + model | model | RSS parse | RSS parse + model |
|---|---|---|---|---|---|
| `init` | 1.281 s | 1.344 s | **0.06 s** for 1 block / 30 records | 542 MB | 541 MB |
| `core` | 2.853 s | 3.050 s | **0.20 s** for 45 blocks / 2 058 records | 1 134 MB | 1 275 MB |

So 45 model families cost 0.2 s and 141 MB — 0.13 % of the run's wall and 6 %
of its peak.  What is *not* free is the declaration table the sort inferer
reads: `const_types` and `ind_blocks` hold every declaration's type and every
inductive block's shape for the whole run, and they are in **both** columns
above, so the table above does not price them.  Task #37 declined to port them
for exactly that reason and was right to, at the time; they are the parse's one
memory cost that scales with the *stream* rather than with the DAG, and there
is no way to run the sort inferer without them (con-leche pays the same).  The
absolute numbers moved down rather than up since #37 measured (init's parse
peak 587 → 542 MB, core's 1 183 → 1 275 MB) because task #38's repacked term
node landed in between and saved more than these tables cost.

#### Structure, and the seven deviations worth naming

1. **`ConstTable`, `heights` and `blocks` are `&dyn Fn`.**  con-leche's `Ctx`
   carries three Lean functions, and both generators build *overlays* over
   them — `tbl'` adds the block's own generated types for the projection
   artifacts' sort inference, `hOf` the heights of the definitions emitted so
   far.  A Lean function argument makes that free; a trait object is the Rust
   spelling of the same thing, and this crate is outside §3.4's Aeneas subset.
2. **Every memo is keyed by the node's ADDRESS**, where con-leche's
   `Std.HashMap Expr _` keys by value.  A memo answer here is a function of
   the node, so an address key is a strictly coarser dedupe of the same
   answers — and it keeps `expr::beq` off the probe path.  That is task #37's
   finding applied prophylactically: `specFamGo`, `specAllGo`, `substParams`,
   `mentionsAnyGo` and `maxHeightGo` are exactly the walks con-leche wrote the
   `tower_*` fixtures for, and a value-keyed memo would have put `beq` on
   every probe of a depth-60 shared tower.  (`nat_op_ground::ExprKey`, task
   #37's, is reused verbatim.)
3. **Nat subtraction is `saturating_sub`** throughout (`kit::sub`).  The
   generators are written in de Bruijn arithmetic — `nF - 1 - i`,
   `M - 1 - m`, `args.length - nIdx`, `o2 - M - n` — and Lean's `Nat` truncates
   where Rust's `u64` wraps in release and panics in debug.  Every one of the
   ~120 subtractions goes through `sub`, so an out-of-range index gives
   con-leche's `0` and the fold rejects the record, rather than the port
   producing a different term or dying.
4. **`genNested`'s ~40 local `let f := fun …` definitions become methods of a
   `Gen` record**, and the iota proof's five (`uOf`, `eOf`, `carrOf`, `rOf`,
   `ihApp`, plus `stmtAt`/`nest`/`goT`) methods of an `Iota` one.  Lean closes
   them over `genNested`'s locals for free and lets them call each other and
   recurse; Rust closures cannot do both, so the captured locals are the
   struct's fields and each closure is a method with the same name and the
   same arguments.  This is the single largest reason `nested.rs` is 3.0× its
   Lean (`kit.rs` is 1.6×, `mutual.rs` 2.4×).
5. **The generalisation state of the iota proof is a slice.**  `stmtAt` takes
   `zs`/`hs` as `&[Option<Expr>]` indexed by field position where con-leche
   passes `Nat → Option Expr`; every caller indexes below `nF`, so the slice
   is the same function tabulated, and `nest`'s two rebuilds of it are two
   `Vec`s instead of two closures over closures.
6. **`note_gen` is split in two.**  `push_gen_d` takes the `DeclC` by value
   (it is pushed into the state) and whether it *was* pushed — con-leche's
   `st'.decls.size > before` — is known only afterwards, when the record is
   gone.  `note_gen_names` takes the names read off it beforehand; `note_gen`
   is kept as the one-argument form the citation names.
7. **`Kit.recTy`/`recRhs`'s four-component tuples become `kit::KCtor`**
   (`proj_rec`'s deviation 3, same reason: `·.2.2.2` is not something to
   transliterate).

#### Three dead expressions in the cited Lean, dropped

Reading 2 436 lines of `partial def` closely turns up three places where
con-leche computes something and throws it away, all of them harmless and all
of them silencing an unused-variable warning rather than doing work:

* `Nested.lean:300-301` — `if pins.any (fun p => (stripAllPis p).1.length > 0 && false) then throw "unreachable"`.
  The `&& false` makes the predicate constantly false, so the `throw` is
  unreachable by construction.  Not ported.
* `Nested.lean:546` — `let _ := groupOf`, the only use of a `groupOf` defined
  twelve lines earlier.  Neither is ported.
* `Nested.lean:717` and `1270-1272` — `let _ := D` in `unpackMinors`, and a
  `fd.liftLooseBVars (o2 + 1 - 1) 1 |> … |> fun _ => fd.liftLooseBVars o2 1`
  pipeline in the projection motive whose first two stages are discarded.
  The port keeps only the value: `lift_loose_bvars(o2, 1, fd)`.

#### What needed a bound, and what did not

The brief asked what in the `partial def`s needed one.  The answer is
**nothing that con-leche does not already bound itself**, and the reason is
worth writing down:

* `sortCeil` is the one `partial def` in the family that is *not* structural —
  it walks up a type tower and down a `∀` telescope — and con-leche already
  gives it a fuel, 128 at `idxSort`'s call.  The port carries the same
  constant.  A stream that exhausts it declines, naming the index whose sort
  no ceiling bounds (task #227's residual).
* every other recursion — `specFamGo`, `specAllGo`, `substParams`,
  `mentionsAnyGo`, `maxHeightGo`, `inferTy`, `congrChain`, `nest`, `goT`,
  `minorsPis`/`minorsLams`, `ihPis` — is structural on the term or on a list
  whose length is a field count, and the memo turns the term walks into DAG
  walks.  Their depth is the term DAG's, which the binary's 1 GiB stack
  reservation (task #37's `STACK_BYTES`) already covers: it is the same bound
  the fold and `canon_expr_eq_fast` run under.
* `betaHead` and `freshLevelName.go` are the two that *could* diverge in
  principle — a self-application and an exhausted name space respectively —
  and both diverge in con-leche too.  Adding a bound would have turned a hang
  into a *decline*, i.e. a verdict divergence from the reference on an input
  neither implementation can handle; the port therefore transliterates them
  and says so here.

#### Two notes for whoever continues

1. **The three `StateD` fields are the modeller's only interface to the
   parse, and `note_decl` is where they are filled.**  It runs on every
   record `push_decl` actually pushes (con-leche's `.inl (noteDecl … d)`), the
   built-in prelude included via `state_d_init` — and the prelude fold had to
   collect its entries *first*, because in Rust the fold would borrow the
   state it writes into, where Lean's value semantics make
   `prelude.decls.foldl noteDecl st` two objects.
2. **The `INMODEL` row of both differential scripts is retired but not
   removed.**  It now greps for the literal "the in-process modeller is not
   ported" and is expected to read 0; a generator *decline* counts as `other`
   and reddens the run, which is what makes the 26 modeller fixtures a gate
   rather than a skip list.  Both scripts' headers say so.

#### Gates

| gate | result |
|---|---|
| `scripts/gates.sh` | all 6 OK (`cargo build`, `cargo test`, lint, provenance, `extract.sh --check`, `lake build`) |
| `cargo test` | **223 pass, 1 ignored** (task #37's exponential measurement), warning-free — **13** new tests: 8 unit in `in_model::kit`, 5 in `in_model` that run the three rungs on con-leche's own `inmodel_{mutual,nested,groups}.ndjson` |
| `scripts/lint-rust-style.sh` | green, and untouched: scoped to `crates/con-ron-core/src` |
| `scripts/provenance.py check` | 1 978 items, 2 171 citations, all current at pin `3e004805` |
| `scripts/extract.sh --check` | clean (`con-ron-core` untouched) |
| `cd proof && lake build` | clean |
| `scripts/diff-frontend.sh` | **315 byte-identical, 0 differ**, 0 INMODEL, 33 no dump, 0 timeouts |
| `scripts/diff-frontend.sh --corpus` | `init` and `core` both **byte-identical** (509 MB of dump) |
| `scripts/diff-e2e.sh --timeout=60` | **348 agree, 0 differ**, 0 INMODEL, 0 timeouts |
| cherries (`scripts/progress.py`) | **7 632 of 8 093 Lean lines translated (94 %)**, up from 68 % |

The two differential scripts are still not in `scripts/gates.sh`, for the
reason tasks #19, #28 and #37 give: they need the Lean dumps and the arena
tarball, which the gate deliberately does not require.

#### Left for next time

* **The full Mathlib run**, which is now askable for the first time: the whole
  binary on the 6 GB export against `_tmp/corpus/baseline.md`'s 12.8 T
  instructions and 8.6 GB.  Mathlib has mutual and nested blocks by the
  thousand, so this task is what unblocks it — and the declaration table of
  the note above is the thing to watch, since it is the one part of the parse
  whose size is the stream's rather than the DAG's.
* **The thread pool** for the check phase (`--jobs`), P4.1's last piece and
  the whole of the 2.4× the `--jobs=8` baseline rows show.
* The residual coverage the generators decline, which is now exactly
  con-leche's residual and nothing more: infinitary nesting, a container group
  cycle (B4's own limit), a `Prop` block with a large eliminator, an index
  domain no ceiling bounds, and `Nested.lean`'s KNOWN GAP (a member whose index
  *domain* mentions a parameter gets an `_impl.rec` the fold rejects).  None of
  the 348 fixtures and neither corpus stream hits any of them; the gap is
  con-leche's to close first.
* **The frontend's refinement against `Scan/Naive.lean`** (P4.3, optional) is
  unchanged by this task: the modeller is untrusted by construction — a wrong
  record is rejected or declined by the fold, never accepted — so there is no
  `_refines` lemma owed here and never will be.

**Update after task #38** (master `04e9f25`, repacked node + memo buckets,
same run conditions): accepted 693 195; `instructions:u` **12 797 G**
(1.00× con-leche; +3.1 % from the handles' extra indirection), wall
**1 967 s** (1.60×, unchanged), max RSS **15.97 GB** (1.86×, from 2.18×).
Equal instructions and 1.6× the wall time is a memory-traffic signature;
task #41 profiles cycles and cache misses at `core` scale.
### Task #40 — The driver: progress, flags, one driver for both binaries (2026-09-12, Opus under Fable)

P4.1's last item but one, and the one that closes the **cherries** ledger.
Tasks #37 and #39 ported `Main.lean`'s front matter — the parse, the prelude,
the hoist, the rewrite, the modeller — and left what sits *above*
`check_decls`: the progress heartbeat, the retired-flag discipline,
`--no-mark-persistent`, the out-of-memory convention, and the one driver rule
that decides an exit code, the taint skip.  Worse, that rule existed **twice**
— task #28 put it in `con-ron-check` off a `--taint-skipped N` parameter, task
#37 put it in `con-ron` off the frontend's own datum — and two copies of a rule
that decides a verdict is one copy too many.  This task ports the rest and
makes the two binaries one driver.

**What landed** (`crates/con-ron/`, 868 lines of new module, 85 of them
tests):

| file | con-leche | what |
|---|---|---|
| `src/driver.rs` (new, 868) | `Main.lean` above `check_decls` | the shared driver: rendering, flag values, the retired table, the two phase loops, the heartbeat, the verdict |
| `src/bin/con-ron.rs` (720 → 586) | `Main.lean` | the raw-stream front door; the driver's pieces deleted from it, the modeller's receipt and the retired `CON_LECHE_INFER_ONLY` gate added |
| `src/bin/con-ron-check.rs` (moved here, 513 → 550) | `Main.lean` | the same driver on a `con-ron-decls/1` dump, its `--stats` reporting now a `PhaseObserver` |

`con-ron-check` **moved from `crates/con-ron-dump` to `crates/con-ron`**,
because the shared driver cannot live in the dump crate (`con-ron` already
depends on it, so the other direction is a cycle).  The binary's name and its
`target/release/con-ron-check` path are unchanged; the one script that built it
by package (`scripts/diff-fixtures.sh`'s `cargo build -p con-ron-dump`) now
builds `-p con-ron`.

#### The heartbeat, and the seam that makes one loop serve three callers

`OVERVIEW.md` §0's six line shapes are ported exactly, with `con-leche: `
replaced by `con-ron: `.  Measured on `_tmp/corpus/init.ndjson`
(`--verified --jobs=1 --pins … --progress=20000`, `ulimit -v 2600000`):

```text
con-ron: parse done: 58002 fold records — 57994 declarations after the 8 built-in prelude records (8 stream copies of prelude records dropped) t=1.050s (parse 1.050s)
con-ron: install 20000/58002 thm Lean.Grind.Linarith.Poly.combine.induct_unfolding t=4.633s
con-ron: install done: 58002/58002 declarations installed, 57362 checks pending t=6.432s (install 5.382s)
con-ron: check 20000/57362 definition String.Slice.Pattern.SearchStep._sizeOf_inst t=25.672s
con-ron: check done: 57362/57362 t=58.326s (check 51.894s)
con-ron: done: parse 1.050s, install 5.382s, check 51.894s, 1 worker t=58.326s
con-ron: accepted 57972 declarations (--verified)
```

`57972` is task #39's and `_tmp/corpus/baseline.md`'s count to the digit, and
58.3 s is inside #39's 59.7 s, so the heartbeat costs nothing measurable.
What the run *says* that no earlier one could is where the time goes: **parse
1.8 %, install 9.2 %, check 89.0 %** — which is the argument for the pool
written in the port's own numbers, and the reason the pool is the next task
rather than an optimisation.

Three details are con-leche's and were easy to get wrong:

1. **Phase A announces before, phase B reports after.**  An install line is
   printed *before* the declaration is installed, so a run that dies — an OOM,
   a timeout, a `SIGKILL` — names on its last line the declaration it died in;
   a check line is printed *after* the check completes, so "a check that is
   running is not on any line, the gap between two lines is where it sits".
2. **`<i>` is the fold position, not the record index.**  The parse folds the
   basis and `quot` blocks, drops taint-skipped records and *adds* the
   modeller's, so the two drift by a stream-dependent amount (`init`: 58 002
   fold records against 57 972 stream declarations).  Calibrate by NAME.
3. **The check line names the record**, `<kind> <name>` off `pend[k].vg` —
   which needed `ValueKind.word`, a declaration DESIGN.md §3.7 had on the skip
   list as driver-only rendering.  It is ported now, in the driver, exactly
   where `msSecs` and `declCLabel` went; all three came off the skip list, and
   con-leche makes the same split for the same reason (`declCLabel` lives
   beside the checker "because the progress heartbeat's compiled hook prints it
   too, and the two must never drift apart").

The seam is `driver::PhaseObserver`, a trait whose seven methods all default to
nothing.  con-leche prints its heartbeat from inside `installLoop`/`checkLoop`
because printing is in `IO` there; the port's loops are pure over a `&mut O`,
so `con-ron`'s `Heartbeat` and `con-ron-check`'s `Stats` (the
`--stats`/`--stats-every` reporter, which forwards to a `Heartbeat` and then
prints its own lines) are two implementations of one loop instead of two copies
of it.  `driver::check_decls_driver` is that loop, and it IS `check_decls`'
body step for step — `annot_decl_step` per record in phase A, `check_pending`
from a fresh `CState` per record in phase B — which is why the flag changes no
verdict.  A run with no flag calls `installed::check_decls` itself and comes
through no observer at all.

**The flag is tested as a no-op at scale, not argued to be one**:
`scripts/diff-e2e.sh --timeout=60` reads **348 agree, 0 differ**, and with
`--progress` it reads **348 agree, 0 differ** again.

#### The retired flags, and the two that are accepted instead

All **thirteen** spellings of `Main.lean`'s RETIRED FLAGS paragraph are
rejected with a message naming what stands in its place, from one table
(`driver::retired_flag`) both binaries consult, and each exits 3 without
reading the input.  Task #37 had six of them and generic messages for two; the
seven new ones are `--set-model`, `--set-model=p`, `--set-model=r`,
`--no-model`, `--tt-model`, and the `=`-carrying `--core=<c>` and
`--check-range=<r>`, which used to answer a bare "X is retired".  The rule is
con-leche's and is about *the port's* verdicts too: a verdict's provenance must
be readable off the invocation, so a retired spelling is never a silent alias.
`every_retired_spelling_names_its_replacement` pins all thirteen and asserts
that the eight live spellings — three of which are prefixes of retired ones —
are not caught by it.

Two flags go the other way, and for the same discipline:

* **`--jobs=<n>` is validated and not acted on**, as at task #37, but the
  `--progress` summary now says `1 worker` whatever `<n>` was.  That line is
  the one place a log could have been made to lie about the lane, so it
  reports the port's own truth.
* **`--no-mark-persistent` is accepted and a no-op, and a run that passes it
  says why.**  con-leche's mark is `unsafe Runtime.markPersistent` on the
  installed environment at the phase boundary: the graph is read-only from
  there on, handing it to a worker task makes the **Lean runtime** mark it
  multi-threaded, and every reference count on it then becomes an atomic
  read-modify-write on cache lines every worker touches — worth 18–32 % of
  wall time on the pool.  Every word of that is about the Lean runtime's
  counting.  The port's counts are its own `Rc`s (§3.2), non-atomic *by type*,
  with no runtime-owned mark to set and nothing to switch off; an `Rc` graph
  handed across threads is a compile error, not a slower program.  So the flag
  is accepted — a script that measures both checkers passes it to both — and
  prints `the persistent mark is a Lean-runtime reference-counting device
  (Runtime.markPersistent), and the port's counts are non-atomic Rc counts with
  no runtime mark to clear`.  Rejecting it would have been the wrong answer: it
  is not a retired spelling, it is a switch for a device this program does not
  have.

#### Out of memory is not an exit code here, and con-leche's is

`Main.lean` documents OOM as **exit 1**: the Lean runtime's
`lean_internal_panic_out_of_memory` prints `INTERNAL PANIC: out of memory` and
calls `exit(1)`, uncatchable in process, so the stderr message is what tells it
from a reject.  The port cannot reproduce that, and pretending otherwise would
be the worst of the options.  A Rust allocation failure goes to
`alloc::handle_alloc_error`, which prints `memory allocation of <n> bytes
failed` and **aborts** — `SIGABRT`, which a shell reports as **134**, never 1 —
and an exhausted address space (`ulimit -v`) or a blown 1 GiB stack aborts the
same way.  So the two checkers' OOM *codes* differ by construction, a
differential sweep must read the stderr line rather than the code, and nothing
in the port can narrow the gap, because catching an abort would mean surviving
the allocation that failed.  `driver`'s module note says all of this where a
reader of the code will find it.

What the port *does* guarantee is the other half: **a panic is exit 3.**  The
fold runs on a spawned 1 GiB-stack thread, so a panic on it — a `debug`
overflow, an index out of range — comes back as a `join` error and both
binaries turn that into 3, "an internal failure of unclear cause", never a
verdict on the input.

#### The taint-skip rule, once

`driver::verdict_accept` is the rule and the accept line together: a clean fold
over a stream whose frontend *skipped* declarations for a tolerated axiom is
still a decline (con-leche's user directive of 2026-08-24, "uses of tolerated
axioms are never accepted"), and a declined stream never says "accepted".
`con-ron` reaches it with its own frontend's `taint_skipped` and its detail
string; `con-ron-check` with `--taint-skipped N` and no detail, because the
count is frontend state the dump does not carry (task #10's surprise 9).  It
must not live in the core, which accepts the list it is given and knows nothing
of what the frontend dropped — and now it lives in exactly one place above it.
`diff-fixtures.sh` reads **315 agree, 0 differ, 33 skipped**, so the three
fixtures the rule is load-bearing for (`sorry_use`, `tolerated_axiom_use`,
`taint_skip_continue`) still land on con-leche's code through the shared
spelling.

#### The cherries ledger, closed

```text
== Cherries (ConLeche/Frontend without Scan/Equiv, Main.lean)
Main.lean                          1184     1000     1000 100%        71 skipped
ConLeche/Frontend/Scan/Fast.lean   2637     2408     2408 100%
…
TOTAL                              9802     7647     7647 100%       446 skipped
```

**7 647 of 7 647 (100 %)**, up from 7 632 of 8 093 (94 %).  The move is 15 Lean
lines newly cited (`checkHeartbeat`) and 446 lines moved from *uncovered* to
*deliberately skipped*, each with its reason in
`scripts/provenance-skip.txt` — which §3.7 makes the machine-readable index of
the module notes that argue them, so the entries and
`crates/con-ron/src/lib.rs`'s "four things deliberately not here" are the same
list:

* **the pool** — `checkOne`, `checkWorker`, `mergeResults`, `checkPool` (71
  Lean lines), reason `parallel phase B: pending the Rc/Arc decision (task
  #40)`.  This is the ledger's one **owed** entry: it is not a decision that
  the port will never have a pool, it is a decision the project has not taken.
* **`Frontend/ExportWrite.lean`** (169) and **`Frontend/InModelDump.lean`**
  (42) — the annotated-NDJSON writer and the debug splice built on it: output
  formats, not checking paths (task #37's and #39's notes).
* **`Frontend/Scan/Naive.lean`'s reference-only half** (164) — the `NRes`
  reader monad and the twenty field tables `Fast.lean` inlines into its slot
  loops, which the Rust recogniser therefore has no declaration for either.
  The other 474 lines of the file *are* cited: every `scan_fast` item names its
  `naive*` specification beside the `Fast` declaration it ports, which is
  P4.3's statement.

Three entries came **off** the list in the same move — `msSecs`, `declCLabel`
and `ValueKind.word`, all three now ported in `driver.rs` — and one more,
`BasisKind.decls`, which `frontend::basis_raw` had cited since task #37 without
anyone noticing, because `coverage` could not see it.  Which is the last
finding:

**`coverage`'s skip validation was blind outside its own globs.**  `STALE` and
`REDUNDANT` were reported only for entries the walk over
`ConLeche/{Kernel,Cached}` reached, so the four `Main.lean` entries this task
added came out `STALE` while the three cited-but-skipped ones stayed quiet.
Every unused key is now validated against the file it *names*
(`scripts/provenance.py`, §3.7's new paragraph): the printed `TOTAL` stays the
verified core's, and the list is checked wherever it points — which is where it
is longest.

#### Gates

| gate | result |
|---|---|
| `scripts/gates.sh` | all 6 OK (`cargo build`, `cargo test`, lint, provenance, `extract.sh --check`, `lake build`) |
| `cargo test` | **227 pass, 1 ignored** (task #37's exponential measurement), warning-free — **4** new tests in `driver` |
| `scripts/lint-rust-style.sh` | green, and untouched: scoped to `crates/con-ron-core/src` |
| `scripts/provenance.py check` | 2 022 items, 2 213 citations, all current at pin `3e004805` |
| `scripts/provenance.py coverage` | `TOTAL 910/910 covered (100.0 %), 0 uncovered, 96 deliberately skipped`, **0 findings** |
| `scripts/extract.sh --check` | clean (`con-ron-core` untouched — not one file of it changed) |
| `cd proof && lake build` | clean |
| `scripts/diff-e2e.sh --timeout=60` | **348 agree, 0 differ**, 0 timeouts — and **348 agree, 0 differ** again with `--progress` |
| `scripts/diff-fixtures.sh --timeout=60` | **315 agree, 0 differ**, 33 skipped |
| `scripts/diff-frontend.sh` | **315 byte-identical, 0 differ**, 33 no dump |
| cherries (`scripts/progress.py`) | **7 647 of 7 647 Lean lines translated (100 %)**, up from 94 % |
| `init.ndjson` end to end | accepted **57972** (`baseline.md`'s number), 58.3 s, no regression on task #39's 59.7 s |

`con-ron-core` is byte-identical to before this task, so the extraction gate is
trivially green and no `Refine/*` lemma is touched: everything here is outside
§1's theorem by construction, as the CLI is in con-leche.

#### Left for next time

* **The thread pool** (`checkPool`, `IO.asTask`, the shared claim counter),
  P4.1's last piece and the ledger's one owed entry.  It needs the `Rc`/`Arc`
  decision first (§3.2: `Rc` is not `Send`; con-leche sidesteps atomic counts
  with a runtime mark the port has no equivalent of), and the numbers above
  price the prize: phase B is **89 % of `init`'s wall time**, and con-leche's
  `--jobs=8` Mathlib row is 337 s against its own 1 228 s at `-j1`.
  `PhaseObserver` was written with it in mind — `check_after` takes the
  completed *count*, so it is monotone whichever worker finished, which is
  con-leche's reason for the same shape.
* **The full Mathlib run** of the whole binary against
  `_tmp/corpus/baseline.md` (P4.2), which wants the machine to itself.
* **`CON_LECHE_ROUTE_TRACE`**, the only `Main.lean` environment switch still
  unported and the only one that is not merely a print: it runs the recognisers
  on the environment the step sees, i.e. a second dispatch of the fold.  It is
  named in `con-ron --help`'s NOT PORTED paragraph and is not on the skip list,
  because the declaration it lives in (`installLoop`) *is* ported.
