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

**Status (2026-09-12): design draft for discussion with the maintainer.  No
port code exists yet.  A feasibility spike (`spikes/rc-fuel/`) went through
Charon and Aeneas cleanly.**

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

The pure checker (`Kernel/Core.lean`) is written against a record of
closures (`CoreFns`, the "knot"); the cached checker ties it with memo
wrappers.  Rust has no cheap closures under Aeneas, so the port closes the
knot: the cached functions are one mutually recursive block with the fuel as
an explicit argument.  The refinement lemma is stated against
`(coreKnotI mode fe fuel).whnf` etc., which unfolds one level per fuel step.

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
* `ron::Nat` — `Small(u64) | Big(Vec<u64>)` limbs, normalised.  Operations
  needed (`Kernel/Core.lean:628-655`): `pred, add, sub, mul, pow (exponent ≤
  2^24), div, mod, gcd, land, lor, xor, shiftLeft, shiftRight, beq, ble`.
  Spec: `toNat : ron.Nat → Nat` is a homomorphism.  Start with shift-subtract
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
