# con-ron: an overview

> **This document was written by an AI agent** (Claude, working with
> the maintainer), in contrast to `README.md`, which is human-written.
> It is a guided tour of the port and its proof, from the binary that
> runs to the theorem it inherits, with links into the source on
> `master`.  `DESIGN.md` is the agents' own design record and task log;
> `AENEAS_FINDINGS.md` is what the port learned about the translator.

con-ron is [con-leche](https://github.com/leanprover/con-leche) — the
Lean checker whose consistency theorem is proved in Lean — ported to
Rust function for function, and proved, through
[Aeneas](https://github.com/AeneasVerif/aeneas), to *refine* the
con-leche it was ported from: whenever the Rust checker accepts a
declaration stream, con-leche accepts the same stream, so con-leche's
`model_exists` and `no_proof_of_False` are theorems about the Rust
binary too.  The point is to take the Lean compiler, the Lean runtime
and its bignum library out of the trusted base of a proof that a Lean
development is consistent: a bug in those would have to have a twin in
`rustc` and Rust's runtime for the two checkers to agree wrongly.

## 0. Using the checker

The binary reads a Lean export in `lean4export`'s NDJSON format and
prints one verdict line
([the usage text in `con-ron.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron.rs#L109-L175)):

```
con-ron [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
        [--progress[=<stride>]] [--pins FILE|--no-pins] [--dump-decls OUT]
        FILE.ndjson
con-ron --help
```

`--verified` is the default and the mode the theorem is about.
`--trusted` runs the same checker bodies with the certification-only work
switched off; it is faster and outside the theorem.  `--jobs=<n>` is the
check phase's worker count, defaulting to one per hardware thread capped
at 16, because each worker reserves a gigabyte of address space for its
stack.  `--progress[=<stride>]` is a heartbeat on stderr.  The three
flags con-leche does not have are marked as con-ron's own in the usage
text: `--pins FILE` and `--no-pins` replace the embedded pin list for
testing, and `--dump-decls OUT` writes the parsed declarations in the
`con-ron-decls/1` format and exits.  `--no-mark-persistent` is accepted
and does nothing: the Lean-runtime device it turns off has no
counterpart in a program whose reference counts are atomic by type.

The exit code follows the Lean kernel arena convention, the same as
con-leche's
([the exit-code table in `driver.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L40-L45)):

| exit | verdict | meaning |
|---|---|---|
| 0 | `accepted N declarations` | every declaration checked |
| 1 | `rejected` | a declaration is invalid |
| 2 | `declined` | the checker detected a feature it does not support, and says which |
| 3 | error | bad usage, malformed input, or an internal failure |

A second binary, `con-ron-check`, is the same driver over a
`con-ron-decls/1` dump instead of a raw export
([its header](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron-check.rs#L1-L14)).
The dump is the parsed declaration list that con-leche's own frontend
produced, so this binary is con-leche's `Main.lean` minus the frontend,
and it is the differential seam of §6: the same dump through both
checkers must give the same verdict.

## 1. Building

Three toolchains meet here, and `flake.nix` pins two of them
([`flake.nix`](https://github.com/leanprover/con-ron/blob/master/flake.nix#L5-L29)):
Aeneas at a fixed commit, which pins the Charon it needs, which pins the
Rust nightly it needs.  `nix develop` (or `direnv allow`) gives a shell
with `cargo`, `rustc`, `charon` and `aeneas`.  Lean comes from `elan`,
at the version in `proof/lean-toolchain` (the same as con-leche's).

```
nix develop                        # cargo, charon, aeneas on PATH
cargo build --release              # target/release/con-ron, con-ron-check
scripts/setup-aeneas-lean.sh       # the patched Aeneas Lean library + Mathlib, once
cd proof && lake build             # the model and the proofs
```

`setup-aeneas-lean.sh` copies Aeneas' Lean backend out of the
`vendor/aeneas` submodule, applies `patches/aeneas-433.patch` (§9) and
fetches Mathlib from the olean cache; it is idempotent
([`setup-aeneas-lean.sh`](https://github.com/leanprover/con-ron/blob/master/scripts/setup-aeneas-lean.sh#L1-L14)).
`vendor/con-leche` is a vendored copy of con-leche (a squashed
`git subtree`, §4), built by `lake` as a dependency of the proof; on a
many-core machine its first build can exhaust memory, and
`LAKE_JOBS=N scripts/gates.sh` caps the parallelism.

The one command a contributor runs before committing is
`scripts/gates.sh`
([the eight steps](https://github.com/leanprover/con-ron/blob/master/scripts/gates.sh#L51-L58)):
the Rust build and tests with warnings denied, the style lint (§3.6),
the provenance check (§4), the embedded-pins check, the extraction check
(the committed Lean model must be what Charon and Aeneas produce from the
crate today), and the Lean build.  §12 has the list.

## 2. What is proved

The headline theorem is stated for the Rust checker's own entry point,
`check_decls` in the verified core, with the pin list it uses obtained
from the verified decoder on any input
([`conron.model_exists_decoded` in `Main.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L238-L249)):

```lean
theorem conron.model_exists_decoded (V : Type w) [ConLeche.SetTheory V]
    {text : Slice Std.U8} {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e))
```

and its companion
[`conron.no_proof_of_False_decoded`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L252-L259):
if the Rust `check_decls` in verified mode accepts the parsed
declarations `ds` and returns the environment `e`, then that environment,
abstracted to con-leche's, has a model in every set theory, and contains
no constant whose type is `False`.  `absEnv` is the abstraction function
from the Rust environment to con-leche's (§5).  The hypotheses are
exactly two: a run of the decoder, and a run of the checker.  Nothing is
assumed about the input, because `check_decls` validates it (§3.5), and
nothing is assumed about the pins' value, because the fold is parametric
in them (§9).

Both censuses are pinned by `#guard_msgs` at con-leche's own three axioms
([the censuses](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L261-L265)):
`propext`, `Classical.choice`, `Quot.sound`.  No `native_decide`, no
`sorry`, nothing sealed.

Three more forms exist for readers who want them.  The general pair
([`conron.model_exists`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L139-L150))
names the two facts the induction owes — that the core knot refines
con-leche's at the checker's fuel, and that the two inductive install
routes refine theirs — as hypotheses, and the well-formedness of the pins
as a third; the primed pair
([`conron.model_exists'`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L179-L188))
discharges the first two from the knot induction (§5).  The embedded pair
([`conron.model_exists_embedded`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L323-L336))
is the decoded pair at the constant the binary ships, `PINS_TEXT`; its
census carries one axiom more, `pins_text.PINS_TEXT._native.decide.ax_1`,
which is not the port's: Aeneas' `toStr` discharges the byte-length bound
of every extracted string constant with `decide +native`, and the axiom
sits in the constant's definition.  §7 says what that leaves trusted.

What connects the Rust run to con-leche's theorem is one refinement
statement over the whole outcome
([`check_decls_refines` in `Installed.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Installed.lean#L3241-L3252)):
if the Rust fold returns `Ok e`, con-leche's fold returns the abstraction
of `e`; if it returns a mirrored error, con-leche throws an error of the
same kind; if it returns the port's own `Native` error, nothing is
claimed.  The main theorems are that statement's accept case composed
with con-leche's `model_exists_with`, the pins-parametric form of its
main theorem.

## 3. The checker

### 3.1 What was ported, and how closely

con-leche has a pure checker (`ConLeche/Kernel`) and a memoising one
(`ConLeche/Cached`) proved equivalent to it; the binary runs the second.
con-ron ports the *memoising* checker, one Rust module per Lean file,
functions in the same order, each carrying a doc comment that cites its
source range (§4).  The port covers con-leche's core completely and its
frontend (the export parser and the in-process modeller for mutual and
nested inductives) completely; the proof covers the core.  §6 has the
ledger.

The one thing con-ron does that con-leche does not is validate its input
(§3.5).  Everything else that differs is either a data-structure
substitution proved to behave the same (§3.2–3.4) or a Rust idiom the
translator requires (§3.6).

### 3.2 Terms

A term is a reference-counted node
([`ExprNode` and `Expr` in `expr.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/expr.rs#L354-L363)):
the constructor data beside a packed 64-bit word that caches what
con-leche computes in its `@[computed_field]`s — the structural hash, the
loose bound-variable bound, the has-free-variable and has-level-parameter
bits.  The pointer type is `std::sync::Arc`, named in exactly one place
([`ron::ptr`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/ptr.rs#L1-L8)),
so that the installed environment can be shared by the check phase's
workers without `unsafe`; the atomic count costs about 15 % of wall time
single-threaded and buys the pool (§10).  Nodes are built only by smart
constructors such as
[`app`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/expr.rs#L429-L440),
which is what the well-formedness predicate of §5 says.

### 3.3 Naturals and hash maps

Two things Lean's runtime provides have no Aeneas model and are the very
things the project wants out of the trusted base, so the port carries its
own: `ron::Nat`, an arbitrary-precision natural as a normalised vector of
64-bit limbs
([`nat.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/nat.rs#L1-L8)),
replacing the GMP-backed `Nat`; and `ron::HashMap`, a chained hash map
after the Aeneas tutorial's verified one, with its own `Hashable` and
`Eq2` traits
([`hashmap.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/hashmap.rs#L1-L10)),
replacing `Std.HashMap`.  Both are verified against their mathematical
specifications, and the memo state is fourteen such maps
([`CState`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/cached/state_c.rs#L326-L360)),
one per con-leche memo table, with the same keys and the same policy.

### 3.4 The knot, fuel, and the pins

con-leche's core is a knot of six mutually recursive operations
(`whnfCore`, `whnf`, `infer`, `defeq`, `annotate`, `inferIO`) tied through
a record and a fuel.  Aeneas rejects recursion that mixes functions and
trait methods, so the knot is six plain mutually recursive functions with
the fuel as an argument
([the wrappers in `core_c.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/cached/core_c.rs#L5089-L5120)),
each probing its memo table, running its body one fuel step down, and
inserting — con-leche's `memoEI`, spelled out.

con-leche checks `Nat.div` and `Nat.mod` against a list of pinned
elaborations.  The port embeds that list as text in the verified core
([`PINS_TEXT`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/pins_text.rs#L40-L44),
generated from con-leche by `scripts/gen-pins.sh` and checked by the
gates) and decodes it with a verified decoder
([`decode`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/pins_decode.rs#L1330-L1347))
whose output is well-formed by construction for every input.

### 3.5 Errors, and the validation pass

The Rust error type has con-leche's three kinds and a fourth
([`CheckError`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/core_types.rs#L87-L92)):
`Native` is a failure con-leche cannot have — a shift amount beyond 64
bits, a pin text that does not decode, a malformed input — and the
refinement claims nothing about it.  The other three mirror con-leche's
`throw` sites one for one (303 of them, classified against their cited
source), and the refinement says con-leche throws the same kind.  Where
con-leche backtracks (`orElse`, in the `Nat.div`/`Nat.mod` pin loop) the
port backtracks from a snapshot of the memo state on a mirrored error and
keeps a `Native` one as the verdict
([`or_else_step`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/cached/checker_c.rs#L123-L132)).

### 3.6 The Rust subset

Aeneas translates a subset of Rust, and the port stays inside it by rule
rather than by luck: no closures, no `?`, no loops (recursion instead),
no `unsafe`, no `std::collections`, no `derive(Debug)`, higher-order
arguments as one-method traits, `&mut` only where the translation's state
passing is wanted.  `scripts/lint-rust-style.sh` enforces the mechanical
part; DESIGN.md §3.4 has the rules and their reasons.  `overflow-checks`
is on in release builds
([`Cargo.toml`](https://github.com/leanprover/con-ron/blob/master/Cargo.toml#L21)),
so an arithmetic overflow the model calls `fail` is a panic in the binary
rather than a wrap.

The unverified crate `con-ron` holds the frontend (the parser and the
modeller, ported from con-leche's), the driver, and the worker pool of
the check phase
([`pool.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L1-L9));
`con-ron-dump` reads and writes the two dump formats.  The verified crate
is `con-ron-core`.

## 4. Keeping the port in sync with con-leche

Every Charon-visible item of the core carries a citation of the con-leche
source it ports, as a doc line `/// con-leche: <path>:<a>-<b> <declaration>`
([an example in `level.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/level.rs#L125-L127)),
or `/// con-leche: none — <reason>` for an item with no Lean counterpart.
The vendored con-leche tree fixes what those citations mean: no hash in
the source, no drift.  `scripts/provenance.py` has three modes:

* `check` — every item cites, every citation resolves to the named
  declaration at the cited range (a gate);
* `update` — after a con-leche bump, relocate every citation whose text
  merely moved and mark every one whose text changed with a `CHANGED`
  line that the porter deletes once the item is re-ported, re-tested and
  re-proved; `check` fails while any remains, and `progress.py` lists the
  lemmas that are stale;
* `coverage` — the ledger: which con-leche declarations are cited, and
  which are deliberately skipped, each with a reason in
  `scripts/provenance-skip.txt`.

con-leche itself is a vendored `git subtree`, squashed, at the commit
named in `vendor/CON_LECHE_PIN`.  A bump is `git subtree pull --squash`,
a new pin line, and `provenance.py update`, which diffs the new tree
against the one at `HEAD`.  The proof then says what else moved: a
refinement lemma that no longer elaborates is a con-leche change that
reached the port.

Two scripts measure the state.  `scripts/progress.py` counts, per
con-leche file, the Lean lines to translate, translated (cited), and
verified (cited by a Rust item with a `_refines` lemma);
`scripts/loc.py` puts the four sizes side by side — upstream lines, Rust
lines, generated Lean, proof lines — and splits the proof lines by how
each theorem is proved.  Both print a summary at the end of the gates.

## 5. The verification

### 5.1 From Rust to Lean

Charon compiles the verified crate to its intermediate representation and
Aeneas translates that to Lean: one definition per function in the
`Result` monad (`ok`, `fail`, `div`), `&mut` arguments as state passing,
recursion as `partial_fixpoint`.  The output is committed under
`proof/ConRon/Generated/` and regenerated by `scripts/extract.sh`; the
gates fail if the committed model is not what the crate extracts to
today.  The model is about 53 000 lines for about 37 500 lines of Rust.

Two things the translation cannot see are modelled by hand
([`TypesExternal.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/TypesExternal.lean#L42),
[`FunsExternal.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L26-L45)):
an `Arc<T>` is its contents, and `Arc::ptr_eq` is `false`.  The first is
faithful because the port never mutates through an `Arc` (the lint
forbids `get_mut`, `make_mut`, `Weak` and interior mutability), so sharing
is invisible to the value.  The second is an under-approximation the
proof has to be sound against: every place the Rust takes a pointer-equal
shortcut, the proof shows the result is what the full computation gives —
the memo tables' pointer-verified buckets, the validation pass's visited
set, and `beq`'s pointer fast path each have that lemma.

### 5.2 Abstraction and well-formedness

The proof relates Rust values to con-leche values through abstraction
functions (`absName`, `absLevel`, `absExpr`, `absEnv`, …) and, for the
two things a function cannot abstract — the memo state and the
environment index, whose Lean counterparts are `Std.HashMap`s — through
relations:
[`StateRel`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/State.lean#L640-L671)
says every lookup in every one of the fourteen maps agrees under the
abstractions, and
[`FEnvRel`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/FEnv.lean#L96-L104)
the same for the index.

Well-formedness is an inductive predicate whose constructors *are* the
port's smart constructors
([`ExprWF`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L511-L525)):
a node is well-formed if some smart constructor returned it on
well-formed children.  No proof ever names the hash formula; what the
readers of the packed word need — that its bits are con-leche's computed
fields, that `absExpr` is injective on well-formed terms, so the Rust
`beq` is exact — follows from that definition once.

### 5.3 The statements

A leaf operation refines its con-leche counterpart as a plain equation
with the abstractions.  A stateful one is stated over the whole outcome
([`Sim` in `Shape.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Core/Arms/Shape.lean#L102-L119)):
for related states and environments, if the Rust returns `Ok r` then
con-leche's action returns `abs r` in a related state and `r` is
well-formed; if it returns a mirrored error, con-leche throws the same
kind
([`ErrSim`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L922-L930));
a `Native` error claims nothing.  This is a *partial* refinement by
design: the Rust may fail where con-leche does not, never the reverse on
an accept.

The knot is stated as one proposition indexed by the fuel
([`KnotSpec` in `Statements.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Core/Statements.lean#L191-L194)):
the six wrappers at fuel `n` refine con-leche's knot at `n`, and the six
bodies at `n` refine con-leche's bodies applied to that knot.  The
induction on the fuel
([`knot_induction`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Core/Knot.lean#L895-L910))
has a memo argument once per wrapper — a probe that hits gives what the
relation promises, a miss runs the body one step down and inserts — and
one lemma per body arm, in the nineteen files of `Refine/Core/Arms/`,
closed by
[`knot_spec`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Core/Arms/Arms.lean#L381-L383).
Above the knot sit the declaration checker, the two inductive install
routes
([`IndRoutesSpec`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/IndSpec.lean#L80-L100)),
the fold, and the capstones of §2.

### 5.4 Differential testing

Before and beside the proof, the port is checked against con-leche on
data: con-leche's own test fixtures through both checkers
(`scripts/diff-fixtures.sh`, 315 fixtures, every verdict and exit code
equal), its end-to-end suite through both binaries (`scripts/diff-e2e.sh`,
348 cases, at several worker counts), and the frontends compared on the
parsed declaration dumps (`scripts/diff-frontend.sh`, byte-identical).
The frontend is unverified; this is what stands in for its proof.

## 6. Results

### 6.1 The ledger

| | |
|---|---|
| con-leche core (`Kernel`, `Cached`) lines to port | 13 761, all ported, 92 % verified (the rest deliberately skipped, listed with reasons) |
| con-leche frontend and driver lines to port | 7 727, all ported, unverified |
| Rust, verified core | 37 509 lines, 1 455 functions, every item cited (912 declarations covered, 94 skipped) |
| Rust, unverified crates | about 20 000 lines |
| generated Lean model | 52 615 lines |
| proofs | 147 035 lines: 3 289 theorems by tactic, 805 by term, 8 by `grind`; 1 289 `_refines` lemmas |
| refinement statements over the whole outcome | 281 of 281 |

The ratios are worth a sentence: the Rust is 2.7× the Lean it ports (a
`match` in Rust is longer than one in Lean, and every memo probe is
spelled out), the model 1.4× the Rust, the proofs 3.9× the Rust and 10.7×
the upstream Lean.

### 6.2 What the proof found

The proof was the port's most productive test.  Deviations it caught in
code that had passed every fixture: a division-by-zero guard weaker than
con-leche's, which would have *accepted* what con-leche rejects; a
non-short-circuiting boolean `and` where con-leche's laziness mattered;
a projection case that copied a tree con-leche shares; a memo table that
evicted its own entries on a hash collision; a family of `u64 → usize`
casts in the modelled inductives; and, in the translator itself, an
Aeneas model of `Vec::insert` that overwrote where Rust inserts
(AENEAS_FINDINGS.md §3.9, since removed from the port's vocabulary).  The
full-outcome restatement of every lemma, done last, found no further
deviation: all 303 mirrored error sites came out as cited.

### 6.3 Performance

Measured with `perf stat -e instructions:u,cycles:u` (the measure of
record) and wall time and peak resident set as secondary numbers, on
`lean4export` exports of Lean's `Init`, of `Init`+`Std`+`Lean`, and of
Mathlib; con-leche at the vendored commit, both binaries in verified
mode, single-threaded and at eight workers.  Instructions are what the
two checkers do; the gap in wall and memory is memory traffic and atomic
reference counts.

<!-- PERF-TABLE: filled from _tmp/perf-overview after the runs at the commit named there -->
| export | jobs | con-leche instructions | con-ron instructions | con-leche wall | con-ron wall | con-leche peak RSS | con-ron peak RSS |
|---|---|---|---|---|---|---|---|
| `Init` (57 972 declarations) | 1 | 586 G | *(pending)* | 59 s | *(pending)* | 0.48 GB | *(pending)* |
| `Init` | 8 | 587 G | *(pending)* | 12 s | *(pending)* | 0.71 GB | *(pending)* |
| `Init`+`Std`+`Lean` (163 391) | 1 | 1 180 G | *(pending)* | 150 s | *(pending)* | 1.24 GB | *(pending)* |
| `Init`+`Std`+`Lean` | 8 | 1 183 G | *(pending)* | 43 s | *(pending)* | 1.39 GB | *(pending)* |
| Mathlib (691 123) | 1 | 12 817 G | *(pending)* | 1 228 s | *(pending)* | 8.6 GB | *(pending)* |
| Mathlib | 8 | 12 843 G | *(pending)* | 337 s | *(pending)* | 9.1 GB | *(pending)* |

Two earlier measurements, recorded in DESIGN.md, explain the shape of
the numbers.  Before the switch to atomic counts, con-ron ran Mathlib at
the same instruction count as con-leche (12 797 G against 12 817 G), 1.6×
the wall time and 1.86× the memory: equal work, more memory traffic.
The switch to `Arc` cost 13–17 % of wall time single-threaded and bought
a check phase that scales to 4.3× at eight workers and 6.9× at sixteen
on `Init`.  The validation pass costs 1.5 % of instructions on `Init` and
3 % on the larger export.

## 7. Trust assumptions

What has to be right for the theorem to mean what it says about the
binary:

* **con-leche's own assumptions.**  The theorem is con-leche's, at the
  Rust run: it rests on a set theory `V` with `ConLeche.SetTheory V`, on
  Lean's kernel checking the proof, and on the three standard axioms.
  con-leche's OVERVIEW says what those are.
* **Aeneas and Charon.**  The Lean model is what the translator says the
  Rust means.  A translator bug is a hole; the port stays inside the
  documented subset and reports what it found (AENEAS_FINDINGS.md).  The
  two hand-written models (§5.1) are an argument, not a proof: `Arc` as
  its contents holds because the lint forbids mutation through it, and
  `ptr_eq` as `false` is sound because every pointer shortcut has its
  equivalence lemma.
* **`rustc`, the Rust standard library, and `mimalloc`**, the allocator
  the binaries use.  These are what the project trades Lean's compiler,
  runtime and GMP for.
* **The unverified crate.**  The parser, the modeller for mutual and
  nested inductives, the driver and the worker pool are ported but not
  proved; they are checked against con-leche's on the fixtures (§5.4).
  What they hand to `check_decls` is validated by it (§3.5), so a
  frontend bug can lose an accept, never fake one.  One fact about the
  driver is what the decoded pair leaves outside Lean: that it calls the
  decoder on the embedded text.
* **Nothing else.**  No `native_decide`, no `sorry`, no extra axiom in
  the headline pair.  The embedded pair's one extra axiom is the
  translator's string-constant artifact, above.

## 8. Proof techniques

Most of the 147 000 lines are hand proofs in one shape: invert the Rust
run (a `do` block in the `Result` monad unfolds into a chain of binds,
each either `ok` with an equation or an early exit), apply the lemma of
each callee through the state relation, and close with the constructor
of the well-formedness predicate.  The Aeneas library's `progress`-style
tactics were tried and set aside: the two relations and the abstraction
functions make the forward-refinement style, with equations in context,
the shorter one here (AENEAS_FINDINGS.md §3.3).

A second style exists for new lemmas, adopted after a study measured it
(`proof/ConRon/Refine/AUTOMATION.md`): a normaliser `rust_norm h` that
reduces the Rust equation in pre-order with two registered simp sets and
peels the binds, then `all_goals rust_grind`, which is `grind` with a
fixed configuration
([`rust_grind` in `Abs.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L170))
and the callee lemmas registered as `grind →` rules keyed on the Rust
equation.  With a node-shaped induction principle, a memoised term walk
is one line.  The cost is 1.2–1.8× the hand proof's elaboration time on
leaves and 3–4× on memo walks and knot arms, all of it `grind`
internalising the context per goal; the study's numbers are in
AUTOMATION.md.  The rule is: existing hand proofs are not rewritten; new
lemmas use the idiom where it applies (leaves, walks, arms — not the
mathematical `Nat` and `HashMap` tiers, not the byte-level pin decoder,
not the list folds).  Its first real use, the validation pass's soundness
lemmas, closed eight of seventeen on the first try, the other nine being
list folds.

The one campaign the proof went through twice is worth knowing about:
every lemma was first stated in the accept direction only (an `Ok` on the
Rust side gives an `ok` on the Lean side), and then restated over the
whole outcome (§5.3) once `orElse` made it necessary — con-leche
backtracks on an error, so an "error means nothing" lemma cannot follow
it through a retry.  The restatement kept every accept half verbatim and
added the error halves by hand; the campaign's tooling, a
statement-shape classifier in `progress.py`, is what a future con-leche
bump will use to see which lemmas are stale.

## 9. Patches against upstream

* **Aeneas' Lean library on Lean v4.33**
  ([`patches/aeneas-433.patch`](https://github.com/leanprover/con-ron/blob/master/patches/aeneas-433.patch)).
  The pinned Aeneas builds its Lean library against Lean v4.31 and
  con-leche is on v4.33; the patch, 375 lines to ten files, makes the
  library build on v4.33 and its Mathlib.  Two options the proofs need
  are set in `proof/lakefile.toml`
  ([the options](https://github.com/leanprover/con-ron/blob/master/proof/lakefile.toml#L21-L23)).
  AENEAS_FINDINGS.md §3.1 has the details; the ask upstream is a v4.33
  release.
* **con-leche's pin list as a parameter of the fold.**  The pinned
  con-leche hard-wires its `Nat.div`/`Nat.mod` pin list at two install
  gates, so a refinement for the *decoded* list could only be stated
  through a `native_decide` identifying the two.  The vendored con-leche
  is con-leche's `pins-param` branch (its task #285): the list is an
  argument of the fold, defaulting to the constant, with the shipped
  statements unchanged and a `model_exists_with` for any list.  That
  branch is being sent upstream; until it lands, `vendor/CON_LECHE_PIN`
  names it.
* **Nothing else.**  Charon is unpatched; the translator findings
  (AENEAS_FINDINGS.md §2, fifteen of them, with the `Vec::insert` model
  bug of §3.9 the one that mattered) were worked around in the Rust.

## 10. Naming conventions

Rust modules mirror con-leche's files (`ConLeche/Kernel/Level.lean` →
`crates/con-ron-core/src/kernel/level.rs`, `ConLeche/Cached/CoreC.lean`
→ `cached/core_c.rs`), nested under `kernel/`, `cached/`, `ron/` because
Aeneas prints unqualified names.  A function keeps con-leche's name in
snake case; con-leche's `fooC` twins are `foo_c`; a function that con-ron
adds is marked `con-leche: none` with its reason.  Proof files mirror the
Rust modules (`Refine/Level.lean`, `Refine/Core/Arms/*.lean` for the
knot); a lemma about `foo` is `foo_refines`; the abstraction functions
are `abs*`, the relations `*Rel`, the well-formedness predicates `*WF`.

## 11. Module map

| where | what |
|---|---|
| `crates/con-ron-core/src/kernel/` | the pure checker: `name`, `level`, `prop_when`, `expr`, `expr_ops`, `env`, `fenv`, `core_k`, `checker*`, `decl_check`, `type_checker`, the basis tables, the axiom tables, `inductives/*`, `pins_text`, `pins_decode` |
| `crates/con-ron-core/src/cached/` | the memoising checker: `state_c`, `expr_ops_c`, `core_c` (the knot), `checker_c`, `parsed_c`, `installed` (`check_decls`) |
| `crates/con-ron-core/src/ron/` | `nat`, `hashmap`, `ptr` — what replaces the runtime |
| `crates/con-ron/src/` | the frontend, the driver, the pool, the two binaries |
| `crates/con-ron-dump/` | the `con-ron-decls/1` and `con-ron-pins/1` readers and writers |
| `proof/ConRon/Generated/` | the committed Aeneas model |
| `proof/ConRon/Refine/` | the proofs: `Abs`, `State`, `FEnv` (abstractions and relations); one file per Rust module; `Core/` (the knot); `Ind*` (the inductive routes); `Pins*` (the decoder); `Validate`; `Installed`; `Main` |
| `proof/ConRon/Refine/README.md` | the proof tier's own map: naming, the hypothesis table, how to write a lemma |
| `vendor/con-leche/` | con-leche, vendored at `vendor/CON_LECHE_PIN` |
| `vendor/aeneas/` | Aeneas, as a submodule, for its Lean library and documentation |
| `scripts/` | the gates and the tooling of §4 |
| `DESIGN.md` | the agents' design record and task log |
| `AENEAS_FINDINGS.md` | what the port learned about Charon and Aeneas |

## 12. Gates

`scripts/gates.sh` runs, in order, and stops at the first failure:

1. `cargo build` with warnings denied;
2. `cargo test`;
3. `scripts/lint-rust-style.sh` — the Aeneas subset;
4. `scripts/provenance.py check` — every item cites, every citation resolves, no `CHANGED` marker left;
5. `scripts/overview-links.sh` — every line-anchored link in this document and in `DESIGN.md` still points at the text it cited (the cited lines are a committed artefact, `scripts/overview-links-expected.txt`, in con-leche's idiom);
6. `scripts/gen-pins.sh --check` — the embedded pin text is what con-leche's list generates;
7. `scripts/extract.sh --check` — the committed model is what Charon and Aeneas produce;
8. `lake build` of the model and the proofs.

It ends with the two summary lines of `progress.py` and `loc.py`.  The
differential tests of §5.4 are not in the gates, since they need the
exports; CI runs them where it can.
