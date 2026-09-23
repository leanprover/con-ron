# con-ron: an overview

> **This document was written by an AI agent** (Claude, working with
> the maintainer), in contrast to `README.md`, which is human-written.
> It describes the port and its proof as they stand: how to run the
> checker, how it is built, what is proved, what is trusted, and the
> conventions a contributor needs.  `DESIGN.md` is the agents' design
> record and task log, and holds the history and the measurements behind
> every decision mentioned here; `AENEAS_FINDINGS.md` is what the port
> learned about the translator.

con-ron is [con-leche](https://github.com/leanprover/con-leche), the Lean
checker whose consistency theorem is proved in Lean, ported to Rust function
for function and proved through [Aeneas](https://github.com/AeneasVerif/aeneas)
to *refine* the con-leche it was ported from: whenever the Rust checker
accepts an export, con-leche accepts it too, so con-leche's theorems about
accepted environments hold for the Rust binary as well.  The point is to
take Lean's compiler, runtime and bignum library out of the trusted base of
a consistency check: a bug there would need a twin in `rustc` and Rust's
runtime for the two checkers to agree wrongly.

## 1. Using the checker

The binary reads a Lean export in `lean4export`'s NDJSON format and prints
one verdict line
([the usage text](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron.rs#L87-L202)):

```
con-ron [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
        [--progress[=<stride>]] [--pins FILE|--no-pins]
        FILE.ndjson
con-ron --help
```

* `--verified` is the default and the mode the theorem is about.
  `--trusted` runs the same checker with the certification-only work
  switched off; it is faster and outside the theorem.
* `--jobs=<n>` is the check phase's worker count, by default one per
  hardware thread capped at 16.  Each worker reserves a gigabyte of address
  space for its stack, which matters under `ulimit -v`.  The verdict, and
  the declaration a rejection names, are the same at every `n`.
* `--progress[=<stride>]` is a heartbeat on stderr.
* `--pins FILE` and `--no-pins` replace the embedded `Nat.div`/`Nat.mod`
  pin list, for testing only.  `--no-mark-persistent` is accepted for
  command-line compatibility with con-leche and does nothing.

The global allocator is a build-time choice, not a flag: `cargo build
--release` uses mimalloc, `--no-default-features` the system `malloc`, and
`--no-default-features --features jemalloc` jemalloc.  `--help` names the
one a binary was built with, so a measurement can be reproduced.

The exit code follows the Lean kernel arena convention, the same as
con-leche's
([the exit-code table](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L18-L23)):

| exit | verdict | meaning |
|---|---|---|
| 0 | `accepted N declarations` | every declaration checked; `N` counts the file's own declaration records, as con-leche counts them |
| 1 | `rejected` | a declaration is invalid |
| 2 | `declined` | the checker detected a feature it does not support, and says which |
| 3 | error | bad usage, malformed input, or an internal failure |

## 2. Building

Three toolchains meet here, and `flake.nix` pins two of them
([`flake.nix`](https://github.com/leanprover/con-ron/blob/master/flake.nix#L5-L29)):
Aeneas at a fixed commit, which pins the Charon it needs, which pins the
Rust nightly it needs.  Lean comes from `elan`, at the version in
`proof/lean-toolchain` (con-leche's).

```
nix develop                        # cargo, charon, aeneas on PATH (or: direnv allow)
cargo build --release              # target/release/con-ron
scripts/setup-aeneas-lean.sh       # the patched Aeneas Lean library + Mathlib, once
cd proof && lake build             # clones con-leche the first time, then builds the model and the proofs
```

`setup-aeneas-lean.sh` copies Aeneas' Lean backend out of the
`vendor/aeneas` submodule, applies `patches/aeneas-433.patch` (§10) and
fetches Mathlib from the olean cache.  con-leche is a plain `lake`
dependency of `proof/`, pinned by `rev` in `proof/lakefile.toml` (§5).  On a
many-core machine con-leche's first build can exhaust memory; `LAKE_JOBS=N`
caps the parallelism of `scripts/gates.sh`.

The one command to run before committing is `scripts/gates.sh` (§12), and
CI (`.github/workflows/ci.yml`) runs the same gates plus the differential
tests of §6.4.

## 3. What is proved

The headline theorem is con-leche's own main corollary, transported to the
Rust pipeline
([`conron.no_False_declaration`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/Main.lean#L730-L746)):

```lean
theorem conron.no_False_declaration (V : Type w) [ConLeche.SetTheory V]
    (hgen : Frontend.ModellerWF inst g)
    (hmr : Frontend.ModellerRefines inst g Frontend.CtxRel)
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    (hpre : frontend.export_c.parse_bytes inst g prelude_bytes true false = ok (.Ok pre))
    (hfalse : ConLeche.jsonWithTheoremFalse (Frontend.absChunks chunks))
    (hparse : frontend.export_c.parse_chunks inst g chunks im ce = ok (.Ok r))
    (hprep : frontend.prepare.prepare_prelude ⟨pre.decls⟩ r.decls = ok ds)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    False
```

A file whose bytes declare a theorem of type `False` is never accepted by
the Rust checker.  The run hypotheses (`hp`, `hpre`, `hparse`, `hprep`,
`h`) are the steps the binary performs, as Lean functions extracted from
the Rust: decode the embedded pin list, parse the built-in prelude, parse
the file's byte chunks, reorder the prelude, fold.  `hgen` and `hmr` are
the two promises made about the one unverified component the pipeline
calls, the in-process modeller for mutual and nested inductive blocks (§4.6,
§8.2): the declarations it generates are well-formed and abstract to what
con-leche's modeller generates.  The prelude is a parameter; the
`_prelude` twin states the theorem at the constant the binary ships.

Behind it stands the model statement
([`conron.model_exists_parsed`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/Main.lean#L550-L564)):
the environment the Rust fold accepts, abstracted to con-leche's, has a
model in every set theory.  Both are pinned by `#guard_msgs` at con-leche's
own three axioms, `propext`, `Classical.choice`, `Quot.sound`
([the censuses](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/Main.lean#L328-L332)).
No `native_decide`, no `sorry`.

What connects the Rust run to con-leche's theorem is one refinement
statement over the whole outcome of the fold
([`check_decls_refines`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/Installed.lean#L3293-L3304)):
if the Rust fold returns `Ok e`, con-leche's fold returns the abstraction
of `e`; if it returns one of con-leche's three error kinds, con-leche throws
an error of the same kind; if it returns the port's own `Native` error
(§4.5), nothing is claimed.  This is *partial* correctness by design: the
Rust may fail where con-leche does not, never the reverse.

Two further forms exist.  The fold-level pair
([`conron.model_exists_decoded`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/Main.lean#L303-L310))
starts at a declaration list rather than at bytes and therefore assumes
the list is well-formed (`hds`), a hypothesis the parsed form discharges.
The embedded pair
([`conron.model_exists_embedded`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/Main.lean#L391-L398))
is stated at the pin text the binary ships and carries one axiom more,
`pins_text.PINS_TEXT._native.decide.ax_1`, an artifact of how Aeneas
extracts a string constant (§8.2).

## 4. The design of the checker

### 4.1 The shape of the port

con-leche has a pure checker (`ConLeche/Kernel`) and a memoising one
(`ConLeche/Cached`) proved equivalent to it; the binary runs the second, and
con-ron ports the second: one Rust module per Lean file, functions in the
same order, each with a doc comment citing its source range (§5).  con-ron
does nothing con-leche does not; what differs is either a data-structure
substitution proved to behave the same (§4.2–4.4) or an idiom the
translator requires.

Aeneas translates a subset of Rust, and the verified crate stays inside it
by rule: no closures, no `?`, no `derive` (explicit `foo_dup`/`foo_beq`
instead), no `std::collections`, no `&str` constants, no `unsafe` at all,
higher-order arguments as one-method traits, `&mut` only
where the translation's state passing is wanted, and recursion rather than
loops (one exemption, §4.6).  `scripts/lint-rust-style.sh` enforces the
mechanical part; DESIGN.md §3.4 has the rules and their reasons.
`overflow-checks` is on in release builds
([`Cargo.toml`](https://github.com/leanprover/con-ron/blob/master/Cargo.toml#L23)),
so an overflow the model calls `fail` is a panic in the binary, not a wrap.

### 4.2 Terms

A term is a reference-counted, immutable node: the constructor's fields
beside a packed 64-bit word caching what con-leche computes in its
`@[computed_field]`s (the structural hash, the loose bound-variable bound,
the has-free-variable and has-level-parameter bits).  The count is atomic
so that the installed environment can be shared by the check phase's
workers.

All four node types — `Expr`, `Name`, `Level` and `PropWhen`'s boxed arms —
are a plain `std::sync::Arc`, named once in the crate as `ron::ptr::P`
([`ron::ptr`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/ptr.rs#L1-L8)),
so a handle is one machine word and an `ExprNode` is the packed word beside
the widest constructor's fields (48 bytes, a 64-byte block).  A binder's
`BinderMeta` — the codomain prop-ness annotation (`PropWhen`) — is held by
value, which is what sets that width.

**Tasks #94-#97-SWAP had a denser `Expr`**: the constructor in the handle's
low four bits, a block per kind (32 bytes for an `app`, 75 % of the live
nodes), and it is what brought the `Expr`-tree checker's memory to
con-leche's level.  It needed a crate-private tagged handle with twelve lines
of `unsafe`, because putting a constructor in a pointer is outside safe Rust.
**Task #97-SWAP-2 retired it**, and the reason is §7.2's: the shipping
checker is the arena, whose terms are `u32` handles into per-constructor
`Vec`s and which builds no `Expr` at all.  The only `Expr` values a run makes
are the pinned data of §4.5, a few thousand nodes interned once at startup,
and their size is not a lever.  So the verified crate has **no `unsafe` in
it**; `scripts/lint-rust-style.sh` asserts that, with no path exemption to
add.

Nodes of every kind are built only by smart constructors such as
[`app`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/expr.rs#L497-L513),
which is what the well-formedness predicate of §6.2 is built from.

### 4.3 Naturals and hash maps

Two things Lean's runtime provides are the very things the project wants
out of the trusted base, so the port carries its own: `ron::Nat`, an
arbitrary-precision natural as a normalised vector of 64-bit limbs
([`nat.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/nat.rs#L1-L8)),
replacing the GMP-backed `Nat`; and `ron::HashMap`, a chained hash map
after the Aeneas tutorial's verified one
([`hashmap.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/hashmap.rs#L1-L10)),
replacing `Std.HashMap`.  Both are verified against their mathematical
specifications.  The memo state is fourteen such maps
(`CState`, retired with the `Expr`-tree checker at task #97-SWAP),
one per con-leche memo table, with the same keys and the same policy.

The per-call memos of the term walks — substitution, abstraction, level
instantiation, the scope and definedness guards, and `beq`'s pair memo —
follow con-leche's one discipline for all of them: **memoise only what is
shared**.  Past each walk's cutoff, a node is probed and recorded only if it
is compound: a leaf is decided on the spot, so an entry for it could never
save a descent.

con-leche's own gate has a second half, `withExclusive` — skip the memo where
the node's reference count is one, since the walk inside its only parent
meets it once — and tasks #94-#98 ported it as a read of the tagged handle's
count.  **Task #97-SWAP-2 retired that read with the handle.**  `ron::ptr`'s
four operations do not include one (DESIGN.md §3.2), the model's answer for
it was `false` — always memoise — at every site, and the walks it gated are
the `Expr`-tree ones the swap deleted; the arena's memo policy is its own.
So nothing in the verified crate looks at a reference count, and §8.1 has one
fewer row than it did.

### 4.4 The knot, fuel, and the pins

con-leche's core is a knot of six mutually recursive operations
(`whnfCore`, `whnf`, `infer`, `defeq`, `annotate`, `inferIO`) tied through
a record and a fuel.  Aeneas rejects recursion that mixes functions and
trait methods, so the knot is six plain mutually recursive functions with
the fuel as an argument
(the wrappers of `cached::core_c`, retired at task #97-SWAP),
each probing its memo table, running its body one fuel step down, and
inserting.

con-leche checks `Nat.div` and `Nat.mod` against a list of pinned
elaborations.  The port embeds that list as text in the verified core
([`PINS_TEXT`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/pins_text.rs#L40-L44),
generated from con-leche by `scripts/gen-pins.sh`) and decodes it with a
verified decoder
([`decode`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/pins_decode.rs#L1328-L1345))
whose output is well-formed by construction.  con-leche's fold takes the
pin list as a parameter, so nothing is assumed about its value.

### 4.5 Errors

The Rust error type has con-leche's three kinds and a fourth
([`CheckError`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/core_types.rs#L87-L92)):
`Native` is a failure con-leche cannot have, such as a shift amount beyond
64 bits or a pin text that does not decode, and the refinement claims
nothing about it.  The other three mirror con-leche's `throw` sites one for
one, and the refinement says con-leche throws the same kind.  Where
con-leche backtracks (`orElse`, in the pin loop) the port backtracks from a
snapshot of the memo state on a mirrored error and keeps a `Native` one as
the verdict
(`or_else_step` of `cached::checker_c`, retired at task #97-SWAP).

### 4.6 The frontend

The whole path from the file's bytes to the fold is in the verified crate,
under `crates/con-ron-core/src/frontend/`
([the module map](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/frontend/mod.rs#L19-L31)):
the byte recogniser (a port of con-leche's `Scan/Fast.lean`, the
`@[csimp]`-selected scanner its binary actually runs, not the naive
specification), the record assembly, the projection rewrite, the ground
hoist, the prelude reorder, and the embedded prelude text.

This directory is the one exemption from the recursion rule: the scanner
recurses once per byte, which Lean compiles to a loop and Rust would not,
so `while`, `loop` and `for` are allowed here and nowhere else.  The
extraction runs with `-loops-to-rec`, so each loop becomes a `foo_loop`
function mirroring the Lean recursion, and the proofs are about that.  The
Rust cost is a shape rule (AENEAS_FINDINGS.md §2.6): a loop is the last
thing in its function, or it becomes its own function.

The **in-process modeller** for mutual and nested inductive blocks stays
unverified, behind a one-method trait
([`Modeller`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/frontend/types.rs#L261-L271))
that the parser takes as a type parameter.  Charon renders a trait method
on a type parameter as an opaque function, so the extracted parse is
quantified over an arbitrary modeller, and the theorem carries two
hypotheses about it (§3) rather than a port of six thousand lines whose own
note says soundness needs nothing from them.  Upstream may remove the
modeller, and the hypotheses go with it.

### 4.7 The crates

`con-ron-core` is the verified crate: the checker, the frontend, and
`ron::{nat, hashmap, ptr, tagged, node}`.  `con-ron` is unverified: the
modeller, the driver (the file reader, the flags, the exit codes, the
heartbeat), and the check phase's worker pool
([`pool.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L1-L11)).
`con-ron-dump` holds the `con-ron-pins/1` reader and writer and the global
allocator
([`MiMallocTight`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-dump/src/lib.rs#L155-L203)),
which enters mimalloc by `mi_malloc` for word-aligned requests so that
small blocks land in the size class their size says.

## 5. Keeping the port in sync with con-leche

Every Charon-visible item of the core carries a citation of the con-leche
source it ports, as a doc line `/// con-leche: <path>:<a>-<b> <declaration>`
([an example](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/level.rs#L125-L127)),
or `/// con-leche: none — <reason>` for an item with no Lean counterpart.
The pinned con-leche commit fixes what those citations mean.
`scripts/provenance.py` has three modes:

* `check` (a gate): every item cites, every citation resolves to the named
  declaration at the cited range, and no `CHANGED` marker is left;
* `update`: after a bump, relocate every citation whose text merely moved,
  and mark every one whose text changed with a `CHANGED` line that the
  porter deletes once the item is re-ported and re-proved;
* `coverage`: which con-leche declarations are cited and which are
  deliberately skipped, each with a reason in `scripts/provenance-skip.txt`.

A bump is: edit the `rev` in `proof/lakefile.toml`, run `lake update
con-leche` in `proof/`, run `provenance.py update`, then work through the
findings.  DESIGN.md §7 is the full procedure.  Two things it insists on:
classify the findings before editing anything, since most of a large bump's
findings are renames and no Rust work, and expect the proofs to report the
rest, because a refinement lemma that no longer elaborates is a con-leche
change that reached the port.

`scripts/progress.py` counts, per con-leche file, the lines to translate,
translated (cited), and verified (cited by an item with a `_refines`
lemma); `scripts/loc.py` puts upstream, Rust, generated and proof lines
side by side.  Both print a summary at the end of the gates.

## 6. The verification

### 6.1 From Rust to Lean

Charon compiles the verified crate to its intermediate representation and
Aeneas translates that to Lean: one definition per function in the
`Result` monad (`ok`, `fail`, `div`), `&mut` arguments as state passing,
recursion as `partial_fixpoint`.  The output is committed under
`proof/ConRon/Generated/` and regenerated by `scripts/extract.sh`; a gate
fails if the committed model is not what the crate extracts to today.

What the translator cannot see, it declares as an axiom and asks for a
model, which is written by hand in
[`TypesExternal.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/TypesExternal.lean#L42)
and
[`FunsExternal.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L26-L45).
These *holes* are the sharpest part of the trust surface, and §8.1 lists
all of them.  Two ideas cover them: a counted pointer is modelled as its
contents, which is faithful because the port never mutates through one (the
lint forbids `get_mut`, `make_mut`, `Weak` and interior mutability); and a
pointer-equality test is modelled as `false`, an under-approximation the
proof is sound against because every pointer shortcut in the Rust has a
lemma showing its result is what the full computation gives.

### 6.2 Abstraction and well-formedness

The proof relates Rust values to con-leche values through abstraction
functions (`absName`, `absLevel`, `absExpr`, `absEnv`, …) and, for the
memo state and the environment index, through relations:
[`StateRel`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/State.lean#L640-L671)
says every lookup in every one of the fourteen maps agrees under the
abstractions, and
[`FEnvRel`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/FEnv.lean#L96-L104)
the same for the index.

Well-formedness is an inductive predicate whose constructors *are* the
port's smart constructors
([`ExprWF`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L636-L649)):
a node is well-formed if some smart constructor returned it on well-formed
children.  No proof ever names the hash formula; that the packed word's
bits are con-leche's computed fields, and that `absExpr` is injective on
well-formed terms, follow from that definition once.  The parser's proofs
in `proof/ConRon/Refine/Frontend/` thread the same invariant through the
parse state, which is why the parsed capstone needs no well-formedness
hypothesis.

### 6.3 The statements

A leaf operation refines its con-leche counterpart as a plain equation
with the abstractions.  A stateful one is stated over the whole outcome
([`Sim`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/Core/Arms/Shape.lean#L102-L119)):
for related states, if the Rust returns `Ok r` then con-leche's action
returns `abs r` in a related state and `r` is well-formed; if it returns a
mirrored error, con-leche throws the same kind
([`ErrSim`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L1059-L1061));
a `Native` error claims nothing.

The knot is one proposition indexed by the fuel
([`KnotSpec`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/Core/Statements.lean#L191-L194)):
the six wrappers at fuel `n` refine con-leche's knot at `n`, and the six
bodies at `n` refine con-leche's bodies applied to that knot.  The induction
on the fuel
([`knot_induction`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/Core/Knot.lean#L895-L910))
has a memo argument per wrapper and one lemma per body arm, in the files of
`Refine/Core/Arms/`.  Above the knot sit the declaration checker, the two
inductive install routes
([`IndRoutesSpec`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/RefineOld/IndSpec.lean#L80-L100)),
the fold, the frontend, and the capstones of §3.

### 6.4 Differential testing

Beside the proof, the port is checked against con-leche on data.
`scripts/diff-e2e.sh` runs the whole binary on every one of con-leche's own
fixtures (its `tests/arena`, `tests/e2e` and `tests/annot` suites, 383
streams) and compares the exit code against con-leche's committed
expectation, in both modes, with and without the embedded pin list, and at
several worker counts.  This is what tests the parts the proof does not
cover: the driver, the pool and the modeller.  The scanner was additionally
run beside its predecessor over 119 million real export lines and 31
million mutated ones with no disagreement, since most of a scanner's
behaviour is in the lines it rejects.

## 7. Results

### 7.1 The ledger

| | |
|---|---|
| con-leche core (`Kernel`, `Cached`) lines to port | 14 136, all ported, 91 % verified (the rest deliberately skipped, listed with reasons) |
| con-leche frontend lines to port | 4 441, all ported into the verified crate, 59 % verified by lemma citation (the capstone covers the whole path) |
| con-leche modeller and driver lines to port | 2 902, all ported, unverified by design |
| Rust, verified crate | 50 971 lines (28 300 of them two generated text constants), 1 894 functions, every item cited |
| Rust, unverified crates | 11 235 lines |
| generated Lean model | 73 269 lines |
| proofs | 189 574 lines, 5 494 theorems; 1 612 `_refines` lemmas |

The Rust is 2.75× the Lean it ports, the model 1.44× the Rust, the proofs
3.7× the Rust.

### 7.2 Performance

Measured with `perf stat -e instructions:u,cycles:u` as the measure of
record, wall time and peak resident set as secondary numbers, on
`lean4export` exports of Lean's `Init`, of `Init`+`Std`+`Lean`, and of
Mathlib; both binaries at the pinned con-leche commit, in verified mode,
release builds with mimalloc.  DESIGN.md has the measurement notes.

| export | jobs | con-leche instructions | con-ron instructions | con-leche wall | con-ron wall | con-leche peak RSS | con-ron peak RSS |
|---|---|---|---|---|---|---|---|
| `Init` (57 977 declarations) | 1 | 585.9 G | 542.1 G | 56 s | 61 s | 0.48 GB | 0.48 GB |
| `Init` | 8 | 587.2 G | 544.3 G | 12 s | 20 s | 0.67 GB | 1.18 GB |
| `Init`+`Std`+`Lean` (163 396) | 1 | 1 176.3 G | 1 155.3 G | 122 s | 147 s | 1.22 GB | 1.34 GB |
| `Init`+`Std`+`Lean` | 8 | 1 179.4 G | 1 166.6 G | 37 s | 73 s | 1.46 GB | 2.80 GB |
| Mathlib (691 128) | 1 | 12 792.4 G | 11 484.4 G | 1 220 s | 1 979 s | 8.75 GB | 7.80 GB |
| Mathlib | 8 | 12 843 G | 11 343 G | 337 s | 929 s | 9.1 GB | 17.8 GB |

Single-threaded, con-ron executes 2–10 % fewer instructions than
con-leche, takes 1.1–1.6× the wall time, and uses the same memory or less.
At eight workers the wall-time gap widens to 1.7–2.8×: con-leche's check
phase scales better, its reference counts being plain where con-ron's are
atomic.  The eight-worker memory cells predate the per-kind node layout of
§4.2 and have not been re-measured.

### 7.3 What the proof found

The proof was the port's most productive test.  Deviations it caught in
code that had passed every fixture include a division-by-zero guard weaker
than con-leche's, which would have *accepted* what con-leche rejects; a
non-short-circuiting boolean `and`; a memo table that evicted its own
entries on a hash collision; a `u64 → usize` cast family in the modelled
inductives; two record-assembly errors in the parser; and, in the
translator, an Aeneas model of `Vec::insert` that overwrote where Rust
inserts (AENEAS_FINDINGS.md §3.9).

## 8. Trust assumptions

What has to be right for the theorem to mean what it says about the
binary.  §8.1 is the part a script keeps honest; §8.2 is everything else.

### 8.1 What the proof does not see: the holes

The theorem is about the verified crate *as Aeneas translates it*.  Where
the translator meets an item it cannot translate, it declares it as an
axiom and asks for a model (§6.1).  Every such model is a claim about the
Rust that no proof checks, so here they all are: **six**, one type and five
functions, and every one of them is the standard library's — the four `Arc`
operations of §3.2 and `str::as_bytes`.  There is nothing of the project's
own in the list.  (Tasks #94-#97-SWAP had seventeen more, the tagged `Expr`
handle of §4.2; task #97-SWAP-2 put `Expr` back on `Arc` and they are gone
with it, `ron::node::view` included — the projection is an ordinary
translated `match` now.)  `scripts/extract.sh --check` fails if the crate
grows a hole nobody modelled; `scripts/holes.sh --check` fails if this table
and the holes drift apart.

<!-- holes: begin — scripts/holes.sh --check keeps this table and the templates in step; the first cell holds the Lean names of the holes, in backticks -->

| hole | the Rust | the model | why the model is faithful |
|---|---|---|---|
| [`alloc.sync.Arc`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/TypesExternal.lean#L41-L42) | `Arc<T>`, named once as [`ron::ptr::P<T>`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/ptr.rs#L1-L8) | `T`: a pointer *is* its contents | The port never mutates through an `Arc` (the lint forbids `get_mut`, `make_mut`, `Weak` and interior mutability), so sharing is invisible to the value |
| [`alloc.sync.Arc.new`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L25-L26), `alloc.sync.Arc.Insts.CoreCloneClone.clone`, `alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref` | `Arc::new`, `Arc::clone`, `Deref::deref` | `ok x`: the identity | Allocation, a count bump and a dereference return the same contents; the model has no notion of the count |
| [`alloc.sync.Arc.ptr_eq`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L36-L38) | `Arc::ptr_eq` | `ok false`: the model always takes the slow path | An under-approximation: every place the Rust takes the fast path (the memo tables' pointer-verified buckets, `beq`'s pointer fast path) has a lemma that the fast path's result is the slow path's |
| [`core.str.Str.as_bytes`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L71-L72) | `str::as_bytes`, at its one call site on `PINS_TEXT` | `ok s`: the identity | Aeneas already models a `&str` as its bytes |

<!-- holes: end -->

### 8.2 The rest of the trust surface

| trusted | what stands in for it |
|---|---|
| **con-leche's own assumptions**: a set theory `V` with `ConLeche.SetTheory V`, Lean's kernel checking the proof, and the axioms `propext`, `Classical.choice`, `Quot.sound` | con-leche's OVERVIEW says what those are |
| **Aeneas and Charon**: the Lean model is what the translator says the Rust means | Nothing; a translator bug is a hole.  The port stays inside the documented subset (§4.1) and records what it found in `AENEAS_FINDINGS.md`, all of it worked around in the Rust |
| **`rustc`, the Rust standard library, and the allocator** | Nothing.  This is the trade the project makes: Lean's compiler, runtime and GMP for these.  The allocator cannot change a verdict, only memory and time |
| **`overflow-checks = true`** in the [release profile](https://github.com/leanprover/con-ron/blob/master/Cargo.toml#L19-L23) | The model is the checked-arithmetic one.  A build without it would wrap where the model fails, and the model would no longer describe it |
| **The modeller**, [`crates/con-ron/src/in_model/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/in_model.rs#L28-L32), unverified by design | The two hypotheses of §3, `ModellerWF` and `ModellerRefines`.  Every record it generates is checked by the fold as a stream declaration, so a wrong one is rejected or declined, never accepted; what it decides is which blocks the checker can accept, not whether an accepted one is sound |
| **The driver**, [`driver.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L5-L14) | That it calls the verified steps on the bytes it read and on the embedded pin text, and maps the outcome to the exit codes of §1 |
| **The worker pool**, [`pool.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L49-L56) | An argument, not a proof: the workers' results are merged by record index and walked in record order, so the verdict is the sequential walk's at every `--jobs`, and a test that a failure is reported first at every worker count |
| **One extra axiom on the embedded pair only**, `pins_text.PINS_TEXT._native.decide.ax_1` | Aeneas discharges the size bound of every extracted string constant with `decide +native` in the constant's own definition (AENEAS_FINDINGS.md §3.8).  It lives in a definition, not a computation, and is not the port's to remove; the parsed capstone does not carry it |

And **no `unsafe`** in the verified crate: tasks #94-#97-SWAP had twelve
lines of it in a tagged `Expr` handle and this table had a row for them,
which task #97-SWAP-2 deleted along with the module (§4.2).
`scripts/lint-rust-style.sh` asserts it.

Nothing else: no `native_decide`, no `sorry`, no axiom beyond the three in
the headline theorems.

## 9. Proof techniques

Most of the proof lines are hand proofs in one shape: invert the Rust run
(a `do` block in the `Result` monad unfolds into a chain of binds, each
either `ok` with an equation or an early exit), apply the lemma of each
callee through the state relation, and close with the constructor of the
well-formedness predicate.  The Aeneas library's `progress`-style tactics
were tried and set aside: with the relations and abstraction functions in
context, forward refinement with equations is the shorter style here
(AENEAS_FINDINGS.md §3.3).

A second style exists for new lemmas
(`proof/ConRon/Refine/AUTOMATION.md`): `rust_norm h` reduces the Rust
equation in pre-order with two registered simp sets and peels the binds,
then `all_goals rust_grind`, which is `grind` with a fixed configuration
([`rust_grind`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L285-L291))
and the callee lemmas registered as `grind →` rules keyed on the Rust
equation.  With a node-shaped induction principle, a memoised term walk is
one line.  It costs 1.2–1.8× the hand proof's elaboration time on leaves
and 3–4× on memo walks and knot arms.  The rule: existing hand proofs are
not rewritten; new lemmas use the idiom where it applies (leaves, walks,
arms), and not for the mathematical `Nat` and `HashMap` tiers, the
byte-level pin decoder, or list folds.

Every lemma is stated over the whole outcome (§6.3) because con-leche
backtracks on an error: an "error means nothing" lemma cannot follow
`orElse` through a retry.  `progress.py`'s statement-shape classifier is
what a con-leche bump uses to see which lemmas are stale.

## 10. Patches against upstream

* **Aeneas' Lean library on Lean v4.33**
  ([`patches/aeneas-433.patch`](https://github.com/leanprover/con-ron/blob/master/patches/aeneas-433.patch)).
  The pinned Aeneas builds its Lean library against Lean v4.31 and
  con-leche is on v4.33; the patch, 375 lines to ten files, makes the
  library build on v4.33 and its Mathlib.  Two options the proofs need are
  set in `proof/lakefile.toml`
  ([the options](https://github.com/leanprover/con-ron/blob/master/proof/lakefile.toml#L24-L26)).
  AENEAS_FINDINGS.md §3.1 has the details; the ask upstream is a v4.33
  release.
* **Nothing else.**  Charon is unpatched, con-leche is used at an upstream
  master commit, and every translator finding was worked around in the
  Rust.

## 11. Naming and module map

Rust modules mirror con-leche's files (`ConLeche/Kernel/Level.lean` →
`crates/con-ron-core/src/kernel/level.rs`, `ConLeche/Cached/CoreC.lean` →
`cached/core_c.rs`), nested under `kernel/`, `cached/`, `frontend/`, `ron/`
because Aeneas prints unqualified names.  A function keeps con-leche's name
in snake case; con-leche's `fooC` twins are `foo_c`; a function con-ron
adds is marked `con-leche: none` with its reason.  Proof files mirror the
Rust modules; a lemma about `foo` is `foo_refines`; the abstraction
functions are `abs*`, the relations `*Rel`, the well-formedness predicates
`*WF`.

| where | what |
|---|---|
| `crates/con-ron-core/src/kernel/` | the pure checker: `name`, `level`, `prop_when`, `expr`, `expr_ops`, `env`, `fenv`, `core_k`, `checker*`, `decl_check`, `type_checker`, the basis tables, `canon` (the pin match), the axiom tables, `inductives/*`, `pins_text`, `pins_decode` |
| `crates/con-ron-core/src/cached/` | the memoising checker: `state_c`, `expr_ops_c`, `core_c` (the knot), `checker_c`, `parsed_c`, `installed` (`check_decls`) |
| `crates/con-ron-core/src/frontend/` | the export parser (§4.6): `scan_types`, `scan_fast`, `export`, `export_c`, `proj_rec`, `nat_op_ground`, `prepare`, `prelude`, and `in_model_rec` (the `Modeller` seam) |
| `crates/con-ron-core/src/ron/` | `nat`, `hashmap`, `ptr`, `tagged`, `node`: what replaces the runtime |
| `crates/con-ron/src/` | the modeller (`in_model`), the driver, the pool, the binary |
| `crates/con-ron-dump/` | the `con-ron-pins/1` reader and writer, the allocator |
| `proof/ConRon/Generated/` | the committed Aeneas model and the hand-written models of the holes |
| `proof/ConRon/Refine/` | the proofs: `Abs`, `State`, `FEnv` (abstractions and relations), `Excl` (the exclusivity read's model); one file per Rust module; `Core/` (the knot); `Ind*` (the inductive routes); `Pins*` (the decoder); `Frontend/` (the parser); `Installed`; `Main` (the capstones) |
| `proof/ConRon/Refine/README.md` | the proof tier's own map: naming, the hypothesis table, how to write a lemma |
| `vendor/aeneas/` | Aeneas, as a submodule, for its Lean library and documentation |
| `scripts/` | the gates and the tooling of §5 |

## 12. Gates

`scripts/gates.sh` runs, in order, and stops at the first failure
([the fifteen steps](https://github.com/leanprover/con-ron/blob/master/scripts/gates.sh#L60-L88)):

1. `cargo build` with warnings denied;
2. `cargo test`;
3. `scripts/lint-rust-style.sh`: the Aeneas subset (§4.1);
4. `scripts/provenance.py check`: every item cites, every citation resolves, no `CHANGED` marker left — in the Rust and, since task #97, in the arena checker's Lean (`proof/ConRon/Arena/**`);
5. `scripts/provenance-selftest.py`: that gate's Lean parser against its own fixture (`scripts/testdata/provenance/`), one declaration per accepted shape and one per finding;
6. `scripts/twin-lines.py check`: the other half of the same ledger — every `Lean twin:` doc line of the Rust names a declaration of `proof/ConRon/**` that exists, and gives its CURRENT lines (task #97-TWIN; `update` relocates by name, a name that is gone is re-pointed by hand);
7. `scripts/overview-links.sh`: every line-anchored link in this document and in `DESIGN.md` still points at the text it cited (the cited lines are a committed artefact, `scripts/overview-links-expected.txt`, in con-leche's idiom);
8. `scripts/holes.sh --check`: §8.1's table is exactly the set of holes the Aeneas templates declare;
9. `scripts/gen-pins.sh --check`: the embedded pin text is what con-leche's list generates;
10. `scripts/gen-prelude.sh --check`: the embedded prelude text is con-leche's own;
11. `scripts/gen-prelude-lean.sh --check`: so are the arena checker's own committed prelude bytes (`proof/ConRon/Arena/Frontend/PreludeText.lean`, task #97e);
12. `scripts/extract.sh --check`: the committed model is what Charon and Aeneas produce, and every hole it declares is modelled by hand;
13. `lake build` of the model and the proofs — the DEFAULT targets;
14. `lake build ConRonRefine2` — Theorem 2's tier, which is deliberately not a
    default target (a half-built P5 tier must not block `lake build`) and was
    therefore elaborated by no gate at all until task #97-P5-Mut found it;
15. `lake build ConRonBridge` — **Theorem 1's spec layer, for the same
    reason**: it is not a default target either, so step 13 never elaborated
    a module of `proof/ConRon/Bridge/**`.  Task #97-P3-Ind round 5 found this
    the way it deserved to be found — a green gate run followed by a broken
    `lake build ConRonBridge`.

It ends with the summary lines of `progress.py` and `loc.py`.  The
differential tests of §6.4 are not in the gates, since they need the
exports; CI runs them.  One landing rule is neither: anything that touches
memory is run on the Mathlib export under `ulimit -v 27000000` before it
lands, since CI and the kernel arena skip Mathlib.
