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
`model_exists` and its letter about `False` are theorems about the Rust
binary too.  The point is to take the Lean compiler, the Lean runtime
and its bignum library out of the trusted base of a proof that a Lean
development is consistent: a bug in those would have to have a twin in
`rustc` and Rust's runtime for the two checkers to agree wrongly.

## 0. Using the checker

The binary reads a Lean export in `lean4export`'s NDJSON format and
prints one verdict line
([the usage text in `con-ron.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron.rs#L116-L188)):

```
con-ron [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
        [--progress[=<stride>]] [--pins FILE|--no-pins]
        FILE.ndjson
con-ron --help
```

`--verified` is the default and the mode the theorem is about.
`--trusted` runs the same checker bodies with the certification-only work
switched off; it is faster and outside the theorem.  `--jobs=<n>` is the
check phase's worker count, defaulting to one per hardware thread capped
at 16, because each worker reserves a gigabyte of address space for its
stack.  `--progress[=<stride>]` is a heartbeat on stderr.  The two flags
con-leche does not have are marked as con-ron's own in the usage text:
`--pins FILE` and `--no-pins` replace the embedded pin list for testing.  `--no-mark-persistent` is accepted and does nothing: the
Lean-runtime device it turns off has no counterpart in a program whose
reference counts are atomic by type.

`N` is the *file's* own accepted declaration records — one per
`def`/`theorem`/`opaque`/`axiom`/`inductive`/`quot` record it declares.  The
built-in prelude's records and the ones the in-process modeller generates are
not counted; a stream record that declares a prelude declaration is, because
the preparation (§3.7) moves it to the front rather than dropping it.  con-ron
and con-leche print the same number — on Lean's `Init` both say 57 977.

Between the file and that line the binary runs con-leche's four pure steps —
the built-in prelude, the parse of the file's byte chunks, the preparation,
the fold — and since task #84 all four are functions of the *verified* crate
(§3.7).  What belongs to the driver is what is not a function of the input:
reading the file 4 MiB at a time, the flags, the heartbeat, the worker pool,
and the in-process modeller it hands the parse.

The exit code follows the Lean kernel arena convention, the same as
con-leche's
([the exit-code table in `driver.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L41-L46)):

| exit | verdict | meaning |
|---|---|---|
| 0 | `accepted N declarations` | every declaration checked; `N` counts the file's declaration records |
| 1 | `rejected` | a declaration is invalid |
| 2 | `declined` | the checker positively detected a feature it does not support, and says which |
| 3 | error | bad usage, malformed input, or an internal failure of unclear cause |

## 1. Building

Three toolchains meet here, and `flake.nix` pins two of them
([`flake.nix`](https://github.com/leanprover/con-ron/blob/master/flake.nix#L5-L29)):
Aeneas at a fixed commit, which pins the Charon it needs, which pins the
Rust nightly it needs.  `nix develop` (or `direnv allow`) gives a shell
with `cargo`, `rustc`, `charon` and `aeneas`.  Lean comes from `elan`,
at the version in `proof/lean-toolchain` (the same as con-leche's).

```
nix develop                        # cargo, charon, aeneas on PATH
cargo build --release              # target/release/con-ron
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
([the nine steps](https://github.com/leanprover/con-ron/blob/master/scripts/gates.sh#L53-L61)):
the Rust build and tests with warnings denied, the style lint (§3.6),
the provenance check (§4), the link gate, the two embedded-text checks
(the pin list and the built-in prelude), the extraction check
(the committed Lean model must be what Charon and Aeneas produce from the
crate today), and the Lean build.  §12 has the list.

## 2. What is proved

The headline theorem is stated for the Rust checker's own entry point,
`check_decls` in the verified core, with the pin list it uses obtained
from the verified decoder on any input
([`conron.model_exists_decoded` in `Main.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L303-L310)):

```lean
theorem conron.model_exists_decoded (V : Type w) [ConLeche.SetTheory V]
    {text : Slice Std.U8} {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    {ds : alloc.vec.Vec env.Declaration} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e))
```

and its companion
[`conron.no_proof_of_False_decoded`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L318-L326):
if the Rust `check_decls` in verified mode accepts the parsed
declarations `ds` and returns the environment `e`, then that environment,
abstracted to con-leche's, has a model in every set theory, and contains
no constant whose type is `False`.  `absEnv` is the abstraction function
from the Rust environment to con-leche's (§5).  The hypotheses are three:
a run of the decoder, a run of the checker, and `hds`, that every parsed
declaration is well-formed — its terms are what the core's smart
constructors built, which is what the parser does by construction.  Since
task #84 that parser is *in* the verified core and has a Lean model like
everything else (§3.7), and **since task #85 `hds` is proved rather than
assumed** (§3.5): there is a second, chunk-level pair below that states the
same thing about con-leche's whole pipeline — the prelude, the streaming
parse, the preparation and the fold — and carries no well-formedness
hypothesis at all.  Nothing is assumed about the pins' value, because the fold
is parametric in them (§9).

The chunk-level pair is
[`conron.model_exists_parsed`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L550-L564)
and its companion `conron.no_proof_of_False_parsed`:

```lean
theorem conron.model_exists_parsed (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hgen : Frontend.ModellerWF inst g)
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    (hpre : frontend.export_c.parse_bytes inst g prelude_bytes true false = ok (.Ok pre))
    (hparse : frontend.export_c.parse_chunks inst g chunks in_model census = ok (.Ok r))
    (hprep : frontend.prepare.prepare_prelude ⟨pre.decls⟩ r.decls = ok ds)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e))
```

What stands where `hds` stood is `hgen`, **one line about the modeller**: every
declaration the in-process generator returns is well-formed.  That is the
residue task #84's seam left, and the maintainer's decision to leave the
modeller unverified; it disappears the day upstream drops it (§7).  The prelude
is a *parameter*, not a constant — identifying the port's embedded prelude with
con-leche's `include_str` is out of reach in the kernel
(AENEAS_FINDINGS.md §3.8) — with the
corollary at the shipped constant stated beside it.

That pair's census is the standard three, and it took a Rust change to get
there.  Until task #86 it was those plus **68 axioms that are the
translator's**, one per `&str` constant in the scanner's key table, which
Aeneas' `toStr` spends with `decide +native` in each constant's own
*definition* — the same artifact the embedded pair still pays once, below.
Nothing was ever evaluated; the axioms came through the closure, and `#print
axioms` on the generated `scan_line_fwd` printed the same 68.  Task #86 spelled
the whole table as `[u8; N]` byte arrays, which carry no axiom, so the parsed
pair and the corollary at the shipped prelude are both pinned at con-leche's
own three.

Both censuses are pinned by `#guard_msgs` at con-leche's own three axioms
([the censuses](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L328-L332)):
`propext`, `Classical.choice`, `Quot.sound`.  No `native_decide`, no
`sorry`, nothing sealed.

**Since task #87 the theorem begins at the bytes.**  The pair above says
*"whatever the parser produced, the fold's accept has a model"*; what it did
not say is that the parser produces what con-leche's parser produces.  That is
the parser's **exactness** tier (§5.2), and on top of it sits
[`conron.no_False_declaration`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L726-L742)
— con-leche's own main corollary transported:

```lean
theorem conron.no_False_declaration (V : Type w) [ConLeche.SetTheory V]
    (hgen : Frontend.ModellerWF inst g)
    (hsp : Frontend.IndRSpec inst g)
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    (hpre : frontend.export_c.parse_bytes inst g prelude_bytes true false = ok (.Ok pre))
    (hfalse : ConLeche.jsonWithTheoremFalse (Frontend.absChunks chunks))
    (hparse : frontend.export_c.parse_chunks inst g chunks im ce = ok (.Ok r))
    (hprep : frontend.prepare.prepare_prelude ⟨pre.decls⟩ r.decls = ok ds)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    False
```

— *a file whose bytes declare a theorem of type `False` in the shape
`jsonWithTheoremFalse` describes is never accepted by the Rust pipeline*, with
`conron.no_False_declaration_prelude` the same at the prelude the binary ships.
Both are pinned at the same three axioms.  The prelude is not identified with
con-leche's and does not have to be: `mem_preparePrelude` holds for every
prelude, so the statement is prelude-parametric for free.  What it still takes
about the parse is named rather than assumed wholesale, and it is a short list:
`hsp`, three facts about the inductive install path, and `hgen`, the modeller's
own promise — the residue task #84's seam left on purpose (§7).  The scanner's
UTF-8 decoder and the ground hoist stood here earlier and are now theorems.
Everything else between the bytes and `parseChunks` is proved.

Three more forms exist for readers who want them.  The general pair
([`conron.model_exists`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L174-L185))
names the two facts the induction owes — that the core knot refines
con-leche's at the checker's fuel, and that the two inductive install
routes refine theirs — as hypotheses, and the well-formedness of the pins
as a third; the primed pair
([`conron.model_exists'`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L241-L251))
discharges the first two from the knot induction (§5).  The embedded pair
([`conron.model_exists_embedded`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L391-L398))
is the decoded pair at the constant the binary ships, `PINS_TEXT`; its
census carries one axiom more, `pins_text.PINS_TEXT._native.decide.ax_1`,
which is not the port's: Aeneas' `toStr` discharges the byte-length bound
of every extracted string constant with `decide +native`, and the axiom
sits in the constant's definition.  §7 says what that leaves trusted.

What connects the Rust run to con-leche's theorem is one refinement
statement over the whole outcome
([`check_decls_refines` in `Installed.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Installed.lean#L3293-L3304)):
if the Rust fold returns `Ok e`, con-leche's fold returns the abstraction
of `e`; if it returns a mirrored error, con-leche throws an error of the
same kind; if it returns the port's own `Native` error, nothing is
claimed.  The main theorems are that statement's accept case composed
with con-leche's own `model_exists` and `Cached.no_proof_of_False_cached`,
which are already stated for every pin list (§9).

## 3. The checker

### 3.1 What was ported, and how closely

con-leche has a pure checker (`ConLeche/Kernel`) and a memoising one
(`ConLeche/Cached`) proved equivalent to it; the binary runs the second.
con-ron ports the *memoising* checker, one Rust module per Lean file,
functions in the same order, each carrying a doc comment that cites its
source range (§4).  The port covers con-leche's core completely and its
frontend (the export parser and the in-process modeller for mutual and
nested inductives) completely; the *verified crate* holds the core and,
since task #84, the parser (§3.7), and the proof covers the core.  §6 has
the ledger.

Everything that differs is either a data-structure substitution proved to
behave the same (§3.2–3.4) or a Rust idiom the translator requires (§3.6);
con-ron does nothing con-leche does not.

### 3.2 Terms

A term is a reference-counted node
([`ExprNode` and `Expr` in `expr.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/expr.rs#L356-L364)):
the constructor data beside a packed 64-bit word that caches what
con-leche computes in its `@[computed_field]`s — the structural hash, the
loose bound-variable bound, the has-free-variable and has-level-parameter
bits.  The pointer type is `std::sync::Arc`, named in exactly one place
([`ron::ptr`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/ptr.rs#L1-L8)),
so that the installed environment can be shared by the check phase's
workers without `unsafe`; the atomic count costs about 15 % of wall time
single-threaded and buys the pool (§10).  Nodes are built only by smart
constructors such as
[`app`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/expr.rs#L430-L441),
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
([the wrappers in `core_c.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/cached/core_c.rs#L5086-L5117)),
each probing its memo table, running its body one fuel step down, and
inserting — con-leche's `memoEI`, spelled out.

con-leche checks `Nat.div` and `Nat.mod` against a list of pinned
elaborations.  The port embeds that list as text in the verified core
([`PINS_TEXT`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/pins_text.rs#L40-L44),
generated from con-leche by `scripts/gen-pins.sh` and checked by the
gates) and decodes it with a verified decoder
([`decode`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/pins_decode.rs#L1328-L1345))
whose output is well-formed by construction for every input.

### 3.5 Errors, and the input's well-formedness

The Rust error type has con-leche's three kinds and a fourth
([`CheckError`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/core_types.rs#L87-L92)):
`Native` is a failure con-leche cannot have — a shift amount beyond 64
bits, a pin text that does not decode, a malformed input — and the
refinement claims nothing about it.  The other three mirror con-leche's
`throw` sites one for one, classified against their cited source, and the
refinement says con-leche throws the same kind.  Two of those sites decide
their kind from the term rather than from the code path: since con-leche's
task #292 an unresolved constant DECLINES when it is `sorryAx` — the one
axiom the checker tolerates as a declaration, whose record installs nothing
and for which there is no set model — and rejects otherwise, at both choke
points (`core_k::unknown_const_error` inside inference,
`checker_base::unresolved_consts_error` at the guards that keep unresolved
constants out of a stored term), and the port's two lemmas are equations
about the *kind*.  Where
con-leche backtracks (`orElse`, in the `Nat.div`/`Nat.mod` pin loop) the
port backtracks from a snapshot of the memo state on a mirrored error and
keeps a `Native` one as the verdict
([`or_else_step`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/cached/checker_c.rs#L123-L132)).

The theorem's `hds` hypothesis is where the frontend meets the proof.  A
term's packed word (§3.2) caches what con-leche computes in a
`@[computed_field]`, correct by construction in Lean; in Rust the smart
constructors fill it, and a node built any other way could carry a word
that makes the checker's `O(1)` shortcuts wrong.  So the theorem assumes
every parsed declaration is well-formed in the sense of §5.2: its terms
are what the smart constructors returned.  A runtime check was tried and
withdrawn (DESIGN.md, tasks #73 and #81): a pass that rebuilds every node
and compares the word needs a visited set over the export's shared DAG,
and a global set costs about ten gigabytes at Mathlib scale while a
per-declaration one costs 3.6–4.4 % of instructions, over the budget for
a check con-leche does not need.

**Upstream did its half** (con-leche tasks #290 and #294, vendored at task
#83): con-leche's parser is inside its theorem, and its main corollary
`no_False_declaration` is over the byte chunks the binary reads rather than
over a declaration list.  **Task #84 did the port's half of the code**: the
parser is in the verified core now (§3.7), extracted to Lean with everything
else, so `hds` stopped being an audit of unverified Rust.  **Task #85 proved
it.**  `proof/ConRon/Refine/Frontend/` threads one invariant through the parse
state — every name, level, expression and declaration it holds is what a smart
constructor returned — and `parse_chunks_wf` is that invariant read off the
result.  The argument is by construction, exactly as the design said at task
#5: the well-formedness predicates are inductives whose constructors *are*
`expr::app`, `name::mk_str`, `level::succ`, and the parse reaches every node it
stores through one of them, so no proof ever names a cached hash word.  The
scanner owes the parse one fact and only one — that a `Vec<u32>` it hands over
as a string payload holds valid code points — which is a loop invariant on its
UTF-8 decoder.

So the capstones come in two levels now.  The fold-level four still take
`hds`, because a caller who does not go through this parser still owes it; the
chunk-level pair (§2) does not.  What is left outside is the **modeller**: the
parse takes it as a type parameter, and the one thing assumed of it is that
the declarations it generates are well-formed.  §7 says why that residue is
narrow.

The *refinement* of the parser against con-leche's — that the port's scanner
and record assembly compute what `scanLineFwd` and `parseChunks` compute — is
a separate and much larger job, and is not done; `scripts/progress.py`'s parser
row stays at 0 % until it is, since that column counts refinement lemmas.

### 3.6 The Rust subset

Aeneas translates a subset of Rust, and the port stays inside it by rule
rather than by luck: no closures, no `?`, no `derive` at all (explicit
`foo_dup`/`foo_beq` instead), no `unsafe`, no `std::collections`,
higher-order arguments as one-method traits, `&mut` only where the
translation's state passing is wanted, and recursion rather than loops —
with one exemption, the parser, which §3.7 explains.
`scripts/lint-rust-style.sh` enforces the mechanical
part; DESIGN.md §3.4 has the rules and their reasons.  `overflow-checks`
is on in release builds
([`Cargo.toml`](https://github.com/leanprover/con-ron/blob/master/Cargo.toml#L21)),
so an arithmetic overflow the model calls `fail` is a panic in the binary
rather than a wrap.

The unverified crate `con-ron` holds the in-process modeller for mutual and
nested inductive blocks, the driver, and the worker pool of
the check phase
([`pool.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L1-L9));
`con-ron-dump` reads and writes `con-ron-pins/1`, the text format the
pin list travels in (§3.4).  The verified crate is `con-ron-core`.

### 3.7 The parser

Since task #84 the whole path from the file's bytes to `check_decls` is
inside the verified crate, one Rust module per con-leche file, under
`crates/con-ron-core/src/frontend/`
([the module map](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/frontend/mod.rs#L13-L27)):
`scan_types` and `scan_fast` (the byte recogniser), `export` and `export_c`
(the record assembly: the parse state, `process_line_core_d`, `feed_chunk`,
`chunk_step`, `chunk_finish`, `parse_chunks`), `proj_rec` (the projection
rewrite) and `nat_op_ground` (the ground hoist), which are on the parse path
and so came with it, `prepare` (the prelude reorder) and `prelude` with its
generated text constant.  The reason is §3.5's hypothesis: con-leche now
states its main corollary over the file's byte chunks, and a port that stops
at the fold cannot inherit it.

Two things are deliberate about *which* code this is.  The scanner ported is
`Scan/Fast.lean`, not `Scan/Naive.lean` — the naive one is the
*specification*, and `Scan/Equiv.lean`'s `scanLineSpec_eq_scanLineFwd` is the
`@[csimp]` that makes the fast one what the Lean compiler actually runs, so
the fast one is what a theorem about the binary has to be about.  And the
**in-process modeller stays unverified**, behind a one-method trait
([`Modeller`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/frontend/in_model_rec.rs#L258-L269))
that `parse_chunks` takes as a type parameter: Charon renders a trait method
on a type parameter as a typeclass field — an opaque function — so the
extracted parse is quantified over an arbitrary modeller, and its refinement
will carry one hypothesis about that modeller's output rather than a port of
six thousand lines whose own module note says "soundness needs nothing from
this module: a wrong record is rejected or declined by the fold, never
accepted".  What the modeller reads is handed to it as a `ModelCtx`
borrowing the parse state's three tables, which the unverified side rewraps
into the closures its generators overlay.

**The loop exemption.**  `Scan/Fast.lean` recurses once per byte, and Lean
compiles those tail calls into loops; Rust does not promise to, and a
per-byte recursion on a long export line is a stack overflow.  So
`crates/con-ron-core/src/frontend/` — and only that directory — may use
`while`, `loop` and `for`, which the lint enforces as a boundary.  This costs
the proof nothing, because the extraction already runs with `-loops-to-rec`:
each loop becomes a `foo_loop` function that mirrors the Lean recursion one
for one, and that is what the refinement is stated against.  What it costs
the *Rust* is a shape rule, because Aeneas duplicates the code after a loop
into every one of its exits and refuses a `return` out of a loop whose tail
is anything but trivial (AENEAS_FINDINGS.md §2.6): a loop is the last thing
in its function, or the loop becomes its own function.

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
a new pin line, and `provenance.py update --old <the commit before the
pull>`, which diffs the new tree against the old one; DESIGN.md §7 has the
whole procedure, written from the one large bump the arrangement has been
through (task #83, 101 upstream commits and 583 findings).  Two things that
procedure insists on, because they are what the tooling does *not* do for
you: classify the findings before editing anything — 338 of those 583 were a
con-leche rename and no Rust work at all — and expect a *renamed* declaration
to come out `GONE` rather than `CHANGED`, its citation left pointing at a
stale range.  The proof then says what else moved: a refinement lemma that no
longer elaborates is a con-leche change that reached the port, and a con-leche
rename that costs no Rust still costs every statement that named the old
declaration.

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
today.  The model is about 53 000 lines for about 38 000 lines of Rust.

Two things the translation cannot see are modelled by hand
([`TypesExternal.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/TypesExternal.lean#L42),
[`FunsExternal.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L26-L45)):
an `Arc<T>` is its contents, and `Arc::ptr_eq` is `false`.  The first is
faithful because the port never mutates through an `Arc` (the lint
forbids `get_mut`, `make_mut`, `Weak` and interior mutability), so sharing
is invisible to the value.  The second is an under-approximation the
proof has to be sound against: every place the Rust takes a pointer-equal
shortcut, the proof shows the result is what the full computation gives —
the memo tables' pointer-verified buckets and `beq`'s pointer fast path
each have that lemma.

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

That shape is also what makes the parser's proof short (§3.5).  The parse
builds every node it stores by calling one of those constructors, so each
lemma of `proof/ConRon/Refine/Frontend/` is a forward walk through a generated
body applying one constructor per arm; the state's invariant, `StateDWF`, is
the same thing for the three index tables and the declaration list it carries.

### 5.3 The statements

A leaf operation refines its con-leche counterpart as a plain equation
with the abstractions.  A stateful one is stated over the whole outcome
([`Sim` in `Shape.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Core/Arms/Shape.lean#L102-L119)):
for related states and environments, if the Rust returns `Ok r` then
con-leche's action returns `abs r` in a related state and `r` is
well-formed; if it returns a mirrored error, con-leche throws the same
kind
([`ErrSim`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L934-L942));
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
data.  `scripts/diff-e2e.sh` runs the whole `con-ron` binary on every
one of con-leche's own fixtures — its `tests/arena`, `tests/e2e` and
`tests/annot` suites, 348 streams — and compares the exit code against
con-leche's committed expectation for that stream, in both modes, with
and without the embedded pin list, and at several worker counts.  Being
end-to-end is the point: everything above the fold is unproved, and a
sweep that fed the checker a ready-made declaration list would test
neither the parser nor the rules that live above the fold (the
frontend's own verdicts, the modeller's coverage).  A run is green only
when every case agrees.

Earlier tasks ran a second, narrower sweep through a text dump of
con-leche's parsed declarations, which let the Rust checker be exercised
before a Rust frontend existed; task #80 retired it once the end-to-end
sweep covered it — the dump's 315 cases were a subset of these 348.

When the parser was rewritten into the Aeneas subset (§3.7, task #84) the
fixtures were not the only evidence: the new byte recogniser was run *beside*
the old one over 119 million real export lines (`Init`, `Init`+`Std`+`Lean`
and a 100 MB prefix of Mathlib), comparing the record, the continue position
and the error tag and offset of each, plus 31 million mutated lines — every
97th line with a byte corrupted, a byte digit-ised and the line truncated.
Zero disagreements.  A scanner is the one component where that kind of sweep
is cheap and worth more than the 348 streams, because most of its behaviour
is in the lines it *rejects*.

## 6. Results

### 6.1 The ledger

| | |
|---|---|
| con-leche core (`Kernel`, `Cached`) lines to port | 14 077, all ported, 92 % verified (the rest deliberately skipped, listed with reasons) |
| con-leche **parser** lines to port (`Frontend`, §3.7) | 4 441, all ported — into the verified crate since task #84 — 0 % verified, the lemmas being the next task's |
| con-leche modeller and driver lines to port | 2 975, all ported, unverified by design (§7) |
| Rust, verified core | 49 674 lines, 1 844 functions, every item cited (the checker's 927 declarations covered, 94 skipped) |
| Rust, unverified crate | about 11 100 lines |
| generated Lean model | 73 164 lines |
| proofs | 148 985 lines: 3 364 theorems by tactic, 800 by term; 1 380 `_refines` lemmas |
| refinement statements over the whole outcome | 283 of 283 |

The ratios are worth a sentence: the Rust is 2.7× the Lean it ports (a
`match` in Rust is longer than one in Lean, and every memo probe is
spelled out) — and the parser, rewritten into the subset by a different
route, came out at the same ratio, which is a small check that the subset
is not the reason for the factor.  The model is 1.5× the Rust.  The proofs
are 3.0× the Rust and 8.1× the upstream Lean, down from 3.9× and 10.6×
not because anything was proved less but because the denominator grew: the
parser is in the verified crate with no lemmas yet.

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
deviation: every mirrored error site came out as cited.  The one place a
verdict has moved since is upstream's, not the port's: con-leche's task #292
made an unresolved `sorryAx` a *decline* where it was a reject, and the port
mirrors the kind through two lemmas rather than at a fixed site (§3.5).

### 6.3 Performance

Measured with `perf stat -e instructions:u,cycles:u` (the measure of
record) and wall time and peak resident set as secondary numbers, on
`lean4export` exports of Lean's `Init`, of `Init`+`Std`+`Lean`, and of
Mathlib; con-leche at the vendored commit, both binaries in verified
mode, single-threaded and at eight workers.  Instructions are what the
two checkers do; the gap in wall and memory is memory traffic and atomic
reference counts.

<!-- re-measured at task #83, both binaries at the vendored commit c431b1ca, release builds with mimalloc, one run per cell; ulimit -v = 3 x con-leche's RSS + 1 GiB per worker.  The wall column was taken on a machine that was also building Lean, so it is worth less than usual; the instruction counts are not a function of load, which is why they are the measure of record.  The eight-worker Mathlib row is the only cell NOT re-measured (task #83 §5) and stands at master 9ea1ac33. -->
| export | jobs | con-leche instructions | con-ron instructions | con-leche wall | con-ron wall | con-leche peak RSS | con-ron peak RSS |
|---|---|---|---|---|---|---|---|
| `Init` (57 977 declarations) | 1 | 585.9 G | 540.4 G | 56 s | 65 s | 0.48 GB | 0.91 GB |
| `Init` | 8 | 587.2 G | 544.3 G | 12 s | 20 s | 0.67 GB | 1.18 GB |
| `Init`+`Std`+`Lean` (163 396) | 1 | 1 176.3 G | 1 157.6 G | 122 s | 161 s | 1.22 GB | 2.44 GB |
| `Init`+`Std`+`Lean` | 8 | 1 179.4 G | 1 166.6 G | 37 s | 73 s | 1.46 GB | 2.80 GB |
| Mathlib (691 128) | 1 | 12 792.4 G | 11 367.0 G | 1 220 s | 1 925 s | 8.75 GB | 16.49 GB |
| Mathlib | 8 | 12 843 G | 11 343 G | 337 s | 929 s | 9.1 GB | 17.8 GB |

Single-threaded, con-ron does 2–11 % fewer instructions than con-leche on
every export and takes 1.16–1.58× the wall time at 1.9–2.0× the memory:
the same work, more memory traffic.  At eight workers the gap in wall
time widens to 1.7–2.8×: con-leche's check phase scales better, its
reference counts being plain where con-ron's are atomic in every lane
(§3.2).

The declaration counts moved by five at the last con-leche bump, on both
binaries alike: a stream's quotient package is four `#QUOT` records plus
`Quot.sound`'s axiom record, and since con-leche's task #293 the parser emits
all five and the fold recognises them, where the parser used to fold them into
one basis record before the fold saw anything (§0).  Two earlier measurements in DESIGN.md
explain the shape: before the switch to atomic reference counts, Mathlib
ran at equal instructions, 1.6× the wall and 1.86× the memory; the switch
to `Arc` cost 13–17 % of wall time single-threaded and bought a check
phase that scales to 4.3× at eight workers and 6.9× at sixteen on `Init`.
The memory gap is the 56-byte node with its `Arc` header against Lean's
compact object, and the `Vec`-backed memo tables against `Std.HashMap`.

The single-worker column has been re-measured twice since, at the two changes
that could have moved it — con-leche's bump (task #83) and the parser's move
into the verified crate (task #84, §3.7) — and it has not: `Init` 540.9 G,
`Init`+`Std`+`Lean` 1 161.3 G, Mathlib 11 348.4 G, each within 0.4 % of the
cell above it, at 0.91, 2.43 and 16.64 GB.  That the *parser* rewrite cost
nothing is worth a sentence, because the budget expected it to cost something:
the hot loop of a parser is the scanner, and the scanner never used a closure
or a `std` map in the first place — what it does per byte is index a slice,
which the Aeneas subset spells the same way.  The two places that could have
paid did not: `ron::HashMap` replaced `std`'s only in the parse tables, probed
once per stream index and not per byte, and the preparation's record copies
(the subset has no `Vec::remove`, so a reordered record's *spine* is copied)
are one small allocation per record against a term DAG that is never copied.

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
* **The unverified crate.**  Since task #84 it is three things: the
  in-process **modeller** for mutual and nested inductive blocks, the
  **driver**, and the **worker pool**.  The parser is not among them any more
  (§3.7), and since **task #85** it is not merely extracted but *proved* to
  produce well-formed declarations (§3.5), so the chunk-level pair assumes
  nothing about the terms handed to `check_decls`.  The fold-level capstones
  still carry `hds` for a caller who does not go through that parser; a
  frontend that respects it, as this one does by construction, can lose an
  accept but not fake one, and a frontend that forged a node's cached word
  could.
  The modeller is the part that *stays* unverified by design, and it is now
  the whole of the residue: the parse takes it as a type parameter, and what
  the chunk-level pair assumes of it is one line — that the declarations it
  generates are well-formed.  It generates `_model` records for a block the
  direct install routes do not serve, and every one of them is checked by the
  fold as a stream declaration, so a wrong one is rejected or declined and
  never accepted; what it decides is which blocks the checker can accept at
  all, not whether an accepted one is sound.  Upstream may remove it, and the
  hypothesis goes with it.
  What the parser's proof does *not* yet cover is that it parses the dialect
  the way con-leche does — its refinement, not its well-formedness (§3.5).  A
  parser that mis-read a record would still produce well-formed declarations,
  and the fold would check those; what it could lose is an accept, not
  soundness.  Until that refinement lands, agreement with con-leche's parser
  rests on the fixtures and the 119-million-line differential (§5.4).
  One more fact about the driver is what the decoded pair leaves outside
  Lean: that it calls the decoder on the embedded text.
* **Nothing else.**  No `native_decide`, no `sorry`, no extra axiom in
  the headline pair or in the chunk-level pair.  One extra axiom is left in
  the whole port, on the embedded pair alone: the translator's
  string-constant artifact at `PINS_TEXT`, above.  The scanner's 68 went at
  task #86, when its key table became byte arrays.

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
not the list folds).  Its first real use, the soundness lemmas of the
runtime validation pass that was later withdrawn (§3.5), closed eight of
seventeen on the first try, the other nine being list folds; those lemmas
left with the pass, so the idiom's next use is the next new lemma.

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
* **con-leche's pin list as a parameter of the fold — upstream since
  con-leche's task #304.**  con-leche used to hard-wire its
  `Nat.div`/`Nat.mod` pin list at two install gates, so a refinement for the
  *decoded* list could only be stated through a `native_decide` identifying
  the two.  The port vendored con-leche's `pins-param` branch for one task
  (#74) and upstream then redid the change on master its own way, which is
  what `vendor/con-leche` carries now: `pins` is an explicit argument of
  `checkDecls` — second, right after the mode, with no default — and there is
  **one** pair of shipped statements, already over every pin list, so
  `model_exists_with` does not exist. The patch is retired; nothing in
  `vendor/con-leche` differs from upstream master.
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
| `crates/con-ron-core/src/kernel/` | the pure checker: `name`, `level`, `prop_when`, `expr`, `expr_ops`, `env`, `fenv`, `core_k`, `checker*`, `decl_check`, `type_checker`, the basis tables and the raw basis pins (`basis_raw`), `canon` (the pin match), the axiom tables, `inductives/*`, `pins_text`, `pins_decode` |
| `crates/con-ron-core/src/cached/` | the memoising checker: `state_c`, `expr_ops_c`, `core_c` (the knot), `checker_c`, `parsed_c`, `installed` (`check_decls`) |
| `crates/con-ron-core/src/frontend/` | the export parser (§3.7): `scan_types`, `scan_fast`, `export`, `export_c`, `proj_rec`, `nat_op_ground`, `prepare`, `prelude` with its generated `prelude_text`, and `in_model_rec` — the modeller's block records and the `Modeller` seam |
| `crates/con-ron-core/src/ron/` | `nat`, `hashmap`, `ptr` — what replaces the runtime |
| `crates/con-ron/src/` | the in-process modeller (`in_model`), the driver, the pool, the binary |
| `crates/con-ron-dump/` | the `con-ron-pins/1` reader and writer |
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
7. `scripts/gen-prelude.sh --check` — the embedded prelude text is con-leche's own committed `pins/<toolchain>.prelude.ndjson`;
8. `scripts/extract.sh --check` — the committed model is what Charon and Aeneas produce;
9. `lake build` of the model and the proofs.

It ends with the two summary lines of `progress.py` and `loc.py`.  The
differential tests of §5.4 are not in the gates, since they need the
exports; CI runs them where it can.

One check is neither a gate nor in CI, and is a landing rule instead:
anything that touches memory is run on the Mathlib export under
`ulimit -v 27000000` (three times con-leche's 8.6 GB) before it lands.
CI and the kernel arena skip Mathlib, so that run is the only place a
regression at scale shows; task #81 in DESIGN.md is what it caught.
