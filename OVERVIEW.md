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
([the usage text in `con-ron.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron.rs#L130-L254)):

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
reference counts are atomic by type.  The usage text closes with the one
*build-time* choice a run's numbers depend on — the global allocator, a
cargo feature of the binary rather than a flag (§3.6) — and `--help`
prints the one this binary was built with.

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
cd proof && lake build              # clones con-leche the first time, then the model and the proofs
```

`setup-aeneas-lean.sh` copies Aeneas' Lean backend out of the
`vendor/aeneas` submodule, applies `patches/aeneas-433.patch` (§9) and
fetches Mathlib from the olean cache; it is idempotent
([`setup-aeneas-lean.sh`](https://github.com/leanprover/con-ron/blob/master/scripts/setup-aeneas-lean.sh#L1-L14)).
con-leche is a plain `lake` dependency of `proof/` (§4), pinned by `rev` in
`proof/lakefile.toml`; `lake build` clones it the first time it is needed,
same as Mathlib, and every later `lake build` reuses the clone (`lake
update con-leche` is only needed to move the pin).  On a many-core machine
con-leche's first build can exhaust memory, and `LAKE_JOBS=N
scripts/gates.sh` caps the parallelism.

The one command a contributor runs before committing is
`scripts/gates.sh`
([the ten steps](https://github.com/leanprover/con-ron/blob/master/scripts/gates.sh#L54-L63)):
the Rust build and tests with warnings denied, the style lint (§3.6),
the provenance check (§4), the link gate, the hole gate (§7.1's inventory
of what the proof does not see must be the model's own list of holes), the
two embedded-text checks (the pin list and the built-in prelude), the
extraction check (the committed Lean model must be what Charon and Aeneas
produce from the crate today), and the Lean build.  §12 has the list.

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
[`conron.no_False_declaration`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L730-L746)
— con-leche's own main corollary transported:

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

— *a file whose bytes declare a theorem of type `False` in the shape
`jsonWithTheoremFalse` describes is never accepted by the Rust pipeline*, with
`conron.no_False_declaration_prelude` the same at the prelude the binary ships.
Both are pinned at the same three axioms.  The prelude is not identified with
con-leche's and does not have to be: `mem_preparePrelude` holds for every
prelude, so the statement is prelude-parametric for free.  What it still takes
about the parse is named rather than assumed wholesale, and it is a short list:
`hgen` and `hmr`, the two promises about the **unverified modeller** — the
residue task #84's seam left on purpose (§7) — and nothing else at all.  Four
further assumptions stood here during task #87 and every one of them is now a
theorem: the scanner's UTF-8 decoder and its string unescaper, the ground
hoist's target pass, and the inductive install path.
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
([`ExprNode` and `Expr` in `expr.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/expr.rs#L355-L366)):
the constructor data beside a packed 64-bit word that caches what
con-leche computes in its `@[computed_field]`s — the structural hash, the
loose bound-variable bound, the has-free-variable and has-level-parameter
bits.  Nodes of every kind are counted, shared and immutable, and the count is
atomic so that the installed environment can be shared by the check phase's
workers (§10).

**A node is as wide as its own constructor, and its kind is in the handle.**
An `Expr` is one machine word: the address of its heap block with the
constructor in the low four bits, which a block aligned to 16 leaves free
([`ron::tagged`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/tagged.rs#L1-L20)).
Each of the ten constructors then has a block of its own size — the count and
the packed word, then that constructor's fields and nothing else:

| block | bytes | live on `Init`+`Std`+`Lean` |
|---|---:|---:|
| `app` | **32** | 18 209 823 |
| `bvar` | 32 | 4 542 384 |
| `sort`, `const`, `fvar`, `lit` | 32 | 478 653 |
| `lam`, `forallE` | **48** | 4 821 064 |
| `letE`, `proj` | 48 | 82 672 |

Before this the node was 48 bytes whatever the constructor — as wide as the
widest arm, `lam`/`forallE` — and the block 64, so two thirds of the nodes
carried 32 bytes of slack.  Three things pay at once now: the kind word moves
into the handle, the weak count goes with `Arc` (the checker never makes a
`Weak`), and the slack goes with the uniform node.  **Peak resident set falls
41 % at Mathlib, 38 % on `Init`+`Std`+`Lean` and 40 % on `Init`** (§6.3), for
3–4 % more instructions and *less* wall time — which closes the memory gap
against con-leche, whose Mathlib peak this now matches.

What a binder carries beyond its type and body is one datum: `BinderMeta`, the
codomain prop-ness annotation the untrusted annotate pass writes and the
checker validates — a `PropWhen`, the set of parameter valuations under which
a level is zero
([`BinderMeta`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/expr.rs#L121-L123)).
It is 16 bytes and held **by value**, because `PropWhen` is one word beside its
tag: `Never`, `Always` and `One` carry no heap cell at all, and only the rare
`Two` and `Many` put their payload behind a handle
([`PropWhenRepr`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/prop_when.rs#L285-L291)).
That datum is why a binder's block is 48 where an application's is 32.

A constant's level list looks like the same opportunity and is not, which is
worth one paragraph because the arithmetic is so inviting.  `Expr.const` holds
its `List Level` behind a handle, so every constant reference costs a block
plus the vector's own array — two allocations even for a monomorphic constant
whose list is empty — and giving it `PropWhen`'s shape would remove both for
four fifths of them.  A census says not to bother: of the 24.2 M distinct
expression nodes alive when `Init`+`Std`+`Lean`'s environment is installed,
only **286 610 — 1.2 % — are constant references**, because the export format
already shares them harder than anything else (one record for every distinct
subterm, so one node for every occurrence of `Nat.succ` in the file).  The
whole prize is 12 MB of a 2.16 GB peak.  It was built and measured anyway:
`Init`+`Std`+`Lean` fell 0.9 %, `Init` *rose* 3.9 %, and the change is not in
the tree.  Only something that touches every node moves this number.


Size classes are the unit a node is priced in, and they are why the shape
above is the one that pays.  Measured on one machine with 20 M live blocks,
mimalloc charges 32 bytes for a 32-byte request, 48 for a 40- or 48-byte one
and 64 for anything from 49 to 64; glibc and jemalloc round the same way.  A
uniform 48-byte node therefore sat in a 64-byte block with no slack it could
give back — the next class down needs the *block* to reach 48, which no
repacking of one shared node type could do.  Per-constructor blocks reach 32
and 48 directly.  Entering mimalloc through `mi_malloc` rather than the
`mimalloc` crate's unconditional `mi_malloc_aligned` is what keeps them there
(and is 4.5 % fewer instructions besides), which is why the binary uses its own
[`MiMallocTight`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-dump/src/lib.rs#L138-L186).

**The `unsafe` this costs, and where it is.**  Putting a constructor in a
pointer is outside safe Rust, and it is the **only** `unsafe` in the checker:
nine lines in
[`ron::tagged`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/tagged.rs#L1-L20),
a file that names no term type.  Its soundness rests on one invariant — a
handle is only ever made by the allocator, which writes the block and attaches
its tag in the same expression and is the sole writer of the private address
field — and the projection is tag-checked, so asking for the wrong constructor
is a `None` rather than undefined behaviour.  The `Expr` side
([`ron::node`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L1-L14))
is a ten-line table and contains no `unsafe` at all; §7 has what this adds to
the trusted base and §3.6 the rule that confines it.

`Name`, `Level` and `PropWhen` keep the plain counted pointer
([`ron::ptr`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/ptr.rs#L1-L8)),
which is `std::sync::Arc`: their nodes are a fortieth of the bulk, so a uniform
block costs them nothing, and the atomic count is what lets the installed
environment be shared by the check phase's workers (§10).  Nodes of every kind
are built only by smart constructors such as
[`app`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/expr.rs#L479-L495),
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
The pinned con-leche commit fixes what those citations mean: no hash in
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

con-leche itself is a plain `lake` dependency of `proof/` (task #91: a
vendored `git subtree` for tasks #74–#90, a submodule before that), pinned
by `rev` in `proof/lakefile.toml` and resolved from
`proof/lake-manifest.json` — `provenance.py dir` prints its package
directory.  A bump is editing that `rev`, `lake update con-leche` in
`proof/` (which resolves the new commit into the manifest and checks it out,
but commits nothing), and `provenance.py update` with no `--old` needed —
it diffs the commit `HEAD`'s manifest still records against the one the
working tree's now names; DESIGN.md §7 has the whole procedure, written
from the one large bump the arrangement has been through (task #83, 101
upstream commits and 583 findings, done while con-leche was still the
vendored subtree — the mechanics of *moving* the pin changed at task #91,
the rest of the procedure did not).  Two things that
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

Those two are one type and five functions in all, and **§7.1 is the whole
list**, with each model and the argument for it; `scripts/holes.sh` prints
it from the templates Aeneas emits, and a gate checks the table against it.

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
([`ExprWF`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L515-L529)):
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
([`ErrSim`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L938-L946));
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

<!-- re-measured at task #83, both binaries at the vendored commit c431b1ca, release builds with mimalloc, one run per cell; ulimit -v = 3 x con-leche's RSS + 1 GiB per worker.  The wall column was taken on a machine that was also building Lean, so it is worth less than usual; the instruction counts are not a function of load, which is why they are the measure of record.  The eight-worker Mathlib row is the only cell NOT re-measured (task #83 §5) and stands at master 9ea1ac33.  The single-worker Mathlib con-ron cells were re-measured at task #90 (the binder datum back inline): instructions unchanged to five figures, peak RSS 11 % down, wall on a shared machine.  All three single-worker con-ron cells were re-measured again at task #92 (the tight mimalloc entry), this time in the DRIVER lane (`--jobs=1 --progress=1000000`; a plain `--jobs=1` bypasses the driver, task #89), which is what a real run takes: `Init` is the median of three (wall spread 62.7-72.4 s), the other two are one run each.  The con-leche column is unchanged from task #83. -->
| export | jobs | con-leche instructions | con-ron instructions | con-leche wall | con-ron wall | con-leche peak RSS | con-ron peak RSS |
|---|---|---|---|---|---|---|---|
| `Init` (57 977 declarations) | 1 | 585.9 G | 538.2 G | 56 s | 61 s | 0.48 GB | **0.48 GB** |
| `Init` | 8 | 587.2 G | 544.3 G | 12 s | 20 s | 0.67 GB | 1.18 GB |
| `Init`+`Std`+`Lean` (163 396) | 1 | 1 176.3 G | 1 155.3 G | 122 s | 147 s | 1.22 GB | **1.34 GB** |
| `Init`+`Std`+`Lean` | 8 | 1 179.4 G | 1 166.6 G | 37 s | 73 s | 1.46 GB | 2.80 GB |
| Mathlib (691 128) | 1 | 12 792.4 G | 11 484.4 G | 1 220 s | 1 979 s | 8.75 GB | **7.80 GB** |
| Mathlib | 8 | 12 843 G | 11 343 G | 337 s | 929 s | 9.1 GB | 17.8 GB |

Single-threaded, con-ron does 2–10 % fewer instructions than con-leche on
every export, takes 1.09–1.62× the wall time, and since task #94 **uses the
same memory or less** — level on `Init`, 1.10× on `Init`+`Std`+`Lean`, and
0.89× at Mathlib, where the gap used to be 1.64×.  At eight workers the gap in
wall time widens to 1.7–2.8×: con-leche's check phase scales better, its
reference counts being plain where con-ron's are atomic in every lane (§3.2).
(The eight-worker rows predate task #94 and their memory will have fallen the
same way; they have not been re-measured.)

The declaration counts moved by five at the last con-leche bump, on both
binaries alike: a stream's quotient package is four `#QUOT` records plus
`Quot.sound`'s axiom record, and since con-leche's task #293 the parser emits
all five and the fold recognises them, where the parser used to fold them into
one basis record before the fold saw anything (§0).  Two earlier measurements in DESIGN.md
explain the shape: before the switch to atomic reference counts, Mathlib
ran at equal instructions, 1.6× the wall and 1.86× the memory; the switch
to `Arc` cost 13–17 % of wall time single-threaded and bought a check
phase that scales to 4.3× at eight workers and 6.9× at sixteen on `Init`.
**The memory gap is closed, and the story of how is worth the paragraph.**  It
used to be the 48-byte node in its 64-byte `Arc` block against Lean's compact
object.  Task #92 measured what closing it would take and priced it: the
block had to drop a whole allocator size class, to 48 bytes, and the cheapest
route — a 40-byte node behind a one-word `triomphe::Arc` — took Mathlib from
14.31 GB to 11.37 GB, 21 % less, for **30 % more instructions**, three times
the budget DESIGN.md §3.2 sets for a memory trade.  That reasoning was right
about a *uniform* node and wrong about the problem: a node does not have to be
one size.  Task #94 put the constructor in the handle and gave each of the ten
its own block (§3.2), which takes Mathlib to **7.80 GB — 45 % less than before
and below con-leche's own 8.75 GB** — for **5 % more instructions**, with
cycles and wall down.  What is left of the gap at `Init`+`Std`+`Lean` is the
`Vec`-backed memo tables against `Std.HashMap`.  One
footnote master left, which the close makes moot but not wrong: measured per
symbol on `Init`+`Std`+`Lean`, `triomphe::Arc` on its own costs **nothing at
all** (−0.09 %, three paired runs) where two earlier measurements recorded
+17 %, and the per-symbol diff shows one inlining change and no extra atomic.
Mathlib was never re-run for it, so that 30 % is unexplained rather than
refuted — and it no longer has to be, since the block it was buying is the one
task #94 made unnecessary.

The single-worker column has been re-measured four times since, at the
changes that could have moved it.  Twice it did not: con-leche's bump
(task #83) and the parser's move into the verified crate (task #84, §3.7)
gave `Init` 540.9 G, `Init`+`Std`+`Lean` 1 161.3 G, Mathlib 11 348.4 G, each
within 0.4 % of the cell above it, at 0.91, 2.43 and 16.64 GB.  The third
time only the *memory* moved: task #90 put the binder datum back inline
(§3.2) and Mathlib fell from 16.64 GB to 14.66 GB, 11 % less, at
11 368.3 G instructions — the same count to five figures, which is what says
the saving is allocator traffic and not work.  The fourth time only the
*work* moved: task #92's tight mimalloc entry (§3.2) took Mathlib to
**10 922.6 G**, 3.9 % fewer instructions, with memory where it was.  The fifth
is the row above: task #94's tagged handle moved both, and in opposite
directions — Mathlib's peak 14.31 → **7.80 GB** for **+5.1 %** instructions —
which is the trade §3.2 records and the only one in this list that was a
maintainer's decision rather than a free win.  That the *parser* rewrite cost
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
binary.  §7.1 is the part a script can keep honest — the *holes*, the items
Aeneas could not translate and that someone answered by hand — and
`scripts/holes.sh --check` (gate 6) fails if that table and the model have
drifted apart.  §7.2 is everything else that is trusted, and §7.3 is the
argument behind both.

### 7.1 What the proof does not see

The theorem is about the verified crate *as Aeneas translates it*.  Where the
translator meets an item it cannot translate — another crate's type or
function, or an item of this crate deliberately marked opaque — it emits a
**template** declaring that item as a bare `axiom` and asks for a model; the
answers live in two hand-written, committed files,
[`TypesExternal.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/TypesExternal.lean#L42)
and
[`FunsExternal.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L26-L45).
Every one of them is a claim about the Rust that no proof checks, so here they
all are, with their models and what makes each faithful.  There are
**twenty-two**: two types and twenty functions.  Five are the counted
pointer's, one is `str::as_bytes`, and the other sixteen are the tagged `Expr`
handle of §3.2 — its type, its projection and cached word, its share and its
identity test, its ten constructors and its `Drop`.  Every one of the sixteen
is `rfl` against the `Expr` inductive `Generated/Types.lean` already had, which
is the sense in which putting the constructor in the handle moved no model.
`scripts/extract.sh` (gate 9) fails if the crate grows a hole nobody modelled;
`scripts/holes.sh --check` (gate 6) fails if it grows one nobody wrote a row
for.

<!-- holes: begin — scripts/holes.sh --check keeps this table and the templates in step; the first cell is the Lean name of the hole, in backticks -->

| hole | the Rust it stands for | the model | why the model is faithful |
|---|---|---|---|
| [`alloc.sync.Arc`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/TypesExternal.lean#L41-L42) | `alloc::sync::Arc<T>`, which the core names exactly once, as [`ron::ptr::P<T>`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/ptr.rs#L30-L36) | `alloc.sync.Arc T := T` — a handle *is* its contents | An allocated `P<T>` is an immutable owner: `get_mut`, `make_mut`, `Weak`, `as_ptr`, `into_raw`, the counts and every form of interior mutability are outside the subset, and `scripts/lint-rust-style.sh` gates those names for `P`, `Rc` and `Arc` alike.  So sharing is invisible to the value.  Atomicity is invisible too — an atomic count and a plain one erase to the same thing, which is why `P = std::sync::Arc` (task #45) needed no model change. |
| [`alloc.sync.Arc.new`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L25-L26) | `Arc::new`, through the wrapper `ron::ptr::new` | `ok x` — the identity | Allocation is the only thing it does, and the model has no heap for it to be visible in. |
| [`alloc.sync.Arc.Insts.CoreCloneClone.clone`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L44-L48) | `Arc::clone`, through `ron::ptr::clone` | `ok x` — the identity | A clone bumps a count and hands back the same immutable value; by the row above, the count is not part of the value. |
| [`alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L54-L57) | `Deref::deref` — `*p`, `p.field` and `match &*p`, some 400 generated call sites, deliberately not wrapped | `ok x` — the identity | Reading through an immutable owner yields the value it owns. |
| [`alloc.sync.Arc.ptr_eq`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L36-L38) | `Arc::ptr_eq`, through `ron::ptr::ptr_eq` | `ok false` — the model always takes the slow path | The one hole that is an *under-approximation* rather than an erasure, and the proof has to be sound against it: wherever the Rust takes a pointer-equal shortcut, a lemma shows the shortcut's answer is what the full computation gives.  The memo tables' pointer-verified buckets and `expr::beq`'s pointer fast path each carry theirs.  `true` would have been the unsound choice; `false` costs only that the model does more work than the binary. |
| [`core.str.Str.as_bytes`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L71-L72) | `str::as_bytes`, at its single call site: `PINS_TEXT.as_bytes()` in `kernel::pins_decode::decode_embedded` | `ok s` — the identity | **Not a trust assumption at all.**  Aeneas models `Str` as `Slice U8` (`Aeneas/Std/StringDef.lean`), so the bytes of a `&str` already *are* the value and `as_bytes` is the identity on it.  The hole exists because Rust offers no other way to index a `&str`, and the alternative — a `b"…"` constant — extracts to a 532 456-element array literal Lean cannot elaborate (task #43). |

| [`ron.tagged.Raw`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/TypesExternal.lean#L74-L78) | [`ron::tagged::Raw<T>`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/tagged.rs#L178-L192), the tagged counted handle an `Expr` is (§3.2) — a `NonNull<u8>` with the constructor in its low four bits, and a `PhantomData<T>` carrying the modelled contents | `ron.tagged.Raw T := T` — a handle *is* its contents | The `Arc` row's argument, for a handle the project wrote itself: a block is immutable for its whole life but for its atomic count, nothing outside `ron::tagged` can build or alter a handle (the address field is private), and the `T` is phantom, so there is no value of it to be wrong about.  What the model additionally cannot see — *which* of the ten blocks the bytes are in — is tied to the constructor by the rows below and by §7.2's `unsafe` row. |
| [`ron.node.view`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L114-L119) | [`ron::node::view`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L219-L245), the projection every reader in the core goes through | `view (Expr.mk (ExprNode.mk d k)) = ok (ExprView.ofKind k)` — the node's constructor, read back | The tag was written beside the block by one of the `alloc_*` below, in the same expression, and nothing else can write one; `ExprView.ofKind` is the arm-for-arm bijection between the view and `ExprKind`, so this says only that reading a node back gives the constructor it was made from.  `Raw::get` checks the tag before it casts, so a wrong tag would be a `None` and not undefined behaviour. |
| [`ron.node.data`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L122-L127) | [`ron::node::data`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L299-L302), con-leche's `@[computed_field]` read back | `ok e._0.data` — the stored word | Every block begins with the same `#[repr(C)]` header whatever its tag, so this read needs no dispatch and no tag check; the word is written once, by the smart constructor, and never again. |
| [`ron.node.dup`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L130-L133) | [`ron::node::dup`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L305-L308), a `Relaxed` count bump | `ok e` — the identity | `Arc::clone`'s row, verbatim: a share bumps a count and hands back the same immutable value, and the count is not part of the value. |
| [`ron.node.ptr_eq`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L136-L142) | [`ron::node::ptr_eq`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L311-L315), the identity test behind `expr::beq`'s fast path | `ok false` — the model always takes the slow path | `Arc::ptr_eq`'s row, verbatim, and the same reflexivity lemmas discharge it.  Comparing the *tagged* words is the same test as comparing the addresses, since a block's tag is a function of the block. |
| [`ron.node.alloc_bvar`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L145-L149) | [`ron::node::alloc_bvar`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L249-L252), `Expr.bvar`'s block | `ok (Expr.mk (ExprNode.mk d (.Bvar i)))` — the constructor | Each `alloc_*` is one line over `Raw::alloc`, which writes the block and attaches *that kind's* `TAG` in the same expression and is the only thing that ever makes a handle.  So a handle's tag is always the tag of the `Kind` whose block the address holds, which is exactly what `view`'s row needs.  The ten tags are checked in range and pairwise distinct by a `const` assertion (`tagged_kinds!`). |
| [`ron.node.alloc_fvar`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L152-L157) | [`ron::node::alloc_fvar`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L255-L258), `Expr.fvar`'s block | `ok (… (.Fvar idx ty))` | As `alloc_bvar`. |
| [`ron.node.alloc_sort`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L160-L164) | [`ron::node::alloc_sort`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L261-L264), `Expr.sort`'s block | `ok (… (.Sort u))` | As `alloc_bvar`. |
| [`ron.node.alloc_const`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L167-L173) | [`ron::node::alloc_const`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L267-L270), `Expr.const`'s block | `ok (… (.Const n us))` | As `alloc_bvar`; the level list arrives already behind its own `P` handle, which the `Arc` rows cover. |
| [`ron.node.alloc_app`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L176-L181) | [`ron::node::alloc_app`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L273-L276), `Expr.app`'s block — 65 % of the nodes of a real term | `ok (… (.App f a))` | As `alloc_bvar`. |
| [`ron.node.alloc_lam`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L184-L190) | [`ron::node::alloc_lam`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L279-L282), `Expr.lam`'s block | `ok (… (.Lam ty b m))` | As `alloc_bvar`. |
| [`ron.node.alloc_forall_e`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L193-L199) | [`ron::node::alloc_forall_e`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L285-L288), `Expr.forallE`'s block | `ok (… (.ForallE ty b m))` | As `alloc_bvar`.  `lam` and `forallE` have the same fields but are two `Kind`s with two tags, so the cast is keyed on the constructor and not on a shared struct. |
| [`ron.node.alloc_let_e`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L202-L206) | [`ron::node::alloc_let_e`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L291-L294), `Expr.letE`'s block | `ok (… (.LetE ty v b))` | As `alloc_bvar`. |
| [`ron.node.alloc_lit`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L209-L213) | [`ron::node::alloc_lit`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L297-L300), `Expr.lit`'s block | `ok (… (.Lit l))` | As `alloc_bvar`. |
| [`ron.node.alloc_proj`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L216-L221) | [`ron::node::alloc_proj`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L303-L306), `Expr.proj`'s block | `ok (… (.Proj n i e))` | As `alloc_bvar`. |
| [`kernel.expr.Expr.Insts.CoreOpsDropDrop.drop`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L222-L225) | [`Drop for Expr`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L317-L326), which gives up one share and frees the block when it was the last | `ok e` — the identity | **Aeneas never calls it.**  `Generated/Funs.lean` mentions it only in the instance record; the model has no deallocation, exactly as it has no allocation, and the identity is there so that the instance is well typed and for no other reason.  `Raw` deliberately has no `Drop` of its own — only a scheme's table knows which type a tag names — so this is the one place the recursion is written down. |
<!-- holes: end -->

### 7.2 The rest of the trust surface

Everything else that has to hold, and what stands in for it:

| trusted | what it is | what stands in for it |
|---|---|---|
| **con-leche's own assumptions** | The theorem is con-leche's, at the Rust run | A set theory `V` with `ConLeche.SetTheory V`, Lean's kernel checking the proof, and the three standard axioms `propext`, `Classical.choice`, `Quot.sound`.  con-leche's OVERVIEW says what those are |
| **Aeneas and Charon** | The Lean model *is* what the translator says the Rust means | Nothing: a translator bug is a hole.  The port stays inside the documented subset (§3.6, `scripts/lint-rust-style.sh`) and reports what it found — `AENEAS_FINDINGS.md`, fifteen findings, all worked around in the Rust |
| **Nine lines of `unsafe`** | [`ron::tagged`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/tagged.rs#L1-L20), the tagged counted handle (§3.2): an `unsafe trait Kind`, two `unsafe impl Send`/`Sync`, four expressions and one macro.  It replaces `std::sync::Arc` as the trusted pointer implementation **for `Expr` nodes only** — `Name`, `Level`, `PropWhen` and `ConstantInfo` are still `P<T>` and still behind §7.1's four `Arc` rows | One invariant, argued in that module's note and checkable by reading ten adjacent one-line functions: **a handle is only ever made by the allocator**, which writes the block and attaches that kind's tag in the same expression and is the sole writer of the private address field.  Everything else follows — the projection is tag-checked and returns an `Option`, the header cast is sound at any tag by `#[repr(C)]`, and the count is `Arc`'s protocol verbatim.  The Expr side ([`ron::node`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/node.rs#L1-L14)) is a ten-line table with no `unsafe` in it, and `scripts/lint-rust-style.sh` (gate 3) enforces that boundary by path |
| **`rustc` and the Rust standard library** | What compiles and runs the binary | Nothing.  This is the trade the project makes: Lean's compiler, runtime and GMP for these |
| **The allocator** | [`MiMallocTight`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-dump/src/lib.rs#L174-L176), an inlined `GlobalAlloc` over `libmimalloc-sys`, chosen at build time (`--no-default-features` gives glibc `malloc`, `--features jemalloc` gives jemalloc) | Nothing, and nothing is needed: an allocator cannot change a verdict, only the memory and the time it takes to reach it.  It is in the *unverified* crate and Charon never sees it |
| **`overflow-checks = true`** | The [release profile](https://github.com/leanprover/con-ron/blob/master/Cargo.toml#L17-L21) of the workspace | The model is the *checked*-arithmetic one: an overflow is a `fail` in the `Result` monad, which is a panic in the binary.  A build without it would wrap where the model fails, and the model would no longer describe it (task #7) |
| **The modeller** | The in-process construction of `_model` records for mutual and nested inductive blocks, [`crates/con-ron/src/in_model/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/in_model/mod.rs#L12-L16) — unverified by design, and the whole of the residue | Two hypotheses of the chunk-level pair, [`ModellerWF` and `ModellerRefines`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L697-L703): that the declarations it generates are well formed, and that it declines where con-leche's declines.  Every record it makes is checked by the fold as a stream declaration, so a wrong one is rejected or declined and never accepted — what it decides is *coverage*, not soundness |
| **The driver** | `Main.lean`'s four steps above `check_decls`, [`crates/con-ron/src/driver.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L21-L27) — the exit-code mapping, the two phase loops, the verdict lines | The chunk-level pair is the statement about the four steps; what stays outside Lean is that the driver *calls* them on the bytes it read, and that it calls the decoder on the embedded pin text |
| **The worker pool** | Phase B on `n` threads, [`crates/con-ron/src/pool.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L15-L21) | An argument, not a proof: the workers' results are merged by record index and walked in record order, so the verdict and the record a rejection names are the sequential walk's at every `--jobs`.  `pool_reports_the_first_failure_at_every_jobs` tests it at 1, 2, 3, 4 and 8 workers |
| **One extra axiom, on the embedded pair alone** | `pins_text.PINS_TEXT._native.decide.ax_1` — Aeneas's `toStr` spends a `decide +native` on the size bound of every extracted `&str` constant (`AENEAS_FINDINGS.md` §3.8) | Nothing; it needs an upstream change.  It is the translator's artifact, not the port's, it lives in the constant's definition rather than in any computation, and `PINS_TEXT` is the port's last `&str` constant — the scanner's 68 went at task #86 |

Nothing else: no `native_decide`, no `sorry`, no axiom beyond the three in the
headline pair or in the chunk-level pair.

### 7.3 The argument

The same ground in prose, which is where the reasoning lives and which the
tables above point back at:

* **con-leche's own assumptions.**  The theorem is con-leche's, at the
  Rust run: it rests on a set theory `V` with `ConLeche.SetTheory V`, on
  Lean's kernel checking the proof, and on the three standard axioms.
  con-leche's OVERVIEW says what those are.
* **Aeneas and Charon.**  The Lean model is what the translator says the
  Rust means.  A translator bug is a hole; the port stays inside the
  documented subset and reports what it found (AENEAS_FINDINGS.md).  The
  hand-written models (§5.1) are an argument, not a proof: a counted handle as
  its contents holds because the lint forbids mutation through it, `ptr_eq` as
  `false` is sound because every pointer shortcut has its equivalence lemma,
  and a term's ten constructors and its projection are `rfl` against the
  inductive the proof tier already had — what they assume is the tagged
  handle's own invariant, which is the next bullet.
* **`rustc`, the Rust standard library, and `mimalloc`**, the allocator
  the binaries use.  These are what the project trades Lean's compiler,
  runtime and GMP for.
* **Nine lines of `unsafe`, in one file.**  A term's constructor lives in the
  low four bits of its handle (§3.2), which is outside safe Rust, and
  [`ron::tagged`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/tagged.rs#L1-L20)
  is the only place in the checker that says so — the `Expr` side is a
  ten-line table with no `unsafe` in it, and the style gate enforces that
  boundary by path.  What has to be right is one invariant, which the module's
  note argues and which a reader can check by reading ten adjacent one-line
  functions: **a handle is only ever made by the allocator**, which writes the
  block and attaches that kind's tag in the same expression and is the sole
  writer of the private address field.  Everything else follows — the
  projection is tag-checked and returns an `Option`, so asking for the wrong
  constructor is a `None` and not undefined behaviour; the header cast needs no
  check at all, since every block begins with it under `#[repr(C)]`; and the
  reference count is `std::sync::Arc`'s protocol verbatim.  The Lean model
  cannot see any of this: it sees `Raw T := T`, the same line it sees for
  `Arc`, so **the fifteen operations this adds are trusted in exactly the way
  `Arc`'s four already were** (§5.1) — what is new is that their
  implementation is the project's own rather than the standard library's.

  **The trust accounting, stated plainly.**  For `Expr` nodes — and only for
  them — this *replaces* `std::sync::Arc` as the trusted pointer
  implementation: what used to be four holes over the standard library's
  allocation, deref, clone and pointer comparison is now fifteen over
  `ron::tagged`'s, namely the ten per-constructor allocators, the projection
  `view`, the cached word `data`, the count bump `dup`, `ptr_eq`, and `Expr`'s
  `Drop` (which Aeneas never calls).  Each is one line and `rfl` against the
  `Expr` inductive the proof tier already had, which is the sense in which the
  change moved no model.  **`Name`, `Level`, `PropWhen` and `ConstantInfo` are
  untouched**: their nodes are still `std::sync::Arc`
  ([`ron::ptr`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/ptr.rs#L1-L8)),
  still behind the same four holes, and no `unsafe` of ours is anywhere near
  them.  What the trade bought is §6.3's row: Mathlib's peak resident set from
  14.31 GB to 7.80 GB.
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
  ([the options](https://github.com/leanprover/con-ron/blob/master/proof/lakefile.toml#L24-L26)).
  AENEAS_FINDINGS.md §3.1 has the details; the ask upstream is a v4.33
  release.
* **con-leche's pin list as a parameter of the fold — upstream since
  con-leche's task #304.**  con-leche used to hard-wire its
  `Nat.div`/`Nat.mod` pin list at two install gates, so a refinement for the
  *decoded* list could only be stated through a `native_decide` identifying
  the two.  The port vendored con-leche's `pins-param` branch for one task
  (#74) and upstream then redid the change on master its own way, which is
  what the pinned commit carries now: `pins` is an explicit argument of
  `checkDecls` — second, right after the mode, with no default — and there is
  **one** pair of shipped statements, already over every pin list, so
  `model_exists_with` does not exist. The patch is retired; nothing in
  con-leche differs from upstream master.
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
| (no `vendor/con-leche/`) | con-leche, a plain `lake` dependency of `proof/`, pinned by `rev` in `proof/lakefile.toml` — `provenance.py dir` prints where `lake` put it |
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
6. `scripts/holes.sh --check` — §7.1's table of holes is exactly the set of holes the Aeneas templates declare: a hole with no row, or a row for something that is no longer a hole, fails and names it;
7. `scripts/gen-pins.sh --check` — the embedded pin text is what con-leche's list generates;
8. `scripts/gen-prelude.sh --check` — the embedded prelude text is con-leche's own committed `pins/<toolchain>.prelude.ndjson`;
9. `scripts/extract.sh --check` — the committed model is what Charon and Aeneas produce, **and every hole it declares is modelled by hand**.  That second half is checked two ways since task #94, because one of them turned out to be blind: Aeneas writes the `@[rust_type]`/`@[rust_fun]` attribute the older rule reads only for externals it maps by *name pattern*, i.e. another crate's, so a hole that is an opaque module of this crate arrived in the template as a bare `axiom` and the rule passed vacuously.  The gate now also requires every `axiom` a template declares to be defined in the corresponding hand-written file, which is the same set step 6 tabulates;
10. `lake build` of the model and the proofs.

It ends with the two summary lines of `progress.py` and `loc.py`.  The
differential tests of §5.4 are not in the gates, since they need the
exports; CI runs them where it can.

One check is neither a gate nor in CI, and is a landing rule instead:
anything that touches memory is run on the Mathlib export under
`ulimit -v 27000000` (three times con-leche's 8.6 GB) before it lands.
CI and the kernel arena skip Mathlib, so that run is the only place a
regression at scale shows; task #81 in DESIGN.md is what it caught.
