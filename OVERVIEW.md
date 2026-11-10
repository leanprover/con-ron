# con-ron: an overview

> **This document was written by an AI agent** (Claude, working with the
> maintainer); `README.md` is the human-written entry point.  It describes
> the checker and its proof as they are.  For the history behind any
> decision, the measurements, and the task log, see
> [`DESIGN.md`](./DESIGN.md).

con-ron is a Lean kernel checker written in Rust.  It is a close port of
[con-leche](https://github.com/leanprover/con-leche), the external Lean
checker whose consistency is proved in Lean, and it is proved, through
[Aeneas](https://github.com/AeneasVerif/aeneas), to accept only what
con-leche accepts.  A file that con-ron accepts therefore has con-leche's
guarantee: its environment has a model, and it proves no theorem of type
`False`.

The point is diversity.  con-leche's proof covers con-leche's Lean source,
not the Lean compiler, runtime and bignum library that execute it.  con-ron
executes the same algorithm on `rustc`, Rust's standard library and its own
bignum code.  A bug in either runtime would need a matching bug in the
other for both checkers to accept the same wrong proof.

The document is for readers who know Lean and Rust and roughly what a kernel
checker does.  Three names recur throughout:

* **(A) con-leche**, specifically its *pure* checker `checkDeclsPure`, over
  ordinary expression trees.  Its soundness theorems are the ones con-ron
  inherits.
* **(B) the twin**: a second checker, written in Lean in this repository
  ([`proof/ConRon/Arena/`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Arena)),
  that follows con-leche's algorithm but works on con-ron's data
  representation.  It mirrors the Rust function for function.
* **(C) the Rust checker**
  ([`crates/con-ron-core/`](https://github.com/leanprover/con-ron/tree/master/crates/con-ron-core)),
  and the Lean model Aeneas extracts from it.

The proof has two halves: (B) refines (A) (**Theorem 1**), and (C) refines
(B) (**Theorem 2**).

## 1. What con-ron is

con-ron reads a Lean environment exported by `lean4export` in its NDJSON
format and checks every declaration in it.  It prints one verdict line and
exits with one of four codes (§2.2).

It is a *port*: every Rust item cites the con-leche declaration it ports,
or says why it has none (§10), and it checks what con-leche checks, the way
con-leche checks it.  What differs is the data representation and the
caching (§4, §5).  con-leche walks
expression trees; con-ron stores every expression once, in per-constructor
arrays, and refers to it by a 32-bit handle.

Before the file's own declarations, every run checks a small built-in
prelude: the basis blocks con-leche pins (`Eq`, `Nat`, `Empty`, `False`,
`Quot`) and the toolchain's `Bool` and `And`.  The prelude text is
con-leche's own, embedded at build time
([`prelude_text.rs`](https://github.com/leanprover/con-ron/tree/master/crates/con-ron-core/src/frontend/prelude_text.rs)).

Every inductive block, mutual and nested ones included, goes through one
verified check, con-leche's *uniform route*: a positivity check that
looks through containers at their concrete instances, and recursors that are
generated in official's shape and compared with the stream's by definitional
equality (§6.3).

## 2. Running it

### 2.1 Command line

```
con-ron [OPTIONS] [--] FILE.ndjson
con-ron [OPTIONS] --olean --search-path=DIRS [--] MODULE...
```

([the help text](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron.rs#L85-L133)).
Run with no arguments, `con-ron` prints these two forms; a usage error prints its
message and a pointer to `--help`, and exits 3.

* **`--verified`** is the default, and the only mode the theorems cover.
* **`--trusted`** runs the same checker with con-leche's certification-only
  checks switched off.  It is faster, and an accept in this mode is outside
  the theorems.
* **`--jobs=<n>`** sets the number of worker threads for the check phase
  (§6.4).  The default is one per hardware thread, at most 16.  Each worker
  reserves 1 GiB of stack address space, which counts against `ulimit -v`.
  The verdict, and the declaration a rejection names, are the same at every
  `n`.
* **`--progress[=PACE]`** prints a heartbeat on stderr.  `PACE` is `N` (a line
  every `N` declarations checked, or `.olean` modules loaded; bare `--progress`
  is every one), `P%` (a line per `P` percent of a phase), or `Ss` (at the first
  item done once `S` seconds have passed).  Every phase says when it starts
  (`reading`, the `read:` lines of an `--olean` read with the time and the
  resident set, `parse done`, `checking`), and a check line names its
  declaration only when every check gets one.
* **`--pins FILE`** and **`--no-pins`** replace the embedded `Nat.div`/`Nat.mod`
  pin list (§6.1).  They exist for testing and are outside the theorems.
* **`--`** ends the options: every argument after it is a file, whatever it is
  called, and only a `--help` before it is help.  The input is a regular file,
  read forward; a FIFO or a directory is exit 3.
* **`--olean`** reads the input from `.olean` files instead of a lean4export
  stream (§6.2): the arguments are root modules, checked with every constant of
  their import closure.  The theorems cover this path (§3.2), on one premise
  about the files: the file operations answer as one unchanging snapshot of the
  file system.
* **`--search-path=DIR[:DIR...]`** names the directories holding `.olean` trees,
  as `LEAN_PATH` lists them.  Every module is looked up in every directory, and a
  module in two places, or a missing, stray or split part, is exit 3.
* **`--constant=NAME`** restricts `--olean` to this constant and what it mentions,
  as lean4export's arguments after `--` do.  It may be given more than once.
  Without it every constant of the closure is checked, whatever its name; unsafe
  and partial constants stay out, as lean4export leaves them out.  A run with
  `--constant` is outside the theorems.

### 2.2 Exit codes

The codes are con-leche's
([the table](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L18-L23)):

| exit | verdict line | meaning |
|---|---|---|
| 0 | `accepted N declarations` | every declaration checked; `N` counts the file's own declaration records |
| 1 | `rejected` | a declaration is invalid |
| 2 | `declined` | the input uses something the checker does not support, and says what |
| 3 | error | bad usage, malformed input, or an internal failure |

Running out of memory is none of these: the process aborts, as Rust does on
a failed allocation.

Every name and raw string a message prints comes from the input, so it is
printed through one rendering, con-leche's
([`render` in `kernel/name.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/name.rs#L618-L630)).
An identifier-shaped name component prints bare (`Nat.add_comm`, `α₁.ℕ`);
any other is wrapped in `«…»` (`x.«3»`, `«a.b»`), with `\` doubled and with
`»` and every control, format and separator character other than the ASCII
space written as `\u{XXXX}`.  A raw string field (a `safety` value, a
quotient kind, an unknown command-line option) prints the same way between
`"`…`"`, and a rendering longer than 512 characters ends in
`…[N more characters]`.  No input can move the cursor, recolour the terminal
or start a line of the output, such as a GitHub Actions `::error::` command.

### 2.3 Building

`flake.nix` pins Aeneas, which pins the Charon it needs, which pins the Rust
nightly it needs
([`flake.nix`](https://github.com/leanprover/con-ron/blob/master/flake.nix#L5-L29)).
Lean comes from `elan`, at con-leche's version (`proof/lean-toolchain`).

```
nix develop                        # cargo, charon, aeneas on PATH (or: direnv allow)
cargo build --release              # target/release/con-ron
scripts/setup-aeneas-lean.sh       # the patched Aeneas Lean library + Mathlib, once
cd proof && lake build             # fetches con-leche, builds the model, both theorems and the capstone
```

The theorems live in three library targets, `ConRonBridge`, `ConRonRefine2`
and `ConRonCapstone` (§11); all three are default targets, so the plain
`lake build` above checks them.

The global allocator is a build-time choice: mimalloc by default,
`--no-default-features` for the system `malloc`, and `--no-default-features
--features jemalloc` for jemalloc.  `con-ron --help` names the one a binary
was built with.

## 3. What is proved

The two headline theorems are in
[`proof/ConRon/Capstone.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L14-L85).
They are stated about the Aeneas model of the Rust functions the binary's
`check_main` calls, one premise per call, in the order it calls them, from
the binary's own start values.  Both depend on con-leche's three axioms
(`propext`, `Classical.choice`, `Quot.sound`) and on nothing else: no
`sorry`, no `native_decide`.  A `#guard_msgs` check keeps it that way
([the census](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L895-L911)).

**Soundness**
([`ConRon.Capstone.no_False_declaration`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L597-L622)),
with the implicit arguments left out:

```lean
theorem ConRon.Capstone.no_False_declaration (V : Type w) [ConLeche.SetTheory V]
    (hfalse : ConLeche.jsonWithTheoremFalse (absChunks chunks))
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    (hreads : ReadsAs sinst src chunks.val)
    (h3 : frontend.export_c.parse_source sinst emptyTier st2 src = ok (.Ok r, st3, src'))
    (h4 : frontend.prepare.prepare_d DeclUsedConsts.Insts… emptyTier st3 pre r.decls ()
      = ok (.Ok prepared, st4))
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
    (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
    (h8 : ParallelAll prepared.decls.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified ipins prepared.decls)) :
    False
```

In words: if the file's bytes (`chunks`) declare a theorem whose type is
`False`, then the binary's calls cannot all succeed.  Each premise says that
one extracted Rust function, run on the state the previous one left,
returned `Ok`; the first starts from `startState`, the value of the binary's
`AState::empty()`, and every step is handed `emptyTier`, the value of its
`PersTier::empty()`.  The theorem's docstring maps each premise to its line
of `check_main`.

**The model statement**
([`ConRon.Capstone.model_exists`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L550-L574))
takes the same premises without `hfalse` and concludes

```lean
    ∃ env, RustDenotes prepared.decls st6 env ∧ Nonempty (ConLeche.Model V env)
```

where
[`RustDenotes`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L441-L445)
says that the records the Rust checked (`prepared.decls`), read in a twin state
related to the Rust's final state, denote a con-leche stream `dsP`, and that
`env` is that stream's environment (`streamEnv dsP`: every record's constants
and tables, in order); `env` has a model (con-leche's `Model V env`) in every
set theory `V`.  The statement goes through the twin because the Rust store
is related to the twin's by a relation, not mapped by a function (§7.4).

Both theorems are **partial correctness**.  The Rust has one error kind
con-leche does not, `Native` (§6.5), raised at resource limits such as a
full handle table.  Theorem 2 relates a Rust `Native` to the twin's own
`native` error at the same point, but the twin's `native` claims nothing
about con-leche, so the headline theorems say nothing about a run that ends
in `Native`.  So con-ron may decline where con-leche accepts, but it never
accepts where con-leche rejects.

### 3.1 What the theorems assume

Every assumption is a premise of the two statements, not an axiom, which
is why `#print axioms` does not list any of them.

| premise | what it says | how it is discharged |
|---|---|---|
| `[ConLeche.SetTheory V]` and con-leche's soundness | a set theory to build the model in; con-leche's `checkDeclsPure_sound_of` and `no_proof_of_False_pure` at the pinned revision.  Only these last steps read it: Theorem 1 (`Arena.pooledAccepts_bridge`) is free of it | con-leche's own proof, on the same three axioms |
| `h1`…`h5`, `hpins` | the binary ran exactly these extracted functions, in this order, on one state that starts at `AState::empty()` under one `PersTier::empty()` | the driver's calling order, which starts [here](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron.rs#L334-L352); each call carries a `// ConRon.Capstone: hᵢ` comment: trusted |
| `h6`, `h7`, `h8` (the index, the freeze, the check phase) | the stream's index was built from the records (`build_index`, from `stream_index_empty()`) as `ix`; `freeze_tier` moved the persistent tables and `ix` into the tier; and the check phase's `parallel_all` accepted: `ParallelAll` says there are lists of record positions, one per worker, that together cover every record, each in increasing order, and for each list the worker's run (one `worker_state`, then `jobStep`, the verified `run_job` on each position, folded over the list) answered `Ok` at every step.  Nothing is assumed about a job being claimed only once | `h6` and `h7` are calls like `h1`…`h5`, inside `driver::check_decls_driver`.  `h8` is the contract of the one generic combinator `pool::parallel_all`, an argument about its control flow (§8.2).  The driver's observer only prints, so `--progress` runs are covered |
| `hreads : ReadsAs sinst src chunks` ([def](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Frontend/Source.lean#L34-L38)) | the chunk source hands out `chunks`, each nonempty, then an empty buffer | that the file handle returns the file's bytes in order: trusted.  The read loop itself (`parse_source`) is verified |
| `hpins : decode pinText = ok (.Ok pins)` | the pin list is what the verified decoder read from some text | the theorems hold at every text, as con-leche's hold at every pin list; the binary decodes the embedded `PINS_TEXT` (`decode_embedded`).  `model_exists_embedded`/`no_False_declaration_embedded` state that call itself, at the cost of one extra axiom Aeneas spends on the constant's definition.  `--pins FILE` and `--no-pins` bypass the decoder and are outside the theorems |
| `.Verified` of `h8` | verified mode | a `--trusted` run is outside the theorems |

The prelude's bytes are not a premise: con-leche's `preparePrelude` puts the
prelude's declarations into the checked stream, so soundness holds whatever
the prelude parses to.  The gate `scripts/gen-prelude-lean.sh --check` (§10)
still checks that con-ron ships con-leche's prelude.

### 3.2 The `.olean` path

`--olean` has its own two theorems,
[`no_False_oleans`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L810-L846)
and
[`model_exists_oleans`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L855-L883),
on the same three axioms.  They take the calls of §3 with the stream's two
replaced by the `.olean` reader's: `hroots`, the roots' names interned one by
one, and `h3`, the whole read of their import closure.  Soundness, with the
implicit arguments and the unchanged premises `h5`…`h7` left out:

```lean
theorem ConRon.Capstone.no_False_oleans (V : Type w) [ConLeche.SetTheory V]
    (hcl : ConLeche.Frontend.Olean.InClosure (absSearchPath dirs) F
      (names.map ConRon.Refine.absName).toArray m)
    (hv : ConLeche.Frontend.Olean.ViewOf (absSearchPath dirs) F m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all)
    (hty : c.type = .const ConLeche.falseName [])
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    (hroots : InternRoots emptyTier st2 names roots.val stR)
    (hsnap : SnapshotOf finst fsv F)
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store dirs roots none
      = ok (.Ok rd, store3))
    (h4 : frontend.prepare.prepare_d OleanRead.Insts… emptyTier { stR with store := store3 } pre
      rd.decls rd = ok (.Ok prepared, st4))
    …
    (h8 : ParallelAll prepared.decls.length (oleanWorkerInit st6.pins)
      (oleanJobStep finst fsv tier .Verified ipins prepared.decls rd.pins rd.values dirs)) :
    False
```

In words: if, in the files `F`, a module of the roots' import closure holds a
theorem whose type is `False`, then the binary's calls cannot all succeed.
The closure and the module's contents are con-leche's specification of the
format (`InClosure`, `ViewOf`), not anything about the fast decoder that
reads them.  The reader leaves a theorem's value in its file: the record holds
a reference, and the theorem's job (`olean_job`) reads the value into its own
scratch tier and checks the theorem with it.  The jobs take only the reader's
pins and the values' modules (`rd.pins`, `rd.values`); the merged constants, read
last by the preparation, are freed before the check.  `model_exists_oleans` takes the
same premises without `hcl` … `hty` and concludes as `model_exists` does, at
`RustDenotesFilled`: the records' stream with each reference replaced by a value
(con-leche states no model theorem for `--olean`).

The one new trust premise is
[`hsnap : SnapshotOf finst fsv F`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L184-L196):
every answer the file operations give (does the file exist, its real path,
its bytes, a byte range of it, its size) is the answer of one snapshot `F` of
the file system.  A failed operation claims nothing, because it gives no
accept.  So the theorems assume that the files do not change during the run
and that the driver's operations over `std` (`olean_fs::StdFs`) read what is on
disk; the reader itself, from the search for a module's files to the records
it hands to the rest of the pipeline, is verified.  A run with `--constant`
is outside the theorems.

§8 lists everything else that must hold for the theorems to describe the
binary: the translator, the compiler, and the hand-written models of what
Aeneas cannot translate.

## 4. The expression representation

The checker's state is one value,
[`AState`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/monad.rs#L300-L322):
the **arena** (the store of all terms), the per-call memo tables and the
per-declaration caches (§5), and the reserved-name pins (§6.1).  Checker
functions take it as `&mut AState`, together with the shared persistent tier
`&PersTier` (§4.4).

### 4.1 Handles

A term is named by a **handle**: one 32-bit word
([layout](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/handle.rs#L4-L30)).

```text
wide (expression app only)        narrow (every other node)
bit  31      tier                 bit  31      tier     (0 = persistent, 1 = scratch)
bit  30      1                    bit  30      0
bits 29…0    index                bits 29…26   constructor tag
                                  bits 25…0    index
```

The index is into that constructor's array in that tier.

There are four handle types, one per store
([`EIdx` … `LsIdx`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/handle.rs#L186-L212)):
expressions, names, levels and level lists (a constant's universe
arguments).  The expression tags
follow con-leche's constructor order, from `bvar` = 0 to `proj` = 9
([the tags](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/handle.rs#L511-L559)).

Because the tier bit sits above the index, a persistent handle keeps its
bits when the scratch tier comes and goes.  An `app` index has 30 bits and
every other index 26, so the `app` array holds at most 2³⁰ nodes per tier
and every other constructor's 2²⁶ (apps are 85 % of an export's expression
nodes); past that, `intern` raises
`Native`, and the twin's intern raises its `native` at the same probe miss.  A handle is its own hash
([`hash64`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/handle.rs#L397-L405)),
and two handles denote the same term only if they are equal (§4.2), so
comparing two terms is comparing two words.

### 4.2 Stores and hash-consing

Each store keeps, per tier, **one array per constructor**, each element a
fixed-size record of handles and scalars; an `app` node is two `u32`s
([`ETables`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/store.rs#L1186-L1200)).
The stores nest: an expression refers to names, levels and level lists, a
level to names.  Reading a node back (`view`) decodes the tag and reads one
array element; there is no node enum in memory.

Beside each array is a **derived column**: per node, the word con-leche
caches on the same term, computed with con-leche's formula.  For an
expression this is `Expr.data`: the structural hash, the loose
bound-variable bound, the free-variable range and the has-level-parameter
bit.  So "does this term have loose bound variables?" is one array read.

Every node is added through **`intern`**, which **hash-conses**: it looks
the node's fields up in the tier's **cons table** (a hash map from fields to
handle, which stores only the handle and compares the fields against the row
the handle names) and returns the existing handle if there is one
([`EStore::intern`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/store.rs#L3603-L3638)).
It probes the persistent table first, then the scratch table, and appends
only if both miss
([the `app` case](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/store.rs#L3888-L3935)).

Hash-consing is needed for soundness, not only for speed.  The checker
treats equal handles as equal terms and unequal name handles as unequal
names.  If two handles could denote the same term, the checker could take a
branch con-leche would not.  The twin proves the denotation injective on a
well-formed store
([`denoteE_inj`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Arena/WFProofs.lean#L1125-L1126)).

Levels and names are interned the same way, but level *algorithms*
(`simplify`, `leq`, `isEquiv`) run on ordinary `Level` trees read back from
the store, with the readback cached (§5).  Name equality is handle equality.

### 4.3 The two tiers

The arena has two **tiers**, each with its own arrays and cons tables:

* the **persistent tier** holds the parsed file, the prelude, the pins, and
  every term the environment keeps;
* the **scratch tier** holds what one declaration's check computes and then
  forgets.

The parse, the pin walk and the stream's index (§6.3) write the persistent tier
directly.  Each record's check then runs inside a **bracket** on a worker's own
store: `enter_record` empties the scratch tier and the memos, and
`leave_record` empties the scratch tier again and flushes the caches
([the bracket](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/core.rs#L10890-L10909)).
Nothing a check builds outlives it: what a declaration adds to the environment
is read off the record itself when the index is built, so no term ever has to
move from the scratch tier to the persistent one.  Dropping the tier leaves
persistent handles valid, because a persistent node never points into the
scratch tier.

### 4.4 Sharing the persistent tier between workers

The check phase runs on several threads (§6.4).  They share one persistent
tier and one stream index, read-only, and each owns a scratch tier.  Apart
from the pool's own bookkeeping (two atomic counters and the progress
observer's lock), the workers share nothing mutable.

In Rust, the sharing is a separate parameter, and it is also what makes a
store FROZEN.  After the index is built,
[`freeze_tier`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/checker.rs#L64-L87)
moves the four stores' persistent tables and the index out into one
[`PersTier`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/store.rs#L1217-L1269)
value whose `frozen` bit is set.  Every persistent read goes to the
`&PersTier` a function is handed when that tier is frozen, and to the store's
own tables otherwise; a worker's store is empty and FROZEN (its scratch tier
open), so every append it makes is a scratch append and none can reach the
shared tier, by construction, not by a guard.  After the check phase,
`thaw_tier` moves the tables back.  In the twin, the same sharing is a
`ReaderT PersTier` layer on the checker monad.

The environment has two tiers in the same way
([`IFEnv`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/env.rs#L586-L615)).
A job's environment is an empty layer of its own over the frozen index: a
lookup reads the layer first (skipped while it is empty), then the index below
the record's position.  No job copies the environment.

### 4.5 What is still an `Expr` tree

One thing still uses con-leche's tree representation (`kernel::expr`, an
`Arc` per node): **the pinned data**, con-leche's own constants that the
checker compares stream records against (the basis blocks, the axiom pins,
the `Nat` operation pins).  They are interned into the persistent tier once,
at startup (§6.1), and no tree is built afterwards while checking.

## 5. Caching

Caches exist at two lifetimes, both keyed on handles.  Keying on a handle
alone is sound because an `fvar` node carries its own type, so a handle
determines its typing context.

**Per-call memos**
([`Memos`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/monad.rs#L173-L235)).
Each term walk of con-leche's `ExprOps` (instantiate, abstract, lift,
instantiate level parameters, the bound computations) has its own table,
keyed by `(handle, cursor)`.  A walk's top-level entry clears its table, so
the value being substituted need not be in the key.  The walks also stop
early using the derived column
([the cutoffs](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/expr_ops.rs#L35-L49)):
instantiation returns a subterm unchanged once its loose-bound-variable
bound is low enough, level substitution once it has no level parameters.
Two more tables sit in the same record for their allocation only: the
declaration guards `allLevelParamsDefined` and `constsResolve` thread their
memo as an argument, as con-leche does, and the port parks it in the state
between calls, moving it out and emptying it at each entry
([`take_walk_memo`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/core_state.rs#L466-L513)),
or dropping it outright past 2¹⁶ slots.

**Per-declaration caches**
([`Caches`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/core_state.rs#L315-L377)).
These are con-leche's memo tables:

* `whnfCore`, `whnf`, `infer` and `inferIO`, each `EIdx ↦ EIdx`.
  The inference grades have separate tables, so an answer computed at one
  grade never serves another, and so do `whnfCore`'s two modes (the
  official kernel's cheap projections, which definitional equality runs,
  and the full mode, which `whnf` runs);
* `defeq` on the ordered pair, storing both `true` and `false` verdicts;
* level and level-list equivalence verdicts;
* a stored constant's type or value, and a recursor rule's right-hand side,
  at a universe instantiation;
* the readbacks of names, levels and level lists (§4.2);
* the eager tower's own set of the six entry-point tables (`eager_memos`):
  an eager comparison swaps it into the six fields for its length and back
  out after it, so an eager entry never serves a plain query, nor the other
  way round, and the eager entries are kept for the declaration like the
  plain ones.

**When they are emptied.**  The per-declaration caches are flushed whole
whenever a bracket closes (§4.3), which ends every job, as con-leche's
`flushC` flushes its own.  A cache entry can name a scratch handle,
so it must go with the tier.  The memos are cleared when a bracket opens and
at every walk's entry.  No table evicts entries and none has a size cap,
as in con-leche: a table grows for the length of its declaration and goes
whole at the bracket.

The type checker runs in two **lanes**
([`LANE_*`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/core.rs#L377-L390)),
one per con-leche knot: the full lane uses the caches above, and the IO lane runs `infer` and `inferIO` unmemoised and uses the
full lane for everything else.

**The hash map.**  The arena's tables use
[`ron::HashMap2`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/hashmap2.rs#L1-L40),
an open-addressed map whose slots carry an epoch stamp, so clearing it is
O(1).  It is proved to implement a finite map in
[`Refine/HashMap2.lean`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Refine/HashMap2.lean).  The cons tables are its key-free variant,
[`arena::cons_map`](https://github.com/leanprover/con-ron/tree/master/crates/con-ron-core/src/arena/cons_map.rs):
an 8-byte slot of stamp, 16-bit hash fragment and handle, the key read from
the row the handle names (task #148); it is proved by simulation, as
`HashMap2` on a view that puts the keys back
([`Refine/ConsMap.lean`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Refine/ConsMap.lean)).

## 6. The checking pipeline

### 6.1 The stages

The binary's `check_main` calls the verified functions in order, on one
`AState`
([`check_main`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron.rs#L308-L541)).
They are the stages of the theorems (§3): `h1`…`h5`, then the index and the jobs.

1. **`intern_reserved_pins`**
   ([`arena::pins`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/pins.rs#L1-L60)):
   about seventy names the checker compares by handle (`Nat`, `Nat.succ`,
   the `Nat` operations, `Bool`, the axiom names) are interned into the
   persistent tier once.  Afterwards each is one table read.
2. **`builtin_prelude_e`**: the built-in prelude (§1) is parsed into the
   store.
3. **`parse_source`**: the file is parsed, streaming (§6.2).
4. **`prepare_prelude`**
   ([`frontend::prepare`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/frontend/prepare.rs#L1-L50)):
   the prelude's declarations go first, using the file's own copy of each
   where it has one.  Then each pinned `Nat` operation's supporting
   definitions are moved ahead of it, if the file declares them later.  No
   record is dropped or changed; moving a record earlier can only turn an
   accept into a reject.
5. **`intern_all_pins`**
   ([`intern_all_pins`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/checker.rs#L162-L188)):
   every **pin** is interned into the persistent tier.  A pin is data,
   fixed by con-leche, that the checker compares stream records against:
   the five basis blocks, the standard and trusted axiom statements, and the
   `Nat.div`/`Nat.mod` pin list.  That list is embedded as text
   ([`PINS_TEXT`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/pins_text.rs#L40-L44),
   generated from con-leche by `scripts/gen-pins.sh`) and read by a verified
   decoder
   ([`decode`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/pins_decode.rs#L1336-L1356)).
6. **The check**: the stream's index, then every record's job (§6.3, §6.4).

### 6.2 Parsing

The parser is in the verified crate
([`frontend/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/frontend/mod.rs#L19-L30)).
The driver reads the file forward in 4 MiB chunks through the
[`HandleSource`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L924-L965)
chunk source and never holds the whole file.  Each line goes through a byte
recogniser ported from con-leche's `Scan/Fast.lean`, the scanner
con-leche's binary actually runs.  Records are interned straight into the
persistent tier, and a table from export index to handle keeps the export's
own sharing.  No expression tree is built.

The parser is the one place where the Rust uses loops rather than recursion,
because a per-byte recursion would overflow the stack.  Aeneas turns each
loop back into a recursive function, which mirrors con-leche's.

**From `.olean` files** (`--olean`).  The reader is con-leche's
`Frontend/Olean/*`, one Rust module per file, in the same directory of the
verified crate, and covered by the theorems (§3.2).  Nothing in the files
is trusted: the files are read through one trait of file operations (`OleanFs`,
implemented over `std` in the driver), every object is located, bounds-checked and
read field by field, and each object of a module is read once, in two passes, by
con-leche's fast decoder.  The values are interned straight into the persistent tier,
as the stream's are, so a node two modules share is one node.  The closure is taken
at the private level, merged as Lean's own import merges it and emitted in
lean4export's order, through the stream parser's own record builder, so that
everything after the parse is the stream path's.  The read is sequential: the store
has one writer, and con-leche's parallel load is not ported.

### 6.3 The index, then the jobs

There is no install phase.  After the parse, the stream's **index** is built
once, from the records alone
([`build_index`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/stream_index.rs#L161-L182)):
what each record adds to the environment is a function of the record
([`decl_constants`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/install.rs#L325-L361)
and `decl_tables`, con-leche's `Kernel/Install.lean`: a definition's constant, a
block's formers, constructors, recursors with the record's K flag and their
rules' firing mode, and its projection tables, read off its records with no
inference and no reduction — a pinned basis block like any other block, a
quotient record as the pin at the names it declares).  A name's first entry wins, so a later record
with a taken name sees it and fails "duplicate declaration" at its own position.

Every record's check is then a **job** at the index's view of its position
([`record_job`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/stream_index.rs#L220-L238)):
an empty environment layer of its own over the frozen index, with everything from
the record on hidden, in its own bracket (§4.3).  A job is the whole of what the
record asks: a definition's header, value and certificates, a theorem's
statement and proof, an axiom's pin, a pinned block's comparison with its pin, an
inductive block's checked install.  What depends on a family's sort (the ι case
split, the η rescue, a projection's guard at a `Prop` structure) is computed where
it is used, from the former's stored type.  The first failing job in fold order is
the verdict; a failing guard at record 9 no longer overtakes a failing value at
record 5.  On an `--olean` run a theorem's value stays in its file until its job,
which reads it into the worker's scratch tier
([`olean_job`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L603-L653)).

The checked install is con-leche's uniform route
(`arena/inductives/`, `check_decl`'s `.indDecl` arm): the recogniser reads
the block's members, constructors and recursors (`block_shape`); the formers
and the constructors are checked as constants; an unverified pre-pass reads
the classes the stream's recursors eliminate off their types
(`class_read`), and each class is checked as a major premise; one positivity
walk (`positivity`) runs over every constructor with the members as holes,
reducing with the kernel's own `whnf` and looking through a container at its
concrete instance; the recursor family is then generated in official's shape
from that walk's table (`gen_rec`), and the stream's recursors are compared
with the generated ones up to definitional equality, types binder by binder
and rules one by one, at the generated install, which is pushed for the
comparison and popped (`stream_recs`), each recursor's K flag compared with the
recomputed condition; what the block adds is what `decl_constants` reads off its
records.  A block the recogniser does not read is declined.

con-leche proves that every job passing is an accept of its pure fold
(`checkDecls_of_jobs`).

### 6.4 The worker pool

After the index is built, the driver freezes the persistent tier (§4.4) and runs
the jobs on a pool of threads
([`check_decls_driver_with`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L516-L576),
[`pool.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L35-L48)).
A worker has its own `AState`
([`worker_state`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/checker.rs#L119-L131)):
an empty store that reads the shared tier, its own memos and caches, and a
copy of the pin handles.  It borrows the frozen tier, which holds the index.
Workers claim one job at a time from a shared counter and run `run_job` on each,
so a worker's jobs come in increasing order.  Results are merged by job index and
read in fold order, so the verdict and the first failure reported do not depend on
timing.  `--jobs=1` is the same jobs on one worker; there is no other path.

The pool is one generic combinator,
[`parallel_all`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L232-L293),
which knows nothing about checking: the driver hands it `worker_state` as
each worker's initial state and `run_job` on the `k`-th job as the
step.  It is unverified, but everything a worker runs is verified: its
start state is the extracted `worker_state`, and each step is the extracted
`run_job` (on an `--olean` run, `olean_job`: the extracted value read and the
extracted `record_check`, in the extracted bracket).
If the OS refuses a worker thread, the pool runs on the workers it has (on
the calling thread if none); the verdict does not depend on the count.

### 6.5 Errors

The Rust error type
([`CheckError`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/core_types.rs#L86-L91))
has con-leche's three kinds (`NotImplemented`, `Invalid`, `Internal`) and a
fourth, **`Native`**, for failures con-leche cannot have: a full handle
array.  (The `Nat` operations have no such limit: a result too large for
memory fails like any other allocation.)  The twin has the same fourth kind,
and Theorem 2 says that wherever the Rust raises any of the four, the twin
raises the same kind at the same point.  There is one exception: a numeral
in the export too large for the Rust scanner's `u64` (`IndexOverflow`, a
`Native`), because the twin runs con-leche's own scanner, which reads a `Nat`;
the frontend's error relation names that error value explicitly
([`ScanOverflowErr`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Frontend/Shape.lean#L387-L389)).
The twin's `native`, like a decline, claims nothing about con-leche.  The
driver reports `Native` as a decline, exit 2
([`exit_code`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L154-L163)).

## 7. How the proof is built

The two theorems compose three layers, each refining the next one down:

```
(C) the Aeneas model of the Rust ──Theorem 2 (Refine2/**)──▶ (B) the twin (Arena/**)
(B) the twin                     ──Theorem 1 (Bridge/**)───▶ (A) con-leche's pure checker
```

The twin is what makes the split work.  Theorem 1 relates two different
representations (handles and trees), but between two Lean programs.
Theorem 2 relates a Lean program to extracted Rust, but at the same
representation, so its relation says only "the same data in two encodings".

### 7.1 From Rust to Lean

Charon compiles the verified crate, and Aeneas translates it to Lean
([`scripts/extract.sh`](https://github.com/leanprover/con-ron/tree/master/scripts/extract.sh)):
one definition per function, in a `Result` monad with `ok`, `fail` (a panic)
and `div` (non-termination); `&mut` arguments become state passed in and
returned; recursion becomes `partial_fixpoint`.  The output is committed in
[`proof/ConRon/Generated/`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Generated),
and a gate fails if it is not what the crate extracts to today.

Aeneas handles a subset of Rust, and the verified crate stays inside it: no
closures, no `?`, no `derive`, no `std::collections`, no `unsafe`,
higher-order arguments as one-method traits, and recursion instead of loops
outside the parser.
[`scripts/lint-rust-style.sh`](https://github.com/leanprover/con-ron/tree/master/scripts/lint-rust-style.sh)
enforces the mechanical rules; DESIGN.md §3.4 lists all of them.  Release
builds keep `overflow-checks` on
([`Cargo.toml`](https://github.com/leanprover/con-ron/blob/master/Cargo.toml#L22-L23)),
so an overflow the model calls `fail` is a panic in the binary, not a
silent wrap.  `AENEAS_FINDINGS.md` records what the port learned about the
translator.

### 7.2 The twin

The twin
([`proof/ConRon/Arena/`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Arena))
is an executable Lean checker with the same stores, handles, caches and
functions as the Rust, down to the order of operations.  Each Rust item
with a twin names it in a `Lean twin:` doc line, and a gate checks those
lines (§10).  Its monad is `ReaderT PersTier (StateT AState (Except CheckError))`;
it uses no `IO` and no `partial`, and fuel is an explicit `Nat`.

Two definitions connect it to con-leche:

* **Denotation.**
  [`denoteE`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Arena/Denote.lean#L185-L208)
  reads a handle back into con-leche's `Expr`, and returns `none` on a
  dangling handle.
* **Well-formedness.**
  [`StoreWF`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Arena/WF.lean#L1-L39)
  says the store is acyclic (by a rank that exists only in the proof), each
  cons table is exactly the inverse of its array, the derived column is
  exact, no scratch entry duplicates a persistent one, and persistent nodes
  have persistent children.  From it follow the injectivity of `denoteE`
  and extension,
  [`Ext st st'`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Arena/Denote.lean#L274-L278):
  every handle that denoted a term still denotes the same term later.

### 7.3 Theorem 1: the twin refines con-leche

[`proof/ConRon/Bridge/`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Bridge)
proves that every twin function computes, on denotations, what the
corresponding con-leche function computes.  The per-declaration statement
is
[`Arena.checkDecl_bridge`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Checker/Fold.lean#L114-L121),
and
[`Arena.pooledAccepts_bridge`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Checker/Pool.lean#L96-L116)
lifts it to the check phase the driver runs: the index built from the records
denotes con-leche's index of the denoted stream, and every job accepting is
the pure fold accepting that stream at some fuel.  The proof is an induction
in fold order: a job runs at the frozen index's view of its position, which is
the environment of the records before it, and the jobs before it (each worker's
claims are increasing) give that the fold accepted them.  That environment is
well formed by con-leche's model-free `foldlM_checkDecl_envWF`
(`ConLeche/Semantics/DeclWF.lean`), so Theorem 1 takes no set theory: `[SetTheory V]`
enters only at step 3 below, where con-leche's soundness builds the model.  Theorem 1 owns every invariant of the twin's state,
`StoreWF` included.

The store primitives and the type checker are specified by Hoare triples
of Lean's `Std.WP`, in one fixed form, proved with `vcgen` (task #111); the
`@[spec]` lemmas of
[`Bridge/Specs.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Specs.lean#L1-L31)
cover one primitive each:

```lean
⦃fun s => s = s₀⦄ f args ⦃fun r s' => Post s₀ r s'; ⊤⦄
```

The precondition only fixes the start state, and the exception
postcondition `⊤` means partial correctness: nothing is claimed when the
twin fails.  Many higher-level
statements are instead plain implications over a successful run, like the
graded ones below.

**Spec grades.**  A twin function's statement has one of two grades
([`Bridge/Inductives/Run.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Inductives/Run.lean#L60-L76),
[`Rel.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Inductives/Rel.lean#L59-L76)):

* **pure grade** (`PSpec`), for functions that do not call the type
  checker: invariant `StateOK` (the store is well-formed), frame `PStep`
  (the store only extended, caches and pins untouched), and the statement
  may not mention the caches;
* **core grade** (`CSpec`), for functions that call the type checker:
  invariant `CheckOK` (also: every cache entry is a true con-leche answer at
  some fuel), frame `CoreStep`, and the type checker's own specification as
  a hypothesis.

A pure step lifts to a core step (`PStep.toCore`), so a core-grade function
may call a pure-grade one; not the other way.

An example at the pure grade
([`StructParts.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Inductives/StructParts.lean#L127-L173)).
The twin's `structPsAt` interns a list of `bvar` nodes; the theorem says the
list denotes con-leche's:

```lean
theorem structPsAt_spec (o nP : Nat) :
    PSpec PT (Arena.structPsAt o nP) (REL (ConLeche.structPsAt o nP)) := by
  intro s₀ s' r hok _ hrun
  obtain ⟨hstep, hd⟩ := structPsAt_go_run o nP nP 0 hok hrun
  refine ⟨hstep, ?_⟩
  simpa only [ConLeche.structPsAt, Nat.zero_add] using hd
```

The work is in `structPsAt_go_run`, just above it: an induction on the
number of nodes left, composing `internBVarE`'s spec with `PStep.trans`.

The type checker itself (con-leche's knot of `whnfCore`, `whnf`, `infer`,
`inferIO`, `defeq` and the eager tower's `defeqE`) is one statement indexed by
fuel and eager flag,
[`KnotSpec`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Core/Knot.lean#L111-L128),
proved by induction on the fuel, over both flags at once (the eager slot runs
the knot one level down with the flag set), in
[`knot_spec_all`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Core/Induction.lean#L67-L91).

### 7.4 Theorem 2: the Rust refines the twin

[`proof/ConRon/Refine2/`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Refine2)
proves that each extracted Rust function, run from a state related to the
twin's, is matched by the twin function.  The proof is **lockstep**: both
sides perform the same operations in the same order, and the relation
carries representation facts only.  Every invariant belongs to Theorem 1.
A lemma that will not go through points at a divergence between the twin
and the Rust, which is fixed by making the two programs agree, not by
adding an invariant.

**The relation.**
[`AStateRel₀`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/AbsState.lean#L352-L366)
relates the Rust `AState` to the twin's field by field (store, memos,
caches, pins): the same data, abstracted by functions such as `absEIdx` and,
for hash maps, by the map they represent.
[`AStateInv`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/AbsState.lean#L375-L380)
holds the Rust-only invariants, such as each hash map's own well-formedness.

**The statement.**  A state-threading Rust function is specified by
[`Sim₀`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Shape.lean#L205-L209):
if the Rust returns `Ok r` in state `st'`, the twin returns `A r` in a state
related to `st'`; if the Rust returns a mirrored error, the twin throws the
same kind (`Native` included: the twin raises its `native` at the same point,
task #98-NATIVE).
[`SimRel₀`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Checker/Shape.lean#L146-L150)
is the same with a relation `R r v` in place of the function `A`.

**The judgements.**  Inside proofs, statements take a form in which both
programs are visible in the goal
([`Tactic/Lockstep.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Lockstep.lean#L1-L30)).
The form depends on the shape of the Rust function:

| judgement | Rust shape |
|---|---|
| [`LS`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Lockstep.lean#L164-L168) | returns a result and a new state |
| [`LSR`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Lockstep.lean#L170-L174) | reads the state, may fail |
| `LSV`, `LSW` | reads and cannot fail; writes and cannot fail |
| `LSP` | a Rust-only step with no twin counterpart (a copy, a `u64` decrement) |
| [`LSM`, `LSRM`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Lockstep.lean#L633-L645) | a memoised walk that returns its memo beside the result |

`LS.toSim₀` converts back to the statement form.

**The `lockstep` tactic**
([`lockstep`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Lockstep.lean#L2661-L2662))
steps the two programs together, one bind at a time.  At each Rust bind it
looks up a lemma for the callee, applies it, and continues with the related
results as hypotheses.  It splits a Rust `if` or `match`, and uses the facts
this gives to decide the twin's.  Side goals go to `simp`, `omega` and
`scalar_tac`; it never calls `grind`.  Every alternative it tries runs without
error recovery, so a term that fails to elaborate makes the alternative fail
instead of closing the goal with `sorry`.  When it stops, the goal sits at the
first bind where the two programs differ, or where a lemma is missing.

**The lemma discipline.**  A lemma is found by its Rust callee: tagging it
[`@[lockstep]`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Attr.lean#L86-L94)
files it under the head constant of the Rust computation in its conclusion,
which must be one of the judgements above.  A local hypothesis in the same
form, such as an induction hypothesis, is found the same way, and is tried
before any lemma.  When several lemmas cover one callee, the first that
applies wins: higher priority first (`@[lockstep high]`), then registration
order; `attribute [-lockstep] foo` removes one.  Lemmas for
handle primitives (copies, handle equality) live in one place,
[`Tactic/Prims.lean`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Refine2/Tactic/Prims.lean).
Proofs extend the tactic only through these attributes (and
`@[lockstep_simp]`, `@[lockstep_inline]`, `@[lockstep_congr_simp]` for twin
equations used only to match a lemma's twin against the goal's, and the
side-goal tactic's `macro_rules`), not by editing its core.

**Representation premises.**  Charon erases the proofs inside con-leche's
subtypes.  A con-leche name component is a `String`, whose characters carry
a proof that they are valid code points; the Rust stores it as a `Vec<u32>`,
which admits values the twin's type cannot represent.  Where a lemma needs
the erased fact, it takes it as a premise:
[`NameWF`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L488-L493)
holds of exactly the names the port's smart constructors can build from valid
code points, and `LevelWF` and `PropWhenWF` lift it to levels and to the
zero-ness datum.  The store invariant carries the same fact for every stored
string.  An example of a lemma with such a premise
([`Refine2/Core/LS/PrimsA1.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Core/LS/PrimsA1.lean#L1312-L1316)):

```lean
@[lockstep] theorem level_param_ls (n : kernel.name.Name) (hn : ConRon.Refine.NameWF n) :
    LSP (kernel.level.param n)
      (fun u => ConRon.Refine.LevelWF u ∧
        TwinEq (.param (ConRon.Refine.absName n)) (ConRon.Refine.absLevel u)) :=
  fun _ h => ⟨ConRon.Refine.Level.param_wf' h hn, (ConRon.Refine.Level.param_refines h).symm⟩
```

The whole proof is: the two refinement lemmas of `level.param`, one for the
premise it preserves and one for the value.

### 7.5 Induction recipes

A walk over a DAG has no structural order, so both sides take fuel, and
their lemmas go by induction.  Two recipes cover most of Theorem 2.

**Fuel induction.**  State an `_aux` lemma over `n` with `fuel.val = n`,
induct on `n`, unfold both sides at `0` and at `m + 1`, and run `lockstep`;
it finds the induction hypothesis in the context.  Then register the general
form with `@[lockstep]`
([`instantiate1_go`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/ExprOps/Mut.lean#L290-L319)):

```lean
theorem instantiate1_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (v : arena.handle.EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) (d : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate1_go pers st v fuel h d) lst
        (instantiate1Go (absEIdx v) n (absEIdx h) (absU d)) := by
  induction n with
  | zero =>
    intro pers st lst v fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate1_go, instantiate1Go_zero]
    lockstep
  | succ m ih =>
    intro pers st lst v fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate1_go, instantiate1Go_succ]
    lockstep
```

**Cursor induction.**  Where the twin recurses on a `List` and the Rust
walks a `Vec` with an index `i`, induct on `args.length - i`, and relate the
twin's list to the suffix from `i`
([`inst_spine_from`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/ExprOps/Mut.lean#L614-L634)):

```lean
theorem inst_spine_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (t : Std.U64) (e : arena.handle.EIdx),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_spine_from pers st fuel args i t e) lst
        (instSpine (absU fuel) (absEIdxListFrom args i) (absU t) (absEIdx e)) := by
  induction n with
  | zero =>
    intro pers st lst fuel args i t e hn hrel hinv
    rw [arena.expr_ops.inst_spine_from, listFrom_nil args i (by omega), instSpine]
    lockstep
  | succ k ih =>
    intro pers st lst fuel args i t e hn hrel hinv
    rw [arena.expr_ops.inst_spine_from, listFrom_cons args i (by omega), instSpine]
    lockstep
```

Theorem 1 uses the same cursor recipe (`structPsAt_go_run`, §7.3).

**The type checker.**  The six mutually recursive functions of con-leche's
type checker are tied by fuel on both sides.  Theorem 2 states them as one
relation per fuel, `KnotRel f`, and proves it for every `f` in
[`knot_rel`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Core/Induction.lean#L1123-L1123):
fuel `0` directly, fuel `f + 1` from the six function bodies at fuel `f`.

### 7.6 The composition

[`Capstone.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L14-L85)
contains no new mathematics, only glue:

1. **Theorem 2, stage by stage**: each of `h1`…`h5` becomes a twin run from
   the twin's own start state, related at every step.  The sixth stage
   (`h6`…`h8`, assembled by `poolAccepts_intro`) goes through
   [`pool_accepts_refines`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Checker/Phased.lean#L283-L292).
2. **Theorem 1** (`Bridge/Stages.lean`): the twin runs feed
   `Arena.pooledAccepts_bridge`, so con-leche's pure fold accepts the denoted
   stream at `streamEnv` of it.  Theorem 1 also supplies the one twin-side fact
   the headline relation needs: `StoreWF` of the final twin store.
3. **con-leche**: `checkDeclsPure_sound_of` turns the pure accept into a
   model, and `no_proof_of_False_pure` rules out the `False` theorem.

### 7.7 The leaf tier

The Rust types that do not depend on the arena are proved directly against
their mathematical meaning, in
[`proof/ConRon/Refine/`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Refine):
the bignum `ron::Nat`, the two hash maps, names, levels, `PropWhen`, the
`Expr` values of the pinned data, and the pin decoder.  Theorem 2 uses these
lemmas wherever the arena calls such code.

## 8. Trust

What must hold for the theorems to describe the binary.  A script keeps
§8.1 in step with the code; §8.2 is the rest.

### 8.1 What the proof does not see: the holes

The theorems are about the verified crate *as Aeneas translates it*.  Where
Aeneas meets an item it cannot translate, it declares an axiom and asks for
a hand-written model
([`TypesExternal.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/TypesExternal.lean#L41-L42),
[`FunsExternal.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L25-L72)).
Each model is a claim about the Rust that no proof checks.  These **holes**
are listed below: one type and five functions, all from the standard
library.  `scripts/extract.sh --check` fails if the crate grows a hole with
no model, and `scripts/holes.sh --check` fails if this table and the holes
differ.

<!-- holes: begin — scripts/holes.sh --check keeps this table and the templates in step; the first cell holds the Lean names of the holes, in backticks -->

| hole | the Rust | the model | why the model is faithful |
|---|---|---|---|
| [`alloc.sync.Arc`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/TypesExternal.lean#L41-L42) | `Arc<T>`, named once as [`ron::ptr::P<T>`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/ptr.rs#L1-L8) | `T`: a pointer *is* its contents | The port never mutates through an `Arc` (the lint forbids `get_mut`, `make_mut`, `Weak` and interior mutability), so sharing is invisible to the value |
| [`alloc.sync.Arc.new`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L25-L26), `alloc.sync.Arc.Insts.CoreCloneClone.clone`, `alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref` | `Arc::new`, `Arc::clone`, `Deref::deref` | `ok x`: the identity | Allocation, a count bump and a dereference return the same contents; the model has no notion of the count |
| [`alloc.sync.Arc.ptr_eq`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L36-L38) | `Arc::ptr_eq` | `ok false`: the model always takes the slow path | An under-approximation: every place the Rust takes the fast path (the memo tables' pointer-verified buckets, `beq`'s pointer fast path) has a lemma that the fast path's result is the slow path's |
| [`core.str.Str.as_bytes`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Generated/FunsExternal.lean#L71-L72) | `str::as_bytes`, at its one call site on `PINS_TEXT` | `ok s`: the identity | Aeneas already models a `&str` as its bytes |

<!-- holes: end -->

`Arc` is used only by tree values: the pinned data (§4.5) and the names and levels the checker reads back.  The arena's nodes are handles.

### 8.2 The rest of the trust surface

| trusted | what stands in for it |
|---|---|
| **con-leche's own assumptions**: a set theory `V`, con-leche's soundness proof at the pinned revision, Lean's kernel checking the proofs, and the axioms `propext`, `Classical.choice`, `Quot.sound` | con-leche's own documentation |
| **Aeneas and Charon**: the Lean model is what the Rust means | Nothing; a translator bug is a hole.  The crate stays inside the documented subset (§7.1), and `AENEAS_FINDINGS.md` records what the port found, all of it worked around in the Rust |
| **`rustc`, the Rust standard library and the allocator** | Nothing.  This is the trade the project makes: these instead of Lean's compiler, runtime and GMP.  The mimalloc wrapper in `con-ron-dump` is the only `unsafe` code in the workspace; an allocator can change memory use and time, not a verdict |
| **`overflow-checks = true`** in the [release profile](https://github.com/leanprover/con-ron/blob/master/Cargo.toml#L22-L23) | The model is the checked-arithmetic one.  A build without it would wrap where the model fails |
| **The driver**, [`driver.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L1-L55) and the binary's `main` | That it calls the verified stages in the order of `h1`…`h8` (§3), on one state from `AState::empty()`, with the pin list the verified decoder reads from the embedded text and `--verified`, and maps the outcome to the exit codes of §2.2.  The read loop is the verified `parse_source`; that the file handle returns the file's bytes in order is `hreads`.  The check phase is a [straight line of verified calls](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L516-L576) (the index, freeze, the jobs as `parallel_all` over two verified closures, thaw), and the progress observer between them holds only shared references |
| **The worker pool**, [`pool.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L50-L102) | One generic combinator, `parallel_all(n, workers, init, step, after)`, that knows nothing about checking.  Its contract is an argument about its control flow, not a proof: if it returns `Ok`, every index in `0..n` was claimed by some worker, and each worker built its state with `init` once and folded `step` over its claims in claim order, every step `Ok`.  That is `h8`, with the driver's closures (`worker_state`, `run_job`) written in; the proof reads it as [`ParallelAll`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Checker/Jobs.lean#L170-L174) and turns it into one accepting fold per worker.  The contract also promises that each worker's claims strictly increase: the code hands out claims off one monotone counter, and the pool's test asserts it.  Theorem 1 needs this: it inducts in fold order, and a job's start state is reached through the jobs its worker ran before it, whose own checks are known correct only at positions already proved.  The contract does not promise that an index is claimed only once (the code does that too); the proof does not need it.  Results are merged by index, and an accept means every slot is `Ok`.  Nothing is claimed about which worker ran which index: the capstone relates each worker's walk to the twin separately.  Tests check the partition property generically, and that the check phase agrees with the one-worker walk and reports the first failure, at every worker count |
| **The `.olean` file operations**, `olean_fs::StdFs` | That their answers are one snapshot's: `hsnap` (§3.2).  The files' contents are not trusted |
| **`Native` errors: partial correctness** | Theorem 2 relates a Rust `Native` to the twin's `native` at the same point, and a twin `native` claims nothing about con-leche, so soundness is unaffected and completeness is not proved.  The arena's sites are the 2²⁷-entry arrays' capacity tests, mirrored by the twin; the one the twin does not mirror is the scanner's `u64` overflow on an oversized numeral (§6.5).  The pin decoder's `Native` is outside Theorem 2: the capstone assumes the embedded pins decode |

Nothing else: no `native_decide`, no `sorry`, and no axiom beyond the three
in §3.

## 9. Performance

<!-- perf-table:begin -->
Measured with `perf stat -e instructions:u,cycles:u`.  Instruction counts
are the measure of record, because they do not depend on machine load; wall
time and peak memory are secondary.  con-ron is its `cargo build --release`
binary (mimalloc, its default allocator) and con-leche its `lake build`
binary, both run with `--verified`; nanoda is its `cargo build --release`
binary (the system allocator) in its default serial configuration.  The
inputs are `lean4export` exports (made with Lean 4.35.0-rc3) of Lean's
`Init` (57 919 declarations) and of Mathlib (703 103).  The table is one
snapshot, taken on 2026-10-05: con-ron at `37ca84fe`, con-leche at its pin
`67f04630`, nanoda at `4c544ed4`.  `Init` wall time is the range of 3 runs
on a shared machine (one-minute load average 9.3–15.8 at the starts of the
runs); Mathlib was run once per checker, so it has no wall-time column.

| | `Init` instructions | `Init` wall, peak RSS | Mathlib instructions | Mathlib peak RSS |
|---|---:|---|---:|---:|
| **con-ron**, one worker | 211.50 G | 21.8–22.0 s, 0.56–0.64 GB | 3 848 G | 7.26 GB |
| **con-ron**, eight workers | 212.97 G | 5.4–5.6 s, 0.82–0.88 GB | 3 861 G | 7.55 GB |
| con-leche, one worker | 488.94 G | 48.2–48.3 s, 0.42 GB | 8 853 G | 7.31 GB |
| nanoda, one worker | 225.76 G | 23.4–23.9 s, 0.36 GB | aborted: memory cap (27 GiB) | 27.67 GB |

Single-threaded, con-ron executes 43.3 % of con-leche's instructions on
`Init` and 43.5 % on Mathlib, and 93.7 % and no figure (nanoda on Mathlib:
aborted: memory cap (27 GiB)) of nanoda's.  Eight workers change con-ron's
instruction count by +0.7 % on `Init` and +0.3 % on Mathlib (medians of the
runs throughout).  CLAUDE.md's memory budget is 3× con-leche's peak RSS on
the same export: every con-ron peak is within it (largest peak 0.88 GB
against 1.25 GB on `Init`, 7.55 GB against 21.94 GB on Mathlib).
`scripts/bench-baselines.sh` runs the measurements and
`scripts/perf-table.py` writes this section from its raw files (both:
`scripts/bench-baselines.sh --build --render --task <id>`);
`scripts/corpus.sh` builds the exports; the raw numbers are in DESIGN.md's
task #114 section.
<!-- perf-table:end -->

## 10. Keeping the port honest

**Provenance.**  Every item of the verified crate carries a doc line naming
the con-leche source it ports, `/// con-leche: <path>:<a>-<b> <declaration>`,
or `/// con-leche: none — <reason>`
([an example](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/handle.rs#L511-L514)).
`scripts/provenance.py check` verifies that each citation still names that
declaration at those lines of the pinned con-leche.  Arena items also carry
a `Lean twin:` line, which `scripts/twin-lines.py check` verifies against
`proof/ConRon/**`.

**The con-leche pin.**  con-leche is a `lake` dependency of `proof/`, pinned
by `rev` in `proof/lakefile.toml`.  To move the pin: edit the `rev`, run
`lake update con-leche` in `proof/`, then `scripts/provenance.py update`.
That moves citations whose text only moved, and marks those whose text
changed with a `CHANGED` line, which `check` rejects until the item is
re-ported.  DESIGN.md §7 has the procedure.

**Differential testing.**  `scripts/diff-e2e.sh` runs the binary on
con-leche's own test fixtures (602 streams) and compares each exit code with
con-leche's recorded one, in both modes and at several worker counts, and
ends with con-leche's display gate (three fixtures whose names and `safety`
field carry control sequences, run with `--progress=1`: no raw control, bidi
or zero-width character and no line starting with `::` may reach the
output).  This covers what the proof does not: the driver and the pool.  CI
runs it (`.github/workflows/ci.yml`).  `scripts/diff-olean.sh` runs con-leche's
`.olean` table (`tests/olean.sh`, 109 cases, on fixtures compiled by its
`tests/olean/build.sh` under `_tmp/`) against the binary, and CI runs that too;
with `--compare` it also compares the reader's records with lean4export's, on
`Init` and on one constant's cone, which needs an exporter and is not in CI.

**The gates.**  `scripts/gates.sh` runs before every commit
([the steps](https://github.com/leanprover/con-ron/blob/master/scripts/gates.sh#L6-L36)).
It stops at the first failure of: `cargo build` (warnings denied) and
`cargo test`; the style lint and the dead-code check (`scripts/dead-rust.py`,
no public Rust item without a caller); the provenance check, the check that
only a branch's last commit moves the con-leche pin (`scripts/pin-last.py`),
and the twin-line check; this
document's link check (`scripts/overview-links.sh`) and holes table
(`scripts/holes.sh --check`); the checks that the embedded pin text, the
Rust prelude text and the twin's prelude bytes are con-leche's
(`gen-pins.sh`, `gen-prelude.sh`, `gen-prelude-lean.sh`, each `--check`);
`scripts/extract.sh --check`; and `lake build` of the default targets, which
include `ConRonBridge`, `ConRonRefine2` and `ConRonCapstone`, failing on any
warning from `proof/`'s own sources.

**Upstream patches.**  One: the pinned Aeneas builds its Lean library
against an older Lean, and
[`patches/aeneas.patch`](https://github.com/leanprover/con-ron/tree/master/patches/aeneas.patch)
(595 lines, nineteen files) makes it build on con-leche's Lean (v4.35.0)
and its Mathlib.  `scripts/setup-aeneas-lean.sh` applies it.  Charon and con-leche
are used unpatched.

## 11. Module map

Rust modules mirror con-leche's files, and function names are con-leche's in
snake case.  Twin files mirror the Rust modules.

**Rust** (`crates/`)

| where | what |
|---|---|
| [`con-ron-core/src/arena/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/mod.rs#L1-L22) | the checker: `handle`, `store` (§4), `monad` (`AState`, the memos), `core_state` (the caches), `expr_ops`, `core` (the type checker), `decl_check`, `check_decl` (one declaration's check), `inductives/` (the uniform inductive route: `block_shape`, `class_read`, `field_tele`, `positivity`, `gen_rec`, `rec_check`, `stream_recs`, `block_install`, …), `install` (what a declaration adds), `stream_index` (the index and a record's job), `checker` (the check phase's sequential pieces), `pins` |
| [`con-ron-core/src/frontend/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/frontend/mod.rs#L19-L30) | the parser: scanner, record assembly, ground hoist, prelude |
| [`con-ron-core/src/kernel/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/lib.rs#L33-L54) | representation-free types (`Name`, `Level`, `PropWhen`, `CheckError`, `CheckMode`), the pinned data as `Expr` values, `pins_text` and `pins_decode` |
| `con-ron-core/src/ron/` | replacements for the Lean runtime: `nat` (bignum), `hashmap`, `hashmap2`, `ptr` (`Arc`) |
| `con-ron/src/` | unverified: the binary, `driver`, `pool`, `olean_fs` (the `.olean` reader's file operations over `std`), and `olean-compare` |
| `con-ron-dump/` | unverified: the `con-ron-pins/2` reader and writer, the global allocator |

**Lean** (`proof/ConRon/`)

| where | library | what |
|---|---|---|
| `Generated/` | `ConRon` (default) | the committed Aeneas model and the hand-written hole models |
| `Refine/` | `ConRon` (default) | the leaf tier (§7.7) |
| `Arena/` | `ConRonArena` (default) | the twin (B), with `Denote.lean`, `WF.lean`, `WFProofs.lean` |
| `Bridge/` | `ConRonBridge` | Theorem 1 |
| `Refine2/` | `ConRonRefine2` | Theorem 2; `Tactic/` holds `lockstep` |
| `Capstone.lean` | `ConRonCapstone` | the two headline theorems |

`vendor/aeneas/` is Aeneas as a submodule, for its Lean library and
documentation; `scripts/` holds the gates and tools of §10.
