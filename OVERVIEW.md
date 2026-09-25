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

Before the file's own declarations, every run installs a small built-in
prelude: the basis blocks con-leche pins (`Eq`, `Nat`, `PUnit`, `Empty`,
`False`, `Quot`) and the toolchain's `Bool` and `And`.  The prelude text is
con-leche's own, embedded at build time
([`prelude_text.rs`](https://github.com/leanprover/con-ron/tree/master/crates/con-ron-core/src/frontend/prelude_text.rs)).

Mutual and nested inductive blocks are handled as con-leche handles them: an
*in-process modeller* translates each block into ordinary declarations, which
the checker then checks like any other (§6.2).  The modeller is not verified,
and soundness does not need it to be: a wrong translation is rejected, not
accepted.

## 2. Running it

### 2.1 Command line

```
con-ron [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
        [--progress[=<stride>]] [--pins FILE|--no-pins]
        FILE.ndjson
con-ron --help
```

([the usage text](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron.rs#L87-L212))

* **`--verified`** is the default, and the only mode the theorems cover.
* **`--trusted`** runs the same checker with con-leche's certification-only
  checks switched off.  It is faster, and an accept in this mode is outside
  the theorems.
* **`--jobs=<n>`** sets the number of worker threads for the check phase
  (§6.4).  The default is one per hardware thread, at most 16.  Each worker
  reserves 1 GiB of stack address space, which counts against `ulimit -v`.
  The verdict, and the declaration a rejection names, are the same at every
  `n`.
* **`--progress[=<stride>]`** prints a heartbeat on stderr: one line per
  `stride` declarations installed or checked.
* **`--pins FILE`** and **`--no-pins`** replace the embedded `Nat.div`/`Nat.mod`
  pin list (§6.1).  They exist for testing and are outside the theorems.
* **`--no-mark-persistent`** is accepted for command-line compatibility with
  con-leche and does nothing.

Three environment variables belong to the in-process modeller, as in
con-leche.  `CON_LECHE_INMODEL=0` turns the modeller off, so the checker
declines every mutual or nested block.  `CON_LECHE_INMODEL_CENSUS=1` reports
each such block's outcome after parsing and stops with exit 2.
`CON_LECHE_PROJREC_TRACE` names each rewritten projection function.  The
first two are parameters of the theorems (§3.1), so runs with them set are
covered; an integration
test
([`inmodel_flags.rs`](https://github.com/leanprover/con-ron/tree/master/crates/con-ron/tests/inmodel_flags.rs))
checks that they do what the help text says.

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
[`proof/ConRon/Capstone.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L14-L144).
They are stated about the Aeneas model of the Rust functions the binary's
`check_main` calls, one premise per call, in the order it calls them, from
the binary's own start values.  Both depend on con-leche's three axioms
(`propext`, `Classical.choice`, `Quot.sound`) and on nothing else: no
`sorry`, no `native_decide`.  A `#guard_msgs` check keeps it that way
([the census](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L955-L971)).

**Soundness**
([`ConRon.Capstone.no_False_declaration`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L806-L844)),
with the implicit arguments left out:

```lean
theorem ConRon.Capstone.no_False_declaration (V : Type w) [ConLeche.SetTheory V]
    (hmr : ModellerRefines inst m ConRon.Arena.Frontend.inProcessModeller)
    (hfalse : ConLeche.jsonWithTheoremFalse (absChunks chunks))
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e inst emptyTier m st1 = ok (.Ok pre, st2))
    (hreads : ReadsAs sinst src chunks.val)
    (h3 : frontend.export_c.parse_source inst sinst emptyTier m st2 src inModel census
      = ok (.Ok r, st3, src'))
    (h4 : frontend.prepare.prepare_d emptyTier st3 pre r.decls = ok (.Ok prepared, st4))
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.annot_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend), st6))
    (h7 : arena.checker.freeze_tier st6.store = ok (tier, frozen))
    (h8 : ∃ ws : List (List (Fin pend.length)),
      (∀ k, ∃ w ∈ ws, k ∈ w) ∧
      ∀ w ∈ ws, ∃ st', (do
        let st ← arena.checker.worker_state st6.pins
        w.foldlM (fun st (k : Fin pend.length) => do
          let (r, st) ← arena.checker.check_pending tier st .Verified fe pend.val[k]
          match r with
          | .Ok () => ok st
          | .Err _ => fail .panic) st) = ok st') :
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
([`ConRon.Capstone.model_exists`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L739-L776))
takes the same premises without `hfalse` and concludes

```lean
    ∃ env, RustDenotes fe st6 env ∧ Nonempty (ConLeche.Model V env)
```

where
[`RustDenotes`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L583-L587)
says that the environment the Rust accepted (`fe`) is related to a twin
environment, which denotes the con-leche environment `env`; `env` has a
model (con-leche's `Model V env`) in every set theory `V`.  The statement
goes through the twin because the Rust store is related to the twin's by a
relation, not mapped by a function (§7.4).

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
| `[ConLeche.SetTheory V]` and con-leche's soundness | a set theory to build the model in; con-leche's `checkDeclsPure_sound_of` and `no_proof_of_False_pure` at the pinned revision | con-leche's own proof, on the same three axioms |
| `h1`…`h5`, `hpins` | the binary ran exactly these extracted functions, in this order, on one state that starts at `AState::empty()` under one `PersTier::empty()` | the driver's calling order, which starts [here](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron.rs#L373-L392); each call carries a `// ConRon.Capstone: hᵢ` comment: trusted |
| `h6`, `h7`, `h8` (phase A, the freeze, phase B) | the install phase (`annot_fold_hooked`) accepted, `freeze_tier` moved the persistent tables into the tier, and phase B's `parallel_all` accepted: there are index lists `ws`, one per worker, that together cover every pending record, and for each list the worker's run (one `worker_state`, then the verified `check_pending` folded over the list, a rejection being the fold's `fail`) accepted.  Nothing is assumed about a record being claimed only once or in order | `h6` and `h7` are calls like `h1`…`h5`, inside `driver::check_decls_driver`.  `h8` is the contract of the one generic combinator `pool::parallel_all`, an argument about its control flow (§8.2).  They hold for every install hook, so `--progress` runs are covered |
| `hreads : ReadsAs sinst src chunks` ([def](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Frontend/Source.lean#L36-L40)) | the chunk source hands out `chunks`, each nonempty, then an empty buffer | that the file handle returns the file's bytes in order: trusted.  The read loop itself (`parse_source`) is verified |
| `hmr : ModellerRefines inst m inProcessModeller` ([def](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Frontend/Shape.lean#L675-L680)) | the unverified Rust modeller (`crates/con-ron/src/in_model/`) answers, from related states, what the twin's `inProcessModeller` answers | trusted by design (§6.2).  The twin's modeller calls con-leche's own `generate`, and Theorem 1 proves it exact (`inProcessModeller_refines`) |
| `hpins : decode pinText = ok (.Ok pins)` | the pin list is what the verified decoder read from some text | the theorems hold at every text, as con-leche's hold at every pin list; the binary decodes the embedded `PINS_TEXT` (`decode_embedded`).  `model_exists_embedded`/`no_False_declaration_embedded` state that call itself, at the cost of one extra axiom Aeneas spends on the constant's definition.  `--pins FILE` and `--no-pins` bypass the decoder and are outside the theorems |
| `inModel`, `census` of `h3` and `.Verified` of `h6`, `h8` | the in-process modeller's two switches; verified mode | the switches are parameters, so runs with `CON_LECHE_INMODEL=0` or `CON_LECHE_INMODEL_CENSUS=1` are covered.  A `--trusted` run is outside the theorems |

The prelude's bytes are not a premise: con-leche's `preparePrelude` puts the
prelude's declarations into the checked stream, so soundness holds whatever
the prelude parses to.  The gate `scripts/gen-prelude-lean.sh --check` (§10)
still checks that con-ron ships con-leche's prelude.

§8 lists everything else that must hold for the theorems to describe the
binary: the translator, the compiler, and the hand-written models of what
Aeneas cannot translate.

## 4. The expression representation

The checker's state is one value,
[`AState`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/monad.rs#L315-L336):
the **arena** (the store of all terms), the per-call memo tables and the
per-declaration caches (§5), and the reserved-name pins (§6.1).  Checker
functions take it as `&mut AState`, together with the shared persistent tier
`&PersTier` (§4.4).

### 4.1 Handles

A term is named by a **handle**: one 32-bit word
([layout](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/handle.rs#L4-L15)).

```text
bits 31…28   constructor tag
bit  27      tier            (0 = persistent, 1 = scratch)
bits 26…0    index           into that constructor's array in that tier
```

There are five handle types, one per store
([`EIdx` … `BMIdx`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/handle.rs#L140-L180)):
expressions, names, levels, level lists (a constant's universe arguments),
and binder data (a binder's `PropWhen` annotation).  The expression tags
follow con-leche's constructor order, from `bvar` = 0 to `proj` = 9
([the tags](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/handle.rs#L528-L576)).

Because the tier bit sits above the index, a persistent handle keeps its
bits when the scratch tier comes and goes.  An index has 27 bits, so each
constructor holds at most 2²⁷ nodes per tier; past that, `intern` raises
`Native`, and the twin's intern raises its `native` at the same probe miss.  A handle is its own hash
([`hash64`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/handle.rs#L400-L408)),
and two handles denote the same term only if they are equal (§4.2), so
comparing two terms is comparing two words.

### 4.2 Stores and hash-consing

Each store keeps, per tier, **one array per constructor**, each element a
fixed-size record of handles and scalars; an `app` node is two `u32`s
([`ETables`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/store.rs#L1274-L1295)).
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
handle) and returns the existing handle if there is one
([`EStore::intern`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/store.rs#L4154-L4189)).
It probes the persistent table first, then the scratch table, and appends
only if both miss
([the `app` case](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/store.rs#L4439-L4485)).

Hash-consing is needed for soundness, not only for speed.  The checker
treats equal handles as equal terms and unequal name handles as unequal
names.  If two handles could denote the same term, the checker could take a
branch con-leche would not.  The twin proves the denotation injective on a
well-formed store
([`denoteE_inj`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Arena/WFProofs.lean#L1121-L1122)).

Levels and names are interned the same way, but level *algorithms*
(`simplify`, `leq`, `isEquiv`) run on ordinary `Level` trees read back from
the store, with the readback cached (§5).  Name equality is handle equality.

### 4.3 The two tiers

The arena has two **tiers**, each with its own arrays and cons tables:

* the **persistent tier** holds the parsed file, the prelude, the pins, and
  every term the installed environment keeps;
* the **scratch tier** holds what one declaration's check computes and then
  forgets.

Each declaration is processed inside a **bracket**: `enter_scratch` opens an
empty scratch tier and FREEZES the store — its persistent tables leave it as
the tier every read inside the bracket goes through (§4.4) — and
`drop_scratch` discards the scratch tier, flushes the caches and thaws the
tier back into the store
([the bracket](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/core.rs#L11695-L11717)).
Dropping the tier leaves persistent handles valid, because a persistent node
never points into the scratch tier.

When a declaration is installed, its annotated type and value must outlive
the bracket.  Before the drop, they are **promoted**: copied from scratch to
persistent with a memo, so the copy costs the size of the result, and a
persistent handle promotes to itself
([`arena::promote`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/promote.rs#L1-L40)).
Most of an annotated term is the parsed term, so the copy usually stops
early.

### 4.4 Sharing the persistent tier between workers

The check phase runs on several threads (§6.4).  They share one persistent
tier, read-only, and each owns a scratch tier.  Apart from the pool's own
bookkeeping (two atomic counters and the progress observer's lock), the
workers share nothing mutable.

In Rust, the sharing is a separate parameter, and it is also what makes a
store FROZEN.  At the phase boundary,
[`freeze_tier`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/checker.rs#L1408-L1430)
moves the four stores' persistent tables out into one
[`PersTier`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/store.rs#L1352-L1361)
value whose `frozen` bit is set.  Every persistent read goes to the
`&PersTier` a function is handed when that tier is frozen, and to the store's
own tables otherwise; a worker's store is empty and FROZEN (its scratch tier
open), so every append it makes is a scratch append and none can reach the
shared tier — by construction, not by a guard (task #98-FREEZE removed the
old frozen-tier guard and its `Native` error).  Each phase-A declaration
bracket is the same move in miniature: it freezes the store, checks, and
promotes into the tier it took out before thawing it back.  After the check
phase, `thaw_tier` moves the tables back.  In the twin, the same sharing is a
`ReaderT PersTier` layer on the checker monad.

### 4.5 What is still an `Expr` tree

Two things still use con-leche's tree representation (`kernel::expr`, an
`Arc` per node):

* **the pinned data**: con-leche's own constants that the checker compares
  stream records against (the basis blocks, the axiom pins, the `Nat`
  operation pins).  They are interned into the persistent tier once, at
  startup (§6.1), and no tree is built afterwards while checking;
* **the in-process modeller**, which reads a block back into trees, runs,
  and interns its output (§6.2).

## 5. Caching

Caches exist at two lifetimes, both keyed on handles.  Keying on a handle
alone is sound because an `fvar` node carries its own type, so a handle
determines its typing context.

**Per-call memos**
([`Memos`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/monad.rs#L182-L248)).
Each term walk of con-leche's `ExprOps` (instantiate, abstract, lift, lower,
instantiate level parameters, the bound computations) has its own table,
keyed by `(handle, cursor)`.  A walk's top-level entry clears its table, so
the value being substituted need not be in the key.  The walks also stop
early using the derived column
([the cutoffs](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/expr_ops.rs#L35-L51)):
instantiation returns a subterm unchanged once its loose-bound-variable
bound is low enough, level substitution once it has no level parameters.
Two more tables sit in the same record for their allocation only: the
declaration guards `allLevelParamsDefined` and `constsResolve` thread their
memo as an argument, as con-leche does, and the port parks it in the state
between calls, moving it out and emptying it at each entry
([`take_walk_memo`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/core_state.rs#L525-L572)),
or dropping it outright past 2¹⁶ slots.

**Per-declaration caches**
([`Caches`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/core_state.rs#L304-L351)).
These are con-leche's memo tables:

* `whnfCore`, `whnf`, `infer`, `inferIO` and `annotate`, each `EIdx ↦ EIdx`.
  The inference grades have separate tables, so an answer computed at one
  grade never serves another;
* `defeq` on the ordered pair, storing both `true` and `false` verdicts;
* level and level-list equivalence verdicts;
* a stored constant's type or value, and a recursor rule's right-hand side,
  at a universe instantiation;
* the readbacks of names, levels and level lists (§4.2).

**When they are emptied.**  The per-declaration caches are flushed whole
whenever a bracket closes (§4.3), and again at the start of each install
step, as con-leche's `flushC` is.  A cache entry can name a scratch handle,
so it must go with the tier.  The memos are cleared when a bracket opens and
at every walk's entry.  No table evicts single entries; a table that
reaches
[`CACHE_CAP`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/core_state.rs#L387-L392)
(2²² entries) is emptied whole.

The type checker runs in three **lanes**
([`LANE_*`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/core.rs#L433-L447)),
one per con-leche knot: the full lane uses the caches above, the gated lane
uses none, and the IO lane runs `infer` and `inferIO` unmemoised and uses the
full lane for everything else.

**The hash map.**  The arena's tables use
[`ron::HashMap2`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/hashmap2.rs#L1-L40),
an open-addressed map whose slots carry an epoch stamp, so clearing it is
O(1).  It is proved to implement a finite map in
[`Refine/HashMap2.lean`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Refine/HashMap2.lean).

## 6. The checking pipeline

### 6.1 The stages

The binary's `check_main` calls six verified functions in order, on one
`AState`
([`check_main`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/bin/con-ron.rs#L358-L595)).
They are the six stages of the theorems (§3), `h1`…`h5` and the fold's three steps `h6`…`h8`.

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
   ([`intern_all_pins`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/checker.rs#L1572-L1599)):
   every **pin** is interned into the persistent tier.  A pin is data,
   fixed by con-leche, that the checker compares stream records against:
   the six basis blocks, the standard and trusted axiom statements, and the
   `Nat.div`/`Nat.mod` pin list.  That list is embedded as text
   ([`PINS_TEXT`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/pins_text.rs#L40-L44),
   generated from con-leche by `scripts/gen-pins.sh`) and read by a verified
   decoder
   ([`decode`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/pins_decode.rs#L1325-L1345)).
6. **The fold**: install every declaration, then check them (§6.3, §6.4).

### 6.2 Parsing and the in-process modeller

The parser is in the verified crate
([`frontend/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/frontend/mod.rs#L19-L31)).
The driver reads the file forward in 4 MiB chunks through the
[`HandleSource`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L939-L984)
chunk source and never holds the whole file.  Each line goes through a byte
recogniser ported from con-leche's `Scan/Fast.lean`, the scanner
con-leche's binary actually runs.  Records are interned straight into the
persistent tier, and a table from export index to handle keeps the export's
own sharing.  No expression tree is built.

The parser is the one place where the Rust uses loops rather than recursion,
because a per-byte recursion would overflow the stack.  Aeneas turns each
loop back into a recursive function, which mirrors con-leche's.

The **in-process modeller** turns a mutual or nested inductive block into
ordinary declarations.  The verified parser calls it through a one-method
trait
([`Modeller`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/frontend/types.rs#L243-L271)),
so the extracted parser is quantified over every possible modeller.  The
binary's modeller
([`in_model.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/in_model.rs#L1-L30))
is a Rust port of con-leche's `InModel.generate`: it reads the block back
into trees, runs the generator, and interns the result.  It keeps no state
between calls.  The fold checks its generated records like any other, so a
wrong one is rejected or declined; what the modeller decides is only which
blocks can be accepted at all.

### 6.3 The fold: install, then check

The fold is con-leche's two-phase `checkDecls`
([`arena::checker`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/checker.rs#L1-L40)).

**Phase A, install**
([`annot_step`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/checker.rs#L920-L960)).
For each declaration in order: flush the caches, open a scratch tier,
annotate the header and value and add the constant to the environment,
promote what the environment keeps, drop the tier.  A definition, theorem or
opaque whose value still needs checking becomes a **pending check**: its
value, its position, and the prefix of the environment it may see.

**Phase B, check**
([`check_pending`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/checker.rs#L1247-L1258)).
Each pending check runs in its own bracket against the prefix environment it
recorded.  Nothing it computes survives it.

con-leche proves that its two-phase fold accepts what its one-pass pure
fold accepts.  Theorem 1 proves the same of the twin's fold (§7.3).

### 6.4 The worker pool

Between the phases, the driver freezes the persistent tier (§4.4) and runs
phase B on a pool of threads
([`check_decls_driver`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L523-L619),
[`pool.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L30-L43)).
A worker has its own `AState`
([`worker_state`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/checker.rs#L1462-L1475)):
an empty store that reads the shared tier, its own memos and caches, and a
copy of the pin handles.  It borrows the frozen tier and the installed
environment.  Workers claim pending checks from a shared counter and run
`check_pending` on each.  Results are merged by record index and read in
record order, so the verdict and the first failure reported do not depend on
timing.

The pool is one generic combinator,
[`parallel_all`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L227-L253),
which knows nothing about checking: the driver hands it `worker_state` as
each worker's initial state and `check_pending` on the `k`-th record as the
step.  It is unverified, but everything a worker runs is verified: one
worker's walk over its records is the extracted
[`check_pending_worker`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/checker.rs#L1477-L1495).
If the OS refuses a worker thread, the pool runs on the workers it has (on
the calling thread if none); the verdict does not depend on the count.

### 6.5 Errors

The Rust error type
([`CheckError`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/core_types.rs#L87-L92))
has con-leche's three kinds (`NotImplemented`, `Invalid`, `Internal`) and a
fourth, **`Native`**, for failures con-leche cannot have: a full handle
array.  (The `Nat` operations have no such limit: a result too large for
memory fails like any other allocation.)  The twin has the same fourth kind,
and Theorem 2 says that wherever the Rust raises any of the four, the twin
raises the same kind at the same point.  There is one exception: a numeral
in the export too large for the Rust scanner's `u64` (`IndexOverflow`, a
`Native`), because the twin runs con-leche's own scanner, which reads a `Nat`;
the frontend's error relation names that error value explicitly
([`ScanOverflowErr`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Frontend/Shape.lean#L558-L560)).
The twin's `native`, like a decline, claims nothing about con-leche.  The
driver reports `Native` as a decline, exit 2
([`exit_code`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L156-L170)).

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
  [`denoteE`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Arena/Denote.lean#L181-L206)
  reads a handle back into con-leche's `Expr`, and returns `none` on a
  dangling handle.
* **Well-formedness.**
  [`StoreWF`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Arena/WF.lean#L1-L40)
  says the store is acyclic (by a rank that exists only in the proof), each
  cons table is exactly the inverse of its array, the derived column is
  exact, no scratch entry duplicates a persistent one, and persistent nodes
  have persistent children.  From it follow the injectivity of `denoteE`
  and extension,
  [`Ext st st'`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Arena/Denote.lean#L272-L276):
  every handle that denoted a term still denotes the same term later.

### 7.3 Theorem 1: the twin refines con-leche

[`proof/ConRon/Bridge/`](https://github.com/leanprover/con-ron/tree/master/proof/ConRon/Bridge)
proves that every twin function computes, on denotations, what the
corresponding con-leche function computes.  The per-declaration statement
is
[`Arena.checkDecl_bridge`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Checker/Fold.lean#L111-L126),
and
[`Arena.pooledAccepts_bridge`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Checker/Phased.lean#L175-L186)
lifts it to the whole two-phase fold: the pure fold accepts the denoted
stream at some fuel.  Theorem 1 owns every invariant of the twin's state,
`StoreWF` included.

The store primitives and the type checker are specified by Hoare triples
of Lean's `Std.Do`, in one fixed form, proved with `mvcgen`; the `@[spec]`
lemmas of
[`Bridge/Specs.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Specs.lean#L1-L60)
cover one primitive each:

```lean
⦃fun s => ⌜s = s₀⌝⦄ f args ⦃⇓? r s' => ⌜Post s₀ r s'⌝⦄
```

The precondition only fixes the start state, and `⇓?` means partial
correctness: nothing is claimed when the twin fails.  Many higher-level
statements are instead plain implications over a successful run, like the
graded ones below.

**Spec grades.**  A twin function's statement has one of two grades
([`Bridge/Inductives/Rel.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Inductives/Rel.lean#L184-L225)):

* **pure grade** (`PSpec`), for functions that do not call the type
  checker: invariant `StateOK` (the store is well-formed), frame `PStep`
  (the store only extended, caches and pins untouched), and the statement
  may not mention the caches;
* **core grade** (`CSpec`), for functions that call the type checker:
  invariant `CheckOK` (also: every cache entry is a true con-leche answer at
  some fuel), frame `CoreStep`, and the type checker's own specification as
  a hypothesis.

A pure-grade statement converts to the core grade (`PSpec.toCSpec`), not
the other way.

An example at the pure grade
([`StructParts.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Inductives/StructParts.lean#L168-L213)).
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
`inferIO`, `defeq`, `annotate`) is one statement indexed by fuel,
[`KnotSpec`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Core/Knot.lean#L153-L170),
proved by induction on the fuel in
[`knot_spec`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Bridge/Core/Induction.lean#L73-L80).

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
[`AStateRel₀`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/AbsState.lean#L346-L360)
relates the Rust `AState` to the twin's field by field (store, memos,
caches, pins): the same data, abstracted by functions such as `absEIdx` and,
for hash maps, by the map they represent.
[`AStateInv`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/AbsState.lean#L379-L384)
holds the Rust-only invariants, such as each hash map's own well-formedness.

**The statement.**  A state-threading Rust function is specified by
[`Sim₀`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Shape.lean#L410-L414):
if the Rust returns `Ok r` in state `st'`, the twin returns `A r` in a state
related to `st'`; if the Rust returns a mirrored error, the twin throws the
same kind (`Native` included: the twin raises its `native` at the same point,
task #98-NATIVE).
[`SimRel₀`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Checker/Shape.lean#L221-L225)
is the same with a relation `R r v` in place of the function `A`.

**The judgements.**  Inside proofs, statements take a form in which both
programs are visible in the goal
([`Tactic/Lockstep.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Lockstep.lean#L1-L30)).
The form depends on the shape of the Rust function:

| judgement | Rust shape |
|---|---|
| [`LS`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Lockstep.lean#L162-L166) | returns a result and a new state |
| [`LSR`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Lockstep.lean#L168-L172) | reads the state, may fail |
| `LSV`, `LSW` | reads and cannot fail; writes and cannot fail |
| `LSP` | a Rust-only step with no twin counterpart (a copy, a `u64` decrement) |
| [`LSM`, `LSRM`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Lockstep.lean#L660-L672) | a memoised walk that returns its memo beside the result |

`LS.toSim₀` converts back to the statement form.

**The `lockstep` tactic**
([`lockstep`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Lockstep.lean#L3008-L3009))
steps the two programs together, one bind at a time.  At each Rust bind it
looks up a lemma for the callee, applies it, and continues with the related
results as hypotheses.  It splits a Rust `if` or `match`, and uses the facts
this gives to decide the twin's.  Side goals go to `simp`, `omega` and
`scalar_tac`; it never calls `grind`.  Every alternative it tries runs without
error recovery, so a term that fails to elaborate makes the alternative fail
instead of closing the goal with `sorry`.  When it stops, the goal sits at the
first bind where the two programs differ, or where a lemma is missing.

**The lemma discipline.**  A lemma is found by its Rust callee: tagging it
[`@[lockstep]`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Tactic/Attr.lean#L87-L95)
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
subtypes.  con-leche's `PropWhen`, for instance, carries a proof that its
name list is sorted; the Rust `PropWhen` does not, so it admits values the
twin's type cannot represent.  Where a lemma needs the erased fact, it takes
it as a premise:
[`PropWhenWF`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Abs.lean#L589-L612)
holds of exactly the values the port's smart constructors can build.  The
store relation carries the same fact for every stored binder datum.  An
example of a lemma with such a premise
([`Refine2/ExprOps/Mut.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/ExprOps/Mut.lean#L179-L185)):

```lean
@[lockstep] theorem intern_rebuilt_lam_ls (h : arena.handle.EIdx) (same : Bool)
    (ty b : arena.handle.EIdx) (m : kernel.expr.BinderMeta)
    (hpw : ConRon.Refine.PropWhenWF m.pw) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_lam pers st h same ty b m)
      lst (internRebuiltLam (absEIdx h) same (absEIdx ty) (absEIdx b)
        (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.expr_ops.intern_rebuilt_lam, internRebuiltLam]; lockstep
```

The whole proof is: unfold both definitions, run `lockstep`.

### 7.5 Induction recipes

A walk over a DAG has no structural order, so both sides take fuel, and
their lemmas go by induction.  Two recipes cover most of Theorem 2.

**Fuel induction.**  State an `_aux` lemma over `n` with `fuel.val = n`,
induct on `n`, unfold both sides at `0` and at `m + 1`, and run `lockstep`;
it finds the induction hypothesis in the context.  Then register the general
form with `@[lockstep]`
([`instantiate1_go`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/ExprOps/Mut.lean#L471-L500)):

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
([`inst_pis_from`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/ExprOps/Mut.lean#L992-L1012)):

```lean
theorem inst_pis_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (e : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absOptE a) (arena.expr_ops.inst_pis_from pers st fuel e args i) lst
        (instPis (absU fuel) (absEIdx e) (absEIdxListFrom args i)) := by
  induction n with
  | zero =>
    intro pers st lst fuel e args i hn hrel hinv
    rw [arena.expr_ops.inst_pis_from, listFrom_nil args i (by omega), instPis]
    lockstep
  | succ k ih =>
    intro pers st lst fuel e args i hn hrel hinv
    rw [arena.expr_ops.inst_pis_from, listFrom_cons args i (by omega), instPis]
    lockstep
```

Theorem 1 uses the same cursor recipe (`structPsAt_go_run`, §7.3).

**The type checker.**  The six mutually recursive functions of con-leche's
type checker are tied by fuel on both sides.  Theorem 2 states them as one
relation per fuel, `KnotRel f`, and proves it for every `f` in
[`knot_rel`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Core/Induction.lean#L1169-L1171):
fuel `0` directly, fuel `f + 1` from the six function bodies at fuel `f`.

### 7.6 The composition

[`Capstone.lean`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Capstone.lean#L14-L144)
contains no new mathematics, only glue:

1. **Theorem 2, stage by stage**: each of `h1`…`h5` becomes a twin run from
   the twin's own start state, related at every step.  The sixth stage
   (`h6`…`h8`, assembled by `poolAccepts_intro`) goes through
   [`pool_accepts_refines`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Checker/Phased.lean#L699-L706).
2. **Theorem 1**: the twin runs feed `Arena.pooledAccepts_bridge`, so
   con-leche's pure fold accepts the denoted stream.  Theorem 1 also
   supplies the one twin-side fact the headline relation needs: `StoreWF`
   of the final twin store.
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

`Arc` is used only by tree values: the pinned data and the modeller's terms
(§4.5), the names and levels the checker reads back, and the `PropWhen`
inside a binder datum.  The arena's nodes are handles.

### 8.2 The rest of the trust surface

| trusted | what stands in for it |
|---|---|
| **con-leche's own assumptions**: a set theory `V`, con-leche's soundness proof at the pinned revision, Lean's kernel checking the proofs, and the axioms `propext`, `Classical.choice`, `Quot.sound` | con-leche's own documentation |
| **Aeneas and Charon**: the Lean model is what the Rust means | Nothing; a translator bug is a hole.  The crate stays inside the documented subset (§7.1), and `AENEAS_FINDINGS.md` records what the port found, all of it worked around in the Rust |
| **`rustc`, the Rust standard library and the allocator** | Nothing.  This is the trade the project makes: these instead of Lean's compiler, runtime and GMP.  The mimalloc wrapper in `con-ron-dump` is the only `unsafe` code in the workspace; an allocator can change memory use and time, not a verdict |
| **`overflow-checks = true`** in the [release profile](https://github.com/leanprover/con-ron/blob/master/Cargo.toml#L22-L23) | The model is the checked-arithmetic one.  A build without it would wrap where the model fails |
| **The modeller**, [`crates/con-ron/src/in_model/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/in_model.rs#L1-L30), unverified by design | One hypothesis, `hmr` (§3.1): the Rust modeller answers what the twin's `inProcessModeller` answers, and that one is proved equal to con-leche's `generate`.  The Rust modeller keeps no state between calls.  Every record it generates is checked by the fold, so a wrong one is rejected or declined, never accepted |
| **The driver**, [`driver.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L1-L60) and the binary's `main` | That it calls the verified stages in the order of `h1`…`h8` (§3), on one state from `AState::empty()`, with the pin list the verified decoder reads from the embedded text and `--verified`, and maps the outcome to the exit codes of §2.2.  The read loop is the verified `parse_source`; that the file handle returns the file's bytes in order is `hreads`.  The fold is a [straight line of verified calls](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/driver.rs#L523-L619) (phase A, freeze, phase B as `parallel_all` over two verified closures, thaw), and the progress observer between them holds only shared references |
| **The worker pool**, [`pool.rs`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron/src/pool.rs#L45-L97) | One generic combinator, `parallel_all(n, workers, init, step, after)`, that knows nothing about checking.  Its contract is an argument about its control flow, not a proof: if it returns `Ok`, every index in `0..n` was claimed by some worker, and each worker built its state with `init` once and folded `step` over its claims in claim order, every step `Ok`.  That is `h8`, with the driver's closures (`worker_state`, `check_pending`) written in; the proof reads it as [`ParallelAll`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine2/Checker/Phased.lean#L435-L439) and turns it into one accepting fold per worker.  The contract does not promise that an index is claimed only once, or that a worker's claims increase (the code does both); the proof needs neither.  Results are merged by index, and an accept means every slot is `Ok`.  Nothing is claimed about which worker ran which index: the capstone relates each worker's walk to the twin separately.  Tests check the partition property generically, and that phase B agrees with the one-worker walk and reports the first failure, at every worker count |
| **`Native` errors: partial correctness** | Theorem 2 relates a Rust `Native` to the twin's `native` at the same point, and a twin `native` claims nothing about con-leche, so soundness is unaffected and completeness is not proved.  The arena's sites are the 2²⁷-entry arrays' capacity tests, mirrored by the twin; the one the twin does not mirror is the scanner's `u64` overflow on an oversized numeral (§6.5).  The pin decoder's `Native` is outside Theorem 2: the capstone assumes the embedded pins decode |

Nothing else: no `native_decide`, no `sorry`, and no axiom beyond the three
in §3.

## 9. Performance

Measured with `perf stat -e instructions:u,cycles:u`.  Instruction counts
are the measure of record, because they do not depend on machine load; wall
time and peak memory are secondary.  All runs are `--verified` release
builds with mimalloc, on `lean4export` exports of Lean's `Init` (57 977
declarations) and of Mathlib (691 128).  The table is one snapshot, taken on
2026-09-24: con-ron at `c6e5f220`, con-leche at its pin `78ded4b6`, nanoda
at `4c544ed`.  The two con-ron `Init` instruction counts were re-taken
later that day at `46450386`, after the bulk slot fill and the kept walk
memos (−3.5 %); the other con-ron cells are still from `c6e5f220`.  `Init` wall time is the range of three runs on a shared,
loaded machine; Mathlib was run once per checker, so it has no wall-time
column.

| | `Init` instructions | `Init` wall, peak RSS | Mathlib instructions | Mathlib peak RSS |
|---|---:|---|---:|---:|
| **con-ron**, one worker | 204.62 G | 21.2–21.9 s, 0.57–0.65 GB | 3 880 G | 6.89 GB |
| **con-ron**, eight workers | 206.20 G | 5.4–5.7 s, 0.85–0.87 GB | 3 902 G | 7.44 GB |
| con-leche, one worker | 453.95 G | 41.9–43.4 s, 0.48–0.49 GB | 8 099 G | 8.70 GB |
| nanoda, one worker | 231.25 G | 23.2–24.2 s, 0.36 GB | 6 057 G | 7.08 GB |

Single-threaded, con-ron executes a little under half of con-leche's
instructions on both exports, about 88 % of nanoda's on `Init` and
two thirds of nanoda's on Mathlib.  Eight workers add about 1 % to the
instruction count.  Every con-ron peak is within 3× con-leche's on the same
export.  `scripts/bench-baselines.sh` measures con-ron and nanoda, and
`scripts/corpus.sh` builds the exports; the raw numbers are in DESIGN.md's
task #97-REMEASURE section.

## 10. Keeping the port honest

**Provenance.**  Every item of the verified crate carries a doc line naming
the con-leche source it ports, `/// con-leche: <path>:<a>-<b> <declaration>`,
or `/// con-leche: none — <reason>`
([an example](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/handle.rs#L528-L531)).
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
con-leche's own test fixtures (383 streams) and compares each exit code with
con-leche's recorded one, in both modes and at several worker counts.  This
covers what the proof does not: the driver, the pool and the modeller.  CI
runs it (`.github/workflows/ci.yml`).

**The gates.**  `scripts/gates.sh` runs before every commit
([the steps](https://github.com/leanprover/con-ron/blob/master/scripts/gates.sh#L6-L28)).
It stops at the first failure of: `cargo build` (warnings denied) and
`cargo test`; the style lint; the provenance and twin-line checks; this
document's link check (`scripts/overview-links.sh`) and holes table
(`scripts/holes.sh --check`); the checks that the embedded pin text, the
Rust prelude text and the twin's prelude bytes are con-leche's
(`gen-pins.sh`, `gen-prelude.sh`, `gen-prelude-lean.sh`, each `--check`);
`scripts/extract.sh --check`; and `lake build` of the default targets, which
include `ConRonBridge`, `ConRonRefine2` and `ConRonCapstone`.

**Upstream patches.**  One: the pinned Aeneas builds its Lean library
against an older Lean, and
[`patches/aeneas-433.patch`](https://github.com/leanprover/con-ron/tree/master/patches/aeneas-433.patch)
(375 lines, ten files) makes it build on con-leche's Lean v4.33 and its
Mathlib.  `scripts/setup-aeneas-lean.sh` applies it.  Charon and con-leche
are used unpatched.

## 11. Module map

Rust modules mirror con-leche's files, and function names are con-leche's in
snake case.  Twin files mirror the Rust modules.

**Rust** (`crates/`)

| where | what |
|---|---|
| [`con-ron-core/src/arena/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/arena/mod.rs#L1-L22) | the checker: `handle`, `store` (§4), `monad` (`AState`, the memos), `core_state` (the caches), `expr_ops`, `core` (the type checker), `decl_check`, `inductives/`, `checker` (the fold), `promote`, `pins` |
| [`con-ron-core/src/frontend/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/frontend/mod.rs#L19-L31) | the parser: scanner, record assembly, projection rewrite, ground hoist, prelude, the `Modeller` trait |
| [`con-ron-core/src/kernel/`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/lib.rs#L33-L54) | representation-free types (`Name`, `Level`, `PropWhen`, `CheckError`, `CheckMode`), the pinned data as `Expr` values, `pins_text` and `pins_decode` |
| `con-ron-core/src/ron/` | replacements for the Lean runtime: `nat` (bignum), `hashmap`, `hashmap2`, `ptr` (`Arc`) |
| `con-ron/src/` | unverified: the binary, `driver`, `pool`, the modeller (`in_model/`, `tree/`) |
| `con-ron-dump/` | unverified: the `con-ron-pins/1` reader and writer, the global allocator |

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
