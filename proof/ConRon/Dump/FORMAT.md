# `con-ron-pins/1` — the `Nat`-operation pin dump format

con-leche's `natOpPinSets` (`ConLeche/Kernel/NatOpPins.lean:61`), written out
as text.  DESIGN.md §3.6 and task #31: encoding those pin sets as *generated
Rust* is 26 512 `Expr` nodes that Charon OOMs on, and the list is a **hint
list** — every pin is re-checked by `isDefEq` against the stream's own stored
value and every certificate proof is kernel-checked against the hand-pinned
`divModCertStmts` — so the pins travel as data rather than as code.  Task #43
then embedded exactly these bytes *inside* the verified core
(`kernel::pins_text::PINS_TEXT`), where a verified decoder reads them, and left
the file route as a test override.

| | |
|---|---|
| Lean writer and reader | `ConRon/Dump/Pins.lean` (`dumpPins`, `parsePins`) |
| Round-trip harness | `lake exe con-ron-dump-pins` (the same file's `main`) |
| Rust reader / writer | `crates/con-ron-dump/src/lib.rs` (`parse_pins`), `write.rs` (`dump_pins`) |
| Verified decoder | `crates/con-ron-core/src/kernel/pins_decode.rs`, proved against `parsePins` in `proof/ConRon/Refine/Pins*.lean` |
| Who produces the bytes | `scripts/gen-pins.sh` (into the core's embedded constant; `--check` is a gate) |
| Who consumes a file | `con-ron --pins FILE`, a test override |

Until task #80 a **sibling format, `con-ron-decls/1`**, carried con-leche's
parsed `List DeclC` (task #10) so that the Rust *checker* could be exercised
without a Rust frontend.  `scripts/diff-e2e.sh` runs the whole binary on every
fixture's raw export against con-leche's own pinned expectations, which
subsumes that seam, so the declaration dump was retired; §§1-4 below are the
record grammar the two formats shared.

## 1. Shape

Text, line-oriented, ASCII-only, deterministic (the same `List NatOpPinSet`
always produces the same bytes).  Lines are separated by a single `\n`; there
is a trailing `\n` after the last line.  Fields inside a line are separated by
a single space `U+0020`; no other whitespace occurs anywhere.

```
con-ron-pins/1         <- the version header, the whole first line
<record>               <- one per line, in the order described below
...
end <setCount>         <- the footer; <setCount> = the number of `S` records
```

A reader must reject a file whose first line is not exactly `con-ron-pins/1`,
and one whose footer count disagrees with the number of `S` records seen.
Blank lines are ignored; there are no comments.

## 2. Ids, and the DAG

con-leche's terms are a DAG: `ExprC` (= `ConLeche.Expr`) nodes are shared
heavily — `Kernel/Expr.lean`'s `bvarPool` and every `instantiate` that returns
a subterm.  Writing the tree out would blow up exponentially (as a tree one
pin variant is 5.1 M nodes), so shared nodes are written **once** and referred
to by an integer id, in the spirit of `lean4export`'s `<id> #N…` records.

There are **four id spaces**, one per interned record kind, each dense from
`0` and each assigned in the order the records appear:

| kind | record letter | what |
|---|---|---|
| name | `N` | `ConLeche.Name` |
| level | `L` | `ConLeche.Level` |
| propwhen | `W` | `ConLeche.PropWhen` |
| expr | `E` | `ExprC` = `ConLeche.Expr` |

**Invariant (the reader may rely on it, and must check it):** within a kind,
the `n`-th record of that kind carries id `n`, and every id a record mentions
is *strictly smaller* than the id of the record that mentions it (for a
reference into another kind: already defined at that point in the file).  So
a reader is a single forward pass that pushes each decoded value onto a
`Vec` per kind and indexes into those vectors — no fixups, no cycles, no
forward references.  This is what the Rust side wants.

All four record kinds are **interned**: the writer keeps a hash map from value
to id, so structurally equal subterms collapse to one record.  The `S` payload
records are not interned and carry no id (§4).

## 3. Scalars

* `<nat>` — a natural number in decimal, no sign, no leading zeros except
  for `0` itself.  Unbounded: `Literal.natVal` can be a bignum.
* `<string>` — **two** fields: `<len> <text>`, where `<len>` is the number of
  Unicode *code points* and `<text>` is the escaped form below.  The length
  is redundant (the escape is self-delimiting) and is there so that the Rust
  reader, which stores strings as `Vec<u32>` code points (DESIGN.md §3.3), can
  size its vector up front and cross-check its decode.  `<text>` is empty
  exactly when `<len>` is `0`, and the line then ends in a space.

### String escaping

Every code point `c` is written as

* the literal ASCII byte, if `0x21 ≤ c ≤ 0x7E` and `c ≠ 0x5C` (backslash);
* `\` followed by `c` in **lowercase hexadecimal, no leading zeros**,
  followed by `;`, otherwise.

So space is `\20;`, newline `\a;`, backslash `\5c;`, `é` is `\e9;` and `∀` is
`\2200;`.  There is exactly one escape form and it is unambiguous: a literal
`;` is never preceded by an unescaped `\`, because `\` itself is always
escaped.  **Every** code point round-trips, `U+0000` included.  The admissible
range is Lean's `Char.isValidChar` — below `U+D800`, or above `U+DFFF` and
below `U+110000`; the surrogate range is not a code point on either side and a
reader rejects an escape naming one.  Text is pure ASCII, so a Rust reader
needs no UTF-8 decoder: it reads bytes and produces `u32`s.

## 4. The records

Below, `<name>`, `<level>`, `<pw>`, `<expr>` are ids into the corresponding
space, written in decimal.  `<k>` is always a list length, immediately
followed by that many fields.

### Names — `ConLeche/Kernel/Name.lean`

```
N <id> a                          -- Name.anonymous
N <id> s <name> <len> <text>      -- Name.str  pre s
N <id> n <name> <nat>             -- Name.num  pre n
```

The cached `hashData` computed field is **not** written: it is a function of
the value and is recomputed by the constructors on read.

### Levels — `ConLeche/Kernel/Expr.lean:39`

```
L <id> z                          -- Level.zero
L <id> s <level>                  -- Level.succ
L <id> m <level> <level>          -- Level.max
L <id> i <level> <level>          -- Level.imax
L <id> p <name>                   -- Level.param
```

`Level.hashData` is a computed field; not written.

### `PropWhen` — `ConLeche/Kernel/PropWhen.lean`

The datum's representation is `private`; the dump goes through its public
API, `PropWhen.toList?` (`none` at `never`, `some ps` otherwise) and the
smart constructor `PropWhen.ifAllZero`.

```
W <id> n                          -- PropWhen.never
W <id> z <k> <name>*              -- PropWhen.ifAllZero [names]
```

The list `ps` is already canonical (sorted by `Name.cmp`, duplicate-free)
when it comes out of `toList`, and `ifAllZero` re-normalises on read, so the
round trip is the identity (`PropWhen.ifAllZero_toList`).  A Rust reader must
either keep the list as given or re-sort it with the same order.

### Expressions — `ConLeche/Kernel/Expr.lean:343`

```
E <id> b <nat>                    -- bvar i
E <id> v <nat> <expr>             -- fvar idx type
E <id> s <level>                  -- sort u
E <id> c <name> <k> <level>*      -- const n us
E <id> a <expr> <expr>            -- app f a
E <id> l <expr> <expr> <pw>       -- lam type body ⟨pw⟩
E <id> f <expr> <expr> <pw>       -- forallE type body ⟨pw⟩
E <id> t <expr> <expr> <expr>     -- letE type value body
E <id> n <nat>                    -- lit (.natVal n)
E <id> g <len> <text>             -- lit (.strVal s)
E <id> p <name> <nat> <expr>      -- proj structName idx e
```

`BinderMeta` has exactly one field, `pw`, so it is written as that field and
nothing else.  The packed `data` word (32-bit hash ǀ `bvarB` ǀ `fvarB` ǀ
`hasLP`) is a `@[computed_field]`: a function of the value, recomputed by the
constructors, never written.  A Rust reader **must** recompute it with
con-leche's own recurrences (`packData`, `satSucc`, `satPred`, `hash32`) —
except for the hash bits, which the port computes with its own `mixHash`
(DESIGN.md task #3, note 6), so the two hash *values* differ by design and
nothing may compare them.

`fvar` does not occur in a pin blob, but it is a constructor of the type and
is representable here.

### Pin variants — `ConLeche/Kernel/NatOpPinSet.lean:30`

```
S <len> <text> <expr> <expr> <expr> <expr> <expr> <expr> <expr> <expr>
        toolchain  div    mod    gcd   land   lor    xor    shl    shr
  <k> <expr>* <k> <expr>* <k> <expr>* <k> <expr>* <k> <expr>* <k> <expr>* <k> <expr>* <k> <expr>*
  divProofs   modProofs   gcdProofs   landProofs  lorProofs   xorProofs   shlProofs   shrProofs
```

(one line, the wrap above is presentation).  `S` records carry **no id**: the
record *is* the payload, and its position in the file is its position in
`natOpPinSets`, which is the order `checkDivModPinLoop` tries the variants in.
The eight pins come first and the eight counted proof lists follow, in the
field order of the structure; `<len> <text>` is the toolchain string (§3),
which the decline message names and nothing else reads.

## 5. Emission order

The writer walks the pin list in order and, for each variant, its fields in
constructor order, emitting a record for every value it has not emitted
before, children first.  The `ExprC` walk is an explicit worklist, not
recursion: con-leche's terms are deep enough (spines of tens of thousands of
`app` nodes) that a recursive writer would overflow the stack.

## 6. What a Rust reader has to get right

1. **Ids are per kind and dense**; push, never insert.
2. **Recompute every computed field** — `Name.hashData`, `Level.hashData`,
   `Expr.data` — from the children, with con-leche's recurrences for the
   range/flag bits, and the port's own `mixHash` for the hash bits.
3. **`Nat` fields are unbounded** (`Literal.natVal`, `Name.num`'s index in
   principle); `ron::Nat` is the target for the first, a `u64` for the
   indices (DESIGN.md §3.3, an overflow being a Rust-side failure).
4. **Strings are code points, not bytes.**
5. **`PropWhen` arrives canonical**; keep it so.
6. **Keep the sharing.**  A byte-identical re-dump does not prove it (the
   writer interns by value, so it would collapse a tree expansion back into
   the same bytes): count the distinct heap nodes the parsed variants reach
   and compare with the file's record counts (`con_ron_dump::dag`).

## 7. The census, at con-leche 3e004805

| | |
|---|---|
| `S` records | 3 (`v4.33.0`, `v4.34.0-rc2`, `nightly-2026-09-10`) |
| `N` / `L` / `W` / `E` records | 200 / 3 / 1 / 26 512 |
| proof blobs per variant | 3 div, 3 mod, 2 each for `gcd`/`land`/`lor`/`xor`/`shiftLeft`/`shiftRight` |
| lines / bytes | 26 721 / 532 456 |
