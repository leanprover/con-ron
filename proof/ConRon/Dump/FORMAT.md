# `con-ron-decls/1` — the `DeclC` dump format

The interchange format between con-leche's Lean frontend and con-ron's Rust
core (DESIGN.md §3.6).  con-leche's own frontend parses an export stream and
produces the `List DeclC` that `ConLeche.Cached.checkDecls` consumes; this
format is that list, written out, so that the Rust core can be exercised on
exactly the declarations the Lean checker sees — no Rust parser needed, and no
frontend rewrite (prelude prepend, `NatOpGround` hoist, projection rewrite,
in-process `_model` generation) reimplemented on the Rust side.

Writer: `ConRon/Dump/Write.lean` (`dumpDecls : List DeclC → String`).
Reader (Lean, the format's validator): `ConRon/Dump/Read.lean`
(`parseDecls : String → Except String (List DeclC)`).
Round-trip harness: `ConRon/Dump/Main.lean` (`lake exe con-ron-dump`).

## 1. Shape

Text, line-oriented, ASCII-only, deterministic (the same `List DeclC` always
produces the same bytes).  Lines are separated by a single `\n`; there is a
trailing `\n` after the last line.  Fields inside a line are separated by a
single space `U+0020`; no other whitespace occurs anywhere.

```
con-ron-decls/1        <- the version header, the whole first line
<record>               <- one per line, in the order described below
...
end <declCount>        <- the footer; <declCount> = the number of `D` records
```

A reader must reject a file whose first line is not exactly
`con-ron-decls/1`, and one whose footer count disagrees with the number of
`D` records seen.  Blank lines are ignored; there are no comments.

## 2. Ids, and the DAG

con-leche's terms are a DAG: `ExprC` (= `ConLeche.Expr`) nodes are shared
heavily — `Kernel/Expr.lean`'s `bvarPool`, the frontend's index tables, and
every `instantiate` that returns a subterm.  Writing the tree out would blow
up exponentially, so shared nodes are written **once** and referred to by an
integer id, in the spirit of `lean4export`'s `<id> #N…` records (the dialect
`ConLeche/Frontend/Scan/Types.lean` recognises).

There are **nine id spaces**, one per record kind, each dense from `0` and
each assigned in the order the records appear:

| kind | record letter | what |
|---|---|---|
| name | `N` | `ConLeche.Name` |
| level | `L` | `ConLeche.Level` |
| propwhen | `W` | `ConLeche.PropWhen` |
| expr | `E` | `ExprC` = `ConLeche.Expr` |
| constval | `V` | `ConLeche.ConstantVal` |
| recrule | `R` | `ConLeche.RecRule` |
| indcaps | `C` | `ConLeche.IndCaps` |
| projtable | `P` | `ConLeche.ProjTable` |
| constinfo | `I` | `ConLeche.ConstantInfo` |

**Invariant (the reader may rely on it, and must check it):** within a kind,
the `n`-th record of that kind carries id `n`, and every id a record mentions
is *strictly smaller* than the id of the record that mentions it (for a
reference into another kind: already defined at that point in the file).  So
a reader is a single forward pass that pushes each decoded value onto a
`Vec` per kind and indexes into those vectors — no fixups, no cycles, no
forward references.  This is what the Rust side wants.

`N`, `L`, `W` and `E` records are **interned**: the writer keeps a hash map
from value to id, so structurally equal subterms collapse to one record.
`V`, `R`, `C`, `P` and `I` records are not interned (each occurs once in
practice); they are emitted immediately before the record that uses them.

## 3. Scalars

* `<nat>` — a natural number in decimal, no sign, no leading zeros except
  for `0` itself.  Unbounded: `Literal.natVal` can be a bignum.
* `<bool>` — `0` (false) or `1` (true).
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

Below, `<name>`, `<level>`, `<pw>`, `<expr>`, `<cv>`, `<rule>`, `<caps>`,
`<tbl>`, `<ci>` are ids into the corresponding space, written in decimal.
`<k>` is always a list length, immediately followed by that many fields.

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

`fvar` never occurs in a parsed declaration (`checkConstantValC` rejects one),
but it is a constructor of the type and is representable here.

### Constant values — `ConLeche/Kernel/Env.lean:197`

```
V <id> <name> <k> <name>* <expr>  -- ⟨name, levelParams, type⟩
```

### Recursor rules — `ConLeche/Kernel/Env.lean:255`

```
R <id> <name> <nat> <nat> <fire> <expr> <bool> <bool> <bool>
       ctor    nfields ctorParams   rhs   k     eta   paramsBlind

<fire> ::= i                          -- RecRuleFire.inert
         | p                          -- RecRuleFire.plain
         | n <k> <level>* <k> <expr>* -- RecRuleFire.nested lvls pins
```

All of `ctorParams`, `fire`, `k`, `eta` and `paramsBlind` are *install*-computed;
the parse placeholders are `0`, `.inert`, `false`, `false`, `false`.  A dump
taken before `checkDecls` therefore always carries the placeholders — but the
format writes them out, because a dump is a `List DeclC` and nothing else is
allowed to know that.

### Inductive capabilities — `ConLeche/Kernel/Env.lean:359`

```
C <id> <bool> <name> <nat> <nat> <bool> <nat> <bool> <pw>
       eta  etaCtor etaParams etaFields unitlike unitParams ruleK sortZ
```

### Projection tables — `ConLeche/Kernel/Env.lean:397`

```
P <id> <name> <k> <name>* <nat> <name> <nat> <level> <k> <expr>* <k> <level>* <nat>
       structName levelParams numParams ctor numFields structSort bodies guards off
```

`bodies` is an `Array Expr` in Lean and is written as a plain counted list.

### Constant infos — `ConLeche/Kernel/Env.lean:471`

```
I <id> a <cv>                     -- axiomInfo
I <id> d <cv> <expr> <hint>       -- defnInfo val value hint
I <id> t <cv> <expr>              -- thmInfo val value
I <id> i <cv> <caps>              -- indInfo val caps
I <id> c <cv> <nat> <nat>         -- ctorInfo val numParams numFields
I <id> r <cv> <nat> <nat> <k> <rule>*
                                  -- recInfo val majorIdx rulePrefix rules
I <id> p <tbl>                    -- projInfo tbl

<hint> ::= o                      -- ReducibilityHint.opaque
         | b                      -- ReducibilityHint.abbrev
         | r <nat>                -- ReducibilityHint.regular height
```

### Declarations — `ConLeche/Cached/ParsedC.lean:55`

`D` records carry **no id**: they are the payload, and their order is the
order of the `List DeclC`, which is the order `checkDecls` folds them in.

```
D a <cv>                          -- axiomDecl val
D d <cv> <expr> <hint>            -- defnDecl val value hint
D t <cv> <expr>                   -- thmDecl val value
D o <cv> <expr>                   -- opaqueDecl val value
D b <basis>                       -- basisDecl kind
D i <nat> <k> <ci>*               -- indDecl block numParams  (numParams first)

<basis> ::= eq | nat | punit | empty | false | quot
```

## 5. Emission order

The writer walks the declaration list in order and, for each declaration, its
fields in constructor order, emitting a record for every value it has not
emitted before, children first.  The `ExprC` walk is an explicit worklist, not
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
6. **The install-computed `RecRule` fields are placeholders in a dump.**
