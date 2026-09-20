import sys, textwrap

src, src_rel, chunk_s = sys.argv[1], sys.argv[2], sys.argv[3]
CHUNK = int(chunk_s)
data = open(src, "rb").read()
n = len(data)
parts = [data[i:i + CHUNK] for i in range(0, n, CHUNK)]

out = []
out.append('''/-
# `ConRon.Arena.Frontend.PreludeText` — the built-in prelude's bytes
(`ConLeche/Frontend/Prelude.lean:57-62`, task #97e part 2)

**Generated file — do not edit.**  Written by `scripts/gen-prelude-lean.sh`
from con-leche's own committed `%s`, the file its
`builtinPreludeText` reads with `include_str`.
`scripts/gen-prelude-lean.sh --check` is the freshness gate, and
`scripts/gates.sh` runs it.

The module-level citation below covers every item in this file: the whole
module is one con-leche declaration's value (DESIGN.md §3.7, the
`basis_tables.rs` rule of task #22, as `crates/con-ron-core/src/frontend/
prelude_text.rs` does for the Rust port).

**Why a constant in the tree and not `include_str`.**  Task #97e part 1 read
the file through the con-leche lake package directory, which makes this
module's `.olean` depend on a path outside the repository — on a package that
may not be checked out, and on a file no reader of `proof/ConRon/Arena` can
see.  `crates/con-ron-core/src/frontend/prelude_text.rs` settled that question
for the Rust port at task #84 and `kernel/pins_text.rs` before it; this
follows both.  The data is committed here, a script regenerates it from
con-leche, and a gate says the two agree.

**Why %d byte arrays and not one string.**  To be ONE-TO-ONE with the Rust
twin, which splits the bytes into %d chunks of at most %d for the two reasons
its own module note records (Aeneas prints a `&str` constant without escaping
the double quotes inside it, and a single `[u8; %d]` array becomes an
element-by-element `Array.make` that does not elaborate).  Neither reason
binds this file — Lean has string literals and array literals — but a twin
that chunks differently from its original is a twin that has to be read twice,
and the chunking costs nothing: `preludeText` is a 0-ary `def`, so Lean
evaluates the concatenation once per process, exactly as con-leche's own
`builtinPreludeText` parses its `include_str` once.

BYTES and not a `String`, though, because a %d-byte boundary may fall inside a
multi-byte character (the prelude has two non-ASCII entries) and a `String`
chunk could not hold the halves.  `Frontend.parseBytes` takes bytes anyway —
`parseExportD` is `parseBytes` of `String.toUTF8` — so nothing is converted.

The wrapping is byte-exact: the concatenation of the chunks is the ndjson
file, byte for byte, including its final newline, so the parse of it is the
parse con-leche does on that file.
-/
import ConRon.Arena.Frontend.ExportC

namespace ConRon.Arena.Frontend

''' % (src_rel, len(parts), len(parts), CHUNK, n, CHUNK))

for i, part in enumerate(parts):
    body = textwrap.fill(", ".join(str(b) for b in part), width=76,
                         initial_indent="  ", subsequent_indent="  ")
    out.append('/-- con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText\n'
               'Bytes %d..%d of the prelude (the module note says why it is split). -/\n'
               'def P%02d : ByteArray := ⟨#[\n%s]⟩\n\n'
               % (i * CHUNK, i * CHUNK + len(part), i, body))

out.append('''/-- con-leche: none — the Rust twin's `push_chunk`
(`crates/con-ron-core/src/frontend/prelude_text.rs`): the accumulator is
passed by value and returned, so the two read the same way. -/
def pushChunk (out : ByteArray) (c : ByteArray) : ByteArray := out ++ c

/-- con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText
The committed prelude for the pinned toolchain (con-leche's `lean-toolchain`),
verbatim: the `meta` header, the name, level and expression table entries, and
the declaration records of the six pinned basis blocks, `Bool` and `And`.
`Frontend.builtinPreludeE` is the parse of it.

A 0-ary `def`, so the %d chunks are joined once per process — which is what
lets this be a constant where the Rust twin has to be a function. -/
def preludeText : ByteArray :=
  let out : ByteArray := ByteArray.empty
''' % len(parts))
for i in range(len(parts)):
    out.append("  let out := pushChunk out P%02d\n" % i)
out.append("  out\n\nend ConRon.Arena.Frontend\n")

sys.stdout.write("".join(out))
