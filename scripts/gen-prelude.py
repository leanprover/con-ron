import sys, textwrap

src, src_rel, chunk_s = sys.argv[1], sys.argv[2], sys.argv[3]
CHUNK = int(chunk_s)
data = open(src, "rb").read()
n = len(data)
parts = [data[i:i + CHUNK] for i in range(0, n, CHUNK)]

out = []
out.append('''//! The embedded lean4export text of con-leche's built-in prelude
//! (`ConLeche/Frontend/Prelude.lean:57-62`, task #84).
//!
//! con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText
//!
//! **Generated file — do not edit.**  Written by `scripts/gen-prelude.sh`
//! from con-leche's own committed `%s`, the file its
//! `builtinPreludeText` reads with `include_str`.
//! `scripts/gen-prelude.sh --check` is the freshness gate, and
//! `scripts/gates.sh` runs it.
//!
//! The module-level citation above covers every item in the file: the whole
//! module is one Lean declaration's value (DESIGN.md §3.7, the
//! `basis_tables.rs` rule of task #22, as `kernel/pins_text.rs` does).
//!
//! **Why a constant in the crate and not `include_str!`.**  The unverified
//! port read the file out of `vendor/` at compile time, which makes the
//! verified crate's build depend on a path outside itself and hides the data
//! from anyone reading `crates/con-ron-core`.  `kernel/pins_text.rs` settled
//! that question at task #43; this follows it.
//!
//! **Why %d byte arrays and not one `&str`.**  Both of the obvious shapes
//! fail, and task #84 measured each:
//!
//! * a `&str` constant, which is what `kernel/pins_text.rs` uses, is printed
//!   by Aeneas as `toStr "..."` **without escaping a double quote inside it**
//!   (AENEAS_FINDINGS §2.1's F17).  The pin dump's format happens to contain
//!   no quote; an ndjson stream is nothing but quotes, and the Lean that came
//!   out did not parse.
//! * one `[u8; %d]` array, the other half of task #43's measurement, is
//!   printed as an element-by-element `Array.make` — and Lean elaborating a
//!   %d-element one **times out** at a million heartbeats (four minutes,
//!   then `synthesize pending MVars`).  The largest array the rest of the
//!   model has is 72 elements.
//!
//! So the bytes are split into %d chunks of at most %d, which elaborate in
//! the ordinary way, and `prelude_text()` concatenates them.  The
//! concatenation is `O(n)` and runs once per process.

''' % (src_rel, len(parts), n, n, len(parts), CHUNK))

for i, part in enumerate(parts):
    body = textwrap.fill(", ".join(str(b) for b in part), width=76,
                         initial_indent="    ", subsequent_indent="    ")
    out.append('/// con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText\n'
               '/// Bytes %d..%d of the prelude (the module note says why it is split).\n'
               'const P%02d: [u8; %d] = [\n%s,\n];\n\n'
               % (i * CHUNK, i * CHUNK + len(part), i, len(part), body))

out.append('''/// con-leche: none — `Vec::extend_from_slice` is in the subset, but the
/// accumulator is passed by value and returned (DESIGN.md §3.4 reserves
/// `&mut` for the state parameter).
fn push_chunk(out: Vec<u8>, c: &[u8]) -> Vec<u8> {
    let mut v = out;
    v.extend_from_slice(c);
    v
}

/// con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText
/// The committed prelude for the pinned toolchain (con-leche's
/// `lean-toolchain`), verbatim: the `meta` header, the name, level and
/// expression table entries, and the declaration records of the six pinned
/// basis blocks, `Bool` and `And`.  `frontend::prelude::builtin_prelude_e`
/// is the parse of it.
///
/// A function and not a `const`, because the bytes are %d chunks (the module
/// note says why) and joining them is a computation.  It runs once per
/// process, at the driver's first step.
pub fn prelude_text() -> Vec<u8> {
    let out: Vec<u8> = Vec::with_capacity(%d);
''' % (len(parts), n))
for i in range(len(parts)):
    out.append("    let out = push_chunk(out, &P%02d);\n" % i)
out.append("    out\n}\n")

sys.stdout.write("".join(out))
