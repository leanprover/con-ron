#!/usr/bin/env python3
"""Task #63, route A(2): a scratch crate holding the pin text as chunked
byte constants, for Charon/Aeneas/Lean measurement.

Usage: genchunked.py <bytes-total> <chunk-size> <crate-dir>
Writes <crate-dir>/{Cargo.toml,src/lib.rs}:  one `const C_i: [u8; N]` per
chunk plus `pub const PINS: &[&[u8]]` listing them, and a trivial consumer so
the constants are reachable.
"""
import os
import sys

# `mkpins.py` writes this file out of the crate's `pins_text.rs`.
SRC = os.environ.get("A63_PINS",
                     os.path.expanduser("~/con-ron/_tmp/a63-pins.txt"))

CARGO = """[workspace]

[package]
name = "a63-chunked"
version = "0.1.0"
edition = "2021"

[lib]
path = "src/lib.rs"
"""

TAIL = """
/// The chunk table.
pub const PINS: &[&[u8]] = &[
%s];

/// Count the newlines of one chunk (index recursion, DESIGN.md 3.4 subset).
pub fn chunk_nl(c: &[u8], j: usize, acc: usize) -> usize {
    if j >= c.len() {
        return acc;
    }
    let b: u8 = c[j];
    let a2: usize = if b == 10u8 { acc + 1 } else { acc };
    chunk_nl(c, j + 1, a2)
}

/// Count the newlines of the whole table.
pub fn total_nl(chunks: &[&[u8]], i: usize, acc: usize) -> usize {
    if i >= chunks.len() {
        return acc;
    }
    let c: &[u8] = chunks[i];
    let a2: usize = chunk_nl(c, 0, acc);
    total_nl(chunks, i + 1, a2)
}

/// The entry point a theorem would speak of.
pub fn pins_nl() -> usize {
    total_nl(PINS, 0, 0)
}
"""


def main():
    total, chunk, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    bs = open(SRC, "rb").read()[:total]
    os.makedirs(out + "/src", exist_ok=True)
    open(out + "/Cargo.toml", "w").write(CARGO)
    parts = [bs[i:i + chunk] for i in range(0, len(bs), chunk)]
    body = ["//! Task #63 spike: the pin text as %d chunks of <= %d bytes.\n"
            % (len(parts), chunk)]
    for k, p in enumerate(parts):
        rows = [", ".join(str(b) for b in p[i:i + 24])
                for i in range(0, len(p), 24)]
        body.append("const C%d: [u8; %d] = [\n    %s,\n];\n"
                    % (k, len(p), ",\n    ".join(rows)))
    body.append(TAIL % "".join("    &C%d,\n" % k for k in range(len(parts))))
    open(out + "/src/lib.rs", "w").write("".join(body))
    print("%d chunks, %d bytes, lib.rs %d bytes"
          % (len(parts), len(bs), os.path.getsize(out + "/src/lib.rs")))


if __name__ == "__main__":
    main()
