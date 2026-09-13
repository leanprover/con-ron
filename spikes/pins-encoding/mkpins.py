#!/usr/bin/env python3
"""Task #63: extract the raw pin text the other scripts measure on.

`crates/con-ron-core/src/kernel/pins_text.rs` holds the 532 456-byte
`con-ron-pins/1` dump as one `&str` constant, one dump line per Rust source
line and no Rust escapes (checked here).  This writes those bytes verbatim to
`_tmp/a63-pins.txt`, which is what `genbench.py` and `genchunked.py` read
(override with `$A63_PINS`).

Usage: mkpins.py [<out>]
"""
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, "crates/con-ron-core/src/kernel/pins_text.rs")


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        ROOT, "_tmp", "a63-pins.txt")
    lines = open(SRC, "rb").read().split(b"\n")
    i = next(k for k, l in enumerate(lines)
             if l.startswith(b"pub const PINS_TEXT"))
    j = next(k for k, l in enumerate(lines) if l == b'";')
    body = b"\n".join(lines[i + 1:j]) + b"\n"
    assert b"\\" not in body, "the constant has Rust escapes; unescape first"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, "wb").write(body)
    print("%s: %d bytes" % (out, len(body)))


if __name__ == "__main__":
    main()
