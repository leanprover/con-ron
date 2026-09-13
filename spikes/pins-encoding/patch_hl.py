#!/usr/bin/env python3
"""Task #63 route A: fill `Aeneas.Std.Array.make`'s `hl` explicitly.

`Array.make (n : Usize) (init : List a) (hl : init.length = n.val := by simp)`
(`Aeneas/Std/Array/Array.lean:95`).  The default `by simp` is what makes a
byte-chunk constant expensive in Lean and what fails outright above ~256
elements at the generated `maxRecDepth 2048`.  This rewrites the generated
`Funs.lean` so each `Array.make ... [ ... ]` gets an explicit proof, to
measure what the side condition alone costs.

Usage: patch_hl.py <Funs.lean> <out.lean> <tactic>   e.g. "by rfl"
"""
import sys

src, out, tac = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(src).read().splitlines()
res, n = [], 0
for line in lines:
    if line == "    ]":
        res.append("    ] (%s)" % tac)
        n += 1
    else:
        res.append(line)
open(out, "w").write("\n".join(res) + "\n")
print("patched %d Array.make calls with (%s)" % (n, tac))
