#!/usr/bin/env python3
"""Task #63: one line per microbenchmark run (see runbench.sh)."""
import re
import sys

enc, n, sz, rc, s, e, out, err = sys.argv[1:]
txt = open(out).read()


def find(pat, last=False):
    m = re.findall(pat + r" took ([0-9.]+)(ms|s)", txt)
    if not m:
        return None
    v, u = m[-1] if last else m[0]
    return float(v) / (1000 if u == "ms" else 1)


ela, tac, ker = find("elaboration"), find("eqRefl"), find("type checking", True)


def f(x):
    return "-" if x is None else "%.3f" % x


print("%-10s %7s src=%-9s rc=%s wall=%5.1fs data_elab=%ss eqRefl=%ss kernel=%ss"
      % (enc, n, sz + "B", rc, float(e) - float(s), f(ela), f(tac), f(ker)))
for line in [l for l in open(err).read().splitlines()
             if "deprecated" not in l][:4]:
    print("   ! " + line)
