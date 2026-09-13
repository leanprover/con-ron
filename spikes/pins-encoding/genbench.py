#!/usr/bin/env python3
"""Task #63: generate Lean kernel-cost microbenchmarks over a byte prefix.

Usage: genbench.py <encoding> <nbytes> <outfile>
Encodings: listu8, listu8rec, listnat, str, natlit
Each file defines the data, a trivial decoder (count 0x0a bytes) and one
theorem closed by `rfl`, so the kernel must reduce it.
"""
import os
import sys

# `mkpins.py` writes this file out of the crate's `pins_text.rs`.
SRC = os.environ.get("A63_PINS",
                     os.path.expanduser("~/con-ron/_tmp/a63-pins.txt"))


def prefix(n):
    return open(SRC, "rb").read()[:n]


def lst(bs, per=32):
    out = []
    for i in range(0, len(bs), per):
        out.append(", ".join(str(b) for b in bs[i:i + per]))
    return ",\n  ".join(out)


REC = """
noncomputable def cnt (l : List %s) : Nat :=
  List.rec 0 (fun b _ ih => (if b == 10 then 1 else 0) + ih) l
"""


def gen(enc, n):
    bs = prefix(n)
    k = bs.count(10)
    h = ["set_option maxRecDepth 4000000\nset_option maxHeartbeats 0\nset_option profiler true\nset_option profiler.threshold 10\n"]
    if enc == "listu8":
        h.append("def data : List UInt8 := [\n  %s]\n" % lst(bs))
        h.append("""
def cnt : List UInt8 -> Nat
  | [] => 0
  | b :: r => (if b == 10 then 1 else 0) + cnt r

theorem t : cnt data = %d := by rfl
""" % k)
    elif enc == "listu8rec":
        h.append("def data : List UInt8 := [\n  %s]\n" % lst(bs))
        h.append(REC % "UInt8")
        h.append("\ntheorem t : cnt data = %d := by rfl\n" % k)
    elif enc == "listnat":
        h.append("def data : List Nat := [\n  %s]\n" % lst(bs))
        h.append(REC % "Nat")
        h.append("\ntheorem t : cnt data = %d := by rfl\n" % k)
    elif enc == "str":
        txt = (bs.decode("utf-8").replace("\\", "\\\\").replace('"', '\\"')
               .replace("\n", "\\n"))
        h.append('def data : String := "%s"\n' % txt)
        h.append("""
noncomputable def cntc (l : List Char) : Nat :=
  List.rec 0 (fun c _ ih => (if c == '\\n' then 1 else 0) + ih) l
""")
        h.append("\ntheorem t : cntc data.data = %d := by rfl\n" % k)
    elif enc == "natlit":
        v = int.from_bytes(bs, "little")
        h.append("def data : Nat := 0x%x\n" % v)
        h.append("""
def cnt : Nat -> Nat -> Nat
  | 0, _ => 0
  | Nat.succ f, m =>
      if m == 0 then 0 else (if m %% 256 == 10 then 1 else 0) + cnt f (m / 256)

theorem t : cnt %d data = %d := by rfl
""" % (n + 1, k))
    else:
        raise SystemExit("unknown encoding " + enc)
    return "".join(h)


if __name__ == "__main__":
    enc, n, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    open(out, "w").write(gen(enc, n))
