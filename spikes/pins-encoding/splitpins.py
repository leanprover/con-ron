#!/usr/bin/env python3
"""Task #63, route B: split one emitted pin-table function into parts.

`lake exe con-ron-gen-tables --pins <i> <out>` writes ONE
`nat_op_pins_v<i>() -> Vec<Expr>` with one `let` per interned DAG node
(20 183 of them for v4.33.0), which task #22 measured Charon OOM on.  This
splits that body into `part_<k>` functions of at most <nodes> node-`let`s
each, threading the built nodes through an explicit arena so the DAG sharing
is preserved exactly:

    pub struct Arena { ns: Vec<Name>, us: Vec<Level>, es: Vec<Expr> }
    fn part_0(mut a: Arena) -> Arena { ...; a.es.push(e0); ...; a }

A reference to a node built in an earlier part becomes `&a.es[K]`; node `K`
of a kind always sits at index `K` of its vector, because the emitter numbers
them in emission order.

Usage: splitpins.py <pins0.rs> <nodes-per-part> <out.rs>
"""
import re
import sys

NODE = re.compile(r"^    let (e|n|u)(\d+) = (.*)$")
KIND = {"e": ("es", "Expr"), "n": ("ns", "Name"), "u": ("us", "Level")}
REF = re.compile(r"&(e|n|u)(\d+)\b")

HEAD = """//! con-leche: none — task-#63 route-B spike: the v4.33.0 pin table,
//! split into %d functions of <= %d interned nodes each.

use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::expr::Literal;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::ron::nat;

/// The node arena: one vector per id space, indexed by the emitter's own
/// node number.
pub struct Arena {
    pub ns: Vec<Name>,
    pub us: Vec<Level>,
    pub es: Vec<Expr>,
}
"""


def main():
    src, per, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    lines = open(src).read().splitlines()
    i = next(k for k, l in enumerate(lines) if l.startswith("pub fn "))
    body = lines[i + 1:]
    while body and body[-1] in ("}", ""):
        body.pop()

    parts, cur, defined, ndefs, done = [], [], set(), 0, set()

    def close():
        nonlocal cur, defined, ndefs
        if cur:
            parts.append((cur, sorted(defined, key=lambda d: (d[0], d[1]))))
            done.update(defined)
        cur, defined, ndefs = [], set(), 0

    for line in body:
        m = NODE.match(line)
        cur.append(line)
        if m:
            defined.add((m.group(1), int(m.group(2))))
            ndefs += 1
            if ndefs >= per:
                close()
    tail = cur[:]
    close()

    # rewrite references, per part, against what earlier parts hold
    text = [HEAD % (len(parts), per)]
    seen = set()
    for k, (ls, defs) in enumerate(parts):
        mine = set(defs)

        def fix(l, mine=mine):
            return REF.sub(
                lambda m: ("&%s%s" % (m.group(1), m.group(2)))
                if (m.group(1), int(m.group(2))) in mine
                else "&a.%s[%s]" % (KIND[m.group(1)][0], m.group(2)), l)

        last = (k == len(parts) - 1)
        if last:
            text.append("\n/// Nodes %d..: the table's tail, and the result.\n"
                        "pub fn part_%d(mut a: Arena) -> Vec<Expr> {" % (k, k))
        else:
            text.append("\n/// One slice of the node DAG.\n"
                        "pub fn part_%d(mut a: Arena) -> Arena {" % k)
        for l in ls:
            text.append(fix(l))
        if last:
            text.append("}")
        else:
            for (kd, num) in defs:
                text.append("    a.%s.push(%s%d);" % (KIND[kd][0], kd, num))
            text.append("    a")
            text.append("}")
        seen |= mine

    text.append("""
/// The whole table, as %d calls.
pub fn nat_op_pins_v0() -> Vec<Expr> {
    let a0: Arena = Arena { ns: Vec::new(), us: Vec::new(), es: Vec::new() };""" % len(parts))
    for k in range(len(parts) - 1):
        text.append("    let a%d: Arena = part_%d(a%d);" % (k + 1, k, k))
    text.append("    part_%d(a%d)" % (len(parts) - 1, len(parts) - 1))
    text.append("}")
    open(out, "w").write("\n".join(text) + "\n")
    print("%d parts, %d lines" % (len(parts), len("\n".join(text).splitlines())))


if __name__ == "__main__":
    main()
