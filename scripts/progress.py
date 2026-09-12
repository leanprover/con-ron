#!/usr/bin/env python3
"""scripts/progress.py — the quantitative progress report (DESIGN.md §7).

Three numbers per con-leche implementation file, in *Lean lines*:

  to translate   lines inside definitional top-level blocks (`def`, `abbrev`,
                 `inductive`, `structure`, `class`, `instance`, `opaque` — not
                 `theorem`s, not proof-only helpers we cannot tell apart, so this
                 slightly overcounts what must be ported);
  translated     of those, the lines some Rust item cites
                 (`/// con-leche: path:A-B decl`, scripts/provenance.py);
  verified       of those, the lines cited by a Rust item `f` in module `m`
                 for which `proof/ConRon/Refine/<M>.lean` states
                 `theorem f_refines` (the §3.5 exact-result lemma).

Two groups: the verified core (`ConLeche/Kernel`, `ConLeche/Cached`) and the
cherries (`ConLeche/Frontend` without the parser's equivalence proofs,
`Main.lean`).  Plus the size of the Rust, the generated Lean and the proofs.

Usage: scripts/progress.py [--md | --summary]   (run from anywhere in the repo)
`--summary` prints only the totals (what scripts/gates.sh shows).
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import provenance as P  # noqa: E402

REPO = P.REPO
CORE_GLOBS = ["ConLeche/Kernel", "ConLeche/Cached"]
CHERRY_GLOBS = ["ConLeche/Frontend", "Main.lean"]
CHERRY_EXCLUDE = re.compile(r"ConLeche/Frontend/Scan/Equiv")
# Not executed by the shipped path, so not to be ported: elaboration-time
# meta code and the proof-tier mode variants of the core bodies (census,
# task #1; DESIGN.md §4).
CORE_EXCLUDE = re.compile(r"ConLeche/Kernel/(BasisGen|CoreGated|CheckerGated|CoreIO)\.lean$")
RUST_ROOTS = ["crates/con-ron-core/src"]
REFINE_DIR = "proof/ConRon/Refine"
GENERATED_DIR = "proof/ConRon/Generated"


def lean_files(globs):
    out = []
    for sub in globs:
        base = os.path.join(REPO, P.CON_LECHE, sub)
        if os.path.isfile(base):
            out.append(sub)
            continue
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(dirnames)
            for fn in sorted(filenames):
                if fn.endswith(".lean"):
                    full = os.path.join(dirpath, fn)
                    out.append(os.path.relpath(full, os.path.join(REPO, P.CON_LECHE)))
    return sorted(set(out))


def definitional_lines(lines):
    """Set of 1-based line numbers inside definitional top-level blocks."""
    got = set()
    for lineno, kw, _name in P.top_level_decls(lines):
        if kw not in P.DEFINITIONAL:
            continue
        a, b = P.extend_block(lines, lineno - 1)
        got.update(range(a, b + 1))
    return got


def refine_lemmas():
    """{(ModuleLower, fn)} for every `theorem <fn>_refines` in Refine/<Module>.lean."""
    out = set()
    d = os.path.join(REPO, REFINE_DIR)
    if not os.path.isdir(d):
        return out
    for fn in os.listdir(d):
        if not fn.endswith(".lean"):
            continue
        module = fn[:-5].lower().replace("_", "")
        text = open(os.path.join(d, fn), encoding="utf-8").read()
        for m in re.finditer(r"^\s*theorem\s+([A-Za-z_][A-Za-z0-9_]*)_refines\b", text, re.M):
            out.add((module, m.group(1)))
    return out


def rust_module_of(item):
    base = os.path.basename(item.file)
    return base[:-3].lower().replace("_", "") if base.endswith(".rs") else base


def count_lines(paths):
    n = 0
    for p in paths:
        try:
            with open(p, encoding="utf-8") as f:
                n += sum(1 for _ in f)
        except OSError:
            pass
    return n


def walk(root, ext):
    out = []
    for dirpath, _d, files in os.walk(os.path.join(REPO, root)):
        for fn in files:
            if fn.endswith(ext):
                out.append(os.path.join(dirpath, fn))
    return sorted(out)


def main(argv):
    md = "--md" in argv
    summary = "--summary" in argv
    items, cites, _malformed, _markers = P.collect([os.path.join(REPO, r) for r in RUST_ROOTS])
    lemmas = refine_lemmas()

    translated = {}  # path -> set(lines)
    verified = {}
    for it in items:
        has_lemma = (rust_module_of(it), it.name()) in lemmas
        for c in it.cites:
            if c is None:
                continue
            translated.setdefault(c.path, set()).update(range(c.a, c.b + 1))
            if has_lemma:
                verified.setdefault(c.path, set()).update(range(c.a, c.b + 1))

    def report(title, globs, exclude=None):
        rows = []
        tot = [0, 0, 0, 0]
        for path in lean_files(globs):
            if exclude and exclude.search(path):
                continue
            full = os.path.join(REPO, P.CON_LECHE, path)
            lines = open(full, encoding="utf-8").read().split("\n")
            defl = definitional_lines(lines)
            tr = translated.get(path, set()) & defl
            ve = verified.get(path, set()) & defl
            rows.append((path, len(lines), len(defl), len(tr), len(ve)))
            tot[0] += len(lines); tot[1] += len(defl); tot[2] += len(tr); tot[3] += len(ve)
        rows.sort(key=lambda r: -r[2])
        pct = lambda a, b: ("%3d%%" % (100 * a // b)) if b else "  -"
        if summary:
            print("%-58s to translate %6d  translated %6d (%s)  verified %6d (%s)"
                  % (title, tot[1], tot[2], pct(tot[2], tot[1]).strip(), tot[3], pct(tot[3], tot[1]).strip()))
        elif md:
            print("### %s\n" % title)
            print("| file | raw | to translate | translated | verified |")
            print("|---|---:|---:|---:|---:|")
            for p, raw, d, t, v in rows:
                if d == 0:
                    continue
                print("| `%s` | %d | %d | %d (%s) | %d (%s) |" % (p, raw, d, t, pct(t, d), v, pct(v, d)))
            print("| **total** | %d | **%d** | **%d (%s)** | **%d (%s)** |\n"
                  % (tot[0], tot[1], tot[2], pct(tot[2], tot[1]), tot[3], pct(tot[3], tot[1])))
        else:
            print("== %s" % title)
            print("%-52s %6s %8s %14s %14s" % ("file", "raw", "to-xlat", "translated", "verified"))
            for p, raw, d, t, v in rows:
                if d == 0:
                    continue
                print("%-52s %6d %8d %8d %s %8d %s" % (p, raw, d, t, pct(t, d), v, pct(v, d)))
            print("%-52s %6d %8d %8d %s %8d %s\n" % ("TOTAL", tot[0], tot[1], tot[2], pct(tot[2], tot[1]), tot[3], pct(tot[3], tot[1])))
        return tot

    core = report("Verified core (ConLeche/Kernel, ConLeche/Cached)", CORE_GLOBS, CORE_EXCLUDE)
    cherry = report("Cherries (ConLeche/Frontend without Scan/Equiv, Main.lean)", CHERRY_GLOBS, CHERRY_EXCLUDE)

    rust = count_lines(walk("crates/con-ron-core/src", ".rs"))
    rust_unverified = count_lines(walk("crates", ".rs")) - rust
    gen = count_lines(walk(GENERATED_DIR, ".lean"))
    proofs = count_lines(walk(REFINE_DIR, ".lean"))
    n_items = sum(1 for it in items if it.kind == "fn")
    n_lemmas = len(lemmas)
    pin = (P.current_submodule_commit() or "?")[:8]
    if summary:
        print("Rust core %d lines (%d fns) | unverified crates %d | generated Lean %d | proofs %d (%d _refines) | pin %s"
              % (rust, n_items, rust_unverified, gen, proofs, n_lemmas, pin))
    elif md:
        print("### Sizes\n")
        print("| what | lines |\n|---|---:|")
        print("| Rust, verified core (`crates/con-ron-core`) | %d |" % rust)
        print("| Rust, unverified crates | %d |" % rust_unverified)
        print("| generated Lean (`%s`) | %d |" % (GENERATED_DIR, gen))
        print("| refinement proofs (`%s`) | %d |" % (REFINE_DIR, proofs))
        print("| Rust functions / `_refines` lemmas | %d / %d |" % (n_items, n_lemmas))
        print("\ncon-leche pin `%s`.  Core: %d%% translated, %d%% verified." % (
            pin, 100 * core[2] // max(core[1], 1), 100 * core[3] // max(core[1], 1)))
    else:
        print("Rust verified core %d lines; unverified crates %d; generated Lean %d; proofs %d; Rust fns %d, _refines lemmas %d; pin %s"
              % (rust, rust_unverified, gen, proofs, n_items, n_lemmas, pin))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
