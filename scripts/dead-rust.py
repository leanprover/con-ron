#!/usr/bin/env python3
"""scripts/dead-rust.py — `pub` Rust items with no caller (task #105).

`cargo build` under `-D warnings` catches a private item nothing uses, but
not a `pub` one: the compiler cannot know that no other crate calls it.
This census does the cross-crate part.  It collects every `pub` item
(`fn`, `const`, `static`, `struct`, `enum`, `type`, `trait`) of every
crate under `crates/`, and looks for a use of its name in any `.rs` file of
the workspace — outside comments, outside the item's own definition line —
that can reach it: in its own file, or in a file that names its module
(`<module>::<name>` or a `use …<module>::{…<name>…}`), or anywhere when the
name is defined only once in the workspace.

    scripts/dead-rust.py [--tests-count] [--check]

Output, one per line: `<file>:<line>  <kind> <name>  [only-tests]`.
An item used only from `#[cfg(test)]` code, `tests/` or `examples/` is
listed as `only-tests` (dead in the binary; a test of dead code is dead
code too) unless `--tests-count` is given.  Heuristic by design: a hit is a
candidate for reading, not a verdict; the compiler is the arbiter when the
item is cut.  `--check` exits 1 if anything is listed and not in
`scripts/dead-rust-allow.txt` (`<file>:<name>` per line, reason after a tab).
"""
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ALLOW = os.path.join(ROOT, "scripts", "dead-rust-allow.txt")

ITEM_RE = re.compile(r"^\s*pub(?:\([^)]*\))?\s+(?:const\s+fn|unsafe\s+fn|fn|const|static|struct|enum|type|trait)\s+([A-Za-z_][A-Za-z0-9_]*)")
KIND_RE = re.compile(r"^\s*pub(?:\([^)]*\))?\s+(const\s+fn|unsafe\s+fn|fn|const|static|struct|enum|type|trait)\b")
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def rs_files():
    out = []
    for dirpath, dirnames, filenames in os.walk(os.path.join(ROOT, "crates")):
        dirnames[:] = [d for d in dirnames if d not in ("target",)]
        for fn in filenames:
            if fn.endswith(".rs"):
                out.append(os.path.join(dirpath, fn))
    return sorted(out)


def strip_comments(text):
    """blank out `//` comments, `/* */` comments and string literals, keeping
    line numbers"""
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        c = text[i]
        two = text[i:i + 2]
        if depth:
            if two == "*/":
                depth -= 1; i += 2; out.append("  "); continue
            if two == "/*":
                depth += 1; i += 2; out.append("  "); continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if two == "//":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if two == "/*":
            depth = 1; i += 2; out.append("  "); continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            seg = text[i:j + 1]
            out.append("".join("\n" if ch == "\n" else " " for ch in seg)); i = j + 1; continue
        out.append(c); i += 1
    return "".join(out)


def module_name(path):
    base = os.path.basename(path)[:-3]
    if base in ("mod", "lib", "main"):
        return os.path.basename(os.path.dirname(path))
    return base


def test_ranges(lines):
    """line indices inside a `#[cfg(test)]` item (brace-matched)"""
    inside = set()
    i = 0
    while i < len(lines):
        if "#[cfg(test)]" in lines[i]:
            depth, started, j = 0, False, i
            while j < len(lines):
                depth += lines[j].count("{") - lines[j].count("}")
                if "{" in lines[j]:
                    started = True
                inside.add(j)
                if started and depth <= 0:
                    break
                j += 1
            i = j + 1
            continue
        i += 1
    return inside


def main():
    tests_count = "--tests-count" in sys.argv
    files = rs_files()
    text = {}
    tests = {}
    for f in files:
        t = strip_comments(open(f, encoding="utf-8", errors="replace").read())
        text[f] = t.split("\n")
        tests[f] = test_ranges(text[f])
    items = []
    defs = defaultdict(set)
    for f in files:
        for i, line in enumerate(text[f]):
            m = ITEM_RE.match(line)
            if m and i not in tests[f]:
                kind = KIND_RE.match(line).group(1)
                items.append((f, i, kind, m.group(1)))
                defs[m.group(1)].add(f)
    occ = defaultdict(lambda: defaultdict(list))  # name -> file -> [line idx]
    for f in files:
        for i, line in enumerate(text[f]):
            for tok in TOKEN_RE.findall(line):
                occ[tok][f].append(i)
    allow = set()
    try:
        for l in open(ALLOW):
            l = l.split("#", 1)[0].strip()
            if l:
                allow.add(l.split("\t")[0].strip())
    except OSError:
        pass
    listed = []
    for f, i, kind, name in items:
        mod = module_name(f)
        uses, test_uses = 0, 0
        for g, idxs in occ[name].items():
            reach = (g == f or len(defs[name]) == 1
                     or any(re.search(r"\b" + re.escape(mod) + r"::(?:\{[^}]*\b" + re.escape(name)
                                      + r"\b|" + re.escape(name) + r"\b)", l) for l in text[g]))
            if not reach:
                continue
            for j in idxs:
                if g == f and j == i:
                    continue
                is_test = (j in tests[g] or "/tests/" in g or "/examples/" in g
                           or "/benches/" in g)
                if is_test:
                    test_uses += 1
                else:
                    uses += 1
        if uses == 0 and (test_uses == 0 or not tests_count):
            rel = os.path.relpath(f, ROOT)
            tag = "  only-tests" if test_uses else ""
            listed.append((rel, i + 1, kind, name, tag))
    bad = 0
    for rel, ln, kind, name, tag in listed:
        mark = "" if f"{rel}:{name}" in allow else ""
        if f"{rel}:{name}" not in allow:
            bad += 1
        print(f"{rel}:{ln}  {kind} {name}{tag}{mark}")
    print(f"dead-rust: {len(listed)} pub item(s) with no non-test use, "
          f"{bad} outside the allowlist", file=sys.stderr)
    if "--check" in sys.argv and bad:
        sys.exit(1)


if __name__ == "__main__":
    main()
