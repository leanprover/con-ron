#!/usr/bin/env python3
"""scripts/dead-rust.py — `pub` Rust items with no caller (task #105).

`cargo build` under `-D warnings` catches a private item nothing uses, but
not a `pub` one: the compiler cannot know that no other crate calls it.
This census does the cross-crate part.  It collects every `pub` item
(`fn`, `const`, `static`, `struct`, `enum`, `type`, `trait`) of every
crate under `crates/`, and looks for a use of its name in any `.rs` file of
the workspace — outside comments, outside definitions — that can reach it,
resolved per occurrence:

* anywhere, when the name is defined only once in the workspace;
* `a::b::<name>`, when `a::b` (a leading `use … as` alias expanded,
  `crate::` absolute, `self`/`super` relative) names the item's module —
  `kernel::expr_ops`, not just any `expr_ops` — or, for a method, its type;
* a bare `<name>`, in its own file or in a file that imports it from its
  module (`use` statements are parsed whole: across lines, nested `{…}`
  groups, `as` renames, globs);
* for a method (a `pub fn` inside an `impl <Type>` block), `x.<name>` in a
  file that mentions `<Type>` (by name or through a `use … as` rename), and
  `x.<fld>.<name>` when some struct the file mentions has a field `<fld>`
  of type `<Type>` (`st.caches.reset()` reaches `Caches::reset`, since
  `AState.caches` is a `Caches`); `self.<name>` only in its own file.

    scripts/dead-rust.py [--tests-count] [--check] [--why <name>]

Output, one per line: `<file>:<line>  <kind> <name>  [only-tests]`.
An item used only from `#[cfg(test)]` code (a `#[cfg(test)] mod x;` file
included), `tests/` or `examples/` is
listed as `only-tests` (dead in the binary; a test of dead code is dead
code too) unless `--tests-count` is given.  `--why <name>` prints, for
every item called `<name>`, the non-test occurrences counted as its uses.
Heuristic by design: a hit is a candidate for reading, not a verdict; the
compiler is the arbiter when the item is cut.  `--check` exits 1 if
anything is listed and not in `scripts/dead-rust-allow.txt` (`<file>:<name>`
per line, reason after a tab).
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
    char_lit = re.compile(r"'(?:\\u\{[0-9a-fA-F]+\}|\\.|[^\\'\n])'")
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
        if c == "'":
            m = char_lit.match(text, i)
            if m:
                out.append(" " * (m.end() - i)); i = m.end(); continue
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
                if not started and j > i and lines[j].rstrip().endswith(";"):
                    break   # `#[cfg(test)] mod x;`, `#[cfg(test)] use …;`
                j += 1
            i = j + 1
            continue
        i += 1
    return inside


USE_RE = re.compile(r"\buse\s+([^;]*);", re.S)
OCC_RE = re.compile(r"((?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*)([A-Za-z_][A-Za-z0-9_]*)")
IMPL_RE = re.compile(r"^\s*impl\b(?:\s*<[^{]*?>)?\s+(?:[^{]*?\bfor\s+)?(?:[A-Za-z_][A-Za-z0-9_]*::)*([A-Za-z_][A-Za-z0-9_]*)")
STRUCT_RE = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?struct\s+([A-Za-z_][A-Za-z0-9_]*)")
FIELD_RE = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?([a-z_][A-Za-z0-9_]*)\s*:\s*[^A-Z]*?([A-Z][A-Za-z0-9_]*)")
DEF_RE = re.compile(r"\b(?:fn|struct|enum|type|trait|const|static|mod)\s*$")


def use_leaves(tree, prefix, out):
    """flatten a use tree `a::b::{c, d::{e as f}, self}` into (path, local)"""
    tree = tree.strip()
    if not tree:
        return
    if tree.endswith("}") and "{" in tree:
        k = tree.index("{")
        pre = [x.strip() for x in tree[:k].split("::") if x.strip()]
        body, depth, cur, parts = tree[k + 1:-1], 0, "", []
        for ch in body:
            if ch == "," and depth == 0:
                parts.append(cur); cur = ""; continue
            depth += (ch == "{") - (ch == "}")
            cur += ch
        parts.append(cur)
        for part in parts:
            use_leaves(part, prefix + pre, out)
        return
    m = re.match(r"(.*?)\s+as\s+([A-Za-z_][A-Za-z0-9_]*)$", tree, re.S)
    local = None
    if m:
        tree, local = m.group(1), m.group(2)
    path = prefix + [x.strip() for x in tree.split("::") if x.strip()]
    if path and path[-1] == "self":
        path = path[:-1]
    if path:
        out.append((path, local or path[-1]))


def mod_path(path):
    """`crates/<c>/src/a/b.rs` -> ['a', 'b'] (`mod.rs`/`lib.rs`/`main.rs` drop)"""
    parts = os.path.relpath(path, ROOT).split(os.sep)
    parts = parts[3:] if len(parts) > 3 and parts[2] == "src" else parts[-1:]
    parts[-1] = parts[-1][:-3]
    if parts[-1] in ("mod", "lib", "main"):
        parts = parts[:-1]
    return parts


def is_suffix(short, long, here):
    """does the module path `short`, written in module `here`, name `long`?
    `crate::…` is absolute; `self` is `here`, `super` its parent or, for the
    inline `mod tests { use super::*; }` shape, `here` itself; anything else
    is a suffix match"""
    if short and short[0] in ("crate", "con_ron_core", "con_ron_dump", "con_ron"):
        return short[1:] == long
    if short and short[0] == "self":
        return here + short[1:] == long
    if short and short[0] == "super":
        return long in (here + short[1:], here[:-1] + short[1:])
    return len(short) <= len(long) and long[len(long) - len(short):] == short


class FileInfo:
    def __init__(self, path, lines):
        self.mod = mod_path(path)
        leaves = []
        for m in USE_RE.finditer("\n".join(lines)):
            use_leaves(" ".join(m.group(1).split()), [], leaves)
        self.bound = {}       # local name -> the path it imports
        self.globs = []       # module paths glob-imported
        for path_, local in leaves:
            if local == "*":
                self.globs.append(path_[:-1])
            else:
                self.bound[local] = path_
        self.tokens = set()
        self.fields = []      # (field, its type's first capitalised token, struct)
        depth, start, pending = 0, None, False
        for line in lines:
            self.tokens.update(TOKEN_RE.findall(line))
            sm = STRUCT_RE.match(line)
            if start is None and sm:
                pending, owner = True, sm.group(1)
            if pending and ";" in line and "{" not in line:
                pending = False   # a tuple or unit struct
            if pending and "{" in line:
                start, pending = depth, False
            elif start is not None:
                fm = FIELD_RE.match(line)
                if fm:
                    self.fields.append((fm.group(1), fm.group(2), owner))
            depth += line.count("{") - line.count("}")
            if start is not None and depth <= start:
                start = None

    def resolve(self, qual):
        """a qualifier path as written -> the path it names"""
        if qual and qual[0] in self.bound:
            return self.bound[qual[0]] + qual[1:]
        return qual

    def type_is(self, tok, mod, ty):
        """does this file's `tok` name the type `ty` of module `mod`?"""
        if tok in self.bound:
            p = self.bound[tok]
            return p[-1] == ty and (len(p) < 2 or is_suffix(p[:-1], mod, self.mod))
        return tok == ty


def main():
    tests_count = "--tests-count" in sys.argv
    why = sys.argv[sys.argv.index("--why") + 1] if "--why" in sys.argv else None
    files = rs_files()
    text, tests, info = {}, {}, {}
    for f in files:
        t = strip_comments(open(f, encoding="utf-8", errors="replace").read())
        text[f] = t.split("\n")
        tests[f] = test_ranges(text[f])
        info[f] = FileInfo(f, text[f])
    # a module declared `#[cfg(test)] mod x;` is test code, all of it
    for f in files:
        for i, line in enumerate(text[f]):
            m = re.match(r"\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;", line)
            if m and i > 0 and "#[cfg(test)]" in text[f][i - 1]:
                base = f[:-3]
                if os.path.basename(f) in ("lib.rs", "main.rs", "mod.rs"):
                    base = os.path.dirname(f)
                for g in (os.path.join(base, m.group(1) + ".rs"),
                          os.path.join(base, m.group(1), "mod.rs")):
                    if g in text:
                        tests[g] = set(range(len(text[g])))
    items = []
    defs = defaultdict(set)
    field_ty = defaultdict(list)  # field name -> [(its type's path, file, struct)]
    local_defs = defaultdict(set)  # file -> every name it defines, pub or not
    for f in files:
        for fld, t, st in info[f].fields:
            field_ty[fld].append((info[f].bound.get(t, [t]), f, st))
        depth, impls, pending = 0, [], None   # impls: (type, depth its body opens at)
        for i, line in enumerate(text[f]):
            m = ITEM_RE.match(line)
            if m and i not in tests[f]:
                kind = KIND_RE.match(line).group(1)
                owner = impls[-1][0] if impls and impls[-1][1] == depth - 1 else None
                items.append((f, i, kind, m.group(1), owner))
                defs[m.group(1)].add(f)
            im = IMPL_RE.match(line)
            if im:
                pending = im.group(1)   # the body's `{` may be lines below
            if pending and "{" in line:
                impls.append((pending, depth))
                pending = None
            depth += line.count("{") - line.count("}")
            while impls and depth <= impls[-1][1]:
                impls.pop()
    # name -> file -> [(line, qualifier path, receiver)]; receiver is None
    # for a non-method occurrence, "" for `x.name`, the field for `x.fld.name`,
    # "self" for `self.name` (the enclosing impl's own method)
    occ = defaultdict(lambda: defaultdict(list))
    for f in files:
        for i, line in enumerate(text[f]):
            for m in OCC_RE.finditer(line):
                before = line[:m.start()].rstrip()
                if DEF_RE.search(before):
                    local_defs[f].add(m.group(2))
                    continue
                qual = [x.strip() for x in m.group(1).split("::") if x.strip()]
                recv = None
                if before.endswith("."):
                    fm = re.search(r"\.\s*([a-z_][A-Za-z0-9_]*)\s*\.$", before)
                    recv = (fm.group(1) if fm else
                            "self" if re.search(r"\bself\s*\.$", before) else "")
                occ[m.group(2)][f].append((i, qual, recv))
    allow = set()
    try:
        for l in open(ALLOW):
            l = l.split("#", 1)[0].strip()
            if l:
                allow.add(l.split("\t")[0].strip())
    except OSError:
        pass

    mention_cache = {}

    def mentions(g, mod, ty):
        key = (g, tuple(mod), ty)
        if key not in mention_cache:
            gi = info[g]
            mention_cache[key] = any(gi.type_is(t, mod, ty) for t in (ty, *gi.bound)
                                     if t in gi.tokens)
        return mention_cache[key]

    def reaches(f, owner, name, g, qual, recv):
        fi, gi = info[f], info[g]
        if qual:
            q = gi.resolve(qual)
            if q[-1] == "Self":
                return g == f
            if owner is not None and gi.type_is(qual[-1], fi.mod, owner):
                return True
            return is_suffix(q, fi.mod, gi.mod)
        if g == f or len(defs[name]) == 1:
            return True
        if owner is not None:
            if recv == "self":
                return False   # g != f: `self` is another impl's
            if recv:
                return any(p[-1] == owner and (len(p) < 2 or is_suffix(p[:-1], fi.mod, info[h].mod))
                           and (g == h or st in gi.tokens)
                           for p, h, st in field_ty.get(recv, ()))
            return recv == "" and mentions(g, fi.mod, owner)
        if name in gi.bound:
            return is_suffix(gi.bound[name][:-1], fi.mod, gi.mod)
        return (name not in local_defs[g]
                and any(is_suffix(p, fi.mod, gi.mod) for p in gi.globs))

    listed = []
    for f, i, kind, name, owner in items:
        uses, test_uses = 0, 0
        for g, occs in occ[name].items():
            for j, qual, recv in occs:
                if g == f and j == i:
                    continue
                if not reaches(f, owner, name, g, qual, recv):
                    continue
                if j in tests[g] or "/tests/" in g or "/examples/" in g or "/benches/" in g:
                    test_uses += 1
                else:
                    uses += 1
                    if why == name:
                        print(f"  {os.path.relpath(f, ROOT)}:{i + 1} <- "
                              f"{os.path.relpath(g, ROOT)}:{j + 1}", file=sys.stderr)
        if uses == 0 and (test_uses == 0 or not tests_count):
            rel = os.path.relpath(f, ROOT)
            tag = "  only-tests" if test_uses else ""
            listed.append((rel, i + 1, kind, name, tag))
    bad = 0
    for rel, ln, kind, name, tag in listed:
        if f"{rel}:{name}" not in allow:
            bad += 1
        print(f"{rel}:{ln}  {kind} {name}{tag}")
    print(f"dead-rust: {len(listed)} pub item(s) with no non-test use, "
          f"{bad} outside the allowlist", file=sys.stderr)
    if "--check" in sys.argv and bad:
        sys.exit(1)


if __name__ == "__main__":
    main()
