#!/usr/bin/env python3
"""scripts/provenance.py — THE PROVENANCE GATE (task #8, DESIGN.md §3.7).

Every Rust item Charon sees cites the con-leche lines it was ported from:

    /// con-leche: ConLeche/Kernel/Level.lean:82-89 leqCore

or, for an item with no Lean counterpart,

    /// con-leche: none — replaces the runtime's `Nat`; spec in NatSpec.lean

The vendored tree is the single source of truth: `vendor/con-leche` is a
squashed `git subtree` of con-leche (task #74; its upstream commit is the
first word of `vendor/CON_LECHE_PIN`), so `(pin, path, range)` fixes the
cited text and no hash is needed in the source.  `check` verifies every
citation against the tree and demands one on every item; `update --old
<rev>` diffs the old tree against the new one — `rev` is a con-ron
revision whose `vendor/con-leche` is the old tree (`HEAD` during an
uncommitted `git subtree pull`), or, for the pre-subtree history, a
con-leche commit resolvable in the retired submodule's git dir —
relocates what merely moved and marks what changed with a `CHANGED`
marker line the porter deletes once reconciled; `coverage` prints the
port ledger.  Pure source-tree work: no build, no network, python3
stdlib only, milliseconds.

Exit codes: 0 clean, 1 findings, 2 usage/IO error.
"""

from __future__ import annotations

import argparse
import difflib
import os
import re
import subprocess
import sys

# The Rust trees that must be annotated, relative to the repository root.
# `crates/con-ron/src` is the UNVERIFIED crate: the in-process modeller, the
# driver and the pool (the parser left it for the verified core at task #84).
# It is inside this gate and outside `lint-rust-style.sh` and `extract.sh` on
# purpose: DESIGN.md §3.7 — "for the unverified frontend it is the only sync
# signal there is".  Its items are cited but not style-linted.
DEFAULT_ROOTS = [
    "crates/con-ron-core/src",
    "crates/con-ron/src",
]

# The con-leche submodule, and the implementation trees the ledger counts.
CON_LECHE = "vendor/con-leche"
COVERAGE_GLOBS = ["ConLeche/Kernel", "ConLeche/Cached"]

# The allowlist of declarations that are deliberately NOT ported (task #33):
# `<path> <decl> <reason>` lines, `<decl>` possibly `*` for a whole file.
SKIP_FILE = "scripts/provenance-skip.txt"

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ---------------------------------------------------------------- annotations

# An annotation is `/// con-leche: …` on an item, or `//! con-leche: …` on a
# whole module (`MODULE_ANNOT_RE` is the same line, used to recognise the
# module-wide form; see `cmd_check`).  A module-level line may be `none` (a
# module with no Lean counterpart, `nat.rs`) or a *citation* (a generated
# module that is one Lean declaration's value, `basis_tables.rs`, task #22);
# either way it covers every item in the file.
ANNOT_RE = re.compile(r"^\s*(?P<pfx>//[/!])\s*con-leche:\s*(?P<body>.*?)\s*$")
MODULE_ANNOT_RE = re.compile(r"^\s*//!\s*con-leche:\s*(?P<body>.*?)\s*$")
CITE_RE = re.compile(
    r"^(?P<path>[^\s:]+):(?P<a>\d+)(?:-(?P<b>\d+))?\s+(?P<decl>\S+)$"
)
NONE_RE = re.compile(r"^none\b")
MARKER_RE = re.compile(r"^\s*//[/!]\s*con-leche:\s*CHANGED\b")


def marker(old, item, pfx="///"):
    return ("%s con-leche: CHANGED since %s — re-port, re-test, re-prove "
            "%s_refines, then delete this line" % (pfx, old[:8], item))


class Cite:
    """One `con-leche:` doc line: where it sits, and what it claims."""

    def __init__(self, rust_file, lineno, path, a, b, decl, pfx="///"):
        self.rust_file = rust_file  # absolute path of the .rs file
        self.lineno = lineno  # 1-based line of the annotation
        self.path = path  # con-leche-relative Lean path
        self.a = a
        self.b = b
        self.decl = decl
        self.pfx = pfx  # `///` (an item's) or `//!` (a whole module's)

    @property
    def range(self):
        return str(self.a) if self.a == self.b else "%d-%d" % (self.a, self.b)

    def render(self, indent):
        return "%s%s con-leche: %s:%s %s" % (
            indent, self.pfx, self.path, self.range, self.decl)

    def where(self):
        return "%s:%d" % (rel(self.rust_file), self.lineno)


def rel(p):
    try:
        return os.path.relpath(p, REPO)
    except ValueError:
        return p


# ------------------------------------------------------------------ Rust scan

ITEM_RE = re.compile(
    r"^\s*(?:pub(?:\s*\([^)]*\))?\s+)?"
    r"(?:default\s+|const\s+|async\s+|unsafe\s+|extern\s+\"[^\"]*\"\s+)*"
    r"(?P<kind>fn|struct|enum|impl|const|trait|type)\b"
)
DOC_RE = re.compile(r"^\s*///")
ATTR_RE = re.compile(r"^\s*#\[")
CFG_TEST_RE = re.compile(r"^\s*#\[cfg\(test\)\]")
MOD_TESTS_RE = re.compile(r"^\s*(?:pub\s+)?mod\s+tests\b")


def strip_code(line):
    """Drop `//` comments and string/char literals before counting braces."""
    out = []
    i = 0
    n = len(line)
    while i < n:
        c = line[i]
        if c == "/" and i + 1 < n and line[i + 1] == "/":
            break
        if c == '"':
            i += 1
            while i < n:
                if line[i] == "\\":
                    i += 2
                    continue
                if line[i] == '"':
                    break
                i += 1
            i += 1
            continue
        if c == "'":
            # char literal or lifetime; only `'x'` / `'\n'` shape swallows
            m = re.match(r"'(\\.|[^\\'])'", line[i:])
            if m:
                i += m.end()
                continue
        out.append(c)
        i += 1
    return "".join(out)


class RustItem:
    def __init__(self, file, lineno, kind, text, cites, has_doc):
        self.file = file
        self.lineno = lineno
        self.kind = kind
        self.text = text
        self.cites = cites  # list[Cite | None]; None = an explicit `none`
        self.has_doc = has_doc

    def name(self):
        m = re.search(r"\b(?:fn|struct|enum|trait|const|type)\s+([A-Za-z_][A-Za-z0-9_]*)",
                      self.text)
        if m:
            return m.group(1)
        return self.text.strip().rstrip("{").strip()


def scan_rust_file(path):
    """Return (items, cites) for one .rs file.

    Items are the Charon-visible `fn`/`struct`/`enum`/`impl`/`const`/`trait`/
    `type` declarations: outside `#[cfg(test)]` and `mod tests`, and outside
    any function body (a helper defined inside a `fn` is part of that item).
    """
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")

    items = []
    cites = []
    markers = []
    depth = 0
    test_depth = None  # depth outside the skipped `#[cfg(test)]` block
    fn_depth = None  # depth outside the current fn body
    pending_test = False
    pending_fn = False

    for idx, raw in enumerate(lines):
        lineno = idx + 1
        code = strip_code(raw)
        opens = code.count("{")
        closes = code.count("}")
        skipping = test_depth is not None or fn_depth is not None

        if not skipping:
            m = ANNOT_RE.match(raw)
            if m:
                body = m.group("body")
                if MARKER_RE.match(raw):
                    markers.append((path, lineno, body))
                elif not NONE_RE.match(body):
                    c = CITE_RE.match(body)
                    if c:
                        a = int(c.group("a"))
                        b = int(c.group("b")) if c.group("b") else a
                        cites.append(Cite(path, lineno, c.group("path"), a, b,
                                          c.group("decl"), m.group("pfx")))
                    else:
                        cites.append(("malformed", path, lineno, body))

            if CFG_TEST_RE.match(raw) or MOD_TESTS_RE.match(raw):
                pending_test = True
            elif ITEM_RE.match(raw):
                kind = ITEM_RE.match(raw).group("kind")
                if not pending_test:
                    doc, docstart = doc_block(lines, idx)
                    item_cites = []
                    for dl in doc:
                        m2 = ANNOT_RE.match(lines[dl])
                        if m2:
                            body = m2.group("body")
                            if MARKER_RE.match(lines[dl]):
                                pass
                            elif NONE_RE.match(body):
                                item_cites.append(None)
                            else:
                                c = CITE_RE.match(body)
                                item_cites.append(
                                    Cite(path, dl + 1, c.group("path"),
                                         int(c.group("a")),
                                         int(c.group("b") or c.group("a")),
                                         c.group("decl"))
                                    if c else "malformed")
                    items.append(RustItem(path, lineno, kind, raw, item_cites,
                                          docstart is not None))
                if kind == "fn" or kind == "impl" or kind == "trait":
                    pending_fn = (kind == "fn")

        depth_before = depth
        depth += opens - closes

        if pending_test and depth > depth_before:
            test_depth = depth_before
            pending_test = False
        elif pending_fn and depth > depth_before:
            if fn_depth is None and test_depth is None:
                fn_depth = depth_before
            pending_fn = False
        elif (pending_test or pending_fn) and ";" in code:
            pending_test = False
            pending_fn = False

        if test_depth is not None and depth <= test_depth:
            test_depth = None
        if fn_depth is not None and depth <= fn_depth:
            fn_depth = None

    return items, cites, markers


def doc_block(lines, idx):
    """The contiguous `///` / `#[...]` block immediately above line `idx`.

    Returns (indices of `///` lines, index where the block starts or None)."""
    i = idx - 1
    doc = []
    start = None
    while i >= 0:
        if DOC_RE.match(lines[i]):
            doc.append(i)
            start = i
        elif ATTR_RE.match(lines[i]):
            start = i
        elif lines[i].strip() == "":
            break
        else:
            break
        i -= 1
    doc.reverse()
    return doc, start


def rust_files(roots):
    out = []
    for root in roots:
        full = root if os.path.isabs(root) else os.path.join(REPO, root)
        if not os.path.isdir(full):
            continue
        for dirpath, dirnames, filenames in os.walk(full):
            dirnames[:] = [d for d in dirnames if d not in ("target", ".git")]
            for fn in sorted(filenames):
                if fn.endswith(".rs"):
                    out.append(os.path.join(dirpath, fn))
    return sorted(out)


# ------------------------------------------------------------------ Lean side

DECL_KW = ("def|theorem|abbrev|inductive|structure|class|instance|opaque|axiom"
           "|lemma|example")
MODIFIERS = r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|public\s+|meta\s+|scoped\s+|local\s+)*"
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*" + MODIFIERS + r"(?P<kw>" + DECL_KW + r")\s+"
    r"(?P<name>[^\s:({\[⟨]+)")
ANON_INSTANCE_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*" + MODIFIERS + r"instance\s*[:(⟨]")
# A column-0 line that ends the previous declaration's block.
STOPPER_RE = re.compile(
    r"^(?:/--|/-!|@\[|end\b|namespace\b|section\b|mutual\b|open\b|variable\b"
    r"|attribute\b|#|" + MODIFIERS + r"(?:" + DECL_KW + r")\s)")


def lean_text(path, old=None):
    """The Lean file's lines: from the vendored tree, or from `old` — a
    con-ron revision whose tree holds the old `vendor/con-leche`, else (the
    history before the subtree, task #74) a con-leche commit in the retired
    submodule's git dir."""
    if old is None:
        full = os.path.join(REPO, CON_LECHE, path)
        if not os.path.exists(full):
            return None
        with open(full, encoding="utf-8") as f:
            return f.read().split("\n")
    r = subprocess.run(["git", "-C", REPO, "show", "%s:%s/%s" % (old, CON_LECHE, path)],
                       capture_output=True, text=True)
    if r.returncode == 0:
        return r.stdout.split("\n")
    common = subprocess.run(["git", "-C", REPO, "rev-parse", "--git-common-dir"],
                            capture_output=True, text=True).stdout.strip()
    moddir = os.path.join(REPO, common, "modules", CON_LECHE)
    if not os.path.isdir(moddir):
        return None
    r = subprocess.run(["git", "--git-dir", moddir, "show", "%s:%s" % (old, path)],
                       capture_output=True, text=True)
    return r.stdout.split("\n") if r.returncode == 0 else None


def comment_lines(lines):
    """The indices of lines inside a `/- … -/` block comment (`/-!` and `/--`
    included), openers and closers counted as inside.

    Without this a column-0 *phrase* in a module docstring reads as a
    declaration: `ExprOps.lean`'s `/-!` block says "inductive install", which
    the ledger counted as a `def` named `install` (task #13's one false
    positive).  A docstring is not a declaration."""
    inside = set()
    depth = 0
    for i, line in enumerate(lines):
        started = depth > 0
        j, n = 0, len(line)
        while j < n - 1:
            two = line[j:j + 2]
            if depth == 0 and two == "--":
                break  # a line comment: `-/` inside it is not a closer
            if two == "/-":
                depth += 1
                j += 2
                continue
            if two == "-/":
                if depth:
                    depth -= 1
                j += 2
                continue
            j += 1
        if started or depth > 0:
            inside.add(i)
    return inside


def decl_name_at(lines, i, skip=None):
    """(keyword, name) if column-0 line `i` starts a declaration."""
    if lines[i][:1].isspace() or not lines[i]:
        return None
    if skip is not None and i in skip:
        return None
    m = DECL_RE.match(lines[i])
    if not m:
        return None
    return m.group("kw"), m.group("name")


def names_compatible(declared, cited):
    """Does the Lean declaration `declared` answer to the citation `cited`?

    `leqCore` answers to `Level.leqCore` and back (a `namespace` either side
    of the citation), and `subst` answers to `subst.go` (a `where` clause is
    part of its parent's block).  A citation is *not* allowed to name a
    namespace and match a declaration inside it: `Level` must not match
    `Level.beqPtr`."""
    if declared == cited:
        return True
    xs, ys = declared.split("."), cited.split(".")
    if len(xs) <= len(ys) and (ys[-len(xs):] == xs or ys[:len(xs)] == xs):
        return True  # namespace-qualified citation, or a `where` clause of it
    if len(ys) <= len(xs) and xs[-len(ys):] == ys:
        return True  # the citation drops a namespace the Lean file opens
    return False


def locate_decl(lines, decl):
    """The block of the declaration named `decl`, as a 1-based (a, b) range.

    The block runs from the declaration's own attributes and doc comment to
    the line before the next column-0 line that starts something new."""
    skip = comment_lines(lines)
    decls = [(i, decl_name_at(lines, i, skip)) for i in range(len(lines))]
    decls = [(i, g[1]) for (i, g) in decls if g]
    xs = decl.split(".")

    def exact(name):
        return name == decl

    def suffix(name):
        ys = name.split(".")
        return (len(ys) <= len(xs) and xs[-len(ys):] == ys) or \
               (len(xs) <= len(ys) and ys[-len(xs):] == xs)

    def parent(name):
        # `subst` answers to `subst.go`: a `where` clause is inside its parent.
        ys = name.split(".")
        return len(ys) < len(xs) and xs[:len(ys)] == ys

    for pred in (exact, suffix, parent):
        for i, name in decls:
            if pred(name):
                return extend_block(lines, i)
    return None


def extend_block(lines, i):
    a = i
    # attributes and the doc comment sitting above the declaration
    j = i - 1
    while j >= 0:
        s = lines[j]
        if s.startswith("@[") or s.startswith("/--"):
            a = j
            j -= 1
            continue
        if s.rstrip().endswith("-/") and not s.startswith("/-!"):
            # A multi-line comment ends here: walk back to its opener, and
            # take it only if that opener is this declaration's own doc
            # comment (`/--`).  A `/-! … -/` section header belongs to no
            # declaration — walking through it would swallow the *previous*
            # declaration's doc comment and make two blocks overlap
            # (`Frontend/InModel/Kit.lean`'s `sortOf`/`sortCeil`, task #33).
            k = j
            while k >= 0 and not (lines[k].startswith("/--")
                                  or lines[k].startswith("/-!")):
                k -= 1
            if k >= 0 and lines[k].startswith("/--"):
                a = k
                j = k - 1
                continue
        break
    b = i
    k = i + 1
    while k < len(lines):
        s = lines[k]
        if s and not s[:1].isspace() and STOPPER_RE.match(s):
            break
        b = k
        k += 1
    while b > i and lines[b].strip() == "":
        b -= 1
    return a + 1, b + 1


def lean_files_for_coverage():
    out = []
    for sub in COVERAGE_GLOBS:
        base = os.path.join(REPO, CON_LECHE, sub)
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(dirnames)
            for fn in sorted(filenames):
                if fn.endswith(".lean"):
                    full = os.path.join(dirpath, fn)
                    out.append(os.path.relpath(full, os.path.join(REPO, CON_LECHE)))
        lone = base + ".lean"
        if os.path.exists(lone):
            out.append(os.path.relpath(lone, os.path.join(REPO, CON_LECHE)))
    return sorted(out)


DEFINITIONAL = ("def", "abbrev", "inductive", "structure", "class", "instance",
                "opaque")


def top_level_decls(lines):
    """[(lineno, kw, name)] for every column-0 definition in the file."""
    out = []
    skip = comment_lines(lines)
    for i, line in enumerate(lines):
        got = decl_name_at(lines, i, skip)
        if got:
            out.append((i + 1, got[0], got[1]))
    return out


# ------------------------------------------------------------------ the modes


def collect(roots):
    items, cites, malformed, markers = [], [], [], []
    for f in rust_files(roots):
        it, ci, mk = scan_rust_file(f)
        items.extend(it)
        markers.extend(mk)
        for c in ci:
            if isinstance(c, Cite):
                cites.append(c)
            else:
                malformed.append(c)
    return items, cites, malformed, markers


def cmd_check(args):
    items, cites, malformed, markers = collect(args.roots)
    findings = 0

    for _, path, lineno, body in malformed:
        print("MALFORMED %s:%d — %s" % (rel(path), lineno, body))
        findings += 1

    for path, lineno, body in markers:
        print("UNRECONCILED %s:%d — %s" % (rel(path), lineno, body))
        findings += 1

    cache = {}
    for c in cites:
        if c.path not in cache:
            cache[c.path] = lean_text(c.path)
        lines = cache[c.path]
        if lines is None:
            print("MISSING %s — %s cites a file not in %s"
                  % (c.where(), c.path, CON_LECHE))
            findings += 1
            continue
        if c.a < 1 or c.b > len(lines) or c.a > c.b:
            print("RANGE %s — %s:%s outside the file (%d lines)"
                  % (c.where(), c.path, c.range, len(lines)))
            findings += 1
            continue
        if c.decl == "_":
            continue
        head = first_decl_line(lines, c.a, c.b)
        if head is None:
            print("NODECL %s — %s:%s declares nothing (expected %s)"
                  % (c.where(), c.path, c.range, c.decl))
            findings += 1
        elif not names_compatible(head, c.decl):
            print("NAME %s — %s:%s declares `%s`, cited as `%s`"
                  % (c.where(), c.path, c.range, head, c.decl))
            findings += 1

    # A module-level annotation covers the whole file, and every item in it is
    # then exempt from the per-item requirement.  Two forms (DESIGN.md §3.7):
    #     //! con-leche: none — <why>           a module with no Lean
    #                                           counterpart (`nat.rs`)
    #     //! con-leche: <path>:<range> <decl>  a *generated* module that is
    #                                           one Lean declaration's value
    #                                           (`basis_tables.rs`, task #22)
    # The citation form is checked exactly like an item's (it is in `cites`);
    # what the module form adds is the exemption.
    module_annot = set()
    for f in {it.file for it in items}:
        for line in open(f, encoding="utf-8"):
            if MODULE_ANNOT_RE.match(line):
                module_annot.add(f)
                break
    for it in items:
        if not it.cites and it.file not in module_annot:
            print("UNCITED %s:%d — `%s %s` has no `con-leche:` line"
                  % (rel(it.file), it.lineno, it.kind, it.name()))
            findings += 1

    if findings:
        print("%d finding(s)." % findings)
        return 1
    print("provenance: %d item(s), %d citation(s), all current at pin %s."
          % (len(items), len(cites), (current_submodule_commit() or "?")[:8]))
    return 0


def first_decl_line(lines, a, b):
    """The name declared by the first non-attribute, non-doc line of a range."""
    i = a - 1
    while i < b:
        s = lines[i]
        if s.strip() == "":
            i += 1
            continue
        if s.startswith("/--") or s.startswith("/-!") or s.startswith("/-"):
            while i < b and not lines[i].rstrip().endswith("-/"):
                i += 1
            i += 1
            continue
        if s.startswith("@[") and not DECL_RE.match(s):
            i += 1
            continue
        m = DECL_RE.match(s)
        if m:
            return m.group("name")
        if ANON_INSTANCE_RE.match(s):
            return "_"
        return None
    return None


PIN_FILE = "vendor/CON_LECHE_PIN"  # first word: the vendored con-leche commit


def recorded_submodule_commit():
    """The con-leche commit recorded in HEAD (`vendor/CON_LECHE_PIN` there) —
    the `old` side of an uncommitted bump.  The name predates the subtree."""
    r = subprocess.run(["git", "-C", REPO, "show", "HEAD:" + PIN_FILE],
                       capture_output=True, text=True)
    if r.returncode == 0 and r.stdout.split():
        return r.stdout.split()[0]
    try:  # the history before task #74: a submodule gitlink
        out = subprocess.run(["git", "-C", REPO, "ls-tree", "HEAD", CON_LECHE],
                             capture_output=True, text=True, check=True).stdout
    except subprocess.CalledProcessError:
        return None
    m = re.search(r"commit ([0-9a-f]{40})", out)
    return m.group(1) if m else None


def current_submodule_commit():
    """The vendored con-leche commit: the first word of `vendor/CON_LECHE_PIN`."""
    try:
        with open(os.path.join(REPO, PIN_FILE), encoding="utf-8") as f:
            words = f.read().split()
        return words[0] if words else None
    except OSError:
        return None


def rewrite(edits):
    """Apply per-file line rewrites and insertions, bottom-up.

    `edits[file]` is a list of `(lineno, replacement_or_None, inserts)`:
    the annotation line is replaced when `replacement` is given, and
    `inserts` are added right after it."""
    for path, es in edits.items():
        with open(path, encoding="utf-8") as f:
            lines = f.read().split("\n")
        for lineno, repl, inserts in sorted(es, key=lambda e: -e[0]):
            indent = re.match(r"^\s*", lines[lineno - 1]).group(0)
            if repl is not None:
                lines[lineno - 1] = repl(indent)
            for k, ins in enumerate(inserts):
                lines.insert(lineno + k, indent + ins)
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines))


def cmd_update(args):
    old = args.old
    if old is None:
        rec, cur = recorded_submodule_commit(), current_submodule_commit()
        if rec and cur and rec != cur:
            old = "HEAD"  # the old tree is HEAD's `vendor/con-leche`
        else:
            print("usage: no uncommitted bump of vendor/con-leche (the pin file "
                  "matches HEAD's); pass --old <rev>", file=sys.stderr)
            return 2

    _, cites, malformed, markers = collect(args.roots)
    findings = len(malformed)
    for _, path, lineno, body in malformed:
        print("MALFORMED %s:%d — %s" % (rel(path), lineno, body))
    for path, lineno, body in markers:
        print("UNRECONCILED %s:%d — %s" % (rel(path), lineno, body))
        findings += 1

    edits = {}
    moved = 0
    cache, oldcache = {}, {}
    for c in cites:
        if c.path not in cache:
            cache[c.path] = lean_text(c.path)
        if c.path not in oldcache:
            oldcache[c.path] = lean_text(c.path, old=old)
        lines, olines = cache[c.path], oldcache[c.path]
        item = rust_item_of(c)

        if lines is None:
            print("GONE %s — %s no longer exists at the new pin → re-port %s"
                  % (c.where(), c.path, item))
            if not has_marker(c):
                edits.setdefault(c.rust_file, []).append(
                    (c.lineno, None, [marker(old, item, c.pfx)]))
            findings += 1
            continue

        old_text = None
        if olines is not None and 1 <= c.a <= c.b <= len(olines):
            old_text = [l.rstrip() for l in olines[c.a - 1:c.b]]

        # Relocate by text first: the cited block, verbatim, nearest to where
        # it was.  This is what makes an anonymous `_` citation (an
        # `instance`) survive a bump — `locate_decl` cannot tell one `_` from
        # another — and it is the honest test for every citation: the text
        # is what the citation fixes (task #74, the first real bump).
        loc = find_block(lines, old_text, c.a) if old_text else None
        if loc is None:
            loc = locate_decl(lines, c.decl)
        if loc is None:
            print("GONE %s — `%s` not found in %s at the new pin → re-port %s"
                  % (c.where(), c.decl, c.path, item))
            if not has_marker(c):
                edits.setdefault(c.rust_file, []).append(
                    (c.lineno, None, [marker(old, item, c.pfx)]))
            findings += 1
            continue
        na, nb = loc
        new_text = [l.rstrip() for l in lines[na - 1:nb]]
        newcite = Cite(c.rust_file, c.lineno, c.path, na, nb, c.decl, c.pfx)

        if old_text != new_text and olines is not None:
            # The cited range may already have been rewritten (a second
            # `update` for the same bump); fall back to the old pin's block
            # for this declaration.  This can only turn a spurious CHANGED
            # into a MOVED: if the text really changed, neither matches.
            oloc = locate_decl(olines, c.decl)
            if oloc is not None:
                alt = [l.rstrip() for l in olines[oloc[0] - 1:oloc[1]]]
                if alt == new_text:
                    old_text = alt

        if old_text is not None and old_text == new_text:
            if (na, nb) != (c.a, c.b):
                print("MOVED %s — %s %s:%s → :%s"
                      % (c.where(), c.decl, c.path, c.range, newcite.range))
                moved += 1
                edits.setdefault(c.rust_file, []).append(
                    (c.lineno, newcite.render, []))
            continue

        print("CHANGED %s %s → re-port %s (%s), re-run differential tests, "
              "re-prove %s_refines" % (c.path, c.decl, item, c.where(), item))
        for dl in difflib.unified_diff(
                old_text or [], new_text,
                fromfile="%s:%s@%s" % (c.path, c.range, old[:8]),
                tofile="%s:%d-%d@current" % (c.path, na, nb), lineterm=""):
            print("  " + dl)
        edits.setdefault(c.rust_file, []).append(
            (c.lineno, newcite.render,
             [] if has_marker(c) else [marker(old, item, c.pfx)]))
        findings += 1

    rewrite(edits)
    if findings:
        print("%d moved, %d need reconciling: re-port, re-test, re-prove, then "
              "delete the `CHANGED` marker lines (`check` fails while any "
              "remains)." % (moved, findings))
        return 1
    print("provenance: %d citation(s) relocated, nothing changed." % moved)
    return 0


def find_block(lines, block, near):
    """The 1-based (start, end) of the occurrence of `block` (a list of
    rstripped lines) in `lines` closest to line `near`, or None."""
    if not block:
        return None
    n = len(block)
    first = block[0]
    hits = [i for i in range(len(lines) - n + 1)
            if lines[i].rstrip() == first
            and [l.rstrip() for l in lines[i:i + n]] == block]
    if not hits:
        return None
    i = min(hits, key=lambda i: abs(i + 1 - near))
    return i + 1, i + n


def has_marker(cite, _cache={}):
    """Is a `CHANGED` marker already sitting right below this citation?"""
    if cite.rust_file not in _cache:
        try:
            with open(cite.rust_file, encoding="utf-8") as f:
                _cache[cite.rust_file] = f.read().split("\n")
        except OSError:
            _cache[cite.rust_file] = []
    lines = _cache[cite.rust_file]
    return cite.lineno < len(lines) and bool(MARKER_RE.match(lines[cite.lineno]))


def rust_item_of(cite):
    """The Rust item a citation sits on (for the alert and marker lines)."""
    try:
        with open(cite.rust_file, encoding="utf-8") as f:
            lines = f.read().split("\n")
    except OSError:
        return rel(cite.rust_file)
    for i in range(cite.lineno, min(cite.lineno + 20, len(lines))):
        m = ITEM_RE.match(lines[i])
        if m:
            it = RustItem(cite.rust_file, i + 1, m.group("kind"), lines[i], [], True)
            return "%s::%s" % (os.path.basename(cite.rust_file)[:-3], it.name())
    return rel(cite.rust_file)


def load_skips():
    """The deliberate-skip allowlist: ({(path, decl): reason}, malformed).

    A `<path> <decl> <reason>` line says the declaration is not to be ported
    and why; `<decl>` may be `*` for the whole file.  A line with no reason is
    malformed — the reason is the point of the file (DESIGN.md §3.7)."""
    skips, bad = {}, []
    full = os.path.join(REPO, SKIP_FILE)
    if not os.path.exists(full):
        return skips, bad
    with open(full, encoding="utf-8") as f:
        for i, raw in enumerate(f):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split(None, 2)
            if len(parts) < 3 or not parts[2].strip():
                bad.append((i + 1, line))
                continue
            path, decl, reason = parts[0], parts[1], parts[2].strip()
            if (path, decl) in skips:
                bad.append((i + 1, line + "  [duplicate]"))
                continue
            skips[(path, decl)] = reason
    return skips, bad


def cmd_coverage(args):
    _, cites, _, _ = collect(args.roots)
    by_file = {}
    for c in cites:
        by_file.setdefault(c.path, []).append(c)
    skips, bad = load_skips()
    findings = 0

    for lineno, line in bad:
        print("MALFORMED %s:%d — a skip needs `<path> <decl> <reason>`: %s"
              % (SKIP_FILE, lineno, line))
        findings += 1

    used = set()
    total = covered = skipped = 0
    for path in lean_files_for_coverage():
        lines = lean_text(path)
        if lines is None:
            continue
        decls = [(ln, kw, nm) for (ln, kw, nm) in top_level_decls(lines)
                 if kw in DEFINITIONAL]
        if not decls:
            continue
        mine = by_file.get(path, [])
        miss, skips_here, redundant = [], [], []
        ncov = 0
        for ln, kw, nm in decls:
            hit = any(c.a <= ln <= c.b or names_compatible(nm, c.decl) for c in mine)
            key = (path, nm) if (path, nm) in skips else (
                (path, "*") if (path, "*") in skips else None)
            if key:
                used.add(key)
            if hit:
                covered += 1
                ncov += 1
                total += 1
                if key:
                    redundant.append("%s %s:%d — skipped (%s) but cited"
                                     % (nm, path, ln,
                                        "file-wide" if key[1] == "*" else "by name"))
            elif key:
                skipped += 1
                skips_here.append((nm, ln, key))
            else:
                miss.append("%s %s:%d" % (nm, path, ln))
                total += 1
        port = len(decls) - len(skips_here)
        print("%-46s %3d/%-3d covered%s"
              % (path, ncov, port,
                 ("   %3d skipped" % len(skips_here)) if skips_here else ""))
        for m in miss:
            print("    uncovered %s" % m)
        # A file-wide skip is reported once, with the names it covers; a
        # per-declaration one with its own reason.
        wide = [nm for (nm, _ln, key) in skips_here if key[1] == "*"]
        if wide:
            print("    skipped   %s * (%d declarations) — %s"
                  % (path, len(wide), skips[(path, "*")]))
        for nm, ln, key in skips_here:
            if key[1] != "*":
                print("    skipped   %s %s:%d — %s" % (nm, path, ln, skips[key]))
        for r in redundant:
            print("    REDUNDANT %s" % r)
        findings += len(redundant)

    # A skip may name a file OUTSIDE `COVERAGE_GLOBS`: `Main.lean` and
    # `ConLeche/Frontend/**` are the CHERRIES, whose ledger is
    # `scripts/progress.py`'s second table (§3.7 — "later `Frontend/**`,
    # `Main.lean`"), so the TOTAL above stays the verified core's.  The
    # entries still have to be checked, or the list rots exactly where it is
    # longest: every unused key is validated against the file it NAMES, for
    # both findings — STALE if the declaration is not there, REDUNDANT if a
    # Rust item cites it after all (task #40, which closed the cherries).
    for key, reason in sorted(skips.items()):
        if key in used:
            continue
        path, decl = key
        lines = lean_text(path)
        decls = ([(ln, nm) for (ln, kw, nm) in top_level_decls(lines)
                  if kw in DEFINITIONAL]
                 if lines is not None else [])
        hit = [(ln, nm) for ln, nm in decls if decl == "*" or nm == decl]
        if not hit:
            print("STALE %s — `%s %s` names no declaration of that file"
                  % (SKIP_FILE, path, decl))
            findings += 1
            continue
        mine = by_file.get(path, [])
        for ln, nm in hit:
            if any(c.a <= ln <= c.b or names_compatible(nm, c.decl) for c in mine):
                print("REDUNDANT %s — `%s %s` is skipped (%s) but cited"
                      % (SKIP_FILE, path, nm,
                         "file-wide" if decl == "*" else "by name"))
                findings += 1

    pct = (100.0 * covered / total) if total else 0.0
    print("TOTAL %d/%d covered (%.1f%%), %d uncovered, %d deliberately "
          "skipped (%s)"
          % (covered, total, pct, total - covered, skipped, SKIP_FILE))
    if findings:
        print("%d skip-list finding(s)." % findings)
        return 1
    return 0


def cmd_locate(args):
    """Print the canonical citation body for each named declaration.

    `locate <path> <decl>…` is the locator `update` uses, exposed so that a
    *generator* can write citations no hand ever edits: `proof/ConRon/Gen`
    calls it for the raw pins each generated basis block is computed from, so
    the emitted `/// con-leche:` ranges are exactly the blocks `update` would
    relocate to and regeneration is a fixed point (task #33)."""
    lines = lean_text(args.path)
    if lines is None:
        print("error: %s is not in %s" % (args.path, CON_LECHE), file=sys.stderr)
        return 2
    rc = 0
    for decl in args.decls:
        loc = locate_decl(lines, decl)
        if loc is None:
            print("NOTFOUND %s %s" % (args.path, decl), file=sys.stderr)
            rc = 1
            continue
        a, b = loc
        rng = str(a) if a == b else "%d-%d" % (a, b)
        print("%s:%s %s" % (args.path, rng, decl))
    return rc


def main(argv):
    p = argparse.ArgumentParser(prog="provenance.py", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--roots", nargs="+", default=None,
                        help="Rust source trees to scan (default: %s)"
                             % " ".join(DEFAULT_ROOTS))
    p.add_argument("--roots", nargs="+", default=None, help=argparse.SUPPRESS)
    sub = p.add_subparsers(dest="cmd")
    sub.add_parser("check", parents=[common])
    up = sub.add_parser("update", parents=[common])
    up.add_argument("--old", default=None,
                    help="the con-leche commit the citations were written against")
    sub.add_parser("coverage", parents=[common])
    lc = sub.add_parser("locate", parents=[common])
    lc.add_argument("path", help="a con-leche-relative Lean path")
    lc.add_argument("decls", nargs="+", help="the declarations to locate")
    args = p.parse_args(argv)
    if args.roots is None:
        args.roots = list(DEFAULT_ROOTS)
    if args.cmd is None:
        p.print_help()
        return 2
    if not os.path.isdir(os.path.join(REPO, CON_LECHE, "ConLeche")):
        print("error: %s is missing (it is a vendored subtree since task #74; "
              "is this a partial checkout?)" % CON_LECHE, file=sys.stderr)
        return 2
    return {"check": cmd_check, "update": cmd_update,
            "coverage": cmd_coverage, "locate": cmd_locate}[args.cmd](args)


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except BrokenPipeError:
        sys.exit(0)
    except OSError as e:
        print("error: %s" % e, file=sys.stderr)
        sys.exit(2)
