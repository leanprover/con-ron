#!/usr/bin/env python3
"""scripts/provenance.py — THE PROVENANCE GATE (task #8, DESIGN.md §3.7).

Every Rust item Charon sees cites the con-leche lines it was ported from:

    /// con-leche: ConLeche/Kernel/Level.lean:82-89 leqCore

or, for an item with no Lean counterpart,

    /// con-leche: none — replaces the runtime's `Nat`; spec in NatSpec.lean

Since task #97 the same gate reads **Lean** sources: the arena checker (B)
of DESIGN.md §8 lives in `proof/ConRon/Arena/**` and is a port of con-leche
exactly as the Rust is, so every top-level `def`/`structure`/`inductive`/
`abbrev` there carries the citation as a doc line

    /-- con-leche: ConLeche/Kernel/Core.lean:120-200 whnfCore -/
    /-- con-leche: none — the store's own handle arithmetic -/

(`theorem`s may be uncited: they are the arena's own verification, not a
port of anything).  Everything else is the same — the same `check`,
`update` and `coverage`, the same `CHANGED` markers, the same
`(pin, path, range)` fact.  `coverage` keeps the two apart: the Rust
ledger's numbers are unchanged, and the arena's coverage of the same
con-leche declarations is a second group under it.

con-leche is a plain `lake` dependency of `proof/` (task #91), pinned by
`rev` in `proof/lakefile.toml`; `proof/lake-manifest.json`'s `con-leche`
entry is the single source of truth for the pin, and its checked-out work
tree lives wherever that manifest's `packagesDir` puts it (ordinarily
`proof/.lake/packages/con-leche`) once `lake update`/`lake build` has run in
`proof/`.  `(pin, path, range)` fixes the cited text, so no hash is needed
in the source.  `check` verifies every citation against the pinned package
and demands one on every item; `update --old <commit>` diffs the old pin
against the new one, relocates what merely moved and marks what changed
with a `CHANGED` marker line the porter deletes once reconciled (`update
--auto` also sorts the findings into buckets and takes the markers of the
mechanical ones back out, task #108 — see `BUCKETS`); `coverage`
prints the port ledger.  Pure source-tree work: no build, no network (once
the package is fetched), python3 stdlib only, milliseconds.

Exit codes: 0 clean, 1 findings, 2 usage/IO error.
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import subprocess
import sys

# The Rust trees that must be annotated, relative to the repository root.
# TWO roots since task #97-SWAP (§8.6's swap), which is one per crate that
# carries ported code:
# `crates/con-ron-core/src` is THE verified crate — the arena checker, the
# store-native parser and the pinned data — inside this gate and inside
# `lint-rust-style.sh`.  (`crates/arena-core/src` was the rewrite's second
# verified tree from task #97-P4a until the swap folded it in here.)
# `crates/con-ron/src` is the UNVERIFIED crate: the driver, the CLI and the
# pool (the in-process modeller and its `tree/` helpers went with upstream's,
# task #105).  It is inside this gate and outside
# `lint-rust-style.sh` and `extract.sh` on purpose: DESIGN.md §3.7 — "for the
# unverified frontend it is the only sync signal there is".  Its items are
# cited but not style-linted.  (`crates/con-ron-arena/src` was its arena-side
# twin from task #97-P4f until the swap put it here under this name.)
RUST_ROOTS = [
    "crates/con-ron-core/src",
    "crates/con-ron/src",
]

# The Lean trees that must be annotated: the arena checker (B) of DESIGN.md
# §8, a port of con-leche's `Kernel/*` and `Frontend/*` written in this
# repository.  It is source that is *ported*, so it is inside this gate; it
# is not Rust, so it is outside `lint-rust-style.sh` and `extract.sh`.  The
# directory does not exist before P2a lands, and an absent root is simply
# empty (as for the Rust roots).
ARENA_ROOTS = [
    "proof/ConRon/Arena",
]

# …minus the arena's own test and scratch code, which is exempt exactly as
# `#[cfg(test)]` and `mod tests` are on the Rust side: NOT SCANNED AT ALL —
# neither its declarations nor its citations reach `check`, and `coverage`
# (which reads the same scan) does not count them either.
#
#   * `StoreTest.lean` — the store's `#guard` fixtures.  Executable test
#     vectors for `Store.lean`, written against the twin, not ported from
#     any con-leche declaration: there is nothing for them to cite, and a
#     citation demanded of them would have to be invented.
#   * `Spike/**` — the throwaway experiments of DESIGN.md §8 (`Mini`,
#     `ExpA`/`ExpB`, the extracted `Spike/Generated`).  They exist to
#     answer one design question each and are deleted once it is answered;
#     holding scratch to the port's provenance discipline buys nothing and
#     would make every spike a documentation chore.
#
# Everything else under `ARENA_ROOTS` is the port, and carries citations.
# Prefix match on the repository-relative path, `/`-separated.
# (`Arena/Spike/` was deleted at task #97-SWAP-2, the question it answered
# being settled; the entry stays because `provenance-selftest.py` asserts the
# exemption set, and because the next spike goes back under that path.)
ARENA_EXEMPT = (
    "proof/ConRon/Arena/StoreTest.lean",
    "proof/ConRon/Arena/Spike/",
)

DEFAULT_ROOTS = RUST_ROOTS + ARENA_ROOTS

# con-leche is a plain lake dependency of proof/ (task #91): its checked-out
# package directory is resolved from proof/lake-manifest.json, not a fixed
# repository-relative path.  MANIFEST_FILE is the single source of truth for
# the pin; CON_LECHE is a display name only (error messages).
MANIFEST_FILE = "proof/lake-manifest.json"
CON_LECHE = "con-leche"
COVERAGE_GLOBS = ["ConLeche/Kernel", "ConLeche/Cached"]

# The allowlist of declarations that are deliberately NOT ported (task #33):
# `<path> <decl> <reason>` lines, `<decl>` possibly `*` for a whole file.
SKIP_FILE = "scripts/provenance-skip.txt"

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ------------------------------------------------------- the con-leche package


def _manifest_con_leche_entry(data):
    """The `con-leche` package entry in a decoded lake-manifest.json, or
    None.  Lake escapes a package name that is not a legal Lean identifier
    with `«»`; the directory on disk is the unescaped form
    (`Dependency.dirName`), so match on that."""
    for pkg in data.get("packages", []):
        if pkg.get("name", "").strip("«»") == "con-leche":
            return pkg
    return None


def con_leche_dir():
    """The absolute path of the con-leche lake package directory, resolved
    from `proof/lake-manifest.json` (task #91: con-leche is a plain lake
    dependency, not vendored) — or None if `lake update`/`lake build` has
    not been run in `proof/` yet, or the package is not there.

    `PROVENANCE_CON_LECHE_DIR` overrides it: the self-test's bucket fixture
    (task #108) is a two-commit git repository of its own, standing in for
    con-leche, so that `update --auto` can be run against a known bump."""
    env = os.environ.get("PROVENANCE_CON_LECHE_DIR")
    if env:
        return env if os.path.isdir(env) else None
    try:
        with open(os.path.join(REPO, MANIFEST_FILE), encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return None
    entry = _manifest_con_leche_entry(data)
    if entry is None:
        return None
    packages_dir = data.get("packagesDir", ".lake/packages")
    d = os.path.join(REPO, "proof", packages_dir, entry["name"].strip("«»"))
    return d if os.path.isdir(d) else None


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
# The same citation as a LEAN doc line, where the declaration name is
# usually not the end of the sentence: the arena writes the twin's delta
# from the cited code right there, after an em dash —
#
#     /-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the fuel-indexed
#     readback of a name. -/
#
# so `<decl>` may be followed by ` — <prose>` (or its ASCII spelling,
# ` -- <prose>`).  The prose is NOT part of the citation: nothing checks
# it, and `update` puts it back verbatim when it rewrites the range (see
# `Cite.prose`).  The RUST rule is unchanged — a `///` line still ends at
# the declaration name, because a Rust doc comment has the next line for
# prose and the one-line-per-citation shape is what task #8 fixed.
LEAN_CITE_RE = re.compile(
    r"^(?P<path>[^\s:]+):(?P<a>\d+)(?:-(?P<b>\d+))?\s+(?P<decl>\S+)"
    r"(?P<prose>\s+(?:—|--)(?:\s.*)?)?$"
)
NONE_RE = re.compile(r"^none\b")
# The `CHANGED` marker, in either language's comment syntax: `///`/`//!` in
# Rust, `--` or a doc comment's `/--` in Lean.
MARKER_RE = re.compile(r"^\s*(?://[/!]|/--|--)\s*con-leche:\s*CHANGED\b")


# The lemma a changed citation invalidates: the Rust port's exact-result
# lemma (DESIGN.md §3.5), or — for the arena checker (B) of §8 — the bridge
# lemma of Theorem 1 (§8.2, `Arena.checkDecl_bridge`).
LEMMA_SUFFIX = {"rust": "_refines", "arena": "_bridge"}


def marker(old, item, pfx="///", source="rust"):
    return ("%s con-leche: CHANGED since %s — re-port, re-test, re-prove "
            "%s%s, then delete this line"
            % (pfx, old[:8], item, LEMMA_SUFFIX[source]))


class Cite:
    """One `con-leche:` doc line: where it sits, and what it claims.

    `source` is `"rust"` or `"arena"` (a Lean file of `ARENA_ROOTS`).  A
    Lean citation may open a multi-line doc comment or sit inside one, so
    an arena citation remembers the exact text around its body (`head`,
    `tail`) and `render` puts the rewritten body back between them; a Rust
    one is rebuilt from its `pfx` as before.  `prose` is the ` — …` tail a
    Lean citation may carry after the declaration name (`LEAN_CITE_RE`):
    unchecked text that `render` must hand back untouched, since `update`
    rewrites only the RANGE and the porter's sentence is not its business.

    `rebase(a, b)` is how `update` makes the relocated citation: the same
    line with a new range, every other field — `source`, `head`, `prose`,
    `tail` — carried over, so a rewritten Lean citation keeps its doc
    comment and its sentence."""

    def __init__(self, rust_file, lineno, path, a, b, decl, pfx="///",
                 source="rust", head=None, tail="", prose=""):
        self.rust_file = rust_file  # absolute path of the .rs / .lean file
        self.lineno = lineno  # 1-based line of the annotation
        self.path = path  # con-leche-relative Lean path
        self.a = a
        self.b = b
        self.decl = decl
        self.pfx = pfx  # `///` (an item's) or `//!` (a whole module's); `--` in Lean
        self.source = source
        self.head = head if head is not None else pfx + " "
        self.tail = tail
        self.prose = prose

    @property
    def range(self):
        return str(self.a) if self.a == self.b else "%d-%d" % (self.a, self.b)

    def rebase(self, a, b, path=None):
        """This citation with the range `(a, b)` — and, for a declaration
        upstream moved to another file (`update --auto`, task #108), the
        path — everything else kept."""
        return Cite(self.rust_file, self.lineno, path or self.path, a, b,
                    self.decl, self.pfx, self.source, self.head, self.tail,
                    self.prose)

    def render(self, indent):
        if self.source == "arena":
            return "%s%scon-leche: %s:%s %s%s%s" % (
                indent, self.head, self.path, self.range, self.decl,
                self.prose, self.tail)
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
        self.source = "rust"
        self.needs_cite = True  # every Charon-visible Rust item, no exceptions

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


def source_files(roots, ext):
    out = []
    for root in roots:
        full = root if os.path.isabs(root) else os.path.join(REPO, root)
        if not os.path.isdir(full):
            continue
        for dirpath, dirnames, filenames in os.walk(full):
            dirnames[:] = [d for d in dirnames
                           if d not in ("target", ".git", ".lake")]
            for fn in sorted(filenames):
                if fn.endswith(ext):
                    out.append(os.path.join(dirpath, fn))
    return sorted(out)


def rust_files(roots):
    return source_files(roots, ".rs")


def arena_exempt(path):
    """Is this arena Lean file test or scratch code (`ARENA_EXEMPT`)?

    `path` may be absolute or repository-relative; a file outside the
    repository (the self-test's scratch copy of its fixture) is never
    exempt."""
    p = rel(path).replace(os.sep, "/")
    return any(p == e or p.startswith(e) for e in ARENA_EXEMPT)


def arena_files(roots):
    return [f for f in source_files(roots, ".lean") if not arena_exempt(f)]


# ------------------------------------------------------------ the arena scan
#
# The arena checker (B) of DESIGN.md §8 is Lean source in THIS repository that
# ports con-leche's `Kernel/*` and `Frontend/*`, so it carries the same
# provenance the Rust does.  The annotation is a doc line on the declaration:
#
#     /-- con-leche: ConLeche/Kernel/Name.lean:82-89 Name.beq -/
#     /-- con-leche: none — the store's own handle arithmetic -/
#
# and it may open a multi-line doc comment whose prose follows:
#
#     /-- con-leche: ConLeche/Kernel/Core.lean:120-200 whnfCore
#     The twin reads `view` where the pure body matches on the `Expr`. -/
#
# A bare `con-leche: …` line inside a doc comment counts too, so an item that
# merges several con-leche declarations lists them one per line.

LEAN_ANNOT_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<head>(?:/--|/-!|--)?[ \t]*)con-leche:[ \t]*"
    r"(?P<body>.*?)(?P<tail>[ \t]*-/)?[ \t]*$")

# Which top-level Lean declarations must carry a citation.  `theorem`, `lemma`
# and `example` need none: they are the arena's OWN verification (the store
# lemmas of P2a, the bridge of P3), not a port of a con-leche declaration.
# An anonymous `instance` has no name to cite and is exempt for the same
# reason `first_decl_line` calls it `_`.
LEAN_PROOF_KW = ("theorem", "lemma", "example")


class LeanItem:
    """One top-level declaration of an arena source file."""

    def __init__(self, file, lineno, kind, name, cites):
        self.file = file
        self.lineno = lineno
        self.kind = kind
        self._name = name
        self.cites = cites  # list[Cite | None]; None = an explicit `none`
        self.source = "arena"
        self.needs_cite = kind not in LEAN_PROOF_KW and name != "_"

    def name(self):
        return self._name


def lean_block_start(lines, idx):
    """The 0-based left edge of the declaration block at `idx`: its
    attributes and doc comment, plus any `--` line comments sitting between
    them and the declaration.

    `extend_block` stops at a `--` line, which is right for con-leche's own
    tree but wrong here: `update` inserts its `CHANGED` marker as exactly
    such a line, right below the citation, and the citation it marks must
    stay attached to the item it marks (else a marked item reads as
    UNCITED as well, which is noise on an already-red run)."""
    j = idx - 1
    while j >= 0 and lines[j].startswith("--"):
        j -= 1
    return extend_block(lines, j + 1)[0] - 1


def scan_lean_file(path):
    """Return (items, cites, markers) for one arena `.lean` file.

    Items are the column-0 declarations; a citation belongs to the item whose
    attribute-and-doc-comment block (`extend_block`'s left edge) it sits in."""
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")

    skip = comment_lines(lines)
    cites, markers, parsed = [], [], {}

    for idx, raw in enumerate(lines):
        m = LEAN_ANNOT_RE.match(raw)
        if not m:
            continue
        body = m.group("body")
        if MARKER_RE.match(raw):
            markers.append((path, idx + 1, body))
            continue
        if NONE_RE.match(body):
            parsed[idx] = None
            continue
        c = LEAN_CITE_RE.match(body)
        if not c:
            bad = ("malformed", path, idx + 1, body)
            parsed[idx] = bad
            cites.append(bad)
            continue
        cite = Cite(path, idx + 1, c.group("path"), int(c.group("a")),
                    int(c.group("b") or c.group("a")), c.group("decl"),
                    pfx="--", source="arena",
                    head=m.group("head"), tail=m.group("tail") or "",
                    prose=c.group("prose") or "")
        parsed[idx] = cite
        cites.append(cite)

    items = []
    for idx, raw in enumerate(lines):
        got = decl_name_at(lines, idx, skip)
        if got is None:
            if ANON_INSTANCE_RE.match(raw) and idx not in skip:
                got = ("instance", "_")
            else:
                continue
        kw, nm = got
        blk = lean_block_start(lines, idx)
        mine = [parsed[j] for j in sorted(parsed) if blk <= j < idx]
        items.append(LeanItem(path, idx + 1, kw, nm,
                              ["malformed" if isinstance(c, tuple) else c
                               for c in mine]))
    return items, cites, markers


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
    """The Lean file's lines: from the con-leche package directory's checked-
    out work tree, or from `old` — a con-leche commit, read from that
    directory's git history (lake clones the full repository, not a
    shallow one, so any commit it has ever pointed at is there)."""
    d = con_leche_dir()
    if d is None:
        return None
    if old is None:
        full = os.path.join(d, path)
        if not os.path.exists(full):
            return None
        with open(full, encoding="utf-8") as f:
            return f.read().split("\n")
    r = subprocess.run(["git", "-C", d, "show", "%s:%s" % (old, path)],
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
    d = con_leche_dir()
    if d is None:
        return []
    out = []
    for sub in COVERAGE_GLOBS:
        base = os.path.join(d, sub)
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(dirnames)
            for fn in sorted(filenames):
                if fn.endswith(".lean"):
                    full = os.path.join(dirpath, fn)
                    out.append(os.path.relpath(full, d))
        lone = base + ".lean"
        if os.path.exists(lone):
            out.append(os.path.relpath(lone, d))
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
    """Every annotated item and citation under `roots`, Rust and arena Lean
    alike.  A file is scanned by its extension, so one root list may mix the
    two (the default one does)."""
    items, cites, malformed, markers = [], [], [], []
    scans = ([(f, scan_rust_file) for f in rust_files(roots)]
             + [(f, scan_lean_file) for f in arena_files(roots)])
    for f, scan in sorted(scans):
        it, ci, mk = scan(f)
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
    for f in {it.file for it in items if it.source == "rust"}:
        for line in open(f, encoding="utf-8"):
            if MODULE_ANNOT_RE.match(line):
                module_annot.add(f)
                break
    for it in items:
        if not it.needs_cite:
            continue  # an arena `theorem`: the port's own verification
        if not it.cites and it.file not in module_annot:
            print("UNCITED %s:%d — `%s %s` has no `con-leche:` line"
                  % (rel(it.file), it.lineno, it.kind, it.name()))
            findings += 1

    if findings:
        print("%d finding(s)." % findings)
        return 1
    nr = sum(1 for it in items if it.source == "rust")
    print("provenance: %d item(s) (%d Rust, %d arena Lean), %d citation(s), "
          "all current at pin %s."
          % (len(items), nr, len(items) - nr, len(cites),
             (current_submodule_commit() or "?")[:8]))
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


def recorded_submodule_commit():
    """The con-leche commit recorded in HEAD's `proof/lake-manifest.json` —
    the `old` side of an uncommitted bump.  The name predates task #91;
    con-leche has been a vendored submodule and a vendored subtree before it
    was a plain lake dependency, and this is still "the pin as committed"."""
    r = subprocess.run(["git", "-C", REPO, "show", "HEAD:" + MANIFEST_FILE],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return None
    try:
        data = json.loads(r.stdout)
    except ValueError:
        return None
    entry = _manifest_con_leche_entry(data)
    return entry.get("rev") if entry else None


def current_submodule_commit():
    """The con-leche commit: `rev` in the working tree's
    `proof/lake-manifest.json` (which `lake update` writes)."""
    try:
        with open(os.path.join(REPO, MANIFEST_FILE), encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return None
    entry = _manifest_con_leche_entry(data)
    return entry.get("rev") if entry else None


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


# ------------------------------------------- the bump classifier (task #108)
#
# `update --auto` is task #105's `classify.py` + `apply-mech.py` and task
# #106's hand deletion of 97 doc-only markers, made part of the gate.  It
# runs the plain `update` (relocate what moved, mark what changed), sorts
# every finding into one of the buckets below, and then takes the markers of
# the MECHANICAL buckets back out.  What is left marked is the work order.
#
#   bucket         what it is                                       marker
#   doc-only       comment-stripped text identical (a docstring      deleted
#                  or `--` comment edit, nothing else)
#   moved          a GONE declaration found, by its exact qualified   deleted,
#                  name, in another file, byte-identical              citation repointed
#   moved-doc      the same, identical up to comments                 deleted, repointed
#   moved-changed  the same, but the code changed                     kept, repointed
#   moved-by-name  only the short name is found elsewhere (another    kept
#                  namespace), or the qualified name more than once:
#                  not trusted as a move — a deletion until a human
#                  says otherwise
#   changed        really changed (the code, not just the comments)   kept
#   deleted        gone upstream                                      kept
#
# The hunt is EXACT (task #98's warning): a declaration is found by its
# namespace-qualified name, never by `names_compatible`, which lets a
# citation of `Expr.beqGo` land on the `Expr` inductive.  The same warning
# is why `update` (with or without `--auto`) no longer accepts a relocation
# by name that matched only a strict PREFIX of the cited name, unless the
# citation already sat on that parent at the old pin (a `where` clause).

BUCKETS = [
    ("doc-only", True, "marker deleted"),
    ("moved", True, "citation repointed, marker deleted"),
    ("moved-doc", True, "citation repointed, marker deleted"),
    ("moved-changed", False, "citation repointed, marker kept: the port"),
    ("moved-by-name", False, "marker kept: a deletion unless a human finds the move"),
    ("changed", False, "marker kept: the port"),
    ("deleted", False, "marker kept: the port, delete all the way down"),
]
MECHANICAL = {b for b, mech, _ in BUCKETS if mech}


def strip_comments(lines):
    """A block's code: every `/- … -/` (nested, doc comments included) and
    every `-- …` comment removed, string literals respected, trailing blanks
    and empty lines dropped.  Two blocks with the same code compare equal
    here whatever their docstrings say (task #105's doc-only test, with
    task #106's `--` comments)."""
    text = "\n".join(lines)
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth:
            if two == "/-":
                depth, i = depth + 1, i + 2
            elif two == "-/":
                depth, i = depth - 1, i + 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if two == "/-":
            depth, i = 1, i + 2
            continue
        if two == "--":
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
            continue
        out.append(text[i])
        i += 1
    return [l.rstrip() for l in "".join(out).split("\n") if l.strip()]


SCOPE_RE = re.compile(
    r"^(?:(?:noncomputable|public|private)\s+)*(?P<kw>namespace|section)\b[ \t]*(?P<name>\S*)")
MUTUAL_RE = re.compile(r"^mutual\b")
END_RE = re.compile(r"^end\b")


def qualified_decls(lines):
    """[(0-based line, qualified name, written name)] for every column-0
    declaration: the written name under the `namespace`s open at that line
    (`_root_.` taken off).  `section`s and `mutual` blocks are tracked only
    so that their `end` closes the right scope."""
    skip = comment_lines(lines)
    stack, out = [], []
    for i, line in enumerate(lines):
        if i in skip or not line or line[:1].isspace():
            continue
        m = SCOPE_RE.match(line)
        if m:
            stack.append((m.group("kw"), m.group("name")))
            continue
        if MUTUAL_RE.match(line):
            stack.append(("mutual", ""))
            continue
        if END_RE.match(line):
            if stack:
                stack.pop()
            continue
        got = decl_name_at(lines, i, skip)
        if not got:
            continue
        nm = got[1]
        if nm.startswith("_root_."):
            q = nm[len("_root_."):]
        else:
            q = ".".join([s for k, s in stack if k == "namespace" and s] + [nm])
        out.append((i, q, nm))
    return out


def decl_head(lines, a, b):
    """(0-based line, qualified name, written name) of the first declaration
    inside the 1-based range `a..b`, or None."""
    for i, q, nm in qualified_decls(lines):
        if a - 1 <= i <= b - 1:
            return i, q, nm
        if i > b - 1:
            break
    return None


class TreeIndex:
    """Every declaration of the new con-leche tree by qualified name, and by
    the last component of its name — the move hunt's two lookups."""

    def __init__(self):
        self.by_q, self.by_short, self.files = {}, {}, {}
        d = con_leche_dir()
        for dirpath, dirnames, filenames in os.walk(d):
            dirnames[:] = sorted(x for x in dirnames
                                 if x not in (".lake", ".git", "tests"))
            for fn in sorted(filenames):
                if not fn.endswith(".lean"):
                    continue
                path = os.path.relpath(os.path.join(dirpath, fn), d)
                lines = lean_text(path)
                if lines is None:
                    continue
                self.files[path] = lines
                for i, q, nm in qualified_decls(lines):
                    self.by_q.setdefault(q, []).append((path, i))
                    self.by_short.setdefault(q.split(".")[-1], []).append((path, i))


def suspect_parent(lines, olines, c, loc):
    """Did `locate_decl` put this citation on a strict PREFIX of its name —
    `Expr.beqGo` on the `Expr` inductive (task #98) — when it did not sit on
    that parent at the old pin?  Then it is not a relocation."""
    head = first_decl_line(lines, loc[0], loc[1])
    if head is None or head == c.decl:
        return False
    hs, xs = head.split("."), c.decl.split(".")
    if not (len(hs) < len(xs) and xs[:len(hs)] == hs):
        return False
    if olines is not None and 1 <= c.a <= c.b <= len(olines):
        if first_decl_line(olines, c.a, c.b) == head:
            return False  # a `where` clause, cited on its parent all along
    return True


def hunt(index, olines, c, old_text):
    """A GONE citation, looked for across the whole new tree by the exact
    qualified name of what it cited at the old pin.  Returns
    (bucket, new_path, a, b, note).

    A declaration whose qualified name is not found, but whose SHORT name
    is, counts as moved only when the text there is the old text (up to
    comments): identical code under a moved namespace is the same
    declaration (`Frontend/InModel/Kit.lean`'s `piBinders` →
    `Kernel/Inductives/FieldTele.lean`, task #105), while a name match
    over different code is exactly task #98's trap, and stays a deletion
    until a human says otherwise (`moved-by-name`)."""
    head = None
    if olines is not None and 1 <= c.a <= c.b <= len(olines):
        head = decl_head(olines, c.a, c.b)
    if head is None:
        return "deleted", None, None, None, "no declaration in the old block"
    oi, q, _nm = head
    oa, ob = extend_block(olines, oi)
    olds = [o for o in (old_text, [l.rstrip() for l in olines[oa - 1:ob]]) if o]

    def compare(path, i):
        """(bucket, a, b) of the candidate at `path`, 0-based line `i`."""
        lines = index.files[path]
        exact = find_block(lines, old_text, i + 1) if old_text else None
        if exact:
            return "moved", exact[0], exact[1]
        a, b = extend_block(lines, i)
        new = [l.rstrip() for l in lines[a - 1:b]]
        if any(o == new for o in olds):
            return "moved", a, b
        if any(strip_comments(o) == strip_comments(new) for o in olds):
            return "moved-doc", a, b
        return "moved-changed", a, b

    def where(hits):
        return ", ".join("%s:%d" % (p, i + 1) for p, i in hits[:5])

    hits = index.by_q.get(q, [])
    if len(hits) == 1:
        bucket, a, b = compare(*hits[0])
        return bucket, hits[0][0], a, b, q
    # several declarations of that qualified name (a `private` one in two
    # files), or none: only a candidate whose text is the old one is a move
    cands = hits or index.by_short.get(q.split(".")[-1], [])
    same = [(h, compare(*h)) for h in cands]
    same = [(h, r) for h, r in same if r[0] in ("moved", "moved-doc")]
    if len(same) == 1:
        (path, _i), (bucket, a, b) = same[0]
        return bucket, path, a, b, "%s, %s; the text %s" % (
            q, "declared %d times" % len(hits) if hits else "under another namespace",
            "identical" if bucket == "moved" else "identical up to comments")
    if hits:
        return ("moved-by-name", None, None, None, "%s declared %d times: %s"
                % (q, len(hits), where(hits)))
    if cands:
        return ("moved-by-name", None, None, None, "only the short name, "
                "over different code: %s" % where(cands))
    return "deleted", None, None, None, q


def part_of(path):
    """Which part of con-ron a citing file belongs to (the findings TSV's
    second column, task #105's "citing parts")."""
    r = rel(path).replace(os.sep, "/")
    for pfx, name in (("crates/con-ron-core/", "rust-core"),
                      ("crates/con-ron/", "rust-unverified"),
                      ("proof/ConRon/Arena/", "twin")):
        if r.startswith(pfx):
            return name
    return "other"


def cmd_update(args):
    old = args.old
    if old is None:
        rec, cur = recorded_submodule_commit(), current_submodule_commit()
        if rec and cur and rec != cur:
            old = rec
        else:
            print("usage: no uncommitted bump of the con-leche pin (the "
                  "manifest's rev matches HEAD's); pass --old <commit>",
                  file=sys.stderr)
            return 2
    auto = args.auto

    _, cites, malformed, markers = collect(args.roots)
    findings = len(malformed)
    for _, path, lineno, body in malformed:
        print("MALFORMED %s:%d — %s" % (rel(path), lineno, body))
    for path, lineno, body in markers:
        print("UNRECONCILED %s:%d — %s" % (rel(path), lineno, body))
        findings += 1

    edits = {}
    moved = 0
    records = []  # (bucket, cite, item, newcite or None, note)
    index = TreeIndex() if auto else None
    cache, oldcache = {}, {}

    def mark(c, item, newcite, bucket, note=""):
        edits.setdefault(c.rust_file, []).append(
            (c.lineno, newcite.render if newcite is not None else None,
             [] if has_marker(c) else [marker(old, item, c.pfx, c.source)]))
        records.append((bucket, c, item, newcite, note))

    def gone(c, item, olines, old_text, why):
        if not auto:
            print("GONE %s — %s → re-port %s" % (c.where(), why, item))
            mark(c, item, None, "deleted")
            return
        bucket, path, a, b, note = hunt(index, olines, c, old_text)
        newcite = c.rebase(a, b, path) if path else None
        print("GONE %s — %s; %s%s → %s"
              % (c.where(), why, bucket,
                 (" to %s:%s" % (path, newcite.range)) if newcite else "",
                 note))
        mark(c, item, newcite, bucket, note)

    for c in cites:
        if c.path not in cache:
            cache[c.path] = lean_text(c.path)
        if c.path not in oldcache:
            oldcache[c.path] = lean_text(c.path, old=old)
        lines, olines = cache[c.path], oldcache[c.path]
        item = item_of(c)

        old_text = None
        if olines is not None and 1 <= c.a <= c.b <= len(olines):
            old_text = [l.rstrip() for l in olines[c.a - 1:c.b]]

        if lines is None:
            gone(c, item, olines, old_text,
                 "%s no longer exists at the new pin" % c.path)
            findings += 1
            continue

        # Relocate by text first: the cited block, verbatim, nearest to where
        # it was.  This is what makes an anonymous `_` citation (an
        # `instance`) survive a bump — `locate_decl` cannot tell one `_` from
        # another — and it is the honest test for every citation: the text
        # is what the citation fixes (task #74, the first real bump).
        loc = find_block(lines, old_text, c.a) if old_text else None
        if loc is None:
            loc = locate_decl(lines, c.decl)
            if loc is not None and suspect_parent(lines, olines, c, loc):
                loc = None  # `Expr.beqGo` is not the `Expr` inductive (#98)
        if loc is None:
            gone(c, item, olines, old_text,
                 "`%s` not found in %s at the new pin" % (c.decl, c.path))
            findings += 1
            continue
        na, nb = loc
        new_text = [l.rstrip() for l in lines[na - 1:nb]]
        # `rebase`, not a fresh `Cite`: the rewrite changes the RANGE and
        # nothing else, so a Lean citation keeps its `/--` head, its `-/`
        # closer and the porter's ` — …` sentence after the name.
        newcite = c.rebase(na, nb)

        old_alt = None
        if old_text != new_text and olines is not None:
            # The cited range may already have been rewritten (a second
            # `update` for the same bump); fall back to the old pin's block
            # for this declaration.  This can only turn a spurious CHANGED
            # into a MOVED: if the text really changed, neither matches.
            oloc = locate_decl(olines, c.decl)
            if oloc is not None:
                old_alt = [l.rstrip() for l in olines[oloc[0] - 1:oloc[1]]]
                if old_alt == new_text:
                    old_text = old_alt

        if old_text is not None and old_text == new_text:
            if (na, nb) != (c.a, c.b):
                print("MOVED %s — %s %s:%s → :%s"
                      % (c.where(), c.decl, c.path, c.range, newcite.range))
                moved += 1
                edits.setdefault(c.rust_file, []).append(
                    (c.lineno, newcite.render, []))
            continue

        bucket = "changed"
        if auto:
            code = strip_comments(new_text)
            if any(o is not None and strip_comments(o) == code
                   for o in (old_text, old_alt)):
                bucket = "doc-only"
        print("CHANGED %s %s → re-port %s (%s), re-run differential tests, "
              "re-prove %s%s%s" % (c.path, c.decl, item, c.where(), item,
                                   LEMMA_SUFFIX[c.source],
                                   " [doc-only]" if bucket == "doc-only" else ""))
        if bucket != "doc-only":
            for dl in difflib.unified_diff(
                    old_text or [], new_text,
                    fromfile="%s:%s@%s" % (c.path, c.range, old[:8]),
                    tofile="%s:%d-%d@current" % (c.path, na, nb), lineterm=""):
                print("  " + dl)
        mark(c, item, newcite, bucket)
        findings += 1

    rewrite(edits)
    if auto:
        return finish_auto(args, old, edits, records, moved, findings)
    if findings:
        print("%d moved, %d need reconciling: re-port, re-test, re-prove, then "
              "delete the `CHANGED` marker lines (`check` fails while any "
              "remains)." % (moved, findings))
        return 1
    print("provenance: %d citation(s) relocated, nothing changed." % moved)
    return 0


def finish_auto(args, old, edits, records, moved, findings):
    """`update --auto`'s second half: every finding is marked on disk now,
    as a plain `update` leaves it; report `progress.py`'s stale count at
    that moment (§7: the only moment it means anything), take the markers
    of the mechanical buckets back out, and print the bucket table and the
    findings TSV."""
    stale = "n/a (not the default roots)"
    if sorted(args.roots) == sorted(DEFAULT_ROOTS):
        prog = subprocess.run([sys.executable,
                               os.path.join(REPO, "scripts", "progress.py"),
                               "--summary"], capture_output=True, text=True)
        m = re.search(r"stale \(CHANGED marker\) (\d+)", prog.stdout)
        stale = m.group(1) if m else "?"

    # Where each citation line sits after `rewrite`: above it, `rewrite`
    # inserted one marker line per earlier marked citation of the same file.
    def final_lineno(f, ln):
        return ln + sum(len(ins) for (l, _r, ins) in edits.get(f, []) if l < ln)

    drop = {}
    for bucket, c, _item, _nc, _note in records:
        if bucket in MECHANICAL:  # a re-run's old marker sits there too
            drop.setdefault(c.rust_file, []).append(final_lineno(c.rust_file, c.lineno))
    for f, lns in drop.items():
        with open(f, encoding="utf-8") as fh:
            lines = fh.read().split("\n")
        for ln in sorted(lns, reverse=True):
            # 0-based index `ln` is the line right below the citation
            if ln < len(lines) and MARKER_RE.match(lines[ln]):
                del lines[ln]
            else:
                print("error: no marker below %s:%d to delete" % (rel(f), ln),
                      file=sys.stderr)
                return 2
        with open(f, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines))

    counts = {b: 0 for b, _, _ in BUCKETS}
    for r in records:
        counts[r[0]] += 1
    tsv = args.tsv
    if tsv:
        os.makedirs(os.path.dirname(os.path.abspath(tsv)), exist_ok=True)
        with open(tsv, "w", encoding="utf-8") as fh:
            fh.write("bucket\tpart\twhere\titem\told\tnew\tnote\n")
            for bucket, c, item, nc, note in records:
                fh.write("%s\t%s\t%s\t%s\t%s:%s %s\t%s\t%s\n" % (
                    bucket, part_of(c.rust_file), c.where(), item,
                    c.path, c.range, c.decl,
                    "%s:%s" % (nc.path, nc.range) if nc is not None else "-",
                    note))
    print()
    print("update --auto: %d finding(s) against %s (%d CHANGED, %d GONE), "
          "%d citation(s) merely moved; progress.py's stale (CHANGED marker) "
          "count before any marker was deleted: %s"
          % (len(records), old[:8],
             sum(1 for r in records if r[0] in ("doc-only", "changed")),
             sum(1 for r in records if r[0] not in ("doc-only", "changed")),
             moved, stale))
    print()
    print("| bucket | count | what happened |")
    print("|---|---:|---|")
    for b, _mech, what in BUCKETS:
        print("| %s | %d | %s |" % (b, counts[b], what))
    left = sum(counts[b] for b in counts if b not in MECHANICAL)
    print()
    print("%d marker(s) deleted mechanically, %d left: the work order%s."
          % (len(records) - left, left, (" (%s)" % tsv) if tsv else ""))
    return 1 if (left or findings > len(records)) else 0


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


def item_of(cite):
    """The item a citation sits on (for the alert and marker lines).  A Rust
    one is `<module>::<name>`, an arena Lean one `<Module>.<name>`."""
    try:
        with open(cite.rust_file, encoding="utf-8") as f:
            lines = f.read().split("\n")
    except OSError:
        return rel(cite.rust_file)
    if cite.source == "arena":
        skip = comment_lines(lines)
        for i in range(cite.lineno, len(lines)):
            got = decl_name_at(lines, i, skip)
            if got:
                return "%s.%s" % (os.path.basename(cite.rust_file)[:-5], got[1])
        return rel(cite.rust_file)
    for i in range(cite.lineno, min(cite.lineno + 20, len(lines))):
        m = ITEM_RE.match(lines[i])
        if m:
            it = RustItem(cite.rust_file, i + 1, m.group("kind"), lines[i], [], True)
            return "%s::%s" % (os.path.basename(cite.rust_file)[:-3], it.name())
    return rel(cite.rust_file)


# The name before task #97, when every citation sat on a Rust item.
rust_item_of = item_of


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


def arena_group(cites, skips):
    """The arena checker's own ledger (task #97): how much of the same
    con-leche declarations (B), the Lean arena checker of DESIGN.md §8, has
    citations for.

    It is a SECOND GROUP, printed under the Rust ledger and counted apart —
    `scripts/progress.py` reads it the same way, as its "Arena checker
    (Lean)" group.  Merging the two would be a lie in both directions: an
    arena twin is not a ported Rust item, and a Rust item is not a twin.

    The denominator is the Rust ledger's, so the two columns are comparable:
    the definitional declarations of `COVERAGE_GLOBS` less the deliberate
    skips.  A skipped declaration the arena cites anyway is counted in
    `beyond` and is NOT a finding — `scripts/provenance-skip.txt` says what
    the RUST port does not carry, which is a different question from what
    the arena needs."""
    by_file = {}
    for c in cites:
        by_file.setdefault(c.path, []).append(c)
    rows, total = [], 0
    covered = beyond = 0
    for path in lean_files_for_coverage():
        lines = lean_text(path)
        if lines is None:
            continue
        decls = [(ln, kw, nm) for (ln, kw, nm) in top_level_decls(lines)
                 if kw in DEFINITIONAL]
        if not decls:
            continue
        mine = by_file.get(path, [])
        ncov = nport = 0
        for ln, _kw, nm in decls:
            hit = any(c.a <= ln <= c.b or names_compatible(nm, c.decl)
                      for c in mine)
            is_skip = (path, nm) in skips or (path, "*") in skips
            if is_skip:
                if hit:
                    beyond += 1
                continue
            nport += 1
            total += 1
            if hit:
                ncov += 1
                covered += 1
        rows.append((path, ncov, nport))
    return rows, covered, total, beyond


def cmd_coverage(args):
    _, cites, _, _ = collect(args.roots)
    arena_cites = [c for c in cites if c.source == "arena"]
    # The Rust ledger below is the Rust port's, exactly as before task #97:
    # an arena citation credits no Rust item.
    cites = [c for c in cites if c.source == "rust"]
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

    # The arena checker (B), DESIGN.md §8 — its own group, over the same
    # denominator, printed only once it exists.
    if arena_cites:
        rows, acov, atot, beyond = arena_group(arena_cites, skips)
        print()
        print("Arena checker (Lean) — (B) of DESIGN.md §8, %s"
              % " ".join(ARENA_ROOTS))
        for path, ncov, nport in rows:
            if ncov:
                print("%-46s %3d/%-3d twinned" % (path, ncov, nport))
        apct = (100.0 * acov / atot) if atot else 0.0
        print("ARENA TOTAL %d/%d twinned (%.1f%%), %d to go%s"
              % (acov, atot, apct, atot - acov,
                 (", %d beyond the Rust port's denominator" % beyond)
                 if beyond else ""))

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


def cmd_dir(args):
    """Print the con-leche lake package directory (task #91): the one place
    a shell script needs to resolve to read con-leche's tree — `gen-pins.sh`,
    `gen-prelude.sh`, `diff-e2e.sh` and `overview-links.sh` all shell out to
    `python3 scripts/provenance.py dir` rather than hard-coding a path."""
    print(con_leche_dir())
    return 0


def cmd_pin(args):
    """Print the pinned con-leche commit from the working tree's
    `proof/lake-manifest.json` — unlike every other subcommand, this reads
    only that (committed, always-present) file, not the package directory
    itself, so it works before `lake update`/`lake build` has ever run (a
    fresh checkout, or CI computing a cache key for the clone it is about to
    do)."""
    rev = current_submodule_commit()
    if rev is None:
        print("error: no con-leche entry in %s" % MANIFEST_FILE, file=sys.stderr)
        return 2
    print(rev)
    return 0


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
    up.add_argument("--auto", action="store_true",
                    help="classify the findings into buckets and apply the "
                         "mechanical ones (task #108)")
    up.add_argument("--tsv", default=None,
                    help="with --auto: write the findings, one per line, here")
    sub.add_parser("coverage", parents=[common])
    lc = sub.add_parser("locate", parents=[common])
    lc.add_argument("path", help="a con-leche-relative Lean path")
    lc.add_argument("decls", nargs="+", help="the declarations to locate")
    sub.add_parser("dir", parents=[common])
    sub.add_parser("pin", parents=[common])
    args = p.parse_args(argv)
    if args.roots is None:
        args.roots = list(DEFAULT_ROOTS)
    if args.cmd is None:
        p.print_help()
        return 2
    if args.cmd != "pin":  # `pin` reads only the manifest, not the package
        d = con_leche_dir()
        if d is None or not os.path.isdir(os.path.join(d, "ConLeche")):
            print("error: the con-leche lake package is not available "
                  "(task #91: a plain lake dependency, not vendored); "
                  "run `lake update` (or `lake build`) in proof/", file=sys.stderr)
            return 2
    return {"check": cmd_check, "update": cmd_update, "coverage": cmd_coverage,
            "locate": cmd_locate, "dir": cmd_dir, "pin": cmd_pin}[args.cmd](args)


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except BrokenPipeError:
        sys.exit(0)
    except OSError as e:
        print("error: %s" % e, file=sys.stderr)
        sys.exit(2)
