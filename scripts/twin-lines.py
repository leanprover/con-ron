#!/usr/bin/env python3
"""scripts/twin-lines.py — THE TWIN-LINE GATE (task #97-TWIN, DESIGN.md §3.7).

`scripts/provenance.py` keeps the Rust honest about con-leche, the thing it
was ported FROM.  This gate keeps it honest about the arena checker's Lean,
the thing it is a port OF — the second half of the same `///` block:

    /// con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
    /// Lean twin: `proof/ConRon/Arena/ExprOps.lean:277-303 instantiate1Go` —
    /// the `bvar` substitution's fuel step.

One Rust function cites ONE twin, and for a walk that task #97-P3-1 split
into a dispatcher and one `def` per constructor arm that twin is the
DISPATCHER: the arms are the twin's own shape (a Lean proof obligation per
arm), not a second ledger the Rust has to mirror.

A `Lean twin:` line names a declaration of `proof/ConRon/**`, and it is a
`(path, range, name)` fact exactly as a con-leche citation is — except that
this side of the ledger moves under us, because it is OUR file and every
task edits it.  Nothing read those ranges until now, so they rotted: task
#97-P3-1's arm split moved every function in `Arena/ExprOps.lean` and said
so in DESIGN ("the Rust is untouched, and owes a repoint"), and the ranges
were already stale before that round.

Two modes, both pure source-tree work — no build, no network, python3
stdlib only, milliseconds:

  `check`   every `Lean twin:` citation resolves: the `.lean` file exists,
            it has a TOP-LEVEL declaration (`def`/`theorem`/`structure`/…)
            whose name answers to the cited one, and that declaration's
            block contains the cited lines.  This is a gate step.

  `update`  relocate by NAME: rewrite the range of every citation whose
            declaration has moved, leaving the path, the name and the
            porter's prose exactly as they are.  Only the digits change, so
            no doc block is ever rewrapped and the generated model's
            `Source: … lines A:0-B:1` records do not move.  A citation whose
            NAME is gone is reported as `GONE` and NOT rewritten: a vanished
            twin is a porting decision (which dispatcher, which renamed
            helper), and the script must not guess it.

The convention the ranges follow is `provenance.py`'s: a declaration's range
is its BLOCK — its doc comment and attributes down to the line before the
next top-level declaration — which is what `provenance.locate_decl` returns.
`check` is laxer than `update`: it accepts any range inside the block, so a
hand-narrowed citation (one clause of a long walk) survives.

Not every `Lean twin:` line is a citation, and the ones that are not are
skipped rather than failed:

  * `Lean twin: none — <why>` and `**none owed** — <why>`: there is no twin
    (DESIGN.md's task #97-SWAP §6 lists the four, plus the arena's own
    infrastructure);
  * a bare `proof/ConRon/Arena/Store.lean` with no declaration name — "the
    persistent arm of `NStore.view`" and its eleven siblings, which are a
    branch of a twin rather than a twin.  The FILE is still checked.

Exit codes: 0 clean, 1 findings, 2 usage/IO error.
"""

from __future__ import annotations

import argparse
import importlib.util
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)

# The Rust trees that carry `Lean twin:` lines: the verified crate's arena
# and store-native frontend (task #97-SWAP's file map), and `in_model.rs`,
# the one module of the unverified crate that has a twin (the in-process
# modeller's readback, task #97-P4f).  Handed the whole of `crates/` this
# would find the same set; naming the roots keeps the gate's subject fixed.
ROOTS = (
    "crates/con-ron-core/src/arena",
    "crates/con-ron-core/src/frontend",
    "crates/con-ron/src",
)


def _load_provenance():
    """`provenance.py` as a module: its Lean parser is this gate's too.

    `comment_lines`, `decl_name_at`, `extend_block`, `locate_decl` and
    `names_compatible` already know what a top-level Lean declaration is,
    that a `/-! … -/` section header belongs to no declaration, that a
    citation may drop or add a namespace, and that a `where` clause is part
    of its parent's block.  One parser, one set of rules, one fixture."""
    spec = importlib.util.spec_from_file_location(
        "provenance", os.path.join(HERE, "provenance.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


P = _load_provenance()


def _memoise_comment_lines():
    """`provenance.comment_lines` scans a file character by character, and
    `locate_decl` calls it once per lookup — 349 times for `Arena/Core.lean`
    alone, which is nine of this gate's ten seconds.  The answer depends on
    the file and nothing else, and every caller here gets its lines from
    `lean_text`'s cache, so the list object identifies the file."""
    inner, seen = P.comment_lines, {}

    def cached(lines):
        key = (id(lines), len(lines))
        if key not in seen:
            seen[key] = inner(lines)
        return seen[key]

    P.comment_lines = cached


_memoise_comment_lines()

DOC_RE = re.compile(r"^\s*//[/!]")
DOC_PFX_RE = re.compile(r"^\s*//[/!] ?")
MARKER_RE = re.compile(r"Lean twin:")
# `none` in either spelling: the plain word, or task #97-SWAP §6's
# `**none owed**` for a store routine the twin has no separate name for.
NONE_RE = re.compile(r"\A\s*(?:\*\*)?none\b")
# The citation itself.  The path is always on one line and so is the range
# that follows it, which is what makes `update` a digits-only rewrite; the
# NAME may be wrapped onto the next doc line (eight of them are, task
# #97-SWAP §6), so the match runs over the doc block's joined text.
CITE_RE = re.compile(
    r"(?P<path>proof/ConRon/[A-Za-z0-9_/]+\.lean)"
    r"(?::(?P<a>\d+)(?:-(?P<b>\d+))?)?"
    r"(?:(?:`?[ \n]+)|:)"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)")


def rel(p):
    try:
        return os.path.relpath(p, REPO)
    except ValueError:
        return p


class Twin:
    """One `Lean twin:` citation, with where its digits live.

    `(line, col_a, col_b)` is the half-open span of the range text — the
    `:275-305` after `.lean`, or the empty span right after `.lean` when the
    citation carries no range yet.  It is a span on ONE line by
    construction, so rewriting it cannot change a doc block's shape."""

    def __init__(self, file, lineno, path, a, b, name, line, col_a, col_b,
                 eat_colon=False):
        self.file = file          # absolute path of the .rs file
        self.lineno = lineno      # 1-based line carrying `.lean`
        self.path = path          # repo-relative .lean path
        self.a = a                # cited range, or (None, None)
        self.b = b
        self.name = name          # the cited declaration, or None
        self.line = line          # 0-based index of `lineno`
        self.col_a = col_a
        self.col_b = col_b
        # `Readback.lean:denoteEShared` — a rangeless citation whose
        # separator is the colon a range would have used.  Filling the range
        # in has to put a space back, or the name would run into the digits.
        self.eat_colon = eat_colon

    def patch(self, a, b):
        """The text that replaces `[col_a, col_b)` to make the range `a-b`."""
        new = ":%d" % a if a == b else ":%d-%d" % (a, b)
        return new + " " if self.eat_colon else new

    @property
    def range(self):
        if self.a is None:
            return "-"
        return str(self.a) if self.b == self.a else "%d-%d" % (self.a, self.b)

    def where(self):
        return "%s:%d" % (rel(self.file), self.lineno)


def rust_files(roots):
    out = []
    for r in roots:
        base = os.path.join(REPO, r)
        if os.path.isfile(base + ".rs"):
            out.append(base + ".rs")
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(dirnames)
            for fn in sorted(filenames):
                if fn.endswith(".rs"):
                    out.append(os.path.join(dirpath, fn))
    return sorted(set(out))


def doc_blocks(lines):
    """[(start_index, [(line_index, text_after_the_prefix)])] for every run
    of consecutive `///` / `//!` lines."""
    out = []
    i, n = 0, len(lines)
    while i < n:
        if DOC_RE.match(lines[i]):
            j = i
            while j < n and DOC_RE.match(lines[j]):
                j += 1
            out.append((i, [(k, DOC_PFX_RE.sub("", lines[k]))
                            for k in range(i, j)]))
            i = j
        else:
            i += 1
    return out


def scan_rust_file(path):
    """Every `Lean twin:` citation in one file, in source order."""
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    out = []
    for _, block in doc_blocks(lines):
        # The block's text, joined by newlines, with a map from each
        # character back to its (line index, column) in the file.
        text, where = [], []
        for k, body in block:
            off = len(lines[k]) - len(body)
            for c, ch in enumerate(body):
                text.append(ch)
                where.append((k, off + c))
            text.append("\n")
            where.append((k, len(lines[k])))
        text = "".join(text)
        marks = [m.end() for m in MARKER_RE.finditer(text)]
        for idx, start in enumerate(marks):
            stop = marks[idx + 1] if idx + 1 < len(marks) else len(text)
            if NONE_RE.match(text[start:stop]):
                continue
            m = CITE_RE.search(text, start, stop)
            if m is None:
                # No name: either there is no path at all (prose — "the `==`
                # of `List LIdx`"), or a bare path (a branch of a twin).
                pm = re.search(r"proof/ConRon/[A-Za-z0-9_/]+\.lean",
                               text[start:stop])
                if pm is None:
                    continue
                ln, col = where[start + pm.start()]
                out.append(Twin(path, ln + 1, pm.group(0), None, None, None,
                                ln, col + len(pm.group(0)),
                                col + len(pm.group(0))))
                continue
            pend = m.end("path")
            rend = m.end("b") if m.group("b") else (
                m.end("a") if m.group("a") else pend)
            eat = not m.group("a") and text[pend:pend + 1] == ":"
            if eat:
                rend = pend + 1
            ln, col = where[pend - 1]
            ln2, col2 = where[rend - 1]
            if ln2 != ln:  # cannot happen: a range never wraps
                ln2, col2 = ln, col
            out.append(Twin(
                path, ln + 1, m.group("path"),
                int(m.group("a")) if m.group("a") else None,
                int(m.group("b") or m.group("a") or 0) or None,
                m.group("name"), ln, col + 1, col2 + 1, eat))
    return out


def collect(roots):
    out = []
    for f in rust_files(roots):
        out.extend(scan_rust_file(f))
    return out


_LEAN = {}


def lean_text(path):
    """The twin file's lines, or None if there is no such file."""
    if path not in _LEAN:
        full = os.path.join(REPO, path)
        if not os.path.exists(full):
            _LEAN[path] = None
        else:
            with open(full, encoding="utf-8") as f:
                _LEAN[path] = f.read().split("\n")
    return _LEAN[path]


def locate_where(lines, a, b, leaf):
    """The block of the `where` member `leaf` inside the 1-based range
    `(a, b)`, or None.

    `provenance.locate_decl` answers a citation like `hoistClosure.pushOne`
    with the PARENT's block, because that is the rule the con-leche ledger
    wants (a `where` clause is part of what it hangs off).  A twin line
    wants the narrower answer: the Rust function is the port of that inner
    loop and of nothing else.  The shape is uniform in this tree — the
    member and its doc comment sit at the `where`'s own indent, its body
    deeper — so the member's block runs to the next line at that indent or
    to the left of it."""
    pat = re.compile(r"^(\s+)" + re.escape(leaf) + r"\b")
    for i in range(a - 1, min(b, len(lines))):
        m = pat.match(lines[i])
        if not m:
            continue
        ind = len(m.group(1))
        s, j = i, i - 1
        while j >= a - 1:  # the member's own doc comment, at its indent
            t = lines[j].strip()
            if lines[j][:ind].isspace() and t.startswith(("@[", "/--")):
                s, j = j, j - 1
                continue
            if t.endswith("-/") and not t.startswith("/-!"):
                k = j
                while k >= a - 1 and not lines[k].strip().startswith("/--"):
                    k -= 1
                if k >= a - 1:
                    s, j = k, k - 1
                    continue
            break
        e = i
        for k in range(i + 1, min(b, len(lines))):
            t = lines[k]
            if not t.strip():
                continue
            head = len(t) - len(t.lstrip())
            if head < ind or (head == ind
                              and re.match(r"(/--|@\[|[^\W\d])", t.lstrip())):
                break
            e = k
        return s + 1, e + 1
    return None


IDENT_RE = re.compile(r"[^\W\d]\w*'*", re.UNICODE)
_ANON = {}


def anon_instances(path, lines):
    """`{generated name: line index}` for the file's ANONYMOUS instances.

    An `instance : BEq AnonNode := …` has no name in the source and so no
    entry in any index built from the source, but it has one in Lean —
    `instBEqAnonNode` — and that is what the Rust's twin line cites (task
    #97-SWAP §6: "six name a declaration an index cannot produce on its
    own").  Lean builds it from the class and the head symbols of the
    instance's type, which for the shapes this repository writes (`C T`,
    `C (T α …)`, with `:=` or `where` after) is exactly: `inst`, then every
    UPPERCASE-initial identifier of the type ascription, in order.  A
    universe or type variable is lowercase and drops out, which is why
    `BEq (Idx k)` is `instBEqIdx` and not `instBEqIdxK`.

    It is a heuristic, and it is a SAFE one: a name it gets wrong resolves
    to nothing and the gate says `GONE` rather than accepting the wrong
    declaration.  Naming the instance in the Lean is always the better
    fix; until then this reads what is there."""
    if path in _ANON:
        return _ANON[path]
    skip = P.comment_lines(lines)
    out = {}
    for i, line in enumerate(lines):
        if i in skip or line[:1].isspace() or not line:
            continue
        if not P.ANON_INSTANCE_RE.match(line):
            continue
        # Cut at the `instance` KEYWORD, not at a fixed offset: attributes
        # and `private`/`scoped` may sit in front of it.
        head = line[line.index("instance") + len("instance"):]
        head = re.split(r":=| where\b", head, maxsplit=1)[0]
        head = head.lstrip().lstrip(":")
        name = "inst" + "".join(w for w in IDENT_RE.findall(head)
                                if w[:1].isupper())
        out.setdefault(name, i)
    _ANON[path] = out
    return out


_RESOLVED = {}


def resolve(t):
    """`(status, payload)` for one citation.

      ("SKIP",   None)        a bare path: nothing to locate
      ("MISSING", None)       the `.lean` file does not exist
      ("GONE",   None)        no top-level declaration of that name
      ("OK",     (a, b))      the declaration's block
    """
    lines = lean_text(t.path)
    if lines is None:
        return "MISSING", None
    if t.name is None:
        return "SKIP", None
    # `locate_decl` re-parses the whole file, and a busy module is cited a
    # hundred times (`core.rs` cites `Arena/Core.lean` 349 times): memoise
    # the answer, which is a function of `(path, name)` alone.
    key = (t.path, t.name)
    if key in _RESOLVED:
        return _RESOLVED[key]
    _RESOLVED[key] = out = _resolve(t, lines)
    return out


def _resolve(t, lines):
    loc = P.locate_decl(lines, t.name)
    if loc is None:
        i = anon_instances(t.path, lines).get(t.name.split(".")[-1])
        if i is not None:
            return "OK", P.extend_block(lines, i)
        return "GONE", None
    # `parent.leaf`, resolved to the parent: narrow it to the `where` member.
    head = P.first_decl_line(lines, loc[0], loc[1])
    if head and "." in t.name:
        xs, ys = t.name.split("."), head.split(".")
        if len(ys) < len(xs) and xs[:len(ys)] == ys:
            w = locate_where(lines, loc[0], loc[1], xs[-1])
            if w is not None:
                loc = w
    return "OK", loc


def cmd_check(args):
    twins = collect(args.roots)
    findings = 0
    for t in twins:
        st, loc = resolve(t)
        if st == "SKIP":
            continue
        if st == "MISSING":
            print("MISSING %s — %s is not a file of this repository"
                  % (t.where(), t.path))
            findings += 1
            continue
        if st == "GONE":
            print("GONE %s — `%s` is not a top-level declaration of %s"
                  % (t.where(), t.name, t.path))
            findings += 1
            continue
        a, b = loc
        if t.a is None:
            print("NORANGE %s — %s %s has no line range (it is %d-%d)"
                  % (t.where(), t.path, t.name, a, b))
            findings += 1
            continue
        if not (a <= t.a and t.b <= b):
            print("STALE %s — %s:%s %s: the declaration is at %d-%d"
                  % (t.where(), t.path, t.range, t.name, a, b))
            findings += 1
    if findings:
        print("%d finding(s).  `scripts/twin-lines.py update` relocates "
              "what merely moved; a `GONE` is re-pointed by hand."
              % findings)
        return 1
    nfiles = len({t.file for t in twins})
    print("twin-lines: %d `Lean twin:` citation(s) in %d file(s), every one "
          "at its twin's current lines." % (len(twins), nfiles))
    return 0


def cmd_update(args):
    twins = collect(args.roots)
    edits, moved, gone = {}, 0, 0
    for t in twins:
        st, loc = resolve(t)
        if st == "SKIP":
            continue
        if st == "MISSING":
            print("MISSING %s — %s is not a file of this repository"
                  % (t.where(), t.path))
            gone += 1
            continue
        if st == "GONE":
            print("GONE %s — `%s` is not a top-level declaration of %s "
                  "→ re-point it by hand (the dispatcher, or the renamed "
                  "twin)" % (t.where(), t.name, t.path))
            gone += 1
            continue
        a, b = loc
        if (a, b) == (t.a, t.b):
            continue
        new = t.patch(a, b)
        print("MOVED %s — %s %s:%s → %s"
              % (t.where(), t.name, t.path, t.range, new.strip()))
        moved += 1
        edits.setdefault(t.file, []).append((t.line, t.col_a, t.col_b, new))
    for path, es in edits.items():
        with open(path, encoding="utf-8") as f:
            lines = f.read().split("\n")
        for ln, ca, cb, new in sorted(es, key=lambda e: (-e[0], -e[1])):
            lines[ln] = lines[ln][:ca] + new + lines[ln][cb:]
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines))
    print("twin-lines: %d citation(s) relocated, %d GONE." % (moved, gone))
    return 1 if gone else 0


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="mode")
    for name, fn in (("check", cmd_check), ("update", cmd_update)):
        p = sub.add_parser(name)
        p.add_argument("roots", nargs="*", default=list(ROOTS))
        p.set_defaults(fn=fn)
    args = ap.parse_args(argv)
    if args.mode is None:
        ap.print_help()
        return 2
    if not args.roots:
        args.roots = list(ROOTS)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
