#!/usr/bin/env python3
"""scripts/provenance-selftest.py — the unit test of the gate's LEAN parser
(task #97 P2 tooling, DESIGN.md §3.7 and §8.4).

`scripts/provenance.py` reads citations out of the arena checker's Lean
sources (`proof/ConRon/Arena/**`) as it reads them out of the Rust.  That
parser is a regex over a language whose comments nest, so it gets a fixture:
`scripts/testdata/provenance/{good,bad}/*.lean`, one declaration per shape
the gate accepts and one per finding it must raise.

The fixtures carry `@@<decl>@@` placeholders instead of literal line ranges,
substituted here with what `provenance.py locate` says at the *current* pin
(`@@#<decl>@@` is the same without the trailing declaration name, for the
case that cites one declaration's range under another's name).  So a
con-leche bump moves the fixture with the tree and cannot rot it — which is
the whole point of a gate that is about staying in sync.

    scripts/provenance-selftest.py [--verbose]

Exit codes: 0 the parser behaves, 1 it does not, 2 usage/IO error.
"""

import hashlib
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import provenance as P  # noqa: E402

REPO = P.REPO
FIXTURES = os.path.join(HERE, "testdata", "provenance")
# The con-leche file every fixture citation points into.  One file, so the
# substitution needs one `locate` call per declaration and nothing else.
FIXTURE_LEAN = "ConLeche/Kernel/Name.lean"

PLACEHOLDER_RE = re.compile(r"@@(?P<bare>#?)(?P<decl>[^@]+)@@")

# What `check` must say about `bad/Bad.lean`: one finding per declaration,
# and no more.  The fixture's own doc comments name them.
EXPECTED_BAD = ["MALFORMED", "UNRECONCILED", "MISSING", "RANGE", "NODECL",
                "NAME", "UNCITED"]


def scratch_dir():
    """A per-checkout scratch directory under `_tmp/` (CLAUDE.md: never the
    system temp directory, and `_tmp/` is shared between agent worktrees, so
    key it by checkout as `gates.sh` does)."""
    key = hashlib.sha256(REPO.encode("utf-8")).hexdigest()[:12]
    return os.path.join(REPO, "_tmp", "provenance-selftest-" + key)


def substitute(text):
    """Replace every `@@decl@@` with the citation body `locate` computes."""
    wanted = sorted({m.group("decl") for m in PLACEHOLDER_RE.finditer(text)})
    if not wanted:
        return text
    lines = P.lean_text(FIXTURE_LEAN)
    if lines is None:
        raise SystemExit("error: %s is not in the pinned con-leche" % FIXTURE_LEAN)
    bodies = {}
    for decl in wanted:
        loc = P.locate_decl(lines, decl)
        if loc is None:
            raise SystemExit("error: %s declares no `%s` at the current pin "
                             "— fix the fixture" % (FIXTURE_LEAN, decl))
        a, b = loc
        rng = str(a) if a == b else "%d-%d" % (a, b)
        bodies[decl] = "%s:%s" % (FIXTURE_LEAN, rng)

    def one(m):
        body = bodies[m.group("decl")]
        return body if m.group("bare") else "%s %s" % (body, m.group("decl"))

    return PLACEHOLDER_RE.sub(one, text)


def materialise(name, dest):
    """Copy one fixture half into `dest`, placeholders substituted."""
    src = os.path.join(FIXTURES, name)
    os.makedirs(dest, exist_ok=True)
    for fn in sorted(os.listdir(src)):
        if not fn.endswith(".lean"):
            continue
        with open(os.path.join(src, fn), encoding="utf-8") as f:
            text = substitute(f.read())
        with open(os.path.join(dest, fn), "w", encoding="utf-8") as f:
            f.write(text)


def run_check(root):
    r = subprocess.run(
        [sys.executable, os.path.join(HERE, "provenance.py"), "check",
         "--roots", root],
        capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def kinds(out):
    """The finding keywords `check` printed, in order."""
    got = []
    for line in out.split("\n"):
        m = re.match(r"^([A-Z]+) ", line)
        if m:
            got.append(m.group(1))
    return got


def main(argv):
    verbose = "--verbose" in argv
    if P.con_leche_dir() is None:
        print("error: the con-leche lake package is not available; run "
              "`lake update` (or `lake build`) in proof/", file=sys.stderr)
        return 2

    work = scratch_dir()
    shutil.rmtree(work, ignore_errors=True)
    failures = []

    # 1. The clean half must come out clean, and every declaration of it must
    #    be seen as an arena item (the count is in `check`'s own summary).
    good = os.path.join(work, "good")
    materialise("good", good)
    rc, out = run_check(good)
    if verbose:
        print(out.rstrip())
    if rc != 0:
        failures.append("good/: expected a clean run, got exit %d:\n%s" % (rc, out))
    else:
        m = re.search(r"(\d+) item\(s\) \((\d+) Rust, (\d+) arena Lean\)", out)
        if not m:
            failures.append("good/: no item count in %r" % out)
        elif (int(m.group(2)), int(m.group(3))) != (0, 6):
            failures.append("good/: expected 0 Rust and 6 arena items, got "
                            "%s Rust and %s arena" % (m.group(2), m.group(3)))

    # 2. The other half must raise exactly the listed findings, once each.
    bad = os.path.join(work, "bad")
    materialise("bad", bad)
    rc, out = run_check(bad)
    if verbose:
        print(out.rstrip())
    if rc != 1:
        failures.append("bad/: expected exit 1, got %d:\n%s" % (rc, out))
    got = kinds(out)
    if sorted(got) != sorted(EXPECTED_BAD):
        failures.append("bad/: expected findings %s, got %s\n%s"
                        % (sorted(EXPECTED_BAD), sorted(got), out))

    if failures:
        for f in failures:
            print("FAIL " + f)
        print("provenance-selftest: %d failure(s)." % len(failures))
        return 1
    shutil.rmtree(work, ignore_errors=True)
    print("provenance-selftest: the Lean parser accepts %d clean shapes and "
          "raises %d findings, as specified."
          % (6, len(EXPECTED_BAD)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
