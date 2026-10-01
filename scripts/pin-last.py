#!/usr/bin/env python3
"""scripts/pin-last.py — THE PIN COMMIT IS THE LAST ONE (task #108).

DESIGN.md §7's bump rule: the con-leche pin — `rev` in
`proof/lakefile.toml`'s con-leche `[[require]]` and the `«con-leche»` entry
of `proof/lake-manifest.json` — changes in the LAST commit of a bump and in
no other, so that every commit before it is reproducible with
`provenance.py update` and no `--old`.  Task #105 broke it twice (a
sub-agent's commit `c4e012cb`, and the lead's own `git add -u proof`), and
nothing noticed until a human read the log.

The check: on the first-parent line of `<base>..HEAD`, every commit but the
tip carries the same pin as `merge-base(<commit>, <base>)` — the master it
was written against.  A merge that brings in master's own pin change passes
(its merge base is that master); a commit that changes the pin, or a merge
of a side branch that left the pin changed, fails.  Side branches merged in
are not walked: a lane that committed the pin and restored it before its
merge is the lane's slip, caught by this same check on the lane's own branch
(where it was first-parent), not a property of the merged result.

It is a gate step (`gates.sh`, after `provenance`) rather than only a
`land` precondition, because the slip happens in a sub-agent's worktree,
whose own gate run is the earliest point anything can see it; and
`scripts/bump-con-leche.sh land` runs it again with the tip REQUIRED to be
the pin commit (`--tip-is-pin`).

    scripts/pin-last.py [--base REF] [--tip-is-pin]

Exit codes: 0 fine, 1 a violation, 2 usage/IO error.
"""

import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAKEFILE = "proof/lakefile.toml"
MANIFEST = "proof/lake-manifest.json"
REQUIRE_RE = re.compile(r"\[\[require\]\]\s*\n(?P<body>(?:(?!\[).*\n?)*)")


def git(*argv, inp=None):
    r = subprocess.run(["git", "-C", REPO] + list(argv), input=inp,
                       capture_output=True)
    if r.returncode != 0:
        raise SystemExit("pin-last: git %s: %s"
                         % (" ".join(argv), r.stderr.decode(errors="replace").strip()))
    return r.stdout


def parse_pin(lakefile, manifest):
    """(lakefile rev, manifest rev) of con-leche, either None if absent."""
    lrev = mrev = None
    for m in REQUIRE_RE.finditer(lakefile or ""):
        body = m.group("body")
        if re.search(r'^name\s*=\s*"con-leche"', body, re.M):
            r = re.search(r'^rev\s*=\s*"([^"]*)"', body, re.M)
            lrev = r.group(1) if r else None
    try:
        data = json.loads(manifest or "")
        for pkg in data.get("packages", []):
            if pkg.get("name", "").strip("«»") == "con-leche":
                mrev = pkg.get("rev")
    except ValueError:
        pass
    return lrev, mrev


def pins(commits):
    """{commit: (lakefile rev, manifest rev)}, read with one `cat-file`."""
    req = "".join("%s:%s\n%s:%s\n" % (c, LAKEFILE, c, MANIFEST) for c in commits)
    out = git("cat-file", "--batch", inp=req.encode())
    blobs, i = [], 0
    while i < len(out):
        nl = out.index(b"\n", i)
        head = out[i:nl].decode().split()
        if len(head) == 2 and head[1] == "missing":
            blobs.append(None)
            i = nl + 1
            continue
        size = int(head[2])
        blobs.append(out[nl + 1:nl + 1 + size].decode())
        i = nl + 1 + size + 1
    return {c: parse_pin(blobs[2 * k], blobs[2 * k + 1])
            for k, c in enumerate(commits)}


def main(argv):
    base, tip_is_pin = "master", False
    args = list(argv)
    while args:
        a = args.pop(0)
        if a == "--base" and args:
            base = args.pop(0)
        elif a.startswith("--base="):
            base = a.split("=", 1)[1]
        elif a == "--tip-is-pin":
            tip_is_pin = True
        else:
            print(__doc__.strip().split("\n\n")[-2], file=sys.stderr)
            return 2
    line = git("rev-list", "--first-parent", "%s..HEAD" % base).decode().split()
    if not line:
        print("pin-last: HEAD is not ahead of %s; nothing to check" % base)
        return 1 if tip_is_pin else 0
    parents = {}
    for row in git("rev-list", "--first-parent", "--parents", "%s..HEAD" % base
                   ).decode().strip().split("\n"):
        cs = row.split()
        parents[cs[0]] = cs[1] if len(cs) > 1 else None
    tip = line[0]
    p = pins(sorted(set(line) | {x for x in parents.values() if x}))
    bad = []
    for c in line[1:]:
        par = parents[c]
        if par is not None and p[c] == p[par]:
            continue  # the pin did not move here
        mb = git("merge-base", c, base).decode().strip()
        want = pins([mb])[mb]
        if p[c] != want:
            bad.append((c, want, p[c]))
    rc = 0
    for c, want, got in reversed(bad):
        subj = git("log", "-1", "--format=%h %s", c).decode().strip()
        print("pin-last: %s changes the con-leche pin (%s → %s), but only the "
              "tip of a branch may (DESIGN.md §7)"
              % (subj, "/".join(x[:8] if x else "-" for x in want),
                 "/".join(x[:8] if x else "-" for x in got)))
        rc = 1
    if tip_is_pin:
        mb = git("merge-base", tip, base).decode().strip()
        tp, bp = pins([tip])[tip], pins([mb])[mb]
        if tp == bp:
            print("pin-last: the tip %s does not change the con-leche pin; "
                  "commit the pin last (scripts/bump-con-leche.sh pin)" % tip[:8])
            rc = 1
        elif tp[0] != tp[1]:
            print("pin-last: the tip's lakefile rev %s and manifest rev %s "
                  "disagree; run `lake update con-leche` in proof/" % tp)
            rc = 1
    if rc == 0:
        print("pin-last: %d commit(s) ahead of %s, the pin moves in %s"
              % (len(line), base,
                 "the tip only" if p[tip] != pins([git("merge-base", tip, base)
                                                   .decode().strip()]).popitem()[1]
                 else "none of them"))
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
