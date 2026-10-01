#!/usr/bin/env bash
# scripts/overview-links.sh — THE OVERVIEW LINK GATE (task #76), ported from
# con-leche's `tests/overview-links.sh` with the same semantics.
#
# WHY THIS EXISTS.  `README.md` is the human-written entry, `OVERVIEW.md` the
# user-facing guided tour; both anchor their claims to *line
# ranges* of source files through `blob/master/<path>#L<a>-L<b>` links.
# Line anchors are the most perishable kind of documentation there is —
# inserting one `use` at the top of a module silently slides every anchor
# into it by one, and nothing in the build notices.  Worse, a link can keep
# pointing at valid lines that no longer say what the prose claims, which no
# existence check would catch.
#
# WHAT IT CHECKS.  The gate does not try to decide whether the prose is
# true; it makes the *cited text* a committed artefact.  It extracts every
# `blob/master` link from `README.md` and then from `OVERVIEW.md`, in
# document order, copies the linked lines (with their line numbers) into one
# text, and diffs that against `scripts/overview-links-expected.txt`.  Hence:
#
#   * moving the linked lines changes the line numbers in the text and
#     fails the gate — the reminder to update the link;
#   * editing the linked lines changes the text and fails the gate — the
#     reminder to re-read the paragraph that cites them, because the
#     document may now be stale in a way no tool can see;
#   * deleting the file, or shrinking it past the anchor, is a hard error
#     naming the link.
#
# The failure is never "you broke the docs, restore them": it is "the
# citation moved, look at what cites it".  After checking that the prose
# still matches, regenerate with
#
#     scripts/overview-links.sh --update
#
# and commit the expectation with the change that moved the lines.
#
# WHAT IS AN ERROR RATHER THAN A DIFF.  A link into *this* repository that
# pins a commit — `blob/<sha>/…` — is rejected outright: the documents must
# track `master`, or the gate would be pinning a snapshot and the tour would
# quietly drift from the tree it describes.  Links that are not of the
# repository-blob form (external URLs, anchors within the document) are
# ignored; they are not this gate's business.
#
# LINKS INTO CON-LECHE (task #91).  con-leche is a plain `lake` dependency
# of `proof/` (pinned by `rev` in `proof/lakefile.toml`, resolved through
# `proof/lake-manifest.json`), not vendored source, so GitHub does not serve
# its files under this repository's own URL: a citation of con-leche code is
# a pinned link straight into `leanprover/con-leche` —
# `blob/<sha>/<path>#L<a>-L<b>`.  Most such pins are immutable (a citation of
# what con-leche looked like at some past commit, e.g. in a task-log entry)
# and are not checked, exactly like a pinned link into any other repository.
# The one exception: a link pinned at *the pinned con-leche commit itself*
# (`proof/lake-manifest.json`'s `con-leche` entry, via `provenance.py`'s
# `con_leche_dir`/`current_submodule_commit`) is checked like a local link,
# against the file in that lake package directory — that is the live
# citation of the code the port is written against, and it should move with
# the pin the same way a local citation moves with this tree.
#
# PATHS.  A link into this repository's `<path>` is resolved from the
# repository root, whatever owner/repo it names (as in con-leche: the
# project has been renamed before).  A link into `leanprover/con-leche` at
# the pinned commit resolves its `<path>` under the con-leche lake package
# directory.
#
# BEFORE `OVERVIEW.md` EXISTS.  The tour is being written; until it lands,
# and while no document carries a link of this form, the gate passes
# trivially so that it can sit in `scripts/gates.sh` from now on.
#
# `--follow` (task #108): THE MECHANICAL HALF OF A RELOCATION.  Every sync
# (#100, #103, #105, #106) had a commit that moved anchors whose cited text
# had not changed: lines inserted above them, or con-leche's pin moving.
# `--follow` does that pile and nothing else.  For each link whose committed
# text (the expectation file's segment for that exact `<path>#L<a>-L<b>`) is
# no longer at its lines, it looks for that text VERBATIM in the same file
# and, when it is there, rewrites the anchor to where it is (the occurrence
# nearest the old one); a link into con-leche at a commit other than the pin
# is re-pinned to the pin.  The expectation file is then rewritten for the
# followed links only.  A link whose text is nowhere in the file keeps its
# anchor and its OLD expectation, so the plain gate still fails on exactly
# those — the paragraphs to re-read — and a link that has no expectation yet
# is left out of it, for the same reason.  It changes numbers and pins in
# README.md/OVERVIEW.md, never words.
#
# The gate itself stays a pure check: a run without `--follow` writes
# nothing, and a moved anchor still fails it until someone (a person, or
# `scripts/bump-con-leche.sh`) runs `--follow`.  Accepting moves inside the
# gate would make every gate run a potential source edit, which `gates.sh`
# promises it never does.
#
# NO BUILD REQUIRED.  This is a pure source-tree gate: it reads the two
# documents and the cited files and nothing else, so it costs milliseconds.
set -u
cd "$(dirname "$0")/.."

DOCS="README.md OVERVIEW.md"
EXPECTED=scripts/overview-links-expected.txt

update=0
follow=0
case "${1:-}" in
  --update) update=1 ;;
  --follow) follow=1 ;;
  "") ;;
  *) echo "usage: scripts/overview-links.sh [--update | --follow]" >&2; exit 2 ;;
esac

tmp=$(mktemp) || exit 3
changed=$(mktemp) || exit 3
trap 'rm -f "$tmp" "$changed"' EXIT

# `--follow`, first half: rewrite the anchors (and con-leche pins) of the
# links whose committed text is found verbatim at other lines.  Writes the
# keys of the links whose text was NOT found ("changed <key>") and of those
# with no expectation at all ("fresh <key>") to "$changed".
if [ "$follow" = 1 ]; then
  [ -f "$EXPECTED" ] || { echo "overview-links --follow: $EXPECTED missing" >&2; exit 2; }
  python3 - "$EXPECTED" "$changed" $DOCS <<'PY' || exit 1
import re, sys, os
expected, changed_out, docs = sys.argv[1], sys.argv[2], sys.argv[3:]
sys.path.insert(0, 'scripts')
import provenance as P  # noqa: E402

LINK = re.compile(
    r'https://github\.com/([^/\s)]+)/([^/\s)]+)/blob/([^/\s)]+)/'
    r'([^)\s#]+)#L(\d+)(?:-L(\d+))?')
PIN, CLD = P.current_submodule_commit(), P.con_leche_dir()

segs, key = {}, None
for line in open(expected, encoding='utf-8').read().split('\n'):
    if line.startswith('== '):
        key = line[3:]
        segs[key] = []
    elif key is not None and re.match(r'^ {0,5}\d+  ', line):
        segs[key].append(line[8:])

def file_lines(p):
    if not os.path.isfile(p):
        return None
    ls = open(p, encoding='utf-8').read().split('\n')
    if ls and ls[-1] == '':
        ls.pop()
    return ls

followed = repinned = 0
changed, fresh = [], []
for doc in docs:
    if not os.path.isfile(doc):
        continue
    text = open(doc, encoding='utf-8').read()
    out, last = [], 0
    for m in LINK.finditer(text):
        owner, repo, ref, path, a, b = m.groups()
        a = int(a); b = int(b) if b is not None else a
        newref = ref
        if repo == 'con-ron':
            if ref != 'master':
                continue
            label, read = path, path
        elif repo == 'con-leche':
            if not (re.fullmatch(r'[0-9a-f]{7,40}', ref) and PIN and CLD):
                continue
            label, read = 'con-leche/' + path, os.path.join(CLD, path)
            newref = ref if PIN.startswith(ref) else PIN[:len(ref)]
        else:
            continue
        anchor = f"#L{a}" if b == a else f"#L{a}-L{b}"
        want = segs.get(label + anchor)
        lines = file_lines(read)
        na, nb = a, b
        if want is None:
            fresh.append(label + anchor)
        elif lines is not None and lines[a - 1:b] != want:
            n = len(want)
            hits = [i for i in range(len(lines) - n + 1) if lines[i:i + n] == want]
            if hits:
                i = min(hits, key=lambda i: abs(i + 1 - a))
                na, nb = i + 1, i + n
                followed += 1
            else:
                changed.append(label + anchor)
        if (na, nb, newref) == (a, b, ref):
            continue
        repinned += newref != ref
        new = f"https://github.com/{owner}/{repo}/blob/{newref}/{path}" + (
            f"#L{na}" if (m.group(6) is None and na == nb) else f"#L{na}-L{nb}")
        out.append(text[last:m.start()])
        out.append(new)
        last = m.end()
    if out:
        out.append(text[last:])
        with open(doc, 'w', encoding='utf-8') as f:
            f.write(''.join(out))
with open(changed_out, 'w', encoding='utf-8') as f:
    f.write(''.join('changed ' + k + '\n' for k in changed))
    f.write(''.join('fresh ' + k + '\n' for k in fresh))
print(f"overview-links --follow: {followed} anchor(s) followed their text, "
      f"{repinned} con-leche link(s) re-pinned, {len(changed)} link(s) whose "
      f"text changed and {len(fresh)} with no expectation yet (left for a reader):")
for k in changed:
    print("  changed " + k)
for k in fresh:
    print("  new     " + k)
PY
fi

# The extractor.  Reads the documents that exist, walks their links in
# order, and writes the segment text to the output file (or reports EVERY
# structural error it finds — a change that renames a module should see all
# its dead links at once, not one per invocation — and exits 1).
if ! python3 - "$tmp" $DOCS <<'PY'
import re, sys, os

out, docs = sys.argv[1], sys.argv[2:]

# cwd is the repository root (the shell script `cd`s there first).
sys.path.insert(0, 'scripts')
import provenance as P  # noqa: E402

# github.com/<owner>/<repo>/blob/<ref>/<path>#L<a>[-L<b>]
#
# The owner/repo are matched loosely on purpose: the project may be renamed
# and the gate should survive that without a script edit.  The <ref> is what
# matters: a link into this repository must be `master` (and is checked); a
# link into another repository must pin a commit.  Most such pins are
# immutable and not checked — EXCEPT a link into `leanprover/con-leche`
# pinned at con-leche's own pinned commit (`provenance.py`'s
# `current_submodule_commit`), which is checked like a local link against
# the file in its lake package directory (task #91: con-leche is a plain
# lake dependency, not vendored, so this is the only way left to cite its
# code that still moves with the pin).
LINK = re.compile(
    r'https://github\.com/([^/\s)]+)/([^/\s)]+)/blob/([^/\s)]+)/'
    r'([^)\s#]+)#L(\d+)(?:-L(\d+))?')

CON_LECHE_PIN = P.current_submodule_commit()
CON_LECHE_DIR = P.con_leche_dir()

errors = []
segments = []

for doc in docs:
    if not os.path.isfile(doc):
        continue
    with open(doc, encoding='utf-8') as f:
        text = f.read()
    for m in LINK.finditer(text):
        owner, repo, ref, path, a, b = m.groups()
        link = m.group(0)
        if repo == 'con-ron':
            if ref != 'master':
                errors.append(
                    f"{link}\n    ({doc}) pins the ref `{ref}`; links into this repository must track `master`.")
                continue
            # `label` is what goes in the committed expectation file, so it
            # must be portable across checkouts; `read_path` is where the
            # bytes actually come from.
            label = path
            read_path = path
        elif repo == 'con-leche':
            # README and OVERVIEW describe the port as it is, so a citation
            # of con-leche must be at the commit the port is pinned to, and
            # is checked against that commit's files.  A con-leche bump
            # therefore fails here until the citations are moved with it.
            if not (CON_LECHE_PIN and CON_LECHE_DIR and os.path.isdir(CON_LECHE_DIR)):
                errors.append(
                    f"{link}\n    ({doc}) cites con-leche, but its lake package is not "
                    f"checked out (run `lake update con-leche` in proof/, or link "
                    f"proof/.lake/packages as CLAUDE.md says).")
                continue
            if not (re.fullmatch(r'[0-9a-f]{7,40}', ref) and CON_LECHE_PIN.startswith(ref)):
                errors.append(
                    f"{link}\n    ({doc}) cites con-leche at `{ref}`, but the pinned "
                    f"commit is `{CON_LECHE_PIN}` (proof/lake-manifest.json).")
                continue
            # At the pinned commit: check it like a local
            # link, against the file in the lake package directory.  The
            # package directory's absolute path is worktree-specific (it
            # lives under a shared, checkout-keyed `_tmp/`), so the label
            # committed to the expectation file is a synthetic, portable one.
            label = f"con-leche/{path}"
            read_path = os.path.join(CON_LECHE_DIR, path)
        else:
            # A link into another repository: it must pin a commit,
            # because nothing here can check it and a branch link would
            # drift; a pinned link is immutable and is not extracted.
            if re.fullmatch(r'[0-9a-f]{7,40}', ref):
                continue
            errors.append(
                f"{link}\n    ({doc}) links another repository at `{ref}`; such a link must pin a commit.")
            continue
        a = int(a)
        b = int(b) if b is not None else a
        anchor = f"#L{a}" if b == a else f"#L{a}-L{b}"
        if not os.path.isfile(read_path):
            errors.append(f"{link}\n    ({doc}) file `{label}` does not exist.")
            continue
        with open(read_path, encoding='utf-8') as f:
            lines = f.read().split('\n')
        # A trailing newline yields a final empty element; it is not a line.
        if lines and lines[-1] == '':
            lines.pop()
        n = len(lines)
        if a < 1 or b < a or b > n:
            errors.append(
                f"{link}\n    ({doc}) range L{a}-L{b} is outside `{label}` "
                f"(which has {n} lines).")
            continue
        body = ''.join(f"{i:6d}  {lines[i-1]}\n" for i in range(a, b + 1))
        segments.append(f"== {label}{anchor}\n{body}")

if errors:
    sys.stderr.write("overview-links: FAIL — %d bad link(s):\n" % len(errors))
    for e in errors:
        sys.stderr.write("  " + e + "\n")
    sys.exit(1)

header = (
    "# GENERATED by scripts/overview-links.sh --update — do not edit by hand.\n"
    "#\n"
    "# Every line-anchored link of README.md and OVERVIEW.md, in document\n"
    "# order, with the lines it points at.  A diff here means a citation moved\n"
    "# or its text changed: re-read the paragraph that cites it, fix the link\n"
    "# or the prose, then regenerate.\n"
    "\n")

with open(out, 'w', encoding='utf-8') as f:
    f.write(header)
    f.write("\n".join(segments))
    if segments:
        f.write("\n")
PY
then
  exit 1
fi

# The summary counts, read back off the generated text: the header lines ARE
# the link list, so no second channel is needed.
nlinks=$(grep -c '^== ' "$tmp")
nfiles=$(grep '^== ' "$tmp" | sed 's/#L.*//' | sort -u | wc -l)

# The tour has not been written yet and nothing links into the tree: pass,
# and do not ask for an expectation file that would have nothing in it.
if [ ! -f OVERVIEW.md ] && [ "$nlinks" = 0 ] && [ ! -f "$EXPECTED" ]; then
  echo "overview-links: OK (no OVERVIEW.md yet)"
  exit 0
fi

# `--follow`, second half: the new expectation is the tree's, except for
# the links whose text changed (their OLD segment is kept, so the gate keeps
# failing on them) and the links that have none yet (left out, ditto).
if [ "$follow" = 1 ]; then
  python3 - "$EXPECTED" "$tmp" "$changed" <<'PY'
import sys
expected, new, changed = sys.argv[1:]
def segments(p):
    text = open(p, encoding='utf-8').read()
    head, _, body = text.partition('\n== ')
    out = []
    for s in ('== ' + body).split('\n== ') if body else []:
        s = s if s.startswith('== ') else '== ' + s
        out.append((s.split('\n', 1)[0][3:], s.rstrip('\n') + '\n'))
    return head + '\n', out
head, old = segments(expected)
_, cur = segments(new)
oldmap = dict(old)
marks = [l.split(' ', 1) for l in open(changed, encoding='utf-8').read().split('\n') if l]
keep = {k for t, k in marks if t == 'changed'}
fresh = {k for t, k in marks if t == 'fresh'}
segs = [oldmap[k] if k in keep else s for k, s in cur if k not in fresh]
with open(expected, 'w', encoding='utf-8') as f:
    f.write(head)
    f.write('\n'.join(segs))
    if segs:
        f.write('\n')
PY
  if diff -q "$EXPECTED" "$tmp" >/dev/null; then
    echo "overview-links: $nlinks links, $nfiles files, OK after --follow"
    exit 0
  fi
  echo "overview-links --follow: the links above still fail the gate; re-read their paragraphs, then --update" >&2
  exit 1
fi

if [ "$update" = 1 ]; then
  if [ -f "$EXPECTED" ] && cmp -s "$tmp" "$EXPECTED"; then
    echo "overview-links: $nlinks links, $nfiles files, expectation already current"
  else
    cp "$tmp" "$EXPECTED"
    echo "overview-links: $nlinks links, $nfiles files, wrote $EXPECTED"
  fi
  exit 0
fi

if [ ! -f "$EXPECTED" ]; then
  echo "overview-links: FAIL — $EXPECTED missing; run scripts/overview-links.sh --update" >&2
  exit 1
fi

if diff -u "$EXPECTED" "$tmp"; then
  echo "overview-links: $nlinks links, $nfiles files, OK"
  exit 0
fi

cat >&2 <<'MSG'

overview-links: FAIL — the cited lines are not what the documents were
written against.  `-` is the committed expectation, `+` the tree.

  * If a citation MOVED (the text is the same, the numbers shifted, or
    con-leche's pin moved), `scripts/overview-links.sh --follow` updates
    the anchors in README.md / OVERVIEW.md and leaves only the rest.
    (`DESIGN.md` is the working log and is not checked, maintainer's
    ruling 2026-09-24.)
  * If the cited lines CHANGED, re-read the paragraph that cites them —
    the document may now be stale.

Then regenerate:  scripts/overview-links.sh --update
MSG
exit 1
