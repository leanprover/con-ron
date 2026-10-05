#!/usr/bin/env python3
"""Apply the mechanical fixes Lean's linters suggest, from a `lake build` log.

Usage (from `proof/`, the directory the log's paths are relative to):

    lake build 2>&1 | tee build.log
    python3 ../scripts/fix-lean-warnings.py build.log [--only simp|vars]

Three warning kinds are fixed (tasks #101 and #110, DESIGN.md):

* `linter.unusedSimpArgs` ("This simp argument is unused: X"): X is dropped
  from its simp call by Mathlib's `scripts/fix_unused_simp_args.py` (read
  from the Mathlib dependency, not vendored; `← X` becomes `- X`).  The log
  is deduplicated first, since the same warning can be printed more than
  once, and a list that becomes empty (`simp only []`, `simp []`) is written
  as `simp only` or `simp` and a list left starting with `[ ` loses the
  space, but only on the lines the fix touched.
* `linter.unusedVariables` ("Variable name `x` is not explicitly
  referenced"): `x` becomes `_x`, which is the linter's own `[apply]` hint.
  The identifier must be exactly at the reported line and column (0-based,
  in code points), otherwise the site is reported and skipped.

* `linter.deprecated` ("`X` has been deprecated: Use `Y` instead", task
  #110's toolchain move: `if_pos` → `ite_eq_left` and friends): the
  identifier at the reported position is renamed.  It must be spelled there
  as the full old name or as a suffix of it whose prefix the new name shares
  (`div_eq` inside `namespace Nat` → `div_eq_ite`); otherwise the site is
  reported and skipped (a warning raised inside a macro points elsewhere).

Only paths under `ConRon/` are touched: dependencies and generated files
are out of scope, and warnings from them are ignored.  Run it once per
build log: a second run over the same log would edit again.
"""
import argparse
import difflib
import importlib.util
import re
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

SIMP_RE = re.compile(r"^warning: (ConRon/[^:]+\.lean):(\d+):(\d+): This simp argument is unused:\s*$")
VAR_RE = re.compile(r"^warning: (ConRon/[^:]+\.lean):(\d+):(\d+): Variable name `([^`]+)` is not explicitly referenced\.")
DEP_RE = re.compile(r"^warning: (ConRon/[^:]+\.lean):(\d+):(\d+): `([^`]+)` has been deprecated: [Uu]se `([^`]+)` instead")
MATHLIB_FIXER = Path(".lake/packages/mathlib/scripts/fix_unused_simp_args.py")


def fix_simp(lines):
    """Run Mathlib's fixer over the deduplicated simp-arg warnings."""
    seen, out = set(), []
    for i, ln in enumerate(lines):
        m = SIMP_RE.match(ln)
        if m and i + 1 < len(lines):
            arg = lines[i + 1].strip()
            if (m.groups(), arg) not in seen:
                seen.add((m.groups(), arg))
                out += [ln, "  " + arg]
    if not seen:
        print("simp: nothing to fix")
        return
    spec = importlib.util.spec_from_file_location("fix_unused_simp_args", MATHLIB_FIXER)
    fixer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fixer)
    touched = sorted({g[0] for g, _ in seen})
    before = {p: Path(p).read_text() for p in touched if Path(p).exists()}
    with tempfile.NamedTemporaryFile("w", suffix=".log", delete=False) as t:
        t.write("\n".join(out) + "\n")
    sys.argv = ["fix_unused_simp_args.py", t.name]
    fixer.main()
    tidied = 0
    for p, old_text in before.items():
        old = old_text.splitlines(keepends=True)
        new = Path(p).read_text().splitlines(keepends=True)
        sm = difflib.SequenceMatcher(None, old, new, autojunk=False)
        for tag, _, _, j1, j2 in sm.get_opcodes():
            if tag == "equal":
                continue
            for j in range(j1, j2):
                s = re.sub(r"\bsimp only \[\]", "simp only", new[j])
                s = re.sub(r"\bsimp \[\]", "simp", s)
                s = re.sub(r"\[ +(?=\S)", "[", s)
                if s != new[j]:
                    new[j], tidied = s, tidied + 1
        Path(p).write_text("".join(new))
    print(f"simp: {len(seen)} warnings, {tidied} lines tidied")


def fix_vars(lines):
    edits = defaultdict(set)
    for ln in lines:
        m = VAR_RE.match(ln)
        if m:
            edits[m[1]].add((int(m[2]), int(m[3]), m[4]))
    done = skipped = 0
    for p, es in edits.items():
        src = Path(p).read_text().splitlines(keepends=True)
        for line, col, name in sorted(es, reverse=True):
            s = src[line - 1]
            end = col + len(name)
            if s[col:end] == name and (end == len(s) or not (s[end].isalnum() or s[end] in "_'!?₀₁₂₃₄₅₆₇₈₉")):
                src[line - 1] = s[:col] + "_" + s[col:]
                done += 1
            else:
                print(f"  skip {p}:{line}:{col}: `{name}` not at that position")
                skipped += 1
        Path(p).write_text("".join(src))
    print(f"vars: {done} renamed to `_x`, {skipped} skipped")


def fix_deprecated(lines):
    edits = defaultdict(set)
    for ln in lines:
        m = DEP_RE.match(ln)
        if m:
            edits[m[1]].add((int(m[2]), int(m[3]), m[4], m[5]))
    done = skipped = 0
    ident = "_'!?₀₁₂₃₄₅₆₇₈₉."
    for p, es in edits.items():
        src = Path(p).read_text().splitlines(keepends=True)
        for line, col, old, new in sorted(es, reverse=True):
            s = src[line - 1]
            old_parts, new_parts = old.split("."), new.split(".")
            hit = None
            for k in range(len(old_parts)):  # the full name first, then suffixes
                written = ".".join(old_parts[k:])
                end = col + len(written)
                if s[col:end] != written or (end < len(s) and (s[end].isalnum() or s[end] in ident)):
                    continue
                if old_parts[:k] != new_parts[:k]:
                    continue
                hit = (end, ".".join(new_parts[k:]))
                break
            if hit:
                src[line - 1] = s[:col] + hit[1] + s[hit[0]:]
                done += 1
            else:
                print(f"  skip {p}:{line}:{col}: `{old}` not at that position")
                skipped += 1
        Path(p).write_text("".join(src))
    print(f"deprecated: {done} renamed, {skipped} skipped")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--only", choices=["simp", "vars", "deprecated"])
    a = ap.parse_args()
    lines = Path(a.log).read_text().splitlines()
    # Renaming keeps line numbers; dropping simp arguments can join lines,
    # so the renames go first, while the log's positions are still exact.
    if a.only in (None, "deprecated"):
        fix_deprecated(lines)
    if a.only in (None, "vars"):
        fix_vars(lines)
    if a.only in (None, "simp"):
        fix_simp(lines)


if __name__ == "__main__":
    main()
