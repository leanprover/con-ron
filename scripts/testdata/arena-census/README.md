# `scripts/testdata/arena-census` — the census's fixture

`scripts/arena-census.py --selftest` runs the WHOLE census over this
directory instead of the repository, and compares what it says with
`expected.txt`.

It is a miniature of the real tree: twenty twins taken from
`proof/ConRon/Arena/**` at task #97-CENSUS's tip, each with its real name,
its real Bridge theorem name, its real `sorry` state, its real Rust function
and its real `Refine2` lemma — so every row's verdict here is the verdict
the census gives that twin in the repository, confirmed by hand before it
was copied in.  Bodies are elided to one line and a walk's five arms are cut
down to two, neither of which changes a verdict.  The twenty were chosen so
that every verdict the census can reach appears at least once (closed,
`sorry`, `part`, unstated, uncited, `_no_claim`, skipped for both, skipped
for T1 only, and a walk whose ARM carries its own spec).

Why a fixture and not the real tree: eight agents are writing under
`proof/` at any moment, so a self-test pinned to the repository's own
verdicts would go red every hour and say nothing about the script.  This
copy does not move, so a red `--selftest` is always a bug in
`arena-census.py`.

Two liberties, both deliberate:

* the `Lean twin:` citations carry **no line range**.  The census reads only
  the PATH and the NAME out of a citation (the ranges are
  `scripts/twin-lines.py`'s business, and it has its own gate), and ranges
  here would have to be re-pointed every time a fixture line moved;
* the Lean does not elaborate and is not meant to.  Every parser this
  fixture exercises — `provenance.top_level_decls`, `extend_block`,
  `comment_lines`, `twin-lines`' doc-block scanner — is a regex over source
  text, which is exactly the surface being tested.
