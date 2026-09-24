# `scripts/testdata/arena-census` — the census's fixture

`scripts/arena-census.py --selftest` runs the WHOLE census over this
directory instead of the repository, and compares what it says with
`expected.txt`.

It is a miniature of the real tree: twenty-six twins taken from
`proof/ConRon/Arena/**` at task #97-CENSUS's tip, each with its real name,
its real Bridge theorem name, its real `sorry` state, its real Rust function
and its real `Refine2` lemma — so every row's verdict here is the verdict
the census gives that twin in the repository, confirmed by hand before it
was copied in.  Bodies are elided to one line and a walk's five arms are cut
down to two, neither of which changes a verdict.  They were chosen so that
every verdict the census can reach appears at least once (closed, `sorry`,
`part`, unstated, uncited, `_no_claim`, skipped for both, skipped for T1
only, and a walk whose ARM carries its own spec).

Task #97-CENSUS round 2 added `Arena/Store.lean` and its `arena/store.rs`,
which carry the rules round 1 did not have — and `expected.txt` pins the
self-check COUNTS (`@ <key> <n>`) beside the per-row verdicts, because a
convention is not a row:

* **the namespace is part of the name.**  `dropScratch` is declared twice
  (in `NStore` and in `EStore`) and `find?` twice (in `Tbl` and in
  `EStore`), so a census keyed by the declared name alone would show one row
  each and lose a twin;
* **one theorem credits one twin.**  `viewApp_spec` is `Monad.lean`'s
  `viewApp` and `EStore.viewApp_spec` is `Store.lean`'s, by namespace;
  `dropScratch_run` names neither namespace, so it is credited to the first
  by module and line and reported AMBIGUOUS;
* **the T2 shapes.**  `tbl_find_abs`, `estore_view_app_abs`,
  `derived_e_run` and `estore_der_of_bvar_obs` are Theorem 2 statements, and
  the first two are qualified by the RECEIVER — `Tbl::find` and
  `EStore::find` are both `find` to `provenance.RustItem.name()`, and
  `estore_find_abs` deliberately does not exist so that `EStore.find?`
  still reads "cited, nothing stated";
* **the doc-comment escape hatch.**  `eidxCopyUpto_toList` says "Theorem 1
  for `eidxCopyUpto`" in its own doc block, and the row is `closed` because
  of that sentence and nothing else.

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
