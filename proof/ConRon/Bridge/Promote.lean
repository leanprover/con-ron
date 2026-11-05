/-
# `ConRon.Bridge.Promote` — the promotion tier

DESIGN §8.3's "Phase A runs in the scratch tier too, with promotion" (DESIGN
`### Task #97-P6-2`) puts a memoised structural copy scratch → persistent on
the fold's path, and `Arena/Promote.lean`'s own note names what the bridge owes
for it: `denote (promote h) = denote h`, `StoreWF` through `promote …
dropScratch`, and the memo invariant.  This is that tier.

* `Bridge/Promote/Pers.lean` — the PERSISTENT extension `PExt` (DESIGN §8.2's
  `Ext` conjunct, corrected for a bracketed step) and the `Pers…` vocabulary;
* `Bridge/Promote/Weak.lean` — the readback (`denote*_unfold'`) at `Arena/WF.lean`'s
  promote-window invariant `StoreWF'`;
* `Bridge/Promote/Memo.lean` — `PSrc` (what a promotion needs of the store it runs on
  and the store its input denotes in), `PMemoPi` (the memo's rows are promoted
  pairs), `Kept` and `PFrame`;
* `Bridge/Promote/Proj.lean` — a persistent intern at the projection `st.dropScratch`,
  and `PSrc`'s constructors `PSrc.self`, `PSrc.of_run`;
* `Bridge/Promote/Walk.lean`, `Bridge/Promote/WalkDecl.lean` — the four
  handle-kind promotions and the declaration layer above them, run forwards over `PSrc`
  (`promoteE_pi`, `promoteL_pi`, `promoteLList_pi`);
* `Bridge/Promote/Exact.lean` — `promoteVG_pi`, `promoteNew_frame`, `promoteNew_pushed`,
  `promoteNew_tpushed`, `promoteNew_projOK`, `promoteBracket_close`;
* `Bridge/Promote/Coh.lean` — the fold's entries `promoteNew_pi` and
  `promoteNew_stored`, with the index coherence after `promoteNew` at the
  extensional definition the promotion can meet (DESIGN
  `### Task #97-P3-Promote`).
-/
module

public import ConRon.Bridge.Promote.Pers
public import ConRon.Bridge.Promote.Weak
public import ConRon.Bridge.Promote.Memo
public import ConRon.Bridge.Promote.Proj
public import ConRon.Bridge.Promote.Walk
public import ConRon.Bridge.Promote.WalkDecl
public import ConRon.Bridge.Promote.Exact
public import ConRon.Bridge.Promote.Coh

public section
