/-
# `ConRon.Bridge.Promote` — the promotion tier (task #97-P3-Checker)

DESIGN §8.3's "Phase A runs in the scratch tier too, with promotion" (task
#97-P6-2) put a memoised structural copy scratch → persistent on the fold's
path, and `Arena/Promote.lean`'s own note names what the bridge owes for it:
`denote (promote h) = denote h`, `StoreWF` through `promote … dropScratch`,
and the memo invariant.  This is that tier.

* `Bridge/Promote/Pers.lean` — the PERSISTENT extension `PExt` (DESIGN §8.2's
  `Ext` conjunct, corrected for a bracketed step) and the `Pers…` vocabulary;
* `Bridge/Promote/Weak.lean` — the readback (`denote*_unfold'`) and the
  closing `dropScratch` (`PExt.dropScratch'`) at `Arena/WF.lean`'s
  promote-window invariant `StoreWF'`;
* `Bridge/Promote/StoreP.lean` — the four `internPersistent` obligations at
  `StoreWF'` (task #97-P3-Promote deleted this file's own `StoreWFP`, which
  task #97-P5-Fresh §6 found wrong in three places);
* `Bridge/Promote/Memo.lean` — `PMemoOK` (the memo's rows are promoted
  pairs) and `PFrame`;
* `Bridge/Promote/Walk.lean`, `Bridge/Promote/WalkDecl.lean` — the four
  handle-kind promotions and the declaration layer above them, run forwards
  (task #97-P3-Promote);
* `Bridge/Promote/Exact.lean` — the specs the checker tier reads
  (`promote*_spec`, `promoteNew_pushed`, `promoteNew_projOK`,
  `promoteBracket_close`);
* `Bridge/Promote/Coh.lean` — the index coherence after `promoteNew`, at the
  extensional definition the promotion can meet (task #97-P3-Promote's
  finding).
-/
import ConRon.Bridge.Promote.Pers
import ConRon.Bridge.Promote.Weak
import ConRon.Bridge.Promote.StoreP
import ConRon.Bridge.Promote.Memo
import ConRon.Bridge.Promote.Walk
import ConRon.Bridge.Promote.WalkDecl
import ConRon.Bridge.Promote.Exact
import ConRon.Bridge.Promote.Coh
