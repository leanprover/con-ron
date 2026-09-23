/-
# `ConRon.Bridge.Frontend.Scratch` — the projection rewrite and the owner
census leave the scratch flag where they found it (task #97-P3-Frontend
round 8)

`ParseStep`'s `scratch` clause (`Bridge/Frontend/Rel.lean`) is what threads
`scratchOn = false` through the parse, and every other step of the parse gets
it from an intern spec that states it.  The two exceptions are the projection
rewrite (`Arena/Frontend/ProjRec.lean`'s `projRecValue`) and the owner census
(`projRecOwners`), whose callees' specs — the Inductives tier's recognisers at
`PStep`, and `Bridge/ExprOps/**`'s `…Fast` walks — do not frame the flag.
Round 8's ruling: rather than widen those tiers' frames, prove here that the
two functions' whole call trees never move it.  The only writers of
`scratchOn` in the arena are `enterScratch`/`dropScratch`, and neither is in
either call tree; this module is that observation as a proof.
-/
import ConRon.Bridge.Specs
import ConRon.Arena.Frontend.ProjRec

namespace ConRon.Bridge.Frontend

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-- con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue — **the
rewrite leaves the scratch flag where it found it.** -/
theorem projRecValue_scratch {fuel : Nat} {o : ProjRecOwner} {l : LIdx}
    {ty val : EIdx} {i : Nat} {s s' : AState} {r : Option EIdx}
    (hrun : projRecValue fuel o l ty val i s = .ok (r, s')) :
    s'.store.scratchOn = s.store.scratchOn := by
  sorry

/-- con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners — **the
owner census leaves the scratch flag where it found it**, through both
recognisers. -/
theorem projRecOwners_scratch {fuel : Nat} {block : List IConstantInfo}
    {types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)}
    {ctors : List (NIdx × Nat × EIdx)}
    {recs : List (NIdx × List NIdx × EIdx × Nat × Nat)} {s s' : AState}
    {os : List ProjRecOwner}
    (hrun : projRecOwners fuel block types ctors recs s = .ok (os, s')) :
    s'.store.scratchOn = s.store.scratchOn := by
  sorry

end ConRon.Bridge.Frontend
