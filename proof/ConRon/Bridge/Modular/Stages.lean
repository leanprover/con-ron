/-
# `ConRon.Bridge.Modular.Stages` — the modular runs' stages at the twin, Theorem 1 (task #166)

The twin's stages of a modular run, from its start state, give upstream's facts:

* `graphStage_run` — **the graph check** (`--check-graph`, and `--modular`'s first step): the
  reserved pins, the reader's pins, the roots interned, `graphOf` with no import added, give
  upstream's `checkGraphG_ok` facts: the closure `CC` of upstream's nodes, each module's imports
  its header's on the snapshot, the roots in it, a one-to-one rank decreasing along every import,
  every module in the headers' closure of the roots.
-/
module

public import ConRon.Bridge.Modular.Graph
public import ConRon.Bridge.Stages
public import ConRon.Bridge.Checker.Pins

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins)
open ConRon.Arena.Modular (Node graphOf)
open ConLeche.Frontend.Olean (Roots)

/-- con-leche: ConLeche/Verify/Driver/Graph.lean checkGraphG_ok — **the graph check at the twin,
from its start state**: the reserved pins, the reader's pins, the roots interned and the graph,
no import added, give upstream's facts over the closure denoted (`CC`). -/
theorem graphStage_run {F : FS} {sp : Roots} (hsp : sp.bare = sp) {names : List ConLeche.Name}
    {sA sB sC sD : AState} {pk : OleanPins} {roots : List NIdx} {C : Array Node}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hP : ConRon.Arena.Frontend.Olean.oleanPins sA = .ok (pk, sB))
    (hR : names.mapM ConRon.Arena.internName sB = .ok (roots, sC))
    (hG : graphOf (modelFs F) pk sp roots none sC = .ok (C, sD)) :
    ∃ (CC : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      (∀ e ∈ CC, ModelIO.CanGive (ConLeche.Frontend.Olean.moduleImports sp e.1) F (.ok e.2)) ∧
      (∀ r ∈ names, r ∈ CC.map (·.1)) ∧
      (∀ e ∈ CC, ∀ i ∈ e.2, i.module ∈ CC.map (·.1) ∧ rk i.module < rk e.1) ∧
      (CC.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ CC, ConLeche.Frontend.Olean.HdrClosure sp F names e.1) := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  obtain ⟨hokA, -, -, -, hoffA, -, -⟩ := internReservedPins_run hok0 rfl hA
  obtain ⟨hstP, hpk⟩ := oleanPins_run hokA hoffA hP
  have hoffB : sB.store.scratchOn = false := by rw [hstP.scratch]; exact hoffA
  obtain ⟨hstR, hnr⟩ := internNames_run hstP.ok hoffB names hR
  have hctx : Ctx pk sC :=
    ⟨hstR.ok, by rw [hstR.scratch]; exact hoffB, (hpk.ext hstR.ext).nulls⟩
  obtain ⟨-, CC, -, rk, hgood, hroots, hedges, hinj, hhdr⟩ :=
    graphOf_run (cmp := none) (extra := fun _ => #[]) hsp hctx (fun _ => rfl) hnr (fun r hr => hr)
      (fun _ i hi => by simp at hi) hG
  exact ⟨CC, rk, fun e he => (hgood e he).plain, hroots, hedges, hinj, hhdr⟩

end ConRon.Bridge.Modular
