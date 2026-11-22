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

/-- `graphStage_run`, with the closure denoted the twin's nodes' (`NodeD` at the walk's last
state): what `--modular` reads its modules' names back from. -/
theorem graphStage_run_nodes {F : FS} {sp : Roots} (hsp : sp.bare = sp) {names : List ConLeche.Name}
    {sA sB sC sD : AState} {pk : OleanPins} {roots : List NIdx} {C : Array Node}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hP : ConRon.Arena.Frontend.Olean.oleanPins sA = .ok (pk, sB))
    (hR : names.mapM ConRon.Arena.internName sB = .ok (roots, sC))
    (hG : graphOf (modelFs F) pk sp roots none sC = .ok (C, sD)) :
    ∃ (CC : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      ListRel (NodeD sD.store) C.toList CC ∧
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
  obtain ⟨-, CC, hlr, rk, hgood, hroots, hedges, hinj, hhdr⟩ :=
    graphOf_run (cmp := none) (extra := fun _ => #[]) hsp hctx (fun _ => rfl) hnr (fun r hr => hr)
      (fun _ i hi => by simp at hi) hG
  exact ⟨CC, rk, hlr, fun e he => (hgood e he).plain, hroots, hedges, hinj, hhdr⟩

/-- con-leche: ConLeche/Verify/Driver/Graph.lean checkGraphG_ok — **the graph check of a compared
run at the twin** (`--check-graph --compare`): the challenge and the solution interned, the graph
of the challenge's closure with `import all` of the solution added to its header (`cmpExtra`):
upstream's facts at the added imports, every module in the headers' closure of both. -/
theorem graphStageCmp_run {F : FS} {sp : Roots} (hsp : sp.bare = sp) {cC sC : ConLeche.Name}
    {sA sB sC' sD : AState} {pk : OleanPins} {c s : NIdx} {C : Array Node}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hP : ConRon.Arena.Frontend.Olean.oleanPins sA = .ok (pk, sB))
    (hR : [cC, sC].mapM ConRon.Arena.internName sB = .ok ([c, s], sC'))
    (hG : graphOf (modelFs F) pk sp [c] (some (c, s)) sC' = .ok (C, sD)) :
    ∃ (CC : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      (∀ e ∈ CC, ConLeche.Driver.Graph.NodeOk sp F (ConLeche.Driver.Graph.cmpExtra cC sC) e) ∧
      cC ∈ CC.map (·.1) ∧
      (∀ e ∈ CC, ∀ i ∈ e.2, i.module ∈ CC.map (·.1) ∧ rk i.module < rk e.1) ∧
      (CC.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ CC, ConLeche.Frontend.Olean.HdrClosure sp F [cC, sC] e.1) := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  obtain ⟨hokA, -, -, -, hoffA, -, -⟩ := internReservedPins_run hok0 rfl hA
  obtain ⟨hstP, hpk⟩ := oleanPins_run hokA hoffA hP
  have hoffB : sB.store.scratchOn = false := by rw [hstP.scratch]; exact hoffA
  obtain ⟨hstR, hnr⟩ := internNames_run hstP.ok hoffB [cC, sC] hR
  have hctx : Ctx pk sC' :=
    ⟨hstR.ok, by rw [hstR.scratch]; exact hoffB, (hpk.ext hstR.ext).nulls⟩
  cases hnr with
  | cons hc hnr' =>
  cases hnr' with
  | cons hs _ =>
  obtain ⟨-, CC, -, rk, hgood, hroots, hedges, hinj, hhdr⟩ :=
    graphOf_run (cmp := some (c, s)) (extra := ConLeche.Driver.Graph.cmpExtra cC sC)
      (roots' := [cC, sC]) hsp hctx ⟨cC, sC, hc, hs, rfl⟩ (.cons hc .nil)
      (fun r hr => by simp at hr; simp [hr])
      (fun m i hi => by
        unfold ConLeche.Driver.Graph.cmpExtra at hi
        split at hi
        · simp [ConLeche.Driver.Graph.solutionImport] at hi; simp [hi]
        · simp at hi) hG
  exact ⟨CC, rk, hgood, hroots cC (by simp), hedges, hinj, hhdr⟩

/-- `graphStageCmp_run`, with the closure denoted the twin's nodes' (`NodeD` at the walk's last
state): what `--modular --compare` reads its modules' names back from. -/
theorem graphStageCmp_run_nodes {F : FS} {sp : Roots} (hsp : sp.bare = sp) {cC sC : ConLeche.Name}
    {sA sB sC' sD : AState} {pk : OleanPins} {c s : NIdx} {C : Array Node}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hP : ConRon.Arena.Frontend.Olean.oleanPins sA = .ok (pk, sB))
    (hR : [cC, sC].mapM ConRon.Arena.internName sB = .ok ([c, s], sC'))
    (hG : graphOf (modelFs F) pk sp [c] (some (c, s)) sC' = .ok (C, sD)) :
    ∃ (CC : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      ListRel (NodeD sD.store) C.toList CC ∧
      (∀ e ∈ CC, ConLeche.Driver.Graph.NodeOk sp F (ConLeche.Driver.Graph.cmpExtra cC sC) e) ∧
      cC ∈ CC.map (·.1) ∧
      (∀ e ∈ CC, ∀ i ∈ e.2, i.module ∈ CC.map (·.1) ∧ rk i.module < rk e.1) ∧
      (CC.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ CC, ConLeche.Frontend.Olean.HdrClosure sp F [cC, sC] e.1) := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  obtain ⟨hokA, -, -, -, hoffA, -, -⟩ := internReservedPins_run hok0 rfl hA
  obtain ⟨hstP, hpk⟩ := oleanPins_run hokA hoffA hP
  have hoffB : sB.store.scratchOn = false := by rw [hstP.scratch]; exact hoffA
  obtain ⟨hstR, hnr⟩ := internNames_run hstP.ok hoffB [cC, sC] hR
  have hctx : Ctx pk sC' :=
    ⟨hstR.ok, by rw [hstR.scratch]; exact hoffB, (hpk.ext hstR.ext).nulls⟩
  cases hnr with
  | cons hc hnr' =>
  cases hnr' with
  | cons hs _ =>
  obtain ⟨-, CC, hlr, rk, hgood, hroots, hedges, hinj, hhdr⟩ :=
    graphOf_run (cmp := some (c, s)) (extra := ConLeche.Driver.Graph.cmpExtra cC sC)
      (roots' := [cC, sC]) hsp hctx ⟨cC, sC, hc, hs, rfl⟩ (.cons hc .nil)
      (fun r hr => by simp at hr; simp [hr])
      (fun m i hi => by
        unfold ConLeche.Driver.Graph.cmpExtra at hi
        split at hi
        · simp [ConLeche.Driver.Graph.solutionImport] at hi; simp [hi]
        · simp at hi) hG
  exact ⟨CC, rk, hlr, hgood, hroots cC (by simp), hedges, hinj, hhdr⟩

end ConRon.Bridge.Modular
