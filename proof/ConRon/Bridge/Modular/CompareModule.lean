/-
# `ConRon.Bridge.Modular.CompareModule` — the challenge's closure walk, Theorem 1 (task #166)

**An accepting twin `chalWalk` is the graph of the challenge's closure through its lookup alone,
checked** (`chalWalk_run`): `graphOf_run` at the one root and no added import.  Upstream's
`chalWalk` answers `none` exactly where that graph is accepted; its modular theorems
(`compare_sees_isModel`, `compare_no_False`) ask nothing of it.
-/
module

public import ConRon.Arena.Modular.CompareModule
public import ConRon.Bridge.Modular.Graph

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge ConRon.Bridge.Frontend ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins)
open ConLeche.Frontend.Olean (Roots)
open ConLeche.Driver.Graph (NodeOk)

/-- con-leche: ConLeche/Driver/CompareModule.lean:36-47 chalWalk — **the challenge's closure
through its own lookup, checked**: `graphOf_run` at the root `c`, no import added. -/
theorem chalWalk_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {c : NIdx} {cC : ConLeche.Name} {s s' : AState}
    (hctx : Ctx pk s) (hc : denoteN s.store.ns c = some cC)
    (h : ConRon.Arena.Modular.chalWalk (modelFs F) pk sp c s = .ok ((), s')) :
    ParseStep s s' ∧ ∃ CC : List ConLeche.Driver.Graph.Node, ∃ rk : ConLeche.Name → Nat,
      (∀ e ∈ CC, NodeOk sp F (fun _ => #[]) e) ∧ cC ∈ CC.map (·.1) ∧
      (∀ e ∈ CC, ∀ i ∈ e.2, i.module ∈ CC.map (·.1) ∧ rk i.module < rk e.1) ∧
      (CC.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ CC, ConLeche.Frontend.Olean.HdrClosure sp F [cC] e.1) := by
  simp only [ConRon.Arena.Modular.chalWalk] at h
  obtain ⟨C, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨-, rfl⟩ := AM.pure_ok h2
  obtain ⟨hst, CC, -, rk, hgood, hroots, hedges, hinj, hhdr⟩ :=
    graphOf_run (roots' := [cC]) (cmp := none) (extra := fun _ => #[]) hsp hctx
      (show ExtraRel s.store none (fun _ => #[]) from fun _ => rfl)
      (.cons hc .nil) (fun r hr => hr) (fun _ i hi => by simp at hi) h1
  exact ⟨hst, CC, rk, hgood, hroots cC (List.mem_singleton_self _), hedges, hinj, hhdr⟩

end ConRon.Bridge.Modular
