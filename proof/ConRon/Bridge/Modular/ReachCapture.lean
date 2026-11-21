/-
# `ConRon.Bridge.Modular.ReachCapture` — agreement and the capture check, Theorem 1 (task #166)

The reach's checks over its caches: a loaded copy's spot (`importerSpot_rel`), a copy's proof
flag (`proofStatus_run`), two copies' agreement (`agreeCheck_run`), the clash rule
(`clashAgree_run`), the capture check of one read (`captureOne_run`) and of a record's reads, the
names a record stores (`storedNamesOk_run`).  Each twin accept is upstream's answer, the caches
related after.  What one expression reads (`NeedsExprHyp`) is the needs walk's Theorem 1,
taken as a hypothesis here.  Run style, not `vcgen`.
-/
module

public import ConRon.Bridge.Modular.ReachParts

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins SM)
open ConLeche.Frontend.Olean (Region Roots OLeanLevel ModFiles CEntryF CKindF Copy)

/-- con-leche: ConLeche/Cached/Needs.lean:44 needsGo — **what one expression reads**, the
twin's walk from a fresh state against upstream's: the needs walk's Theorem 1. -/
@[expose] def NeedsExprHyp : Prop :=
  ∀ {s s' : AState} {e : EIdx} {eC : Expr} {x : ConRon.Arena.NeedsSt},
    DriverOK s → s.store.scratchOn = false → denoteE s.store e = some eC →
    ConRon.Arena.NeedsSt.empty.expr e s = .ok (x, s') →
    DStep s s' ∧ denoteNList s'.store.ns x.acc = some (ConLeche.Cached.needsGo {} #[] eC).2.toList

/-- con-leche: ConLeche/Driver/Reach.lean:376-382 ProofStatus — the twin's flag as upstream's. -/
@[expose] def psC : ConRon.Arena.Modular.ProofStatus → ConLeche.Driver.ProofStatus
  | .yes => .yes
  | .no => .no
  | .infer => .infer

/-! ## A loaded copy's spot -/

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:110-111 HeaderLoads.nameAt — a module's
name for messages, read back. -/
theorem nameAt_rel {st : EStore} {pk : OleanPins} (hp : NullsRel st pk)
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    (hl : LoadsRel st ld ldC) (i : Nat) :
    denoteN st.ns (ld.nameAt pk i) = some (ldC.nameAt i) := by
  unfold ConRon.Arena.Frontend.Olean.HeaderLoads.nameAt ConLeche.Frontend.Olean.HeaderLoads.nameAt
  rcases optRel_cases (listRel_getElem? hl.order i) with ⟨g1, g2⟩ | ⟨a, b, g1, g2, g3⟩
  · simp only [Array.getElem?_toList] at g1 g2
    rw [g1, g2]; exact hp.anon
  · simp only [Array.getElem?_toList] at g1 g2
    rw [g1, g2]; exact g3

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:51-53 NameIndex.at — a copy's name position,
read back. -/
theorem indexAt_rel {st : EStore} {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (h : IndexRel st ix ixC) (cp : Copy) :
    Option.Rel (NPRel st) (ix.at cp) (ixC.at cp) := by
  unfold ConRon.Arena.Frontend.Olean.NameIndex.at ConLeche.Frontend.Olean.NameIndex.at
  rcases optRel_cases (listRel_getElem? h.parts cp.mod) with ⟨g1, g2⟩ | ⟨a, b, g1, g2, g3⟩
  · simp only [Array.getElem?_toList] at g1 g2
    rw [g1, g2]; exact .none
  · simp only [Array.getElem?_toList] at g1 g2
    rw [g1, g2]
    have := listRel_getElem? g3.consts cp.pos
    simpa [Array.getElem?_toList] using this

/-- con-leche: ConLeche/Driver/Reach.lean:366-372 importerSpot — **the importer's copy of a
loaded name**, upstream's. -/
theorem importerSpot_rel {st : EStore} (hw : NStoreWF st.ns) {pk : OleanPins} (hp : NullsRel st pk)
    {sp : Roots} {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    (he : EnvRel sp st env envC) {y : NIdx} {yC : ConLeche.Name} (hy : denoteN st.ns y = some yC) :
    Option.Rel (fun (a : Nat × ConRon.Arena.Modular.Spot) (b : Nat × ConLeche.Driver.Spot) =>
        a.1 = b.1 ∧ SpotRel st a.2 b.2)
      (ConRon.Arena.Modular.importerSpot pk env y) (ConLeche.Driver.importerSpot envC yC) := by
  unfold ConRon.Arena.Modular.importerSpot ConLeche.Driver.importerSpot
  have hf := he.wr.index.first.get_eq hw hy
  simp only [Option.bind_eq_bind, hf]
  cases hfC : envC.wr.index.first[yC]? with
  | none => exact .none
  | some cp =>
    simp only [Option.bind_some]
    rcases optRel_cases (indexAt_rel he.wr.index cp) with ⟨g1, g2⟩ | ⟨q, qC, g1, g2, g3⟩
    · rw [g1, g2]; exact .none
    · rw [g1, g2]
      refine .some ⟨rfl, ⟨nameAt_rel hp he.wr.loads cp.mod, ?_⟩, g3⟩
      simp [ConRon.Arena.Frontend.Olean.HeaderLoads.levelAt, he.wr.loads.flags]

end ConRon.Bridge.Modular
