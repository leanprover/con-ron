/-
# `ConRon.Bridge.Modular.Accepted` — an accepted worker at the twin is upstream's (task #166)

The composition of the worker's Theorem 1: the twin's `workerRead` accepting, then its check
phase from `start` accepting and its inferred flags accepting, give upstream's `WorkerAccepted`
(`ConLeche/Verify/Driver/Worker.lean`): the facts of what the worker read and checked
(`WorkerFacts`), and the pure run of the own records, their theorems' values in place, from the
context's environment.

* `workerRead_run` — the twin's phases 1–4 against upstream's, piece by piece: the home
  (`HomeHyp`), the reads (`workerReads_run`), the own records (`ownRecords_run`), the holes, the
  roots (`rootsAt_exact`), the reach (`ReachRunHyp`), the context's names (`ctxNamesNodup_run`),
  the copies (`copiesOk_run`), the own records in the hoist's order (`recsOf_run`).
-/
module

public import ConRon.Bridge.Modular.Reads
public import ConRon.Bridge.Modular.Worker
public import ConRon.Bridge.Modular.Roots
public import ConRon.Bridge.Modular.Copies
public import ConRon.Bridge.Modular.Flags
public import ConRon.Bridge.Modular.ReachTail
public import ConRon.Bridge.Checker.PoolFrom
public import ConLeche.Verify.Driver.Worker

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins Loaded)
open ConLeche.Frontend.Olean (Roots ImportF ImportRec Expo)

/-- con-leche: none — `DriverOK` across a read of the files. -/
theorem DriverOK.of_parse {s s' : AState} (h : DriverOK s) (hp : ParseStep s s') : DriverOK s' :=
  DriverOK.of_check ⟨hp.ok, h.caches.monoF hp.ext hp.cframe, h.pins.mono hp.ext hp.pins,
    h.ienv.mono hp.ext⟩ hp.pins

/-- con-leche: ConLeche/Verify/Driver/Worker.lean WorkerFacts.home — **the home at the twin**:
the private files read and the private view loaded and checked give upstream's load of them
(`LoadOf`) and its views' check, the load read back, its frontier good on the files' region. -/
@[expose] def HomeHyp : Prop :=
  ∀ {pk : OleanPins} {F : FS} {sp : Roots} {s s₁ s' : AState} {m : NIdx} {mC : ConLeche.Name}
    {f : ConLeche.Frontend.Olean.ModFiles} {l : Loaded} {expo : Array Expo},
    sp.bare = sp → Ctx pk s → denoteN s.store.ns m = some mC →
    ConRon.Arena.Frontend.Olean.liftE
      (ConRon.Arena.Frontend.Olean.readFiles (modelFs F) sp mC .private) s = .ok (f, s₁) →
    ConRon.Arena.Modular.homeOf pk m f s₁ = .ok ((l, expo), s') →
    ParseStep s s' ∧ ∃ lC expoC,
      ModelIO.Gives (ConLeche.Frontend.Olean.readFiles sp mC .private : ModelIO _) F (.ok f) ∧
      ConLeche.Driver.LoadOf 0 mC f lC ∧
      ConLeche.Frontend.Olean.checkViews mC f lC = .ok expoC ∧
      LoadedRel s'.store l lC ∧ FrontGoodAt s'.store f l.frontier

/-- con-leche: ConLeche/Verify/Driver/Worker.lean WorkerFacts.reach — **the reach at the twin**:
its accept gives upstream's context and pending statements, read back, and upstream's reach
answering it under every flag inference that accepts them. -/
@[expose] def ReachRunHyp : Prop :=
  ∀ {pk : OleanPins} {F : FS} {sp : Roots} {s s' : AState} {m : NIdx} {mC : ConLeche.Name}
    {wr : ConRon.Arena.Frontend.Olean.WorkerReads} {wrC : ConLeche.Frontend.Olean.WorkerReads}
    {own : Std.HashSet NIdx} {ownC : Std.HashSet ConLeche.Name}
    {roots : Array NIdx} {rootsC : Array ConLeche.Name} {r : ConRon.Arena.Modular.Reach},
    sp.bare = sp → DriverOK s → s.store.scratchOn = false → PinsRel s.store pk →
    denoteN s.store.ns m = some mC → WorkerReadsRel s.store wr wrC → LoadsKeys wr.loads wrC.loads →
    SetRel s.store own ownC → ListRel (NR s.store) roots.toList rootsC.toList →
    ConRon.Arena.Modular.reach (modelFs F) pk sp m wr own roots s = .ok (r, s') →
    DStep s s' ∧ (∀ d ∈ r.ctx.toList, PersDecl d) ∧ ∃ rC pendC, ReachRel s'.store r rC ∧
      ListRel (PendRel s'.store) r.pending.toList pendC ∧
      ∀ fl : ConLeche.Driver.FlagInfer, fl rC.ctx.toList pendC = .ok () →
        ModelIO.CanGive (ConLeche.Driver.reachWith fl (.ofPath sp) mC wrC ownC rootsC) F
          (.ok rC)

end ConRon.Bridge.Modular
