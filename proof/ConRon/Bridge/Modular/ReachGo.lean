/-
# `ConRon.Bridge.Modular.ReachGo` — the reach's worklist and the reach, Theorem 1 (task #166)

The twin's worklist (`reachGo`: `reachRead` at a name popped, `reachPartners` at an empty stack)
against upstream's `reachGo`, over the log's relation (`ReachLogRel`), and the reach's headline
(`reachRunHyp_holds'`, `ReachRunHyp` of `Accepted.lean`) gluing the clash rule, the worklist, the
read order, the validation and the flags' pending statements.  The record read at a name
(`readRecord`) is taken in the shape `ReadRecordHyp`.  Run style throughout.
-/
module

public import ConRon.Bridge.Modular.ReachRecord
public import ConRon.Bridge.Modular.Accepted

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins SM)
open ConLeche.Frontend.Olean (Region Roots OLeanLevel ModFiles CEntryF CKindF Copy)

/-- con-leche: ConLeche/Driver/Reach.lean:693-729 readRecord — **the record read at `x`, at the
twin**: its accept is upstream's, the record and its home read back, the caches related after,
the record persistent. -/
@[expose] def ReadRecordHyp : Prop :=
  ∀ {pk : OleanPins} {F : FS} {sp : Roots} {env : ConRon.Arena.Modular.ReachEnv}
    {envC : ConLeche.Driver.ReachEnv ModelIO} {c c' : ConRon.Arena.Modular.ReachCache}
    {cC : ConLeche.Driver.ReachCache} {x : NIdx} {xC : ConLeche.Name} {s s' : AState}
    {d : IDeclaration} {h : NIdx},
    sp.bare = sp → RCtx pk s → EnvRel sp s.store env envC → CacheRel s.store c cC →
    denoteN s.store.ns x = some xC →
    ConRon.Arena.Modular.readRecord (modelFs F) pk sp env c x s = .ok ((c', d, h), s') →
    DStep s s' ∧ PersDecl d ∧ ∃ cC' dC hC,
      ModelIO.Gives (ConLeche.Driver.readRecord envC cC xC) F (cC', .ok (dC, hC)) ∧
      CacheRel s'.store c' cC' ∧ ConRon.Arena.Frontend.denoteDecl s'.store d = some dC ∧
      denoteN s'.store.ns h = some hC

end ConRon.Bridge.Modular
