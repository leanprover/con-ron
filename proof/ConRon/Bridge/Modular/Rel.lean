/-
# `ConRon.Bridge.Modular.Rel` — the worker's values read back (task #166)

The relations Theorem 1 of the worker states its results in: each twin value (over handles) is
upstream's value (over names and expressions) read back at a store.  The name positions
(`NPRel`, `NPsRel`), the name index (`IndexRel`), a clash (`ClashRel`), the reads
(`WorkerReadsRel`), the reach (`ReachRel`).  A twin map keyed by handles is upstream's keyed
by names through `HMRel` (`Bridge/Frontend/Olean/Levels.lean`); a map keyed by copies (two
numbers, upstream's own type) answers alike up to the values' denotation (`CopyMapRel`).
-/
module

public import ConRon.Bridge.Frontend.Olean.Levels
public import ConRon.Bridge.Frontend.Olean.Read
public import ConRon.Bridge.Frontend.Rel
public import ConRon.Arena.Modular.Worker
public import ConLeche.Driver.Worker

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConLeche.Frontend.Olean (Copy CKindF)

/-- con-leche: none — a statement over handles read back. -/
@[expose] def denoteStmt (st : EStore) (s : ConRon.Arena.Frontend.Olean.StmtRec) :
    Option ConstantVal := do
  pure ⟨← denoteN st.ns s.name, ← s.levelParams.mapM (denoteN st.ns), ← denoteE st s.type⟩

/-- con-leche: none — a kind with its expressions left out, its names read back. -/
@[expose] def denoteKindN (st : EStore) (k : CKindF NIdx Unit) : Option (CKindF ConLeche.Name Unit) :=
  k.mapM (denoteN st.ns) (fun _ => some ())

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:55-63 NamePosition — one name position read
back: its name denoted, the rest equal. -/
structure NPRel (st : EStore) (q : ConRon.Arena.Frontend.Olean.NamePosition)
    (qC : ConLeche.Frontend.Olean.NamePosition) : Prop where
  loc : q.loc = qC.loc
  name : denoteN st.ns q.name = some qC.name
  tag : q.tag = qC.tag
  skipped : q.skipped = qC.skipped

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:65-69 NamePositions — a module's name
positions read back: the header's flag equal, its imports denoted, each position related. -/
structure NPsRel (st : EStore) (p : ConRon.Arena.Frontend.Olean.NamePositions)
    (pC : ConLeche.Frontend.Olean.NamePositions) : Prop where
  isModule : p.header.isModule = pC.header.isModule
  imports : ImpsD st p.header.imports pC.header.imports
  consts : ListRel (NPRel st) p.consts.toList pC.consts.toList

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:41-49 NameIndex — the name index read
back: the parts related, the first copies a map over handles against one over names, the
later copies in order, each name denoted, each copy equal. -/
structure IndexRel (st : EStore) (ix : ConRon.Arena.Frontend.Olean.NameIndex)
    (ixC : ConLeche.Frontend.Olean.NameIndex) : Prop where
  parts : ListRel (NPsRel st) ix.parts.toList ixC.parts.toList
  first : HMRel (· = ·) st ix.first ixC.first
  more : ListRel (fun (a : NIdx × Copy) (b : ConLeche.Name × Copy) =>
    denoteN st.ns a.1 = some b.1 ∧ a.2 = b.2) ix.more.toList ixC.more.toList

/-- con-leche: none — one copy with its statement and kind read back. -/
@[expose] def CopyInfoRel (st : EStore)
    (x : Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)
    (y : Copy × ConstantVal × CKindF ConLeche.Name Unit) : Prop :=
  x.1 = y.1 ∧ denoteStmt st x.2.1 = some y.2.1 ∧ denoteKindN st x.2.2 = some y.2.2

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:68-72 Clash — a clash read back. -/
structure ClashRel (st : EStore) (cl : ConRon.Arena.Frontend.Olean.Clash)
    (clC : ConLeche.Frontend.Olean.Clash) : Prop where
  name : denoteN st.ns cl.name = some clC.name
  copies : ListRel (CopyInfoRel st) cl.copies.toList clC.copies.toList

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:150-161 WorkerReads — **the worker's reads
read back**. -/
structure WorkerReadsRel (st : EStore) (wr : ConRon.Arena.Frontend.Olean.WorkerReads)
    (wrC : ConLeche.Frontend.Olean.WorkerReads) : Prop where
  own : NPsRel st wr.own wrC.own
  loads : LoadsRel st wr.loads wrC.loads
  pub : wr.pub = wrC.pub
  index : IndexRel st wr.index wrC.index
  clashes : ListRel (ClashRel st) wr.clashes.toList wrC.clashes.toList

/-- con-leche: none — one pending statement of the reach read back. -/
@[expose] def PendRel (st : EStore) (x : String × NIdx × ConRon.Arena.Frontend.Olean.StmtRec)
    (y : String × ConLeche.Name × ConstantVal) : Prop :=
  denoteN st.ns x.2.1 = some y.2.1 ∧ denoteStmt st x.2.2 = some y.2.2

/-- con-leche: ConLeche/Driver/Reach.lean:925-931 Reach — **the reach read back**: the context
denoted, the homes and the completed names denoted, the counts equal. -/
structure ReachRel (st : EStore) (r : ConRon.Arena.Modular.Reach) (rC : ConLeche.Driver.Reach) :
    Prop where
  ctx : denoteDecls st r.ctx.toList = some rC.ctx.toList
  homes : ListRel (NR st) r.homes.toList rC.homes.toList
  completed : ListRel (fun (a : NIdx × NIdx) (b : ConLeche.Name × ConLeche.Name) =>
    denoteN st.ns a.1 = some b.1 ∧ denoteN st.ns a.2 = some b.2)
    r.completed.toList rC.completed.toList
  searches : r.searches = rC.searches
  inferred : r.inferred = rC.inferred

/-- con-leche: ConLeche/Driver/Reach.lean:734-743 ReachLog — **the reach's logical state read
back**: the name sets related, the records denoted, the homes, each record's reads and the stack
denoted. -/
structure ReachLogRel (st : EStore) (L : ConRon.Arena.Modular.ReachLog)
    (LC : ConLeche.Driver.ReachLog) : Prop where
  seen : SetRel st L.seen LC.seen
  stored : SetRel st L.stored LC.stored
  ctx : denoteDecls st L.ctx.toList = some LC.ctx.toList
  homes : ListRel (NR st) L.homes.toList LC.homes.toList
  reads : ListRel (fun (a : List NIdx) (b : List ConLeche.Name) => ListRel (NR st) a b)
    L.reads.toList LC.reads.toList
  stack : ListRel (NR st) L.stack LC.stack

theorem ReachRel.ext {st st' : EStore} {r : ConRon.Arena.Modular.Reach}
    {rC : ConLeche.Driver.Reach} (h : ReachRel st r rC) (hx : Ext st st') : ReachRel st' r rC :=
  ⟨denoteDecls_ext hx _ _ h.ctx, ListRel.mono' (fun _ _ h => denoteN_ext h hx) h.homes,
    ListRel.mono' (fun _ _ h => ⟨denoteN_ext h.1 hx, denoteN_ext h.2 hx⟩) h.completed,
    h.searches, h.inferred⟩

end ConRon.Bridge.Modular
