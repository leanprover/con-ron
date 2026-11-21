/-
# `ConRon.Bridge.Modular.ReachRecord` — the reach's records, Theorem 1 (task #166)

A group's record (`groupRecord_run`, upstream's `Olean/Group.lean`), a constant's record
(`recordOfEntry_run`, `Olean/Present.lean`), a part's recursors by block (`recBlocksOf_run`), a
group read from a part (`groupAt_run`), a copy as its statement (`stmtRecord_run`), the record
presenting a name (`readRecord_run`).  Run style.
-/
module

public import ConRon.Bridge.Modular.ReachStored
public import ConRon.Bridge.Frontend.Olean.Records
public import ConRon.Arena.Frontend.Olean.Group
public import ConRon.Arena.Frontend.Olean.Present
public import ConLeche.Frontend.Olean.Group
public import ConLeche.Frontend.Olean.Present

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins SM Merged CEntry Emit declsOf blockTys blockCtors
  blockRecs recMapOf)
open ConLeche.Frontend.Olean (Region Roots OLeanLevel ModFiles CEntryF CKindF Copy bind_some_left)

/-- A related list of stored names, as names. -/
theorem sr_names {st : EStore} {mg : Merged} :
    ∀ {l : List NIdx} {zs : List ConLeche.Frontend.Olean.CEntry}, ListRel (SR st mg) l zs →
      ListRel (NR st) l (zs.map (·.name))
  | _, _, .nil => .nil
  | _, _, .cons h hr => .cons h.1 (sr_names hr)

/-- A one-record emission's records, read back: its one record. -/
theorem decls_one {st : EStore} {ds : Array IDeclaration} {dsC : Array Declaration}
    (h : denoteDeclArray st ds = some dsC) {d : IDeclaration} (hd : ds[0]? = some d)
    (hs : ds.size = 1) : ∃ dC, dsC[0]? = some dC ∧ dsC.size = 1 ∧ Frontend.denoteDecl st d = some dC := by
  have hl := denoteDeclArray_iff.mp h
  have hd' : ds.toList = [d] := by
    rcases ds with ⟨l⟩
    match l, hs, hd with
    | [x], _, hd => simp at hd; simp [hd]
  rw [hd'] at hl
  simp only [denoteDecls] at hl
  cases hx : Frontend.denoteDecl st d with
  | none => simp [hx] at hl
  | some dC =>
    simp only [hx, Option.some.injEq] at hl
    refine ⟨dC, ?_, ?_, rfl⟩
    · rcases dsC with ⟨lC⟩; simp only at hl; subst hl; rfl
    · rcases dsC with ⟨lC⟩; simp only at hl; subst hl; rfl

/-- con-leche: ConLeche/Frontend/Olean/Group.lean:56-69 groupRecord — **one inductive group's
record**: the twin's accept is upstream's, the record read back. -/
theorem groupRecord_run {pk : OleanPins} {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false) (hpins : PinsOK s)
    (hc : WalkCtx s.store mg mgC) (hp : PinsRel s.store pk) {n : NIdx} {nC : ConLeche.Name}
    (hn : denoteN s.store.ns n = some nC) {d : IDeclaration}
    (h : ConRon.Arena.Frontend.Olean.groupRecord pk mg n s = .ok (d, s')) :
    ParseStep s s' ∧ PersDecl d ∧ ∃ dC, ConLeche.Frontend.Olean.groupRecord mgC nC = .ok dC ∧
      Frontend.denoteDecl s'.store d = some dC := by
  unfold ConRon.Arena.Frontend.Olean.groupRecord at h
  unfold ConLeche.Frontend.Olean.groupRecord
  unfold ConRon.Arena.Frontend.Olean.groupParts at h
  unfold ConLeche.Frontend.Olean.groupParts
  cases hg : mg.get n with
  | none =>
    rw [hg] at h
    exfalso; am_never h
  | some x =>
  rw [hg] at h
  obtain ⟨xC, hxC, hdx⟩ := hc.rel.got hn hg
  rw [hxC]
  obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hdx
  dsimp only at h ⊢
  cases hk1 : x.c.kind with
  | induct np ni al cs nn ir iu irf =>
    obtain ⟨allC, csC, hzk, hal, -⟩ := kindCtors_rel hk hk1
    rw [hk1] at h
    rw [hzk]
    dsimp only at h ⊢
    have htys := blockTys_rel hc hal
    have hcts := blockCtors_rel hc htys
    have hrcs : ListRel (SR s.store mg) (blockRecs mg (recMapOf mg) n)
        (ConLeche.Frontend.Olean.blockRecs mgC (ConLeche.Frontend.Olean.recMapOf mgC) nC) :=
      blockTys_rel hc (recMapOf_rel hc _ _ hn)
    have hall := ListRel.append (ListRel.append htys hcts) hrcs
    obtain ⟨u, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨rfl, hfm⟩ := forM_rel (fun x xC u s' hx hr => blockStep_run hc hp hx hr)
      (.cons hn (sr_names hall)) h1
    rw [hfm]
    dsimp only
    obtain ⟨r, s₂, h3, h4⟩ := AM.bind_ok h2
    rcases r with ⟨e, k⟩ | ds
    · exfalso; am_never h4
    obtain ⟨hst, hpr, dsC, hdC, hden⟩ := declsOf_run hok hoff hpins
      (EmitRel.block (EmitRel.empty _) htys hcts hrcs) h3
    unfold ConRon.Arena.Frontend.Olean.groupEmit at h3
    unfold ConLeche.Frontend.Olean.groupEmit
    rw [hdC]
    dsimp only at h4 ⊢
    cases hd0 : ds.decls[0]? with
    | none => rw [hd0] at h4; exfalso; am_never h4
    | some d0 =>
    rw [hd0] at h4
    dsimp only at h4
    by_cases hs1 : ds.decls.size == 1
    · rw [ite_eq_left hs1] at h4
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
      obtain ⟨dC, h0, hsz, hdd⟩ := decls_one hden hd0 (beq_iff_eq.mp hs1)
      rw [h0]
      simp only [hsz, beq_self_eq_true, ↓reduceIte]
      refine ⟨hst, hpr d (Array.mem_of_getElem? hd0), dC, rfl, hdd⟩
    · rw [ite_eq_right hs1] at h4; exfalso; am_never h4
  | _ =>
    rw [hk1] at h
    exfalso; am_never h

end ConRon.Bridge.Modular
