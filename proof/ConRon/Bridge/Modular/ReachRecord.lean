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
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Grind

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

/-- con-leche: ConLeche/Frontend/Olean/Present.lean:44-53 recordOfEntry — **a constant's record**:
the twin's accept is upstream's, the record read back. -/
theorem recordOfEntry_run {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false)
    (hpins : PinsOK s) {c : CEntryF NIdx EIdx} {cC : CEntryF ConLeche.Name Expr}
    (hc : denoteEntry s.store c = some cC) {d : IDeclaration}
    (h : ConRon.Arena.Frontend.Olean.recordOfEntry c s = .ok (d, s')) :
    ParseStep s s' ∧ PersDecl d ∧ ∃ dC, ConLeche.Frontend.Olean.recordOfEntry cC = .ok dC ∧
      Frontend.denoteDecl s'.store d = some dC := by
  unfold ConRon.Arena.Frontend.Olean.recordOfEntry at h
  unfold ConLeche.Frontend.Olean.recordOfEntry
  have hcr : CR s.store { c := c } (ConLeche.Frontend.Olean.CEntry.ofF cC) := by
    simp only [CR, denoteCEntry, hc]
    rfl
  obtain ⟨r, s₁, h1, h2⟩ := AM.bind_ok h
  rcases r with ⟨e, k⟩ | ds
  · exfalso; am_never h2
  obtain ⟨hst, hpr, dsC, hdC, hden⟩ := declsOf_run hok hoff hpins (EmitRel.one (EmitRel.empty _) hcr) h1
  rw [hdC]
  dsimp only at h2 ⊢
  have hl := denoteDeclArray_iff.mp hden
  generalize hdl : ds.decls.toList = dl at h2 hl
  generalize hdlC : dsC.toList = dlC at hl
  match dl, h2, hl with
  | [d1], h2, hl =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    simp only [denoteDecls] at hl
    cases hx : Frontend.denoteDecl s'.store d with
    | none => simp [hx] at hl
    | some dC =>
      simp only [hx, Option.some.injEq] at hl
      subst hl
      exact ⟨hst, hpr d (by rw [← Array.mem_toList_iff, hdl]; simp), dC, rfl, rfl⟩
  | [], h2, _ => exfalso; am_never h2
  | _ :: _ :: _, h2, _ => exfalso; am_never h2

/-! ## A part's recursors by block -/

theorem AM.bind_of {α β : Type} {x : AM α} {f : α → AM β} {s s₁ s' : AState} {a : α} {b : β}
    (h1 : x s = .ok (a, s₁)) (h2 : f a s₁ = .ok (b, s')) : (x >>= f) s = .ok (b, s') := by
  rw [AM.bind_apply, h1]; exact h2

/-- upstream's step of `recBlocksAt`'s fold. -/
@[expose] def rbStepC (m : Std.HashMap ConLeche.Name (Array Nat)) (x : Nat × CKindF ConLeche.Name Unit) :
    Std.HashMap ConLeche.Name (Array Nat) :=
  match x with
  | (l, k) => match k with
    | .recur (a :: _) .. => m.alter a fun | none => some #[l] | some xs => some (xs.push l)
    | _ => m

theorem recBlocksAdd_rel {st : EStore} (hw : NStoreWF st.ns) {m : Std.HashMap NIdx (Array Nat)}
    {mC : Std.HashMap ConLeche.Name (Array Nat)} (hm : HMRel (· = ·) st m mC) (l : Nat)
    {k : CKindF NIdx Unit} {kC : CKindF ConLeche.Name Unit} (hk : denoteKindN st k = some kC) :
    HMRel (· = ·) st (ConRon.Arena.Modular.recBlocksAdd m l k) (rbStepC mC (l, kC)) := by
  unfold denoteKindN at hk
  cases k with
  | recur all np ni nmo nmi rules kk iu =>
    simp only [CKindF.mapM] at hk
    obtain ⟨allC, hall, hk⟩ := bind_some_left hk
    obtain ⟨rulesC, -, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk
    subst hk
    cases all with
    | nil =>
      simp only [List.mapM_nil, pure, Option.some.injEq] at hall
      subst hall
      exact hm
    | cons a as =>
      simp only [List.mapM_cons] at hall
      obtain ⟨aC, ha, hall⟩ := bind_some_left hall
      obtain ⟨asC, -, hall⟩ := bind_some_left hall
      simp only [pure, Option.some.injEq] at hall
      subst hall
      simp only [ConRon.Arena.Modular.recBlocksAdd, rbStepC]
      have hget := hm.get_eq hw ha
      constructor
      · intro x v hx
        rw [Std.HashMap.getElem?_insert] at hx
        by_cases hxa : (a == x) = true
        · rw [ite_eq_left hxa] at hx
          cases hx
          have hxa' : a = x := eq_of_beq hxa
          subst hxa'
          refine ⟨aC, _, ha, ?_, rfl⟩
          rw [Std.HashMap.getElem?_alter, ite_eq_left (beq_self_eq_true aC), ← hget]
          cases m[a]? <;> rfl
        · rw [ite_eq_right hxa] at hx
          obtain ⟨n, b, h1, h2, h3⟩ := hm.fwd x v hx
          refine ⟨n, b, h1, ?_, h3⟩
          rw [Std.HashMap.getElem?_alter]
          have : (aC == n) = false := by
            cases hb : (aC == n)
            · rfl
            · exfalso; apply hxa
              have := eq_of_beq hb; subst this
              exact beq_iff_eq.mpr (denoteN_inj hw ha h1)
          rw [ite_eq_right (by simp [this])]
          exact h2
      · intro n b hn
        rw [Std.HashMap.getElem?_alter] at hn
        by_cases hna : (aC == n) = true
        · rw [ite_eq_left hna] at hn
          have : aC = n := eq_of_beq hna
          subst this
          refine ⟨a, _, ha, by rw [Std.HashMap.getElem?_insert, ite_eq_left (beq_self_eq_true a)], ?_⟩
          rw [hget]
          revert hn
          cases mC[aC]? <;> intro hn <;> cases hn <;> rfl
        · rw [ite_eq_right hna] at hn
          obtain ⟨x, v, h1, h2, h3⟩ := hm.bwd n b hn
          refine ⟨x, v, h1, ?_, h3⟩
          rw [Std.HashMap.getElem?_insert]
          have : (a == x) = false := by
            cases hb : (a == x)
            · rfl
            · exfalso; apply hna
              have := eq_of_beq hb; subst this
              rw [ha] at h1; cases h1; exact beq_self_eq_true _
          rw [ite_eq_right (by simp [this])]
          exact h2
  | ax _ => simp only [CKindF.mapM, pure, Option.some.injEq] at hk; subst hk; exact hm
  | defn _ _ _ =>
    simp only [CKindF.mapM] at hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk; subst hk; exact hm
  | thm _ _ =>
    simp only [CKindF.mapM] at hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
    obtain ⟨_, _, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk; subst hk; exact hm
  | opaq _ _ =>
    simp only [CKindF.mapM] at hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk; subst hk; exact hm
  | quot _ => simp only [CKindF.mapM, pure, Option.some.injEq] at hk; subst hk; exact hm
  | induct _ _ _ _ _ _ _ _ =>
    simp only [CKindF.mapM] at hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
    obtain ⟨_, _, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk; subst hk; exact hm
  | ctor _ _ _ _ _ =>
    simp only [CKindF.mapM] at hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk; subst hk; exact hm

/-- upstream's read of one recursor's kind (`recBlocksAt`'s `mapM`). -/
@[expose] def rbReadC (r : Region) (l : Nat) : Option (Nat × CKindF ConLeche.Name Unit) :=
  (ConLeche.Frontend.Olean.kindNamesAt r l).map (l, ·)

/-- con-leche: ConLeche/Driver/Reach.lean:588-595 recBlocksAt — the twin's walk of a part's
positions, from any accumulated map: upstream's kinds read, folded onto the related map. -/
theorem recBlocksAt_go {pk : OleanPins} {r : Region} :
    ∀ (qs : List ConRon.Arena.Frontend.Olean.NamePosition)
      {qsC : List ConLeche.Frontend.Olean.NamePosition}
      {m m' : Std.HashMap NIdx (Array Nat)} {mC : Std.HashMap ConLeche.Name (Array Nat)}
      {s s' : AState}, Ctx pk s → HMRel (· = ·) s.store m mC → ListRel (NPRel s.store) qs qsC →
      ConRon.Arena.Modular.recBlocksAt pk r m qs s = .ok (some m', s') →
      ParseStep s s' ∧ ∃ ks, ((qsC.filter (·.tag == 7)).map (·.loc)).mapM (rbReadC r) = some ks ∧
        HMRel (· = ·) s'.store m' (ks.foldl rbStepC mC)
  | [], _, m, m', mC, s, s', hctx, hm, .nil, h => by
    rw [ConRon.Arena.Modular.recBlocksAt] at h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    cases hv
    exact ⟨ParseStep.refl hctx.ok, [], rfl, hm⟩
  | q :: qs, _, m, m', mC, s, s', hctx, hm, .cons hq hqs, h => by
    rename_i qC qsC
    rw [ConRon.Arena.Modular.recBlocksAt] at h
    have htC : (qC.tag == 7) = (q.tag == 7) := by rw [hq.tag]
    by_cases ht : (q.tag == 7) = true
    · rw [ite_eq_left ht] at h
      obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
      rcases o with _ | k
      · obtain ⟨hv, -⟩ := AM.pure_ok h2; cases hv
      dsimp only at h2
      obtain ⟨hst1, kC, hkC, hk⟩ := kindNamesAt_run hctx (hq.loc ▸ h1)
      have hw1 := nsWF_of_StateOK hst1.ok
      have hm1 := recBlocksAdd_rel hw1 (hm.ext hst1.ext (fun _ _ h => h)) q.loc hk
      obtain ⟨hst2, ks, hks, hm2⟩ := recBlocksAt_go qs (hctx.step hst1) hm1
        (ListRel.mono' (fun _ _ h => h.ext hst1.ext) hqs) h2
      refine ⟨hst1.trans hst2, (q.loc, kC) :: ks, ?_, ?_⟩
      · simp only [List.filter_cons, htC, ht, ↓reduceIte, List.map_cons, List.mapM_cons, rbReadC]
        rw [hkC, hks, hq.loc]; rfl
      · simpa [List.foldl_cons] using hm2
    · rw [ite_eq_right ht] at h
      obtain ⟨hst, ks, hks, hm'⟩ := recBlocksAt_go qs hctx hm hqs h
      refine ⟨hst, ks, ?_, hm'⟩
      simp only [Bool.not_eq_true] at ht
      simp only [List.filter_cons, htC, ht, Bool.false_eq_true, ↓reduceIte]
      exact hks

/-- `takePart` keeps the tables. -/
theorem takePart_tables {pk : OleanPins} {F : FS} {sp : Roots} {c c' : ConRon.Arena.Modular.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {r : Region} {st : SM} {s s' : AState}
    (h : ConRon.Arena.Modular.takePart (modelFs F) pk sp c k s = .ok ((c', r, st), s')) :
    c'.tables = c.tables := by
  unfold ConRon.Arena.Modular.takePart at h
  cases hp : c.parts[k]? with
  | some p =>
    obtain ⟨r', st'⟩ := p
    rw [hp] at h
    obtain ⟨hv, -⟩ := AM.pure_ok h
    simp only [Prod.mk.injEq] at hv
    rw [hv.1]
  | none =>
    rw [hp] at h
    obtain ⟨mn, t₁, g1, k1⟩ := AM.bind_ok h
    obtain ⟨fv, t₂, g2, k2⟩ := AM.bind_ok k1
    cases hv : fv.viewRegion k.level with
    | none => rw [hv] at k2; exfalso; am_never k2
    | some ra =>
      rw [hv] at k2
      obtain ⟨hv, -⟩ := AM.pure_ok k2
      simp only [Prod.mk.injEq] at hv
      rw [← hv.1]

theorem recBlocksAt_eq (r : Region) (t : ConLeche.Frontend.Olean.NamePositions) :
    ConLeche.Driver.recBlocksAt r t =
      (((t.consts.toList.filter (·.tag == 7)).map (·.loc)).mapM (rbReadC r)).map
        (fun ks => ks.foldl rbStepC {}) := by
  unfold ConLeche.Driver.recBlocksAt
  rw [Array.toList_filter]
  rfl

/-- con-leche: ConLeche/Driver/Reach.lean:597-608 recBlocksOf — **a part's recursors by block,
read once**: upstream's accept, the twin's cached map related to upstream's. -/
theorem recBlocksOf_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hk : PKRel s.store k kC)
    (h : ConRon.Arena.Modular.recBlocksOf (modelFs F) pk sp env c k s = .ok (c', s')) :
    DStep s s' ∧ ∃ cC' mC m, ModelIO.Gives (ConLeche.Driver.recBlocksOf envC cC kC) F (cC', .ok mC) ∧
      CacheRel s'.store c' cC' ∧ c'.recBlocks[k]? = some m ∧ HMRel (· = ·) s'.store m mC := by
  have hw := hctx.wf
  unfold ConRon.Arena.Modular.recBlocksOf at h
  unfold ConLeche.Driver.recBlocksOf
  have hrb := hc.recBlocks.get hw hk
  by_cases h0 : c.recBlocks.contains k = true
  · rw [ite_eq_left h0] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    rw [Std.HashMap.contains_eq_isSome_getElem?] at h0
    rcases optRel_cases hrb with ⟨g1, -⟩ | ⟨m, mC, g1, g2, g3⟩
    · rw [g1] at h0; cases h0
    rw [g2]
    exact ⟨DStep.refl hctx.ok hctx.off, cC, mC, m, ModelIO.gives_pure _ _, hc, g1, g3⟩
  rw [ite_eq_right h0] at h
  have hnone : cC.recBlocks[kC]? = none := by
    rcases optRel_cases hrb with ⟨-, g2⟩ | ⟨m, mC, g1, -, -⟩
    · exact g2
    · exfalso; apply h0; rw [Std.HashMap.contains_eq_isSome_getElem?, g1]; rfl
  rw [hnone]
  dsimp only
  obtain ⟨u0, s₀, h0', h⟩ := AM.bind_ok h
  obtain ⟨-, hs0⟩ := AM.pure_ok h0'
  subst s₀
  -- the table
  obtain ⟨c₁, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hst1, cC₁, tC, t, hg1, hc1, htg, ht⟩ := tableOf_run hsp hctx he hc hk h1
  have hctx1 := hctx.step hst1
  -- the part
  obtain ⟨tk, s₂, h2, h⟩ := AM.bind_ok h
  obtain ⟨c₂, r, st⟩ := tk
  have htab := takePart_tables h2
  have htg2 : ConRon.Arena.Modular.tableGet env.wr c₂ k = some t := by
    unfold ConRon.Arena.Modular.tableGet at htg ⊢; rw [htab]; exact htg
  dsimp only at h
  rw [htg2] at h
  dsimp only at h
  obtain ⟨res, s₃, h3, h⟩ := AM.bind_ok h
  obtain ⟨cm, s₄, h4, h5⟩ := AM.bind_ok h
  obtain ⟨c₃, m⟩ := cm
  obtain ⟨hv, rfl⟩ := AM.pure_ok h5
  subst hv
  have h' : (do
      let (c, r, st) ← ConRon.Arena.Modular.takePart (modelFs F) pk sp c₁ k
      ConRon.Arena.Modular.putPart c k r (← (fun (r : Region) (st : SM) => (do
        let res ← ConRon.Arena.Modular.recBlocksAt pk r {} t.consts.toList
        pure (st, res) : AM (SM × Option (Std.HashMap NIdx (Array Nat))))) r st)) s₁ = .ok ((c₃, m), s') :=
    AM.bind_of h2 (AM.bind_of (AM.bind_of h3 rfl) h4)
  obtain ⟨hst2, cC₂, mC, hg2, hc2, hmr⟩ := partRead_run
    (R := fun st (a : Std.HashMap NIdx (Array Nat)) (b : Std.HashMap ConLeche.Name (Array Nat)) =>
      HMRel (· = ·) st a b)
    (f := fun r st => (ConLeche.Driver.recBlocksAt r tC).map (st, ·))
    (g := fun (r : Region) (st : SM) => (do
        let res ← ConRon.Arena.Modular.recBlocksAt pk r {} t.consts.toList
        pure (st, res) : AM (SM × Option (Std.HashMap NIdx (Array Nat)))))
    (fun r m₀ m₁ a s₀ s₀' hx₀ hctx₀ hgood hrun => by
      obtain ⟨res', s₀₁, k1, k2⟩ := AM.bind_ok hrun
      obtain ⟨hv, rfl⟩ := AM.pure_ok k2
      injection hv with e1 e2
      subst e1 e2
      obtain ⟨hst, ks, hks, hm⟩ := recBlocksAt_go (r := r) t.consts.toList hctx₀
        (HMRel.empty _ _) (ListRel.mono' (fun _ _ q => q.ext hx₀) ht.consts) k1
      refine ⟨hst, hgood.ext hst.ext, fun mC hG => ⟨mC, _, ?_, hG, hm⟩⟩
      rw [recBlocksAt_eq, hks]; rfl)
    hsp hctx1 (he.ext hst1.ext hctx1.wf) hc1 (hk.ext hst1.ext) (Ext.refl _) h'
  have hw' := nsWF_of_StateOK hst2.ok.state
  have hk' := (hk.ext hst1.ext).ext hst2.ext
  refine ⟨hst1.trans hst2, { cC₂ with recBlocks := cC₂.recBlocks.insert kC mC }, mC, m,
    hg1.bind (hg2.bind (ModelIO.gives_pure _ _)),
    ⟨hc2.tables, hc2.looks, hc2.parts, hc2.recBlocks.insert hw' hk' hmr, hc2.views, hc2.located,
      hc2.completed, hc2.pending, hc2.partners, hc2.searches⟩, ?_, hmr⟩
  simp

/-! ## A group read from one part -/

/-- `takePart` keeps the lookups and the recursor blocks. -/
theorem takePart_keeps {pk : OleanPins} {F : FS} {sp : Roots} {c c' : ConRon.Arena.Modular.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {r : Region} {st : SM} {s s' : AState}
    (h : ConRon.Arena.Modular.takePart (modelFs F) pk sp c k s = .ok ((c', r, st), s')) :
    c'.looks = c.looks ∧ c'.recBlocks = c.recBlocks := by
  unfold ConRon.Arena.Modular.takePart at h
  cases hp : c.parts[k]? with
  | some p =>
    obtain ⟨r', st'⟩ := p
    rw [hp] at h
    obtain ⟨hv, -⟩ := AM.pure_ok h
    simp only [Prod.mk.injEq] at hv
    rw [hv.1]
    exact ⟨rfl, rfl⟩
  | none =>
    rw [hp] at h
    obtain ⟨mn, t₁, g1, k1⟩ := AM.bind_ok h
    obtain ⟨fv, t₂, g2, k2⟩ := AM.bind_ok k1
    cases hv : fv.viewRegion k.level with
    | none => rw [hv] at k2; exfalso; am_never k2
    | some ra =>
      rw [hv] at k2
      obtain ⟨hv, -⟩ := AM.pure_ok k2
      simp only [Prod.mk.injEq] at hv
      rw [← hv.1]
      exact ⟨rfl, rfl⟩

/-- `putPart` keeps the lookups and the recursor blocks. -/
theorem putPart_keeps {α : Type} {c c' : ConRon.Arena.Modular.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {r : Region} {res : SM × Option α} {a : α} {s s' : AState}
    (h : ConRon.Arena.Modular.putPart c k r res s = .ok ((c', a), s')) :
    c'.looks = c.looks ∧ c'.recBlocks = c.recBlocks := by
  unfold ConRon.Arena.Modular.putPart at h
  obtain ⟨st, o⟩ := res
  cases o with
  | some a' =>
    obtain ⟨hv, -⟩ := AM.pure_ok h
    simp only [Prod.mk.injEq] at hv
    rw [hv.1]
    exact ⟨rfl, rfl⟩
  | none => exfalso; am_never h

theorem partEntry_keeps {pk : OleanPins} {F : FS} {sp : Roots} {c c' : ConRon.Arena.Modular.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {l : Nat} {e : CEntryF NIdx EIdx} {s s' : AState}
    (h : ConRon.Arena.Modular.partEntry (modelFs F) pk sp c k l s = .ok ((c', e), s')) :
    c'.looks = c.looks ∧ c'.recBlocks = c.recBlocks := by
  unfold ConRon.Arena.Modular.partEntry at h
  obtain ⟨⟨c₁, r, st⟩, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨res, s₂, h2, h3⟩ := AM.bind_ok h
  obtain ⟨e1, e2⟩ := takePart_keeps h1
  obtain ⟨e3, e4⟩ := putPart_keeps h3
  exact ⟨e3.trans e1, e4.trans e2⟩

theorem partEntries_keeps {pk : OleanPins} {F : FS} {sp : Roots} {c c' : ConRon.Arena.Modular.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {ls : List Nat} {es : List (CEntryF NIdx EIdx)} {s s' : AState}
    (h : ConRon.Arena.Modular.partEntries (modelFs F) pk sp c k ls s = .ok ((c', es), s')) :
    c'.looks = c.looks ∧ c'.recBlocks = c.recBlocks := by
  unfold ConRon.Arena.Modular.partEntries at h
  obtain ⟨⟨c₁, r, st⟩, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨res, s₂, h2, h3⟩ := AM.bind_ok h
  obtain ⟨e1, e2⟩ := takePart_keeps h1
  obtain ⟨e3, e4⟩ := putPart_keeps h3
  exact ⟨e3.trans e1, e4.trans e2⟩

/-- A constant read back: its kind's names and expressions, read back. -/
theorem denoteEntry_kind {st : EStore} {c : CEntryF NIdx EIdx} {cC : CEntryF ConLeche.Name Expr}
    (h : denoteEntry st c = some cC) :
    c.kind.mapM (denoteN st.ns) (denoteE st) = some cC.kind := by
  simp only [denoteEntry, ConLeche.Frontend.Olean.CEntryF.mapM] at h
  obtain ⟨a, _, h⟩ := bind_some_left h
  obtain ⟨b, _, h⟩ := bind_some_left h
  obtain ⟨t, _, h⟩ := bind_some_left h
  obtain ⟨k, hk, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq] at h
  subst h
  exact hk

/-- An inductive type's kind read back: its members and constructors. -/
theorem kind_induct_rel {st : EStore} {k : CKindF NIdx EIdx} {kC : CKindF ConLeche.Name Expr}
    (h : k.mapM (denoteN st.ns) (denoteE st) = some kC) {np ni nn : Nat} {all cs : List NIdx}
    {ir iu irf : Bool} (hk : k = .induct np ni all cs nn ir iu irf) :
    ∃ allC csC, kC = .induct np ni allC csC nn ir iu irf ∧ all.mapM (denoteN st.ns) = some allC ∧
      cs.mapM (denoteN st.ns) = some csC := by
  subst hk
  simp only [ConLeche.Frontend.Olean.CKindF.mapM] at h
  obtain ⟨allC, ha, h⟩ := bind_some_left h
  obtain ⟨csC, hc, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq] at h
  exact ⟨allC, csC, h.symm, ha, hc⟩

/-- The locations of some names in a lookup, upstream's. -/
theorem lookLocs_rel {st : EStore} (hw : NStoreWF st.ns)
    {l : Std.HashMap NIdx ConRon.Arena.Frontend.Olean.NamePosition}
    {lC : Std.HashMap ConLeche.Name ConLeche.Frontend.Olean.NamePosition}
    (hl : HMRel (NPRel st) st l lC) :
    ∀ {ns : List NIdx} {nsC : List ConLeche.Name}, ListRel (NR st) ns nsC →
      (ns.mapM fun n => (l[n]?).map (·.loc)) = (nsC.mapM (lC[·]?)).map (·.map (·.loc))
  | [], [], .nil => rfl
  | n :: ns, nC :: nsC, .cons hn hr => by
    have ih := lookLocs_rel hw hl hr
    rcases optRel_cases (hl.get hw hn) with ⟨g1, g2⟩ | ⟨q, qC, g1, g2, g3⟩
    · simp [g1, g2]
    · simp only [List.mapM_cons, g1, g2, ih, Option.map_some, Option.bind_eq_bind]
      cases nsC.mapM (lC[·]?) <;> simp [g3.loc]

/-- The constructors a group's types list, read back. -/
theorem groupCtorNames_rel {st : EStore} :
    ∀ {tys : List (CEntryF NIdx EIdx)} {tysC : List (CEntryF ConLeche.Name Expr)},
      tys.mapM (denoteEntry st) = some tysC →
      (ConRon.Arena.Modular.groupCtorNames tys).mapM (denoteN st.ns) =
        some (ConLeche.Driver.groupCtorNames tysC)
  | [], tysC, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | t :: tys, tysC, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨tC, ht, h⟩ := bind_some_left h
    obtain ⟨tysC', hts, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    have ih := groupCtorNames_rel hts
    have hk := denoteEntry_kind ht
    simp only [ConRon.Arena.Modular.groupCtorNames, ConLeche.Driver.groupCtorNames,
      List.flatMap_cons] at ih ⊢
    rw [List.mapM_append, ih]
    generalize tC.kind = kC at hk
    cases hkk : t.kind with
    | induct np ni all cs nn ir iu irf =>
      obtain ⟨allC, csC, rfl, -, hc⟩ := kind_induct_rel hk hkk
      simp [hc]
    | ax u => rw [hkk] at hk; simp [ConLeche.Frontend.Olean.CKindF.mapM, pure] at hk; subst hk; simp
    | defn v hh sf =>
      rw [hkk] at hk; simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
      obtain ⟨_, _, hk⟩ := bind_some_left hk; simp only [pure, Option.some.injEq] at hk; subst hk; simp
    | thm v al =>
      rw [hkk] at hk; simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
      obtain ⟨_, _, hk⟩ := bind_some_left hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
      simp only [pure, Option.some.injEq] at hk; subst hk; simp
    | opaq v u =>
      rw [hkk] at hk; simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
      obtain ⟨_, _, hk⟩ := bind_some_left hk; simp only [pure, Option.some.injEq] at hk; subst hk; simp
    | quot q => rw [hkk] at hk; simp [ConLeche.Frontend.Olean.CKindF.mapM, pure] at hk; subst hk; simp
    | ctor ind ci np nf iu =>
      rw [hkk] at hk; simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
      obtain ⟨_, _, hk⟩ := bind_some_left hk; simp only [pure, Option.some.injEq] at hk; subst hk; simp
    | recur al np ni nmo nmi rules k iu =>
      rw [hkk] at hk; simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
      obtain ⟨_, _, hk⟩ := bind_some_left hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
      simp only [pure, Option.some.injEq] at hk; subst hk; simp

/-- A filter of related lists by related tests. -/
theorem filter_mapM_rel {st : EStore} {p : CEntryF NIdx EIdx → Bool}
    {pC : CEntryF ConLeche.Name Expr → Bool}
    (hp : ∀ e eC, denoteEntry st e = some eC → p e = pC eC) :
    ∀ {rest : List (CEntryF NIdx EIdx)} {restC : List (CEntryF ConLeche.Name Expr)},
      rest.mapM (denoteEntry st) = some restC →
      (rest.filter p).mapM (denoteEntry st) = some (restC.filter pC)
  | [], restC, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | e :: rest, restC, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨eC, he, h⟩ := bind_some_left h
    obtain ⟨restC', hr, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    have ih := filter_mapM_rel hp hr
    have hpe := hp e eC he
    cases hb : p e with
    | true =>
      rw [hb] at hpe
      simp only [List.filter_cons, hb, ← hpe, ↓reduceIte, List.mapM_cons, he, ih]
      rfl
    | false =>
      rw [hb] at hpe
      simp only [List.filter_cons, hb, ← hpe, Bool.false_eq_true, ↓reduceIte, ih]

/-- con-leche: ConLeche/Driver/Reach.lean:620-627 groupMerged — the test keeping a constant among
a group's rest. -/
@[expose] def recKeepC (allC : List ConLeche.Name) (e : CEntryF ConLeche.Name Expr) : Bool :=
  match e.kind with
  | .recur all' .. => all' == allC
  | _ => true

/-- A constant kept among a group's rest, alike. -/
theorem groupKeeps_rel {st : EStore} (hw : NStoreWF st.ns) {all : List NIdx}
    {allC : List ConLeche.Name} (ha : all.mapM (denoteN st.ns) = some allC)
    {e : CEntryF NIdx EIdx} {eC : CEntryF ConLeche.Name Expr} (he : denoteEntry st e = some eC) :
    ConRon.Arena.Modular.groupKeeps e all = recKeepC allC eC := by
  have hk := denoteEntry_kind he
  unfold ConRon.Arena.Modular.groupKeeps recKeepC
  generalize eC.kind = kC at hk
  cases hkk : e.kind with
  | recur al np ni nmo nmi rules k iu =>
    rw [hkk] at hk; simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
    obtain ⟨alC, hal, hk⟩ := bind_some_left hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk; subst hk
    exact nameList_beq hw hal ha
  | _ =>
    rw [hkk] at hk
    simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
    first
    | (simp only [pure] at hk; injection hk with hk; subst hk; rfl)
    | (obtain ⟨_, _, hk⟩ := bind_some_left hk
       first
       | (simp only [pure] at hk; injection hk with hk; subst hk; rfl)
       | (obtain ⟨_, _, hk⟩ := bind_some_left hk
          simp only [pure, Option.some.injEq] at hk; subst hk; rfl))

/-- A group's recursors' locations, upstream's. -/
theorem groupRecLocs_eq {st : EStore} (hw : NStoreWF st.ns) {m : Std.HashMap NIdx (Array Nat)}
    {mC : Std.HashMap ConLeche.Name (Array Nat)} (hm : HMRel (· = ·) st m mC) {all : List NIdx}
    {allC : List ConLeche.Name} (ha : all.mapM (denoteN st.ns) = some allC) :
    ConRon.Arena.Modular.groupRecLocs m all = ConLeche.Driver.groupRecLocs mC allC := by
  unfold ConRon.Arena.Modular.groupRecLocs ConLeche.Driver.groupRecLocs
  cases all with
  | nil => simp only [List.mapM_nil, pure, Option.some.injEq] at ha; subst ha; rfl
  | cons a as =>
    simp only [List.mapM_cons] at ha
    obtain ⟨aC, haC, ha⟩ := bind_some_left ha
    obtain ⟨_, _, ha⟩ := bind_some_left ha
    simp only [pure, Option.some.injEq] at ha
    subst ha
    simp [HMRel.get_eq hw hm haC]

/-- A list of constants read back, as the merge's entries. -/
theorem entries_cr {st : EStore} :
    ∀ {es : List (CEntryF NIdx EIdx)} {esC : List (CEntryF ConLeche.Name Expr)},
      es.mapM (denoteEntry st) = some esC →
      ListRel (fun c cC => denoteCEntry st c = some cC) (es.map fun c => { c })
        (esC.map ConLeche.Frontend.Olean.CEntry.ofF)
  | [], esC, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact .nil
  | e :: es, esC, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨eC, he, h⟩ := bind_some_left h
    obtain ⟨esC', hr, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    refine .cons ?_ (entries_cr hr)
    simp only [denoteCEntry, he]
    rfl

/-- con-leche: ConLeche/Driver/Reach.lean:620-627 groupMerged — **a group's merge, upstream's**. -/
theorem groupMerged_rel {st : EStore} (hw : NStoreWF st.ns) (pk : OleanPins)
    {t : CEntryF NIdx EIdx} {tC : CEntryF ConLeche.Name Expr} (ht : denoteEntry st t = some tC)
    {tys rest : List (CEntryF NIdx EIdx)} {tysC restC : List (CEntryF ConLeche.Name Expr)}
    (hty : tys.mapM (denoteEntry st) = some tysC) (hr : rest.mapM (denoteEntry st) = some restC)
    {all : List NIdx} {allC : List ConLeche.Name} (ha : all.mapM (denoteN st.ns) = some allC) :
    WalkCtx st (ConRon.Arena.Modular.groupMerged pk t tys rest all)
      (ConLeche.Driver.groupMerged tC tysC restC allC) := by
  have heq : ConLeche.Driver.groupMerged tC tysC restC allC =
      ConLeche.Frontend.Olean.mergedOfList
        ((tC :: tysC ++ restC.filter (recKeepC allC)).map ConLeche.Frontend.Olean.CEntry.ofF) := rfl
  rw [heq]
  unfold ConRon.Arena.Modular.groupMerged
  have hf := filter_mapM_rel (fun e eC he => groupKeeps_rel hw ha he) hr
  have hall : (t :: tys ++ rest.filter (ConRon.Arena.Modular.groupKeeps · all)).mapM (denoteEntry st) =
      some (tC :: tysC ++ restC.filter (recKeepC allC)) := by
    simp only [List.cons_append, List.mapM_cons, ht, List.mapM_append, hty, hf]
    rfl
  exact mergedOfList_rel hw pk (by simpa using entries_cr hall)

/-- con-leche: ConLeche/Driver/Reach.lean:629-667 groupAt — **type `n`'s group read from one
part, upstream's**: the caches related after, the record (where the part holds the group) read
back, persistent. -/
theorem groupAt_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey} {n : NIdx} {nC : ConLeche.Name}
    {od : Option IDeclaration} {s s' : AState}
    (hctx : RCtx pk s) (hpk : PinsRel s.store pk) (he : EnvRel sp s.store env envC)
    (hc : CacheRel s.store c cC) (hk : PKRel s.store k kC) (hn : denoteN s.store.ns n = some nC)
    (h : ConRon.Arena.Modular.groupAt (modelFs F) pk sp env c k n s = .ok ((c', od), s')) :
    DStep s s' ∧ ∃ cC' odC, ModelIO.Gives (ConLeche.Driver.groupAt envC cC kC nC) F (cC', .ok odC) ∧
      CacheRel s'.store c' cC' ∧
      Option.Rel (fun d dC => Frontend.denoteDecl s'.store d = some dC ∧ PersDecl d) od odC := by
  unfold ConRon.Arena.Modular.groupAt at h
  unfold ConLeche.Driver.groupAt
  -- the part
  obtain ⟨c₁, s₁, h1, hA⟩ := AM.bind_ok h
  obtain ⟨hst1, cC₁, hg1, hc1⟩ := loadPart_run hsp hctx he hc hk h1
  have hctx1 := hctx.step hst1
  have he1 := he.ext hst1.ext hctx1.wf
  -- its lookup
  obtain ⟨c₂, s₂, h2, hB⟩ := AM.bind_ok hA
  obtain ⟨hst2, cC₂, lC, l, hg2, hc2, hl2, hlr⟩ := lookOf_run hsp hctx1 he1 hc1 (hk.ext hst1.ext) h2
  have hctx2 := hctx1.step hst2
  have hw2 := hctx2.wf
  have hx12 := hst1.ext.trans hst2.ext
  obtain ⟨oq, s₃, h3, hC⟩ := AM.bind_ok hB
  rw [lookAt_eq hl2] at h3
  obtain ⟨hoq, hs3⟩ := AM.pure_ok h3
  subst hoq; subst s₃
  have hq := hlr.get hw2 (denoteN_ext hn hx12)
  rcases optRel_cases hq with ⟨g1, g2⟩ | ⟨q, qC, g1, g2, g3⟩
  · -- not in the part
    rw [g1] at hC
    obtain ⟨hv, rfl⟩ := AM.pure_ok hC
    cases hv
    refine ⟨hst1.trans hst2, cC₂, none, ?_, hc2, .none⟩
    refine hg1.bind (hg2.bind ?_)
    simp only [g2]
    exact ModelIO.gives_pure _ _
  rw [g1] at hC
  dsimp only at hC
  -- the type's constant
  have he2 := he1.ext hst2.ext hw2
  have hk2 := (hk.ext hst1.ext).ext hst2.ext
  obtain ⟨ct, s₄, h4, hD⟩ := AM.bind_ok hC
  obtain ⟨c₃, t⟩ := ct
  obtain ⟨hst4, cC₃, tC, hg4, hc4, htC⟩ := partEntry_run hsp hctx2 he2 hc2 hk2 h4
  have hkeep4 := partEntry_keeps h4
  have hctx4 := hctx2.step hst4
  have hw4 := hctx4.wf
  have hk4 := hk2.ext hst4.ext
  have he4 := he2.ext hst4.ext hw4
  dsimp only at hD
  have hlr4 : HMRel (NPRel s₄.store) s₄.store l lC := hlr.ext hst4.ext (fun _ _ q => q.ext hst4.ext)
  have hl4 : c₃.looks[k]? = some l := by rw [hkeep4.1]; exact hl2
  have hx14 := hx12.trans hst4.ext
  cases hkt : t.kind with
  | induct np ni all cs nn ir iu irf =>
    rw [hkt] at hD
    obtain ⟨allC, csC, hkC, hall, -⟩ := kind_induct_rel (denoteEntry_kind htC) hkt
    obtain ⟨y, s₅, h5, hE⟩ := AM.bind_ok hD
    obtain ⟨hy, hs5⟩ := AM.pure_ok h5
    subst hy; subst s₅
    obtain ⟨om, s₆, h6, hF⟩ := AM.bind_ok hE
    simp only [ConRon.Arena.Modular.lookLocs, hl4] at h6
    obtain ⟨hom, hs6⟩ := AM.pure_ok h6
    subst hom; subst s₆
    have hlocs := lookLocs_rel hw4 hlr4 (listRel_of_mapM hall)
    rw [hlocs] at hF
    -- the upstream run up to the type's members
    have hupA : ∀ v, ModelIO.Gives (match allC.mapM (lC[·]?) with
          | none => pure (cC₃, .ok none)
          | some mqs => (do
            match ← ConLeche.Driver.withPart envC cC₃ kC fun r st =>
                ConLeche.Driver.entriesWith r st (mqs.map (·.loc)) with
            | (c, .error e) => pure (c, .error e)
            | (c, .ok tys) =>
              match (ConLeche.Driver.groupCtorNames tys).mapM (lC[·]?) with
              | none => pure (c, .ok none)
              | some cqs =>
                match ← ConLeche.Driver.recBlocksOf envC c kC with
                | (c, .error e) => pure (c, .error e)
                | (c, .ok rb) =>
                  match ← ConLeche.Driver.withPart envC c kC fun r st =>
                      ConLeche.Driver.entriesWith r st (cqs.map (·.loc) ++
                        ConLeche.Driver.groupRecLocs rb allC) with
                  | (c, .error e) => pure (c, .error e)
                  | (c, .ok rest) =>
                    match ConLeche.Frontend.Olean.groupRecord
                        (ConLeche.Driver.groupMerged tC tys rest allC) nC with
                    | .ok d => pure (c, .ok (some d))
                    | .error e => pure (c, .error e) : ModelIO _)) F v →
        ModelIO.Gives (ConLeche.Driver.groupAt envC cC kC nC) F v := by
      intro v hv
      unfold ConLeche.Driver.groupAt
      refine hg1.bind (hg2.bind ?_)
      simp only [g2]
      rw [← g3.loc]
      refine hg4.bind ?_
      simp only [hkC]
      exact hv
    have hst14 : DStep s s₄ := hst1.trans (hst2.trans hst4)
    cases hmq : allC.mapM (lC[·]?) with
    | none =>
      rw [hmq] at hF
      obtain ⟨hv, rfl⟩ := AM.pure_ok hF
      cases hv
      refine ⟨hst14, cC₃, none, hupA _ ?_, hc4, .none⟩
      simp only [hmq]
      exact ModelIO.gives_pure _ _
    | some mqsC =>
    rw [hmq] at hF
    try dsimp only at hF
    -- the members
    obtain ⟨ce, s₇, h7, hG⟩ := AM.bind_ok hF
    obtain ⟨c₄, tys⟩ := ce
    obtain ⟨hst7, cC₄, tysC, hg7, hc7, htys⟩ := partEntries_run hsp hctx4 he4 hc4 hk4 h7
    have hkeep7 := partEntries_keeps h7
    have hctx7 := hctx4.step hst7
    have hw7 := hctx7.wf
    have hk7 := hk4.ext hst7.ext
    have he7 := he4.ext hst7.ext hw7
    have hlr7 : HMRel (NPRel s₇.store) s₇.store l lC := hlr4.ext hst7.ext (fun _ _ q => q.ext hst7.ext)
    have hl7 : c₄.looks[k]? = some l := by rw [hkeep7.1]; exact hl4
    try dsimp only at hG
    obtain ⟨oc, s₈, h8, hH⟩ := AM.bind_ok hG
    simp only [ConRon.Arena.Modular.lookLocs, hl7] at h8
    obtain ⟨hoc, hs8⟩ := AM.pure_ok h8
    subst hoc; subst s₈
    rw [lookLocs_rel hw7 hlr7 (listRel_of_mapM (groupCtorNames_rel htys))] at hH
    have hupB : ∀ v, ModelIO.Gives (match (ConLeche.Driver.groupCtorNames tysC).mapM (lC[·]?) with
          | none => pure (cC₄, .ok none)
          | some cqs => (do
                match ← ConLeche.Driver.recBlocksOf envC cC₄ kC with
                | (c, .error e) => pure (c, .error e)
                | (c, .ok rb) =>
                  match ← ConLeche.Driver.withPart envC c kC fun r st =>
                      ConLeche.Driver.entriesWith r st (cqs.map (·.loc) ++
                        ConLeche.Driver.groupRecLocs rb allC) with
                  | (c, .error e) => pure (c, .error e)
                  | (c, .ok rest) =>
                    match ConLeche.Frontend.Olean.groupRecord
                        (ConLeche.Driver.groupMerged tC tysC rest allC) nC with
                    | .ok d => pure (c, .ok (some d))
                    | .error e => pure (c, .error e) : ModelIO _)) F v →
        ModelIO.Gives (ConLeche.Driver.groupAt envC cC kC nC) F v := by
      intro v hv
      refine hupA _ ?_
      simp only [hmq]
      rw [← (show (mqsC.map (·.loc)) = _ from rfl)]
      refine hg7.bind ?_
      exact hv
    have hst17 : DStep s s₇ := hst14.trans hst7
    cases hcq : (ConLeche.Driver.groupCtorNames tysC).mapM (lC[·]?) with
    | none =>
      rw [hcq] at hH
      obtain ⟨hv, rfl⟩ := AM.pure_ok hH
      cases hv
      refine ⟨hst17, cC₄, none, hupB _ ?_, hc7, .none⟩
      simp only [hcq]
      exact ModelIO.gives_pure _ _
    | some cqsC =>
    rw [hcq] at hH
    try dsimp only at hH
    -- the recursors' blocks
    obtain ⟨c₅, s₉, h9, hI⟩ := AM.bind_ok hH
    obtain ⟨hst9, cC₅, mC, m, hg9, hc9, hrb9, hmr⟩ := recBlocksOf_run hsp hctx7 he7 hc7 hk7 h9
    have hctx9 := hctx7.step hst9
    have hw9 := hctx9.wf
    have hk9 := hk7.ext hst9.ext
    have he9 := he7.ext hst9.ext hw9
    obtain ⟨rl, s₁₀, h10, hJ⟩ := AM.bind_ok hI
    simp only [ConRon.Arena.Modular.recLocsAt, hrb9] at h10
    obtain ⟨hrl, hs10⟩ := AM.pure_ok h10
    subst hrl; subst s₁₀
    have hall9 : y.mapM (denoteN s₉.store.ns) = some allC :=
      mapM_denoteN_ext (hst7.ext.trans hst9.ext) hall
    rw [groupRecLocs_eq hw9 hmr hall9] at hJ
    -- the rest
    obtain ⟨cr, s₁₁, h11, hK⟩ := AM.bind_ok hJ
    obtain ⟨c₆, rest⟩ := cr
    obtain ⟨hst11, cC₆, restC, hg11, hc11, hrest⟩ := partEntries_run hsp hctx9 he9 hc9 hk9 h11
    have hctx11 := hctx9.step hst11
    have hw11 := hctx11.wf
    try dsimp only at hK
    obtain ⟨d, s₁₂, h12, hL⟩ := AM.bind_ok hK
    obtain ⟨hv, hs⟩ := AM.pure_ok hL
    cases hv
    subst hs
    have hx9_11 := hst11.ext
    have hx4_11 := ((hst7.ext.trans hst9.ext).trans hst11.ext)
    obtain ⟨hst12, hpd, dC, hgd, hdd⟩ := groupRecord_run hctx11.ok.state hctx11.off hctx11.ok.pins
      (groupMerged_rel hw11 pk (denoteEntry_ext hx4_11 htC)
        (list_mono (fun x y hxy => denoteEntry_ext (hst9.ext.trans hst11.ext) hxy) tys htys) hrest
        (mapM_denoteN_ext hst11.ext hall9))
      (hpk.ext (((hst1.ext.trans hst2.ext).trans hst4.ext).trans hx4_11))
      (denoteN_ext hn (((hst1.ext.trans hst2.ext).trans hst4.ext).trans hx4_11)) h12
    refine ⟨hst17.trans (hst9.trans (hst11.trans (DStep.of_parse hctx11.ok hctx11.off hst12))),
      cC₆, some dC, hupB _ ?_, hc11.ext hst12.ext, .some ⟨hdd, hpd⟩⟩
    simp only [hcq]
    refine hg9.bind ?_
    simp only
    refine hg11.bind ?_
    dsimp only
    rw [hgd]
    exact ModelIO.gives_pure _ _
  | _ =>
    exfalso
    rw [hkt] at hD
    obtain ⟨_, _, _, g1'⟩ := AM.bind_ok hD
    obtain ⟨_, _, _, g2'⟩ := AM.bind_ok g1'
    obtain ⟨_, _, g3', _⟩ := AM.bind_ok g2'
    exact AM.fail_ok g3'

/-! ## A copy as its statement, and the record presenting a name -/

/-- A statement's parts read back. -/
theorem denoteStmt_rr {st : EStore} {cv : ConRon.Arena.Frontend.Olean.StmtRec} {cvC : ConstantVal}
    (h : denoteStmt st cv = some cvC) :
    denoteN st.ns cv.name = some cvC.name ∧ cv.levelParams.mapM (denoteN st.ns) = some cvC.levelParams ∧
      denoteE st cv.type = some cvC.type := by
  simp only [denoteStmt] at h
  obtain ⟨a, ha, h⟩ := bind_some_left h
  obtain ⟨b, hb, h⟩ := bind_some_left h
  obtain ⟨c, hc, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq] at h
  subst h
  exact ⟨ha, hb, hc⟩

/-- A statement as an axiom's record, read back. -/
theorem axiomOf_den {st : EStore} {cv : ConRon.Arena.Frontend.Olean.StmtRec} {cvC : ConstantVal}
    (h : denoteStmt st cv = some cvC) :
    Frontend.denoteDecl st (ConRon.Arena.Modular.axiomOf cv) = some (.axiomDecl cvC) := by
  obtain ⟨h1, h2, h3⟩ := denoteStmt_rr h
  simp only [ConRon.Arena.Modular.axiomOf, Frontend.denoteDecl, Frontend.denoteCV, h1,
    denoteNList_eq_mapM, h2, h3, Option.map_some]

/-- con-leche: ConLeche/Driver/Reach.lean:678-691 stmtRecord — **a copy presented as its
statement, upstream's**. -/
theorem stmtRecord_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {sp₀ : ConRon.Arena.Modular.Spot} {spC : ConLeche.Driver.Spot}
    {cv : ConRon.Arena.Frontend.Olean.StmtRec} {cvC : ConstantVal}
    {d : IDeclaration} {hh : NIdx} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hs : SpotRel s.store sp₀ spC) (hcv : denoteStmt s.store cv = some cvC)
    (h : ConRon.Arena.Modular.stmtRecord (modelFs F) pk sp env c sp₀ cv s = .ok ((c', d, hh), s')) :
    DStep s s' ∧ PersDecl d ∧ ∃ cC' dC hC,
      ModelIO.Gives (ConLeche.Driver.stmtRecord envC cC spC cvC) F (cC', .ok (dC, hC)) ∧
      CacheRel s'.store c' cC' ∧ Frontend.denoteDecl s'.store d = some dC ∧
      denoteN s'.store.ns hh = some hC := by
  unfold ConRon.Arena.Modular.stmtRecord at h
  unfold ConLeche.Driver.stmtRecord
  obtain ⟨ns, s₁, h1, hA⟩ := AM.bind_ok h
  obtain ⟨hs1, hns⟩ := reduceOpNames_run hctx.ok.pins h1
  subst s₁
  have hcont : ns.contains cv.name = ConLeche.reduceOpNames.contains cvC.name :=
    denoteNList_contains hctx.ok.state.wf ns ConLeche.reduceOpNames
      (denoteNL_toList ns ConLeche.reduceOpNames hns) cv.name cvC.name (denoteStmt_rr hcv).1
  have hax := axiomOf_den hcv
  have hpax := PersDecl_of_denote hctx.ok.state.wf hctx.off hax
  by_cases hop : ns.contains cv.name = true
  · rw [ite_eq_right (by simpa using hop)] at hA
    obtain ⟨u, s₂, h2, hB⟩ := AM.bind_ok hA
    obtain ⟨-, hs2⟩ := AM.pure_ok h2
    subst s₂
    obtain ⟨cp, s₃, h3, hC⟩ := AM.bind_ok hB
    obtain ⟨c₁, p⟩ := cp
    obtain ⟨hst3, cC₁, pC, hg3, hc3, hp3⟩ := privSpot_run hsp hctx he hc hs h3
    have hopC : ConLeche.reduceOpNames.contains cvC.name = true := hcont ▸ hop
    dsimp only at hC
    by_cases htag : (p.pos.tag == 0 || p.pos.tag == 3) = true
    · rw [ite_eq_left htag] at hC
      obtain ⟨hv, rfl⟩ := AM.pure_ok hC
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      refine ⟨hst3, hpax, cC₁, .axiomDecl cvC, spC.part.mod, ?_, hc3,
        Frontend.denoteDecl_ext hst3.ext hax, denoteN_ext hs.1.1 hst3.ext⟩
      rw [ite_eq_right (by simpa using hopC)]
      refine hg3.bind ?_
      dsimp only
      rw [ite_eq_left (by rw [← hp3.2.tag]; exact htag)]
      exact ModelIO.gives_pure _ _
    · rw [ite_eq_right htag] at hC
      exfalso; am_never hC
  · rw [ite_eq_left (by simpa using hop)] at hA
    obtain ⟨hv, rfl⟩ := AM.pure_ok hA
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    have hopC : ConLeche.reduceOpNames.contains cvC.name = false := by
      rw [← hcont]; simpa using hop
    refine ⟨DStep.refl hctx.ok hctx.off, hpax, cC, .axiomDecl cvC, spC.part.mod, ?_, hc, hax,
      hs.1.1⟩
    rw [ite_eq_left (by simpa using hopC)]
    exact ModelIO.gives_pure _ _

/-- The type whose group presents a copy, upstream's. -/
theorem groupOfKind_rel {st : EStore} {x : NIdx} {xC : ConLeche.Name} (hx : denoteN st.ns x = some xC)
    {k : CKindF NIdx Unit} {kC : CKindF ConLeche.Name Unit} (hk : denoteKindN st k = some kC) :
    Option.Rel (fun a b => denoteN st.ns a = some b)
      (ConRon.Arena.Modular.groupOfKind x k) (ConLeche.Driver.groupOfKind xC kC) := by
  unfold denoteKindN at hk
  cases k with
  | induct np ni all cs nn ir iu irf =>
    simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
    obtain ⟨_, _, hk⟩ := bind_some_left hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk; subst hk
    exact .some hx
  | ctor ind ci np nf iu =>
    simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
    obtain ⟨indC, hi, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk; subst hk
    exact .some hi
  | recur all np ni nmo nmi rules kk iu =>
    simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
    obtain ⟨allC, ha, hk⟩ := bind_some_left hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk; subst hk
    simp only [ConRon.Arena.Modular.groupOfKind, ConLeche.Driver.groupOfKind]
    refine .some ?_
    cases all with
    | nil => simp only [List.mapM_nil, pure, Option.some.injEq] at ha; subst ha; exact hx
    | cons a as =>
      simp only [List.mapM_cons] at ha
      obtain ⟨aC, haC, ha⟩ := bind_some_left ha; obtain ⟨_, _, ha⟩ := bind_some_left ha
      simp only [pure, Option.some.injEq] at ha; subst ha
      exact haC
  | ax u =>
    simp only [ConLeche.Frontend.Olean.CKindF.mapM, pure, Option.some.injEq] at hk; subst hk; exact .none
  | defn v hh sf =>
    simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
    obtain ⟨_, _, hk⟩ := bind_some_left hk; simp only [pure, Option.some.injEq] at hk; subst hk
    exact .none
  | thm v al =>
    simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
    obtain ⟨_, _, hk⟩ := bind_some_left hk; obtain ⟨_, _, hk⟩ := bind_some_left hk
    simp only [pure, Option.some.injEq] at hk; subst hk; exact .none
  | opaq v u =>
    simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
    obtain ⟨_, _, hk⟩ := bind_some_left hk; simp only [pure, Option.some.injEq] at hk; subst hk
    exact .none
  | quot q =>
    simp only [ConLeche.Frontend.Olean.CKindF.mapM, pure, Option.some.injEq] at hk; subst hk; exact .none

/-- con-leche: ConLeche/Driver/Reach.lean:693-729 readRecord — **the record presenting `x`, and its
home, upstream's**: the caches related after, the record read back and persistent, its home
denoted. -/
theorem readRecord_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {x : NIdx} {xC : ConLeche.Name} {s s' : AState} {d : IDeclaration} {h : NIdx}
    (hctx : RCtx pk s) (hpk : PinsRel s.store pk) (he : EnvRel sp s.store env envC)
    (hc : CacheRel s.store c cC) (hx : denoteN s.store.ns x = some xC)
    (hr : ConRon.Arena.Modular.readRecord (modelFs F) pk sp env c x s = .ok ((c', d, h), s')) :
    DStep s s' ∧ PersDecl d ∧ ∃ cC' dC hC,
      ModelIO.Gives (ConLeche.Driver.readRecord envC cC xC) F (cC', .ok (dC, hC)) ∧
      CacheRel s'.store c' cC' ∧ Frontend.denoteDecl s'.store d = some dC ∧
      denoteN s'.store.ns h = some hC := by
  have hw := hctx.wf
  unfold ConRon.Arena.Modular.readRecord at hr
  unfold ConLeche.Driver.readRecord
  have hI := importerSpot_rel hw hctx.nulls he hx
  cases hrsT : ConRon.Arena.Modular.recordSpot pk env c x with
  | none =>
    rw [hrsT] at hr
    exfalso
    obtain ⟨_, _, _, g⟩ := AM.bind_ok hr
    exact AM.fail_ok g
  | some sc =>
  obtain ⟨sp₀, comp⟩ := sc
  rw [hrsT] at hr
  dsimp only at hr
  unfold ConRon.Arena.Modular.recordSpot at hrsT
  cases hiC : ConLeche.Driver.importerSpot envC xC with
  | some p =>
    rcases optRel_cases hI with ⟨-, g⟩ | ⟨a, b, g1, g2, g3⟩
    · rw [g] at hiC; cases hiC
    rw [g2] at hiC
    cases hiC
    rw [g1] at hrsT
    simp only [Option.some.injEq, Prod.mk.injEq] at hrsT
    obtain ⟨ha, hcomp⟩ := hrsT
    have hsr := g3.2
    rw [ha] at hsr
    subst hcomp
    simp only
    generalize p.2 = spC at hsr ⊢
    -- not unsafe or partial
    have hsk : sp₀.pos.skipped = spC.pos.skipped := hsr.2.skipped
    cases hskT : sp₀.pos.skipped with
    | true =>
      rw [hskT] at hr
      exfalso
      obtain ⟨_, _, _, g1⟩ := AM.bind_ok hr
      obtain ⟨_, _, _, g2⟩ := AM.bind_ok g1
      first
      | exact AM.fail_ok g2
      | (obtain ⟨_, _, g3, _⟩ := AM.bind_ok g2; exact AM.fail_ok g3)
    | false =>
    rw [hskT] at hr
    rw [← hsk, hskT]
    simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
    obtain ⟨u0, s₀, h0, hA⟩ := AM.bind_ok hr
    obtain ⟨-, hs0⟩ := AM.pure_ok h0
    subst s₀
    -- its statement and kind
    obtain ⟨cs, s₁, h1, hB⟩ := AM.bind_ok hA
    obtain ⟨c₁, cv, k⟩ := cs
    obtain ⟨hst1, cC₁, cvC, kC, hg1, hc1, hcv, hk⟩ := stmtAt_run hsp hctx he hc hsr h1
    have hctx1 := hctx.step hst1
    have hw1 := hctx1.wf
    have he1 := he.ext hst1.ext hw1
    have hpk1 := hpk.ext hst1.ext
    have hsr1 := hsr.ext hst1.ext
    have hx1 := denoteN_ext hx hst1.ext
    have hh1 : denoteN s₁.store.ns sp₀.part.mod = some spC.part.mod := hsr1.1.1
    dsimp only at hB
    have hgk := groupOfKind_rel hx1 hk
    cases hgT : ConRon.Arena.Modular.groupOfKind x k with
    | some n =>
      rw [hgT] at hB hgk
      rcases optRel_cases hgk with ⟨g1, -⟩ | ⟨a, nC, g1, g2, g3⟩
      · cases g1
      cases g1
      dsimp only at hB
      obtain ⟨cd, s₂, h2, hC⟩ := AM.bind_ok hB
      obtain ⟨c₂, od⟩ := cd
      obtain ⟨hst2, cC₂, odC, hg2, hc2, hod⟩ := groupAt_run (k := ConRon.Arena.Modular.privKey sp₀.part.mod) (kC := ⟨spC.part.mod, .private⟩) hsp hctx1
        hpk1 he1 hc1 ⟨hh1, rfl⟩ g3 h2
      cases od with
      | none => exfalso; dsimp only at hC; am_never hC
      | some d' =>
      dsimp only at hC
      obtain ⟨hv, rfl⟩ := AM.pure_ok hC
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      rcases optRel_cases hod with ⟨g4, -⟩ | ⟨d'', dC, g4, g5, g6⟩
      · cases g4
      cases g4
      refine ⟨hst1.trans hst2, g6.2, cC₂, dC, spC.part.mod, ?_, hc2, g6.1,
        denoteN_ext hh1 hst2.ext⟩
      refine hg1.bind ?_
      dsimp only
      rw [g2]
      dsimp only
      refine hg2.bind ?_
      rw [g5]
      exact ModelIO.gives_pure _ _
    | none =>
    rw [hgT] at hB hgk
    have g2 : ConLeche.Driver.groupOfKind xC kC = none := by
      rcases optRel_cases hgk with ⟨-, g⟩ | ⟨a, nC, g1, -, -⟩
      · exact g
      · cases g1
    dsimp only at hB
    have hst1d := hst1
    cases hkT : k with
    | induct np ni all cs nn ir iu irf => rw [hkT] at hgT; simp [ConRon.Arena.Modular.groupOfKind] at hgT
    | ctor ind ci np nf iu => rw [hkT] at hgT; simp [ConRon.Arena.Modular.groupOfKind] at hgT
    | recur all np ni nmo nmi rules kk iu => rw [hkT] at hgT; simp [ConRon.Arena.Modular.groupOfKind] at hgT
    | quot q =>
      rw [hkT] at hB hk
      simp only [denoteKindN, ConLeche.Frontend.Olean.CKindF.mapM, pure, Option.some.injEq] at hk
      subst hk
      dsimp only at hB
      obtain ⟨d', s₂, h2, hC⟩ := AM.bind_ok hB
      obtain ⟨hv, rfl⟩ := AM.pure_ok hC
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      obtain ⟨hn1, hl1, ht1⟩ := denoteStmt_rr hcv
      have hent : denoteEntry s₁.store ⟨cv.name, cv.levelParams, cv.type, .quot q⟩ =
          some ⟨cvC.name, cvC.levelParams, cvC.type, .quot q⟩ := by
        simp only [denoteEntry, ConLeche.Frontend.Olean.CEntryF.mapM, hn1, hl1, ht1,
          ConLeche.Frontend.Olean.CKindF.mapM]
        rfl
      obtain ⟨hst2, hpd, dC, hgd, hdd⟩ := recordOfEntry_run hctx1.ok.state hctx1.off hctx1.ok.pins hent h2
      refine ⟨hst1.trans (DStep.of_parse hctx1.ok hctx1.off hst2), hpd, cC₁, dC, spC.part.mod, ?_,
        hc1.ext hst2.ext, hdd, denoteN_ext hh1 hst2.ext⟩
      refine hg1.bind ?_
      dsimp only
      rw [g2]
      dsimp only
      rw [hgd]
      exact ModelIO.gives_pure _ _
    | defn v hints sf =>
      rw [hkT] at hB hk
      simp only [denoteKindN, ConLeche.Frontend.Olean.CKindF.mapM] at hk
      obtain ⟨u, -, hk⟩ := bind_some_left hk
      simp only [pure, Option.some.injEq] at hk
      subst hk
      dsimp only at hB
      first
      | try simp only [↓reduceIte] at hB
        obtain ⟨r1, s₂, h2, hC⟩ := AM.bind_ok hB
        obtain ⟨hv, rfl⟩ := AM.pure_ok hC
        subst hv
        obtain ⟨hst2, hpd, cC₂, dC, hC', hg2, hc2, hdd, hhd⟩ := stmtRecord_run hsp hctx1 he1 hc1 hsr1 hcv h2
        refine ⟨hst1.trans hst2, hpd, cC₂, dC, hC', ?_, hc2, hdd, hhd⟩
        refine hg1.bind ?_
        dsimp only
        rw [g2]
        dsimp only
        try simp only [↓reduceIte]
        exact hg2
      | try simp only [Bool.false_eq_true, ↓reduceIte] at hB
        obtain ⟨u0, s₀, h0, hC⟩ := AM.bind_ok hB
        obtain ⟨-, hs0⟩ := AM.pure_ok h0
        subst s₀
        obtain ⟨ce, s₂, h2, hD⟩ := AM.bind_ok hC
        obtain ⟨c₂, e⟩ := ce
        obtain ⟨hst2, cC₂, eC, hg2, hc2, he2⟩ := partEntry_run hsp hctx1 he1 hc1 hsr1.1 h2
        have hctx2 := hctx1.step hst2
        dsimp only at hD
        obtain ⟨d', s₃, h3, hE⟩ := AM.bind_ok hD
        obtain ⟨hv, rfl⟩ := AM.pure_ok hE
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl, rfl⟩ := hv
        obtain ⟨hst3, hpd, dC, hgd, hdd⟩ := recordOfEntry_run hctx2.ok.state hctx2.off hctx2.ok.pins he2 h3
        refine ⟨hst1.trans (hst2.trans (DStep.of_parse hctx2.ok hctx2.off hst3)), hpd, cC₂, dC,
          spC.part.mod, ?_, hc2.ext hst3.ext, hdd, denoteN_ext (denoteN_ext hh1 hst2.ext) hst3.ext⟩
        refine hg1.bind ?_
        dsimp only
        rw [g2]
        dsimp only
        try simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← hsr1.2.loc]
        refine hg2.bind ?_
        dsimp only
        rw [hgd]
        exact ModelIO.gives_pure _ _
    | ax u =>
        rw [hkT] at hB hk
        have hkC : (match kC with
            | .defn .. => true
            | .quot _ => true
            | _ => false) = false := by
          revert hk; unfold denoteKindN
          intro hk
          first
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM, pure] at hk; injection hk with hk; subst hk; rfl)
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
             obtain ⟨_, _, hk⟩ := bind_some_left hk
             first
             | (simp only [pure] at hk; injection hk with hk; subst hk; rfl)
             | (obtain ⟨_, _, hk⟩ := bind_some_left hk
                simp only [pure] at hk; injection hk with hk; subst hk; rfl))
        dsimp only at hB
        obtain ⟨hst2, hpd, cC₂, dC, hC', hg2, hc2, hdd, hhd⟩ := stmtRecord_run hsp hctx1 he1 hc1 hsr1 hcv hB
        refine ⟨hst1.trans hst2, hpd, cC₂, dC, hC', ?_, hc2, hdd, hhd⟩
        refine hg1.bind ?_
        dsimp only
        rw [g2]
        dsimp only
        revert hkC
        cases kC <;> intro hkC <;> first | exact hg2 | cases hkC
    | thm v al =>
        rw [hkT] at hB hk
        have hkC : (match kC with
            | .defn .. => true
            | .quot _ => true
            | _ => false) = false := by
          revert hk; unfold denoteKindN
          intro hk
          first
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM, pure] at hk; injection hk with hk; subst hk; rfl)
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
             obtain ⟨_, _, hk⟩ := bind_some_left hk
             first
             | (simp only [pure] at hk; injection hk with hk; subst hk; rfl)
             | (obtain ⟨_, _, hk⟩ := bind_some_left hk
                simp only [pure] at hk; injection hk with hk; subst hk; rfl))
        dsimp only at hB
        obtain ⟨hst2, hpd, cC₂, dC, hC', hg2, hc2, hdd, hhd⟩ := stmtRecord_run hsp hctx1 he1 hc1 hsr1 hcv hB
        refine ⟨hst1.trans hst2, hpd, cC₂, dC, hC', ?_, hc2, hdd, hhd⟩
        refine hg1.bind ?_
        dsimp only
        rw [g2]
        dsimp only
        revert hkC
        cases kC <;> intro hkC <;> first | exact hg2 | cases hkC
    | opaq v u =>
        rw [hkT] at hB hk
        have hkC : (match kC with
            | .defn .. => true
            | .quot _ => true
            | _ => false) = false := by
          revert hk; unfold denoteKindN
          intro hk
          first
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM, pure] at hk; injection hk with hk; subst hk; rfl)
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
             obtain ⟨_, _, hk⟩ := bind_some_left hk
             first
             | (simp only [pure] at hk; injection hk with hk; subst hk; rfl)
             | (obtain ⟨_, _, hk⟩ := bind_some_left hk
                simp only [pure] at hk; injection hk with hk; subst hk; rfl))
        dsimp only at hB
        obtain ⟨hst2, hpd, cC₂, dC, hC', hg2, hc2, hdd, hhd⟩ := stmtRecord_run hsp hctx1 he1 hc1 hsr1 hcv hB
        refine ⟨hst1.trans hst2, hpd, cC₂, dC, hC', ?_, hc2, hdd, hhd⟩
        refine hg1.bind ?_
        dsimp only
        rw [g2]
        dsimp only
        revert hkC
        cases kC <;> intro hkC <;> first | exact hg2 | cases hkC
  | none =>
    have g : ConRon.Arena.Modular.importerSpot pk env x = none := by
      rcases optRel_cases hI with ⟨g, -⟩ | ⟨a, b, g1, g2, g3⟩
      · exact g
      · rw [g2] at hiC; cases hiC
    rw [g] at hrsT
    simp only [ConRon.Arena.Modular.locatedAt] at hrsT
    rcases optRel_cases (hc.located.get hw hx) with ⟨h1, -⟩ | ⟨q, qC, h1, h2, h3⟩
    · rw [h1] at hrsT; cases hrsT
    rw [h1] at hrsT
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrsT
    obtain ⟨ha, hcomp⟩ := hrsT
    rw [ha] at h3
    subst hcomp
    simp only [h2, Option.map_some]
    generalize qC = spC at h3 ⊢
    have hsr := h3
    -- not unsafe or partial
    have hsk : sp₀.pos.skipped = spC.pos.skipped := hsr.2.skipped
    cases hskT : sp₀.pos.skipped with
    | true =>
      rw [hskT] at hr
      exfalso
      obtain ⟨_, _, _, g1⟩ := AM.bind_ok hr
      obtain ⟨_, _, _, g2⟩ := AM.bind_ok g1
      first
      | exact AM.fail_ok g2
      | (obtain ⟨_, _, g3, _⟩ := AM.bind_ok g2; exact AM.fail_ok g3)
    | false =>
    rw [hskT] at hr
    rw [← hsk, hskT]
    simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
    obtain ⟨u0, s₀, h0, hA⟩ := AM.bind_ok hr
    obtain ⟨-, hs0⟩ := AM.pure_ok h0
    subst s₀
    -- its statement and kind
    obtain ⟨cs, s₁, h1, hB⟩ := AM.bind_ok hA
    obtain ⟨c₁, cv, k⟩ := cs
    obtain ⟨hst1, cC₁, cvC, kC, hg1, hc1, hcv, hk⟩ := stmtAt_run hsp hctx he hc hsr h1
    have hctx1 := hctx.step hst1
    have hw1 := hctx1.wf
    have he1 := he.ext hst1.ext hw1
    have hpk1 := hpk.ext hst1.ext
    have hsr1 := hsr.ext hst1.ext
    have hx1 := denoteN_ext hx hst1.ext
    have hh1 : denoteN s₁.store.ns sp₀.part.mod = some spC.part.mod := hsr1.1.1
    dsimp only at hB
    have hgk := groupOfKind_rel hx1 hk
    cases hgT : ConRon.Arena.Modular.groupOfKind x k with
    | some n =>
      rw [hgT] at hB hgk
      rcases optRel_cases hgk with ⟨g1, -⟩ | ⟨a, nC, g1, g2, g3⟩
      · cases g1
      cases g1
      dsimp only at hB
      obtain ⟨cd, s₂, h2, hC⟩ := AM.bind_ok hB
      obtain ⟨c₂, od⟩ := cd
      obtain ⟨hst2, cC₂, odC, hg2, hc2, hod⟩ := groupAt_run (k := ConRon.Arena.Modular.privKey sp₀.part.mod) (kC := ⟨spC.part.mod, .private⟩) hsp hctx1
        hpk1 he1 hc1 ⟨hh1, rfl⟩ g3 h2
      cases od with
      | none => exfalso; dsimp only at hC; am_never hC
      | some d' =>
      dsimp only at hC
      obtain ⟨hv, rfl⟩ := AM.pure_ok hC
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      rcases optRel_cases hod with ⟨g4, -⟩ | ⟨d'', dC, g4, g5, g6⟩
      · cases g4
      cases g4
      refine ⟨hst1.trans hst2, g6.2, cC₂, dC, spC.part.mod, ?_, hc2, g6.1,
        denoteN_ext hh1 hst2.ext⟩
      refine hg1.bind ?_
      dsimp only
      rw [g2]
      dsimp only
      refine hg2.bind ?_
      rw [g5]
      exact ModelIO.gives_pure _ _
    | none =>
    rw [hgT] at hB hgk
    have g2 : ConLeche.Driver.groupOfKind xC kC = none := by
      rcases optRel_cases hgk with ⟨-, g⟩ | ⟨a, nC, g1, -, -⟩
      · exact g
      · cases g1
    dsimp only at hB
    have hst1d := hst1
    cases hkT : k with
    | induct np ni all cs nn ir iu irf => rw [hkT] at hgT; simp [ConRon.Arena.Modular.groupOfKind] at hgT
    | ctor ind ci np nf iu => rw [hkT] at hgT; simp [ConRon.Arena.Modular.groupOfKind] at hgT
    | recur all np ni nmo nmi rules kk iu => rw [hkT] at hgT; simp [ConRon.Arena.Modular.groupOfKind] at hgT
    | quot q =>
      rw [hkT] at hB hk
      simp only [denoteKindN, ConLeche.Frontend.Olean.CKindF.mapM, pure, Option.some.injEq] at hk
      subst hk
      dsimp only at hB
      obtain ⟨d', s₂, h2, hC⟩ := AM.bind_ok hB
      obtain ⟨hv, rfl⟩ := AM.pure_ok hC
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      obtain ⟨hn1, hl1, ht1⟩ := denoteStmt_rr hcv
      have hent : denoteEntry s₁.store ⟨cv.name, cv.levelParams, cv.type, .quot q⟩ =
          some ⟨cvC.name, cvC.levelParams, cvC.type, .quot q⟩ := by
        simp only [denoteEntry, ConLeche.Frontend.Olean.CEntryF.mapM, hn1, hl1, ht1,
          ConLeche.Frontend.Olean.CKindF.mapM]
        rfl
      obtain ⟨hst2, hpd, dC, hgd, hdd⟩ := recordOfEntry_run hctx1.ok.state hctx1.off hctx1.ok.pins hent h2
      refine ⟨hst1.trans (DStep.of_parse hctx1.ok hctx1.off hst2), hpd, cC₁, dC, spC.part.mod, ?_,
        hc1.ext hst2.ext, hdd, denoteN_ext hh1 hst2.ext⟩
      refine hg1.bind ?_
      dsimp only
      rw [g2]
      dsimp only
      rw [hgd]
      exact ModelIO.gives_pure _ _
    | defn v hints sf =>
      rw [hkT] at hB hk
      simp only [denoteKindN, ConLeche.Frontend.Olean.CKindF.mapM] at hk
      obtain ⟨u, -, hk⟩ := bind_some_left hk
      simp only [pure, Option.some.injEq] at hk
      subst hk
      dsimp only at hB
      first
      | try simp only [↓reduceIte] at hB
        obtain ⟨r1, s₂, h2, hC⟩ := AM.bind_ok hB
        obtain ⟨hv, rfl⟩ := AM.pure_ok hC
        subst hv
        obtain ⟨hst2, hpd, cC₂, dC, hC', hg2, hc2, hdd, hhd⟩ := stmtRecord_run hsp hctx1 he1 hc1 hsr1 hcv h2
        refine ⟨hst1.trans hst2, hpd, cC₂, dC, hC', ?_, hc2, hdd, hhd⟩
        refine hg1.bind ?_
        dsimp only
        rw [g2]
        dsimp only
        try simp only [↓reduceIte]
        exact hg2
      | try simp only [Bool.false_eq_true, ↓reduceIte] at hB
        obtain ⟨u0, s₀, h0, hC⟩ := AM.bind_ok hB
        obtain ⟨-, hs0⟩ := AM.pure_ok h0
        subst s₀
        obtain ⟨ce, s₂, h2, hD⟩ := AM.bind_ok hC
        obtain ⟨c₂, e⟩ := ce
        obtain ⟨hst2, cC₂, eC, hg2, hc2, he2⟩ := partEntry_run hsp hctx1 he1 hc1 hsr1.1 h2
        have hctx2 := hctx1.step hst2
        dsimp only at hD
        obtain ⟨d', s₃, h3, hE⟩ := AM.bind_ok hD
        obtain ⟨hv, rfl⟩ := AM.pure_ok hE
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl, rfl⟩ := hv
        obtain ⟨hst3, hpd, dC, hgd, hdd⟩ := recordOfEntry_run hctx2.ok.state hctx2.off hctx2.ok.pins he2 h3
        refine ⟨hst1.trans (hst2.trans (DStep.of_parse hctx2.ok hctx2.off hst3)), hpd, cC₂, dC,
          spC.part.mod, ?_, hc2.ext hst3.ext, hdd, denoteN_ext (denoteN_ext hh1 hst2.ext) hst3.ext⟩
        refine hg1.bind ?_
        dsimp only
        rw [g2]
        dsimp only
        try simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← hsr1.2.loc]
        refine hg2.bind ?_
        dsimp only
        rw [hgd]
        exact ModelIO.gives_pure _ _
    | ax u =>
        rw [hkT] at hB hk
        have hkC : (match kC with
            | .defn .. => true
            | .quot _ => true
            | _ => false) = false := by
          revert hk; unfold denoteKindN
          intro hk
          first
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM, pure] at hk; injection hk with hk; subst hk; rfl)
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
             obtain ⟨_, _, hk⟩ := bind_some_left hk
             first
             | (simp only [pure] at hk; injection hk with hk; subst hk; rfl)
             | (obtain ⟨_, _, hk⟩ := bind_some_left hk
                simp only [pure] at hk; injection hk with hk; subst hk; rfl))
        dsimp only at hB
        obtain ⟨hst2, hpd, cC₂, dC, hC', hg2, hc2, hdd, hhd⟩ := stmtRecord_run hsp hctx1 he1 hc1 hsr1 hcv hB
        refine ⟨hst1.trans hst2, hpd, cC₂, dC, hC', ?_, hc2, hdd, hhd⟩
        refine hg1.bind ?_
        dsimp only
        rw [g2]
        dsimp only
        revert hkC
        cases kC <;> intro hkC <;> first | exact hg2 | cases hkC
    | thm v al =>
        rw [hkT] at hB hk
        have hkC : (match kC with
            | .defn .. => true
            | .quot _ => true
            | _ => false) = false := by
          revert hk; unfold denoteKindN
          intro hk
          first
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM, pure] at hk; injection hk with hk; subst hk; rfl)
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
             obtain ⟨_, _, hk⟩ := bind_some_left hk
             first
             | (simp only [pure] at hk; injection hk with hk; subst hk; rfl)
             | (obtain ⟨_, _, hk⟩ := bind_some_left hk
                simp only [pure] at hk; injection hk with hk; subst hk; rfl))
        dsimp only at hB
        obtain ⟨hst2, hpd, cC₂, dC, hC', hg2, hc2, hdd, hhd⟩ := stmtRecord_run hsp hctx1 he1 hc1 hsr1 hcv hB
        refine ⟨hst1.trans hst2, hpd, cC₂, dC, hC', ?_, hc2, hdd, hhd⟩
        refine hg1.bind ?_
        dsimp only
        rw [g2]
        dsimp only
        revert hkC
        cases kC <;> intro hkC <;> first | exact hg2 | cases hkC
    | opaq v u =>
        rw [hkT] at hB hk
        have hkC : (match kC with
            | .defn .. => true
            | .quot _ => true
            | _ => false) = false := by
          revert hk; unfold denoteKindN
          intro hk
          first
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM, pure] at hk; injection hk with hk; subst hk; rfl)
          | (simp only [ConLeche.Frontend.Olean.CKindF.mapM] at hk
             obtain ⟨_, _, hk⟩ := bind_some_left hk
             first
             | (simp only [pure] at hk; injection hk with hk; subst hk; rfl)
             | (obtain ⟨_, _, hk⟩ := bind_some_left hk
                simp only [pure] at hk; injection hk with hk; subst hk; rfl))
        dsimp only at hB
        obtain ⟨hst2, hpd, cC₂, dC, hC', hg2, hc2, hdd, hhd⟩ := stmtRecord_run hsp hctx1 he1 hc1 hsr1 hcv hB
        refine ⟨hst1.trans hst2, hpd, cC₂, dC, hC', ?_, hc2, hdd, hhd⟩
        refine hg1.bind ?_
        dsimp only
        rw [g2]
        dsimp only
        revert hkC
        cases kC <;> intro hkC <;> first | exact hg2 | cases hkC

end ConRon.Bridge.Modular
