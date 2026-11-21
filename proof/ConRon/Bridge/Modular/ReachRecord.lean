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

end ConRon.Bridge.Modular
