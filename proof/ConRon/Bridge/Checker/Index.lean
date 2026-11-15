/-
# `ConRon.Bridge.Checker.Index` — the twin's `buildIndex` denotes con-leche's

`Arena/StreamIndex.lean`'s `buildIndex` reads every record once, on the driver's state with no
scratch tier open, and inserts what it installs (`declConstants`, `declTables`) into two maps, a
name's first entry winning (`insertConsts`, `insertTables`).  con-leche's `buildIndex`
(`ConLeche/Cached/StreamIndex.lean`) does the same over the denoted records.  `buildIndex_run`:
the twin's index denotes con-leche's (`IndexDenotes`), and every handle in it is persistent.

The two maps are related by one generic relation (`IdxRel2`) and one generic insertion lemma
(`IdxRel2.insertIfNew`): a first entry wins on both sides at keys that denote each other, by
`denoteN_inj`.  What a record installs is taken from the records' walks as the two hypotheses
`ConstsSpec` and `TablesSpec`, discharged in `Bridge/Checker/Pool.lean`.
-/
module

public import ConRon.Bridge.Checker.StreamIndex
import ConLeche.Verify.Cached.WalkersC
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr

public section

namespace ConRon.Bridge

set_option autoImplicit false
set_option experimental.vcgen true

open ConLeche ConRon.Arena Std.WP
open scoped Lean.Order

/-! ## The two maps, related -/

/-- con-leche: ConLeche/Cached/StreamIndex.lean:38-43 StreamIndex — two maps answer each other
through the denotation: at keys that denote each other, the same counter, the values related. -/
@[expose] def IdxRel2 {V W : Type} (st : EStore) (R : V → W → Prop)
    (m : Std.HashMap NIdx (Nat × V)) (mJ : Std.HashMap ConLeche.Name (Nat × W)) : Prop :=
  (∀ n p, m[n]? = some p → ∃ nm q, denoteN st.ns n = some nm ∧ R p.2 q ∧ mJ[nm]? = some (p.1, q)) ∧
    (∀ nm q, mJ[nm]? = some q → ∃ n v, denoteN st.ns n = some nm ∧ m[n]? = some (q.1, v) ∧ R v q.2)

/-- con-leche: ConLeche/Cached/StreamIndex.lean:45-55 insertConsts / insertTables — **a first
entry wins on both sides**: inserting at keys that denote each other keeps the maps related. -/
theorem IdxRel2.insertIfNew {V W : Type} {st : EStore} {R : V → W → Prop}
    {m : Std.HashMap NIdx (Nat × V)} {mJ : Std.HashMap ConLeche.Name (Nat × W)}
    (hwf : StoreWF st) (h : IdxRel2 st R m mJ) {k : NIdx} {kn : ConLeche.Name} {c : Nat}
    {v : V} {w : W} (hk : denoteN st.ns k = some kn) (hR : R v w) :
    IdxRel2 st R (m.insertIfNew k (c, v)) (mJ.insertIfNew kn (c, w)) := by
  obtain ⟨rk, hrk⟩ := hwf
  -- the key is new on one side exactly when it is new on the other
  have hmem : k ∈ m ↔ kn ∈ mJ := by
    rw [Std.HashMap.mem_iff_isSome_getElem?, Std.HashMap.mem_iff_isSome_getElem?]
    constructor
    · intro hs
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨nm, q, h1, -, h3⟩ := h.1 k p hp
      obtain rfl := Option.some.inj (hk.symm.trans h1)
      rw [h3]; rfl
    · intro hs
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨n, v', h1, h2, -⟩ := h.2 kn q hq
      obtain rfl := denoteN_inj hrk.nsWF h1 hk
      rw [h2]; rfl
  refine ⟨fun n p hp => ?_, fun nm q hq => ?_⟩
  · rw [Std.HashMap.getElem?_insertIfNew] at hp
    split at hp
    · rename_i hc
      obtain ⟨hb, hnm⟩ := hc
      obtain rfl : k = n := eq_of_beq hb
      cases hp
      refine ⟨kn, w, hk, hR, ?_⟩
      rw [Std.HashMap.getElem?_insertIfNew, ite_eq_left ⟨beq_self_eq_true _, fun h' => hnm (hmem.mpr h')⟩]
    · obtain ⟨nm, q, h1, h2, h3⟩ := h.1 n p hp
      refine ⟨nm, q, h1, h2, ?_⟩
      rw [Std.HashMap.getElem?_insertIfNew, ite_eq_right]
      · exact h3
      · rintro ⟨hb, hnm⟩
        obtain rfl : kn = nm := eq_of_beq hb
        exact hnm (by rw [Std.HashMap.mem_iff_isSome_getElem?, h3]; rfl)
  · rw [Std.HashMap.getElem?_insertIfNew] at hq
    split at hq
    · rename_i hc
      obtain ⟨hb, hnm⟩ := hc
      obtain rfl : kn = nm := eq_of_beq hb
      cases hq
      refine ⟨k, v, hk, ?_, hR⟩
      rw [Std.HashMap.getElem?_insertIfNew, ite_eq_left ⟨beq_self_eq_true _, fun h' => hnm (hmem.mp h')⟩]
    · obtain ⟨n, v', h1, h2, h3⟩ := h.2 nm q hq
      refine ⟨n, v', h1, ?_, h3⟩
      rw [Std.HashMap.getElem?_insertIfNew, ite_eq_right]
      · exact h2
      · rintro ⟨hb, hnm⟩
        obtain rfl : k = n := eq_of_beq hb
        exact hnm (by rw [Std.HashMap.mem_iff_isSome_getElem?, h2]; rfl)

/-- con-leche: none — every value of a map satisfies `P`, its key persistent. -/
@[expose] def PersMap {V : Type} (P : V → Prop) (m : Std.HashMap NIdx (Nat × V)) : Prop :=
  ∀ n p, m[n]? = some p → PersN n ∧ P p.2

theorem PersMap.insertIfNew {V : Type} {P : V → Prop} {m : Std.HashMap NIdx (Nat × V)}
    (h : PersMap P m) {k : NIdx} {p : Nat × V} (hk : PersN k) (hp : P p.2) :
    PersMap P (m.insertIfNew k p) := by
  intro n q hq
  rw [Std.HashMap.getElem?_insertIfNew] at hq
  split at hq
  · rename_i hc
    obtain rfl : k = n := eq_of_beq hc.1
    cases hq; exact ⟨hk, hp⟩
  · exact h n q hq

/-! ## The two insertions -/

/-- con-leche: ConLeche/Cached/StreamIndex.lean:45-49 insertConsts — the constants' insertion,
on both sides. -/
theorem insertConsts_rel {st : EStore} (hwf : StoreWF st) :
    ∀ (L : List IConstantInfo) (LJ : List ConstantInfo)
      (m : Std.HashMap NIdx (Nat × IConstantInfo)) (mJ : Std.HashMap ConLeche.Name (Nat × ConstantInfo))
      (c : Nat),
      Frontend.denoteCIList st L = some LJ → PersCIList L →
      IdxRel2 st (fun ci cj => Frontend.denoteCI st ci = some cj) m mJ → PersMap PersCI m →
      IdxRel2 st (fun ci cj => Frontend.denoteCI st ci = some cj)
          (ConRon.Arena.insertConsts m c L).1 (ConLeche.Cached.insertConsts mJ c LJ).1 ∧
        (ConRon.Arena.insertConsts m c L).2 = (ConLeche.Cached.insertConsts mJ c LJ).2 ∧
        PersMap PersCI (ConRon.Arena.insertConsts m c L).1
  | [], LJ, m, mJ, c, hL, _, hR, hP => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at hL
    subst hL
    exact ⟨hR, rfl, hP⟩
  | ci :: L, LJ, m, mJ, c, hL, hp, hR, hP => by
    simp only [Frontend.denoteCIList] at hL
    cases h1 : Frontend.denoteCI st ci with
    | none => rw [h1] at hL; simp at hL
    | some cj =>
      cases h2 : Frontend.denoteCIList st L with
      | none => rw [h1, h2] at hL; simp at hL
      | some LJ' =>
        rw [h1, h2] at hL
        obtain rfl := Option.some.inj hL.symm
        have hpc : PersCI ci := hp ci (by simp)
        exact insertConsts_rel hwf L LJ' _ _ (c + 1) h2 (fun x hx => hp x (by simp [hx]))
          (hR.insertIfNew hwf (denoteCI_name h1) h1)
          (hP.insertIfNew (persCI_name hpc) hpc)

/-- con-leche: ConLeche/Cached/StreamIndex.lean:51-55 insertTables — the tables' insertion, on
both sides. -/
theorem insertTables_rel {st : EStore} (hwf : StoreWF st) (r : Nat) :
    ∀ (Q : List IProjTable) (QJ : List ProjTable)
      (m : Std.HashMap NIdx (Nat × IProjTable)) (mJ : Std.HashMap ConLeche.Name (Nat × ProjTable)),
      Frontend.denoteProjTableList st Q = some QJ → (∀ t ∈ Q, PersProjTable t ∧ IProjTableOK t) →
      IdxRel2 st (fun t pt => Frontend.denoteProjTable st t = some pt ∧ IProjTableOK t) m mJ →
      PersMap PersProjTable m →
      IdxRel2 st (fun t pt => Frontend.denoteProjTable st t = some pt ∧ IProjTableOK t)
          (ConRon.Arena.insertTables m r Q) (ConLeche.Cached.insertTables mJ r QJ) ∧
        PersMap PersProjTable (ConRon.Arena.insertTables m r Q)
  | [], QJ, m, mJ, hQ, _, hR, hP => by
    simp only [Frontend.denoteProjTableList, Option.some.injEq] at hQ
    subst hQ
    exact ⟨hR, hP⟩
  | t :: Q, QJ, m, mJ, hQ, hp, hR, hP => by
    simp only [Frontend.denoteProjTableList] at hQ
    cases h1 : Frontend.denoteProjTable st t with
    | none => rw [h1] at hQ; simp at hQ
    | some pt =>
      cases h2 : Frontend.denoteProjTableList st Q with
      | none => rw [h1, h2] at hQ; simp at hQ
      | some QJ' =>
        rw [h1, h2] at hQ
        obtain rfl := Option.some.inj hQ.symm
        obtain ⟨hpt, hokt⟩ := hp t (by simp)
        exact insertTables_rel hwf r Q QJ' _ _ h2 (fun x hx => hp x (by simp [hx]))
          (hR.insertIfNew hwf (denoteProjTable_structName h1) ⟨h1, hokt⟩)
          (hP.insertIfNew hpt.structName hpt)

/-- con-leche: none — `IdxRel2` across an append of the store. -/
theorem IdxRel2.mono {V W : Type} {st st' : EStore} {R : V → W → Prop} {R' : V → W → Prop}
    {m : Std.HashMap NIdx (Nat × V)} {mJ : Std.HashMap ConLeche.Name (Nat × W)}
    (h : IdxRel2 st R m mJ) (hx : Ext st st') (hR : ∀ v w, R v w → R' v w) :
    IdxRel2 st' R' m mJ :=
  ⟨fun n p hp => by
      obtain ⟨nm, q, h1, h2, h3⟩ := h.1 n p hp
      exact ⟨nm, q, denoteN_ext h1 hx, hR _ _ h2, h3⟩,
    fun nm q hq => by
      obtain ⟨n, v, h1, h2, h3⟩ := h.2 nm q hq
      exact ⟨n, v, denoteN_ext h1 hx, h2, hR _ _ h3⟩⟩

/-! ## What a record installs, as this module takes it -/

/-- con-leche: ConLeche/Kernel/FEnv.lean:251-253 mkFEnv — **the driver's index**: the empty
environment's, over a base holding nothing but the literal names off the pin table, as
`mkIFEnvLits` builds it. -/
@[expose] def driverFE (p : Pins) : IFEnv :=
  IFEnv.ofParts IEnv.empty ∅
    { lits := [PIN_NAT, PIN_NAT_ZERO, PIN_NAT_SUCC, PIN_STRING, PIN_STRING_OF_LIST, PIN_LIST,
        PIN_LIST_NIL, PIN_LIST_CONS, PIN_CHAR, PIN_CHAR_OF_NAT].map (p.names.getD · default) } ∅

/-- con-leche: none — the driver's index's literal names are the pins'. -/
theorem driverFE_lits {s : AState} (hp : PinsOK s) : LitsOK (driverFE s.pins).base s.store := by
  have h : ∀ i, i < pinCount → denoteN s.store.ns (s.pins.names.getD i default) = pinNames[i]? :=
    fun i hi => by
      have hlt : i < s.pins.names.size := by rw [hp.ready]; exact hi
      have hpl : pinNames.length = pinCount := by decide
      have hl : i < pinNames.length := by rw [hpl]; exact hi
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some,
        List.getElem?_eq_getElem hl]
      exact hp.pinAt hlt _ (List.getElem?_eq_getElem hl)
  unfold LitsOK driverFE IFEnv.ofParts
  simp only [List.map_cons, List.map_nil]
  rw [h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide),
    h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide)]
  rfl

/-- con-leche: none — **the driver's state before the check phase**: the core tier's invariant at
the empty environment, which is what the records' walks run from (their readback caches sound,
the pins in place). -/
abbrev DriverOK (s : AState) : Prop := CheckOK false Env.empty (driverFE s.pins) s

/-- con-leche: none — `DriverOK` at a state with the same pins. -/
theorem DriverOK.of_check {s s' : AState} (h : CheckOK false Env.empty (driverFE s.pins) s')
    (hp : s'.pins = s.pins) : DriverOK s' := by
  unfold DriverOK; rw [hp]; exact h

/-- con-leche: ConLeche/Kernel/Install.lean:80-98 declConstants — **the twin's `declConstants`
denotes con-leche's**, on a state with no scratch tier open: the store invariant, an append, the
pins, the tier still closed, and the constants persistent. -/
@[expose] def ConstsSpec : Prop :=
  ∀ {s s' : AState} {pd : IDeclaration} {d : Declaration} {L : List IConstantInfo},
    DriverOK s → s.store.scratchOn = false → PersDecl pd →
    Frontend.denoteDecl s.store pd = some d → declConstants pd s = .ok (L, s') →
    DriverOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧ s'.store.scratchOn = false ∧
      Frontend.denoteCIList s'.store L = some (ConLeche.declConstants d) ∧ PersCIList L

/-- con-leche: ConLeche/Kernel/Install.lean:100-109 declTables — **the twin's `declTables`
denotes con-leche's**, each table persistent and well shaped. -/
@[expose] def TablesSpec : Prop :=
  ∀ {s s' : AState} {pd : IDeclaration} {d : Declaration} {Q : List IProjTable},
    DriverOK s → s.store.scratchOn = false → PersDecl pd →
    Frontend.denoteDecl s.store pd = some d → declTables pd s = .ok (Q, s') →
    DriverOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧ s'.store.scratchOn = false ∧
      Frontend.denoteProjTableList s'.store Q = some (ConLeche.declTables d) ∧
      ∀ t ∈ Q, PersProjTable t ∧ IProjTableOK t

/-! ## The index -/

/-- con-leche: none — the index under construction, related: `IndexDenotes`' content, and
everything in it persistent. -/
structure IndexRel (st : EStore) (I : IStreamIndex) (J : ConLeche.Cached.StreamIndex) : Prop where
  firsts : I.firsts = J.firsts
  next : I.next = J.next
  idx : IdxRel2 st (fun ci cj => Frontend.denoteCI st ci = some cj) I.base.idx J.base.idx
  tbls : IdxRel2 st (fun t pt => Frontend.denoteProjTable st t = some pt ∧ IProjTableOK t)
    I.base.tbls J.base.tbls
  persIdx : PersMap PersCI I.base.idx
  persTbls : PersMap PersProjTable I.base.tbls

/-- con-leche: ConLeche/Cached/StreamIndex.lean:68-76 FrozenIndex — **a frozen index's own
facts**: its literal names denote con-leche's and are persistent, and its two thresholds are
`litFrom` over them (con-leche's proof fields `natFrom_eq`, `strFrom_eq`). -/
structure Frozen (st : EStore) (I : IStreamIndex) : Prop where
  lits : LitsOK I.base st
  persLits : PersNList I.base.lits
  natFrom : I.natFrom = litFrom I.base.idx I.base.lits 0 NAT_LIT_COUNT
  strFrom : I.strFrom = litFrom I.base.idx I.base.lits 0 STR_LIT_COUNT

theorem IndexRel.denotes {st : EStore} {I : IStreamIndex} {J : ConLeche.Cached.StreamIndex}
    (h : IndexRel st I J) (hf : Frozen st I) : IndexDenotes st I J where
  lits := hf.lits
  natFrom := hf.natFrom
  strFrom := hf.strFrom
  firsts := h.firsts
  next := h.next
  idxHit := h.idx.1
  idxCover := h.idx.2
  tblHit := fun n p hp => by
    obtain ⟨nm, q, h1, ⟨h2, h4⟩, h3⟩ := h.tbls.1 n p hp
    exact ⟨nm, q, h1, h2, h3, h4⟩
  tblCover := fun nm q hq => by
    obtain ⟨n, t, h1, h2, h3, -⟩ := h.tbls.2 nm q hq
    exact ⟨n, t, h1, h2, h3⟩

theorem IndexRel.pers {st : EStore} {I : IStreamIndex} {J : ConLeche.Cached.StreamIndex}
    (h : IndexRel st I J) (hl : PersNList I.base.lits) : PersIFBase I.base :=
  ⟨h.persIdx, h.persTbls, hl⟩

theorem IndexRel.mono {st st' : EStore} {I : IStreamIndex} {J : ConLeche.Cached.StreamIndex}
    (h : IndexRel st I J) (hx : Ext st st') : IndexRel st' I J where
  firsts := h.firsts
  next := h.next
  idx := h.idx.mono hx fun _ _ h' => denoteCI_ext h' hx
  tbls := h.tbls.mono hx fun _ _ h' => ⟨denoteProjTable_ext h'.1 hx, h'.2⟩
  persIdx := h.persIdx
  persTbls := h.persTbls

/-- con-leche: ConLeche/Cached/StreamIndex.lean:57-62 StreamIndex.add — **one record into the
index, on both sides**. -/
theorem add_run (hcs : ConstsSpec) (hts : TablesSpec) {s s' : AState} {I I' : IStreamIndex}
    {J : ConLeche.Cached.StreamIndex} {pd : IDeclaration} {d : Declaration}
    (hst : DriverOK s) (hoff : s.store.scratchOn = false) (hp : PersDecl pd)
    (hd : Frontend.denoteDecl s.store pd = some d) (hI : IndexRel s.store I J)
    (h : I.add pd s = .ok (I', s')) :
    DriverOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧ s'.store.scratchOn = false ∧
      IndexRel s'.store I' (J.add d) := by
  simp only [IStreamIndex.add, Bind.bind, StateT.bind, Except.bind] at h
  cases h1 : declConstants pd s with
  | error e => rw [h1] at h; exact nomatch h
  | ok r =>
    obtain ⟨L, s₁⟩ := r
    rw [h1] at h
    obtain ⟨hst₁, hx₁, hp₁, hoff₁, hL, hpL⟩ := hcs hst hoff hp hd h1
    have hd₁ := denoteDecl_pext (PExt.of_ext hx₁) hp hd
    simp only at h
    cases h2 : declTables pd s₁ with
    | error e => rw [h2] at h; exact nomatch h
    | ok r =>
      obtain ⟨Q, s₂⟩ := r
      rw [h2] at h
      obtain ⟨hst₂, hx₂, hp₂, hoff₂, hQ, hpQ⟩ := hts hst₁ hoff₁ hp hd₁ h2
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hI₁ := hI.mono hx₁
      obtain ⟨hidx, hnext, hpidx⟩ := insertConsts_rel hst₁.state.wf L _ I.base.idx J.base.idx I.next hL
        hpL hI₁.idx hI₁.persIdx
      have hI₂ := hI₁.mono hx₂
      have hidx₂ := hidx.mono hx₂ fun _ _ h' => denoteCI_ext h' hx₂
      obtain ⟨htbl, hptbl⟩ := insertTables_rel hst₂.state.wf I.firsts.size Q _ I.base.tbls J.base.tbls
        hQ hpQ hI₂.tbls hI₂.persTbls
      refine ⟨hst₂, hx₁.trans hx₂, hp₂.trans hp₁, hoff₂, ?_⟩
      have hsz : I.firsts.size = J.firsts.size := by rw [hI.firsts]
      refine ⟨by simp [ConLeche.Cached.StreamIndex.add, hI.firsts, hI.next],
        by simp only [ConLeche.Cached.StreamIndex.add, ConLeche.Cached.declConstantsC_eq]
           rw [← hI.next]; exact hnext,
        ?_, ?_, ?_, ?_⟩
      · simpa [ConLeche.Cached.StreamIndex.add, hI.next, ConLeche.Cached.declConstantsC_eq]
          using hidx₂
      · simpa [ConLeche.Cached.StreamIndex.add, hsz, ConLeche.Cached.declTablesC_eq] using htbl
      · simpa using hpidx
      · simpa using hptbl

/-- con-leche: none — `Bridge/Specs.lean`'s `pinAt_spec` with its answer persistent. -/
theorem pinAt_specP (s₀ : AState) (i : Nat) (hp : PinsOK s₀) (hpp : PersPins s₀) :
    ⦃fun s => s = s₀⦄ pinAt i
    ⦃fun n s' => s' = s₀ ∧ (∀ x, pinNames[i]? = some x → denoteN s₀.store.ns n = some x) ∧
        PersN n; ⊤⦄ := by
  have hpn : ∀ j (h : j < s₀.pins.names.size), PersN s₀.pins.names[j] :=
    fun j h => hpp.names _ (Array.getElem_mem h)
  sym only [bridge_grind, PinsOK.pinAt] =>
    vcgen [pinAt] <;> finish

/-- con-leche: none — a pin read, as a run: the state as it was, the handle the pin's name's,
persistent. -/
theorem pinAt_runP {s s' : AState} {i : Nat} {n : NIdx} {x : ConLeche.Name}
    (hp : PinsOK s) (hpp : PersPins s) (hx : pinNames[i]? = some x)
    (h : pinAt i s = .ok (n, s')) : s' = s ∧ denoteN s.store.ns n = some x ∧ PersN n := by
  obtain ⟨rfl, hd, hpn⟩ := AM.of_run (P := fun t => t = s) rfl h (pinAt_specP s i hp hpp)
  exact ⟨rfl, hd x hx, hpn⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:57-60 strLitNames — **the twin's literal names are
con-leche's ten**, at persistent handles off the pin table. -/
theorem strLitNames_run {s s' : AState} {L : List NIdx} (hp : PinsOK s) (hpp : PersPins s)
    (h : Arena.strLitNames s = .ok (L, s')) :
    s' = s ∧ L.map (denoteN s.store.ns) = ConLeche.strLitNames.map some ∧ PersNList L := by
  unfold Arena.strLitNames at h
  obtain ⟨o, s1, hA, hB⟩ := AM.bind_ok h
  unfold Arena.natLitNames at hA
  obtain ⟨b0, t0, g0, k0⟩ := AM.bind_ok hA
  obtain ⟨e0, d0, p0⟩ := pinAt_runP (i := PIN_NAT) hp hpp pinNames_eq_natName g0
  subst e0
  obtain ⟨b1, t1, g1, k1⟩ := AM.bind_ok k0
  obtain ⟨e1, d1, p1⟩ := pinAt_runP (i := PIN_NAT_ZERO) hp hpp pinNames_eq_natZeroName g1
  subst e1
  obtain ⟨b2, t2, g2, k2⟩ := AM.bind_ok k1
  obtain ⟨e2, d2, p2⟩ := pinAt_runP (i := PIN_NAT_SUCC) hp hpp pinNames_eq_natSuccName g2
  subst e2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
  obtain ⟨b3, t3, g3, k3⟩ := AM.bind_ok hB
  obtain ⟨e3, d3, p3⟩ := pinAt_runP (i := PIN_STRING) hp hpp pinNames_eq_stringName g3
  subst e3
  obtain ⟨b4, t4, g4, k4⟩ := AM.bind_ok k3
  obtain ⟨e4, d4, p4⟩ := pinAt_runP (i := PIN_STRING_OF_LIST) hp hpp pinNames_eq_stringOfListName g4
  subst e4
  obtain ⟨b5, t5, g5, k5⟩ := AM.bind_ok k4
  obtain ⟨e5, d5, p5⟩ := pinAt_runP (i := PIN_LIST) hp hpp pinNames_eq_listName g5
  subst e5
  obtain ⟨b6, t6, g6, k6⟩ := AM.bind_ok k5
  obtain ⟨e6, d6, p6⟩ := pinAt_runP (i := PIN_LIST_NIL) hp hpp pinNames_eq_listNilName g6
  subst e6
  obtain ⟨b7, t7, g7, k7⟩ := AM.bind_ok k6
  obtain ⟨e7, d7, p7⟩ := pinAt_runP (i := PIN_LIST_CONS) hp hpp pinNames_eq_listConsName g7
  subst e7
  obtain ⟨b8, t8, g8, k8⟩ := AM.bind_ok k7
  obtain ⟨e8, d8, p8⟩ := pinAt_runP (i := PIN_CHAR) hp hpp pinNames_eq_charName g8
  subst e8
  obtain ⟨b9, t9, g9, k9⟩ := AM.bind_ok k8
  obtain ⟨e9, d9, p9⟩ := pinAt_runP (i := PIN_CHAR_OF_NAT) hp hpp pinNames_eq_charOfNatName g9
  subst e9
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k9
  refine ⟨rfl, ?_, ?_⟩
  · simp [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, ConLeche.strLitNames, ConLeche.natLitNames]
  · intro n hn
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption

/-- con-leche: ConLeche/Cached/StreamIndex.lean:78-80 StreamIndex.freeze — **the twin's freeze**:
the state as it was, the index with the literal names and its thresholds over them, which is
`Frozen`. -/
theorem freeze_run {s s' : AState} {I F : IStreamIndex} (hp : PinsOK s) (hpp : PersPins s)
    (h : I.freeze s = .ok (F, s')) :
    s' = s ∧ F.base.idx = I.base.idx ∧ F.base.tbls = I.base.tbls ∧ F.firsts = I.firsts ∧
      F.next = I.next ∧ Frozen s.store F := by
  unfold IStreamIndex.freeze at h
  obtain ⟨L, s1, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, hL, hpL⟩ := strLitNames_run hp hpp h1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨hL, hpL, rfl, rfl⟩⟩

/-- con-leche: ConLeche/Cached/StreamIndex.lean:64-66 buildIndex — the records, one after
another, on both sides, and the index frozen past the last. -/
theorem buildIndexGo_run (hcs : ConstsSpec) (hts : TablesSpec) :
    ∀ (ds : List IDeclaration) (dsP : List Declaration) (I : IStreamIndex)
      (J : ConLeche.Cached.StreamIndex) (k : Nat) {s s' : AState} {I' : IStreamIndex},
      DriverOK s → PersPins s → s.store.scratchOn = false → (∀ x ∈ ds, PersDecl x) →
      denoteDecls s.store ds = some dsP → IndexRel s.store I J →
      buildIndexGo I k ds s = .ok (.ok I', s') →
      DriverOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧ s'.store.scratchOn = false ∧
        IndexRel s'.store I' (dsP.foldl ConLeche.Cached.StreamIndex.add J) ∧ Frozen s'.store I'
  | [], dsP, I, J, k, s, s', I', hst, hpp, hoff, _, hden, hI, h => by
    simp only [denoteDecls, Option.some.injEq] at hden
    subst hden
    simp only [buildIndexGo] at h
    cases hf : I.freeze s with
    | error e => rw [hf] at h; simp at h
    | ok r =>
      obtain ⟨F, s1⟩ := r
      rw [hf] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨⟩, rfl⟩ := h
      obtain ⟨rfl, hi, ht, hfi, hn, hfz⟩ := freeze_run hst.pins hpp hf
      refine ⟨hst, Ext.refl _, rfl, hoff, ?_, hfz⟩
      exact { firsts := hfi.trans hI.firsts, next := hn.trans hI.next
              idx := hi ▸ hI.idx, tbls := ht ▸ hI.tbls
              persIdx := hi ▸ hI.persIdx, persTbls := ht ▸ hI.persTbls }
  | pd :: ds, dsP, I, J, k, s, s', I', hst, hpp, hoff, hp, hden, hI, h => by
    simp only [denoteDecls] at hden
    cases h1 : Frontend.denoteDecl s.store pd with
    | none => rw [h1] at hden; simp at hden
    | some d =>
      cases h2 : denoteDecls s.store ds with
      | none => rw [h1, h2] at hden; simp at hden
      | some dsP' =>
        rw [h1, h2] at hden
        obtain rfl := Option.some.inj hden.symm
        simp only [buildIndexGo] at h
        cases ha : I.add pd s with
        | error e => rw [ha] at h; simp at h
        | ok r =>
          obtain ⟨I₁, s₁⟩ := r
          rw [ha] at h
          obtain ⟨hst₁, hx₁, hp₁, hoff₁, hI₁⟩ := add_run hcs hts hst hoff (hp pd (by simp)) h1 hI ha
          have hden₁ := denoteDecls_pext (PExt.of_ext hx₁) ds dsP' (fun x hx => hp x (by simp [hx])) h2
          obtain ⟨hst₂, hx₂, hp₂, hoff₂, hI₂, hf₂⟩ := buildIndexGo_run hcs hts ds dsP' I₁ (J.add d)
            (k + 1) hst₁ (hpp.mono hp₁) hoff₁ (fun x hx => hp x (by simp [hx])) hden₁ hI₁ h
          exact ⟨hst₂, hx₁.trans hx₂, hp₂.trans hp₁, hoff₂, hI₂, hf₂⟩

/-- con-leche: ConLeche/Cached/StreamIndex.lean:64-66 buildIndex — **the twin's index of the
records denotes con-leche's index of the denoted records**, on a state with no scratch tier open,
and every handle in it is persistent. -/
theorem buildIndex_run (hcs : ConstsSpec) (hts : TablesSpec) {ds : Array IDeclaration}
    {dsP : List Declaration} {s s' : AState} {I : IStreamIndex}
    (hst : DriverOK s) (hpp : PersPins s) (hoff : s.store.scratchOn = false)
    (hp : ∀ x ∈ ds.toList, PersDecl x)
    (hden : denoteDecls s.store ds.toList = some dsP)
    (h : buildIndex ds s = .ok (.ok I, s')) :
    DriverOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧ s'.store.scratchOn = false ∧
      IndexDenotes s'.store I (ConLeche.Cached.buildIndex dsP.toArray) ∧ PersIFBase I.base := by
  have h0 : IndexRel s.store {} {} :=
    { firsts := rfl, next := rfl
      idx := ⟨fun _ _ hp => by simp at hp, fun _ _ hq => by simp at hq⟩
      tbls := ⟨fun _ _ hp => by simp at hp, fun _ _ hq => by simp at hq⟩
      persIdx := fun _ _ hp => by simp at hp
      persTbls := fun _ _ hp => by simp at hp }
  obtain ⟨hst', hx, hpins, hoff', hI, hfz⟩ :=
    buildIndexGo_run hcs hts ds.toList dsP {} {} 0 hst hpp hoff hp hden h0 h
  have hb : ConLeche.Cached.buildIndex dsP.toArray = dsP.foldl ConLeche.Cached.StreamIndex.add {} := by
    simp [ConLeche.Cached.buildIndex]
  exact ⟨hst', hx, hpins, hoff', hb ▸ hI.denotes hfz, hI.pers hfz.persLits⟩

end ConRon.Bridge
