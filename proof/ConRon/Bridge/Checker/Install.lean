/-
# `ConRon.Bridge.Checker.Install` — what a record installs, at the twin

`Arena/Install.lean`'s `declConstants` and `declTables` read what a record installs off the record,
with no environment: a value record its own constant, an axiom itself (or `Quot.sound`'s pin, or
nothing for `sorryAx`), a quotient record its slot's pin at its names, a block `readBlock` reads
(a pinned basis block included) its formers, constructors, recursors and tables, any other block
nothing.  `constsSpec` and
`tablesSpec`: on the driver's state they denote con-leche's `declConstants`/`declTables` of the
denoted record, keep the core invariant at the empty environment and the scratch tier closed, and
what they return is persistent.  These are the hypotheses `Bridge/Checker/Index.lean`'s
`buildIndex_run` takes.

The pieces are the quotient record's walk (`Bridge/Checker/Basis.lean`: `quotAt_run`) and the
block's (`Bridge/Inductives/Install.lean`: `readBlock_installS`, `blockConstants_run`,
`blockTables_run`).
-/
module

public import ConRon.Bridge.Checker.Index
public import ConRon.Bridge.Checker.Basis
public import ConRon.Bridge.Inductives.Install
import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Frontend.Rel

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge.Inductives

/-! ## The core invariant at the empty environment, carried -/

/-- con-leche: none — `DriverOK` across a frame that writes only the readback caches. -/
theorem DriverOK.of_pstep {s s' : AState} (h : DriverOK s) (hp : PStep s s') : DriverOK s' :=
  ⟨hp.ok, h.caches.monoF hp.ext hp.cframe, h.pins.mono hp.ext hp.pins, h.ienv.mono hp.ext⟩

/-- con-leche: none — `DriverOK` across a renaming. -/
theorem DriverOK.of_rstep {s s' : AState} (h : DriverOK s) (hr : RStep s s') : DriverOK s' :=
  hr.checkOK h

/-- con-leche: none — a denoting record list on a store with no scratch tier open is
persistent. -/
theorem persCIList_of {st : EStore} (hwf : StoreWF st) (hoff : st.scratchOn = false)
    {L : List IConstantInfo} {cs : List ConstantInfo}
    (h : Frontend.denoteCIList st L = some cs) : PersCIList L :=
  Frontend.PersCIList_of_denote hwf hoff h

/-- con-leche: none — a denoting table list on a store with no scratch tier open is
persistent. -/
theorem persProjTables_of {st : EStore} (hwf : StoreWF st) (hoff : st.scratchOn = false) :
    ∀ {Q : List IProjTable} {QP : List ProjTable},
      Frontend.denoteProjTableList st Q = some QP → ∀ t ∈ Q, PersProjTable t
  | [], _, _, _, ht => nomatch ht
  | t :: Q, QP, h, t', ht => by
    rw [denoteProjTableList_cons_opt, opt2_eq_some_iff] at h
    obtain ⟨pt, QP', h1, h2, -⟩ := h
    rcases List.mem_cons.mp ht with rfl | ht'
    · rw [denoteProjTable_opt, opt2_eq_some_iff] at h1
      obtain ⟨a, bs, ha, hbs, -⟩ := h1
      rw [opt3_eq_some_iff] at ha
      obtain ⟨n1, l1, c1, h11, h12, h13, -⟩ := ha
      rw [denoteEArray_map, Option.map_eq_some_iff] at hbs
      obtain ⟨l, hl, -⟩ := hbs
      exact ⟨Frontend.PersN_of_denote hwf hoff h11, Frontend.PersNList_of_denote hwf hoff h12,
        Frontend.PersN_of_denote hwf hoff h13, Frontend.PersEList_of_denote hwf hoff hl⟩
    · exact persProjTables_of hwf hoff h2 t' ht'

/-! ## The constants -/

/-- con-leche: ConLeche/Kernel/Install.lean:80-98 declConstants — **what a record installs,
denoted**. -/
theorem constsSpec : ConstsSpec := by
  intro s s' pd d L hok hoff hp hd hrun
  have hwf := hok.state.wf
  cases pd with
  | defnDecl v e hint =>
    simp only [Frontend.denoteDecl] at hd
    split at hd
    · rename_i cv x hcv hx
      cases hd
      simp only [Arena.declConstants] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      have h : Frontend.denoteCIList s'.store [.defnInfo v e hint] =
          some (ConLeche.declConstants (.defnDecl cv x hint)) := by
        simp [Frontend.denoteCIList, Frontend.denoteCI, hcv, hx, ConLeche.declConstants]
      exact ⟨hok, Ext.refl _, rfl, hoff, h, persCIList_of hwf hoff h⟩
    · cases hd
  | thmDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    split at hd
    · rename_i cv x hcv hx
      cases hd
      simp only [Arena.declConstants] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      have h : Frontend.denoteCIList s'.store [.thmInfo v] =
          some (ConLeche.declConstants (.thmDecl cv x)) := by
        simp [Frontend.denoteCIList, Frontend.denoteCI, hcv, ConLeche.declConstants]
      exact ⟨hok, Ext.refl _, rfl, hoff, h, persCIList_of hwf hoff h⟩
    · cases hd
  | opaqueDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    split at hd
    · rename_i cv x hcv hx
      cases hd
      simp only [Arena.declConstants] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      have h : Frontend.denoteCIList s'.store [.axiomInfo v] =
          some (ConLeche.declConstants (.opaqueDecl cv x)) := by
        simp [Frontend.denoteCIList, Frontend.denoteCI, hcv, ConLeche.declConstants]
      exact ⟨hok, Ext.refl _, rfl, hoff, h, persCIList_of hwf hoff h⟩
    · cases hd
  | axiomDecl v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    obtain ⟨hnm, -, -⟩ := denoteCV_inv hcv
    simp only [Arena.declConstants, declConstantsAxiom] at hrun
    obtain ⟨qs, s1, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.quotSoundName) hok.pins rfl g1
    have hqs : (v.name == qs) = true ↔ cv.name = ConLeche.quotSoundName :=
      beq_handle_iff hwf hnm d1
    rcases AM.ite_ok r1 with ⟨hyes, k⟩ | ⟨hno, k⟩
    · obtain ⟨ci, s2, g2, k2⟩ := AM.bind_ok k
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      obtain ⟨hr, hci⟩ := quotAt_run hok.state hok.readOK hcv g2
      have h : Frontend.denoteCIList s'.store [ci] =
          some (ConLeche.declConstants (.axiomDecl cv)) := by
        simp [Frontend.denoteCIList, hci, ConLeche.declConstants, hqs.mp hyes]
      exact ⟨hok.of_rstep hr, hr.ext, hr.pins, by rw [hr.scratch, hoff], h,
        persCIList_of hr.ok.wf (by rw [hr.scratch, hoff]) h⟩
    · obtain ⟨sa, s2, g2, r2⟩ := AM.bind_ok k
      obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.sorryAxName) hok.pins rfl g2
      have hsa : (v.name == sa) = true ↔ cv.name = ConLeche.sorryAxName :=
        beq_handle_iff hwf hnm d2
      have hq : ¬ cv.name = ConLeche.quotSoundName := fun h => hno (hqs.mpr h)
      rcases AM.ite_ok r2 with ⟨hy2, k3⟩ | ⟨hn2, k3⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        have h : Frontend.denoteCIList s'.store [] =
            some (ConLeche.declConstants (.axiomDecl cv)) := by
          have hq' : ¬ ConLeche.sorryAxName = ConLeche.quotSoundName := hsa.mp hy2 ▸ hq
          simp [Frontend.denoteCIList, ConLeche.declConstants, hsa.mp hy2, hq']
        exact ⟨hok, Ext.refl _, rfl, hoff, h, persCIList_of hwf hoff h⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        have hs : ¬ cv.name = ConLeche.sorryAxName := fun h => hn2 (hsa.mpr h)
        have h : Frontend.denoteCIList s'.store [.axiomInfo v] =
            some (ConLeche.declConstants (.axiomDecl cv)) := by
          simp [Frontend.denoteCIList, Frontend.denoteCI, hcv, ConLeche.declConstants, hq, hs]
        exact ⟨hok, Ext.refl _, rfl, hoff, h, persCIList_of hwf hoff h⟩
  | quotDecl k v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    simp only [Arena.declConstants] at hrun
    obtain ⟨ci, s2, g2, k2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
    obtain ⟨hr, hci⟩ := quotAt_run hok.state hok.readOK hcv g2
    have h : Frontend.denoteCIList s'.store [ci] =
        some (ConLeche.declConstants (.quotDecl k cv)) := by
      simp [Frontend.denoteCIList, hci, ConLeche.declConstants]
    exact ⟨hok.of_rstep hr, hr.ext, hr.pins, by rw [hr.scratch, hoff], h,
      persCIList_of hr.ok.wf (by rw [hr.scratch, hoff]) h⟩
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, rfl⟩ := hd
    simp only [Arena.declConstants] at hrun
    obtain ⟨q, s2, g2, k2⟩ := AM.bind_ok hrun
    obtain ⟨hp2, hsc2, hq⟩ := readBlock_installS hok hb g2
    have hok2 := hok.of_pstep hp2
    have hoff2 : s2.store.scratchOn = false := by rw [hsc2, hoff]
    cases q with
    | error e =>
      simp only [ROp, Except.toOption] at hq
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      have h : Frontend.denoteCIList s'.store [] =
          some (ConLeche.declConstants (.indDecl b nP)) := by
        obtain ⟨e', he'⟩ := Inductives.toOption_eq_none hq
        simp [Frontend.denoteCIList, ConLeche.declConstants, he']
      exact ⟨hok2, hp2.ext, hp2.pins, hoff2, h, persCIList_of hp2.ok.wf hoff2 h⟩
    | ok p =>
      simp only [ROp, Except.toOption] at hq
      obtain ⟨pP, hpP, hdp⟩ := hq
      obtain ⟨hp3, hsc3, hL⟩ := blockConstants_run hok2.state hok2.pins hdp k2
      have h : Frontend.denoteCIList s'.store L =
          some (ConLeche.declConstants (.indDecl b nP)) := by
        simp [ConLeche.declConstants, Inductives.toOption_eq_some hpP, hL]
      have hoff' : s'.store.scratchOn = false := by rw [hsc3, hoff2]
      exact ⟨hok2.of_pstep hp3, hp2.ext.trans hp3.ext, hp3.pins.trans hp2.pins, hoff', h,
        persCIList_of hp3.ok.wf hoff' h⟩

/-! ## The tables -/

/-- con-leche: ConLeche/Kernel/Install.lean:100-109 declTables — **the tables a record installs,
denoted**, each well shaped. -/
theorem tablesSpec : TablesSpec := by
  intro s s' pd d Q hok hoff hp hd hrun
  have nil_arm : Arena.declTables pd = pure [] → ConLeche.declTables d = [] →
      DriverOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧ s'.store.scratchOn = false ∧
        Frontend.denoteProjTableList s'.store Q = some (ConLeche.declTables d) ∧
        ∀ t ∈ Q, PersProjTable t ∧ IProjTableOK t := by
    intro h1 h2
    rw [h1] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨hok, Ext.refl _, rfl, hoff, by rw [h2]; rfl, fun _ h => nomatch h⟩
  cases pd with
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, rfl⟩ := hd
    simp only [Arena.declTables] at hrun
    obtain ⟨q, s2, g2, k2⟩ := AM.bind_ok hrun
    obtain ⟨hp2, hsc2, hq⟩ := readBlock_installS hok hb g2
    have hok2 := hok.of_pstep hp2
    have hoff2 : s2.store.scratchOn = false := by rw [hsc2, hoff]
    cases q with
    | error e =>
      simp only [ROp, Except.toOption] at hq
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      obtain ⟨e', he'⟩ := Inductives.toOption_eq_none hq
      exact ⟨hok2, hp2.ext, hp2.pins, hoff2,
        by simp [ConLeche.declTables, he', Frontend.denoteProjTableList],
        fun _ h => nomatch h⟩
    | ok p =>
      simp only [ROp, Except.toOption] at hq
      obtain ⟨pP, hpP, hdp⟩ := hq
      obtain ⟨hms, -⟩ := dShape_inv hdp
      obtain ⟨o, s3, k3, k4⟩ := AM.bind_ok k2
      obtain ⟨hp3, hsc3, hQ⟩ := blockTables_run p.members pP.members hok2.state hdp hms k3
      have hoff' : s3.store.scratchOn = false := by rw [hsc3, hoff2]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
        simp only [ROp] at hQ
        exact ⟨hok2.of_pstep hp3, hp2.ext.trans hp3.ext, hp3.pins.trans hp2.pins, hoff',
          by simp [ConLeche.declTables, Inductives.toOption_eq_some hpP, hQ,
            Frontend.denoteProjTableList],
          fun _ h => nomatch h⟩
      | some q =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
        obtain ⟨qP, hqP, hq, hokQ⟩ := hQ
        refine ⟨hok2.of_pstep hp3, hp2.ext.trans hp3.ext, hp3.pins.trans hp2.pins, hoff',
          by simp [ConLeche.declTables, Inductives.toOption_eq_some hpP, hqP, hq],
          fun t ht => ⟨?_, hokQ t ht⟩⟩
        exact persProjTables_of hp3.ok.wf hoff' hq t ht
  | defnDecl v e hint =>
    refine nil_arm rfl ?_
    revert hd; cases d <;> simp [Frontend.denoteDecl, ConLeche.declTables] <;> split <;> simp
  | thmDecl v e =>
    refine nil_arm rfl ?_
    revert hd; cases d <;> simp [Frontend.denoteDecl, ConLeche.declTables] <;> split <;> simp
  | opaqueDecl v e =>
    refine nil_arm rfl ?_
    revert hd; cases d <;> simp [Frontend.denoteDecl, ConLeche.declTables] <;> split <;> simp
  | axiomDecl v =>
    refine nil_arm rfl ?_
    revert hd; cases d <;> simp [Frontend.denoteDecl, ConLeche.declTables] <;> split <;> simp
  | quotDecl k v =>
    refine nil_arm rfl ?_
    revert hd; cases d <;> simp [Frontend.denoteDecl, ConLeche.declTables] <;> split <;> simp

end ConRon.Bridge
