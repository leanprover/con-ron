/-
# `ConRon.Bridge.Checker.StreamIndex` — the stream's index denotes con-leche's, and a view is the fold's environment

The twin builds the stream's index once (`Arena/StreamIndex.lean`'s `buildIndex`), and each
record's job checks at the index's view of its position (`IStreamIndex.view`).  This module
relates both to con-leche's (`ConLeche/Cached/StreamIndex.lean`):

* `IndexDenotes st I J`: the twin's index `I` and con-leche's `J` have the same record
  positions and counter, and their two maps answer each other entry for entry through the
  denotation (keys by `denoteN`, constants by `denoteCI`, tables by `denoteProjTable`), every
  table well shaped.  It survives a persistent extension of the store when the index is
  persistent (`IndexDenotes.pmono`), which is how a worker reads it across its jobs' brackets.
* `view_ok`: at a position `pre.length` whose names so far are distinct, the twin's view
  answers what con-leche's environment of the prefix answers (`IFEnvOK (streamEnv pre)`), and no
  table without its structure (`TblGate`).  The step from con-leche's view to the prefix's
  environment is con-leche's own `viewTwin`; this module only moves its two lookups across the
  denotation.

What the index holds (`IndexSpec`, upstream's `buildIndex_spec`) is con-leche's; that the twin's
`buildIndex` denotes con-leche's `buildIndex` is `Bridge/Checker/Index.lean`'s.
-/
module

public import ConRon.Bridge.Checker.Inv
public import ConRon.Arena.StreamIndex
public import ConLeche.Verify.Cached.StreamIndex

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The relation -/

/-- con-leche: ConLeche/Cached/StreamIndex.lean:38-43 StreamIndex — **the twin's index denotes
con-leche's**: the same record positions and next counter; each map's entries answer the other's
through the denotation, at the same counter or record position; every table well shaped. -/
structure IndexDenotes (st : EStore) (I : IStreamIndex) (J : ConLeche.Cached.StreamIndex) :
    Prop where
  firsts : I.firsts = J.firsts
  next : I.next = J.next
  idxHit : ∀ n p, I.base.idx[n]? = some p → ∃ nm c, denoteN st.ns n = some nm ∧
    Frontend.denoteCI st p.2 = some c ∧ J.base.idx[nm]? = some (p.1, c)
  idxCover : ∀ nm q, J.base.idx[nm]? = some q → ∃ n ci, denoteN st.ns n = some nm ∧
    I.base.idx[n]? = some (q.1, ci) ∧ Frontend.denoteCI st ci = some q.2
  tblHit : ∀ n p, I.base.tbls[n]? = some p → ∃ nm pt, denoteN st.ns n = some nm ∧
    Frontend.denoteProjTable st p.2 = some pt ∧ J.base.tbls[nm]? = some (p.1, pt) ∧
    IProjTableOK p.2
  tblCover : ∀ nm q, J.base.tbls[nm]? = some q → ∃ n t, denoteN st.ns n = some nm ∧
    I.base.tbls[n]? = some (q.1, t) ∧ Frontend.denoteProjTable st t = some q.2

/-- con-leche: none — **the index reads the same across a persistent extension**: every handle
it holds is persistent. -/
theorem IndexDenotes.pmono {st st' : EStore} {I : IStreamIndex} {J : ConLeche.Cached.StreamIndex}
    (h : IndexDenotes st I J) (hp : PersIFBase I.base) (hx : PExt st st') :
    IndexDenotes st' I J where
  firsts := h.firsts
  next := h.next
  idxHit := fun n p hn => by
    obtain ⟨hpn, hpc⟩ := hp.idx n p hn
    obtain ⟨nm, c, h1, h2, h3⟩ := h.idxHit n p hn
    exact ⟨nm, c, denoteN_pext hx hpn h1, denoteCI_pext hx hpc h2, h3⟩
  idxCover := fun nm q hq => by
    obtain ⟨n, ci, h1, h2, h3⟩ := h.idxCover nm q hq
    obtain ⟨hpn, hpc⟩ := hp.idx n _ h2
    exact ⟨n, ci, denoteN_pext hx hpn h1, h2, denoteCI_pext hx hpc h3⟩
  tblHit := fun n p hn => by
    obtain ⟨hpn, hpt⟩ := hp.tbls n p hn
    obtain ⟨nm, pt, h1, h2, h3, h4⟩ := h.tblHit n p hn
    exact ⟨nm, pt, denoteN_pext hx hpn h1, denoteProjTable_pext hx hpt h2, h3, h4⟩
  tblCover := fun nm q hq => by
    obtain ⟨n, t, h1, h2, h3⟩ := h.tblCover nm q hq
    obtain ⟨hpn, hpt⟩ := hp.tbls n _ h2
    exact ⟨n, t, denoteN_pext hx hpn h1, h2, denoteProjTable_pext hx hpt h3⟩

/-! ## What a view reads -/

/-- con-leche: ConLeche/Cached/StreamIndex.lean:68-72 StreamIndex.view — the twin's view finds
in the frozen layer, below the record's first counter. -/
theorem IStreamIndex.view_find? (I : IStreamIndex) (k : Nat) (n : NIdx) :
    (I.view k).find? n = match I.base.idx[n]? with
      | some p => if p.1 < I.firsts.getD k I.next then some p.2 else none
      | none => none := by
  rw [IFEnv.find?_eq]
  simp only [IStreamIndex.view, Std.HashMap.getElem?_empty, IFBase.find?]
  cases I.base.idx[n]? with
  | none => rfl
  | some p => obtain ⟨c, ci⟩ := p; rfl

/-- con-leche: ConLeche/Cached/StreamIndex.lean:68-72 StreamIndex.view — the twin's view's raw
table lookup reads the frozen layer, below the record's position. -/
theorem IStreamIndex.view_rawTable? (I : IStreamIndex) (k : Nat) (n : NIdx) :
    (I.view k).rawTable? n = match I.base.tbls[n]? with
      | some p => if p.1 < k then some p.2 else none
      | none => none := by
  simp only [IStreamIndex.view, IFEnv.rawTable?, Std.HashMap.getElem?_empty, IFBase.findTable?]
  cases I.base.tbls[n]? with
  | none => rfl
  | some p => obtain ⟨r, t⟩ := p; rfl

/-- con-leche: ConLeche/Cached/StreamIndex.lean:68-72 StreamIndex.view — con-leche's view, the
same shape. -/
theorem cachedView_find? (J : ConLeche.Cached.StreamIndex) (k : Nat) (nm : ConLeche.Name) :
    (J.view k).find? nm = match J.base.idx[nm]? with
      | some p => if p.1 < J.firsts.getD k J.next then some p.2 else none
      | none => none := by
  simp only [ConLeche.Cached.StreamIndex.view, FEnv.find?, FEnv.lookup_eq,
    Std.HashMap.getElem?_empty, FBase.find?]
  cases J.base.idx[nm]? with
  | none => rfl
  | some p => obtain ⟨c, ci⟩ := p; rfl

/-- con-leche: ConLeche/Cached/StreamIndex.lean:68-72 StreamIndex.view — con-leche's view's raw
table lookup. -/
theorem cachedView_rawTable? (J : ConLeche.Cached.StreamIndex) (k : Nat) (nm : ConLeche.Name) :
    (J.view k).rawTable? nm = match J.base.tbls[nm]? with
      | some p => if p.1 < k then some p.2 else none
      | none => none := by
  simp only [ConLeche.Cached.StreamIndex.view, FEnv.rawTable?, Std.HashMap.getElem?_empty,
    FBase.findTable?]
  cases J.base.tbls[nm]? with
  | none => rfl
  | some p => obtain ⟨r, t⟩ := p; rfl

/-! ## A view is the fold's environment -/

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:420 viewTwin — **the view of a position
answers as the environment of the records before it**, once those records' names are distinct:
`IFEnvOK` at `streamEnv pre`, and no table without its structure.  con-leche's `viewTwin` makes
its own view the prefix's index; this moves the two lookups across `IndexDenotes`. -/
theorem view_ok {s : AState} {I : IStreamIndex} {J : ConLeche.Cached.StreamIndex}
    {pre rest : List Declaration} (hst : StateOK s) (hI : IndexDenotes s.store I J)
    (hJ : ConLeche.Cached.IndexSpec (pre ++ rest) J)
    (hnd : ((ConLeche.Cached.recsConsts pre).map (·.name)).Nodup) :
    IFEnvOK (ConLeche.Cached.streamEnv pre) (I.view pre.length) s ∧
      TblGate (I.view pre.length) := by
  obtain ⟨rk, hrk⟩ := hst.wf
  have htw := ConLeche.Cached.viewTwin hJ rfl hnd
  -- con-leche's view against the prefix's environment
  have hF : ∀ nm, (J.view pre.length).find? nm = (ConLeche.Cached.streamEnv pre).find? nm :=
    fun nm => by rw [← htw.find, mkFEnv_find?]
  have hR : ∀ nm, (J.view pre.length).rawTable? nm =
      (ConLeche.Cached.streamEnv pre).tables.find? (·.structName == nm) :=
    fun nm => by rw [← htw.raw, mkFEnv_rawTable?]
  have hc : I.firsts.getD pre.length I.next = J.firsts.getD pre.length J.next := by
    rw [hI.firsts, hI.next]
  -- the twin's find against con-leche's view
  have fHit : ∀ n ci, (I.view pre.length).find? n = some ci → ∃ nm c,
      denoteN s.store.ns n = some nm ∧ Frontend.denoteCI s.store ci = some c ∧
      (J.view pre.length).find? nm = some c := by
    intro n ci hf
    rw [IStreamIndex.view_find?] at hf
    cases hp : I.base.idx[n]? with
    | none => rw [hp] at hf; cases hf
    | some p =>
      rw [hp] at hf
      simp only at hf
      split at hf
      · rename_i hlt
        cases hf
        obtain ⟨nm, c, h1, h2, h3⟩ := hI.idxHit n p hp
        refine ⟨nm, c, h1, h2, ?_⟩
        rw [cachedView_find?, h3]
        simp only
        rw [ite_eq_left (by rw [← hc]; exact hlt)]
      · cases hf
  have fCover : ∀ nm c, (J.view pre.length).find? nm = some c → ∃ n ci,
      denoteN s.store.ns n = some nm ∧ (I.view pre.length).find? n = some ci ∧
      Frontend.denoteCI s.store ci = some c := by
    intro nm c hf
    rw [cachedView_find?] at hf
    cases hq : J.base.idx[nm]? with
    | none => rw [hq] at hf; cases hf
    | some q =>
      rw [hq] at hf
      simp only at hf
      split at hf
      · rename_i hlt
        cases hf
        obtain ⟨n, ci, h1, h2, h3⟩ := hI.idxCover nm q hq
        refine ⟨n, ci, h1, ?_, h3⟩
        rw [IStreamIndex.view_find?, h2]
        simp only
        rw [ite_eq_left (by rw [hc]; exact hlt)]
      · cases hf
  -- the twin's raw table lookup against con-leche's view
  have tHit : ∀ n t, (I.view pre.length).rawTable? n = some t → ∃ nm pt,
      denoteN s.store.ns n = some nm ∧ Frontend.denoteProjTable s.store t = some pt ∧
      (J.view pre.length).rawTable? nm = some pt ∧ IProjTableOK t := by
    intro n t hf
    rw [IStreamIndex.view_rawTable?] at hf
    cases hp : I.base.tbls[n]? with
    | none => rw [hp] at hf; cases hf
    | some p =>
      rw [hp] at hf
      simp only at hf
      split at hf
      · rename_i hlt
        cases hf
        obtain ⟨nm, pt, h1, h2, h3, h4⟩ := hI.tblHit n p hp
        refine ⟨nm, pt, h1, h2, ?_, h4⟩
        rw [cachedView_rawTable?, h3]
        simp only
        rw [ite_eq_left hlt]
      · cases hf
  have tCover : ∀ nm pt, (J.view pre.length).rawTable? nm = some pt → ∃ n t,
      denoteN s.store.ns n = some nm ∧ (I.view pre.length).rawTable? n = some t ∧
      Frontend.denoteProjTable s.store t = some pt := by
    intro nm pt hf
    rw [cachedView_rawTable?] at hf
    cases hq : J.base.tbls[nm]? with
    | none => rw [hq] at hf; cases hf
    | some q =>
      rw [hq] at hf
      simp only at hf
      split at hf
      · rename_i hlt
        cases hf
        obtain ⟨n, t, h1, h2, h3⟩ := hI.tblCover nm q hq
        refine ⟨n, t, h1, ?_, h3⟩
        rw [IStreamIndex.view_rawTable?, h2]
        simp only
        rw [ite_eq_left hlt]
      · cases hf
  -- a stored table's structure is stored in the prefix's environment
  have hstored : ∀ nm pt, (ConLeche.Cached.streamEnv pre).tables.find? (·.structName == nm)
      = some pt → ((ConLeche.Cached.streamEnv pre).find? nm).isSome = true := by
    intro nm pt hf
    have hmem := List.mem_of_find?_eq_some hf
    have hn : pt.structName = nm := by simpa using List.find?_some hf
    have htabs : (ConLeche.Cached.streamEnv pre).tables = (pre.flatMap declTables).reverse := by
      simpa [Env.empty] using ConLeche.Cached.streamEnv_tables pre Env.empty
    have hcons : (ConLeche.Cached.streamEnv pre).consts =
        (ConLeche.Cached.recsConsts pre).reverse := by
      simpa [Env.empty] using ConLeche.Cached.streamEnv_consts pre Env.empty
    rw [htabs, List.mem_reverse] at hmem
    have hmn : nm ∈ (ConLeche.Cached.recsConsts pre).map (·.name) :=
      (ConLeche.Cached.recsTables_sublist pre).subset
        (List.mem_map.mpr ⟨pt, hmem, hn⟩)
    obtain ⟨c, hc', hcn⟩ := List.mem_map.mp hmn
    unfold Env.find?
    rw [hcons]
    cases hfe : (ConLeche.Cached.recsConsts pre).reverse.find? (·.name == nm) with
    | some _ => rfl
    | none =>
      have := List.find?_eq_none.mp hfe c (List.mem_reverse.mpr hc')
      simp [hcn] at this
  -- the table lookups behind their gates
  have gate : TblGate (I.view pre.length) := by
    intro n t ht
    obtain ⟨nm, pt, h1, -, h3, -⟩ := tHit n t ht
    rw [hR] at h3
    have hs := hstored nm pt h3
    rw [← hF] at hs
    obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨n', ci, h1', h2', -⟩ := fCover nm c hc'
    obtain rfl := denoteN_inj hrk.nsWF h1 h1'
    rw [h2']; rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, gate⟩
  · intro n ci hf
    obtain ⟨nm, c, h1, h2, h3⟩ := fHit n ci hf
    exact ⟨nm, c, h1, h2, by rw [← hF]; exact h3⟩
  · intro nm c he
    rw [← hF] at he
    exact fCover nm c he
  · intro n t hf
    have hraw := IFEnv.rawTable?_of_findTable? hf
    have hg := IFEnv.find?_of_findTable? hf
    obtain ⟨nm, pt, h1, h2, h3, h4⟩ := tHit n t hraw
    refine ⟨nm, pt, h1, h2, ?_, h4⟩
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hg
    obtain ⟨nm', c, h1', -, h3'⟩ := fHit n ci hci
    obtain rfl := Option.some.inj (h1'.symm.trans h1)
    unfold Env.findTable?
    rw [← hF, h3']
    simp only [Option.isSome_some, ↓reduceIte]
    rw [← hR]; exact h3
  · intro nm pt he
    unfold Env.findTable? at he
    split at he
    · rename_i hg
      rw [← hR] at he
      obtain ⟨n, t, h1, h2, h3⟩ := tCover nm pt he
      refine ⟨n, t, h1, ?_, h3⟩
      unfold IFEnv.findTable?
      rw [← hF] at hg
      obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp hg
      obtain ⟨n', ci, h1', h2', -⟩ := fCover nm c hc'
      obtain rfl := denoteN_inj hrk.nsWF h1 h1'
      rw [h2']
      simp only [Option.isSome_some, ↓reduceIte]
      exact h2
    · cases he

end ConRon.Bridge
