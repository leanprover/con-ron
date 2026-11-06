/-
# `ConRon.Bridge.EnvDenote` — the declaration layer read back, and across a `PExt`

The readback of an environment's own layer (`denoteIEnv`, `denoteFEnv`), the
coherence of its own index with its list (`IFEnvCoh`), the two "the step only
pushed" relations (`Pushed`, `TPushed`), and the declaration layer's
denotation carried along an append (`…_mono`) and along a persistent extension
(`PExt.denote…`).  What the frozen layer answers is not here: it has no list, and
`IFEnvOK` (`Bridge/StateOK.lean`) states it by lookups.
-/
module

public import ConRon.Bridge.Pers
public import ConRon.Bridge.Rel

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The readback, as `opt` combinators -/

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteNList_cons_opt (st : NStore) (h : NIdx) (hs : List NIdx) :
    Frontend.denoteNList st (h :: hs) =
      opt2 List.cons (denoteN st h) (Frontend.denoteNList st hs) := by
  simp only [Frontend.denoteNList, opt2]
  cases denoteN st h <;> cases Frontend.denoteNList st hs <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteEList_cons_opt (st : EStore) (h : EIdx) (hs : List EIdx) :
    Frontend.denoteEList st (h :: hs) =
      opt2 List.cons (denoteE st h) (Frontend.denoteEList st hs) := by
  simp only [Frontend.denoteEList, opt2]
  cases denoteE st h <;> cases Frontend.denoteEList st hs <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteEArray_map (st : EStore) (hs : Array EIdx) :
    Frontend.denoteEArray st hs = (Frontend.denoteEList st hs.toList).map List.toArray := by
  simp only [Frontend.denoteEArray]
  cases Frontend.denoteEList st hs.toList <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteFire_nested_opt (st : EStore) (lvls : List LIdx) (pins : List EIdx) :
    Frontend.denoteFire st (.nested lvls pins) =
      opt2 RecRuleFire.nested (denoteLList st.ls lvls) (Frontend.denoteEList st pins) := by
  simp only [Frontend.denoteFire, opt2]
  cases denoteLList st.ls lvls <;> cases Frontend.denoteEList st pins <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteProjTable_opt (st : EStore) (t : IProjTable) :
    Frontend.denoteProjTable st t = opt2
      (fun a b => (⟨a.1, a.2.1, t.numParams, a.2.2, t.numFields, b⟩ : ProjTable))
      (opt3 (fun x y z => (x, y, z)) (denoteN st.ns t.structName)
        (Frontend.denoteNList st.ns t.levelParams) (denoteN st.ns t.ctor))
      (Frontend.denoteEArray st t.bodies) := by
  simp only [Frontend.denoteProjTable, opt2, opt3]
  cases denoteN st.ns t.structName <;> cases Frontend.denoteNList st.ns t.levelParams <;>
    cases denoteN st.ns t.ctor <;> cases Frontend.denoteEArray st t.bodies <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteProjTableList_cons_opt (st : EStore) (t : IProjTable) (ts : List IProjTable) :
    Frontend.denoteProjTableList st (t :: ts) =
      opt2 List.cons (Frontend.denoteProjTable st t) (Frontend.denoteProjTableList st ts) := by
  simp only [Frontend.denoteProjTableList, opt2]
  cases Frontend.denoteProjTable st t <;> cases Frontend.denoteProjTableList st ts <;> rfl

/-! ## The declaration layer's denotation across an append -/

/-- con-leche: none — a block's denotation survives an
append (the lanes above have their own copies; this tier cannot import them). -/
theorem denoteCIList_mono {st st' : EStore} (hx : Ext st st') :
    ∀ (cs : List IConstantInfo) (xs : List ConstantInfo),
      Frontend.denoteCIList st cs = some xs → Frontend.denoteCIList st' cs = some xs := by
  intro cs
  induction cs with
  | nil => intro _ h; exact h
  | cons c cs ih =>
    intro xs hxs
    simp only [Frontend.denoteCIList] at hxs ⊢
    cases ha : Frontend.denoteCI st c with
    | none => rw [ha] at hxs; simp at hxs
    | some a =>
      cases has : Frontend.denoteCIList st cs with
      | none => rw [ha, has] at hxs; simp at hxs
      | some as =>
        rw [ha, has] at hxs
        rw [denoteCI_ext ha hx, ih as has]
        exact hxs

/-! ## The own layer's denotation -/

/-- con-leche: ConLeche/Kernel/FEnv.lean:92-94 mkFEnv — **the own index is its
list's index**, con-leche's `fe' = mkFEnv fe'.env` for the layer above the frozen
base, stated EXTENSIONALLY: the same answer at every key of both maps.  The
frozen layer is not constrained. -/
@[expose] def IFEnvCoh (fe : IFEnv) : Prop :=
  (∀ n : NIdx, fe.idx[n]? = (mkIFEnvGo fe.env.consts)[n]?) ∧
    ∀ n : NIdx, fe.tbls[n]? = (mkIFEnvTblsGo fe.env.tables)[n]?

/-- con-leche: ConLeche/Kernel/FEnv.lean:78-84 mkIdxGo — the constant index's
half of `IFEnvCoh`. -/
theorem IFEnvCoh.idx {fe : IFEnv} (h : IFEnvCoh fe) (n : NIdx) :
    fe.idx[n]? = (mkIFEnvGo fe.env.consts)[n]? := h.1 n

/-- con-leche: ConLeche/Kernel/FEnv.lean:86-90 mkTblsGo — the table map's
half of `IFEnvCoh`. -/
theorem IFEnvCoh.tbls {fe : IFEnv} (h : IFEnvCoh fe) (n : NIdx) :
    fe.tbls[n]? = (mkIFEnvTblsGo fe.env.tables)[n]? := h.2 n

/-- con-leche: ConLeche/Kernel/FEnv.lean:130-134 FEnv.push — **`IFEnv.push`
preserves the coherence clause**: `mkIFEnvGo` inserts from the back, so the
cons-extended list's index is the old one with the new constant inserted. -/
theorem IFEnvCoh.push {fe : IFEnv} (h : IFEnvCoh fe) (ci : IConstantInfo) :
    IFEnvCoh (fe.push ci) := by
  refine ⟨fun n => ?_, fun n => h.tbls n⟩
  simp only [IFEnv.push, mkIFEnvGo, Std.HashMap.getElem?_insert, h.idx n]

/-- con-leche: none — a persistent constant's name is persistent. -/
theorem persCI_name {ci : IConstantInfo} (h : PersCI ci) : PersN ci.name := by
  cases ci with
  | axiomInfo v => exact (show PersCV v from h).name
  | defnInfo v e hint => exact h.1.name
  | thmInfo v => exact (show PersCV v from h).name
  | indInfo v c => exact h.1.name
  | ctorInfo v nP nF => exact (show PersCV v from h).name
  | recInfo v mI rP k rs => exact h.1.name

/-! ## A persistent record reads the same at both ends of a `PExt` -/

/-- con-leche: none — a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteNList {a b : EStore} (hx : PExt a b) : ∀ (ns : List NIdx), PersNList ns →
    ∀ xs, Frontend.denoteNList a.ns ns = some xs → Frontend.denoteNList b.ns ns = some xs := by
  intro ns
  induction ns with
  | nil => intro _ _ h; exact h
  | cons n ns ih =>
    intro hp xs h
    rw [denoteNList_cons_opt, opt2_eq_some_iff] at h ⊢
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨p, q, hx.lss.ls.ns n p (hp n (by simp)) h1,
      ih (fun c hc => hp c (by simp [hc])) q h2, rfl⟩

/-- con-leche: none — a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteLList {a b : EStore} (hx : PExt a b) : ∀ (us : List LIdx), PersLList us →
    ∀ xs, Arena.denoteLList a.ls us = some xs → Arena.denoteLList b.ls us = some xs := by
  intro us
  induction us with
  | nil => intro _ _ h; exact h
  | cons n ns ih =>
    intro hp xs h
    simp only [Arena.denoteLList, opt2_eq_some_iff] at h ⊢
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨p, q, hx.lss.ls.lvl n p (hp n (by simp)) h1,
      ih (fun c hc => hp c (by simp [hc])) q h2, rfl⟩

/-- con-leche: none — a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteEList {a b : EStore} (hx : PExt a b) : ∀ (es : List EIdx), PersEList es →
    ∀ xs, Frontend.denoteEList a es = some xs → Frontend.denoteEList b es = some xs := by
  intro es
  induction es with
  | nil => intro _ _ h; exact h
  | cons n ns ih =>
    intro hp xs h
    rw [denoteEList_cons_opt, opt2_eq_some_iff] at h ⊢
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨p, q, hx.expr n p (hp n (by simp)) h1,
      ih (fun c hc => hp c (by simp [hc])) q h2, rfl⟩

/-- con-leche: none — a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteFire {a b : EStore} (hx : PExt a b) {f : IRecRuleFire} (hp : PersFire f)
    (x : RecRuleFire) (h : Frontend.denoteFire a f = some x) :
    Frontend.denoteFire b f = some x := by
  cases f with
  | plain => exact h
  | nested lvls pins =>
    rw [denoteFire_nested_opt, opt2_eq_some_iff] at h ⊢
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨p, q, hx.denoteLList _ hp.1 p h1, hx.denoteEList _ hp.2 q h2, rfl⟩
  | levels lvls =>
    simp only [Frontend.denoteFire, Option.map_eq_some_iff] at h ⊢
    obtain ⟨p, h1, rfl⟩ := h
    exact ⟨p, hx.denoteLList _ hp p h1, rfl⟩

/-- con-leche: none — a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteProjTable {a b : EStore} (hx : PExt a b) {t : IProjTable}
    (hp : PersProjTable t) (x : ProjTable) (h : Frontend.denoteProjTable a t = some x) :
    Frontend.denoteProjTable b t = some x := by
  rw [denoteProjTable_opt, opt2_eq_some_iff] at h ⊢
  obtain ⟨p, q, h1, h2, rfl⟩ := h
  rw [opt3_eq_some_iff] at h1
  obtain ⟨p1, p2, p3, h11, h12, h13, rfl⟩ := h1
  refine ⟨_, _, opt3_eq_some_iff.mpr ⟨p1, p2, p3, hx.lss.ls.ns _ p1 hp.structName h11,
    hx.denoteNList _ hp.levelParams p2 h12, hx.lss.ls.ns _ p3 hp.ctor h13, rfl⟩, ?_, rfl⟩
  rw [denoteEArray_map, Option.map_eq_some_iff] at h2 ⊢
  obtain ⟨l, hl, rfl⟩ := h2
  exact ⟨l, hx.denoteEList _ hp.bodies l hl, rfl⟩

end ConRon.Bridge
