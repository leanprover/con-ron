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
theorem denoteCV_opt (st : EStore) (cv : IConstantVal) :
    Frontend.denoteCV st cv = opt3 (fun n l t => (⟨n, l, t⟩ : ConstantVal))
      (denoteN st.ns cv.name) (Frontend.denoteNList st.ns cv.levelParams)
      (denoteE st cv.type) := by
  simp only [Frontend.denoteCV, opt3]
  cases denoteN st.ns cv.name <;> cases Frontend.denoteNList st.ns cv.levelParams <;>
    cases denoteE st cv.type <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteFire_nested_opt (st : EStore) (lvls : List LIdx) (pins : List EIdx) :
    Frontend.denoteFire st (.nested lvls pins) =
      opt2 RecRuleFire.nested (denoteLList st.ls lvls) (Frontend.denoteEList st pins) := by
  simp only [Frontend.denoteFire, opt2]
  cases denoteLList st.ls lvls <;> cases Frontend.denoteEList st pins <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteRule_opt (st : EStore) (rl : IRecRule) :
    Frontend.denoteRule st rl = opt3
      (fun c f r => (⟨c, rl.nfields, f, r⟩ : RecRule))
      (denoteN st.ns rl.ctor) (Frontend.denoteFire st rl.fire) (denoteE st rl.rhs) := by
  simp only [Frontend.denoteRule, opt3]
  cases denoteN st.ns rl.ctor <;> cases Frontend.denoteFire st rl.fire <;>
    cases denoteE st rl.rhs <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteRules_cons_opt (st : EStore) (r : IRecRule) (rs : List IRecRule) :
    Frontend.denoteRules st (r :: rs) =
      opt2 List.cons (Frontend.denoteRule st r) (Frontend.denoteRules st rs) := by
  simp only [Frontend.denoteRules, opt2]
  cases Frontend.denoteRule st r <;> cases Frontend.denoteRules st rs <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteCaps_opt (st : EStore) (c : IIndCaps) :
    Frontend.denoteCaps st c = opt3
      (fun ct all ctors => (⟨c.eta, ct, c.etaParams, c.etaFields, c.unitlike, c.unitParams,
          all, c.nparams, c.nIdx, ctors⟩ : IndCaps))
      (denoteN st.ns c.etaCtor) (Frontend.denoteNList st.ns c.all)
      (Frontend.denoteNList st.ns c.ctors) := by
  simp only [Frontend.denoteCaps, opt3]
  cases denoteN st.ns c.etaCtor <;> cases Frontend.denoteNList st.ns c.all <;>
    cases Frontend.denoteNList st.ns c.ctors <;> rfl

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
theorem denoteCI_defn_opt (st : EStore) (v : IConstantVal) (e : EIdx) (h : ReducibilityHint) :
    Frontend.denoteCI st (.defnInfo v e h) =
      opt2 (fun cv x => ConstantInfo.defnInfo cv x h) (Frontend.denoteCV st v) (denoteE st e) := by
  simp only [Frontend.denoteCI, opt2]
  cases Frontend.denoteCV st v <;> cases denoteE st e <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteCI_ind_opt (st : EStore) (v : IConstantVal) (c : IIndCaps) :
    Frontend.denoteCI st (.indInfo v c) =
      opt2 ConstantInfo.indInfo (Frontend.denoteCV st v) (Frontend.denoteCaps st c) := by
  simp only [Frontend.denoteCI, opt2]
  cases Frontend.denoteCV st v <;> cases Frontend.denoteCaps st c <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteCI_rec_opt (st : EStore) (v : IConstantVal) (mI rP : Nat) (k : Bool)
    (rs : List IRecRule) :
    Frontend.denoteCI st (.recInfo v mI rP k rs) =
      opt2 (fun cv rules => ConstantInfo.recInfo cv mI rP k rules) (Frontend.denoteCV st v)
        (Frontend.denoteRules st rs) := by
  simp only [Frontend.denoteCI, opt2]
  cases Frontend.denoteCV st v <;> cases Frontend.denoteRules st rs <;> rfl

/-- con-leche: none — the readback, as a combinator of its fields'
readbacks. -/
theorem denoteCIList_cons_opt (st : EStore) (c : IConstantInfo) (cs : List IConstantInfo) :
    Frontend.denoteCIList st (c :: cs) =
      opt2 List.cons (Frontend.denoteCI st c) (Frontend.denoteCIList st cs) := by
  simp only [Frontend.denoteCIList, opt2]
  cases Frontend.denoteCI st c <;> cases Frontend.denoteCIList st cs <;> rfl

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

/-- con-leche: none — the denotation of a list of
projection tables survives an append. -/
theorem denoteProjTableList_mono {st st' : EStore} (hx : Ext st st') :
    ∀ (ts : List IProjTable) (xs : List ProjTable),
      Frontend.denoteProjTableList st ts = some xs →
        Frontend.denoteProjTableList st' ts = some xs := by
  intro ts
  induction ts with
  | nil => intro _ h; exact h
  | cons t ts ih =>
    intro xs hxs
    simp only [Frontend.denoteProjTableList] at hxs ⊢
    cases ha : Frontend.denoteProjTable st t with
    | none => rw [ha] at hxs; simp at hxs
    | some a =>
      cases has : Frontend.denoteProjTableList st ts with
      | none => rw [ha, has] at hxs; simp at hxs
      | some as =>
        rw [ha, has] at hxs
        rw [denoteProjTable_ext ha hx, ih as has]
        exact hxs

/-! ## The own layer's denotation -/

/-- con-leche: none — the denotation of an environment
INDEX: its constant list and its table list, read back.  §8.2's `denoteEnv`. -/
@[expose] def denoteIEnv (st : EStore) (e : IEnv) : Option Env :=
  match Frontend.denoteCIList st e.consts, Frontend.denoteProjTableList st e.tables with
  | some cs, some ts => some ⟨cs, ts⟩
  | _, _ => none

/-- con-leche: none — `denoteIEnv` read off: both lists
denote. -/
theorem denoteIEnv_some {st : EStore} {e : IEnv} {env : Env} :
    denoteIEnv st e = some env ↔
      Frontend.denoteCIList st e.consts = some env.consts ∧
        Frontend.denoteProjTableList st e.tables = some env.tables := by
  unfold denoteIEnv
  constructor
  · intro h
    split at h
    · rename_i cs ts hcs hts
      cases h; exact ⟨hcs, hts⟩
    · cases h
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- con-leche: none — the denotation of the indexed
environment's OWN layer is the denotation of its list (the own index is a cache
of the list, DESIGN §8.3 lesson 13).  The frozen layer below it has no list; what
it answers is stated by lookups (`IFEnvOK`), never as an `Env`. -/
@[expose] def denoteFEnv (st : EStore) (fe : IFEnv) : Option Env := denoteIEnv st fe.env

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

/-- con-leche: ConLeche/Kernel/FEnv.lean:92-94 mkFEnv — an index built by
`mkIFEnv` is coherent. -/
theorem IFEnvCoh.mk (e : IEnv) : IFEnvCoh (mkIFEnv e) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:130-134 FEnv.push — **`IFEnv.push`
preserves the coherence clause**: `mkIFEnvGo` inserts from the back, so the
cons-extended list's index is the old one with the new constant inserted. -/
theorem IFEnvCoh.push {fe : IFEnv} (h : IFEnvCoh fe) (ci : IConstantInfo) :
    IFEnvCoh (fe.push ci) := by
  refine ⟨fun n => ?_, fun n => h.tbls n⟩
  simp only [IFEnv.push, mkIFEnvGo, Std.HashMap.getElem?_insert, h.idx n]

/-- con-leche: ConLeche/Kernel/FEnv.lean:136-141 FEnv.pushTable — **`IFEnv.pushTable`
preserves the coherence clause**. -/
theorem IFEnvCoh.pushTable {fe : IFEnv} (h : IFEnvCoh fe) (t : IProjTable) :
    IFEnvCoh (fe.pushTable t) := by
  refine ⟨fun n => h.idx n, fun n => ?_⟩
  simp only [IFEnv.pushTable, mkIFEnvTblsGo, Std.HashMap.getElem?_insert, h.tbls n]

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **what a push does
to the denotation**: one more constant at the front, which is exactly what
con-leche's `⟨ci :: env.consts, env.tables⟩` writes. -/
theorem denoteFEnv_push {st : EStore} {fe : IFEnv} {env : Env}
    {ci : IConstantInfo} {c : ConstantInfo} (h : denoteFEnv st fe = some env)
    (hci : Frontend.denoteCI st ci = some c) :
    denoteFEnv st (fe.push ci) = some ⟨c :: env.consts, env.tables⟩ := by
  obtain ⟨hcs, hts⟩ := denoteIEnv_some.mp h
  refine denoteIEnv_some.mpr ⟨?_, hts⟩
  simp only [IFEnv.push, Frontend.denoteCIList, hci, hcs]

/-- con-leche: ConLeche/Kernel/FEnv.lean:199-205 pushTable — **what a table
install does to the denotation**: one more table at the front, which is exactly
what con-leche's `⟨env.consts, t :: env.tables⟩` writes. -/
theorem denoteFEnv_pushTable {st : EStore} {fe : IFEnv} {env : Env}
    {t : IProjTable} {pt : ProjTable} (h : denoteFEnv st fe = some env)
    (ht : Frontend.denoteProjTable st t = some pt) :
    denoteFEnv st (fe.pushTable t) = some ⟨env.consts, pt :: env.tables⟩ := by
  obtain ⟨hcs, hts⟩ := denoteIEnv_some.mp h
  refine denoteIEnv_some.mpr ⟨hcs, ?_⟩
  simp only [IFEnv.pushTable, Frontend.denoteProjTableList, ht, hts]

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **the step only
PUSHED**: everything the fold's step did to the environment was `IFEnv.push`,
so the old list is a suffix of the new one. -/
@[expose] def Pushed (fe0 fe : IFEnv) : Prop :=
  ∃ new, fe.env.consts = new ++ fe0.env.consts

theorem Pushed.refl (fe : IFEnv) : Pushed fe fe := ⟨[], rfl⟩

theorem Pushed.trans {a b c : IFEnv} (h₁ : Pushed a b) (h₂ : Pushed b c) :
    Pushed a c := by
  obtain ⟨n₁, e₁⟩ := h₁
  obtain ⟨n₂, e₂⟩ := h₂
  exact ⟨n₂ ++ n₁, by rw [e₂, e₁, List.append_assoc]⟩

theorem Pushed.push (fe : IFEnv) (ci : IConstantInfo) : Pushed fe (fe.push ci) :=
  ⟨[ci], rfl⟩

/-- con-leche: none — a table install pushes no constant. -/
theorem Pushed.pushTable (fe : IFEnv) (t : IProjTable) : Pushed fe (fe.pushTable t) :=
  ⟨[], rfl⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:199-205 pushTable — **the step only
pushed TABLES onto the table list**: the table half of `Pushed`. -/
@[expose] def TPushed (fe0 fe : IFEnv) : Prop :=
  ∃ new, fe.env.tables = new ++ fe0.env.tables

theorem TPushed.refl (fe : IFEnv) : TPushed fe fe := ⟨[], rfl⟩

theorem TPushed.trans {a b c : IFEnv} (h₁ : TPushed a b) (h₂ : TPushed b c) :
    TPushed a c := by
  obtain ⟨n₁, e₁⟩ := h₁
  obtain ⟨n₂, e₂⟩ := h₂
  exact ⟨n₂ ++ n₁, by rw [e₂, e₁, List.append_assoc]⟩

/-- con-leche: none — a constant push installs no table. -/
theorem TPushed.push (fe : IFEnv) (ci : IConstantInfo) : TPushed fe (fe.push ci) :=
  ⟨[], rfl⟩

theorem TPushed.pushTable (fe : IFEnv) (t : IProjTable) : TPushed fe (fe.pushTable t) :=
  ⟨[t], rfl⟩

/-- con-leche: none — a persistent constant's name is persistent. -/
theorem persCI_name {ci : IConstantInfo} (h : PersCI ci) : PersN ci.name := by
  cases ci with
  | axiomInfo v => exact (show PersCV v from h).name
  | defnInfo v e hint => exact h.1.name
  | thmInfo v => exact (show PersCV v from h).name
  | indInfo v c => exact h.1.name
  | ctorInfo v nP nF => exact (show PersCV v from h).name
  | recInfo v mI rP rs => exact h.1.name

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
theorem PExt.denoteCV {a b : EStore} (hx : PExt a b) {cv : IConstantVal} (hp : PersCV cv)
    (x : ConstantVal) (h : Frontend.denoteCV a cv = some x) :
    Frontend.denoteCV b cv = some x := by
  rw [denoteCV_opt, opt3_eq_some_iff] at h ⊢
  obtain ⟨p, q, r, h1, h2, h3, rfl⟩ := h
  exact ⟨p, q, r, hx.lss.ls.ns _ p hp.name h1, hx.denoteNList _ hp.levelParams q h2,
    hx.expr _ r hp.type h3, rfl⟩

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
theorem PExt.denoteRule {a b : EStore} (hx : PExt a b) {rl : IRecRule} (hp : PersRule rl)
    (x : RecRule) (h : Frontend.denoteRule a rl = some x) :
    Frontend.denoteRule b rl = some x := by
  rw [denoteRule_opt, opt3_eq_some_iff] at h ⊢
  obtain ⟨p, q, r, h1, h2, h3, rfl⟩ := h
  exact ⟨p, q, r, hx.lss.ls.ns _ p hp.ctor h1, hx.denoteFire hp.fire q h2,
    hx.expr _ r hp.rhs h3, rfl⟩

/-- con-leche: none — a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteRules {a b : EStore} (hx : PExt a b) : ∀ (rs : List IRecRule), PersRules rs →
    ∀ xs, Frontend.denoteRules a rs = some xs → Frontend.denoteRules b rs = some xs := by
  intro rs
  induction rs with
  | nil => intro _ _ h; exact h
  | cons n ns ih =>
    intro hp xs h
    rw [denoteRules_cons_opt, opt2_eq_some_iff] at h ⊢
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨p, q, hx.denoteRule (hp n (by simp)) p h1,
      ih (fun c hc => hp c (by simp [hc])) q h2, rfl⟩

/-- con-leche: none — a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteCaps {a b : EStore} (hx : PExt a b) {c : IIndCaps} (hp : PersCaps c)
    (x : IndCaps) (h : Frontend.denoteCaps a c = some x) :
    Frontend.denoteCaps b c = some x := by
  rw [denoteCaps_opt, opt3_eq_some_iff] at h ⊢
  obtain ⟨p, q, r, h1, h2, h3, rfl⟩ := h
  exact ⟨p, q, r, hx.lss.ls.ns _ p hp.etaCtor h1, hx.denoteNList _ hp.all q h2,
    hx.denoteNList _ hp.ctors r h3, rfl⟩

/-- con-leche: none — a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteCI {a b : EStore} (hx : PExt a b) {ci : IConstantInfo} (hp : PersCI ci)
    (x : ConstantInfo) (h : Frontend.denoteCI a ci = some x) :
    Frontend.denoteCI b ci = some x := by
  cases ci with
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨p, h1, rfl⟩ := h
    exact ⟨p, hx.denoteCV hp p h1, rfl⟩
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨p, h1, rfl⟩ := h
    exact ⟨p, hx.denoteCV hp p h1, rfl⟩
  | ctorInfo v nP nF =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨p, h1, rfl⟩ := h
    exact ⟨p, hx.denoteCV hp p h1, rfl⟩
  | defnInfo v e hint =>
    rw [denoteCI_defn_opt, opt2_eq_some_iff] at h ⊢
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨p, q, hx.denoteCV hp.1 p h1, hx.expr _ q hp.2 h2, rfl⟩
  | indInfo v c =>
    rw [denoteCI_ind_opt, opt2_eq_some_iff] at h ⊢
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨p, q, hx.denoteCV hp.1 p h1, hx.denoteCaps hp.2 q h2, rfl⟩
  | recInfo v mI rP rs =>
    rw [denoteCI_rec_opt, opt2_eq_some_iff] at h ⊢
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨p, q, hx.denoteCV hp.1 p h1, hx.denoteRules _ hp.2 q h2, rfl⟩

/-- con-leche: none — a persistent block denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteCIList {a b : EStore} (hx : PExt a b) : ∀ (cs : List IConstantInfo),
    PersCIList cs → ∀ xs, Frontend.denoteCIList a cs = some xs →
      Frontend.denoteCIList b cs = some xs := by
  intro cs
  induction cs with
  | nil => intro _ _ h; exact h
  | cons n ns ih =>
    intro hp xs h
    rw [denoteCIList_cons_opt, opt2_eq_some_iff] at h ⊢
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨p, q, hx.denoteCI (hp n (by simp)) p h1,
      ih (fun c hc => hp c (by simp [hc])) q h2, rfl⟩

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

/-- con-leche: none — a persistent table list denotes in the far
end of a `PExt` what it denotes in the near one. -/
theorem PExt.denoteProjTableList {a b : EStore} (hx : PExt a b) : ∀ (ts : List IProjTable),
    (∀ t ∈ ts, PersProjTable t) → ∀ xs, Frontend.denoteProjTableList a ts = some xs →
      Frontend.denoteProjTableList b ts = some xs := by
  intro ts
  induction ts with
  | nil => intro _ _ h; exact h
  | cons n ns ih =>
    intro hp xs h
    rw [denoteProjTableList_cons_opt, opt2_eq_some_iff] at h ⊢
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨p, q, hx.denoteProjTable (hp n (by simp)) p h1,
      ih (fun c hc => hp c (by simp [hc])) q h2, rfl⟩

end ConRon.Bridge
