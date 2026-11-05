/-
# `ConRon.Bridge.Promote.WalkDecl` — the declaration layer's promotion, run forwards

`Arena/Promote.lean`'s record walk, field for field, over
`Bridge/Promote/Walk.lean`'s four handle-kind cores.
Every lemma has the cores' shape — `PSrc` and the memo survive, the projection only
grows, the answer is persistent, and it keeps the subject's denotation (`Kept`) — at the
`Arena/Frontend/Readback.lean` denotation of its record.

One thing is added at the projection table: the denotation cannot say what
the promotion did to the table's SHAPE or to its key.  `PromotedTable` says
it: the shape fields `IProjTableOK` reads are unchanged, and the structure's
name handle — the table map's key — denotes what it denoted.  That is what
carries `IProjTableOK` across the promotion (`IProjTableOK.promoted`).
-/
module

public import ConRon.Bridge.Promote.Walk
public import ConRon.Bridge.StateOK

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

variable {src : EStore}

/-! ## The readback, as `opt` combinators -/

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteNList_cons_opt (st : NStore) (h : NIdx) (hs : List NIdx) :
    Frontend.denoteNList st (h :: hs) =
      opt2 List.cons (denoteN st h) (Frontend.denoteNList st hs) := by
  simp only [Frontend.denoteNList, opt2]
  cases denoteN st h <;> cases Frontend.denoteNList st hs <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteEList_cons_opt (st : EStore) (h : EIdx) (hs : List EIdx) :
    Frontend.denoteEList st (h :: hs) =
      opt2 List.cons (denoteE st h) (Frontend.denoteEList st hs) := by
  simp only [Frontend.denoteEList, opt2]
  cases denoteE st h <;> cases Frontend.denoteEList st hs <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteEArray_map (st : EStore) (hs : Array EIdx) :
    Frontend.denoteEArray st hs = (Frontend.denoteEList st hs.toList).map List.toArray := by
  simp only [Frontend.denoteEArray]
  cases Frontend.denoteEList st hs.toList <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteCV_opt (st : EStore) (cv : IConstantVal) :
    Frontend.denoteCV st cv = opt3 (fun n l t => (⟨n, l, t⟩ : ConstantVal))
      (denoteN st.ns cv.name) (Frontend.denoteNList st.ns cv.levelParams)
      (denoteE st cv.type) := by
  simp only [Frontend.denoteCV, opt3]
  cases denoteN st.ns cv.name <;> cases Frontend.denoteNList st.ns cv.levelParams <;>
    cases denoteE st cv.type <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteFire_nested_opt (st : EStore) (lvls : List LIdx) (pins : List EIdx) :
    Frontend.denoteFire st (.nested lvls pins) =
      opt2 RecRuleFire.nested (denoteLList st.ls lvls) (Frontend.denoteEList st pins) := by
  simp only [Frontend.denoteFire, opt2]
  cases denoteLList st.ls lvls <;> cases Frontend.denoteEList st pins <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteRule_opt (st : EStore) (rl : IRecRule) :
    Frontend.denoteRule st rl = opt3
      (fun c f r => (⟨c, rl.nfields, rl.ctorParams, f, r, rl.k, rl.eta⟩ : RecRule))
      (denoteN st.ns rl.ctor) (Frontend.denoteFire st rl.fire) (denoteE st rl.rhs) := by
  simp only [Frontend.denoteRule, opt3]
  cases denoteN st.ns rl.ctor <;> cases Frontend.denoteFire st rl.fire <;>
    cases denoteE st rl.rhs <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteRules_cons_opt (st : EStore) (r : IRecRule) (rs : List IRecRule) :
    Frontend.denoteRules st (r :: rs) =
      opt2 List.cons (Frontend.denoteRule st r) (Frontend.denoteRules st rs) := by
  simp only [Frontend.denoteRules, opt2]
  cases Frontend.denoteRule st r <;> cases Frontend.denoteRules st rs <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteCaps_opt (st : EStore) (c : IIndCaps) :
    Frontend.denoteCaps st c = opt3
      (fun ct all ctors => (⟨c.eta, ct, c.etaParams, c.etaFields, c.unitlike, c.unitParams,
          c.ruleK, c.sortZ, all, c.nparams, ctors⟩ : IndCaps))
      (denoteN st.ns c.etaCtor) (Frontend.denoteNList st.ns c.all)
      (Frontend.denoteNList st.ns c.ctors) := by
  simp only [Frontend.denoteCaps, opt3]
  cases denoteN st.ns c.etaCtor <;> cases Frontend.denoteNList st.ns c.all <;>
    cases Frontend.denoteNList st.ns c.ctors <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteProjTable_opt (st : EStore) (t : IProjTable) :
    Frontend.denoteProjTable st t = opt2
      (fun a b => (⟨a.1, a.2.1, t.numParams, a.2.2, t.numFields, b.1, b.2.1, b.2.2⟩ : ProjTable))
      (opt3 (fun x y z => (x, y, z)) (denoteN st.ns t.structName)
        (Frontend.denoteNList st.ns t.levelParams) (denoteN st.ns t.ctor))
      (opt3 (fun x y z => (x, y, z)) (denoteL st.ls t.structSort)
        (Frontend.denoteEArray st t.bodies) (denoteLList st.ls t.guards)) := by
  simp only [Frontend.denoteProjTable, opt2, opt3]
  cases denoteN st.ns t.structName <;> cases Frontend.denoteNList st.ns t.levelParams <;>
    cases denoteN st.ns t.ctor <;> cases denoteL st.ls t.structSort <;>
    cases Frontend.denoteEArray st t.bodies <;> cases denoteLList st.ls t.guards <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteCI_defn_opt (st : EStore) (v : IConstantVal) (e : EIdx) (h : ReducibilityHint) :
    Frontend.denoteCI st (.defnInfo v e h) =
      opt2 (fun cv x => ConstantInfo.defnInfo cv x h) (Frontend.denoteCV st v) (denoteE st e) := by
  simp only [Frontend.denoteCI, opt2]
  cases Frontend.denoteCV st v <;> cases denoteE st e <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteCI_ind_opt (st : EStore) (v : IConstantVal) (c : IIndCaps) :
    Frontend.denoteCI st (.indInfo v c) =
      opt2 ConstantInfo.indInfo (Frontend.denoteCV st v) (Frontend.denoteCaps st c) := by
  simp only [Frontend.denoteCI, opt2]
  cases Frontend.denoteCV st v <;> cases Frontend.denoteCaps st c <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteCI_rec_opt (st : EStore) (v : IConstantVal) (mI rP : Nat) (rs : List IRecRule) :
    Frontend.denoteCI st (.recInfo v mI rP rs) =
      opt2 (fun cv rules => ConstantInfo.recInfo cv mI rP rules) (Frontend.denoteCV st v)
        (Frontend.denoteRules st rs) := by
  simp only [Frontend.denoteCI, opt2]
  cases Frontend.denoteCV st v <;> cases Frontend.denoteRules st rs <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteCIList_cons_opt (st : EStore) (c : IConstantInfo) (cs : List IConstantInfo) :
    Frontend.denoteCIList st (c :: cs) =
      opt2 List.cons (Frontend.denoteCI st c) (Frontend.denoteCIList st cs) := by
  simp only [Frontend.denoteCIList, opt2]
  cases Frontend.denoteCI st c <;> cases Frontend.denoteCIList st cs <;> rfl

/-- con-leche: none — arena infrastructure; the readback, as a combinator of its fields'
readbacks. -/
theorem denoteProjTableList_cons_opt (st : EStore) (t : IProjTable) (ts : List IProjTable) :
    Frontend.denoteProjTableList st (t :: ts) =
      opt2 List.cons (Frontend.denoteProjTable st t) (Frontend.denoteProjTableList st ts) := by
  simp only [Frontend.denoteProjTableList, opt2]
  cases Frontend.denoteProjTable st t <;> cases Frontend.denoteProjTableList st ts <;> rfl

/-! ## The lists -/

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteNList_step {fuel : Nat} : ∀ (ns : List NIdx) {m m' : PMemo}
    {ns' : List NIdx} {s s' : AState},
    PSrc src s.store → PMemoPi m src s.store →
    promoteNList m fuel ns s = .ok ((m', ns'), s') →
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧
      PersNList ns' ∧ ns'.length = ns.length ∧
      Kept (Frontend.denoteNList src.ns ns) (Frontend.denoteNList s'.store.dropScratch.ns ns') := by
  intro ns
  induction ns with
  | nil =>
    intro m m' ns' s s' hs hm hrun
    simp only [promoteNList] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, hm, Ext.refl _, fun _ h => absurd h (by simp), rfl, Kept.some _⟩
  | cons n ns ih =>
    intro m m' ns' s s' hs hm hrun
    simp only [promoteNList] at hrun
    obtain ⟨⟨m1, n1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hd1⟩ := promoteN_step hs hm h1
    obtain ⟨⟨m2, ns2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hm2, hx2, hp2, hl2, hd2⟩ := ih hs1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs2, hm2, hx1.trans hx2, ?_, by simp [hl2], ?_⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hp1
      · exact hp2 c hc
    · rw [denoteNList_cons_opt, denoteNList_cons_opt]
      exact Kept.opt2 List.cons (hd1.post (hx2.lss.ls.ns n1)) hd2

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteEList_step {fuel : Nat} : ∀ (es : List EIdx) {m m' : PMemo}
    {es' : List EIdx} {s s' : AState},
    PSrc src s.store → PMemoPi m src s.store →
    promoteEList m fuel es s = .ok ((m', es'), s') →
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧
      PersEList es' ∧ es'.length = es.length ∧
      Kept (Frontend.denoteEList src es) (Frontend.denoteEList s'.store.dropScratch es') := by
  intro es
  induction es with
  | nil =>
    intro m m' es' s s' hs hm hrun
    simp only [promoteEList] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, hm, Ext.refl _, fun _ h => absurd h (by simp), rfl, Kept.some _⟩
  | cons e es ih =>
    intro m m' es' s s' hs hm hrun
    simp only [promoteEList] at hrun
    obtain ⟨⟨m1, e1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hd1⟩ := promoteE_step hs hm h1
    obtain ⟨⟨m2, es2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hm2, hx2, hp2, hl2, hd2⟩ := ih hs1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs2, hm2, hx1.trans hx2, ?_, by simp [hl2], ?_⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hp1
      · exact hp2 c hc
    · rw [denoteEList_cons_opt, denoteEList_cons_opt]
      exact Kept.opt2 List.cons (hd1.post (hx2.expr e1)) hd2

/-! ## The constant header -/

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteCV_step {m m' : PMemo} {fuel : Nat} {cv cv' : IConstantVal}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteCV m fuel cv s = .ok ((m', cv'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersCV cv' ∧
      NameKept src s'.store.dropScratch cv.name cv'.name ∧
      Kept (Frontend.denoteCV src cv) (Frontend.denoteCV s'.store.dropScratch cv') := by
  simp only [promoteCV] at hrun
  obtain ⟨⟨m1, n1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hm1, hx1, hp1, hd1⟩ := promoteN_step hs hm h1
  have hk1 := promoteN_kept hs hm h1
  obtain ⟨⟨m2, l2⟩, s2, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hs2, hm2, hx2, hp2, -, hd2⟩ := promoteNList_step _ hs1 hm1 h3
  obtain ⟨⟨m3, t3⟩, s3, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨hs3, hm3, hx3, hp3, hd3⟩ := promoteE_step hs2 hm2 h5
  obtain ⟨hr, rfl⟩ := AM.pure_ok h6
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  refine ⟨hs3, hm3, (hx1.trans hx2).trans hx3, ⟨hp1, hp2, hp3⟩, hk1.post (hx2.trans hx3), ?_⟩
  rw [denoteCV_opt, denoteCV_opt]
  exact Kept.opt3 _ (hd1.post ((hx2.trans hx3).lss.ls.ns n1))
    (hd2.post (denoteNList_ext hx3.lss.ls.ns l2)) hd3

/-! ## Recursor rules, capabilities, projection tables -/

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteFire_step {m m' : PMemo} {fuel : Nat} {f f' : IRecRuleFire}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteFire m fuel f s = .ok ((m', f'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersFire f' ∧
      Kept (Frontend.denoteFire src f) (Frontend.denoteFire s'.store.dropScratch f') := by
  cases f with
  | plain =>
    simp only [promoteFire] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, hm, Ext.refl _, trivial, Kept.some _⟩
  | nested lvls pins =>
    simp only [promoteFire] at hrun
    obtain ⟨⟨m1, l1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, -, hd1⟩ := promoteLList_step lvls hs hm h1
    obtain ⟨⟨m2, p2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hm2, hx2, hp2, -, hd2⟩ := promoteEList_step pins hs1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩, ?_⟩
    rw [denoteFire_nested_opt, denoteFire_nested_opt]
    exact Kept.opt2 _ (hd1.post (denoteLList_ext hx2.lss.ls l1)) hd2

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteRule_step {m m' : PMemo} {fuel : Nat} {rl rl' : IRecRule}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteRule m fuel rl s = .ok ((m', rl'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersRule rl' ∧
      Kept (Frontend.denoteRule src rl) (Frontend.denoteRule s'.store.dropScratch rl') := by
  simp only [promoteRule] at hrun
  obtain ⟨⟨m1, c1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hm1, hx1, hp1, hd1⟩ := promoteN_step hs hm h1
  obtain ⟨⟨m2, f2⟩, s2, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hs2, hm2, hx2, hp2, hd2⟩ := promoteFire_step hs1 hm1 h3
  obtain ⟨⟨m3, r3⟩, s3, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨hs3, hm3, hx3, hp3, hd3⟩ := promoteE_step hs2 hm2 h5
  obtain ⟨hr, rfl⟩ := AM.pure_ok h6
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  refine ⟨hs3, hm3, (hx1.trans hx2).trans hx3, ⟨hp1, hp2, hp3⟩, ?_⟩
  rw [denoteRule_opt, denoteRule_opt]
  exact Kept.opt3 _ (hd1.post ((hx2.trans hx3).lss.ls.ns c1))
    (hd2.post fun _ h => denoteFire_ext h hx3) hd3

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteRules_step {fuel : Nat} : ∀ (rs : List IRecRule) {m m' : PMemo}
    {rs' : List IRecRule} {s s' : AState},
    PSrc src s.store → PMemoPi m src s.store →
    promoteRules m fuel rs s = .ok ((m', rs'), s') →
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧
      PersRules rs' ∧
      Kept (Frontend.denoteRules src rs) (Frontend.denoteRules s'.store.dropScratch rs') := by
  intro rs
  induction rs with
  | nil =>
    intro m m' rs' s s' hs hm hrun
    simp only [promoteRules] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, hm, Ext.refl _, fun _ h => absurd h (by simp), Kept.some _⟩
  | cons r rs ih =>
    intro m m' rs' s s' hs hm hrun
    simp only [promoteRules] at hrun
    obtain ⟨⟨m1, r1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hd1⟩ := promoteRule_step hs hm h1
    obtain ⟨⟨m2, rs2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hm2, hx2, hp2, hd2⟩ := ih hs1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs2, hm2, hx1.trans hx2, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hp1
      · exact hp2 c hc
    · rw [denoteRules_cons_opt, denoteRules_cons_opt]
      exact Kept.opt2 List.cons (hd1.post fun _ h => denoteRule_ext h hx2) hd2

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteCaps_step {m m' : PMemo} {fuel : Nat} {c c' : IIndCaps}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteCaps m fuel c s = .ok ((m', c'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersCaps c' ∧
      Kept (Frontend.denoteCaps src c) (Frontend.denoteCaps s'.store.dropScratch c') := by
  simp only [promoteCaps] at hrun
  obtain ⟨⟨m1, n1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hm1, hx1, hp1, hd1⟩ := promoteN_step hs hm h1
  obtain ⟨⟨m2, al⟩, s2, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hs2, hm2, hx2, hp2, -, hd2⟩ := promoteNList_step _ hs1 hm1 h3
  obtain ⟨⟨m3, ks⟩, s3, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨hs3, hm3, hx3, hp3, -, hd3⟩ := promoteNList_step _ hs2 hm2 h5
  obtain ⟨hr, rfl⟩ := AM.pure_ok h6
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  refine ⟨hs3, hm3, (hx1.trans hx2).trans hx3, ⟨hp1, hp2, hp3⟩, ?_⟩
  rw [denoteCaps_opt, denoteCaps_opt]
  exact Kept.opt3 _ (hd1.post ((hx2.trans hx3).lss.ls.ns n1))
    (hd2.post (denoteNList_ext hx3.lss.ls.ns al)) hd3

/-- con-leche: none — arena infrastructure; **what the promotion does to a
projection table** beyond its denotation: the fields `IProjTableOK` reads are
unchanged, and the structure's name handle — the table map's key — denotes in the
projection `st'` what it denoted in the source `src`, and is unmoved when it was
persistent. -/
structure PromotedTable (src st' : EStore) (t t' : IProjTable) : Prop where
  numFields : t'.numFields = t.numFields
  bodies : t'.bodies.size = t.bodies.size
  guards : t'.guards.length = t.guards.length
  structName : ∀ x, denoteN src.ns t.structName = some x →
    denoteN st'.ns t'.structName = some x
  structPers : PersN t.structName → t'.structName = t.structName

/-- con-leche: none — arena infrastructure; the answer's side of `PromotedTable` moves
along an append. -/
theorem PromotedTable.mono {src st' st'' : EStore} {t t' : IProjTable}
    (h : PromotedTable src st' t t') (hx : Ext st' st'') : PromotedTable src st'' t t' where
  numFields := h.numFields
  bodies := h.bodies
  guards := h.guards
  structName := fun x hx' => hx.lss.ls.ns _ _ (h.structName x hx')
  structPers := h.structPers

/-- con-leche: none — arena infrastructure; **`IProjTableOK` survives the
promotion** of its table. -/
theorem IProjTableOK.promoted {st st' : EStore} {t t' : IProjTable}
    (h : IProjTableOK t) (hp : PromotedTable st st' t t') : IProjTableOK t' where
  bodies := by rw [hp.bodies, hp.numFields]; exact h.bodies
  guards := by rw [hp.guards, hp.numFields]; exact h.guards

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteProjTable_step {m m' : PMemo} {fuel : Nat} {t t' : IProjTable}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteProjTable m fuel t s = .ok ((m', t'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧
      PersProjTable t' ∧ PromotedTable src s'.store.dropScratch t t' ∧
      Kept (Frontend.denoteProjTable src t) (Frontend.denoteProjTable s'.store.dropScratch t') := by
  simp only [promoteProjTable] at hrun
  obtain ⟨⟨m1, sn1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hm1, hx1, hp1, hd1⟩ := promoteN_step hs hm h1
  have hsp : PersN t.structName → sn1 = t.structName := fun hp => promoteN_pers_self hp h1
  obtain ⟨⟨m3, lps3⟩, s3, h5, h6⟩ := AM.bind_ok h2
  obtain ⟨hs3, hm3, hx3, hp3, -, hd3⟩ := promoteNList_step _ hs1 hm1 h5
  obtain ⟨⟨m4, c4⟩, s4, h7, h8⟩ := AM.bind_ok h6
  obtain ⟨hs4, hm4, hx4, hp4, hd4⟩ := promoteN_step hs3 hm3 h7
  obtain ⟨⟨m5, ss5⟩, s5, h9, h10⟩ := AM.bind_ok h8
  obtain ⟨hs5, hm5, hx5, hp5, hd5⟩ := promoteL_step hs4 hm4 h9
  obtain ⟨⟨m6, bs6⟩, s6, h11, h12⟩ := AM.bind_ok h10
  obtain ⟨hs6, hm6, hx6, hp6, hl6, hd6⟩ := promoteEList_step _ hs5 hm5 h11
  obtain ⟨⟨m7, gs7⟩, s7, h13, h14⟩ := AM.bind_ok h12
  obtain ⟨hs7, hm7, hx7, hp7, hl7, hd7⟩ := promoteLList_step _ hs6 hm6 h13
  obtain ⟨hr, rfl⟩ := AM.pure_ok h14
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  have x37 := ((hx4.trans hx5).trans hx6).trans hx7
  have x27 := hx3.trans x37
  have x47 := (hx5.trans hx6).trans hx7
  have x57 := hx6.trans hx7
  refine ⟨hs7, hm7, hx1.trans x27, ⟨hp1, hp3, hp4, hp5, by simpa using hp6, hp7⟩,
    ⟨rfl, by simp [hl6], hl7, fun x h => x27.lss.ls.ns _ _ (hd1.2 x h), hsp⟩, ?_⟩
  rw [denoteProjTable_opt, denoteProjTable_opt]
  refine Kept.opt2 _ (Kept.opt3 _ (hd1.post (x27.lss.ls.ns sn1))
    (hd3.post (denoteNList_ext x37.lss.ls.ns lps3)) (hd4.post (x47.lss.ls.ns c4)))
    (Kept.opt3 _ (hd5.post (x57.lss.ls.lvl ss5)) ?_ hd7)
  rw [denoteEArray_map, denoteEArray_map]
  exact Kept.map _ (hd6.post (denoteEList_ext hx7 bs6))

/-! ## The stored constant -/

/-- con-leche: none — arena infrastructure; `IConstantInfo.name`'s handle
denotes what it denoted: the header's name. -/
@[expose] def CINameKept (src st' : EStore) (ci ci' : IConstantInfo) : Prop :=
  NameKept src st' ci.name ci'.name

/-- con-leche: none — arena infrastructure; `CINameKept` entry by entry. -/
inductive CIListKept (src st' : EStore) : List IConstantInfo → List IConstantInfo → Prop
  | nil : CIListKept src st' [] []
  | cons {c c' : IConstantInfo} {cs cs' : List IConstantInfo} :
      CINameKept src st' c c' → CIListKept src st' cs cs' →
      CIListKept src st' (c :: cs) (c' :: cs')

/-- con-leche: none — arena infrastructure; the promotion keeps a block's length. -/
theorem CIListKept.length {src st' : EStore} {cs cs' : List IConstantInfo}
    (h : CIListKept src st' cs cs') : cs'.length = cs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteCI_step {m m' : PMemo} {fuel : Nat} {ci ci' : IConstantInfo}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteCI m fuel ci s = .ok ((m', ci'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersCI ci' ∧
      CINameKept src s'.store.dropScratch ci ci' ∧
      Kept (Frontend.denoteCI src ci) (Frontend.denoteCI s'.store.dropScratch ci') := by
  cases ci with
  | axiomInfo v =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hs hm h1
    obtain ⟨hr, rfl⟩ := AM.pure_ok h2
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs1, hm1, hx1, hp1, hn1, Kept.map _ hd1⟩
  | ctorInfo v nP nF =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hs hm h1
    obtain ⟨hr, rfl⟩ := AM.pure_ok h2
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs1, hm1, hx1, hp1, hn1, Kept.map _ hd1⟩
  | defnInfo v e hint =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hs hm h1
    obtain ⟨⟨m2, e2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hm2, hx2, hp2, hd2⟩ := promoteE_step hs1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩, hn1.post hx2, ?_⟩
    rw [denoteCI_defn_opt, denoteCI_defn_opt]
    exact Kept.opt2 _ (hd1.post fun _ h => denoteCV_ext h hx2) hd2
  | thmInfo v =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hs hm h1
    obtain ⟨hr, rfl⟩ := AM.pure_ok h2
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs1, hm1, hx1, hp1, hn1, Kept.map _ hd1⟩
  | indInfo v caps =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hs hm h1
    obtain ⟨⟨m2, c2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hm2, hx2, hp2, hd2⟩ := promoteCaps_step hs1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩, hn1.post hx2, ?_⟩
    rw [denoteCI_ind_opt, denoteCI_ind_opt]
    exact Kept.opt2 _ (hd1.post fun _ h => denoteCV_ext h hx2) hd2
  | recInfo v mI rP rs =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hs hm h1
    obtain ⟨⟨m2, r2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hm2, hx2, hp2, hd2⟩ := promoteRules_step rs hs1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩, hn1.post hx2, ?_⟩
    rw [denoteCI_rec_opt, denoteCI_rec_opt]
    exact Kept.opt2 _ (hd1.post fun _ h => denoteCV_ext h hx2) hd2

/-- con-leche: none — arena infrastructure; a block's denotation survives an
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

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteCIList_step {fuel : Nat} : ∀ (cs : List IConstantInfo) {m m' : PMemo}
    {cs' : List IConstantInfo} {s s' : AState},
    PSrc src s.store → PMemoPi m src s.store →
    promoteCIList m fuel cs s = .ok ((m', cs'), s') →
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧
      PersCIList cs' ∧ CIListKept src s'.store.dropScratch cs cs' ∧
      Kept (Frontend.denoteCIList src cs) (Frontend.denoteCIList s'.store.dropScratch cs') := by
  intro cs
  induction cs with
  | nil =>
    intro m m' cs' s s' hs hm hrun
    simp only [promoteCIList] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, hm, Ext.refl _, fun _ h => absurd h (by simp), .nil, Kept.some _⟩
  | cons c cs ih =>
    intro m m' cs' s s' hs hm hrun
    simp only [promoteCIList] at hrun
    obtain ⟨⟨m1, c1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCI_step hs hm h1
    obtain ⟨⟨m2, cs2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hm2, hx2, hp2, hn2, hd2⟩ := ih hs1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs2, hm2, hx1.trans hx2, ?_, .cons (NameKept.post hn1 hx2) hn2, ?_⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hp1
      · exact hp2 x hx
    · rw [denoteCIList_cons_opt, denoteCIList_cons_opt]
      exact Kept.opt2 List.cons (hd1.post fun _ h => denoteCI_ext h hx2) hd2

/-! ## A step's projection tables -/

/-- con-leche: none — arena infrastructure; `PromotedTable` table by table. -/
inductive TblListKept (src st' : EStore) : List IProjTable → List IProjTable → Prop
  | nil : TblListKept src st' [] []
  | cons {t t' : IProjTable} {ts ts' : List IProjTable} :
      PromotedTable src st' t t' → TblListKept src st' ts ts' →
      TblListKept src st' (t :: ts) (t' :: ts')

/-- con-leche: none — arena infrastructure; the denotation of a list of
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

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteProjTables_step {fuel : Nat} : ∀ (ts : List IProjTable) {m m' : PMemo}
    {ts' : List IProjTable} {s s' : AState},
    PSrc src s.store → PMemoPi m src s.store →
    promoteProjTables m fuel ts s = .ok ((m', ts'), s') →
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧
      (∀ t ∈ ts', PersProjTable t) ∧ TblListKept src s'.store.dropScratch ts ts' ∧
      Kept (Frontend.denoteProjTableList src ts)
        (Frontend.denoteProjTableList s'.store.dropScratch ts') := by
  intro ts
  induction ts with
  | nil =>
    intro m m' ts' s s' hs hm hrun
    simp only [promoteProjTables] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, hm, Ext.refl _, fun _ h => absurd h (by simp), .nil, Kept.some _⟩
  | cons t ts ih =>
    intro m m' ts' s s' hs hm hrun
    simp only [promoteProjTables] at hrun
    obtain ⟨⟨m1, t1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hn1, hd1⟩ := promoteProjTable_step hs hm h1
    obtain ⟨⟨m2, ts2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hm2, hx2, hp2, hn2, hd2⟩ := ih hs1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs2, hm2, hx1.trans hx2, ?_, .cons (hn1.mono hx2) hn2, ?_⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hp1
      · exact hp2 x hx
    · rw [denoteProjTableList_cons_opt, denoteProjTableList_cons_opt]
      exact Kept.opt2 List.cons (hd1.post fun _ h => denoteProjTable_ext h hx2) hd2

/-! ## The install/check seam -/

/-- con-leche: none — arena infrastructure; the record's promotion, run forwards over the
walks. -/
theorem promoteVG_step {m m' : PMemo} {fuel : Nat} {g g' : Arena.ValueGroup}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteVG m fuel g s = .ok ((m', g'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersVG g' ∧
      g'.kind = g.kind ∧
      Kept (Frontend.denoteCV src g.cv) (Frontend.denoteCV s'.store.dropScratch g'.cv) ∧
      Kept (denoteE src g.jv) (denoteE s'.store.dropScratch g'.jv) := by
  simp only [promoteVG] at hrun
  obtain ⟨⟨m1, c1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hm1, hx1, hp1, -, hd1⟩ := promoteCV_step hs hm h1
  obtain ⟨⟨m2, j2⟩, s2, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hs2, hm2, hx2, hp2, hd2⟩ := promoteE_step hs1 hm1 h3
  obtain ⟨hr, rfl⟩ := AM.pure_ok h4
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨hs2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩, rfl,
    hd1.post (fun _ h => denoteCV_ext h hx2), hd2⟩

/-! ## A persistent record reads the same at both ends of a `PExt` -/

/-- con-leche: none — arena infrastructure; a persistent record denotes in the far end of
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

/-- con-leche: none — arena infrastructure; a persistent record denotes in the far end of
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

/-- con-leche: none — arena infrastructure; a persistent record denotes in the far end of
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

/-- con-leche: none — arena infrastructure; a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteCV {a b : EStore} (hx : PExt a b) {cv : IConstantVal} (hp : PersCV cv)
    (x : ConstantVal) (h : Frontend.denoteCV a cv = some x) :
    Frontend.denoteCV b cv = some x := by
  rw [denoteCV_opt, opt3_eq_some_iff] at h ⊢
  obtain ⟨p, q, r, h1, h2, h3, rfl⟩ := h
  exact ⟨p, q, r, hx.lss.ls.ns _ p hp.name h1, hx.denoteNList _ hp.levelParams q h2,
    hx.expr _ r hp.type h3, rfl⟩

/-- con-leche: none — arena infrastructure; a persistent record denotes in the far end of
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

/-- con-leche: none — arena infrastructure; a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteRule {a b : EStore} (hx : PExt a b) {rl : IRecRule} (hp : PersRule rl)
    (x : RecRule) (h : Frontend.denoteRule a rl = some x) :
    Frontend.denoteRule b rl = some x := by
  rw [denoteRule_opt, opt3_eq_some_iff] at h ⊢
  obtain ⟨p, q, r, h1, h2, h3, rfl⟩ := h
  exact ⟨p, q, r, hx.lss.ls.ns _ p hp.ctor h1, hx.denoteFire hp.fire q h2,
    hx.expr _ r hp.rhs h3, rfl⟩

/-- con-leche: none — arena infrastructure; a persistent record denotes in the far end of
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

/-- con-leche: none — arena infrastructure; a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteCaps {a b : EStore} (hx : PExt a b) {c : IIndCaps} (hp : PersCaps c)
    (x : IndCaps) (h : Frontend.denoteCaps a c = some x) :
    Frontend.denoteCaps b c = some x := by
  rw [denoteCaps_opt, opt3_eq_some_iff] at h ⊢
  obtain ⟨p, q, r, h1, h2, h3, rfl⟩ := h
  exact ⟨p, q, r, hx.lss.ls.ns _ p hp.etaCtor h1, hx.denoteNList _ hp.all q h2,
    hx.denoteNList _ hp.ctors r h3, rfl⟩

/-- con-leche: none — arena infrastructure; a persistent record denotes in the far end of
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

/-- con-leche: none — arena infrastructure; a persistent block denotes in the far end of
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

/-- con-leche: none — arena infrastructure; a persistent record denotes in the far end of
a `PExt` what it denotes in the near one. -/
theorem PExt.denoteProjTable {a b : EStore} (hx : PExt a b) {t : IProjTable}
    (hp : PersProjTable t) (x : ProjTable) (h : Frontend.denoteProjTable a t = some x) :
    Frontend.denoteProjTable b t = some x := by
  rw [denoteProjTable_opt, opt2_eq_some_iff] at h ⊢
  obtain ⟨p, q, h1, h2, rfl⟩ := h
  rw [opt3_eq_some_iff] at h1 h2
  obtain ⟨p1, p2, p3, h11, h12, h13, rfl⟩ := h1
  obtain ⟨q1, q2, q3, h21, h22, h23, rfl⟩ := h2
  refine ⟨_, _, opt3_eq_some_iff.mpr ⟨p1, p2, p3, hx.lss.ls.ns _ p1 hp.structName h11,
    hx.denoteNList _ hp.levelParams p2 h12, hx.lss.ls.ns _ p3 hp.ctor h13, rfl⟩,
    opt3_eq_some_iff.mpr ⟨q1, q2, q3, hx.lss.ls.lvl _ q1 hp.structSort h21, ?_,
      hx.denoteLList _ hp.guards q3 h23, rfl⟩, rfl⟩
  rw [denoteEArray_map, Option.map_eq_some_iff] at h22 ⊢
  obtain ⟨l, hl, rfl⟩ := h22
  exact ⟨l, hx.denoteEList _ hp.bodies l hl, rfl⟩

/-- con-leche: none — arena infrastructure; a persistent table list denotes in the far
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
