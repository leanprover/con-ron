/-
# `ConRon.Bridge.Frontend.Olean.EmitWalk` — the emission's walk and the blocks' check

The twin's walk names constants where upstream's holds them (`SR`, a name that is stored, and its
constant read back) and takes fuel where upstream's is well founded.  Spent fuel is a `fail`, so a
twin's run that answers ran the same steps, and its result is upstream's `emitLoop` on the
denotations (`emitLoop_run`).  What upstream proves of `emitAll` then holds of the twin's records.
-/
module

public import ConRon.Bridge.Frontend.Olean.EmitRec

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Merged CEntry Emit Work entriesOf blockTys blockCtors
  blockRecs quotNames quotConstants recMapAdd recMapStep recMapOf emitLoop)
open ConLeche.Frontend (DeclRec)
open ConLeche.Frontend.Olean (CEntryF CKindF bind_some_left mkN)

/-- A stored name and its constant, against upstream's constant. -/
abbrev SR (st : EStore) (mg : Merged) : NIdx → ConLeche.Frontend.Olean.CEntry → Prop :=
  fun n z => denoteN st.ns n = some z.name ∧ ∃ x, mg.get n = some x ∧ denoteCEntry st x = some z

/-- What the walk's theorems read of the merge. -/
structure WalkCtx (st : EStore) (mg : Merged) (mgC : ConLeche.Frontend.Olean.Merged) : Prop where
  rel : MergedRel st mg mgC
  wf : NStoreWF st.ns
  names : ∀ (n : ConLeche.Name) (c : ConLeche.Frontend.Olean.CEntry), mgC.map[n]? = some c → c.name = n

theorem entriesOf_rel {st : EStore} {mg : Merged} :
    ∀ {ns : List NIdx} {zs : List ConLeche.Frontend.Olean.CEntry}, ListRel (SR st mg) ns zs →
      ListRel (CR st) (entriesOf mg ns) zs
  | _, _, .nil => .nil
  | n :: ns, z :: zs, .cons ⟨_, x, hg, hx⟩ hr => by
    have e : entriesOf mg (n :: ns) = x :: entriesOf mg ns := by
      simp [entriesOf, hg]
    rw [e]
    exact .cons hx (entriesOf_rel hr)

theorem blockTys_rel {st : EStore} {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    (hc : WalkCtx st mg mgC) :
    ∀ {all : List NIdx} {allC : List ConLeche.Name}, ListRel (NR st) all allC →
      ListRel (SR st mg) (blockTys mg all) (ConLeche.Frontend.Olean.blockTys mgC allC)
  | _, _, .nil => .nil
  | n :: ns, nC :: nsC, .cons hn hr => by
    have ih := blockTys_rel hc hr
    have hcn := hc.rel.contains hn
    simp only [blockTys, ConLeche.Frontend.Olean.blockTys, List.filter_cons, List.filterMap_cons] at ih ⊢
    cases hg : mgC.map[nC]? with
    | none =>
      have : mgC.map.contains nC = false := by
        simp [Std.HashMap.contains_eq_isSome_getElem?, hg]
      rw [this] at hcn
      simp only [hcn, Bool.false_eq_true, ↓reduceIte]
      exact ih
    | some z =>
      have hct : mgC.map.contains nC = true := by
        simp [Std.HashMap.contains_eq_isSome_getElem?, hg]
      rw [hct] at hcn
      simp only [hcn, ↓reduceIte]
      refine .cons ?_ ih
      have hzn := hc.names nC z hg
      refine ⟨by rw [hzn]; exact hn, ?_⟩
      cases hget : mg.get n with
      | none =>
        have := hc.rel.absent hn hget
        rw [hg] at this
        cases this
      | some x =>
        obtain ⟨z', hz', hd⟩ := hc.rel.got hn hget
        rw [hg] at hz'
        cases hz'
        exact ⟨x, rfl, hd⟩

/-- A kind's block members, against upstream's. -/
theorem kindCtors_rel {st : EStore} {k : CKindF NIdx EIdx}
    {zk : ConLeche.Frontend.Olean.CKind}
    (hk : k.mapM (denoteN st.ns) (denoteE st) = some zk) {np ni : Nat} {all cs : List NIdx} {nn : Nat}
    {ir iu irf : Bool} (h : k = .induct np ni all cs nn ir iu irf) :
    ∃ allC csC, zk = .induct np ni allC csC nn ir iu irf ∧ ListRel (NR st) all allC ∧
      ListRel (NR st) cs csC := by
  subst h
  simp only [CKindF.mapM] at hk
  obtain ⟨as, h1, hk⟩ := bind_some_left hk
  obtain ⟨cs', h2, hk⟩ := bind_some_left hk
  simp only [pure, Option.some.injEq] at hk
  exact ⟨as, cs', hk.symm, listRel_of_mapM h1, listRel_of_mapM h2⟩

theorem blockCtors_rel {st : EStore} {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    (hc : WalkCtx st mg mgC) :
    ∀ {tys : List NIdx} {zs : List ConLeche.Frontend.Olean.CEntry}, ListRel (SR st mg) tys zs →
      ListRel (SR st mg) (blockCtors mg tys) (ConLeche.Frontend.Olean.blockCtors mgC zs)
  | _, _, .nil => .nil
  | t :: ts, z :: zs, .cons ⟨_, x, hg, hx⟩ hr => by
    have ih := blockCtors_rel hc hr
    simp only [blockCtors, ConLeche.Frontend.Olean.blockCtors, List.flatMap_cons] at ih ⊢
    refine ListRel.append ?_ ih
    simp only [hg]
    obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hx
    have htag := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk).1
    split
    · rename_i np ni al cs nn ir iu irf hk1
      obtain ⟨allC, csC, hz, -, hcs⟩ := kindCtors_rel hk hk1
      simp only [hz]
      exact blockTys_rel hc hcs
    · rename_i hne
      split
      · rename_i np ni al cs nn ir iu irf hz
        rw [hz] at htag
        cases hk1 : x.c.kind <;> simp [hk1, CKindF.tag] at htag
        exact (hne _ _ _ _ _ _ _ _ hk1).elim
      · exact .nil

/-! ## The recursors' map -/

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:340-355 recMapOf — the recursors of a block's
members, read back. -/
@[expose] def RecRel (st : EStore) (m : Std.HashMap NIdx (Array NIdx))
    (mC : Std.HashMap ConLeche.Name (Array ConLeche.Name)) : Prop :=
  ∀ (n : NIdx) (nC : ConLeche.Name), denoteN st.ns n = some nC →
    ListRel (NR st) ((m[n]?).getD #[]).toList ((mC[nC]?).getD #[]).toList

theorem array_contains_rel {st : EStore} (hw : NStoreWF st.ns) {n : NIdx} {nC : ConLeche.Name}
    (hn : denoteN st.ns n = some nC) :
    ∀ {l : List NIdx} {ls : List ConLeche.Name}, ListRel (NR st) l ls → l.contains n = ls.contains nC
  | _, _, .nil => rfl
  | x :: xs, y :: ys, .cons hxy hr => by
    simp only [List.contains_cons]
    have e : (n == x) = (nC == y) := by
      cases hb : (n == x) with
      | true =>
        have : n = x := by simpa using hb
        subst this
        have : nC = y := Option.some.inj (hn.symm.trans hxy)
        simp [this]
      | false =>
        symm
        rw [beq_eq_false_iff_ne]
        intro hyy
        subst hyy
        have : n = x := denoteN_inj hw hn hxy
        simp [this] at hb
    rw [array_contains_rel hw hn hr]
    rw [e]

theorem recMapAdd_rel {st : EStore} (hw : NStoreWF st.ns) {n i : NIdx} {nC iC : ConLeche.Name}
    (hn : denoteN st.ns n = some nC) (hi : denoteN st.ns i = some iC)
    {m : Std.HashMap NIdx (Array NIdx)} {mC : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    (hr : RecRel st m mC) : RecRel st (recMapAdd n m i) (ConLeche.Frontend.Olean.recMapAdd nC mC iC) := by
  intro k kC hk
  by_cases e : i = k
  · subst e
    have hkk : kC = iC := Option.some.inj (hk.symm.trans hi)
    subst hkk
    have hbase := hr _ _ hk
    have ha : (recMapAdd n m i)[i]? = some (let a := (m[i]?).getD #[]
        if a.contains n then a else a.push n) := by
      simp only [recMapAdd, Std.HashMap.getElem?_alter_self]
      cases hmi : m[i]? <;> simp
    have hb : (ConLeche.Frontend.Olean.recMapAdd nC mC kC)[kC]? = some (let a := (mC[kC]?).getD #[]
        if a.contains nC then a else a.push nC) := by
      simp only [ConLeche.Frontend.Olean.recMapAdd, Std.HashMap.getElem?_alter_self]
      cases hmi : mC[kC]? <;> simp
    rw [ha, hb]
    simp only [Option.getD_some]
    have hcon := array_contains_rel hw hn hbase
    have ec : ((m[i]?).getD #[]).contains n = ((mC[kC]?).getD #[]).contains nC := by
      simpa using hcon
    rw [ec]
    split
    · exact hbase
    · simp only [Array.toList_push]
      exact ListRel.append hbase (.cons hn .nil)
  · have hne : kC ≠ iC := fun e' => e (denoteN_inj hw hi (e' ▸ hk))
    have ha : (recMapAdd n m i)[k]? = m[k]? := by
      simp [recMapAdd, Std.HashMap.getElem?_alter, e]
    have hb : (ConLeche.Frontend.Olean.recMapAdd nC mC iC)[kC]? = mC[kC]? := by
      simp [ConLeche.Frontend.Olean.recMapAdd, Std.HashMap.getElem?_alter, Ne.symm hne]
    rw [ha, hb]
    exact hr _ _ hk

theorem recMapAdds_rel {st : EStore} (hw : NStoreWF st.ns) {n : NIdx} {nC : ConLeche.Name}
    (hn : denoteN st.ns n = some nC) :
    ∀ {all : List NIdx} {allC : List ConLeche.Name}, ListRel (NR st) all allC →
      ∀ {m : Std.HashMap NIdx (Array NIdx)} {mC : Std.HashMap ConLeche.Name (Array ConLeche.Name)},
      RecRel st m mC → RecRel st (all.foldl (recMapAdd n) m)
        (allC.foldl (ConLeche.Frontend.Olean.recMapAdd nC) mC)
  | _, _, .nil, _, _, hr => hr
  | _, _, .cons hi ha, _, _, hr => recMapAdds_rel hw hn ha (recMapAdd_rel hw hn hi hr)

/-- A recursor's block, against upstream's. -/
theorem kindRec_rel {st : EStore} {k : CKindF NIdx EIdx} {zk : ConLeche.Frontend.Olean.CKind}
    (hk : k.mapM (denoteN st.ns) (denoteE st) = some zk) {all : List NIdx} {np ni nmo nmi : Nat}
    {rules : List (NIdx × Nat × EIdx)} {kk iu : Bool}
    (h : k = .recur all np ni nmo nmi rules kk iu) :
    ∃ allC rulesC, zk = .recur allC np ni nmo nmi rulesC kk iu ∧ ListRel (NR st) all allC := by
  subst h
  simp only [CKindF.mapM] at hk
  obtain ⟨as, h1, hk⟩ := bind_some_left hk
  obtain ⟨rs, -, hk⟩ := bind_some_left hk
  simp only [pure, Option.some.injEq] at hk
  exact ⟨as, rs, hk.symm, listRel_of_mapM h1⟩

theorem recMapStep_rel {st : EStore} {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    (hc : WalkCtx st mg mgC) {n : NIdx} {nC : ConLeche.Name} (hn : denoteN st.ns n = some nC)
    {m : Std.HashMap NIdx (Array NIdx)} {mC : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    (hr : RecRel st m mC) : RecRel st (recMapStep mg m n) (ConLeche.Frontend.Olean.recMapStep mgC mC nC) := by
  unfold recMapStep ConLeche.Frontend.Olean.recMapStep
  cases hget : mg.get n with
  | none =>
    simp only [hc.rel.absent hn hget, Option.map_none]
    exact hr
  | some x =>
    obtain ⟨z, hz, hd⟩ := hc.rel.got hn hget
    simp only [hz, Option.map_some]
    obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hd
    have htag := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk).1
    split
    · rename_i al np ni nmo nmi rules kk iu hk1
      obtain ⟨allC, rulesC, hzk, hal⟩ := kindRec_rel hk (by simpa using hk1)
      simp only [hzk]
      exact recMapAdds_rel hc.wf hn hal hr
    · rename_i hne
      split
      · rename_i al np ni nmo nmi rules kk iu hz'
        have hz'' : z.kind = .recur al np ni nmo nmi rules kk iu := by simpa using hz'
        rw [hz''] at htag
        cases hk1 : x.c.kind <;> simp [hk1, CKindF.tag] at htag
        exact (hne _ _ _ _ _ _ _ _ (by rw [hk1])).elim
      · exact hr

theorem recMapOf_rel {st : EStore} {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    (hc : WalkCtx st mg mgC) : RecRel st (recMapOf mg) (ConLeche.Frontend.Olean.recMapOf mgC) := by
  have key : ∀ {l : List NIdx} {ls : List ConLeche.Name}, ListRel (NR st) l ls →
      ∀ {m : Std.HashMap NIdx (Array NIdx)} {mC : Std.HashMap ConLeche.Name (Array ConLeche.Name)},
      RecRel st m mC → RecRel st (l.foldl (recMapStep mg) m)
        (ls.foldl (ConLeche.Frontend.Olean.recMapStep mgC) mC) := by
    intro l ls hl
    induction hl with
    | nil => intro _ _ hr; exact hr
    | cons hn _ ih => intro _ _ hr; exact ih (recMapStep_rel hc hn hr)
  unfold recMapOf ConLeche.Frontend.Olean.recMapOf
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact key hc.rel.order (fun _ _ _ => by simp; exact .nil)

end ConRon.Bridge.Frontend.Olean
