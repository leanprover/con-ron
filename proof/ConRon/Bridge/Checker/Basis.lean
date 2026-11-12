/-
# `ConRon.Bridge.Checker.Basis` — the pinned blocks and the axiom installs

Three things that share a shape: they compare a stream record against a
BUILD-TIME literal.

* `Arena/Basis.lean` — `BasisKind.decls` (the pinned blocks, interned), a pin
  at a stream's level-parameter names (`IConstantInfo.atLps`), the block's
  comparison with its pin (`pinListOk`), the name test (`basisNameHit`), what a
  quotient record stores (`quotAt`), the reserved names' check (`basisNamesOk`), and
  the quotient record's own tests (`quotPinHit`, `quotPredsOk`);
* `Arena/DeclCheck.lean` — the quotient record's check
  (`checkQuotRecord`) and the standard / compiler-trust
  axioms' environment shapes (`stdAxiomOk`, `trustCompilerOk`, `ofReduceAxOk`);
* `Arena/Basis.lean`'s `andPinOk`, the fold's `And` pin.

**The literals are con-leche's values, interned** (`Arena/Intern.lean`), so
each literal's bridge is one instance of the frontend tier's intern exactness —
`denoteCI st (internCI c) = some c`.

**The comparisons are `==` on handles where con-leche has `beqP`**, and each is
exact because the denotation is injective (`denoteCI_inj` and its siblings): a
handle record equality is the denoted records' equality.

**The renaming `atLps` is a walk**: `instantiateLevelParams` over handles
(`ExprOps.instLPFast_specS`) and the `.levels` firing mode's
`Level.subst`.  Both READ handles back, and the memoised readback writes the
three readback caches, so the frame of everything that renames is `RStep`: the
store grew, the scratch flag and the pin table did not move, the cache record
moved at the three readback tables only, and their invariants survived.
-/
module

import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Names
public import ConRon.Bridge.Frontend.Shared
import ConRon.Bridge.EnvDenote
import ConRon.Bridge.Specs
import ConRon.Bridge.SpecsL
import ConRon.Bridge.ExprOps.Owed
public import ConRon.Bridge.Checker.Decl
public import ConLeche.Kernel.Checker
public import ConRon.Arena.CheckDecl

public section

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The interned literals -/

/-- con-leche: ConLeche/Kernel/Basis.lean:38-44 BasisKind.decls — the pinned
block, interned, denotes con-leche's.

**Proof:** `Frontend.internCIList_sstep` at a fresh memo. -/
theorem BasisKind.decls_run {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s) (hrun : BasisKind.decls k s = .ok (r, s')) :
    Frontend.IStepS s s' ∧
      Frontend.denoteCIList s'.store r = some k.decls := by
  simp only [ConRon.Arena.BasisKind.decls, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, cis⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨hstep, hden, -⟩ :=
    Frontend.internCIList_sstep (ConLeche.BasisKind.decls k) hok
      (Frontend.EMemoOK.empty s.store) hgo
  exact ⟨hstep, hden⟩

/-! ## `Arena/Intern.lean`'s fresh-memo wrappers, in run form -/

/-- con-leche: none — `Arena.internCI` (a fresh memo) denotes its argument. -/
theorem internCI_fresh {c : ConstantInfo} {ci : IConstantInfo} {s s' : AState}
    (hok : StateOK s) (hrun : ConRon.Arena.internCI c s = .ok (ci, s')) :
    Frontend.IStepS s s' ∧ Frontend.denoteCI s'.store ci = some c := by
  simp only [ConRon.Arena.internCI] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, x⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨hstep, hden, -⟩ :=
    Frontend.internCI_sstep hok (Frontend.EMemoOK.empty s.store) hgo
  exact ⟨hstep, hden⟩

/-- con-leche: none — `Arena.internCV` (a fresh memo) denotes its argument. -/
theorem internCV_fresh {c : ConstantVal} {cv : IConstantVal} {s s' : AState}
    (hok : StateOK s) (hrun : ConRon.Arena.internCV c s = .ok (cv, s')) :
    Frontend.IStepS s s' ∧ Frontend.denoteCV s'.store cv = some c := by
  simp only [ConRon.Arena.internCV] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, x⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨hstep, hden, -⟩ :=
    Frontend.internCV_sstep hok (Frontend.EMemoOK.empty s.store) hgo
  exact ⟨hstep, hden⟩

/-! ## Recognising a pinned block: the names -/

/-- con-leche: none — **the block's name handles denote the block's names**. -/
theorem denoteCIList_names {st : EStore} :
    ∀ (cs : List IConstantInfo) (zs : List ConstantInfo),
      Frontend.denoteCIList st cs = some zs →
      Frontend.denoteNList st.ns (blockNames cs) = some (zs.map (·.name)) := by
  intro cs
  induction cs with
  | nil =>
    intro zs h
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro zs h
    obtain ⟨x, xs, hx, hxs, rfl⟩ := denoteCIList_cons h
    have hn := denoteCI_name hx
    have hih := ih xs hxs
    simp only [ConRon.Arena.blockNames] at hih
    simp only [ConRon.Arena.blockNames, List.map_cons, Frontend.denoteNList,
      hn, hih]

/-- con-leche: ConLeche/Kernel/Basis.lean:133-136 basisNameHit — the search,
kind by kind: the first kind whose members' NAMES are the block's decides.  A
name-list comparison is a handle-list comparison (`denoteNList_inj`). -/
theorem basisNameHitGo_run {block : List IConstantInfo} {b : List ConstantInfo} :
    ∀ (ks : List BasisKind) {r : Option BasisKind} {s s' : AState},
      StateOK s →
      Frontend.denoteCIList s.store block = some b →
      basisNameHitGo block ks s = .ok (r, s') →
      Frontend.IStepS s s' ∧
        r = ks.find? fun k =>
              (ConLeche.BasisKind.decls k).map (·.name) == b.map (·.name) := by
  intro ks
  induction ks with
  | nil =>
    intro r s s' hok _ hrun
    simp only [ConRon.Arena.basisNameHitGo] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨Frontend.IStepS.refl hok, by simp⟩
  | cons k ks ih =>
    intro r s s' hok hb hrun
    simp only [ConRon.Arena.basisNameHitGo] at hrun
    obtain ⟨pinned, s₁, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hdp⟩ := BasisKind.decls_run hok g1
    have hb1 := denoteCIList_mono hs1.ext _ _ hb
    have hnA : Frontend.denoteNList s₁.store.ns (blockNames pinned)
        = some ((ConLeche.BasisKind.decls k).map (·.name)) :=
      denoteCIList_names pinned _ hdp
    have hblock : Frontend.denoteNList s₁.store.ns (blockNames block)
          = some (b.map (·.name)) :=
      denoteCIList_names block _ hb1
    rcases AM.ite_ok k1 with ⟨hy, k2⟩ | ⟨hn, k2⟩
    · -- the handle lists agree: this kind decides
      have hbn : blockNames pinned = blockNames block := by simpa using hy
      have hsame : ((ConLeche.BasisKind.decls k).map (·.name) == b.map (·.name))
            = true := by
        have h1 := hblock
        rw [← hbn, hnA] at h1
        simpa using Option.some.inj h1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      exact ⟨hs1, by simp [hsame]⟩
    · -- the handle lists differ, and so do the names: on to the next kind
      have hbn : blockNames pinned ≠ blockNames block := by simpa using hn
      have hP : ((ConLeche.BasisKind.decls k).map (·.name)
          == b.map (·.name)) = false := by
        cases hpk : ((ConLeche.BasisKind.decls k).map (·.name)
            == b.map (·.name)) with
        | false => rfl
        | true =>
          refine absurd (denoteNList_inj hs1.ok.wf _ _ _ hnA ?_) hbn
          have h1 := hblock
          rw [(by simpa using hpk : (ConLeche.BasisKind.decls k).map (·.name)
            = b.map (·.name))]
          exact h1
      obtain ⟨hs2, he⟩ := ih hs1.ok hb1 k2
      exact ⟨hs1.trans hs2, by rw [he]; simp [hP]⟩

/-- con-leche: ConLeche/Kernel/Basis.lean:133-136 basisNameHit — **the pinned
block a record declares**, by its members' names: the arena's answer is
con-leche's at the denoted block.  The run only interns the pinned blocks, so
it is a scratch-agnostic step (`Frontend.IStepS`): it runs inside a job and on
the driver's state alike, and leaves the scratch flag, the memos, the caches and
the pin table where it found them. -/
theorem basisNameHit_run {block : List IConstantInfo} {b : List ConstantInfo}
    {r : Option BasisKind} {s s' : AState} (hok : StateOK s)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hrun : basisNameHit block s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      s'.caches = s.caches ∧ s'.memos = s.memos ∧
      s'.store.scratchOn = s.store.scratchOn ∧ r = ConLeche.basisNameHit b := by
  obtain ⟨h1, h2⟩ := basisNameHitGo_run _ hok hb hrun
  exact ⟨h1.ok, h1.ext, h1.pins, h1.caches, h1.memos, h1.scratch, by rw [h2]; rfl⟩

/-! ## Injectivity: a handle equality is a value equality

con-leche compares records with its pointer-first `beqP`
(`ConLeche/Kernel/Canon.lean`), which is equality; the twin compares handle
records with the derived `==`.  The readbacks are injective, so the two
agree at any pair of denoting records. -/

/-- con-leche: none — a handle comparison IS the comparison of the two
denotations, at any readback that is injective. -/
theorem beq_of_denote_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β]
    [LawfulBEq β] {d : α → Option β}
    (hinj : ∀ {i j : α} {x : β}, d i = some x → d j = some x → i = j)
    {i j : α} {x y : β} (hi : d i = some x) (hj : d j = some y) :
    (i == j) = (x == y) := by
  cases hb : (x == y) with
  | true =>
    obtain rfl := eq_of_beq hb
    exact beq_iff_eq.mpr (hinj hi hj)
  | false =>
    cases hb' : (i == j) with
    | false => rfl
    | true =>
      obtain rfl := eq_of_beq hb'
      rw [hi] at hj
      obtain rfl := Option.some.inj hj
      simp at hb

/-- con-leche: ConLeche/Kernel/Canon.lean:305-307 ConstantVal.beqP — it is
equality. -/
theorem ConstantVal.beqP_eq (a b : ConstantVal) : a.beqP b = (a == b) := by
  cases h : a.beqP b with
  | true => rw [ConstantVal.eq_of_beqP h]; simp
  | false =>
    symm; cases h' : (a == b) with
    | false => rfl
    | true =>
      obtain rfl := eq_of_beq h'
      simp [ConstantVal.beqP] at h

/-- con-leche: ConLeche/Kernel/Canon.lean:338-347 ConstantInfo.beqP — it is
equality. -/
theorem ConstantInfo.beqP_eq (a b : ConstantInfo) : a.beqP b = (a == b) := by
  cases h : a.beqP b with
  | true => rw [ConstantInfo.eq_of_beqP h]; simp
  | false =>
    symm; cases h' : (a == b) with
    | false => rfl
    | true =>
      obtain rfl := eq_of_beq h'
      have hr : ∀ r : RecRule, r.beqP r = true := by
        intro r; simp [RecRule.beqP]
        cases r.fire <;> simp [RecRuleFire.beqP]
      have hl : ∀ rs : List RecRule, ConLeche.listBeqBy RecRule.beqP rs rs = true := by
        intro rs; induction rs with
        | nil => rfl
        | cons x xs ih => simp [ConLeche.listBeqBy, hr x, ih]
      cases a <;> simp_all [ConLeche.ConstantInfo.beqP, ConLeche.ConstantVal.beqP]

/-- con-leche: none — `Frontend.denoteCV` is injective. -/
theorem denoteCV_inj {st : EStore} (hwf : StoreWF st) {v w : IConstantVal}
    {c : ConstantVal} (hv : Frontend.denoteCV st v = some c)
    (hw : Frontend.denoteCV st w = some c) : v = w := by
  have hwf' := hwf
  obtain ⟨rk, hrk⟩ := hwf'
  obtain ⟨h1, h2, h3⟩ := denoteCV_inv hv
  obtain ⟨g1, g2, g3⟩ := denoteCV_inv hw
  cases v; cases w
  simp only at h1 h2 h3 g1 g2 g3
  rw [denoteN_inj hrk.nsWF h1 g1, denoteNList_inj hwf _ _ _ h2 g2,
    denoteE_inj hwf h3 g3]

/-- con-leche: none — `Frontend.denoteCaps` is injective. -/
theorem denoteCaps_inj {st : EStore} (hwf : StoreWF st) {cap cap' : IIndCaps}
    {d : IndCaps} (hc : Frontend.denoteCaps st cap = some d)
    (hc' : Frontend.denoteCaps st cap' = some d) : cap = cap' := by
  have hwf' := hwf
  obtain ⟨rk, hrk⟩ := hwf'
  simp only [Frontend.denoteCaps] at hc hc'
  · cases ha : Frontend.denoteNList st.ns cap.all with
      | none => rw [ha] at hc; simp at hc
      | some al =>
      cases ha' : Frontend.denoteNList st.ns cap'.all with
      | none => rw [ha'] at hc'; simp at hc'
      | some al' =>
      cases hk : Frontend.denoteNList st.ns cap.ctors with
      | none => rw [ha, hk] at hc; simp at hc
      | some ks =>
      cases hk' : Frontend.denoteNList st.ns cap'.ctors with
      | none => rw [ha', hk'] at hc'; simp at hc'
      | some ks' =>
      rw [ha, hk] at hc; rw [ha', hk'] at hc'
      rw [← hc'] at hc
      simp only [Option.some.injEq, IndCaps.mk.injEq] at hc
      obtain ⟨e1, rfl, e3, e4, rfl, e6⟩ := hc
      have hA := denoteNList_inj hwf _ _ _ ha ha'
      have hK := denoteNList_inj hwf _ _ _ hk hk'
      cases cap; cases cap'
      simp_all

/-- con-leche: none — `Frontend.denoteRule` is injective. -/
theorem denoteRule_inj {st : EStore} (hwf : StoreWF st) {r r' : IRecRule}
    {R : RecRule} (h : Frontend.denoteRule st r = some R)
    (h' : Frontend.denoteRule st r' = some R) : r = r' := by
  have hwf' := hwf
  obtain ⟨rk, hrk⟩ := hwf'
  obtain ⟨c1, f1, e1, n1⟩ := denoteRule_inv h
  obtain ⟨c2, f2, e2, n2⟩ := denoteRule_inv h'
  cases r; cases r'
  simp only at c1 f1 e1 n1 c2 f2 e2 n2
  rw [denoteN_inj hrk.nsWF c1 c2, denoteFire_inj hwf f1 f2, denoteE_inj hwf e1 e2,
    n1, n2]

/-- con-leche: none — `Frontend.denoteRules` is injective. -/
theorem denoteRules_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (rs rs' : List IRecRule) (Rs : List RecRule),
      Frontend.denoteRules st rs = some Rs →
      Frontend.denoteRules st rs' = some Rs → rs = rs' := by
  intro rs
  induction rs with
  | nil =>
    intro rs' Rs h h'
    simp only [Frontend.denoteRules, Option.some.injEq] at h
    subst h
    cases rs' with
    | nil => rfl
    | cons a as =>
      obtain ⟨x, xs, -, -, hx⟩ := denoteRules_cons h'
      cases hx
  | cons a as ih =>
    intro rs' Rs h h'
    obtain ⟨x, xs, hx, hxs, rfl⟩ := denoteRules_cons h
    cases rs' with
    | nil => simp [Frontend.denoteRules] at h'
    | cons b bs =>
      obtain ⟨y, ys, hy, hys, he⟩ := denoteRules_cons h'
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [denoteRule_inj hwf hx hy, ih bs xs hxs hys]

/-- con-leche: none — **`Frontend.denoteCI` is injective**: a handle record
equality is the denoted records' equality. -/
theorem denoteCI_inj {st : EStore} (hwf : StoreWF st) {ci ci' : IConstantInfo}
    {c : ConstantInfo} (h : Frontend.denoteCI st ci = some c)
    (h' : Frontend.denoteCI st ci' = some c) : ci = ci' := by
  cases ci with
  | axiomInfo v =>
    obtain ⟨cv, rfl, hv⟩ := denoteCI_axiom_inv h
    cases ci' with
    | axiomInfo w =>
      obtain ⟨cw, he, hw⟩ := denoteCI_axiom_inv h'
      cases he; rw [denoteCV_inj hwf hv hw]
    | defnInfo w _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_defn_inv h'; cases he
    | thmInfo w => obtain ⟨_, he, _⟩ := denoteCI_thm_inv h'; cases he
    | indInfo w _ => obtain ⟨_, _, he, _⟩ := denoteCI_ind_inv h'; cases he
    | ctorInfo w _ _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv h'; cases he
    | recInfo w _ _ _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_rec_inv h'; cases he
  | defnInfo v e hh =>
    obtain ⟨cv, x, rfl, hv, hx⟩ := denoteCI_defn_inv h
    cases ci' with
    | defnInfo w e' hh' =>
      obtain ⟨cw, x', he, hw, hx'⟩ := denoteCI_defn_inv h'
      cases he; rw [denoteCV_inj hwf hv hw, denoteE_inj hwf hx hx']
    | axiomInfo w => obtain ⟨_, he, _⟩ := denoteCI_axiom_inv h'; cases he
    | thmInfo w => obtain ⟨_, he, _⟩ := denoteCI_thm_inv h'; cases he
    | indInfo w _ => obtain ⟨_, _, he, _⟩ := denoteCI_ind_inv h'; cases he
    | ctorInfo w _ _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv h'; cases he
    | recInfo w _ _ _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_rec_inv h'; cases he
  | thmInfo v =>
    obtain ⟨cv, rfl, hv⟩ := denoteCI_thm_inv h
    cases ci' with
    | thmInfo w =>
      obtain ⟨cw, he, hw⟩ := denoteCI_thm_inv h'
      cases he; rw [denoteCV_inj hwf hv hw]
    | axiomInfo w => obtain ⟨_, he, _⟩ := denoteCI_axiom_inv h'; cases he
    | defnInfo w _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_defn_inv h'; cases he
    | indInfo w _ => obtain ⟨_, _, he, _⟩ := denoteCI_ind_inv h'; cases he
    | ctorInfo w _ _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv h'; cases he
    | recInfo w _ _ _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_rec_inv h'; cases he
  | indInfo v cap =>
    obtain ⟨cv, d, rfl, hv, hd⟩ := denoteCI_ind_inv h
    cases ci' with
    | indInfo w cap' =>
      obtain ⟨cw, d', he, hw, hd'⟩ := denoteCI_ind_inv h'
      cases he; rw [denoteCV_inj hwf hv hw, denoteCaps_inj hwf hd hd']
    | axiomInfo w => obtain ⟨_, he, _⟩ := denoteCI_axiom_inv h'; cases he
    | defnInfo w _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_defn_inv h'; cases he
    | thmInfo w => obtain ⟨_, he, _⟩ := denoteCI_thm_inv h'; cases he
    | ctorInfo w _ _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv h'; cases he
    | recInfo w _ _ _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_rec_inv h'; cases he
  | ctorInfo v nP nF T =>
    have hT := denoteCI_ctor_induct h
    obtain ⟨cv, rfl, hv⟩ := denoteCI_ctor_inv h
    cases ci' with
    | ctorInfo w nP' nF' T' =>
      have hT' := denoteCI_ctor_induct h'
      obtain ⟨cw, he, hw⟩ := denoteCI_ctor_inv h'
      simp only [ConstantInfo.ctorInfo.injEq] at he
      obtain ⟨rfl, rfl, rfl, hTT⟩ := he
      rw [← hTT] at hT'
      rw [denoteCV_inj hwf hv hw, denoteN_injS hwf hT hT']
    | axiomInfo w => obtain ⟨_, he, _⟩ := denoteCI_axiom_inv h'; cases he
    | defnInfo w _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_defn_inv h'; cases he
    | thmInfo w => obtain ⟨_, he, _⟩ := denoteCI_thm_inv h'; cases he
    | indInfo w _ => obtain ⟨_, _, he, _⟩ := denoteCI_ind_inv h'; cases he
    | recInfo w _ _ _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_rec_inv h'; cases he
  | recInfo v mI rP k rs =>
    obtain ⟨cv, Rs, rfl, hv, hr⟩ := denoteCI_rec_inv h
    cases ci' with
    | recInfo w mI' rP' k' rs' =>
      obtain ⟨cw, Rs', he, hw, hr'⟩ := denoteCI_rec_inv h'
      cases he; rw [denoteCV_inj hwf hv hw, denoteRules_inj hwf _ _ _ hr hr']
    | axiomInfo w => obtain ⟨_, he, _⟩ := denoteCI_axiom_inv h'; cases he
    | defnInfo w _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_defn_inv h'; cases he
    | thmInfo w => obtain ⟨_, he, _⟩ := denoteCI_thm_inv h'; cases he
    | indInfo w _ => obtain ⟨_, _, he, _⟩ := denoteCI_ind_inv h'; cases he
    | ctorInfo w _ _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv h'; cases he

/-! ## The renaming's frame

`atLps` reads handles back (`readNamesM`, `readLevelM`, `instLPFast`'s two
readbacks), and the memoised readback WRITES the three readback caches.  So the
frame of every run below is `RStep`: the store grew, the scratch flag and the
pin table did not move, the cache record moved at the three readback tables
only (one record equation), and the three readback invariants hold afterwards.
`ReadOK` is those three invariants, which `CheckOK` carries
(`CheckOK.readOK`) and `RStep.checkOK` hands back. -/

/-- con-leche: none — the three readback caches are sound. -/
structure ReadOK (s : AState) : Prop where
  readN : ReadNCacheOK s.caches.readNC s.store
  readL : ReadLCacheOK s.caches.readLC s.store
  readLs : ReadLsCacheOK s.caches.readLsC s.store

/-- con-leche: none — `CheckOK` carries the three readback invariants. -/
theorem CheckOK.readOK {eager : Bool} {env : Env} {fe : IFEnv} {s : AState}
    (h : CheckOK eager env fe s) : ReadOK s :=
  ⟨h.caches.readN, h.caches.readL, h.caches.readLs⟩

/-- con-leche: none — **the frame of a run that renames level parameters**. -/
structure RStep (s s' : AState) : Prop where
  ok : StateOK s'
  ext : Ext s.store s'.store
  scratch : s'.store.scratchOn = s.store.scratchOn
  pins : s'.pins = s.pins
  caches : s'.caches = { s.caches with
    readLC := s'.caches.readLC, readNC := s'.caches.readNC,
    readLsC := s'.caches.readLsC }
  read : ReadOK s'

theorem RStep.refl {s : AState} (hok : StateOK s) (hr : ReadOK s) : RStep s s :=
  ⟨hok, Ext.refl _, rfl, rfl, rfl, hr⟩

theorem RStep.trans {a b c : AState} (h₁ : RStep a b) (h₂ : RStep b c) :
    RStep a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, by rw [h₂.scratch, h₁.scratch],
    by rw [h₂.pins, h₁.pins], by rw [h₂.caches, h₁.caches], h₂.read⟩

/-- con-leche: none — an intern step is a renaming step. -/
theorem RStep.of_istep {s s' : AState} (h : Frontend.IStepS s s') (hr : ReadOK s) :
    RStep s s' :=
  ⟨h.ok, h.ext, h.scratch, h.pins, by rw [h.caches],
    ⟨by rw [h.caches]; exact hr.readN.mono h.ext, by rw [h.caches]; exact hr.readL.mono h.ext,
      by rw [h.caches]; exact hr.readLs.mono h.ext⟩⟩

/-- con-leche: none — a renaming step is a `CacheFrame` (the level-verdict
table did not move). -/
theorem RStep.frame {s s' : AState} (h : RStep s s') : CacheFrame s s' where
  caches := by rw [h.caches]
  readL := fun _ => h.read.readL
  lvlEq := fun _ hl => by rw [h.caches]; exact hl.mono h.ext
  readN := fun _ => h.read.readN
  readLs := fun _ => h.read.readLs

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — `CheckOK` past a renaming
step. -/
theorem RStep.checkOK {eager : Bool} {env : Env} {fe : IFEnv} {s s' : AState}
    (h : RStep s s') (hc : CheckOK eager env fe s) : CheckOK eager env fe s' where
  state := h.ok
  caches := hc.caches.monoF h.ext h.frame
  pins := hc.pins.mono h.ext h.pins
  ienv := hc.ienv.mono h.ext

/-! ## The readers and interns `atLps` runs, in run form -/

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the memoised
`readNames`, as a renaming step. -/
theorem readNamesM_run {hs : List NIdx} {xs : List ConLeche.Name} {s s' : AState}
    (hok : StateOK s) (hr : ReadOK s) (hrun : readNamesM hs s = .ok (xs, s')) :
    RStep s s' ∧ Frontend.denoteNList s.store.ns hs = some xs := by
  obtain ⟨hst, -, hp, hc, hd, hn⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (readNamesM_spec s hs hr.readN)
  refine ⟨⟨⟨hst ▸ hok.wf⟩, hst ▸ Ext.refl _, by rw [hst], hp, by rw [hc], ?_⟩, hd⟩
  exact ⟨hn, by rw [hc, hst]; exact hr.readL, by rw [hc, hst]; exact hr.readLs⟩

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — the memoised level
readback, as a renaming step. -/
theorem readLevelM_run {h : LIdx} {u : Level} {s s' : AState}
    (hok : StateOK s) (hr : ReadOK s) (hrun : readLevelM h s = .ok (u, s')) :
    RStep s s' ∧ denoteL s.store.ls h = some u := by
  obtain ⟨hst, -, hp, hc, hd, hl⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (readLevelM_spec s h hr.readL)
  refine ⟨⟨⟨hst ▸ hok.wf⟩, hst ▸ Ext.refl _, by rw [hst], hp, by rw [hc], ?_⟩, hd⟩
  exact ⟨by rw [hc, hst]; exact hr.readN, hl, by rw [hc, hst]; exact hr.readLs⟩

/-- con-leche: none — `internLevel`, as an intern step. -/
theorem internLevel_run {u : Level} {h : LIdx} {s s' : AState} (hok : StateOK s)
    (hrun : internLevel u s = .ok (h, s')) :
    Frontend.IStepS s s' ∧ denoteL s'.store.ls h = some u := by
  obtain ⟨q1, q2, -, -, q5, q6, q7, q8, q9⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLevel_spec s u hok.wf)
  exact ⟨⟨⟨q1⟩, q2, q5, q6, q7, q8⟩, q9⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2718-2722 Expr.instLPFast —
`instantiateLevelParams` over handles, as a renaming step
(`ExprOps.instLPFast_specS`). -/
theorem instLPFast_run {fuel : Nat} {ks : List NIdx} {us : LsIdx} {e r : EIdx}
    {ksv : List ConLeche.Name} {usv : List Level} {x : Expr} {s s' : AState}
    (hok : StateOK s) (hr : ReadOK s)
    (hks : Frontend.denoteNList s.store.ns ks = some ksv)
    (hus : denoteLs s.store.lss us = some usv) (he : denoteE s.store e = some x)
    (hrun : instLPFast fuel ks us e s = .ok (r, s')) :
    RStep s s' ∧ denoteE s'.store r = some (x.instantiateLevelParams ksv usv) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun
      (ExprOps.instLPFast_specS fuel s ks us e ksv usv hok hr.readN hr.readL hr.readLs
        hks hus (by rw [he]; rfl))
  exact ⟨⟨h1, h2, h3, h8, h7, ⟨h6, h4, h5⟩⟩, h9 x he⟩

/-- con-leche: none — a level list that denotes decodes (`intern`'s children
precondition). -/
theorem denoteLList_viewOK {st : EStore} :
    ∀ (v : List LIdx) (L : List Level), denoteLList st.ls v = some L →
      st.lss.ViewOK v := by
  intro v
  induction v with
  | nil => intro L _ c hc; simp at hc
  | cons a as ih =>
    intro L h c hc
    obtain ⟨l, L', ha, has, -⟩ := denoteLList_cons_inv h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact lview_isSome_of_denote (show denoteL st.lss.ls c = some l from ha)
    · exact ih L' has c hc

/-- con-leche: none — `paramLevels`' list, by list induction. -/
theorem paramLevelsGo_run : ∀ (lps : List NIdx) {psv : List ConLeche.Name}
    {s s' : AState} {r : List LIdx}, StateOK s →
    Frontend.denoteNList s.store.ns lps = some psv →
    Arena.paramLevels.go lps s = .ok (r, s') →
    Frontend.IStepS s s' ∧ denoteLList s'.store.ls r = some (psv.map Level.param) := by
  intro lps
  induction lps with
  | nil =>
    intro psv s s' r hok hd hrun
    simp only [Frontend.denoteNList, Option.some.injEq] at hd
    subst hd
    simp only [Arena.paramLevels.go] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨Frontend.IStepS.refl hok, rfl⟩
  | cons n ns ih =>
    intro psv s s' r hok hd hrun
    obtain ⟨x, xs, hn, hns, rfl⟩ := denoteNList_cons_inv hd
    simp only [Arena.paramLevels.go] at hrun
    obtain ⟨u, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rest, s₂, h3, h4⟩ := AM.bind_ok h2
    have hv : s.store.ls.ViewOK (.param n) :=
      ⟨by simp [LNodeView.lchildren], by
        intro c hc
        simp only [LNodeView.nchildren, List.mem_singleton] at hc
        subst hc; exact nview_isSome_of_denote hn⟩
    obtain ⟨q1, q2, -, -, q5, q6, q7, q8, -, q10⟩ :=
      AM.of_run (P := fun t => t = s) rfl h1 (internLNode_spec s _ hok.wf hv)
    have hs1 : Frontend.IStepS s s₁ := ⟨⟨q1⟩, q2, q5, q6, q7, q8⟩
    have hu : denoteL s₁.store.ls u = some (.param x) := by
      rw [q10]
      simp [denoteLView, show denoteN s₁.store.ls.ns n = some x from denoteN_ext hn hs1.ext]
    obtain ⟨hs2, hrest⟩ := ih hs1.ok (denoteNListE_ext hs1.ext _ _ hns) h3
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
    refine ⟨hs1.trans hs2, ?_⟩
    simp only [denoteLList, opt2, denoteL_ext hu hs2.ext, hrest, List.map_cons]

/-- con-leche: none — `lps.map .param`, interned: the universe arguments a
pin carries at the stream's names. -/
theorem paramLevels_run {ps : List NIdx} {psv : List ConLeche.Name} {us : LsIdx}
    {s s' : AState} (hok : StateOK s) (hd : Frontend.denoteNList s.store.ns ps = some psv)
    (hrun : Arena.paramLevels ps s = .ok (us, s')) :
    Frontend.IStepS s s' ∧ denoteLs s'.store.lss us = some (psv.map Level.param) := by
  simp only [Arena.paramLevels] at hrun
  obtain ⟨ls, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hls⟩ := paramLevelsGo_run ps hok hd h1
  obtain ⟨q1, q2, -, -, q5, q6, q7, q8, -, q10⟩ :=
    AM.of_run (P := fun t => t = s₁) rfl h2
      (internLsNode_spec s₁ ls hs1.ok.wf (denoteLList_viewOK ls _ hls))
  refine ⟨hs1.trans ⟨⟨q1⟩, q2, q5, q6, q7, q8⟩, ?_⟩
  rw [q10]
  exact denoteLList_ext q2.lss.ls _ _ hls

/-- con-leche: ConLeche/Kernel/Basis.lean:57-60 RecRuleFire.atLps — the
`.levels` comparands, `lvls.map (Level.subst lps us)`. -/
theorem substLevelsAt_run (ks : List ConLeche.Name) (vs : List Level) :
    ∀ (lvls : List LIdx) {L : List Level} {s s' : AState} {r : List LIdx},
      StateOK s → ReadOK s → denoteLList s.store.ls lvls = some L →
      Arena.substLevelsAt ks vs lvls s = .ok (r, s') →
      RStep s s' ∧ denoteLList s'.store.ls r = some (L.map (Level.subst ks vs)) := by
  intro lvls
  induction lvls with
  | nil =>
    intro L s s' r hok hr hL hrun
    simp only [denoteLList, Option.some.injEq] at hL
    subst hL
    simp only [Arena.substLevelsAt] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨RStep.refl hok hr, rfl⟩
  | cons u us ih =>
    intro L s s' r hok hr hL hrun
    obtain ⟨l, L', hu, hus, rfl⟩ := denoteLList_cons_inv hL
    simp only [Arena.substLevelsAt] at hrun
    obtain ⟨l0, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hl0⟩ := readLevelM_run hok hr h1
    rw [hu] at hl0
    obtain rfl := (Option.some.inj hl0).symm
    obtain ⟨hh, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hhd⟩ := internLevel_run hs1.ok h3
    have hs2' := RStep.of_istep hs2 hs1.read
    obtain ⟨rest, s₃, h5, h6⟩ := AM.bind_ok h4
    obtain ⟨hs3, hrest⟩ := ih hs2.ok hs2'.read
      (denoteLListE_ext (hs1.ext.trans hs2.ext) _ _ hus) h5
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
    refine ⟨(hs1.trans hs2').trans hs3, ?_⟩
    simp only [denoteLList, opt2, denoteL_ext hhd hs3.ext, hrest, List.map_cons]

/-! ## A pin at a stream's level-parameter names -/

/-- con-leche: ConLeche/Kernel/Basis.lean:53-55 ConstantVal.atLps — a
constant's common data at other level-parameter names. -/
theorem IConstantVal.atLps_run {cv r : IConstantVal} {ps : List NIdx}
    {c : ConstantVal} {psv : List ConLeche.Name} {s s' : AState}
    (hok : StateOK s) (hr : ReadOK s) (hc : Frontend.denoteCV s.store cv = some c)
    (hps : Frontend.denoteNList s.store.ns ps = some psv)
    (hrun : IConstantVal.atLps cv ps s = .ok (r, s')) :
    RStep s s' ∧ Frontend.denoteCV s'.store r = some (c.atLps psv) := by
  obtain ⟨hn, hl, ht⟩ := denoteCV_inv hc
  simp only [IConstantVal.atLps] at hrun
  obtain ⟨us, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hus⟩ := paramLevels_run hok hps h1
  have hs1' := RStep.of_istep hs1 hr
  obtain ⟨ty, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hs2, hty⟩ := instLPFast_run hs1.ok hs1'.read
    (denoteNListE_ext hs1.ext _ _ hl) hus (denote_ext ht hs1.ext) h3
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
  refine ⟨hs1'.trans hs2, ?_⟩
  have hx := hs1.ext.trans hs2.ext
  simp only [Frontend.denoteCV, denoteN_ext hn hx, denoteNListE_ext hx _ _ hps, hty,
    ConLeche.ConstantVal.atLps]

/-- con-leche: ConLeche/Kernel/Basis.lean:57-60 RecRuleFire.atLps — a firing
mode at other level-parameter names. -/
theorem IRecRuleFire.atLps_run {lps : List ConLeche.Name} {us : List Level}
    {f r : IRecRuleFire} {F : RecRuleFire} {s s' : AState}
    (hok : StateOK s) (hr : ReadOK s) (hf : Frontend.denoteFire s.store f = some F)
    (hrun : IRecRuleFire.atLps lps us f s = .ok (r, s')) :
    RStep s s' ∧ Frontend.denoteFire s'.store r = some (F.atLps lps us) := by
  cases f with
  | plain =>
    simp only [IRecRuleFire.atLps] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    simp only [Frontend.denoteFire, Option.some.injEq] at hf
    subst hf
    exact ⟨RStep.refl hok hr, rfl⟩
  | nested l p =>
    simp only [IRecRuleFire.atLps] at hrun
    obtain ⟨rfl, hs⟩ := AM.pure_ok hrun
    rw [hs]
    refine ⟨RStep.refl hok hr, ?_⟩
    simp only [Frontend.denoteFire] at hf
    cases hl : denoteLList s.store.ls l with
    | none => rw [hl] at hf; simp at hf
    | some ls =>
      cases hp : Frontend.denoteEList s.store p with
      | none => rw [hl, hp] at hf; simp at hf
      | some ps =>
        rw [hl, hp] at hf
        obtain rfl := (Option.some.inj hf).symm
        simp only [Frontend.denoteFire, hl, hp, ConLeche.RecRuleFire.atLps]
  | levels l =>
    simp only [IRecRuleFire.atLps] at hrun
    obtain ⟨l2, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
    obtain ⟨L, hL, rfl⟩ := hf
    obtain ⟨hs1, hl2⟩ := substLevelsAt_run lps us l hok hr hL h1
    refine ⟨hs1, ?_⟩
    simp only [Frontend.denoteFire, hl2, Option.map_some, ConLeche.RecRuleFire.atLps]

/-- con-leche: ConLeche/Kernel/Basis.lean:62-78 ConstantInfo.atLps — the
`.recInfo` arm's `rules.map`. -/
theorem rulesAtLps_run (lpsH : List NIdx) (us : LsIdx) (lpsT : List ConLeche.Name)
    (usT : List Level) :
    ∀ (rules : List IRecRule) {Rs : List RecRule} {s s' : AState} {r : List IRecRule},
      StateOK s → ReadOK s → Frontend.denoteNList s.store.ns lpsH = some lpsT →
      denoteLs s.store.lss us = some usT →
      Frontend.denoteRules s.store rules = some Rs →
      rulesAtLps lpsH us lpsT usT rules s = .ok (r, s') →
      RStep s s' ∧ Frontend.denoteRules s'.store r = some (Rs.map fun rl =>
        { rl with
          rhs := rl.rhs.instantiateLevelParams lpsT usT
          fire := rl.fire.atLps lpsT usT }) := by
  intro rules
  induction rules with
  | nil =>
    intro Rs s s' r hok hr _ _ hRs hrun
    simp only [Frontend.denoteRules, Option.some.injEq] at hRs
    subst hRs
    simp only [rulesAtLps] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨RStep.refl hok hr, rfl⟩
  | cons rl rls ih =>
    intro Rs s s' r hok hr hl hu hRs hrun
    obtain ⟨x, xs, hx, hxs, rfl⟩ := denoteRules_cons hRs
    obtain ⟨hc, hf, hrhs, hnf⟩ := denoteRule_inv hx
    simp only [rulesAtLps] at hrun
    obtain ⟨rhs, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hrhs1⟩ := instLPFast_run hok hr hl hu hrhs h1
    obtain ⟨fire, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hf2⟩ := IRecRuleFire.atLps_run hs1.ok hs1.read
      (denoteFire_ext hf hs1.ext) h3
    obtain ⟨rest, s₃, h5, h6⟩ := AM.bind_ok h4
    have hx12 := hs1.ext.trans hs2.ext
    obtain ⟨hs3, hrest⟩ := ih hs2.ok hs2.read (denoteNListE_ext hx12 _ _ hl)
      (denoteLs_ext hu hx12) (denoteRules_ext hx12 _ _ hxs) h5
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
    refine ⟨(hs1.trans hs2).trans hs3, ?_⟩
    have hx3 := hs2.ext.trans hs3.ext
    have hc3 := denoteN_ext hc ((hs1.ext.trans hs2.ext).trans hs3.ext)
    simp only [Frontend.denoteRules, Frontend.denoteRule, hc3,
      denoteFire_ext hf2 hs3.ext, denote_ext hrhs1 hx3, hrest, List.map_cons, hnf]

/-- con-leche: ConLeche/Kernel/Basis.lean:62-78 ConstantInfo.atLps — **a stored
constant at other level-parameter names**: the arena's renaming denotes
con-leche's. -/
theorem IConstantInfo.atLps_run {ci r : IConstantInfo} {ps : List NIdx}
    {c : ConstantInfo} {psv : List ConLeche.Name} {s s' : AState}
    (hok : StateOK s) (hr : ReadOK s) (hc : Frontend.denoteCI s.store ci = some c)
    (hps : Frontend.denoteNList s.store.ns ps = some psv)
    (hrun : IConstantInfo.atLps ci ps s = .ok (r, s')) :
    RStep s s' ∧ Frontend.denoteCI s'.store r = some (c.atLps psv) := by
  cases ci with
  | axiomInfo v =>
    obtain ⟨cv, rfl, hv⟩ := denoteCI_axiom_inv hc
    simp only [IConstantInfo.atLps] at hrun
    obtain ⟨v2, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    obtain ⟨hs1, hv2⟩ := IConstantVal.atLps_run hok hr hv hps h1
    exact ⟨hs1, by simp [Frontend.denoteCI, hv2, ConLeche.ConstantInfo.atLps]⟩
  | thmInfo v =>
    obtain ⟨cv, rfl, hv⟩ := denoteCI_thm_inv hc
    simp only [IConstantInfo.atLps] at hrun
    obtain ⟨v2, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    obtain ⟨hs1, hv2⟩ := IConstantVal.atLps_run hok hr hv hps h1
    exact ⟨hs1, by simp [Frontend.denoteCI, hv2, ConLeche.ConstantInfo.atLps]⟩
  | ctorInfo v nP nF T =>
    have hT := denoteCI_ctor_induct hc
    obtain ⟨cv, rfl, hv⟩ := denoteCI_ctor_inv hc
    simp only [IConstantInfo.atLps] at hrun
    obtain ⟨v2, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    obtain ⟨hs1, hv2⟩ := IConstantVal.atLps_run hok hr hv hps h1
    exact ⟨hs1, by simp [Frontend.denoteCI, hv2, denoteN_ext hT hs1.ext,
      ConLeche.ConstantInfo.atLps]⟩
  | indInfo v cap =>
    obtain ⟨cv, d, rfl, hv, hd⟩ := denoteCI_ind_inv hc
    simp only [IConstantInfo.atLps] at hrun
    obtain ⟨v2, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    obtain ⟨hs1, hv2⟩ := IConstantVal.atLps_run hok hr hv hps h1
    exact ⟨hs1, by simp [Frontend.denoteCI, hv2, denoteCaps_ext hd hs1.ext,
      ConLeche.ConstantInfo.atLps]⟩
  | defnInfo v e hh =>
    obtain ⟨cv, x, rfl, hv, hx⟩ := denoteCI_defn_inv hc
    obtain ⟨-, hl, -⟩ := denoteCV_inv hv
    simp only [IConstantInfo.atLps] at hrun
    obtain ⟨v2, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hv2⟩ := IConstantVal.atLps_run hok hr hv hps h1
    obtain ⟨us, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hus⟩ := paramLevels_run hs1.ok (denoteNListE_ext hs1.ext _ _ hps) h3
    have hs2' := RStep.of_istep hs2 hs1.read
    obtain ⟨e2, s₃, h5, h6⟩ := AM.bind_ok h4
    have hx12 := hs1.ext.trans hs2.ext
    obtain ⟨hs3, he2⟩ := instLPFast_run hs2.ok hs2'.read
      (denoteNListE_ext hx12 _ _ hl) hus (denote_ext hx hx12) h5
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
    refine ⟨(hs1.trans hs2').trans hs3, ?_⟩
    simp [Frontend.denoteCI, denoteCV_ext hv2 (hs2.ext.trans hs3.ext), he2,
      ConLeche.ConstantInfo.atLps, ConLeche.ConstantInfo.toConstantVal]
  | recInfo v mI rP k rules =>
    obtain ⟨cv, Rs, rfl, hv, hRs⟩ := denoteCI_rec_inv hc
    obtain ⟨-, hl, -⟩ := denoteCV_inv hv
    simp only [IConstantInfo.atLps] at hrun
    obtain ⟨v2, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hv2⟩ := IConstantVal.atLps_run hok hr hv hps h1
    obtain ⟨us, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hus⟩ := paramLevels_run hs1.ok (denoteNListE_ext hs1.ext _ _ hps) h3
    have hs2' := RStep.of_istep hs2 hs1.read
    have hx12 := hs1.ext.trans hs2.ext
    obtain ⟨lpsT, s₃, h5, h6⟩ := AM.bind_ok h4
    obtain ⟨hs3, hlT⟩ := readNamesM_run hs2.ok hs2'.read h5
    rw [denoteNListE_ext hx12 _ _ hl] at hlT
    obtain rfl := (Option.some.inj hlT).symm
    obtain ⟨psT, s₄, h7, h8⟩ := AM.bind_ok h6
    have hx13 := hx12.trans hs3.ext
    obtain ⟨hs4, hpT⟩ := readNamesM_run hs3.ok hs3.read h7
    rw [denoteNListE_ext hx13 _ _ hps] at hpT
    obtain rfl := Option.some.inj hpT
    obtain ⟨rules2, s₅, h9, h10⟩ := AM.bind_ok h8
    have hx14 := hx13.trans hs4.ext
    have hx24 := hs3.ext.trans hs4.ext
    obtain ⟨hs5, hR2⟩ := rulesAtLps_run v.levelParams us cv.levelParams
      (psv.map Level.param) rules hs4.ok hs4.read (denoteNListE_ext hx14 _ _ hl)
      (denoteLs_ext hus hx24) (denoteRules_ext hx14 _ _ hRs) h9
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h10
    refine ⟨(((hs1.trans hs2').trans hs3).trans hs4).trans hs5, ?_⟩
    simp [Frontend.denoteCI, denoteCV_ext hv2 ((hs2.ext.trans hx24).trans hs5.ext), hR2,
      ConLeche.ConstantInfo.atLps, ConLeche.ConstantInfo.toConstantVal]

/-! ## The block's comparison with its pin -/

/-- con-leche: ConLeche/Kernel/Level.lean:228-230 Name.nodup — the handle test
is the name test, by `denoteNList_contains` at every tail. -/
theorem nameNodup_denote {st : EStore} (hwf : StoreWF st) :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns ns = some xs →
        nameNodup ns = ConLeche.Name.nodup xs := by
  intro ns
  induction ns with
  | nil =>
    intro xs h
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro xs h
    obtain ⟨y, ys, ha, has, rfl⟩ := denoteNList_cons_inv h
    simp only [nameNodup, ConLeche.Name.nodup,
      denoteNList_contains hwf as ys has a y ha, ih ys has]

/-- con-leche: ConLeche/Kernel/Basis.lean:80-84 pinAgrees — the handle test is
con-leche's, by injectivity (`denoteCI_inj`, `denoteCV_inj`). -/
theorem pinAgrees_eq {st : EStore} (hwf : StoreWF st) {ci p : IConstantInfo}
    {c P : ConstantInfo} (hc : Frontend.denoteCI st ci = some c)
    (hp : Frontend.denoteCI st p = some P) :
    Arena.pinAgrees ci p = ConLeche.pinAgrees c P := by
  have hgen : (ci == p) = c.beqP P := by
    rw [ConstantInfo.beqP_eq]; exact beq_of_denote_inj (denoteCI_inj hwf) hc hp
  cases ci <;> cases p
  all_goals first
    | obtain ⟨cv, rfl, hv⟩ := denoteCI_axiom_inv hc
    | obtain ⟨cv, x, rfl, hv, hx⟩ := denoteCI_defn_inv hc
    | obtain ⟨cv, rfl, hv⟩ := denoteCI_thm_inv hc
    | obtain ⟨cv, d, rfl, hv, hd⟩ := denoteCI_ind_inv hc
    | obtain ⟨cv, rfl, hv⟩ := denoteCI_ctor_inv hc
    | obtain ⟨cv, Rs, rfl, hv, hRs⟩ := denoteCI_rec_inv hc
  all_goals first
    | obtain ⟨cv', rfl, hv'⟩ := denoteCI_axiom_inv hp
    | obtain ⟨cv', x', rfl, hv', hx'⟩ := denoteCI_defn_inv hp
    | obtain ⟨cv', rfl, hv'⟩ := denoteCI_thm_inv hp
    | obtain ⟨cv', d', rfl, hv', hd'⟩ := denoteCI_ind_inv hp
    | obtain ⟨cv', rfl, hv'⟩ := denoteCI_ctor_inv hp
    | obtain ⟨cv', Rs', rfl, hv', hRs'⟩ := denoteCI_rec_inv hp
  all_goals first
    | exact (beq_of_denote_inj (denoteCV_inj hwf) hv hv').trans
        (ConstantVal.beqP_eq _ _).symm
    | exact hgen

/-- con-leche: ConLeche/Kernel/Basis.lean:86-91 pinCopyOk — **is the record the
pin, up to its level-parameter names?**  The arena's answer is con-leche's. -/
theorem pinCopyOk_run {ci pin : IConstantInfo} {c P : ConstantInfo} {r : Bool}
    {s s' : AState} (hok : StateOK s) (hr : ReadOK s)
    (hc : Frontend.denoteCI s.store ci = some c)
    (hp : Frontend.denoteCI s.store pin = some P)
    (hrun : pinCopyOk ci pin s = .ok (r, s')) :
    RStep s s' ∧ r = ConLeche.pinCopyOk c P := by
  have hps := (denoteCV_inv (denoteCI_toConstantVal hc)).2.1
  have hpp := (denoteCV_inv (denoteCI_toConstantVal hp)).2.1
  have hcond : (nameNodup ci.toConstantVal.levelParams &&
      ci.toConstantVal.levelParams.length == pin.toConstantVal.levelParams.length) =
      (ConLeche.Name.nodup c.toConstantVal.levelParams &&
        c.toConstantVal.levelParams.length == P.toConstantVal.levelParams.length) := by
    rw [nameNodup_denote hok.wf _ _ hps, denoteNList_length _ _ hps,
      denoteNList_length _ _ hpp]
  simp only [Arena.pinCopyOk] at hrun
  rcases AM.ite_ok hrun with ⟨hy, k⟩ | ⟨hn, k⟩
  · obtain ⟨x, s₁, h1, h2⟩ := AM.bind_ok k
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    obtain ⟨hs1, hx⟩ := IConstantInfo.atLps_run hok hr hp hps h1
    refine ⟨hs1, ?_⟩
    rw [pinAgrees_eq hs1.ok.wf (denoteCI_ext hc hs1.ext) hx]
    simp only [ConLeche.pinCopyOk, ← hcond, hy, Bool.true_and]
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    refine ⟨RStep.refl hok hr, ?_⟩
    have hf : (nameNodup ci.toConstantVal.levelParams &&
        ci.toConstantVal.levelParams.length == pin.toConstantVal.levelParams.length)
        = false := by simpa using hn
    simp only [ConLeche.pinCopyOk, ← hcond, hf, Bool.false_and]

/-- con-leche: ConLeche/Kernel/Basis.lean:93-98 pinLinkOk — what a recursor's
rule reads off its constructor's parameters, on the read-back names. -/
theorem pinLinkOk_run {R Rp C Cp : List NIdx} {RT RpT CT CpT : List ConLeche.Name}
    {r : Bool} {s s' : AState} (hok : StateOK s) (hr : ReadOK s)
    (hR : Frontend.denoteNList s.store.ns R = some RT)
    (hRp : Frontend.denoteNList s.store.ns Rp = some RpT)
    (hC : Frontend.denoteNList s.store.ns C = some CT)
    (hCp : Frontend.denoteNList s.store.ns Cp = some CpT)
    (hrun : pinLinkOk R Rp C Cp s = .ok (r, s')) :
    RStep s s' ∧ r = ConLeche.pinLinkOk RT RpT CT CpT := by
  simp only [Arena.pinLinkOk] at hrun
  obtain ⟨a, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, ha⟩ := readNamesM_run hok hr h1
  rw [hR] at ha; obtain rfl := (Option.some.inj ha).symm
  obtain ⟨b, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hs2, hb⟩ := readNamesM_run hs1.ok hs1.read h3
  rw [denoteNListE_ext hs1.ext _ _ hRp] at hb; obtain rfl := (Option.some.inj hb).symm
  obtain ⟨c, s₃, h5, h6⟩ := AM.bind_ok h4
  have hx12 := hs1.ext.trans hs2.ext
  obtain ⟨hs3, hc⟩ := readNamesM_run hs2.ok hs2.read h5
  rw [denoteNListE_ext hx12 _ _ hC] at hc; obtain rfl := (Option.some.inj hc).symm
  obtain ⟨d, s₄, h7, h8⟩ := AM.bind_ok h6
  obtain ⟨hs4, hd⟩ := readNamesM_run hs3.ok hs3.read h7
  rw [denoteNListE_ext (hx12.trans hs3.ext) _ _ hCp] at hd
  obtain rfl := (Option.some.inj hd).symm
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h8
  exact ⟨((hs1.trans hs2).trans hs3).trans hs4, rfl⟩

/-- con-leche: none — the index answers what the environment answers, as one
disjunction a `match` on both sides can be read off. -/
@[expose] def FindRel (st : EStore) (x : Option IConstantInfo) (y : Option ConstantInfo) :
    Prop :=
  (x = none ∧ y = none) ∨
    ∃ ci c, x = some ci ∧ y = some c ∧ Frontend.denoteCI st ci = some c

/-- con-leche: none — a lookup's presence test agrees. -/
theorem FindRel.isSome {st : EStore} {x : Option IConstantInfo}
    {y : Option ConstantInfo} (h : FindRel st x y) : x.isSome = y.isSome := by
  rcases h with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, -⟩ <;> rfl

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — `IFEnvOK`'s two halves at
one handle. -/
theorem IFEnvOK.findRel {env : Env} {fe : IFEnv} {s : AState}
    (hok : StateOK s) (h : IFEnvOK env fe s) {n : NIdx} {nm : ConLeche.Name}
    (hd : denoteN s.store.ns n = some nm) :
    FindRel s.store (fe.find? n) (env.find? nm) := by
  cases hf : fe.find? n with
  | none => exact Or.inl ⟨rfl, h.miss hok hd hf⟩
  | some ci =>
    obtain ⟨nm', c, h1, h2, h3⟩ := h.hit n ci hf
    rw [hd] at h1
    obtain rfl := Option.some.inj h1
    exact Or.inr ⟨ci, c, rfl, h3, h2⟩

/-- con-leche: ConLeche/Kernel/Basis.lean:100-102 constNamed? — the constant
of a list by name: the handle search finds what con-leche's finds. -/
theorem constNamed_rel {st : EStore} (hwf : StoreWF st) :
    ∀ (cs : List IConstantInfo) (zs : List ConstantInfo) (n : NIdx)
      (nm : ConLeche.Name),
      Frontend.denoteCIList st cs = some zs → denoteN st.ns n = some nm →
      FindRel st (Arena.constNamed? cs n) (ConLeche.constNamed? zs nm) := by
  intro cs
  induction cs with
  | nil =>
    intro zs n nm h _
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h
    exact Or.inl ⟨rfl, rfl⟩
  | cons a as ih =>
    intro zs n nm h hn
    obtain ⟨x, xs, hx, hxs, rfl⟩ := denoteCIList_cons h
    have hiff := beq_handle_iff hwf (denoteCI_name hx) hn
    simp only [Arena.constNamed?, ConLeche.constNamed?, List.find?_cons]
    by_cases he : x.name = nm
    · have ha : (a.name == n) = true := hiff.mpr he
      rw [ha]
      simp only [he, beq_self_eq_true]
      exact Or.inr ⟨a, x, rfl, rfl, hx⟩
    · have ha : (a.name == n) = false := by
        cases hb : (a.name == n) with
        | false => rfl
        | true => exact absurd (hiff.mp hb) he
      have hb : (x.name == nm) = false := by simpa using he
      rw [ha, hb]
      exact ih xs n nm hxs hn

/-- con-leche: ConLeche/Kernel/Basis.lean:104-118 blockLinksOk — the cited
`rules.all`'s predicate, one rule. -/
@[expose] def ruleLinkP (block pins : List ConstantInfo) (R Rp : List ConLeche.Name)
    (rl : RecRule) : Bool :=
  match ConLeche.constNamed? block rl.ctor, ConLeche.constNamed? pins rl.ctor with
  | some C, some Cp =>
    ConLeche.pinLinkOk R Rp C.toConstantVal.levelParams Cp.toConstantVal.levelParams
  | _, _ => false

/-- con-leche: ConLeche/Kernel/Basis.lean:104-118 blockLinksOk — the cited
`(List.zip block pins).all`'s predicate, one pair. -/
@[expose] def blockLinkAtP (block pins : List ConstantInfo)
    (former : List ConLeche.Name) : ConstantInfo × ConstantInfo → Bool :=
  fun (c, p) =>
    match c, p with
    | .ctorInfo cv _ _ _, _ => cv.levelParams == former
    | .recInfo cv .., .recInfo cvp _ _ _ rules =>
      rules.all (ruleLinkP block pins cv.levelParams cvp.levelParams)
    | _, _ => true

/-- con-leche: ConLeche/Kernel/Basis.lean:104-118 blockLinksOk — the
definition, with its two predicates named. -/
theorem blockLinksOk_eq (block pins : List ConstantInfo) :
    ConLeche.blockLinksOk block pins =
      (List.zip block pins).all (blockLinkAtP block pins
        ((block.head?.map (·.toConstantVal.levelParams)).getD [])) := rfl

/-- con-leche: ConLeche/Kernel/Basis.lean:104-118 blockLinksOk — the cited
`rules.all`, rule by rule. -/
theorem rulesLinkOk_run {block pins : List IConstantInfo} {B P : List ConstantInfo}
    {R Rp : List NIdx} {RT RpT : List ConLeche.Name} :
    ∀ (rules : List IRecRule) {Rs : List RecRule} {r : Bool} {s s' : AState},
      StateOK s → ReadOK s →
      Frontend.denoteCIList s.store block = some B →
      Frontend.denoteCIList s.store pins = some P →
      Frontend.denoteNList s.store.ns R = some RT →
      Frontend.denoteNList s.store.ns Rp = some RpT →
      Frontend.denoteRules s.store rules = some Rs →
      rulesLinkOk block pins R Rp rules s = .ok (r, s') →
      RStep s s' ∧ r = Rs.all (ruleLinkP B P RT RpT) := by
  intro rules
  induction rules with
  | nil =>
    intro Rs r s s' hok hr _ _ _ _ hRs hrun
    simp only [Frontend.denoteRules, Option.some.injEq] at hRs
    subst hRs
    simp only [rulesLinkOk] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨RStep.refl hok hr, rfl⟩
  | cons rl rls ih =>
    intro Rs r s s' hok hr hB hP hR hRp hRs hrun
    obtain ⟨x, xs, hx, hxs, rfl⟩ := denoteRules_cons hRs
    obtain ⟨hc, -, -, -⟩ := denoteRule_inv hx
    simp only [rulesLinkOk] at hrun
    have h1 := constNamed_rel hok.wf block B rl.ctor x.ctor hB hc
    have h2 := constNamed_rel hok.wf pins P rl.ctor x.ctor hP hc
    simp only [List.all_cons, ruleLinkP]
    rcases h1 with ⟨e1, e1'⟩ | ⟨C, C', e1, e1', hC⟩
    · rw [e1] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨RStep.refl hok hr, by rw [e1']; rfl⟩
    · rcases h2 with ⟨e2, e2'⟩ | ⟨Cp, Cp', e2, e2', hCp⟩
      · rw [e1, e2] at hrun
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        exact ⟨RStep.refl hok hr, by rw [e1', e2']; rfl⟩
      · rw [e1, e2] at hrun
        simp only at hrun
        obtain ⟨b, s₁, g1, k1⟩ := AM.bind_ok hrun
        obtain ⟨hs1, hb⟩ := pinLinkOk_run hok hr hR hRp
          (denoteCV_inv (denoteCI_toConstantVal hC)).2.1
          (denoteCV_inv (denoteCI_toConstantVal hCp)).2.1 g1
        rw [e1', e2']
        simp only
        rcases AM.ite_ok k1 with ⟨hy, k2⟩ | ⟨hn, k2⟩
        · obtain ⟨hs2, hrest⟩ := ih hs1.ok hs1.read
            (denoteCIList_mono hs1.ext _ _ hB) (denoteCIList_mono hs1.ext _ _ hP)
            (denoteNListE_ext hs1.ext _ _ hR) (denoteNListE_ext hs1.ext _ _ hRp)
            (denoteRules_ext hs1.ext _ _ hxs) k2
          refine ⟨hs1.trans hs2, ?_⟩
          rw [hrest, ← hb, (by simpa using hy : b = true), Bool.true_and]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
          refine ⟨hs1, ?_⟩
          rw [← hb, (by simpa using hn : b = false), Bool.false_and]

/-- con-leche: ConLeche/Kernel/Basis.lean:104-118 blockLinksOk — the cited
`match c, p with`, one pair. -/
theorem blockLinkOkAt_run {block pins : List IConstantInfo} {B P : List ConstantInfo}
    {former : List NIdx} {formerT : List ConLeche.Name} {c p : IConstantInfo}
    {c' p' : ConstantInfo} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hr : ReadOK s)
    (hB : Frontend.denoteCIList s.store block = some B)
    (hP : Frontend.denoteCIList s.store pins = some P)
    (hf : Frontend.denoteNList s.store.ns former = some formerT)
    (hc : Frontend.denoteCI s.store c = some c')
    (hp : Frontend.denoteCI s.store p = some p')
    (hrun : blockLinkOkAt block pins former c p s = .ok (r, s')) :
    RStep s s' ∧ r = blockLinkAtP B P formerT (c', p') := by
  cases c with
  | ctorInfo v nP nF T =>
    obtain ⟨cv, rfl, hv⟩ := denoteCI_ctor_inv hc
    simp only [blockLinkOkAt] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    refine ⟨RStep.refl hok hr, ?_⟩
    exact beq_of_denote_inj (fun h1 h2 => denoteNList_inj hok.wf _ _ _ h1 h2)
      (denoteCV_inv hv).2.1 hf
  | recInfo v mI rP k rules =>
    obtain ⟨cv, Rs, rfl, hv, hRs⟩ := denoteCI_rec_inv hc
    cases p with
    | recInfo vp mIp rPp kp rulesp =>
      obtain ⟨cvp, Rsp, rfl, hvp, hRsp⟩ := denoteCI_rec_inv hp
      simp only [blockLinkOkAt] at hrun
      exact rulesLinkOk_run rulesp hok hr hB hP (denoteCV_inv hv).2.1
        (denoteCV_inv hvp).2.1 hRsp hrun
    | axiomInfo _ =>
      obtain ⟨_, rfl, _⟩ := denoteCI_axiom_inv hp
      simp only [blockLinkOkAt] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨RStep.refl hok hr, rfl⟩
    | defnInfo _ _ _ =>
      obtain ⟨_, _, rfl, _, _⟩ := denoteCI_defn_inv hp
      simp only [blockLinkOkAt] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨RStep.refl hok hr, rfl⟩
    | thmInfo _ =>
      obtain ⟨_, rfl, _⟩ := denoteCI_thm_inv hp
      simp only [blockLinkOkAt] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨RStep.refl hok hr, rfl⟩
    | indInfo _ _ =>
      obtain ⟨_, _, rfl, _, _⟩ := denoteCI_ind_inv hp
      simp only [blockLinkOkAt] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨RStep.refl hok hr, rfl⟩
    | ctorInfo _ _ _ _ =>
      obtain ⟨_, rfl, _⟩ := denoteCI_ctor_inv hp
      simp only [blockLinkOkAt] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨RStep.refl hok hr, rfl⟩
  | axiomInfo _ =>
    obtain ⟨_, rfl, _⟩ := denoteCI_axiom_inv hc
    simp only [blockLinkOkAt] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨RStep.refl hok hr, rfl⟩
  | defnInfo _ _ _ =>
    obtain ⟨_, _, rfl, _, _⟩ := denoteCI_defn_inv hc
    simp only [blockLinkOkAt] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨RStep.refl hok hr, rfl⟩
  | thmInfo _ =>
    obtain ⟨_, rfl, _⟩ := denoteCI_thm_inv hc
    simp only [blockLinkOkAt] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨RStep.refl hok hr, rfl⟩
  | indInfo _ _ =>
    obtain ⟨_, _, rfl, _, _⟩ := denoteCI_ind_inv hc
    simp only [blockLinkOkAt] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨RStep.refl hok hr, rfl⟩

/-- con-leche: ConLeche/Kernel/Basis.lean:104-118 blockLinksOk — the cited
`(List.zip block pins).all`, pair by pair. -/
theorem blockLinksOkGo_run {block pins : List IConstantInfo} {B P : List ConstantInfo}
    {former : List NIdx} {formerT : List ConLeche.Name} :
    ∀ (cs ps : List IConstantInfo) {zs qs : List ConstantInfo} {r : Bool}
      {s s' : AState},
      StateOK s → ReadOK s →
      Frontend.denoteCIList s.store block = some B →
      Frontend.denoteCIList s.store pins = some P →
      Frontend.denoteNList s.store.ns former = some formerT →
      Frontend.denoteCIList s.store cs = some zs →
      Frontend.denoteCIList s.store ps = some qs →
      blockLinksOkGo block pins former cs ps s = .ok (r, s') →
      RStep s s' ∧ r = (List.zip zs qs).all (blockLinkAtP B P formerT) := by
  intro cs
  induction cs with
  | nil =>
    intro ps zs qs r s s' hok hr _ _ _ hzs _ hrun
    simp only [Frontend.denoteCIList, Option.some.injEq] at hzs
    subst hzs
    simp only [blockLinksOkGo] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨RStep.refl hok hr, rfl⟩
  | cons c cs ih =>
    intro ps zs qs r s s' hok hr hB hP hf hzs hqs hrun
    obtain ⟨z, zs', hz, hzs', rfl⟩ := denoteCIList_cons hzs
    cases ps with
    | nil =>
      simp only [Frontend.denoteCIList, Option.some.injEq] at hqs
      subst hqs
      simp only [blockLinksOkGo] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨RStep.refl hok hr, rfl⟩
    | cons p ps =>
      obtain ⟨q, qs', hq, hqs', rfl⟩ := denoteCIList_cons hqs
      simp only [blockLinksOkGo] at hrun
      obtain ⟨b, s₁, g1, k1⟩ := AM.bind_ok hrun
      obtain ⟨hs1, hb⟩ := blockLinkOkAt_run hok hr hB hP hf hz hq g1
      simp only [List.zip_cons_cons, List.all_cons]
      rcases AM.ite_ok k1 with ⟨hy, k2⟩ | ⟨hn, k2⟩
      · obtain ⟨hs2, hrest⟩ := ih ps hs1.ok hs1.read
          (denoteCIList_mono hs1.ext _ _ hB) (denoteCIList_mono hs1.ext _ _ hP)
          (denoteNListE_ext hs1.ext _ _ hf) (denoteCIList_mono hs1.ext _ _ hzs')
          (denoteCIList_mono hs1.ext _ _ hqs') k2
        refine ⟨hs1.trans hs2, ?_⟩
        rw [hrest, ← hb, (by simpa using hy : b = true), Bool.true_and]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        refine ⟨hs1, ?_⟩
        rw [← hb, (by simpa using hn : b = false), Bool.false_and]

/-- con-leche: ConLeche/Kernel/Basis.lean:104-118 blockLinksOk — the stream's
recursor links its rules' constructors as the pin's does, and a constructor
carries its former's names. -/
theorem blockLinksOk_run {block pins : List IConstantInfo} {B P : List ConstantInfo}
    {r : Bool} {s s' : AState} (hok : StateOK s) (hr : ReadOK s)
    (hB : Frontend.denoteCIList s.store block = some B)
    (hP : Frontend.denoteCIList s.store pins = some P)
    (hrun : Arena.blockLinksOk block pins s = .ok (r, s')) :
    RStep s s' ∧ r = ConLeche.blockLinksOk B P := by
  have hf : Frontend.denoteNList s.store.ns
      ((block.head?.map (·.toConstantVal.levelParams)).getD []) =
      some ((B.head?.map (·.toConstantVal.levelParams)).getD []) := by
    cases block with
    | nil =>
      simp only [Frontend.denoteCIList, Option.some.injEq] at hB
      subst hB; rfl
    | cons a as =>
      obtain ⟨x, xs, hx, -, rfl⟩ := denoteCIList_cons hB
      exact (denoteCV_inv (denoteCI_toConstantVal hx)).2.1
  rw [blockLinksOk_eq]
  exact blockLinksOkGo_run block pins hok hr hB hP hf hB hP hrun

/-- con-leche: ConLeche/Kernel/Canon.lean:290-294 listBeqBy
con-leche: ConLeche/Kernel/Basis.lean:120-122 pinListOk — the cited
`listBeqBy pinCopyOk block pins`. -/
theorem pinCopiesOk_run :
    ∀ (cs ps : List IConstantInfo) {zs qs : List ConstantInfo} {r : Bool}
      {s s' : AState},
      StateOK s → ReadOK s →
      Frontend.denoteCIList s.store cs = some zs →
      Frontend.denoteCIList s.store ps = some qs →
      pinCopiesOk cs ps s = .ok (r, s') →
      RStep s s' ∧ r = ConLeche.listBeqBy ConLeche.pinCopyOk zs qs := by
  intro cs
  induction cs with
  | nil =>
    intro ps zs qs r s s' hok hr hzs hqs hrun
    simp only [Frontend.denoteCIList, Option.some.injEq] at hzs
    subst hzs
    cases ps with
    | nil =>
      simp only [Frontend.denoteCIList, Option.some.injEq] at hqs
      subst hqs
      simp only [pinCopiesOk] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨RStep.refl hok hr, rfl⟩
    | cons p ps =>
      obtain ⟨q, qs', -, -, rfl⟩ := denoteCIList_cons hqs
      simp only [pinCopiesOk] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨RStep.refl hok hr, rfl⟩
  | cons c cs ih =>
    intro ps zs qs r s s' hok hr hzs hqs hrun
    obtain ⟨z, zs', hz, hzs', rfl⟩ := denoteCIList_cons hzs
    cases ps with
    | nil =>
      simp only [Frontend.denoteCIList, Option.some.injEq] at hqs
      subst hqs
      simp only [pinCopiesOk] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨RStep.refl hok hr, rfl⟩
    | cons p ps =>
      obtain ⟨q, qs', hq, hqs', rfl⟩ := denoteCIList_cons hqs
      simp only [pinCopiesOk] at hrun
      obtain ⟨b, s₁, g1, k1⟩ := AM.bind_ok hrun
      obtain ⟨hs1, hb⟩ := pinCopyOk_run hok hr hz hq g1
      simp only [ConLeche.listBeqBy]
      rcases AM.ite_ok k1 with ⟨hy, k2⟩ | ⟨hn, k2⟩
      · obtain ⟨hs2, hrest⟩ := ih ps hs1.ok hs1.read
          (denoteCIList_mono hs1.ext _ _ hzs') (denoteCIList_mono hs1.ext _ _ hqs') k2
        refine ⟨hs1.trans hs2, ?_⟩
        rw [hrest, ← hb, (by simpa using hy : b = true), Bool.true_and]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        refine ⟨hs1, ?_⟩
        rw [← hb, (by simpa using hn : b = false), Bool.false_and]

/-- con-leche: ConLeche/Kernel/Basis.lean:120-122 pinListOk — **the block's
comparison with its pin**: the arena's answer is con-leche's. -/
theorem pinListOk_run {block pins : List IConstantInfo} {B P : List ConstantInfo}
    {r : Bool} {s s' : AState} (hok : StateOK s) (hr : ReadOK s)
    (hB : Frontend.denoteCIList s.store block = some B)
    (hP : Frontend.denoteCIList s.store pins = some P)
    (hrun : Arena.pinListOk block pins s = .ok (r, s')) :
    RStep s s' ∧ r = ConLeche.pinListOk B P := by
  simp only [Arena.pinListOk] at hrun
  obtain ⟨b, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hb⟩ := pinCopiesOk_run block pins hok hr hB hP g1
  simp only [ConLeche.pinListOk]
  rcases AM.ite_ok k1 with ⟨hy, k2⟩ | ⟨hn, k2⟩
  · obtain ⟨hs2, hrest⟩ := blockLinksOk_run hs1.ok hs1.read
      (denoteCIList_mono hs1.ext _ _ hB) (denoteCIList_mono hs1.ext _ _ hP) k2
    refine ⟨hs1.trans hs2, ?_⟩
    rw [hrest, ← hb, (by simpa using hy : b = true), Bool.true_and]
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
    refine ⟨hs1, ?_⟩
    rw [← hb, (by simpa using hn : b = false), Bool.false_and]

/-! ## What a pinned block and a quotient record store -/

/-- con-leche: ConLeche/Kernel/Basis.lean:143-145 quotPin — the pinned
quotient package's constant at a slot.  The `getD` default is never read: the
package has five members and every slot is below five. -/
theorem quotPin_run {k : QuotKind} {ci : IConstantInfo} {s s' : AState}
    (hok : StateOK s) (hrun : Arena.quotPin k s = .ok (ci, s')) :
    Frontend.IStepS s s' ∧ Frontend.denoteCI s'.store ci = some (ConLeche.quotPin k) := by
  simp only [Arena.quotPin] at hrun
  obtain ⟨blk, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
  obtain ⟨hs1, hden1⟩ := BasisKind.decls_run hok g1
  have hlen : blk.length = (ConLeche.BasisKind.decls .quotK).length :=
    denoteCIList_length blk _ hden1
  have hslot : k.slot < blk.length := by
    rw [hlen]; cases k <;> decide
  refine ⟨hs1, ?_⟩
  cases hb : blk[k.slot]? with
  | none => exact absurd (List.getElem?_eq_none_iff.mp hb) (by omega)
  | some ci =>
    obtain ⟨x, hx, hdci⟩ := denoteCIList_get blk _ k.slot ci hden1 hb
    have h1 : blk.getD k.slot default = ci := by
      rw [List.getD_eq_getElem?_getD, hb]; rfl
    have h2 : ConLeche.quotPin k = x := by
      simp only [ConLeche.quotPin, List.getD_eq_getElem?_getD, hx]; rfl
    rw [h1, h2]; exact hdci

/-- con-leche: ConLeche/Kernel/Basis.lean:147-150 quotAt — **what a quotient
record stores**: its slot's pin at the names it declares. -/
theorem quotAt_run {k : QuotKind} {v : IConstantVal} {cv : ConstantVal}
    {ci : IConstantInfo} {s s' : AState} (hok : StateOK s) (hr : ReadOK s)
    (hv : Frontend.denoteCV s.store v = some cv)
    (hrun : Arena.quotAt k v s = .ok (ci, s')) :
    RStep s s' ∧ Frontend.denoteCI s'.store ci = some (ConLeche.quotAt k cv) := by
  simp only [Arena.quotAt] at hrun
  obtain ⟨p, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hp⟩ := quotPin_run hok g1
  have hs1' := RStep.of_istep hs1 hr
  obtain ⟨hs2, hci⟩ := IConstantInfo.atLps_run hs1.ok hs1'.read hp
    (denoteNListE_ext hs1.ext _ _ (denoteCV_inv hv).2.1) k1
  exact ⟨hs1'.trans hs2, hci⟩

/-- con-leche: ConLeche/Kernel/Basis.lean:152-158 quotPinHit — **the
quotient-pin match**: the arena's answer is con-leche's. -/
theorem quotPinHit_run {k : QuotKind} {v : IConstantVal} {cv : ConstantVal}
    {r : Bool} {s s' : AState} (hok : StateOK s) (hr : ReadOK s)
    (hv : Frontend.denoteCV s.store v = some cv)
    (hrun : Arena.quotPinHit k v s = .ok (r, s')) :
    RStep s s' ∧ r = ConLeche.quotPinHit k cv := by
  have hl := (denoteCV_inv hv).2.1
  simp only [Arena.quotPinHit] at hrun
  obtain ⟨p, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hp⟩ := quotPin_run hok g1
  have hs1' := RStep.of_istep hs1 hr
  have hpl := (denoteCV_inv (denoteCI_toConstantVal hp)).2.1
  have hcond : (nameNodup v.levelParams &&
      v.levelParams.length == p.toConstantVal.levelParams.length) =
      (ConLeche.Name.nodup cv.levelParams &&
        cv.levelParams.length == (ConLeche.quotPin k).toConstantVal.levelParams.length) := by
    rw [nameNodup_denote hs1.ok.wf _ _ (denoteNListE_ext hs1.ext _ _ hl),
      denoteNList_length _ _ hl, denoteNList_length _ _ hpl]
  rcases AM.ite_ok k1 with ⟨hy, k⟩ | ⟨hn, k⟩
  · obtain ⟨x, s₂, h1, h2⟩ := AM.bind_ok k
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    obtain ⟨hs2, hx⟩ := IConstantVal.atLps_run hs1.ok hs1'.read
      (denoteCI_toConstantVal hp) (denoteNListE_ext hs1.ext _ _ hl) h1
    refine ⟨hs1'.trans hs2, ?_⟩
    have hv2 := denoteCV_ext hv (hs1.ext.trans hs2.ext)
    rw [beq_of_denote_inj (denoteCV_inj hs2.ok.wf) hv2 hx]
    simp only [ConLeche.quotPinHit, ← hcond, hy, Bool.true_and, ConstantVal.beqP_eq]
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    refine ⟨hs1', ?_⟩
    have hf : (nameNodup v.levelParams &&
        v.levelParams.length == p.toConstantVal.levelParams.length) = false := by
      simpa using hn
    simp only [ConLeche.quotPinHit, ← hcond, hf, Bool.false_and]

/-- con-leche: ConLeche/Kernel/Basis.lean:160-172 quotPredsOk — what a quotient
record's slot needs stored before it: three presence tests, each the
environment's (`IFEnvOK.findRel`).  The test only reads. -/
theorem quotPredsOk_run {env : Env} {fe : IFEnv} {k : QuotKind} {r : Bool}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s) (hie : IFEnvOK env fe s)
    (hrun : Arena.quotPredsOk fe k s = .ok (r, s')) :
    s' = s ∧ r = ConLeche.quotPredsOk env.find? k := by
  simp only [Arena.quotPredsOk, pinEq, pinQuot, pinQuotMk] at hrun
  obtain ⟨e, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.eqName) hp rfl g1
  obtain ⟨q, s₂, g2, k2⟩ := AM.bind_ok k1
  obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.quotName) hp rfl g2
  obtain ⟨m, s₃, g3, k3⟩ := AM.bind_ok k2
  obtain ⟨rfl, d3⟩ := pinAt_run (x := ConLeche.quotMkName) hp rfl g3
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
  refine ⟨rfl, ?_⟩
  simp only [ConLeche.quotPredsOk, (hie.findRel hok d1).isSome,
    (hie.findRel hok d2).isSome, (hie.findRel hok d3).isSome]
  cases k <;> rfl

/-! ## The checks and the installs -/

/-- con-leche: ConLeche/Kernel/Checker.lean:472-483 checkQuotRecord — **a
quotient record's check and install**: compared with its slot's pin
(`quotPinHit_run`), the slots it needs stored (`quotPredsOk_run`), and its pin
installed at its own names (`quotAt_run`).  It serves `checkDecl`'s `.quotDecl`
arm and the `Quot.sound` record of its `.axiomDecl` arm. -/
theorem checkQuotRecord_bridge {env : Env} {fe fe' : IFEnv} {k : QuotKind}
    {v : IConstantVal} {cv : ConstantVal} {s s' : AState}
    (hok : FoldOK env fe s) (hv : Frontend.denoteCV s.store v = some cv)
    (hrun : checkQuotRecord fe k v s = .ok (fe', s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ env', ConLeche.checkQuotRecord (m := CheckM) env k cv = .ok env' := by
  have hst := hok.check.state
  have hr := hok.check.readOK
  simp only [Arena.checkQuotRecord] at hrun
  obtain ⟨c1, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hc1⟩ := quotPinHit_run hst hr hv g1
  obtain ⟨hy1, k2⟩ := AM.dunless_ok AM.Never.fail_any k1
  replace k2 := AM.pure_bind_ok k2
  have hhit : ConLeche.quotPinHit k cv = true := by rw [← hc1]; simpa using hy1
  obtain ⟨c2, s₂, g2, k3⟩ := AM.bind_ok k2
  obtain ⟨rfl, hc2⟩ := quotPredsOk_run hs1.ok (hok.check.pins.mono hs1.ext hs1.pins)
    (hok.check.ienv.mono hs1.ext) g2
  obtain ⟨hy2, k4⟩ := AM.dunless_ok AM.Never.fail_any k3
  replace k4 := AM.pure_bind_ok k4
  have hpred : ConLeche.quotPredsOk env.find? k = true := by rw [← hc2]; simpa using hy2
  obtain ⟨ci, s₃, g3, k5⟩ := AM.bind_ok k4
  obtain ⟨hs3, hci⟩ := quotAt_run hs1.ok hs1.read (denoteCV_ext hv hs1.ext) g3
  have hs13 := hs1.trans hs3
  simp only [ConRon.Arena.installBasisDecl] at k5
  obtain ⟨hdup, k6⟩ := AM.dunless_ok AM.Never.fail_any k5
  replace k6 := AM.pure_bind_ok k6
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k6
  have hfind : fe.find? ci.name = none := by
    cases hf : fe.find? ci.name with
    | none => rfl
    | some d => rw [hf] at hdup; exact absurd hdup (by simp)
  have hfindP : env.find? (ConLeche.quotAt k cv).name = none :=
    IFEnvOK.miss hs3.ok (hok.check.ienv.mono hs13.ext) (denoteCI_name hci) hfind
  refine ⟨hs3.ok, hs13.ext, hs13.pins, ⟨ConLeche.quotAt k cv :: env.consts, env.tables⟩, ?_⟩
  simp only [ConLeche.checkQuotRecord, hhit, hpred, ConLeche.installBasisDecl, hfindP]
  rfl

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind (the
`.quotDecl` arm) — it IS `checkQuotRecord`, on both sides. -/
theorem checkDeclKind_bridge_quot {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {env : Env} {fe fe' : IFEnv} {k : QuotKind} {v : IConstantVal}
    {cv : ConstantVal} {s s' : AState}
    (hok : FoldOK env fe s) (hv : Frontend.denoteCV s.store v = some cv)
    (hrun : Arena.checkDeclKind .verified pins fe (.quotDecl k v) s = .ok (fe', s')) :
    DeclKindOut pinsP env (.quotDecl k cv) s s' := by
  simp only [Arena.checkDeclKind] at hrun
  obtain ⟨h1, h2, h3, env', h4⟩ := checkQuotRecord_bridge hok hv hrun
  exact { state := h1, ext := h2, pins := h3,
          run := ⟨env', 0, by simp only [ConLeche.checkDeclKind]; exact h4⟩ }

/-! ## The reserved names' check -/

/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
reserved names, read off the pin table: the state does not move. -/
theorem reservedBasisNames_runB {s s' : AState} {hs : List NIdx} (hp : PinsOK s)
    (hr : Arena.reservedBasisNames s = .ok (hs, s')) :
    s' = s ∧ Frontend.denoteNList s.store.ns hs = some ConLeche.reservedBasisNames := by
  simp only [Arena.reservedBasisNames] at hr
  obtain ⟨rfl, hd⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ denoteNL s.store r reservedBasisNameValues)
    rfl hr (pinReserved_spec s hp)
  exact ⟨rfl, by rw [← reservedBasisNameValues_eq]; exact denoteNL_toList _ _ hd⟩

/-- con-leche: ConLeche/Kernel/Basis.lean:138-151 basisNamesOk — the
one-constant arms' test. -/
theorem basisNameUnreserved_run {n : NIdx} {nm : ConLeche.Name} {r : Bool} {s s' : AState}
    (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hrun : Arena.basisNameUnreserved n s = .ok (r, s')) :
    s' = s ∧ r = !ConLeche.reservedBasisNames.contains nm := by
  simp only [Arena.basisNameUnreserved] at hrun
  obtain ⟨rs, s1, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hrs⟩ := reservedBasisNames_runB hp g1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
  exact ⟨rfl, by rw [denoteNList_contains hok.wf _ _ hrs _ _ hn]⟩

/-- con-leche: none — a frame that moved nothing but the store's growth is a
renaming step. -/
theorem RStep.of_frame {s s' : AState} (hok : StateOK s') (hx : Ext s.store s'.store)
    (hsc : s'.store.scratchOn = s.store.scratchOn) (hp : s'.pins = s.pins)
    (hc : s'.caches = s.caches) (hr : ReadOK s) : RStep s s' :=
  ⟨hok, hx, hsc, hp, by rw [hc],
    ⟨by rw [hc]; exact hr.readN.mono hx, by rw [hc]; exact hr.readL.mono hx,
      by rw [hc]; exact hr.readLs.mono hx⟩⟩

/-- con-leche: none — a block's members are unreserved on both sides alike. -/
theorem all_unreserved_denote {st : EStore} (hwf : StoreWF st) {rs : List NIdx}
    (hrs : Frontend.denoteNList st.ns rs = some ConLeche.reservedBasisNames) :
    ∀ (block : List IConstantInfo) (b : List ConstantInfo),
      Frontend.denoteCIList st block = some b →
      (block.all fun c => !rs.contains c.name) =
        (b.all fun c => !ConLeche.reservedBasisNames.contains c.name)
  | [], b, hb => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at hb; subst hb; rfl
  | c :: cs, b, hb => by
    obtain ⟨x, xs, hx, hxs, rfl⟩ := denoteCIList_cons hb
    simp only [List.all_cons, denoteNList_contains hwf _ _ hrs _ _ (denoteCI_name hx),
      all_unreserved_denote hwf hrs cs xs hxs]

/-- con-leche: ConLeche/Kernel/Basis.lean:138-151 basisNamesOk — **the
reserved names' check is con-leche's**: a block under a pinned block's names
compared with its pin (`pinListOk_run`), any other block's members and every
one-constant declaration's name tested against the reserved list, `Quot.sound`
and the quotient records passed. -/
theorem basisNamesOk_run {pd : IDeclaration} {d : Declaration} {r : Bool} {s s' : AState}
    (hok : StateOK s) (hr : ReadOK s) (hp : PinsOK s)
    (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.basisNamesOk pd s = .ok (r, s')) :
    RStep s s' ∧ r = ConLeche.basisNamesOk d := by
  have one : ∀ {n : NIdx} {nm : ConLeche.Name}, denoteN s.store.ns n = some nm →
      Arena.basisNameUnreserved n s = .ok (r, s') →
      RStep s s' ∧ r = !ConLeche.reservedBasisNames.contains nm := fun hn h => by
    obtain ⟨rfl, hb⟩ := basisNameUnreserved_run hok hp hn h
    exact ⟨RStep.refl hok hr, hb⟩
  cases pd with
  | quotDecl k v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, -, rfl⟩ := hd
    simp only [Arena.basisNamesOk] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨RStep.refl hok hr, rfl⟩
  | axiomDecl v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    have hn := (denoteCV_inv hcv).1
    simp only [Arena.basisNamesOk] at hrun
    obtain ⟨qs, s1, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.quotSoundName) hp rfl g1
    have hqs := beq_handle_iff hok.wf hn d1
    simp only [ConLeche.basisNamesOk]
    rcases AM.ite_ok k1 with ⟨hy, k2⟩ | ⟨hno, k2⟩
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      exact ⟨RStep.refl hok hr, by simp [hqs.mp hy]⟩
    · obtain ⟨h1, h2⟩ := one hn k2
      refine ⟨h1, ?_⟩
      rw [h2]
      have : (cv.name == ConLeche.quotSoundName) = false := by
        simpa using fun h => hno (hqs.mpr h)
      rw [this, Bool.false_or]
  | defnDecl v e h =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        obtain rfl := (Option.some.inj hd).symm
        exact one (denoteCV_inv hcv).1 hrun
  | thmDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        obtain rfl := (Option.some.inj hd).symm
        exact one (denoteCV_inv hcv).1 hrun
  | opaqueDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        obtain rfl := (Option.some.inj hd).symm
        exact one (denoteCV_inv hcv).1 hrun
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, rfl⟩ := hd
    simp only [Arena.basisNamesOk] at hrun
    obtain ⟨o, s1, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨hst1, hx1, hp1, hc1, -, hsc1, rfl⟩ := basisNameHit_run hok hb g1
    have hs1 : RStep s s1 := RStep.of_frame hst1 hx1 hsc1 hp1 hc1 hr
    have hb1 := denoteCIList_mono hx1 _ _ hb
    simp only [ConLeche.basisNamesOk]
    cases hk : ConLeche.basisNameHit b with
    | some kind =>
      rw [hk] at k1
      obtain ⟨pins, s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hs2, hP⟩ := BasisKind.decls_run hs1.ok g2
      have hs2' := RStep.of_istep hs2 hs1.read
      obtain ⟨hs3, hc⟩ := pinListOk_run hs2.ok hs2'.read
        (denoteCIList_mono hs2.ext _ _ hb1) hP k2
      exact ⟨(hs1.trans hs2').trans hs3, hc⟩
    | none =>
      rw [hk] at k1
      obtain ⟨rs, s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨rfl, hrs⟩ := reservedBasisNames_runB (hp.mono hx1 hp1) g2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      exact ⟨hs1, all_unreserved_denote hst1.wf hrs block b hb1⟩

/-! ## The pin shape comparison

con-leche's `matchesPin` is plain equality of the three fields, and the
twin compares HANDLES: the readbacks are injective, so each
handle comparison is the denotations' comparison.  The test only READS the
store, so its frame is `s' = s`. -/

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:89-91 ConstantVal.matchesPin —
**the pin comparison is con-leche's**: it is plain equality of
name, level parameters and type, and over handles each comparison is the
denotations' (the readbacks are injective). -/
theorem matchesPin_run {cv pin : IConstantVal} {c p : ConstantVal}
    {r : Bool} {s s' : AState} (hwf : StoreWF s.store)
    (hc : Frontend.denoteCV s.store cv = some c)
    (hp : Frontend.denoteCV s.store pin = some p)
    (hrun : IConstantVal.matchesPin cv pin s = .ok (r, s')) :
    s' = s ∧ r = ConLeche.ConstantVal.matchesPin c p := by
  have hwf' := hwf
  obtain ⟨rk, hrk⟩ := hwf'
  obtain ⟨hcn, hcl, hct⟩ := denoteCV_inv hc
  obtain ⟨hpn, hpl, hpt⟩ := denoteCV_inv hp
  have e1 := beq_of_denote_inj (fun h1 h2 => denoteN_inj hrk.nsWF h1 h2) hcn hpn
  have e2 := beq_of_denote_inj
    (fun h1 h2 => denoteNList_inj hwf _ _ _ h1 h2) hcl hpl
  have e3 := beq_of_denote_inj (fun h1 h2 => denoteE_inj hwf h1 h2) hct hpt
  simp only [IConstantVal.matchesPin] at hrun
  obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
  refine ⟨rfl, ?_⟩
  rw [e1, e2, e3, ConLeche.ConstantVal.matchesPin]
  congr 2 <;> exact Bool.eq_iff_iff.mpr (by simp)

/-! ## The shape tests' frame

Every shape test below is a `Bool`-valued chain of pin reads, fresh-memo
interns, index lookups and `matchesPin`s, and every link of it is a
scratch-agnostic step (`Frontend.IStepS`).  `RunsB m s b` says exactly that of
a whole chain: every success of `m` at `s` is such a step and answers `b`.  The
combinators below follow the arena's `do`-blocks link by link, so each test is
its own `do`-block read top to bottom, and con-leche's `&&`-chain is the `b`. -/

/-- con-leche: none — every success of `m` at `s` is a scratch-agnostic step
answering `b`. -/
@[expose] def RunsB (m : AM Bool) (s : AState) (b : Bool) : Prop :=
  ∀ (r : Bool) (s' : AState), m s = .ok (r, s') → Frontend.IStepS s s' ∧ r = b

theorem RunsB.ret {s : AState} (hok : StateOK s) {b : Bool} :
    RunsB (Pure.pure b) s b := by
  intro r s' h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h
  exact ⟨Frontend.IStepS.refl hok, rfl⟩

theorem RunsB.bind {α : Type} {m : AM α} {k : α → AM Bool} {s : AState}
    {b : Bool}
    (h : ∀ {a : α} {s₁ : AState}, m s = .ok (a, s₁) →
      Frontend.IStepS s s₁ ∧ RunsB (k a) s₁ b) :
    RunsB (m >>= k) s b := by
  intro r s' hr
  obtain ⟨a, s₁, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨hs1, hk⟩ := h h1
  obtain ⟨hs2, rfl⟩ := hk _ _ h2
  exact ⟨hs1.trans hs2, rfl⟩

/-- a `Bool` answered by a step, then bound. -/
theorem RunsB.bindB {m : AM Bool} {k : Bool → AM Bool} {s : AState}
    {A b : Bool}
    (hm : RunsB m s A)
    (hk : ∀ {s₁ : AState}, Frontend.IStepS s s₁ → RunsB (k A) s₁ b) :
    RunsB (m >>= k) s b :=
  RunsB.bind fun h1 => by
    obtain ⟨hs, rfl⟩ := hm _ _ h1
    exact ⟨hs, hk hs⟩

theorem RunsB.ite {c c' : Prop} [Decidable c] [Decidable c'] {X Y : AM Bool}
    {s : AState} {b1 b2 : Bool} (hc : c ↔ c')
    (h1 : c → RunsB X s b1) (h2 : ¬ c → RunsB Y s b2) :
    RunsB (if c then X else Y) s (if c' then b1 else b2) := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left (hc.mp h)]; exact h1 h
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hc.mpr h'))]; exact h2 h

/-- con-leche: none — a known view, read. -/
theorem view_run_of_some {h : EIdx} {s : AState} {v : ENodeView}
    (hv : s.store.view h = some v) : view h s = .ok (v, s) := by
  simp only [view, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, Except.bind, Except.pure, hv]

/-- con-leche: none — **the tag-first twin's test**:
`if h.tag == t then (view h >>= f) else e` runs as `view h >>= f` at a handle
whose view is known, because on the `else` side the continuation's catch-all
arm IS `e`. -/
theorem RunsB.tagView {h : EIdx} {t : UInt32} {v : ENodeView}
    {f : ENodeView → AM Bool} {e : AM Bool} {s : AState} {b : Bool}
    (hv : s.store.view h = some v) (he : v.tagOf ≠ t → f v = e)
    (hk : RunsB (view h >>= f) s b) :
    RunsB (if h.tag == t then (view h >>= f) else e) s b := by
  by_cases ht : (h.tag == t) = true
  · rw [ite_eq_left ht]; exact hk
  · rw [ite_eq_right ht]
    have hne : v.tagOf ≠ t := by rw [← EStore.tagOf_of_view hv]; simpa using ht
    intro r s' hrun
    apply hk r s'
    have hb : (view h >>= f) s = f v s := by
      show StateT.bind (view h) f s = _
      simp only [StateT.bind, view_run_of_some hv]; rfl
    rw [hb, he hne]; exact hrun

/-- a guard: `if c then pure false else Y` is `D && B` when `c` is `!D`. -/
theorem RunsB.guard {c D B : Bool} {Y : AM Bool} {s : AState}
    (hok : StateOK s) (hc : c = !D) (hY : D = true → RunsB Y s B) :
    RunsB (if c then pure false else Y) s (D && B) := by
  cases D with
  | false =>
    subst hc
    simp only [Bool.not_false, ite_true, Bool.false_and]
    exact RunsB.ret hok
  | true =>
    subst hc
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.true_and]
    exact hY rfl

theorem RunsB.matchInd {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.indInfo cvI _) => K cvI | _ => pure false) s
      ((match (generalizing := false) y with | some (.indInfo cvI _) => L cvI | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci with
    | indInfo v cap =>
      obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      exact hK v v' hv
    | axiomInfo v =>
      obtain ⟨v', rfl, -⟩ := denoteCI_axiom_inv hd; exact RunsB.ret hok
    | ctorInfo v nP nF T =>
      obtain ⟨v', rfl, -⟩ := denoteCI_ctor_inv hd; exact RunsB.ret hok
    | defnInfo v e hh =>
      obtain ⟨v', x, rfl, -⟩ := denoteCI_defn_inv hd; exact RunsB.ret hok
    | thmInfo v =>
      obtain ⟨v', rfl, -⟩ := denoteCI_thm_inv hd; exact RunsB.ret hok
    | recInfo v mI rP k rs =>
      obtain ⟨v', x, rfl, -⟩ := denoteCI_rec_inv hd; exact RunsB.ret hok

/-- The index lookups of the shape tests, one per constructor pattern. -/
theorem RunsB.matchAxiom {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.axiomInfo cv) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.axiomInfo cv) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip

theorem RunsB.matchCtor0 {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.ctorInfo cv 0 0 _) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.ctorInfo cv 0 0 _) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip
    all_goals
      rename_i nP nF _
      rcases nP with _ | nP <;> rcases nF with _ | nF <;>
        first | exact RunsB.ret hok | exact hK _ _ hv

theorem RunsB.matchCtor1 {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.ctorInfo cv 1 1 _) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.ctorInfo cv 1 1 _) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip
    all_goals
      rename_i nP nF _
      rcases nP with _ | _ | nP <;> rcases nF with _ | _ | nF <;>
        first | exact RunsB.ret hok | exact hK _ _ hv

theorem RunsB.matchCtor2 {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.ctorInfo cv 2 2 _) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.ctorInfo cv 2 2 _) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip
    all_goals
      rename_i nP nF _
      rcases nP with _ | _ | _ | nP <;> rcases nF with _ | _ | _ | nF <;>
        first | exact RunsB.ret hok | exact hK _ _ hv

theorem RunsB.matchRec3 {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.recInfo cv 3 3 _ _) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.recInfo cv 3 3 _ _) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip
    all_goals
      rename_i mI rP k rs
      rcases mI with _ | _ | _ | _ | mI <;> rcases rP with _ | _ | _ | _ | rP <;>
        first | exact RunsB.ret hok | exact hK _ _ hv

theorem RunsB.matchRec4 {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.recInfo cv 4 4 _ _) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.recInfo cv 4 4 _ _) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip
    all_goals
      rename_i mI rP k rs
      rcases mI with _ | _ | _ | _ | _ | mI <;> rcases rP with _ | _ | _ | _ | _ | rP <;>
        first | exact RunsB.ret hok | exact hK _ _ hv

/-- A stored constant compared against a freshly interned `ConstantVal` pin,
then continued. -/
theorem RunsB.pinCV {P : ConstantVal} {v : IConstantVal} {v' : ConstantVal}
    {k : Bool → AM Bool} {s : AState} {b : Bool} (hst : StateOK s)
    (hv : Frontend.denoteCV s.store v = some v')
    (hk : ∀ {s₁ : AState}, Frontend.IStepS s s₁ →
      RunsB (k (ConLeche.ConstantVal.matchesPin v' P)) s₁ b) :
    RunsB (internCV P >>= fun p => IConstantVal.matchesPin v p >>= k) s b := by
  refine RunsB.bind fun {p s₁} g1 => ?_
  obtain ⟨hs1, hp⟩ := internCV_fresh hst g1
  refine ⟨hs1, RunsB.bindB (fun _ _ h => ?_) fun hs3 => hk (hs1.trans hs3)⟩
  obtain ⟨rfl, rfl⟩ := matchesPin_run hs1.ok.wf (denoteCV_ext hv hs1.ext) hp h
  exact ⟨Frontend.IStepS.refl hs1.ok, rfl⟩

/-- The same, as the last link of a chain. -/
theorem RunsB.pinCVLast {P : ConstantVal} {v : IConstantVal} {v' : ConstantVal}
    {s : AState} (hst : StateOK s)
    (hv : Frontend.denoteCV s.store v = some v') :
    RunsB (internCV P >>= fun p => IConstantVal.matchesPin v p) s
      (ConLeche.ConstantVal.matchesPin v' P) := by
  refine RunsB.bind fun {p s₁} g1 => ?_
  obtain ⟨hs1, hp⟩ := internCV_fresh hst g1
  refine ⟨hs1, fun _ _ h => ?_⟩
  obtain ⟨rfl, rfl⟩ := matchesPin_run hs1.ok.wf (denoteCV_ext hv hs1.ext) hp h
  exact ⟨Frontend.IStepS.refl hs1.ok, rfl⟩

/-- A stored constant compared against the common data of a freshly interned
`ConstantInfo` pin, then continued. -/
theorem RunsB.pinCI {P : ConstantInfo} {v : IConstantVal} {v' : ConstantVal}
    {k : Bool → AM Bool} {s : AState} {b : Bool} (hst : StateOK s)
    (hv : Frontend.denoteCV s.store v = some v')
    (hk : ∀ {s₁ : AState}, Frontend.IStepS s s₁ →
      RunsB (k (ConLeche.ConstantVal.matchesPin v' P.toConstantVal)) s₁ b) :
    RunsB (internCI P >>= fun a => IConstantVal.matchesPin v a.toConstantVal >>= k) s b := by
  refine RunsB.bind fun {a s₁} g1 => ?_
  obtain ⟨hs1, ha⟩ := internCI_fresh hst g1
  refine ⟨hs1, RunsB.bindB (fun _ _ h => ?_) fun hs3 => hk (hs1.trans hs3)⟩
  obtain ⟨rfl, rfl⟩ := matchesPin_run hs1.ok.wf
    (denoteCV_ext hv hs1.ext) (denoteCI_toConstantVal ha) h
  exact ⟨Frontend.IStepS.refl hs1.ok, rfl⟩

/-- A pinned name read off the table, then continued. -/
theorem RunsB.pin {i : Nat} {x : ConLeche.Name} {k : NIdx → AM Bool}
    {s : AState} {b : Bool} (hst : StateOK s) (hp : PinsOK s)
    (hx : pinNames[i]? = some x)
    (hk : ∀ n, denoteN s.store.ns n = some x → RunsB (k n) s b) :
    RunsB (pinAt i >>= k) s b := by
  refine RunsB.bind fun {n s₁} g1 => ?_
  obtain ⟨rfl, d1⟩ := pinAt_run hp hx g1
  exact ⟨Frontend.IStepS.refl hst, hk n d1⟩

/-- A stored constant compared against a pin some step computes, as the last
link of a chain. -/
theorem RunsB.pinLastOf {m : AM IConstantVal} {P : ConstantVal}
    {v : IConstantVal} {v' : ConstantVal} {s : AState}
    (hv : Frontend.denoteCV s.store v = some v')
    (hm : ∀ {p : IConstantVal} {s₁ : AState}, m s = .ok (p, s₁) →
      Frontend.IStepS s s₁ ∧ Frontend.denoteCV s₁.store p = some P) :
    RunsB (m >>= fun p => IConstantVal.matchesPin v p) s
      (ConLeche.ConstantVal.matchesPin v' P) := by
  refine RunsB.bind fun {p s₁} g1 => ?_
  obtain ⟨hs1, hp⟩ := hm g1
  refine ⟨hs1, fun _ _ h => ?_⟩
  obtain ⟨rfl, rfl⟩ := matchesPin_run hs1.ok.wf (denoteCV_ext hv hs1.ext) hp h
  exact ⟨Frontend.IStepS.refl hs1.ok, rfl⟩

theorem RunsB.and_true {m : AM Bool} {s : AState} {b : Bool}
    (h : RunsB m s (b && true)) : RunsB m s b := by
  rwa [Bool.and_true] at h

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:73-77 ofReduceOp — the reduce
operation an `ofReduce*` axiom speaks about, a handle comparison here. -/
theorem ofReduceOp_run {n c : NIdx} {nm : ConLeche.Name} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hd : denoteN s.store.ns n = some nm)
    (hrun : Arena.ofReduceOp n s = .ok (c, s')) :
    s' = s ∧ denoteN s.store.ns c = some (ConLeche.ofReduceOp nm) := by
  simp only [Arena.ofReduceOp] at hrun
  obtain ⟨orn, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.ofReduceNatName) hp (by rfl) g1
  have hiff := beq_handle_iff hst.wf hd d1
  rcases AM.ite_ok r1 with ⟨hc, k⟩ | ⟨hc, k⟩
  · obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.reduceNatName) hp (by rfl) k
    refine ⟨rfl, ?_⟩
    rw [d2, ConLeche.ofReduceOp, ite_eq_left (hiff.mp hc)]
  · obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.reduceBoolName) hp (by rfl) k
    refine ⟨rfl, ?_⟩
    rw [d2, ConLeche.ofReduceOp, ite_eq_right (fun h => hc (hiff.mpr h))]

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:131-133 reduceOpCvA — the
annotated pinned type of a reduce operation, interned. -/
theorem reduceOpCvA_run {cH : NIdx} {cn : ConLeche.Name} {v : IConstantVal}
    {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hd : denoteN s.store.ns cH = some cn)
    (hrun : Arena.reduceOpCvA cH s = .ok (v, s')) :
    Frontend.IStepS s s' ∧
      Frontend.denoteCV s'.store v = some (ConLeche.reduceOpCvA cn) := by
  simp only [Arena.reduceOpCvA] at hrun
  obtain ⟨rn, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.reduceNatName) hp (by rfl) g1
  have hiff := beq_handle_iff hst.wf hd d1
  rcases AM.ite_ok r1 with ⟨hc, k⟩ | ⟨hc, k⟩
  · obtain ⟨hs, hv⟩ := internCV_fresh hst k
    refine ⟨hs, ?_⟩
    rw [hv, ConLeche.reduceOpCvA, ite_eq_left (hiff.mp hc)]
  · obtain ⟨hs, hv⟩ := internCV_fresh hst k
    refine ⟨hs, ?_⟩
    rw [hv, ConLeche.reduceOpCvA, ite_eq_right (fun h => hc (hiff.mpr h))]

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:135-137 ofReducePinA — the
pin an `ofReduce*` axiom is matched against, interned. -/
theorem ofReducePinA_run {nH : NIdx} {nm : ConLeche.Name} {v : IConstantVal}
    {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hd : denoteN s.store.ns nH = some nm)
    (hrun : Arena.ofReducePinA nH s = .ok (v, s')) :
    Frontend.IStepS s s' ∧
      Frontend.denoteCV s'.store v = some (ConLeche.ofReducePinA nm) := by
  simp only [Arena.ofReducePinA] at hrun
  obtain ⟨rn, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.ofReduceNatName) hp (by rfl) g1
  have hiff := beq_handle_iff hst.wf hd d1
  rcases AM.ite_ok r1 with ⟨hc, k⟩ | ⟨hc, k⟩
  · obtain ⟨hs, hv⟩ := internCV_fresh hst k
    refine ⟨hs, ?_⟩
    rw [hv, ConLeche.ofReducePinA, ite_eq_left (hiff.mp hc)]
  · obtain ⟨hs, hv⟩ := internCV_fresh hst k
    refine ⟨hs, ?_⟩
    rw [hv, ConLeche.ofReducePinA, ite_eq_right (fun h => hc (hiff.mpr h))]

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:162-172 reduceElemOk — the
element inductive's shape test is con-leche's: a stored inductive compared
with a pin's `ConstantVal`, at `Nat` and at `Bool`. -/
theorem reduceElemOk_run {env : Env} {fe : IFEnv} {cH : NIdx}
    {cn : ConLeche.Name} {s : AState} (hst : StateOK s) (hp : PinsOK s)
    (hie : IFEnvOK env fe s) (hd : denoteN s.store.ns cH = some cn) :
    RunsB (Arena.reduceElemOk fe cH) s (ConLeche.reduceElemOk env cn) := by
  unfold Arena.reduceElemOk ConLeche.reduceElemOk
  refine RunsB.pin hst hp (x := ConLeche.reduceNatName) (by rfl) fun rn drn => ?_
  refine RunsB.ite (beq_handle_iff hst.wf hd drn) (fun _ => ?_) (fun _ => ?_)
  · refine RunsB.pin hst hp (x := ConLeche.natName) (by rfl) fun nn dnn => ?_
    refine RunsB.and_true
      (RunsB.matchInd hst (hie.findRel hst dnn) fun v v' hv => ?_)
    rw [Bool.and_true]
    have e : (Arena.natA >>= fun a => IConstantVal.matchesPin v a.toConstantVal) =
        (internCI ConLeche.natA >>= fun a => IConstantVal.matchesPin v a.toConstantVal >>=
          fun b => pure b) := by
      simp only [Arena.natA, bind_pure]
    rw [e]
    exact RunsB.pinCI hst hv fun hs1 => RunsB.ret hs1.ok
  · refine RunsB.pin hst hp (x := ConLeche.boolName) (by rfl) fun bn dbn => ?_
    refine RunsB.and_true
      (RunsB.matchInd hst (hie.findRel hst dbn) fun v v' hv => ?_)
    rw [Bool.and_true]
    exact RunsB.pinCVLast hst hv

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:154-160 reduceStoredOk — the
stored reduce operation's shape test is con-leche's. -/
theorem reduceStoredOk_run {env : Env} {fe : IFEnv} {cH : NIdx}
    {cn : ConLeche.Name} {s : AState} (hst : StateOK s) (hp : PinsOK s)
    (hie : IFEnvOK env fe s) (hd : denoteN s.store.ns cH = some cn) :
    RunsB (Arena.reduceStoredOk fe cH) s (ConLeche.reduceStoredOk env cn) := by
  unfold Arena.reduceStoredOk ConLeche.reduceStoredOk
  refine RunsB.and_true
    (RunsB.matchAxiom hst (hie.findRel hst hd) fun v v' hv => ?_)
  rw [Bool.and_true]
  exact RunsB.pinLastOf hv fun h => reduceOpCvA_run hst hp hd h

theorem RunsB.matchDefn {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.defnInfo cv _ _) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.defnInfo cv _ _) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip

/-- The dual guard: `if c then Y else pure false` is `D && B` when `c` is
`D`. -/
theorem RunsB.guardT {c D B : Bool} {Y : AM Bool} {s : AState}
    (hok : StateOK s) (hc : c = D) (hY : D = true → RunsB Y s B) :
    RunsB (if c then Y else pure false) s (D && B) := by
  subst hc
  cases c with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Bool.false_and]
    exact RunsB.ret hok
  | true =>
    simp only [ite_true, Bool.true_and]
    exact hY rfl

/-- `natOpCod`'s `Bool` lookup: the stored `Bool`'s level parameters and type,
read through `IConstantInfo.toConstantVal`, against the pinned `Sort 1`. -/
theorem RunsB.matchCod {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hp : PinsOK s) (hxy : FindRel s.store x y) :
    RunsB (match (generalizing := false) x with
        | some ci => do
          let cv := ci.toConstantVal
          let s1 ← sortOne
          pure (cv.levelParams.isEmpty && cv.type == s1)
        | none => pure false) s
      (match (generalizing := false) y with
        | some ci => ci.toConstantVal.levelParams.isEmpty &&
            ci.toConstantVal.type == .sort (.succ .zero)
        | none => false) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · have hs1 := Frontend.IStepS.refl hok
    have hv := denoteCI_toConstantVal hd
    refine RunsB.bind fun {e s₂} g2 => ?_
    obtain ⟨rfl, he⟩ := AM.of_run (P := fun t => t = s)
      (Q := fun r t => t = s ∧ denoteE s.store r = some (.sort (.succ .zero)))
      rfl g2 (pinSortOne_spec s (hp.mono hs1.ext hs1.pins))
    refine ⟨Frontend.IStepS.refl hs1.ok, ?_⟩
    obtain ⟨-, hl, hty⟩ := denoteCV_inv hv
    have hlen := denoteNList_length _ _ hl
    have h1 : ci.toConstantVal.levelParams.isEmpty = c.toConstantVal.levelParams.isEmpty := by
      cases h1 : ci.toConstantVal.levelParams <;> cases h2 : c.toConstantVal.levelParams <;>
        simp_all
    have h2 : (ci.toConstantVal.type == e) = (c.toConstantVal.type == .sort (.succ .zero)) :=
      beq_of_denote_inj (fun h1 h2 => denoteE_inj hs1.ok.wf h1 h2) hty he
    rw [h1, h2]
    exact RunsB.ret hs1.ok

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk (the
`(env.find? eqName).isSome` conjunct, which `ofReduceAxOk` shares) — the
presence test is the environment's. -/
theorem eqStored_run {env : Env} {fe : IFEnv} {s : AState} (hst : StateOK s)
    (hp : PinsOK s) (hie : IFEnvOK env fe s) :
    RunsB (eqStored fe) s (env.find? ConLeche.eqName).isSome := by
  unfold Arena.eqStored pinEq
  refine RunsB.pin hst hp (x := ConLeche.eqName) (by rfl) fun en den => ?_
  rw [← (hie.findRel hst den).isSome]
  exact RunsB.ret hst

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk — the standard
axioms' environment shape test is con-leche's.

**Proof:** the `do`-block read link by link
through the `RunsB` combinators — `pinAt_run` per pinned name, `IFEnvOK.findRel`
per index lookup, `matchesPin_run` per shape
comparison, and `eqStored_run` for the `Eq` presence test. -/
theorem stdAxiomOk_run {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : stdAxiomOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.stdAxiomOk env c := by
  have hst := hok.check.state
  suffices h : RunsB (stdAxiomOk fe cvA) s (ConLeche.stdAxiomOk env c) by
    obtain ⟨hs, rfl⟩ := h _ _ hrun
    exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, rfl⟩
  have tr : ∀ {t : AState}, Frontend.IStepS s t →
      StateOK t ∧ PinsOK t ∧ IFEnvOK env fe t ∧
        Frontend.denoteCV t.store cvA = some c := fun ht =>
    ⟨ht.ok, hok.check.pins.mono ht.ext ht.pins, hok.check.ienv.mono ht.ext,
      denoteCV_ext hcv ht.ext⟩
  have hnm := (denoteCV_inv hcv).1
  simp only [ConLeche.stdAxiomOk, Bool.and_assoc]
  unfold Arena.stdAxiomOk
  obtain ⟨hst0, hp0, hie0, -⟩ := tr (Frontend.IStepS.refl hst)
  refine RunsB.pin hst hp0 (x := ConLeche.propextName) (by rfl) fun pn dpn => ?_
  refine RunsB.ite (beq_handle_iff hst.wf hnm dpn) (fun _ => ?_) (fun _ => ?_)
  · -- `propext`, over the pinned `Eq` basis and the `Iff` family
    refine RunsB.bindB (eqStored_run hst hp0 hie0) fun {s1} hs1 => ?_
    obtain ⟨st1, hp1, hie1, -⟩ := tr hs1
    refine RunsB.guard st1 rfl fun _ => ?_
    refine RunsB.pin st1 hp1 (x := ConLeche.iffName) (by rfl) fun n2 d2 => ?_
    refine RunsB.matchInd st1 (hie1.findRel st1 d2) fun v v' hv => ?_
    refine RunsB.pinCI st1 hv fun {s3} hs3 => ?_
    obtain ⟨st3, hp3, hie3, -⟩ := tr (hs1.trans hs3)
    refine RunsB.guard st3 (by simp) fun _ => ?_
    refine RunsB.pin st3 hp3 (x := ConLeche.iffIntroName) (by rfl) fun n4 d4 => ?_
    refine RunsB.matchCtor2 st3 (hie3.findRel st3 d4) fun w w' hw => ?_
    refine RunsB.pinCI st3 hw fun {s5} hs5 => ?_
    obtain ⟨st5, hp5, hie5, -⟩ := tr ((hs1.trans hs3).trans hs5)
    refine RunsB.guard st5 (by simp) fun _ => ?_
    refine RunsB.pin st5 hp5 (x := ConLeche.iffRecName) (by rfl) fun n6 d6 => ?_
    refine RunsB.matchRec4 st5 (hie5.findRel st5 d6) fun u u' hu => ?_
    refine RunsB.pinCI st5 hu fun {s7} hs7 => ?_
    obtain ⟨st7, -, -, hcv7⟩ := tr (((hs1.trans hs3).trans hs5).trans hs7)
    refine RunsB.guard st7 (by simp) fun _ => ?_
    exact RunsB.pinCVLast st7 hcv7
  · refine RunsB.pin hst hp0 (x := ConLeche.choiceName) (by rfl) fun cn dcn => ?_
    refine RunsB.ite (beq_handle_iff hst.wf hnm dcn) (fun _ => ?_)
      (fun _ => RunsB.ret hst)
    -- `Classical.choice`, over the `Nonempty` family
    refine RunsB.pin hst hp0 (x := ConLeche.nonemptyName) (by rfl) fun n2 d2 => ?_
    refine RunsB.matchInd hst (hie0.findRel hst d2) fun v v' hv => ?_
    refine RunsB.pinCI hst hv fun {s3} hs3 => ?_
    obtain ⟨st3, hp3, hie3, -⟩ := tr hs3
    refine RunsB.guard st3 (by simp) fun _ => ?_
    refine RunsB.pin st3 hp3 (x := ConLeche.nonemptyIntroName) (by rfl) fun n4 d4 => ?_
    refine RunsB.matchCtor1 st3 (hie3.findRel st3 d4) fun w w' hw => ?_
    refine RunsB.pinCI st3 hw fun {s5} hs5 => ?_
    obtain ⟨st5, hp5, hie5, -⟩ := tr (hs3.trans hs5)
    refine RunsB.guard st5 (by simp) fun _ => ?_
    refine RunsB.pin st5 hp5 (x := ConLeche.nonemptyRecName) (by rfl) fun n6 d6 => ?_
    refine RunsB.matchRec3 st5 (hie5.findRel st5 d6) fun u u' hu => ?_
    refine RunsB.pinCI st5 hu fun {s7} hs7 => ?_
    obtain ⟨st7, -, -, hcv7⟩ := tr ((hs3.trans hs5).trans hs7)
    refine RunsB.guard st7 (by simp) fun _ => ?_
    exact RunsB.pinCVLast st7 hcv7

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:141-152 trustCompilerOk — the
`Lean.trustCompiler` environment shape test is con-leche's.

**Proof:** exactly as `stdAxiomOk_run`. -/
theorem trustCompilerOk_run {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : trustCompilerOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.trustCompilerOk env c := by
  have hst := hok.check.state
  suffices h : RunsB (trustCompilerOk fe cvA) s (ConLeche.trustCompilerOk env c) by
    obtain ⟨hs, rfl⟩ := h _ _ hrun
    exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, rfl⟩
  have hie := hok.check.ienv
  simp only [ConLeche.trustCompilerOk, Bool.and_assoc]
  unfold Arena.trustCompilerOk
  refine RunsB.pin hst hok.check.pins (x := ConLeche.trueName) (by rfl) fun n1 d1 => ?_
  refine RunsB.matchInd hst (hie.findRel hst d1) fun v v' hv => ?_
  refine RunsB.pinCV hst hv fun {s2} hs2 => ?_
  refine RunsB.guard hs2.ok (by simp) fun _ => ?_
  refine RunsB.pin hs2.ok (hok.check.pins.mono hs2.ext hs2.pins) (x := ConLeche.trueIntroName)
    (by rfl) fun n2 d2 => ?_
  refine RunsB.matchCtor0 hs2.ok ((hie.mono hs2.ext).findRel hs2.ok d2)
    fun w w' hw => ?_
  refine RunsB.pinCV hs2.ok hw fun {s3} hs3 => ?_
  refine RunsB.guard hs3.ok (by simp) fun _ => ?_
  exact RunsB.pinCVLast hs3.ok (denoteCV_ext hcv (hs2.ext.trans hs3.ext))

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:171-181 ofReduceAxOk — the
`Lean.ofReduceNat`/`ofReduceBool` environment shape test is con-leche's.

**Proof:** `ofReduceOp_run`, the `Eq` basis
test, then `reduceElemOk_run` / `reduceStoredOk_run` and the pinned type. -/
theorem ofReduceAxOk_run {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : ofReduceAxOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.ofReduceAxOk env c := by
  have hst := hok.check.state
  suffices h : RunsB (ofReduceAxOk fe cvA) s (ConLeche.ofReduceAxOk env c) by
    obtain ⟨hs, rfl⟩ := h _ _ hrun
    exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, rfl⟩
  have tr : ∀ {t : AState}, Frontend.IStepS s t →
      StateOK t ∧ PinsOK t ∧ IFEnvOK env fe t ∧
        Frontend.denoteCV t.store cvA = some c := fun ht =>
    ⟨ht.ok, hok.check.pins.mono ht.ext ht.pins, hok.check.ienv.mono ht.ext,
      denoteCV_ext hcv ht.ext⟩
  have hnm := (denoteCV_inv hcv).1
  simp only [ConLeche.ofReduceAxOk, Bool.and_assoc]
  unfold Arena.ofReduceAxOk
  obtain ⟨-, hp0, -, -⟩ := tr (Frontend.IStepS.refl hst)
  refine RunsB.bind fun {cH s0} g0 => ?_
  obtain ⟨rfl, dc⟩ := ofReduceOp_run hst hp0 hnm g0
  refine ⟨Frontend.IStepS.refl hst, ?_⟩
  obtain ⟨-, -, hie0, -⟩ := tr (Frontend.IStepS.refl hst)
  refine RunsB.bindB (eqStored_run hst hp0 hie0) fun {s1} hs1 => ?_
  obtain ⟨st1, hp1, hie1, -⟩ := tr hs1
  refine RunsB.guard st1 rfl fun _ => ?_
  refine RunsB.bindB (reduceElemOk_run st1 hp1 hie1 (denoteN_ext dc hs1.ext))
    fun {s2} hs2 => ?_
  obtain ⟨st2, hp2, hie2, -⟩ := tr (hs1.trans hs2)
  refine RunsB.guard st2 (by simp) fun _ => ?_
  refine RunsB.bindB
    (reduceStoredOk_run st2 hp2 hie2 (denoteN_ext dc (hs1.trans hs2).ext))
    fun {s3} hs3 => ?_
  obtain ⟨st3, hp3, -, hcv3⟩ := tr ((hs1.trans hs2).trans hs3)
  refine RunsB.guard st3 (by simp) fun _ => ?_
  exact RunsB.pinLastOf hcv3 fun h =>
    ofReducePinA_run st3 hp3 (denoteCV_inv hcv3).1 h

/-! ## The pinned `And` (con-leche's ANDPIN)

The fold asks `andPinOk` of every record before its dispatch
(`Arena.checkDeclStep`).  Theorem 1 is about ACCEPTING runs, and con-leche's
soundness chain never reads the test (`Cached/Installed.lean`'s note on
the install step: the stuck-proof rescue it keeps available is sound for any
`And`), so what the fold theorem needs of it is the frame: an accepting test
only grew the store, and moved neither the caches nor the pin table. -/

/-- con-leche: ConLeche/Kernel/Basis/And.lean:97-99 andPinNames — the three
slot reads move nothing. -/
theorem andPinNameHs_run {hs : List NIdx} {s s' : AState} (hp : PinsOK s)
    (hrun : andPinNameHs s = .ok (hs, s')) : s' = s := by
  simp only [ConRon.Arena.andPinNameHs, pinAnd, pinAndIntro, pinAndRec] at hrun
  obtain ⟨a, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, -⟩ := pinAt_run (x := ConLeche.andName) hp rfl g1
  obtain ⟨i, s₂, g2, k2⟩ := AM.bind_ok k1
  obtain ⟨rfl, -⟩ := pinAt_run (x := ConLeche.andIntroName) hp rfl g2
  obtain ⟨r, s₃, g3, k3⟩ := AM.bind_ok k2
  obtain ⟨rfl, -⟩ := pinAt_run (x := ConLeche.andRecName) hp rfl g3
  exact (AM.pure_ok k3).2

/-- con-leche: ConLeche/Kernel/Basis.lean:186-194 andPinOk — the one-constant
arm moves nothing. -/
theorem andPinNameFree_run {n : NIdx} {r : Bool} {s s' : AState} (hp : PinsOK s)
    (hrun : andPinNameFree n s = .ok (r, s')) : s' = s := by
  simp only [ConRon.Arena.andPinNameFree] at hrun
  obtain ⟨hs, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain rfl := andPinNameHs_run hp g1
  exact (AM.pure_ok k1).2

/-- con-leche: ConLeche/Kernel/Basis.lean:186-194 andPinOk — **the fold's `And`
pin, as a frame**: the test only grows the store (the pinned block is interned
and compared with `canonEqList` when a block declares one of its names) and
moves neither the caches nor the pin table. -/
theorem andPinOk_run {pd : IDeclaration} {d : Declaration} {r : Bool}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : andPinOk pd s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins := by
  have hfree : ∀ {n : NIdx}, andPinNameFree n s = .ok (r, s') →
      StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
        s'.pins = s.pins := fun h => by
    obtain rfl := andPinNameFree_run hp h
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  cases pd with
  | axiomDecl cv => exact hfree hrun
  | defnDecl cv _ _ => exact hfree hrun
  | thmDecl cv _ => exact hfree hrun
  | opaqueDecl cv _ => exact hfree hrun
  | quotDecl _ cv => exact hfree hrun
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, -⟩ := hd
    simp only [ConRon.Arena.andPinOk] at hrun
    obtain ⟨hs, s₁, g1, k1⟩ := AM.bind_ok hrun
    obtain rfl := andPinNameHs_run hp g1
    rcases AM.ite_ok k1 with ⟨-, k2⟩ | ⟨-, k2⟩
    · rcases AM.ite_ok k2 with ⟨-, k3⟩ | ⟨-, k3⟩
      · obtain ⟨pinned, s₂, g2, k4⟩ := AM.bind_ok k3
        simp only [ConRon.Arena.andPinDecls, ConRon.Arena.internCIList] at g2
        obtain ⟨p, s₃, hgo, hrest⟩ := AM.bind_ok g2
        obtain ⟨m1, cis⟩ := p
        obtain ⟨hv, hst⟩ := AM.pure_ok hrest
        subst hv; subst hst
        obtain ⟨hstep, hdp, -⟩ :=
          Frontend.internCIList_sstep ConLeche.andPin hok
            (Frontend.EMemoOK.empty _) hgo
        obtain ⟨hok2, hx2, hc2, hp2, -⟩ :=
          canonEqList_run hstep.ok (denoteCIList_mono hstep.ext _ _ hb) hdp k4
        exact ⟨hok2, hstep.ext.trans hx2, by rw [hc2, hstep.caches],
          by rw [hp2, hstep.pins]⟩
      · obtain ⟨-, rfl⟩ := AM.pure_ok k3
        exact ⟨hok, Ext.refl _, rfl, rfl⟩
    · obtain ⟨-, rfl⟩ := AM.pure_ok k2
      exact ⟨hok, Ext.refl _, rfl, rfl⟩

end ConRon.Bridge
