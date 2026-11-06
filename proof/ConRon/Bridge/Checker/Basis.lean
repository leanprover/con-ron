/-
# `ConRon.Bridge.Checker.Basis` — the pinned blocks and the axiom installs

Three things that share a shape: they compare a stream record against a
BUILD-TIME literal.

* `Arena/Basis.lean` — `BasisKind.decls` (the pinned blocks, interned), a pin
  at a stream's level-parameter names (`IConstantInfo.atLps`), the block's
  comparison with its pin (`pinListOk`), the name test (`basisNameHit`), what a
  pinned block and a quotient record store (`BasisKind.atBlock`, `quotAt`), and
  the quotient record's own tests (`quotPinHit`, `quotPredsOk`);
* `Arena/DeclCheck.lean` — the pinned block's and the quotient record's check
  (`checkBasisBlock`, `checkQuotRecord`) and the standard / compiler-trust
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

/-- con-leche: ConLeche/Kernel/Canon.lean:290-294 listBeqBy — at an `f` that is
equality, it is equality. -/
theorem listBeqBy_eq {α : Type} [BEq α] [LawfulBEq α] {f : α → α → Bool}
    (hf : ∀ a b, f a b = (a == b)) :
    ∀ l l' : List α, ConLeche.listBeqBy f l l' = (l == l') := by
  intro l
  induction l with
  | nil => intro l'; cases l' <;> rfl
  | cons a as ih =>
    intro l'
    cases l' with
    | nil => rfl
    | cons b bs =>
      simp only [ConLeche.listBeqBy, hf, ih, List.cons_beq_cons]

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
  cases he : denoteN st.ns cap.etaCtor with
  | none => rw [he] at hc; simp at hc
  | some ct =>
    cases he' : denoteN st.ns cap'.etaCtor with
    | none => rw [he'] at hc'; simp at hc'
    | some ct' =>
      cases ha : Frontend.denoteNList st.ns cap.all with
      | none => rw [he, ha] at hc; simp at hc
      | some al =>
      cases ha' : Frontend.denoteNList st.ns cap'.all with
      | none => rw [he', ha'] at hc'; simp at hc'
      | some al' =>
      cases hk : Frontend.denoteNList st.ns cap.ctors with
      | none => rw [he, ha, hk] at hc; simp at hc
      | some ks =>
      cases hk' : Frontend.denoteNList st.ns cap'.ctors with
      | none => rw [he', ha', hk'] at hc'; simp at hc'
      | some ks' =>
      rw [he, ha, hk] at hc; rw [he', ha', hk'] at hc'
      rw [← hc'] at hc
      simp only [Option.some.injEq, IndCaps.mk.injEq] at hc
      obtain ⟨e1, rfl, e3, e4, e5, e6, rfl, e8, e9, rfl⟩ := hc
      have := denoteN_inj hrk.nsWF he he'
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
    | ctorInfo w _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv h'; cases he
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
    | ctorInfo w _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv h'; cases he
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
    | ctorInfo w _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv h'; cases he
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
    | ctorInfo w _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv h'; cases he
    | recInfo w _ _ _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_rec_inv h'; cases he
  | ctorInfo v nP nF =>
    obtain ⟨cv, rfl, hv⟩ := denoteCI_ctor_inv h
    cases ci' with
    | ctorInfo w nP' nF' =>
      obtain ⟨cw, he, hw⟩ := denoteCI_ctor_inv h'
      cases he; rw [denoteCV_inj hwf hv hw]
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
    | ctorInfo w _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv h'; cases he

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
  | ctorInfo v nP nF =>
    obtain ⟨cv, rfl, hv⟩ := denoteCI_ctor_inv hc
    simp only [IConstantInfo.atLps] at hrun
    obtain ⟨v2, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    obtain ⟨hs1, hv2⟩ := IConstantVal.atLps_run hok hr hv hps h1
    exact ⟨hs1, by simp [Frontend.denoteCI, hv2, ConLeche.ConstantInfo.atLps]⟩
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
    | .ctorInfo cv _ _, _ => cv.levelParams == former
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
  | ctorInfo v nP nF =>
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
    | ctorInfo _ _ _ =>
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

/-- con-leche: ConLeche/Kernel/Basis.lean:138-141 BasisKind.atBlock — the cited
`List.zipWith`. -/
theorem atBlockGo_run :
    ∀ (pins cs : List IConstantInfo) {P zs : List ConstantInfo} {r : List IConstantInfo}
      {s s' : AState},
      StateOK s → ReadOK s →
      Frontend.denoteCIList s.store pins = some P →
      Frontend.denoteCIList s.store cs = some zs →
      atBlockGo pins cs s = .ok (r, s') →
      RStep s s' ∧ Frontend.denoteCIList s'.store r =
        some (List.zipWith (fun pin c => pin.atLps c.toConstantVal.levelParams) P zs) := by
  intro pins
  induction pins with
  | nil =>
    intro cs P zs r s s' hok hr hP _ hrun
    simp only [Frontend.denoteCIList, Option.some.injEq] at hP
    subst hP
    simp only [atBlockGo] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨RStep.refl hok hr, rfl⟩
  | cons pin pins ih =>
    intro cs P zs r s s' hok hr hP hzs hrun
    obtain ⟨p, P', hp, hP', rfl⟩ := denoteCIList_cons hP
    cases cs with
    | nil =>
      simp only [Frontend.denoteCIList, Option.some.injEq] at hzs
      subst hzs
      simp only [atBlockGo] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨RStep.refl hok hr, rfl⟩
    | cons c cs =>
      obtain ⟨z, zs', hz, hzs', rfl⟩ := denoteCIList_cons hzs
      simp only [atBlockGo] at hrun
      obtain ⟨x, s₁, g1, k1⟩ := AM.bind_ok hrun
      obtain ⟨hs1, hx⟩ := IConstantInfo.atLps_run hok hr hp
        (denoteCV_inv (denoteCI_toConstantVal hz)).2.1 g1
      obtain ⟨rest, s₂, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hs2, hrest⟩ := ih cs hs1.ok hs1.read (denoteCIList_mono hs1.ext _ _ hP')
        (denoteCIList_mono hs1.ext _ _ hzs') g2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      refine ⟨hs1.trans hs2, ?_⟩
      simp only [Frontend.denoteCIList, denoteCI_ext hx hs2.ext, hrest,
        List.zipWith_cons_cons]

/-- con-leche: ConLeche/Kernel/Basis.lean:138-141 BasisKind.atBlock — **what a
pinned block's check installs**: each pin at the names its record declares.
The arena's list denotes con-leche's. -/
theorem BasisKind.atBlock_run {kind : BasisKind} {block : List IConstantInfo}
    {b : List ConstantInfo} {L : List IConstantInfo} {s s' : AState}
    (hok : StateOK s) (hr : ReadOK s)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hrun : Arena.BasisKind.atBlock kind block s = .ok (L, s')) :
    RStep s s' ∧ Frontend.denoteCIList s'.store L = some (kind.atBlock b) := by
  simp only [Arena.BasisKind.atBlock] at hrun
  obtain ⟨pins, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hP⟩ := BasisKind.decls_run hok g1
  obtain ⟨hs2, hL⟩ := atBlockGo_run pins block hs1.ok (RStep.of_istep hs1 hr).read hP
    (denoteCIList_mono hs1.ext _ _ hb) k1
  exact ⟨(RStep.of_istep hs1 hr).trans hs2, hL⟩

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

/-- con-leche: ConLeche/Kernel/Checker.lean:24-28 installBasisDecl
con-leche: ConLeche/Kernel/Checker.lean:467-470 checkBasisBlock — **the block,
one constant at a time**, against con-leche's `foldlM`.  The duplicate test
reads the index through `IFEnvOK`, which survives each push
(`IFEnvOK.pushStored`). -/
theorem installBasisDecls_bridge :
    ∀ (cis : List IConstantInfo) (xs : List ConstantInfo) {env : Env}
      {fe fe' : IFEnv} {s s' : AState},
      StateOK s → IFEnvOK env fe s → TblGate fe → TablesStored env →
      Frontend.denoteCIList s.store cis = some xs →
      installBasisDecls fe cis s = .ok (fe', s') →
      s' = s ∧ ∃ env', xs.foldlM (ConLeche.installBasisDecl (m := CheckM)) env = .ok env' := by
  intro cis
  induction cis with
  | nil =>
    intro xs env fe fe' s s' _ _ _ _ hcs hrun
    simp only [Frontend.denoteCIList, Option.some.injEq] at hcs
    subst hcs
    simp only [ConRon.Arena.installBasisDecls] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, env, rfl⟩
  | cons a as ih =>
    intro xs env fe fe' s s' hst hie hgate htS hcs hrun
    obtain ⟨x, xt, hx, hxt, rfl⟩ := denoteCIList_cons hcs
    simp only [ConRon.Arena.installBasisDecls] at hrun
    obtain ⟨fe1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    simp only [ConRon.Arena.installBasisDecl] at h1
    obtain ⟨hdup, r1⟩ := AM.dunless_ok AM.Never.fail_any h1
    replace r1 := AM.pure_bind_ok r1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
    have hfind : fe.find? a.name = none := by
      cases hf : fe.find? a.name with
      | none => rfl
      | some d => rw [hf] at hdup; exact absurd hdup (by simp)
    have hfindP : env.find? x.name = none := IFEnvOK.miss hst hie (denoteCI_name hx) hfind
    obtain ⟨rfl, env', hfold⟩ :=
      ih xt hst (hie.pushStored hst hgate htS hx) (hgate.push a) htS.cons hxt hrest
    refine ⟨rfl, env', ?_⟩
    simp only [List.foldlM_cons, ConLeche.installBasisDecl, hfindP,
      Option.isNone_none, bind, Except.bind, pure, Except.pure]
    exact hfold

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:157-163 checkDecl (the `.indDecl`
arm at a pinned block's names)
con-leche: ConLeche/Kernel/Checker.lean:463-470 checkBasisBlock — **a pinned
block's check and install**: the records compared with the pin
(`pinListOk_run`), each pin installed at the names its record declares
(`BasisKind.atBlock_run`, `installBasisDecls_bridge`).  The conclusion is the
arm's: con-leche's `checkDecl` accepts the denoted `indDecl`. -/
theorem checkBasisBlock_bridge {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {kind : BasisKind} {block : List IConstantInfo}
    {b : List ConstantInfo} {nP : Nat} {s s' : AState}
    (hok : FoldOK env fe s)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hhit : ConLeche.basisNameHit b = some kind)
    (hrun : checkBasisBlock fe kind block s = .ok (fe', s')) :
    DeclOut pinsP env (.indDecl b nP) s s' := by
  have hst := hok.check.state
  have hr := hok.check.readOK
  simp only [Arena.checkBasisBlock] at hrun
  obtain ⟨pins, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hP⟩ := BasisKind.decls_run hst g1
  have hs1' := RStep.of_istep hs1 hr
  obtain ⟨c, s₂, g2, k2⟩ := AM.bind_ok k1
  obtain ⟨hs2, hc⟩ := pinListOk_run hs1.ok hs1'.read
    (denoteCIList_mono hs1.ext _ _ hb) hP g2
  obtain ⟨hy, k3⟩ := AM.dunless_ok AM.Never.fail_any k2
  replace k3 := AM.pure_bind_ok k3
  have hpin : ConLeche.pinListOk b kind.decls = true := by rw [← hc]; simpa using hy
  obtain ⟨L, s₃, g3, k4⟩ := AM.bind_ok k3
  have hs12 := hs1'.trans hs2
  obtain ⟨hs3, hL⟩ := BasisKind.atBlock_run hs2.ok hs2.read
    (denoteCIList_mono hs12.ext _ _ hb) g3
  have hs13 := hs12.trans hs3
  obtain ⟨rfl, env', hfold⟩ := installBasisDecls_bridge L _ hs3.ok
    (hok.check.ienv.mono hs13.ext) hok.gate (TablesStored.of_envWF hok.envWF) hL k4
  refine { state := hs3.ok, ext := hs13.ext, pins := hs13.pins, run := ⟨env', 0, ?_⟩ }
  simp only [ConLeche.checkDecl, hhit, ConLeche.checkBasisBlock, hpin]
  exact hfold

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

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:183 checkDecl (the `.quotDecl`
arm) — it IS `checkQuotRecord`, on both sides. -/
theorem checkDecl_bridge_quot {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {env : Env} {fe fe' : IFEnv} {k : QuotKind} {v : IConstantVal}
    {cv : ConstantVal} {s s' : AState}
    (hok : FoldOK env fe s) (hv : Frontend.denoteCV s.store v = some cv)
    (hrun : Arena.checkDecl .verified pins fe (.quotDecl k v) s = .ok (fe', s')) :
    DeclOut pinsP env (.quotDecl k cv) s s' := by
  simp only [Arena.checkDecl] at hrun
  obtain ⟨h1, h2, h3, env', h4⟩ := checkQuotRecord_bridge hok hv hrun
  exact { state := h1, ext := h2, pins := h3,
          run := ⟨env', 0, by simp only [ConLeche.checkDecl]; exact h4⟩ }

end ConRon.Bridge
