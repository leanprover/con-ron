/-
# `ConRon.Bridge.Frontend.ProjRecOwners` — the owner census, at its exact
letter (task #97-P3-Frontend round 8)

`Arena/Frontend/ProjRec.lean`'s `projRecOwners` against con-leche's
(`ConLeche/Frontend/ProjRec.lean:344-370`).  Moved out of
`Bridge/Frontend/ProjRec.lean` because the census's cone needs the Inductives
tier's recognisers (`structPartsCore?_isSome`, `nativeParts?_isSome`) and its
run-form lemmas at `PStep`, which that module does not import.

## The frame

Everything is composed at `Bridge/Inductives/Rel.lean`'s `PStep`; the one
clause `PStep` does not have — the scratch flag — is
`Bridge/Frontend/Scratch.lean`'s `projRecOwners_scratch`, and the parse's
`ParseStep` is assembled from the two at the end.

## The pieces

* `projRecCandidates_run` — the twin's explicit recursion against con-leche's
  `filterMap` closure (`clProjCand`, restated verbatim so the two terms are
  definitionally the same function).  The twin computes the TAIL first; the
  element is then read at the state the tail left.  `denoteN_inj` carries the
  constructor lookup and the recursor lookup (a handle comparison against a
  name comparison), `readLevel`'s answer IS `denoteL`, so `Level.isEquiv`
  sees the same level on both sides.
* `ctorsMentionBlock_run` — read-only, over `stripPisAll_run` and
  `occursConstFast_run` (whose two con-leche-tier lemmas
  `clOccursConstB_eq`/`clOccursConstGo_eq` task #97-T1-OCC proved).
* the reordering (the module note's deviation 3): the twin runs the guards
  only on a non-empty candidate list, and an empty `filterMap` makes
  con-leche's answer `[]` whichever guard fires.
-/
import ConRon.Bridge.Frontend.ProjRec
import ConRon.Bridge.Frontend.Scratch
import ConRon.Bridge.Inductives.StructParts
import ConRon.Bridge.Inductives.NativeParts

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## Name lists -/

/-- con-leche: none — a name-handle list that denotes, as an element
relation. -/
theorem listRel_of_denoteNList {st : NStore} :
    ∀ {hs : List NIdx} {ns : List ConLeche.Name},
      denoteNList st hs = some ns →
      ListRel (fun h n => denoteN st h = some n) hs ns
  | [], ns, h => by
    simp only [denoteNList, Option.some.injEq] at h
    subst h; exact ListRel.nil
  | x :: xs, ns, h => by
    simp only [denoteNList] at h
    cases hx : denoteN st x with
    | none => rw [hx] at h; simp at h
    | some y =>
      cases hxs : denoteNList st xs with
      | none => rw [hx, hxs] at h; simp at h
      | some ys =>
        rw [hx, hxs] at h
        obtain rfl := Option.some.inj h
        exact ListRel.cons hx (listRel_of_denoteNList hxs)

/-- con-leche: none — `denoteNList` preserves length. -/
theorem denoteNList_length' {st : NStore} {hs : List NIdx} {ns : List ConLeche.Name}
    (h : denoteNList st hs = some ns) : hs.length = ns.length :=
  (listRel_of_denoteNList h).length_eq

/-- con-leche: none — `denoteNList` past an arena extension. -/
theorem denoteNList_ext' {st st' : EStore} (hx : Ext st st') {hs : List NIdx}
    {ns : List ConLeche.Name} (h : denoteNList st.ns hs = some ns) :
    denoteNList st'.ns hs = some ns :=
  denoteNList_ext hx.lss.ls.ns hs ns h

/-! ## The two lookups -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:364 projRecOwners — the
constructor record relation. -/
def CtorRel (st : EStore) (p : NIdx × Nat × EIdx) (q : ConLeche.Name × Nat × Expr) :
    Prop :=
  denoteN st.ns p.1 = some q.1 ∧ p.2.1 = q.2.1 ∧ denoteE st p.2.2 = some q.2.2

/-- con-leche: ConLeche/Frontend/ProjRec.lean:365 projRecOwners — the
recursor record relation. -/
def RecRel (st : EStore) (p : NIdx × List NIdx × EIdx × Nat × Nat)
    (q : ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat) : Prop :=
  denoteN st.ns p.1 = some q.1 ∧ denoteNList st.ns p.2.1 = some q.2.1 ∧
    denoteE st p.2.2.1 = some q.2.2.1 ∧ p.2.2.2.1 = q.2.2.2.1 ∧
    p.2.2.2.2 = q.2.2.2.2

/-- con-leche: none — a handle comparison against a name comparison, exact
both ways by `denoteN_inj`. -/
theorem beq_denoteN {st : NStore} (hw : NStoreWF st) {a b : NIdx}
    {aP bP : ConLeche.Name} (ha : denoteN st a = some aP)
    (hb : denoteN st b = some bP) : (a == b) = (aP == bP) := by
  by_cases hab : a = b
  · subst hab
    rw [Option.some.inj (ha.symm.trans hb)]; simp
  · have : aP ≠ bP := fun h => hab (denoteN_inj hw ha (h ▸ hb))
    rw [beq_eq_false_iff_ne.mpr hab, beq_eq_false_iff_ne.mpr this]

/-- con-leche: ConLeche/Frontend/ProjRec.lean:364 projRecOwners —
`ctors.find? (·.1 == C)`. -/
theorem findCtorRec_rel {st : EStore} (hw : NStoreWF st.ns) {c : NIdx}
    {C : ConLeche.Name} (hc : denoteN st.ns c = some C) :
    ∀ {ctors : List (NIdx × Nat × EIdx)} {ctorsP : List (ConLeche.Name × Nat × Expr)},
      ListRel (CtorRel st) ctors ctorsP →
      OptRel (CtorRel st) (findCtorRec c ctors) (ctorsP.find? (·.1 == C)) := by
  intro ctors ctorsP h
  induction h with
  | nil => exact trivial
  | @cons a b as bs hab _ ih =>
    simp only [findCtorRec, List.find?_cons]
    rw [beq_denoteN hw hab.1 hc]
    cases hbc : (b.1 == C) <;> simp only [if_true, if_false, Bool.false_eq_true]
    · exact ih
    · exact hab

/-- con-leche: ConLeche/Frontend/ProjRec.lean:365 projRecOwners —
`recs.find? (·.1 == T.str "rec")`. -/
theorem findRecRec_rel {st : EStore} (hw : NStoreWF st.ns) {n : NIdx}
    {N : ConLeche.Name} (hn : denoteN st.ns n = some N) :
    ∀ {recs : List (NIdx × List NIdx × EIdx × Nat × Nat)}
      {recsP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat)},
      ListRel (RecRel st) recs recsP →
      OptRel (RecRel st) (findRecRec n recs) (recsP.find? (·.1 == N)) := by
  intro recs recsP h
  induction h with
  | nil => exact trivial
  | @cons a b as bs hab _ ih =>
    simp only [findRecRec, List.find?_cons]
    rw [beq_denoteN hw hab.1 hn]
    cases hbc : (b.1 == N) <;> simp only [if_true, if_false, Bool.false_eq_true]
    · exact ih
    · exact hab

/-- con-leche: none — `CtorRel` past an arena extension. -/
theorem CtorRel.ext {st st' : EStore} (hx : Ext st st') {p : NIdx × Nat × EIdx}
    {q : ConLeche.Name × Nat × Expr} (h : CtorRel st p q) : CtorRel st' p q :=
  ⟨denoteN_ext h.1 hx, h.2.1, denote_ext h.2.2 hx⟩

/-- con-leche: none — `RecRel` past an arena extension. -/
theorem RecRel.ext {st st' : EStore} (hx : Ext st st')
    {p : NIdx × List NIdx × EIdx × Nat × Nat}
    {q : ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat} (h : RecRel st p q) :
    RecRel st' p q :=
  ⟨denoteN_ext h.1 hx, denoteNList_ext' hx h.2.1, denote_ext h.2.2.1 hx, h.2.2.2⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:344 projRecOwners — the type
record relation, the seven fields of the export's type record. -/
def TyRel (st : EStore) (p : NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)
    (q : ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat × List ConLeche.Name ×
      Bool) : Prop :=
  denoteN st.ns p.1 = some q.1 ∧
    denoteNList st.ns p.2.1 = some q.2.1 ∧
    denoteE st p.2.2.1 = some q.2.2.1 ∧
    p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2.1 = q.2.2.2.2.1 ∧
    denoteNList st.ns p.2.2.2.2.2.1 = some q.2.2.2.2.2.1 ∧
    p.2.2.2.2.2.2 = q.2.2.2.2.2.2

/-- con-leche: none — `TyRel` past an arena extension. -/
theorem TyRel.ext {st st' : EStore} (hx : Ext st st')
    {p : NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool}
    {q : ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat × List ConLeche.Name ×
      Bool} (h : TyRel st p q) : TyRel st' p q :=
  ⟨denoteN_ext h.1 hx, denoteNList_ext' hx h.2.1, denote_ext h.2.2.1 hx, h.2.2.2.1,
    h.2.2.2.2.1, denoteNList_ext' hx h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-! ## The candidates -/

set_option backward.do.legacy false in
/-- con-leche: ConLeche/Frontend/ProjRec.lean:360-369 projRecOwners — the
`filterMap` closure, restated verbatim (con-leche writes it inline). -/
def clProjCand (ctors : List (ConLeche.Name × Nat × Expr))
    (recs : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat)) :
    ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat × List ConLeche.Name × Bool →
      Option ConLeche.Frontend.ProjRecOwner :=
  fun (T, lps, tty, nP, nI, cs, _) => do
      let [C] := cs | none
      guard (nI == 0)
      let (_, .sort s) ← tty.stripPis nP | none
      guard (Level.isEquiv s .zero != some true)
      let (_, nF, _) ← ctors.find? (·.1 == C)
      let (rn, rlps, rty, nM, nm) ← recs.find? (·.1 == T.str "rec")
      guard (rlps.length == lps.length + 1)
      pure ⟨T, lps, nP, C, nF, rn, rlps, rty, nM, nm⟩

/-- con-leche: none — a `readLevelM` run is a parse step: the store, the
memos and the pins do not move, and the caches move by a `CacheFrame`
(`Bridge/Core/Walks/Cached.lean`'s frame). -/
theorem pstep_of_readLevelM {s s' : AState} {u : LIdx} {l : Level} (hok : StateOK s)
    (h : readLevelM u s = .ok (l, s')) : Inductives.PStep s s' := by
  obtain ⟨hst, -, hpins, -⟩ := Core.readLevelM_frame h
  exact ⟨⟨by rw [hst]; exact hok.wf⟩, by rw [hst]; exact Ext.refl _,
    by rw [hst]; exact BMExt.refl _, Core.CacheFrame.ofReadLevelM h, hpins⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:360-369 projRecOwners — **the
candidates**: the twin's explicit recursion is con-leche's `filterMap`.  The
tail is computed first; the element is read at the state it left. -/
theorem projRecCandidates_run {fuel : Nat} :
    ∀ {types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)}
      {typesP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat ×
        List ConLeche.Name × Bool)}
      {ctors : List (NIdx × Nat × EIdx)} {ctorsP : List (ConLeche.Name × Nat × Expr)}
      {recs : List (NIdx × List NIdx × EIdx × Nat × Nat)}
      {recsP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat)}
      {s s' : AState} {os : List ProjRecOwner},
      StateOK s → ReadLCacheOK s.caches.readLC s.store → ListRel (TyRel s.store) types typesP →
      ListRel (CtorRel s.store) ctors ctorsP → ListRel (RecRel s.store) recs recsP →
      projRecCandidates fuel ctors recs types s = .ok (os, s') →
      Inductives.PStep s s' ∧
        ListRel (ProjRecOwnerRel s'.store) os (typesP.filterMap (clProjCand ctorsP recsP)) := by
  intro types
  induction types with
  | nil =>
    intro typesP ctors ctorsP recs recsP s s' os hok _ htys _ _ hrun
    cases htys
    rw [projRecCandidates] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨Inductives.PStep.refl hok, ListRel.nil⟩
  | cons x rest ih =>
    intro typesP ctors ctorsP recs recsP s s' os hok hrl htys hcts hrcs hrun
    cases htys with
    | @cons _ xP _ restP hx hrest =>
    obtain ⟨t, lps, tty, nP, nI, cs, rf⟩ := x
    obtain ⟨T, lpsP, ttyP, nPP, nIP, csP, rfP⟩ := xP
    obtain ⟨hT, hlps, htty, rfl, rfl, hcs, rfl⟩ := hx
    rw [projRecCandidates] at hrun
    obtain ⟨tail, s₁, h1, hel⟩ := AM.bind_ok hrun
    try dsimp only at hel
    obtain ⟨p1, htail⟩ := ih hok hrl hrest hcts hrcs h1
    have hx1 := p1.ext
    rw [List.filterMap_cons]
    -- the element, at `s₁`
    have hT1 := denoteN_ext hT hx1
    have hlps1 := denoteNList_ext' hx1 hlps
    have htty1 := denote_ext htty hx1
    have hcts1 := ListRel.mono (fun _ _ h => CtorRel.ext hx1 h) hcts
    have hrcs1 := ListRel.mono (fun _ _ h => RecRel.ext hx1 h) hrcs
    have hw1 := nsWF_of_StateOK p1.ok
    -- the result is `tail` or one owner on top of it
    suffices H : Inductives.PStep s₁ s' ∧
        ((os = tail ∧ clProjCand ctorsP recsP (T, lpsP, ttyP, nP, nI, csP, rf) = none) ∨
         ∃ o oc, os = o :: tail ∧
           clProjCand ctorsP recsP (T, lpsP, ttyP, nP, nI, csP, rf) = some oc ∧
           ProjRecOwnerRel s'.store o oc) by
      obtain ⟨p2, hres⟩ := H
      refine ⟨p1.trans p2, ?_⟩
      have htail2 := ListRel.mono (fun _ _ h => ProjRecOwnerRel.ext p2.ext h) htail
      rcases hres with ⟨rfl, hn⟩ | ⟨o, oc, rfl, hs, ho⟩
      · rw [hn]; exact htail2
      · rw [hs]; exact ListRel.cons ho htail2
    have hnone : ∀ (h : os = tail ∧ s' = s₁)
        (hcl : clProjCand ctorsP recsP (T, lpsP, ttyP, nP, nI, csP, rf) = none),
        Inductives.PStep s₁ s' ∧
        ((os = tail ∧ clProjCand ctorsP recsP (T, lpsP, ttyP, nP, nI, csP, rf) = none) ∨
         ∃ o oc, os = o :: tail ∧
           clProjCand ctorsP recsP (T, lpsP, ttyP, nP, nI, csP, rf) = some oc ∧
           ProjRecOwnerRel s'.store o oc) := by
      intro h hcl
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Inductives.PStep.refl p1.ok, Or.inl ⟨rfl, hcl⟩⟩
    have hcsr := listRel_of_denoteNList hcs
    cases hcsr with
    | nil =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hel
      exact hnone ⟨rfl, rfl⟩ (by simp [clProjCand])
    | @cons c C cs' csP' hcC hcs' =>
    cases hcs' with
    | @cons d D ds dsP hdD hds =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hel
      exact hnone ⟨rfl, rfl⟩ (by simp [clProjCand])
    | nil =>
    have hC1 := denoteN_ext hcC hx1
    simp only [] at hel
    by_cases hnI : (nI != 0) = true
    · rw [if_pos hnI] at hel
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hel
      refine hnone ⟨rfl, rfl⟩ ?_
      have : nI ≠ 0 := by simpa using hnI
      simp [clProjCand, this, guard]
    rw [if_neg hnI] at hel
    have hnI0 : nI = 0 := by simpa using hnI
    subst hnI0
    obtain ⟨sp, s₂, h2, hel1⟩ := AM.bind_ok hel
    obtain ⟨rfl, hbp⟩ := Inductives.stripPis_pstep p1.ok htty1 h2
    cases sp with
    | none =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hel1
      refine hnone ⟨rfl, rfl⟩ ?_
      have := Inductives.stripPis_none hbp
      simp [clProjCand, this, guard]
    | some sp =>
    obtain ⟨bs, body⟩ := sp
    obtain ⟨xs, bodyP, hsp, -, hbody⟩ := ExprOps.denoteBP_some_inv hbp
    try dsimp only at hsp
    try dsimp only at hbody
    try dsimp only at hel1
    obtain ⟨w0, hw0⟩ := view_of_denote_isSome (Option.isSome_iff_exists.mpr ⟨_, hbody⟩)
    replace hel1 := tagIf_view_runF hw0
      (fun hne => by cases w0 with | sort u => exact absurd rfl hne | _ => rfl) hel1
    obtain ⟨v, s₃, h3, hel2⟩ := AM.bind_ok hel1
    obtain ⟨rfl, hv⟩ := view_run h3
    have hdv := (denoteE_view_eq p1.ok.wf hv).symm.trans hbody
    cases v
    case sort u =>
      try dsimp only at hel2
      obtain ⟨l, rfl, hl⟩ := denote_sort_inv p1.ok.wf hv hbody
      obtain ⟨sP, s₄, h4, hel3⟩ := AM.bind_ok hel2
      -- the port's `read_level_m`, memoised: the readback cache moves
      have hrl1 := p1.cframe.readL hrl
      obtain ⟨hsP, -⟩ := Core.readLevelM_denote hrl1 h4
      obtain rfl : sP = l := Option.some.inj (hsP.symm.trans hl)
      have p4 := pstep_of_readLevelM p1.ok h4
      by_cases hz : (Level.isEquiv sP .zero == some true) = true
      · rw [if_pos hz] at hel3
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hel3
        refine ⟨p4, Or.inl ⟨rfl, ?_⟩⟩
        have : Level.isEquiv sP .zero = some true := by simpa using hz
        simp [clProjCand, hsp, this, guard]
      rw [if_neg hz] at hel3
      have hz' : Level.isEquiv sP .zero ≠ some true := by simpa using hz
      have hfc := findCtorRec_rel hw1 hC1 hcts1
      cases hfc' : findCtorRec c ctors with
      | none =>
        rw [hfc'] at hel3 hfc
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hel3
        refine ⟨p4, Or.inl ⟨rfl, ?_⟩⟩
        have hn := hfc.none_left rfl
        simp [clProjCand, hsp, hn, guard]
      | some cr =>
      rw [hfc'] at hel3 hfc
      obtain ⟨cP, hcP, hcrel⟩ := hfc.some_left rfl
      obtain ⟨cn, nF, cty⟩ := cr
      obtain ⟨cnP, nFP, ctyP⟩ := cP
      obtain ⟨-, rfl, -⟩ := hcrel
      simp only [] at hel3
      obtain ⟨rn, s₅, h5, hel4⟩ := AM.bind_ok hel3
      obtain ⟨p5, hrn⟩ := Inductives.internStrN_run p4.ok (denoteN_ext hT1 p4.ext) h5
      have hrcs5 := ListRel.mono (fun _ _ h => RecRel.ext (p4.ext.trans p5.ext) h) hrcs1
      have hfr := findRecRec_rel (nsWF_of_StateOK p5.ok) hrn hrcs5
      cases hfr' : findRecRec rn recs with
      | none =>
        rw [hfr'] at hel4 hfr
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hel4
        refine ⟨p4.trans p5, Or.inl ⟨rfl, ?_⟩⟩
        have hn := hfr.none_left rfl
        simp [clProjCand, hsp, hcP, hn, guard]
      | some rr =>
      rw [hfr'] at hel4 hfr
      obtain ⟨rP, hrP, hrrel⟩ := hfr.some_left rfl
      obtain ⟨rn', rlps, rty, nM, nm⟩ := rr
      obtain ⟨rnP, rlpsP, rtyP, nMP, nmP⟩ := rP
      obtain ⟨hrn', hrlps, hrty, rfl, rfl⟩ := hrrel
      simp only [] at hel4
      have hlen : (rlps.length != lps.length + 1) = (rlpsP.length != lpsP.length + 1) := by
        rw [denoteNList_length' hrlps, denoteNList_length' hlps1]
      by_cases hL : (rlps.length != lps.length + 1) = true
      · rw [if_pos hL] at hel4
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hel4
        refine ⟨p4.trans p5, Or.inl ⟨rfl, ?_⟩⟩
        rw [hlen] at hL
        have : rlpsP.length ≠ lpsP.length + 1 := by simpa using hL
        simp [clProjCand, hsp, hz', hcP, hrP, this, guard]
      · rw [if_neg hL] at hel4
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hel4
        rw [hlen] at hL
        have hL' : rlpsP.length = lpsP.length + 1 := by simpa using hL
        refine ⟨p4.trans p5, Or.inr ⟨_, ⟨T, lpsP, nP, C, nF, rnP, rlpsP, rtyP, nM, nm⟩, rfl,
          by simp [clProjCand, hsp, hz', hcP, hrP, hL', guard], ?_⟩⟩
        exact
          { T := denoteN_ext hT1 (p4.ext.trans p5.ext)
            lps := denoteNList_ext' (p4.ext.trans p5.ext) hlps1
            nP := rfl
            ctor := denoteN_ext hC1 (p4.ext.trans p5.ext)
            nF := rfl
            recName := hrn'
            recLps := hrlps
            recType := hrty
            numMotives := rfl
            numMinors := rfl }
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hel2
      refine hnone ⟨rfl, rfl⟩ ?_
      have hns : ∀ l, bodyP ≠ .sort l := ExprOps.denoteEView_not_sort hdv (by intro u hu; cases hu)
      cases hb : bodyP with
      | sort l => exact absurd hb (hns l)
      | _ => simp [clProjCand, hsp, hb, guard]

/-! ## The recursion test -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:351-352 projRecOwners — the
innermost `blockNames.any fun n => occursConstFast n d`; read-only. -/
theorem occursAnyOf_run {s : AState} (hok : StateOK s) {fuel : Nat} {d : EIdx}
    {dP : Expr} (hd : denoteE s.store d = some dP) :
    ∀ {ns : List NIdx} {nsP : List ConLeche.Name} {b : Bool} {s' : AState},
      ListRel (fun h n => denoteN s.store.ns h = some n) ns nsP →
      occursAnyOf fuel ns d s = .ok (b, s') →
      s' = s ∧ b = nsP.any fun n => ConLeche.Frontend.occursConstFast n dP := by
  intro ns nsP b s' hns
  induction hns generalizing b s' with
  | nil =>
    intro hrun
    rw [occursAnyOf] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, rfl⟩
  | @cons n nP ns' nsP' hn _ ih =>
    intro hrun
    rw [occursAnyOf] at hrun
    obtain ⟨c, s₁, h1, hr1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, hc⟩ := occursConstFast_run hok hn hd h1
    rw [List.any_cons]
    cases hcv : c
    · rw [hcv] at hr1 hc
      simp only [Bool.false_eq_true, if_false] at hr1
      obtain ⟨rfl, hb⟩ := ih hr1
      rw [← hc, hb]; exact ⟨rfl, by simp⟩
    · rw [hcv] at hr1 hc
      simp only [if_true] at hr1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr1
      rw [← hc]; exact ⟨rfl, by simp⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:350-352 projRecOwners — the
middle `(stripPisAll cty).1.any fun (d, _) => …`; read-only. -/
theorem domsMentionAny_run {s : AState} (hok : StateOK s) {fuel : Nat}
    {ns : List NIdx} {nsP : List ConLeche.Name}
    (hns : ListRel (fun h n => denoteN s.store.ns h = some n) ns nsP) :
    ∀ {bs : List (EIdx × BinderMeta)} {bsP : List (Expr × BinderMeta)} {b : Bool}
      {s' : AState},
      ListRel (fun (p : EIdx × BinderMeta) (q : Expr × BinderMeta) =>
        denoteE s.store p.1 = some q.1 ∧ p.2 = q.2) bs bsP →
      domsMentionAny fuel ns bs s = .ok (b, s') →
      s' = s ∧ b = bsP.any fun (d, _) =>
        nsP.any fun n => ConLeche.Frontend.occursConstFast n d := by
  intro bs bsP b s' hbs
  induction hbs generalizing b s' with
  | nil =>
    intro hrun
    rw [domsMentionAny] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, rfl⟩
  | @cons p q ps qs hpq _ ih =>
    intro hrun
    obtain ⟨d, m⟩ := p
    obtain ⟨dP, m'⟩ := q
    obtain ⟨hd, -⟩ := hpq
    rw [domsMentionAny] at hrun
    obtain ⟨c, s₁, h1, hr1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, hc⟩ := occursAnyOf_run hok hd hns h1
    rw [List.any_cons]
    cases hcv : c
    · rw [hcv] at hr1 hc
      simp only [Bool.false_eq_true, if_false] at hr1
      obtain ⟨rfl, hb⟩ := ih hr1
      rw [hb]; simp [← hc]
    · rw [hcv] at hr1 hc
      simp only [if_true] at hr1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr1
      exact ⟨rfl, by simp [← hc]⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:349-352 projRecOwners — **the
recursion test's second disjunct**: a block name in a constructor's binder
domains.  Read-only. -/
theorem ctorsMentionBlock_run {s : AState} (hok : StateOK s) {fuel : Nat}
    {ns : List NIdx} {nsP : List ConLeche.Name}
    (hns : ListRel (fun h n => denoteN s.store.ns h = some n) ns nsP) :
    ∀ {ctors : List (NIdx × Nat × EIdx)} {ctorsP : List (ConLeche.Name × Nat × Expr)}
      {b : Bool} {s' : AState},
      ListRel (CtorRel s.store) ctors ctorsP →
      ctorsMentionBlock fuel ns ctors s = .ok (b, s') →
      s' = s ∧ b = ctorsP.any fun (_, _, cty) =>
        (ConLeche.Frontend.stripPisAll cty).1.any fun (d, _) =>
          nsP.any fun n => ConLeche.Frontend.occursConstFast n d := by
  intro ctors ctorsP b s' hcs
  induction hcs generalizing b s' with
  | nil =>
    intro hrun
    rw [ctorsMentionBlock] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, rfl⟩
  | @cons p q ps qs hpq _ ih =>
    intro hrun
    obtain ⟨cn, nf, cty⟩ := p
    obtain ⟨cnP, nfP, ctyP⟩ := q
    obtain ⟨-, -, hcty⟩ := hpq
    rw [ctorsMentionBlock] at hrun
    obtain ⟨pr, s₁, h1, hr1⟩ := AM.bind_ok hrun
    obtain ⟨bs, body⟩ := pr
    obtain ⟨rfl, bsP, bP, hcl, hrel, -⟩ := stripPisAll_run hok fuel hcty h1
    obtain ⟨c, s₂, h2, hr2⟩ := AM.bind_ok hr1
    obtain ⟨rfl, hc⟩ := domsMentionAny_run hok hns hrel h2
    rw [List.any_cons]
    simp only [hcl]
    cases hcv : c
    · rw [hcv] at hr2 hc
      simp only [Bool.false_eq_true, if_false] at hr2
      obtain ⟨rfl, hb⟩ := ih hr2
      rw [hb]; simp [← hc]
    · rw [hcv] at hr2 hc
      simp only [if_true] at hr2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
      exact ⟨rfl, by simp [← hc]⟩

/-! ## The census -/

/-- con-leche: none — the record flags agree. -/
theorem any_isRec_eq {st : EStore} :
    ∀ {types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)}
      {typesP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat ×
        List ConLeche.Name × Bool)},
      ListRel (TyRel st) types typesP →
      types.any (·.2.2.2.2.2.2) = typesP.any (·.2.2.2.2.2.2) := by
  intro types typesP h
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.any_cons, hab.2.2.2.2.2.2, ih]

/-- con-leche: none — the block names denote. -/
theorem blockNames_rel {st : EStore} :
    ∀ {types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)}
      {typesP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat ×
        List ConLeche.Name × Bool)},
      ListRel (TyRel st) types typesP →
      ListRel (fun h n => denoteN st.ns h = some n) (types.map (·.1)) (typesP.map (·.1)) := by
  intro types typesP h
  induction h with
  | nil => exact ListRel.nil
  | cons hab _ ih => exact ListRel.cons hab.1 ih

/-- con-leche: none — the first record's declared parameter count agrees. -/
theorem headNP_eq {st : EStore} :
    ∀ {types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)}
      {typesP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat ×
        List ConLeche.Name × Bool)},
      ListRel (TyRel st) types typesP →
      (types.head?.map (·.2.2.2.1)).getD 0 = (typesP.head?.map (·.2.2.2.1)).getD 0 := by
  intro types typesP h
  cases h with
  | nil => rfl
  | cons hab _ => simp [hab.2.2.2.1]

/-- con-leche: ConLeche/Frontend/ProjRec.lean:344-370 projRecOwners — **the
owner census, AND the module note's deviation 3 as a theorem**: the twin
computes the `filterMap` first and the two guards only when it is non-empty,
which is the same value because both guard branches return `[]` and an empty
`filterMap` makes the whole function `[]` whatever the guards say.

**CLOSED** (task #97-P3-Frontend round 8), over `projRecCandidates_run`,
`ctorsMentionBlock_run` and the Inductives tier's `structPartsCore?_isSome`/
`nativeParts?_isSome` at `PSpecP` (the recognisers read the pin table, hence
`PinsOK s`).  The recognisers compute an `isProp` field with `lvlEq?`, which
moves `readLC`/`lvlEqC`; that is `ParseStep.cframe`'s `CacheFrame`, and this
walk reads the recognisers through `.isSome` alone, so the verdict never
reaches the answer.  The frame is composed at `Inductives.PStep` and the
scratch clause is `Bridge/Frontend/Scratch.lean`'s `projRecOwners_scratch`.
`occursConstFast_run`'s two con-leche-tier lemmas (`clOccursConstB_eq`,
`clOccursConstGo_eq`) were proved in task #97-T1-OCC, so it is closed. -/
theorem projRecOwners_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s)
    (hrl : ReadLCacheOK s.caches.readLC s.store) {fuel : Nat} {block : List IConstantInfo}
    {blockP : List ConstantInfo} (hb : denoteCIList s.store block = some blockP)
    {types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)}
    {typesP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat ×
      List ConLeche.Name × Bool)}
    {ctors : List (NIdx × Nat × EIdx)}
    {ctorsP : List (ConLeche.Name × Nat × Expr)}
    {recs : List (NIdx × List NIdx × EIdx × Nat × Nat)}
    {recsP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat)}
    (htys : ListRel (fun p q =>
      denoteN s.store.ns p.1 = some q.1 ∧
        denoteNList s.store.ns p.2.1 = some q.2.1 ∧
        denoteE s.store p.2.2.1 = some q.2.2.1 ∧
        p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2.1 = q.2.2.2.2.1 ∧
        denoteNList s.store.ns p.2.2.2.2.2.1 = some q.2.2.2.2.2.1 ∧
        p.2.2.2.2.2.2 = q.2.2.2.2.2.2) types typesP)
    (hcts : ListRel (fun p q =>
      denoteN s.store.ns p.1 = some q.1 ∧ p.2.1 = q.2.1 ∧
        denoteE s.store p.2.2 = some q.2.2) ctors ctorsP)
    (hrcs : ListRel (fun p q =>
      denoteN s.store.ns p.1 = some q.1 ∧
        denoteNList s.store.ns p.2.1 = some q.2.1 ∧
        denoteE s.store p.2.2.1 = some q.2.2.1 ∧
        p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2 = q.2.2.2.2) recs recsP)
    {os : List ProjRecOwner}
    (hrun : projRecOwners fuel block types ctors recs s = .ok (os, s')) :
    ParseStep s s' ∧
      ListRel (ProjRecOwnerRel s'.store) os
        (ConLeche.Frontend.projRecOwners blockP typesP ctorsP recsP) := by
  have hsc := projRecOwners_scratch hrun
  have hw := nsWF_of_StateOK hok
  rw [projRecOwners] at hrun
  obtain ⟨owners, s₁, h1, hr1⟩ := AM.bind_ok hrun
  obtain ⟨p1, hown⟩ := projRecCandidates_run hok hrl htys hcts hrcs h1
  suffices H : Inductives.PStep s₁ s' ∧
      ListRel (ProjRecOwnerRel s'.store) os
        (ConLeche.Frontend.projRecOwners blockP typesP ctorsP recsP) by
    have p := p1.trans H.1
    exact ⟨⟨p.ok, p.ext, hsc, p.cframe, p.pins⟩, H.2⟩
  unfold ConLeche.Frontend.projRecOwners
  dsimp only
  cases owners with
  | nil =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hr1
    refine ⟨Inductives.PStep.refl p1.ok, ?_⟩
    have hnil : List.filterMap (clProjCand ctorsP recsP) typesP = [] := by
      cases h : List.filterMap (clProjCand ctorsP recsP) typesP with
      | nil => rfl
      | cons _ _ => rw [h] at hown; cases hown
    split
    · exact ListRel.nil
    · split
      · exact ListRel.nil
      · show ListRel _ [] (List.filterMap (clProjCand ctorsP recsP) typesP)
        rw [hnil]; exact ListRel.nil
  | cons o os' =>
    simp only [] at hr1
    have hx1 := p1.ext
    have hns := blockNames_rel (st := s₁.store)
      (ListRel.mono (fun _ _ h => TyRel.ext hx1 h) htys)
    obtain ⟨cm, s₂, h2, hr2⟩ := AM.bind_ok hr1
    obtain ⟨rfl, hcm⟩ := ctorsMentionBlock_run p1.ok hns
      (ListRel.mono (fun _ _ h => CtorRel.ext hx1 h) hcts) h2
    obtain ⟨sp, s₃, h3, hr3⟩ := AM.bind_ok hr2
    have hb1 := denoteCIList_ext hx1 block blockP hb
    obtain ⟨p3, hsp⟩ := Inductives.structPartsCore?_isSome block blockP _ _ _ p1.ok
      (hpins.mono hx1 p1.pins) hb1 h3
    have hrec := any_isRec_eq htys
    have hcond : (sp.isSome && !(types.any (·.2.2.2.2.2.2) || cm)) =
        ((ConLeche.structPartsCore? blockP).isSome && !(typesP.any (·.2.2.2.2.2.2) ||
          ctorsP.any fun (_, _, cty) =>
            (ConLeche.Frontend.stripPisAll cty).1.any fun (d, _) =>
              (typesP.map (·.1)).any fun n => ConLeche.Frontend.occursConstFast n d)) := by
      rw [hsp, hrec, hcm]
    have p13 := p1.trans p3
    split at hr3 <;> rename_i htw <;> split <;> rename_i hcg
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok hr3
      exact ⟨p3, ListRel.nil⟩
    · have hc : ((ConLeche.structPartsCore? blockP).isSome && !(typesP.any (·.2.2.2.2.2.2) ||
          ctorsP.any fun (_, _, cty) =>
            (ConLeche.Frontend.stripPisAll cty).1.any fun (d, _) =>
              (typesP.map (·.1)).any fun n => ConLeche.Frontend.occursConstFast n d)) = true :=
        hcond ▸ htw
      exact absurd hc hcg
    · have hc : ((ConLeche.structPartsCore? blockP).isSome && !(typesP.any (·.2.2.2.2.2.2) ||
          ctorsP.any fun (_, _, cty) =>
            (ConLeche.Frontend.stripPisAll cty).1.any fun (d, _) =>
              (typesP.map (·.1)).any fun n => ConLeche.Frontend.occursConstFast n d)) = true :=
        hcg
      exact absurd (hcond ▸ hc) htw
    obtain ⟨np, s₄, h4, hr4⟩ := AM.bind_ok hr3
    have hb3 := denoteCIList_ext p13.ext block blockP hb
    obtain ⟨p4, hnp⟩ := Inductives.nativeParts?_isSome _ block blockP _ _ _ p3.ok
      (hpins.mono p13.ext p13.pins) hb3 h4
    rw [headNP_eq htys] at hnp
    split at hr4 <;> rename_i htw2 <;> split <;> rename_i hcg2
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok hr4
      exact ⟨p3.trans p4, ListRel.nil⟩
    · exact absurd (hnp ▸ htw2) hcg2
    · exact absurd (hnp.symm ▸ hcg2) htw2
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok hr4
      refine ⟨p3.trans p4, ?_⟩
      show ListRel _ _ (List.filterMap (clProjCand ctorsP recsP) typesP)
      exact ListRel.mono (fun _ _ h => ProjRecOwnerRel.ext (p3.trans p4).ext h) hown

end ConRon.Bridge.Frontend
