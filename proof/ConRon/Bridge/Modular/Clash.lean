/-
# `ConRon.Bridge.Modular.Clash` — Lean's clash rule over the loaded names, Theorem 1 (task #166)

`isPropCheapF_run` and `subsumesF_run` are `MergeAll.lean`'s `isPropCheap_run` and
`subsumes_run` over any head-type lookup that answers as upstream's where it answers
(`HeadRel`).  As there, the twin's walks run on fuel, so a twin's `false` may be upstream's
`true` — only at two axioms of one statement, where the two copies are, read back, one constant.
So the clash rule's fold (`clashOk_run`) follows upstream's with the kept copy's statement and
kind read back as upstream's kept copy's.  Run style, not `vcgen`.
-/
module

public import ConRon.Bridge.Modular.Index
public import ConRon.Bridge.Frontend.Olean.MergeAll

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins isPropBody isPropHead isPropDrop)
open ConLeche.Frontend.Olean (CEntryF CKindF bind_some_left Copy)

/-- con-leche: none — **a head-type lookup over handles that answers as upstream's** where it
answers. -/
@[expose] def HeadRel (st : EStore) (headTy : NIdx → Option EIdx)
    (headTyC : ConLeche.Name → Option Expr) : Prop :=
  ∀ n t nC, headTy n = some t → denoteN st.ns n = some nC →
    ∃ tC, headTyC nC = some tC ∧ denoteE st t = some tC

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap — **the twin's test leaves
the state alone, and its `true` is upstream's**, at a head-type lookup that answers as
upstream's. -/
theorem isPropCheapF_run {pk : OleanPins} {s : AState} (hok : StateOK s) (hnu : NullsRel s.store pk)
    {headTy : NIdx → Option EIdx} {headTyC : ConLeche.Name → Option Expr}
    (hh : HeadRel s.store headTy headTyC)
    {ty : EIdx} {tyC : Expr} (hty : denoteE s.store ty = some tyC) {b : Bool} {s' : AState}
    (h : ConRon.Arena.Frontend.Olean.isPropCheapF pk headTy ty s = .ok (b, s')) :
    s' = s ∧ (b = true → ConLeche.Frontend.Olean.isPropCheap headTyC tyC = true) := by
  unfold ConRon.Arena.Frontend.Olean.isPropCheapF at h
  obtain ⟨x, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hs1, xC, hx, hbd⟩ := isPropBody_run hok _ hty h1
  rw [hs1] at h
  obtain ⟨o, s₂, h2, h⟩ := AM.bind_ok h
  have hs2 := isPropHead_state _ h2
  rw [hs2] at h
  rcases o with _ | ⟨n, k⟩
  · obtain ⟨hv, hs⟩ := AM.pure_ok h
    exact ⟨hs, fun hb => by rw [hv] at hb; cases hb⟩
  · obtain ⟨-, hbody, nC, hn, hhead⟩ := isPropHead_run hok _ hx h2
    simp only [] at h
    cases hg : headTy n with
    | none =>
      simp only [hg] at h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      exact ⟨hs, fun hb => by rw [hv] at hb; cases hb⟩
    | some d =>
      simp only [hg] at h
      obtain ⟨dC, hdC, htd⟩ := hh n d nC hg hn
      obtain ⟨o', s₃, h3, h⟩ := AM.bind_ok h
      have hs3 := isPropDrop_state _ h3
      rw [hs3] at h
      cases o' with
      | none =>
        obtain ⟨hv, hs⟩ := AM.pure_ok h
        exact ⟨hs, fun hb => by rw [hv] at hb; cases hb⟩
      | some y =>
        obtain ⟨-, yC, hy, hdrop⟩ := isPropDrop_run hok _ htd h3
        obtain ⟨v, s₄, h4, h⟩ := AM.bind_ok h
        obtain ⟨hs4, hv⟩ := view_run h4
        rw [hs4] at h
        have hden := denoteE_view_eq hok.wf hv
        rw [hden] at hy
        have hfin : s' = s ∧ (b = true → ∃ u, v = .sort u ∧ u = pk.zero) := by
          cases v with
          | sort u =>
            obtain ⟨hv', hs⟩ := AM.pure_ok h
            refine ⟨hs, fun hb => ⟨u, rfl, ?_⟩⟩
            rw [hv'] at hb
            simpa using hb
          | bvar _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | fvar _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | const _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | app _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | lam _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | forallE _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | letE _ _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | lit _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | proj _ _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
        refine ⟨hfin.1, fun hb => ?_⟩
        obtain ⟨u, rfl, rfl⟩ := hfin.2 hb
        have hyC : yC = .sort .zero := by
          have hz := hnu.zero
          simp only [denoteEView, hz, Option.map_some, Option.some.injEq] at hy
          exact hy.symm
        subst hyC
        unfold ConLeche.Frontend.Olean.isPropCheap
        rw [hbd, hbody, hhead]
        simp only [hdC, hdrop]

theorem denoteStmt_parts {st : EStore} {c : ConRon.Arena.Frontend.Olean.StmtRec} {z : ConstantVal}
    (h : denoteStmt st c = some z) :
    denoteN st.ns c.name = some z.name ∧ c.levelParams.mapM (denoteN st.ns) = some z.levelParams ∧
      denoteE st c.type = some z.type := by
  simp only [denoteStmt] at h
  obtain ⟨a, ha, h⟩ := bind_some_left h
  obtain ⟨b, hb, h⟩ := bind_some_left h
  obtain ⟨c', hc, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq] at h
  subst h
  exact ⟨ha, hb, hc⟩

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:49-59 subsumesF — **the twin's `true` is
upstream's, and upstream may say `true` to a twin's `false` only at two axioms of one
statement**: there the two copies, read back, are one statement and one kind. -/
theorem subsumesF_run {pk : OleanPins} {s : AState} (hok : StateOK s) (hnu : NullsRel s.store pk)
    {headTy : NIdx → Option EIdx} {headTyC : ConLeche.Name → Option Expr}
    (hh : HeadRel s.store headTy headTyC)
    {c1 c2 : ConRon.Arena.Frontend.Olean.StmtRec} {k1 k2 : CKindF NIdx Unit}
    {z1 z2 : ConstantVal} {j1 j2 : CKindF ConLeche.Name Unit}
    (h1 : denoteStmt s.store c1 = some z1) (h2 : denoteStmt s.store c2 = some z2)
    (hk1 : denoteKindN s.store k1 = some j1) (hk2 : denoteKindN s.store k2 = some j2)
    {b : Bool} {s' : AState}
    (h : ConRon.Arena.Frontend.Olean.subsumesF pk headTy c1 k1 c2 k2 s = .ok (b, s')) :
    s' = s ∧ (b = true → ConLeche.Frontend.Olean.subsumesF headTyC z1 j1 z2 j2 = true) ∧
      (b = false → ConLeche.Frontend.Olean.subsumesF headTyC z1 j1 z2 j2 = true →
        z1 = z2 ∧ j1 = j2) := by
  have hw := nsWF_of_StateOK hok
  obtain ⟨n1, l1, t1⟩ := denoteStmt_parts h1
  obtain ⟨n2, l2, t2⟩ := denoteStmt_parts h2
  have hcmp : (c1.name == c2.name && c1.type == c2.type && c1.levelParams == c2.levelParams)
      = (z1.name == z2.name && z1.type == z2.type && z1.levelParams == z2.levelParams) := by
    have e1 : (c1.name == c2.name) = (z1.name == z2.name) := by
      cases hb : (c1.name == c2.name) with
      | true =>
        have := beq_iff_eq.mp hb
        rw [this] at n1
        have hz : z1.name = z2.name := Option.some.inj (n1.symm.trans n2)
        simp [hz]
      | false =>
        symm
        rw [beq_eq_false_iff_ne]
        intro hz
        have := denoteN_inj hw n1 (hz ▸ n2)
        simp [this] at hb
    have e2 : (c1.type == c2.type) = (z1.type == z2.type) := by
      cases hb : (c1.type == c2.type) with
      | true =>
        have := beq_iff_eq.mp hb
        rw [this] at t1
        have hz : z1.type = z2.type := Option.some.inj (t1.symm.trans t2)
        simp [hz]
      | false =>
        symm
        rw [beq_eq_false_iff_ne]
        intro hz
        have := denoteE_inj hok.wf t1 (hz ▸ t2)
        simp [this] at hb
    rw [e1, e2, nameList_beq hw l1 l2]
  have hzeq : (z1.name == z2.name && z1.type == z2.type && z1.levelParams == z2.levelParams) = true →
      z1 = z2 := by
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨ha, hb⟩, hc⟩ := hc
    cases z1; cases z2; simp_all
  generalize hF : ConRon.Arena.Frontend.Olean.subsumesF pk headTy c1 k1 c2 k2 = f at h
  unfold ConRon.Arena.Frontend.Olean.subsumesF at hF
  unfold ConLeche.Frontend.Olean.subsumesF
  rw [← hcmp]
  by_cases hc : (c1.name == c2.name && c1.type == c2.type && c1.levelParams == c2.levelParams) = true
  · simp only [hc, ↓reduceIte, Bool.true_and] at hF ⊢
    have hz12 := hzeq (hcmp ▸ hc)
    split at hF
    · -- two theorems
      rename_i v a v' a' hk1' hk2'
      subst hF hk1' hk2'
      simp only [denoteKindN, CKindF.mapM] at hk1 hk2
      obtain ⟨w, -, hk1⟩ := bind_some_left hk1
      obtain ⟨as, ha, hk1⟩ := bind_some_left hk1
      obtain ⟨w', -, hk2⟩ := bind_some_left hk2
      obtain ⟨as', ha', hk2⟩ := bind_some_left hk2
      simp only [pure, Option.some.injEq] at hk1 hk2
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      subst hv
      simp only [← hk1, ← hk2]
      rw [nameList_beq hw ha ha']
      exact ⟨hs, id, fun hb hb' => by rw [hb] at hb'; cases hb'⟩
    · -- a theorem and an axiom
      rename_i v a u hk1' hk2'
      subst hF hk1' hk2'
      simp only [denoteKindN, CKindF.mapM] at hk1 hk2
      obtain ⟨w, -, hk1⟩ := bind_some_left hk1
      obtain ⟨as, ha, hk1⟩ := bind_some_left hk1
      simp only [pure, Option.some.injEq] at hk1 hk2
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      subst hv
      simp only [← hk1, ← hk2]
      have hl : [c2.name].mapM (denoteN s.store.ns) = some [z2.name] := by
        simp only [List.mapM_cons, List.mapM_nil, n2]; rfl
      rw [nameList_beq hw ha hl]
      exact ⟨hs, id, fun hb hb' => by rw [hb] at hb'; cases hb'⟩
    · -- two axioms
      rename_i u u' hk1' hk2'
      subst hF hk1' hk2'
      simp only [denoteKindN, CKindF.mapM, pure, Option.some.injEq] at hk1 hk2
      simp only [← hk1, ← hk2]
      by_cases hu : (u == u') = true
      · simp only [hu, ↓reduceIte, Bool.true_and] at h ⊢
        obtain ⟨hs, htrue⟩ := isPropCheapF_run hok hnu hh t1 h
        refine ⟨hs, htrue, fun _ _ => ⟨hz12, ?_⟩⟩
        have huu : u = u' := by simpa using hu
        rw [huu]
      · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨hv, hs⟩ := AM.pure_ok h
        subst hv
        simp only [Bool.not_eq_true] at hu
        refine ⟨hs, fun hb => (by cases hb), fun _ hb => ?_⟩
        simp [hu] at hb
    · -- anything else
      rename_i h3 h4 h5
      subst hF
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      subst hv
      have htag1 := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk1).1
      have htag2 := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk2).1
      have hfalse : (match (generalizing := false) j1, j2 with
          | .thm _ a₁, .thm _ a₂ => a₁ == a₂
          | .thm _ a₁, .ax u₂ => a₁ == [z2.name] && !u₂
          | .ax u₁, .ax u₂ => u₁ == u₂ && ConLeche.Frontend.Olean.isPropCheap headTyC z1.type
          | _, _ => false) = false := by
        cases j1 <;> cases j2 <;> first
          | rfl
          | (exfalso
             rename_i a b c d
             first
              | (obtain ⟨v, x, e⟩ := tag_thm (k := k1) (by rw [htag1]; rfl)
                 obtain ⟨v', x', e'⟩ := tag_thm (k := k2) (by rw [htag2]; rfl)
                 exact h3 _ _ _ _ e e')
              | (obtain ⟨v, x, e⟩ := tag_thm (k := k1) (by rw [htag1]; rfl)
                 obtain ⟨u, e'⟩ := tag_ax (k := k2) (by rw [htag2]; rfl)
                 exact h4 _ _ _ e e')
              | (obtain ⟨u, e⟩ := tag_ax (k := k1) (by rw [htag1]; rfl)
                 obtain ⟨u', e'⟩ := tag_ax (k := k2) (by rw [htag2]; rfl)
                 exact h5 _ _ e e'))
      refine ⟨hs, fun hb => (by cases hb), fun _ hb => ?_⟩
      rw [hfalse] at hb
      cases hb
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hF
    subst hF
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    simp only [Bool.not_eq_true] at hc
    subst hv
    refine ⟨hs, fun hb => (by cases hb), fun _ hb => ?_⟩
    simp [hc] at hb

/-! ## The clash rule -/

/-- con-leche: none — the copy kept so far, its statement and kind read back. -/
@[expose] def KeptRel (st : EStore)
    (x : Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)
    (y : Copy × ConstantVal × CKindF ConLeche.Name Unit) : Prop :=
  denoteStmt st x.2.1 = some y.2.1 ∧ denoteKindN st x.2.2 = some y.2.2

theorem clashFold_run {pk : OleanPins} {ld : ConRon.Arena.Frontend.Olean.HeaderLoads}
    {ldC : ConLeche.Frontend.Olean.HeaderLoads} {n : NIdx} {nC : ConLeche.Name}
    {headTy : NIdx → Option EIdx} {headTyC : ConLeche.Name → Option Expr} :
    ∀ {rest : List (Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)}
      {restC : List (Copy × ConstantVal × CKindF ConLeche.Name Unit)} {s s' : AState}
      {kept : Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit}
      {keptC : Copy × ConstantVal × CKindF ConLeche.Name Unit}
      {res : Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit},
      StateOK s → NullsRel s.store pk → HeadRel s.store headTy headTyC →
      ListRel (CopyInfoRel s.store) rest restC → KeptRel s.store kept keptC →
      rest.foldlM (fun (kept : Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit) next => do
        let (_, cv₁, k₁) := next
        let (_, cv₂, k₂) := kept
        if ← ConRon.Arena.Frontend.Olean.subsumesF pk headTy cv₁ k₁ cv₂ k₂ then pure next
        else if ← ConRon.Arena.Frontend.Olean.subsumesF pk headTy cv₂ k₂ cv₁ k₁ then pure kept
        else fail (.invalid s!"modules {← readName (ld.nameAt pk kept.1.mod)} and \
          {← readName (ld.nameAt pk next.1.mod)} store different constants named \
          {← readName n}, and both are loaded")) kept s = .ok (res, s') →
      s' = s ∧ ∃ r, restC.foldlM (fun (kept : Copy × ConstantVal × CKindF ConLeche.Name Unit) next =>
        let (_, cv₁, k₁) := next
        let (_, cv₂, k₂) := kept
        if ConLeche.Frontend.Olean.subsumesF headTyC cv₁ k₁ cv₂ k₂ then .ok next
        else if ConLeche.Frontend.Olean.subsumesF headTyC cv₂ k₂ cv₁ k₁ then .ok kept
        else .error (.invalid s!"modules {ldC.nameAt kept.1.mod} and {ldC.nameAt next.1.mod} \
          store different constants named {nC}, and both are loaded")) keptC = .ok r
  | [], [], s, s', kept, keptC, res, _, _, _, .nil, _, h => by
    simp only [List.foldlM_nil] at h
    exact ⟨(AM.pure_ok h).2, keptC, rfl⟩
  | next :: rest, nextC :: restC, s, s', kept, keptC, res, hok, hnu, hh, .cons hr t, hk, h => by
    obtain ⟨c1, cv1, k1⟩ := next
    obtain ⟨c2, cv2, k2⟩ := kept
    obtain ⟨d1, z1, j1⟩ := nextC
    obtain ⟨d2, z2, j2⟩ := keptC
    obtain ⟨-, hz1, hj1⟩ := hr
    obtain ⟨hz2, hj2⟩ := hk
    dsimp only at hz1 hj1 hz2 hj2
    simp only [List.foldlM_cons] at h ⊢
    obtain ⟨x, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨b1, s₂, hb1, hx⟩ := AM.bind_ok h1
    obtain ⟨rfl, hA, hA'⟩ := subsumesF_run hok hnu hh hz1 hz2 hj1 hj2 hb1
    cases b1 with
    | true =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hx
      have hC := hA rfl
      simp only [hC, ↓reduceIte]
      exact clashFold_run hok hnu hh t ⟨hz1, hj1⟩ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hx
      obtain ⟨b2, s₃, hb2, hx⟩ := AM.bind_ok hx
      obtain ⟨rfl, hB, -⟩ := subsumesF_run hok hnu hh hz2 hz1 hj2 hj1 hb2
      cases b2 with
      | true =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hx
        have hC := hB rfl
        cases hu : ConLeche.Frontend.Olean.subsumesF headTyC z1 j1 z2 j2 with
        | true =>
          -- upstream keeps the next copy: one constant with the kept one, read back
          obtain ⟨rfl, rfl⟩ := hA' rfl hu
          simp only [↓reduceIte]
          exact clashFold_run hok hnu hh t ⟨hz2, hj2⟩ h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, hC]
          exact clashFold_run hok hnu hh t ⟨hz2, hj2⟩ h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hx
        obtain ⟨_, _, -, hx⟩ := AM.bind_ok hx
        obtain ⟨_, _, -, hx⟩ := AM.bind_ok hx
        obtain ⟨_, _, -, hx⟩ := AM.bind_ok hx
        exact (AM.fail_ok hx).elim

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:113-127 clashOk — **the twin's accept of one
name's copies is upstream's**, at a head-type lookup that answers as upstream's. -/
theorem clashOk_run {pk : OleanPins} {ld : ConRon.Arena.Frontend.Olean.HeaderLoads}
    {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    {headTy : NIdx → Option EIdx} {headTyC : ConLeche.Name → Option Expr}
    {cl : ConRon.Arena.Frontend.Olean.Clash} {clC : ConLeche.Frontend.Olean.Clash}
    {s s' : AState} (hok : StateOK s) (hnu : NullsRel s.store pk)
    (hh : HeadRel s.store headTy headTyC) (hc : ClashRel s.store cl clC)
    (h : ConRon.Arena.Frontend.Olean.clashOk pk ld headTy cl s = .ok ((), s')) :
    s' = s ∧ ConLeche.Frontend.Olean.clashOk ldC headTyC clC = .ok () := by
  unfold ConRon.Arena.Frontend.Olean.clashOk at h
  unfold ConLeche.Frontend.Olean.clashOk
  have hcs := hc.copies
  revert h
  generalize cl.copies.toList = l at hcs
  generalize clC.copies.toList = lC at hcs
  intro h
  cases hcs with
  | nil => exact ⟨(AM.pure_ok h).2, rfl⟩
  | cons hr t =>
    dsimp only at h ⊢
    obtain ⟨res, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨-, rfl⟩ := AM.pure_ok h2
    obtain ⟨rfl, r, hr'⟩ := clashFold_run (nC := clC.name) (ldC := ldC) hok hnu hh t
      ⟨hr.2.1, hr.2.2⟩ h1
    refine ⟨rfl, ?_⟩
    rw [hr']
    rfl

end ConRon.Bridge.Modular
