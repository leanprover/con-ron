/-
# `ConRon.Bridge.Frontend.Olean.Blocks` — the blocks' check against upstream's

`blocksOk` reads the merge and compares handles.  Where the twin's says `ok`, upstream's says
`ok` on the denotations, which is what `blocksOk_good` asks.
-/
module

public import ConRon.Bridge.Frontend.Olean.EmitRun

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Merged CEntry entriesOf quotNames quotConstants
  blockMemberOk blockCtorOk blockStep blocksOk)
open ConLeche.Frontend.Olean (CEntryF CKindF bind_some_left mkN)

/-- con-leche: none — an action none of whose runs answers: a message, then a failure. -/
@[expose] def NoOk {α : Type} (x : AM α) : Prop := ∀ s r, x s ≠ .ok r

theorem NoOk.fail {α : Type} (e : ConRon.Arena.CheckError) : NoOk (ConRon.Arena.fail e : AM α) :=
  fun _ _ h => by cases h

theorem NoOk.bind {α β : Type} {x : AM α} {f : α → AM β} (h : ∀ a, NoOk (f a)) : NoOk (x >>= f) := by
  intro s r hr
  obtain ⟨a, s₁, -, h2⟩ := AM.bind_ok hr
  exact h a s₁ r h2

theorem NoOk.elim {α : Type} {x : AM α} {s : AState} {r : α × AState} (hn : NoOk x)
    (h : x s = .ok r) : False := hn s r h

/-- Proves `NoOk` of a chain of reads ending in a `fail`. -/
macro "no_ok" : tactic =>
  `(tactic| repeat' first | exact NoOk.fail _ | refine NoOk.bind fun _ => ?_)

theorem mapM_of_listRel {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β}, ListRel (fun a b => f a = some b) l ys → l.mapM f = some ys
  | _, _, .nil => rfl
  | _, _, .cons h hr => by
    simp only [List.mapM_cons, h, mapM_of_listRel hr]
    rfl

theorem name_beq {st : EStore} (hw : NStoreWF st.ns) {a b : NIdx} {aC bC : ConLeche.Name}
    (ha : denoteN st.ns a = some aC) (hb : denoteN st.ns b = some bC) : (a == b) = (aC == bC) := by
  cases he : (a == b) with
  | true =>
    have : a = b := by simpa using he
    subst this
    have : aC = bC := Option.some.inj (ha.symm.trans hb)
    simp [this]
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro hz
    subst hz
    have : a = b := denoteN_inj hw ha hb
    simp [this] at he

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:363-376 blockMemberOk -/
theorem blockMemberOk_run {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    {s : AState} (hc : WalkCtx s.store mg mgC) {n x : NIdx} {nC xC : ConLeche.Name}
    {all : List NIdx} {allC : List ConLeche.Name} {sk : Bool}
    (hx : denoteN s.store.ns x = some xC) (hal : ListRel (NR s.store) all allC) {u : Unit}
    {s' : AState} (h : blockMemberOk mg n all sk x s = .ok (u, s')) :
    s' = s ∧ ConLeche.Frontend.Olean.blockMemberOk mgC nC allC sk xC = .ok () := by
  generalize hF : blockMemberOk mg n all sk x = fn at h
  unfold blockMemberOk at hF
  dsimp only at hF
  cases hget : mg.get x with
  | none =>
    simp only [hget] at hF
    subst hF
    exact (NoOk.elim (by no_ok) h).elim
  | some m =>
    simp only [hget] at hF
    obtain ⟨z, hz, hd⟩ := hc.rel.got hx hget
    obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hd
    have htag := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk)
    split at hF
    · rename_i np ni al' cs nn ir iu irf hk1
      obtain ⟨allC', csC, hzk, hal', -⟩ := kindCtors_rel hk hk1
      have hbe := nameList_beq hc.wf (mapM_of_listRel hal') (mapM_of_listRel hal)
      unfold ConLeche.Frontend.Olean.blockMemberOk
      simp only [hz, hzk]
      by_cases e1 : (al' == all) = true
      · simp only [e1, ↓reduceIte] at hF
        have e1C : (allC' == allC) = true := by rw [← hbe]; exact e1
        rw [ite_eq_left e1C]
        by_cases e2 : (m.skipped == sk) = true
        · simp only [e2, ↓reduceIte] at hF
          subst hF
          obtain ⟨-, hs⟩ := AM.pure_ok h
          have e2C : (z.skipped == sk) = true := by
            have : m.skipped = z.skipped := htag.2
            rw [← this]; exact e2
          rw [ite_eq_left e2C]
          exact ⟨hs, rfl⟩
        · simp only [e2, Bool.false_eq_true, ↓reduceIte] at hF
          subst hF
          exact (NoOk.elim (by no_ok) h).elim
      · simp only [e1, Bool.false_eq_true, ↓reduceIte] at hF
        subst hF
        exact (NoOk.elim (by no_ok) h).elim
    · subst hF
      exact (NoOk.elim (by no_ok) h).elim

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:378-390 blockCtorOk -/
theorem blockCtorOk_run {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    {s : AState} (hc : WalkCtx s.store mg mgC) {n x : NIdx} {nC xC : ConLeche.Name} {sk : Bool}
    (hn : denoteN s.store.ns n = some nC) (hx : denoteN s.store.ns x = some xC) {u : Unit}
    {s' : AState} (h : blockCtorOk mg n sk x s = .ok (u, s')) :
    s' = s ∧ ConLeche.Frontend.Olean.blockCtorOk mgC nC sk xC = .ok () := by
  generalize hF : blockCtorOk mg n sk x = fn at h
  unfold blockCtorOk at hF
  dsimp only at hF
  cases hget : mg.get x with
  | none =>
    simp only [hget] at hF
    subst hF
    exact (NoOk.elim (by no_ok) h).elim
  | some m =>
    simp only [hget] at hF
    obtain ⟨z, hz, hd⟩ := hc.rel.got hx hget
    obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hd
    have htag := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk)
    split at hF
    · rename_i ind ci np nf iu hk1
      rw [hk1] at hk
      simp only [CKindF.mapM] at hk
      obtain ⟨i', hi, hk⟩ := bind_some_left hk
      simp only [pure, Option.some.injEq] at hk
      have hbe := name_beq hc.wf hi hn
      unfold ConLeche.Frontend.Olean.blockCtorOk
      simp only [hz, ← hk]
      by_cases e1 : (ind == n) = true
      · simp only [e1, ↓reduceIte] at hF
        have e1C : (i' == nC) = true := by rw [← hbe]; exact e1
        rw [ite_eq_left e1C]
        by_cases e2 : (m.skipped == sk) = true
        · simp only [e2, ↓reduceIte] at hF
          subst hF
          obtain ⟨-, hs⟩ := AM.pure_ok h
          have e2C : (z.skipped == sk) = true := by
            have : m.skipped = z.skipped := htag.2
            rw [← this]; exact e2
          rw [ite_eq_left e2C]
          exact ⟨hs, rfl⟩
        · simp only [e2, Bool.false_eq_true, ↓reduceIte] at hF
          subst hF
          exact (NoOk.elim (by no_ok) h).elim
      · simp only [e1, Bool.false_eq_true, ↓reduceIte] at hF
        subst hF
        exact (NoOk.elim (by no_ok) h).elim
    · subst hF
      exact (NoOk.elim (by no_ok) h).elim

/-- A `forM` of the twin against upstream's, step by step. -/
theorem forM_rel {s : AState} {f : NIdx → AM Unit}
    {g : ConLeche.Name → Except ConLeche.CheckError Unit}
    (hstep : ∀ x xC u s', denoteN s.store.ns x = some xC → f x s = .ok (u, s') →
      s' = s ∧ g xC = .ok ()) :
    ∀ {l : List NIdx} {ls : List ConLeche.Name}, ListRel (NR s.store) l ls → ∀ {u : Unit} {s' : AState},
      l.forM f s = .ok (u, s') → s' = s ∧ ls.forM g = .ok ()
  | _, _, .nil, u, s', h => by
    obtain ⟨-, hs⟩ := AM.pure_ok h
    exact ⟨hs, rfl⟩
  | _, _, @ListRel.cons _ _ _ x xC l ls hx hr, u, s', h => by
    have e : (List.forM (x :: l) f : AM Unit) = (f x >>= fun _ => List.forM l f) := rfl
    rw [e] at h
    obtain ⟨a, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hs1, hg⟩ := hstep _ _ _ _ hx h1
    rw [hs1] at h2
    obtain ⟨hs2, hl⟩ := forM_rel hstep hr h2
    refine ⟨hs2, ?_⟩
    show (g xC >>= fun _ => List.forM ls g) = _
    rw [hg]
    exact hl

/-- The quotient package's check: a constant's tag is its denotation's. -/
theorem all_tag_rel {st : EStore} :
    ∀ {l : List CEntry} {zs : List ConLeche.Frontend.Olean.CEntry}, ListRel (CR st) l zs →
      l.all (fun x => x.c.kind.tag == 4) = zs.all (fun x => x.kind.tag == 4)
  | _, _, .nil => rfl
  | _, _, .cons hc hr => by
    obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hc
    have ht := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk).1
    simp only [List.all_cons, ht, all_tag_rel hr]

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:392-438 blockStep -/
theorem blockStep_run {pk : OleanPins} {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    {s : AState} (hc : WalkCtx s.store mg mgC) (hp : PinsRel s.store pk) {n : NIdx}
    {nC : ConLeche.Name} (hn : denoteN s.store.ns n = some nC) {u : Unit} {s' : AState}
    (h : blockStep pk mg n s = .ok (u, s')) :
    s' = s ∧ ConLeche.Frontend.Olean.blockStep mgC nC = .ok () := by
  generalize hF : blockStep pk mg n = fn at h
  unfold blockStep at hF
  dsimp only at hF
  unfold ConLeche.Frontend.Olean.blockStep
  dsimp only
  cases hget : mg.get n with
  | none =>
    simp only [hget] at hF
    subst hF
    obtain ⟨-, hs⟩ := AM.pure_ok h
    simp only [hc.rel.absent hn hget]
    first | exact ⟨hs, rfl⟩ | exact ⟨hs, trivial⟩
  | some c =>
    simp only [hget] at hF
    obtain ⟨z, hz, hd⟩ := hc.rel.got hn hget
    obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hd
    have htag := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk)
    simp only [hz]
    cases hk1 : c.c.kind with
    | ax u =>
      rw [hk1] at hk
      simp only [CKindF.mapM, pure, Option.some.injEq] at hk
      simp only [hk1] at hF
      subst hF
      obtain ⟨-, hs⟩ := AM.pure_ok h
      simp only [← hk]
      first | exact ⟨hs, rfl⟩ | exact ⟨hs, trivial⟩
    | defn v hs' sf =>
      rw [hk1] at hk
      simp only [CKindF.mapM] at hk
      obtain ⟨w, -, hk⟩ := bind_some_left hk
      simp only [pure, Option.some.injEq] at hk
      simp only [hk1] at hF
      subst hF
      obtain ⟨-, hs⟩ := AM.pure_ok h
      simp only [← hk]
      first | exact ⟨hs, rfl⟩ | exact ⟨hs, trivial⟩
    | thm v a =>
      rw [hk1] at hk
      simp only [CKindF.mapM] at hk
      obtain ⟨w, -, hk⟩ := bind_some_left hk
      obtain ⟨as, -, hk⟩ := bind_some_left hk
      simp only [pure, Option.some.injEq] at hk
      simp only [hk1] at hF
      subst hF
      obtain ⟨-, hs⟩ := AM.pure_ok h
      simp only [← hk]
      first | exact ⟨hs, rfl⟩ | exact ⟨hs, trivial⟩
    | opaq v u =>
      rw [hk1] at hk
      simp only [CKindF.mapM] at hk
      obtain ⟨w, -, hk⟩ := bind_some_left hk
      simp only [pure, Option.some.injEq] at hk
      simp only [hk1] at hF
      subst hF
      obtain ⟨-, hs⟩ := AM.pure_ok h
      simp only [← hk]
      first | exact ⟨hs, rfl⟩ | exact ⟨hs, trivial⟩
    | quot q =>
      rw [hk1] at hk
      simp only [CKindF.mapM, pure, Option.some.injEq] at hk
      simp only [hk1] at hF
      simp only [← hk]
      have hqn : ListRel (NR s.store) (quotNames pk) ConLeche.Frontend.Olean.quotNames :=
        .cons hp.nQuot (.cons hp.nQuotMk (.cons hp.nQuotLift (.cons hp.nQuotInd .nil)))
      have hcq := array_contains_rel hc.wf hn hqn
      have hq := entriesOf_rel (blockTys_rel hc hqn)
      have hall := all_tag_rel hq
      by_cases e1 : (quotNames pk).contains n = true
      · simp only [e1, ↓reduceIte] at hF
        have e1C : ConLeche.Frontend.Olean.quotNames.contains nC = true := by rw [← hcq]; exact e1
        rw [ite_eq_left e1C]
        by_cases e2 : (entriesOf mg (quotConstants pk mg)).all (fun x => x.c.kind.tag == 4) = true
        · simp only [e2, ↓reduceIte] at hF
          subst hF
          obtain ⟨-, hs⟩ := AM.pure_ok h
          have e2C : (ConLeche.Frontend.Olean.quotConstants mgC).all (fun x => x.kind.tag == 4) = true := by
            exact hall.symm.trans e2
          rw [ite_eq_left e2C]
          exact ⟨hs, rfl⟩
        · simp only [e2, Bool.false_eq_true, ↓reduceIte] at hF
          subst hF
          exact (NoOk.elim (by no_ok) h).elim
      · simp only [e1, Bool.false_eq_true, ↓reduceIte] at hF
        subst hF
        exact (NoOk.elim (by no_ok) h).elim
    | induct np ni al cs nn ir iu irf =>
      obtain ⟨allC, csC, hzk, hal, hcs⟩ := kindCtors_rel hk hk1
      simp only [hk1] at hF
      simp only [hzk]
      have hcon := array_contains_rel hc.wf hn hal
      by_cases e1 : al.contains n = true
      · simp only [e1, ↓reduceIte] at hF
        have e1C : allC.contains nC = true := by rw [← hcon]; exact e1
        rw [ite_eq_left e1C]
        subst hF
        obtain ⟨a, s₁, h1, h2⟩ := AM.bind_ok h
        have hsk : c.skipped = z.skipped := htag.2
        obtain ⟨hs1, hf1⟩ := forM_rel (g := ConLeche.Frontend.Olean.blockMemberOk mgC nC allC z.skipped)
          (fun x xC u s' hx hr => by
            rw [← hsk]
            exact blockMemberOk_run hc hx hal hr) hal h1
        rw [hs1] at h2
        obtain ⟨hs2, hf2⟩ := forM_rel (g := ConLeche.Frontend.Olean.blockCtorOk mgC nC z.skipped)
          (fun x xC u s' hx hr => by
            rw [← hsk]
            exact blockCtorOk_run hc hn hx hr) hcs h2
        refine ⟨hs2, ?_⟩
        simp only [hf1]
        exact hf2
      · simp only [e1, Bool.false_eq_true, ↓reduceIte] at hF
        subst hF
        exact (NoOk.elim (by no_ok) h).elim
    | ctor ind ci np nf iu =>
      rw [hk1] at hk
      simp only [CKindF.mapM] at hk
      obtain ⟨iC, hi, hk⟩ := bind_some_left hk
      simp only [pure, Option.some.injEq] at hk
      simp only [hk1] at hF
      simp only [← hk]
      cases hgi : mg.get ind with
      | none =>
        simp only [hgi] at hF
        subst hF
        exact (NoOk.elim (by no_ok) h).elim
      | some t =>
        simp only [hgi] at hF
        obtain ⟨tC, htC, htd⟩ := hc.rel.got hi hgi
        obtain ⟨-, -, -, htk⟩ := denoteCEntry_parts htd
        simp only [htC]
        split at hF
        · rename_i np' ni' al' cs nn ir iu' irf hk2
          obtain ⟨allC, csC, hzk, -, hcs⟩ := kindCtors_rel htk hk2
          simp only [hzk]
          have hcon := array_contains_rel hc.wf hn hcs
          by_cases e1 : cs.contains n = true
          · simp only [e1, ↓reduceIte] at hF
            subst hF
            obtain ⟨-, hs⟩ := AM.pure_ok h
            have e1C : csC.contains nC = true := by rw [← hcon]; exact e1
            rw [ite_eq_left e1C]
            exact ⟨hs, rfl⟩
          · simp only [e1, Bool.false_eq_true, ↓reduceIte] at hF
            subst hF
            exact (NoOk.elim (by no_ok) h).elim
        · subst hF
          exact (NoOk.elim (by no_ok) h).elim
    | recur al np ni nmo nmi rules kk iu =>
      obtain ⟨allC, rulesC, hzk, hal⟩ := kindRec_rel hk hk1
      simp only [hk1] at hF
      simp only [hzk]
      cases hal with
      | nil =>
        simp only [] at hF
        subst hF
        exact (NoOk.elim (by no_ok) h).elim
      | @cons t tC ts tsC ht hts =>
        simp only [] at hF
        cases hgt : mg.get t with
        | none =>
          simp only [hgt] at hF
          subst hF
          exact (NoOk.elim (by no_ok) h).elim
        | some m =>
          simp only [hgt] at hF
          obtain ⟨mC, hmC, hmd⟩ := hc.rel.got ht hgt
          obtain ⟨-, -, -, hmk⟩ := denoteCEntry_parts hmd
          have hmtag := (ConLeche.Frontend.Olean.CKindF.mapM_tag hmk)
          simp only [hmC]
          split at hF
          · rename_i np' ni' al' cs nn ir iu' irf hk2
            obtain ⟨allC', csC, hzk', hal', -⟩ := kindCtors_rel hmk hk2
            simp only [hzk']
            have hbe := nameList_beq hc.wf (mapM_of_listRel hal') (mapM_of_listRel (.cons ht hts))
            by_cases e1 : (al' == t :: ts) = true
            · simp only [e1, ↓reduceIte] at hF
              have e1C : (allC' == tC :: tsC) = true := by rw [← hbe]; exact e1
              rw [ite_eq_left e1C]
              by_cases e2 : (m.skipped == c.skipped) = true
              · simp only [e2, ↓reduceIte] at hF
                subst hF
                obtain ⟨-, hs⟩ := AM.pure_ok h
                have e2C : (mC.skipped == z.skipped) = true := by
                  have a : m.skipped = mC.skipped := hmtag.2
                  have b : c.skipped = z.skipped := htag.2
                  rw [← a, ← b]; exact e2
                rw [ite_eq_left e2C]
                exact ⟨hs, rfl⟩
              · simp only [e2, Bool.false_eq_true, ↓reduceIte] at hF
                subst hF
                exact (NoOk.elim (by no_ok) h).elim
            · simp only [e1, Bool.false_eq_true, ↓reduceIte] at hF
              subst hF
              exact (NoOk.elim (by no_ok) h).elim
          · subst hF
            exact (NoOk.elim (by no_ok) h).elim

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:440-441 blocksOk -/
theorem blocksOk_run {pk : OleanPins} {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    {s : AState} (hc : WalkCtx s.store mg mgC) (hp : PinsRel s.store pk) {u : Unit} {s' : AState}
    (h : blocksOk pk mg s = .ok (u, s')) :
    s' = s ∧ ConLeche.Frontend.Olean.blocksOk mgC = .ok () := by
  unfold blocksOk at h
  unfold ConLeche.Frontend.Olean.blocksOk
  exact forM_rel (fun x xC u s' hx hr => blockStep_run hc hp hx hr) hc.rel.order h

end ConRon.Bridge.Frontend.Olean
