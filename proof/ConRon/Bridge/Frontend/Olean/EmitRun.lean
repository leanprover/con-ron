/-
# `ConRon.Bridge.Frontend.Olean.EmitRun` — the walk, step by step

`emitLoop_run`: where the twin's walk answers, upstream's `emitLoop` on the denotations has a
related emitter.  The stacks are related item by item (`WR`).
-/
module

public import ConRon.Bridge.Frontend.Olean.EmitWalk

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Merged CEntry Emit Work entriesOf blockTys blockCtors
  blockRecs quotNames quotConstants emitLoop)
open ConLeche.Frontend.Olean (CEntryF CKindF bind_some_left mkN)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:23-28 Work — one step of the walk against
upstream's. -/
@[expose] def WR (st : EStore) (mg : Merged) : Work → ConLeche.Frontend.Olean.Work → Prop
  | .visit n, .visit nC => denoteN st.ns n = some nC
  | .one n, .one c => SR st mg n c
  | .quot cs, .quot zs => ListRel (SR st mg) cs zs
  | .block a b c, .block a' b' c' =>
    ListRel (SR st mg) a a' ∧ ListRel (SR st mg) b b' ∧ ListRel (SR st mg) c c'
  | _, _ => False

theorem visits_rel {st : EStore} {mg : Merged} :
    ∀ {ns : List NIdx} {nsC : List ConLeche.Name}, ListRel (NR st) ns nsC →
      ListRel (WR st mg) (Work.visits ns) (ConLeche.Frontend.Olean.Work.visits nsC)
  | _, _, .nil => .nil
  | _, _, .cons h hr => .cons h (visits_rel hr)

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:71-75 CEntry — a constant's `uses`, read
back. -/
theorem denoteCEntry_uses {st : EStore} {x : CEntry} {z : ConLeche.Frontend.Olean.CEntry}
    (h : denoteCEntry st x = some z) : ListRel (NR st) x.uses.toList z.uses.toList := by
  unfold denoteCEntry at h
  obtain ⟨e, -, h⟩ := bind_some_left h
  obtain ⟨u, hu, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq] at h
  subst h
  simpa using listRel_of_mapM hu

theorem usesOf_rel {st : EStore} {mg : Merged} :
    ∀ {ns : List NIdx} {zs : List ConLeche.Frontend.Olean.CEntry}, ListRel (SR st mg) ns zs →
      ListRel (WR st mg) (Work.usesOf mg ns) (ConLeche.Frontend.Olean.Work.usesOf zs)
  | _, _, .nil => .nil
  | n :: ns, z :: zs, .cons ⟨_, x, hg, hx⟩ hr => by
    have e : Work.usesOf mg (n :: ns) = x.uses.toList.map Work.visit ++ Work.usesOf mg ns := by
      simp [Work.usesOf, entriesOf, hg]
    rw [e]
    simp only [ConLeche.Frontend.Olean.Work.usesOf, List.flatMap_cons]
    exact ListRel.append (visits_rel (denoteCEntry_uses hx)) (usesOf_rel hr)

theorem marks_rel {st : EStore} {mg : Merged} :
    ∀ {ns : List NIdx} {zs : List ConLeche.Frontend.Olean.CEntry}, ListRel (SR st mg) ns zs →
      ∀ {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}, EmitRel st em emC →
      EmitRel st (ns.foldl Emit.mark em) (zs.foldl (fun st x => st.mark x.name) emC)
  | _, _, .nil, _, _, h => h
  | _, _, .cons hn hr, _, _, h => marks_rel hr (h.mark hn.1)

theorem ones_rel {st : EStore} :
    ∀ {cs : List CEntry} {zs : List ConLeche.Frontend.Olean.CEntry}, ListRel (CR st) cs zs →
      ∀ {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}, EmitRel st em emC →
      EmitRel st (cs.foldl Emit.one em) (zs.foldl ConLeche.Frontend.Olean.Emit.one emC)
  | _, _, .nil, _, _, h => h
  | _, _, .cons hc hr, _, _, h => ones_rel hr (h.one hc)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:127-132 Emit.block -/
theorem EmitRel.block {st : EStore} {mg : Merged} {em : Emit} {emC : ConLeche.Frontend.Olean.Emit}
    (h : EmitRel st em emC) {a b c : List NIdx} {a' b' c' : List ConLeche.Frontend.Olean.CEntry}
    (ha : ListRel (SR st mg) a a') (hb : ListRel (SR st mg) b b') (hc : ListRel (SR st mg) c c') :
    EmitRel st (em.block mg a b c) (emC.block a' b' c') := by
  obtain ⟨h1, e1⟩ := steps_fold (@fun _ _ acc _ _ he hc => EmitRel.tyStep he acc hc) (entriesOf_rel ha) _ _ #[] h
  obtain ⟨h2, e2⟩ := steps_fold (@fun _ _ acc _ _ he hc => EmitRel.ctorStep he acc hc) (entriesOf_rel hb) _ _ #[] h1
  obtain ⟨h3, e3⟩ := steps_fold (@fun _ _ acc _ _ he hc => EmitRel.recStep he acc hc) (entriesOf_rel hc) _ _ #[] h2
  have ea : em.block mg a b c =
      (((entriesOf mg c).foldl Emit.recStep (((entriesOf mg b).foldl Emit.ctorStep
        (((entriesOf mg a).foldl Emit.tyStep (em, #[])).1, #[])).1, #[])).1).push
        (.ind ((entriesOf mg a).foldl Emit.tyStep (em, #[])).2.toList
          ((entriesOf mg b).foldl Emit.ctorStep (((entriesOf mg a).foldl Emit.tyStep (em, #[])).1, #[])).2.toList
          ((entriesOf mg c).foldl Emit.recStep (((entriesOf mg b).foldl Emit.ctorStep
            (((entriesOf mg a).foldl Emit.tyStep (em, #[])).1, #[])).1, #[])).2.toList) := rfl
  have eb : emC.block a' b' c' =
      ((c'.foldl ConLeche.Frontend.Olean.Emit.recStep ((b'.foldl ConLeche.Frontend.Olean.Emit.ctorStep
        ((a'.foldl ConLeche.Frontend.Olean.Emit.tyStep (emC, #[])).1, #[])).1, #[])).1).push
        (.ind (a'.foldl ConLeche.Frontend.Olean.Emit.tyStep (emC, #[])).2.toList
          (b'.foldl ConLeche.Frontend.Olean.Emit.ctorStep ((a'.foldl ConLeche.Frontend.Olean.Emit.tyStep (emC, #[])).1, #[])).2.toList
          (c'.foldl ConLeche.Frontend.Olean.Emit.recStep ((b'.foldl ConLeche.Frontend.Olean.Emit.ctorStep
            ((a'.foldl ConLeche.Frontend.Olean.Emit.tyStep (emC, #[])).1, #[])).1, #[])).2.toList) := rfl
  rw [ea, eb, e1, e2, e3]
  exact h3.push _

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:294-338 emitLoop — **the twin's walk, on the
denotations, is upstream's**: spent fuel is a `fail`, so a run that answers took the same
steps. -/
theorem emitLoop_run {pk : OleanPins} {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    {rm : Std.HashMap NIdx (Array NIdx)} {rmC : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    {st : EStore} (hc : WalkCtx st mg mgC) (hp : PinsRel st pk) (hr : RecRel st rm rmC) {s : AState} :
    ∀ (fuel : Nat) (stack : List Work) (stackC : List ConLeche.Frontend.Olean.Work) (em : Emit)
      (emC : ConLeche.Frontend.Olean.Emit) {em' : Emit} {s' : AState},
      ListRel (WR st mg) stack stackC → EmitRel st em emC →
      emitLoop pk mg rm fuel stack em s = .ok (em', s') →
      s' = s ∧ EmitRel st em' (ConLeche.Frontend.Olean.emitLoop mgC rmC stackC emC) := by
  intro fuel
  induction fuel with
  | zero =>
    intro stack stackC em emC em' s' hst he h
    cases hst with
    | nil =>
      rw [emitLoop] at h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      subst hv
      rw [ConLeche.Frontend.Olean.emitLoop]
      exact ⟨hs, he⟩
    | cons _ _ =>
      rw [emitLoop] at h
      cases h
  | succ fuel ih =>
    intro stack stackC em emC em' s' hst he h
    cases hst with
    | nil =>
      rw [emitLoop] at h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      subst hv
      rw [ConLeche.Frontend.Olean.emitLoop]
      exact ⟨hs, he⟩
    | @cons w wC rest restC hw hrest =>
      cases w with
      | one n =>
        cases wC with
        | one z =>
          rw [emitLoop] at h
          rw [ConLeche.Frontend.Olean.emitLoop]
          obtain ⟨hdn, x, hg, hx⟩ := hw
          have e : em.ones mg [n] = em.one x := by
            simp [Emit.ones, entriesOf, hg]
          rw [e] at h
          exact ih _ _ _ _ hrest (he.one hx) h
        | visit _ => exact hw.elim
        | quot _ => exact hw.elim
        | block _ _ _ => exact hw.elim
      | quot cs =>
        cases wC with
        | quot zs =>
          rw [emitLoop] at h
          rw [ConLeche.Frontend.Olean.emitLoop]
          have h1 := ih _ _ _ _ hrest (ones_rel (entriesOf_rel hw) he) h
          exact h1
        | visit _ => exact hw.elim
        | one _ => exact hw.elim
        | block _ _ _ => exact hw.elim
      | block a b c =>
        cases wC with
        | block a' b' c' =>
          rw [emitLoop] at h
          rw [ConLeche.Frontend.Olean.emitLoop]
          exact ih _ _ _ _ hrest (he.block hw.1 hw.2.1 hw.2.2) h
        | visit _ => exact hw.elim
        | one _ => exact hw.elim
        | quot _ => exact hw.elim
      | visit n =>
        cases wC with
        | visit nC =>
          rw [emitLoop] at h
          rw [ConLeche.Frontend.Olean.emitLoop]
          have hdn : denoteN st.ns n = some nC := hw
          have hcv := he.visited.contains hc.wf hdn
          by_cases hv : em.visited.contains n = true
          · have hvC : emC.visited.contains nC = true := by rw [← hcv]; exact hv
            simp only [hv, ↓reduceIte] at h
            simp only [hvC, ↓reduceDIte]
            exact ih _ _ _ _ hrest he h
          · have hvC : ¬ emC.visited.contains nC = true := by rw [← hcv]; exact hv
            simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
            rw [dite_eq_right_of_eq_false (eq_false hvC)]
            cases hget : mg.get n with
            | none =>
              simp only [hget] at h
              have hab := hc.rel.absent hdn hget
              split
              · exact ih _ _ _ _ hrest he h
              · rename_i heq
                rw [hab] at heq
                cases heq
            | some x =>
              simp only [hget] at h
              obtain ⟨z, hz, hd⟩ := hc.rel.got hdn hget
              split
              · rename_i heq
                rw [hz] at heq
                cases heq
              · rename_i z' hz'
                rw [hz] at hz'
                cases hz'
                obtain ⟨-, -, -, hk⟩ := denoteCEntry_parts hd
                have hsk : x.skipped = z.skipped := by
                  exact (ConLeche.Frontend.Olean.CKindF.mapM_tag hk).2
                by_cases hs : x.skipped = true
                · have hsC : z.skipped = true := by rw [← hsk]; exact hs
                  simp only [hs, ↓reduceIte] at h
                  rw [ite_eq_left hsC]
                  exact ih _ _ _ _ hrest he h
                · have hsC : ¬ z.skipped = true := by rw [← hsk]; exact hs
                  simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
                  rw [ite_eq_right hsC]
                  have hzn := hc.names nC z hz
                  have sr : SR st mg n z := ⟨by rw [hzn]; exact hdn, x, hget, hd⟩
                  have he1 := he.mark hdn
                  dsimp only at h ⊢
                  cases hk1 : x.c.kind with
                  | ax u =>
                    rw [hk1] at hk
                    simp only [CKindF.mapM, pure, Option.some.injEq] at hk
                    simp only [hk1] at h
                    simp only [← hk]
                    exact ih (Work.usesOf mg [n] ++ Work.one n :: rest) _ _ _ (ListRel.append (usesOf_rel (.cons sr .nil)) (.cons sr hrest)) he1 h
                  | defn v hs' sf =>
                    rw [hk1] at hk
                    simp only [CKindF.mapM] at hk
                    obtain ⟨w, -, hk⟩ := bind_some_left hk
                    simp only [pure, Option.some.injEq] at hk
                    simp only [hk1] at h
                    simp only [← hk]
                    exact ih (Work.usesOf mg [n] ++ Work.one n :: rest) _ _ _ (ListRel.append (usesOf_rel (.cons sr .nil)) (.cons sr hrest)) he1 h
                  | thm v a =>
                    rw [hk1] at hk
                    simp only [CKindF.mapM] at hk
                    obtain ⟨w, -, hk⟩ := bind_some_left hk
                    obtain ⟨as, -, hk⟩ := bind_some_left hk
                    simp only [pure, Option.some.injEq] at hk
                    simp only [hk1] at h
                    simp only [← hk]
                    exact ih (Work.usesOf mg [n] ++ Work.one n :: rest) _ _ _ (ListRel.append (usesOf_rel (.cons sr .nil)) (.cons sr hrest)) he1 h
                  | opaq v u =>
                    rw [hk1] at hk
                    simp only [CKindF.mapM] at hk
                    obtain ⟨w, -, hk⟩ := bind_some_left hk
                    simp only [pure, Option.some.injEq] at hk
                    simp only [hk1] at h
                    simp only [← hk]
                    exact ih (Work.usesOf mg [n] ++ Work.one n :: rest) _ _ _ (ListRel.append (usesOf_rel (.cons sr .nil)) (.cons sr hrest)) he1 h
                  | quot q =>
                    rw [hk1] at hk
                    simp only [CKindF.mapM, pure, Option.some.injEq] at hk
                    simp only [hk1] at h
                    simp only [← hk]
                    have hqn : ListRel (NR st) (quotNames pk) ConLeche.Frontend.Olean.quotNames :=
                      .cons hp.nQuot (.cons hp.nQuotMk (.cons hp.nQuotLift (.cons hp.nQuotInd .nil)))
                    have hq := blockTys_rel hc hqn
                    exact ih (Work.visit pk.nEq :: Work.quot (quotConstants pk mg) :: rest) _ _ _
                      (.cons hp.nEq (.cons hq hrest)) (marks_rel hq he1) h
                  | ctor ind ci np nf iu =>
                    rw [hk1] at hk
                    simp only [CKindF.mapM] at hk
                    obtain ⟨i', hi, hk⟩ := bind_some_left hk
                    simp only [pure, Option.some.injEq] at hk
                    simp only [hk1] at h
                    simp only [← hk]
                    exact ih (Work.visit ind :: rest) _ _ _ (.cons hi hrest) he1 h
                  | recur al np ni nmo nmi rules kk iu =>
                    obtain ⟨allC, rulesC, hzk, hal⟩ := kindRec_rel hk hk1
                    simp only [hk1] at h
                    simp only [hzk]
                    exact ih (Work.visits al ++ rest) _ _ _ (ListRel.append (visits_rel hal) hrest) he1 h
                  | induct np ni al cs nn ir iu irf =>
                    obtain ⟨allC, csC, hzk, hal, -⟩ := kindCtors_rel hk hk1
                    simp only [hk1] at h
                    simp only [hzk]
                    have htys := blockTys_rel hc hal
                    have hcts := blockCtors_rel hc htys
                    have hrcs : ListRel (SR st mg) (blockRecs mg rm n)
                        (ConLeche.Frontend.Olean.blockRecs mgC rmC nC) := blockTys_rel hc (hr _ _ hdn)
                    have hall := ListRel.append (ListRel.append htys hcts) hrcs
                    exact ih (Work.usesOf mg (blockTys mg al ++ blockCtors mg (blockTys mg al) ++ blockRecs mg rm n) ++
                      Work.block (blockTys mg al) (blockCtors mg (blockTys mg al)) (blockRecs mg rm n) :: rest) _ _ _
                      (ListRel.append (usesOf_rel hall)
                      (.cons ⟨htys, hcts, hrcs⟩ hrest)) (marks_rel hall he1) h
        | one _ => exact hw.elim
        | quot _ => exact hw.elim
        | block _ _ _ => exact hw.elim

end ConRon.Bridge.Frontend.Olean
