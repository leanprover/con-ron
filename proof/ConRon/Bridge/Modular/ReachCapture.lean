/-
# `ConRon.Bridge.Modular.ReachCapture` — agreement and the capture check, Theorem 1 (task #166)

The reach's checks over its caches: a loaded copy's spot (`importerSpot_rel`), a copy's proof
flag (`proofStatus_run`), two copies' agreement (`agreeCheck_run`), the clash rule
(`clashAgree_run`), the capture check of one read (`captureOne_run`) and of a record's reads, the
names a record stores (`storedNamesOk_run`).  Each twin accept is upstream's answer, the caches
related after.  What one expression reads (`NeedsExprHyp`) is the needs walk's Theorem 1,
taken as a hypothesis here.  Run style, not `vcgen`.
-/
module

public import ConRon.Bridge.Modular.ReachParts
public import ConRon.Bridge.Modular.Roots

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins SM)
open ConLeche.Frontend.Olean (Region Roots OLeanLevel ModFiles CEntryF CKindF Copy)

/-- con-leche: ConLeche/Cached/Needs.lean:44 needsGo — **what one expression reads**, the
twin's walk from a fresh state against upstream's: the needs walk's Theorem 1. -/
@[expose] def NeedsExprHyp : Prop :=
  ∀ {s s' : AState} {e : EIdx} {eC : Expr} {x : ConRon.Arena.NeedsSt},
    DriverOK s → s.store.scratchOn = false → denoteE s.store e = some eC →
    ConRon.Arena.NeedsSt.empty.expr e s = .ok (x, s') →
    DStep s s' ∧ denoteNList s'.store.ns x.acc = some (ConLeche.Cached.needsGo {} #[] eC).2.toList

/-- The needs walk of one expression is upstream's (`expr_exact`, `Roots.lean`). -/
theorem needsExprHyp_holds : NeedsExprHyp := by
  intro s s' e eC x hok hoff he h
  obtain ⟨rfl, -, hx⟩ := expr_exact hok.state hok.pins (XRel.empty s.store) he h
  exact ⟨DStep.refl hok hoff, hx⟩

/-- con-leche: ConLeche/Driver/Reach.lean:376-382 ProofStatus — the twin's flag as upstream's. -/
@[expose] def psC : ConRon.Arena.Modular.ProofStatus → ConLeche.Driver.ProofStatus
  | .yes => .yes
  | .no => .no
  | .infer => .infer

/-! ## A loaded copy's spot -/

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:110-111 HeaderLoads.nameAt — a module's
name for messages, read back. -/
theorem loadsNameAt_rel {st : EStore} {pk : OleanPins} (hp : NullsRel st pk)
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    (hl : LoadsRel st ld ldC) (i : Nat) :
    denoteN st.ns (ld.nameAt pk i) = some (ldC.nameAt i) := by
  unfold ConRon.Arena.Frontend.Olean.HeaderLoads.nameAt ConLeche.Frontend.Olean.HeaderLoads.nameAt
  rcases optRel_cases (listRel_getElem? hl.order i) with ⟨g1, g2⟩ | ⟨a, b, g1, g2, g3⟩
  · simp only [Array.getElem?_toList] at g1 g2
    rw [g1, g2]; exact hp.anon
  · simp only [Array.getElem?_toList] at g1 g2
    rw [g1, g2]; exact g3

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:51-53 NameIndex.at — a copy's name position,
read back. -/
theorem indexAt_rel {st : EStore} {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (h : IndexRel st ix ixC) (cp : Copy) :
    Option.Rel (NPRel st) (ix.at cp) (ixC.at cp) := by
  unfold ConRon.Arena.Frontend.Olean.NameIndex.at ConLeche.Frontend.Olean.NameIndex.at
  rcases optRel_cases (listRel_getElem? h.parts cp.mod) with ⟨g1, g2⟩ | ⟨a, b, g1, g2, g3⟩
  · simp only [Array.getElem?_toList] at g1 g2
    rw [g1, g2]; exact .none
  · simp only [Array.getElem?_toList] at g1 g2
    rw [g1, g2]
    have := listRel_getElem? g3.consts cp.pos
    simpa [Array.getElem?_toList] using this

/-- con-leche: ConLeche/Driver/Reach.lean:366-372 importerSpot — **the importer's copy of a
loaded name**, upstream's. -/
theorem importerSpot_rel {st : EStore} (hw : NStoreWF st.ns) {pk : OleanPins} (hp : NullsRel st pk)
    {sp : Roots} {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    (he : EnvRel sp st env envC) {y : NIdx} {yC : ConLeche.Name} (hy : denoteN st.ns y = some yC) :
    Option.Rel (fun (a : Nat × ConRon.Arena.Modular.Spot) (b : Nat × ConLeche.Driver.Spot) =>
        a.1 = b.1 ∧ SpotRel st a.2 b.2)
      (ConRon.Arena.Modular.importerSpot pk env y) (ConLeche.Driver.importerSpot envC yC) := by
  unfold ConRon.Arena.Modular.importerSpot ConLeche.Driver.importerSpot
  have hf := he.wr.index.first.get_eq hw hy
  simp only [Option.bind_eq_bind, hf]
  cases hfC : envC.wr.index.first[yC]? with
  | none => exact .none
  | some cp =>
    simp only [Option.bind_some]
    rcases optRel_cases (indexAt_rel he.wr.index cp) with ⟨g1, g2⟩ | ⟨q, qC, g1, g2, g3⟩
    · rw [g1, g2]; exact .none
    · rw [g1, g2]
      refine .some ⟨rfl, ⟨loadsNameAt_rel hp he.wr.loads cp.mod, ?_⟩, g3⟩
      simp [ConRon.Arena.Frontend.Olean.HeaderLoads.levelAt, he.wr.loads.flags]

/-! ## A copy's proof flag -/

theorem tagStatus_eq (n : Nat) :
    psC (if n == 2 then .yes else if n == 0 || n == 1 || n == 3 then .infer else .no) =
      (match n with
        | 2 => .yes
        | 0 | 1 | 3 => .infer
        | _ => .no) := by
  rcases n with _ | _ | _ | _ | n <;> simp [psC]

/-- con-leche: ConLeche/Driver/Reach.lean:384-402 proofStatus — **a copy's proof flag**,
upstream's. -/
theorem proofStatus_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {sp₀ : ConRon.Arena.Modular.Spot} {spC : ConLeche.Driver.Spot}
    {k : CKindF NIdx Unit} {kC : CKindF ConLeche.Name Unit} {p : ConRon.Arena.Modular.ProofStatus}
    {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hs : SpotRel s.store sp₀ spC) (hk : denoteKindN s.store k = some kC)
    (h : ConRon.Arena.Modular.proofStatus (modelFs F) pk sp env c sp₀ k s = .ok ((c', p), s')) :
    DStep s s' ∧ ∃ cC', ModelIO.Gives (ConLeche.Driver.proofStatus envC cC spC kC) F
        (cC', .ok (psC p)) ∧ CacheRel s'.store c' cC' := by
  have refl : ∀ {q : ConRon.Arena.Modular.ProofStatus},
      (pure (c, q) : AM _) s = .ok ((c', p), s') → c' = c ∧ p = q ∧ s' = s := by
    intro q hq
    obtain ⟨hv, rfl⟩ := AM.pure_ok hq
    simp only [Prod.mk.injEq] at hv
    exact ⟨hv.1, hv.2, rfl⟩
  have htag := (ConLeche.Frontend.Olean.CKindF.mapM_tag hk).1
  unfold ConRon.Arena.Modular.proofStatus at h
  unfold ConLeche.Driver.proofStatus
  have easy : ∀ {q : ConRon.Arena.Modular.ProofStatus} {x : ConLeche.Driver.ReachCache ×
      Except ConLeche.CheckError ConLeche.Driver.ProofStatus},
      (pure (c, q) : AM _) s = .ok ((c', p), s') → x = (cC, .ok (psC q)) →
      DStep s s' ∧ ∃ cC', ModelIO.Gives (pure x : ModelIO _) F (cC', .ok (psC p)) ∧
        CacheRel s'.store c' cC' := by
    intro q x hq hx
    obtain ⟨rfl, rfl, rfl⟩ := refl hq
    subst hx
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  cases k <;> cases kC <;> simp [CKindF.tag] at htag
  case thm.thm => exact easy h rfl
  case defn.defn => exact easy h rfl
  case opaq.opaq => exact easy h rfl
  case quot.quot => exact easy h rfl
  case induct.induct => exact easy h rfl
  case ctor.ctor => exact easy h rfl
  case recur.recur => exact easy h rfl
  case ax.ax u u' =>
    have hlev : (sp₀.part.level == .private) = (spC.part.level == .private) := by rw [hs.1.2]
    by_cases h1 : (sp₀.part.level == .private) = true
    · simp only [h1, ↓reduceIte] at h
      rw [hlev] at h1
      simp only [h1, ↓reduceIte]
      exact easy h rfl
    simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
    obtain ⟨⟨c₁, q⟩, s₁, g1, k1⟩ := AM.bind_ok h
    obtain ⟨hst1, cC₁, qC, hgq, hc1, hq⟩ := privSpot_run hsp hctx he hc hs g1
    have h1C : (spC.part.level == .private) = false := by rw [← hlev]; simpa using h1
    have htg := hq.2.tag
    have key : c' = c₁ ∧ psC p = (match qC.pos.tag with | 2 => .yes | 0 | 1 | 3 => .infer | _ => .no) ∧
        s' = s₁ := by
      have hk1 : (if q.pos.tag == 2 then pure (c₁, .yes) else if q.pos.tag == 0 || q.pos.tag == 1 ||
          q.pos.tag == 3 then pure (c₁, .infer) else pure (c₁, .no) :
          AM (ConRon.Arena.Modular.ReachCache × ConRon.Arena.Modular.ProofStatus)) =
          pure (c₁, if q.pos.tag == 2 then .yes else if q.pos.tag == 0 || q.pos.tag == 1 ||
            q.pos.tag == 3 then .infer else .no) := by
        split <;> (try split) <;> rfl
      rw [hk1] at k1
      obtain ⟨hv, rfl⟩ := AM.pure_ok k1
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact ⟨rfl, by rw [tagStatus_eq, htg], rfl⟩
    obtain ⟨rfl, hps, rfl⟩ := key
    refine ⟨hst1, cC₁, ?_, hc1⟩
    simp only [h1C, Bool.false_eq_true, ↓reduceIte]
    refine hgq.bind ?_
    rw [hps]
    exact ModelIO.gives_pure _ _

/-! ## Two copies' agreement -/

theorem statusIs_no (p : ConRon.Arena.Modular.ProofStatus) :
    ConRon.Arena.Modular.statusIs p false = (psC p == .no) := by
  cases p <;> rfl

theorem statusIs_yes (p : ConRon.Arena.Modular.ProofStatus) :
    ConRon.Arena.Modular.statusIs p true = (psC p == .yes) := by
  cases p <;> rfl

theorem nameText_ok {h : NIdx} {t : String} {s s' : AState}
    (hr : ConRon.Arena.Frontend.nameText h s = .ok (t, s')) : s' = s := by
  unfold ConRon.Arena.Frontend.nameText at hr
  obtain ⟨st, s₁, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  revert h2
  cases denoteN s₁.store.ns h <;> intro h2 <;> exact (AM.pure_ok h2).2

theorem captureWhat_ok {h y : NIdx} {t : String} {s s' : AState}
    (hr : ConRon.Arena.Modular.captureWhat h y s = .ok (t, s')) : s' = s := by
  unfold ConRon.Arena.Modular.captureWhat at hr
  obtain ⟨a, s₁, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨b, s₂, h3, h4⟩ := AM.bind_ok h2
  rw [(AM.pure_ok h4).2, nameText_ok h3, nameText_ok h1]

theorem pushReads_rel {st : EStore} {hh : NIdx} {hC : ConLeche.Name} (hd : denoteN st.ns hh = some hC) :
    ∀ (ys : List NIdx) {ns : List ConLeche.Name} {acc : Array (NIdx × NIdx)}
      {accC : Array (ConLeche.Name × ConLeche.Name)},
      denoteNList st.ns ys = some ns → ListRel (NN st) acc.toList accC.toList →
      ListRel (NN st) (ys.foldl (fun acc y => acc.push (hh, y)) acc).toList
        (accC.toList ++ ns.map (hC, ·))
  | [], ns, acc, accC, h, hr => by
    simp only [denoteNList, Option.some.injEq] at h
    subst h
    simpa using hr
  | y :: ys, ns, acc, accC, h, hr => by
    simp only [denoteNList] at h
    cases hy : denoteN st.ns y with
    | none => simp [hy] at h
    | some n =>
    cases hys : denoteNList st.ns ys with
    | none => simp [hy, hys] at h
    | some ns' =>
    simp only [hy, hys, Option.some.injEq] at h
    subst h
    rw [List.foldl_cons]
    have h1 : ListRel (NN st) (acc.push (hh, y)).toList (accC.push (hC, n)).toList := by
      rw [Array.toList_push, Array.toList_push]
      exact listRel_append hr (.cons ⟨hd, hy⟩ .nil)
    have := pushReads_rel hd ys hys h1
    rw [Array.toList_push, List.append_assoc] at this
    exact this

/-- con-leche: ConLeche/Driver/Reach.lean:404-406 partnerReads — a statement's names, each
with a home, onto the partners: upstream's. -/
theorem partnerReads_run (hN : NeedsExprHyp) {hh : NIdx} {hC : ConLeche.Name} {ty : EIdx}
    {tyC : Expr} {acc out : Array (NIdx × NIdx)} {accC : Array (ConLeche.Name × ConLeche.Name)}
    {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    (hd : denoteN s.store.ns hh = some hC) (ht : denoteE s.store ty = some tyC)
    (hr : ListRel (NN s.store) acc.toList accC.toList)
    (h : ConRon.Arena.Modular.partnerReads acc hh ty s = .ok (out, s')) :
    DStep s s' ∧ ListRel (NN s'.store) out.toList
      (accC ++ ConLeche.Driver.partnerReads hC tyC).toList := by
  unfold ConRon.Arena.Modular.partnerReads at h
  obtain ⟨x, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  obtain ⟨hst, hx⟩ := hN hok hoff ht h1
  refine ⟨hst, ?_⟩
  unfold ConLeche.Driver.partnerReads
  have := pushReads_rel (denoteN_ext hd hst.ext) x.acc hx
    (ListRel.mono' (fun _ _ h => h.ext hst.ext) hr)
  rw [Array.toList_append, Array.toList_map]
  simpa using this

theorem nidx_beq_iff {st : EStore} (hw : NStoreWF st.ns) {a b : NIdx} {aC bC : ConLeche.Name}
    (ha : denoteN st.ns a = some aC) (hb : denoteN st.ns b = some bC) : (a == b) = (aC == bC) := by
  by_cases h : a = b
  · subst h
    rw [ha] at hb; cases hb
    exact (beq_self_eq_true a).trans (beq_self_eq_true aC).symm
  · have : aC ≠ bC := fun he => h (denoteN_inj hw ha (he ▸ hb))
    rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr this]

/-- con-leche: ConLeche/Driver/Reach.lean:408-440 agreeCheck — **two copies of `y` agree**:
upstream's accept, the caches related after. -/
theorem agreeCheck_run (hN : NeedsExprHyp) {pk : OleanPins} {F : FS} {sp : Roots}
    (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {h y : NIdx} {hC yC : ConLeche.Name} {s₁ s₂ : ConRon.Arena.Modular.Spot}
    {s₁C s₂C : ConLeche.Driver.Spot} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hy : denoteN s.store.ns y = some yC)
    (h1 : SpotRel s.store s₁ s₁C) (h2 : SpotRel s.store s₂ s₂C)
    (hrun : ConRon.Arena.Modular.agreeCheck (modelFs F) pk sp env c h y s₁ s₂ s = .ok (c', s')) :
    DStep s s' ∧ ∃ cC', ModelIO.Gives (ConLeche.Driver.agreeCheck envC cC hC yC s₁C s₂C) F
        (cC', .ok ()) ∧ CacheRel s'.store c' cC' := by
  have hw := hctx.wf
  have hmods := nidx_beq_iff hw h1.1.1 h2.1.1
  unfold ConRon.Arena.Modular.agreeCheck at hrun
  unfold ConLeche.Driver.agreeCheck
  by_cases hm : (s₁.part.mod == s₂.part.mod) = true
  · simp only [hm, ↓reduceIte] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    rw [hmods] at hm
    simp only [hm, ↓reduceIte]
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  have hmC : (s₁C.part.mod == s₂C.part.mod) = false := by rw [← hmods]; simpa using hm
  simp only [hm, Bool.false_eq_true, ↓reduceIte, pure_bind] at hrun
  simp only [hmC, Bool.false_eq_true, ↓reduceIte]
  have hsk := h2.2.skipped
  by_cases hk : s₂.pos.skipped = true
  · simp only [hk, ↓reduceIte] at hrun
    am_never hrun
  simp only [hk, Bool.false_eq_true, ↓reduceIte] at hrun
  have hkC : s₂C.pos.skipped = false := by rw [← hsk]; simpa using hk
  simp only [hkC, Bool.false_eq_true, ↓reduceIte]
  -- the two statements
  obtain ⟨⟨c₁, cv₁, k₁⟩, t₁, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, cC₁, cvC₁, kC₁, hg1, hc1, hd1, hk1⟩ := stmtAt_run hsp hctx he hc h1 g1
  have hctx1 := hctx.step hst1
  have he1 := he.ext hst1.ext hctx1.wf
  obtain ⟨⟨c₂, cv₂, k₂⟩, t₂, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hst2, cC₂, cvC₂, kC₂, hg2, hc2, hd2, hk2⟩ :=
    stmtAt_run hsp hctx1 he1 hc1 (h2.ext hst1.ext) g2
  have hctx2 := hctx1.step hst2
  have he2 := he1.ext hst2.ext hctx2.wf
  have hd1' := denoteStmt_ext hst2.ext hd1
  -- one statement
  cases hsame : (cv₁.levelParams == cv₂.levelParams && cv₁.type == cv₂.type) with
  | false =>
    simp only [hsame, Bool.not_false, ↓reduceIte] at r2
    am_never r2
  | true =>
  simp only [hsame, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at r2
  have hsameC : (cvC₁.levelParams == cvC₂.levelParams && cvC₁.type == cvC₂.type) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq] at hsame ⊢
    obtain ⟨n1, l1, t1⟩ := denoteStmt_parts hd1'
    obtain ⟨n2, l2, t2⟩ := denoteStmt_parts hd2
    rw [hsame.1] at l1; rw [hsame.2] at t1
    exact ⟨Option.some.inj (l1.symm.trans l2), Option.some.inj (t1.symm.trans t2)⟩
  -- the proof flags
  obtain ⟨⟨c₃, p₁⟩, t₃, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨hst3, cC₃, hg3, hc3⟩ := proofStatus_run hsp hctx2 he2 hc2
    ((h1.ext hst1.ext).ext hst2.ext) (denoteKindN_ext hst2.ext hk1) g3
  have hctx3 := hctx2.step hst3
  have he3 := he2.ext hst3.ext hctx3.wf
  obtain ⟨⟨c₄, p₂⟩, t₄, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨hst4, cC₄, hg4, hc4⟩ := proofStatus_run hsp hctx3 he3 hc3
    ((h2.ext hst1.ext).ext (hst2.trans hst3).ext) (denoteKindN_ext hst3.ext hk2) g4
  have hctx4 := hctx3.step hst4
  rw [statusIs_no, statusIs_no] at r4
  by_cases hno : (psC p₁ == .no || psC p₂ == .no) = true
  · simp only [hno, ↓reduceIte] at r4
    am_never r4
  simp only [hno, Bool.false_eq_true, ↓reduceIte] at r4
  -- the partners
  obtain ⟨ps, t₅, g5, r5⟩ := AM.bind_ok r4
  have hs2m := denoteN_ext h2.1.1 ((((hst1.trans hst2).trans hst3).trans hst4)).ext
  obtain ⟨-, -, ht2⟩ := denoteStmt_parts (denoteStmt_ext (hst3.trans hst4).ext hd2)
  obtain ⟨hst5, hps⟩ := partnerReads_run hN hctx4.ok hctx4.off hs2m ht2 hc4.partners g5
  have hst45 := hst5
  rw [statusIs_yes, statusIs_yes] at r5
  have hc5 : CacheRel t₅.store { c₄ with partners := ps }
      { cC₄ with partners := cC₄.partners ++ ConLeche.Driver.partnerReads s₂C.part.mod cvC₂.type } :=
    { hc4.ext hst5.ext with partners := hps }
  have hall := (((hst1.trans hst2).trans hst3).trans hst4).trans hst5
  have hnoC : (psC p₁ == .no || psC p₂ == .no) = false := by simpa using hno
  by_cases hyes : (psC p₁ == .yes || psC p₂ == .yes) = true
  · simp only [hyes, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at r5
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r5
    refine ⟨hall, _, ?_, hc5⟩
    refine hg1.bind ?_
    refine hg2.bind ?_
    simp only [hsameC, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine hg3.bind ?_
    refine hg4.bind ?_
    simp only [hnoC, Bool.false_eq_true, ↓reduceIte, hyes]
    exact ModelIO.gives_pure _ _
  · simp only [hyes, Bool.not_false, ↓reduceIte] at r5
    obtain ⟨w, t₆, g6, r6⟩ := AM.bind_ok r5
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r6
    have e6 := captureWhat_ok g6
    subst e6
    let what : String := s!"name capture at {yC}, read by module {hC}"
    let parts' := cC₄.partners ++ ConLeche.Driver.partnerReads s₂C.part.mod cvC₂.type
    let cF : ConLeche.Driver.ReachCache :=
      { cC₄ with partners := parts', pending := cC₄.pending.push (what, yC, cvC₁) }
    refine ⟨hall, cF, ?_, { hc5 with pending := ?_ }⟩
    · refine hg1.bind ?_
      refine hg2.bind ?_
      simp only [hsameC, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine hg3.bind ?_
      refine hg4.bind ?_
      have hyesC : (psC p₁ == .yes || psC p₂ == .yes) = false := by simpa using hyes
      simp only [hnoC, Bool.false_eq_true, ↓reduceIte, hyesC]
      exact ModelIO.gives_pure _ _
    · show ListRel _ _ (cC₄.pending.push (what, yC, cvC₁)).toList
      simp only [Array.toList_push]
      exact listRel_append hc5.pending (.cons ⟨denoteN_ext hy hall.ext,
        denoteStmt_ext ((hst2.trans hst3).trans (hst4.trans hst5)).ext hd1⟩ .nil)

/-! ## The capture check -/

/-- con-leche: ConLeche/Driver/Reach.lean:480-486 inExported — **is `y` in module `m`'s
exported part**, upstream's answer. -/
theorem inExported_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {m y : NIdx} {mC yC : ConLeche.Name} {level : OLeanLevel} {b : Bool} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hm : denoteN s.store.ns m = some mC) (hy : denoteN s.store.ns y = some yC)
    (h : ConRon.Arena.Modular.inExported (modelFs F) pk sp env c m level y s = .ok ((c', b), s')) :
    DStep s s' ∧ ∃ cC', ModelIO.Gives (ConLeche.Driver.inExported envC cC mC level yC) F
        (cC', .ok b) ∧ CacheRel s'.store c' cC' := by
  unfold ConRon.Arena.Modular.inExported at h
  unfold ConLeche.Driver.inExported
  by_cases hl : (level == .exported) = true
  · simp only [hl, ↓reduceIte] at h ⊢
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  simp only [hl, Bool.false_eq_true, ↓reduceIte, pure_bind] at h ⊢
  obtain ⟨c₁, s₁, g1, k1⟩ := AM.bind_ok h
  obtain ⟨hst1, cC₁, lC, l, hgl, hc1, hl1, hlr⟩ := lookOf_run hsp hctx he hc
    (k := ⟨m, .exported⟩) (kC := ⟨mC, .exported⟩) ⟨hm, rfl⟩ g1
  obtain ⟨o, s₂, g2, k2⟩ := AM.bind_ok k1
  rw [lookAt_eq hl1] at g2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok g2
  obtain ⟨hv, rfl⟩ := AM.pure_ok k2
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  refine ⟨hst1, cC₁, ?_, hc1⟩
  refine hgl.bind ?_
  have := hmrel_contains (nsWF_of_StateOK hst1.ok.state) hlr (denoteN_ext hy hst1.ext)
  rw [Std.HashMap.contains_eq_isSome_getElem?] at this
  rw [this]
  exact ModelIO.gives_pure _ _

/-- con-leche: ConLeche/Driver/Reach.lean:488-531 captureOne — whether `h`'s public-import
closure holds the module at load position `i`, upstream's. -/
theorem pubHas_eq {sp : Roots} {st : EStore} {env : ConRon.Arena.Modular.ReachEnv}
    {envC : ConLeche.Driver.ReachEnv ModelIO} (he : EnvRel sp st env envC) {h : NIdx}
    {hC : ConLeche.Name} (hh : denoteN st.ns h = some hC) (i : Nat) :
    ConRon.Arena.Modular.pubHas env h i = (match envC.wr.loads.index[hC]? with
      | some hi => ((envC.wr.pub[hi]?).map (·.has i)).getD false
      | none => false) := by
  unfold ConRon.Arena.Modular.pubHas
  rw [he.wr.loads.index h hC hh, he.wr.pub]
  rfl

/-- con-leche: ConLeche/Driver/Reach.lean:488-531 captureOne — **a copy against the copy `h`'s
view holds**: the located copy, then the agreement; upstream's, whatever its rejecting message. -/
theorem captureAgainst_run (hN : NeedsExprHyp) {pk : OleanPins} {F : FS} {sp : Roots}
    (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {h y : NIdx} {hC yC : ConLeche.Name} {s₁ : ConRon.Arena.Modular.Spot}
    {s₁C : ConLeche.Driver.Spot} {s s' : AState} (bad : ConLeche.CheckError)
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hh : denoteN s.store.ns h = some hC) (hy : denoteN s.store.ns y = some yC)
    (h1 : SpotRel s.store s₁ s₁C)
    (hrun : ConRon.Arena.Modular.captureAgainst (modelFs F) pk sp env c h y s₁ s = .ok (c', s')) :
    DStep s s' ∧ ∃ cC', ModelIO.Gives (do
        match ← ConLeche.Driver.locate envC cC hC yC with
        | (c, .error e) => pure (c, .error e)
        | (c, .ok none) => pure (c, .error bad)
        | (c, .ok (some s₂)) => ConLeche.Driver.agreeCheck envC c hC yC s₁C s₂ :
          ModelIO (ConLeche.Driver.ReachCache × Except ConLeche.CheckError Unit)) F (cC', .ok ()) ∧
      CacheRel s'.store c' cC' := by
  unfold ConRon.Arena.Modular.captureAgainst at hrun
  obtain ⟨⟨c₁, o⟩, s₂, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, cC₁, oC, hgo, hc1, ho⟩ := locate_run hsp hctx he hc hh hy g1
  rcases optRel_cases ho with ⟨rfl, rfl⟩ | ⟨s₂', s₂C, rfl, rfl, hs2⟩
  · am_never k1
  have hctx1 := hctx.step hst1
  obtain ⟨hst2, cC', hga, hc'⟩ := agreeCheck_run hN hsp hctx1 (he.ext hst1.ext hctx1.wf) hc1
    (denoteN_ext hy hst1.ext) (h1.ext hst1.ext) hs2 k1
  exact ⟨hst1.trans hst2, cC', hgo.bind hga, hc'⟩

/-- con-leche: ConLeche/Driver/Reach.lean:488-531 captureOne — **the capture check of one read**
`y` of a record of home `h`, and the completion of a name the index lacks: upstream's accept, the
caches related after. -/
theorem captureOne_run (hN : NeedsExprHyp) {pk : OleanPins} {F : FS} {sp : Roots}
    (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache}
    {h y : NIdx} {hC yC : ConLeche.Name} {s s' : AState}
    (hctx : RCtx pk s) (he : EnvRel sp s.store env envC) (hc : CacheRel s.store c cC)
    (hh : denoteN s.store.ns h = some hC) (hy : denoteN s.store.ns y = some yC)
    (hrun : ConRon.Arena.Modular.captureOne (modelFs F) pk sp env c h y s = .ok (c', s')) :
    DStep s s' ∧ ∃ cC', ModelIO.Gives (ConLeche.Driver.captureOne envC cC hC yC) F (cC', .ok ()) ∧
      CacheRel s'.store c' cC' := by
  have hw := hctx.wf
  unfold ConRon.Arena.Modular.captureOne at hrun
  unfold ConLeche.Driver.captureOne
  have hown := he.own.contains hw hy
  by_cases ho : env.own.contains y = true
  · simp only [ho, ↓reduceIte] at hrun
    am_never hrun
  simp only [ho, Bool.false_eq_true, ↓reduceIte, pure_bind] at hrun
  have hoC : envC.own.contains yC = false := by rw [← hown]; simpa using ho
  simp only [hoC, Bool.false_eq_true, ↓reduceIte]
  rcases optRel_cases (importerSpot_rel hw hctx.nulls he hy) with ⟨g1, g2⟩ | ⟨⟨i, s₁⟩, ⟨iC, s₁C⟩, g1, g2, ⟨rfl, hs1⟩⟩
  · -- no importer copy
    rw [g1] at hrun
    rw [g2]
    dsimp only at hrun ⊢
    have hloc := hc.located.get hw hy
    rcases optRel_cases hloc with ⟨l1, l2⟩ | ⟨s₁, s₁C, l1, l2, hs1⟩
    · -- not located: complete it
      simp only [ConRon.Arena.Modular.locatedAt, l1] at hrun
      simp only [l2]
      obtain ⟨⟨c₁, o⟩, t₁, f1, r1⟩ := AM.bind_ok hrun
      obtain ⟨hst1, cC₁, oC, hgo, hc1, horel⟩ := locate_run hsp hctx he hc hh hy f1
      rcases optRel_cases horel with ⟨rfl, rfl⟩ | ⟨sp₁, spC, rfl, rfl, hsp1⟩
      · am_never r1
      have hctx1 := hctx.step hst1
      obtain ⟨⟨c₂, p⟩, t₂, f2, r2⟩ := AM.bind_ok r1
      obtain ⟨hst2, cC₂, pC, hgp, hc2, hp⟩ := privSpot_run hsp hctx1 (he.ext hst1.ext hctx1.wf) hc1
        hsp1 f2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
      have hall := hst1.trans hst2
      have hw2 := nsWF_of_StateOK hst2.ok.state
      let cF : ConLeche.Driver.ReachCache :=
        { cC₂ with located := cC₂.located.insert yC pC, completed := cC₂.completed.push (yC, hC) }
      have hL := hc2.located.insert hw2 (denoteN_ext hy hall.ext) hp
      refine ⟨hall, cF, ?_, { hc2 with located := hL, completed := ?_ }⟩
      · refine hgo.bind ?_
        refine hgp.bind ?_
        exact ModelIO.gives_pure _ _
      · show ListRel _ _ (cC₂.completed.push (yC, hC)).toList
        simp only [Array.toList_push]
        exact listRel_append hc2.completed (.cons ⟨denoteN_ext hy hall.ext, denoteN_ext hh hall.ext⟩ .nil)
    · -- a located copy
      simp only [ConRon.Arena.Modular.locatedAt, l1] at hrun
      simp only [l2]
      have hmods := nidx_beq_iff hw hs1.1.1 hh
      by_cases hm : (s₁.part.mod == h) = true
      · simp only [hm, ↓reduceIte] at hrun
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        rw [hmods] at hm
        simp only [hm, ↓reduceIte]
        exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
      simp only [hm, Bool.false_eq_true, ↓reduceIte] at hrun
      have hmC : (s₁C.part.mod == hC) = false := by rw [← hmods]; simpa using hm
      simp only [hmC, Bool.false_eq_true, ↓reduceIte]
      exact captureAgainst_run hN hsp _ hctx he hc hh hy hs1 hrun
  · -- an importer copy
    rw [g1] at hrun
    rw [g2]
    dsimp only at hrun ⊢
    have hmods := nidx_beq_iff hw hs1.1.1 hh
    by_cases hm : (s₁.part.mod == h) = true
    · simp only [hm, ↓reduceIte] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      rw [hmods] at hm
      simp only [hm, ↓reduceIte]
      exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
    simp only [hm, Bool.false_eq_true, ↓reduceIte] at hrun
    have hmC : (s₁C.part.mod == hC) = false := by rw [← hmods]; simpa using hm
    simp only [hmC, Bool.false_eq_true, ↓reduceIte]
    have hpb := pubHas_eq he hh i
    have hfalse : ConRon.Arena.Modular.pubHas env h i = false →
        DStep s s' ∧ ∃ cC', ModelIO.Gives (do
          let short ← (pure (cC, .ok false) : ModelIO (ConLeche.Driver.ReachCache × Except ConLeche.CheckError Bool))
          match short with
          | (c, .error e) => pure (c, .error e)
          | (c, .ok true) => pure (c, .ok ())
          | (c, .ok false) => do
            match ← ConLeche.Driver.locate envC c hC yC with
            | (c, .error e) => pure (c, .error e)
            | (c, .ok none) => pure (c, .error (.invalid s!"module {hC} reads {yC}, which its view does not hold"))
            | (c, .ok (some s₂)) => ConLeche.Driver.agreeCheck envC c hC yC s₁C s₂) F (cC', .ok ()) ∧
          CacheRel s'.store c' cC' := by
      intro hp
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at hrun
      obtain ⟨hst2, cC', hga, hc'⟩ := captureAgainst_run hN hsp
        (.invalid s!"module {hC} reads {yC}, which its view does not hold") hctx he hc hh hy hs1 hrun
      exact ⟨hst2, cC', (ModelIO.gives_pure _ _).bind hga, hc'⟩
    rcases hix : envC.wr.loads.index[hC]? with _ | hi
    · simp only [hix] at hpb
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hfalse hpb
    simp only [hix] at hpb ⊢
    by_cases hpX : ((envC.wr.pub[hi]?).map (·.has i)).getD false = true
    · have hp : ConRon.Arena.Modular.pubHas env h i = true := hpb.trans hpX
      simp only [hp, ↓reduceIte] at hrun
      simp only [hpX, ↓reduceIte]
      obtain ⟨⟨c₁, short⟩, t₁, f1, r1⟩ := AM.bind_ok hrun
      rw [hs1.1.2] at f1
      obtain ⟨hst1, cC₁, hgs, hc1⟩ := inExported_run hsp hctx he hc hs1.1.1 hy f1
      cases short with
      | true =>
        simp only [↓reduceIte] at r1
        obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
        exact ⟨hst1, cC₁, hgs.bind (ModelIO.gives_pure _ _), hc1⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at r1
        have hctx1 := hctx.step hst1
        obtain ⟨hst2, cC', hga, hc'⟩ := captureAgainst_run hN hsp
          (.invalid s!"module {hC} reads {yC}, which its view does not hold") hctx1
          (he.ext hst1.ext hctx1.wf) hc1 (denoteN_ext hh hst1.ext) (denoteN_ext hy hst1.ext)
          (hs1.ext hst1.ext) r1
        exact ⟨hst1.trans hst2, cC', hgs.bind hga, hc'⟩
    · have hpX' : ((envC.wr.pub[hi]?).map (·.has i)).getD false = false := by simpa using hpX
      have hp' : ConRon.Arena.Modular.pubHas env h i = false := hpb.trans hpX'
      simp only [hpX', Bool.false_eq_true, ↓reduceIte]
      exact hfalse hp'

/-- con-leche: ConLeche/Driver/Reach.lean:568-575 captureAll — **the capture check of every
read of a record**, upstream's accept. -/
theorem captureAll_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO}
    {h : NIdx} {hC : ConLeche.Name} :
    ∀ (ys : List NIdx) {ysC : List ConLeche.Name}
      {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache} {s s' : AState},
      RCtx pk s → EnvRel sp s.store env envC → CacheRel s.store c cC →
      denoteN s.store.ns h = some hC → ListRel (NR s.store) ys ysC →
      ConRon.Arena.Modular.captureAll (modelFs F) pk sp env h c ys s = .ok (c', s') →
      DStep s s' ∧ ∃ cC', ModelIO.Gives (ConLeche.Driver.captureAll envC hC cC ysC) F (cC', .ok ()) ∧
        CacheRel s'.store c' cC'
  | [], _, c, c', cC, s, s', hctx, _, hc, _, .nil, hrun => by
    rw [ConRon.Arena.Modular.captureAll] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  | y :: ys, _, c, c', cC, s, s', hctx, he, hc, hh, .cons hy hys, hrun => by
    rw [ConRon.Arena.Modular.captureAll] at hrun
    obtain ⟨c₁, s₁, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨hst1, cC₁, hg1, hc1⟩ := captureOne_run needsExprHyp_holds hsp hctx he hc hh hy g1
    have hctx1 := hctx.step hst1
    obtain ⟨hst2, cC', hg2, hc'⟩ := captureAll_run hsp ys hctx1 (he.ext hst1.ext hctx1.wf) hc1
      (denoteN_ext hh hst1.ext) (ListRel.mono' (fun _ _ h => denoteN_ext h hst1.ext) hys) k1
    exact ⟨hst1.trans hst2, cC', by rw [ConLeche.Driver.captureAll]; exact hg1.bind hg2, hc'⟩

/-- con-leche: ConLeche/Driver/Reach.lean:577-584 capturePairs — **the partners' reads
checked**, upstream's accept. -/
theorem capturePairs_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {env : ConRon.Arena.Modular.ReachEnv} {envC : ConLeche.Driver.ReachEnv ModelIO} :
    ∀ (ps : List (NIdx × NIdx)) {psC : List (ConLeche.Name × ConLeche.Name)}
      {c c' : ConRon.Arena.Modular.ReachCache} {cC : ConLeche.Driver.ReachCache} {s s' : AState},
      RCtx pk s → EnvRel sp s.store env envC → CacheRel s.store c cC →
      ListRel (NN s.store) ps psC →
      ConRon.Arena.Modular.capturePairs (modelFs F) pk sp env c ps s = .ok (c', s') →
      DStep s s' ∧ ∃ cC', ModelIO.Gives (ConLeche.Driver.capturePairs envC cC psC) F (cC', .ok ()) ∧
        CacheRel s'.store c' cC'
  | [], _, c, c', cC, s, s', hctx, _, hc, .nil, hrun => by
    rw [ConRon.Arena.Modular.capturePairs] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  | (h, y) :: ps, _, c, c', cC, s, s', hctx, he, hc, .cons hp hps, hrun => by
    rw [ConRon.Arena.Modular.capturePairs] at hrun
    obtain ⟨c₁, s₁, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨hst1, cC₁, hg1, hc1⟩ := captureOne_run needsExprHyp_holds hsp hctx he hc hp.1 hp.2 g1
    have hctx1 := hctx.step hst1
    obtain ⟨hst2, cC', hg2, hc'⟩ := capturePairs_run hsp ps hctx1 (he.ext hst1.ext hctx1.wf) hc1
      (ListRel.mono' (fun _ _ h => h.ext hst1.ext) hps) k1
    exact ⟨hst1.trans hst2, cC', by rw [ConLeche.Driver.capturePairs]; exact hg1.bind hg2, hc'⟩


end ConRon.Bridge.Modular
