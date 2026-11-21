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

/-- con-leche: ConLeche/Driver/Reach.lean:376-382 ProofStatus — the twin's flag as upstream's. -/
@[expose] def psC : ConRon.Arena.Modular.ProofStatus → ConLeche.Driver.ProofStatus
  | .yes => .yes
  | .no => .no
  | .infer => .infer

/-! ## A loaded copy's spot -/

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:110-111 HeaderLoads.nameAt — a module's
name for messages, read back. -/
theorem nameAt_rel {st : EStore} {pk : OleanPins} (hp : NullsRel st pk)
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
      refine .some ⟨rfl, ⟨nameAt_rel hp he.wr.loads cp.mod, ?_⟩, g3⟩
      simp [ConRon.Arena.Frontend.Olean.HeaderLoads.levelAt, he.wr.loads.flags]

/-! ## A copy's proof flag -/

theorem tagStatus_eq (n : Nat) :
    psC (if n == 2 then .yes else if n == 0 || n == 1 || n == 3 then .infer else .no) =
      (match n with
        | 2 => .yes
        | 0 | 1 | 3 => .infer
        | _ => .no) := by
  rcases n with _ | _ | _ | _ | n <;> simp [psC]
  omega

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
  unfold ConRon.Arena.Modular.proofStatus at h
  unfold ConLeche.Driver.proofStatus
  cases k with
  | thm v all =>
    simp only [denoteKindN, CKindF.mapM] at hk
    obtain ⟨as, -, hk⟩ := ConLeche.Frontend.Olean.bind_some_left hk
    cases hk
    obtain ⟨rfl, rfl, rfl⟩ := refl h
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  | defn v hh sf =>
    simp only [denoteKindN, CKindF.mapM] at hk
    cases hk
    obtain ⟨rfl, rfl, rfl⟩ := refl h
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  | opaq v u =>
    simp only [denoteKindN, CKindF.mapM] at hk
    cases hk
    obtain ⟨rfl, rfl, rfl⟩ := refl h
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  | ax u =>
    simp only [denoteKindN, CKindF.mapM] at hk
    cases hk
    have hlev : (sp₀.part.level == .private) = (spC.part.level == .private) := by rw [hs.1.2]
    by_cases h1 : (sp₀.part.level == .private) = true
    · simp only [h1, ↓reduceIte] at h
      obtain ⟨rfl, rfl, rfl⟩ := refl h
      rw [hlev] at h1
      refine ⟨DStep.refl hctx.ok hctx.off, cC, ?_, hc⟩
      simp only [h1, ↓reduceIte]
      exact ModelIO.gives_pure _ _
    simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
    obtain ⟨⟨c₁, q⟩, s₁, g1, k1⟩ := AM.bind_ok h
    obtain ⟨hst1, cC₁, qC, hgq, hc1, hq⟩ := privSpot_run hsp hctx he hc hs g1
    have h1C : (spC.part.level == .private) = false := by rw [← hlev]; simpa using h1
    have htag := hq.2.tag
    have key : ∀ x, (x : AM (ConRon.Arena.Modular.ReachCache × ConRon.Arena.Modular.ProofStatus)) =
        pure (c₁, if q.pos.tag == 2 then .yes else if q.pos.tag == 0 || q.pos.tag == 1 ||
          q.pos.tag == 3 then .infer else .no) → x s₁ = .ok ((c', p), s') →
        c' = c₁ ∧ psC p = (match qC.pos.tag with | 2 => .yes | 0 | 1 | 3 => .infer | _ => .no) ∧
          s' = s₁ := by
      intro x hx hrun
      rw [hx] at hrun
      obtain ⟨hv, rfl⟩ := AM.pure_ok hrun
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact ⟨rfl, by rw [tagStatus_eq, htag], rfl⟩
    obtain ⟨rfl, hps, rfl⟩ := key _ (by
      by_cases t2 : q.pos.tag == 2 <;> simp only [t2, ↓reduceIte] <;>
        by_cases t0 : (q.pos.tag == 0 || q.pos.tag == 1 || q.pos.tag == 3) <;>
          simp [t0]) k1
    refine ⟨hst1, cC₁, ?_, hc1⟩
    simp only [h1C, Bool.false_eq_true, ↓reduceIte]
    refine hgq.bind ?_
    rw [hps]
    exact ModelIO.gives_pure _ _
  | quot q =>
    simp only [denoteKindN, CKindF.mapM] at hk
    cases hk
    obtain ⟨rfl, rfl, rfl⟩ := refl h
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  | induct np ni all cs nn ir iu irf =>
    simp only [denoteKindN, CKindF.mapM] at hk
    obtain ⟨_, -, hk⟩ := ConLeche.Frontend.Olean.bind_some_left hk
    obtain ⟨_, -, hk⟩ := ConLeche.Frontend.Olean.bind_some_left hk
    cases hk
    obtain ⟨rfl, rfl, rfl⟩ := refl h
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  | ctor ind ci np nf iu =>
    simp only [denoteKindN, CKindF.mapM] at hk
    obtain ⟨_, -, hk⟩ := ConLeche.Frontend.Olean.bind_some_left hk
    cases hk
    obtain ⟨rfl, rfl, rfl⟩ := refl h
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩
  | recur all np ni nmo nmi rules kk iu =>
    rw [denoteKindN, recur_mapM] at hk
    obtain ⟨_, -, hk⟩ := ConLeche.Frontend.Olean.bind_some_left hk
    obtain ⟨_, -, hk⟩ := ConLeche.Frontend.Olean.bind_some_left hk
    cases hk
    obtain ⟨rfl, rfl, rfl⟩ := refl h
    exact ⟨DStep.refl hctx.ok hctx.off, cC, ModelIO.gives_pure _ _, hc⟩

end ConRon.Bridge.Modular
