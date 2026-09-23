/-
# `ConRon.Bridge.Frontend.Scratch` — the projection rewrite and the owner
census leave the scratch flag where they found it (task #97-P3-Frontend
round 8)

`ParseStep`'s `scratch` clause (`Bridge/Frontend/Rel.lean`) is what threads
`scratchOn = false` through the parse, and every other step of the parse gets
it from an intern spec that states it.  The two exceptions are the projection
rewrite (`Arena/Frontend/ProjRec.lean`'s `projRecValue`) and the owner census
(`projRecOwners`), whose callees' specs — the Inductives tier's recognisers at
`PStep`, and `Bridge/ExprOps/**`'s `…Fast` walks — do not frame the flag.
Round 8's ruling: rather than widen those tiers' frames, prove here that the
two functions' whole call trees never move it.  The only writers of
`scratchOn` in the arena are `enterScratch`/`dropScratch`, and neither is in
either call tree; this module is that observation as a proof.
-/
import ConRon.Bridge.Specs
import ConRon.Arena.Frontend.ProjRec

namespace ConRon.Bridge.Frontend

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The predicate and its combinators -/

/-- con-leche: none — **`c` keeps the scratch flag at `b`**: from a state
whose flag is `b`, every accepting run of `c` ends at a state whose flag is
`b`.  Relative to `b` rather than an equation between the two states so that
a `get`-then-`set` body can be read with the gotten state's flag in hand. -/
def SPb {α : Type} (b : Bool) (c : AM α) : Prop :=
  ∀ (s s' : AState) (r : α), s.store.scratchOn = b → c s = .ok (r, s') →
    s'.store.scratchOn = b

namespace SPb

/-- con-leche: none — `pure` moves nothing. -/
theorem pure' {α : Type} {b : Bool} (a : α) : SPb b (pure a : AM α) := by
  intro s s' r hs h
  simp only [Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact hs

/-- con-leche: none — a bind keeps the flag if both halves do. -/
theorem bind' {α β : Type} {b : Bool} {c : AM α} {f : α → AM β}
    (hc : SPb b c) (hf : ∀ a, SPb b (f a)) : SPb b (c >>= f) := by
  intro s s' r hs h
  change (c s >>= fun p => f p.1 p.2) = _ at h
  revert h
  cases hx : c s with
  | error e => intro h; exact nomatch h
  | ok p =>
    obtain ⟨a, s₁⟩ := p
    intro h
    exact hf a s₁ s' r (hc s s₁ a hs hx) h

/-- con-leche: none — a `get` hands the continuation a state whose flag is `b`. -/
theorem get_bind {β : Type} {b : Bool} {f : AState → AM β}
    (hf : ∀ t, t.store.scratchOn = b → SPb b (f t)) : SPb b (get >>= f) := by
  intro s s' r hs h
  exact hf s hs s s' r hs h

/-- con-leche: none — `get` moves nothing. -/
theorem get' {b : Bool} : SPb b (get : AM AState) := by
  intro s s' r hs h
  simp only [get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact hs

/-- con-leche: none — a `set` keeps the flag if the new state has it. -/
theorem set' {b : Bool} {t : AState} (ht : t.store.scratchOn = b) :
    SPb b (set t : AM Unit) := by
  intro s s' r _ h
  simp only [set, MonadStateOf.set, StateT.set, Pure.pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact ht

/-- con-leche: none — a `modify` keeps the flag if its function does. -/
theorem modify' {b : Bool} {g : AState → AState}
    (hg : ∀ t, t.store.scratchOn = b → (g t).store.scratchOn = b) :
    SPb b (modify g : AM Unit) := by
  intro s s' r hs h
  simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Pure.pure,
    Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact hg s hs

/-- con-leche: none — `fail` never succeeds. -/
theorem fail' {α : Type} {b : Bool} (e : Arena.CheckError) : SPb b (fail e : AM α) := by
  intro s s' r _ h
  exact nomatch h

/-- con-leche: none — `throw` never succeeds. -/
theorem throw' {α : Type} {b : Bool} (e : Arena.CheckError) :
    SPb b (throw e : AM α) := by
  intro s s' r _ h
  exact nomatch h

end SPb

open Lean Elab Tactic Meta in
/-- con-leche: none — close an `SPb` goal with an induction hypothesis
(a local `∀ …, SPb _ _`), at reducible transparency. -/
elab "sp_ih" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let (xs, _, concl) ← forallMetaTelescope (← instantiateMVars ldecl.type)
      unless concl.isAppOf ``SPb do continue
      let ok ← withReducible (isDefEq concl tgt)
      if ok then
        let pf ← instantiateMVars (mkAppN (mkFVar ldecl.fvarId) xs)
        unless pf.hasExprMVar do
          g.assign pf
          replaceMainGoal []
          return
    throwError "sp_ih: no hypothesis"

/-- con-leche: none — the registry the automation below consults: one
`macro_rules` alternative per lemma of this module. -/
syntax "sp_lemma" : tactic
macro_rules | `(tactic| sp_lemma) => `(tactic| fail "no sp lemma")

/-- con-leche: none — the side conditions a `set`/`modify` leaves. -/
syntax "sp_side" : tactic
macro_rules
  | `(tactic| sp_side) => `(tactic| first
      | assumption
      | (simp_all only [NStore.scratchOn_intern, LStore.scratchOn_intern,
          LsStore.scratchOn_intern, EStore.scratchOn_intern, EStore.scratchOn_internName,
          EStore.scratchOn_internLevel, EStore.scratchOn_internLevels]; done)
      | (simp_all [EStore.scratchOn_intern, EStore.scratchOn_internName,
          EStore.scratchOn_internLevel, EStore.scratchOn_internLevels]; done))

/-- con-leche: none — one step of the automation. -/
syntax "sp_step" : tactic
macro_rules
  | `(tactic| sp_step) => `(tactic| first
      | with_reducible exact SPb.pure' _
      | with_reducible exact SPb.fail' _
      | with_reducible exact SPb.throw' _
      | with_reducible exact SPb.get'
      | (with_reducible apply SPb.get_bind; intro _ _)
      | (with_reducible apply SPb.bind' (c := get) SPb.get'; intro _)
      | (with_reducible apply SPb.set'; sp_side)
      | (with_reducible apply SPb.modify'; intro _ _; sp_side)
      | (with_reducible apply SPb.bind' <;> try intro _)
      | with_reducible sp_lemma
      | with_reducible assumption
      | sp_ih
      | split
      | dsimp only)

/-- con-leche: none — the automation. -/
syntax "sp_auto" : tactic
macro_rules | `(tactic| sp_auto) => `(tactic| repeat' sp_step)

/-- con-leche: none — `view` reads. -/
theorem view_sp (b : Bool) (h : EIdx) : SPb b (view h) := by unfold view; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact view_sp _ _)

/-- con-leche: none — the typed projections the tag-first twins read
(task #97-T2-LOCKSTEP), and their dangling-handle arm, read only. -/
theorem viewBind_sp (b : Bool) (h : EIdx) : SPb b (viewBind h) := by unfold viewBind; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact viewBind_sp _ _)
theorem viewBindI_sp (b : Bool) (h : EIdx) : SPb b (viewBindI h) := by unfold viewBindI; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact viewBindI_sp _ _)
theorem viewFVarTy_sp (b : Bool) (h : EIdx) : SPb b (viewFVarTy h) := by
  unfold viewFVarTy; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact viewFVarTy_sp _ _)
theorem failDanglingE_sp (b : Bool) {α : Type} : SPb b (failDanglingE : AM α) := by
  unfold failDanglingE; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact failDanglingE_sp _)

/-- con-leche: none — `internNodeE` interns in the tier it found. -/
theorem internNodeE_sp (b : Bool) (w : ENodeView) : SPb b (internNodeE w) := by
  unfold internNodeE; sp_auto

/-- con-leche: none — `internE` interns in the tier it found: the eight node
arms are `internNodeE`, and the two binder arms (task #97-T2-LOCKSTEP D6) are
the datum step and the node step, neither of which moves the flag. -/
theorem internE_sp (b : Bool) (w : ENodeView) : SPb b (internE w) := by
  intro s s' r hs h
  cases w
  case lam ty bd m =>
    obtain ⟨mi, s₁, h1, h2⟩ := internE_lam_split h
    obtain ⟨-, rfl, rfl⟩ := internBME_ok h1
    obtain ⟨-, rfl⟩ := internLamIE_ok h2
    simp only [EStore.internLamI, EStore.scratchOn_internBindI, EStore.scratchOn_internBM]
    exact hs
  case forallE ty bd m =>
    obtain ⟨mi, s₁, h1, h2⟩ := internE_forallE_split h
    obtain ⟨-, rfl, rfl⟩ := internBME_ok h1
    obtain ⟨-, rfl⟩ := internForallEIE_ok h2
    simp only [EStore.internForallEI, EStore.scratchOn_internBindI,
      EStore.scratchOn_internBM]
    exact hs
  all_goals exact internNodeE_sp b _ s s' r hs h
macro_rules | `(tactic| sp_lemma) => `(tactic| exact internE_sp _ _)

/-- con-leche: none — `internNNode`. -/
theorem internNNode_sp (b : Bool) (w : NNodeView) : SPb b (internNNode w) := by
  unfold internNNode; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact internNNode_sp _ _)

/-- con-leche: none — `internName`. -/
theorem internName_sp (b : Bool) : ∀ n, SPb b (internName n) := by
  intro n; induction n <;> unfold internName <;> sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact internName_sp _ _)

/-! ## The call trees, callees first -/

/-- con-leche: none — `stripPis` keeps the scratch flag. -/
theorem sp_stripPis (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.stripPis x0 x1) := by
  intro x0 x1
  induction x0 generalizing x1 <;> (unfold ConRon.Arena.stripPis; sp_auto)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_stripPis _ _ _)

/-- con-leche: none — `readLevel` keeps the scratch flag. -/
theorem sp_readLevel (b : Bool) : ∀ x0, SPb b (ConRon.Arena.readLevel x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.readLevel; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.readLevel; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_readLevel _ _)

/-- con-leche: none — `Frontend.projRecCandidates` keeps the scratch flag. -/
theorem sp_projRecCandidates (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.Frontend.projRecCandidates x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.Frontend.projRecCandidates; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.Frontend.projRecCandidates; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.Frontend.projRecCandidates; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.Frontend.projRecCandidates; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.Frontend.projRecCandidates; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_projRecCandidates _ _ _ _ _)

/-- con-leche: none — `Frontend.stripPisAll` keeps the scratch flag. -/
theorem sp_stripPisAll (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.Frontend.stripPisAll x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.Frontend.stripPisAll; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.Frontend.stripPisAll; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.Frontend.stripPisAll; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_stripPisAll _ _ _)

/-- con-leche: none — `Frontend.occursConstGo` keeps the scratch flag. -/
theorem sp_occursConstGo (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.Frontend.occursConstGo x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.Frontend.occursConstGo; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.Frontend.occursConstGo; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.Frontend.occursConstGo; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.Frontend.occursConstGo; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.Frontend.occursConstGo; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_occursConstGo _ _ _ _ _)

/-- con-leche: none — `Frontend.occursConstFast` keeps the scratch flag. -/
theorem sp_occursConstFast (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.Frontend.occursConstFast x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.Frontend.occursConstFast; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.Frontend.occursConstFast; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.Frontend.occursConstFast; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.Frontend.occursConstFast; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_occursConstFast _ _ _ _)

/-- con-leche: none — `Frontend.occursAnyOf` keeps the scratch flag. -/
theorem sp_occursAnyOf (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.Frontend.occursAnyOf x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.Frontend.occursAnyOf; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.Frontend.occursAnyOf; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.Frontend.occursAnyOf; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.Frontend.occursAnyOf; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_occursAnyOf _ _ _ _)

/-- con-leche: none — `Frontend.domsMentionAny` keeps the scratch flag. -/
theorem sp_domsMentionAny (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.Frontend.domsMentionAny x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.Frontend.domsMentionAny; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.Frontend.domsMentionAny; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.Frontend.domsMentionAny; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.Frontend.domsMentionAny; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_domsMentionAny _ _ _ _)

/-- con-leche: none — `Frontend.ctorsMentionBlock` keeps the scratch flag. -/
theorem sp_ctorsMentionBlock (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.Frontend.ctorsMentionBlock x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.Frontend.ctorsMentionBlock; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.Frontend.ctorsMentionBlock; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.Frontend.ctorsMentionBlock; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.Frontend.ctorsMentionBlock; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_ctorsMentionBlock _ _ _ _)

/-- con-leche: none — `pinAt` keeps the scratch flag. -/
theorem sp_pinAt (b : Bool) : ∀ x0, SPb b (ConRon.Arena.pinAt x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.pinAt; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.pinAt; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_pinAt _ _)

/-- con-leche: none — `pinEq` keeps the scratch flag. -/
theorem sp_pinEq (b : Bool) : SPb b (ConRon.Arena.pinEq) := by
  first
  | (unfold ConRon.Arena.pinEq; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_pinEq _)

/-- con-leche: none — `pin` keeps the scratch flag. -/
theorem sp_pin (b : Bool) : ∀ x0, SPb b (ConRon.Arena.pin x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.pin; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.pin; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_pin _ _)

/-- con-leche: none — `pinNat` keeps the scratch flag. -/
theorem sp_pinNat (b : Bool) : SPb b (ConRon.Arena.pinNat) := by
  first
  | (unfold ConRon.Arena.pinNat; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_pinNat _)

/-- con-leche: none — `pinNatZero` keeps the scratch flag. -/
theorem sp_pinNatZero (b : Bool) : SPb b (ConRon.Arena.pinNatZero) := by
  first
  | (unfold ConRon.Arena.pinNatZero; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_pinNatZero _)

/-- con-leche: none — `pinNatSucc` keeps the scratch flag. -/
theorem sp_pinNatSucc (b : Bool) : SPb b (ConRon.Arena.pinNatSucc) := by
  first
  | (unfold ConRon.Arena.pinNatSucc; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_pinNatSucc _)

/-- con-leche: none — `pinPUnit` keeps the scratch flag. -/
theorem sp_pinPUnit (b : Bool) : SPb b (ConRon.Arena.pinPUnit) := by
  first
  | (unfold ConRon.Arena.pinPUnit; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_pinPUnit _)

/-- con-leche: none — `pinQuotSound` keeps the scratch flag. -/
theorem sp_pinQuotSound (b : Bool) : SPb b (ConRon.Arena.pinQuotSound) := by
  first
  | (unfold ConRon.Arena.pinQuotSound; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_pinQuotSound _)

/-- con-leche: none — `reservedBasisNames` keeps the scratch flag. -/
theorem sp_reservedBasisNames (b : Bool) : SPb b (ConRon.Arena.reservedBasisNames) := by
  first
  | (unfold ConRon.Arena.reservedBasisNames ConRon.Arena.pinReserved; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_reservedBasisNames _)

/-- con-leche: none — `stripLams` keeps the scratch flag. -/
theorem sp_stripLams (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.stripLams x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.stripLams; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.stripLams; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.stripLams; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_stripLams _ _ _)

/-- con-leche: none — `pinZeroLevel` keeps the scratch flag. -/
theorem sp_pinZeroLevel (b : Bool) : SPb b (ConRon.Arena.pinZeroLevel) := by
  first
  | (unfold ConRon.Arena.pinZeroLevel; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_pinZeroLevel _)

/-- con-leche: none — `zeroLevel` keeps the scratch flag. -/
theorem sp_zeroLevel (b : Bool) : SPb b (ConRon.Arena.zeroLevel) := by
  first
  | (unfold ConRon.Arena.zeroLevel; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_zeroLevel _)

/-- con-leche: none — `readLevelM` keeps the scratch flag. -/
theorem sp_readLevelM (b : Bool) : ∀ x0, SPb b (ConRon.Arena.readLevelM x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.readLevelM; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.readLevelM; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_readLevelM _ _)

/-- con-leche: none — `lvlEq?` keeps the scratch flag. -/
theorem sp_lvlEq? (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.lvlEq? x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.lvlEq?; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.lvlEq?; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.lvlEq?; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_lvlEq? _ _ _)

/-- con-leche: none — `internLNode` keeps the scratch flag. -/
theorem sp_internLNode (b : Bool) : ∀ x0, SPb b (ConRon.Arena.internLNode x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.internLNode; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.internLNode; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internLNode _ _)

/-- con-leche: none — `paramLevels.go` keeps the scratch flag. -/
theorem sp_paramLevels_go (b : Bool) : ∀ x0, SPb b (ConRon.Arena.paramLevels.go x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.paramLevels.go; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.paramLevels.go; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_paramLevels_go _ _)

/-- con-leche: none — `internLsNode` keeps the scratch flag. -/
theorem sp_internLsNode (b : Bool) : ∀ x0, SPb b (ConRon.Arena.internLsNode x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.internLsNode; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.internLsNode; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internLsNode _ _)

/-- con-leche: none — `paramLevels` keeps the scratch flag. -/
theorem sp_paramLevels (b : Bool) : ∀ x0, SPb b (ConRon.Arena.paramLevels x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.paramLevels; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.paramLevels; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_paramLevels _ _)

/-- con-leche: none — `structPsAt.go` keeps the scratch flag. -/
theorem sp_structPsAt_go (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.structPsAt.go x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.structPsAt.go; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.structPsAt.go; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.structPsAt.go; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.structPsAt.go; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.structPsAt.go; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_structPsAt_go _ _ _ _ _)

/-- con-leche: none — `structPsAt` keeps the scratch flag. -/
theorem sp_structPsAt (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.structPsAt x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.structPsAt; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.structPsAt; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.structPsAt; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_structPsAt _ _ _)

/-- con-leche: none — `mkAppN` keeps the scratch flag. -/
theorem sp_mkAppN (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.mkAppN x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.mkAppN; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.mkAppN; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.mkAppN; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_mkAppN _ _ _)

/-- con-leche: none — `structFam` keeps the scratch flag. -/
theorem sp_structFam (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.structFam x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.structFam; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.structFam; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.structFam; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.structFam; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.structFam; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_structFam _ _ _ _ _)

/-- con-leche: none — `bvarsDesc` keeps the scratch flag. -/
theorem sp_bvarsDesc (b : Bool) : ∀ x0, SPb b (ConRon.Arena.bvarsDesc x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.bvarsDesc; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.bvarsDesc; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarsDesc _ _)

/-- con-leche: none — `structCtorSpine` keeps the scratch flag. -/
theorem sp_structCtorSpine (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.structCtorSpine x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.structCtorSpine; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.structCtorSpine; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.structCtorSpine; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.structCtorSpine; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.structCtorSpine; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_structCtorSpine _ _ _ _ _)

/-- con-leche: none — `structShape` keeps the scratch flag. -/
theorem sp_structShape (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, SPb b (ConRon.Arena.structShape x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
  first
  | (unfold ConRon.Arena.structShape; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 x7 x8 x9 <;> (unfold ConRon.Arena.structShape; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 x7 x8 x9 <;> (unfold ConRon.Arena.structShape; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 x7 x8 x9 <;> (unfold ConRon.Arena.structShape; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 x7 x8 x9 <;> (unfold ConRon.Arena.structShape; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 x7 x8 x9 <;> (unfold ConRon.Arena.structShape; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 x7 x8 x9 <;> (unfold ConRon.Arena.structShape; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 x7 x8 x9 <;> (unfold ConRon.Arena.structShape; sp_auto) <;> done)
  | (induction x7 generalizing x0 x1 x2 x3 x4 x5 x6 x8 x9 <;> (unfold ConRon.Arena.structShape; sp_auto) <;> done)
  | (induction x8 generalizing x0 x1 x2 x3 x4 x5 x6 x7 x9 <;> (unfold ConRon.Arena.structShape; sp_auto) <;> done)
  | (induction x9 generalizing x0 x1 x2 x3 x4 x5 x6 x7 x8 <;> (unfold ConRon.Arena.structShape; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_structShape _ _ _ _ _ _ _ _ _ _ _)

/-- con-leche: none — `structRuleBody` keeps the scratch flag. -/
theorem sp_structRuleBody (b : Bool) : ∀ x0, SPb b (ConRon.Arena.structRuleBody x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.structRuleBody; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.structRuleBody; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_structRuleBody _ _)

/-- con-leche: none — `structPartsCore?` keeps the scratch flag. -/
theorem sp_structPartsCore? (b : Bool) : ∀ x0, SPb b (ConRon.Arena.structPartsCore? x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.structPartsCore?; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.structPartsCore?; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_structPartsCore? _ _)

/-- con-leche: none — `piBinders` keeps the scratch flag. -/
theorem sp_piBinders (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.piBinders x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.piBinders; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.piBinders; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.piBinders; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_piBinders _ _ _)

/-- con-leche: none — `nativeCounts?` keeps the scratch flag. -/
theorem sp_nativeCounts? (b : Bool) : ∀ x0 x1 x2 x3 x4, SPb b (ConRon.Arena.nativeCounts? x0 x1 x2 x3 x4) := by
  intro x0 x1 x2 x3 x4
  first
  | (unfold ConRon.Arena.nativeCounts?; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 <;> (unfold ConRon.Arena.nativeCounts?; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 <;> (unfold ConRon.Arena.nativeCounts?; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 <;> (unfold ConRon.Arena.nativeCounts?; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 <;> (unfold ConRon.Arena.nativeCounts?; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 <;> (unfold ConRon.Arena.nativeCounts?; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_nativeCounts? _ _ _ _ _ _)

/-- con-leche: none — `nativeShape?` keeps the scratch flag. -/
theorem sp_nativeShape? (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.nativeShape? x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.nativeShape?; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.nativeShape?; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.nativeShape?; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_nativeShape? _ _ _)

/-- con-leche: none — `nativeParts?` keeps the scratch flag. -/
theorem sp_nativeParts? (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.nativeParts? x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.nativeParts?; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.nativeParts?; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.nativeParts?; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_nativeParts? _ _ _)

/-- con-leche: none — `Frontend.projRecOwners` keeps the scratch flag. -/
theorem sp_projRecOwners (b : Bool) : ∀ x0 x1 x2 x3 x4, SPb b (ConRon.Arena.Frontend.projRecOwners x0 x1 x2 x3 x4) := by
  intro x0 x1 x2 x3 x4
  first
  | (unfold ConRon.Arena.Frontend.projRecOwners; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 <;> (unfold ConRon.Arena.Frontend.projRecOwners; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 <;> (unfold ConRon.Arena.Frontend.projRecOwners; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 <;> (unfold ConRon.Arena.Frontend.projRecOwners; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 <;> (unfold ConRon.Arena.Frontend.projRecOwners; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 <;> (unfold ConRon.Arena.Frontend.projRecOwners; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_projRecOwners _ _ _ _ _ _)

/-- con-leche: none — `Frontend.projRecValue.internParamLevels` keeps the scratch flag. -/
theorem sp_projRecValue_internParamLevels (b : Bool) : ∀ x0, SPb b (ConRon.Arena.Frontend.projRecValue.internParamLevels x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.Frontend.projRecValue.internParamLevels; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.Frontend.projRecValue.internParamLevels; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_projRecValue_internParamLevels _ _)

/-- con-leche: none — `derivedE` keeps the scratch flag. -/
theorem sp_derivedE (b : Bool) : ∀ x0, SPb b (ConRon.Arena.derivedE x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.derivedE; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.derivedE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_derivedE _ _)

/-- con-leche: none — `readNameM` keeps the scratch flag. -/
theorem sp_readNameM (b : Bool) : ∀ x0, SPb b (ConRon.Arena.readNameM x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.readNameM; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.readNameM; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_readNameM _ _)

/-- con-leche: none — `readNamesM` keeps the scratch flag. -/
theorem sp_readNamesM (b : Bool) : ∀ x0, SPb b (ConRon.Arena.readNamesM x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.readNamesM; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.readNamesM; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_readNamesM _ _)

/-- con-leche: none — `failDanglingLs` keeps the scratch flag. -/
theorem sp_failDanglingLs (b : Bool) {α : Type} : SPb b (ConRon.Arena.failDanglingLs : AM α) := by
  unfold ConRon.Arena.failDanglingLs; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_failDanglingLs _)

/-- con-leche: none — `readLevelsM` keeps the scratch flag. -/
theorem sp_readLevelsM (b : Bool) : ∀ x0, SPb b (ConRon.Arena.readLevelsM x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.readLevelsM; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.readLevelsM; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_readLevelsM _ _)

/-- con-leche: none — `instLPClear` keeps the scratch flag. -/
theorem sp_instLPClear (b : Bool) : SPb b (ConRon.Arena.instLPClear) := by
  first
  | (unfold ConRon.Arena.instLPClear; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPClear _)

/-- con-leche: none — `instLPLGet` keeps the scratch flag. -/
theorem sp_instLPLGet (b : Bool) : ∀ x0, SPb b (ConRon.Arena.instLPLGet x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.instLPLGet; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.instLPLGet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPLGet _ _)

/-- con-leche: none — `internLevel` keeps the scratch flag. -/
theorem sp_internLevel (b : Bool) : ∀ x0, SPb b (ConRon.Arena.internLevel x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.internLevel; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.internLevel; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internLevel _ _)

/-- con-leche: none — `instLPLSet` keeps the scratch flag. -/
theorem sp_instLPLSet (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.instLPLSet x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.instLPLSet; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.instLPLSet; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.instLPLSet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPLSet _ _ _)

/-- con-leche: none — `substLMemoAt` keeps the scratch flag. -/
theorem sp_substLMemoAt (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.substLMemoAt x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.substLMemoAt; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.substLMemoAt; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.substLMemoAt; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.substLMemoAt; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_substLMemoAt _ _ _ _)

/-- con-leche: none — `internSortE` keeps the scratch flag. -/
theorem sp_internSortE (b : Bool) : ∀ x0, SPb b (ConRon.Arena.internSortE x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.internSortE; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.internSortE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internSortE _ _)

/-- con-leche: none — `internRebuiltSort` keeps the scratch flag. -/
theorem sp_internRebuiltSort (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.internRebuiltSort x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.internRebuiltSort; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.internRebuiltSort; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.internRebuiltSort; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.internRebuiltSort; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internRebuiltSort _ _ _ _)

/-- con-leche: none — `instLPLsGet` keeps the scratch flag. -/
theorem sp_instLPLsGet (b : Bool) : ∀ x0, SPb b (ConRon.Arena.instLPLsGet x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.instLPLsGet; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.instLPLsGet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPLsGet _ _)

/-- con-leche: none — `internLevelList` keeps the scratch flag. -/
theorem sp_internLevelList (b : Bool) : ∀ x0, SPb b (ConRon.Arena.internLevelList x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.internLevelList; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.internLevelList; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internLevelList _ _)

/-- con-leche: none — `internLevels` keeps the scratch flag. -/
theorem sp_internLevels (b : Bool) : ∀ x0, SPb b (ConRon.Arena.internLevels x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.internLevels; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.internLevels; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internLevels _ _)

/-- con-leche: none — `instLPLsSet` keeps the scratch flag. -/
theorem sp_instLPLsSet (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.instLPLsSet x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.instLPLsSet; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.instLPLsSet; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.instLPLsSet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPLsSet _ _ _)

/-- con-leche: none — `substLsMemoAt` keeps the scratch flag. -/
theorem sp_substLsMemoAt (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.substLsMemoAt x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.substLsMemoAt; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.substLsMemoAt; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.substLsMemoAt; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.substLsMemoAt; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_substLsMemoAt _ _ _ _)

/-- con-leche: none — `internConstE` keeps the scratch flag. -/
theorem sp_internConstE (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.internConstE x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.internConstE; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.internConstE; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.internConstE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internConstE _ _ _)

/-- con-leche: none — `internRebuiltConst` keeps the scratch flag. -/
theorem sp_internRebuiltConst (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.internRebuiltConst x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.internRebuiltConst; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.internRebuiltConst; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.internRebuiltConst; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.internRebuiltConst; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.internRebuiltConst; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internRebuiltConst _ _ _ _ _)

/-- con-leche: none — `instLPGet` keeps the scratch flag. -/
theorem sp_instLPGet (b : Bool) : ∀ x0, SPb b (ConRon.Arena.instLPGet x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.instLPGet; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.instLPGet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPGet _ _)

/-- con-leche: none — `internFVarE` keeps the scratch flag. -/
theorem sp_internFVarE (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.internFVarE x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.internFVarE; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.internFVarE; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.internFVarE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internFVarE _ _ _)

/-- con-leche: none — `internRebuiltFVar` keeps the scratch flag. -/
theorem sp_internRebuiltFVar (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.internRebuiltFVar x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.internRebuiltFVar; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.internRebuiltFVar; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.internRebuiltFVar; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.internRebuiltFVar; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.internRebuiltFVar; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internRebuiltFVar _ _ _ _ _)

/-- con-leche: none — `instLPSet` keeps the scratch flag. -/
theorem sp_instLPSet (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.instLPSet x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.instLPSet; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.instLPSet; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.instLPSet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPSet _ _ _)

/-- con-leche: none — `internAppE` keeps the scratch flag. -/
theorem sp_internAppE (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.internAppE x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.internAppE; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.internAppE; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.internAppE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internAppE _ _ _)

/-- con-leche: none — `internRebuiltApp` keeps the scratch flag. -/
theorem sp_internRebuiltApp (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.internRebuiltApp x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.internRebuiltApp; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.internRebuiltApp; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.internRebuiltApp; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.internRebuiltApp; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.internRebuiltApp; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internRebuiltApp _ _ _ _ _)

/-- con-leche: none — `internLamE` keeps the scratch flag. -/
theorem sp_internLamE (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.internLamE x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.internLamE; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.internLamE; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.internLamE; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.internLamE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internLamE _ _ _ _)

/-- con-leche: none — `internRebuiltLam` keeps the scratch flag. -/
theorem sp_internRebuiltLam (b : Bool) : ∀ x0 x1 x2 x3 x4, SPb b (ConRon.Arena.internRebuiltLam x0 x1 x2 x3 x4) := by
  intro x0 x1 x2 x3 x4
  first
  | (unfold ConRon.Arena.internRebuiltLam; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 <;> (unfold ConRon.Arena.internRebuiltLam; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 <;> (unfold ConRon.Arena.internRebuiltLam; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 <;> (unfold ConRon.Arena.internRebuiltLam; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 <;> (unfold ConRon.Arena.internRebuiltLam; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 <;> (unfold ConRon.Arena.internRebuiltLam; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internRebuiltLam _ _ _ _ _ _)

/-- con-leche: none — `internForallEE` keeps the scratch flag. -/
theorem sp_internForallEE (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.internForallEE x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.internForallEE; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.internForallEE; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.internForallEE; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.internForallEE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internForallEE _ _ _ _)

/-- con-leche: none — `internRebuiltForallE` keeps the scratch flag. -/
theorem sp_internRebuiltForallE (b : Bool) : ∀ x0 x1 x2 x3 x4, SPb b (ConRon.Arena.internRebuiltForallE x0 x1 x2 x3 x4) := by
  intro x0 x1 x2 x3 x4
  first
  | (unfold ConRon.Arena.internRebuiltForallE; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 <;> (unfold ConRon.Arena.internRebuiltForallE; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 <;> (unfold ConRon.Arena.internRebuiltForallE; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 <;> (unfold ConRon.Arena.internRebuiltForallE; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 <;> (unfold ConRon.Arena.internRebuiltForallE; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 <;> (unfold ConRon.Arena.internRebuiltForallE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internRebuiltForallE _ _ _ _ _ _)

/-- con-leche: none — `internLetEE` keeps the scratch flag. -/
theorem sp_internLetEE (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.internLetEE x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.internLetEE; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.internLetEE; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.internLetEE; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.internLetEE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internLetEE _ _ _ _)

/-- con-leche: none — `internRebuiltLetE` keeps the scratch flag. -/
theorem sp_internRebuiltLetE (b : Bool) : ∀ x0 x1 x2 x3 x4, SPb b (ConRon.Arena.internRebuiltLetE x0 x1 x2 x3 x4) := by
  intro x0 x1 x2 x3 x4
  first
  | (unfold ConRon.Arena.internRebuiltLetE; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 <;> (unfold ConRon.Arena.internRebuiltLetE; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 <;> (unfold ConRon.Arena.internRebuiltLetE; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 <;> (unfold ConRon.Arena.internRebuiltLetE; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 <;> (unfold ConRon.Arena.internRebuiltLetE; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 <;> (unfold ConRon.Arena.internRebuiltLetE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internRebuiltLetE _ _ _ _ _ _)

/-- con-leche: none — `internProjE` keeps the scratch flag. -/
theorem sp_internProjE (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.internProjE x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.internProjE; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.internProjE; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.internProjE; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.internProjE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internProjE _ _ _ _)

/-- con-leche: none — `internRebuiltProj` keeps the scratch flag. -/
theorem sp_internRebuiltProj (b : Bool) : ∀ x0 x1 x2 x3 x4, SPb b (ConRon.Arena.internRebuiltProj x0 x1 x2 x3 x4) := by
  intro x0 x1 x2 x3 x4
  first
  | (unfold ConRon.Arena.internRebuiltProj; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 <;> (unfold ConRon.Arena.internRebuiltProj; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 <;> (unfold ConRon.Arena.internRebuiltProj; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 <;> (unfold ConRon.Arena.internRebuiltProj; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 <;> (unfold ConRon.Arena.internRebuiltProj; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 <;> (unfold ConRon.Arena.internRebuiltProj; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_internRebuiltProj _ _ _ _ _ _)

/-- con-leche: none — `instLPGo` keeps the scratch flag. -/
theorem sp_instLPGo (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.instLPGo x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  induction x2 generalizing x3 with
  | zero => unfold ConRon.Arena.instLPGo; sp_auto
  | succ n ih => unfold ConRon.Arena.instLPGo; unfold ConRon.Arena.instLPArmFVar ConRon.Arena.instLPArmApp ConRon.Arena.instLPArmLam ConRon.Arena.instLPArmForallE ConRon.Arena.instLPArmLet ConRon.Arena.instLPArmProj; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPGo _ _ _ _ _)

/-- con-leche: none — `instLPArmFVar` keeps the scratch flag. -/
theorem sp_instLPArmFVar (b : Bool) : ∀ x0 x1 x2 x3 x4 x5, SPb b (ConRon.Arena.instLPArmFVar x0 x1 x2 x3 x4 x5) := by
  intro x0 x1 x2 x3 x4 x5
  first
  | (unfold ConRon.Arena.instLPArmFVar; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.instLPArmFVar; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 <;> (unfold ConRon.Arena.instLPArmFVar; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 <;> (unfold ConRon.Arena.instLPArmFVar; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 <;> (unfold ConRon.Arena.instLPArmFVar; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 <;> (unfold ConRon.Arena.instLPArmFVar; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 <;> (unfold ConRon.Arena.instLPArmFVar; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPArmFVar _ _ _ _ _ _ _)

/-- con-leche: none — `instLPArmApp` keeps the scratch flag. -/
theorem sp_instLPArmApp (b : Bool) : ∀ x0 x1 x2 x3 x4 x5, SPb b (ConRon.Arena.instLPArmApp x0 x1 x2 x3 x4 x5) := by
  intro x0 x1 x2 x3 x4 x5
  first
  | (unfold ConRon.Arena.instLPArmApp; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.instLPArmApp; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 <;> (unfold ConRon.Arena.instLPArmApp; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 <;> (unfold ConRon.Arena.instLPArmApp; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 <;> (unfold ConRon.Arena.instLPArmApp; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 <;> (unfold ConRon.Arena.instLPArmApp; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 <;> (unfold ConRon.Arena.instLPArmApp; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPArmApp _ _ _ _ _ _ _)

/-- con-leche: none — `instLPArmLam` keeps the scratch flag. -/
theorem sp_instLPArmLam (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.instLPArmLam x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.instLPArmLam; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmLam; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmLam; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmLam; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmLam; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.instLPArmLam; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.instLPArmLam; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.instLPArmLam; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPArmLam _ _ _ _ _ _ _ _)

/-- con-leche: none — `instLPArmForallE` keeps the scratch flag. -/
theorem sp_instLPArmForallE (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.instLPArmForallE x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.instLPArmForallE; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmForallE; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmForallE; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmForallE; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmForallE; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.instLPArmForallE; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.instLPArmForallE; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.instLPArmForallE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPArmForallE _ _ _ _ _ _ _ _)

/-- con-leche: none — `instLPArmLet` keeps the scratch flag. -/
theorem sp_instLPArmLet (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.instLPArmLet x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.instLPArmLet; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmLet; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmLet; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmLet; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmLet; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.instLPArmLet; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.instLPArmLet; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.instLPArmLet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPArmLet _ _ _ _ _ _ _ _)

/-- con-leche: none — `instLPArmProj` keeps the scratch flag. -/
theorem sp_instLPArmProj (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.instLPArmProj x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.instLPArmProj; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmProj; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmProj; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmProj; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.instLPArmProj; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.instLPArmProj; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.instLPArmProj; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.instLPArmProj; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPArmProj _ _ _ _ _ _ _ _)

/-- con-leche: none — `instLPFast` keeps the scratch flag. -/
theorem sp_instLPFast (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.instLPFast x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.instLPFast; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.instLPFast; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.instLPFast; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.instLPFast; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.instLPFast; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instLPFast _ _ _ _ _)

/-- con-leche: none — `bvarRange` keeps the scratch flag. -/
theorem sp_bvarRange (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.bvarRange x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.bvarRange; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.bvarRange; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.bvarRange; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.bvarRange; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarRange _ _ _ _)

/-- con-leche: none — `inst1LClear` keeps the scratch flag. -/
theorem sp_inst1LClear (b : Bool) : SPb b (ConRon.Arena.inst1LClear) := by
  first
  | (unfold ConRon.Arena.inst1LClear; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_inst1LClear _)

/-- con-leche: none — `bvarBClear` keeps the scratch flag. -/
theorem sp_bvarBClear (b : Bool) : SPb b (ConRon.Arena.bvarBClear) := by
  first
  | (unfold ConRon.Arena.bvarBClear; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarBClear _)

/-- con-leche: none — `bvarBGet` keeps the scratch flag. -/
theorem sp_bvarBGet (b : Bool) : ∀ x0, SPb b (ConRon.Arena.bvarBGet x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.bvarBGet; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.bvarBGet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarBGet _ _)

/-- con-leche: none — `bvarBSet` keeps the scratch flag. -/
theorem sp_bvarBSet (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.bvarBSet x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.bvarBSet; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.bvarBSet; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.bvarBSet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarBSet _ _ _)

/-- con-leche: none — `bvarBoundGo` keeps the scratch flag. -/
theorem sp_bvarBoundGo (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.bvarBoundGo x0 x1) := by
  intro x0 x1
  induction x0 generalizing x1 with
  | zero => unfold ConRon.Arena.bvarBoundGo; sp_auto
  | succ n ih => unfold ConRon.Arena.bvarBoundGo; unfold ConRon.Arena.bvarBoundArmApp ConRon.Arena.bvarBoundArmBind ConRon.Arena.bvarBoundArmLet; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarBoundGo _ _ _)

/-- con-leche: none — `bvarBoundArmApp` keeps the scratch flag. -/
theorem sp_bvarBoundArmApp (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.bvarBoundArmApp x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.bvarBoundArmApp; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.bvarBoundArmApp; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.bvarBoundArmApp; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.bvarBoundArmApp; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarBoundArmApp _ _ _ _)

/-- con-leche: none — `bvarBoundArmBind` keeps the scratch flag. -/
theorem sp_bvarBoundArmBind (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.bvarBoundArmBind x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.bvarBoundArmBind; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.bvarBoundArmBind; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.bvarBoundArmBind; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.bvarBoundArmBind; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarBoundArmBind _ _ _ _)

/-- con-leche: none — `bvarBoundArmLet` keeps the scratch flag. -/
theorem sp_bvarBoundArmLet (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.bvarBoundArmLet x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.bvarBoundArmLet; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.bvarBoundArmLet; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.bvarBoundArmLet; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.bvarBoundArmLet; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.bvarBoundArmLet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarBoundArmLet _ _ _ _ _)

/-- con-leche: none — `bvarBoundMemo` keeps the scratch flag. -/
theorem sp_bvarBoundMemo (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.bvarBoundMemo x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.bvarBoundMemo; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.bvarBoundMemo; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.bvarBoundMemo; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarBoundMemo _ _ _)

/-- con-leche: none — `bvarB` keeps the scratch flag. -/
theorem sp_bvarB (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.bvarB x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.bvarB; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.bvarB; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.bvarB; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_bvarB _ _ _)

/-- con-leche: none — `liftClear` keeps the scratch flag. -/
theorem sp_liftClear (b : Bool) : SPb b (ConRon.Arena.liftClear) := by
  first
  | (unfold ConRon.Arena.liftClear; sp_auto; done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_liftClear _)

/-- con-leche: none — `liftGet` keeps the scratch flag. -/
theorem sp_liftGet (b : Bool) : ∀ x0, SPb b (ConRon.Arena.liftGet x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.liftGet; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.liftGet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_liftGet _ _)

/-- con-leche: none — `liftSet` keeps the scratch flag. -/
theorem sp_liftSet (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.liftSet x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.liftSet; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.liftSet; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.liftSet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_liftSet _ _ _)

/-- con-leche: none — `liftLooseBVarsGo` keeps the scratch flag. -/
theorem sp_liftLooseBVarsGo (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.liftLooseBVarsGo x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  induction x1 generalizing x2 x3 with
  | zero => unfold ConRon.Arena.liftLooseBVarsGo; sp_auto
  | succ n ih => unfold ConRon.Arena.liftLooseBVarsGo; unfold ConRon.Arena.liftArmApp ConRon.Arena.liftArmLam ConRon.Arena.liftArmForallE ConRon.Arena.liftArmLet ConRon.Arena.liftArmProj; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_liftLooseBVarsGo _ _ _ _ _)

/-- con-leche: none — `liftArmApp` keeps the scratch flag. -/
theorem sp_liftArmApp (b : Bool) : ∀ x0 x1 x2 x3 x4 x5, SPb b (ConRon.Arena.liftArmApp x0 x1 x2 x3 x4 x5) := by
  intro x0 x1 x2 x3 x4 x5
  first
  | (unfold ConRon.Arena.liftArmApp; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.liftArmApp; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 <;> (unfold ConRon.Arena.liftArmApp; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 <;> (unfold ConRon.Arena.liftArmApp; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 <;> (unfold ConRon.Arena.liftArmApp; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 <;> (unfold ConRon.Arena.liftArmApp; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 <;> (unfold ConRon.Arena.liftArmApp; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_liftArmApp _ _ _ _ _ _ _)

/-- con-leche: none — `liftArmLam` keeps the scratch flag. -/
theorem sp_liftArmLam (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.liftArmLam x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.liftArmLam; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmLam; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmLam; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmLam; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmLam; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.liftArmLam; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.liftArmLam; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.liftArmLam; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_liftArmLam _ _ _ _ _ _ _ _)

/-- con-leche: none — `liftArmForallE` keeps the scratch flag. -/
theorem sp_liftArmForallE (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.liftArmForallE x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.liftArmForallE; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmForallE; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmForallE; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmForallE; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmForallE; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.liftArmForallE; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.liftArmForallE; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.liftArmForallE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_liftArmForallE _ _ _ _ _ _ _ _)

/-- con-leche: none — `liftArmLet` keeps the scratch flag. -/
theorem sp_liftArmLet (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.liftArmLet x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.liftArmLet; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmLet; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmLet; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmLet; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmLet; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.liftArmLet; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.liftArmLet; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.liftArmLet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_liftArmLet _ _ _ _ _ _ _ _)

/-- con-leche: none — `liftArmProj` keeps the scratch flag. -/
theorem sp_liftArmProj (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.liftArmProj x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.liftArmProj; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmProj; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmProj; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmProj; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.liftArmProj; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.liftArmProj; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.liftArmProj; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.liftArmProj; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_liftArmProj _ _ _ _ _ _ _ _)

/-- con-leche: none — `liftLooseBVarsFast` keeps the scratch flag. -/
theorem sp_liftLooseBVarsFast (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.liftLooseBVarsFast x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.liftLooseBVarsFast; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.liftLooseBVarsFast; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.liftLooseBVarsFast; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.liftLooseBVarsFast; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.liftLooseBVarsFast; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_liftLooseBVarsFast _ _ _ _ _)

/-- con-leche: none — `inst1LGet` keeps the scratch flag. -/
theorem sp_inst1LGet (b : Bool) : ∀ x0, SPb b (ConRon.Arena.inst1LGet x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.inst1LGet; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.inst1LGet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_inst1LGet _ _)

/-- con-leche: none — `inst1LSet` keeps the scratch flag. -/
theorem sp_inst1LSet (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.inst1LSet x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.inst1LSet; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.inst1LSet; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.inst1LSet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_inst1LSet _ _ _)

/-- con-leche: none — `instantiate1LiftGo` keeps the scratch flag. -/
theorem sp_instantiate1LiftGo (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.instantiate1LiftGo x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  induction x1 generalizing x2 x3 with
  | zero => unfold ConRon.Arena.instantiate1LiftGo; sp_auto
  | succ n ih => unfold ConRon.Arena.instantiate1LiftGo; unfold ConRon.Arena.inst1LiftArmApp ConRon.Arena.inst1LiftArmLam ConRon.Arena.inst1LiftArmForallE ConRon.Arena.inst1LiftArmLet ConRon.Arena.inst1LiftArmProj; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instantiate1LiftGo _ _ _ _ _)

/-- con-leche: none — `inst1LiftArmApp` keeps the scratch flag. -/
theorem sp_inst1LiftArmApp (b : Bool) : ∀ x0 x1 x2 x3 x4 x5, SPb b (ConRon.Arena.inst1LiftArmApp x0 x1 x2 x3 x4 x5) := by
  intro x0 x1 x2 x3 x4 x5
  first
  | (unfold ConRon.Arena.inst1LiftArmApp; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.inst1LiftArmApp; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 <;> (unfold ConRon.Arena.inst1LiftArmApp; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 <;> (unfold ConRon.Arena.inst1LiftArmApp; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 <;> (unfold ConRon.Arena.inst1LiftArmApp; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 <;> (unfold ConRon.Arena.inst1LiftArmApp; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 <;> (unfold ConRon.Arena.inst1LiftArmApp; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_inst1LiftArmApp _ _ _ _ _ _ _)

/-- con-leche: none — `inst1LiftArmLam` keeps the scratch flag. -/
theorem sp_inst1LiftArmLam (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.inst1LiftArmLam x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.inst1LiftArmLam; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmLam; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmLam; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmLam; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmLam; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmLam; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.inst1LiftArmLam; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.inst1LiftArmLam; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_inst1LiftArmLam _ _ _ _ _ _ _ _)

/-- con-leche: none — `inst1LiftArmForallE` keeps the scratch flag. -/
theorem sp_inst1LiftArmForallE (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.inst1LiftArmForallE x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.inst1LiftArmForallE; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmForallE; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmForallE; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmForallE; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmForallE; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmForallE; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.inst1LiftArmForallE; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.inst1LiftArmForallE; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_inst1LiftArmForallE _ _ _ _ _ _ _ _)

/-- con-leche: none — `inst1LiftArmLet` keeps the scratch flag. -/
theorem sp_inst1LiftArmLet (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.inst1LiftArmLet x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.inst1LiftArmLet; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmLet; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmLet; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmLet; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmLet; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmLet; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.inst1LiftArmLet; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.inst1LiftArmLet; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_inst1LiftArmLet _ _ _ _ _ _ _ _)

/-- con-leche: none — `inst1LiftArmProj` keeps the scratch flag. -/
theorem sp_inst1LiftArmProj (b : Bool) : ∀ x0 x1 x2 x3 x4 x5 x6, SPb b (ConRon.Arena.inst1LiftArmProj x0 x1 x2 x3 x4 x5 x6) := by
  intro x0 x1 x2 x3 x4 x5 x6
  first
  | (unfold ConRon.Arena.inst1LiftArmProj; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmProj; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmProj; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmProj; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmProj; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 x6 <;> (unfold ConRon.Arena.inst1LiftArmProj; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 x6 <;> (unfold ConRon.Arena.inst1LiftArmProj; sp_auto) <;> done)
  | (induction x6 generalizing x0 x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.inst1LiftArmProj; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_inst1LiftArmProj _ _ _ _ _ _ _ _)

/-- con-leche: none — `instantiate1LiftFast` keeps the scratch flag. -/
theorem sp_instantiate1LiftFast (b : Bool) : ∀ x0 x1 x2 x3, SPb b (ConRon.Arena.instantiate1LiftFast x0 x1 x2 x3) := by
  intro x0 x1 x2 x3
  first
  | (unfold ConRon.Arena.instantiate1LiftFast; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 <;> (unfold ConRon.Arena.instantiate1LiftFast; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 <;> (unfold ConRon.Arena.instantiate1LiftFast; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 <;> (unfold ConRon.Arena.instantiate1LiftFast; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 <;> (unfold ConRon.Arena.instantiate1LiftFast; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instantiate1LiftFast _ _ _ _ _)

/-- con-leche: none — `Frontend.instPisOpen` keeps the scratch flag. -/
theorem sp_instPisOpen (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.Frontend.instPisOpen x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.Frontend.instPisOpen; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.Frontend.instPisOpen; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.Frontend.instPisOpen; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.Frontend.instPisOpen; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_instPisOpen _ _ _ _)

/-- con-leche: none — `viewApp` keeps the scratch flag. -/
theorem sp_viewApp (b : Bool) : ∀ x0, SPb b (ConRon.Arena.viewApp x0) := by
  intro x0
  first
  | (unfold ConRon.Arena.viewApp; sp_auto; done)
  | (induction x0 <;> (unfold ConRon.Arena.viewApp; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_viewApp _ _)

/-- con-leche: none — `failDanglingE` keeps the scratch flag. -/
theorem sp_failDanglingE (b : Bool) {α : Type} : SPb b (ConRon.Arena.failDanglingE : AM α) := by
  unfold ConRon.Arena.failDanglingE; sp_auto
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_failDanglingE _)

/-- con-leche: none — `getAppFn` keeps the scratch flag. -/
theorem sp_getAppFn (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.getAppFn x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.getAppFn; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.getAppFn; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.getAppFn; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_getAppFn _ _ _)

/-- con-leche: none — `Frontend.headIs` keeps the scratch flag. -/
theorem sp_headIs (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.Frontend.headIs x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.Frontend.headIs; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.Frontend.headIs; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.Frontend.headIs; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.Frontend.headIs; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_headIs _ _ _ _)

/-- con-leche: none — `Frontend.mkLams` keeps the scratch flag. -/
theorem sp_mkLams (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.Frontend.mkLams x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.Frontend.mkLams; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.Frontend.mkLams; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.Frontend.mkLams; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_mkLams _ _ _)

/-- con-leche: none — `Frontend.mkProjMotive` keeps the scratch flag. -/
theorem sp_mkProjMotive (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.Frontend.mkProjMotive x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.Frontend.mkProjMotive; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.Frontend.mkProjMotive; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.Frontend.mkProjMotive; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.Frontend.mkProjMotive; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_mkProjMotive _ _ _ _)

/-- con-leche: none — `getAppArgs` keeps the scratch flag. -/
theorem sp_getAppArgs (b : Bool) : ∀ x0 x1, SPb b (ConRon.Arena.getAppArgs x0 x1) := by
  intro x0 x1
  first
  | (unfold ConRon.Arena.getAppArgs; sp_auto; done)
  | (induction x0 generalizing x1 <;> (unfold ConRon.Arena.getAppArgs; sp_auto) <;> done)
  | (induction x1 generalizing x0 <;> (unfold ConRon.Arena.getAppArgs; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_getAppArgs _ _ _)

/-- con-leche: none — `Frontend.mkProjMinor` keeps the scratch flag. -/
theorem sp_mkProjMinor (b : Bool) : ∀ x0 x1 x2, SPb b (ConRon.Arena.Frontend.mkProjMinor x0 x1 x2) := by
  intro x0 x1 x2
  first
  | (unfold ConRon.Arena.Frontend.mkProjMinor; sp_auto; done)
  | (induction x0 generalizing x1 x2 <;> (unfold ConRon.Arena.Frontend.mkProjMinor; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 <;> (unfold ConRon.Arena.Frontend.mkProjMinor; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 <;> (unfold ConRon.Arena.Frontend.mkProjMinor; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_mkProjMinor _ _ _ _)

/-- con-leche: none — `Frontend.buildBinders` keeps the scratch flag. -/
theorem sp_buildBinders (b : Bool) : ∀ x0 x1 x2 x3 x4, SPb b (ConRon.Arena.Frontend.buildBinders x0 x1 x2 x3 x4) := by
  intro x0 x1 x2 x3 x4
  first
  | (unfold ConRon.Arena.Frontend.buildBinders; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 <;> (unfold ConRon.Arena.Frontend.buildBinders; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 <;> (unfold ConRon.Arena.Frontend.buildBinders; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 <;> (unfold ConRon.Arena.Frontend.buildBinders; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 <;> (unfold ConRon.Arena.Frontend.buildBinders; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 <;> (unfold ConRon.Arena.Frontend.buildBinders; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_buildBinders _ _ _ _ _ _)

/-- con-leche: none — `Frontend.projRecValue` keeps the scratch flag. -/
theorem sp_projRecValue (b : Bool) : ∀ x0 x1 x2 x3 x4 x5, SPb b (ConRon.Arena.Frontend.projRecValue x0 x1 x2 x3 x4 x5) := by
  intro x0 x1 x2 x3 x4 x5
  first
  | (unfold ConRon.Arena.Frontend.projRecValue; sp_auto; done)
  | (induction x0 generalizing x1 x2 x3 x4 x5 <;> (unfold ConRon.Arena.Frontend.projRecValue; sp_auto) <;> done)
  | (induction x1 generalizing x0 x2 x3 x4 x5 <;> (unfold ConRon.Arena.Frontend.projRecValue; sp_auto) <;> done)
  | (induction x2 generalizing x0 x1 x3 x4 x5 <;> (unfold ConRon.Arena.Frontend.projRecValue; sp_auto) <;> done)
  | (induction x3 generalizing x0 x1 x2 x4 x5 <;> (unfold ConRon.Arena.Frontend.projRecValue; sp_auto) <;> done)
  | (induction x4 generalizing x0 x1 x2 x3 x5 <;> (unfold ConRon.Arena.Frontend.projRecValue; sp_auto) <;> done)
  | (induction x5 generalizing x0 x1 x2 x3 x4 <;> (unfold ConRon.Arena.Frontend.projRecValue; sp_auto) <;> done)
macro_rules | `(tactic| sp_lemma) => `(tactic| exact sp_projRecValue _ _ _ _ _ _ _)


/-- con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue — **the
rewrite leaves the scratch flag where it found it.** -/
theorem projRecValue_scratch {fuel : Nat} {o : ProjRecOwner} {l : LIdx}
    {ty val : EIdx} {i : Nat} {s s' : AState} {r : Option EIdx}
    (hrun : projRecValue fuel o l ty val i s = .ok (r, s')) :
    s'.store.scratchOn = s.store.scratchOn :=
  sp_projRecValue s.store.scratchOn fuel o l ty val i s s' r rfl hrun

/-- con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners — **the
owner census leaves the scratch flag where it found it**, through both
recognisers. -/
theorem projRecOwners_scratch {fuel : Nat} {block : List IConstantInfo}
    {types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)}
    {ctors : List (NIdx × Nat × EIdx)}
    {recs : List (NIdx × List NIdx × EIdx × Nat × Nat)} {s s' : AState}
    {os : List ProjRecOwner}
    (hrun : projRecOwners fuel block types ctors recs s = .ok (os, s')) :
    s'.store.scratchOn = s.store.scratchOn :=
  sp_projRecOwners s.store.scratchOn fuel block types ctors recs s s' os rfl hrun

#print axioms projRecValue_scratch
#print axioms projRecOwners_scratch

end ConRon.Bridge.Frontend
