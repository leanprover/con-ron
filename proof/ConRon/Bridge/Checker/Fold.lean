/-
# `ConRon.Bridge.Checker.Fold` — THEOREM 1, per declaration

DESIGN.md §8.2's per-declaration statement.

    theorem Arena.checkDecl_bridge (hμ : μ.verifiedChecks = true)
        (hok : StateOK st) (h : Arena.checkDecl μ pins pd st = .ok ((), st')) :
        StateOK st' ∧ Ext st st' ∧
        ∃ F, ConLeche.checkDecl μ (fueledOps μ F) pins (denoteEnv st) (denoteDecl st pd)
               = .ok (denoteEnv st')

**`denoteEnv` is a function of the STORE and the INDEX, and it is partial.**
`denoteEnv st` in §8.2 reads as if the environment were a projection of the
state; it is not — the environment is `Arena/Env.lean`'s `IFEnv`, threaded as
a value, and its readback can fail (a handle may not decode).  So the
conclusion is `∃ env', denoteFEnv s'.store fe' = some env' ∧ … = .ok env'`,
which is con-leche's own join-point shape
(`Verify/Cached/BridgeC.lean:609`'s `fe' = mkFEnv fe'.env ∧ ∃ F, … = .ok
fe'.env`) with the readback where con-leche has the identity.

`Arena.checkDecl_bridge` is `cases pd` over `Bridge/Checker/Decl.lean`'s
seven arm theorems.  Its consumer is `Bridge/Checker/Split.lean`'s
install/check seam, whose fold (`Arena.installThenCheck_bridge`, and
`Bridge/Checker/Phased.lean` above it) is the one the binary runs.

**The sequential fold is gone** (task #97-T2-CLEANUP).  This module used to
carry the bracketed step `Arena.checkDeclStep_bridge` (a `sorry`, waiting on
`IFEnvOK` at the new environment), the list induction
`Arena.checkDeclsPureGo_bridge`/`Arena.checkDeclsPure_bridge` over it, and
`Bridge/Checker/Capstone.lean` the letters `Arena.model_exists` /
`no_proof_of_False` / `no_proof_of_Empty` at that fold.  None of them was
reached by `ConRon.Capstone`, which goes through the phased/pooled fold, so
the chain was deleted rather than proved.
-/
import ConRon.Bridge.Checker.Mono
import ConRon.Bridge.Checker.Arms

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## Running an `AM` do-block

Three `rfl` equations; the bind's inversion (`AM.bind_ok`) moved down to
`Bridge/Promote/Pers.lean` in task #97-P3-Checker-2, because
`Bridge/Checker/Base.lean` needs it too and sits below this module.  After
them no proof in this module mentions `StateT`. -/

/-- con-leche: none — `flushCaches` as an equation. -/
theorem flushCaches_run (s : AState) :
    flushCaches s = .ok ((), { s with caches := Caches.empty }) := rfl

/-- con-leche: none — `enterScratch` as an equation. -/
theorem enterScratch_run (s : AState) :
    enterScratch s = .ok ((),
      { store := s.store.enableScratch, memos := Memos.empty,
        caches := s.caches, pins := s.pins }) := rfl

/-- con-leche: none — `dropScratch` as an equation. -/
theorem dropScratch_run (s : AState) :
    dropScratch s = .ok ((),
      { store := s.store.dropScratch, memos := s.memos,
        caches := Caches.empty, pins := s.pins }) := rfl

/-! ## The pin list survives a drop -/

/-- con-leche: none — the interned pin variants keep denoting across a
`dropScratch`, because `internAllPins` ran before the parse with the scratch
tier closed and every pin handle is therefore persistent. -/
theorem PinsDenote.pmono {st st' : EStore} (hx : PExt st st') :
    ∀ ps qs, PersPinSets ps → PinsDenote st ps qs → PinsDenote st' ps qs := by
  intro ps
  induction ps with
  | nil => intro qs _ h; cases qs <;> exact h
  | cons a as ih =>
    intro qs hp h
    cases qs with
    | nil => exact h
    | cons b bs =>
      obtain ⟨h1, h2⟩ := h
      have hpa : PersPinSet a := hp a (by simp)
      have hpp := hpa.pins
      have hpr := hpa.proofs
      simp only [PersEList, List.mem_cons] at hpp
      refine ⟨?_, ih bs (fun c hc => hp c (by simp [hc])) h2⟩
      refine {
        toolchain := h1.toolchain
        divPin := denoteE_pext hx (hpp _ (by simp)) h1.divPin
        modPin := denoteE_pext hx (hpp _ (by simp)) h1.modPin
        gcdPin := denoteE_pext hx (hpp _ (by simp)) h1.gcdPin
        landPin := denoteE_pext hx (hpp _ (by simp)) h1.landPin
        lorPin := denoteE_pext hx (hpp _ (by simp)) h1.lorPin
        xorPin := denoteE_pext hx (hpp _ (by simp)) h1.xorPin
        shiftLeftPin := denoteE_pext hx (hpp _ (by simp)) h1.shiftLeftPin
        shiftRightPin := denoteE_pext hx (hpp _ (by simp)) h1.shiftRightPin
        divProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.divProofs
        modProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.modProofs
        gcdProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.gcdProofs
        landProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.landProofs
        lorProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.lorProofs
        xorProofs := denoteEList_pext hx _ _ (fun c hc => hpr c (by simp [hc])) h1.xorProofs
        shiftLeftProofs := denoteEList_pext hx _ _
          (fun c hc => hpr c (by simp [hc])) h1.shiftLeftProofs
        shiftRightProofs := denoteEList_pext hx _ _
          (fun c hc => hpr c (by simp [hc])) h1.shiftRightProofs }

/-! ## THE PER-DECLARATION BRIDGE -/

/-- con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run
**DESIGN §8.2's Theorem 1, per declaration.**  One `cases` over
`Bridge/Checker/Decl.lean`'s seven arms; the arms are where the content is
and where the tier's remaining `sorry`s live.

`Ext` and not `PExt`: `checkDecl` is the UNBRACKETED call (the module note of
`Arena/Checker.lean`: "What is NOT bracketed is `checkDecl` itself"), so the
total extension holds here and weakens one level up. -/
theorem Arena.checkDecl_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {pd : IDeclaration} {d : Declaration}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.checkDecl μ pins fe pd s = .ok (fe', s')) :
    DeclOut μ pinsP env d s fe fe' s' := by
  cases pd with
  | axiomDecl v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    exact checkDecl_bridge_axiom hμ hk hok hpins hcv hrun
  | quotDecl k v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    exact checkDecl_bridge_quot hμ hk hok hpins hcv hrun
  | basisDecl kind =>
    simp only [Frontend.denoteDecl, Option.some.injEq] at hd
    subst hd
    exact checkDecl_bridge_basis hμ hk hok hpins hrun
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, rfl⟩ := hd
    exact checkDecl_bridge_ind hμ hk hind hok hpins hb hrun
  | defnDecl v e hint =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        exact checkDecl_bridge_defn hμ hk hok hpins hcv he hrun
  | thmDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        exact checkDecl_bridge_thm hμ hk hok hpins hcv he hrun
  | opaqueDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        exact checkDecl_bridge_opaque hμ hk hok hpins hcv he hrun

end ConRon.Bridge
