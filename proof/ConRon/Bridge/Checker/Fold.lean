/-
# `ConRon.Bridge.Checker.Fold` — THEOREM 1, per declaration and folded

DESIGN.md §8.2, and this module is its three statements.

    theorem Arena.checkDecl_bridge (hμ : μ.verifiedChecks = true)
        (hok : StateOK st) (h : Arena.checkDecl μ pins pd st = .ok ((), st')) :
        StateOK st' ∧ Ext st st' ∧
        ∃ F, ConLeche.checkDecl μ (fueledOps μ F) pins (denoteEnv st) (denoteDecl st pd)
               = .ok (denoteEnv st')

The letter is §8.2's; three things about it are sharper here, and each is a
finding of this tier rather than a restatement.

**1. `denoteEnv` is a function of the STORE and the INDEX, and it is partial.**
`denoteEnv st` in §8.2 reads as if the environment were a projection of the
state; it is not — the environment is `Arena/Env.lean`'s `IFEnv`, threaded as
a value, and its readback can fail (a handle may not decode).  So the
conclusion is `∃ env', denoteFEnv s'.store fe' = some env' ∧ … = .ok env'`,
which is con-leche's own join-point shape
(`Verify/Cached/BridgeC.lean:609`'s `fe' = mkFEnv fe'.env ∧ ∃ F, … = .ok
fe'.env`) with the readback where con-leche has the identity.

**2. At the STEP the `Ext` conjunct is `PExt`.**  `checkDecl` appends and
never drops, so it does deliver the total `Ext`; `checkDeclStep` ends in
`dropScratch` and cannot.  `Bridge/Promote/Pers.lean` has the argument.

**3. The fold's fuel is one `max` per step.**  §8.2's per-declaration `∃ F`
and `checkDeclsPure_sound_of`'s single `F` are reconciled by
`Bridge/Checker/Mono.lean`'s `checkDecl_mono`, which is con-leche's own
`FueledM` monotonicity read through `checkDecl_datF`.  This is the history
report's fine print 2, discharged.

## What is proved here and what is assumed

Everything in this module is CLOSED except what it delegates:

* `Arena.checkDecl_bridge` is `cases pd` over `Bridge/Checker/Decl.lean`'s
  seven arm theorems — the arms carry the tier's remaining `sorry`s;
* `Arena.checkDeclStep_bridge` is the per-declaration bracket —
  `flushCaches` / `enterScratch` / `promoteNew` / `dropScratch` composed over
  `Bridge/Promote/Exact.lean`'s `promoteNew_spec` and
  `Bridge/Promote/Pers.lean`'s `PExt.{enterScratch,dropScratch}` — and it is
  the ONE `sorry` of this module, waiting on the store-layer gap the first of
  those two names;
* `Arena.checkDeclsPure_bridge` is the list induction, and it is proved.

So the shape of the whole tier is: one induction (here), one bracket (here),
seven arms (`Decl.lean`), and two named hypotheses (`Hyp.lean`).
-/
import ConRon.Bridge.Checker.Mono

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

/-! ## The bracketed step -/

/-- con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure
con-leche: ConLeche/Cached/ParsedC.lean:279-282 checkDeclStepC
**the fold's step, bracketed** — `flushCaches`, `enterScratch`, `checkDecl`,
`promoteNew`, `dropScratch` — and the invariant that comes out the other side.

This is where DESIGN §8.2's `Ext` becomes `PExt` and where the promotion
earns its keep: after `promoteNew` the environment names persistent handles
only, so `PExt.dropScratch` carries its denotation across the drop and the
next step starts from a `FoldOK` again.

`sorry`, and **the reason is a one-lemma gap in the store layer** (task
#97-P3-Checker, finding 4): the five stages are each spec'd
(`flushCaches_run`, `enterScratch_run`, `Arena.checkDecl_bridge`,
`promoteNew_spec`, `dropScratch_run` / `PExt.dropScratch`) and `AM.bind_ok`
inverts the binds, but re-establishing `FoldOK` *after the `enterScratch`* —
which is where the composition starts — needs the persistent denotation to
survive the flag flip, and `Arena/WFProofs.lean` states that for
`dropScratch` and not for `enableScratch`.  `Bridge/Promote/Pers.lean`'s
`PExt.enterScratch` is that gap, named as a lemma; with it this proof is the
mechanical composition it looks like.  Task #97-P3-Checker's sorry list,
item 8. -/
theorem Arena.checkDeclStep_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {pd : IDeclaration} {d : Declaration}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hpp : PersPinSets pins) (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.checkDeclStep μ pins fe pd s = .ok (fe', s')) :
    ∃ env' F', FoldOK μ env' fe' s' ∧ PExt s.store s'.store ∧
      ConLeche.checkDecl μ (ConLeche.fueledOps μ F') pinsP env d = .ok env' := by
  sorry

/-! ## THE FOLD

`checkDeclsPureGo` is `Arena/Checker.lean`'s explicit list recursion (DESIGN
§3.4 forbids the closure `foldlM` takes); con-leche's `checkDeclsPure` IS a
`foldlM`, so the induction relates a recursion to a fold and the fuel is
raised to the maximum as it goes. -/

/-- con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure — **the
fold of Theorem 1**, at an arbitrary starting environment.

The `max` is `Bridge/Checker/Mono.lean`'s `checkDecl_mono` at work: the step
gives a fuel `F₁` and the tail gives `F₂`, and both runs are reproduced at
`max F₁ F₂`, which is con-leche's own idiom
(`Verify/Cached/InstalledC.lean:416`'s `⟨max F₁ F, …⟩`). -/
theorem Arena.checkDeclsPureGo_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hpp : PersPinSets pins) :
    ∀ (ds : List IDeclaration) (dsP : List Declaration) (env : Env)
      (fe fe' : IFEnv) (s s' : AState),
      FoldOK μ env fe s → PinsDenote s.store pins pinsP →
      (∀ x ∈ ds, PersDecl x) → denoteDecls s.store ds = some dsP →
      Arena.checkDeclsPureGo μ pins fe ds s = .ok (fe', s') →
      ∃ env' F', FoldOK μ env' fe' s' ∧ PExt s.store s'.store ∧
        List.foldlM (ConLeche.checkDecl μ (ConLeche.fueledOps μ F') pinsP) env dsP
          = .ok env' := by
  intro ds
  induction ds with
  | nil =>
    intro dsP env fe fe' s s' hok hpins _ hden hrun
    simp only [denoteDecls, Option.some.injEq] at hden
    subst hden
    simp only [Arena.checkDeclsPureGo, pure, StateT.pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨env, 0, hok, PExt.refl _, rfl⟩
  | cons a as ih =>
    intro dsP env fe fe' s s' hok hpins hpd hden hrun
    -- the stream's head and tail denote
    simp only [denoteDecls] at hden
    cases ha : Frontend.denoteDecl s.store a with
    | none => rw [ha] at hden; simp at hden
    | some x =>
      cases has : denoteDecls s.store as with
      | none => rw [ha, has] at hden; simp at hden
      | some xs =>
        rw [ha, has] at hden
        simp only [Option.some.injEq] at hden
        subst hden
        -- the step
        simp only [Arena.checkDeclsPureGo] at hrun
        obtain ⟨fe₁, s₁, hstep, htail⟩ := AM.bind_ok hrun
        obtain ⟨env₁, F₁, hok₁, hx₁, hrun₁⟩ :=
          Arena.checkDeclStep_bridge hμ hk hind hok hpins hpp ha hstep
        -- the tail, at the state the step left
        obtain ⟨env₂, F₂, hok₂, hx₂, hrun₂⟩ :=
          ih xs env₁ fe₁ fe' s₁ s' hok₁ (PinsDenote.pmono hx₁ _ _ hpp hpins)
            (fun c hc => hpd c (by simp [hc]))
            (denoteDecls_pext hx₁ as xs (fun c hc => hpd c (by simp [hc])) has)
            htail
        -- one fuel for both
        refine ⟨env₂, max F₁ F₂, hok₂, hx₁.trans hx₂, ?_⟩
        simp only [List.foldlM, Bind.bind, Except.bind]
        rw [checkDecl_mono (Nat.le_max_left F₁ F₂) hrun₁]
        exact foldlM_mono (Nat.le_max_right F₁ F₂) xs env₁ env₂ hrun₂
where
  /-- the tail's fuel, raised. -/
  foldlM_mono {μ : CheckMode} {pinsP : List NatOpPinSet} {F₁ F₂ : Nat}
      (hle : F₂ ≤ F₁) :
      ∀ (xs : List Declaration) (env env' : Env),
        List.foldlM (ConLeche.checkDecl μ (ConLeche.fueledOps μ F₂) pinsP) env xs
          = .ok env' →
        List.foldlM (ConLeche.checkDecl μ (ConLeche.fueledOps μ F₁) pinsP) env xs
          = .ok env' := by
    intro xs
    induction xs with
    | nil => intro env env' h; exact h
    | cons b bs ihb =>
      intro env env' h
      simp only [List.foldlM, Bind.bind, Except.bind] at h ⊢
      cases hb : ConLeche.checkDecl μ (ConLeche.fueledOps μ F₂) pinsP env b with
      | error e => rw [hb] at h; exact nomatch h
      | ok env₁ =>
        rw [hb] at h
        rw [checkDecl_mono hle hb]
        exact ihb env₁ env' h

/-- con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure — **THE
FOLD OF THEOREM 1**, at the empty environment: DESIGN §8.2's

    ∃ F, checkDeclsPure μ (fueledOps μ F) pins (denoteDecls ds) = .ok (denoteEnv st')

which `Model/Fold.lean:254 checkDeclsPure_sound_of` consumes with zero
model-tier work. -/
theorem Arena.checkDeclsPure_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : List IDeclaration} {dsP : List Declaration} {fe' : IFEnv}
    {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hpp : PersPinSets pins)
    (hok : FoldOK μ Env.empty (mkIFEnv IEnv.empty) s)
    (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds, PersDecl x) (hden : denoteDecls s.store ds = some dsP)
    (hrun : Arena.checkDeclsPure μ pins ds s = .ok (fe', s')) :
    ∃ env' F', FoldOK μ env' fe' s' ∧ PExt s.store s'.store ∧
      ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F') pinsP dsP = .ok env' := by
  obtain ⟨env', F', h1, h2, h3⟩ :=
    Arena.checkDeclsPureGo_bridge hμ hk hind hpp ds dsP Env.empty
      (mkIFEnv IEnv.empty) fe' s s' hok hpins hpd hden hrun
  exact ⟨env', F', h1, h2, h3⟩

end ConRon.Bridge
