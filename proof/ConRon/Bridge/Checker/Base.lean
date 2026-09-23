/-
# `ConRon.Bridge.Checker.Base` — `CheckerBase`'s specs

The twin of `ConLeche/Kernel/CheckerBase.lean` is `Arena/CheckerBase.lean`,
and this module is its bridge tier: the variant fallback, the two memoised
DAG walks the declaration front door runs, the per-declaration constant check
and the three list checks.

## `orElseAttempt` — the only recovery, and the only thing here that is CLOSED

`Arena/CheckerBase.lean`'s `orElseAttempt` is the one place (B) recovers from
a thrown error, and the module note there records the one seam where (B) and
(C) are not the same state:

> The port keeps its `&mut AState` across a failing attempt, so it restores
> the memos and the caches and KEEPS the store […].  A throw in `StateT σ
> (Except ε)` carries no state at all, so the twin's error arm can only resume
> at `s`, whose store is the pre-attempt one.

`orElseAttempt_run` below is that, as a theorem: the attempt's outcome
determines the step, and on a recovered error the state is *literally* the
pre-attempt one — `attemptRestore s (attemptSnapshot s) = s` is `rfl`, which
is what makes the snapshot/restore pair invisible to the bridge.  con-leche's
`orElse` combinator (`CheckerBase.lean:25-53`'s sixth field, its
`fueledOps` clause) has the same three-way outcome with the same states, so
the two agree on the verdict and on everything the bridge can observe.

**Where con-leche has no counterpart**: `OrElseStep.failed`, the fourth arm,
carries only a `native` error (DESIGN §8.3's ruling), and a `native` claims
nothing.  So the bridge says nothing about that arm and does not need to.

## The rest, and why it is stated rather than proved

Everything else here bottoms out in `KnotSpec` (the annotation and the
inference calls) and in the `ExprOps` tier's walks, and the guards that do
NOT are the memoised ones — `allLevelParamsDefined` and `constsResolveFFast`
— which `Arena/CheckerBase.lean` carries because con-leche's own tree walks do
not terminate on a shared DAG (con-leche's task #210 Part B).  Each is a
memoised walk with an explicitly threaded table, so each needs its own memo
invariant and its own fuel induction, in `Bridge/ExprOps/Walks.lean`'s shape.
That is a tier of its own and this round states it.
-/
import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.ExprOps.Ranges
import ConLeche.Verify.BridgeDecl

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The variant fallback -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps (the `orElse`
field) — **the attempt's snapshot and restore, closed.**  Three outcomes, and
on the recovered one the state handed back is the pre-attempt state itself.

The `rfl` in the last arm is the whole content of the snapshot/restore pair:
`attemptRestore s (attemptSnapshot s)` is `{ s with memos := s.memos,
caches := s.caches }`, which is `s`.  In (C) it is not — the port keeps the
attempt's appended nodes — and `Arena/CheckerBase.lean`'s module note prices
that deviation (`Ext` rather than store equality, eight attempts on the whole
of `Init`). -/
theorem orElseAttempt_run {att : AM Bool} {s s' : AState} {r : OrElseStep}
    (h : orElseAttempt att s = .ok (r, s')) :
    (∃ b, att s = .ok (b, s') ∧ r = orElseStepOf (.ok b)) ∨
      (∃ e, att s = .error e ∧ r = orElseStepOf (.error e) ∧ s' = s) := by
  simp only [orElseAttempt] at h
  revert h
  cases ha : att s with
  | ok p =>
    obtain ⟨b, s₁⟩ := p
    intro h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨b, rfl, rfl⟩
  | error e =>
    intro h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨e, rfl, rfl, rfl⟩

/-- con-leche: none — a `matched` attempt matched, and a `continued` attempt
did not: the step's tag reads back the attempt's `Bool`.  The gate's loop
(`Arena/DeclCheck.lean`'s `checkDivModPinLoop`) dispatches on the tag, so this
is what lets the bridge read the loop. -/
theorem orElseStepOf_ok_iff {b : Bool} :
    orElseStepOf (.ok b) = .matched ↔ b = true := by
  cases b <;> simp [orElseStepOf]

/-! ## The memoised DAG walks of the front door

`allLevelParamsDefined_run` and `constsResolveFFast_run`, with their cone,
moved to `Bridge/Checker/Names.lean` (task #97-P3-Checker round 9): the
inductive tier reads them and cannot import this module. -/

/-! ## The name-shape guards

Pure tests on handles.  Each is a handle comparison where con-leche has a
`Name` comparison, and each is exact for the same reason: `denoteN` is
injective (`Arena/WFProofs.lean`'s `denoteN_inj`, DESIGN §8.3's soundness
obligation).  The LIST membership test of the family,
`denoteNList_contains`, moved to `Bridge/Checker/Names.lean` with the
reserved-name chain that is its only caller here (task #97-P3-Layout).

**The `AM` readers, as equations.**  `viewN` is a `get` and a `match`, so its
run form is `rfl`; after `viewN_apply` no proof below mentions `StateT`. -/

/-- con-leche: none — `viewN`'s inversion, off `Bridge/Specs.lean`'s triple:
an accepting read leaves the state alone and names the view. -/
theorem viewN_run {h : NIdx} {s s' : AState} {v : NNodeView}
    (hr : viewN h s = .ok (v, s')) : s' = s ∧ s.store.ns.view h = some v :=
  AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ s.store.ns.view h = some r) rfl hr (viewN_spec s h)

/-- con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup — the handle test
is the name test, by `denoteNList_contains` at every tail. -/
theorem nameNodup_spec {st : EStore} (hwf : StoreWF st) :
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
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [nameNodup, ConLeche.Name.nodup,
          denoteNList_contains hwf as ys has a y ha, ih ys has]

/-- con-leche: ConLeche/Kernel/Level.lean:223-230 Name.isProjFnShape — the
handle test is the name test: two `viewN` reads, two `denoteN` inversions, and
the four shapes con-leche's `match` distinguishes. -/
theorem isProjFnShape_run {st : EStore} {n : NIdx} {x : ConLeche.Name}
    {r : Bool} {s s' : AState} (hok : StateOK s) (hs : s.store = st)
    (hd : denoteN st.ns n = some x)
    (hrun : NIdx.isProjFnShape n s = .ok (r, s')) :
    s' = s ∧ r = x.isProjFnShape := by
  subst hs
  obtain ⟨rk, hrk⟩ := hok.wf
  have hns : NStoreWF s.store.ns := hrk.nsWF
  obtain ⟨rkn, hn⟩ := hns
  simp only [NIdx.isProjFnShape] at hrun
  obtain ⟨v, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hv⟩ := viewN_run h1
  rw [denoteN_unfold hn hv] at hd
  cases v with
  | anonymous =>
    simp only [denoteNView, Option.some.injEq] at hd
    subst hd
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨rfl, rfl⟩
  | str p t =>
    simp only [denoteNView, Option.map_eq_some_iff] at hd
    obtain ⟨q, _, rfl⟩ := hd
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨rfl, rfl⟩
  | num p k =>
    simp only [denoteNView, Option.map_eq_some_iff] at hd
    obtain ⟨q, hq, rfl⟩ := hd
    obtain ⟨w, s₂, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, hw⟩ := viewN_run h3
    rw [denoteN_unfold hn hw] at hq
    cases w with
    | anonymous =>
      simp only [denoteNView, Option.some.injEq] at hq
      subst hq
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
      exact ⟨rfl, rfl⟩
    | str p' t' =>
      simp only [denoteNView, Option.map_eq_some_iff] at hq
      obtain ⟨q', _, rfl⟩ := hq
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.Name.isProjFnShape]
      by_cases h1' : t' = "proj"
      · subst h1'; simp
      · by_cases h2' : t' = "projTable"
        · subst h2'; simp
        · simp [h1', h2']
    | num p' k' =>
      simp only [denoteNView, Option.map_eq_some_iff] at hq
      obtain ⟨q', _, rfl⟩ := hq
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
      exact ⟨rfl, rfl⟩

/-! ## The per-declaration constant check -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal —
**THE declaration front door**, and what every arm of
`Bridge/Checker/Decl.lean` bottoms out in: the six guards, the annotation, the
inference and the sort test.

The conclusion is a refinement, as everywhere in this tier: an accepting arena
run gives an accepting pure run whose answer the arena's answer denotes.  The
guards are what make it non-trivial — each must be *exact*, not merely sound,
because the arena's acceptance has to imply con-leche's.

`sorry`: the six guards (`fe.find?` through `IFEnvOK`, `reservedBasisNames`
and `isProjFnShape` through the two lemmas above, `nameNodup`,
`looseBVarsBoundedFast` and `hasFvarFast` through `Bridge/ExprOps/Walks.lean`),
then `KnotSpec.annotate`, `allLevelParamsDefined_run`,
`constsResolveFFast_run`, `KnotSpec.infer` and
`EnsureSortSpec.ensureSort`, in that order.  Task #97-P3-Checker's sorry list,
item 11 — the single highest-value remaining proof of the tier, since all
seven arms wait on it. 

**Restated in task #97-P3-Checker round 10** (the coordinator's ruling, for
the Inductives tier): the hypotheses are `CheckOK` and `EnvWF`, not `FoldOK`.
The inductive routes call it at an index that already holds a scratch
constant, where `FoldOK`'s `PersIFEnv` is false; the proof never read
`PersIFEnv` (the two sites that did computed an unused denotation).  The
arms use `checkConstantVal_bridge_of_fold`. -/
theorem checkConstantVal_pure {μ : CheckMode} {F : Nat} {env : Env}
    {c : ConstantVal} {ty sty : Expr} {u : Level}
    (h1 : env.find? c.name = none)
    (h2 : ConLeche.reservedBasisNames.contains c.name = false)
    (h3 : c.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup c.levelParams = true)
    (h5 : c.type.looseBVarsBounded 0 = true)
    (h6 : c.type.hasFvar = false)
    (h7 : ConLeche.annotateCore μ env F 0 c.type = .ok ty)
    (h8 : ty.allLevelParamsDefined c.levelParams = true)
    (h9 : ty.constsResolve env = true)
    (h10 : ConLeche.inferTypeCore μ env F 0 ty = .ok sty)
    (h11 : ConLeche.ensureSortCore μ env F 0 sty = .ok u) :
    ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c
      = .ok { c with type := ty } := by
  simp only [ConLeche.checkConstantVal, ConLeche.fueledOps, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, h10, h11, Option.isSome_none, Bool.false_eq_true, if_false,
    if_true, bind, Except.bind, pure, Except.pure]

theorem checkConstantVal_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {cv cvA : IConstantVal} {c : ConstantVal} {s s' : AState}
    (_hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hck0 : CheckOK μ env fe s) (henv : EnvWF env)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : checkConstantVal μ fe cv s = .ok (cvA, s')) :
    CoreStep μ env fe s s' ∧ ∃ cA F, Frontend.denoteCV s'.store cvA = some cA ∧
      ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA := by
  obtain ⟨hnm, hlps, hty⟩ := denoteCV_inv hcv
  have hknot := hk.knot env fe henv
  have hsortS := hk.sort env fe henv
  have hnever : ∀ {α β γ : Type} {x : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (x >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  simp only [Arena.checkConstantVal] at hrun
  -- 1. the duplicate-declaration guard
  obtain ⟨hdup, r1⟩ := AM.dguard_ok hnever hrun
  replace r1 := AM.pure_bind_ok r1
  have hfind : fe.find? cv.name = none := by
    cases hf : fe.find? cv.name with
    | none => rfl
    | some ci => rw [hf] at hdup; exact absurd rfl hdup
  have hfindP : env.find? c.name = none :=
    IFEnvOK.miss hck0.state hck0.ienv hnm hfind
  -- 2. the reserved-name guard
  obtain ⟨rs, s2, g2r, r2⟩ := AM.bind_ok r1
  obtain ⟨hp2, hrs⟩ := reservedBasisNames_run hck0.state.wf hck0.pins g2r
  have hck2 : CheckOK μ env fe s2 := hck0.mono ⟨hp2.wf⟩ hp2.ext hp2.caches hp2.pins
  have hnm2 : denoteN s2.store.ns cv.name = some c.name := denoteN_ext hnm hp2.ext
  have hlps2 : Frontend.denoteNList s2.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hp2.ext.lss.ls.ns _ _ hlps
  have hty2 : denoteE s2.store cv.type = some c.type := denote_ext hty hp2.ext
  obtain ⟨hres, r3⟩ := AM.dguard_ok hnever r2
  replace r3 := AM.pure_bind_ok r3
  have hresP : ConLeche.reservedBasisNames.contains c.name = false := by
    have hc := denoteNList_contains hck2.state.wf rs reservedBasisNameValues
      (denoteNL_toList rs reservedBasisNameValues hrs) cv.name c.name hnm2
    rw [← reservedBasisNameValues_eq, ← hc]
    cases hb : rs.contains cv.name with
    | false => rfl
    | true => rw [hb] at hres; exact absurd rfl hres
  -- 3. the reserved-projection-name guard
  obtain ⟨b3, s3, g3r, r4⟩ := AM.bind_ok r3
  obtain ⟨hs3, hb3⟩ := isProjFnShape_run hck2.state rfl hnm2 g3r
  obtain ⟨hproj, r5⟩ := AM.dguard_ok hnever r4
  replace r5 := AM.pure_bind_ok r5
  have hprojP : c.name.isProjFnShape = false := by
    rw [← hb3]
    cases hb : b3 with
    | false => rfl
    | true => rw [hb] at hproj; exact absurd rfl hproj
  -- 4. the duplicate-universe-parameter guard
  obtain ⟨hnod, r6⟩ := AM.dunless_ok hnever r5
  replace r6 := AM.pure_bind_ok r6
  have hnodP : ConLeche.Name.nodup c.levelParams = true := by
    rw [← nameNodup_spec hck2.state.wf cv.levelParams c.levelParams hlps2]
    exact hnod
  subst hs3
  -- 5. the loose-bound-variable guard
  obtain ⟨b5, s5, g5r, r7⟩ := AM.bind_ok r6
  obtain ⟨h5st, h5c, h5p, h5r⟩ := AM.of_run (P := fun t => t = s3)
    (Q := fun r t => t.store = s3.store ∧ t.caches = s3.caches ∧
      t.pins = s3.pins ∧ RelV (Expr.looseBVarsBounded 0) s3.store cv.type r)
    rfl g5r (ConRon.Bridge.ExprOps.looseBVarsBoundedFast_spec coreWalkFuel 0 s3 cv.type
      hck2.state (by rw [hty2]; rfl))
  obtain ⟨hlbb, r8⟩ := AM.dunless_ok hnever r7
  replace r8 := AM.pure_bind_ok r8
  have hlbbP : c.type.looseBVarsBounded 0 = true := by
    rw [← h5r c.type hty2]; exact hlbb
  have hck5 : CheckOK μ env fe s5 :=
    hck2.mono ⟨by rw [h5st]; exact hck2.state.wf⟩ (by rw [h5st]; exact Ext.refl _)
      h5c h5p
  have hnm5 : denoteN s5.store.ns cv.name = some c.name := by rw [h5st]; exact hnm2
  have hty5 : denoteE s5.store cv.type = some c.type := by rw [h5st]; exact hty2
  have hlps5 : Frontend.denoteNList s5.store.ns cv.levelParams
      = some c.levelParams := by rw [h5st]; exact hlps2
  -- 6. the free-variable guard
  obtain ⟨b6, s6, g6r, r9⟩ := AM.bind_ok r8
  obtain ⟨h6st, h6c, h6p, h6r⟩ := AM.of_run (P := fun t => t = s5)
    (Q := fun r t => t.store = s5.store ∧ t.caches = s5.caches ∧
      t.pins = s5.pins ∧ RelV Expr.hasFvar s5.store cv.type r)
    rfl g6r (ConRon.Bridge.ExprOps.hasFvarFast_spec coreWalkFuel s5 cv.type hck5.state
      (by rw [hty5]; rfl))
  obtain ⟨hfv, r10⟩ := AM.dguard_ok hnever r9
  replace r10 := AM.pure_bind_ok r10
  have hfvP : c.type.hasFvar = false := by
    rw [← h6r c.type hty5]
    cases hb : b6 with
    | false => rfl
    | true => rw [hb] at hfv; exact absurd rfl hfv
  have hck6 : CheckOK μ env fe s6 :=
    hck5.mono ⟨by rw [h6st]; exact hck5.state.wf⟩ (by rw [h6st]; exact Ext.refl _)
      h6c h6p
  have hnm6 : denoteN s6.store.ns cv.name = some c.name := by rw [h6st]; exact hnm5
  have hty6 : denoteE s6.store cv.type = some c.type := by rw [h6st]; exact hty5
  have hlps6 : Frontend.denoteNList s6.store.ns cv.levelParams
      = some c.levelParams := by rw [h6st]; exact hlps5
  have hws : Expr.WScoped 0 c.type := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  -- 7. the annotation
  obtain ⟨type, s7, g7r, r11⟩ := AM.bind_ok r10
  obtain ⟨hck7, hx7, hp7, hsim7⟩ := AM.of_run (P := fun t => t = s6)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s6.store t.store ∧
      t.pins = s6.pins ∧
      Core.SimE (ConLeche.annotateCore μ env) 0 c.type t.store r)
    rfl g7r (hknot.annotate s6 0 cv.type c.type hck6 hty6 hws)
  obtain ⟨v, hv7, hwsv, F7, hF7⟩ := hsim7
  have hnm7 : denoteN s7.store.ns cv.name = some c.name := denoteN_ext hnm6 hx7
  have hlps7 : Frontend.denoteNList s7.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hx7.lss.ls.ns _ _ hlps6
  -- 8. the undeclared-universe-parameter guard
  obtain ⟨b8, s8, g8r, r12⟩ := AM.bind_ok r11
  obtain ⟨h8st, h8c, h8p, h8r⟩ :=
    allLevelParamsDefined_run hck7.state hlps7 hv7 g8r
  obtain ⟨hlpd, r13⟩ := AM.dunless_ok hnever r12
  replace r13 := AM.pure_bind_ok r13
  have hlpdP : v.allLevelParamsDefined c.levelParams = true := by
    rw [← h8r]; exact hlpd
  have hck8 : CheckOK μ env fe s8 :=
    hck7.mono ⟨by rw [h8st]; exact hck7.state.wf⟩ (by rw [h8st]; exact Ext.refl _)
      h8c h8p
  have hv8 : denoteE s8.store type = some v := by rw [h8st]; exact hv7
  have hnm8 : denoteN s8.store.ns cv.name = some c.name := by rw [h8st]; exact hnm7
  have hlps8 : Frontend.denoteNList s8.store.ns cv.levelParams
      = some c.levelParams := by rw [h8st]; exact hlps7
  -- 9. the unresolved-constant guard
  obtain ⟨b9, s9, g9r, r14⟩ := AM.bind_ok r13
  have hpins8 : s8.pins = s.pins := by rw [h8p, hp7, h6p, h5p, hp2.pins]
  obtain ⟨h9st, h9c, h9p, h9r⟩ :=
    constsResolveFFast_run hck8 hv8 g9r
  obtain ⟨hcr, r15⟩ := AM.dunless_ok
    (AM.Never.bind fun _ => AM.Never.bind fun _ => AM.Never.fail_any) r14
  replace r15 := AM.pure_bind_ok r15
  have hcrP : v.constsResolve env = true := by rw [← h9r]; exact hcr
  have hck9 : CheckOK μ env fe s9 :=
    hck8.mono ⟨by rw [h9st]; exact hck8.state.wf⟩ (by rw [h9st]; exact Ext.refl _)
      h9c h9p
  have hv9 : denoteE s9.store type = some v := by rw [h9st]; exact hv8
  have hnm9 : denoteN s9.store.ns cv.name = some c.name := by rw [h9st]; exact hnm8
  have hlps9 : Frontend.denoteNList s9.store.ns cv.levelParams
      = some c.levelParams := by rw [h9st]; exact hlps8
  -- 10. the inference
  obtain ⟨stype, s10, g10r, r16⟩ := AM.bind_ok r15
  obtain ⟨hck10, hx10, hp10, hsim10⟩ := AM.of_run (P := fun t => t = s9)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s9.store t.store ∧
      t.pins = s9.pins ∧
      Core.SimE (ConLeche.inferTypeCore μ env) 0 v t.store r)
    rfl g10r (hknot.infer s9 0 type v hck9 hv9 hwsv)
  obtain ⟨w, hw10, hwsw, F10, hF10⟩ := hsim10
  have hv10 : denoteE s10.store type = some v := denote_ext hv9 hx10
  have hnm10 : denoteN s10.store.ns cv.name = some c.name := denoteN_ext hnm9 hx10
  have hlps10 : Frontend.denoteNList s10.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hx10.lss.ls.ns _ _ hlps9
  -- 11. the sort test
  obtain ⟨u, s11, g11r, r17⟩ := AM.bind_ok r16
  obtain ⟨hck11, hx11, hp11, hsim11⟩ := AM.of_run (P := fun t => t = s10)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s10.store t.store ∧
      t.pins = s10.pins ∧
      SimL (ConLeche.ensureSortCore μ env) 0 w t.store r)
    rfl g11r (hsortS s10 0 stype w hck10 hw10 hwsw)
  obtain ⟨uu, huu, F11, hF11⟩ := hsim11
  have hv11 : denoteE s11.store type = some v := denote_ext hv10 hx11
  have hnm11 : denoteN s11.store.ns cv.name = some c.name := denoteN_ext hnm10 hx11
  have hlps11 : Frontend.denoteNList s11.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hx11.lss.ls.ns _ _ hlps10
  -- 12. the answer
  obtain ⟨hcvA, hs'⟩ := AM.pure_ok r17
  subst hcvA
  subst hs'
  -- the frame
  have hext : Ext s.store s'.store := by
    refine hp2.ext.trans ?_
    rw [← h5st, ← h6st]
    refine hx7.trans ?_
    rw [← h8st, ← h9st]
    exact hx10.trans hx11
  have hpins : s'.pins = s.pins := by
    rw [hp11, hp10, h9p, h8p, hp7, h6p, h5p, hp2.pins]
  have hle7 : F7 ≤ max (max F7 F10) F11 :=
    Nat.le_trans (Nat.le_max_left F7 F10) (Nat.le_max_left _ F11)
  have hle10 : F10 ≤ max (max F7 F10) F11 :=
    Nat.le_trans (Nat.le_max_right F7 F10) (Nat.le_max_left _ F11)
  have hle11 : F11 ≤ max (max F7 F10) F11 := Nat.le_max_right _ F11
  refine ⟨⟨hck11, hext, hpins⟩,
    ⟨{ c with type := v }, max (max F7 F10) F11, ?_, ?_⟩⟩
  · simp only [Frontend.denoteCV, hnm11, hlps11, hv11]
  · exact checkConstantVal_pure hfindP hresP hprojP hnodP hlbbP hfvP
      (ConLeche.annotateCore_mono hle7 hF7) hlpdP hcrP
      (ConLeche.inferTypeCore_mono hle10 hF10)
      (ConLeche.ensureSortCore_mono hle11 hF11)


/-- con-leche: ConLeche/Verify/Cached/BridgeCS1.lean:43 checkConstantValS_sim —
`checkConstantVal_bridge` at the fold's invariant, which is what the seven
arms hold. -/
theorem checkConstantVal_bridge_of_fold {μ : CheckMode} {env : Env}
    {fe : IFEnv} {cv cvA : IConstantVal} {c : ConstantVal} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : checkConstantVal μ fe cv s = .ok (cvA, s')) :
    CoreStep μ env fe s s' ∧ ∃ cA F, Frontend.denoteCV s'.store cvA = some cA ∧
      ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA :=
  checkConstantVal_bridge hμ hk hok.check hok.envWF hcv hrun

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:279 checkConstantVal_datF —
one fuel for the front door, through con-leche's own monotone family. -/
theorem checkConstantVal_mono {μ : CheckMode} {env : Env} {c cA : ConstantVal}
    {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA) :
    ConLeche.checkConstantVal (ConLeche.fueledOps μ F') env c = .ok cA := by
  rw [← ConLeche.checkConstantVal_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkConstantVal (ConLeche.fueledOpsM μ) env c).property hle h

/-! ## The three list checks

`checkTypedList`, `checkAnnotList` and `checkDefEqList` are the nested-pin and
iota-statement guards: list recursions over one or two `KnotSpec` clauses each,
with nothing of their own.  Each is stated at the denoted lists, so the
recursion is `Frontend.denoteEList`'s.

**Two hypotheses the round that stated them did not have** (task
#97-P3-Checker-2): `EnvWF env`, because `CoreSpec.knot` is stated at a
well-formed environment, and the elements' `Expr.WScoped depth`, because every
`KnotSpec` slot takes it as a precondition.  Both are free at every call site —
the inductive tier reaches these through `CSpec`, which carries `CheckOK` at an
environment `FoldOK` already knows is well formed — but neither can be
conjured inside the proof. -/

/-- con-leche: none — `Frontend.denoteEList`'s `cons` inversion. -/
theorem denoteEList_cons {st : EStore} {a : EIdx} {as : List EIdx}
    {zs : List Expr} (h : Frontend.denoteEList st (a :: as) = some zs) :
    ∃ x xs, denoteE st a = some x ∧ Frontend.denoteEList st as = some xs ∧
      zs = x :: xs := by
  simp only [Frontend.denoteEList] at h
  cases hx : denoteE st a with
  | none => rw [hx] at h; exact absurd h (by simp)
  | some x =>
    cases hxs : Frontend.denoteEList st as with
    | none => rw [hx, hxs] at h; exact absurd h (by simp)
    | some xs =>
      rw [hx, hxs] at h
      simp only [Option.some.injEq] at h
      exact ⟨x, xs, rfl, rfl, h.symm⟩

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:330 checkTypedList_datF — one
fuel for a whole list check, through con-leche's own monotone family. -/
theorem checkTypedList_mono {μ : CheckMode} {env : Env} {depth F F' : Nat}
    {xs ys : List Expr} (hle : F ≤ F')
    (h : ConLeche.checkTypedList (ConLeche.fueledOps μ F) env depth xs ys
      = .ok ()) :
    ConLeche.checkTypedList (ConLeche.fueledOps μ F') env depth xs ys
      = .ok () := by
  rw [← ConLeche.checkTypedList_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkTypedList (ConLeche.fueledOpsM μ) env depth xs ys).property
    hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:348 checkAnnotList_datF — the
same for the annotation list. -/
theorem checkAnnotList_mono {μ : CheckMode} {env : Env} {depth F F' : Nat}
    {xs : List Expr} (hle : F ≤ F')
    (h : ConLeche.checkAnnotList (ConLeche.fueledOps μ F) env depth xs
      = .ok ()) :
    ConLeche.checkAnnotList (ConLeche.fueledOps μ F') env depth xs = .ok () := by
  rw [← ConLeche.checkAnnotList_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkAnnotList (ConLeche.fueledOpsM μ) env depth xs).property
    hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:313 checkDefEqList_datF — the
same for the pairwise conversion list. -/
theorem checkDefEqList_mono {μ : CheckMode} {env : Env} {depth F F' : Nat}
    {xs ys : List Expr} (hle : F ≤ F')
    (h : ConLeche.checkDefEqList (ConLeche.fueledOps μ F) env depth xs ys
      = .ok ()) :
    ConLeche.checkDefEqList (ConLeche.fueledOps μ F') env depth xs ys
      = .ok () := by
  rw [← ConLeche.checkDefEqList_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkDefEqList (ConLeche.fueledOpsM μ) env depth xs ys).property
    hle h

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:178-190 checkTypedList — the
pure side's step lemma at the `cons` clause. -/
theorem checkTypedList_cons_pure {μ : CheckMode} {env : Env} {depth F : Nat}
    {a t ty : Expr} {as ts : List Expr}
    (h1 : (ConLeche.fueledOps μ F).inferType env depth a = .ok ty)
    (h2 : (ConLeche.fueledOps μ F).isDefEq env depth ty t = .ok true)
    (h3 : ConLeche.checkTypedList (ConLeche.fueledOps μ F) env depth as ts
      = .ok ()) :
    ConLeche.checkTypedList (ConLeche.fueledOps μ F) env depth (a :: as)
      (t :: ts) = .ok () := by
  simp only [ConLeche.checkTypedList, h1, h2, h3, if_true, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:192-206 checkAnnotList — the
pure side's step lemma at the `cons` clause. -/
theorem checkAnnotList_cons_pure {μ : CheckMode} {env : Env} {depth F : Nat}
    {a : Expr} {as : List Expr}
    (h1 : (ConLeche.fueledOps μ F).annotate env depth a = .ok a)
    (h3 : ConLeche.checkAnnotList (ConLeche.fueledOps μ F) env depth as
      = .ok ()) :
    ConLeche.checkAnnotList (ConLeche.fueledOps μ F) env depth (a :: as)
      = .ok () := by
  simp only [ConLeche.checkAnnotList, h1, h3, beq_self_eq_true, if_true, bind,
    Except.bind]

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:222-231 checkDefEqList — the
pure side's step lemma at the `cons` clause. -/
theorem checkDefEqList_cons_pure {μ : CheckMode} {env : Env} {depth F : Nat}
    {a b : Expr} {as bs : List Expr}
    (h1 : (ConLeche.fueledOps μ F).isDefEq env depth a b = .ok true)
    (h3 : ConLeche.checkDefEqList (ConLeche.fueledOps μ F) env depth as bs
      = .ok ()) :
    ConLeche.checkDefEqList (ConLeche.fueledOps μ F) env depth (a :: as)
      (b :: bs) = .ok () := by
  simp only [ConLeche.checkDefEqList, h1, h3, if_true, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:178-190 checkTypedList —
**Theorem 1 for the nested-pin type check**: a list induction over
`KnotSpec.infer` and `KnotSpec.defeq`, one fuel for the whole list. -/
theorem checkTypedList_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) :
    ∀ (depth : Nat) (as ts : List EIdx) (xs ys : List Expr) (s s' : AState),
      CheckOK μ env fe s →
      Frontend.denoteEList s.store as = some xs →
      Frontend.denoteEList s.store ts = some ys →
      (∀ x ∈ xs, Expr.WScoped depth x) → (∀ y ∈ ys, Expr.WScoped depth y) →
      checkTypedList μ fe depth as ts s = .ok ((), s') →
      CoreStep μ env fe s s' ∧ ∃ F,
        ConLeche.checkTypedList (ConLeche.fueledOps μ F) env depth xs ys
          = .ok () := by
  have hknot := hk.knot env fe henv
  intro depth as
  induction as with
  | nil =>
    intro ts xs ys s s' hok ha ht _ _ hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at ha
    subst ha
    cases ts with
    | nil =>
      simp only [Frontend.denoteEList, Option.some.injEq] at ht
      subst ht
      obtain ⟨-, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, 0, rfl⟩
    | cons b bs => exact nomatch hrun
  | cons a as ih =>
    intro ts xs ys s s' hok ha ht hwx hwy hrun
    cases ts with
    | nil => exact nomatch hrun
    | cons t ts =>
      obtain ⟨x, xs', hx, hxs, rfl⟩ := denoteEList_cons ha
      obtain ⟨y, ys', hy, hys, rfl⟩ := denoteEList_cons ht
      simp only [Arena.checkTypedList] at hrun
      -- the inference
      obtain ⟨ty, s1, g1, r1⟩ := AM.bind_ok hrun
      obtain ⟨hok1, hx1, hp1, hsim1⟩ := AM.of_run (P := fun u => u = s)
        (Q := fun r u => CheckOK μ env fe u ∧ Ext s.store u.store ∧
          u.pins = s.pins ∧
          Core.SimE (ConLeche.inferTypeCore μ env) depth x u.store r)
        rfl g1 (hknot.infer s depth a x hok hx (hwx x (by simp)))
      obtain ⟨w, hw1, hwsw, F1, hF1⟩ := hsim1
      have hy1 : denoteE s1.store t = some y := denote_ext hy hx1
      -- the conversion
      obtain ⟨b2, s2, g2, r2⟩ := AM.bind_ok r1
      obtain ⟨hok2, hx2, hp2, hsim2⟩ := AM.of_run (P := fun u => u = s1)
        (Q := fun r u => CheckOK μ env fe u ∧ Ext s1.store u.store ∧
          u.pins = s1.pins ∧
          Core.SimV (ConLeche.isDefEqCore μ env) depth w y r)
        rfl g2 (hknot.defeq s1 depth ty t w y hok1 hw1 hy1 hwsw
          (hwy y (by simp)))
      obtain ⟨F2, hF2⟩ := hsim2
      obtain ⟨hb2, r3⟩ := AM.dunless_ok AM.Never.fail_any r2
      replace r3 := AM.pure_bind_ok r3
      subst hb2
      -- the tail
      have hxE : Ext s.store s2.store := hx1.trans hx2
      obtain ⟨hstep3, F3, hF3⟩ := ih ts xs' ys' s2 s' hok2
        (denoteEList_ext hxE _ _ hxs) (denoteEList_ext hxE _ _ hys)
        (fun z hz => hwx z (by simp [hz])) (fun z hz => hwy z (by simp [hz])) r3
      have hle1 : F1 ≤ max (max F1 F2) F3 :=
        Nat.le_trans (Nat.le_max_left F1 F2) (Nat.le_max_left _ F3)
      have hle2 : F2 ≤ max (max F1 F2) F3 :=
        Nat.le_trans (Nat.le_max_right F1 F2) (Nat.le_max_left _ F3)
      have hle3 : F3 ≤ max (max F1 F2) F3 := Nat.le_max_right _ F3
      refine ⟨⟨hstep3.ok, hxE.trans hstep3.ext, by rw [hstep3.pins, hp2, hp1]⟩,
        max (max F1 F2) F3, ?_⟩
      exact checkTypedList_cons_pure
        (ConLeche.inferTypeCore_mono hle1 hF1)
        (ConLeche.isDefEqCore_mono hle2 hF2)
        (checkTypedList_mono hle3 hF3)

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:192-206 checkAnnotList —
**Theorem 1 for the nested-pin annotation check**.  The twin compares HANDLES
where con-leche compares terms, and the two agree because `denoteE` is a
function: an accepted `aA == a` makes the annotation's denotation the
subject's own. -/
theorem checkAnnotList_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) :
    ∀ (depth : Nat) (as : List EIdx) (xs : List Expr) (s s' : AState),
      CheckOK μ env fe s →
      Frontend.denoteEList s.store as = some xs →
      (∀ x ∈ xs, Expr.WScoped depth x) →
      checkAnnotList μ fe depth as s = .ok ((), s') →
      CoreStep μ env fe s s' ∧ ∃ F,
        ConLeche.checkAnnotList (ConLeche.fueledOps μ F) env depth xs
          = .ok () := by
  have hknot := hk.knot env fe henv
  intro depth as
  induction as with
  | nil =>
    intro xs s s' hok ha _ hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at ha
    subst ha
    obtain ⟨-, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, 0, rfl⟩
  | cons a as ih =>
    intro xs s s' hok ha hwx hrun
    obtain ⟨x, xs', hx, hxs, rfl⟩ := denoteEList_cons ha
    simp only [Arena.checkAnnotList] at hrun
    obtain ⟨aA, s1, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨hok1, hx1, hp1, hsim1⟩ := AM.of_run (P := fun u => u = s)
      (Q := fun r u => CheckOK μ env fe u ∧ Ext s.store u.store ∧
        u.pins = s.pins ∧
        Core.SimE (ConLeche.annotateCore μ env) depth x u.store r)
      rfl g1 (hknot.annotate s depth a x hok hx (hwx x (by simp)))
    obtain ⟨v, hv1, hwsv, F1, hF1⟩ := hsim1
    obtain ⟨heq, r2⟩ := AM.dunless_ok AM.Never.fail_any r1
    replace r2 := AM.pure_bind_ok r2
    have haA : aA = a := eq_of_beq heq
    subst haA
    have hvx : v = x := Option.some.inj (hv1.symm.trans (denote_ext hx hx1))
    subst hvx
    obtain ⟨hstep2, F2, hF2⟩ := ih xs' s1 s' hok1 (denoteEList_ext hx1 _ _ hxs)
      (fun z hz => hwx z (by simp [hz])) r2
    have hle1 : F1 ≤ max F1 F2 := Nat.le_max_left _ _
    have hle2 : F2 ≤ max F1 F2 := Nat.le_max_right _ _
    refine ⟨⟨hstep2.ok, hx1.trans hstep2.ext, by rw [hstep2.pins, hp1]⟩,
      max F1 F2, ?_⟩
    exact checkAnnotList_cons_pure (ConLeche.annotateCore_mono hle1 hF1)
      (checkAnnotList_mono hle2 hF2)

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:222-231 checkDefEqList —
**Theorem 1 for the iota-statement component check**: a list induction over
`KnotSpec.defeq`. -/
theorem checkDefEqList_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) :
    ∀ (depth : Nat) (as bs : List EIdx) (xs ys : List Expr) (s s' : AState),
      CheckOK μ env fe s →
      Frontend.denoteEList s.store as = some xs →
      Frontend.denoteEList s.store bs = some ys →
      (∀ x ∈ xs, Expr.WScoped depth x) → (∀ y ∈ ys, Expr.WScoped depth y) →
      checkDefEqList μ fe depth as bs s = .ok ((), s') →
      CoreStep μ env fe s s' ∧ ∃ F,
        ConLeche.checkDefEqList (ConLeche.fueledOps μ F) env depth xs ys
          = .ok () := by
  have hknot := hk.knot env fe henv
  intro depth as
  induction as with
  | nil =>
    intro bs xs ys s s' hok ha hb _ _ hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at ha
    subst ha
    cases bs with
    | nil =>
      simp only [Frontend.denoteEList, Option.some.injEq] at hb
      subst hb
      obtain ⟨-, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, 0, rfl⟩
    | cons b bs => exact nomatch hrun
  | cons a as ih =>
    intro bs xs ys s s' hok ha hb hwx hwy hrun
    cases bs with
    | nil => exact nomatch hrun
    | cons b bs =>
      obtain ⟨x, xs', hx, hxs, rfl⟩ := denoteEList_cons ha
      obtain ⟨y, ys', hy, hys, rfl⟩ := denoteEList_cons hb
      simp only [Arena.checkDefEqList] at hrun
      obtain ⟨c1, s1, g1, r1⟩ := AM.bind_ok hrun
      obtain ⟨hok1, hx1, hp1, hsim1⟩ := AM.of_run (P := fun u => u = s)
        (Q := fun r u => CheckOK μ env fe u ∧ Ext s.store u.store ∧
          u.pins = s.pins ∧
          Core.SimV (ConLeche.isDefEqCore μ env) depth x y r)
        rfl g1 (hknot.defeq s depth a b x y hok hx hy (hwx x (by simp))
          (hwy y (by simp)))
      obtain ⟨F1, hF1⟩ := hsim1
      obtain ⟨hc1, r2⟩ := AM.dunless_ok AM.Never.fail_any r1
      replace r2 := AM.pure_bind_ok r2
      subst hc1
      obtain ⟨hstep2, F2, hF2⟩ := ih bs xs' ys' s1 s' hok1
        (denoteEList_ext hx1 _ _ hxs) (denoteEList_ext hx1 _ _ hys)
        (fun z hz => hwx z (by simp [hz])) (fun z hz => hwy z (by simp [hz])) r2
      have hle1 : F1 ≤ max F1 F2 := Nat.le_max_left _ _
      have hle2 : F2 ≤ max F1 F2 := Nat.le_max_right _ _
      refine ⟨⟨hstep2.ok, hx1.trans hstep2.ext, by rw [hstep2.pins, hp1]⟩,
        max F1 F2, ?_⟩
      exact checkDefEqList_cons_pure (ConLeche.isDefEqCore_mono hle1 hF1)
        (checkDefEqList_mono hle2 hF2)

end ConRon.Bridge
