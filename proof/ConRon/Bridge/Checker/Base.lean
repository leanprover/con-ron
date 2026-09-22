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
import ConRon.Bridge.ExprOps.Ranges

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

/-! ## The memoised DAG walks of the front door -/

/-- con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
— the memo invariant of `allLevelParamsDefinedGo`: a recorded answer is the
real one.  `Bridge/StateOK.lean`'s `MemoVOK` shape at an explicitly threaded
table (the walk does not use `Monad.lean`'s `Memos`: its answer depends on the
parameter LIST, which is a per-call datum). -/
def LPDMemoOK (params : List ConLeche.Name) (tbl : Std.HashMap EIdx Bool)
    (st : EStore) : Prop :=
  ∀ k v, tbl[k]? = some v →
    ∃ e, denoteE st k = some e ∧ v = Expr.allLevelParamsDefined params e

/-- con-leche: ConLeche/Kernel/Level.lean:405-407
Expr.allLevelParamsDefinedFast — **Theorem 1 for the front door's
level-parameter guard**: the memoised DAG walk answers what con-leche's
`allLevelParamsDefined` answers at the denoted parameter list.

`sorry`: the fuel induction in `Bridge/ExprOps/Walks.lean`'s shape, with
`LPDMemoOK` threaded (the walk's `memo` is an explicit argument-and-result
pair, so the invariant is a hypothesis and a conclusion rather than a state
clause).  Task #97-P3-Checker's sorry list, item 9. -/
theorem allLevelParamsDefined_run {lps : List NIdx} {ks : List ConLeche.Name}
    {e : EIdx} {x : Expr} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hlps : Frontend.denoteNList s.store.ns lps = some ks)
    (hd : denoteE s.store e = some x)
    (hrun : allLevelParamsDefined lps e s = .ok (r, s')) :
    s'.store = s.store ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      r = Expr.allLevelParamsDefined ks x := by
  sorry

/-- con-leche: ConLeche/Kernel/DeclCheck.lean:197-199 Expr.constsResolveFFast
— **Theorem 1 for the front door's unresolved-constant guard**: the memoised
DAG walk answers what con-leche's `Expr.constsResolve` answers at the denoted
environment.

`sorry`: the fuel induction, with the memo invariant and `IFEnvOK`'s `hit` /
`miss` pair at the `.const` and `.proj` arms (the walk asks `fe.find?` and
con-leche asks `env.find?`, and `IFEnvOK.miss` — hence `denoteN_inj` — is what
makes the two agree on a MISS).  Task #97-P3-Checker's sorry list, item 9. -/
theorem constsResolveFFast_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {e : EIdx} {x : Expr} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hd : denoteE s.store e = some x)
    (hrun : constsResolveFFast fe e s = .ok (r, s')) :
    s'.store = s.store ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      r = Expr.constsResolve env x := by
  sorry

/-! ## The name-shape guards

Three pure tests on handles.  Each is a handle comparison where con-leche has
a `Name` comparison, and each is exact for the same reason: `denoteN` is
injective (`Arena/WFProofs.lean`'s `denoteN_inj`, DESIGN §8.3's soundness
obligation).

**The `AM` readers, as equations.**  `viewN` is a `get` and a `match`, so its
run form is `rfl`; after `viewN_apply` no proof below mentions `StateT`. -/

/-- con-leche: none — `viewN`'s inversion, off `Bridge/Specs.lean`'s triple:
an accepting read leaves the state alone and names the view. -/
theorem viewN_run {h : NIdx} {s s' : AState} {v : NNodeView}
    (hr : viewN h s = .ok (v, s')) : s' = s ∧ s.store.ns.view h = some v :=
  AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ s.store.ns.view h = some r) rfl hr (viewN_spec s h)

/-- con-leche: none — **a handle comparison is a name comparison, at a LIST**:
`List.contains` over handles answers what `List.contains` over the denoted
names answers.  Both directions are needed and they come from different
places — `denoteN` is a function (handles equal ⇒ names equal) and it is
INJECTIVE (names equal ⇒ handles equal), which is DESIGN §8.3's soundness
obligation cashed. -/
theorem denoteNList_contains {st : EStore} (hwf : StoreWF st) :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns ns = some xs →
      ∀ (n : NIdx) (x : ConLeche.Name), denoteN st.ns n = some x →
        ns.contains n = xs.contains x := by
  obtain ⟨rk, hrk⟩ := hwf
  have hns : NStoreWF st.ns := hrk.nsWF
  intro ns
  induction ns with
  | nil => intro xs h n x _; simp only [Frontend.denoteNList, Option.some.injEq] at h
           subst h; rfl
  | cons a as ih =>
    intro xs h n x hx
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
        have hhead : (n == a) = (x == y) := by
          by_cases hae : a = n
          · subst hae
            rw [hx] at ha
            obtain rfl := Option.some.inj ha
            simp
          · have hae' : ¬ n = a := fun hh => hae hh.symm
            have hne' : ¬ x = y := by
              intro hxy; subst hxy
              exact hae (denoteN_inj hns ha hx)
            rw [beq_eq_false_iff_ne.mpr hae', beq_eq_false_iff_ne.mpr hne']
        simp only [List.contains_cons, hhead, ih ys has n x hx]

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

/-! ## The reserved-name list, interned

`Arena/Core.lean`'s `reservedBasisNames` is not `Arena/Pins.lean`'s
`pinReserved`: it reads six names off the pin table and INTERNS the other
thirteen, so it appends to the arena and its spec is an `Ext` rather than a
state equation.  The two halves are `Bridge/Specs.lean`'s `pinAt_spec` (which
consumes `PinsOK`) and `internName_spec` (which is closed), and the chain
re-establishes `PinsOK` after every append.

`PinStep` is the frame all nineteen steps share, so the chain is nineteen
lines of the same shape. -/

/-- con-leche: none — the frame a pin read or a name intern leaves: the store
only grew, and nothing else moved. -/
structure PinStep (s s' : AState) : Prop where
  wf : StoreWF s'.store
  ext : Ext s.store s'.store
  memos : s'.memos = s.memos
  caches : s'.caches = s.caches
  pins : s'.pins = s.pins

theorem PinStep.refl {s : AState} (h : StoreWF s.store) : PinStep s s :=
  ⟨h, Ext.refl _, rfl, rfl, rfl⟩

theorem PinStep.trans {a b c : AState} (h₁ : PinStep a b) (h₂ : PinStep b c) :
    PinStep a c :=
  ⟨h₂.wf, h₁.ext.trans h₂.ext, by rw [h₂.memos, h₁.memos],
    by rw [h₂.caches, h₁.caches], by rw [h₂.pins, h₁.pins]⟩

theorem PinStep.pinsOK {s s' : AState} (h : PinStep s s') (hp : PinsOK s) :
    PinsOK s' := hp.mono h.ext h.pins

/-- con-leche: none — `pinAt` in run form, off `Bridge/Specs.lean`'s triple. -/
theorem pinAt_run {i : Nat} {s s' : AState} {n : NIdx} {x : ConLeche.Name}
    (hp : PinsOK s) (hx : pinNames[i]? = some x)
    (hr : pinAt i s = .ok (n, s')) :
    s' = s ∧ denoteN s.store.ns n = some x := by
  have h := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ ∀ y, pinNames[i]? = some y →
      denoteN s.store.ns r = some y) rfl hr (pinAt_spec s i hp)
  exact ⟨h.1, h.2 x hx⟩

/-- con-leche: none — `internName` in run form, off `Bridge/Specs.lean`'s
triple. -/
theorem internName_run {nm : ConLeche.Name} {s s' : AState} {n : NIdx}
    (hwf : StoreWF s.store) (hr : internName nm s = .ok (n, s')) :
    PinStep s s' ∧ denoteN s'.store.ns n = some nm := by
  have h := AM.of_run (P := fun t => t = s)
    (Q := fun r t => StoreWF t.store ∧ Ext s.store t.store ∧
        t.store.pers = s.store.pers ∧ t.store.scr = s.store.scr ∧
        t.store.scratchOn = s.store.scratchOn ∧
        t.memos = s.memos ∧ t.caches = s.caches ∧ t.pins = s.pins ∧
        denoteN t.store.ns r = some nm) rfl hr (internName_spec s nm hwf)
  obtain ⟨h1, h2, _, _, _, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h6, h7, h8⟩, h9⟩

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
**the nineteen reserved names, as handles that denote them.**  Six are pin
slots and thirteen are fresh interns, so the run appends; the frame is
`PinStep` and the answer is `denoteNL` at con-leche's own list.

`sorry`: the nineteen-step chain over `pinAt_run` and `internName_run`, each
step transporting the earlier denotations across its `Ext` and `PinsOK` across
its append.  It is the pinned-literal exactness of task #97-P3-Checker's items
13/15 at the one caller that the declaration front door has. -/
theorem reservedBasisNames_run {s s' : AState} {hs : List NIdx}
    (hwf : StoreWF s.store) (hp : PinsOK s)
    (hr : reservedBasisNames s = .ok (hs, s')) :
    PinStep s s' ∧ denoteNL s'.store hs reservedBasisNameValues := by
  sorry

/-! ## The name-list denotation, as a function -/

/-- con-leche: none — `denoteNL` (the relation `PinsOK` is stated with) and
`Frontend.denoteNList` (the function everything else is stated with) are the
same fact. -/
theorem denoteNL_toList {st : EStore} :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name),
      denoteNL st hs xs → Frontend.denoteNList st.ns hs = some xs := by
  intro hs
  induction hs with
  | nil => intro xs h; cases xs with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons a as ih =>
    intro xs h
    cases xs with
    | nil => exact h.elim
    | cons y ys =>
      simp only [Frontend.denoteNList, h.1, ih ys h.2]

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-119 reservedBasisNames —
the arena's copy of the reserved list IS con-leche's, on the nose. -/
theorem reservedBasisNameValues_eq :
    reservedBasisNameValues = ConLeche.reservedBasisNames := rfl

/-! ## The constant header's denotation, inverted -/

/-- con-leche: none — `Frontend.denoteCV`'s inversion: the three fields denote
the three fields. -/
theorem denoteCV_inv {st : EStore} {cv : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st cv = some c) :
    denoteN st.ns cv.name = some c.name ∧
      Frontend.denoteNList st.ns cv.levelParams = some c.levelParams ∧
      denoteE st cv.type = some c.type := by
  simp only [Frontend.denoteCV] at h
  cases hn : denoteN st.ns cv.name with
  | none => rw [hn] at h; exact absurd h (by simp)
  | some n =>
    cases hl : Frontend.denoteNList st.ns cv.levelParams with
    | none => rw [hn, hl] at h; exact absurd h (by simp)
    | some lps =>
      cases ht : denoteE st cv.type with
      | none => rw [hn, hl, ht] at h; exact absurd h (by simp)
      | some ty =>
        rw [hn, hl, ht] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl⟩

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
seven arms wait on it. -/
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
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : checkConstantVal μ fe cv s = .ok (cvA, s')) :
    CoreStep μ env fe s s' ∧ ∃ cA F, Frontend.denoteCV s'.store cvA = some cA ∧
      ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA := by
  obtain ⟨hnm, hlps, hty⟩ := denoteCV_inv hcv
  have hknot := hk.knot env fe hok.envWF
  have hsortS := hk.sort env fe hok.envWF
  have hframe := hk.frame fe
  have hck0 : CheckOK μ env fe s := hok.check
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
  have hden6 : denoteFEnv s6.store fe = some env := by
    rw [h6st, h5st]
    exact denoteFEnv_pext (PExt.of_ext hp2.ext) hok.persEnv hok.denote
  -- 7. the annotation
  obtain ⟨type, s7, g7r, r11⟩ := AM.bind_ok r10
  obtain ⟨hck7, hx7, hsim7⟩ := AM.of_run (P := fun t => t = s6)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s6.store t.store ∧
      Core.SimE (ConLeche.annotateCore μ env) 0 c.type t.store r)
    rfl g7r (hknot.annotate s6 0 cv.type c.type hck6 hty6 hws)
  obtain ⟨v, hv7, hwsv, F7, hF7⟩ := hsim7
  have hp7 : s7.pins = s6.pins := hframe.annotate 0 cv.type s6 s7 type g7r
  have hnm7 : denoteN s7.store.ns cv.name = some c.name := denoteN_ext hnm6 hx7
  have hlps7 : Frontend.denoteNList s7.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hx7.lss.ls.ns _ _ hlps6
  have hden7 : denoteFEnv s7.store fe = some env :=
    denoteFEnv_pext (PExt.of_ext hx7) hok.persEnv hden6
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
  have hden8 : denoteFEnv s8.store fe = some env := by rw [h8st]; exact hden7
  -- 9. the unresolved-constant guard
  obtain ⟨b9, s9, g9r, r14⟩ := AM.bind_ok r13
  have hpins8 : s8.pins = s.pins := by rw [h8p, hp7, h6p, h5p, hp2.pins]
  obtain ⟨h9st, h9c, h9p, h9r⟩ :=
    constsResolveFFast_run ⟨hck8, hok.envWF, hok.persPins.mono hpins8,
      hok.persEnv, hok.coh, hden8⟩ hv8 g9r
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
  obtain ⟨hck10, hx10, hsim10⟩ := AM.of_run (P := fun t => t = s9)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s9.store t.store ∧
      Core.SimE (ConLeche.inferTypeCore μ env) 0 v t.store r)
    rfl g10r (hknot.infer s9 0 type v hck9 hv9 hwsv)
  obtain ⟨w, hw10, hwsw, F10, hF10⟩ := hsim10
  have hp10 : s10.pins = s9.pins := hframe.infer 0 type s9 s10 stype g10r
  have hv10 : denoteE s10.store type = some v := denote_ext hv9 hx10
  have hnm10 : denoteN s10.store.ns cv.name = some c.name := denoteN_ext hnm9 hx10
  have hlps10 : Frontend.denoteNList s10.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hx10.lss.ls.ns _ _ hlps9
  -- 11. the sort test
  obtain ⟨u, s11, g11r, r17⟩ := AM.bind_ok r16
  obtain ⟨hck11, hx11, hsim11⟩ := AM.of_run (P := fun t => t = s10)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s10.store t.store ∧
      SimL (ConLeche.ensureSortCore μ env) 0 w t.store r)
    rfl g11r (hsortS s10 0 stype w hck10 hw10 hwsw)
  obtain ⟨uu, huu, F11, hF11⟩ := hsim11
  have hp11 : s11.pins = s10.pins := hframe.sort 0 stype s10 s11 u g11r
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


/-! ## The three list checks

`checkTypedList`, `checkAnnotList` and `checkDefEqList` are the nested-pin and
iota-statement guards: list recursions over one `KnotSpec` clause each, with
nothing of their own.  Each is stated at the denoted lists, so the recursion
is `Frontend.denoteEList`'s. -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:178-190 checkTypedList.

`sorry`: a list induction over `KnotSpec.infer` and
`KnotSpec.defeq`.  Task #97-P3-Checker's sorry list, item 12. -/
theorem checkTypedList_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {depth : Nat} {as ts : List EIdx} {xs ys : List Expr}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : CheckOK μ env fe s)
    (ha : Frontend.denoteEList s.store as = some xs)
    (ht : Frontend.denoteEList s.store ts = some ys)
    (hrun : checkTypedList μ fe depth as ts s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkTypedList (ConLeche.fueledOps μ F) env depth xs ys
        = .ok () := by
  sorry

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:192-206 checkAnnotList.

`sorry`: a list induction over `KnotSpec.annotate` and `denoteE`'s
injectivity (the twin compares HANDLES where con-leche compares terms).  Task
#97-P3-Checker's sorry list, item 12. -/
theorem checkAnnotList_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {depth : Nat} {as : List EIdx} {xs : List Expr}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : CheckOK μ env fe s)
    (ha : Frontend.denoteEList s.store as = some xs)
    (hrun : checkAnnotList μ fe depth as s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkAnnotList (ConLeche.fueledOps μ F) env depth xs = .ok () := by
  sorry

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:222-231 checkDefEqList.

`sorry`: a list induction over `KnotSpec.defeq`.  Task
#97-P3-Checker's sorry list, item 12. -/
theorem checkDefEqList_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {depth : Nat} {as bs : List EIdx} {xs ys : List Expr}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : CheckOK μ env fe s)
    (ha : Frontend.denoteEList s.store as = some xs)
    (hb : Frontend.denoteEList s.store bs = some ys)
    (hrun : checkDefEqList μ fe depth as bs s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkDefEqList (ConLeche.fueledOps μ F) env depth xs ys
        = .ok () := by
  sorry

end ConRon.Bridge
