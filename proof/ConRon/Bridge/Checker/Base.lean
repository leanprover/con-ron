/-
# `ConRon.Bridge.Checker.Base` — `CheckerBase`'s specs

The twin of `ConLeche/Kernel/CheckerBase.lean` is `Arena/CheckerBase.lean`,
and this module is its bridge tier: the variant fallback, the two memoised
DAG walks the declaration front door runs, and the per-declaration constant
check.

## `orElseAttempt` — the only recovery

`Arena/CheckerBase.lean`'s `orElseAttempt` is the one place (B) recovers from
a thrown error.  A throw in `StateT σ (Except ε)` carries no state at all, so
the twin's error arm can only resume at `s`; the port moves back a full copy
of the pre-attempt state (DESIGN `### Task #97-T2-LOCKSTEP` D4b), which is
the same state.

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

## The rest

Everything else here bottoms out in `KnotSpec` (the inference call) and in the `ExprOps` tier's walks, and the guards that do
NOT are the memoised ones — `allLevelParamsDefined` and `constsResolveFFast`
— which `Arena/CheckerBase.lean` carries because con-leche's own tree walks do
not terminate on a shared DAG (con-leche's task #210 Part B).  Each is a
memoised walk with an explicitly threaded table, so each needs its own memo
invariant and its own fuel induction, in `Bridge/ExprOps/Walks.lean`'s shape.
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
`attemptRestore s (attemptSnapshot s)` is `s`.  In (C) the restore moves the
snapshot, a full copy of the pre-attempt state, back as the state, and
Theorem 2 (`Refine2/Checker/Base.lean`'s `attempt_restore_refines₀`) relates
that to `s` (DESIGN `### Task #97-T2-LOCKSTEP` D4b). -/
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

/-! ## The name-shape guards

Pure tests on handles.  Each is a handle comparison where con-leche has a
`Name` comparison, and each is exact for the same reason: `denoteN` is
injective (`Arena/WFProofs.lean`'s `denoteN_inj`, DESIGN §8.3's soundness
obligation).  The LIST membership test of the family,
`denoteNList_contains`, is `Bridge/Grind.lean`'s.

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

/-- con-leche: none — **a name handle's tag is its view's constructor**
(unconditionally: `NTables.get` dispatches on the tag).  What turns the
tag-first twin's tag test into the con-leche constructor test. -/
theorem NTables.tagOf_of_get {t : NTables} {i : NIdx} {v : NNodeView}
    (h : t.get i = some v) : i.tag = v.tagOf := by
  simp only [NTables.get] at h
  split at h
  · rename_i h1
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    exact eq_of_beq h1
  · split at h
    · rename_i _ h1
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      exact eq_of_beq h1
    · split at h
      · rename_i _ _ h1
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨_, _, rfl⟩ := h
        exact eq_of_beq h1
      · exact absurd h (by simp)

/-- con-leche: none — `NTables.tagOf_of_get` at the store. -/
theorem NStore.tagOf_of_view {st : NStore} {i : NIdx} {v : NNodeView}
    (h : st.view i = some v) : i.tag = v.tagOf := by
  simp only [NStore.view] at h
  split at h
  · exact NTables.tagOf_of_get h
  · split at h
    · exact NTables.tagOf_of_get h
    · exact absurd h (by simp)

/-! ## The per-declaration constant check -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal —
**THE declaration front door**, and what every arm of
`Bridge/Checker/Decl.lean` bottoms out in: the seven guards, the inference of
the type as stored, and the sort test.  It returns nothing (con-leche e74d32ad:
no annotation pass, `checkConstantVal` returns `Unit`).

The conclusion is a refinement, as everywhere in this tier: an accepting arena
run gives an accepting pure run whose answer the arena's answer denotes.  The
guards are what make it non-trivial — each must be *exact*, not merely sound,
because the arena's acceptance has to imply con-leche's.

Proved: the five guards (`fe.find?` through `IFEnvOK`, `reservedBasisNames`
through the lemma above, `nameNodup`,
`looseBVarsBoundedFast` and `hasFvarFast` through `Bridge/ExprOps/Walks.lean`),
then `allLevelParamsDefined_run`,
`constsResolveFFast_run`, `KnotSpec.infer` and
`EnsureSortSpec.ensureSort`, in that order.  All seven arms rest on it.

**The hypotheses are `CheckOK` and `EnvWF`, not `FoldOK`**, for the
Inductives tier: the inductive routes call it at an index that already holds
a scratch constant, where `FoldOK`'s `PersIFEnv` is false, and the proof
does not read `PersIFEnv`.  The arms use `checkConstantVal_bridge_of_fold`. -/
theorem checkConstantVal_pure {μ : CheckMode} {F : Nat} {env : Env}
    {c : ConstantVal} {sty : Expr} {u : Level}
    (h1 : env.find? c.name = none)
    (h2 : ConLeche.reservedBasisNames.contains c.name = false)
    (h4 : ConLeche.Name.nodup c.levelParams = true)
    (h5 : c.type.looseBVarsBounded 0 = true)
    (h6 : c.type.hasFvar = false)
    (h8 : c.type.allLevelParamsDefined c.levelParams = true)
    (h9 : c.type.constsResolve env = true)
    (h10 : ConLeche.inferTypeCore μ env F 0 c.type = .ok sty)
    (h11 : ConLeche.ensureSortCore μ env F 0 sty = .ok u) :
    ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok () := by
  simp only [ConLeche.checkConstantVal, ConLeche.fueledOps, h1, h2, h4, h5,
    h6, h8, h9, h10, h11, Option.isSome_none, Bool.false_eq_true, ite_false,
    ite_true, bind, Except.bind, pure, Except.pure]

theorem checkConstantVal_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {cv : IConstantVal} {c : ConstantVal} {s s' : AState}
    (_hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hck0 : CheckOK μ env fe s) (henv : EnvWF env)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : checkConstantVal μ fe cv s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok () := by
  obtain ⟨hnm, hlps, hty⟩ := denoteCV_inv hcv
  have hknot := hk.knot env fe henv
  have hsortS := hk.sort env fe henv
  have hnever : ∀ {α β γ : Type} {x : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (x >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  simp only [Arena.checkConstantVal] at hrun
  -- 1. the duplicate-declaration guard
  obtain ⟨hdup, r1⟩ := AM.dguard_ok AM.Never.fail_any hrun
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
  obtain ⟨hres, r3⟩ := AM.dguard_ok AM.Never.fail_any r2
  replace r3 := AM.pure_bind_ok r3
  have hresP : ConLeche.reservedBasisNames.contains c.name = false := by
    have hc := denoteNList_contains hck2.state.wf rs reservedBasisNameValues
      (denoteNL_toList rs reservedBasisNameValues hrs) cv.name c.name hnm2
    rw [← reservedBasisNameValues_eq, ← hc]
    cases hb : rs.contains cv.name with
    | false => rfl
    | true => rw [hb] at hres; exact absurd rfl hres
  -- 3. the duplicate-universe-parameter guard
  obtain ⟨hnod, r6⟩ := AM.dunless_ok AM.Never.fail_any r3
  replace r6 := AM.pure_bind_ok r6
  have hnodP : ConLeche.Name.nodup c.levelParams = true := by
    rw [← nameNodup_spec hck2.state.wf cv.levelParams c.levelParams hlps2]
    exact hnod
  -- 4. the loose-bound-variable guard
  obtain ⟨b5, s5, g5r, r7⟩ := AM.bind_ok r6
  obtain ⟨h5st, h5c, h5p, h5r⟩ := AM.of_run (P := fun t => t = s2)
    (Q := fun r t => t.store = s2.store ∧ t.caches = s2.caches ∧
      t.pins = s2.pins ∧ RelV (Expr.looseBVarsBounded 0) s2.store cv.type r)
    rfl g5r (ConRon.Bridge.ExprOps.looseBVarsBoundedFast_spec coreWalkFuel 0 s2 cv.type
      hck2.state (by rw [hty2]; rfl))
  obtain ⟨hlbb, r8⟩ := AM.dunless_ok AM.Never.fail_any r7
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
  -- 5. the free-variable guard
  obtain ⟨b6, s6, g6r, r9⟩ := AM.bind_ok r8
  obtain ⟨h6st, h6c, h6p, h6r⟩ := AM.of_run (P := fun t => t = s5)
    (Q := fun r t => t.store = s5.store ∧ t.caches = s5.caches ∧
      t.pins = s5.pins ∧ RelV Expr.hasFvar s5.store cv.type r)
    rfl g6r (ConRon.Bridge.ExprOps.hasFvarFast_spec coreWalkFuel s5 cv.type hck5.state
      (by rw [hty5]; rfl))
  obtain ⟨hfv, r10⟩ := AM.dguard_ok AM.Never.fail_any r9
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
  -- 6. the undeclared-universe-parameter guard
  obtain ⟨b8, s8, g8r, r12⟩ := AM.bind_ok r10
  obtain ⟨h8st, h8c, h8p, h8r⟩ :=
    allLevelParamsDefined_run hck6.state hlps6 hty6 g8r
  obtain ⟨hlpd, r13⟩ := AM.dunless_ok AM.Never.fail_any r12
  replace r13 := AM.pure_bind_ok r13
  have hlpdP : c.type.allLevelParamsDefined c.levelParams = true := by
    rw [← h8r]; exact hlpd
  have hck8 : CheckOK μ env fe s8 :=
    hck6.mono ⟨by rw [h8st]; exact hck6.state.wf⟩ (by rw [h8st]; exact Ext.refl _)
      h8c h8p
  have hty8 : denoteE s8.store cv.type = some c.type := by rw [h8st]; exact hty6
  -- 7. the unresolved-constant guard
  obtain ⟨b9, s9, g9r, r14⟩ := AM.bind_ok r13
  obtain ⟨h9st, h9c, h9p, h9r⟩ :=
    constsResolveFFast_run hck8 hty8 g9r
  obtain ⟨hcr, r15⟩ := AM.dunless_ok
    (AM.Never.bind fun _ => AM.Never.bind fun _ => AM.Never.fail_any) r14
  replace r15 := AM.pure_bind_ok r15
  have hcrP : c.type.constsResolve env = true := by rw [← h9r]; exact hcr
  have hck9 : CheckOK μ env fe s9 :=
    hck8.mono ⟨by rw [h9st]; exact hck8.state.wf⟩ (by rw [h9st]; exact Ext.refl _)
      h9c h9p
  have hty9 : denoteE s9.store cv.type = some c.type := by rw [h9st]; exact hty8
  -- 8. the inference, of the type AS STORED
  obtain ⟨stype, s10, g10r, r16⟩ := AM.bind_ok r15
  obtain ⟨hck10, hx10, hp10, hsim10⟩ := AM.of_run (P := fun t => t = s9)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s9.store t.store ∧
      t.pins = s9.pins ∧
      Core.SimE (ConLeche.inferTypeCore μ env) 0 c.type t.store r)
    rfl g10r (hknot.infer s9 0 cv.type c.type hck9 hty9 hws)
  obtain ⟨w, hw10, hwsw, F10, hF10⟩ := hsim10
  -- 9. the sort test
  obtain ⟨u, s11, g11r, r17⟩ := AM.bind_ok r16
  obtain ⟨hck11, hx11, hp11, hsim11⟩ := AM.of_run (P := fun t => t = s10)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s10.store t.store ∧
      t.pins = s10.pins ∧
      SimL (ConLeche.ensureSortCore μ env) 0 w t.store r)
    rfl g11r (hsortS s10 0 stype w hck10 hw10 hwsw)
  obtain ⟨uu, huu, F11, hF11⟩ := hsim11
  -- 10. the answer: the run ENDS at the sort test
  obtain ⟨-, rfl⟩ := AM.pure_ok r17
  -- the frame
  have hext : Ext s.store s'.store := by
    refine hp2.ext.trans ?_
    rw [← h5st, ← h6st, ← h8st, ← h9st]
    exact hx10.trans hx11
  have hpins : s'.pins = s.pins := by
    rw [hp11, hp10, h9p, h8p, h6p, h5p, hp2.pins]
  have hle10 : F10 ≤ max F10 F11 := Nat.le_max_left F10 F11
  have hle11 : F11 ≤ max F10 F11 := Nat.le_max_right F10 F11
  refine ⟨⟨hck11, hext, hpins⟩, max F10 F11, ?_⟩
  exact checkConstantVal_pure hfindP hresP hnodP hlbbP hfvP
    hlpdP hcrP
    (ConLeche.inferTypeCore_mono hle10 hF10)
    (ConLeche.ensureSortCore_mono hle11 hF11)


/-- con-leche: ConLeche/Verify/Cached/BridgeCS1.lean:43 checkConstantValS_sim —
`checkConstantVal_bridge` at the fold's invariant, which is what the seven
arms hold. -/
theorem checkConstantVal_bridge_of_fold {μ : CheckMode} {env : Env}
    {fe : IFEnv} {cv : IConstantVal} {c : ConstantVal} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : checkConstantVal μ fe cv s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok () :=
  checkConstantVal_bridge hμ hk hok.check hok.envWF hcv hrun

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:279 checkConstantVal_datF —
one fuel for the front door, through con-leche's own monotone family. -/
theorem checkConstantVal_mono {μ : CheckMode} {env : Env} {c : ConstantVal}
    {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok ()) :
    ConLeche.checkConstantVal (ConLeche.fueledOps μ F') env c = .ok () := by
  rw [← ConLeche.checkConstantVal_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkConstantVal (ConLeche.fueledOpsM μ) env c).property hle h

/-! ## A list inversion -/

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

end ConRon.Bridge
