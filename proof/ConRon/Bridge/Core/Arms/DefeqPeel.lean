/-
# `ConRon.Bridge.Core.Arms.DefeqPeel` — the batched ∀ descent's identification

Task #97-P3-Core round 6, restated for tasks #109 and #119.  The twin's
`quickDefEq` runs its `.forallE` arm as `defeqBinders`: the first domains
compared, then the batched `defeqPeel` for the rest of the two telescopes —
the one obligation of the Core tier that con-leche has no lemma for (task
#97-P6-14's batched defeq binder descent is the port's own algorithm).  It
is proved here, by induction on the peel's budget, over one invariant:

*`defeqPeel … a b k fvs` answers `x` only if, at some fuel, the chain's
`isDefEqCore` at depth `d + k` on the two OPENED residuals
`ca.instantiateList ws`, `cb.instantiateList ws` answers `x`*;
`defeqBinders_spec` folds the first level in and concludes con-leche's
`quickDefEq` on the two ∀s (`quick_step_pure`).  Since con-leche's task #342
the λ pair is not peeled (its arm is `defeqLams`, `Arms/DefeqLazy.lean`), and
no binder datum is compared, so the invariant carries no pending mismatch.

The parts of the argument written on `Arena/Core.lean`'s `defeqPeel` are the
places the proof spends something:

1. *the opens agree* — `Expr.instantiateList_cons` (`peel_open_body`), at the
   push-order vector's reversal (`InstLVec`);
2. *the chain reaches the ∀ arm at every level* — `isDefEqCore_forallE`: at
   each level the chain runs a whole `defeqBody`, whose prefix is a no-op on
   two ∀s (`isBoolTrue` is `false`), so it reaches `quickDefEq`'s ∀ arm on the
   pair itself (`quickDefEq_forallE`);
3. *fuel is existential* — `isDefEqCore_mono`.

The two equality short-circuits (`a == b` at the residuals, `da == db` at the
domains) are `isDefEqCore_refl`: at equal terms the chain's own syntactic
fast path answers `true` at every fuel that answers at all.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.StrCtor

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env}

/-! ## 1. The pure side -/

/-- con-leche: ConLeche/Kernel/Core.lean:1674-1702 defeqBody — the syntactic
fast path at the entry point: at equal terms every answer is `true`. -/
theorem isDefEqCore_refl {F d : Nat} {e : Expr} {v : Bool}
    (h : ConLeche.isDefEqCore mode env F d e e = .ok v) : v = true := by
  cases F with
  | zero => rw [ConLeche.isDefEqCore_zero] at h; cases h
  | succ F =>
    rw [ConLeche.isDefEqCore_succ, ConLeche.defeqBody] at h
    simp only [beq_self_eq_true, ite_true, pure, Except.pure] at h
    cases h; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1674-1702 defeqBody — and it does
answer, from fuel one on. -/
theorem isDefEqCore_refl_one {F d : Nat} {e : Expr} :
    ConLeche.isDefEqCore mode env (F + 1) d e e = .ok true := by
  rw [ConLeche.isDefEqCore_succ, ConLeche.defeqBody]
  simp only [beq_self_eq_true, ite_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1366 quickDefEq — **the ∀ arm of
the easy cases**: at two distinct ∀s `quickDefEq` is the domain comparison,
then the bodies opened at the second domain's free variable.  Stated for the
two ways the arm answers. -/
theorem quickDefEq_forallE {F d : Nat} {t₁ c₁ t₂ c₂ : Expr} {x : Bool}
    (hne : (Expr.forallE t₁ c₁ == .forallE t₂ c₂) = false)
    (h : (ConLeche.isDefEqCore mode env F d t₁ t₂ = .ok false ∧
            x = false) ∨
         (ConLeche.isDefEqCore mode env F d t₁ t₂ = .ok true ∧
            ConLeche.isDefEqCore mode env F (d + 1)
              (c₁.instantiate1 (.fvar d t₂)) (c₂.instantiate1 (.fvar d t₂))
              = .ok x)) :
    ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d
      (.forallE t₁ c₁) (.forallE t₂ c₂) = .ok (some x) := by
  unfold ConLeche.quickDefEq
  simp only [← ConLeche.defeq_def] at h
  rcases h with ⟨h1, rfl⟩ | ⟨h1, h2⟩
  · simp [hne, h1, bind, Except.bind, pure, Except.pure]
  · cases x <;> simp [hne, h1, h2, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1674-1702 defeqBody — **the chain's
∀ arm, as the peel needs it**: at two distinct ∀s the entry point IS
`quickDefEq`'s ∀ arm, because the body's only earlier step, the eq-true
shortcut, is a no-op off `Bool.true`, and the arm answers `some`. -/
theorem isDefEqCore_forallE {F d : Nat} {t₁ c₁ t₂ c₂ : Expr} {x : Bool}
    (hne : (Expr.forallE t₁ c₁ == .forallE t₂ c₂) = false)
    (h : (ConLeche.isDefEqCore mode env (F + 1) d t₁ t₂ = .ok false ∧
            x = false) ∨
         (ConLeche.isDefEqCore mode env (F + 1) d t₁ t₂ = .ok true ∧
            ConLeche.isDefEqCore mode env (F + 1) (d + 1)
              (c₁.instantiate1 (.fvar d t₂)) (c₂.instantiate1 (.fvar d t₂))
              = .ok x)) :
    ConLeche.isDefEqCore mode env (F + 2) d (.forallE t₁ c₁)
      (.forallE t₂ c₂) = .ok x := by
  have hq := quickDefEq_forallE hne h
  rw [ConLeche.isDefEqCore_succ, ConLeche.defeqBody]
  have hbt : (Expr.forallE t₂ c₂).isBoolTrue = false := rfl
  simp only [hne, hbt, Bool.false_and, Bool.false_eq_true, ite_false, bind,
    Except.bind, pure, Except.pure, hq]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — a ∀
opens componentwise, the body one cursor up. -/
theorem forallE_instantiateList (t c : Expr) (ws : List Expr) :
    (Expr.forallE t c).instantiateList ws 0 =
      .forallE (t.instantiateList ws 0) (c.instantiateList ws 1) := by
  simp [Expr.instantiateList]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:393 instantiateList_cons — **part
1 of the identification, the opens agree**: opening a raw body against one
more free variable is the chain's `instantiate1` of the body already opened
against the rest. -/
theorem peel_open_body (c v : Expr) (ws : List Expr) :
    c.instantiateList (v :: ws) 0 = (c.instantiateList ws 1).instantiate1 v :=
  Expr.instantiateList_cons ws c v 0

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1366 quickDefEq — **one peeled
level, on the pure side**: a domain verdict `dq` that holds from some fuel on,
the level's answer `false` when `dq` is, and otherwise the next level's
answer at the body pair the chain opens (at the second domain's free
variable), give this level's answer.  The equality case is the chain's
syntactic fast path; the other is `isDefEqCore_forallE`. -/
theorem peel_step_pure {j F1 F2 : Nat} {A1 c1 A2 c2 : Expr} {dq x : Bool}
    (hdq : ∀ F, F1 ≤ F → ConLeche.isDefEqCore mode env F j A1 A2 = .ok dq)
    (hx : dq = false → x = false)
    (hin : dq = true → ConLeche.isDefEqCore mode env F2 (j + 1)
      (c1.instantiate1 (.fvar j A2)) (c2.instantiate1 (.fvar j A2)) = .ok x) :
    ∃ F, ConLeche.isDefEqCore mode env F j (.forallE A1 c1) (.forallE A2 c2)
      = .ok x := by
  by_cases heq : (Expr.forallE A1 c1 == .forallE A2 c2) = true
  · -- the syntactic fast path: every component agrees
    have he : Expr.forallE A1 c1 = .forallE A2 c2 := eq_of_beq heq
    obtain ⟨rfl, rfl⟩ := Expr.forallE.inj he
    cases dq with
    | false =>
      exact absurd (isDefEqCore_refl (hdq F1 (Nat.le_refl _))) (by simp)
    | true =>
      obtain rfl := isDefEqCore_refl (hin rfl)
      exact ⟨1, isDefEqCore_refl_one⟩
  · have hne : (Expr.forallE A1 c1 == .forallE A2 c2) = false := by
      simpa using heq
    refine ⟨max F1 F2 + 2, ?_⟩
    have hd := hdq (max F1 F2 + 1) (by omega)
    cases dq with
    | false =>
      obtain rfl := hx rfl
      exact isDefEqCore_forallE hne (.inl ⟨hd, rfl⟩)
    | true =>
      exact isDefEqCore_forallE hne
        (.inr ⟨hd, ConLeche.isDefEqCore_mono (by omega) (hin rfl)⟩)

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1366 quickDefEq — **the first
binder level, on the pure side**: `peel_step_pure` at the top of the
telescope, where the twin's `quickDefEq` has already ruled out equal
binders; the conclusion is `quickDefEq`'s own answer. -/
theorem quick_step_pure {j F1 F2 : Nat} {A1 c1 A2 c2 : Expr} {dq x : Bool}
    (hne : (Expr.forallE A1 c1 == .forallE A2 c2) = false)
    (hdq : ∀ F, F1 ≤ F → ConLeche.isDefEqCore mode env F j A1 A2 = .ok dq)
    (hx : dq = false → x = false)
    (hin : dq = true → ConLeche.isDefEqCore mode env F2 (j + 1)
      (c1.instantiate1 (.fvar j A2)) (c2.instantiate1 (.fvar j A2)) = .ok x) :
    ∃ F, ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) j
      (.forallE A1 c1) (.forallE A2 c2) = .ok (some x) := by
  refine ⟨max F1 F2, ?_⟩
  have hd := hdq (max F1 F2) (by omega)
  cases dq with
  | false =>
    obtain rfl := hx rfl
    exact quickDefEq_forallE hne (.inl ⟨hd, rfl⟩)
  | true =>
    exact quickDefEq_forallE hne
      (.inr ⟨hd, ConLeche.isDefEqCore_mono (by omega) (hin rfl)⟩)

/-! ## 2. The twin's leaf -/

variable {fe : IFEnv} {fuel : Nat}

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1366 quickDefEq — **the peel's
leaf**: both residuals opened once against the whole vector, then the knot,
which is the chain's own next step. -/
theorem defeqPeelLeaf_spec (hsim : KnotSpec mode env fe fuel) (d : Nat)
    (s₀ : AState) (a b : EIdx) (k : Nat) (fvs : Array EIdx) (ws : List Expr)
    (ca cb : Expr) (hok : CheckOK mode env fe s₀)
    (ha : denoteE s₀.store a = some ca) (hb : denoteE s₀.store b = some cb)
    (hvec : ExprOps.InstLVec s₀.store fvs ws)
    (hwa : Expr.WScoped (d + k) (ca.instantiateList ws 0))
    (hwb : Expr.WScoped (d + k) (cb.instantiateList ws 0)) :
    ⦃fun s => s = s₀⦄
      defeqPeelLeaf (coreKnot mode fe id fuel) d a b k fvs
    ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ F, ConLeche.isDefEqCore mode env F (d + k) (ca.instantiateList ws 0)
          (cb.instantiateList ws 0) = .ok x; ⊤⦄ := by
  unfold defeqPeelLeaf
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ a fvs 0 ws
    hok.state hvec (by rw [ha]; rfl)) ?_
  rintro o1 s1 ⟨hst1, hx1, hc1, hp1, _, hrel1⟩
  have hok1 := hok.mono hst1 hx1 hc1 hp1
  have ho1 : denoteE s1.store o1 = some (ca.instantiateList ws 0) := hrel1 _ ha
  have hb1 := denote_ext hb hx1
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s1 b fvs 0 ws
    hst1 (hvec.ext hx1) (by rw [hb1]; rfl)) ?_
  rintro o2 s2 ⟨hst2, hx2, hc2, hp2, _, hrel2⟩
  have hok2 := hok1.mono hst2 hx2 hc2 hp2
  have ho2 : denoteE s2.store o2 = some (cb.instantiateList ws 0) := hrel2 _ hb1
  refine triple_mono (hsim.defeq s2 (d + k) o1 o2 _ _ hok2 (denote_ext ho1 hx2)
    ho2 hwa hwb) ?_
  rintro v s3 ⟨hok3, hx3, hp3, F, hF⟩
  exact ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1), F, hF⟩

/-! ## 3. The peel, by induction on its budget -/

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1366 quickDefEq — one level of
`Arena/Core.lean`'s `defeqPeel`, verbatim, with the recursive call (and the
dead budget-zero leaf) abstracted as `cont`.  The equation compiler cannot
produce `defeqPeel`'s own unfolding lemma within its fixed heartbeat budget
(a structural recursion whose recursive call sits under four monadic binds
and two `match`es), so the two unfoldings are stated here and proved by
`delta` and `rfl`. -/
def peelStep (r : CoreFnsA) (d : Nat) (peel : Nat)
    (cont : EIdx → EIdx → Nat → Array EIdx → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) : AM Bool := do
  if a == b then pure true
  else if peel = 0 || a.tag != ETag.forallE || b.tag != ETag.forallE then
    defeqPeelLeaf r d a b k fvs
  else
    match ← viewBind a with
    | none => failDanglingE
    | some (da, ba) =>
      match ← viewBind b with
      | none => failDanglingE
      | some (db, bb) => do
        let sameDom := da == db
        let t1 ← instantiateListFast coreWalkFuel da fvs 0
        let t2 ← if sameDom then pure t1
                 else instantiateListFast coreWalkFuel db fvs 0
        let dq ← if sameDom then pure true else r.defeq (d + k) t1 t2
        if !dq then pure false
        else do
          let fv ← internFVarE (d + k) t2
          cont ba bb (k + 1) (fvs.push fv)

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1366 quickDefEq — `defeqPeel` at
a successor budget is one level over the rest. -/
theorem defeqPeel_succ_eq (r : CoreFnsA) (d p : Nat)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) :
    defeqPeel r d (p + 1) a b k fvs =
      peelStep r d (p + 1) (defeqPeel r d p) a b k fvs := by
  delta defeqPeel peelStep
  exact rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1366 quickDefEq — and at budget
zero (where the level's own guard sends every pair to the leaf). -/
theorem defeqPeel_zero_eq (r : CoreFnsA) (d : Nat)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) :
    defeqPeel r d 0 a b k fvs =
      peelStep r d 0 (defeqPeelLeaf r d) a b k fvs := by
  delta defeqPeel peelStep
  exact rfl

/-- con-leche: none — the equality short-circuit: two equal handles are one
opened pair, and the chain's syntactic fast path answers `true`. -/
theorem peel_eq_case (s₀ : AState) (a b : EIdx) (j : Nat) (ws : List Expr)
    (ca cb : Expr) (hok : CheckOK mode env fe s₀)
    (ha : denoteE s₀.store a = some ca) (hb : denoteE s₀.store b = some cb)
    (hab : (a == b) = true) :
    ⦃fun s => s = s₀⦄ (pure true : AM Bool)
    ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ F, ConLeche.isDefEqCore mode env F j (ca.instantiateList ws 0)
          (cb.instantiateList ws 0) = .ok x; ⊤⦄ := by
  have hab' : a = b := eq_of_beq hab
  subst hab'
  obtain rfl : ca = cb := Option.some.inj (ha.symm.trans hb)
  vcgen
  subst_vars
  exact ⟨hok, Ext.refl _, rfl, 1, isDefEqCore_refl_one⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1366 quickDefEq — **THEOREM 1
for the batched descent**: at every budget, `defeqPeel` answers the chain's
`isDefEqCore` at the opened pair.  Induction on the budget; one level is
`peel_step_pure` over three stages (the two domain opens, the domain
comparison or its equality short-circuit, the fresh free variable). -/
theorem defeqPeel_spec (hsim : KnotSpec mode env fe fuel) (d : Nat) :
    ∀ (peel : Nat) (s₀ : AState) (a b : EIdx) (k : Nat) (fvs : Array EIdx)
      (ws : List Expr) (ca cb : Expr),
      CheckOK mode env fe s₀ → denoteE s₀.store a = some ca →
      denoteE s₀.store b = some cb → ExprOps.InstLVec s₀.store fvs ws →
      Expr.WScoped (d + k) (ca.instantiateList ws 0) →
      Expr.WScoped (d + k) (cb.instantiateList ws 0) →
      ⦃fun s => s = s₀⦄
        defeqPeel (coreKnot mode fe id fuel) d peel a b k fvs
      ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∃ F, ConLeche.isDefEqCore mode env F (d + k)
            (ca.instantiateList ws 0) (cb.instantiateList ws 0) = .ok x; ⊤⦄ := by
  intro peel
  induction peel with
  | zero =>
    intro s₀ a b k fvs ws ca cb hok ha hb hvec hwa hwb
    rw [defeqPeel_zero_eq]
    unfold peelStep
    split
    · rename_i hab
      exact peel_eq_case s₀ a b (d + k) ws ca cb hok ha hb hab
    · simp only [decide_true, Bool.true_or, ite_true]
      exact defeqPeelLeaf_spec hsim d s₀ a b k fvs ws ca cb hok ha hb
        hvec hwa hwb
  | succ p ih =>
    intro s₀ a b k fvs ws ca cb hok ha hb hvec hwa hwb
    rw [defeqPeel_succ_eq]
    unfold peelStep
    dsimp only
    split
    · rename_i hab
      exact peel_eq_case s₀ a b (d + k) ws ca cb hok ha hb hab
    split
    · exact defeqPeelLeaf_spec hsim d s₀ a b k fvs ws ca cb hok ha hb
        hvec hwa hwb
    rename_i hguard
    have htag : a.tag = ETag.forallE ∧ b.tag = ETag.forallE := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
        not_or, Decidable.not_not] at hguard
      exact ⟨hguard.1.2, hguard.2⟩
    have hwf := hok.state.wf
    -- stage 0: the two binder projections
    refine triple_seq (viewBind_spec s₀ a) ?_
    rintro ra s1 ⟨hs1, hra⟩
    subst s1 ra
    cases hva : s₀.store.viewBind a with
    | none => exact triple_failDanglingE
    | some pa =>
    obtain ⟨da, ba⟩ := pa
    dsimp only
    refine triple_seq (viewBind_spec s₀ b) ?_
    rintro rb s1 ⟨hs1, hrb⟩
    subst s1 rb
    cases hvb : s₀.store.viewBind b with
    | none => exact triple_failDanglingE
    | some pb =>
    obtain ⟨db, bb⟩ := pb
    dsimp only
    obtain ⟨tda, cba, rfl, hda, hba⟩ :=
      denote_forallE_inv hwf (view_of_viewBind_forallE htag.1 hva) ha
    obtain ⟨tdb, cbb, rfl, hdb, hbb⟩ :=
      denote_forallE_inv hwf (view_of_viewBind_forallE htag.2 hvb) hb
    rw [forallE_instantiateList] at hwa hwb ⊢
    rw [forallE_instantiateList]
    obtain ⟨hwA1, hwC1⟩ : Expr.WScoped (d + k) (tda.instantiateList ws 0) ∧
        Expr.WScoped (d + k) (cba.instantiateList ws 1) := by
      simpa only [Expr.WScoped] using hwa
    obtain ⟨hwA2, hwC2⟩ : Expr.WScoped (d + k) (tdb.instantiateList ws 0) ∧
        Expr.WScoped (d + k) (cbb.instantiateList ws 1) := by
      simpa only [Expr.WScoped] using hwb
    -- the level's tail, once the second domain `t2` and the verdict `dq` are
    -- in hand: the fresh free variable, then the rest of the telescope
    have tail : ∀ (t2 : EIdx) (dq : Bool) (s4 : AState),
        CheckOK mode env fe s4 → Ext s₀.store s4.store → s4.pins = s₀.pins →
        denoteE s4.store t2 = some (tdb.instantiateList ws 0) →
        (∃ F1, ∀ F, F1 ≤ F → ConLeche.isDefEqCore mode env F (d + k)
          (tda.instantiateList ws 0) (tdb.instantiateList ws 0) = .ok dq) →
        ⦃fun s => s = s4⦄
          (if (!dq) = true then pure false
           else do
             let fv ← internFVarE (d + k) t2
             defeqPeel (coreKnot mode fe id fuel) d p ba bb (k + 1)
               (fvs.push fv))
        ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
            s'.pins = s₀.pins ∧
            ∃ F, ConLeche.isDefEqCore mode env F (d + k)
              (.forallE (tda.instantiateList ws 0) (cba.instantiateList ws 1))
              (.forallE (tdb.instantiateList ws 0) (cbb.instantiateList ws 1))
              = .ok x; ⊤⦄ := by
      intro t2 dq s4 hok4 hx04 hp04 ht2 ⟨F1, hF1⟩
      cases dq with
      | false =>
        vcgen +internalize; subst_vars
        exact ⟨hok4, hx04, hp04, peel_step_pure (F2 := 0) hF1
          (fun _ => rfl) (fun h => absurd h (by simp))⟩
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        -- stage 4: the fresh free variable at the second opened domain
        refine triple_seq (internFVarE_spec s4 (d + k) t2 hok4.state.wf
          (by rw [ht2]; rfl)) ?_
        rintro fv s5 ⟨hwf5, hx5, -, -, -, hc5, hp5, -, hfv⟩
        have hok5 := hok4.mono ⟨hwf5⟩ hx5 hc5 hp5
        have hfv' : denoteE s5.store fv =
            some (.fvar (d + k) (tdb.instantiateList ws 0)) := by
          rw [hfv]; simp [denoteEView, denote_ext ht2 hx5]
        have hx05 : Ext s₀.store s5.store := hx04.trans hx5
        have hvec5 : ExprOps.InstLVec s5.store (fvs.push fv)
            (.fvar (d + k) (tdb.instantiateList ws 0) :: ws) := by
          unfold ExprOps.InstLVec
          simp only [Array.toList_push, List.reverse_cons]
          exact ExprOps.denoteEList_snoc hfv' _ _ (hvec.ext hx05)
        refine triple_mono (ih s5 ba bb (k + 1) (fvs.push fv)
          (.fvar (d + k) (tdb.instantiateList ws 0) :: ws) cba cbb hok5
          (denote_ext hba hx05) (denote_ext hbb hx05) hvec5 ?_ ?_) ?_
        · rw [peel_open_body]; exact Expr.WScoped.instantiate1 hwA2 0 hwC1
        · rw [peel_open_body]; exact Expr.WScoped.instantiate1 hwA2 0 hwC2
        rintro x s6 ⟨hok6, hx6, hp6, F2, hF2⟩
        refine ⟨hok6, hx05.trans hx6, hp6.trans (hp5.trans hp04), ?_⟩
        rw [peel_open_body, peel_open_body,
          show d + (k + 1) = d + k + 1 by omega] at hF2
        exact peel_step_pure hF1 (fun h => absurd h (by simp)) (fun _ => hF2)
    -- stage 1: the first domain, opened against the whole vector
    refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ da fvs 0
      ws hok.state hvec (by rw [hda]; rfl)) ?_
    rintro t1 s2 ⟨hst2, hx2, hc2, hp2, _, hrel2⟩
    have hok2 := hok.mono hst2 hx2 hc2 hp2
    have ht1 : denoteE s2.store t1 = some (tda.instantiateList ws 0) :=
      hrel2 _ hda
    by_cases hsame : (da == db) = true
    · -- stages 2–3, the equality short-circuit: one open, no knot call
      have hsd : da = db := eq_of_beq hsame
      subst hsd
      obtain rfl : tda = tdb := Option.some.inj (hda.symm.trans hdb)
      simp only [hsame, ite_true, pure_bind]
      exact tail t1 true s2 hok2 hx2 hp2 ht1 ⟨1, fun F hF => by
        obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
        exact isDefEqCore_refl_one⟩
    · have hsame' : (da == db) = false := by simpa using hsame
      simp only [hsame', Bool.false_eq_true, ite_false]
      -- stage 2: the second domain
      have hdb2 := denote_ext hdb hx2
      refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s2 db
        fvs 0 ws hst2 (hvec.ext hx2) (by rw [hdb2]; rfl)) ?_
      rintro t2 s3 ⟨hst3, hx3, hc3, hp3, _, hrel3⟩
      have hok3 := hok2.mono hst3 hx3 hc3 hp3
      have ht2 : denoteE s3.store t2 = some (tdb.instantiateList ws 0) :=
        hrel3 _ hdb2
      -- stage 3: the domain verdict
      refine triple_seq (hsim.defeq s3 (d + k) t1 t2 _ _ hok3
        (denote_ext ht1 hx3) ht2 hwA1 hwA2) ?_
      rintro dq s4 ⟨hok4, hx4, hp4, F1, hF1⟩
      exact tail t2 dq s4 hok4 (hx2.trans (hx3.trans hx4))
        (hp4.trans (hp3.trans hp2)) (denote_ext ht2 hx4)
        ⟨F1, fun F hF => ConLeche.isDefEqCore_mono hF hF1⟩

/-! ## 4. The arm: the first binder, then the peel -/

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1366 quickDefEq — **THEOREM 1
for `defeqBinders`**, `quickDefEq`'s ∀ arm on the twin side: the first
binder compared as the chain compares it, then `defeqPeel_spec` at budget
`peelFuel` from depth `d + 1`, and `quick_step_pure` to fold the first level
in; the answer is con-leche's `quickDefEq` on the two ∀s. -/
theorem defeqBinders_spec {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty1 body1 ty2 body2 : EIdx)
    (t1 b1 t2 b2 : Expr)
    (hok : CheckOK mode env fe s₀)
    (ht1 : denoteE s₀.store ty1 = some t1)
    (hb1 : denoteE s₀.store body1 = some b1)
    (ht2 : denoteE s₀.store ty2 = some t2)
    (hb2 : denoteE s₀.store body2 = some b2)
    (hwa : Expr.WScoped d (.forallE t1 b1))
    (hwb : Expr.WScoped d (.forallE t2 b2))
    (hne : (Expr.forallE t1 b1 == .forallE t2 b2) = false) :
    ⦃fun s => s = s₀⦄
      defeqBinders (coreKnot mode fe id fuel) d ty1 body1 ty2 body2
    ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ F, ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d
          (.forallE t1 b1) (.forallE t2 b2) = .ok (some x); ⊤⦄ := by
  obtain ⟨hwt1, hwb1⟩ : Expr.WScoped d t1 ∧ Expr.WScoped d b1 := by
    simpa only [Expr.WScoped] using hwa
  obtain ⟨hwt2, hwb2⟩ : Expr.WScoped d t2 ∧ Expr.WScoped d b2 := by
    simpa only [Expr.WScoped] using hwb
  unfold defeqBinders
  -- stage 1: the first domains, through the knot
  refine triple_seq (hsim.defeq s₀ d ty1 ty2 t1 t2 hok ht1 ht2 hwt1 hwt2) ?_
  rintro v s1 ⟨hok1, hx1, hp1, F1, hF1⟩
  have hdq : ∀ F, F1 ≤ F → ConLeche.isDefEqCore mode env F d t1 t2 = .ok v :=
    fun F hF => ConLeche.isDefEqCore_mono hF hF1
  cases v with
  | false =>
    vcgen +internalize; subst_vars
    exact ⟨hok1, hx1, hp1, quick_step_pure (F2 := 0) hne hdq
      (fun _ => rfl) (fun h => absurd h (by simp))⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    -- stage 2: the first free variable, at the second domain
    have ht2' := denote_ext ht2 hx1
    refine triple_seq (internFVarE_spec s1 d ty2 hok1.state.wf
      (by rw [ht2']; rfl)) ?_
    rintro fv s2 ⟨hwf2, hx2, -, -, -, hc2, hp2, -, hfv⟩
    have hok2 := hok1.mono ⟨hwf2⟩ hx2 hc2 hp2
    have hfv' : denoteE s2.store fv = some (.fvar d t2) := by
      rw [hfv]; simp [denoteEView, denote_ext ht2' hx2]
    have hx02 : Ext s₀.store s2.store := hx1.trans hx2
    have hvec : ExprOps.InstLVec s2.store #[fv] [.fvar d t2] := by
      unfold ExprOps.InstLVec
      simpa using ExprOps.denoteEList_snoc hfv' [] [] rfl
    -- stage 3: the rest of the two telescopes, batched
    refine triple_mono (defeqPeel_spec hsim d peelFuel s2 body1 body2 1 #[fv]
      [.fvar d t2] b1 b2 hok2 (denote_ext hb1 hx02) (denote_ext hb2 hx02)
      hvec ?_ ?_) ?_
    · rw [peel_open_body, Expr.instantiateList_nil]
      exact Expr.WScoped.instantiate1 hwt2 0 hwb1
    · rw [peel_open_body, Expr.instantiateList_nil]
      exact Expr.WScoped.instantiate1 hwt2 0 hwb2
    rintro x s3 ⟨hok3, hx3, hp3, F2, hF2⟩
    rw [peel_open_body, peel_open_body, Expr.instantiateList_nil,
      Expr.instantiateList_nil] at hF2
    refine ⟨hok3, hx02.trans hx3, hp3.trans (hp2.trans hp1), ?_⟩
    exact quick_step_pure hne hdq (fun h => absurd h (by simp)) (fun _ => hF2)

/-! ## The axiom census -/

#print axioms isDefEqCore_refl
#print axioms quickDefEq_forallE
#print axioms isDefEqCore_forallE
#print axioms quick_step_pure
#print axioms peel_step_pure
#print axioms defeqPeelLeaf_spec
#print axioms defeqPeel_succ_eq
#print axioms defeqPeel_zero_eq
#print axioms defeqPeel_spec
#print axioms defeqBinders_spec

end ConRon.Bridge.Core
