/-
# `ConRon.Bridge.Core.Arms.DefeqPeel` — the batched binder descent's identification

Task #97-P3-Core round 6.  `Arms/Defeq.lean`'s `defeqPeel_chain` — the one
obligation of the Core tier that con-leche has no lemma for (task #97-P6-14's
batched defeq binder descent is the port's own algorithm) — is proved here,
by induction on the peel's budget, over one invariant:

*`defeqPeel … a b k fvs mism` answers `x` only if, at some fuel, the chain's
`isDefEqCore` at depth `d + k` on the two OPENED residuals
`ca.instantiateList ws`, `cb.instantiateList ws` answers `false` and `x` is
`false`, or answers `true`, no mismatch is pending, and `x` is `true`*
(`PeelOK`).

The four parts of the doc comment on `defeqPeel_chain` are the four places the
proof spends something:

1. *the opens agree* — `Expr.instantiateList_cons` (`peel_open_body`), at the
   push-order vector's reversal (`InstLVec`);
2. *the chain reaches the binder arm at every level* — `isDefEqCore_bnd`,
   proved by unfolding con-leche's `defeqStep` at two distinct binders of one
   kind;
3. *a failure lands at the same binder* — `PeelOK` drops the message: a
   pending mismatch only ever turns an `ok true` into a throw, and
   `⇓?` claims nothing of a throw;
4. *fuel is existential* — `PeelOK.mono`, `isDefEqCore_mono`.

The two equality short-circuits (`a == b` at the residuals, `da == db` at the
domains) are `isDefEqCore_refl`: at equal terms the chain's own syntactic
fast path answers `true` at every fuel that answers at all.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.StrCtor

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. The pure side -/

/-- con-leche: none — a binder of either kind, the spelling of
`defeqPeel_chain`'s statement. -/
abbrev bndE (isLam : Bool) (t c : Expr) (m : BinderMeta) : Expr :=
  if isLam then .lam t c m else .forallE t c m

unseal ConLeche.defeqLoopFuel in
/-- con-leche: ConLeche/Kernel/Core.lean:1710-1714 defeqLoopFuel — the budget
is a successor (`Arms/Defeq.lean`'s `defeqLoopFuel_succ`, which this module
cannot import). -/
theorem defeqLoopFuel_succ' : ConLeche.defeqLoopFuel = 99999 + 1 := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1463-1464 defeqStep — the syntactic
fast path at the entry point: at equal terms every answer is `true`. -/
theorem isDefEqCore_refl {F d : Nat} {e : Expr} {v : Bool}
    (h : ConLeche.isDefEqCore mode env F d e e = .ok v) : v = true := by
  cases F with
  | zero => rw [ConLeche.isDefEqCore_zero] at h; cases h
  | succ F =>
    rw [ConLeche.isDefEqCore_succ, ConLeche.defeqBody, defeqLoopFuel_succ',
      ConLeche.defeqLoop, ConLeche.defeqStep] at h
    simp only [beq_self_eq_true, if_true, pure, Except.pure] at h
    cases h; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1463-1464 defeqStep — and it does
answer, from fuel one on. -/
theorem isDefEqCore_refl_one {F d : Nat} {e : Expr} :
    ConLeche.isDefEqCore mode env (F + 1) d e e = .ok true := by
  rw [ConLeche.isDefEqCore_succ, ConLeche.defeqBody, defeqLoopFuel_succ',
    ConLeche.defeqLoop, ConLeche.defeqStep]
  simp only [beq_self_eq_true, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1636-1662 defeqStep — **the chain's
binder arm, as the peel needs it**: at two distinct binders of one kind the
entry point is the domain comparison, then the bodies opened at the second
domain's free variable, then the annotation test, because every earlier arm
of the step is a no-op on two binders (`whnfCore` is the identity,
`isBoolTrue` is `false`, `quickPair` holds, `reduceNat` declines,
`unfoldableHead` is `false`).  Stated for the three ways the arm answers. -/
theorem isDefEqCore_bnd {F d : Nat} (isLam : Bool) {t₁ c₁ t₂ c₂ : Expr}
    {m₁ m₂ : BinderMeta} {x : Bool}
    (hne : (bndE isLam t₁ c₁ m₁ == bndE isLam t₂ c₂ m₂) = false)
    (h : (ConLeche.isDefEqCore mode env (F + 1) d t₁ t₂ = .ok false ∧
            x = false) ∨
         (ConLeche.isDefEqCore mode env (F + 1) d t₁ t₂ = .ok true ∧
            ConLeche.isDefEqCore mode env (F + 1) (d + 1)
              (c₁.instantiate1 (.fvar d t₂)) (c₂.instantiate1 (.fvar d t₂))
              = .ok false ∧ x = false) ∨
         (ConLeche.isDefEqCore mode env (F + 1) d t₁ t₂ = .ok true ∧
            ConLeche.isDefEqCore mode env (F + 1) (d + 1)
              (c₁.instantiate1 (.fvar d t₂)) (c₂.instantiate1 (.fvar d t₂))
              = .ok true ∧
            (mode.verifiedChecks && !(m₁.pw == m₂.pw)) = false ∧ x = true)) :
    ConLeche.isDefEqCore mode env (F + 2) d (bndE isLam t₁ c₁ m₁)
      (bndE isLam t₂ c₂ m₂) = .ok x := by
  rw [ConLeche.isDefEqCore_succ, ConLeche.defeqBody, defeqLoopFuel_succ',
    ConLeche.defeqLoop, ConLeche.defeqStep]
  cases isLam
  · simp only [bndE, Bool.false_eq_true, if_false] at hne ⊢
    have ha : (ConLeche.pureFns mode env (F + 1)).whnfCore d (.forallE t₁ c₁ m₁) =
        .ok (.forallE t₁ c₁ m₁) := rfl
    have hb : (ConLeche.pureFns mode env (F + 1)).whnfCore d (.forallE t₂ c₂ m₂) =
        .ok (.forallE t₂ c₂ m₂) := rfl
    simp only [ha, hb]
    simp only [ConLeche.isDefEqCore_succ] at h
    rcases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, hm, rfl⟩
    · simp [hne,
        ConLeche.Expr.quickPair, ConLeche.reduceNat, ConLeche.unfoldableHead,
        ConLeche.Expr.getAppFn,
        ConLeche.Expr.isBoolTrue, h1, bind, Except.bind, pure, Except.pure]
    · simp [hne,
        ConLeche.Expr.quickPair, ConLeche.reduceNat, ConLeche.unfoldableHead,
        ConLeche.Expr.getAppFn,
        ConLeche.Expr.isBoolTrue, h1, h2, bind, Except.bind, pure, Except.pure]
    · simp [hne,
        ConLeche.Expr.quickPair, ConLeche.reduceNat, ConLeche.unfoldableHead,
        ConLeche.Expr.getAppFn,
        ConLeche.Expr.isBoolTrue, h1, h2, hm, bind, Except.bind, pure,
        Except.pure]
  · simp only [bndE, if_true] at hne ⊢
    have ha : (ConLeche.pureFns mode env (F + 1)).whnfCore d (.lam t₁ c₁ m₁) =
        .ok (.lam t₁ c₁ m₁) := rfl
    have hb : (ConLeche.pureFns mode env (F + 1)).whnfCore d (.lam t₂ c₂ m₂) =
        .ok (.lam t₂ c₂ m₂) := rfl
    simp only [ha, hb]
    simp only [ConLeche.isDefEqCore_succ] at h
    rcases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, hm, rfl⟩
    · simp [hne,
        ConLeche.Expr.quickPair, ConLeche.reduceNat, ConLeche.unfoldableHead,
        ConLeche.Expr.getAppFn,
        ConLeche.Expr.isBoolTrue, h1, bind, Except.bind, pure, Except.pure]
    · simp [hne,
        ConLeche.Expr.quickPair, ConLeche.reduceNat, ConLeche.unfoldableHead,
        ConLeche.Expr.getAppFn,
        ConLeche.Expr.isBoolTrue, h1, h2, bind, Except.bind, pure, Except.pure]
    · simp [hne,
        ConLeche.Expr.quickPair, ConLeche.reduceNat, ConLeche.unfoldableHead,
        ConLeche.Expr.getAppFn,
        ConLeche.Expr.isBoolTrue, h1, h2, hm, bind, Except.bind, pure,
        Except.pure]

/-- con-leche: none — **the peel's invariant**: the peel's answer `x` is the
chain's continuation at the opened pair `oa`, `ob` — the entry point's
`false` (and then `x` is `false`), or its `true` with no mismatch pending
(and then `x` is `true`).  A pending mismatch turns the chain's `true` into
a throw, which `⇓?` does not see: the message is not part of the claim. -/
def PeelOK (mode : CheckMode) (env : Env) (F j : Nat) (oa ob : Expr)
    (mism x : Bool) : Prop :=
  (ConLeche.isDefEqCore mode env F j oa ob = .ok false ∧ x = false) ∨
  (ConLeche.isDefEqCore mode env F j oa ob = .ok true ∧ mism = false ∧
    x = true)

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the
invariant is fuel-monotone. -/
theorem PeelOK.mono {F F' j : Nat} {oa ob : Expr} {mism x : Bool}
    (hle : F ≤ F') (h : PeelOK mode env F j oa ob mism x) :
    PeelOK mode env F' j oa ob mism x := by
  rcases h with ⟨h, rfl⟩ | ⟨h, hm, rfl⟩
  · exact .inl ⟨ConLeche.isDefEqCore_mono hle h, rfl⟩
  · exact .inr ⟨ConLeche.isDefEqCore_mono hle h, hm, rfl⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211-226 instantiateList — a
binder opens componentwise, the body one cursor up. -/
theorem bndE_instantiateList (L : Bool) (t c : Expr) (m : BinderMeta)
    (ws : List Expr) :
    (bndE L t c m).instantiateList ws 0 =
      bndE L (t.instantiateList ws 0) (c.instantiateList ws 1) m := by
  cases L <;> simp [bndE, Expr.instantiateList]

/-- con-leche: ConLeche/Verify/InstList.lean:54 instantiateList_cons — **part
1 of the identification, the opens agree**: opening a raw body against one
more free variable is the chain's `instantiate1` of the body already opened
against the rest. -/
theorem peel_open_body (c v : Expr) (ws : List Expr) :
    c.instantiateList (v :: ws) 0 = (c.instantiateList ws 1).instantiate1 v :=
  Expr.instantiateList_cons ws c v 0

/-- con-leche: ConLeche/Kernel/Core.lean:1636-1662 defeqStep — **one peeled
level, on the pure side**: a domain verdict `dq` that holds from some fuel on,
the level's answer `false` when `dq` is, and otherwise the next level's
invariant at the body pair the chain opens (at the second domain's free
variable, with this level's mismatch `mm` folded into the pending flag), give
this level's invariant.  The equality case is the chain's syntactic fast
path; the other is `isDefEqCore_bnd`. -/
theorem peel_step_pure {j F1 F2 : Nat} (L : Bool) {A1 c1 A2 c2 : Expr}
    {m1 m2 : BinderMeta} {dq mism mm x : Bool}
    (hdq : ∀ F, F1 ≤ F → ConLeche.isDefEqCore mode env F j A1 A2 = .ok dq)
    (hx : dq = false → x = false)
    (hin : dq = true → PeelOK mode env F2 (j + 1)
      (c1.instantiate1 (.fvar j A2)) (c2.instantiate1 (.fvar j A2))
      (mism || mm) x)
    (hmm : mm = false → (mode.verifiedChecks && !(m1.pw == m2.pw)) = false) :
    ∃ F, PeelOK mode env F j (bndE L A1 c1 m1) (bndE L A2 c2 m2) mism x := by
  by_cases heq : (bndE L A1 c1 m1 == bndE L A2 c2 m2) = true
  · -- the syntactic fast path: every component agrees
    have he : bndE L A1 c1 m1 = bndE L A2 c2 m2 := eq_of_beq heq
    have hA : A1 = A2 ∧ c1 = c2 := by
      cases L <;> simp only [bndE, Bool.false_eq_true, if_false, if_true,
        Expr.lam.injEq, Expr.forallE.injEq] at he <;> exact ⟨he.1, he.2.1⟩
    obtain ⟨rfl, rfl⟩ := hA
    cases dq with
    | false =>
      have h0 := hdq F1 (Nat.le_refl _)
      exact absurd (isDefEqCore_refl h0) (by simp)
    | true =>
      rcases hin rfl with ⟨h1, _⟩ | ⟨_, hm, rfl⟩
      · exact absurd (isDefEqCore_refl h1) (by simp)
      · refine ⟨1, .inr ⟨?_, ?_, rfl⟩⟩
        · rw [he]; exact isDefEqCore_refl_one
        · cases mism <;> simp_all
  · have hne : (bndE L A1 c1 m1 == bndE L A2 c2 m2) = false := by
      simpa using heq
    refine ⟨max F1 F2 + 2, ?_⟩
    have hd := hdq (max F1 F2 + 1) (by omega)
    cases dq with
    | false =>
      obtain rfl := hx rfl
      exact .inl ⟨isDefEqCore_bnd L hne (.inl ⟨hd, rfl⟩), rfl⟩
    | true =>
      rcases hin rfl with ⟨h1, rfl⟩ | ⟨h1, hm, rfl⟩
      · exact .inl ⟨isDefEqCore_bnd L hne
          (.inr (.inl ⟨hd, ConLeche.isDefEqCore_mono (by omega) h1, rfl⟩)), rfl⟩
      · have hm1 : mism = false := by cases mism <;> simp_all
        have hm2 : mm = false := by cases mm <;> simp_all
        exact .inr ⟨isDefEqCore_bnd L hne (.inr (.inr ⟨hd,
          ConLeche.isDefEqCore_mono (by omega) h1, hmm hm2, rfl⟩)), hm1, rfl⟩

/-! ## 2. The twin's three pieces -/

variable {fe : IFEnv} {fuel : Nat}

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — the peel's
outward step answers only `true`, and only with no mismatch pending. -/
theorem defeqPeelDone_spec (s₀ : AState) (mism ml : Bool) :
    ⦃fun s => ⌜s = s₀⌝⦄ defeqPeelDone mism ml
    ⦃⇓? r s' => ⌜s' = s₀ ∧ mism = false ∧ r = true⌝⦄ := by
  unfold defeqPeelDone
  cases mism with
  | true =>
    simp only [if_true]
    split
    · exact triple_fail
    · exact triple_fail
  | false =>
    simp only [Bool.false_eq_true, if_false]
    mvcgen

/-- con-leche: none — the equality short-circuit: two equal handles are one
opened pair, and the chain's syntactic fast path answers `true`. -/
theorem peel_eq_case (s₀ : AState) (a b : EIdx) (j : Nat) (ws : List Expr)
    (mism ml : Bool) (ca cb : Expr) (hok : CheckOK mode env fe s₀)
    (ha : denoteE s₀.store a = some ca) (hb : denoteE s₀.store b = some cb)
    (hab : (a == b) = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ defeqPeelDone mism ml
    ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ F, PeelOK mode env F j (ca.instantiateList ws 0)
          (cb.instantiateList ws 0) mism x⌝⦄ := by
  have hab' : a = b := eq_of_beq hab
  subst hab'
  obtain rfl : ca = cb := Option.some.inj (ha.symm.trans hb)
  refine triple_mono (defeqPeelDone_spec s₀ mism ml) ?_
  rintro x s' ⟨rfl, hm, rfl⟩
  exact ⟨hok, Ext.refl _, rfl, 1, .inr ⟨isDefEqCore_refl_one, hm, rfl⟩⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — **the peel's
leaf**: both residuals opened once against the whole vector, then the knot,
which is the chain's own next step. -/
theorem defeqPeelLeaf_spec (hsim : KnotSpec mode env fe fuel) (d : Nat)
    (s₀ : AState) (a b : EIdx) (k : Nat) (fvs : Array EIdx) (ws : List Expr)
    (mism ml : Bool) (ca cb : Expr) (hok : CheckOK mode env fe s₀)
    (ha : denoteE s₀.store a = some ca) (hb : denoteE s₀.store b = some cb)
    (hvec : ExprOps.InstLVec s₀.store fvs ws)
    (hwa : Expr.WScoped (d + k) (ca.instantiateList ws 0))
    (hwb : Expr.WScoped (d + k) (cb.instantiateList ws 0)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      defeqPeelLeaf (coreKnot mode fe id fuel) d a b k fvs mism ml
    ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ F, PeelOK mode env F (d + k) (ca.instantiateList ws 0)
          (cb.instantiateList ws 0) mism x⌝⦄ := by
  unfold defeqPeelLeaf
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ a fvs 0 ws
    hok.state hvec (by rw [ha]; rfl)) ?_
  rintro o1 s1 ⟨hst1, hx1, _, hc1, hp1, _, hrel1⟩
  have hok1 := hok.mono hst1 hx1 hc1 hp1
  have ho1 : denoteE s1.store o1 = some (ca.instantiateList ws 0) := hrel1 _ ha
  have hb1 := denote_ext hb hx1
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s1 b fvs 0 ws
    hst1 (hvec.ext hx1) (by rw [hb1]; rfl)) ?_
  rintro o2 s2 ⟨hst2, hx2, _, hc2, hp2, _, hrel2⟩
  have hok2 := hok1.mono hst2 hx2 hc2 hp2
  have ho2 : denoteE s2.store o2 = some (cb.instantiateList ws 0) := hrel2 _ hb1
  refine triple_seq (hsim.defeq s2 (d + k) o1 o2 _ _ hok2 (denote_ext ho1 hx2)
    ho2 hwa hwb) ?_
  rintro v s3 ⟨hok3, hx3, hp3, F, hF⟩
  have hx03 : Ext s₀.store s3.store := hx1.trans (hx2.trans hx3)
  have hp03 : s3.pins = s₀.pins := hp3.trans (hp2.trans hp1)
  cases v with
  | false =>
    simp only [Bool.not_false, if_true]
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok3, hx03, hp03, F, .inl ⟨hF, rfl⟩⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    refine triple_mono (defeqPeelDone_spec s3 mism ml) ?_
    rintro x s' ⟨rfl, hm, rfl⟩
    exact ⟨hok3, hx03, hp03, F, .inr ⟨hF, hm, rfl⟩⟩

/-! ## 3. The peel, by induction on its budget -/

/-- con-leche: ConLeche/Verify/Shift.lean:115 WScoped — a binder is well
scoped exactly when its domain and its body are. -/
theorem wscoped_bndE {j : Nat} {L : Bool} {t c : Expr} {m : BinderMeta} :
    Expr.WScoped j (bndE L t c m) ↔ Expr.WScoped j t ∧ Expr.WScoped j c := by
  cases L <;> simp [bndE, Expr.WScoped]

/-- con-leche: none — a handle whose view is a binder of its own tag denotes
that binder, `bndE` at the tag's kind. -/
theorem denote_bind_inv {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} {e : Expr} (hw : st.view h = some (eBindView h.tag ty b m))
    (he : denoteE st h = some e) :
    ∃ et eb, e = bndE (h.tag == ETag.lam) et eb m ∧ denoteE st ty = some et ∧
      denoteE st b = some eb := by
  unfold eBindView at hw
  split at hw
  · rename_i hl
    obtain ⟨et, eb, rfl, h1, h2⟩ := denote_lam_inv hwf hw he
    exact ⟨et, eb, by simp [bndE, hl], h1, h2⟩
  · rename_i hl
    obtain ⟨et, eb, rfl, h1, h2⟩ := denote_forallE_inv hwf hw he
    exact ⟨et, eb, by simp [bndE, hl], h1, h2⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — one level of
`Arena/Core.lean`'s `defeqPeel`, verbatim, with the recursive call (and the
dead budget-zero leaf) abstracted as `cont`.  The equation compiler cannot
produce `defeqPeel`'s own unfolding lemma within its fixed heartbeat budget
(a structural recursion whose recursive call sits under four monadic binds
and two `match`es), so the two unfoldings are stated here and proved by
`delta` and `rfl`. -/
def peelStep (mode : CheckMode) (r : CoreFnsA) (d : Nat) (peel : Nat)
    (cont : EIdx → EIdx → Nat → Array EIdx → Bool → Bool → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (mism mismLam : Bool) :
    AM Bool := do
  let ta := a.tag
  if a == b then defeqPeelDone mism mismLam
  else if peel = 0 || ta != b.tag || !(ETag.isBind ta) then
    defeqPeelLeaf r d a b k fvs mism mismLam
  else
    match ← viewBindI a with
    | none => failDanglingE
    | some (da, ba, ma) =>
      match ← viewBindI b with
      | none => failDanglingE
      | some (db, bb, mb) => do
        let sameDom := da == db
        let t1 ← instantiateListFast coreWalkFuel da fvs 0
        let t2 ← if sameDom then pure t1
                 else instantiateListFast coreWalkFuel db fvs 0
        let dq ← if sameDom then pure true else r.defeq (d + k) t1 t2
        if !dq then pure false
        else do
          let fv ← internFVarE (d + k) t2
          let mm := mode.verifiedChecks && !(ma == mb)
          let m2 := mism || mm
          let ml2 := if mm then ta == ETag.lam else mismLam
          cont ba bb (k + 1) (fvs.push fv) m2 ml2

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — `defeqPeel` at
a successor budget is one level over the rest. -/
theorem defeqPeel_succ_eq (mode : CheckMode) (r : CoreFnsA) (d p : Nat)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (mism ml : Bool) :
    defeqPeel mode r d (p + 1) a b k fvs mism ml =
      peelStep mode r d (p + 1) (defeqPeel mode r d p) a b k fvs mism ml := by
  delta defeqPeel peelStep
  exact rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — and at budget
zero (where the level's own guard sends every pair to the leaf). -/
theorem defeqPeel_zero_eq (mode : CheckMode) (r : CoreFnsA) (d : Nat)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (mism ml : Bool) :
    defeqPeel mode r d 0 a b k fvs mism ml =
      peelStep mode r d 0 (defeqPeelLeaf r d) a b k fvs mism ml := by
  delta defeqPeel peelStep
  exact rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — **THEOREM 1
for the batched descent**: at every budget, `defeqPeel` answers the chain's
continuation at the opened pair (`PeelOK`).  Induction on the budget; one
level is `peel_step_pure` over three stages (the two domain opens, the
domain comparison or its equality short-circuit, the fresh free variable). -/
theorem defeqPeel_spec (hsim : KnotSpec mode env fe fuel) (d : Nat) :
    ∀ (peel : Nat) (s₀ : AState) (a b : EIdx) (k : Nat) (fvs : Array EIdx)
      (ws : List Expr) (mism ml : Bool) (ca cb : Expr),
      CheckOK mode env fe s₀ → denoteE s₀.store a = some ca →
      denoteE s₀.store b = some cb → ExprOps.InstLVec s₀.store fvs ws →
      Expr.WScoped (d + k) (ca.instantiateList ws 0) →
      Expr.WScoped (d + k) (cb.instantiateList ws 0) →
      ⦃fun s => ⌜s = s₀⌝⦄
        defeqPeel mode (coreKnot mode fe id fuel) d peel a b k fvs mism ml
      ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∃ F, PeelOK mode env F (d + k) (ca.instantiateList ws 0)
            (cb.instantiateList ws 0) mism x⌝⦄ := by
  intro peel
  induction peel with
  | zero =>
    intro s₀ a b k fvs ws mism ml ca cb hok ha hb hvec hwa hwb
    rw [defeqPeel_zero_eq]
    unfold peelStep
    split
    · rename_i hab
      exact peel_eq_case s₀ a b (d + k) ws mism ml ca cb hok ha hb hab
    · simp only [decide_true, Bool.true_or, if_true]
      exact defeqPeelLeaf_spec hsim d s₀ a b k fvs ws mism ml ca cb hok ha hb
        hvec hwa hwb
  | succ p ih =>
    intro s₀ a b k fvs ws mism ml ca cb hok ha hb hvec hwa hwb
    rw [defeqPeel_succ_eq]
    unfold peelStep
    dsimp only
    split
    · rename_i hab
      exact peel_eq_case s₀ a b (d + k) ws mism ml ca cb hok ha hb hab
    split
    · exact defeqPeelLeaf_spec hsim d s₀ a b k fvs ws mism ml ca cb hok ha hb
        hvec hwa hwb
    rename_i hguard
    have htag : b.tag = a.tag ∧ ETag.isBind a.tag = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
        Bool.not_eq_eq_eq_not, Bool.not_true, not_or, Decidable.not_not,
        Bool.not_eq_false] at hguard
      exact ⟨hguard.1.2.symm, hguard.2⟩
    obtain ⟨htb, hbind⟩ := htag
    have hwf := hok.state.wf
    -- stage 0: the two binder projections
    refine triple_seq (viewBindI_spec s₀ a) ?_
    rintro ra s1 ⟨hs1, hra⟩
    subst s1 ra
    cases hva : s₀.store.viewBindI a with
    | none => exact triple_failDanglingE
    | some pa =>
    obtain ⟨da, ba, ma⟩ := pa
    dsimp only
    refine triple_seq (viewBindI_spec s₀ b) ?_
    rintro rb s1 ⟨hs1, hrb⟩
    subst s1 rb
    cases hvb : s₀.store.viewBindI b with
    | none => exact triple_failDanglingE
    | some pb =>
    obtain ⟨db, bb, mb⟩ := pb
    dsimp only
    obtain ⟨mA, hmA, _, hviewA⟩ := view_of_viewBindI_wf hwf hbind hva
    obtain ⟨mB, hmB, _, hviewB⟩ :=
      view_of_viewBindI_wf hwf (by rw [htb]; exact hbind) hvb
    obtain ⟨tda, cba, rfl, hda, hba⟩ := denote_bind_inv hwf hviewA ha
    obtain ⟨tdb, cbb, rfl, hdb, hbb⟩ := denote_bind_inv hwf hviewB hb
    rw [htb] at hwb ⊢
    rw [bndE_instantiateList] at hwa hwb ⊢
    rw [bndE_instantiateList]
    obtain ⟨hwA1, hwC1⟩ := wscoped_bndE.mp hwa
    obtain ⟨hwA2, hwC2⟩ := wscoped_bndE.mp hwb
    have hmm : (mode.verifiedChecks && !(ma == mb)) = false →
        (mode.verifiedChecks && !(mA.pw == mB.pw)) = false := by
      intro h
      cases hv : mode.verifiedChecks with
      | false => rfl
      | true =>
        rw [hv] at h
        simp only [Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_false] at h
        have hmab : ma = mb := eq_of_beq h
        subst hmab
        obtain rfl : mA = mB := Option.some.inj (hmA.symm.trans hmB)
        simp
    -- the level's tail, once the second domain `t2` and the verdict `dq` are
    -- in hand: the fresh free variable, then the rest of the telescope
    have tail : ∀ (t2 : EIdx) (dq : Bool) (s4 : AState),
        CheckOK mode env fe s4 → Ext s₀.store s4.store → s4.pins = s₀.pins →
        denoteE s4.store t2 = some (tdb.instantiateList ws 0) →
        (∃ F1, ∀ F, F1 ≤ F → ConLeche.isDefEqCore mode env F (d + k)
          (tda.instantiateList ws 0) (tdb.instantiateList ws 0) = .ok dq) →
        ⦃fun s => ⌜s = s4⌝⦄
          (if (!dq) = true then pure false
           else do
             let fv ← internFVarE (d + k) t2
             defeqPeel mode (coreKnot mode fe id fuel) d p ba bb (k + 1)
               (fvs.push fv) (mism || (mode.verifiedChecks && !(ma == mb)))
               (if (mode.verifiedChecks && !(ma == mb)) = true then
                  a.tag == ETag.lam else ml))
        ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
            s'.pins = s₀.pins ∧
            ∃ F, PeelOK mode env F (d + k)
              (bndE (a.tag == ETag.lam) (tda.instantiateList ws 0)
                (cba.instantiateList ws 1) mA)
              (bndE (a.tag == ETag.lam) (tdb.instantiateList ws 0)
                (cbb.instantiateList ws 1) mB) mism x⌝⦄ := by
      intro t2 dq s4 hok4 hx04 hp04 ht2 ⟨F1, hF1⟩
      cases dq with
      | false =>
        simp only [Bool.not_false, if_true]
        mvcgen
        bridge_peel; subst_vars
        exact ⟨hok4, hx04, hp04, peel_step_pure (F2 := 0)
          (mm := mode.verifiedChecks && !(ma == mb)) (a.tag == ETag.lam) hF1
          (fun _ => rfl) (fun h => absurd h (by simp)) hmm⟩
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, if_false]
        -- stage 4: the fresh free variable at the second opened domain
        refine triple_seq (internE_ok_spec s4 (.fvar (d + k) t2) hok4
          (viewOK_fvar (by rw [ht2]; rfl))) ?_
        rintro fv s5 ⟨hok5, hx5, hp5, hfv⟩
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
          (.fvar (d + k) (tdb.instantiateList ws 0) :: ws) _ _ cba cbb hok5
          (denote_ext hba hx05) (denote_ext hbb hx05) hvec5 ?_ ?_) ?_
        · rw [peel_open_body]; exact Expr.WScoped.instantiate1 hwA2 0 hwC1
        · rw [peel_open_body]; exact Expr.WScoped.instantiate1 hwA2 0 hwC2
        rintro x s6 ⟨hok6, hx6, hp6, F2, hF2⟩
        refine ⟨hok6, hx05.trans hx6, hp6.trans (hp5.trans hp04), ?_⟩
        rw [peel_open_body, peel_open_body] at hF2
        exact peel_step_pure (a.tag == ETag.lam) hF1
          (fun h => absurd h (by simp)) (fun _ => hF2) hmm
    -- stage 1: the first domain, opened against the whole vector
    refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ da fvs 0
      ws hok.state hvec (by rw [hda]; rfl)) ?_
    rintro t1 s2 ⟨hst2, hx2, _, hc2, hp2, _, hrel2⟩
    have hok2 := hok.mono hst2 hx2 hc2 hp2
    have ht1 : denoteE s2.store t1 = some (tda.instantiateList ws 0) :=
      hrel2 _ hda
    by_cases hsame : (da == db) = true
    · -- stages 2–3, the equality short-circuit: one open, no knot call
      have hsd : da = db := eq_of_beq hsame
      subst hsd
      obtain rfl : tda = tdb := Option.some.inj (hda.symm.trans hdb)
      simp only [hsame, if_true, pure_bind]
      exact tail t1 true s2 hok2 hx2 hp2 ht1 ⟨1, fun F hF => by
        obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
        exact isDefEqCore_refl_one⟩
    · have hsame' : (da == db) = false := by simpa using hsame
      simp only [hsame', Bool.false_eq_true, if_false]
      -- stage 2: the second domain
      have hdb2 := denote_ext hdb hx2
      refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s2 db
        fvs 0 ws hst2 (hvec.ext hx2) (by rw [hdb2]; rfl)) ?_
      rintro t2 s3 ⟨hst3, hx3, _, hc3, hp3, _, hrel3⟩
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

/-- con-leche: ConLeche/Kernel/Core.lean:1636-1662 defeqStep — **THEOREM 1
for `defeqBinders`**, the statement `Arms/Defeq.lean`'s `defeqPeel_chain`
publishes (and is proved by): the first binder compared as the chain compares
it, then `defeqPeel_spec` at budget `peelFuel` from depth `d + 1`, and one
more `peel_step_pure` to fold the first level in.  `henv` is carried for the
published statement and not spent. -/
theorem defeqBinders_spec {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty1 body1 ty2 body2 : EIdx)
    (m1 m2 : BinderMeta) (isLam : Bool) (t1 b1 t2 b2 : Expr)
    (hok : CheckOK mode env fe s₀)
    (ht1 : denoteE s₀.store ty1 = some t1)
    (hb1 : denoteE s₀.store body1 = some b1)
    (ht2 : denoteE s₀.store ty2 = some t2)
    (hb2 : denoteE s₀.store body2 = some b2)
    (hwa : Expr.WScoped d (if isLam then .lam t1 b1 m1 else .forallE t1 b1 m1))
    (hwb : Expr.WScoped d
      (if isLam then .lam t2 b2 m2 else .forallE t2 b2 m2)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      defeqBinders mode (coreKnot mode fe id fuel) d ty1 body1 m1 ty2 body2 m2
        isLam
    ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimV (ConLeche.isDefEqCore mode env) d
          (if isLam then .lam t1 b1 m1 else .forallE t1 b1 m1)
          (if isLam then .lam t2 b2 m2 else .forallE t2 b2 m2) x⌝⦄ := by
  obtain ⟨hwt1, hwb1⟩ := wscoped_bndE.mp
    (show Expr.WScoped d (bndE isLam t1 b1 m1) from hwa)
  obtain ⟨hwt2, hwb2⟩ := wscoped_bndE.mp
    (show Expr.WScoped d (bndE isLam t2 b2 m2) from hwb)
  have fin : ∀ x, (∃ F, PeelOK mode env F d (bndE isLam t1 b1 m1)
      (bndE isLam t2 b2 m2) false x) →
      SimV (ConLeche.isDefEqCore mode env) d
        (if isLam then .lam t1 b1 m1 else .forallE t1 b1 m1)
        (if isLam then .lam t2 b2 m2 else .forallE t2 b2 m2) x := by
    rintro x ⟨F, (⟨h, rfl⟩ | ⟨h, _, rfl⟩)⟩
    · exact ⟨F, h⟩
    · exact ⟨F, h⟩
  unfold defeqBinders
  -- stage 1: the first domains, through the knot
  refine triple_seq (hsim.defeq s₀ d ty1 ty2 t1 t2 hok ht1 ht2 hwt1 hwt2) ?_
  rintro v s1 ⟨hok1, hx1, hp1, F1, hF1⟩
  have hdq : ∀ F, F1 ≤ F → ConLeche.isDefEqCore mode env F d t1 t2 = .ok v :=
    fun F hF => ConLeche.isDefEqCore_mono hF hF1
  cases v with
  | false =>
    simp only [Bool.not_false, if_true]
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok1, hx1, hp1, fin _ (peel_step_pure (F2 := 0) (mism := false)
      (mm := mode.verifiedChecks && !(m1.pw == m2.pw)) isLam hdq
      (fun _ => rfl) (fun h => absurd h (by simp)) id)⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    -- stage 2: the first free variable, at the second domain
    have ht2' := denote_ext ht2 hx1
    refine triple_seq (internE_ok_spec s1 (.fvar d ty2) hok1
      (viewOK_fvar (by rw [ht2']; rfl))) ?_
    rintro fv s2 ⟨hok2, hx2, hp2, hfv⟩
    have hfv' : denoteE s2.store fv = some (.fvar d t2) := by
      rw [hfv]; simp [denoteEView, denote_ext ht2' hx2]
    have hx02 : Ext s₀.store s2.store := hx1.trans hx2
    have hvec : ExprOps.InstLVec s2.store #[fv] [.fvar d t2] := by
      unfold ExprOps.InstLVec
      simpa using ExprOps.denoteEList_snoc hfv' [] [] rfl
    -- stage 3: the rest of the two telescopes, batched
    refine triple_mono (defeqPeel_spec hsim d peelFuel s2 body1 body2 1 #[fv]
      [.fvar d t2] _ _ b1 b2 hok2 (denote_ext hb1 hx02) (denote_ext hb2 hx02)
      hvec ?_ ?_) ?_
    · rw [peel_open_body, Expr.instantiateList_nil]
      exact Expr.WScoped.instantiate1 hwt2 0 hwb1
    · rw [peel_open_body, Expr.instantiateList_nil]
      exact Expr.WScoped.instantiate1 hwt2 0 hwb2
    rintro x s3 ⟨hok3, hx3, hp3, F2, hF2⟩
    rw [peel_open_body, peel_open_body, Expr.instantiateList_nil,
      Expr.instantiateList_nil] at hF2
    refine ⟨hok3, hx02.trans hx3, hp3.trans (hp2.trans hp1), fin _ ?_⟩
    exact peel_step_pure isLam hdq (fun h => absurd h (by simp))
      (fun _ => by rw [Bool.false_or]; exact hF2) id

/-! `sorryAx` expected nowhere: the module is closed. -/

#print axioms isDefEqCore_refl
#print axioms isDefEqCore_bnd
#print axioms peel_step_pure
#print axioms defeqPeelLeaf_spec
#print axioms defeqPeel_succ_eq
#print axioms defeqPeel_zero_eq
#print axioms defeqPeel_spec
#print axioms defeqBinders_spec

end ConRon.Bridge.Core
