/-
# Experiment A, subject 2 — the `app`-of-`lam` β arm of `whnfCoreBody`

`ConLeche/Kernel/Core.lean:1935`, the `.app` clause, with the knot record
abstracted as a hypothesis exactly as con-leche's body takes `r : CoreFns m`.
This is the subject that tests whether the `@[spec]`/`mvcgen` idiom composes
through a *record of hypotheses* rather than through global lemmas.

**Closed in round 2.**  `mvcgen` leaves **28** verification conditions;
**25** of them fall to the same uniform closer subject 1 uses, and the three
that do not are the three exits of the *pure* function — the β gate fires,
the argument certificate succeeds, the certificate fails.  That is the
round-2 finding the brief asks for: **a body arm whose recursive calls go
through the abstract record needs one rule beyond the seven, and it is about
the pure side, not the monadic side** — *one step lemma per clause of the
pure function* (`PureAt.beta_step`, `.defeq_step`, `.stuck_step` below),
which is §4.1's group 7 read at the `whnfCore` grade.  The record of
hypotheses itself costs nothing: `hsim.whnfCore`, `hsim.inferIO` and
`hsim.defeq` go into `mvcgen`'s list exactly as subject 3's single `hf` did.

Two traps, both worth carrying into P2c:

* `mvcgen [f, hsim.whnfCore]` does not parse as a spec — bind the projection
  with `have` first;
* `instantiate1Top_spec` takes the substituted term `ve` as an explicit
  argument, so passing it raw leaves `mvcgen` a goal `⊢ Expr` and a side
  goal with a metavariable in it (round 1's rule 4, from the other side).
  Specialise it at the arm's own `ea` with a `have` before `mvcgen`.
-/
import ConRon.Arena.Spike.ExpA

namespace ConRon.Arena.Spike

open ConLeche Std.Do

set_option mvcgen.warning false
set_option maxHeartbeats 4000000

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the pure side of a
`whnfCore`-grade step, at a *fixed* pure record (the knot is not tied here,
so there is no `∃ F`; that appears one level up, in subject 3). -/
def PureAt (op : Expr → CheckM Expr) (st : EStore) (c : EIdx) (st' : EStore)
    (r : EIdx) : Prop :=
  ∀ e, denoteE st c = some e → ∃ e', denoteE st' r = some e' ∧ op e = .ok e'

/-- con-leche: ConLeche/Verify/SimIKnot.lean:28 SSimI — the knot record's
simulation hypothesis, one clause per slot `whnfCoreAppArm` calls. -/
structure CoreSimA (rp : CoreFns CheckM) (ra : CoreFnsA) : Prop where
  whnfCore : ∀ (s₀ : AState) (dep : Nat) (c : EIdx), StateOK s₀ →
    (denoteE s₀.store c).isSome = true → s₀.inst1C = ∅ →
    ⦃fun s => ⌜s = s₀⌝⦄ ra.whnfCore dep c
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
        PureAt (rp.whnfCore dep) s₀.store c s'.store r⌝⦄
  inferIO : ∀ (s₀ : AState) (dep : Nat) (c : EIdx), StateOK s₀ →
    (denoteE s₀.store c).isSome = true → s₀.inst1C = ∅ →
    ⦃fun s => ⌜s = s₀⌝⦄ ra.inferIO dep c
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
        PureAt (rp.inferIO dep) s₀.store c s'.store r⌝⦄
  defeq : ∀ (s₀ : AState) (dep : Nat) (c₁ c₂ : EIdx), StateOK s₀ →
    (denoteE s₀.store c₁).isSome = true → (denoteE s₀.store c₂).isSome = true →
    s₀.inst1C = ∅ →
    ⦃fun s => ⌜s = s₀⌝⦄ ra.defeq dep c₁ c₂
    ⦃⇓? b s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
        ∀ e₁ e₂, denoteE s₀.store c₁ = some e₁ → denoteE s₀.store c₂ = some e₂ →
          rp.defeq dep e₁ e₂ = .ok b⌝⦄

/-! ## The pure side, computed

`whnfCoreBody`'s `.app` clause reduced in `Except`: three lemmas, one per
exit.  This is the work subject 3 did not have, because subject 3's pure
side is *assumed* (`∃ F, ∀ d, pw F d a = .ok b`) rather than computed. -/

theorem ok_bind_ex {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

theorem wcb_app_beta {mode : CheckMode} {rp : CoreFns CheckM} {env : Env} {dep : Nat}
    {ef ea ty body : Expr} {mb : BinderMeta} {e' : Expr}
    (h1 : rp.whnfCore dep ef = .ok (.lam ty body mb))
    (hg : betaGateFires mode mb.pw = true)
    (h2 : rp.whnfCore dep (body.instantiate1 ea) = .ok e') :
    whnfCoreBody mode rp env dep (.app ef ea) = .ok e' := by
  simp [whnfCoreBody, ok_bind_ex, h1, hg, h2]

theorem wcb_app_defeq {mode : CheckMode} {rp : CoreFns CheckM} {env : Env} {dep : Nat}
    {ef ea ty body ta : Expr} {mb : BinderMeta} {e' : Expr}
    (h1 : rp.whnfCore dep ef = .ok (.lam ty body mb))
    (hg : betaGateFires mode mb.pw = false)
    (hi : rp.inferIO dep ea = .ok ta)
    (hd : rp.defeq dep ta ty = .ok true)
    (h2 : rp.whnfCore dep (body.instantiate1 ea) = .ok e') :
    whnfCoreBody mode rp env dep (.app ef ea) = .ok e' := by
  simp [whnfCoreBody, ok_bind_ex, h1, hg, hi, hd, h2]

theorem wcb_app_stuck {mode : CheckMode} {rp : CoreFns CheckM} {env : Env} {dep : Nat}
    {ef ea ty body ta : Expr} {mb : BinderMeta}
    (h1 : rp.whnfCore dep ef = .ok (.lam ty body mb))
    (hg : betaGateFires mode mb.pw = false)
    (hi : rp.inferIO dep ea = .ok ta)
    (hd : rp.defeq dep ta ty = .ok false) :
    whnfCoreBody mode rp env dep (.app ef ea) = .ok (.app (.lam ty body mb) ea) := by
  simp [whnfCoreBody, ok_bind_ex, h1, hg, hi, hd]
  rfl

@[grind →] theorem PureAt.apply {op : Expr → CheckM Expr} {st st' : EStore} {c r : EIdx}
    {e : Expr} (h : PureAt op st c st' r) (he : denoteE st c = some e) :
    ∃ e', denoteE st' r = some e' ∧ op e = .ok e' := h e he

@[grind →] theorem PureAt.isSome {op : Expr → CheckM Expr} {st st' : EStore} {c r : EIdx}
    (h : PureAt op st c st' r) (hs : (denoteE st c).isSome = true) :
    (denoteE st' r).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨e', he', _⟩ := h e he
  rw [he']; rfl

theorem PureAt.mk {op : Expr → CheckM Expr} {st st' : EStore} {c r : EIdx}
    {e e' : Expr} (hc : denoteE st c = some e) (hr : denoteE st' r = some e')
    (hop : op e = .ok e') : PureAt op st c st' r := by
  intro x hx
  rw [hc] at hx
  obtain rfl := Option.some.inj hx
  exact ⟨e', hr, hop⟩


/-! ## The pure side of the arm, as three step lemmas

The eighth rule the body arm needs: **one step lemma per clause of the
*pure* function**, not per constructor of the subject.  `whnfCoreBody`'s
`.app` arm has three exits — the gate fires, the certificate succeeds, the
certificate fails — and each one is a separate `PureAt` introduction that
`grind` fires in a single ematch. -/

theorem PureAt.beta_step {mode : CheckMode} {rp : CoreFns CheckM} {env : Env}
    {dep : Nat} {s3 s2 s1 s : EStore} {hh f r2 ty body r1 r : EIdx}
    {mb : BinderMeta} {ea ef : Expr}
    (hwf2 : StoreWF s2)
    (hehh : denoteE s3 hh = some (.app ef ea))
    (hef : denoteE s3 f = some ef)
    (hpf : PureAt (rp.whnfCore dep) s3 f s2 r2)
    (hvw : s2.view r2 = some (.lam ty body mb))
    (hg : betaGateFires mode mb.pw = true)
    (hins : Inst1At ea 0 s2 body s1 r1)
    (hpb : PureAt (rp.whnfCore dep) s1 r1 s r) :
    PureAt (whnfCoreBody mode rp env dep) s3 hh s r := by
  intro e he
  rw [hehh] at he
  obtain rfl := Option.some.inj he
  obtain ⟨ef', hef', hop1⟩ := hpf ef hef
  obtain ⟨et, eb, rfl, het, heb⟩ := denote_lam_inv hwf2 hvw hef'
  have hr1 : denoteE s1 r1 = some (eb.instantiate1 ea 0) := hins eb heb
  obtain ⟨e'', he'', hop2⟩ := hpb _ hr1
  exact ⟨e'', he'', wcb_app_beta hop1 hg hop2⟩

theorem PureAt.defeq_step {mode : CheckMode} {rp : CoreFns CheckM} {env : Env}
    {dep : Nat} {s4 s3 s2 sd s1 s : EStore} {hh f a r3 ty body r2 r1 r : EIdx}
    {mb : BinderMeta} {ea ef : Expr}
    (hehh : denoteE s4 hh = some (.app ef ea))
    (hef : denoteE s4 f = some ef) (hea : denoteE s4 a = some ea)
    (hpf : PureAt (rp.whnfCore dep) s4 f s3 r3)
    (hvw : s3.view r3 = some (.lam ty body mb))
    (hg : ¬ betaGateFires mode mb.pw = true)
    (hwf3 : StoreWF s3)
    (hx43 : Ext s4 s3)
    (hpi : PureAt (rp.inferIO dep) s3 a s2 r2)
    (hdq : ∀ e₁ e₂, denoteE s2 r2 = some e₁ → denoteE s2 ty = some e₂ →
      rp.defeq dep e₁ e₂ = .ok true)
    (hx32 : Ext s3 s2) (hx2d : Ext s2 sd)
    (hins : Inst1At ea 0 sd body s1 r1)
    (hpb : PureAt (rp.whnfCore dep) s1 r1 s r) :
    PureAt (whnfCoreBody mode rp env dep) s4 hh s r := by
  intro e he
  rw [hehh] at he
  obtain rfl := Option.some.inj he
  obtain ⟨ef', hef', hop1⟩ := hpf ef hef
  obtain ⟨et, eb, rfl, het, heb⟩ := denote_lam_inv hwf3 hvw hef'
  obtain ⟨eta, heta, hop2⟩ := hpi ea (denote_ext hea hx43)
  have hd := hdq eta et heta (denote_ext het hx32)
  have hr1 : denoteE s1 r1 = some (eb.instantiate1 ea 0) :=
    hins eb (denote_ext (denote_ext heb hx32) hx2d)
  obtain ⟨e'', he'', hop3⟩ := hpb _ hr1
  exact ⟨e'', he'', wcb_app_defeq hop1 (by simpa using hg) hop2 hd hop3⟩

theorem PureAt.stuck_step {mode : CheckMode} {rp : CoreFns CheckM} {env : Env}
    {dep : Nat} {s4 s3 s2 s : EStore} {hh f a r3 ty body r2 r : EIdx}
    {mb : BinderMeta} {ea ef : Expr}
    (hwf4 : StoreWF s4)
    (hehh : denoteE s4 hh = some (.app ef ea))
    (hef : denoteE s4 f = some ef) (hea : denoteE s4 a = some ea)
    (hpf : PureAt (rp.whnfCore dep) s4 f s3 r3)
    (hvw : s3.view r3 = some (.lam ty body mb))
    (hg : ¬ betaGateFires mode mb.pw = true)
    (hwf3 : StoreWF s3)
    (hx43 : Ext s4 s3)
    (hpi : PureAt (rp.inferIO dep) s3 a s2 r2)
    (hdq : ∀ e₁ e₂, denoteE s2 r2 = some e₁ → denoteE s2 ty = some e₂ →
      rp.defeq dep e₁ e₂ = .ok false)
    (hx32 : Ext s3 s2) (hx2s : Ext s2 s)
    (hr : denoteE s r = denoteEView s (.app r3 a)) :
    PureAt (whnfCoreBody mode rp env dep) s4 hh s r := by
  intro e he
  rw [hehh] at he
  obtain rfl := Option.some.inj he
  obtain ⟨ef', hef', hop1⟩ := hpf ef hef
  obtain ⟨et, eb, rfl, het, heb⟩ := denote_lam_inv hwf3 hvw hef'
  obtain ⟨eta, heta, hop2⟩ := hpi ea (denote_ext hea hx43)
  have hd := hdq eta et heta (denote_ext het hx32)
  refine ⟨.app (.lam et eb mb) ea, ?_, wcb_app_stuck hop1 (by simpa using hg) hop2 hd⟩
  rw [hr, denoteEView, denote_ext (denote_ext hef' hx32) hx2s,
    denote_ext (denote_ext (denote_ext hea hx43) hx32) hx2s]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1941 whnfCoreBody (the `.app` arm) —
**Theorem 1 for subject 2**, closed. -/
theorem whnfCoreAppArm_spec (mode : CheckMode) (env : Env) (rp : CoreFns CheckM)
    (ra : CoreFnsA) (hsim : CoreSimA rp ra) (fuel : Nat) (s₀ : AState)
    (dep : Nat) (hh f a : EIdx) (hok : StateOK s₀) (hempty : s₀.inst1C = ∅)
    (hview : s₀.store.view hh = some (.app f a))
    (hden : (denoteE s₀.store hh).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ whnfCoreAppArm mode ra fuel dep f a
    ⦃⇓? h' s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
        PureAt (whnfCoreBody mode rp env dep) s₀.store hh s'.store h'⌝⦄ := by
  obtain ⟨hsf, hsa⟩ := isSome_app hok.wf hview hden
  obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp hsa
  obtain ⟨ef, hef⟩ := Option.isSome_iff_exists.mp hsf
  have hehh : denoteE s₀.store hh = some (.app ef ea) := by
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
    obtain ⟨x, y, rfl, hx, hy⟩ := denote_app_inv hok.wf hview he
    rw [hx] at hef; rw [hy] at hea
    rw [he, Option.some.inj hef, Option.some.inj hea]
  have hw := hsim.whnfCore
  have hio := hsim.inferIO
  have hq := hsim.defeq
  have hinst : ∀ (fl : Nat) (s : AState) (c : EIdx), StateOK s → Ext s₀.store s.store →
      (denoteE s.store c).isSome = true →
      ⦃fun x => ⌜x = s⌝⦄ instantiate1Top a fl c
      ⦃⇓? h' s' => ⌜StateOK s' ∧ Ext s.store s'.store ∧ s'.inst1C = ∅ ∧
          Inst1At ea 0 s.store c s'.store h'⌝⦄ :=
    fun fl s c hok2 hx hd => instantiate1Top_spec a ea fl s c hok2 (denote_ext hea hx) hd
  mvcgen [whnfCoreAppArm, hw, hio, hq, hinst]
  all_goals
    (first
      | (intro hf; exact False.elim hf)
      | (spike_peel
         subst_vars
         grind (instances := 8000) [StateOK, Ext.trans, Ext.refl, viewOK_app,
           Option.isSome_iff_exists, PureAt.mk, wcb_app_beta, wcb_app_defeq,
           wcb_app_stuck, denote_eq_lam, Inst1At.apply, EStore.derived_exact,
           PureAt.beta_step, PureAt.defeq_step, PureAt.stuck_step])
      | (spike_peel
         subst_vars
         intro hOK hX hE hP
         refine ⟨hOK, ?_, hE, ?_⟩
         · grind (instances := 8000) [Ext.trans, Ext.refl]
         · grind (instances := 20000) [PureAt.beta_step, PureAt.defeq_step,
             PureAt.stuck_step, StateOK, Ext.trans, Ext.refl, denote_ext]))

end ConRon.Arena.Spike
