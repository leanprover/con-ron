/-
# Experiment A at scale — subject 1, one spec theorem per constructor arm

Round 1 proved subject 1 (`instantiate1A_spec`, `ExpA.lean`) in thirteen lines
of proof script, and the file took **185 s** to elaborate.  At the ~700
functions P2b–P2d will carry that is 36 h per build, which is not a build.
This module is the same theorem at **11 s**, and the recipe is four changes,
each measured in `_tmp/t97r2/perf/NOTES.md`:

1. **`grind`'s hint set must not contain the `Inst1At` transport closure.**
   `Inst1At.ext`, `Inst1At.of_ext` and `Inst1At.retarget` are tagged
   `@[grind →]` in `Specs.lean`; together they close `Inst1At` under `Ext` in
   both directions, so every intermediate store multiplies every known answer.
   Measured on *one* `app` verification condition: `Inst1At.apply` 252
   instantiations, `denote_ext` 155, `.ext` 144, `.of_ext` 144, `.retarget`
   144 — and the 1000-instance budget exhausted.  The `attribute [-grind]`
   below is the single highest-value line in this file: it takes the `app` arm
   from 15.4 s to 8.4 s on its own.
2. **One `def` per constructor arm, one spec theorem per arm.**  Each arm's
   `grind` then sees that arm's fifteen verification conditions and nothing
   else, and the dispatcher's `mvcgen` never looks inside an arm.
3. **The two *structural* verification conditions of every arm are applied by
   hand.**  They are the memo insert's `Inst1At` and the arm's postcondition,
   and both are exactly one `Inst1At.*_step` lemma — the lemmas round 1 built
   for the purpose.  `grind` spends thousands of E-matching instances
   rediscovering them; `exact` spends none.
4. **The arm specs are NOT tagged `@[spec]`.**  Registering the attribute costs
   2–7 s *per theorem* (`attribute application` in the profile); passing the
   six of them to the dispatcher's one `mvcgen` costs 8.4 s once.  Measured:
   22.3 s tagged against 11.3 s passed.

What is NOT the cost: `mvcgen`'s own verification-condition generation.
`ExpA.lean` with every verification condition closed by `sorry` elaborates in
**3.7 s** of 185 s — 2 %.  The 185 s was `grind`, and 41.6 s of it was a
single goal paying for the 8000-instance fallback that round 1's closer runs
after the first `grind` fails.

The theorem proved here is `instantiate1A_spec`'s statement verbatim, against
a twin (`instantiate1B`) that is `instantiate1A` with its arms named.  The
recipe therefore has one prerequisite for P2b–P2d: **(B) must be written with
one `def` per constructor arm**, which is a style rule, not a proof trick.
-/
import ConRon.Arena.Spike.Specs
import ConRon.Arena.Spike.Peel

namespace ConRon.Arena.Spike.Fast

open ConLeche Std.Do ConRon.Arena.Spike

set_option mvcgen.warning false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/- **Attribute hygiene** (change 1).  `Inst1At.ext`, `.of_ext` and `.retarget`
are the transitive closure of the answer relation under arena extension.  The
`_step` lemmas already carry the whole chain, so the three are redundant here
*and* they are what exhausts the E-matching budget.

Measured, this file with and without this one line: **11.5 s against 70 s**,
and without it one verification condition of the `proj` arm does not close at
all.  (`attribute [local -grind]` is not syntax; the erasure is therefore
file-scoped by position — a module that imports this one and wants the
transports back must re-tag them.) -/
attribute [-grind] Inst1At.ext Inst1At.of_ext Inst1At.retarget

/-- **The small closer.**  One `grind` with a curated list and a budget of
1000 E-matching instances; a second stage, for the handful of verification
conditions that genuinely have to move an answer along the extension chain,
puts the transports back and raises the budget to 4000.  Round 1's closer ran
the wide list first and a *wider* one second; both stages here are narrower
than round 1's first. -/
macro "vcs" : tactic => `(tactic| first
  | (intro hf; exact False.elim hf)
  | (spike_peel
     subst_vars
     try unfold Inst1At
     grind (instances := 1000) [StateOK, Inst1MemoA.mono, Inst1MemoA.insert,
       Ext.trans, Ext.refl, viewOK_bvar, viewOK_app, viewOK_lam, viewOK_forallE,
       viewOK_letE, viewOK_proj, denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
       Expr.instantiate1, Option.isSome_iff_exists, Option.map_eq_some_iff])
  | (spike_peel
     subst_vars
     try unfold Inst1At
     grind (instances := 4000) [StateOK, Inst1MemoA.mono, Inst1MemoA.insert,
       Ext.trans, Ext.refl, Inst1At.ext, Inst1At.of_ext,
       viewOK_bvar, viewOK_app, viewOK_lam, viewOK_forallE,
       viewOK_letE, viewOK_proj, denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
       Expr.instantiate1, Option.isSome_iff_exists, Option.map_eq_some_iff]))

/-! ## The twin, refactored: one `def` per constructor arm

`instantiate1B` is `instantiate1A` (`Twins.lean`) clause for clause; the only
change is that each branching arm is a named `def`.  The substituted handle
`v` is threaded into every arm even where the arm does not read it: without it
`mvcgen` has nothing in the *program* to pin the arm spec's `v` against, and
it unifies `v` with whichever handle comes to hand (measured: the app arm's
second child).  In the real (B) this is a section variable and the threading
is free. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33 instantiate1 — the `bvar` arm. -/
def inst1Bvar (v h : EIdx) (d i : Nat) : AM EIdx :=
  if i = d then pure v
  else if i > d then internE (.bvar (i - 1))
  else pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the `app` arm. -/
def inst1App (v : EIdx) (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (f a : EIdx) : AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none => do
    let f' ← rec f d
    let a' ← rec a d
    let r ← internE (.app f' a')
    inst1Set (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the `lam` arm. -/
def inst1Lam (v : EIdx) (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let b' ← rec body (d + 1)
    let r ← internE (.lam t b' m)
    inst1Set (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the `forallE`
arm. -/
def inst1Forall (v : EIdx) (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let b' ← rec body (d + 1)
    let r ← internE (.forallE t b' m)
    inst1Set (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the `letE` arm. -/
def inst1Let (v : EIdx) (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty val body : EIdx) : AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let w ← rec val d
    let b' ← rec body (d + 1)
    let r ← internE (.letE t w b')
    inst1Set (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the `proj` arm. -/
def inst1Proj (v : EIdx) (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (n : NIdx) (i : Nat) (sub : EIdx) : AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none => do
    let u ← rec sub d
    let r ← internE (.proj n i u)
    inst1Set (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33 instantiate1 — the dispatcher:
the derived-word cutoff, the view, and one call per arm. -/
def instantiate1B (v : EIdx) : Nat → EIdx → Nat → AM EIdx
  | 0, _, _ => fail (.internal "fuel exhausted: instantiate1")
  | fuel + 1, h, d => do
    let der ← derivedE h
    let b := (bvarOfData der).toNat
    if b < satRange && b ≤ d then
      pure h
    else
      match ← view h with
      | .bvar i => inst1Bvar v h d i
      | .fvar _ _ => pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .app f a => inst1App v (instantiate1B v fuel) h d f a
      | .lam ty body m => inst1Lam v (instantiate1B v fuel) h d ty body m
      | .forallE ty body m => inst1Forall v (instantiate1B v fuel) h d ty body m
      | .letE ty val body => inst1Let v (instantiate1B v fuel) h d ty val body
      | .proj n i sub => inst1Proj v (instantiate1B v fuel) h d n i sub

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of the recursion, as a one-field record so that the arm specs can
take it as a hypothesis and the dispatcher can discharge it with the induction
hypothesis. -/
structure Inst1Spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (dd : Nat), StateOK s₁ → Inst1MemoA ve s₁ →
    denoteE s₁.store v = some ve → (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        Inst1At ve dd s₁.store c s'.store r⌝⦄

/-! ## One spec theorem per arm

Each arm is proved on its own, so every `grind` sees one arm's verification
conditions.  Two moves carry all six:

* the *structural* verification conditions — the memo insert's `Inst1At` and
  the arm's postcondition — are closed by the matching `_step` lemma, applied
  by hand;
* everything else goes to the small closer above.

The `(by assumption)` arguments are the extension chain and the children's
answers: `mvcgen` produces them in the exact shape `Inst1At.*_step` asks for,
which is what round 1's `§4.1` group 7 was built to guarantee. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33 instantiate1 — the `bvar` arm. -/
theorem inst1Bvar_spec (v : EIdx) (ve : Expr) (s₀ : AState) (h : EIdx)
    (d i : Nat) (hok : StateOK s₀) (hm : Inst1MemoA ve s₀)
    (hv : denoteE s₀.store v = some ve)
    (hview : s₀.store.view h = some (.bvar i))
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Bvar v h d i
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₀.store s'.store ∧
        Inst1At ve d s₀.store h s'.store r⌝⦄ := by
  mvcgen [inst1Bvar]
  all_goals vcs

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the `app` arm. -/
theorem inst1App_spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx)
    (hrec : Inst1Spec v ve rec) (s₀ : AState) (h : EIdx) (d : Nat) (f a : EIdx)
    (hok : StateOK s₀) (hm : Inst1MemoA ve s₀) (hv : denoteE s₀.store v = some ve)
    (hview : s₀.store.view h = some (.app f a))
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1App v rec h d f a
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₀.store s'.store ∧
        Inst1At ve d s₀.store h s'.store r⌝⦄ := by
  have hr := hrec.run
  mvcgen [inst1App, hr]
  case vc15 =>
    spike_peel
    subst_vars
    refine Inst1At.retarget ?_ ?_ hden
    · exact Inst1At.app_step hok.wf hview (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption)
    · grind only [Ext.trans]
  case vc16 =>
    spike_peel
    subst_vars
    grind only [Inst1At.app_step, Ext.trans, StateOK, StateOK.mk]
  all_goals vcs

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the `lam` arm. -/
theorem inst1Lam_spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx)
    (hrec : Inst1Spec v ve rec) (s₀ : AState) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : BinderMeta)
    (hok : StateOK s₀) (hm : Inst1MemoA ve s₀) (hv : denoteE s₀.store v = some ve)
    (hview : s₀.store.view h = some (.lam ty body m))
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Lam v rec h d ty body m
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₀.store s'.store ∧
        Inst1At ve d s₀.store h s'.store r⌝⦄ := by
  have hr := hrec.run
  mvcgen [inst1Lam, hr]
  case vc15 =>
    spike_peel
    subst_vars
    refine Inst1At.retarget ?_ ?_ hden
    · exact Inst1At.lam_step hok.wf hview (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption)
    · grind only [Ext.trans]
  case vc16 =>
    spike_peel
    subst_vars
    grind only [Inst1At.lam_step, Ext.trans, StateOK, StateOK.mk]
  all_goals vcs

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the `forallE`
arm. -/
theorem inst1Forall_spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx)
    (hrec : Inst1Spec v ve rec) (s₀ : AState) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : BinderMeta)
    (hok : StateOK s₀) (hm : Inst1MemoA ve s₀) (hv : denoteE s₀.store v = some ve)
    (hview : s₀.store.view h = some (.forallE ty body m))
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Forall v rec h d ty body m
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₀.store s'.store ∧
        Inst1At ve d s₀.store h s'.store r⌝⦄ := by
  have hr := hrec.run
  mvcgen [inst1Forall, hr]
  case vc15 =>
    spike_peel
    subst_vars
    refine Inst1At.retarget ?_ ?_ hden
    · exact Inst1At.forallE_step hok.wf hview (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption)
    · grind only [Ext.trans]
  case vc16 =>
    spike_peel
    subst_vars
    grind only [Inst1At.forallE_step, Ext.trans, StateOK, StateOK.mk]
  all_goals vcs

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the `letE` arm,
the widest one: three children, four intermediate stores. -/
theorem inst1Let_spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx)
    (hrec : Inst1Spec v ve rec) (s₀ : AState) (h : EIdx) (d : Nat)
    (ty val body : EIdx)
    (hok : StateOK s₀) (hm : Inst1MemoA ve s₀) (hv : denoteE s₀.store v = some ve)
    (hview : s₀.store.view h = some (.letE ty val body))
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Let v rec h d ty val body
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₀.store s'.store ∧
        Inst1At ve d s₀.store h s'.store r⌝⦄ := by
  have hr := hrec.run
  mvcgen [inst1Let, hr]
  case vc19 =>
    spike_peel
    subst_vars
    refine Inst1At.retarget ?_ ?_ hden
    · exact Inst1At.letE_step hok.wf hview (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption)
    · grind only [Ext.trans]
  case vc20 =>
    spike_peel
    subst_vars
    grind only [Inst1At.letE_step, Ext.trans, StateOK, StateOK.mk]
  all_goals vcs

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the `proj` arm.
The one arm whose `_step` lemma needs a fact about the *name* store, so the
inversion is taken by hand inside the two structural cases (taken before
`mvcgen`, it hands `mvcgen` a second `Expr` to unify `ve` against, and it
picks the wrong one — measured). -/
theorem inst1Proj_spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx)
    (hrec : Inst1Spec v ve rec) (s₀ : AState) (h : EIdx) (d : Nat) (n : NIdx)
    (i : Nat) (sub : EIdx)
    (hok : StateOK s₀) (hm : Inst1MemoA ve s₀) (hv : denoteE s₀.store v = some ve)
    (hview : s₀.store.view h = some (.proj n i sub))
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Proj v rec h d n i sub
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₀.store s'.store ∧
        Inst1At ve d s₀.store h s'.store r⌝⦄ := by
  have hr := hrec.run
  mvcgen [inst1Proj, hr]
  case vc11 =>
    spike_peel
    subst_vars
    obtain ⟨nm, es, hpe, hn0, hsub⟩ := denote_eq_proj hok.wf hview hden
    refine Inst1At.retarget ?_ ?_ hden
    · exact Inst1At.proj_step hok.wf hview (by assumption) (by assumption)
        (by assumption) (by assumption) hn0
    · grind only [Ext.trans]
  case vc12 =>
    spike_peel
    subst_vars
    obtain ⟨nm, es, hpe, hn0, hsub⟩ := denote_eq_proj hok.wf hview hden
    grind only [Inst1At.proj_step, Ext.trans, StateOK, StateOK.mk]
  all_goals vcs

/-! ## The dispatcher

Every arm is a spec theorem passed to this one `mvcgen`, so `mvcgen` never
looks inside an arm: what is left is the *dispatch* — the derived-word cutoff,
the four leaf kinds that answer with the handle itself, the view each arm spec
asks for, and one `Inst1Spec` side goal per arm, discharged by the induction
hypothesis. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33 instantiate1 — **Theorem 1 for
subject 1**, arm by arm.  Same statement as `ExpA.instantiate1A_spec`, at a
twin whose arms are named. -/
theorem instantiate1B_spec (v : EIdx) (ve : Expr) :
    ∀ (fuel : Nat), Inst1Spec v ve (instantiate1B v fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h d _ _ _ _
    mvcgen [instantiate1B]
    all_goals vcs
  | succ fuel ih =>
    constructor
    intro s₀ h d hok hm hv hden
    mvcgen [instantiate1B, inst1Bvar_spec, inst1App_spec, inst1Lam_spec,
      inst1Forall_spec, inst1Let_spec, inst1Proj_spec]
    -- the derived-word cutoff: the one dispatch condition that is neither an
    -- `assumption` nor a leaf equation
    case vc1 =>
      spike_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, Inst1At.cutoff hok.wf (by grind) (by grind)⟩
    all_goals (first
      | exact ih
      | (intro hf; exact False.elim hf)
      | (intros
         spike_peel
         subst_vars
         first
         | rfl
         | assumption
         | (unfold Inst1At
            grind (instances := 200) [StateOK, Ext.refl, Expr.instantiate1])))

/-! ## The top-level call, and Theorem 1 as a statement about a run -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:120 instantiate1 (the `@[csimp]`
entry point) — the memo is fresh before and dropped after. -/
def instantiate1BTop (v : EIdx) (fuel : Nat) (h : EIdx) : AM EIdx := do
  inst1Clear
  let r ← instantiate1B v fuel h 0
  inst1Clear
  pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:120 instantiate1 — the dropped memo
satisfies `Inst1MemoA` for every substituted term, which is why the per-call
memo never appears in a caller's invariant. -/
theorem instantiate1BTop_spec (v : EIdx) (ve : Expr) (fuel : Nat) (s₀ : AState)
    (h : EIdx) (hok : StateOK s₀) (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instantiate1BTop v fuel h
    ⦃⇓? h' s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
        Inst1At ve 0 s₀.store h s'.store h'⌝⦄ := by
  have hr := (instantiate1B_spec v ve fuel).run
  mvcgen [instantiate1BTop, hr]
  all_goals vcs

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same statement about a
*run*, which is the form the tier above consumes. -/
theorem instantiate1BTop_run {v : EIdx} {ve : Expr} {fuel : Nat} {s₀ s' : AState}
    {h h' : EIdx} (hok : StateOK s₀) (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (instantiate1BTop v fuel h).run s₀ = .ok (h', s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
      Inst1At ve 0 s₀.store h s'.store h' :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (instantiate1BTop_spec v ve fuel s₀ h hok hv hden)

/-! ## The axiom check

`propext`, `Classical.choice`, `Quot.sound` and nothing else — in particular
no `sorryAx`.  (Unlike round 1's `instantiate1A_spec`, which reaches
`EStore.intern_spec` through `internE_spec` and therefore carried `sorryAx`
while task #97a's `intern_wf` was open; that clause is closed now.) -/
#print axioms instantiate1B_spec
#print axioms instantiate1BTop_spec
#print axioms instantiate1BTop_run

end ConRon.Arena.Spike.Fast
