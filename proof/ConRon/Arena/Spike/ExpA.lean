/-
# Experiment A — Theorem 1 for the three subjects, by `mvcgen`

DESIGN §8.6's P2s experiment A.  Each theorem is

```
  intro …
  mvcgen [<the twin's equations>, <the IH>]
  all_goals spike_vcs
```

and nothing else: `spike_vcs` is the one uniform closer below.  **Every
verification condition `mvcgen` leaves is pure** — no `wp`, no monad, no
`SPred` — and `grind` discharges all of them from the `@[spec]`/`@[grind]`
layer in `Specs.lean`.  What the layer has to contain for that to be true is
the spike's real finding; see `_tmp/t97/spike-report.md` and DESIGN §8's task
section.
-/
import ConRon.Arena.Spike.Specs
import ConRon.Arena.Spike.Peel

namespace ConRon.Arena.Spike

open ConLeche Std.Do

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

/-- **The uniform closer.**  Three moves, in this order:

1. *peel* (`casesm* _ ∧ _` then `subst_vars`) — `mvcgen` threads its plumbing
   as conjunctions `s' = s ∧ <what the step did>`; destructing them and
   substituting the state equalities is purely syntactic and is what lets
   `grind`'s congruence closure see one state where the goal shows seven.
   (An earlier version peeled with `repeat obtain … := ‹_ ∧ _›`; the
   `assumption` behind `‹_›` searches with metavariables and cost minutes of
   `whnf` on the goals that have no conjunction left.  `casesm` is the cheap
   spelling.);
2. *unfold the answer relation in the goal* — the postcondition is a `def`
   (so that `grind` can ematch on it in hypotheses); in the goal it has to be
   introduced, which is `intro` after `unfold`;
3. *`grind`* with the store layer. -/
macro "spike_vcs" : tactic => `(tactic| first
  | (intro hf; exact False.elim hf)
  | (spike_peel
     subst_vars
     try unfold Inst1At
     grind (instances := 8000) [StateOK, Inst1MemoA.mono, Inst1MemoA.insert,
       Inst1MemoA.get, Ext.trans, Ext.refl, viewOK_bvar, viewOK_app, viewOK_lam,
       viewOK_forallE, viewOK_letE, viewOK_proj, Expr.instantiate1,
       instantiate1_of_raw_le, EStore.derived_exact, Option.isSome_iff_exists,
       Expr.bvarBRaw, denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
       Option.map_eq_some_iff])
  | (spike_peel
     subst_vars
     try unfold Inst1At
     grind (instances := 20000) [StateOK, Inst1MemoA.mono, Inst1MemoA.insert,
       Inst1MemoA.get, Ext.trans, Ext.refl, Inst1At.ext, Inst1At.of_ext,
       Inst1At.letE, Inst1At.app, Inst1At.lam, Inst1At.forallE, Inst1At.proj,
       viewOK_bvar, viewOK_app, viewOK_lam,
       viewOK_forallE, viewOK_letE, viewOK_proj, Expr.instantiate1,
       instantiate1_of_raw_le, EStore.derived_exact, Option.isSome_iff_exists,
       Expr.bvarBRaw, denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
       Option.map_eq_some_iff]))

/-! ## Subject 1 — `instantiate1`

Theorem 1 for `instantiate1A`, in the shape the spike recommends for every
(B) function:

* the precondition is `s = s₀` in the triple and *ordinary hypotheses*
  besides;
* "the subject denotes" is an `isSome`, never a named `Expr` — that is what
  keeps every recursive call's side goal metavariable-free;
* the answer is the named relation `Inst1At`, never a bare `∀ e, … → …`.
-/
theorem instantiate1A_spec (v : EIdx) (ve : Expr) :
    ∀ (fuel : Nat) (s₀ : AState) (h : EIdx) (d : Nat),
      StateOK s₀ → Inst1MemoA ve s₀ → denoteE s₀.store v = some ve →
      (denoteE s₀.store h).isSome = true →
      ⦃fun s => ⌜s = s₀⌝⦄ instantiate1A v fuel h d
      ⦃⇓? h' s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₀.store s'.store ∧
          Inst1At ve d s₀.store h s'.store h'⌝⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ h d _ _ _ _
    mvcgen [instantiate1A]
    all_goals spike_vcs
  | succ fuel ih =>
    intro s₀ h d hok hm hv hden
    mvcgen [instantiate1A, ih]
    -- The derived-word cutoff is the ONE verification condition the uniform
    -- closer does not take: `Expr.instantiate1` and `instantiate1_of_raw_le`
    -- together send `grind` into an ematching spiral on
    -- `((e.instantiate1 v d).instantiate1 v d)…`.  `Inst1At.cutoff` is that
    -- pair packaged as a single step, applied here by hand.
    case vc1.succ.post.success.isTrue =>
      spike_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, Inst1At.cutoff hok.wf (by grind) (by grind)⟩
    all_goals spike_vcs

/-- con-leche: ConLeche/Kernel/ExprOps.lean:120 instantiate1 — the top-level
call, whose memo is fresh in and empty out.  The empty memo satisfies
`Inst1MemoA` for **every** substituted term, which is why the per-call memo
never appears in the caller's invariant. -/
theorem instantiate1Top_spec (v : EIdx) (ve : Expr) (fuel : Nat) (s₀ : AState)
    (h : EIdx) (hok : StateOK s₀) (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instantiate1Top v fuel h
    ⦃⇓? h' s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
        Inst1At ve 0 s₀.store h s'.store h'⌝⦄ := by
  mvcgen [instantiate1Top, instantiate1A_spec]
  all_goals spike_vcs

/-! ## Theorem 1 as a statement about a *run*

`AM.of_run` turns the triple into con-leche's `SimAt` shape.  This is the
form the tier above consumes, and it is three lines from the triple. -/
theorem instantiate1Top_run {v : EIdx} {ve : Expr} {fuel : Nat} {s₀ s' : AState}
    {h h' : EIdx} (hok : StateOK s₀) (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (instantiate1Top v fuel h).run s₀ = .ok (h', s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
      Inst1At ve 0 s₀.store h s'.store h' :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (instantiate1Top_spec v ve fuel s₀ h hok hv hden)

end ConRon.Arena.Spike
