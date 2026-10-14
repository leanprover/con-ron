/-
# `ConRon.Bridge.ExprOps.Inst1` — Theorem 1 for `instantiate1`

DESIGN §8.2's Theorem 1 at `ExprOps.lean`'s first twin, and the module the
rest of the tier is written against: it fixes the shape of a walk's statement,
the shape of its arm's step lemma, and what the tag dispatch costs the proof.

## The statement

```lean
structure Inst1Spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ s₁ c dd, StateOK s₁ → Inst1MemoA ve s₁ →
    denoteE s₁.store v = some ve → (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ rec c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄
```

* `Inst1At ve dd` is `Bridge/Rel.lean`'s **generic** `RelE` with the pure
  function fixed (task #97b finding 1), so all of `RelE`'s eliminators apply
  and `grind` still sees a head symbol;
* the record wraps the triple so that the arms can take it as a hypothesis
  and the dispatcher can discharge it with the fuel induction — task #97s's
  rule 8 shape;
* `s'.caches = s₁.caches` and `s'.pins = s₁.pins` are the frame `CheckOK.mono`
  consumes; **the twelve other per-call memo tables are NOT framed here** —
  see "What this module does not claim" at the end.

## The two deviations from con-leche this twin carries

1. **The derived-word cutoff** (DESIGN §8.3 lesson 20, the one §8.3 asks for
   by name and con-leche's `instantiate1Go` does not have): the walk returns
   `h` when the packed loose-bvar bound is exact and at most the cursor.  Its
   licence is `instantiate1_of_raw_le` below — `Expr.bvarBRaw_exact` (con-leche
   `ExprOps.lean:1456`) plus an induction on `Expr`.
2. **Fuel**, because a handle DAG has no structural order the elaborator can
   see.  Exhaustion is a failure and Theorem 1 claims nothing on failure
   (con-leche's `SimAt`), which is what the `⊤` exception postcondition says.

Everything else is clause for clause: the five leaf kinds answer without
touching the memo, and the four branching kinds probe the memo, run the body
one level down and insert.

## The tag dispatch, and the closer

The twin tests `h.tag` before reading the store (task #97-P6-13), so the arms
are guarded by tag equations rather than by `view` patterns.  Every proof is
`sym only [bridge_grind] => vcgen [f, callee specs…] <;> finish`: `grind`
sees the arm's projection read as a `DenoteView` fact on the subject
(`Bridge/Grind.lean` §6), the subject's denotation as its
constructor with projected fields (the tag-guarded `exprTag_*` etas), the
children's answers as `MapRel` equations, and `Expr.instantiate1`'s own
equations — so the arm's step is congruence closure, with no step lemma and
no case split.  The cutoff and the catch-all are one equation each
(`inst1_cut`, `inst1_leaf`), keyed on the term they rewrite.
-/
import ConRon.Bridge.Specs
import ConRon.Bridge.Grind

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## The cutoff's licence

The one pure lemma this twin needs that con-leche does not have, because
con-leche's `instantiate1Go` has no cutoff. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — **the
cutoff's licence**: a term with no loose `bvar` at or above the cursor is its
own instantiation.  DESIGN §8.3's "instantiate returns at `bvarB ≤
offset`". -/
theorem instantiate1_of_bvarBound_le {v : Expr} :
    ∀ (e : Expr) (d : Nat), e.bvarBound ≤ d → e.instantiate1 v d = e := by
  intro e
  induction e with
  | bvar i =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp only [Expr.instantiate1, ite_eq_right (show ¬ i = d by omega),
      ite_eq_right (show ¬ i > d by omega)]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro d _; simp [Expr.instantiate1]
  | app f a ihf iha =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, ihf d h.1, iha d h.2]
  | lam ty b iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1, ihb (d + 1) (by omega)]
  | forallE ty b iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1, ihb (d + 1) (by omega)]
  | letE ty w b iht ihw ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1.1, ihw d h.1.2, ihb (d + 1) (by omega)]
  | proj n i e ih =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp [Expr.instantiate1, ih d h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1456 bvarBRaw_exact — the cutoff
as the arena TESTS it: the packed field, below saturation, licences the early
return. -/
theorem instantiate1_of_raw_le {v e : Expr} {d : Nat}
    (hsat : e.bvarBRaw < satRange) (hle : e.bvarBRaw ≤ d) :
    e.instantiate1 v d = e :=
  instantiate1_of_bvarBound_le e d (by rw [← Expr.bvarBRaw_exact e hsat]; exact hle)

/-! ## The answer relation

`Inst1At` is `RelE` at `instantiate1`'s pure function; the arms are closed
by `grind` from `Bridge/Grind.lean`'s vocabulary and the two clause
equations below. -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `instantiate1`'s answer
relation. -/
abbrev Inst1At (ve : Expr) (d : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (fun e => e.instantiate1 ve d)

/-! ### `instantiate1`'s two non-structural clauses as equations

The derived-word cutoff and the catch-all, each keyed on the term it
rewrites, so that the dispatcher's two exits need no step lemma. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1456 bvarBRaw_exact — the
CUTOFF as an equation: below the packed bound, `instantiate1` is the identity
on the handle's denotation (guarded by the denotation). -/
private theorem inst1_cut {st : EStore} (hwf : StoreWF st) {h : EIdx} {e v : Expr} {d : Nat}
    (he : denoteE st h = some e) (hsat : (bvarOfData (st.derived h)).toNat < satRange)
    (hle : (bvarOfData (st.derived h)).toNat ≤ d) : e.instantiate1 v d = e := by
  have hd := EStore.derived_exact hwf he
  rw [hd] at hsat hle
  exact instantiate1_of_raw_le hsat hle
local grind_pattern [bridge_grind] inst1_cut =>
    bvarOfData (st.derived h), Expr.instantiate1 e v d where
  guard denoteE st h = some e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — the
CATCH-ALL as an equation: a term whose tag is none of the six the walk
dispatches on is a fixed point. -/
private theorem inst1_leaf {e v : Expr} {d : Nat} (happ : ¬ exprTag e = ETag.app)
    (hbind : ETag.isBind (exprTag e) = false) (hbvar : ¬ exprTag e = ETag.bvar)
    (hlet : ¬ exprTag e = ETag.letE) (hproj : ¬ exprTag e = ETag.proj) :
    e.instantiate1 v d = e := by
  cases e <;> simp_all [exprTag, ETag.isBind, Expr.instantiate1] <;> contradiction
local grind_pattern [bridge_grind] inst1_leaf => Expr.instantiate1 e v d, exprTag e

/-! ## Theorem 1 for `instantiate1Go`

One level of the recursion as a record, so that the fuel induction has
something to hand the arms (task #97s rule 8).

**Per DESIGN §8.6's arm-split ruling** the twin
is a `mutual` block — a dispatcher and one `def` per constructor arm — and
the proof follows it exactly: one theorem per arm, each taking the previous
fuel level's record as its induction hypothesis, and a dispatcher whose
`vcgen` list is the five arm theorems.  The dispatcher's body is then the
cutoff, the tag chain and six calls, so `vcgen` leaves a handful of
verification conditions, and `grind` never sees more than one arm's
worth of context at a time.

**Each arm carries its own tag hypothesis.**  `EStore.viewApp` does not test
the tag (it is the array read the tag dispatch has already decided, tasks
#97-P6-10 and #97-P6-13), so `view_of_viewApp` needs `h.tag = ETag.app` and
the arm theorem takes it as a parameter; the dispatcher supplies it from the
branch it is in, as one more verification condition that `assumption` closes. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `instantiate1Go`'s recursion. -/
structure Inst1Spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx) :
    Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (dd : Nat), StateOK s₁ → Inst1MemoA ve s₁ →
    denoteE s₁.store v = some ve → (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ rec c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `bvar`
ARM, which is not recursive and needs no induction hypothesis.  The three
branches are `Expr.instantiate1`'s own three, given to `sym` as its
equations. -/
theorem instantiate1ArmBVar_spec (v : EIdx) (ve : Expr) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.bvar) = true) :
    ⦃fun s => s = s₁⦄ instantiate1ArmBVar v c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄ := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  -- the three branches are `Expr.instantiate1`'s own three
  sym only [bridge_grind, denoteEView, Expr.instantiate1] =>
    vcgen [instantiate1ArmBVar] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `app`
ARM: probe, project, recurse into both children, rebuild, insert. -/
theorem instantiate1ArmApp_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.app) = true) :
    ⦃fun s => s = s₁⦄ instantiate1ArmApp v fuel c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄ := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  sym only [bridge_grind, denoteEView, opt2, Expr.instantiate1] =>
    vcgen [instantiate1ArmApp, ih.run, inst1Set_spec (ve := ve)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the BINDER
ARM (`lam` and `forallE` in one, as the tag dispatch tests them). -/
theorem instantiate1ArmBind_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : ETag.isBind c.tag = true) :
    ⦃fun s => s = s₁⦄ instantiate1ArmBind v fuel c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄ := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  -- `lam` or `forallE`: the one case split, on `ETag.isBind`'s disjunction
  sym only [bridge_grind, denoteEView, opt2, Expr.instantiate1, ETag.isBind] =>
    vcgen [instantiate1ArmBind, ih.run, inst1Set_spec (ve := ve)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `letE`
ARM; the body descends at `dd + 1`. -/
theorem instantiate1ArmLet_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.letE) = true) :
    ⦃fun s => s = s₁⦄ instantiate1ArmLet v fuel c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄ := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  sym only [bridge_grind, denoteEView, opt3, Expr.instantiate1] =>
    vcgen [instantiate1ArmLet, ih.run, inst1Set_spec (ve := ve)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `proj`
ARM.  The struct NAME is carried unchanged, and its denotation comes from
`denote_eq_proj`'s existential, which `grind` cannot see through. -/
theorem instantiate1ArmProj_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.proj) = true) :
    ⦃fun s => s = s₁⦄ instantiate1ArmProj v fuel c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄ := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  sym only [bridge_grind, denoteEView, opt2, Expr.instantiate1] =>
    vcgen [instantiate1ArmProj, ih.run, inst1Set_spec (ve := ve)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1
con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
**THEOREM 1 for `instantiate1`**, at one level of the recursion, by induction
on the fuel.  The dispatcher: the cutoff, the tag chain, the five arms by
name, and the catch-all. -/
theorem instantiate1Go_spec (v : EIdx) (ve : Expr) :
    ∀ fuel, Inst1Spec v ve (instantiate1Go v fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h d _ _ _ _
    sym only [bridge_grind] => vcgen [instantiate1Go_zero] <;> finish
  | succ fuel ih =>
    constructor
    intro s₀ h d hok hm hv hden
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
    -- the five arms' preconditions, the derived-word cutoff and the catch-all
    sym only [bridge_grind] =>
      vcgen [instantiate1Go_succ, instantiate1ArmApp_spec v ve fuel ih,
        instantiate1ArmBind_spec v ve fuel ih, instantiate1ArmBVar_spec v ve,
        instantiate1ArmLet_spec v ve fuel ih, instantiate1ArmProj_spec v ve fuel ih] <;> finish
/-! ## The top-level entry, and Theorem 1 as a statement about a RUN

`instantiate1Fast` is con-leche's `(instantiate1Go v {} e d).1`: the memo is
fresh before and dropped after, because its answers depend on the substituted
term.  The dropped memo satisfies `Inst1MemoA` for EVERY substituted term
(`MemoOK.of_empty`), which is why the per-call memo never appears in a
caller's invariant. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast —
**THEOREM 1 for `instantiate1`, at the entry point**. -/
theorem instantiate1Fast_spec (fuel : Nat) (s₀ : AState) (e v : EIdx) (d : Nat)
    (ve : Expr) (hok : StateOK s₀) (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ instantiate1Fast fuel e v d
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.inst1C = ∅ ∧
        Inst1At ve d s₀.store e s'.store r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [instantiate1Fast, (instantiate1Go_spec v ve fuel).run] <;> finish

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same statement about
a RUN, which is the form the tier above consumes. -/
theorem instantiate1Fast_run {fuel : Nat} {s₀ s' : AState} {e v r : EIdx}
    {d : Nat} {ve : Expr} (hok : StateOK s₀)
    (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (instantiate1Fast fuel e v d).run s₀ = Except.ok (r, s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧
      s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.inst1C = ∅ ∧
      Inst1At ve d s₀.store e s'.store r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (instantiate1Fast_spec fuel s₀ e v d ve hok hv hden)

/-! ## The axiom check -/

#print axioms instantiate1_of_bvarBound_le
#print axioms instantiate1_of_raw_le

end ConRon.Bridge.ExprOps
