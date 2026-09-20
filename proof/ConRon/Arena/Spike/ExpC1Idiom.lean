/-
# Experiment C1, redone with the task-#70/#71 refinement idiom

Round 2 proved experiment C1 (`Spike/ExpC1.lean`: the Aeneas model of the
Rust refines the Lean twin) **by hand** — 394 lines, ~300 of them the same
six moves repeated down every branch — and concluded that "there is no
automation for program-to-program equality".  The maintainer's question for
round 3 is the obvious one: *the `Refine` tier has had an idiom for exactly
this shape since task #70; is Rust-against-twin different from
Rust-against-Cached-twin?*

This file answers it by redoing C1 with that idiom and nothing else:

```lean
⟨shape step⟩ ; rust_norm hrun ; all_goals rust_grind
```

with `rust_grind`'s one budget raised (§"The closing call") and one Aeneas
`@[grind ext]` registration erased (§"The scalar dictionary") — both of them
one line, neither of them per-branch tuning.

`rust_norm` and `rust_grind` are `ConRon/Refine/Abs.lean`'s, unmodified, with
their two registered simp sets (`rust_reduce`, `rust_invert`); the callee
lemmas are registered as `@[grind →]` rules **keyed on the Rust equation**,
which is `Refine/AUTOMATION.md`'s first keying rule; the induction hypothesis
is packaged as a `Spec` predicate with a `use` lemma, which is its second.

The answer is in DESIGN §"Task #97s" `#### Round 3`.  In one line: it is the
*same* idiom and it works — round 2's **378 lines of proof, ~300 of them
hand matching**, become **22 lines, 20 of them the shape step**, on top of a
**one-off 92-line** inversion layer, because the twin's `.run` equation
(`MiniRun.lean`) turns the "two programs to line up" of round 2 into an
ordinary Rust success hypothesis with an `Except`-valued right-hand side,
which is precisely the shape `rust_norm` was built to peel.  `rust_norm`
leaves seven goals and the closer shuts seven; nothing is left open.

**Cost of the import.**  `ConRon.Refine.Abs` costs **0.02 s** of elaboration
per importing file and brings *no* Mathlib — Aeneas already imports Mathlib
and the spike already imports Aeneas, so the task-#97a "no Mathlib in the
arena libraries" rule was never holding for `Spike/`.  What it does bring is
a build dependency on `ConRon.Generated`'s 76 448 lines: ≈ 3.5 min one-off at
`LAKE_JOBS=1` in a fresh worktree, 134 MB of `.olean`.  That is an accident
of file layout — `rust_norm`, `rust_grind`, `rust_pairs` and the two
`register_simp_attr` sets depend on nothing in the model — so for P5 the
conclusion is to split them out of `Refine/Abs.lean` into a small
`Refine/Idiom.lean` that imports only `Aeneas` and `Refine/SimpSets.lean`.
Nothing under `Refine/` was changed for this experiment.
-/
import ConRon.Arena.Spike.MiniAbs
import ConRon.Refine.Abs

namespace ConRon.Arena.Spike

open ConLeche Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

/-! ## The inversion layer

`MiniAbs.lean` states its callee lemmas existentially (`∃ o, f args = .ok o ∧
…`), which is the right shape for a *hand* proof — `obtain` gives the Rust
equation and the abstraction fact in one step.  It is the wrong shape for
`grind`: `AUTOMATION.md` §"What does not work" records that an existential
conclusion is negated into a `∀` whose body never reaches the E-graph.

So each is restated once in the `→` form the idiom wants, **with the Rust
success equation as the first hypothesis** so that E-matching keys on it.
These fifteen lemmas (92 code lines with the dictionary and the `Spec`/`use`
pair below) are the whole per-crate cost of the idiom on the Rust side; they
are derivations, not proofs, and each is one line. -/

/-- con-leche: none — `tag_of`, inverted. -/
@[grind →] theorem abs_tag_use {h t : U32} (ht : Generated.tag_of h = .ok t) :
    absU t = mTagOf (absU h) := by
  obtain ⟨t', h1, h2⟩ := abs_tag h
  rw [ht, Result.ok.injEq] at h1; subst h1; exact h2

/-- con-leche: none — `view_bvar`, inverted. -/
@[grind →] theorem abs_view_bvar_use {st : Generated.State} {h : U32} {o : Option U32}
    (ho : Generated.view_bvar st h = .ok o) :
    (absState st).viewBvar (absU h) = o.map absU := by
  obtain ⟨o', h1, h2⟩ := abs_view_bvar st h
  rw [ho, Result.ok.injEq] at h1; subst h1; exact h2

/-- con-leche: none — `view_app`, inverted. -/
@[grind →] theorem abs_view_app_use {st : Generated.State} {h : U32}
    {o : Option (U32 × U32)} (ho : Generated.view_app st h = .ok o) :
    (absState st).viewApp (absU h) = o.map (fun p => (absU p.1, absU p.2)) := by
  obtain ⟨o', h1, h2⟩ := abs_view_app st h
  rw [ho, Result.ok.injEq] at h1; subst h1; exact h2

/-- con-leche: none — `view_lam`, inverted. -/
@[grind →] theorem abs_view_lam_use {st : Generated.State} {h : U32}
    {o : Option (U32 × U32)} (ho : Generated.view_lam st h = .ok o) :
    (absState st).viewLam (absU h) = o.map (fun p => (absU p.1, absU p.2)) := by
  obtain ⟨o', h1, h2⟩ := abs_view_lam st h
  rw [ho, Result.ok.injEq] at h1; subst h1; exact h2

/-- con-leche: none — `memo_get`, inverted. -/
@[grind →] theorem abs_memo_get_use {st : Generated.State} {h d : U32} {o : Option U32}
    (ho : Generated.memo_get st h d = .ok o) :
    mMemoGet (absState st) (absU h) (absU d) = o.map absU := by
  obtain ⟨o', h1, h2⟩ := abs_memo_get st h d
  rw [ho, Result.ok.injEq] at h1; subst h1; exact h2

/-- con-leche: none — `intern_bvar`, inverted: the abstraction half. -/
@[grind →] theorem abs_intern_bvar_use {st st' : Generated.State} {k r : U32}
    (hi : Generated.intern_bvar st k = .ok (some r, st')) (hwf : GWF st) :
    (mInternBvar (absU k)).run (absState st) = .ok (absU r, absState st') := by
  obtain ⟨o, sta, h1, h2, h3⟩ := abs_intern_bvar st hwf k
  rw [hi, Result.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨e1, e2⟩ := h1; subst e2; exact h3 r e1.symm

/-- con-leche: none — `intern_bvar`, inverted: the invariant half. -/
@[grind →] theorem abs_intern_bvar_wf {st st' : Generated.State} {k : U32} {o : Option U32}
    (hi : Generated.intern_bvar st k = .ok (o, st')) (hwf : GWF st) : GWF st' := by
  obtain ⟨o', sta, h1, h2, h3⟩ := abs_intern_bvar st hwf k
  rw [hi, Result.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨-, e2⟩ := h1; subst e2; exact h2

/-- con-leche: none — `intern_app`, inverted: the abstraction half. -/
@[grind →] theorem abs_intern_app_use {st st' : Generated.State} {f a r : U32}
    (hi : Generated.intern_app st f a = .ok (some r, st')) (hwf : GWF st) :
    (mInternApp (absU f) (absU a)).run (absState st) = .ok (absU r, absState st') := by
  obtain ⟨o, sta, h1, h2, h3⟩ := abs_intern_app st hwf f a
  rw [hi, Result.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨e1, e2⟩ := h1; subst e2; exact h3 r e1.symm

/-- con-leche: none — `intern_app`, inverted: the invariant half. -/
@[grind →] theorem abs_intern_app_wf {st st' : Generated.State} {f a : U32} {o : Option U32}
    (hi : Generated.intern_app st f a = .ok (o, st')) (hwf : GWF st) : GWF st' := by
  obtain ⟨o', sta, h1, h2, h3⟩ := abs_intern_app st hwf f a
  rw [hi, Result.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨-, e2⟩ := h1; subst e2; exact h2

/-- con-leche: none — `intern_lam`, inverted: the abstraction half. -/
@[grind →] theorem abs_intern_lam_use {st st' : Generated.State} {ty b r : U32}
    (hi : Generated.intern_lam st ty b = .ok (some r, st')) (hwf : GWF st) :
    (mInternLam (absU ty) (absU b)).run (absState st) = .ok (absU r, absState st') := by
  obtain ⟨o, sta, h1, h2, h3⟩ := abs_intern_lam st hwf ty b
  rw [hi, Result.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨e1, e2⟩ := h1; subst e2; exact h3 r e1.symm

/-- con-leche: none — `intern_lam`, inverted: the invariant half. -/
@[grind →] theorem abs_intern_lam_wf {st st' : Generated.State} {ty b : U32} {o : Option U32}
    (hi : Generated.intern_lam st ty b = .ok (o, st')) (hwf : GWF st) : GWF st' := by
  obtain ⟨o', sta, h1, h2, h3⟩ := abs_intern_lam st hwf ty b
  rw [hi, Result.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨-, e2⟩ := h1; subst e2; exact h2

/-- con-leche: none — `memo_set`, inverted: the abstraction half.  (Already
keyed on the Rust equation in `MiniAbs`; only the conjunction is split.) -/
@[grind →] theorem abs_memo_set_use {st st' : Generated.State} {h d r : U32}
    (hr : Generated.memo_set st h d r = .ok st') :
    absState st' = { absState st with
      memo := (absState st).memo ++ [(absU h, absU d, absU r)] } :=
  (abs_memo_set st st' h d r hr).1

/-- con-leche: none — `memo_set`, inverted: the invariant half. -/
@[grind →] theorem abs_memo_set_wf {st st' : Generated.State} {h d r : U32}
    (hr : Generated.memo_set st h d r = .ok st') (hwf : GWF st) : GWF st' :=
  (abs_memo_set st st' h d r hr).2 hwf

/-- con-leche: none — the checked `u32` subtraction, inverted: the success
tells the caller both that it did not underflow and what it produced.  (The
`+` twin is `MiniAbs.u32_add_inv`.) -/
@[grind →] theorem u32_sub_inv {x y z : U32} (h : (x - y : Result U32) = .ok z) :
    y.val ≤ x.val ∧ z.val = x.val - y.val := by
  have he := UScalar.sub_equiv x y
  rw [h] at he
  simp only [Result.match.ok] at he
  exact ⟨he.1, by have := he.2.1; omega⟩

attribute [grind →] u32_add_inv

/-! ## The scalar dictionary, and the one attribute that has to be *removed*

`absU` is `.val`; the three tags and the cap are literals.  These are `grind
=` equations, elaborated once, so that the arithmetic of the fuel counter and
of the tag comparison is visible to `grind`'s linear solver.

The `attribute [-grind]` line is the round-3 counterpart of round 2's
attribute-hygiene finding.  Aeneas registers `U32.bv_eq_imp_eq` and
`UScalar.val_eq_imp` as `@[grind ext]`, so a machine-word *dis*equality —
which every split of a generated `if tag = TAG_APP` produces — is blasted
into `∀ i, x.bv[i] = y.bv[i]`.  Two things go wrong at once: the bit-level
facts are useless here, and on an `@[irreducible]` generated constant
(`Generated.TAG_BVAR := 0#u32`) `grind`'s `lia` module then closes a goal
with a `decide`-by-`rfl` step that the *elaborator* evaluates to `false` and
the *kernel*, which does unfold `irreducible`, evaluates to `true` — a
`(kernel) application type mismatch: decide (0 = 0) = false` on an otherwise
accepted proof.  Removing the two `ext` registrations removes both.  (`-lia`
also removes the kernel error, but then the fuel bound is out of reach.) -/

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

@[grind =] theorem absU_def (x : U32) : absU x = x.val := rfl
attribute [grind →] absU_inj
attribute [grind =] tagbvar tagapp taglam idxcap
attribute [grind =] mTagBvar mTagApp mTagLam
attribute [grind =] mMemoSet_run mInstantiate1_run_zero

/-- con-leche: none — the `Except` bind at a value, reduced.  This is the one
equation that makes the twin's `.run` chain collapse under `grind`. -/
@[grind =] theorem except_ok_bind' {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α).bind f = f a := rfl

/-! ## The induction hypothesis, as a predicate

`AUTOMATION.md`'s packaging rule: a local `∀`-hypothesis has its E-matching
pattern inferred from its *conclusion*, which here is the twin's `.run`
equation — a term that does not exist until the recursive call has been
abstracted.  A named predicate with a `use` lemma keyed on the Rust equation
fixes the pattern where the proof can see it. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — **C1 at a fuel bound**. -/
def C1Spec (n : Nat) : Prop :=
  ∀ (st st' : Generated.State) (v fuel h d r : U32), GWF st → absU fuel ≤ n →
    Generated.instantiate1 st v fuel h d = .ok (some r, st') →
    GWF st' ∧ (mInstantiate1 (absU v) (absU fuel) (absU h) (absU d)).run (absState st)
      = .ok (absU r, absState st')

/-- con-leche: none — the `use` lemma, Rust equation first. -/
@[grind →] theorem C1Spec.use {n : Nat} {st st' : Generated.State} {v fuel h d r : U32}
    (hrun : Generated.instantiate1 st v fuel h d = .ok (some r, st'))
    (hs : C1Spec n) (hwf : GWF st) (hn : absU fuel ≤ n) :
    GWF st' ∧ (mInstantiate1 (absU v) (absU fuel) (absU h) (absU d)).run (absState st)
      = .ok (absU r, absState st') :=
  hs st st' v fuel h d r hwf hn hrun

/-! ## The closing call

`rust_grind` is `grind (ematch := 12) (gen := 24)` and that is one case-split
short here: a generated body with three tag tests, three `Option` matches and
four `Result` binds in one arm needs more splits than a `Level` leaf, and
`grind` says so (`[limit] maximum number of case-splits has been reached,
threshold: (splits := 9)`).  `AUTOMATION.md`'s rule for exactly this case is
"raising the macro's default is the answer, not a per-lemma override", so
this is `rust_grind` with that one default raised — the same configuration
for every goal of the file, and nothing tuned per branch. -/

macro "arena_grind" : tactic => `(tactic| grind (ematch := 12) (gen := 24) (splits := 40))

/-! ## The proof

The idiom, with the shape step spelled out: the `Result`-valued body is
opened with its `eq_def`, the fuel counter is put in `m + 1` form (the
analogue of `ExprWF.ind_node`'s constructor inversion — it is what makes the
twin's one-step equation apply), and then `rust_norm` peels the Rust success
hypothesis into one goal per reachable path — **seven** of them — and
`arena_grind` closes every one. -/

/-- con-leche: none — **experiment C1 by the task-#70/#71 idiom**, with the
fuel bound explicit. -/
theorem instantiate1_C1_idiom_aux : ∀ n : Nat, C1Spec n := by
  intro n
  induction n with
  | zero =>
    intro st st' v fuel h d r hwf hn hrun
    rw [Generated.instantiate1.eq_def] at hrun
    have : fuel = 0#u32 := absU_inj (by simp only [absU] at hn ⊢; scalar_tac)
    rw [this, if_pos rfl] at hrun
    simp at hrun
  | succ n ih =>
    intro st st' v fuel h d r hwf hn hrun
    rw [Generated.instantiate1.eq_def] at hrun
    by_cases hf0 : fuel = 0#u32
    · rw [hf0, if_pos rfl] at hrun; simp at hrun
    rw [if_neg hf0] at hrun
    obtain ⟨m, hm⟩ : ∃ m, absU fuel = m + 1 :=
      ⟨absU fuel - 1, by
        have : fuel.val ≠ 0 := fun hc => hf0 (absU_inj (by simp [absU, hc]))
        simp only [absU]; omega⟩
    rw [hm, mInstantiate1_run_succ]
    rust_norm hrun
    all_goals arena_grind

/-- **Experiment C1**, by the idiom.  Same statement as `ExpC1.instantiate1_C1`. -/
theorem instantiate1_C1_idiom (st st' : Generated.State) (v fuel h d r : Aeneas.Std.U32)
    (hwf : GWF st)
    (hrun : Generated.instantiate1 st v fuel h d = .ok (some r, st')) :
    (mInstantiate1 (absU v) (absU fuel) (absU h) (absU d)).run (absState st)
      = .ok (absU r, absState st') :=
  (instantiate1_C1_idiom_aux (absU fuel) st st' v fuel h d r hwf (Nat.le_refl _) hrun).2

/-- con-leche: none — C1's invariant half, by the idiom. -/
theorem instantiate1_C1_idiom_wf (st st' : Generated.State) (v fuel h d r : Aeneas.Std.U32)
    (hwf : GWF st)
    (hrun : Generated.instantiate1 st v fuel h d = .ok (some r, st')) : GWF st' :=
  (instantiate1_C1_idiom_aux (absU fuel) st st' v fuel h d r hwf (Nat.le_refl _) hrun).1

/-! ## The axiom check -/

#print axioms instantiate1_C1_idiom
#print axioms instantiate1_C1_idiom_wf

end ConRon.Arena.Spike
