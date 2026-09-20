/-
# Experiment C1, variant 2: Aeneas's own `step` (the tactic formerly called
# `progress`)

Round 3's second variant.  `AENEAS_FINDINGS.md` §3.3 set this tactic aside
for the `Refine` tier — "our lemmas have the shape *exact result on success*:
`h : rust_fn x = ok y ⊢ lean_fn (abs x) = abs y`.  That is forward reasoning
from a hypothesis; `step` wants a `⦃ ⦄` goal."  The arena's model is much
simpler than `con-ron-core`'s (no `Arc`, no `&mut`, no tuple-`let` trap, a
four-field `State` of flat `Vec`s), so the brief asks whether that changes
the verdict.

(In this Aeneas, `progress` is the deprecated spelling of `step` and
`@[progress]` of `@[step]`: `Aeneas/Tactic/Step/Deprecated.lean`.  Same
tactic, same attribute.)

**Two findings, and they point opposite ways.**

1. **On the arena's model `step` works, and works well.**  `bvar_demo` below
   is the `bvar` arm of `instantiate1` proved by `step*` and then
   `arena_grind`: `step*` walks the whole generated body, applies the nine
   `@[step]` specs of this file *and* Aeneas's own `U32.sub_spec`, and leaves
   exactly the same pure residue that `ExpC1Idiom.lean`'s `rust_norm` leaves
   — with the postconditions already named in the context.  §3.3's "not one
   proof script transferred" was about `con-ron-core`'s shapes, not about a
   flat arena.

2. **But `⦃ ⦄` is total correctness, and Theorem 2 is partial.**
   `Aeneas/Std/WP.lean:249`: `spec_imp_exists : spec m P → ∃ y, m = ok y ∧ P
   y`.  A `⦃ ⦄` goal *claims the call succeeds*.  Theorem 2 claims nothing
   when the Rust fails (con-leche's `SimAt`, `Verify/SimI.lean:244`; DESIGN
   §8.6), and the extracted `instantiate1` genuinely can fail: Aeneas models
   `Vec::push` as failing at `Usize.max`, and nothing bounds the memo — `GWF`
   bounds the three constructor arrays, and the fuel bounds how often the
   memo grows per call, not how long it is.  `memo_set_step_spec` below is
   the first spec in the file that needs a hypothesis, and `MemoCapShape`
   says what the walk's version of that hypothesis would have to be: a bound
   that is **exponential in the fuel**, since a call at fuel `f + 1` makes
   two calls at fuel `f` and each may insert.  At con-ron's fuel that
   premise is unsatisfiable, so the `step`-shaped statement is not C1 and is
   not a useful theorem either.

So: `step` is usable *inside* an arm (and is a fine alternative to
`rust_norm` there), and is not usable for the theorem.  P5 should read
finding 1 as "either normaliser works" and finding 2 as "the top-level
statement stays `h : rust = ok y ⊢ …`".

**One trap worth recording.** `lake env lean` on a single file does *not*
apply `proof/lakefile.toml`'s `[leanOptions]`, and without
`backward.do.legacy` every `step` here fails with "Could not unify the
theorem with the target".  The two `set_option`s below make the file behave
the same under `lake env lean` and under `lake build`.
-/
import ConRon.Arena.Spike.ExpC1Idiom

namespace ConRon.Arena.Spike

open ConLeche Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.do.legacy true

/-! `attribute [-grind]` does not travel through an import, so
`ExpC1Idiom.lean`'s erasure of Aeneas's two `@[grind ext]` machine-word
lemmas has to be repeated here.  Without it the `arena_grind` below closes
its goals with a `decide`-by-`rfl` step the kernel rejects — see
`ExpC1Idiom.lean` §"The scalar dictionary". -/
attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

/-! ## The primitives as Aeneas `@[step]` specs

Each is `exists_imp_spec` applied to the existential `MiniAbs.lean` already
proves, which is what makes them one-liners: Aeneas's spec shape and the
refinement tier's forward shape are *the same statement* up to that bridge —
**for a call that cannot fail**.  All nine of these cannot. -/

@[step] theorem tag_of_step_spec (h : U32) :
    Generated.tag_of h ⦃ t => absU t = mTagOf (absU h) ⦄ :=
  exists_imp_spec (abs_tag h)

@[step] theorem idx_of_step_spec (h : U32) :
    Generated.idx_of h ⦃ i => absU i = mIdxOf (absU h) ⦄ :=
  exists_imp_spec (abs_idx h)

@[step] theorem view_bvar_step_spec (st : Generated.State) (h : U32) :
    Generated.view_bvar st h ⦃ o => (absState st).viewBvar (absU h) = o.map absU ⦄ :=
  exists_imp_spec (abs_view_bvar st h)

@[step] theorem view_app_step_spec (st : Generated.State) (h : U32) :
    Generated.view_app st h
      ⦃ o => (absState st).viewApp (absU h) = o.map (fun p => (absU p.1, absU p.2)) ⦄ :=
  exists_imp_spec (abs_view_app st h)

@[step] theorem view_lam_step_spec (st : Generated.State) (h : U32) :
    Generated.view_lam st h
      ⦃ o => (absState st).viewLam (absU h) = o.map (fun p => (absU p.1, absU p.2)) ⦄ :=
  exists_imp_spec (abs_view_lam st h)

@[step] theorem memo_get_step_spec (st : Generated.State) (h d : U32) :
    Generated.memo_get st h d
      ⦃ o => mMemoGet (absState st) (absU h) (absU d) = o.map absU ⦄ :=
  exists_imp_spec (abs_memo_get st h d)

@[step] theorem intern_bvar_step_spec (st : Generated.State) (hwf : GWF st) (k : U32) :
    Generated.intern_bvar st k ⦃ p => GWF p.2 ∧ ∀ r, p.1 = some r →
      (mInternBvar (absU k)).run (absState st) = .ok (absU r, absState p.2) ⦄ := by
  obtain ⟨o, st', h1, h2, h3⟩ := abs_intern_bvar st hwf k
  exact exists_imp_spec ⟨(o, st'), h1, h2, h3⟩

@[step] theorem intern_app_step_spec (st : Generated.State) (hwf : GWF st) (f a : U32) :
    Generated.intern_app st f a ⦃ p => GWF p.2 ∧ ∀ r, p.1 = some r →
      (mInternApp (absU f) (absU a)).run (absState st) = .ok (absU r, absState p.2) ⦄ := by
  obtain ⟨o, st', h1, h2, h3⟩ := abs_intern_app st hwf f a
  exact exists_imp_spec ⟨(o, st'), h1, h2, h3⟩

@[step] theorem intern_lam_step_spec (st : Generated.State) (hwf : GWF st) (ty b : U32) :
    Generated.intern_lam st ty b ⦃ p => GWF p.2 ∧ ∀ r, p.1 = some r →
      (mInternLam (absU ty) (absU b)).run (absState st) = .ok (absU r, absState p.2) ⦄ := by
  obtain ⟨o, st', h1, h2, h3⟩ := abs_intern_lam st hwf ty b
  exact exists_imp_spec ⟨(o, st'), h1, h2, h3⟩

/-! ## The tenth primitive: the one that can fail

`memo_set` is `Vec::push`, which Aeneas models as failing at `Usize.max`, so
its `⦃ ⦄` spec needs a capacity hypothesis.  That hypothesis *is* the whole
difference between `step` and the forward idiom: `MiniAbs.abs_memo_set` takes
the success as a hypothesis and needs nothing. -/

@[step] theorem memo_set_step_spec (st : Generated.State) (h d r : U32)
    (hcap : st.memo.val.length < Usize.max) :
    Generated.memo_set st h d r ⦃ st' => absState st' = { absState st with
      memo := (absState st).memo ++ [(absU h, absU d, absU r)] } ∧ (GWF st → GWF st') ⦄ := by
  obtain ⟨w, hw1, hw2⟩ := spec_imp_exists (alloc.vec.Vec.push_spec st.memo
    ({ key_h := h, key_d := d, val := r } : Generated.MemoEntry) hcap)
  have hms : Generated.memo_set st h d r = .ok { st with memo := w } := by
    unfold Generated.memo_set; rw [hw1, bind_tc_ok]
  exact exists_imp_spec ⟨{ st with memo := w }, hms, abs_memo_set st _ h d r hms⟩

/-! ## Finding 1: `step` does walk the arena's body

The `bvar` arm, end to end, by `step*` and the same `arena_grind`
`ExpC1Idiom.lean` uses.  Nothing else: no `rust_norm`, no hand matching.
This arm has no `memo_set`, so it *is* total — which is exactly why it can be
stated as a `⦃ ⦄` and why the other two arms cannot. -/

/-- con-leche: none — the `bvar` arm of C1, by `step*`. -/
theorem bvar_demo (st : Generated.State) (v fuel h d : U32) (m : Nat)
    (hwf : GWF st) (hm : absU fuel = m + 1) (htag : mTagOf (absU h) = mTagBvar) :
    Generated.instantiate1 st v fuel h d ⦃ p => GWF p.2 ∧ ∀ r, p.1 = some r →
      (mInstantiate1 (absU v) (absU fuel) (absU h) (absU d)).run (absState st)
        = .ok (absU r, absState p.2) ⦄ := by
  have hf0 : ¬ fuel = 0#u32 := by
    intro hc; rw [hc] at hm; simp [absU] at hm
  rw [Generated.instantiate1.eq_def, if_neg hf0, hm, mInstantiate1_run_succ, if_pos htag]
  step*
  all_goals arena_grind

/-! ## Finding 2: the premise the walk would need

`MemoCapShape` is the hypothesis a `⦃ ⦄`-shaped C1 would have to carry
through the induction.  It is stated, not claimed: the point is its *shape*.
`instantiate1` at fuel `f + 1` makes two calls at fuel `f`, each of which may
insert one memo entry, so the number of inserts a call may make is bounded by
`2 ^ f` and by nothing smaller — the memo is keyed on `(handle, depth)` and
the arena has `2 ^ 28` handles.  At con-ron's fuel that premise cannot be
discharged.

Restated: `spec` forces the theorem to say *the Rust succeeds*; Theorem 2
says *if the Rust succeeds*.  `exists_imp_spec`/`spec_imp_exists` is an
equivalence, so wherever the Rust provably succeeds the two shapes are
interchangeable (the nine specs above are proof of that) — and where it does
not, only the forward shape is available. -/

/-- con-leche: none — the premise a `step`-shaped C1 would carry.  Stated for
its shape; never claimed. -/
def MemoCapShape (st : Generated.State) (fuel : Nat) : Prop :=
  st.memo.val.length + 2 ^ fuel < Usize.max

/-! ## The axiom check -/

#print axioms bvar_demo

end ConRon.Arena.Spike
