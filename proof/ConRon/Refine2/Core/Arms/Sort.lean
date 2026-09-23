/-
# `ConRon.Refine2.Core.Arms.Sort` — `ensure_sort`, the tier's first closed body

**Task #97-P5-Arms.**  Task #97-P5-Core §7 calls `ensure_sort_refines` *"the
smallest of the ten, and the natural first"*.  It is: one `knot_whnf` call, one
tag test and one projection.  Closing it nonetheless needed two things this
tier did not have, and both of them are findings rather than plumbing.

1. **The `view`/tag agreement, in the two directions `ensure_sort` reads it,
   and the second of them is task #97-P5-2 §10's ten-way `estore_view_tagOf`.**
   The port tests `w.tag() == ETAG_SORT`; the twin writes
   `match ← view w with | .sort u`.  `EStore_view_of_tag_sort` is the port's
   *positive* arm — **19 lines**, one constructor — and `EStore_view_tagOf` is
   the *negative* one, ten-way and general: *"`view` answers the view whose
   constructor is the handle's own tag"*, **77 lines** against that section's
   estimate of sixty, of which sixty-odd are `ETables.get`'s ten-arm `if`
   chain taken apart by `Arena/WFProofs.lean`'s own `tag_cases`.  **Both are
   UNCONDITIONAL — no `StoreWF`**, which confirms that section's reading:
   P5-0's finding 3 weakens to `EResolves` alone everywhere.
   `EStore_view_tagOf` **lives in `Specs.lean`** beside `view_run` and is
   here only because this tier may not edit that file.

2. **Finding 3 at a callee's ANSWER — gone with the twin fix (task
   #97-P5-Core round 4).**  The port tests the TAG of `knot_whnf`'s reduct and
   the twin used to read its VIEW, so at a dangling non-`sort` reduct the port
   said `Invalid` and the twin `internal`; the statement carried
   `AnswerResolves` for it.  Round 4's audit (task #97-P5-Core round 4 in
   DESIGN) found the same split at ≈ 60 sites of the knot and made the twin
   test the tag first everywhere the port does, so `ensure_sort_refines` is a
   lockstep statement over `AStateRel₀` with no resolution hypothesis at all.
   The port's own dangling decline (`fail_dangling_e` under a `sort` tag)
   needs nothing: `view_of_tag_sort` says the twin's `view` answers `none`
   exactly there, and the twin's `none` arm is the same `internal` kind.
-/
import ConRon.Refine2.Core.Eqns
import ConRon.Refine2.Core.Entries

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

set_option maxRecDepth 4000

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.ExprOps (EResolves)

/-! ## The `view` / tag agreement at the `sort` constructor -/

/-- **A `sort`-tagged handle's view IS its `sort` projection**, with no
`StoreWF`: `EStore.view`'s binder test fails, its tier select is
`EStore.viewSort`'s own, and `ETables.get`'s third arm is `ETables.getSort`
wrapped in the constructor.  This is the positive half of task #97-P5-2 §10's
`estore_view_tagOf`, at one constructor. -/
theorem EStore_view_of_tag_sort (st : EStore) (i : EIdx) (hi : i.tag = ETag.sort) :
    st.view i = (st.viewSort i).map ENodeView.sort := by
  have key : ∀ t : ETables, t.get i = (t.getSort i).map ENodeView.sort := by
    intro t
    rw [ETables.get, ETables.getSort,
      if_neg (by rw [hi]; simp [ETag.bvar, ETag.sort]),
      if_neg (by rw [hi]; simp [ETag.fvar, ETag.sort]),
      if_pos (by rw [hi]; rfl)]
    cases t.sorts.node? i.idxNat <;> rfl
  rw [EStore.view, EStore.viewSort,
    if_neg (by rw [ETag.isBind, hi]; simp [ETag.lam, ETag.forallE, ETag.sort])]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetSort]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl

/-! ## The tag/view agreement

`ETables_get_tagOf` and `EStore_view_tagOf` were written here and in task
#97-P5-3's `ExprOps/Read.lean` on the same day; **they live in
`Refine2/Specs.lean` now**, which is where this file's own note said they
belong, and this tier consumes them from there.  The migration was the
deletion that used to be here. -/

/-- **A `.sort` view comes only from a `sort`-tagged handle** — the negative
half the port's `else` arm (`Invalid`) needs: the twin must not succeed where
the port declines.  An instance of `EStore_view_tagOf`, since
`(ENodeView.sort u).tagOf` is `ETag.sort` by `rfl`. -/
theorem EStore_tag_of_view_sort {st : EStore} {i : EIdx} {u : LIdx}
    (h : st.view i = some (.sort u)) : i.tag = ETag.sort :=
  EStore_view_tagOf h

/-- `Arena.view`'s run, named: the store read, and the twin's `internal`
decline where the port raises `fail_dangling_e`.  `Core/Arms/Gated.lean`
spells this inline; it is a lemma here because three arms below want it. -/
theorem view_run_eq (h : EIdx) (lst : AState) :
    (Arena.view h).run lst
      = (match lst.store.view h with
         | some v => Except.ok (v, lst)
         | none => Except.error
             (Arena.CheckError.internal "arena: dangling expression handle")) := by
  show ((match lst.store.view h with
          | some v => (pure v : AM ENodeView)
          | none => Arena.fail
              (.internal "arena: dangling expression handle")).run lst) = _
  cases lst.store.view h <;> rfl

/-! ## `ensureSort`'s run, split -/

/-- The twin's `ensureSort` — since task #97-P5-Core round 4, **tag first**, as
the port's `ensure_sort` is: the knot's `whnf`, then the reduct's TAG, and only
under a `sort` tag one `view` read.  This is the `rfl`-level unfolding the
refinement matches the port's two `if`/`match`es against. -/
theorem ensureSort_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx)
    (lst : AState) :
    (ensureSort r fe d e).run lst
      = ((r.whnf d e).run lst) >>= fun p =>
          if p.1.tag == ETag.sort then
            (match p.2.store.view p.1 with
             | some (.sort u) => .ok (u, p.2)
             | some _ => .error (Arena.CheckError.invalid "expected a sort")
             | none => .error (Arena.CheckError.internal
                 "arena: dangling expression handle"))
          else .error (Arena.CheckError.invalid "expected a sort") := by
  show ((do
      let w ← r.whnf d e
      if w.tag == ETag.sort then
        match ← Arena.view w with
        | .sort u => pure u
        | _ => Arena.fail (.invalid "expected a sort")
      else Arena.fail (.invalid "expected a sort")) : AM LIdx).run lst = _
  rw [am_run_bind]
  cases hx : (r.whnf d e).run lst with
  | error er => rfl
  | ok p =>
    obtain ⟨w, lst1⟩ := p
    show ((if w.tag == ETag.sort then
        (do
          match ← Arena.view w with
          | .sort u => pure u
          | _ => Arena.fail (.invalid "expected a sort"))
      else Arena.fail (.invalid "expected a sort")) : AM LIdx).run lst1
      = (if w.tag == ETag.sort then
          (match lst1.store.view w with
           | some (.sort u) => .ok (u, lst1)
           | some _ => .error (Arena.CheckError.invalid "expected a sort")
           | none => .error (Arena.CheckError.internal
               "arena: dangling expression handle"))
        else .error (Arena.CheckError.invalid "expected a sort"))
    by_cases ht : (w.tag == ETag.sort) = true
    · rw [if_pos ht, if_pos ht, am_run_bind, view_run_eq]
      cases hv : lst1.store.view w with
      | none => rfl
      | some v => cases v <;> rfl
    · rw [if_neg ht, if_neg ht]; rfl

/-! ## `arena::core::ensure_sort` -/

/-- `arena::core::ensure_sort` against `Arena.ensureSort` — a LOCKSTEP
statement (task #97-P5-Core round 4): over `AStateRel₀`, with no `StoreWF`, no
`EResolves` of the argument and no `AnswerResolves` of the reduct.  The last of
those was task #97-P5-Arms' finding 14 — the port tested the reduct's TAG and
the twin read its VIEW, so at a dangling non-`sort` reduct the port said
`Invalid` and the twin `internal` — and it is gone because the twin now tests
the tag too.  The entry `ensure_sort_core` is this at `LANE_FULL`. -/
theorem ensure_sort_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.ensure_sort pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absLIdx pers lst o
      (ensureSort (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) := by
  rw [arena.core.ensure_sort] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st1⟩ := p
  have hw := hk.whnf hrel hinv hctx hf hp
  have htw := ensureSort_run (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
    lfe (absU depth) (absEIdx e) lst
  cases r with
  | Err er =>
    have ho : (core.result.Result.Err er, st1) = o := Result.ok_injective hrun
    rw [← ho]
    exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hw) _) htw)
  | Ok w =>
    obtain ⟨lst1, hb1, hrel1, hinv1⟩ := Sim₀.apply hw
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hta := eidx_tag_abs ht
    by_cases hts : t = arena.handle.ETAG_SORT
    · -- the `sort` arm: the tag decides the view, both ways
      rw [if_pos hts] at hrun
      have htag : (absEIdx w).tag = ETag.sort := by
        rw [hta, hts]; exact etag_sort_abs
      have htw2 : (ensureSort (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
          (absU depth) (absEIdx e)).run lst
          = (match lst1.store.view (absEIdx w) with
             | some (.sort u) => Except.ok (u, lst1)
             | some _ => Except.error (Arena.CheckError.invalid "expected a sort")
             | none => Except.error (Arena.CheckError.internal
                 "arena: dangling expression handle")) := by
        rw [htw, hb1]
        show (if (absEIdx w).tag == ETag.sort then _ else _) = _
        rw [if_pos (by rw [htag]; rfl)]
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hvs : lst1.store.viewSort (absEIdx w) = q.map absLIdx := by
        rw [arena.monad.view_sort] at hq
        exact estore_view_sort_abs hrel1.store hq
      have hvw := EStore_view_of_tag_sort lst1.store (absEIdx w) htag
      rw [hvs] at hvw
      cases hqc : q with
      | none =>
        -- the port's dangling decline; `view_of_tag_sort` says the twin's
        -- `view` is `none` there too, and the two `internal`s match
        rw [hqc] at hrun hvw
        rw [arena.monad.fail_dangling_e] at hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨s, -, hr1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr1
        obtain ⟨v, -, hr1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr1
        rw [fail_run hr1] at hrun
        have ho : (core.result.Result.Err
          (kernel.core_types.CheckError.Internal v), st1) = o :=
          Result.ok_injective hrun
        rw [← ho]
        refine AOut₀.err (AErrSim.internal
          (s := "arena: dangling expression handle") ?_)
        rw [htw2, hvw]
        rfl
      | some u =>
        rw [hqc] at hrun hvw
        have ho : (core.result.Result.Ok u, st1) = o := Result.ok_injective hrun
        rw [← ho]
        refine AOut₀.ok (lst' := lst1) ?_ hrel1 hinv1
        rw [htw2, hvw]
        rfl
    · -- the non-`sort` arm: both decline as `Invalid`, off the tag alone
      rw [if_neg hts] at hrun
      obtain ⟨s, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨v, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [fail_run hr1] at hrun
      have ho : (core.result.Result.Err
        (kernel.core_types.CheckError.Invalid v), st1) = o :=
        Result.ok_injective hrun
      rw [← ho]
      refine AOut₀.err (AErrSim.invalid (s := "expected a sort") ?_)
      rw [htw, hb1]
      show (if (absEIdx w).tag == ETag.sort then _ else _) = _
      rw [if_neg (fun hx => hts (absU32_inj (by
        rw [← eidx_tag_abs ht, etag_sort_abs]; exact beq_iff_eq.mp hx)))]

/-- **`arena::core::ensure_sort_core`, the Checker tier's seventh front door.**
Task #97-P5-Core §8: *"`ensure_sort_core` is the seventh (T) declaration and is
NOT an entry of `Core/Entries.lean`'s kind: `ensure_sort` is a body"*.  It is
`ensure_sort` at `LANE_FULL`, and `Refine2/Checker/**` takes this beside
`Core/Entries.lean`'s six. -/
theorem ensure_sort_core_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode fe lfe fu depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.ensure_sort_core pers vis st mode fe fu depth e = ok o) :
    Sim₀ absLIdx pers lst o
      (ensureSortCore (ConRon.Refine.absMode mode) lfe f (absU depth)
        (absEIdx e)) := by
  rw [arena.core.ensure_sort_core] at hrun
  have h := ensure_sort_refines hk hrel hinv hctx hf hrun
  rw [laneKnot_full] at h
  exact h

section Axioms

/-- info: 'ConRon.Refine2.EStore_view_of_tag_sort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EStore_view_of_tag_sort

/-- info: 'ConRon.Refine2.EStore_tag_of_view_sort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EStore_tag_of_view_sort

/-- info: 'ConRon.Refine2.ensureSort_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ensureSort_run

/-- info: 'ConRon.Refine2.ensure_sort_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ensure_sort_refines

/-- info: 'ConRon.Refine2.ensure_sort_core_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ensure_sort_core_refines

end Axioms

end ConRon.Refine2
