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

2. **Finding 3 at a callee's ANSWER, not at the caller's argument.**  On a
   handle whose tag is not `sort` and which does NOT resolve, the port answers
   `Invalid` and the twin answers `internal` — two different mirrored kinds, so
   `AErrSim` fails.  The handle in question is `knot_whnf`'s own reduct, which
   no hypothesis of `KnotRel` mentions, and `AOut`'s `WF` slot is a predicate
   on the VALUE that cannot say `EResolves lst' w`.  So the statement carries
   `AnswerResolves`, below — *"the reduct the port produced resolves in any
   twin state related to the port's post-state"*.  It is task #97-P5-0's
   finding 3 met from the other side, and it is Theorem 1's to discharge
   (`StoreWF` plus "the checker never holds a dangling handle").

   **Only the non-`sort` arm needs it.**  The port's own dangling decline
   (`fail_dangling_e` under a `sort` tag) needs nothing: `view_of_tag_sort`
   says the twin's `view` answers `none` exactly there, and the twin's `none`
   arm is the same `internal` kind.
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

/-! ## Finding 3 at a callee's answer -/

/-- **"Whatever handle this call answered resolves in the twin."**  Task
#97-P5-0's finding 3 said the tag-first / view-first split needs `StoreWF` plus
"this handle resolves" at ≈ 60 sites, and carried it at the caller's ARGUMENT;
a body that dispatches on the tag of a handle a CALLEE produced needs the same
pair about the callee's answer, and no `Sim` conclusion can state it (`AOut`'s
`WF` is a predicate on the value alone, while `EResolves` names the twin
state).  So it is a hypothesis, and it is P3's to discharge from `StateOK`. -/
def AnswerResolves (pers : arena.store.PersTier)
    (p : core.result.Result arena.handle.EIdx kernel.core_types.CheckError ×
      arena.monad.AState) : Prop :=
  ∀ w, p.1 = .Ok w → ∀ lst', AStateRel pers p.2 lst' → EResolves lst' (absEIdx w)

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

/-! ## `ensureSort`'s run, split -/

/-- The twin's `ensureSort`, as a bind of the knot's `whnf` and one `view`
read: the `rfl`-level unfolding the refinement matches the port's two
`match`es against. -/
theorem ensureSort_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx)
    (lst : AState) :
    (ensureSort r fe d e).run lst
      = ((r.whnf d e).run lst) >>= fun p =>
          (match p.2.store.view p.1 with
           | some (.sort u) => .ok (u, p.2)
           | some _ => .error (Arena.CheckError.invalid "expected a sort")
           | none => .error (Arena.CheckError.internal
               "arena: dangling expression handle")) := by
  show ((do
      let w ← r.whnf d e
      let v ← Arena.view w
      match v with
      | .sort u => pure u
      | _ => Arena.fail (.invalid "expected a sort")) : AM LIdx).run lst = _
  rw [am_run_bind]
  cases hx : (r.whnf d e).run lst with
  | error er => rfl
  | ok p =>
    obtain ⟨w, lst1⟩ := p
    show ((do
        let v ← Arena.view w
        match v with
        | .sort u => pure u
        | _ => Arena.fail (.invalid "expected a sort")) : AM LIdx).run lst1
      = (match lst1.store.view w with
         | some (.sort u) => Except.ok (u, lst1)
         | some _ => Except.error (Arena.CheckError.invalid "expected a sort")
         | none => Except.error (Arena.CheckError.internal
             "arena: dangling expression handle"))
    rw [am_run_bind,
      show (Arena.view w).run lst1
          = (match lst1.store.view w with
             | some v => Except.ok (v, lst1)
             | none => Except.error (Arena.CheckError.internal
                 "arena: dangling expression handle")) from by
        show ((match lst1.store.view w with
                | some v => (pure v : AM ENodeView)
                | none => Arena.fail
                    (.internal "arena: dangling expression handle")).run lst1) = _
        cases lst1.store.view w <;> rfl]
    cases hv : lst1.store.view w with
    | none => rfl
    | some v => cases v <;> rfl

/-! ## `arena::core::ensure_sort` -/

/-- `arena::core::ensure_sort` against `Arena.ensureSort`: `r.whnf` and then one
view read.  The entry `ensure_sort_core` is this at `LANE_FULL`; since task
#97-P5-Core-2 there is no gated side condition to be vacuous there, because
`KnotRel.whnf` carries none.

`hout` is the module note's second finding: `ensure_sort` dispatches on the tag
of `knot_whnf`'s OWN answer, so finding 3's "this handle resolves" is owed
about the callee's result and not about `e`. -/
theorem ensure_sort_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f)
    (hout : ∀ p, arena.core.knot_whnf pers vis st mode lane fu fe depth e = ok p →
      AnswerResolves pers p)
    (hrun : arena.core.ensure_sort pers vis st mode lane fu fe depth e = ok o) :
    Sim absLIdx (fun _ => True) pers lst o
      (ensureSort (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) := by
  rw [arena.core.ensure_sort] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st1⟩ := p
  have hw := hk.whnf hrel hinv hctx hwf hres hf hp
  have htw := ensureSort_run (laneKnot (ConRon.Refine.absMode mode) lfe lane f)
    lfe (absU depth) (absEIdx e) lst
  cases r with
  | Err er =>
    have ho : (core.result.Result.Err er, st1) = o := Result.ok_injective hrun
    rw [← ho]
    exact AOut.err (AErrSim.of_eq (AErrSim.bind (Sim.apply_err hw) _) htw)
  | Ok w =>
    obtain ⟨lst1, hb1, hrel1, hinv1, hext1, -⟩ := Sim.apply hw
    -- the twin's run, all the way down to the one `view` the port reads
    have htw2 : (ensureSort (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)).run lst
        = (match lst1.store.view (absEIdx w) with
           | some (.sort u) => Except.ok (u, lst1)
           | some _ => Except.error (Arena.CheckError.invalid "expected a sort")
           | none => Except.error (Arena.CheckError.internal
               "arena: dangling expression handle")) := by
      rw [htw, hb1]; rfl
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hta := eidx_tag_abs ht
    by_cases hts : t = arena.handle.ETAG_SORT
    · -- the `sort` arm: the tag decides the view, both ways
      rw [if_pos hts] at hrun
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have htag : (absEIdx w).tag = ETag.sort := by
        rw [hta, hts]; exact etag_sort_abs
      have hvs : lst1.store.viewSort (absEIdx w) = q.map absLIdx := by
        have h2 := SimR.apply (view_sort_run hrel1 hq)
        rw [show (Arena.viewSort (absEIdx w)).run lst1
              = Except.ok (lst1.store.viewSort (absEIdx w), lst1) from rfl] at h2
        exact congrArg (fun z => z.1) (Except.ok.inj h2)
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
        refine AOut.err (AErrSim.internal
          (s := "arena: dangling expression handle") ?_)
        rw [htw2, hvw]
        rfl
      | some u =>
        rw [hqc] at hrun hvw
        have ho : (core.result.Result.Ok u, st1) = o := Result.ok_injective hrun
        rw [← ho]
        refine AOut.ok (lst' := lst1) ?_ hrel1 hinv1 hext1 trivial
        rw [htw2, hvw]
        rfl
    · -- the non-`sort` arm: the port declines as `Invalid`, so the twin must
      -- decline as `invalid` and not as the dangling `internal` — which is the
      -- module note's `hout`
      rw [if_neg hts] at hrun
      obtain ⟨s, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨v, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [fail_run hr1] at hrun
      have ho : (core.result.Result.Err
        (kernel.core_types.CheckError.Invalid v), st1) = o :=
        Result.ok_injective hrun
      rw [← ho]
      have hwres : EResolves lst1 (absEIdx w) := hout _ hp w rfl lst1 hrel1
      refine AOut.err (AErrSim.invalid (s := "expected a sort") ?_)
      obtain ⟨vw, hvw⟩ := Option.isSome_iff_exists.mp hwres
      rw [htw2, hvw]
      cases vw with
      | sort u =>
        exact absurd (EStore_tag_of_view_sort hvw)
          (by rw [hta]; intro hx
              exact hts (absU32_inj (by rw [hx, etag_sort_abs])))
      | _ => rfl

/-- **`arena::core::ensure_sort_core`, the Checker tier's seventh front door.**
Task #97-P5-Core §8: *"`ensure_sort_core` is the seventh (T) declaration and is
NOT an entry of `Core/Entries.lean`'s kind: `ensure_sort` is a body"*.  It is
`ensure_sort` at `LANE_FULL`, and `Refine2/Checker/**` takes this beside
`Core/Entries.lean`'s six. -/
theorem ensure_sort_core_refines {f : Nat} (hk : KnotRel f)
    {pers vis st mode fe lfe fu depth e lst o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hwf : StoreWF lst.store)
    (hres : EResolves lst (absEIdx e)) (hf : absU fu = f)
    (hout : ∀ p, arena.core.knot_whnf pers vis st mode arena.core.LANE_FULL fu fe
      depth e = ok p → AnswerResolves pers p)
    (hrun : arena.core.ensure_sort_core pers vis st mode fe fu depth e = ok o) :
    Sim absLIdx (fun _ => True) pers lst o
      (ensureSortCore (ConRon.Refine.absMode mode) lfe f (absU depth)
        (absEIdx e)) := by
  rw [arena.core.ensure_sort_core] at hrun
  have h := ensure_sort_refines hk hrel hinv hctx hwf hres hf hout hrun
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
