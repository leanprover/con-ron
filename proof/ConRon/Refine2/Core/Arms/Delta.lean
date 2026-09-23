/-
# `ConRon.Refine2.Core.Arms.Delta` — the `whnf` loop's delta leaf

**Task #97-P5-Core-2.**  `Core/Arms/Loops.lean` closed the `whnf` loop modulo
its two leaves and named them: `reduce_nat` (the literal acceleration) and
`unfold_definition` (one delta step).  This file is the second of the two, and
the four things it needed that the tier did not have.

## 1. The environment index's reader

`unfold_definition` is the first body of the tier to READ the environment, and
`arena::env::ifenv_find` is where the port's shape differs from the twin's:
task #97-P6-5's lever 1 split the index's value in two, so the Rust's index
answers `(counter, position)` and reads the constant out of `env.consts` at
that position, where the twin's index answers `(counter, constant)`.
`Refine2/AbsState.lean`'s `IFEnvRel.idx` composes the probe with the array
read, and `ifenv_find_abs` below is that clause spent: **one equation,
`o.map absIConstantInfo = lfe.find? (absNIdx n)`**, and the visibility test is
`CoreCtx.vis` on both sides.

It wants two clauses `CoreCtx` did not carry — the index's `HashMap2.Inv`
(without which a probe specifies nothing) and "a stored position fits a
`usize`" (the `pos as usize` cast).  Both are `IFEnvInv`'s and P3's; see
`Core/KnotRel.lean`'s note.

## 2. The tag/view agreement at `const`

`unfold_definition` dispatches on `get_app_fn`'s answer's TAG and the twin
reads its VIEW, which is task #97-P5-0's finding 3 at a callee's answer once
more (`Core/Arms/Sort.lean`'s §2).  `EStore_view_of_tag_const` is the `sort`
lemma of that file at the other constructor — nineteen lines, no `StoreWF` —
and the negative direction is `EStore_view_tagOf`, already general.

The same shape appears one store down: the port reads `view_ls_len` where the
twin reads `viewLs` and takes `.length`, and `LsStore_viewLen_eq` is the
projection's exactness lemma at the level-list store.

## 3. The port's split, transcribed

`arena::core::unfold_definition` is one Rust function against one twin
function, but the refinement still needs two local transcriptions — the tail
from the head handle on (`unfoldDefAt`) and the tail from the resolved
constant on (`unfoldDefConst`) — because the twin's `match ← view (← getAppFn
…)` binds the head and the view in one expression and no lemma can name the
intermediate otherwise.  Both are `rfl`-equal to what they transcribe
(`unfoldDefinition_unfold`), which is `ExprOps/Read.lean`'s `wscopedBGo`
shape and what task #97-P5-Arms §9 asked for at `defeqAfterWhnf`.

## 4. What is a HYPOTHESIS and why

`ExprOpsHyp` below, and every field of it is a theorem that exists elsewhere
and is **stated by name rather than cited**, so that `#print axioms` on
anything here shows the three standard axioms and no `sorryAx`:

* `instLPFast` — `Refine2/ExprOps/Mut.lean`'s `inst_lp_fast_refines`, P5-3's;
* `mkAppN` — `Refine2/ExprOps/Mut.lean`'s `mk_app_n_refines`, likewise;
* `mkAppNRes` and `headRes` — task #97-P5-Arms' finding 14 at two more call
  sites (*"the handle this callee answered resolves"*), P3's, exactly as
  `CoreAmbient.wf` is.

`const_val_at_refines` is NOT among them: the delta step's memo is this tier's
own, `Core/Probes.lean` grew its probe and its write (`const_val_probe_abs`,
`const_val_set_rel`), and the lemma is proved here modulo `instLPFast`.
-/
import ConRon.Refine2.Core.Arms.Sort
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine2.Dup

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

set_option maxRecDepth 4000

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.ExprOps (EResolves absEIdxList)

/-! ## The `view` / tag agreement at the `const` constructor -/

/-- **A `const`-tagged handle's view IS its `const` projection**, with no
`StoreWF` — `Core/Arms/Sort.lean`'s `EStore_view_of_tag_sort` at the other
constructor the tier dispatches on. -/
theorem EStore_view_of_tag_const (st : EStore) (i : EIdx)
    (hi : i.tag = ETag.const) :
    st.view i = (st.viewConst i).map (fun p => ENodeView.const p.1 p.2) := by
  have key : ∀ t : ETables,
      t.get i = (t.getConst i).map (fun p => ENodeView.const p.1 p.2) := by
    intro t
    rw [ETables.get, ETables.getConst,
      if_neg (by rw [hi]; simp [ETag.bvar, ETag.const]),
      if_neg (by rw [hi]; simp [ETag.fvar, ETag.const]),
      if_neg (by rw [hi]; simp [ETag.sort, ETag.const]),
      if_pos (by rw [hi]; rfl)]
    cases t.consts.node? i.idxNat <;> rfl
  rw [EStore.view, EStore.viewConst,
    if_neg (by rw [ETag.isBind, hi]; simp [ETag.lam, ETag.forallE, ETag.const])]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetConst]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl

/-- **A `.const` view comes only from a `const`-tagged handle** — the negative
half the port's `else` arm needs, an instance of `EStore_view_tagOf`. -/
theorem EStore_tag_of_view_const {st : EStore} {i : EIdx} {n : NIdx}
    {us : LsIdx} (h : st.view i = some (.const n us)) : i.tag = ETag.const :=
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

/-! ## The level-list length, as a projection of the view -/

/-- `LsStore.viewLen` IS the length of `LsStore.view` — task #97-P6-10's
length projection, exactly. -/
theorem LsStore_viewLen_eq (st : LsStore) (i : LsIdx) :
    st.viewLen i = (st.view i).map List.length := by
  have key : ∀ t : LsTables, t.getLen i = (t.get i).map List.length := by
    intro t
    rw [LsTables.getLen, LsTables.get]
    by_cases h : i.tag == LsTag.list
    · rw [if_pos h, if_pos h]; cases t.lists.node? i.idxNat <;> rfl
    · rw [if_neg h, if_neg h]; rfl
  rw [LsStore.viewLen, LsStore.view]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, LsStore.persGetLen]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl

/-- `Arena.viewLs`'s run: the store read, and the twin's own `internal`
decline where the port raises `fail_dangling_ls`. -/
theorem viewLs_run_eq (h : LsIdx) (lst : AState) :
    (Arena.viewLs h).run lst
      = (match lst.store.lss.view h with
         | some v => Except.ok (v, lst)
         | none => Except.error
             (Arena.CheckError.internal "arena: dangling level-list handle")) := by
  show ((do
      let s ← get
      match s.store.lss.view h with
      | some v => (pure v : AM LsNodeView)
      | none => Arena.fail (.internal "arena: dangling level-list handle")) :
      AM LsNodeView).run lst = _
  rw [run_get_bind]
  cases lst.store.lss.view h <;> rfl

/-- `CORE_WALK_FUEL = coreWalkFuel = 4 000 000 000` on both sides — the
`check_fuel_abs` of the walks, so the two leaves need no fuel hypothesis. -/
theorem core_walk_fuel_abs : absU arena.core.CORE_WALK_FUEL = coreWalkFuel := by
  rw [arena.core.CORE_WALK_FUEL, Arena.coreWalkFuel]
  rfl

/-! ## The environment index's one reader -/

/-- **`arena::env::ifenv_find` against `IFEnv.find?`.**  The port probes the
index for `(counter, position)` and reads `env.consts` at the position; the
twin's index holds the constant itself.  `IFEnvRel.idx` is that composition
and this lemma is it spent — see the module note. -/
theorem ifenv_find_abs {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx vis fe lfe) {n : arena.handle.NIdx}
    {o : Option arena.env.IConstantInfo}
    (hrun : arena.env.ifenv_find vis fe n = ok o) :
    o.map absIConstantInfo = lfe.find? (absNIdx n) := by
  rw [arena.env.ifenv_find] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hctx.idxInv
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hidx := hctx.idx n
  rw [← hto] at hidx
  cases hr2 : r with
  | none =>
    rw [hr2] at hrun hidx
    have ho : (none : Option arena.env.IConstantInfo) = o :=
      Result.ok_injective hrun
    rw [← ho, IFEnv.find?, ← hidx]
    rfl
  | some p =>
    obtain ⟨c, pos⟩ := p
    rw [hr2] at hrun hidx
    -- the port's `match` on a literal `some`, and the twin's `Option.bind`
    -- on the same, both by `rfl`
    replace hrun : (if c < vis then
        (do
          let i2 ← lift (Std.UScalar.cast .Usize pos)
          if i2 < alloc.vec.Vec.len fe.env.consts then
            (do
              let i4 ← lift (Std.UScalar.cast .Usize pos)
              let ii ← alloc.vec.Vec.index
                (core.slice.index.SliceIndexUsizeSlice arena.env.IConstantInfo)
                fe.env.consts i4
              ok (some ii))
          else ok none)
      else (ok none : Result (Option arena.env.IConstantInfo))) = ok o := hrun
    replace hidx : Option.map (fun ci => (absU c, absIConstantInfo ci))
        fe.env.consts.val[pos.val]? = lfe.idx[absNIdx n]? := hidx
    have hposfit : pos.val ≤ Std.Usize.max :=
      hctx.idxPos n (c, pos) (hto.symm.trans hr2)
    have hlen : (alloc.vec.Vec.len fe.env.consts).val
        = fe.env.consts.val.length := alloc.vec.Vec.len_val _
    by_cases hc : c < vis
    · rw [if_pos hc] at hrun
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v : i2.val = pos.val := by
        rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hposfit]
        exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi2).symm
      have hcv : absU c < lfe.visibleBelow := by
        rw [← hctx.vis]
        exact (Std.UScalar.lt_equiv c vis).mp hc
      by_cases hb : i2 < alloc.vec.Vec.len fe.env.consts
      · rw [if_pos hb] at hrun
        obtain ⟨i4, hi4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨ii, hii, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have ho : some ii = o := Result.ok_injective hrun
        have hi4v : i4.val = pos.val := by
          rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hposfit]
          exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi4).symm
        obtain ⟨hlt, hne⟩ := ConRon.Refine.ExprOps.vec_index_val hii
        simp only [hi4v] at hlt hne
        rw [List.getElem?_eq_getElem hlt] at hidx
        rw [← ho, hne, IFEnv.find?, ← hidx]
        simp only [Option.map_some]
        rw [if_pos hcv]
      · rw [if_neg hb] at hrun
        have ho : (none : Option arena.env.IConstantInfo) = o :=
          Result.ok_injective hrun
        have hge : fe.env.consts.val.length ≤ pos.val := by
          have hnl : ¬ (i2.val < (alloc.vec.Vec.len fe.env.consts).val) := by
            intro hxx; exact hb ((Std.UScalar.lt_equiv _ _).mpr hxx)
          rw [hlen] at hnl
          omega
        rw [List.getElem?_eq_none hge] at hidx
        rw [← ho, IFEnv.find?, ← hidx]
        rfl
    · rw [if_neg hc] at hrun
      have ho : (none : Option arena.env.IConstantInfo) = o :=
        Result.ok_injective hrun
      have hcv : ¬ (absU c < lfe.visibleBelow) := by
        rw [← hctx.vis]
        intro hxx; exact hc ((Std.UScalar.lt_equiv c vis).mpr hxx)
      rw [← ho, IFEnv.find?, ← hidx]
      cases hg : fe.env.consts.val[pos.val]? with
      | none => rfl
      | some ci =>
        simp only [Option.map_some]
        rw [if_neg hcv]
        rfl

-- `nidx_vec_dup_val` moved down to `Refine2/Dup.lean` (task #97-P5-Front
-- round 2), beside the other `arena::env` copies.

/-! ## The `arena::expr_ops` lemmas this tier consumes, stated by name -/

/-- The `Option EIdx` form of `Core/Arms/Sort.lean`'s `AnswerResolves`: what
`reduce_nat` and `unfold_definition` owe about the reduct they hand back to
the `whnf` loop. -/
def AnswerResolvesOpt (pers : arena.store.PersTier)
    (p : core.result.Result (Option arena.handle.EIdx)
      kernel.core_types.CheckError × arena.monad.AState) : Prop :=
  ∀ w, p.1 = .Ok (some w) → ∀ lst', AStateRel pers p.2 lst' →
    EResolves lst' (absEIdx w)

/-- **What the `core` bodies borrow from the tier below**, as one structure so
that instantiating it is one edit — see the module note. -/
structure ExprOpsHyp (pers : arena.store.PersTier) : Prop where
  /-- `Refine2/ExprOps/Mut.lean`'s `inst_lp_fast_refines`. -/
  instLPFast : ∀ {st lst} {fuel : Std.U64}
    {lps : alloc.vec.Vec arena.handle.NIdx} {us : arena.handle.LsIdx}
    {value : arena.handle.EIdx} {o},
    AStateRel pers st lst → AStateInv pers st →
    arena.expr_ops.inst_lp_fast pers st fuel lps us value = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (instLPFast (absU fuel) (lps.val.map absNIdx) (absLsIdx us)
        (absEIdx value))
  /-- `Refine2/ExprOps/Mut.lean`'s `mk_app_n_refines`. -/
  mkAppN : ∀ {st lst} {f : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {o},
    AStateRel pers st lst → AStateInv pers st →
    arena.expr_ops.mk_app_n pers st f args = ok o →
    Sim absEIdx (fun _ => True) pers lst o
      (Arena.mkAppN (absEIdx f) (absEIdxList args))
  /-- Finding 14 at the node `mk_app_n` INTERNED: the handle it answered
  resolves in any related twin state.  P3's, from `StoreWF` and the intern
  lemmas. -/
  mkAppNRes : ∀ {st} {f : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {p},
    arena.expr_ops.mk_app_n pers st f args = ok p → AnswerResolves pers p
  /-- Finding 14 at `get_app_fn`: **the head of a handle this run reaches
  resolves**.  `StoreWF`'s `childOK` is what proves it, and that is
  Theorem 1's. -/
  headRes : ∀ {st lst'} {fuel : Std.U64} {h w : arena.handle.EIdx},
    AStateRel pers st lst' →
    arena.expr_ops.get_app_fn pers st fuel h = ok (.Ok w) →
    EResolves lst' (absEIdx w)

/-! ## `const_val_at` — the delta step's memo

`Core/Probes.lean`'s seventh probe and its write, spent.  The twin writes the
table INLINE (there is no `constValSet`), which is why the two halves are
spelled here rather than named. -/

/-- The twin's `constValAt`, split at its probe. -/
theorem constValAt_split (n : NIdx) (lps : List NIdx) (value : EIdx)
    (us : LsIdx) (lst : AState) :
    (constValAt n lps value us).run lst
      = (((match lst.caches.constValC[(n, us)]? with
            | some r => pure r
            | none => do
                let r ← instLPFast coreWalkFuel lps us value
                let s ← get
                let mp := s.caches.constValC
                let mp := if mp.size < cacheCap then mp else ∅
                let s := { s with caches := { s.caches with constValC := ∅ } }
                set { s with caches :=
                  { s.caches with constValC := mp.insert (n, us) r } }
                pure r) : AM EIdx)).run lst := by
  rw [Arena.constValAt]; rfl

theorem constValAt_hit (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx)
    (lst : AState) (x : EIdx) (h : lst.caches.constValC[(n, us)]? = some x) :
    (constValAt n lps value us).run lst = .ok (x, lst) := by
  rw [constValAt_split, h]; rfl

theorem constValAt_miss (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx)
    (lst : AState) (h : lst.caches.constValC[(n, us)]? = none) :
    (constValAt n lps value us).run lst
      = (((do
            let r ← instLPFast coreWalkFuel lps us value
            let s ← get
            let mp := s.caches.constValC
            let mp := if mp.size < cacheCap then mp else ∅
            let s := { s with caches := { s.caches with constValC := ∅ } }
            set { s with caches :=
              { s.caches with constValC := mp.insert (n, us) r } }
            pure r) : AM EIdx)).run lst := by
  rw [constValAt_split, h]

/-- **`arena::core::const_val_at` against `Arena.constValAt`** — the memo pair
of `Core/Probes.lean` in front of P5-3's `inst_lp_fast_refines`. -/
theorem const_val_at_refines {pers st lst} {n : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {value : arena.handle.EIdx}
    {us : arena.handle.LsIdx} {o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.const_val_at pers st n lps value us = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (constValAt (absNIdx n) (lps.val.map absNIdx) (absEIdx value)
        (absLsIdx us)) := by
  have hfuel := core_walk_fuel_abs
  rw [arena.core.const_val_at] at hrun
  obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hprobe := const_val_probe_abs hrel hinv hop
  rw [nls_key_abs hk] at hprobe
  cases hoc : op with
  | some x =>
    rw [hoc] at hrun hprobe
    have ho : (core.result.Result.Ok x, st) = o := Result.ok_injective hrun
    rw [← ho]
    exact AOut.ok (constValAt_hit _ _ _ _ _ _ hprobe.symm) hrel hinv
      (Ext.refl _) trivial
  | none =>
    rw [hoc] at hrun hprobe
    obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, st1⟩ := q
    have hbody := hx.instLPFast hrel hinv hq
    rw [hfuel] at hbody
    have htw := (constValAt_miss (absNIdx n) (lps.val.map absNIdx) (absEIdx value)
      (absLsIdx us) lst hprobe.symm).trans
      (am_run_bind (instLPFast coreWalkFuel (lps.val.map absNIdx) (absLsIdx us)
        (absEIdx value)) _ lst)
    cases r with
    | Err er =>
      have ho : (core.result.Result.Err er, st1) = o := Result.ok_injective hrun
      rw [← ho]
      exact AOut.err (AErrSim.of_eq (AErrSim.bind (Sim.apply_err hbody) _) htw)
    | Ok r1 =>
      obtain ⟨lst1, hb1, hrel1, hinv1, hext1, -⟩ := Sim.apply hbody
      obtain ⟨st2, hs2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have ho : (core.result.Result.Ok r1, st2) = o := Result.ok_injective hrun
      rw [← ho]
      obtain ⟨hrel2, hinv2⟩ := const_val_set_rel hrel1 hinv1 hs2
      rw [nls_key_abs hk] at hrel2
      refine AOut.ok ?_ hrel2 hinv2 hext1 trivial
      rw [htw, hb1]
      rfl

/-! ## `unfold_definition` — the delta step

The port's own split, transcribed: `unfoldDefAt` is `unfoldDefinition`'s tail
from the head handle on (the port tests `get_app_fn`'s answer's tag there),
`unfoldDefConst` its tail from the resolved constant on, and `unfoldDefGo` the
three calls the length test licenses.  All three are `rfl`-equal to the twin
they transcribe, which is `ExprOps/Read.lean`'s `wscopedBGo` shape. -/

/-- The three calls `unfoldDefinition` makes once the level-arity test passes. -/
def unfoldDefGo (e : EIdx) (n : NIdx) (lps : List NIdx) (value : EIdx)
    (us : LsIdx) : AM (Option EIdx) := do
  let v ← constValAt n lps value us
  let args ← getAppArgs coreWalkFuel e
  let r ← Arena.mkAppN v args
  pure (some r)

/-- `unfoldDefinition`'s tail from the resolved constant on. -/
def unfoldDefConst (fe : IFEnv) (e : EIdx) (n : NIdx) (us : LsIdx) :
    AM (Option EIdx) := do
  match fe.find? n with
  | some (.defnInfo cv value _) => do
    let usl ← Arena.viewLs us
    if usl.length = cv.levelParams.length then
      unfoldDefGo e n cv.levelParams value us
    else pure none
  | _ => pure none

/-- `unfoldDefinition`'s tail from the head handle on — the port's own split
point (`unfold_definition` tests the TAG of `get_app_fn`'s answer). -/
def unfoldDefAt (fe : IFEnv) (e h : EIdx) : AM (Option EIdx) := do
  match ← Arena.view h with
  | .const n us => unfoldDefConst fe e n us
  | _ => pure none

/-- The `_unfold` equation back to the twin. -/
theorem unfoldDefinition_unfold (fe : IFEnv) (e : EIdx) :
    unfoldDefinition fe e = (do
      let h ← getAppFn coreWalkFuel e
      unfoldDefAt fe e h) := rfl

theorem unfoldDefGo_run (e : EIdx) (n : NIdx) (lps : List NIdx) (value : EIdx)
    (us : LsIdx) (lst : AState) :
    (unfoldDefGo e n lps value us).run lst
      = ((constValAt n lps value us).run lst) >>= fun p =>
          ((getAppArgs coreWalkFuel e).run p.2) >>= fun q =>
            ((Arena.mkAppN p.1 q.1).run q.2) >>= fun r =>
              Except.ok (some r.1, r.2) := by
  show ((do
      let v ← constValAt n lps value us
      let args ← getAppArgs coreWalkFuel e
      let r ← Arena.mkAppN v args
      pure (some r)) : AM (Option EIdx)).run lst = _
  rw [am_run_bind]
  cases (constValAt n lps value us).run lst with
  | error er => rfl
  | ok p =>
    obtain ⟨v, lst1⟩ := p
    show ((do
        let args ← getAppArgs coreWalkFuel e
        let r ← Arena.mkAppN v args
        pure (some r)) : AM (Option EIdx)).run lst1
      = ((getAppArgs coreWalkFuel e).run lst1) >>= fun q =>
          ((Arena.mkAppN v q.1).run q.2) >>= fun r =>
            Except.ok (some r.1, r.2)
    rw [am_run_bind]
    cases (getAppArgs coreWalkFuel e).run lst1 with
    | error er => rfl
    | ok q =>
      obtain ⟨args, lst2⟩ := q
      show ((do
          let r ← Arena.mkAppN v args
          pure (some r)) : AM (Option EIdx)).run lst2
        = ((Arena.mkAppN v args).run lst2) >>= fun r =>
            Except.ok (some r.1, r.2)
      rw [am_run_bind]
      cases (Arena.mkAppN v args).run lst2 with
      | error er => rfl
      | ok r => rfl

theorem unfoldDefConst_run (fe : IFEnv) (e : EIdx) (n : NIdx) (us : LsIdx)
    (lst : AState) :
    (unfoldDefConst fe e n us).run lst
      = (match fe.find? n with
         | some (.defnInfo cv value _) =>
           (match lst.store.lss.view us with
            | none => Except.error
                (Arena.CheckError.internal "arena: dangling level-list handle")
            | some usl =>
              if usl.length = cv.levelParams.length then
                (unfoldDefGo e n cv.levelParams value us).run lst
              else Except.ok (none, lst))
         | _ => Except.ok (none, lst)) := by
  rw [unfoldDefConst]
  cases hf : fe.find? n with
  | none => rfl
  | some ci =>
    cases ci with
    | defnInfo cv value hint =>
      show ((do
          let usl ← Arena.viewLs us
          if usl.length = cv.levelParams.length then
            unfoldDefGo e n cv.levelParams value us
          else pure none) : AM (Option EIdx)).run lst
        = (match lst.store.lss.view us with
           | none => Except.error (Arena.CheckError.internal
               "arena: dangling level-list handle")
           | some usl =>
             if usl.length = cv.levelParams.length then
               (unfoldDefGo e n cv.levelParams value us).run lst
             else Except.ok (none, lst))
      rw [am_run_bind, viewLs_run_eq]
      cases lst.store.lss.view us with
      | none => rfl
      | some usl =>
        show ((if usl.length = cv.levelParams.length then
                 unfoldDefGo e n cv.levelParams value us
               else (pure none : AM (Option EIdx))).run lst)
          = (if usl.length = cv.levelParams.length then
               (unfoldDefGo e n cv.levelParams value us).run lst
             else Except.ok (none, lst))
        by_cases hl : usl.length = cv.levelParams.length
        · rw [if_pos hl, if_pos hl]
        · rw [if_neg hl, if_neg hl]; rfl
    | axiomInfo _ => rfl
    | thmInfo _ _ => rfl
    | indInfo _ _ => rfl
    | ctorInfo _ _ _ => rfl
    | recInfo _ _ _ _ => rfl
    | projInfo _ => rfl

theorem unfoldDefAt_run (fe : IFEnv) (e h : EIdx) (lst : AState) :
    (unfoldDefAt fe e h).run lst
      = (match lst.store.view h with
         | none => Except.error
             (Arena.CheckError.internal "arena: dangling expression handle")
         | some (.const n us) => (unfoldDefConst fe e n us).run lst
         | some _ => Except.ok (none, lst)) := by
  show ((do
      let v ← Arena.view h
      match v with
      | .const n us => unfoldDefConst fe e n us
      | _ => pure none) : AM (Option EIdx)).run lst = _
  rw [am_run_bind, view_run_eq]
  cases hv : lst.store.view h with
  | none => rfl
  | some v => cases v <;> rfl

/-- **`arena::core::unfold_definition` against `Arena.unfoldDefinition`** — one
delta step, and the `whnf` loop's second leaf.  Closed modulo `ExprOpsHyp`
(P5-3's `inst_lp_fast_refines` and `mk_app_n_refines`, plus finding 14 at two
call sites) and `CoreCtx`'s two index clauses; no `sorry`. -/
theorem unfold_definition_refines {pers vis st fe lfe e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe)
    (hrun : arena.core.unfold_definition pers vis st fe e = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (unfoldDefinition lfe (absEIdx e))
    ∧ AnswerResolvesOpt pers o := by
  have hfuel := core_walk_fuel_abs
  rw [arena.core.unfold_definition] at hrun
  obtain ⟨rh, hrh, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have htw0 : (unfoldDefinition lfe (absEIdx e)).run lst
      = ((getAppFn coreWalkFuel (absEIdx e)).run lst) >>= fun p =>
          (unfoldDefAt lfe (absEIdx e) p.1).run p.2 := by
    rw [unfoldDefinition_unfold]
    exact am_run_bind _ _ lst
  have hfn := ExprOps.get_app_fn_refines hrel hinv hrh
  rw [hfuel] at hfn
  cases rh with
  | Err er =>
    have ho : (core.result.Result.Err (T := Option arena.handle.EIdx) er, st) = o :=
      Result.ok_injective hrun
    refine ⟨?_, ?_⟩
    · rw [← ho]
      exact AOut.err (AErrSim.of_eq (AErrSim.bind (AOut.destErr hfn) _) htw0)
    · intro w hw; rw [← ho] at hw; simp at hw
  | Ok h =>
    obtain ⟨lst0, hb0, hrel0, hinv0, hext0, -⟩ := AOut.dest hfn
    have htw1 : (unfoldDefinition lfe (absEIdx e)).run lst
        = (unfoldDefAt lfe (absEIdx e) (absEIdx h)).run lst0 := by
      rw [htw0, hb0]; rfl
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hta := eidx_tag_abs ht
    by_cases hts : t = arena.handle.ETAG_CONST
    · rw [if_pos hts] at hrun
      have htag : (absEIdx h).tag = ETag.const := by
        rw [hta, hts]; exact etag_const_abs
      obtain ⟨oc, hoc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hvc : lst0.store.viewConst (absEIdx h) = oc.map absConstT := by
        have h2 := SimR.apply (view_const_run hrel0 hoc)
        rw [show (Arena.viewConst (absEIdx h)).run lst0
              = Except.ok (lst0.store.viewConst (absEIdx h), lst0) from rfl] at h2
        exact congrArg (fun z => z.1) (Except.ok.inj h2)
      have hvw := EStore_view_of_tag_const lst0.store (absEIdx h) htag
      rw [hvc] at hvw
      cases hocc : oc with
      | none =>
        rw [hocc] at hrun hvw
        rw [arena.monad.fail_dangling_e] at hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨sl, -, hr1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr1
        obtain ⟨cps, -, hr1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr1
        rw [fail_run hr1] at hrun
        have ho : (core.result.Result.Err
          (T := Option arena.handle.EIdx)
          (kernel.core_types.CheckError.Internal cps), st) = o :=
          Result.ok_injective hrun
        refine ⟨?_, ?_⟩
        · rw [← ho]
          refine AOut.err (AErrSim.internal
            (s := "arena: dangling expression handle") ?_)
          rw [htw1, unfoldDefAt_run, hvw]
          rfl
        · intro w hw; rw [← ho] at hw; simp at hw
      | some p =>
        obtain ⟨n, us⟩ := p
        rw [hocc] at hrun hvw
        have htw2 : (unfoldDefinition lfe (absEIdx e)).run lst
            = (unfoldDefConst lfe (absEIdx e) (absNIdx n) (absLsIdx us)).run lst0 := by
          rw [htw1, unfoldDefAt_run, hvw]
          rfl
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hfind := ifenv_find_abs hctx ho1
        cases ho1c : o1 with
        | none =>
          rw [ho1c] at hrun hfind
          have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
              = o := Result.ok_injective hrun
          refine ⟨?_, ?_⟩
          · rw [← ho]
            refine AOut.ok (lst' := lst0) ?_ hrel0 hinv0 hext0 trivial
            rw [htw2, unfoldDefConst_run, ← hfind]
            rfl
          · intro w hw; rw [← ho] at hw; simp at hw
        | some ii =>
          rw [ho1c] at hrun hfind
          cases ii with
          | DefnInfo cv value hint =>
            obtain ⟨lps, hlps, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨val, hval, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨o2, ho2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hlpsv := nidx_vec_dup_val hlps
            have hvalv := dupId_eidx _ _ hval
            have hvl : lst0.store.lss.viewLen (absLsIdx us) = o2.map absSz := by
              have h2 := SimR.apply (view_ls_len_run hrel0 ho2)
              rw [show (Arena.viewLsLen (absLsIdx us)).run lst0
                    = Except.ok (lst0.store.lss.viewLen (absLsIdx us), lst0)
                  from rfl] at h2
              exact congrArg (fun z => z.1) (Except.ok.inj h2)
            rw [LsStore_viewLen_eq] at hvl
            have htw3 : (unfoldDefinition lfe (absEIdx e)).run lst
                = (match lst0.store.lss.view (absLsIdx us) with
                   | none => Except.error (Arena.CheckError.internal
                       "arena: dangling level-list handle")
                   | some usl =>
                     if usl.length = (cv.level_params.val.map absNIdx).length then
                       (unfoldDefGo (absEIdx e) (absNIdx n)
                         (cv.level_params.val.map absNIdx) (absEIdx value)
                         (absLsIdx us)).run lst0
                     else Except.ok (none, lst0)) := by
              rw [htw2, unfoldDefConst_run, ← hfind]
              rfl
            cases ho2c : o2 with
            | none =>
              rw [ho2c] at hrun hvl
              dsimp only at hrun
              rw [arena.monad.fail_dangling_ls] at hrun
              obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨sl, -, hr1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr1
              obtain ⟨cps, -, hr1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr1
              rw [fail_run hr1] at hrun
              have ho : (core.result.Result.Err
                (T := Option arena.handle.EIdx)
                (kernel.core_types.CheckError.Internal cps), st) = o :=
                Result.ok_injective hrun
              have hvn : lst0.store.lss.view (absLsIdx us) = none := by
                cases hq : lst0.store.lss.view (absLsIdx us) with
                | none => rfl
                | some l => rw [hq] at hvl; simp at hvl
              refine ⟨?_, ?_⟩
              · rw [← ho]
                refine AOut.err (AErrSim.internal
                  (s := "arena: dangling level-list handle") ?_)
                rw [htw3, hvn]
              · intro w hw; rw [← ho] at hw; simp at hw
            | some usl =>
              rw [ho2c] at hrun hvl
              dsimp only at hrun
              obtain ⟨l, hl, hll⟩ : ∃ l, lst0.store.lss.view (absLsIdx us) = some l
                  ∧ l.length = usl.val := by
                cases hq : lst0.store.lss.view (absLsIdx us) with
                | none => rw [hq] at hvl; simp at hvl
                | some l =>
                  rw [hq] at hvl
                  exact ⟨l, rfl, by simpa using hvl⟩
              have hlenlps : (alloc.vec.Vec.len lps).val
                  = (cv.level_params.val.map absNIdx).length := by
                rw [alloc.vec.Vec.len_val, List.length_map]
                exact congrArg List.length hlpsv
              by_cases hb : usl = alloc.vec.Vec.len lps
              · rw [if_pos hb] at hrun
                have hlt : l.length = (cv.level_params.val.map absNIdx).length := by
                  rw [hll, ← hlenlps, hb]
                have htw4 : (unfoldDefinition lfe (absEIdx e)).run lst
                    = (unfoldDefGo (absEIdx e) (absNIdx n)
                        (cv.level_params.val.map absNIdx) (absEIdx value)
                        (absLsIdx us)).run lst0 := by
                  rw [htw3, hl]
                  dsimp only
                  rw [if_pos hlt]
                rw [unfoldDefGo_run] at htw4
                obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                obtain ⟨rv, st1⟩ := q1
                have hcva := const_val_at_refines hx hrel0 hinv0 hq1
                rw [hlpsv, hvalv] at hcva
                cases rv with
                | Err er =>
                  have ho : (core.result.Result.Err
                    (T := Option arena.handle.EIdx) er, st1) = o :=
                    Result.ok_injective hrun
                  refine ⟨?_, ?_⟩
                  · rw [← ho]
                    exact AOut.err (AErrSim.of_eq
                      (AErrSim.bind (Sim.apply_err hcva) _) htw4)
                  · intro w hw; rw [← ho] at hw; simp at hw
                | Ok v =>
                  obtain ⟨lst1, hb1, hrel1, hinv1, hext1, -⟩ := Sim.apply hcva
                  have htw5 : (unfoldDefinition lfe (absEIdx e)).run lst
                      = ((getAppArgs coreWalkFuel (absEIdx e)).run lst1) >>= fun q =>
                          ((Arena.mkAppN (absEIdx v) q.1).run q.2) >>= fun r =>
                            Except.ok (some r.1, r.2) := by
                    rw [htw4, hb1]; rfl
                  obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                  have hga := ExprOps.get_app_args_refines hrel1 hinv1 hr2
                  rw [hfuel] at hga
                  cases r2 with
                  | Err er =>
                    have ho : (core.result.Result.Err
                      (T := Option arena.handle.EIdx) er, st1) = o :=
                      Result.ok_injective hrun
                    refine ⟨?_, ?_⟩
                    · rw [← ho]
                      exact AOut.err (AErrSim.of_eq
                        (AErrSim.bind (AOut.destErr hga) _) htw5)
                    · intro w hw; rw [← ho] at hw; simp at hw
                  | Ok args =>
                    obtain ⟨lst2, hb2, hrel2, hinv2, hext2, -⟩ := AOut.dest hga
                    have htw6 : (unfoldDefinition lfe (absEIdx e)).run lst
                        = ((Arena.mkAppN (absEIdx v)
                            (absEIdxList args)).run lst2) >>= fun r =>
                            Except.ok (some r.1, r.2) := by
                      rw [htw5, hb2]; rfl
                    obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                    obtain ⟨r3, st2⟩ := q3
                    have hmk := hx.mkAppN hrel2 hinv2 hq3
                    cases r3 with
                    | Err er =>
                      have ho : (core.result.Result.Err
                        (T := Option arena.handle.EIdx) er, st2) = o :=
                        Result.ok_injective hrun
                      refine ⟨?_, ?_⟩
                      · rw [← ho]
                        exact AOut.err (AErrSim.of_eq
                          (AErrSim.bind (Sim.apply_err hmk) _) htw6)
                      · intro w hw; rw [← ho] at hw; simp at hw
                    | Ok r4 =>
                      obtain ⟨lst3, hb3, hrel3, hinv3, hext3, -⟩ := Sim.apply hmk
                      have ho : (core.result.Result.Ok
                        (T := Option arena.handle.EIdx) (some r4), st2) = o :=
                        Result.ok_injective hrun
                      refine ⟨?_, ?_⟩
                      · rw [← ho]
                        refine AOut.ok (lst' := lst3) ?_ hrel3 hinv3 ?_ trivial
                        · rw [htw6, hb3]; rfl
                        · exact Ext.trans hext0 (Ext.trans hext1
                            (Ext.trans hext2 hext3))
                      · intro w hw lst' hrel'
                        rw [← ho] at hw hrel'
                        have hw2 : r4 = w := by
                          simpa using hw
                        rw [← hw2]
                        exact hx.mkAppNRes hq3 r4 rfl lst' hrel'
              · rw [if_neg hb] at hrun
                have ho : (core.result.Result.Ok
                  (T := Option arena.handle.EIdx) none, st) = o :=
                  Result.ok_injective hrun
                have hlt : ¬ (l.length = (cv.level_params.val.map absNIdx).length) := by
                  rw [hll, ← hlenlps]
                  intro hx2
                  apply hb
                  apply Aeneas.Std.UScalar.eq_imp
                  exact hx2
                refine ⟨?_, ?_⟩
                · rw [← ho]
                  refine AOut.ok (lst' := lst0) ?_ hrel0 hinv0 hext0 trivial
                  rw [htw3, hl]
                  dsimp only
                  rw [if_neg hlt]
                  rfl
                · intro w hw; rw [← ho] at hw; simp at hw
          | AxiomInfo cv =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            refine ⟨?_, ?_⟩
            · rw [← ho]
              refine AOut.ok (lst' := lst0) ?_ hrel0 hinv0 hext0 trivial
              rw [htw2, unfoldDefConst_run, ← hfind]
              rfl
            · intro w hw; rw [← ho] at hw; simp at hw
          | ThmInfo cv v =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            refine ⟨?_, ?_⟩
            · rw [← ho]
              refine AOut.ok (lst' := lst0) ?_ hrel0 hinv0 hext0 trivial
              rw [htw2, unfoldDefConst_run, ← hfind]
              rfl
            · intro w hw; rw [← ho] at hw; simp at hw
          | IndInfo cv caps =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            refine ⟨?_, ?_⟩
            · rw [← ho]
              refine AOut.ok (lst' := lst0) ?_ hrel0 hinv0 hext0 trivial
              rw [htw2, unfoldDefConst_run, ← hfind]
              rfl
            · intro w hw; rw [← ho] at hw; simp at hw
          | CtorInfo cv np nf =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            refine ⟨?_, ?_⟩
            · rw [← ho]
              refine AOut.ok (lst' := lst0) ?_ hrel0 hinv0 hext0 trivial
              rw [htw2, unfoldDefConst_run, ← hfind]
              rfl
            · intro w hw; rw [← ho] at hw; simp at hw
          | RecInfo cv mi rp rules =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            refine ⟨?_, ?_⟩
            · rw [← ho]
              refine AOut.ok (lst' := lst0) ?_ hrel0 hinv0 hext0 trivial
              rw [htw2, unfoldDefConst_run, ← hfind]
              rfl
            · intro w hw; rw [← ho] at hw; simp at hw
          | ProjInfo tbl =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            refine ⟨?_, ?_⟩
            · rw [← ho]
              refine AOut.ok (lst' := lst0) ?_ hrel0 hinv0 hext0 trivial
              rw [htw2, unfoldDefConst_run, ← hfind]
              rfl
            · intro w hw; rw [← ho] at hw; simp at hw
    · rw [if_neg hts] at hrun
      have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
          = o := Result.ok_injective hrun
      have hres0 : EResolves lst0 (absEIdx h) := hx.headRes hrel0 hrh
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hres0
      have htagv := EStore_view_tagOf hv
      refine ⟨?_, ?_⟩
      · rw [← ho]
        refine AOut.ok (lst' := lst0) ?_ hrel0 hinv0 hext0 trivial
        rw [htw1, unfoldDefAt_run, hv]
        cases v with
        | const n us =>
          exfalso
          apply hts
          apply absU32_inj
          rw [etag_const_abs, ← hta, htagv]
          rfl
        | _ => rfl
      · intro w hw; rw [← ho] at hw; simp at hw

section Axioms

/-- info: 'ConRon.Refine2.EStore_view_of_tag_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EStore_view_of_tag_const

/-- info: 'ConRon.Refine2.ifenv_find_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ifenv_find_abs

/-- info: 'ConRon.Refine2.LsStore_viewLen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms LsStore_viewLen_eq

/-- info: 'ConRon.Refine2.nidx_vec_dup_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nidx_vec_dup_val

/-- info: 'ConRon.Refine2.core_walk_fuel_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms core_walk_fuel_abs

/-- info: 'ConRon.Refine2.const_val_at_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms const_val_at_refines

/-- info: 'ConRon.Refine2.unfold_definition_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unfold_definition_refines

end Axioms

end ConRon.Refine2
