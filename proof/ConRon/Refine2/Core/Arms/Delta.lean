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

## 2. The tag test at `const`

`unfold_definition` dispatches on `get_app_fn`'s answer's TAG, and since task
#97-P5-Core round 4 the twin does too (`unfoldDefinition` tests
`h.tag == ETag.const` before its `view`; the audit's row for this function).
Under a `const` tag `EStore_view_of_tag_const` says the view IS the `const`
projection — nineteen lines, no `StoreWF` — and off it both sides answer
`none` reading nothing, so no resolution fact is needed anywhere.

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

`ExprOpsHyp` below: the two interning walks the delta step borrows
(`inst_lp_fast`, `mk_app_n`), stated at the LOCKSTEP shape the Core tier is
stated at since task #97-P5-Core round 4 (`AStateRel₀`, `Sim₀`).
`Refine2/ExprOps/Mut.lean` proves both over `AStateRel` with `EResolves`
premises (their interns need the twin's `StoreWF`), which does not apply
here; the `ExprOps` tier's migration to `AStateRel₀` owes them, and the
audit found both in lockstep with their twins.  The two spine readers and
the three store readers the leaf also needs are proved here at the lockstep
relation (`get_app_fn_refines₀` …, copies of `Read.lean`'s / `Specs.lean`'s
proofs, which never used `storeWF`).

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

/-! ## The three store readers, at the lockstep relation

`Refine2/Specs.lean`'s `view_app_run`, `view_const_run` and `view_ls_len_run`
take `AStateRel` and use its `store` clause alone; these are the same three
lines over `AStateRel₀` (task #97-P5-Core round 4).  They belong in
`Specs.lean`, which is not this lane's: the tier-wide migration to
`AStateRel₀` retires these copies. -/

theorem view_app_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_app pers st h = ok o) :
    SimR (Option.map absPairE) lst o (Arena.viewApp (absEIdx h)) := by
  rw [arena.monad.view_app] at hrun
  show (Arena.viewApp (absEIdx h)).run lst = _
  rw [show (Arena.viewApp (absEIdx h)).run lst
        = .ok (lst.store.viewApp (absEIdx h), lst) from rfl,
    estore_view_app_abs hrel.store hrun]

theorem view_const_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_const pers st h = ok o) :
    SimR (Option.map absConstT) lst o (Arena.viewConst (absEIdx h)) := by
  rw [arena.monad.view_const] at hrun
  show (Arena.viewConst (absEIdx h)).run lst = _
  rw [show (Arena.viewConst (absEIdx h)).run lst
        = .ok (lst.store.viewConst (absEIdx h), lst) from rfl,
    estore_view_const_abs hrel.store hrun]

theorem view_ls_len_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.view_ls_len pers st h = ok o) :
    SimR (Option.map absSz) lst o (Arena.viewLsLen (absLsIdx h)) := by
  rw [arena.monad.view_ls_len] at hrun
  obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ls_s] at hl
  have hl2 : l = st.store.lss := (Result.ok_injective hl).symm
  subst hl2
  show (Arena.viewLsLen (absLsIdx h)).run lst = _
  rw [show (Arena.viewLsLen (absLsIdx h)).run lst
        = .ok (lst.store.lss.viewLen (absLsIdx h), lst) from rfl,
    lsstore_view_len_abs hrel.store.lss hrun]

/-! ## The two spine readers, at the lockstep relation

`Refine2/ExprOps/Read.lean`'s `get_app_fn_refines` and `get_app_args_refines`,
over `AStateRel₀` — the same proofs (they never used `storeWF`, and the state
does not move), copied here for the reason the three readers above are. -/

private theorem get_app_fn_aux₀ (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      arena.expr_ops.get_app_fn pers st fuel h = ok o →
      AOut₀ absEIdx pers o st ((getAppFn (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.get_app_fn] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut₀.err ?_
    show AErrSim _ ((getAppFn (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, getAppFn, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.get_app_fn] at hrun
    have hne : ¬ (fuel = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htag := eidx_tag_abs ht
    rw [show absU fuel = m + 1 from hn, getAppFn]
    by_cases hc : t = arena.handle.ETAG_APP
    · rw [if_pos hc] at hrun
      subst hc
      rw [show ((absEIdx h).tag == ETag.app) = true by
        rw [htag, etag_app_abs]; simp]
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hva := view_app_run₀ hrel hp
      simp only [if_true]
      rw [StateT.run_bind, hva]
      cases hpc : p with
      | none =>
        rw [hpc] at hrun
        rw [arena.monad.fail_dangling_e] at hrun
        obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [fail_run hrun]
        refine AOut₀.err ?_
        show AErrSim _ ((Arena.failDanglingE : AM EIdx).run lst)
        exact failDanglingE_errSim lst
      | some q =>
        rw [hpc] at hrun
        obtain ⟨f1, a1⟩ := q
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        show AOut₀ absEIdx pers o st ((getAppFn m (absEIdx f1)).run lst)
        have := ih (fuel := i1) (h := f1) hi1v hrel hinv hrun
        rw [show absU i1 = m from hi1v] at this
        exact this
    · rw [if_neg hc] at hrun
      obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [dupId_eidx _ _ he1] at hrun
      have ho : (core.result.Result.Ok h : core.result.Result _ _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      rw [show ((absEIdx h).tag == ETag.app) = false by
        rw [htag]
        have : absU32 t ≠ ETag.app := by
          rw [← etag_app_abs]
          intro hcc; exact hc (absU32_inj hcc)
        simp [this]]
      simp only [Bool.false_eq_true, if_false]
      exact AOut₀.ok rfl hrel hinv

/-- `get_app_fn` ⊑ `getAppFn`, lockstep. -/
theorem get_app_fn_refines₀ {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.get_app_fn pers st fuel h = ok o) :
    AOut₀ absEIdx pers o st ((getAppFn (absU fuel) (absEIdx h)).run lst) :=
  get_app_fn_aux₀ fuel.val rfl hrel hinv hrun

private theorem get_app_args_go_aux₀ (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {k : Std.Usize} {o},
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      arena.expr_ops.get_app_args_go pers st fuel h k = ok o →
      AOut₀ absEIdxList pers o st ((getAppArgs (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h k o hn hrel hinv hrun
    rw [arena.expr_ops.get_app_args_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut₀.err ?_
    show AErrSim _ ((getAppArgs (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, getAppArgs, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h k o hn hrel hinv hrun
    rw [arena.expr_ops.get_app_args_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htag := eidx_tag_abs ht
    rw [show absU fuel = m + 1 from hn, getAppArgs]
    by_cases hc : t = arena.handle.ETAG_APP
    · rw [if_pos hc] at hrun
      subst hc
      rw [show ((absEIdx h).tag == ETag.app) = true by
        rw [htag, etag_app_abs]; simp]
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hva := view_app_run₀ hrel hp
      simp only [if_true]
      rw [StateT.run_bind, hva]
      cases hpc : p with
      | none =>
        rw [hpc] at hrun
        rw [arena.monad.fail_dangling_e] at hrun
        obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [fail_run hrun]
        refine AOut₀.err ?_
        show AErrSim _ ((Arena.failDanglingE : AM (List EIdx)).run lst)
        exact failDanglingE_errSim lst
      | some q =>
        rw [hpc] at hrun
        obtain ⟨f1, a1⟩ := q
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec := ih (fuel := i1) (h := f1) (k := i2) hi1v hrel hinv hr
        rw [show absU i1 = m from hi1v] at hrec
        show AOut₀ absEIdxList pers o st
          ((do let qs ← getAppArgs m (absEIdx f1); pure (qs ++ [absEIdx a1])).run lst)
        cases hrc : r with
        | Err e =>
          rw [hrc] at hrun hrec
          have ho : (core.result.Result.Err e :
              core.result.Result (alloc.vec.Vec arena.handle.EIdx) _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          refine AOut₀.err ?_
          rw [StateT.run_bind]
          intro kk hk
          obtain ⟨le, hle, hlk⟩ := hrec kk hk
          exact ⟨le, by rw [hle]; rfl, hlk⟩
        | Ok args =>
          rw [hrc] at hrun hrec
          obtain ⟨lst', hx, hrel', hinv'⟩ := hrec
          obtain ⟨args1, ha1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok args1 :
              core.result.Result (alloc.vec.Vec arena.handle.EIdx) _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          refine AOut₀.ok ?_ hrel' hinv'
          rw [StateT.run_bind, hx]
          show Except.ok _ = _
          rw [show absEIdxList args1 = absEIdxList args ++ [absEIdx a1] by
            unfold absEIdxList
            rw [ConRon.Refine.vec_push_val ha1, List.map_append]
            rfl]
    · rw [if_neg hc] at hrun
      have ho : (core.result.Result.Ok
          (alloc.vec.Vec.with_capacity arena.handle.EIdx k) :
          core.result.Result (alloc.vec.Vec arena.handle.EIdx) _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      rw [show ((absEIdx h).tag == ETag.app) = false by
        rw [htag]
        have : absU32 t ≠ ETag.app := by
          rw [← etag_app_abs]
          intro hcc; exact hc (absU32_inj hcc)
        simp [this]]
      simp only [Bool.false_eq_true, if_false]
      refine AOut₀.ok ?_ hrel hinv
      show Except.ok ([], lst) = _
      rfl

/-- `get_app_args` ⊑ `getAppArgs`, lockstep. -/
theorem get_app_args_refines₀ {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.get_app_args pers st fuel h = ok o) :
    AOut₀ absEIdxList pers o st ((getAppArgs (absU fuel) (absEIdx h)).run lst) := by
  rw [arena.expr_ops.get_app_args] at hrun
  exact get_app_args_go_aux₀ fuel.val rfl hrel hinv hrun

/-! ## The two interning walks this tier consumes, stated by name

**`ExprOpsHyp` is the delta leaf's bundle, restated at the lockstep shape**
(task #97-P5-Core round 4).  Round 3 found its four fields false or
unsuppliable as written: `headRes` and `mkAppNRes` were resolution claims
with no premise on the input (a dangling non-`app` handle, an empty argument
vector over a dangling head), and `instLPFast`/`mkAppN` were STRONGER than
`ExprOps/Mut.lean`'s closed lemmas, which take `EResolves` of their inputs.
Ruling 2 asked for the fields to be restated to what `Mut.lean` proves and the
bundle filled from it; the coordinator's later ruling (i) moved `KnotRel`
and `BodyRel` — and with them this leaf — to `AStateRel₀`, where `Mut.lean`'s
lemmas (over `AStateRel`, and needing `StoreWF` for their interns) do not
apply, so:

* `headRes` and `mkAppNRes` are GONE: the twin's `unfoldDefinition` now tests
  the head's TAG where the port does (round 4's audit), so no resolution fact
  is consumed, and the `AnswerResolvesOpt` conjunct they fed is gone with the
  `Sim₀` conclusion;
* `instLPFast` and `mkAppN` are the lockstep statements the `ExprOps` tier's
  migration to `AStateRel₀` owes — no premise beyond the relation and the
  invariant.  Round 4's audit found `inst_lp_fast` and `mk_app_n` in lockstep
  with their twins (neither reads a view where the port reads a tag), so they
  are expected TRUE; they are not yet proved at this shape, and this bundle is
  the named seam until they are. -/
structure ExprOpsHyp (pers : arena.store.PersTier) : Prop where
  /-- `Refine2/ExprOps/Mut.lean`'s `inst_lp_fast_refines`, at the lockstep
  relation. -/
  instLPFast : ∀ {st lst} {fuel : Std.U64}
    {lps : alloc.vec.Vec arena.handle.NIdx} {us : arena.handle.LsIdx}
    {value : arena.handle.EIdx} {o},
    AStateRel₀ pers st lst → AStateInv pers st →
    arena.expr_ops.inst_lp_fast pers st fuel lps us value = ok o →
    Sim₀ absEIdx pers lst o
      (instLPFast (absU fuel) (lps.val.map absNIdx) (absLsIdx us)
        (absEIdx value))
  /-- `Refine2/ExprOps/Mut.lean`'s `mk_app_n_refines`, at the lockstep
  relation. -/
  mkAppN : ∀ {st lst} {f : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {o},
    AStateRel₀ pers st lst → AStateInv pers st →
    arena.expr_ops.mk_app_n pers st f args = ok o →
    Sim₀ absEIdx pers lst o
      (Arena.mkAppN (absEIdx f) (absEIdxList args))

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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.const_val_at pers st n lps value us = ok o) :
    Sim₀ absEIdx pers lst o
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
    exact AOut₀.ok (constValAt_hit _ _ _ _ _ _ hprobe.symm) hrel hinv
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
      exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hbody) _) htw)
    | Ok r1 =>
      obtain ⟨lst1, hb1, hrel1, hinv1⟩ := Sim₀.apply hbody
      obtain ⟨st2, hs2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have ho : (core.result.Result.Ok r1, st2) = o := Result.ok_injective hrun
      rw [← ho]
      obtain ⟨hrel2, hinv2⟩ := const_val_set_rel hrel1 hinv1 hs2
      rw [nls_key_abs hk] at hrel2
      refine AOut₀.ok ?_ hrel2 hinv2
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
  if h.tag == ETag.const then
    match ← Arena.view h with
    | .const n us => unfoldDefConst fe e n us
    | _ => pure none
  else pure none

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

/-- `unfoldDefAt` at a `const`-tagged head: the one `view` read. -/
theorem unfoldDefAt_run (fe : IFEnv) (e h : EIdx) (lst : AState)
    (htag : h.tag = ETag.const) :
    (unfoldDefAt fe e h).run lst
      = (match lst.store.view h with
         | none => Except.error
             (Arena.CheckError.internal "arena: dangling expression handle")
         | some (.const n us) => (unfoldDefConst fe e n us).run lst
         | some _ => Except.ok (none, lst)) := by
  show ((if h.tag == ETag.const then
      (do
        let v ← Arena.view h
        match v with
        | .const n us => unfoldDefConst fe e n us
        | _ => pure none)
    else pure none) : AM (Option EIdx)).run lst = _
  rw [if_pos (by rw [htag]; rfl), am_run_bind, view_run_eq]
  cases hv : lst.store.view h with
  | none => rfl
  | some v => cases v <;> rfl

/-- `unfoldDefAt` at any other head: `none`, off the tag, no store read — the
port's `else` arm (task #97-P5-Core round 4's twin fix). -/
theorem unfoldDefAt_run_ne (fe : IFEnv) (e h : EIdx) (lst : AState)
    (htag : ¬ h.tag = ETag.const) :
    (unfoldDefAt fe e h).run lst = Except.ok (none, lst) := by
  show ((if h.tag == ETag.const then
      (do
        let v ← Arena.view h
        match v with
        | .const n us => unfoldDefConst fe e n us
        | _ => pure none)
    else pure none) : AM (Option EIdx)).run lst = _
  rw [if_neg (by simpa using htag)]
  rfl

/-- **`arena::core::unfold_definition` against `Arena.unfoldDefinition`** — one
delta step, and the `whnf` loop's second leaf.  Closed modulo `ExprOpsHyp`
(P5-3's `inst_lp_fast_refines` and `mk_app_n_refines`, plus finding 14 at two
call sites) and `CoreCtx`'s two index clauses; no `sorry`. -/
theorem unfold_definition_refines {pers vis st fe lfe e lst o}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe)
    (hrun : arena.core.unfold_definition pers vis st fe e = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (unfoldDefinition lfe (absEIdx e)) := by
  have hfuel := core_walk_fuel_abs
  rw [arena.core.unfold_definition] at hrun
  obtain ⟨rh, hrh, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have htw0 : (unfoldDefinition lfe (absEIdx e)).run lst
      = ((getAppFn coreWalkFuel (absEIdx e)).run lst) >>= fun p =>
          (unfoldDefAt lfe (absEIdx e) p.1).run p.2 := by
    rw [unfoldDefinition_unfold]
    exact am_run_bind _ _ lst
  have hfn := get_app_fn_refines₀ hrel hinv hrh
  rw [hfuel] at hfn
  cases rh with
  | Err er =>
    have ho : (core.result.Result.Err (T := Option arena.handle.EIdx) er, st) = o :=
      Result.ok_injective hrun
    rw [← ho]
    exact AOut₀.err (AErrSim.of_eq (AErrSim.bind hfn _) htw0)
  | Ok h =>
    obtain ⟨lst0, hb0, hrel0, hinv0⟩ := hfn
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
        have h2 := SimR.apply (view_const_run₀ hrel0 hoc)
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
        rw [← ho]
        refine AOut₀.err (AErrSim.internal
          (s := "arena: dangling expression handle") ?_)
        rw [htw1, unfoldDefAt_run _ _ _ _ htag, hvw]
        rfl
      | some p =>
        obtain ⟨n, us⟩ := p
        rw [hocc] at hrun hvw
        have htw2 : (unfoldDefinition lfe (absEIdx e)).run lst
            = (unfoldDefConst lfe (absEIdx e) (absNIdx n) (absLsIdx us)).run lst0 := by
          rw [htw1, unfoldDefAt_run _ _ _ _ htag, hvw]
          rfl
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hfind := ifenv_find_abs hctx ho1
        cases ho1c : o1 with
        | none =>
          rw [ho1c] at hrun hfind
          have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
              = o := Result.ok_injective hrun
          rw [← ho]
          refine AOut₀.ok (lst' := lst0) ?_ hrel0 hinv0
          rw [htw2, unfoldDefConst_run, ← hfind]
          rfl
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
              have h2 := SimR.apply (view_ls_len_run₀ hrel0 ho2)
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
              rw [← ho]
              refine AOut₀.err (AErrSim.internal
                (s := "arena: dangling level-list handle") ?_)
              rw [htw3, hvn]
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
                  rw [← ho]
                  exact AOut₀.err (AErrSim.of_eq
                    (AErrSim.bind (Sim₀.apply_err hcva) _) htw4)
                | Ok v =>
                  obtain ⟨lst1, hb1, hrel1, hinv1⟩ := Sim₀.apply hcva
                  have htw5 : (unfoldDefinition lfe (absEIdx e)).run lst
                      = ((getAppArgs coreWalkFuel (absEIdx e)).run lst1) >>= fun q =>
                          ((Arena.mkAppN (absEIdx v) q.1).run q.2) >>= fun r =>
                            Except.ok (some r.1, r.2) := by
                    rw [htw4, hb1]; rfl
                  obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                  have hga := get_app_args_refines₀ hrel1 hinv1 hr2
                  rw [hfuel] at hga
                  cases r2 with
                  | Err er =>
                    have ho : (core.result.Result.Err
                      (T := Option arena.handle.EIdx) er, st1) = o :=
                      Result.ok_injective hrun
                    rw [← ho]
                    exact AOut₀.err (AErrSim.of_eq
                      (AErrSim.bind hga _) htw5)
                  | Ok args =>
                    obtain ⟨lst2, hb2, hrel2, hinv2⟩ := hga
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
                      rw [← ho]
                      exact AOut₀.err (AErrSim.of_eq
                        (AErrSim.bind (Sim₀.apply_err hmk) _) htw6)
                    | Ok r4 =>
                      obtain ⟨lst3, hb3, hrel3, hinv3⟩ := Sim₀.apply hmk
                      have ho : (core.result.Result.Ok
                        (T := Option arena.handle.EIdx) (some r4), st2) = o :=
                        Result.ok_injective hrun
                      rw [← ho]
                      refine AOut₀.ok (lst' := lst3) ?_ hrel3 hinv3
                      rw [htw6, hb3]; rfl
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
                rw [← ho]
                refine AOut₀.ok (lst' := lst0) ?_ hrel0 hinv0
                rw [htw3, hl]
                dsimp only
                rw [if_neg hlt]
                rfl
          | AxiomInfo cv =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut₀.ok (lst' := lst0) ?_ hrel0 hinv0
            rw [htw2, unfoldDefConst_run, ← hfind]
            rfl
          | ThmInfo cv v =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut₀.ok (lst' := lst0) ?_ hrel0 hinv0
            rw [htw2, unfoldDefConst_run, ← hfind]
            rfl
          | IndInfo cv caps =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut₀.ok (lst' := lst0) ?_ hrel0 hinv0
            rw [htw2, unfoldDefConst_run, ← hfind]
            rfl
          | CtorInfo cv np nf =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut₀.ok (lst' := lst0) ?_ hrel0 hinv0
            rw [htw2, unfoldDefConst_run, ← hfind]
            rfl
          | RecInfo cv mi rp rules =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut₀.ok (lst' := lst0) ?_ hrel0 hinv0
            rw [htw2, unfoldDefConst_run, ← hfind]
            rfl
          | ProjInfo tbl =>
            have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
                = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut₀.ok (lst' := lst0) ?_ hrel0 hinv0
            rw [htw2, unfoldDefConst_run, ← hfind]
            rfl
    · -- the port's `else` arm, off the tag: the twin tests the same tag
      rw [if_neg hts] at hrun
      have ho : (core.result.Result.Ok (T := Option arena.handle.EIdx) none, st)
          = o := Result.ok_injective hrun
      rw [← ho]
      refine AOut₀.ok (lst' := lst0) ?_ hrel0 hinv0
      rw [htw1, unfoldDefAt_run_ne _ _ _ _ (fun hx2 => hts (absU32_inj (by
        rw [← hta, hx2, etag_const_abs])))]
      rfl

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
