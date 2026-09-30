/-
# `ConRon.Refine2.Inductives.SumInstall` — Theorem 2 for `arena::inductives::sum_install`

**Task #97-P5-Ind** (DESIGN.md §8.2); repaired by **task #105**.
`crates/con-ron-core/src/arena/inductives/sum_install.rs` against
`proof/ConRon/Arena/Inductives/SumInstall.lean`: official's telescope loop,
the type former's telescope, the per-field universe bound, the constructors'
stage and the stored rules.  Task #105 deleted the direct route's type-former
install (`check_sum_ind`, `native_caps_at`) and official's positivity walk as
a normalisation (`norm_pos_dom`, `norm_field_doms`, `norm_ctor_val`,
`zip_fvar_doms`); their lemmas went with them.

`close_telescope`'s twin is `Arena/Inductives/Positivity.lean`'s
`closeTelescope` (the Rust keeps a copy here and one in `positivity`).
`checkSumCtor` is ONE twin `def` and four Rust functions; the three tails are
`Refine2/Inductives/Spec.lean`'s `checkSumCtor{Frames,Resid,Sorts}Spec`, tied
back by `checkSumCtor_unfold`.  `field_sort_bound` is `fieldSortBoundSpec`
there, and `eidx_contains` is `List.contains` (a `TwinEq`).

The Core tier arrives here: `whnf_telescope` calls `whnf`,
`check_struct_field_sorts_i` calls `infer_type_core` and `ensure_sort_core`,
`check_sum_tele_slow` and `check_sum_ctor` call `check_constant_val`
(`Refine2/Checker/{KnotHyp,Base}.lean`).  `cons_sum_ctors` is PURE on both
sides (the index push touches no term).
-/
import ConRon.Refine2.Inductives.StructInstall
import ConRon.Refine2.Inductives.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open scoped ConRon.Refine2.IndSide

open ConRon.Arena

/-! ## The binders' canonical metas (`PropWhenWF`, the erased subtype invariant)

The telescope walks push `(dom, meta)` pairs whose `meta` comes from a view
(`EViewMetaWF`, from `AStateInv`); `close_telescope` interns them back, which
needs the fact (the cleanup lane's statement change).  One side-tier move:
a pushed vector's binders are canonical when the old ones and the pushed
meta are. -/

theorem bwf_push {out o : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {d : arena.handle.EIdx} {m : kernel.expr.BinderMeta}
    (hv : o.val = out.val ++ [(d, m)]) (hout : ∀ p ∈ out.val, ConRon.Refine.PropWhenWF p.2.pw)
    (hm : ConRon.Refine.PropWhenWF m.pw) : ∀ p ∈ o.val, ConRon.Refine.PropWhenWF p.2.pw := by
  intro p hp
  rw [hv] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hout p hp
  · rw [List.mem_singleton.mp hp]; exact hm

theorem wf_of_view_some {ty b : arena.handle.EIdx} {m : kernel.expr.BinderMeta}
    (h : ∀ t : arena.handle.EIdx × arena.handle.EIdx × kernel.expr.BinderMeta,
      some (ty, b, m) = some t → ConRon.Refine.PropWhenWF t.2.2.pw) :
    ConRon.Refine.PropWhenWF m.pw := h _ rfl

theorem bwf_new : ∀ p ∈ (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)).val,
    ConRon.Refine.PropWhenWF p.2.pw := by
  intro p hp; simp [alloc.vec.Vec.new] at hp

local macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| first
      | exact bwf_new
      | (apply bwf_push; all_goals first | assumption | (simp only [Lockstep.EViewMetaWF] at *; assumption) | (apply wf_of_view_some; assumption) | (subst_vars; simpa using ‹ConRon.Refine.PropWhenWF _›)))

/-! ## The type former's stage -/

theorem whnf_telescope_aux (m : Nat) :
    ∀ {pers st lst} {vis : Std.U64} {rf lf} {mode : kernel.env.CheckMode} {i n : Std.U64}
      {e : arena.handle.EIdx} {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)},
      n.val = m → AStateRel₀ pers st lst → AStateInv pers st → IFEnvRelI rf lf →
      absU vis = lf.visibleBelow → (∀ p ∈ out.val, ConRon.Refine.PropWhenWF p.2.pw) →
      Lockstep.LS pers (fun r b => b = (absBinderL r.1, absLIdx r.2) ∧
          ∀ p ∈ r.1.val, ConRon.Refine.PropWhenWF p.2.pw)
        (arena.inductives.sum_install.whnf_telescope pers vis st mode rf i n e out) lst
        (do
          let q ← whnfTelescope (ConRon.Refine.absMode mode) lf (absU i) (absU n)
            (absEIdx e)
          pure (absBinderL out ++ q.1, q.2)) := by
  induction m with
  | zero =>
    intro pers st lst vis rf lf mode i n e out hn hrel hinv hfe hvis hout
    rw [arena.inductives.sum_install.whnf_telescope, show absU n = 0 from hn, whnfTelescope_zero]
    lockstep
  | succ m ih =>
    intro pers st lst vis rf lf mode i n e out hn hrel hinv hfe hvis hout
    rw [arena.inductives.sum_install.whnf_telescope, show absU n = m + 1 from hn, whnfTelescope_succ]
    have hn1 : 1 ≤ n.val := by omega
    obtain rfl : m = n.val - 1 := by omega
    clear hn
    lockstep

open Lockstep in
/-- `whnf_telescope` ⊑ `whnfTelescope`, with the accumulated binders in front
— **official's telescope loop** (`check_inductive_types`): peel `n` Π binders
off `e`, reducing the residual to weak head normal form before each binder and
at the end, where it must be a sort. -/
@[lockstep] theorem whnf_telescope_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {i n : Std.U64}
    {e : arena.handle.EIdx}
    {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow)
    (hout : ∀ p ∈ out.val, ConRon.Refine.PropWhenWF p.2.pw) :
    LS pers (fun r b => b = (absBinderL r.1, absLIdx r.2) ∧
        ∀ p ∈ r.1.val, ConRon.Refine.PropWhenWF p.2.pw) (arena.inductives.sum_install.whnf_telescope pers vis st mode rf i n e out) lst
      (do
        let q ← whnfTelescope (ConRon.Refine.absMode mode) lf (absU i) (absU n)
          (absEIdx e)
        pure (absBinderL out ++ q.1, q.2)) :=
  whnf_telescope_aux _ rfl hrel hinv hfe hvis hout

open Lockstep in
/-- `close_telescope` ⊑ `closeTelescope` from the cursor on: close a telescope
opened at the free variables `i ..< i + bs.length` back into a syntactic
Π-telescope over `body`. -/
@[lockstep] theorem sum_close_telescope_ls
    {pers st lst}
    {bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize}
    {i : Std.U64}
    {body : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hpw : ∀ p ∈ bs.val, ConRon.Refine.PropWhenWF p.2.pw) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.sum_install.close_telescope pers st bs k i body) lst
      (closeTelescope (absBinderLFrom bs k) (absU i) (absEIdx body)) := by
  revert st lst hrel hinv
  simp only [absBinderLFrom]
  intro st lst hrel hinv
  refine ls_cursor_acc bs (fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2))
    (fun i xs => closeTelescope xs (absU i) (absEIdx body))
    (fun st k i => arena.inductives.sum_install.close_telescope pers st bs k i body)
    ?_ ?_ k st lst i hrel hinv
  · intro st lst k i hn hrel hinv
    try simp only []
    rw [arena.inductives.sum_install.close_telescope.eq_def, closeTelescope]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst k i hb hrel hinv ih
    try simp only []
    rw [arena.inductives.sum_install.close_telescope.eq_def, closeTelescope]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    have hpwk := hpw _ (List.getElem_mem hb)
    lockstep

open Lockstep in
/-- `check_sum_tele_slow` ⊑ `checkSumTele`'s `where` clause — the `_` arm of
its match, named on both sides because over handles the syntactic test is two
`view`s and duplicating the arm would duplicate the whnf loop. -/
@[lockstep] theorem check_sum_tele_slow_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {n : Std.U64}
    {cv_ta0 : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun r => (absIConstantVal r.1, absLIdx r.2)) a) (arena.inductives.sum_install.check_sum_tele_slow pers vis st mode rf cv n cv_ta0) lst
      (checkSumTele.checkSumTeleSlow (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absU n) (absIConstantVal cv_ta0)) := by
  rw [arena.inductives.sum_install.check_sum_tele_slow, checkSumTele.checkSumTeleSlow]
  lockstep

open Lockstep in
/-- `check_sum_tele` ⊑ `checkSumTele` — the type former's TELESCOPE
(con-leche's task #195): the checked declared type when it is already a
syntactic telescope of `n` Π binders ending in a sort, else the declared
type's whnf'd telescope, closed and checked in its place. -/
@[lockstep] theorem check_sum_tele_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {n : Std.U64}
    {cv_ta0 : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun r => (absIConstantVal r.1, absLIdx r.2)) a) (arena.inductives.sum_install.check_sum_tele pers vis st mode rf cv n cv_ta0) lst
      (checkSumTele (ConRon.Refine.absMode mode) lf (absIConstantVal cv) (absU n)
        (absIConstantVal cv_ta0)) := by
  rw [arena.inductives.sum_install.check_sum_tele, checkSumTele]
  lockstep

/-! ## The constructors' stage -/

/-- `eidx_contains` ⊑ `idxArgs.contains fv` from the cursor on — handles, so
`==` is word equality and the test transfers by `absEIdx`'s injectivity. -/
theorem eidx_contains_refines {xs : alloc.vec.Vec arena.handle.EIdx}
    {x : arena.handle.EIdx} {i : Std.Usize} {o}
    (hrun : arena.inductives.sum_install.eidx_contains xs x i = ok o) :
    o = (absEIdxLFrom xs i).contains (absEIdx x) := by
  simp only [absEIdxLFrom, List.contains_eq_any_beq, List.any_map, Function.comp_def]
  refine vec_cursor_any xs _
    (arena.inductives.sum_install.eidx_contains xs x) ?_ ?_ i o hrun
  · intro i o hn h
    rw [arena.inductives.sum_install.eidx_contains.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [← h]
  · intro i y o hy h
    have hlt : i.val < xs.val.length := (List.getElem?_eq_some_iff.mp hy).1
    rw [arena.inductives.sum_install.eidx_contains.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hey : e = y := by
      have h1 := vec_index_some he; rw [hy] at h1; exact (Option.some_inj.mp h1).symm
    subst hey
    have hbv : b = (absEIdx x == absEIdx e) := by
      rw [eidx_eq2_abs hb]
      by_cases hcc : absEIdx e = absEIdx x
      · simp [hcc]
      · have hcc' : ¬ absEIdx x = absEIdx e := fun z => hcc z.symm
        simp [hcc, hcc']
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
    · rw [hbb] at h hbv
      rw [if_pos (by simp), Result.ok.injEq] at h
      exact Or.inl ⟨hbv.symm, h.symm⟩

open Lockstep in
/-- `eidx_contains_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem eidx_contains_twin0
    {xs : alloc.vec.Vec arena.handle.EIdx}
    {x : arena.handle.EIdx} :
    LSP (arena.inductives.sum_install.eidx_contains xs x 0#usize) (fun o => TwinEq ((absEIdxL xs).contains (absEIdx x)) (o)) := by
  intro o h
  have h' := (eidx_contains_refines h).symm
  simpa [Lockstep.TwinEq, absEIdxLFrom, absEIdxL, alloc.vec.Vec.new] using h'

open Lockstep in
/-- `field_sort_bound` ⊑ `checkStructFieldSortsI`'s per-field universe
bound. -/
@[lockstep] theorem field_sort_bound_ls
    {pers st lst}
    {is_prop large : Bool}
    {s u : arena.handle.LIdx}
    {fv : arena.handle.EIdx}
    {idx_args : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.sum_install.field_sort_bound pers st is_prop large s u fv idx_args) lst
      (fieldSortBoundSpec is_prop large (absLIdx s) (absLIdx u) (absEIdx fv)
        (absEIdxL idx_args)) := by
  rw [arena.inductives.sum_install.field_sort_bound, fieldSortBoundSpec]
  lockstep

/-- `checkStructFieldSortsI`'s step with the per-field bound named as the
port's `field_sort_bound` (`fieldSortBoundSpec`). -/
theorem checkStructFieldSortsI_succ_port (mode : ConLeche.CheckMode) (fe : IFEnv)
    (isProp large : Bool) (s : LIdx) (nP : Nat) (fvs idxArgs : List EIdx) (j : Nat) :
    checkStructFieldSortsI mode fe isProp large s nP fvs idxArgs (j + 1) = (do
      let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
      let ty ← inferTypeCore mode fe checkFuel (nP + j) (← fvarTypeD fv)
      let u ← ensureSortCore mode fe checkFuel (nP + j) ty
      fieldSortBoundSpec isProp large s u fv idxArgs
      let rest ← checkStructFieldSortsI mode fe isProp large s nP fvs idxArgs j
      pure (rest ++ [u])) := by
  rw [checkStructFieldSortsI]
  simp only [fieldSortBoundSpec]
  congr 1; funext fv; congr 1; funext d; congr 1; funext ty; congr 1; funext u
  split
  · simp only [bind_assoc]
    congr 1; funext lu; congr 1; funext ls; congr 1; funext b
    split <;> simp
  · split
    · simp only [bind_assoc]
      congr 1; funext z; congr 1; funext b
      split <;> simp
    · simp

open Lockstep in
/-- `check_struct_field_sorts_i` ⊑ `checkStructFieldSortsI` — the fields'
sorts over the opened constructor telescope, with the official per-field
universe bound unless the family is propositional.  Walks the fields from the
last to the first and returns the sorts in field order, which is why the
counter is the twin's `j + 1` recursion. -/
@[lockstep] theorem check_struct_field_sorts_i_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {is_prop large : Bool}
    {s : arena.handle.LIdx}
    {n_p : Std.U64}
    {fvs idx_args : alloc.vec.Vec arena.handle.EIdx}
    {k : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absLIdxL a) (arena.inductives.sum_install.check_struct_field_sorts_i pers vis st mode rf is_prop large s n_p fvs idx_args k) lst
      (checkStructFieldSortsI (ConRon.Refine.absMode mode) lf is_prop large
        (absLIdx s) (absU n_p) (absEIdxL fvs) (absEIdxL idx_args) (absU k)) := by
  induction hk : k.val generalizing k st lst with
  | zero =>
    rw [arena.inductives.sum_install.check_struct_field_sorts_i.eq_def,
      if_pos (by scalar_tac), show absU k = 0 from hk, checkStructFieldSortsI]
    lockstep
  | succ m ih =>
    rw [arena.inductives.sum_install.check_struct_field_sorts_i.eq_def,
      if_neg (by scalar_tac), show absU k = m + 1 from hk, checkStructFieldSortsI_succ_port]
    have hk1 : 1 ≤ k.val := by omega
    obtain rfl : m = k.val - 1 := by omega
    clear hk
    dsimp only
    simp only [absEIdxL]
    by_cases hf : k.val - 1 < fvs.val.length
    · rw [List.getElem?_map, List.getElem?_eq_getElem hf, Option.map_some]
      lockstep
    · rw [List.getElem?_map, List.getElem?_eq_none (by omega), Option.map_none]
      lockstep

/-! ## `checkSumCtor`, split four ways (`Spec.lean`'s three `checkSumCtor…Spec`s) -/

open Lockstep in
/-- `field_doms_resolve` ⊑ `checkSumCtor`'s field-domain resolution, from the
cursor on. -/
@[lockstep] theorem field_doms_resolve_ls
    {pers st lst}
    {vis : Std.U64}
    {rf0 lf0}
    {x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.sum_install.field_doms_resolve pers vis st rf0 x_fvs i) lst
      (fieldDomsResolve lf0 (absEIdxLFrom x_fvs i)) := by
  revert st lst hrel hinv
  simp only [absEIdxLFrom]
  intro st lst hrel hinv
  refine ls_cursor x_fvs absEIdx (fieldDomsResolve lf0)
    (fun st i => arena.inductives.sum_install.field_doms_resolve pers vis st rf0 x_fvs i)
    ?_ ?_ i st lst hrel hinv
  · intro st lst i hn hrel hinv
    rw [arena.inductives.sum_install.field_doms_resolve.eq_def, fieldDomsResolve]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    rw [arena.inductives.sum_install.field_doms_resolve.eq_def, fieldDomsResolve]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
/-- `idx_args_resolve` ⊑ `checkSumCtor`'s index-expression resolution, from the
cursor on. -/
@[lockstep] theorem idx_args_resolve_ls
    {pers st lst}
    {vis : Std.U64}
    {rf0 lf0}
    {idx_args : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.sum_install.idx_args_resolve pers vis st rf0 idx_args i) lst
      (idxArgsResolve lf0 (absEIdxLFrom idx_args i)) := by
  revert st lst hrel hinv
  simp only [absEIdxLFrom]
  intro st lst hrel hinv
  refine ls_cursor idx_args absEIdx (idxArgsResolve lf0)
    (fun st i => arena.inductives.sum_install.idx_args_resolve pers vis st rf0 idx_args i)
    ?_ ?_ i st lst hrel hinv
  · intro st lst i hn hrel hinv
    rw [arena.inductives.sum_install.idx_args_resolve.eq_def, idxArgsResolve]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    rw [arena.inductives.sum_install.idx_args_resolve.eq_def, idxArgsResolve]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
/-- `check_sum_ctor_sorts` ⊑ `checkSumCtor`'s tail. -/
@[lockstep] theorem check_sum_ctor_sorts_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf0 lf0}
    {rf lf}
    {n_p : Std.U64}
    {res_sort : arena.handle.LIdx}
    {is_prop large : Bool}
    {n_f : Std.U64}
    {cv_ca : arena.env.IConstantVal}
    {x_fvs idx_args : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe0 : IFEnvRelI rf0 lf0)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = (fun r => (absIConstantVal r.1, absLIdxL r.2)) a) (arena.inductives.sum_install.check_sum_ctor_sorts pers st mode rf0 rf n_p res_sort is_prop large n_f cv_ca x_fvs idx_args) lst
      (checkSumCtorSortsSpec (ConRon.Refine.absMode mode) lf0 lf (absU n_p)
        (absLIdx res_sort) is_prop large (absU n_f) (absIConstantVal cv_ca)
        (absEIdxL x_fvs) (absEIdxL idx_args)) := by
  rw [arena.inductives.sum_install.check_sum_ctor_sorts, checkSumCtorSortsSpec]
  lockstep

open Lockstep in
/-- `check_sum_ctor_resid` ⊑ `checkSumCtor`'s residual stage. -/
@[lockstep] theorem check_sum_ctor_resid_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf0 lf0}
    {rf lf}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx}
    {is_prop large : Bool}
    {n_f : Std.U64}
    {cv_ca : arena.env.IConstantVal}
    {p_fvs x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe0 : IFEnvRelI rf0 lf0)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = (fun r => (absIConstantVal r.1, absLIdxL r.2)) a) (arena.inductives.sum_install.check_sum_ctor_resid pers st mode rf0 rf t lps n_p n_idx res_sort is_prop large n_f cv_ca p_fvs x_fvs xrest) lst
      (checkSumCtorResidSpec (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absU n_f) (absIConstantVal cv_ca) (absEIdxL p_fvs) (absEIdxL x_fvs)
        (absEIdx xrest)) := by
  rw [arena.inductives.sum_install.check_sum_ctor_resid, checkSumCtorResidSpec]
  lockstep
  · -- the residual is the family at the parameters: the twin's test holds
    rename_i a3 a2 hT _ x hl1 hl2 k hk
    have e := absEIdxL_of_takeEidx hT
    have hb : List.map absEIdx a2.val = List.map absEIdx p_fvs.val := beq_iff_eq.mp hc
    simp only [absEIdxL] at e
    have hlen : a3.val.length = n_p.val + n_idx.val := by
      scalar_tac
    have hkk : k.val = n_p.val := by
      rcases hk with h | h
      · exact h
      · exfalso; have := a3.property; scalar_tac
    have hd : List.drop n_p.val (List.map absEIdx a3.val) = List.map absEIdx a.val := by
      have := hP; simp only [Lockstep.TwinEq, absEIdxL, hkk] at this; exact this
    rw [if_pos (by simp [← e, hb, hlen]), hd]
    exact check_sum_ctor_sorts_ls hrel hinv hfe0 hfe
  · -- the parameter spine differs: both sides decline
    rename_i a3 a2 hT _ _ _
    have e := absEIdxL_of_takeEidx hT
    simp only [absEIdxL] at e
    have hne : ¬ (List.take n_p.val (List.map absEIdx a3.val) = List.map absEIdx p_fvs.val) := by
      rw [← e]; simpa using hc
    rw [if_neg (by simp [hne])]
    lockstep

open Lockstep in
open scoped ConRon.Refine2.IndInstPrims in
/-- `check_sum_ctor_frames` ⊑ `checkSumCtor`'s frame stage. -/
@[lockstep] theorem check_sum_ctor_frames_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf0 lf0}
    {rf lf}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx}
    {is_prop large : Bool}
    {n_f : Std.U64}
    {cv_ta cv_ca : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe0 : IFEnvRelI rf0 lf0)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = (fun r => (absIConstantVal r.1, absLIdxL r.2)) a) (arena.inductives.sum_install.check_sum_ctor_frames pers st mode rf0 rf t lps n_p n_idx res_sort is_prop large n_f cv_ta cv_ca) lst
      (checkSumCtorFramesSpec (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absU n_f) (absIConstantVal cv_ta) (absIConstantVal cv_ca)) := by
  rw [arena.inductives.sum_install.check_sum_ctor_frames, checkSumCtorFramesSpec]
  lockstep

open Lockstep in
open scoped ConRon.Refine2.IndInstPrims in
/-- `check_sum_ctor` ⊑ `checkSumCtor` — stage 2, one constructor's type. -/
@[lockstep] theorem check_sum_ctor_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf0 lf0}
    {rf lf}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx}
    {is_prop large : Bool}
    {cv_c : arena.env.IConstantVal}
    {n_f : Std.U64}
    {cv_ta : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe0 : IFEnvRelI rf0 lf0)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = (fun r => (absIConstantVal r.1, absLIdxL r.2)) a) (arena.inductives.sum_install.check_sum_ctor pers st mode rf0 rf t lps n_p n_idx res_sort is_prop large cv_c n_f cv_ta) lst
      (checkSumCtor (ConRon.Refine.absMode mode) lf0 lf (absNIdx t) (absNIdxL lps)
        (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absIConstantVal cv_c) (absU n_f) (absIConstantVal cv_ta)) := by
  rw [arena.inductives.sum_install.check_sum_ctor, checkSumCtor_unfold]
  lockstep

theorem check_sum_ctors_aux (m : Nat) :
    ∀ {pers st lst} {mode : kernel.env.CheckMode} {rf0 lf0 rf lf}
      {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
      {n_p n_idx : Std.U64} {res_sort : arena.handle.LIdx} {is_prop large : Bool}
      {cv_ta : arena.env.IConstantVal}
      {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
      {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
      {sout : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)},
      ctors.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf0 lf0 → IFEnvRelI rf lf →
      Lockstep.LS pers (fun a b => b = (absCtorsL a.1, absLIdxLL a.2))
        (arena.inductives.sum_install.check_sum_ctors pers st mode rf0 rf t lps
          n_p n_idx res_sort is_prop large cv_ta ctors i out sout) lst
        (do
          let q ← checkSumCtors (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
            (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
            (absIConstantVal cv_ta) (absCtorsLFrom ctors i)
          pure (absCtorsL out ++ q.1, absLIdxLL sout ++ q.2)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf0 lf0 rf lf t lps n_p n_idx res_sort is_prop large cv_ta ctors i
      out sout hn hrel hinv hfe0 hfe
    rw [arena.inductives.sum_install.check_sum_ctors, if_pos (by scalar_tac), absCtorsLFrom,
      vecFrom_nil _ _ _ (by omega), checkSumCtors]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf0 lf0 rf lf t lps n_p n_idx res_sort is_prop large cv_ta ctors i
      out sout hn hrel hinv hfe0 hfe
    rw [arena.inductives.sum_install.check_sum_ctors, if_neg (by scalar_tac), absCtorsLFrom,
      vecFrom_cons _ _ _ (by omega), checkSumCtors]
    lockstep

open Lockstep in
/-- `check_sum_ctors` ⊑ `checkSumCtors` from the cursor on, with the
accumulated constructors and sort lists in front. -/
@[lockstep] theorem check_sum_ctors_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf0 lf0}
    {rf lf}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx}
    {is_prop large : Bool}
    {cv_ta : arena.env.IConstantVal}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {sout : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe0 : IFEnvRelI rf0 lf0)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = (fun r => (absCtorsL r.1, absLIdxLL r.2)) a) (arena.inductives.sum_install.check_sum_ctors pers st mode rf0 rf t lps n_p n_idx res_sort is_prop large cv_ta ctors i out sout) lst
      (do
        let q ← checkSumCtors (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
          (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
          (absIConstantVal cv_ta) (absCtorsLFrom ctors i)
        pure (absCtorsL out ++ q.1, absLIdxLL sout ++ q.2)) :=
  check_sum_ctors_aux _ rfl hrel hinv hfe0 hfe

/-- `cons_sum_ctors` ⊑ `consSumCtors` from the cursor on — the constructors'
conses, in order (the first constructor deepest).  **Pure on both sides**: the
index push touches no term, so there is no monad and no state, and the
statement is an `IFEnvRel` of two folds. -/
theorem cons_sum_ctors_refines {n_p : Std.U64}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {rf lf} {o}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.inductives.sum_install.cons_sum_ctors n_p ctors i rf = ok o) :
    IFEnvRel o (consSumCtors (absU n_p) (absCtorsLFrom ctors i) lf) ∧
      IFEnvInv o := by
  refine cursor_induction (fun i : Std.Usize => i.val) ctors.val.length
    (fun i rf => ∀ lf o, IFEnvRel rf lf → IFEnvInv rf →
      arena.inductives.sum_install.cons_sum_ctors n_p ctors i rf = ok o →
      IFEnvRel o (consSumCtors (absU n_p) (absCtorsLFrom ctors i) lf) ∧ IFEnvInv o)
    ?_ ?_ i rf lf o hfe hfinv hrun
  · intro i rf hn lf o hfe hfinv h
    rw [arena.inductives.sum_install.cons_sum_ctors.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ctors by scalar_tac)] at h
    obtain rfl := Result.ok_injective h
    rw [absCtorsLFrom, List.drop_eq_nil_of_le hn]
    exact ⟨hfe, hfinv⟩
  · intro i rf hi ih lf o hfe hfinv h
    rw [arena.inductives.sum_install.cons_sum_ctors.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ctors by scalar_tac)] at h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨iv, nf⟩ := p
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨fe1, hfe1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx : ctors.val[i.val]? = some (iv, nf) := vec_index_some hp
    obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hrel1, hinv1⟩ := ifenv_push_refines (ci := .CtorInfo _ _ _) hfe hfinv trivial hfe1
    have h3 : i3.val = i.val + 1 := by
      have := ConRon.Refine.Nat.uadd_val hi3; simpa using this
    have hdrop : absCtorsLFrom ctors i
        = (absIConstantVal iv, absU nf) :: absCtorsLFrom ctors i3 := by
      rw [absCtorsLFrom, absCtorsLFrom, h3,
        List.drop_eq_getElem_cons hb, hxv]
      simp
    rw [hdrop, consSumCtors]
    refine ih i3 fe1 h3 _ o ?_ hinv1 h
    have : absIConstantInfo (arena.env.IConstantInfo.CtorInfo iv1 n_p nf)
        = IConstantInfo.ctorInfo (absIConstantVal iv) (absU n_p) (absU nf) := by
      simp [absIConstantInfo, i_constant_val_dup_abs hiv1]
    rwa [this] at hrel1

open Lockstep in
/-- `cons_sum_ctors` against `consSumCtors`: a pure Rust-only step, the related
and well-formed environment after the folds. -/
@[lockstep] theorem cons_sum_ctors_ls {n_p : Std.U64}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {rf lf} (hfe : IFEnvRelI rf lf) :
    LSP (arena.inductives.sum_install.cons_sum_ctors n_p ctors i rf)
      (fun o => IFEnvRelI o (consSumCtors (absU n_p) (absCtorsLFrom ctors i) lf)) :=
  fun _ h => cons_sum_ctors_refines hfe.rel hfe.inv h

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.whnf_telescope_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_telescope_ls

/-- info: 'ConRon.Refine2.check_sum_ctor_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_sum_ctor_ls

/-- info: 'ConRon.Refine2.cons_sum_ctors_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cons_sum_ctors_refines

end ConRon.Refine2
