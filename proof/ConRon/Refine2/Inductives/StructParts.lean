/-
# `ConRon.Refine2.Inductives.StructParts` — Theorem 2 for `arena::inductives::struct_parts`

**Task #97-P5-Ind** (DESIGN.md §8.2); repaired by **task #105**.
`crates/con-ron-core/src/arena/inductives/struct_parts.rs` against
`proof/ConRon/Arena/Inductives/StructParts.lean`: what survives of the direct
install's parts under the uniform inductive route — the level list and the
parameter spine, the elimination level, a constructor residual's shape, the
projection bodies and guards, and the memoised `hasLooseBVarB` walk
(`mentionsConst` is proved in `Refine2/Checker/Leaves.lean`).  The generators
of the old direct recursor (families, spines, rule bodies, the Π→Π/λ
rewrites, `structShape`, `structPartsCore?`) left with their Rust in task
#105.  `Refine2/Inductives/Spec.lean` carries the transcription of every
fragment DESIGN §3.4's rules cut out.

## What the cursor companions claim

The `…_from` / `…_go` cursor recursions carry an
accumulator.  Every one of them PUSHES on the way in where the twin CONSES on
the way out, so the shape is the same in all of them:

    <abs> o = <abs> out ++ <the twin from the cursor on>

which is the same reading `Refine2/ExprOps/Read.lean` gives the `expr_ops`
cursors, and is sound for the same reason: the two orders of EFFECT agree
(the port interns the `k`-th element before it recurses, and so does the twin
— see `Arena/Inductives/StructParts.lean`'s own `structPsAt.go`).

## The two memo-threading walks

`has_loose_bvar_b_go` threads a `HashMap2<EIdxNat, bool>` and
`mentions_const_go` a `HashMap2<EIdx, bool>`, both by value, moved in and
returned — the twin's `AM (Bool × Std.HashMap …)` term for term.  The shapes
are `Refine2/ExprOps/Read.lean`'s **`WOut`** and **`LOut`** at their own
memos, reused rather than re-declared: task #97-P5-0's finding 4 is met for
the third time and the answer has not changed.

## What these lemmas wait on

`Refine2/Specs.lean`'s `intern_*` family, `Refine2/ExprOps/**`'s
`inst_pis_at_lift`, `Refine2/Core/LS/{Leaves,Prims}.lean`'s `zero_level` and
spine readers (`get_app_fn`, `get_app_args`), and `Refine2/Inductives/Spec.lean`'s
`_unfold` equations.  **No clause of `KnotRel`.**
-/
import ConRon.Refine2.Inductives.Spec
import ConRon.Refine2.Core.LS.Leaves
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open scoped ConRon.Refine2.IndSide

open ConRon.Arena
open ConRon.Refine2.ExprOps (WMemoRel LMemoRel)

/-! ## Helpers for Shape/Abs

Bridges this file needs from tiers that do not reach it: `Checker/Base`'s
`absU_beq_u64` (restated), `Core/Arms/Delta`'s `core_walk_fuel_abs` as a
`lockstep_simp` fact (it is one in `Checker/KnotHyp`), and `inst_pis_at_lift`'s
`ExprOps` companion at the walk fuel and this tier's abstractions.  All three
are `local` so nothing clashes when those tiers are imported together. -/

theorem sp_absU_beq_u64 (a b : Std.U64) :
    (absU a == absU b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : absU a ≠ absU b := fun e => h (Std.UScalar.eq_of_val_eq e)
    simp [h, this]

attribute [local lockstep_simp] sp_absU_beq_u64 core_walk_fuel_abs

open Lockstep in
theorem sp_inst_pis_at_lift_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (args : alloc.vec.Vec arena.handle.EIdx)
    (h : arena.handle.EIdx) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.expr_ops.inst_pis_at_lift pers st arena.core.CORE_WALK_FUEL args h) lst
      (instPisAtLift coreWalkFuel (absEIdxL args) (absEIdx h)) := by
  have := inst_pis_at_lift_ls hrel hinv arena.core.CORE_WALK_FUEL args h
  rw [core_walk_fuel_abs] at this
  exact this

attribute [local lockstep] sp_inst_pis_at_lift_ls

/-! ## The level lists -/

/-- `param_levels_go` ⊑ `paramLevels`' inner `go`, from the cursor on. -/
theorem param_levels_go_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.param_levels_go pers st lps i out = ok o) :
    Sim₀ absLIdxL pers lst o
      (do pure (absLIdxL out ++ (← paramLevelsGoSpec (absNIdxLFrom lps i)))) := by
  simp only [absLIdxL, absNIdxLFrom]
  refine sim_vec_cursor_copy lps ⟨⟨0#u32⟩⟩ absNIdx absLIdx
    (fun n => Arena.internLNode (.param n)) paramLevelsGoSpec
    (fun s i out => arena.inductives.struct_parts.param_levels_go pers s lps i out)
    rfl (fun _ _ => rfl) ?_ ?_ i out st lst o hrel hinv hrun
  · intro st i out o hn h
    rw [arena.inductives.struct_parts.param_levels_go.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len lps by scalar_tac)] at h
    exact (Result.ok_injective h).symm
  · intro st lst i x out o hx hrel hinv h
    rw [arena.inductives.struct_parts.param_levels_go.eq_def] at h
    have hlt : i.val < lps.val.length := by
      rcases Nat.lt_or_ge i.val lps.val.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hx; cases hx
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len lps by scalar_tac)] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨r, st1⟩ := p
    have hnx : n = x := by
      have := vec_index_some hn; rw [hx] at this; exact (Option.some.inj this).symm
    have hn1n : n1 = n := dupId_nidx n n1 hn1
    subst hnx; subst hn1n
    refine ⟨r, st1, intern_l_node_run₀ hrel hinv _ hp, ?_, ?_⟩
    · intro u hu
      subst hu
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨i2, out1, ?_, ConRon.Refine.vec_push_val hout1, h⟩
      have := ConRon.Refine.Nat.uadd_val hi2
      simpa using this
    · intro e he
      subst he
      exact (Result.ok_injective h).symm

open Lockstep in
@[lockstep] theorem param_levels_go_ls
    {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdxL a) (arena.inductives.struct_parts.param_levels_go pers st lps i out) lst
      (do pure (absLIdxL out ++ (← paramLevelsGoSpec (absNIdxLFrom lps i)))) :=
  LS.ofSim₀ fun _ h => param_levels_go_refines hrel hinv h

open Lockstep in
/-- `param_levels` ⊑ `paramLevels`: the cursor from `0` into an empty
accumulator, then the list node. -/
@[lockstep] theorem param_levels_ls
    {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLsIdx a) (arena.inductives.struct_parts.param_levels pers st lps) lst
                             (paramLevels (absNIdxL lps)) := by
  have hgo := param_levels_go_ls (lps := lps) (i := 0#usize)
    (out := alloc.vec.Vec.new arena.handle.LIdx) hrel hinv
  have e : (do pure (absLIdxL (alloc.vec.Vec.new arena.handle.LIdx) ++
      (← paramLevelsGoSpec (absNIdxLFrom lps 0#usize))) : AM _) =
      paramLevelsGoSpec (absNIdxL lps) := by
    simp [absLIdxL, alloc.vec.Vec.new]
  rw [e] at hgo
  rw [arena.inductives.struct_parts.param_levels, paramLevels_unfold]
  lockstep

/-! ## The families and the spines -/

/-- `struct_ps_at_from` ⊑ `structPsAt`'s inner `go` from the `k`-th parameter
on.  The port counts `k` up to `n_p` where the twin counts `n` down, which is
the `nP - k` in the statement. -/
theorem struct_ps_at_from_refines {pers st lst} {ofs n_p k : Std.U64}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_ps_at_from pers st ofs n_p k out
      = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← structPsAtGoSpec (absU ofs) (absU n_p) (absU n_p - absU k) (absU k)))) := by
  refine sim_cursor_copy (fun k : Std.U64 => k.val) (absU n_p) absEIdx
    (fun m => Arena.internBVarE (absU ofs + absU n_p - 1 - m))
    (fun m => structPsAtGoSpec (absU ofs) (absU n_p) (absU n_p - m) m)
    (fun s k out => arena.inductives.struct_parts.struct_ps_at_from pers s ofs n_p k out)
    ?_ ?_ ?_ ?_
    k out st lst o hrel hinv hrun
  · intro m hm
    rw [show absU n_p - m = 0 by omega]
    rfl
  · intro m hm
    obtain ⟨d, hd⟩ : ∃ d, absU n_p - m = d + 1 := ⟨absU n_p - m - 1, by omega⟩
    rw [hd, show absU n_p - (m + 1) = d by omega]
    rfl
  · intro st i out o hn h
    rw [arena.inductives.struct_parts.struct_ps_at_from.eq_def] at h
    rw [if_pos (show i ≥ n_p by scalar_tac)] at h
    exact (Result.ok_injective h).symm
  · intro st lst i out o hi hrel hinv h
    rw [arena.inductives.struct_parts.struct_ps_at_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ n_p by scalar_tac)] at h
    obtain ⟨a1, ha1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨a2, ha2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨a3, ha3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨r, st1⟩ := p
    have hval : absU a3 = absU ofs + absU n_p - 1 - i.val := by
      have e1 := ConRon.Refine.Nat.uadd_val ha1
      have e2 := ConRon.Refine.Nat.usub_val ha2
      have e3 := ConRon.Refine.Nat.usub_val ha3
      have hone : (1#u64 : Std.U64).val = 1 := by scalar_tac
      simp only [absU]
      omega
    refine ⟨r, st1, by rw [← hval]; exact intern_e_bvar_run₀ hrel hinv a3 hp,
      ?_, ?_⟩
    · intro u hu
      subst hu
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨i3, out1, ?_, ConRon.Refine.vec_push_val hout1, h⟩
      have := ConRon.Refine.Nat.uadd_val hi3
      simpa using this
    · intro e he
      subst he
      exact (Result.ok_injective h).symm

open Lockstep in
@[lockstep] theorem struct_ps_at_from_ls
    {pers st lst}
    {ofs n_p k : Std.U64}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.struct_parts.struct_ps_at_from pers st ofs n_p k out) lst
      (do pure (absEIdxL out ++
        (← structPsAtGoSpec (absU ofs) (absU n_p) (absU n_p - absU k) (absU k)))) :=
  LS.ofSim₀ fun _ h => struct_ps_at_from_refines hrel hinv h

/-- `struct_ps_at` ⊑ `structPsAt`. -/
theorem struct_ps_at_refines {pers st lst} {ofs n_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_ps_at pers st ofs n_p = ok o) :
    Sim₀ absEIdxL pers lst o (structPsAt (absU ofs) (absU n_p)) := by
  rw [arena.inductives.struct_parts.struct_ps_at] at hrun
  have h := struct_ps_at_from_refines hrel hinv hrun
  rw [structPsAt_unfold]
  have h0 : ((0#u64 : Std.U64)).val = 0 := by scalar_tac
  simpa [absEIdxL, alloc.vec.Vec.new, h0, absU] using h

open Lockstep in
@[lockstep] theorem struct_ps_at_ls
    {pers st lst}
    {ofs n_p : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.struct_parts.struct_ps_at pers st ofs n_p) lst
                             (structPsAt (absU ofs) (absU n_p)) :=
  LS.ofSim₀ fun _ h => struct_ps_at_refines hrel hinv h

/-- `struct_elim_level` ⊑ `structElimLevel`. -/
theorem struct_elim_level_refines {pers st lst} {elim : arena.handle.NIdx}
    {large : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_elim_level pers st elim large
      = ok o) :
    Sim₀ absLIdx pers lst o
      (structElimLevel (absNIdx elim) large) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_elim_level, structElimLevel]
  lockstep

open Lockstep in
@[lockstep] theorem struct_elim_level_ls
    {pers st lst}
    {elim : arena.handle.NIdx}
    {large : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdx a) (arena.inductives.struct_parts.struct_elim_level pers st elim large) lst
      (structElimLevel (absNIdx elim) large) :=
  LS.ofSim₀ fun _ h => struct_elim_level_refines hrel hinv h

/-! ## The generated recursor at an indexed family -/

/-- `struct_ctor_resid_ok` ⊑ `structCtorResidOk`. -/
theorem struct_ctor_resid_ok_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p ofs n_idx : Std.U64}
    {cbody : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_ctor_resid_ok pers st t lps n_p ofs
      n_idx cbody = ok o) :
    Sim₀ id pers lst o
      (structCtorResidOk (absNIdx t) (absNIdxL lps) (absU n_p) (absU ofs)
        (absU n_idx) (absEIdx cbody)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.struct_parts.struct_ctor_resid_ok, structCtorResidOk]
  lockstep

open Lockstep in
@[lockstep] theorem struct_ctor_resid_ok_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p ofs n_idx : Std.U64}
    {cbody : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.struct_ctor_resid_ok pers st t lps n_p ofs n_idx cbody) lst
      (structCtorResidOk (absNIdx t) (absNIdxL lps) (absU n_p) (absU ofs)
        (absU n_idx) (absEIdx cbody)) :=
  LS.ofSim₀ fun _ h => struct_ctor_resid_ok_refines hrel hinv h

/-! ## The projection bodies -/

/-- `struct_proj_ps` ⊑ `structProjPs`. -/
theorem struct_proj_ps_refines {pers st lst} {n_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_ps pers st n_p = ok o) :
    Sim₀ absEIdxL pers lst o (structProjPs (absU n_p)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_proj_ps, structProjPs]
  lockstep

open Lockstep in
@[lockstep] theorem struct_proj_ps_ls
    {pers st lst}
    {n_p : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.struct_parts.struct_proj_ps pers st n_p) lst
                             (structProjPs (absU n_p)) :=
  LS.ofSim₀ fun _ h => struct_proj_ps_refines hrel hinv h

/-- `struct_proj_arg_p` ⊑ `structProjArgP`. -/
theorem struct_proj_arg_p_refines {pers st lst} {t : arena.handle.NIdx}
    {j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_arg_p pers st t j = ok o) :
    Sim₀ absEIdx pers lst o
      (structProjArgP (absNIdx t) (absU j)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_proj_arg_p, structProjArgP]
  lockstep

open Lockstep in
@[lockstep] theorem struct_proj_arg_p_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.struct_parts.struct_proj_arg_p pers st t j) lst
      (structProjArgP (absNIdx t) (absU j)) :=
  LS.ofSim₀ fun _ h => struct_proj_arg_p_refines hrel hinv h

open Lockstep in
/-- `struct_proj_resid_p` by induction on the count `i` (the port recurses on
`i - 1` first, as the twin's `i + 1` arm does). -/
theorem struct_proj_resid_p_aux {pers} {t : arena.handle.NIdx}
    {n_p : Std.U64} {cty : arena.handle.EIdx} :
    ∀ (n : Nat) (i : Std.U64) st lst, i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = (Option.map absEIdx) a)
        (arena.inductives.struct_parts.struct_proj_resid_p pers st t n_p cty i) lst
        (structProjResidP (absNIdx t) (absU n_p) (absEIdx cty) (absU i)) := by
  intro n
  induction n with
  | zero =>
    intro i st lst hi hrel hinv
    have h0 : i = 0#u64 := by scalar_tac
    subst h0
    rw [arena.inductives.struct_parts.struct_proj_resid_p.eq_def, if_pos rfl,
      show absU (0#u64 : Std.U64) = 0 from rfl, structProjResidP]
    lockstep
  | succ n ih =>
    intro i st lst hi hrel hinv
    rw [arena.inductives.struct_parts.struct_proj_resid_p.eq_def, if_neg (by scalar_tac),
      show absU i = n + 1 by simp [absU, hi], structProjResidP]
    lockstep

/-- `struct_proj_resid_p` ⊑ `structProjResidP`. -/
theorem struct_proj_resid_p_refines {pers st lst} {t : arena.handle.NIdx}
    {n_p : Std.U64} {cty : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_resid_p pers st t n_p cty i
      = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structProjResidP (absNIdx t) (absU n_p) (absEIdx cty) (absU i)) :=
  Lockstep.LS.toSim₀ (struct_proj_resid_p_aux _ i st lst rfl hrel hinv) hrun

open Lockstep in
@[lockstep] theorem struct_proj_resid_p_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {n_p : Std.U64}
    {cty : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.struct_parts.struct_proj_resid_p pers st t n_p cty i) lst
      (structProjResidP (absNIdx t) (absU n_p) (absEIdx cty) (absU i)) :=
  LS.ofSim₀ fun _ h => struct_proj_resid_p_refines hrel hinv h

/-! ## `hasLooseBVarB` — the cutoff, the memo and the walk

`hlb_probe` and `has_loose_bvar_b_ins` are the memo's two primitives, split
off by task #97-P4c's **extraction rule 5** (a `HashMap::get` match that
produces a value is its own function).  The walk is `WOut`. -/

/-- `hlb_probe` ⊑ `memo[(h, i)]?` — the probe answers what the twin's map
answers, which is exactly what `WMemoRel` says. -/
theorem hlb_probe_refines
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {k : arena.monad.EIdxNat} {o}
    (hm : WMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.hlb_probe rm k = ok o) :
    o = lm[absEIdxNat k]? := by
  rw [arena.inductives.struct_parts.hlb_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hmr, hminv⟩ := hm
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hminv
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hmr k trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option Bool) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some v =>
    rw [hrc] at hrun
    have h2 : some v = o := Result.ok_injective hrun
    subst h2
    rfl

open Lockstep in
@[lockstep] theorem hlb_probe_twin
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool}
    {k : arena.monad.EIdxNat}
    (hm : WMemoRel rm lm) :
    LSP (arena.inductives.struct_parts.hlb_probe rm k) (fun o => TwinEq (lm[absEIdxNat k]?) (o)) :=
  fun _o h => (hlb_probe_refines hm h).symm

/-- `has_loose_bvar_b_ins` ⊑ `hasLooseBVarBIns` — one answer recorded. -/
theorem has_loose_bvar_b_ins_refines {e : arena.handle.EIdx} {i : Std.U64}
    {r : Bool × ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {o}
    (hm : WMemoRel r.2 lm)
    (hrun : arena.inductives.struct_parts.has_loose_bvar_b_ins e i r = ok o) :
    o.1 = (hasLooseBVarBIns (absEIdx e) (absU i) (r.1, lm)).1 ∧
      WMemoRel o.2 (hasLooseBVarBIns (absEIdx e) (absU i) (r.1, lm)).2 := by
  obtain ⟨b, memo⟩ := r
  rw [arena.inductives.struct_parts.has_loose_bvar_b_ins] at hrun
  obtain ⟨en, hen, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, memo1⟩ := q
  have ho : (b, memo1) = o := Result.ok_injective hrun
  obtain ⟨hrel, hinv⟩ := hm
  rw [arena.monad.eidx_nat_key] at hen
  obtain ⟨e1, he1, hen⟩ := ConRon.Refine.bind_eq_ok_iff.mp hen
  have henv : en = ⟨e1, i⟩ := (Result.ok_injective hen).symm
  have hee : e1 = e := dupId_eidx e e1 he1
  have hinj : ∀ a b : arena.monad.EIdxNat, True → True →
      absEIdxNat a = absEIdxNat b → a = b := by
    intro a b _ _ hab
    obtain ⟨⟨wa⟩, da⟩ := a; obtain ⟨⟨wb⟩, db⟩ := b
    simp only [absEIdxNat, absEIdx, Prod.mk.injEq, Idx.ofWord.injEq] at hab
    have hw : wa = wb := absU32_inj hab.1
    have hd : da = db := Std.UScalar.eq_imp _ _ hab.2
    rw [hw, hd]
  subst henv
  subst hee
  obtain ⟨hrel', hkeys'⟩ :=
    ConRon.Refine.HashMap2.Rel_insert_wf eidxNat_eq2 hinj hinv
      ConRon.Refine.HashMap2.KeysOk_true hrel trivial hq
  have hinv' := (ConRon.Refine.HashMap2.insert_refines_wf eidxNat_eq2 hinv
    ConRon.Refine.HashMap2.KeysOk_true trivial hq).1
  rw [← ho]
  exact ⟨rfl, ⟨hrel', hinv'⟩⟩

open Lockstep in
/-- `has_loose_bvar_b_ins` against the twin's `hasLooseBVarBIns` at a related
walk answer. -/
@[lockstep] theorem has_loose_bvar_b_ins_ls {e : arena.handle.EIdx} {i : Std.U64}
    {r : Bool × ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} (hm : WMemoRel r.2 lm) :
    LSP (arena.inductives.struct_parts.has_loose_bvar_b_ins e i r)
      (fun o => WOutRel o (hasLooseBVarBIns (absEIdx e) (absU i) (r.1, lm))) :=
  fun _ h => has_loose_bvar_b_ins_refines hm h

open Lockstep in
/-- `has_loose_bvar_b_node` at fuel `m`, from `has_loose_bvar_b_go` at fuel `m`
(the fuel induction's hypothesis). -/
theorem has_loose_bvar_b_node_of_go {pers : arena.store.PersTier} {m : Nat}
    (hgo : ∀ {st : arena.monad.AState} {lst : AState}
      (rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
      (lm : Std.HashMap (EIdx × Nat) Bool) (i fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = m → AStateRel₀ pers st lst → AStateInv pers st → WMemoRel rm lm →
      LS pers WOutRel
        (arena.inductives.struct_parts.has_loose_bvar_b_go pers st rm i fuel h) lst
        (hasLooseBVarBGo lm (absU i) m (absEIdx h))) :
    ∀ (st : arena.monad.AState) (lst : AState)
      (rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
      (lm : Std.HashMap (EIdx × Nat) Bool) (i fuel : Std.U64) (v : arena.store.ENodeView),
      fuel.val = m → AStateRel₀ pers st lst → AStateInv pers st → WMemoRel rm lm →
      LS pers WOutRel
        (arena.inductives.struct_parts.has_loose_bvar_b_node pers st rm i fuel v) lst
        (hasLooseBVarBNodeSpec lm (absU i) m (absENodeView v)) := by
  intro st lst rm lm i fuel v hf hrel hinv hm
  rw [arena.inductives.struct_parts.has_loose_bvar_b_node.eq_def]
  cases v <;> simp only [absENodeView, hasLooseBVarBNodeSpec] <;> lockstep

open Lockstep in
/-- `has_loose_bvar_b_go` ⊑ `hasLooseBVarBGo`, by induction on the fuel. -/
theorem has_loose_bvar_b_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
      (lm : Std.HashMap (EIdx × Nat) Bool) (i fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → WMemoRel rm lm →
      LS pers WOutRel
        (arena.inductives.struct_parts.has_loose_bvar_b_go pers st rm i fuel h) lst
        (hasLooseBVarBGo lm (absU i) n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm i fuel h hn hrel hinv hm
    have h0 : fuel = 0#u64 := by scalar_tac
    subst h0
    rw [arena.inductives.struct_parts.has_loose_bvar_b_go, hasLooseBVarBGo]
    lockstep
  | succ m ih =>
    intro pers st lst rm lm i fuel h hn hrel hinv hm
    have hnode := has_loose_bvar_b_node_of_go (pers := pers) (m := m) (fun {st lst} => @ih pers st lst)
    rw [arena.inductives.struct_parts.has_loose_bvar_b_go, hasLooseBVarBGo_unfold]
    rw [if_neg (by scalar_tac)]
    lockstep

open Lockstep in
@[lockstep] theorem has_loose_bvar_b_node_ls
    {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool}
    {i fuel : Std.U64}
    {v : arena.store.ENodeView}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hm : WMemoRel rm lm) :
    LS pers WOutRel (arena.inductives.struct_parts.has_loose_bvar_b_node pers st rm i fuel v) lst
      (hasLooseBVarBNodeSpec lm (absU i) (absU fuel) (absENodeView v)) :=
  has_loose_bvar_b_node_of_go (m := fuel.val)
    (fun {st lst} => @has_loose_bvar_b_go_aux _ pers st lst) st lst rm lm i fuel v rfl hrel hinv hm

open Lockstep in
@[lockstep] theorem has_loose_bvar_b_go_ls
    {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool}
    {i fuel : Std.U64}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hm : WMemoRel rm lm) :
    LS pers WOutRel (arena.inductives.struct_parts.has_loose_bvar_b_go pers st rm i fuel h) lst
      (hasLooseBVarBGo lm (absU i) (absU fuel) (absEIdx h)) :=
  has_loose_bvar_b_go_aux _ rm lm i fuel h rfl hrel hinv hm

/-- `has_loose_bvar_b_fast` ⊑ `hasLooseBVarBFast` — one memoised walk from the
empty memo. -/
theorem has_loose_bvar_b_fast_refines {pers st lst} {i : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.has_loose_bvar_b_fast pers st i e = ok o) :
    Sim₀ id pers lst o
      (hasLooseBVarBFast (absU i) (absEIdx e)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.struct_parts.has_loose_bvar_b_fast, hasLooseBVarBFast]
  lockstep

open Lockstep in
@[lockstep] theorem has_loose_bvar_b_fast_ls
    {pers st lst}
    {i : Std.U64}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.has_loose_bvar_b_fast pers st i e) lst
      (hasLooseBVarBFast (absU i) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => has_loose_bvar_b_fast_refines hrel hinv h

/-! ## `structUsedLater` and the guard table -/

/-- `struct_used_later` ⊑ `structUsedLater`. -/
theorem struct_used_later_refines {pers st lst} {cty : arena.handle.EIdx}
    {n_p j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_used_later pers st cty n_p j
      = ok o) :
    Sim₀ id pers lst o
      (structUsedLater (absEIdx cty) (absU n_p) (absU j)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_used_later, structUsedLater]
  lockstep

open Lockstep in
@[lockstep] theorem struct_used_later_ls
    {pers st lst}
    {cty : arena.handle.EIdx}
    {n_p j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.struct_used_later pers st cty n_p j) lst
      (structUsedLater (absEIdx cty) (absU n_p) (absU j)) :=
  LS.ofSim₀ fun _ h => struct_used_later_refines hrel hinv h

open Lockstep in
@[lockstep] theorem struct_used_later_go_ls
    {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool}
    {cty : arena.handle.EIdx}
    {n_p j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hm : WMemoRel rm lm) :
    LS pers WOutRel (arena.inductives.struct_parts.struct_used_later_go pers st rm cty n_p j) lst
      (structUsedLaterGo lm (absEIdx cty) (absU n_p) (absU j)) := by
  rw [arena.inductives.struct_parts.struct_used_later_go, structUsedLaterGo]
  lockstep

open Lockstep in
theorem struct_used_later_list_aux {pers} {cty : arena.handle.EIdx} {n_p : Std.U64} (N : Nat) :
    ∀ (n : Std.U64) (base : Std.U64) (rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
      (lm : Std.HashMap (EIdx × Nat) Bool) (out : alloc.vec.Vec Bool) st lst, n.val = N →
      AStateRel₀ pers st lst → AStateInv pers st → WMemoRel rm lm →
      LS pers (fun a b => b = absBoolL a)
        (arena.inductives.struct_parts.struct_used_later_list pers st rm cty n_p n base out) lst
        (do pure (absBoolL out ++
          (← structUsedLaterList (absEIdx cty) (absU n_p) lm (absU n) (absU base)))) := by
  induction N with
  | zero =>
    intro n base rm lm out st lst hn hrel hinv hm
    have h0 : n = 0#u64 := by scalar_tac
    subst h0
    rw [arena.inductives.struct_parts.struct_used_later_list.eq_def, if_pos rfl,
      show absU (0#u64 : Std.U64) = 0 from rfl, structUsedLaterList]
    lockstep
  | succ N ih =>
    intro n base rm lm out st lst hn hrel hinv hm
    rw [arena.inductives.struct_parts.struct_used_later_list.eq_def, if_neg (by scalar_tac),
      show absU n = N + 1 by simp [absU, hn], structUsedLaterList]
    lockstep

/-- `struct_used_later_list` ⊑ `structUsedLaterList`, with the accumulated
answers in front. -/
theorem struct_used_later_list_refines {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {cty : arena.handle.EIdx}
    {n_p n base : Std.U64} {out : alloc.vec.Vec Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hm : WMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.struct_used_later_list pers st rm cty n_p n
      base out = ok o) :
    Sim₀ absBoolL pers lst o
      (do pure (absBoolL out ++
        (← structUsedLaterList (absEIdx cty) (absU n_p) lm (absU n) (absU base)))) :=
  Lockstep.LS.toSim₀ (struct_used_later_list_aux _ n base rm lm out st lst rfl hrel hinv hm) hrun

open Lockstep in
@[lockstep] theorem struct_used_later_list_ls
    {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool}
    {cty : arena.handle.EIdx}
    {n_p n base : Std.U64}
    {out : alloc.vec.Vec Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hm : WMemoRel rm lm) :
    LS pers (fun a b => b = absBoolL a) (arena.inductives.struct_parts.struct_used_later_list pers st rm cty n_p n base out) lst
      (do pure (absBoolL out ++
        (← structUsedLaterList (absEIdx cty) (absU n_p) lm (absU n) (absU base)))) :=
  LS.ofSim₀ fun _ h => struct_used_later_list_refines hrel hinv hm h

/-- `used_get_d` ⊑ `used.getD j false`. -/
theorem used_get_d_refines {used : alloc.vec.Vec Bool} {j : Std.U64} {o}
    (hrun : arena.inductives.struct_parts.used_get_d used j = ok o) :
    o = (absBoolL used).getD (absU j) false := by
  -- task #97-P5-Usize: the bound is compared in `u64` (round 3 §R3.5).
  rw [arena.inductives.struct_parts.used_get_d] at hrun
  obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  simp only [lift, Result.ok.injEq] at hi1
  have hi1v : i1.val = used.val.length := by
    rw [← hi1, ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
  by_cases hlt : j < i1
  · rw [if_pos hlt] at hrun
    have hlt' : j.val < used.val.length := by scalar_tac
    obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    simp only [lift, Result.ok.injEq] at hi2
    have hi2v : i2.val = j.val := by
      rw [← hi2]
      exact ConRon.Refine.ExprOps.u64_cast_usize_val
        (le_trans (Nat.le_of_lt hlt') used.property)
    have hx := vec_index_some hrun
    rw [hi2v] at hx
    simp [absBoolL, absU, List.getD_eq_getElem?_getD, hx]
  · rw [if_neg hlt] at hrun
    obtain rfl := Result.ok_injective hrun
    have hge : used.val.length ≤ j.val := by scalar_tac
    simp [absBoolL, absU, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa using hge)]

open Lockstep in
@[lockstep] theorem used_get_d_twin
    {used : alloc.vec.Vec Bool}
    {j : Std.U64} :
    LSP (arena.inductives.struct_parts.used_get_d used j) (fun o => TwinEq ((absBoolL used).getD (absU j) false) (o)) :=
  fun _o h => (used_get_d_refines h).symm

/-- `sort_get_d` ⊑ `sorts.getD j z`. -/
theorem sort_get_d_refines {sorts : alloc.vec.Vec arena.handle.LIdx} {j : Std.U64}
    {z : arena.handle.LIdx} {o}
    (hrun : arena.inductives.struct_parts.sort_get_d sorts j z = ok o) :
    absLIdx o = (absLIdxL sorts).getD (absU j) (absLIdx z) := by
  -- task #97-P5-Usize: the bound is compared in `u64` (round 3 §R3.5).
  rw [arena.inductives.struct_parts.sort_get_d] at hrun
  obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  simp only [lift, Result.ok.injEq] at hi1
  have hi1v : i1.val = sorts.val.length := by
    rw [← hi1, ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
  by_cases hlt : j < i1
  · rw [if_pos hlt] at hrun
    have hlt' : j.val < sorts.val.length := by scalar_tac
    obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    simp only [lift, Result.ok.injEq] at hi2
    have hi2v : i2.val = j.val := by
      rw [← hi2]
      exact ConRon.Refine.ExprOps.u64_cast_usize_val
        (le_trans (Nat.le_of_lt hlt') sorts.property)
    obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hx := vec_index_some hl
    rw [hi2v] at hx
    rw [dupId_lidx _ _ hrun]
    simp [absLIdxL, absU, List.getD_eq_getElem?_getD, hx]
  · rw [if_neg hlt] at hrun
    rw [dupId_lidx _ _ hrun]
    have hge : sorts.val.length ≤ j.val := by scalar_tac
    simp [absLIdxL, absU, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa using hge)]

open Lockstep in
@[lockstep] theorem sort_get_d_twin
    {sorts : alloc.vec.Vec arena.handle.LIdx}
    {j : Std.U64}
    {z : arena.handle.LIdx} :
    LSP (arena.inductives.struct_parts.sort_get_d sorts j z) (fun o => TwinEq ((absLIdxL sorts).getD (absU j) (absLIdx z)) (absLIdx o)) :=
  fun _o h => (sort_get_d_refines h).symm

/-- `struct_proj_guards_col` ⊑ `structProjGuards`' `col`. -/
theorem struct_proj_guards_col_refines {pers st lst} {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec arena.handle.LIdx} {z : arena.handle.LIdx}
    {j k : Std.U64} {acc : arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_guards_col pers st used sorts z
      j k acc = ok o) :
    Sim₀ absLIdx pers lst o
      (structProjGuardsColSpec (absBoolL used) (absLIdxL sorts) (absLIdx z)
        (absU j) (absU k) (absLIdx acc)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  induction hk : k.val generalizing k j acc st lst with
  | zero =>
    rw [arena.inductives.struct_parts.struct_proj_guards_col.eq_def,
      if_pos (by scalar_tac), show absU k = 0 from hk, structProjGuardsColSpec]
    lockstep
  | succ m ih =>
    rw [arena.inductives.struct_parts.struct_proj_guards_col.eq_def,
      if_neg (by scalar_tac), show absU k = m + 1 from hk, structProjGuardsColSpec]
    lockstep

open Lockstep in
@[lockstep] theorem struct_proj_guards_col_ls
    {pers st lst}
    {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec arena.handle.LIdx}
    {z : arena.handle.LIdx}
    {j k : Std.U64}
    {acc : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdx a) (arena.inductives.struct_parts.struct_proj_guards_col pers st used sorts z j k acc) lst
      (structProjGuardsColSpec (absBoolL used) (absLIdxL sorts) (absLIdx z)
        (absU j) (absU k) (absLIdx acc)) :=
  LS.ofSim₀ fun _ h => struct_proj_guards_col_refines hrel hinv h

open Lockstep in
theorem struct_proj_guards_row_aux {pers} {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec arena.handle.LIdx} {z : arena.handle.LIdx} (N : Nat) :
    ∀ (i k : Std.U64) (out : alloc.vec.Vec arena.handle.LIdx) st lst, k.val = N →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absLIdxL a)
        (arena.inductives.struct_parts.struct_proj_guards_row pers st used sorts z i k out) lst
        (do pure (absLIdxL out ++
          (← structProjGuardsRowSpec (absBoolL used) (absLIdxL sorts) (absLIdx z)
            (absU i) (absU k)))) := by
  induction N with
  | zero =>
    intro i k out st lst hk hrel hinv
    have h0 : k = 0#u64 := by scalar_tac
    subst h0
    rw [arena.inductives.struct_parts.struct_proj_guards_row.eq_def, if_pos rfl,
      show absU (0#u64 : Std.U64) = 0 from rfl, structProjGuardsRowSpec]
    lockstep
  | succ N ih =>
    intro i k out st lst hk hrel hinv
    rw [arena.inductives.struct_parts.struct_proj_guards_row.eq_def, if_neg (by scalar_tac),
      show absU k = N + 1 by simp [absU, hk], structProjGuardsRowSpec]
    lockstep

/-- `struct_proj_guards_row` ⊑ `structProjGuards`' `row`, with the accumulated
guards in front. -/
theorem struct_proj_guards_row_refines {pers st lst} {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec arena.handle.LIdx} {z : arena.handle.LIdx}
    {i k : Std.U64} {out : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_guards_row pers st used sorts z
      i k out = ok o) :
    Sim₀ absLIdxL pers lst o
      (do pure (absLIdxL out ++
        (← structProjGuardsRowSpec (absBoolL used) (absLIdxL sorts) (absLIdx z)
          (absU i) (absU k)))) :=
  Lockstep.LS.toSim₀ (struct_proj_guards_row_aux _ i k out st lst rfl hrel hinv) hrun

open Lockstep in
@[lockstep] theorem struct_proj_guards_row_ls
    {pers st lst}
    {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec arena.handle.LIdx}
    {z : arena.handle.LIdx}
    {i k : Std.U64}
    {out : alloc.vec.Vec arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdxL a) (arena.inductives.struct_parts.struct_proj_guards_row pers st used sorts z i k out) lst
      (do pure (absLIdxL out ++
        (← structProjGuardsRowSpec (absBoolL used) (absLIdxL sorts) (absLIdx z)
          (absU i) (absU k)))) :=
  LS.ofSim₀ fun _ h => struct_proj_guards_row_refines hrel hinv h

/-- `struct_proj_guards` ⊑ `structProjGuards`. -/
theorem struct_proj_guards_refines {pers st lst} {cty : arena.handle.EIdx}
    {n_p n_f : Std.U64} {sorts : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_guards pers st cty n_p n_f
      sorts = ok o) :
    Sim₀ absLIdxL pers lst o
      (structProjGuards (absEIdx cty) (absU n_p) (absU n_f) (absLIdxL sorts)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_proj_guards, structProjGuards_unfold]
  lockstep

open Lockstep in
@[lockstep] theorem struct_proj_guards_ls
    {pers st lst}
    {cty : arena.handle.EIdx}
    {n_p n_f : Std.U64}
    {sorts : alloc.vec.Vec arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdxL a) (arena.inductives.struct_parts.struct_proj_guards pers st cty n_p n_f sorts) lst
      (structProjGuards (absEIdx cty) (absU n_p) (absU n_f) (absLIdxL sorts)) :=
  LS.ofSim₀ fun _ h => struct_proj_guards_refines hrel hinv h

open Lockstep in
theorem struct_proj_bodies_go_aux {pers} {t : arena.handle.NIdx} (N : Nat) :
    ∀ (k i : Std.U64) (h : arena.handle.EIdx) (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      k.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = (Option.map absEIdxL) a)
        (arena.inductives.struct_parts.struct_proj_bodies_go pers st t k i h out) lst
        (do pure ((← structProjBodiesGo (absNIdx t) (absU k) (absU i) (absEIdx h)).map
          fun r => absEIdxL out ++ r)) := by
  induction N with
  | zero =>
    intro k i h out st lst hk hrel hinv
    have h0 : k = 0#u64 := by scalar_tac
    subst h0
    rw [arena.inductives.struct_parts.struct_proj_bodies_go.eq_def, if_pos rfl,
      show absU (0#u64 : Std.U64) = 0 from rfl, structProjBodiesGo]
    lockstep
  | succ N ih =>
    intro k i h out st lst hk hrel hinv
    rw [arena.inductives.struct_parts.struct_proj_bodies_go.eq_def, if_neg (by scalar_tac),
      show absU k = N + 1 by simp [absU, hk], structProjBodiesGo]
    lockstep
    -- the tail call: the twin's `some (fdom :: r)` against the port's `out`
    -- grown by `fdom`
    rename_i b out1 hout1 k1 hk1
    refine LS.tail (ih k1 _ b out1 _ _ (by scalar_tac) ‹_› ‹_›) ?_ (fun _ _ h => h)
    have e1 : absU k1 = N := by simp only [absU]; scalar_tac
    have e2 : absU a = (i : Nat) + 1 := by simp only [absU]; scalar_tac
    rw [e1, e2]
    refine am_bind_congr _ ?_; intro x
    cases x <;> simp [absEIdxL, hout1]

/-- `struct_proj_bodies_go` ⊑ `structProjBodiesGo`, with the accumulated
domains in front. -/
theorem struct_proj_bodies_go_refines {pers st lst} {t : arena.handle.NIdx}
    {k i : Std.U64} {h : arena.handle.EIdx}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_bodies_go pers st t k i h out
      = ok o) :
    Sim₀ (Option.map absEIdxL) pers lst o
      (do pure ((← structProjBodiesGo (absNIdx t) (absU k) (absU i) (absEIdx h)).map
        fun r => absEIdxL out ++ r)) :=
  Lockstep.LS.toSim₀ (struct_proj_bodies_go_aux _ k i h out st lst rfl hrel hinv) hrun

open Lockstep in
@[lockstep] theorem struct_proj_bodies_go_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {k i : Std.U64}
    {h : arena.handle.EIdx}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdxL) a) (arena.inductives.struct_parts.struct_proj_bodies_go pers st t k i h out) lst
      (do pure ((← structProjBodiesGo (absNIdx t) (absU k) (absU i) (absEIdx h)).map
        fun r => absEIdxL out ++ r)) :=
  LS.ofSim₀ fun _ h => struct_proj_bodies_go_refines hrel hinv h

open Lockstep in
/-- `struct_proj_bodies_go` from field `0` and an empty accumulator, read as
the twin's `structProjBodies` tail (the list to an array). -/
@[lockstep] theorem struct_proj_bodies_go_new_ls {pers st lst} {t : arena.handle.NIdx}
    {k : Std.U64} {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdxL a).map List.toArray)
      (arena.inductives.struct_parts.struct_proj_bodies_go pers st t k 0#u64 h
        (alloc.vec.Vec.new arena.handle.EIdx)) lst
      (do match ← structProjBodiesGo (absNIdx t) (absU k) 0 (absEIdx h) with
        | some l => pure (some l.toArray)
        | none => pure none) := by
  have h1 := LS.twin_map (f := fun o => o.map List.toArray) (R := fun a b => b = (Option.map absEIdxL a).map List.toArray)
    (struct_proj_bodies_go_aux (pers := pers) (t := t) _ k 0#u64 h (alloc.vec.Vec.new _) st lst rfl hrel hinv)
    (fun a b hb => by rw [hb])
  have e : ((do pure ((← structProjBodiesGo (absNIdx t) (absU k) (absU (0#u64 : Std.U64)) (absEIdx h)).map
      fun r => absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) ++ r)) >>=
        fun b => pure (Option.map List.toArray b) : AM _) =
      (do match ← structProjBodiesGo (absNIdx t) (absU k) 0 (absEIdx h) with
        | some l => pure (some l.toArray)
        | none => pure none) := by
    simp only [bind_assoc, pure_bind]
    refine am_bind_congr _ ?_; intro o
    cases o <;> simp [absEIdxL, alloc.vec.Vec.new]
  rwa [e] at h1


/-- `struct_proj_bodies` ⊑ `structProjBodies` — the twin's answer is an
`Array` (the table stores it so) and the port's a `Vec`, which is task
#97-P5-0's finding 5 at this module. -/
theorem struct_proj_bodies_refines {pers st lst} {t : arena.handle.NIdx}
    {n_p n_f : Std.U64} {cty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_bodies pers st t n_p n_f cty
      = ok o) :
    Sim₀ (fun r => (Option.map absEIdxL r).map List.toArray) pers lst o
      (structProjBodies (absNIdx t) (absU n_p) (absU n_f) (absEIdx cty)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_proj_bodies, structProjBodies]
  lockstep

open Lockstep in
@[lockstep] theorem struct_proj_bodies_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {cty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun r => (Option.map absEIdxL r).map List.toArray) a) (arena.inductives.struct_parts.struct_proj_bodies pers st t n_p n_f cty) lst
      (structProjBodies (absNIdx t) (absU n_p) (absU n_f) (absEIdx cty)) :=
  LS.ofSim₀ fun _ h => struct_proj_bodies_refines hrel hinv h

/-! ## `mentionsConst` -/

-- `mc_probe`, `mentions_const_go`/`_node` and `mentions_const` live in
-- `Refine2/Checker/Leaves.lean` (task #97-T2-LOCKSTEP lane Checker Base/Top):
-- the checker's base consumes the walk, so it sits below this tier.

/-! ## The axiom census

The tier's first STATEFUL `_refines` (round 4), and the shape every other one
of the family will be built from. -/

/-- info: 'ConRon.Refine2.struct_ps_at_from_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms struct_ps_at_from_refines

/-- info: 'ConRon.Refine2.used_get_d_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms used_get_d_refines

/-- info: 'ConRon.Refine2.sort_get_d_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sort_get_d_refines

end ConRon.Refine2
