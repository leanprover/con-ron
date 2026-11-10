/-
# `ConRon.Refine2.Inductives.StructParts` — Theorem 2 for `arena::inductives::struct_parts`

**Task #97-P5-Ind** (DESIGN.md §8.2); repaired by **task #105**.
`crates/con-ron-core/src/arena/inductives/struct_parts.rs` against
`proof/ConRon/Arena/Inductives/StructParts.lean`: what survives of the direct
install's parts under the uniform inductive route — the level list and the
parameter spine, the elimination level, a constructor residual's shape, the
projection bodies (`mentionsConst` is proved in `Refine2/Checker/Leaves.lean`;
the `hasLooseBVarB` walk and `structUsedLater` are the core tier's).  The generators
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

## What these lemmas wait on

`Refine2/Specs.lean`'s `intern_*` family, `Refine2/ExprOps/**`'s
`instantiate_lift_fast` and `strip_pis`, `Refine2/Core/LS/{Leaves,Prims}.lean`'s `zero_level` and
spine readers (`get_app_fn`, `get_app_args`), and `Refine2/Inductives/Spec.lean`'s
`_unfold` equations.  **No clause of `KnotRel`.**
-/
import ConRon.Refine2.Inductives.Spec
import ConRon.Refine2.Core.LS.Leaves
import ConRon.Refine2.Core.LS.Prims
import ConRon.Refine2.Checker.Base

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open scoped ConRon.Refine2.IndSide

open ConRon.Arena

/-! ## Helpers for Shape/Abs

The bridge this file needs: `Core/Arms/Delta`'s `core_walk_fuel_abs` as a
`lockstep_simp` fact (it is one in `Checker/KnotHyp`).  It is `local` so
nothing clashes when those tiers are imported together
(`Checker/Base`'s `absU_beq_u64` is a global `lockstep_simp` row). -/

attribute [local lockstep_simp] core_walk_fuel_abs

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
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len lps by scalar_tac)] at h
    exact (Result.ok_injective h).symm
  · intro st lst i x out o hx hrel hinv h
    rw [arena.inductives.struct_parts.param_levels_go.eq_def] at h
    have hlt : i.val < lps.val.length := by
      rcases Nat.lt_or_ge i.val lps.val.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hx; cases hx
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len lps by scalar_tac)] at h
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
    rw [ite_eq_left (show i ≥ n_p by scalar_tac)] at h
    exact (Result.ok_injective h).symm
  · intro st lst i out o hi hrel hinv h
    rw [arena.inductives.struct_parts.struct_ps_at_from.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ n_p by scalar_tac)] at h
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

open Lockstep in
/-- `struct_elim_level` ⊑ `structElimLevel`. -/
@[lockstep] theorem struct_elim_level_ls
    {pers st lst}
    {elim : arena.handle.NIdx}
    {large : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdx a) (arena.inductives.struct_parts.struct_elim_level pers st elim large) lst
      (structElimLevel (absNIdx elim) large) := by
  rw [arena.inductives.struct_parts.struct_elim_level, structElimLevel]
  lockstep

/-! ## The generated recursor at an indexed family -/

open Lockstep in
/-- `struct_ctor_resid_ok` ⊑ `structCtorResidOk`. -/
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
        (absU n_idx) (absEIdx cbody)) := by
  rw [arena.inductives.struct_parts.struct_ctor_resid_ok, structCtorResidOk]
  lockstep

/-! ## The projection bodies -/

open Lockstep in
/-- `struct_proj_ps` ⊑ `structProjPs`. -/
@[lockstep] theorem struct_proj_ps_ls
    {pers st lst}
    {n_p : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.struct_parts.struct_proj_ps pers st n_p) lst
                             (structProjPs (absU n_p)) := by
  rw [arena.inductives.struct_parts.struct_proj_ps, structProjPs]
  lockstep

open Lockstep in
/-- `struct_proj_arg_p` ⊑ `structProjArgP`. -/
@[lockstep] theorem struct_proj_arg_p_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.struct_parts.struct_proj_arg_p pers st t j) lst
      (structProjArgP (absNIdx t) (absU j)) := by
  rw [arena.inductives.struct_parts.struct_proj_arg_p, structProjArgP]
  lockstep

open Lockstep in
theorem struct_proj_bodies_go_aux {pers} {t : arena.handle.NIdx} (N : Nat) :
    ∀ (vs : alloc.vec.Vec arena.handle.EIdx) (k i : Std.U64) (h : arena.handle.EIdx)
      (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      k.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = (Option.map absEIdxL) a)
        (arena.inductives.struct_parts.struct_proj_bodies_go pers st t vs k i h out) lst
        (do pure ((← structProjBodiesGo (absNIdx t) (absEIdxArr vs) (absU k) (absU i)
          (absEIdx h)).map fun r => absEIdxL out ++ r)) := by
  induction N with
  | zero =>
    intro vs k i h out st lst hk hrel hinv
    have h0 : k = 0#u64 := by scalar_tac
    subst h0
    rw [arena.inductives.struct_parts.struct_proj_bodies_go.eq_def, ite_eq_left rfl,
      show absU (0#u64 : Std.U64) = 0 from rfl, structProjBodiesGo]
    lockstep
  | succ N ih =>
    intro vs k i h out st lst hk hrel hinv
    rw [arena.inductives.struct_parts.struct_proj_bodies_go.eq_def, ite_eq_right (by scalar_tac),
      show absU k = N + 1 by simp [absU, hk], structProjBodiesGo]
    lockstep
    -- the tail call: the twin's `some (fdom :: r)` against the port's `out`
    -- grown by `fdom`
    rename_i b vs1 hvs1 out1 hout1 k1 hk1
    refine LS.tail (ih vs1 k1 _ _ out1 _ _ (by scalar_tac) ‹_› ‹_›) ?_ (fun _ _ h => h)
    have e1 : absU k1 = N := by simp only [absU]; scalar_tac
    have e2 : absU a = (i : Nat) + 1 := by simp only [absU]; scalar_tac
    have e3 : absEIdxArr vs1 = (absEIdxArr vs).push (absEIdx b) := by
      simp [absEIdxArr, absEIdxL, hvs1]
    rw [e1, e2, e3]
    refine am_bind_congr _ ?_; intro x
    cases x <;> simp [absEIdxL, hout1]

open Lockstep in
/-- `struct_proj_bodies_go` from field `0` and an empty accumulator, read as
the twin's `structProjBodies` tail (the list to an array). -/
@[lockstep] theorem struct_proj_bodies_go_new_ls {pers st lst} {t : arena.handle.NIdx}
    {vs : alloc.vec.Vec arena.handle.EIdx} {k : Std.U64} {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdxL a).map List.toArray)
      (arena.inductives.struct_parts.struct_proj_bodies_go pers st t vs k 0#u64 h
        (alloc.vec.Vec.new arena.handle.EIdx)) lst
      (do match ← structProjBodiesGo (absNIdx t) (absEIdxL vs).toArray (absU k) 0 (absEIdx h) with
        | some l => pure (some l.toArray)
        | none => pure none) := by
  have h1 := LS.tail_bind_pure (f := fun o => o.map List.toArray) (R := fun a b => b = (Option.map absEIdxL a).map List.toArray)
    (struct_proj_bodies_go_aux (pers := pers) (t := t) _ vs k 0#u64 h (alloc.vec.Vec.new _) st lst rfl hrel hinv)
    (fun a b hb => by rw [hb])
  have e : ((do pure ((← structProjBodiesGo (absNIdx t) (absEIdxArr vs) (absU k) (absU (0#u64 : Std.U64)) (absEIdx h)).map
      fun r => absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) ++ r)) >>=
        fun b => pure (Option.map List.toArray b) : AM _) =
      (do match ← structProjBodiesGo (absNIdx t) (absEIdxL vs).toArray (absU k) 0 (absEIdx h) with
        | some l => pure (some l.toArray)
        | none => pure none) := by
    simp only [bind_assoc, pure_bind, absEIdxArr]
    refine am_bind_congr _ ?_; intro o
    cases o <;> simp [absEIdxL, alloc.vec.Vec.new]
  rwa [e] at h1

open Lockstep in
/-- `struct_proj_bodies` ⊑ `structProjBodies` — the twin's answer is an
`Array` (the table stores it so) and the port's a `Vec`, which is task
#97-P5-0's finding 5 at this module. -/
@[lockstep] theorem struct_proj_bodies_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {cty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun r => (Option.map absEIdxL r).map List.toArray) a) (arena.inductives.struct_parts.struct_proj_bodies pers st t n_p n_f cty) lst
      (structProjBodies (absNIdx t) (absU n_p) (absU n_f) (absEIdx cty)) := by
  rw [arena.inductives.struct_parts.struct_proj_bodies, structProjBodies]
  lockstep

/-! ## `mentionsConst` -/

-- `mc_probe`, `mentions_const_go`/`_node` and `mentions_const` live in
-- `Refine2/Checker/Leaves.lean` (task #97-T2-LOCKSTEP lane Checker Base/Top):
-- the checker's base consumes the walk, so it sits below this tier.

/-! ## The axiom census

A cursor lemma and the bodies' builder. -/

/-- info: 'ConRon.Refine2.struct_ps_at_from_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms struct_ps_at_from_refines

/-- info: 'ConRon.Refine2.struct_proj_bodies_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms struct_proj_bodies_ls

end ConRon.Refine2
