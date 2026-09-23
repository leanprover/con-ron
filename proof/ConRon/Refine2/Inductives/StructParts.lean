/-
# `ConRon.Refine2.Inductives.StructParts` — Theorem 2 for `arena::inductives::struct_parts`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/struct_parts.rs` against
`proof/ConRon/Arena/Inductives/StructParts.lean`: the direct install's
generators — the type-former family, the constructor spines, the rule bodies,
the Π→Π/λ rewrites — `StructParts` and its recogniser, the projection bodies
and guards, and the two memoised walks (`hasLooseBVarB`, `mentionsConst`).

**Fifty `pub fn`s against twenty-nine twin `def`s.**  The difference is
DESIGN §3.4's three rules and nothing else; `Refine2/Inductives/Spec.lean`
carries the transcription of every fragment they cut out, and every statement
below is either against a named twin or against one of those.

## What the cursor companions claim

Nine of the fifty are `…_from` / `…_go` cursor recursions with an
accumulator.  Every one of them PUSHES on the way in where the twin CONSES on
the way out, so the shape is the same in all nine:

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

`Refine2/Specs.lean`'s `intern_e` family and its `intern_l_node` /
`intern_n_node` siblings (the generators intern at every step),
`Refine2/ExprOps/**`'s `strip_pis` / `strip_lams` / `mk_app_n` /
`instantiate1_lift_fast` / `inst_pis_at_lift` (statements only so far), and
`Refine2/Inductives/Spec.lean`'s own six `_unfold` equations.  **No clause of
`KnotRel` and no clause of `IndRel`**: this module calls nothing of
`arena::core` but `zero_level`, `lvl_eq`, `bvar_b` and
`reserved_basis_names`, none of which is knotted.
-/
import ConRon.Refine2.Inductives.Spec

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.ExprOps (WMemoRel LMemoRel)

/-! ## The one list helper

`nidx_vec_tail` has no twin of its own: the twin's recogniser destructures
`cvR.levelParams` with `elim :: relps`, and a `Vec` has no tail-sharing, so
the tail is copied.  The subject is a declaration's level parameters and never
a term, so both statements are plain list equations. -/

/-- `nidx_vec_tail_from` copies `ns` from the cursor on onto `out`. -/
theorem nidx_vec_tail_from_refines {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.inductives.struct_parts.nidx_vec_tail_from ns i out = ok o) :
    absNIdxL o = absNIdxL out ++ absNIdxLFrom ns i := by
  simp only [absNIdxL, absNIdxLFrom]
  refine vec_cursor_copy ns absNIdx absNIdx
    (arena.inductives.struct_parts.nidx_vec_tail_from ns) ?_ ?_ i out o hrun
  · intro i out o hn h
    rw [arena.inductives.struct_parts.nidx_vec_tail_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ns by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < ns.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.struct_parts.nidx_vec_tail_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ns by scalar_tac)] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnx : n1 = x := by
      have h1 := vec_index_some hn1; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hnx
    exact ⟨i2, n2, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_nidx _ _ hn2], h⟩

open Lockstep in
/-- `nidx_vec_tail_from_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem nidx_vec_tail_from_twin0
    {ns : alloc.vec.Vec arena.handle.NIdx} :
    LSP (arena.inductives.struct_parts.nidx_vec_tail_from ns 0#usize (alloc.vec.Vec.new arena.handle.NIdx)) (fun o => TwinEq (absNIdxL ns) (absNIdxL o)) := by
  intro o h
  have h' := (nidx_vec_tail_from_refines h).symm
  simpa [Lockstep.TwinEq, absNIdxLFrom, absNIdxL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem nidx_vec_tail_from_twin
    {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.NIdx} :
    LSP (arena.inductives.struct_parts.nidx_vec_tail_from ns i out) (fun o => TwinEq (absNIdxL out ++ absNIdxLFrom ns i) (absNIdxL o)) :=
  fun o h => (nidx_vec_tail_from_refines h).symm

/-- `nidx_vec_tail` is `List.tail` on the abstraction — the twin's
`elim :: relps` pattern. -/
theorem nidx_vec_tail_refines {ns : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.inductives.struct_parts.nidx_vec_tail ns = ok o) :
    absNIdxL o = (absNIdxL ns).tail := by
  rw [arena.inductives.struct_parts.nidx_vec_tail] at hrun
  rw [nidx_vec_tail_from_refines hrun]
  have h1 : ((1#usize : Std.Usize)).val = 1 := by scalar_tac
  simp [absNIdxL, absNIdxLFrom, alloc.vec.Vec.new, h1, List.drop_one]

open Lockstep in
@[lockstep] theorem nidx_vec_tail_twin
    {ns : alloc.vec.Vec arena.handle.NIdx} :
    LSP (arena.inductives.struct_parts.nidx_vec_tail ns) (fun o => TwinEq ((absNIdxL ns).tail) (absNIdxL o)) :=
  fun o h => (nidx_vec_tail_refines h).symm

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

/-- `param_levels` ⊑ `paramLevels`. -/
theorem param_levels_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.param_levels pers st lps = ok o) :
    Sim₀ absLsIdx pers lst o (paramLevels (absNIdxL lps)) := by
  rw [arena.inductives.struct_parts.param_levels] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st1⟩ := p
  have hgo := param_levels_go_refines hrel hinv hp
  rw [paramLevels_unfold]
  have h0 : absNIdxLFrom lps 0#usize = absNIdxL lps := by
    simp [absNIdxLFrom, absNIdxL]
  have hnew : absLIdxL (alloc.vec.Vec.new arena.handle.LIdx) = [] := rfl
  rw [h0, hnew] at hgo
  simp only [List.nil_append, bind_pure] at hgo
  cases r with
  | Err e =>
    have ho : (core.result.Result.Err e, st1) = o := Result.ok_injective hrun
    subst ho
    show AOut₀ _ _ (core.result.Result.Err e) st1 _
    rw [am_run_bind]
    exact AErrSim.bind (Sim₀.apply_err hgo) _
  | Ok us =>
    obtain ⟨lst1, hrun1, hrel1, hinv1⟩ := Sim₀.apply hgo
    have hls := intern_ls_node_run₀ hrel1 hinv1 us hrun
    show AOut₀ _ _ o.1 o.2 _
    rw [am_run_bind, hrun1]
    exact hls

open Lockstep in
@[lockstep] theorem param_levels_ls
    {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLsIdx a) (arena.inductives.struct_parts.param_levels pers st lps) lst
                             (paramLevels (absNIdxL lps)) :=
  LS.ofSim₀ fun _ h => param_levels_refines hrel hinv h

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

/-- `bvars_desc` ⊑ `bvarsDesc` — `structPsAt 0 n`, named apart because
con-leche writes the two inline at different frames. -/
theorem bvars_desc_refines {pers st lst} {n : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.bvars_desc pers st n = ok o) :
    Sim₀ absEIdxL pers lst o (bvarsDesc (absU n)) := by
  rw [arena.inductives.struct_parts.bvars_desc] at hrun
  have h := struct_ps_at_refines hrel hinv hrun
  have h0 : ((0#u64 : Std.U64)).val = 0 := by scalar_tac
  rw [show absU (0#u64 : Std.U64) = 0 from h0] at h
  rwa [bvarsDesc]

open Lockstep in
@[lockstep] theorem bvars_desc_ls
    {pers st lst}
    {n : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.struct_parts.bvars_desc pers st n) lst
                             (bvarsDesc (absU n)) :=
  LS.ofSim₀ fun _ h => bvars_desc_refines hrel hinv h

/-- `struct_fam` ⊑ `structFam`. -/
theorem struct_fam_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p ofs : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_fam pers st t lps n_p ofs = ok o) :
    Sim₀ absEIdx pers lst o
      (structFam (absNIdx t) (absNIdxL lps) (absU n_p) (absU ofs)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_fam, structFam]
  lockstep

open Lockstep in
@[lockstep] theorem struct_fam_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p ofs : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.struct_parts.struct_fam pers st t lps n_p ofs) lst
      (structFam (absNIdx t) (absNIdxL lps) (absU n_p) (absU ofs)) :=
  LS.ofSim₀ fun _ h => struct_fam_refines hrel hinv h

/-- `struct_ctor_spine` ⊑ `structCtorSpine`. -/
theorem struct_ctor_spine_refines {pers st lst} {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_ctor_spine pers st c lps n_p n_f
      = ok o) :
    Sim₀ absEIdx pers lst o
      (structCtorSpine (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_ctor_spine_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.struct_parts.struct_ctor_spine pers st c lps n_p n_f) lst
      (structCtorSpine (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f)) :=
  LS.ofSim₀ fun _ h => struct_ctor_spine_refines hrel hinv h

/-- `struct_rule_body` ⊑ `structRuleBody`. -/
theorem struct_rule_body_refines {pers st lst} {n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_rule_body pers st n_f = ok o) :
    Sim₀ absEIdx pers lst o (structRuleBody (absU n_f)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_rule_body, structRuleBody]
  lockstep

open Lockstep in
@[lockstep] theorem struct_rule_body_ls
    {pers st lst}
    {n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.struct_parts.struct_rule_body pers st n_f) lst
                            (structRuleBody (absU n_f)) :=
  LS.ofSim₀ fun _ h => struct_rule_body_refines hrel hinv h

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

/-- `struct_ctor_spine_at` ⊑ `structCtorSpineAt`. -/
theorem struct_ctor_spine_at_refines {pers st lst} {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {ofs n_p n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_ctor_spine_at pers st c lps ofs
      n_p n_f = ok o) :
    Sim₀ absEIdx pers lst o
      (structCtorSpineAt (absNIdx c) (absNIdxL lps) (absU ofs) (absU n_p)
        (absU n_f)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_ctor_spine_at_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ofs n_p n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.struct_parts.struct_ctor_spine_at pers st c lps ofs n_p n_f) lst
      (structCtorSpineAt (absNIdx c) (absNIdxL lps) (absU ofs) (absU n_p)
        (absU n_f)) :=
  LS.ofSim₀ fun _ h => struct_ctor_spine_at_refines hrel hinv h

/-- `replace_pis_pw` ⊑ `replacePisPw`. -/
theorem replace_pis_pw_refines {pers st lst} {pw : kernel.prop_when.PropWhen}
    {k : Std.U64} {h b : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.replace_pis_pw pers st pw k h b = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (replacePisPw (ConRon.Refine.absPropWhen pw) (absU k) (absEIdx h)
        (absEIdx b)) := by
  sorry

open Lockstep in
@[lockstep] theorem replace_pis_pw_ls
    {pers st lst}
    {pw : kernel.prop_when.PropWhen}
    {k : Std.U64}
    {h b : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.struct_parts.replace_pis_pw pers st pw k h b) lst
      (replacePisPw (ConRon.Refine.absPropWhen pw) (absU k) (absEIdx h)
        (absEIdx b)) :=
  LS.ofSim₀ fun _ h => replace_pis_pw_refines hrel hinv h

/-- `pis_to_lams_pw` ⊑ `pisToLamsPw`. -/
theorem pis_to_lams_pw_refines {pers st lst} {pw : kernel.prop_when.PropWhen}
    {k : Std.U64} {h b : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.pis_to_lams_pw pers st pw k h b = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (pisToLamsPw (ConRon.Refine.absPropWhen pw) (absU k) (absEIdx h)
        (absEIdx b)) := by
  sorry

open Lockstep in
@[lockstep] theorem pis_to_lams_pw_ls
    {pers st lst}
    {pw : kernel.prop_when.PropWhen}
    {k : Std.U64}
    {h b : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.struct_parts.pis_to_lams_pw pers st pw k h b) lst
      (pisToLamsPw (ConRon.Refine.absPropWhen pw) (absU k) (absEIdx h)
        (absEIdx b)) :=
  LS.ofSim₀ fun _ h => pis_to_lams_pw_refines hrel hinv h

/-! ## The generated recursor at an indexed family -/

/-- `struct_fam_i` ⊑ `structFamI`. -/
theorem struct_fam_i_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx e ofs : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_fam_i pers st t lps n_p n_idx e ofs
      = ok o) :
    Sim₀ absEIdx pers lst o
      (structFamI (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU e)
        (absU ofs)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_fam_i_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx e ofs : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.struct_parts.struct_fam_i pers st t lps n_p n_idx e ofs) lst
      (structFamI (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU e)
        (absU ofs)) :=
  LS.ofSim₀ fun _ h => struct_fam_i_refines hrel hinv h

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
  sorry

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

/-- `struct_motive_ty_i` ⊑ `structMotiveTyI`. -/
theorem struct_motive_ty_i_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {l : arena.handle.LIdx} {itele : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_motive_ty_i pers st t lps n_p n_idx
      l itele = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structMotiveTyI (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absLIdx l) (absEIdx itele)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_motive_ty_i, structMotiveTyI]
  lockstep

open Lockstep in
@[lockstep] theorem struct_motive_ty_i_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {l : arena.handle.LIdx}
    {itele : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.struct_parts.struct_motive_ty_i pers st t lps n_p n_idx l itele) lst
      (structMotiveTyI (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absLIdx l) (absEIdx itele)) :=
  LS.ofSim₀ fun _ h => struct_motive_ty_i_refines hrel hinv h

/-! ## `structShape`, split four ways

`Refine2/Inductives/Spec.lean`'s four `…Spec` definitions are the subjects;
`structShape_unfold` is the equation that ties them back. -/

/-- `struct_shape_motive` ⊑ `structShape`'s `motiveOk` `let`. -/
theorem struct_shape_motive_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_shape_motive pers st t lps elim
      large n_p rbs = ok o) :
    Sim₀ id pers lst o
      (structShapeMotiveSpec (absNIdx t) (absNIdxL lps) (absNIdx elim) large
        (absU n_p) (absBinderL rbs)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_shape_motive_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {elim : arena.handle.NIdx}
    {large : Bool}
    {n_p : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.struct_shape_motive pers st t lps elim large n_p rbs) lst
      (structShapeMotiveSpec (absNIdx t) (absNIdxL lps) (absNIdx elim) large
        (absU n_p) (absBinderL rbs)) :=
  LS.ofSim₀ fun _ h => struct_shape_motive_refines hrel hinv h

/-- `struct_shape_minor` ⊑ `structShape`'s `minorOk` `let`. -/
theorem struct_shape_minor_refines {pers st lst} {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_shape_minor pers st c lps n_p n_f
      rbs = ok o) :
    Sim₀ id pers lst o
      (structShapeMinorSpec (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f)
        (absBinderL rbs)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_shape_minor_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.struct_shape_minor pers st c lps n_p n_f rbs) lst
      (structShapeMinorSpec (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f)
        (absBinderL rbs)) :=
  LS.ofSim₀ fun _ h => struct_shape_minor_refines hrel hinv h

/-- `struct_shape_major` ⊑ `structShape`'s last `match`. -/
theorem struct_shape_major_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_shape_major pers st t lps n_p rbs
      = ok o) :
    Sim₀ id pers lst o
      (structShapeMajorSpec (absNIdx t) (absNIdxL lps) (absU n_p)
        (absBinderL rbs)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_shape_major_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.struct_shape_major pers st t lps n_p rbs) lst
      (structShapeMajorSpec (absNIdx t) (absNIdxL lps) (absU n_p)
        (absBinderL rbs)) :=
  LS.ofSim₀ fun _ h => struct_shape_major_refines hrel hinv h

/-- `struct_shape_at` ⊑ `structShape`'s body past the three peels. -/
theorem struct_shape_at_refines {pers st lst} {t c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p n_f : Std.U64} {cbody : arena.handle.EIdx}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {rbody : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_shape_at pers st t c lps elim large
      n_p n_f cbody rbs rbody = ok o) :
    Sim₀ id pers lst o
      (structShapeAtSpec (absNIdx t) (absNIdx c) (absNIdxL lps) (absNIdx elim) large
        (absU n_p) (absU n_f) (absEIdx cbody) (absBinderL rbs) (absEIdx rbody)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_shape_at, structShapeAtSpec]
  lockstep

open Lockstep in
@[lockstep] theorem struct_shape_at_ls
    {pers st lst}
    {t c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {elim : arena.handle.NIdx}
    {large : Bool}
    {n_p n_f : Std.U64}
    {cbody : arena.handle.EIdx}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {rbody : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.struct_shape_at pers st t c lps elim large n_p n_f cbody rbs rbody) lst
      (structShapeAtSpec (absNIdx t) (absNIdx c) (absNIdxL lps) (absNIdx elim) large
        (absU n_p) (absU n_f) (absEIdx cbody) (absBinderL rbs) (absEIdx rbody)) :=
  LS.ofSim₀ fun _ h => struct_shape_at_refines hrel hinv h

/-- `struct_shape` ⊑ `structShape`. -/
theorem struct_shape_refines {pers st lst} {t c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p n_f : Std.U64} {tty cty rty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_shape pers st t c lps elim large
      n_p n_f tty cty rty = ok o) :
    Sim₀ id pers lst o
      (structShape (absNIdx t) (absNIdx c) (absNIdxL lps) (absNIdx elim) large
        (absU n_p) (absU n_f) (absEIdx tty) (absEIdx cty) (absEIdx rty)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_shape, structShape_unfold]
  lockstep

open Lockstep in
@[lockstep] theorem struct_shape_ls
    {pers st lst}
    {t c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {elim : arena.handle.NIdx}
    {large : Bool}
    {n_p n_f : Std.U64}
    {tty cty rty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.struct_shape pers st t c lps elim large n_p n_f tty cty rty) lst
      (structShape (absNIdx t) (absNIdx c) (absNIdxL lps) (absNIdx elim) large
        (absU n_p) (absU n_f) (absEIdx tty) (absEIdx cty) (absEIdx rty)) :=
  LS.ofSim₀ fun _ h => struct_shape_refines hrel hinv h

/-! ## `structPartsCore?`, split five ways -/

/-- `struct_parts_rhs_ok` ⊑ the recogniser's `rhsOk` `let`. -/
theorem struct_parts_rhs_ok_refines {pers st lst} {n_p n_f : Std.U64}
    {rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_rhs_ok pers st n_p n_f rhs
      = ok o) :
    Sim₀ id pers lst o
      (structPartsRhsOkSpec (absU n_p) (absU n_f) (absEIdx rhs)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_parts_rhs_ok, structPartsRhsOkSpec]
  lockstep

open Lockstep in
@[lockstep] theorem struct_parts_rhs_ok_ls
    {pers st lst}
    {n_p n_f : Std.U64}
    {rhs : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.struct_parts_rhs_ok pers st n_p n_f rhs) lst
      (structPartsRhsOkSpec (absU n_p) (absU n_f) (absEIdx rhs)) :=
  LS.ofSim₀ fun _ h => struct_parts_rhs_ok_refines hrel hinv h

/-- `struct_parts_core_small` ⊑ the recogniser's small-eliminator arm. -/
theorem struct_parts_core_small_refines {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal} {rule : arena.env.IRecRule}
    {s : arena.handle.LIdx} {is_prop : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_core_small pers st cv_t cv_c
      n_p n_f cv_r rule s is_prop = ok o) :
    Sim₀ (Option.map absStructParts) pers lst o
      (structPartsCoreSmallSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absIRecRule rule)
        (absLIdx s) is_prop) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_parts_core_small_ls
    {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal}
    {rule : arena.env.IRecRule}
    {s : arena.handle.LIdx}
    {is_prop : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absStructParts) a) (arena.inductives.struct_parts.struct_parts_core_small pers st cv_t cv_c n_p n_f cv_r rule s is_prop) lst
      (structPartsCoreSmallSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absIRecRule rule)
        (absLIdx s) is_prop) :=
  LS.ofSim₀ fun _ h => struct_parts_core_small_refines hrel hinv h

/-- `struct_parts_core_elim` ⊑ the recogniser's eliminator split. -/
theorem struct_parts_core_elim_refines {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal} {rule : arena.env.IRecRule}
    {s : arena.handle.LIdx} {is_prop : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_core_elim pers st cv_t cv_c
      n_p n_f cv_r rule s is_prop = ok o) :
    Sim₀ (Option.map absStructParts) pers lst o
      (structPartsCoreElimSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absIRecRule rule)
        (absLIdx s) is_prop) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_parts_core_elim_ls
    {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal}
    {rule : arena.env.IRecRule}
    {s : arena.handle.LIdx}
    {is_prop : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absStructParts) a) (arena.inductives.struct_parts.struct_parts_core_elim pers st cv_t cv_c n_p n_f cv_r rule s is_prop) lst
      (structPartsCoreElimSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absIRecRule rule)
        (absLIdx s) is_prop) :=
  LS.ofSim₀ fun _ h => struct_parts_core_elim_refines hrel hinv h

/-- `struct_parts_core_sort` ⊑ the recogniser's result-sort read. -/
theorem struct_parts_core_sort_refines {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal} {rule : arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_core_sort pers st cv_t cv_c
      n_p n_f cv_r rule = ok o) :
    Sim₀ (Option.map absStructParts) pers lst o
      (structPartsCoreSortSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absIRecRule rule)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.struct_parts.struct_parts_core_sort, structPartsCoreSortSpec]
  lockstep

open Lockstep in
@[lockstep] theorem struct_parts_core_sort_ls
    {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal}
    {rule : arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absStructParts) a) (arena.inductives.struct_parts.struct_parts_core_sort pers st cv_t cv_c n_p n_f cv_r rule) lst
      (structPartsCoreSortSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absIRecRule rule)) :=
  LS.ofSim₀ fun _ h => struct_parts_core_sort_refines hrel hinv h

/-- `struct_parts_core_at` ⊑ the recogniser's body past the block match. -/
theorem struct_parts_core_at_refines {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal} {m_i r_p : Std.U64}
    {rule : arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_core_at pers st cv_t cv_c n_p
      n_f cv_r m_i r_p rule = ok o) :
    Sim₀ (Option.map absStructParts) pers lst o
      (structPartsCoreAtSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absU m_i) (absU r_p)
        (absIRecRule rule)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_parts_core_at_ls
    {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal}
    {m_i r_p : Std.U64}
    {rule : arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absStructParts) a) (arena.inductives.struct_parts.struct_parts_core_at pers st cv_t cv_c n_p n_f cv_r m_i r_p rule) lst
      (structPartsCoreAtSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absU m_i) (absU r_p)
        (absIRecRule rule)) :=
  LS.ofSim₀ fun _ h => struct_parts_core_at_refines hrel hinv h

/-- `struct_parts_core` ⊑ `structPartsCore?`. -/
theorem struct_parts_core_refines {pers st lst}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_core pers st block = ok o) :
    Sim₀ (Option.map absStructParts) pers lst o
      (structPartsCore? (absICIL block)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_parts_core_ls
    {pers st lst}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absStructParts) a) (arena.inductives.struct_parts.struct_parts_core pers st block) lst
      (structPartsCore? (absICIL block)) :=
  LS.ofSim₀ fun _ h => struct_parts_core_refines hrel hinv h

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

/-- `struct_proj_resid_p` ⊑ `structProjResidP`. -/
theorem struct_proj_resid_p_refines {pers st lst} {t : arena.handle.NIdx}
    {n_p : Std.U64} {cty : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_resid_p pers st t n_p cty i
      = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structProjResidP (absNIdx t) (absU n_p) (absEIdx cty) (absU i)) := by
  sorry

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
  fun o h => (hlb_probe_refines hm h).symm

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

/-- `has_loose_bvar_b_node` ⊑ `hasLooseBVarBGo`'s arm dispatch. -/
theorem has_loose_bvar_b_node_refines {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {i fuel : Std.U64}
    {v : arena.store.ENodeView} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hm : WMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.has_loose_bvar_b_node pers st rm i fuel v
      = ok o) :
    SimRel₀ WOutRel pers lst o
      (hasLooseBVarBNodeSpec lm (absU i) (absU fuel) (absENodeView v)) := by
  sorry

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
  LS.ofSimRel₀ fun _ h => has_loose_bvar_b_node_refines hrel hinv hm h

/-- `has_loose_bvar_b_go` ⊑ `hasLooseBVarBGo`. -/
theorem has_loose_bvar_b_go_refines {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {i fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hm : WMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.has_loose_bvar_b_go pers st rm i fuel h
      = ok o) :
    SimRel₀ WOutRel pers lst o
      (hasLooseBVarBGo lm (absU i) (absU fuel) (absEIdx h)) := by
  sorry

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
  LS.ofSimRel₀ fun _ h => has_loose_bvar_b_go_refines hrel hinv hm h

/-- `has_loose_bvar_b_fast` ⊑ `hasLooseBVarBFast` — one memoised walk from the
empty memo. -/
theorem has_loose_bvar_b_fast_refines {pers st lst} {i : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.has_loose_bvar_b_fast pers st i e = ok o) :
    Sim₀ id pers lst o
      (hasLooseBVarBFast (absU i) (absEIdx e)) := by
  sorry

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

/-- `struct_used_later_go` ⊑ `structUsedLaterGo`. -/
theorem struct_used_later_go_refines {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {cty : arena.handle.EIdx}
    {n_p j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hm : WMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.struct_used_later_go pers st rm cty n_p j
      = ok o) :
    SimRel₀ WOutRel pers lst o
      (structUsedLaterGo lm (absEIdx cty) (absU n_p) (absU j)) := by
  sorry

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
      (structUsedLaterGo lm (absEIdx cty) (absU n_p) (absU j)) :=
  LS.ofSimRel₀ fun _ h => struct_used_later_go_refines hrel hinv hm h

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
        (← structUsedLaterList (absEIdx cty) (absU n_p) lm (absU n) (absU base)))) := by
  sorry

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
  fun o h => (used_get_d_refines h).symm

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
  fun o h => (sort_get_d_refines h).symm

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
          (absU i) (absU k)))) := by
  sorry

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
        fun r => absEIdxL out ++ r)) := by
  sorry

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
  sorry

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

/-- `mc_probe` ⊑ `memo[h]?`. -/
theorem mc_probe_refines {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {k : arena.handle.EIdx} {o}
    (hm : LMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.mc_probe rm k = ok o) :
    o = lm[absEIdx k]? := by
  rw [arena.inductives.struct_parts.mc_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hmr, hminv⟩ := hm
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hminv
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
@[lockstep] theorem mc_probe_twin
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {k : arena.handle.EIdx}
    (hm : LMemoRel rm lm) :
    LSP (arena.inductives.struct_parts.mc_probe rm k) (fun o => TwinEq (lm[absEIdx k]?) (o)) :=
  fun o h => (mc_probe_refines hm h).symm

/-- `mentions_const_node` ⊑ `mentionsConstGo`'s arm dispatch. -/
theorem mentions_const_node_refines {pers st lst} {t : arena.handle.NIdx}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {fuel : Std.U64} {v : arena.store.ENodeView} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hm : LMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.mentions_const_node pers st t rm fuel v
      = ok o) :
    SimRel₀ LOutRel pers lst o
      (mentionsConstNodeSpec (absNIdx t) lm (absU fuel)
        (absENodeView v)) := by
  sorry

open Lockstep in
@[lockstep] theorem mentions_const_node_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {fuel : Std.U64}
    {v : arena.store.ENodeView}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hm : LMemoRel rm lm) :
    LS pers LOutRel (arena.inductives.struct_parts.mentions_const_node pers st t rm fuel v) lst
      (mentionsConstNodeSpec (absNIdx t) lm (absU fuel)
        (absENodeView v)) :=
  LS.ofSimRel₀ fun _ h => mentions_const_node_refines hrel hinv hm h

/-- `mentions_const_go` ⊑ `mentionsConstGo`. -/
theorem mentions_const_go_refines {pers st lst} {t : arena.handle.NIdx}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hm : LMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.mentions_const_go pers st t rm fuel h
      = ok o) :
    SimRel₀ LOutRel pers lst o
      (mentionsConstGo (absNIdx t) lm (absU fuel) (absEIdx h)) := by
  sorry

open Lockstep in
@[lockstep] theorem mentions_const_go_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {fuel : Std.U64}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hm : LMemoRel rm lm) :
    LS pers LOutRel (arena.inductives.struct_parts.mentions_const_go pers st t rm fuel h) lst
      (mentionsConstGo (absNIdx t) lm (absU fuel) (absEIdx h)) :=
  LS.ofSimRel₀ fun _ h => mentions_const_go_refines hrel hinv hm h

/-- `mentions_const` ⊑ `mentionsConst` — one memoised walk from the empty
memo. -/
theorem mentions_const_refines {pers st lst} {t : arena.handle.NIdx}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.mentions_const pers st t e = ok o) :
    Sim₀ id pers lst o
      (mentionsConst (absNIdx t) (absEIdx e)) := by
  sorry

open Lockstep in
@[lockstep] theorem mentions_const_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.mentions_const pers st t e) lst
      (mentionsConst (absNIdx t) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => mentions_const_refines hrel hinv h

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
