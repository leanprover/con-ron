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
open ConRon.Refine2.ExprOps (WOut LOut WMemoRel LMemoRel)

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

/-- `nidx_vec_tail` is `List.tail` on the abstraction — the twin's
`elim :: relps` pattern. -/
theorem nidx_vec_tail_refines {ns : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.inductives.struct_parts.nidx_vec_tail ns = ok o) :
    absNIdxL o = (absNIdxL ns).tail := by
  rw [arena.inductives.struct_parts.nidx_vec_tail] at hrun
  rw [nidx_vec_tail_from_refines hrun]
  have h1 : ((1#usize : Std.Usize)).val = 1 := by scalar_tac
  simp [absNIdxL, absNIdxLFrom, alloc.vec.Vec.new, h1, List.drop_one]

/-! ## The level lists -/

/-- `param_levels_go` ⊑ `paramLevels`' inner `go`, from the cursor on. -/
theorem param_levels_go_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.param_levels_go pers st lps i out = ok o) :
    Sim absLIdxL (fun _ => True) pers lst o
      (do pure (absLIdxL out ++ (← paramLevelsGoSpec (absNIdxLFrom lps i)))) := by
  sorry

/-- `param_levels` ⊑ `paramLevels`. -/
theorem param_levels_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.param_levels pers st lps = ok o) :
    Sim absLsIdx (fun _ => True) pers lst o (paramLevels (absNIdxL lps)) := by
  sorry

/-! ## The families and the spines -/

/-- `struct_ps_at_from` ⊑ `structPsAt`'s inner `go` from the `k`-th parameter
on.  The port counts `k` up to `n_p` where the twin counts `n` down, which is
the `nP - k` in the statement. -/
theorem struct_ps_at_from_refines {pers st lst} {ofs n_p k : Std.U64}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hrun : arena.inductives.struct_parts.struct_ps_at_from pers st ofs n_p k out
      = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o
      (do pure (absEIdxL out ++
        (← structPsAtGoSpec (absU ofs) (absU n_p) (absU n_p - absU k) (absU k)))) := by
  refine sim_cursor_copy (fun k : Std.U64 => k.val) (absU n_p) absEIdx
    (fun s => s.store.shared_on = true → s.store.scratch_on = true)
    (fun m => Arena.internBVarE (absU ofs + absU n_p - 1 - m))
    (fun m => structPsAtGoSpec (absU ofs) (absU n_p) (absU n_p - m) m)
    (fun s k out => arena.inductives.struct_parts.struct_ps_at_from pers s ofs n_p k out)
    ?_ ?_ ?_ ?_
    k out st lst o hrel hinv hfrozen hrun
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
  · intro st lst i out o hi hrel hinv hfr h
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
    have hf := intern_e_bvar_flags hrel hinv hfr hp
    refine ⟨r, st1, by rw [← hval]; exact intern_e_bvar_run hrel hinv hfr a3 hp,
      ?_, ?_⟩
    · intro u hu
      subst hu
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨i3, out1, ?_, ConRon.Refine.vec_push_val hout1, ?_, h⟩
      · have := ConRon.Refine.Nat.uadd_val hi3
        simpa using this
      · intro hs
        rw [hf.2]
        exact hfr (by rw [← hf.1]; exact hs)
    · intro e he
      subst he
      exact (Result.ok_injective h).symm

/-- `struct_ps_at` ⊑ `structPsAt`. -/
theorem struct_ps_at_refines {pers st lst} {ofs n_p : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hrun : arena.inductives.struct_parts.struct_ps_at pers st ofs n_p = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o (structPsAt (absU ofs) (absU n_p)) := by
  rw [arena.inductives.struct_parts.struct_ps_at] at hrun
  have h := struct_ps_at_from_refines hrel hinv hfrozen hrun
  rw [structPsAt_unfold]
  have h0 : ((0#u64 : Std.U64)).val = 0 := by scalar_tac
  simpa [absEIdxL, alloc.vec.Vec.new, h0, absU] using h

/-- `bvars_desc` ⊑ `bvarsDesc` — `structPsAt 0 n`, named apart because
con-leche writes the two inline at different frames. -/
theorem bvars_desc_refines {pers st lst} {n : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hrun : arena.inductives.struct_parts.bvars_desc pers st n = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o (bvarsDesc (absU n)) := by
  rw [arena.inductives.struct_parts.bvars_desc] at hrun
  have h := struct_ps_at_refines hrel hinv hfrozen hrun
  have h0 : ((0#u64 : Std.U64)).val = 0 := by scalar_tac
  rw [show absU (0#u64 : Std.U64) = 0 from h0] at h
  rwa [bvarsDesc]

/-- `struct_fam` ⊑ `structFam`. -/
theorem struct_fam_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p ofs : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_fam pers st t lps n_p ofs = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (structFam (absNIdx t) (absNIdxL lps) (absU n_p) (absU ofs)) := by
  sorry

/-- `struct_ctor_spine` ⊑ `structCtorSpine`. -/
theorem struct_ctor_spine_refines {pers st lst} {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_ctor_spine pers st c lps n_p n_f
      = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (structCtorSpine (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f)) := by
  sorry

/-- `struct_rule_body` ⊑ `structRuleBody`. -/
theorem struct_rule_body_refines {pers st lst} {n_f : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_rule_body pers st n_f = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (structRuleBody (absU n_f)) := by
  sorry

/-- `struct_elim_level` ⊑ `structElimLevel`. -/
theorem struct_elim_level_refines {pers st lst} {elim : arena.handle.NIdx}
    {large : Bool} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_elim_level pers st elim large
      = ok o) :
    Sim absLIdx (fun _ => True) pers lst o
      (structElimLevel (absNIdx elim) large) := by
  sorry

/-- `struct_ctor_spine_at` ⊑ `structCtorSpineAt`. -/
theorem struct_ctor_spine_at_refines {pers st lst} {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {ofs n_p n_f : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_ctor_spine_at pers st c lps ofs
      n_p n_f = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (structCtorSpineAt (absNIdx c) (absNIdxL lps) (absU ofs) (absU n_p)
        (absU n_f)) := by
  sorry

/-- `replace_pis_pw` ⊑ `replacePisPw`. -/
theorem replace_pis_pw_refines {pers st lst} {pw : kernel.prop_when.PropWhen}
    {k : Std.U64} {h b : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.replace_pis_pw pers st pw k h b = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (replacePisPw (ConRon.Refine.absPropWhen pw) (absU k) (absEIdx h)
        (absEIdx b)) := by
  sorry

/-- `pis_to_lams_pw` ⊑ `pisToLamsPw`. -/
theorem pis_to_lams_pw_refines {pers st lst} {pw : kernel.prop_when.PropWhen}
    {k : Std.U64} {h b : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.pis_to_lams_pw pers st pw k h b = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (pisToLamsPw (ConRon.Refine.absPropWhen pw) (absU k) (absEIdx h)
        (absEIdx b)) := by
  sorry

/-! ## The generated recursor at an indexed family -/

/-- `struct_fam_i` ⊑ `structFamI`. -/
theorem struct_fam_i_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx e ofs : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_fam_i pers st t lps n_p n_idx e ofs
      = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (structFamI (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU e)
        (absU ofs)) := by
  sorry

/-- `struct_ctor_resid_ok` ⊑ `structCtorResidOk`. -/
theorem struct_ctor_resid_ok_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p ofs n_idx : Std.U64}
    {cbody : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_ctor_resid_ok pers st t lps n_p ofs
      n_idx cbody = ok o) :
    Sim id (fun _ => True) pers lst o
      (structCtorResidOk (absNIdx t) (absNIdxL lps) (absU n_p) (absU ofs)
        (absU n_idx) (absEIdx cbody)) := by
  sorry

/-- `struct_motive_ty_i` ⊑ `structMotiveTyI`. -/
theorem struct_motive_ty_i_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {l : arena.handle.LIdx} {itele : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_motive_ty_i pers st t lps n_p n_idx
      l itele = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structMotiveTyI (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absLIdx l) (absEIdx itele)) := by
  sorry

/-! ## `structShape`, split four ways

`Refine2/Inductives/Spec.lean`'s four `…Spec` definitions are the subjects;
`structShape_unfold` is the equation that ties them back. -/

/-- `struct_shape_motive` ⊑ `structShape`'s `motiveOk` `let`. -/
theorem struct_shape_motive_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_shape_motive pers st t lps elim
      large n_p rbs = ok o) :
    Sim id (fun _ => True) pers lst o
      (structShapeMotiveSpec (absNIdx t) (absNIdxL lps) (absNIdx elim) large
        (absU n_p) (absBinderL rbs)) := by
  sorry

/-- `struct_shape_minor` ⊑ `structShape`'s `minorOk` `let`. -/
theorem struct_shape_minor_refines {pers st lst} {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_shape_minor pers st c lps n_p n_f
      rbs = ok o) :
    Sim id (fun _ => True) pers lst o
      (structShapeMinorSpec (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f)
        (absBinderL rbs)) := by
  sorry

/-- `struct_shape_major` ⊑ `structShape`'s last `match`. -/
theorem struct_shape_major_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_shape_major pers st t lps n_p rbs
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (structShapeMajorSpec (absNIdx t) (absNIdxL lps) (absU n_p)
        (absBinderL rbs)) := by
  sorry

/-- `struct_shape_at` ⊑ `structShape`'s body past the three peels. -/
theorem struct_shape_at_refines {pers st lst} {t c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p n_f : Std.U64} {cbody : arena.handle.EIdx}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {rbody : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_shape_at pers st t c lps elim large
      n_p n_f cbody rbs rbody = ok o) :
    Sim id (fun _ => True) pers lst o
      (structShapeAtSpec (absNIdx t) (absNIdx c) (absNIdxL lps) (absNIdx elim) large
        (absU n_p) (absU n_f) (absEIdx cbody) (absBinderL rbs) (absEIdx rbody)) := by
  sorry

/-- `struct_shape` ⊑ `structShape`. -/
theorem struct_shape_refines {pers st lst} {t c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p n_f : Std.U64} {tty cty rty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_shape pers st t c lps elim large
      n_p n_f tty cty rty = ok o) :
    Sim id (fun _ => True) pers lst o
      (structShape (absNIdx t) (absNIdx c) (absNIdxL lps) (absNIdx elim) large
        (absU n_p) (absU n_f) (absEIdx tty) (absEIdx cty) (absEIdx rty)) := by
  sorry

/-! ## `structPartsCore?`, split five ways -/

/-- `struct_parts_rhs_ok` ⊑ the recogniser's `rhsOk` `let`. -/
theorem struct_parts_rhs_ok_refines {pers st lst} {n_p n_f : Std.U64}
    {rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_rhs_ok pers st n_p n_f rhs
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (structPartsRhsOkSpec (absU n_p) (absU n_f) (absEIdx rhs)) := by
  sorry

/-- `struct_parts_core_small` ⊑ the recogniser's small-eliminator arm. -/
theorem struct_parts_core_small_refines {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal} {rule : arena.env.IRecRule}
    {s : arena.handle.LIdx} {is_prop : Bool} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_core_small pers st cv_t cv_c
      n_p n_f cv_r rule s is_prop = ok o) :
    Sim (Option.map absStructParts) (fun _ => True) pers lst o
      (structPartsCoreSmallSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absIRecRule rule)
        (absLIdx s) is_prop) := by
  sorry

/-- `struct_parts_core_elim` ⊑ the recogniser's eliminator split. -/
theorem struct_parts_core_elim_refines {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal} {rule : arena.env.IRecRule}
    {s : arena.handle.LIdx} {is_prop : Bool} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_core_elim pers st cv_t cv_c
      n_p n_f cv_r rule s is_prop = ok o) :
    Sim (Option.map absStructParts) (fun _ => True) pers lst o
      (structPartsCoreElimSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absIRecRule rule)
        (absLIdx s) is_prop) := by
  sorry

/-- `struct_parts_core_sort` ⊑ the recogniser's result-sort read. -/
theorem struct_parts_core_sort_refines {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal} {rule : arena.env.IRecRule} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_core_sort pers st cv_t cv_c
      n_p n_f cv_r rule = ok o) :
    Sim (Option.map absStructParts) (fun _ => True) pers lst o
      (structPartsCoreSortSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absIRecRule rule)) := by
  sorry

/-- `struct_parts_core_at` ⊑ the recogniser's body past the block match. -/
theorem struct_parts_core_at_refines {pers st lst}
    {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {cv_r : arena.env.IConstantVal} {m_i r_p : Std.U64}
    {rule : arena.env.IRecRule} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_core_at pers st cv_t cv_c n_p
      n_f cv_r m_i r_p rule = ok o) :
    Sim (Option.map absStructParts) (fun _ => True) pers lst o
      (structPartsCoreAtSpec (absIConstantVal cv_t) (absIConstantVal cv_c)
        (absU n_p) (absU n_f) (absIConstantVal cv_r) (absU m_i) (absU r_p)
        (absIRecRule rule)) := by
  sorry

/-- `struct_parts_core` ⊑ `structPartsCore?`. -/
theorem struct_parts_core_refines {pers st lst}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_parts_core pers st block = ok o) :
    Sim (Option.map absStructParts) (fun _ => True) pers lst o
      (structPartsCore? (absICIL block)) := by
  sorry

/-! ## The projection bodies -/

/-- `struct_proj_ps` ⊑ `structProjPs`. -/
theorem struct_proj_ps_refines {pers st lst} {n_p : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_ps pers st n_p = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o (structProjPs (absU n_p)) := by
  sorry

/-- `struct_proj_arg_p` ⊑ `structProjArgP`. -/
theorem struct_proj_arg_p_refines {pers st lst} {t : arena.handle.NIdx}
    {j : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_arg_p pers st t j = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (structProjArgP (absNIdx t) (absU j)) := by
  sorry

/-- `struct_proj_resid_p` ⊑ `structProjResidP`. -/
theorem struct_proj_resid_p_refines {pers st lst} {t : arena.handle.NIdx}
    {n_p : Std.U64} {cty : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_resid_p pers st t n_p cty i
      = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structProjResidP (absNIdx t) (absU n_p) (absEIdx cty) (absU i)) := by
  sorry

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
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hm : WMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.has_loose_bvar_b_node pers st rm i fuel v
      = ok o) :
    WOut pers lst o.1 o.2
      ((hasLooseBVarBNodeSpec lm (absU i) (absU fuel) (absENodeView v)).run lst) := by
  sorry

/-- `has_loose_bvar_b_go` ⊑ `hasLooseBVarBGo`. -/
theorem has_loose_bvar_b_go_refines {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {i fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hm : WMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.has_loose_bvar_b_go pers st rm i fuel h
      = ok o) :
    WOut pers lst o.1 o.2
      ((hasLooseBVarBGo lm (absU i) (absU fuel) (absEIdx h)).run lst) := by
  sorry

/-- `has_loose_bvar_b_fast` ⊑ `hasLooseBVarBFast` — one memoised walk from the
empty memo. -/
theorem has_loose_bvar_b_fast_refines {pers st lst} {i : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.has_loose_bvar_b_fast pers st i e = ok o) :
    Sim id (fun _ => True) pers lst o
      (hasLooseBVarBFast (absU i) (absEIdx e)) := by
  sorry

/-! ## `structUsedLater` and the guard table -/

/-- `struct_used_later` ⊑ `structUsedLater`. -/
theorem struct_used_later_refines {pers st lst} {cty : arena.handle.EIdx}
    {n_p j : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_used_later pers st cty n_p j
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (structUsedLater (absEIdx cty) (absU n_p) (absU j)) := by
  sorry

/-- `struct_used_later_go` ⊑ `structUsedLaterGo`. -/
theorem struct_used_later_go_refines {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {cty : arena.handle.EIdx}
    {n_p j : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hm : WMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.struct_used_later_go pers st rm cty n_p j
      = ok o) :
    WOut pers lst o.1 o.2
      ((structUsedLaterGo lm (absEIdx cty) (absU n_p) (absU j)).run lst) := by
  sorry

/-- `struct_used_later_list` ⊑ `structUsedLaterList`, with the accumulated
answers in front. -/
theorem struct_used_later_list_refines {pers st lst}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {cty : arena.handle.EIdx}
    {n_p n base : Std.U64} {out : alloc.vec.Vec Bool} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hm : WMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.struct_used_later_list pers st rm cty n_p n
      base out = ok o) :
    Sim absBoolL (fun _ => True) pers lst o
      (do pure (absBoolL out ++
        (← structUsedLaterList (absEIdx cty) (absU n_p) lm (absU n) (absU base)))) := by
  sorry

/-- `used_get_d` ⊑ `used.getD j false`. -/
theorem used_get_d_refines {used : alloc.vec.Vec Bool} {j : Std.U64} {o}
    (hrun : arena.inductives.struct_parts.used_get_d used j = ok o) :
    o = (absBoolL used).getD (absU j) false := by
  sorry

/-- `sort_get_d` ⊑ `sorts.getD j z`. -/
theorem sort_get_d_refines {sorts : alloc.vec.Vec arena.handle.LIdx} {j : Std.U64}
    {z : arena.handle.LIdx} {o}
    (hrun : arena.inductives.struct_parts.sort_get_d sorts j z = ok o) :
    absLIdx o = (absLIdxL sorts).getD (absU j) (absLIdx z) := by
  sorry

/-- `struct_proj_guards_col` ⊑ `structProjGuards`' `col`. -/
theorem struct_proj_guards_col_refines {pers st lst} {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec arena.handle.LIdx} {z : arena.handle.LIdx}
    {j k : Std.U64} {acc : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_guards_col pers st used sorts z
      j k acc = ok o) :
    Sim absLIdx (fun _ => True) pers lst o
      (structProjGuardsColSpec (absBoolL used) (absLIdxL sorts) (absLIdx z)
        (absU j) (absU k) (absLIdx acc)) := by
  sorry

/-- `struct_proj_guards_row` ⊑ `structProjGuards`' `row`, with the accumulated
guards in front. -/
theorem struct_proj_guards_row_refines {pers st lst} {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec arena.handle.LIdx} {z : arena.handle.LIdx}
    {i k : Std.U64} {out : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_guards_row pers st used sorts z
      i k out = ok o) :
    Sim absLIdxL (fun _ => True) pers lst o
      (do pure (absLIdxL out ++
        (← structProjGuardsRowSpec (absBoolL used) (absLIdxL sorts) (absLIdx z)
          (absU i) (absU k)))) := by
  sorry

/-- `struct_proj_guards` ⊑ `structProjGuards`. -/
theorem struct_proj_guards_refines {pers st lst} {cty : arena.handle.EIdx}
    {n_p n_f : Std.U64} {sorts : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_guards pers st cty n_p n_f
      sorts = ok o) :
    Sim absLIdxL (fun _ => True) pers lst o
      (structProjGuards (absEIdx cty) (absU n_p) (absU n_f) (absLIdxL sorts)) := by
  sorry

/-- `struct_proj_bodies_go` ⊑ `structProjBodiesGo`, with the accumulated
domains in front. -/
theorem struct_proj_bodies_go_refines {pers st lst} {t : arena.handle.NIdx}
    {k i : Std.U64} {h : arena.handle.EIdx}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_bodies_go pers st t k i h out
      = ok o) :
    Sim (Option.map absEIdxL) (fun _ => True) pers lst o
      (do pure ((← structProjBodiesGo (absNIdx t) (absU k) (absU i) (absEIdx h)).map
        fun r => absEIdxL out ++ r)) := by
  sorry

/-- `struct_proj_bodies` ⊑ `structProjBodies` — the twin's answer is an
`Array` (the table stores it so) and the port's a `Vec`, which is task
#97-P5-0's finding 5 at this module. -/
theorem struct_proj_bodies_refines {pers st lst} {t : arena.handle.NIdx}
    {n_p n_f : Std.U64} {cty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.struct_proj_bodies pers st t n_p n_f cty
      = ok o) :
    Sim (fun r => (Option.map absEIdxL r).map List.toArray) (fun _ => True) pers lst o
      (structProjBodies (absNIdx t) (absU n_p) (absU n_f) (absEIdx cty)) := by
  sorry

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

/-- `mentions_const_node` ⊑ `mentionsConstGo`'s arm dispatch. -/
theorem mentions_const_node_refines {pers st lst} {t : arena.handle.NIdx}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {fuel : Std.U64} {v : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hm : LMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.mentions_const_node pers st t rm fuel v
      = ok o) :
    LOut pers lst o.1 o.2
      ((mentionsConstNodeSpec (absNIdx t) lm (absU fuel)
        (absENodeView v)).run lst) := by
  sorry

/-- `mentions_const_go` ⊑ `mentionsConstGo`. -/
theorem mentions_const_go_refines {pers st lst} {t : arena.handle.NIdx}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hm : LMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.mentions_const_go pers st t rm fuel h
      = ok o) :
    LOut pers lst o.1 o.2
      ((mentionsConstGo (absNIdx t) lm (absU fuel) (absEIdx h)).run lst) := by
  sorry

/-- `mentions_const` ⊑ `mentionsConst` — one memoised walk from the empty
memo. -/
theorem mentions_const_refines {pers st lst} {t : arena.handle.NIdx}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.mentions_const pers st t e = ok o) :
    Sim id (fun _ => True) pers lst o
      (mentionsConst (absNIdx t) (absEIdx e)) := by
  sorry

end ConRon.Refine2
