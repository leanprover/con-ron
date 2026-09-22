/-
# `ConRon.Refine2.Inductives.NativeParts` — Theorem 2 for `arena::inductives::native_parts`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/native_parts.rs` against
`proof/ConRon/Arena/Inductives/NativeParts.lean`: the field kinds and
official's positivity classification, the generated recursor with its
inductive-hypothesis binders, the comparison of the stream's rules against the
generated ones, and the recogniser.

**Seventy `pub fn`s against twenty-nine twin `def`s** — the second densest
split of the crate after `decl_check`'s (task #97-P5-Checker's finding 11), and
for the same reason: `structRecTyR`, `structRecRhsR`, `structMinorTyR`,
`structIhPis` and `nativeShape?` are hundred-line `do` blocks whose `let`-bound
handles outlive a `match` arm.  `Refine2/Inductives/Spec.lean` carries a
transcription of every fragment.

## Three findings about this module

**Finding 16 — `structMinorsPisR` and `structMinorsLamsR` are ONE Rust
function, and the parameter is a node constructor.**  The two twins differ in
one node (`.forallE` against `.lam`), and task #97-P4d-2's **extraction rule 7**
forbids the port an `if` whose two arms MOVE a node's fields; so
`struct_minors_pis_r` takes `is_lam : bool` and `intern_binder` builds AND
interns inside each branch.  `structMinorsRSpec` is the two twins as one
recursion at that flag, and `struct_minors_lams_r` is it at `false`… **at
`true`**: the port's `struct_minors_lams_r` delegates with `is_lam := true`,
and the twin whose `λ` it is is `structMinorsLamsR`.  The statement pins the
delegation, not the flag's spelling.

**Finding 17 — `nativeCounts?` takes the CONSTRUCTOR LIST in the twin and its
LENGTH in the port.**  `cs.length + 1` is the only thing the twin reads it for,
so the port narrows the argument to `n_ctors : u64` — a narrowing, in P4b's
standing sense, and the statement supplies `(absCtors3L cs).length`.

**Finding 18 — `pi_binders` is the module's one `SimRE`.**  It takes
`&AState` and returns `Result<…, CheckError>` with no state in the return:
the telescope walk reads the store and appends nothing, and its only failure
is the fuel.  `Refine2/Checker/Shape.lean`'s fourth shape is what states it.

## What these lemmas wait on

`Refine2/Specs.lean`'s `intern_*` family, `Refine2/ExprOps/**`'s
`strip_pis` / `strip_lams` / `mk_app_n` / `lift_loose_bvars_fast` /
`reset_meta_fast` / `get_app_args`, `Refine2/Inductives/StructParts.lean`'s
generators, and `Refine2/Inductives/Spec.lean`'s four `_unfold` equations.
**No clause of `KnotRel`**: the classification walks the store and never the
knot.
-/
import ConRon.Refine2.Inductives.SumInstallF

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## `RecFieldKind` and its containers

The twin's `RecFieldKind` is twinned rather than imported
(`Arena/Inductives/NativeParts.lean`'s module note); it carries no term, so
its copy is the identity and its `==` is `DecidableEq`. -/

/-- `rec_field_kind_dup` is the identity on the abstraction. -/
theorem rec_field_kind_dup_refines
    {k : arena.inductives.native_parts.RecFieldKind} {o}
    (hrun : arena.inductives.native_parts.rec_field_kind_dup k = ok o) :
    absRecFieldKind o = absRecFieldKind k := by
  rw [arena.inductives.native_parts.rec_field_kind_dup.eq_def] at hrun
  cases k <;> (have h2 := Result.ok_injective hrun; subst h2; rfl)

/-- `rec_field_kind_beq` ⊑ `RecFieldKind`'s `DecidableEq` — §3.4 forbids
`#[derive]`, so the port spells the five-by-five table out. -/
theorem rec_field_kind_beq_refines
    {a b : arena.inductives.native_parts.RecFieldKind} {o}
    (hrun : arena.inductives.native_parts.rec_field_kind_beq a b = ok o) :
    o = (absRecFieldKind a == absRecFieldKind b) := by
  rw [arena.inductives.native_parts.rec_field_kind_beq.eq_def] at hrun
  cases a <;> cases b <;> (have h2 := Result.ok_injective hrun; subst h2; rfl)

/-- `kinds_copy` is the identity on the abstraction from the cursor on. -/
theorem kinds_copy_refines
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {o}
    (hrun : arena.inductives.native_parts.kinds_copy ks i out = ok o) :
    absKindL o = absKindL out ++ absKindLFrom ks i := by
  have aux : ∀ (n : Nat) (i : Std.Usize)
      (out o : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind),
      ks.val.length ≤ i.val + n →
      arena.inductives.native_parts.kinds_copy ks i out = ok o →
      absKindL o = absKindL out ++ absKindLFrom ks i := by
    intro n
    induction n with
    | zero =>
      intro i out o hn h
      rw [arena.inductives.native_parts.kinds_copy.eq_def] at h
      rw [if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
      subst h
      simp [absKindL, absKindLFrom,
        List.drop_eq_nil_of_le (by omega : ks.val.length ≤ i.val)]
    | succ n ih =>
      intro i out o hn h
      rw [arena.inductives.native_parts.kinds_copy.eq_def] at h
      by_cases hc : i.val ≥ ks.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
        subst h
        simp [absKindL, absKindLFrom,
          List.drop_eq_nil_of_le (by omega : ks.val.length ≤ i.val)]
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ks by scalar_tac)] at h
        obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hb, hkv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hk)
        have hkd : absRecFieldKind k1 = absRecFieldKind k := rec_field_kind_dup_refines hk1
        have hpv : out1.val = out.val ++ [k1] := ConRon.Refine.vec_push_val hout1
        have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
        have hih := ih i2 out1 o (by omega) h
        rw [hih]
        simp only [absKindL, absKindLFrom, hpv, hi2v, List.map_append,
          List.append_assoc, List.map_cons, List.map_nil, hkd]
        congr 1
        rw [List.drop_eq_getElem_cons hb, hkv]
        simp
  exact aux ks.val.length i out o (by omega) hrun

/-- `kindss_copy` is the identity on the abstraction from the cursor on. -/
theorem kindss_copy_refines
    {kss : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o} (hrun : arena.inductives.native_parts.kindss_copy kss i out = ok o) :
    absKindLL o = absKindLL out ++ absKindLLFrom kss i := by
  sorry

/-- `kind_get_d` ⊑ `ks.getD i .ordinary`. -/
theorem kind_get_d_refines
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {i : Std.U64}
    {o} (hrun : arena.inductives.native_parts.kind_get_d ks i = ok o) :
    absRecFieldKind o = (absKindL ks).getD (absU i) .ordinary := by
  sorry

/-! ## The field kinds -/

/-- `rec_fam_ok` ⊑ `recFamOk` — is `e` the family at the parameter variables
followed by `nIdx` index expressions none of which mentions the block?
Official's `is_valid_ind_app` exactly. -/
theorem rec_fam_ok_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx ofs : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_fam_ok pers st t lps n_p n_idx ofs e
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (recFamOk (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU ofs)
        (absEIdx e)) := by
  sorry

/-- `idx_free_of` ⊑ `recFamOk`'s closing `allM`, from the cursor on. -/
theorem idx_free_of_refines {pers st lst} {t : arena.handle.NIdx}
    {idx : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.idx_free_of pers st t idx i = ok o) :
    Sim id (fun _ => True) pers lst o
      (idxFreeOfSpec (absNIdx t) (absEIdxLFrom idx i)) := by
  sorry

/-- `rec_positivity_at` ⊑ `recPositivity`'s `_` arm. -/
theorem rec_positivity_at_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx ofs : Std.U64}
    {h : arena.handle.EIdx} {k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_positivity_at pers st t lps n_p n_idx
      ofs h k = ok o) :
    Sim absRecFieldKind (fun _ => True) pers lst o
      (recPositivityAtSpec (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absU ofs) (absEIdx h) (absU k)) := by
  sorry

/-- `rec_positivity` ⊑ `recPositivity` — official `check_positivity`'s
telescope walk on a field domain that mentions the block, syntactically. -/
theorem rec_positivity_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx ofs fuel : Std.U64}
    {h : arena.handle.EIdx} {k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_positivity pers st t lps n_p n_idx ofs
      fuel h k = ok o) :
    Sim absRecFieldKind (fun _ => True) pers lst o
      (recPositivity (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU ofs)
        (absU fuel) (absEIdx h) (absU k)) := by
  sorry

/-- `rec_field_kind` ⊑ `recFieldKind`. -/
theorem rec_field_kind_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx ofs : Std.U64}
    {dom : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_field_kind pers st t lps n_p n_idx ofs
      dom = ok o) :
    Sim absRecFieldKind (fun _ => True) pers lst o
      (recFieldKind (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU ofs)
        (absEIdx dom)) := by
  sorry

/-- `rec_ctor_kind_at` ⊑ `recCtorKinds`' per-field post-step. -/
theorem rec_ctor_kind_at_refines {pers st lst} {cty : arena.handle.EIdx}
    {n_p i : Std.U64} {k : arena.inductives.native_parts.RecFieldKind} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_ctor_kind_at pers st cty n_p i k
      = ok o) :
    Sim absRecFieldKind (fun _ => True) pers lst o
      (recCtorKindAtSpec (absEIdx cty) (absU n_p) (absU i)
        (absRecFieldKind k)) := by
  sorry

/-- `rec_ctor_kinds_from` ⊑ `recCtorKinds`' per-field walk from field `i` on,
with the accumulated kinds in front. -/
theorem rec_ctor_kinds_from_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {cty : arena.handle.EIdx} {n_f : Std.U64}
    {cbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {i : Std.U64}
    {out : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_ctor_kinds_from pers st t lps n_p n_idx
      cty n_f cbs i out = ok o) :
    Sim absKindL (fun _ => True) pers lst o
      (do pure (absKindL out ++
        (← recCtorKindsFromSpec (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
          (absEIdx cty) (absBinderL cbs) (absU n_f - absU i) (absU i)))) := by
  sorry

/-- `all_negative` ⊑ `ks.map fun _ => .negative` from the cursor on. -/
theorem all_negative_refines {n i : Std.U64}
    {out : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {o}
    (hrun : arena.inductives.native_parts.all_negative n i out = ok o) :
    absKindL o = absKindL out ++ List.replicate (absU n - absU i) .negative := by
  sorry

/-- `rec_ctor_kinds` ⊑ `recCtorKinds` — the kinds of one constructor's fields,
off its (raw or annotated) type. -/
theorem rec_ctor_kinds_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {c : arena.env.IConstantVal × Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_ctor_kinds pers st t lps n_p n_idx c
      = ok o) :
    Sim (Option.map absKindL) (fun _ => True) pers lst o
      (recCtorKinds (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absIConstantVal c.1, absU c.2)) := by
  sorry

/-! ## The telescope readers -/

/-- `pi_binders` ⊑ `piBinders`, with the accumulated binders in front.
**Finding 18's `SimRE`**: the walk reads the store, appends nothing, and its
only failure is the fuel. -/
theorem pi_binders_refines {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx}
    {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.pi_binders pers st fuel h out = ok o) :
    SimRE (fun r => (absBinderL r.1, absEIdx r.2)) lst o
      (do
        let q ← piBinders (absU fuel) (absEIdx h)
        pure (absBinderL out ++ q.1, q.2)) := by
  sorry

/-- `struct_field_tele_of` ⊑ `structFieldTeleOf`. -/
theorem struct_field_tele_of_refines {pers st lst} {cty : arena.handle.EIdx}
    {n_p n_f i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_field_tele_of pers st cty n_p n_f i
      = ok o) :
    Sim absBinderL (fun _ => True) pers lst o
      (structFieldTeleOf (absEIdx cty) (absU n_p) (absU n_f) (absU i)) := by
  sorry

/-- `struct_field_idx_of` ⊑ `structFieldIdxOf`. -/
theorem struct_field_idx_of_refines {pers st lst} {cty : arena.handle.EIdx}
    {n_p n_f i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_field_idx_of pers st cty n_p n_f i
      = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o
      (structFieldIdxOf (absEIdx cty) (absU n_p) (absU n_f) (absU i)) := by
  sorry

/-- `rec_idx_of` ⊑ `recIdxOf` from the cursor on: the positions of the
recursive fields (finitary or reflexive).  The port's positions are absolute,
so the cursor's offset travels with them. -/
theorem rec_idx_of_refines
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {i : Std.Usize}
    {out : alloc.vec.Vec Std.U64} {o}
    (hrun : arena.inductives.native_parts.rec_idx_of ks i out = ok o) :
    absNatL o = absNatL out ++
      ((recIdxOf (absKindL ks)).filter fun j => decide (absSz i ≤ j)) := by
  sorry

/-! ## The record -/

/-- `native_parts_dup` is the identity on the abstraction. -/
theorem native_parts_dup_refines
    {p : arena.inductives.native_parts.NativeParts} {o}
    (hrun : arena.inductives.native_parts.native_parts_dup p = ok o) :
    absNativeParts o = absNativeParts p := by
  sorry

/-- `complete` ⊑ `NativeParts.complete` — the sum parts the former's run
returned with the recogniser's field kinds. -/
theorem complete_refines {p0 : arena.inductives.native_parts.NativeParts}
    {p1 : arena.inductives.sum_parts.InductiveShape} {o}
    (hrun : arena.inductives.native_parts.complete p0 p1 = ok o) :
    absNativeParts o =
      (absNativeParts p0).complete (absInductiveShape p1) := by
  sorry

/-- `with_kinds` ⊑ `NativeParts.withKinds`. -/
theorem with_kinds_refines {p : arena.inductives.native_parts.NativeParts}
    {ks : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o} (hrun : arena.inductives.native_parts.with_kinds p ks = ok o) :
    absNativeParts o = (absNativeParts p).withKinds (absKindLL ks) := by
  sorry

/-! ## The generated recursor with inductive hypotheses -/

/-- `struct_rec_prefix_at` ⊑ `structRecPrefixAt`. -/
theorem struct_rec_prefix_at_refines {pers st lst} {n_p n n_f e : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_prefix_at pers st n_p n n_f e
      = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o
      (structRecPrefixAt (absU n_p) (absU n) (absU n_f) (absU e)) := by
  sorry

/-- `struct_idx_at` ⊑ `structIdxAt`. -/
theorem struct_idx_at_refines {pers st lst} {n_f ofs i l m : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_idx_at pers st n_f ofs i l m e
      = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (structIdxAt (absU n_f) (absU ofs) (absU i) (absU l) (absU m)
        (absEIdx e)) := by
  sorry

/-- `struct_tele_at` ⊑ `structTeleAt` from the cursor on, with the accumulated
binders in front. -/
theorem struct_tele_at_refines {pers st lst} {n_f ofs i l : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize}
    {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_tele_at pers st n_f ofs i l pw tele
      k out = ok o) :
    Sim absBinderL (fun _ => True) pers lst o
      (do pure (absBinderL out ++
        (← structTeleAt (absU n_f) (absU ofs) (absU i) (absU l)
          (ConRon.Refine.absPropWhen pw) (absBinderLFrom tele k)))) := by
  sorry

/-- `struct_tele_vars` ⊑ `structTeleVars`. -/
theorem struct_tele_vars_refines {pers st lst} {m : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_tele_vars pers st m = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o (structTeleVars (absU m)) := by
  sorry

/-- `mk_pis_of` ⊑ `Expr.mkPisOf` from the cursor on. -/
theorem mk_pis_of_refines {pers st lst}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize} {body : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.mk_pis_of pers st tele k body = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (mkPisOf (absBinderLFrom tele k) (absEIdx body)) := by
  sorry

/-- `mk_lams_of` ⊑ `Expr.mkLamsOf` from the cursor on. -/
theorem mk_lams_of_refines {pers st lst}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize} {body : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.mk_lams_of pers st tele k body = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (mkLamsOf (absBinderLFrom tele k) (absEIdx body)) := by
  sorry

/-- `struct_idx_list` ⊑ `structIhApp`'s `idx.mapM` from the cursor on, with the
accumulated expressions in front. -/
theorem struct_idx_list_refines {pers st lst} {n_f ofs i l m : Std.U64}
    {idx : alloc.vec.Vec arena.handle.EIdx} {k : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_idx_list pers st n_f ofs i l m idx k
      out = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o
      (do pure (absEIdxL out ++
        (← structIdxListSpec (absU n_f) (absU ofs) (absU i) (absU l) (absU m)
          (absEIdxLFrom idx k)))) := by
  sorry

/-- `struct_ih_app` ⊑ `structIhApp`. -/
theorem struct_ih_app_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n n_f i : Std.U64}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {idx : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_ih_app pers st rec_c rlvls pw n_p n
      n_f i tele idx = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (structIhApp (absNIdx rec_c) (absLsIdx rlvls) (ConRon.Refine.absPropWhen pw)
        (absU n_p) (absU n) (absU n_f) (absU i) (absBinderL tele)
        (absEIdxL idx)) := by
  sorry

/-- `struct_ih_list` ⊑ `structRuleBodyR`'s `recIdx.mapM` from the cursor on. -/
theorem struct_ih_list_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n n_f : Std.U64} {rec_idx : alloc.vec.Vec Std.U64}
    {cty : arena.handle.EIdx} {k : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_ih_list pers st rec_c rlvls pw n_p n
      n_f rec_idx cty k out = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o
      (do pure (absEIdxL out ++
        (← structIhListSpec (absNIdx rec_c) (absLsIdx rlvls)
          (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absU n_f)
          (absEIdx cty) (absNatLFrom rec_idx k)))) := by
  sorry

/-- `struct_rule_body_r` ⊑ `structRuleBodyR`. -/
theorem struct_rule_body_r_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n n_f j : Std.U64} {rec_idx : alloc.vec.Vec Std.U64}
    {cty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rule_body_r pers st rec_c rlvls pw
      n_p n n_f j rec_idx cty = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (structRuleBodyR (absNIdx rec_c) (absLsIdx rlvls)
        (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absU n_f) (absU j)
        (absNatL rec_idx) (absEIdx cty)) := by
  sorry

/-- `struct_ih_pis_at` ⊑ `structIhPis`' cons arm past its three reads. -/
theorem struct_ih_pis_at_refines {pers st lst} {n_f ofs n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen} {cty : arena.handle.EIdx}
    {is : alloc.vec.Vec Std.U64} {k : Std.Usize} {l : Std.U64}
    {body : arena.handle.EIdx}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {idx2 : alloc.vec.Vec arena.handle.EIdx} {motive : arena.handle.EIdx}
    {i m : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_ih_pis_at pers st n_f ofs n_p pw cty
      is k l body tele idx2 motive i m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (structIhPisAtSpec (absU n_f) (absU ofs) (absU n_p)
        (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatLFrom is k |>.tail)
        (absU l) (absEIdx body) (absBinderL tele) (absEIdxL idx2) (absEIdx motive)
        (absU i) (absU m)) := by
  sorry

/-- `struct_ih_pis` ⊑ `structIhPis` from the cursor on. -/
theorem struct_ih_pis_refines {pers st lst} {n_f ofs n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen} {cty : arena.handle.EIdx}
    {is : alloc.vec.Vec Std.U64} {k : Std.Usize} {l : Std.U64}
    {body : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_ih_pis pers st n_f ofs n_p pw cty is
      k l body = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (structIhPis (absU n_f) (absU ofs) (absU n_p) (ConRon.Refine.absPropWhen pw)
        (absEIdx cty) (absNatLFrom is k) (absU l) (absEIdx body)) := by
  sorry

/-- `lift_list` ⊑ `structMinorTyR`'s `(rargs.drop nP).mapM` from the cursor
on. -/
theorem lift_list_refines {pers st lst} {amount c : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.lift_list pers st amount c xs i out
      = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o
      (do pure (absEIdxL out ++
        (← liftListSpec (absU amount) (absU c) (absEIdxLFrom xs i)))) := by
  sorry

/-- `struct_minor_ty_close` ⊑ `structMinorTyR`'s closing stage. -/
theorem struct_minor_ty_close_refines {pers st lst} {n_f ofs n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen} {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64} {q2 concl0 : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_minor_ty_close pers st n_f ofs n_p
      pw cty rec_idx q2 concl0 = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structMinorTyCloseSpec (absU n_f) (absU ofs) (absU n_p)
        (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatL rec_idx)
        (absEIdx q2) (absEIdx concl0)) := by
  sorry

/-- `struct_minor_ty_at` ⊑ `structMinorTyR`'s conclusion stage. -/
theorem struct_minor_ty_at_refines {pers st lst} {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f ofs : Std.U64}
    {pw : kernel.prop_when.PropWhen} {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64} {q2 r2 : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_minor_ty_at pers st c lps n_p n_f
      ofs pw cty rec_idx q2 r2 = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structMinorTyAtSpec (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f)
        (absU ofs) (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatL rec_idx)
        (absEIdx q2) (absEIdx r2)) := by
  sorry

/-- `struct_minor_ty_r` ⊑ `structMinorTyR`. -/
theorem struct_minor_ty_r_refines {pers st lst} {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f ofs : Std.U64}
    {pw : kernel.prop_when.PropWhen} {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_minor_ty_r pers st c lps n_p n_f ofs
      pw cty rec_idx = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structMinorTyR (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f) (absU ofs)
        (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatL rec_idx)) := by
  sorry

/-- `intern_binder` ⊑ the one node `structMinorsPisR` and `structMinorsLamsR`
differ in (finding 16). -/
theorem intern_binder_refines {pers st lst} {is_lam : Bool}
    {ty body : arena.handle.EIdx} {pw : kernel.prop_when.PropWhen} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.intern_binder pers st is_lam ty body pw
      = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internBinderSpec is_lam (absEIdx ty) (absEIdx body)
        (ConRon.Refine.absPropWhen pw)) := by
  sorry

/-- `struct_minors_pis_r` ⊑ the two twins as one recursion at `isLam`
(finding 16), from the cursor on. -/
theorem struct_minors_pis_r_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {k : Std.Usize} {ofs : Std.U64} {body : arena.handle.EIdx} {is_lam : Bool} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_minors_pis_r pers st lps n_p pw
      ctors k ofs body is_lam = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structMinorsRSpec (absNIdxL lps) (absU n_p) (ConRon.Refine.absPropWhen pw)
        (absCtors4LFrom ctors k) (absU ofs) (absEIdx body) is_lam) := by
  sorry

/-- `struct_minors_lams_r` ⊑ `structMinorsLamsR` from the cursor on — the
delegation of finding 16 at the `λ` flag. -/
theorem struct_minors_lams_r_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {k : Std.Usize} {ofs : Std.U64} {body : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_minors_lams_r pers st lps n_p pw
      ctors k ofs body = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structMinorsLamsR (absNIdxL lps) (absU n_p) (ConRon.Refine.absPropWhen pw)
        (absCtors4LFrom ctors k) (absU ofs) (absEIdx body)) := by
  sorry

/-- `u64_vec_dup` is the identity on the abstraction from the cursor on. -/
theorem u64_vec_dup_refines {xs : alloc.vec.Vec Std.U64} {i : Std.Usize}
    {out : alloc.vec.Vec Std.U64} {o}
    (hrun : arena.inductives.native_parts.u64_vec_dup xs i out = ok o) :
    absNatL o = absNatL out ++ absNatLFrom xs i := by
  have aux : ∀ (n : Nat) (i : Std.Usize) (out o : alloc.vec.Vec Std.U64),
      xs.val.length ≤ i.val + n →
      arena.inductives.native_parts.u64_vec_dup xs i out = ok o →
      absNatL o = absNatL out ++ absNatLFrom xs i := by
    intro n
    induction n with
    | zero =>
      intro i out o hn h
      rw [arena.inductives.native_parts.u64_vec_dup.eq_def] at h
      rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
      subst h
      simp [absNatL, absNatLFrom, List.drop_eq_nil_of_le (by omega : xs.val.length ≤ i.val)]
    | succ n ih =>
      intro i out o hn h
      rw [arena.inductives.native_parts.u64_vec_dup.eq_def] at h
      by_cases hc : i.val ≥ xs.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
        subst h
        simp [absNatL, absNatLFrom,
          List.drop_eq_nil_of_le (by omega : xs.val.length ≤ i.val)]
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
        obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hx)
        have hpv : out1.val = out.val ++ [x] := ConRon.Refine.vec_push_val hout1
        have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
        have hih := ih i2 out1 o (by omega) h
        rw [hih]
        simp only [absNatL, absNatLFrom, hpv, hi2v, List.map_append,
          List.append_assoc, List.map_cons, List.map_nil]
        congr 1
        rw [List.drop_eq_getElem_cons hb, hxv]
        simp
  exact aux xs.val.length i out o (by omega) hrun

/-! ## The generated recursor type and rules -/

/-- `struct_rec_ty_close` ⊑ `structRecTyR`'s closing stage. -/
theorem struct_rec_ty_close_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {pw : kernel.prop_when.PropWhen} {n : Std.U64}
    {q2 motive_ty major_body : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_ty_close pers st lps n_p n_idx
      tty ctors pw n q2 motive_ty major_body = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structRecTyCloseSpec (absNIdxL lps) (absU n_p) (absU n_idx) (absEIdx tty)
        (absCtors4L ctors) (ConRon.Refine.absPropWhen pw) (absU n) (absEIdx q2)
        (absEIdx motive_ty) (absEIdx major_body)) := by
  sorry

/-- `struct_rec_ty_at` ⊑ `structRecTyR`'s major-premise stage. -/
theorem struct_rec_ty_at_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {pw : kernel.prop_when.PropWhen} {n : Std.U64}
    {q2 motive_ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_ty_at pers st t lps n_p n_idx
      tty ctors pw n q2 motive_ty = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structRecTyAtSpec (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absEIdx tty) (absCtors4L ctors) (ConRon.Refine.absPropWhen pw) (absU n)
        (absEIdx q2) (absEIdx motive_ty)) := by
  sorry

/-- `struct_rec_ty_r` ⊑ `structRecTyR` — **the generated recursor type at a
recursive block**. -/
theorem struct_rec_ty_r_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p n_idx : Std.U64} {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_ty_r pers st t lps elim large
      n_p n_idx tty ctors = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structRecTyR (absNIdx t) (absNIdxL lps) (absNIdx elim) large (absU n_p)
        (absU n_idx) (absEIdx tty) (absCtors4L ctors)) := by
  sorry

/-- `struct_rec_rhs_close` ⊑ `structRecRhsR`'s closing stage. -/
theorem struct_rec_rhs_close_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {pw : kernel.prop_when.PropWhen} {n n_f : Std.U64}
    {q2 body motive_ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_rhs_close pers st lps n_p tty
      ctors pw n n_f q2 body motive_ty = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structRecRhsCloseSpec (absNIdxL lps) (absU n_p) (absEIdx tty)
        (absCtors4L ctors) (ConRon.Refine.absPropWhen pw) (absU n) (absU n_f)
        (absEIdx q2) (absEIdx body) (absEIdx motive_ty)) := by
  sorry

/-- `struct_rec_rhs_at` ⊑ `structRecRhsR`'s body past the `ctors[j]?`
lookup. -/
theorem struct_rec_rhs_at_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {rec_c : arena.handle.NIdx} {rlvls : arena.handle.LsIdx} {j : Std.U64}
    {pw : kernel.prop_when.PropWhen} {n n_f : Std.U64} {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64} {l : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_rhs_at pers st t lps n_p n_idx
      tty ctors rec_c rlvls j pw n n_f cty rec_idx l = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structRecRhsAtSpec (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absEIdx tty) (absCtors4L ctors) (absNIdx rec_c) (absLsIdx rlvls) (absU j)
        (ConRon.Refine.absPropWhen pw) (absU n) (absU n_f) (absEIdx cty)
        (absNatL rec_idx) (absLIdx l)) := by
  sorry

/-- `struct_rec_rhs_r` ⊑ `structRecRhsR` — **the generated rule** for
constructor `j` at a recursive block. -/
theorem struct_rec_rhs_r_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p n_idx : Std.U64} {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {rec_c : arena.handle.NIdx} {rlvls : arena.handle.LsIdx} {j : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_rhs_r pers st t lps elim large
      n_p n_idx tty ctors rec_c rlvls j = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (structRecRhsR (absNIdx t) (absNIdxL lps) (absNIdx elim) large (absU n_p)
        (absU n_idx) (absEIdx tty) (absCtors4L ctors) (absNIdx rec_c)
        (absLsIdx rlvls) (absU j)) := by
  sorry

/-- `native_ctors4` ⊑ `nativeCtors4` from the cursor on. -/
theorem native_ctors4_refines
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))} {o}
    (hrun : arena.inductives.native_parts.native_ctors4 ctors_a kinds i out = ok o) :
    absCtors4L o = absCtors4L out ++
      nativeCtors4 (absCtorsLFrom ctors_a i) (absKindLLFrom kinds i) := by
  sorry

/-! ## The stream's rules against the generated ones -/

/-- `binders_reset_beq_from` ⊑ `nativeRulePrefixOk`'s binder comparison from
the `i`-th on. -/
theorem binders_reset_beq_from_refines {pers st lst}
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 n i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.binders_reset_beq_from pers st bs1 bs2 o1
      o2 n i = ok o) :
    Sim id (fun _ => True) pers lst o
      (bindersResetBeqSpec (absBinderL bs1) (absBinderL bs2) (absU o1) (absU o2)
        (absU n - absU i) (absU i)) := by
  sorry

/-- `binders_reset_beq` ⊑ the same at `i = 0`. -/
theorem binders_reset_beq_refines {pers st lst}
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 n : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.binders_reset_beq pers st bs1 bs2 o1 o2 n
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (bindersResetBeqSpec (absBinderL bs1) (absBinderL bs2) (absU o1) (absU o2)
        (absU n) 0) := by
  sorry

/-- `native_rule_fields_ok` ⊑ `nativeRulePrefixOk`'s field comparison. -/
theorem native_rule_fields_ok_refines {pers st lst} {n_p n j n_f : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {mty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_rule_fields_ok pers st n_p n j n_f
      rbs mty = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeRuleFieldsOkSpec (absU n_p) (absU n) (absU j) (absU n_f)
        (absBinderL rbs) (absEIdx mty)) := by
  sorry

/-- `native_rule_prefix_ok` ⊑ `nativeRulePrefixOk` — **the rule's `λ` prefix
against the stream's own recursor type** (con-leche's task #271). -/
theorem native_rule_prefix_ok_refines {pers st lst} {rec_ty : arena.handle.EIdx}
    {n_p n j n_f : Std.U64} {rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_rule_prefix_ok pers st rec_ty n_p n
      j n_f rhs = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeRulePrefixOk (absEIdx rec_ty) (absU n_p) (absU n) (absU j) (absU n_f)
        (absEIdx rhs)) := by
  sorry

/-- `native_rule_body_ok` ⊑ `nativeRulesOk`'s per-rule body test. -/
theorem native_rule_body_ok_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n n_f j : Std.U64} {rec_idx : alloc.vec.Vec Std.U64}
    {cty rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_rule_body_ok pers st rec_c rlvls pw
      n_p n n_f j rec_idx cty rhs = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeRuleBodyOkSpec (absNIdx rec_c) (absLsIdx rlvls)
        (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absU n_f) (absU j)
        (absNatL rec_idx) (absEIdx cty) (absEIdx rhs)) := by
  sorry

/-- `native_rules_ok_from` ⊑ `nativeRulesOk`'s `(List.range n).allM` from rule
`j` on. -/
theorem native_rules_ok_from_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n : Std.U64} {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {rhss : alloc.vec.Vec arena.handle.EIdx} {rec_ty : arena.handle.EIdx}
    {j : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_rules_ok_from pers st rec_c rlvls pw
      n_p n cs kinds rhss rec_ty j = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeRulesOkFromSpec (absNIdx rec_c) (absLsIdx rlvls)
        (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absCtorsL cs)
        (absKindLL kinds) (absEIdxL rhss) (absEIdx rec_ty) (absU n - absU j)
        (absU j)) := by
  sorry

/-- `native_rules_ok` ⊑ `nativeRulesOk` — **the stream's rules against the
generated ones**, at install. -/
theorem native_rules_ok_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n : Std.U64} {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {rhss : alloc.vec.Vec arena.handle.EIdx} {rec_ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_rules_ok pers st rec_c rlvls pw n_p
      n cs kinds rhss rec_ty = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeRulesOk (absNIdx rec_c) (absLsIdx rlvls) (ConRon.Refine.absPropWhen pw)
        (absU n_p) (absU n) (absCtorsL cs) (absKindLL kinds) (absEIdxL rhss)
        (absEIdx rec_ty)) := by
  sorry

/-! ## Recognition -/

/-- `native_counts` ⊑ `nativeCounts?` — **finding 17**: the port takes the
constructor count where the twin takes the list, so the statement supplies
`cs.length`. -/
theorem native_counts_refines {pers st lst} {n_pd : Std.U64}
    {cv_t : arena.env.IConstantVal} {n_ctors m_i r_p : Std.U64} {o}
    {cs : List (IConstantVal × Nat × Nat)}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hlen : absU n_ctors = cs.length)
    (hrun : arena.inductives.native_parts.native_counts pers st n_pd cv_t n_ctors m_i
      r_p = ok o) :
    Sim (Option.map fun p => (absU p.1, absU p.2)) (fun _ => True) pers lst o
      (nativeCounts? (absU n_pd) (absIConstantVal cv_t) cs (absU m_i)
        (absU r_p)) := by
  sorry

/-- `rules_pin_ok` ⊑ `nativeRecPinOk`'s `(List.range …).all` from rule `j`
on. -/
theorem rules_pin_ok_refines {rules : alloc.vec.Vec arena.env.IRecRule}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {n j : Std.U64} {o}
    (hrun : arena.inductives.native_parts.rules_pin_ok rules cs n j = ok o) :
    o = rulesPinOkSpec (rules.val.map absIRecRule) (absCtors3L cs)
      (absU n - absU j) (absU j) := by
  sorry

/-- `native_rec_pin_ok` ⊑ `nativeRecPinOk` — **the recursor record's structural
pin** (con-leche's task #220).  Pure on both sides: tags, names and counts
only. -/
theorem native_rec_pin_ok_refines
    {p : arena.inductives.sum_parts.InductiveShape}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrun : arena.inductives.native_parts.native_rec_pin_ok p block = ok o) :
    o = nativeRecPinOk (absInductiveShape p) (absICIL block) := by
  sorry

/-- `native_rec_lps_ok` ⊑ `nativeRecLpsOk` — the recursor record's
level-parameter pin. -/
theorem native_rec_lps_ok_refines
    {p : arena.inductives.sum_parts.InductiveShape} {o}
    (hrun : arena.inductives.native_parts.native_rec_lps_ok p = ok o) :
    o = nativeRecLpsOk (absInductiveShape p) := by
  sorry

/-- `nidx_cons_from` copies `ns` from the cursor on onto `out`. -/
theorem nidx_cons_from_refines {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.inductives.native_parts.nidx_cons_from ns i out = ok o) :
    absNIdxL o = absNIdxL out ++ absNIdxLFrom ns i := by
  sorry

/-- `nidx_cons` ⊑ `n :: ns` — the twin's `elim :: lps`, over a `Vec`. -/
theorem nidx_cons_refines {n : arena.handle.NIdx}
    {ns : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.inductives.native_parts.nidx_cons n ns = ok o) :
    absNIdxL o = absNIdx n :: absNIdxL ns := by
  sorry

/-- `ctors_pin_ok` ⊑ `nativeShape?`'s `cs.all` pin from the cursor on. -/
theorem ctors_pin_ok_refines {reserved : alloc.vec.Vec arena.handle.NIdx}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {n_p : Std.U64} {lps : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize} {o}
    (hrun : arena.inductives.native_parts.ctors_pin_ok reserved cs n_p lps i
      = ok o) :
    o = ctorsPinOkSpec (absNIdxL reserved) (absCtors3LFrom cs i) (absU n_p)
      (absNIdxL lps) := by
  sorry

/-- `ctors_of` ⊑ `cs.map fun c => (c.1, c.2.2)` from the cursor on. -/
theorem ctors_of_refines
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {i : Std.Usize} {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {o}
    (hrun : arena.inductives.native_parts.ctors_of cs i out = ok o) :
    absCtorsL o = absCtorsL out ++
      (absCtors3LFrom cs i).map fun c => (c.1, c.2.2) := by
  sorry

/-- `rhss_of` ⊑ `rules.map (·.rhs)` from the cursor on. -/
theorem rhss_of_refines {rules : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrun : arena.inductives.native_parts.rhss_of rules i out = ok o) :
    absEIdxL o = absEIdxL out ++ (absIRecRuleLFrom rules i).map (·.rhs) := by
  sorry

/-- `native_shape_small` ⊑ `nativeShape?`'s small-eliminator arm. -/
theorem native_shape_small_refines {pers st lst}
    {cv_t cv_r : arena.env.IConstantVal} {n_p n_idx : Std.U64}
    {s : arena.handle.LIdx} {is_prop : Bool}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {rhss : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_shape_small pers st cv_t cv_r n_p
      n_idx s is_prop ctors rhss = ok o) :
    Sim (Option.map absInductiveShape) (fun _ => True) pers lst o
      (nativeShapeSmallSpec (absIConstantVal cv_t) (absIConstantVal cv_r) (absU n_p)
        (absU n_idx) (absLIdx s) is_prop (absCtorsL ctors) (absEIdxL rhss)) := by
  sorry

/-- `native_shape_elim` ⊑ `nativeShape?`'s eliminator split. -/
theorem native_shape_elim_refines {pers st lst}
    {cv_t : arena.env.IConstantVal}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {cv_r : arena.env.IConstantVal} {rules : alloc.vec.Vec arena.env.IRecRule}
    {n_p n_idx : Std.U64} {s : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_shape_elim pers st cv_t cs cv_r
      rules n_p n_idx s = ok o) :
    Sim (Option.map absInductiveShape) (fun _ => True) pers lst o
      (nativeShapeElimSpec (absIConstantVal cv_t) (absCtors3L cs)
        (absIConstantVal cv_r) (absIRecRuleL rules) (absU n_p) (absU n_idx)
        (absLIdx s)) := by
  sorry

/-- `native_shape_sort` ⊑ `nativeShape?`'s result-sort read. -/
theorem native_shape_sort_refines {pers st lst} {cv_t : arena.env.IConstantVal}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {cv_r : arena.env.IConstantVal} {rules : alloc.vec.Vec arena.env.IRecRule}
    {n_p n_idx : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_shape_sort pers st cv_t cs cv_r
      rules n_p n_idx = ok o) :
    Sim (Option.map absInductiveShape) (fun _ => True) pers lst o
      (nativeShapeSortSpec (absIConstantVal cv_t) (absCtors3L cs)
        (absIConstantVal cv_r) (absIRecRuleL rules) (absU n_p) (absU n_idx)) := by
  sorry

/-- `native_shape_at` ⊑ `nativeShape?`'s body once the block's members are in
hand. -/
theorem native_shape_at_refines {pers st lst} {n_pd : Std.U64}
    {cv_t : arena.env.IConstantVal}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {cv_r : arena.env.IConstantVal} {m_i r_p : Std.U64}
    {rules : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_shape_at pers st n_pd cv_t cs cv_r
      m_i r_p rules = ok o) :
    Sim (Option.map absInductiveShape) (fun _ => True) pers lst o
      (nativeShapeAtSpec (absU n_pd) (absIConstantVal cv_t) (absCtors3L cs)
        (absIConstantVal cv_r) (absU m_i) (absU r_p) (absIRecRuleL rules)) := by
  sorry

/-- `native_shape` ⊑ `nativeShape?`. -/
theorem native_shape_refines {pers st lst} {n_pd : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_shape pers st n_pd block = ok o) :
    Sim (Option.map absInductiveShape) (fun _ => True) pers lst o
      (nativeShape? (absU n_pd) (absICIL block)) := by
  sorry

/-- `native_parts` ⊑ `nativeParts?` — recognise a direct block: its SHAPE; the
fields' kinds are a PLACEHOLDER the install fills. -/
theorem native_parts_refines {pers st lst} {n_pd : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_parts pers st n_pd block = ok o) :
    Sim (Option.map absNativeParts) (fun _ => True) pers lst o
      (nativeParts? (absU n_pd) (absICIL block)) := by
  sorry

/-! ## The axiom census

DESIGN.md §8.2's discipline (task #97-P5-0 §8): every CLOSED lemma of the tier
is `#print axioms`-checked under `#guard_msgs`, and every one reads
`[propext, Classical.choice, Quot.sound]` and nothing else — no `sorryAx` on a
closed lemma, and no `bv_decide` axiom anywhere in `Refine2/`.  These two are
this module's closed pair: the five-constructor copy and the five-by-five
equality table §3.4 forbids `#[derive]` for. -/

/-- info: 'ConRon.Refine2.rec_field_kind_dup_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rec_field_kind_dup_refines

/-- info: 'ConRon.Refine2.rec_field_kind_beq_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rec_field_kind_beq_refines

end ConRon.Refine2
