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
import ConRon.Refine2.Inductives.SumParts

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

open Lockstep in
@[lockstep] theorem rec_field_kind_dup_twin
    {k : arena.inductives.native_parts.RecFieldKind} :
    LSP (arena.inductives.native_parts.rec_field_kind_dup k) (fun o => TwinEq (absRecFieldKind k) (absRecFieldKind o)) :=
  fun o h => (rec_field_kind_dup_refines h).symm

/-- `rec_field_kind_beq` ⊑ `RecFieldKind`'s `DecidableEq` — §3.4 forbids
`#[derive]`, so the port spells the five-by-five table out. -/
theorem rec_field_kind_beq_refines
    {a b : arena.inductives.native_parts.RecFieldKind} {o}
    (hrun : arena.inductives.native_parts.rec_field_kind_beq a b = ok o) :
    o = (absRecFieldKind a == absRecFieldKind b) := by
  rw [arena.inductives.native_parts.rec_field_kind_beq.eq_def] at hrun
  cases a <;> cases b <;> (have h2 := Result.ok_injective hrun; subst h2; rfl)

open Lockstep in
@[lockstep] theorem rec_field_kind_beq_twin
    {a b : arena.inductives.native_parts.RecFieldKind} :
    LSP (arena.inductives.native_parts.rec_field_kind_beq a b) (fun o => TwinEq ((absRecFieldKind a == absRecFieldKind b)) (o)) :=
  fun o h => (rec_field_kind_beq_refines h).symm

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

open Lockstep in
/-- `kinds_copy_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem kinds_copy_twin0
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} :
    LSP (arena.inductives.native_parts.kinds_copy ks 0#usize (alloc.vec.Vec.new arena.inductives.native_parts.RecFieldKind)) (fun o => TwinEq (absKindL ks) (absKindL o)) := by
  intro o h
  have h' := (kinds_copy_refines h).symm
  simpa [Lockstep.TwinEq, absKindLFrom, absKindL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem kinds_copy_twin
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} :
    LSP (arena.inductives.native_parts.kinds_copy ks i out) (fun o => TwinEq (absKindL out ++ absKindLFrom ks i) (absKindL o)) :=
  fun o h => (kinds_copy_refines h).symm

/-- `kindss_copy` is the identity on the abstraction from the cursor on. -/
theorem kindss_copy_refines
    {kss : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o} (hrun : arena.inductives.native_parts.kindss_copy kss i out = ok o) :
    absKindLL o = absKindLL out ++ absKindLLFrom kss i := by
  simp only [absKindLL, absKindLLFrom]
  refine vec_cursor_copy kss _ _
    (arena.inductives.native_parts.kindss_copy kss) ?_ ?_ i out o hrun
  · intro i out o hn h
    rw [arena.inductives.native_parts.kindss_copy.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len kss by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < kss.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.native_parts.kindss_copy.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len kss by scalar_tac)] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hvx : v = x := by
      have h1 := vec_index_some hv; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hvx
    refine ⟨i2, v1, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, ?_, h⟩
    have h2 := kinds_copy_refines hv1
    simpa [absKindL, absKindLFrom, alloc.vec.Vec.new,
      show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h2

open Lockstep in
/-- `kindss_copy_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem kindss_copy_twin0
    {kss : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)} :
    LSP (arena.inductives.native_parts.kindss_copy kss 0#usize (alloc.vec.Vec.new (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind))) (fun o => TwinEq (absKindLL kss) (absKindLL o)) := by
  intro o h
  have h' := (kindss_copy_refines h).symm
  simpa [Lockstep.TwinEq, absKindLLFrom, absKindLL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem kindss_copy_twin
    {kss : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)} :
    LSP (arena.inductives.native_parts.kindss_copy kss i out) (fun o => TwinEq (absKindLL out ++ absKindLLFrom kss i) (absKindLL o)) :=
  fun o h => (kindss_copy_refines h).symm

/-- `kind_get_d` ⊑ `ks.getD i .ordinary`. -/
theorem kind_get_d_refines
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {i : Std.U64}
    {o} (hrun : arena.inductives.native_parts.kind_get_d ks i = ok o) :
    absRecFieldKind o = (absKindL ks).getD (absU i) .ordinary := by
  -- task #97-P5-Usize: the bound is compared in `u64`, so the cast under it
  -- is exact on every platform (round 3 §R3.5's finding, fixed in the Rust).
  rw [arena.inductives.native_parts.kind_get_d] at hrun
  obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  simp only [lift, Result.ok.injEq] at hi2
  have hi2v : i2.val = ks.val.length := by
    rw [← hi2, ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
  by_cases hlt : i < i2
  · rw [if_pos hlt] at hrun
    have hlt' : i.val < ks.val.length := by scalar_tac
    obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    simp only [lift, Result.ok.injEq] at hi3
    have hi3v : i3.val = i.val := by
      rw [← hi3]
      exact ConRon.Refine.ExprOps.u64_cast_usize_val
        (le_trans (Nat.le_of_lt hlt') ks.property)
    obtain ⟨rfk, hrfk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hx := vec_index_some hrfk
    rw [hi3v] at hx
    rw [rec_field_kind_dup_refines hrun]
    simp [absKindL, absU, List.getD_eq_getElem?_getD, hx]
  · rw [if_neg hlt] at hrun
    obtain rfl := Result.ok_injective hrun
    have hge : ks.val.length ≤ i.val := by scalar_tac
    simp [absKindL, absU, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa using hge), absRecFieldKind]

open Lockstep in
@[lockstep] theorem kind_get_d_twin
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {i : Std.U64} :
    LSP (arena.inductives.native_parts.kind_get_d ks i) (fun o => TwinEq ((absKindL ks).getD (absU i) .ordinary) (absRecFieldKind o)) :=
  fun o h => (kind_get_d_refines h).symm

/-! ## The field kinds -/

/-- `rec_fam_ok` ⊑ `recFamOk` — is `e` the family at the parameter variables
followed by `nIdx` index expressions none of which mentions the block?
Official's `is_valid_ind_app` exactly. -/
theorem rec_fam_ok_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx ofs : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_fam_ok pers st t lps n_p n_idx ofs e
      = ok o) :
    Sim₀ id pers lst o
      (recFamOk (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU ofs)
        (absEIdx e)) := by
  sorry

open Lockstep in
@[lockstep] theorem rec_fam_ok_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx ofs : Std.U64}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_parts.rec_fam_ok pers st t lps n_p n_idx ofs e) lst
      (recFamOk (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU ofs)
        (absEIdx e)) :=
  LS.ofSim₀ fun _ h => rec_fam_ok_refines hrel hinv h

/-- `idx_free_of` ⊑ `recFamOk`'s closing `allM`, from the cursor on. -/
theorem idx_free_of_refines {pers st lst} {t : arena.handle.NIdx}
    {idx : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.idx_free_of pers st t idx i = ok o) :
    Sim₀ id pers lst o
      (idxFreeOfSpec (absNIdx t) (absEIdxLFrom idx i)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  revert st lst hrel hinv hrun
  simp only [absEIdxLFrom]
  intro st lst hrel hinv _
  refine ls_cursor idx (absEIdx) (idxFreeOfSpec (absNIdx t))
    (fun st i => arena.inductives.native_parts.idx_free_of pers st t idx i) ?_ ?_ i st lst hrel hinv
  · intro st lst i hn hrel hinv
    try simp only []
    rw [arena.inductives.native_parts.idx_free_of.eq_def, idxFreeOfSpec]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    try simp only []
    rw [arena.inductives.native_parts.idx_free_of.eq_def, idxFreeOfSpec]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
@[lockstep] theorem idx_free_of_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {idx : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_parts.idx_free_of pers st t idx i) lst
      (idxFreeOfSpec (absNIdx t) (absEIdxLFrom idx i)) :=
  LS.ofSim₀ fun _ h => idx_free_of_refines hrel hinv h

/-- `rec_positivity_at` ⊑ `recPositivityAt` — the leaf of the walk, past the
`mentionsConst` test (which `rec_positivity` makes before the call; the
statement used to read `recPositivityAtSpec`, which includes that test, so the
two sides did not do the same thing — task #97-T2-LOCKSTEP lane Inductives). -/
theorem rec_positivity_at_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx ofs : Std.U64}
    {h : arena.handle.EIdx} {k : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_positivity_at pers st t lps n_p n_idx
      ofs h k = ok o) :
    Sim₀ absRecFieldKind pers lst o
      (recPositivityAt (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absU ofs) (absEIdx h) (absU k)) := by
  sorry

open Lockstep in
@[lockstep] theorem rec_positivity_at_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx ofs : Std.U64}
    {h : arena.handle.EIdx}
    {k : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absRecFieldKind a) (arena.inductives.native_parts.rec_positivity_at pers st t lps n_p n_idx ofs h k) lst
      (recPositivityAt (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absU ofs) (absEIdx h) (absU k)) :=
  LS.ofSim₀ fun _ h => rec_positivity_at_refines hrel hinv h

/-- `rec_positivity` ⊑ `recPositivity` — official `check_positivity`'s
telescope walk on a field domain that mentions the block, syntactically. -/
theorem rec_positivity_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx ofs fuel : Std.U64}
    {h : arena.handle.EIdx} {k : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_positivity pers st t lps n_p n_idx ofs
      fuel h k = ok o) :
    Sim₀ absRecFieldKind pers lst o
      (recPositivity (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU ofs)
        (absU fuel) (absEIdx h) (absU k)) := by
  sorry

open Lockstep in
@[lockstep] theorem rec_positivity_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx ofs fuel : Std.U64}
    {h : arena.handle.EIdx}
    {k : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absRecFieldKind a) (arena.inductives.native_parts.rec_positivity pers st t lps n_p n_idx ofs fuel h k) lst
      (recPositivity (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU ofs)
        (absU fuel) (absEIdx h) (absU k)) :=
  LS.ofSim₀ fun _ h => rec_positivity_refines hrel hinv h

/-- `rec_field_kind` ⊑ `recFieldKind`. -/
theorem rec_field_kind_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx ofs : Std.U64}
    {dom : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_field_kind pers st t lps n_p n_idx ofs
      dom = ok o) :
    Sim₀ absRecFieldKind pers lst o
      (recFieldKind (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU ofs)
        (absEIdx dom)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.rec_field_kind, recFieldKind]
  lockstep

open Lockstep in
@[lockstep] theorem rec_field_kind_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx ofs : Std.U64}
    {dom : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absRecFieldKind a) (arena.inductives.native_parts.rec_field_kind pers st t lps n_p n_idx ofs dom) lst
      (recFieldKind (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx) (absU ofs)
        (absEIdx dom)) :=
  LS.ofSim₀ fun _ h => rec_field_kind_refines hrel hinv h

/-- `rec_ctor_kind_at` ⊑ `recCtorKinds`' per-field post-step. -/
theorem rec_ctor_kind_at_refines {pers st lst} {cty : arena.handle.EIdx}
    {n_p i : Std.U64} {k : arena.inductives.native_parts.RecFieldKind} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_ctor_kind_at pers st cty n_p i k
      = ok o) :
    Sim₀ absRecFieldKind pers lst o
      (recCtorKindAtSpec (absEIdx cty) (absU n_p) (absU i)
        (absRecFieldKind k)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  cases k <;> simp only [arena.inductives.native_parts.rec_ctor_kind_at,
    recCtorKindAtSpec, absRecFieldKind] <;> lockstep

open Lockstep in
@[lockstep] theorem rec_ctor_kind_at_ls
    {pers st lst}
    {cty : arena.handle.EIdx}
    {n_p i : Std.U64}
    {k : arena.inductives.native_parts.RecFieldKind}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absRecFieldKind a) (arena.inductives.native_parts.rec_ctor_kind_at pers st cty n_p i k) lst
      (recCtorKindAtSpec (absEIdx cty) (absU n_p) (absU i)
        (absRecFieldKind k)) :=
  LS.ofSim₀ fun _ h => rec_ctor_kind_at_refines hrel hinv h

/-- `rec_ctor_kinds_from` ⊑ `recCtorKinds`' per-field walk from field `i` on,
with the accumulated kinds in front. -/
theorem rec_ctor_kinds_from_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {cty : arena.handle.EIdx} {n_f : Std.U64}
    {cbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {i : Std.U64}
    {out : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_ctor_kinds_from pers st t lps n_p n_idx
      cty n_f cbs i out = ok o) :
    Sim₀ absKindL pers lst o
      (do pure (absKindL out ++
        (← recCtorKindsFromSpec (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
          (absEIdx cty) (absBinderL cbs) (absU n_f - absU i) (absU i)))) := by
  sorry

open Lockstep in
@[lockstep] theorem rec_ctor_kinds_from_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {cty : arena.handle.EIdx}
    {n_f : Std.U64}
    {cbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {i : Std.U64}
    {out : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absKindL a) (arena.inductives.native_parts.rec_ctor_kinds_from pers st t lps n_p n_idx cty n_f cbs i out) lst
      (do pure (absKindL out ++
        (← recCtorKindsFromSpec (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
          (absEIdx cty) (absBinderL cbs) (absU n_f - absU i) (absU i)))) :=
  LS.ofSim₀ fun _ h => rec_ctor_kinds_from_refines hrel hinv h

/-- `all_negative` ⊑ `ks.map fun _ => .negative` from the cursor on. -/
theorem all_negative_refines {n i : Std.U64}
    {out : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {o}
    (hrun : arena.inductives.native_parts.all_negative n i out = ok o) :
    absKindL o = absKindL out ++ List.replicate (absU n - absU i) .negative := by
  refine cursor_induction (fun i : Std.U64 => i.val) n.val
    (fun i out => ∀ o, arena.inductives.native_parts.all_negative n i out = ok o →
      absKindL o = absKindL out ++ List.replicate (absU n - absU i) .negative)
    ?_ ?_ i out o hrun
  · intro i out hn o h
    have hn' : n.val ≤ i.val := hn
    rw [arena.inductives.native_parts.all_negative.eq_def] at h
    rw [if_pos (show i ≥ n by scalar_tac), Result.ok.injEq] at h
    subst h
    simp [absU, show n.val - i.val = 0 by omega]
  · intro i out hi ih o h
    have hi' : i.val < n.val := hi
    rw [arena.inductives.native_parts.all_negative.eq_def] at h
    rw [if_neg (show ¬ i ≥ n by scalar_tac)] at h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi1v : i1.val = i.val + 1 := absU_add_one hi1
    rw [ih i1 out1 hi1v o h]
    have hrep : absU n - absU i = (absU n - absU i1) + 1 := by
      simp only [absU, hi1v]; omega
    rw [hrep, List.replicate_succ]
    simp [absKindL, ConRon.Refine.vec_push_val hout1, absRecFieldKind]

open Lockstep in
@[lockstep] theorem all_negative_twin
    {n i : Std.U64}
    {out : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} :
    LSP (arena.inductives.native_parts.all_negative n i out) (fun o => TwinEq (absKindL out ++ List.replicate (absU n - absU i) .negative) (absKindL o)) :=
  fun o h => (all_negative_refines h).symm

/-- `rec_ctor_kinds` ⊑ `recCtorKinds` — the kinds of one constructor's fields,
off its (raw or annotated) type. -/
theorem rec_ctor_kinds_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {c : arena.env.IConstantVal × Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.rec_ctor_kinds pers st t lps n_p n_idx c
      = ok o) :
    Sim₀ (Option.map absKindL) pers lst o
      (recCtorKinds (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absIConstantVal c.1, absU c.2)) := by
  sorry

open Lockstep in
@[lockstep] theorem rec_ctor_kinds_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {c : arena.env.IConstantVal × Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absKindL) a) (arena.inductives.native_parts.rec_ctor_kinds pers st t lps n_p n_idx c) lst
      (recCtorKinds (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absIConstantVal c.1, absU c.2)) :=
  LS.ofSim₀ fun _ h => rec_ctor_kinds_refines hrel hinv h

/-! ## The telescope readers -/

open Lockstep in
/-- `pi_binders` ⊑ `piBinders`, with the accumulated binders in front — a READ
(`LSR`), proved by the counted fuel induction.  (Finding 18's `SimRE`
statement, which also claimed the twin state unchanged, is gone: the lockstep
judgement does not carry that, and no caller used it.) -/
@[lockstep] theorem pi_binders_ls
    {pers st lst}
    {fuel : Std.U64}
    {h : arena.handle.EIdx}
    {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (fun r => (absBinderL r.1, absEIdx r.2)) a) (arena.inductives.native_parts.pi_binders pers st fuel h out) st lst
      (do
        let q ← piBinders (absU fuel) (absEIdx h)
        pure (absBinderL out ++ q.1, q.2)) := by
  suffices H : ∀ (n : Nat) (fuel : Std.U64) (h : arena.handle.EIdx)
      (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (lst : AState),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = (fun r => (absBinderL r.1, absEIdx r.2)) a)
        (arena.inductives.native_parts.pi_binders pers st fuel h out) st lst
        (do
          let q ← piBinders (absU fuel) (absEIdx h)
          pure (absBinderL out ++ q.1, q.2)) from H _ fuel h out lst rfl hrel hinv
  clear hrel hinv
  intro n
  induction n with
  | zero =>
    intro fuel h out lst hf hrel hinv
    have h0 : fuel = 0#u64 := by scalar_tac
    subst h0
    rw [arena.inductives.native_parts.pi_binders.eq_def, if_pos rfl]
    rw [show absU (0#u64 : Std.U64) = 0 from rfl, piBinders]
    apply LSR.of_LS
    lockstep
  | succ n ih =>
    intro fuel h out lst hf hrel hinv
    rw [arena.inductives.native_parts.pi_binders.eq_def, if_neg (by scalar_tac)]
    rw [show absU fuel = n + 1 by simp [absU, hf], piBinders]
    apply LSR.of_LS
    lockstep

open Lockstep in
/-- `pi_binders` from an empty accumulator IS `piBinders` (the callers' form). -/
@[lockstep] theorem pi_binders_new_ls
    {pers st lst}
    {fuel : Std.U64}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (fun r => (absBinderL r.1, absEIdx r.2)) a)
      (arena.inductives.native_parts.pi_binders pers st fuel h
        (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta))) st lst
      (piBinders (absU fuel) (absEIdx h)) := by
  have hl := pi_binders_ls (fuel := fuel) (h := h)
    (out := alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)) hrel hinv
  have e : (do
      let q ← piBinders (absU fuel) (absEIdx h)
      pure (absBinderL (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)) ++ q.1,
        q.2) : AM _) = piBinders (absU fuel) (absEIdx h) := by
    simp [absBinderL, alloc.vec.Vec.new]
  rwa [e] at hl

/-- `struct_field_tele_of` ⊑ `structFieldTeleOf`. -/
theorem struct_field_tele_of_refines {pers st lst} {cty : arena.handle.EIdx}
    {n_p n_f i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_field_tele_of pers st cty n_p n_f i
      = ok o) :
    Sim₀ absBinderL pers lst o
      (structFieldTeleOf (absEIdx cty) (absU n_p) (absU n_f) (absU i)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_field_tele_of_ls
    {pers st lst}
    {cty : arena.handle.EIdx}
    {n_p n_f i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absBinderL a) (arena.inductives.native_parts.struct_field_tele_of pers st cty n_p n_f i) lst
      (structFieldTeleOf (absEIdx cty) (absU n_p) (absU n_f) (absU i)) :=
  LS.ofSim₀ fun _ h => struct_field_tele_of_refines hrel hinv h

/-- `struct_field_idx_of` ⊑ `structFieldIdxOf`. -/
theorem struct_field_idx_of_refines {pers st lst} {cty : arena.handle.EIdx}
    {n_p n_f i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_field_idx_of pers st cty n_p n_f i
      = ok o) :
    Sim₀ absEIdxL pers lst o
      (structFieldIdxOf (absEIdx cty) (absU n_p) (absU n_f) (absU i)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_field_idx_of_ls
    {pers st lst}
    {cty : arena.handle.EIdx}
    {n_p n_f i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.native_parts.struct_field_idx_of pers st cty n_p n_f i) lst
      (structFieldIdxOf (absEIdx cty) (absU n_p) (absU n_f) (absU i)) :=
  LS.ofSim₀ fun _ h => struct_field_idx_of_refines hrel hinv h

/-- `rec_idx_of` ⊑ `recIdxOf` from the cursor on: the positions of the
recursive fields (finitary or reflexive).  The port's positions are absolute,
so the cursor's offset travels with them. -/
theorem rec_idx_of_refines
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {i : Std.Usize}
    {out : alloc.vec.Vec Std.U64} {o}
    (hrun : arena.inductives.native_parts.rec_idx_of ks i out = ok o) :
    absNatL o = absNatL out ++
      ((recIdxOf (absKindL ks)).filter fun j => decide (absSz i ≤ j)) := by
  have hlen : (absKindL ks).length = ks.val.length := by simp [absKindL]
  simp only [recIdxOf, absSz, filter_range_filter_ge, hlen]
  refine cursor_induction (fun i : Std.Usize => i.val) ks.val.length
    (fun i out => ∀ o, arena.inductives.native_parts.rec_idx_of ks i out = ok o →
      absNatL o = absNatL out ++ (List.range' i.val (ks.val.length - i.val)).filter
        (fun j => (absKindL ks).getD j .ordinary == RecFieldKind.recursive ||
          (absKindL ks).getD j .ordinary == RecFieldKind.reflexive))
    ?_ ?_ i out o hrun
  · intro i out hn o h
    rw [arena.inductives.native_parts.rec_idx_of.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
    obtain rfl := h
    simp [show ks.val.length - i.val = 0 by omega]
  · intro i out hi ih o h
    rw [arena.inductives.native_parts.rec_idx_of.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ks by scalar_tac)] at h
    obtain ⟨rfk, hrfk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hit, hhit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hrfk
    have hgetd : (absKindL ks).getD i.val .ordinary = absRecFieldKind rfk := by
      simp only [absKindL, List.getD_eq_getElem?_getD, List.getElem?_map, hx]
      rfl
    have hbv : b = (absRecFieldKind rfk == RecFieldKind.recursive) :=
      rec_field_kind_beq_refines hb
    have hhitv : hit = ((absRecFieldKind rfk == RecFieldKind.recursive) ||
        (absRecFieldKind rfk == RecFieldKind.reflexive)) := by
      cases hbb : b
      · rw [hbb] at hbv hhit
        rw [if_neg (by simp)] at hhit
        rw [rec_field_kind_beq_refines hhit, ← hbv]
        simp
      · rw [hbb] at hbv hhit
        rw [if_pos (by simp), Result.ok.injEq] at hhit
        rw [← hhit, ← hbv]
        simp
    have hsucc : ks.val.length - i.val = (ks.val.length - (i.val + 1)) + 1 := by omega
    simp only [hsucc, List.range'_succ, List.filter_cons, hgetd, ← hhitv]
    cases hitb : hit
    · rw [hitb] at hhitv h
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out hi2v o h, hi2v]
      simp
    · rw [hitb] at hhitv h
      rw [if_pos (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi3v : i3.val = i.val + 1 := absSz_add_one hi3
      have hi2v : i2.val = i.val := by
        simp only [lift, Result.ok.injEq] at hi2
        rw [← hi2, ConRon.Refine.ExprOps.usize_cast_u64_val]
      rw [ih i3 out1 hi3v o h, hi3v]
      simp only [absNatL, ConRon.Refine.vec_push_val hout1, List.map_append,
        List.map_cons, List.map_nil, absU, hi2v, List.append_assoc, List.cons_append,
        List.nil_append]
      simp

open Lockstep in
@[lockstep] theorem rec_idx_of_twin
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {i : Std.Usize}
    {out : alloc.vec.Vec Std.U64} :
    LSP (arena.inductives.native_parts.rec_idx_of ks i out) (fun o => TwinEq (absNatL out ++ ((recIdxOf (absKindL ks)).filter fun j => decide (absSz i ≤ j))) (absNatL o)) :=
  fun o h => (rec_idx_of_refines h).symm

/-! ## The record -/

/-- `native_parts_dup` is the identity on the abstraction. -/
theorem native_parts_dup_refines
    {p : arena.inductives.native_parts.NativeParts} {o}
    (hrun : arena.inductives.native_parts.native_parts_dup p = ok o) :
    absNativeParts o = absNativeParts p := by
  rw [arena.inductives.native_parts.native_parts_dup] at hrun
  obtain ⟨is, his, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [← Result.ok_injective hrun]
  have hk : absKindLL v = absKindLL p.kinds := by
    simpa [absKindLL, absKindLLFrom, alloc.vec.Vec.new,
      show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using kindss_copy_refines hv
  simp only [absNativeParts, inductive_shape_dup_refines his, hk]

open Lockstep in
@[lockstep] theorem native_parts_dup_twin
    {p : arena.inductives.native_parts.NativeParts} :
    LSP (arena.inductives.native_parts.native_parts_dup p) (fun o => TwinEq (absNativeParts p) (absNativeParts o)) :=
  fun o h => (native_parts_dup_refines h).symm

/-- `complete` ⊑ `NativeParts.complete` — the sum parts the former's run
returned with the recogniser's field kinds. -/
theorem complete_refines {p0 : arena.inductives.native_parts.NativeParts}
    {p1 : arena.inductives.sum_parts.InductiveShape} {o}
    (hrun : arena.inductives.native_parts.complete p0 p1 = ok o) :
    absNativeParts o =
      (absNativeParts p0).complete (absInductiveShape p1) := by
  rw [arena.inductives.native_parts.complete] at hrun
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [← Result.ok_injective hrun]
  have hk : absKindLL v = absKindLL p0.kinds := by
    simpa [absKindLL, absKindLLFrom, alloc.vec.Vec.new,
      show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using kindss_copy_refines hv
  simp only [absNativeParts, NativeParts.complete, hk]

open Lockstep in
@[lockstep] theorem complete_twin
    {p0 : arena.inductives.native_parts.NativeParts}
    {p1 : arena.inductives.sum_parts.InductiveShape} :
    LSP (arena.inductives.native_parts.complete p0 p1) (fun o => TwinEq ((absNativeParts p0).complete (absInductiveShape p1)) (absNativeParts o)) :=
  fun o h => (complete_refines h).symm

/-- `with_kinds` ⊑ `NativeParts.withKinds`. -/
theorem with_kinds_refines {p : arena.inductives.native_parts.NativeParts}
    {ks : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o} (hrun : arena.inductives.native_parts.with_kinds p ks = ok o) :
    absNativeParts o = (absNativeParts p).withKinds (absKindLL ks) := by
  rw [arena.inductives.native_parts.with_kinds] at hrun
  rw [← Result.ok_injective hrun]
  rfl

open Lockstep in
@[lockstep] theorem with_kinds_twin
    {p : arena.inductives.native_parts.NativeParts}
    {ks : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)} :
    LSP (arena.inductives.native_parts.with_kinds p ks) (fun o => TwinEq ((absNativeParts p).withKinds (absKindLL ks)) (absNativeParts o)) :=
  fun o h => (with_kinds_refines h).symm

/-! ## The generated recursor with inductive hypotheses -/

/-- `struct_rec_prefix_at` ⊑ `structRecPrefixAt`. -/
theorem struct_rec_prefix_at_refines {pers st lst} {n_p n n_f e : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_prefix_at pers st n_p n n_f e
      = ok o) :
    Sim₀ absEIdxL pers lst o
      (structRecPrefixAt (absU n_p) (absU n) (absU n_f) (absU e)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_rec_prefix_at_ls
    {pers st lst}
    {n_p n n_f e : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.native_parts.struct_rec_prefix_at pers st n_p n n_f e) lst
      (structRecPrefixAt (absU n_p) (absU n) (absU n_f) (absU e)) :=
  LS.ofSim₀ fun _ h => struct_rec_prefix_at_refines hrel hinv h

/-- `struct_idx_at` ⊑ `structIdxAt`. -/
theorem struct_idx_at_refines {pers st lst} {n_f ofs i l m : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_idx_at pers st n_f ofs i l m e
      = ok o) :
    Sim₀ absEIdx pers lst o
      (structIdxAt (absU n_f) (absU ofs) (absU i) (absU l) (absU m)
        (absEIdx e)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.struct_idx_at, structIdxAt]
  lockstep

open Lockstep in
@[lockstep] theorem struct_idx_at_ls
    {pers st lst}
    {n_f ofs i l m : Std.U64}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.native_parts.struct_idx_at pers st n_f ofs i l m e) lst
      (structIdxAt (absU n_f) (absU ofs) (absU i) (absU l) (absU m)
        (absEIdx e)) :=
  LS.ofSim₀ fun _ h => struct_idx_at_refines hrel hinv h

/-- `struct_tele_at` ⊑ `structTeleAt` from the cursor on, with the accumulated
binders in front. -/
theorem struct_tele_at_refines {pers st lst} {n_f ofs i l : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize}
    {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_tele_at pers st n_f ofs i l pw tele
      k out = ok o) :
    Sim₀ absBinderL pers lst o
      (do pure (absBinderL out ++
        (← structTeleAt (absU n_f) (absU ofs) (absU i) (absU l)
          (ConRon.Refine.absPropWhen pw) (absBinderLFrom tele k)))) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_tele_at_ls
    {pers st lst}
    {n_f ofs i l : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize}
    {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absBinderL a) (arena.inductives.native_parts.struct_tele_at pers st n_f ofs i l pw tele k out) lst
      (do pure (absBinderL out ++
        (← structTeleAt (absU n_f) (absU ofs) (absU i) (absU l)
          (ConRon.Refine.absPropWhen pw) (absBinderLFrom tele k)))) :=
  LS.ofSim₀ fun _ h => struct_tele_at_refines hrel hinv h

/-- `struct_tele_vars` ⊑ `structTeleVars`. -/
theorem struct_tele_vars_refines {pers st lst} {m : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_tele_vars pers st m = ok o) :
    Sim₀ absEIdxL pers lst o (structTeleVars (absU m)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.struct_tele_vars, structTeleVars]
  lockstep

open Lockstep in
@[lockstep] theorem struct_tele_vars_ls
    {pers st lst}
    {m : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.native_parts.struct_tele_vars pers st m) lst
                             (structTeleVars (absU m)) :=
  LS.ofSim₀ fun _ h => struct_tele_vars_refines hrel hinv h

/-- `mk_pis_of` ⊑ `Expr.mkPisOf` from the cursor on. -/
theorem mk_pis_of_refines {pers st lst}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize} {body : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.mk_pis_of pers st tele k body = ok o) :
    Sim₀ absEIdx pers lst o
      (mkPisOf (absBinderLFrom tele k) (absEIdx body)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  revert st lst hrel hinv
  simp only [absBinderLFrom]
  intro st lst hrel hinv
  refine ls_cursor tele (fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2))
    (fun l => mkPisOf l (absEIdx body))
    (fun st i => arena.inductives.native_parts.mk_pis_of pers st tele i body) ?_ ?_ k st lst hrel hinv
  · intro st lst i hn hrel hinv
    try simp only []
    rw [arena.inductives.native_parts.mk_pis_of.eq_def, mkPisOf]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    try simp only []
    rw [arena.inductives.native_parts.mk_pis_of.eq_def, mkPisOf]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
@[lockstep] theorem mk_pis_of_ls
    {pers st lst}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize}
    {body : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.native_parts.mk_pis_of pers st tele k body) lst
      (mkPisOf (absBinderLFrom tele k) (absEIdx body)) :=
  LS.ofSim₀ fun _ h => mk_pis_of_refines hrel hinv h

/-- `mk_lams_of` ⊑ `Expr.mkLamsOf` from the cursor on. -/
theorem mk_lams_of_refines {pers st lst}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize} {body : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.mk_lams_of pers st tele k body = ok o) :
    Sim₀ absEIdx pers lst o
      (mkLamsOf (absBinderLFrom tele k) (absEIdx body)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  revert st lst hrel hinv
  simp only [absBinderLFrom]
  intro st lst hrel hinv
  refine ls_cursor tele (fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2))
    (fun l => mkLamsOf l (absEIdx body))
    (fun st i => arena.inductives.native_parts.mk_lams_of pers st tele i body) ?_ ?_ k st lst hrel hinv
  · intro st lst i hn hrel hinv
    try simp only []
    rw [arena.inductives.native_parts.mk_lams_of.eq_def, mkLamsOf]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    try simp only []
    rw [arena.inductives.native_parts.mk_lams_of.eq_def, mkLamsOf]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
@[lockstep] theorem mk_lams_of_ls
    {pers st lst}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {k : Std.Usize}
    {body : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.native_parts.mk_lams_of pers st tele k body) lst
      (mkLamsOf (absBinderLFrom tele k) (absEIdx body)) :=
  LS.ofSim₀ fun _ h => mk_lams_of_refines hrel hinv h

/-- `struct_idx_list` ⊑ `structIhApp`'s `idx.mapM` from the cursor on, with the
accumulated expressions in front. -/
theorem struct_idx_list_refines {pers st lst} {n_f ofs i l m : Std.U64}
    {idx : alloc.vec.Vec arena.handle.EIdx} {k : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_idx_list pers st n_f ofs i l m idx k
      out = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← structIdxListSpec (absU n_f) (absU ofs) (absU i) (absU l) (absU m)
          (absEIdxLFrom idx k)))) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_idx_list_ls
    {pers st lst}
    {n_f ofs i l m : Std.U64}
    {idx : alloc.vec.Vec arena.handle.EIdx}
    {k : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.native_parts.struct_idx_list pers st n_f ofs i l m idx k out) lst
      (do pure (absEIdxL out ++
        (← structIdxListSpec (absU n_f) (absU ofs) (absU i) (absU l) (absU m)
          (absEIdxLFrom idx k)))) :=
  LS.ofSim₀ fun _ h => struct_idx_list_refines hrel hinv h

/-- `struct_ih_app` ⊑ `structIhApp`. -/
theorem struct_ih_app_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n n_f i : Std.U64}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {idx : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_ih_app pers st rec_c rlvls pw n_p n
      n_f i tele idx = ok o) :
    Sim₀ absEIdx pers lst o
      (structIhApp (absNIdx rec_c) (absLsIdx rlvls) (ConRon.Refine.absPropWhen pw)
        (absU n_p) (absU n) (absU n_f) (absU i) (absBinderL tele)
        (absEIdxL idx)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_ih_app_ls
    {pers st lst}
    {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx}
    {pw : kernel.prop_when.PropWhen}
    {n_p n n_f i : Std.U64}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {idx : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.native_parts.struct_ih_app pers st rec_c rlvls pw n_p n n_f i tele idx) lst
      (structIhApp (absNIdx rec_c) (absLsIdx rlvls) (ConRon.Refine.absPropWhen pw)
        (absU n_p) (absU n) (absU n_f) (absU i) (absBinderL tele)
        (absEIdxL idx)) :=
  LS.ofSim₀ fun _ h => struct_ih_app_refines hrel hinv h

/-- `struct_ih_list` ⊑ `structRuleBodyR`'s `recIdx.mapM` from the cursor on. -/
theorem struct_ih_list_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n n_f : Std.U64} {rec_idx : alloc.vec.Vec Std.U64}
    {cty : arena.handle.EIdx} {k : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_ih_list pers st rec_c rlvls pw n_p n
      n_f rec_idx cty k out = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← structIhListSpec (absNIdx rec_c) (absLsIdx rlvls)
          (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absU n_f)
          (absEIdx cty) (absNatLFrom rec_idx k)))) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_ih_list_ls
    {pers st lst}
    {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx}
    {pw : kernel.prop_when.PropWhen}
    {n_p n n_f : Std.U64}
    {rec_idx : alloc.vec.Vec Std.U64}
    {cty : arena.handle.EIdx}
    {k : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.native_parts.struct_ih_list pers st rec_c rlvls pw n_p n n_f rec_idx cty k out) lst
      (do pure (absEIdxL out ++
        (← structIhListSpec (absNIdx rec_c) (absLsIdx rlvls)
          (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absU n_f)
          (absEIdx cty) (absNatLFrom rec_idx k)))) :=
  LS.ofSim₀ fun _ h => struct_ih_list_refines hrel hinv h

/-- `struct_rule_body_r` ⊑ `structRuleBodyR`. -/
theorem struct_rule_body_r_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n n_f j : Std.U64} {rec_idx : alloc.vec.Vec Std.U64}
    {cty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rule_body_r pers st rec_c rlvls pw
      n_p n n_f j rec_idx cty = ok o) :
    Sim₀ absEIdx pers lst o
      (structRuleBodyR (absNIdx rec_c) (absLsIdx rlvls)
        (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absU n_f) (absU j)
        (absNatL rec_idx) (absEIdx cty)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_rule_body_r_ls
    {pers st lst}
    {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx}
    {pw : kernel.prop_when.PropWhen}
    {n_p n n_f j : Std.U64}
    {rec_idx : alloc.vec.Vec Std.U64}
    {cty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.native_parts.struct_rule_body_r pers st rec_c rlvls pw n_p n n_f j rec_idx cty) lst
      (structRuleBodyR (absNIdx rec_c) (absLsIdx rlvls)
        (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absU n_f) (absU j)
        (absNatL rec_idx) (absEIdx cty)) :=
  LS.ofSim₀ fun _ h => struct_rule_body_r_refines hrel hinv h

/-- `struct_ih_pis_at` ⊑ `structIhPis`' cons arm past its three reads. -/
theorem struct_ih_pis_at_refines {pers st lst} {n_f ofs n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen} {cty : arena.handle.EIdx}
    {is : alloc.vec.Vec Std.U64} {k : Std.Usize} {l : Std.U64}
    {body : arena.handle.EIdx}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {idx2 : alloc.vec.Vec arena.handle.EIdx} {motive : arena.handle.EIdx}
    {i m : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_ih_pis_at pers st n_f ofs n_p pw cty
      is k l body tele idx2 motive i m = ok o) :
    Sim₀ absEIdx pers lst o
      (structIhPisAtSpec (absU n_f) (absU ofs) (absU n_p)
        (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatLFrom is k |>.tail)
        (absU l) (absEIdx body) (absBinderL tele) (absEIdxL idx2) (absEIdx motive)
        (absU i) (absU m)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_ih_pis_at_ls
    {pers st lst}
    {n_f ofs n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {cty : arena.handle.EIdx}
    {is : alloc.vec.Vec Std.U64}
    {k : Std.Usize}
    {l : Std.U64}
    {body : arena.handle.EIdx}
    {tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {idx2 : alloc.vec.Vec arena.handle.EIdx}
    {motive : arena.handle.EIdx}
    {i m : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.native_parts.struct_ih_pis_at pers st n_f ofs n_p pw cty is k l body tele idx2 motive i m) lst
      (structIhPisAtSpec (absU n_f) (absU ofs) (absU n_p)
        (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatLFrom is k |>.tail)
        (absU l) (absEIdx body) (absBinderL tele) (absEIdxL idx2) (absEIdx motive)
        (absU i) (absU m)) :=
  LS.ofSim₀ fun _ h => struct_ih_pis_at_refines hrel hinv h

/-- `struct_ih_pis` ⊑ `structIhPis` from the cursor on. -/
theorem struct_ih_pis_refines {pers st lst} {n_f ofs n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen} {cty : arena.handle.EIdx}
    {is : alloc.vec.Vec Std.U64} {k : Std.Usize} {l : Std.U64}
    {body : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_ih_pis pers st n_f ofs n_p pw cty is
      k l body = ok o) :
    Sim₀ absEIdx pers lst o
      (structIhPis (absU n_f) (absU ofs) (absU n_p) (ConRon.Refine.absPropWhen pw)
        (absEIdx cty) (absNatLFrom is k) (absU l) (absEIdx body)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_ih_pis_ls
    {pers st lst}
    {n_f ofs n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {cty : arena.handle.EIdx}
    {is : alloc.vec.Vec Std.U64}
    {k : Std.Usize}
    {l : Std.U64}
    {body : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.native_parts.struct_ih_pis pers st n_f ofs n_p pw cty is k l body) lst
      (structIhPis (absU n_f) (absU ofs) (absU n_p) (ConRon.Refine.absPropWhen pw)
        (absEIdx cty) (absNatLFrom is k) (absU l) (absEIdx body)) :=
  LS.ofSim₀ fun _ h => struct_ih_pis_refines hrel hinv h

/-- `lift_list` ⊑ `structMinorTyR`'s `(rargs.drop nP).mapM` from the cursor
on. -/
theorem lift_list_refines {pers st lst} {amount c : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.lift_list pers st amount c xs i out
      = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← liftListSpec (absU amount) (absU c) (absEIdxLFrom xs i)))) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  revert st lst hrel hinv
  simp only [absEIdxLFrom]
  intro st lst hrel hinv
  refine ls_cursor_acc xs absEIdx
    (fun out l => do pure (absEIdxL out ++ (← liftListSpec (absU amount) (absU c) l)))
    (fun st i out => arena.inductives.native_parts.lift_list pers st amount c xs i out)
    ?_ ?_ i st lst out hrel hinv
  · intro st lst i out hn hrel hinv
    try simp only []
    rw [arena.inductives.native_parts.lift_list.eq_def, liftListSpec]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i out hb hrel hinv ih
    try simp only []
    rw [arena.inductives.native_parts.lift_list.eq_def, liftListSpec]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
@[lockstep] theorem lift_list_ls
    {pers st lst}
    {amount c : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.native_parts.lift_list pers st amount c xs i out) lst
      (do pure (absEIdxL out ++
        (← liftListSpec (absU amount) (absU c) (absEIdxLFrom xs i)))) :=
  LS.ofSim₀ fun _ h => lift_list_refines hrel hinv h

/-- `struct_minor_ty_close` ⊑ `structMinorTyR`'s closing stage. -/
theorem struct_minor_ty_close_refines {pers st lst} {n_f ofs n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen} {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64} {q2 concl0 : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_minor_ty_close pers st n_f ofs n_p
      pw cty rec_idx q2 concl0 = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structMinorTyCloseSpec (absU n_f) (absU ofs) (absU n_p)
        (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatL rec_idx)
        (absEIdx q2) (absEIdx concl0)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.struct_minor_ty_close, structMinorTyCloseSpec]
  lockstep

open Lockstep in
@[lockstep] theorem struct_minor_ty_close_ls
    {pers st lst}
    {n_f ofs n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64}
    {q2 concl0 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_minor_ty_close pers st n_f ofs n_p pw cty rec_idx q2 concl0) lst
      (structMinorTyCloseSpec (absU n_f) (absU ofs) (absU n_p)
        (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatL rec_idx)
        (absEIdx q2) (absEIdx concl0)) :=
  LS.ofSim₀ fun _ h => struct_minor_ty_close_refines hrel hinv h

/-- `struct_minor_ty_at` ⊑ `structMinorTyR`'s conclusion stage. -/
theorem struct_minor_ty_at_refines {pers st lst} {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f ofs : Std.U64}
    {pw : kernel.prop_when.PropWhen} {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64} {q2 r2 : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_minor_ty_at pers st c lps n_p n_f
      ofs pw cty rec_idx q2 r2 = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structMinorTyAtSpec (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f)
        (absU ofs) (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatL rec_idx)
        (absEIdx q2) (absEIdx r2)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_minor_ty_at_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f ofs : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64}
    {q2 r2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_minor_ty_at pers st c lps n_p n_f ofs pw cty rec_idx q2 r2) lst
      (structMinorTyAtSpec (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f)
        (absU ofs) (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatL rec_idx)
        (absEIdx q2) (absEIdx r2)) :=
  LS.ofSim₀ fun _ h => struct_minor_ty_at_refines hrel hinv h

/-- `struct_minor_ty_r` ⊑ `structMinorTyR`. -/
theorem struct_minor_ty_r_refines {pers st lst} {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f ofs : Std.U64}
    {pw : kernel.prop_when.PropWhen} {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_minor_ty_r pers st c lps n_p n_f ofs
      pw cty rec_idx = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structMinorTyR (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f) (absU ofs)
        (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatL rec_idx)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.struct_minor_ty_r, structMinorTyR]
  lockstep

open Lockstep in
@[lockstep] theorem struct_minor_ty_r_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f ofs : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_minor_ty_r pers st c lps n_p n_f ofs pw cty rec_idx) lst
      (structMinorTyR (absNIdx c) (absNIdxL lps) (absU n_p) (absU n_f) (absU ofs)
        (ConRon.Refine.absPropWhen pw) (absEIdx cty) (absNatL rec_idx)) :=
  LS.ofSim₀ fun _ h => struct_minor_ty_r_refines hrel hinv h

/-- `intern_binder` ⊑ the one node `structMinorsPisR` and `structMinorsLamsR`
differ in (finding 16). -/
theorem intern_binder_refines {pers st lst} {is_lam : Bool}
    {ty body : arena.handle.EIdx} {pw : kernel.prop_when.PropWhen} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.intern_binder pers st is_lam ty body pw
      = ok o) :
    Sim₀ absEIdx pers lst o
      (internBinderSpec is_lam (absEIdx ty) (absEIdx body)
        (ConRon.Refine.absPropWhen pw)) := by
  sorry

open Lockstep in
@[lockstep] theorem intern_binder_ls
    {pers st lst}
    {is_lam : Bool}
    {ty body : arena.handle.EIdx}
    {pw : kernel.prop_when.PropWhen}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.native_parts.intern_binder pers st is_lam ty body pw) lst
      (internBinderSpec is_lam (absEIdx ty) (absEIdx body)
        (ConRon.Refine.absPropWhen pw)) :=
  LS.ofSim₀ fun _ h => intern_binder_refines hrel hinv h

/-- `struct_minors_pis_r` ⊑ the two twins as one recursion at `isLam`
(finding 16), from the cursor on. -/
theorem struct_minors_pis_r_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {k : Std.Usize} {ofs : Std.U64} {body : arena.handle.EIdx} {is_lam : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_minors_pis_r pers st lps n_p pw
      ctors k ofs body is_lam = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structMinorsRSpec (absNIdxL lps) (absU n_p) (ConRon.Refine.absPropWhen pw)
        (absCtors4LFrom ctors k) (absU ofs) (absEIdx body) is_lam) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_minors_pis_r_ls
    {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {k : Std.Usize}
    {ofs : Std.U64}
    {body : arena.handle.EIdx}
    {is_lam : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_minors_pis_r pers st lps n_p pw ctors k ofs body is_lam) lst
      (structMinorsRSpec (absNIdxL lps) (absU n_p) (ConRon.Refine.absPropWhen pw)
        (absCtors4LFrom ctors k) (absU ofs) (absEIdx body) is_lam) :=
  LS.ofSim₀ fun _ h => struct_minors_pis_r_refines hrel hinv h

/-- `struct_minors_lams_r` ⊑ `structMinorsLamsR` from the cursor on — the
delegation of finding 16 at the `λ` flag. -/
theorem struct_minors_lams_r_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {k : Std.Usize} {ofs : Std.U64} {body : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_minors_lams_r pers st lps n_p pw
      ctors k ofs body = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structMinorsLamsR (absNIdxL lps) (absU n_p) (ConRon.Refine.absPropWhen pw)
        (absCtors4LFrom ctors k) (absU ofs) (absEIdx body)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_minors_lams_r_ls
    {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {k : Std.Usize}
    {ofs : Std.U64}
    {body : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_minors_lams_r pers st lps n_p pw ctors k ofs body) lst
      (structMinorsLamsR (absNIdxL lps) (absU n_p) (ConRon.Refine.absPropWhen pw)
        (absCtors4LFrom ctors k) (absU ofs) (absEIdx body)) :=
  LS.ofSim₀ fun _ h => struct_minors_lams_r_refines hrel hinv h

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

open Lockstep in
/-- `u64_vec_dup_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem u64_vec_dup_twin0
    {xs : alloc.vec.Vec Std.U64} :
    LSP (arena.inductives.native_parts.u64_vec_dup xs 0#usize (alloc.vec.Vec.new Std.U64)) (fun o => TwinEq (absNatL xs) (absNatL o)) := by
  intro o h
  have h' := (u64_vec_dup_refines h).symm
  simpa [Lockstep.TwinEq, absNatLFrom, absNatL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem u64_vec_dup_twin
    {xs : alloc.vec.Vec Std.U64}
    {i : Std.Usize}
    {out : alloc.vec.Vec Std.U64} :
    LSP (arena.inductives.native_parts.u64_vec_dup xs i out) (fun o => TwinEq (absNatL out ++ absNatLFrom xs i) (absNatL o)) :=
  fun o h => (u64_vec_dup_refines h).symm

/-! ## The generated recursor type and rules -/

/-- `struct_rec_ty_close` ⊑ `structRecTyR`'s closing stage. -/
theorem struct_rec_ty_close_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {pw : kernel.prop_when.PropWhen} {n : Std.U64}
    {q2 motive_ty major_body : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_ty_close pers st lps n_p n_idx
      tty ctors pw n q2 motive_ty major_body = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structRecTyCloseSpec (absNIdxL lps) (absU n_p) (absU n_idx) (absEIdx tty)
        (absCtors4L ctors) (ConRon.Refine.absPropWhen pw) (absU n) (absEIdx q2)
        (absEIdx motive_ty) (absEIdx major_body)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_rec_ty_close_ls
    {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {pw : kernel.prop_when.PropWhen}
    {n : Std.U64}
    {q2 motive_ty major_body : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_rec_ty_close pers st lps n_p n_idx tty ctors pw n q2 motive_ty major_body) lst
      (structRecTyCloseSpec (absNIdxL lps) (absU n_p) (absU n_idx) (absEIdx tty)
        (absCtors4L ctors) (ConRon.Refine.absPropWhen pw) (absU n) (absEIdx q2)
        (absEIdx motive_ty) (absEIdx major_body)) :=
  LS.ofSim₀ fun _ h => struct_rec_ty_close_refines hrel hinv h

/-- `struct_rec_ty_at` ⊑ `structRecTyR`'s major-premise stage. -/
theorem struct_rec_ty_at_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {pw : kernel.prop_when.PropWhen} {n : Std.U64}
    {q2 motive_ty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_ty_at pers st t lps n_p n_idx
      tty ctors pw n q2 motive_ty = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structRecTyAtSpec (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absEIdx tty) (absCtors4L ctors) (ConRon.Refine.absPropWhen pw) (absU n)
        (absEIdx q2) (absEIdx motive_ty)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_rec_ty_at_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {pw : kernel.prop_when.PropWhen}
    {n : Std.U64}
    {q2 motive_ty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_rec_ty_at pers st t lps n_p n_idx tty ctors pw n q2 motive_ty) lst
      (structRecTyAtSpec (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absEIdx tty) (absCtors4L ctors) (ConRon.Refine.absPropWhen pw) (absU n)
        (absEIdx q2) (absEIdx motive_ty)) :=
  LS.ofSim₀ fun _ h => struct_rec_ty_at_refines hrel hinv h

/-- `struct_rec_ty_r` ⊑ `structRecTyR` — **the generated recursor type at a
recursive block**. -/
theorem struct_rec_ty_r_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p n_idx : Std.U64} {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_ty_r pers st t lps elim large
      n_p n_idx tty ctors = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structRecTyR (absNIdx t) (absNIdxL lps) (absNIdx elim) large (absU n_p)
        (absU n_idx) (absEIdx tty) (absCtors4L ctors)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_rec_ty_r_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {elim : arena.handle.NIdx}
    {large : Bool}
    {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_rec_ty_r pers st t lps elim large n_p n_idx tty ctors) lst
      (structRecTyR (absNIdx t) (absNIdxL lps) (absNIdx elim) large (absU n_p)
        (absU n_idx) (absEIdx tty) (absCtors4L ctors)) :=
  LS.ofSim₀ fun _ h => struct_rec_ty_r_refines hrel hinv h

/-- `struct_rec_rhs_close` ⊑ `structRecRhsR`'s closing stage. -/
theorem struct_rec_rhs_close_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {pw : kernel.prop_when.PropWhen} {n n_f : Std.U64}
    {q2 body motive_ty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_rhs_close pers st lps n_p tty
      ctors pw n n_f q2 body motive_ty = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structRecRhsCloseSpec (absNIdxL lps) (absU n_p) (absEIdx tty)
        (absCtors4L ctors) (ConRon.Refine.absPropWhen pw) (absU n) (absU n_f)
        (absEIdx q2) (absEIdx body) (absEIdx motive_ty)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_rec_rhs_close_ls
    {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {pw : kernel.prop_when.PropWhen}
    {n n_f : Std.U64}
    {q2 body motive_ty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_rec_rhs_close pers st lps n_p tty ctors pw n n_f q2 body motive_ty) lst
      (structRecRhsCloseSpec (absNIdxL lps) (absU n_p) (absEIdx tty)
        (absCtors4L ctors) (ConRon.Refine.absPropWhen pw) (absU n) (absU n_f)
        (absEIdx q2) (absEIdx body) (absEIdx motive_ty)) :=
  LS.ofSim₀ fun _ h => struct_rec_rhs_close_refines hrel hinv h

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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_rhs_at pers st t lps n_p n_idx
      tty ctors rec_c rlvls j pw n n_f cty rec_idx l = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structRecRhsAtSpec (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absEIdx tty) (absCtors4L ctors) (absNIdx rec_c) (absLsIdx rlvls) (absU j)
        (ConRon.Refine.absPropWhen pw) (absU n) (absU n_f) (absEIdx cty)
        (absNatL rec_idx) (absLIdx l)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.struct_rec_rhs_at, structRecRhsAtSpec]
  lockstep

open Lockstep in
@[lockstep] theorem struct_rec_rhs_at_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx}
    {j : Std.U64}
    {pw : kernel.prop_when.PropWhen}
    {n n_f : Std.U64}
    {cty : arena.handle.EIdx}
    {rec_idx : alloc.vec.Vec Std.U64}
    {l : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_rec_rhs_at pers st t lps n_p n_idx tty ctors rec_c rlvls j pw n n_f cty rec_idx l) lst
      (structRecRhsAtSpec (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absEIdx tty) (absCtors4L ctors) (absNIdx rec_c) (absLsIdx rlvls) (absU j)
        (ConRon.Refine.absPropWhen pw) (absU n) (absU n_f) (absEIdx cty)
        (absNatL rec_idx) (absLIdx l)) :=
  LS.ofSim₀ fun _ h => struct_rec_rhs_at_refines hrel hinv h

/-- `struct_rec_rhs_r` ⊑ `structRecRhsR` — **the generated rule** for
constructor `j` at a recursive block. -/
theorem struct_rec_rhs_r_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p n_idx : Std.U64} {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {rec_c : arena.handle.NIdx} {rlvls : arena.handle.LsIdx} {j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.struct_rec_rhs_r pers st t lps elim large
      n_p n_idx tty ctors rec_c rlvls j = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (structRecRhsR (absNIdx t) (absNIdxL lps) (absNIdx elim) large (absU n_p)
        (absU n_idx) (absEIdx tty) (absCtors4L ctors) (absNIdx rec_c)
        (absLsIdx rlvls) (absU j)) := by
  sorry

open Lockstep in
@[lockstep] theorem struct_rec_rhs_r_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {elim : arena.handle.NIdx}
    {large : Bool}
    {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx}
    {j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absEIdx) a) (arena.inductives.native_parts.struct_rec_rhs_r pers st t lps elim large n_p n_idx tty ctors rec_c rlvls j) lst
      (structRecRhsR (absNIdx t) (absNIdxL lps) (absNIdx elim) large (absU n_p)
        (absU n_idx) (absEIdx tty) (absCtors4L ctors) (absNIdx rec_c)
        (absLsIdx rlvls) (absU j)) :=
  LS.ofSim₀ fun _ h => struct_rec_rhs_r_refines hrel hinv h

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
  refine cursor_induction (fun i : Std.Usize => i.val)
    (min ctors_a.val.length kinds.val.length)
    (fun i out => ∀ o,
      arena.inductives.native_parts.native_ctors4 ctors_a kinds i out = ok o →
      absCtors4L o = absCtors4L out ++
        nativeCtors4 (absCtorsLFrom ctors_a i) (absKindLLFrom kinds i))
    ?_ ?_ i out o hrun
  · intro i out hn o h
    rw [arena.inductives.native_parts.native_ctors4.eq_def] at h
    by_cases hc : ctors_a.val.length ≤ i.val
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ctors_a by scalar_tac), Result.ok.injEq] at h
      obtain rfl := h
      simp [nativeCtors4, absCtorsLFrom, List.drop_eq_nil_of_le hc]
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ctors_a by scalar_tac)] at h
      have hk : kinds.val.length ≤ i.val := by omega
      rw [if_pos (show i ≥ alloc.vec.Vec.len kinds by scalar_tac), Result.ok.injEq] at h
      obtain rfl := h
      simp [nativeCtors4, absKindLLFrom, List.drop_eq_nil_of_le hk]
  · intro i out hi ih o h
    have hca : i.val < ctors_a.val.length := by omega
    have hki : i.val < kinds.val.length := by omega
    rw [arena.inductives.native_parts.native_ctors4.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ctors_a by scalar_tac)] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len kinds by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨iv, nf⟩ := q
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi4v : i4.val = i.val + 1 := absSz_add_one hi4
    obtain ⟨hqb, hqv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hq)
    obtain ⟨hvb, hvv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hv)
    have hrec : absNatL v1 = recIdxOf (absKindL v) := by
      rw [rec_idx_of_refines hv1]
      simp [absNatL, alloc.vec.Vec.new, absSz,
        show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
    rw [ih i4 out1 hi4v o h]
    simp only [absNatL, absKindL] at hrec
    simp [absCtorsLFrom, absKindLLFrom, hi4v, nativeCtors4,
      List.drop_eq_getElem_cons hqb, List.drop_eq_getElem_cons hvb, hqv, hvv,
      absCtors4L, ConRon.Refine.vec_push_val hout1,
      absIConstantVal, dupId_nidx _ _ hn, dupId_eidx _ _ he, absNatL]
    exact hrec

open Lockstep in
@[lockstep] theorem native_ctors4_twin
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))} :
    LSP (arena.inductives.native_parts.native_ctors4 ctors_a kinds i out) (fun o => TwinEq (absCtors4L out ++ nativeCtors4 (absCtorsLFrom ctors_a i) (absKindLLFrom kinds i)) (absCtors4L o)) :=
  fun o h => (native_ctors4_refines h).symm

/-! ## The stream's rules against the generated ones -/

/-- `binders_reset_beq_from` ⊑ `nativeRulePrefixOk`'s binder comparison from
the `i`-th on. -/
theorem binders_reset_beq_from_refines {pers st lst}
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 n i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.binders_reset_beq_from pers st bs1 bs2 o1
      o2 n i = ok o) :
    Sim₀ id pers lst o
      (bindersResetBeqSpec (absBinderL bs1) (absBinderL bs2) (absU o1) (absU o2)
        (absU n - absU i) (absU i)) := by
  sorry

open Lockstep in
@[lockstep] theorem binders_reset_beq_from_ls
    {pers st lst}
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 n i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_parts.binders_reset_beq_from pers st bs1 bs2 o1 o2 n i) lst
      (bindersResetBeqSpec (absBinderL bs1) (absBinderL bs2) (absU o1) (absU o2)
        (absU n - absU i) (absU i)) :=
  LS.ofSim₀ fun _ h => binders_reset_beq_from_refines hrel hinv h

/-- `binders_reset_beq` ⊑ the same at `i = 0`. -/
theorem binders_reset_beq_refines {pers st lst}
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 n : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.binders_reset_beq pers st bs1 bs2 o1 o2 n
      = ok o) :
    Sim₀ id pers lst o
      (bindersResetBeqSpec (absBinderL bs1) (absBinderL bs2) (absU o1) (absU o2)
        (absU n) 0) := by
  sorry

open Lockstep in
@[lockstep] theorem binders_reset_beq_ls
    {pers st lst}
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 n : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_parts.binders_reset_beq pers st bs1 bs2 o1 o2 n) lst
      (bindersResetBeqSpec (absBinderL bs1) (absBinderL bs2) (absU o1) (absU o2)
        (absU n) 0) :=
  LS.ofSim₀ fun _ h => binders_reset_beq_refines hrel hinv h

/-- `native_rule_fields_ok` ⊑ `nativeRulePrefixOk`'s field comparison. -/
theorem native_rule_fields_ok_refines {pers st lst} {n_p n j n_f : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {mty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_rule_fields_ok pers st n_p n j n_f
      rbs mty = ok o) :
    Sim₀ id pers lst o
      (nativeRuleFieldsOkSpec (absU n_p) (absU n) (absU j) (absU n_f)
        (absBinderL rbs) (absEIdx mty)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.native_rule_fields_ok, nativeRuleFieldsOkSpec]
  lockstep

open Lockstep in
@[lockstep] theorem native_rule_fields_ok_ls
    {pers st lst}
    {n_p n j n_f : Std.U64}
    {rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {mty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_parts.native_rule_fields_ok pers st n_p n j n_f rbs mty) lst
      (nativeRuleFieldsOkSpec (absU n_p) (absU n) (absU j) (absU n_f)
        (absBinderL rbs) (absEIdx mty)) :=
  LS.ofSim₀ fun _ h => native_rule_fields_ok_refines hrel hinv h

/-- `native_rule_prefix_ok` ⊑ `nativeRulePrefixOk` — **the rule's `λ` prefix
against the stream's own recursor type** (con-leche's task #271). -/
theorem native_rule_prefix_ok_refines {pers st lst} {rec_ty : arena.handle.EIdx}
    {n_p n j n_f : Std.U64} {rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_rule_prefix_ok pers st rec_ty n_p n
      j n_f rhs = ok o) :
    Sim₀ id pers lst o
      (nativeRulePrefixOk (absEIdx rec_ty) (absU n_p) (absU n) (absU j) (absU n_f)
        (absEIdx rhs)) := by
  sorry

open Lockstep in
@[lockstep] theorem native_rule_prefix_ok_ls
    {pers st lst}
    {rec_ty : arena.handle.EIdx}
    {n_p n j n_f : Std.U64}
    {rhs : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_parts.native_rule_prefix_ok pers st rec_ty n_p n j n_f rhs) lst
      (nativeRulePrefixOk (absEIdx rec_ty) (absU n_p) (absU n) (absU j) (absU n_f)
        (absEIdx rhs)) :=
  LS.ofSim₀ fun _ h => native_rule_prefix_ok_refines hrel hinv h

/-- `native_rule_body_ok` ⊑ `nativeRulesOk`'s per-rule body test. -/
theorem native_rule_body_ok_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n n_f j : Std.U64} {rec_idx : alloc.vec.Vec Std.U64}
    {cty rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_rule_body_ok pers st rec_c rlvls pw
      n_p n n_f j rec_idx cty rhs = ok o) :
    Sim₀ id pers lst o
      (nativeRuleBodyOkSpec (absNIdx rec_c) (absLsIdx rlvls)
        (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absU n_f) (absU j)
        (absNatL rec_idx) (absEIdx cty) (absEIdx rhs)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.native_rule_body_ok, nativeRuleBodyOkSpec]
  lockstep

open Lockstep in
@[lockstep] theorem native_rule_body_ok_ls
    {pers st lst}
    {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx}
    {pw : kernel.prop_when.PropWhen}
    {n_p n n_f j : Std.U64}
    {rec_idx : alloc.vec.Vec Std.U64}
    {cty rhs : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_parts.native_rule_body_ok pers st rec_c rlvls pw n_p n n_f j rec_idx cty rhs) lst
      (nativeRuleBodyOkSpec (absNIdx rec_c) (absLsIdx rlvls)
        (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absU n_f) (absU j)
        (absNatL rec_idx) (absEIdx cty) (absEIdx rhs)) :=
  LS.ofSim₀ fun _ h => native_rule_body_ok_refines hrel hinv h

/-- `native_rules_ok_from` ⊑ `nativeRulesOk`'s `(List.range n).allM` from rule
`j` on. -/
theorem native_rules_ok_from_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n : Std.U64} {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {rhss : alloc.vec.Vec arena.handle.EIdx} {rec_ty : arena.handle.EIdx}
    {j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_rules_ok_from pers st rec_c rlvls pw
      n_p n cs kinds rhss rec_ty j = ok o) :
    Sim₀ id pers lst o
      (nativeRulesOkFromSpec (absNIdx rec_c) (absLsIdx rlvls)
        (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absCtorsL cs)
        (absKindLL kinds) (absEIdxL rhss) (absEIdx rec_ty) (absU n - absU j)
        (absU j)) := by
  sorry

open Lockstep in
@[lockstep] theorem native_rules_ok_from_ls
    {pers st lst}
    {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx}
    {pw : kernel.prop_when.PropWhen}
    {n_p n : Std.U64}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {rhss : alloc.vec.Vec arena.handle.EIdx}
    {rec_ty : arena.handle.EIdx}
    {j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_parts.native_rules_ok_from pers st rec_c rlvls pw n_p n cs kinds rhss rec_ty j) lst
      (nativeRulesOkFromSpec (absNIdx rec_c) (absLsIdx rlvls)
        (ConRon.Refine.absPropWhen pw) (absU n_p) (absU n) (absCtorsL cs)
        (absKindLL kinds) (absEIdxL rhss) (absEIdx rec_ty) (absU n - absU j)
        (absU j)) :=
  LS.ofSim₀ fun _ h => native_rules_ok_from_refines hrel hinv h

/-- `native_rules_ok` ⊑ `nativeRulesOk` — **the stream's rules against the
generated ones**, at install. -/
theorem native_rules_ok_refines {pers st lst} {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx} {pw : kernel.prop_when.PropWhen}
    {n_p n : Std.U64} {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {rhss : alloc.vec.Vec arena.handle.EIdx} {rec_ty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_rules_ok pers st rec_c rlvls pw n_p
      n cs kinds rhss rec_ty = ok o) :
    Sim₀ id pers lst o
      (nativeRulesOk (absNIdx rec_c) (absLsIdx rlvls) (ConRon.Refine.absPropWhen pw)
        (absU n_p) (absU n) (absCtorsL cs) (absKindLL kinds) (absEIdxL rhss)
        (absEIdx rec_ty)) := by
  sorry

open Lockstep in
@[lockstep] theorem native_rules_ok_ls
    {pers st lst}
    {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx}
    {pw : kernel.prop_when.PropWhen}
    {n_p n : Std.U64}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {rhss : alloc.vec.Vec arena.handle.EIdx}
    {rec_ty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_parts.native_rules_ok pers st rec_c rlvls pw n_p n cs kinds rhss rec_ty) lst
      (nativeRulesOk (absNIdx rec_c) (absLsIdx rlvls) (ConRon.Refine.absPropWhen pw)
        (absU n_p) (absU n) (absCtorsL cs) (absKindLL kinds) (absEIdxL rhss)
        (absEIdx rec_ty)) :=
  LS.ofSim₀ fun _ h => native_rules_ok_refines hrel hinv h

/-! ## Recognition -/

/-- `nativeCounts?` at a constructor COUNT: the twin reads its list only
through `cs.length` (finding 17), so the tier states the port's
`native_counts` against this normal form, and `nativeCounts?_len` (a
`lockstep_simp` rewrite of the twin side) brings every caller's twin to it —
the count is then a side goal (`absU n = cs.length`) instead of a list the
tactic would have to guess. -/
def nativeCountsLen (nPd : Nat) (cvT : IConstantVal) (n : Nat) (mI rP : Nat) :
    AM (Option (Nat × Nat)) :=
  nativeCounts? nPd cvT (List.replicate n default) mI rP

@[lockstep_simp] theorem nativeCounts?_len (nPd : Nat) (cvT : IConstantVal)
    (cs : List (IConstantVal × Nat × Nat)) (mI rP : Nat) :
    nativeCounts? nPd cvT cs mI rP = nativeCountsLen nPd cvT cs.length mI rP := by
  simp only [nativeCountsLen, nativeCounts?, List.length_replicate]

/-- `native_counts` ⊑ `nativeCounts?` — **finding 17**: the port takes the
constructor count where the twin takes the list; the statement is at the
count (`nativeCountsLen`). -/
theorem native_counts_refines {pers st lst} {n_pd : Std.U64}
    {cv_t : arena.env.IConstantVal} {n_ctors m_i r_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_counts pers st n_pd cv_t n_ctors m_i
      r_p = ok o) :
    Sim₀ (Option.map fun p => (absU p.1, absU p.2)) pers lst o
      (nativeCountsLen (absU n_pd) (absIConstantVal cv_t) (absU n_ctors) (absU m_i)
        (absU r_p)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_parts.native_counts, nativeCountsLen, nativeCounts?]
  lockstep

open Lockstep in
@[lockstep] theorem native_counts_ls
    {pers st lst}
    {n_pd : Std.U64}
    {cv_t : arena.env.IConstantVal}
    {n_ctors m_i r_p : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map fun p => (absU p.1, absU p.2)) a) (arena.inductives.native_parts.native_counts pers st n_pd cv_t n_ctors m_i r_p) lst
      (nativeCountsLen (absU n_pd) (absIConstantVal cv_t) (absU n_ctors) (absU m_i)
        (absU r_p)) :=
  LS.ofSim₀ fun _ h => native_counts_refines hrel hinv h

/-- `rulesPinOkSpec` is `nativeRecPinOk`'s `(List.range …).all` from rule `j`
on, read over `List.range'`: a fact about the spec alone. -/
theorem rulesPinOkSpec_eq_all (rules : List IRecRule)
    (cs : List (IConstantVal × Nat × Nat)) :
    ∀ m j, rulesPinOkSpec rules cs m j = (List.range' j m).all fun j =>
      match rules[j]?, cs[j]? with
      | some rule, some (cvC, _, nF) => rule.ctor == cvC.name && rule.nfields == nF
      | _, _ => false := by
  intro m
  induction m with
  | zero => intro j; simp [rulesPinOkSpec]
  | succ m ih =>
    intro j
    simp only [rulesPinOkSpec, List.range'_succ, List.all_cons, ih (j + 1)]
    rcases rules[j]? with _ | rule <;> rcases cs[j]? with _ | ⟨cvC, a, nF⟩ <;>
      simp [Bool.and_assoc]

/-- `rules_pin_ok` ⊑ `nativeRecPinOk`'s `(List.range …).all` from rule `j`
on. -/
theorem rules_pin_ok_refines {rules : alloc.vec.Vec arena.env.IRecRule}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {n j : Std.U64} {o}
    (hrun : arena.inductives.native_parts.rules_pin_ok rules cs n j = ok o) :
    o = rulesPinOkSpec (rules.val.map absIRecRule) (absCtors3L cs)
      (absU n - absU j) (absU j) := by
  -- task #97-P5-Usize: the three bounds are compared in `u64`, so every
  -- `j as usize` under them is exact (round 3 §R3.5's finding, fixed in the
  -- Rust rather than carried as a hypothesis).
  suffices H : ∀ (m : Nat) (j : Std.U64) (o : Bool), n.val - j.val = m →
      arena.inductives.native_parts.rules_pin_ok rules cs n j = ok o →
      o = rulesPinOkSpec (rules.val.map absIRecRule) (absCtors3L cs) m j.val from
    H _ j o rfl hrun
  intro m
  induction m with
  | zero =>
    intro j o hm h
    rw [arena.inductives.native_parts.rules_pin_ok.eq_def] at h
    rw [if_pos (show j ≥ n by scalar_tac)] at h
    obtain rfl := Result.ok_injective h
    simp [rulesPinOkSpec]
  | succ m ih =>
    intro j o hm h
    rw [arena.inductives.native_parts.rules_pin_ok.eq_def] at h
    rw [if_neg (show ¬ j ≥ n by scalar_tac)] at h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp only [lift, Result.ok.injEq] at hi1
    have hi1v : i1.val = rules.val.length := by
      rw [← hi1, ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
    by_cases hr : j ≥ i1
    · rw [if_pos hr] at h
      obtain rfl := Result.ok_injective h
      have hge : rules.val.length ≤ j.val := by scalar_tac
      simp [rulesPinOkSpec, List.getElem?_eq_none (by simpa using hge)]
    rw [if_neg hr] at h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp only [lift, Result.ok.injEq] at hi3
    have hi3v : i3.val = cs.val.length := by
      rw [← hi3, ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
    by_cases hc : j ≥ i3
    · rw [if_pos hc] at h
      obtain rfl := Result.ok_injective h
      have hge : cs.val.length ≤ j.val := by scalar_tac
      simp only [rulesPinOkSpec, absCtors3L]
      rcases (rules.val.map absIRecRule)[j.val]? with _ | _ <;>
        simp [List.getElem?_eq_none (by simpa using hge)]
    rw [if_neg hc] at h
    have hjr : j.val < rules.val.length := by scalar_tac
    have hjc : j.val < cs.val.length := by scalar_tac
    have hcast : ∀ i4 : Std.Usize, lift (UScalar.cast .Usize j) = ok i4 →
        i4.val = j.val := by
      intro i4 hi4
      simp only [lift, Result.ok.injEq] at hi4
      rw [← hi4]
      exact ConRon.Refine.ExprOps.u64_cast_usize_val
        (le_trans (Nat.le_of_lt hjr) rules.property)
    obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ir, hir, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i5, hi5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨iv, a, b⟩, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hxr := vec_index_some hir
    have hxc := vec_index_some hiv
    rw [hcast i4 hi4] at hxr
    rw [hcast i5 hi5] at hxc
    obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbbv := nidx_eq2_abs hbb
    have hsr : (rules.val.map absIRecRule)[j.val]? = some (absIRecRule ir) := by
      simp [hxr]
    have hsc : (absCtors3L cs)[j.val]? = some (absIConstantVal iv, absU a, absU b) := by
      simp [absCtors3L, hxc]
    simp only [rulesPinOkSpec, hsr, hsc]
    cases hbbt : bb
    · rw [hbbt] at hbbv h
      simp only [Bool.false_eq_true, if_false] at h
      obtain rfl := Result.ok_injective h
      simp [absIRecRule, absIConstantVal, ← hbbv]
    rw [hbbt] at hbbv h
    simp only [if_true] at h
    obtain ⟨i6, hi6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ir1, hir1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i7, hi7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨iv', a', b'⟩, hiv', h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hxr1 := vec_index_some hir1
    have hxc1 := vec_index_some hiv'
    rw [hcast i6 hi6, hxr] at hxr1
    rw [hcast i7 hi7, hxc] at hxc1
    obtain rfl := (Option.some_inj.mp hxr1)
    obtain ⟨rfl, rfl, rfl⟩ : iv = iv' ∧ a = a' ∧ b = b' := by
      have := Option.some_inj.mp hxc1; simp_all
    have hctor : (absIRecRule ir).ctor = (absIConstantVal iv).name := by
      simpa [absIRecRule, absIConstantVal] using hbbv.symm
    replace h : (if ir.nfields = b then (do
        let i9 ← j + 1#u64
        arena.inductives.native_parts.rules_pin_ok rules cs n i9) else ok false) = ok o := h
    by_cases hnf : ir.nfields = b
    · rw [if_pos hnf] at h
      obtain ⟨i9, hi9, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi9v : i9.val = j.val + 1 := ConRon.Refine.Nat.uadd_val hi9
      have hrec := ih i9 o (by omega) h
      rw [hi9v] at hrec
      have hctor2 : absNIdx ir.ctor = (absIConstantVal iv).name := by
        simpa [absIRecRule] using hctor
      simp [absIRecRule, absU, hnf, hrec, hctor2]
    · rw [if_neg hnf] at h
      obtain rfl := Result.ok_injective h
      have hnf' : ir.nfields.val ≠ b.val := fun e => hnf (by scalar_tac)
      simp [absIRecRule, absU, hnf']

open Lockstep in
@[lockstep] theorem rules_pin_ok_twin
    {rules : alloc.vec.Vec arena.env.IRecRule}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {n j : Std.U64} :
    LSP (arena.inductives.native_parts.rules_pin_ok rules cs n j) (fun o => TwinEq (rulesPinOkSpec (rules.val.map absIRecRule) (absCtors3L cs) (absU n - absU j) (absU j)) (o)) :=
  fun o h => (rules_pin_ok_refines h).symm

-- `i_constant_infos_dup_from_abs` moved down to `Refine2/Dup.lean` (task
-- #97-P5-Front round 2).

/-- `native_rec_pin_ok` ⊑ `nativeRecPinOk` — **the recursor record's structural
pin** (con-leche's task #220).  Pure on both sides: tags, names and counts
only. -/
theorem native_rec_pin_ok_refines
    {p : arena.inductives.sum_parts.InductiveShape}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrun : arena.inductives.native_parts.native_rec_pin_ok p block = ok o) :
    o = nativeRecPinOk (absInductiveShape p) (absICIL block) := by
  rw [arena.inductives.native_parts.native_rec_pin_ok] at hrun
  by_cases h0 : alloc.vec.Vec.len block = 0#usize
  · rw [if_pos h0] at hrun
    obtain rfl := Result.ok_injective hrun
    have hnil : block.val = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
    simp [nativeRecPinOk, absICIL, hnil]
  rw [if_neg h0] at hrun
  obtain ⟨ii, hii, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hx := vec_index_some hii
  have habs : absICIL block
      = absIConstantInfo ii :: (block.val.drop 1).map absIConstantInfo := by
    simp only [absICIL]
    rcases hb : block.val with _ | ⟨y, ys⟩
    · simp [hb] at hx
    · simp only [hb, show ((0#usize : Std.Usize)).val = 0 by scalar_tac,
        List.getElem?_cons_zero, Option.some.injEq] at hx
      simp [hx]
  rw [habs]
  cases ii with
  | IndInfo a b =>
    simp only [] at hrun
    obtain ⟨rest, hrest, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hr := i_constant_infos_dup_from_abs hrest
    obtain ⟨os, hos, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hs := sum_split_refines hos
    have hrest' : absICIL rest = (block.val.drop 1).map absIConstantInfo := by
      simpa [absICIL, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
        show ((1#usize : Std.Usize)).val = 1 by scalar_tac] using hr
    rw [hrest'] at hs
    simp only [nativeRecPinOk, absIConstantInfo, ← hs]
    cases os with
    | none =>
      obtain rfl := Result.ok_injective hrun
      simp
    | some q =>
      obtain ⟨v1, x, i3, i4, v2⟩ := q
      simp only [Option.map_some]
      obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      simp only [lift, Result.ok.injEq] at hn
      have hnv : n.val = p.ctors.val.length := by
        rw [← hn, ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      obtain ⟨i5, hi5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi5v : i5.val = p.n_p.val + 1 := ConRon.Refine.Nat.uadd_val hi5
      obtain ⟨i6, hi6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi6v : i6.val = i5.val + n.val := ConRon.Refine.Nat.uadd_val hi6
      have hlen : (absInductiveShape p).ctors.length = p.ctors.val.length := by
        simp [absInductiveShape, absCtorsL]
      simp only [hlen]
      by_cases hc1 : i4 = i6
      · rw [if_pos hc1] at hrun
        have hc1' : absU i4 = absU p.n_p + 1 + p.ctors.val.length := by
          simp only [absU]; rw [hc1]; omega
        obtain ⟨i7, hi7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi7v : i7.val = i5.val + n.val := ConRon.Refine.Nat.uadd_val hi7
        obtain ⟨i8, hi8, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi8v : i8.val = i7.val + p.n_idx.val := ConRon.Refine.Nat.uadd_val hi8
        by_cases hc2 : i3 = i8
        · rw [if_pos hc2] at hrun
          have hc2' : absU i3 = absU p.n_p + 1 + p.ctors.val.length + absU p.n_idx := by
            simp only [absU]; rw [hc2]; omega
          obtain ⟨i10, hi10, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          simp only [lift, Result.ok.injEq] at hi10
          have hi10v : i10.val = v2.val.length := by
            rw [← hi10, ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
          by_cases hc3 : i10 = n
          · rw [if_pos hc3] at hrun
            have hc3' : v2.val.length = p.ctors.val.length := by
              rw [← hi10v, ← hnv, hc3]
            have hpin := rules_pin_ok_refines hrun
            rw [hpin, rulesPinOkSpec_eq_all]
            simp [absInductiveShape, hc1', hc2', hc3', absU, hnv,
              List.range_eq_range']
            congr 1
          · rw [if_neg hc3] at hrun
            obtain rfl := Result.ok_injective hrun
            have : v2.val.length ≠ p.ctors.val.length := by
              intro e; apply hc3; scalar_tac
            simp [absInductiveShape, hc1', hc2', this]
        · rw [if_neg hc2] at hrun
          obtain rfl := Result.ok_injective hrun
          have : absU i3 ≠ absU p.n_p + 1 + p.ctors.val.length + absU p.n_idx := by
            simp only [absU]; intro e; apply hc2; scalar_tac
          simp [absInductiveShape, hc1', this]
      · rw [if_neg hc1] at hrun
        obtain rfl := Result.ok_injective hrun
        have : absU i4 ≠ absU p.n_p + 1 + p.ctors.val.length := by
          simp only [absU]; intro e; apply hc1; scalar_tac
        simp [absInductiveShape, this]
  | _ =>
    obtain rfl := Result.ok_injective hrun
    simp [nativeRecPinOk, absIConstantInfo]

open Lockstep in
@[lockstep] theorem native_rec_pin_ok_twin
    {p : arena.inductives.sum_parts.InductiveShape}
    {block : alloc.vec.Vec arena.env.IConstantInfo} :
    LSP (arena.inductives.native_parts.native_rec_pin_ok p block) (fun o => TwinEq (nativeRecPinOk (absInductiveShape p) (absICIL block)) (o)) :=
  fun o h => (native_rec_pin_ok_refines h).symm

/-- `native_rec_lps_ok` ⊑ `nativeRecLpsOk` — the recursor record's
level-parameter pin. -/
theorem native_rec_lps_ok_refines
    {p : arena.inductives.sum_parts.InductiveShape} {o}
    (hrun : arena.inductives.native_parts.native_rec_lps_ok p = ok o) :
    o = nativeRecLpsOk (absInductiveShape p) := by
  rw [arena.inductives.native_parts.native_rec_lps_ok] at hrun
  simp only [nativeRecLpsOk, absInductiveShape, absIConstantVal]
  by_cases hl : p.large
  · rw [if_pos hl] at hrun
    obtain ⟨want, hwant, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [if_pos hl, nidx_vec_beq_abs hrun]
    simp [absNIdxL, nidx_cons_abs hwant]
  · rw [if_neg hl] at hrun
    rw [if_neg hl, nidx_vec_beq_abs hrun]
    simp [absNIdxL]

open Lockstep in
@[lockstep] theorem native_rec_lps_ok_twin
    {p : arena.inductives.sum_parts.InductiveShape} :
    LSP (arena.inductives.native_parts.native_rec_lps_ok p) (fun o => TwinEq (nativeRecLpsOk (absInductiveShape p)) (o)) :=
  fun o h => (native_rec_lps_ok_refines h).symm

/-- `nidx_cons_from` copies `ns` from the cursor on onto `out`. -/
theorem nidx_cons_from_refines {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.inductives.native_parts.nidx_cons_from ns i out = ok o) :
    absNIdxL o = absNIdxL out ++ absNIdxLFrom ns i := by
  simpa [absNIdxL, absNIdxLFrom] using nidx_cons_from_map i out o hrun

open Lockstep in
/-- `nidx_cons_from_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem nidx_cons_from_twin0
    {ns : alloc.vec.Vec arena.handle.NIdx} :
    LSP (arena.inductives.native_parts.nidx_cons_from ns 0#usize (alloc.vec.Vec.new arena.handle.NIdx)) (fun o => TwinEq (absNIdxL ns) (absNIdxL o)) := by
  intro o h
  have h' := (nidx_cons_from_refines h).symm
  simpa [Lockstep.TwinEq, absNIdxLFrom, absNIdxL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem nidx_cons_from_twin
    {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.NIdx} :
    LSP (arena.inductives.native_parts.nidx_cons_from ns i out) (fun o => TwinEq (absNIdxL out ++ absNIdxLFrom ns i) (absNIdxL o)) :=
  fun o h => (nidx_cons_from_refines h).symm

/-- `nidx_cons` ⊑ `n :: ns` — the twin's `elim :: lps`, over a `Vec`. -/
theorem nidx_cons_refines {n : arena.handle.NIdx}
    {ns : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.inductives.native_parts.nidx_cons n ns = ok o) :
    absNIdxL o = absNIdx n :: absNIdxL ns := by
  simpa [absNIdxL] using nidx_cons_abs hrun


open Lockstep in
@[lockstep] theorem nidx_cons_twin
    {n : arena.handle.NIdx}
    {ns : alloc.vec.Vec arena.handle.NIdx} :
    LSP (arena.inductives.native_parts.nidx_cons n ns) (fun o => TwinEq (absNIdx n :: absNIdxL ns) (absNIdxL o)) :=
  fun o h => (nidx_cons_refines h).symm

/-- `ctors_pin_ok` ⊑ `nativeShape?`'s `cs.all` pin from the cursor on. -/
theorem ctors_pin_ok_refines {reserved : alloc.vec.Vec arena.handle.NIdx}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {n_p : Std.U64} {lps : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize} {o}
    (hrun : arena.inductives.native_parts.ctors_pin_ok reserved cs n_p lps i
      = ok o) :
    o = ctorsPinOkSpec (absNIdxL reserved) (absCtors3LFrom cs i) (absU n_p)
      (absNIdxL lps) := by
  simp only [ctorsPinOkSpec, absCtors3LFrom, List.all_map, Function.comp_def]
  refine vec_cursor_all cs _
    (fun i => arena.inductives.native_parts.ctors_pin_ok reserved cs n_p lps i) ?_ ?_ i o hrun
  · intro i o hn h
    rw [arena.inductives.native_parts.ctors_pin_ok.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [← h]
  · intro i x o hx h
    have hlt : i.val < cs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.native_parts.ctors_pin_ok.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨iv, np, nf⟩ := q
    have h : (if np = n_p then
        (do
          let b ← arena.core.nidx_vec_beq iv.level_params lps
          if b then
            (do
              let b1 ← arena.env.nidx_vec_contains reserved iv.name
              if b1 then ok false
              else (do
                let i3 ← i + 1#usize
                arena.inductives.native_parts.ctors_pin_ok reserved cs n_p lps i3))
          else ok false)
      else ok false) = ok o := h
    by_cases hnp : np = n_p
    · subst hnp
      rw [if_pos rfl] at h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hbv : b = (absNIdxL iv.level_params == absNIdxL lps) := nidx_vec_beq_abs hb
      cases hbb : b
      · rw [hbb] at h hbv
        rw [if_neg (by simp), Result.ok.injEq] at h
        refine Or.inr ⟨?_, h.symm⟩
        simp only [absNIdxL] at hbv
        simp only [absIConstantVal, absNIdxL, ← hbv, Bool.and_false, Bool.false_and]
      · rw [hbb] at h hbv
        rw [if_pos (by simp)] at h
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hb1v : b1 = (absNIdxL reserved).contains (absNIdx iv.name) :=
          nidx_vec_contains_abs hb1
        cases hbb1 : b1
        · rw [hbb1] at h hb1v
          rw [if_neg (by simp)] at h
          obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          refine Or.inl ⟨?_, i3, absSz_add_one hi3, h⟩
          simp only [absNIdxL] at hbv hb1v
          simp only [absIConstantVal, absNIdxL, ← hbv, ← hb1v, beq_self_eq_true,
            Bool.and_true, Bool.true_and]
        · rw [hbb1] at h hb1v
          rw [if_pos (by simp), Result.ok.injEq] at h
          refine Or.inr ⟨?_, h.symm⟩
          simp only [absNIdxL] at hbv hb1v
          simp only [absIConstantVal, absNIdxL, ← hbv, ← hb1v, beq_self_eq_true,
            Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and]
          rfl
    · rw [if_neg hnp, Result.ok.injEq] at h
      refine Or.inr ⟨?_, h.symm⟩
      have : absU np ≠ absU n_p := by
        simp only [absU]
        intro hc
        exact hnp (by scalar_tac)
      simp [this]

open Lockstep in
/-- `ctors_pin_ok_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem ctors_pin_ok_twin0
    {reserved : alloc.vec.Vec arena.handle.NIdx}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {n_p : Std.U64}
    {lps : alloc.vec.Vec arena.handle.NIdx} :
    LSP (arena.inductives.native_parts.ctors_pin_ok reserved cs n_p lps 0#usize) (fun o => TwinEq (ctorsPinOkSpec (absNIdxL reserved) (absCtors3L cs) (absU n_p) (absNIdxL lps)) (o)) := by
  intro o h
  have h' := (ctors_pin_ok_refines h).symm
  simpa [Lockstep.TwinEq, absCtors3LFrom, absCtors3L, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem ctors_pin_ok_twin
    {reserved : alloc.vec.Vec arena.handle.NIdx}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {n_p : Std.U64}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} :
    LSP (arena.inductives.native_parts.ctors_pin_ok reserved cs n_p lps i) (fun o => TwinEq (ctorsPinOkSpec (absNIdxL reserved) (absCtors3LFrom cs i) (absU n_p) (absNIdxL lps)) (o)) :=
  fun o h => (ctors_pin_ok_refines h).symm

/-- `ctors_of` ⊑ `cs.map fun c => (c.1, c.2.2)` from the cursor on. -/
theorem ctors_of_refines
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {i : Std.Usize} {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {o}
    (hrun : arena.inductives.native_parts.ctors_of cs i out = ok o) :
    absCtorsL o = absCtorsL out ++
      (absCtors3LFrom cs i).map fun c => (c.1, c.2.2) := by
  simp only [absCtorsL, absCtors3LFrom, List.map_map]
  refine vec_cursor_copy cs _ _
    (arena.inductives.native_parts.ctors_of cs) ?_ ?_ i out o hrun
  · intro i out o hn h
    rw [arena.inductives.native_parts.ctors_of.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < cs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.native_parts.ctors_of.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨iv, np, nf⟩ := q
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, (iv1, nf), out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by simp [i_constant_val_dup_abs hiv1], h⟩

open Lockstep in
/-- `ctors_of_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem ctors_of_twin0
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)} :
    LSP (arena.inductives.native_parts.ctors_of cs 0#usize (alloc.vec.Vec.new (arena.env.IConstantVal × Std.U64))) (fun o => TwinEq ((absCtors3L cs).map fun c => (c.1, c.2.2)) (absCtorsL o)) := by
  intro o h
  have h' := (ctors_of_refines h).symm
  simpa [Lockstep.TwinEq, absCtors3LFrom, absCtors3L, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem ctors_of_twin
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} :
    LSP (arena.inductives.native_parts.ctors_of cs i out) (fun o => TwinEq (absCtorsL out ++ (absCtors3LFrom cs i).map fun c => (c.1, c.2.2)) (absCtorsL o)) :=
  fun o h => (ctors_of_refines h).symm

/-- `rhss_of` ⊑ `rules.map (·.rhs)` from the cursor on. -/
theorem rhss_of_refines {rules : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrun : arena.inductives.native_parts.rhss_of rules i out = ok o) :
    absEIdxL o = absEIdxL out ++ (absIRecRuleLFrom rules i).map (·.rhs) := by
  simp only [absEIdxL, absIRecRuleLFrom, List.map_map]
  refine vec_cursor_copy rules _ _
    (arena.inductives.native_parts.rhss_of rules) ?_ ?_ i out o hrun
  · intro i out o hn h
    rw [arena.inductives.native_parts.rhss_of.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len rules by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < rules.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.native_parts.rhss_of.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len rules by scalar_tac)] at h
    obtain ⟨ir, hir, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hix : ir = x := by
      have h1 := vec_index_some hir; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hix
    exact ⟨i2, e, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by simp [absIRecRule, dupId_eidx _ _ he], h⟩

open Lockstep in
/-- `rhss_of_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem rhss_of_twin0
    {rules : alloc.vec.Vec arena.env.IRecRule} :
    LSP (arena.inductives.native_parts.rhss_of rules 0#usize (alloc.vec.Vec.new arena.handle.EIdx)) (fun o => TwinEq ((absIRecRuleL rules).map (·.rhs)) (absEIdxL o)) := by
  intro o h
  have h' := (rhss_of_refines h).symm
  simpa [Lockstep.TwinEq, absIRecRuleLFrom, absIRecRuleL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem rhss_of_twin
    {rules : alloc.vec.Vec arena.env.IRecRule}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} :
    LSP (arena.inductives.native_parts.rhss_of rules i out) (fun o => TwinEq (absEIdxL out ++ (absIRecRuleLFrom rules i).map (·.rhs)) (absEIdxL o)) :=
  fun o h => (rhss_of_refines h).symm

/-- `native_shape_small` ⊑ `nativeShape?`'s small-eliminator arm. -/
theorem native_shape_small_refines {pers st lst}
    {cv_t cv_r : arena.env.IConstantVal} {n_p n_idx : Std.U64}
    {s : arena.handle.LIdx} {is_prop : Bool}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {rhss : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_shape_small pers st cv_t cv_r n_p
      n_idx s is_prop ctors rhss = ok o) :
    Sim₀ (Option.map absInductiveShape) pers lst o
      (nativeShapeSmallSpec (absIConstantVal cv_t) (absIConstantVal cv_r) (absU n_p)
        (absU n_idx) (absLIdx s) is_prop (absCtorsL ctors) (absEIdxL rhss)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.native_shape_small, nativeShapeSmallSpec]
  lockstep

open Lockstep in
@[lockstep] theorem native_shape_small_ls
    {pers st lst}
    {cv_t cv_r : arena.env.IConstantVal}
    {n_p n_idx : Std.U64}
    {s : arena.handle.LIdx}
    {is_prop : Bool}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {rhss : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absInductiveShape) a) (arena.inductives.native_parts.native_shape_small pers st cv_t cv_r n_p n_idx s is_prop ctors rhss) lst
      (nativeShapeSmallSpec (absIConstantVal cv_t) (absIConstantVal cv_r) (absU n_p)
        (absU n_idx) (absLIdx s) is_prop (absCtorsL ctors) (absEIdxL rhss)) :=
  LS.ofSim₀ fun _ h => native_shape_small_refines hrel hinv h

/-- `native_shape_elim` ⊑ `nativeShape?`'s eliminator split. -/
theorem native_shape_elim_refines {pers st lst}
    {cv_t : arena.env.IConstantVal}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {cv_r : arena.env.IConstantVal} {rules : alloc.vec.Vec arena.env.IRecRule}
    {n_p n_idx : Std.U64} {s : arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_shape_elim pers st cv_t cs cv_r
      rules n_p n_idx s = ok o) :
    Sim₀ (Option.map absInductiveShape) pers lst o
      (nativeShapeElimSpec (absIConstantVal cv_t) (absCtors3L cs)
        (absIConstantVal cv_r) (absIRecRuleL rules) (absU n_p) (absU n_idx)
        (absLIdx s)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_parts.native_shape_elim, nativeShapeElimSpec]
  simp only [absIConstantVal]
  rcases hc : cv_r.level_params.val with _ | ⟨elim, relps⟩
  · have hlen : alloc.vec.Vec.len cv_r.level_params = 0#usize := by
      have : (alloc.vec.Vec.len cv_r.level_params).val = 0 := by
        simp [alloc.vec.Vec.len, hc]
      scalar_tac
    simp only [hlen, if_true, List.map_nil]
    lockstep
  · have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        arena.handle.NIdx) cv_r.level_params 0#usize = ok elim := by
      rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
      simp [hc]
    have hlen : ¬ (alloc.vec.Vec.len cv_r.level_params = 0#usize) := by
      intro h0
      have : (alloc.vec.Vec.len cv_r.level_params).val = 0 := by rw [h0]; rfl
      simp [alloc.vec.Vec.len, hc] at this
    simp only [if_neg hlen, hidx, List.map_cons]
    lockstep

open Lockstep in
@[lockstep] theorem native_shape_elim_ls
    {pers st lst}
    {cv_t : arena.env.IConstantVal}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {cv_r : arena.env.IConstantVal}
    {rules : alloc.vec.Vec arena.env.IRecRule}
    {n_p n_idx : Std.U64}
    {s : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absInductiveShape) a) (arena.inductives.native_parts.native_shape_elim pers st cv_t cs cv_r rules n_p n_idx s) lst
      (nativeShapeElimSpec (absIConstantVal cv_t) (absCtors3L cs)
        (absIConstantVal cv_r) (absIRecRuleL rules) (absU n_p) (absU n_idx)
        (absLIdx s)) :=
  LS.ofSim₀ fun _ h => native_shape_elim_refines hrel hinv h

/-- `native_shape_sort` ⊑ `nativeShape?`'s result-sort read. -/
theorem native_shape_sort_refines {pers st lst} {cv_t : arena.env.IConstantVal}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {cv_r : arena.env.IConstantVal} {rules : alloc.vec.Vec arena.env.IRecRule}
    {n_p n_idx : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_shape_sort pers st cv_t cs cv_r
      rules n_p n_idx = ok o) :
    Sim₀ (Option.map absInductiveShape) pers lst o
      (nativeShapeSortSpec (absIConstantVal cv_t) (absCtors3L cs)
        (absIConstantVal cv_r) (absIRecRuleL rules) (absU n_p) (absU n_idx)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.native_shape_sort, nativeShapeSortSpec]
  lockstep

open Lockstep in
@[lockstep] theorem native_shape_sort_ls
    {pers st lst}
    {cv_t : arena.env.IConstantVal}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {cv_r : arena.env.IConstantVal}
    {rules : alloc.vec.Vec arena.env.IRecRule}
    {n_p n_idx : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absInductiveShape) a) (arena.inductives.native_parts.native_shape_sort pers st cv_t cs cv_r rules n_p n_idx) lst
      (nativeShapeSortSpec (absIConstantVal cv_t) (absCtors3L cs)
        (absIConstantVal cv_r) (absIRecRuleL rules) (absU n_p) (absU n_idx)) :=
  LS.ofSim₀ fun _ h => native_shape_sort_refines hrel hinv h

/-- `native_shape_at` ⊑ `nativeShape?`'s body once the block's members are in
hand. -/
theorem native_shape_at_refines {pers st lst} {n_pd : Std.U64}
    {cv_t : arena.env.IConstantVal}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {cv_r : arena.env.IConstantVal} {m_i r_p : Std.U64}
    {rules : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_shape_at pers st n_pd cv_t cs cv_r
      m_i r_p rules = ok o) :
    Sim₀ (Option.map absInductiveShape) pers lst o
      (nativeShapeAtSpec (absU n_pd) (absIConstantVal cv_t) (absCtors3L cs)
        (absIConstantVal cv_r) (absU m_i) (absU r_p) (absIRecRuleL rules)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.native_shape_at, nativeShapeAtSpec]
  lockstep

open Lockstep in
@[lockstep] theorem native_shape_at_ls
    {pers st lst}
    {n_pd : Std.U64}
    {cv_t : arena.env.IConstantVal}
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {cv_r : arena.env.IConstantVal}
    {m_i r_p : Std.U64}
    {rules : alloc.vec.Vec arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absInductiveShape) a) (arena.inductives.native_parts.native_shape_at pers st n_pd cv_t cs cv_r m_i r_p rules) lst
      (nativeShapeAtSpec (absU n_pd) (absIConstantVal cv_t) (absCtors3L cs)
        (absIConstantVal cv_r) (absU m_i) (absU r_p) (absIRecRuleL rules)) :=
  LS.ofSim₀ fun _ h => native_shape_at_refines hrel hinv h

/-- `native_shape` ⊑ `nativeShape?`. -/
theorem native_shape_refines {pers st lst} {n_pd : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_shape pers st n_pd block = ok o) :
    Sim₀ (Option.map absInductiveShape) pers lst o
      (nativeShape? (absU n_pd) (absICIL block)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.native_shape, nativeShape_unfold]
  -- the tail copy from `1`, at the twin's list tail
  have hdup : ∀ ci rest, block.val = ci :: rest → ∀ (n : Std.Usize),
      Lockstep.LSP (arena.env.i_constant_infos_dup_from block 1#usize
        (alloc.vec.Vec.with_capacity arena.env.IConstantInfo n))
        (fun o => Lockstep.TwinEq (rest.map absIConstantInfo) (absICIL o)) := by
    intro ci rest hcr n o h
    have := i_constant_infos_dup_from_abs h
    rw [hcr] at this
    simpa [Lockstep.TwinEq, absICIL, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using
      this.symm
  rcases hb : block.val with _ | ⟨ci, rest⟩
  · have hlen : alloc.vec.Vec.len block = 0#usize := by
      have : (alloc.vec.Vec.len block).val = 0 := by simp [alloc.vec.Vec.len, hb]
      scalar_tac
    simp only [hlen, if_true, absICIL, hb, List.map_nil]
    lockstep
  · have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        arena.env.IConstantInfo) block 0#usize = ok ci := by
      rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
      simp [hb]
    have hlen : ¬ (alloc.vec.Vec.len block = 0#usize) := by
      intro h0
      have : (alloc.vec.Vec.len block).val = 0 := by rw [h0]; rfl
      simp [alloc.vec.Vec.len, hb] at this
    have hdup' := hdup ci rest hb
    rw [if_neg hlen, hidx]
    simp only [absICIL, hb, List.map_cons]
    cases ci <;> simp only [absIConstantInfo] <;> lockstep

open Lockstep in
@[lockstep] theorem native_shape_ls
    {pers st lst}
    {n_pd : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absInductiveShape) a) (arena.inductives.native_parts.native_shape pers st n_pd block) lst
      (nativeShape? (absU n_pd) (absICIL block)) :=
  LS.ofSim₀ fun _ h => native_shape_refines hrel hinv h

/-- `native_parts` ⊑ `nativeParts?` — recognise a direct block: its SHAPE; the
fields' kinds are a PLACEHOLDER the install fills. -/
theorem native_parts_refines {pers st lst} {n_pd : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_parts.native_parts pers st n_pd block = ok o) :
    Sim₀ (Option.map absNativeParts) pers lst o
      (nativeParts? (absU n_pd) (absICIL block)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_parts.native_parts, nativeParts?]
  lockstep

open Lockstep in
@[lockstep] theorem native_parts_ls {pers st lst} {n_pd : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = Option.map absNativeParts a)
      (arena.inductives.native_parts.native_parts pers st n_pd block) lst
      (nativeParts? (absU n_pd) (absICIL block)) :=
  LS.ofSim₀ fun _ h => native_parts_refines hrel hinv h

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
/-- info: 'ConRon.Refine2.rec_idx_of_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rec_idx_of_refines

/-- info: 'ConRon.Refine2.ctors_pin_ok_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ctors_pin_ok_refines

/-- info: 'ConRon.Refine2.kind_get_d_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms kind_get_d_refines

/-- info: 'ConRon.Refine2.rules_pin_ok_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rules_pin_ok_refines

/-- info: 'ConRon.Refine2.native_rec_pin_ok_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms native_rec_pin_ok_refines


end ConRon.Refine2
