/-
# `ConRon.Refine2.Inductives.SumParts` — Theorem 2 for `arena::inductives::sum_parts`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/sum_parts.rs` against
`proof/ConRon/Arena/Inductives/SumParts.lean`: the block's shape record, the
member split that reads it, and the completion with the result sort.

**Eight `pub fn`s, seven of them PURE.**  The twin's own module note says why:
`sumSplit` matches on the members' CONSTRUCTORS and moves their fields,
touching no term, so it takes no state — and `inductive_shape_dup` /
`ctors_copy` are the record copy Lean's value semantics gives for free.  Only
`with_sort` reads the store (`lvlEq?` caches its verdict), and it is the one
`Sim` of the file.

**Two Rust functions have no twin of their own**: `ctors_copy` and its
`_from` cursor are `ron::hashmap::Dup` lifted to a `Vec`, which the twin's
`List` does not need, so both are stated as the IDENTITY on the abstraction —
the same reading `Refine2/Checker/Base.lean`'s `vec_dup_refines` gives.
-/
import ConRon.Refine2.Inductives.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The record copies -/

/-- `ctors_copy_from` is the identity on the abstraction from the cursor on:
`ron::hashmap::Dup`'s `dup2` at an `IConstantVal` copies handles, and
`Refine2/Inv.lean`'s five `DupId` lemmas say every one of them is the
identity. -/
theorem ctors_copy_from_refines
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {o}
    (hrun : arena.inductives.sum_parts.ctors_copy_from cs i out = ok o) :
    absCtorsL o = absCtorsL out ++ absCtorsLFrom cs i := by
  simp only [absCtorsL, absCtorsLFrom]
  refine vec_cursor_copy cs _ _
    (arena.inductives.sum_parts.ctors_copy_from cs) ?_ ?_ i out o hrun
  · intro i out o hn h
    rw [arena.inductives.sum_parts.ctors_copy_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < cs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.sum_parts.ctors_copy_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨iv, nf⟩ := q
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, (iv1, nf), out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by simp [i_constant_val_dup_abs hiv1], h⟩

open Lockstep in
@[lockstep] theorem ctors_copy_from_twin
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} :
    LSP (arena.inductives.sum_parts.ctors_copy_from cs i out) (fun o => TwinEq (absCtorsL out ++ absCtorsLFrom cs i) (absCtorsL o)) :=
  fun o h => (ctors_copy_from_refines h).symm

/-- `ctors_copy` is the identity on the abstraction. -/
theorem ctors_copy_refines
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {o}
    (hrun : arena.inductives.sum_parts.ctors_copy cs = ok o) :
    absCtorsL o = absCtorsL cs := by
  rw [arena.inductives.sum_parts.ctors_copy] at hrun
  have h := ctors_copy_from_refines hrun
  simpa [absCtorsL, absCtorsLFrom, alloc.vec.Vec.new,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h

open Lockstep in
@[lockstep] theorem ctors_copy_twin
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} :
    LSP (arena.inductives.sum_parts.ctors_copy cs) (fun o => TwinEq (absCtorsL cs) (absCtorsL o)) :=
  fun o h => (ctors_copy_refines h).symm

/-- `inductive_shape_dup` is the identity on the abstraction — the twin's
`InductiveShape` is a value and has no copy. -/
theorem inductive_shape_dup_refines
    {p : arena.inductives.sum_parts.InductiveShape} {o}
    (hrun : arena.inductives.sum_parts.inductive_shape_dup p = ok o) :
    absInductiveShape o = absInductiveShape p := by
  rw [arena.inductives.sum_parts.inductive_shape_dup] at hrun
  obtain ⟨iv, hiv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨iv1, hiv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [← Result.ok_injective hrun]
  simp only [absInductiveShape, i_constant_val_dup_abs hiv,
    i_constant_val_dup_abs hiv1, dupId_nidx _ _ hn, dupId_lidx _ _ hl,
    ctors_copy_refines hv, absEIdxL, eidx_vec_dup_val hv1]

open Lockstep in
@[lockstep] theorem inductive_shape_dup_twin
    {p : arena.inductives.sum_parts.InductiveShape} :
    LSP (arena.inductives.sum_parts.inductive_shape_dup p) (fun o => TwinEq (absInductiveShape p) (absInductiveShape o)) :=
  fun o h => (inductive_shape_dup_refines h).symm

/-! ## The member split

`sumSplit` is PURE on both sides, so the statement is the exact-result
equation of DESIGN §3.5 and there is no state anywhere in it.  The nested
`Option`-of-tuple of the twin (`q.2` is four components) is ONE five-component
tuple in the port, which is the module note's shape and is why the abstraction
is spelled out rather than composed. -/

/-- `sum_split_from` ⊑ `sumSplit` from the cursor on, with the accumulated
constructors in front.  Lean conses the constructor on the way *out* and the
port accumulates on the way *in*; both are the declaration-order list, which
is what the `++` says. -/
theorem sum_split_from_refines {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize} {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)}
    {o} (hrun : arena.inductives.sum_parts.sum_split_from block i out = ok o) :
    (o.map fun q => (absCtors3L q.1, absIConstantVal q.2.1, absU q.2.2.1,
        absU q.2.2.2.1, q.2.2.2.2.val.map absIRecRule))
      = (sumSplit (absICILFrom block i)).map
          fun q => (absCtors3L out ++ q.1, q.2) := by
  refine cursor_induction (fun i : Std.Usize => i.val) block.val.length
    (fun i out => ∀ o, arena.inductives.sum_parts.sum_split_from block i out = ok o →
      (o.map fun q => (absCtors3L q.1, absIConstantVal q.2.1, absU q.2.2.1,
          absU q.2.2.2.1, q.2.2.2.2.val.map absIRecRule))
        = (sumSplit (absICILFrom block i)).map
            fun q => (absCtors3L out ++ q.1, q.2)) ?_ ?_ i out o hrun
  · intro i out hn o h
    rw [arena.inductives.sum_parts.sum_split_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
    subst h
    simp only [absICILFrom, List.drop_eq_nil_of_le hn, List.map_nil, Option.map_none]
    rfl
  · intro i out hi ih o h
    rw [arena.inductives.sum_parts.sum_split_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hb, hiiv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hii)
    have hdrop : block.val.drop i.val = ii :: block.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hb, hiiv]
    simp only [absICILFrom, hdrop, List.map_cons]
    cases ii with
    | AxiomInfo cv => obtain rfl := Result.ok_injective h; rfl
    | DefnInfo cv v hint => obtain rfl := Result.ok_injective h; rfl
    | ThmInfo cv v => obtain rfl := Result.ok_injective h; rfl
    | IndInfo cv caps => obtain rfl := Result.ok_injective h; rfl
    | ProjInfo tbl => obtain rfl := Result.ok_injective h; rfl
    | CtorInfo cv np nf =>
      simp only [] at h
      obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v := absSz_add_one hi2
      have h2 := ih i2 out1 hi2v o h
      rw [h2]
      simp only [absICILFrom, hi2v, absIConstantInfo, absCtors3L,
        ConRon.Refine.vec_push_val hout1, List.map_append, List.map_cons,
        List.map_nil, i_constant_val_dup_abs hiv]
      simp only [sumSplit]
      cases sumSplit ((block.val.drop (i.val + 1)).map absIConstantInfo) <;> simp
    | RecInfo cv mi rp rules =>
      simp only [] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      by_cases hlen : i.val + 1 = block.val.length
      · rw [if_pos (show i2 = alloc.vec.Vec.len block by scalar_tac)] at h
        obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain rfl := Result.ok_injective h
        simp only [absIConstantInfo,
          List.drop_eq_nil_of_le (by omega : block.val.length ≤ i.val + 1),
          List.map_nil, Option.map_some]
        simp [sumSplit, i_constant_val_dup_abs hiv, i_rec_rules_dup_abs hv]
      · rw [if_neg (show ¬ i2 = alloc.vec.Vec.len block by scalar_tac)] at h
        obtain rfl := Result.ok_injective h
        have hlt : i.val + 1 < block.val.length := by omega
        rcases hr : block.val.drop (i.val + 1) with _ | ⟨y, ys⟩
        · exact absurd (List.drop_eq_nil_iff.mp hr) (by omega)
        · simp only [absIConstantInfo, List.map_cons, Option.map_none]
          rfl

open Lockstep in
@[lockstep] theorem sum_split_from_twin
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize}
    {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)} :
    LSP (arena.inductives.sum_parts.sum_split_from block i out) (fun o => TwinEq ((sumSplit (absICILFrom block i)).map fun q => (absCtors3L out ++ q.1, q.2)) ((o.map fun q => (absCtors3L q.1, absIConstantVal q.2.1, absU q.2.2.1, absU q.2.2.2.1, q.2.2.2.2.val.map absIRecRule)))) :=
  fun o h => (sum_split_from_refines h).symm

/-- `sum_split` ⊑ `sumSplit`. -/
theorem sum_split_refines {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrun : arena.inductives.sum_parts.sum_split block = ok o) :
    (o.map fun q => (absCtors3L q.1, absIConstantVal q.2.1, absU q.2.2.1,
        absU q.2.2.2.1, q.2.2.2.2.val.map absIRecRule))
      = sumSplit (absICIL block) := by
  rw [arena.inductives.sum_parts.sum_split] at hrun
  have h := sum_split_from_refines hrun
  simpa [absCtors3L, absICIL, absICILFrom, alloc.vec.Vec.new,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h

open Lockstep in
@[lockstep] theorem sum_split_twin
    {block : alloc.vec.Vec arena.env.IConstantInfo} :
    LSP (arena.inductives.sum_parts.sum_split block) (fun o => TwinEq (sumSplit (absICIL block)) ((o.map fun q => (absCtors3L q.1, absIConstantVal q.2.1, absU q.2.2.1, absU q.2.2.2.1, q.2.2.2.2.val.map absIRecRule)))) :=
  fun o h => (sum_split_refines h).symm

/-! ## The completion, and the two readers -/

/-- `with_sort` ⊑ `InductiveShape.withSort` — the one function of this module
that reads the store: `isProp` is `lvlEq? s zero`, whose verdict is cached. -/
theorem with_sort_refines {pers st lst}
    {p : arena.inductives.sum_parts.InductiveShape} {s : arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.sum_parts.with_sort pers st p s = ok o) :
    Sim₀ absInductiveShape pers lst o
      ((absInductiveShape p).withSort (absLIdx s)) := by
  -- lockstep trial
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.sum_parts.with_sort, absInductiveShape]
  lockstep

open Lockstep in
@[lockstep] theorem with_sort_ls
    {pers st lst}
    {p : arena.inductives.sum_parts.InductiveShape}
    {s : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absInductiveShape a) (arena.inductives.sum_parts.with_sort pers st p s) lst
      ((absInductiveShape p).withSort (absLIdx s)) :=
  LS.ofSim₀ fun _ h => with_sort_refines hrel hinv h

/-- `rule_prefix` ⊑ `InductiveShape.rulePrefix` — `nP + 1 + |ctors|`, and the
port's `ctors.len() as u64` against the twin's `List.length` is the one place
this module's arithmetic crosses the container. -/
theorem rule_prefix_refines {p : arena.inductives.sum_parts.InductiveShape} {o}
    (hrun : arena.inductives.sum_parts.rule_prefix p = ok o) :
    absU o = (absInductiveShape p).rulePrefix := by
  rw [arena.inductives.sum_parts.rule_prefix] at hrun
  obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have h1 := ConRon.Refine.Nat.uadd_val hi
  have h3 := ConRon.Refine.Nat.uadd_val hrun
  simp only [lift, Result.ok.injEq] at hi2
  subst hi2
  simp only [InductiveShape.rulePrefix, absInductiveShape, absU, absCtorsL,
    List.length_map]
  have hc : (Std.UScalar.cast .U64 (alloc.vec.Vec.len p.ctors)).val
      = p.ctors.val.length := by
    rw [ConRon.Refine.ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
  rw [h3, h1, hc]
  scalar_tac

open Lockstep in
@[lockstep] theorem rule_prefix_twin
    {p : arena.inductives.sum_parts.InductiveShape} :
    LSP (arena.inductives.sum_parts.rule_prefix p) (fun o => TwinEq ((absInductiveShape p).rulePrefix) (absU o)) :=
  fun o h => (rule_prefix_refines h).symm

/-- `major_idx` ⊑ `InductiveShape.majorIdx`. -/
theorem major_idx_refines {p : arena.inductives.sum_parts.InductiveShape} {o}
    (hrun : arena.inductives.sum_parts.major_idx p = ok o) :
    absU o = (absInductiveShape p).majorIdx := by
  rw [arena.inductives.sum_parts.major_idx] at hrun
  obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have h1 := rule_prefix_refines hi
  have h3 := ConRon.Refine.Nat.uadd_val hrun
  simp only [InductiveShape.majorIdx, absInductiveShape, absU] at *
  omega

open Lockstep in
@[lockstep] theorem major_idx_twin
    {p : arena.inductives.sum_parts.InductiveShape} :
    LSP (arena.inductives.sum_parts.major_idx p) (fun o => TwinEq ((absInductiveShape p).majorIdx) (absU o)) :=
  fun o h => (major_idx_refines h).symm

/-! ## The axiom census

The file's five closed `_refines` read `[propext, Classical.choice,
Quot.sound]` and nothing else; the block's dearest stands for them. -/

/-- info: 'ConRon.Refine2.sum_split_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sum_split_refines


end ConRon.Refine2
