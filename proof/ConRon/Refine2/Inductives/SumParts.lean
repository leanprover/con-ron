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
  sorry

/-- `ctors_copy` is the identity on the abstraction. -/
theorem ctors_copy_refines
    {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {o}
    (hrun : arena.inductives.sum_parts.ctors_copy cs = ok o) :
    absCtorsL o = absCtorsL cs := by
  sorry

/-- `inductive_shape_dup` is the identity on the abstraction — the twin's
`InductiveShape` is a value and has no copy. -/
theorem inductive_shape_dup_refines
    {p : arena.inductives.sum_parts.InductiveShape} {o}
    (hrun : arena.inductives.sum_parts.inductive_shape_dup p = ok o) :
    absInductiveShape o = absInductiveShape p := by
  sorry

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
  sorry

/-- `sum_split` ⊑ `sumSplit`. -/
theorem sum_split_refines {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrun : arena.inductives.sum_parts.sum_split block = ok o) :
    (o.map fun q => (absCtors3L q.1, absIConstantVal q.2.1, absU q.2.2.1,
        absU q.2.2.2.1, q.2.2.2.2.val.map absIRecRule))
      = sumSplit (absICIL block) := by
  sorry

/-! ## The completion, and the two readers -/

/-- `with_sort` ⊑ `InductiveShape.withSort` — the one function of this module
that reads the store: `isProp` is `lvlEq? s zero`, whose verdict is cached. -/
theorem with_sort_refines {pers st lst}
    {p : arena.inductives.sum_parts.InductiveShape} {s : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.sum_parts.with_sort pers st p s = ok o) :
    Sim absInductiveShape (fun _ => True) pers lst o
      ((absInductiveShape p).withSort (absLIdx s)) := by
  sorry

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

end ConRon.Refine2
