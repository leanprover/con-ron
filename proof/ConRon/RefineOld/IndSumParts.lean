/-
# `kernel::inductives::sum_parts` refined (task #57)

`CORE_PLAN.md` step 7.  The **block-shape record** every direct (fixpoint)
install is read into, and the member split that recognises it
(`crates/con-ron-core/src/kernel/inductives/sum_parts.rs`) against
`ConLeche/Kernel/Inductives/SumParts.lean`.  `IndAbs.absInductiveShape` is the
record's abstraction; `SumParts.lean`'s other fifteen declarations are the
`@[simp]` projection equations of `InductiveShape.withSort` plus
`withSort_self`, which carry no code and are the specification, so they are
used here rather than re-proved.

| group | items |
|---|---|
| the record's copy | `inductive_shape_dup`, `ctors_copy`, `ctors_copy_from` |
| the member split | `sum_split`, `sum_split_from` |
| the readers | `with_sort`, `rule_prefix` (`InductiveShape.rulePrefix`, cited in `SumInstall.lean` but a reader of this record), `major_idx` |

**Two deviations the statements had to absorb** (task #25):

* `sum_split` is an **index recursion accumulating on the way in**, where
  Lean's `sumSplit` conses the constructor on the way *out*
  (`(cvC, nP, nF) :: q.1`).  The general lemma is therefore stated with the
  accumulator in front — `absCtorSpecs out ++ q.1` — and the entry point is
  its `i = 0`, `out = []` reading, where the accumulator vanishes and the
  statement is the plain `absConstantInfos block`'s `sumSplit`.
* the nested `Option (List _ × ConstantVal × Nat × Nat × List RecRule)` is
  **one flat five-component tuple** in the port; `absSumSplit` below is where
  the two spellings meet.

The three copies are stated as **identities** (`v = cs`, `p' = p`), which is
the strongest form a copy can have and the form `Refine/Env.lean` gives every
other copy in the port; the `abs` reading follows by `congrArg`.

No `sorry`: the whole module is proved, and `#guard_msgs in #print axioms` at
the bottom pins `sum_split_refines` — the recogniser's entry point — at the
three standard axioms.
-/
import ConRon.RefineOld.IndAbs

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.SumParts

/-! ## The split's two extra abstractions (**to be unified into
`Refine/Abs.lean`**) -/

/-- `sumSplit`'s constructor list: a `Vec<(ConstantVal, u64, u64)>` as
`List (ConstantVal × Nat × Nat)`. -/
def absCtorSpecs (cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)) :
    List (ConLeche.ConstantVal × Nat × Nat) :=
  cs.val.map (fun c => (absConstantVal c.1, c.2.1.val, c.2.2.val))

/-- Every stored constant of a split's constructor list is well formed. -/
def CtorSpecsWF (cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)) : Prop :=
  ∀ c ∈ cs.val, ConstantValWF c.1

/-- `sumSplit`'s result: the port's flat five-component tuple as Lean's
nested one (task #25's deviation 6 — `q.2` is the same thing). -/
def absSumSplit
    (q : (alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)) × env.ConstantVal
      × Std.U64 × Std.U64 × (alloc.vec.Vec env.RecRule)) :
    List (ConLeche.ConstantVal × Nat × Nat) × ConLeche.ConstantVal × Nat × Nat
      × List ConLeche.RecRule :=
  (absCtorSpecs q.1, absConstantVal q.2.1, q.2.2.1.val, q.2.2.2.1.val,
    absRecRules q.2.2.2.2)

/-! ## The record's copy -/

/-- `ConLeche/Kernel/Inductives/SumParts.lean:78-101` — `ctors_copy_from`
appends the rest of the constructor list to its accumulator.  Stated as the
*identity* on the `Vec`, which is the strongest form a copy can have and the
form `Refine/Env.lean` gives every other copy in the port. -/
theorem ctors_copy_from_val (cs : alloc.vec.Vec (env.ConstantVal × Std.U64)) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec (env.ConstantVal × Std.U64)),
      cs.length - i.val ≤ k →
      inductives.sum_parts.ctors_copy_from cs i out = ok v →
      v.val = out.val ++ cs.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [inductives.sum_parts.ctors_copy_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [inductives.sum_parts.ctors_copy_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ cs.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      have hlt : i.val < cs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := cs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, hw, bind_tc_ok] at h
      obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      rw [Env.constant_val_dup_refines hcv] at hout1
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `ctors_copy_from` at its own statement. -/
theorem ctors_copy_from_refines
    {cs out v : alloc.vec.Vec (env.ConstantVal × Std.U64)} {i : Std.Usize}
    (h : inductives.sum_parts.ctors_copy_from cs i out = ok v) :
    v.val = out.val ++ cs.val.drop i.val :=
  ctors_copy_from_val cs cs.length i out v (by scalar_tac) h

/-- `ConLeche/Kernel/Inductives/SumParts.lean:78-101` — `ctors_copy` is the
identity. -/
theorem ctors_copy_refines {cs v : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    (h : inductives.sum_parts.ctors_copy cs = ok v) : v = cs := by
  rw [inductives.sum_parts.ctors_copy] at h
  exact alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.new] using
      ctors_copy_from_val cs cs.length 0#usize _ v (by scalar_tac) h)

/-- `ConLeche/Kernel/Inductives/SumParts.lean:78-101` — `inductive_shape_dup`
is Lean's value semantics: the record is unchanged. -/
theorem inductive_shape_dup_refines
    {p p' : inductives.sum_parts.InductiveShape}
    (h : inductives.sum_parts.inductive_shape_dup p = ok p') : p' = p := by
  rw [inductives.sum_parts.inductive_shape_dup] at h
  simp only [name_dup_eq, level_dup_eq, bind_tc_ok] at h
  obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨es, hes, h⟩ := bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h, Env.constant_val_dup_refines hcv,
    Env.constant_val_dup_refines hcv1, ctors_copy_refines hv,
    Env.exprs_copy_refines hes]

/-! ## The member split -/

/-- `ConLeche/Kernel/Inductives/SumParts.lean:103-110` — `sum_split_from`
refines `sumSplit` on the block's tail, with the port's accumulator in front
of what Lean conses on the way out. -/
theorem sum_split_from_refines {block : alloc.vec.Vec env.ConstantInfo}
    {out : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)} {i : Std.Usize}
    {o : Option ((alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64))
      × env.ConstantVal × Std.U64 × Std.U64 × (alloc.vec.Vec env.RecRule))}
    (hblock : ConstantInfosWF block) (hout : CtorSpecsWF out)
    (h : inductives.sum_parts.sum_split_from block i out = ok o) :
    o.map absSumSplit
      = (ConLeche.sumSplit ((absConstantInfos block).drop i.val)).map
          (fun q => (absCtorSpecs out ++ q.1, q.2)) := by
  generalize hd : block.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i out o with
  | _ d ih =>
    rw [inductives.sum_parts.sum_split_from] at h
    split at h
    · -- past the end: `sumSplit []` is `none`
      rename_i hge
      have hnil : (absConstantInfos block).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absConstantInfos, List.length_map]
        scalar_tac
      rw [hnil, ← Result.ok_injective h]
      rfl
    · rename_i hlt
      have hlt' : i.val < block.val.length := by
        have := alloc.vec.Vec.len_val block; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block i hlt')
      subst hyv
      have hlt2 : i.val < (absConstantInfos block).length := by
        simpa [absConstantInfos] using hlt'
      have hcons : (absConstantInfos block).drop i.val
          = absConstantInfo block.val[i.val]
            :: (absConstantInfos block).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absConstantInfos]
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      rw [hcons]
      -- `block[i]`'s tag decides the arm on both sides
      cases hci : block.val[i.val] with
      | AxiomInfo cv => rw [hci] at h; rw [← Result.ok_injective h]; rfl
      | DefnInfo cv v hint => rw [hci] at h; rw [← Result.ok_injective h]; rfl
      | ThmInfo cv v => rw [hci] at h; rw [← Result.ok_injective h]; rfl
      | IndInfo cv caps => rw [hci] at h; rw [← Result.ok_injective h]; rfl
      | ProjInfo t => rw [hci] at h; rw [← Result.ok_injective h]; rfl
      | CtorInfo cv_c n_p n_f =>
        -- a constructor: push and recurse
        rw [hci] at h
        obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hout : CtorSpecsWF out1 := by
          intro c hc
          rw [vec_push_val hout1] at hc
          rcases List.mem_append.mp hc with hc' | hc'
          · exact hout c hc'
          · simp only [List.mem_singleton] at hc'
            subst hc'
            rw [Env.constant_val_dup_refines hcv]
            have hciwf := hblock _ (List.getElem_mem hlt')
            rw [hci] at hciwf
            exact hciwf
        have hrec := ih (block.length - i2.val) (by scalar_tac) hout h (by scalar_tac)
        have habs : absCtorSpecs out1
            = absCtorSpecs out ++ [(absConstantVal cv_c, n_p.val, n_f.val)] := by
          rw [absCtorSpecs, vec_push_val hout1, Env.constant_val_dup_refines hcv]
          simp [absCtorSpecs]
        rw [hi2v] at hrec
        have hcs : ConLeche.sumSplit (ConLeche.ConstantInfo.ctorInfo
              (absConstantVal cv_c) n_p.val n_f.val
              :: (absConstantInfos block).drop (i.val + 1))
            = (ConLeche.sumSplit ((absConstantInfos block).drop (i.val + 1))).map
                (fun q => ((absConstantVal cv_c, n_p.val, n_f.val) :: q.1, q.2)) :=
          rfl
        rw [hrec, habs, absConstantInfo, hcs]
        cases ConLeche.sumSplit ((absConstantInfos block).drop (i.val + 1)) with
        | none => rfl
        | some q => simp
      | RecInfo cv_r m_i r_p rules =>
        -- the closing recursor: only when it is the last member
        rw [hci] at h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hdrop : (absConstantInfos block).drop (i.val + 1) = []
            ↔ i.val + 1 = block.val.length := by
          rw [List.drop_eq_nil_iff]
          simp only [absConstantInfos, List.length_map]
          omega
        split at h
        · rename_i heq
          have hlen : i.val + 1 = block.val.length := by
            have := alloc.vec.Vec.len_val block; scalar_tac
          obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          rw [← Result.ok_injective h, hdrop.mpr hlen,
            Env.constant_val_dup_refines hcv, Env.rec_rules_copy_refines hv]
          simp [absSumSplit, absConstantInfo, absRecRules, ConLeche.sumSplit]
        · rename_i hne
          have hlen : i.val + 1 ≠ block.val.length := by
            have := alloc.vec.Vec.len_val block; scalar_tac
          obtain ⟨rest, hrest⟩ : ∃ rest,
              (absConstantInfos block).drop (i.val + 1) = rest ∧ rest ≠ [] :=
            ⟨_, rfl, fun hc => hlen (hdrop.mp hc)⟩
          rw [← Result.ok_injective h]
          rcases hr : (absConstantInfos block).drop (i.val + 1) with _ | ⟨a, rest'⟩
          · exact absurd (hdrop.mp hr) hlen
          · simp [absConstantInfo, ConLeche.sumSplit]

/-- `ConLeche/Kernel/Inductives/SumParts.lean:103-110` — `sum_split` refines
`sumSplit`: the entry point, where the accumulator is empty. -/
theorem sum_split_refines {block : alloc.vec.Vec env.ConstantInfo}
    {o : Option ((alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64))
      × env.ConstantVal × Std.U64 × Std.U64 × (alloc.vec.Vec env.RecRule))}
    (hblock : ConstantInfosWF block)
    (h : inductives.sum_parts.sum_split block = ok o) :
    o.map absSumSplit = ConLeche.sumSplit (absConstantInfos block) := by
  rw [inductives.sum_parts.sum_split] at h
  have hout : CtorSpecsWF (alloc.vec.Vec.new (env.ConstantVal × Std.U64 × Std.U64)) := by
    intro c hc; simp [alloc.vec.Vec.new] at hc
  have := sum_split_from_refines hblock hout h
  simpa [absCtorSpecs, alloc.vec.Vec.new] using this

/-! ## The readers -/

/-- `ConLeche/Kernel/Inductives/SumParts.lean:112-119` — `with_sort` refines
`InductiveShape.withSort`: the record completed with the former's result sort,
`isProp` recomputed so that the recogniser's invariant holds by definition.
The port's `is_prop` is `struct_parts::level_is_prop`, which is the cited
`Level.isEquiv s .zero == some true` spelled as a three-way match. -/
theorem with_sort_refines {p p' : inductives.sum_parts.InductiveShape}
    {s : level.Level} (hs : LevelWF s)
    (h : inductives.sum_parts.with_sort p s = ok p') :
    IndAbs.absInductiveShape p'
      = (IndAbs.absInductiveShape p).withSort (absLevel s) := by
  rw [inductives.sum_parts.with_sort] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  rw [inductives.struct_parts.level_is_prop] at hb
  obtain ⟨u, hu, hb⟩ := bind_eq_ok_iff.mp hb
  obtain ⟨o, ho, hb⟩ := bind_eq_ok_iff.mp hb
  have hz : absLevel u = .zero := Level.zero_refines hu
  have hzwf : LevelWF u := LevelWF.zero hu
  have heq : ConLeche.Level.isEquiv (absLevel s) .zero = o := by
    rw [← hz]; exact Level.is_equiv_refines hs hzwf ho
  rw [← Result.ok_injective h]
  cases p
  cases o with
  | none => simp_all [IndAbs.absInductiveShape, ConLeche.InductiveShape.withSort]
  | some bb =>
    cases bb <;>
      simp_all [IndAbs.absInductiveShape, ConLeche.InductiveShape.withSort]

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:292-294` — `rule_prefix`
refines `InductiveShape.rulePrefix`: the parameters, the motive and the
minors. -/
theorem rule_prefix_refines {p : inductives.sum_parts.InductiveShape}
    {r : Std.U64} (h : inductives.sum_parts.rule_prefix p = ok r) :
    r.val = (IndAbs.absInductiveShape p).rulePrefix := by
  rw [inductives.sum_parts.rule_prefix] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  have hlen : (IndAbs.absInductiveShape p).ctors.length = p.ctors.val.length := by
    simp [IndAbs.absInductiveShape, IndAbs.absCtors]
  have hi2v : i2.val = p.ctors.val.length := by
    have hlv := alloc.vec.Vec.len_val p.ctors
    have hc : (Std.UScalar.cast .U64 p.ctors.len).val = p.ctors.len.val :=
      ExprOps.usize_cast_u64_val _
    simp only [lift, Result.ok.injEq] at hi2
    rw [← hi2, hc, hlv]
  have hiv : i.val = p.n_p.val + 1 := HashMap.uscalar_add_eq hi
  have hrv : r.val = i.val + i2.val := HashMap.uscalar_add_eq h
  rw [ConLeche.InductiveShape.rulePrefix, hrv, hiv, hi2v, hlen]
  simp [IndAbs.absInductiveShape]

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:295` — `major_idx` refines
`InductiveShape.majorIdx`: the rule prefix, then the indices. -/
theorem major_idx_refines {p : inductives.sum_parts.InductiveShape}
    {r : Std.U64} (h : inductives.sum_parts.major_idx p = ok r) :
    r.val = (IndAbs.absInductiveShape p).majorIdx := by
  rw [inductives.sum_parts.major_idx] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  have hiv := rule_prefix_refines hi
  have hrv : r.val = i.val + p.n_idx.val := HashMap.uscalar_add_eq h
  rw [ConLeche.InductiveShape.majorIdx, hrv, hiv]
  simp [IndAbs.absInductiveShape]

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/-- info: 'ConRon.Refine.SumParts.sum_split_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sum_split_refines

/-- info: 'ConRon.Refine.SumParts.with_sort_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms with_sort_refines

end ConRon.Refine.SumParts
