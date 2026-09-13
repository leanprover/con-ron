/-
# `kernel::inductives::struct_parts` refined (task #57)

`CORE_PLAN.md` step 7.  The **pure recognition and generation layer** every
direct install reads
(`crates/con-ron-core/src/kernel/inductives/struct_parts.rs`, 52 items)
against `ConLeche/Kernel/Inductives/StructParts.lean`.

| group | items |
|---|---|
| the small list helpers | `params_of`, `params_of_from`, `level_is_prop` |
| the generators | `struct_ps_at(_from)`, `struct_fam`, `field_spine(_from)`, `struct_ctor_spine(_at)`, `struct_rule_body`, `struct_elim_level`, `replace_pis_pw`, `pis_to_lams_pw`, `struct_fam_i`, `struct_ctor_resid_ok`, `struct_motive_ty_i` |
| `StructParts` and its recogniser | `struct_shape_motive`/`_minor`/`_major`, `struct_shape`, `struct_parts_front_ok`, `struct_parts_large`, `struct_parts_small_ok`, `struct_parts_core` |
| the projection table's pieces | `struct_proj_ps(_from)`, `struct_proj_arg_p`, `struct_proj_resid_p` |
| `hasLooseBVar(B)` and its memoized walk | `has_loose_bvar`, `has_loose_bvar_b_spec`, `memo_b_get`, `has_loose_bvar_b_ins`, `has_loose_bvar_b_go`, `has_loose_bvar_b_node`, `has_loose_bvar_b` |
| `structUsedLater` and the guard table | `struct_used_later(_go)`, `struct_used_later_list`, `sort_get_d`, `struct_proj_guard_at`, `struct_proj_guards(_from)` |
| the projection bodies | `struct_proj_bodies_go`, `struct_proj_bodies` |
| `mentionsConst` and its memoized walk | `mentions_const_spec`, `memo_eb_get`, `mentions_const_go`, `mentions_const_node`, `mentions_const` |
| the arithmetic helper | `nat_sub` |

## The three `@[csimp]` families, and what the statements say

con-leche writes `Expr.hasLooseBVarB`, `structProjGuards` and
`Expr.mentionsConst` **twice** — a plain structural `def` every proof consumes
and a memoized `*Go`/`*Fast` pair a `@[csimp]` lemma substitutes into compiled
code.  The port implements the `*Fast` member and cites the `*Go` walk; the
plain `def`s are ported too, unmemoized and uncalled, so that the provenance
gate stays in step with its source.  So:

* the *statement* of the port's executed function is always against the
  **logical `def`** — `has_loose_bvar_b_refines` concludes
  `= Expr.hasLooseBVarB`, `struct_proj_guards_refines` concludes
  `= structProjGuards`, `mentions_const_refines` concludes `= Expr.mentionsConst`
  — which is what the `@[csimp]` equation (`Expr.hasLooseBVarB_eq_hasLooseBVarBFast`,
  `structProjGuards_eq_structProjGuardsFast`,
  `Expr.mentionsConst_eq_mentionsConstFast`) makes the right thing to claim;
* the proof goes through con-leche's own `*_spec` lemma's *content*
  (`Expr.hasLooseBVarBGo_spec`, `structUsedLaterList_spec`,
  `Expr.mentionsConstGo_spec`), restated over the port's `&mut HashMap` memo in
  task #47's `MemoInv` shape (`Refine/ExprOps.lean`): `LooseQ` and `MentionsQ`
  below are con-leche's `LooseBVarMemoInv`/`MentionsMemoInv` as the `Q` of
  `MemoInv`, and `MemoInv.empty`/`hit`/`set` are its `.empty`/`.insert`.

## The deviations this file had to reason about

1. **`mentionsConstGo` does not short-circuit** and `hasLooseBVarBGo` does.
   The cited `mentionsConstGo` writes `let (b₁, memo) := go f; let (b₂, memo) :=
   go a; (b₁ || b₂, memo)` — *both* children are walked even when the first
   answers `true`, because the memo it hands back must hold both answers — and
   `hasLooseBVarBGo` matches on `(true, memo)` and stops.  The port keeps both
   behaviours, so `mentions_const_node`'s arms bind `b1`, `b2` and *then* test,
   and `has_loose_bvar_b_node`'s arms test after the first descent.  Both
   statements are the same `MemoInv`-threaded equation; only the proofs differ.
2. **The memo is a `&mut HashMap`**, not a threaded value (task #13); Aeneas
   turns the `&mut` back into con-leche's own threaded return, so the generated
   signature is the cited one and `MemoInv` threads through the pair.
3. **The accumulators run the other way.**  `struct_ps_at_from`,
   `field_spine_from`, `struct_proj_ps_from`, `struct_used_later_list`,
   `struct_proj_guards_from` and `struct_proj_bodies_go` push on the way *in*
   where con-leche's `List.map`/cons builds on the way out; every general lemma
   below therefore carries `absXs out ++ …` in front, and the entry point is
   its `i = 0`, `out = []` reading where the accumulator vanishes.
4. **`Array Expr` is `Vec<Expr>`** (the port has one list type), so
   `structProjBodies`' `List.toArray` is the identity here — which is why
   `struct_proj_bodies_refines` concludes at `(absExprs bs).toArray`.
5. **Every count is a `U64`** (§3.3), read by `.val`; Lean's `Nat` subtraction
   truncates where `u64`'s fails, so a Rust success is a Nat equation
   (`nat_sub` is task #13's helper, `expr_ops::sub_nat`).

## What this file owes its siblings

* **`struct_proj_bodies_refines`** is `IndStructInstall.lean`'s
  `StructProjBodiesRefines` — the second of `StructWalkers.plain`'s two
  walkers — stated at exactly that shape, so that
  `check_struct_proj_table_refines` can take it as an ingredient.
* **`level_is_prop_refines`** is what `IndSumParts.lean`'s
  `with_sort_refines`, `IndNativeParts.lean`'s `native_shape` and
  `struct_parts_core_refines` below all read: the `isProp` flag all three
  recognisers compute.

`StructParts` itself is abstracted by `IndAbs.absStructParts` and its
well-formedness is `IndAbs.StructPartsWF`; nothing in the shipped install path
consumes the record (the simple-structure route was deleted at con-leche's
task #210 Part C), so this file is the only reader of both.

25 `sorry`s, all of them one of two things and never a weakened statement:
(a) an Aeneas `partial_fixpoint` index recursion whose unfolding needs the
fixpoint equation plus a measure — `params_of_from`, `struct_ps_at_from`,
`field_spine_from`, `struct_proj_ps_from`, `replace_pis_pw`, `pis_to_lams_pw`,
`struct_proj_resid_p`, `struct_used_later_list`, `struct_proj_guard_at`,
`struct_proj_guards_from`, `struct_proj_bodies_go`, and the two structural
walks `has_loose_bvar`/`has_loose_bvar_b_spec`;
(b) a ten-armed `ExprWF` induction over a memoized walk —
`has_loose_bvar_b_go`/`_node` and `mentions_const_spec`/`_go`/`_node` — whose
shape is `Refine/ExprOps.lean`'s `instantiate1_go_refines` but whose arms have
to be replayed for each of the two short-circuit conventions.
The lemmas that only *combine* these (`params_of`, `struct_ps_at`,
`struct_fam`, `field_spine`, `struct_ctor_spine(_at)`, `struct_rule_body`,
`struct_elim_level`, `struct_fam_i`, `struct_ctor_resid_ok`,
`struct_motive_ty_i`, the four `struct_shape*`, the four `struct_parts_*`,
`struct_proj_ps`, `struct_proj_arg_p`, the two memo probes,
`has_loose_bvar_b_ins`, `has_loose_bvar_b`, `struct_used_later(_go)`,
`sort_get_d`, `struct_proj_guards`, `struct_proj_bodies`, `mentions_const`,
`nat_sub`) are proved.
-/
import ConRon.Refine.IndAbs
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.CoreKBase
import ConRon.Refine.CoreKVec
import ConRon.Refine.BasisNames

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.StructParts

/-! ## Two `Vec` readings this file needs (**to be unified into
`Refine/ExprOps.lean`** beside `vec_index_expr`) -/

/-- Indexing a well-formed `Vec<Name>`: the entry is well formed and the
abstracted list's `drop` peels it off. -/
theorem vec_index_name {ns : alloc.vec.Vec name.Name} {i : Std.Usize}
    {x : name.Name} (hns : NamesWF ns)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice name.Name) ns i
      = ok x) :
    i.val < ns.val.length ∧ NameWF x ∧
      (absNames ns).drop i.val = absName x :: (absNames ns).drop (i.val + 1) := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : i.val < ns.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : ns.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  refine ⟨hlt, hns x (by rw [← hx]; exact List.getElem_mem hlt), ?_⟩
  rw [absNames, List.drop_eq_getElem_cons (by simpa using hlt), List.getElem_map, hx]

/-- A `Vec<Level>` pushed on: the abstraction appends. -/
theorem absLevels_push {v w : alloc.vec.Vec level.Level} {x : level.Level}
    (h : v.push x = ok w) : absLevels w = absLevels v ++ [absLevel x] := by
  rw [absLevels, absLevels, vec_push_val h]; simp

/-- …and stays well formed. -/
theorem levelsWF_push {v w : alloc.vec.Vec level.Level} {x : level.Level}
    (hv : LevelsWF v) (hx : LevelWF x) (h : v.push x = ok w) : LevelsWF w := by
  intro u hu
  rw [vec_push_val h] at hu
  rcases List.mem_append.mp hu with h1 | h1
  · exact hv u h1
  · simp only [List.mem_singleton] at h1; rw [h1]; exact hx

/-! ## The small list helpers -/

/-- `ConLeche/Kernel/Inductives/StructParts.lean:82-86` (`lps.map .param`, the
level spine every generator's head carries) — `params_of_from` appends the
parameters from `i` on to its accumulator. -/
theorem params_of_from_refines (lps : alloc.vec.Vec name.Name) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec level.Level),
      lps.val.length - i.val ≤ k → NamesWF lps → LevelsWF out →
      inductives.struct_parts.params_of_from lps i out = ok v →
      absLevels v
          = absLevels out ++ ((absNames lps).drop i.val).map ConLeche.Level.param
        ∧ LevelsWF v := by
  intro k
  induction k with
  | zero =>
    intro i out v hk hlps hout h
    rw [inductives.struct_parts.params_of_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len lps by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (by simpa [absNames] using (show lps.val.length ≤ i.val by
      scalar_tac))]
    exact ⟨by simp, hout⟩
  | succ k ih =>
    intro i out v hk hlps hout h
    rw [inductives.struct_parts.params_of_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ lps.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len lps by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by simpa [absNames] using hi)]
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len lps by scalar_tac)] at h
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hlt, hnwf, hdrop⟩ := vec_index_name hlps hn
      have hn1e : n1 = n := (by simpa using hn1 : n = n1).symm
      rw [hn1e] at hl
      have hlv : absLevel l = .param (absName n) := Level.param_refines hl
      have hlwf : LevelWF l := LevelWF.param hnwf hl
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨habs, hwf⟩ :=
        ih i2 out1 v (by scalar_tac) hlps (levelsWF_push hout hlwf hout1) h
      refine ⟨?_, hwf⟩
      rw [habs, absLevels_push hout1, hlv, hi2v, hdrop]
      simp

/-- `params_of` is `lps.map .param`: the `i = 0`, `out = []` reading. -/
theorem params_of_refines {lps : alloc.vec.Vec name.Name}
    {v : alloc.vec.Vec level.Level} (hlps : NamesWF lps)
    (h : inductives.struct_parts.params_of lps = ok v) :
    absLevels v = (absNames lps).map ConLeche.Level.param ∧ LevelsWF v := by
  rw [inductives.struct_parts.params_of] at h
  have hout : LevelsWF (alloc.vec.Vec.new level.Level) := by
    intro u hu; simp [alloc.vec.Vec.new] at hu
  obtain ⟨habs, hwf⟩ :=
    params_of_from_refines lps lps.val.length 0#usize _ v (by scalar_tac) hlps hout h
  exact ⟨by simpa [absLevels, alloc.vec.Vec.new] using habs, hwf⟩

/-- `ConLeche/Kernel/Inductives/SumParts.lean:112-119` (`InductiveShape.withSort`),
`NativeParts.lean:562-614` (`nativeShape?`) and
`StructParts.lean:283-329` (`structPartsCore?`) — `level_is_prop` is the
`isProp` flag all three recognisers compute, `Level.isEquiv s .zero == some
true`, spelled as a three-way match because the `Option Bool` borrows the level
the caller then moves (task #14's rule).

**Owed to the siblings**: `IndSumParts.lean`'s `with_sort_refines` and
`IndNativeParts.lean`'s recogniser read exactly this equation. -/
theorem level_is_prop_refines {s : level.Level} {b : Bool} (hs : LevelWF s)
    (h : inductives.struct_parts.level_is_prop s = ok b) :
    b = (ConLeche.Level.isEquiv (absLevel s) .zero == some true) := by
  rw [inductives.struct_parts.level_is_prop] at h
  obtain ⟨u, hu, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hz : absLevel u = .zero := Level.zero_refines hu
  have heq : ConLeche.Level.isEquiv (absLevel s) .zero = o := by
    rw [← hz]; exact Level.is_equiv_refines hs (LevelWF.zero hu) ho
  rw [heq]
  cases o with
  | none => simpa using h.symm
  | some bb => cases bb <;> simp_all

/-! ## The generators (`StructParts.lean:82-211`) -/

/-- `ConLeche/Kernel/Inductives/StructParts.lean:134-137` — `struct_ps_at_from`
is the index recursion behind `structPsAt`, with the port's accumulator in
front of the entries Lean's `List.map` produces (deviation 3). -/
theorem struct_ps_at_from_refines (o n_p : Std.U64) :
    ∀ (k : Std.U64) (out v : alloc.vec.Vec expr.Expr), ExprsWF out →
      inductives.struct_parts.struct_ps_at_from o n_p k out = ok v →
      absExprs v = absExprs out
          ++ (List.range' k.val (n_p.val - k.val)).map
              (fun j => ConLeche.Expr.bvar (o.val + n_p.val - 1 - j))
        ∧ ExprsWF v := by
  intro k
  generalize hd : n_p.val - k.val = d
  induction d using Nat.strong_induction_on generalizing k with
  | _ d ih =>
    intro out v hout h
    rw [inductives.struct_parts.struct_ps_at_from.eq_def] at h
    by_cases hk : k.val ≥ n_p.val
    · rw [if_pos (show k ≥ n_p by scalar_tac), Result.ok.injEq] at h
      subst h
      have hz : d = 0 := by omega
      subst hz
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ k ≥ n_p by scalar_tac)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = o.val + n_p.val := HashMap.uscalar_add_eq hi
      have hi1v : i1.val = i.val - 1 := HashMap.uscalar_sub_eq hi1
      have hi2v : i2.val = i1.val - k.val := HashMap.uscalar_sub_eq hi2
      have hi3v : i3.val = k.val + 1 := HashMap.uscalar_add_eq hi3
      have hsplit : d = (n_p.val - (k.val + 1)) + 1 := by omega
      subst hsplit
      obtain ⟨habs, hwf⟩ := ih (n_p.val - (k.val + 1)) (by omega) i3 (by rw [hi3v])
        out1 v (ExprOps.exprsWF_push hout (Expr.bvar_wf he) hout1) h
      refine ⟨?_, hwf⟩
      rw [habs, ExprOps.absExprs_push hout1, Expr.bvar_refines he, hi2v, hi1v, hiv,
        hi3v, List.range'_succ]
      simp

/-- `ConLeche/Kernel/Inductives/StructParts.lean:134-137` — `struct_ps_at`
refines `structPsAt`: the parameter variables seen from under `o` extra
binders. -/
theorem struct_ps_at_refines {o n_p : Std.U64} {v : alloc.vec.Vec expr.Expr}
    (h : inductives.struct_parts.struct_ps_at o n_p = ok v) :
    absExprs v = ConLeche.structPsAt o.val n_p.val ∧ ExprsWF v := by
  rw [inductives.struct_parts.struct_ps_at] at h
  obtain ⟨habs, hwf⟩ :=
    struct_ps_at_from_refines o n_p 0#u64 _ v ExprOps.exprsWF_new h
  refine ⟨?_, hwf⟩
  rw [habs]
  simp [ConLeche.structPsAt, List.range_eq_range', alloc.vec.Vec.new, absExprs]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:82-86` — `struct_fam` refines
`structFam`: the type former applied to its parameter variables. -/
theorem struct_fam_refines {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p o : Std.U64} {e : expr.Expr} (ht : NameWF t) (hlps : NamesWF lps)
    (h : inductives.struct_parts.struct_fam t lps n_p o = ok e) :
    absExpr e = ConLeche.structFam (absName t) (absNames lps) n_p.val o.val
      ∧ ExprWF e := by
  rw [inductives.struct_parts.struct_fam] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
  have hne : n = t := (by simpa using hn : t = n).symm
  rw [hne] at hhead
  obtain ⟨husabs, huswf⟩ := params_of_refines hlps hus
  obtain ⟨hv1abs, hv1wf⟩ := struct_ps_at_refines hv1
  obtain ⟨habs, hwf⟩ :=
    ExprOps.mk_app_n_refines (Expr.mk_const_wf ht huswf hhead) hv1wf h
  refine ⟨?_, hwf⟩
  rw [habs, Expr.mk_const_refines hhead, husabs, hv1abs, ConLeche.structFam,
    ConLeche.structPsAt]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:88-94` — `field_spine_from` is
the index recursion behind the field spine `(List.range m).map fun j =>
.bvar (m - 1 - j)`, accumulator in front. -/
theorem field_spine_from_refines (m : Std.U64) :
    ∀ (k : Std.U64) (out v : alloc.vec.Vec expr.Expr), ExprsWF out →
      inductives.struct_parts.field_spine_from m k out = ok v →
      absExprs v = absExprs out
          ++ (List.range' k.val (m.val - k.val)).map
              (fun j => ConLeche.Expr.bvar (m.val - 1 - j))
        ∧ ExprsWF v := by
  intro k
  generalize hd : m.val - k.val = d
  induction d using Nat.strong_induction_on generalizing k with
  | _ d ih =>
    intro out v hout h
    rw [inductives.struct_parts.field_spine_from.eq_def] at h
    by_cases hk : k.val ≥ m.val
    · rw [if_pos (show k ≥ m by scalar_tac), Result.ok.injEq] at h
      subst h
      have hz : d = 0 := by omega
      subst hz
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ k ≥ m by scalar_tac)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = m.val - 1 := HashMap.uscalar_sub_eq hi
      have hi1v : i1.val = i.val - k.val := HashMap.uscalar_sub_eq hi1
      have hi2v : i2.val = k.val + 1 := HashMap.uscalar_add_eq hi2
      have hsplit : d = (m.val - (k.val + 1)) + 1 := by omega
      subst hsplit
      obtain ⟨habs, hwf⟩ := ih (m.val - (k.val + 1)) (by omega) i2 (by rw [hi2v])
        out1 v (ExprOps.exprsWF_push hout (Expr.bvar_wf he) hout1) h
      refine ⟨?_, hwf⟩
      rw [habs, ExprOps.absExprs_push hout1, Expr.bvar_refines he, hi1v, hiv,
        hi2v, List.range'_succ]
      simp

/-- `ConLeche/Kernel/Inductives/StructParts.lean:88-94` — `field_spine` is the
field spine `(List.range m).map fun j => .bvar (m - 1 - j)` that every
constructor spine and rule body appends (`structCtorSpine`, `structRuleBody`,
and at a reflexive field's telescope length `NativeParts.lean`'s
`structTeleVars`). -/
theorem field_spine_refines {m : Std.U64} {v : alloc.vec.Vec expr.Expr}
    (h : inductives.struct_parts.field_spine m = ok v) :
    absExprs v = (List.range m.val).map (fun j => ConLeche.Expr.bvar (m.val - 1 - j))
      ∧ ExprsWF v := by
  rw [inductives.struct_parts.field_spine] at h
  obtain ⟨habs, hwf⟩ := field_spine_from_refines m 0#u64 _ v ExprOps.exprsWF_new h
  refine ⟨?_, hwf⟩
  rw [habs]
  simp [List.range_eq_range', alloc.vec.Vec.new, absExprs]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:144-150` —
`struct_ctor_spine_at` refines `structCtorSpineAt`: the constructor applied to
the parameter and field variables under `o` binders. -/
theorem struct_ctor_spine_at_refines {c : name.Name}
    {lps : alloc.vec.Vec name.Name} {o n_p n_f : Std.U64} {e : expr.Expr}
    (hc : NameWF c) (hlps : NamesWF lps)
    (h : inductives.struct_parts.struct_ctor_spine_at c lps o n_p n_f = ok e) :
    absExpr e
        = ConLeche.structCtorSpineAt (absName c) (absNames lps) o.val n_p.val n_f.val
      ∧ ExprWF e := by
  rw [inductives.struct_parts.struct_ctor_spine_at] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
  have hne : n = c := (by simpa using hn : c = n).symm
  rw [hne] at hhead
  obtain ⟨husabs, huswf⟩ := params_of_refines hlps hus
  obtain ⟨hv1abs, hv1wf⟩ := struct_ps_at_refines hv1
  obtain ⟨hv2abs, hv2wf⟩ := field_spine_refines hv2
  obtain ⟨hargsabs, hargswf⟩ := CoreK.append_exprs_refines hv1wf hv2wf hargs
  obtain ⟨habs, hwf⟩ :=
    ExprOps.mk_app_n_refines (Expr.mk_const_wf hc huswf hhead) hargswf h
  refine ⟨?_, hwf⟩
  have hiv : i.val = o.val + n_f.val := HashMap.uscalar_add_eq hi
  rw [habs, Expr.mk_const_refines hhead, husabs, hargsabs, hv1abs, hv2abs, hiv,
    ConLeche.structCtorSpineAt]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:88-94` — `struct_ctor_spine`
refines `structCtorSpine`, which is `structCtorSpineAt` at `o = 1`
(con-leche's `structCtorSpine_eq_at`, a `Nat`-arithmetic identity on the
parameter spine: `1 + nF + nP - 1 - k = nF + nP - k`). -/
theorem struct_ctor_spine_refines {c : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f : Std.U64} {e : expr.Expr} (hc : NameWF c) (hlps : NamesWF lps)
    (h : inductives.struct_parts.struct_ctor_spine c lps n_p n_f = ok e) :
    absExpr e = ConLeche.structCtorSpine (absName c) (absNames lps) n_p.val n_f.val
      ∧ ExprWF e := by
  rw [inductives.struct_parts.struct_ctor_spine] at h
  obtain ⟨habs, hwf⟩ := struct_ctor_spine_at_refines hc hlps h
  refine ⟨?_, hwf⟩
  rw [habs, ConLeche.structCtorSpineAt, ConLeche.structCtorSpine,
    ConLeche.structPsAt]
  congr 2
  · refine List.map_congr_left ?_
    intro k _
    congr 1
    simp only [show ((1#u64 : Std.U64)).val = 1 from rfl]
    omega

/-- `ConLeche/Kernel/Inductives/StructParts.lean:96-99` — `struct_rule_body`
refines `structRuleBody`: the minor premise applied to the field variables. -/
theorem struct_rule_body_refines {n_f : Std.U64} {e : expr.Expr}
    (h : inductives.struct_parts.struct_rule_body n_f = ok e) :
    absExpr e = ConLeche.structRuleBody n_f.val ∧ ExprWF e := by
  rw [inductives.struct_parts.struct_rule_body] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hvabs, hvwf⟩ := field_spine_refines hv
  obtain ⟨habs, hwf⟩ := ExprOps.mk_app_n_refines (Expr.bvar_wf hb) hvwf h
  exact ⟨by rw [habs, Expr.bvar_refines hb, hvabs, ConLeche.structRuleBody], hwf⟩

/-- `ConLeche/Kernel/Inductives/StructParts.lean:139-142` —
`struct_elim_level` refines `structElimLevel`: the fresh parameter at the large
eliminator, `zero` at the small one. -/
theorem struct_elim_level_refines {elim : name.Name} {large : Bool}
    {u : level.Level} (helim : NameWF elim)
    (h : inductives.struct_parts.struct_elim_level elim large = ok u) :
    absLevel u = ConLeche.structElimLevel (absName elim) large ∧ LevelWF u := by
  rw [inductives.struct_parts.struct_elim_level] at h
  cases large with
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    exact ⟨by rw [Level.zero_refines h, ConLeche.structElimLevel]; simp,
      LevelWF.zero h⟩
  | true =>
    simp only [if_true] at h
    obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
    have hne : n = elim := (by simpa using hn : elim = n).symm
    rw [hne] at h
    exact ⟨by rw [Level.param_refines h, ConLeche.structElimLevel]; simp,
      LevelWF.param helim h⟩

/-- `ConLeche/Kernel/Inductives/StructParts.lean:152-158` — `replace_pis_pw`
refines `Expr.replacePisPw`: the body under the first `k` `∀`-binders replaced,
their codomain data reset to `pw`, the domains kept. -/
theorem replace_pis_pw_refines_aux (N : Nat) :
    ∀ (pw : prop_when.PropWhen) (k : Std.U64) (e b : expr.Expr)
      (o : Option expr.Expr),
      k.val = N → PropWhenWF pw → ExprWF e → ExprWF b →
      inductives.struct_parts.replace_pis_pw pw k e b = ok o →
      o.map absExpr
          = ConLeche.Expr.replacePisPw (absPropWhen pw) k.val (absExpr e) (absExpr b)
        ∧ ∀ r, o = some r → ExprWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro pw k e b o hN hpw he hb h
    rw [inductives.struct_parts.replace_pis_pw.eq_def] at h
    split at h
    · rename_i hk0
      have hkv : k.val = 0 := by rw [hk0]; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr, hkv]
      exact ⟨by simp [ConLeche.Expr.replacePisPw], fun r hr' => by
        simp only [Option.some.injEq] at hr'; rw [← hr']; exact hb⟩
    · rename_i hk0
      obtain ⟨n, hn⟩ : ∃ n, k.val = n + 1 := by
        have : k.val ≠ 0 := fun hc => hk0 (Std.UScalar.eq_of_val_eq (by rw [hc]; scalar_tac))
        exact ⟨k.val - 1, by omega⟩
      cases he with
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
        obtain ⟨i, hi, o1, ho1, h⟩ := h
        have hiv : i.val = n := by rw [HashMap.uscalar_sub_eq hi, hn]; scalar_tac
        obtain ⟨habs, hwf⟩ := ih n (by omega) pw i bo b o1 hiv hpw hbo hb ho1
        rw [hiv] at habs
        cases o1 with
        | none =>
          simp only [Option.map_none] at habs
          simp only [Result.ok.injEq] at h
          rw [← h, hn]
          refine ⟨?_, by simp⟩
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.replacePisPw, ← habs]
          simp
        | some r0 =>
          simp only [Option.map_some] at habs
          simp only [bind_eq_ok_iff] at h
          obtain ⟨c, hdup, pw1, hpw1, bm, hbm, e2, he2, hres⟩ := h
          rw [Expr.dup_eq hdup] at he2
          have hpw1e : pw1 = pw := PropWhen.dup_eq hpw1
          rw [hpw1e, ExprOps.binder_meta_eq pw] at hbm
          have hbme : bm = ⟨pw⟩ := (Result.ok_injective hbm).symm
          rw [hbme] at he2
          simp only [Result.ok.injEq] at hres
          rw [← hres, hn]
          refine ⟨?_, fun r hr' => by
            simp only [Option.some.injEq] at hr'
            rw [← hr']
            exact Expr.forall_e_wf hty (hwf r0 rfl) hpw he2⟩
          simp only [Option.map_some, absExpr_mk, absExprKind,
            ConLeche.Expr.replacePisPw, Expr.forall_e_refines he2, ← habs]
          simp [absBinderMeta]
      | @bvar i e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @mk_const n2 us e hn2 hus h1 =>
        obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @proj s i x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩

/-- `replace_pis_pw` at its own statement. -/
theorem replace_pis_pw_refines {pw : prop_when.PropWhen} {k : Std.U64}
    {e b : expr.Expr} {o : Option expr.Expr} (hpw : PropWhenWF pw)
    (he : ExprWF e) (hb : ExprWF b)
    (h : inductives.struct_parts.replace_pis_pw pw k e b = ok o) :
    o.map absExpr
        = ConLeche.Expr.replacePisPw (absPropWhen pw) k.val (absExpr e) (absExpr b)
      ∧ ∀ r, o = some r → ExprWF r :=
  replace_pis_pw_refines_aux k.val pw k e b o rfl hpw he hb h

/-- `ConLeche/Kernel/Inductives/StructParts.lean:160-167` — `pis_to_lams_pw`
refines `Expr.pisToLamsPw`: the first `k` `∀`-binders converted to `λ`-binders
with datum `pw`. -/
theorem pis_to_lams_pw_refines_aux (N : Nat) :
    ∀ (pw : prop_when.PropWhen) (k : Std.U64) (e b : expr.Expr)
      (o : Option expr.Expr),
      k.val = N → PropWhenWF pw → ExprWF e → ExprWF b →
      inductives.struct_parts.pis_to_lams_pw pw k e b = ok o →
      o.map absExpr
          = ConLeche.Expr.pisToLamsPw (absPropWhen pw) k.val (absExpr e) (absExpr b)
        ∧ ∀ r, o = some r → ExprWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro pw k e b o hN hpw he hb h
    rw [inductives.struct_parts.pis_to_lams_pw.eq_def] at h
    split at h
    · rename_i hk0
      have hkv : k.val = 0 := by rw [hk0]; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr, hkv]
      exact ⟨by simp [ConLeche.Expr.pisToLamsPw], fun r hr' => by
        simp only [Option.some.injEq] at hr'; rw [← hr']; exact hb⟩
    · rename_i hk0
      obtain ⟨n, hn⟩ : ∃ n, k.val = n + 1 := by
        have : k.val ≠ 0 := fun hc => hk0 (Std.UScalar.eq_of_val_eq (by rw [hc]; scalar_tac))
        exact ⟨k.val - 1, by omega⟩
      cases he with
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
        obtain ⟨i, hi, o1, ho1, h⟩ := h
        have hiv : i.val = n := by rw [HashMap.uscalar_sub_eq hi, hn]; scalar_tac
        obtain ⟨habs, hwf⟩ := ih n (by omega) pw i bo b o1 hiv hpw hbo hb ho1
        rw [hiv] at habs
        cases o1 with
        | none =>
          simp only [Option.map_none] at habs
          simp only [Result.ok.injEq] at h
          rw [← h, hn]
          refine ⟨?_, by simp⟩
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.pisToLamsPw, ← habs]
          simp
        | some r0 =>
          simp only [Option.map_some] at habs
          simp only [bind_eq_ok_iff] at h
          obtain ⟨c, hdup, pw1, hpw1, bm, hbm, e2, he2, hres⟩ := h
          rw [Expr.dup_eq hdup] at he2
          have hpw1e : pw1 = pw := PropWhen.dup_eq hpw1
          rw [hpw1e, ExprOps.binder_meta_eq pw] at hbm
          have hbme : bm = ⟨pw⟩ := (Result.ok_injective hbm).symm
          rw [hbme] at he2
          simp only [Result.ok.injEq] at hres
          rw [← hres, hn]
          refine ⟨?_, fun r hr' => by
            simp only [Option.some.injEq] at hr'
            rw [← hr']
            exact Expr.lam_wf hty (hwf r0 rfl) hpw he2⟩
          simp only [Option.map_some, absExpr_mk, absExprKind,
            ConLeche.Expr.pisToLamsPw, Expr.lam_refines he2, ← habs]
          simp [absBinderMeta]
      | @bvar i e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @mk_const n2 us e hn2 hus h1 =>
        obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @proj s i x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩

/-- `pis_to_lams_pw` at its own statement. -/
theorem pis_to_lams_pw_refines {pw : prop_when.PropWhen} {k : Std.U64}
    {e b : expr.Expr} {o : Option expr.Expr} (hpw : PropWhenWF pw)
    (he : ExprWF e) (hb : ExprWF b)
    (h : inductives.struct_parts.pis_to_lams_pw pw k e b = ok o) :
    o.map absExpr
        = ConLeche.Expr.pisToLamsPw (absPropWhen pw) k.val (absExpr e) (absExpr b)
      ∧ ∀ r, o = some r → ExprWF r :=
  pis_to_lams_pw_refines_aux k.val pw k e b o rfl hpw he hb h


/-- `ConLeche/Kernel/Inductives/StructParts.lean:189-194` — `struct_fam_i`
refines `structFamI`: the family applied to its parameter *and* index
variables, `e` extra binders between them and `o` below the index frame. -/
theorem struct_fam_i_refines {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_idx e o : Std.U64} {r : expr.Expr} (ht : NameWF t) (hlps : NamesWF lps)
    (h : inductives.struct_parts.struct_fam_i t lps n_p n_idx e o = ok r) :
    absExpr r
        = ConLeche.structFamI (absName t) (absNames lps) n_p.val n_idx.val e.val o.val
      ∧ ExprWF r := by
  rw [inductives.struct_parts.struct_fam_i] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
  have hne : n = t := (by simpa using hn : t = n).symm
  rw [hne] at hhead
  obtain ⟨husabs, huswf⟩ := params_of_refines hlps hus
  obtain ⟨hv1abs, hv1wf⟩ := struct_ps_at_refines hv1
  obtain ⟨hv2abs, hv2wf⟩ := struct_ps_at_refines hv2
  obtain ⟨hargsabs, hargswf⟩ := CoreK.append_exprs_refines hv1wf hv2wf hargs
  obtain ⟨habs, hwf⟩ :=
    ExprOps.mk_app_n_refines (Expr.mk_const_wf ht huswf hhead) hargswf h
  refine ⟨?_, hwf⟩
  have hiv : i.val = o.val + e.val := HashMap.uscalar_add_eq hi
  have hi1v : i1.val = i.val + n_idx.val := HashMap.uscalar_add_eq hi1
  rw [habs, Expr.mk_const_refines hhead, husabs, hargsabs, hv1abs, hv2abs, hi1v,
    hiv, ConLeche.structFamI]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:196-202` —
`struct_ctor_resid_ok` refines `structCtorResidOk`: the family at exactly the
parameter variables followed by `nIdx` index expressions.  The cited `&&`
cascade is an `if` nest in the port (task #3's pattern 9), keeping the
short-circuit order. -/
theorem struct_ctor_resid_ok_refines {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p o n_idx : Std.U64} {cbody : expr.Expr}
    {b : Bool} (ht : NameWF t) (hlps : NamesWF lps) (hcbody : ExprWF cbody)
    (h : inductives.struct_parts.struct_ctor_resid_ok t lps n_p o n_idx cbody = ok b) :
    b = ConLeche.structCtorResidOk (absName t) (absNames lps) n_p.val o.val
      n_idx.val (absExpr cbody) := by
  rw [inductives.struct_parts.struct_ctor_resid_ok] at h
  obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨expected, hexp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
  have hne : n = t := (by simpa using hn : t = n).symm
  rw [hne] at hexp
  obtain ⟨husabs, huswf⟩ := params_of_refines hlps hus
  obtain ⟨hheadabs, hheadwf⟩ := ExprOps.get_app_fn_refines hcbody hhead
  have hb0e : b0 = decide ((absExpr cbody).getAppFn
      = ConLeche.Expr.const (absName t) ((absNames lps).map ConLeche.Level.param)) := by
    rw [Expr.beq_refines hheadwf (Expr.mk_const_wf ht huswf hexp) hb0, hheadabs,
      Expr.mk_const_refines hexp, husabs]
  rw [ConLeche.structCtorResidOk]
  cases hb0d : b0 with
  | false =>
    rw [hb0d] at h hb0e
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h]
    have : ¬ ((absExpr cbody).getAppFn
        = ConLeche.Expr.const (absName t) ((absNames lps).map ConLeche.Level.param)) :=
      of_decide_eq_false hb0e.symm
    simp [this]
  | true =>
    rw [hb0d] at h hb0e
    simp only [if_true] at h
    have hheq : (absExpr cbody).getAppFn
        = ConLeche.Expr.const (absName t) ((absNames lps).map ConLeche.Level.param) :=
      of_decide_eq_true hb0e.symm
    obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hargsabs, hargswf⟩ := ExprOps.get_app_args_refines hcbody hargs
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi1v : i1.val = args.val.length := by
      have hlv := alloc.vec.Vec.len_val args
      have hc : (Std.UScalar.cast .U64 args.len).val = args.len.val :=
        ExprOps.usize_cast_u64_val _
      simp only [lift, Result.ok.injEq] at hi1
      rw [← hi1, hc, hlv]
    have hi2v : i2.val = n_p.val + n_idx.val := HashMap.uscalar_add_eq hi2
    have hlen : ((absExpr cbody).getAppArgs).length = args.val.length := by
      rw [← hargsabs]; simp [absExprs]
    rw [hheq]
    simp only [beq_self_eq_true, Bool.true_and, hlen]
    by_cases hlend : args.val.length = n_p.val + n_idx.val
    · rw [if_pos (show i1 = i2 by scalar_tac)] at h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
      have hnp : n_p.val ≤ Std.Usize.max := by
        have hb : args.val.length ≤ Std.Usize.max := by scalar_tac
        omega
      have hi3v : i3.val = n_p.val := by
        simp only [lift, Result.ok.injEq] at hi3
        rw [← hi3]
        exact ExprOps.u64_cast_usize_val hnp
      obtain ⟨hv1abs, hv1wf⟩ := ExprOps.take_exprs_refines hargswf hv1
      obtain ⟨hv2abs, hv2wf⟩ := struct_ps_at_refines hv2
      rw [Env.exprs_beq_refines hv1wf hv2wf h, hv1abs, hv2abs, hargsabs, hi3v]
      simp only [hlend]
      refine Bool.eq_iff_iff.mpr ?_
      simp
    · rw [if_neg (show ¬ i1 = i2 by scalar_tac), Result.ok.injEq] at h
      rw [← h]
      simp [hlend]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:204-211` —
`struct_motive_ty_i` refines `structMotiveTyI`: the motive's type
`∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ` over the former's index telescope. -/
theorem struct_motive_ty_i_refines {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_idx : Std.U64} {l : level.Level} {itele : expr.Expr}
    {o : Option expr.Expr} (ht : NameWF t) (hlps : NamesWF lps) (hl : LevelWF l)
    (hitele : ExprWF itele)
    (h : inductives.struct_parts.struct_motive_ty_i t lps n_p n_idx l itele = ok o) :
    o.map absExpr
        = ConLeche.structMotiveTyI (absName t) (absNames lps) n_p.val n_idx.val
            (absLevel l) (absExpr itele)
      ∧ ∀ r, o = some r → ExprWF r := by
  rw [inductives.struct_parts.struct_motive_ty_i] at h
  obtain ⟨fam, hfam, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨l1, hl1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pw, hpw, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨body, hbody, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hfamabs, hfamwf⟩ := struct_fam_i_refines ht hlps hfam
  have hl1e : l1 = l := (by simpa using hl1 : l = l1).symm
  rw [hl1e] at hs
  have hpwabs : absPropWhen pw = ConLeche.PropWhen.never := PropWhen.never_refines hpw
  have hpwwf : PropWhenWF pw := PropWhen.never_wf hpw
  have hbmabs : absBinderMeta bm = ⟨ConLeche.PropWhen.never⟩ := by
    rw [ExprOps.binder_meta_eq pw] at hbm
    rw [← Result.ok_injective hbm, absBinderMeta, hpwabs]
  have hbodywf : ExprWF body :=
    Expr.forall_e_wf hfamwf (Expr.sort_wf hl hs) (by
      rw [ExprOps.binder_meta_eq pw] at hbm
      rw [← Result.ok_injective hbm]; exact hpwwf) hbody
  obtain ⟨habs, hwf⟩ := replace_pis_pw_refines hpwwf hitele hbodywf h
  refine ⟨?_, hwf⟩
  rw [habs, hpwabs, Expr.forall_e_refines hbody, hfamabs, Expr.sort_refines hs,
    hbmabs, ConLeche.structMotiveTyI]
  simp


/-! ## `StructParts` and its recogniser (`StructParts.lean:213-333`)

The record is `IndAbs.absStructParts`/`IndAbs.StructPartsWF` (the abstraction
and well-formedness of `struct_parts::StructParts`, the 18th item of the
module).  Nothing in the shipped install path consumes it — the simple
structure route was deleted at con-leche's task #210 Part C — so the
recogniser below is its only producer. -/

/-- `ConLeche/Kernel/Inductives/StructParts.lean:246-281` —
`struct_shape_motive` refines `structShape`'s motive-binder clause: the
motive's codomain is `Sort elim` at the large eliminator and `Prop` at the
small one, and its own major domain is the family at the parameters.  Split
off in the port so that every `else` arm of the cited `&&` cascade stays a
tail position (task #18's pattern 3). -/
theorem struct_shape_motive_refines {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {elim : name.Name} {large : Bool}
    {n_p : Std.U64} {rbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {b : Bool} (ht : NameWF t) (hlps : NamesWF lps) (helim : NameWF elim)
    (hrbs : ExprOps.BindersWF rbs)
    (h : inductives.struct_parts.struct_shape_motive t lps elim large n_p rbs
        = ok b) :
    b = (match (ExprOps.absBinders rbs)[n_p.val]? with
      | some (.forallE mmaj (.sort s') _, _) =>
        (if large then s' == ConLeche.Level.param (absName elim)
         else s' == ConLeche.Level.zero)
          && mmaj == ConLeche.structFam (absName t) (absNames lps) n_p.val 0
      | _ => false) := by
  -- the bounds test, the two node reads and the two `beq`s
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:246-281` —
`struct_shape_minor` refines `structShape`'s minor-binder clause: the minor's
own `nF`-binder telescope ends in `motive (C p⃗ f⃗)`. -/
theorem struct_shape_minor_refines {c : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f : Std.U64}
    {rbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {b : Bool}
    (hc : NameWF c) (hlps : NamesWF lps) (hrbs : ExprOps.BindersWF rbs)
    (h : inductives.struct_parts.struct_shape_minor c lps n_p n_f rbs = ok b) :
    b = (match (ExprOps.absBinders rbs)[n_p.val + 1]? with
      | some (mindom, _) =>
        match mindom.stripPis n_f.val with
        | some (_, mbody) =>
          mbody == ConLeche.Expr.app (.bvar n_f.val)
            (ConLeche.structCtorSpine (absName c) (absNames lps) n_p.val n_f.val)
        | none => false
      | none => false) := by
  -- the bounds test, `strip_pis` and the `beq`
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:246-281` —
`struct_shape_major` refines `structShape`'s major-binder clause: its domain is
the family at the parameters, two binders down. -/
theorem struct_shape_major_refines {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p : Std.U64}
    {rbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {b : Bool}
    (ht : NameWF t) (hlps : NamesWF lps) (hrbs : ExprOps.BindersWF rbs)
    (h : inductives.struct_parts.struct_shape_major t lps n_p rbs = ok b) :
    b = (match (ExprOps.absBinders rbs)[n_p.val + 2]? with
      | some (majdom, _) =>
        majdom == ConLeche.structFam (absName t) (absNames lps) n_p.val 2
      | none => false) := by
  -- the bounds test and the `beq`
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:246-281` — `struct_shape`
refines `structShape`: the *shape* facts the model reads off the stored
(annotated) types, everything annotation cannot change, checked on both the raw
block (recognition) and the annotated constants (install). -/
theorem struct_shape_refines {t c : name.Name} {lps : alloc.vec.Vec name.Name}
    {elim : name.Name} {large : Bool} {n_p n_f : Std.U64}
    {tty cty rty : expr.Expr} {b : Bool}
    (ht : NameWF t) (hc : NameWF c) (hlps : NamesWF lps) (helim : NameWF elim)
    (htty : ExprWF tty) (hcty : ExprWF cty) (hrty : ExprWF rty)
    (h : inductives.struct_parts.struct_shape t c lps elim large n_p n_f tty cty rty
        = ok b) :
    b = ConLeche.structShape (absName t) (absName c) (absNames lps)
      (absName elim) large n_p.val n_f.val (absExpr tty) (absExpr cty)
      (absExpr rty) := by
  -- the three `strip_pis`, the `.sort` read and the three clauses above
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:283-329` —
`struct_parts_front_ok` refines the block-independent front guards of
`structPartsCore?`: the recursor's name, the shared level parameters, the three
reserved-name exclusions, the two argument sums and the single rule's
constructor, field count and λ-stripped body.  Split off in the port so that
the cited `&&` cascade's arms stay tail positions. -/
theorem struct_parts_front_ok_refines {cv_t cv_c cv_r : env.ConstantVal}
    {n_p n_f m_i r_p : Std.U64} {rule : env.RecRule} {b : Bool}
    (hcvt : ConstantValWF cv_t) (hcvc : ConstantValWF cv_c)
    (hcvr : ConstantValWF cv_r) (hrule : RecRuleWF rule)
    (h : inductives.struct_parts.struct_parts_front_ok cv_t cv_c cv_r n_p n_f
        m_i r_p rule = ok b) :
    b = ((absName cv_r.name == (absName cv_t.name).str "rec")
      && (absNames cv_c.level_params == absNames cv_t.level_params)
      && (ConLeche.reservedBasisNames.contains (absName cv_t.name) == false)
      && (ConLeche.reservedBasisNames.contains (absName cv_c.name) == false)
      && (ConLeche.reservedBasisNames.contains (absName cv_r.name) == false)
      && (m_i.val == n_p.val + 2) && (r_p.val == n_p.val + 2)
      && ((absRecRule rule).ctor == absName cv_c.name)
      && ((absRecRule rule).nfields == n_f.val)
      && (match (absRecRule rule).rhs.stripLams (n_p.val + 2 + n_f.val) with
          | some (_, rbody) => rbody == ConLeche.structRuleBody n_f.val
          | none => false)) := by
  -- the pinned `.str "rec"` (`str_lit_step`), `reservedBasisNames`, `strip_lams`
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:283-329` —
`struct_parts_large` refines `structPartsCore?`'s `large?` reading: a fresh
elimination level parameter in front of the block's own, with the
large-eliminator shape confirmed.  Lean's `match cvR.levelParams with
| elim :: relps` is a length test and a spine copy in the port (task #25). -/
theorem struct_parts_large_refines {cv_t cv_c cv_r : env.ConstantVal}
    {n_p n_f : Std.U64} {o : Option name.Name}
    (hcvt : ConstantValWF cv_t) (hcvc : ConstantValWF cv_c)
    (hcvr : ConstantValWF cv_r)
    (h : inductives.struct_parts.struct_parts_large cv_t cv_c cv_r n_p n_f = ok o) :
    o.map absName = (match absNames cv_r.level_params with
      | elim :: relps =>
        if relps == absNames cv_t.level_params
            && !(absNames cv_t.level_params).contains elim
            && ConLeche.structShape (absName cv_t.name) (absName cv_c.name)
                (absNames cv_t.level_params) elim true n_p.val n_f.val
                (absExpr cv_t.ty) (absExpr cv_c.ty) (absExpr cv_r.ty) then
          some elim
        else none
      | [] => none)
    ∧ ∀ n, o = some n → NameWF n := by
  -- the length test, `prop_when::append_from`, `names_beq`, `contains`, the shape
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:283-329` —
`struct_parts_small_ok` refines `structPartsCore?`'s `large? = none` branch
guard: the recursor carries the block's own level parameters and the
small-eliminator shape holds. -/
theorem struct_parts_small_ok_refines {cv_t cv_c cv_r : env.ConstantVal}
    {n_p n_f : Std.U64} {b : Bool}
    (hcvt : ConstantValWF cv_t) (hcvc : ConstantValWF cv_c)
    (hcvr : ConstantValWF cv_r)
    (h : inductives.struct_parts.struct_parts_small_ok cv_t cv_c cv_r n_p n_f
        = ok b) :
    b = ((absNames cv_r.level_params == absNames cv_t.level_params)
      && ConLeche.structShape (absName cv_t.name) (absName cv_c.name)
          (absNames cv_t.level_params) .anonymous false n_p.val n_f.val
          (absExpr cv_t.ty) (absExpr cv_c.ty) (absExpr cv_r.ty)) := by
  -- `names_beq` and `struct_shape_refines` at `.anonymous`
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:283-329` —
`struct_parts_core` refines `structPartsCore?`: a recognised direct
simple-structure block.  `none` means "not this class" — the caller falls
through to the modeled path, so this is never an error source.  The port's
three-element list pattern is an index match on a `Vec` and Lean's `[rule]` a
length test (task #25). -/
theorem struct_parts_core_refines {block : alloc.vec.Vec env.ConstantInfo}
    {o : Option inductives.struct_parts.StructParts}
    (hblock : ConstantInfosWF block)
    (h : inductives.struct_parts.struct_parts_core block = ok o) :
    o.map IndAbs.absStructParts
        = ConLeche.structPartsCore? (absConstantInfos block)
      ∧ ∀ p, o = some p → IndAbs.StructPartsWF p := by
  -- the three `ConstantInfo` matches, the front guards, `strip_pis`, the two
  -- eliminator branches
  sorry

/-! ## The projection table's pieces (`StructParts.lean:335-356`) -/

/-- `ConLeche/Kernel/Inductives/StructParts.lean:331-337` —
`struct_proj_ps_from` is the index recursion behind `structProjPs`,
accumulator in front. -/
theorem struct_proj_ps_from_refines (n_p : Std.U64) :
    ∀ (k : Std.U64) (out v : alloc.vec.Vec expr.Expr), ExprsWF out →
      inductives.struct_parts.struct_proj_ps_from n_p k out = ok v →
      absExprs v = absExprs out
          ++ (List.range' k.val (n_p.val - k.val)).map
              (fun j => ConLeche.Expr.bvar (n_p.val - j))
        ∧ ExprsWF v := by
  intro k
  generalize hd : n_p.val - k.val = d
  induction d using Nat.strong_induction_on generalizing k with
  | _ d ih =>
    intro out v hout h
    rw [inductives.struct_parts.struct_proj_ps_from.eq_def] at h
    by_cases hk : k.val ≥ n_p.val
    · rw [if_pos (show k ≥ n_p by scalar_tac), Result.ok.injEq] at h
      subst h
      have hz : d = 0 := by omega
      subst hz
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ k ≥ n_p by scalar_tac)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = n_p.val - k.val := HashMap.uscalar_sub_eq hi
      have hi1v : i1.val = k.val + 1 := HashMap.uscalar_add_eq hi1
      have hsplit : d = (n_p.val - (k.val + 1)) + 1 := by omega
      subst hsplit
      obtain ⟨habs, hwf⟩ := ih (n_p.val - (k.val + 1)) (by omega) i1 (by rw [hi1v])
        out1 v (ExprOps.exprsWF_push hout (Expr.bvar_wf he) hout1) h
      refine ⟨?_, hwf⟩
      rw [habs, ExprOps.absExprs_push hout1, Expr.bvar_refines he, hiv, hi1v,
        List.range'_succ]
      simp

/-- `ConLeche/Kernel/Inductives/StructParts.lean:331-337` — `struct_proj_ps`
refines `structProjPs`: the parameter spine of the generated projection types,
spelled at the frame of the final `∀ p⃗ (t : T p⃗), _` telescope. -/
theorem struct_proj_ps_refines {n_p : Std.U64} {v : alloc.vec.Vec expr.Expr}
    (h : inductives.struct_parts.struct_proj_ps n_p = ok v) :
    absExprs v = ConLeche.structProjPs n_p.val ∧ ExprsWF v := by
  rw [inductives.struct_parts.struct_proj_ps] at h
  obtain ⟨habs, hwf⟩ :=
    struct_proj_ps_from_refines n_p 0#u64 _ v ExprOps.exprsWF_new h
  refine ⟨?_, hwf⟩
  rw [habs]
  simp [ConLeche.structProjPs, List.range_eq_range', alloc.vec.Vec.new, absExprs]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:339-345` —
`struct_proj_arg_p` refines `structProjArgP`: the `j`-th earlier-field
substitute in a tower entry's generated type, the first-class node `t.j`. -/
theorem struct_proj_arg_p_refines {t : name.Name} {j : Std.U64} {e : expr.Expr}
    (ht : NameWF t) (h : inductives.struct_parts.struct_proj_arg_p t j = ok e) :
    absExpr e = ConLeche.structProjArgP (absName t) j.val ∧ ExprWF e := by
  rw [inductives.struct_parts.struct_proj_arg_p] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
  have hne : n = t := (by simpa using hn : t = n).symm
  rw [hne] at h
  refine ⟨?_, Expr.proj_wf ht (Expr.bvar_wf hx) h⟩
  rw [Expr.proj_refines h, Expr.bvar_refines hx, ConLeche.structProjArgP]
  simp

/-- `ConLeche/Kernel/Inductives/StructParts.lean:347-354` —
`struct_proj_resid_p` refines `structProjResidP`: the constructor telescope
peeled at the parameters and the first `i` subject projections, threaded
incrementally.  Deviation: the cited `Option.bind` over a closure is an
explicit `match` (§3.4). -/
theorem struct_proj_resid_p_refines {t : name.Name} {n_p : Std.U64}
    {cty : expr.Expr} {i : Std.U64} {o : Option expr.Expr} (ht : NameWF t)
    (hcty : ExprWF cty)
    (h : inductives.struct_parts.struct_proj_resid_p t n_p cty i = ok o) :
    o.map absExpr
        = ConLeche.structProjResidP (absName t) n_p.val (absExpr cty) i.val
      ∧ ∀ r, o = some r → ExprWF r := by
  -- the `partial_fixpoint` recursion on `i`
  sorry

/-! ## `hasLooseBVar`, `hasLooseBVarB` and the memoized walk
(`StructParts.lean:357-636`) -/

/-- `ConLeche/Kernel/Inductives/StructParts.lean:356-369` — `has_loose_bvar`
refines `Expr.hasLooseBVar`: does `bvar i` occur loose in `e`?  The
*specification* of the bounded walk below; nothing executable calls it, and it
is ported so the provenance gate stays in step with its source. -/
theorem has_loose_bvar_refines {i : Std.U64} {e : expr.Expr} {b : Bool}
    (he : ExprWF e) (h : inductives.struct_parts.has_loose_bvar i e = ok b) :
    b = ConLeche.Expr.hasLooseBVar i.val (absExpr e) := by
  -- the ten-armed `ExprWF` induction
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:371-390` —
`has_loose_bvar_b_spec` refines `Expr.hasLooseBVarB`: `hasLooseBVar` with the
packed bound's cutoff.  The *logical* definition; the executed one is
`has_loose_bvar_b` below (the `@[csimp]` family, module note). -/
theorem has_loose_bvar_b_spec_refines {i : Std.U64} {e : expr.Expr} {b : Bool}
    (he : ExprWF e)
    (h : inductives.struct_parts.has_loose_bvar_b_spec i e = ok b) :
    b = ConLeche.Expr.hasLooseBVarB i.val (absExpr e) := by
  -- the ten-armed `ExprWF` induction, with `bvar_b_refines` at the cutoff
  sorry

/-- con-leche's `LooseBVarMemoInv` (`StructParts.lean:412-414`) as the `Q` of
task #47's `MemoInv`: every recorded answer is the real one. -/
def LooseQ : ConLeche.Expr × Nat → Bool → Prop :=
  fun k r => r = ConLeche.Expr.hasLooseBVarB k.2 k.1

/-- `struct_parts::memo_b_get` is the owning probe of the `(node, cursor)` memo
(task #13's pattern 1): a `Bool` is `Copy`, so the port's `match` is the
lookup itself. -/
theorem memo_b_get_eq {m : ron.hashmap.HashMap expr_ops.ExprNatKey Bool}
    {k : expr_ops.ExprNatKey} {o : Option Bool}
    (h : inductives.struct_parts.memo_b_get m k = ok o) :
    ron.hashmap.HashMap.get
        expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapHashable
        expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapEq2 m k = ok o := by
  rw [inductives.struct_parts.memo_b_get] at h
  obtain ⟨o1, hget, h⟩ := bind_eq_ok_iff.mp h
  cases o1 with
  | none => rw [hget]; simpa using h
  | some w => rw [hget]; simpa using h

/-- `ConLeche/Kernel/Inductives/StructParts.lean:435-440` —
`has_loose_bvar_b_ins` refines `Expr.hasLooseBVarBIns`: recording a correct
answer keeps con-leche's `LooseBVarMemoInv` (`MemoInv.set`). -/
theorem has_loose_bvar_b_ins_inv
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool}
    {e : expr.Expr} {i : Std.U64} {r : Bool} (he : ExprWF e)
    (hm : ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo)
    (hr : r = ConLeche.Expr.hasLooseBVarB i.val (absExpr e))
    (h : inductives.struct_parts.has_loose_bvar_b_ins memo e i r = ok memo') :
    ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo' := by
  rw [inductives.struct_parts.has_loose_bvar_b_ins] at h
  obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨old, m1⟩ := p
  rw [ExprOps.expr_nat_key_eq hkey] at hins
  have hm1 : m1 = memo' := by simpa using h
  rw [hm1] at hins
  exact ExprOps.MemoInv.set ExprOps.key_exact hm (ExprOps.keyWF_mk he) hr hins

/-- `ConLeche/Kernel/Inductives/StructParts.lean:442-478` —
`has_loose_bvar_b_go` refines `Expr.hasLooseBVarBGo`, whose specification is
con-leche's `hasLooseBVarBGo_spec`: the answer is `Expr.hasLooseBVarB` and the
memo it hands back still satisfies `LooseBVarMemoInv`.  The five leaf arms
answer *before* the probe, exactly as cited, and the walk **does**
short-circuit (`match … with | (true, memo) => (true, memo)`). -/
theorem has_loose_bvar_b_go_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool)
      (i : Std.U64) (r : Bool),
      ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo →
      inductives.struct_parts.has_loose_bvar_b_go memo i e = ok (r, memo') →
      r = ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
        ∧ ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo' := by
  -- the ten-armed `ExprWF` induction, `MemoInv.hit` on the probe and
  -- `has_loose_bvar_b_ins_inv` on the miss
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:442-478` —
`has_loose_bvar_b_node` refines the inner `match e with` of
`hasLooseBVarBGo`'s miss branch, split off in the port so that the probe's
borrow dies before the descent mutates the memo (task #14's rule).  The
`_ => (false, memo)` arm is the cited unreachable one — the five leaf kinds
answered above — so on the five rebuilding kinds this is the same equation as
the walk's. -/
theorem has_loose_bvar_b_node_refines {e : expr.Expr} (he : ExprWF e)
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool}
    {i : Std.U64} {r : Bool}
    (hcut : i.val < (absExpr e).bvarB)
    (hm : ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo)
    (h : inductives.struct_parts.has_loose_bvar_b_node memo i e = ok (r, memo')) :
    r = ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
      ∧ ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo' := by
  -- the five rebuilding arms of `has_loose_bvar_b_go_refines`
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:624-631` — **the executed
`hasLooseBVarB`**: `has_loose_bvar_b` refines `Expr.hasLooseBVarB` — the
`@[csimp]` lemma `Expr.hasLooseBVarB_eq_hasLooseBVarBFast` is what makes the
memoized walk with an empty, per-call memo the port of the logical definition
(module note). -/
theorem has_loose_bvar_b_refines {i : Std.U64} {e : expr.Expr} {b : Bool}
    (he : ExprWF e) (h : inductives.struct_parts.has_loose_bvar_b i e = ok b) :
    b = ConLeche.Expr.hasLooseBVarB i.val (absExpr e) := by
  rw [inductives.struct_parts.has_loose_bvar_b] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = b := by simpa using h
  rw [hr] at hgo
  exact (has_loose_bvar_b_go_refines he memo memo' i b
    (ExprOps.new_memo_inv hnew) hgo).1

/-- The same fact as `Expr.hasLooseBVarBFast`'s: the port's function is the
`@[csimp]` member con-leche executes. -/
theorem has_loose_bvar_b_fast_refines {i : Std.U64} {e : expr.Expr} {b : Bool}
    (he : ExprWF e) (h : inductives.struct_parts.has_loose_bvar_b i e = ok b) :
    b = ConLeche.Expr.hasLooseBVarBFast i.val (absExpr e) := by
  rw [has_loose_bvar_b_refines he h,
    ConLeche.Expr.hasLooseBVarB_eq_hasLooseBVarBFast]

/-! ## `structUsedLater` and the guard table (`StructParts.lean:634-759`) -/

/-- `ConLeche/Kernel/Inductives/StructParts.lean:633-641` —
`struct_used_later` refines `structUsedLater`: **field `j` is used by a later
field**, the official `infer_proj`'s `has_loose_bvars(binding_body(r))` at step
`j`. -/
theorem struct_used_later_refines {cty : expr.Expr} {n_p j : Std.U64} {b : Bool}
    (hcty : ExprWF cty)
    (h : inductives.struct_parts.struct_used_later cty n_p j = ok b) :
    b = ConLeche.structUsedLater (absExpr cty) n_p.val j.val := by
  rw [inductives.struct_parts.struct_used_later] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hiv : i.val = n_p.val + j.val := HashMap.uscalar_add_eq hi
  have hi1v : i1.val = n_p.val + j.val + 1 := by
    rw [HashMap.uscalar_add_eq hi1, hiv]; rfl
  obtain ⟨habs, hwf⟩ := ExprOps.strip_pis_refines hcty ho
  rw [hi1v] at habs
  rw [ConLeche.structUsedLater, ← habs]
  cases o with
  | none => simpa using h.symm
  | some q =>
    obtain ⟨bs, rest⟩ := q
    simp only [Option.map_some]
    simp only at h
    exact has_loose_bvar_b_refines (hwf (bs, rest) rfl).2 h

/-- `ConLeche/Kernel/Inductives/StructParts.lean:669-674` —
`struct_used_later_go` refines `structUsedLaterGo` (con-leche's
`structUsedLaterGo_spec`): the same answer, through the shared memo. -/
theorem struct_used_later_go_refines {cty : expr.Expr} {n_p j : Std.U64}
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool} {r : Bool}
    (hcty : ExprWF cty)
    (hm : ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo)
    (h : inductives.struct_parts.struct_used_later_go memo cty n_p j
        = ok (r, memo')) :
    r = ConLeche.structUsedLater (absExpr cty) n_p.val j.val
      ∧ ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo' := by
  rw [inductives.struct_parts.struct_used_later_go] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hiv : i.val = n_p.val + j.val := HashMap.uscalar_add_eq hi
  have hi1v : i1.val = n_p.val + j.val + 1 := by
    rw [HashMap.uscalar_add_eq hi1, hiv]; rfl
  obtain ⟨habs, hwf⟩ := ExprOps.strip_pis_refines hcty ho
  rw [hi1v] at habs
  rw [ConLeche.structUsedLater, ← habs]
  cases o with
  | none =>
    simp only [Option.map_none]
    have hp : (false, memo) = (r, memo') := by simpa using h
    have h1 : r = false := (congrArg Prod.fst hp).symm
    have h2 : memo' = memo := (congrArg Prod.snd hp).symm
    rw [h1, h2]
    exact ⟨rfl, hm⟩
  | some q =>
    obtain ⟨bs, rest⟩ := q
    simp only [Option.map_some]
    simp only at h
    exact has_loose_bvar_b_go_refines (hwf (bs, rest) rfl).2 memo memo' 0#u64 r hm h

/-- `ConLeche/Kernel/Inductives/StructParts.lean:685-692` —
`struct_used_later_list` refines `structUsedLaterList` at the strength
con-leche states it, `structUsedLaterList_spec`: entry `t` of the list is
`structUsedLater cty nP (base + t)`, for every `t < n`.  Lean conses on the way
out; the port pushes on the way in, which is the same order (task #13's
pattern 3), so the accumulator sits in front. -/
theorem struct_used_later_list_refines {cty : expr.Expr} {n_p : Std.U64}
    (hcty : ExprWF cty) :
    ∀ (n base : Std.U64)
      (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool)
      (out v : alloc.vec.Vec Bool),
      ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo →
      inductives.struct_parts.struct_used_later_list memo cty n_p n base out
        = ok (v, memo') →
      v.val = out.val ++ (List.range n.val).map
          (fun t => ConLeche.structUsedLater (absExpr cty) n_p.val (base.val + t))
        ∧ ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo' := by
  -- the `partial_fixpoint` count-down recursion on `n`
  sorry

/-- `struct_parts::sort_get_d` is the out-of-range fallback the guard fold
spells at every read (`sorts.getD i .zero`; no cited definition of its own). -/
theorem sort_get_d_refines {sorts : alloc.vec.Vec level.Level} {i : Std.U64}
    {u : level.Level} (hsorts : LevelsWF sorts)
    (h : inductives.struct_parts.sort_get_d sorts i = ok u) :
    absLevel u = (absLevels sorts).getD i.val .zero ∧ LevelWF u := by
  -- the bounds test, `level::dup` on the hit and `level::zero` on the miss
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:643-656`, `:722-732` —
`struct_proj_guard_at` refines the inner `(List.range i).foldl` of the guard
table from index `j`: field `i`'s own sort joined with the sorts of the earlier
fields a later field uses. -/
theorem struct_proj_guard_at_refines {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec level.Level} (hsorts : LevelsWF sorts) :
    ∀ (i j : Std.U64) (acc u : level.Level), LevelWF acc →
      inductives.struct_parts.struct_proj_guard_at used sorts i j acc = ok u →
      absLevel u = (List.range' j.val (i.val - j.val)).foldl
          (fun a k => if used.val.getD k false
            then .max a ((absLevels sorts).getD k .zero) else a)
          (absLevel acc)
        ∧ LevelWF u := by
  -- the `partial_fixpoint` index recursion on `i - j`
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:722-732` —
`struct_proj_guards_from` refines the outer `(List.range nF).map` of
`structProjGuardsFast` from index `i`, accumulator in front. -/
theorem struct_proj_guards_from_refines {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec level.Level} {n_f : Std.U64} (hsorts : LevelsWF sorts) :
    ∀ (i : Std.U64) (out v : alloc.vec.Vec level.Level), LevelsWF out →
      inductives.struct_parts.struct_proj_guards_from used sorts n_f i out = ok v →
      absLevels v = absLevels out
          ++ (List.range' i.val (n_f.val - i.val)).map (fun k =>
              (List.range k).foldl
                (fun a j => if used.val.getD j false
                  then .max a ((absLevels sorts).getD j .zero) else a)
                ((absLevels sorts).getD k .zero))
        ∧ LevelsWF v := by
  -- the `partial_fixpoint` index recursion on `n_f - i`
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:643-656`, `:722-746` —
**the projection guard levels**: `struct_proj_guards` refines
`structProjGuards`, the *logical* definition, as con-leche executes them — the
`nF` `structUsedLater` answers first, through *one* shared `hasLooseBVarBGo`
memo, then the fold.  The cited `@[csimp]` lemma
`structProjGuards_eq_structProjGuardsFast` is what lets the port implement the
fast form and still refine the definition the model stage tables consume; the
proof is con-leche's own, `structUsedLaterList_spec` supplying the `used`
table's pointwise reading. -/
theorem struct_proj_guards_refines {cty : expr.Expr} {n_p n_f : Std.U64}
    {sorts v : alloc.vec.Vec level.Level} (hcty : ExprWF cty)
    (hsorts : LevelsWF sorts)
    (h : inductives.struct_parts.struct_proj_guards cty n_p n_f sorts = ok v) :
    absLevels v = ConLeche.structProjGuards (absExpr cty) n_p.val n_f.val
        (absLevels sorts)
      ∧ LevelsWF v := by
  rw [inductives.struct_parts.struct_proj_guards] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hlist, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨used, memo'⟩ := p
  obtain ⟨hused, -⟩ := struct_used_later_list_refines hcty n_f 0#u64 memo memo' _
    used (ExprOps.new_memo_inv hnew) hlist
  have hout : LevelsWF (alloc.vec.Vec.new level.Level) := by
    intro u hu; simp [alloc.vec.Vec.new] at hu
  obtain ⟨habs, hwf⟩ := struct_proj_guards_from_refines hsorts 0#u64 _ v hout h
  refine ⟨?_, hwf⟩
  rw [habs]
  simp only [absLevels, alloc.vec.Vec.new, List.map_nil, List.nil_append,
    show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero,
    ← List.range_eq_range']
  rw [ConLeche.structProjGuards]
  refine List.map_congr_left ?_
  intro i hi
  refine ConLeche.foldlCongrMem _ _ ?_
  intro j hj x
  have hjlt : j < n_f.val :=
    Nat.lt_trans (List.mem_range.mp hj) (List.mem_range.mp hi)
  have huj : used.val.getD j false
      = ConLeche.structUsedLater (absExpr cty) n_p.val j := by
    rw [hused]
    simp only [alloc.vec.Vec.new, List.nil_append]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by simpa using hjlt)]
    simp
  rw [huj]

/-! ## The projection bodies (`StructParts.lean:761-773`) -/

/-- `ConLeche/Kernel/Inductives/StructParts.lean:748-766` and
`ConLeche/Cached/CheckerC.lean:37-43` — `struct_proj_bodies_go` refines
`structProjBodiesGo`: field `i`'s domain is body `i`, and the field is replaced
by the subject's projection `.proj T i (bvar 0)` before the walk continues.
Lean conses `fdom` on the way out; the port pushes it on the way in, which is
the same outermost-first list (task #13's pattern 3), so the accumulator sits
in front.  The cached driver's walker `structProjBodiesGoC` is the same walk at
`ExprC.instantiate1Lift`, which is this substitution (`structProjBodiesC_eq`). -/
theorem struct_proj_bodies_go_refines {t : name.Name} (ht : NameWF t) :
    ∀ (k i : Std.U64) (e : expr.Expr) (out : alloc.vec.Vec expr.Expr)
      (o : Option (alloc.vec.Vec expr.Expr)),
      ExprWF e → ExprsWF out →
      inductives.struct_parts.struct_proj_bodies_go t k i e out = ok o →
      o.map absExprs
          = (ConLeche.structProjBodiesGo (absName t) k.val i.val (absExpr e)).map
              (fun l => absExprs out ++ l)
        ∧ ∀ bs, o = some bs → ExprsWF bs := by
  -- the `partial_fixpoint` recursion on `k`, with a `cases` on `ExprWF e` inside
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:768-771` and
`ConLeche/Cached/CheckerC.lean:45-50` — **the projection bodies of a recognised
block**: `struct_proj_bodies` refines `structProjBodies`.  `Array Expr` is
`Vec<Expr>` in the port (one list type), so the cited `List.toArray` is the
identity here.

**Owed to the sibling**: this is exactly `IndStructInstall.lean`'s
`StructProjBodiesRefines`, the second of `StructWalkers.plain`'s two walkers,
which `check_struct_proj_table_refines` takes as an ingredient. -/
theorem struct_proj_bodies_refines {t : name.Name} {n_p n_f : Std.U64}
    {cty : expr.Expr} {o : Option (alloc.vec.Vec expr.Expr)}
    (ht : NameWF t) (hcty : ExprWF cty)
    (h : inductives.struct_parts.struct_proj_bodies t n_p n_f cty = ok o) :
    o.map (fun bs => (absExprs bs).toArray)
        = ConLeche.structProjBodies (absName t) n_p.val n_f.val (absExpr cty)
      ∧ ∀ bs, o = some bs → ExprsWF bs := by
  rw [inductives.struct_parts.struct_proj_bodies] at h
  obtain ⟨ps, hps, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpsabs, hpswf⟩ := struct_proj_ps_refines hps
  obtain ⟨hiabs, hiwf⟩ := ExprOps.inst_pis_at_lift_refines hpswf hcty ho1
  rw [hpsabs] at hiabs
  rw [ConLeche.structProjBodies, ← hiabs]
  cases o1 with
  | none =>
    simp only [Option.map_none] at h ⊢
    have ho : o = none := (Result.ok_injective h).symm
    rw [ho]; simp
  | some r =>
    simp only [Option.map_some]
    obtain ⟨habs, hwf⟩ := struct_proj_bodies_go_refines ht n_f 0#u64 r _ o
      (hiwf r rfl) ExprOps.exprsWF_new h
    refine ⟨?_, hwf⟩
    cases hg : ConLeche.structProjBodiesGo (absName t) n_f.val
        ((0#u64 : Std.U64)).val (absExpr r) with
    | none =>
      rw [hg] at habs
      cases o with
      | none => simp
      | some bs => simp at habs
    | some l =>
      rw [hg] at habs
      cases o with
      | none => simp at habs
      | some bs =>
        simp only [Option.map_some, Option.some.injEq] at habs ⊢
        rw [habs]
        simp [alloc.vec.Vec.new, absExprs]

/-! ## `mentionsConst` and its memoized walk (`StructParts.lean:775-930`) -/

/-- `ConLeche/Kernel/Inductives/StructParts.lean:773-782` —
`mentions_const_spec` refines `Expr.mentionsConst`: does the constant `T` occur
in `e`?  A syntactic walk (`fvar` annotations included; a `.proj` node names
its structure).  The *logical* definition; the executed one is
`mentions_const` below. -/
theorem mentions_const_spec_refines {t : name.Name} {e : expr.Expr} {b : Bool}
    (ht : NameWF t) (he : ExprWF e)
    (h : inductives.struct_parts.mentions_const_spec t e = ok b) :
    b = ConLeche.Expr.mentionsConst (absName t) (absExpr e) := by
  -- the ten-armed `ExprWF` induction
  sorry

/-- con-leche's `MentionsMemoInv` (`StructParts.lean:801-803`) as the `Q` of
task #47's `MemoInv`, at the `Expr` key. -/
def MentionsQ (t : ConLeche.Name) : ConLeche.Expr → Bool → Prop :=
  fun k r => r = ConLeche.Expr.mentionsConst t k

/-- `struct_parts::memo_eb_get` is the owning probe of the `Expr`-keyed memo
(task #13's pattern 1). -/
theorem memo_eb_get_eq {m : ron.hashmap.HashMap expr.Expr Bool}
    {k : expr.Expr} {o : Option Bool}
    (h : inductives.struct_parts.memo_eb_get m k = ok o) :
    ron.hashmap.HashMap.get expr.Expr.Insts.Con_ron_coreRonHashmapHashable
        expr.Expr.Insts.Con_ron_coreRonHashmapEq2 m k = ok o := by
  rw [inductives.struct_parts.memo_eb_get] at h
  obtain ⟨o1, hget, h⟩ := bind_eq_ok_iff.mp h
  cases o1 with
  | none => rw [hget]; simpa using h
  | some w => rw [hget]; simpa using h

/-- `ConLeche/Kernel/Inductives/StructParts.lean:814-849` —
`mentions_const_go` refines `Expr.mentionsConstGo`, whose specification is
con-leche's `mentionsConstGo_spec`: the answer is `Expr.mentionsConst` and the
memo it hands back still satisfies `MentionsMemoInv`.  The four leaf arms
answer before the probe, every other node is probed, walked and recorded. -/
theorem mentions_const_go_refines {t : name.Name} (ht : NameWF t)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool) (r : Bool),
      ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo →
      inductives.struct_parts.mentions_const_go t memo e = ok (r, memo') →
      r = ConLeche.Expr.mentionsConst (absName t) (absExpr e)
        ∧ ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo' := by
  -- the ten-armed `ExprWF` induction, `MemoInv.hit` on the probe and
  -- `MemoInv.set` on the miss
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:814-849` —
`mentions_const_node` refines the inner `match e with` of the miss branch,
split off in the port so the probe's borrow dies before the descent mutates the
memo (task #14's rule).  The final `| e => (e.mentionsConst T, memo)` arm is
the cited unreachable one — the four leaf kinds answered above.

**The deviation this arm keeps**: the cited walk does *not* short-circuit —
`let (b₁, memo) := go f; let (b₂, memo) := go a; (b₁ || b₂, memo)` walks both
children even when the first answers `true`, because the memo it hands back
must hold both answers — so the port binds `b1` and `b2` and only then tests,
and the memo contents agree node for node with con-leche's. -/
theorem mentions_const_node_refines {t : name.Name} (ht : NameWF t)
    {e : expr.Expr} (he : ExprWF e)
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {r : Bool}
    (hm : ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo)
    (h : inductives.struct_parts.mentions_const_node t memo e = ok (r, memo')) :
    r = ConLeche.Expr.mentionsConst (absName t) (absExpr e)
      ∧ ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo' := by
  -- the six rebuilding arms of `mentions_const_go_refines`
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:922-929` — **the executed
`mentionsConst`**: `mentions_const` refines `Expr.mentionsConst` — one
memoized DAG walk with an empty, per-call memo, which the `@[csimp]` lemma
`Expr.mentionsConst_eq_mentionsConstFast` makes the port of the logical
definition too.  The recogniser's positivity walk asks this of every field
domain and index argument, and on a DAG-shared field type the tree walk does
not finish. -/
theorem mentions_const_refines {t : name.Name} {e : expr.Expr} {b : Bool}
    (ht : NameWF t) (he : ExprWF e)
    (h : inductives.struct_parts.mentions_const t e = ok b) :
    b = ConLeche.Expr.mentionsConst (absName t) (absExpr e) := by
  rw [inductives.struct_parts.mentions_const] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = b := by simpa using h
  rw [hr] at hgo
  exact (mentions_const_go_refines ht he memo memo' b
    (ExprOps.new_memo_inv hnew) hgo).1

/-- The same fact as `Expr.mentionsConstFast`'s: the port's function is the
`@[csimp]` member con-leche executes. -/
theorem mentions_const_fast_refines {t : name.Name} {e : expr.Expr} {b : Bool}
    (ht : NameWF t) (he : ExprWF e)
    (h : inductives.struct_parts.mentions_const t e = ok b) :
    b = ConLeche.Expr.mentionsConstFast (absName t) (absExpr e) := by
  rw [mentions_const_refines ht he h,
    ConLeche.Expr.mentionsConst_eq_mentionsConstFast]

/-! ## The arithmetic helper -/

/-- `struct_parts::nat_sub` is `expr_ops::sub_nat` re-exported so the
generators read as the Lean does: Lean's `Nat` subtraction truncates at zero
where `u64`'s underflows into an Aeneas `fail`, so on success the two agree. -/
theorem nat_sub_refines {a b r : Std.U64}
    (h : inductives.struct_parts.nat_sub a b = ok r) : r.val = a.val - b.val := by
  rw [inductives.struct_parts.nat_sub] at h
  exact ExprOps.sub_nat_val h

end ConRon.Refine.StructParts
