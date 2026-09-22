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
6. **The `u64 → usize` index casts** — `Refine/Scalars.lean` (task #59) is the
   one place for this fact and every site below goes through it.  Four
   functions index a `Vec` at a `u64` count — `sort_get_d`,
   `struct_proj_guard_at` and the three `struct_shape_*` clauses write
   `xs[(i as usize)]` behind an `(i as usize) < xs.len()` test — and Aeneas
   keeps `usize`'s width abstract (`System.Platform.numBits_eq`), so the cast
   may wrap in the *model*.  Those five lemmas therefore carry the side
   condition as a **hypothesis** (`i.val ≤ Std.Usize.max`), because their
   counter is a free `u64` with no `Vec` to bound it: it is the *declared*
   parameter or field count.  Everywhere the counter does come from a `Vec`
   the bound is **discharged** instead, by
   `Scalars.u64_le_usize_max_of_le_len` / `Scalars.vec_len_le_usize_max`, and
   the hypothesis is gone: `struct_ctor_resid_ok_refines` reads it off the
   argument spine, `struct_shape_refines` off the `nP + 3` binders
   `strip_pis` returned (so it supplies all three `struct_shape_*` clauses
   theirs), and `struct_proj_guards_refines` off the `nF`-long `used` table
   its own walk just built.  Nothing here assumes a platform width.

## What this file owes its siblings

* **`struct_proj_bodies_refines`** is `IndStructInstall.lean`'s
  `StructProjBodiesRefines` — the second of `StructWalkers.plain`'s two
  walkers — stated at exactly that shape, so that
  `check_struct_proj_table_refines` can take it as an ingredient.  **Proved.**
* **`level_is_prop_refines`** is what `IndSumParts.lean`'s
  `with_sort_refines`, `IndNativeParts.lean`'s recogniser and
  `struct_parts_core_refines` below all read: the `isProp` flag all three
  recognisers compute.  **Proved.**

`StructParts` itself is abstracted by `IndAbs.absStructParts` and its
well-formedness is `IndAbs.StructPartsWF`; nothing in the shipped install path
consumes the record (the simple-structure route was deleted at con-leche's
task #210 Part C), so this file is the only reader of both.

## `sorry`s

**None** (task #59 closed the last seven).  `structPartsCore?`'s recogniser —
`struct_shape_motive`/`_minor`/`_major`, `struct_shape`,
`struct_parts_front_ok`, `struct_parts_large`, `struct_parts_small_ok`,
`struct_parts_core`, the ten-armed `&&`/`match` cascade that reads the three
stored types — is proved at its stated shape: each clause is
`b = <the cited Bool>`, and the recogniser itself
`o.map absStructParts = structPartsCore? (absConstantInfos block)` together
with `StructPartsWF` of what it returns.  `binders_index`/`binders_index_none`
are the reading of `rbs[k]?` the three clauses need, `wf_forall_inv`/
`wf_sort_inv` the two `ExprWF` inversions their `match … .kind` arms need, and
`core_none`/`core_none_len`/`list_three`/`list_one` the block-pattern
bookkeeping the recogniser's eleven `none` arms share.

Two proof notes, because they recur:

* **con-leche builds its own `match_*` auxiliaries.**  A `match` written in
  this file and the syntactically identical one inside `structShape` /
  `structPartsCore?` are *different constants* (definitionally equal, but `rw`
  matches syntactically), so `struct_shape_refines` and
  `struct_parts_core_refines` each open with a `show` that respells the goal at
  this file's matchers.  After that the ingredient lemmas rewrite straight in.
* **A tuple bind's `let (e, _) := (…, …)` does not reduce under `dsimp`**
  (task #57's finding 2); `struct_shape_motive_refines` needs a full `simp at h`
  before it can case on the node's kind.

Everything else in the module was already proved, including all three
`@[csimp]` families end to end (`has_loose_bvar_b_walk` and
`mentions_const_walk` are the two mutual `ExprWF` inductions,
`struct_proj_guards_refines` the guard table), the two `Π`-rewrites, the
projection bodies and `struct_proj_resid_p`.
-/
import ConRon.RefineOld.IndAbs
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

/-- `foldl` respects a pointwise equality of the step functions on the list's
elements.  con-leche's own `foldlCongrMem` (`StructParts.lean:706-713`), which
is `private` there, so `struct_proj_guards_refines` carries its own copy of the
one lemma its proof is con-leche's. -/
theorem foldlCongrMem {α β : Type _} {f g : α → β → α} :
    ∀ (l : List β) (a : α), (∀ b ∈ l, ∀ x : α, f x b = g x b) →
      l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, a, hb => by
    rw [List.foldl_cons, List.foldl_cons, hb b (by simp) a]
    exact foldlCongrMem l _ (fun b' hb' => hb b' (by simp [hb']))

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

/-- A memoized walk's `ok (r, memo)` result, split.  (`Result` is Aeneas's
coinductive `ITree`, so `simp`'s `injEq` machinery does not always see through
the pair; `Result.ok_injective` always does.) -/
theorem pair_ok {A B : Type} {a a' : A} {b b' : B}
    (h : (ok (a, b) : Result (A × B)) = ok (a', b')) : a = a' ∧ b = b' :=
  ⟨congrArg Prod.fst (Result.ok_injective h),
   congrArg Prod.snd (Result.ok_injective h)⟩

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
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
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
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @mk_const n2 us e hn2 hus h1 =>
        obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePisPw], by simp⟩
      | @proj s i x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
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
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
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
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @mk_const n2 us e hn2 hus h1 =>
        obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLamsPw], by simp⟩
      | @proj s i x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
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
        Scalars.usize_cast_u64_val _
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
      -- the `u64 → usize` cast is the identity here, discharged from the
      -- `Vec` the count came from (`Refine/Scalars.lean`)
      have hi3v : i3.val = n_p.val := by
        simp only [lift, Result.ok.injEq] at hi3
        rw [← hi3]
        exact Scalars.cast_val_of_le_len (v := args) (by omega)
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

/-- Indexing a well-formed binder list: the entry is well formed and the
abstracted list's `getElem?` is the abstracted entry.  (**To be unified into
`Refine/ExprOpsSpine.lean`** beside `absBinders`.) -/
theorem binders_index {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {i : Std.Usize} {x : expr.Expr × expr.BinderMeta} (hbs : ExprOps.BindersWF bs)
    (h : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice (expr.Expr × expr.BinderMeta)) bs i
      = ok x) :
    (ExprOps.absBinders bs)[i.val]? = some (absExpr x.1, absBinderMeta x.2)
      ∧ ExprWF x.1 ∧ BinderMetaWF x.2 := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : i.val < bs.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : bs.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  refine ⟨?_, hbs x (by rw [← hx]; exact List.getElem_mem hlt)⟩
  rw [ExprOps.absBinders, List.getElem?_map,
    List.getElem?_eq_getElem hlt, hx]
  simp

/-- A list of length three, read off.  (The port's three-element `Vec` pattern
is an index match; con-leche's is a list pattern.) -/
theorem list_three {α : Type} : ∀ {l : List α}, l.length = 3 → ∃ a b c, l = [a, b, c]
  | [], h => by simp at h
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | [a, b, c], _ => ⟨a, b, c, rfl⟩
  | _ :: _ :: _ :: _ :: _, h => by simp at h

/-- …and a list of length one (the single recursor rule). -/
theorem list_one {α : Type} : ∀ {l : List α}, l.length = 1 → ∃ a, l = [a]
  | [], h => by simp at h
  | [a], _ => ⟨a, rfl⟩
  | _ :: _ :: _, h => by simp at h

/-- `structPartsCore?`'s block pattern, read backwards: anything it does not
match is `none`.  This is what every `ok none` arm of the port's three
`ConstantInfo` matches, its two length tests and its `strip_pis` fall-through
needs, and it is one lemma instead of one case analysis per arm. -/
theorem core_none {L : List ConLeche.ConstantInfo}
    (hL : ∀ cvT caps cvC nP nF cvR mI rP rule,
      L ≠ [.indInfo cvT caps, .ctorInfo cvC nP nF, .recInfo cvR mI rP [rule]]) :
    ConLeche.structPartsCore? L = none := by
  -- the `rw` closes the equation by the default arm and leaves its side
  -- condition, which is exactly `hL`
  rw [ConLeche.structPartsCore?]
  intro cvT caps cvC nP nF cvR mI rP rule hc
  exact hL _ _ _ _ _ _ _ _ _ hc

/-- …in particular at a block that is not three constants long. -/
theorem core_none_len {L : List ConLeche.ConstantInfo} (h : L.length ≠ 3) :
    ConLeche.structPartsCore? L = none :=
  core_none (fun _ _ _ _ _ _ _ _ _ hc => by rw [hc] at h; simp at h)

/-- Past the end, the abstracted binder list has no entry. -/
theorem binders_index_none {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {n : Nat} (h : bs.val.length ≤ n) : (ExprOps.absBinders bs)[n]? = none := by
  rw [ExprOps.absBinders, List.getElem?_eq_none (by simpa using h)]

/-! ### Two `ExprWF` inversions the recogniser's `match … .kind` arms need

Casing on a node's *kind* throws the `ExprWF` derivation away, so each arm that
descends has to recover the sub-derivation from the shape.  `Refine/CheckerBase.lean`
and `Refine/CoreKGuards.lean` carry the same two copies for the same reason;
**to be unified into `Refine/Expr.lean`** beside the `*_inv` lemmas (neither of
those files is in this one's import closure). -/

/-- A well-formed `ForallE` node has well-formed parts. -/
theorem wf_forall_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {ty bo : expr.Expr} {m : expr.BinderMeta}
    (hk : e = .mk (.mk d (.ForallE ty bo m))) :
    ExprWF ty ∧ ExprWF bo ∧ BinderMetaWF m := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty1 _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u1 _ _ h1 => obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; simp at hk
  | @mk_const n1 us1 _ _ _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; simp at hk
  | @app f1 a1 _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp at hk
  | @lam ty1 bo1 m1 _ _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; simp at hk
  | @forall_e ty1 bo1 m1 _ hty hbo hm h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.ForallE.injEq] at hk
    obtain ⟨-, rfl, rfl, rfl⟩ := hk
    exact ⟨hty, hbo, hm⟩
  | @let_e ty1 v1 bo1 _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk

/-- A well-formed `Sort` node has a well-formed level. -/
theorem wf_sort_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64} {u : level.Level}
    (hk : e = .mk (.mk d (.Sort u))) : LevelWF u := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u1 _ hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.Sort.injEq] at hk
    obtain ⟨-, rfl⟩ := hk
    exact hu
  | @mk_const n1 us1 _ _ _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; simp at hk
  | @app f a _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp at hk
  | @lam ty bo m _ _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; simp at hk
  | @forall_e ty bo m _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; simp at hk
  | @let_e ty v bo _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk

/-- `ConLeche/Kernel/Inductives/StructParts.lean:246-281` —
`struct_shape_motive` refines `structShape`'s motive-binder clause: the
motive's codomain is `Sort elim` at the large eliminator and `Prop` at the
small one, and its own major domain is the family at the parameters.  Split
off in the port so that every `else` arm of the cited `&&` cascade stays a
tail position (task #18's pattern 3).

`n_p.val ≤ Std.Usize.max` is the `u64 → usize` width side condition of
`Refine/Scalars.lean` (the port writes `rbs[n_p as usize]`, and Aeneas keeps
`usize`'s width abstract).  It stays a hypothesis because `n_p` is the
*declared* parameter count, a free `u64` here; `struct_shape_refines`
discharges it from the `nP + 3` binders `strip_pis` gave it. -/
theorem struct_shape_motive_refines {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {elim : name.Name} {large : Bool}
    {n_p : Std.U64} {rbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {b : Bool} (ht : NameWF t) (hlps : NamesWF lps) (helim : NameWF elim)
    (hrbs : ExprOps.BindersWF rbs) (hnp : n_p.val ≤ Std.Usize.max)
    (h : inductives.struct_parts.struct_shape_motive t lps elim large n_p rbs
        = ok b) :
    b = (match (ExprOps.absBinders rbs)[n_p.val]? with
      | some (.forallE mmaj (.sort s') _, _) =>
        (if large then s' == ConLeche.Level.param (absName elim)
         else s' == ConLeche.Level.zero)
          && mmaj == ConLeche.structFam (absName t) (absNames lps) n_p.val 0
      | _ => false) := by
  rw [inductives.struct_parts.struct_shape_motive] at h
  simp only [lift_eq, bind_tc_ok] at h
  have hcv : (Std.UScalar.cast .Usize n_p : Std.Usize).val = n_p.val :=
    Scalars.u64_cast_usize_val hnp
  split at h
  · rename_i hlt
    obtain ⟨x, hidx, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e0, m0⟩ := x
    obtain ⟨hgx, hewf, hmwf⟩ := binders_index hrbs hidx
    rw [hcv] at hgx
    rw [hgx]
    obtain ⟨⟨dd, kk⟩⟩ := e0
    -- the tuple bind's `let (e, _) := (…, …)` needs a full `simp` to reduce
    simp at h
    cases kk with
    | ForallE mmaj cod mm =>
      obtain ⟨hmajwf, hcodwf, -⟩ := wf_forall_inv hewf rfl
      obtain ⟨⟨d2, k2⟩⟩ := cod
      simp only [ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      cases k2 with
      | «Sort» u =>
        have huwf : LevelWF u := wf_sort_inv hcodwf rfl
        obtain ⟨ok1, hok1, h⟩ := bind_eq_ok_iff.mp h
        have hok1e : ok1
            = (if large then absLevel u == ConLeche.Level.param (absName elim)
               else absLevel u == ConLeche.Level.zero) := by
          cases large with
          | true =>
            simp only [if_true] at hok1 ⊢
            obtain ⟨l, hl, hok1⟩ := bind_eq_ok_iff.mp hok1
            rw [Level.beq_refines huwf (LevelWF.param helim hl) hok1,
              Level.param_refines hl]
            refine Bool.eq_iff_iff.mpr ?_
            simp
          | false =>
            simp only [Bool.false_eq_true, if_false] at hok1 ⊢
            obtain ⟨l, hl, hok1⟩ := bind_eq_ok_iff.mp hok1
            rw [Level.beq_refines huwf (LevelWF.zero hl) hok1, Level.zero_refines hl]
            refine Bool.eq_iff_iff.mpr ?_
            simp
        cases hok1d : ok1 with
        | false =>
          rw [hok1d] at h hok1e
          simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
          rw [← h]
          simp only [absExpr_mk, absExprKind, ← hok1e, Bool.false_and]
        | true =>
          rw [hok1d] at h hok1e
          simp only [if_true] at h
          obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hfabs, hfwf⟩ := struct_fam_refines ht hlps he1
          rw [Expr.beq_refines hmajwf hfwf h]
          simp only [absExpr_mk, absExprKind, ← hok1e, Bool.true_and, hfabs]
          refine Bool.eq_iff_iff.mpr ?_
          simp
      | Bvar _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
      | Fvar _ _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
      | Const _ _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
      | App _ _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
      | Lam _ _ _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
      | ForallE _ _ _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
      | LetE _ _ _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
      | Lit _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
      | Proj _ _ _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
    | Bvar _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | Fvar _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | «Sort» _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | Const _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | App _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | Lam _ _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | LetE _ _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | Lit _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | Proj _ _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
  · rename_i hge
    have hgev : rbs.val.length ≤ n_p.val := by
      have := alloc.vec.Vec.len_val rbs; scalar_tac
    rw [binders_index_none hgev, ← Result.ok_injective h]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:246-281` —
`struct_shape_minor` refines `structShape`'s minor-binder clause: the minor's
own `nF`-binder telescope ends in `motive (C p⃗ f⃗)`.

`n_p.val + 1 ≤ Std.Usize.max` is `Refine/Scalars.lean`'s width side condition
at `rbs[nP + 1]`; `struct_shape_refines` discharges it. -/
theorem struct_shape_minor_refines {c : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f : Std.U64}
    {rbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {b : Bool}
    (hc : NameWF c) (hlps : NamesWF lps) (hrbs : ExprOps.BindersWF rbs)
    (hnp : n_p.val + 1 ≤ Std.Usize.max)
    (h : inductives.struct_parts.struct_shape_minor c lps n_p n_f rbs = ok b) :
    b = (match (ExprOps.absBinders rbs)[n_p.val + 1]? with
      | some (mindom, _) =>
        match mindom.stripPis n_f.val with
        | some (_, mbody) =>
          mbody == ConLeche.Expr.app (.bvar n_f.val)
            (ConLeche.structCtorSpine (absName c) (absNames lps) n_p.val n_f.val)
        | none => false
      | none => false) := by
  rw [inductives.struct_parts.struct_shape_minor] at h
  simp only [lift_eq, bind_tc_ok] at h
  have hcv : (Std.UScalar.cast .Usize n_p : Std.Usize).val = n_p.val :=
    Scalars.u64_cast_usize_val (by omega)
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = n_p.val + 1 := by rw [HashMap.uscalar_add_eq hi1, hcv]; rfl
  split at h
  · rename_i hlt
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = n_p.val + 1 := by rw [HashMap.uscalar_add_eq hi2, hcv]; rfl
    obtain ⟨x, hidx, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e0, m0⟩ := x
    obtain ⟨hgx, hewf, hmwf⟩ := binders_index hrbs hidx
    rw [hi2v] at hgx
    rw [hgx]
    simp at h
    obtain ⟨o, ho, h⟩ := h
    obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines hewf ho
    cases o with
    | none =>
      simp only [Option.map_none] at hoabs
      simp only [Result.ok.injEq] at h
      rw [← h]
      simp [← hoabs]
    | some q =>
      obtain ⟨bs, mbody⟩ := q
      simp only [Option.map_some] at hoabs
      obtain ⟨hbswf, hmbwf⟩ := howf _ rfl
      simp at h
      obtain ⟨e2, he2, e3, he3, e4, he4, h⟩ := h
      obtain ⟨hspabs, hspwf⟩ := struct_ctor_spine_refines hc hlps he3
      rw [Expr.beq_refines hmbwf (Expr.app_wf (Expr.bvar_wf he2) hspwf he4) h,
        Expr.app_refines he4, Expr.bvar_refines he2, hspabs]
      simp only [← hoabs]
      refine Bool.eq_iff_iff.mpr ?_
      simp
  · rename_i hge
    have hgev : rbs.val.length ≤ n_p.val + 1 := by
      have := alloc.vec.Vec.len_val rbs; scalar_tac
    rw [binders_index_none hgev, ← Result.ok_injective h]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:246-281` —
`struct_shape_major` refines `structShape`'s major-binder clause: its domain is
the family at the parameters, two binders down.

`n_p.val + 2 ≤ Std.Usize.max` is `Refine/Scalars.lean`'s width side condition
at `rbs[nP + 2]`; `struct_shape_refines` discharges it. -/
theorem struct_shape_major_refines {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p : Std.U64}
    {rbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {b : Bool}
    (ht : NameWF t) (hlps : NamesWF lps) (hrbs : ExprOps.BindersWF rbs)
    (hnp : n_p.val + 2 ≤ Std.Usize.max)
    (h : inductives.struct_parts.struct_shape_major t lps n_p rbs = ok b) :
    b = (match (ExprOps.absBinders rbs)[n_p.val + 2]? with
      | some (majdom, _) =>
        majdom == ConLeche.structFam (absName t) (absNames lps) n_p.val 2
      | none => false) := by
  rw [inductives.struct_parts.struct_shape_major] at h
  simp only [lift_eq, bind_tc_ok] at h
  have hcv : (Std.UScalar.cast .Usize n_p).val = n_p.val :=
    Scalars.u64_cast_usize_val (by omega)
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = n_p.val + 2 := by rw [HashMap.uscalar_add_eq hi1, hcv]; rfl
  split at h
  · rename_i hlt
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = n_p.val + 2 := by rw [HashMap.uscalar_add_eq hi2, hcv]; rfl
    obtain ⟨x, hidx, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e0, m0⟩ := x
    obtain ⟨hgx, hewf, hmwf⟩ := binders_index hrbs hidx
    rw [hi2v] at hgx
    rw [hgx]
    obtain ⟨fam, hfam, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hfabs, hfwf⟩ := struct_fam_refines ht hlps hfam
    rw [Expr.beq_refines hewf hfwf h, hfabs]
    refine Bool.eq_iff_iff.mpr ?_
    simp
  · rename_i hge
    have hgev : rbs.val.length ≤ n_p.val + 2 := by
      have := alloc.vec.Vec.len_val rbs; scalar_tac
    rw [binders_index_none hgev, ← Result.ok_injective h]

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
  rw [inductives.struct_parts.struct_shape] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨htabs, htwf⟩ := ExprOps.strip_pis_refines htty ho
  rw [ConLeche.structShape]
  cases o with
  | none =>
    simp only [Option.map_none] at htabs
    simp only [Result.ok.injEq] at h
    rw [← h, ← htabs]
  | some tq =>
    obtain ⟨tbs, tbody⟩ := tq
    have htbwf : ExprWF tbody := (htwf _ rfl).2
    simp only [Option.map_some] at htabs
    obtain ⟨⟨td, tk⟩⟩ := tbody
    simp at h
    rw [← htabs]
    cases tk with
    | «Sort» su =>
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hi
      obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hcabs, hcwf⟩ := ExprOps.strip_pis_refines hcty ho1
      rw [hiv] at hcabs
      cases o1 with
      | none =>
        simp only [Option.map_none] at hcabs
        simp only [Result.ok.injEq] at h
        rw [← h, ← hcabs]
        simp
      | some cq =>
        obtain ⟨cbs, cbody⟩ := cq
        have hcbwf : ExprWF cbody := (hcwf _ rfl).2
        simp only [Option.map_some] at hcabs
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        have hi1v : i1.val = n_p.val + 3 := by rw [HashMap.uscalar_add_eq hi1]; rfl
        obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hrabs, hrwf⟩ := ExprOps.strip_pis_refines hrty ho2
        rw [hi1v] at hrabs
        cases o2 with
        | none =>
          simp only [Option.map_none] at hrabs
          simp only [Result.ok.injEq] at h
          rw [← h, ← hrabs]
          simp
        | some rq =>
          obtain ⟨rbs, rbody⟩ := rq
          have hrbswf : ExprOps.BindersWF rbs := (hrwf _ rfl).1
          have hrbwf : ExprWF rbody := (hrwf _ rfl).2
          simp only [Option.map_some] at hrabs
          -- the platform bound of the three clauses, discharged from the `Vec`
          -- the `nP + 3` binders came back in (`Refine/Scalars.lean`)
          have hrlen : rbs.val.length = n_p.val + 3 := by
            have := ConLeche.Expr.stripPis_length _ hrabs.symm
            simpa [ExprOps.absBinders] using this
          have hbnd : n_p.val + 3 ≤ Std.Usize.max := by
            have := Scalars.vec_len_le_usize_max rbs; omega
          rw [← hcabs, ← hrabs]
          -- respell the three clauses at *this* file's matchers, so that the
          -- three clause lemmas above rewrite into the goal (con-leche's
          -- `structShape` builds its own `match_*` auxiliaries for the same
          -- patterns, and `rw` matches syntactically)
          show b = (absExpr cbody
                == ConLeche.structFam (absName t) (absNames lps) n_p.val n_f.val &&
              absExpr rbody == ConLeche.Expr.app (.bvar 2) (.bvar 0) &&
              (match (ExprOps.absBinders rbs)[n_p.val]? with
               | some (.forallE mmaj (.sort s') _, _) =>
                 (if large then s' == ConLeche.Level.param (absName elim)
                  else s' == ConLeche.Level.zero)
                   && mmaj == ConLeche.structFam (absName t) (absNames lps) n_p.val 0
               | _ => false) &&
              (match (ExprOps.absBinders rbs)[n_p.val + 1]? with
               | some (mindom, _) =>
                 match mindom.stripPis n_f.val with
                 | some (_, mbody) =>
                   mbody == ConLeche.Expr.app (.bvar n_f.val)
                     (ConLeche.structCtorSpine (absName c) (absNames lps) n_p.val n_f.val)
                 | none => false
               | none => false) &&
              (match (ExprOps.absBinders rbs)[n_p.val + 2]? with
               | some (majdom, _) =>
                 majdom == ConLeche.structFam (absName t) (absNames lps) n_p.val 2
               | none => false))
          obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hfabs, hfwf⟩ := struct_fam_refines ht hlps he2
          obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
          have hbbe : bb
              = (absExpr cbody
                  == ConLeche.structFam (absName t) (absNames lps) n_p.val n_f.val) := by
            rw [Expr.beq_refines hcbwf hfwf hbb, hfabs]
            refine Bool.eq_iff_iff.mpr ?_
            simp
          cases hbbd : bb with
          | false =>
            rw [hbbd] at h hbbe
            simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
            rw [← h, ← hbbe]
            simp
          | true =>
            rw [hbbd] at h hbbe
            simp only [if_true] at h
            obtain ⟨e4, he4, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨e5, he5, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨e6, he6, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
            have hb1e : b1
                = (absExpr rbody
                    == ConLeche.Expr.app (.bvar 2) (.bvar 0)) := by
              rw [Expr.beq_refines hrbwf
                    (Expr.app_wf (Expr.bvar_wf he4) (Expr.bvar_wf he5) he6) hb1,
                Expr.app_refines he6, Expr.bvar_refines he4, Expr.bvar_refines he5]
              refine Bool.eq_iff_iff.mpr ?_
              simp
            cases hb1d : b1 with
            | false =>
              rw [hb1d] at h hb1e
              simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
              rw [← h, ← hbbe, ← hb1e]
              simp
            | true =>
              rw [hb1d] at h hb1e
              simp only [if_true] at h
              obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
              have hb2e := struct_shape_motive_refines ht hlps helim hrbswf
                (by omega) hb2
              cases hb2d : b2 with
              | false =>
                rw [hb2d] at h hb2e
                simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
                rw [← h, ← hbbe, ← hb1e, ← hb2e]
                simp
              | true =>
                rw [hb2d] at h hb2e
                simp only [if_true] at h
                obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
                have hb3e := struct_shape_minor_refines hc hlps hrbswf (by omega) hb3
                cases hb3d : b3 with
                | false =>
                  rw [hb3d] at h hb3e
                  simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
                  rw [← h, ← hbbe, ← hb1e, ← hb2e, ← hb3e]
                  simp
                | true =>
                  rw [hb3d] at h hb3e
                  simp only [if_true] at h
                  rw [struct_shape_major_refines ht hlps hrbswf (by omega) h,
                    ← hbbe, ← hb1e, ← hb2e, ← hb3e]
                  simp
    | Bvar _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | Fvar _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | Const _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | App _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | Lam _ _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | ForallE _ _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | LetE _ _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | Lit _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp
    | Proj _ _ _ => simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h; rw [← h]; simp

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
  rw [inductives.struct_parts.struct_parts_front_ok] at h
  obtain ⟨tn, htn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨cps, hcps, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨er, her, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨reserved, hres, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
  have htne : tn = cv_t.name := (by simpa using htn : cv_t.name = tn).symm
  rw [htne] at her
  obtain ⟨herabs, herwf⟩ := str_lit_step hcvt.1 hsl hcps her
    (L := [114#u32, 101#u32, 99#u32])
    (by simp [inductives.struct_parts.struct_parts_front_ok.REC]) (by decide)
  obtain ⟨hresabs, hreswf⟩ := BasisNames.reserved_basis_names_refines hres
  have hb0e : b0 = (absName cv_r.name == (absName cv_t.name).str "rec") := by
    rw [Name.beq_refines hcvr.1 herwf hb0, herabs]
    refine Bool.eq_iff_iff.mpr ?_
    simp; rfl
  cases hb0d : b0 with
  | false =>
    rw [hb0d] at h hb0e
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h, ← hb0e]; simp
  | true =>
    rw [hb0d] at h hb0e
    simp only [if_true] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1e : b1 = (absNames cv_c.level_params == absNames cv_t.level_params) := by
      rw [Env.names_beq_refines hcvc.2.1 hcvt.2.1 hb1]
      refine Bool.eq_iff_iff.mpr ?_; simp
    cases hb1d : b1 with
    | false =>
      rw [hb1d] at h hb1e
      simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
      rw [← h, ← hb0e, ← hb1e]; simp
    | true =>
      rw [hb1d] at h hb1e
      simp only [if_true] at h
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2e : b2 = ConLeche.reservedBasisNames.contains (absName cv_t.name) := by
        rw [Name.contains_refines hreswf hcvt.1 hb2, hresabs]
      cases hb2d : b2 with
      | true =>
        rw [hb2d] at h hb2e
        simp only [if_true, Result.ok.injEq] at h
        rw [← h, ← hb0e, ← hb1e, ← hb2e]; simp
      | false =>
        rw [hb2d] at h hb2e
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
        have hb3e : b3 = ConLeche.reservedBasisNames.contains (absName cv_c.name) := by
          rw [Name.contains_refines hreswf hcvc.1 hb3, hresabs]
        cases hb3d : b3 with
        | true =>
          rw [hb3d] at h hb3e
          simp only [if_true, Result.ok.injEq] at h
          rw [← h, ← hb0e, ← hb1e, ← hb2e, ← hb3e]; simp
        | false =>
          rw [hb3d] at h hb3e
          simp only [Bool.false_eq_true, if_false] at h
          obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
          have hb4e : b4 = ConLeche.reservedBasisNames.contains (absName cv_r.name) := by
            rw [Name.contains_refines hreswf hcvr.1 hb4, hresabs]
          cases hb4d : b4 with
          | true =>
            rw [hb4d] at h hb4e
            simp only [if_true, Result.ok.injEq] at h
            rw [← h, ← hb0e, ← hb1e, ← hb2e, ← hb3e, ← hb4e]; simp
          | false =>
            rw [hb4d] at h hb4e
            simp only [Bool.false_eq_true, if_false] at h
            obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
            have hiv : i.val = n_p.val + 2 := HashMap.uscalar_add_eq hi
            rw [← hb0e, ← hb1e, ← hb2e, ← hb3e, ← hb4e]
            by_cases hmi : m_i = i
            · rw [if_pos hmi] at h
              have hmiv : m_i.val = n_p.val + 2 := by rw [hmi, hiv]
              by_cases hrp : r_p = i
              · rw [if_pos hrp] at h
                have hrpv : r_p.val = n_p.val + 2 := by rw [hrp, hiv]
                obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
                have hb5e : b5 = ((absRecRule rule).ctor == absName cv_c.name) := by
                  rw [Name.beq_refines hrule.1 hcvc.1 hb5]
                  refine Bool.eq_iff_iff.mpr ?_; simp [absRecRule]
                cases hb5d : b5 with
                | false =>
                  rw [hb5d] at h hb5e
                  simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
                  rw [← h, ← hb5e]; simp [hmiv, hrpv]
                | true =>
                  rw [hb5d] at h hb5e
                  simp only [if_true] at h
                  rw [← hb5e]
                  by_cases hnf : rule.nfields = n_f
                  · rw [if_pos hnf] at h
                    have hnfv : (absRecRule rule).nfields = n_f.val := by
                      simp only [absRecRule]; rw [hnf]
                    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
                    have hi1v : i1.val = n_p.val + 2 + n_f.val := by
                      rw [HashMap.uscalar_add_eq hi1, hiv]
                    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨hoabs, howf⟩ := ExprOps.strip_lams_refines hrule.2.2 ho
                    rw [hi1v] at hoabs
                    have hrhs : (absRecRule rule).rhs = absExpr rule.rhs := rfl
                    rw [hrhs]
                    cases o with
                    | none =>
                      simp only [Option.map_none] at hoabs
                      simp only [Result.ok.injEq] at h
                      rw [← h, ← hoabs]; simp [hmiv, hrpv, hnfv]
                    | some q =>
                      obtain ⟨qbs, qbody⟩ := q
                      have hqwf : ExprWF qbody := (howf _ rfl).2
                      simp only [Option.map_some] at hoabs
                      rw [← hoabs]
                      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
                      obtain ⟨hsrb, hsrbwf⟩ := struct_rule_body_refines he1
                      rw [Expr.beq_refines hqwf hsrbwf h, hsrb]
                      simp only [hmiv, hrpv, hnfv]
                      refine Bool.eq_iff_iff.mpr ?_
                      simp
                  · rw [if_neg hnf, Result.ok.injEq] at h
                    have hnfv : ¬ ((absRecRule rule).nfields = n_f.val) := by
                      simp only [absRecRule]
                      intro hc; exact hnf (Std.UScalar.eq_of_val_eq hc)
                    rw [← h]; simp [hmiv, hrpv, hnfv]
              · rw [if_neg hrp, Result.ok.injEq] at h
                have hrpv : ¬ (r_p.val = n_p.val + 2) := by
                  intro hc; exact hrp (Std.UScalar.eq_of_val_eq (by rw [hc, hiv]))
                rw [← h]; simp [hmiv, hrpv]
            · rw [if_neg hmi, Result.ok.injEq] at h
              have hmiv : ¬ (m_i.val = n_p.val + 2) := by
                intro hc; exact hmi (Std.UScalar.eq_of_val_eq (by rw [hc, hiv]))
              rw [← h]; simp [hmiv]

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
  rw [inductives.struct_parts.struct_parts_large] at h
  split at h
  · rename_i hz
    have h0 : cv_r.level_params.val = [] := by
      have := alloc.vec.Vec.len_val cv_r.level_params
      exact List.eq_nil_of_length_eq_zero (by scalar_tac)
    have hnil : absNames cv_r.level_params = [] := by simp [absNames, h0]
    have ho : none = o := Result.ok_injective h
    rw [← ho]
    exact ⟨by simp [hnil], by simp⟩
  · rename_i hz
    obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨el, hel, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨relps, hrelps, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hlt, hnwf, hdrop⟩ := vec_index_name hcvr.2.1 hn
    have hele : el = n := (by simpa using hel : n = el).symm
    rw [hele] at h
    simp only [show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero,
      Nat.zero_add] at hdrop
    have hrelpsv : relps.val = cv_r.level_params.val.drop 1 := by
      have := PropWhen.append_from_val cv_r.level_params cv_r.level_params.val.length
        1#usize _ relps (by scalar_tac) hrelps
      simpa [alloc.vec.Vec.new] using this
    have hrelpsabs : absNames relps = (absNames cv_r.level_params).drop 1 := by
      simp [absNames, hrelpsv]
    have hrelpswf : NamesWF relps := by
      intro x hx
      rw [hrelpsv] at hx
      exact hcvr.2.1 x (List.mem_of_mem_drop hx)
    have hbbe : bb
        = ((absNames cv_r.level_params).drop 1 == absNames cv_t.level_params) := by
      rw [Env.names_beq_refines hrelpswf hcvt.2.1 hbb, hrelpsabs]
      refine Bool.eq_iff_iff.mpr ?_; simp
    rw [hdrop]
    show (o.map absName = (if ((absNames cv_r.level_params).drop 1
              == absNames cv_t.level_params
            && !(absNames cv_t.level_params).contains (absName n)
            && ConLeche.structShape (absName cv_t.name) (absName cv_c.name)
                (absNames cv_t.level_params) (absName n) true n_p.val n_f.val
                (absExpr cv_t.ty) (absExpr cv_c.ty) (absExpr cv_r.ty)) then
            some (absName n) else none))
      ∧ ∀ m, o = some m → NameWF m
    cases hbbd : bb with
    | false =>
      rw [hbbd] at h hbbe
      simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
      rw [← h]
      exact ⟨by rw [← hbbe]; simp, by simp⟩
    | true =>
      rw [hbbd] at h hbbe
      simp only [if_true] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1e : b1 = (absNames cv_t.level_params).contains (absName n) :=
        Name.contains_refines hcvt.2.1 hnwf hb1
      cases hb1d : b1 with
      | true =>
        rw [hb1d] at h hb1e
        simp only [if_true, Result.ok.injEq] at h
        rw [← h]
        exact ⟨by rw [← hbbe, ← hb1e]; simp, by simp⟩
      | false =>
        rw [hb1d] at h hb1e
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
        have hb2e := struct_shape_refines hcvt.1 hcvc.1 hcvt.2.1 hnwf hcvt.2.2
          hcvc.2.2 hcvr.2.2 hb2
        cases hb2d : b2 with
        | false =>
          rw [hb2d] at h hb2e
          simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
          rw [← h]
          exact ⟨by rw [← hbbe, ← hb1e, ← hb2e]; simp, by simp⟩
        | true =>
          rw [hb2d] at h hb2e
          simp only [if_true, Result.ok.injEq] at h
          rw [← h]
          refine ⟨by rw [← hbbe, ← hb1e, ← hb2e]; simp, ?_⟩
          intro m hm
          simp only [Option.some.injEq] at hm
          rw [← hm]; exact hnwf

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
  rw [inductives.struct_parts.struct_parts_small_ok] at h
  obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
  have hbbe : bb = (absNames cv_r.level_params == absNames cv_t.level_params) := by
    rw [Env.names_beq_refines hcvr.2.1 hcvt.2.1 hbb]
    refine Bool.eq_iff_iff.mpr ?_; simp
  cases hbbd : bb with
  | false =>
    rw [hbbd] at h hbbe
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h, ← hbbe]; simp
  | true =>
    rw [hbbd] at h hbbe
    simp only [if_true] at h
    obtain ⟨an, han, h⟩ := bind_eq_ok_iff.mp h
    rw [struct_shape_refines hcvt.1 hcvc.1 hcvt.2.1 (Name.anonymous_wf han) hcvt.2.2
        hcvc.2.2 hcvr.2.2 h,
      Name.anonymous_refines han, ← hbbe]
    simp

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
  rw [inductives.struct_parts.struct_parts_core] at h
  have hblen := alloc.vec.Vec.len_val block
  split at h
  · rename_i hne
    have hne3 : block.val.length ≠ 3 := by scalar_tac
    have hne3' : (absConstantInfos block).length ≠ 3 := by
      simpa [absConstantInfos] using hne3
    rw [← Result.ok_injective h]
    simp [core_none_len hne3']
  · rename_i he3
    have he3' : block.val.length = 3 := by scalar_tac
    obtain ⟨ci, hci, h1⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ci1, hci1, h2⟩ := bind_eq_ok_iff.mp h1
    obtain ⟨ci2, hci2, h3⟩ := bind_eq_ok_iff.mp h2
    clear h h1 h2
    obtain ⟨x0, x1, x2, hbl⟩ := list_three he3'
    have hbl' : block.val = [ci, ci1, ci2] := by
      have g0 := ExprOps.vec_index_getElem? hci
      have g1 := ExprOps.vec_index_getElem? hci1
      have g2 := ExprOps.vec_index_getElem? hci2
      rw [hbl] at g0 g1 g2 ⊢
      simp only [show ((0#usize : Std.Usize).val) = 0 from rfl,
        show ((1#usize : Std.Usize).val) = 1 from rfl,
        show ((2#usize : Std.Usize).val) = 2 from rfl] at g0 g1 g2
      simp at g0 g1 g2
      rw [g0, g1, g2]
    have habs : absConstantInfos block
        = [absConstantInfo ci, absConstantInfo ci1, absConstantInfo ci2] := by
      simp [absConstantInfos, hbl']
    have hw0 : ConstantInfoWF ci := hblock ci (by rw [hbl']; simp)
    have hw1 : ConstantInfoWF ci1 := hblock ci1 (by rw [hbl']; simp)
    have hw2 : ConstantInfoWF ci2 := hblock ci2 (by rw [hbl']; simp)
    rw [habs]
    clear habs hbl' hbl hci hci1 hci2 he3' hblen he3 hblock x0 x1 x2
    cases ci
    case IndInfo cv_t caps =>
      cases ci1
      case CtorInfo cv_c n_p n_f =>
        cases ci2
        case RecInfo cv_r m_i r_p rules =>
          obtain ⟨hcvtwf, -⟩ := hw0
          have hcvcwf : ConstantValWF cv_c := hw1
          obtain ⟨hcvrwf, hruleswf⟩ := hw2
          dsimp only at h3
          split at h3
          · rename_i hr1
            have hrl1 : rules.val.length ≠ 1 := by
              have := alloc.vec.Vec.len_val rules; scalar_tac
            rw [← Result.ok_injective h3]
            refine ⟨?_, by simp⟩
            rw [core_none (fun _ _ _ _ _ _ _ _ rule hc => by
              simp only [absConstantInfo, List.cons.injEq, and_true] at hc
              injection hc.2.2 with _ _ _ e4
              exact hrl1 (by simpa using congrArg List.length e4))]
            simp
          · rename_i hr1
            have hrl1 : rules.val.length = 1 := by
              have := alloc.vec.Vec.len_val rules; scalar_tac
            obtain ⟨rr, hrr, h4⟩ := bind_eq_ok_iff.mp h3
            clear h3
            obtain ⟨r0, hr0⟩ := list_one hrl1
            have hrlv : rules.val = [rr] := by
              have hg := ExprOps.vec_index_getElem? hrr
              rw [hr0] at hg ⊢
              simp only [show ((0#usize : Std.Usize).val) = 0 from rfl] at hg
              simp at hg
              rw [hg]
            have hrrwf : RecRuleWF rr := hruleswf rr (by rw [hrlv]; simp)
            have hrmap : rules.val.map absRecRule = [absRecRule rr] := by rw [hrlv]; simp
            obtain ⟨bf, hbf, h5⟩ := bind_eq_ok_iff.mp h4
            clear h4
            have hbfe := struct_parts_front_ok_refines hcvtwf hcvcwf hcvrwf hrrwf hbf
            simp only [absConstantInfo, hrmap]
            rw [ConLeche.structPartsCore?]
            -- respell `structPartsCore?`'s body at *this* file's matchers, so
            -- that the four ingredient lemmas above rewrite into it (con-leche
            -- builds its own `match_*` auxiliaries for the same patterns, and
            -- `rw` matches syntactically); the two readings are definitionally
            -- equal, which is what `show` checks
            show (Option.map IndAbs.absStructParts o
                = (if ((absName cv_r.name == (absName cv_t.name).str "rec")
                      && (absNames cv_c.level_params == absNames cv_t.level_params)
                      && (ConLeche.reservedBasisNames.contains (absName cv_t.name) == false)
                      && (ConLeche.reservedBasisNames.contains (absName cv_c.name) == false)
                      && (ConLeche.reservedBasisNames.contains (absName cv_r.name) == false)
                      && (m_i.val == n_p.val + 2) && (r_p.val == n_p.val + 2)
                      && ((absRecRule rr).ctor == absName cv_c.name)
                      && ((absRecRule rr).nfields == n_f.val)
                      && (match (absRecRule rr).rhs.stripLams (n_p.val + 2 + n_f.val) with
                          | some (_, rbody) => rbody == ConLeche.structRuleBody n_f.val
                          | none => false)) then
                    (match (absExpr cv_t.ty).stripPis n_p.val with
                     | some (_, .sort s) =>
                       (match (match absNames cv_r.level_params with
                               | elim :: relps =>
                                 if relps == absNames cv_t.level_params
                                     && !(absNames cv_t.level_params).contains elim
                                     && ConLeche.structShape (absName cv_t.name)
                                         (absName cv_c.name) (absNames cv_t.level_params)
                                         elim true n_p.val n_f.val (absExpr cv_t.ty)
                                         (absExpr cv_c.ty) (absExpr cv_r.ty) then
                                   some elim
                                 else none
                               | [] => none) with
                        | some elim =>
                          some ⟨absConstantVal cv_t, absConstantVal cv_c, n_p.val, n_f.val,
                            absConstantVal cv_r, elim, s, absExpr rr.rhs, true,
                            ConLeche.Level.isEquiv s .zero == some true⟩
                        | none =>
                          if ((absNames cv_r.level_params == absNames cv_t.level_params)
                              && ConLeche.structShape (absName cv_t.name) (absName cv_c.name)
                                  (absNames cv_t.level_params) .anonymous false n_p.val
                                  n_f.val (absExpr cv_t.ty) (absExpr cv_c.ty)
                                  (absExpr cv_r.ty)) then
                            some ⟨absConstantVal cv_t, absConstantVal cv_c, n_p.val, n_f.val,
                              absConstantVal cv_r, .anonymous, s, absExpr rr.rhs, false,
                              ConLeche.Level.isEquiv s .zero == some true⟩
                          else none)
                     | _ => none)
                  else none))
              ∧ ∀ p, o = some p → IndAbs.StructPartsWF p
            rw [← hbfe]
            cases bf with
            | false =>
              simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h5
              rw [← h5]
              exact ⟨by simp, by simp⟩
            | true =>
              simp only [if_true] at h5 ⊢
              obtain ⟨so, hso, h6⟩ := bind_eq_ok_iff.mp h5
              clear h5
              obtain ⟨hsoabs, hsowf⟩ := ExprOps.strip_pis_refines hcvtwf.2.2 hso
              rw [← hsoabs]
              cases so with
              | none =>
                simp only [Result.ok.injEq] at h6
                rw [← h6]
                exact ⟨by simp, by simp⟩
              | some q =>
                obtain ⟨sbs, sbody⟩ := q
                have hsbwf : ExprWF sbody := (hsowf _ rfl).2
                obtain ⟨⟨sd, sk⟩⟩ := sbody
                simp at h6
                simp only [Option.map_some, absExpr_mk]
                cases sk with
                | «Sort» su =>
                  have hsuwf : LevelWF su := wf_sort_inv hsbwf rfl
                  obtain ⟨ip, hip, h7⟩ := bind_eq_ok_iff.mp h6
                  have hipe := level_is_prop_refines hsuwf hip
                  obtain ⟨o1, ho1, h8⟩ := bind_eq_ok_iff.mp h7
                  obtain ⟨hlabs, hlwf⟩ :=
                    struct_parts_large_refines hcvtwf hcvcwf hcvrwf ho1
                  rw [← hlabs]
                  cases o1 with
                  | some elim =>
                    simp only [Option.map_some]
                    obtain ⟨cv, hcv, h9⟩ := bind_eq_ok_iff.mp h8
                    obtain ⟨cv1, hcv1, h10⟩ := bind_eq_ok_iff.mp h9
                    obtain ⟨cv2, hcv2, h11⟩ := bind_eq_ok_iff.mp h10
                    have e1 : cv = cv_t := Env.constant_val_dup_refines hcv
                    have e2 : cv1 = cv_c := Env.constant_val_dup_refines hcv1
                    have e3 : cv2 = cv_r := Env.constant_val_dup_refines hcv2
                    simp only [Result.ok.injEq] at h11
                    rw [← h11]
                    refine ⟨?_, ?_⟩
                    · simp only [absExprKind, Option.map_some, IndAbs.absStructParts,
                        e1, e2, e3, hipe]
                    · intro p hp
                      simp only [Option.some.injEq] at hp
                      rw [← hp]
                      exact ⟨by rw [e1]; exact hcvtwf, by rw [e2]; exact hcvcwf,
                        by rw [e3]; exact hcvrwf, hlwf elim rfl, hsuwf, hrrwf.2.2⟩
                  | none =>
                    simp only [Option.map_none]
                    obtain ⟨b1, hb1, h9⟩ := bind_eq_ok_iff.mp h8
                    have hb1e := struct_parts_small_ok_refines hcvtwf hcvcwf hcvrwf hb1
                    rw [← hb1e]
                    cases b1 with
                    | false =>
                      simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h9
                      rw [← h9]; exact ⟨by simp, by simp⟩
                    | true =>
                      simp only [if_true] at h9 ⊢
                      obtain ⟨cv, hcv, h10⟩ := bind_eq_ok_iff.mp h9
                      obtain ⟨cv1, hcv1, h11⟩ := bind_eq_ok_iff.mp h10
                      obtain ⟨cv2, hcv2, h12⟩ := bind_eq_ok_iff.mp h11
                      obtain ⟨an, han, h13⟩ := bind_eq_ok_iff.mp h12
                      have e1 : cv = cv_t := Env.constant_val_dup_refines hcv
                      have e2 : cv1 = cv_c := Env.constant_val_dup_refines hcv1
                      have e3 : cv2 = cv_r := Env.constant_val_dup_refines hcv2
                      simp only [Result.ok.injEq] at h13
                      rw [← h13]
                      refine ⟨?_, ?_⟩
                      · simp only [absExprKind, Option.map_some, IndAbs.absStructParts,
                          e1, e2, e3, hipe, Name.anonymous_refines han]
                      · intro p hp
                        simp only [Option.some.injEq] at hp
                        rw [← hp]
                        exact ⟨by rw [e1]; exact hcvtwf, by rw [e2]; exact hcvcwf,
                          by rw [e3]; exact hcvrwf, Name.anonymous_wf han, hsuwf, hrrwf.2.2⟩
                | Bvar _ =>
                  simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h6; rw [← h6]; exact ⟨by simp, by simp⟩
                | Fvar _ _ =>
                  simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h6; rw [← h6]; exact ⟨by simp, by simp⟩
                | Const _ _ =>
                  simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h6; rw [← h6]; exact ⟨by simp, by simp⟩
                | App _ _ =>
                  simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h6; rw [← h6]; exact ⟨by simp, by simp⟩
                | Lam _ _ _ =>
                  simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h6; rw [← h6]; exact ⟨by simp, by simp⟩
                | ForallE _ _ _ =>
                  simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h6; rw [← h6]; exact ⟨by simp, by simp⟩
                | LetE _ _ _ =>
                  simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h6; rw [← h6]; exact ⟨by simp, by simp⟩
                | Lit _ =>
                  simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h6; rw [← h6]; exact ⟨by simp, by simp⟩
                | Proj _ _ _ =>
                  simp only [ron.node.ExprView.ofKind, Result.ok.injEq] at h6; rw [← h6]; exact ⟨by simp, by simp⟩
        all_goals
          (rw [← Result.ok_injective h3]
           refine ⟨?_, by simp⟩
           rw [core_none (fun _ _ _ _ _ _ _ _ _ hc => by simp [absConstantInfo] at hc)]
           simp)
      all_goals
        (rw [← Result.ok_injective h3]
         refine ⟨?_, by simp⟩
         rw [core_none (fun _ _ _ _ _ _ _ _ _ hc => by simp [absConstantInfo] at hc)]
         simp)
    all_goals
      (rw [← Result.ok_injective h3]
       refine ⟨?_, by simp⟩
       rw [core_none (fun _ _ _ _ _ _ _ _ _ hc => by simp [absConstantInfo] at hc)]
       simp)

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
theorem struct_proj_resid_p_refines_aux {t : name.Name} (ht : NameWF t)
    {n_p : Std.U64} {cty : expr.Expr} (hcty : ExprWF cty) (N : Nat) :
    ∀ (i : Std.U64) (o : Option expr.Expr), i.val = N →
      inductives.struct_parts.struct_proj_resid_p t n_p cty i = ok o →
      o.map absExpr
          = ConLeche.structProjResidP (absName t) n_p.val (absExpr cty) i.val
        ∧ ∀ r, o = some r → ExprWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i o hN h
    rw [inductives.struct_parts.struct_proj_resid_p.eq_def] at h
    split at h
    · rename_i h0
      have hiv : i.val = 0 := by rw [h0]; scalar_tac
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hvabs, hvwf⟩ := struct_proj_ps_refines hv
      obtain ⟨habs, hwf⟩ := ExprOps.inst_pis_at_lift_refines hvwf hcty h
      refine ⟨?_, hwf⟩
      rw [hiv, ConLeche.structProjResidP, habs, hvabs]
    · rename_i h0
      obtain ⟨m0, hm0⟩ : ∃ m0, i.val = m0 + 1 := by
        have : i.val ≠ 0 := fun hc => h0 (Std.UScalar.eq_of_val_eq (by rw [hc]; scalar_tac))
        exact ⟨i.val - 1, by omega⟩
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = m0 := by
        rw [HashMap.uscalar_sub_eq hi1, hm0]; scalar_tac
      obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨habs1, hwf1⟩ := ih m0 (by omega) i1 o1 hi1v ho1
      rw [hi1v] at habs1
      cases o1 with
      | none =>
        simp only [Option.map_none] at habs1
        have ho : o = none := (Result.ok_injective h).symm
        rw [ho, hm0, ConLeche.structProjResidP, ← habs1]
        exact ⟨by simp, by simp⟩
      | some r0 =>
        simp only [Option.map_some] at habs1
        obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨heabs, hewf⟩ := struct_proj_arg_p_refines ht he
        obtain ⟨hargsabs, hargswf⟩ := CoreK.expr_singleton_refines hewf hargs
        obtain ⟨habs, hwf⟩ :=
          ExprOps.inst_pis_at_lift_refines hargswf (hwf1 r0 rfl) h
        refine ⟨?_, hwf⟩
        rw [hm0, ConLeche.structProjResidP, ← habs1, habs, hargsabs, heabs, hi1v]
        simp

/-- `struct_proj_resid_p` at its own statement. -/
theorem struct_proj_resid_p_refines {t : name.Name} {n_p : Std.U64}
    {cty : expr.Expr} {i : Std.U64} {o : Option expr.Expr} (ht : NameWF t)
    (hcty : ExprWF cty)
    (h : inductives.struct_parts.struct_proj_resid_p t n_p cty i = ok o) :
    o.map absExpr
        = ConLeche.structProjResidP (absName t) n_p.val (absExpr cty) i.val
      ∧ ∀ r, o = some r → ExprWF r :=
  struct_proj_resid_p_refines_aux ht hcty i.val i o rfl h

/-! ## `hasLooseBVar`, `hasLooseBVarB` and the memoized walk
(`StructParts.lean:357-636`) -/

/-- `ConLeche/Kernel/Inductives/StructParts.lean:356-369` — `has_loose_bvar`
refines `Expr.hasLooseBVar`: does `bvar i` occur loose in `e`?  The
*specification* of the bounded walk below; nothing executable calls it, and it
is ported so the provenance gate stays in step with its source. -/
theorem has_loose_bvar_refines_aux {e : expr.Expr} (he : ExprWF e) :
    ∀ (i : Std.U64) (b : Bool),
      inductives.struct_parts.has_loose_bvar i e = ok b →
      b = ConLeche.Expr.hasLooseBVar i.val (absExpr e) := by
  induction he with
  | @bvar j e h1 =>
    intro i b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    rw [inductives.struct_parts.has_loose_bvar.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.hasLooseBVar]
    refine Bool.eq_iff_iff.mpr ?_
    simp only [decide_eq_true_eq, beq_iff_eq]
    exact ⟨fun hc => by rw [hc], fun hc => Std.UScalar.eq_of_val_eq hc⟩
  | @fvar idx ty e hty h1 ih =>
    intro i b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    rw [inductives.struct_parts.has_loose_bvar.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.hasLooseBVar]
  | @sort u e hu h1 =>
    intro i b h
    obtain ⟨d, bw, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    rw [inductives.struct_parts.has_loose_bvar.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.hasLooseBVar]
  | @mk_const n us e hn hus h1 =>
    intro i b h
    obtain ⟨d, bw, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    rw [inductives.struct_parts.has_loose_bvar.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.hasLooseBVar]
  | @lit l e hl h1 =>
    intro i b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    rw [inductives.struct_parts.has_loose_bvar.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.hasLooseBVar]
  | @app f a e hf ha h1 ihf iha =>
    intro i b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    rw [inductives.struct_parts.has_loose_bvar.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := ihf i b1 hb1
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.hasLooseBVar]
    split at h
    · rename_i hc
      rw [← Result.ok_injective h, ← hb1v, hc]; simp
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      rw [iha i b h, ← hb1v, hc]; simp
  | @lam ty bo m e hty hbo hm h1 iht ihb =>
    intro i b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    rw [inductives.struct_parts.has_loose_bvar.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := iht i b1 hb1
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.hasLooseBVar]
    split at h
    · rename_i hc
      rw [← Result.ok_injective h, ← hb1v, hc]; simp
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      rw [ihb i1 b h, hi1v, ← hb1v, hc]; simp
  | @forall_e ty bo m e hty hbo hm h1 iht ihb =>
    intro i b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    rw [inductives.struct_parts.has_loose_bvar.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := iht i b1 hb1
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.hasLooseBVar]
    split at h
    · rename_i hc
      rw [← Result.ok_injective h, ← hb1v, hc]; simp
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      rw [ihb i1 b h, hi1v, ← hb1v, hc]; simp
  | @let_e ty w bo e hty hw hbo h1 iht ihv ihb =>
    intro i b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    rw [inductives.struct_parts.has_loose_bvar.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := iht i b1 hb1
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.hasLooseBVar]
    split at h
    · rename_i hc
      rw [← Result.ok_injective h, ← hb1v, hc]; simp
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2v := ihv i b2 hb2
      split at h
      · rename_i hc2
        rw [← Result.ok_injective h, ← hb1v, hc, ← hb2v, hc2]; simp
      · rename_i hc2
        simp only [Bool.not_eq_true] at hc2
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        rw [ihb i1 b h, hi1v, ← hb1v, hc, ← hb2v, hc2]; simp
  | @proj s j x e hs hx h1 ih =>
    intro i b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    rw [inductives.struct_parts.has_loose_bvar.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [ih i b h]
    simp [ConLeche.Expr.hasLooseBVar]

/-- `has_loose_bvar` at its own statement. -/
theorem has_loose_bvar_refines {i : Std.U64} {e : expr.Expr} {b : Bool}
    (he : ExprWF e) (h : inductives.struct_parts.has_loose_bvar i e = ok b) :
    b = ConLeche.Expr.hasLooseBVar i.val (absExpr e) :=
  has_loose_bvar_refines_aux he i b h

/-- `ConLeche/Kernel/Inductives/StructParts.lean:371-390` —
`has_loose_bvar_b_spec` refines `Expr.hasLooseBVarB`: `hasLooseBVar` with the
packed bound's cutoff.  The *logical* definition; the executed one is
`has_loose_bvar_b` below (the `@[csimp]` family, module note). -/
theorem has_loose_bvar_b_spec_refines_aux {e : expr.Expr} (he : ExprWF e) :
    ∀ (i : Std.U64) (b : Bool),
      inductives.struct_parts.has_loose_bvar_b_spec i e = ok b →
      b = ConLeche.Expr.hasLooseBVarB i.val (absExpr e) := by
  induction he with
  | @bvar j e h1 =>
    intro i b h
    obtain ⟨d, hde, -, -, -⟩ := Expr.bvar_inv h1
    have hewf : ExprWF e := ExprWF.bvar h1
    have habs : absExpr e = .bvar j.val := by rw [hde]; simp
    rw [inductives.struct_parts.has_loose_bvar_b_spec.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      rw [← Result.ok_injective h, ConLeche.Expr.hasLooseBVarB.eq_def,
        if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
    · rename_i hle
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      rw [← Result.ok_injective h, ConLeche.Expr.hasLooseBVarB.eq_def,
        if_neg (show ¬ (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac), habs]
      refine Bool.eq_iff_iff.mpr ?_
      simp only [decide_eq_true_eq, beq_iff_eq]
      exact ⟨fun hc => by rw [hc], fun hc => Std.UScalar.eq_of_val_eq hc⟩
  | @fvar idx ty e hty h1 ih =>
    intro i b h
    obtain ⟨d, hde, -, -, -⟩ := Expr.fvar_inv h1
    have habs : absExpr e = .fvar idx.val (absExpr ty) := by rw [hde]; simp
    have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
      rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def]; split <;> rfl
    rw [inductives.struct_parts.has_loose_bvar_b_spec.eq_def, hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rw [← Result.ok_injective h, hspec]
    · simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      rw [← Result.ok_injective h, hspec]
  | @sort u e hu h1 =>
    intro i b h
    obtain ⟨d, bw, -, hde, -, -, -⟩ := Expr.sort_inv h1
    have habs : absExpr e = .sort (absLevel u) := by rw [hde]; simp
    have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
      rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def]; split <;> rfl
    rw [inductives.struct_parts.has_loose_bvar_b_spec.eq_def, hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rw [← Result.ok_injective h, hspec]
    · simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      rw [← Result.ok_injective h, hspec]
  | @mk_const n us e hn hus h1 =>
    intro i b h
    obtain ⟨d, bw, -, hde, -, -, -⟩ := Expr.mk_const_inv h1
    have habs : absExpr e = .const (absName n) (absLevels us) := by rw [hde]; simp
    have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
      rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def]; split <;> rfl
    rw [inductives.struct_parts.has_loose_bvar_b_spec.eq_def, hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rw [← Result.ok_injective h, hspec]
    · simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      rw [← Result.ok_injective h, hspec]
  | @lit l e hl h1 =>
    intro i b h
    obtain ⟨d, hde, -, -, -⟩ := Expr.lit_inv h1
    have habs : absExpr e = .lit (absLiteral l) := by rw [hde]; simp
    have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
      rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def]; split <;> rfl
    rw [inductives.struct_parts.has_loose_bvar_b_spec.eq_def, hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rw [← Result.ok_injective h, hspec]
    · simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      rw [← Result.ok_injective h, hspec]
  | @app f a e hf ha h1 ihf iha =>
    intro i b h
    obtain ⟨d, hde, -, -, -⟩ := Expr.app_inv h1
    have hewf : ExprWF e := ExprWF.app hf ha h1
    have habs : absExpr e = .app (absExpr f) (absExpr a) := by rw [hde]; simp
    rw [inductives.struct_parts.has_loose_bvar_b_spec.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      rw [← Result.ok_injective h, ConLeche.Expr.hasLooseBVarB.eq_def,
        if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
    · rename_i hle
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
          = (ConLeche.Expr.hasLooseBVarB i.val (absExpr f)
             || ConLeche.Expr.hasLooseBVarB i.val (absExpr a)) := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def,
          if_neg (show ¬ ((absExpr f).app (absExpr a)).bvarB ≤ i.val by
            rw [← habs, ← hbbv]; scalar_tac)]
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := ihf i b1 hb1
      rw [hspec]
      split at h
      · rename_i hc
        rw [← Result.ok_injective h, ← hb1v, hc]; simp
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        rw [iha i b h, ← hb1v, hc]; simp
  | @lam ty bo m e hty hbo hm h1 iht ihb =>
    intro i b h
    obtain ⟨d, hde, -, -, -⟩ := Expr.lam_inv h1
    have hewf : ExprWF e := ExprWF.lam hty hbo hm h1
    have habs : absExpr e = .lam (absExpr ty) (absExpr bo) (absBinderMeta m) := by
      rw [hde]; simp
    rw [inductives.struct_parts.has_loose_bvar_b_spec.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      rw [← Result.ok_injective h, ConLeche.Expr.hasLooseBVarB.eq_def,
        if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
    · rename_i hle
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
          = (ConLeche.Expr.hasLooseBVarB i.val (absExpr ty)
             || ConLeche.Expr.hasLooseBVarB (i.val + 1) (absExpr bo)) := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def,
          if_neg (show ¬ ((absExpr ty).lam (absExpr bo) (absBinderMeta m)).bvarB
              ≤ i.val by rw [← habs, ← hbbv]; scalar_tac)]
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := iht i b1 hb1
      rw [hspec]
      split at h
      · rename_i hc
        rw [← Result.ok_injective h, ← hb1v, hc]; simp
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        rw [ihb i2 b h, hi2v, ← hb1v, hc]; simp
  | @forall_e ty bo m e hty hbo hm h1 iht ihb =>
    intro i b h
    obtain ⟨d, hde, -, -, -⟩ := Expr.forall_e_inv h1
    have hewf : ExprWF e := ExprWF.forall_e hty hbo hm h1
    have habs : absExpr e = .forallE (absExpr ty) (absExpr bo) (absBinderMeta m) := by
      rw [hde]; simp
    rw [inductives.struct_parts.has_loose_bvar_b_spec.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      rw [← Result.ok_injective h, ConLeche.Expr.hasLooseBVarB.eq_def,
        if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
    · rename_i hle
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
          = (ConLeche.Expr.hasLooseBVarB i.val (absExpr ty)
             || ConLeche.Expr.hasLooseBVarB (i.val + 1) (absExpr bo)) := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def,
          if_neg (show ¬ ((absExpr ty).forallE (absExpr bo) (absBinderMeta m)).bvarB
              ≤ i.val by rw [← habs, ← hbbv]; scalar_tac)]
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := iht i b1 hb1
      rw [hspec]
      split at h
      · rename_i hc
        rw [← Result.ok_injective h, ← hb1v, hc]; simp
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        rw [ihb i2 b h, hi2v, ← hb1v, hc]; simp
  | @let_e ty w bo e hty hw hbo h1 iht ihv ihb =>
    intro i b h
    obtain ⟨d, hde, -, -, -⟩ := Expr.let_e_inv h1
    have hewf : ExprWF e := ExprWF.let_e hty hw hbo h1
    have habs : absExpr e = .letE (absExpr ty) (absExpr w) (absExpr bo) := by
      rw [hde]; simp
    rw [inductives.struct_parts.has_loose_bvar_b_spec.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      rw [← Result.ok_injective h, ConLeche.Expr.hasLooseBVarB.eq_def,
        if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
    · rename_i hle
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
          = (ConLeche.Expr.hasLooseBVarB i.val (absExpr ty)
             || ConLeche.Expr.hasLooseBVarB i.val (absExpr w)
             || ConLeche.Expr.hasLooseBVarB (i.val + 1) (absExpr bo)) := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def,
          if_neg (show ¬ ((absExpr ty).letE (absExpr w) (absExpr bo)).bvarB
              ≤ i.val by rw [← habs, ← hbbv]; scalar_tac)]
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1v := iht i b1 hb1
      rw [hspec]
      split at h
      · rename_i hc
        rw [← Result.ok_injective h, ← hb1v, hc]; simp
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
        have hb2v := ihv i b2 hb2
        split at h
        · rename_i hc2
          rw [← Result.ok_injective h, ← hb1v, hc, ← hb2v, hc2]; simp
        · rename_i hc2
          simp only [Bool.not_eq_true] at hc2
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
          rw [ihb i2 b h, hi2v, ← hb1v, hc, ← hb2v, hc2]; simp
  | @proj s j x e hs hx h1 ih =>
    intro i b h
    obtain ⟨d, hde, -, -, -⟩ := Expr.proj_inv h1
    have hewf : ExprWF e := ExprWF.proj hs hx h1
    have habs : absExpr e = .proj (absName s) j.val (absExpr x) := by rw [hde]; simp
    rw [inductives.struct_parts.has_loose_bvar_b_spec.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      rw [← Result.ok_injective h, ConLeche.Expr.hasLooseBVarB.eq_def,
        if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
    · rename_i hle
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
          = ConLeche.Expr.hasLooseBVarB i.val (absExpr x) := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def,
          if_neg (show ¬ (ConLeche.Expr.proj (absName s) j.val (absExpr x)).bvarB
              ≤ i.val by rw [← habs, ← hbbv]; scalar_tac)]
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      rw [ih i b h, hspec]

/-- `has_loose_bvar_b_spec` at its own statement. -/
theorem has_loose_bvar_b_spec_refines {i : Std.U64} {e : expr.Expr} {b : Bool}
    (he : ExprWF e)
    (h : inductives.struct_parts.has_loose_bvar_b_spec i e = ok b) :
    b = ConLeche.Expr.hasLooseBVarB i.val (absExpr e) :=
  has_loose_bvar_b_spec_refines_aux he i b h

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

/-- The five **rebuilding** node kinds — the ones `hasLooseBVarBGo`'s miss
branch reaches.  The `_ => (false, memo)` arm of `has_loose_bvar_b_node` is
con-leche's cited *unreachable* one (the five leaf kinds answer before the
probe), so the node lemma below is stated at exactly the kinds the walk calls
it on; at a leaf the port's arm and `Expr.hasLooseBVarB` genuinely disagree
(`hasLooseBVarB 0 (.bvar 0)` is `true`), which is why the guard is part of the
statement. -/
def Rebuilding (e : expr.Expr) : Prop :=
  match e._0.kind with
  | .App _ _ => True
  | .Lam _ _ _ => True
  | .«ForallE» _ _ _ => True
  | .LetE _ _ _ => True
  | .Proj _ _ _ => True
  | _ => False

/-- "`has_loose_bvar_b_go` answers `Expr.hasLooseBVarB` at this node and keeps
con-leche's `LooseBVarMemoInv`" — the walk's half of the induction. -/
def LooseGoOK (e : expr.Expr) : Prop :=
  ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool) (i : Std.U64)
    (r : Bool),
    ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo →
    inductives.struct_parts.has_loose_bvar_b_go memo i e = ok (r, memo') →
    r = ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
      ∧ ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo'

/-- The same for the miss branch's `has_loose_bvar_b_node`, at the five
rebuilding kinds and below the cutoff — which is where the walk calls it. -/
def LooseNodeOK (e : expr.Expr) : Prop :=
  ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool) (i : Std.U64)
    (r : Bool),
    Rebuilding e → i.val < (absExpr e).bvarB →
    ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo →
    inductives.struct_parts.has_loose_bvar_b_node memo i e = ok (r, memo') →
    r = ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
      ∧ ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo'

/-- The probe-and-record step the five rebuilding arms of
`has_loose_bvar_b_go` share. -/
theorem loose_probe_step {e : expr.Expr} (he : ExprWF e)
    (hnode : LooseNodeOK e) (hre : Rebuilding e)
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool} {i : Std.U64}
    {key : expr_ops.ExprNatKey} {o : Option Bool} {r : Bool}
    (hcut : i.val < (absExpr e).bvarB)
    (hm : ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo)
    (h : (match o with
          | none => do
              let (r, memo1) ←
                inductives.struct_parts.has_loose_bvar_b_node memo i e
              let memo2 ←
                inductives.struct_parts.has_loose_bvar_b_ins memo1 e i r
              ok (r, memo2)
          | some r => ok (r, memo)) = ok (r, memo'))
    (hkey : expr_ops.expr_nat_key e i = ok key)
    (hprobe : inductives.struct_parts.memo_b_get memo key = ok o) :
    r = ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
      ∧ ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo' := by
  have hkv : key = ⟨e, i⟩ := ExprOps.expr_nat_key_eq hkey
  cases o with
  | some r0 =>
    obtain ⟨hr, hmm⟩ := pair_ok h
    have hq : LooseQ (ExprOps.absKey key) r0 :=
      ExprOps.MemoInv.hit ExprOps.key_exact hm (by rw [hkv]; exact he)
        (memo_b_get_eq hprobe)
    rw [hkv] at hq
    rw [← hr, ← hmm]
    exact ⟨hq, hm⟩
  | none =>
    obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, memo1⟩ := p
    obtain ⟨hr1, hm1⟩ := hnode memo memo1 i r1 hre hcut hm hnd
    obtain ⟨memo2, hins, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hr, hmm⟩ := pair_ok h
    rw [← hr, ← hmm]
    exact ⟨hr1, has_loose_bvar_b_ins_inv he hm1 hr1 hins⟩

/-- `ConLeche/Kernel/Inductives/StructParts.lean:442-478` — **the memoized
`hasLooseBVarB` walk**, both halves at once (they are mutually recursive), by
induction on the `ExprWF` derivation.  This is con-leche's
`hasLooseBVarBGo_spec` restated over the port's `&mut HashMap`; the cutoff and
the memo are complementary, and the walk **does** short-circuit. -/
theorem has_loose_bvar_b_walk {e : expr.Expr} (he : ExprWF e) :
    LooseGoOK e ∧ LooseNodeOK e := by
  induction he with
  | @bvar j e h1 =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.bvar_inv h1
    have hewf : ExprWF e := ExprWF.bvar h1
    constructor
    · intro memo memo' i r hm h
      have habs : absExpr e = .bvar j.val := by rw [hde]; simp
      rw [inductives.struct_parts.has_loose_bvar_b_go.eq_def, hde] at h
      rw [← hde] at h
      obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
      have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
      split at h
      · rename_i hle
        have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
          rw [ConLeche.Expr.hasLooseBVarB.eq_def,
            if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, hspec]
        exact ⟨rfl, hm⟩
      · rename_i hle
        have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
            = (i.val == j.val) := by
          rw [ConLeche.Expr.hasLooseBVarB.eq_def,
            if_neg (show ¬ (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac), habs]
        rw [hde] at h
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, hspec]
        refine ⟨?_, hm⟩
        refine Bool.eq_iff_iff.mpr ?_
        simp only [decide_eq_true_eq, beq_iff_eq]
        constructor
        · intro hc; rw [hc]
        · intro hc; exact Std.UScalar.eq_of_val_eq hc
    · intro memo memo' i r hre hcut hm h
      rw [hde] at hre
      simp [Rebuilding] at hre
  | @sort u e hu h1 =>
    obtain ⟨d, bw, -, hde, -, -, -⟩ := Expr.sort_inv h1
    have hewf : ExprWF e := ExprWF.sort hu h1
    have habs : absExpr e = .sort (absLevel u) := by rw [hde]; simp
    constructor
    · intro memo memo' i r hm h
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def]; split <;> rfl
      rw [inductives.struct_parts.has_loose_bvar_b_go.eq_def, hde] at h
      obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · rename_i hle
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, hspec]
        exact ⟨rfl, hm⟩
      · rename_i hle
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, hspec]
        exact ⟨rfl, hm⟩
    · intro memo memo' i r hre hcut hm h
      rw [hde] at hre
      simp [Rebuilding] at hre
  | @lit l e hl h1 =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.lit_inv h1
    have hewf : ExprWF e := ExprWF.lit hl h1
    have habs : absExpr e = .lit (absLiteral l) := by rw [hde]; simp
    constructor
    · intro memo memo' i r hm h
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def]; split <;> rfl
      rw [inductives.struct_parts.has_loose_bvar_b_go.eq_def, hde] at h
      obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · rename_i hle
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, hspec]
        exact ⟨rfl, hm⟩
      · rename_i hle
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, hspec]
        exact ⟨rfl, hm⟩
    · intro memo memo' i r hre hcut hm h
      rw [hde] at hre
      simp [Rebuilding] at hre
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, bw, -, hde, -, -, -⟩ := Expr.mk_const_inv h1
    have hewf : ExprWF e := ExprWF.mk_const hn hus h1
    have habs : absExpr e = .const (absName n) (absLevels us) := by rw [hde]; simp
    constructor
    · intro memo memo' i r hm h
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def]; split <;> rfl
      rw [inductives.struct_parts.has_loose_bvar_b_go.eq_def, hde] at h
      obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · rename_i hle
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, hspec]
        exact ⟨rfl, hm⟩
      · rename_i hle
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, hspec]
        exact ⟨rfl, hm⟩
    · intro memo memo' i r hre hcut hm h
      rw [hde] at hre
      simp [Rebuilding] at hre
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.fvar_inv h1
    have hewf : ExprWF e := ExprWF.fvar hty h1
    have habs : absExpr e = .fvar idx.val (absExpr ty) := by rw [hde]; simp
    constructor
    · intro memo memo' i r hm h
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def]; split <;> rfl
      rw [inductives.struct_parts.has_loose_bvar_b_go.eq_def, hde] at h
      obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · rename_i hle
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, hspec]
        exact ⟨rfl, hm⟩
      · rename_i hle
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, hspec]
        exact ⟨rfl, hm⟩
    · intro memo memo' i r hre hcut hm h
      rw [hde] at hre
      simp [Rebuilding] at hre
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.app_inv h1
    have hewf : ExprWF e := ExprWF.app hf ha h1
    have habs : absExpr e = .app (absExpr f) (absExpr a) := by rw [hde]; simp
    have hre : Rebuilding e := by rw [hde]; simp [Rebuilding]
    have hnode : LooseNodeOK e := by
      intro memo memo' i r _ hcut hm h
      rw [inductives.struct_parts.has_loose_bvar_b_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, h1', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, memo1⟩ := p1
      obtain ⟨hb1, hm1⟩ := ihf.1 memo memo1 i b1 hm h1'
      replace h : (if b1 = true then ok (true, memo1)
          else inductives.struct_parts.has_loose_bvar_b_go memo1 i a)
            = ok (r, memo') := h
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
          = (ConLeche.Expr.hasLooseBVarB i.val (absExpr f)
             || ConLeche.Expr.hasLooseBVarB i.val (absExpr a)) := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def,
          if_neg (by rw [← habs]; omega)]
      rw [hspec]
      split at h
      · rename_i hc
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, ← hb1, hc]; exact ⟨by simp, hm1⟩
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        obtain ⟨hb2, hm2⟩ := iha.1 memo1 memo' i r hm1 h
        rw [hb2, ← hb1, hc]; exact ⟨by simp, hm2⟩
    refine ⟨?_, hnode⟩
    intro memo memo' i r hm h
    rw [inductives.struct_parts.has_loose_bvar_b_go.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
        rw [ConLeche.Expr.hasLooseBVarB.eq_def,
          if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
      obtain ⟨hr, hmm⟩ := pair_ok h
      rw [← hr, ← hmm, hspec]
      exact ⟨rfl, hm⟩
    · rename_i hle
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
      rw [← hde] at hkey h
      exact loose_probe_step hewf hnode hre
        (show i.val < (absExpr e).bvarB by rw [← hbbv]; scalar_tac) hm h hkey hprobe
  | @lam ty bo m e hty hbo hm0 h1 iht ihb =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.lam_inv h1
    have hewf : ExprWF e := ExprWF.lam hty hbo hm0 h1
    have habs : absExpr e = .lam (absExpr ty) (absExpr bo) (absBinderMeta m) := by
      rw [hde]; simp
    have hre : Rebuilding e := by rw [hde]; simp [Rebuilding]
    have hnode : LooseNodeOK e := by
      intro memo memo' i r _ hcut hm h
      rw [inductives.struct_parts.has_loose_bvar_b_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, h1', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, memo1⟩ := p1
      obtain ⟨hb1, hm1⟩ := iht.1 memo memo1 i b1 hm h1'
      replace h : (if b1 = true then ok (true, memo1)
          else do
            let i1 ← i + 1#u64
            inductives.struct_parts.has_loose_bvar_b_go memo1 i1 bo)
            = ok (r, memo') := h
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
          = (ConLeche.Expr.hasLooseBVarB i.val (absExpr ty)
             || ConLeche.Expr.hasLooseBVarB (i.val + 1) (absExpr bo)) := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def,
          if_neg (by rw [← habs]; omega)]
      rw [hspec]
      split at h
      · rename_i hc
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, ← hb1, hc]; exact ⟨by simp, hm1⟩
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨hb2, hm2⟩ := ihb.1 memo1 memo' i2 r hm1 h
        rw [hb2, hi2v, ← hb1, hc]; exact ⟨by simp, hm2⟩
    refine ⟨?_, hnode⟩
    intro memo memo' i r hm h
    rw [inductives.struct_parts.has_loose_bvar_b_go.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
        rw [ConLeche.Expr.hasLooseBVarB.eq_def,
          if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
      obtain ⟨hr, hmm⟩ := pair_ok h
      rw [← hr, ← hmm, hspec]
      exact ⟨rfl, hm⟩
    · rename_i hle
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
      rw [← hde] at hkey h
      exact loose_probe_step hewf hnode hre
        (show i.val < (absExpr e).bvarB by rw [← hbbv]; scalar_tac) hm h hkey hprobe
  | @forall_e ty bo m e hty hbo hm0 h1 iht ihb =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.forall_e_inv h1
    have hewf : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    have habs : absExpr e = .forallE (absExpr ty) (absExpr bo) (absBinderMeta m) := by
      rw [hde]; simp
    have hre : Rebuilding e := by rw [hde]; simp [Rebuilding]
    have hnode : LooseNodeOK e := by
      intro memo memo' i r _ hcut hm h
      rw [inductives.struct_parts.has_loose_bvar_b_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, h1', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, memo1⟩ := p1
      obtain ⟨hb1, hm1⟩ := iht.1 memo memo1 i b1 hm h1'
      replace h : (if b1 = true then ok (true, memo1)
          else do
            let i1 ← i + 1#u64
            inductives.struct_parts.has_loose_bvar_b_go memo1 i1 bo)
            = ok (r, memo') := h
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
          = (ConLeche.Expr.hasLooseBVarB i.val (absExpr ty)
             || ConLeche.Expr.hasLooseBVarB (i.val + 1) (absExpr bo)) := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def,
          if_neg (by rw [← habs]; omega)]
      rw [hspec]
      split at h
      · rename_i hc
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, ← hb1, hc]; exact ⟨by simp, hm1⟩
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨hb2, hm2⟩ := ihb.1 memo1 memo' i2 r hm1 h
        rw [hb2, hi2v, ← hb1, hc]; exact ⟨by simp, hm2⟩
    refine ⟨?_, hnode⟩
    intro memo memo' i r hm h
    rw [inductives.struct_parts.has_loose_bvar_b_go.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
        rw [ConLeche.Expr.hasLooseBVarB.eq_def,
          if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
      obtain ⟨hr, hmm⟩ := pair_ok h
      rw [← hr, ← hmm, hspec]
      exact ⟨rfl, hm⟩
    · rename_i hle
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
      rw [← hde] at hkey h
      exact loose_probe_step hewf hnode hre
        (show i.val < (absExpr e).bvarB by rw [← hbbv]; scalar_tac) hm h hkey hprobe
  | @let_e ty w bo e hty hw hbo h1 iht ihv ihb =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.let_e_inv h1
    have hewf : ExprWF e := ExprWF.let_e hty hw hbo h1
    have habs : absExpr e = .letE (absExpr ty) (absExpr w) (absExpr bo) := by
      rw [hde]; simp
    have hre : Rebuilding e := by rw [hde]; simp [Rebuilding]
    have hnode : LooseNodeOK e := by
      intro memo memo' i r _ hcut hm h
      rw [inductives.struct_parts.has_loose_bvar_b_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, h1', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, memo1⟩ := p1
      obtain ⟨hb1, hm1⟩ := iht.1 memo memo1 i b1 hm h1'
      replace h : (if b1 = true then ok (true, memo1)
          else do
            let (b2, memo2) ←
              inductives.struct_parts.has_loose_bvar_b_go memo1 i w
            if b2 = true then ok (true, memo2)
            else do
              let i1 ← i + 1#u64
              inductives.struct_parts.has_loose_bvar_b_go memo2 i1 bo)
            = ok (r, memo') := h
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
          = (ConLeche.Expr.hasLooseBVarB i.val (absExpr ty)
             || ConLeche.Expr.hasLooseBVarB i.val (absExpr w)
             || ConLeche.Expr.hasLooseBVarB (i.val + 1) (absExpr bo)) := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def,
          if_neg (by rw [← habs]; omega)]
      rw [hspec]
      split at h
      · rename_i hc
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, ← hb1, hc]; exact ⟨by simp, hm1⟩
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        obtain ⟨p2, h2', h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨b2, memo2⟩ := p2
        obtain ⟨hb2, hm2⟩ := ihv.1 memo1 memo2 i b2 hm1 h2'
        replace h : (if b2 = true then ok (true, memo2)
            else do
              let i1 ← i + 1#u64
              inductives.struct_parts.has_loose_bvar_b_go memo2 i1 bo)
              = ok (r, memo') := h
        split at h
        · rename_i hc2
          obtain ⟨hr, hmm⟩ := pair_ok h
          rw [← hr, ← hmm, ← hb1, hc, ← hb2, hc2]; exact ⟨by simp, hm2⟩
        · rename_i hc2
          simp only [Bool.not_eq_true] at hc2
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
          obtain ⟨hb3, hm3⟩ := ihb.1 memo2 memo' i2 r hm2 h
          rw [hb3, hi2v, ← hb1, hc, ← hb2, hc2]; exact ⟨by simp, hm3⟩
    refine ⟨?_, hnode⟩
    intro memo memo' i r hm h
    rw [inductives.struct_parts.has_loose_bvar_b_go.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
        rw [ConLeche.Expr.hasLooseBVarB.eq_def,
          if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
      obtain ⟨hr, hmm⟩ := pair_ok h
      rw [← hr, ← hmm, hspec]
      exact ⟨rfl, hm⟩
    · rename_i hle
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
      rw [← hde] at hkey h
      exact loose_probe_step hewf hnode hre
        (show i.val < (absExpr e).bvarB by rw [← hbbv]; scalar_tac) hm h hkey hprobe
  | @proj s j x e hs hx h1 ih =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.proj_inv h1
    have hewf : ExprWF e := ExprWF.proj hs hx h1
    have habs : absExpr e = .proj (absName s) j.val (absExpr x) := by rw [hde]; simp
    have hre : Rebuilding e := by rw [hde]; simp [Rebuilding]
    have hnode : LooseNodeOK e := by
      intro memo memo' i r _ hcut hm h
      rw [inductives.struct_parts.has_loose_bvar_b_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨hb1, hm1⟩ := ih.1 memo memo' i r hm h
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
          = ConLeche.Expr.hasLooseBVarB i.val (absExpr x) := by
        rw [habs, ConLeche.Expr.hasLooseBVarB.eq_def,
          if_neg (by rw [← habs]; omega)]
      rw [hspec]
      exact ⟨hb1, hm1⟩
    refine ⟨?_, hnode⟩
    intro memo memo' i r hm h
    rw [inductives.struct_parts.has_loose_bvar_b_go.eq_def, hde] at h
    rw [← hde] at h
    obtain ⟨i1, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv : i1.val = (absExpr e).bvarB := ExprOps.bvar_b_refines hewf hbb
    split at h
    · rename_i hle
      have hspec : ConLeche.Expr.hasLooseBVarB i.val (absExpr e) = false := by
        rw [ConLeche.Expr.hasLooseBVarB.eq_def,
          if_pos (show (absExpr e).bvarB ≤ i.val by rw [← hbbv]; scalar_tac)]
      obtain ⟨hr, hmm⟩ := pair_ok h
      rw [← hr, ← hmm, hspec]
      exact ⟨rfl, hm⟩
    · rename_i hle
      rw [hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
      rw [← hde] at hkey h
      exact loose_probe_step hewf hnode hre
        (show i.val < (absExpr e).bvarB by rw [← hbbv]; scalar_tac) hm h hkey hprobe

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
        ∧ ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo' :=
  (has_loose_bvar_b_walk he).1

/-- `ConLeche/Kernel/Inductives/StructParts.lean:442-478` —
`has_loose_bvar_b_node` refines the inner `match e with` of
`hasLooseBVarBGo`'s miss branch, split off in the port so that the probe's
borrow dies before the descent mutates the memo (task #14's rule).  Stated at
the five rebuilding kinds and below the cutoff, which is exactly where the walk
calls it: the port's `_ => (false, memo)` arm is the cited *unreachable* one,
and at a leaf it does not agree with `Expr.hasLooseBVarB`. -/
theorem has_loose_bvar_b_node_refines {e : expr.Expr} (he : ExprWF e)
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool}
    {i : Std.U64} {r : Bool}
    (hre : Rebuilding e) (hcut : i.val < (absExpr e).bvarB)
    (hm : ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo)
    (h : inductives.struct_parts.has_loose_bvar_b_node memo i e = ok (r, memo')) :
    r = ConLeche.Expr.hasLooseBVarB i.val (absExpr e)
      ∧ ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo' :=
  (has_loose_bvar_b_walk he).2 memo memo' i r hre hcut hm h

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
    (hcty : ExprWF cty) (N : Nat) :
    ∀ (n base : Std.U64)
      (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool)
      (out v : alloc.vec.Vec Bool),
      n.val = N →
      ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo →
      inductives.struct_parts.struct_used_later_list memo cty n_p n base out
        = ok (v, memo') →
      v.val = out.val ++ (List.range n.val).map
          (fun t => ConLeche.structUsedLater (absExpr cty) n_p.val (base.val + t))
        ∧ ExprOps.MemoInv ExprOps.KeyWF ExprOps.absKey LooseQ memo' := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n base memo memo' out v hN hm h
    rw [inductives.struct_parts.struct_used_later_list.eq_def] at h
    split at h
    · rename_i hn0
      have hnv : n.val = 0 := by rw [hn0]; scalar_tac
      have hp : (out, memo) = (v, memo') := by simpa using h
      have h1 : v = out := (congrArg Prod.fst hp).symm
      have h2 : memo' = memo := (congrArg Prod.snd hp).symm
      rw [h1, h2, hnv]
      exact ⟨by simp, hm⟩
    · rename_i hn0
      obtain ⟨m0, hm0⟩ : ∃ m0, n.val = m0 + 1 := by
        have : n.val ≠ 0 := fun hc => hn0 (Std.UScalar.eq_of_val_eq (by rw [hc]; scalar_tac))
        exact ⟨n.val - 1, by omega⟩
      obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, memo1⟩ := p
      obtain ⟨habsr, hm1⟩ := struct_used_later_go_refines hcty hm hgo
      obtain ⟨out1, hpush, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, hrec⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = m0 := by rw [HashMap.uscalar_sub_eq hi, hm0]; scalar_tac
      have hi1v : i1.val = base.val + 1 := HashMap.uscalar_add_eq hi1
      obtain ⟨hlist, hm2⟩ := ih m0 (by omega) i i1 memo1 memo' out1 v hiv hm1 hrec
      refine ⟨?_, hm2⟩
      rw [hlist, hiv, hi1v, vec_push_val hpush, habsr, hm0,
        List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero,
        List.append_assoc, List.cons_append, List.nil_append]
      congr 2
      refine List.map_congr_left ?_
      intro x _
      congr 1
      omega

/-- `struct_parts::sort_get_d` is the out-of-range fallback the guard fold
spells at every read (`sorts.getD i .zero`; no cited definition of its own).

`i.val ≤ Std.Usize.max` is `Refine/Scalars.lean`'s `u64 → usize` width side
condition, not a weakening: the port writes `(i as usize) < sorts.len()`, and
Aeneas keeps `usize`'s width abstract (`System.Platform.numBits_eq`), so the
model has to say that the cast does not wrap.  It stays a hypothesis because
`i` is a free `u64` here — nothing relates it to `sorts` — and every caller
discharges it from the `Vec` its own counter came from. -/
theorem sort_get_d_refines {sorts : alloc.vec.Vec level.Level} {i : Std.U64}
    {u : level.Level} (hsorts : LevelsWF sorts) (hi : i.val ≤ Std.Usize.max)
    (h : inductives.struct_parts.sort_get_d sorts i = ok u) :
    absLevel u = (absLevels sorts).getD i.val .zero ∧ LevelWF u := by
  rw [inductives.struct_parts.sort_get_d] at h
  simp only [lift_eq, bind_tc_ok] at h
  have hcv : (Std.UScalar.cast .Usize i).val = i.val := Scalars.u64_cast_usize_val hi
  split at h
  · rename_i hlt
    have hltv : i.val < sorts.val.length := by
      have := alloc.vec.Vec.len_val sorts; scalar_tac
    obtain ⟨l, hidx, hdup⟩ := bind_eq_ok_iff.mp h
    have hg := ExprOps.vec_index_getElem? hidx
    rw [hcv, List.getElem?_eq_getElem hltv] at hg
    have hlv : sorts.val[i.val] = l := Option.some_injective _ hg
    have hue : l = u := Result.ok_injective (by rw [← hdup]; simp)
    refine ⟨?_, by rw [← hue]; exact hsorts l (by rw [← hlv]; exact List.getElem_mem hltv)⟩
    rw [← hue, absLevels, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hltv, hlv]
    simp
  · rename_i hge
    have hgev : sorts.val.length ≤ i.val := by
      have := alloc.vec.Vec.len_val sorts; scalar_tac
    refine ⟨?_, LevelWF.zero h⟩
    rw [Level.zero_refines h, absLevels, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa using hgev)]
    rfl

/-- `ConLeche/Kernel/Inductives/StructParts.lean:643-656`, `:722-732` —
`struct_proj_guard_at` refines the inner `(List.range i).foldl` of the guard
table from index `j`: field `i`'s own sort joined with the sorts of the earlier
fields a later field uses.  `i.val ≤ Std.Usize.max` is `sort_get_d_refines`'
width side condition (`Refine/Scalars.lean`), which every `j < i` inherits. -/
theorem struct_proj_guard_at_refines {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec level.Level} (hsorts : LevelsWF sorts) (N : Nat) :
    ∀ (i j : Std.U64) (acc u : level.Level), i.val - j.val = N →
      i.val ≤ Std.Usize.max → LevelWF acc →
      inductives.struct_parts.struct_proj_guard_at used sorts i j acc = ok u →
      absLevel u = (List.range' j.val (i.val - j.val)).foldl
          (fun a k => if used.val.getD k false
            then .max a ((absLevels sorts).getD k .zero) else a)
          (absLevel acc)
        ∧ LevelWF u := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i j acc u hN hi hacc h
    rw [inductives.struct_parts.struct_proj_guard_at.eq_def] at h
    split at h
    · rename_i hge
      have hz : i.val - j.val = 0 := by scalar_tac
      have hu : u = acc := (Result.ok_injective h).symm
      subst hu
      rw [hz]
      exact ⟨by simp, hacc⟩
    · rename_i hge
      have hlt : j.val < i.val := by scalar_tac
      have hjmax : j.val ≤ Std.Usize.max := by omega
      have hcv : (Std.UScalar.cast .Usize j).val = j.val :=
        Scalars.u64_cast_usize_val hjmax
      simp only [lift_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨ub, hub, acc2, hacc2, i3, hi3, h⟩ := h
      have hubv : ub = used.val.getD j.val false := by
        split at hub
        · rename_i hlt2
          have hltv : j.val < used.val.length := by
            have := alloc.vec.Vec.len_val used; scalar_tac
          have hg := ExprOps.vec_index_getElem? hub
          rw [hcv, List.getElem?_eq_getElem hltv] at hg
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltv]
          simpa using (Option.some_injective _ hg).symm
        · rename_i hge2
          have hgev : used.val.length ≤ j.val := by
            have := alloc.vec.Vec.len_val used; scalar_tac
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          simpa using (Result.ok_injective hub).symm
      have hacc2v : absLevel acc2
          = (if used.val.getD j.val false
             then .max (absLevel acc) ((absLevels sorts).getD j.val .zero)
             else absLevel acc) ∧ LevelWF acc2 := by
        split at hacc2
        · rename_i hut
          obtain ⟨l, hl, hmax⟩ := bind_eq_ok_iff.mp hacc2
          obtain ⟨hlabs, hlwf⟩ := sort_get_d_refines hsorts hjmax hl
          rw [← hubv, hut]
          exact ⟨by rw [Level.max_refines hmax, hlabs]; simp,
            LevelWF.max hacc hlwf hmax⟩
        · rename_i huf
          simp only [Bool.not_eq_true] at huf
          rw [← hubv, huf]
          have : acc = acc2 := Result.ok_injective hacc2
          rw [← this]
          exact ⟨by simp, hacc⟩
      have hi3v : i3.val = j.val + 1 := HashMap.uscalar_add_eq hi3
      have hsplit : i.val - j.val = (i.val - (j.val + 1)) + 1 := by omega
      obtain ⟨habs, hwf⟩ := ih (i.val - (j.val + 1)) (by omega) i i3 acc2 u
        (by rw [hi3v]) hi hacc2v.2 h
      refine ⟨?_, hwf⟩
      rw [habs, hi3v, hsplit, List.range'_succ, List.foldl_cons, hacc2v.1]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:722-732` —
`struct_proj_guards_from` refines the outer `(List.range nF).map` of
`structProjGuardsFast` from index `i`, accumulator in front.

`n_f.val ≤ Std.Usize.max` is `sort_get_d_refines`' width side condition
(`Refine/Scalars.lean`) at the `i < n_f` this walk reads;
`struct_proj_guards_refines` discharges it from its own `used` table. -/
theorem struct_proj_guards_from_refines {used : alloc.vec.Vec Bool}
    {sorts : alloc.vec.Vec level.Level} {n_f : Std.U64} (hsorts : LevelsWF sorts)
    (hnf : n_f.val ≤ Std.Usize.max) :
    ∀ (i : Std.U64) (out v : alloc.vec.Vec level.Level), LevelsWF out →
      inductives.struct_parts.struct_proj_guards_from used sorts n_f i out = ok v →
      absLevels v = absLevels out
          ++ (List.range' i.val (n_f.val - i.val)).map (fun k =>
              (List.range k).foldl
                (fun a j => if used.val.getD j false
                  then .max a ((absLevels sorts).getD j .zero) else a)
                ((absLevels sorts).getD k .zero))
        ∧ LevelsWF v := by
  intro i
  generalize hd : n_f.val - i.val = d
  induction d using Nat.strong_induction_on generalizing i with
  | _ d ih =>
    intro out v hout h
    rw [inductives.struct_parts.struct_proj_guards_from.eq_def] at h
    split at h
    · rename_i hge
      have hz : d = 0 := by scalar_tac
      subst hz
      have hv : v = out := (Result.ok_injective h).symm
      subst hv
      exact ⟨by simp, hout⟩
    · rename_i hge
      have hlt : i.val < n_f.val := by scalar_tac
      have himax : i.val ≤ Std.Usize.max := by omega
      simp only [bind_eq_ok_iff] at h
      obtain ⟨l, hl, l1, hl1, out1, hpush, i1, hi1, hrec⟩ := h
      obtain ⟨hlabs, hlwf⟩ := sort_get_d_refines hsorts himax hl
      obtain ⟨hl1abs, hl1wf⟩ := struct_proj_guard_at_refines hsorts
        (i.val - ((0#u64 : Std.U64)).val) i 0#u64 l l1 rfl himax hlwf hl1
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hsplit : d = (n_f.val - (i.val + 1)) + 1 := by omega
      subst hsplit
      obtain ⟨habs, hwf⟩ := ih (n_f.val - (i.val + 1)) (by omega) i1 (by rw [hi1v])
        out1 v (levelsWF_push hout hl1wf hpush) hrec
      refine ⟨?_, hwf⟩
      rw [habs, absLevels_push hpush, hl1abs, hlabs, hi1v, List.range'_succ]
      simp only [show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero,
        ← List.range_eq_range', List.map_cons, List.append_assoc,
        List.cons_append, List.nil_append]

/-- `ConLeche/Kernel/Inductives/StructParts.lean:643-656`, `:722-746` —
**the projection guard levels**: `struct_proj_guards` refines
`structProjGuards`, the *logical* definition, as con-leche executes them — the
`nF` `structUsedLater` answers first, through *one* shared `hasLooseBVarBGo`
memo, then the fold.  The cited `@[csimp]` lemma
`structProjGuards_eq_structProjGuardsFast` is what lets the port implement the
fast form and still refine the definition the model stage tables consume; the
proof is con-leche's own, `structUsedLaterList_spec` supplying the `used`
table's pointwise reading.

No platform side condition: the `used` table this builds is `nF` long and a
`Vec`'s length fits a `usize`, so `Refine/Scalars.lean`'s width bound on `nF`
is **discharged** here rather than assumed (task #59). -/
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
  obtain ⟨hused, -⟩ := struct_used_later_list_refines hcty n_f.val n_f 0#u64 memo
    memo' _ used rfl (ExprOps.new_memo_inv hnew) hlist
  -- **the width side condition, discharged** (`Refine/Scalars.lean`): the
  -- `used` table the walk just built is `nF` long, and a `Vec`'s length fits a
  -- `usize`, so `struct_proj_guards_from_refines`' hypothesis is free here
  have hnf : n_f.val ≤ Std.Usize.max := by
    have hlen : used.val.length = n_f.val := by
      rw [hused]; simp [alloc.vec.Vec.new]
    rw [← hlen]
    exact Scalars.vec_len_le_usize_max used
  have hout : LevelsWF (alloc.vec.Vec.new level.Level) := by
    intro u hu; simp [alloc.vec.Vec.new] at hu
  obtain ⟨habs, hwf⟩ := struct_proj_guards_from_refines hsorts hnf 0#u64 _ v hout h
  refine ⟨?_, hwf⟩
  rw [habs]
  simp only [absLevels, show (alloc.vec.Vec.new level.Level).val
      = ([] : List level.Level) from rfl, List.map_nil, List.nil_append,
    show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero,
    ← List.range_eq_range']
  rw [ConLeche.structProjGuards]
  refine List.map_congr_left ?_
  intro i hi
  refine foldlCongrMem _ _ ?_
  intro j hj x
  have hjlt : j < n_f.val :=
    Nat.lt_trans (List.mem_range.mp hj) (List.mem_range.mp hi)
  have huj : used.val.getD j false
      = ConLeche.structUsedLater (absExpr cty) n_p.val j := by
    rw [hused, show (alloc.vec.Vec.new Bool).val = ([] : List Bool) from rfl,
      List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show j < (List.range n_f.val).length by simpa using hjlt)]
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
`Expr.instantiate1LiftC`, which is this substitution (`structProjBodiesC_eq`). -/
theorem struct_proj_bodies_go_refines_aux {t : name.Name} (ht : NameWF t)
    (N : Nat) :
    ∀ (k i : Std.U64) (e : expr.Expr) (out : alloc.vec.Vec expr.Expr)
      (o : Option (alloc.vec.Vec expr.Expr)),
      k.val = N → ExprWF e → ExprsWF out →
      inductives.struct_parts.struct_proj_bodies_go t k i e out = ok o →
      o.map absExprs
          = (ConLeche.structProjBodiesGo (absName t) k.val i.val (absExpr e)).map
              (fun l => absExprs out ++ l)
        ∧ ∀ bs, o = some bs → ExprsWF bs := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k i e out o hN he hout h
    rw [inductives.struct_parts.struct_proj_bodies_go.eq_def] at h
    split at h
    · rename_i hk0
      have hkv : k.val = 0 := by rw [hk0]; scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h, hkv]
      exact ⟨by simp [ConLeche.structProjBodiesGo], fun bs hbs => by
        simp only [Option.some.injEq] at hbs; rw [← hbs]; exact hout⟩
    · rename_i hk0
      obtain ⟨n, hn⟩ : ∃ n, k.val = n + 1 := by
        have : k.val ≠ 0 := fun hc => hk0 (Std.UScalar.eq_of_val_eq (by rw [hc]; scalar_tac))
        exact ⟨k.val - 1, by omega⟩
      cases he with
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
        obtain ⟨c, hdup, out1, hpush, e2, he2, next, hnext, i1, hi1, i2, hi2, hrec⟩ := h
        rw [Expr.dup_eq hdup] at hpush
        obtain ⟨he2abs, he2wf⟩ := struct_proj_arg_p_refines ht he2
        obtain ⟨hnabs, hnwf⟩ := ExprOps.instantiate1_lift_refines hbo he2wf hnext
        have hi1v : i1.val = n := by
          rw [HashMap.uscalar_sub_eq hi1, hn]; scalar_tac
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨habs, hwf⟩ := ih n (by omega) i1 i2 next out1 o hi1v hnwf
          (ExprOps.exprsWF_push hout hty hpush) hrec
        refine ⟨?_, hwf⟩
        rw [habs, hi1v, hi2v, hnabs, he2abs, ExprOps.absExprs_push hpush, hn]
        simp only [absExpr_mk, absExprKind, ConLeche.structProjBodiesGo,
          show ((0#u64 : Std.U64)).val = 0 from rfl, Option.map_map]
        cases ConLeche.structProjBodiesGo (absName t) n (i.val + 1)
            ((absExpr bo).instantiate1Lift (ConLeche.structProjArgP (absName t) i.val)) with
        | none => simp
        | some l => simp
      | @bvar j e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.structProjBodiesGo], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.structProjBodiesGo], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.structProjBodiesGo], by simp⟩
      | @mk_const n2 us e hn2 hus h1 =>
        obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.structProjBodiesGo], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.structProjBodiesGo], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.structProjBodiesGo], by simp⟩
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.structProjBodiesGo], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.structProjBodiesGo], by simp⟩
      | @proj s j x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.structProjBodiesGo], by simp⟩

/-- `struct_proj_bodies_go` at its own statement. -/
theorem struct_proj_bodies_go_refines {t : name.Name} (ht : NameWF t) :
    ∀ (k i : Std.U64) (e : expr.Expr) (out : alloc.vec.Vec expr.Expr)
      (o : Option (alloc.vec.Vec expr.Expr)),
      ExprWF e → ExprsWF out →
      inductives.struct_parts.struct_proj_bodies_go t k i e out = ok o →
      o.map absExprs
          = (ConLeche.structProjBodiesGo (absName t) k.val i.val (absExpr e)).map
              (fun l => absExprs out ++ l)
        ∧ ∀ bs, o = some bs → ExprsWF bs :=
  fun k i e out o he hout h =>
    struct_proj_bodies_go_refines_aux ht k.val k i e out o rfl he hout h

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
    simp only [ExprOps.absExprs_new, List.nil_append,
      show ((0#u64 : Std.U64)).val = 0 from rfl, Option.map_id_fun', id_eq] at habs
    rw [← habs]
    cases o <;> simp

/-! ## `mentionsConst` and its memoized walk (`StructParts.lean:775-930`) -/

/-- `ConLeche/Kernel/Inductives/StructParts.lean:773-782` —
`mentions_const_spec` refines `Expr.mentionsConst`: does the constant `T` occur
in `e`?  A syntactic walk (`fvar` annotations included; a `.proj` node names
its structure).  The *logical* definition; the executed one is
`mentions_const` below. -/
theorem mentions_const_spec_refines_aux {t : name.Name} (ht : NameWF t)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ b, inductives.struct_parts.mentions_const_spec t e = ok b →
      b = ConLeche.Expr.mentionsConst (absName t) (absExpr e) := by
  induction he with
  | @bvar i e h1 =>
    intro b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    rw [inductives.struct_parts.mentions_const_spec.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.mentionsConst]
  | @sort u e hu h1 =>
    intro b h
    obtain ⟨d, bw, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    rw [inductives.struct_parts.mentions_const_spec.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.mentionsConst]
  | @lit l e hl h1 =>
    intro b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    rw [inductives.struct_parts.mentions_const_spec.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.mentionsConst]
  | @mk_const n us e hn hus h1 =>
    intro b h
    obtain ⟨d, bw, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    rw [inductives.struct_parts.mentions_const_spec.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [Name.name_beq_exact' hn ht h]
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.mentionsConst]
    refine Bool.eq_iff_iff.mpr ?_
    simp
  | @fvar idx ty e hty h1 ih =>
    intro b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    rw [inductives.struct_parts.mentions_const_spec.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [ih b h]
    simp [ConLeche.Expr.mentionsConst]
  | @app f a e hf ha h1 ihf iha =>
    intro b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    rw [inductives.struct_parts.mentions_const_spec.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := ihf b1 hb1
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.mentionsConst]
    split at h
    · rename_i hc
      rw [← Result.ok_injective h, ← hb1v, hc]; simp
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      rw [iha b h, ← hb1v, hc]; simp
  | @lam ty bo m e hty hbo hm h1 iht ihb =>
    intro b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    rw [inductives.struct_parts.mentions_const_spec.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := iht b1 hb1
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.mentionsConst]
    split at h
    · rename_i hc
      rw [← Result.ok_injective h, ← hb1v, hc]; simp
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      rw [ihb b h, ← hb1v, hc]; simp
  | @forall_e ty bo m e hty hbo hm h1 iht ihb =>
    intro b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    rw [inductives.struct_parts.mentions_const_spec.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := iht b1 hb1
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.mentionsConst]
    split at h
    · rename_i hc
      rw [← Result.ok_injective h, ← hb1v, hc]; simp
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      rw [ihb b h, ← hb1v, hc]; simp
  | @let_e ty w bo e hty hw hbo h1 iht ihv ihb =>
    intro b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    rw [inductives.struct_parts.mentions_const_spec.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := iht b1 hb1
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.mentionsConst]
    split at h
    · rename_i hc
      rw [← Result.ok_injective h, ← hb1v, hc]; simp
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2v := ihv b2 hb2
      split at h
      · rename_i hc2
        rw [← Result.ok_injective h, ← hb1v, hc, ← hb2v, hc2]; simp
      · rename_i hc2
        simp only [Bool.not_eq_true] at hc2
        rw [ihb b h, ← hb1v, hc, ← hb2v, hc2]; simp
  | @proj s j x e hs hx h1 ih =>
    intro b h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    rw [inductives.struct_parts.mentions_const_spec.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := Name.name_beq_exact' hs ht hb1
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.mentionsConst]
    split at h
    · rename_i hc
      rw [hb1v, decide_eq_true_eq] at hc
      rw [← Result.ok_injective h]
      simp [hc]
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      rw [hb1v, decide_eq_false_iff_not] at hc
      rw [ih b h]
      simp [hc]

/-- `mentions_const_spec` at its own statement. -/
theorem mentions_const_spec_refines {t : name.Name} {e : expr.Expr} {b : Bool}
    (ht : NameWF t) (he : ExprWF e)
    (h : inductives.struct_parts.mentions_const_spec t e = ok b) :
    b = ConLeche.Expr.mentionsConst (absName t) (absExpr e) :=
  mentions_const_spec_refines_aux ht he b h

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

/-- "`mentions_const_go` answers `Expr.mentionsConst` at this node and keeps
con-leche's `MentionsMemoInv`" — the walk's half of the induction. -/
def GoOK (t : name.Name) (e : expr.Expr) : Prop :=
  ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool) (r : Bool),
    ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo →
    inductives.struct_parts.mentions_const_go t memo e = ok (r, memo') →
    r = ConLeche.Expr.mentionsConst (absName t) (absExpr e)
      ∧ ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo'

/-- The same for the miss branch's `mentions_const_node`. -/
def NodeOK (t : name.Name) (e : expr.Expr) : Prop :=
  ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool) (r : Bool),
    ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo →
    inductives.struct_parts.mentions_const_node t memo e = ok (r, memo') →
    r = ConLeche.Expr.mentionsConst (absName t) (absExpr e)
      ∧ ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo'

/-- The probe-and-record step the six rebuilding arms of `mentions_const_go`
share: a hit is a correct answer (`MemoInv.hit`, over `Expr.beq`'s exactness)
and a miss recurses and writes the answer back (`MemoInv.set`). -/
theorem mentions_probe_step {t : name.Name} {e : expr.Expr} (he : ExprWF e)
    (hnode : NodeOK t e)
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {o : Option Bool}
    {r : Bool}
    (hm : ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo)
    (h : (match o with
          | none => do
              let (r, memo1) ← inductives.struct_parts.mentions_const_node t memo e
              let e1 ← expr.dup e
              let (_, memo2) ← ron.hashmap.HashMap.insert
                  expr.Expr.Insts.Con_ron_coreRonHashmapHashable
                  expr.Expr.Insts.Con_ron_coreRonHashmapEq2 memo1 e1 r
              ok (r, memo2)
          | some r => ok (r, memo)) = ok (r, memo'))
    (hprobe : inductives.struct_parts.memo_eb_get memo e = ok o) :
    r = ConLeche.Expr.mentionsConst (absName t) (absExpr e)
      ∧ ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo' := by
  cases o with
  | some r0 =>
    obtain ⟨hr, hmm⟩ := pair_ok h
    have hq : MentionsQ (absName t) (absExpr e) r0 :=
      ExprOps.MemoInv.hit ExprOps.expr_key_exact hm he (memo_eb_get_eq hprobe)
    rw [← hr, ← hmm]
    exact ⟨hq, hm⟩
  | none =>
    obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, memo1⟩ := p
    obtain ⟨hr1, hm1⟩ := hnode memo memo1 r1 hm hnd
    obtain ⟨c, hdup, h⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq hdup] at h
    obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨old, memo2⟩ := q
    obtain ⟨hr, hmm⟩ := pair_ok h
    rw [← hr, ← hmm]
    exact ⟨hr1, ExprOps.MemoInv.set ExprOps.expr_key_exact hm1 he hr1 hins⟩

/-- `ConLeche/Kernel/Inductives/StructParts.lean:814-849` — **the memoized
`mentionsConst` walk**, both halves at once (they are mutually recursive: the
walk's miss branch calls the node function, and the node function calls the
walk on the children), by induction on the `ExprWF` derivation.  This is
con-leche's `mentionsConstGo_spec` restated over the port's `&mut HashMap`. -/
theorem mentions_const_walk {t : name.Name} (ht : NameWF t) {e : expr.Expr}
    (he : ExprWF e) : GoOK t e ∧ NodeOK t e := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.bvar_inv h1
    have hewf : ExprWF e := ExprWF.bvar h1
    constructor
    · intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_go.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨hr, hmm⟩ := h
      rw [← hr, ← hmm, hde]
      exact ⟨by simp [ConLeche.Expr.mentionsConst], hm⟩
    · intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hr, hmm⟩ := h
      rw [← hr, ← hmm]
      exact ⟨mentions_const_spec_refines ht hewf (by rw [hde]; exact hb2), hm⟩
  | @sort u e hu h1 =>
    obtain ⟨d, bw, -, hde, -, -, -⟩ := Expr.sort_inv h1
    have hewf : ExprWF e := ExprWF.sort hu h1
    have habs : absExpr e = .sort (absLevel u) := by rw [hde]; simp
    constructor
    · intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_go.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨hr, hmm⟩ := h
      rw [← hr, ← hmm, hde]
      exact ⟨by simp [ConLeche.Expr.mentionsConst], hm⟩
    · intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hr, hmm⟩ := h
      rw [← hr, ← hmm]
      exact ⟨mentions_const_spec_refines ht hewf (by rw [hde]; exact hb2), hm⟩
  | @lit l e hl h1 =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.lit_inv h1
    have hewf : ExprWF e := ExprWF.lit hl h1
    have habs : absExpr e = .lit (absLiteral l) := by rw [hde]; simp
    constructor
    · intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_go.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨hr, hmm⟩ := h
      rw [← hr, ← hmm, hde]
      exact ⟨by simp [ConLeche.Expr.mentionsConst], hm⟩
    · intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hr, hmm⟩ := h
      rw [← hr, ← hmm]
      exact ⟨mentions_const_spec_refines ht hewf (by rw [hde]; exact hb2), hm⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, bw, -, hde, -, -, -⟩ := Expr.mk_const_inv h1
    have hewf : ExprWF e := ExprWF.mk_const hn hus h1
    have habs : absExpr e = .const (absName n) (absLevels us) := by rw [hde]; simp
    constructor
    · intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_go.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hr, hmm⟩ := h
      rw [← hr, ← hmm, habs, Name.name_beq_exact' hn ht hb2]
      refine ⟨?_, hm⟩
      simp only [ConLeche.Expr.mentionsConst]
      refine Bool.eq_iff_iff.mpr ?_
      simp
    · intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hr, hmm⟩ := h
      rw [← hr, ← hmm]
      exact ⟨mentions_const_spec_refines ht hewf (by rw [hde]; exact hb2), hm⟩
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.fvar_inv h1
    have hewf : ExprWF e := ExprWF.fvar hty h1
    have habs : absExpr e = .fvar idx.val (absExpr ty) := by rw [hde]; simp
    have hnode : NodeOK t e := by
      intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨hr, hm'⟩ := ih.1 memo memo' r hm h
      exact ⟨by rw [hr, habs]; simp [ConLeche.Expr.mentionsConst], hm'⟩
    refine ⟨?_, hnode⟩
    intro memo memo' r hm h
    rw [inductives.struct_parts.mentions_const_go.eq_def, hde] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
    rw [← hde] at hprobe h
    exact mentions_probe_step hewf hnode hm h hprobe
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.app_inv h1
    have hewf : ExprWF e := ExprWF.app hf ha h1
    have habs : absExpr e = .app (absExpr f) (absExpr a) := by rw [hde]; simp
    have hnode : NodeOK t e := by
      intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, h1', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, memo1⟩ := p1
      obtain ⟨hb1, hm1⟩ := ihf.1 memo memo1 b1 hm h1'
      obtain ⟨p2, h2', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b2, memo2⟩ := p2
      obtain ⟨hb2, hm2⟩ := iha.1 memo1 memo2 b2 hm1 h2'
      rw [habs]
      simp only [ConLeche.Expr.mentionsConst]
      split at h <;> rename_i hc <;>
        obtain ⟨hr, hmm⟩ := pair_ok h <;> rw [← hr, ← hmm, ← hb1, ← hb2]
      · exact ⟨by rw [hc]; simp, hm2⟩
      · simp only [Bool.not_eq_true] at hc
        exact ⟨by rw [hc]; simp, hm2⟩
    refine ⟨?_, hnode⟩
    intro memo memo' r hm h
    rw [inductives.struct_parts.mentions_const_go.eq_def, hde] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
    rw [← hde] at hprobe h
    exact mentions_probe_step hewf hnode hm h hprobe
  | @lam ty bo m e hty hbo hm0 h1 iht ihb =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.lam_inv h1
    have hewf : ExprWF e := ExprWF.lam hty hbo hm0 h1
    have habs : absExpr e = .lam (absExpr ty) (absExpr bo) (absBinderMeta m) := by
      rw [hde]; simp
    have hnode : NodeOK t e := by
      intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, h1', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, memo1⟩ := p1
      obtain ⟨hb1, hm1⟩ := iht.1 memo memo1 b1 hm h1'
      obtain ⟨p2, h2', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b2, memo2⟩ := p2
      obtain ⟨hb2, hm2⟩ := ihb.1 memo1 memo2 b2 hm1 h2'
      rw [habs]
      simp only [ConLeche.Expr.mentionsConst]
      split at h <;> rename_i hc <;>
        obtain ⟨hr, hmm⟩ := pair_ok h <;> rw [← hr, ← hmm, ← hb1, ← hb2]
      · exact ⟨by rw [hc]; simp, hm2⟩
      · simp only [Bool.not_eq_true] at hc
        exact ⟨by rw [hc]; simp, hm2⟩
    refine ⟨?_, hnode⟩
    intro memo memo' r hm h
    rw [inductives.struct_parts.mentions_const_go.eq_def, hde] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
    rw [← hde] at hprobe h
    exact mentions_probe_step hewf hnode hm h hprobe
  | @forall_e ty bo m e hty hbo hm0 h1 iht ihb =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.forall_e_inv h1
    have hewf : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    have habs : absExpr e = .forallE (absExpr ty) (absExpr bo) (absBinderMeta m) := by
      rw [hde]; simp
    have hnode : NodeOK t e := by
      intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, h1', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, memo1⟩ := p1
      obtain ⟨hb1, hm1⟩ := iht.1 memo memo1 b1 hm h1'
      obtain ⟨p2, h2', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b2, memo2⟩ := p2
      obtain ⟨hb2, hm2⟩ := ihb.1 memo1 memo2 b2 hm1 h2'
      rw [habs]
      simp only [ConLeche.Expr.mentionsConst]
      split at h <;> rename_i hc <;>
        obtain ⟨hr, hmm⟩ := pair_ok h <;> rw [← hr, ← hmm, ← hb1, ← hb2]
      · exact ⟨by rw [hc]; simp, hm2⟩
      · simp only [Bool.not_eq_true] at hc
        exact ⟨by rw [hc]; simp, hm2⟩
    refine ⟨?_, hnode⟩
    intro memo memo' r hm h
    rw [inductives.struct_parts.mentions_const_go.eq_def, hde] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
    rw [← hde] at hprobe h
    exact mentions_probe_step hewf hnode hm h hprobe
  | @let_e ty w bo e hty hw hbo h1 iht ihv ihb =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.let_e_inv h1
    have hewf : ExprWF e := ExprWF.let_e hty hw hbo h1
    have habs : absExpr e = .letE (absExpr ty) (absExpr w) (absExpr bo) := by
      rw [hde]; simp
    have hnode : NodeOK t e := by
      intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, h1', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, memo1⟩ := p1
      obtain ⟨hb1, hm1⟩ := iht.1 memo memo1 b1 hm h1'
      obtain ⟨p2, h2', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b2, memo2⟩ := p2
      obtain ⟨hb2, hm2⟩ := ihv.1 memo1 memo2 b2 hm1 h2'
      obtain ⟨p3, h3', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b3, memo3⟩ := p3
      obtain ⟨hb3, hm3⟩ := ihb.1 memo2 memo3 b3 hm2 h3'
      rw [habs]
      simp only [ConLeche.Expr.mentionsConst]
      split at h
      · rename_i hc
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, ← hb1, ← hb2, ← hb3, hc]
        exact ⟨by simp, hm3⟩
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        split at h
        · rename_i hc2
          obtain ⟨hr, hmm⟩ := pair_ok h
          rw [← hr, ← hmm, ← hb1, ← hb2, ← hb3, hc, hc2]
          exact ⟨by simp, hm3⟩
        · rename_i hc2
          simp only [Bool.not_eq_true] at hc2
          obtain ⟨hr, hmm⟩ := pair_ok h
          rw [← hr, ← hmm, ← hb1, ← hb2, ← hb3, hc, hc2]
          exact ⟨by simp, hm3⟩
    refine ⟨?_, hnode⟩
    intro memo memo' r hm h
    rw [inductives.struct_parts.mentions_const_go.eq_def, hde] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
    rw [← hde] at hprobe h
    exact mentions_probe_step hewf hnode hm h hprobe
  | @proj s j x e hs hx h1 ih =>
    obtain ⟨d, hde, -, -, -⟩ := Expr.proj_inv h1
    have hewf : ExprWF e := ExprWF.proj hs hx h1
    have habs : absExpr e = .proj (absName s) j.val (absExpr x) := by rw [hde]; simp
    have hnode : NodeOK t e := by
      intro memo memo' r hm h
      rw [inductives.struct_parts.mentions_const_node.eq_def, hde] at h
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, h1', h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, memo1⟩ := p1
      obtain ⟨hb1, hm1⟩ := ih.1 memo memo1 b1 hm h1'
      obtain ⟨bs, hbs, h⟩ := bind_eq_ok_iff.mp h
      have hbsv := Name.name_beq_exact' hs ht hbs
      rw [habs]
      simp only [ConLeche.Expr.mentionsConst]
      split at h
      · rename_i hc
        rw [hbsv, decide_eq_true_eq] at hc
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm]
        exact ⟨by simp [hc], hm1⟩
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        rw [hbsv, decide_eq_false_iff_not] at hc
        obtain ⟨hr, hmm⟩ := pair_ok h
        rw [← hr, ← hmm, ← hb1]
        exact ⟨by simp [hc], hm1⟩
    refine ⟨?_, hnode⟩
    intro memo memo' r hm h
    rw [inductives.struct_parts.mentions_const_go.eq_def, hde] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
    rw [← hde] at hprobe h
    exact mentions_probe_step hewf hnode hm h hprobe

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
        ∧ ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo' :=
  (mentions_const_walk ht he).1

/-- `ConLeche/Kernel/Inductives/StructParts.lean:814-849` —
`mentions_const_node` refines the inner `match e with` of the miss branch,
split off in the port so the probe's borrow dies before the descent mutates the
memo (task #14's rule).  The final `| e => (e.mentionsConst T, memo)` arm is
the cited unreachable one — the four leaf kinds answered above, and it is
`mentions_const_spec` in the port, which is why the leaf arms of the proof go
through `mentions_const_spec_refines`.

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
      ∧ ExprOps.MemoInv ExprWF absExpr (MentionsQ (absName t)) memo' :=
  (mentions_const_walk ht he).2 memo memo' r hm h

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
