/-
# `kernel::inductives::native_parts` refined (task #57)

`CORE_PLAN.md` step 7.  The **direct recursive class**
(`crates/con-ron-core/src/kernel/inductives/native_parts.rs`, 69 functions)
against `ConLeche/Kernel/Inductives/NativeParts.lean`: the positivity
classification, the block recogniser, and — the file's heart — the
**generated recursor with its inductive-hypothesis binders**.

| group | items |
|---|---|
| the field kinds | `rec_field_kind_dup`, `rec_field_kind_beq`, `kind_get_d`, `kinds_copy(_from)`, `kindss_copy(_from)` |
| positivity | `rec_fam_ok`, `args_free_of_from`, `rec_positivity`, `rec_field_kind`, `binder_dom_get_d`, `rec_ctor_kinds_at`, `kinds_all_negative`, `rec_ctor_kinds` |
| the field telescopes | `pi_binders(_go)`, `struct_field_tele_of`, `struct_field_idx_of`, `rec_idx_of(_from)` |
| the record | `native_parts_dup`, `complete`, `with_kinds` |
| the generated recursor | `struct_rec_prefix_at`/`_minors`, `struct_idx_at(_all)`, `struct_tele_at(_from)`, `struct_tele_vars`, `mk_pis_of(_from)`, `mk_lams_of(_from)`, `struct_ih_app(s)`, `struct_rule_body_r`, `struct_ih_pis`, `struct_minor_ty_r`, `struct_ctor_spine_at_o`, `lift_all`, `struct_minors_pis_r`, `struct_minors_lams_r`, `struct_rec_ty_r`, `struct_rec_rhs_r`, `u64s_copy(_from)`, `native_ctors4(_from)` |
| the stream's rules against the generated ones | `native_rule_prefix_head`, `native_rule_prefix_fields`, `native_rule_prefix_ok`, `native_rule_ok`, `native_rules_ok(_from)` |
| recognition | `native_counts`, `native_rec_pin_rules`, `native_rec_pin_ok`, `native_rec_lps_ok`, `native_ctors_ok_from`, `native_shape_names_ok`, `native_ctors_of(_from)`, `native_rhss_of(_from)`, `native_shape_large`, `native_shape`, `native_parts` |

## Why every statement here is *structural*

`checkNativeRec` generates the recursor's type and compares it with the
stream's by one closed `isDefEq`, and `nativeRulesOk` compares the stream's
rule bodies with the generated ones by **structural equality**.  So a
generator that differs from con-leche's by one `liftLooseBVars` amount, one
cutoff, one binder datum or one append position is not merely a term the proof
has to relate — it is a different *verdict*.  Each lemma below is therefore
the exact equation `absExpr (rust_gen …) = lean_gen …`, plus `ExprWF` of the
generated term (which is what the `isDefEq` and `resetMeta` sites need).

## The three deviations the statements absorb (task #25)

* **`NativeParts extends InductiveShape` is the port's field `shape`**
  (deviation 3).  `IndAbs.absNativeParts` is where the two spellings meet, and
  every statement about the record goes through it.
* **The two higher-order arguments are monomorphised** (§3.4, task #18's
  pattern 1).  `structIhApp`, `structRuleBodyR`, `structIhPis`,
  `structMinorTyR` and `structRecRhsR` take
  `teleOf : Nat → List (Expr × BinderMeta)` and `idxOf : Nat → List Expr`;
  *every* con-leche call site passes `structFieldTeleOf cty nP nF` and
  `structFieldIdxOf cty nP nF`, so the port passes `cty`/`nP`/`nF` and calls
  the two readers by name.  Every statement below instantiates the two
  arguments at exactly those partial applications — nothing is generalised and
  nothing is weakened.
* **Lean's truncated `Nat` subtraction is `expr_ops::sub_nat`** at every
  `nF - 1 - i`, read through `(a - b) - c = a - (b + c)`
  (`ExprOps.sub_nat_val_trunc`).

## Sibling facts travel as named ingredients

Only `Refine.IndAbs` and `Refine.IndSumParts` of the `Ind*` family are
imported.  `struct_parts`' twelve generators and readers are this file's
*ingredients* but `Refine/IndStructParts.lean`'s *property*: they are bundled
in `StructGens` below, each field the exact refinement statement that file
owns.  Nothing is weakened this way — every conclusion here is the exact one,
under an explicit hypothesis.

`absU64s`, `absCtors4`, `Ctors4WF` and `nativeRuleOkAt` are this file's own and
are **to be unified into `Refine/Abs.lean`** with the rest of the routes'
abstractions when the tier is merged.

## A platform side condition, not a weakening

`kind_get_d` and `binder_dom_get_d` index a `Vec` with `(i as usize)` on a
`u64` counter, and Aeneas keeps `usize`'s width abstract
(`System.Platform.numBits_eq`), so the two lemmas carry
`i.val ≤ Std.Usize.max` — the same side condition
`IndStructParts.sort_get_d_refines` carries, vacuous on the 64-bit targets the
port builds for.

## `sorry`s

**38 of the 69 lemmas are proved**, including every copy (as an identity),
every list/telescope builder (`lift_all`, `struct_idx_at(_all)`,
`struct_tele_at(_from)`, `struct_tele_vars`, `mk_pis_of(_from)`,
`mk_lams_of(_from)`, `struct_rec_prefix_at`/`_minors`), the positions
(`rec_idx_of(_from)`), the two `getD` readers, `args_free_of_from`,
`rec_field_kind`, the whole record group, `native_rules_ok`,
`native_ctors_of(_from)` and `native_rhss_of(_from)`.

**31 `sorry`s**, each a `partial_fixpoint` index recursion, a structural walk
down a term, or a composition of several of those.  Every statement is the
exact one; only the proof is missing.

| what is missing | lemmas |
|---|---|
| the positivity walk | `rec_fam_ok`, `rec_positivity`, `rec_ctor_kinds_at`, `rec_ctor_kinds` |
| the `∀`-telescope readers | `pi_binders_go`, `struct_field_tele_of`, `struct_field_idx_of` |
| the recursor's own generators | `struct_ih_app`, `struct_ih_apps`, `struct_rule_body_r`, `struct_ih_pis`, `struct_minor_ty_r`, `struct_minors_pis_r`, `struct_minors_lams_r`, `struct_rec_ty_r`, `struct_rec_rhs_r`, `native_ctors4_from` |
| the stream's rules | `native_rule_prefix_head`, `native_rule_prefix_fields`, `native_rule_prefix_ok`, `native_rule_ok`, `native_rules_ok_from` |
| recognition | `native_counts`, `native_rec_pin_rules`, `native_rec_pin_ok`, `native_rec_lps_ok`, `native_ctors_ok_from`, `native_shape_names_ok`, `native_shape_large`, `native_shape`, `native_parts` |
-/
import ConRon.Refine.IndAbs
import ConRon.Refine.IndSumParts
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.CoreKVec
import ConRon.Refine.BasisNames

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv
open ConRon.Refine.IndAbs (absRecFieldKind absRecFieldKinds absKindss absCtors
  absInductiveShape absNativeParts InductiveShapeWF NativePartsWF)

namespace ConRon.Refine.NativeParts

/-! ## This file's own abstractions (**to be unified into `Refine/Abs.lean`**) -/

/-- A `Vec<u64>` as con-leche's `List Nat` (`recIdxOf`'s result, the
generators' `recIdx` argument). -/
def absU64s (xs : alloc.vec.Vec Std.U64) : List Nat := xs.val.map (·.val)

/-- `nativeCtors4`'s result: the four-component constructor records the
generators take, `Vec<(Name, u64, Expr, Vec<u64>)>` as
`List (Name × Nat × Expr × List Nat)`. -/
def absCtors4
    (cs : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))) :
    List (ConLeche.Name × Nat × ConLeche.Expr × List Nat) :=
  cs.val.map (fun c => (absName c.1, c.2.1.val, absExpr c.2.2.1, absU64s c.2.2.2))

/-- Every stored name and constructor type of a `nativeCtors4` list is WF. -/
def Ctors4WF
    (cs : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))) :
    Prop :=
  ∀ c ∈ cs.val, NameWF c.1 ∧ ExprWF c.2.2.1

/-- The body of `nativeRulesOk`'s `(List.range n).all`
(`ConLeche/Kernel/Inductives/NativeParts.lean:465-475`), named so that the
port's `native_rule_ok` — which is exactly that body pulled out into a
function — has something exact to be stated against.  `nativeRulesOk_eq` is
the `rfl` that pins it to the cited definition. -/
def nativeRuleOkAt (recC : ConLeche.Name) (rlvls : List ConLeche.Level)
    (pw : ConLeche.PropWhen) (nP n : Nat) (rhs : ConLeche.Expr)
    (cA : ConLeche.ConstantVal) (nF : Nat) (ks : List ConLeche.RecFieldKind)
    (recTy : ConLeche.Expr) (j : Nat) : Bool :=
  ks.length == nF &&
  (match rhs.stripLams (nP + 1 + n + nF) with
   | some (_, rbody) =>
     rbody == ConLeche.Expr.resetMeta
       (ConLeche.structRuleBodyR recC rlvls pw nP n nF j (ConLeche.recIdxOf ks)
         (ConLeche.structFieldTeleOf cA.type nP nF)
         (ConLeche.structFieldIdxOf cA.type nP nF))
   | none => false) &&
  ConLeche.nativeRulePrefixOk recTy nP n j nF rhs

/-- `nativeRuleOkAt` *is* the cited `all`'s body. -/
theorem nativeRulesOk_eq (recC : ConLeche.Name) (rlvls : List ConLeche.Level)
    (pw : ConLeche.PropWhen) (nP n : Nat)
    (cs : List (ConLeche.ConstantVal × Nat))
    (kinds : List (List ConLeche.RecFieldKind))
    (rhss : List ConLeche.Expr) (recTy : ConLeche.Expr) :
    ConLeche.nativeRulesOk recC rlvls pw nP n cs kinds rhss recTy
      = (rhss.length == n && kinds.length == n &&
          (List.range n).all fun j =>
            match rhss[j]?, cs[j]?, kinds[j]? with
            | some rhs, some (cA, nF), some ks =>
              nativeRuleOkAt recC rlvls pw nP n rhs cA nF ks recTy j
            | _, _, _ => false) := rfl

/-! ## The ingredients this file does not own

`kernel::inductives::struct_parts`' generators and readers, which every
generator below calls.  **Owned by `Refine/IndStructParts.lean`**; bundled
here so that each statement keeps its exact conclusion under one explicit
hypothesis. -/

/-- The twelve `struct_parts` facts this file reads.  Each field is the exact
refinement statement of `Refine/IndStructParts.lean` — nothing here is weaker
than what that file proves. -/
structure StructGens : Prop where
  /-- `params_of lps` is `lps.map .param` (`StructParts.lean:48-61`). -/
  params_of : ∀ (lps : alloc.vec.Vec name.Name) (us : alloc.vec.Vec level.Level),
    NamesWF lps → inductives.struct_parts.params_of lps = ok us →
    absLevels us = (absNames lps).map ConLeche.Level.param ∧ LevelsWF us
  /-- `level_is_prop` is `Level.isEquiv s .zero == some true`
  (`StructParts.lean:75-85`). -/
  level_is_prop : ∀ (s : level.Level) (b : Bool), LevelWF s →
    inductives.struct_parts.level_is_prop s = ok b →
    b = (ConLeche.Level.isEquiv (absLevel s) .zero == some true)
  /-- `struct_ps_at` refines `structPsAt` (`StructParts.lean:135-137`). -/
  struct_ps_at : ∀ (o n_p : Std.U64) (r : alloc.vec.Vec expr.Expr),
    inductives.struct_parts.struct_ps_at o n_p = ok r →
    absExprs r = ConLeche.structPsAt o.val n_p.val ∧ ExprsWF r
  /-- `field_spine` is the field-variable spine that `structCtorSpineAt` and
  `structTeleVars` both spell (`StructParts.lean:117-131`). -/
  field_spine : ∀ (m : Std.U64) (r : alloc.vec.Vec expr.Expr),
    inductives.struct_parts.field_spine m = ok r →
    absExprs r = (List.range m.val).map (fun j => ConLeche.Expr.bvar (m.val - 1 - j))
      ∧ ExprsWF r
  /-- `struct_ctor_spine_at` refines `structCtorSpineAt`
  (`StructParts.lean:144-150`). -/
  struct_ctor_spine_at : ∀ (c : name.Name) (lps : alloc.vec.Vec name.Name)
    (o n_p n_f : Std.U64) (r : expr.Expr), NameWF c → NamesWF lps →
    inductives.struct_parts.struct_ctor_spine_at c lps o n_p n_f = ok r →
    absExpr r
        = ConLeche.structCtorSpineAt (absName c) (absNames lps) o.val n_p.val n_f.val
      ∧ ExprWF r
  /-- `struct_elim_level` refines `structElimLevel`
  (`StructParts.lean:139-142`). -/
  struct_elim_level : ∀ (elim : name.Name) (large : Bool) (r : level.Level),
    NameWF elim → inductives.struct_parts.struct_elim_level elim large = ok r →
    absLevel r = ConLeche.structElimLevel (absName elim) large ∧ LevelWF r
  /-- `replace_pis_pw` refines `Expr.replacePisPw`
  (`StructParts.lean:152-159`). -/
  replace_pis_pw : ∀ (pw : prop_when.PropWhen) (k : Std.U64) (e b : expr.Expr)
    (o : Option expr.Expr), PropWhenWF pw → ExprWF e → ExprWF b →
    inductives.struct_parts.replace_pis_pw pw k e b = ok o →
    o.map absExpr
        = ConLeche.Expr.replacePisPw (absPropWhen pw) k.val (absExpr e) (absExpr b)
      ∧ ∀ r, o = some r → ExprWF r
  /-- `pis_to_lams_pw` refines `Expr.pisToLamsPw`
  (`StructParts.lean:161-168`). -/
  pis_to_lams_pw : ∀ (pw : prop_when.PropWhen) (k : Std.U64) (e b : expr.Expr)
    (o : Option expr.Expr), PropWhenWF pw → ExprWF e → ExprWF b →
    inductives.struct_parts.pis_to_lams_pw pw k e b = ok o →
    o.map absExpr
        = ConLeche.Expr.pisToLamsPw (absPropWhen pw) k.val (absExpr e) (absExpr b)
      ∧ ∀ r, o = some r → ExprWF r
  /-- `struct_fam_i` refines `structFamI` (`StructParts.lean:190-194`). -/
  struct_fam_i : ∀ (t : name.Name) (lps : alloc.vec.Vec name.Name)
    (n_p n_idx e o : Std.U64) (r : expr.Expr), NameWF t → NamesWF lps →
    inductives.struct_parts.struct_fam_i t lps n_p n_idx e o = ok r →
    absExpr r
        = ConLeche.structFamI (absName t) (absNames lps) n_p.val n_idx.val e.val o.val
      ∧ ExprWF r
  /-- `struct_motive_ty_i` refines `structMotiveTyI`
  (`StructParts.lean:203-211`). -/
  struct_motive_ty_i : ∀ (t : name.Name) (lps : alloc.vec.Vec name.Name)
    (n_p n_idx : Std.U64) (l : level.Level) (itele : expr.Expr)
    (o : Option expr.Expr), NameWF t → NamesWF lps → LevelWF l → ExprWF itele →
    inductives.struct_parts.struct_motive_ty_i t lps n_p n_idx l itele = ok o →
    o.map absExpr = ConLeche.structMotiveTyI (absName t) (absNames lps) n_p.val
        n_idx.val (absLevel l) (absExpr itele)
      ∧ ∀ r, o = some r → ExprWF r
  /-- `mentions_const` refines `Expr.mentionsConst` through con-leche's own
  `mentionsConst_eq_fast` (`StructParts.lean:775-813`, `:923`). -/
  mentions_const : ∀ (t : name.Name) (e : expr.Expr) (b : Bool),
    NameWF t → ExprWF e → inductives.struct_parts.mentions_const t e = ok b →
    b = (absExpr e).mentionsConst (absName t)
  /-- `struct_used_later` refines `structUsedLater`
  (`StructParts.lean:632-668`). -/
  struct_used_later : ∀ (cty : expr.Expr) (n_p j : Std.U64) (b : Bool),
    ExprWF cty → inductives.struct_parts.struct_used_later cty n_p j = ok b →
    b = ConLeche.structUsedLater (absExpr cty) n_p.val j.val

section Gens

-- (the `StructGens` ingredient is taken explicitly by the lemmas that need it)

/-! ## The field kinds (`NativeParts.lean:60-76`) -/

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:60-76` — `rec_field_kind_dup`
is Lean's value semantics on a tag: the kind is unchanged. -/
theorem rec_field_kind_dup_refines {k k' : inductives.native_parts.RecFieldKind}
    (h : inductives.native_parts.rec_field_kind_dup k = ok k') : k' = k := by
  cases k <;>
    (rw [inductives.native_parts.rec_field_kind_dup] at h;
     exact (Result.ok_injective h).symm)

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:60-76` — `rec_field_kind_beq`
is the cited `deriving DecidableEq`, exactly. -/
theorem rec_field_kind_beq_refines {a b : inductives.native_parts.RecFieldKind}
    {c : Bool} (h : inductives.native_parts.rec_field_kind_beq a b = ok c) :
    c = decide (absRecFieldKind a = absRecFieldKind b) := by
  cases a <;> cases b <;>
    (rw [inductives.native_parts.rec_field_kind_beq] at h;
     rw [← Result.ok_injective h]; decide)

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:171-175` — `kind_get_d` is
the cited `ks.getD i .ordinary`, the derived `Inhabited` default every read
spells.

`i.val ≤ Std.Usize.max` is a **platform** side condition, not a weakening: the
port writes `(i as usize) < ks.len()` and Aeneas keeps `usize`'s width abstract
(`System.Platform.numBits_eq`), so the model has to say that the cast does not
wrap; on the 64-bit targets the port builds for it is vacuous. -/
theorem kind_get_d_refines {ks : alloc.vec.Vec inductives.native_parts.RecFieldKind}
    {i : Std.U64} {r : inductives.native_parts.RecFieldKind}
    (hi : i.val ≤ Std.Usize.max)
    (h : inductives.native_parts.kind_get_d ks i = ok r) :
    absRecFieldKind r = (absRecFieldKinds ks).getD i.val .ordinary := by
  rw [inductives.native_parts.kind_get_d] at h
  simp only [lift_eq, bind_tc_ok] at h
  have hcv : (Std.UScalar.cast .Usize i).val = i.val := ExprOps.u64_cast_usize_val hi
  split at h
  · rename_i hlt
    have hltv : i.val < ks.val.length := by
      have := alloc.vec.Vec.len_val ks; scalar_tac
    obtain ⟨k0, hidx, hdup⟩ := bind_eq_ok_iff.mp h
    have hg := ExprOps.vec_index_getElem? hidx
    rw [hcv, List.getElem?_eq_getElem hltv] at hg
    have hkv : ks.val[i.val] = k0 := Option.some_injective _ hg
    rw [rec_field_kind_dup_refines hdup, ← hkv, IndAbs.absRecFieldKinds,
      List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hltv]
    simp
  · rename_i hge
    have hgev : ks.val.length ≤ i.val := by
      have := alloc.vec.Vec.len_val ks; scalar_tac
    rw [← Result.ok_injective h, IndAbs.absRecFieldKinds,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hgev)]
    rfl

/-- `kinds_copy_from` appends the rest of the kind list to its accumulator;
stated as the **identity** on the `Vec`, the strongest form a copy can have
and the form `Refine/Env.lean` gives every other copy in the port. -/
theorem kinds_copy_from_val
    (ks : alloc.vec.Vec inductives.native_parts.RecFieldKind) :
    ∀ k : Nat,
      ∀ (i : Std.Usize) (out v : alloc.vec.Vec inductives.native_parts.RecFieldKind),
      ks.length - i.val ≤ k →
      inductives.native_parts.kinds_copy_from ks i out = ok v →
      v.val = out.val ++ ks.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [inductives.native_parts.kinds_copy_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [inductives.native_parts.kinds_copy_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ ks.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ks by scalar_tac)] at h
      have hlt : i.val < ks.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ks.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ks i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, hw, bind_tc_ok] at h
      obtain ⟨rfk, hrfk, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      rw [rec_field_kind_dup_refines hrfk] at hout1
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `kinds_copy_from` at its own statement. -/
theorem kinds_copy_from_refines
    {ks out v : alloc.vec.Vec inductives.native_parts.RecFieldKind} {i : Std.Usize}
    (h : inductives.native_parts.kinds_copy_from ks i out = ok v) :
    v.val = out.val ++ ks.val.drop i.val :=
  kinds_copy_from_val ks ks.length i out v (by scalar_tac) h

/-- `kinds_copy` is the identity. -/
theorem kinds_copy_refines
    {ks v : alloc.vec.Vec inductives.native_parts.RecFieldKind}
    (h : inductives.native_parts.kinds_copy ks = ok v) : v = ks := by
  rw [inductives.native_parts.kinds_copy] at h
  exact alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.new] using kinds_copy_from_refines h)

/-- `kindss_copy_from` appends the rest of the per-constructor kind lists to
its accumulator, as an identity. -/
theorem kindss_copy_from_val
    (kss : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)) :
    ∀ k : Nat, ∀ (i : Std.Usize)
      (out v : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)),
      kss.length - i.val ≤ k →
      inductives.native_parts.kindss_copy_from kss i out = ok v →
      v.val = out.val ++ kss.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [inductives.native_parts.kindss_copy_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len kss by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [inductives.native_parts.kindss_copy_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ kss.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len kss by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len kss by scalar_tac)] at h
      have hlt : i.val < kss.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := kss.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec kss i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, hw, bind_tc_ok] at h
      obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      rw [kinds_copy_refines hv1] at hout1
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `kindss_copy_from` at its own statement. -/
theorem kindss_copy_from_refines
    {kss out v : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {i : Std.Usize}
    (h : inductives.native_parts.kindss_copy_from kss i out = ok v) :
    v.val = out.val ++ kss.val.drop i.val :=
  kindss_copy_from_val kss kss.length i out v (by scalar_tac) h

/-- `kindss_copy` is the identity. -/
theorem kindss_copy_refines
    {kss v : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    (h : inductives.native_parts.kindss_copy kss = ok v) : v = kss := by
  rw [inductives.native_parts.kindss_copy] at h
  exact alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.new] using kindss_copy_from_refines h)

/-! ## Positivity (`NativeParts.lean:78-145`) -/

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:78-87` and `:118-145` —
`args_free_of_from` is the two cited
`(args.drop k).all fun a => !a.mentionsConst T` conjuncts (`recFamOk`'s index
arguments and `recCtorKinds`' residual), as one index recursion. -/
theorem args_free_of_from_refines (hg : StructGens) {t : name.Name} {args : alloc.vec.Vec expr.Expr}
    {i : Std.Usize} {b : Bool} (ht : NameWF t) (hargs : ExprsWF args)
    (h : inductives.native_parts.args_free_of_from t args i = ok b) :
    b = ((absExprs args).drop i.val).all (fun a => !a.mentionsConst (absName t)) := by
  generalize hd : args.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.native_parts.args_free_of_from] at h
    split at h
    · rename_i hge
      have hnil : (absExprs args).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absExprs, List.length_map]; scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hltv : i.val < args.val.length := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec args i hltv)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
      have hew : ExprWF args.val[i.val] := hargs _ (List.getElem_mem hltv)
      have hb0v : b0 = (absExpr args.val[i.val]).mentionsConst (absName t) :=
        hg.mentions_const t _ b0 ht hew hb0
      have hlt2 : i.val < (absExprs args).length := by simpa [absExprs] using hltv
      have hcons : (absExprs args).drop i.val
          = absExpr args.val[i.val] :: (absExprs args).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absExprs]
      rw [hcons, List.all_cons, ← hb0v]
      cases b0
      · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false] at h ⊢
        obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
        have hwv : w.val = i.val + 1 := HashMap.uscalar_add_eq hw
        have hrec := ih (args.length - w.val) (by scalar_tac) h rfl
        rw [hwv] at hrec
        exact hrec
      · simp only [Bool.not_true, Bool.false_and, if_true] at h ⊢
        exact (Result.ok_injective h).symm

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:78-87` — `rec_fam_ok` refines
`recFamOk`: official's `is_valid_ind_app` exactly, the `&&` cascade spelled as
an `if` nest. -/
theorem rec_fam_ok_refines (hg : StructGens) {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_idx o : Std.U64} {e : expr.Expr} {b : Bool}
    (ht : NameWF t) (hlps : NamesWF lps) (he : ExprWF e)
    (h : inductives.native_parts.rec_fam_ok t lps n_p n_idx o e = ok b) :
    b = ConLeche.recFamOk (absName t) (absNames lps) n_p.val n_idx.val o.val
      (absExpr e) := by
  -- `get_app_fn`, `params_of`, `get_app_args`, `take_exprs`, `struct_ps_at`,
  -- then `args_free_of_from`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:89-111` — `rec_positivity`
refines `recPositivity`: official `check_positivity`'s telescope walk on a
field domain that mentions the block, `k` binders of the field's own telescope
peeled. -/
theorem rec_positivity_refines (hg : StructGens) {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_idx o : Std.U64} {e : expr.Expr} {k : Std.U64}
    {r : inductives.native_parts.RecFieldKind}
    (ht : NameWF t) (hlps : NamesWF lps) (he : ExprWF e)
    (h : inductives.native_parts.rec_positivity t lps n_p n_idx o e k = ok r) :
    absRecFieldKind r
      = ConLeche.recPositivity (absName t) (absNames lps) n_p.val n_idx.val o.val
          (absExpr e) k.val := by
  -- the structural recursion down the field's own `∀`-telescope
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:113-116` — `rec_field_kind`
refines `recFieldKind`: the kind of a field whose domain is `dom`, `o` fields
into the constructor's telescope. -/
theorem rec_field_kind_refines (hg : StructGens) {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_idx o : Std.U64} {dom : expr.Expr}
    {r : inductives.native_parts.RecFieldKind}
    (ht : NameWF t) (hlps : NamesWF lps) (hdom : ExprWF dom)
    (h : inductives.native_parts.rec_field_kind t lps n_p n_idx o dom = ok r) :
    absRecFieldKind r
      = ConLeche.recFieldKind (absName t) (absNames lps) n_p.val n_idx.val o.val
          (absExpr dom) := by
  rw [inductives.native_parts.rec_field_kind] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  rw [ConLeche.recFieldKind, ← hg.mentions_const t dom b ht hdom hb]
  cases b
  · simp only [Bool.false_eq_true, if_false] at h ⊢
    rw [← Result.ok_injective h]; rfl
  · simp only [if_true] at h ⊢
    exact rec_positivity_refines hg ht hlps hdom h

/-- `binder_dom_get_d` is the cited `(cbs.getD (nP + i) default).1`: only the
`.1` of Lean's `default : Expr × BinderMeta` is ever read, and that is the
derived `Inhabited Expr` — `env::default_expr`, `.bvar 0` (task #14's
deviation 3).  `i.val ≤ Std.Usize.max` is the same **platform** side condition
as `kind_get_d`'s. -/
theorem binder_dom_get_d_refines
    {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {i : Std.U64}
    {r : expr.Expr} (hbs : ExprOps.BindersWF bs) (hi : i.val ≤ Std.Usize.max)
    (h : inductives.native_parts.binder_dom_get_d bs i = ok r) :
    absExpr r = ((ExprOps.absBinders bs).getD i.val default).1 ∧ ExprWF r := by
  rw [inductives.native_parts.binder_dom_get_d] at h
  simp only [lift_eq, bind_tc_ok] at h
  have hcv : (Std.UScalar.cast .Usize i).val = i.val := ExprOps.u64_cast_usize_val hi
  split at h
  · rename_i hlt
    have hltv : i.val < bs.val.length := by
      have := alloc.vec.Vec.len_val bs; scalar_tac
    rcases hsplit : bs.val[i.val] with ⟨e0, m0⟩
    obtain ⟨p, hidx, hdup⟩ := bind_eq_ok_iff.mp h
    have hg := ExprOps.vec_index_getElem? hidx
    rw [hcv, List.getElem?_eq_getElem hltv, hsplit] at hg
    have hpv : ((e0, m0) : expr.Expr × expr.BinderMeta) = p :=
      Option.some_injective _ hg
    rw [← hpv] at hdup
    have hwf : ExprWF e0 := by
      have := hbs _ (List.getElem_mem hltv); rw [hsplit] at this; exact this.1
    refine ⟨?_, by rw [Expr.dup_eq hdup]; exact hwf⟩
    rw [Expr.dup_eq hdup, ExprOps.absBinders, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem hltv, hsplit]
    simp
  · rename_i hge
    have hgev : bs.val.length ≤ i.val := by
      have := alloc.vec.Vec.len_val bs; scalar_tac
    refine ⟨?_, Env.default_expr_wf h⟩
    rw [Env.default_expr_refines h, ExprOps.absBinders,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hgev)]
    rfl

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:118-145` —
`rec_ctor_kinds_at` is `recCtorKinds`' per-field `(List.range c.2).map`, with
the `structUsedLater` downgrade of a recursive or reflexive field. -/
theorem rec_ctor_kinds_at_refines (hg : StructGens) {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_idx : Std.U64} {cty : expr.Expr}
    {cbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {n_f i : Std.U64}
    {out v : alloc.vec.Vec inductives.native_parts.RecFieldKind}
    (ht : NameWF t) (hlps : NamesWF lps) (hcty : ExprWF cty)
    (hcbs : ExprOps.BindersWF cbs)
    (h : inductives.native_parts.rec_ctor_kinds_at t lps n_p n_idx cty cbs n_f i out
        = ok v) :
    absRecFieldKinds v = absRecFieldKinds out ++
      (List.range' i.val (n_f.val - i.val)).map (fun k =>
        match ConLeche.recFieldKind (absName t) (absNames lps) n_p.val n_idx.val k
            ((ExprOps.absBinders cbs).getD (n_p.val + k) default).1 with
        | .recursive =>
          if ConLeche.structUsedLater (absExpr cty) n_p.val k then .unsupported
          else .recursive
        | .reflexive =>
          if ConLeche.structUsedLater (absExpr cty) n_p.val k then .unsupported
          else .reflexive
        | other => other) := by
  -- the `partial_fixpoint` index recursion on `n_f - i`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:118-145` —
`kinds_all_negative` is the `ks.map fun _ => .negative` arm: a residual whose
index expressions mention the block is official's "invalid return type", so
*every* field is reported negative and the install rejects the block. -/
theorem kinds_all_negative_refines {n : Std.Usize}
    {out v : alloc.vec.Vec inductives.native_parts.RecFieldKind}
    (h : inductives.native_parts.kinds_all_negative n out = ok v) :
    absRecFieldKinds v = absRecFieldKinds out ++ List.replicate n.val .negative := by
  revert n out v
  suffices hgen : ∀ k : Nat, ∀ (n : Std.Usize)
      (out v : alloc.vec.Vec inductives.native_parts.RecFieldKind),
      n.val ≤ k → inductives.native_parts.kinds_all_negative n out = ok v →
      absRecFieldKinds v = absRecFieldKinds out ++ List.replicate n.val .negative by
    intro n out v h; exact hgen n.val n out v (le_refl _) h
  intro k
  induction k with
  | zero =>
    intro n out v hk h
    rw [inductives.native_parts.kinds_all_negative] at h
    rw [if_pos (show n = 0#usize by scalar_tac), Result.ok.injEq] at h
    rw [← h, show n.val = 0 by scalar_tac]; simp
  | succ k ih =>
    intro n out v hk h
    rw [inductives.native_parts.kinds_all_negative] at h
    by_cases hz : n = 0#usize
    · rw [if_pos hz, Result.ok.injEq] at h
      rw [← h, show n.val = 0 by rw [hz]; rfl]; simp
    · rw [if_neg hz] at h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      have hnv : 0 < n.val := by
        rcases Nat.eq_zero_or_pos n.val with hc | hc
        · exact absurd (by scalar_tac : n = 0#usize) hz
        · exact hc
      have hiv : i.val = n.val - 1 := HashMap.uscalar_sub_eq hi
      rw [ih i out1 v (by omega) h, IndAbs.absRecFieldKinds,
        IndAbs.absRecFieldKinds, vec_push_val hout1]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        ]
      congr 1
      rw [hiv, show n.val = (n.val - 1) + 1 by omega, List.replicate_succ]
      simp [absRecFieldKind]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:118-145` — `rec_ctor_kinds`
refines `recCtorKinds`: the kinds of one constructor's fields, off its (raw or
annotated) type. -/
theorem rec_ctor_kinds_refines (hg : StructGens) {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_idx : Std.U64} {c : env.ConstantVal × Std.U64}
    {o : Option (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    (ht : NameWF t) (hlps : NamesWF lps) (hc : ConstantValWF c.1)
    (h : inductives.native_parts.rec_ctor_kinds t lps n_p n_idx c = ok o) :
    o.map absRecFieldKinds
      = ConLeche.recCtorKinds (absName t) (absNames lps) n_p.val n_idx.val
          (absConstantVal c.1, c.2.val) := by
  -- `strip_pis`, `rec_ctor_kinds_at`, then the residual's `args_free_of_from`
  sorry

/-! ## The field telescopes (`NativeParts.lean:147-175`) -/

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:147-154` — `pi_binders_go`
refines `Expr.piBinders` with the binder list accumulated on the way *in*
(task #13's pattern 3: Lean conses on the way out, and both orders give the
same outermost-first list). -/
theorem pi_binders_go_refines {e : expr.Expr}
    {out : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {r : (alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr}
    (he : ExprWF e) (hout : ExprOps.BindersWF out)
    (h : inductives.native_parts.pi_binders_go e out = ok r) :
    ExprOps.absBinders r.1
        = ExprOps.absBinders out ++ (ConLeche.Expr.piBinders (absExpr e)).1
      ∧ absExpr r.2 = (ConLeche.Expr.piBinders (absExpr e)).2
      ∧ ExprOps.BindersWF r.1 ∧ ExprWF r.2 := by
  -- the structural recursion down the `∀`-telescope
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:147-154` — `pi_binders`
refines `Expr.piBinders`: the entry point, where the accumulator is empty. -/
theorem pi_binders_refines {e : expr.Expr}
    {r : (alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr} (he : ExprWF e)
    (h : inductives.native_parts.pi_binders e = ok r) :
    ExprOps.absBinders r.1 = (ConLeche.Expr.piBinders (absExpr e)).1
      ∧ absExpr r.2 = (ConLeche.Expr.piBinders (absExpr e)).2
      ∧ ExprOps.BindersWF r.1 ∧ ExprWF r.2 := by
  rw [inductives.native_parts.pi_binders] at h
  obtain ⟨h1, h2, h3, h4⟩ := pi_binders_go_refines he ExprOps.bindersWF_new h
  exact ⟨by simpa using h1, h2, h3, h4⟩

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:156-161` —
`struct_field_tele_of` refines `structFieldTeleOf`: field `i`'s own telescope
`a⃗ : A⃗`, at the field's frame, off the constructor's type. -/
theorem struct_field_tele_of_refines {cty : expr.Expr} {n_p n_f i : Std.U64}
    {r : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} (hcty : ExprWF cty)
    (h : inductives.native_parts.struct_field_tele_of cty n_p n_f i = ok r) :
    ExprOps.absBinders r
        = ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val i.val
      ∧ ExprOps.BindersWF r := by
  -- `strip_pis`, `binder_dom_get_d`, `pi_binders`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:163-169` —
`struct_field_idx_of` refines `structFieldIdxOf`: the index expressions of
field `i`'s domain `Π a⃗, T p⃗ e⃗`, `[]` when the field is not of that shape. -/
theorem struct_field_idx_of_refines {cty : expr.Expr} {n_p n_f i : Std.U64}
    {r : alloc.vec.Vec expr.Expr} (hcty : ExprWF cty)
    (h : inductives.native_parts.struct_field_idx_of cty n_p n_f i = ok r) :
    absExprs r = ConLeche.structFieldIdxOf (absExpr cty) n_p.val n_f.val i.val
      ∧ ExprsWF r := by
  -- `strip_pis`, `binder_dom_get_d`, `pi_binders`, `get_app_args`, `drop_exprs`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:171-175` — `rec_idx_of_from`
is `recIdxOf`'s `(List.range ks.length).filter` from index `i`, with the port's
accumulator in front. -/
theorem rec_idx_of_from_refines
    {ks : alloc.vec.Vec inductives.native_parts.RecFieldKind} {i : Std.Usize}
    {out v : alloc.vec.Vec Std.U64}
    (h : inductives.native_parts.rec_idx_of_from ks i out = ok v) :
    absU64s v = absU64s out ++
      (List.range' i.val ((absRecFieldKinds ks).length - i.val)).filter
        (fun k => (absRecFieldKinds ks).getD k .ordinary == .recursive
          || (absRecFieldKinds ks).getD k .ordinary == .reflexive) := by
  have hlen : (absRecFieldKinds ks).length = ks.val.length := by
    simp [IndAbs.absRecFieldKinds]
  revert h; revert out v i
  suffices hgen : ∀ d : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec Std.U64),
      ks.length - i.val ≤ d →
      inductives.native_parts.rec_idx_of_from ks i out = ok v →
      absU64s v = absU64s out ++
        (List.range' i.val ((absRecFieldKinds ks).length - i.val)).filter
          (fun k => (absRecFieldKinds ks).getD k .ordinary == .recursive
            || (absRecFieldKinds ks).getD k .ordinary == .reflexive) by
    intro i out v h; exact hgen ks.length i out v (by scalar_tac) h
  intro d
  induction d with
  | zero =>
    intro i out v hk h
    rw [inductives.native_parts.rec_idx_of_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
    rw [← h, hlen, show ks.val.length - i.val = 0 by scalar_tac]; simp
  | succ d ih =>
    intro i out v hk h
    rw [inductives.native_parts.rec_idx_of_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ ks.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
      rw [← h, hlen, show ks.val.length - i.val = 0 by scalar_tac]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ks by scalar_tac)] at h
      have hltv : i.val < ks.val.length := by scalar_tac
      have hcast : (Std.UScalar.cast .U64 i).val = i.val := ExprOps.usize_cast_u64_val i
      simp only [lift_eq, bind_tc_ok] at h
      obtain ⟨k0, hk0, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨keep, hkeep, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      have hi3v : i3.val = i.val + 1 := HashMap.uscalar_add_eq hi3
      have hk0v : absRecFieldKind k0 = (absRecFieldKinds ks).getD i.val .ordinary := by
        have hg0 := kind_get_d_refines (by rw [hcast]; scalar_tac) hk0
        rwa [hcast] at hg0
      have hbv : b = decide (absRecFieldKind k0 = ConLeche.RecFieldKind.recursive) :=
        rec_field_kind_beq_refines hb
      have hkeepv : keep
          = (decide (absRecFieldKind k0 = ConLeche.RecFieldKind.recursive)
            || decide (absRecFieldKind k0 = ConLeche.RecFieldKind.reflexive)) := by
        cases b
        · rw [if_neg (by simp)] at hkeep
          rw [rec_field_kind_beq_refines hkeep, ← hbv, Bool.false_or]
          rfl
        · rw [if_pos rfl, Result.ok.injEq] at hkeep
          rw [← hkeep, ← hbv, Bool.true_or]
      have houtv : absU64s out1
          = if keep then absU64s out ++ [i.val] else absU64s out := by
        cases keep
        · rw [if_neg (by simp)] at hout1
          rw [← Result.ok_injective hout1]; simp
        · rw [if_pos rfl] at hout1
          rw [absU64s, absU64s, vec_push_val hout1, if_pos rfl]
          simp [hcast]
      rw [ih i3 out1 v (by scalar_tac) h, hi3v, houtv, hlen,
        show ks.val.length - i.val = (ks.val.length - (i.val + 1)) + 1 by omega,
        List.range'_succ, List.filter_cons]
      rw [show ((absRecFieldKinds ks).getD i.val ConLeche.RecFieldKind.ordinary
            == ConLeche.RecFieldKind.recursive
          || (absRecFieldKinds ks).getD i.val ConLeche.RecFieldKind.ordinary
            == ConLeche.RecFieldKind.reflexive) = keep by
        rw [hkeepv, ← hk0v]; rfl]
      cases keep <;> simp

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:171-175` — `rec_idx_of`
refines `recIdxOf`: the positions of the recursive fields (finitary or
reflexive: the ones with an inductive hypothesis). -/
theorem rec_idx_of_refines
    {ks : alloc.vec.Vec inductives.native_parts.RecFieldKind}
    {v : alloc.vec.Vec Std.U64}
    (h : inductives.native_parts.rec_idx_of ks = ok v) :
    absU64s v = ConLeche.recIdxOf (absRecFieldKinds ks) := by
  rw [inductives.native_parts.rec_idx_of] at h
  have hv := rec_idx_of_from_refines h
  simpa [absU64s, alloc.vec.Vec.new, ConLeche.recIdxOf, List.range_eq_range']
    using hv

/-! ## The record (`NativeParts.lean:177-199`, `:616-622`) -/

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:177-192` — `native_parts_dup`
is Lean's value semantics: the record is unchanged. -/
theorem native_parts_dup_refines {p p' : inductives.native_parts.NativeParts}
    (h : inductives.native_parts.native_parts_dup p = ok p') : p' = p := by
  rw [inductives.native_parts.native_parts_dup] at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨kss, hkss, h⟩ := bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h, SumParts.inductive_shape_dup_refines hs,
    kindss_copy_refines hkss]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:194-199` — `complete` refines
`NativeParts.complete`: the sum parts the former's stage returned (its result
sort read through `whnf`) with the recogniser's field kinds and its recursor
verdict. -/
theorem complete_refines {p0 : inductives.native_parts.NativeParts}
    {p1 : inductives.sum_parts.InductiveShape}
    {p' : inductives.native_parts.NativeParts}
    (h : inductives.native_parts.complete p0 p1 = ok p') :
    absNativeParts p' = (absNativeParts p0).complete (absInductiveShape p1) := by
  rw [inductives.native_parts.complete] at h
  obtain ⟨kss, hkss, h⟩ := bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h, kindss_copy_refines hkss]
  rfl

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:616-622` — `with_kinds`
refines `NativeParts.withKinds`: the record completed with the fields' kinds
the install classified on the constructors it stored. -/
theorem with_kinds_refines {p p' : inductives.native_parts.NativeParts}
    {ks : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    (h : inductives.native_parts.with_kinds p ks = ok p') :
    absNativeParts p' = (absNativeParts p).withKinds (absKindss ks) := by
  rw [inductives.native_parts.with_kinds] at h
  rw [← Result.ok_injective h]; rfl

/-! ## The generated recursor with inductive hypotheses
(`NativeParts.lean:230-392`)

Every lemma of this section is one node of the term `checkNativeRec` `isDefEq`s
and `nativeRulesOk` compares *structurally*, so each is the exact equation with
the cited `liftLooseBVars` amounts and cutoffs, the cited binder data
(`Level.zeronessOf ℓ` on every generated binder, `.never` on the motive's own,
which is `structMotiveTyI`'s and so `IndStructParts.lean`'s) and the cited
append order. -/

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:230-235` —
`struct_rec_prefix_minors` is the minor half of `structRecPrefixAt`'s spine,
`(List.range n).map fun l => .bvar (e + nF + n - 1 - l)` from `l` on;
`sub_nat base (1 + l)` is the cited `base - 1 - l` (`(a - b) - c = a - (b + c)`,
Lean's truncated subtraction). -/
theorem struct_rec_prefix_minors_refines {n base l : Std.U64}
    {out v : alloc.vec.Vec expr.Expr} (hout : ExprsWF out)
    (h : inductives.native_parts.struct_rec_prefix_minors n base l out = ok v) :
    absExprs v = absExprs out ++
        (List.range' l.val (n.val - l.val)).map
          (fun k => ConLeche.Expr.bvar (base.val - 1 - k))
      ∧ ExprsWF v := by
  revert h; revert hout; revert out v l
  suffices hgen : ∀ k : Nat, ∀ (l : Std.U64) (out v : alloc.vec.Vec expr.Expr),
      n.val - l.val ≤ k → ExprsWF out →
      inductives.native_parts.struct_rec_prefix_minors n base l out = ok v →
      absExprs v = absExprs out ++
          (List.range' l.val (n.val - l.val)).map
            (fun k => ConLeche.Expr.bvar (base.val - 1 - k))
        ∧ ExprsWF v by
    intro l out v hout h; exact hgen n.val l out v (by scalar_tac) hout h
  intro k
  induction k with
  | zero =>
    intro l out v hk hout h
    rw [inductives.native_parts.struct_rec_prefix_minors] at h
    rw [if_pos (show l ≥ n by scalar_tac), Result.ok.injEq] at h
    rw [← h, show n.val - l.val = 0 by scalar_tac]
    exact ⟨by simp, hout⟩
  | succ k ih =>
    intro l out v hk hout h
    rw [inductives.native_parts.struct_rec_prefix_minors] at h
    by_cases hl : l.val ≥ n.val
    · rw [if_pos (show l ≥ n by scalar_tac), Result.ok.injEq] at h
      rw [← h, show n.val - l.val = 0 by scalar_tac]
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ l ≥ n by scalar_tac)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = 1 + l.val := HashMap.uscalar_add_eq hi
      have hi1v : i1.val = base.val - i.val := ExprOps.sub_nat_val_trunc hi1
      have hi2v : i2.val = l.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨habs, hwf⟩ :=
        ih i2 out1 v (by scalar_tac) (ExprOps.ExprsWF_push hout (Expr.bvar_wf he) hout1) h
      refine ⟨?_, hwf⟩
      rw [habs, hi2v, absExprs, absExprs, vec_push_val hout1,
        show n.val - l.val = (n.val - (l.val + 1)) + 1 by omega, List.range'_succ]
      simp [Expr.bvar_refines he, hi1v, hiv, Nat.sub_sub]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:230-235` —
`struct_rec_prefix_at` refines `structRecPrefixAt`: the recursor's leading
spine `p⃗ motive m⃗` as seen from under the `nF` fields and `e` further
binders. -/
theorem struct_rec_prefix_at_refines (hg : StructGens) {n_p n n_f e : Std.U64}
    {v : alloc.vec.Vec expr.Expr}
    (h : inductives.native_parts.struct_rec_prefix_at n_p n n_f e = ok v) :
    absExprs v = ConLeche.structRecPrefixAt n_p.val n.val n_f.val e.val
      ∧ ExprsWF v := by
  rw [inductives.native_parts.struct_rec_prefix_at] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ps, hps, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
  have hiv : i.val = e.val + n_f.val := HashMap.uscalar_add_eq hi
  have hi1v : i1.val = i.val + n.val := HashMap.uscalar_add_eq hi1
  have hi2v : i2.val = i1.val + 1 := HashMap.uscalar_add_eq hi2
  have hi3v : i3.val = i.val + n.val := HashMap.uscalar_add_eq hi3
  have hi4v : i4.val = i.val + n.val := HashMap.uscalar_add_eq hi4
  obtain ⟨habsps, hwfps⟩ := hg.struct_ps_at i2 n_p ps hps
  have hout1wf : ExprsWF out1 := ExprOps.ExprsWF_push hwfps (Expr.bvar_wf he1) hout1
  obtain ⟨habs, hwf⟩ := struct_rec_prefix_minors_refines hout1wf h
  refine ⟨?_, hwf⟩
  rw [habs, ConLeche.structRecPrefixAt, absExprs, vec_push_val hout1,
    List.map_append, show ps.val.map absExpr = absExprs ps from rfl, habsps]
  simp only [List.map_cons, List.map_nil, Expr.bvar_refines he1]
  rw [hi2v, hi1v, hi3v, hi4v, hiv]
  simp [List.range_eq_range']

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:237-244` — `struct_idx_at`
refines `structIdxAt`: the two lifts in the cited order, at the cited amounts
and cutoffs (`nF - i` is Lean's truncated subtraction, hence `sub_nat`). -/
theorem struct_idx_at_refines {n_f o i l m : Std.U64} {e r : expr.Expr}
    (he : ExprWF e)
    (h : inductives.native_parts.struct_idx_at n_f o i l m e = ok r) :
    absExpr r = ConLeche.structIdxAt n_f.val o.val i.val l.val m.val (absExpr e)
      ∧ ExprWF r := by
  rw [inductives.native_parts.struct_idx_at] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨step1, hs1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = n_f.val - i.val := ExprOps.sub_nat_val_trunc hi1
  have hi2v : i2.val = i1.val + l.val := HashMap.uscalar_add_eq hi2
  have hi3v : i3.val = n_f.val + l.val := HashMap.uscalar_add_eq hi3
  have hi4v : i4.val = i3.val + m.val := HashMap.uscalar_add_eq hi4
  obtain ⟨habs1, hwf1⟩ := ExprOps.lift_loose_bvars_refines he hs1
  obtain ⟨habs2, hwf2⟩ := ExprOps.lift_loose_bvars_refines hwf1 h
  refine ⟨?_, hwf2⟩
  rw [habs2, habs1, ConLeche.structIdxAt, hi2v, hi1v, hi4v, hi3v]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:237-244` —
`struct_idx_at_all` is `idx.map (structIdxAt nF o i l m)` from `j` on, with the
port's accumulator in front. -/
theorem struct_idx_at_all_refines {n_f o i l m : Std.U64}
    {idx out v : alloc.vec.Vec expr.Expr} {j : Std.Usize}
    (hidx : ExprsWF idx) (hout : ExprsWF out)
    (h : inductives.native_parts.struct_idx_at_all n_f o i l m idx j out = ok v) :
    absExprs v = absExprs out ++
        ((absExprs idx).drop j.val).map
          (ConLeche.structIdxAt n_f.val o.val i.val l.val m.val)
      ∧ ExprsWF v := by
  revert h; revert hout; revert out v j
  suffices hgen : ∀ k : Nat, ∀ (j : Std.Usize) (out v : alloc.vec.Vec expr.Expr),
      idx.length - j.val ≤ k → ExprsWF out →
      inductives.native_parts.struct_idx_at_all n_f o i l m idx j out = ok v →
      absExprs v = absExprs out ++
          ((absExprs idx).drop j.val).map
            (ConLeche.structIdxAt n_f.val o.val i.val l.val m.val)
        ∧ ExprsWF v by
    intro out v j hout h; exact hgen idx.length j out v (by scalar_tac) hout h
  intro k
  induction k with
  | zero =>
    intro j out v hk hout h
    rw [inductives.native_parts.struct_idx_at_all.eq_def] at h; simp only [] at h
    rw [if_pos (show j ≥ alloc.vec.Vec.len idx by scalar_tac), Result.ok.injEq] at h
    rw [← h]
    refine ⟨?_, hout⟩
    rw [List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; scalar_tac)]
    simp
  | succ k ih =>
    intro j out v hk hout h
    rw [inductives.native_parts.struct_idx_at_all.eq_def] at h; simp only [] at h
    by_cases hj : j.val ≥ idx.length
    · rw [if_pos (show j ≥ alloc.vec.Vec.len idx by scalar_tac), Result.ok.injEq] at h
      rw [← h]
      refine ⟨?_, hout⟩
      rw [List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; scalar_tac)]
      simp
    · rw [if_neg (show ¬ j ≥ alloc.vec.Vec.len idx by scalar_tac)] at h
      have hltv : j.val < idx.val.length := by scalar_tac
      have hmax : j.val + 1 ≤ Std.Usize.max := by have := idx.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec idx j hltv)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, hw, bind_tc_ok] at h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨habs1, hwf1⟩ :=
        struct_idx_at_refines (ExprOps.ExprsWF_getElem hidx hltv) he1
      obtain ⟨habs, hwf⟩ :=
        ih w out1 v (by scalar_tac) (ExprOps.ExprsWF_push hout hwf1 hout1) h
      refine ⟨?_, hwf⟩
      rw [habs, hwv, ExprOps.absExprs_drop_cons_lt hltv, absExprs, absExprs,
        vec_push_val hout1]
      simp [absExprs, habs1]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:246-252` —
`struct_tele_at_from` is `structTeleAt`'s `(List.range tele.length).map` from
`k` on: binder `k` sits under `k` earlier telescope binders, and every binder's
datum is reset to `pw`. -/
theorem struct_tele_at_from_refines {n_f o i l : Std.U64} {pw : prop_when.PropWhen}
    {tele out v : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {k : Std.Usize}
    (hpw : PropWhenWF pw) (htele : ExprOps.BindersWF tele)
    (hout : ExprOps.BindersWF out)
    (h : inductives.native_parts.struct_tele_at_from n_f o i l pw tele k out
        = ok v) :
    ExprOps.absBinders v = ExprOps.absBinders out ++
        (List.range' k.val ((ExprOps.absBinders tele).length - k.val)).map
          (fun j =>
            (ConLeche.structIdxAt n_f.val o.val i.val l.val j
              ((ExprOps.absBinders tele).getD j default).1, ⟨absPropWhen pw⟩))
      ∧ ExprOps.BindersWF v := by
  have hlen : (ExprOps.absBinders tele).length = tele.val.length := by
    simp [ExprOps.absBinders]
  revert h; revert hout; revert out v k
  suffices hgen : ∀ d : Nat, ∀ (k : Std.Usize)
      (out v : alloc.vec.Vec (expr.Expr × expr.BinderMeta)),
      tele.length - k.val ≤ d → ExprOps.BindersWF out →
      inductives.native_parts.struct_tele_at_from n_f o i l pw tele k out = ok v →
      ExprOps.absBinders v = ExprOps.absBinders out ++
          (List.range' k.val ((ExprOps.absBinders tele).length - k.val)).map
            (fun j =>
              (ConLeche.structIdxAt n_f.val o.val i.val l.val j
                ((ExprOps.absBinders tele).getD j default).1, ⟨absPropWhen pw⟩))
        ∧ ExprOps.BindersWF v by
    intro out v k hout h; exact hgen tele.length k out v (by scalar_tac) hout h
  intro d
  induction d with
  | zero =>
    intro k out v hk hout h
    rw [inductives.native_parts.struct_tele_at_from.eq_def] at h; simp only [] at h
    rw [if_pos (show k ≥ alloc.vec.Vec.len tele by scalar_tac), Result.ok.injEq] at h
    rw [← h, hlen, show tele.val.length - k.val = 0 by scalar_tac]
    exact ⟨by simp, hout⟩
  | succ d ih =>
    intro k out v hk hout h
    rw [inductives.native_parts.struct_tele_at_from.eq_def] at h; simp only [] at h
    by_cases hkge : k.val ≥ tele.length
    · rw [if_pos (show k ≥ alloc.vec.Vec.len tele by scalar_tac), Result.ok.injEq] at h
      rw [← h, hlen, show tele.val.length - k.val = 0 by scalar_tac]
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ k ≥ alloc.vec.Vec.len tele by scalar_tac)] at h
      have hltv : k.val < tele.val.length := by scalar_tac
      simp only [lift_eq, bind_tc_ok] at h
      rcases hsplit : tele.val[k.val] with ⟨e0, m0⟩
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec tele k hltv)
      subst hyv
      rw [alloc.vec.Vec.index_slice_index, hy, hsplit, bind_tc_ok] at h
      obtain ⟨dom, hdom, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨pw1, hpw1, h⟩ := bind_eq_ok_iff.mp h
      rw [PropWhen.dup_eq hpw1, ExprOps.binder_meta_eq, bind_tc_ok] at h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨k2, hk2, h⟩ := bind_eq_ok_iff.mp h
      have hk2v : k2.val = k.val + 1 := HashMap.uscalar_add_eq hk2
      have hew : ExprWF e0 ∧ BinderMetaWF m0 := by
        have := htele _ (List.getElem_mem hltv); rw [hsplit] at this; exact this
      obtain ⟨habsd, hwfd⟩ := struct_idx_at_refines hew.1 hdom
      rw [ExprOps.usize_cast_u64_val] at habsd
      have hout1wf : ExprOps.BindersWF out1 :=
        ExprOps.bindersWF_push hout hwfd hpw hout1
      obtain ⟨habs, hwf⟩ := ih k2 out1 v (by scalar_tac) hout1wf h
      refine ⟨?_, hwf⟩
      rw [habs, hk2v, ExprOps.absBinders_push hout1, hlen,
        show tele.val.length - k.val = (tele.val.length - (k.val + 1)) + 1 by omega,
        List.range'_succ]
      have hgetD : ((ExprOps.absBinders tele).getD k.val default).1 = absExpr e0 := by
        rw [ExprOps.absBinders, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hltv, hsplit]
        simp
      simp only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append,
        hgetD, habsd]
      rfl

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:246-252` — `struct_tele_at`
refines `structTeleAt`: field `i`'s own telescope moved as `structIdxAt` moves
its expressions. -/
theorem struct_tele_at_refines {n_f o i l : Std.U64} {pw : prop_when.PropWhen}
    {tele v : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (hpw : PropWhenWF pw) (htele : ExprOps.BindersWF tele)
    (h : inductives.native_parts.struct_tele_at n_f o i l pw tele = ok v) :
    ExprOps.absBinders v = ConLeche.structTeleAt n_f.val o.val i.val l.val
        (absPropWhen pw) (ExprOps.absBinders tele)
      ∧ ExprOps.BindersWF v := by
  rw [inductives.native_parts.struct_tele_at] at h
  obtain ⟨habs, hwf⟩ := struct_tele_at_from_refines hpw htele ExprOps.bindersWF_new h
  refine ⟨?_, hwf⟩
  rw [habs, ConLeche.structTeleAt]
  simp [List.range_eq_range']

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:254-255` — `struct_tele_vars`
refines `structTeleVars`: the variables of an `m`-binder telescope, innermost
last.  The port spells the recursion once, in `struct_parts::field_spine`. -/
theorem struct_tele_vars_refines (hg : StructGens) {m : Std.U64} {v : alloc.vec.Vec expr.Expr}
    (h : inductives.native_parts.struct_tele_vars m = ok v) :
    absExprs v = ConLeche.structTeleVars m.val ∧ ExprsWF v := by
  rw [inductives.native_parts.struct_tele_vars] at h
  exact hg.field_spine m v h

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:257-260` — `mk_pis_of_from`
refines `Expr.mkPisOf` on the binder list from `i` on (built on the way out, as
cited). -/
theorem mk_pis_of_from_refines
    {tele : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {i : Std.Usize}
    {body r : expr.Expr} (htele : ExprOps.BindersWF tele) (hbody : ExprWF body)
    (h : inductives.native_parts.mk_pis_of_from tele i body = ok r) :
    absExpr r
        = ConLeche.Expr.mkPisOf ((ExprOps.absBinders tele).drop i.val) (absExpr body)
      ∧ ExprWF r := by
  revert h; revert i r
  suffices hgen : ∀ k : Nat, ∀ (i : Std.Usize) (r : expr.Expr),
      tele.length - i.val ≤ k →
      inductives.native_parts.mk_pis_of_from tele i body = ok r →
      absExpr r
          = ConLeche.Expr.mkPisOf ((ExprOps.absBinders tele).drop i.val) (absExpr body)
        ∧ ExprWF r by
    intro i r h; exact hgen tele.length i r (by scalar_tac) h
  intro k
  induction k with
  | zero =>
    intro i r hk h
    rw [inductives.native_parts.mk_pis_of_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len tele by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le
      (by simp only [ExprOps.absBinders, List.length_map]; scalar_tac)]
    exact ⟨rfl, hbody⟩
  | succ k ih =>
    intro i r hk h
    rw [inductives.native_parts.mk_pis_of_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ tele.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len tele by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le
        (by simp only [ExprOps.absBinders, List.length_map]; scalar_tac)]
      exact ⟨rfl, hbody⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len tele by scalar_tac)] at h
      have hltv : i.val < tele.val.length := by scalar_tac
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨habsr, hwfr⟩ := ih i2 rest (by scalar_tac) hrest
      rcases hsplit : tele.val[i.val] with ⟨e0, m0⟩
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec tele i hltv)
      subst hyv
      rw [alloc.vec.Vec.index_slice_index, hy, hsplit, bind_tc_ok] at h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨bm1, hbm1, h⟩ := bind_eq_ok_iff.mp h
      have hew : ExprWF e0 ∧ BinderMetaWF m0 := by
        have := htele _ (List.getElem_mem hltv); rw [hsplit] at this; exact this
      rw [Expr.dup_eq he1] at h
      rw [Expr.binder_meta_dup_eq hbm1] at h
      have hcons : (ExprOps.absBinders tele).drop i.val
          = (absExpr e0, absBinderMeta m0) :: (ExprOps.absBinders tele).drop (i.val + 1) := by
        rw [ExprOps.absBinders, ← List.map_drop, List.drop_eq_getElem_cons hltv,
          List.map_cons, List.map_drop, hsplit]
      refine ⟨?_, Expr.forall_e_wf hew.1 hwfr hew.2 h⟩
      rw [Expr.forall_e_refines h, habsr, hi2v, hcons, ConLeche.Expr.mkPisOf]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:257-260` — `mk_pis_of`
refines `Expr.mkPisOf`: `∀ tele, body` over a binder list (outermost first). -/
theorem mk_pis_of_refines {tele : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {body r : expr.Expr} (htele : ExprOps.BindersWF tele) (hbody : ExprWF body)
    (h : inductives.native_parts.mk_pis_of tele body = ok r) :
    absExpr r = ConLeche.Expr.mkPisOf (ExprOps.absBinders tele) (absExpr body)
      ∧ ExprWF r := by
  rw [inductives.native_parts.mk_pis_of] at h
  obtain ⟨habs, hwf⟩ := mk_pis_of_from_refines htele hbody h
  exact ⟨by simpa using habs, hwf⟩

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:261-263` — `mk_lams_of_from`
refines `Expr.mkLamsOf` on the binder list from `i` on. -/
theorem mk_lams_of_from_refines
    {tele : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {i : Std.Usize}
    {body r : expr.Expr} (htele : ExprOps.BindersWF tele) (hbody : ExprWF body)
    (h : inductives.native_parts.mk_lams_of_from tele i body = ok r) :
    absExpr r
        = ConLeche.Expr.mkLamsOf ((ExprOps.absBinders tele).drop i.val) (absExpr body)
      ∧ ExprWF r := by
  revert h; revert i r
  suffices hgen : ∀ k : Nat, ∀ (i : Std.Usize) (r : expr.Expr),
      tele.length - i.val ≤ k →
      inductives.native_parts.mk_lams_of_from tele i body = ok r →
      absExpr r
          = ConLeche.Expr.mkLamsOf ((ExprOps.absBinders tele).drop i.val) (absExpr body)
        ∧ ExprWF r by
    intro i r h; exact hgen tele.length i r (by scalar_tac) h
  intro k
  induction k with
  | zero =>
    intro i r hk h
    rw [inductives.native_parts.mk_lams_of_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len tele by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le
      (by simp only [ExprOps.absBinders, List.length_map]; scalar_tac)]
    exact ⟨rfl, hbody⟩
  | succ k ih =>
    intro i r hk h
    rw [inductives.native_parts.mk_lams_of_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ tele.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len tele by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le
        (by simp only [ExprOps.absBinders, List.length_map]; scalar_tac)]
      exact ⟨rfl, hbody⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len tele by scalar_tac)] at h
      have hltv : i.val < tele.val.length := by scalar_tac
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨habsr, hwfr⟩ := ih i2 rest (by scalar_tac) hrest
      rcases hsplit : tele.val[i.val] with ⟨e0, m0⟩
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec tele i hltv)
      subst hyv
      rw [alloc.vec.Vec.index_slice_index, hy, hsplit, bind_tc_ok] at h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨bm1, hbm1, h⟩ := bind_eq_ok_iff.mp h
      have hew : ExprWF e0 ∧ BinderMetaWF m0 := by
        have := htele _ (List.getElem_mem hltv); rw [hsplit] at this; exact this
      rw [Expr.dup_eq he1] at h
      rw [Expr.binder_meta_dup_eq hbm1] at h
      have hcons : (ExprOps.absBinders tele).drop i.val
          = (absExpr e0, absBinderMeta m0) :: (ExprOps.absBinders tele).drop (i.val + 1) := by
        rw [ExprOps.absBinders, ← List.map_drop, List.drop_eq_getElem_cons hltv,
          List.map_cons, List.map_drop, hsplit]
      refine ⟨?_, Expr.lam_wf hew.1 hwfr hew.2 h⟩
      rw [Expr.lam_refines h, habsr, hi2v, hcons, ConLeche.Expr.mkLamsOf]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:261-263` — `mk_lams_of`
refines `Expr.mkLamsOf`: `λ tele, body` over a binder list. -/
theorem mk_lams_of_refines {tele : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {body r : expr.Expr} (htele : ExprOps.BindersWF tele) (hbody : ExprWF body)
    (h : inductives.native_parts.mk_lams_of tele body = ok r) :
    absExpr r = ConLeche.Expr.mkLamsOf (ExprOps.absBinders tele) (absExpr body)
      ∧ ExprWF r := by
  rw [inductives.native_parts.mk_lams_of] at h
  obtain ⟨habs, hwf⟩ := mk_lams_of_from_refines htele hbody h
  exact ⟨by simpa using habs, hwf⟩

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:265-277` — `struct_ih_app`
refines `structIhApp` at the *monomorphised* higher-order arguments: the
`teleOf i` and `idxOf i` of the cited definition are
`structFieldTeleOf cty nP nF i` and `structFieldIdxOf cty nP nF i`, which is
what every con-leche call site passes.  `sub_nat nF (1 + i) + m` is the cited
`nF - 1 - i + m`. -/
theorem struct_ih_app_refines (hg : StructGens) {rec_c : name.Name}
    {rlvls : alloc.vec.Vec level.Level} {pw : prop_when.PropWhen}
    {n_p n n_f i : Std.U64} {cty r : expr.Expr}
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls) (hpw : PropWhenWF pw)
    (hcty : ExprWF cty)
    (h : inductives.native_parts.struct_ih_app rec_c rlvls pw n_p n n_f i cty
        = ok r) :
    absExpr r = ConLeche.structIhApp (absName rec_c) (absLevels rlvls)
        (absPropWhen pw) n_p.val n.val n_f.val i.val
        (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val i.val)
        (ConLeche.structFieldIdxOf (absExpr cty) n_p.val n_f.val i.val)
      ∧ ExprWF r := by
  -- the prefix spine, the lifted index expressions, the field at its telescope
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:279-288` — `struct_ih_apps`
is `recIdx.map fun i => structIhApp …` from `k` on, at the monomorphised
readers. -/
theorem struct_ih_apps_refines (hg : StructGens) {rec_c : name.Name}
    {rlvls : alloc.vec.Vec level.Level} {pw : prop_when.PropWhen}
    {n_p n n_f : Std.U64} {rec_idx : alloc.vec.Vec Std.U64} {cty : expr.Expr}
    {k : Std.Usize} {out v : alloc.vec.Vec expr.Expr}
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls) (hpw : PropWhenWF pw)
    (hcty : ExprWF cty) (hout : ExprsWF out)
    (h : inductives.native_parts.struct_ih_apps rec_c rlvls pw n_p n n_f rec_idx
        cty k out = ok v) :
    absExprs v = absExprs out ++
        ((absU64s rec_idx).drop k.val).map (fun i =>
          ConLeche.structIhApp (absName rec_c) (absLevels rlvls) (absPropWhen pw)
            n_p.val n.val n_f.val i
            (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val i)
            (ConLeche.structFieldIdxOf (absExpr cty) n_p.val n_f.val i))
      ∧ ExprsWF v := by
  -- the `partial_fixpoint` index recursion on `rec_idx.len() - k`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:279-288` —
`struct_rule_body_r` refines `structRuleBodyR`: minor `j` at the fields, then
at the inductive hypotheses of the recursive fields.  `sub_nat (nF + n) (1 + j)`
is the cited `nF + n - 1 - j`. -/
theorem struct_rule_body_r_refines (hg : StructGens) {rec_c : name.Name}
    {rlvls : alloc.vec.Vec level.Level} {pw : prop_when.PropWhen}
    {n_p n n_f j : Std.U64} {rec_idx : alloc.vec.Vec Std.U64} {cty r : expr.Expr}
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls) (hpw : PropWhenWF pw)
    (hcty : ExprWF cty)
    (h : inductives.native_parts.struct_rule_body_r rec_c rlvls pw n_p n n_f j
        rec_idx cty = ok r) :
    absExpr r = ConLeche.structRuleBodyR (absName rec_c) (absLevels rlvls)
        (absPropWhen pw) n_p.val n.val n_f.val j.val (absU64s rec_idx)
        (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val)
        (ConLeche.structFieldIdxOf (absExpr cty) n_p.val n_f.val)
      ∧ ExprWF r := by
  -- `struct_tele_vars`, `struct_ih_apps`, `mk_app_n` at the minor's variable
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:290-305` — `struct_ih_pis`
refines `structIhPis` on the recursive positions from `k` on, `l` `ih` binders
already emitted.  `sub_nat nF (1 + i) + l + m` and `sub_nat (nF + o) 1 + l + m`
are the cited `nF - 1 - i + l + m` and `nF + o - 1 + l + m`. -/
theorem struct_ih_pis_refines (hg : StructGens) {n_f o : Std.U64} {pw : prop_when.PropWhen}
    {cty : expr.Expr} {n_p : Std.U64} {rec_idx : alloc.vec.Vec Std.U64}
    {k : Std.Usize} {l : Std.U64} {body r : expr.Expr}
    (hpw : PropWhenWF pw) (hcty : ExprWF cty) (hbody : ExprWF body)
    (h : inductives.native_parts.struct_ih_pis n_f o pw cty n_p rec_idx k l body
        = ok r) :
    absExpr r = ConLeche.structIhPis n_f.val o.val (absPropWhen pw)
        (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val)
        (ConLeche.structFieldIdxOf (absExpr cty) n_p.val n_f.val)
        ((absU64s rec_idx).drop k.val) l.val (absExpr body)
      ∧ ExprWF r := by
  -- the `partial_fixpoint` recursion down `recIdx`, built on the way out
  sorry

/-- `ConLeche/Kernel/Inductives/StructParts.lean:144-150` —
`struct_ctor_spine_at_o` is `structCtorSpineAt` under the name the
minor-premise generator calls it by; `struct_parts` holds the recursion. -/
theorem struct_ctor_spine_at_o_refines (hg : StructGens) {c : name.Name}
    {lps : alloc.vec.Vec name.Name} {o n_p n_f : Std.U64} {r : expr.Expr}
    (hc : NameWF c) (hlps : NamesWF lps)
    (h : inductives.native_parts.struct_ctor_spine_at_o c lps o n_p n_f = ok r) :
    absExpr r
        = ConLeche.structCtorSpineAt (absName c) (absNames lps) o.val n_p.val n_f.val
      ∧ ExprWF r := by
  rw [inductives.native_parts.struct_ctor_spine_at_o] at h
  exact hg.struct_ctor_spine_at c lps o n_p n_f r hc hlps h

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:307-320` — `lift_all` is
`structMinorTyR`'s `(r.2.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF)`,
as an index recursion. -/
theorem lift_all_refines {o cut : Std.U64} {es out v : alloc.vec.Vec expr.Expr}
    {i : Std.Usize} (hes : ExprsWF es) (hout : ExprsWF out)
    (h : inductives.native_parts.lift_all o cut es i out = ok v) :
    absExprs v = absExprs out ++
        ((absExprs es).drop i.val).map (ConLeche.Expr.liftLooseBVars o.val cut.val)
      ∧ ExprsWF v := by
  revert h
  revert hout
  revert out v i
  suffices hgen : ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec expr.Expr),
      es.length - i.val ≤ k → ExprsWF out →
      inductives.native_parts.lift_all o cut es i out = ok v →
      absExprs v = absExprs out ++
          ((absExprs es).drop i.val).map (ConLeche.Expr.liftLooseBVars o.val cut.val)
        ∧ ExprsWF v by
    intro out v i hout h; exact hgen es.length i out v (by scalar_tac) hout h
  intro k
  induction k with
  | zero =>
    intro i out v hk hout h
    rw [inductives.native_parts.lift_all.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
    rw [← h]
    refine ⟨?_, hout⟩
    rw [List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; scalar_tac)]
    simp
  | succ k ih =>
    intro i out v hk hout h
    rw [inductives.native_parts.lift_all.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ es.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
      rw [← h]
      refine ⟨?_, hout⟩
      rw [List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; scalar_tac)]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len es by scalar_tac)] at h
      have hltv : i.val < es.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := es.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec es i hltv)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, hw, bind_tc_ok] at h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨habs1, hwf1⟩ :=
        ExprOps.lift_loose_bvars_refines (ExprOps.ExprsWF_getElem hes hltv) he1
      obtain ⟨habs, hwf⟩ :=
        ih w out1 v (by scalar_tac) (ExprOps.ExprsWF_push hout hwf1 hout1) h
      refine ⟨?_, hwf⟩
      rw [habs, hwv, ExprOps.absExprs_drop_cons_lt hltv, absExprs, absExprs,
        vec_push_val hout1]
      simp [absExprs, habs1]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:307-320` —
`struct_minor_ty_r` refines `structMinorTyR` at the monomorphised readers: the
field telescope lifted under the `o` extras with every binder's datum reset to
the elimination datum, then the `ih` binders, ending in `motive e⃗ (C p⃗ f⃗)`
lifted above the `ih`s. -/
theorem struct_minor_ty_r_refines (hg : StructGens) {c : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_f o : Std.U64} {pw : prop_when.PropWhen} {cty : expr.Expr}
    {rec_idx : alloc.vec.Vec Std.U64} {r : Option expr.Expr}
    (hc : NameWF c) (hlps : NamesWF lps) (hpw : PropWhenWF pw) (hcty : ExprWF cty)
    (h : inductives.native_parts.struct_minor_ty_r c lps n_p n_f o pw cty rec_idx
        = ok r) :
    r.map absExpr = ConLeche.structMinorTyR (absName c) (absNames lps) n_p.val
        n_f.val o.val (absPropWhen pw) (absExpr cty) (absU64s rec_idx)
      ∧ ∀ x, r = some x → ExprWF x := by
  -- two `strip_pis`, `lift_all`, the constructor spine, `struct_ih_pis`,
  -- `replace_pis_pw`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:322-330` —
`struct_minors_pis_r` refines `structMinorsPisR` on the constructors from `k`
on, the cited extras count `o` growing by one per minor. -/
theorem struct_minors_pis_r_refines (hg : StructGens) {lps : alloc.vec.Vec name.Name}
    {n_p : Std.U64} {pw : prop_when.PropWhen}
    {ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    {k : Std.Usize} {o : Std.U64} {body : expr.Expr} {r : Option expr.Expr}
    (hlps : NamesWF lps) (hpw : PropWhenWF pw) (hctors : Ctors4WF ctors)
    (hbody : ExprWF body)
    (h : inductives.native_parts.struct_minors_pis_r lps n_p pw ctors k o body
        = ok r) :
    r.map absExpr = ConLeche.structMinorsPisR (absNames lps) n_p.val
        (absPropWhen pw) ((absCtors4 ctors).drop k.val) o.val (absExpr body)
      ∧ ∀ x, r = some x → ExprWF x := by
  -- the `partial_fixpoint` recursion down `ctors`, built on the way out
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:332-339` —
`struct_minors_lams_r` refines `structMinorsLamsR`, the `λ` twin. -/
theorem struct_minors_lams_r_refines (hg : StructGens) {lps : alloc.vec.Vec name.Name}
    {n_p : Std.U64} {pw : prop_when.PropWhen}
    {ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    {k : Std.Usize} {o : Std.U64} {body : expr.Expr} {r : Option expr.Expr}
    (hlps : NamesWF lps) (hpw : PropWhenWF pw) (hctors : Ctors4WF ctors)
    (hbody : ExprWF body)
    (h : inductives.native_parts.struct_minors_lams_r lps n_p pw ctors k o body
        = ok r) :
    r.map absExpr = ConLeche.structMinorsLamsR (absNames lps) n_p.val
        (absPropWhen pw) ((absCtors4 ctors).drop k.val) o.val (absExpr body)
      ∧ ∀ x, r = some x → ExprWF x := by
  -- the `partial_fixpoint` recursion down `ctors`, built on the way out
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:341-362` — `struct_rec_ty_r`
refines `structRecTyR`: **the generated recursor type at a recursive block**,
the term `checkNativeRec` `isDefEq`s against the stream's. -/
theorem struct_rec_ty_r_refines (hg : StructGens) {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {elim : name.Name} {large : Bool} {n_p n_idx : Std.U64} {tty : expr.Expr}
    {ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    {r : Option expr.Expr}
    (ht : NameWF t) (hlps : NamesWF lps) (helim : NameWF elim) (htty : ExprWF tty)
    (hctors : Ctors4WF ctors)
    (h : inductives.native_parts.struct_rec_ty_r t lps elim large n_p n_idx tty
        ctors = ok r) :
    r.map absExpr = ConLeche.structRecTyR (absName t) (absNames lps) (absName elim)
        large n_p.val n_idx.val (absExpr tty) (absCtors4 ctors)
      ∧ ∀ x, r = some x → ExprWF x := by
  -- `struct_elim_level`/`zeroness_of`, `strip_pis`, `struct_motive_ty_i`,
  -- the major premise, `struct_minors_pis_r`, `replace_pis_pw`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:364-386` — `struct_rec_rhs_r`
refines `structRecRhsR`: **the generated rule** for constructor `j`, the term
`nativeRulesOk` compares with the stream's *structurally*. -/
theorem struct_rec_rhs_r_refines (hg : StructGens) {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {elim : name.Name} {large : Bool} {n_p n_idx : Std.U64} {tty : expr.Expr}
    {ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    {rec_c : name.Name} {rlvls : alloc.vec.Vec level.Level} {j : Std.U64}
    {r : Option expr.Expr}
    (ht : NameWF t) (hlps : NamesWF lps) (helim : NameWF elim) (htty : ExprWF tty)
    (hctors : Ctors4WF ctors) (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls)
    (h : inductives.native_parts.struct_rec_rhs_r t lps elim large n_p n_idx tty
        ctors rec_c rlvls j = ok r) :
    r.map absExpr = ConLeche.structRecRhsR (absName t) (absNames lps) (absName elim)
        large n_p.val n_idx.val (absExpr tty) (absCtors4 ctors) (absName rec_c)
        (absLevels rlvls) j.val
      ∧ ∀ x, r = some x → ExprWF x := by
  -- the `ctors[j]?` read, `struct_rule_body_r`, `pis_to_lams_pw`,
  -- `struct_minors_lams_r`
  sorry

/-- `u64s_copy_from` appends the rest of the position list to its accumulator,
as an identity. -/
theorem u64s_copy_from_val (xs : alloc.vec.Vec Std.U64) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec Std.U64),
      xs.length - i.val ≤ k →
      inductives.native_parts.u64s_copy_from xs i out = ok v →
      v.val = out.val ++ xs.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [inductives.native_parts.u64s_copy_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [inductives.native_parts.u64s_copy_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ xs.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      have hlt : i.val < xs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := xs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec xs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, hw, bind_tc_ok] at h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `u64s_copy_from` at its own statement. -/
theorem u64s_copy_from_refines {xs out v : alloc.vec.Vec Std.U64} {i : Std.Usize}
    (h : inductives.native_parts.u64s_copy_from xs i out = ok v) :
    v.val = out.val ++ xs.val.drop i.val :=
  u64s_copy_from_val xs xs.length i out v (by scalar_tac) h

/-- `u64s_copy` is the identity. -/
theorem u64s_copy_refines {xs v : alloc.vec.Vec Std.U64}
    (h : inductives.native_parts.u64s_copy xs = ok v) : v = xs := by
  rw [inductives.native_parts.u64s_copy] at h
  exact alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.new] using u64s_copy_from_refines h)

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:388-392` —
`native_ctors4_from` is `nativeCtors4`'s `List.zipWith` from index `i` on;
`zipWith` stops at the shorter list, which is what the port's two length
guards spell. -/
theorem native_ctors4_from_refines
    {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {i : Std.Usize}
    {out v : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    (hctors : ∀ c ∈ ctors_a.val, ConstantValWF c.1) (hout : Ctors4WF out)
    (h : inductives.native_parts.native_ctors4_from ctors_a kinds i out = ok v) :
    absCtors4 v = absCtors4 out ++
        ConLeche.nativeCtors4 ((absCtors ctors_a).drop i.val)
          ((absKindss kinds).drop i.val)
      ∧ Ctors4WF v := by
  -- the `partial_fixpoint` index recursion on `ctors_a.len() - i`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:388-392` — `native_ctors4`
refines `nativeCtors4`: the constructors zipped with their recursive
positions, as the generators take them. -/
theorem native_ctors4_refines {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {v : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    (hctors : ∀ c ∈ ctors_a.val, ConstantValWF c.1)
    (h : inductives.native_parts.native_ctors4 ctors_a kinds = ok v) :
    absCtors4 v = ConLeche.nativeCtors4 (absCtors ctors_a) (absKindss kinds)
      ∧ Ctors4WF v := by
  rw [inductives.native_parts.native_ctors4] at h
  have hout : Ctors4WF (alloc.vec.Vec.new
      (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))) := by
    intro c hc; simp [alloc.vec.Vec.new] at hc
  obtain ⟨habs, hwf⟩ := native_ctors4_from_refines hctors hout h
  exact ⟨by simpa [absCtors4, alloc.vec.Vec.new] using habs, hwf⟩

/-! ## The stream's rules against the generated ones
(`NativeParts.lean:394-475`) -/

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:394-445` —
`native_rule_prefix_head` is `nativeRulePrefixOk`'s leading
`(List.range (nP + 1 + n)).all`, from index `i` on: the rule's λ-domains are
the recursor record's own Π-domains at the same depths, up to the parse
placeholder's binder data (`resetMeta`). -/
theorem native_rule_prefix_head_refines
    {rbs tbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {n i : Std.U64}
    {b : Bool} (hrbs : ExprOps.BindersWF rbs) (htbs : ExprOps.BindersWF tbs)
    (h : inductives.native_parts.native_rule_prefix_head rbs tbs n i = ok b) :
    b = (List.range' i.val (n.val - i.val)).all (fun k =>
      match (ExprOps.absBinders rbs)[k]?, (ExprOps.absBinders tbs)[k]? with
      | some x, some t => ConLeche.Expr.resetMeta x.1 == ConLeche.Expr.resetMeta t.1
      | _, _ => false) := by
  -- the `partial_fixpoint` index recursion on `n - i`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:394-445` —
`native_rule_prefix_fields` is the trailing `(List.range nF).all`: the rule's
field λ-domains are the `j`-th minor premise's first `nF` Π-domains, the rule's
sitting at `base = nP + 1 + n`. -/
theorem native_rule_prefix_fields_refines
    {rbs fbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {base n_f i : Std.U64}
    {b : Bool} (hrbs : ExprOps.BindersWF rbs) (hfbs : ExprOps.BindersWF fbs)
    (h : inductives.native_parts.native_rule_prefix_fields rbs fbs base n_f i
        = ok b) :
    b = (List.range' i.val (n_f.val - i.val)).all (fun k =>
      match (ExprOps.absBinders rbs)[base.val + k]?,
            (ExprOps.absBinders fbs)[k]? with
      | some x, some f => ConLeche.Expr.resetMeta x.1 == ConLeche.Expr.resetMeta f.1
      | _, _ => false) := by
  -- the `partial_fixpoint` index recursion on `n_f - i`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:394-445` —
`native_rule_prefix_ok` refines `nativeRulePrefixOk`: **the rule's `λ` prefix
against the stream's own recursor type**, deliberately not against
`structRecRhsR` (the cited docstring says why: the two are generated from
different data, and comparing the terms rejects 45 e2e fixtures official
accepts). -/
theorem native_rule_prefix_ok_refines {rec_ty : expr.Expr} {n_p n j n_f : Std.U64}
    {rhs : expr.Expr} {b : Bool} (hrec : ExprWF rec_ty) (hrhs : ExprWF rhs)
    (h : inductives.native_parts.native_rule_prefix_ok rec_ty n_p n j n_f rhs
        = ok b) :
    b = ConLeche.nativeRulePrefixOk (absExpr rec_ty) n_p.val n.val j.val n_f.val
      (absExpr rhs) := by
  -- `strip_lams`, `strip_pis`, the head walk, the minor's lift, the field walk
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:447-475` — `native_rule_ok`
is one rule of `nativeRulesOk`: the field count, the body against the canonical
right-hand side at the parse placeholder's binder data, and the λ prefix. -/
theorem native_rule_ok_refines (hg : StructGens) {rec_c : name.Name}
    {rlvls : alloc.vec.Vec level.Level} {pw : prop_when.PropWhen} {n_p n : Std.U64}
    {rhs : expr.Expr} {c_a : env.ConstantVal × Std.U64}
    {ks : alloc.vec.Vec inductives.native_parts.RecFieldKind} {rec_ty : expr.Expr}
    {j : Std.U64} {b : Bool}
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls) (hpw : PropWhenWF pw)
    (hrhs : ExprWF rhs) (hca : ConstantValWF c_a.1) (hrecty : ExprWF rec_ty)
    (h : inductives.native_parts.native_rule_ok rec_c rlvls pw n_p n rhs c_a ks
        rec_ty j = ok b) :
    b = nativeRuleOkAt (absName rec_c) (absLevels rlvls) (absPropWhen pw) n_p.val
      n.val (absExpr rhs) (absConstantVal c_a.1) c_a.2.val (absRecFieldKinds ks)
      (absExpr rec_ty) j.val := by
  -- `strip_lams`, `struct_rule_body_r`, `reset_meta`, `native_rule_prefix_ok`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:447-475` —
`native_rules_ok_from` is `nativeRulesOk`'s `(List.range n).all` from `j` on. -/
theorem native_rules_ok_from_refines (hg : StructGens) {rec_c : name.Name}
    {rlvls : alloc.vec.Vec level.Level} {pw : prop_when.PropWhen} {n_p n : Std.U64}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {rhss : alloc.vec.Vec expr.Expr} {rec_ty : expr.Expr} {j : Std.U64} {b : Bool}
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls) (hpw : PropWhenWF pw)
    (hcs : ∀ c ∈ cs.val, ConstantValWF c.1) (hrhss : ExprsWF rhss)
    (hrecty : ExprWF rec_ty)
    (h : inductives.native_parts.native_rules_ok_from rec_c rlvls pw n_p n cs kinds
        rhss rec_ty j = ok b) :
    b = (List.range' j.val (n.val - j.val)).all (fun k =>
      match (absExprs rhss)[k]?, (absCtors cs)[k]?, (absKindss kinds)[k]? with
      | some rhs, some (cA, nF), some ks =>
        nativeRuleOkAt (absName rec_c) (absLevels rlvls) (absPropWhen pw) n_p.val
          n.val rhs cA nF ks (absExpr rec_ty) k
      | _, _, _ => false) := by
  -- the `partial_fixpoint` index recursion on `n - j`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:447-475` — `native_rules_ok`
refines `nativeRulesOk`: **the stream's rules against the generated ones**, the
structural comparison official's replay makes. -/
theorem native_rules_ok_refines (hg : StructGens) {rec_c : name.Name}
    {rlvls : alloc.vec.Vec level.Level} {pw : prop_when.PropWhen} {n_p n : Std.U64}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {rhss : alloc.vec.Vec expr.Expr} {rec_ty : expr.Expr} {b : Bool}
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls) (hpw : PropWhenWF pw)
    (hcs : ∀ c ∈ cs.val, ConstantValWF c.1) (hrhss : ExprsWF rhss)
    (hrecty : ExprWF rec_ty)
    (h : inductives.native_parts.native_rules_ok rec_c rlvls pw n_p n cs kinds rhss
        rec_ty = ok b) :
    b = ConLeche.nativeRulesOk (absName rec_c) (absLevels rlvls) (absPropWhen pw)
      n_p.val n.val (absCtors cs) (absKindss kinds) (absExprs rhss)
      (absExpr rec_ty) := by
  rw [nativeRulesOk_eq]
  rw [inductives.native_parts.native_rules_ok] at h
  simp only [lift, bind_tc_ok] at h
  have hrl : (absExprs rhss).length = rhss.val.length := by simp [absExprs]
  have hkl : (absKindss kinds).length = kinds.val.length := by
    simp [IndAbs.absKindss]
  have hcr : (Std.UScalar.cast .U64 (alloc.vec.Vec.len rhss)).val
      = (alloc.vec.Vec.len rhss).val := ExprOps.usize_cast_u64_val _
  have hck : (Std.UScalar.cast .U64 (alloc.vec.Vec.len kinds)).val
      = (alloc.vec.Vec.len kinds).val := ExprOps.usize_cast_u64_val _
  have hlr := alloc.vec.Vec.len_val rhss
  have hlk := alloc.vec.Vec.len_val kinds
  split at h
  · rename_i hn1
    split at h
    · rename_i hn2
      have hr : (absExprs rhss).length = n.val := by
        simp only [hrl]; rw [← hcr, hn1] at hlr; scalar_tac
      have hk : (absKindss kinds).length = n.val := by
        simp only [hkl]; rw [← hck, hn2] at hlk; scalar_tac
      rw [native_rules_ok_from_refines hg hrec hrlvls hpw hcs hrhss hrecty h]
      simp [hr, hk, List.range_eq_range']
    · rename_i hn2
      have hk : ¬ (absKindss kinds).length = n.val := by
        simp only [hkl]; rw [← hck] at hlk
        intro hc; exact hn2 (by scalar_tac)
      rw [← Result.ok_injective h]; simp [hk]
  · rename_i hn1
    have hr : ¬ (absExprs rhss).length = n.val := by
      simp only [hrl]; rw [← hcr] at hlr
      intro hc; exact hn1 (by scalar_tac)
    rw [← Result.ok_injective h]; simp [hr]

/-! ## Recognition (`NativeParts.lean:501-652`) -/

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:501-523` — `native_counts`
refines `nativeCounts?`: `nP` is the count the DECLARATION carries and `nIdx`
is what is left of the type former's Π-telescope once those binders are peeled;
at a former declared at a *definition* the recursor record's two argument sums
are the only reading available. -/
theorem native_counts_refines {n_pd : Std.U64} {cv_t : env.ConstantVal}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)} {m_i r_p : Std.U64}
    {o : Option (Std.U64 × Std.U64)}
    (hcv : ConstantValWF cv_t) (hcs : SumParts.CtorSpecsWF cs)
    (h : inductives.native_parts.native_counts n_pd cv_t cs m_i r_p = ok o) :
    o.map (fun p => (p.1.val, p.2.val))
      = ConLeche.nativeCounts? n_pd.val (absConstantVal cv_t)
          (SumParts.absCtorSpecs cs) m_i.val r_p.val := by
  -- `pi_binders`, the `.sort` residual test, the three `U64` subtractions
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:525-549` —
`native_rec_pin_rules` is `nativeRecPinOk`'s `(List.range p.ctors.length).all`:
rule `j` names constructor `j` with its field count. -/
theorem native_rec_pin_rules_refines {rules : alloc.vec.Vec env.RecRule}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)} {n j : Std.U64}
    {b : Bool} (hrules : RecRulesWF rules) (hcs : SumParts.CtorSpecsWF cs)
    (h : inductives.native_parts.native_rec_pin_rules rules cs n j = ok b) :
    b = (List.range' j.val (n.val - j.val)).all (fun k =>
      match (absRecRules rules)[k]?, (SumParts.absCtorSpecs cs)[k]? with
      | some rule, some (cvC, _, nF) => rule.ctor == cvC.name && rule.nfields == nF
      | _, _ => false) := by
  -- the `partial_fixpoint` index recursion on `n - j`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:525-549` —
`native_rec_pin_ok` refines `nativeRecPinOk`: **the recursor record's
structural pin**, whose `false` the recursor stage throws on. -/
theorem native_rec_pin_ok_refines {p : inductives.sum_parts.InductiveShape}
    {block : alloc.vec.Vec env.ConstantInfo} {b : Bool}
    (hp : InductiveShapeWF p) (hblock : ConstantInfosWF block)
    (h : inductives.native_parts.native_rec_pin_ok p block = ok b) :
    b = ConLeche.nativeRecPinOk (absInductiveShape p) (absConstantInfos block) := by
  -- the `.indInfo` head, `sum_split_from` at `i = 1`, the two argument sums,
  -- `native_rec_pin_rules`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:551-560` —
`native_rec_lps_ok` refines `nativeRecLpsOk`: **the recursor record's
level-parameter pin** — the block's own level parameters, with a fresh
elimination parameter in front at the LARGE eliminator. -/
theorem native_rec_lps_ok_refines {p : inductives.sum_parts.InductiveShape}
    {b : Bool} (hp : InductiveShapeWF p)
    (h : inductives.native_parts.native_rec_lps_ok p = ok b) :
    b = ConLeche.nativeRecLpsOk (absInductiveShape p) := by
  -- `prop_when::append_from` for the cons, then `names_beq`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:562-614` —
`native_ctors_ok_from` is `nativeShape?`'s `cs.all` front guard from index `i`:
every constructor carries the block's parameter count and level parameters and
no reserved basis name. -/
theorem native_ctors_ok_from_refines
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)} {n_p : Std.U64}
    {lps reserved : alloc.vec.Vec name.Name} {i : Std.Usize} {b : Bool}
    (hcs : SumParts.CtorSpecsWF cs) (hlps : NamesWF lps) (hres : NamesWF reserved)
    (h : inductives.native_parts.native_ctors_ok_from cs n_p lps reserved i
        = ok b) :
    b = ((SumParts.absCtorSpecs cs).drop i.val).all (fun c =>
      c.2.1 == n_p.val && c.1.levelParams == absNames lps
        && (absNames reserved).contains c.1.name == false) := by
  -- the `partial_fixpoint` index recursion on `cs.len() - i`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:562-614` —
`native_shape_names_ok` is `nativeShape?`'s two reserved-name exclusions and
the constructors' guard, pulled into one function because Aeneas could not
join the borrows of the cited `&&` cascade (task #14's rule: never hold a
container's borrow across a branch that touches the container). -/
theorem native_shape_names_ok_refines {cv_t cv_r : env.ConstantVal}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)} {n_p : Std.U64}
    {reserved : alloc.vec.Vec name.Name} {b : Bool}
    (hcvt : ConstantValWF cv_t) (hcvr : ConstantValWF cv_r)
    (hcs : SumParts.CtorSpecsWF cs) (hres : NamesWF reserved)
    (h : inductives.native_parts.native_shape_names_ok cv_t cv_r cs n_p reserved
        = ok b) :
    b = ((absNames reserved).contains (absConstantVal cv_t).name == false
      && (absNames reserved).contains (absConstantVal cv_r).name == false
      && (SumParts.absCtorSpecs cs).all (fun c =>
          c.2.1 == n_p.val && c.1.levelParams == (absConstantVal cv_t).levelParams
            && (absNames reserved).contains c.1.name == false)) := by
  -- two `name::contains`, then `native_ctors_ok_from` at `i = 0`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:562-614` —
`native_ctors_of_from` is `nativeShape?`'s `cs.map fun c => (c.1, c.2.2)` from
index `i`, with the port's accumulator in front; stated as an identity on the
`Vec`, since the port only copies. -/
theorem native_ctors_of_from_val
    (cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec (env.ConstantVal × Std.U64)),
      cs.length - i.val ≤ k →
      inductives.native_parts.native_ctors_of_from cs i out = ok v →
      v.val = out.val ++ (cs.val.drop i.val).map (fun c => (c.1, c.2.2)) := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [inductives.native_parts.native_ctors_of_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [inductives.native_parts.native_ctors_of_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ cs.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      have hlt : i.val < cs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := cs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt)
      subst hyv
      rcases hsplit : cs.val[i.val] with ⟨cv0, n0, f0⟩
      simp only [alloc.vec.Vec.index_slice_index, hy, hw, hsplit, bind_tc_ok] at h
      obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      rw [Env.constant_val_dup_refines hcv1] at hout1
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt, hsplit]
      simp

/-- `native_ctors_of_from` at its own statement. -/
theorem native_ctors_of_from_refines
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)} {i : Std.Usize}
    {out v : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    (h : inductives.native_parts.native_ctors_of_from cs i out = ok v) :
    v.val = out.val ++ (cs.val.drop i.val).map (fun c => (c.1, c.2.2)) :=
  native_ctors_of_from_val cs cs.length i out v (by scalar_tac) h

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:562-614` — `native_ctors_of`
is the cited `cs.map fun c => (c.1, c.2.2)`: the constructors with their
*field* counts (the parameter count is the block's). -/
theorem native_ctors_of_refines
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)}
    {v : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    (h : inductives.native_parts.native_ctors_of cs = ok v) :
    absCtors v = (SumParts.absCtorSpecs cs).map (fun c => (c.1, c.2.2)) := by
  rw [inductives.native_parts.native_ctors_of] at h
  have hv := native_ctors_of_from_refines h
  simp only [alloc.vec.Vec.new] at hv
  simp [IndAbs.absCtors, SumParts.absCtorSpecs, hv]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:562-614` —
`native_rhss_of_from` is `nativeShape?`'s `rules.map (·.rhs)` from index `i`. -/
theorem native_rhss_of_from_val (rules : alloc.vec.Vec env.RecRule) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec expr.Expr),
      rules.length - i.val ≤ k →
      inductives.native_parts.native_rhss_of_from rules i out = ok v →
      v.val = out.val ++ (rules.val.drop i.val).map (fun r => r.rhs) := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [inductives.native_parts.native_rhss_of_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len rules by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [inductives.native_parts.native_rhss_of_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ rules.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len rules by scalar_tac),
        Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len rules by scalar_tac)] at h
      have hlt : i.val < rules.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := rules.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rules i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, hw, bind_tc_ok] at h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      rw [Expr.dup_eq he] at hout1
      have hlt2 : i.val < (rules.val.map (fun r : env.RecRule => r.rhs)).length := by
        simpa using hlt
      have hcons : (rules.val.map (fun r : env.RecRule => r.rhs)).drop i.val
          = rules.val[i.val].rhs
            :: (rules.val.map (fun r : env.RecRule => r.rhs)).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv]
      simp [hcons]

/-- `native_rhss_of_from` at its own statement. -/
theorem native_rhss_of_from_refines {rules : alloc.vec.Vec env.RecRule}
    {i : Std.Usize} {out v : alloc.vec.Vec expr.Expr}
    (h : inductives.native_parts.native_rhss_of_from rules i out = ok v) :
    v.val = out.val ++ (rules.val.drop i.val).map (fun r => r.rhs) :=
  native_rhss_of_from_val rules rules.length i out v (by scalar_tac) h

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:562-614` — `native_rhss_of`
is the cited `rules.map (·.rhs)`: the rules' right-hand sides as exported. -/
theorem native_rhss_of_refines {rules : alloc.vec.Vec env.RecRule}
    {v : alloc.vec.Vec expr.Expr}
    (h : inductives.native_parts.native_rhss_of rules = ok v) :
    absExprs v = (absRecRules rules).map (fun r => r.rhs) := by
  rw [inductives.native_parts.native_rhss_of] at h
  have hv := native_rhss_of_from_refines h
  simp only [alloc.vec.Vec.new] at hv
  simp [absExprs, absRecRules, absRecRule, hv]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:562-614` —
`native_shape_large` is `nativeShape?`'s `large?` reading: a fresh elimination
level parameter in front of the block's own.  A record that is neither shape is
read as the *small* eliminator with the pin failing (`nativeRecLpsOk`, thrown
at `checkNativeRec`) rather than refusing the block. -/
theorem native_shape_large_refines {cv_r : env.ConstantVal}
    {lps : alloc.vec.Vec name.Name} {o : Option name.Name}
    (hcv : ConstantValWF cv_r) (hlps : NamesWF lps)
    (h : inductives.native_parts.native_shape_large cv_r lps = ok o) :
    o.map absName
      = (match (absConstantVal cv_r).levelParams with
         | elim :: relps =>
           if relps == absNames lps && !(absNames lps).contains elim then some elim
           else none
         | [] => none) := by
  -- the head/tail split, `prop_when::append_from`, `names_beq`, `name::contains`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:562-614` — `native_shape`
refines `nativeShape?`: the block's shape at a recursive block — the type
former, the constructors and the counts (`nativeCounts?`), with the rules'
right-hand sides as exported and the recursor's level-parameter shape.
Nothing else of the recursor record is pinned here. -/
theorem native_shape_refines (hg : StructGens) {n_pd : Std.U64}
    {block : alloc.vec.Vec env.ConstantInfo}
    {o : Option inductives.sum_parts.InductiveShape}
    (hblock : ConstantInfosWF block)
    (h : inductives.native_parts.native_shape n_pd block = ok o) :
    o.map absInductiveShape = ConLeche.nativeShape? n_pd.val (absConstantInfos block)
      ∧ ∀ p, o = some p → InductiveShapeWF p := by
  -- the `.indInfo` head, `sum_split_from` at `i = 1`, `native_counts`,
  -- `native_shape_names_ok`, the result sort through `strip_pis`,
  -- `level_is_prop`, `native_ctors_of`, `native_rhss_of`, `native_shape_large`
  sorry

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:631-652` — `native_parts`
refines `nativeParts?`: recognise a direct block — ONE ROUTE — its SHAPE, the
fields' kinds a placeholder the install fills (`NativeParts.withKinds`), and
the recursor record's structural pin recorded as a verdict rather than a
refusal (task #220: a block whose recursor record is a stub is REJECTED by its
own type and constructors rather than declined). -/
theorem native_parts_refines (hg : StructGens) {n_pd : Std.U64}
    {block : alloc.vec.Vec env.ConstantInfo}
    {o : Option inductives.native_parts.NativeParts}
    (hblock : ConstantInfosWF block)
    (h : inductives.native_parts.native_parts n_pd block = ok o) :
    o.map absNativeParts = ConLeche.nativeParts? n_pd.val (absConstantInfos block)
      ∧ ∀ p, o = some p → NativePartsWF p := by
  -- `native_shape`, then `native_rec_pin_ok` on the same block
  sorry

end Gens

end ConRon.Refine.NativeParts
