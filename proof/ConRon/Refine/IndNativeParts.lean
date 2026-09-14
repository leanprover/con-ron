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

Task #59 found the same shape at the readers below, and each carries the same
hypothesis for the same reason — the statements are *false* without it, because
on a hypothetical 32-bit target the port's `i as usize >= v.len()` guard lets a
WRAPPED index through where con-leche's `v[i]?` answers `none`:

* `native_rec_pin_rules` (`j.val ≤ Std.Usize.max`),
* `native_rule_prefix_head` (`i.val ≤ Std.Usize.max`),
* `native_rule_prefix_fields` (`base.val + i.val ≤ Std.Usize.max`),
* `native_rules_ok_from` (`j.val ≤ Std.Usize.max`),
* `rec_ctor_kinds_at` (`n_p.val + n_f.val ≤ Std.Usize.max`),
* `struct_field_tele_of` and `struct_field_idx_of` (`i.val ≤ n_f.val`, which
  with the telescope's own length is the same bound),
* `native_rule_prefix_ok` and `native_rule_ok` (`j.val ≤ n.val`, likewise:
  the recursor type's `Π` tower has exactly `nP + 1 + n` binders, so the
  minor's index `nP + 1 + j` fits a `usize` exactly on the minors),
* `struct_ih_app`, `struct_ih_apps`, `struct_rule_body_r`, `struct_ih_pis`,
  `struct_minor_ty_r`, `struct_minors_pis_r`, `struct_minors_lams_r`,
  `struct_rec_ty_r` and `struct_rec_rhs_r`: the recursive POSITIONS a
  generator reads a field telescope at are field indices, `x.val ≤ n_f.val`
  (per constructor from `struct_minors_pis_r` on — that is
  `IndNativeInstall.RecPosWF`),
* `struct_rec_rhs_r` also carries `j.val ≤ Std.Usize.max`: it reads
  `ctors[j as usize]` where the cited `structRecRhsR` reads `ctors[j]?`,
* `native_ctors4(_from)` takes the matching *producer* side,
  `IndNativeInstall.KindsFitCtors` (`kinds[k].length ≤ ctors_a[k].2`), and
  **concludes** `RecPosWF` of its output: every position it records comes from
  `recIdxOf kinds[k]`, whose members are `< kinds[k].length`.

Every one of them is discharged at its call sites — `native_rec_pin_ok`,
`native_rules_ok` and `rec_ctor_kinds` start their recursions at `0`
(`Nat.zero_le`), `native_rules_ok_from` passes its own `j < n`,
`native_rule_ok` reads the positions off `recIdxOf ks` (whose members are
`< ks.length == nF`), the telescope readers' callers loop over the
constructor's `n_f` fields, and `RecPosWF`/`KindsFitCtors` travel from
`check_native_tail_guards`' `native_fields_ok` through `native_ctors4` to the
recursor stage — and re-discharged at each step from the `Vec` the counter
indexes (`Scalars.u64_le_usize_max_of_le_len`, `Vec.property` through
`ConLeche.Expr.stripPis_length`).  Nothing is weakened: every conclusion is
the exact one, and the whole chain closes inside the tier with no platform
assumption anywhere.

## `sorry`s

**None.**  All 69 lemmas are proved: every copy (as an identity), every
list/telescope builder (`lift_all`, `struct_idx_at(_all)`,
`struct_tele_at(_from)`, `struct_tele_vars`, `mk_pis_of(_from)`,
`mk_lams_of(_from)`, `struct_rec_prefix_at`/`_minors`), the positions
(`rec_idx_of(_from)`, `u64s_copy(_from)`), the two `getD` readers, the whole
record group, `native_ctors4(_from)`, `native_ctors_of(_from)`,
`native_rhss_of(_from)`, and — whole groups at a time —

* **the positivity walk**: `rec_fam_ok`, `args_free_of_from`,
  `rec_positivity`, `rec_field_kind`, `rec_ctor_kinds_at`, `rec_ctor_kinds`;
* **the `∀`-telescope readers**: `pi_binders(_go)`, `struct_field_tele_of`,
  `struct_field_idx_of`;
* **the recursor's own generators**: `struct_ih_app`, `struct_ih_apps`,
  `struct_rule_body_r`, `struct_ih_pis`, `struct_minor_ty_r`,
  `struct_ctor_spine_at_o`, `struct_minors_pis_r`, `struct_minors_lams_r`,
  `struct_rec_ty_r`, `struct_rec_rhs_r`;
* **the stream's rules**: `native_rule_prefix_head`, `native_rule_prefix_fields`,
  `native_rule_prefix_ok`, `native_rule_ok`, `native_rules_ok(_from)`;
* **recognition**: `native_counts`, `native_rec_pin_rules`,
  `native_rec_pin_ok`, `native_rec_lps_ok`, `native_ctors_ok_from`,
  `native_shape_names_ok`, `native_shape_large`, `native_shape` and
  `native_parts`.

The four entry points the install's ingredients name —
`native_parts_refines` (the recogniser the spec bridge composes),
`native_rules_ok_refines` (the stream's rules against the generated ones),
`struct_rec_ty_r_refines` and `struct_rec_rhs_r_refines` (the recursor type
and the generated rule `checkNativeRec` compares) — are each closed at
`[propext, Classical.choice, Quot.sound]` under `StructGens`.
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
  rw [inductives.native_parts.rec_fam_ok] at h
  rw [ConLeche.recFamOk]
  obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habsh, hheadwf⟩ := ExprOps.get_app_fn_refines he hhead
  simp only [name_dup_eq, bind_tc_ok] at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hvabs, hvwf⟩ := hg.params_of lps v hlps hv
  obtain ⟨expected, hexp, h⟩ := bind_eq_ok_iff.mp h
  have hexpabs : absExpr expected
      = .const (absName t) ((absNames lps).map ConLeche.Level.param) := by
    rw [Expr.mk_const_refines hexp, hvabs]
  have hexpwf : ExprWF expected := ExprWF.mk_const ht hvwf hexp
  obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
  have hb0abs := Expr.beq_refines hheadwf hexpwf hb0
  rw [habsh, hexpabs] at hb0abs
  split at h
  · rename_i hbt
    rw [hb0abs] at hbt
    have hc1 : ((absExpr e).getAppFn
        == ConLeche.Expr.const (absName t) ((absNames lps).map .param)) = true := by
      simp [of_decide_eq_true hbt]
    obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hargsabs, hargswf⟩ := ExprOps.get_app_args_refines he hargs
    simp only [lift_eq, bind_tc_ok] at h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = n_p.val + n_idx.val := HashMap.uscalar_add_eq hi2
    have hlcast : (Std.UScalar.cast .U64 (alloc.vec.Vec.len args) : Std.U64).val
        = args.val.length := by
      rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
    have hgal : (absExpr e).getAppArgs.length = args.val.length := by
      rw [← hargsabs]; simp [absExprs]
    split at h
    · rename_i he2
      have hlen : args.val.length = n_p.val + n_idx.val := by
        rw [← hlcast, he2, hi2v]
      have hc2 : ((absExpr e).getAppArgs.length == n_p.val + n_idx.val) = true := by
        rw [hgal, hlen]; simp
      have hnpcast : (Std.UScalar.cast .Usize n_p : Std.Usize).val = n_p.val :=
        ExprOps.u64_cast_usize_val
          (Scalars.u64_le_usize_max_of_le_len (v := args) (by omega))
      obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hv1abs, hv1wf⟩ := ExprOps.take_exprs_refines hargswf hv1
      obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hv2abs, hv2wf⟩ := hg.struct_ps_at o n_p v2 hv2
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1abs := Env.exprs_beq_refines hv1wf hv2wf hb1
      rw [hv1abs, hv2abs, hnpcast, hargsabs] at hb1abs
      split at h
      · rename_i hb1t
        rw [hb1abs] at hb1t
        have hc3 : ((absExpr e).getAppArgs.take n_p.val
            == ConLeche.structPsAt o.val n_p.val) = true := by
          simp [of_decide_eq_true hb1t]
        rw [args_free_of_from_refines hg ht hargswf h, hnpcast, hargsabs]
        simp only [hc1, hc2, hc3, Bool.true_and]
      · rename_i hb1f
        rw [hb1abs] at hb1f
        have hc3 : ((absExpr e).getAppArgs.take n_p.val
            == ConLeche.structPsAt o.val n_p.val) = false := by
          rw [Bool.eq_false_iff]
          intro hc; exact hb1f (by simp [by simpa using hc])
        rw [← Result.ok_injective h]
        simp only [hc1, hc2, hc3, Bool.true_and, Bool.false_and]
    · rename_i he2
      have hc2 : ((absExpr e).getAppArgs.length == n_p.val + n_idx.val) = false := by
        rw [hgal, Bool.eq_false_iff]
        intro hc
        refine he2 (Std.UScalar.eq_of_val_eq ?_)
        rw [hlcast, hi2v]; simpa using hc
      rw [← Result.ok_injective h]
      simp only [hc1, hc2, Bool.true_and, Bool.false_and]
  · rename_i hbf
    rw [hb0abs] at hbf
    have hc1 : ((absExpr e).getAppFn
        == ConLeche.Expr.const (absName t) ((absNames lps).map .param)) = false := by
      rw [Bool.eq_false_iff]
      intro hc; exact hbf (by simp [by simpa using hc])
    rw [← Result.ok_injective h]
    simp only [hc1, Bool.false_and]

/-- `ExprNode`'s `kind` projection at a decomposed node (`Refine/ExprOps.lean`'s
`node_kind` is the same fact one `Arc` deeper, and does not fire here). -/
theorem exprNode_kind (d : Std.U64) (k : expr.ExprKind) :
    (expr.ExprNode.mk d k).kind = k := rfl

/-- A well-formed `Const` node has a well-formed name. -/
theorem wf_const_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64} {n : name.Name}
    {us : levels.Levels}
    (hk : e = .mk (.mk d (.Const n us))) : NameWF n := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u1 _ hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; simp at hk
  | @mk_const n1 us1 _ hn1 _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.Const.injEq] at hk
    obtain ⟨-, rfl, -⟩ := hk
    exact hn1
  | @app f a _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp at hk
  | @lam ty bo m _ _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; simp at hk
  | @forall_e ty bo m _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; simp at hk
  | @let_e ty v bo _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk

/-- `recPositivity` at a `∀` binder: the cited peel. -/
theorem recPositivity_forallE {T : ConLeche.Name} {lps : List ConLeche.Name}
    {nP nIdx o k : Nat} {dom body : ConLeche.Expr} {m : ConLeche.BinderMeta} :
    ConLeche.recPositivity T lps nP nIdx o (.forallE dom body m) k
      = (if dom.mentionsConst T then .negative
         else ConLeche.recPositivity T lps nP nIdx o body (k + 1)) := by
  rw [ConLeche.recPositivity]

/-- `recPositivity` at the residual of the field's own telescope: the cited
`is_valid_ind_app` cascade. -/
theorem recPositivity_other {T : ConLeche.Name} {lps : List ConLeche.Name}
    {nP nIdx o k : Nat} {e : ConLeche.Expr}
    (hne : ∀ dom body m, e ≠ .forallE dom body m) :
    ConLeche.recPositivity T lps nP nIdx o e k
      = (if !e.mentionsConst T then .ordinary
         else if e.getAppFn == ConLeche.Expr.const T (lps.map .param) then
           (if e.getAppArgs.length == nP + nIdx
               && e.getAppArgs.take nP == ConLeche.structPsAt (o + k) nP then
             (if ConLeche.recFamOk T lps nP nIdx (o + k) e then
               (if k == 0 then .recursive else .reflexive)
              else .negative)
            else .negative)
         else
           match e.getAppFn with
           | .const T' _ => if T' == T then .negative else .unsupported
           | _ => .unsupported) := by
  rw [ConLeche.recPositivity]
  · rfl
  · intro dom body m hc
    exact absurd hc (hne dom body m)

/-- The residual arm of `rec_positivity`, once the node is known not to be a
`∀`: official's `is_valid_ind_app` on the field's residual. -/
private theorem rec_positivity_other_refines (hg : StructGens) {t : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_idx o k : Std.U64} {e : expr.Expr}
    {r : inductives.native_parts.RecFieldKind}
    (ht : NameWF t) (hlps : NamesWF lps) (he : ExprWF e)
    (hkf : ∀ ty bo m, (expr.ExprNode.kind e._0) ≠ .ForallE ty bo m)
    (hnf : ∀ dom body m, absExpr e ≠ .forallE dom body m)
    (h : inductives.native_parts.rec_positivity t lps n_p n_idx o e k = ok r) :
    absRecFieldKind r
      = ConLeche.recPositivity (absName t) (absNames lps) n_p.val n_idx.val o.val
          (absExpr e) k.val := by
  rw [inductives.native_parts.rec_positivity] at h
  simp only [arc_deref_eq, bind_tc_ok] at h
  rw [recPositivity_other hnf]
  split at h
  case h_7 => rename_i ty bo m hkc; exact absurd hkc (hkf ty bo m)
  all_goals
    obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
    have hb0abs := hg.mentions_const t e b0 ht he hb0
    split at h
    · rename_i hbt
      rw [hb0abs] at hbt
      rw [if_neg (by rw [hbt]; simp)]
      obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hheadabs, hheadwf⟩ := ExprOps.get_app_fn_refines he hhead
      simp only [name_dup_eq, bind_tc_ok] at h
      obtain ⟨ps, hps, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hpsabs, hpswf⟩ := hg.params_of lps ps hlps hps
      obtain ⟨expected, hexp, h⟩ := bind_eq_ok_iff.mp h
      have hexpabs : absExpr expected
          = .const (absName t) ((absNames lps).map ConLeche.Level.param) := by
        rw [Expr.mk_const_refines hexp, hpsabs]
      have hexpwf : ExprWF expected := ExprWF.mk_const ht hpswf hexp
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1abs := Expr.beq_refines hheadwf hexpwf hb1
      rw [hheadabs, hexpabs] at hb1abs
      split at h
      · rename_i hb1t
        rw [hb1abs] at hb1t
        rw [if_pos (show ((absExpr e).getAppFn
            == ConLeche.Expr.const (absName t)
              ((absNames lps).map ConLeche.Level.param)) = true by
          simp [of_decide_eq_true hb1t])]
        obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hargsabs, hargswf⟩ := ExprOps.get_app_args_refines he hargs
        simp only [lift_eq, bind_tc_ok] at h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = n_p.val + n_idx.val := HashMap.uscalar_add_eq hi2
        have hlcast : (Std.UScalar.cast .U64 (alloc.vec.Vec.len args) : Std.U64).val
            = args.val.length := by
          rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
        have hgal : (absExpr e).getAppArgs.length = args.val.length := by
          rw [← hargsabs]; simp [absExprs]
        obtain ⟨sh, hsh, h⟩ := bind_eq_ok_iff.mp h
        have hshabs : sh = ((absExpr e).getAppArgs.length == n_p.val + n_idx.val
            && (absExpr e).getAppArgs.take n_p.val
              == ConLeche.structPsAt (o.val + k.val) n_p.val) := by
          split at hsh
          · rename_i he2
            have hlen : args.val.length = n_p.val + n_idx.val := by
              rw [← hlcast, he2, hi2v]
            have hnpcast : (Std.UScalar.cast .Usize n_p : Std.Usize).val = n_p.val :=
              ExprOps.u64_cast_usize_val
                (Scalars.u64_le_usize_max_of_le_len (v := args) (by omega))
            obtain ⟨v1, hv1, hsh⟩ := bind_eq_ok_iff.mp hsh
            obtain ⟨hv1abs, hv1wf⟩ := ExprOps.take_exprs_refines hargswf hv1
            obtain ⟨i4, hi4, hsh⟩ := bind_eq_ok_iff.mp hsh
            have hi4v : i4.val = o.val + k.val := HashMap.uscalar_add_eq hi4
            obtain ⟨v2, hv2, hsh⟩ := bind_eq_ok_iff.mp hsh
            obtain ⟨hv2abs, hv2wf⟩ := hg.struct_ps_at i4 n_p v2 hv2
            rw [hi4v] at hv2abs
            rw [Env.exprs_beq_refines hv1wf hv2wf hsh, hv1abs, hv2abs, hnpcast,
              hargsabs, hgal, hlen]
            rw [Bool.eq_iff_iff]
            simp
          · rename_i he2
            have hlen : ¬ (args.val.length = n_p.val + n_idx.val) := by
              intro hc
              exact he2 (Std.UScalar.eq_of_val_eq (by rw [hlcast, hi2v]; exact hc))
            rw [← Result.ok_injective hsh, hgal]
            simp [hlen]
        split at h
        · rename_i hsht
          rw [hshabs] at hsht
          rw [if_pos hsht]
          obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
          have hi3v : i3.val = o.val + k.val := HashMap.uscalar_add_eq hi3
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2abs := rec_fam_ok_refines hg ht hlps he hb2
          rw [hi3v] at hb2abs
          split at h
          · rename_i hb2t
            rw [hb2abs] at hb2t
            rw [if_pos hb2t]
            split at h
            · rename_i hk0
              rw [← Result.ok_injective h,
                if_pos (show (k.val == 0) = true by rw [hk0]; rfl)]
              rfl
            · rename_i hk0
              rw [← Result.ok_injective h,
                if_neg (show ¬ (k.val == 0) = true by
                  intro hc
                  exact hk0 (Std.UScalar.eq_of_val_eq (by simpa using hc)))]
              rfl
          · rename_i hb2f
            rw [hb2abs] at hb2f
            rw [← Result.ok_injective h, if_neg hb2f]
            rfl
        · rename_i hshf
          rw [hshabs] at hshf
          rw [← Result.ok_injective h, if_neg hshf]
          rfl
      · rename_i hb1f
        rw [hb1abs] at hb1f
        rw [if_neg (by intro hc; exact hb1f (by simp [by simpa using hc])),
          ← hheadabs]
        obtain ⟨nd⟩ := head
        obtain ⟨dh, kh⟩ := nd
        simp only [ExprOps.node_kind] at h
        cases kh with
        | Const t2 us =>
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2abs := Name.beq_refines (wf_const_inv hheadwf rfl) ht hb2
          simp only [absExpr_mk, absExprKind]
          split at h
          · rename_i hb2t
            rw [hb2abs] at hb2t
            rw [← Result.ok_injective h,
              if_pos (show (absName t2 == absName t) = true by
                simp [of_decide_eq_true hb2t])]
            rfl
          · rename_i hb2f
            rw [hb2abs] at hb2f
            rw [← Result.ok_injective h,
              if_neg (show ¬ (absName t2 == absName t) = true by
                intro hc; exact hb2f (by simp [by simpa using hc]))]
            rfl
        | _ =>
          rw [← Result.ok_injective h]
          simp only [absExpr_mk, absExprKind]
          rfl
    · rename_i hbf
      rw [hb0abs] at hbf
      rw [if_pos (by rw [Bool.eq_false_iff.mpr hbf]; simp), ← Result.ok_injective h]
      rfl

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
  revert k r
  induction he with
  | @bvar i e h1 =>
    intro k r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    exact rec_positivity_other_refines hg ht hlps (ExprWF.bvar h1) (by simp)
      (by simp) h
  | @fvar idx ty e hty h1 ihty =>
    intro k r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    exact rec_positivity_other_refines hg ht hlps (ExprWF.fvar hty h1) (by simp)
      (by simp) h
  | @sort u e hu h1 =>
    intro k r h
    obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    exact rec_positivity_other_refines hg ht hlps (ExprWF.sort hu h1) (by simp)
      (by simp) h
  | @mk_const n us e hn hus h1 =>
    intro k r h
    obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    exact rec_positivity_other_refines hg ht hlps (ExprWF.mk_const hn hus h1)
      (by simp) (by simp) h
  | @app f a e hf ha h1 ihf iha =>
    intro k r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    exact rec_positivity_other_refines hg ht hlps (ExprWF.app hf ha h1) (by simp)
      (by simp) h
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    intro k r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    exact rec_positivity_other_refines hg ht hlps (ExprWF.lam hty hbo hm h1)
      (by simp) (by simp) h
  | @let_e ty vv bo e hty hvv hbo h1 ihty ihvv ihbo =>
    intro k r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    exact rec_positivity_other_refines hg ht hlps (ExprWF.let_e hty hvv hbo h1)
      (by simp) (by simp) h
  | @lit l e hl h1 =>
    intro k r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    exact rec_positivity_other_refines hg ht hlps (ExprWF.lit hl h1) (by simp)
      (by simp) h
  | @proj s i x e hs hx h1 ihx =>
    intro k r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    exact rec_positivity_other_refines hg ht hlps (ExprWF.proj hs hx h1) (by simp)
      (by simp) h
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    intro k r h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    rw [inductives.native_parts.rec_positivity] at h
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    simp only [absExpr_mk, absExprKind, recPositivity_forallE]
    obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
    have hb0abs := hg.mentions_const t ty b0 ht hty hb0
    split at h
    · rename_i hbt
      rw [hb0abs] at hbt
      rw [if_pos hbt, ← Result.ok_injective h]
      rfl
    · rename_i hbf
      rw [hb0abs] at hbf
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = k.val + 1 := HashMap.uscalar_add_eq hi1
      rw [if_neg hbf, ← hi1v]
      exact ihbo h

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
    (hcbs : ExprOps.BindersWF cbs) (hb : n_p.val + n_f.val ≤ Std.Usize.max)
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
  generalize hd : n_f.val - i.val = d
  induction d using Nat.strong_induction_on generalizing i out v with
  | _ d ih =>
    subst hd
    rw [inductives.native_parts.rec_ctor_kinds_at] at h
    split at h
    · rename_i hge
      rw [← Result.ok_injective h, show n_f.val - i.val = 0 by scalar_tac]
      simp
    · rename_i hnge
      have hin : i.val < n_f.val := by scalar_tac
      have hrange : List.range' i.val (n_f.val - i.val)
          = i.val :: List.range' (i.val + 1) (n_f.val - (i.val + 1)) := by
        rw [show n_f.val - i.val = (n_f.val - (i.val + 1)) + 1 by omega]; rfl
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = n_p.val + i.val := HashMap.uscalar_add_eq hi1
      obtain ⟨dom, hdom, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hdomabs, hdomwf⟩ :=
        binder_dom_get_d_refines hcbs (by rw [hi1v]; omega) hdom
      obtain ⟨k0, hk0, h⟩ := bind_eq_ok_iff.mp h
      have hk0abs := rec_field_kind_refines hg ht hlps hdomwf hk0
      obtain ⟨kk, hk, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hdomv : absExpr dom
          = ((ExprOps.absBinders cbs).getD (n_p.val + i.val) default).1 := by
        rw [hdomabs, hi1v]
      have hk0v : absRecFieldKind k0
          = ConLeche.recFieldKind (absName t) (absNames lps) n_p.val n_idx.val i.val
              ((ExprOps.absBinders cbs).getD (n_p.val + i.val) default).1 := by
        rw [hk0abs, hdomv]
      have hkv : absRecFieldKind kk
          = (match ConLeche.recFieldKind (absName t) (absNames lps) n_p.val n_idx.val
                i.val ((ExprOps.absBinders cbs).getD (n_p.val + i.val) default).1 with
             | .recursive =>
               if ConLeche.structUsedLater (absExpr cty) n_p.val i.val then .unsupported
               else .recursive
             | .reflexive =>
               if ConLeche.structUsedLater (absExpr cty) n_p.val i.val then .unsupported
               else .reflexive
             | other => other) := by
        rw [← hk0v]
        cases k0 with
        | Ordinary => rw [← Result.ok_injective hk]; rfl
        | Negative => rw [← Result.ok_injective hk]; rfl
        | Unsupported => rw [← Result.ok_injective hk]; rfl
        | Recursive =>
          obtain ⟨bu, hbu, hk⟩ := bind_eq_ok_iff.mp hk
          have hbuabs := hg.struct_used_later cty n_p i bu hcty hbu
          split at hk
          · rename_i hbt
            rw [hbuabs] at hbt
            rw [← Result.ok_injective hk]
            simp only [absRecFieldKind, hbt, if_true]
          · rename_i hbf
            rw [hbuabs] at hbf
            rw [← Result.ok_injective hk]
            simp only [absRecFieldKind, Bool.eq_false_iff.mpr hbf, Bool.false_eq_true,
              if_false]
        | Reflexive =>
          obtain ⟨bu, hbu, hk⟩ := bind_eq_ok_iff.mp hk
          have hbuabs := hg.struct_used_later cty n_p i bu hcty hbu
          split at hk
          · rename_i hbt
            rw [hbuabs] at hbt
            rw [← Result.ok_injective hk]
            simp only [absRecFieldKind, hbt, if_true]
          · rename_i hbf
            rw [hbuabs] at hbf
            rw [← Result.ok_injective hk]
            simp only [absRecFieldKind, Bool.eq_false_iff.mpr hbf, Bool.false_eq_true,
              if_false]
      have habsout1 : absRecFieldKinds out1
          = absRecFieldKinds out ++ [absRecFieldKind kk] := by
        rw [IndAbs.absRecFieldKinds, vec_push_val hout1]
        simp [IndAbs.absRecFieldKinds]
      have hrec := ih (n_f.val - i2.val) (by scalar_tac) h (by scalar_tac)
      rw [hi2v] at hrec
      rw [hrec, habsout1, hrange, List.map_cons, hkv]
      simp

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

/-- `recCtorKinds` declines a constructor whose type has no `nP + nF`-binder
`Π` tower. -/
theorem recCtorKinds_none {T : ConLeche.Name} {lps : List ConLeche.Name}
    {nP nIdx : Nat} {c : ConLeche.ConstantVal × Nat}
    (hs : c.1.type.stripPis (nP + c.2) = none) :
    ConLeche.recCtorKinds T lps nP nIdx c = none := by
  rw [ConLeche.recCtorKinds, hs]

/-- `recCtorKinds` at a constructor whose type reads: the per-field kinds, and
the residual's index guard that downgrades them all. -/
theorem recCtorKinds_some {T : ConLeche.Name} {lps : List ConLeche.Name}
    {nP nIdx : Nat} {c : ConLeche.ConstantVal × Nat}
    {cbs : List (ConLeche.Expr × ConLeche.BinderMeta)} {cbody : ConLeche.Expr}
    {ks : List ConLeche.RecFieldKind}
    (hs : c.1.type.stripPis (nP + c.2) = some (cbs, cbody))
    (hks : ks = (List.range c.2).map (fun i =>
        match ConLeche.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
        | .recursive =>
          if ConLeche.structUsedLater c.1.type nP i then .unsupported else .recursive
        | .reflexive =>
          if ConLeche.structUsedLater c.1.type nP i then .unsupported else .reflexive
        | other => other)) :
    ConLeche.recCtorKinds T lps nP nIdx c
      = (if (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsConst T) then some ks
         else some (ks.map fun _ => .negative)) := by
  subst hks
  rw [ConLeche.recCtorKinds, hs]
  rfl

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
  rw [inductives.native_parts.rec_ctor_kinds] at h
  obtain ⟨cv, nf⟩ := c
  simp only [lift_eq, bind_tc_ok] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = n_p.val + nf.val := HashMap.uscalar_add_eq hi1
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_pis_refines hc.2.2 ho1
  rw [hi1v] at ho1abs
  cases o1 with
  | none =>
    simp only [Option.map_none] at ho1abs
    rw [← Result.ok_injective h, recCtorKinds_none ho1abs.symm]
    rfl
  | some q =>
    obtain ⟨cbs, cbody⟩ := q
    obtain ⟨hcbswf, hcbodywf⟩ := ho1wf _ rfl
    simp only [Option.map_some] at ho1abs
    have hcbslen : (ExprOps.absBinders cbs).length = n_p.val + nf.val :=
      ConLeche.Expr.stripPis_length _ ho1abs.symm
    have hcbsvlen : cbs.val.length = n_p.val + nf.val := by
      rw [← hcbslen, ExprOps.absBinders, List.length_map]
    have hbound : n_p.val + nf.val ≤ Std.Usize.max := by
      rw [← hcbsvlen]; exact cbs.property
    obtain ⟨ks, hks, h⟩ := bind_eq_ok_iff.mp h
    have hksabs :=
      rec_ctor_kinds_at_refines hg ht hlps hc.2.2 hcbswf hbound hks
    have hksv : absRecFieldKinds ks
        = (List.range nf.val).map (fun i =>
            match ConLeche.recFieldKind (absName t) (absNames lps) n_p.val n_idx.val i
                ((ExprOps.absBinders cbs).getD (n_p.val + i) default).1 with
            | .recursive =>
              if ConLeche.structUsedLater (absExpr cv.ty) n_p.val i then .unsupported
              else .recursive
            | .reflexive =>
              if ConLeche.structUsedLater (absExpr cv.ty) n_p.val i then .unsupported
              else .reflexive
            | other => other) := by
      rw [hksabs]
      simp [IndAbs.absRecFieldKinds, alloc.vec.Vec.new,
        show ((0#u64 : Std.U64).val) = 0 from rfl, List.range_eq_range']
    obtain ⟨resid, hresid, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hresidabs, hresidwf⟩ := ExprOps.get_app_args_refines hcbodywf hresid
    have hnpcast : (Std.UScalar.cast .Usize n_p : Std.Usize).val = n_p.val :=
      ExprOps.u64_cast_usize_val (by omega)
    obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
    have hb0abs := args_free_of_from_refines hg ht hresidwf hb0
    rw [hnpcast, hresidabs] at hb0abs
    rw [recCtorKinds_some ho1abs.symm hksv]
    split at h
    · rename_i hbt
      rw [hb0abs] at hbt
      rw [if_pos hbt, ← Result.ok_injective h]
      rfl
    · rename_i hbf
      have hbf' : (((absExpr cbody).getAppArgs.drop n_p.val).all
          (fun a => !a.mentionsConst (absName t))) = true → False := by
        intro hc2; exact hbf (by rw [hb0abs]; exact hc2)
      obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
      have hv1abs := kinds_all_negative_refines hv1
      rw [if_neg hbf', ← Result.ok_injective h]
      simp only [Option.map_some, Option.some.injEq]
      rw [hv1abs]
      simp only [IndAbs.absRecFieldKinds]
      rw [List.map_const']
      simp [alloc.vec.Vec.new]

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
  revert out r
  induction he with
  | @bvar i e h1 =>
    intro out r hout h
    rw [inductives.native_parts.pi_binders_go] at h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨e1, he1, hr⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq he1, Result.ok.injEq] at hr
    subst hr
    exact ⟨by simp [ConLeche.Expr.piBinders], by simp [ConLeche.Expr.piBinders],
      hout, ExprWF.bvar h1⟩
  | @fvar idx ty e hty h1 ihty =>
    intro out r hout h
    rw [inductives.native_parts.pi_binders_go] at h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨e1, he1, hr⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq he1, Result.ok.injEq] at hr
    subst hr
    exact ⟨by simp [ConLeche.Expr.piBinders], by simp [ConLeche.Expr.piBinders],
      hout, ExprWF.fvar hty h1⟩
  | @sort u e hu h1 =>
    intro out r hout h
    rw [inductives.native_parts.pi_binders_go] at h
    obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨e1, he1, hr⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq he1, Result.ok.injEq] at hr
    subst hr
    exact ⟨by simp [ConLeche.Expr.piBinders], by simp [ConLeche.Expr.piBinders],
      hout, ExprWF.sort hu h1⟩
  | @mk_const n us e hn hus h1 =>
    intro out r hout h
    rw [inductives.native_parts.pi_binders_go] at h
    obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨e1, he1, hr⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq he1, Result.ok.injEq] at hr
    subst hr
    exact ⟨by simp [ConLeche.Expr.piBinders], by simp [ConLeche.Expr.piBinders],
      hout, ExprWF.mk_const hn hus h1⟩
  | @app f a e hf ha h1 ihf iha =>
    intro out r hout h
    rw [inductives.native_parts.pi_binders_go] at h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨e1, he1, hr⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq he1, Result.ok.injEq] at hr
    subst hr
    exact ⟨by simp [ConLeche.Expr.piBinders], by simp [ConLeche.Expr.piBinders],
      hout, ExprWF.app hf ha h1⟩
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    intro out r hout h
    rw [inductives.native_parts.pi_binders_go] at h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨e1, he1, hr⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq he1, Result.ok.injEq] at hr
    subst hr
    exact ⟨by simp [ConLeche.Expr.piBinders], by simp [ConLeche.Expr.piBinders],
      hout, ExprWF.lam hty hbo hm h1⟩
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    intro out r hout h
    rw [inductives.native_parts.pi_binders_go] at h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨out1, hpush, h⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq ht1, Expr.binder_meta_dup_eq hbm] at hpush
    obtain ⟨ha1, ha2, ha3, ha4⟩ :=
      ihbo (ExprOps.bindersWF_push hout hty hm hpush) h
    refine ⟨?_, ?_, ha3, ha4⟩
    · rw [ha1, ExprOps.absBinders_push hpush]
      simp [absExpr_mk, absExprKind, ConLeche.Expr.piBinders]
    · rw [ha2]
      simp [absExpr_mk, absExprKind, ConLeche.Expr.piBinders]
  | @let_e ty vv bo e hty hvv hbo h1 ihty ihvv ihbo =>
    intro out r hout h
    rw [inductives.native_parts.pi_binders_go] at h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨e1, he1, hr⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq he1, Result.ok.injEq] at hr
    subst hr
    exact ⟨by simp [ConLeche.Expr.piBinders], by simp [ConLeche.Expr.piBinders],
      hout, ExprWF.let_e hty hvv hbo h1⟩
  | @lit l e hl h1 =>
    intro out r hout h
    rw [inductives.native_parts.pi_binders_go] at h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨e1, he1, hr⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq he1, Result.ok.injEq] at hr
    subst hr
    exact ⟨by simp [ConLeche.Expr.piBinders], by simp [ConLeche.Expr.piBinders],
      hout, ExprWF.lit hl h1⟩
  | @proj s i x e hs hx h1 ihx =>
    intro out r hout h
    rw [inductives.native_parts.pi_binders_go] at h
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    obtain ⟨e1, he1, hr⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq he1, Result.ok.injEq] at hr
    subst hr
    exact ⟨by simp [ConLeche.Expr.piBinders], by simp [ConLeche.Expr.piBinders],
      hout, ExprWF.proj hs hx h1⟩

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

/-- `structFieldTeleOf` at a constructor type with no `nP + nF`-binder tower. -/
theorem structFieldTeleOf_none {cty : ConLeche.Expr} {nP nF i : Nat}
    (hs : cty.stripPis (nP + nF) = none) :
    ConLeche.structFieldTeleOf cty nP nF i = [] := by
  rw [ConLeche.structFieldTeleOf, hs]

/-- `structFieldTeleOf` at a constructor type whose tower reads. -/
theorem structFieldTeleOf_some {cty : ConLeche.Expr} {nP nF i : Nat}
    {cbs : List (ConLeche.Expr × ConLeche.BinderMeta)} {cbody : ConLeche.Expr}
    (hs : cty.stripPis (nP + nF) = some (cbs, cbody)) :
    ConLeche.structFieldTeleOf cty nP nF i
      = ((cbs.getD (nP + i) default).1.piBinders).1 := by
  rw [ConLeche.structFieldTeleOf, hs]

/-- `structFieldIdxOf` at a constructor type with no `nP + nF`-binder tower. -/
theorem structFieldIdxOf_none {cty : ConLeche.Expr} {nP nF i : Nat}
    (hs : cty.stripPis (nP + nF) = none) :
    ConLeche.structFieldIdxOf cty nP nF i = [] := by
  rw [ConLeche.structFieldIdxOf, hs]

/-- `structFieldIdxOf` at a constructor type whose tower reads. -/
theorem structFieldIdxOf_some {cty : ConLeche.Expr} {nP nF i : Nat}
    {cbs : List (ConLeche.Expr × ConLeche.BinderMeta)} {cbody : ConLeche.Expr}
    (hs : cty.stripPis (nP + nF) = some (cbs, cbody)) :
    ConLeche.structFieldIdxOf cty nP nF i
      = ((cbs.getD (nP + i) default).1.piBinders).2.getAppArgs.drop nP := by
  rw [ConLeche.structFieldIdxOf, hs]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:156-161` —
`struct_field_tele_of` refines `structFieldTeleOf`.

`i.val ≤ n_f.val` is the **platform** side condition of the header's note,
packaged at the reader: the port takes the domain with
`binder_dom_get_d(cbs, n_p + i)`, i.e. at `(n_p + i) as usize`, and the
telescope `strip_pis` peeled has exactly `n_p + n_f` binders, so the cast is
the identity exactly on the fields.  Every call site is a loop over the
constructor's `n_f` fields. -/
theorem struct_field_tele_of_refines {cty : expr.Expr} {n_p n_f i : Std.U64}
    {r : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} (hcty : ExprWF cty)
    (hi : i.val ≤ n_f.val)
    (h : inductives.native_parts.struct_field_tele_of cty n_p n_f i = ok r) :
    ExprOps.absBinders r
        = ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val i.val
      ∧ ExprOps.BindersWF r := by
  rw [inductives.native_parts.struct_field_tele_of] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hi1
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines hcty ho
  rw [hi1v] at hoabs
  cases o with
  | none =>
    simp only [Option.map_none] at hoabs
    rw [← Result.ok_injective h, structFieldTeleOf_none hoabs.symm]
    exact ⟨rfl, ExprOps.bindersWF_new⟩
  | some q =>
    obtain ⟨cbs, cbody⟩ := q
    obtain ⟨hcbswf, -⟩ := howf _ rfl
    simp only [Option.map_some] at hoabs
    rw [structFieldTeleOf_some hoabs.symm]
    have hcbslen : (ExprOps.absBinders cbs).length = n_p.val + n_f.val :=
      ConLeche.Expr.stripPis_length _ hoabs.symm
    have hcbsvlen : cbs.val.length = n_p.val + n_f.val := by
      rw [← hcbslen, ExprOps.absBinders, List.length_map]
    have hbound : n_p.val + n_f.val ≤ Std.Usize.max := by
      rw [← hcbsvlen]; exact cbs.property
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = n_p.val + i.val := HashMap.uscalar_add_eq hi2
    obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨heabs, hewf⟩ :=
      binder_dom_get_d_refines hcbswf (by rw [hi2v]; omega) he
    rw [hi2v] at heabs
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v1, vb⟩ := p
    obtain ⟨hp1, hp2, hp3, hp4⟩ := pi_binders_refines hewf hp
    rw [← Result.ok_injective h]
    exact ⟨by rw [hp1, heabs], hp3⟩

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:163-169` —
`struct_field_idx_of` refines `structFieldIdxOf`: the index expressions of
field `i`'s domain `Π a⃗, T p⃗ e⃗`, `[]` when the field is not of that shape.
`i.val ≤ n_f.val` is `struct_field_tele_of_refines`' side condition, for the
same reason. -/
theorem struct_field_idx_of_refines {cty : expr.Expr} {n_p n_f i : Std.U64}
    {r : alloc.vec.Vec expr.Expr} (hcty : ExprWF cty) (hi : i.val ≤ n_f.val)
    (h : inductives.native_parts.struct_field_idx_of cty n_p n_f i = ok r) :
    absExprs r = ConLeche.structFieldIdxOf (absExpr cty) n_p.val n_f.val i.val
      ∧ ExprsWF r := by
  rw [inductives.native_parts.struct_field_idx_of] at h
  simp only [lift_eq, bind_tc_ok] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hi1
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines hcty ho
  rw [hi1v] at hoabs
  cases o with
  | none =>
    simp only [Option.map_none] at hoabs
    rw [← Result.ok_injective h, structFieldIdxOf_none hoabs.symm]
    exact ⟨rfl, ExprOps.exprsWF_new⟩
  | some q =>
    obtain ⟨cbs, cbody⟩ := q
    obtain ⟨hcbswf, -⟩ := howf _ rfl
    simp only [Option.map_some] at hoabs
    rw [structFieldIdxOf_some hoabs.symm]
    have hcbslen : (ExprOps.absBinders cbs).length = n_p.val + n_f.val :=
      ConLeche.Expr.stripPis_length _ hoabs.symm
    have hcbsvlen : cbs.val.length = n_p.val + n_f.val := by
      rw [← hcbslen, ExprOps.absBinders, List.length_map]
    have hbound : n_p.val + n_f.val ≤ Std.Usize.max := by
      rw [← hcbsvlen]; exact cbs.property
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = n_p.val + i.val := HashMap.uscalar_add_eq hi2
    obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨heabs, hewf⟩ :=
      binder_dom_get_d_refines hcbswf (by rw [hi2v]; omega) he
    rw [hi2v] at heabs
    obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v1, vb⟩ := p
    obtain ⟨hp1, hp2, hp3, hp4⟩ := pi_binders_refines hewf hp
    obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hargsabs, hargswf⟩ := ExprOps.get_app_args_refines hp4 hargs
    have hnpcast : (Std.UScalar.cast .Usize n_p : Std.Usize).val = n_p.val :=
      ExprOps.u64_cast_usize_val (by omega)
    obtain ⟨hdabs, hdwf⟩ := CoreK.drop_exprs_refines hargswf h
    exact ⟨by rw [hdabs, hnpcast, hargsabs, hp2, heabs], hdwf⟩

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
    (hcty : ExprWF cty) (hi : i.val ≤ n_f.val)
    (h : inductives.native_parts.struct_ih_app rec_c rlvls pw n_p n n_f i cty
        = ok r) :
    absExpr r = ConLeche.structIhApp (absName rec_c) (absLevels rlvls)
        (absPropWhen pw) n_p.val n.val n_f.val i.val
        (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val i.val)
        (ConLeche.structFieldIdxOf (absExpr cty) n_p.val n_f.val i.val)
      ∧ ExprWF r := by
  rw [inductives.native_parts.struct_ih_app] at h
  rw [ConLeche.structIhApp]
  simp only [lift_eq, name_dup_eq, bind_tc_ok] at h
  obtain ⟨tele, htele, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hteleabs, htelewf⟩ := struct_field_tele_of_refines hcty hi htele
  obtain ⟨idx, hidx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hidxabs, hidxwf⟩ := struct_field_idx_of_refines hcty hi hidx
  have hM : (Std.UScalar.cast .U64 (alloc.vec.Vec.len tele) : Std.U64).val
      = (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val i.val).length := by
    rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val, ← hteleabs,
      ExprOps.absBinders, List.length_map]
  obtain ⟨lv, hlv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
  have hheadabs : absExpr head = .const (absName rec_c) (absLevels rlvls) := by
    rw [Expr.mk_const_refines hhead, Env.levels_copy_refines hlv]
  have hheadwf : ExprWF head :=
    ExprWF.mk_const hrec (by rw [Env.levels_copy_refines hlv]; exact hrlvls) hhead
  obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hargsabs, hargswf⟩ := struct_rec_prefix_at_refines hg hargs
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  have hi2v : i2.val = n.val + 1 := HashMap.uscalar_add_eq hi2
  obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hv1abs, hv1wf⟩ :=
    struct_idx_at_all_refines hidxwf ExprOps.exprsWF_new hv1
  obtain ⟨args1, hargs1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hargs1abs, hargs1wf⟩ := CoreK.append_exprs_refines hargswf hv1wf hargs1
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
  have hi3v : i3.val = 1 + i.val := HashMap.uscalar_add_eq hi3
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
  have hi4v : i4.val = n_f.val - (1 + i.val) := by
    rw [ExprOps.sub_nat_val_trunc hi4, hi3v]
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
  have hi5v : i5.val = n_f.val - 1 - i.val
      + (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val i.val).length := by
    rw [HashMap.uscalar_add_eq hi5, hi4v, hM]; omega
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v2, hv2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hv2abs, hv2wf⟩ := struct_tele_vars_refines hg hv2
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨he1abs, he1wf⟩ := ExprOps.mk_app_n_refines (Expr.bvar_wf he) hv2wf he1
  obtain ⟨args2, hargs2, h⟩ := bind_eq_ok_iff.mp h
  have hargs2wf : ExprsWF args2 := by
    intro x hx
    rw [vec_push_val hargs2] at hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hargs1wf x hx'
    · simp only [List.mem_singleton] at hx'; subst hx'; exact he1wf
  have hargs2abs : absExprs args2 = absExprs args1 ++ [absExpr e1] := by
    rw [absExprs, vec_push_val hargs2]; simp [absExprs]
  obtain ⟨v3, hv3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hv3abs, hv3wf⟩ := struct_tele_at_refines hpw htelewf hv3
  obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨he2abs, he2wf⟩ := ExprOps.mk_app_n_refines hheadwf hargs2wf he2
  obtain ⟨hrabs, hrwf⟩ := mk_lams_of_refines hv3wf he2wf h
  refine ⟨?_, hrwf⟩
  rw [hrabs, hv3abs, he2abs, hheadabs, hargs2abs, hargs1abs, hargsabs, hv1abs,
    he1abs, hv2abs, Expr.bvar_refines he, hi5v, hidxabs, hteleabs, hi2v, hM,
    show ((0#u64 : Std.U64).val) = 0 from rfl,
    show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero]
  simp [absExprs, alloc.vec.Vec.new]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:279-288` — `struct_ih_apps`
is `recIdx.map fun i => structIhApp …` from `k` on, at the monomorphised
readers. -/
theorem struct_ih_apps_refines (hg : StructGens) {rec_c : name.Name}
    {rlvls : alloc.vec.Vec level.Level} {pw : prop_when.PropWhen}
    {n_p n n_f : Std.U64} {rec_idx : alloc.vec.Vec Std.U64} {cty : expr.Expr}
    {k : Std.Usize} {out v : alloc.vec.Vec expr.Expr}
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls) (hpw : PropWhenWF pw)
    (hcty : ExprWF cty) (hridx : ∀ x ∈ rec_idx.val, x.val ≤ n_f.val)
    (hout : ExprsWF out)
    (h : inductives.native_parts.struct_ih_apps rec_c rlvls pw n_p n n_f rec_idx
        cty k out = ok v) :
    absExprs v = absExprs out ++
        ((absU64s rec_idx).drop k.val).map (fun i =>
          ConLeche.structIhApp (absName rec_c) (absLevels rlvls) (absPropWhen pw)
            n_p.val n.val n_f.val i
            (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val i)
            (ConLeche.structFieldIdxOf (absExpr cty) n_p.val n_f.val i))
      ∧ ExprsWF v := by
  generalize hd : rec_idx.length - k.val = d
  induction d using Nat.strong_induction_on generalizing k out v with
  | _ d ih =>
    rw [inductives.native_parts.struct_ih_apps] at h
    have hlv := alloc.vec.Vec.len_val rec_idx
    split at h
    · rename_i hge
      have hnil : (absU64s rec_idx).drop k.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absU64s, List.length_map]; scalar_tac
      rw [← Result.ok_injective h, hnil]
      exact ⟨by simp, hout⟩
    · rename_i hlt
      have hIk : k.val < rec_idx.val.length := by scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rec_idx k hIk)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨heabs, hewf⟩ := struct_ih_app_refines hg hrec hrlvls hpw hcty
        (hridx _ (List.getElem_mem hIk)) he
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hi2v : i2.val = k.val + 1 := HashMap.uscalar_add_eq hi2
      have hout1wf : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hout1] at hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hout x hx'
        · simp only [List.mem_singleton] at hx'; subst hx'; exact hewf
      have habsout1 : absExprs out1 = absExprs out ++ [absExpr e] := by
        rw [absExprs, vec_push_val hout1]; simp [absExprs]
      obtain ⟨hrec1, hrecwf⟩ :=
        ih (rec_idx.length - i2.val) (by scalar_tac) hout1wf h (by scalar_tac)
      refine ⟨?_, hrecwf⟩
      rw [hrec1, hi2v, habsout1]
      have hcons : (absU64s rec_idx).drop k.val
          = rec_idx.val[k.val].val :: (absU64s rec_idx).drop (k.val + 1) := by
        rw [List.drop_eq_getElem_cons
          (show k.val < (absU64s rec_idx).length by
            simpa [absU64s] using hIk)]
        congr 1
        simp [absU64s]
      rw [hcons, List.map_cons, heabs]
      simp

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:279-288` —
`struct_rule_body_r` refines `structRuleBodyR`: minor `j` at the fields, then
at the inductive hypotheses of the recursive fields.  `sub_nat (nF + n) (1 + j)`
is the cited `nF + n - 1 - j`. -/
theorem struct_rule_body_r_refines (hg : StructGens) {rec_c : name.Name}
    {rlvls : alloc.vec.Vec level.Level} {pw : prop_when.PropWhen}
    {n_p n n_f j : Std.U64} {rec_idx : alloc.vec.Vec Std.U64} {cty r : expr.Expr}
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls) (hpw : PropWhenWF pw)
    (hcty : ExprWF cty) (hridx : ∀ x ∈ rec_idx.val, x.val ≤ n_f.val)
    (h : inductives.native_parts.struct_rule_body_r rec_c rlvls pw n_p n n_f j
        rec_idx cty = ok r) :
    absExpr r = ConLeche.structRuleBodyR (absName rec_c) (absLevels rlvls)
        (absPropWhen pw) n_p.val n.val n_f.val j.val (absU64s rec_idx)
        (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val)
        (ConLeche.structFieldIdxOf (absExpr cty) n_p.val n_f.val)
      ∧ ExprWF r := by
  rw [inductives.native_parts.struct_rule_body_r] at h
  rw [ConLeche.structRuleBodyR]
  obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hargsabs, hargswf⟩ := struct_tele_vars_refines hg hargs
  obtain ⟨args1, hargs1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hargs1abs, hargs1wf⟩ :=
    struct_ih_apps_refines hg hrec hrlvls hpw hcty hridx hargswf hargs1
  obtain ⟨i0, hi0, h⟩ := bind_eq_ok_iff.mp h
  have hi0v : i0.val = n_f.val + n.val := HashMap.uscalar_add_eq hi0
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = 1 + j.val := HashMap.uscalar_add_eq hi1
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  have hi2v : i2.val = n_f.val + n.val - 1 - j.val := by
    rw [ExprOps.sub_nat_val_trunc hi2, hi0v, hi1v]; omega
  obtain ⟨e0, he0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := ExprOps.mk_app_n_refines (Expr.bvar_wf he0) hargs1wf h
  refine ⟨?_, hwf⟩
  rw [habs, Expr.bvar_refines he0, hi2v, hargs1abs, hargsabs,
    show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero,
    ConLeche.structTeleVars]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:290-305` — `struct_ih_pis`
refines `structIhPis` on the recursive positions from `k` on, `l` `ih` binders
already emitted.  `sub_nat nF (1 + i) + l + m` and `sub_nat (nF + o) 1 + l + m`
are the cited `nF - 1 - i + l + m` and `nF + o - 1 + l + m`. -/
theorem struct_ih_pis_refines (hg : StructGens) {n_f o : Std.U64} {pw : prop_when.PropWhen}
    {cty : expr.Expr} {n_p : Std.U64} {rec_idx : alloc.vec.Vec Std.U64}
    {k : Std.Usize} {l : Std.U64} {body r : expr.Expr}
    (hpw : PropWhenWF pw) (hcty : ExprWF cty) (hbody : ExprWF body)
    (hridx : ∀ x ∈ rec_idx.val, x.val ≤ n_f.val)
    (h : inductives.native_parts.struct_ih_pis n_f o pw cty n_p rec_idx k l body
        = ok r) :
    absExpr r = ConLeche.structIhPis n_f.val o.val (absPropWhen pw)
        (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val)
        (ConLeche.structFieldIdxOf (absExpr cty) n_p.val n_f.val)
        ((absU64s rec_idx).drop k.val) l.val (absExpr body)
      ∧ ExprWF r := by
  generalize hd : rec_idx.length - k.val = d
  induction d using Nat.strong_induction_on generalizing k l r with
  | _ d ih =>
    rw [inductives.native_parts.struct_ih_pis] at h
    have hlv := alloc.vec.Vec.len_val rec_idx
    split at h
    · rename_i hge
      have hnil : (absU64s rec_idx).drop k.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absU64s, List.length_map]; scalar_tac
      rw [← Result.ok_injective h, hnil]
      exact ⟨rfl, hbody⟩
    · rename_i hlt
      have hIk : k.val < rec_idx.val.length := by scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rec_idx k hIk)
      subst hyv
      have hcons : (absU64s rec_idx).drop k.val
          = rec_idx.val[k.val].val :: (absU64s rec_idx).drop (k.val + 1) := by
        rw [List.drop_eq_getElem_cons
          (show k.val < (absU64s rec_idx).length by simpa [absU64s] using hIk)]
        congr 1
        simp [absU64s]
      rw [hcons, ConLeche.structIhPis]
      simp only [alloc.vec.Vec.index_slice_index, hy, lift_eq, bind_tc_ok] at h
      obtain ⟨tele, htele, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hteleabs, htelewf⟩ :=
        struct_field_tele_of_refines hcty (hridx _ (List.getElem_mem hIk)) htele
      obtain ⟨idx, hidx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hidxabs, hidxwf⟩ :=
        struct_field_idx_of_refines hcty (hridx _ (List.getElem_mem hIk)) hidx
      have hM : (Std.UScalar.cast .U64 (alloc.vec.Vec.len tele) : Std.U64).val
          = (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val
              rec_idx.val[k.val].val).length := by
        rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val, ← hteleabs,
          ExprOps.absBinders, List.length_map]
      obtain ⟨margs, hmargs, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hmargsabs, hmargswf⟩ :=
        struct_idx_at_all_refines hidxwf ExprOps.exprsWF_new hmargs
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      have hi3v : i3.val = 1 + rec_idx.val[k.val].val := HashMap.uscalar_add_eq hi3
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
      have hi4v : i4.val = n_f.val - (1 + rec_idx.val[k.val].val) := by
        rw [ExprOps.sub_nat_val_trunc hi4, hi3v]
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
      have hi5v : i5.val = n_f.val - (1 + rec_idx.val[k.val].val) + l.val := by
        rw [HashMap.uscalar_add_eq hi5, hi4v]
      obtain ⟨i6, hi6, h⟩ := bind_eq_ok_iff.mp h
      have hi6v : i6.val = n_f.val - 1 - rec_idx.val[k.val].val + l.val
          + (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val
              rec_idx.val[k.val].val).length := by
        rw [HashMap.uscalar_add_eq hi6, hi5v, hM]; omega
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hvabs, hvwf⟩ := struct_tele_vars_refines hg hv
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨he1abs, he1wf⟩ := ExprOps.mk_app_n_refines (Expr.bvar_wf he) hvwf he1
      obtain ⟨margs1, hmargs1, h⟩ := bind_eq_ok_iff.mp h
      have hmargs1wf : ExprsWF margs1 := by
        intro x hx
        rw [vec_push_val hmargs1] at hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hmargswf x hx'
        · simp only [List.mem_singleton] at hx'; subst hx'; exact he1wf
      have hmargs1abs : absExprs margs1 = absExprs margs ++ [absExpr e1] := by
        rw [absExprs, vec_push_val hmargs1]; simp [absExprs]
      obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hv1abs, hv1wf⟩ := struct_tele_at_refines hpw htelewf hv1
      obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
      have hi7v : i7.val = n_f.val + o.val := HashMap.uscalar_add_eq hi7
      obtain ⟨i8, hi8, h⟩ := bind_eq_ok_iff.mp h
      have hi8v : i8.val = n_f.val + o.val - 1 := by
        rw [ExprOps.sub_nat_val_trunc hi8, hi7v]; rfl
      obtain ⟨i9, hi9, h⟩ := bind_eq_ok_iff.mp h
      have hi9v : i9.val = n_f.val + o.val - 1 + l.val := by
        rw [HashMap.uscalar_add_eq hi9, hi8v]
      obtain ⟨i10, hi10, h⟩ := bind_eq_ok_iff.mp h
      have hi10v : i10.val = n_f.val + o.val - 1 + l.val
          + (ConLeche.structFieldTeleOf (absExpr cty) n_p.val n_f.val
              rec_idx.val[k.val].val).length := by
        rw [HashMap.uscalar_add_eq hi10, hi9v, hM]
      obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e3, he3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨he3abs, he3wf⟩ :=
        ExprOps.mk_app_n_refines (Expr.bvar_wf he2) hmargs1wf he3
      obtain ⟨dom, hdom, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hdomabs, hdomwf⟩ := mk_pis_of_refines hv1wf he3wf hdom
      obtain ⟨i11, hi11, h⟩ := bind_eq_ok_iff.mp h
      have hi11v : i11.val = k.val + 1 := HashMap.uscalar_add_eq hi11
      obtain ⟨i12, hi12, h⟩ := bind_eq_ok_iff.mp h
      have hi12v : i12.val = l.val + 1 := HashMap.uscalar_add_eq hi12
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hrestabs, hrestwf⟩ :=
        ih (rec_idx.length - i11.val) (by scalar_tac) hrest (by scalar_tac)
      rw [hi11v, hi12v] at hrestabs
      obtain ⟨pw1, hpw1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
      rw [PropWhen.dup_eq hpw1, ExprOps.binder_meta_eq, Result.ok.injEq] at hbm
      subst hbm
      refine ⟨?_, Expr.forall_e_wf hdomwf hrestwf hpw h⟩
      rw [Expr.forall_e_refines h, hrestabs, hdomabs, hv1abs, he3abs,
        Expr.bvar_refines he2, hi10v, hmargs1abs, hmargsabs, he1abs, hvabs,
        Expr.bvar_refines he, hi6v, hidxabs, hteleabs, hM,
        show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero]
      simp [absExprs, alloc.vec.Vec.new, absBinderMeta]

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
    (hridx : ∀ x ∈ rec_idx.val, x.val ≤ n_f.val)
    (h : inductives.native_parts.struct_minor_ty_r c lps n_p n_f o pw cty rec_idx
        = ok r) :
    r.map absExpr = ConLeche.structMinorTyR (absName c) (absNames lps) n_p.val
        n_f.val o.val (absPropWhen pw) (absExpr cty) (absU64s rec_idx)
      ∧ ∀ x, r = some x → ExprWF x := by
  rw [inductives.native_parts.struct_minor_ty_r] at h
  rw [ConLeche.structMinorTyR]
  simp only [lift_eq, bind_tc_ok] at h
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_pis_refines hcty ho1
  cases o1 with
  | none =>
    simp only [Option.map_none] at ho1abs
    rw [← Result.ok_injective h, ← ho1abs]
    exact ⟨rfl, by simp⟩
  | some q =>
    obtain ⟨qbs, qe⟩ := q
    obtain ⟨hqbswf, hqewf⟩ := ho1wf _ rfl
    simp only [Option.map_some] at ho1abs
    rw [← ho1abs]
    simp only [Option.bind]
    have hqlen : (ExprOps.absBinders qbs).length = n_p.val :=
      ConLeche.Expr.stripPis_length _ ho1abs.symm
    have hqvlen : qbs.val.length = n_p.val := by
      rw [← hqlen, ExprOps.absBinders, List.length_map]
    have hnpb : n_p.val ≤ Std.Usize.max := by rw [← hqvlen]; exact qbs.property
    obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho2abs, ho2wf⟩ := ExprOps.strip_pis_refines hqewf ho2
    cases o2 with
    | none =>
      simp only [Option.map_none] at ho2abs
      rw [← Result.ok_injective h, ← ho2abs]
      exact ⟨rfl, by simp⟩
    | some rr =>
      obtain ⟨rbs, re⟩ := rr
      obtain ⟨hrbswf, hrewf⟩ := ho2wf _ rfl
      simp only [Option.map_some] at ho2abs
      rw [← ho2abs]
      obtain ⟨resid, hresid, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hresidabs, hresidwf⟩ := ExprOps.get_app_args_refines hrewf hresid
      have hnpcast : (Std.UScalar.cast .Usize n_p : Std.Usize).val = n_p.val :=
        ExprOps.u64_cast_usize_val hnpb
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hvabs, hvwf⟩ := CoreK.drop_exprs_refines hresidwf hv
      obtain ⟨idxs, hidxs, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hidxsabs, hidxswf⟩ := lift_all_refines hvwf ExprOps.exprsWF_new hidxs
      obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨he2abs, he2wf⟩ := struct_ctor_spine_at_o_refines hg hc hlps he2
      obtain ⟨idxs1, hidxs1, h⟩ := bind_eq_ok_iff.mp h
      have hidxs1wf : ExprsWF idxs1 := by
        intro x hx
        rw [vec_push_val hidxs1] at hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hidxswf x hx'
        · simp only [List.mem_singleton] at hx'; subst hx'; exact he2wf
      have hidxs1abs : absExprs idxs1 = absExprs idxs ++ [absExpr e2] := by
        rw [absExprs, vec_push_val hidxs1]; simp [absExprs]
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      have hi3v : i3.val = n_f.val + o.val := HashMap.uscalar_add_eq hi3
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
      have hi4v : i4.val = n_f.val + o.val - 1 := by
        rw [ExprOps.sub_nat_val_trunc hi4, hi3v]; rfl
      obtain ⟨e3, he3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e4, he4, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨he4abs, he4wf⟩ :=
        ExprOps.mk_app_n_refines (Expr.bvar_wf he3) hidxs1wf he4
      have hclen : (Std.UScalar.cast .U64 (alloc.vec.Vec.len rec_idx) : Std.U64).val
          = (absU64s rec_idx).length := by
        rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val, absU64s,
          List.length_map]
      obtain ⟨concl, hconcl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hconclabs, hconclwf⟩ :=
        ExprOps.lift_loose_bvars_refines he4wf hconcl
      obtain ⟨inner, hinner, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hinnerabs, hinnerwf⟩ :=
        struct_ih_pis_refines hg hpw hcty hconclwf hridx hinner
      obtain ⟨lifted, hlifted, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hliftedabs, hliftedwf⟩ :=
        ExprOps.lift_loose_bvars_refines hqewf hlifted
      obtain ⟨hrabs, hrwf⟩ := hg.replace_pis_pw pw n_f lifted inner r hpw hliftedwf
        hinnerwf h
      refine ⟨?_, hrwf⟩
      rw [hrabs, hliftedabs, hinnerabs, hconclabs, he4abs,
        Expr.bvar_refines he3, hi4v, hidxs1abs, hidxsabs, he2abs, hvabs, hnpcast,
        hresidabs, hclen,
        show ((0#u64 : Std.U64).val) = 0 from rfl,
        show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero]
      simp [absExprs, alloc.vec.Vec.new]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:322-330` —
`struct_minors_pis_r` refines `structMinorsPisR` on the constructors from `k`
on, the cited extras count `o` growing by one per minor. -/
theorem struct_minors_pis_r_refines (hg : StructGens) {lps : alloc.vec.Vec name.Name}
    {n_p : Std.U64} {pw : prop_when.PropWhen}
    {ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    {k : Std.Usize} {o : Std.U64} {body : expr.Expr} {r : Option expr.Expr}
    (hlps : NamesWF lps) (hpw : PropWhenWF pw) (hctors : Ctors4WF ctors)
    (hridx : ∀ c ∈ ctors.val, ∀ x ∈ c.2.2.2.val, x.val ≤ c.2.1.val)
    (hbody : ExprWF body)
    (h : inductives.native_parts.struct_minors_pis_r lps n_p pw ctors k o body
        = ok r) :
    r.map absExpr = ConLeche.structMinorsPisR (absNames lps) n_p.val
        (absPropWhen pw) ((absCtors4 ctors).drop k.val) o.val (absExpr body)
      ∧ ∀ x, r = some x → ExprWF x := by
  generalize hd : ctors.length - k.val = d
  induction d using Nat.strong_induction_on generalizing k o r with
  | _ d ih =>
    rw [inductives.native_parts.struct_minors_pis_r] at h
    have hlv := alloc.vec.Vec.len_val ctors
    split at h
    · rename_i hge
      have hnil : (absCtors4 ctors).drop k.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absCtors4, List.length_map]; scalar_tac
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      rw [Expr.dup_eq he] at h
      rw [← Result.ok_injective h, hnil]
      exact ⟨rfl, by intro x hx; rw [← Option.some.inj hx]; exact hbody⟩
    · rename_i hlt
      have hIk : k.val < ctors.val.length := by scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ctors k hIk)
      subst hyv
      rcases hsp : ctors.val[k.val] with ⟨cn, cnf, ccty, cridx⟩
      have hcwf := hctors _ (List.getElem_mem hIk)
      rw [hsp] at hcwf
      have hcridx : ∀ x ∈ cridx.val, x.val ≤ cnf.val := by
        have := hridx _ (List.getElem_mem hIk)
        rw [hsp] at this; exact this
      have hcons : (absCtors4 ctors).drop k.val
          = (absName cn, cnf.val, absExpr ccty, absU64s cridx)
            :: (absCtors4 ctors).drop (k.val + 1) := by
        rw [List.drop_eq_getElem_cons
          (show k.val < (absCtors4 ctors).length by simpa [absCtors4] using hIk)]
        congr 1
        simp [absCtors4, hsp]
      rw [hcons, ConLeche.structMinorsPisR]
      simp only [alloc.vec.Vec.index_slice_index, hy, hsp, bind_tc_ok] at h
      obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ho1abs, ho1wf⟩ :=
        struct_minor_ty_r_refines hg hcwf.1 hlps hpw hcwf.2 hcridx ho1
      cases o1 with
      | none =>
        simp only [Option.map_none] at ho1abs
        rw [← Result.ok_injective h, ← ho1abs]
        exact ⟨rfl, by simp⟩
      | some mty =>
        simp only [Option.map_some] at ho1abs
        rw [← ho1abs]
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = k.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hi3v : i3.val = o.val + 1 := HashMap.uscalar_add_eq hi3
        obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ho2abs, ho2wf⟩ :=
          ih (ctors.length - i2.val) (by scalar_tac) ho2 (by scalar_tac)
        rw [hi2v, hi3v] at ho2abs
        cases o2 with
        | none =>
          simp only [Option.map_none] at ho2abs
          rw [← Result.ok_injective h, ← ho2abs]
          exact ⟨rfl, by simp⟩
        | some rest =>
          simp only [Option.map_some] at ho2abs
          rw [← ho2abs]
          obtain ⟨pw1, hpw1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
          rw [PropWhen.dup_eq hpw1, ExprOps.binder_meta_eq, Result.ok.injEq] at hbm
          subst hbm
          obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
          rw [← Result.ok_injective h]
          refine ⟨?_, ?_⟩
          · simp only [Option.map_some, Expr.forall_e_refines he1]
            simp [absBinderMeta]
          · intro x hx
            rw [← Option.some.inj hx]
            exact Expr.forall_e_wf (ho1wf _ rfl) (ho2wf _ rfl) hpw he1

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:332-339` —
`struct_minors_lams_r` refines `structMinorsLamsR`, the `λ` twin. -/
theorem struct_minors_lams_r_refines (hg : StructGens) {lps : alloc.vec.Vec name.Name}
    {n_p : Std.U64} {pw : prop_when.PropWhen}
    {ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    {k : Std.Usize} {o : Std.U64} {body : expr.Expr} {r : Option expr.Expr}
    (hlps : NamesWF lps) (hpw : PropWhenWF pw) (hctors : Ctors4WF ctors)
    (hridx : ∀ c ∈ ctors.val, ∀ x ∈ c.2.2.2.val, x.val ≤ c.2.1.val)
    (hbody : ExprWF body)
    (h : inductives.native_parts.struct_minors_lams_r lps n_p pw ctors k o body
        = ok r) :
    r.map absExpr = ConLeche.structMinorsLamsR (absNames lps) n_p.val
        (absPropWhen pw) ((absCtors4 ctors).drop k.val) o.val (absExpr body)
      ∧ ∀ x, r = some x → ExprWF x := by
  generalize hd : ctors.length - k.val = d
  induction d using Nat.strong_induction_on generalizing k o r with
  | _ d ih =>
    rw [inductives.native_parts.struct_minors_lams_r] at h
    have hlv := alloc.vec.Vec.len_val ctors
    split at h
    · rename_i hge
      have hnil : (absCtors4 ctors).drop k.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absCtors4, List.length_map]; scalar_tac
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      rw [Expr.dup_eq he] at h
      rw [← Result.ok_injective h, hnil]
      exact ⟨rfl, by intro x hx; rw [← Option.some.inj hx]; exact hbody⟩
    · rename_i hlt
      have hIk : k.val < ctors.val.length := by scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ctors k hIk)
      subst hyv
      rcases hsp : ctors.val[k.val] with ⟨cn, cnf, ccty, cridx⟩
      have hcwf := hctors _ (List.getElem_mem hIk)
      rw [hsp] at hcwf
      have hcridx : ∀ x ∈ cridx.val, x.val ≤ cnf.val := by
        have := hridx _ (List.getElem_mem hIk)
        rw [hsp] at this; exact this
      have hcons : (absCtors4 ctors).drop k.val
          = (absName cn, cnf.val, absExpr ccty, absU64s cridx)
            :: (absCtors4 ctors).drop (k.val + 1) := by
        rw [List.drop_eq_getElem_cons
          (show k.val < (absCtors4 ctors).length by simpa [absCtors4] using hIk)]
        congr 1
        simp [absCtors4, hsp]
      rw [hcons, ConLeche.structMinorsLamsR]
      simp only [alloc.vec.Vec.index_slice_index, hy, hsp, bind_tc_ok] at h
      obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ho1abs, ho1wf⟩ :=
        struct_minor_ty_r_refines hg hcwf.1 hlps hpw hcwf.2 hcridx ho1
      cases o1 with
      | none =>
        simp only [Option.map_none] at ho1abs
        rw [← Result.ok_injective h, ← ho1abs]
        exact ⟨rfl, by simp⟩
      | some mty =>
        simp only [Option.map_some] at ho1abs
        rw [← ho1abs]
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = k.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hi3v : i3.val = o.val + 1 := HashMap.uscalar_add_eq hi3
        obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ho2abs, ho2wf⟩ :=
          ih (ctors.length - i2.val) (by scalar_tac) ho2 (by scalar_tac)
        rw [hi2v, hi3v] at ho2abs
        cases o2 with
        | none =>
          simp only [Option.map_none] at ho2abs
          rw [← Result.ok_injective h, ← ho2abs]
          exact ⟨rfl, by simp⟩
        | some rest =>
          simp only [Option.map_some] at ho2abs
          rw [← ho2abs]
          obtain ⟨pw1, hpw1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
          rw [PropWhen.dup_eq hpw1, ExprOps.binder_meta_eq, Result.ok.injEq] at hbm
          subst hbm
          obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
          rw [← Result.ok_injective h]
          refine ⟨?_, ?_⟩
          · simp only [Option.map_some, Expr.lam_refines he1]
            simp [absBinderMeta]
          · intro x hx
            rw [← Option.some.inj hx]
            exact Expr.lam_wf (ho1wf _ rfl) (ho2wf _ rfl) hpw he1

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
/-- `ConLeche/Kernel/Inductives/NativeParts.lean:341-362` — `struct_rec_ty_r`
refines `structRecTyR`: **the generated recursor type at a recursive block**,
the term `checkNativeRec` `isDefEq`s against the stream's.

`hcpos` is `IndNativeInstall.RecPosWF ctors` spelled out — the header's
platform side condition, per constructor: `struct_minors_pis_r` reads each
constructor's field telescope at `(n_p + i) as usize` for every recorded
recursive position `i`, and the cast is the identity exactly on the field
indices.  The install carries it from `check_native_tail_guards`'
`native_fields_ok` through `native_ctors4`. -/
theorem struct_rec_ty_r_refines (hg : StructGens) {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {elim : name.Name} {large : Bool} {n_p n_idx : Std.U64} {tty : expr.Expr}
    {ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    {r : Option expr.Expr}
    (ht : NameWF t) (hlps : NamesWF lps) (helim : NameWF elim) (htty : ExprWF tty)
    (hctors : Ctors4WF ctors)
    (hcpos : ∀ c ∈ ctors.val, ∀ x ∈ c.2.2.2.val, x.val ≤ c.2.1.val)
    (h : inductives.native_parts.struct_rec_ty_r t lps elim large n_p n_idx tty
        ctors = ok r) :
    r.map absExpr = ConLeche.structRecTyR (absName t) (absNames lps) (absName elim)
        large n_p.val n_idx.val (absExpr tty) (absCtors4 ctors)
      ∧ ∀ x, r = some x → ExprWF x := by
  rw [inductives.native_parts.struct_rec_ty_r] at h
  rw [ConLeche.structRecTyR]
  simp only [lift_eq, bind_tc_ok] at h
  obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlabs, hlwf⟩ := hg.struct_elim_level elim large l helim hl
  obtain ⟨pw, hpw, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpwabs, hpwwf⟩ := ExprOps.zeroness_of_refines hlwf pw hpw
  have hn : (Std.UScalar.cast .U64 (alloc.vec.Vec.len ctors) : Std.U64).val
      = (absCtors4 ctors).length := by
    rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val, absCtors4,
      List.length_map]
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines htty ho
  cases o with
  | none =>
    simp only [Option.map_none] at hoabs
    rw [← Result.ok_injective h, ← hoabs]
    exact ⟨rfl, by simp⟩
  | some q =>
    obtain ⟨qbs, qe⟩ := q
    obtain ⟨hqbswf, hqewf⟩ := howf _ rfl
    simp only [Option.map_some] at hoabs
    rw [← hoabs]
    simp only [Option.bind]
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho1abs, ho1wf⟩ :=
      hg.struct_motive_ty_i t lps n_p n_idx l qe o1 ht hlps hlwf hqewf ho1
    rw [hlabs] at ho1abs
    cases o1 with
    | none =>
      simp only [Option.map_none] at ho1abs
      rw [← Result.ok_injective h, ← ho1abs]
      exact ⟨rfl, by simp⟩
    | some motive_ty =>
      simp only [Option.map_some] at ho1abs
      rw [← ho1abs]
      obtain ⟨margs, hmargs, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hmargsabs, hmargswf⟩ := hg.struct_ps_at 1#u64 n_idx margs hmargs
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨margs1, hmargs1, h⟩ := bind_eq_ok_iff.mp h
      have hmargs1wf : ExprsWF margs1 := by
        intro x hx
        rw [vec_push_val hmargs1] at hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hmargswf x hx'
        · simp only [List.mem_singleton] at hx'; subst hx'; exact Expr.bvar_wf he1
      have hmargs1abs : absExprs margs1 = absExprs margs ++ [absExpr e1] := by
        rw [absExprs, vec_push_val hmargs1]; simp [absExprs]
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = (absCtors4 ctors).length + 1 := by
        rw [HashMap.uscalar_add_eq hi1, hn]; rfl
      obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨he2abs, he2wf⟩ :=
        hg.struct_fam_i t lps n_p n_idx i1 0#u64 e2 ht hlps he2
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hi2v : i2.val = n_idx.val + (absCtors4 ctors).length := by
        rw [HashMap.uscalar_add_eq hi2, hn]
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      have hi3v : i3.val = n_idx.val + (absCtors4 ctors).length + 1 := by
        rw [HashMap.uscalar_add_eq hi3, hi2v]; rfl
      obtain ⟨e3, he3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e4, he4, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨he4abs, he4wf⟩ :=
        ExprOps.mk_app_n_refines (Expr.bvar_wf he3) hmargs1wf he4
      obtain ⟨pw1, hpw1, h⟩ := bind_eq_ok_iff.mp h
      rw [PropWhen.dup_eq hpw1] at h
      obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
      rw [ExprOps.binder_meta_eq, Result.ok.injEq] at hbm
      subst hbm
      obtain ⟨major_body, hmb, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨itele, hitele, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hiteleabs, hitelewf⟩ :=
        ExprOps.lift_loose_bvars_refines hqewf hitele
      obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ho2abs, ho2wf⟩ := hg.replace_pis_pw pw n_idx itele major_body o2
        hpwwf hitelewf
        (Expr.forall_e_wf he2wf he4wf hpwwf hmb) ho2
      rw [hpwabs, hlabs, hiteleabs, hi1v,
        show ((0#u64 : Std.U64).val) = 0 from rfl,
        Expr.forall_e_refines hmb, he2abs, hi1v, he4abs,
        Expr.bvar_refines he3, hi3v, hmargs1abs, hmargsabs, Expr.bvar_refines he1]
        at ho2abs
      simp only [absBinderMeta, hpwabs, hlabs,
        show ((0#u64 : Std.U64).val) = 0 from rfl,
        show ((1#u64 : Std.U64).val) = 1 from rfl] at ho2abs
      cases o2 with
      | none =>
        simp only [Option.map_none] at ho2abs
        rw [← Result.ok_injective h, ← ho2abs]
        exact ⟨rfl, by simp⟩
      | some major =>
        simp only [Option.map_some] at ho2abs
        rw [← ho2abs]
        simp only []
        obtain ⟨o3, ho3, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ho3abs, ho3wf⟩ :=
          struct_minors_pis_r_refines hg hlps hpwwf hctors hcpos
            (ho2wf _ rfl) ho3
        rw [hpwabs, hlabs,
          show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero,
          show ((1#u64 : Std.U64).val) = 1 from rfl] at ho3abs
        cases o3 with
        | none =>
          simp only [Option.map_none] at ho3abs
          rw [← Result.ok_injective h, ← ho3abs]
          exact ⟨rfl, by simp⟩
        | some minors =>
          simp only [Option.map_some] at ho3abs
          rw [← ho3abs]
          simp only []
          obtain ⟨bm1, hbm1, h⟩ := bind_eq_ok_iff.mp h
          rw [ExprOps.binder_meta_eq, Result.ok.injEq] at hbm1
          subst hbm1
          obtain ⟨body, hbody, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hrabs, hrwf⟩ := hg.replace_pis_pw pw n_p tty body r hpwwf htty
            (Expr.forall_e_wf (ho1wf _ rfl) (ho3wf _ rfl) hpwwf hbody) h
          refine ⟨?_, hrwf⟩
          rw [hrabs, hpwabs, Expr.forall_e_refines hbody]
          simp only [absBinderMeta, hpwabs, hlabs]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:364-386` — `struct_rec_rhs_r`
refines `structRecRhsR`: **the generated rule** for constructor `j`, the term
`nativeRulesOk` compares with the stream's *structurally*.

`hcpos` is `struct_rec_ty_r_refines`' side condition, for the same reason.
`hj` is one more of the same kind and this lemma's own: the port reads
`ctors[j as usize]` where the cited `structRecRhsR` reads `ctors[j]?`, so the
two agree exactly when `j.val ≤ Std.Usize.max` — without it a wrapped `j`
would name a constructor where the cited reader answers `none`.  Every caller
runs `j` over the block's rules, `j < n = ctors.len()`, so
`Scalars.u64_le_usize_max_of_lt_len` discharges it. -/
theorem struct_rec_rhs_r_refines (hg : StructGens) {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {elim : name.Name} {large : Bool} {n_p n_idx : Std.U64} {tty : expr.Expr}
    {ctors : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    {rec_c : name.Name} {rlvls : alloc.vec.Vec level.Level} {j : Std.U64}
    {r : Option expr.Expr}
    (ht : NameWF t) (hlps : NamesWF lps) (helim : NameWF elim) (htty : ExprWF tty)
    (hctors : Ctors4WF ctors)
    (hcpos : ∀ c ∈ ctors.val, ∀ x ∈ c.2.2.2.val, x.val ≤ c.2.1.val)
    (hj : j.val ≤ Std.Usize.max)
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls)
    (h : inductives.native_parts.struct_rec_rhs_r t lps elim large n_p n_idx tty
        ctors rec_c rlvls j = ok r) :
    r.map absExpr = ConLeche.structRecRhsR (absName t) (absNames lps) (absName elim)
        large n_p.val n_idx.val (absExpr tty) (absCtors4 ctors) (absName rec_c)
        (absLevels rlvls) j.val
      ∧ ∀ x, r = some x → ExprWF x := by
  rw [inductives.native_parts.struct_rec_rhs_r] at h
  rw [ConLeche.structRecRhsR]
  simp only [lift_eq, bind_tc_ok] at h
  obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlabs, hlwf⟩ := hg.struct_elim_level elim large l helim hl
  obtain ⟨pw, hpw, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpwabs, hpwwf⟩ := ExprOps.zeroness_of_refines hlwf pw hpw
  have hn : (Std.UScalar.cast .U64 (alloc.vec.Vec.len ctors) : Std.U64).val
      = (absCtors4 ctors).length := by
    rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val, absCtors4,
      List.length_map]
  have hcast : (Std.UScalar.cast .Usize j : Std.Usize).val = j.val :=
    ExprOps.u64_cast_usize_val hj
  have hlv := alloc.vec.Vec.len_val ctors
  split at h
  · rename_i hge
    have hnone : (absCtors4 ctors)[j.val]? = none := by
      apply List.getElem?_eq_none
      simp only [absCtors4, List.length_map]; scalar_tac
    rw [← Result.ok_injective h, hnone]
    exact ⟨rfl, by simp⟩
  · rename_i hlt
    have hIj : j.val < ctors.val.length := by scalar_tac
    have hIjc : (Std.UScalar.cast .Usize j : Std.Usize).val < ctors.val.length := by
      rw [hcast]; exact hIj
    obtain ⟨y1, hy1, hy1v⟩ :=
      WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec ctors (Std.UScalar.cast .Usize j) hIjc)
    subst hy1v
    rcases hsp : ctors.val[(Std.UScalar.cast .Usize j : Std.Usize).val]
      with ⟨cn, cnf, ccty, cridx⟩
    have hcwf := hctors _ (List.getElem_mem hIjc)
    rw [hsp] at hcwf
    have hcridx : ∀ x ∈ cridx.val, x.val ≤ cnf.val := by
      have hx := hcpos _ (List.getElem_mem hIjc)
      rw [hsp] at hx; exact hx
    have hsome : (absCtors4 ctors)[j.val]?
        = some (absName cn, cnf.val, absExpr ccty, absU64s cridx) := by
      have hg' : (absCtors4 ctors)[(Std.UScalar.cast .Usize j : Std.Usize).val]?
          = some (absName cn, cnf.val, absExpr ccty, absU64s cridx) := by
        rw [absCtors4, List.getElem?_map, List.getElem?_eq_getElem hIjc, hsp]
        rfl
      rw [← hcast]; exact hg'
    rw [hsome]
    simp only []
    simp only [alloc.vec.Vec.index_slice_index, hy1, hsp, bind_tc_ok] at h
    obtain ⟨cty, hcty, h⟩ := bind_eq_ok_iff.mp h
    rw [Expr.dup_eq hcty] at h
    obtain ⟨ridx, hridx, h⟩ := bind_eq_ok_iff.mp h
    rw [u64s_copy_refines hridx] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines htty ho
    cases o with
    | none =>
      simp only [Option.map_none] at hoabs
      rw [← Result.ok_injective h, ← hoabs]
      exact ⟨rfl, by simp⟩
    | some tq =>
      obtain ⟨tqbs, tqe⟩ := tq
      obtain ⟨htqbswf, htqewf⟩ := howf _ rfl
      simp only [Option.map_some] at hoabs
      rw [← hoabs]
      simp only [Option.bind]
      obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ho1abs, ho1wf⟩ :=
        hg.struct_motive_ty_i t lps n_p n_idx l tqe o1 ht hlps hlwf htqewf ho1
      rw [hlabs] at ho1abs
      cases o1 with
      | none =>
        simp only [Option.map_none] at ho1abs
        rw [← Result.ok_injective h, ← ho1abs]
        exact ⟨rfl, by simp⟩
      | some motive_ty =>
        simp only [Option.map_some] at ho1abs
        rw [← ho1abs]
        simp only []
        obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ho2abs, ho2wf⟩ := ExprOps.strip_pis_refines hcwf.2 ho2
        cases o2 with
        | none =>
          simp only [Option.map_none] at ho2abs
          rw [← Result.ok_injective h, ← ho2abs]
          exact ⟨rfl, by simp⟩
        | some q =>
          obtain ⟨qbs, qe⟩ := q
          obtain ⟨hqbswf, hqewf⟩ := ho2wf _ rfl
          simp only [Option.map_some] at ho2abs
          rw [← ho2abs]
          simp only []
          obtain ⟨body, hbody, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hbodyabs, hbodywf⟩ :=
            struct_rule_body_r_refines hg hrec hrlvls hpwwf hcwf.2 hcridx hbody
          rw [hpwabs, hlabs, hn] at hbodyabs
          obtain ⟨i6, hi6, h⟩ := bind_eq_ok_iff.mp h
          have hi6v : i6.val = (absCtors4 ctors).length + 1 := by
            rw [HashMap.uscalar_add_eq hi6, hn]; rfl
          obtain ⟨lifted, hlifted, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hliftedabs, hliftedwf⟩ :=
            ExprOps.lift_loose_bvars_refines hqewf hlifted
          rw [hi6v, show ((0#u64 : Std.U64).val) = 0 from rfl] at hliftedabs
          obtain ⟨o3, ho3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ho3abs, ho3wf⟩ := hg.pis_to_lams_pw pw cnf lifted body o3
            hpwwf hliftedwf hbodywf ho3
          rw [hpwabs, hlabs, hliftedabs, hbodyabs] at ho3abs
          cases o3 with
          | none =>
            simp only [Option.map_none] at ho3abs
            rw [← Result.ok_injective h, ← ho3abs]
            exact ⟨rfl, by simp⟩
          | some inner =>
            simp only [Option.map_some] at ho3abs
            rw [← ho3abs]
            simp only []
            obtain ⟨o4, ho4, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ho4abs, ho4wf⟩ :=
              struct_minors_lams_r_refines hg hlps hpwwf hctors hcpos
                (ho3wf _ rfl) ho4
            rw [hpwabs, hlabs,
              show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero,
              show ((1#u64 : Std.U64).val) = 1 from rfl] at ho4abs
            cases o4 with
            | none =>
              simp only [Option.map_none] at ho4abs
              rw [← Result.ok_injective h, ← ho4abs]
              exact ⟨rfl, by simp⟩
            | some minors =>
              simp only [Option.map_some] at ho4abs
              rw [← ho4abs]
              simp only []
              obtain ⟨pw1, hpw1, h⟩ := bind_eq_ok_iff.mp h
              rw [PropWhen.dup_eq hpw1] at h
              obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
              rw [ExprOps.binder_meta_eq, Result.ok.injEq] at hbm
              subst hbm
              obtain ⟨lam, hlam, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hrabs, hrwf⟩ := hg.pis_to_lams_pw pw n_p tty lam r hpwwf
                htty (Expr.lam_wf (ho1wf _ rfl) (ho4wf _ rfl) hpwwf hlam) h
              refine ⟨?_, hrwf⟩
              rw [hrabs, hpwabs, Expr.lam_refines hlam]
              simp only [absBinderMeta, hpwabs, hlabs]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:388-392` —
`native_ctors4_from` is `nativeCtors4`'s `List.zipWith` from index `i` on;
`zipWith` stops at the shorter list, which is what the port's two length
guards spell. -/
theorem native_ctors4_from_refines
    {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {i : Std.Usize}
    {out v : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    (hctors : ∀ c ∈ ctors_a.val, ConstantValWF c.1)
    (hkf : ∀ (k : Nat) (hi : k < ctors_a.val.length) (hk : k < kinds.val.length),
      kinds.val[k].val.length ≤ ctors_a.val[k].2.val)
    (hout : Ctors4WF out)
    (hpos : ∀ c ∈ out.val, ∀ x ∈ c.2.2.2.val, x.val ≤ c.2.1.val)
    (h : inductives.native_parts.native_ctors4_from ctors_a kinds i out = ok v) :
    absCtors4 v = absCtors4 out ++
        ConLeche.nativeCtors4 ((absCtors ctors_a).drop i.val)
          ((absKindss kinds).drop i.val)
      ∧ Ctors4WF v ∧ ∀ c ∈ v.val, ∀ x ∈ c.2.2.2.val, x.val ≤ c.2.1.val := by
  generalize hd : ctors_a.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i out v with
  | _ d ih =>
    rw [inductives.native_parts.native_ctors4_from] at h
    have hlc := alloc.vec.Vec.len_val ctors_a
    have hlk := alloc.vec.Vec.len_val kinds
    split at h
    · rename_i hge
      have hnil : (IndAbs.absCtors ctors_a).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [IndAbs.absCtors, List.length_map]; scalar_tac
      rw [← Result.ok_injective h, hnil]
      exact ⟨by simp [ConLeche.nativeCtors4], hout, hpos⟩
    · rename_i hltc
      simp only [] at h
      split at h
      · rename_i hgek
        have hnil : (IndAbs.absKindss kinds).drop i.val = [] := by
          apply List.drop_eq_nil_of_le
          simp only [IndAbs.absKindss, List.length_map]; scalar_tac
        rw [← Result.ok_injective h, hnil]
        exact ⟨by simp [ConLeche.nativeCtors4], hout, hpos⟩
      · rename_i hltk
        have hIc : i.val < ctors_a.val.length := by scalar_tac
        have hIk : i.val < kinds.val.length := by scalar_tac
        obtain ⟨y1, hy1, hy1v⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ctors_a i hIc)
        subst hy1v
        obtain ⟨y2, hy2, hy2v⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec kinds i hIk)
        subst hy2v
        rcases hsplit : ctors_a.val[i.val] with ⟨cv0, n0⟩
        have hcvwf : ConstantValWF cv0 := by
          have hm := hctors _ (List.getElem_mem hIc)
          rw [hsplit] at hm; exact hm
        simp only [alloc.vec.Vec.index_slice_index, hy1, hy2, hsplit,
          name_dup_eq, Env.expr_dup_val, bind_tc_ok] at h
        obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        have hi4v : i4.val = i.val + 1 := HashMap.uscalar_add_eq hi4
        have hidx := rec_idx_of_refines hv1
        have habsout1 : absCtors4 out1
            = absCtors4 out ++ [(absName cv0.name, n0.val, absExpr cv0.ty,
                ConLeche.recIdxOf (absRecFieldKinds kinds.val[i.val]))] := by
          rw [absCtors4, vec_push_val hout1]
          simp [absCtors4, hidx]
        have hout1wf : Ctors4WF out1 := by
          intro c hc
          rw [vec_push_val hout1] at hc
          rcases List.mem_append.mp hc with hc' | hc'
          · exact hout c hc'
          · simp only [List.mem_singleton] at hc'
            subst hc'
            exact ⟨hcvwf.1, hcvwf.2.2⟩
        have hout1pos : ∀ c ∈ out1.val, ∀ x ∈ c.2.2.2.val, x.val ≤ c.2.1.val := by
          intro c hc
          rw [vec_push_val hout1] at hc
          rcases List.mem_append.mp hc with hc' | hc'
          · exact hpos c hc'
          · simp only [List.mem_singleton] at hc'
            subst hc'
            intro x hx
            have hxm : x.val ∈ absU64s v1 := by
              simp only [absU64s]; exact List.mem_map_of_mem hx
            rw [hidx, ConLeche.recIdxOf] at hxm
            have hxr := List.mem_of_mem_filter hxm
            rw [List.mem_range] at hxr
            have hkl : (absRecFieldKinds kinds.val[i.val]).length
                = kinds.val[i.val].val.length := by
              simp [IndAbs.absRecFieldKinds]
            have hfit : kinds.val[i.val].val.length ≤ n0.val := by
              have hf := hkf i.val hIc hIk
              rw [hsplit] at hf
              exact hf
            show x.val ≤ n0.val
            omega
        obtain ⟨hrec, hrecwf, hrecpos⟩ :=
          ih (ctors_a.length - i4.val) (by scalar_tac) hout1wf hout1pos h
            (by scalar_tac)
        refine ⟨?_, hrecwf, hrecpos⟩
        rw [hrec, hi4v, habsout1]
        have hcc : (IndAbs.absCtors ctors_a).drop i.val
            = (absConstantVal cv0, n0.val)
              :: (IndAbs.absCtors ctors_a).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons
            (show i.val < (IndAbs.absCtors ctors_a).length by
              simpa [IndAbs.absCtors] using hIc)]
          congr 1
          simp [IndAbs.absCtors, hsplit]
        have hkk : (IndAbs.absKindss kinds).drop i.val
            = absRecFieldKinds kinds.val[i.val]
              :: (IndAbs.absKindss kinds).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons
            (show i.val < (IndAbs.absKindss kinds).length by
              simpa [IndAbs.absKindss] using hIk)]
          congr 1
          simp [IndAbs.absKindss]
        rw [hcc, hkk]
        simp [ConLeche.nativeCtors4, absConstantVal]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:388-392` — `native_ctors4`
refines `nativeCtors4`: the constructors zipped with their recursive
positions, as the generators take them.

This is the **producer** of the two generators' `RecPosWF` side condition:
under `IndNativeInstall.KindsFitCtors` (`hkf`: the classification's kind list
is no longer than the field count, which `check_native_tail_guards`'
`native_fields_ok` checks with equality) every position it records comes from
`recIdxOf kinds[k]`, whose members are `< kinds[k].length ≤ ctors_a[k].2`. -/
theorem native_ctors4_refines {ctors_a : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {v : alloc.vec.Vec (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))}
    (hctors : ∀ c ∈ ctors_a.val, ConstantValWF c.1)
    (hkf : ∀ (k : Nat) (hi : k < ctors_a.val.length) (hk : k < kinds.val.length),
      kinds.val[k].val.length ≤ ctors_a.val[k].2.val)
    (h : inductives.native_parts.native_ctors4 ctors_a kinds = ok v) :
    absCtors4 v = ConLeche.nativeCtors4 (absCtors ctors_a) (absKindss kinds)
      ∧ Ctors4WF v ∧ ∀ c ∈ v.val, ∀ x ∈ c.2.2.2.val, x.val ≤ c.2.1.val := by
  rw [inductives.native_parts.native_ctors4] at h
  have hout : Ctors4WF (alloc.vec.Vec.new
      (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))) := by
    intro c hc; simp [alloc.vec.Vec.new] at hc
  have hpos : ∀ c ∈ (alloc.vec.Vec.new
      (name.Name × Std.U64 × expr.Expr × (alloc.vec.Vec Std.U64))).val,
      ∀ x ∈ c.2.2.2.val, x.val ≤ c.2.1.val := by
    intro c hc; simp [alloc.vec.Vec.new] at hc
  obtain ⟨habs, hwf, hvpos⟩ := native_ctors4_from_refines hctors hkf hout hpos h
  exact ⟨by simpa [absCtors4, alloc.vec.Vec.new] using habs, hwf, hvpos⟩

/-! ## The stream's rules against the generated ones
(`NativeParts.lean:394-475`) -/

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:394-445` —
`native_rule_prefix_head` is `nativeRulePrefixOk`'s leading
`(List.range (nP + 1 + n)).all`, from index `i` on: the rule's λ-domains are
the recursor record's own Π-domains at the same depths, up to the parse
placeholder's binder data (`resetMeta`).

**The platform side condition** (the file's header note): the port indexes both
binder lists with `i as usize`, so it and con-leche's `rbs[i]?` agree exactly
when `i.val ≤ Std.Usize.max`.  The only caller, `native_rule_prefix_ok` below,
starts at `i = 0`; the recursion re-discharges it from the `Vec`'s own length. -/
theorem native_rule_prefix_head_refines
    {rbs tbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {n i : Std.U64}
    {b : Bool} (hrbs : ExprOps.BindersWF rbs) (htbs : ExprOps.BindersWF tbs)
    (hi : i.val ≤ Std.Usize.max)
    (h : inductives.native_parts.native_rule_prefix_head rbs tbs n i = ok b) :
    b = (List.range' i.val (n.val - i.val)).all (fun k =>
      match (ExprOps.absBinders rbs)[k]?, (ExprOps.absBinders tbs)[k]? with
      | some x, some t => ConLeche.Expr.resetMeta x.1 == ConLeche.Expr.resetMeta t.1
      | _, _ => false) := by
  generalize hd : n.val - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    subst hd
    rw [inductives.native_parts.native_rule_prefix_head] at h
    simp only [lift_eq, bind_tc_ok] at h
    have hlr := alloc.vec.Vec.len_val rbs
    have hlt := alloc.vec.Vec.len_val tbs
    obtain ⟨ii, hii⟩ : ∃ ii : Std.Usize,
        (Std.UScalar.cast .Usize i : Std.Usize) = ii := ⟨_, rfl⟩
    have hcast : ii.val = i.val := by
      rw [← hii]; exact ExprOps.u64_cast_usize_val hi
    rw [hii] at h
    split at h
    · rename_i hge
      rw [← Result.ok_injective h, show n.val - i.val = 0 by scalar_tac]
      rfl
    · rename_i hnge
      have hin : i.val < n.val := by scalar_tac
      have hrange : List.range' i.val (n.val - i.val)
          = i.val :: List.range' (i.val + 1) (n.val - (i.val + 1)) := by
        rw [show n.val - i.val = (n.val - (i.val + 1)) + 1 by omega]; rfl
      rw [hrange, List.all_cons]
      split at h
      · rename_i hgr
        have hnb : (ExprOps.absBinders rbs)[i.val]? = none := by
          apply List.getElem?_eq_none
          simp only [ExprOps.absBinders, List.length_map]; scalar_tac
        rw [← Result.ok_injective h]; simp [hnb]
      · rename_i hnr
        have hIr : ii.val < rbs.val.length := by scalar_tac
        split at h
        · rename_i hgt
          have hnb : (ExprOps.absBinders tbs)[i.val]? = none := by
            apply List.getElem?_eq_none
            simp only [ExprOps.absBinders, List.length_map]; scalar_tac
          have hgetr : (ExprOps.absBinders rbs)[i.val]?
              = some (absExpr rbs.val[ii.val].1,
                  absBinderMeta rbs.val[ii.val].2) := by
            conv_lhs => rw [← hcast]
            simp [ExprOps.absBinders, List.getElem?_eq_getElem hIr]
          rw [← Result.ok_injective h]; simp [hgetr, hnb]
        · rename_i hnt
          have hIt : ii.val < tbs.val.length := by scalar_tac
          obtain ⟨y1, hy1, hy1v⟩ :=
            WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rbs ii hIr)
          subst hy1v
          obtain ⟨y2, hy2, hy2v⟩ :=
            WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec tbs ii hIt)
          subst hy2v
          rcases hspr : rbs.val[ii.val] with ⟨rb0, rm0⟩
          rcases hspt : tbs.val[ii.val] with ⟨tb0, tm0⟩
          have hrwf : ExprWF rb0 := by
            have hm := hrbs _ (List.getElem_mem hIr); rw [hspr] at hm; exact hm.1
          have htwf : ExprWF tb0 := by
            have hm := htbs _ (List.getElem_mem hIt); rw [hspt] at hm; exact hm.1
          have hgetr : (ExprOps.absBinders rbs)[i.val]?
              = some (absExpr rb0, absBinderMeta rm0) := by
            conv_lhs => rw [← hcast]
            simp [ExprOps.absBinders, List.getElem?_eq_getElem hIr, hspr]
          have hgett : (ExprOps.absBinders tbs)[i.val]?
              = some (absExpr tb0, absBinderMeta tm0) := by
            conv_lhs => rw [← hcast]
            simp [ExprOps.absBinders, List.getElem?_eq_getElem hIt, hspt]
          simp only [alloc.vec.Vec.index_slice_index, hy1, hy2, hspr, hspt,
            bind_tc_ok] at h
          obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e3, he3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨he1a, he1w⟩ := ExprOps.reset_meta_refines hrwf he1
          obtain ⟨he3a, he3w⟩ := ExprOps.reset_meta_refines htwf he3
          have hbbabs := Expr.beq_refines he1w he3w hbb
          rw [he1a, he3a] at hbbabs
          split at h
          · rename_i hbt
            rw [hbbabs] at hbt
            have heq : (ConLeche.Expr.resetMeta (absExpr rb0)
                == ConLeche.Expr.resetMeta (absExpr tb0)) = true := by
              simp [of_decide_eq_true hbt]
            obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
            have hi7v : i7.val = i.val + 1 := HashMap.uscalar_add_eq hi7
            have hi7 : i7.val ≤ Std.Usize.max :=
              Scalars.u64_le_usize_max_of_le_len (v := rbs)
                (by rw [hi7v]; scalar_tac)
            have hrec := ih (n.val - i7.val) (by scalar_tac) hi7 h (by scalar_tac)
            rw [hi7v] at hrec
            rw [hrec]
            simp only [hgetr, hgett, heq, Bool.true_and]
          · rename_i hbf
            rw [hbbabs] at hbf
            have hne : (ConLeche.Expr.resetMeta (absExpr rb0)
                == ConLeche.Expr.resetMeta (absExpr tb0)) = false := by
              rw [Bool.eq_false_iff]
              intro hc; exact hbf (by simp [by simpa using hc])
            rw [← Result.ok_injective h]
            simp only [hgetr, hgett, hne, Bool.false_and]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:394-445` —
`native_rule_prefix_fields` is the trailing `(List.range nF).all`: the rule's
field λ-domains are the `j`-th minor premise's first `nF` Π-domains, the rule's
sitting at `base = nP + 1 + n`.

**The platform side condition** (the file's header note): the port reads the
rule's binder at `(base + i) as usize`, so it and con-leche's
`rbs[base + i]?` agree exactly when `base.val + i.val ≤ Std.Usize.max`.  The
only caller, `native_rule_prefix_ok` below, starts at `i = 0` with
`base = nP + 1 + n` already bounded by the rule's own binder list; the
recursion re-discharges it from that `Vec`'s length. -/
theorem native_rule_prefix_fields_refines
    {rbs fbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {base n_f i : Std.U64}
    {b : Bool} (hrbs : ExprOps.BindersWF rbs) (hfbs : ExprOps.BindersWF fbs)
    (hbi : base.val + i.val ≤ Std.Usize.max)
    (h : inductives.native_parts.native_rule_prefix_fields rbs fbs base n_f i
        = ok b) :
    b = (List.range' i.val (n_f.val - i.val)).all (fun k =>
      match (ExprOps.absBinders rbs)[base.val + k]?,
            (ExprOps.absBinders fbs)[k]? with
      | some x, some f => ConLeche.Expr.resetMeta x.1 == ConLeche.Expr.resetMeta f.1
      | _, _ => false) := by
  generalize hd : n_f.val - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    subst hd
    rw [inductives.native_parts.native_rule_prefix_fields] at h
    simp only [lift_eq, bind_tc_ok] at h
    have hlr := alloc.vec.Vec.len_val rbs
    have hlf := alloc.vec.Vec.len_val fbs
    have hif : i.val ≤ Std.Usize.max := by omega
    obtain ⟨ii, hii⟩ : ∃ ii : Std.Usize,
        (Std.UScalar.cast .Usize i : Std.Usize) = ii := ⟨_, rfl⟩
    have hcasti : ii.val = i.val := by
      rw [← hii]; exact ExprOps.u64_cast_usize_val hif
    split at h
    · rename_i hge
      rw [← Result.ok_injective h, show n_f.val - i.val = 0 by scalar_tac]
      rfl
    · rename_i hnge
      have hin : i.val < n_f.val := by scalar_tac
      have hrange : List.range' i.val (n_f.val - i.val)
          = i.val :: List.range' (i.val + 1) (n_f.val - (i.val + 1)) := by
        rw [show n_f.val - i.val = (n_f.val - (i.val + 1)) + 1 by omega]; rfl
      rw [hrange, List.all_cons]
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = base.val + i.val := HashMap.uscalar_add_eq hi1
      obtain ⟨jj, hjj⟩ : ∃ jj : Std.Usize,
          (Std.UScalar.cast .Usize i1 : Std.Usize) = jj := ⟨_, rfl⟩
      have hcastj : jj.val = base.val + i.val := by
        rw [← hjj, ExprOps.u64_cast_usize_val (by rw [hi1v]; exact hbi), hi1v]
      rw [hjj, hii] at h
      split at h
      · rename_i hgr
        have hnb : (ExprOps.absBinders rbs)[base.val + i.val]? = none := by
          apply List.getElem?_eq_none
          simp only [ExprOps.absBinders, List.length_map]; scalar_tac
        rw [← Result.ok_injective h]; simp [hnb]
      · rename_i hnr
        have hIr : jj.val < rbs.val.length := by scalar_tac
        split at h
        · rename_i hgf
          have hnb : (ExprOps.absBinders fbs)[i.val]? = none := by
            apply List.getElem?_eq_none
            simp only [ExprOps.absBinders, List.length_map]; scalar_tac
          have hgetr : (ExprOps.absBinders rbs)[base.val + i.val]?
              = some (absExpr rbs.val[jj.val].1,
                  absBinderMeta rbs.val[jj.val].2) := by
            conv_lhs => rw [← hcastj]
            simp [ExprOps.absBinders, List.getElem?_eq_getElem hIr]
          rw [← Result.ok_injective h]; simp [hgetr, hnb]
        · rename_i hnf
          have hIf : ii.val < fbs.val.length := by scalar_tac
          obtain ⟨y1, hy1, hy1v⟩ :=
            WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rbs jj hIr)
          subst hy1v
          obtain ⟨y2, hy2, hy2v⟩ :=
            WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec fbs ii hIf)
          subst hy2v
          rcases hspr : rbs.val[jj.val] with ⟨rb0, rm0⟩
          rcases hspf : fbs.val[ii.val] with ⟨fb0, fm0⟩
          have hrwf : ExprWF rb0 := by
            have hm := hrbs _ (List.getElem_mem hIr); rw [hspr] at hm; exact hm.1
          have hfwf : ExprWF fb0 := by
            have hm := hfbs _ (List.getElem_mem hIf); rw [hspf] at hm; exact hm.1
          have hgetr : (ExprOps.absBinders rbs)[base.val + i.val]?
              = some (absExpr rb0, absBinderMeta rm0) := by
            conv_lhs => rw [← hcastj]
            simp [ExprOps.absBinders, List.getElem?_eq_getElem hIr, hspr]
          have hgetf : (ExprOps.absBinders fbs)[i.val]?
              = some (absExpr fb0, absBinderMeta fm0) := by
            conv_lhs => rw [← hcasti]
            simp [ExprOps.absBinders, List.getElem?_eq_getElem hIf, hspf]
          simp only [alloc.vec.Vec.index_slice_index, hy1, hy2, hspr, hspf,
            bind_tc_ok] at h
          obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e3, he3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨he1a, he1w⟩ := ExprOps.reset_meta_refines hrwf he1
          obtain ⟨he3a, he3w⟩ := ExprOps.reset_meta_refines hfwf he3
          have hbbabs := Expr.beq_refines he1w he3w hbb
          rw [he1a, he3a] at hbbabs
          split at h
          · rename_i hbt
            rw [hbbabs] at hbt
            have heq : (ConLeche.Expr.resetMeta (absExpr rb0)
                == ConLeche.Expr.resetMeta (absExpr fb0)) = true := by
              simp [of_decide_eq_true hbt]
            obtain ⟨i8, hi8, h⟩ := bind_eq_ok_iff.mp h
            have hi8v : i8.val = i.val + 1 := HashMap.uscalar_add_eq hi8
            have hb8 : base.val + i8.val ≤ Std.Usize.max := by
              rw [hi8v]
              exact le_trans (show base.val + (i.val + 1) ≤ rbs.val.length by
                scalar_tac) rbs.property
            have hrec := ih (n_f.val - i8.val) (by scalar_tac) hb8 h (by scalar_tac)
            rw [hi8v] at hrec
            rw [hrec]
            simp only [hgetr, hgetf, heq, Bool.true_and]
          · rename_i hbf
            rw [hbbabs] at hbf
            have hne : (ConLeche.Expr.resetMeta (absExpr rb0)
                == ConLeche.Expr.resetMeta (absExpr fb0)) = false := by
              rw [Bool.eq_false_iff]
              intro hc; exact hbf (by simp [by simpa using hc])
            rw [← Result.ok_injective h]
            simp only [hgetr, hgetf, hne, Bool.false_and]

/-! ### `nativeRulePrefixOk`, one arm at a time

The cited definition is a `match` on two `Option`s with two more nested inside,
so the composition below rewrites against these six equations rather than
unfolding the recogniser; each is the cited body with one arm decided. -/

/-- `nativeRulePrefixOk` declines a rule whose `λ` tower is too short. -/
theorem nativeRulePrefixOk_none_lams {recTy : ConLeche.Expr} {nP n j nF : Nat}
    {rhs : ConLeche.Expr}
    (hl : rhs.stripLams (nP + 1 + n + nF) = none) :
    ConLeche.nativeRulePrefixOk recTy nP n j nF rhs = false := by
  rw [ConLeche.nativeRulePrefixOk, hl]

/-- … one whose recursor type's `Π` tower is too short. -/
theorem nativeRulePrefixOk_none_pis {recTy : ConLeche.Expr} {nP n j nF : Nat}
    {rhs : ConLeche.Expr} {rbs : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {rb : ConLeche.Expr}
    (hl : rhs.stripLams (nP + 1 + n + nF) = some (rbs, rb))
    (hp : recTy.stripPis (nP + 1 + n) = none) :
    ConLeche.nativeRulePrefixOk recTy nP n j nF rhs = false := by
  rw [ConLeche.nativeRulePrefixOk, hl, hp]

/-- … one whose recursor type has no `j`-th minor premise. -/
theorem nativeRulePrefixOk_none_minor {recTy : ConLeche.Expr} {nP n j nF : Nat}
    {rhs : ConLeche.Expr} {rbs tbs : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {rb tb : ConLeche.Expr}
    (hl : rhs.stripLams (nP + 1 + n + nF) = some (rbs, rb))
    (hp : recTy.stripPis (nP + 1 + n) = some (tbs, tb))
    (hm : tbs[nP + 1 + j]? = none) :
    ConLeche.nativeRulePrefixOk recTy nP n j nF rhs = false := by
  simp only [ConLeche.nativeRulePrefixOk, hl, hp, hm, Bool.and_false]

/-- … one whose `j`-th minor premise has no `nF`-binder `Π` tower. -/
theorem nativeRulePrefixOk_none_fields {recTy : ConLeche.Expr} {nP n j nF : Nat}
    {rhs : ConLeche.Expr} {rbs tbs : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {rb tb : ConLeche.Expr} {mty : ConLeche.Expr × ConLeche.BinderMeta}
    (hl : rhs.stripLams (nP + 1 + n + nF) = some (rbs, rb))
    (hp : recTy.stripPis (nP + 1 + n) = some (tbs, tb))
    (hm : tbs[nP + 1 + j]? = some mty)
    (hf : (ConLeche.Expr.liftLooseBVars (n - j) 0 mty.1).stripPis nF = none) :
    ConLeche.nativeRulePrefixOk recTy nP n j nF rhs = false := by
  simp only [ConLeche.nativeRulePrefixOk, hl, hp, hm, hf, Bool.and_false]

/-- `nativeRulePrefixOk` at a rule whose two towers read and whose `j`-th minor
premise has its own: the cited `&&` of the head walk and the field walk. -/
theorem nativeRulePrefixOk_ok {recTy : ConLeche.Expr} {nP n j nF : Nat}
    {rhs : ConLeche.Expr} {rbs tbs fbs : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {rb tb fb : ConLeche.Expr} {mty : ConLeche.Expr × ConLeche.BinderMeta}
    (hl : rhs.stripLams (nP + 1 + n + nF) = some (rbs, rb))
    (hp : recTy.stripPis (nP + 1 + n) = some (tbs, tb))
    (hm : tbs[nP + 1 + j]? = some mty)
    (hf : (ConLeche.Expr.liftLooseBVars (n - j) 0 mty.1).stripPis nF
        = some (fbs, fb)) :
    ConLeche.nativeRulePrefixOk recTy nP n j nF rhs
      = ((List.range (nP + 1 + n)).all (fun i =>
            match rbs[i]?, tbs[i]? with
            | some b, some t =>
              ConLeche.Expr.resetMeta b.1 == ConLeche.Expr.resetMeta t.1
            | _, _ => false)
        && (List.range nF).all (fun i =>
            match rbs[nP + 1 + n + i]?, fbs[i]? with
            | some b, some f =>
              ConLeche.Expr.resetMeta b.1 == ConLeche.Expr.resetMeta f.1
            | _, _ => false)) := by
  simp only [ConLeche.nativeRulePrefixOk, hl, hp, hm, hf]
  rfl

/-- … one whose leading `nP + 1 + n` `λ`-domains are not the record's. -/
theorem nativeRulePrefixOk_head_false {recTy : ConLeche.Expr} {nP n j nF : Nat}
    {rhs : ConLeche.Expr} {rbs tbs : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {rb tb : ConLeche.Expr}
    (hl : rhs.stripLams (nP + 1 + n + nF) = some (rbs, rb))
    (hp : recTy.stripPis (nP + 1 + n) = some (tbs, tb))
    (hh : ((List.range (nP + 1 + n)).all (fun i =>
        match rbs[i]?, tbs[i]? with
        | some b, some t =>
          ConLeche.Expr.resetMeta b.1 == ConLeche.Expr.resetMeta t.1
        | _, _ => false)) = false) :
    ConLeche.nativeRulePrefixOk recTy nP n j nF rhs = false := by
  cases hm : tbs[nP + 1 + j]? with
  | none => exact nativeRulePrefixOk_none_minor hl hp hm
  | some mty =>
    cases hf : (ConLeche.Expr.liftLooseBVars (n - j) 0 mty.1).stripPis nF with
    | none => exact nativeRulePrefixOk_none_fields hl hp hm hf
    | some fq =>
      obtain ⟨fbs, fb⟩ := fq
      rw [nativeRulePrefixOk_ok hl hp hm hf, hh, Bool.false_and]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:394-445` —
`native_rule_prefix_ok` refines `nativeRulePrefixOk`: **the rule's `λ` prefix
against the stream's own recursor type**, deliberately not against
`structRecRhsR` (the cited docstring says why: the two are generated from
different data, and comparing the terms rejects 45 e2e fixtures official
accepts). -/
theorem native_rule_prefix_ok_refines {rec_ty : expr.Expr} {n_p n j n_f : Std.U64}
    {rhs : expr.Expr} {b : Bool} (hrec : ExprWF rec_ty) (hrhs : ExprWF rhs)
    (hjn : j.val ≤ n.val)
    (h : inductives.native_parts.native_rule_prefix_ok rec_ty n_p n j n_f rhs
        = ok b) :
    b = ConLeche.nativeRulePrefixOk (absExpr rec_ty) n_p.val n.val j.val n_f.val
      (absExpr rhs) := by
  rw [inductives.native_parts.native_rule_prefix_ok] at h
  simp only [lift_eq, bind_tc_ok] at h
  obtain ⟨i0, hi0, h⟩ := bind_eq_ok_iff.mp h
  have hi0v : i0.val = n_p.val + 1 := HashMap.uscalar_add_eq hi0
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = n_p.val + 1 + n.val := by
    rw [HashMap.uscalar_add_eq hi1, hi0v]
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  have hi2v : i2.val = n_p.val + 1 + n.val + n_f.val := by
    rw [HashMap.uscalar_add_eq hi2, hi1v]
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ExprOps.strip_lams_refines hrhs ho
  rw [hi2v] at hoabs
  cases o with
  | none =>
    simp only [Option.map_none] at hoabs
    rw [← Result.ok_injective h, nativeRulePrefixOk_none_lams hoabs.symm]
  | some rq =>
    obtain ⟨rv, rbody⟩ := rq
    obtain ⟨hrvwf, -⟩ := howf _ rfl
    simp only [Option.map_some] at hoabs
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
    have hi3v : i3.val = n_p.val + 1 + n.val := by
      rw [HashMap.uscalar_add_eq hi3, hi0v]
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ho1abs, ho1wf⟩ := ExprOps.strip_pis_refines hrec ho1
    rw [hi3v] at ho1abs
    cases o1 with
    | none =>
      simp only [Option.map_none] at ho1abs
      rw [← Result.ok_injective h,
        nativeRulePrefixOk_none_pis hoabs.symm ho1abs.symm]
    | some tq =>
      obtain ⟨tv, tbody⟩ := tq
      obtain ⟨htvwf, -⟩ := ho1wf _ rfl
      simp only [Option.map_some] at ho1abs
      have htlen : (ExprOps.absBinders tv).length = n_p.val + 1 + n.val :=
        ConLeche.Expr.stripPis_length _ ho1abs.symm
      have htvlen : tv.val.length = n_p.val + 1 + n.val := by
        rw [← htlen, ExprOps.absBinders, List.length_map]
      have hbound : n_p.val + 1 + n.val ≤ Std.Usize.max := by
        rw [← htvlen]; exact tv.property
      have hjb : n_p.val + 1 + j.val ≤ Std.Usize.max := by omega
      have hlv := alloc.vec.Vec.len_val tv
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
      have hi4v : i4.val = n_p.val + 1 + n.val := by
        rw [HashMap.uscalar_add_eq hi4, hi0v]
      obtain ⟨bh, hbh, h⟩ := bind_eq_ok_iff.mp h
      have hbhabs := native_rule_prefix_head_refines hrvwf htvwf (Nat.zero_le _) hbh
      rw [show ((0#u64 : Std.U64).val) = 0 from rfl, Nat.sub_zero, hi4v] at hbhabs
      split at h
      · rename_i hbt
        have hhead : ((List.range (n_p.val + 1 + n.val)).all (fun i =>
            match (ExprOps.absBinders rv)[i]?, (ExprOps.absBinders tv)[i]? with
            | some x, some t =>
              ConLeche.Expr.resetMeta x.1 == ConLeche.Expr.resetMeta t.1
            | _, _ => false)) = true := by
          rw [List.range_eq_range', ← hbhabs]; exact hbt
        obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
        have hi5v : i5.val = n_p.val + 1 + j.val := by
          rw [HashMap.uscalar_add_eq hi5, hi0v]
        obtain ⟨i6, hi6⟩ : ∃ i6 : Std.Usize,
            (Std.UScalar.cast .Usize i5 : Std.Usize) = i6 := ⟨_, rfl⟩
        have hi6v : i6.val = n_p.val + 1 + j.val := by
          rw [← hi6, ExprOps.u64_cast_usize_val (by rw [hi5v]; exact hjb), hi5v]
        rw [hi6] at h
        split at h
        · rename_i hlt
          have hIt : i6.val < tv.val.length := by scalar_tac
          obtain ⟨i8, hi8, h⟩ := bind_eq_ok_iff.mp h
          have hi8v : i8.val = n.val - j.val := ExprOps.sub_nat_val_trunc hi8
          obtain ⟨i9, hi9, h⟩ := bind_eq_ok_iff.mp h
          have hi9e : i9 = i5 := Std.UScalar.eq_of_val_eq (by
            rw [HashMap.uscalar_add_eq hi9, hi0v, hi5v])
          rw [hi9e, hi6] at h
          obtain ⟨y, hy, hyv⟩ :=
            WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec tv i6 hIt)
          subst hyv
          rcases hsp : tv.val[i6.val] with ⟨te0, tm0⟩
          have hte0wf : ExprWF te0 := by
            have hm := htvwf _ (List.getElem_mem hIt); rw [hsp] at hm; exact hm.1
          have hget : (ExprOps.absBinders tv)[n_p.val + 1 + j.val]?
              = some (absExpr te0, absBinderMeta tm0) := by
            conv_lhs => rw [← hi6v]
            simp [ExprOps.absBinders, List.getElem?_eq_getElem hIt, hsp]
          simp only [alloc.vec.Vec.index_slice_index, hy, hsp, bind_tc_ok] at h
          obtain ⟨mty, hmty, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hmtyabs, hmtywf⟩ := ExprOps.lift_loose_bvars_refines hte0wf hmty
          rw [hi8v, show ((0#u64 : Std.U64).val) = 0 from rfl] at hmtyabs
          obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ho2abs, ho2wf⟩ := ExprOps.strip_pis_refines hmtywf ho2
          rw [hmtyabs] at ho2abs
          cases o2 with
          | none =>
            simp only [Option.map_none] at ho2abs
            rw [← Result.ok_injective h,
              nativeRulePrefixOk_none_fields hoabs.symm ho1abs.symm hget
                ho2abs.symm]
          | some fq =>
            obtain ⟨fv, fbody⟩ := fq
            obtain ⟨hfvwf, -⟩ := ho2wf _ rfl
            simp only [Option.map_some] at ho2abs
            rw [nativeRulePrefixOk_ok hoabs.symm ho1abs.symm hget ho2abs.symm,
              hhead, Bool.true_and]
            obtain ⟨i11, hi11, h⟩ := bind_eq_ok_iff.mp h
            have hi11v : i11.val = n_p.val + 1 + n.val := by
              rw [HashMap.uscalar_add_eq hi11, hi0v]
            have hfields := native_rule_prefix_fields_refines hrvwf hfvwf
              (by rw [hi11v, show ((0#u64 : Std.U64).val) = 0 from rfl]; omega) h
            rw [show ((0#u64 : Std.U64).val) = 0 from rfl, Nat.sub_zero, hi11v]
              at hfields
            rw [hfields, List.range_eq_range']
        · rename_i hge
          have hnb : (ExprOps.absBinders tv)[n_p.val + 1 + j.val]? = none := by
            apply List.getElem?_eq_none
            rw [htlen]
            have : tv.val.length ≤ i6.val := by scalar_tac
            omega
          rw [← Result.ok_injective h,
            nativeRulePrefixOk_none_minor hoabs.symm ho1abs.symm hnb]
      · rename_i hbf
        have hhf : ((List.range (n_p.val + 1 + n.val)).all (fun i =>
            match (ExprOps.absBinders rv)[i]?, (ExprOps.absBinders tv)[i]? with
            | some x, some t =>
              ConLeche.Expr.resetMeta x.1 == ConLeche.Expr.resetMeta t.1
            | _, _ => false)) = false := by
          rw [List.range_eq_range', ← hbhabs]
          exact Bool.eq_false_iff.mpr hbf
        rw [← Result.ok_injective h,
          nativeRulePrefixOk_head_false hoabs.symm ho1abs.symm hhf]

/-- `nativeRuleOkAt` at a rule whose `λ` tower is too short. -/
theorem nativeRuleOkAt_none_lams {recC : ConLeche.Name} {rlvls : List ConLeche.Level}
    {pw : ConLeche.PropWhen} {nP n nF j : Nat} {rhs : ConLeche.Expr}
    {cA : ConLeche.ConstantVal} {ks : List ConLeche.RecFieldKind}
    {recTy : ConLeche.Expr}
    (hl : rhs.stripLams (nP + 1 + n + nF) = none) :
    nativeRuleOkAt recC rlvls pw nP n rhs cA nF ks recTy j = false := by
  simp only [nativeRuleOkAt, hl, Bool.and_false, Bool.false_and]

/-- `nativeRuleOkAt` at a rule whose `λ` tower reads: the cited `&&` of the
field count, the body comparison and the `λ`-prefix pin. -/
theorem nativeRuleOkAt_lams {recC : ConLeche.Name} {rlvls : List ConLeche.Level}
    {pw : ConLeche.PropWhen} {nP n nF j : Nat} {rhs : ConLeche.Expr}
    {cA : ConLeche.ConstantVal} {ks : List ConLeche.RecFieldKind}
    {recTy : ConLeche.Expr} {rbs : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {rbody : ConLeche.Expr}
    (hl : rhs.stripLams (nP + 1 + n + nF) = some (rbs, rbody)) :
    nativeRuleOkAt recC rlvls pw nP n rhs cA nF ks recTy j
      = ((ks.length == nF
          && (rbody == ConLeche.Expr.resetMeta
               (ConLeche.structRuleBodyR recC rlvls pw nP n nF j
                 (ConLeche.recIdxOf ks)
                 (ConLeche.structFieldTeleOf cA.type nP nF)
                 (ConLeche.structFieldIdxOf cA.type nP nF))))
        && ConLeche.nativeRulePrefixOk recTy nP n j nF rhs) := by
  simp only [nativeRuleOkAt, hl]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:447-475` — `native_rule_ok`
is one rule of `nativeRulesOk`: the field count, the body against the canonical
right-hand side at the parse placeholder's binder data, and the λ prefix.

`j.val ≤ n.val` is the hypothesis `native_rule_prefix_ok_refines` needs (see
there); `native_rules_ok_from` discharges it from its own `j < n`. -/
theorem native_rule_ok_refines (hg : StructGens) {rec_c : name.Name}
    {rlvls : alloc.vec.Vec level.Level} {pw : prop_when.PropWhen} {n_p n : Std.U64}
    {rhs : expr.Expr} {c_a : env.ConstantVal × Std.U64}
    {ks : alloc.vec.Vec inductives.native_parts.RecFieldKind} {rec_ty : expr.Expr}
    {j : Std.U64} {b : Bool}
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls) (hpw : PropWhenWF pw)
    (hrhs : ExprWF rhs) (hca : ConstantValWF c_a.1) (hrecty : ExprWF rec_ty)
    (hjn : j.val ≤ n.val)
    (h : inductives.native_parts.native_rule_ok rec_c rlvls pw n_p n rhs c_a ks
        rec_ty j = ok b) :
    b = nativeRuleOkAt (absName rec_c) (absLevels rlvls) (absPropWhen pw) n_p.val
      n.val (absExpr rhs) (absConstantVal c_a.1) c_a.2.val (absRecFieldKinds ks)
      (absExpr rec_ty) j.val := by
  rw [inductives.native_parts.native_rule_ok] at h
  obtain ⟨cv, nf⟩ := c_a
  simp only [lift_eq, bind_tc_ok] at h
  have hkl : (absRecFieldKinds ks).length = ks.val.length := by
    rw [IndAbs.absRecFieldKinds, List.length_map]
  simp at h
  split at h
  · rename_i hke
    have hkv : ks.val.length = nf.val := by
      have h2 := congrArg Std.UScalar.val hke
      simpa [ExprOps.usize_cast_u64_val] using h2
    have hc1 : ((absRecFieldKinds ks).length == nf.val) = true := by
      rw [hkl, hkv]; simp
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = n_p.val + 1 := HashMap.uscalar_add_eq hi2
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
    have hi3v : i3.val = n_p.val + 1 + n.val := by
      rw [HashMap.uscalar_add_eq hi3, hi2v]
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v : i4.val = n_p.val + 1 + n.val + nf.val := by
      rw [HashMap.uscalar_add_eq hi4, hi3v]
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hoabs, howf⟩ := ExprOps.strip_lams_refines hrhs ho
    rw [hi4v] at hoabs
    obtain ⟨bo, hbo, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | none =>
      simp only [Option.map_none] at hoabs
      have hbov : bo = false := (Result.ok_injective hbo).symm
      subst hbov
      simp only [Bool.false_eq_true, if_false] at h
      rw [← Result.ok_injective h, nativeRuleOkAt_none_lams hoabs.symm]
    | some q =>
      obtain ⟨rbs, rbody⟩ := q
      obtain ⟨hrbswf, hrbodywf⟩ := howf _ rfl
      simp only [Option.map_some] at hoabs
      rw [nativeRuleOkAt_lams hoabs.symm, hc1, Bool.true_and,
        show (absConstantVal cv).type = absExpr cv.ty from rfl]
      obtain ⟨v, hv, hbo⟩ := bind_eq_ok_iff.mp hbo
      have hvabs := rec_idx_of_refines hv
      have hridx : ∀ x ∈ v.val, x.val ≤ nf.val := by
        intro x hx
        have hmem : x.val ∈ absU64s v := by
          simp only [absU64s]; exact List.mem_map_of_mem hx
        rw [hvabs, ConLeche.recIdxOf] at hmem
        have hr := List.mem_of_mem_filter hmem
        rw [List.mem_range] at hr
        omega
      obtain ⟨gen, hgen, hbo⟩ := bind_eq_ok_iff.mp hbo
      obtain ⟨hgenabs, hgenwf⟩ :=
        struct_rule_body_r_refines hg hrec hrlvls hpw hca.2.2 hridx hgen
      rw [hvabs] at hgenabs
      obtain ⟨e1, he1, hbo⟩ := bind_eq_ok_iff.mp hbo
      obtain ⟨he1abs, he1wf⟩ := ExprOps.reset_meta_refines hgenwf he1
      rw [hgenabs] at he1abs
      have hbeq := Expr.beq_refines hrbodywf he1wf hbo
      have hbeqb : (absExpr rbody == absExpr e1) = bo := by
        rw [hbeq, Bool.eq_iff_iff]; simp
      rw [he1abs] at hbeqb
      rw [hbeqb]
      cases bo with
      | false =>
        rw [if_neg (by simp)] at h
        rw [Bool.false_and, ← Result.ok_injective h]
      | true =>
        rw [if_pos rfl] at h
        rw [Bool.true_and]
        exact native_rule_prefix_ok_refines hrecty hrhs hjn h
  · rename_i hke
    have hkv : ks.val.length ≠ nf.val := by
      intro hc
      exact hke (Std.UScalar.eq_of_val_eq (by simp [hc]))
    have hc1 : ((absRecFieldKinds ks).length == nf.val) = false := by
      rw [hkl, Bool.eq_false_iff]
      intro hc
      exact hkv (by simpa using hc)
    rw [← Result.ok_injective h]
    rcases hlm : (absExpr rhs).stripLams (n_p.val + 1 + n.val + nf.val) with _ | q
    · rw [nativeRuleOkAt_none_lams hlm]
    · obtain ⟨rbs, rbody⟩ := q
      rw [nativeRuleOkAt_lams hlm, hc1, Bool.false_and, Bool.false_and]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:447-475` —
`native_rules_ok_from` is `nativeRulesOk`'s `(List.range n).all` from `j` on.

**The platform side condition** (the file's header note): the port reads all
three lists at `j as usize`, so it and con-leche's `rhss[j]?` agree exactly
when `j.val ≤ Std.Usize.max`.  `native_rules_ok` below starts the recursion at
`j = 0`; the recursion re-discharges it from the `Vec`'s own length. -/
theorem native_rules_ok_from_refines (hg : StructGens) {rec_c : name.Name}
    {rlvls : alloc.vec.Vec level.Level} {pw : prop_when.PropWhen} {n_p n : Std.U64}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec inductives.native_parts.RecFieldKind)}
    {rhss : alloc.vec.Vec expr.Expr} {rec_ty : expr.Expr} {j : Std.U64} {b : Bool}
    (hrec : NameWF rec_c) (hrlvls : LevelsWF rlvls) (hpw : PropWhenWF pw)
    (hcs : ∀ c ∈ cs.val, ConstantValWF c.1) (hrhss : ExprsWF rhss)
    (hrecty : ExprWF rec_ty) (hj : j.val ≤ Std.Usize.max)
    (h : inductives.native_parts.native_rules_ok_from rec_c rlvls pw n_p n cs kinds
        rhss rec_ty j = ok b) :
    b = (List.range' j.val (n.val - j.val)).all (fun k =>
      match (absExprs rhss)[k]?, (absCtors cs)[k]?, (absKindss kinds)[k]? with
      | some rhs, some (cA, nF), some ks =>
        nativeRuleOkAt (absName rec_c) (absLevels rlvls) (absPropWhen pw) n_p.val
          n.val rhs cA nF ks (absExpr rec_ty) k
      | _, _, _ => false) := by
  generalize hd : n.val - j.val = d
  induction d using Nat.strong_induction_on generalizing j b with
  | _ d ih =>
    subst hd
    rw [inductives.native_parts.native_rules_ok_from] at h
    simp only [lift_eq, bind_tc_ok] at h
    have hlr := alloc.vec.Vec.len_val rhss
    have hlc := alloc.vec.Vec.len_val cs
    have hlk := alloc.vec.Vec.len_val kinds
    obtain ⟨jj, hjj⟩ : ∃ jj : Std.Usize,
        (Std.UScalar.cast .Usize j : Std.Usize) = jj := ⟨_, rfl⟩
    have hcast : jj.val = j.val := by
      rw [← hjj]; exact ExprOps.u64_cast_usize_val hj
    rw [hjj] at h
    split at h
    · rename_i hge
      rw [← Result.ok_injective h, show n.val - j.val = 0 by scalar_tac]
      rfl
    · rename_i hnge
      have hjn : j.val < n.val := by scalar_tac
      have hrange : List.range' j.val (n.val - j.val)
          = j.val :: List.range' (j.val + 1) (n.val - (j.val + 1)) := by
        rw [show n.val - j.val = (n.val - (j.val + 1)) + 1 by omega]; rfl
      rw [hrange, List.all_cons]
      split at h
      · rename_i hgr
        have hnb : (absExprs rhss)[j.val]? = none := by
          apply List.getElem?_eq_none
          simp only [absExprs, List.length_map]; scalar_tac
        rw [← Result.ok_injective h]; simp [hnb]
      · rename_i hnr
        have hIr : jj.val < rhss.val.length := by scalar_tac
        have hgetr : (absExprs rhss)[j.val]? = some (absExpr rhss.val[jj.val]) := by
          conv_lhs => rw [← hcast]
          simp [absExprs, List.getElem?_eq_getElem hIr]
        split at h
        · rename_i hgc
          have hnb : (IndAbs.absCtors cs)[j.val]? = none := by
            apply List.getElem?_eq_none
            simp only [IndAbs.absCtors, List.length_map]; scalar_tac
          rw [← Result.ok_injective h]; simp [hgetr, hnb]
        · rename_i hnc
          have hIc : jj.val < cs.val.length := by scalar_tac
          have hgetc : (IndAbs.absCtors cs)[j.val]?
              = some (absConstantVal cs.val[jj.val].1, cs.val[jj.val].2.val) := by
            conv_lhs => rw [← hcast]
            simp [IndAbs.absCtors, List.getElem?_eq_getElem hIc]
          split at h
          · rename_i hgk
            have hnb : (IndAbs.absKindss kinds)[j.val]? = none := by
              apply List.getElem?_eq_none
              simp only [IndAbs.absKindss, List.length_map]; scalar_tac
            rw [← Result.ok_injective h]; simp [hgetr, hgetc, hnb]
          · rename_i hnk
            have hIk : jj.val < kinds.val.length := by scalar_tac
            have hgetk : (IndAbs.absKindss kinds)[j.val]?
                = some (absRecFieldKinds kinds.val[jj.val]) := by
              conv_lhs => rw [← hcast]
              simp [IndAbs.absKindss, List.getElem?_eq_getElem hIk]
            obtain ⟨y1, hy1, hy1v⟩ :=
              WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rhss jj hIr)
            subst hy1v
            obtain ⟨y2, hy2, hy2v⟩ :=
              WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs jj hIc)
            subst hy2v
            obtain ⟨y3, hy3, hy3v⟩ :=
              WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec kinds jj hIk)
            subst hy3v
            simp only [alloc.vec.Vec.index_slice_index, hy1, hy2, hy3,
              bind_tc_ok] at h
            obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
            have hrhswf : ExprWF rhss.val[jj.val] := hrhss _ (List.getElem_mem hIr)
            have hcawf : ConstantValWF cs.val[jj.val].1 :=
              hcs _ (List.getElem_mem hIc)
            have hbbabs := native_rule_ok_refines hg hrec hrlvls hpw hrhswf hcawf
              hrecty hjn.le hbb
            split at h
            · rename_i hbt
              obtain ⟨i9, hi9, h⟩ := bind_eq_ok_iff.mp h
              have hi9v : i9.val = j.val + 1 := HashMap.uscalar_add_eq hi9
              have hj9 : i9.val ≤ Std.Usize.max :=
                Scalars.u64_le_usize_max_of_le_len (v := rhss)
                  (by rw [hi9v]; scalar_tac)
              have hrec9 := ih (n.val - i9.val) (by scalar_tac) hj9 h (by scalar_tac)
              rw [hi9v] at hrec9
              rw [hrec9]
              simp only [hgetr, hgetc, hgetk, ← hbbabs, hbt, Bool.true_and]
            · rename_i hbf
              have hbbf : bb = false := by
                cases bb with
                | false => rfl
                | true => exact absurd rfl hbf
              rw [← Result.ok_injective h]
              simp only [hgetr, hgetc, hgetk, ← hbbabs, hbbf, Bool.false_and]

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
      rw [native_rules_ok_from_refines hg hrec hrlvls hpw hcs hrhss hrecty
        (Nat.zero_le _) h]
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

/-- The **well-formedness companion** to `SumParts.sum_split_from_refines`,
which states the abstraction equation alone: a split of a well-formed block
has a well-formed constructor list, recursor constant and rule list.  This
file's own helper because the two recognisers below need it and
`Refine/IndSumParts.lean` states its split without a WF clause; it is to move
there with the rest of the split when the tier is merged. -/
theorem sum_split_from_wf {block : alloc.vec.Vec env.ConstantInfo}
    {out : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)} {i : Std.Usize}
    {o : Option ((alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64))
      × env.ConstantVal × Std.U64 × Std.U64 × (alloc.vec.Vec env.RecRule))}
    (hblock : ConstantInfosWF block) (hout : SumParts.CtorSpecsWF out)
    (h : inductives.sum_parts.sum_split_from block i out = ok o) :
    ∀ q, o = some q →
      SumParts.CtorSpecsWF q.1 ∧ ConstantValWF q.2.1 ∧ RecRulesWF q.2.2.2.2 := by
  generalize hd : block.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i out o with
  | _ d ih =>
    rw [inductives.sum_parts.sum_split_from] at h
    split at h
    · rw [← Result.ok_injective h]; simp
    · rename_i hlt
      have hlt' : i.val < block.val.length := by
        have := alloc.vec.Vec.len_val block; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block i hlt')
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      have hciwf := hblock _ (List.getElem_mem hlt')
      cases hci : block.val[i.val] with
      | AxiomInfo cv => rw [hci] at h; rw [← Result.ok_injective h]; simp
      | DefnInfo cv v hint => rw [hci] at h; rw [← Result.ok_injective h]; simp
      | ThmInfo cv v => rw [hci] at h; rw [← Result.ok_injective h]; simp
      | IndInfo cv caps => rw [hci] at h; rw [← Result.ok_injective h]; simp
      | ProjInfo t => rw [hci] at h; rw [← Result.ok_injective h]; simp
      | CtorInfo cv_c n_p n_f =>
        rw [hci] at h
        rw [hci] at hciwf
        obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hout' : SumParts.CtorSpecsWF out1 := by
          intro c hc
          rw [vec_push_val hout1] at hc
          rcases List.mem_append.mp hc with hc' | hc'
          · exact hout c hc'
          · simp only [List.mem_singleton] at hc'
            subst hc'
            rw [Env.constant_val_dup_refines hcv]
            exact hciwf
        exact ih (block.length - i2.val) (by scalar_tac) hout' h (by scalar_tac)
      | RecInfo cv_r m_i r_p rules =>
        rw [hci] at h
        rw [hci] at hciwf
        obtain ⟨hcvwf, hruleswf⟩ := hciwf
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          rw [← Result.ok_injective h]
          intro q hq
          simp only [Option.some.injEq] at hq
          subst hq
          exact ⟨hout, by rw [Env.constant_val_dup_refines hcv]; exact hcvwf,
            by rw [Env.rec_rules_copy_refines hv]; exact hruleswf⟩
        · rw [← Result.ok_injective h]; simp

/-- `nativeCounts?` at a former whose declared type IS a syntactic telescope
ending in a sort: the declared parameter count and the telescope's residual. -/
theorem nativeCounts_eq_sort {nPd : Nat} {cvT : ConLeche.ConstantVal}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)} {mI rP : Nat}
    {bs : List (ConLeche.Expr × ConLeche.BinderMeta)} {u : ConLeche.Level}
    (hpb : cvT.type.piBinders = (bs, .sort u)) :
    ConLeche.nativeCounts? nPd cvT cs mI rP
      = (if nPd ≤ bs.length then some (nPd, bs.length - nPd) else none) := by
  rw [ConLeche.nativeCounts?, hpb]

/-- `nativeCounts?` at a former declared AT A DEFINITION (task #195): the
recursor record's two argument sums are the only reading available. -/
theorem nativeCounts_eq_other {nPd : Nat} {cvT : ConLeche.ConstantVal}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)} {mI rP : Nat}
    {bs : List (ConLeche.Expr × ConLeche.BinderMeta)} {res : ConLeche.Expr}
    (hns : ∀ u, res ≠ .sort u) (hpb : cvT.type.piBinders = (bs, res)) :
    ConLeche.nativeCounts? nPd cvT cs mI rP
      = (if rP < cs.length + 1 || mI < rP then none
         else if rP - (cs.length + 1) == nPd then some (nPd, mI - rP) else none) := by
  rw [ConLeche.nativeCounts?, hpb]
  cases res with
  | sort u => exact absurd rfl (hns u)
  | _ => rfl

set_option linter.unusedVariables false in
/-- `ConLeche/Kernel/Inductives/NativeParts.lean:501-523` — `native_counts`
refines `nativeCounts?`: `nP` is the count the DECLARATION carries and `nIdx`
is what is left of the type former's Π-telescope once those binders are peeled;
at a former declared at a *definition* the recursor record's two argument sums
are the only reading available.  (`hcs` stays on the statement for uniformity
with the rest of the recognition group; the counts read the constructor list's
LENGTH only.) -/
theorem native_counts_refines {n_pd : Std.U64} {cv_t : env.ConstantVal}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)} {m_i r_p : Std.U64}
    {o : Option (Std.U64 × Std.U64)}
    (hcv : ConstantValWF cv_t) (hcs : SumParts.CtorSpecsWF cs)
    (h : inductives.native_parts.native_counts n_pd cv_t cs m_i r_p = ok o) :
    o.map (fun p => (p.1.val, p.2.val))
      = ConLeche.nativeCounts? n_pd.val (absConstantVal cv_t)
          (SumParts.absCtorSpecs cs) m_i.val r_p.val := by
  rw [inductives.native_parts.native_counts] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨vb, e⟩ := q
  obtain ⟨hb1, hb2, hbwf, hewf⟩ := pi_binders_refines hcv.2.2 hq
  have hpb : (absConstantVal cv_t).type.piBinders
      = (ExprOps.absBinders vb, absExpr e) := by rw [hb1, hb2]; rfl
  have hlv : (ExprOps.absBinders vb).length = vb.val.length := by
    rw [ExprOps.absBinders, List.length_map]
  have hcl : (SumParts.absCtorSpecs cs).length = cs.val.length := by
    rw [SumParts.absCtorSpecs, List.length_map]
  have hccast : (Std.UScalar.cast .U64 (alloc.vec.Vec.len cs) : Std.U64).val
      = cs.val.length := by
    rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
  have hvcast : (Std.UScalar.cast .U64 (alloc.vec.Vec.len vb) : Std.U64).val
      = vb.val.length := by
    rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
  obtain ⟨nd⟩ := e
  obtain ⟨de, ke⟩ := nd
  obtain ⟨en, hen, h⟩ := bind_eq_ok_iff.mp h
  have henv : expr.ExprNode.mk de ke = en :=
    Result.ok_injective ((arc_deref_eq Global (expr.ExprNode.mk de ke)).symm.trans hen)
  subst henv
  cases ke with
  | «Sort» u =>
    simp only [absExpr_mk, absExprKind] at hpb
    rw [nativeCounts_eq_sort hpb]
    simp only [exprNode_kind, lift_eq, bind_tc_ok] at h
    split at h
    · rename_i hle
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
      have hi4v : i4.val = vb.val.length - n_pd.val := by
        rw [HashMap.uscalar_sub_eq hi4, hvcast]
      rw [← Result.ok_injective h,
        if_pos (show n_pd.val ≤ (ExprOps.absBinders vb).length by
          rw [hlv]; scalar_tac)]
      simp only [Option.map_some, hi4v, hlv]
    · rename_i hgt
      rw [← Result.ok_injective h,
        if_neg (show ¬ n_pd.val ≤ (ExprOps.absBinders vb).length by
          rw [hlv]; scalar_tac)]
      rfl
  | _ =>
    simp only [absExpr_mk, absExprKind] at hpb
    rw [nativeCounts_eq_other (by intro u; simp) hpb]
    simp only [exprNode_kind, lift_eq, bind_tc_ok] at h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = cs.val.length + 1 := by
      rw [HashMap.uscalar_add_eq hi2, hccast]; rfl
    split at h
    · rename_i hlt1
      rw [← Result.ok_injective h,
        if_pos (show (decide (r_p.val < (SumParts.absCtorSpecs cs).length + 1)
            || decide (m_i.val < r_p.val)) = true by
          rw [hcl]; simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inl (by scalar_tac))]
      rfl
    · rename_i hge1
      split at h
      · rename_i hlt2
        rw [← Result.ok_injective h,
          if_pos (show (decide (r_p.val < (SumParts.absCtorSpecs cs).length + 1)
              || decide (m_i.val < r_p.val)) = true by
            simp only [Bool.or_eq_true, decide_eq_true_eq]
            exact Or.inr (by scalar_tac))]
        rfl
      · rename_i hge2
        have hnc : (decide (r_p.val < (SumParts.absCtorSpecs cs).length + 1)
            || decide (m_i.val < r_p.val)) = false := by
          rw [hcl]
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
          exact ⟨by scalar_tac, by scalar_tac⟩
        obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
        have hi5v : i5.val = cs.val.length + 1 := by
          rw [HashMap.uscalar_add_eq hi5, hccast]; rfl
        obtain ⟨i6, hi6, h⟩ := bind_eq_ok_iff.mp h
        have hi6v : i6.val = r_p.val - i5.val := HashMap.uscalar_sub_eq hi6
        split at h
        · rename_i heq
          obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
          have hi7v : i7.val = m_i.val - r_p.val := HashMap.uscalar_sub_eq hi7
          have hsub : r_p.val - (cs.val.length + 1) = n_pd.val := by
            rw [← hi5v, ← hi6v, heq]
          rw [← Result.ok_injective h, if_neg (by rw [hnc]; simp),
            if_pos (show ((r_p.val - ((SumParts.absCtorSpecs cs).length + 1))
                == n_pd.val) = true by rw [hcl, hsub]; simp)]
          simp only [Option.map_some, hi7v]
        · rename_i hne
          have hsub : ¬ (r_p.val - (cs.val.length + 1) = n_pd.val) := by
            intro hc
            exact hne (Std.UScalar.eq_of_val_eq (by rw [hi6v, hi5v]; exact hc))
          rw [← Result.ok_injective h, if_neg (by rw [hnc]; simp),
            if_neg (show ¬ ((r_p.val - ((SumParts.absCtorSpecs cs).length + 1))
                == n_pd.val) = true by rw [hcl]; simp [hsub])]
          rfl

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:525-549` —
`native_rec_pin_rules` is `nativeRecPinOk`'s `(List.range p.ctors.length).all`:
rule `j` names constructor `j` with its field count.

**The platform side condition** (the file's header note, and the reason
`Refine/Scalars.lean` exists): the port indexes both `Vec`s with `j as usize`,
and Aeneas keeps `usize`'s width abstract, so the port's reading and
con-leche's `rules[j]?` agree exactly when `j.val ≤ Std.Usize.max`.  Without
that hypothesis the statement is *false*: on a hypothetical 32-bit target a
`j` past `2 ^ 32` reads a WRAPPED entry, which the port's `j as usize >=
rules.len()` guard lets through while `rules[j]?` is `none`.  The only caller,
`native_rec_pin_ok` below, starts the recursion at `j = 0` and discharges it
with `Nat.zero_le`; the recursion re-discharges it at each step from the
`Vec`'s own length (`Scalars.u64_le_usize_max_of_le_len`). -/
theorem native_rec_pin_rules_refines {rules : alloc.vec.Vec env.RecRule}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64)} {n j : Std.U64}
    {b : Bool} (hrules : RecRulesWF rules) (hcs : SumParts.CtorSpecsWF cs)
    (hj : j.val ≤ Std.Usize.max)
    (h : inductives.native_parts.native_rec_pin_rules rules cs n j = ok b) :
    b = (List.range' j.val (n.val - j.val)).all (fun k =>
      match (absRecRules rules)[k]?, (SumParts.absCtorSpecs cs)[k]? with
      | some rule, some (cvC, _, nF) => rule.ctor == cvC.name && rule.nfields == nF
      | _, _ => false) := by
  generalize hd : n.val - j.val = d
  induction d using Nat.strong_induction_on generalizing j b with
  | _ d ih =>
    subst hd
    rw [inductives.native_parts.native_rec_pin_rules] at h
    simp only [lift_eq, bind_tc_ok] at h
    have hlr := alloc.vec.Vec.len_val rules
    have hlc := alloc.vec.Vec.len_val cs
    obtain ⟨jj, hjj⟩ : ∃ jj : Std.Usize,
        (Std.UScalar.cast .Usize j : Std.Usize) = jj := ⟨_, rfl⟩
    have hcast : jj.val = j.val := by
      rw [← hjj]; exact ExprOps.u64_cast_usize_val hj
    rw [hjj] at h
    split at h
    · rename_i hge
      rw [← Result.ok_injective h, show n.val - j.val = 0 by scalar_tac]
      rfl
    · rename_i hnge
      have hjn : j.val < n.val := by scalar_tac
      have hrange : List.range' j.val (n.val - j.val)
          = j.val :: List.range' (j.val + 1) (n.val - (j.val + 1)) := by
        rw [show n.val - j.val = (n.val - (j.val + 1)) + 1 by omega]; rfl
      rw [hrange, List.all_cons]
      split at h
      · rename_i hgr
        have hnb : (absRecRules rules)[j.val]? = none := by
          apply List.getElem?_eq_none
          simp only [absRecRules, List.length_map]
          scalar_tac
        rw [← Result.ok_injective h]
        simp [hnb]
      · rename_i hnr
        have hIr : jj.val < rules.val.length := by scalar_tac
        have hgetr : (absRecRules rules)[j.val]?
            = some (absRecRule rules.val[jj.val]) := by
          conv_lhs => rw [← hcast]
          simp [absRecRules, List.getElem?_eq_getElem hIr]
        split at h
        · rename_i hgc
          have hnb : (SumParts.absCtorSpecs cs)[j.val]? = none := by
            apply List.getElem?_eq_none
            simp only [SumParts.absCtorSpecs, List.length_map]
            scalar_tac
          rw [← Result.ok_injective h]
          simp [hgetr, hnb]
        · rename_i hnc
          have hIc : jj.val < cs.val.length := by scalar_tac
          rcases hsplit : cs.val[jj.val] with ⟨cv0, n0, f0⟩
          have hgetc : (SumParts.absCtorSpecs cs)[j.val]?
              = some (absConstantVal cv0, n0.val, f0.val) := by
            conv_lhs => rw [← hcast]
            simp [SumParts.absCtorSpecs, List.getElem?_eq_getElem hIc, hsplit]
          obtain ⟨y1, hy1, hy1v⟩ :=
            WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rules jj hIr)
          subst hy1v
          obtain ⟨y2, hy2, hy2v⟩ :=
            WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs jj hIc)
          subst hy2v
          simp only [alloc.vec.Vec.index_slice_index, hy1, hy2, hsplit,
            bind_tc_ok] at h
          simp at h
          have hrwf : RecRuleWF rules.val[jj.val] := hrules _ (List.getElem_mem hIr)
          have hcwf : ConstantValWF cv0 := by
            have hm := hcs _ (List.getElem_mem hIc)
            rw [hsplit] at hm; exact hm
          rcases h with ⟨hbb, hbv⟩ | ⟨hbb, h⟩
          · have hbbabs := Name.beq_refines hrwf.1 hcwf.1 hbb
            have hne : ¬ (absName rules.val[jj.val].ctor = absName cv0.name) := by
              intro hc; rw [hc] at hbbabs; simp at hbbabs
            have hnameq : (absName rules.val[jj.val].ctor == absName cv0.name)
                = false := by simp [hne]
            subst hbv
            simp only [hgetr, hgetc, absRecRule, absConstantVal, hnameq,
              Bool.false_and]
          · have hbbabs := Name.beq_refines hrwf.1 hcwf.1 hbb
            have heq : absName rules.val[jj.val].ctor = absName cv0.name :=
              of_decide_eq_true hbbabs.symm
            have hnameq : (absName rules.val[jj.val].ctor == absName cv0.name)
                = true := by simp [heq]
            split at h
            · rename_i hnf
              have hnf' : (rules.val[jj.val].nfields.val == f0.val) = true := by
                simp [hnf]
              obtain ⟨i9, hi9, h⟩ := bind_eq_ok_iff.mp h
              have hi9v : i9.val = j.val + 1 := HashMap.uscalar_add_eq hi9
              have hj9 : i9.val ≤ Std.Usize.max :=
                Scalars.u64_le_usize_max_of_le_len (v := rules)
                  (by rw [hi9v]; scalar_tac)
              have hrec := ih (n.val - i9.val) (by scalar_tac) hj9 h (by scalar_tac)
              rw [hi9v] at hrec
              rw [hrec]
              simp only [hgetr, hgetc, absRecRule, absConstantVal, hnameq, hnf',
                Bool.and_self, Bool.true_and]
            · rename_i hnf
              have hnf' : (rules.val[jj.val].nfields.val == f0.val) = false := by
                rw [Bool.eq_false_iff]
                intro hc
                exact hnf (Std.UScalar.eq_of_val_eq (by simpa using hc))
              rw [← Result.ok_injective h]
              simp only [hgetr, hgetc, absRecRule, absConstantVal, hnameq, hnf',
                Bool.and_false, Bool.false_and]

/-- `nativeRecPinOk` declines a head whose tail does not split. -/
theorem nativeRecPinOk_cons_none {p : ConLeche.InductiveShape}
    {cvT : ConLeche.ConstantVal} {caps : ConLeche.IndCaps}
    {rest : List ConLeche.ConstantInfo} (hss : ConLeche.sumSplit rest = none) :
    ConLeche.nativeRecPinOk p (.indInfo cvT caps :: rest) = false := by
  rw [ConLeche.nativeRecPinOk, hss]

/-- `nativeRecPinOk` at a head whose tail splits: the cited `&&` cascade, so
that the composition below rewrites against the two argument sums and the
rule walk rather than unfolding the pin. -/
theorem nativeRecPinOk_cons_split {p : ConLeche.InductiveShape}
    {cvT : ConLeche.ConstantVal} {caps : ConLeche.IndCaps}
    {rest : List ConLeche.ConstantInfo}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)} {cvR : ConLeche.ConstantVal}
    {mI rP : Nat} {rules : List ConLeche.RecRule}
    (hss : ConLeche.sumSplit rest = some (cs, cvR, mI, rP, rules)) :
    ConLeche.nativeRecPinOk p (.indInfo cvT caps :: rest)
      = (rP == p.nP + 1 + p.ctors.length
        && mI == p.nP + 1 + p.ctors.length + p.nIdx
        && rules.length == p.ctors.length
        && (List.range p.ctors.length).all (fun j =>
            match rules[j]?, cs[j]? with
            | some rule, some (cvC, _, nF) =>
              rule.ctor == cvC.name && rule.nfields == nF
            | _, _ => false)) := by
  rw [ConLeche.nativeRecPinOk, hss]
  rfl

set_option linter.unusedVariables false in
/-- `ConLeche/Kernel/Inductives/NativeParts.lean:525-549` —
`native_rec_pin_ok` refines `nativeRecPinOk`: **the recursor record's
structural pin**, whose `false` the recursor stage throws on.  (`hp` stays on
the statement for uniformity with the rest of the recognition group; the pin
compares counters and names and does not read the shape's own
well-formedness.) -/
theorem native_rec_pin_ok_refines {p : inductives.sum_parts.InductiveShape}
    {block : alloc.vec.Vec env.ConstantInfo} {b : Bool}
    (hp : InductiveShapeWF p) (hblock : ConstantInfosWF block)
    (h : inductives.native_parts.native_rec_pin_ok p block = ok b) :
    b = ConLeche.nativeRecPinOk (absInductiveShape p) (absConstantInfos block) := by
  rw [inductives.native_parts.native_rec_pin_ok] at h
  have hlen := alloc.vec.Vec.len_val block
  split at h
  · rename_i hz
    have hnil : block.val = [] := by
      apply List.eq_nil_of_length_eq_zero; scalar_tac
    rw [← Result.ok_injective h]
    simp only [absConstantInfos, hnil, List.map_nil]
    rfl
  · rename_i hz
    have hlt : 0 < block.val.length := by scalar_tac
    obtain ⟨y, hy, hyv⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block 0#usize hlt)
    subst hyv
    simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
    have hltm : 0 < (absConstantInfos block).length := by
      simpa [absConstantInfos] using hlt
    have hcons : absConstantInfos block
        = absConstantInfo block.val[(0#usize : Std.Usize).val]
          :: (absConstantInfos block).drop 1 := by
      have := List.drop_eq_getElem_cons (l := absConstantInfos block) (i := 0) hltm
      simpa [absConstantInfos] using this
    rw [hcons]
    cases hci : block.val[(0#usize : Std.Usize).val] with
    | AxiomInfo cv => rw [hci] at h; rw [← Result.ok_injective h]; rfl
    | DefnInfo cv w hint => rw [hci] at h; rw [← Result.ok_injective h]; rfl
    | ThmInfo cv w => rw [hci] at h; rw [← Result.ok_injective h]; rfl
    | CtorInfo cv np nf => rw [hci] at h; rw [← Result.ok_injective h]; rfl
    | RecInfo cv mi rp rs => rw [hci] at h; rw [← Result.ok_injective h]; rfl
    | ProjInfo t => rw [hci] at h; rw [← Result.ok_injective h]; rfl
    | IndInfo cv_t caps =>
      rw [hci] at h
      simp only [absConstantInfo]
      obtain ⟨oq, hoq, h⟩ := bind_eq_ok_iff.mp h
      have hout : SumParts.CtorSpecsWF
          (alloc.vec.Vec.new (env.ConstantVal × Std.U64 × Std.U64)) := by
        intro c hc; simp [alloc.vec.Vec.new] at hc
      have hsp : oq.map SumParts.absSumSplit
          = ConLeche.sumSplit ((absConstantInfos block).drop 1) := by
        have := SumParts.sum_split_from_refines hblock hout hoq
        simpa [SumParts.absCtorSpecs, alloc.vec.Vec.new] using this
      have hspwf := sum_split_from_wf hblock hout hoq
      cases oq with
      | none =>
        rw [← Result.ok_injective h]
        rw [nativeRecPinOk_cons_none (by rw [← hsp]; rfl)]
      | some q =>
        obtain ⟨v, cv, i2, i3, v1⟩ := q
        obtain ⟨hvwf, hcvwf, hv1wf⟩ := hspwf _ rfl
        have hss : ConLeche.sumSplit ((absConstantInfos block).drop 1)
            = some (SumParts.absCtorSpecs v, absConstantVal cv, i2.val, i3.val,
                absRecRules v1) := by
          rw [← hsp]; rfl
        rw [nativeRecPinOk_cons_split hss]
        simp only [lift_eq, bind_tc_ok] at h
        have hnv : (Std.UScalar.cast .U64 (alloc.vec.Vec.len p.ctors) : Std.U64).val
            = p.ctors.val.length := by
          rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
        have hcv1 : (Std.UScalar.cast .U64 (alloc.vec.Vec.len v1) : Std.U64).val
            = v1.val.length := by
          rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
        have hctl : (absInductiveShape p).ctors.length = p.ctors.val.length := by
          change (IndAbs.absCtors p.ctors).length = p.ctors.val.length
          rw [IndAbs.absCtors, List.length_map]
        have hnP : (absInductiveShape p).nP = p.n_p.val := rfl
        have hnIdx : (absInductiveShape p).nIdx = p.n_idx.val := rfl
        have hrl : (absRecRules v1).length = v1.val.length := by
          rw [absRecRules, List.length_map]
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        have hi4v : i4.val = p.n_p.val + 1 := HashMap.uscalar_add_eq hi4
        obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
        have hi5v : i5.val
            = i4.val + (Std.UScalar.cast .U64 (alloc.vec.Vec.len p.ctors) : Std.U64).val :=
          HashMap.uscalar_add_eq hi5
        split at h
        · rename_i he1
          have hi3v : i3.val = p.n_p.val + 1 + p.ctors.val.length := by
            rw [he1, hi5v, hi4v, hnv]
          have hc1 : (i3.val == (absInductiveShape p).nP + 1
              + (absInductiveShape p).ctors.length) = true := by
            rw [hnP, hctl, hi3v]; simp
          obtain ⟨i6, hi6, h⟩ := bind_eq_ok_iff.mp h
          have hi6v : i6.val
              = i4.val + (Std.UScalar.cast .U64 (alloc.vec.Vec.len p.ctors) : Std.U64).val :=
            HashMap.uscalar_add_eq hi6
          obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
          have hi7v : i7.val = i6.val + p.n_idx.val := HashMap.uscalar_add_eq hi7
          split at h
          · rename_i he2
            have hi2v : i2.val
                = p.n_p.val + 1 + p.ctors.val.length + p.n_idx.val := by
              rw [he2, hi7v, hi6v, hi4v, hnv]
            have hc2 : (i2.val == (absInductiveShape p).nP + 1
                + (absInductiveShape p).ctors.length + (absInductiveShape p).nIdx)
                = true := by
              rw [hnP, hnIdx, hctl, hi2v]; simp
            split at h
            · rename_i he3
              have hlv1 : v1.val.length = p.ctors.val.length := by
                rw [← hcv1, he3, hnv]
              have hc3 : ((absRecRules v1).length
                  == (absInductiveShape p).ctors.length) = true := by
                rw [hrl, hctl, hlv1]; simp
              rw [native_rec_pin_rules_refines hv1wf hvwf (Nat.zero_le _) h]
              rw [hc1, hc2, hc3]
              simp only [Bool.true_and,
                show ((0#u64 : Std.U64).val) = 0 from rfl, Nat.sub_zero,
                hnv, hctl, List.range_eq_range']
            · rename_i he3
              have hlv1 : ¬ (v1.val.length = p.ctors.val.length) := by
                intro hc
                exact he3 (Std.UScalar.eq_of_val_eq (by rw [hcv1, hnv]; exact hc))
              have hc3 : ((absRecRules v1).length
                  == (absInductiveShape p).ctors.length) = false := by
                rw [hrl, hctl, Bool.eq_false_iff]
                intro hc; exact hlv1 (by simpa using hc)
              rw [← Result.ok_injective h]
              rw [hc1, hc2, hc3]
              simp only [Bool.true_and, Bool.false_and]
          · rename_i he2
            have hc2 : (i2.val == (absInductiveShape p).nP + 1
                + (absInductiveShape p).ctors.length + (absInductiveShape p).nIdx)
                = false := by
              rw [hnP, hnIdx, hctl, Bool.eq_false_iff]
              intro hc
              refine he2 (Std.UScalar.eq_of_val_eq ?_)
              rw [hi7v, hi6v, hi4v, hnv]
              simpa using hc
            rw [← Result.ok_injective h]
            rw [hc1, hc2]
            simp only [Bool.true_and, Bool.false_and]
        · rename_i he1
          have hc1 : (i3.val == (absInductiveShape p).nP + 1
              + (absInductiveShape p).ctors.length) = false := by
            rw [hnP, hctl, Bool.eq_false_iff]
            intro hc
            refine he1 (Std.UScalar.eq_of_val_eq ?_)
            rw [hi5v, hi4v, hnv]
            simpa using hc
          rw [← Result.ok_injective h]
          rw [hc1]
          simp only [Bool.false_and]

/-- `ConLeche/Kernel/Inductives/NativeParts.lean:551-560` —
`native_rec_lps_ok` refines `nativeRecLpsOk`: **the recursor record's
level-parameter pin** — the block's own level parameters, with a fresh
elimination parameter in front at the LARGE eliminator. -/
theorem native_rec_lps_ok_refines {p : inductives.sum_parts.InductiveShape}
    {b : Bool} (hp : InductiveShapeWF p)
    (h : inductives.native_parts.native_rec_lps_ok p = ok b) :
    b = ConLeche.nativeRecLpsOk (absInductiveShape p) := by
  obtain ⟨hcvt, hctors, hcvr, helim, hsort, hrhss⟩ := hp
  rw [inductives.native_parts.native_rec_lps_ok] at h
  simp only [ConLeche.nativeRecLpsOk, absInductiveShape]
  split at h
  · rename_i hlarge
    rw [if_pos hlarge]
    simp only [name_dup_eq, bind_tc_ok] at h
    obtain ⟨expected, hexp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨expected1, hexp1, h⟩ := bind_eq_ok_iff.mp h
    have hev : expected.val = [p.elim] := by
      rw [vec_push_val hexp]; simp [alloc.vec.Vec.new]
    have he1v : expected1.val = expected.val ++ p.cv_t.level_params.val := by
      have := PropWhen.append_from_val p.cv_t.level_params
        p.cv_t.level_params.length 0#usize expected expected1 (by scalar_tac) hexp1
      simpa using this
    have hwf1 : NamesWF expected1 := by
      intro n hn
      rw [he1v, hev] at hn
      rcases List.mem_append.mp hn with hc | hc
      · simp only [List.mem_singleton] at hc; subst hc; exact helim
      · exact hcvt.2.1 n hc
    rw [Env.names_beq_refines hcvr.2.1 hwf1 h]
    simp only [absConstantVal, absNames, he1v, hev, List.map_cons,
      List.singleton_append]
    rw [Bool.eq_iff_iff]
    simp
  · rename_i hsmall
    rw [if_neg hsmall]
    rw [Env.names_beq_refines hcvr.2.1 hcvt.2.1 h]
    simp only [absConstantVal]
    rw [Bool.eq_iff_iff]
    simp

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
  generalize hd : cs.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.native_parts.native_ctors_ok_from] at h
    have hlenv := alloc.vec.Vec.len_val cs
    split at h
    · rename_i hge
      have hnil : (SumParts.absCtorSpecs cs).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [SumParts.absCtorSpecs, List.length_map]
        scalar_tac
      rw [← Result.ok_injective h, hnil]
      rfl
    · rename_i hltc
      have hlt' : i.val < cs.val.length := by scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt')
      subst hyv
      have hltm : i.val < (SumParts.absCtorSpecs cs).length := by
        simpa [SumParts.absCtorSpecs] using hlt'
      rcases hsplit : cs.val[i.val] with ⟨cv0, n0, f0⟩
      have hcvwf : ConstantValWF cv0 := by
        have hm := hcs _ (List.getElem_mem hlt')
        rw [hsplit] at hm; exact hm
      have hcons : (SumParts.absCtorSpecs cs).drop i.val
          = (absConstantVal cv0, n0.val, f0.val)
            :: (SumParts.absCtorSpecs cs).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hltm]
        congr 1
        simp [SumParts.absCtorSpecs, hsplit]
      simp only [alloc.vec.Vec.index_slice_index, hy, hsplit, bind_tc_ok] at h
      simp at h
      rw [hcons, List.all_cons]
      split at h
      · rename_i hnp
        subst hnp
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1abs := Env.names_beq_refines hcvwf.2.1 hlps hb1
        split at h
        · rename_i hbt
          rw [hb1abs] at hbt
          have hleq : absNames cv0.level_params = absNames lps := of_decide_eq_true hbt
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2abs := Name.contains_refines hres hcvwf.1 hb2
          split at h
          · rename_i hct
            rw [hb2abs] at hct
            have hct' : ((absNames reserved).contains (absName cv0.name) == false)
                = false := by rw [hct]; rfl
            rw [← Result.ok_injective h]
            simp only [absConstantVal, hleq, hct', beq_self_eq_true, Bool.true_and,
              Bool.and_false, Bool.false_and]
          · rename_i hcf
            rw [hb2abs] at hcf
            have hcf' : ((absNames reserved).contains (absName cv0.name) == false)
                = true := by rw [Bool.eq_false_iff.mpr hcf]; rfl
            obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
            have hi3v : i3.val = i.val + 1 := HashMap.uscalar_add_eq hi3
            have hrec := ih (cs.length - i3.val) (by scalar_tac) h (by scalar_tac)
            rw [hi3v] at hrec
            rw [hrec]
            simp only [absConstantVal, hleq, hcf', beq_self_eq_true, Bool.true_and]
        · rename_i hbf
          rw [hb1abs] at hbf
          have hlne : (absNames cv0.level_params == absNames lps) = false := by
            rw [Bool.eq_false_iff]
            intro hc; exact hbf (by simp [of_decide_eq_true (by simpa using hc)])
          rw [← Result.ok_injective h]
          simp only [absConstantVal, hlne, beq_self_eq_true, Bool.false_and,
            Bool.and_false]
      · rename_i hnne
        have hvne : (n0.val == n_p.val) = false := by
          rw [Bool.eq_false_iff]
          intro hc; exact hnne (Std.UScalar.eq_of_val_eq (by simpa using hc))
        rw [← Result.ok_injective h]
        simp only [hvne, Bool.false_and]

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
  rw [inductives.native_parts.native_shape_names_ok] at h
  obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
  have hb0abs := Name.contains_refines hres hcvt.1 hb0
  split at h
  · rename_i ht
    rw [hb0abs] at ht
    have ht' : ((absNames reserved).contains (absName cv_t.name) == false) = false := by
      rw [ht]; rfl
    rw [← Result.ok_injective h]
    simp only [absConstantVal, ht', Bool.false_and]
  · rename_i hf
    rw [hb0abs] at hf
    have hf' : ((absNames reserved).contains (absName cv_t.name) == false) = true := by
      rw [Bool.eq_false_iff.mpr hf]; rfl
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := Name.contains_refines hres hcvr.1 hb1
    split at h
    · rename_i ht1
      rw [hb1abs] at ht1
      have ht1' : ((absNames reserved).contains (absName cv_r.name) == false) = false := by
        rw [ht1]; rfl
      rw [← Result.ok_injective h]
      simp only [absConstantVal, hf', ht1', Bool.false_and, Bool.and_false]
    · rename_i hf1
      rw [hb1abs] at hf1
      have hf1' : ((absNames reserved).contains (absName cv_r.name) == false) = true := by
        rw [Bool.eq_false_iff.mpr hf1]; rfl
      rw [native_ctors_ok_from_refines hcs hcvt.2.1 hres h]
      simp only [absConstantVal, hf', hf1', Bool.true_and,
        show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero]

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

/-- A well-formed `Sort` node has a well-formed level (`Refine/CoreKGuards.lean`
and `Refine/IndStructParts.lean` each carry this same two-line inversion; this
file imports neither). -/
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
  rw [inductives.native_parts.native_shape_large] at h
  have hcvl : NamesWF cv_r.level_params := hcv.2.1
  have hlen := alloc.vec.Vec.len_val cv_r.level_params
  split at h
  · rename_i hz
    have hnil : cv_r.level_params.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [hz] at hlen; simpa using hlen.symm
    rw [← Result.ok_injective h]
    simp [absConstantVal, absNames, hnil]
  · rename_i hz
    have hlt : 0 < cv_r.level_params.val.length := by scalar_tac
    obtain ⟨y, hy, hyv⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cv_r.level_params 0#usize hlt)
    subst hyv
    simp only [alloc.vec.Vec.index_slice_index, hy, name_dup_eq, bind_tc_ok] at h
    obtain ⟨relps, hrelps, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hrv : relps.val = cv_r.level_params.val.drop 1 := by
      have := PropWhen.append_from_val cv_r.level_params cv_r.level_params.length
        1#usize _ relps (by scalar_tac) hrelps
      simpa [alloc.vec.Vec.new] using this
    have hrelpswf : NamesWF relps := by
      intro n hn; rw [hrv] at hn; exact hcvl n (List.mem_of_mem_drop hn)
    have h0wf : NameWF cv_r.level_params.val[(0#usize : Std.Usize).val] :=
      hcvl _ (List.getElem_mem hlt)
    have hcons : cv_r.level_params.val
        = cv_r.level_params.val[(0#usize : Std.Usize).val]
          :: cv_r.level_params.val.drop 1 := by
      have := List.drop_eq_getElem_cons (l := cv_r.level_params.val) (i := 0) hlt
      simpa using this
    have habs : (absConstantVal cv_r).levelParams
        = absName cv_r.level_params.val[(0#usize : Std.Usize).val]
          :: (absNames cv_r.level_params).tail := by
      conv_lhs => rw [absConstantVal, absNames, hcons]
      simp [absNames]
    have hrabs : absNames relps = (absNames cv_r.level_params).tail := by
      simp only [absNames, hrv]
      conv_rhs => rw [hcons]
      simp
    have hbabs : b = decide ((absNames cv_r.level_params).tail = absNames lps) := by
      rw [Env.names_beq_refines hrelpswf hlps hb, hrabs]
    rw [habs]
    split at h
    · rename_i hbt
      rw [hbabs] at hbt
      have heq : (absNames cv_r.level_params).tail = absNames lps :=
        of_decide_eq_true hbt
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1abs : b1 = (absNames lps).contains
          (absName cv_r.level_params.val[(0#usize : Std.Usize).val]) :=
        Name.contains_refines hlps h0wf hb1
      split at h
      · rename_i hct
        rw [hb1abs] at hct
        have hmem : absName cv_r.level_params.val[0] ∈ absNames lps := by
          simpa using hct
        rw [← Result.ok_injective h]
        simp [heq, hmem]
      · rename_i hcf
        rw [hb1abs] at hcf
        have hmem : absName cv_r.level_params.val[0] ∉ absNames lps := by
          simpa using hcf
        rw [← Result.ok_injective h]
        simp [heq, hmem]
    · rename_i hbf
      rw [hbabs] at hbf
      have hne : ¬ ((absNames cv_r.level_params).tail = absNames lps) := by
        intro hc; exact hbf (by simp [hc])
      rw [← Result.ok_injective h]
      simp [hne]

/-- `nativeShape?` at a block whose head is an `.indInfo` and whose tail
splits: the cited body with its `let`s spelled out, so that the composition
below *rewrites* against the readers rather than unfolding the recogniser. -/
theorem nativeShape_cons_split {nPd : Nat} {cvT : ConLeche.ConstantVal}
    {caps : ConLeche.IndCaps} {rest : List ConLeche.ConstantInfo}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)} {cvR : ConLeche.ConstantVal}
    {mI rP : Nat} {rules : List ConLeche.RecRule}
    (hss : ConLeche.sumSplit rest = some (cs, cvR, mI, rP, rules)) :
    ConLeche.nativeShape? nPd (.indInfo cvT caps :: rest)
      = (match ConLeche.nativeCounts? nPd cvT cs mI rP with
         | none => none
         | some (nP, nIdx) =>
           if ConLeche.reservedBasisNames.contains cvT.name == false
               && ConLeche.reservedBasisNames.contains cvR.name == false
               && cs.all (fun c => c.2.1 == nP && c.1.levelParams == cvT.levelParams
                   && ConLeche.reservedBasisNames.contains c.1.name == false) then
             (let s : ConLeche.Level := match cvT.type.stripPis (nP + nIdx) with
                | some (_, .sort s) => s
                | _ => .zero
              match (match cvR.levelParams with
                     | elim :: relps =>
                       if relps == cvT.levelParams && !cvT.levelParams.contains elim
                       then some elim else none
                     | [] => none) with
              | some elim =>
                some ⟨cvT, cs.map (fun c => (c.1, c.2.2)), nP, nIdx, cvR, elim, s,
                  rules.map (·.rhs), true,
                  ConLeche.Level.isEquiv s .zero == some true⟩
              | none =>
                some ⟨cvT, cs.map (fun c => (c.1, c.2.2)), nP, nIdx, cvR, .anonymous, s,
                  rules.map (·.rhs), false,
                  ConLeche.Level.isEquiv s .zero == some true⟩)
           else none) := by
  rw [ConLeche.nativeShape?, hss]
  rfl

/-- `nativeShape?` declines a head whose tail does not split. -/
theorem nativeShape_cons_none {nPd : Nat} {cvT : ConLeche.ConstantVal}
    {caps : ConLeche.IndCaps} {rest : List ConLeche.ConstantInfo}
    (hss : ConLeche.sumSplit rest = none) :
    ConLeche.nativeShape? nPd (.indInfo cvT caps :: rest) = none := by
  rw [ConLeche.nativeShape?, hss]

/-- `nativeShape?` declines a block whose counts do not read. -/
theorem nativeShape_cons_counts_none {nPd : Nat} {cvT : ConLeche.ConstantVal}
    {caps : ConLeche.IndCaps} {rest : List ConLeche.ConstantInfo}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)} {cvR : ConLeche.ConstantVal}
    {mI rP : Nat} {rules : List ConLeche.RecRule}
    (hss : ConLeche.sumSplit rest = some (cs, cvR, mI, rP, rules))
    (hc : ConLeche.nativeCounts? nPd cvT cs mI rP = none) :
    ConLeche.nativeShape? nPd (.indInfo cvT caps :: rest) = none := by
  rw [nativeShape_cons_split hss, hc]

/-- `nativeShape?` declines a block that fails the reserved-name guard. -/
theorem nativeShape_cons_guard_false {nPd : Nat} {cvT : ConLeche.ConstantVal}
    {caps : ConLeche.IndCaps} {rest : List ConLeche.ConstantInfo}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)} {cvR : ConLeche.ConstantVal}
    {mI rP nP nIdx : Nat} {rules : List ConLeche.RecRule}
    (hss : ConLeche.sumSplit rest = some (cs, cvR, mI, rP, rules))
    (hc : ConLeche.nativeCounts? nPd cvT cs mI rP = some (nP, nIdx))
    (hguard : (ConLeche.reservedBasisNames.contains cvT.name == false
        && ConLeche.reservedBasisNames.contains cvR.name == false
        && cs.all (fun c => c.2.1 == nP && c.1.levelParams == cvT.levelParams
            && ConLeche.reservedBasisNames.contains c.1.name == false)) = false) :
    ConLeche.nativeShape? nPd (.indInfo cvT caps :: rest) = none := by
  rw [nativeShape_cons_split hss, hc]
  simp only [hguard, Bool.false_eq_true, if_false]

/-- `nativeShape?` at a recognised block: the record it returns, with the
result sort, the elimination reading and the guard taken as *hypotheses*, so
that the composition below never has to match the recogniser's own spelling of
`absConstantVal`'s projections. -/
theorem nativeShape_cons_ok {nPd : Nat} {cvT : ConLeche.ConstantVal}
    {caps : ConLeche.IndCaps} {rest : List ConLeche.ConstantInfo}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)} {cvR : ConLeche.ConstantVal}
    {mI rP nP nIdx : Nat} {rules : List ConLeche.RecRule} {s : ConLeche.Level}
    {lg : Option ConLeche.Name}
    (hss : ConLeche.sumSplit rest = some (cs, cvR, mI, rP, rules))
    (hc : ConLeche.nativeCounts? nPd cvT cs mI rP = some (nP, nIdx))
    (hguard : (ConLeche.reservedBasisNames.contains cvT.name == false
        && ConLeche.reservedBasisNames.contains cvR.name == false
        && cs.all (fun c => c.2.1 == nP && c.1.levelParams == cvT.levelParams
            && ConLeche.reservedBasisNames.contains c.1.name == false)) = true)
    (hsv : (match cvT.type.stripPis (nP + nIdx) with
            | some (_, .sort u) => u
            | _ => .zero) = s)
    (hlg : (match cvR.levelParams with
            | elim :: relps =>
              if relps == cvT.levelParams && !cvT.levelParams.contains elim
              then some elim else none
            | [] => none) = lg) :
    ConLeche.nativeShape? nPd (.indInfo cvT caps :: rest)
      = lg.elim
          (some ⟨cvT, cs.map (fun c => (c.1, c.2.2)), nP, nIdx, cvR, .anonymous, s,
            rules.map (·.rhs), false, ConLeche.Level.isEquiv s .zero == some true⟩)
          (fun elim =>
            some ⟨cvT, cs.map (fun c => (c.1, c.2.2)), nP, nIdx, cvR, elim, s,
              rules.map (·.rhs), true,
              ConLeche.Level.isEquiv s .zero == some true⟩) := by
  rw [nativeShape_cons_split hss, hc]
  simp only [hguard, if_true, hsv]
  rw [hlg]
  cases lg <;> rfl

/-- The well-formedness companion to `native_shape_large_refines`: the
elimination parameter it returns is the recursor record's own first level
parameter. -/
theorem native_shape_large_wf {cv_r : env.ConstantVal}
    {lps : alloc.vec.Vec name.Name} {o : Option name.Name}
    (hcv : ConstantValWF cv_r)
    (h : inductives.native_parts.native_shape_large cv_r lps = ok o) :
    ∀ n, o = some n → NameWF n := by
  rw [inductives.native_parts.native_shape_large] at h
  have hlen := alloc.vec.Vec.len_val cv_r.level_params
  split at h
  · rw [← Result.ok_injective h]; simp
  · rename_i hz
    have hlt : 0 < cv_r.level_params.val.length := by scalar_tac
    obtain ⟨y, hy, hyv⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cv_r.level_params 0#usize hlt)
    subst hyv
    simp only [alloc.vec.Vec.index_slice_index, hy, name_dup_eq, bind_tc_ok] at h
    obtain ⟨relps, hrelps, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · rw [← Result.ok_injective h]; simp
      · rw [← Result.ok_injective h]
        intro n hn
        simp only [Option.some.injEq] at hn
        subst hn
        exact hcv.2.1 _ (List.getElem_mem hlt)
    · rw [← Result.ok_injective h]; simp

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
  rw [inductives.native_parts.native_shape] at h
  have hlen := alloc.vec.Vec.len_val block
  split at h
  · rename_i hz
    have hnil : block.val = [] := by
      apply List.eq_nil_of_length_eq_zero; scalar_tac
    rw [← Result.ok_injective h]
    refine ⟨?_, by simp⟩
    simp only [absConstantInfos, hnil, List.map_nil, Option.map_none]
    rfl
  · rename_i hz
    have hlt : 0 < block.val.length := by scalar_tac
    obtain ⟨y, hy, hyv⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block 0#usize hlt)
    subst hyv
    simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
    have hltm : 0 < (absConstantInfos block).length := by
      simpa [absConstantInfos] using hlt
    have hcons : absConstantInfos block
        = absConstantInfo block.val[(0#usize : Std.Usize).val]
          :: (absConstantInfos block).drop 1 := by
      have := List.drop_eq_getElem_cons (l := absConstantInfos block) (i := 0) hltm
      simpa [absConstantInfos] using this
    have hciwf : ConstantInfoWF block.val[(0#usize : Std.Usize).val] :=
      hblock _ (List.getElem_mem
        (show (0#usize : Std.Usize).val < block.val.length from hlt))
    rw [hcons]
    cases hci : block.val[(0#usize : Std.Usize).val] with
    | AxiomInfo cv => rw [hci] at h; rw [← Result.ok_injective h]; exact ⟨rfl, by simp⟩
    | DefnInfo cv w hint => rw [hci] at h; rw [← Result.ok_injective h]; exact ⟨rfl, by simp⟩
    | ThmInfo cv w => rw [hci] at h; rw [← Result.ok_injective h]; exact ⟨rfl, by simp⟩
    | CtorInfo cv np nf => rw [hci] at h; rw [← Result.ok_injective h]; exact ⟨rfl, by simp⟩
    | RecInfo cv mi rp rs => rw [hci] at h; rw [← Result.ok_injective h]; exact ⟨rfl, by simp⟩
    | ProjInfo t => rw [hci] at h; rw [← Result.ok_injective h]; exact ⟨rfl, by simp⟩
    | IndInfo cv_t caps =>
      rw [hci] at h
      rw [hci] at hciwf
      have hcvt : ConstantValWF cv_t := hciwf.1
      simp only [absConstantInfo]
      obtain ⟨oq, hoq, h⟩ := bind_eq_ok_iff.mp h
      have hout : SumParts.CtorSpecsWF
          (alloc.vec.Vec.new (env.ConstantVal × Std.U64 × Std.U64)) := by
        intro c hc; simp [alloc.vec.Vec.new] at hc
      have hsp : oq.map SumParts.absSumSplit
          = ConLeche.sumSplit ((absConstantInfos block).drop 1) := by
        have := SumParts.sum_split_from_refines hblock hout hoq
        simpa [SumParts.absCtorSpecs, alloc.vec.Vec.new] using this
      have hspwf := sum_split_from_wf hblock hout hoq
      cases oq with
      | none =>
        rw [← Result.ok_injective h]
        refine ⟨?_, by simp⟩
        rw [nativeShape_cons_none (by rw [← hsp]; rfl)]
        rfl
      | some q =>
        obtain ⟨v, cv, i1, i2, v1⟩ := q
        obtain ⟨hvwf, hcvwf, hv1wf⟩ := hspwf _ rfl
        have hss : ConLeche.sumSplit ((absConstantInfos block).drop 1)
            = some (SumParts.absCtorSpecs v, absConstantVal cv, i1.val, i2.val,
                absRecRules v1) := by
          rw [← hsp]; rfl
        obtain ⟨reserved, hres, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hresabs, hreswf⟩ := BasisNames.reserved_basis_names_refines hres
        obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
        have hcounts := native_counts_refines hcvt hvwf ho1
        cases o1 with
        | none =>
          rw [← Result.ok_injective h]
          refine ⟨?_, by simp⟩
          rw [nativeShape_cons_counts_none hss hcounts.symm]
          rfl
        | some counts =>
          obtain ⟨n_p, n_idx⟩ := counts
          have hc : ConLeche.nativeCounts? n_pd.val (absConstantVal cv_t)
              (SumParts.absCtorSpecs v) i1.val i2.val = some (n_p.val, n_idx.val) :=
            hcounts.symm
          obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
          have hbabs := native_shape_names_ok_refines hcvt hcvwf hvwf hreswf hb
          rw [hresabs] at hbabs
          split at h
          · rename_i hbt
            have hguard : (ConLeche.reservedBasisNames.contains
                    (absConstantVal cv_t).name == false
                  && ConLeche.reservedBasisNames.contains (absConstantVal cv).name == false
                  && (SumParts.absCtorSpecs v).all (fun c => c.2.1 == n_p.val
                      && c.1.levelParams == (absConstantVal cv_t).levelParams
                      && ConLeche.reservedBasisNames.contains c.1.name == false)) = true :=
              hbabs.symm.trans hbt
            obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
            have hi3v : i3.val = n_p.val + n_idx.val := HashMap.uscalar_add_eq hi3
            obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hpabs, hpwf⟩ := ExprOps.strip_pis_refines hcvt.2.2 ho2
            rw [hi3v] at hpabs
            obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
            have hsfacts : (match (absExpr cv_t.ty).stripPis (n_p.val + n_idx.val) with
                  | some (_, .sort u) => u
                  | _ => .zero) = absLevel s ∧ LevelWF s := by
              cases o2 with
              | none =>
                simp only [Option.map_none] at hpabs
                rw [← hpabs]
                exact ⟨(Level.zero_refines hs).symm, LevelWF.zero hs⟩
              | some tq =>
                obtain ⟨tb, te⟩ := tq
                obtain ⟨-, htewf⟩ := hpwf _ rfl
                simp only [Option.map_some] at hpabs
                rw [← hpabs]
                obtain ⟨nd⟩ := te
                obtain ⟨de, ke⟩ := nd
                cases ke with
                | «Sort» u =>
                  simp only [arc_deref_eq, bind_tc_ok, level_dup_eq] at hs
                  simp at hs
                  refine ⟨?_, ?_⟩
                  · rw [← hs]; simp [absExpr_mk, absExprKind]
                  · rw [← hs]; exact wf_sort_inv htewf rfl
                | _ =>
                  simp only [arc_deref_eq, bind_tc_ok] at hs
                  simp at hs
                  exact ⟨by rw [Level.zero_refines hs]; simp [absExpr_mk, absExprKind],
                    LevelWF.zero hs⟩
            obtain ⟨is_prop, hip, h⟩ := bind_eq_ok_iff.mp h
            have hipabs := hg.level_is_prop s is_prop hsfacts.2 hip
            obtain ⟨ctors, hctors, h⟩ := bind_eq_ok_iff.mp h
            have hctorsabs := native_ctors_of_refines hctors
            have hctorsval : ctors.val = v.val.map (fun c => (c.1, c.2.2)) := by
              rw [inductives.native_parts.native_ctors_of] at hctors
              have := native_ctors_of_from_refines hctors
              simpa [alloc.vec.Vec.new] using this
            have hctorswf : ∀ c ∈ ctors.val, ConstantValWF c.1 := by
              intro c hcm
              rw [hctorsval, List.mem_map] at hcm
              obtain ⟨c0, hc0, rfl⟩ := hcm
              exact hvwf c0 hc0
            obtain ⟨rhss, hrhss, h⟩ := bind_eq_ok_iff.mp h
            have hrhssabs := native_rhss_of_refines hrhss
            have hrhssval : rhss.val = v1.val.map (fun r => r.rhs) := by
              rw [inductives.native_parts.native_rhss_of] at hrhss
              have := native_rhss_of_from_refines hrhss
              simpa [alloc.vec.Vec.new] using this
            have hrhsswf : ExprsWF rhss := by
              intro e hem
              rw [hrhssval, List.mem_map] at hem
              obtain ⟨r0, hr0, rfl⟩ := hem
              exact (hv1wf r0 hr0).2.2
            obtain ⟨o3, ho3, h⟩ := bind_eq_ok_iff.mp h
            have ho3abs := native_shape_large_refines hcvwf hcvt.2.1 ho3
            have ho3wf := native_shape_large_wf hcvwf ho3
            rw [nativeShape_cons_ok hss hc hguard hsfacts.1 ho3abs.symm]
            cases o3 with
            | none =>
              obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨nn, hnn, h⟩ := bind_eq_ok_iff.mp h
              have hcv1e : cv1 = cv_t := Env.constant_val_dup_refines hcv1
              rw [← Result.ok_injective h]
              refine ⟨?_, ?_⟩
              · simp only [Option.map_some, Option.map_none, Option.elim,
                  absInductiveShape, hcv1e, hctorsabs, hrhssabs, hipabs,
                  Name.anonymous_refines hnn]
              · intro p hp
                rw [← Option.some.inj hp]
                exact ⟨hcv1e ▸ hcvt, hctorswf, hcvwf, NameWF.anonymous hnn,
                  hsfacts.2, hrhsswf⟩
            | some elim =>
              obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
              have hcv1e : cv1 = cv_t := Env.constant_val_dup_refines hcv1
              rw [← Result.ok_injective h]
              refine ⟨?_, ?_⟩
              · simp only [Option.map_some, Option.elim,
                  absInductiveShape, hcv1e, hctorsabs, hrhssabs, hipabs]
              · intro p hp
                rw [← Option.some.inj hp]
                exact ⟨hcv1e ▸ hcvt, hctorswf, hcvwf, ho3wf elim rfl,
                  hsfacts.2, hrhsswf⟩
          · rename_i hbf
            rw [← Result.ok_injective h]
            refine ⟨?_, by simp⟩
            rw [nativeShape_cons_guard_false hss hc
              (by rw [← hbabs]; simpa using hbf)]
            rfl

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
  rw [inductives.native_parts.native_parts] at h
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hs, hswf⟩ := native_shape_refines hg hblock ho1
  cases o1 with
  | none =>
    simp only [] at h
    rw [← Result.ok_injective h]
    refine ⟨?_, ?_⟩
    · rw [ConLeche.nativeParts?, ← hs]; rfl
    · intro p hp; exact absurd hp (by simp)
  | some p =>
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hpwf : InductiveShapeWF p := hswf p rfl
    have hpin := native_rec_pin_ok_refines hpwf hblock hb
    rw [← Result.ok_injective h]
    refine ⟨?_, ?_⟩
    · rw [ConLeche.nativeParts?, ← hs]
      simp only [Option.map_some, absNativeParts, hpin, IndAbs.absKindss,
        alloc.vec.Vec.new]
      rfl
    · intro q hq
      rw [← Option.some.inj hq]
      exact hpwf

end Gens

end ConRon.Refine.NativeParts
