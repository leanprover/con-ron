/-
`CORE_PLAN.md` step 4 (task #49), the **literal-reduction** leaves of
`crates/con-ron-core/src/kernel/core_k.rs`, refined against
`ConLeche/Kernel/Core.lean`:

* the `Nat`-literal readers and builders --- `natLitToConstructor` (`:266`),
  `rawNatLit?` (`:341`, whose `Cached/StateC.lean:98` twin `rawNatLitC?` is the
  same function), `litToCtorIfNat` (`:334`, twin `Cached/CoreC.lean:84`
  `litToCtorIfNatI` under a `pure`) and the `defeqStep` (`:2371-2631`)
  predecessor probe `succ_of`;
* the `String`-literal constructor form `strLitToConstructor` (`:360`), whose
  `s.toList.foldr` the port spells as the downward index recursion
  `str_lit_cons_from`;
* the equation table `natOpEquations` (`:597`) with its three spine builders
  `nat_eq_s`/`nat_eq_ap1`/`nat_eq_ap2` (the `let`-bound closures of the cited
  block, named because §3.4 forbids closures), and
* **`natOpResult` (`:628`)**, the `Nat`-operation fast path --- the headline
  lemma of this file, and the one pinned in the axiom census;
* `Expr.isBoolTrue` (`:524`), the `Bool`-constructor reader the equation table
  and the fast path both name.

Three things carry the proofs.

**The pinned names are hypotheses.**  Every function here mentions pinned
names (`basis_names::nat_zero_name`, `core_k::nat_add_name`, ...), whose
refinements are landed in `Refine/CoreKNames.lean` and `Refine/BasisNames.lean`
by sibling agents of the same task.  Rather than duplicate them, each lemma
takes what it needs as a `PinnedName` hypothesis --- literally the shape those
files prove (`∀ n, f = ok n → absName n = ln ∧ NameWF n`), so that discharging
them at merge is `exact ⟨fun _ h => nat_add_name_refines h, ...⟩`.  The
seventeen the fast path and the equation table need are bundled as
`NatOpPinned`.

**Exactness of `name::beq`** (`Refine/Name.lean`'s `beq_refines`) is what turns
the port's `if name::beq c &nat_add_name()` cascade into the cited
`if c = natAddName` cascade; it needs `NameWF` on both sides, which is why the
name arguments carry `NameWF` and the `PinnedName` hypotheses carry the
`∧ NameWF n` conjunct.

**No arithmetic is re-proved.**  Every operation `nat_op_result` dispatches on
is `Refine/Nat.lean`'s, used as a black box.  Task #61 removed the one place
the port used to answer `none` where con-leche computes (a
`shiftLeft`/`shiftRight` amount beyond `u64`): the port *fails* there instead,
so `OpSpec` is an exact refinement in both directions --- see
`nat_op_result_refines`'s doc comment.  Task #67 classified that failure: it is
one of the port's own `Native` declines, since `ConLeche.natOpResult` is total
and there is no `throw` anywhere in the cited range to mirror.  What the failure
half claims is therefore only `absErrKind ce = none` --- `nat_op_result_native`,
which is what a caller feeds to `ErrSim.of_none`.

Two local helpers, `const_wf_inv` and `lit_wf_inv`, invert `ExprWF` at a `Const`
and at a `Lit` node (the head name's `NameWF`, the payload's `LiteralWF`); they
belong in `Refine/Expr.lean` beside the `*_inv` family and are *not* added there
by this file, so they are `private` here.  Every other generically named helper
is `private` for the same reason.

**On merge**: `PinnedName` is defined here *and*, character for character, in
`Refine/CoreKNatOps.lean` -- one of the two copies goes, and the vocabulary is
deliberately the same.  `lit_to_ctor_if_nat_refines`'s `hsupp` hypothesis is
`CoreKNatOps.lean`'s `NatLitSupportedSpec` spelled out, at whichever of the two
guard readings the caller has.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

/-! ## The pinned names, as hypotheses

`PinnedName f ln` is exactly the statement `Refine/CoreKNames.lean` and
`Refine/BasisNames.lean` prove of a pinned name, so a hypothesis of this shape
is discharged by the corresponding `*_name_refines` and nothing else. -/

/-- The fifteen pinned names `nat_op_result` and `nat_op_equations` dispatch
on, plus the two `Bool` constructors they build. -/
structure NatOpPinned : Prop where
  pred : PinnedName core_k.nat_pred_name ConLeche.natPredName
  add : PinnedName core_k.nat_add_name ConLeche.natAddName
  sub : PinnedName core_k.nat_sub_name ConLeche.natSubName
  mul : PinnedName core_k.nat_mul_name ConLeche.natMulName
  pow : PinnedName core_k.nat_pow_name ConLeche.natPowName
  div : PinnedName core_k.nat_div_name ConLeche.natDivName
  mod : PinnedName core_k.nat_mod_name ConLeche.natModName
  gcd : PinnedName core_k.nat_gcd_name ConLeche.natGcdName
  land : PinnedName core_k.nat_land_name ConLeche.natLandName
  lor : PinnedName core_k.nat_lor_name ConLeche.natLorName
  xor : PinnedName core_k.nat_xor_name ConLeche.natXorName
  shl : PinnedName core_k.nat_shift_left_name ConLeche.natShiftLeftName
  shr : PinnedName core_k.nat_shift_right_name ConLeche.natShiftRightName
  beq : PinnedName core_k.nat_beq_name ConLeche.natBeqName
  ble : PinnedName core_k.nat_ble_name ConLeche.natBleName
  boolTrue : PinnedName core_k.bool_true_name ConLeche.boolTrueName
  boolFalse : PinnedName core_k.bool_false_name ConLeche.boolFalseName

/-! ## Two plumbing facts -/

/-- The port's `Vec::new` of levels is con-leche's `[]`. -/
@[local simp] private theorem absLevels_new : absLevels (alloc.vec.Vec.new level.Level) = [] := rfl

/-- **`ExprWF` inverted at a `Const` node.**  Belongs in `Refine/Expr.lean`
beside the `*_inv` family; written here because task #49 owns no other file.
Only the head name's `NameWF` is used (by the `name::beq` exactness of the three
constant readers below), but the levels come for free. -/
private theorem const_wf_inv {e : expr.Expr} (he : ExprWF e) :
    ∀ {d : Std.U64} {c : name.Name} {us : alloc.vec.Vec level.Level},
      e = .mk (.mk d (.Const c us)) → NameWF c ∧ LevelsWF us := by
  cases he with
  | @bvar i e h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; intros; simp_all
  | @fvar idx ty e _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; intros; simp_all
  | @sort u e _ h1 => obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1; intros; simp_all
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro d c us' hk
    cases hk
    exact ⟨hn, hus⟩
  | @app f a e _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; intros; simp_all
  | @lam ty b m e _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; intros; simp_all
  | @forall_e ty b m e _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; intros; simp_all
  | @let_e ty v b e _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; intros; simp_all
  | @lit l e _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; intros; simp_all
  | @proj s i x e _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; intros; simp_all

/-- **`ExprWF` inverted at a `Lit` node** -- the payload's `LiteralWF`, i.e. the
bignum's `NatWF` (which the `Nat`-literal readers hand on) or the string's
`StrWF` (which `str_lit_to_constructor` needs to know its code points are
`Char`s).  Belongs in `Refine/Expr.lean`, like `const_wf_inv`. -/
private theorem lit_wf_inv {e : expr.Expr} (he : ExprWF e) :
    ∀ {d : Std.U64} {l : expr.Literal}, e = .mk (.mk d (.Lit l)) → LiteralWF l := by
  cases he with
  | @bvar i e h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; intros; simp_all
  | @fvar idx ty e _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; intros; simp_all
  | @sort u e _ h1 => obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1; intros; simp_all
  | @mk_const n us e _ _ h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; intros; simp_all
  | @app f a e _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; intros; simp_all
  | @lam ty b m e _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; intros; simp_all
  | @forall_e ty b m e _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; intros; simp_all
  | @let_e ty v b e _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; intros; simp_all
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro d l' hk
    cases hk
    exact hl
  | @proj s i x e _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; intros; simp_all

/-! ## The `Bool`-constructor reader

`Core.lean:524-529` -- `Expr.isBoolTrue`.  A plain `Bool` equation (§3.5): the
port reads the node's kind and compares the head name, so the content is
`name::beq`'s exactness at the pinned `Bool.true`. -/

/-- **`core_k::is_bool_true` refines `Expr.isBoolTrue`** (`Core.lean:524-529`). -/
theorem is_bool_true_refines {e : expr.Expr} {b : Bool} (he : ExprWF e)
    (htrue : PinnedName core_k.bool_true_name ConLeche.boolTrueName)
    (h : core_k.is_bool_true e = ok b) :
    b = (absExpr e).isBoolTrue := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [core_k.is_bool_true.eq_def] at h
  simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
  cases k with
  | Const c us =>
    dsimp only at h
    split at h <;> rename_i hlen
    · have hnil : us.val = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
      obtain ⟨n, hn, hbeq⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hnabs, hnwf⟩ := htrue n hn
      obtain ⟨hcwf, -⟩ := const_wf_inv he rfl
      rw [Name.beq_refines hcwf hnwf hbeq, hnabs]
      show _ = ConLeche.Expr.isBoolTrue (.const (absName c) (absLevels us))
      rw [show absLevels us = [] by simp [absLevels, hnil]]
      rfl
    · have hne : us.val ≠ [] := by
        intro hc
        exact hlen (by scalar_tac)
      simp only [Result.ok.injEq] at h
      rw [← h]
      show _ = ConLeche.Expr.isBoolTrue (.const (absName c) (absLevels us))
      cases hl : absLevels us with
      | nil => exact absurd (by simpa [absLevels] using hl) hne
      | cons u l => rfl
  | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp [ConLeche.Expr.isBoolTrue]

/-! ## The three spine builders of the equation table

`Core.lean:597-626` -- the `let`-bound `s`/`ap1`/`ap2` of `natOpEquations`.
§3.4 forbids closures, so the port names them; each is one `mk_const` and one
or two `app`s, and each therefore gets a plain refinement plus `ExprWF`. -/

/-- `LevelsWF` of the empty level vector -- every `mk_const` here is
level-monomorphic. -/
private theorem levels_wf_new : LevelsWF (alloc.vec.Vec.new level.Level) := by
  intro u hu; simp [alloc.vec.Vec.new] at hu

/-- **`core_k::nat_eq_s` refines the `s : Expr → Expr` local**
(`Core.lean:605`): `Nat.succ ·`. -/
theorem nat_eq_s_refines {a r : expr.Expr} (ha : ExprWF a)
    (hsucc : PinnedName basis_names.nat_succ_name ConLeche.natSuccName)
    (h : core_k.nat_eq_s a = ok r) :
    absExpr r = .app (.const ConLeche.natSuccName []) (absExpr a) ∧ ExprWF r := by
  rw [core_k.nat_eq_s] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, e, he, happ⟩ := h
  obtain ⟨hnabs, hnwf⟩ := hsucc n hn
  refine ⟨?_, Expr.app_wf (Expr.mk_const_wf hnwf levels_wf_new he) ha happ⟩
  rw [Expr.app_refines happ, Expr.mk_const_refines he, hnabs, absLevels_new]

/-- **`core_k::nat_eq_ap1` refines the `ap1 : Name → Expr → Expr` local**
(`Core.lean:606`). -/
theorem nat_eq_ap1_refines {n : name.Name} {a r : expr.Expr} (hn : NameWF n)
    (ha : ExprWF a) (h : core_k.nat_eq_ap1 n a = ok r) :
    absExpr r = .app (.const (absName n) []) (absExpr a) ∧ ExprWF r := by
  rw [core_k.nat_eq_ap1] at h
  simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨e, he, happ⟩ := h
  refine ⟨?_, Expr.app_wf (Expr.mk_const_wf hn levels_wf_new he) ha happ⟩
  rw [Expr.app_refines happ, Expr.mk_const_refines he, absLevels_new]

/-- **`core_k::nat_eq_ap2` refines the `ap2 : Name → Expr → Expr → Expr` local**
(`Core.lean:607-608`). -/
theorem nat_eq_ap2_refines {n : name.Name} {a b r : expr.Expr} (hn : NameWF n)
    (ha : ExprWF a) (hb : ExprWF b) (h : core_k.nat_eq_ap2 n a b = ok r) :
    absExpr r = .app (.app (.const (absName n) []) (absExpr a)) (absExpr b) ∧ ExprWF r := by
  rw [core_k.nat_eq_ap2] at h
  simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨e, he, e1, h1, happ⟩ := h
  refine ⟨?_, Expr.app_wf (Expr.app_wf (Expr.mk_const_wf hn levels_wf_new he) ha h1) hb happ⟩
  rw [Expr.app_refines happ, Expr.app_refines h1, Expr.mk_const_refines he, absLevels_new]

/-! ## `Nat` literals

`Core.lean:266-346`.  The cited `match n with | 0 | k + 1` of
`natLitToConstructor` is `nat::is_zero` plus `nat::pred` on the bignum
(DESIGN.md §3.3), so the two arms are decided by `Refine/Nat.lean`'s
`is_zero_refines` and closed by its `pred_refines`. -/

/-- `expr::literal_nat` builds the `NatVal` literal (the `ron::ptr` wrapper is
the identity). -/
private theorem literal_nat_eq {n : ron.nat.Nat} {l : expr.Literal}
    (h : expr.literal_nat n = ok l) : l = .NatVal n := by
  rw [expr.literal_nat] at h
  simp only [bind_eq_ok_iff, ptr_new_eq, Result.ok.injEq, exists_eq_left'] at h
  exact h.symm

/-- **`core_k::nat_lit_to_constructor` refines `natLitToConstructor`**
(`Core.lean:266-272`). -/
theorem nat_lit_to_constructor_refines {n : ron.nat.Nat} {e : expr.Expr}
    (hn : Nat.NatWF n)
    (hzero : PinnedName basis_names.nat_zero_name ConLeche.natZeroName)
    (hsucc : PinnedName basis_names.nat_succ_name ConLeche.natSuccName)
    (h : core_k.nat_lit_to_constructor n = ok e) :
    absExpr e = ConLeche.natLitToConstructor (Nat.toNat n) ∧ ExprWF e := by
  rw [core_k.nat_lit_to_constructor] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  rw [Nat.is_zero_refines hn hb] at h
  by_cases hz : Nat.toNat n = 0
  · simp only [hz, decide_true, if_true] at h
    obtain ⟨n1, hn1, hmk⟩ := bind_eq_ok_iff.mp h
    obtain ⟨habs, hwf⟩ := hzero n1 hn1
    refine ⟨?_, Expr.mk_const_wf hwf levels_wf_new hmk⟩
    rw [Expr.mk_const_refines hmk, habs, absLevels_new, hz]
    rfl
  · simp only [hz, decide_false, Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, e1, hmk, n2, hpred, l, hlit, e2, hlv, happ⟩ := h
    obtain ⟨habs, hwf⟩ := hsucc n1 hn1
    obtain ⟨hpv, hpwf⟩ := Nat.pred_refines hn hpred
    obtain ⟨k, hk⟩ : ∃ k, Nat.toNat n = k + 1 := ⟨Nat.toNat n - 1, by omega⟩
    have hlwf : LiteralWF l := by rw [literal_nat_eq hlit]; exact hpwf
    refine ⟨?_, Expr.app_wf (Expr.mk_const_wf hwf levels_wf_new hmk)
      (Expr.lit_wf hlwf hlv) happ⟩
    rw [Expr.app_refines happ, Expr.mk_const_refines hmk, habs, absLevels_new,
      Expr.lit_refines hlv, literal_nat_eq hlit, hk]
    show _ = ConLeche.Expr.app (.const ConLeche.natSuccName []) (.lit (.natVal k))
    rw [show absLiteral (.NatVal n2) = .natVal k by
      simp only [absLiteral]; rw [hpv, hk]; simp]

/-- **`core_k::raw_nat_lit` refines `rawNatLit?`** (`Core.lean:341-346`); its
`Cached/StateC.lean:98-103` twin `rawNatLitC?` is the same function
(`Expr = Expr`).  The `NatWF` conjunct is what lets a caller feed the answer to
`nat_op_result`. -/
theorem raw_nat_lit_refines {e : expr.Expr} {o : Option ron.nat.Nat} (he : ExprWF e)
    (hzero : PinnedName basis_names.nat_zero_name ConLeche.natZeroName)
    (h : core_k.raw_nat_lit e = ok o) :
    o.map Nat.toNat = ConLeche.rawNatLit? (absExpr e) ∧ ∀ m ∈ o, Nat.NatWF m := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [core_k.raw_nat_lit.eq_def] at h
  simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
  cases k with
  | Const c us =>
    dsimp only at h
    obtain ⟨hcwf, -⟩ := const_wf_inv he rfl
    split at h <;> rename_i hlen
    · have hnil : us.val = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
      simp only [bind_eq_ok_iff] at h
      obtain ⟨n, hn, b, hb, h⟩ := h
      obtain ⟨hnabs, hnwf⟩ := hzero n hn
      rw [Name.beq_refines hcwf hnwf hb, hnabs] at h
      show Option.map Nat.toNat o
          = ConLeche.rawNatLit? (.const (absName c) (absLevels us)) ∧ _
      rw [show absLevels us = [] by simp [absLevels, hnil]]
      simp only [ConLeche.rawNatLit?]
      by_cases hc : absName c = ConLeche.natZeroName
      · simp only [hc, decide_true, if_true, bind_eq_ok_iff] at h ⊢
        obtain ⟨z, hz, ho⟩ := h
        obtain ⟨hzv, hzwf⟩ := Nat.zero_refines hz
        rw [← Result.ok_injective ho]
        exact ⟨by simp [hzv], by intro m hm; simp at hm; rw [← hm]; exact hzwf⟩
      · simp only [hc, decide_false, Bool.false_eq_true, if_false, Result.ok.injEq] at h ⊢
        rw [← h]; simp
    · have hne : us.val ≠ [] := fun hc => hlen (by scalar_tac)
      simp only [Result.ok.injEq] at h
      rw [← h]
      show Option.map Nat.toNat none
          = ConLeche.rawNatLit? (.const (absName c) (absLevels us)) ∧ _
      cases hl : absLevels us with
      | nil => exact absurd (by simpa [absLevels] using hl) hne
      | cons u l => exact ⟨rfl, by simp⟩
  | Lit l =>
    dsimp only at h
    have hlwf : LiteralWF l := lit_wf_inv he rfl
    cases l with
    | NatVal n =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨n2, hcl, ho⟩ := h
      obtain ⟨hlimbs, hval⟩ := Nat.clone_refines hcl
      rw [← Result.ok_injective ho]
      refine ⟨by simp [absLiteral, hval, ConLeche.rawNatLit?], ?_⟩
      intro m hm; simp only [Option.mem_def, Option.some.injEq] at hm
      rw [← hm]
      have hnwf : Nat.NatWF n := hlwf
      simp only [Nat.NatWF, hlimbs]
      exact hnwf
    | StrVal s => simp only [Result.ok.injEq] at h; rw [← h]; exact ⟨rfl, by simp⟩
  | _ => simp only [Result.ok.injEq] at h; rw [← h]; exact ⟨rfl, by simp⟩

/-- The shared body of the two citations, with the guard's *value* abstracted:
`Kernel/Core.lean:334-339`'s `litToCtorIfNat env` reads it as
`natLitSupported env` and `Cached/CoreC.lean:84-90`'s twin `litToCtorIfNatI fe`
(under a `pure`) as `natLitSupportedF fe`; nothing else differs. -/
def litToCtorIfNatBody (supported : Bool) (e : ConLeche.Expr) : ConLeche.Expr :=
  match e with
  | .lit (.natVal n) =>
    if supported then ConLeche.natLitToConstructor n else .lit (.natVal n)
  | e' => e'

theorem litToCtorIfNat_eq (lenv : ConLeche.Env) (e : ConLeche.Expr) :
    ConLeche.litToCtorIfNat lenv e = litToCtorIfNatBody (ConLeche.natLitSupported lenv) e := by
  cases e <;> rfl

/-- **`core_k::lit_to_ctor_if_nat` refines `litToCtorIfNat`**
(`Core.lean:334-339`), stated on `litToCtorIfNatBody` so that it serves both
citations.

The one environment fact the port reads is `core_k::nat_lit_supported`, whose
refinement belongs to task #49's *guards* file; it is taken here as the explicit
hypothesis `hsupp`, which is why no `FindAgree` appears -- `FindAgree` is what
supplies `hsupp` once the guard's lemma lands.  Instantiating `supported` at
`natLitSupported lenv` gives the `Kernel/Core.lean` citation
(`lit_to_ctor_if_nat_refines_env` below); at `natLitSupportedF lfe` it gives the
`Cached/CoreC.lean` twin's body directly. -/
theorem lit_to_ctor_if_nat_refines {fe : fenv.FEnv} {supported : Bool}
    {e r : expr.Expr} (he : ExprWF e)
    (hsupp : ∀ b, core_k.nat_lit_supported fe = ok b → b = supported)
    (hzero : PinnedName basis_names.nat_zero_name ConLeche.natZeroName)
    (hsucc : PinnedName basis_names.nat_succ_name ConLeche.natSuccName)
    (h : core_k.lit_to_ctor_if_nat fe e = ok r) :
    absExpr r = litToCtorIfNatBody supported (absExpr e) ∧ ExprWF r := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [core_k.lit_to_ctor_if_nat.eq_def] at h
  simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
  cases k with
  | Lit l =>
    dsimp only at h
    have hlwf : LiteralWF l := lit_wf_inv he rfl
    cases l with
    | NatVal n =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b, hb, h⟩ := h
      rw [hsupp b hb] at h
      cases supported with
      | true =>
        simp only [if_true] at h
        obtain ⟨habs, hwf⟩ := nat_lit_to_constructor_refines hlwf hzero hsucc h
        exact ⟨by rw [habs]; simp [litToCtorIfNatBody, absLiteral], hwf⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        rw [Expr.dup_eq h]
        exact ⟨by simp [litToCtorIfNatBody, absLiteral], he⟩
    | StrVal s => rw [Expr.dup_eq h]; exact ⟨rfl, he⟩
  | _ => rw [Expr.dup_eq h]; exact ⟨rfl, he⟩

/-- The `Kernel/Core.lean:334-339` citation itself, from the lemma above. -/
theorem lit_to_ctor_if_nat_refines_env {fe : fenv.FEnv} {lenv : ConLeche.Env}
    {e r : expr.Expr} (he : ExprWF e)
    (hsupp : ∀ b, core_k.nat_lit_supported fe = ok b → b = ConLeche.natLitSupported lenv)
    (hzero : PinnedName basis_names.nat_zero_name ConLeche.natZeroName)
    (hsucc : PinnedName basis_names.nat_succ_name ConLeche.natSuccName)
    (h : core_k.lit_to_ctor_if_nat fe e = ok r) :
    absExpr r = ConLeche.litToCtorIfNat lenv (absExpr e) ∧ ExprWF r := by
  obtain ⟨habs, hwf⟩ := lit_to_ctor_if_nat_refines he hsupp hzero hsucc h
  exact ⟨by rw [habs, litToCtorIfNat_eq], hwf⟩

/-- **`core_k::succ_of` refines the packed-literal-against-`Nat.succ` arms of
`defeqStep`** (`Core.lean:2371-2631`, the `match nn, f with | k + 1, .const c []
=> if c = natSuccName ...` of `:2524-2534`): the predecessor, when the literal is
positive and the function part is the bare `Nat.succ`. -/
theorem succ_of_refines {nn : ron.nat.Nat} {f : expr.Expr} {o : Option ron.nat.Nat}
    (hnn : Nat.NatWF nn) (hf : ExprWF f)
    (hsucc : PinnedName basis_names.nat_succ_name ConLeche.natSuccName)
    (h : core_k.succ_of nn f = ok o) :
    o.map Nat.toNat =
        (match Nat.toNat nn, absExpr f with
          | k + 1, .const c [] => if c = ConLeche.natSuccName then some k else none
          | _, _ => none) ∧
      ∀ m ∈ o, Nat.NatWF m := by
  rw [core_k.succ_of.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  rw [Nat.is_zero_refines hnn hb] at h
  by_cases hz : Nat.toNat nn = 0
  · simp only [hz, decide_true, if_true, Result.ok.injEq] at h
    rw [← h, hz]
    exact ⟨rfl, by simp⟩
  · simp only [hz, decide_false, Bool.false_eq_true, if_false] at h
    obtain ⟨k, hk⟩ : ∃ k, Nat.toNat nn = k + 1 := ⟨Nat.toNat nn - 1, by omega⟩
    obtain ⟨⟨d, kk⟩⟩ := f
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    cases kk with
    | Const c us =>
      dsimp only at h
      obtain ⟨hcwf, -⟩ := const_wf_inv hf rfl
      split at h <;> rename_i hlen
      · have hnil : us.val = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
        simp only [bind_eq_ok_iff] at h
        obtain ⟨n, hn, b1, hb1, h⟩ := h
        obtain ⟨hnabs, hnwf⟩ := hsucc n hn
        rw [Name.beq_refines hcwf hnwf hb1, hnabs] at h
        show Option.map Nat.toNat o
            = (match Nat.toNat nn, ConLeche.Expr.const (absName c) (absLevels us) with
                | k + 1, .const c [] => if c = ConLeche.natSuccName then some k else none
                | _, _ => none) ∧ _
        rw [hk, show absLevels us = [] by simp [absLevels, hnil]]
        simp only []
        by_cases hc : absName c = ConLeche.natSuccName
        · simp only [hc, decide_true, if_true, bind_eq_ok_iff] at h ⊢
          obtain ⟨p, hp, ho⟩ := h
          obtain ⟨hpv, hpwf⟩ := Nat.pred_refines hnn hp
          rw [← Result.ok_injective ho]
          refine ⟨by simp only [Option.map_some]; rw [hpv, hk]; simp, ?_⟩
          intro m hm; simp only [Option.mem_def, Option.some.injEq] at hm
          rw [← hm]; exact hpwf
        · simp only [hc, decide_false, Bool.false_eq_true, if_false, Result.ok.injEq] at h ⊢
          rw [← h]; simp
      · have hne : us.val ≠ [] := fun hc => hlen (by scalar_tac)
        simp only [Result.ok.injEq] at h
        rw [← h]
        show Option.map Nat.toNat none
            = (match Nat.toNat nn, ConLeche.Expr.const (absName c) (absLevels us) with
                | k + 1, .const c [] => if c = ConLeche.natSuccName then some k else none
                | _, _ => none) ∧ _
        rw [hk]
        cases hl : absLevels us with
        | nil => exact absurd (by simpa [absLevels] using hl) hne
        | cons u l => exact ⟨rfl, by simp⟩
    | _ =>
      simp only [Result.ok.injEq] at h
      rw [← h, hk]
      exact ⟨rfl, by simp⟩

/-! ## String literals

`Core.lean:360-371` -- `strLitToConstructor`.  The cited `s.toList.foldr` is the
port's downward index recursion `str_lit_cons_from`, so the statement is on
`s.val.take i` in the task-#5 accumulator shape: at `i = s.len()` that is the
whole list, which is `str_lit_to_constructor`.

The one real content is the code point: the cited Lean builds
`Char.ofNat (lit c.toNat)` from the `Char`s of the `String`, while the port's
code point *is* `c.toNat` (DESIGN.md §3.3).  `StrWF s` -- every stored word is a
valid code point -- is what makes `(Char.ofNat c.val).toNat = c.val`, i.e. what
makes the two agree. -/

/-- The cited `foldr`'s step: one `List.cons.{0} Char (Char.ofNat (lit c)) ·`
cell. -/
def strCell (c : Char) (e : ConLeche.Expr) : ConLeche.Expr :=
  .app (.app (.app (.const ConLeche.listConsName [.zero]) (.const ConLeche.charName []))
    (.app (.const ConLeche.charOfNatName []) (.lit (.natVal c.toNat)))) e

/-- The cited `foldr`'s `init`: `List.nil.{0} Char`. -/
def strInit : ConLeche.Expr :=
  .app (.const ConLeche.listNilName [.zero]) (.const ConLeche.charName [])

/-- The cited definition, in the `strCell`/`strInit` spelling. -/
theorem strLitToConstructor_eq (s : String) :
    ConLeche.strLitToConstructor s =
      .app (.const ConLeche.stringOfListName []) (s.toList.foldr strCell strInit) := rfl

/-- A `u32`-to-`u64` cast is the identity on values (the port narrows a code
point to the bignum's machine word). -/
private theorem u32_cast_u64_val (x : Std.U32) : (Std.UScalar.cast .U64 x).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_greater_numBits_eq _ _ ?_
  decide

/-- A valid code point survives `Char.ofNat`. -/
private theorem toNat_ofNat_of_valid {n : Nat} (h : Nat.isValidChar n) : (Char.ofNat n).toNat = n := by
  rw [Char.ofNat, dif_pos h, Char.ofNatAux, Char.toNat]
  show (BitVec.ofNatLT n _).toNat = n
  simp

/-- A `level::singleton level::zero` is con-leche's `[.zero]`. -/
private theorem levels_zero_singleton {u : level.Level} {v : alloc.vec.Vec level.Level}
    (hu : level.zero = ok u) (h : level.singleton u = ok v) :
    absLevels v = [ConLeche.Level.zero] ∧ LevelsWF v := by
  rw [level.singleton] at h
  refine ⟨by rw [absLevels, vec_push_val h]; simp [Level.zero_refines hu], ?_⟩
  intro w hw
  rw [vec_push_val h] at hw
  simp at hw
  rw [hw]; exact LevelWF.zero hu

/-- **`core_k::str_lit_cons_from` refines the cited `foldr`**
(`Core.lean:360-371`), in the task-#5 accumulator shape: the answer is the
`foldr` over `s[0..i]` applied to the accumulator. -/
theorem str_lit_cons_from_refines (N : Nat) :
    ∀ (s : alloc.vec.Vec Std.U32) (i : Std.Usize) (acc r : expr.Expr),
      i.val = N → i.val ≤ s.val.length → StrWF s → ExprWF acc →
      PinnedName basis_names.char_name ConLeche.charName →
      PinnedName basis_names.char_of_nat_name ConLeche.charOfNatName →
      PinnedName basis_names.list_cons_name ConLeche.listConsName →
      core_k.str_lit_cons_from s i acc = ok r →
      absExpr r =
          ((s.val.take i.val).map fun c => Char.ofNat c.val).foldr strCell (absExpr acc) ∧
        ExprWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s i acc r hN hle hs hacc hchar hofnat hcons h
    rw [core_k.str_lit_cons_from.eq_def] at h
    split at h <;> rename_i hi0
    · have : i.val = 0 := by scalar_tac
      rw [← Result.ok_injective h, this]
      exact ⟨by simp, hacc⟩
    · have hipos : 0 < i.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, c, hidx, n, hn, e, hmke, i2, hi2, n1, hfrom, l, hlit, e1, hlv,
        ch, hch, n2, hn2, l1, hl1, v, hv, e2, hmke2, n3, hn3, e3, hmke3,
        e4, hap4, e5, hap5, cell, hcell, hrec⟩ := h
      have hi1v : i1.val = i.val - 1 := by
        have := Nat.usub_val hi1; simp at this; omega
      -- the indexed word and its validity
      have hg := ExprOps.vec_index_getElem? hidx
      have hlt : i1.val < s.val.length := by omega
      have hcv : s.val[i1.val] = c := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hvalid : Nat.isValidChar c.val := hs c (by rw [← hcv]; exact List.getElem_mem hlt)
      -- the `Char.ofNat` cell the port builds
      obtain ⟨hnabs, hnwf⟩ := hofnat n hn
      obtain ⟨h2abs, h2wf⟩ := hcons n2 hn2
      obtain ⟨h3abs, h3wf⟩ := hchar n3 hn3
      obtain ⟨hvabs, hvwf⟩ := levels_zero_singleton hl1 hv
      have hi2v : i2.val = c.val := by
        simp only [lift_eq, Result.ok.injEq] at hi2
        rw [← hi2, u32_cast_u64_val]
      obtain ⟨hfv, hfwf⟩ := Nat.from_u64_refines hfrom
      have hlwf : LiteralWF l := by rw [literal_nat_eq hlit]; exact hfwf
      have he1wf : ExprWF e1 := Expr.lit_wf hlwf hlv
      have hchwf : ExprWF ch :=
        Expr.app_wf (Expr.mk_const_wf hnwf levels_wf_new hmke) he1wf hch
      have he2wf : ExprWF e2 := Expr.mk_const_wf h2wf hvwf hmke2
      have he3wf : ExprWF e3 := Expr.mk_const_wf h3wf levels_wf_new hmke3
      have he4wf : ExprWF e4 := Expr.app_wf he2wf he3wf hap4
      have he5wf : ExprWF e5 := Expr.app_wf he4wf hchwf hap5
      have hcellwf : ExprWF cell := Expr.app_wf he5wf hacc hcell
      have hcellabs : absExpr cell = strCell (Char.ofNat c.val) (absExpr acc) := by
        rw [Expr.app_refines hcell, Expr.app_refines hap5, Expr.app_refines hap4,
          Expr.mk_const_refines hmke2, Expr.mk_const_refines hmke3,
          Expr.app_refines hch, Expr.mk_const_refines hmke, Expr.lit_refines hlv,
          literal_nat_eq hlit, h2abs, h3abs, hnabs, hvabs, absLevels_new]
        rw [strCell, toNat_ofNat_of_valid hvalid]
        simp only [absLiteral]
        rw [hfv, hi2v]
      obtain ⟨habs, hwf⟩ :=
        ih i1.val (by omega) s i1 cell r rfl (by omega) hs hcellwf hchar hofnat hcons hrec
      refine ⟨?_, hwf⟩
      rw [habs, hcellabs,
        show s.val.take i.val = s.val.take i1.val ++ [c] by
          rw [show i.val = i1.val + 1 by omega, List.take_add_one,
            List.getElem?_eq_getElem hlt, hcv]; simp]
      simp

/-- **`core_k::str_lit_to_constructor` refines `strLitToConstructor`**
(`Core.lean:360-371`). -/
theorem str_lit_to_constructor_refines {s : alloc.vec.Vec Std.U32} {r : expr.Expr}
    (hs : StrWF s)
    (hchar : PinnedName basis_names.char_name ConLeche.charName)
    (hofnat : PinnedName basis_names.char_of_nat_name ConLeche.charOfNatName)
    (hnil : PinnedName basis_names.list_nil_name ConLeche.listNilName)
    (hcons : PinnedName basis_names.list_cons_name ConLeche.listConsName)
    (hofl : PinnedName basis_names.string_of_list_name ConLeche.stringOfListName)
    (h : core_k.str_lit_to_constructor s = ok r) :
    absExpr r = ConLeche.strLitToConstructor (absString s) ∧ ExprWF r := by
  rw [core_k.str_lit_to_constructor] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, l, hl, v, hv, e, hmke, n1, hn1, e1, hmke1, init, hinit,
    n2, hn2, e2, hmke2, e3, hgo, happ⟩ := h
  obtain ⟨hnabs, hnwf⟩ := hnil n hn
  obtain ⟨h1abs, h1wf⟩ := hchar n1 hn1
  obtain ⟨h2abs, h2wf⟩ := hofl n2 hn2
  obtain ⟨hvabs, hvwf⟩ := levels_zero_singleton hl hv
  have hinitwf : ExprWF init :=
    Expr.app_wf (Expr.mk_const_wf hnwf hvwf hmke) (Expr.mk_const_wf h1wf levels_wf_new hmke1) hinit
  have hinitabs : absExpr init = strInit := by
    rw [Expr.app_refines hinit, Expr.mk_const_refines hmke, Expr.mk_const_refines hmke1,
      hnabs, h1abs, hvabs, absLevels_new]
    rfl
  obtain ⟨habs, hwf⟩ := str_lit_cons_from_refines (alloc.vec.Vec.len s).val s
    (alloc.vec.Vec.len s) init e3 rfl (by scalar_tac) hs hinitwf hchar hofnat hcons hgo
  refine ⟨?_, Expr.app_wf (Expr.mk_const_wf h2wf levels_wf_new hmke2) hwf happ⟩
  rw [Expr.app_refines happ, Expr.mk_const_refines hmke2, h2abs, absLevels_new,
    habs, hinitabs, strLitToConstructor_eq]
  have hlen : (alloc.vec.Vec.len s).val = s.val.length := by scalar_tac
  rw [hlen, List.take_length]
  rw [show (absString s).toList = s.val.map fun c => Char.ofNat c.val by simp [absString]]

/-! ## The `Nat`-operation fast path

`Core.lean:628-654` -- `natOpResult`, **the headline lemma of this file**.  The
port is a fifteen-rung `if name::beq c &nat_X_name()` cascade over `ron::nat`'s
arithmetic; `op_step` below turns one rung into the cited `if c = natXName`
(this is where `name::beq`'s exactness is spent), the `natOpResult_*` bank
evaluates the cited cascade at each pinned name, and `lit_arm_done` /
`const_arm_done` close an arm from the corresponding `Refine/Nat.lean` lemma.
No arithmetic is re-proved here. -/

/-- The cited cascade at each pinned name.  `simp +decide` is what decides the
fourteen name *dis*equalities of a rung (the names are closed `Name` terms). -/
theorem natOpResult_pred (A B : Nat) :
    ConLeche.natOpResult ConLeche.natPredName A B = some (.lit (.natVal (A - 1))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_add (A B : Nat) :
    ConLeche.natOpResult ConLeche.natAddName A B = some (.lit (.natVal (A + B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_sub (A B : Nat) :
    ConLeche.natOpResult ConLeche.natSubName A B = some (.lit (.natVal (A - B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_mul (A B : Nat) :
    ConLeche.natOpResult ConLeche.natMulName A B = some (.lit (.natVal (A * B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_pow (A B : Nat) :
    ConLeche.natOpResult ConLeche.natPowName A B =
      (if B > 16777216 then none else some (.lit (.natVal (A ^ B)))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_div (A B : Nat) :
    ConLeche.natOpResult ConLeche.natDivName A B = some (.lit (.natVal (A / B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_mod (A B : Nat) :
    ConLeche.natOpResult ConLeche.natModName A B = some (.lit (.natVal (A % B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_gcd (A B : Nat) :
    ConLeche.natOpResult ConLeche.natGcdName A B = some (.lit (.natVal (Nat.gcd A B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_land (A B : Nat) :
    ConLeche.natOpResult ConLeche.natLandName A B = some (.lit (.natVal (Nat.land A B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_lor (A B : Nat) :
    ConLeche.natOpResult ConLeche.natLorName A B = some (.lit (.natVal (Nat.lor A B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_xor (A B : Nat) :
    ConLeche.natOpResult ConLeche.natXorName A B = some (.lit (.natVal (Nat.xor A B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_shl (A B : Nat) :
    ConLeche.natOpResult ConLeche.natShiftLeftName A B =
      some (.lit (.natVal (Nat.shiftLeft A B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_shr (A B : Nat) :
    ConLeche.natOpResult ConLeche.natShiftRightName A B =
      some (.lit (.natVal (Nat.shiftRight A B))) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_beq (A B : Nat) :
    ConLeche.natOpResult ConLeche.natBeqName A B =
      some (.const (if A = B then ConLeche.boolTrueName else ConLeche.boolFalseName) []) := by
  simp +decide [ConLeche.natOpResult]

theorem natOpResult_ble (A B : Nat) :
    ConLeche.natOpResult ConLeche.natBleName A B =
      some (.const (if A ≤ B then ConLeche.boolTrueName else ConLeche.boolFalseName) []) := by
  simp +decide [ConLeche.natOpResult]

/-- The cited cascade's fall-through: a name that is none of the fifteen. -/
theorem natOpResult_none {c : ConLeche.Name} (A B : Nat)
    (h1 : c ≠ ConLeche.natPredName) (h2 : c ≠ ConLeche.natAddName)
    (h3 : c ≠ ConLeche.natSubName) (h4 : c ≠ ConLeche.natMulName)
    (h5 : c ≠ ConLeche.natPowName) (h6 : c ≠ ConLeche.natDivName)
    (h7 : c ≠ ConLeche.natModName) (h8 : c ≠ ConLeche.natGcdName)
    (h9 : c ≠ ConLeche.natLandName) (h10 : c ≠ ConLeche.natLorName)
    (h11 : c ≠ ConLeche.natXorName) (h12 : c ≠ ConLeche.natShiftLeftName)
    (h13 : c ≠ ConLeche.natShiftRightName) (h14 : c ≠ ConLeche.natBeqName)
    (h15 : c ≠ ConLeche.natBleName) :
    ConLeche.natOpResult c A B = none := by
  simp [ConLeche.natOpResult, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

/-- **One rung of the port's cascade.**  `if name::beq c &nat_X_name()` is the
cited `if c = natXName`, exactly: `Refine/Name.lean`'s `beq_refines` on a
well-formed name and the rung's `PinnedName`. -/
theorem op_step {α : Type} {f : Result name.Name} {ln : ConLeche.Name} {c : name.Name}
    {A B : Result α} {o : α}
    (hpin : PinnedName f ln) (hc : NameWF c)
    (h : (do let n ← f; let bb ← name.beq c n; if bb then A else B) = ok o) :
    (absName c = ln ∧ A = ok o) ∨ (absName c ≠ ln ∧ B = ok o) := by
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := hpin n hn
  rw [Name.beq_refines hc hwf hbb, habs] at h
  by_cases hcl : absName c = ln
  · rw [hcl] at h
    simp only [decide_true, if_true] at h
    exact Or.inl ⟨hcl, h⟩
  · simp only [hcl, decide_false, Bool.false_eq_true, if_false] at h
    exact Or.inr ⟨hcl, h⟩

/-- **The conclusion of `nat_op_result_refines`**, named because every arm
proves it.  Two clauses rather than one `Option.map` equation only because the
`some` arm also carries `ExprWF`; both directions are **exact** (task #61: the
port's one escape, a `shiftLeft`/`shiftRight` amount beyond `u64`, is a failure
and not a `none`, and task #67 places that failure in the `Native` class, which
`nat_op_result_native` claims and `ErrSim.of_none` consumes). -/
def OpSpec (c : name.Name) (a b : ron.nat.Nat) (o : Option expr.Expr) : Prop :=
  (∀ e, o = some e →
      ConLeche.natOpResult (absName c) (Nat.toNat a) (Nat.toNat b) = some (absExpr e) ∧
        ExprWF e) ∧
    (o = none → ConLeche.natOpResult (absName c) (Nat.toNat a) (Nat.toNat b) = none)

/-- The value `nat_op_result` now answers in (task #61): an `Option` under a
`CheckError`, so that a shift amount beyond `u64` can *fail* rather than
decline.  The `.Err` half of that outcome is `nat_op_result_native`'s: a port
`Native`, never a mirrored kind (task #67). -/
abbrev OpRes := core.result.Result (Option expr.Expr) core_types.CheckError

/-- A literal-producing arm: `expr::lit (expr::literal_nat ·)` of a bignum whose
value is the cited one. -/
theorem lit_arm_done {c : name.Name} {a b n : ron.nat.Nat} {o : Option expr.Expr} {x : Nat}
    (hspec : ConLeche.natOpResult (absName c) (Nat.toNat a) (Nat.toNat b)
      = some (.lit (.natVal x)))
    (hn : Nat.NatWF n) (hx : Nat.toNat n = x)
    (h : (do let l ← expr.literal_nat n; let e ← expr.lit l
             ok (core.result.Result.Ok (some e) : OpRes)) = ok (.Ok o)) :
    OpSpec c a b o := by
  simp only [bind_eq_ok_iff] at h
  obtain ⟨l, hlit, e, hlv, ho⟩ := h
  have ho' : o = some e := by simpa using (Result.ok_injective ho).symm
  have hlwf : LiteralWF l := by rw [literal_nat_eq hlit]; exact hn
  have habs : absExpr e = ConLeche.Expr.lit (.natVal x) := by
    rw [Expr.lit_refines hlv, literal_nat_eq hlit]
    simp only [absLiteral]
    rw [hx]
  refine ⟨?_, by rw [ho']; simp⟩
  intro e' he'
  rw [ho', Option.some.injEq] at he'
  subst he'
  exact ⟨by rw [hspec, habs], Expr.lit_wf hlwf hlv⟩

/-- A constant-producing arm (`beq`/`ble`): `expr::mk_const` of a pinned `Bool`
constructor. -/
theorem const_arm_done {c n : name.Name} {a b : ron.nat.Nat} {o : Option expr.Expr}
    {ln : ConLeche.Name}
    (hspec : ConLeche.natOpResult (absName c) (Nat.toNat a) (Nat.toNat b)
      = some (.const ln []))
    (hnabs : absName n = ln) (hnwf : NameWF n)
    (h : (do let e ← expr.mk_const n (alloc.vec.Vec.new level.Level)
             ok (core.result.Result.Ok (some e) : OpRes)) = ok (.Ok o)) :
    OpSpec c a b o := by
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, hmk, ho⟩ := h
  have ho' : o = some e := by simpa using (Result.ok_injective ho).symm
  refine ⟨?_, by rw [ho']; simp⟩
  intro e' he'
  rw [ho', Option.some.injEq] at he'
  subst he'
  refine ⟨?_, Expr.mk_const_wf hnwf levels_wf_new hmk⟩
  rw [hspec, Expr.mk_const_refines hmk, hnabs, absLevels_new]

/-- An arm that declines: the port answered `none`, and so does the cited
`natOpResult`. -/
theorem none_arm_done {c : name.Name} {a b : ron.nat.Nat} {o : Option expr.Expr}
    (h : (ok (.Ok none) : Result OpRes) = ok (.Ok o))
    (hn : ConLeche.natOpResult (absName c) (Nat.toNat a) (Nat.toNat b) = none) :
    OpSpec c a b o := by
  have ho : o = none := by
    have := Result.ok_injective h; simpa using this.symm
  exact ⟨by intro e he; rw [ho] at he; simp at he, fun _ => hn⟩

/-- **One rung of the port's cascade, with the rung's name forgotten.**
`op_step` without the `PinnedName`/`NameWF` hypotheses: the failure half never
needs to know *which* rung fired, only that control reached one of the two
branches. -/
private theorem rung {α : Type} {f : Result name.Name} {c : name.Name}
    {A B : Result α} {o : α}
    (h : (do let n ← f; let bb ← name.beq c n; if bb then A else B) = ok o) :
    A = ok o ∨ B = ok o := by
  obtain ⟨n, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bb, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · exact Or.inl h
  · exact Or.inr h

/-- **A `Native` leaf**: the port builds a message and hands it to
`core_types::native`, so the error abstracts to nothing. -/
private theorem native_leaf {α : Type} {ce : core_types.CheckError}
    {ms : Result (Slice Std.U32)}
    (h : (do let s ← ms; let v ← core_types.code_points s
             let e ← core_types.native v
             ok (core.result.Result.Err e : core.result.Result α core_types.CheckError))
      = ok (.Err ce)) : absErrKind ce = none := by
  obtain ⟨s, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  rw [core_types.native] at he
  rw [← Result.ok_injective he] at h
  have hce : core_types.CheckError.Native v = ce := by simpa using Result.ok_injective h
  rw [← hce]
  rfl

/-- **`core_k::nat_op_result`'s failure half is the port's own** (`core_k.rs:1651`
and `:1656`, the two `shiftLeft`/`shiftRight` amounts beyond `u64`).
`ConLeche.natOpResult` (`Core.lean:628-654`) is *total* -- it has no `throw` at
all -- so there is nothing to mirror, and what the lemma claims is exactly that:
the error is the port's own `Native`, i.e. `absErrKind ce = none`, which a caller
turns into `ErrSim` against whatever con-leche side it is looking at by
`ErrSim.of_none`.  These are two of task #67's census's thirty-one native sites
and the only two in `core_k.rs`.

No hypothesis is needed: the proof walks the cascade and observes that every
`Err` leaf in it is `core_types::native`'s. -/
theorem nat_op_result_native {c : name.Name} {a b : ron.nat.Nat}
    {ce : core_types.CheckError}
    (h : core_k.nat_op_result c a b = ok (.Err ce)) : absErrKind ce = none := by
  rw [core_k.nat_op_result] at h
  -- pred, add, sub, mul: a literal each, no failure
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  -- pow: the S2 bound and the narrowing both *decline*, they do not fail
  rcases rung h with h | h
  · exfalso
    obtain ⟨_, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact absurd h (by simp)
    · obtain ⟨oo, -, h⟩ := bind_eq_ok_iff.mp h
      cases oo <;> exact absurd h (by simp [bind_eq_ok_iff])
  -- div, mod, gcd, land, lor, xor
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  -- shiftLeft (`core_k.rs:1651`) and shiftRight (`:1656`): the port's own
  -- failures, and the only two in the cascade
  rcases rung h with h | h
  · obtain ⟨oo, -, h⟩ := bind_eq_ok_iff.mp h
    cases oo with
    | none => exact native_leaf h
    | some k => exact absurd h (by simp [bind_eq_ok_iff])
  rcases rung h with h | h
  · obtain ⟨oo, -, h⟩ := bind_eq_ok_iff.mp h
    cases oo with
    | none => exact native_leaf h
    | some k => exact absurd h (by simp [bind_eq_ok_iff])
  -- beq, ble, and the fall-through
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  rcases rung h with h | h
  · exact absurd h (by simp [bind_eq_ok_iff])
  exact absurd h (by simp)

/-- **`core_k::nat_op_result` refines `natOpResult`** (`Core.lean:628-654`): the
reduct of op `c` on literal arguments, `pred` ignoring the second slot.

The port's one remaining deviation is in the direction of declining and is the
cited `b > 16777216` guard on `pow` (the audit's S2 bound), which is mirrored
exactly; the port then narrows the exponent to `u64` for `nat::pow`, and the
narrowing cannot fail under the bound, so that arm too is an *exact*
refinement.

`shiftLeft`/`shiftRight` take a `u64` shift amount.  Task #61: on an amount
beyond `u64` the port **fails** rather than answering `none`, where a `none`
would have been a different verdict.  Task #67 made that failure the port's own
`Native` (`Err (native "shift amount beyond u64")`), which claims nothing about
con-leche --- `nat_op_result_native` is the failure half.  The accept lemma is
therefore exact in both directions.

Every arithmetic operation is `Refine/Nat.lean`'s, used as a black box.

Stated over the full outcome (task #67): the `Ok` arm is the accept direction,
and the `Err` arm delegates to `nat_op_result_native` just above -- the port's
own `Native`, which claims nothing about con-leche.  `nat_op_result_native`
stays a theorem of its own rather than a corollary of this one because it needs
none of the four hypotheses below. -/
theorem nat_op_result_refines {c : name.Name} {a b : ron.nat.Nat} {r : OpRes}
    (hc : NameWF c) (ha : Nat.NatWF a) (hb : Nat.NatWF b) (hpin : NatOpPinned)
    (h : core_k.nat_op_result c a b = ok r) :
    match r with
    | .Ok o => OpSpec c a b o
    | .Err ce => absErrKind ce = none := by
  cases r with
  | Err ce => exact nat_op_result_native h
  | Ok o =>
    show OpSpec c a b o
    rw [core_k.nat_op_result] at h
    -- pred
    rcases op_step hpin.pred hc h with ⟨hc1, h⟩ | ⟨hc1, h⟩
    · obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      exact lit_arm_done (by rw [hc1]; exact natOpResult_pred _ _)
        (Nat.pred_refines ha hp).2 (Nat.pred_refines ha hp).1 h
    -- add
    rcases op_step hpin.add hc h with ⟨hc2, h⟩ | ⟨hc2, h⟩
    · obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      exact lit_arm_done (by rw [hc2]; exact natOpResult_add _ _)
        (Nat.add_refines hp).2 (Nat.add_refines hp).1 h
    -- sub
    rcases op_step hpin.sub hc h with ⟨hc3, h⟩ | ⟨hc3, h⟩
    · obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      exact lit_arm_done (by rw [hc3]; exact natOpResult_sub _ _)
        (Nat.sub_refines ha hb hp).2 (Nat.sub_refines ha hb hp).1 h
    -- mul
    rcases op_step hpin.mul hc h with ⟨hc4, h⟩ | ⟨hc4, h⟩
    · obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      exact lit_arm_done (by rw [hc4]; exact natOpResult_mul _ _)
        (Nat.mul_refines hp).2 (Nat.mul_refines hp).1 h
    -- pow: the S2 bound, then the narrowing (which the bound makes total)
    rcases op_step hpin.pow hc h with ⟨hc5, h⟩ | ⟨hc5, h⟩
    · obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨bl, hbl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hlimv, hlimwf⟩ := Nat.from_u64_refines hlim
      have hlimn : Nat.toNat lim = 16777216 := by rw [hlimv]; scalar_tac
      rw [Nat.blt_refines hlimwf hb hbl] at h
      by_cases hgt : Nat.toNat lim < Nat.toNat b
      · simp only [hgt, decide_true, if_true] at h
        refine none_arm_done h ?_
        rw [hc5, natOpResult_pow, if_pos (by omega)]
      · simp only [hgt, decide_false, Bool.false_eq_true, if_false] at h
        obtain ⟨oo, hoo, h⟩ := bind_eq_ok_iff.mp h
        cases oo with
        | none =>
          rcases Nat.to_u64_refines hb hoo with ⟨x, hx, -⟩ | ⟨-, hge⟩
          · simp at hx
          · omega
        | some ex =>
          rcases Nat.to_u64_refines hb hoo with ⟨x, hx, hxv⟩ | ⟨hn, -⟩
          · simp only [Option.some.injEq] at hx
            subst hx
            simp only [] at h
            obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hpv, hpwf⟩ := Nat.pow_refines ex.val a p ex rfl hp
            refine lit_arm_done (c := c) ?_ hpwf (by rw [hpv, hxv]) h
            rw [hc5, natOpResult_pow, if_neg (by omega)]
          · simp at hn
    -- div
    rcases op_step hpin.div hc h with ⟨hc6, h⟩ | ⟨hc6, h⟩
    · obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      exact lit_arm_done (by rw [hc6]; exact natOpResult_div _ _)
        (Nat.div_refines ha hb hp).2 (Nat.div_refines ha hb hp).1 h
    -- mod
    rcases op_step hpin.mod hc h with ⟨hc7, h⟩ | ⟨hc7, h⟩
    · obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      exact lit_arm_done (by rw [hc7]; exact natOpResult_mod _ _)
        (Nat.modulo_refines ha hb hp).2 (Nat.modulo_refines ha hb hp).1 h
    -- gcd
    rcases op_step hpin.gcd hc h with ⟨hc8, h⟩ | ⟨hc8, h⟩
    · obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      exact lit_arm_done (by rw [hc8]; exact natOpResult_gcd _ _)
        (Nat.gcd_refines (Nat.toNat a) a b p rfl ha hb hp).2
        (Nat.gcd_refines (Nat.toNat a) a b p rfl ha hb hp).1 h
    -- land
    rcases op_step hpin.land hc h with ⟨hc9, h⟩ | ⟨hc9, h⟩
    · obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      exact lit_arm_done (by rw [hc9]; exact natOpResult_land _ _)
        (Nat.land_refines hp).2 (Nat.land_refines hp).1 h
    -- lor
    rcases op_step hpin.lor hc h with ⟨hc10, h⟩ | ⟨hc10, h⟩
    · obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      exact lit_arm_done (by rw [hc10]; exact natOpResult_lor _ _)
        (Nat.lor_refines hp).2 (Nat.lor_refines hp).1 h
    -- xor
    rcases op_step hpin.xor hc h with ⟨hc11, h⟩ | ⟨hc11, h⟩
    · obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      exact lit_arm_done (by rw [hc11]; exact natOpResult_xor _ _)
        (Nat.xor_refines hp).2 (Nat.xor_refines hp).1 h
    -- shiftLeft: task #61 -- an amount beyond `u64` FAILS, so the `none` arm of
    -- `nat::to_u64` cannot produce an `ok` and there is nothing to prove there
    rcases op_step hpin.shl hc h with ⟨hc12, h⟩ | ⟨hc12, h⟩
    · obtain ⟨oo, hoo, h⟩ := bind_eq_ok_iff.mp h
      cases oo with
      | none => exfalso; simp [bind_eq_ok_iff] at h
      | some k =>
        rcases Nat.to_u64_refines hb hoo with ⟨x, hx, hxv⟩ | ⟨hn, -⟩
        · simp only [Option.some.injEq] at hx
          subst hx
          simp only [] at h
          obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hpv, hpwf⟩ := Nat.shift_left_refines hp
          exact lit_arm_done (by rw [hc12]; exact natOpResult_shl _ _) hpwf
            (by rw [hpv, hxv]) h
        · simp at hn
    -- shiftRight: likewise
    rcases op_step hpin.shr hc h with ⟨hc13, h⟩ | ⟨hc13, h⟩
    · obtain ⟨oo, hoo, h⟩ := bind_eq_ok_iff.mp h
      cases oo with
      | none => exfalso; simp [bind_eq_ok_iff] at h
      | some k =>
        rcases Nat.to_u64_refines hb hoo with ⟨x, hx, hxv⟩ | ⟨hn, -⟩
        · simp only [Option.some.injEq] at hx
          subst hx
          simp only [] at h
          obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hpv, hpwf⟩ := Nat.shift_right_refines hp
          exact lit_arm_done (by rw [hc13]; exact natOpResult_shr _ _) hpwf
            (by rw [hpv, hxv]) h
        · simp at hn
    -- beq
    rcases op_step hpin.beq hc h with ⟨hc14, h⟩ | ⟨hc14, h⟩
    · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
      rw [Nat.beq_refines ha hb hbb] at hnm
      by_cases hab : Nat.toNat a = Nat.toNat b
      · simp only [hab, decide_true, if_true] at hnm
        obtain ⟨hnabs, hnwf⟩ := hpin.boolTrue nm hnm
        refine const_arm_done (c := c) ?_ hnabs hnwf h
        rw [hc14, natOpResult_beq, if_pos hab]
      · simp only [hab, decide_false, Bool.false_eq_true, if_false] at hnm
        obtain ⟨hnabs, hnwf⟩ := hpin.boolFalse nm hnm
        refine const_arm_done (c := c) ?_ hnabs hnwf h
        rw [hc14, natOpResult_beq, if_neg hab]
    -- ble
    rcases op_step hpin.ble hc h with ⟨hc15, h⟩ | ⟨hc15, h⟩
    · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨nm, hnm, h⟩ := bind_eq_ok_iff.mp h
      rw [Nat.ble_refines ha hb hbb] at hnm
      by_cases hab : Nat.toNat a ≤ Nat.toNat b
      · simp only [hab, decide_true, if_true] at hnm
        obtain ⟨hnabs, hnwf⟩ := hpin.boolTrue nm hnm
        refine const_arm_done (c := c) ?_ hnabs hnwf h
        rw [hc15, natOpResult_ble, if_pos hab]
      · simp only [hab, decide_false, Bool.false_eq_true, if_false] at hnm
        obtain ⟨hnabs, hnwf⟩ := hpin.boolFalse nm hnm
        refine const_arm_done (c := c) ?_ hnabs hnwf h
        rw [hc15, natOpResult_ble, if_neg hab]
    -- the fall-through
    exact none_arm_done h
      (natOpResult_none _ _ hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12 hc13
        hc14 hc15)

/-! ## The equation table

`Core.lean:597-626` -- `natOpEquations`, the defining recurrence equations of a
structural-`Nat` operation over constructor forms with free variables `d`,
`d + 1`.  The cited block's `let`-bound locals are spelled out below as
`eqNatTy`/`eqX`/`eqY`/`eqZ`/`eqS`/`eqAp1`/`eqAp2`/`eqBT`/`eqBF` (the port names
the three closures as functions, §3.4), the `natOpEquations_*` bank evaluates
the cited seven-rung cascade at each pinned name, and the arms are then a
transcription: `expr::dup` is the identity, so each pair is exactly one of the
cited ones. -/

/-- The port's `Vec::new` is the empty list. -/
@[local simp] private theorem vec_new_val {α : Type} : (alloc.vec.Vec.new α).val = [] := rfl

/-- The `let`-bound locals of the cited `natOpEquations` block. -/
def eqNatTy : ConLeche.Expr := .const ConLeche.natName []
def eqX (D : Nat) : ConLeche.Expr := .fvar D eqNatTy
def eqY (D : Nat) : ConLeche.Expr := .fvar (D + 1) eqNatTy
def eqZ : ConLeche.Expr := .const ConLeche.natZeroName []
def eqS (a : ConLeche.Expr) : ConLeche.Expr := .app (.const ConLeche.natSuccName []) a
def eqAp1 (n : ConLeche.Name) (a : ConLeche.Expr) : ConLeche.Expr := .app (.const n []) a
def eqAp2 (n : ConLeche.Name) (a b : ConLeche.Expr) : ConLeche.Expr :=
  .app (.app (.const n []) a) b
def eqBT : ConLeche.Expr := .const ConLeche.boolTrueName []
def eqBF : ConLeche.Expr := .const ConLeche.boolFalseName []

/-! The cited cascade at each pinned name. -/

theorem natOpEquations_pred (D : Nat) :
    ConLeche.natOpEquations D ConLeche.natPredName =
      [(eqAp1 ConLeche.natPredName eqZ, eqZ),
       (eqAp1 ConLeche.natPredName (eqS (eqX D)), eqX D)] := by
  simp +decide [ConLeche.natOpEquations, eqAp1, eqZ, eqS, eqX, eqNatTy]

theorem natOpEquations_add (D : Nat) :
    ConLeche.natOpEquations D ConLeche.natAddName =
      [(eqAp2 ConLeche.natAddName (eqX D) eqZ, eqX D),
       (eqAp2 ConLeche.natAddName (eqX D) (eqS (eqY D)),
        eqS (eqAp2 ConLeche.natAddName (eqX D) (eqY D)))] := by
  simp +decide [ConLeche.natOpEquations, eqAp2, eqZ, eqS, eqX, eqY, eqNatTy]

theorem natOpEquations_sub (D : Nat) :
    ConLeche.natOpEquations D ConLeche.natSubName =
      [(eqAp2 ConLeche.natSubName (eqX D) eqZ, eqX D),
       (eqAp2 ConLeche.natSubName (eqX D) (eqS (eqY D)),
        eqAp1 ConLeche.natPredName (eqAp2 ConLeche.natSubName (eqX D) (eqY D)))] := by
  simp +decide [ConLeche.natOpEquations, eqAp1, eqAp2, eqZ, eqS, eqX, eqY, eqNatTy]

theorem natOpEquations_mul (D : Nat) :
    ConLeche.natOpEquations D ConLeche.natMulName =
      [(eqAp2 ConLeche.natMulName (eqX D) eqZ, eqZ),
       (eqAp2 ConLeche.natMulName (eqX D) (eqS (eqY D)),
        eqAp2 ConLeche.natAddName (eqAp2 ConLeche.natMulName (eqX D) (eqY D)) (eqX D))] := by
  simp +decide [ConLeche.natOpEquations, eqAp2, eqZ, eqS, eqX, eqY, eqNatTy]

theorem natOpEquations_pow (D : Nat) :
    ConLeche.natOpEquations D ConLeche.natPowName =
      [(eqAp2 ConLeche.natPowName (eqX D) eqZ, eqS eqZ),
       (eqAp2 ConLeche.natPowName (eqX D) (eqS (eqY D)),
        eqAp2 ConLeche.natMulName (eqAp2 ConLeche.natPowName (eqX D) (eqY D)) (eqX D))] := by
  simp +decide [ConLeche.natOpEquations, eqAp2, eqZ, eqS, eqX, eqY, eqNatTy]

theorem natOpEquations_beq (D : Nat) :
    ConLeche.natOpEquations D ConLeche.natBeqName =
      [(eqAp2 ConLeche.natBeqName eqZ eqZ, eqBT),
       (eqAp2 ConLeche.natBeqName eqZ (eqS (eqY D)), eqBF),
       (eqAp2 ConLeche.natBeqName (eqS (eqX D)) eqZ, eqBF),
       (eqAp2 ConLeche.natBeqName (eqS (eqX D)) (eqS (eqY D)),
        eqAp2 ConLeche.natBeqName (eqX D) (eqY D))] := by
  simp +decide [ConLeche.natOpEquations, eqAp2, eqZ, eqS, eqX, eqY, eqBT, eqBF, eqNatTy]

theorem natOpEquations_ble (D : Nat) :
    ConLeche.natOpEquations D ConLeche.natBleName =
      [(eqAp2 ConLeche.natBleName eqZ (eqY D), eqBT),
       (eqAp2 ConLeche.natBleName (eqS (eqX D)) eqZ, eqBF),
       (eqAp2 ConLeche.natBleName (eqS (eqX D)) (eqS (eqY D)),
        eqAp2 ConLeche.natBleName (eqX D) (eqY D))] := by
  simp +decide [ConLeche.natOpEquations, eqAp2, eqZ, eqS, eqX, eqY, eqBT, eqBF, eqNatTy]

theorem natOpEquations_none {c : ConLeche.Name} (D : Nat)
    (h1 : c ≠ ConLeche.natPredName) (h2 : c ≠ ConLeche.natAddName)
    (h3 : c ≠ ConLeche.natSubName) (h4 : c ≠ ConLeche.natMulName)
    (h5 : c ≠ ConLeche.natPowName) (h6 : c ≠ ConLeche.natBeqName)
    (h7 : c ≠ ConLeche.natBleName) :
    ConLeche.natOpEquations D c = [] := by
  simp [ConLeche.natOpEquations, h1, h2, h3, h4, h5, h6, h7]

/-! The `Vec::push` chains the port builds the list with. -/

private theorem eqs_two {p q : expr.Expr × expr.Expr} {w v : alloc.vec.Vec (expr.Expr × expr.Expr)}
    (h1 : alloc.vec.Vec.push (alloc.vec.Vec.new (expr.Expr × expr.Expr)) p = ok w)
    (h2 : alloc.vec.Vec.push w q = ok v) : v.val = [p, q] := by
  rw [vec_push_val h2, vec_push_val h1]; simp

private theorem eqs_three {p q r : expr.Expr × expr.Expr}
    {w w2 v : alloc.vec.Vec (expr.Expr × expr.Expr)}
    (h1 : alloc.vec.Vec.push (alloc.vec.Vec.new (expr.Expr × expr.Expr)) p = ok w)
    (h2 : alloc.vec.Vec.push w q = ok w2) (h3 : alloc.vec.Vec.push w2 r = ok v) :
    v.val = [p, q, r] := by
  rw [vec_push_val h3, vec_push_val h2, vec_push_val h1]; simp

private theorem eqs_four {p q r s : expr.Expr × expr.Expr}
    {w w2 w3 v : alloc.vec.Vec (expr.Expr × expr.Expr)}
    (h1 : alloc.vec.Vec.push (alloc.vec.Vec.new (expr.Expr × expr.Expr)) p = ok w)
    (h2 : alloc.vec.Vec.push w q = ok w2) (h3 : alloc.vec.Vec.push w2 r = ok w3)
    (h4 : alloc.vec.Vec.push w3 s = ok v) : v.val = [p, q, r, s] := by
  rw [vec_push_val h4, vec_push_val h3, vec_push_val h2, vec_push_val h1]; simp

/-- **`core_k::nat_op_equations` refines `natOpEquations`**
(`Core.lean:597-626`): the list of abstracted pairs is the cited list, exactly,
and every `Expr` in it is well formed. -/
theorem nat_op_equations_refines {d : Std.U64} {c : name.Name}
    {v : alloc.vec.Vec (expr.Expr × expr.Expr)}
    (hc : NameWF c) (hpin : NatOpPinned)
    (hnat : PinnedName basis_names.nat_name ConLeche.natName)
    (hzero : PinnedName basis_names.nat_zero_name ConLeche.natZeroName)
    (hsucc : PinnedName basis_names.nat_succ_name ConLeche.natSuccName)
    (h : core_k.nat_op_equations d c = ok v) :
    v.val.map (fun p => (absExpr p.1, absExpr p.2))
        = ConLeche.natOpEquations d.val (absName c) ∧
      ∀ p ∈ v.val, ExprWF p.1 ∧ ExprWF p.2 := by
  rw [core_k.nat_op_equations] at h
  -- the prelude: `natTy`, `x`, `y`, `z`, `bT`, `bF`
  obtain ⟨nn, hnn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨nat_ty, hnat_ty, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e0, hdup, h⟩ := bind_eq_ok_iff.mp h
  rw [Expr.dup_eq hdup] at h
  obtain ⟨x, hxmk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨y, hymk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨z, hzmk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n2, hn2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b_t, hbtmk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n3, hn3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b_f, hbfmk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnnabs, hnnwf⟩ := hnat nn hnn
  have hnattywf : ExprWF nat_ty := Expr.mk_const_wf hnnwf levels_wf_new hnat_ty
  have hnatty : absExpr nat_ty = eqNatTy := by
    rw [Expr.mk_const_refines hnat_ty, hnnabs, absLevels_new]; rfl
  have hxwf : ExprWF x := Expr.fvar_wf hnattywf hxmk
  have hxabs : absExpr x = eqX d.val := by rw [Expr.fvar_refines hxmk, hnatty]; rfl
  have hiv : i.val = d.val + 1 := by have := Nat.uadd_val hi; simpa using this
  have hywf : ExprWF y := Expr.fvar_wf hnattywf hymk
  have hyabs : absExpr y = eqY d.val := by
    rw [Expr.fvar_refines hymk, hnatty, hiv]; rfl
  obtain ⟨h1abs, h1wf⟩ := hzero n1 hn1
  have hzwf : ExprWF z := Expr.mk_const_wf h1wf levels_wf_new hzmk
  have hzabs : absExpr z = eqZ := by
    rw [Expr.mk_const_refines hzmk, h1abs, absLevels_new]; rfl
  obtain ⟨h2abs, h2wf⟩ := hpin.boolTrue n2 hn2
  have hbtwf : ExprWF b_t := Expr.mk_const_wf h2wf levels_wf_new hbtmk
  have hbtabs : absExpr b_t = eqBT := by
    rw [Expr.mk_const_refines hbtmk, h2abs, absLevels_new]; rfl
  obtain ⟨h3abs, h3wf⟩ := hpin.boolFalse n3 hn3
  have hbfwf : ExprWF b_f := Expr.mk_const_wf h3wf levels_wf_new hbfmk
  have hbfabs : absExpr b_f = eqBF := by
    rw [Expr.mk_const_refines hbfmk, h3abs, absLevels_new]; rfl
  -- the cascade
  obtain ⟨n4, hn4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hn4abs, hn4wf⟩ := hpin.pred n4 hn4
  rw [Name.beq_refines hc hn4wf hbb, hn4abs] at h
  by_cases hc1 : absName c = ConLeche.natPredName
  · rw [hc1] at h
    simp only [decide_true, if_true, bind_eq_ok_iff, expr_dup_eq, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨e2, ha2, eqs, hp1, e4, ha4, e5, ha5, hp2⟩ := h
    obtain ⟨ha2abs, ha2wf⟩ := nat_eq_ap1_refines hc hzwf ha2
    obtain ⟨ha4abs, ha4wf⟩ := nat_eq_s_refines hxwf hsucc ha4
    obtain ⟨ha5abs, ha5wf⟩ := nat_eq_ap1_refines hc ha4wf ha5
    rw [eqs_two hp1 hp2]
    refine ⟨?_, ?_⟩
    · rw [hc1, natOpEquations_pred]
      simp only [List.map_cons, List.map_nil]
      rw [ha2abs, ha5abs, ha4abs, hxabs, hzabs, hc1]
      rfl
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      exacts [⟨ha2wf, hzwf⟩, ⟨ha5wf, hxwf⟩]
  simp only [hc1, decide_false, Bool.false_eq_true, if_false] at h
  obtain ⟨n5, hn5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bb1, hbb1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hn5abs, hn5wf⟩ := hpin.add n5 hn5
  rw [Name.beq_refines hc hn5wf hbb1, hn5abs] at h
  by_cases hc2 : absName c = ConLeche.natAddName
  · rw [hc2] at h
    simp only [decide_true, if_true, bind_eq_ok_iff, expr_dup_eq, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨e3, ha3, eqs, hp1, e5, ha5, e6, ha6, e7, ha7, e8, ha8, hp2⟩ := h
    obtain ⟨ha3abs, ha3wf⟩ := nat_eq_ap2_refines hc hxwf hzwf ha3
    obtain ⟨ha5abs, ha5wf⟩ := nat_eq_s_refines hywf hsucc ha5
    obtain ⟨ha6abs, ha6wf⟩ := nat_eq_ap2_refines hc hxwf ha5wf ha6
    obtain ⟨ha7abs, ha7wf⟩ := nat_eq_ap2_refines hc hxwf hywf ha7
    obtain ⟨ha8abs, ha8wf⟩ := nat_eq_s_refines ha7wf hsucc ha8
    rw [eqs_two hp1 hp2]
    refine ⟨?_, ?_⟩
    · rw [hc2, natOpEquations_add]
      simp only [List.map_cons, List.map_nil]
      rw [ha3abs, ha6abs, ha8abs, ha7abs, ha5abs, hxabs, hyabs, hzabs, hc2]
      rfl
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      exacts [⟨ha3wf, hxwf⟩, ⟨ha6wf, ha8wf⟩]
  simp only [hc2, decide_false, Bool.false_eq_true, if_false] at h
  obtain ⟨n6, hn6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bb2, hbb2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hn6abs, hn6wf⟩ := hpin.sub n6 hn6
  rw [Name.beq_refines hc hn6wf hbb2, hn6abs] at h
  by_cases hc3 : absName c = ConLeche.natSubName
  · rw [hc3] at h
    simp only [decide_true, if_true, bind_eq_ok_iff, expr_dup_eq, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨e3, ha3, eqs, hp1, e5, ha5, e6, ha6, e7, ha7, e8, ha8, hp2⟩ := h
    obtain ⟨ha3abs, ha3wf⟩ := nat_eq_ap2_refines hc hxwf hzwf ha3
    obtain ⟨ha5abs, ha5wf⟩ := nat_eq_s_refines hywf hsucc ha5
    obtain ⟨ha6abs, ha6wf⟩ := nat_eq_ap2_refines hc hxwf ha5wf ha6
    obtain ⟨ha7abs, ha7wf⟩ := nat_eq_ap2_refines hc hxwf hywf ha7
    obtain ⟨ha8abs, ha8wf⟩ := nat_eq_ap1_refines hn4wf ha7wf ha8
    rw [eqs_two hp1 hp2]
    refine ⟨?_, ?_⟩
    · rw [hc3, natOpEquations_sub]
      simp only [List.map_cons, List.map_nil]
      rw [ha3abs, ha6abs, ha8abs, ha7abs, ha5abs, hxabs, hyabs, hzabs, hc3, hn4abs]
      rfl
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      exacts [⟨ha3wf, hxwf⟩, ⟨ha6wf, ha8wf⟩]
  simp only [hc3, decide_false, Bool.false_eq_true, if_false] at h
  obtain ⟨n7, hn7, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bb3, hbb3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hn7abs, hn7wf⟩ := hpin.mul n7 hn7
  rw [Name.beq_refines hc hn7wf hbb3, hn7abs] at h
  by_cases hc4 : absName c = ConLeche.natMulName
  · rw [hc4] at h
    simp only [decide_true, if_true, bind_eq_ok_iff, expr_dup_eq, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨e3, ha3, eqs, hp1, e5, ha5, e6, ha6, e7, ha7, e8, ha8, hp2⟩ := h
    obtain ⟨ha3abs, ha3wf⟩ := nat_eq_ap2_refines hc hxwf hzwf ha3
    obtain ⟨ha5abs, ha5wf⟩ := nat_eq_s_refines hywf hsucc ha5
    obtain ⟨ha6abs, ha6wf⟩ := nat_eq_ap2_refines hc hxwf ha5wf ha6
    obtain ⟨ha7abs, ha7wf⟩ := nat_eq_ap2_refines hc hxwf hywf ha7
    obtain ⟨ha8abs, ha8wf⟩ := nat_eq_ap2_refines hn5wf ha7wf hxwf ha8
    rw [eqs_two hp1 hp2]
    refine ⟨?_, ?_⟩
    · rw [hc4, natOpEquations_mul]
      simp only [List.map_cons, List.map_nil]
      rw [ha3abs, ha6abs, ha8abs, ha7abs, ha5abs, hxabs, hyabs, hzabs, hc4, hn5abs]
      rfl
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      exacts [⟨ha3wf, hzwf⟩, ⟨ha6wf, ha8wf⟩]
  simp only [hc4, decide_false, Bool.false_eq_true, if_false] at h
  obtain ⟨n8, hn8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bb4, hbb4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hn8abs, hn8wf⟩ := hpin.pow n8 hn8
  rw [Name.beq_refines hc hn8wf hbb4, hn8abs] at h
  by_cases hc5 : absName c = ConLeche.natPowName
  · rw [hc5] at h
    simp only [decide_true, if_true, bind_eq_ok_iff, expr_dup_eq, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨e3, ha3, e4, ha4, eqs, hp1, e6, ha6, e7, ha7, e8, ha8, e9, ha9, hp2⟩ := h
    obtain ⟨ha3abs, ha3wf⟩ := nat_eq_ap2_refines hc hxwf hzwf ha3
    obtain ⟨ha4abs, ha4wf⟩ := nat_eq_s_refines hzwf hsucc ha4
    obtain ⟨ha6abs, ha6wf⟩ := nat_eq_s_refines hywf hsucc ha6
    obtain ⟨ha7abs, ha7wf⟩ := nat_eq_ap2_refines hc hxwf ha6wf ha7
    obtain ⟨ha8abs, ha8wf⟩ := nat_eq_ap2_refines hc hxwf hywf ha8
    obtain ⟨ha9abs, ha9wf⟩ := nat_eq_ap2_refines hn7wf ha8wf hxwf ha9
    rw [eqs_two hp1 hp2]
    refine ⟨?_, ?_⟩
    · rw [hc5, natOpEquations_pow]
      simp only [List.map_cons, List.map_nil]
      rw [ha3abs, ha4abs, ha7abs, ha9abs, ha8abs, ha6abs, hxabs, hyabs, hzabs, hc5, hn7abs]
      rfl
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      exacts [⟨ha3wf, ha4wf⟩, ⟨ha7wf, ha9wf⟩]
  simp only [hc5, decide_false, Bool.false_eq_true, if_false] at h
  obtain ⟨n9, hn9, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bb5, hbb5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hn9abs, hn9wf⟩ := hpin.beq n9 hn9
  rw [Name.beq_refines hc hn9wf hbb5, hn9abs] at h
  by_cases hc6 : absName c = ConLeche.natBeqName
  · rw [hc6] at h
    simp only [decide_true, if_true, bind_eq_ok_iff, expr_dup_eq, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨e2, ha2, eqs, hp1, e5, ha5, e6, ha6, eqs1, hp2, e9, ha9, e10, ha10,
      eqs2, hp3, e11, ha11, e12, ha12, e13, ha13, e14, ha14, hp4⟩ := h
    obtain ⟨ha2abs, ha2wf⟩ := nat_eq_ap2_refines hc hzwf hzwf ha2
    obtain ⟨ha5abs, ha5wf⟩ := nat_eq_s_refines hywf hsucc ha5
    obtain ⟨ha6abs, ha6wf⟩ := nat_eq_ap2_refines hc hzwf ha5wf ha6
    obtain ⟨ha9abs, ha9wf⟩ := nat_eq_s_refines hxwf hsucc ha9
    obtain ⟨ha10abs, ha10wf⟩ := nat_eq_ap2_refines hc ha9wf hzwf ha10
    obtain ⟨ha11abs, ha11wf⟩ := nat_eq_s_refines hxwf hsucc ha11
    obtain ⟨ha12abs, ha12wf⟩ := nat_eq_s_refines hywf hsucc ha12
    obtain ⟨ha13abs, ha13wf⟩ := nat_eq_ap2_refines hc ha11wf ha12wf ha13
    obtain ⟨ha14abs, ha14wf⟩ := nat_eq_ap2_refines hc hxwf hywf ha14
    rw [eqs_four hp1 hp2 hp3 hp4]
    refine ⟨?_, ?_⟩
    · rw [hc6, natOpEquations_beq]
      simp only [List.map_cons, List.map_nil]
      rw [ha2abs, ha6abs, ha10abs, ha13abs, ha14abs, ha5abs, ha9abs, ha11abs, ha12abs,
        hxabs, hyabs, hzabs, hbtabs, hbfabs, hc6]
      rfl
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      exacts [⟨ha2wf, hbtwf⟩, ⟨ha6wf, hbfwf⟩, ⟨ha10wf, hbfwf⟩, ⟨ha13wf, ha14wf⟩]
  simp only [hc6, decide_false, Bool.false_eq_true, if_false] at h
  obtain ⟨n10, hn10, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bb6, hbb6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hn10abs, hn10wf⟩ := hpin.ble n10 hn10
  rw [Name.beq_refines hc hn10wf hbb6, hn10abs] at h
  by_cases hc7 : absName c = ConLeche.natBleName
  · rw [hc7] at h
    simp only [decide_true, if_true, bind_eq_ok_iff, expr_dup_eq, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨e3, ha3, eqs, hp1, e6, ha6, e7, ha7, eqs1, hp2, e9, ha9, e10, ha10,
      e11, ha11, e12, ha12, hp3⟩ := h
    obtain ⟨ha3abs, ha3wf⟩ := nat_eq_ap2_refines hc hzwf hywf ha3
    obtain ⟨ha6abs, ha6wf⟩ := nat_eq_s_refines hxwf hsucc ha6
    obtain ⟨ha7abs, ha7wf⟩ := nat_eq_ap2_refines hc ha6wf hzwf ha7
    obtain ⟨ha9abs, ha9wf⟩ := nat_eq_s_refines hxwf hsucc ha9
    obtain ⟨ha10abs, ha10wf⟩ := nat_eq_s_refines hywf hsucc ha10
    obtain ⟨ha11abs, ha11wf⟩ := nat_eq_ap2_refines hc ha9wf ha10wf ha11
    obtain ⟨ha12abs, ha12wf⟩ := nat_eq_ap2_refines hc hxwf hywf ha12
    rw [eqs_three hp1 hp2 hp3]
    refine ⟨?_, ?_⟩
    · rw [hc7, natOpEquations_ble]
      simp only [List.map_cons, List.map_nil]
      rw [ha3abs, ha7abs, ha11abs, ha12abs, ha6abs, ha9abs, ha10abs,
        hxabs, hyabs, hzabs, hbtabs, hbfabs, hc7]
      rfl
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      exacts [⟨ha3wf, hbtwf⟩, ⟨ha7wf, hbfwf⟩, ⟨ha11wf, ha12wf⟩]
  simp only [hc7, decide_false, Bool.false_eq_true, if_false, Result.ok.injEq] at h
  rw [← h]
  exact ⟨by rw [natOpEquations_none _ hc1 hc2 hc3 hc4 hc5 hc6 hc7]; rfl, by simp⟩

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The headline lemma: nothing beyond Lean's own three -- no Aeneas library axiom,
nothing from the `Arc` model, nothing from con-leche. -/

/--
info: 'ConRon.Refine.CoreK.nat_op_result_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nat_op_result_refines

end ConRon.Refine.CoreK
