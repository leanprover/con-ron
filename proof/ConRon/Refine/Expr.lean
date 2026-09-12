/-
`ConRon.Refine.Expr` -- the refinement lemmas of
`crates/con-ron-core/src/kernel/expr.rs` against `ConLeche/Kernel/Expr.lean`
from `BinderMeta` on (DESIGN.md §3.5; P3.3 of §5, task #20).  The `Level` half
of that con-leche file is `ConRon/Refine/Level.lean`.

Shape, as fixed by task #5: **exact result on success**.  `ptr_eq` is `false`
in the model (DESIGN.md §3.2), so `beq_refl` is what makes the real program's
fast path agree, and `absExpr_injective` is what makes `beq` *exact*.

## The data word, bit for bit

This is the one module where the port's stored word and con-leche's
`@[computed_field] data` have to be related, and only the **observed** bits can
be: the hash field is `mixHash`-derived on both sides and `mixHash` is opaque
in Lean (DESIGN.md §3.2), while the port hashes its own `Nat`s and strings
anyway.  So `hash` gets no refinement lemma, and the three readers that *are*
observed (`has_lp`, `bvar_b_raw`, `fvar_b_raw`) are proved against con-leche's
`Expr.hasLP`/`bvarBRaw`/`fvarBRaw` through `wf_data`, whose proof is *by the
shape of `packData`* and never by a hash value:

* `pack_bits` is the port's roundtrip lemma -- `packData h b f lp` read back
  at bits 30…16, 15…1 and 0 is `b`, `f`, `lp` whenever the two range fields
  fit in 15 bits, whatever `h` is.  con-leche's own `bvarOfData_pack` and its
  thirty `@[simp]` constructor equations (`bvarBRaw_app`, `hasLP_lam`, …) are
  the same fact on the other side;
* `wf_data` then runs the two recurrences in lock step over an `ExprWF`
  derivation.  Both `packData`s are the same arithmetic, so every case is
  `pack_bits` plus the matching con-leche equation.

Since `absExpr` drops the word, `absExpr_injective` (and with it `beq_exact`)
needs the *whole* word to be a function of the abstraction -- which it is,
because a well-formed node is by definition what a smart constructor built
from its children, and equal children give an equal call.
-/
import ConRon.Refine.Level
import ConRon.Refine.PropWhen

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Expr

/-! ## The stored word as a field read -/

/-- The node's packed word (`expr::data` is this read in the `Result` monad). -/
def dataOf (e : expr.Expr) : Std.U64 := e._0.data

@[simp] theorem data_eq (e : expr.Expr) : expr.data e = ok (dataOf e) := by
  simp [expr.data, dataOf]

@[simp] theorem dataOf_mk (d : Std.U64) (k : expr.ExprKind) :
    dataOf (.mk (.mk d k)) = d := rfl

/-- Bits 30…16 of the stored word: the saturating loose-bvar bound. -/
def bvarBits (e : expr.Expr) : Nat := (dataOf e).val / 65536 % 32768

/-- Bits 15…1 of the stored word: the saturating fvar range. -/
def fvarBits (e : expr.Expr) : Nat := (dataOf e).val / 2 % 32768

/-- Bit 0 of the stored word: has-level-param. -/
def lpBit (e : expr.Expr) : Bool := (dataOf e).val % 2 == 1

theorem bvarBits_lt (e : expr.Expr) : bvarBits e < 32768 := by
  simp only [bvarBits]; omega

theorem fvarBits_lt (e : expr.Expr) : fvarBits e < 32768 := by
  simp only [fvarBits]; omega

/-! ## The packed word's arithmetic

Lean's `UInt64` `*`/`+` wrap, so the port uses `wrapping_mul`/`wrapping_add`
(task #11); these two lemmas are all that is needed of them. -/

/-- The five `u64` literals the packing arithmetic uses, as `Nat`s: `omega`
needs them substituted, or `x.val * (4294967296#u64).val` is a product of two
unknowns to it. -/
@[simp] theorem val_2_32 : ((4294967296#u64) : Std.U64).val = 4294967296 := rfl
@[simp] theorem val_2_16 : ((65536#u64) : Std.U64).val = 65536 := rfl
@[simp] theorem val_two : ((2#u64) : Std.U64).val = 2 := rfl
@[simp] theorem val_zero : ((0#u64) : Std.U64).val = 0 := rfl
@[simp] theorem val_one : ((1#u64) : Std.U64).val = 1 := rfl

theorem wrapping_mul_val (x y : Std.U64) :
    (core.num.U64.wrapping_mul x y).val = x.val * y.val % 2 ^ 64 := by
  show (core.num.U64.wrapping_mul x y).bv.toNat = _
  simp only [core.num.U64.wrapping_mul_bv_eq, BitVec.toNat_mul]
  rfl

theorem wrapping_add_val (x y : Std.U64) :
    (core.num.U64.wrapping_add x y).val = (x.val + y.val) % 2 ^ 64 := by
  show (core.num.U64.wrapping_add x y).bv.toNat = _
  simp only [core.num.U64.wrapping_add_bv_eq, BitVec.toNat_add]
  rfl

/-- `expr::pack_data` in normal form: the hash field truncated to 32 bits,
then the two ranges and the flag.  Nothing is assumed about `h`. -/
theorem pack_val {h b f w : Std.U64} {lp : Bool}
    (hb : b.val < 32768) (hf : f.val < 32768)
    (hw : expr.pack_data h b f lp = ok w) :
    w.val = h.val % 4294967296 * 4294967296 + b.val * 65536 + f.val * 2
      + (if lp then 1 else 0) := by
  have hh : h.val < 2 ^ 64 := by scalar_tac
  rw [expr.pack_data.eq_def] at hw
  cases lp <;>
    simp only [Bool.false_eq_true, if_false, if_true, lift_eq, bind_tc_ok,
      Result.ok.injEq] at hw ⊢ <;>
    rw [← hw] <;>
    simp only [wrapping_add_val, wrapping_mul_val, val_2_32, val_2_16, val_two,
      val_zero, val_one] <;>
    omega

/-- The port's roundtrip lemma: the three *observed* fields of a packed word
are what was packed, whatever the hash field holds.  con-leche's
`bvarOfData_pack`/`fvarOfData_pack`/`lpOfData_pack` are the same fact. -/
theorem pack_bits {h b f w : Std.U64} {lp : Bool}
    (hb : b.val < 32768) (hf : f.val < 32768)
    (hw : expr.pack_data h b f lp = ok w) :
    w.val / 65536 % 32768 = b.val ∧ w.val / 2 % 32768 = f.val ∧
      w.val % 2 = if lp then 1 else 0 := by
  have hv := pack_val hb hf hw
  cases lp <;>
    simp only [Bool.false_eq_true, if_false, if_true] at hv ⊢ <;>
    exact ⟨by omega, by omega, by omega⟩

/-- The `lpBit`-shaped reading of `pack_bits`'s third component. -/
theorem lpBit_eq {w : Std.U64} {lp : Bool} (h : w.val % 2 = if lp then 1 else 0) :
    (w.val % 2 == 1) = lp := by
  cases lp <;> simp_all

/-! ## Forward readings of the word helpers -/

theorem sat_range_val {r : Std.U64} (h : expr.sat_range = ok r) :
    r.val = ConLeche.satRange := by
  rw [expr.sat_range, Result.ok.injEq] at h; rw [← h]; rfl

theorem max_u64_val {a b r : Std.U64} (h : expr.max_u64 a b = ok r) :
    r.val = max a.val b.val := by
  rw [expr.max_u64.eq_def] at h
  split at h <;> rename_i hlt <;> simp only [Result.ok.injEq] at h <;>
    rw [← h] <;> scalar_tac

theorem hash_of_data_val {w r : Std.U64} (h : expr.hash_of_data w = ok r) :
    r.val = w.val / 4294967296 := by
  rw [expr.hash_of_data] at h
  simpa using Nat.udiv_val h

theorem hash32_val {w r : Std.U64} (h : expr.hash32 w = ok r) :
    r.val = w.val % 4294967296 := by
  rw [expr.hash32] at h
  simpa using Nat.urem_val h

theorem bvar_of_data_val {w r : Std.U64} (h : expr.bvar_of_data w = ok r) :
    r.val = w.val / 65536 % 32768 := by
  rw [expr.bvar_of_data] at h
  obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
  rw [Nat.urem_val h, Nat.udiv_val hy]; rfl

theorem fvar_of_data_val {w r : Std.U64} (h : expr.fvar_of_data w = ok r) :
    r.val = w.val / 2 % 32768 := by
  rw [expr.fvar_of_data] at h
  obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
  rw [Nat.urem_val h, Nat.udiv_val hy]; rfl

theorem lp_of_data_val {w : Std.U64} {b : Bool} (h : expr.lp_of_data w = ok b) :
    b = (w.val % 2 == 1) := by
  rw [expr.lp_of_data] at h
  obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  have hyv : y.val = w.val % 2 := by simpa using Nat.urem_val hy
  rw [← h]
  by_cases hc : y = 1#u64
  · have h1 : w.val % 2 = 1 := by rw [← hyv, hc]; rfl
    simp [hc, h1]
  · have h1 : w.val % 2 ≠ 1 := by
      intro hcc
      exact hc (Std.UScalar.eq_of_val_eq (by rw [hyv, hcc]; rfl))
    simp [hc, h1]

/-- `expr::sat_succ` is con-leche's `satSucc` at `Nat` level: the deviation of
task #11 (the saturation test first, so that `n + 1` cannot overflow a `u64`)
is the same function of the same value. -/
theorem sat_succ_val {n r : Std.U64} (h : expr.sat_succ n = ok r) :
    r.val = min (n.val + 1) ConLeche.satRange := by
  rw [expr.sat_succ.eq_def] at h
  simp only [ConLeche.satRange]
  split at h <;> rename_i hge
  · simp only [Result.ok.injEq] at h
    rw [← h]
    have h2 : 32766 ≤ n.val := by scalar_tac
    scalar_tac
  · have hv := Nat.uadd_val h
    have h2 : n.val < 32766 := by scalar_tac
    scalar_tac

/-- `expr::sat_pred` is con-leche's `satPred` at `Nat` level. -/
theorem sat_pred_val {x r : Std.U64} (h : expr.sat_pred x = ok r) :
    r.val = if x.val = ConLeche.satRange then ConLeche.satRange else x.val - 1 := by
  rw [expr.sat_pred.eq_def] at h
  split at h <;> rename_i h1
  · simp only [Result.ok.injEq] at h
    have h1' : x.val = ConLeche.satRange := by rw [h1]; rfl
    rw [← h, if_pos h1']
    rfl
  · have h1' : x.val ≠ ConLeche.satRange := by
      intro hc
      exact h1 (Std.UScalar.eq_of_val_eq (by simp only [hc]; rfl))
    split at h <;> rename_i h2
    · simp only [Result.ok.injEq] at h
      have h2' : x.val = 0 := by rw [h2]; rfl
      rw [← h, if_neg h1']
      scalar_tac
    · obtain ⟨-, hv⟩ := Nat.usub_val h
      rw [if_neg h1', hv]
      scalar_tac


/-! ## Smart-constructor shapes

Every `*_inv` says what node the port's smart constructor built *and* what the
three observed fields of its word are, in terms of the children's.  Together
they are the port's half of con-leche's thirty `bvarBRaw_*`/`fvarBRaw_*`/
`hasLP_*` equations; `wf_data` below is the two halves put side by side.  The
fields a leaf helper computes (`level_has_param`, `levels_have_param`,
`has_params`) are left as a hypothesis rather than an existential, so that the
lemma says nothing about *whether* the helper was called (`lam`'s `||` chain
short-circuits). -/

/-- The three field reads, at a node's own word. -/
theorem bvar_bits_val {e : expr.Expr} {r : Std.U64}
    (h : expr.bvar_of_data (dataOf e) = ok r) : r.val = bvarBits e :=
  bvar_of_data_val h

theorem fvar_bits_val {e : expr.Expr} {r : Std.U64}
    (h : expr.fvar_of_data (dataOf e) = ok r) : r.val = fvarBits e :=
  fvar_of_data_val h

theorem lp_bit_val {e : expr.Expr} {b : Bool}
    (h : expr.lp_of_data (dataOf e) = ok b) : b = lpBit e :=
  lp_of_data_val h

/-- The last two steps of every smart constructor: pack the word, allocate. -/
theorem node_bits {h b f d : Std.U64} {lp : Bool} {k : expr.ExprKind}
    (hb : b.val < 32768) (hf : f.val < 32768)
    (hd : expr.pack_data h b f lp = ok d) :
    bvarBits (.mk (.mk d k)) = b.val ∧ fvarBits (.mk (.mk d k)) = f.val ∧
      lpBit (.mk (.mk d k)) = lp := by
  obtain ⟨h1, h2, h3⟩ := pack_bits hb hf hd
  simp only [bvarBits, fvarBits, lpBit, dataOf_mk]
  exact ⟨h1, h2, lpBit_eq h3⟩

theorem bvar_inv {i : Std.U64} {e : expr.Expr} (h : expr.bvar i = ok e) :
    ∃ d, e = .mk (.mk d (.Bvar i)) ∧
      bvarBits e = min (i.val + 1) ConLeche.satRange ∧ fvarBits e = 0 ∧
      lpBit e = false := by
  rw [expr.bvar.eq_def] at h
  simp only [bind_eq_ok_iff, rc_new_eq, Result.ok.injEq] at h
  obtain ⟨_, -, _, -, _, -, i3, hi3, d, hd, _, hnd, he⟩ := h
  subst hnd; subst he
  have hs := sat_succ_val hi3
  have hlt : i3.val < 32768 := by simp only [ConLeche.satRange] at hs; omega
  obtain ⟨b1, b2, b3⟩ := node_bits (k := .Bvar i) hlt (by scalar_tac) hd
  exact ⟨d, rfl, by rw [b1, hs], by rw [b2]; rfl, b3⟩

theorem fvar_inv {idx : Std.U64} {ty e : expr.Expr} (h : expr.fvar idx ty = ok e) :
    ∃ d, e = .mk (.mk d (.Fvar idx ty)) ∧ bvarBits e = 0 ∧
      fvarBits e = min (idx.val + 1) ConLeche.satRange ∧ lpBit e = lpBit ty := by
  rw [expr.fvar.eq_def] at h
  simp only [bind_eq_ok_iff, rc_new_eq, data_eq, Result.ok.injEq] at h
  obtain ⟨dt, hdt, _, -, _, -, _, -, _, -, _, -, i4, hi4, bb, hbb, d, hd, _, hnd, he⟩ := h
  subst hdt; subst hnd; subst he
  have hs := sat_succ_val hi4
  have hlt : i4.val < 32768 := by simp only [ConLeche.satRange] at hs; omega
  obtain ⟨b1, b2, b3⟩ := node_bits (k := .Fvar idx ty) (by scalar_tac) hlt hd
  exact ⟨d, rfl, by rw [b1]; rfl, by rw [b2, hs], by rw [b3, lp_bit_val hbb]⟩

theorem sort_inv {u : level.Level} {e : expr.Expr} (h : expr.sort u = ok e) :
    ∃ d b, level.level_has_param u = ok b ∧ e = .mk (.mk d (.«Sort» u)) ∧
      bvarBits e = 0 ∧ fvarBits e = 0 ∧ lpBit e = b := by
  rw [expr.sort.eq_def] at h
  simp only [bind_eq_ok_iff, rc_new_eq, Result.ok.injEq] at h
  obtain ⟨_, -, _, -, _, -, bb, hbb, d, hd, _, hnd, he⟩ := h
  subst hnd; subst he
  obtain ⟨b1, b2, b3⟩ := node_bits (k := .«Sort» u) (by scalar_tac) (by scalar_tac) hd
  exact ⟨d, bb, hbb, rfl, by rw [b1]; rfl, by rw [b2]; rfl, b3⟩

theorem mk_const_inv {n : name.Name} {us : alloc.vec.Vec level.Level} {e : expr.Expr}
    (h : expr.mk_const n us = ok e) :
    ∃ d b, level.levels_have_param us = ok b ∧ e = .mk (.mk d (.Const n us)) ∧
      bvarBits e = 0 ∧ fvarBits e = 0 ∧ lpBit e = b := by
  rw [expr.mk_const.eq_def] at h
  simp only [bind_eq_ok_iff, rc_new_eq, Result.ok.injEq] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, bb, hbb, d, hd, _, rfl, _, hnd, he⟩ := h
  subst hnd; subst he
  obtain ⟨b1, b2, b3⟩ := node_bits (k := .Const n us) (by scalar_tac) (by scalar_tac) hd
  exact ⟨d, bb, hbb, rfl, by rw [b1]; rfl, by rw [b2]; rfl, b3⟩

theorem app_inv {f a e : expr.Expr} (h : expr.app f a = ok e) :
    ∃ d, e = .mk (.mk d (.App f a)) ∧
      bvarBits e = max (bvarBits f) (bvarBits a) ∧
      fvarBits e = max (fvarBits f) (fvarBits a) ∧
      lpBit e = (lpBit f || lpBit a) := by
  rw [expr.app.eq_def] at h
  simp only [bind_eq_ok_iff, rc_new_eq, data_eq, Result.ok.injEq] at h
  obtain ⟨df, hdf, da, hda, _, -, _, -, _, -, _, -, _, -,
    i4, hi4, i5, hi5, i6, hi6, i7, hi7, i8, hi8, i9, hi9, bb, hbb, b1, hb1, d, hd,
    _, hnd, he⟩ := h
  subst hdf; subst hda; subst hnd; subst he
  have e6 : i6.val = max (bvarBits f) (bvarBits a) := by
    rw [max_u64_val hi6, bvar_bits_val hi4, bvar_bits_val hi5]
  have e9 : i9.val = max (fvarBits f) (fvarBits a) := by
    rw [max_u64_val hi9, fvar_bits_val hi7, fvar_bits_val hi8]
  have hlt6 : i6.val < 32768 := by
    rw [e6]; have := bvarBits_lt f; have := bvarBits_lt a; omega
  have hlt9 : i9.val < 32768 := by
    rw [e9]; have := fvarBits_lt f; have := fvarBits_lt a; omega
  obtain ⟨c1, c2, c3⟩ := node_bits (k := .App f a) hlt6 hlt9 hd
  refine ⟨d, rfl, by rw [c1, e6], by rw [c2, e9], ?_⟩
  have ebb : bb = lpBit f := lp_bit_val hbb
  cases hcf : bb
  · rw [hcf] at hb1
    simp only [Bool.false_eq_true, if_false] at hb1
    rw [c3, lp_bit_val hb1, ← ebb, hcf]
    rfl
  · rw [hcf] at hb1
    simp only [if_true, Result.ok.injEq] at hb1
    rw [c3, ← hb1, ← ebb, hcf]
    rfl

/-- The `satPred` of a 15-bit field still fits in 15 bits (con-leche's
`satPred_lt`, at `Nat` level). -/
theorem satPred_lt {n : Nat} (h : n < 32768) :
    (if n = ConLeche.satRange then ConLeche.satRange else n - 1) < 32768 := by
  by_cases hc : n = ConLeche.satRange
  · rw [if_pos hc]; simp only [ConLeche.satRange]; omega
  · rw [if_neg hc]; omega

/-- `lam`'s and `forall_e`'s bit recurrences are the same; this is the common
half, stated over the node the caller built. -/
theorem binder_bits {ty bo : expr.Expr} {m : expr.BinderMeta} {k : expr.ExprKind}
    {i9 i10 i11 i12 i13 i14 i15 d : Std.U64} {bt b1 : Bool}
    (hi9 : expr.bvar_of_data (dataOf ty) = ok i9)
    (hi10 : expr.bvar_of_data (dataOf bo) = ok i10)
    (hi11 : expr.sat_pred i10 = ok i11)
    (hi12 : expr.max_u64 i9 i11 = ok i12)
    (hi13 : expr.fvar_of_data (dataOf ty) = ok i13)
    (hi14 : expr.fvar_of_data (dataOf bo) = ok i14)
    (hi15 : expr.max_u64 i13 i14 = ok i15)
    (hbt : expr.lp_of_data (dataOf ty) = ok bt)
    (hb1 : (if bt = true then ok true
      else do let b2 ← expr.lp_of_data (dataOf bo)
              if b2 = true then ok true else prop_when.has_params m.pw) = ok b1)
    (hd : expr.pack_data d i12 i15 b1 = ok d') :
    bvarBits (expr.Expr.mk (expr.ExprNode.mk d' k)) = max (bvarBits ty)
        (if bvarBits bo = ConLeche.satRange then ConLeche.satRange
         else bvarBits bo - 1) ∧
      fvarBits (expr.Expr.mk (expr.ExprNode.mk d' k)) =
        max (fvarBits ty) (fvarBits bo) ∧
      ∀ hp, prop_when.has_params m.pw = ok hp →
        lpBit (expr.Expr.mk (expr.ExprNode.mk d' k)) = (lpBit ty || lpBit bo || hp) := by
  have hsp : i11.val =
      if bvarBits bo = ConLeche.satRange then ConLeche.satRange else bvarBits bo - 1 := by
    have h1 := sat_pred_val hi11
    simp only [bvar_bits_val hi10] at h1
    exact h1
  have e12 : i12.val = max (bvarBits ty)
      (if bvarBits bo = ConLeche.satRange then ConLeche.satRange else bvarBits bo - 1) := by
    rw [max_u64_val hi12, bvar_bits_val hi9, hsp]
  have e15 : i15.val = max (fvarBits ty) (fvarBits bo) := by
    rw [max_u64_val hi15, fvar_bits_val hi13, fvar_bits_val hi14]
  have hlt12 : i12.val < 32768 := by
    rw [e12]
    have := bvarBits_lt ty
    have := satPred_lt (bvarBits_lt bo)
    omega
  have hlt15 : i15.val < 32768 := by
    rw [e15]; have := fvarBits_lt ty; have := fvarBits_lt bo; omega
  obtain ⟨c1, c2, c3⟩ := node_bits (k := k) hlt12 hlt15 hd
  refine ⟨by rw [c1, e12], by rw [c2, e15], ?_⟩
  intro hp hhp
  have ebt : bt = lpBit ty := lp_bit_val hbt
  cases hct : bt
  · rw [hct] at hb1
    simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at hb1
    obtain ⟨b2, hb2, hb1⟩ := hb1
    have eb2 : b2 = lpBit bo := lp_bit_val hb2
    cases hc2 : b2
    · rw [hc2] at hb1
      simp only [Bool.false_eq_true, if_false] at hb1
      rw [c3, Result.ok_injective (hb1.symm.trans hhp), ← ebt, hct, ← eb2, hc2]
      rfl
    · rw [hc2] at hb1
      simp only [if_true, Result.ok.injEq] at hb1
      rw [c3, ← hb1, ← ebt, hct, ← eb2, hc2]
      rfl
  · rw [hct] at hb1
    simp only [if_true, Result.ok.injEq] at hb1
    rw [c3, ← hb1, ← ebt, hct]
    rfl

theorem lam_inv {ty bo : expr.Expr} {m : expr.BinderMeta} {e : expr.Expr}
    (h : expr.lam ty bo m = ok e) :
    ∃ d, e = .mk (.mk d (.Lam ty bo m)) ∧
      bvarBits e = max (bvarBits ty)
        (if bvarBits bo = ConLeche.satRange then ConLeche.satRange
         else bvarBits bo - 1) ∧
      fvarBits e = max (fvarBits ty) (fvarBits bo) ∧
      ∀ hp, prop_when.has_params m.pw = ok hp →
        lpBit e = (lpBit ty || lpBit bo || hp) := by
  rw [expr.lam.eq_def] at h
  simp only [bind_eq_ok_iff, rc_new_eq, rc_deref_eq, data_eq, Result.ok.injEq] at h
  obtain ⟨dt, hdt, db, hdb, _, -, _, -, _, rfl, _, -, _, -, _, -, _, -, _, -,
    i9, hi9, i10, hi10, i11, hi11, i12, hi12, i13, hi13, i14, hi14, i15, hi15,
    bt, hbt, b1, hb1, d, hd, _, hnd, he⟩ := h
  subst hdt; subst hdb; subst hnd; subst he
  exact ⟨d, rfl, binder_bits hi9 hi10 hi11 hi12 hi13 hi14 hi15 hbt hb1 hd⟩

theorem forall_e_inv {ty bo : expr.Expr} {m : expr.BinderMeta} {e : expr.Expr}
    (h : expr.forall_e ty bo m = ok e) :
    ∃ d, e = .mk (.mk d (.ForallE ty bo m)) ∧
      bvarBits e = max (bvarBits ty)
        (if bvarBits bo = ConLeche.satRange then ConLeche.satRange
         else bvarBits bo - 1) ∧
      fvarBits e = max (fvarBits ty) (fvarBits bo) ∧
      ∀ hp, prop_when.has_params m.pw = ok hp →
        lpBit e = (lpBit ty || lpBit bo || hp) := by
  rw [expr.forall_e.eq_def] at h
  simp only [bind_eq_ok_iff, rc_new_eq, rc_deref_eq, data_eq, Result.ok.injEq] at h
  obtain ⟨dt, hdt, db, hdb, _, -, _, -, _, rfl, _, -, _, -, _, -, _, -, _, -,
    i9, hi9, i10, hi10, i11, hi11, i12, hi12, i13, hi13, i14, hi14, i15, hi15,
    bt, hbt, b1, hb1, d, hd, _, hnd, he⟩ := h
  subst hdt; subst hdb; subst hnd; subst he
  exact ⟨d, rfl, binder_bits hi9 hi10 hi11 hi12 hi13 hi14 hi15 hbt hb1 hd⟩

theorem let_e_inv {ty v bo e : expr.Expr} (h : expr.let_e ty v bo = ok e) :
    ∃ d, e = .mk (.mk d (.LetE ty v bo)) ∧
      bvarBits e = max (max (bvarBits ty) (bvarBits v))
        (if bvarBits bo = ConLeche.satRange then ConLeche.satRange
         else bvarBits bo - 1) ∧
      fvarBits e = max (max (fvarBits ty) (fvarBits v)) (fvarBits bo) ∧
      lpBit e = (lpBit ty || lpBit v || lpBit bo) := by
  rw [expr.let_e.eq_def] at h
  simp only [bind_eq_ok_iff, rc_new_eq, data_eq, Result.ok.injEq] at h
  obtain ⟨dt, hdt, dv, hdv, db, hdb, _, -, _, -, _, -, _, -, _, -, _, -, _, -,
    i6, hi6, i7, hi7, i8, hi8, i9, hi9, i10, hi10, i11, hi11,
    i12, hi12, i13, hi13, i14, hi14, i15, hi15, i16, hi16,
    bt, hbt, b1, hb1, d, hd, _, hnd, he⟩ := h
  subst hdt; subst hdv; subst hdb; subst hnd; subst he
  have hsp : i10.val =
      if bvarBits bo = ConLeche.satRange then ConLeche.satRange else bvarBits bo - 1 := by
    have h1 := sat_pred_val hi10
    simp only [bvar_bits_val hi9] at h1
    exact h1
  have e11 : i11.val = max (max (bvarBits ty) (bvarBits v))
      (if bvarBits bo = ConLeche.satRange then ConLeche.satRange else bvarBits bo - 1) := by
    rw [max_u64_val hi11, hsp, max_u64_val hi8, bvar_bits_val hi6, bvar_bits_val hi7]
  have e16 : i16.val = max (max (fvarBits ty) (fvarBits v)) (fvarBits bo) := by
    rw [max_u64_val hi16, fvar_bits_val hi15, max_u64_val hi14,
      fvar_bits_val hi12, fvar_bits_val hi13]
  have hlt11 : i11.val < 32768 := by
    rw [e11]
    have := bvarBits_lt ty; have := bvarBits_lt v
    have := satPred_lt (bvarBits_lt bo)
    omega
  have hlt16 : i16.val < 32768 := by
    rw [e16]
    have := fvarBits_lt ty; have := fvarBits_lt v; have := fvarBits_lt bo
    omega
  obtain ⟨c1, c2, c3⟩ := node_bits (k := .LetE ty v bo) hlt11 hlt16 hd
  refine ⟨d, rfl, by rw [c1, e11], by rw [c2, e16], ?_⟩
  have ebt : bt = lpBit ty := lp_bit_val hbt
  cases hct : bt
  · rw [hct] at hb1
    simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at hb1
    obtain ⟨b2, hb2, hb1⟩ := hb1
    have eb2 : b2 = lpBit v := lp_bit_val hb2
    cases hc2 : b2
    · rw [hc2] at hb1
      simp only [Bool.false_eq_true, if_false] at hb1
      rw [c3, lp_bit_val hb1, ← ebt, hct, ← eb2, hc2]
      rfl
    · rw [hc2] at hb1
      simp only [if_true, Result.ok.injEq] at hb1
      rw [c3, ← hb1, ← ebt, hct, ← eb2, hc2]
      rfl
  · rw [hct] at hb1
    simp only [if_true, Result.ok.injEq] at hb1
    rw [c3, ← hb1, ← ebt, hct]
    rfl

theorem lit_inv {l : expr.Literal} {e : expr.Expr} (h : expr.lit l = ok e) :
    ∃ d, e = .mk (.mk d (.Lit l)) ∧ bvarBits e = 0 ∧ fvarBits e = 0 ∧
      lpBit e = false := by
  rw [expr.lit.eq_def] at h
  simp only [bind_eq_ok_iff, rc_new_eq, Result.ok.injEq] at h
  obtain ⟨_, -, _, -, _, -, d, hd, _, hnd, he⟩ := h
  subst hnd; subst he
  obtain ⟨b1, b2, b3⟩ := node_bits (k := .Lit l) (by scalar_tac) (by scalar_tac) hd
  exact ⟨d, rfl, by rw [b1]; rfl, by rw [b2]; rfl, b3⟩

theorem proj_inv {s : name.Name} {idx : Std.U64} {x e : expr.Expr}
    (h : expr.proj s idx x = ok e) :
    ∃ d, e = .mk (.mk d (.Proj s idx x)) ∧ bvarBits e = bvarBits x ∧
      fvarBits e = fvarBits x ∧ lpBit e = lpBit x := by
  rw [expr.proj.eq_def] at h
  simp only [bind_eq_ok_iff, rc_new_eq, data_eq, Result.ok.injEq] at h
  obtain ⟨de, hde, _, -, _, -, _, -, _, -, _, -, _, -, _, -,
    i6, hi6, i7, hi7, bt, hbt, d, hd, _, hnd, he⟩ := h
  subst hde; subst hnd; subst he
  have e6 : i6.val = bvarBits x := bvar_bits_val hi6
  have e7 : i7.val = fvarBits x := fvar_bits_val hi7
  obtain ⟨c1, c2, c3⟩ := node_bits (k := .Proj s idx x)
    (by rw [e6]; exact bvarBits_lt x) (by rw [e7]; exact fvarBits_lt x) hd
  exact ⟨d, rfl, by rw [c1, e6], by rw [c2, e7], by rw [c3, lp_bit_val hbt]⟩

/-! ## The data word refines con-leche's computed field

`wf_data` is the module's central lemma: on a well-formed node the three
*observed* fields of the port's word are con-leche's `bvarBRaw`, `fvarBRaw`
and `hasLP` of the abstraction.  One case per `ExprWF` constructor, each the
port's `*_inv` beside con-leche's `@[simp]` equation for the same
constructor -- nothing about the hash field, which is where the two words
legitimately differ (DESIGN.md §3.2). -/

/-- `prop_when::has_params` is a five-arm `match`, hence total -- which is what
lets `lam`'s short-circuited `||` chain be related to con-leche's. -/
theorem has_params_ok (pw : prop_when.PropWhen) :
    ∃ b, prop_when.has_params pw = ok b := by
  obtain ⟨r⟩ := pw
  cases r <;> exact ⟨_, rfl⟩

theorem wf_data {e : expr.Expr} (h : ExprWF e) :
    bvarBits e = (absExpr e).bvarBRaw ∧ fvarBits e = (absExpr e).fvarBRaw ∧
      lpBit e = (absExpr e).hasLP := by
  induction h with
  | @bvar i e h =>
    obtain ⟨d, rfl, hb, hf, hl⟩ := bvar_inv h
    refine ⟨?_, ?_, ?_⟩
    · rw [hb]; simp
    · rw [hf]; simp
    · rw [hl]; simp
  | @fvar idx ty e hty h ih =>
    obtain ⟨d, rfl, hb, hf, hl⟩ := fvar_inv h
    refine ⟨?_, ?_, ?_⟩
    · rw [hb]; simp
    · rw [hf]; simp
    · rw [hl, ih.2.2]; simp
  | @sort u e hu h =>
    obtain ⟨d, b, hpar, rfl, hb, hf, hl⟩ := sort_inv h
    refine ⟨?_, ?_, ?_⟩
    · rw [hb]; simp
    · rw [hf]; simp
    · rw [hl, Level.level_has_param_refines hpar]; simp
  | @mk_const n us e hn hus h =>
    obtain ⟨d, b, hpar, rfl, hb, hf, hl⟩ := mk_const_inv h
    refine ⟨?_, ?_, ?_⟩
    · rw [hb]; simp
    · rw [hf]; simp
    · rw [hl, Level.levels_have_param_refines hpar]; simp
  | @app f a e hf ha h ihf iha =>
    obtain ⟨d, rfl, hb, hff, hl⟩ := app_inv h
    refine ⟨?_, ?_, ?_⟩
    · rw [hb, ihf.1, iha.1]; simp
    · rw [hff, ihf.2.1, iha.2.1]; simp
    · rw [hl, ihf.2.2, iha.2.2]; simp
  | @lam ty bo m e hty hbo hm h ihty ihbo =>
    obtain ⟨d, rfl, hb, hff, hl⟩ := lam_inv h
    obtain ⟨hp, hhp⟩ := has_params_ok m.pw
    refine ⟨?_, ?_, ?_⟩
    · rw [hb]; simp only [ihty.1, ihbo.1]; simp
    · rw [hff, ihty.2.1, ihbo.2.1]; simp
    · rw [hl hp hhp, ihty.2.2, ihbo.2.2, PropWhen.has_params_refines hm hhp]; simp
  | @forall_e ty bo m e hty hbo hm h ihty ihbo =>
    obtain ⟨d, rfl, hb, hff, hl⟩ := forall_e_inv h
    obtain ⟨hp, hhp⟩ := has_params_ok m.pw
    refine ⟨?_, ?_, ?_⟩
    · rw [hb]; simp only [ihty.1, ihbo.1]; simp
    · rw [hff, ihty.2.1, ihbo.2.1]; simp
    · rw [hl hp hhp, ihty.2.2, ihbo.2.2, PropWhen.has_params_refines hm hhp]; simp
  | @let_e ty v bo e hty hv hbo h ihty ihv ihbo =>
    obtain ⟨d, rfl, hb, hff, hl⟩ := let_e_inv h
    refine ⟨?_, ?_, ?_⟩
    · rw [hb]; simp only [ihty.1, ihv.1, ihbo.1]; simp
    · rw [hff, ihty.2.1, ihv.2.1, ihbo.2.1]; simp
    · rw [hl, ihty.2.2, ihv.2.2, ihbo.2.2]; simp
  | @lit l e hl h =>
    obtain ⟨d, rfl, hb, hf, hlp⟩ := lit_inv h
    refine ⟨?_, ?_, ?_⟩
    · rw [hb]; simp
    · rw [hf]; simp
    · rw [hlp]; simp
  | @proj s i x e hs hx h ih =>
    obtain ⟨d, rfl, hb, hf, hl⟩ := proj_inv h
    refine ⟨?_, ?_, ?_⟩
    · rw [hb, ih.1]; simp
    · rw [hf, ih.2.1]; simp
    · rw [hl, ih.2.2]; simp

/-! ## The smart constructors

`<c>_wf` is literally the `ExprWF` constructor (the §3.5 convention);
`<c>_refines` is what the node abstracts to. -/

theorem bvar_wf {i : Std.U64} {e : expr.Expr} : expr.bvar i = ok e → ExprWF e :=
  ExprWF.bvar

theorem fvar_wf {idx : Std.U64} {ty e : expr.Expr} (hty : ExprWF ty) :
    expr.fvar idx ty = ok e → ExprWF e := ExprWF.fvar hty

theorem sort_wf {u : level.Level} {e : expr.Expr} (hu : LevelWF u) :
    expr.sort u = ok e → ExprWF e := ExprWF.sort hu

theorem mk_const_wf {n : name.Name} {us : alloc.vec.Vec level.Level} {e : expr.Expr}
    (hn : NameWF n) (hus : LevelsWF us) : expr.mk_const n us = ok e → ExprWF e :=
  ExprWF.mk_const hn hus

theorem app_wf {f a e : expr.Expr} (hf : ExprWF f) (ha : ExprWF a) :
    expr.app f a = ok e → ExprWF e := ExprWF.app hf ha

theorem lam_wf {ty bo e : expr.Expr} {m : expr.BinderMeta}
    (hty : ExprWF ty) (hbo : ExprWF bo) (hm : BinderMetaWF m) :
    expr.lam ty bo m = ok e → ExprWF e := ExprWF.lam hty hbo hm

theorem forall_e_wf {ty bo e : expr.Expr} {m : expr.BinderMeta}
    (hty : ExprWF ty) (hbo : ExprWF bo) (hm : BinderMetaWF m) :
    expr.forall_e ty bo m = ok e → ExprWF e := ExprWF.forall_e hty hbo hm

theorem let_e_wf {ty v bo e : expr.Expr} (hty : ExprWF ty) (hv : ExprWF v)
    (hbo : ExprWF bo) : expr.let_e ty v bo = ok e → ExprWF e := ExprWF.let_e hty hv hbo

theorem lit_wf {l : expr.Literal} {e : expr.Expr} (hl : LiteralWF l) :
    expr.lit l = ok e → ExprWF e := ExprWF.lit hl

theorem proj_wf {s : name.Name} {i : Std.U64} {x e : expr.Expr}
    (hs : NameWF s) (hx : ExprWF x) : expr.proj s i x = ok e → ExprWF e :=
  ExprWF.proj hs hx

theorem bvar_refines {i : Std.U64} {e : expr.Expr} (h : expr.bvar i = ok e) :
    absExpr e = .bvar i.val := by
  obtain ⟨d, rfl, -, -, -⟩ := bvar_inv h; simp

theorem fvar_refines {idx : Std.U64} {ty e : expr.Expr} (h : expr.fvar idx ty = ok e) :
    absExpr e = .fvar idx.val (absExpr ty) := by
  obtain ⟨d, rfl, -, -, -⟩ := fvar_inv h; simp

theorem sort_refines {u : level.Level} {e : expr.Expr} (h : expr.sort u = ok e) :
    absExpr e = .sort (absLevel u) := by
  obtain ⟨d, b, -, rfl, -, -, -⟩ := sort_inv h; simp

theorem mk_const_refines {n : name.Name} {us : alloc.vec.Vec level.Level} {e : expr.Expr}
    (h : expr.mk_const n us = ok e) :
    absExpr e = .const (absName n) (absLevels us) := by
  obtain ⟨d, b, -, rfl, -, -, -⟩ := mk_const_inv h; simp

theorem app_refines {f a e : expr.Expr} (h : expr.app f a = ok e) :
    absExpr e = .app (absExpr f) (absExpr a) := by
  obtain ⟨d, rfl, -, -, -⟩ := app_inv h; simp

theorem lam_refines {ty bo e : expr.Expr} {m : expr.BinderMeta}
    (h : expr.lam ty bo m = ok e) :
    absExpr e = .lam (absExpr ty) (absExpr bo) (absBinderMeta m) := by
  obtain ⟨d, rfl, -, -, -⟩ := lam_inv h; simp

theorem forall_e_refines {ty bo e : expr.Expr} {m : expr.BinderMeta}
    (h : expr.forall_e ty bo m = ok e) :
    absExpr e = .forallE (absExpr ty) (absExpr bo) (absBinderMeta m) := by
  obtain ⟨d, rfl, -, -, -⟩ := forall_e_inv h; simp

theorem let_e_refines {ty v bo e : expr.Expr} (h : expr.let_e ty v bo = ok e) :
    absExpr e = .letE (absExpr ty) (absExpr v) (absExpr bo) := by
  obtain ⟨d, rfl, -, -, -⟩ := let_e_inv h; simp

theorem lit_refines {l : expr.Literal} {e : expr.Expr} (h : expr.lit l = ok e) :
    absExpr e = .lit (absLiteral l) := by
  obtain ⟨d, rfl, -, -, -⟩ := lit_inv h; simp

theorem proj_refines {s : name.Name} {i : Std.U64} {x e : expr.Expr}
    (h : expr.proj s i x = ok e) :
    absExpr e = .proj (absName s) i.val (absExpr x) := by
  obtain ⟨d, rfl, -, -, -⟩ := proj_inv h; simp

/-- `expr::mk_bvar` refines `Expr.mkBvar`.  The `bvarPool` is not ported
(task #11); con-leche's own `mkBvar_eq` is why that is free -- the pooled and
the fresh node are the same *value*, which is exactly what this says. -/
theorem mk_bvar_refines {i : Std.U64} {e : expr.Expr} (h : expr.mk_bvar i = ok e) :
    absExpr e = ConLeche.Expr.mkBvar i.val := by
  rw [expr.mk_bvar] at h
  rw [bvar_refines h, ConLeche.Expr.mkBvar_eq]

theorem mk_bvar_wf {i : Std.U64} {e : expr.Expr} (h : expr.mk_bvar i = ok e) :
    ExprWF e := by rw [expr.mk_bvar] at h; exact ExprWF.bvar h

/-- `expr::bvar_pool_size` refines `Expr.bvarPoolSize` (kept for the record;
nothing reads it, since the pool is not ported). -/
theorem bvar_pool_size_refines {r : Std.U64} (h : expr.bvar_pool_size = ok r) :
    r.val = ConLeche.Expr.bvarPoolSize := by
  rw [expr.bvar_pool_size, Result.ok.injEq] at h; rw [← h]; rfl

/-! ## The packed word's accessors

`hash` gets **no** refinement lemma: it reads the one field of the word that
the port and con-leche legitimately disagree on (DESIGN.md §3.2 -- `mixHash`
is opaque, the port hashes its own bignums and strings, and a hash only ever
picks a memo bucket).  The other three are exact. -/

theorem has_lp_refines {e : expr.Expr} {b : Bool} (hwf : ExprWF e)
    (h : expr.has_lp e = ok b) : b = ConLeche.Expr.hasLP (absExpr e) := by
  rw [expr.has_lp, data_eq, bind_tc_ok] at h
  rw [lp_bit_val h, (wf_data hwf).2.2]

theorem bvar_b_raw_refines {e : expr.Expr} {r : Std.U64} (hwf : ExprWF e)
    (h : expr.bvar_b_raw e = ok r) : r.val = ConLeche.Expr.bvarBRaw (absExpr e) := by
  rw [expr.bvar_b_raw, data_eq, bind_tc_ok] at h
  rw [bvar_bits_val h, (wf_data hwf).1]

theorem fvar_b_raw_refines {e : expr.Expr} {r : Std.U64} (hwf : ExprWF e)
    (h : expr.fvar_b_raw e = ok r) : r.val = ConLeche.Expr.fvarBRaw (absExpr e) := by
  rw [expr.fvar_b_raw, data_eq, bind_tc_ok] at h
  rw [fvar_bits_val h, (wf_data hwf).2.1]

/-! ## `dup`, `ptr_eq` and the copies -/

/-- `expr::dup` is the identity in the model (`Rc::clone` is; DESIGN.md §3.2). -/
theorem dup_eq {e c : expr.Expr} (h : expr.dup e = ok c) : c = e := by
  obtain ⟨r⟩ := e
  simp only [expr.dup, rc_clone_eq, bind_tc_ok, Result.ok.injEq] at h
  exact h.symm

/-- `expr::ptr_eq` is `false` in the model, so the model always takes the slow
path (DESIGN.md §3.2); `beq_refl` below is the transparency obligation. -/
@[simp] theorem ptr_eq_eq (a b : expr.Expr) : expr.ptr_eq a b = ok false := by
  simp [expr.ptr_eq]

/-- `expr::str_copy_from` appends the rest of the code points (the task-#5
index-loop shape, with the conclusion on `List.drop i`). -/
theorem str_copy_from_val {s : alloc.vec.Vec Std.U32} :
    ∀ k : Nat, ∀ (i : Std.Usize) (out r : alloc.vec.Vec Std.U32),
      s.val.length - i.val ≤ k → expr.str_copy_from s i out = ok r →
      r.val = out.val ++ s.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out r hk h
    rw [expr.str_copy_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len s by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac), List.append_nil]
  | succ k ih =>
    intro i out r hk h
    rw [expr.str_copy_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ s.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len s by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac), List.append_nil]
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len s by scalar_tac)] at h
      have hlt : i.val < s.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := s.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec s i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨o1, ho1, h⟩ := h
      simp only [hw, Result.ok.injEq, exists_eq_left'] at h
      have hrec := ih w o1 r (by scalar_tac) h
      rw [hrec, vec_push_val ho1, hwv, List.drop_eq_getElem_cons hlt]
      simp

/-- `expr::str_copy` is the identity in the model: a `Vec` copy has the same
list (DESIGN.md §3.2). -/
theorem str_copy_eq {s r : alloc.vec.Vec Std.U32} (h : expr.str_copy s = ok r) :
    r = s := by
  rw [expr.str_copy] at h
  have := str_copy_from_val s.val.length 0#usize (alloc.vec.Vec.new Std.U32) r
    (by scalar_tac) h
  exact alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.new] using this)

/-- `expr::literal_dup` is the identity in the model -- and since task #38 put
both payloads behind a handle it is so *on the nose*: a `dup` is `Rc::clone`,
whose model is the identity, where it used to be a `Nat` limb copy and a
`Vec<u32>` copy that `Nat.clone_refines`/`str_copy_eq` had to identify. -/
theorem literal_dup_eq {l c : expr.Literal} (h : expr.literal_dup l = ok c) : c = l := by
  cases l with
  | NatVal n =>
    simp only [expr.literal_dup, rc_clone_eq, bind_tc_ok, Result.ok.injEq] at h
    exact h.symm
  | StrVal s =>
    simp only [expr.literal_dup, rc_clone_eq, bind_tc_ok, Result.ok.injEq] at h
    exact h.symm

/-- `expr::binder_meta_dup` is the identity in the model. -/
theorem binder_meta_dup_eq {m c : expr.BinderMeta} (h : expr.binder_meta_dup m = ok c) :
    c = m := by
  simp only [expr.binder_meta_dup, rc_clone_eq, bind_tc_ok, Result.ok.injEq] at h
  exact h.symm

/-! ## The derived equalities on the leaf data -/

/-- `expr::literal_beq` refines `Literal`'s `DecidableEq`, exactly. -/
theorem literal_beq_refines {a b : expr.Literal} {c : Bool}
    (ha : LiteralWF a) (hb : LiteralWF b) (h : expr.literal_beq a b = ok c) :
    c = decide (absLiteral a = absLiteral b) := by
  cases a with
  | NatVal m =>
    cases b with
    | NatVal n =>
      simp only [expr.literal_beq, rc_deref_eq, bind_tc_ok] at h
      rw [Nat.beq_refines ha hb h]
      simp
    | StrVal t =>
      simp only [expr.literal_beq, Result.ok.injEq] at h
      rw [← h]; simp
  | StrVal s =>
    cases b with
    | NatVal n =>
      simp only [expr.literal_beq, Result.ok.injEq] at h
      rw [← h]; simp
    | StrVal t =>
      simp only [expr.literal_beq, rc_deref_eq, bind_tc_ok] at h
      rw [Name.str_eq_refines ha hb h]
      simp

/-- `expr::binder_meta_beq` refines `BinderMeta`'s `DecidableEq`, exactly. -/
theorem binder_meta_beq_refines {a b : expr.BinderMeta} {c : Bool}
    (ha : BinderMetaWF a) (hb : BinderMetaWF b)
    (h : expr.binder_meta_beq a b = ok c) :
    c = decide (absBinderMeta a = absBinderMeta b) := by
  simp only [expr.binder_meta_beq, rc_deref_eq, bind_tc_ok] at h
  rw [PropWhen.beq_refines ha hb h]
  simp [absBinderMeta]

/-- `expr::beq_recursive` refines `Expr.beqRecursive`. -/
theorem beq_recursive_refines {e : expr.Expr} {b : Bool}
    (h : expr.beq_recursive e = ok b) : b = ConLeche.Expr.beqRecursive (absExpr e) := by
  obtain ⟨⟨d, k⟩⟩ := e
  simp only [expr.beq_recursive, rc_deref_eq, bind_tc_ok,
    expr.Expr._0._simpLemma_, expr.ExprNode.kind._simpLemma_] at h
  cases k <;> simp only [Result.ok.injEq] at h <;> rw [← h] <;>
    simp [ConLeche.Expr.beqRecursive]

/-! ## `List Level` equality

`beq_go`'s `.const` arm is con-leche's `us == vs` at `LawfulBEq Level`, i.e.
`decide (us = vs)`; the port walks the two `Vec`s by index (task #11, item 4).
The loop only guards on `ls`'s length, because `levels_beq` has already
compared the two lengths -- hence `hlen` in the loop lemma. -/

theorem levels_beq_from_refines {ls rs : alloc.vec.Vec level.Level}
    (hls : LevelsWF ls) (hrs : LevelsWF rs) (hlen : ls.val.length = rs.val.length) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool), ls.val.length - i.val ≤ k →
      expr.levels_beq_from ls rs i = ok b →
      (b = true ↔ (ls.val.drop i.val).map absLevel = (rs.val.drop i.val).map absLevel) := by
  have hnil : ∀ (i : Std.Usize), ls.val.length ≤ i.val →
      ((ls.val.drop i.val).map absLevel = (rs.val.drop i.val).map absLevel) := by
    intro i hi
    rw [List.drop_eq_nil_of_le hi, List.drop_eq_nil_of_le (by omega)]
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [expr.levels_beq_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len ls by scalar_tac), Result.ok.injEq] at h
    rw [← h]
    exact iff_of_true rfl (hnil i (by scalar_tac))
  | succ k ih =>
    intro i b hk h
    rw [expr.levels_beq_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ ls.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len ls by scalar_tac), Result.ok.injEq] at h
      rw [← h]
      exact iff_of_true rfl (hnil i (by scalar_tac))
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len ls by scalar_tac)] at h
      have hl : i.val < ls.val.length := by scalar_tac
      have hr : i.val < rs.val.length := by omega
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ls.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ls i hl)
      obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rs i hr)
      subst hyv; subst hzv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b0, hb0, h⟩ := h
      have hb0' := Level.beq_refines (hls _ (List.getElem_mem hl))
        (hrs _ (List.getElem_mem hr)) hb0
      rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons hr,
        List.map_cons, List.map_cons, List.cons.injEq]
      cases hc : b0
      · rw [hc] at hb0' h
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        have hne := of_decide_eq_false hb0'.symm
        rw [← h]
        simp only [Bool.false_eq_true, false_iff, not_and]
        intro hhd; exact absurd hhd hne
      · rw [hc] at hb0' h
        simp only [if_true, bind_eq_ok_iff, hw, Result.ok.injEq, exists_eq_left'] at h
        have heq := of_decide_eq_true hb0'.symm
        have hrec := ih w b (by scalar_tac) h
        rw [hwv] at hrec
        rw [hrec]
        simp only [heq, true_and]

/-- `expr::levels_beq` decides equality of the abstracted level lists, exactly. -/
theorem levels_beq_refines {ls rs : alloc.vec.Vec level.Level} {c : Bool}
    (hls : LevelsWF ls) (hrs : LevelsWF rs) (h : expr.levels_beq ls rs = ok c) :
    c = decide (absLevels ls = absLevels rs) := by
  rw [expr.levels_beq.eq_def] at h; simp only [] at h
  by_cases hlen : ls.val.length = rs.val.length
  · rw [if_neg (show ¬ (alloc.vec.Vec.len ls != alloc.vec.Vec.len rs) by
      simp only [bne_iff_ne, ne_eq, not_not]; scalar_tac)] at h
    have hfrom := levels_beq_from_refines hls hrs hlen ls.val.length 0#usize c
      (by scalar_tac) h
    have h0 : (0#usize : Std.Usize).val = 0 := rfl
    rw [h0, List.drop_zero, List.drop_zero] at hfrom
    cases c
    · refine (decide_eq_false ?_).symm
      simp only [absLevels]
      intro hcc
      simpa using hfrom.mpr hcc
    · refine (decide_eq_true ?_).symm
      simp only [absLevels]
      exact hfrom.mp rfl
  · rw [if_pos (show (alloc.vec.Vec.len ls != alloc.vec.Vec.len rs) by
      simp only [bne_iff_ne, ne_eq]; intro hc; exact hlen (by scalar_tac)),
      Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    simp only [absLevels]
    intro hc
    exact hlen (by simpa using congrArg List.length hc)

/-! ## `absExpr` is injective on well-formed input

This is what `beq`'s *exactness* rests on: `absExpr` drops the stored word, so
completeness of the word guard (`data a ≠ data b → false`) needs the whole
word -- hash field included -- to be a function of the abstraction.  It is,
and for the reason §3.5 gives: a well-formed node *is* what a smart
constructor built from its children, and a smart constructor is a function, so
equal children give an equal node (`Result.ok_injective`).  No hash formula
appears anywhere in the proof. -/

theorem levels_list_inj {l m : List level.Level} (hl : ∀ u ∈ l, LevelWF u)
    (hm : ∀ u ∈ m, LevelWF u) (h : l.map absLevel = m.map absLevel) : l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp_all
  | cons x xs ih =>
    cases m with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [Level.absLevel_injective (hl x (by simp)) (hm y (by simp)) h.1,
        ih (fun n hn => hl n (by simp [hn])) (fun n hn => hm n (by simp [hn])) h.2]

theorem absLevels_inj {us vs : alloc.vec.Vec level.Level}
    (hus : LevelsWF us) (hvs : LevelsWF vs) (h : absLevels us = absLevels vs) :
    us = vs :=
  alloc.vec.Vec.ext _ _ (levels_list_inj hus hvs h)

theorem absLiteral_inj {a b : expr.Literal} (ha : LiteralWF a) (hb : LiteralWF b)
    (h : absLiteral a = absLiteral b) : a = b := by
  cases a with
  | NatVal m =>
    cases b with
    | NatVal n =>
      simp only [absLiteral, ConLeche.Literal.natVal.injEq] at h
      rw [Nat.toNat_inj ha hb h]
    | StrVal t => simp only [absLiteral] at h; exact absurd h (by simp)
  | StrVal s =>
    cases b with
    | NatVal n => simp only [absLiteral] at h; exact absurd h (by simp)
    | StrVal t =>
      simp only [absLiteral, ConLeche.Literal.strVal.injEq] at h
      rw [Name.absString_inj ha hb h]

theorem absBinderMeta_inj {a b : expr.BinderMeta} (ha : BinderMetaWF a)
    (hb : BinderMetaWF b) (h : absBinderMeta a = absBinderMeta b) : a = b := by
  obtain ⟨pa⟩ := a
  obtain ⟨pb⟩ := b
  simp only [absBinderMeta, ConLeche.BinderMeta.mk.injEq] at h
  rw [expr.BinderMeta.mk.injEq]
  exact PropWhen.absPropWhen_injective ha hb h

theorem absExpr_injective {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b) :
    absExpr a = absExpr b → a = b := by
  induction ha generalizing b with
  | @bvar i1 e1 h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := bvar_inv h1
    intro hab
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.bvar.injEq] at hab
      have q1 : i1 = i2 := Std.UScalar.eq_of_val_eq hab
      subst q1
      exact Result.ok_injective (h1.symm.trans h2)
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      simp at hab
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      simp at hab
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      simp at hab
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      simp at hab
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      simp at hab
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      simp at hab
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      simp at hab
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      simp at hab
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      simp at hab
  | @fvar idx1 ty1 e1 hty1 h1 ih1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := fvar_inv h1
    intro hab
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      simp at hab
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.fvar.injEq] at hab
      have q1 : idx1 = idx2 := Std.UScalar.eq_of_val_eq hab.1
      have q2 : ty1 = ty2 := ih1 hty2 hab.2
      subst q1; subst q2
      exact Result.ok_injective (h1.symm.trans h2)
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      simp at hab
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      simp at hab
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      simp at hab
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      simp at hab
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      simp at hab
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      simp at hab
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      simp at hab
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      simp at hab
  | @sort u1 e1 hu1 h1 =>
    obtain ⟨d1, _, -, rfl, -, -, -⟩ := sort_inv h1
    intro hab
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      simp at hab
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      simp at hab
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.sort.injEq] at hab
      have q1 : u1 = u2 := Level.absLevel_injective hu1 hu2 hab
      subst q1
      exact Result.ok_injective (h1.symm.trans h2)
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      simp at hab
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      simp at hab
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      simp at hab
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      simp at hab
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      simp at hab
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      simp at hab
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      simp at hab
  | @mk_const n1 us1 e1 hn1 hus1 h1 =>
    obtain ⟨d1, _, -, rfl, -, -, -⟩ := mk_const_inv h1
    intro hab
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      simp at hab
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      simp at hab
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      simp at hab
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.const.injEq] at hab
      have q1 : n1 = n2 := Name.absName_injective hn1 hn2 hab.1
      have q2 : us1 = us2 := absLevels_inj hus1 hus2 hab.2
      subst q1; subst q2
      exact Result.ok_injective (h1.symm.trans h2)
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      simp at hab
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      simp at hab
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      simp at hab
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      simp at hab
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      simp at hab
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      simp at hab
  | @app f1 a1 e1 hf1 ha1 h1 ihf1 iha1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := app_inv h1
    intro hab
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      simp at hab
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      simp at hab
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      simp at hab
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      simp at hab
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.app.injEq] at hab
      have q1 : f1 = f2 := ihf1 hf2 hab.1
      have q2 : a1 = a2 := iha1 ha2 hab.2
      subst q1; subst q2
      exact Result.ok_injective (h1.symm.trans h2)
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      simp at hab
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      simp at hab
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      simp at hab
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      simp at hab
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      simp at hab
  | @lam ty1 bo1 m1 e1 hty1 hbo1 hm1 h1 ihty1 ihbo1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := lam_inv h1
    intro hab
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      simp at hab
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      simp at hab
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      simp at hab
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      simp at hab
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      simp at hab
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.lam.injEq] at hab
      have q1 : ty1 = ty2 := ihty1 hty2 hab.1
      have q2 : bo1 = bo2 := ihbo1 hbo2 hab.2.1
      have q3 : m1 = m2 := absBinderMeta_inj hm1 hm2 hab.2.2
      subst q1; subst q2; subst q3
      exact Result.ok_injective (h1.symm.trans h2)
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      simp at hab
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      simp at hab
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      simp at hab
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      simp at hab
  | @forall_e ty1 bo1 m1 e1 hty1 hbo1 hm1 h1 ihty1 ihbo1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := forall_e_inv h1
    intro hab
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      simp at hab
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      simp at hab
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      simp at hab
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      simp at hab
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      simp at hab
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      simp at hab
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.forallE.injEq] at hab
      have q1 : ty1 = ty2 := ihty1 hty2 hab.1
      have q2 : bo1 = bo2 := ihbo1 hbo2 hab.2.1
      have q3 : m1 = m2 := absBinderMeta_inj hm1 hm2 hab.2.2
      subst q1; subst q2; subst q3
      exact Result.ok_injective (h1.symm.trans h2)
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      simp at hab
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      simp at hab
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      simp at hab
  | @let_e ty1 v1 bo1 e1 hty1 hv1 hbo1 h1 ihty1 ihv1 ihbo1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := let_e_inv h1
    intro hab
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      simp at hab
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      simp at hab
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      simp at hab
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      simp at hab
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      simp at hab
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      simp at hab
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      simp at hab
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.letE.injEq] at hab
      have q1 : ty1 = ty2 := ihty1 hty2 hab.1
      have q2 : v1 = v2 := ihv1 hv2 hab.2.1
      have q3 : bo1 = bo2 := ihbo1 hbo2 hab.2.2
      subst q1; subst q2; subst q3
      exact Result.ok_injective (h1.symm.trans h2)
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      simp at hab
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      simp at hab
  | @lit l1 e1 hl1 h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := lit_inv h1
    intro hab
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      simp at hab
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      simp at hab
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      simp at hab
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      simp at hab
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      simp at hab
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      simp at hab
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      simp at hab
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      simp at hab
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.lit.injEq] at hab
      have q1 : l1 = l2 := absLiteral_inj hl1 hl2 hab
      subst q1
      exact Result.ok_injective (h1.symm.trans h2)
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      simp at hab
  | @proj s1 i1 x1 e1 hs1 hx1 h1 ih1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := proj_inv h1
    intro hab
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      simp at hab
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      simp at hab
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      simp at hab
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      simp at hab
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      simp at hab
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      simp at hab
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      simp at hab
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      simp at hab
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      simp at hab
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.proj.injEq] at hab
      have q1 : s1 = s2 := Name.absName_injective hs1 hs2 hab.1
      have q2 : i1 = i2 := Std.UScalar.eq_of_val_eq hab.2.1
      have q3 : x1 = x2 := ih1 hx2 hab.2.2
      subst q1; subst q2; subst q3
      exact Result.ok_injective (h1.symm.trans h2)

/-! ## `beq`

`beq_go` is the official kernel's descent: pointer identity, then the computed
word (a mismatch *is* an inequality), then -- since task #30 -- the pair memo's
probe, then the constructor cases (`beq_arm`), then the write-back.  The
pointer test is `false` in the model (DESIGN.md §3.2), so the model always
takes the slow path; the word guard is what needs `absExpr`'s injectivity, and
every arm of the descent has the same shape -- one comparison, then the rest --
which `guard_step` and its state-threading twins handle once.

**The memo is dead in the model, and that is the whole of task #30's proof
obligation.**  A probe verifies a stored pair by *identity* (`expr::probe_hit`
tests `ptr_eq` on both components), and `ptr_eq` is `false` here, so the probe
misses whatever the table holds (`probe_hit_false`) -- no fact about the table
is ever needed, not even `ron::HashMap`'s invariant.  The write-back changes
the table and not the decision (`beq_finish_fst`).  So `beq_go` is its frame
around `beq_arm` (`beq_go_arm` peels it once) and the hundred-case constructor
induction below is about `beq_arm`, the memo-free descent -- word for word the
one task #20 proved, with the table carried along as state no case looks at.
The binary side of the argument (a hit repeats what this same walk produced
for those same two objects) is the module note of `kernel/expr.rs`. -/

/-- The memo table `beq_go` threads (`expr::BeqMap`): a **bucket** of pairs
per key since task #38, because a key of the two *hash words* collides on
exactly the structurally equal, pointer-distinct objects the memo is for.
Nothing in the model reads it either way. -/
abbrev BeqMap :=
  ron.hashmap.HashMap Std.U64 (alloc.vec.Vec (expr.Expr × expr.Expr))

theorem u64_decide_val (i j : Std.U64) : decide (i = j) = decide (i.val = j.val) := by
  by_cases hc : i = j
  · simp [hc]
  · have hne : i.val ≠ j.val := fun hv => hc (Std.UScalar.eq_of_val_eq hv)
    simp [hc, hne]

theorem u64_eq_test {i j : Std.U64} {y : Bool}
    (hy : Aeneas.Std.lift (core.cmp.impls.PartialEqU64.eq i j) = ok y) :
    y = decide (i.val = j.val) := by
  simp only [lift_eq, Result.ok.injEq] at hy
  rw [← hy, core.cmp.impls.PartialEqU64.eq, u64_decide_val]

/-- Every arm of the descent is `let y ← <test>; if y then <rest> else false`;
given the two components' exactness, that arm is exact. -/
theorem guard_step {P Q : Prop} [Decidable P] [Decidable Q] {c : Bool}
    {test rest : Result Bool}
    (htest : ∀ y, test = ok y → y = decide P)
    (hrest : ∀ y, rest = ok y → y = decide Q)
    (h : (do let y ← test; if y = true then rest else ok false) = ok c) :
    c = decide (P ∧ Q) := by
  simp only [bind_eq_ok_iff] at h
  obtain ⟨y, hy, h⟩ := h
  have e := htest y hy
  cases hc : y
  · rw [hc] at e h
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h]
    have hnp : ¬ P := of_decide_eq_false e.symm
    simp [hnp]
  · rw [hc] at e h
    simp only [if_true] at h
    have hp : P := of_decide_eq_true e.symm
    rw [hrest c h]
    simp [hp]

/-- A memo probe never hits in the model: it verifies a stored pair by
identity and `expr::ptr_eq` is `false` (DESIGN.md §3.2).  Note what the
statement does *not* assume -- nothing at all about the table, in particular
not `ron::HashMap`'s invariant: both branches of the probe answer `false`
whatever `get` returned.  This is the model half of task #30's trust
argument. -/
theorem pair_is_false {p : expr.Expr × expr.Expr} {a b : expr.Expr} {r : Bool}
    (h : expr.pair_is p a b = ok r) : r = false := by
  rw [expr.pair_is] at h
  obtain ⟨p1, p2⟩ := p
  simp only [ptr_eq_eq, bind_tc_ok, Bool.false_eq_true, if_false] at h
  simpa using h.symm

/-- The bucket scan of task #38's memo, by the measure induction every index
recursion in this development uses (DESIGN.md §3.5: induct on the argument,
not on the function).  Every candidate misses, so the scan runs off the end
and answers `false` -- and it says so for *any* bucket, which is why the
model still needs no fact about the table. -/
theorem probe_hit_from_false {a b : expr.Expr}
    {ps : alloc.vec.Vec (expr.Expr × expr.Expr)} :
    ∀ k : Nat, ∀ (i : Std.Usize) (r : Bool),
      ps.val.length - i.val ≤ k → expr.probe_hit_from ps i a b = ok r →
      r = false := by
  intro k
  induction k with
  | zero =>
    intro i r hk h
    rw [expr.probe_hit_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
    exact h.symm
  | succ k ih =>
    intro i r hk h
    rw [expr.probe_hit_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ ps.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
      exact h.symm
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len ps by scalar_tac)] at h
      have hlt : i.val < ps.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff] at h
      obtain ⟨p, -, c, hc, h⟩ := h
      rw [pair_is_false hc] at h
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, hw,
        Result.ok.injEq, exists_eq_left'] at h
      exact ih w r (by scalar_tac) h

theorem probe_hit_false {m : BeqMap} {key : Std.U64} {a b : expr.Expr} {r : Bool}
    (h : expr.probe_hit m key a b = ok r) : r = false := by
  rw [expr.probe_hit] at h
  obtain ⟨o, -, h⟩ := bind_eq_ok_iff.mp h
  cases o with
  | none => simpa using h.symm
  | some ps => exact probe_hit_from_false ps.val.length 0#usize r (by scalar_tac) h

/-- The write-back (con-leche's `finish`) changes the table, never the
decision. -/
theorem beq_finish_fst {r rc : Bool} {m : BeqMap} {key : Std.U64}
    {a b : expr.Expr} {rm : Bool × BeqMap}
    (h : expr.beq_finish r m rc key a b = ok rm) : rm.1 = r := by
  rw [expr.beq_finish] at h
  cases r with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h]
  | true =>
    cases rc with
    | false =>
      simp only [if_true, Bool.false_eq_true, if_false, Result.ok.injEq] at h
      rw [← h]
    | true =>
      simp only [if_true] at h
      obtain ⟨m', -, h⟩ := bind_eq_ok_iff.mp h
      simp only [Result.ok.injEq] at h
      rw [← h]

/-- **The frame peeled, once.**  On a pair whose stored words agree, `beq_go`
is `beq_arm`'s own decision: the identity test is `false`, the word guard
passes, the probe misses (`probe_hit_false`) and the write-back passes the
`Bool` through (`beq_finish_fst`).  Everything below therefore reasons about
`beq_arm`. -/
theorem beq_go_arm {a b : expr.Expr} {m : BeqMap} {rm : Bool × BeqMap}
    (h : expr.beq_go m a b = ok rm) (hd : dataOf a = dataOf b) :
    ∃ rm' : Bool × BeqMap, expr.beq_arm m a b = ok rm' ∧ rm'.1 = rm.1 := by
  rw [expr.beq_go.eq_def] at h
  simp only [ptr_eq_eq, Bool.false_eq_true, if_false, data_eq, bind_tc_ok, hd,
    bne_self_eq_false] at h
  obtain ⟨rc, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i3, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨key, -, h⟩ := bind_eq_ok_iff.mp h
  cases rc with
  | true =>
    simp only [if_true] at h
    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
    rw [probe_hit_false hb2] at h
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, m1⟩ := q
    exact ⟨(r1, m1), hq, (beq_finish_fst h).symm⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, m1⟩ := q
    exact ⟨(r1, m1), hq, (beq_finish_fst h).symm⟩

/-- A non-recursive arm: one test, then the table unchanged. -/
theorem pure_step {test : Result Bool} {m : BeqMap} {rm : Bool × BeqMap} {v : Bool}
    (htest : ∀ y, test = ok y → y = v)
    (h : (do let y ← test; ok (y, m)) = ok rm) : rm.1 = v := by
  obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  rw [← h]
  exact htest y hy

/-- The `.fvar`/`.proj` arms: a field test decides the arm, then one recursive
call (`expr::beq_when`). -/
theorem when_step {P Q : Prop} [Decidable P] [Decidable Q] {test : Result Bool}
    {m : BeqMap} {x y : expr.Expr} {rm : Bool × BeqMap}
    (htest : ∀ c, test = ok c → c = decide P)
    (hrest : ∀ (m : BeqMap) (rm : Bool × BeqMap),
        expr.beq_go m x y = ok rm → rm.1 = decide Q)
    (h : (do let c ← test; expr.beq_when m c x y) = ok rm) :
    rm.1 = decide (P ∧ Q) := by
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  have e := htest c hc
  rw [expr.beq_when] at h
  cases c with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h]
    have hnp : ¬ P := of_decide_eq_false e.symm
    simp [hnp]
  | true =>
    simp only [if_true] at h
    have hp : P := of_decide_eq_true e.symm
    rw [hrest m rm h]
    simp [hp]

/-- The `.app` arm: the two children in order, aborting on the first `false`
(`expr::beq_both`). -/
theorem both_step {P Q : Prop} [Decidable P] [Decidable Q] {m : BeqMap}
    {x1 y1 x2 y2 : expr.Expr} {rm : Bool × BeqMap}
    (h1 : ∀ (m : BeqMap) (rm : Bool × BeqMap),
        expr.beq_go m x1 y1 = ok rm → rm.1 = decide P)
    (h2 : ∀ (m : BeqMap) (rm : Bool × BeqMap),
        expr.beq_go m x2 y2 = ok rm → rm.1 = decide Q)
    (h : expr.beq_both m x1 y1 x2 y2 = ok rm) : rm.1 = decide (P ∧ Q) := by
  rw [expr.beq_both] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r1, m1⟩ := q
  have e : r1 = decide P := h1 m (r1, m1) hq
  cases r1 with
  | false =>
    have h' : (ok (false, m1) : Result (Bool × BeqMap)) = ok rm := h
    simp only [Result.ok.injEq] at h'
    rw [← h']
    have hnp : ¬ P := of_decide_eq_false e.symm
    simp [hnp]
  | true =>
    have h' : expr.beq_go m1 x2 y2 = ok rm := h
    have hp : P := of_decide_eq_true e.symm
    rw [h2 m1 rm h']
    simp [hp]

/-- The `.lam`/`.forallE` arms: the binder datum decides the arm, then the
domain and the body (`expr::beq_both_when`). -/
theorem both_when_step {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R]
    {test : Result Bool} {m : BeqMap} {x1 y1 x2 y2 : expr.Expr}
    {rm : Bool × BeqMap}
    (htest : ∀ c, test = ok c → c = decide P)
    (h1 : ∀ (m : BeqMap) (rm : Bool × BeqMap),
        expr.beq_go m x1 y1 = ok rm → rm.1 = decide Q)
    (h2 : ∀ (m : BeqMap) (rm : Bool × BeqMap),
        expr.beq_go m x2 y2 = ok rm → rm.1 = decide R)
    (h : (do let c ← test; expr.beq_both_when m c x1 y1 x2 y2) = ok rm) :
    rm.1 = decide (P ∧ Q ∧ R) := by
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  have e := htest c hc
  rw [expr.beq_both_when] at h
  cases c with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h]
    have hnp : ¬ P := of_decide_eq_false e.symm
    simp [hnp]
  | true =>
    simp only [if_true] at h
    have hp : P := of_decide_eq_true e.symm
    rw [both_step h1 h2 h]
    simp [hp]

/-- The `.letE` arm: the type, the value, the body (`expr::beq_three`). -/
theorem three_step {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R]
    {m : BeqMap} {x1 y1 x2 y2 x3 y3 : expr.Expr} {rm : Bool × BeqMap}
    (h1 : ∀ (m : BeqMap) (rm : Bool × BeqMap),
        expr.beq_go m x1 y1 = ok rm → rm.1 = decide P)
    (h2 : ∀ (m : BeqMap) (rm : Bool × BeqMap),
        expr.beq_go m x2 y2 = ok rm → rm.1 = decide Q)
    (h3 : ∀ (m : BeqMap) (rm : Bool × BeqMap),
        expr.beq_go m x3 y3 = ok rm → rm.1 = decide R)
    (h : expr.beq_three m x1 y1 x2 y2 x3 y3 = ok rm) :
    rm.1 = decide (P ∧ Q ∧ R) := by
  rw [expr.beq_three] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r1, m1⟩ := q
  have e : r1 = decide P := h1 m (r1, m1) hq
  cases r1 with
  | false =>
    have h' : (ok (false, m1) : Result (Bool × BeqMap)) = ok rm := h
    simp only [Result.ok.injEq] at h'
    rw [← h']
    have hnp : ¬ P := of_decide_eq_false e.symm
    simp [hnp]
  | true =>
    have h' : expr.beq_both m1 x2 y2 x3 y3 = ok rm := h
    have hp : P := of_decide_eq_true e.symm
    rw [both_step h2 h3 h']
    simp [hp]

/-- The `.const` arm's `n == m && us == vs`, as its own function
(`expr::const_beq`). -/
theorem const_beq_refines {n n2 : name.Name} {us vs : alloc.vec.Vec level.Level}
    {c : Bool} (hn : NameWF n) (hn2 : NameWF n2) (hus : LevelsWF us)
    (hvs : LevelsWF vs) (h : expr.const_beq n us n2 vs = ok c) :
    c = decide (absName n = absName n2 ∧ absLevels us = absLevels vs) := by
  rw [expr.const_beq] at h
  exact guard_step (fun y hy => Name.beq_refines hn hn2 hy)
    (fun y hy => levels_beq_refines hus hvs hy) h

/-- The `.proj` arm's `s == s' && i == i'` (`expr::proj_head_beq`). -/
theorem proj_head_beq_refines {s1 s2 : name.Name} {i1 i2 : Std.U64} {c : Bool}
    (hs1 : NameWF s1) (hs2 : NameWF s2)
    (h : expr.proj_head_beq s1 i1 s2 i2 = ok c) :
    c = decide (absName s1 = absName s2 ∧ i1.val = i2.val) := by
  rw [expr.proj_head_beq] at h
  exact guard_step (fun y hy => Name.beq_refines hs1 hs2 hy)
    (fun y hy => u64_eq_test hy) h

/-- The word guard, once and for all: a stored-word mismatch *is* an
inequality, because `absExpr` is injective on well-formed nodes. -/
theorem beq_go_data_ne {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b)
    {m : BeqMap} {rm : Bool × BeqMap}
    (h : expr.beq_go m a b = ok rm) (hne : dataOf a ≠ dataOf b) :
    rm.1 = decide (absExpr a = absExpr b) := by
  rw [expr.beq_go.eq_def] at h
  simp only [ptr_eq_eq, Bool.false_eq_true, if_false, data_eq, bind_tc_ok] at h
  rw [if_pos (show (dataOf a != dataOf b) = true by simpa using hne),
    Result.ok.injEq] at h
  subst h
  refine (decide_eq_false ?_).symm
  intro hc
  exact hne (by rw [absExpr_injective ha hb hc])



/-- The descent is **sound and complete**: the `Bool` it returns is con-leche's
`decide (· = ·)` on the abstractions.  One case per `ExprWF` constructor pair;
the ninety off-diagonal ones are closed by the fact that `absExpr` maps the ten
kinds onto the ten con-leche constructors, and the word guard is discharged once
and for all by `beq_go_data_ne`. -/
theorem beq_go_abs {a : expr.Expr} (ha : ExprWF a) :
    ∀ b, ExprWF b → ∀ (m : BeqMap) (rm : Bool × BeqMap),
      expr.beq_go m a b = ok rm → rm.1 = decide (absExpr a = absExpr b) := by
  induction ha with
  | @bvar i1 e1 h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := bvar_inv h1
    intro b hb m rm h
    rcases eq_or_ne d1 (dataOf b) with hdd | hdd
    case inr => exact beq_go_data_ne (ExprWF.bvar h1) hb h (by simpa using hdd)
    obtain ⟨rm, h, hrm⟩ := beq_go_arm h (by simpa using hdd)
    rw [← hrm]
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      have hd2 : d1 = d2 := by simpa using hdd
      subst hd2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_] at h
      rw [pure_step (fun y hy => u64_eq_test hy) h]
      simp
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
  | @fvar idx1 ty1 e1 hty1 h1 ih1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := fvar_inv h1
    intro b hb m rm h
    rcases eq_or_ne d1 (dataOf b) with hdd | hdd
    case inr => exact beq_go_data_ne (ExprWF.fvar hty1 h1) hb h (by simpa using hdd)
    obtain ⟨rm, h, hrm⟩ := beq_go_arm h (by simpa using hdd)
    rw [← hrm]
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      have hd2 : d1 = d2 := by simpa using hdd
      subst hd2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_] at h
      rw [when_step (P := idx1.val = idx2.val) (Q := absExpr ty1 = absExpr ty2)
        (fun y hy => u64_eq_test hy) (fun m rm hr => ih1 ty2 hty2 m rm hr) h]
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.fvar.injEq]
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
  | @sort u1 e1 hu1 h1 =>
    obtain ⟨d1, _, -, rfl, -, -, -⟩ := sort_inv h1
    intro b hb m rm h
    rcases eq_or_ne d1 (dataOf b) with hdd | hdd
    case inr => exact beq_go_data_ne (ExprWF.sort hu1 h1) hb h (by simpa using hdd)
    obtain ⟨rm, h, hrm⟩ := beq_go_arm h (by simpa using hdd)
    rw [← hrm]
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      have hd2 : d1 = d2 := by simpa using hdd
      subst hd2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_] at h
      rw [pure_step (fun y hy => Level.beq_refines hu1 hu2 hy) h]
      simp
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
  | @mk_const n1 us1 e1 hn1 hus1 h1 =>
    obtain ⟨d1, _, -, rfl, -, -, -⟩ := mk_const_inv h1
    intro b hb m rm h
    rcases eq_or_ne d1 (dataOf b) with hdd | hdd
    case inr => exact beq_go_data_ne (ExprWF.mk_const hn1 hus1 h1) hb h (by simpa using hdd)
    obtain ⟨rm, h, hrm⟩ := beq_go_arm h (by simpa using hdd)
    rw [← hrm]
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      have hd2 : d1 = d2 := by simpa using hdd
      subst hd2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_] at h
      rw [pure_step (fun y hy => const_beq_refines hn1 hn2 hus1 hus2 hy) h]
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.const.injEq]
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
  | @app f1 a1 e1 hf1 ha1 h1 ihf1 iha1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := app_inv h1
    intro b hb m rm h
    rcases eq_or_ne d1 (dataOf b) with hdd | hdd
    case inr => exact beq_go_data_ne (ExprWF.app hf1 ha1 h1) hb h (by simpa using hdd)
    obtain ⟨rm, h, hrm⟩ := beq_go_arm h (by simpa using hdd)
    rw [← hrm]
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      have hd2 : d1 = d2 := by simpa using hdd
      subst hd2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_] at h
      rw [both_step (P := absExpr f1 = absExpr f2) (Q := absExpr a1 = absExpr a2)
        (fun m rm hr => ihf1 f2 hf2 m rm hr) (fun m rm hr => iha1 a2 ha2 m rm hr) h]
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.app.injEq]
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
  | @lam ty1 bo1 m1 e1 hty1 hbo1 hm1 h1 ihty1 ihbo1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := lam_inv h1
    intro b hb m rm h
    rcases eq_or_ne d1 (dataOf b) with hdd | hdd
    case inr => exact beq_go_data_ne (ExprWF.lam hty1 hbo1 hm1 h1) hb h (by simpa using hdd)
    obtain ⟨rm, h, hrm⟩ := beq_go_arm h (by simpa using hdd)
    rw [← hrm]
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      have hd2 : d1 = d2 := by simpa using hdd
      subst hd2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_] at h
      rw [both_when_step (P := absBinderMeta m1 = absBinderMeta m2)
        (Q := absExpr ty1 = absExpr ty2) (R := absExpr bo1 = absExpr bo2)
        (fun y hy => binder_meta_beq_refines hm1 hm2 hy)
        (fun m rm hr => ihty1 ty2 hty2 m rm hr)
        (fun m rm hr => ihbo1 bo2 hbo2 m rm hr) h]
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.lam.injEq, decide_eq_decide]
      tauto
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
  | @forall_e ty1 bo1 m1 e1 hty1 hbo1 hm1 h1 ihty1 ihbo1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := forall_e_inv h1
    intro b hb m rm h
    rcases eq_or_ne d1 (dataOf b) with hdd | hdd
    case inr => exact beq_go_data_ne (ExprWF.forall_e hty1 hbo1 hm1 h1) hb h (by simpa using hdd)
    obtain ⟨rm, h, hrm⟩ := beq_go_arm h (by simpa using hdd)
    rw [← hrm]
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      have hd2 : d1 = d2 := by simpa using hdd
      subst hd2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_] at h
      rw [both_when_step (P := absBinderMeta m1 = absBinderMeta m2)
        (Q := absExpr ty1 = absExpr ty2) (R := absExpr bo1 = absExpr bo2)
        (fun y hy => binder_meta_beq_refines hm1 hm2 hy)
        (fun m rm hr => ihty1 ty2 hty2 m rm hr)
        (fun m rm hr => ihbo1 bo2 hbo2 m rm hr) h]
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.forallE.injEq, decide_eq_decide]
      tauto
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
  | @let_e ty1 v1 bo1 e1 hty1 hv1 hbo1 h1 ihty1 ihv1 ihbo1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := let_e_inv h1
    intro b hb m rm h
    rcases eq_or_ne d1 (dataOf b) with hdd | hdd
    case inr => exact beq_go_data_ne (ExprWF.let_e hty1 hv1 hbo1 h1) hb h (by simpa using hdd)
    obtain ⟨rm, h, hrm⟩ := beq_go_arm h (by simpa using hdd)
    rw [← hrm]
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      have hd2 : d1 = d2 := by simpa using hdd
      subst hd2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_] at h
      rw [three_step (P := absExpr ty1 = absExpr ty2)
        (Q := absExpr v1 = absExpr v2) (R := absExpr bo1 = absExpr bo2)
        (fun m rm hr => ihty1 ty2 hty2 m rm hr)
        (fun m rm hr => ihv1 v2 hv2 m rm hr)
        (fun m rm hr => ihbo1 bo2 hbo2 m rm hr) h]
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.letE.injEq]
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
  | @lit l1 e1 hl1 h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := lit_inv h1
    intro b hb m rm h
    rcases eq_or_ne d1 (dataOf b) with hdd | hdd
    case inr => exact beq_go_data_ne (ExprWF.lit hl1 h1) hb h (by simpa using hdd)
    obtain ⟨rm, h, hrm⟩ := beq_go_arm h (by simpa using hdd)
    rw [← hrm]
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      have hd2 : d1 = d2 := by simpa using hdd
      subst hd2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_] at h
      rw [pure_step (fun y hy => literal_beq_refines hl1 hl2 hy) h]
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.lit.injEq]
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
  | @proj s1 i1 x1 e1 hs1 hx1 h1 ih1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := proj_inv h1
    intro b hb m rm h
    rcases eq_or_ne d1 (dataOf b) with hdd | hdd
    case inr => exact beq_go_data_ne (ExprWF.proj hs1 hx1 h1) hb h (by simpa using hdd)
    obtain ⟨rm, h, hrm⟩ := beq_go_arm h (by simpa using hdd)
    rw [← hrm]
    cases hb with
    | @bvar i2 e2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := bvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @fvar idx2 ty2 e2 hty2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := fvar_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @sort u2 e2 hu2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := sort_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @mk_const n2 us2 e2 hn2 hus2 h2 =>
      obtain ⟨d2, _, -, rfl, -, -, -⟩ := mk_const_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @app f2 a2 e2 hf2 ha2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := app_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lam ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lam_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @forall_e ty2 bo2 m2 e2 hty2 hbo2 hm2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := forall_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @let_e ty2 v2 bo2 e2 hty2 hv2 hbo2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := let_e_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @lit l2 e2 hl2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := lit_inv h2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_, Result.ok.injEq] at h
      rw [← h]
      simp
    | @proj s2 i2 x2 e2 hs2 hx2 h2 =>
      obtain ⟨d2, rfl, -, -, -⟩ := proj_inv h2
      have hd2 : d1 = d2 := by simpa using hdd
      subst hd2
      rw [expr.beq_arm.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, expr.Expr._0._simpLemma_,
        expr.ExprNode.kind._simpLemma_] at h
      rw [when_step (P := absName s1 = absName s2 ∧ i1.val = i2.val)
        (Q := absExpr x1 = absExpr x2)
        (fun y hy => proj_head_beq_refines hs1 hs2 hy)
        (fun m rm hr => ih1 x2 hx2 m rm hr) h]
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.proj.injEq, decide_eq_decide]
      tauto

/-! ## Reflexivity: the pointer fast path is transparent

`ptr_eq` is `false` in the model, so the model always descends where the real
program may answer `true` in `O(1)`.  The two agree because the descent is
reflexive, which is DESIGN.md §3.2's obligation and this lemma. -/

theorem levels_beq_from_refl {ls : alloc.vec.Vec level.Level} (hls : LevelsWF ls) :
    ∀ k : Nat, ∀ i : Std.Usize, ls.val.length - i.val ≤ k →
      expr.levels_beq_from ls ls i = ok true := by
  intro k
  induction k with
  | zero =>
    intro i hk
    rw [expr.levels_beq_from.eq_def]
    simp only []
    rw [if_pos (show i >= alloc.vec.Vec.len ls by scalar_tac)]
  | succ k ih =>
    intro i hk
    rw [expr.levels_beq_from.eq_def]
    simp only []
    by_cases hi : i.val ≥ ls.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len ls by scalar_tac)]
    · have hlt : i.val < ls.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ls.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ls i hlt)
      subst hyv
      rw [if_neg (show ¬ i >= alloc.vec.Vec.len ls by scalar_tac)]
      simp only [alloc.vec.Vec.index_slice_index, hy, hw, bind_tc_ok,
        Level.level_beq_refl (hls _ (List.getElem_mem hlt)), if_true]
      exact ih w (by scalar_tac)

theorem levels_beq_refl {ls : alloc.vec.Vec level.Level} (hls : LevelsWF ls) :
    expr.levels_beq ls ls = ok true := by
  rw [expr.levels_beq.eq_def]
  simp only []
  rw [if_neg (by simp)]
  exact levels_beq_from_refl hls ls.val.length 0#usize (by scalar_tac)

theorem literal_beq_refl {l : expr.Literal} (hl : LiteralWF l) :
    expr.literal_beq l l = ok true := by
  cases l with
  | NatVal n =>
    rw [expr.literal_beq]; simp only [rc_deref_eq, bind_tc_ok]; exact Nat.beq_refl n
  | StrVal s =>
    rw [expr.literal_beq]; simp only [rc_deref_eq, bind_tc_ok]; exact Name.str_eq_refl s

theorem binder_meta_beq_refl {m : expr.BinderMeta} (hm : BinderMetaWF m) :
    expr.binder_meta_beq m m = ok true := by
  rw [expr.binder_meta_beq]; simp only [rc_deref_eq, bind_tc_ok]
  exact PropWhen.beq_refl hm

/-- **Reflexivity, the transparency obligation of DESIGN.md §3.2** — in the
forward shape this development uses everywhere (task #5: *exact result on
success*).  The real program answers `true` on `beq e e` by the pointer test;
the model takes the slow path, and this says the slow path cannot answer
anything else.

Task #30 note: the *stronger* form task #20 had here, `expr.beq_go e e =
ok true`, additionally said that the descent **cannot fail**.  With the pair
memo threaded through it, that now also asserts that `ron::HashMap`'s `get`
and `insert` cannot fail — the *totality* half of task #16, which the
forward-style development of §3.5 does not have for any function (every
`*_refines` in `proof/` reasons from `f x = ok y`).  So the statement is the
forward one, and it is a corollary of `beq_go_abs` rather than a second
hundred-case induction.  Nothing else in `proof/` used the strong form. -/
theorem beq_go_refl {e : expr.Expr} (h : ExprWF e) {m : BeqMap}
    {rm : Bool × BeqMap} (hr : expr.beq_go m e e = ok rm) : rm.1 = true := by
  simpa using beq_go_abs h e h m rm hr

/-! ## The public statements, under the `ConRon/Refine/README.md` names -/

/-- `expr::beq` -- and the `Eq2` dictionary that *is* it -- decides equality of
the abstracted terms **exactly**: the `Bool` the Rust returns is the `Bool`
con-leche's `Expr.beq` returns (`= decide (· = ·)`, `Expr.lean:975`).
Task #30: `expr::beq` allocates the pair memo and calls the descent, whose
decision is the memo-free one (`beq_go_abs`, and `probe_hit_false` for why the
memo never enters it). -/
theorem beq_refines {a b : expr.Expr} {c : Bool} (ha : ExprWF a) (hb : ExprWF b)
    (h : expr.beq a b = ok c) : c = decide (absExpr a = absExpr b) := by
  rw [expr.beq] at h
  simp only [ptr_eq_eq, Bool.false_eq_true, if_false, data_eq, bind_tc_ok] at h
  by_cases hd : dataOf a = dataOf b
  · rw [if_neg (show ¬ (dataOf a != dataOf b) = true by simp [hd])] at h
    obtain ⟨m, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨rm, hrm, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r, m'⟩ := rm
    have h' : (ok r : Result Bool) = ok c := h
    simp only [Result.ok.injEq] at h'
    rw [← h']
    exact beq_go_abs ha b hb m (r, m') hrm
  · rw [if_pos (show (dataOf a != dataOf b) = true by simpa using hd),
      Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    intro hc
    exact hd (by rw [absExpr_injective ha hb hc])

/-- `expr::beq` is reflexive on well-formed terms: the real program's pointer
fast path answers what the model's descent answers (DESIGN.md §3.2).  Forward
shape since task #30 — see `beq_go_refl`. -/
theorem beq_refl {e : expr.Expr} (h : ExprWF e) {c : Bool}
    (hc : expr.beq e e = ok c) : c = true := by
  simpa using beq_refines h h hc

/-- The same fact as con-leche states it: `Expr.beq` is `decide (· = ·)`. -/
theorem beq_exact {a b : expr.Expr} {c : Bool} (ha : ExprWF a) (hb : ExprWF b)
    (h : expr.beq a b = ok c) :
    c = ConLeche.Expr.beq (absExpr a) (absExpr b) := beq_refines ha hb h

/-! ## The hash-map dictionaries

`Hashable` is the `hash` field read and `Eq2` is `beq`, which is what makes an
`Expr` a memo key (task #7's own traits, not Lean's classes).  The `Hashable`
side gets no refinement lemma, by §3.2: a hash only picks a bucket, and the
abstract-map relation of §3.3 does not see it. -/

theorem hash64_eq (e : expr.Expr) :
    expr.Expr.Insts.Con_ron_coreRonHashmapHashable.hash64 e = expr.hash e := rfl

theorem eq2_eq (a b : expr.Expr) :
    expr.Expr.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = expr.beq a b := rfl

/-- The `Eq2` dictionary decides equality of the abstracted terms exactly. -/
theorem eq2_refines {a b : expr.Expr} {c : Bool} (ha : ExprWF a) (hb : ExprWF b)
    (h : expr.Expr.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok c) :
    c = decide (absExpr a = absExpr b) := by
  rw [eq2_eq] at h; exact beq_refines ha hb h

/-- The `Eq2` dictionary is reflexive (the `Hashable`/`Eq2` pair is what
`ron::hashmap` needs of a key: equal keys hash equally, which is immediate
here since both are functions of the node). -/
theorem eq2_refl {e : expr.Expr} (h : ExprWF e) {c : Bool}
    (hc : expr.Expr.Insts.Con_ron_coreRonHashmapEq2.eq2 e e = ok c) : c = true := by
  rw [eq2_eq] at hc; exact beq_refl h hc

/-! ## What has no refinement lemma, and why

* `expr::hash`, `expr::binder_meta_hash`, `expr::literal_hash` and the
  `Hashable` dictionary: DESIGN.md §3.2.  `mixHash` is opaque in Lean, the port
  hashes its own bignums and strings, and a hash value only ever picks a memo
  bucket -- which the abstract-map relation of §3.3 does not see.  The *other*
  fields of the same word are related, bit for bit, by `wf_data`.
* `expr::sat_range`, `expr::max_u64`, `expr::pack_data`, `expr::hash32` and the
  four `*_of_data` readers get `*_val` lemmas rather than `*_refines` ones:
  they are arithmetic on the machine word, below the abstraction.

## Axiom census (DESIGN.md §5, the P3 gate)

Nothing from Aeneas's library, nothing from the `Rc` models, no `sorry`, and --
as for `PropWhen` -- no `import all`: `absExpr` and every statement here go
through con-leche's public API. -/

/--
info: 'ConRon.Refine.Expr.app_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms app_refines

/--
info: 'ConRon.Refine.Expr.beq_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beq_exact

/--
info: 'ConRon.Refine.Expr.bvar_b_raw_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bvar_b_raw_refines

end ConRon.Refine.Expr
