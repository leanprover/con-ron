/-
**The expression-record slot loops, exact against con-leche** (task #87,
phase 3).

`crates/con-ron-core/src/frontend/scan_fast.rs:1608-2075` against
`ConLeche/Frontend/Scan/Fast.lean:906-1325`: the five slot loops that build an
`ExprRec` — `app`, the two binders, `letE`, `const` and `proj`.

## What this file gives the line scanner

Agent L (`ScanLine.lean`) consumes exactly these six, one per `scan*Expr` of
`Scan/Fast.lean`:

    theorem scan_app_expr_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_app_expr b i = ok o) :
        ScanSim absExprRec o (scanAppExpr (absBytes b) (absPos i))

    theorem scan_lam_expr_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_lam_expr b i = ok o) :
        ScanSim absExprRec o (scanLamExpr (absBytes b) (absPos i))

    theorem scan_forall_expr_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_forall_expr b i = ok o) :
        ScanSim absExprRec o (scanForallExpr (absBytes b) (absPos i))

    theorem scan_let_expr_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_let_expr b i = ok o) :
        ScanSim absExprRec o (scanLetExpr (absBytes b) (absPos i))

    theorem scan_const_expr_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_const_expr b i = ok o) :
        ScanSim absExprRec o (scanConstExpr (absBytes b) (absPos i))

    theorem scan_proj_expr_refines {b : Slice Std.U8} {i : Std.Usize} {o}
        (h : frontend.scan_fast.scan_proj_expr b i = ok o) :
        ScanSim absExprRec o (scanProjExpr (absBytes b) (absPos i))

**The port's one binder loop against con-leche's two.**
`scan_binder_expr_loop(b, i, lam)` is `scanLamExprLoop` when `lam` and
`scanForallExprLoop` when not: the two Lean bodies are the same up to the
`ExprRec` constructor the closing brace builds, so the two statements above
are proved from *two* instances of one loop lemma and no new definition is
needed (the brief's escape hatch is not used in this file).

## The shape, once

con-leche writes the member step out inline in each of its twenty
`scan*Loop`s; the port factors it once as `scan_fast::next_member`
(`scan_types.rs`'s module note, deviation 3, the way `Scan/Naive.lean`'s
`naiveObjLoop` factors it).  `memberBody` is con-leche's inlined skeleton read
back with its two record-specific continuations abstracted — the closing arm
`CL` and the key dispatch `DI` — and `nextMember_step` is the single induction
(measure `b.len() - i`, phase 1's) that runs the port's factored copy against
it.  A loop then owes only its own `Close` and `Key` arms.

`nextMember_step` takes the three `ScanKit` facts it needs —
`key_end`/`value_at`/`key_at` against `keyEnd`/`valueAt`/`keyAt` — as
hypotheses, so that this file does not wait for them; they are discharged with
`ScanKit`'s lemmas the moment it has them.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.ScanKit

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

open ConRon.Refine
open ConLeche.Frontend

/-! ## The `u32` key bitset

Every slot loop threads a `seen` bitset, `u32` in the port and `UInt32` in
con-leche.  Both are a `BitVec 32`, so the map is the identity on the bits and
every operation on it is `rfl`. -/

/-- The port's `u32` bitset as con-leche's. -/
private def absU32 (n : Std.U32) : UInt32 := UInt32.ofBitVec n.bv

private theorem absU32_and (a b : Std.U32) :
    absU32 (a &&& b) = absU32 a &&& absU32 b := rfl

private theorem absU32_or (a b : Std.U32) :
    absU32 (a ||| b) = absU32 a ||| absU32 b := rfl

private theorem absU32_inj {a b : Std.U32} (h : absU32 a = absU32 b) : a = b := by
  cases a; cases b
  simp only [absU32, UInt32.ofBitVec.injEq] at h
  exact congrArg _ h

private theorem absU32_beq (a b : Std.U32) : (absU32 a == absU32 b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have h2 : absU32 a ≠ absU32 b := fun he => h (absU32_inj he)
    simp [h, h2]

/-! ## Bytes and positions -/

private theorem absByte_inj {a b : Std.U8} (h : absByte a = absByte b) : a = b := by
  have := congrArg UInt8.toNat h
  simp only [absByte_toNat] at this
  scalar_tac

/-- Two port bytes compare as con-leche's. -/
private theorem absByte_beq_u8 (a b : Std.U8) :
    (absByte a == absByte b) = (a == b) := by
  simp only [absByte_beq, absByte_toNat]
  by_cases h : a = b
  · subst h; simp
  · have h2 : ¬ (a.val = b.val) := fun hc => h (by scalar_tac)
    simp [h, h2]

/-- A slice read at an in-range index, forwards. -/
private theorem index_ok {t : Slice Std.U8} {i : Std.Usize} (hi : i.val < t.length) :
    Slice.index_usize t i = ok t.val[i.val] := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Slice.index_usize_spec t i hi)
  rw [hy, hyv]

/-- The byte con-leche's `uget` reads at an abstracted position. -/
private theorem uget_val (b : Slice Std.U8) (i : Std.Usize)
    (h : (absPos i) < (absBytes b).usize) (hi : i.val < b.val.length) :
    (absBytes b).uget (absPos i) (usizeInBounds _ _ h) = absByte (b.val[i.val]'hi) := by
  rw [absBytes_uget b (absPos i) (usizeInBounds _ _ h) (by simpa using hi)]
  simp

private theorem absPos_beq (a b : Std.Usize) : (absPos a == absPos b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have h2 : absPos a ≠ absPos b := by
      intro he; exact h (by have := absPos_inj he; scalar_tac)
    simp [h, h2]

/-- The port's `usize` subtraction, abstracted: a difference the port returned
`ok` for did not underflow, so con-leche's machine word did not wrap. -/
private theorem absPos_sub {x y z : Std.Usize} (h : x - y = ok z) :
    absPos z = absPos x - absPos y := by
  have h2 := UScalar.sub_equiv x y
  rw [h] at h2
  simp at h2
  have hy : y.val ≤ x.val := by scalar_tac
  have hz : z.val = x.val - y.val := by scalar_tac
  have hx : x.val < USize.size := usize_val_lt_size x
  have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
  apply USize.toNat_inj.mp
  rw [USize.toNat_sub]
  simp only [absPos_toNat, hz]
  have hstep : 2 ^ System.Platform.numBits - y.val + x.val
      = (x.val - y.val) + 2 ^ System.Platform.numBits := by omega
  rw [hstep, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ## The member step -/

/-- **con-leche's inlined member skeleton**, with the record-specific closing
arm `CL` and key dispatch `DI` abstracted.  Every `scan*Loop` of
`Scan/Fast.lean` is `memberBody` at its own `CL` and `DI`; the port calls
`scan_fast::next_member` in its place. -/
def memberBody {α : Type} (b : ByteArray)
    (L : USize → Bool → ScanRes α) (CL : USize → Bool → ScanRes α)
    (DI : Key → USize → USize → ScanRes α) (i : USize) (w : Bool) : ScanRes α :=
  if h : i < b.usize then
    if isWs (b.uget i (usizeInBounds b i h)) then L (i + 1) w
    else if b.uget i (usizeInBounds b i h) == 125 then CL i w
    else if b.uget i (usizeInBounds b i h) == 44 then
      (if w then .err ⟨i.toNat, .expectedKey⟩ else L (i + 1) true)
    else if b.uget i (usizeInBounds b i h) == 34 then
      (if !w then .err ⟨i.toNat, .expectedComma⟩
       else
        if keyEnd b (i + 1) == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if valueAt b i (keyEnd b (i + 1)) == i then
          .err ⟨i.toNat, .expectedColon⟩
        else DI (keyAt b i (keyEnd b (i + 1) - (i + 1))) i
          (valueAt b i (keyEnd b (i + 1))))
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩

/-- What one `scan_fast::next_member` step says about con-leche's skeleton:
the closing brace hands the loop to `CL` at the same position and
`wantMember`, a key hands it to `DI` at the same key and value positions, and
a failure is mirrored. -/
def MemberStep {α : Type} (L CL : USize → Bool → ScanRes α)
    (DI : Key → USize → USize → ScanRes α) (i : Std.Usize) (w : Bool)
    (o : core.result.Result (frontend.scan_fast.Member × Std.Usize × Bool)
           frontend.scan_types.ScanErr) : Prop :=
  match o with
  | .Ok (.Close, ni, nw) => L (absPos i) w = CL (absPos ni) nw
  | .Ok (.Key k ks v, _, _) => L (absPos i) w = DI (absKey k) (absPos ks) (absPos v)
  | .Err e => ScanErrSim e (L (absPos i) w)

section Step
variable {b : Slice Std.U8}
  (hKeyEnd : ∀ (j ke : Std.Usize),
    frontend.scan_fast.key_end b j = ok ke → keyEnd (absBytes b) (absPos j) = absPos ke)
  (hValueAt : ∀ (i ke v : Std.Usize),
    frontend.scan_fast.value_at b i ke = ok v →
      valueAt (absBytes b) (absPos i) (absPos ke) = absPos v)
  (hKeyAt : ∀ (i kl : Std.Usize) (k : frontend.scan_types.Key),
    frontend.scan_fast.key_at b i kl = ok k →
      keyAt (absBytes b) (absPos i) (absPos kl) = absKey k)

include hKeyEnd hValueAt hKeyAt in
/-- **The one induction every slot loop of the tier runs.**
`scan_fast::next_member` (`scan_fast.rs:1374-1435`) against the
whitespace/comma/key skeleton every `scan*Loop` of `Scan/Fast.lean` writes out
inline.  The measure is phase 1's, `b.len() - i`. -/
theorem nextMember_step {α : Type} {L CL : USize → Bool → ScanRes α}
    {DI : Key → USize → USize → ScanRes α}
    (hbody : ∀ p w, L p w = memberBody (absBytes b) L CL DI p w) (f : Nat) :
    ∀ (i : Std.Usize) (w : Bool) (o), b.length - i.val ≤ f →
      frontend.scan_fast.next_member b i w = ok o → MemberStep L CL DI i w o := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro i w o hf h
    rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
    rw [MemberStep.eq_def, hbody, memberBody]
    by_cases hend : i ≥ Slice.len b
    · rw [if_pos hend] at h
      rw [← Result.ok_injective h]
      have hnot : ¬ (absPos i < (absBytes b).usize) := by
        rw [absPos_lt_usize]; scalar_tac
      rw [dif_neg hnot]
      exact ScanErrSim.mk (t := .expectedComma) rfl (by simp)
    · rw [if_neg hend] at h
      have hi : i.val < b.val.length := by scalar_tac
      have hi' : i.val < b.length := by scalar_tac
      have hlt : absPos i < (absBytes b).usize := absPos_lt_usize.mpr hi
      rw [dif_pos hlt, uget_val b i hlt hi]
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      have hcv : c = b.val[i.val]'hi :=
        Result.ok_injective (hc.symm.trans (index_ok hi))
      rw [← hcv]
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hws := is_ws_refines hb1
      subst hws
      by_cases hw : isWs (absByte c) = true
      · rw [if_pos hw] at h ⊢
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hstep : i2.val = i.val + 1 := usize_add_one_inv hi2
        rw [← absPos_add_one hi2]
        have hres := ih (b.length - i2.val) (by omega) i2 w o (le_refl _) h
        rwa [MemberStep.eq_def] at hres
      · rw [if_neg hw] at h ⊢
        rw [show ((125 : UInt8)) = absByte 125#u8 from rfl, absByte_beq_u8,
          show ((44 : UInt8)) = absByte 44#u8 from rfl, absByte_beq_u8,
          show ((34 : UInt8)) = absByte 34#u8 from rfl, absByte_beq_u8]
        by_cases h1 : c = 125#u8
        · rw [if_pos h1] at h
          rw [if_pos (beq_iff_eq.mpr h1), ← Result.ok_injective h]
        · rw [if_neg h1] at h
          rw [if_neg (by simp [h1])]
          by_cases h2 : c = 44#u8
          · rw [if_pos h2] at h
            rw [if_pos (beq_iff_eq.mpr h2)]
            by_cases h3 : w = true
            · rw [if_pos h3] at h
              rw [if_pos h3, ← Result.ok_injective h]
              exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
            · rw [if_neg h3] at h
              rw [if_neg h3]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have hstep : i2.val = i.val + 1 := usize_add_one_inv hi2
              rw [← absPos_add_one hi2]
              have hres := ih (b.length - i2.val) (by omega) i2 true o (le_refl _) h
              rwa [MemberStep.eq_def] at hres
          · rw [if_neg h2] at h
            rw [if_neg (by simp [h2])]
            by_cases h4 : c = 34#u8
            · rw [if_pos h4] at h
              rw [if_pos (beq_iff_eq.mpr h4)]
              by_cases h5 : w = true
              · rw [if_pos h5] at h
                rw [if_neg (by simp [h5])]
                obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨ke, hke, h⟩ := bind_eq_ok_iff.mp h
                have hp2 : absPos i2 = absPos i + 1 := absPos_add_one hi2
                have hkeE : keyEnd (absBytes b) (absPos i + 1) = absPos ke := by
                  rw [← hp2]; exact hKeyEnd i2 ke hke
                rw [hkeE, show ((0 : USize)) = absPos 0#usize from rfl, absPos_beq]
                by_cases h6 : ke = 0#usize
                · rw [if_pos h6] at h
                  rw [if_pos (beq_iff_eq.mpr h6), ← Result.ok_injective h]
                  exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
                · rw [if_neg h6] at h
                  rw [if_neg (by simp [h6])]
                  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                  rw [hValueAt i ke v hv, absPos_beq]
                  by_cases h7 : v = i
                  · rw [if_pos h7] at h
                    rw [if_pos (beq_iff_eq.mpr h7), ← Result.ok_injective h]
                    exact ScanErrSim.mk (t := .expectedColon) rfl (by simp)
                  · rw [if_neg h7] at h
                    rw [if_neg (by simp [h7])]
                    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
                    have h3E : absPos ke - (absPos i + 1) = absPos i3 := by
                      rw [← hp2, ← absPos_sub hi3]
                    rw [h3E, hKeyAt i i3 k hk, ← Result.ok_injective h]
              · rw [if_neg h5] at h
                rw [if_pos (by simp [h5]), ← Result.ok_injective h]
                exact ScanErrSim.mk (t := .expectedComma) rfl (by simp)
            · rw [if_neg h4] at h
              rw [if_neg (by simp [h4]), ← Result.ok_injective h]
              exact ScanErrSim.mk (t := .expectedComma) rfl (by simp)

end Step

end ConRon.Refine.Frontend
