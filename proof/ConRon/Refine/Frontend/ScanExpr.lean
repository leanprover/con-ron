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

Every one is **proved**, and every one is `<name>_of` applied to the two leaf
facts the tier still owes:

* `kf : KitFacts b` — `ScanObj`'s bundle of the three `ScanKit` leaves the
  member step needs.  `ScanKit` has `key_end_refines` and `value_at_refines`;
  it still owes **`key_at_refines`**.
* `hbi : BinderInfoRefines b` — `scan_fast::scan_binder_info` against
  `Scan/Fast.lean:657-666 scanBinderInfo`, which is `ScanStr`'s
  `scan_binder_info_refines`.  Only the two binder lemmas take it.

So the shipped names today are

    scan_app_expr_refines_of    (kf)        h
    scan_proj_expr_refines_of   (kf)        h
    scan_const_expr_refines_of  (kf)        h
    scan_let_expr_refines_of    (kf)        h
    scan_lam_expr_refines_of    (kf) (hbi)  h
    scan_forall_expr_refines_of (kf) (hbi)  h

and the six hypothesis-free statements above are three lines each — `fun h =>
<name>_of (kitFacts b) h` — the moment `ScanKit.key_at_refines` and
`ScanStr.scan_binder_info_refines` land.  Nothing else in this file is
waiting on anything.

**The port's one binder loop against con-leche's two.**
`scan_binder_expr_loop(b, i, lam)` is `scanLamExprLoop` when `lam` and
`scanForallExprLoop` when not: the two Lean bodies are the same up to the
`ExprRec` constructor the closing brace builds, so the two statements above
come from *two* instances of one loop lemma and no new definition is needed
(the brief's escape hatch is not used in this file).

## The shape, once

con-leche writes the member step out inline in each of its twenty
`scan*Loop`s; the port factors it once as `scan_fast::next_member`
(`scan_types.rs`'s module note, deviation 3).  `ScanObj`'s `memberBody` is
con-leche's inlined skeleton with the two record-specific continuations
abstracted — the closing arm `CL` and the key dispatch `DI` — and
`nextMember_step` runs the port's factored copy against it, so a loop owes
only its own `Close` and `Key` arms.  `natSlot`/`natSlot_step` do the same for
`scan_fast::slot_nat`, the `numEnd`/`readNatAt`/`noProgress` chain every
`Nat`-valued slot writes out.  (Both were written here and moved to `ScanObj`
by the coordinator's ruling; see `ScanObj`'s "The shared object-member
step".)

What stays here is phase 1's two measure facts — `next_member_ge` and
`next_member_lt`, `private` in `Refine/Frontend/ScanWF.lean` — plus
`slot_nat_prog`, and the `seen`-bitset bridges.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.ScanObj

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

open ConRon.Refine
open ConLeche.Frontend

/-! ## Plumbing -/

/-- An Aeneas `err` arm, read forwards. -/
private theorem err_val {T : Type} {offset : Std.Usize}
    {what : frontend.scan_types.ErrTag} {x : core.result.Result (T × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.err T offset what = ok x) : x = .Err ⟨offset, what⟩ := by
  rw [frontend.scan_fast.err] at h
  exact (Result.ok_injective h).symm

/-- Every error arm of a scanner is `scan_fast::err`, which never yields an
`Ok`. -/
private theorem err_ne_ok {T : Type} {offset : Std.Usize}
    {what : frontend.scan_types.ErrTag} {x : T × Std.Usize}
    (h : frontend.scan_fast.err T offset what = ok (.Ok x)) : False := by
  simp [frontend.scan_fast.err] at h

/-- A pure value the extraction lifted into `Result`. -/
private theorem lift_val {s r : Std.U32} (h : lift s = ok r) : r = s := by
  simpa using h.symm

section Step
variable {b : Slice Std.U8}

/-! ## The cursor never moves backwards

Phase 1's two measure facts (`Refine/Frontend/ScanWF.lean`, where they are
`private`), and the slot's own progress guard.  They belong with
`next_member` in `ScanKit`. -/

private theorem next_member_ge {b : Slice Std.U8} (f : Nat) :
    ∀ (i : Std.Usize) (w : Bool) (k : frontend.scan_types.Key)
      (ks v ni : Std.Usize) (nw : Bool),
      b.length - i.val ≤ f →
      frontend.scan_fast.next_member b i w
        = ok (.Ok (frontend.scan_fast.Member.Key k ks v, ni, nw)) →
      i.val ≤ ks.val := by
  induction f with
  | zero =>
    intro i w k ks v ni nw hf h
    rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
    rw [if_pos (show i ≥ Slice.len b by scalar_tac)] at h
    simp at h
  | succ f ih =>
    intro i w k ks v ni nw hf h
    rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
    by_cases hend : i ≥ Slice.len b
    · rw [if_pos hend] at h; simp at h
    · rw [if_neg hend] at h
      have hi : i.val < b.length := by scalar_tac
      obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w1, -, h⟩ := bind_eq_ok_iff.mp h
      by_cases hws : w1 = true
      · rw [if_pos hws] at h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have h1 : i2.val = i.val + 1 := usize_add_one_inv hi2
        have h2 := ih i2 w k ks v ni nw (by omega) h
        omega
      · rw [if_neg hws] at h
        by_cases hc1 : c = 125#u8
        · rw [if_pos hc1] at h; simp at h
        · rw [if_neg hc1] at h
          by_cases hc2 : c = 44#u8
          · rw [if_pos hc2] at h
            by_cases hw : w = true
            · rw [if_pos hw] at h; simp at h
            · rw [if_neg hw] at h
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have h1 : i2.val = i.val + 1 := usize_add_one_inv hi2
              have h2 := ih i2 true k ks v ni nw (by omega) h
              omega
          · rw [if_neg hc2] at h
            by_cases hc3 : c = 34#u8
            · rw [if_pos hc3] at h
              by_cases hw : w = true
              · rw [if_pos hw] at h
                obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨ke, -, h⟩ := bind_eq_ok_iff.mp h
                by_cases hke : ke = 0#usize
                · rw [if_pos hke] at h; simp at h
                · rw [if_neg hke] at h
                  obtain ⟨v1, -, h⟩ := bind_eq_ok_iff.mp h
                  by_cases hv : v1 = i
                  · rw [if_pos hv] at h; simp at h
                  · rw [if_neg hv] at h
                    obtain ⟨i3, -, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨k1, -, h⟩ := bind_eq_ok_iff.mp h
                    simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                      Prod.mk.injEq, frontend.scan_fast.Member.Key.injEq] at h
                    obtain ⟨⟨-, hks, -⟩, -⟩ := h
                    subst hks
                    exact le_refl _
              · rw [if_neg hw] at h; simp at h
            · rw [if_neg hc3] at h; simp at h

private theorem next_member_lt {b : Slice Std.U8} {i : Std.Usize} {w : Bool}
    {x : frontend.scan_fast.Member × Std.Usize × Bool}
    (h : frontend.scan_fast.next_member b i w = ok (.Ok x)) : i.val < b.length := by
  by_contra hc
  rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
  rw [if_pos (show i ≥ Slice.len b by scalar_tac)] at h
  simp at h

/-- `scan_fast::slot_nat` closes with the module's `prog` guard, so a slot that
succeeded really consumed at least one byte. -/
private theorem slot_nat_prog {b : Slice Std.U8} {ks v e : Std.Usize} {x : Std.U64}
    (h : frontend.scan_fast.slot_nat b ks v = ok (.Ok (x, e))) : ks.val < e.val := by
  rw [frontend.scan_fast.slot_nat] at h
  obtain ⟨e1, -, h⟩ := bind_eq_ok_iff.mp h
  by_cases h1 : e1 = v
  · rw [if_pos h1] at h; exact (err_ne_ok h).elim
  · rw [if_neg h1] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    rw [frontend.scan_fast.prog, Result.ok.injEq] at hb1
    by_cases h2 : b1 = true
    · rw [if_pos h2] at h
      obtain ⟨r, -, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err er => simp at h
      | Ok y =>
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        rw [← hb1] at h2
        scalar_tac
    · rw [if_neg h2] at h; exact (err_ne_ok h).elim

/-! ## The `seen` bitset, as the two sides spell it

`scan_fast::dup(seen, bit)` is con-leche's `seen &&& bit != 0`, the closing
arm's `seen &&& m != m` is the same mask read the other way, and `seen ||| bit`
is the install.  One lemma per literal, so that `simp only` can pick the one
the key in hand uses. -/

private theorem absU32_bne (a b : Std.U32) : (absU32 a != absU32 b) = (a != b) := by
  simp only [bne, absU32_beq]

private theorem bits_abs (s n m : Std.U32) (d e : UInt32)
    (hd : d = absU32 n) (he : e = absU32 m) :
    (absU32 s &&& d != e) = ((s &&& n) != m) := by
  rw [hd, he, ← absU32_and, absU32_bne]

private theorem or_lit (s n : Std.U32) (d : UInt32) (hd : d = absU32 n) :
    absU32 s ||| d = absU32 (s ||| n) := by rw [hd, absU32_or]

private theorem dup_abs1 (s : Std.U32) :
    (absU32 s &&& 1 != 0) = ((s &&& 1#u32) != 0#u32) := bits_abs s 1#u32 0#u32 1 0 rfl rfl
private theorem dup_abs2 (s : Std.U32) :
    (absU32 s &&& 2 != 0) = ((s &&& 2#u32) != 0#u32) := bits_abs s 2#u32 0#u32 2 0 rfl rfl
private theorem dup_abs4 (s : Std.U32) :
    (absU32 s &&& 4 != 0) = ((s &&& 4#u32) != 0#u32) := bits_abs s 4#u32 0#u32 4 0 rfl rfl
private theorem dup_abs8 (s : Std.U32) :
    (absU32 s &&& 8 != 0) = ((s &&& 8#u32) != 0#u32) := bits_abs s 8#u32 0#u32 8 0 rfl rfl
private theorem dup_abs16 (s : Std.U32) :
    (absU32 s &&& 16 != 0) = ((s &&& 16#u32) != 0#u32) := bits_abs s 16#u32 0#u32 16 0 rfl rfl

private theorem mask_abs3 (s : Std.U32) :
    (absU32 s &&& 3 != 3) = ((s &&& 3#u32) != 3#u32) := bits_abs s 3#u32 3#u32 3 3 rfl rfl
private theorem mask_abs7 (s : Std.U32) :
    (absU32 s &&& 7 != 7) = ((s &&& 7#u32) != 7#u32) := bits_abs s 7#u32 7#u32 7 7 rfl rfl
private theorem mask_abs15 (s : Std.U32) :
    (absU32 s &&& 15 != 15) = ((s &&& 15#u32) != 15#u32) :=
  bits_abs s 15#u32 15#u32 15 15 rfl rfl
private theorem mask_abs27 (s : Std.U32) :
    (absU32 s &&& 27 != 27) = ((s &&& 27#u32) != 27#u32) :=
  bits_abs s 27#u32 27#u32 27 27 rfl rfl

private theorem or_abs1 (s : Std.U32) : absU32 s ||| 1 = absU32 (s ||| 1#u32) :=
  or_lit s 1#u32 1 rfl
private theorem or_abs2 (s : Std.U32) : absU32 s ||| 2 = absU32 (s ||| 2#u32) :=
  or_lit s 2#u32 2 rfl
private theorem or_abs4 (s : Std.U32) : absU32 s ||| 4 = absU32 (s ||| 4#u32) :=
  or_lit s 4#u32 4 rfl
private theorem or_abs8 (s : Std.U32) : absU32 s ||| 8 = absU32 (s ||| 8#u32) :=
  or_lit s 8#u32 8 rfl
private theorem or_abs16 (s : Std.U32) : absU32 s ||| 16 = absU32 (s ||| 16#u32) :=
  or_lit s 16#u32 16 rfl

private theorem zero_abs (s : Std.U32) : (absU32 s != 0) = (s != 0#u32) := by
  rw [show ((0 : UInt32)) = absU32 0#u32 from rfl, absU32_bne]

/-- `scan_fast::dup`, read forwards. -/
private theorem dup_val {seen bit : Std.U32} {r : Bool}
    (h : frontend.scan_fast.dup seen bit = ok r) : r = ((seen &&& bit) != 0#u32) := by
  rw [frontend.scan_fast.dup] at h
  exact (by simpa using h : ((seen &&& bit) != 0#u32) = r).symm

/-- The opening brace of every `scan*Expr`. -/
private theorem brace_abs {b : Slice Std.U8} {i : Std.Usize} {c : Std.U8}
    (h : frontend.scan_fast.byte_at b i = ok c) :
    (byteAt (absBytes b) (absPos i) == 123) = (c == 123#u8) := by
  rw [← byte_at_refines h, show ((123 : UInt8)) = absByte 123#u8 from rfl, absByte_beq_u8]

/-! ## A slot a sub-scanner fills

`pw`, `nondep` and `us` are not `Nat`s: the port calls the sub-scanner, then
closes with the module's `prog` guard, exactly as con-leche's
`match scanX b v with | .err e => .err e | .ok x e => if _hj : i < e then …`.
That `match` is written out inline in the dispatch below rather than factored
into a `subSlot` helper: a helper of its own introduces a **new matcher**, and
two matchers on a stuck scrutinee are not definitionally equal, so the
`hbody` `rfl` against `scan*Loop.eq_def` fails.  Written inline, Lean reuses
con-leche's matcher and the `rfl` goes through; the sub-scanner's `ScanSim` is
then rewritten into the scrutinee, which reduces the `match` by `iota`. -/

/-- `scan_fast::prog`, read forwards. -/
private theorem prog_val {ks e : Std.Usize} {r : Bool}
    (h : frontend.scan_fast.prog ks e = ok r) : r = decide (ks.val < e.val) := by
  rw [frontend.scan_fast.prog] at h
  rw [← Result.ok_injective h]
  exact decide_eq_decide.mpr (by constructor <;> (intro hx; scalar_tac))

/-! ## `scan_app_expr`

`scan_fast.rs:1608-1673` against `Scan/Fast.lean:906-959`.  The smallest slot
loop and the template for the four below: two `Nat` slots, a two-bit `seen`,
and `ExprRec::App` at the closing brace. -/

private theorem scan_app_expr_loop_aux (kf : KitFacts b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (arg fnx : Std.U64) o,
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_app_expr_loop_loop w b i seen arg fnx = ok o →
      ScanSim absExprRec o
        (scanAppExprLoop (absBytes b) (absPos i) w (absU32 seen)
          (absU64 arg) (absU64 fnx)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen arg fnx o hf h
    rw [frontend.scan_fast.scan_app_expr_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    have hstep := nextMember_step kf
      (L := fun p w' =>
        scanAppExprLoop (absBytes b) p w' (absU32 seen) (absU64 arg) (absU64 fnx))
      (CL := fun p w' =>
        if w' && absU32 seen != 0 then .err ⟨p.toNat, .expectedKey⟩
        else if absU32 seen &&& 3 != 3 then .err ⟨p.toNat, .missingKey⟩
        else .ok (.app (absU64 fnx) (absU64 arg)) (p + 1))
      (DI := fun k p v =>
        match k with
        | .kArg =>
          if absU32 seen &&& 1 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            scanAppExprLoop (absBytes b) e false (absU32 seen ||| 1) x (absU64 fnx))
        | .kFn =>
          if absU32 seen &&& 2 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            scanAppExprLoop (absBytes b) e false (absU32 seen ||| 2) (absU64 arg) x)
        | _ => .err ⟨p.toNat, .unknownKey⟩)
      (by intro p w'; rw [scanAppExprLoop.eq_def]; rfl)
      (b.length - i.val) i w res (le_refl _) hres
    cases res with
    | Err er =>
      rw [← Result.ok_injective h]
      exact hstep.err
    | Ok p =>
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      cases mem with
      | Close =>
        rw [hstep.close, zero_abs, mask_abs3]
        have hclose : ∀ (o' : core.result.Result
              (frontend.scan_types.ExprRec × Std.Usize) frontend.scan_types.ScanErr),
            (do let i1 ← lift (seen &&& 3#u32)
                if i1 != 3#u32 then
                  frontend.scan_fast.err frontend.scan_types.ExprRec ni
                    frontend.scan_types.ErrTag.MissingKey
                else do let i2 ← ni + 1#usize
                        ok (core.result.Result.Ok
                          (frontend.scan_types.ExprRec.App fnx arg, i2))) = ok o' →
            ScanSim absExprRec o'
              (if seen &&& 3#u32 != 3#u32 then
                 ScanRes.err ⟨(absPos ni).toNat, .missingKey⟩
               else ScanRes.ok (.app (absU64 fnx) (absU64 arg)) (absPos ni + 1)) := by
          intro o' h'
          obtain ⟨i1, hi1, h'⟩ := bind_eq_ok_iff.mp h'
          rw [lift_val hi1] at h'
          by_cases hm : (seen &&& 3#u32 != 3#u32) = true
          · rw [if_pos hm] at h'
            rw [if_pos hm, err_val h']
            exact ScanErrSim.mk (t := .missingKey) rfl (by simp)
          · rw [if_neg hm] at h'
            rw [if_neg hm]
            obtain ⟨i2, hi2, h'⟩ := bind_eq_ok_iff.mp h'
            rw [← Result.ok_injective h', ← absPos_add_one hi2]
            rfl
        by_cases hnw : nw = true
        · rw [if_pos hnw] at h
          by_cases hz : (seen != 0#u32) = true
          · rw [if_pos hz] at h
            rw [if_pos (by simp [hnw, hz]), err_val h]
            exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
          · rw [if_neg hz] at h
            rw [if_neg (by simp [hz])]
            exact hclose o h
        · rw [if_neg hnw] at h
          rw [if_neg (by simp [hnw])]
          exact hclose o h
      | Key k ks v =>
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        have hilt := next_member_lt hres
        cases k <;>
          (rw [hstep.key]
           simp only [absKey]
           first
             | (rw [err_val h]; exact ScanErrSim.mk (t := .unknownKey) rfl (by simp))
             | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
                have hb1' := dup_val hb1
                simp only [dup_abs1, dup_abs2]
                by_cases hd : b1 = true
                · rw [if_pos hd] at h
                  rw [if_pos (by rw [← hb1']; exact hd), err_val h]
                  exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
                · rw [if_neg hd] at h
                  rw [if_neg (by rw [← hb1']; simpa using hd)]
                  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                  cases r1 with
                  | Err er =>
                    rw [← Result.ok_injective h]
                    exact NatSlotStep.err (natSlot_step hr1)
                  | Ok pr =>
                    obtain ⟨x, e⟩ := pr
                    simp only [uncurry_apply_pair] at h
                    have hprog := slot_nat_prog hr1
                    rw [NatSlotStep.ok (natSlot_step hr1)]
                    obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                    simp only [or_abs1, or_abs2]
                    rw [← lift_val hseen1]
                    exact ih (b.length - e.val) (by omega) false e seen1 _ _ o (le_refl _) h))

/-- **`scan_fast::scan_app_expr`** (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:955-959 scanAppExpr`). -/
theorem scan_app_expr_refines_of (kf : KitFacts b) {i : Std.Usize} {o}
    (h : frontend.scan_fast.scan_app_expr b i = ok o) :
    ScanSim absExprRec o (scanAppExpr (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_app_expr] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanAppExpr, brace_abs hc]
  by_cases hc1 : c = 123#u8
  · rw [if_pos hc1] at h
    rw [if_pos (beq_iff_eq.mpr hc1)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2, frontend.scan_fast.scan_app_expr_loop] at *
    exact scan_app_expr_loop_aux kf (b.length - i2.val) true i2 0#u32 0#u64 0#u64 o
      (le_refl _) h
  · rw [if_neg hc1] at h
    rw [if_neg (by simp [hc1]), err_val h]
    exact ScanErrSim.mk (t := .expectedObject) rfl (by simp)

/-! ## `scan_proj_expr`

`scan_fast.rs:1993-2072` against `Scan/Fast.lean:1262-1324`.  Three `Nat`
slots and `ExprRec::Proj`; the field order differs between the record and the
JSON object, which is exactly what the slot loop makes irrelevant. -/

private theorem scan_proj_expr_loop_aux (kf : KitFacts b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (ix st tn : Std.U64) o,
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_proj_expr_loop_loop w b i seen ix st tn = ok o →
      ScanSim absExprRec o
        (scanProjExprLoop (absBytes b) (absPos i) w (absU32 seen)
          (absU64 ix) (absU64 st) (absU64 tn)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen ix st tn o hf h
    rw [frontend.scan_fast.scan_proj_expr_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    have hstep := nextMember_step kf
      (L := fun p w' =>
        scanProjExprLoop (absBytes b) p w' (absU32 seen)
          (absU64 ix) (absU64 st) (absU64 tn))
      (CL := fun p w' =>
        if w' && absU32 seen != 0 then .err ⟨p.toNat, .expectedKey⟩
        else if absU32 seen &&& 7 != 7 then .err ⟨p.toNat, .missingKey⟩
        else .ok (.proj (absU64 tn) (absU64 ix) (absU64 st)) (p + 1))
      (DI := fun k p v =>
        match k with
        | .kIdx =>
          if absU32 seen &&& 1 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            scanProjExprLoop (absBytes b) e false (absU32 seen ||| 1) x
              (absU64 st) (absU64 tn))
        | .kStruct =>
          if absU32 seen &&& 2 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            scanProjExprLoop (absBytes b) e false (absU32 seen ||| 2) (absU64 ix) x
              (absU64 tn))
        | .kTypeName =>
          if absU32 seen &&& 4 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            scanProjExprLoop (absBytes b) e false (absU32 seen ||| 4) (absU64 ix)
              (absU64 st) x)
        | _ => .err ⟨p.toNat, .unknownKey⟩)
      (by intro p w'; rw [scanProjExprLoop.eq_def]; rfl)
      (b.length - i.val) i w res (le_refl _) hres
    cases res with
    | Err er =>
      rw [← Result.ok_injective h]
      exact hstep.err
    | Ok p =>
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      cases mem with
      | Close =>
        rw [hstep.close, zero_abs, mask_abs7]
        have hclose : ∀ (o' : core.result.Result
              (frontend.scan_types.ExprRec × Std.Usize) frontend.scan_types.ScanErr),
            (do let i1 ← lift (seen &&& 7#u32)
                if i1 != 7#u32 then
                  frontend.scan_fast.err frontend.scan_types.ExprRec ni
                    frontend.scan_types.ErrTag.MissingKey
                else do let i2 ← ni + 1#usize
                        ok (core.result.Result.Ok
                          (frontend.scan_types.ExprRec.Proj tn ix st, i2))) = ok o' →
            ScanSim absExprRec o'
              (if seen &&& 7#u32 != 7#u32 then
                 ScanRes.err ⟨(absPos ni).toNat, .missingKey⟩
               else ScanRes.ok (.proj (absU64 tn) (absU64 ix) (absU64 st))
                 (absPos ni + 1)) := by
          intro o' h'
          obtain ⟨i1, hi1, h'⟩ := bind_eq_ok_iff.mp h'
          rw [lift_val hi1] at h'
          by_cases hm : (seen &&& 7#u32 != 7#u32) = true
          · rw [if_pos hm] at h'
            rw [if_pos hm, err_val h']
            exact ScanErrSim.mk (t := .missingKey) rfl (by simp)
          · rw [if_neg hm] at h'
            rw [if_neg hm]
            obtain ⟨i2, hi2, h'⟩ := bind_eq_ok_iff.mp h'
            rw [← Result.ok_injective h', ← absPos_add_one hi2]
            rfl
        by_cases hnw : nw = true
        · rw [if_pos hnw] at h
          by_cases hz : (seen != 0#u32) = true
          · rw [if_pos hz] at h
            rw [if_pos (by simp [hnw, hz]), err_val h]
            exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
          · rw [if_neg hz] at h
            rw [if_neg (by simp [hz])]
            exact hclose o h
        · rw [if_neg hnw] at h
          rw [if_neg (by simp [hnw])]
          exact hclose o h
      | Key k ks v =>
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        have hilt := next_member_lt hres
        cases k <;>
          (rw [hstep.key]
           simp only [absKey]
           first
             | (rw [err_val h]; exact ScanErrSim.mk (t := .unknownKey) rfl (by simp))
             | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
                have hb1' := dup_val hb1
                simp only [dup_abs1, dup_abs2, dup_abs4]
                by_cases hd : b1 = true
                · rw [if_pos hd] at h
                  rw [if_pos (by rw [← hb1']; exact hd), err_val h]
                  exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
                · rw [if_neg hd] at h
                  rw [if_neg (by rw [← hb1']; simpa using hd)]
                  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                  cases r1 with
                  | Err er =>
                    rw [← Result.ok_injective h]
                    exact NatSlotStep.err (natSlot_step hr1)
                  | Ok pr =>
                    obtain ⟨x, e⟩ := pr
                    simp only [uncurry_apply_pair] at h
                    have hprog := slot_nat_prog hr1
                    rw [NatSlotStep.ok (natSlot_step hr1)]
                    obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                    simp only [or_abs1, or_abs2, or_abs4]
                    rw [← lift_val hseen1]
                    exact ih (b.length - e.val) (by omega) false e seen1 _ _ _ o (le_refl _) h))

/-- **`scan_fast::scan_proj_expr`** (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1320-1324 scanProjExpr`). -/
theorem scan_proj_expr_refines_of (kf : KitFacts b) {i : Std.Usize} {o}
    (h : frontend.scan_fast.scan_proj_expr b i = ok o) :
    ScanSim absExprRec o (scanProjExpr (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_proj_expr] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanProjExpr, brace_abs hc]
  by_cases hc1 : c = 123#u8
  · rw [if_pos hc1] at h
    rw [if_pos (beq_iff_eq.mpr hc1)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    rw [frontend.scan_fast.scan_proj_expr_loop] at h
    exact scan_proj_expr_loop_aux kf (b.length - i2.val) true i2 0#u32 0#u64 0#u64
      0#u64 o (le_refl _) h
  · rw [if_neg hc1] at h
    rw [if_neg (by simp [hc1]), err_val h]
    exact ScanErrSim.mk (t := .expectedObject) rfl (by simp)

/-! ## `scan_const_expr`

`scan_fast.rs:1922-1990` against `Scan/Fast.lean:1206-1260`.  A `Nat` slot and
a list slot: `us` is a `Vec<u64>` in the port and a `List Nat` in con-leche,
and `absU64s` is what `ScanObj`'s `scan_nat_list_refines` delivers. -/

private theorem scan_const_expr_loop_aux (kf : KitFacts b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (nm : Std.U64)
      (us : alloc.vec.Vec Std.U64) o,
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_const_expr_loop_loop w b i seen nm us = ok o →
      ScanSim absExprRec o
        (scanConstExprLoop (absBytes b) (absPos i) w (absU32 seen)
          (absU64 nm) (absU64s us)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen nm us o hf h
    rw [frontend.scan_fast.scan_const_expr_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    have hstep := nextMember_step kf
      (L := fun p w' =>
        scanConstExprLoop (absBytes b) p w' (absU32 seen) (absU64 nm) (absU64s us))
      (CL := fun p w' =>
        if w' && absU32 seen != 0 then .err ⟨p.toNat, .expectedKey⟩
        else if absU32 seen &&& 3 != 3 then .err ⟨p.toNat, .missingKey⟩
        else .ok (.const (absU64 nm) (absU64s us)) (p + 1))
      (DI := fun k p v =>
        match k with
        | .kName =>
          if absU32 seen &&& 1 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            scanConstExprLoop (absBytes b) e false (absU32 seen ||| 1) x (absU64s us))
        | .kUs =>
          if absU32 seen &&& 2 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else
            match scanNatList (absBytes b) v with
            | .err err => .err err
            | .ok x e =>
              if _hj : p < e then
                scanConstExprLoop (absBytes b) e false (absU32 seen ||| 2) (absU64 nm) x
              else .err ⟨p.toNat, .noProgress⟩
        | _ => .err ⟨p.toNat, .unknownKey⟩)
      (by intro p w'; rw [scanConstExprLoop.eq_def]; rfl)
      (b.length - i.val) i w res (le_refl _) hres
    cases res with
    | Err er =>
      rw [← Result.ok_injective h]
      exact hstep.err
    | Ok p =>
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      cases mem with
      | Close =>
        rw [hstep.close, zero_abs, mask_abs3]
        have hclose : ∀ (o' : core.result.Result
              (frontend.scan_types.ExprRec × Std.Usize) frontend.scan_types.ScanErr),
            (do let i1 ← lift (seen &&& 3#u32)
                if i1 != 3#u32 then
                  frontend.scan_fast.err frontend.scan_types.ExprRec ni
                    frontend.scan_types.ErrTag.MissingKey
                else do let i2 ← ni + 1#usize
                        ok (core.result.Result.Ok
                          (frontend.scan_types.ExprRec.Const nm us, i2))) = ok o' →
            ScanSim absExprRec o'
              (if seen &&& 3#u32 != 3#u32 then
                 ScanRes.err ⟨(absPos ni).toNat, .missingKey⟩
               else ScanRes.ok (.const (absU64 nm) (absU64s us)) (absPos ni + 1)) := by
          intro o' h'
          obtain ⟨i1, hi1, h'⟩ := bind_eq_ok_iff.mp h'
          rw [lift_val hi1] at h'
          by_cases hm : (seen &&& 3#u32 != 3#u32) = true
          · rw [if_pos hm] at h'
            rw [if_pos hm, err_val h']
            exact ScanErrSim.mk (t := .missingKey) rfl (by simp)
          · rw [if_neg hm] at h'
            rw [if_neg hm]
            obtain ⟨i2, hi2, h'⟩ := bind_eq_ok_iff.mp h'
            rw [← Result.ok_injective h', ← absPos_add_one hi2]
            rfl
        by_cases hnw : nw = true
        · rw [if_pos hnw] at h
          by_cases hz : (seen != 0#u32) = true
          · rw [if_pos hz] at h
            rw [if_pos (by simp [hnw, hz]), err_val h]
            exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
          · rw [if_neg hz] at h
            rw [if_neg (by simp [hz])]
            exact hclose o h
        · rw [if_neg hnw] at h
          rw [if_neg (by simp [hnw])]
          exact hclose o h
      | Key k ks v =>
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        have hilt := next_member_lt hres
        cases k <;>
          (rw [hstep.key]
           simp only [absKey]
           first
             | (rw [err_val h]; exact ScanErrSim.mk (t := .unknownKey) rfl (by simp))
             | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
                have hb1' := dup_val hb1
                simp only [dup_abs1]
                by_cases hd : b1 = true
                · rw [if_pos hd] at h
                  rw [if_pos (by rw [← hb1']; exact hd), err_val h]
                  exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
                · rw [if_neg hd] at h
                  rw [if_neg (by rw [← hb1']; simpa using hd)]
                  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                  cases r1 with
                  | Err er =>
                    rw [← Result.ok_injective h]
                    exact NatSlotStep.err (natSlot_step hr1)
                  | Ok pr =>
                    obtain ⟨x, e⟩ := pr
                    simp only [uncurry_apply_pair] at h
                    have hprog := slot_nat_prog hr1
                    rw [NatSlotStep.ok (natSlot_step hr1)]
                    obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                    simp only [or_abs1]
                    rw [← lift_val hseen1]
                    exact ih (b.length - e.val) (by omega) false e seen1 _ _ o
                      (le_refl _) h)
             | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
                have hb1' := dup_val hb1
                simp only [dup_abs2]
                by_cases hd : b1 = true
                · rw [if_pos hd] at h
                  rw [if_pos (by rw [← hb1']; exact hd), err_val h]
                  exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
                · rw [if_neg hd] at h
                  rw [if_neg (by rw [← hb1']; simpa using hd)]
                  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                  cases r1 with
                  | Err er =>
                    rw [← Result.ok_injective h]
                    intro le hle
                    simp only [scan_nat_list_refines hr1 le hle]
                  | Ok pr =>
                    obtain ⟨x, e⟩ := pr
                    simp only [uncurry_apply_pair] at h
                    have hsub : scanNatList (absBytes b) (absPos v)
                        = ScanRes.ok (absU64s x) (absPos e) := scan_nat_list_refines hr1
                    simp only [hsub]
                    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                    have hb2' := prog_val hb2
                    by_cases hp : b2 = true
                    · rw [if_pos hp] at h
                      have hprog : ks.val < e.val := by rw [hb2'] at hp; simpa using hp
                      rw [dif_pos (absPos_lt.mpr hprog)]
                      obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                      simp only [or_abs2]
                      rw [← lift_val hseen1]
                      exact ih (b.length - e.val) (by omega) false e seen1 _ _ o
                        (le_refl _) h
                    · rw [if_neg hp] at h
                      have hprog : ¬ ks.val < e.val := by
                        rw [hb2'] at hp; simpa using hp
                      rw [dif_neg (by rw [absPos_lt]; exact hprog), err_val h]
                      exact ScanErrSim.mk (t := .noProgress) rfl (by simp)))

/-- **`scan_fast::scan_const_expr`** (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1256-1260 scanConstExpr`). -/
theorem scan_const_expr_refines_of (kf : KitFacts b) {i : Std.Usize} {o}
    (h : frontend.scan_fast.scan_const_expr b i = ok o) :
    ScanSim absExprRec o (scanConstExpr (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_const_expr] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanConstExpr, brace_abs hc]
  by_cases hc1 : c = 123#u8
  · rw [if_pos hc1] at h
    rw [if_pos (beq_iff_eq.mpr hc1)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    rw [frontend.scan_fast.scan_const_expr_loop] at h
    have hnil : absU64s (alloc.vec.Vec.new Std.U64) = [] := rfl
    rw [← hnil]
    exact scan_const_expr_loop_aux kf (b.length - i2.val) true i2 0#u32 0#u64 _ o
      (le_refl _) h
  · rw [if_neg hc1] at h
    rw [if_neg (by simp [hc1]), err_val h]
    exact ScanErrSim.mk (t := .expectedObject) rfl (by simp)

/-! ## `scan_let_expr`

`scan_fast.rs:1813-1919` against `Scan/Fast.lean:1125-1204`.  Five slots, of
which `name` is read and dropped and `nondep` is the format's own flag, read
through `scanBool` and dropped; the mask is therefore `27`, not `31`. -/

private theorem scan_let_expr_loop_aux (kf : KitFacts b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (bd ty vl : Std.U64) o,
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_let_expr_loop_loop w b i seen bd ty vl = ok o →
      ScanSim absExprRec o
        (scanLetExprLoop (absBytes b) (absPos i) w (absU32 seen)
          (absU64 bd) (absU64 ty) (absU64 vl)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen bd ty vl o hf h
    rw [frontend.scan_fast.scan_let_expr_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    have hstep := nextMember_step kf
      (L := fun p w' =>
        scanLetExprLoop (absBytes b) p w' (absU32 seen)
          (absU64 bd) (absU64 ty) (absU64 vl))
      (CL := fun p w' =>
        if w' && absU32 seen != 0 then .err ⟨p.toNat, .expectedKey⟩
        else if absU32 seen &&& 27 != 27 then .err ⟨p.toNat, .missingKey⟩
        else .ok (.letE (absU64 ty) (absU64 vl) (absU64 bd)) (p + 1))
      (DI := fun k p v =>
        match k with
        | .kBody =>
          if absU32 seen &&& 1 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            scanLetExprLoop (absBytes b) e false (absU32 seen ||| 1) x
              (absU64 ty) (absU64 vl))
        | .kName =>
          if absU32 seen &&& 2 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun _x e =>
            scanLetExprLoop (absBytes b) e false (absU32 seen ||| 2) (absU64 bd)
              (absU64 ty) (absU64 vl))
        | .kNondep =>
          if absU32 seen &&& 4 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else
            match scanBool (absBytes b) v with
            | .err err => .err err
            | .ok _x e =>
              if _hj : p < e then
                scanLetExprLoop (absBytes b) e false (absU32 seen ||| 4) (absU64 bd)
                  (absU64 ty) (absU64 vl)
              else .err ⟨p.toNat, .noProgress⟩
        | .kType =>
          if absU32 seen &&& 8 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            scanLetExprLoop (absBytes b) e false (absU32 seen ||| 8) (absU64 bd) x
              (absU64 vl))
        | .kValue =>
          if absU32 seen &&& 16 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            scanLetExprLoop (absBytes b) e false (absU32 seen ||| 16) (absU64 bd)
              (absU64 ty) x)
        | _ => .err ⟨p.toNat, .unknownKey⟩)
      (by intro p w'; rw [scanLetExprLoop.eq_def]; rfl)
      (b.length - i.val) i w res (le_refl _) hres
    cases res with
    | Err er =>
      rw [← Result.ok_injective h]
      exact hstep.err
    | Ok p =>
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      cases mem with
      | Close =>
        rw [hstep.close, zero_abs, mask_abs27]
        have hclose : ∀ (o' : core.result.Result
              (frontend.scan_types.ExprRec × Std.Usize) frontend.scan_types.ScanErr),
            (do let i1 ← lift (seen &&& 27#u32)
                if i1 != 27#u32 then
                  frontend.scan_fast.err frontend.scan_types.ExprRec ni
                    frontend.scan_types.ErrTag.MissingKey
                else do let i2 ← ni + 1#usize
                        ok (core.result.Result.Ok
                          (frontend.scan_types.ExprRec.LetE ty vl bd, i2))) = ok o' →
            ScanSim absExprRec o'
              (if seen &&& 27#u32 != 27#u32 then
                 ScanRes.err ⟨(absPos ni).toNat, .missingKey⟩
               else ScanRes.ok (.letE (absU64 ty) (absU64 vl) (absU64 bd))
                 (absPos ni + 1)) := by
          intro o' h'
          obtain ⟨i1, hi1, h'⟩ := bind_eq_ok_iff.mp h'
          rw [lift_val hi1] at h'
          by_cases hm : (seen &&& 27#u32 != 27#u32) = true
          · rw [if_pos hm] at h'
            rw [if_pos hm, err_val h']
            exact ScanErrSim.mk (t := .missingKey) rfl (by simp)
          · rw [if_neg hm] at h'
            rw [if_neg hm]
            obtain ⟨i2, hi2, h'⟩ := bind_eq_ok_iff.mp h'
            rw [← Result.ok_injective h', ← absPos_add_one hi2]
            rfl
        by_cases hnw : nw = true
        · rw [if_pos hnw] at h
          by_cases hz : (seen != 0#u32) = true
          · rw [if_pos hz] at h
            rw [if_pos (by simp [hnw, hz]), err_val h]
            exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
          · rw [if_neg hz] at h
            rw [if_neg (by simp [hz])]
            exact hclose o h
        · rw [if_neg hnw] at h
          rw [if_neg (by simp [hnw])]
          exact hclose o h
      | Key k ks v =>
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        have hilt := next_member_lt hres
        cases k <;>
          (rw [hstep.key]
           simp only [absKey]
           first
             | (rw [err_val h]; exact ScanErrSim.mk (t := .unknownKey) rfl (by simp))
             | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
                have hb1' := dup_val hb1
                simp only [dup_abs1, dup_abs2, dup_abs8, dup_abs16]
                by_cases hd : b1 = true
                · rw [if_pos hd] at h
                  rw [if_pos (by rw [← hb1']; exact hd), err_val h]
                  exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
                · rw [if_neg hd] at h
                  rw [if_neg (by rw [← hb1']; simpa using hd)]
                  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                  cases r1 with
                  | Err er =>
                    rw [← Result.ok_injective h]
                    exact NatSlotStep.err (natSlot_step hr1)
                  | Ok pr =>
                    obtain ⟨x, e⟩ := pr
                    simp only [uncurry_apply_pair] at h
                    have hprog := slot_nat_prog hr1
                    rw [NatSlotStep.ok (natSlot_step hr1)]
                    obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                    simp only [or_abs1, or_abs2, or_abs8, or_abs16]
                    rw [← lift_val hseen1]
                    exact ih (b.length - e.val) (by omega) false e seen1 _ _ _ o
                      (le_refl _) h)
             | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
                have hb1' := dup_val hb1
                simp only [dup_abs4]
                by_cases hd : b1 = true
                · rw [if_pos hd] at h
                  rw [if_pos (by rw [← hb1']; exact hd), err_val h]
                  exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
                · rw [if_neg hd] at h
                  rw [if_neg (by rw [← hb1']; simpa using hd)]
                  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                  cases r1 with
                  | Err er =>
                    rw [← Result.ok_injective h]
                    intro le hle
                    simp only [scan_bool_refines hr1 le hle]
                  | Ok pr =>
                    obtain ⟨x, e⟩ := pr
                    simp only [uncurry_apply_pair] at h
                    have hsub : scanBool (absBytes b) (absPos v)
                        = ScanRes.ok x (absPos e) := scan_bool_refines hr1
                    simp only [hsub]
                    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                    have hb2' := prog_val hb2
                    by_cases hp : b2 = true
                    · rw [if_pos hp] at h
                      have hprog : ks.val < e.val := by rw [hb2'] at hp; simpa using hp
                      rw [dif_pos (absPos_lt.mpr hprog)]
                      obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                      simp only [or_abs4]
                      rw [← lift_val hseen1]
                      exact ih (b.length - e.val) (by omega) false e seen1 _ _ _ o
                        (le_refl _) h
                    · rw [if_neg hp] at h
                      have hprog : ¬ ks.val < e.val := by
                        rw [hb2'] at hp; simpa using hp
                      rw [dif_neg (by rw [absPos_lt]; exact hprog), err_val h]
                      exact ScanErrSim.mk (t := .noProgress) rfl (by simp)))

/-- **`scan_fast::scan_let_expr`** (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1200-1204 scanLetExpr`). -/
theorem scan_let_expr_refines_of (kf : KitFacts b) {i : Std.Usize} {o}
    (h : frontend.scan_fast.scan_let_expr b i = ok o) :
    ScanSim absExprRec o (scanLetExpr (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_let_expr] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanLetExpr, brace_abs hc]
  by_cases hc1 : c = 123#u8
  · rw [if_pos hc1] at h
    rw [if_pos (beq_iff_eq.mpr hc1)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    rw [frontend.scan_fast.scan_let_expr_loop] at h
    exact scan_let_expr_loop_aux kf (b.length - i2.val) true i2 0#u32 0#u64 0#u64
      0#u64 o (le_refl _) h
  · rw [if_neg hc1] at h
    rw [if_neg (by simp [hc1]), err_val h]
    exact ScanErrSim.mk (t := .expectedObject) rfl (by simp)

/-! ## `scan_lam_expr` and `scan_forall_expr`

`scan_fast.rs:1681-1809` against **two** con-leche loops,
`Scan/Fast.lean:961-1034 scanLamExprLoop` and `1044-1117 scanForallExprLoop`.
The port has one loop with a `lam : bool` parameter because the two Lean
bodies are the same up to the `ExprRec` constructor the closing brace builds
(and `Scan/Naive.lean` already shares them, `binderFields`).  No intermediate
definition is needed: the loop lemma's con-leche side is
`if lam then scanLamExprLoop … else scanForallExprLoop …`, and
`scan_binder_expr_loop_lam` / `scan_binder_expr_loop_forall` below are the two
statements, one per value of `lam`. -/

/-- **The one `ScanStr` leaf the binder loop still waits on**:
`scan_fast::scan_binder_info` against `Scan/Fast.lean:657-666 scanBinderInfo`,
in `ScanKit`'s port-on-the-left orientation. -/
def BinderInfoRefines (b : Slice Std.U8) : Prop :=
  ∀ (i j : Std.Usize), frontend.scan_fast.scan_binder_info b i = ok j →
    absPos j = scanBinderInfo (absBytes b) (absPos i)

private theorem scan_binder_expr_loop_aux (kf : KitFacts b) (hbi : BinderInfoRefines b)
    (f : Nat) :
    ∀ (w lam : Bool) (i : Std.Usize) (seen : Std.U32) (bd ty : Std.U64)
      (pw : frontend.scan_types.PwRec) o,
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_binder_expr_loop_loop w b lam i seen bd ty pw = ok o →
      ScanSim absExprRec o
        (if lam then
          scanLamExprLoop (absBytes b) (absPos i) w (absU32 seen)
            (absU64 bd) (absU64 ty) (absPwRec pw)
         else
          scanForallExprLoop (absBytes b) (absPos i) w (absU32 seen)
            (absU64 bd) (absU64 ty) (absPwRec pw)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w lam i seen bd ty pw o hf h
    rw [frontend.scan_fast.scan_binder_expr_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    have hstep := nextMember_step kf
      (L := fun p w' =>
        if lam then
          scanLamExprLoop (absBytes b) p w' (absU32 seen)
            (absU64 bd) (absU64 ty) (absPwRec pw)
        else
          scanForallExprLoop (absBytes b) p w' (absU32 seen)
            (absU64 bd) (absU64 ty) (absPwRec pw))
      (CL := fun p w' =>
        if w' && absU32 seen != 0 then .err ⟨p.toNat, .expectedKey⟩
        else if absU32 seen &&& 15 != 15 then .err ⟨p.toNat, .missingKey⟩
        else .ok (if lam then .lam (absU64 ty) (absU64 bd) (absPwRec pw)
                  else .forallE (absU64 ty) (absU64 bd) (absPwRec pw)) (p + 1))
      (DI := fun k p v =>
        match k with
        | .kBinderInfo =>
          if absU32 seen &&& 1 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else
            if scanBinderInfo (absBytes b) v == 0 then
              .err ⟨v.toNat, .badBinderInfo⟩
            else if _hj : p < scanBinderInfo (absBytes b) v then
              (if lam then
                scanLamExprLoop (absBytes b) (scanBinderInfo (absBytes b) v) false
                  (absU32 seen ||| 1) (absU64 bd) (absU64 ty) (absPwRec pw)
               else
                scanForallExprLoop (absBytes b) (scanBinderInfo (absBytes b) v) false
                  (absU32 seen ||| 1) (absU64 bd) (absU64 ty) (absPwRec pw))
            else .err ⟨p.toNat, .noProgress⟩
        | .kBody =>
          if absU32 seen &&& 2 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            if lam then
              scanLamExprLoop (absBytes b) e false (absU32 seen ||| 2) x
                (absU64 ty) (absPwRec pw)
            else
              scanForallExprLoop (absBytes b) e false (absU32 seen ||| 2) x
                (absU64 ty) (absPwRec pw))
        | .kName =>
          if absU32 seen &&& 4 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun _x e =>
            if lam then
              scanLamExprLoop (absBytes b) e false (absU32 seen ||| 4) (absU64 bd)
                (absU64 ty) (absPwRec pw)
            else
              scanForallExprLoop (absBytes b) e false (absU32 seen ||| 4) (absU64 bd)
                (absU64 ty) (absPwRec pw))
        | .kType =>
          if absU32 seen &&& 8 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else natSlot (absBytes b) p v (fun x e =>
            if lam then
              scanLamExprLoop (absBytes b) e false (absU32 seen ||| 8) (absU64 bd) x
                (absPwRec pw)
            else
              scanForallExprLoop (absBytes b) e false (absU32 seen ||| 8) (absU64 bd) x
                (absPwRec pw))
        | .kPw =>
          if absU32 seen &&& 16 != 0 then .err ⟨p.toNat, .duplicateKey⟩
          else
            match scanPw (absBytes b) v with
            | .err err => .err err
            | .ok x e =>
              if _hj : p < e then
                (if lam then
                  scanLamExprLoop (absBytes b) e false (absU32 seen ||| 16) (absU64 bd)
                    (absU64 ty) x
                 else
                  scanForallExprLoop (absBytes b) e false (absU32 seen ||| 16)
                    (absU64 bd) (absU64 ty) x)
              else .err ⟨p.toNat, .noProgress⟩
        | _ => .err ⟨p.toNat, .unknownKey⟩)
      (by
        intro p w'
        cases lam <;>
          simp only [Bool.false_eq_true, if_false, if_true] <;>
          [rw [scanForallExprLoop.eq_def]; rw [scanLamExprLoop.eq_def]] <;> rfl)
      (b.length - i.val) i w res (le_refl _) hres
    cases res with
    | Err er =>
      rw [← Result.ok_injective h]
      exact hstep.err
    | Ok p =>
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      cases mem with
      | Close =>
        rw [hstep.close, zero_abs, mask_abs15]
        have hclose : ∀ (o' : core.result.Result
              (frontend.scan_types.ExprRec × Std.Usize) frontend.scan_types.ScanErr),
            (do let i1 ← lift (seen &&& 15#u32)
                if i1 != 15#u32 then
                  frontend.scan_fast.err frontend.scan_types.ExprRec ni
                    frontend.scan_types.ErrTag.MissingKey
                else do
                  let er ← if lam then ok (frontend.scan_types.ExprRec.Lam ty bd pw)
                           else ok (frontend.scan_types.ExprRec.ForallE ty bd pw)
                  let i2 ← ni + 1#usize
                  ok (core.result.Result.Ok (er, i2))) = ok o' →
            ScanSim absExprRec o'
              (if seen &&& 15#u32 != 15#u32 then
                 ScanRes.err ⟨(absPos ni).toNat, .missingKey⟩
               else ScanRes.ok
                 (if lam then ExprRec.lam (absU64 ty) (absU64 bd) (absPwRec pw)
                  else ExprRec.forallE (absU64 ty) (absU64 bd) (absPwRec pw))
                 (absPos ni + 1)) := by
          intro o' h'
          obtain ⟨i1, hi1, h'⟩ := bind_eq_ok_iff.mp h'
          rw [lift_val hi1] at h'
          by_cases hm : (seen &&& 15#u32 != 15#u32) = true
          · rw [if_pos hm] at h'
            rw [if_pos hm, err_val h']
            exact ScanErrSim.mk (t := .missingKey) rfl (by simp)
          · rw [if_neg hm] at h'
            rw [if_neg hm]
            obtain ⟨er, her, h'⟩ := bind_eq_ok_iff.mp h'
            obtain ⟨i2, hi2, h'⟩ := bind_eq_ok_iff.mp h'
            rw [← Result.ok_injective h', ← absPos_add_one hi2]
            cases lam <;> simp only [Bool.false_eq_true, if_false, if_true] at her ⊢ <;>
              rw [← Result.ok_injective her] <;> rfl
        by_cases hnw : nw = true
        · rw [if_pos hnw] at h
          by_cases hz : (seen != 0#u32) = true
          · rw [if_pos hz] at h
            rw [if_pos (by simp [hnw, hz]), err_val h]
            exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
          · rw [if_neg hz] at h
            rw [if_neg (by simp [hz])]
            exact hclose o h
        · rw [if_neg hnw] at h
          rw [if_neg (by simp [hnw])]
          exact hclose o h
      | Key k ks v =>
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        have hilt := next_member_lt hres
        cases k <;>
          (rw [hstep.key]
           simp only [absKey]
           first
             | (rw [err_val h]; exact ScanErrSim.mk (t := .unknownKey) rfl (by simp))
             | -- `pw`: a sub-scanner
               (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
                have hb1' := dup_val hb1
                simp only [dup_abs16]
                by_cases hd : b1 = true
                · rw [if_pos hd] at h
                  rw [if_pos (by rw [← hb1']; exact hd), err_val h]
                  exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
                · rw [if_neg hd] at h
                  rw [if_neg (by rw [← hb1']; simpa using hd)]
                  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                  cases r1 with
                  | Err er =>
                    rw [← Result.ok_injective h]
                    intro le hle
                    simp only [scan_pw_refines hr1 le hle]
                  | Ok pr =>
                    obtain ⟨x, e⟩ := pr
                    simp only [uncurry_apply_pair] at h
                    have hsub : scanPw (absBytes b) (absPos v)
                        = ScanRes.ok (absPwRec x) (absPos e) := scan_pw_refines hr1
                    simp only [hsub]
                    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                    have hb2' := prog_val hb2
                    by_cases hp : b2 = true
                    · rw [if_pos hp] at h
                      have hprog : ks.val < e.val := by rw [hb2'] at hp; simpa using hp
                      rw [dif_pos (absPos_lt.mpr hprog)]
                      obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                      simp only [or_abs16]
                      rw [← lift_val hseen1]
                      exact ih (b.length - e.val) (by omega) false lam e seen1 _ _ _ o
                        (le_refl _) h
                    · rw [if_neg hp] at h
                      have hprog : ¬ ks.val < e.val := by
                        rw [hb2'] at hp; simpa using hp
                      rw [dif_neg (by rw [absPos_lt]; exact hprog), err_val h]
                      exact ScanErrSim.mk (t := .noProgress) rfl (by simp))
             | -- the three `Nat` slots
               (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
                have hb1' := dup_val hb1
                simp only [dup_abs1, dup_abs2, dup_abs4, dup_abs8]
                by_cases hd : b1 = true
                · rw [if_pos hd] at h
                  rw [if_pos (by rw [← hb1']; exact hd), err_val h]
                  exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
                · rw [if_neg hd] at h
                  rw [if_neg (by rw [← hb1']; simpa using hd)]
                  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                  cases r1 with
                  | Err er =>
                    rw [← Result.ok_injective h]
                    exact NatSlotStep.err (natSlot_step hr1)
                  | Ok pr =>
                    obtain ⟨x, e⟩ := pr
                    simp only [uncurry_apply_pair] at h
                    have hprog := slot_nat_prog hr1
                    rw [NatSlotStep.ok (natSlot_step hr1)]
                    obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                    simp only [or_abs2, or_abs4, or_abs8]
                    rw [← lift_val hseen1]
                    exact ih (b.length - e.val) (by omega) false lam e seen1 _ _ _ o
                      (le_refl _) h)
             | -- `binderInfo`: a bare `usize`, `0` for "not one of the four"
               (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
                have hb1' := dup_val hb1
                simp only [dup_abs1]
                by_cases hd : b1 = true
                · rw [if_pos hd] at h
                  rw [if_pos (by rw [← hb1']; exact hd), err_val h]
                  exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
                · rw [if_neg hd] at h
                  rw [if_neg (by rw [← hb1']; simpa using hd)]
                  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
                  rw [← hbi v e he]
                  by_cases he0 : e = 0#usize
                  · rw [if_pos he0] at h
                    rw [if_pos (show (absPos e == (0 : USize)) = true by simp [he0]),
                      err_val h]
                    exact ScanErrSim.mk (t := .badBinderInfo) rfl (by simp)
                  · rw [if_neg he0] at h
                    rw [if_neg (show ¬ (absPos e == (0 : USize)) = true by
                      simp only [absPos_beq, decide_eq_true_eq,
                        show ((0 : USize)).toNat = 0 from rfl]
                      intro hc; exact he0 (by scalar_tac))]
                    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                    have hb2' := prog_val hb2
                    by_cases hp : b2 = true
                    · rw [if_pos hp] at h
                      have hprog : ks.val < e.val := by rw [hb2'] at hp; simpa using hp
                      rw [dif_pos (absPos_lt.mpr hprog)]
                      obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                      simp only [or_abs1]
                      rw [← lift_val hseen1]
                      exact ih (b.length - e.val) (by omega) false lam e seen1 _ _ _ o
                        (le_refl _) h
                    · rw [if_neg hp] at h
                      have hprog : ¬ ks.val < e.val := by
                        rw [hb2'] at hp; simpa using hp
                      rw [dif_neg (by rw [absPos_lt]; exact hprog), err_val h]
                      exact ScanErrSim.mk (t := .noProgress) rfl (by simp)))


/-- The binder loop at `lam = true`: `Scan/Fast.lean:961-1034 scanLamExprLoop`. -/
private theorem scan_binder_expr_loop_lam (kf : KitFacts b) (hbi : BinderInfoRefines b)
    {w : Bool} {i : Std.Usize} {seen : Std.U32} {bd ty : Std.U64}
    {pw : frontend.scan_types.PwRec} {o}
    (h : frontend.scan_fast.scan_binder_expr_loop_loop w b true i seen bd ty pw
      = ok o) :
    ScanSim absExprRec o
      (scanLamExprLoop (absBytes b) (absPos i) w (absU32 seen)
        (absU64 bd) (absU64 ty) (absPwRec pw)) :=
  scan_binder_expr_loop_aux kf hbi (b.length - i.val) w true i seen bd ty pw o
    (le_refl _) h

/-- The binder loop at `lam = false`:
`Scan/Fast.lean:1044-1117 scanForallExprLoop`. -/
private theorem scan_binder_expr_loop_forall (kf : KitFacts b)
    (hbi : BinderInfoRefines b)
    {w : Bool} {i : Std.Usize} {seen : Std.U32} {bd ty : Std.U64}
    {pw : frontend.scan_types.PwRec} {o}
    (h : frontend.scan_fast.scan_binder_expr_loop_loop w b false i seen bd ty pw
      = ok o) :
    ScanSim absExprRec o
      (scanForallExprLoop (absBytes b) (absPos i) w (absU32 seen)
        (absU64 bd) (absU64 ty) (absPwRec pw)) :=
  scan_binder_expr_loop_aux kf hbi (b.length - i.val) w false i seen bd ty pw o
    (le_refl _) h

/-- **`scan_fast::scan_lam_expr`** (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1036-1042 scanLamExpr`). -/
theorem scan_lam_expr_refines_of (kf : KitFacts b) (hbi : BinderInfoRefines b)
    {i : Std.Usize} {o} (h : frontend.scan_fast.scan_lam_expr b i = ok o) :
    ScanSim absExprRec o (scanLamExpr (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_lam_expr] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanLamExpr, brace_abs hc]
  by_cases hc1 : c = 123#u8
  · rw [if_pos hc1] at h
    rw [if_pos (beq_iff_eq.mpr hc1)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    rw [frontend.scan_fast.scan_binder_expr_loop] at h
    exact scan_binder_expr_loop_lam kf hbi h
  · rw [if_neg hc1] at h
    rw [if_neg (by simp [hc1]), err_val h]
    exact ScanErrSim.mk (t := .expectedObject) rfl (by simp)

/-- **`scan_fast::scan_forall_expr`** (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1119-1123 scanForallExpr`). -/
theorem scan_forall_expr_refines_of (kf : KitFacts b) (hbi : BinderInfoRefines b)
    {i : Std.Usize} {o} (h : frontend.scan_fast.scan_forall_expr b i = ok o) :
    ScanSim absExprRec o (scanForallExpr (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_forall_expr] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanForallExpr, brace_abs hc]
  by_cases hc1 : c = 123#u8
  · rw [if_pos hc1] at h
    rw [if_pos (beq_iff_eq.mpr hc1)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    rw [frontend.scan_fast.scan_binder_expr_loop] at h
    exact scan_binder_expr_loop_forall kf hbi h
  · rw [if_neg hc1] at h
    rw [if_neg (by simp [hc1]), err_val h]
    exact ScanErrSim.mk (t := .expectedObject) rfl (by simp)

end Step

end ConRon.Refine.Frontend
