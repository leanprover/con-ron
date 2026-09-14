/-
**The inductive block's record scanners, exact against con-leche** (task #87,
phase 3).

`crates/con-ron-core/src/frontend/scan_fast.rs:2075-3014` against
`ConLeche/Frontend/Scan/Fast.lean:1326-1921` -- the four slot loops and four
list loops that read an inductive block's `types`, `ctors` and `recs`, and the
recursor rules inside a `recs` member.

## What this file gives the line scanner

Agent L's `scan_ind_decl_loop` reads exactly three of these, one per key of an
`"inductive"` line, and they are the file's product:

    theorem scan_ind_types_refines {b : Slice Std.U8} (kit : KitFacts b)
        {i : Std.Usize} {o} (h : frontend.scan_fast.scan_ind_types b i = ok o) :
        ScanSim absIndTypeRecs o (scanIndTypes (absBytes b) (absPos i))

    theorem scan_ind_ctors_refines {b : Slice Std.U8} (kit : KitFacts b)
        {i : Std.Usize} {o} (h : frontend.scan_fast.scan_ind_ctors b i = ok o) :
        ScanSim absIndCtorRecs o (scanIndCtors (absBytes b) (absPos i))

    theorem scan_ind_recs_refines {b : Slice Std.U8} (kit : KitFacts b)
        {i : Std.Usize} {o} (h : frontend.scan_fast.scan_ind_recs b i = ok o) :
        ScanSim absIndRecRecs o (scanIndRecs (absBytes b) (absPos i))

`scan_rules_refines` (the `"rules"` slot of a `recs` member) has the same shape
with `absRuleRecs` / `scanRules`, and is used only inside this file.
`ScanObj.KitFacts` -- `keyEnd`, `valueAt`, `keyAt` -- is the only hypothesis
left; it is `ScanKit`'s to discharge and then every statement here is
hypothesis-free.

## The two shapes

* **A list loop** (`scanRuleListLoop`, `scanIndRecListLoop`,
  `scanIndTypeListLoop`, `scanIndCtorListLoop`) accumulates into a `Vec` in the
  port and conses onto a `List` in con-leche, reversing at the close.  The
  invariant is therefore `(absRuleRecs acc).reverse` -- *the port's
  accumulator, abstracted and reversed, is con-leche's* -- and the close is
  `List.reverse_reverse`.  The unfolding lemma (`scanRuleListLoop_eq` and its
  three copies) keeps con-leche's `dite` for the `_hj : i < e` progress guard,
  or it is not the `rfl` it has to be.
* **A slot loop** (`scanRuleLoop`, `scanIndRecLoop`, `scanIndTypeLoop`,
  `scanIndCtorLoop`) is a `while` over JSON members.  con-leche writes the
  member step out inline in every loop; the port factors it as
  `scan_fast::next_member` (`scan_types.rs`'s module note, deviation 3).  The
  bridge is `ScanObj`'s `memberBody` / `nextMember_step`: each loop is
  `memberBody` at its own closing arm and key dispatch (`scanRuleLoop_body` and
  its three copies, each a `rfl` after `scan*Loop.eq_def`), and then owes only
  those two arms.  A `Nat`-valued slot goes through `ScanObj`'s `natSlot` /
  `natSlot_step`; a slot a sub-scanner fills is written out **inline** in the
  key dispatch -- factoring it into a helper `def` introduces a second matcher,
  and two matchers on a stuck scrutinee are not definitionally equal, so the
  `rfl` fails (measured: agent E lost twenty minutes to the same trap).

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.ScanObj

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

open ConLeche.Frontend

/-! ## The local kit

`ScanInd` holds what this file needs and `ScanKit`/`ScanObj` do not state: the
byte reads the *list* loops make (they index the slice directly rather than
through `byte_at`), the `Vec` accumulator lemmas, and the two readings of
`ScanSim` that let a sub-scanner's result rewrite a stuck `match`. -/

namespace ScanInd

/-- A slice read at an in-range index, in the forward `= ok` form. -/
theorem slice_index_ok {t : Slice Std.U8} {i : Std.Usize}
    (hi : i.val < t.val.length) : Slice.index_usize t i = ok t.val[i.val] := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Slice.index_usize_spec t i hi)
  rw [hy, hyv]

/-- The port's byte read as a total function of a `Nat` index. -/
def pByte (b : Slice Std.U8) (n : Nat) : Std.U8 :=
  if h : n < b.val.length then b.val[n] else 0#u8

/-- A byte read inside the slice, through `absPos`: what con-leche's loops see
where the port sees `pByte`. -/
theorem uget_absPos {b : Slice Std.U8} {i : Std.Usize}
    (h : (absPos i).toNat < (absBytes b).size) :
    (absBytes b).uget (absPos i) h = absByte (pByte b i.val) := by
  have hi : i.val < b.val.length := by
    rw [absBytes_size, absPos_toNat] at h; exact h
  rw [absBytes_uget b (absPos i) h (by rw [absPos_toNat]; exact hi), pByte, dif_pos hi]
  simp only [absPos_toNat]

/-- The byte the port's loop read, as `pByte`. -/
theorem index_pByte {b : Slice Std.U8} {i : Std.Usize} {c : Std.U8}
    (hi : i.val < b.val.length) (h : Slice.index_usize b i = ok c) :
    c = pByte b i.val := by
  rw [slice_index_ok hi] at h
  rw [pByte, dif_pos hi]
  simpa using h.symm

/-- A byte literal crosses `absByte`: the port's `c = 93#u8` is con-leche's
`c == 93`. -/
theorem absByte_beq_lit {c d : Std.U8} {n : UInt8} (hd : d.val = n.toNat) :
    (absByte c == n) = decide (c = d) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, UScalar.eq_equiv]
  constructor
  · intro hc; rw [hd, ← absByte_toNat c, hc]
  · intro hc; apply UInt8.toNat_inj.mp; rw [absByte_toNat, hc, hd]

/-- `scan_fast::is_ws` is con-leche's `isWs` (`Scan/Fast.lean:78-80`). -/
theorem is_ws_abs {c : Std.U8} {r : Bool}
    (h : frontend.scan_fast.is_ws c = ok r) : r = isWs (absByte c) := by
  rw [frontend.scan_fast.is_ws] at h
  rw [isWs, absByte_beq_lit (d := 32#u8) (by decide), absByte_beq_lit (d := 9#u8) (by decide),
    absByte_beq_lit (d := 13#u8) (by decide)]
  split at h
  · rename_i hc; simp only [Result.ok.injEq] at h; rw [← h, hc]; simp
  · rename_i hc1
    split at h
    · rename_i hc2; simp only [Result.ok.injEq] at h; rw [← h, hc2]; simp
    · rename_i hc2; simp only [Result.ok.injEq] at h; rw [← h]; simp [hc1, hc2]

/-- `scan_fast::prog` read forwards. -/
theorem prog_val {ks e : Std.Usize} {c : Bool}
    (h : frontend.scan_fast.prog ks e = ok c) : c = decide (ks.val < e.val) := by
  rw [frontend.scan_fast.prog, Result.ok.injEq] at h
  rw [← h]
  simp only [decide_eq_decide]
  scalar_tac

/-- `scan_fast::err` never yields an `Ok`. -/
theorem err_eq {T : Type} (offset : Std.Usize) (what : frontend.scan_types.ErrTag) :
    frontend.scan_fast.err T offset what = ok (.Err ⟨offset, what⟩) := rfl

/-- A `Vec::push`, read forwards. -/
theorem vec_push_val {α : Type} {v v1 : alloc.vec.Vec α} {x : α}
    (h : alloc.vec.Vec.push v x = ok v1) : v1.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · simp only [Result.ok.injEq] at h
    rw [← h]
    simp
  · simp at h

/-- The port's `Vec::len != 0` test, read as a fact about the list. -/
theorem vec_len_ne {α : Type} {v : alloc.vec.Vec α}
    (h : (alloc.vec.Vec.len v != 0#usize) = true) : v.val ≠ [] := by
  simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv] at h
  rw [alloc.vec.Vec.len_val] at h
  intro hc
  exact h (by rw [alloc.vec.Vec.length, hc]; rfl)

theorem vec_len_eq {α : Type} {v : alloc.vec.Vec α}
    (h : ¬ (alloc.vec.Vec.len v != 0#usize) = true) : v.val = [] := by
  simp only [bne_iff_ne, ne_eq, Decidable.not_not, UScalar.eq_equiv] at h
  rw [alloc.vec.Vec.len_val] at h
  have : v.val.length = 0 := by simpa using h
  exact List.eq_nil_of_length_eq_zero this

/-- A mapped, reversed accumulator is empty exactly when the port's `Vec` is. -/
theorem map_reverse_isEmpty {α β : Type} (l : List α) (g : α → β) :
    ((l.map g).reverse).isEmpty = decide (l = []) := by
  cases l <;> simp

/-- `scan_fast::byte_at` is con-leche's `byteAt` (`Scan/Fast.lean:74-76`). -/
theorem byte_at_abs {b : Slice Std.U8} {i : Std.Usize} {c : Std.U8}
    (h : frontend.scan_fast.byte_at b i = ok c) :
    byteAt (absBytes b) (absPos i) = absByte c := by
  rw [frontend.scan_fast.byte_at] at h
  rw [byteAt]
  by_cases hi : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr hi), uget_absPos, pByte, dif_pos hi]
    rw [if_pos (show i < Slice.len b by scalar_tac), slice_index_ok hi] at h
    simp only [Result.ok.injEq] at h
    rw [h]
  · rw [dif_neg (fun hc => hi (absPos_lt_usize.mp hc))]
    rw [if_neg (show ¬ i < Slice.len b by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    rw [← h]
    rfl

/-- `lift` is `ok`, so a lifted pure step is an equation on its value. -/
theorem lift_val {α : Type} {x y : α} (h : lift x = ok y) : x = y := by
  rw [lift] at h; exact Result.ok_injective h

/-- A `u32` literal crosses `absU32`, in the direction a `!=` test needs.  The
con-leche numeral is left implicit and pinned by `by rfl` at the use site, so
that the rewrite matches the literal as it stands in the goal. -/
theorem u32_bne {x y : Std.U32} {n : UInt32} (hn : absU32 y = n) :
    (absU32 x != n) = (x != y) := by
  rw [← hn]; simp only [bne, absU32_beq]

/-- The port's `seen &&& lit`, read forwards. -/
theorem and_lit {x y z : Std.U32} {n : UInt32} (hn : absU32 y = n)
    (h : lift (x &&& y) = ok z) : absU32 z = absU32 x &&& n := by
  rw [← hn, ← absU32_and, lift_val h]

/-- The port's `seen ||| lit`, read forwards. -/
theorem or_lit {x y z : Std.U32} {n : UInt32} (hn : absU32 y = n)
    (h : lift (x ||| y) = ok z) : absU32 z = absU32 x ||| n := by
  rw [← hn, ← absU32_or, lift_val h]

/-- `scan_fast::dup` is con-leche's `(seen &&& bit) != 0` test. -/
theorem dup_bit {seen bit : Std.U32} {r : Bool} {n : UInt32} (hn : absU32 bit = n)
    (h : frontend.scan_fast.dup seen bit = ok r) :
    ((absU32 seen &&& n) != 0) = r := by
  rw [frontend.scan_fast.dup] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h, ← and_lit hn hi1]
  exact u32_bne (y := 0#u32) rfl

/-- A `ScanSim` on an `Ok`, read as the equation it is: what con-leche's
sub-scanner returned, so that the slot's `match` iota-reduces. -/
theorem scanSim_ok_eq {T α : Type} {A : T → α} {x : T} {e : Std.Usize}
    {r : ConLeche.Frontend.ScanRes α} (h : ScanSim A (.Ok (x, e)) r) :
    r = .ok (A x) (absPos e) := h

/-- A `ScanSim` on a mirrored `Err`, read the same way. -/
theorem scanSim_err_eq {T α : Type} {A : T → α} {er : frontend.scan_types.ScanErr}
    {r : ConLeche.Frontend.ScanRes α} {le : ConLeche.Frontend.ScanErr}
    (h : ScanSim A (.Err er) r) (hle : absScanErr er = some le) : r = .err le := h le hle

/-- A mirrored error, at the position the port reports it. -/
theorem scanSim_err {T α : Type} {A : T → α} {i : Std.Usize}
    {tag : frontend.scan_types.ErrTag} {t : ConLeche.Frontend.ErrTag}
    {x : ConLeche.Frontend.ScanRes α} (ht : absErrTag tag = some t)
    (hx : x = .err ⟨i.val, t⟩) :
    ScanSim A (.Err ⟨i, tag⟩) x :=
  ScanSim.err (ScanErrSim.mk ht hx)

end ScanInd

open ScanInd

/-! ## What the rest of the tier owes this file

`ScanObj.KitFacts` — `keyEnd`, `valueAt` and `keyAt` — is the only thing the
slot loops below still take as a hypothesis; the day `ScanKit` proves
`key_at_refines` it is discharged once and every theorem here is
hypothesis-free.  The two value scanners an inductive-block slot reads
(`scan_bool`, `scan_nat_list`) are already proved in `ScanObj`. -/

/-! ## The recursor rules

`scan_fast.rs:2075-2221` against `Scan/Fast.lean:1326-1422`. -/

/-- `scanRuleListLoop` (`Scan/Fast.lean:1390-1416`), unfolded once at a port
position. -/
private theorem scanRuleListLoop_eq (b : Slice Std.U8) (i : Std.Usize)
    (acc : List RuleRec) (wi : Bool) :
    scanRuleListLoop (absBytes b) (absPos i) acc wi =
      if i.val < b.val.length then
        (if isWs (absByte (pByte b i.val)) then
          scanRuleListLoop (absBytes b) (absPos i + 1) acc wi
         else if absByte (pByte b i.val) == 93 then
           (if wi && !acc.isEmpty then .err ⟨i.val, .expectedList⟩
            else .ok acc.reverse (absPos i + 1))
         else if absByte (pByte b i.val) == 44 then
           (if wi then .err ⟨i.val, .expectedList⟩
            else scanRuleListLoop (absBytes b) (absPos i + 1) acc true)
         else if absByte (pByte b i.val) == 123 then
           (if !wi then .err ⟨i.val, .expectedList⟩
            else match scanRule (absBytes b) (absPos i) with
              | .err e => .err e
              | .ok x e =>
                if absPos i < e then scanRuleListLoop (absBytes b) e (x :: acc) false
                else .err ⟨i.val, .noProgress⟩)
         else .err ⟨i.val, .expectedList⟩)
      else .err ⟨i.val, .expectedList⟩ := by
  rw [scanRuleListLoop]
  by_cases hi : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr hi), if_pos hi]
    simp only [uget_absPos, absPos_toNat]
    rfl
  · rw [dif_neg (fun hc => hi (absPos_lt_usize.mp hc)), if_neg hi, absPos_toNat]

/-- con-leche's `scanRuleLoop` (`Scan/Fast.lean:1326-1382`) is `ScanObj`'s
`memberBody` at its own closing arm and key dispatch. -/
private theorem scanRuleLoop_body (B : ByteArray) (S : UInt32) (ct nf rhs : Nat) :
    ∀ (p : USize) (w : Bool),
      scanRuleLoop B p w S ct nf rhs
        = memberBody B (fun q w' => scanRuleLoop B q w' S ct nf rhs)
            (fun q w' =>
              if w' && S != 0 then .err ⟨q.toNat, .expectedKey⟩
              else if (S &&& 7) != 7 then .err ⟨q.toNat, .missingKey⟩
              else .ok ⟨ct, nf, rhs⟩ (q + 1))
            (fun k q v =>
              match k with
              | .kCtor =>
                if (S &&& 1) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e => scanRuleLoop B e false (S ||| 1) n nf rhs)
              | .kNfields =>
                if (S &&& 2) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e => scanRuleLoop B e false (S ||| 2) ct n rhs)
              | .kRhs =>
                if (S &&& 4) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e => scanRuleLoop B e false (S ||| 4) ct nf n)
              | _ => .err ⟨q.toNat, .unknownKey⟩)
            p w := by
  intro p w
  rw [scanRuleLoop.eq_def]
  rfl

/-- `scan_fast::scan_rule_loop`'s loop refines `scanRuleLoop`
(`Scan/Fast.lean:1326-1382`).  Three `slot_nat` slots and fifty-odd keys that
are not this record's, every one of them `unknownKey`. -/
private theorem scan_rule_loop_loop_refines {b : Slice Std.U8} (kit : KitFacts b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (ct nf rhs : Std.U64)
      (o : core.result.Result (frontend.scan_types.RuleRec × Std.Usize)
        frontend.scan_types.ScanErr),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.scan_rule_loop_loop w b i seen ct nf rhs = ok o →
      ScanSim absRuleRec o
        (scanRuleLoop (absBytes b) (absPos i) w (absU32 seen)
          (absU64 ct) (absU64 nf) (absU64 rhs)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i seen ct nf rhs o hf h
  rw [frontend.scan_fast.scan_rule_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hstep := nextMember_step kit
    (scanRuleLoop_body (absBytes b) (absU32 seen) (absU64 ct) (absU64 nf) (absU64 rhs))
    (b.val.length - i.val) i w res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err hstep.err
  | Ok pm =>
    obtain ⟨mem, ni, nw⟩ := pm
    have hilt : i.val < b.val.length := next_member_lt hres
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [hstep.close]
      try dsimp only at h
      rw [u32_bne (x := seen) (y := 0#u32) (by rfl)]
      by_cases hnw : nw = true
      · rw [if_pos hnw] at h
        rw [hnw, Bool.true_and]
        by_cases hz : (seen != 0#u32) = true
        · rw [if_pos hz] at h
          rw [if_pos hz, err_eq] at *
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact scanSim_err rfl (by rw [absPos_toNat])
        · rw [if_neg hz] at h
          rw [if_neg hz]
          obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
          rw [← and_lit (x := seen) (by rfl) hi1, u32_bne (x := i1) (y := 7#u32) (by rfl)]
          by_cases hm : (i1 != 7#u32) = true
          · rw [if_pos hm, err_eq] at h
            rw [if_pos hm]
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact scanSim_err rfl (by rw [absPos_toNat])
          · rw [if_neg hm] at h
            rw [if_neg hm]
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.ok (by rw [absPos_add_one hi2]; rfl)
      · rw [if_neg hnw] at h
        simp only [Bool.not_eq_true] at hnw
        rw [hnw, Bool.false_and, if_neg (by simp)]
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        rw [← and_lit (x := seen) (by rfl) hi1, u32_bne (x := i1) (y := 7#u32) (by rfl)]
        by_cases hm : (i1 != 7#u32) = true
        · rw [if_pos hm, err_eq] at h
          rw [if_pos hm]
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact scanSim_err rfl (by rw [absPos_toNat])
        · rw [if_neg hm] at h
          rw [if_neg hm]
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact ScanSim.ok (by rw [absPos_add_one hi2]; rfl)
    | Key k ks v =>
      rw [hstep.key]
      have hks := next_member_ge (b.val.length - i.val) i w k ks v ni nw (le_refl _) hres
      cases k <;> dsimp only [absKey] at h ⊢ <;>
        first
          | (rw [err_eq] at h
             simp only [Result.ok.injEq] at h
             rw [← h]
             exact scanSim_err rfl (by rw [absPos_toNat]))
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 exact ScanSim.err (NatSlotStep.err (natSlot_step hr1))
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [NatSlotStep.ok (natSlot_step hr1)]
                 obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                 rw [← or_lit (x := seen) (by rfl) hseen1]
                 have hlt := slot_nat_prog hr1
                 exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ o
                   (le_refl _) h)

/-- `scan_fast::scan_rule` refines `scanRule` (`Scan/Fast.lean:1384-1388`). -/
theorem scan_rule_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.RuleRec × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_rule b i = ok o) :
    ScanSim absRuleRec o (scanRule (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_rule] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanRule, byte_at_abs hc, absByte_beq_lit (d := 123#u8) (by decide)]
  by_cases h123 : c = 123#u8
  · rw [if_pos h123] at h
    rw [if_pos (by simpa using h123)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2, frontend.scan_fast.scan_rule_loop] at *
    exact scan_rule_loop_loop_refines kit (b.val.length - i2.val) true i2 0#u32 0#u64 0#u64
      0#u64 o (le_refl _) h
  · rw [if_neg h123, err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [if_neg (by simpa using h123), ← h]
    exact scanSim_err rfl (by rw [absPos_toNat])

/-- `scan_fast::scan_rule_list_loop`'s loop refines `scanRuleListLoop`
(`Scan/Fast.lean:1390-1416`).  The port pushes onto a `Vec` where con-leche
conses onto a `List` and reverses at the close, so the invariant carries
`(absRuleRecs acc).reverse`. -/
private theorem scan_rule_list_loop_loop_refines {b : Slice Std.U8} (kit : KitFacts b)
    (f : Nat) :
    ∀ (i : Std.Usize) (acc : alloc.vec.Vec frontend.scan_types.RuleRec) (wi : Bool)
      (o : core.result.Result ((alloc.vec.Vec frontend.scan_types.RuleRec) × Std.Usize)
        frontend.scan_types.ScanErr),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.scan_rule_list_loop_loop b i acc wi = ok o →
      ScanSim absRuleRecs o
        (scanRuleListLoop (absBytes b) (absPos i) (absRuleRecs acc).reverse wi) := by
  induction f with
  | zero =>
    intro i acc wi o hf h
    rw [frontend.scan_fast.scan_rule_list_loop_loop.eq_def,
      if_pos (show i ≥ Slice.len b by scalar_tac), err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [scanRuleListLoop_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
    rw [← h]
    exact scanSim_err rfl rfl
  | succ f ih =>
    intro i acc wi o hf h
    rw [frontend.scan_fast.scan_rule_list_loop_loop.eq_def] at h
    rw [scanRuleListLoop_eq]
    by_cases hend : i ≥ Slice.len b
    · rw [if_pos hend, err_eq] at h
      simp only [Result.ok.injEq] at h
      rw [if_neg (show ¬ i.val < b.val.length by scalar_tac), ← h]
      exact scanSim_err rfl rfl
    · rw [if_neg hend] at h
      have hi : i.val < b.val.length := by scalar_tac
      rw [if_pos hi]
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
      rw [index_pByte hi hc] at hw h
      rw [← is_ws_abs hw]
      by_cases hws : w = true
      · rw [if_pos hws] at h
        rw [if_pos hws]
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hv := usize_add_one_inv hi2
        rw [← absPos_add_one hi2]
        exact ih i2 acc wi o (by omega) h
      · rw [if_neg hws] at h
        rw [if_neg hws]
        rw [absByte_beq_lit (d := 93#u8) (by decide), absByte_beq_lit (d := 44#u8) (by decide),
          absByte_beq_lit (d := 123#u8) (by decide)]
        by_cases h93 : pByte b i.val = 93#u8
        · rw [if_pos h93] at h
          rw [if_pos (by simpa using h93)]
          by_cases hwi : wi = true
          · rw [if_pos hwi] at h
            by_cases hne : (alloc.vec.Vec.len acc != 0#usize) = true
            · rw [if_pos hne, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_pos (show (wi && !(absRuleRecs acc).reverse.isEmpty) = true by
                rw [absRuleRecs, map_reverse_isEmpty, hwi]
                simp [vec_len_ne hne]), ← h]
              exact scanSim_err rfl rfl
            · rw [if_neg hne] at h
              obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
              simp only [Result.ok.injEq] at h
              rw [if_neg (show ¬ (wi && !(absRuleRecs acc).reverse.isEmpty) = true by
                rw [absRuleRecs, map_reverse_isEmpty]
                simp [vec_len_eq hne]), ← h]
              exact ScanSim.ok (by rw [List.reverse_reverse, absPos_add_one hi3])
          · rw [if_neg hwi] at h
            obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq] at h
            rw [if_neg (by simp [hwi]), ← h]
            exact ScanSim.ok (by rw [List.reverse_reverse, absPos_add_one hi3])
        · rw [if_neg h93] at h
          rw [if_neg (by simpa using h93)]
          by_cases h44 : pByte b i.val = 44#u8
          · rw [if_pos h44] at h
            rw [if_pos (by simpa using h44)]
            by_cases hwi : wi = true
            · rw [if_pos hwi, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_pos hwi, ← h]
              exact scanSim_err rfl rfl
            · rw [if_neg hwi] at h
              rw [if_neg hwi]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have hv := usize_add_one_inv hi2
              rw [← absPos_add_one hi2]
              exact ih i2 acc true o (by omega) h
          · rw [if_neg h44] at h
            rw [if_neg (by simpa using h44)]
            by_cases h123 : pByte b i.val = 123#u8
            · rw [if_pos h123] at h
              rw [if_pos (by simpa using h123)]
              by_cases hwi : wi = true
              · rw [if_pos hwi] at h
                rw [if_neg (by simp [hwi])]
                obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
                have hsim := scan_rule_refines kit hr
                cases r with
                | Err er =>
                  simp only [Result.ok.injEq] at h
                  rw [← h]
                  refine ScanSim.err ?_
                  intro le hle
                  rw [hsim le hle]
                | Ok p =>
                  obtain ⟨x, e⟩ := p
                  simp only [uncurry_apply_pair] at h
                  rw [(hsim : scanRule (absBytes b) (absPos i) = _)]
                  dsimp only
                  obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                  have hb2v := prog_val hb2
                  by_cases hp : b2 = true
                  · rw [if_pos hp] at h
                    have hlt : i.val < e.val := by
                      rw [hp] at hb2v; simpa using hb2v.symm
                    rw [if_pos (show absPos i < absPos e by
                      rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]; exact hlt)]
                    obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok_iff.mp h
                    have : (absRuleRecs acc1).reverse
                        = absRuleRec x :: (absRuleRecs acc).reverse := by
                      rw [absRuleRecs, vec_push_val hacc1]
                      simp [absRuleRecs]
                    rw [← this]
                    exact ih e acc1 false o (by omega) h
                  · rw [if_neg hp, err_eq] at h
                    simp only [Result.ok.injEq] at h
                    have hge : ¬ i.val < e.val := by
                      simp only [Bool.not_eq_true] at hp
                      rw [hp] at hb2v; simpa using hb2v.symm
                    rw [if_neg (show ¬ absPos i < absPos e by
                      rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]; exact hge), ← h]
                    exact scanSim_err rfl rfl
              · rw [if_neg hwi, err_eq] at h
                simp only [Result.ok.injEq] at h
                rw [if_pos (by simp [hwi]), ← h]
                exact scanSim_err rfl rfl
            · rw [if_neg h123, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_neg (by simpa using h123), ← h]
              exact scanSim_err rfl rfl

/-- `scan_fast::scan_rule_list_loop` refines `scanRuleListLoop` entered past
the `[` (`Scan/Fast.lean:1390-1416`). -/
theorem scan_rule_list_loop_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result ((alloc.vec.Vec frontend.scan_types.RuleRec) × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_rule_list_loop b i = ok o) :
    ScanSim absRuleRecs o (scanRuleListLoop (absBytes b) (absPos i) [] true) := by
  rw [frontend.scan_fast.scan_rule_list_loop] at h
  have := scan_rule_list_loop_loop_refines kit (b.val.length - i.val) i
    (alloc.vec.Vec.new frontend.scan_types.RuleRec) true o (le_refl _) h
  simpa [absRuleRecs, alloc.vec.Vec.new] using this

/-- `scan_fast::scan_rules` refines `scanRules` (`Scan/Fast.lean:1418-1422`). -/
theorem scan_rules_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result ((alloc.vec.Vec frontend.scan_types.RuleRec) × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_rules b i = ok o) :
    ScanSim absRuleRecs o (scanRules (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_rules] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanRules, byte_at_abs hc, absByte_beq_lit (d := 91#u8) (by decide)]
  by_cases h91 : c = 91#u8
  · rw [if_pos h91] at h
    rw [if_pos (by simpa using h91)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    exact scan_rule_list_loop_refines kit h
  · rw [if_neg h91, err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [if_neg (by simpa using h91), ← h]
    exact scanSim_err rfl (by rw [absPos_toNat])

/-! ## An inductive block's recursors

`scan_fast.rs:2224-2500` against `Scan/Fast.lean:1424-1596`. -/

/-- `scanIndRecListLoop` (`Scan/Fast.lean:1564-1590`), unfolded once at a port
position. -/
private theorem scanIndRecListLoop_eq (b : Slice Std.U8) (i : Std.Usize)
    (acc : List IndRecRec) (wi : Bool) :
    scanIndRecListLoop (absBytes b) (absPos i) acc wi =
      if i.val < b.val.length then
        (if isWs (absByte (pByte b i.val)) then
          scanIndRecListLoop (absBytes b) (absPos i + 1) acc wi
         else if absByte (pByte b i.val) == 93 then
           (if wi && !acc.isEmpty then .err ⟨i.val, .expectedList⟩
            else .ok acc.reverse (absPos i + 1))
         else if absByte (pByte b i.val) == 44 then
           (if wi then .err ⟨i.val, .expectedList⟩
            else scanIndRecListLoop (absBytes b) (absPos i + 1) acc true)
         else if absByte (pByte b i.val) == 123 then
           (if !wi then .err ⟨i.val, .expectedList⟩
            else match scanIndRec (absBytes b) (absPos i) with
              | .err e => .err e
              | .ok x e =>
                if absPos i < e then scanIndRecListLoop (absBytes b) e (x :: acc) false
                else .err ⟨i.val, .noProgress⟩)
         else .err ⟨i.val, .expectedList⟩)
      else .err ⟨i.val, .expectedList⟩ := by
  rw [scanIndRecListLoop]
  by_cases hi : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr hi), if_pos hi]
    simp only [uget_absPos, absPos_toNat]
    rfl
  · rw [dif_neg (fun hc => hi (absPos_lt_usize.mp hc)), if_neg hi, absPos_toNat]

set_option maxHeartbeats 2000000 in
/-- con-leche's `scanIndRecLoop` (`Scan/Fast.lean:1424-1556`) is `ScanObj`'s
`memberBody` at its own closing arm and key dispatch. -/
private theorem scanIndRecLoop_body (B : ByteArray) (S : UInt32) (isUns kf : Bool)
    (lps : List Nat) (nm nIdx nMin nMot nP : Nat) (rules : List RuleRec) (ty : Nat) :
    ∀ (p : USize) (w : Bool),
      scanIndRecLoop B p w S isUns kf lps nm nIdx nMin nMot nP rules ty
        = memberBody B
            (fun q w' => scanIndRecLoop B q w' S isUns kf lps nm nIdx nMin nMot nP rules ty)
            (fun q w' =>
              if w' && S != 0 then .err ⟨q.toNat, .expectedKey⟩
              else if (S &&& 2046) != 2046 then .err ⟨q.toNat, .missingKey⟩
              else .ok ⟨⟨nm, lps, ty⟩, isUns, kf, nIdx, nMin, nMot, nP, rules⟩ (q + 1))
            (fun k q v =>
              match k with
              | .kAll =>
                if (S &&& 1) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanNatList B v with
                  | .err err => .err err
                  | .ok _x e =>
                    if _hj : q < e then scanIndRecLoop B e false (S ||| 1) isUns kf lps nm nIdx nMin nMot nP rules ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kIsUnsafe =>
                if (S &&& 2) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanBool B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndRecLoop B e false (S ||| 2) x kf lps nm nIdx nMin nMot nP rules ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kK =>
                if (S &&& 4) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanBool B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndRecLoop B e false (S ||| 4) isUns x lps nm nIdx nMin nMot nP rules ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kLevelParams =>
                if (S &&& 8) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanNatList B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndRecLoop B e false (S ||| 8) isUns kf x nm nIdx nMin nMot nP rules ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kName =>
                if (S &&& 16) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndRecLoop B e false (S ||| 16) isUns kf lps n nIdx nMin nMot nP rules ty)
              | .kNumIndices =>
                if (S &&& 32) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndRecLoop B e false (S ||| 32) isUns kf lps nm n nMin nMot nP rules ty)
              | .kNumMinors =>
                if (S &&& 64) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndRecLoop B e false (S ||| 64) isUns kf lps nm nIdx n nMot nP rules ty)
              | .kNumMotives =>
                if (S &&& 128) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndRecLoop B e false (S ||| 128) isUns kf lps nm nIdx nMin n nP rules ty)
              | .kNumParams =>
                if (S &&& 256) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndRecLoop B e false (S ||| 256) isUns kf lps nm nIdx nMin nMot n rules ty)
              | .kRules =>
                if (S &&& 512) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanRules B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndRecLoop B e false (S ||| 512) isUns kf lps nm nIdx nMin nMot nP x ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kType =>
                if (S &&& 1024) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndRecLoop B e false (S ||| 1024) isUns kf lps nm nIdx nMin nMot nP rules n)
              | _ => .err ⟨q.toNat, .unknownKey⟩)
            p w := by
  intro p w
  rw [scanIndRecLoop.eq_def]
  rfl

/-- `scan_fast::scan_ind_rec_loop`'s loop refines `scanIndRecLoop`
(`Scan/Fast.lean:1424-1556`). -/
private theorem scan_ind_rec_loop_loop_refines {b : Slice Std.U8} (kit : KitFacts b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (is_uns kf : Bool)
      (lps : alloc.vec.Vec Std.U64) (nm n_idx n_min n_mot n_p : Std.U64)
      (rules : alloc.vec.Vec frontend.scan_types.RuleRec) (ty : Std.U64)
      (o : core.result.Result (frontend.scan_types.IndRecRec × Std.Usize)
        frontend.scan_types.ScanErr),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.scan_ind_rec_loop_loop w b i seen is_uns kf lps nm n_idx n_min n_mot n_p rules ty = ok o →
      ScanSim absIndRecRec o
        (scanIndRecLoop (absBytes b) (absPos i) w (absU32 seen) is_uns kf (absU64s lps)
          (absU64 nm) (absU64 n_idx) (absU64 n_min) (absU64 n_mot) (absU64 n_p)
          (absRuleRecs rules) (absU64 ty)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i seen is_uns kf lps nm n_idx n_min n_mot n_p rules ty o hf h
  rw [frontend.scan_fast.scan_ind_rec_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hstep := nextMember_step kit (scanIndRecLoop_body (absBytes b) (absU32 seen) is_uns kf (absU64s lps) (absU64 nm) (absU64 n_idx)
      (absU64 n_min) (absU64 n_mot) (absU64 n_p) (absRuleRecs rules) (absU64 ty)) (b.val.length - i.val) i w
    res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err hstep.err
  | Ok pm =>
    obtain ⟨mem, ni, nw⟩ := pm
    have hilt : i.val < b.val.length := next_member_lt hres
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [hstep.close]
      try dsimp only at h
      rw [u32_bne (x := seen) (y := 0#u32) (by rfl)]
      by_cases hnw : nw = true
      · rw [if_pos hnw] at h
        rw [hnw, Bool.true_and]
        by_cases hz : (seen != 0#u32) = true
        · rw [if_pos hz, err_eq] at h
          rw [if_pos hz]
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact scanSim_err rfl (by rw [absPos_toNat])
        · rw [if_neg hz] at h
          rw [if_neg hz]
          obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
          rw [← and_lit (x := seen) (by rfl) hi1, u32_bne (x := i1) (y := 2046#u32) (by rfl)]
          by_cases hm : (i1 != 2046#u32) = true
          · rw [if_pos hm, err_eq] at h
            rw [if_pos hm]
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact scanSim_err rfl (by rw [absPos_toNat])
          · rw [if_neg hm] at h
            rw [if_neg hm]
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.ok (by rw [absPos_add_one hi2]; rfl)
      · rw [if_neg hnw] at h
        simp only [Bool.not_eq_true] at hnw
        rw [hnw, Bool.false_and, if_neg (by simp)]
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        rw [← and_lit (x := seen) (by rfl) hi1, u32_bne (x := i1) (y := 2046#u32) (by rfl)]
        by_cases hm : (i1 != 2046#u32) = true
        · rw [if_pos hm, err_eq] at h
          rw [if_pos hm]
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact scanSim_err rfl (by rw [absPos_toNat])
        · rw [if_neg hm] at h
          rw [if_neg hm]
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact ScanSim.ok (by rw [absPos_add_one hi2]; rfl)
    | Key k ks v =>
      rw [hstep.key]
      have hks := next_member_ge (b.val.length - i.val) i w k ks v ni nw (le_refl _) hres
      cases k <;> dsimp only [absKey] at h ⊢ <;>
        first
          | (rw [err_eq] at h
             simp only [Result.ok.injEq] at h
             rw [← h]
             exact scanSim_err rfl (by rw [absPos_toNat]))
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 exact ScanSim.err (NatSlotStep.err (natSlot_step hr1))
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [NatSlotStep.ok (natSlot_step hr1)]
                 obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                 rw [← or_lit (x := seen) (by rfl) hseen1]
                 have hlt := slot_nat_prog hr1
                 exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ _ _ _ _ _ _ _ o
                   (le_refl _) h)
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 refine ScanSim.err ?_
                 intro le hle
                 rw [scanSim_err_eq (scan_nat_list_refines hr1) hle]
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [scanSim_ok_eq (scan_nat_list_refines hr1)]
                 try dsimp only
                 obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                 by_cases hp : b2 = true
                 · rw [if_pos hp] at h
                   have hlt := prog_lt hb2 hp
                   rw [dif_pos (absPos_lt.mpr hlt)]
                   obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                   rw [← or_lit (x := seen) (by rfl) hseen1]
                   exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ _ _ _ _ _ _ _ o
                     (le_refl _) h
                 · rw [if_neg hp, err_eq] at h
                   rw [dif_neg (fun hc => (prog_not_lt hb2 hp) (absPos_lt.mp hc))]
                   simp only [Result.ok.injEq] at h
                   rw [← h]
                   exact scanSim_err rfl (by rw [absPos_toNat]))
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 refine ScanSim.err ?_
                 intro le hle
                 rw [scanSim_err_eq (scan_bool_refines hr1) hle]
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [scanSim_ok_eq (scan_bool_refines hr1)]
                 try dsimp only
                 obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                 by_cases hp : b2 = true
                 · rw [if_pos hp] at h
                   have hlt := prog_lt hb2 hp
                   rw [dif_pos (absPos_lt.mpr hlt)]
                   obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                   rw [← or_lit (x := seen) (by rfl) hseen1]
                   exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ _ _ _ _ _ _ _ o
                     (le_refl _) h
                 · rw [if_neg hp, err_eq] at h
                   rw [dif_neg (fun hc => (prog_not_lt hb2 hp) (absPos_lt.mp hc))]
                   simp only [Result.ok.injEq] at h
                   rw [← h]
                   exact scanSim_err rfl (by rw [absPos_toNat]))
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 refine ScanSim.err ?_
                 intro le hle
                 rw [scanSim_err_eq (scan_rules_refines kit hr1) hle]
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [scanSim_ok_eq (scan_rules_refines kit hr1)]
                 try dsimp only
                 obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                 by_cases hp : b2 = true
                 · rw [if_pos hp] at h
                   have hlt := prog_lt hb2 hp
                   rw [dif_pos (absPos_lt.mpr hlt)]
                   obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                   rw [← or_lit (x := seen) (by rfl) hseen1]
                   exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ _ _ _ _ _ _ _ o
                     (le_refl _) h
                 · rw [if_neg hp, err_eq] at h
                   rw [dif_neg (fun hc => (prog_not_lt hb2 hp) (absPos_lt.mp hc))]
                   simp only [Result.ok.injEq] at h
                   rw [← h]
                   exact scanSim_err rfl (by rw [absPos_toNat]))

/-- `scan_fast::scan_ind_rec` refines `scanIndRec` (`Scan/Fast.lean:1558-1562`). -/
theorem scan_ind_rec_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.IndRecRec × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_ind_rec b i = ok o) :
    ScanSim absIndRecRec o (scanIndRec (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_ind_rec] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanIndRec, byte_at_abs hc, absByte_beq_lit (d := 123#u8) (by decide)]
  by_cases h123 : c = 123#u8
  · rw [if_pos h123] at h
    rw [if_pos (by simpa using h123)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2, frontend.scan_fast.scan_ind_rec_loop] at *
    exact scan_ind_rec_loop_loop_refines kit (b.val.length - i2.val) true i2 0#u32 false false
      (alloc.vec.Vec.new Std.U64) 0#u64 0#u64 0#u64 0#u64 0#u64
      (alloc.vec.Vec.new frontend.scan_types.RuleRec) 0#u64 o (le_refl _) h
  · rw [if_neg h123, err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [if_neg (by simpa using h123), ← h]
    exact scanSim_err rfl (by rw [absPos_toNat])

/-- `scan_fast::scan_ind_rec_list_loop`'s loop refines `scanIndRecListLoop`
(`Scan/Fast.lean:1564-1590`).  The port pushes onto a `Vec` where con-leche
conses onto a `List` and reverses at the close, so the invariant carries
`(absIndRecRecs acc).reverse`. -/
private theorem scan_ind_rec_list_loop_loop_refines {b : Slice Std.U8} (kit : KitFacts b)
    (f : Nat) :
    ∀ (i : Std.Usize) (acc : alloc.vec.Vec frontend.scan_types.IndRecRec) (wi : Bool)
      (o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndRecRec) × Std.Usize)
        frontend.scan_types.ScanErr),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.scan_ind_rec_list_loop_loop b i acc wi = ok o →
      ScanSim absIndRecRecs o
        (scanIndRecListLoop (absBytes b) (absPos i) (absIndRecRecs acc).reverse wi) := by
  induction f with
  | zero =>
    intro i acc wi o hf h
    rw [frontend.scan_fast.scan_ind_rec_list_loop_loop.eq_def,
      if_pos (show i ≥ Slice.len b by scalar_tac), err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [scanIndRecListLoop_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
    rw [← h]
    exact scanSim_err rfl rfl
  | succ f ih =>
    intro i acc wi o hf h
    rw [frontend.scan_fast.scan_ind_rec_list_loop_loop.eq_def] at h
    rw [scanIndRecListLoop_eq]
    by_cases hend : i ≥ Slice.len b
    · rw [if_pos hend, err_eq] at h
      simp only [Result.ok.injEq] at h
      rw [if_neg (show ¬ i.val < b.val.length by scalar_tac), ← h]
      exact scanSim_err rfl rfl
    · rw [if_neg hend] at h
      have hi : i.val < b.val.length := by scalar_tac
      rw [if_pos hi]
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
      rw [index_pByte hi hc] at hw h
      rw [← is_ws_abs hw]
      by_cases hws : w = true
      · rw [if_pos hws] at h
        rw [if_pos hws]
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hv := usize_add_one_inv hi2
        rw [← absPos_add_one hi2]
        exact ih i2 acc wi o (by omega) h
      · rw [if_neg hws] at h
        rw [if_neg hws]
        rw [absByte_beq_lit (d := 93#u8) (by decide), absByte_beq_lit (d := 44#u8) (by decide),
          absByte_beq_lit (d := 123#u8) (by decide)]
        by_cases h93 : pByte b i.val = 93#u8
        · rw [if_pos h93] at h
          rw [if_pos (by simpa using h93)]
          by_cases hwi : wi = true
          · rw [if_pos hwi] at h
            by_cases hne : (alloc.vec.Vec.len acc != 0#usize) = true
            · rw [if_pos hne, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_pos (show (wi && !(absIndRecRecs acc).reverse.isEmpty) = true by
                rw [absIndRecRecs, map_reverse_isEmpty, hwi]
                simp [vec_len_ne hne]), ← h]
              exact scanSim_err rfl rfl
            · rw [if_neg hne] at h
              obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
              simp only [Result.ok.injEq] at h
              rw [if_neg (show ¬ (wi && !(absIndRecRecs acc).reverse.isEmpty) = true by
                rw [absIndRecRecs, map_reverse_isEmpty]
                simp [vec_len_eq hne]), ← h]
              exact ScanSim.ok (by rw [List.reverse_reverse, absPos_add_one hi3])
          · rw [if_neg hwi] at h
            obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq] at h
            rw [if_neg (by simp [hwi]), ← h]
            exact ScanSim.ok (by rw [List.reverse_reverse, absPos_add_one hi3])
        · rw [if_neg h93] at h
          rw [if_neg (by simpa using h93)]
          by_cases h44 : pByte b i.val = 44#u8
          · rw [if_pos h44] at h
            rw [if_pos (by simpa using h44)]
            by_cases hwi : wi = true
            · rw [if_pos hwi, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_pos hwi, ← h]
              exact scanSim_err rfl rfl
            · rw [if_neg hwi] at h
              rw [if_neg hwi]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have hv := usize_add_one_inv hi2
              rw [← absPos_add_one hi2]
              exact ih i2 acc true o (by omega) h
          · rw [if_neg h44] at h
            rw [if_neg (by simpa using h44)]
            by_cases h123 : pByte b i.val = 123#u8
            · rw [if_pos h123] at h
              rw [if_pos (by simpa using h123)]
              by_cases hwi : wi = true
              · rw [if_pos hwi] at h
                rw [if_neg (by simp [hwi])]
                obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
                have hsim := scan_ind_rec_refines kit hr
                cases r with
                | Err er =>
                  simp only [Result.ok.injEq] at h
                  rw [← h]
                  refine ScanSim.err ?_
                  intro le hle
                  rw [hsim le hle]
                | Ok p =>
                  obtain ⟨x, e⟩ := p
                  simp only [uncurry_apply_pair] at h
                  rw [(hsim : scanIndRec (absBytes b) (absPos i) = _)]
                  dsimp only
                  obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                  have hb2v := prog_val hb2
                  by_cases hp : b2 = true
                  · rw [if_pos hp] at h
                    have hlt : i.val < e.val := by
                      rw [hp] at hb2v; simpa using hb2v.symm
                    rw [if_pos (show absPos i < absPos e by
                      rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]; exact hlt)]
                    obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok_iff.mp h
                    have : (absIndRecRecs acc1).reverse
                        = absIndRecRec x :: (absIndRecRecs acc).reverse := by
                      rw [absIndRecRecs, vec_push_val hacc1]
                      simp [absIndRecRecs]
                    rw [← this]
                    exact ih e acc1 false o (by omega) h
                  · rw [if_neg hp, err_eq] at h
                    simp only [Result.ok.injEq] at h
                    have hge : ¬ i.val < e.val := by
                      simp only [Bool.not_eq_true] at hp
                      rw [hp] at hb2v; simpa using hb2v.symm
                    rw [if_neg (show ¬ absPos i < absPos e by
                      rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]; exact hge), ← h]
                    exact scanSim_err rfl rfl
              · rw [if_neg hwi, err_eq] at h
                simp only [Result.ok.injEq] at h
                rw [if_pos (by simp [hwi]), ← h]
                exact scanSim_err rfl rfl
            · rw [if_neg h123, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_neg (by simpa using h123), ← h]
              exact scanSim_err rfl rfl

/-- `scan_fast::scan_ind_rec_list_loop` refines `scanIndRecListLoop` entered past
the `[` (`Scan/Fast.lean:1564-1590`). -/
theorem scan_ind_rec_list_loop_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndRecRec) × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_ind_rec_list_loop b i = ok o) :
    ScanSim absIndRecRecs o (scanIndRecListLoop (absBytes b) (absPos i) [] true) := by
  rw [frontend.scan_fast.scan_ind_rec_list_loop] at h
  have := scan_ind_rec_list_loop_loop_refines kit (b.val.length - i.val) i
    (alloc.vec.Vec.new frontend.scan_types.IndRecRec) true o (le_refl _) h
  simpa [absIndRecRecs, alloc.vec.Vec.new] using this

/-- `scan_fast::scan_ind_recs` refines `scanIndRecs` (`Scan/Fast.lean:1592-1596`). -/
theorem scan_ind_recs_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndRecRec) × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_ind_recs b i = ok o) :
    ScanSim absIndRecRecs o (scanIndRecs (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_ind_recs] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanIndRecs, byte_at_abs hc, absByte_beq_lit (d := 91#u8) (by decide)]
  by_cases h91 : c = 91#u8
  · rw [if_pos h91] at h
    rw [if_pos (by simpa using h91)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    exact scan_ind_rec_list_loop_refines kit h
  · rw [if_neg h91, err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [if_neg (by simpa using h91), ← h]
    exact scanSim_err rfl (by rw [absPos_toNat])

/-! ## An inductive block's types

`scan_fast.rs:2503-2782` against `Scan/Fast.lean:1598-1771`. -/

/-- `scanIndTypeListLoop` (`Scan/Fast.lean:1739-1765`), unfolded once at a port
position. -/
private theorem scanIndTypeListLoop_eq (b : Slice Std.U8) (i : Std.Usize)
    (acc : List IndTypeRec) (wi : Bool) :
    scanIndTypeListLoop (absBytes b) (absPos i) acc wi =
      if i.val < b.val.length then
        (if isWs (absByte (pByte b i.val)) then
          scanIndTypeListLoop (absBytes b) (absPos i + 1) acc wi
         else if absByte (pByte b i.val) == 93 then
           (if wi && !acc.isEmpty then .err ⟨i.val, .expectedList⟩
            else .ok acc.reverse (absPos i + 1))
         else if absByte (pByte b i.val) == 44 then
           (if wi then .err ⟨i.val, .expectedList⟩
            else scanIndTypeListLoop (absBytes b) (absPos i + 1) acc true)
         else if absByte (pByte b i.val) == 123 then
           (if !wi then .err ⟨i.val, .expectedList⟩
            else match scanIndType (absBytes b) (absPos i) with
              | .err e => .err e
              | .ok x e =>
                if absPos i < e then scanIndTypeListLoop (absBytes b) e (x :: acc) false
                else .err ⟨i.val, .noProgress⟩)
         else .err ⟨i.val, .expectedList⟩)
      else .err ⟨i.val, .expectedList⟩ := by
  rw [scanIndTypeListLoop]
  by_cases hi : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr hi), if_pos hi]
    simp only [uget_absPos, absPos_toNat]
    rfl
  · rw [dif_neg (fun hc => hi (absPos_lt_usize.mp hc)), if_neg hi, absPos_toNat]

set_option maxHeartbeats 2000000 in
/-- con-leche's `scanIndTypeLoop` (`Scan/Fast.lean:1598-1731`) is `ScanObj`'s
`memberBody` at its own closing arm and key dispatch. -/
private theorem scanIndTypeLoop_body (B : ByteArray) (S : UInt32) (ctors : List Nat)
    (isRec isRefl isUns : Bool) (lps : List Nat) (nm nIdx nNest nP ty : Nat) :
    ∀ (p : USize) (w : Bool),
      scanIndTypeLoop B p w S ctors isRec isRefl isUns lps nm nIdx nNest nP ty
        = memberBody B
            (fun q w' =>
              scanIndTypeLoop B q w' S ctors isRec isRefl isUns lps nm nIdx nNest nP ty)
            (fun q w' =>
              if w' && S != 0 then .err ⟨q.toNat, .expectedKey⟩
              else if (S &&& 2046) != 2046 then .err ⟨q.toNat, .missingKey⟩
              else .ok ⟨⟨nm, lps, ty⟩, ctors, isRec, isRefl, isUns, nIdx, nNest, nP⟩ (q + 1))
            (fun k q v =>
              match k with
              | .kAll =>
                if (S &&& 1) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanNatList B v with
                  | .err err => .err err
                  | .ok _x e =>
                    if _hj : q < e then scanIndTypeLoop B e false (S ||| 1) ctors isRec isRefl isUns lps nm nIdx nNest nP ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kCtors =>
                if (S &&& 2) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanNatList B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndTypeLoop B e false (S ||| 2) x isRec isRefl isUns lps nm nIdx nNest nP ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kIsRec =>
                if (S &&& 4) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanBool B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndTypeLoop B e false (S ||| 4) ctors x isRefl isUns lps nm nIdx nNest nP ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kIsReflexive =>
                if (S &&& 8) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanBool B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndTypeLoop B e false (S ||| 8) ctors isRec x isUns lps nm nIdx nNest nP ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kIsUnsafe =>
                if (S &&& 16) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanBool B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndTypeLoop B e false (S ||| 16) ctors isRec isRefl x lps nm nIdx nNest nP ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kLevelParams =>
                if (S &&& 32) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanNatList B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndTypeLoop B e false (S ||| 32) ctors isRec isRefl isUns x nm nIdx nNest nP ty
                    else .err ⟨q.toNat, .noProgress⟩
              | .kName =>
                if (S &&& 64) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndTypeLoop B e false (S ||| 64) ctors isRec isRefl isUns lps n nIdx nNest nP ty)
              | .kNumIndices =>
                if (S &&& 128) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndTypeLoop B e false (S ||| 128) ctors isRec isRefl isUns lps nm n nNest nP ty)
              | .kNumNested =>
                if (S &&& 256) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndTypeLoop B e false (S ||| 256) ctors isRec isRefl isUns lps nm nIdx n nP ty)
              | .kNumParams =>
                if (S &&& 512) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndTypeLoop B e false (S ||| 512) ctors isRec isRefl isUns lps nm nIdx nNest n ty)
              | .kType =>
                if (S &&& 1024) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndTypeLoop B e false (S ||| 1024) ctors isRec isRefl isUns lps nm nIdx nNest nP n)
              | _ => .err ⟨q.toNat, .unknownKey⟩)
            p w := by
  intro p w
  rw [scanIndTypeLoop.eq_def]
  rfl

/-- `scan_fast::scan_ind_type_loop`'s loop refines `scanIndTypeLoop`
(`Scan/Fast.lean:1598-1731`). -/
private theorem scan_ind_type_loop_loop_refines {b : Slice Std.U8} (kit : KitFacts b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (ctors : alloc.vec.Vec Std.U64)
      (is_rec is_refl is_uns : Bool) (lps : alloc.vec.Vec Std.U64)
      (nm n_idx n_nest n_p ty : Std.U64)
      (o : core.result.Result (frontend.scan_types.IndTypeRec × Std.Usize)
        frontend.scan_types.ScanErr),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.scan_ind_type_loop_loop w b i seen ctors is_rec is_refl is_uns lps nm n_idx n_nest n_p ty = ok o →
      ScanSim absIndTypeRec o
        (scanIndTypeLoop (absBytes b) (absPos i) w (absU32 seen) (absU64s ctors) is_rec is_refl
          is_uns (absU64s lps) (absU64 nm) (absU64 n_idx) (absU64 n_nest) (absU64 n_p)
          (absU64 ty)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i seen ctors is_rec is_refl is_uns lps nm n_idx n_nest n_p ty o hf h
  rw [frontend.scan_fast.scan_ind_type_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hstep := nextMember_step kit (scanIndTypeLoop_body (absBytes b) (absU32 seen) (absU64s ctors) is_rec is_refl is_uns (absU64s lps)
      (absU64 nm) (absU64 n_idx) (absU64 n_nest) (absU64 n_p) (absU64 ty)) (b.val.length - i.val) i w
    res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err hstep.err
  | Ok pm =>
    obtain ⟨mem, ni, nw⟩ := pm
    have hilt : i.val < b.val.length := next_member_lt hres
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [hstep.close]
      try dsimp only at h
      rw [u32_bne (x := seen) (y := 0#u32) (by rfl)]
      by_cases hnw : nw = true
      · rw [if_pos hnw] at h
        rw [hnw, Bool.true_and]
        by_cases hz : (seen != 0#u32) = true
        · rw [if_pos hz, err_eq] at h
          rw [if_pos hz]
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact scanSim_err rfl (by rw [absPos_toNat])
        · rw [if_neg hz] at h
          rw [if_neg hz]
          obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
          rw [← and_lit (x := seen) (by rfl) hi1, u32_bne (x := i1) (y := 2046#u32) (by rfl)]
          by_cases hm : (i1 != 2046#u32) = true
          · rw [if_pos hm, err_eq] at h
            rw [if_pos hm]
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact scanSim_err rfl (by rw [absPos_toNat])
          · rw [if_neg hm] at h
            rw [if_neg hm]
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.ok (by rw [absPos_add_one hi2]; rfl)
      · rw [if_neg hnw] at h
        simp only [Bool.not_eq_true] at hnw
        rw [hnw, Bool.false_and, if_neg (by simp)]
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        rw [← and_lit (x := seen) (by rfl) hi1, u32_bne (x := i1) (y := 2046#u32) (by rfl)]
        by_cases hm : (i1 != 2046#u32) = true
        · rw [if_pos hm, err_eq] at h
          rw [if_pos hm]
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact scanSim_err rfl (by rw [absPos_toNat])
        · rw [if_neg hm] at h
          rw [if_neg hm]
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact ScanSim.ok (by rw [absPos_add_one hi2]; rfl)
    | Key k ks v =>
      rw [hstep.key]
      have hks := next_member_ge (b.val.length - i.val) i w k ks v ni nw (le_refl _) hres
      cases k <;> dsimp only [absKey] at h ⊢ <;>
        first
          | (rw [err_eq] at h
             simp only [Result.ok.injEq] at h
             rw [← h]
             exact scanSim_err rfl (by rw [absPos_toNat]))
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 exact ScanSim.err (NatSlotStep.err (natSlot_step hr1))
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [NatSlotStep.ok (natSlot_step hr1)]
                 obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                 rw [← or_lit (x := seen) (by rfl) hseen1]
                 have hlt := slot_nat_prog hr1
                 exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ _ _ _ _ _ _ _ o
                   (le_refl _) h)
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 refine ScanSim.err ?_
                 intro le hle
                 rw [scanSim_err_eq (scan_nat_list_refines hr1) hle]
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [scanSim_ok_eq (scan_nat_list_refines hr1)]
                 try dsimp only
                 obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                 by_cases hp : b2 = true
                 · rw [if_pos hp] at h
                   have hlt := prog_lt hb2 hp
                   rw [dif_pos (absPos_lt.mpr hlt)]
                   obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                   rw [← or_lit (x := seen) (by rfl) hseen1]
                   exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ _ _ _ _ _ _ _ o
                     (le_refl _) h
                 · rw [if_neg hp, err_eq] at h
                   rw [dif_neg (fun hc => (prog_not_lt hb2 hp) (absPos_lt.mp hc))]
                   simp only [Result.ok.injEq] at h
                   rw [← h]
                   exact scanSim_err rfl (by rw [absPos_toNat]))
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 refine ScanSim.err ?_
                 intro le hle
                 rw [scanSim_err_eq (scan_bool_refines hr1) hle]
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [scanSim_ok_eq (scan_bool_refines hr1)]
                 try dsimp only
                 obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                 by_cases hp : b2 = true
                 · rw [if_pos hp] at h
                   have hlt := prog_lt hb2 hp
                   rw [dif_pos (absPos_lt.mpr hlt)]
                   obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                   rw [← or_lit (x := seen) (by rfl) hseen1]
                   exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ _ _ _ _ _ _ _ o
                     (le_refl _) h
                 · rw [if_neg hp, err_eq] at h
                   rw [dif_neg (fun hc => (prog_not_lt hb2 hp) (absPos_lt.mp hc))]
                   simp only [Result.ok.injEq] at h
                   rw [← h]
                   exact scanSim_err rfl (by rw [absPos_toNat]))

/-- `scan_fast::scan_ind_type` refines `scanIndType` (`Scan/Fast.lean:1733-1737`). -/
theorem scan_ind_type_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.IndTypeRec × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_ind_type b i = ok o) :
    ScanSim absIndTypeRec o (scanIndType (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_ind_type] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanIndType, byte_at_abs hc, absByte_beq_lit (d := 123#u8) (by decide)]
  by_cases h123 : c = 123#u8
  · rw [if_pos h123] at h
    rw [if_pos (by simpa using h123)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2, frontend.scan_fast.scan_ind_type_loop] at *
    exact scan_ind_type_loop_loop_refines kit (b.val.length - i2.val) true i2 0#u32
      (alloc.vec.Vec.new Std.U64) false false false (alloc.vec.Vec.new Std.U64)
      0#u64 0#u64 0#u64 0#u64 0#u64 o (le_refl _) h
  · rw [if_neg h123, err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [if_neg (by simpa using h123), ← h]
    exact scanSim_err rfl (by rw [absPos_toNat])

/-- `scan_fast::scan_ind_type_list_loop`'s loop refines `scanIndTypeListLoop`
(`Scan/Fast.lean:1739-1765`).  The port pushes onto a `Vec` where con-leche
conses onto a `List` and reverses at the close, so the invariant carries
`(absIndTypeRecs acc).reverse`. -/
private theorem scan_ind_type_list_loop_loop_refines {b : Slice Std.U8} (kit : KitFacts b)
    (f : Nat) :
    ∀ (i : Std.Usize) (acc : alloc.vec.Vec frontend.scan_types.IndTypeRec) (wi : Bool)
      (o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndTypeRec) × Std.Usize)
        frontend.scan_types.ScanErr),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.scan_ind_type_list_loop_loop b i acc wi = ok o →
      ScanSim absIndTypeRecs o
        (scanIndTypeListLoop (absBytes b) (absPos i) (absIndTypeRecs acc).reverse wi) := by
  induction f with
  | zero =>
    intro i acc wi o hf h
    rw [frontend.scan_fast.scan_ind_type_list_loop_loop.eq_def,
      if_pos (show i ≥ Slice.len b by scalar_tac), err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [scanIndTypeListLoop_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
    rw [← h]
    exact scanSim_err rfl rfl
  | succ f ih =>
    intro i acc wi o hf h
    rw [frontend.scan_fast.scan_ind_type_list_loop_loop.eq_def] at h
    rw [scanIndTypeListLoop_eq]
    by_cases hend : i ≥ Slice.len b
    · rw [if_pos hend, err_eq] at h
      simp only [Result.ok.injEq] at h
      rw [if_neg (show ¬ i.val < b.val.length by scalar_tac), ← h]
      exact scanSim_err rfl rfl
    · rw [if_neg hend] at h
      have hi : i.val < b.val.length := by scalar_tac
      rw [if_pos hi]
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
      rw [index_pByte hi hc] at hw h
      rw [← is_ws_abs hw]
      by_cases hws : w = true
      · rw [if_pos hws] at h
        rw [if_pos hws]
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hv := usize_add_one_inv hi2
        rw [← absPos_add_one hi2]
        exact ih i2 acc wi o (by omega) h
      · rw [if_neg hws] at h
        rw [if_neg hws]
        rw [absByte_beq_lit (d := 93#u8) (by decide), absByte_beq_lit (d := 44#u8) (by decide),
          absByte_beq_lit (d := 123#u8) (by decide)]
        by_cases h93 : pByte b i.val = 93#u8
        · rw [if_pos h93] at h
          rw [if_pos (by simpa using h93)]
          by_cases hwi : wi = true
          · rw [if_pos hwi] at h
            by_cases hne : (alloc.vec.Vec.len acc != 0#usize) = true
            · rw [if_pos hne, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_pos (show (wi && !(absIndTypeRecs acc).reverse.isEmpty) = true by
                rw [absIndTypeRecs, map_reverse_isEmpty, hwi]
                simp [vec_len_ne hne]), ← h]
              exact scanSim_err rfl rfl
            · rw [if_neg hne] at h
              obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
              simp only [Result.ok.injEq] at h
              rw [if_neg (show ¬ (wi && !(absIndTypeRecs acc).reverse.isEmpty) = true by
                rw [absIndTypeRecs, map_reverse_isEmpty]
                simp [vec_len_eq hne]), ← h]
              exact ScanSim.ok (by rw [List.reverse_reverse, absPos_add_one hi3])
          · rw [if_neg hwi] at h
            obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq] at h
            rw [if_neg (by simp [hwi]), ← h]
            exact ScanSim.ok (by rw [List.reverse_reverse, absPos_add_one hi3])
        · rw [if_neg h93] at h
          rw [if_neg (by simpa using h93)]
          by_cases h44 : pByte b i.val = 44#u8
          · rw [if_pos h44] at h
            rw [if_pos (by simpa using h44)]
            by_cases hwi : wi = true
            · rw [if_pos hwi, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_pos hwi, ← h]
              exact scanSim_err rfl rfl
            · rw [if_neg hwi] at h
              rw [if_neg hwi]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have hv := usize_add_one_inv hi2
              rw [← absPos_add_one hi2]
              exact ih i2 acc true o (by omega) h
          · rw [if_neg h44] at h
            rw [if_neg (by simpa using h44)]
            by_cases h123 : pByte b i.val = 123#u8
            · rw [if_pos h123] at h
              rw [if_pos (by simpa using h123)]
              by_cases hwi : wi = true
              · rw [if_pos hwi] at h
                rw [if_neg (by simp [hwi])]
                obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
                have hsim := scan_ind_type_refines kit hr
                cases r with
                | Err er =>
                  simp only [Result.ok.injEq] at h
                  rw [← h]
                  refine ScanSim.err ?_
                  intro le hle
                  rw [hsim le hle]
                | Ok p =>
                  obtain ⟨x, e⟩ := p
                  simp only [uncurry_apply_pair] at h
                  rw [(hsim : scanIndType (absBytes b) (absPos i) = _)]
                  dsimp only
                  obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                  have hb2v := prog_val hb2
                  by_cases hp : b2 = true
                  · rw [if_pos hp] at h
                    have hlt : i.val < e.val := by
                      rw [hp] at hb2v; simpa using hb2v.symm
                    rw [if_pos (show absPos i < absPos e by
                      rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]; exact hlt)]
                    obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok_iff.mp h
                    have : (absIndTypeRecs acc1).reverse
                        = absIndTypeRec x :: (absIndTypeRecs acc).reverse := by
                      rw [absIndTypeRecs, vec_push_val hacc1]
                      simp [absIndTypeRecs]
                    rw [← this]
                    exact ih e acc1 false o (by omega) h
                  · rw [if_neg hp, err_eq] at h
                    simp only [Result.ok.injEq] at h
                    have hge : ¬ i.val < e.val := by
                      simp only [Bool.not_eq_true] at hp
                      rw [hp] at hb2v; simpa using hb2v.symm
                    rw [if_neg (show ¬ absPos i < absPos e by
                      rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]; exact hge), ← h]
                    exact scanSim_err rfl rfl
              · rw [if_neg hwi, err_eq] at h
                simp only [Result.ok.injEq] at h
                rw [if_pos (by simp [hwi]), ← h]
                exact scanSim_err rfl rfl
            · rw [if_neg h123, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_neg (by simpa using h123), ← h]
              exact scanSim_err rfl rfl

/-- `scan_fast::scan_ind_type_list_loop` refines `scanIndTypeListLoop` entered past
the `[` (`Scan/Fast.lean:1739-1765`). -/
theorem scan_ind_type_list_loop_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndTypeRec) × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_ind_type_list_loop b i = ok o) :
    ScanSim absIndTypeRecs o (scanIndTypeListLoop (absBytes b) (absPos i) [] true) := by
  rw [frontend.scan_fast.scan_ind_type_list_loop] at h
  have := scan_ind_type_list_loop_loop_refines kit (b.val.length - i.val) i
    (alloc.vec.Vec.new frontend.scan_types.IndTypeRec) true o (le_refl _) h
  simpa [absIndTypeRecs, alloc.vec.Vec.new] using this

/-- `scan_fast::scan_ind_types` refines `scanIndTypes` (`Scan/Fast.lean:1767-1771`). -/
theorem scan_ind_types_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndTypeRec) × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_ind_types b i = ok o) :
    ScanSim absIndTypeRecs o (scanIndTypes (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_ind_types] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanIndTypes, byte_at_abs hc, absByte_beq_lit (d := 91#u8) (by decide)]
  by_cases h91 : c = 91#u8
  · rw [if_pos h91] at h
    rw [if_pos (by simpa using h91)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    exact scan_ind_type_list_loop_refines kit h
  · rw [if_neg h91, err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [if_neg (by simpa using h91), ← h]
    exact scanSim_err rfl (by rw [absPos_toNat])

/-! ## An inductive block's constructors

`scan_fast.rs:2785-3011` against `Scan/Fast.lean:1773-1920`. -/

/-- `scanIndCtorListLoop` (`Scan/Fast.lean:1888-1914`), unfolded once at a port
position. -/
private theorem scanIndCtorListLoop_eq (b : Slice Std.U8) (i : Std.Usize)
    (acc : List IndCtorRec) (wi : Bool) :
    scanIndCtorListLoop (absBytes b) (absPos i) acc wi =
      if i.val < b.val.length then
        (if isWs (absByte (pByte b i.val)) then
          scanIndCtorListLoop (absBytes b) (absPos i + 1) acc wi
         else if absByte (pByte b i.val) == 93 then
           (if wi && !acc.isEmpty then .err ⟨i.val, .expectedList⟩
            else .ok acc.reverse (absPos i + 1))
         else if absByte (pByte b i.val) == 44 then
           (if wi then .err ⟨i.val, .expectedList⟩
            else scanIndCtorListLoop (absBytes b) (absPos i + 1) acc true)
         else if absByte (pByte b i.val) == 123 then
           (if !wi then .err ⟨i.val, .expectedList⟩
            else match scanIndCtor (absBytes b) (absPos i) with
              | .err e => .err e
              | .ok x e =>
                if absPos i < e then scanIndCtorListLoop (absBytes b) e (x :: acc) false
                else .err ⟨i.val, .noProgress⟩)
         else .err ⟨i.val, .expectedList⟩)
      else .err ⟨i.val, .expectedList⟩ := by
  rw [scanIndCtorListLoop]
  by_cases hi : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr hi), if_pos hi]
    simp only [uget_absPos, absPos_toNat]
    rfl
  · rw [dif_neg (fun hc => hi (absPos_lt_usize.mp hc)), if_neg hi, absPos_toNat]

set_option maxHeartbeats 2000000 in
/-- con-leche's `scanIndCtorLoop` (`Scan/Fast.lean:1773-1878`) is `ScanObj`'s
`memberBody` at its own closing arm and key dispatch.  `cidx` and `induct` are
the dialect's optional redundant fields, so their slots install a `some`. -/
private theorem scanIndCtorLoop_body (B : ByteArray) (S : UInt32) (isUns : Bool)
    (lps : List Nat) (nm nF nP ty : Nat) (ci ind : Option Nat) :
    ∀ (p : USize) (w : Bool),
      scanIndCtorLoop B p w S isUns lps nm nF nP ty ci ind
        = memberBody B
            (fun q w' => scanIndCtorLoop B q w' S isUns lps nm nF nP ty ci ind)
            (fun q w' =>
              if w' && S != 0 then .err ⟨q.toNat, .expectedKey⟩
              else if (S &&& 252) != 252 then .err ⟨q.toNat, .missingKey⟩
              else .ok ⟨⟨nm, lps, ty⟩, isUns, nF, nP, ci, ind⟩ (q + 1))
            (fun k q v =>
              match k with
              | .kCidx =>
                if (S &&& 1) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndCtorLoop B e false (S ||| 1) isUns lps nm nF nP ty (some n) ind)
              | .kInduct =>
                if (S &&& 2) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndCtorLoop B e false (S ||| 2) isUns lps nm nF nP ty ci (some n))
              | .kIsUnsafe =>
                if (S &&& 4) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanBool B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndCtorLoop B e false (S ||| 4) x lps nm nF nP ty ci ind
                    else .err ⟨q.toNat, .noProgress⟩
              | .kLevelParams =>
                if (S &&& 8) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else match scanNatList B v with
                  | .err err => .err err
                  | .ok x e =>
                    if _hj : q < e then scanIndCtorLoop B e false (S ||| 8) isUns x nm nF nP ty ci ind
                    else .err ⟨q.toNat, .noProgress⟩
              | .kName =>
                if (S &&& 16) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndCtorLoop B e false (S ||| 16) isUns lps n nF nP ty ci ind)
              | .kNumFields =>
                if (S &&& 32) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndCtorLoop B e false (S ||| 32) isUns lps nm n nP ty ci ind)
              | .kNumParams =>
                if (S &&& 64) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndCtorLoop B e false (S ||| 64) isUns lps nm nF n ty ci ind)
              | .kType =>
                if (S &&& 128) != 0 then .err ⟨q.toNat, .duplicateKey⟩
                else natSlot B q v (fun n e =>
                  scanIndCtorLoop B e false (S ||| 128) isUns lps nm nF nP n ci ind)
              | _ => .err ⟨q.toNat, .unknownKey⟩)
            p w := by
  intro p w
  rw [scanIndCtorLoop.eq_def]
  rfl

/-- `scan_fast::scan_ind_ctor_loop`'s loop refines `scanIndCtorLoop`
(`Scan/Fast.lean:1773-1878`). -/
private theorem scan_ind_ctor_loop_loop_refines {b : Slice Std.U8} (kit : KitFacts b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (is_uns : Bool)
      (lps : alloc.vec.Vec Std.U64) (nm n_f n_p ty : Std.U64) (ci ind : Option Std.U64)
      (o : core.result.Result (frontend.scan_types.IndCtorRec × Std.Usize)
        frontend.scan_types.ScanErr),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.scan_ind_ctor_loop_loop w b i seen is_uns lps nm n_f n_p ty ci ind = ok o →
      ScanSim absIndCtorRec o
        (scanIndCtorLoop (absBytes b) (absPos i) w (absU32 seen) is_uns (absU64s lps) (absU64 nm)
          (absU64 n_f) (absU64 n_p) (absU64 ty) (ci.map absU64) (ind.map absU64)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i seen is_uns lps nm n_f n_p ty ci ind o hf h
  rw [frontend.scan_fast.scan_ind_ctor_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hstep := nextMember_step kit (scanIndCtorLoop_body (absBytes b) (absU32 seen) is_uns (absU64s lps) (absU64 nm) (absU64 n_f)
      (absU64 n_p) (absU64 ty) (ci.map absU64) (ind.map absU64)) (b.val.length - i.val) i w
    res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err hstep.err
  | Ok pm =>
    obtain ⟨mem, ni, nw⟩ := pm
    have hilt : i.val < b.val.length := next_member_lt hres
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [hstep.close]
      try dsimp only at h
      rw [u32_bne (x := seen) (y := 0#u32) (by rfl)]
      by_cases hnw : nw = true
      · rw [if_pos hnw] at h
        rw [hnw, Bool.true_and]
        by_cases hz : (seen != 0#u32) = true
        · rw [if_pos hz, err_eq] at h
          rw [if_pos hz]
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact scanSim_err rfl (by rw [absPos_toNat])
        · rw [if_neg hz] at h
          rw [if_neg hz]
          obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
          rw [← and_lit (x := seen) (by rfl) hi1, u32_bne (x := i1) (y := 252#u32) (by rfl)]
          by_cases hm : (i1 != 252#u32) = true
          · rw [if_pos hm, err_eq] at h
            rw [if_pos hm]
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact scanSim_err rfl (by rw [absPos_toNat])
          · rw [if_neg hm] at h
            rw [if_neg hm]
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.ok (by rw [absPos_add_one hi2]; rfl)
      · rw [if_neg hnw] at h
        simp only [Bool.not_eq_true] at hnw
        rw [hnw, Bool.false_and, if_neg (by simp)]
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        rw [← and_lit (x := seen) (by rfl) hi1, u32_bne (x := i1) (y := 252#u32) (by rfl)]
        by_cases hm : (i1 != 252#u32) = true
        · rw [if_pos hm, err_eq] at h
          rw [if_pos hm]
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact scanSim_err rfl (by rw [absPos_toNat])
        · rw [if_neg hm] at h
          rw [if_neg hm]
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact ScanSim.ok (by rw [absPos_add_one hi2]; rfl)
    | Key k ks v =>
      rw [hstep.key]
      have hks := next_member_ge (b.val.length - i.val) i w k ks v ni nw (le_refl _) hres
      cases k <;> dsimp only [absKey] at h ⊢ <;>
        first
          | (rw [err_eq] at h
             simp only [Result.ok.injEq] at h
             rw [← h]
             exact scanSim_err rfl (by rw [absPos_toNat]))
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 exact ScanSim.err (NatSlotStep.err (natSlot_step hr1))
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [NatSlotStep.ok (natSlot_step hr1)]
                 obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                 rw [← or_lit (x := seen) (by rfl) hseen1]
                 have hlt := slot_nat_prog hr1
                 exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ _ _ _ _ _ o
                   (le_refl _) h)
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 refine ScanSim.err ?_
                 intro le hle
                 rw [scanSim_err_eq (scan_nat_list_refines hr1) hle]
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [scanSim_ok_eq (scan_nat_list_refines hr1)]
                 try dsimp only
                 obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                 by_cases hp : b2 = true
                 · rw [if_pos hp] at h
                   have hlt := prog_lt hb2 hp
                   rw [dif_pos (absPos_lt.mpr hlt)]
                   obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                   rw [← or_lit (x := seen) (by rfl) hseen1]
                   exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ _ _ _ _ _ o
                     (le_refl _) h
                 · rw [if_neg hp, err_eq] at h
                   rw [dif_neg (fun hc => (prog_not_lt hb2 hp) (absPos_lt.mp hc))]
                   simp only [Result.ok.injEq] at h
                   rw [← h]
                   exact scanSim_err rfl (by rw [absPos_toNat]))
          | (obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
             rw [dup_bit (by rfl) hb1]
             by_cases hd : b1 = true
             · rw [if_pos hd, err_eq] at h
               rw [if_pos hd]
               simp only [Result.ok.injEq] at h
               rw [← h]
               exact scanSim_err rfl (by rw [absPos_toNat])
             · rw [if_neg hd] at h
               rw [if_neg hd]
               obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
               cases r1 with
               | Err er =>
                 simp only [Result.ok.injEq] at h
                 rw [← h]
                 refine ScanSim.err ?_
                 intro le hle
                 rw [scanSim_err_eq (scan_bool_refines hr1) hle]
               | Ok p1 =>
                 obtain ⟨x, e⟩ := p1
                 simp only [uncurry_apply_pair] at h
                 rw [scanSim_ok_eq (scan_bool_refines hr1)]
                 try dsimp only
                 obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                 by_cases hp : b2 = true
                 · rw [if_pos hp] at h
                   have hlt := prog_lt hb2 hp
                   rw [dif_pos (absPos_lt.mpr hlt)]
                   obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                   rw [← or_lit (x := seen) (by rfl) hseen1]
                   exact ih (b.val.length - e.val) (by omega) false e seen1 _ _ _ _ _ _ _ _ o
                     (le_refl _) h
                 · rw [if_neg hp, err_eq] at h
                   rw [dif_neg (fun hc => (prog_not_lt hb2 hp) (absPos_lt.mp hc))]
                   simp only [Result.ok.injEq] at h
                   rw [← h]
                   exact scanSim_err rfl (by rw [absPos_toNat]))

/-- `scan_fast::scan_ind_ctor` refines `scanIndCtor` (`Scan/Fast.lean:1880-1886`). -/
theorem scan_ind_ctor_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.IndCtorRec × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_ind_ctor b i = ok o) :
    ScanSim absIndCtorRec o (scanIndCtor (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_ind_ctor] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanIndCtor, byte_at_abs hc, absByte_beq_lit (d := 123#u8) (by decide)]
  by_cases h123 : c = 123#u8
  · rw [if_pos h123] at h
    rw [if_pos (by simpa using h123)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2, frontend.scan_fast.scan_ind_ctor_loop] at *
    exact scan_ind_ctor_loop_loop_refines kit (b.val.length - i2.val) true i2 0#u32 false
      (alloc.vec.Vec.new Std.U64) 0#u64 0#u64 0#u64 0#u64 none none o (le_refl _) h
  · rw [if_neg h123, err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [if_neg (by simpa using h123), ← h]
    exact scanSim_err rfl (by rw [absPos_toNat])

/-- `scan_fast::scan_ind_ctor_list_loop`'s loop refines `scanIndCtorListLoop`
(`Scan/Fast.lean:1888-1914`).  The port pushes onto a `Vec` where con-leche
conses onto a `List` and reverses at the close, so the invariant carries
`(absIndCtorRecs acc).reverse`. -/
private theorem scan_ind_ctor_list_loop_loop_refines {b : Slice Std.U8} (kit : KitFacts b)
    (f : Nat) :
    ∀ (i : Std.Usize) (acc : alloc.vec.Vec frontend.scan_types.IndCtorRec) (wi : Bool)
      (o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndCtorRec) × Std.Usize)
        frontend.scan_types.ScanErr),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.scan_ind_ctor_list_loop_loop b i acc wi = ok o →
      ScanSim absIndCtorRecs o
        (scanIndCtorListLoop (absBytes b) (absPos i) (absIndCtorRecs acc).reverse wi) := by
  induction f with
  | zero =>
    intro i acc wi o hf h
    rw [frontend.scan_fast.scan_ind_ctor_list_loop_loop.eq_def,
      if_pos (show i ≥ Slice.len b by scalar_tac), err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [scanIndCtorListLoop_eq, if_neg (show ¬ i.val < b.val.length by scalar_tac)]
    rw [← h]
    exact scanSim_err rfl rfl
  | succ f ih =>
    intro i acc wi o hf h
    rw [frontend.scan_fast.scan_ind_ctor_list_loop_loop.eq_def] at h
    rw [scanIndCtorListLoop_eq]
    by_cases hend : i ≥ Slice.len b
    · rw [if_pos hend, err_eq] at h
      simp only [Result.ok.injEq] at h
      rw [if_neg (show ¬ i.val < b.val.length by scalar_tac), ← h]
      exact scanSim_err rfl rfl
    · rw [if_neg hend] at h
      have hi : i.val < b.val.length := by scalar_tac
      rw [if_pos hi]
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
      rw [index_pByte hi hc] at hw h
      rw [← is_ws_abs hw]
      by_cases hws : w = true
      · rw [if_pos hws] at h
        rw [if_pos hws]
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hv := usize_add_one_inv hi2
        rw [← absPos_add_one hi2]
        exact ih i2 acc wi o (by omega) h
      · rw [if_neg hws] at h
        rw [if_neg hws]
        rw [absByte_beq_lit (d := 93#u8) (by decide), absByte_beq_lit (d := 44#u8) (by decide),
          absByte_beq_lit (d := 123#u8) (by decide)]
        by_cases h93 : pByte b i.val = 93#u8
        · rw [if_pos h93] at h
          rw [if_pos (by simpa using h93)]
          by_cases hwi : wi = true
          · rw [if_pos hwi] at h
            by_cases hne : (alloc.vec.Vec.len acc != 0#usize) = true
            · rw [if_pos hne, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_pos (show (wi && !(absIndCtorRecs acc).reverse.isEmpty) = true by
                rw [absIndCtorRecs, map_reverse_isEmpty, hwi]
                simp [vec_len_ne hne]), ← h]
              exact scanSim_err rfl rfl
            · rw [if_neg hne] at h
              obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
              simp only [Result.ok.injEq] at h
              rw [if_neg (show ¬ (wi && !(absIndCtorRecs acc).reverse.isEmpty) = true by
                rw [absIndCtorRecs, map_reverse_isEmpty]
                simp [vec_len_eq hne]), ← h]
              exact ScanSim.ok (by rw [List.reverse_reverse, absPos_add_one hi3])
          · rw [if_neg hwi] at h
            obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq] at h
            rw [if_neg (by simp [hwi]), ← h]
            exact ScanSim.ok (by rw [List.reverse_reverse, absPos_add_one hi3])
        · rw [if_neg h93] at h
          rw [if_neg (by simpa using h93)]
          by_cases h44 : pByte b i.val = 44#u8
          · rw [if_pos h44] at h
            rw [if_pos (by simpa using h44)]
            by_cases hwi : wi = true
            · rw [if_pos hwi, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_pos hwi, ← h]
              exact scanSim_err rfl rfl
            · rw [if_neg hwi] at h
              rw [if_neg hwi]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have hv := usize_add_one_inv hi2
              rw [← absPos_add_one hi2]
              exact ih i2 acc true o (by omega) h
          · rw [if_neg h44] at h
            rw [if_neg (by simpa using h44)]
            by_cases h123 : pByte b i.val = 123#u8
            · rw [if_pos h123] at h
              rw [if_pos (by simpa using h123)]
              by_cases hwi : wi = true
              · rw [if_pos hwi] at h
                rw [if_neg (by simp [hwi])]
                obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
                have hsim := scan_ind_ctor_refines kit hr
                cases r with
                | Err er =>
                  simp only [Result.ok.injEq] at h
                  rw [← h]
                  refine ScanSim.err ?_
                  intro le hle
                  rw [hsim le hle]
                | Ok p =>
                  obtain ⟨x, e⟩ := p
                  simp only [uncurry_apply_pair] at h
                  rw [(hsim : scanIndCtor (absBytes b) (absPos i) = _)]
                  dsimp only
                  obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                  have hb2v := prog_val hb2
                  by_cases hp : b2 = true
                  · rw [if_pos hp] at h
                    have hlt : i.val < e.val := by
                      rw [hp] at hb2v; simpa using hb2v.symm
                    rw [if_pos (show absPos i < absPos e by
                      rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]; exact hlt)]
                    obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok_iff.mp h
                    have : (absIndCtorRecs acc1).reverse
                        = absIndCtorRec x :: (absIndCtorRecs acc).reverse := by
                      rw [absIndCtorRecs, vec_push_val hacc1]
                      simp [absIndCtorRecs]
                    rw [← this]
                    exact ih e acc1 false o (by omega) h
                  · rw [if_neg hp, err_eq] at h
                    simp only [Result.ok.injEq] at h
                    have hge : ¬ i.val < e.val := by
                      simp only [Bool.not_eq_true] at hp
                      rw [hp] at hb2v; simpa using hb2v.symm
                    rw [if_neg (show ¬ absPos i < absPos e by
                      rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]; exact hge), ← h]
                    exact scanSim_err rfl rfl
              · rw [if_neg hwi, err_eq] at h
                simp only [Result.ok.injEq] at h
                rw [if_pos (by simp [hwi]), ← h]
                exact scanSim_err rfl rfl
            · rw [if_neg h123, err_eq] at h
              simp only [Result.ok.injEq] at h
              rw [if_neg (by simpa using h123), ← h]
              exact scanSim_err rfl rfl

/-- `scan_fast::scan_ind_ctor_list_loop` refines `scanIndCtorListLoop` entered past
the `[` (`Scan/Fast.lean:1888-1914`). -/
theorem scan_ind_ctor_list_loop_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndCtorRec) × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_ind_ctor_list_loop b i = ok o) :
    ScanSim absIndCtorRecs o (scanIndCtorListLoop (absBytes b) (absPos i) [] true) := by
  rw [frontend.scan_fast.scan_ind_ctor_list_loop] at h
  have := scan_ind_ctor_list_loop_loop_refines kit (b.val.length - i.val) i
    (alloc.vec.Vec.new frontend.scan_types.IndCtorRec) true o (le_refl _) h
  simpa [absIndCtorRecs, alloc.vec.Vec.new] using this

/-- `scan_fast::scan_ind_ctors` refines `scanIndCtors` (`Scan/Fast.lean:1916-1920`). -/
theorem scan_ind_ctors_refines {b : Slice Std.U8} (kit : KitFacts b) {i : Std.Usize}
    {o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndCtorRec) × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_ind_ctors b i = ok o) :
    ScanSim absIndCtorRecs o (scanIndCtors (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_ind_ctors] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanIndCtors, byte_at_abs hc, absByte_beq_lit (d := 91#u8) (by decide)]
  by_cases h91 : c = 91#u8
  · rw [if_pos h91] at h
    rw [if_pos (by simpa using h91)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    exact scan_ind_ctor_list_loop_refines kit h
  · rw [if_neg h91, err_eq] at h
    simp only [Result.ok.injEq] at h
    rw [if_neg (by simpa using h91), ← h]
    exact scanSim_err rfl (by rw [absPos_toNat])

end ConRon.Refine.Frontend
