/-
**The list and name-object scanners, exact against con-leche** (task #87,
phase 3).

`crates/con-ron-core/src/frontend/scan_fast.rs:1169-1608` against
`ConLeche/Frontend/Scan/Fast.lean:666-905`: the index-list loop, the two
variant-valued fields `pw` and `hints`, and the first two **slot loops** —
the two name-table records.

## What this file gives the record scanners

Agents E, I and L consume exactly these, plus the object skeleton below.
`kitFacts b : KitFacts b` discharges the `kf` argument from `ScanKit`.

    theorem scan_bool_refines
        (h : frontend.scan_fast.scan_bool b i = ok o) :
        ScanSim id o (scanBool (absBytes b) (absPos i))

    theorem scan_nat_list_refines
        (h : frontend.scan_fast.scan_nat_list b i = ok o) :
        ScanSim absU64s o (scanNatList (absBytes b) (absPos i))

    theorem scan_nat_list_loop_refines
        (h : frontend.scan_fast.scan_nat_list_loop b i = ok o) :
        ScanSim absU64s o (scanNatListLoop (absBytes b) (absPos i) [] true)

    theorem scan_pw_refines
        (h : frontend.scan_fast.scan_pw b i = ok o) :
        ScanSim absPwRec o (scanPw (absBytes b) (absPos i))

    theorem scan_hints_refines (kf : KitFacts b)
        (h : frontend.scan_fast.scan_hints b i = ok o) :
        ScanSim absHintsRec o (scanHints (absBytes b) (absPos i))

    theorem scan_str_name_refines (kf : KitFacts b) (hstr : ScanStringFacts b)
        (h : frontend.scan_fast.scan_str_name b i = ok o) :
        ScanSim absNameRec o (scanStrName (absBytes b) (absPos i))

    theorem scan_num_name_refines (kf : KitFacts b)
        (h : frontend.scan_fast.scan_num_name b i = ok o) :
        ScanSim absNameRec o (scanNumName (absBytes b) (absPos i))

`b : Slice Std.U8`, `i : Std.Usize` and the port's outcome `o` are implicit in
all of them.  `scan_nat_list_loop_refines` is exported because `scanPw` and
every list-valued slot of the tier enter the loop past the `[` rather than
through `scanNatList`; `scan_str_name_loop_refines` and
`scan_num_name_loop_refines` likewise.

`ScanStringFacts b` is the one ingredient still outstanding:
`scan_fast::scan_string` against `Scan/Fast.lean:617-638 scanString`, which
`Refine/Frontend/ScanStr.lean` does not have yet.  It is a named hypothesis in
the `Refine/IndSpec.lean` style, not a `sorry`.

## The two shapes, once

* **A list loop** (`scan_nat_list_loop`) accumulates into a `Vec` in the port
  and conses onto a `List` in con-leche, reversing at the close.  The
  invariant is therefore `(absU64s acc).reverse` — *the port's accumulator,
  abstracted and reversed, is con-leche's* — and the close is
  `List.reverse_reverse`.  Every other list loop of the tier (agent I's four,
  agent L's) is this proof with another element abstraction.

* **A slot loop** (`scan_str_name_loop`, `scan_num_name_loop`) is a `while`
  over JSON members.  con-leche writes the member step out inline in each of
  its twenty `scan*Loop`s; the port factors it once as
  `scan_fast::next_member` (`scan_types.rs`'s module note, deviation 3, the
  way `Scan/Naive.lean`'s `naiveObjLoop` factors it).  The bridge is
  `objStep` — con-leche's inlined skeleton read back with its three
  continuations abstracted — and `next_member_sim`, which runs the port's
  factored copy against it once and for all.  A loop then owes only its own
  `close` and `key` arms.

## `sorry` count in this file: 0

**Moved back from `RefineOld/Frontend/ScanObj.lean` by task #97-P5-Front** (namespace
`ConRon.Refine2.Frontend`, the `#guard_msgs` strings re-spelled, nothing else).
-/
import ConRon.Refine2.Frontend.Scan.Kit

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine2.Frontend
open ConRon.Refine

open ConRon.Refine
open ConLeche.Frontend

/-! ## Plumbing -/

/-- An Aeneas `err` arm, read forwards. -/
private theorem err_val {T : Type} {offset : Std.Usize}
    {what : frontend.scan_types.ErrTag} {x : core.result.Result (T × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.err T offset what = ok x) :
    x = .Err ⟨offset, what⟩ := by
  rw [frontend.scan_fast.err] at h
  exact (Result.ok_injective h).symm

/-- Two port positions are equal exactly when their values are. -/
theorem usize_ext {i j : Std.Usize} (h : i.val = j.val) : i = j :=
  Std.UScalar.eq_of_val_eq h

@[simp] theorem absPos_eq_iff {i j : Std.Usize} : absPos i = absPos j ↔ i = j := by
  constructor
  · intro h; exact usize_ext (absPos_inj h)
  · intro h; rw [h]

/-- `absPos` of the zero position is `0`, which is con-leche's "no such
position" sentinel. -/
@[simp] theorem absPos_zero : absPos 0#usize = 0 := by
  apply USize.toNat_inj.mp; simp

/-! ## `num_end`'s digit run

`ScanKit` owns the scalar readers now, including `read_nat_at_refines` with the
**side condition** this file's first draft discovered it needs: con-leche's
`readNatAt` falls back to `readNat`, which runs to the end of the *digit run*
rather than to `e`, so "the port's `read_nat_at b i e` is `readNatAt b i e`" is
false for an `e` inside a run (a 22-digit run and `e = i + 19` make the two
sides differ).  Every caller has the condition; the one line below is how the
object loops get it out of `num_end`. -/

/-- A `lift`ed pure step is an equation on its value. -/
private theorem lift_val {α : Type} {x y : α} (h : lift x = ok y) : x = y := by
  simpa only [lift, Result.ok.injEq] using h

/-- The digit run `num_end` accepted really starts at `i` **and moves forward**
-- `ScanKit`'s `num_end_run` and `skip_digits_ge` together, which is the shape
every `Nat`-valued slot wants. -/
private theorem kit_num_end_run {b : Slice Std.U8} {i e : Std.Usize}
    (h : frontend.scan_fast.num_end b i = ok e) (hne : e ≠ i) :
    frontend.scan_fast.skip_digits b i = ok e ∧ i.val < e.val := by
  have hs := num_end_run h hne
  have hge := skip_digits_ge hs
  have hne' : i.val ≠ e.val := fun hc => hne (usize_ext hc.symm)
  exact ⟨hs, by omega⟩

/-! ## The shared object-member step

**Hosted here** (coordinator's ruling of task #87): `ScanObj` is the lowest
common ancestor of `ScanExpr`, `ScanInd` and `ScanLine`, so the one copy of
con-leche's inlined member skeleton and of the induction that runs the port's
factored `scan_fast::next_member` against it lives here.  The text is agent
E's, from `Refine/Frontend/ScanExpr.lean`, with two changes:

* `KitFacts` keeps only the three *key* facts.  `num_end` and `read_nat_at`
  were fields of it; they are proved above instead, and `natSlot_step` uses
  the proofs.
* `KitFacts.read_nat_at` could not have been proved as it stood: con-leche's
  `readNatAt` falls back to `readNat`, which runs to the end of the **digit
  run** rather than to `e`, so the claim needs `e` to be that end.  Every
  caller has it (`num_end`/`skip_digits` produced `e`), and `kit_read_nat_at`
  takes it as a hypothesis. -/

theorem absByte_inj {a b : Std.U8} (h : absByte a = absByte b) : a = b := by
  have := congrArg UInt8.toNat h
  simp only [absByte_toNat] at this
  scalar_tac

/-- Two port bytes compare as con-leche's. -/
theorem absByte_beq_u8 (a b : Std.U8) : (absByte a == absByte b) = (a == b) := by
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

/-- The port's `usize` subtraction, abstracted: a difference the port returned
`ok` for did not underflow, so con-leche's machine word did not wrap. -/
theorem absPos_sub {x y z : Std.Usize} (h : x - y = ok z) :
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

/-- **The `ScanKit` facts the skeleton stands on**: the three key lemmas
`ScanKit` owes.  Bundling them keeps every consumer one `KitFacts b` away from
being hypothesis-free. -/
structure KitFacts (b : Slice Std.U8) : Prop where
  /-- `scan_fast::key_end` against `Scan/Fast.lean:133-146 keyEnd`. -/
  key_end : ∀ (j ke : Std.Usize),
    frontend.scan_fast.key_end b j = ok ke → keyEnd (absBytes b) (absPos j) = absPos ke
  /-- `scan_fast::value_at` against `Scan/Fast.lean:448-453 valueAt`. -/
  value_at : ∀ (i ke v : Std.Usize),
    frontend.scan_fast.value_at b i ke = ok v →
      valueAt (absBytes b) (absPos i) (absPos ke) = absPos v
  /-- `scan_fast::key_at` against `Scan/Fast.lean:224-446 keyAt`. -/
  key_at : ∀ (i kl : Std.Usize) (k : frontend.scan_types.Key),
    frontend.scan_fast.key_at b i kl = ok k →
      keyAt (absBytes b) (absPos i) (absPos kl) = absKey k

/-- **`KitFacts` from `ScanKit`.**  `ScanKit` states every leaf refinement
port-on-the-left and `KitFacts`' fields state them con-leche-on-the-left,
hence the three `.symm`s. -/
theorem kitFacts (b : Slice Std.U8) : KitFacts b :=
  ⟨fun _ _ h => (key_end_refines h).symm,
   fun _ _ _ h => (value_at_refines h).symm,
   fun _ _ _ h => (key_at_refines h).symm⟩

section Step
variable {b : Slice Std.U8}

/-- **The one induction every slot loop of the tier runs.**
`scan_fast::next_member` (`scan_fast.rs:1374-1435`) against the
whitespace/comma/key skeleton every `scan*Loop` of `Scan/Fast.lean` writes out
inline.  The measure is phase 1's, `b.len() - i`. -/
theorem nextMember_step {α : Type} (kf : KitFacts b) {L CL : USize → Bool → ScanRes α}
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
                  rw [← hp2]; exact kf.key_end i2 ke hke
                rw [hkeE]
                by_cases h6 : ke = 0#usize
                · rw [if_pos h6] at h
                  rw [if_pos (show (absPos ke == (0 : USize)) = true by simp; scalar_tac),
                    ← Result.ok_injective h]
                  exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
                · rw [if_neg h6] at h
                  rw [if_neg (show ¬ ((absPos ke == (0 : USize)) = true) by
                    simp; intro hx; exact h6 (usize_ext (by simpa using hx)))]
                  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                  rw [kf.value_at i ke v hv]
                  by_cases h7 : v = i
                  · rw [if_pos h7] at h
                    rw [if_pos (show (absPos v == absPos i) = true by simp; scalar_tac),
                      ← Result.ok_injective h]
                    exact ScanErrSim.mk (t := .expectedColon) rfl (by simp)
                  · rw [if_neg h7] at h
                    rw [if_neg (show ¬ ((absPos v == absPos i) = true) by
                      simp; intro hx; exact h7 (usize_ext hx))]
                    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
                    have h3E : absPos ke - (absPos i + 1) = absPos i3 := by
                      rw [← hp2, ← absPos_sub hi3]
                    rw [h3E, kf.key_at i i3 k hk, ← Result.ok_injective h]
              · rw [if_neg h5] at h
                rw [if_pos (by simp [h5]), ← Result.ok_injective h]
                exact ScanErrSim.mk (t := .expectedComma) rfl (by simp)
            · rw [if_neg h4] at h
              rw [if_neg (by simp [h4]), ← Result.ok_injective h]
              exact ScanErrSim.mk (t := .expectedComma) rfl (by simp)

/-! ### Reading a member step back -/

theorem MemberStep.close {α : Type} {L CL : USize → Bool → ScanRes α}
    {DI : Key → USize → USize → ScanRes α} {i ni : Std.Usize} {w nw : Bool}
    (h : MemberStep L CL DI i w (.Ok (.Close, ni, nw))) :
    L (absPos i) w = CL (absPos ni) nw := h

theorem MemberStep.key {α : Type} {L CL : USize → Bool → ScanRes α}
    {DI : Key → USize → USize → ScanRes α} {i ks v ni : Std.Usize} {w nw : Bool}
    {k : frontend.scan_types.Key}
    (h : MemberStep L CL DI i w (.Ok (.Key k ks v, ni, nw))) :
    L (absPos i) w = DI (absKey k) (absPos ks) (absPos v) := h

theorem MemberStep.err {α : Type} {L CL : USize → Bool → ScanRes α}
    {DI : Key → USize → USize → ScanRes α} {i : Std.Usize} {w : Bool}
    {e : frontend.scan_types.ScanErr} (h : MemberStep L CL DI i w (.Err e)) :
    ScanErrSim e (L (absPos i) w) := h

/-! ## A `Nat`-valued slot

`scan_fast::slot_nat` is the `numEnd`/`readNatAt`/`noProgress` chain every
`Nat`-valued slot of every `scan*Loop` writes out (module note, deviation 3).
`natSlot` is that chain with the slot's continuation abstracted. -/

/-- con-leche's `Nat`-valued slot, with the continuation abstracted. -/
def natSlot {α : Type} (b : ByteArray) (ks v : USize)
    (K : Nat → USize → ScanRes α) : ScanRes α :=
  if numEnd b v == v then .err ⟨v.toNat, .expectedNat⟩
  else if _hj : ks < numEnd b v then K (readNatAt b v (numEnd b v)) (numEnd b v)
  else .err ⟨ks.toNat, .noProgress⟩

/-- What one `scan_fast::slot_nat` says about that chain. -/
def NatSlotStep {α : Type} (b : Slice Std.U8) (ks v : Std.Usize)
    (K : Nat → USize → ScanRes α)
    (o : core.result.Result (Std.U64 × Std.Usize) frontend.scan_types.ScanErr) : Prop :=
  match o with
  | .Ok (x, e) => natSlot (absBytes b) (absPos ks) (absPos v) K = K (absU64 x) (absPos e)
  | .Err er => ScanErrSim er (natSlot (absBytes b) (absPos ks) (absPos v) K)

theorem NatSlotStep.ok {α : Type} {b : Slice Std.U8} {ks v e : Std.Usize}
    {K : Nat → USize → ScanRes α} {x : Std.U64}
    (h : NatSlotStep b ks v K (.Ok (x, e))) :
    natSlot (absBytes b) (absPos ks) (absPos v) K = K (absU64 x) (absPos e) := h

theorem NatSlotStep.err {α : Type} {b : Slice Std.U8} {ks v : Std.Usize}
    {K : Nat → USize → ScanRes α} {er : frontend.scan_types.ScanErr}
    (h : NatSlotStep b ks v K (.Err er)) :
    ScanErrSim er (natSlot (absBytes b) (absPos ks) (absPos v) K) := h

/-- **`scan_fast::slot_nat` against the chain con-leche writes out.**  Needs no
`KitFacts`: `num_end` and `read_nat_at` are proved above. -/
theorem natSlot_step {α : Type} {ks v : Std.Usize}
    {K : Nat → USize → ScanRes α} {o}
    (h : frontend.scan_fast.slot_nat b ks v = ok o) : NatSlotStep b ks v K o := by
  rw [frontend.scan_fast.slot_nat] at h
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  have heA : absPos e = numEnd (absBytes b) (absPos v) := num_end_refines he
  rw [NatSlotStep.eq_def, natSlot, ← heA]
  by_cases h1 : e = v
  · rw [if_pos h1] at h
    rw [if_pos (show (absPos e == absPos v) = true by simp; scalar_tac), err_val h]
    exact ScanErrSim.mk (t := .expectedNat) rfl (by simp)
  · rw [if_neg h1] at h
    rw [if_neg (show ¬ ((absPos e == absPos v) = true) by
      simp; intro hx; exact h1 (usize_ext hx))]
    obtain ⟨hrun, -⟩ := kit_num_end_run he h1
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1' : b1 = decide (ks.val < e.val) := by
      rw [frontend.scan_fast.prog] at hb1
      have := Result.ok_injective hb1
      rw [← this]; exact decide_eq_decide.mpr (by constructor <;> (intro hx; scalar_tac))
    by_cases h2 : b1 = true
    · rw [if_pos h2] at h
      rw [dif_pos (absPos_lt.mpr (by rw [hb1'] at h2; simpa using h2))]
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Ok x =>
        rw [← Result.ok_injective h, ← read_nat_at_refines hrun hr]
      | Err er =>
        rw [← Result.ok_injective h]
        exact read_nat_at_err hr
    · rw [if_neg h2] at h
      rw [dif_neg (by rw [absPos_lt]; rw [hb1'] at h2; simpa using h2), err_val h]
      exact ScanErrSim.mk (t := .noProgress) rfl (by simp)

end Step

/-! ## Literals

Every string literal of the module is a `[u8; N]` constant (task #86, DESIGN.md
§3.8), read as a slice at the call site. -/

/-- A `const [u8; N]` literal read as a slice: the slice is the array. -/
private theorem slice_lit_val {k : Std.Usize} {S : Std.Array Std.U8 k} {s : Slice Std.U8}
    (h : lift (Std.Array.to_slice S) = ok s) : s.val = S.val := by
  simp only [lift_eq, Result.ok.injEq] at h
  subst h
  simp [Std.Array.val_to_slice]

/-- A port position advanced by a literal's width. -/
theorem absPos_add {i c j : Std.Usize} (h : i + c = ok j) :
    absPos j = absPos i + absPos c := by
  have hj : j.val = i.val + c.val := ConRon.Refine.Nat.uadd_val h
  have hb : i.val + c.val < USize.size := by have := usize_val_lt_size j; omega
  apply USize.toNat_inj.mp
  simp only [USize.toNat_add, absPos_toNat, hj]
  exact (Nat.mod_eq_of_lt hb).symm

/-! ## `scan_bool`

`scan_fast.rs:723-733` against `Scan/Fast.lean:466-469 scanBool`. -/

/-- **`scan_bool` refines `scanBool`** (`Scan/Fast.lean:466-469`). -/
theorem scan_bool_refines {b : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (Bool × Std.Usize) frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_bool b i = ok o) :
    ScanSim id o (scanBool (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_bool] at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  have hsv : s.val = [116#u8, 114#u8, 117#u8, 101#u8] := by
    rw [slice_lit_val hs]; simp [global_simps]
  have hsb : absBytes s = "true".toUTF8 := by rw [absBytes, hsv]; decide
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
  have hb1' : b1 = matchLit (absBytes b) (absPos i) "true".toUTF8 0 := by
    rw [← hsb]; exact match_lit_refines (by rw [hsv]; decide) hb1
  rw [scanBool, ← hb1']
  by_cases hbt : b1 = true
  · rw [if_pos hbt] at h ⊢
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    refine ScanSim.ok ?_
    rw [absPos_add hi1, show absPos 4#usize = (4 : USize) from by
      apply USize.toNat_inj.mp; simp]
    rfl
  · rw [if_neg hbt] at h ⊢
    obtain ⟨s1, hs1, h⟩ := bind_eq_ok_iff.mp h
    have hs1v : s1.val = [102#u8, 97#u8, 108#u8, 115#u8, 101#u8] := by
      rw [slice_lit_val hs1]; simp [global_simps]
    have hs1b : absBytes s1 = "false".toUTF8 := by rw [absBytes, hs1v]; decide
    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
    have hb2' : b2 = matchLit (absBytes b) (absPos i) "false".toUTF8 0 := by
      rw [← hs1b]; exact match_lit_refines (by rw [hs1v]; decide) hb2
    rw [← hb2']
    by_cases hbf : b2 = true
    · rw [if_pos hbf] at h ⊢
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h]
      refine ScanSim.ok ?_
      rw [absPos_add hi1, show absPos 5#usize = (5 : USize) from by
        apply USize.toNat_inj.mp; simp]
      rfl
    · rw [if_neg hbf] at h ⊢
      rw [err_val h]
      exact ScanErrSim.mk (t := .expectedBool) rfl (by simp)

/-! ## The index list

`scan_fast.rs:1169-1221` against `Scan/Fast.lean:674-702` (`scanNatListLoop`,
`scanNatList`).  **This is the tier's list-loop template.**  The port pushes
onto a `Vec` where con-leche conses onto a `List` and reverses at the close, so
the invariant is `(absU64s acc).reverse` — the port's accumulator, abstracted
and reversed, is con-leche's — and the close is `List.reverse_reverse`. -/

/-- `scanNatListLoop` at a port position, unfolded once. -/
private theorem scanNatListLoop_eq (b : Slice Std.U8) (i : Std.Usize)
    (acc : List Nat) (w : Bool) :
    scanNatListLoop (absBytes b) (absPos i) acc w =
      if i.val < b.val.length then
        (if isWs (absByte (pByteAt b i.val)) then
            scanNatListLoop (absBytes b) (absPos i + 1) acc w
         else if absByte (pByteAt b i.val) == 93 then
            (if w && !acc.isEmpty then .err ⟨i.val, .expectedList⟩
             else .ok acc.reverse (absPos i + 1))
         else if absByte (pByteAt b i.val) == 44 then
            (if w then .err ⟨i.val, .expectedList⟩
             else scanNatListLoop (absBytes b) (absPos i + 1) acc true)
         else if isDigit (absByte (pByteAt b i.val)) then
            (if !w then .err ⟨i.val, .expectedList⟩
             else if numEnd (absBytes b) (absPos i) == absPos i then
               .err ⟨i.val, .expectedNat⟩
             else if _hj : absPos i < numEnd (absBytes b) (absPos i) then
               scanNatListLoop (absBytes b) (numEnd (absBytes b) (absPos i))
                 (readNatAt (absBytes b) (absPos i) (numEnd (absBytes b) (absPos i)) :: acc)
                 false
             else .err ⟨i.val, .noProgress⟩)
         else .err ⟨i.val, .expectedList⟩)
      else .err ⟨i.val, .expectedList⟩ := by
  rw [scanNatListLoop]
  by_cases h : i.val < b.val.length
  · rw [dif_pos (absPos_lt_usize.mpr h), if_pos h, uget_pos]
    simp only [absPos_toNat]
  · rw [dif_neg (fun hc => h (absPos_lt_usize.mp hc)), if_neg h]
    simp only [absPos_toNat]

/-- The loop of `scan_fast::scan_nat_list_loop` (con-leche:
`Scan/Fast.lean:674-698 scanNatListLoop`). -/
private theorem scan_nat_list_loop_aux {b : Slice Std.U8} (f : Nat) :
    ∀ (i : Std.Usize) (acc : alloc.vec.Vec Std.U64) (w : Bool)
      (o : core.result.Result (alloc.vec.Vec Std.U64 × Std.Usize)
             frontend.scan_types.ScanErr),
      b.val.length - i.val ≤ f →
      frontend.scan_fast.scan_nat_list_loop_loop b i acc w = ok o →
      ScanSim absU64s o
        (scanNatListLoop (absBytes b) (absPos i) (absU64s acc).reverse w) := by
  induction f with
  | zero =>
    intro i acc w o hf h
    have hi : ¬ i.val < b.val.length := by omega
    rw [frontend.scan_fast.scan_nat_list_loop_loop.eq_def,
      if_pos (show i ≥ Slice.len b by scalar_tac)] at h
    rw [err_val h, scanNatListLoop_eq, if_neg hi]
    exact ScanErrSim.mk (t := .expectedList) rfl (by simp)
  | succ f ih =>
    intro i acc w o hf h
    rw [frontend.scan_fast.scan_nat_list_loop_loop.eq_def] at h
    by_cases hi : i.val < b.val.length
    · rw [if_neg (show ¬ (i ≥ Slice.len b) by scalar_tac)] at h
      rw [scanNatListLoop_eq, if_pos hi]
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      have hcp : c = pByteAt b i.val := by
        rw [pByteAt, dif_pos hi]
        obtain ⟨y1, hy1, hy2⟩ := WP.spec_imp_exists (Slice.index_usize_spec b i hi)
        rw [hy1] at hc
        rw [← Result.ok_injective hc, hy2]
      rw [← hcp]
      obtain ⟨w1, hw1, h⟩ := bind_eq_ok_iff.mp h
      have hw1' : w1 = isWs (absByte c) := is_ws_refines hw1
      by_cases hws : w1 = true
      · rw [if_pos hws] at h
        rw [if_pos (by rw [← hw1']; exact hws)]
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v := usize_add_one_inv hi2
        rw [← absPos_add_one hi2]
        exact ih i2 acc w o (by omega) h
      · rw [if_neg hws] at h
        rw [if_neg (by rw [← hw1']; exact hws),
          show ((93 : UInt8)) = absByte 93#u8 from rfl, absByte_beq_u8]
        by_cases h93 : c = 93#u8
        · -- the closing bracket
          rw [if_pos h93] at h
          rw [if_pos (beq_iff_eq.mpr h93)]
          have hE : ((absU64s acc).reverse).isEmpty = decide (acc.val.length = 0) := by
            cases hv : acc.val with
            | nil => simp [absU64s, hv]
            | cons x xs => simp [absU64s, hv]
          have hlen : (alloc.vec.Vec.len acc).val = acc.val.length := by scalar_tac
          have hz0 : ((0#usize : Std.Usize)).val = 0 := by scalar_tac
          by_cases hw : w = true
          · rw [if_pos hw] at h
            simp only at h
            by_cases hne : (alloc.vec.Vec.len acc != 0#usize) = true
            · rw [if_pos hne] at h
              have hnz : acc.val.length ≠ 0 := by
                intro hx
                have h0 : alloc.vec.Vec.len acc ≠ 0#usize := by simpa using hne
                exact h0 (usize_ext (by omega))
              rw [if_pos (show (w && !((absU64s acc).reverse).isEmpty) = true by
                rw [hE, hw]; simp [hnz]), err_val h]
              exact ScanErrSim.mk (t := .expectedList) rfl (by simp)
            · rw [if_neg hne] at h
              have hzl : acc.val.length = 0 := by
                have h0 : acc.val = [] := by simpa using hne
                rw [h0, List.length_nil]
              rw [if_neg (show ¬ ((w && !((absU64s acc).reverse).isEmpty) = true) by
                rw [hE, hzl]; simp)]
              obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
              rw [← Result.ok_injective h]
              refine ScanSim.ok ?_
              rw [List.reverse_reverse, ← absPos_add_one hi3]
          · rw [if_neg hw] at h
            have hwf : w = false := by simpa using hw
            rw [if_neg (show ¬ ((w && !((absU64s acc).reverse).isEmpty) = true) by
              rw [hwf]; simp)]
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            rw [← Result.ok_injective h]
            refine ScanSim.ok ?_
            rw [List.reverse_reverse, ← absPos_add_one hi2]
        · rw [if_neg h93] at h
          rw [if_neg (by simp [h93]),
            show ((44 : UInt8)) = absByte 44#u8 from rfl, absByte_beq_u8]
          by_cases h44 : c = 44#u8
          · -- the comma
            rw [if_pos h44] at h
            rw [if_pos (beq_iff_eq.mpr h44)]
            by_cases hw : w = true
            · rw [if_pos hw] at h
              rw [if_pos hw, err_val h]
              exact ScanErrSim.mk (t := .expectedList) rfl (by simp)
            · rw [if_neg hw] at h
              rw [if_neg hw]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have hi2v := usize_add_one_inv hi2
              rw [← absPos_add_one hi2]
              exact ih i2 acc true o (by omega) h
          · rw [if_neg h44] at h
            rw [if_neg (by simp [h44])]
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            have hb2' : b2 = isDigit (absByte c) := is_digit_refines hb2
            by_cases hdg : b2 = true
            · -- a list member
              rw [if_pos hdg] at h
              rw [if_pos (by rw [← hb2']; exact hdg)]
              by_cases hw : w = true
              · rw [if_pos hw] at h
                rw [if_neg (by simp [hw])]
                obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
                have heA : absPos e = numEnd (absBytes b) (absPos i) := num_end_refines he
                rw [← heA]
                by_cases hei : e = i
                · rw [if_pos hei] at h
                  rw [if_pos (show (absPos e == absPos i) = true by simp; scalar_tac),
                    err_val h]
                  exact ScanErrSim.mk (t := .expectedNat) rfl (by simp)
                · rw [if_neg hei] at h
                  rw [if_neg (show ¬ ((absPos e == absPos i) = true) by
                    simp; intro hx; exact hei (usize_ext hx))]
                  obtain ⟨hrun, hlt⟩ := kit_num_end_run he hei
                  rw [dif_pos (absPos_lt.mpr hlt)]
                  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
                  cases r with
                  | Ok p =>
                    obtain ⟨acc1, hpush, h⟩ := bind_eq_ok_iff.mp h
                    have hpv := ConRon.Refine.vec_push_val hpush
                    rw [show readNatAt (absBytes b) (absPos i) (absPos e) = absU64 p from
                      (read_nat_at_refines hrun hr).symm]
                    have hacc : (absU64s acc1).reverse
                        = absU64 p :: (absU64s acc).reverse := by
                      simp [absU64s, hpv]
                    rw [← hacc]
                    exact ih e acc1 false o (by omega) h
                  | Err er =>
                    rw [← Result.ok_injective h]
                    exact read_nat_at_err hr
              · rw [if_neg hw] at h
                rw [if_pos (by simp [hw]), err_val h]
                exact ScanErrSim.mk (t := .expectedList) rfl (by simp)
            · rw [if_neg hdg] at h
              rw [if_neg (by rw [← hb2']; exact hdg), err_val h]
              exact ScanErrSim.mk (t := .expectedList) rfl (by simp)
    · rw [if_pos (show i ≥ Slice.len b by scalar_tac)] at h
      rw [err_val h, scanNatListLoop_eq, if_neg hi]
      exact ScanErrSim.mk (t := .expectedList) rfl (by simp)

/-- **`scan_nat_list_loop` refines `scanNatListLoop`** at the empty
accumulator (`Scan/Fast.lean:674-698`).  `scanPw` and every list-valued slot
of the tier enter here, past the `[`. -/
theorem scan_nat_list_loop_refines {b : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (alloc.vec.Vec Std.U64 × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_nat_list_loop b i = ok o) :
    ScanSim absU64s o (scanNatListLoop (absBytes b) (absPos i) [] true) := by
  have hr := scan_nat_list_loop_aux (b.val.length - i.val) i
    (alloc.vec.Vec.new Std.U64) true o (le_refl _) h
  simpa [absU64s, alloc.vec.Vec.new] using hr

/-- **`scan_nat_list` refines `scanNatList`** (`Scan/Fast.lean:700-702`). -/
theorem scan_nat_list_refines {b : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (alloc.vec.Vec Std.U64 × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_nat_list b i = ok o) :
    ScanSim absU64s o (scanNatList (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_nat_list] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  have hcA : absByte c = byteAt (absBytes b) (absPos i) := byte_at_refines hc
  rw [scanNatList, ← hcA, show ((91 : UInt8)) = absByte 91#u8 from rfl, absByte_beq_u8]
  by_cases h91 : c = 91#u8
  · rw [if_pos h91] at h
    rw [if_pos (beq_iff_eq.mpr h91)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    exact scan_nat_list_loop_refines h
  · rw [if_neg h91] at h
    rw [if_neg (by simp [h91]), err_val h]
    exact ScanErrSim.mk (t := .expectedList) rfl (by simp)

/-! ## `pw`

`scan_fast.rs:1226-1249` against `Scan/Fast.lean:707-715 scanPw`. -/

/-- **`scan_pw` refines `scanPw`** (`Scan/Fast.lean:707-715`). -/
theorem scan_pw_refines {b : Slice Std.U8} {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.PwRec × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_pw b i = ok o) :
    ScanSim absPwRec o (scanPw (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_pw] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  have hcA : absByte c = byteAt (absBytes b) (absPos i) := byte_at_refines hc
  rw [scanPw, ← hcA, show ((91 : UInt8)) = absByte 91#u8 from rfl,
    show ((34 : UInt8)) = absByte 34#u8 from rfl, absByte_beq_u8, absByte_beq_u8]
  by_cases h91 : c = 91#u8
  · rw [if_pos h91] at h
    rw [if_pos (beq_iff_eq.mpr h91)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    have hrs := scan_nat_list_loop_refines hr
    rw [← absPos_add_one hi2]
    cases r with
    | Ok p =>
      obtain ⟨ns, j⟩ := p
      rw [← Result.ok_injective h]
      rw [ScanSim] at hrs
      rw [hrs]
      rfl
    | Err er =>
      rw [← Result.ok_injective h]
      intro le hle
      rw [hrs le hle]
  · rw [if_neg h91] at h
    rw [if_neg (by simp [h91])]
    by_cases h34 : c = 34#u8
    · rw [if_pos h34] at h
      rw [if_pos (beq_iff_eq.mpr h34)]
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
      have hsv : s.val = [110#u8, 101#u8, 118#u8, 101#u8, 114#u8, 34#u8] := by
        rw [slice_lit_val hs]; simp [global_simps]
      have hsb : absBytes s = "never\"".toUTF8 := by rw [absBytes, hsv]; decide
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1' : b1 = matchLit (absBytes b) (absPos i2) "never\"".toUTF8 0 := by
        rw [← hsb]; exact match_lit_refines (by rw [hsv]; decide) hb1
      rw [← absPos_add_one hi2, ← hb1']
      by_cases hbt : b1 = true
      · rw [if_pos hbt] at h ⊢
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        rw [← Result.ok_injective h]
        refine ScanSim.ok ?_
        rw [absPos_add hi3, show absPos 7#usize = (7 : USize) from by
          apply USize.toNat_inj.mp; simp]
        rfl
      · rw [if_neg hbt] at h ⊢
        rw [err_val h]
        exact ScanErrSim.mk (t := .badPw) rfl (by simp)
    · rw [if_neg h34] at h
      rw [if_neg (by simp [h34]), err_val h]
      exact ScanErrSim.mk (t := .badPw) rfl (by simp)

/-! ## The slot loops' measure

`partial_fixpoint` gives the port's loops no induction principle, so every slot
loop is a strong induction on `b.len() - i`.  The two facts that make it drop
are phase 1's (`Refine/Frontend/ScanWF.lean`, where they are `private`): a
`next_member` that reported a key reported it at or after the cursor, and one
that returned `Ok` was inside the chunk. -/

/-- `scan_fast::next_member` only ever skips forward: the key it reports sits at
or after the cursor it was given. -/
theorem next_member_ge {b : Slice Std.U8} (f : Nat) :
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
        have h1 := usize_add_one_inv hi2
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
              have h1 := usize_add_one_inv hi2
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

/-- Past the end of the chunk `next_member` reports `ExpectedComma`, so a member
loop that got an `Ok` was still inside the chunk. -/
theorem next_member_lt {b : Slice Std.U8} {i : Std.Usize} {w : Bool}
    {x : frontend.scan_fast.Member × Std.Usize × Bool}
    (h : frontend.scan_fast.next_member b i w = ok (.Ok x)) : i.val < b.length := by
  by_contra hc
  rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
  rw [if_pos (show i ≥ Slice.len b by scalar_tac)] at h
  simp at h

/-- `scan_fast::prog` is `ks < e`, read forwards. -/
theorem prog_lt {ks e : Std.Usize} {c : Bool}
    (h : frontend.scan_fast.prog ks e = ok c) (hc : c = true) : ks.val < e.val := by
  rw [frontend.scan_fast.prog, Result.ok.injEq] at h
  rw [← h] at hc
  simp only [decide_eq_true_eq] at hc
  scalar_tac

/-- `scan_fast::slot_nat` closes with the module's `prog` guard, so a slot that
succeeded really consumed at least one byte. -/
theorem slot_nat_prog {b : Slice Std.U8} {ks v e : Std.Usize} {x : Std.U64}
    (h : frontend.scan_fast.slot_nat b ks v = ok (.Ok (x, e))) : ks.val < e.val := by
  rw [frontend.scan_fast.slot_nat] at h
  obtain ⟨e1, -, h⟩ := bind_eq_ok_iff.mp h
  by_cases h1 : e1 = v
  · rw [if_pos h1] at h; simp [frontend.scan_fast.err] at h
  · rw [if_neg h1] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    by_cases h2 : b1 = true
    · rw [if_pos h2] at h
      have hp := prog_lt hb1 h2
      obtain ⟨r, -, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err er => simp at h
      | Ok y =>
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact hp
    · rw [if_neg h2] at h; simp [frontend.scan_fast.err] at h

/-! ## The name-table records

`scan_fast.rs:1469-1605` against `Scan/Fast.lean:795-904`.  **These are the
tier's slot-loop template.**  Each is `memberBody` (above) at its own closing
arm and key dispatch; `nextMember_step` runs the port's factored
`scan_fast::next_member` against the skeleton, and the arms are the only work
left. -/

/-- con-leche's `scanNumNameLoop` closing arm (`Scan/Fast.lean:855-859`). -/
def numNameClose (pre n : Nat) (seen : UInt32) (p : USize) (w : Bool) : ScanRes NameRec :=
  if w && seen != 0 then .err ⟨p.toNat, .expectedKey⟩
  else if (seen &&& 3) != 3 then .err ⟨p.toNat, .missingKey⟩
  else .ok (.num pre n) (p + 1)

/-- con-leche's `scanNumNameLoop` key dispatch (`Scan/Fast.lean:869-895`). -/
def numNameKey (b : ByteArray) (seen : UInt32) (n pre : Nat)
    (k : Key) (ks v : USize) : ScanRes NameRec :=
  match k with
  | .kI =>
    if (seen &&& 1) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
    else natSlot b ks v (fun x e => scanNumNameLoop b e false (seen ||| 1) x pre)
  | .kPre =>
    if (seen &&& 2) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
    else natSlot b ks v (fun x e => scanNumNameLoop b e false (seen ||| 2) n x)
  | _ => .err ⟨ks.toNat, .unknownKey⟩

/-- **`scanNumNameLoop` is `memberBody`** at those two arms. -/
theorem numNameLoop_body (b : ByteArray) (seen : UInt32) (n pre : Nat)
    (p : USize) (w : Bool) :
    scanNumNameLoop b p w seen n pre
      = memberBody b (fun p w => scanNumNameLoop b p w seen n pre)
          (numNameClose pre n seen) (numNameKey b seen n pre) p w := by
  rw [scanNumNameLoop]
  rfl

/-- The loop of `scan_fast::scan_num_name_loop` (con-leche:
`Scan/Fast.lean:851-898 scanNumNameLoop`). -/
private theorem scan_num_name_loop_aux {b : Slice Std.U8} (kf : KitFacts b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (n pre : Std.U64)
      (o : core.result.Result (frontend.scan_types.NameRec × Std.Usize)
             frontend.scan_types.ScanErr),
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_num_name_loop_loop w b i seen n pre = ok o →
      ScanSim absNameRec o
        (scanNumNameLoop (absBytes b) (absPos i) w (absU32 seen) (absU64 n) (absU64 pre)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen n pre o hf h
    rw [frontend.scan_fast.scan_num_name_loop_loop.eq_def] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    have hstep := nextMember_step (b := b)
      (L := fun p w => scanNumNameLoop (absBytes b) p w (absU32 seen) (absU64 n) (absU64 pre))
      (CL := numNameClose (absU64 pre) (absU64 n) (absU32 seen))
      (DI := numNameKey (absBytes b) (absU32 seen) (absU64 n) (absU64 pre))
      kf (numNameLoop_body (absBytes b) (absU32 seen) (absU64 n) (absU64 pre))
      (b.length - i.val) i w r (le_refl _) hr
    have hz0 : ((0 : UInt32)) = absU32 0#u32 := rfl
    cases r with
    | Err er =>
      rw [← Result.ok_injective h]
      exact hstep
    | Ok p =>
      obtain ⟨mem, ni, nw⟩ := p
      have hilt := next_member_lt hr
      cases mem with
      | Close =>
        simp only [uncurry_apply_pair] at h
        have key : scanNumNameLoop (absBytes b) (absPos i) w (absU32 seen) (absU64 n)
              (absU64 pre)
            = numNameClose (absU64 pre) (absU64 n) (absU32 seen) (absPos ni) nw :=
          MemberStep.close hstep
        rw [key, numNameClose]
        have hseen0 : ((absU32 seen != 0)) = ((seen != 0#u32)) := by
          rw [hz0]; simp only [bne, absU32_beq]
        by_cases hnw : nw = true
        · rw [if_pos hnw] at h
          by_cases hzr : (seen != 0#u32) = true
          · rw [if_pos hzr] at h
            rw [if_pos (show (nw && (absU32 seen != 0)) = true by
              rw [hnw, hseen0, hzr]; rfl), err_val h]
            exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
          · rw [if_neg hzr] at h
            rw [if_neg (show ¬ ((nw && (absU32 seen != 0)) = true) by
              rw [hnw, hseen0]; simpa using hzr)]
            obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
            have hi1' : seen &&& 3#u32 = i1 := lift_val hi1
            have hmask : (((absU32 seen &&& 3) != 3)) = ((i1 != 3#u32)) := by
              rw [← hi1', show ((3 : UInt32)) = absU32 3#u32 from rfl, ← absU32_and]
              simp only [bne, absU32_beq]
            by_cases hm : (i1 != 3#u32) = true
            · rw [if_pos hm] at h
              rw [if_pos (show (((absU32 seen &&& 3) != 3)) = true by rw [hmask]; exact hm),
                err_val h]
              exact ScanErrSim.mk (t := .missingKey) rfl (by simp)
            · rw [if_neg hm] at h
              rw [if_neg (show ¬ ((((absU32 seen &&& 3) != 3)) = true) by
                rw [hmask]; exact hm)]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              rw [← Result.ok_injective h]
              refine ScanSim.ok ?_
              rw [← absPos_add_one hi2]
              rfl
        · rw [if_neg hnw] at h
          rw [if_neg (show ¬ ((nw && (absU32 seen != 0)) = true) by
            rw [show nw = false by simpa using hnw]; simp)]
          obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
          have hi1' : seen &&& 3#u32 = i1 := lift_val hi1
          have hmask : (((absU32 seen &&& 3) != 3)) = ((i1 != 3#u32)) := by
            rw [← hi1', show ((3 : UInt32)) = absU32 3#u32 from rfl, ← absU32_and]
            simp only [bne, absU32_beq]
          by_cases hm : (i1 != 3#u32) = true
          · rw [if_pos hm] at h
            rw [if_pos (show (((absU32 seen &&& 3) != 3)) = true by rw [hmask]; exact hm),
              err_val h]
            exact ScanErrSim.mk (t := .missingKey) rfl (by simp)
          · rw [if_neg hm] at h
            rw [if_neg (show ¬ ((((absU32 seen &&& 3) != 3)) = true) by
              rw [hmask]; exact hm)]
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            rw [← Result.ok_injective h]
            refine ScanSim.ok ?_
            rw [← absPos_add_one hi2]
            rfl
      | Key k ks v =>
        simp only [uncurry_apply_pair] at h
        have key : scanNumNameLoop (absBytes b) (absPos i) w (absU32 seen) (absU64 n)
              (absU64 pre)
            = numNameKey (absBytes b) (absU32 seen) (absU64 n) (absU64 pre)
                (absKey k) (absPos ks) (absPos v) :=
          MemberStep.key hstep
        rw [key]
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hr
        cases k
        case KI =>
          simp only [absKey, numNameKey]
          obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
          have hb1' : b1 = ((absU32 seen &&& absU32 1#u32) != 0) := dup_eq hb1
          by_cases hd : b1 = true
          · rw [if_pos hd] at h
            rw [if_pos (show ((absU32 seen &&& 1) != 0) = true by
              rw [show ((1 : UInt32)) = absU32 1#u32 from rfl, ← hb1']; exact hd), err_val h]
            exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
          · rw [if_neg hd] at h
            rw [if_neg (show ¬ (((absU32 seen &&& 1) != 0) = true) by
              rw [show ((1 : UInt32)) = absU32 1#u32 from rfl, ← hb1']; exact hd)]
            obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
            have hslot := natSlot_step (b := b) (ks := ks) (v := v)
              (K := fun (x : Nat) (e : USize) =>
                scanNumNameLoop (absBytes b) e false (absU32 seen ||| 1) x (absU64 pre)) hr1
            cases r1 with
            | Ok p1 =>
              obtain ⟨x, e⟩ := p1
              rw [NatSlotStep.ok hslot]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              have hs1 : absU32 seen1 = absU32 seen ||| 1 := by
                rw [← lift_val hseen1, absU32_or]
                rfl
              have hlt := slot_nat_prog hr1
              rw [← hs1]
              exact ih (b.length - e.val) (by omega) false e seen1 x pre o (le_refl _) h
            | Err er =>
              rw [← Result.ok_injective h]
              exact NatSlotStep.err hslot
        case KPre =>
          simp only [absKey, numNameKey]
          obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
          have hb1' : b1 = ((absU32 seen &&& absU32 2#u32) != 0) := dup_eq hb1
          by_cases hd : b1 = true
          · rw [if_pos hd] at h
            rw [if_pos (show ((absU32 seen &&& 2) != 0) = true by
              rw [show ((2 : UInt32)) = absU32 2#u32 from rfl, ← hb1']; exact hd), err_val h]
            exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
          · rw [if_neg hd] at h
            rw [if_neg (show ¬ (((absU32 seen &&& 2) != 0) = true) by
              rw [show ((2 : UInt32)) = absU32 2#u32 from rfl, ← hb1']; exact hd)]
            obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
            have hslot := natSlot_step (b := b) (ks := ks) (v := v)
              (K := fun (x : Nat) (e : USize) =>
                scanNumNameLoop (absBytes b) e false (absU32 seen ||| 2) (absU64 n) x) hr1
            cases r1 with
            | Ok p1 =>
              obtain ⟨x, e⟩ := p1
              rw [NatSlotStep.ok hslot]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              have hs1 : absU32 seen1 = absU32 seen ||| 2 := by
                rw [← lift_val hseen1, absU32_or]
                rfl
              have hlt := slot_nat_prog hr1
              rw [← hs1]
              exact ih (b.length - e.val) (by omega) false e seen1 n x o (le_refl _) h
            | Err er =>
              rw [← Result.ok_injective h]
              exact NatSlotStep.err hslot
        all_goals
          (simp only [absKey, numNameKey]
           rw [err_val h]
           exact ScanErrSim.mk (t := .unknownKey) rfl (by simp))

/-- **`scan_num_name_loop` refines `scanNumNameLoop`** at the empty state. -/
theorem scan_num_name_loop_refines {b : Slice Std.U8} (kf : KitFacts b) {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.NameRec × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_num_name_loop b i = ok o) :
    ScanSim absNameRec o (scanNumNameLoop (absBytes b) (absPos i) true 0 0 0) :=
  scan_num_name_loop_aux kf (b.length - i.val) true i 0#u32 0#u64 0#u64 o (le_refl _) h

/-- **`scan_num_name` refines `scanNumName`** (`Scan/Fast.lean:900-904`). -/
theorem scan_num_name_refines {b : Slice Std.U8} (kf : KitFacts b) {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.NameRec × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_num_name b i = ok o) :
    ScanSim absNameRec o (scanNumName (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_num_name] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  have hcA : absByte c = byteAt (absBytes b) (absPos i) := byte_at_refines hc
  rw [scanNumName, ← hcA, show ((123 : UInt8)) = absByte 123#u8 from rfl, absByte_beq_u8]
  by_cases h123 : c = 123#u8
  · rw [if_pos h123] at h
    rw [if_pos (beq_iff_eq.mpr h123)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    exact scan_num_name_loop_refines kf h
  · rw [if_neg h123] at h
    rw [if_neg (by simp [h123]), err_val h]
    exact ScanErrSim.mk (t := .expectedObject) rfl (by simp)

/-! ## A string-valued slot

`scan_string` followed by the module's `prog` guard, which is what every
string-valued slot of every `scan*Loop` writes out.  `ScanStr` does not have
`scan_string_refines` yet, so it is a named hypothesis here, the way `KitFacts`
is: discharge it the moment `Refine/Frontend/ScanStr.lean` has the lemma. -/

/-- **The one `ScanStr` fact the string-valued slots stand on.**
`scan_fast::scan_string` against `Scan/Fast.lean:617-638 scanString`. -/
def ScanStringFacts (b : Slice Std.U8) : Prop :=
  ∀ (v : Std.Usize) (o : core.result.Result (alloc.vec.Vec Std.U32 × Std.Usize)
      frontend.scan_types.ScanErr),
    frontend.scan_fast.scan_string b v = ok o →
      ScanSim absString o (scanString (absBytes b) (absPos v))

/-- con-leche's string-valued slot, with the continuation abstracted. -/
def strSlot {α : Type} (b : ByteArray) (ks v : USize)
    (K : String → USize → ScanRes α) : ScanRes α :=
  match scanString b v with
  | .err e => .err e
  | .ok x e => if _hj : ks < e then K x e else .err ⟨ks.toNat, .noProgress⟩

/-- `scan_fast::prog` refused, read forwards. -/
theorem prog_not_lt {ks e : Std.Usize} {c : Bool}
    (h : frontend.scan_fast.prog ks e = ok c) (hc : ¬ c = true) : ¬ ks.val < e.val := by
  rw [frontend.scan_fast.prog, Result.ok.injEq] at h
  rw [← h] at hc
  simp only [decide_eq_true_eq] at hc
  intro hx; exact hc (by scalar_tac)

/-- A string slot the port read and the `prog` guard accepted. -/
theorem strSlot_ok {α : Type} {b : Slice Std.U8} (hstr : ScanStringFacts b)
    {ks v e : Std.Usize} {x : alloc.vec.Vec Std.U32} {K : String → USize → ScanRes α}
    (h : frontend.scan_fast.scan_string b v = ok (.Ok (x, e))) (hlt : ks.val < e.val) :
    strSlot (absBytes b) (absPos ks) (absPos v) K = K (absString x) (absPos e) := by
  rw [strSlot, (hstr v _ h : scanString (absBytes b) (absPos v) = _)]
  exact dif_pos (absPos_lt.mpr hlt)

/-- A string slot the `prog` guard refused: `noProgress` on both sides. -/
theorem strSlot_noprog {α : Type} {b : Slice Std.U8} (hstr : ScanStringFacts b)
    {ks v e : Std.Usize} {x : alloc.vec.Vec Std.U32} {K : String → USize → ScanRes α}
    (h : frontend.scan_fast.scan_string b v = ok (.Ok (x, e))) (hlt : ¬ ks.val < e.val) :
    strSlot (absBytes b) (absPos ks) (absPos v) K
      = .err ⟨ks.val, .noProgress⟩ := by
  have h1 : strSlot (absBytes b) (absPos ks) (absPos v) K
      = .err ⟨(absPos ks).toNat, .noProgress⟩ := by
    rw [strSlot, (hstr v _ h : scanString (absBytes b) (absPos v) = _)]
    exact dif_neg (fun hc => hlt (absPos_lt.mp hc))
  rw [h1, absPos_toNat]

/-- A string slot the port failed on: con-leche fails at the same place. -/
theorem strSlot_err {α : Type} {b : Slice Std.U8} (hstr : ScanStringFacts b)
    {ks v : Std.Usize} {er : frontend.scan_types.ScanErr} {K : String → USize → ScanRes α}
    (h : frontend.scan_fast.scan_string b v = ok (.Err er)) :
    ScanErrSim er (strSlot (absBytes b) (absPos ks) (absPos v) K) := by
  intro le hle
  rw [strSlot, (hstr v _ h le hle : scanString (absBytes b) (absPos v) = _)]

/-- con-leche's `scanStrNameLoop` closing arm (`Scan/Fast.lean:799-803`). -/
def strNameClose (pre : Nat) (s : String) (seen : UInt32) (p : USize) (w : Bool) :
    ScanRes NameRec :=
  if w && seen != 0 then .err ⟨p.toNat, .expectedKey⟩
  else if (seen &&& 3) != 3 then .err ⟨p.toNat, .missingKey⟩
  else .ok (.str pre s) (p + 1)

/-- con-leche's `scanStrNameLoop` key dispatch (`Scan/Fast.lean:813-840`). -/
def strNameKey (b : ByteArray) (seen : UInt32) (pre : Nat) (s : String)
    (k : Key) (ks v : USize) : ScanRes NameRec :=
  match k with
  | .kPre =>
    if (seen &&& 1) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
    else natSlot b ks v (fun x e => scanStrNameLoop b e false (seen ||| 1) x s)
  | .kStr =>
    if (seen &&& 2) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
    else strSlot b ks v (fun x e => scanStrNameLoop b e false (seen ||| 2) pre x)
  | _ => .err ⟨ks.toNat, .unknownKey⟩

/-- **`scanStrNameLoop` is `memberBody`** at those two arms. -/
theorem strNameLoop_body (b : ByteArray) (seen : UInt32) (pre : Nat) (s : String)
    (p : USize) (w : Bool) :
    scanStrNameLoop b p w seen pre s
      = memberBody b (fun p w => scanStrNameLoop b p w seen pre s)
          (strNameClose pre s seen) (strNameKey b seen pre s) p w := by
  rw [scanStrNameLoop]
  rfl

/-- The loop of `scan_fast::scan_str_name_loop` (con-leche:
`Scan/Fast.lean:795-843 scanStrNameLoop`). -/
private theorem scan_str_name_loop_aux {b : Slice Std.U8} (kf : KitFacts b)
    (hstr : ScanStringFacts b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (pre : Std.U64)
      (s : alloc.vec.Vec Std.U32)
      (o : core.result.Result (frontend.scan_types.NameRec × Std.Usize)
             frontend.scan_types.ScanErr),
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_str_name_loop_loop w b i seen pre s = ok o →
      ScanSim absNameRec o
        (scanStrNameLoop (absBytes b) (absPos i) w (absU32 seen) (absU64 pre)
          (absString s)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen pre s o hf h
    rw [frontend.scan_fast.scan_str_name_loop_loop.eq_def] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    have hstep := nextMember_step (b := b)
      (L := fun p w => scanStrNameLoop (absBytes b) p w (absU32 seen) (absU64 pre)
        (absString s))
      (CL := strNameClose (absU64 pre) (absString s) (absU32 seen))
      (DI := strNameKey (absBytes b) (absU32 seen) (absU64 pre) (absString s))
      kf (strNameLoop_body (absBytes b) (absU32 seen) (absU64 pre) (absString s))
      (b.length - i.val) i w r (le_refl _) hr
    have hz0 : ((0 : UInt32)) = absU32 0#u32 := rfl
    cases r with
    | Err er =>
      rw [← Result.ok_injective h]
      exact hstep
    | Ok p =>
      obtain ⟨mem, ni, nw⟩ := p
      have hilt := next_member_lt hr
      cases mem with
      | Close =>
        simp only [uncurry_apply_pair] at h
        have key : scanStrNameLoop (absBytes b) (absPos i) w (absU32 seen) (absU64 pre)
              (absString s)
            = strNameClose (absU64 pre) (absString s) (absU32 seen) (absPos ni) nw :=
          MemberStep.close hstep
        rw [key, strNameClose]
        have hseen0 : ((absU32 seen != 0)) = ((seen != 0#u32)) := by
          rw [hz0]; simp only [bne, absU32_beq]
        by_cases hnw : nw = true
        · rw [if_pos hnw] at h
          by_cases hzr : (seen != 0#u32) = true
          · rw [if_pos hzr] at h
            rw [if_pos (show (nw && (absU32 seen != 0)) = true by
              rw [hnw, hseen0, hzr]; rfl), err_val h]
            exact ScanErrSim.mk (t := .expectedKey) rfl (by simp)
          · rw [if_neg hzr] at h
            rw [if_neg (show ¬ ((nw && (absU32 seen != 0)) = true) by
              rw [hnw, hseen0]; simpa using hzr)]
            obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
            have hi1' : seen &&& 3#u32 = i1 := lift_val hi1
            have hmask : (((absU32 seen &&& 3) != 3)) = ((i1 != 3#u32)) := by
              rw [← hi1', show ((3 : UInt32)) = absU32 3#u32 from rfl, ← absU32_and]
              simp only [bne, absU32_beq]
            by_cases hm : (i1 != 3#u32) = true
            · rw [if_pos hm] at h
              rw [if_pos (show (((absU32 seen &&& 3) != 3)) = true by rw [hmask]; exact hm),
                err_val h]
              exact ScanErrSim.mk (t := .missingKey) rfl (by simp)
            · rw [if_neg hm] at h
              rw [if_neg (show ¬ ((((absU32 seen &&& 3) != 3)) = true) by
                rw [hmask]; exact hm)]
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              rw [← Result.ok_injective h]
              refine ScanSim.ok ?_
              rw [← absPos_add_one hi2]
              rfl
        · rw [if_neg hnw] at h
          rw [if_neg (show ¬ ((nw && (absU32 seen != 0)) = true) by
            rw [show nw = false by simpa using hnw]; simp)]
          obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
          have hi1' : seen &&& 3#u32 = i1 := lift_val hi1
          have hmask : (((absU32 seen &&& 3) != 3)) = ((i1 != 3#u32)) := by
            rw [← hi1', show ((3 : UInt32)) = absU32 3#u32 from rfl, ← absU32_and]
            simp only [bne, absU32_beq]
          by_cases hm : (i1 != 3#u32) = true
          · rw [if_pos hm] at h
            rw [if_pos (show (((absU32 seen &&& 3) != 3)) = true by rw [hmask]; exact hm),
              err_val h]
            exact ScanErrSim.mk (t := .missingKey) rfl (by simp)
          · rw [if_neg hm] at h
            rw [if_neg (show ¬ ((((absU32 seen &&& 3) != 3)) = true) by
              rw [hmask]; exact hm)]
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            rw [← Result.ok_injective h]
            refine ScanSim.ok ?_
            rw [← absPos_add_one hi2]
            rfl
      | Key k ks v =>
        simp only [uncurry_apply_pair] at h
        have key : scanStrNameLoop (absBytes b) (absPos i) w (absU32 seen) (absU64 pre)
              (absString s)
            = strNameKey (absBytes b) (absU32 seen) (absU64 pre) (absString s)
                (absKey k) (absPos ks) (absPos v) :=
          MemberStep.key hstep
        rw [key]
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hr
        cases k
        case KPre =>
          simp only [absKey, strNameKey]
          obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
          have hb1' : b1 = ((absU32 seen &&& absU32 1#u32) != 0) := dup_eq hb1
          by_cases hd : b1 = true
          · rw [if_pos hd] at h
            rw [if_pos (show ((absU32 seen &&& 1) != 0) = true by
              rw [show ((1 : UInt32)) = absU32 1#u32 from rfl, ← hb1']; exact hd), err_val h]
            exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
          · rw [if_neg hd] at h
            rw [if_neg (show ¬ (((absU32 seen &&& 1) != 0) = true) by
              rw [show ((1 : UInt32)) = absU32 1#u32 from rfl, ← hb1']; exact hd)]
            obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
            have hslot := natSlot_step (b := b) (ks := ks) (v := v)
              (K := fun (x : Nat) (e : USize) =>
                scanStrNameLoop (absBytes b) e false (absU32 seen ||| 1) x (absString s)) hr1
            cases r1 with
            | Ok p1 =>
              obtain ⟨x, e⟩ := p1
              rw [NatSlotStep.ok hslot]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              have hs1 : absU32 seen1 = absU32 seen ||| 1 := by
                rw [← lift_val hseen1, absU32_or]
                rfl
              have hlt := slot_nat_prog hr1
              rw [← hs1]
              exact ih (b.length - e.val) (by omega) false e seen1 x s o (le_refl _) h
            | Err er =>
              rw [← Result.ok_injective h]
              exact NatSlotStep.err hslot
        case KStr =>
          simp only [absKey, strNameKey]
          obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
          have hb1' : b1 = ((absU32 seen &&& absU32 2#u32) != 0) := dup_eq hb1
          by_cases hd : b1 = true
          · rw [if_pos hd] at h
            rw [if_pos (show ((absU32 seen &&& 2) != 0) = true by
              rw [show ((2 : UInt32)) = absU32 2#u32 from rfl, ← hb1']; exact hd), err_val h]
            exact ScanErrSim.mk (t := .duplicateKey) rfl (by simp)
          · rw [if_neg hd] at h
            rw [if_neg (show ¬ (((absU32 seen &&& 2) != 0) = true) by
              rw [show ((2 : UInt32)) = absU32 2#u32 from rfl, ← hb1']; exact hd)]
            obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
            cases r1 with
            | Ok p1 =>
              obtain ⟨x, e⟩ := p1
              obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
              by_cases hp : b2 = true
              · rw [if_pos hp] at h
                have hlt := prog_lt hb2 hp
                rw [strSlot_ok hstr hr1 hlt]
                obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
                have hs1 : absU32 seen1 = absU32 seen ||| 2 := by
                  rw [← lift_val hseen1, absU32_or]
                  rfl
                rw [← hs1]
                exact ih (b.length - e.val) (by omega) false e seen1 pre x o (le_refl _) h
              · rw [if_neg hp] at h
                rw [strSlot_noprog hstr hr1 (prog_not_lt hb2 hp), err_val h]
                exact ScanErrSim.mk (t := .noProgress) rfl (by simp)
            | Err er =>
              rw [← Result.ok_injective h]
              exact strSlot_err hstr hr1
        all_goals
          (simp only [absKey, strNameKey]
           rw [err_val h]
           exact ScanErrSim.mk (t := .unknownKey) rfl (by simp))

/-- **`scan_str_name_loop` refines `scanStrNameLoop`** at the empty state. -/
theorem scan_str_name_loop_refines {b : Slice Std.U8} (kf : KitFacts b)
    (hstr : ScanStringFacts b) {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.NameRec × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_str_name_loop b i = ok o) :
    ScanSim absNameRec o (scanStrNameLoop (absBytes b) (absPos i) true 0 0 "") := by
  have hr := scan_str_name_loop_aux kf hstr (b.length - i.val) true i 0#u32 0#u64
    (alloc.vec.Vec.new Std.U32) o (le_refl _) h
  simpa [absString, alloc.vec.Vec.new, show absU32 0#u32 = 0 from rfl] using hr

/-- **`scan_str_name` refines `scanStrName`** (`Scan/Fast.lean:845-849`). -/
theorem scan_str_name_refines {b : Slice Std.U8} (kf : KitFacts b)
    (hstr : ScanStringFacts b) {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.NameRec × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_str_name b i = ok o) :
    ScanSim absNameRec o (scanStrName (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_str_name] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  have hcA : absByte c = byteAt (absBytes b) (absPos i) := byte_at_refines hc
  rw [scanStrName, ← hcA, show ((123 : UInt8)) = absByte 123#u8 from rfl, absByte_beq_u8]
  by_cases h123 : c = 123#u8
  · rw [if_pos h123] at h
    rw [if_pos (beq_iff_eq.mpr h123)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← absPos_add_one hi2]
    exact scan_str_name_loop_refines kf hstr h
  · rw [if_neg h123] at h
    rw [if_neg (by simp [h123]), err_val h]
    exact ScanErrSim.mk (t := .expectedObject) rfl (by simp)

/-! ## A definition's `hints`

`scan_fast.rs:1254-1301` against `Scan/Fast.lean:717-742 scanHints`: the one
object of the dialect whose key dispatch is *not* a slot loop — a single key,
read inline. -/

/-- **`scan_hints` refines `scanHints`** (`Scan/Fast.lean:717-742`). -/
theorem scan_hints_refines {b : Slice Std.U8} (kf : KitFacts b) {i : Std.Usize}
    {o : core.result.Result (frontend.scan_types.HintsRec × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.scan_hints b i = ok o) :
    ScanSim absHintsRec o (scanHints (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_hints] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  have hcA : absByte c = byteAt (absBytes b) (absPos i) := byte_at_refines hc
  have hcond34 : (byteAt (absBytes b) (absPos i) == 34) = (c == 34#u8) := by
    rw [← hcA, show ((34 : UInt8)) = absByte 34#u8 from rfl]; exact absByte_beq_u8 c 34#u8
  have hcond123 : (byteAt (absBytes b) (absPos i) == 123) = (c == 123#u8) := by
    rw [← hcA, show ((123 : UInt8)) = absByte 123#u8 from rfl]; exact absByte_beq_u8 c 123#u8
  rw [scanHints, hcond34, hcond123]
  by_cases h34 : c = 34#u8
  · rw [if_pos h34] at h
    rw [if_pos (beq_iff_eq.mpr h34)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
    have hsv : s.val = [97#u8, 98#u8, 98#u8, 114#u8, 101#u8, 118#u8, 34#u8] := by
      rw [slice_lit_val hs]; simp [global_simps]
    have hsb : absBytes s = "abbrev\"".toUTF8 := by rw [absBytes, hsv]; decide
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1' : b1 = matchLit (absBytes b) (absPos i2) "abbrev\"".toUTF8 0 := by
      rw [← hsb]; exact match_lit_refines (by rw [hsv]; decide) hb1
    rw [← absPos_add_one hi2, ← hb1']
    by_cases hbt : b1 = true
    · rw [if_pos hbt] at h ⊢
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h]
      refine ScanSim.ok ?_
      rw [absPos_add hi3, show absPos 8#usize = (8 : USize) from by
        apply USize.toNat_inj.mp; simp]
      rfl
    · rw [if_neg hbt] at h ⊢
      obtain ⟨s1, hs1, h⟩ := bind_eq_ok_iff.mp h
      have hs1v : s1.val = [111#u8, 112#u8, 97#u8, 113#u8, 117#u8, 101#u8, 34#u8] := by
        rw [slice_lit_val hs1]; simp [global_simps]
      have hs1b : absBytes s1 = "opaque\"".toUTF8 := by rw [absBytes, hs1v]; decide
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2' : b2 = matchLit (absBytes b) (absPos i2) "opaque\"".toUTF8 0 := by
        rw [← hs1b]; exact match_lit_refines (by rw [hs1v]; decide) hb2
      rw [← hb2']
      by_cases hbo : b2 = true
      · rw [if_pos hbo] at h ⊢
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        rw [← Result.ok_injective h]
        refine ScanSim.ok ?_
        rw [absPos_add hi3, show absPos 8#usize = (8 : USize) from by
          apply USize.toNat_inj.mp; simp]
        rfl
      · rw [if_neg hbo] at h ⊢
        rw [err_val h]
        exact ScanErrSim.mk (t := .badHints) rfl (by simp)
  · rw [if_neg h34] at h
    rw [if_neg (by simp [h34])]
    by_cases h123 : c = 123#u8
    · rw [if_pos h123] at h
      rw [if_pos (beq_iff_eq.mpr h123)]
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      have hpA : skipWs (absBytes b) (absPos i + 1) = absPos p := by
        rw [← absPos_add_one hi2]; exact (skip_ws_refines hp).symm
      simp only [hpA]
      obtain ⟨c3, hc3, h⟩ := bind_eq_ok_iff.mp h
      have hc3A : absByte c3 = byteAt (absBytes b) (absPos p) := byte_at_refines hc3
      have hcondq : (byteAt (absBytes b) (absPos p) != 34) = (c3 != 34#u8) := by
        rw [← hc3A, show ((34 : UInt8)) = absByte 34#u8 from rfl]
        simp only [bne, absByte_beq_u8]
      rw [hcondq]
      by_cases hq : (c3 != 34#u8) = true
      · rw [if_pos hq] at h
        rw [if_pos hq, err_val h]
        exact ScanErrSim.mk (t := .badHints) rfl (by simp)
      · rw [if_neg hq] at h
        rw [if_neg hq]
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ke, hke, h⟩ := bind_eq_ok_iff.mp h
        have hkeA : keyEnd (absBytes b) (absPos p + 1) = absPos ke := by
          rw [← absPos_add_one hi4]; exact kf.key_end i4 ke hke
        simp only [hkeA]
        by_cases hz : ke = 0#usize
        · rw [if_pos hz] at h
          rw [if_pos (show (absPos ke == (0 : USize)) = true by simp; scalar_tac), err_val h]
          exact ScanErrSim.mk (t := .badHints) rfl (by simp)
        · rw [if_neg hz] at h
          rw [if_neg (show ¬ ((absPos ke == (0 : USize)) = true) by
            simp; intro hx; exact hz (usize_ext (by simpa using hx)))]
          obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
          have hkA : keyAt (absBytes b) (absPos p) (absPos ke - (absPos p + 1)) = absKey k := by
            rw [← absPos_add_one hi4, ← absPos_sub hi5]
            exact kf.key_at p i5 k hk
          simp only [hkA]
          cases k
          case KRegular =>
            simp only [absKey]
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            have hvA : valueAt (absBytes b) (absPos p) (absPos ke) = absPos v :=
              (value_at_refines hv).symm
            simp only [hvA]
            by_cases hvp : v = p
            · rw [if_pos hvp] at h
              rw [if_pos (show (absPos v == absPos p) = true by simp; scalar_tac), err_val h]
              exact ScanErrSim.mk (t := .expectedColon) rfl (by simp)
            · rw [if_neg hvp] at h
              rw [if_neg (show ¬ ((absPos v == absPos p) = true) by
                simp; intro hx; exact hvp (usize_ext hx))]
              obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
              have heA : numEnd (absBytes b) (absPos v) = absPos e := (num_end_refines he).symm
              simp only [heA]
              by_cases hev : e = v
              · rw [if_pos hev] at h
                rw [if_pos (show (absPos e == absPos v) = true by simp; scalar_tac), err_val h]
                exact ScanErrSim.mk (t := .expectedNat) rfl (by simp)
              · rw [if_neg hev] at h
                rw [if_neg (show ¬ ((absPos e == absPos v) = true) by
                  simp; intro hx; exact hev (usize_ext hx))]
                obtain ⟨hrun, -⟩ := kit_num_end_run he hev
                obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
                cases r with
                | Err er =>
                  rw [← Result.ok_injective h]
                  exact read_nat_at_err hr
                | Ok x =>
                  obtain ⟨q, hqs, h⟩ := bind_eq_ok_iff.mp h
                  have hqA : skipWs (absBytes b) (absPos e) = absPos q :=
                    (skip_ws_refines hqs).symm
                  simp only [hqA]
                  obtain ⟨c6, hc6, h⟩ := bind_eq_ok_iff.mp h
                  have hc6A : absByte c6 = byteAt (absBytes b) (absPos q) := byte_at_refines hc6
                  have hcond125 : (byteAt (absBytes b) (absPos q) == 125) = (c6 == 125#u8) := by
                    rw [← hc6A, show ((125 : UInt8)) = absByte 125#u8 from rfl]
                    exact absByte_beq_u8 c6 125#u8
                  rw [hcond125]
                  by_cases h125 : c6 = 125#u8
                  · rw [if_pos h125] at h
                    rw [if_pos (beq_iff_eq.mpr h125)]
                    obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
                    rw [← Result.ok_injective h]
                    refine ScanSim.ok ?_
                    rw [← absPos_add_one hi7, ← read_nat_at_refines hrun hr]
                    rfl
                  · rw [if_neg h125] at h
                    rw [if_neg (by simp [h125]), err_val h]
                    exact ScanErrSim.mk (t := .expectedComma) rfl (by simp)
          all_goals
            (simp only [absKey]
             rw [err_val h]
             exact ScanErrSim.mk (t := .badHints) rfl (by simp))
    · rw [if_neg h123] at h
      rw [if_neg (by simp [h123]), err_val h]
      exact ScanErrSim.mk (t := .badHints) rfl (by simp)

/-! ## The file's products are axiom-free

`ScanStringFacts` is a *hypothesis* of the two `scan_str_name` lemmas, not an
axiom: nothing below leans on anything but `propext`, `Classical.choice` and
`Quot.sound`. -/

/-- info: 'ConRon.Refine2.Frontend.scan_nat_list_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_nat_list_refines

/-- info: 'ConRon.Refine2.Frontend.scan_pw_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_pw_refines

/-- info: 'ConRon.Refine2.Frontend.scan_hints_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_hints_refines

/-- info: 'ConRon.Refine2.Frontend.scan_num_name_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_num_name_refines

/-- info: 'ConRon.Refine2.Frontend.scan_str_name_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_str_name_refines

end ConRon.Refine2.Frontend
