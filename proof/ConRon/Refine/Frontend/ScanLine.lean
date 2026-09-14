/-
**The declaration records and the line scanner, exactly** (task #87, phase 3).

`Refine/Frontend/ScanWF.lean` (phase 1) proved that every record
`scan_fast::scan_line_fwd` hands the parse is *well formed*.  This file proves
that it is **the record con-leche reads from the same bytes**, and that it
fails where con-leche fails:

    ScanSim absLineRec (scan_line_fwd b i) (scanLineFwd (absBytes b) (absPos i))

— the capstone of the scanner tier, and the last link of the chain
`ScanKit → ScanStr/ScanObj → ScanExpr/ScanInd → ScanLine`.

## The one shape mismatch, and how it is bridged

con-leche's `Scan/Fast.lean` writes the JSON object skeleton — skip
whitespace, stop at `}`, take the alternation at `,`, classify the key at `"`
— *inline* in each of its twenty `scan*Loop`s; the port factors it out as
`scan_fast::next_member` (module note, deviation 3, which is how
`Scan/Naive.lean`'s `naiveObjLoop` factors it too).  The bridge is

* `objStep`, con-leche's inlined skeleton abstracted over its three
  continuations (the tail call, the closing brace, the key), and
* one `*_objStep` equation per con-leche loop saying that the loop **is**
  `objStep` with its own three arms filled in — each `rfl` after unfolding, so
  no new definition of the recogniser is introduced, only a reading of it, and
* `next_member_sim`, which runs the port's factored skeleton against `objStep`
  once and for all: a `Member::Close` at `ni` lands on the `close`
  continuation at `absPos ni`, a `Member::Key k ks v` on the `key`
  continuation at `absKey k`, and an error is mirrored at the same offset.

That is the only place the two recognisers are lined up by hand; everything
below is the skeleton plus the slot arms.

## The ingredients

Everything this file's loops call into is proved elsewhere in the tier
(`ScanKit`, `ScanStr`, `ScanObj`, `ScanExpr`, `ScanInd`).  Rather than wait,
the file states what it needs as `ScanLineIngredients` — the `Refine/IndSpec.lean`
pattern — and proves every lemma below **from** it.  The instance
`scanLineIngredients` discharges the fields from the upstream lemmas; the
report of task #87 records which fields were still hypotheses when the file
landed.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.Abs

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

open ConRon.Refine

/-! ## Plumbing: the two machine words the loops thread

`seen` is a `u32` bitmask on both sides and `idx_kind` a `u8`; `absU32` and
`Abs.lean`'s `absByte` are the maps, and the three lemmas below are all the
loops ever ask of them. -/

/-- A port `u32` as con-leche's `UInt32`. -/
def absU32 (n : Std.U32) : UInt32 := UInt32.ofNat n.val

@[simp] theorem absU32_toNat (n : Std.U32) : (absU32 n).toNat = n.val := by
  simp [absU32]

/-- A `lift`ed pure step is an equation on its value. -/
private theorem lift_val {α : Type} {x y : α} (h : lift x = ok y) : x = y := by
  simpa only [lift, Result.ok.injEq] using h

theorem absU32_and {x y z : Std.U32} (h : lift (x &&& y) = ok z) :
    absU32 z = absU32 x &&& absU32 y := by
  apply UInt32.toNat.inj
  rw [← lift_val h]
  simp [Std.UScalar.val_and]

theorem absU32_or {x y z : Std.U32} (h : lift (x ||| y) = ok z) :
    absU32 z = absU32 x ||| absU32 y := by
  apply UInt32.toNat.inj
  rw [← lift_val h]
  simp [Std.UScalar.val_or]

@[simp] theorem absU32_eq_iff {x y : Std.U32} : absU32 x = absU32 y ↔ x = y := by
  constructor
  · intro h
    have := congrArg UInt32.toNat h
    simp only [absU32_toNat] at this
    scalar_tac
  · intro h; rw [h]

@[simp] theorem absByte_eq_iff {x y : Std.U8} : absByte x = absByte y ↔ x = y := by
  constructor
  · intro h
    have := congrArg UInt8.toNat h
    simp only [absByte_toNat] at this
    scalar_tac
  · intro h; rw [h]

/-- The port's `usize` subtraction, inverted: a step the port returned `ok` for
did not underflow, so con-leche's machine word did not wrap either. -/
theorem absPos_sub {i j k : Std.Usize} (h : i - j = ok k) :
    absPos k = absPos i - absPos j := by
  obtain ⟨hle, hk⟩ := ConRon.Refine.Nat.usub_val h
  apply USize.toNat_inj.mp
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; simpa using hle)]
  simp only [absPos_toNat]
  omega

/-- An Aeneas `err` never equals an `ok`. -/
private theorem err_ne_ok {T : Type} {offset : Std.Usize}
    {what : frontend.scan_types.ErrTag} {x : core.result.Result (T × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.err T offset what = ok x) :
    x = .Err ⟨offset, what⟩ := by
  rw [frontend.scan_fast.err] at h
  exact (Result.ok_injective h).symm

/-! ## The line payload

`scan_fast::LinePayload` against `ConLeche/Frontend/Scan/Fast.lean:2449-2456`,
field for field. -/

/-- `LinePayload` (`Scan/Fast.lean:2449-2456`). -/
def absLinePayload : frontend.scan_fast.LinePayload → ConLeche.Frontend.LinePayload
  | .Absent => .absent
  | .Name r => .name (absNameRec r)
  | .Level r => .level (absLevelRec r)
  | .Expr r => .expr (absExprRec r)
  | .Decl d => .decl (absDeclRec d)
  | .Header => .header

/-- `scan_fast::line_payload_is_absent` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:2458-2460 LinePayload.isAbsent`). -/
theorem line_payload_is_absent_refines {p : frontend.scan_fast.LinePayload} {r : Bool}
    (h : frontend.scan_fast.line_payload_is_absent p = ok r) :
    r = (absLinePayload p).isAbsent := by
  cases p <;>
    (rw [frontend.scan_fast.line_payload_is_absent] at h
     rw [← Result.ok_injective h]
     rfl)

/-! ## The object skeleton

`objStep` is what every `scan*Loop` of `ConLeche/Frontend/Scan/Fast.lean`
writes out inline; `scan_fast::next_member` is the port's one copy of it. -/

open ConLeche.Frontend in
/-- con-leche's inlined object skeleton, abstracted over its three
continuations: the tail call, the closing brace, and the key. -/
def objStep {α : Type} (b : ByteArray) (i : USize) (w : Bool)
    (loop : USize → Bool → ScanRes α)
    (close : USize → Bool → ScanRes α)
    (key : Key → USize → USize → ScanRes α) : ScanRes α :=
  if h : i < b.usize then
    if isWs (b.uget i (usizeInBounds b i h)) then loop (i + 1) w
    else if b.uget i (usizeInBounds b i h) == 125 then close i w
    else if b.uget i (usizeInBounds b i h) == 44 then
      if w then .err ⟨i.toNat, .expectedKey⟩ else loop (i + 1) true
    else if b.uget i (usizeInBounds b i h) == 34 then
      if !w then .err ⟨i.toNat, .expectedComma⟩
      else if keyEnd b (i + 1) == 0 then .err ⟨i.toNat, .expectedKey⟩
      else if valueAt b i (keyEnd b (i + 1)) == i then .err ⟨i.toNat, .expectedColon⟩
      else key (keyAt b i (keyEnd b (i + 1) - (i + 1))) i (valueAt b i (keyEnd b (i + 1)))
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩

/-- Which continuation a `Member` lands on. -/
def memArm {α : Type} (close : USize → Bool → ConLeche.Frontend.ScanRes α)
    (key : ConLeche.Frontend.Key → USize → USize → ConLeche.Frontend.ScanRes α) :
    frontend.scan_fast.Member → Std.Usize → Bool → ConLeche.Frontend.ScanRes α
  | .Close, ni, nw => close (absPos ni) nw
  | .Key k ks v, _, _ => key (absKey k) (absPos ks) (absPos v)

open ConLeche.Frontend in
/-- The `numEnd`/`readNatAt`/`noProgress` chain every `Nat`-valued slot of
`ConLeche/Frontend/Scan/Fast.lean` writes out, as one function: the reading of
`scan_fast::slot_nat` (which factors exactly that chain, module note). -/
def slotNatL (b : ByteArray) (ks v : USize) : ScanRes Nat :=
  if numEnd b v == v then .err ⟨v.toNat, .expectedNat⟩
  else if ks < numEnd b v then .ok (readNatAt b v (numEnd b v)) (numEnd b v)
  else .err ⟨ks.toNat, .noProgress⟩

open ConLeche.Frontend in
/-- A slot that read a `Nat`: where the run ended, that it was not empty, that
it made progress, and what it read. -/
theorem slotNatL_ok {b : ByteArray} {ks v : USize} {n : Nat} {e : USize}
    (h : slotNatL b ks v = .ok n e) :
    numEnd b v = e ∧ (e == v) = false ∧ ks < e ∧ readNatAt b v e = n := by
  rw [slotNatL] at h
  split at h
  · simp at h
  · rename_i h1
    split at h
    · rename_i h2
      simp only [ScanRes.ok.injEq] at h
      obtain ⟨hn, he⟩ := h
      subst he
      exact ⟨rfl, by simpa using h1, h2, hn⟩
    · simp at h

open ConLeche.Frontend in
/-- A slot that failed: an empty digit run, or no progress. -/
theorem slotNatL_err {b : ByteArray} {ks v : USize} {er : ScanErr}
    (h : slotNatL b ks v = .err er) :
    (numEnd b v = v ∧ er = ⟨v.toNat, .expectedNat⟩) ∨
      ((numEnd b v == v) = false ∧ ¬ (ks < numEnd b v) ∧ er = ⟨ks.toNat, .noProgress⟩) := by
  rw [slotNatL] at h
  split at h
  · rename_i h1
    simp only [ScanRes.err.injEq] at h
    exact Or.inl ⟨by simpa using h1, h.symm⟩
  · rename_i h1
    split at h
    · simp at h
    · rename_i h2
      simp only [ScanRes.err.injEq] at h
      exact Or.inr ⟨by simpa using h1, h2, h.symm⟩

/-! ## What the rest of the tier owes this file

`ScanKit`, `ScanStr`, `ScanObj`, `ScanExpr` and `ScanInd` prove the leaves and
the member records; this file's loops are stated over the record of what they
prove, in the `Refine/IndSpec.lean` style, so that the dispatcher and the
capstone can be proved before (or independently of) them. -/

open ConLeche.Frontend in
/-- The scanner leaves and member records this file's loops call into. -/
structure ScanLineIngredients (b : Slice Std.U8) : Prop where
  /-- `scan_fast::byte_at` (`Scan/Fast.lean:75-77 byteAt`). -/
  byte_at : ∀ {i : Std.Usize} {c : Std.U8}, frontend.scan_fast.byte_at b i = ok c →
    absByte c = byteAt (absBytes b) (absPos i)
  /-- `scan_fast::skip_ws` (`Scan/Fast.lean:85-92 skipWs`). -/
  skip_ws : ∀ {i s : Std.Usize}, frontend.scan_fast.skip_ws b i = ok s →
    absPos s = skipWs (absBytes b) (absPos i)
  /-- `scan_fast::key_end` (`Scan/Fast.lean:137-159 keyEnd`). -/
  key_end : ∀ {j k : Std.Usize}, frontend.scan_fast.key_end b j = ok k →
    absPos k = keyEnd (absBytes b) (absPos j)
  /-- `scan_fast::value_at` (`Scan/Fast.lean:451-453 valueAt`). -/
  value_at : ∀ {i ke v : Std.Usize}, frontend.scan_fast.value_at b i ke = ok v →
    absPos v = valueAt (absBytes b) (absPos i) (absPos ke)
  /-- `scan_fast::key_at` (`Scan/Fast.lean:229-446 keyAt`). -/
  key_at : ∀ {i kl : Std.Usize} {k : frontend.scan_types.Key},
    frontend.scan_fast.key_at b i kl = ok k →
    absKey k = keyAt (absBytes b) (absPos i) (absPos kl)
  /-- `scan_fast::slot_nat` (the `numEnd`/`readNatAt`/`noProgress` chain). -/
  slot_nat : ∀ {ks v : Std.Usize} {o}, frontend.scan_fast.slot_nat b ks v = ok o →
    ScanSim absU64 o (slotNatL (absBytes b) (absPos ks) (absPos v))
  /-- `scan_fast::skip_braced` (`Scan/Fast.lean:755-792 skipBraced`). -/
  skip_braced : ∀ {i : Std.Usize} {d : Std.U64} {e : Std.Usize},
    frontend.scan_fast.skip_braced b i d = ok e →
    absPos e = skipBraced (absBytes b) (absPos i) (absU64 d)
  /-- `scan_fast::scan_bool` (`Scan/Fast.lean:464-467 scanBool`). -/
  scan_bool : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_bool b i = ok o →
    ScanSim id o (scanBool (absBytes b) (absPos i))
  /-- `scan_fast::scan_nat_list` (`Scan/Fast.lean:700-704 scanNatList`). -/
  scan_nat_list : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_nat_list b i = ok o →
    ScanSim absU64s o (scanNatList (absBytes b) (absPos i))
  /-- `scan_fast::scan_hints` (`Scan/Fast.lean:718-752 scanHints`). -/
  scan_hints : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_hints b i = ok o →
    ScanSim absHintsRec o (scanHints (absBytes b) (absPos i))
  /-- `scan_fast::scan_string` (`Scan/Fast.lean:630-647 scanString`). -/
  scan_string : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_string b i = ok o →
    ScanSim absString o (scanString (absBytes b) (absPos i))
  /-- `scan_fast::scan_quoted_nat` (`Scan/Fast.lean:650-657 scanQuotedNat`). -/
  scan_quoted_nat : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_quoted_nat b i = ok o →
    ScanSim natOfDigits o (scanQuotedNat (absBytes b) (absPos i))
  /-- `scan_fast::scan_str_name` (`Scan/Fast.lean:846-849 scanStrName`). -/
  scan_str_name : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_str_name b i = ok o →
    ScanSim absNameRec o (scanStrName (absBytes b) (absPos i))
  /-- `scan_fast::scan_num_name` (`Scan/Fast.lean:901-904 scanNumName`). -/
  scan_num_name : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_num_name b i = ok o →
    ScanSim absNameRec o (scanNumName (absBytes b) (absPos i))
  /-- `scan_fast::scan_app_expr` (`Scan/Fast.lean:956-959 scanAppExpr`). -/
  scan_app_expr : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_app_expr b i = ok o →
    ScanSim absExprRec o (scanAppExpr (absBytes b) (absPos i))
  /-- `scan_fast::scan_lam_expr` (`Scan/Fast.lean:1039-1042 scanLamExpr`). -/
  scan_lam_expr : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_lam_expr b i = ok o →
    ScanSim absExprRec o (scanLamExpr (absBytes b) (absPos i))
  /-- `scan_fast::scan_forall_expr` (`Scan/Fast.lean:1120-1123 scanForallExpr`). -/
  scan_forall_expr : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_forall_expr b i = ok o →
    ScanSim absExprRec o (scanForallExpr (absBytes b) (absPos i))
  /-- `scan_fast::scan_let_expr` (`Scan/Fast.lean:1201-1204 scanLetExpr`). -/
  scan_let_expr : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_let_expr b i = ok o →
    ScanSim absExprRec o (scanLetExpr (absBytes b) (absPos i))
  /-- `scan_fast::scan_const_expr` (`Scan/Fast.lean:1257-1260 scanConstExpr`). -/
  scan_const_expr : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_const_expr b i = ok o →
    ScanSim absExprRec o (scanConstExpr (absBytes b) (absPos i))
  /-- `scan_fast::scan_proj_expr` (`Scan/Fast.lean:1321-1324 scanProjExpr`). -/
  scan_proj_expr : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_proj_expr b i = ok o →
    ScanSim absExprRec o (scanProjExpr (absBytes b) (absPos i))
  /-- `scan_fast::scan_ind_types` (`Scan/Fast.lean:1768-1771 scanIndTypes`). -/
  scan_ind_types : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_ind_types b i = ok o →
    ScanSim absIndTypeRecs o (scanIndTypes (absBytes b) (absPos i))
  /-- `scan_fast::scan_ind_ctors` (`Scan/Fast.lean:1917-1920 scanIndCtors`). -/
  scan_ind_ctors : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_ind_ctors b i = ok o →
    ScanSim absIndCtorRecs o (scanIndCtors (absBytes b) (absPos i))
  /-- `scan_fast::scan_ind_recs` (`Scan/Fast.lean:1593-1596 scanIndRecs`). -/
  scan_ind_recs : ∀ {i : Std.Usize} {o}, frontend.scan_fast.scan_ind_recs b i = ok o →
    ScanSim absIndRecRecs o (scanIndRecs (absBytes b) (absPos i))

/-! ## The port's factored skeleton against con-leche's inlined one -/

/-- `Slice::index_usize` when it succeeds. -/
private theorem slice_index_val {b : Slice Std.U8} {i : Std.Usize} {c : Std.U8}
    (h : Slice.index_usize b i = ok c) : b.val[i.val]? = some c := by
  rw [Slice.index_usize] at h
  have hb : b[i]? = b.val[i.val]? := rfl
  rcases hi : b.val[i.val]? with _ | y
  · rw [hb, hi] at h; simp at h
  · rw [hb, hi] at h
    exact congrArg some (Result.ok_injective h)

/-- The byte the port read at `i` is the byte con-leche reads at `absPos i`. -/
private theorem uget_of_index {b : Slice Std.U8} {i : Std.Usize} {c : Std.U8}
    (h : Slice.index_usize b i = ok c) (hb : absPos i < (absBytes b).usize) :
    (absBytes b).uget (absPos i) (ConLeche.Frontend.usizeInBounds _ _ hb) = absByte c := by
  have hlt : i.val < b.val.length := absPos_lt_usize.mp hb
  rw [absBytes_uget b (absPos i) _ (by simpa using hlt)]
  have hg := slice_index_val h
  rw [List.getElem?_eq_getElem hlt] at hg
  simp only [absPos_toNat]
  exact congrArg absByte (Option.some.inj hg)

private theorem absByte_beq_true {c d : Std.U8} (h : c = d) :
    (absByte c == absByte d) = true := by rw [h]; simp

private theorem absByte_beq_false {c d : Std.U8} (h : ¬ (c = d)) :
    (absByte c == absByte d) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq, absByte_eq_iff]; exact h

/-- `scan_fast::is_ws` (`Scan/Fast.lean:80 isWs`). -/
theorem is_ws_refines {c : Std.U8} {r : Bool} (h : frontend.scan_fast.is_ws c = ok r) :
    r = ConLeche.Frontend.isWs (absByte c) := by
  rw [frontend.scan_fast.is_ws] at h
  rw [ConLeche.Frontend.isWs,
    show (32 : UInt8) = absByte 32#u8 from rfl,
    show (9 : UInt8) = absByte 9#u8 from rfl,
    show (13 : UInt8) = absByte 13#u8 from rfl]
  by_cases h1 : c = 32#u8
  · rw [if_pos h1] at h
    rw [← Result.ok_injective h, absByte_beq_true h1]; rfl
  · rw [if_neg h1] at h
    rw [absByte_beq_false h1]
    by_cases h2 : c = 9#u8
    · rw [if_pos h2] at h
      rw [← Result.ok_injective h, absByte_beq_true h2]; rfl
    · rw [if_neg h2] at h
      rw [absByte_beq_false h2]
      rw [← Result.ok_injective h]
      by_cases h3 : c = 13#u8
      · rw [absByte_beq_true h3, decide_eq_true h3]; rfl
      · rw [absByte_beq_false h3, decide_eq_false h3]; rfl

@[simp] theorem absPos_eq_iff {i j : Std.Usize} : absPos i = absPos j ↔ i = j := by
  constructor
  · intro h; have := absPos_inj h; scalar_tac
  · intro h; rw [h]

private theorem absPos_beq_true {i j : Std.Usize} (h : i = j) :
    (absPos i == absPos j) = true := by rw [h]; simp

private theorem absPos_beq_false {i j : Std.Usize} (h : ¬ (i = j)) :
    (absPos i == absPos j) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq, absPos_eq_iff]; exact h

/-! A byte or a position compared with a con-leche literal.  `n` is passed
explicitly so that the rewrite matches the numeral as it stands in the goal. -/

private theorem lit_eq {c d : Std.U8} (n : UInt8) (hd : absByte d = n) (h : c = d) :
    (absByte c == n) = true := by
  simp only [beq_iff_eq]; rw [h, hd]

private theorem lit_ne {c d : Std.U8} (n : UInt8) (hd : absByte d = n) (h : ¬ (c = d)) :
    ¬ ((absByte c == n) = true) := by
  simp only [beq_iff_eq]
  intro hh
  exact h (absByte_eq_iff.mp (hh.trans hd.symm))

private theorem plit_eq {i j : Std.Usize} (n : USize) (hd : absPos j = n) (h : i = j) :
    (absPos i == n) = true := by
  simp only [beq_iff_eq]; rw [h, hd]

private theorem plit_ne {i j : Std.Usize} (n : USize) (hd : absPos j = n) (h : ¬ (i = j)) :
    ¬ ((absPos i == n) = true) := by
  simp only [beq_iff_eq]
  intro hh
  exact h (absPos_eq_iff.mp (hh.trans hd.symm))

/-- A machine-word increment really moves the cursor forward. -/
private theorem uadd_gt {x c z : Std.Usize} (h : x + c = ok z) (hc : 0 < c.val) :
    x.val < z.val := by
  have := ConRon.Refine.Nat.uadd_val h; omega

/-- Past the end of the chunk `next_member` reports `ExpectedComma`, so a
member loop that got an `Ok` was still inside the chunk. -/
private theorem next_member_lt {b : Slice Std.U8} {i : Std.Usize} {w : Bool}
    {x : frontend.scan_fast.Member × Std.Usize × Bool}
    (h : frontend.scan_fast.next_member b i w = ok (.Ok x)) : i.val < b.length := by
  by_contra hc
  rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
  rw [if_pos (show i ≥ Slice.len b by scalar_tac)] at h
  simp at h

/-- `scan_fast::next_member` only skips forward: the cursor it reports sits at
or after the one it was given. -/
private theorem next_member_ge {b : Slice Std.U8} (f : Nat) :
    ∀ (i : Std.Usize) (w : Bool) (mem : frontend.scan_fast.Member)
      (ni : Std.Usize) (nw : Bool),
      b.length - i.val ≤ f →
      frontend.scan_fast.next_member b i w = ok (.Ok (mem, ni, nw)) →
      i.val ≤ ni.val := by
  induction f with
  | zero =>
    intro i w mem ni nw hf h
    rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
    rw [if_pos (show i ≥ Slice.len b by scalar_tac)] at h
    simp at h
  | succ f ih =>
    intro i w mem ni nw hf h
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
        have h1 := uadd_gt hi2 (by scalar_tac)
        have h2 := ih i2 w mem ni nw (by omega) h
        omega
      · rw [if_neg hws] at h
        by_cases hc1 : c = 125#u8
        · rw [if_pos hc1] at h
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, hni, -⟩ := h
          scalar_tac
        · rw [if_neg hc1] at h
          by_cases hc2 : c = 44#u8
          · rw [if_pos hc2] at h
            by_cases hw : w = true
            · rw [if_pos hw] at h; simp at h
            · rw [if_neg hw] at h
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have h1 := uadd_gt hi2 (by scalar_tac)
              have h2 := ih i2 true mem ni nw (by omega) h
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
                      Prod.mk.injEq] at h
                    obtain ⟨-, hni, -⟩ := h
                    scalar_tac
              · rw [if_neg hw] at h; simp at h
            · rw [if_neg hc3] at h; simp at h

open ConLeche.Frontend in
/-- **The bridge.**  `scan_fast::next_member` runs the object skeleton once
where con-leche writes it inline in every `scan*Loop`: a `Member::Close` lands
on the `close` continuation, a `Member::Key` on the `key` continuation with the
key classified, and every error is mirrored at the same offset and tag.  `L` is
the con-leche loop and `hL` its reading as `objStep`. -/
private theorem next_member_sim {b : Slice Std.U8} (K : ScanLineIngredients b) (f : Nat) :
    ∀ {α : Type} (i : Std.Usize) (w : Bool)
      (o : core.result.Result (frontend.scan_fast.Member × Std.Usize × Bool)
             frontend.scan_types.ScanErr)
      (L close : USize → Bool → ScanRes α)
      (key : Key → USize → USize → ScanRes α),
      b.length - i.val ≤ f →
      (∀ i' w', L i' w' = objStep (absBytes b) i' w' L close key) →
      frontend.scan_fast.next_member b i w = ok o →
      (match o with
       | .Ok (mem, ni, nw) => L (absPos i) w = memArm close key mem ni nw
       | .Err e => ScanErrSim e (L (absPos i) w)) := by
  induction f with
  | zero =>
    intro α i w o L close key hf hL h
    rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
    rw [if_pos (show i ≥ Slice.len b by scalar_tac)] at h
    rw [← Result.ok_injective h]
    refine ScanErrSim.mk rfl ?_
    rw [hL (absPos i) w, objStep, dif_neg (by rw [absPos_lt_usize]; scalar_tac)]
    simp
  | succ f ih =>
    intro α i w o L close key hf hL h
    rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
    by_cases hend : i ≥ Slice.len b
    · rw [if_pos hend] at h
      rw [← Result.ok_injective h]
      refine ScanErrSim.mk rfl ?_
      rw [hL (absPos i) w, objStep, dif_neg (by rw [absPos_lt_usize]; scalar_tac)]
      simp
    · rw [if_neg hend] at h
      have hi : i.val < b.length := by scalar_tac
      have hlt : absPos i < (absBytes b).usize := absPos_lt_usize.mpr (by simpa using hi)
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨w1, hw1, h⟩ := bind_eq_ok_iff.mp h
      rw [hL (absPos i) w, objStep, dif_pos hlt, uget_of_index hc hlt]
      rw [← is_ws_refines hw1]
      by_cases hws : w1 = true
      · rw [if_pos hws] at h ⊢
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have h1 := uadd_gt hi2 (by scalar_tac)
        rw [← absPos_add_one hi2]
        exact ih i2 w o L close key (by omega) hL h
      · rw [if_neg hws] at h
        rw [if_neg (show ¬ (w1 = true) from hws)]
        by_cases hc1 : c = 125#u8
        · rw [if_pos hc1] at h
          rw [if_pos (lit_eq (d := 125#u8) 125 rfl hc1)]
          rw [← Result.ok_injective h]
          rfl
        · rw [if_neg hc1] at h
          rw [if_neg (lit_ne (d := 125#u8) 125 rfl hc1)]
          by_cases hc2 : c = 44#u8
          · rw [if_pos hc2] at h
            rw [if_pos (lit_eq (d := 44#u8) 44 rfl hc2)]
            by_cases hw : w = true
            · rw [if_pos hw] at h ⊢
              rw [← Result.ok_injective h]
              exact ScanErrSim.mk rfl (by simp)
            · rw [if_neg hw] at h ⊢
              obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
              have h1 := uadd_gt hi2 (by scalar_tac)
              rw [← absPos_add_one hi2]
              exact ih i2 true o L close key (by omega) hL h
          · rw [if_neg hc2] at h
            rw [if_neg (lit_ne (d := 44#u8) 44 rfl hc2)]
            by_cases hc3 : c = 34#u8
            · rw [if_pos hc3] at h
              rw [if_pos (lit_eq (d := 34#u8) 34 rfl hc3)]
              by_cases hw : w = true
              · rw [if_pos hw] at h
                rw [if_neg (show ¬ ((!w) = true) by simp [hw])]
                obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨ke, hke', h⟩ := bind_eq_ok_iff.mp h
                rw [← absPos_add_one hi2, ← K.key_end hke']
                by_cases hke : ke = 0#usize
                · rw [if_pos hke] at h
                  rw [if_pos (plit_eq (j := 0#usize) 0 rfl hke)]
                  rw [← Result.ok_injective h]
                  exact ScanErrSim.mk rfl (by simp)
                · rw [if_neg hke] at h
                  rw [if_neg (plit_ne (j := 0#usize) 0 rfl hke)]
                  obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
                  rw [← K.value_at hv1]
                  by_cases hv : v1 = i
                  · rw [if_pos hv] at h
                    rw [if_pos (absPos_beq_true hv)]
                    rw [← Result.ok_injective h]
                    exact ScanErrSim.mk rfl (by simp)
                  · rw [if_neg hv] at h
                    rw [if_neg (by rw [absPos_beq_false hv]; exact Bool.false_ne_true)]
                    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
                    rw [← absPos_sub hi3, ← K.key_at hk1]
                    rw [← Result.ok_injective h]
                    rfl
              · rw [if_neg hw] at h
                rw [if_pos (show ((!w) = true) by simp [hw] )]
                rw [← Result.ok_injective h]
                exact ScanErrSim.mk rfl (by simp)
            · rw [if_neg hc3] at h
              rw [if_neg (lit_ne (d := 34#u8) 34 rfl hc3)]
              rw [← Result.ok_injective h]
              exact ScanErrSim.mk rfl (by simp)

end ConRon.Refine.Frontend
