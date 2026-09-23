/-
# `ConRon.Refine2.Frontend.Scan.Spec` — `ScanSpec` is a theorem

**Task #97-P5-Front.**  The tier's scanner seam, `Refine2/Frontend/Shape.lean`'s
three-clause `ScanSpec`, was carried as a named hypothesis because its clauses
were theorems only of the out-of-build `RefineOld/Frontend/Scan*.lean`.  The
Rust byte recogniser (`crates/con-ron-core/src/frontend/{scan_fast,scan_types,
nat_decimal,text}.rs`) is unchanged since task #86 and the arena twin calls
con-leche's `scanLineFwd` by name, so those files were moved back as
`Refine2/Frontend/Scan/{Kit,Str,Obj,Expr,Ind,WFBase,WF,Line}.lean` — namespace
changed, three `open`s, the `#guard_msgs` census strings re-spelled, nothing
else — and every one elaborates `sorry`-free against the swapped model.

This file assembles the record:

* `scanLineFwd` is `Scan/Line.lean`'s `scan_line_fwd_refines`, at
  `Scan/Str.lean`'s two decoder theorems `utf8_decode_spec`/`unescape_spec`;
* `scanLineStr` is `scan_line_fwd_str_wf` (the spellings) and
  `scan_line_fwd_digits` (a `natVal`'s digits are a decimal run) through
  `natValSpec_of_digits`, which is `RefineOld/Frontend/StateDR.lean`'s lemma of
  that name moved here (its subject, `nat_decimal::from_decimal`, is term-free);
* `newlineFrom` is `Scan/Kit.lean`'s `newline_from_refines`.

And the con-leche-side fact `Refine2/Frontend/Top.lean`'s `feed_chunk` loop
needs — a line the scanner accepts with a nonzero continue position ends at a
newline at or after its start — is `Scan/Line.lean`'s
`scanLineFwd_tail_of_no_newline`, contraposed.

## `sorry` count in this file: 0
-/
import ConRon.Refine2.Frontend.Shape
import ConRon.Refine2.Frontend.Scan.Line

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2.Frontend

/-- **`NatValSpec` from the scanner's digit fact** (moved from
`RefineOld/Frontend/StateDR.lean`): `from_decimal_ok` rules out the `none` arm
and `from_decimal_refines` gives the value. -/
theorem natValSpec_of_digits {r : frontend.scan_types.ExprRec}
    (h : ExprDigits r) : NatValSpec r := by
  intro ds hr o ho
  subst hr
  simp only [ExprDigits] at h
  have hval : (alloc.vec.Vec.deref ds).val = ds.val := Slice.from_val _ _
  obtain ⟨n, hn⟩ := from_decimal_ok (ds := alloc.vec.Vec.deref ds)
    (by rw [hval]; exact h.1) (by rw [hval]; exact h.2)
  rw [hn] at ho
  refine ⟨n, (Result.ok_injective ho).symm, ?_⟩
  rw [(from_decimal_refines hn).1, natOfDigits_eq, hval]

/-- **The scanner seam, discharged.** -/
theorem scanSpec : ScanSpec where
  scanLineFwd h := scan_line_fwd_refines utf8_decode_spec unescape_spec h
  scanLineStr h := by
    refine ⟨?_, ?_⟩
    · have := scan_line_fwd_str_wf h
      revert this
      rename_i r _
      cases r <;> simp [LineStrWF, LineRecStrWF]
      rename_i d
      cases d <;> simp [DeclStrWF, DeclRecStrWF]
    · have := scan_line_fwd_digits h
      revert this
      rename_i r _
      cases r <;> simp [LineExprDigits, LineNatValSpec]
      exact natValSpec_of_digits
  newlineFrom h := newline_from_refines h

/-- **A line con-leche's scanner accepts with a continue position ends at a
newline at or after its start** — `scanLineFwd_tail_of_no_newline`,
contraposed. -/
theorem scanLineFwd_ok_newline {b : ByteArray} {i : USize}
    {r : ConLeche.Frontend.LineRec} {j : USize}
    (h : ConLeche.Frontend.scanLineFwd b i = .ok r j) (hj : j ≠ 0) :
    ConLeche.Frontend.newlineFrom b i = true := by
  cases hn : ConLeche.Frontend.newlineFrom b i
  · rcases scanLineFwd_tail_of_no_newline b i hn with ⟨le, hle⟩ | ⟨r', hr'⟩
    · rw [h] at hle; cases hle
    · rw [h] at hr'; cases hr'; exact absurd rfl hj
  · rfl

/-- info: 'ConRon.Refine2.Frontend.scanSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scanSpec

end ConRon.Refine2.Frontend
