/-
**The declaration records and the line scanner, exactly** (task #87, phase 3).

`Refine/Frontend/ScanWF.lean` (phase 1) proved that every record
`scan_fast::scan_line_fwd` hands the parse is *well formed*.  This file proves
that it is **the record con-leche reads from the same bytes**, and that it
fails where con-leche fails:

    ScanSim absLineRec (scan_line_fwd b i) (scanLineFwd (absBytes b) (absPos i))

— the capstone of the scanner tier, and the last link of the chain
`ScanKit → ScanObj/ScanStr → ScanExpr/ScanInd → ScanLine`.

## What this file gives the tier

* `absLinePayload` and `line_payload_is_absent_refines`;
* `scan_axiom_decl_refines`, `scan_def_decl_refines`, `scan_thm_decl_refines`,
  `scan_opaque_decl_refines`, `scan_quot_decl_refines`,
  `scan_ind_decl_refines` — the six declaration records;
* `scan_line_loop_refines` — the line dispatcher;
* **`scan_line_fwd_refines`** — the capstone, with its axiom census pinned.

## How the two recognisers are lined up

con-leche's `Scan/Fast.lean` writes the JSON object skeleton inline in each of
its twenty `scan*Loop`s; the port factors it out as `scan_fast::next_member`
(module note, deviation 3).  `Refine/Frontend/ScanObj.lean` owns that bridge —
`memberBody`, `MemberStep`, `nextMember_step` — and the `Nat`-valued slot,
`natSlot`/`NatSlotStep`/`natSlot_step`.  Each loop below contributes only its
own reading: a `*_body` equation saying that the con-leche loop **is**
`memberBody` at its own closing arm and key dispatch.  Every one of them is
`rfl` after one unfolding, so nothing new is defined here, only read.

`scanLineLoop`'s closing arm matches a `LinePayload` against a `UInt8`
`idxKind`, so its patterns overlap and `rw [scanLineLoop]` would pick one
equation and leave side conditions; its `*_body` is the one that has to unfold
with `scanLineLoop.eq_def`.

## The ingredients

The record scanners this file dispatches to are proved elsewhere in the tier.
Those that had not landed when this file did are stated as
`ScanLineIngredients` — the `Refine/IndSpec.lean` pattern — and every lemma
below is proved **from** it, together with `ScanObj.KitFacts` for the two
`ScanKit` leaves (`key_at`, `value_at`) the skeleton needs.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.ScanObj

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

open ConLeche.Frontend

/-! ## Plumbing -/

/-- A `lift`ed pure step is an equation on its value. -/
private theorem lift_val {α : Type} {x y : α} (h : lift x = ok y) : x = y := by
  simpa only [lift, Result.ok.injEq] using h

/-- An Aeneas `err` arm, read forwards. -/
private theorem err_val {T : Type} {offset : Std.Usize}
    {what : frontend.scan_types.ErrTag} {x : core.result.Result (T × Std.Usize)
      frontend.scan_types.ScanErr}
    (h : frontend.scan_fast.err T offset what = ok x) : x = .Err ⟨offset, what⟩ := by
  rw [frontend.scan_fast.err] at h
  exact (Result.ok_injective h).symm

/-- The `seen` mask, masked against a con-leche literal. -/
private theorem u32_and_lit {x y z : Std.U32} (n : UInt32) (hn : absU32 y = n)
    (h : lift (x &&& y) = ok z) : absU32 x &&& n = absU32 z := by
  rw [← hn, ← absU32_and, lift_val h]

/-- The `seen` mask, with a con-leche literal set. -/
private theorem u32_or_lit {x y z : Std.U32} (n : UInt32) (hn : absU32 y = n)
    (h : lift (x ||| y) = ok z) : absU32 x ||| n = absU32 z := by
  rw [← hn, ← absU32_or, lift_val h]

/-- A `u32` compared with a con-leche literal. -/
private theorem u32_bne {x y : Std.U32} (n : UInt32) (hn : absU32 y = n) :
    (absU32 x != n) = (x != y) := by
  rw [← hn]; simp only [bne, absU32_beq]

/-- `scan_fast::dup` (the duplicate-key test every slot opens with). -/
private theorem dup_refines {seen bit : Std.U32} {r : Bool} (n : UInt32)
    (hn : absU32 bit = n) (h : frontend.scan_fast.dup seen bit = ok r) :
    ((absU32 seen &&& n) != 0) = r := by
  rw [frontend.scan_fast.dup] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h, u32_and_lit n hn hi]
  exact u32_bne (y := 0#u32) 0 rfl

/-- `scan_fast::prog` (the `noProgress` guard every slot closes with). -/
private theorem prog_iff {ks e : Std.Usize} {r : Bool}
    (h : frontend.scan_fast.prog ks e = ok r) : (r = true) ↔ (absPos ks < absPos e) := by
  rw [frontend.scan_fast.prog] at h
  rw [← Result.ok_injective h, decide_eq_true_eq, absPos_lt]
  constructor <;> intro hh <;> scalar_tac

/-- A byte compared with a con-leche literal, positively. -/
private theorem blit_eq {c d : Std.U8} (n : UInt8) (hd : absByte d = n) (h : c = d) :
    (absByte c == n) = true := by simp only [beq_iff_eq]; rw [h, hd]

/-- A byte compared with a con-leche literal, negatively. -/
private theorem blit_ne {c d : Std.U8} (n : UInt8) (hd : absByte d = n) (h : ¬ (c = d)) :
    ¬ ((absByte c == n) = true) := by
  simp only [beq_iff_eq]
  intro hh
  exact h (absByte_inj (hh.trans hd.symm))

/-- A byte compared with a con-leche literal, as the port's `!=`. -/
private theorem u8_bne {x y : Std.U8} (n : UInt8) (hn : absByte y = n) :
    (absByte x != n) = (x != y) := by
  rw [← hn]; simp only [bne, absByte_beq_u8]

/-- A position compared with con-leche's `0`. -/
private theorem p_beq0 {e : Std.Usize} : (absPos e == (0 : USize)) = (e == 0#usize) := by
  by_cases he : e = 0#usize
  · subst he; simp
  · have h1 : ¬ (e.val = 0) := fun hc => he (by scalar_tac)
    simp [he, h1]

/-- `Vec::index` at a literal position, as a `getElem?` fact. -/
private theorem vec_index_get? {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    exact congrArg some (Result.ok_injective h)

/-- A machine-word increment really moves the cursor forward. -/
private theorem uadd_gt {x c z : Std.Usize} (h : x + c = ok z) (hc : 0 < c.val) :
    x.val < z.val := by
  have := ConRon.Refine.Nat.uadd_val h; omega

/-- The chunk's length on con-leche's side. -/
private theorem usize_le_absPos {b : Slice Std.U8} {s : Std.Usize} :
    (absBytes b).usize ≤ absPos s ↔ b.val.length ≤ s.val := by
  rw [USize.le_iff_toNat_le, absBytes_usize, absPos_toNat]

/-- The closing brace of a declaration record: the `seen` mask against the
record's required keys, and then the record itself. -/
private theorem close_mask {seen mask : Std.U32} {ni : Std.Usize}
    (n : UInt32) (hn : absU32 mask = n)
    {r : frontend.scan_types.DeclRec} {lr : DeclRec} (hr : absDeclRec r = lr)
    {o : core.result.Result (frontend.scan_types.DeclRec × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : (do
        let i1 ← lift (seen &&& mask)
        if i1 != mask then
          frontend.scan_fast.err frontend.scan_types.DeclRec ni
            frontend.scan_types.ErrTag.MissingKey
        else do
          let i2 ← ni + 1#usize
          ok (.Ok (r, i2))) = ok o) :
    ScanSim absDeclRec o
      (if (absU32 seen &&& n) != n then .err ⟨(absPos ni).toNat, .missingKey⟩
       else .ok lr (absPos ni + 1)) := by
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  rw [u32_and_lit n hn hi1, u32_bne n hn]
  by_cases hm : (i1 != mask) = true
  · rw [if_pos hm] at h
    rw [if_pos hm, err_val h]
    exact ScanSim.err (ScanErrSim.mk rfl (by simp))
  · rw [if_neg hm] at h
    rw [if_neg hm]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    exact ScanSim.ok (by rw [absPos_add_one hi2, hr])

/-! ## The line payload

`scan_fast::LinePayload` against `ConLeche/Frontend/Scan/Fast.lean:2449-2456`,
constructor for constructor. -/

/-- `LinePayload` (`Scan/Fast.lean:2449-2456`). -/
def absLinePayload : frontend.scan_fast.LinePayload → LinePayload
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

/-- The closing brace of a line: the payload matched against the index key. -/
private theorem close_line {pl : frontend.scan_fast.LinePayload} {idx_kind : Std.U8}
    {idx : Std.U64} {ni : Std.Usize}
    {o : core.result.Result (frontend.scan_types.LineRec × Std.Usize)
           frontend.scan_types.ScanErr}
    (h : (match pl with
          | .Absent =>
            frontend.scan_fast.err frontend.scan_types.LineRec ni
              frontend.scan_types.ErrTag.MissingKey
          | .Name r1 =>
            if idx_kind = 1#u8 then do
              let i1 ← ni + 1#usize
              ok (.Ok (frontend.scan_types.LineRec.Name idx r1, i1))
            else
              frontend.scan_fast.err frontend.scan_types.LineRec ni
                frontend.scan_types.ErrTag.MixedKeys
          | .Level r1 =>
            if idx_kind = 2#u8 then do
              let i1 ← ni + 1#usize
              ok (.Ok (frontend.scan_types.LineRec.Level idx r1, i1))
            else
              frontend.scan_fast.err frontend.scan_types.LineRec ni
                frontend.scan_types.ErrTag.MixedKeys
          | .Expr r1 =>
            if idx_kind = 3#u8 then do
              let i1 ← ni + 1#usize
              ok (.Ok (frontend.scan_types.LineRec.Expr idx r1, i1))
            else
              frontend.scan_fast.err frontend.scan_types.LineRec ni
                frontend.scan_types.ErrTag.MixedKeys
          | .Decl d =>
            if idx_kind = 0#u8 then do
              let i1 ← ni + 1#usize
              ok (.Ok (frontend.scan_types.LineRec.Decl d, i1))
            else
              frontend.scan_fast.err frontend.scan_types.LineRec ni
                frontend.scan_types.ErrTag.MixedKeys
          | .Header =>
            if idx_kind = 0#u8 then do
              let i1 ← ni + 1#usize
              ok (.Ok (frontend.scan_types.LineRec.Header, i1))
            else
              frontend.scan_fast.err frontend.scan_types.LineRec ni
                frontend.scan_types.ErrTag.MixedKeys) = ok o) :
    ScanSim absLineRec o
      (match absLinePayload pl, absByte idx_kind with
       | .name r, 1 => .ok (.name (absU64 idx) r) (absPos ni + 1)
       | .level r, 2 => .ok (.level (absU64 idx) r) (absPos ni + 1)
       | .expr r, 3 => .ok (.expr (absU64 idx) r) (absPos ni + 1)
       | .decl d, 0 => .ok (.decl d) (absPos ni + 1)
       | .header, 0 => .ok .header (absPos ni + 1)
       | .absent, _ => .err ⟨(absPos ni).toNat, .missingKey⟩
       | _, _ => .err ⟨(absPos ni).toNat, .mixedKeys⟩) := by
  cases pl with
  | Absent =>
    dsimp only at h
    rw [err_val h]
    exact ScanSim.err (ScanErrSim.mk rfl (by simp [absLinePayload]))
  | Name r1 =>
    dsimp only at h
    by_cases hk : idx_kind = 1#u8
    · rw [if_pos hk] at h
      subst hk
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h]
      exact ScanSim.ok (by rw [absPos_add_one hi1]; rfl)
    · rw [if_neg hk] at h
      rw [err_val h]
      refine ScanSim.err (ScanErrSim.mk rfl ?_)
      have hne : ¬ (absByte idx_kind = 1) := fun hc => hk (absByte_inj (hc.trans rfl))
      simp only [absLinePayload]
      split <;> simp_all
  | Level r1 =>
    dsimp only at h
    by_cases hk : idx_kind = 2#u8
    · rw [if_pos hk] at h
      subst hk
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h]
      exact ScanSim.ok (by rw [absPos_add_one hi1]; rfl)
    · rw [if_neg hk] at h
      rw [err_val h]
      refine ScanSim.err (ScanErrSim.mk rfl ?_)
      have hne : ¬ (absByte idx_kind = 2) := fun hc => hk (absByte_inj (hc.trans rfl))
      simp only [absLinePayload]
      split <;> simp_all
  | Expr r1 =>
    dsimp only at h
    by_cases hk : idx_kind = 3#u8
    · rw [if_pos hk] at h
      subst hk
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h]
      exact ScanSim.ok (by rw [absPos_add_one hi1]; rfl)
    · rw [if_neg hk] at h
      rw [err_val h]
      refine ScanSim.err (ScanErrSim.mk rfl ?_)
      have hne : ¬ (absByte idx_kind = 3) := fun hc => hk (absByte_inj (hc.trans rfl))
      simp only [absLinePayload]
      split <;> simp_all
  | Decl d =>
    dsimp only at h
    by_cases hk : idx_kind = 0#u8
    · rw [if_pos hk] at h
      subst hk
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h]
      exact ScanSim.ok (by rw [absPos_add_one hi1]; rfl)
    · rw [if_neg hk] at h
      rw [err_val h]
      refine ScanSim.err (ScanErrSim.mk rfl ?_)
      have hne : ¬ (absByte idx_kind = 0) := fun hc => hk (absByte_inj (hc.trans rfl))
      simp only [absLinePayload]
      split <;> simp_all
  | Header =>
    dsimp only at h
    by_cases hk : idx_kind = 0#u8
    · rw [if_pos hk] at h
      subst hk
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h]
      exact ScanSim.ok (by rw [absPos_add_one hi1]; rfl)
    · rw [if_neg hk] at h
      rw [err_val h]
      refine ScanSim.err (ScanErrSim.mk rfl ?_)
      have hne : ¬ (absByte idx_kind = 0) := fun hc => hk (absByte_inj (hc.trans rfl))
      simp only [absLinePayload]
      split <;> simp_all

/-! ## What the rest of the tier owes this file -/

/-- The record scanners this file's loops dispatch to, as they are proved in
`ScanStr`, `ScanObj` and `ScanExpr`. -/
structure ScanLineIngredients (b : Slice Std.U8) : Prop where
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

/-! ## The six declaration records

Each is `memberBody` plus its own slots, and each proof is the same five
steps: peel `next_member`, send it through `nextMember_step`, close the
`Close` arm at the `seen` mask, send the sixty-odd keys outside the record's
alphabet to `unknownKey`, and take each slot through its scanner and the
`prog` guard into the induction hypothesis. -/
/-- `scanAxiomDeclLoop` (`ConLeche/Frontend/Scan/Fast.lean:1922-1988`) read as
`memberBody`. -/
private theorem scanAxiomDeclLoop_body (b : ByteArray) (seen : UInt32) (isUns : Bool)
    (lps : List Nat) (nm ty : Nat) (p : USize) (w : Bool) :
    scanAxiomDeclLoop b p w seen isUns lps nm ty
      = memberBody b (fun p' w' => scanAxiomDeclLoop b p' w' seen isUns lps nm ty)
          (fun p' w' =>
            if w' && seen != 0 then .err ⟨p'.toNat, .expectedKey⟩
            else if (seen &&& 15) != 15 then .err ⟨p'.toNat, .missingKey⟩
            else .ok (.ax ⟨nm, lps, ty⟩ isUns) (p' + 1))
          (fun k ks v =>
            match k with
            | .kIsUnsafe =>
              if (seen &&& 1) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanBool b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then scanAxiomDeclLoop b e false (seen ||| 1) x lps nm ty
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kLevelParams =>
              if (seen &&& 2) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanNatList b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then scanAxiomDeclLoop b e false (seen ||| 2) isUns x nm ty
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kName =>
              if (seen &&& 4) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanAxiomDeclLoop b e false (seen ||| 4) isUns lps n ty)
            | .kType =>
              if (seen &&& 8) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanAxiomDeclLoop b e false (seen ||| 8) isUns lps nm n)
            | _ => .err ⟨ks.toNat, .unknownKey⟩) p w := by
  rw [scanAxiomDeclLoop]
  rfl

private theorem scanDefDeclLoop_body (b : ByteArray) (seen : UInt32) (hints : HintsRec)
    (lps : List Nat) (nm : Nat) (safety : String) (ty vl : Nat) (p : USize) (w : Bool) :
    scanDefDeclLoop b p w seen hints lps nm safety ty vl
      = memberBody b
          (fun p' w' => scanDefDeclLoop b p' w' seen hints lps nm safety ty vl)
          (fun p' w' =>
            if w' && seen != 0 then .err ⟨p'.toNat, .expectedKey⟩
            else if (seen &&& 124) != 124 then .err ⟨p'.toNat, .missingKey⟩
            else .ok (.defn ⟨nm, lps, ty⟩ vl hints safety) (p' + 1))
          (fun k ks v =>
            match k with
            | .kAll =>
              if (seen &&& 1) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanNatList b v with
                | .err e => .err e
                | .ok _x e =>
                  if ks < e then
                    scanDefDeclLoop b e false (seen ||| 1) hints lps nm safety ty vl
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kHints =>
              if (seen &&& 2) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanHints b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then
                    scanDefDeclLoop b e false (seen ||| 2) x lps nm safety ty vl
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kLevelParams =>
              if (seen &&& 4) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanNatList b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then
                    scanDefDeclLoop b e false (seen ||| 4) hints x nm safety ty vl
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kName =>
              if (seen &&& 8) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanDefDeclLoop b e false (seen ||| 8) hints lps n safety ty vl)
            | .kSafety =>
              if (seen &&& 16) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanString b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then
                    scanDefDeclLoop b e false (seen ||| 16) hints lps nm x ty vl
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kType =>
              if (seen &&& 32) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanDefDeclLoop b e false (seen ||| 32) hints lps nm safety n vl)
            | .kValue =>
              if (seen &&& 64) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanDefDeclLoop b e false (seen ||| 64) hints lps nm safety ty n)
            | _ => .err ⟨ks.toNat, .unknownKey⟩) p w := by
  rw [scanDefDeclLoop]; rfl

private theorem scanThmDeclLoop_body (b : ByteArray) (seen : UInt32)
    (lps : List Nat) (nm ty vl : Nat) (p : USize) (w : Bool) :
    scanThmDeclLoop b p w seen lps nm ty vl
      = memberBody b (fun p' w' => scanThmDeclLoop b p' w' seen lps nm ty vl)
          (fun p' w' =>
            if w' && seen != 0 then .err ⟨p'.toNat, .expectedKey⟩
            else if (seen &&& 30) != 30 then .err ⟨p'.toNat, .missingKey⟩
            else .ok (.thm ⟨nm, lps, ty⟩ vl) (p' + 1))
          (fun k ks v =>
            match k with
            | .kAll =>
              if (seen &&& 1) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanNatList b v with
                | .err e => .err e
                | .ok _x e =>
                  if ks < e then scanThmDeclLoop b e false (seen ||| 1) lps nm ty vl
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kLevelParams =>
              if (seen &&& 2) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanNatList b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then scanThmDeclLoop b e false (seen ||| 2) x nm ty vl
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kName =>
              if (seen &&& 4) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanThmDeclLoop b e false (seen ||| 4) lps n ty vl)
            | .kType =>
              if (seen &&& 8) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanThmDeclLoop b e false (seen ||| 8) lps nm n vl)
            | .kValue =>
              if (seen &&& 16) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanThmDeclLoop b e false (seen ||| 16) lps nm ty n)
            | _ => .err ⟨ks.toNat, .unknownKey⟩) p w := by
  rw [scanThmDeclLoop]; rfl

private theorem scanOpaqueDeclLoop_body (b : ByteArray) (seen : UInt32) (isUns : Bool)
    (lps : List Nat) (nm ty vl : Nat) (p : USize) (w : Bool) :
    scanOpaqueDeclLoop b p w seen isUns lps nm ty vl
      = memberBody b (fun p' w' => scanOpaqueDeclLoop b p' w' seen isUns lps nm ty vl)
          (fun p' w' =>
            if w' && seen != 0 then .err ⟨p'.toNat, .expectedKey⟩
            else if (seen &&& 62) != 62 then .err ⟨p'.toNat, .missingKey⟩
            else .ok (.opaq ⟨nm, lps, ty⟩ vl isUns) (p' + 1))
          (fun k ks v =>
            match k with
            | .kAll =>
              if (seen &&& 1) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanNatList b v with
                | .err e => .err e
                | .ok _x e =>
                  if ks < e then
                    scanOpaqueDeclLoop b e false (seen ||| 1) isUns lps nm ty vl
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kIsUnsafe =>
              if (seen &&& 2) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanBool b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then
                    scanOpaqueDeclLoop b e false (seen ||| 2) x lps nm ty vl
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kLevelParams =>
              if (seen &&& 4) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanNatList b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then
                    scanOpaqueDeclLoop b e false (seen ||| 4) isUns x nm ty vl
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kName =>
              if (seen &&& 8) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanOpaqueDeclLoop b e false (seen ||| 8) isUns lps n ty vl)
            | .kType =>
              if (seen &&& 16) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanOpaqueDeclLoop b e false (seen ||| 16) isUns lps nm n vl)
            | .kValue =>
              if (seen &&& 32) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanOpaqueDeclLoop b e false (seen ||| 32) isUns lps nm ty n)
            | _ => .err ⟨ks.toNat, .unknownKey⟩) p w := by
  rw [scanOpaqueDeclLoop]; rfl

private theorem scanQuotDeclLoop_body (b : ByteArray) (seen : UInt32) (kind : String)
    (lps : List Nat) (nm ty : Nat) (p : USize) (w : Bool) :
    scanQuotDeclLoop b p w seen kind lps nm ty
      = memberBody b (fun p' w' => scanQuotDeclLoop b p' w' seen kind lps nm ty)
          (fun p' w' =>
            if w' && seen != 0 then .err ⟨p'.toNat, .expectedKey⟩
            else if (seen &&& 15) != 15 then .err ⟨p'.toNat, .missingKey⟩
            else .ok (.quot ⟨nm, lps, ty⟩ kind) (p' + 1))
          (fun k ks v =>
            match k with
            | .kKind =>
              if (seen &&& 1) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanString b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then scanQuotDeclLoop b e false (seen ||| 1) x lps nm ty
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kLevelParams =>
              if (seen &&& 2) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanNatList b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then scanQuotDeclLoop b e false (seen ||| 2) kind x nm ty
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kName =>
              if (seen &&& 4) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanQuotDeclLoop b e false (seen ||| 4) kind lps n ty)
            | .kType =>
              if (seen &&& 8) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanQuotDeclLoop b e false (seen ||| 8) kind lps nm n)
            | _ => .err ⟨ks.toNat, .unknownKey⟩) p w := by
  rw [scanQuotDeclLoop]; rfl

private theorem scanIndDeclLoop_body (b : ByteArray) (seen : UInt32)
    (ctors : List IndCtorRec) (recs : List IndRecRec) (types : List IndTypeRec)
    (p : USize) (w : Bool) :
    scanIndDeclLoop b p w seen ctors recs types
      = memberBody b (fun p' w' => scanIndDeclLoop b p' w' seen ctors recs types)
          (fun p' w' =>
            if w' && seen != 0 then .err ⟨p'.toNat, .expectedKey⟩
            else if (seen &&& 26) != 26 then .err ⟨p'.toNat, .missingKey⟩
            else .ok (.ind types ctors recs) (p' + 1))
          (fun k ks v =>
            match k with
            | .kAll =>
              if (seen &&& 1) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanNatList b v with
                | .err e => .err e
                | .ok _x e =>
                  if ks < e then scanIndDeclLoop b e false (seen ||| 1) ctors recs types
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kCtors =>
              if (seen &&& 2) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanIndCtors b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then scanIndDeclLoop b e false (seen ||| 2) x recs types
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kIsUnsafe =>
              if (seen &&& 4) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanBool b v with
                | .err e => .err e
                | .ok _x e =>
                  if ks < e then scanIndDeclLoop b e false (seen ||| 4) ctors recs types
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kRecs =>
              if (seen &&& 8) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanIndRecs b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then scanIndDeclLoop b e false (seen ||| 8) ctors x types
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kTypes =>
              if (seen &&& 16) != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanIndTypes b v with
                | .err e => .err e
                | .ok x e =>
                  if ks < e then scanIndDeclLoop b e false (seen ||| 16) ctors recs x
                  else .err ⟨ks.toNat, .noProgress⟩
            | _ => .err ⟨ks.toNat, .unknownKey⟩) p w := by
  rw [scanIndDeclLoop]; rfl

private theorem scanLineLoop_body (b : ByteArray) (idxKind : UInt8) (idx : Nat)
    (pl : LinePayload) (p : USize) (w : Bool) :
    scanLineLoop b p w idxKind idx pl
      = memberBody b (fun p' w' => scanLineLoop b p' w' idxKind idx pl)
          (fun p' w' =>
            if w' && (idxKind != 0 || !pl.isAbsent) then .err ⟨p'.toNat, .expectedKey⟩
            else
              match pl, idxKind with
              | .name r, 1 => .ok (.name idx r) (p' + 1)
              | .level r, 2 => .ok (.level idx r) (p' + 1)
              | .expr r, 3 => .ok (.expr idx r) (p' + 1)
              | .decl d, 0 => .ok (.decl d) (p' + 1)
              | .header, 0 => .ok .header (p' + 1)
              | .absent, _ => .err ⟨p'.toNat, .missingKey⟩
              | _, _ => .err ⟨p'.toNat, .mixedKeys⟩)
          (fun k ks v =>
            match k with
            | .kIn | .kIl | .kIe =>
              if idxKind != 0 then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanLineLoop b e false
                  (match k with | .kIn => 1 | .kIl => 2 | _ => 3) n pl)
            | .kBvar | .kSort | .kSucc | .kParam =>
              if !pl.isAbsent then .err ⟨ks.toNat, .duplicateKey⟩
              else natSlot b ks v (fun n e =>
                scanLineLoop b e false idxKind idx
                  (match k with
                   | .kBvar => .expr (.bvar n)
                   | .kSort => .expr (.sort n)
                   | .kSucc => .level (.succ n)
                   | _ => .level (.param n)))
            | .kMax | .kImax =>
              if !pl.isAbsent then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanNatList b v with
                | .err e => .err e
                | .ok us e =>
                  match us with
                  | [a, d] =>
                    if ks < e then
                      scanLineLoop b e false idxKind idx
                        (match k with
                         | .kMax => .level (.max a d)
                         | _ => .level (.imax a d))
                    else .err ⟨ks.toNat, .noProgress⟩
                  | _ => .err ⟨v.toNat, .expectedList⟩
            | .kStr | .kNum =>
              if !pl.isAbsent then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match (match k with
                       | .kStr => scanStrName b v
                       | _ => scanNumName b v) with
                | .err e => .err e
                | .ok r e =>
                  if ks < e then scanLineLoop b e false idxKind idx (.name r)
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kApp | .kLam | .kForallE | .kLetE | .kConst | .kProj =>
              if !pl.isAbsent then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match (match k with
                       | .kApp => scanAppExpr b v
                       | .kLam => scanLamExpr b v
                       | .kForallE => scanForallExpr b v
                       | .kLetE => scanLetExpr b v
                       | .kConst => scanConstExpr b v
                       | _ => scanProjExpr b v) with
                | .err e => .err e
                | .ok r e =>
                  if ks < e then scanLineLoop b e false idxKind idx (.expr r)
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kNatVal =>
              if !pl.isAbsent then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanQuotedNat b v with
                | .err e => .err e
                | .ok n e =>
                  if ks < e then scanLineLoop b e false idxKind idx (.expr (.natVal n))
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kStrVal =>
              if !pl.isAbsent then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match scanString b v with
                | .err e => .err e
                | .ok str e =>
                  if ks < e then scanLineLoop b e false idxKind idx (.expr (.strVal str))
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kAxiom | .kDef | .kThm | .kOpaque | .kQuot | .kInductive =>
              if !pl.isAbsent then .err ⟨ks.toNat, .duplicateKey⟩
              else
                match (match k with
                       | .kAxiom => scanAxiomDecl b v
                       | .kDef => scanDefDecl b v
                       | .kThm => scanThmDecl b v
                       | .kOpaque => scanOpaqueDecl b v
                       | .kQuot => scanQuotDecl b v
                       | _ => scanIndDecl b v) with
                | .err e => .err e
                | .ok d e =>
                  if ks < e then scanLineLoop b e false idxKind idx (.decl d)
                  else .err ⟨ks.toNat, .noProgress⟩
            | .kMeta =>
              if !pl.isAbsent then .err ⟨ks.toNat, .duplicateKey⟩
              else if byteAt b v != 123 then .err ⟨v.toNat, .expectedObject⟩
              else if skipBraced b (v + 1) 0 == 0 then .err ⟨v.toNat, .expectedObject⟩
              else if ks < skipBraced b (v + 1) 0 then
                scanLineLoop b (skipBraced b (v + 1) 0) false idxKind idx .header
              else .err ⟨ks.toNat, .noProgress⟩
            | _ => .err ⟨ks.toNat, .unknownKey⟩) p w := by
  rw [scanLineLoop.eq_def]; rfl


/-- `scan_fast::scan_axiom_decl_loop` (con-leche: `scanAxiomDeclLoop`). -/
private theorem scan_axiom_decl_loop_refines {b : Slice Std.U8}
    (kf : KitFacts b) (K : ScanLineIngredients b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (isUns : Bool) (lps : alloc.vec.Vec Std.U64) (nm ty : Std.U64)
      (o : core.result.Result (frontend.scan_types.DeclRec × Std.Usize)
             frontend.scan_types.ScanErr),
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_axiom_decl_loop_loop w b i seen isUns lps nm ty = ok o →
      ScanSim absDeclRec o
        (scanAxiomDeclLoop (absBytes b) (absPos i) w (absU32 seen) isUns (absU64s lps) (absU64 nm) (absU64 ty)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i seen isUns lps nm ty o hf h
  rw [frontend.scan_fast.scan_axiom_decl_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hbody := fun (p : USize) (w' : Bool) =>
    scanAxiomDeclLoop_body (absBytes b) (absU32 seen) isUns (absU64s lps) (absU64 nm) (absU64 ty) p w'
  have hstep := nextMember_step kf hbody (b.length - i.val) i w res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err (MemberStep.err hstep)
  | Ok p =>
    obtain ⟨mem, ni, nw⟩ := p
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [MemberStep.close hstep]
      cases nw with
      | false =>
        rw [if_neg (show ¬ ((false : Bool) = true) by simp)] at h
        rw [Bool.false_and, if_neg (show ¬ ((false : Bool) = true) by simp)]
        exact close_mask 15 rfl rfl h
      | true =>
        rw [if_pos (show (true : Bool) = true from rfl)] at h
        rw [Bool.true_and, u32_bne (y := 0#u32) 0 rfl]
        by_cases hs : (seen != 0#u32) = true
        · rw [if_pos hs] at h
          rw [if_pos hs, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hs] at h
          rw [if_neg hs]
          exact close_mask 15 rfl rfl h
    | Key k ks v =>
      rw [MemberStep.key hstep]
      have hks : i.val ≤ ks.val :=
        next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
      have hib : i.val < b.length := next_member_lt hres
      cases k <;> simp only [absKey]
      all_goals
        (try (rw [err_val h]; exact ScanSim.err (ScanErrSim.mk rfl (by simp))))
      case KIsUnsafe =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 1#u32) 1 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_bool hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanBool (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanBool (absBytes b) (absPos v) = .ok x (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 1#u32) 1 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 x lps nm ty o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KLevelParams =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 2#u32) 2 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 2#u32) 2 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 isUns x nm ty o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KName =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 4#u32) 4 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanAxiomDeclLoop (absBytes b) e false (absU32 seen ||| 4) isUns (absU64s lps) n (absU64 ty)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 4#u32) 4 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 isUns lps x ty o
              (le_refl _) h
      case KType =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 8#u32) 8 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanAxiomDeclLoop (absBytes b) e false (absU32 seen ||| 8) isUns (absU64s lps) (absU64 nm) n) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 8#u32) 8 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 isUns lps nm x o
              (le_refl _) h

/-- `scan_fast::scan_def_decl_loop` (con-leche: `scanDefDeclLoop`). -/
private theorem scan_def_decl_loop_refines {b : Slice Std.U8}
    (kf : KitFacts b) (K : ScanLineIngredients b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (hints : frontend.scan_types.HintsRec) (lps : alloc.vec.Vec Std.U64) (nm : Std.U64) (safety : alloc.vec.Vec Std.U32) (ty vl : Std.U64)
      (o : core.result.Result (frontend.scan_types.DeclRec × Std.Usize)
             frontend.scan_types.ScanErr),
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_def_decl_loop_loop w b i seen hints lps nm safety ty vl = ok o →
      ScanSim absDeclRec o
        (scanDefDeclLoop (absBytes b) (absPos i) w (absU32 seen) (absHintsRec hints) (absU64s lps) (absU64 nm) (absString safety) (absU64 ty) (absU64 vl)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i seen hints lps nm safety ty vl o hf h
  rw [frontend.scan_fast.scan_def_decl_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hbody := fun (p : USize) (w' : Bool) =>
    scanDefDeclLoop_body (absBytes b) (absU32 seen) (absHintsRec hints) (absU64s lps) (absU64 nm) (absString safety) (absU64 ty) (absU64 vl) p w'
  have hstep := nextMember_step kf hbody (b.length - i.val) i w res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err (MemberStep.err hstep)
  | Ok p =>
    obtain ⟨mem, ni, nw⟩ := p
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [MemberStep.close hstep]
      cases nw with
      | false =>
        rw [if_neg (show ¬ ((false : Bool) = true) by simp)] at h
        rw [Bool.false_and, if_neg (show ¬ ((false : Bool) = true) by simp)]
        exact close_mask 124 rfl rfl h
      | true =>
        rw [if_pos (show (true : Bool) = true from rfl)] at h
        rw [Bool.true_and, u32_bne (y := 0#u32) 0 rfl]
        by_cases hs : (seen != 0#u32) = true
        · rw [if_pos hs] at h
          rw [if_pos hs, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hs] at h
          rw [if_neg hs]
          exact close_mask 124 rfl rfl h
    | Key k ks v =>
      rw [MemberStep.key hstep]
      have hks : i.val ≤ ks.val :=
        next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
      have hib : i.val < b.length := next_member_lt hres
      cases k <;> simp only [absKey]
      all_goals
        (try (rw [err_val h]; exact ScanSim.err (ScanErrSim.mk rfl (by simp))))
      case KAll =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 1#u32) 1 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 1#u32) 1 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 hints lps nm safety ty vl o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KHints =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 2#u32) 2 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_hints hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanHints (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanHints (absBytes b) (absPos v) = .ok (absHintsRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 2#u32) 2 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 x lps nm safety ty vl o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KLevelParams =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 4#u32) 4 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 4#u32) 4 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 hints x nm safety ty vl o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KName =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 8#u32) 8 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanDefDeclLoop (absBytes b) e false (absU32 seen ||| 8) (absHintsRec hints) (absU64s lps) n (absString safety) (absU64 ty) (absU64 vl)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 8#u32) 8 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 hints lps x safety ty vl o
              (le_refl _) h
      case KSafety =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 16#u32) 16 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_string hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanString (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanString (absBytes b) (absPos v) = .ok (absString x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 16#u32) 16 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 hints lps nm x ty vl o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KType =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 32#u32) 32 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanDefDeclLoop (absBytes b) e false (absU32 seen ||| 32) (absHintsRec hints) (absU64s lps) (absU64 nm) (absString safety) n (absU64 vl)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 32#u32) 32 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 hints lps nm safety x vl o
              (le_refl _) h
      case KValue =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 64#u32) 64 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanDefDeclLoop (absBytes b) e false (absU32 seen ||| 64) (absHintsRec hints) (absU64s lps) (absU64 nm) (absString safety) (absU64 ty) n) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 64#u32) 64 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 hints lps nm safety ty x o
              (le_refl _) h

/-- `scan_fast::scan_thm_decl_loop` (con-leche: `scanThmDeclLoop`). -/
private theorem scan_thm_decl_loop_refines {b : Slice Std.U8}
    (kf : KitFacts b) (K : ScanLineIngredients b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (lps : alloc.vec.Vec Std.U64) (nm ty vl : Std.U64)
      (o : core.result.Result (frontend.scan_types.DeclRec × Std.Usize)
             frontend.scan_types.ScanErr),
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_thm_decl_loop_loop w b i seen lps nm ty vl = ok o →
      ScanSim absDeclRec o
        (scanThmDeclLoop (absBytes b) (absPos i) w (absU32 seen) (absU64s lps) (absU64 nm) (absU64 ty) (absU64 vl)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i seen lps nm ty vl o hf h
  rw [frontend.scan_fast.scan_thm_decl_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hbody := fun (p : USize) (w' : Bool) =>
    scanThmDeclLoop_body (absBytes b) (absU32 seen) (absU64s lps) (absU64 nm) (absU64 ty) (absU64 vl) p w'
  have hstep := nextMember_step kf hbody (b.length - i.val) i w res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err (MemberStep.err hstep)
  | Ok p =>
    obtain ⟨mem, ni, nw⟩ := p
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [MemberStep.close hstep]
      cases nw with
      | false =>
        rw [if_neg (show ¬ ((false : Bool) = true) by simp)] at h
        rw [Bool.false_and, if_neg (show ¬ ((false : Bool) = true) by simp)]
        exact close_mask 30 rfl rfl h
      | true =>
        rw [if_pos (show (true : Bool) = true from rfl)] at h
        rw [Bool.true_and, u32_bne (y := 0#u32) 0 rfl]
        by_cases hs : (seen != 0#u32) = true
        · rw [if_pos hs] at h
          rw [if_pos hs, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hs] at h
          rw [if_neg hs]
          exact close_mask 30 rfl rfl h
    | Key k ks v =>
      rw [MemberStep.key hstep]
      have hks : i.val ≤ ks.val :=
        next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
      have hib : i.val < b.length := next_member_lt hres
      cases k <;> simp only [absKey]
      all_goals
        (try (rw [err_val h]; exact ScanSim.err (ScanErrSim.mk rfl (by simp))))
      case KAll =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 1#u32) 1 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 1#u32) 1 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 lps nm ty vl o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KLevelParams =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 2#u32) 2 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 2#u32) 2 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 x nm ty vl o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KName =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 4#u32) 4 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanThmDeclLoop (absBytes b) e false (absU32 seen ||| 4) (absU64s lps) n (absU64 ty) (absU64 vl)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 4#u32) 4 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 lps x ty vl o
              (le_refl _) h
      case KType =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 8#u32) 8 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanThmDeclLoop (absBytes b) e false (absU32 seen ||| 8) (absU64s lps) (absU64 nm) n (absU64 vl)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 8#u32) 8 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 lps nm x vl o
              (le_refl _) h
      case KValue =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 16#u32) 16 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanThmDeclLoop (absBytes b) e false (absU32 seen ||| 16) (absU64s lps) (absU64 nm) (absU64 ty) n) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 16#u32) 16 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 lps nm ty x o
              (le_refl _) h

/-- `scan_fast::scan_opaque_decl_loop` (con-leche: `scanOpaqueDeclLoop`). -/
private theorem scan_opaque_decl_loop_refines {b : Slice Std.U8}
    (kf : KitFacts b) (K : ScanLineIngredients b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (isUns : Bool) (lps : alloc.vec.Vec Std.U64) (nm ty vl : Std.U64)
      (o : core.result.Result (frontend.scan_types.DeclRec × Std.Usize)
             frontend.scan_types.ScanErr),
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_opaque_decl_loop_loop w b i seen isUns lps nm ty vl = ok o →
      ScanSim absDeclRec o
        (scanOpaqueDeclLoop (absBytes b) (absPos i) w (absU32 seen) isUns (absU64s lps) (absU64 nm) (absU64 ty) (absU64 vl)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i seen isUns lps nm ty vl o hf h
  rw [frontend.scan_fast.scan_opaque_decl_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hbody := fun (p : USize) (w' : Bool) =>
    scanOpaqueDeclLoop_body (absBytes b) (absU32 seen) isUns (absU64s lps) (absU64 nm) (absU64 ty) (absU64 vl) p w'
  have hstep := nextMember_step kf hbody (b.length - i.val) i w res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err (MemberStep.err hstep)
  | Ok p =>
    obtain ⟨mem, ni, nw⟩ := p
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [MemberStep.close hstep]
      cases nw with
      | false =>
        rw [if_neg (show ¬ ((false : Bool) = true) by simp)] at h
        rw [Bool.false_and, if_neg (show ¬ ((false : Bool) = true) by simp)]
        exact close_mask 62 rfl rfl h
      | true =>
        rw [if_pos (show (true : Bool) = true from rfl)] at h
        rw [Bool.true_and, u32_bne (y := 0#u32) 0 rfl]
        by_cases hs : (seen != 0#u32) = true
        · rw [if_pos hs] at h
          rw [if_pos hs, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hs] at h
          rw [if_neg hs]
          exact close_mask 62 rfl rfl h
    | Key k ks v =>
      rw [MemberStep.key hstep]
      have hks : i.val ≤ ks.val :=
        next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
      have hib : i.val < b.length := next_member_lt hres
      cases k <;> simp only [absKey]
      all_goals
        (try (rw [err_val h]; exact ScanSim.err (ScanErrSim.mk rfl (by simp))))
      case KAll =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 1#u32) 1 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 1#u32) 1 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 isUns lps nm ty vl o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KIsUnsafe =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 2#u32) 2 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_bool hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanBool (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanBool (absBytes b) (absPos v) = .ok x (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 2#u32) 2 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 x lps nm ty vl o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KLevelParams =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 4#u32) 4 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 4#u32) 4 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 isUns x nm ty vl o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KName =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 8#u32) 8 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanOpaqueDeclLoop (absBytes b) e false (absU32 seen ||| 8) isUns (absU64s lps) n (absU64 ty) (absU64 vl)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 8#u32) 8 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 isUns lps x ty vl o
              (le_refl _) h
      case KType =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 16#u32) 16 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanOpaqueDeclLoop (absBytes b) e false (absU32 seen ||| 16) isUns (absU64s lps) (absU64 nm) n (absU64 vl)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 16#u32) 16 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 isUns lps nm x vl o
              (le_refl _) h
      case KValue =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 32#u32) 32 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanOpaqueDeclLoop (absBytes b) e false (absU32 seen ||| 32) isUns (absU64s lps) (absU64 nm) (absU64 ty) n) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 32#u32) 32 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 isUns lps nm ty x o
              (le_refl _) h

/-- `scan_fast::scan_quot_decl_loop` (con-leche: `scanQuotDeclLoop`). -/
private theorem scan_quot_decl_loop_refines {b : Slice Std.U8}
    (kf : KitFacts b) (K : ScanLineIngredients b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (kind : alloc.vec.Vec Std.U32) (lps : alloc.vec.Vec Std.U64) (nm ty : Std.U64)
      (o : core.result.Result (frontend.scan_types.DeclRec × Std.Usize)
             frontend.scan_types.ScanErr),
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_quot_decl_loop_loop w b i seen kind lps nm ty = ok o →
      ScanSim absDeclRec o
        (scanQuotDeclLoop (absBytes b) (absPos i) w (absU32 seen) (absString kind) (absU64s lps) (absU64 nm) (absU64 ty)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i seen kind lps nm ty o hf h
  rw [frontend.scan_fast.scan_quot_decl_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hbody := fun (p : USize) (w' : Bool) =>
    scanQuotDeclLoop_body (absBytes b) (absU32 seen) (absString kind) (absU64s lps) (absU64 nm) (absU64 ty) p w'
  have hstep := nextMember_step kf hbody (b.length - i.val) i w res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err (MemberStep.err hstep)
  | Ok p =>
    obtain ⟨mem, ni, nw⟩ := p
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [MemberStep.close hstep]
      cases nw with
      | false =>
        rw [if_neg (show ¬ ((false : Bool) = true) by simp)] at h
        rw [Bool.false_and, if_neg (show ¬ ((false : Bool) = true) by simp)]
        exact close_mask 15 rfl rfl h
      | true =>
        rw [if_pos (show (true : Bool) = true from rfl)] at h
        rw [Bool.true_and, u32_bne (y := 0#u32) 0 rfl]
        by_cases hs : (seen != 0#u32) = true
        · rw [if_pos hs] at h
          rw [if_pos hs, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hs] at h
          rw [if_neg hs]
          exact close_mask 15 rfl rfl h
    | Key k ks v =>
      rw [MemberStep.key hstep]
      have hks : i.val ≤ ks.val :=
        next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
      have hib : i.val < b.length := next_member_lt hres
      cases k <;> simp only [absKey]
      all_goals
        (try (rw [err_val h]; exact ScanSim.err (ScanErrSim.mk rfl (by simp))))
      case KKind =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 1#u32) 1 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_string hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanString (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanString (absBytes b) (absPos v) = .ok (absString x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 1#u32) 1 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 x lps nm ty o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KLevelParams =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 2#u32) 2 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 2#u32) 2 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 kind x nm ty o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KName =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 4#u32) 4 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanQuotDeclLoop (absBytes b) e false (absU32 seen ||| 4) (absString kind) (absU64s lps) n (absU64 ty)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 4#u32) 4 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 kind lps x ty o
              (le_refl _) h
      case KType =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 8#u32) 8 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanQuotDeclLoop (absBytes b) e false (absU32 seen ||| 8) (absString kind) (absU64s lps) (absU64 nm) n) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
            rw [u32_or_lit (y := 8#u32) 8 rfl hseen1]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e seen1 kind lps nm x o
              (le_refl _) h

/-- `scan_fast::scan_ind_decl_loop` (con-leche: `scanIndDeclLoop`). -/
private theorem scan_ind_decl_loop_refines {b : Slice Std.U8}
    (kf : KitFacts b) (K : ScanLineIngredients b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (ctors : alloc.vec.Vec frontend.scan_types.IndCtorRec) (recs : alloc.vec.Vec frontend.scan_types.IndRecRec) (types : alloc.vec.Vec frontend.scan_types.IndTypeRec)
      (o : core.result.Result (frontend.scan_types.DeclRec × Std.Usize)
             frontend.scan_types.ScanErr),
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_ind_decl_loop_loop w b i seen ctors recs types = ok o →
      ScanSim absDeclRec o
        (scanIndDeclLoop (absBytes b) (absPos i) w (absU32 seen) (absIndCtorRecs ctors) (absIndRecRecs recs) (absIndTypeRecs types)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i seen ctors recs types o hf h
  rw [frontend.scan_fast.scan_ind_decl_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hbody := fun (p : USize) (w' : Bool) =>
    scanIndDeclLoop_body (absBytes b) (absU32 seen) (absIndCtorRecs ctors) (absIndRecRecs recs) (absIndTypeRecs types) p w'
  have hstep := nextMember_step kf hbody (b.length - i.val) i w res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err (MemberStep.err hstep)
  | Ok p =>
    obtain ⟨mem, ni, nw⟩ := p
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [MemberStep.close hstep]
      cases nw with
      | false =>
        rw [if_neg (show ¬ ((false : Bool) = true) by simp)] at h
        rw [Bool.false_and, if_neg (show ¬ ((false : Bool) = true) by simp)]
        exact close_mask 26 rfl rfl h
      | true =>
        rw [if_pos (show (true : Bool) = true from rfl)] at h
        rw [Bool.true_and, u32_bne (y := 0#u32) 0 rfl]
        by_cases hs : (seen != 0#u32) = true
        · rw [if_pos hs] at h
          rw [if_pos hs, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hs] at h
          rw [if_neg hs]
          exact close_mask 26 rfl rfl h
    | Key k ks v =>
      rw [MemberStep.key hstep]
      have hks : i.val ≤ ks.val :=
        next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
      have hib : i.val < b.length := next_member_lt hres
      cases k <;> simp only [absKey]
      all_goals
        (try (rw [err_val h]; exact ScanSim.err (ScanErrSim.mk rfl (by simp))))
      case KAll =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 1#u32) 1 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 1#u32) 1 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 ctors recs types o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KCtors =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 2#u32) 2 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_ind_ctors hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanIndCtors (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanIndCtors (absBytes b) (absPos v) = .ok (absIndCtorRecs x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 2#u32) 2 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 x recs types o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KIsUnsafe =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 4#u32) 4 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_bool hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanBool (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanBool (absBytes b) (absPos v) = .ok x (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 4#u32) 4 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 ctors recs types o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KRecs =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 8#u32) 8 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_ind_recs hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanIndRecs (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanIndRecs (absBytes b) (absPos v) = .ok (absIndRecRecs x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 8#u32) 8 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 ctors x types o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KTypes =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        rw [dup_refines (bit := 16#u32) 16 rfl hb1]
        by_cases hd : b1 = true
        · rw [if_pos hd] at h
          rw [if_pos hd, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hd] at h
          rw [if_neg hd]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_ind_types hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanIndTypes (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanIndTypes (absBytes b) (absPos v) = .ok (absIndTypeRecs x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              obtain ⟨seen1, hseen1, h⟩ := bind_eq_ok_iff.mp h
              rw [u32_or_lit (y := 16#u32) 16 rfl hseen1]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e seen1 ctors recs x o
                (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))

/-- `scan_fast::scan_axiom_decl` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1922-1995 scanAxiomDecl`). -/
theorem scan_axiom_decl_refines {b : Slice Std.U8} (kf : KitFacts b) (K : ScanLineIngredients b)
    {i : Std.Usize} {o} (h : frontend.scan_fast.scan_axiom_decl b i = ok o) :
    ScanSim absDeclRec o (scanAxiomDecl (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_axiom_decl] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanAxiomDecl, ← byte_at_refines hc]
  by_cases hb : c = 123#u8
  · rw [if_pos hb] at h
    rw [if_pos (blit_eq 123 rfl hb)]
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    rw [frontend.scan_fast.scan_axiom_decl_loop] at h
    rw [← absPos_add_one hi1]
    have := scan_axiom_decl_loop_refines kf K (b.length - i1.val) true i1 0#u32 false (alloc.vec.Vec.new Std.U64) 0#u64 0#u64 o (le_refl _) h
    simpa [absU64s, absU32, absString, absHintsRec, absU64, absIndCtorRecs,
      absIndRecRecs, absIndTypeRecs, alloc.vec.Vec.new] using this
  · rw [if_neg hb] at h
    rw [if_neg (blit_ne 123 rfl hb), err_val h]
    exact ScanSim.err (ScanErrSim.mk rfl (by simp))

/-- `scan_fast::scan_def_decl` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1997-2100 scanDefDecl`). -/
theorem scan_def_decl_refines {b : Slice Std.U8} (kf : KitFacts b) (K : ScanLineIngredients b)
    {i : Std.Usize} {o} (h : frontend.scan_fast.scan_def_decl b i = ok o) :
    ScanSim absDeclRec o (scanDefDecl (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_def_decl] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanDefDecl, ← byte_at_refines hc]
  by_cases hb : c = 123#u8
  · rw [if_pos hb] at h
    rw [if_pos (blit_eq 123 rfl hb)]
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    rw [frontend.scan_fast.scan_def_decl_loop] at h
    rw [← absPos_add_one hi1]
    have := scan_def_decl_loop_refines kf K (b.length - i1.val) true i1 0#u32 (frontend.scan_types.HintsRec.Regular 0#u64) (alloc.vec.Vec.new Std.U64) 0#u64 (alloc.vec.Vec.new Std.U32) 0#u64 0#u64 o (le_refl _) h
    simpa [absU64s, absU32, absString, absHintsRec, absU64, absIndCtorRecs,
      absIndRecRecs, absIndTypeRecs, alloc.vec.Vec.new] using this
  · rw [if_neg hb] at h
    rw [if_neg (blit_ne 123 rfl hb), err_val h]
    exact ScanSim.err (ScanErrSim.mk rfl (by simp))

/-- `scan_fast::scan_thm_decl` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:2102-2183 scanThmDecl`). -/
theorem scan_thm_decl_refines {b : Slice Std.U8} (kf : KitFacts b) (K : ScanLineIngredients b)
    {i : Std.Usize} {o} (h : frontend.scan_fast.scan_thm_decl b i = ok o) :
    ScanSim absDeclRec o (scanThmDecl (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_thm_decl] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanThmDecl, ← byte_at_refines hc]
  by_cases hb : c = 123#u8
  · rw [if_pos hb] at h
    rw [if_pos (blit_eq 123 rfl hb)]
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    rw [frontend.scan_fast.scan_thm_decl_loop] at h
    rw [← absPos_add_one hi1]
    have := scan_thm_decl_loop_refines kf K (b.length - i1.val) true i1 0#u32 (alloc.vec.Vec.new Std.U64) 0#u64 0#u64 0#u64 o (le_refl _) h
    simpa [absU64s, absU32, absString, absHintsRec, absU64, absIndCtorRecs,
      absIndRecRecs, absIndTypeRecs, alloc.vec.Vec.new] using this
  · rw [if_neg hb] at h
    rw [if_neg (blit_ne 123 rfl hb), err_val h]
    exact ScanSim.err (ScanErrSim.mk rfl (by simp))

/-- `scan_fast::scan_opaque_decl` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:2185-2276 scanOpaqueDecl`). -/
theorem scan_opaque_decl_refines {b : Slice Std.U8} (kf : KitFacts b) (K : ScanLineIngredients b)
    {i : Std.Usize} {o} (h : frontend.scan_fast.scan_opaque_decl b i = ok o) :
    ScanSim absDeclRec o (scanOpaqueDecl (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_opaque_decl] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanOpaqueDecl, ← byte_at_refines hc]
  by_cases hb : c = 123#u8
  · rw [if_pos hb] at h
    rw [if_pos (blit_eq 123 rfl hb)]
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    rw [frontend.scan_fast.scan_opaque_decl_loop] at h
    rw [← absPos_add_one hi1]
    have := scan_opaque_decl_loop_refines kf K (b.length - i1.val) true i1 0#u32 false (alloc.vec.Vec.new Std.U64) 0#u64 0#u64 0#u64 o (le_refl _) h
    simpa [absU64s, absU32, absString, absHintsRec, absU64, absIndCtorRecs,
      absIndRecRecs, absIndTypeRecs, alloc.vec.Vec.new] using this
  · rw [if_neg hb] at h
    rw [if_neg (blit_ne 123 rfl hb), err_val h]
    exact ScanSim.err (ScanErrSim.mk rfl (by simp))

/-- `scan_fast::scan_quot_decl` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:2278-2350 scanQuotDecl`). -/
theorem scan_quot_decl_refines {b : Slice Std.U8} (kf : KitFacts b) (K : ScanLineIngredients b)
    {i : Std.Usize} {o} (h : frontend.scan_fast.scan_quot_decl b i = ok o) :
    ScanSim absDeclRec o (scanQuotDecl (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_quot_decl] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanQuotDecl, ← byte_at_refines hc]
  by_cases hb : c = 123#u8
  · rw [if_pos hb] at h
    rw [if_pos (blit_eq 123 rfl hb)]
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    rw [frontend.scan_fast.scan_quot_decl_loop] at h
    rw [← absPos_add_one hi1]
    have := scan_quot_decl_loop_refines kf K (b.length - i1.val) true i1 0#u32 (alloc.vec.Vec.new Std.U32) (alloc.vec.Vec.new Std.U64) 0#u64 0#u64 o (le_refl _) h
    simpa [absU64s, absU32, absString, absHintsRec, absU64, absIndCtorRecs,
      absIndRecRecs, absIndTypeRecs, alloc.vec.Vec.new] using this
  · rw [if_neg hb] at h
    rw [if_neg (blit_ne 123 rfl hb), err_val h]
    exact ScanSim.err (ScanErrSim.mk rfl (by simp))

/-- `scan_fast::scan_ind_decl` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:2352-2436 scanIndDecl`). -/
theorem scan_ind_decl_refines {b : Slice Std.U8} (kf : KitFacts b) (K : ScanLineIngredients b)
    {i : Std.Usize} {o} (h : frontend.scan_fast.scan_ind_decl b i = ok o) :
    ScanSim absDeclRec o (scanIndDecl (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_ind_decl] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanIndDecl, ← byte_at_refines hc]
  by_cases hb : c = 123#u8
  · rw [if_pos hb] at h
    rw [if_pos (blit_eq 123 rfl hb)]
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    rw [frontend.scan_fast.scan_ind_decl_loop] at h
    rw [← absPos_add_one hi1]
    have := scan_ind_decl_loop_refines kf K (b.length - i1.val) true i1 0#u32 (alloc.vec.Vec.new frontend.scan_types.IndCtorRec) (alloc.vec.Vec.new frontend.scan_types.IndRecRec) (alloc.vec.Vec.new frontend.scan_types.IndTypeRec) o (le_refl _) h
    simpa [absU64s, absU32, absString, absHintsRec, absU64, absIndCtorRecs,
      absIndRecRecs, absIndTypeRecs, alloc.vec.Vec.new] using this
  · rw [if_neg hb] at h
    rw [if_neg (blit_ne 123 rfl hb), err_val h]
    exact ScanSim.err (ScanErrSim.mk rfl (by simp))

/-- `scan_fast::scan_line_loop` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:2464-2621 scanLineLoop`).  The dispatcher:
one index key, one payload key, matched at the closing brace. -/
private theorem scan_line_loop_loop_refines {b : Slice Std.U8}
    (kf : KitFacts b) (K : ScanLineIngredients b) (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (idx_kind : Std.U8) (idx : Std.U64)
      (pl : frontend.scan_fast.LinePayload)
      (o : core.result.Result (frontend.scan_types.LineRec × Std.Usize)
             frontend.scan_types.ScanErr),
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_line_loop_loop w b i idx_kind idx pl = ok o →
      ScanSim absLineRec o
        (scanLineLoop (absBytes b) (absPos i) w (absByte idx_kind) (absU64 idx)
          (absLinePayload pl)) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro w i idx_kind idx pl o hf h
  rw [frontend.scan_fast.scan_line_loop_loop.eq_def] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
  have hbody := fun (p : USize) (w' : Bool) =>
    scanLineLoop_body (absBytes b) (absByte idx_kind) (absU64 idx) (absLinePayload pl) p w'
  have hstep := nextMember_step kf hbody (b.length - i.val) i w res (le_refl _) hres
  cases res with
  | Err er =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ScanSim.err (MemberStep.err hstep)
  | Ok p =>
    obtain ⟨mem, ni, nw⟩ := p
    simp only [uncurry_apply_pair] at h
    cases mem with
    | Close =>
      rw [MemberStep.close hstep, u8_bne (y := 0#u8) 0 rfl]
      cases nw with
      | false =>
        rw [if_neg (show ¬ ((false : Bool) = true) by simp)] at h
        rw [Bool.false_and, if_neg (show ¬ ((false : Bool) = true) by simp)]
        exact close_line h
      | true =>
        rw [if_pos (show (true : Bool) = true from rfl)] at h
        rw [Bool.true_and]
        by_cases hk0 : (idx_kind != 0#u8) = true
        · rw [if_pos hk0] at h
          rw [hk0, Bool.true_or, if_pos rfl, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hk0] at h
          rw [show (idx_kind != 0#u8) = false by rw [← Bool.not_eq_true]; exact hk0,
            Bool.false_or]
          obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
          have hb1' := line_payload_is_absent_refines hb1
          rw [← hb1']
          by_cases ha : b1 = true
          · rw [if_pos ha] at h
            rw [if_neg (by simp [ha])]
            exact close_line h
          · rw [if_neg ha] at h
            rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
            exact ScanSim.err (ScanErrSim.mk rfl (by simp))
    | Key k ks v =>
      rw [MemberStep.key hstep]
      have hks : i.val ≤ ks.val :=
        next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
      have hib : i.val < b.length := next_member_lt hres
      cases k <;> simp only [absKey]
      all_goals (try dsimp only at h)
      all_goals
        (try (rw [err_val h]; exact ScanSim.err (ScanErrSim.mk rfl (by simp))))
      case KIn =>
        rw [u8_bne (y := 0#u8) 0 rfl]
        by_cases hk : (idx_kind != 0#u8) = true
        · rw [if_pos hk] at h
          rw [if_pos hk, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hk] at h
          rw [if_neg hk]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanLineLoop (absBytes b) e false 1 n (absLinePayload pl)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e 1#u8 x pl o (le_refl _) h
      case KIl =>
        rw [u8_bne (y := 0#u8) 0 rfl]
        by_cases hk : (idx_kind != 0#u8) = true
        · rw [if_pos hk] at h
          rw [if_pos hk, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hk] at h
          rw [if_neg hk]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanLineLoop (absBytes b) e false 2 n (absLinePayload pl)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e 2#u8 x pl o (le_refl _) h
      case KIe =>
        rw [u8_bne (y := 0#u8) 0 rfl]
        by_cases hk : (idx_kind != 0#u8) = true
        · rw [if_pos hk] at h
          rw [if_pos hk, err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg hk] at h
          rw [if_neg hk]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanLineLoop (absBytes b) e false 3 n (absLinePayload pl)) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e 3#u8 x pl o (le_refl _) h
      case KBvar =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanLineLoop (absBytes b) e false (absByte idx_kind) (absU64 idx) (.expr (.bvar n))) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e idx_kind idx
              (frontend.scan_fast.LinePayload.Expr (frontend.scan_types.ExprRec.Bvar x)) o (le_refl _) h
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KSort =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanLineLoop (absBytes b) e false (absByte idx_kind) (absU64 idx) (.expr (.sort n))) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e idx_kind idx
              (frontend.scan_fast.LinePayload.Expr (frontend.scan_types.ExprRec.Sort x)) o (le_refl _) h
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KSucc =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanLineLoop (absBytes b) e false (absByte idx_kind) (absU64 idx) (.level (.succ n))) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e idx_kind idx
              (frontend.scan_fast.LinePayload.Level (frontend.scan_types.LevelRec.Succ x)) o (le_refl _) h
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KParam =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsl := natSlot_step (K := fun n e =>
            scanLineLoop (absBytes b) e false (absByte idx_kind) (absU64 idx) (.level (.param n))) hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ScanSim.err (NatSlotStep.err hsl)
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            simp only [uncurry_apply_pair] at h
            rw [NatSlotStep.ok hsl]
            have hlt : ks.val < e.val := slot_nat_prog hr1
            exact ih (b.length - e.val) (by omega) false e idx_kind idx
              (frontend.scan_fast.LinePayload.Level (frontend.scan_types.LevelRec.Param x)) o (le_refl _) h
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KApp =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_app_expr hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanAppExpr (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanAppExpr (absBytes b) (absPos v) = .ok (absExprRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Expr x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KLam =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_lam_expr hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanLamExpr (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanLamExpr (absBytes b) (absPos v) = .ok (absExprRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Expr x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KForallE =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_forall_expr hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanForallExpr (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanForallExpr (absBytes b) (absPos v) = .ok (absExprRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Expr x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KLetE =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_let_expr hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanLetExpr (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanLetExpr (absBytes b) (absPos v) = .ok (absExprRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Expr x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KConst =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_const_expr hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanConstExpr (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanConstExpr (absBytes b) (absPos v) = .ok (absExprRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Expr x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KProj =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_proj_expr hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanProjExpr (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanProjExpr (absBytes b) (absPos v) = .ok (absExprRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Expr x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KNatVal =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_quoted_nat hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanQuotedNat (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanQuotedNat (absBytes b) (absPos v) = .ok (natOfDigits x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Expr (frontend.scan_types.ExprRec.NatVal x)) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KStrVal =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_string hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanString (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanString (absBytes b) (absPos v) = .ok (absString x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Expr (frontend.scan_types.ExprRec.StrVal x)) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KAxiom =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := scan_axiom_decl_refines kf K hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanAxiomDecl (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanAxiomDecl (absBytes b) (absPos v) = .ok (absDeclRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Decl x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KDef =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := scan_def_decl_refines kf K hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanDefDecl (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanDefDecl (absBytes b) (absPos v) = .ok (absDeclRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Decl x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KThm =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := scan_thm_decl_refines kf K hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanThmDecl (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanThmDecl (absBytes b) (absPos v) = .ok (absDeclRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Decl x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KOpaque =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := scan_opaque_decl_refines kf K hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanOpaqueDecl (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanOpaqueDecl (absBytes b) (absPos v) = .ok (absDeclRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Decl x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KQuot =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := scan_quot_decl_refines kf K hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanQuotDecl (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanQuotDecl (absBytes b) (absPos v) = .ok (absDeclRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Decl x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KInductive =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := scan_ind_decl_refines kf K hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanIndDecl (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanIndDecl (absBytes b) (absPos v) = .ok (absDeclRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b2 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb2).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Decl x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KStr =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2' : b2 = true := by
            have hkb : frontend.scan_types.key_beq frontend.scan_types.Key.KStr
                frontend.scan_types.Key.KStr = ok true := by
              simp [frontend.scan_types.key_beq, frontend.scan_types.key_code]
            rw [hkb] at hb2
            exact (Result.ok_injective hb2).symm
          rw [if_pos hb2'] at h
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_str_name hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanStrName (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanStrName (absBytes b) (absPos v) = .ok (absNameRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b3 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb3).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb3).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Name x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb3).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KNum =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2' : b2 = false := by
            have hkb : frontend.scan_types.key_beq frontend.scan_types.Key.KNum
                frontend.scan_types.Key.KStr = ok false := by
              simp [frontend.scan_types.key_beq, frontend.scan_types.key_code]
            rw [hkb] at hb2
            exact (Result.ok_injective hb2).symm
          rw [if_neg (by simp [hb2'])] at h
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_num_name hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNumName (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨x, e⟩ := p1
            have hsb' : scanNumName (absBytes b) (absPos v) = .ok (absNameRec x) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
            by_cases hp : b3 = true
            · rw [if_pos hp] at h
              rw [if_pos ((prog_iff hb3).mp hp)]
              have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb3).mp hp)
              exact ih (b.length - e.val) (by omega) false e idx_kind idx
                (frontend.scan_fast.LinePayload.Name x) o (le_refl _) h
            · rw [if_neg hp] at h
              rw [if_neg (fun hc => hp ((prog_iff hb3).mpr hc)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))

      case KMax =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨us, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s us) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            by_cases hl : us.val.length = 2
            · obtain ⟨a0, a1, hus⟩ := List.length_eq_two.mp hl
              rw [if_neg (show ¬ ((alloc.vec.Vec.len us != 2#usize) = true) by
                simp only [bne_iff_ne, ne_eq, not_not]
                have : (alloc.vec.Vec.len us).val = 2 := by
                  rw [alloc.vec.Vec.len_val, alloc.vec.Vec.length, hl]
                scalar_tac)] at h
              obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
              by_cases hp : b2 = true
              · rw [if_pos hp] at h
                obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
                have hb3' : b3 = true := by
                  have hkb : frontend.scan_types.key_beq frontend.scan_types.Key.KMax
                      frontend.scan_types.Key.KMax = ok true := by
                    simp [frontend.scan_types.key_beq, frontend.scan_types.key_code]
                  rw [hkb] at hb3
                  exact (Result.ok_injective hb3).symm
                rw [if_pos hb3'] at h
                obtain ⟨x0, hx0, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨x1, hx1, h⟩ := bind_eq_ok_iff.mp h
                have h0 : x0 = a0 := by
                  have := vec_index_get? hx0
                  rw [hus] at this; simpa using this.symm
                have h1 : x1 = a1 := by
                  have := vec_index_get? hx1
                  rw [hus] at this; simpa using this.symm
                simp only [show absU64s us = [absU64 a0, absU64 a1] by
                  simp [absU64s, hus]]
                rw [if_pos ((prog_iff hb2).mp hp)]
                have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
                rw [← h0, ← h1]
                exact ih (b.length - e.val) (by omega) false e idx_kind idx
                  (frontend.scan_fast.LinePayload.Level
                    (frontend.scan_types.LevelRec.Max x0 x1)) o (le_refl _) h
              · rw [if_neg hp] at h
                simp only [show absU64s us = [absU64 a0, absU64 a1] by
                  simp [absU64s, hus]]
                rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
                exact ScanSim.err (ScanErrSim.mk rfl (by simp))
            · rw [if_pos (show ((alloc.vec.Vec.len us != 2#usize) = true) by
                simp only [bne_iff_ne, ne_eq]
                intro hc
                apply hl
                have hv2 : (alloc.vec.Vec.len us).val = (2#usize : Std.Usize).val := by
                  rw [hc]
                rw [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at hv2
                simpa using hv2)] at h
              rw [err_val h]
              refine ScanSim.err (ScanErrSim.mk rfl ?_)
              rcases hv : us.val with _ | ⟨c0, l1⟩
              · simp [absU64s, hv]
              · rcases l1 with _ | ⟨c1, l2⟩
                · simp [absU64s, hv]
                · rcases l2 with _ | ⟨c2, l3⟩
                  · exact absurd (by rw [hv]; rfl) hl
                  · simp [absU64s, hv]
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KImax =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
          have hsb := K.scan_nat_list hr1
          cases r1 with
          | Err er =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine ScanSim.err ?_
            intro le hle
            have hse : ScanErrSim er (scanNatList (absBytes b) (absPos v)) := hsb
            rw [hse le hle]
          | Ok p1 =>
            obtain ⟨us, e⟩ := p1
            have hsb' : scanNatList (absBytes b) (absPos v) = .ok (absU64s us) (absPos e) := hsb
            simp only [uncurry_apply_pair] at h
            simp only [hsb']
            by_cases hl : us.val.length = 2
            · obtain ⟨a0, a1, hus⟩ := List.length_eq_two.mp hl
              rw [if_neg (show ¬ ((alloc.vec.Vec.len us != 2#usize) = true) by
                simp only [bne_iff_ne, ne_eq, not_not]
                have : (alloc.vec.Vec.len us).val = 2 := by
                  rw [alloc.vec.Vec.len_val, alloc.vec.Vec.length, hl]
                scalar_tac)] at h
              obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
              by_cases hp : b2 = true
              · rw [if_pos hp] at h
                obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
                have hb3' : b3 = false := by
                  have hkb : frontend.scan_types.key_beq frontend.scan_types.Key.KImax
                      frontend.scan_types.Key.KMax = ok false := by
                    simp [frontend.scan_types.key_beq, frontend.scan_types.key_code]
                  rw [hkb] at hb3
                  exact (Result.ok_injective hb3).symm
                rw [if_neg (by simp [hb3'])] at h
                obtain ⟨x0, hx0, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨x1, hx1, h⟩ := bind_eq_ok_iff.mp h
                have h0 : x0 = a0 := by
                  have := vec_index_get? hx0
                  rw [hus] at this; simpa using this.symm
                have h1 : x1 = a1 := by
                  have := vec_index_get? hx1
                  rw [hus] at this; simpa using this.symm
                simp only [show absU64s us = [absU64 a0, absU64 a1] by
                  simp [absU64s, hus]]
                rw [if_pos ((prog_iff hb2).mp hp)]
                have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
                rw [← h0, ← h1]
                exact ih (b.length - e.val) (by omega) false e idx_kind idx
                  (frontend.scan_fast.LinePayload.Level
                    (frontend.scan_types.LevelRec.Imax x0 x1)) o (le_refl _) h
              · rw [if_neg hp] at h
                simp only [show absU64s us = [absU64 a0, absU64 a1] by
                  simp [absU64s, hus]]
                rw [if_neg (fun hc => hp ((prog_iff hb2).mpr hc)), err_val h]
                exact ScanSim.err (ScanErrSim.mk rfl (by simp))
            · rw [if_pos (show ((alloc.vec.Vec.len us != 2#usize) = true) by
                simp only [bne_iff_ne, ne_eq]
                intro hc
                apply hl
                have hv2 : (alloc.vec.Vec.len us).val = (2#usize : Std.Usize).val := by
                  rw [hc]
                rw [alloc.vec.Vec.len_val, alloc.vec.Vec.length] at hv2
                simpa using hv2)] at h
              rw [err_val h]
              refine ScanSim.err (ScanErrSim.mk rfl ?_)
              rcases hv : us.val with _ | ⟨c0, l1⟩
              · simp [absU64s, hv]
              · rcases l1 with _ | ⟨c1, l2⟩
                · simp [absU64s, hv]
                · rcases l2 with _ | ⟨c2, l3⟩
                  · exact absurd (by rw [hv]; rfl) hl
                  · simp [absU64s, hv]
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      case KMeta =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1' := line_payload_is_absent_refines hb1
        rw [← hb1']
        by_cases ha : b1 = true
        · rw [if_pos ha] at h
          rw [if_neg (by simp [ha])]
          obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
          rw [← byte_at_refines hc1, u8_bne (y := 123#u8) 123 rfl]
          by_cases hc : (c1 != 123#u8) = true
          · rw [if_pos hc] at h
            rw [if_pos hc, err_val h]
            exact ScanSim.err (ScanErrSim.mk rfl (by simp))
          · rw [if_neg hc] at h
            rw [if_neg hc]
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
            have hsk : skipBraced (absBytes b) (absPos v + 1) 0 = absPos e := by
              rw [← absPos_add_one hi2]; exact (K.skip_braced he).symm
            rw [hsk, p_beq0]
            by_cases he0 : e = 0#usize
            · rw [if_pos he0] at h
              rw [if_pos (by simp [he0]), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
            · rw [if_neg he0] at h
              rw [if_neg (by simp [he0])]
              obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
              by_cases hp : b2 = true
              · rw [if_pos hp] at h
                rw [if_pos ((prog_iff hb2).mp hp)]
                have hlt : ks.val < e.val := absPos_lt.mp ((prog_iff hb2).mp hp)
                exact ih (b.length - e.val) (by omega) false e idx_kind idx
                  frontend.scan_fast.LinePayload.Header o (le_refl _) h
              · rw [if_neg hp] at h
                rw [if_neg (fun hcc => hp ((prog_iff hb2).mpr hcc)), err_val h]
                exact ScanSim.err (ScanErrSim.mk rfl (by simp))
        · rw [if_neg ha] at h
          rw [if_pos (by simp only [Bool.not_eq_true] at ha; simp [ha]), err_val h]
          exact ScanSim.err (ScanErrSim.mk rfl (by simp))

/-- `scan_fast::scan_line_loop` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:2464-2621 scanLineLoop` at its initial
state). -/
theorem scan_line_loop_refines {b : Slice Std.U8} (kf : KitFacts b)
    (K : ScanLineIngredients b) {i : Std.Usize} {o}
    (h : frontend.scan_fast.scan_line_loop b i = ok o) :
    ScanSim absLineRec o (scanLineLoop (absBytes b) (absPos i) true 0 0 .absent) := by
  rw [frontend.scan_fast.scan_line_loop] at h
  exact scan_line_loop_loop_refines kf K (b.length - i.val) true i 0#u8 0#u64
    frontend.scan_fast.LinePayload.Absent o (le_refl _) h

/-- **The capstone of the scanner tier.**  `scan_fast::scan_line_fwd`
(con-leche: `ConLeche/Frontend/Scan/Fast.lean:2622-2638 scanLineFwd`): for the
same bytes the port reads the record con-leche reads, stops where con-leche
stops, and fails where con-leche fails. -/
theorem scan_line_fwd_refines {b : Slice Std.U8} (kf : KitFacts b)
    (K : ScanLineIngredients b) {i : Std.Usize} {o}
    (h : frontend.scan_fast.scan_line_fwd b i = ok o) :
    ScanSim absLineRec o (scanLineFwd (absBytes b) (absPos i)) := by
  rw [frontend.scan_fast.scan_line_fwd] at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [scanLineFwd, ← skip_ws_refines hs, ← byte_at_refines hc]
  by_cases h10 : c = 10#u8
  · rw [if_pos h10] at h
    rw [if_pos (blit_eq 10 rfl h10)]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    exact ScanSim.ok (by rw [absPos_add_one hi2]; try rfl)
  · rw [if_neg h10] at h
    rw [if_neg (blit_ne 10 rfl h10)]
    by_cases hend : Slice.len b ≤ s
    · rw [if_pos hend] at h
      rw [if_pos (usize_le_absPos.mpr (by scalar_tac))]
      rw [← Result.ok_injective h]
      exact ScanSim.ok (by rfl)
    · rw [if_neg hend] at h
      rw [if_neg (fun hcc => hend (by
        have := usize_le_absPos.mp hcc; scalar_tac))]
      by_cases h123 : c = 123#u8
      · rw [if_neg (show ¬ ((c != 123#u8) = true) by simp [h123])] at h
        rw [if_neg (show ¬ ((absByte c != (123 : UInt8)) = true) by
          rw [u8_bne (y := 123#u8) 123 rfl]; simp [h123])]
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
        have hlp := scan_line_loop_refines kf K hr
        rw [← absPos_add_one hi3]
        cases r with
        | Err er =>
          simp only [Result.ok.injEq] at h
          rw [← h]
          refine ScanSim.err ?_
          intro le hle
          have hse : ScanErrSim er
            (scanLineLoop (absBytes b) (absPos i3) true 0 0 .absent) := hlp
          rw [hse le hle]
        | Ok p =>
          obtain ⟨r1, j⟩ := p
          have hlp' : scanLineLoop (absBytes b) (absPos i3) true 0 0 .absent
              = .ok (absLineRec r1) (absPos j) := hlp
          simp only [uncurry_apply_pair] at h
          simp only [hlp']
          obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨c2, hc2, h⟩ := bind_eq_ok_iff.mp h
          rw [← skip_ws_refines hp1, ← byte_at_refines hc2]
          by_cases h10' : c2 = 10#u8
          · rw [if_pos h10'] at h
            rw [if_pos (blit_eq 10 rfl h10')]
            obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
            rw [← Result.ok_injective h]
            exact ScanSim.ok (by rw [absPos_add_one hi5]; try rfl)
          · rw [if_neg h10'] at h
            rw [if_neg (blit_ne 10 rfl h10')]
            by_cases hend' : Slice.len b ≤ p1
            · rw [if_pos hend'] at h
              rw [if_pos (usize_le_absPos.mpr (by scalar_tac))]
              rw [← Result.ok_injective h]
              exact ScanSim.ok (by rfl)
            · rw [if_neg hend'] at h
              rw [if_neg (fun hcc => hend' (by
                have := usize_le_absPos.mp hcc; scalar_tac)), err_val h]
              exact ScanSim.err (ScanErrSim.mk rfl (by simp))
      · rw [if_pos (show ((c != 123#u8) = true) by simp [h123])] at h
        rw [if_pos (show ((absByte c != (123 : UInt8)) = true) by
          rw [u8_bne (y := 123#u8) 123 rfl]; simp [h123]), err_val h]
        exact ScanSim.err (ScanErrSim.mk rfl (by simp))

-- The census is the standard three.  Task #86 spelled the scanner's
-- sixty-eight key literals as `[u8; N]` arrays, so nothing in `key_at` or
-- `scan_bool` carries Aeneas's `decide +native` bound any more and this
-- statement, which names `scan_line_fwd` and `scanLineFwd`, inherits none.

end ConRon.Refine.Frontend
