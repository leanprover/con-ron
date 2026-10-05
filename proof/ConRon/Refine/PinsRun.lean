/-
`kernel::pins_decode`'s payload record and pass against
`ConRon.Refine.PinsDec` — half (A) of task #64's decoder refinement, the top.

`record_pin_set` is the one record that builds a `NatOpPinSet`; the pass
(`run_records`, `run_footer`) is the one recursion whose step is a record of
unknown length, so it is where `PinsDec.runRecords`' fuel is discharged: the
model's index `i` moves forward by at least one byte per record, so
`t.length - i.val` is a budget and `decode` passes `t.length`, which is at
least that.

`decode_refines` is this file's product and the whole of (A), over the model's
**whole** outcome (task #67):

    decode t = ok o → match o with
                      | .Ok v  => PinsDec.decode (bytesOf t) = some (absPins v)
                      | .Err ce => absErrKind ce = none

The failure branch claims *nothing*, and has to: `kernel::pins_decode` is the
one module whose errors are wholly the port's own — con-leche has no decoder to
mirror, its `natOpPinSets` being elaboration-time data — so all twenty-eight
throws go through `pins_decode::bad_text`, a `CheckError::Native`.
`Refine/PinsBytes.lean`'s module note and `bad_text_native`/`err_native` pin
that down; `ErrSim.of_none` is what turns `absErrKind ce = none` into an
`ErrSim` at a caller.

(B), `PinsDec` against the reader, and `Refine/Pins.lean`, which composed the
two, were deleted at task #105: nothing used either.
-/
import ConRon.Refine.Env
import ConRon.Refine.PinsRecords

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.PinsRun

open ConRon.Refine ConRon.Refine.PinsDec ConRon.Refine.PinsBytes
open ConRon.Refine.PinsRecords

/-! ## Plumbing

The four facts every proof below spends: how a `bytesFrom` suffix splits at an
in-range index, what a machine-word step does to the index it names, and how a
`Vec` read and an eight-element `Vec` are taken apart.  `Refine/PinsBytes.lean`
keeps private copies of the first two; they are three lines each and importing
`Refine/HashMap.lean` for the scalar ones would pull the whole memo-table
development into the decoder's dependency cone. -/

private theorem usub_eq {ty : Std.UScalarTy} {x y z : Std.UScalar ty}
    (h : x - y = ok z) : z.val = x.val - y.val := by
  have := Std.UScalar.sub_equiv x y
  rw [h] at this; simp at this; omega

private theorem vec_index_ok {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (hi : i.val < v.length) :
    alloc.vec.Vec.index_usize v i = ok v.val[i.val] := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hi)
  rw [hy, hyv]

/-- The model's `v[i]`, in the forward `= ok` form, from the list read. -/
private theorem vec_index_eq {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (hx : v.val[i.val]? = some x) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x := by
  have hi : i.val < v.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hx
    simp at hx
  rw [alloc.vec.Vec.index_slice_index, vec_index_ok hi]
  rw [List.getElem?_eq_getElem hi] at hx
  exact congrArg ok (Option.some.inj hx)

/-- An eight-element list is eight elements: what turns the model's `len() = 8`
guard into the eight-element pattern `PinsDec.recordPinSet` matches on. -/
private theorem eight_cases {α : Type} {l : List α} (h : l.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, l = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  rcases l with _ | ⟨a0, l⟩; · simp at h
  rcases l with _ | ⟨a1, l⟩; · simp at h
  rcases l with _ | ⟨a2, l⟩; · simp at h
  rcases l with _ | ⟨a3, l⟩; · simp at h
  rcases l with _ | ⟨a4, l⟩; · simp at h
  rcases l with _ | ⟨a5, l⟩; · simp at h
  rcases l with _ | ⟨a6, l⟩; · simp at h
  rcases l with _ | ⟨a7, l⟩; · simp at h
  rcases l with _ | ⟨a8, l⟩
  · exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
  · simp at h

/-- `expr::dup` is `Arc::clone`, the identity, in the forward `= ok` form. -/
private theorem expr_dup_ok (e : expr.Expr) : expr.dup e = ok e := by
  cases e; simp [expr.dup]

/-! ## `S` — the payload record -/

/-- `pins_eight_from`'s counter recursion, with the counter bounded by a `Nat`
the induction runs on.  The `i.val ≤ t.length` hypothesis is what the `k = 0`
base case needs: there the reader stops where it started, so the index bound
cannot come from a read. -/
private theorem pins_eight_from_aux {t : Slice Std.U8} {tb : pins_decode.Tables} :
    ∀ (n : Nat) (k i : Std.Usize) (out : alloc.vec.Vec expr.Expr)
      (o : core.result.Result (alloc.vec.Vec expr.Expr × Std.Usize) core_types.CheckError),
      k.val ≤ n →
      pins_decode.pins_eight_from t i tb k out = ok o →
      match o with
      | .Ok (es, j) =>
        i.val ≤ t.length →
      PinsDec.pinsEightFrom (bytesFrom t i) (absTables tb) k.val (absExprs out)
          = some (absExprs es, bytesFrom t j)
            ∧ i.val ≤ j.val ∧ j.val ≤ t.length
      | .Err ce => absErrKind ce = none := by
  intro n
  induction n with
  | zero =>
    intro k i out o hk h
    have hk0 : k.val = 0 := by omega
    rw [pins_decode.pins_eight_from.eq_def] at h
    rw [ite_eq_left (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    intro hi
    exact ⟨by rw [hk0]; rfl, le_refl _, hi⟩
  | succ n ih =>
    intro k i out o hk h
    rw [pins_decode.pins_eight_from.eq_def] at h
    split at h
    · rename_i hk0
      have hk0' : k.val = 0 := by rw [hk0]; rfl
      simp only [Result.ok.injEq] at h
      subst h
      intro hi
      exact ⟨by rw [hk0']; rfl, le_refl _, hi⟩
    · rename_i hk0
      have hkpos : 0 < k.val := by
        rcases Nat.eq_zero_or_pos k.val with _ | hp
        · exact absurd (by scalar_tac : k = 0#usize) hk0
        · exact hp
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h
        subst h
        exact after_space_refines hr
      | Ok j1 =>
        obtain ⟨hsp, hij1, hj1t⟩ := after_space_refines hr
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e =>
          simp only [Result.ok.injEq] at h
          subst h
          exact expr_ref_refines hr1
        | Ok p =>
          obtain ⟨e, m⟩ := p
          obtain ⟨href, hj1m, hmt⟩ := expr_ref_refines hr1
          obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
          have hk1v : k1.val = k.val - 1 := usub_eq hk1
          cases o with
          | Err ce => exact ih k1 m out1 _ (by omega) h
          | Ok pr =>
          obtain ⟨es, j⟩ := pr
          intro hi
          obtain ⟨hrec, hmj, hjt⟩ := (ih k1 m out1 _ (by omega) h) hmt
          refine ⟨?_, by omega, hjt⟩
          rw [show k.val = k1.val + 1 by omega]
          rw [show absExprs out1 = absExprs out ++ [absExpr e] by
            rw [absExprs, vec_push_val hout1]; simp [absExprs]] at hrec
          simp only [PinsDec.pinsEightFrom, hsp, href]
          exact hrec

/-- A non-trivial counter makes the reader read, and a read bounds its index:
what supplies `pins_eight_from_aux`'s hypothesis at `pins_eight`'s `k = 8`. -/
private theorem pins_eight_from_start {t : Slice Std.U8} {i j k : Std.Usize}
    {tb : pins_decode.Tables} {out es : alloc.vec.Vec expr.Expr}
    (hk : ¬ (k = 0#usize))
    (h : pins_decode.pins_eight_from t i tb k out = ok (.Ok (es, j))) :
    i.val ≤ t.length := by
  rw [pins_decode.pins_eight_from.eq_def, ite_eq_right hk] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok j1 => obtain ⟨_, h1, h2⟩ := after_space_refines hr; omega

theorem pins_eight_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (alloc.vec.Vec expr.Expr × Std.Usize) core_types.CheckError}
    (h : pins_decode.pins_eight t i tb = ok o) :
    match o with
    | .Ok (es, j) =>
        PinsDec.pinsEight (bytesFrom t i) (absTables tb)
            = some (absExprs es, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.pins_eight] at h
  cases o with
  | Err ce => exact pins_eight_from_aux 8 8#usize i _ _ (by scalar_tac) h
  | Ok pr =>
  obtain ⟨es, j⟩ := pr
  have hi := pins_eight_from_start (by decide) h
  obtain ⟨heq, h1, h2⟩ := (pins_eight_from_aux 8 8#usize i _ _ (by scalar_tac) h) hi
  refine ⟨?_, h1, h2⟩
  rw [PinsDec.pinsEight]
  rw [show (8#usize : Std.Usize).val = 8 from rfl] at heq
  rw [show absExprs (alloc.vec.Vec.new expr.Expr) = [] by
    simp [absExprs, alloc.vec.Vec.new]] at heq
  exact heq

/-- `proofs_eight_from`'s counter recursion; `pins_eight_from_aux` with
`expr_list` for `expr_ref`. -/
private theorem proofs_eight_from_aux {t : Slice Std.U8} {tb : pins_decode.Tables} :
    ∀ (n : Nat) (k i : Std.Usize) (out : alloc.vec.Vec (alloc.vec.Vec expr.Expr))
      (o : core.result.Result (alloc.vec.Vec (alloc.vec.Vec expr.Expr) × Std.Usize) core_types.CheckError),
      k.val ≤ n →
      pins_decode.proofs_eight_from t i tb k out = ok o →
      match o with
      | .Ok (es, j) =>
        i.val ≤ t.length →
      PinsDec.proofsEightFrom (bytesFrom t i) (absTables tb) k.val
            (out.val.map absExprs)
          = some (es.val.map absExprs, bytesFrom t j)
            ∧ i.val ≤ j.val ∧ j.val ≤ t.length
      | .Err ce => absErrKind ce = none := by
  intro n
  induction n with
  | zero =>
    intro k i out o hk h
    have hk0 : k.val = 0 := by omega
    rw [pins_decode.proofs_eight_from.eq_def] at h
    rw [ite_eq_left (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    intro hi
    exact ⟨by rw [hk0]; rfl, le_refl _, hi⟩
  | succ n ih =>
    intro k i out o hk h
    rw [pins_decode.proofs_eight_from.eq_def] at h
    split at h
    · rename_i hk0
      have hk0' : k.val = 0 := by rw [hk0]; rfl
      simp only [Result.ok.injEq] at h
      subst h
      intro hi
      exact ⟨by rw [hk0']; rfl, le_refl _, hi⟩
    · rename_i hk0
      have hkpos : 0 < k.val := by
        rcases Nat.eq_zero_or_pos k.val with _ | hp
        · exact absurd (by scalar_tac : k = 0#usize) hk0
        · exact hp
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h
        subst h
        exact after_space_refines hr
      | Ok j1 =>
        obtain ⟨hsp, hij1, hj1t⟩ := after_space_refines hr
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e =>
          simp only [Result.ok.injEq] at h
          subst h
          exact expr_list_refines hr1
        | Ok p =>
          obtain ⟨el, m⟩ := p
          obtain ⟨href, hj1m, hmt⟩ := expr_list_refines hr1
          obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
          have hk1v : k1.val = k.val - 1 := usub_eq hk1
          cases o with
          | Err ce => exact ih k1 m out1 _ (by omega) h
          | Ok pr =>
          obtain ⟨es, j⟩ := pr
          intro hi
          obtain ⟨hrec, hmj, hjt⟩ := (ih k1 m out1 _ (by omega) h) hmt
          refine ⟨?_, by omega, hjt⟩
          rw [show k.val = k1.val + 1 by omega]
          rw [show out1.val.map absExprs = out.val.map absExprs ++ [absExprs el] by
            rw [vec_push_val hout1]; simp] at hrec
          simp only [PinsDec.proofsEightFrom, hsp, href]
          exact hrec

private theorem proofs_eight_from_start {t : Slice Std.U8} {i j k : Std.Usize}
    {tb : pins_decode.Tables} {out es : alloc.vec.Vec (alloc.vec.Vec expr.Expr)}
    (hk : ¬ (k = 0#usize))
    (h : pins_decode.proofs_eight_from t i tb k out = ok (.Ok (es, j))) :
    i.val ≤ t.length := by
  rw [pins_decode.proofs_eight_from.eq_def, ite_eq_right hk] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok j1 => obtain ⟨_, h1, h2⟩ := after_space_refines hr; omega

theorem proofs_eight_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (alloc.vec.Vec (alloc.vec.Vec expr.Expr) × Std.Usize)
        core_types.CheckError}
    (h : pins_decode.proofs_eight t i tb = ok o) :
    match o with
    | .Ok (es, j) =>
        PinsDec.proofsEight (bytesFrom t i) (absTables tb)
            = some (es.val.map absExprs, bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.proofs_eight] at h
  cases o with
  | Err ce => exact proofs_eight_from_aux 8 8#usize i _ _ (by scalar_tac) h
  | Ok pr =>
  obtain ⟨es, j⟩ := pr
  have hi := proofs_eight_from_start (by decide) h
  obtain ⟨heq, h1, h2⟩ := (proofs_eight_from_aux 8 8#usize i _ _ (by scalar_tac) h) hi
  refine ⟨?_, h1, h2⟩
  rw [PinsDec.proofsEight]
  rw [show (8#usize : Std.Usize).val = 8 from rfl] at heq
  rw [show (alloc.vec.Vec.new (alloc.vec.Vec expr.Expr)).val.map absExprs = [] by
    simp [alloc.vec.Vec.new]] at heq
  exact heq

/-- The full outcome (task #67).  The `.Err` branch is the module's one
`Native` error, about which nothing is claimed — see the module note. -/
theorem record_pin_set_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables}
    {o : core.result.Result (pins_decode.Tables × Std.Usize) core_types.CheckError}
    (h : pins_decode.record_pin_set t i tb = ok o) :
    match o with
    | .Ok (tb', j) =>
        PinsDec.recordPinSet (bytesFrom t i) (absTables tb)
            = some (absTables tb', bytesFrom t j)
          ∧ i.val ≤ j.val ∧ j.val ≤ t.length
    | .Err ce => absErrKind ce = none := by
  rw [pins_decode.record_pin_set] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    subst h
    exact read_string_refines hr
  | Ok p =>
    obtain ⟨toolchain, i1⟩ := p
    obtain ⟨hstr, hs1, hs2⟩ := read_string_refines hr
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e =>
      simp only [Result.ok.injEq] at h
      subst h
      exact pins_eight_refines hr1
    | Ok p1 =>
      obtain ⟨pins, i2⟩ := p1
      obtain ⟨hpins, hp1, hp2⟩ := pins_eight_refines hr1
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e =>
        simp only [Result.ok.injEq] at h
        subst h
        exact proofs_eight_refines hr2
      | Ok p2 =>
        obtain ⟨proofs, i3⟩ := p2
        obtain ⟨hproofs, hq1, hq2⟩ := proofs_eight_refines hr2
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e =>
          simp only [Result.ok.injEq] at h
          subst h
          exact after_newline_refines hr3
        | Ok i4 =>
          obtain ⟨hnl, hn1, hn2⟩ := after_newline_refines hr3
          simp only [] at h
          split at h
          · obtain ⟨ce, rfl, hce⟩ := err_native h
            exact hce
          · rename_i hp8
            split at h
            · obtain ⟨ce, rfl, hce⟩ := err_native h
              exact hce
            · rename_i hq8
              have hplen : pins.val.length = 8 := by scalar_tac
              have hqlen : proofs.val.length = 8 := by scalar_tac
              obtain ⟨p0, p1', p2', p3', p4', p5', p6', p7', hpv⟩ := eight_cases hplen
              obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, hqv⟩ := eight_cases hqlen
              simp only [
                vec_index_eq (v := pins) (i := 0#usize) (x := p0) (by simp [hpv]),
                vec_index_eq (v := pins) (i := 1#usize) (x := p1') (by simp [hpv]),
                vec_index_eq (v := pins) (i := 2#usize) (x := p2') (by simp [hpv]),
                vec_index_eq (v := pins) (i := 3#usize) (x := p3') (by simp [hpv]),
                vec_index_eq (v := pins) (i := 4#usize) (x := p4') (by simp [hpv]),
                vec_index_eq (v := pins) (i := 5#usize) (x := p5') (by simp [hpv]),
                vec_index_eq (v := pins) (i := 6#usize) (x := p6') (by simp [hpv]),
                vec_index_eq (v := pins) (i := 7#usize) (x := p7') (by simp [hpv]),
                vec_index_eq (v := proofs) (i := 0#usize) (x := q0) (by simp [hqv]),
                vec_index_eq (v := proofs) (i := 1#usize) (x := q1) (by simp [hqv]),
                vec_index_eq (v := proofs) (i := 2#usize) (x := q2) (by simp [hqv]),
                vec_index_eq (v := proofs) (i := 3#usize) (x := q3) (by simp [hqv]),
                vec_index_eq (v := proofs) (i := 4#usize) (x := q4) (by simp [hqv]),
                vec_index_eq (v := proofs) (i := 5#usize) (x := q5) (by simp [hqv]),
                vec_index_eq (v := proofs) (i := 6#usize) (x := q6) (by simp [hqv]),
                vec_index_eq (v := proofs) (i := 7#usize) (x := q7) (by simp [hqv]),
                expr_dup_ok, bind_tc_ok] at h
              obtain ⟨w0, hw0, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨w1, hw1, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨w2, hw2, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨w3, hw3, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨w4, hw4, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨w5, hw5, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨w6, hw6, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨w7, hw7, h⟩ := bind_eq_ok_iff.mp h
              rw [ConRon.Refine.Env.exprs_copy_refines hw0] at h
              rw [ConRon.Refine.Env.exprs_copy_refines hw1] at h
              rw [ConRon.Refine.Env.exprs_copy_refines hw2] at h
              rw [ConRon.Refine.Env.exprs_copy_refines hw3] at h
              rw [ConRon.Refine.Env.exprs_copy_refines hw4] at h
              rw [ConRon.Refine.Env.exprs_copy_refines hw5] at h
              rw [ConRon.Refine.Env.exprs_copy_refines hw6] at h
              rw [ConRon.Refine.Env.exprs_copy_refines hw7] at h
              obtain ⟨v16, hv16, h⟩ := bind_eq_ok_iff.mp h
              simp only [Result.ok.injEq] at h
              subst h
              refine ⟨?_, by omega, hn2⟩
              rw [show absExprs pins = [absExpr p0, absExpr p1', absExpr p2',
                  absExpr p3', absExpr p4', absExpr p5', absExpr p6', absExpr p7'] by
                simp [absExprs, hpv]] at hpins
              rw [show proofs.val.map absExprs = [absExprs q0, absExprs q1,
                  absExprs q2, absExprs q3, absExprs q4, absExprs q5, absExprs q6,
                  absExprs q7] by simp [hqv]] at hproofs
              simp only [PinsDec.recordPinSet, hstr, hpins, hproofs, hnl,
                decString_absString]
              simp [absTables, absNatOpPinSet, vec_push_val hv16]

end ConRon.Refine.PinsRun
