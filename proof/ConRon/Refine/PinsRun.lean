/-
`kernel::pins_decode`'s payload record and pass against
`ConRon.Refine.PinsDec` — half (A) of task #64's decoder refinement, the top.

`record_pin_set` is the one record that builds a `NatOpPinSet`; the pass
(`run_records`, `run_footer`) is the one recursion whose step is a record of
unknown length, so it is where `PinsDec.runRecords`' fuel is discharged: the
model's index `i` moves forward by at least one byte per record, so
`t.length - i.val` is a budget and `decode` passes `t.length`, which is at
least that.

`decode_refines` is this file's product and the whole of (A):

    decode t = ok (.Ok v) → PinsDec.decode (bytesOf t) = some (absPins v)

`Refine/PinsRead.lean` is (B), and `Refine/Pins.lean` composes the two.
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

private theorem uadd_eq {ty : Std.UScalarTy} {x y z : Std.UScalar ty}
    (h : x + y = ok z) : z.val = x.val + y.val := by
  have := Std.UScalar.add_equiv x y
  rw [h] at this; simpa using this.2.1

private theorem usub_eq {ty : Std.UScalarTy} {x y z : Std.UScalar ty}
    (h : x - y = ok z) : z.val = x.val - y.val := by
  have := Std.UScalar.sub_equiv x y
  rw [h] at this; simp at this; omega

/-- The suffix at an in-range index is its first byte, then the suffix at the
next one. -/
private theorem bytesFrom_cons {t : Slice Std.U8} {i j : Std.Usize}
    (hi : i.val < t.length) (hj : j.val = i.val + 1) :
    bytesFrom t i = PinsDec.byteAt (bytesFrom t i) :: bytesFrom t j := by
  have hlen : i.val < (bytesOf t).length := by rw [bytesOf_length]; exact hi
  have h1 : bytesFrom t i = (bytesOf t)[i.val] :: bytesFrom t j := by
    simp only [bytesFrom, hj]
    exact List.drop_eq_getElem_cons hlen
  rw [h1]; rfl

/-- A byte that is not the past-the-end sentinel splits the suffix: only an
in-range index can produce one, and there the split is `bytesFrom_cons`. -/
private theorem bytesFrom_cons_byte {t : Slice Std.U8} {i j : Std.Usize} {k : Nat}
    (hk : PinsDec.byteAt (bytesFrom t i) = k) (hne : k ≠ 256)
    (hj : j.val = i.val + 1) : bytesFrom t i = k :: bytesFrom t j := by
  have hi : i.val < t.length := by
    by_contra hc
    rw [bytesFrom_eq_nil (by omega)] at hk
    exact hne (by simpa [PinsDec.byteAt] using hk)
  rw [← hk]; exact bytesFrom_cons hi hj

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
    ∀ (n : Nat) (k i j : Std.Usize) (out es : alloc.vec.Vec expr.Expr),
      k.val ≤ n → i.val ≤ t.length →
      pins_decode.pins_eight_from t i tb k out = ok (.Ok (es, j)) →
      PinsDec.pinsEightFrom (bytesFrom t i) (absTables tb) k.val (absExprs out)
          = some (absExprs es, bytesFrom t j)
        ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  intro n
  induction n with
  | zero =>
    intro k i j out es hk hi h
    have hk0 : k.val = 0 := by omega
    rw [pins_decode.pins_eight_from.eq_def] at h
    rw [if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hk0]
    exact ⟨rfl, le_refl _, hi⟩
  | succ n ih =>
    intro k i j out es hk hi h
    rw [pins_decode.pins_eight_from.eq_def] at h
    split at h
    · rename_i hk0
      have hk0' : k.val = 0 := by rw [hk0]; rfl
      simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hk0']
      exact ⟨rfl, le_refl _, hi⟩
    · rename_i hk0
      have hkpos : 0 < k.val := by
        rcases Nat.eq_zero_or_pos k.val with _ | hp
        · exact absurd (by scalar_tac : k = 0#usize) hk0
        · exact hp
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok j1 =>
        obtain ⟨hsp, hij1, hj1t⟩ := after_space_refines hr
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e => simp at h
        | Ok p =>
          obtain ⟨e, m⟩ := p
          obtain ⟨href, hj1m, hmt⟩ := expr_ref_refines hr1
          obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
          have hk1v : k1.val = k.val - 1 := usub_eq hk1
          obtain ⟨hrec, hmj, hjt⟩ := ih k1 m j out1 es (by omega) hmt h
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
  rw [pins_decode.pins_eight_from.eq_def, if_neg hk] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok j1 => obtain ⟨_, h1, h2⟩ := after_space_refines hr; omega

/-- **The `i` bound is a hypothesis here, and has to be** (task #64, a
statement corrected during the proof).  At `k = 0` the reader is the identity:
`pins_eight_from t i tb 0 out` is `ok (.Ok (out, i))` for *every* `i`,
including one past the end of `t`, so without `hi` the `j.val ≤ t.length`
conjunct is false — take `t = []`, `i = j = 1`, `k = 0`.  Every caller has the
bound: `k ≠ 0` forces an `after_space`, which supplies it (`pins_eight_from_
start`), and `pins_eight` enters at `k = 8`.  The same correction is on
`proofs_eight_from_refines` below and on `Refine/PinsBytes.lean`'s three
`*_list_from_refines`; nothing above the `*_from` layer changed. -/
theorem pins_eight_from_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb : pins_decode.Tables} {k : Std.Usize}
    {out es : alloc.vec.Vec expr.Expr} (hi : i.val ≤ t.length)
    (h : pins_decode.pins_eight_from t i tb k out = ok (.Ok (es, j))) :
    PinsDec.pinsEightFrom (bytesFrom t i) (absTables tb) k.val (absExprs out)
        = some (absExprs es, bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length :=
  pins_eight_from_aux k.val k i j out es (le_refl _) hi h

theorem pins_eight_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb : pins_decode.Tables} {es : alloc.vec.Vec expr.Expr}
    (h : pins_decode.pins_eight t i tb = ok (.Ok (es, j))) :
    PinsDec.pinsEight (bytesFrom t i) (absTables tb)
        = some (absExprs es, bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.pins_eight] at h
  have hi := pins_eight_from_start (by decide) h
  obtain ⟨heq, h1, h2⟩ := pins_eight_from_aux 8 8#usize i j _ es (by scalar_tac) hi h
  refine ⟨?_, h1, h2⟩
  rw [PinsDec.pinsEight]
  rw [show (8#usize : Std.Usize).val = 8 from rfl] at heq
  rw [show absExprs (alloc.vec.Vec.new expr.Expr) = [] by
    simp [absExprs, alloc.vec.Vec.new]] at heq
  exact heq

/-- `proofs_eight_from`'s counter recursion; `pins_eight_from_aux` with
`expr_list` for `expr_ref`. -/
private theorem proofs_eight_from_aux {t : Slice Std.U8} {tb : pins_decode.Tables} :
    ∀ (n : Nat) (k i j : Std.Usize)
      (out es : alloc.vec.Vec (alloc.vec.Vec expr.Expr)),
      k.val ≤ n → i.val ≤ t.length →
      pins_decode.proofs_eight_from t i tb k out = ok (.Ok (es, j)) →
      PinsDec.proofsEightFrom (bytesFrom t i) (absTables tb) k.val
            (out.val.map absExprs)
          = some (es.val.map absExprs, bytesFrom t j)
        ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  intro n
  induction n with
  | zero =>
    intro k i j out es hk hi h
    have hk0 : k.val = 0 := by omega
    rw [pins_decode.proofs_eight_from.eq_def] at h
    rw [if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hk0]
    exact ⟨rfl, le_refl _, hi⟩
  | succ n ih =>
    intro k i j out es hk hi h
    rw [pins_decode.proofs_eight_from.eq_def] at h
    split at h
    · rename_i hk0
      have hk0' : k.val = 0 := by rw [hk0]; rfl
      simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hk0']
      exact ⟨rfl, le_refl _, hi⟩
    · rename_i hk0
      have hkpos : 0 < k.val := by
        rcases Nat.eq_zero_or_pos k.val with _ | hp
        · exact absurd (by scalar_tac : k = 0#usize) hk0
        · exact hp
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok j1 =>
        obtain ⟨hsp, hij1, hj1t⟩ := after_space_refines hr
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e => simp at h
        | Ok p =>
          obtain ⟨el, m⟩ := p
          obtain ⟨href, hj1m, hmt⟩ := expr_list_refines hr1
          obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
          have hk1v : k1.val = k.val - 1 := usub_eq hk1
          obtain ⟨hrec, hmj, hjt⟩ := ih k1 m j out1 es (by omega) hmt h
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
  rw [pins_decode.proofs_eight_from.eq_def, if_neg hk] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok j1 => obtain ⟨_, h1, h2⟩ := after_space_refines hr; omega

/-- The same correction as `pins_eight_from_refines`, and for the same `k = 0`
reason: without `hi` the `j.val ≤ t.length` conjunct is false. -/
theorem proofs_eight_from_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb : pins_decode.Tables} {k : Std.Usize}
    {out es : alloc.vec.Vec (alloc.vec.Vec expr.Expr)} (hi : i.val ≤ t.length)
    (h : pins_decode.proofs_eight_from t i tb k out = ok (.Ok (es, j))) :
    PinsDec.proofsEightFrom (bytesFrom t i) (absTables tb) k.val
          (out.val.map absExprs)
        = some (es.val.map absExprs, bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length :=
  proofs_eight_from_aux k.val k i j out es (le_refl _) hi h

theorem proofs_eight_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb : pins_decode.Tables} {es : alloc.vec.Vec (alloc.vec.Vec expr.Expr)}
    (h : pins_decode.proofs_eight t i tb = ok (.Ok (es, j))) :
    PinsDec.proofsEight (bytesFrom t i) (absTables tb)
        = some (es.val.map absExprs, bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.proofs_eight] at h
  have hi := proofs_eight_from_start (by decide) h
  obtain ⟨heq, h1, h2⟩ := proofs_eight_from_aux 8 8#usize i j _ es (by scalar_tac) hi h
  refine ⟨?_, h1, h2⟩
  rw [PinsDec.proofsEight]
  rw [show (8#usize : Std.Usize).val = 8 from rfl] at heq
  rw [show (alloc.vec.Vec.new (alloc.vec.Vec expr.Expr)).val.map absExprs = [] by
    simp [alloc.vec.Vec.new]] at heq
  exact heq

theorem record_pin_set_refines {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables}
    (h : pins_decode.record_pin_set t i tb = ok (.Ok (tb', j))) :
    PinsDec.recordPinSet (bytesFrom t i) (absTables tb)
        = some (absTables tb', bytesFrom t j)
      ∧ i.val ≤ j.val ∧ j.val ≤ t.length := by
  rw [pins_decode.record_pin_set] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok p =>
    obtain ⟨toolchain, i1⟩ := p
    obtain ⟨hstr, hs1, hs2⟩ := read_string_refines hr
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p1 =>
      obtain ⟨pins, i2⟩ := p1
      obtain ⟨hpins, hp1, hp2⟩ := pins_eight_refines hr1
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok p2 =>
        obtain ⟨proofs, i3⟩ := p2
        obtain ⟨hproofs, hq1, hq2⟩ := proofs_eight_refines hr2
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok i4 =>
          obtain ⟨hnl, hn1, hn2⟩ := after_newline_refines hr3
          simp only [] at h
          split at h
          · obtain ⟨ce, _, h⟩ := bind_eq_ok_iff.mp h; simp at h
          · rename_i hp8
            split at h
            · obtain ⟨ce, _, h⟩ := bind_eq_ok_iff.mp h; simp at h
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
              simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
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

/-! ## The pass -/

theorem run_footer_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables} {v : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (h : pins_decode.run_footer t i tb = ok (.Ok v)) :
    PinsDec.runFooter (bytesFrom t i) (absTables tb) = some (absPins v) := by
  rw [pins_decode.run_footer] at h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨ce, _, h⟩ := bind_eq_ok_iff.mp h; simp at h
  · rename_i hne1
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = i.val + 1 := uadd_eq hi2
    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · obtain ⟨ce, _, h⟩ := bind_eq_ok_iff.mp h; simp at h
    · rename_i hne2
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
      have hi4v : i4.val = i.val + 2 := uadd_eq hi4
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok i5 =>
        obtain ⟨hsp, ha1, ha2⟩ := after_space_refines hr
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e => simp at h
        | Ok p =>
          obtain ⟨n, i6⟩ := p
          obtain ⟨hix, hb3, hb4⟩ := read_index_refines hr1
          obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
          cases r2 with
          | Err e => simp at h
          | Ok i7 =>
            obtain ⟨hnl, hc1, hc2⟩ := after_newline_refines hr2
            simp only [] at h
            split at h
            · obtain ⟨ce, _, h⟩ := bind_eq_ok_iff.mp h; simp at h
            · rename_i hend
              split at h
              · obtain ⟨ce, _, h⟩ := bind_eq_ok_iff.mp h; simp at h
              · rename_i hcount
                simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
                subst h
                have h1 : bytesFrom t i = 110 :: bytesFrom t i2 :=
                  bytesFrom_cons_byte (by rw [← byte_at_refines hb1]; scalar_tac)
                    (by omega) hi2v
                have h2 : bytesFrom t i2 = 100 :: bytesFrom t i4 :=
                  bytesFrom_cons_byte (by rw [← byte_at_refines hb2]; scalar_tac)
                    (by omega) (by omega)
                have h7 : bytesFrom t i7 = [] :=
                  bytesFrom_eq_nil (by scalar_tac)
                have hcnt : n.val = (absTables tb).sets.length := by
                  simp only [absTables, List.length_map]; scalar_tac
                rw [h1, h2]
                simp only [PinsDec.runFooter, hsp, hix, hnl, h7, hcnt]
                simp [absPins, absTables]

/-- The pass, with the byte budget the record step spends: each step reads at
least the record's own kind byte and the space after it, so the index has
advanced by at least two when the recursion is entered again. -/
private theorem run_records_aux {t : Slice Std.U8} :
    ∀ (f : Nat) (i : Std.Usize) (tb : pins_decode.Tables)
      (v : alloc.vec.Vec nat_op_pins.NatOpPinSet),
      pins_decode.run_records t i tb = ok (.Ok v) →
      t.length - i.val ≤ f →
      PinsDec.runRecords f (bytesFrom t i) (absTables tb) = some (absPins v) := by
  intro f
  induction f with
  | zero =>
    intro i tb v h hf
    exfalso
    have hnil : bytesFrom t i = [] := bytesFrom_eq_nil (by omega)
    rw [pins_decode.run_records.eq_def] at h
    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
    have hkv : k.val = 256 := by rw [byte_at_refines hk, hnil]; rfl
    split at h
    · rename_i hk101; rw [hk101] at hkv; simp at hkv
    · obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := uadd_eq hi1
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok j => obtain ⟨_, h1, h2⟩ := after_space_refines hr; omega
  | succ f ih =>
    intro i tb v h hf
    rw [pins_decode.run_records.eq_def] at h
    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
    have hkv := byte_at_refines hk
    split at h
    · rename_i hk101
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := uadd_eq hi1
      have hcons : bytesFrom t i = 101 :: bytesFrom t i1 :=
        bytesFrom_cons_byte (by rw [← hkv, hk101]; rfl) (by omega) hi1v
      rw [hcons]
      simp only [PinsDec.runRecords, reduceIte]
      exact run_footer_refines h
    · rename_i hk101
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := uadd_eq hi1
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok jj =>
        obtain ⟨hsp, hb1, hb2⟩ := after_space_refines hr
        have hne : k.val ≠ 101 := by
          intro hc
          exact hk101 (by scalar_tac)
        have hilt : i.val < t.length := by omega
        have hcons : bytesFrom t i = k.val :: bytesFrom t i1 := by
          rw [hkv]; exact bytesFrom_cons hilt hi1v
        obtain ⟨step, hstep, h⟩ := bind_eq_ok_iff.mp h
        cases step with
        | Err e => simp at h
        | Ok sp =>
          obtain ⟨tb1, m⟩ := sp
          have hrec : PinsDec.recordStep k.val (bytesFrom t jj) (absTables tb)
              = some (absTables tb1, bytesFrom t m)
              ∧ jj.val ≤ m.val ∧ m.val ≤ t.length := by
            split at hstep
            · rename_i h78
              obtain ⟨hs, h1, h2⟩ := record_name_refines hstep
              refine ⟨?_, h1, h2⟩
              rw [show k.val = 78 by rw [h78]; rfl]
              simpa [PinsDec.recordStep] using hs
            · split at hstep
              · rename_i h76
                obtain ⟨hs, h1, h2⟩ := record_level_refines hstep
                refine ⟨?_, h1, h2⟩
                rw [show k.val = 76 by rw [h76]; rfl]
                simpa [PinsDec.recordStep] using hs
              · split at hstep
                · rename_i h87
                  obtain ⟨hs, h1, h2⟩ := record_pw_refines hstep
                  refine ⟨?_, h1, h2⟩
                  rw [show k.val = 87 by rw [h87]; rfl]
                  simpa [PinsDec.recordStep] using hs
                · split at hstep
                  · rename_i h69
                    obtain ⟨hs, h1, h2⟩ := record_expr_refines hstep
                    refine ⟨?_, h1, h2⟩
                    rw [show k.val = 69 by rw [h69]; rfl]
                    simpa [PinsDec.recordStep] using hs
                  · split at hstep
                    · rename_i h83
                      obtain ⟨hs, h1, h2⟩ := record_pin_set_refines hstep
                      refine ⟨?_, h1, h2⟩
                      rw [show k.val = 83 by rw [h83]; rfl]
                      simpa [PinsDec.recordStep] using hs
                    · exfalso
                      obtain ⟨ce, _, hstep⟩ := bind_eq_ok_iff.mp hstep
                      simp at hstep
          obtain ⟨hstepd, hm1, hm2⟩ := hrec
          have hfuel : t.length - m.val ≤ f := by omega
          rw [hcons]
          simp only [PinsDec.runRecords, if_neg hne, hsp, hstepd]
          exact ih m tb1 v h hfuel

/-- The pass, with the byte budget the record step spends.  `fuel` is anything
at least the number of bytes left, which is what `decode` hands it. -/
theorem run_records_refines {t : Slice Std.U8} {i : Std.Usize}
    {tb : pins_decode.Tables} {v : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (h : pins_decode.run_records t i tb = ok (.Ok v)) :
    ∀ f : Nat, t.length - i.val ≤ f →
      PinsDec.runRecords f (bytesFrom t i) (absTables tb) = some (absPins v) := by
  intro f hf
  exact run_records_aux f i tb v h hf

/-- **(A): the model's decoder refines `PinsDec`.** -/
theorem decode_refines {t : Slice Std.U8}
    {v : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (h : pins_decode.decode t = ok (.Ok v)) :
    PinsDec.decode (bytesOf t) = some (absPins v) := by
  rw [pins_decode.decode] at h
  obtain ⟨hdr, hhdr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · rename_i hbt
    subst hbt
    obtain ⟨tn, htn, h⟩ := bind_eq_ok_iff.mp h
    have hhv : hdr.val.map (fun c => c.val) = PinsDec.headerBytes :=
      pins_header_refines hhdr
    have hlen : hdr.val.length = 15 := by
      have := congrArg List.length hhv
      simpa [PinsDec.headerBytes] using this
    have hsw : PinsDec.startsWith (bytesOf t) PinsDec.headerBytes = true := by
      have := starts_with_from_refines (t := t) (p := alloc.vec.Vec.deref hdr)
        (i := 0#usize) hb (by simp)
      simpa [bytesFrom, bytesOf, alloc.vec.Vec.deref, hhv] using this
    have htn' : absTables tn = PinsDec.tablesNew := by
      rw [pins_decode.tables_new] at htn
      simp only [Result.ok.injEq] at htn
      subst htn
      simp [absTables, PinsDec.tablesNew, alloc.vec.Vec.new]
    have hrun := run_records_aux (t := t) (bytesOf t).length
      (alloc.vec.Vec.len hdr) tn v h (by simp [bytesOf, Slice.length])
    rw [PinsDec.decode, if_pos hsw]
    rw [htn'] at hrun
    rw [show (bytesOf t).drop PinsDec.headerBytes.length
        = bytesFrom t (alloc.vec.Vec.len hdr) by
      simp [bytesFrom, PinsDec.headerBytes, hlen]]
    exact hrun
  · obtain ⟨ce, _, h⟩ := bind_eq_ok_iff.mp h; simp at h

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`decode_refines` is the whole of half (A), so this is the line that says the
Aeneas model of `kernel::pins_decode` refines `Refine/PinsDec.lean` on con-
leche's own three axioms and nothing else. -/

/-- info: 'ConRon.Refine.PinsRun.decode_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decode_refines

/-- info: 'ConRon.Refine.PinsRun.run_records_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_records_refines

end ConRon.Refine.PinsRun
