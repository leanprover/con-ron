/-
The **scanner's one obligation** (task #85, phase 1).

`Refine/Frontend/Base.lean`'s `LineRecWF` is the whole of what the byte scanner
owes the parse: every `Vec<u32>` `frontend::scan_fast` hands over as a *string
payload* holds valid Unicode scalar values (`Refine/Abs.lean`'s `StrWF`),
because `name::mk_str` asks for exactly that and `absString` is not injective
without it.  Nothing else about the scanner is claimed here -- no refinement
against con-leche's `scanLineFwd`, no error agreement, no position facts.  The
file's product is

    scan_line_fwd b i = ok (.Ok (r, j)) → LineRecWF r

for **every** byte slice, so nothing here is evaluated.

## The one leaf, and why it is the only one

The only producer of a string payload is `scan_fast::scan_string`, which
returns either `utf8_decode(b, i+1, e)` or `unescape(body, 0, body.len())`, and
`unescape` is `unescape_bytes` followed by `utf8_decode` again.  **So
`unescape_bytes` needs no lemma at all**: it produces *bytes*, and the port
validates the whole buffer afterwards, exactly as con-leche's
`String.fromUTF8? acc` does -- which is precisely why the port validates there
and not at each escape.  `utf8_decode_wf` is therefore the file's one piece of
real arithmetic.

## Why the rest is not free

`ExprRecWF`/`NameRecWF` are `True` on every constructor but `StrVal` and
`Str`, but "`True` here" is not a *syntactic* fact about a scanner's result:
to know that `scan_line_loop`'s `"app"` member installed an `ExprRec` that is
not a `StrVal`, one has to know which constructor `scan_app_expr` builds.  So
every record scanner the line dispatcher can reach gets its own lemma, and
each is the same shallow induction -- `Close` builds one fixed constructor,
every `Key` arm either errors or recurses.

## The measure

`partial_fixpoint` gives these loops no induction principle, so every one of
them is a strong induction on a `Nat` measure.  For `utf8_decode` it is `n - k`.
For the member loops it is `b.len() - i`, and it drops because of two facts
proved once here: `next_member_ge` (the key it reports sits at or after the
cursor it was given) and the module's own `prog` guard, which every slot closes
with -- directly, or inside `slot_nat`.  `next_member_lt` supplies the `i <
b.len()` that makes the drop strict.

## `sorry` count in this file: 0
-/
import ConRon.RefineOld.Frontend.Base

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

open ConRon.Refine

/-! ## Plumbing -/

/-- A push extends a `StrWF` by the pushed word. -/
private theorem push_str {v w : alloc.vec.Vec Std.U32} {x : Std.U32}
    (hv : StrWF v) (hx : Nat.isValidChar x.val)
    (h : alloc.vec.Vec.push v x = ok w) : StrWF w := by
  rw [StrWF, vec_push_val h]
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hv y hy
  · rw [List.mem_singleton.mp hy]; exact hx

/-- The empty vector is trivially well formed. -/
private theorem str_new : StrWF (alloc.vec.Vec.new Std.U32) := by
  simp [StrWF, alloc.vec.Vec.new]

/-- A machine-word increment really moves the cursor forward: the one fact the
decoder's measure needs. -/
private theorem uadd_gt {x c z : Std.Usize} (h : x + c = ok z) (hc : 0 < c.val) :
    x.val < z.val := by
  have := ConRon.Refine.Nat.uadd_val h; omega

/-- `lift` is `ok`, so a `lift`ed pure step is an equation on its value. -/
private theorem lift_val {α : Type} {x y : α} (h : lift x = ok y) : x = y := by
  simpa only [lift, Result.ok.injEq] using h

/-- A mask keeps only the low bits: the bound every continuation byte gets. -/
private theorem and_le {x m z : Std.U32} (h : lift (x &&& m) = ok z) : z.val ≤ m.val := by
  rw [← lift_val h, Std.UScalar.val_and]; exact Nat.and_le_right

/-- An `or` of two values below `2 ^ p` stays below `2 ^ p`: how the assembled
code point inherits the bound of its widest piece. -/
private theorem or_lt {x y z : Std.U32} {p : Nat} (h : lift (x ||| y) = ok z)
    (hx : x.val < 2 ^ p) (hy : y.val < 2 ^ p) : z.val < 2 ^ p := by
  rw [← lift_val h, Std.UScalar.val_or]; exact Nat.or_lt_two_pow hx hy

/-! ## The leaf: `utf8_decode`

`crates/con-ron-core/src/frontend/scan_fast.rs`'s `utf8_decode` (con-leche:
none -- it stands for Lean's `String.fromUTF8?`, which `scanString` and
`unescape` call on the bytes they have collected).  Every byte sequence the
decoder accepts pushes a word it has just range-checked, so the invariant is
that the accumulator stays a sequence of scalar values.  The four widths close
differently:

* ASCII is below `0x80`;
* a two-byte form is a five-bit lead and a six-bit tail, so below `0x800`;
* a three-byte form is explicitly refused below `0x800` and inside the
  surrogate block `[0xD800, 0xE000)`, and its four-bit lead bounds it below
  `0x10000`;
* a four-byte form is refused below `0x10000` and above `0x10FFFF`, which *is*
  the upper half of `Nat.isValidChar` -- that arm needs no bit arithmetic at
  all.
-/

/-- The loop of `scan_fast::utf8_decode`, as the invariant "the accumulator is
a sequence of scalar values".  `partial_fixpoint` gives no induction principle,
so the induction is on the `while k < n` measure `n - k`. -/
private theorem utf8_decode_loop_wf {b : Slice Std.U8} (f : Nat) :
    ∀ (n k : Std.Usize) (out res : alloc.vec.Vec Std.U32),
      n.val - k.val ≤ f → StrWF out →
      frontend.scan_fast.utf8_decode_loop b n out k = ok (some res) → StrWF res := by
  induction f with
  | zero =>
    intro n k out res hf hout h
    rw [frontend.scan_fast.utf8_decode_loop.eq_def] at h
    rw [if_neg (show ¬ (k < n) by scalar_tac)] at h
    simp only [Result.ok.injEq, Option.some.injEq] at h
    rw [← h]; exact hout
  | succ f ih =>
    intro n k out res hf hout h
    rw [frontend.scan_fast.utf8_decode_loop.eq_def] at h
    by_cases hlt : k < n
    · rw [if_pos hlt] at h
      have hkn : k.val < n.val := by scalar_tac
      -- the one recursive step: a validated word is pushed and the cursor has
      -- moved forward, so the measure has dropped.
      have hstep : ∀ (v : Std.U32) (out1 : alloc.vec.Vec Std.U32) (k1 : Std.Usize),
          Nat.isValidChar v.val → alloc.vec.Vec.push out v = ok out1 → k.val < k1.val →
          frontend.scan_fast.utf8_decode_loop b n out1 k1 = ok (some res) → StrWF res :=
        fun v out1 k1 hv hpush hk1 hrec =>
          ih n k1 out1 res (by omega) (push_str hout hv hpush) hrec
      obtain ⟨c0, -, h⟩ := bind_eq_ok_iff.mp h
      by_cases h1 : c0 < 128#u8
      · -- ASCII
        rw [if_pos h1] at h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
        have hvv : v.val = c0.val := by
          rw [← lift_val hv]; exact Std.U8.cast_U32_val_eq c0
        have hc0 : c0.val < 128 := by scalar_tac
        exact hstep v out1 k1 (by unfold Nat.isValidChar; omega) hout1
          (uadd_gt hk1 (by scalar_tac)) h
      · rw [if_neg h1] at h
        by_cases h2 : c0 < 194#u8
        · rw [if_pos h2] at h; simp at h
        · rw [if_neg h2] at h
          by_cases h3 : c0 < 224#u8
          · -- two bytes: below `0x800`
            rw [if_pos h3] at h
            obtain ⟨i, -, h⟩ := bind_eq_ok_iff.mp h
            by_cases hn1 : n ≤ i
            · rw [if_pos hn1] at h; simp at h
            · rw [if_neg hn1] at h
              obtain ⟨c1, -, h⟩ := bind_eq_ok_iff.mp h
              by_cases hg1 : c1 < 128#u8
              · rw [if_pos hg1] at h; simp at h
              · rw [if_neg hg1] at h
                by_cases hg2 : 192#u8 ≤ c1
                · rw [if_pos hg2] at h; simp at h
                · rw [if_neg hg2] at h
                  obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨i4, -, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨i6, hi6, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
                  have e2 : i2.val ≤ 31 := by
                    have := and_le hi2; scalar_tac
                  have e3 : i3.val < 2 ^ 11 :=
                    have hv : i3.val = i2.val * 64 % 4294967296 :=
                      (ConRon.Refine.Nat.ushiftLeftI_val hi3).2
                    by omega
                  have e5 : i5.val < 2 ^ 11 := by
                    have := and_le hi5; scalar_tac
                  exact hstep i6 out1 k1
                    (by have := or_lt hi6 e3 e5; unfold Nat.isValidChar; omega) hout1
                    (uadd_gt hk1 (by scalar_tac)) h
          · rw [if_neg h3] at h
            by_cases h4 : c0 < 240#u8
            · -- three bytes: below `0x10000`, and not a surrogate
              rw [if_pos h4] at h
              obtain ⟨i, -, h⟩ := bind_eq_ok_iff.mp h
              by_cases hn1 : n ≤ i
              · rw [if_pos hn1] at h; simp at h
              · rw [if_neg hn1] at h
                obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨c1, -, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨c2, -, h⟩ := bind_eq_ok_iff.mp h
                by_cases hg1 : c1 < 128#u8
                · rw [if_pos hg1] at h; simp at h
                · rw [if_neg hg1] at h
                  by_cases hg2 : 192#u8 ≤ c1
                  · rw [if_pos hg2] at h; simp at h
                  · rw [if_neg hg2] at h
                    by_cases hg3 : c2 < 128#u8
                    · rw [if_pos hg3] at h; simp at h
                    · rw [if_neg hg3] at h
                      by_cases hg4 : 192#u8 ≤ c2
                      · rw [if_pos hg4] at h; simp at h
                      · rw [if_neg hg4] at h
                        obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨i5, -, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨i6, hi6, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨i8, hi8, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨i9, -, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨i10, hi10, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨v, hvd, h⟩ := bind_eq_ok_iff.mp h
                        have e3 : i3.val ≤ 15 := by
                          have := and_le hi3; scalar_tac
                        have e4 : i4.val < 2 ^ 16 :=
                          have hv : i4.val = i3.val * 4096 % 4294967296 :=
                            (ConRon.Refine.Nat.ushiftLeftI_val hi4).2
                          by omega
                        have e6 : i6.val ≤ 63 := by
                          have := and_le hi6; scalar_tac
                        have e7 : i7.val < 2 ^ 16 :=
                          have hv : i7.val = i6.val * 64 % 4294967296 :=
                            (ConRon.Refine.Nat.ushiftLeftI_val hi7).2
                          by omega
                        have e10 : i10.val < 2 ^ 16 := by
                          have := and_le hi10; scalar_tac
                        have ev : v.val < 65536 := or_lt hvd (or_lt hi8 e4 e7) e10
                        -- the three-byte guards: overlong forms and the
                        -- surrogate block are refused.
                        by_cases hv1 : v < 2048#u32
                        · rw [if_pos hv1] at h; simp at h
                        · rw [if_neg hv1] at h
                          by_cases hv2 : 55296#u32 ≤ v
                          · rw [if_pos hv2] at h
                            by_cases hv3 : v < 57344#u32
                            · rw [if_pos hv3] at h; simp at h
                            · rw [if_neg hv3] at h
                              have hvge : 57344 ≤ v.val := by scalar_tac
                              obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
                              exact hstep v out1 k1
                                (by unfold Nat.isValidChar; omega) hout1
                                (uadd_gt hk1 (by scalar_tac)) h
                          · rw [if_neg hv2] at h
                            have hvlt : v.val < 55296 := by scalar_tac
                            obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
                            obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
                            exact hstep v out1 k1
                              (by unfold Nat.isValidChar; omega) hout1
                              (uadd_gt hk1 (by scalar_tac)) h
            · rw [if_neg h4] at h
              by_cases h5 : c0 < 245#u8
              · -- four bytes: the two guards *are* `Nat.isValidChar`'s upper
                -- half, so no bit arithmetic is needed here.
                rw [if_pos h5] at h
                obtain ⟨i, -, h⟩ := bind_eq_ok_iff.mp h
                by_cases hn1 : n ≤ i
                · rw [if_pos hn1] at h; simp at h
                · rw [if_neg hn1] at h
                  obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨c1, -, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨c2, -, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨c3, -, h⟩ := bind_eq_ok_iff.mp h
                  by_cases hg1 : c1 < 128#u8
                  · rw [if_pos hg1] at h; simp at h
                  · rw [if_neg hg1] at h
                    by_cases hg2 : 192#u8 ≤ c1
                    · rw [if_pos hg2] at h; simp at h
                    · rw [if_neg hg2] at h
                      by_cases hg3 : c2 < 128#u8
                      · rw [if_pos hg3] at h; simp at h
                      · rw [if_neg hg3] at h
                        by_cases hg4 : 192#u8 ≤ c2
                        · rw [if_pos hg4] at h; simp at h
                        · rw [if_neg hg4] at h
                          by_cases hg5 : c3 < 128#u8
                          · rw [if_pos hg5] at h; simp at h
                          · rw [if_neg hg5] at h
                            by_cases hg6 : 192#u8 ≤ c3
                            · rw [if_pos hg6] at h; simp at h
                            · rw [if_neg hg6] at h
                              obtain ⟨i3, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i4, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i5, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i6, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i7, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i8, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i9, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i10, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i11, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i12, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i13, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i14, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨i15, -, h⟩ := bind_eq_ok_iff.mp h
                              obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
                              by_cases hv1 : v < 65536#u32
                              · rw [if_pos hv1] at h; simp at h
                              · rw [if_neg hv1] at h
                                by_cases hv2 : 1114111#u32 < v
                                · rw [if_pos hv2] at h; simp at h
                                · rw [if_neg hv2] at h
                                  have hlo : 65536 ≤ v.val := by scalar_tac
                                  have hhi : v.val ≤ 1114111 := by scalar_tac
                                  obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
                                  obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
                                  exact hstep v out1 k1
                                    (by unfold Nat.isValidChar; omega) hout1
                                    (uadd_gt hk1 (by scalar_tac)) h
              · rw [if_neg h5] at h; simp at h
    · rw [if_neg hlt] at h
      simp only [Result.ok.injEq, Option.some.injEq] at h
      rw [← h]; exact hout

/-! ## The member loop's cursor

Every `scan_*_loop` of the module is the same `while` over JSON members, and
every one of them needs the same two facts to have a measure: `next_member`
does not move the cursor backwards, and a slot always makes progress.  They are
proved once here and used by each loop below. -/

/-- Every error arm of a scanner is `scan_fast::err`, which never yields an
`Ok`. -/
private theorem err_ne_ok {T : Type} {offset : Std.Usize}
    {what : frontend.scan_types.ErrTag} {x : T × Std.Usize}
    (h : frontend.scan_fast.err T offset what = ok (.Ok x)) : False := by
  simp [frontend.scan_fast.err] at h

/-- `scan_fast::next_member` only ever skips forward: the key it reports sits
at or after the cursor it was given.  (`next_member` returns the key's own
offset as both the `Member::Key` payload and the new cursor.) -/
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
        have h1 := uadd_gt hi2 (by scalar_tac)
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
              have h1 := uadd_gt hi2 (by scalar_tac)
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

/-- **The leaf.**  `scan_fast::utf8_decode`'s output is a sequence of scalar
values -- for *every* byte slice, since the decoder's own guards are what carry
the fact. -/
theorem utf8_decode_wf {b : Slice Std.U8} {j e : Std.Usize} {out : alloc.vec.Vec Std.U32}
    (h : frontend.scan_fast.utf8_decode b j e = ok (some out)) : StrWF out := by
  rw [frontend.scan_fast.utf8_decode] at h
  obtain ⟨n, -, h⟩ := bind_eq_ok_iff.mp h
  exact utf8_decode_loop_wf (n.val - j.val) n j _ out (le_refl _) str_new h

/-! ## `scan_string`: the only producer of a string payload -/

/-- `scan_fast::unescape` (con-leche: `ConLeche/Frontend/Scan/Fast.lean:566-625
unescape`).  It is `unescape_bytes` followed by `utf8_decode`, so the byte half
owes nothing at all -- the validation at the end is what carries `StrWF`, which
is exactly why the port validates there and not at each escape. -/
theorem unescape_wf {b : Slice Std.U8} {j e : Std.Usize} {out : alloc.vec.Vec Std.U32}
    (h : frontend.scan_fast.unescape b j e = ok (some out)) : StrWF out := by
  rw [frontend.scan_fast.unescape] at h
  obtain ⟨o, -, h⟩ := bind_eq_ok_iff.mp h
  cases o with
  | none => simp at h
  | some acc => exact utf8_decode_wf h

/-- `scan_fast::scan_string` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:627-647 scanString`,
`ConLeche/Frontend/Scan/Naive.lean:128-147 naiveStr`).  Both exits decode: the
escape-free body through `utf8_decode` on the chunk, an escaped one through
`unescape` on the sliced-out body. -/
theorem scan_string_wf {b : Slice Std.U8} {i : Std.Usize}
    {s : alloc.vec.Vec Std.U32} {j : Std.Usize}
    (h : frontend.scan_fast.scan_string b i = ok (.Ok (s, j))) : StrWF s := by
  rw [frontend.scan_fast.scan_string] at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
  by_cases h1 : (i1 != 34#u8) = true
  · rw [if_pos h1] at h; exact (err_ne_ok h).elim
  · rw [if_neg h1] at h
    obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e, -, h⟩ := bind_eq_ok_iff.mp h
    by_cases h2 : e = 0#usize
    · rw [if_pos h2] at h; exact (err_ne_ok h).elim
    · rw [if_neg h2] at h
      obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
      by_cases h3 : b1 = true
      · rw [if_pos h3] at h
        obtain ⟨body, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
        cases o with
        | none => exact (err_ne_ok h).elim
        | some s1 =>
          obtain ⟨i4, -, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]; exact unescape_wf ho
      · rw [if_neg h3] at h
        obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
        cases o with
        | none => exact (err_ne_ok h).elim
        | some s1 =>
          obtain ⟨i3, -, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]; exact utf8_decode_wf ho

/-! ## The member loops

Each `scan_*_loop` is the same `while` over the members of one JSON object, so
each proof is the same three steps: peel `next_member`, close the `Close` arm
with the record the loop has accumulated, and send every `Key` arm either to
`err` (which never yields an `Ok`) or to the recursive call, whose measure has
dropped because `next_member_ge` and the slot's own `prog` guard together move
the cursor at least one byte forward. -/

/-- Past the end of the chunk `next_member` reports `ExpectedComma`, so a
member loop that got an `Ok` was still inside the chunk. -/
private theorem next_member_lt {b : Slice Std.U8} {i : Std.Usize} {w : Bool}
    {x : frontend.scan_fast.Member × Std.Usize × Bool}
    (h : frontend.scan_fast.next_member b i w = ok (.Ok x)) : i.val < b.length := by
  by_contra hc
  rw [frontend.scan_fast.next_member, frontend.scan_fast.next_member_loop.eq_def] at h
  rw [if_pos (show i ≥ Slice.len b by scalar_tac)] at h
  simp at h

/-- `scan_fast::prog` is `ks < e`, read forwards. -/
private theorem prog_lt {ks e : Std.Usize} {c : Bool}
    (h : frontend.scan_fast.prog ks e = ok c) (hc : c = true) : ks.val < e.val := by
  rw [frontend.scan_fast.prog, Result.ok.injEq] at h
  rw [← h] at hc
  simp only [decide_eq_true_eq] at hc
  scalar_tac

/-- `scan_fast::scan_str_name_loop` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:795-843 scanStrNameLoop`).  The loop carries
the decoded string as an accumulator, so this is the one member loop with a
real invariant: what `"str"` installs came from `scan_string`. -/
private theorem scan_str_name_loop_wf {b : Slice Std.U8} (f : Nat) :
    ∀ (w : Bool) (i : Std.Usize) (seen : Std.U32) (pre : Std.U64)
      (s : alloc.vec.Vec Std.U32) (r : frontend.scan_types.NameRec) (j : Std.Usize),
      b.length - i.val ≤ f → StrWF s →
      frontend.scan_fast.scan_str_name_loop_loop w b i seen pre s = ok (.Ok (r, j)) →
      NameRecWF r := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen pre s r j hf hs h
    rw [frontend.scan_fast.scan_str_name_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i _ p
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      have hilt := next_member_lt hres
      split at h
      · -- `Close`: the record the loop has accumulated
        by_cases hnw : nw = true
        · rw [if_pos hnw] at h
          by_cases hz : (seen != 0#u32) = true
          · rw [if_pos hz] at h; exact (err_ne_ok h).elim
          · rw [if_neg hz] at h
            obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
            by_cases hm : (i1 != 3#u32) = true
            · rw [if_pos hm] at h; exact (err_ne_ok h).elim
            · rw [if_neg hm] at h
              obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
              simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                Prod.mk.injEq] at h
              rw [← h.1]; exact hs
        · rw [if_neg hnw] at h
          obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
          by_cases hm : (i1 != 3#u32) = true
          · rw [if_pos hm] at h; exact (err_ne_ok h).elim
          · rw [if_neg hm] at h
            obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
              Prod.mk.injEq] at h
            rw [← h.1]; exact hs
      · -- `Key`: `"pre"`, `"str"`, and fifty-odd keys that are not this
        -- record's, every one of them `err`
        rename_i k ks v
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        split at h
        all_goals
          first
            | exact (err_ne_ok h).elim
            | -- `"pre"`: a machine word, the accumulator is untouched
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               by_cases hd : b1 = true
               · rw [if_pos hd] at h; exact (err_ne_ok h).elim
               · rw [if_neg hd] at h
                 obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   have he := slot_nat_prog hr1
                   obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                   exact ih (b.length - e.val) (by omega) false e seen1 x s r j
                     (le_refl _) hs h
                 · simp at h)
            | -- `"str"`: the accumulator is replaced by `scan_string`'s value
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               by_cases hd : b1 = true
               · rw [if_pos hd] at h; exact (err_ne_ok h).elim
               · rw [if_neg hd] at h
                 obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                   by_cases hp : b2 = true
                   · rw [if_pos hp] at h
                     have he := prog_lt hb2 hp
                     obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                     exact ih (b.length - e.val) (by omega) false e seen1 pre x r j
                       (le_refl _) (scan_string_wf hr1) h
                   · rw [if_neg hp] at h; exact (err_ne_ok h).elim
                 · simp at h)
    · simp at h

/-- `scan_fast::scan_str_name` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:845-849 scanStrName`,
`ConLeche/Frontend/Scan/Naive.lean:407-408 naiveStrName`). -/
theorem scan_str_name_wf {b : Slice Std.U8} {i : Std.Usize}
    {r : frontend.scan_types.NameRec} {j : Std.Usize}
    (h : frontend.scan_fast.scan_str_name b i = ok (.Ok (r, j))) : NameRecWF r := by
  rw [frontend.scan_fast.scan_str_name] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
  by_cases hc : c = 123#u8
  · rw [if_pos hc] at h
    obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
    exact scan_str_name_loop_wf (b.length - i2.val) true i2 0#u32 0#u64 _ r j
      (le_refl _) str_new h
  · rw [if_neg hc] at h; exact (err_ne_ok h).elim

/-! ### The records with no string payload

`NameRecWF` and `ExprRecWF` are `True` on every constructor but `Str` and
`StrVal`, so each of these loops owes only *which constructor it built*, and
that is what the induction establishes: every exit of the `Close` arm is one
fixed constructor, and every `Key` arm either errors or recurses.  The three
arm shapes are the module's three slot idioms -- a `slot_nat` machine word, a
sub-scanner closed by the `prog` guard, and `scan_binder_info`'s bare `usize`
-- and `first` picks whichever one the key in hand uses. -/

/-- `scan_fast::scan_num_name_loop` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:851-898 scanNumNameLoop`): `NameRec::Num`. -/
private theorem scan_num_name_loop_wf {b : Slice Std.U8} (f : Nat) :
    ∀ {w : Bool} {i : Std.Usize} {seen : Std.U32} {n pre : Std.U64}
      {r : frontend.scan_types.NameRec} {j : Std.Usize},
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_num_name_loop_loop w b i seen n pre
        = ok (.Ok (r, j)) → NameRecWF r := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen n pre r j hf h
    rw [frontend.scan_fast.scan_num_name_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i _ p
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      have hilt := next_member_lt hres
      split at h
      · repeat' (first
          | exact (err_ne_ok h).elim
          | split at h
          | (obtain ⟨_, -, h⟩ := bind_eq_ok_iff.mp h))
        all_goals
          (simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
             Prod.mk.injEq] at h
           rw [← h.1]; trivial)
      · rename_i k ks v
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        split at h
        all_goals
          first
            | exact (err_ne_ok h).elim
            | (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   have he := slot_nat_prog hr1
                   obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                   exact ih _ (by omega) (le_refl _) h
                 · simp at h)
    · simp at h

/-- `scan_fast::scan_num_name` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:900-904 scanNumName`). -/
theorem scan_num_name_wf {b : Slice Std.U8} {i : Std.Usize}
    {r : frontend.scan_types.NameRec} {j : Std.Usize}
    (h : frontend.scan_fast.scan_num_name b i = ok (.Ok (r, j))) : NameRecWF r := by
  rw [frontend.scan_fast.scan_num_name] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
    exact scan_num_name_loop_wf (b.length - i2.val) (le_refl _) h
  · exact (err_ne_ok h).elim

/-- `scan_fast::scan_app_expr_loop` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1001-1049 scanAppExprLoop`):
`ExprRec::App`. -/
private theorem scan_app_expr_loop_wf {b : Slice Std.U8} (f : Nat) :
    ∀ {w : Bool} {i : Std.Usize} {seen : Std.U32} {arg fnx : Std.U64}
      {r : frontend.scan_types.ExprRec} {j : Std.Usize},
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_app_expr_loop_loop w b i seen arg fnx
        = ok (.Ok (r, j)) → ExprRecWF r := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen arg fnx r j hf h
    rw [frontend.scan_fast.scan_app_expr_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i _ p
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      have hilt := next_member_lt hres
      split at h
      · repeat' (first
          | exact (err_ne_ok h).elim
          | split at h
          | (obtain ⟨_, -, h⟩ := bind_eq_ok_iff.mp h))
        all_goals
          (simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
             Prod.mk.injEq] at h
           rw [← h.1]; trivial)
      · rename_i k ks v
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        split at h
        all_goals
          first
            | exact (err_ne_ok h).elim
            | (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   have he := slot_nat_prog hr1
                   obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                   exact ih _ (by omega) (le_refl _) h
                 · simp at h)
    · simp at h

/-- `scan_fast::scan_app_expr` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1051-1055 scanAppExpr`). -/
theorem scan_app_expr_wf {b : Slice Std.U8} {i : Std.Usize}
    {r : frontend.scan_types.ExprRec} {j : Std.Usize}
    (h : frontend.scan_fast.scan_app_expr b i = ok (.Ok (r, j))) : ExprRecWF r := by
  rw [frontend.scan_fast.scan_app_expr] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
    exact scan_app_expr_loop_wf (b.length - i2.val) (le_refl _) h
  · exact (err_ne_ok h).elim

/-- `scan_fast::scan_binder_expr_loop` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1074-1174 scanBinderExprLoop`): `ExprRec::Lam`
or `ExprRec::ForallE`, behind the `lam` flag. -/
private theorem scan_binder_expr_loop_wf {b : Slice Std.U8} (f : Nat) :
    ∀ {w : Bool} {lam : Bool} {i : Std.Usize} {seen : Std.U32} {bd ty : Std.U64}
      {pw : frontend.scan_types.PwRec}
      {r : frontend.scan_types.ExprRec} {j : Std.Usize},
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_binder_expr_loop_loop w b lam i seen bd ty pw
        = ok (.Ok (r, j)) → ExprRecWF r := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w lam i seen bd ty pw r j hf h
    rw [frontend.scan_fast.scan_binder_expr_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i _ p
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      have hilt := next_member_lt hres
      split at h
      · -- `Close`: `Lam` or `ForallE` behind the `lam` flag, neither of them
        -- with a string payload
        have hlam : ∀ er : frontend.scan_types.ExprRec,
            (if lam = true then ok (frontend.scan_types.ExprRec.Lam ty bd pw)
             else ok (frontend.scan_types.ExprRec.ForallE ty bd pw)) = ok er →
            ExprRecWF er := by
          intro er h1
          split at h1 <;>
            (simp only [Result.ok.injEq] at h1; rw [← h1]; trivial)
        have hexit : ∀ (i1 : Std.U32),
            (if (i1 != 15#u32) = true then
               frontend.scan_fast.err frontend.scan_types.ExprRec ni
                 frontend.scan_types.ErrTag.MissingKey
             else do
               let er ←
                 if lam = true then ok (frontend.scan_types.ExprRec.Lam ty bd pw)
                 else ok (frontend.scan_types.ExprRec.ForallE ty bd pw)
               let i2 ← ni + 1#usize
               ok (core.result.Result.Ok (er, i2)))
              = ok (core.result.Result.Ok (r, j)) → ExprRecWF r := by
          intro i1 h1
          split at h1
          · exact (err_ne_ok h1).elim
          · obtain ⟨er, her, h1⟩ := bind_eq_ok_iff.mp h1
            obtain ⟨i2, -, h1⟩ := bind_eq_ok_iff.mp h1
            simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
              Prod.mk.injEq] at h1
            rw [← h1.1]; exact hlam er her
        split at h
        · split at h
          · exact (err_ne_ok h).elim
          · obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
            exact hexit i1 h
        · obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
          exact hexit i1 h
      · rename_i k ks v
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        split at h
        all_goals
          first
            | exact (err_ne_ok h).elim
            | -- a `slot_nat` machine word
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   have he := slot_nat_prog hr1
                   obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                   exact ih _ (by omega) (le_refl _) h
                 · simp at h)
            | -- a sub-scanner closed by the `prog` guard
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                   split at h
                   · have he := prog_lt hb2 (by assumption)
                     obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                     exact ih _ (by omega) (le_refl _) h
                   · exact (err_ne_ok h).elim
                 · simp at h)
            | -- `scan_binder_info`'s bare `usize`
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨e, -, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · exact (err_ne_ok h).elim
                 · obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                   split at h
                   · have he := prog_lt hb2 (by assumption)
                     obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                     exact ih _ (by omega) (le_refl _) h
                   · exact (err_ne_ok h).elim)
    · simp at h


/-- `scan_fast::scan_lam_expr` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1176-1180 scanLamExpr`). -/
theorem scan_lam_expr_wf {b : Slice Std.U8} {i : Std.Usize}
    {r : frontend.scan_types.ExprRec} {j : Std.Usize}
    (h : frontend.scan_fast.scan_lam_expr b i = ok (.Ok (r, j))) : ExprRecWF r := by
  rw [frontend.scan_fast.scan_lam_expr] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
    exact scan_binder_expr_loop_wf (b.length - i2.val) (le_refl _) h
  · exact (err_ne_ok h).elim

/-- `scan_fast::scan_forall_expr` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1182-1186 scanForallExpr`). -/
theorem scan_forall_expr_wf {b : Slice Std.U8} {i : Std.Usize}
    {r : frontend.scan_types.ExprRec} {j : Std.Usize}
    (h : frontend.scan_fast.scan_forall_expr b i = ok (.Ok (r, j))) : ExprRecWF r := by
  rw [frontend.scan_fast.scan_forall_expr] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
    exact scan_binder_expr_loop_wf (b.length - i2.val) (le_refl _) h
  · exact (err_ne_ok h).elim

/-- `scan_fast::scan_let_expr_loop` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1188-1281 scanLetExprLoop`): `ExprRec::LetE`. -/
private theorem scan_let_expr_loop_wf {b : Slice Std.U8} (f : Nat) :
    ∀ {w : Bool} {i : Std.Usize} {seen : Std.U32} {bd ty vl : Std.U64}
      {r : frontend.scan_types.ExprRec} {j : Std.Usize},
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_let_expr_loop_loop w b i seen bd ty vl
        = ok (.Ok (r, j)) → ExprRecWF r := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen bd ty vl r j hf h
    rw [frontend.scan_fast.scan_let_expr_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i _ p
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      have hilt := next_member_lt hres
      split at h
      · repeat' (first
          | exact (err_ne_ok h).elim
          | split at h
          | (obtain ⟨_, -, h⟩ := bind_eq_ok_iff.mp h))
        all_goals
          (simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
             Prod.mk.injEq] at h
           rw [← h.1]; trivial)
      · rename_i k ks v
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        split at h
        all_goals
          first
            | exact (err_ne_ok h).elim
            | -- a `slot_nat` machine word
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   have he := slot_nat_prog hr1
                   obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                   exact ih _ (by omega) (le_refl _) h
                 · simp at h)
            | -- a sub-scanner closed by the `prog` guard
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                   split at h
                   · have he := prog_lt hb2 (by assumption)
                     obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                     exact ih _ (by omega) (le_refl _) h
                   · exact (err_ne_ok h).elim
                 · simp at h)
    · simp at h


/-- `scan_fast::scan_let_expr` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1283-1287 scanLetExpr`). -/
theorem scan_let_expr_wf {b : Slice Std.U8} {i : Std.Usize}
    {r : frontend.scan_types.ExprRec} {j : Std.Usize}
    (h : frontend.scan_fast.scan_let_expr b i = ok (.Ok (r, j))) : ExprRecWF r := by
  rw [frontend.scan_fast.scan_let_expr] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
    exact scan_let_expr_loop_wf (b.length - i2.val) (le_refl _) h
  · exact (err_ne_ok h).elim

/-- `scan_fast::scan_const_expr_loop` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1289-1338 scanConstExprLoop`):
`ExprRec::Const`. -/
private theorem scan_const_expr_loop_wf {b : Slice Std.U8} (f : Nat) :
    ∀ {w : Bool} {i : Std.Usize} {seen : Std.U32} {nm : Std.U64}
      {us : alloc.vec.Vec Std.U64}
      {r : frontend.scan_types.ExprRec} {j : Std.Usize},
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_const_expr_loop_loop w b i seen nm us
        = ok (.Ok (r, j)) → ExprRecWF r := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen nm us r j hf h
    rw [frontend.scan_fast.scan_const_expr_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i _ p
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      have hilt := next_member_lt hres
      split at h
      · repeat' (first
          | exact (err_ne_ok h).elim
          | split at h
          | (obtain ⟨_, -, h⟩ := bind_eq_ok_iff.mp h))
        all_goals
          (simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
             Prod.mk.injEq] at h
           rw [← h.1]; trivial)
      · rename_i k ks v
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        split at h
        all_goals
          first
            | exact (err_ne_ok h).elim
            | -- a `slot_nat` machine word
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   have he := slot_nat_prog hr1
                   obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                   exact ih _ (by omega) (le_refl _) h
                 · simp at h)
            | -- a sub-scanner closed by the `prog` guard
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                   split at h
                   · have he := prog_lt hb2 (by assumption)
                     obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                     exact ih _ (by omega) (le_refl _) h
                   · exact (err_ne_ok h).elim
                 · simp at h)
    · simp at h


/-- `scan_fast::scan_const_expr` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1340-1344 scanConstExpr`). -/
theorem scan_const_expr_wf {b : Slice Std.U8} {i : Std.Usize}
    {r : frontend.scan_types.ExprRec} {j : Std.Usize}
    (h : frontend.scan_fast.scan_const_expr b i = ok (.Ok (r, j))) : ExprRecWF r := by
  rw [frontend.scan_fast.scan_const_expr] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
    exact scan_const_expr_loop_wf (b.length - i2.val) (le_refl _) h
  · exact (err_ne_ok h).elim

/-- `scan_fast::scan_proj_expr_loop` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1346-1404 scanProjExprLoop`): `ExprRec::Proj`. -/
private theorem scan_proj_expr_loop_wf {b : Slice Std.U8} (f : Nat) :
    ∀ {w : Bool} {i : Std.Usize} {seen : Std.U32} {ix st tn : Std.U64}
      {r : frontend.scan_types.ExprRec} {j : Std.Usize},
      b.length - i.val ≤ f →
      frontend.scan_fast.scan_proj_expr_loop_loop w b i seen ix st tn
        = ok (.Ok (r, j)) → ExprRecWF r := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i seen ix st tn r j hf h
    rw [frontend.scan_fast.scan_proj_expr_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i _ p
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      have hilt := next_member_lt hres
      split at h
      · repeat' (first
          | exact (err_ne_ok h).elim
          | split at h
          | (obtain ⟨_, -, h⟩ := bind_eq_ok_iff.mp h))
        all_goals
          (simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
             Prod.mk.injEq] at h
           rw [← h.1]; trivial)
      · rename_i k ks v
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        split at h
        all_goals
          first
            | exact (err_ne_ok h).elim
            | -- a `slot_nat` machine word
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   have he := slot_nat_prog hr1
                   obtain ⟨seen1, -, h⟩ := bind_eq_ok_iff.mp h
                   exact ih _ (by omega) (le_refl _) h
                 · simp at h)
    · simp at h


/-- `scan_fast::scan_proj_expr` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:1406-1410 scanProjExpr`). -/
theorem scan_proj_expr_wf {b : Slice Std.U8} {i : Std.Usize}
    {r : frontend.scan_types.ExprRec} {j : Std.Usize}
    (h : frontend.scan_fast.scan_proj_expr b i = ok (.Ok (r, j))) : ExprRecWF r := by
  rw [frontend.scan_fast.scan_proj_expr] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
    exact scan_proj_expr_loop_wf (b.length - i2.val) (le_refl _) h
  · exact (err_ne_ok h).elim

/-! ## The line dispatcher

`scan_line_loop` accumulates a `LinePayload` and turns it into a `LineRec` at
the closing brace, so the invariant is `LinePayloadWF`: the one payload that
carries a name and the one that carries an expression are well formed, and the
other three have no clause.  The `Key` arms are the module's slot idioms again,
now with the payload the slot installs: `trivial` wherever the payload is a
machine word or a declaration, and one of the scanners' lemmas above wherever
it is a record. -/

/-- The parse state of one line: what `scan_line_loop` carries between
members. -/
private def LinePayloadWF : frontend.scan_fast.LinePayload → Prop
  | .Name r => NameRecWF r
  | .Expr r => ExprRecWF r
  | _ => True

/-- `scan_fast::scan_line_loop` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:2462-2609 scanLineLoop`,
`ConLeche/Frontend/Scan/Naive.lean:645-784 naiveLineLoop`). -/
private theorem scan_line_loop_wf {b : Slice Std.U8} (f : Nat) :
    ∀ {w : Bool} {i : Std.Usize} {ik : Std.U8} {idx : Std.U64}
      {pl : frontend.scan_fast.LinePayload} {r : frontend.scan_types.LineRec}
      {j : Std.Usize},
      b.length - i.val ≤ f → LinePayloadWF pl →
      frontend.scan_fast.scan_line_loop_loop w b i ik idx pl = ok (.Ok (r, j)) →
      LineRecWF r := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro w i ik idx pl r j hf hpl h
    rw [frontend.scan_fast.scan_line_loop_loop.eq_def] at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i _ p
      obtain ⟨mem, ni, nw⟩ := p
      simp only [uncurry_apply_pair] at h
      have hilt := next_member_lt hres
      split at h
      · -- `Close`: the payload must match the index key, and then it *is* the
        -- record
        repeat' (first
          | exact (err_ne_ok h).elim
          | split at h
          | (obtain ⟨_, -, h⟩ := bind_eq_ok_iff.mp h))
        all_goals
          (simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
             Prod.mk.injEq] at h
           rw [← h.1]
           -- `trivial` reads the payload invariant straight off `hpl`
           trivial)
      · rename_i k ks v
        have hks := next_member_ge (b.length - i.val) i w k ks v ni nw (le_refl _) hres
        split at h
        all_goals
          first
            | exact (err_ne_ok h).elim
            | -- a `slot_nat` machine word wrapped in a fresh payload
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   have he := slot_nat_prog hr1
                   exact ih _ (by omega) (le_refl _) (by trivial) h
                 · simp at h
               · exact (err_ne_ok h).elim)
            | -- a sub-scanner closed by the `prog` guard
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                   split at h
                   · have he := prog_lt hb2 (by assumption)
                     exact ih _ (by omega) (le_refl _)
                       (by first
                             | trivial
                             | exact scan_app_expr_wf hr1
                             | exact scan_lam_expr_wf hr1
                             | exact scan_forall_expr_wf hr1
                             | exact scan_let_expr_wf hr1
                             | exact scan_const_expr_wf hr1
                             | exact scan_proj_expr_wf hr1
                             | exact scan_string_wf hr1) h
                   · exact (err_ne_ok h).elim
                 · simp at h
               · exact (err_ne_ok h).elim)
            | -- `"str"` / `"num"`: the two name scanners behind one `key_beq`
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · obtain ⟨b2, -, h⟩ := bind_eq_ok_iff.mp h
                 split at h <;>
                   (obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                    split at h
                    · rename_i _ p1
                      obtain ⟨x, e⟩ := p1
                      simp only [uncurry_apply_pair] at h
                      obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
                      split at h
                      · have he := prog_lt hb3 (by assumption)
                        exact ih _ (by omega) (le_refl _)
                          (by first
                                | exact scan_str_name_wf hr1
                                | exact scan_num_name_wf hr1) h
                      · exact (err_ne_ok h).elim
                    · simp at h)
               · exact (err_ne_ok h).elim)
            | -- `"max"` / `"imax"`: a two-element `scan_nat_list`
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨us, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   split at h
                   · exact (err_ne_ok h).elim
                   · obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                     split at h
                     · have he := prog_lt hb2 (by assumption)
                       obtain ⟨b3, -, h⟩ := bind_eq_ok_iff.mp h
                       split at h <;>
                         (obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
                          obtain ⟨i3, -, h⟩ := bind_eq_ok_iff.mp h
                          exact ih _ (by omega) (le_refl _) (by trivial) h)
                     · exact (err_ne_ok h).elim
                 · simp at h
               · exact (err_ne_ok h).elim)
            | -- `"meta"`: a braced object skipped wholesale
              (obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
               split at h
               · obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · exact (err_ne_ok h).elim
                 · obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
                   obtain ⟨e, -, h⟩ := bind_eq_ok_iff.mp h
                   split at h
                   · exact (err_ne_ok h).elim
                   · obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
                     split at h
                     · have he := prog_lt hb2 (by assumption)
                       exact ih _ (by omega) (le_refl _) (by trivial) h
                     · exact (err_ne_ok h).elim
               · exact (err_ne_ok h).elim)
            | -- `"in"` / `"il"` / `"ie"`: the index key, which leaves the
              -- payload alone
              (split at h
               · exact (err_ne_ok h).elim
               · obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
                 split at h
                 · rename_i _ p1
                   obtain ⟨x, e⟩ := p1
                   simp only [uncurry_apply_pair] at h
                   have he := slot_nat_prog hr1
                   exact ih _ (by omega) (le_refl _) hpl h
                 · simp at h)
    · simp at h

/-- **The file's product.**  `scan_fast::scan_line_fwd` (con-leche:
`ConLeche/Frontend/Scan/Fast.lean:2611-2634 scanLineFwd`,
`ConLeche/Frontend/Scan/Naive.lean:786-803 naiveLine`): every record the
scanner hands the parse is well formed, which is the one thing the parse needs
of the byte tier. -/
theorem scan_line_fwd_wf {b : Slice Std.U8} {i : Std.Usize}
    {r : frontend.scan_types.LineRec} {j : Std.Usize}
    (h : frontend.scan_fast.scan_line_fwd b i = ok (.Ok (r, j))) : LineRecWF r := by
  rw [frontend.scan_fast.scan_line_fwd] at h
  obtain ⟨s, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
  simp only at h
  split at h
  · -- a blank line
    obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; trivial
  · split at h
    · -- the chunk ran out before a newline did
      simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]; trivial
    · split at h
      · exact (err_ne_ok h).elim
      · obtain ⟨i3, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨rr, hrr, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · rename_i _ p
          obtain ⟨r1, j1⟩ := p
          simp only [uncurry_apply_pair] at h
          rw [frontend.scan_fast.scan_line_loop] at hrr
          have hw := scan_line_loop_wf (b.length - i3.val) (le_refl _) (by trivial) hrr
          obtain ⟨p1, -, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨i4, -, h⟩ := bind_eq_ok_iff.mp h
          split at h
          · obtain ⟨i5, -, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
              Prod.mk.injEq] at h
            rw [← h.1]; exact hw
          · split at h
            · simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                Prod.mk.injEq] at h
              rw [← h.1]; exact hw
            · exact (err_ne_ok h).elim
        · simp at h

-- The census is the standard three since task #86.  It was the three plus
-- SIXTY-EIGHT: Aeneas's `toStr` discharges the bound
-- `s.toByteArray.size <= U32.max` with `by decide +native` on every extracted
-- `&str` constant (`AENEAS_FINDINGS.md` §3.8), so the sixty-six key literals
-- `scan_fast::key_at` compares against (and `scan_fast::scan_bool`'s two) sat
-- in the DEFINITION of `scan_line_fwd` and every statement that named it
-- inherited them with nothing evaluated.  Task #86 spelled all sixty-eight
-- `[u8; N]`, which carries no axiom; nothing here evaluates a key either way,
-- so the theorem holds for every byte slice.

/-- info: 'ConRon.Refine.Frontend.scan_line_fwd_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms scan_line_fwd_wf

end ConRon.Refine.Frontend
