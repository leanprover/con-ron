/-
`kernel::pins_decode`'s **well-formedness invariant** — the piece of task #64
that was owed, and task #66's whole content.

`Refine/Pins.lean`'s `check_decls_pins_refines` says what the embedded pin list
*abstracts to*; it says nothing about how it was *built*.  The checker tier
needs the second fact too: `Refine/CheckerPins.lean`'s `PinsWF` — `ExprWF` for
each of the eight pinned expressions and each of the eight certificate lists,
`StrWF` for the toolchain string — is what makes `expr::beq` exact on a pin
(two pin lists can abstract to `natOpPinSets` with one carrying a stored hash
word the smart constructors would never have written).  It was the last
hypothesis the `conron.*_embedded` corollaries carried.

It is discharged here, and the argument is the one DESIGN.md §3.5 fixed at task
#5: **the `*WF` predicates are inductives whose constructors are the port's own
smart constructors**, and the decoder reaches every `Name`, `Level`, `PropWhen`
and `Expr` it installs through exactly one of them.  So the proof is a single
invariant, `TablesWF`, threaded through the record pass:

    TablesWF tb → record_* t i tb = ok (.Ok (tb', j)) → TablesWF tb'

with the four backward references (`name_ref`, `level_ref`, `pw_ref`,
`expr_ref`) reading a well-formed entry out of a well-formed table and the
three counted lists (`name_list`, `level_list`, `expr_list`) collecting them.
`decode_wf` is this file's product:

    decode t = ok (.Ok v) → CheckerPins.PinsWF v

for **every** byte slice, so nothing here is evaluated and the census is
con-leche's own three axioms — the embedded corollaries keep exactly the two
native-decide entries `Refine/Pins.lean` already had.

Two leaves are not table entries and are proved on their own:

* `StrWF` for a `<string>` field, through `Refine/PinsDec.lean` rather than a
  second walk over the port: `unescapeFrom` only ever appends a code point that
  passed its own `isValidChar` guard, or a printable ASCII byte, and
  `PinsBytes.read_string_refines` carries that list onto the port's `Vec<u32>`;
* `Nat.NatWF` for a `<bignum>` field, which has no `PinsDec` counterpart and is
  the file's one fuel induction: `ron::nat`'s `zero`/`add`/`mul` each return a
  normalised limb list, so the accumulator is well formed at every step.

This file sits *above* `Refine/CheckerPins.lean` in the import order — not
beside the other `Pins*` files — because `PinsWF` is defined there and
`Refine/CheckerPins.lean` already imports `Refine/Pins.lean`.  The predicate is
marked "to be unified into `Abs.lean`" at its definition; when that move
happens this file belongs beside `Refine/PinsRun.lean`, with nothing else
changed.

## `sorry` count in this file: 0
-/
import ConRon.Refine.CheckerPins

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.PinsWF

open ConRon.Refine ConRon.Refine.PinsBytes ConRon.Refine.CheckerPins

/-! ## Plumbing -/

/-- Every error arm of the decoder is `bad_text`, which never yields an `Ok`.
`Refine/PinsBytes.lean` keeps a private copy; it is four lines. -/
private theorem err_ne_ok {T : Type} {y : T}
    (h : (pins_decode.bad_text >>= fun ce =>
            ok (core.result.Result.Err ce : core.result.Result T core_types.CheckError))
        = ok (core.result.Result.Ok y)) : False := by
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ce, -, h⟩ := h
  simp at h

/-- `expr::dup` is `Arc::clone`, the identity, in the forward `= ok` form. -/
private theorem expr_dup_ok (e : expr.Expr) : expr.dup e = ok e := by
  cases e; simp [expr.dup]

/-- A push extends a "every entry satisfies `P`" invariant by the pushed
element: the one step every table and every counted list takes. -/
private theorem push_wf {α : Type} {P : α → Prop} {v w : alloc.vec.Vec α} {x : α}
    (hv : ∀ y ∈ v.val, P y) (hx : P x)
    (h : alloc.vec.Vec.push v x = ok w) : ∀ y ∈ w.val, P y := by
  rw [vec_push_val h]
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hv y hy
  · rw [List.mem_singleton.mp hy]; exact hx

/-- A `Vec` read at an in-range index, in the forward `= ok` form. -/
private theorem vec_index_ok {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (hi : i.val < v.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i
      = ok v.val[i.val] := by
  simp only [alloc.vec.Vec.index_slice_index]
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hi)
  rw [hy, hyv]

/-- What a `Vec` read hands back is one of the `Vec`'s entries: how a
well-formed table makes a well-formed reading. -/
private theorem vec_index_mem {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    {x : α} (hi : i.val < v.length)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    x ∈ v.val := by
  rw [vec_index_ok hi] at h
  rw [← Result.ok_injective h]
  exact List.getElem_mem (by scalar_tac)

/-! ## The first leaf: a `<string>` field is a sequence of code points

`StrWF` is `Refine/Abs.lean`'s "every word of the `Vec<u32>` is a valid Unicode
scalar value", which is what `absString` needs to be readable and what
`name::mk_str` asks of its payload.  The port's guard is
`pins_decode::is_valid_char`, and rather than walk `unescape_from` a second
time the fact is proved over `Refine/PinsDec.lean`'s `unescapeFrom` — a
*structural* recursion on the byte list — and carried across by
`PinsBytes.read_string_refines`, which already says the port's `Vec<u32>` is
that list of code points. -/

/-- The decoder's guard is Lean's predicate: below the surrogate block, or
above it and below `0x110000`. -/
private theorem isValidChar_of {n : Nat} (h : PinsDec.isValidChar n = true) :
    Nat.isValidChar n := by
  unfold PinsDec.isValidChar at h
  unfold Nat.isValidChar
  split_ifs at h with hc
  · omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega

/-- Every code point `unescapeFrom` appends is valid: an escape closes only
through `isValidChar`, and a literal byte is printable ASCII. -/
private theorem unescapeFrom_valid :
    ∀ (bs : PinsDec.Bytes) (v : Nat) (inEsc : Bool) (out cps : List Nat)
      (r : PinsDec.Bytes),
      (∀ c ∈ out, Nat.isValidChar c) →
      PinsDec.unescapeFrom bs v inEsc out = some (cps, r) →
      ∀ c ∈ cps, Nat.isValidChar c := by
  intro bs
  induction bs with
  | nil => intro v inEsc out cps r _ h; simp [PinsDec.unescapeFrom] at h
  | cons b rest ih =>
    intro v inEsc out cps r hout h
    rw [PinsDec.unescapeFrom] at h
    dsimp only at h
    by_cases h1 : (decide (b = 32) || decide (b = 10)) = true
    · rw [if_pos h1] at h
      by_cases h2 : inEsc = true
      · rw [if_pos h2] at h; simp at h
      · rw [if_neg h2] at h
        rw [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact hout
    · rw [if_neg h1] at h
      by_cases h2 : inEsc = true
      · rw [if_pos h2] at h
        by_cases h3 : b = 59
        · rw [if_pos h3] at h
          by_cases h4 : PinsDec.isValidChar v = true
          · rw [if_pos h4] at h
            refine ih 0 false (out ++ [v]) cps r ?_ h
            intro c hc
            rcases List.mem_append.mp hc with hc | hc
            · exact hout c hc
            · rw [List.mem_singleton.mp hc]; exact isValidChar_of h4
          · rw [if_neg h4] at h; simp at h
        · rw [if_neg h3] at h
          by_cases h5 : (decide (PinsDec.hexDigit b = 16) || decide (1114111 < v)) = true
          · rw [if_pos h5] at h; simp at h
          · rw [if_neg h5] at h
            exact ih (v * 16 + PinsDec.hexDigit b) true out cps r hout h
      · rw [if_neg h2] at h
        by_cases h3 : b = 92
        · rw [if_pos h3] at h
          exact ih 0 true out cps r hout h
        · rw [if_neg h3] at h
          by_cases h4 : (decide (b < 33) || decide (126 < b)) = true
          · rw [if_pos h4] at h; simp at h
          · rw [if_neg h4] at h
            refine ih 0 false (out ++ [b]) cps r ?_ h
            intro c hc
            rcases List.mem_append.mp hc with hc | hc
            · exact hout c hc
            · rw [List.mem_singleton.mp hc]
              simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h4
              unfold Nat.isValidChar
              omega

/-- A `<string>` field decodes to valid code points. -/
private theorem readString_valid {bs : PinsDec.Bytes} {cps : List Nat}
    {r : PinsDec.Bytes} (h : PinsDec.readString bs = some (cps, r)) :
    ∀ c ∈ cps, Nat.isValidChar c := by
  rw [PinsDec.readString] at h
  cases hidx : PinsDec.readIndex bs with
  | none => rw [hidx] at h; simp at h
  | some p =>
    obtain ⟨n, r1⟩ := p
    rw [hidx] at h
    dsimp only at h
    cases hsp : PinsDec.afterSpace r1 with
    | none => rw [hsp] at h; simp at h
    | some r2 =>
      rw [hsp] at h
      dsimp only at h
      cases hun : PinsDec.unescapeFrom r2 0 false [] with
      | none => rw [hun] at h; simp at h
      | some q =>
        obtain ⟨s, r3⟩ := q
        rw [hun] at h
        dsimp only at h
        split at h
        · rw [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          exact unescapeFrom_valid r2 0 false [] s r3 (by simp) hun
        · simp at h

/-- **The first leaf.**  `read_string`'s `Vec<u32>` is well formed. -/
theorem read_string_wf {t : Slice Std.U8} {i j : Std.Usize}
    {s : alloc.vec.Vec Std.U32}
    (h : pins_decode.read_string t i = ok (.Ok (s, j))) : StrWF s := by
  have hr := (PinsBytes.read_string_refines h).1
  intro c hc
  exact readString_valid hr c.val (List.mem_map_of_mem hc)

/-! ## The second leaf: a `<bignum>` field is a normalised `ron::nat`

`LiteralWF (.NatVal n)` is `ron::nat`'s own invariant (`Refine/Nat.lean`'s
`NatWF`: no leading zero limb), and unlike the string it has no `PinsDec`
counterpart — the reference decoder carries a `Nat`.  It is the file's one fuel
induction, and it is short because every arithmetic step the digit loop takes
is one of `ron::nat`'s constructors, each of which normalises. -/

private theorem read_big_nat_from_wf {t : Slice Std.U8} :
    ∀ (k : Nat) (i : Std.Usize) (acc : ron.nat.Nat), t.length - i.val ≤ k →
      Nat.NatWF acc → ∀ (n : ron.nat.Nat) (j : Std.Usize),
        pins_decode.read_big_nat_from t i acc = ok (.Ok (n, j)) → Nat.NatWF n := by
  intro k
  induction k with
  | zero =>
    intro i acc hk hacc n j h
    rw [pins_decode.read_big_nat_from.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbv : b.val = 256 := by
      rw [PinsBytes.byte_at_refines hb, PinsBytes.bytesFrom_eq_nil (by omega)]; rfl
    split at h
    · rename_i hlt; exact absurd hbv (by scalar_tac)
    · split at h
      · split at h
        · simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]; exact hacc
        · split at h
          · simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
            rw [← h.1]; exact hacc
          · exact (err_ne_ok h).elim
      · rename_i hgt; exact absurd hbv (by scalar_tac)
  | succ k ih =>
    intro i acc hk hacc n j h
    rw [pins_decode.read_big_nat_from.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hstop : ∀ (r : Result (core.result.Result (ron.nat.Nat × Std.Usize)
          core_types.CheckError)),
        r = ok (.Ok (acc, i)) → r = ok (.Ok (n, j)) → Nat.NatWF n := by
      intro r h1 h2
      rw [h1, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h2
      rw [← h2.1]; exact hacc
    split at h
    · split at h
      · exact hstop _ rfl h
      · split at h
        · exact hstop _ rfl h
        · exact (err_ne_ok h).elim
    · rename_i hge
      split at h
      · split at h
        · exact hstop _ rfl h
        · split at h
          · exact hstop _ rfl h
          · exact (err_ne_ok h).elim
      · rename_i hle
        -- a digit: the index really is in range, and the accumulator step is
        -- `nat::mul` then `nat::add`, both of which normalise.
        have hbv : b.val ≠ 256 := by scalar_tac
        have hi : i.val < t.length := by
          by_contra hc
          exact hbv (by
            rw [PinsBytes.byte_at_refines hb, PinsBytes.bytesFrom_eq_nil (by omega)]; rfl)
        simp only [bind_eq_ok_iff] at h
        obtain ⟨ten, hten, shifted, hshifted, d1, hd1, digit, hdigit, i2, hi2, nn, hnn, h⟩ := h
        have hi2v : i2.val = i.val + 1 := by
          have := Std.UScalar.add_equiv i 1#usize
          rw [hi2] at this; simpa using this.2.1
        exact ih i2 nn (by omega) (Nat.add_refines hnn).2 n j h

/-- **The second leaf.**  `read_big_nat`'s value is normalised. -/
theorem read_big_nat_wf {t : Slice Std.U8} {i j : Std.Usize} {n : ron.nat.Nat}
    (h : pins_decode.read_big_nat t i = ok (.Ok (n, j))) : Nat.NatWF n := by
  rw [pins_decode.read_big_nat] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  split at h
  · exact (err_ne_ok h).elim
  · split at h
    · exact (err_ne_ok h).elim
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨z, hz, h⟩ := h
      exact read_big_nat_from_wf (t.length - i.val) i z (le_refl _)
        (Nat.zero_refines hz).2 n j h

/-! ## The invariant

One clause per id space.  `Refine/Abs.lean`'s `NamesWF`/`LevelsWF`/`ExprsWF`
are already the "every entry" form; the `PropWhen` and pin-variant tables get
theirs spelled out because no abbreviation exists for them. -/

/-- Every value the decoder has installed so far was built by the port's own
smart constructors. -/
structure TablesWF (tb : pins_decode.Tables) : Prop where
  names : NamesWF tb.names
  levels : LevelsWF tb.levels
  pws : ∀ pw ∈ tb.pws.val, PropWhenWF pw
  exprs : ExprsWF tb.exprs
  sets : ∀ s ∈ tb.sets.val, NatOpPinSetWF s

/-- The empty tables are well formed. -/
theorem tables_new_wf {tb : pins_decode.Tables}
    (h : pins_decode.tables_new = ok tb) : TablesWF tb := by
  rw [pins_decode.tables_new, Result.ok.injEq] at h
  subst h
  exact ⟨by simp [NamesWF, alloc.vec.Vec.new], by simp [LevelsWF, alloc.vec.Vec.new],
    by simp [alloc.vec.Vec.new], by simp [ExprsWF, alloc.vec.Vec.new],
    by simp [alloc.vec.Vec.new]⟩

/-! ## The backward references

A reference is an index into a table that is already long enough, and the copy
the reader hands back is an `Arc::clone` — the identity in the model.  So a
well-formed table reads well-formed values, four times over. -/

theorem name_ref_wf {t : Slice Std.U8} {i j : Std.Usize} {tb : pins_decode.Tables}
    {n : name.Name} (htb : TablesWF tb)
    (h : pins_decode.name_ref t i tb = ok (.Ok (n, j))) : NameWF n := by
  rw [pins_decode.name_ref] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e => simp at h
  | Ok p =>
    obtain ⟨k, j1⟩ := p
    replace h : (if k < alloc.vec.Vec.len tb.names then _ else _)
        = ok (core.result.Result.Ok (n, j)) := h
    split at h
    · rename_i hlt
      have hkl : k.val < tb.names.length := by scalar_tac
      rw [vec_index_ok hkl] at h
      simp only [bind_tc_ok, name_dup_eq, Result.ok.injEq,
        core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact htb.names _ (List.getElem_mem (by scalar_tac))
    · exact (err_ne_ok h).elim

theorem level_ref_wf {t : Slice Std.U8} {i j : Std.Usize} {tb : pins_decode.Tables}
    {u : level.Level} (htb : TablesWF tb)
    (h : pins_decode.level_ref t i tb = ok (.Ok (u, j))) : LevelWF u := by
  rw [pins_decode.level_ref] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e => simp at h
  | Ok p =>
    obtain ⟨k, j1⟩ := p
    replace h : (if k < alloc.vec.Vec.len tb.levels then _ else _)
        = ok (core.result.Result.Ok (u, j)) := h
    split at h
    · rename_i hlt
      have hkl : k.val < tb.levels.length := by scalar_tac
      rw [vec_index_ok hkl] at h
      simp only [bind_tc_ok, level_dup_eq, Result.ok.injEq,
        core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact htb.levels _ (List.getElem_mem (by scalar_tac))
    · exact (err_ne_ok h).elim

theorem pw_ref_wf {t : Slice Std.U8} {i j : Std.Usize} {tb : pins_decode.Tables}
    {pw : prop_when.PropWhen} (htb : TablesWF tb)
    (h : pins_decode.pw_ref t i tb = ok (.Ok (pw, j))) : PropWhenWF pw := by
  rw [pins_decode.pw_ref] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e => simp at h
  | Ok p =>
    obtain ⟨k, j1⟩ := p
    replace h : (if k < alloc.vec.Vec.len tb.pws then _ else _)
        = ok (core.result.Result.Ok (pw, j)) := h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨pw0, hpw0, pw1, hpw1, h⟩ := h
      simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, PropWhen.dup_eq hpw1]
      exact htb.pws pw0 (vec_index_mem (by scalar_tac) hpw0)
    · exact (err_ne_ok h).elim

theorem expr_ref_wf {t : Slice Std.U8} {i j : Std.Usize} {tb : pins_decode.Tables}
    {e : expr.Expr} (htb : TablesWF tb)
    (h : pins_decode.expr_ref t i tb = ok (.Ok (e, j))) : ExprWF e := by
  rw [pins_decode.expr_ref] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e => simp at h
  | Ok p =>
    obtain ⟨k, j1⟩ := p
    replace h : (if k < alloc.vec.Vec.len tb.exprs then _ else _)
        = ok (core.result.Result.Ok (e, j)) := h
    split at h
    · rename_i hlt
      have hkl : k.val < tb.exprs.length := by scalar_tac
      rw [vec_index_ok hkl] at h
      simp only [bind_tc_ok, expr_dup_ok, Result.ok.injEq,
        core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact htb.exprs _ (List.getElem_mem (by scalar_tac))
    · exact (err_ne_ok h).elim


/-! ## The counted lists

`<count>` references, each read through the matching `*_ref` and pushed onto an
accumulator.  The recursion is on the *counter*, so the induction is too. -/

private theorem usub_eq {ty : Std.UScalarTy} {x y z : Std.UScalar ty}
    (h : x - y = ok z) : z.val = x.val - y.val := by
  have := Std.UScalar.sub_equiv x y
  rw [h] at this; simp at this; omega

private theorem name_list_from_wf {t : Slice Std.U8} {tb : pins_decode.Tables}
    (htb : TablesWF tb) :
    ∀ (kf : Nat) (i k : Std.Usize) (out : alloc.vec.Vec name.Name),
      k.val ≤ kf → NamesWF out →
      ∀ (res : alloc.vec.Vec name.Name) (j : Std.Usize),
        pins_decode.name_list_from t i tb k out = ok (.Ok (res, j)) → NamesWF res := by
  intro kf
  induction kf with
  | zero =>
    intro i k out hk hout res j h
    rw [pins_decode.name_list_from.eq_def] at h
    rw [if_pos (show k = 0#usize from by scalar_tac)] at h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hout
  | succ kf ih =>
    intro i k out hk hout res j h
    rw [pins_decode.name_list_from.eq_def] at h
    split at h
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hout
    · rename_i hk0
      have hkpos : 0 < k.val := by
        rcases Nat.eq_zero_or_pos k.val with _ | hp
        · exact absurd (by scalar_tac : k = 0#usize) hk0
        · exact hp
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok j1 =>
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e => simp at h
        | Ok p =>
          obtain ⟨x, m⟩ := p
          obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
          have hk1v : k1.val = k.val - 1 := usub_eq hk1
          exact ih m k1 out1 (by omega)
            (push_wf hout (name_ref_wf htb hr1) hout1) res j h

/-- `name_list` enters the loop at the count it just read, with an empty
accumulator. -/
theorem name_list_wf {t : Slice Std.U8} {i j : Std.Usize} {tb : pins_decode.Tables}
    {res : alloc.vec.Vec name.Name} (htb : TablesWF tb)
    (h : pins_decode.name_list t i tb = ok (.Ok (res, j))) : NamesWF res := by
  rw [pins_decode.name_list] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok p =>
    obtain ⟨n, j1⟩ := p
    exact name_list_from_wf htb n.val j1 n _ (le_refl _)
      (by simp [NamesWF, alloc.vec.Vec.new]) res j h

private theorem level_list_from_wf {t : Slice Std.U8} {tb : pins_decode.Tables}
    (htb : TablesWF tb) :
    ∀ (kf : Nat) (i k : Std.Usize) (out : alloc.vec.Vec level.Level),
      k.val ≤ kf → LevelsWF out →
      ∀ (res : alloc.vec.Vec level.Level) (j : Std.Usize),
        pins_decode.level_list_from t i tb k out = ok (.Ok (res, j)) → LevelsWF res := by
  intro kf
  induction kf with
  | zero =>
    intro i k out hk hout res j h
    rw [pins_decode.level_list_from.eq_def] at h
    rw [if_pos (show k = 0#usize from by scalar_tac)] at h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hout
  | succ kf ih =>
    intro i k out hk hout res j h
    rw [pins_decode.level_list_from.eq_def] at h
    split at h
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hout
    · rename_i hk0
      have hkpos : 0 < k.val := by
        rcases Nat.eq_zero_or_pos k.val with _ | hp
        · exact absurd (by scalar_tac : k = 0#usize) hk0
        · exact hp
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok j1 =>
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e => simp at h
        | Ok p =>
          obtain ⟨x, m⟩ := p
          obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
          have hk1v : k1.val = k.val - 1 := usub_eq hk1
          exact ih m k1 out1 (by omega)
            (push_wf hout (level_ref_wf htb hr1) hout1) res j h

/-- `level_list` enters the loop at the count it just read, with an empty
accumulator. -/
theorem level_list_wf {t : Slice Std.U8} {i j : Std.Usize} {tb : pins_decode.Tables}
    {res : alloc.vec.Vec level.Level} (htb : TablesWF tb)
    (h : pins_decode.level_list t i tb = ok (.Ok (res, j))) : LevelsWF res := by
  rw [pins_decode.level_list] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok p =>
    obtain ⟨n, j1⟩ := p
    exact level_list_from_wf htb n.val j1 n _ (le_refl _)
      (by simp [LevelsWF, alloc.vec.Vec.new]) res j h

private theorem expr_list_from_wf {t : Slice Std.U8} {tb : pins_decode.Tables}
    (htb : TablesWF tb) :
    ∀ (kf : Nat) (i k : Std.Usize) (out : alloc.vec.Vec expr.Expr),
      k.val ≤ kf → ExprsWF out →
      ∀ (res : alloc.vec.Vec expr.Expr) (j : Std.Usize),
        pins_decode.expr_list_from t i tb k out = ok (.Ok (res, j)) → ExprsWF res := by
  intro kf
  induction kf with
  | zero =>
    intro i k out hk hout res j h
    rw [pins_decode.expr_list_from.eq_def] at h
    rw [if_pos (show k = 0#usize from by scalar_tac)] at h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hout
  | succ kf ih =>
    intro i k out hk hout res j h
    rw [pins_decode.expr_list_from.eq_def] at h
    split at h
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hout
    · rename_i hk0
      have hkpos : 0 < k.val := by
        rcases Nat.eq_zero_or_pos k.val with _ | hp
        · exact absurd (by scalar_tac : k = 0#usize) hk0
        · exact hp
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok j1 =>
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e => simp at h
        | Ok p =>
          obtain ⟨x, m⟩ := p
          obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
          have hk1v : k1.val = k.val - 1 := usub_eq hk1
          exact ih m k1 out1 (by omega)
            (push_wf hout (expr_ref_wf htb hr1) hout1) res j h

/-- `expr_list` enters the loop at the count it just read, with an empty
accumulator. -/
theorem expr_list_wf {t : Slice Std.U8} {i j : Std.Usize} {tb : pins_decode.Tables}
    {res : alloc.vec.Vec expr.Expr} (htb : TablesWF tb)
    (h : pins_decode.expr_list t i tb = ok (.Ok (res, j))) : ExprsWF res := by
  rw [pins_decode.expr_list] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok p =>
    obtain ⟨n, j1⟩ := p
    exact expr_list_from_wf htb n.val j1 n _ (le_refl _)
      (by simp [ExprsWF, alloc.vec.Vec.new]) res j h


/-! ## The records

One lemma per record kind, and each is the same three steps: destructure the
reader chain, read the smart constructor's own `= ok` equation off the end of
it, and hand that equation to the matching `*WF` constructor.  Nothing about
bytes or indices is needed — the record's *shape* is what carries the
invariant. -/

/-- A record only ever replaces one table, so the other four clauses travel
unchanged.  Five one-liners, one per id space. -/
private theorem with_names {tb : pins_decode.Tables} {v : alloc.vec.Vec name.Name}
    (htb : TablesWF tb) (hv : NamesWF v) : TablesWF { tb with names := v } :=
  ⟨hv, htb.levels, htb.pws, htb.exprs, htb.sets⟩

private theorem with_levels {tb : pins_decode.Tables} {v : alloc.vec.Vec level.Level}
    (htb : TablesWF tb) (hv : LevelsWF v) : TablesWF { tb with levels := v } :=
  ⟨htb.names, hv, htb.pws, htb.exprs, htb.sets⟩

private theorem with_pws {tb : pins_decode.Tables}
    {v : alloc.vec.Vec prop_when.PropWhen} (htb : TablesWF tb)
    (hv : ∀ pw ∈ v.val, PropWhenWF pw) : TablesWF { tb with pws := v } :=
  ⟨htb.names, htb.levels, hv, htb.exprs, htb.sets⟩

private theorem with_exprs {tb : pins_decode.Tables} {v : alloc.vec.Vec expr.Expr}
    (htb : TablesWF tb) (hv : ExprsWF v) : TablesWF { tb with exprs := v } :=
  ⟨htb.names, htb.levels, htb.pws, hv, htb.sets⟩

private theorem with_sets {tb : pins_decode.Tables}
    {v : alloc.vec.Vec nat_op_pins.NatOpPinSet} (htb : TablesWF tb)
    (hv : ∀ s ∈ v.val, NatOpPinSetWF s) : TablesWF { tb with sets := v } :=
  ⟨htb.names, htb.levels, htb.pws, htb.exprs, hv⟩

/-- `expr::binder_meta` is `Arc::new`, so the datum's `PropWhen` is the one it
was given. -/
private theorem binder_meta_wf {pw : prop_when.PropWhen} {m : expr.BinderMeta}
    (hpw : PropWhenWF pw) (h : expr.binder_meta pw = ok m) : BinderMetaWF m := by
  simp only [expr.binder_meta, ptr_new_eq, bind_tc_ok, Result.ok.injEq] at h
  rw [← h]; exact hpw

/-- `expr::literal_nat` is `Arc::new` on a normalised bignum. -/
private theorem literal_nat_wf {n : ron.nat.Nat} {l : expr.Literal}
    (hn : Nat.NatWF n) (h : expr.literal_nat n = ok l) : LiteralWF l := by
  simp only [expr.literal_nat, ptr_new_eq, bind_tc_ok, Result.ok.injEq] at h
  rw [← h]; exact hn

/-- `expr::literal_str` is `Arc::new` on a code-point list. -/
private theorem literal_str_wf {s : alloc.vec.Vec Std.U32} {l : expr.Literal}
    (hs : StrWF s) (h : expr.literal_str s = ok l) : LiteralWF l := by
  simp only [expr.literal_str, ptr_new_eq, bind_tc_ok, Result.ok.injEq] at h
  rw [← h]; exact hs

/-! ### `N` — the name records -/

theorem record_name_num_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_name_num t i tb = ok (.Ok (tb', j))) : TablesWF tb' := by
  rw [pins_decode.record_name_num] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨pre, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok p1 =>
          obtain ⟨k, i4⟩ := p1
          obtain ⟨r4, hr4, h⟩ := bind_eq_ok_iff.mp h
          cases r4 with
          | Err e => simp at h
          | Ok i5 =>
            obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
              Prod.mk.injEq] at h
            rw [← h.1]
            exact with_names htb
              (push_wf htb.names (.num (name_ref_wf htb hr1) hn) hv)

theorem record_name_str_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_name_str t i tb = ok (.Ok (tb', j))) : TablesWF tb' := by
  rw [pins_decode.record_name_str] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨pre, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok p1 =>
          obtain ⟨s, i4⟩ := p1
          obtain ⟨r4, hr4, h⟩ := bind_eq_ok_iff.mp h
          cases r4 with
          | Err e => simp at h
          | Ok i5 =>
            obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
              Prod.mk.injEq] at h
            rw [← h.1]
            exact with_names htb
              (push_wf htb.names
                (.str (name_ref_wf htb hr1) (read_string_wf hr3) hn) hv)

theorem record_name_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_name t i tb = ok (.Ok (tb', j))) : TablesWF tb' := by
  rw [pins_decode.record_name] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i2 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok i3 =>
      obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
        cases r2 with
        | Err e => simp at h
        | Ok i5 =>
          obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
            Prod.mk.injEq] at h
          rw [← h.1]
          exact with_names htb (push_wf htb.names (.anonymous hn) hv)
      · split at h
        · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
          exact record_name_str_wf htb h
        · split at h
          · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
            exact record_name_num_wf htb h
          · exact (err_ne_ok h).elim

/-! ### `L` — the level records -/

theorem record_level_param_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_level_param t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_level_param] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨n, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
          Prod.mk.injEq] at h
        rw [← h.1]
        exact with_levels htb
          (push_wf htb.levels (.param (name_ref_wf htb hr1) hl) hv)

theorem record_level_succ_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_level_succ t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_level_succ] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨u, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
          Prod.mk.injEq] at h
        rw [← h.1]
        exact with_levels htb
          (push_wf htb.levels (.succ (level_ref_wf htb hr1) hl) hv)

theorem record_level_binop_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} {isMax : Bool} (htb : TablesWF tb)
    (h : pins_decode.record_level_binop t i tb isMax = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_level_binop] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨u, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok p1 =>
          obtain ⟨w, i4⟩ := p1
          obtain ⟨r4, hr4, h⟩ := bind_eq_ok_iff.mp h
          cases r4 with
          | Err e => simp at h
          | Ok i5 =>
            dsimp only at h
            split at h
            · obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
              simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                Prod.mk.injEq] at h
              rw [← h.1]
              exact with_levels htb
                (push_wf htb.levels
                  (.max (level_ref_wf htb hr1) (level_ref_wf htb hr3) hl) hv)
            · obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
              simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                Prod.mk.injEq] at h
              rw [← h.1]
              exact with_levels htb
                (push_wf htb.levels
                  (.imax (level_ref_wf htb hr1) (level_ref_wf htb hr3) hl) hv)

theorem record_level_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_level t i tb = ok (.Ok (tb', j))) : TablesWF tb' := by
  rw [pins_decode.record_level] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i2 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok i3 =>
      obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
        cases r2 with
        | Err e => simp at h
        | Ok i5 =>
          obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
            Prod.mk.injEq] at h
          rw [← h.1]
          exact with_levels htb (push_wf htb.levels (.zero hl) hv)
      · split at h
        · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
          exact record_level_succ_wf htb h
        · split at h
          · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
            exact record_level_binop_wf htb h
          · split at h
            · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
              exact record_level_binop_wf htb h
            · split at h
              · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
                exact record_level_param_wf htb h
              · exact (err_ne_ok h).elim

/-! ### `W` — the prop-when records -/

theorem record_pw_zero_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_pw_zero t i tb = ok (.Ok (tb', j))) : TablesWF tb' := by
  rw [pins_decode.record_pw_zero] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨ps, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨pw, hpw, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
          Prod.mk.injEq] at h
        rw [← h.1]
        exact with_pws htb
          (push_wf htb.pws (.if_all_zero (name_list_wf htb hr1) hpw) hv)

theorem record_pw_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_pw t i tb = ok (.Ok (tb', j))) : TablesWF tb' := by
  rw [pins_decode.record_pw] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i2 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok i3 =>
      obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
        cases r2 with
        | Err e => simp at h
        | Ok i5 =>
          obtain ⟨pw, hpw, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
            Prod.mk.injEq] at h
          rw [← h.1]
          exact with_pws htb (push_wf htb.pws (.never hpw) hv)
      · split at h
        · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
          exact record_pw_zero_wf htb h
        · exact (err_ne_ok h).elim


/-! ### `E` — the expression records

Ten smart constructors behind eleven reader chains, and every chain is the
shape the `N` and `L` records already had: read the operands through the
backward references, take the constructor's own `= ok` equation off the end,
hand it to the matching `ExprWF` constructor.  `record_expr_binder` is the one
record with two of them, `lam` and `forall_e`, behind its `is_lam` flag. -/

theorem record_expr_bvar_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_expr_bvar t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_expr_bvar] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨k, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
          Prod.mk.injEq] at h
        rw [← h.1]
        exact with_exprs htb (push_wf htb.exprs (.bvar hex) hv)

theorem record_expr_fvar_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_expr_fvar t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_expr_fvar] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨idx, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok p1 =>
          obtain ⟨ty, i4⟩ := p1
          obtain ⟨r4, hr4, h⟩ := bind_eq_ok_iff.mp h
          cases r4 with
          | Err e => simp at h
          | Ok i5 =>
            obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
              Prod.mk.injEq] at h
            rw [← h.1]
            exact with_exprs htb
              (push_wf htb.exprs (.fvar (expr_ref_wf htb hr3) hex) hv)

theorem record_expr_sort_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_expr_sort t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_expr_sort] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨u, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
          Prod.mk.injEq] at h
        rw [← h.1]
        exact with_exprs htb
          (push_wf htb.exprs (.sort (level_ref_wf htb hr1) hex) hv)

theorem record_expr_const_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_expr_const t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_expr_const] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨n, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok p1 =>
          obtain ⟨us, i4⟩ := p1
          obtain ⟨r4, hr4, h⟩ := bind_eq_ok_iff.mp h
          cases r4 with
          | Err e => simp at h
          | Ok i5 =>
            obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
              Prod.mk.injEq] at h
            rw [← h.1]
            exact with_exprs htb
              (push_wf htb.exprs
                (.mk_const (name_ref_wf htb hr1) (level_list_wf htb hr3) hex) hv)

theorem record_expr_app_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_expr_app t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_expr_app] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨f, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok p1 =>
          obtain ⟨a, i4⟩ := p1
          obtain ⟨r4, hr4, h⟩ := bind_eq_ok_iff.mp h
          cases r4 with
          | Err e => simp at h
          | Ok i5 =>
            obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
              Prod.mk.injEq] at h
            rw [← h.1]
            exact with_exprs htb
              (push_wf htb.exprs
                (.app (expr_ref_wf htb hr1) (expr_ref_wf htb hr3) hex) hv)

theorem record_expr_binder_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} {isLam : Bool} (htb : TablesWF tb)
    (h : pins_decode.record_expr_binder t i tb isLam = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_expr_binder] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨ty, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok p1 =>
          obtain ⟨body, i4⟩ := p1
          obtain ⟨r4, hr4, h⟩ := bind_eq_ok_iff.mp h
          cases r4 with
          | Err e => simp at h
          | Ok i5 =>
            obtain ⟨r5, hr5, h⟩ := bind_eq_ok_iff.mp h
            cases r5 with
            | Err e => simp at h
            | Ok p2 =>
              obtain ⟨pw, i6⟩ := p2
              obtain ⟨r6, hr6, h⟩ := bind_eq_ok_iff.mp h
              cases r6 with
              | Err e => simp at h
              | Ok i7 =>
                obtain ⟨m, hm, h⟩ := bind_eq_ok_iff.mp h
                have hmw : BinderMetaWF m := binder_meta_wf (pw_ref_wf htb hr5) hm
                split at h
                · obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                  simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                    Prod.mk.injEq] at h
                  rw [← h.1]
                  exact with_exprs htb
                    (push_wf htb.exprs
                      (.lam (expr_ref_wf htb hr1) (expr_ref_wf htb hr3) hmw hex) hv)
                · obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                  simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                    Prod.mk.injEq] at h
                  rw [← h.1]
                  exact with_exprs htb
                    (push_wf htb.exprs
                      (.forall_e (expr_ref_wf htb hr1) (expr_ref_wf htb hr3) hmw hex)
                      hv)

theorem record_expr_let_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_expr_let t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_expr_let] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨ty, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok p1 =>
          obtain ⟨val, i4⟩ := p1
          obtain ⟨r4, hr4, h⟩ := bind_eq_ok_iff.mp h
          cases r4 with
          | Err e => simp at h
          | Ok i5 =>
            obtain ⟨r5, hr5, h⟩ := bind_eq_ok_iff.mp h
            cases r5 with
            | Err e => simp at h
            | Ok p2 =>
              obtain ⟨body, i6⟩ := p2
              obtain ⟨r6, hr6, h⟩ := bind_eq_ok_iff.mp h
              cases r6 with
              | Err e => simp at h
              | Ok i7 =>
                obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                  Prod.mk.injEq] at h
                rw [← h.1]
                exact with_exprs htb
                  (push_wf htb.exprs
                    (.let_e (expr_ref_wf htb hr1) (expr_ref_wf htb hr3)
                      (expr_ref_wf htb hr5) hex) hv)

theorem record_expr_nat_lit_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_expr_nat_lit t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_expr_nat_lit] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨n, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
          Prod.mk.injEq] at h
        rw [← h.1]
        exact with_exprs htb
          (push_wf htb.exprs
            (.lit (literal_nat_wf (read_big_nat_wf hr1) hl) hex) hv)

theorem record_expr_str_lit_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_expr_str_lit t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_expr_str_lit] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨s, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
          Prod.mk.injEq] at h
        rw [← h.1]
        exact with_exprs htb
          (push_wf htb.exprs
            (.lit (literal_str_wf (read_string_wf hr1) hl) hex) hv)

theorem record_expr_proj_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_expr_proj t i tb = ok (.Ok (tb', j))) :
    TablesWF tb' := by
  rw [pins_decode.record_expr_proj] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i1 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p =>
      obtain ⟨sn, i2⟩ := p
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok i3 =>
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok p1 =>
          obtain ⟨idx, i4⟩ := p1
          obtain ⟨r4, hr4, h⟩ := bind_eq_ok_iff.mp h
          cases r4 with
          | Err e => simp at h
          | Ok i5 =>
            obtain ⟨r5, hr5, h⟩ := bind_eq_ok_iff.mp h
            cases r5 with
            | Err e => simp at h
            | Ok p2 =>
              obtain ⟨str, i6⟩ := p2
              obtain ⟨r6, hr6, h⟩ := bind_eq_ok_iff.mp h
              cases r6 with
              | Err e => simp at h
              | Ok i7 =>
                obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                  Prod.mk.injEq] at h
                rw [← h.1]
                exact with_exprs htb
                  (push_wf htb.exprs
                    (.proj (name_ref_wf htb hr1) (expr_ref_wf htb hr5) hex) hv)

set_option maxHeartbeats 1000000 in
/-- The `E` dispatch: eleven kind bytes, and `l`/`f` share
`record_expr_binder` — the flat `split` chain `Refine/PinsRecords.lean` uses
on the same eleven, and with the same heartbeat allowance. -/
theorem record_expr_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_expr t i tb = ok (.Ok (tb', j))) : TablesWF tb' := by
  rw [pins_decode.record_expr] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok i2 =>
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok i3 =>
      obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · -- `b`: a bound variable
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_bvar_wf htb h
      split at h
      · -- `v`: a free variable
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_fvar_wf htb h
      split at h
      · -- `s`: a sort
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_sort_wf htb h
      split at h
      · -- `c`: a constant
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_const_wf htb h
      split at h
      · -- `a`: an application
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_app_wf htb h
      split at h
      · -- `l`: a lambda
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_binder_wf htb h
      split at h
      · -- `f`: a dependent function type
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_binder_wf htb h
      split at h
      · -- `t`: a `let`
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_let_wf htb h
      split at h
      · -- `n`: a bignum literal
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_nat_lit_wf htb h
      split at h
      · -- `g`: a string literal
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_str_lit_wf htb h
      split at h
      · -- `p`: a projection
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
        exact record_expr_proj_wf htb h
      exact (err_ne_ok h).elim


/-! ### `S` — the payload record

The one record that builds a `NatOpPinSet`, and the only place a `<string>`
field and the two eight-element lists meet.  `pins_eight`/`proofs_eight` are
counted lists like the three above, over `expr_ref` and `expr_list`; the
seventeen fields are then read back out of them by index, through `expr::dup`
and `env::exprs_copy`, both of which are the identity. -/

/-- `expr::dup` is `Arc::clone`, so it hands back the term it was given. -/
private theorem expr_dup_wf {e d : expr.Expr} (he : ExprWF e)
    (h : expr.dup e = ok d) : ExprWF d := by
  rw [expr_dup_ok e, Result.ok.injEq] at h
  rw [← h]; exact he

private theorem pins_eight_from_wf {t : Slice Std.U8} {tb : pins_decode.Tables}
    (htb : TablesWF tb) :
    ∀ (kf : Nat) (i k : Std.Usize) (out : alloc.vec.Vec expr.Expr),
      k.val ≤ kf → ExprsWF out →
      ∀ (res : alloc.vec.Vec expr.Expr) (j : Std.Usize),
        pins_decode.pins_eight_from t i tb k out = ok (.Ok (res, j)) → ExprsWF res := by
  intro kf
  induction kf with
  | zero =>
    intro i k out hk hout res j h
    rw [pins_decode.pins_eight_from.eq_def] at h
    rw [if_pos (show k = 0#usize from by scalar_tac)] at h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hout
  | succ kf ih =>
    intro i k out hk hout res j h
    rw [pins_decode.pins_eight_from.eq_def] at h
    split at h
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hout
    · rename_i hk0
      have hkpos : 0 < k.val := by
        rcases Nat.eq_zero_or_pos k.val with _ | hp
        · exact absurd (by scalar_tac : k = 0#usize) hk0
        · exact hp
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok j1 =>
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e => simp at h
        | Ok p =>
          obtain ⟨x, m⟩ := p
          obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
          have hk1v : k1.val = k.val - 1 := usub_eq hk1
          exact ih m k1 out1 (by omega)
            (push_wf hout (expr_ref_wf htb hr1) hout1) res j h

/-- The eight pinned terms are well formed. -/
theorem pins_eight_wf {t : Slice Std.U8} {i j : Std.Usize} {tb : pins_decode.Tables}
    {res : alloc.vec.Vec expr.Expr} (htb : TablesWF tb)
    (h : pins_decode.pins_eight t i tb = ok (.Ok (res, j))) : ExprsWF res := by
  rw [pins_decode.pins_eight] at h
  exact pins_eight_from_wf htb 8 i 8#usize _ (by scalar_tac)
    (by simp [ExprsWF, alloc.vec.Vec.new]) res j h

private theorem proofs_eight_from_wf {t : Slice Std.U8} {tb : pins_decode.Tables}
    (htb : TablesWF tb) :
    ∀ (kf : Nat) (i k : Std.Usize) (out : alloc.vec.Vec (alloc.vec.Vec expr.Expr)),
      k.val ≤ kf → (∀ es ∈ out.val, ExprsWF es) →
      ∀ (res : alloc.vec.Vec (alloc.vec.Vec expr.Expr)) (j : Std.Usize),
        pins_decode.proofs_eight_from t i tb k out = ok (.Ok (res, j)) →
        ∀ es ∈ res.val, ExprsWF es := by
  intro kf
  induction kf with
  | zero =>
    intro i k out hk hout res j h
    rw [pins_decode.proofs_eight_from.eq_def] at h
    rw [if_pos (show k = 0#usize from by scalar_tac)] at h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hout
  | succ kf ih =>
    intro i k out hk hout res j h
    rw [pins_decode.proofs_eight_from.eq_def] at h
    split at h
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hout
    · rename_i hk0
      have hkpos : 0 < k.val := by
        rcases Nat.eq_zero_or_pos k.val with _ | hp
        · exact absurd (by scalar_tac : k = 0#usize) hk0
        · exact hp
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok j1 =>
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e => simp at h
        | Ok p =>
          obtain ⟨x, m⟩ := p
          obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
          have hk1v : k1.val = k.val - 1 := usub_eq hk1
          exact ih m k1 out1 (by omega)
            (push_wf hout (expr_list_wf htb hr1) hout1) res j h

/-- The eight certificate lists are well formed. -/
theorem proofs_eight_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb : pins_decode.Tables} {res : alloc.vec.Vec (alloc.vec.Vec expr.Expr)}
    (htb : TablesWF tb)
    (h : pins_decode.proofs_eight t i tb = ok (.Ok (res, j))) :
    ∀ es ∈ res.val, ExprsWF es := by
  rw [pins_decode.proofs_eight] at h
  exact proofs_eight_from_wf htb 8 i 8#usize _ (by scalar_tac)
    (by simp [alloc.vec.Vec.new]) res j h

/-- **The `S` record.**  Seventeen fields, each read out of one of the two
eight-element lists and copied; the copies are the identity, so each field
carries the list entry's own derivation. -/
theorem record_pin_set_wf {t : Slice Std.U8} {i j : Std.Usize}
    {tb tb' : pins_decode.Tables} (htb : TablesWF tb)
    (h : pins_decode.record_pin_set t i tb = ok (.Ok (tb', j))) : TablesWF tb' := by
  rw [pins_decode.record_pin_set] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok p =>
    obtain ⟨toolchain, i1⟩ := p
    obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => simp at h
    | Ok p1 =>
      obtain ⟨pins, i2⟩ := p1
      have hpins : ExprsWF pins := pins_eight_wf htb hr1
      obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok p2 =>
        obtain ⟨proofs, i3⟩ := p2
        have hproofs : ∀ es ∈ proofs.val, ExprsWF es := proofs_eight_wf htb hr2
        obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
        cases r3 with
        | Err e => simp at h
        | Ok i4 =>
          simp only [] at h
          split at h
          · exact (err_ne_ok h).elim
          · rename_i hp8
            split at h
            · exact (err_ne_ok h).elim
            · rename_i hq8
              -- The two guards the record just passed, in the form the
              -- sixteen field reads want: both lists are exactly eight long.
              have hplen : pins.length = 8 := by scalar_tac
              have hqlen : proofs.length = 8 := by scalar_tac
              have hp0 : (0#usize).val < pins.length := by simp [hplen]
              have hp1 : (1#usize).val < pins.length := by simp [hplen]
              have hp2 : (2#usize).val < pins.length := by simp [hplen]
              have hp3 : (3#usize).val < pins.length := by simp [hplen]
              have hp4 : (4#usize).val < pins.length := by simp [hplen]
              have hp5 : (5#usize).val < pins.length := by simp [hplen]
              have hp6 : (6#usize).val < pins.length := by simp [hplen]
              have hp7 : (7#usize).val < pins.length := by simp [hplen]
              have hq0 : (0#usize).val < proofs.length := by simp [hqlen]
              have hq1 : (1#usize).val < proofs.length := by simp [hqlen]
              have hq2 : (2#usize).val < proofs.length := by simp [hqlen]
              have hq3 : (3#usize).val < proofs.length := by simp [hqlen]
              have hq4 : (4#usize).val < proofs.length := by simp [hqlen]
              have hq5 : (5#usize).val < proofs.length := by simp [hqlen]
              have hq6 : (6#usize).val < proofs.length := by simp [hqlen]
              have hq7 : (7#usize).val < proofs.length := by simp [hqlen]
              obtain ⟨a0, ha0, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨a1, ha1, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨a2, ha2, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨a3, ha3, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨a4, ha4, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨a5, ha5, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨a6, ha6, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b6, hb6, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨a7, ha7, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b7, hb7, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨c0, hc0, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨d0, hd0, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨d1, hd1, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨c2, hc2, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨d2, hd2, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨c3, hc3, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨d3, hd3, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨c4, hc4, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨d4, hd4, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨c5, hc5, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨d5, hd5, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨c6, hc6, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨d6, hd6, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨c7, hc7, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨d7, hd7, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v16, hv16, h⟩ := bind_eq_ok_iff.mp h
              simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                Prod.mk.injEq] at h
              rw [← h.1]
              refine with_sets htb (push_wf htb.sets ⟨read_string_wf hr, ?_, ?_,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hv16)
              · exact expr_dup_wf (hpins _ (vec_index_mem hp0 ha0)) hb0
              · exact expr_dup_wf (hpins _ (vec_index_mem hp1 ha1)) hb1
              · exact expr_dup_wf (hpins _ (vec_index_mem hp2 ha2)) hb2
              · exact expr_dup_wf (hpins _ (vec_index_mem hp3 ha3)) hb3
              · exact expr_dup_wf (hpins _ (vec_index_mem hp4 ha4)) hb4
              · exact expr_dup_wf (hpins _ (vec_index_mem hp5 ha5)) hb5
              · exact expr_dup_wf (hpins _ (vec_index_mem hp6 ha6)) hb6
              · exact expr_dup_wf (hpins _ (vec_index_mem hp7 ha7)) hb7
              · exact ConRon.Refine.Env.exprs_copy_wf
                  (hproofs _ (vec_index_mem hq0 hc0)) hd0
              · exact ConRon.Refine.Env.exprs_copy_wf
                  (hproofs _ (vec_index_mem hq1 hc1)) hd1
              · exact ConRon.Refine.Env.exprs_copy_wf
                  (hproofs _ (vec_index_mem hq2 hc2)) hd2
              · exact ConRon.Refine.Env.exprs_copy_wf
                  (hproofs _ (vec_index_mem hq3 hc3)) hd3
              · exact ConRon.Refine.Env.exprs_copy_wf
                  (hproofs _ (vec_index_mem hq4 hc4)) hd4
              · exact ConRon.Refine.Env.exprs_copy_wf
                  (hproofs _ (vec_index_mem hq5 hc5)) hd5
              · exact ConRon.Refine.Env.exprs_copy_wf
                  (hproofs _ (vec_index_mem hq6 hc6)) hd6
              · exact ConRon.Refine.Env.exprs_copy_wf
                  (hproofs _ (vec_index_mem hq7 hc7)) hd7


/-! ## The pass

`run_records` is a `partial_fixpoint`, so the invariant is carried by the same
byte budget `Refine/PinsRun.lean` spends on the value half: a record step reads
at least its own kind byte and the space after it, so the cursor has advanced
by at least two when the recursion is entered again, and `t.length - i.val` is
a decreasing measure.  The bounds themselves are not reproved here — they are
the second and third components of half (A)'s record lemmas. -/

/-- A machine-word step names the index it computes. -/
private theorem uadd_eq {ty : Std.UScalarTy} {x y z : Std.UScalar ty}
    (h : x + y = ok z) : z.val = x.val + y.val := by
  have := Std.UScalar.add_equiv x y
  rw [h] at this; simpa using this.2.1

/-- The footer installs nothing: it hands back the pin table it was given, so
the invariant's last clause *is* its conclusion. -/
theorem run_footer_wf {t : Slice Std.U8} {i : Std.Usize} {tb : pins_decode.Tables}
    {v : alloc.vec.Vec nat_op_pins.NatOpPinSet} (htb : TablesWF tb)
    (h : pins_decode.run_footer t i tb = ok (.Ok v)) : PinsWF v := by
  rw [pins_decode.run_footer] at h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · exact (err_ne_ok h).elim
  · obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact (err_ne_ok h).elim
    · obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok i5 =>
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        cases r1 with
        | Err e => simp at h
        | Ok p =>
          obtain ⟨n, i6⟩ := p
          obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
          cases r2 with
          | Err e => simp at h
          | Ok i7 =>
            simp only [] at h
            split at h
            · exact (err_ne_ok h).elim
            · split at h
              · exact (err_ne_ok h).elim
              · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
                rw [← h]
                exact htb.sets

/-- The pass, with the byte budget the record step spends.  Each of the five
record kinds preserves `TablesWF`, and the footer reads the invariant off the
table it stops at. -/
private theorem run_records_wf {t : Slice Std.U8} :
    ∀ (f : Nat) (i : Std.Usize) (tb : pins_decode.Tables),
      t.length - i.val ≤ f → TablesWF tb →
      ∀ (v : alloc.vec.Vec nat_op_pins.NatOpPinSet),
        pins_decode.run_records t i tb = ok (.Ok v) → PinsWF v := by
  intro f
  induction f with
  | zero =>
    intro i tb hf htb v h
    have hnil : bytesFrom t i = [] := bytesFrom_eq_nil (by omega)
    rw [pins_decode.run_records.eq_def] at h
    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
    have hkv : k.val = 256 := by rw [byte_at_refines hk, hnil]; rfl
    split at h
    · rename_i hk101
      rw [hk101] at hkv; simp at hkv
    · obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := uadd_eq hi1
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok jj =>
        exfalso
        obtain ⟨-, h1, h2⟩ := after_space_refines hr
        omega
  | succ f ih =>
    intro i tb hf htb v h
    rw [pins_decode.run_records.eq_def] at h
    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      exact run_footer_wf htb h
    · obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := uadd_eq hi1
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok jj =>
        obtain ⟨-, hb1, hb2⟩ := after_space_refines hr
        obtain ⟨step, hstep, h⟩ := bind_eq_ok_iff.mp h
        cases step with
        | Err e => simp at h
        | Ok sp =>
          obtain ⟨tb1, m⟩ := sp
          have hrec : TablesWF tb1 ∧ jj.val ≤ m.val ∧ m.val ≤ t.length := by
            split at hstep
            · obtain ⟨-, h1, h2⟩ := PinsRecords.record_name_refines hstep
              exact ⟨record_name_wf htb hstep, h1, h2⟩
            · split at hstep
              · obtain ⟨-, h1, h2⟩ := PinsRecords.record_level_refines hstep
                exact ⟨record_level_wf htb hstep, h1, h2⟩
              · split at hstep
                · obtain ⟨-, h1, h2⟩ := PinsRecords.record_pw_refines hstep
                  exact ⟨record_pw_wf htb hstep, h1, h2⟩
                · split at hstep
                  · obtain ⟨-, h1, h2⟩ := PinsRecords.record_expr_refines hstep
                    exact ⟨record_expr_wf htb hstep, h1, h2⟩
                  · split at hstep
                    · obtain ⟨-, h1, h2⟩ := PinsRun.record_pin_set_refines hstep
                      exact ⟨record_pin_set_wf htb hstep, h1, h2⟩
                    · exfalso
                      obtain ⟨ce, -, hstep⟩ := bind_eq_ok_iff.mp hstep
                      simp at hstep
          exact ih m tb1 (by omega) hrec.1 v h

/-! ## The product

`decode_wf` holds for **every** byte slice, so nothing here is evaluated: the
`conron.*_embedded` capstones get their `PinsWF pins` from the same theorem
that any other input would get it from. -/

/-- **The product.**  Whatever `kernel::pins_decode` decodes, every node of it
was built by the port's own smart constructors. -/
theorem decode_wf {t : Slice Std.U8} {v : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (h : pins_decode.decode t = ok (.Ok v)) : PinsWF v := by
  rw [pins_decode.decode] at h
  obtain ⟨hdr, hhdr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨tn, htn, h⟩ := bind_eq_ok_iff.mp h
    exact run_records_wf t.length (alloc.vec.Vec.len hdr) tn (by omega)
      (tables_new_wf htn) v h
  · exact (err_ne_ok h).elim

/-- The embedded pin text is a byte slice like any other. -/
theorem decode_embedded_wf {v : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (h : pins_decode.decode_embedded = ok (.Ok v)) : PinsWF v := by
  rw [pins_decode.decode_embedded] at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  exact decode_wf h

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`decode_wf` is the file's product and it is proved for every byte slice, so
its census is con-leche's own three and nothing else — in particular nothing
native.  `decode_embedded_wf` names the embedded constant, so it picks up
`pins_text.PINS_TEXT._native.decide.ax_1`, the one Aeneas's `toStr` already
spent on *that constant's definition* (`AENEAS_FINDINGS.md` §3.8); nothing is
evaluated by this file.  Since **task #74** that single entry is the whole
difference between the `conron.*_embedded` corollaries' census and the general
pair's: task #64's second entry, `pins_closed`'s sealed computation, is gone
with `pins_closed`. -/

/-- info: 'ConRon.Refine.PinsWF.decode_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decode_wf

/-- info: 'ConRon.Refine.PinsWF.decode_embedded_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms decode_embedded_wf

end ConRon.Refine.PinsWF
