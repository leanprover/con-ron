/-
# `ConRon.Refine2.Frontend.Olean.Names` — a name as the command line spells it

**Task #142, Theorem 2.**  `olean/files.rs`'s scan of a name against upstream's `scanName`,
over the strings' code points.  `parse_mod_name` is exact.  `parse_const_name` reads a
numeric component with `digits_value`, which stops at `u64::MAX` where upstream's `toNat!`
goes on, so it is stated under `DigitsFit`: no run of digits of the input is past the word.
-/
import ConRon.Refine2.Frontend.Olean.Region

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.files

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Refine (absString absName StrWF NameWF vec_push_val)
open ConRon.Refine.Name (mk_str_refines mk_num_refines mk_str_wf mk_num_wf anonymous_refines anonymous_wf)
open ConLeche.Frontend.Olean (scanName parseModName parseConstName)

/-! ## The characters of a stored string -/

theorem absString_toList' (s : alloc.vec.Vec Std.U32) :
    (absString s).toList = s.val.map fun c => Char.ofNat c.val := by
  rw [absString, String.toList_ofList]

theorem vec_len_val {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.len v).val = v.val.length := by
  simp

@[simp] theorem u64_val_lit10 : (10#u64 : Std.U64).val = 10 := by decide

theorem str_wf_new' : StrWF (alloc.vec.Vec.new Std.U32) := by
  simp [StrWF, alloc.vec.Vec.new]

theorem absString_new : absString (alloc.vec.Vec.new Std.U32) = "" := by
  simp [absString, alloc.vec.Vec.new]

theorem str_wf_push {v w : alloc.vec.Vec Std.U32} {x : Std.U32} (hv : StrWF v)
    (hx : Nat.isValidChar x.val) (h : alloc.vec.Vec.push v x = ok w) : StrWF w := by
  rw [StrWF, vec_push_val h]
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hv y hy
  · rw [List.mem_singleton.mp hy]; exact hx

theorem absString_push {v w : alloc.vec.Vec Std.U32} {x : Std.U32}
    (h : alloc.vec.Vec.push v x = ok w) :
    absString w = (absString v).push (Char.ofNat x.val) := by
  apply String.toList_inj.mp
  rw [String.toList_push, absString_toList', absString_toList', vec_push_val h]
  simp

theorem char_ofNat_toNat {n : Nat} (hv : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

/-- A stored character against a literal, on the abstraction. -/
theorem char_beq {c l : Std.U32} {k : Char} (hc : Nat.isValidChar c.val) (hl : l.val = k.toNat) :
    (Char.ofNat c.val == k) = decide (c = l) := by
  by_cases h : c = l
  · subst h
    simp only [decide_true, beq_iff_eq]
    apply Char.toNat_inj.mp
    rw [char_ofNat_toNat hc, hl]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he
    apply h
    apply UScalar.eq_of_val_eq
    rw [hl, ← he, char_ofNat_toNat hc]

/-! ## `all_digits`, `digits_value` -/

/-- A code point that is a decimal digit. -/
@[reducible] def isDigitW (c : Std.U32) : Bool := decide (48 ≤ c.val) && decide (c.val ≤ 57)

theorem all_digits_loop_eq (cur : alloc.vec.Vec Std.U32) (i : Std.Usize) {o : Bool}
    (h : all_digits_loop cur i = ok o) : o = (cur.val.drop i.val).all isDigitW := by
  rw [all_digits_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len cur
  · rw [ite_eq_left hlt] at h
    peel h as x, hx
    obtain ⟨hi, rfl⟩ := vec_index_eq hx
    have hd : cur.val.drop i.val = cur.val[i.val] :: cur.val.drop (i.val + 1) :=
      (List.drop_eq_getElem_cons hi)
    rw [hd, List.all_cons]
    by_cases h48 : cur.val[i.val] < 48#u32
    · rw [ite_eq_left h48] at h
      cases Result.ok_injective h
      have : ¬ 48 ≤ (cur.val[i.val]).val := by
        have : (cur.val[i.val]).val < (48#u32 : Std.U32).val := h48
        simpa using this
      simp [isDigitW, this]
    rw [ite_eq_right h48] at h
    have h48' : 48 ≤ (cur.val[i.val]).val := by
      have : ¬ (cur.val[i.val]).val < (48#u32 : Std.U32).val := h48
      simpa using this
    by_cases h57 : cur.val[i.val] > 57#u32
    · rw [ite_eq_left h57] at h
      cases Result.ok_injective h
      have : ¬ (cur.val[i.val]).val ≤ 57 := by
        have : (57#u32 : Std.U32).val < (cur.val[i.val]).val := h57
        simpa using this
      simp [isDigitW, this]
    rw [ite_eq_right h57] at h
    have h57' : (cur.val[i.val]).val ≤ 57 := by
      have : ¬ (57#u32 : Std.U32).val < (cur.val[i.val]).val := h57
      simpa using this
    peel h as i3, hi3
    have hv := ConRon.Refine.Nat.uadd_val hi3
    have e : i3.val = i.val + 1 := by rw [hv]; rfl
    have := all_digits_loop_eq cur i3 h
    rw [e] at this
    rw [this]
    simp [isDigitW, h48', h57']
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : cur.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len cur).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le this]; rfl
termination_by cur.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len cur).val := hlt
  rw [vec_len_val] at this
  omega

theorem char_isDigit_toNat (k : Char) :
    k.isDigit = (decide (48 ≤ k.toNat) && decide (k.toNat ≤ 57)) := by
  have h1 : ('0'.val ≤ k.val) ↔ 48 ≤ k.toNat := UInt32.le_iff_toNat_le
  have h2 : (k.val ≤ '9'.val) ↔ k.toNat ≤ 57 := UInt32.le_iff_toNat_le
  show (decide ('0'.val ≤ k.val) && decide (k.val ≤ '9'.val)) = _
  simp only [h1, h2]

theorem isDigitW_abs {c : Std.U32} (hc : Nat.isValidChar c.val) :
    (Char.ofNat c.val).isDigit = isDigitW c := by
  rw [char_isDigit_toNat, char_ofNat_toNat hc]

theorem all_abs_list (l : List Std.U32) (hs : ∀ c ∈ l, Nat.isValidChar c.val) :
    (l.map fun c => Char.ofNat c.val).all Char.isDigit = l.all isDigitW := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    simp only [List.map_cons, List.all_cons]
    rw [isDigitW_abs (hs c (.head _)), ih (fun x hx => hs x (.tail _ hx))]

theorem all_abs {cur : alloc.vec.Vec Std.U32} (hs : StrWF cur) :
    (absString cur).all Char.isDigit = cur.val.all isDigitW := by
  rw [String.all_bool_eq, absString_toList']
  exact all_abs_list _ hs

/-- **`all_digits` is `cur.all Char.isDigit`.** -/
theorem all_digits_eq {cur : alloc.vec.Vec Std.U32} {o : Bool} (hs : StrWF cur)
    (h : all_digits cur = ok o) : o = (absString cur).all Char.isDigit := by
  rw [all_digits] at h
  rw [all_digits_loop_eq cur _ h, all_abs hs]
  rfl

/-- The value of a run of digits after `v`. -/
def digValFrom (l : List Std.U32) (v : Nat) : Nat :=
  l.foldl (fun v c => v * 10 + (c.val - 48)) v

theorem digValFrom_ge (l : List Std.U32) (v : Nat) : v ≤ digValFrom l v := by
  induction l generalizing v with
  | nil => exact Nat.le_refl _
  | cons c t ih =>
    have := ih (v * 10 + (c.val - 48))
    simp only [digValFrom, List.foldl_cons] at this ⊢
    omega

theorem digits_value_loop_eq (cur : alloc.vec.Vec Std.U32) (v : Std.U64) (i : Std.Usize) {o : Std.U64}
    (h : digits_value_loop cur v i = ok o) :
    o.val = min (digValFrom (cur.val.drop i.val) v.val) (2 ^ 64 - 1) := by
  rw [digits_value_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len cur
  · rw [ite_eq_left hlt] at h
    peel h as x, hx
    obtain ⟨hi, rfl⟩ := vec_index_eq hx
    have hd : cur.val.drop i.val = cur.val[i.val] :: cur.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hi
    peel h as i3, hi3
    peel h as d, hd'
    cases Result.ok_injective (show ok _ = ok d from hd')
    peel h as i4, hi4
    peel h as i5, hi5
    have v3 := ConRon.Refine.HashMap.uscalar_sub_eq hi3
    have vd : (UScalar.cast UScalarTy.U64 i3).val = i3.val := cast_u64_u32 i3
    have v4 := ConRon.Refine.HashMap.uscalar_sub_eq hi4
    rw [u64_max_val, vd] at v4
    have v5 := ConRon.Refine.HashMap.uscalar_div_eq hi5
    rw [u64_val_lit10] at v5
    have l48 : (48#u32 : Std.U32).val = 48 := by decide
    rw [l48] at v3
    rw [hd]
    simp only [digValFrom, List.foldl_cons]
    by_cases hgt : v > i5
    · rw [ite_eq_left hgt] at h
      cases Result.ok_injective h
      have hg : i5.val < v.val := hgt
      have := digValFrom_ge (cur.val.drop (i.val + 1)) (v.val * 10 + ((cur.val[i.val]).val - 48))
      simp only [digValFrom] at this
      rw [u64_max_val]
      omega
    rw [ite_eq_right hgt] at h
    have hg : ¬ i5.val < v.val := hgt
    peel h as i6, hi6
    peel h as v1, hv1
    peel h as i7, hi7
    have v6 := ConRon.Refine.HashMap.uscalar_mul_eq hi6
    rw [u64_val_lit10] at v6
    have v1v := ConRon.Refine.HashMap.uscalar_add_eq hv1
    rw [vd] at v1v
    have e7 : i7.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi7]; rfl
    have ih := digits_value_loop_eq cur v1 i7 h
    rw [e7] at ih
    rw [ih]
    have e1 : v1.val = v.val * 10 + ((cur.val[i.val]).val - 48) := by omega
    rw [e1]
    rfl
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : cur.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len cur).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le this]
    have := u64_lt v
    simp only [digValFrom, List.foldl_nil]
    omega
termination_by cur.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len cur).val := hlt
  rw [vec_len_val] at this
  omega

/-- The value of a run of digits. -/
abbrev digVal (l : List Std.U32) : Nat := digValFrom l 0

/-- **`digits_value` is the digits' value, stopped at `u64::MAX`.** -/
theorem digits_value_eq {cur : alloc.vec.Vec Std.U32} {o : Std.U64} (h : digits_value cur = ok o) :
    o.val = min (digVal cur.val) (2 ^ 64 - 1) := by
  rw [digits_value] at h
  exact digits_value_loop_eq cur _ _ h

theorem digit_ne_underscore {c : Char} (h : c.isDigit = true) : c ≠ '_' := by
  rintro rfl; revert h; decide

theorem forIn_digits {f : Char → Option Bool × Bool → Id (ForInStep (Option Bool × Bool))}
    (hf : ∀ c p, c.isDigit = true → f c p = pure (.yield (none, true))) (l : List Char)
    (hd : l.all Char.isDigit = true) (b : Bool) :
    forIn (m := Id) l (none, b) f = pure (none, if l = [] then b else true) := by
  induction l generalizing b with
  | nil => rfl
  | cons c t ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hd
    rw [List.forIn_cons, hf _ _ hd.1]
    show forIn (m := Id) t (none, true) f = _
    rw [ih hd.2]
    simp

/-- Upstream's `isNat` of a nonempty run of digits. -/
theorem isNat_digits {l : List Char} (hne : l ≠ []) (hd : l.all Char.isDigit = true) :
    (String.ofList l).toSlice.isNat = true := by
  simp only [String.Slice.isNat, Id.run, String.Slice.forIn_eq_forIn_toList, String.copy_toSlice,
    String.toList_ofList]
  rw [forIn_digits (fun c p hc => ?_) l hd false]
  · simp only [hne, ↓reduceIte]; rfl
  · simp [digit_ne_underscore hc, hc]

theorem foldl_digits (l : List Std.U32) (hs : ∀ c ∈ l, Nat.isValidChar c.val)
    (hd : l.all isDigitW = true) (v : Nat) :
    (l.map fun c => Char.ofNat c.val).foldl
      (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) v = digValFrom l v := by
  induction l generalizing v with
  | nil => rfl
  | cons c t ih =>
    rw [List.all_cons, Bool.and_eq_true] at hd
    have hc := isDigitW_abs (hs c (.head _))
    have hn : Char.ofNat c.val ≠ '_' := digit_ne_underscore (by rw [hc]; exact hd.1)
    simp only [List.map_cons, List.foldl_cons, hn, ↓reduceIte, char_ofNat_toNat (hs c (.head _))]
    exact ih (fun x hx => hs x (.tail _ hx)) hd.2 _

/-- Upstream's `toNat!` of a nonempty run of digits. -/
theorem toNat!_digits {s : alloc.vec.Vec Std.U32} (hs : StrWF s) (hne : s.val ≠ [])
    (hd : s.val.all isDigitW = true) : (absString s).toNat! = digVal s.val := by
  have hl : (s.val.map fun c => Char.ofNat c.val).all Char.isDigit = true := by
    rw [all_abs_list _ hs]; exact hd
  have hn := isNat_digits (l := s.val.map fun c => Char.ofNat c.val) (by simpa using hne) hl
  simp only [String.toNat!, String.Slice.toNat!, absString, hn, ↓reduceIte,
    String.Slice.foldl_eq_foldl_toList, String.copy_toSlice, String.toList_ofList]
  exact foldl_digits _ hs hd 0

/-! ## `name_push_plain` -/

/-- No run of digits of the input is past the word. -/
def DigitsFit (s : alloc.vec.Vec Std.U32) : Prop :=
  ∀ l, l <:+: s.val → l ≠ [] → l.all isDigitW = true → digVal l < 2 ^ 64

theorem name_push_plain_str {n r : kernel.name.Name} {cur : alloc.vec.Vec Std.U32} {nums : Bool}
    (hn : NameWF n) (hc : StrWF cur) (hmk : kernel.name.mk_str n cur = ok r)
    (hif : ¬ (nums && !(absString cur).isEmpty && (absString cur).all Char.isDigit) = true) :
    absName r = ConLeche.Frontend.Olean.Name.pushPlain (absName n) (absString cur) nums ∧ NameWF r := by
  simp only [ConLeche.Frontend.Olean.Name.pushPlain, hif]
  exact ⟨mk_str_refines hmk, mk_str_wf hn hc hmk⟩

theorem absString_isEmpty (cur : alloc.vec.Vec Std.U32) :
    (absString cur).isEmpty = decide (cur.val = []) := by
  by_cases h : cur.val = []
  · simp [absString, h]
  · have : absString cur ≠ "" := by
      intro he
      have := congrArg String.toList he
      rw [absString_toList', String.toList_empty] at this
      exact h (List.map_eq_nil_iff.mp this)
    simp [h, this]

/-- **`name_push_plain` is `Name.pushPlain`**, the run of digits fitting. -/
theorem name_push_plain_eq {n r : kernel.name.Name} {cur : alloc.vec.Vec Std.U32} {nums : Bool}
    (hn : NameWF n) (hc : StrWF cur)
    (hfit : nums = true → cur.val ≠ [] → cur.val.all isDigitW = true → digVal cur.val < 2 ^ 64)
    (h : name_push_plain n cur nums = ok r) :
    absName r = ConLeche.Frontend.Olean.Name.pushPlain (absName n) (absString cur) nums ∧ NameWF r := by
  rw [name_push_plain] at h
  by_cases hnums : nums = true
  · rw [ite_eq_left hnums] at h
    subst hnums
    by_cases h0 : alloc.vec.Vec.len cur > 0#usize
    · rw [ite_eq_left h0] at h
      have hne : cur.val ≠ [] := by
        intro he
        have : (0#usize : Std.Usize).val < (alloc.vec.Vec.len cur).val := h0
        rw [vec_len_val, he] at this
        simp at this
      peel h as b, hb
      have eb := all_digits_eq hc hb
      by_cases hd : b = true
      · rw [ite_eq_left hd] at h
        peel h as v, hv
        have ev := digits_value_eq hv
        have hall : cur.val.all isDigitW = true := by rw [← all_abs hc, ← eb]; exact hd
        have hf := hfit rfl hne hall
        have hvv : v.val = (absString cur).toNat! := by
          rw [toNat!_digits hc hne hall, ev]; omega
        refine ⟨?_, mk_num_wf hn h⟩
        rw [mk_num_refines h, hvv]
        simp only [ConLeche.Frontend.Olean.Name.pushPlain, absString_isEmpty, hne, ← eb, hd]
        simp
      · rw [ite_eq_right hd] at h
        refine name_push_plain_str hn hc h ?_
        rw [← eb]; simp [hd]
    · rw [ite_eq_right h0] at h
      refine name_push_plain_str hn hc h ?_
      have he : cur.val = [] := by
        have : ¬ (0#usize : Std.Usize).val < (alloc.vec.Vec.len cur).val := h0
        rw [vec_len_val] at this
        apply List.eq_nil_of_length_eq_zero
        have l0 : (0#usize : Std.Usize).val = 0 := by decide
        omega
      simp [absString_isEmpty, he]
  · rw [ite_eq_right hnums] at h
    exact name_push_plain_str hn hc h (by simp [hnums])

/-! ## The scan -/

/-- Where the scan is, as upstream's. -/
def absScan : NameScan → ConLeche.Frontend.Olean.NameScan
  | .Start => .start
  | .Plain => .plain
  | .Esc => .esc
  | .Closed => .closed

/-- The input's characters. -/
abbrev chars (s : alloc.vec.Vec Std.U32) : List Char := s.val.map fun c => Char.ofNat c.val

/-- What a loop of the scan claims of the twin's answer `X`. -/
def ScanOut (nums : Bool) (s : alloc.vec.Vec Std.U32) (X : Option ConLeche.Name)
    (o : Option (kernel.name.Name × NameScan × alloc.vec.Vec Std.U32)) : Prop :=
  match o with
  | none => X = none
  | some (n', st', cur') =>
      X = scanName nums [] (absName n') (absScan st') (absString cur') ∧
      NameWF n' ∧ StrWF cur' ∧ cur'.val <:+: s.val

theorem suf_new {l : List Std.U32} (j : Nat) :
    ((alloc.vec.Vec.new Std.U32).val ++ l.drop j) <:+ l :=
  List.drop_suffix _ _

theorem suf_push {l : List Std.U32} {j : Nat} (hj : j < l.length) {pre w : List Std.U32}
    (h : (pre ++ l.drop j) <:+ l) (hw : w = pre ++ [l[j]]) : (w ++ l.drop (j + 1)) <:+ l := by
  rw [List.drop_eq_getElem_cons hj] at h
  rw [hw]
  simpa using h

theorem hfit_of_suf {nums : Bool} {s cur : alloc.vec.Vec Std.U32} {j : Nat}
    (hfit : nums = true → DigitsFit s) (h : (cur.val ++ s.val.drop j) <:+ s.val) :
    nums = true → cur.val ≠ [] → cur.val.all isDigitW = true → digVal cur.val < 2 ^ 64 :=
  fun hn => hfit hn _ ((List.prefix_append _ _).isInfix.trans h.isInfix)

/-- **The scan's loop against `scanName`.** -/
theorem scan_loop {nums : Bool} {s : alloc.vec.Vec Std.U32} (hs : StrWF s)
    (hfit : nums = true → DigitsFit s) (n : kernel.name.Name) (st : NameScan)
    (cur : alloc.vec.Vec Std.U32) (i : Std.Usize) (hn : NameWF n) (hc : StrWF cur)
    (hsuf : (cur.val ++ s.val.drop i.val) <:+ s.val) {o}
    (h : scan_name_go_loop nums s n st cur i = ok o) :
    ScanOut nums s (scanName nums ((chars s).drop i.val) (absName n) (absScan st) (absString cur)) o := by
  rw [scan_name_go_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len s
  · rw [ite_eq_left hlt] at h
    peel h as c, hc0
    obtain ⟨hi, rfl⟩ := vec_index_eq hc0
    have hv : Nat.isValidChar (s.val[i.val]).val := hs _ (List.getElem_mem hi)
    have hd : (chars s).drop i.val = Char.ofNat (s.val[i.val]).val :: (chars s).drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa [chars] using hi)]
      simp [chars]
    have e1 := char_beq (k := '«') (l := 171#u32) hv (by decide)
    have e2 := char_beq (k := '.') (l := 46#u32) hv (by decide)
    have e3 := char_beq (k := '»') (l := 187#u32) hv (by decide)
    rw [hd]
    cases st with
    | Start =>
      show ScanOut nums s (if (Char.ofNat (s.val[i.val]).val == '«') = true then _ else
        if (Char.ofNat (s.val[i.val]).val == '.') = true then none else _) o
      dsimp only at h
      rw [e1, e2]
      simp only [decide_eq_true_eq]
      by_cases c1 : s.val[i.val] = 171#u32
      · rw [ite_eq_left c1] at h ⊢
        peel h as i2, hi2
        have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
        have := scan_loop hs hfit n .Esc _ i2 hn str_wf_new' (by rw [hi2v]; exact suf_new _) h
        rw [hi2v, absString_new] at this
        exact this
      rw [ite_eq_right c1] at h ⊢
      by_cases c2 : s.val[i.val] = 46#u32
      · rw [ite_eq_left c2] at h ⊢
        cases Result.ok_injective h
        rfl
      rw [ite_eq_right c2] at h ⊢
      peel h as w, hw
      peel h as i2, hi2
      have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
      have hwv : w.val = (alloc.vec.Vec.new Std.U32).val ++ [s.val[i.val]] := vec_push_val hw
      have := scan_loop hs hfit n .Plain w i2 hn (str_wf_push str_wf_new' hv hw)
        (by rw [hi2v]; exact suf_push hi (suf_new _) hwv) h
      rw [hi2v, absString_push hw, absString_new] at this
      have e : ("" : String).push (Char.ofNat (s.val[i.val]).val) = String.singleton (Char.ofNat (s.val[i.val]).val) := rfl
      rw [e] at this
      exact this
    | Plain =>
      show ScanOut nums s (if (Char.ofNat (s.val[i.val]).val == '.') = true then _ else _) o
      dsimp only at h
      rw [e2]
      simp only [decide_eq_true_eq]
      by_cases c2 : s.val[i.val] = 46#u32
      · rw [ite_eq_left c2] at h ⊢
        peel h as t, ht
        peel ht as n2, hn2
        cases Result.ok_injective ht
        peel h as i2, hi2
        have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
        obtain ⟨hr, hw⟩ := name_push_plain_eq hn hc (hfit_of_suf hfit hsuf) hn2
        have := scan_loop hs hfit n2 .Start _ i2 hw str_wf_new' (by rw [hi2v]; exact suf_new _) h
        rw [hi2v, absString_new, hr] at this
        exact this
      · rw [ite_eq_right c2] at h ⊢
        peel h as t, ht
        peel ht as w, hw
        cases Result.ok_injective ht
        peel h as i2, hi2
        have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
        have hwv : w.val = cur.val ++ [s.val[i.val]] := vec_push_val hw
        have := scan_loop hs hfit n .Plain w i2 hn (str_wf_push hc hv hw)
          (by rw [hi2v]; exact suf_push hi hsuf hwv) h
        rw [hi2v, absString_push hw] at this
        exact this
    | Esc =>
      show ScanOut nums s (if (Char.ofNat (s.val[i.val]).val == '»') = true then
        (if (absString cur).isEmpty = true then none else _) else _) o
      dsimp only at h
      rw [e3, absString_isEmpty]
      simp only [decide_eq_true_eq]
      by_cases c3 : s.val[i.val] = 187#u32
      · rw [ite_eq_left c3] at h ⊢
        have hl : alloc.vec.Vec.len cur = 0#usize ↔ cur.val = [] := by
          constructor
          · intro he
            have := congrArg UScalar.val he
            rw [vec_len_val] at this
            exact List.eq_nil_of_length_eq_zero this
          · intro he
            apply UScalar.eq_of_val_eq
            rw [vec_len_val, he]; rfl
        by_cases c0 : cur.val = []
        · rw [ite_eq_left (hl.mpr c0)] at h
          rw [ite_eq_left c0]
          cases Result.ok_injective h
          rfl
        · rw [ite_eq_right (fun x => c0 (hl.mp x))] at h
          rw [ite_eq_right c0]
          peel h as n1, hn1
          peel h as i3, hi3
          have hi2v : i3.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi3]; rfl
          have := scan_loop hs hfit n1 .Closed _ i3 (mk_str_wf hn hc hn1) str_wf_new'
            (by rw [hi2v]; exact suf_new _) h
          rw [hi2v, absString_new, mk_str_refines hn1] at this
          exact this
      · rw [ite_eq_right c3] at h ⊢
        peel h as w, hw
        peel h as i2, hi2
        have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
        have hwv : w.val = cur.val ++ [s.val[i.val]] := vec_push_val hw
        have := scan_loop hs hfit n .Esc w i2 hn (str_wf_push hc hv hw)
          (by rw [hi2v]; exact suf_push hi hsuf hwv) h
        rw [hi2v, absString_push hw] at this
        exact this
    | Closed =>
      show ScanOut nums s (if (Char.ofNat (s.val[i.val]).val == '.') = true then _ else none) o
      dsimp only at h
      rw [e2]
      simp only [decide_eq_true_eq]
      by_cases c2 : s.val[i.val] = 46#u32
      · rw [ite_eq_left c2] at h ⊢
        peel h as i2, hi2
        have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
        have := scan_loop hs hfit n .Start _ i2 hn str_wf_new' (by rw [hi2v]; exact suf_new _) h
        rw [hi2v, absString_new] at this
        exact this
      · rw [ite_eq_right c2] at h ⊢
        cases Result.ok_injective h
        rfl
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hle : s.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len s).val := hlt
      rw [vec_len_val] at this; omega
    refine ⟨?_, hn, hc, ?_⟩
    · rw [List.drop_of_length_le (by simpa [chars] using hle)]
    · exact (List.prefix_append _ _).isInfix.trans hsuf.isInfix
termination_by s.val.length - i.val
decreasing_by all_goals omega

/-- **`scan_name_go` runs `scanName` up to its end.** -/
theorem scan_name_go_eq {nums : Bool} {s : alloc.vec.Vec Std.U32} (hs : StrWF s)
    (hfit : nums = true → DigitsFit s) {o} (h : scan_name_go nums s = ok o) :
    ScanOut nums s (scanName nums (chars s) .anonymous .start "") o := by
  rw [scan_name_go] at h
  peel h as n, hn
  have := scan_loop hs hfit n .Start _ _ (anonymous_wf hn) str_wf_new' (by simp) h
  rw [anonymous_refines hn, absString_new] at this
  simpa [absScan] using this

/-- What a parse claims: upstream's answer, and a stored name's well-formedness. -/
def ParseOut (X : Option ConLeche.Name) (o : Option kernel.name.Name) : Prop :=
  o.map absName = X ∧ ∀ r, o = some r → NameWF r

/-- **`scan_name` is `scanName`.** -/
theorem scan_name_eq {nums : Bool} {s : alloc.vec.Vec Std.U32} (hs : StrWF s)
    (hfit : nums = true → DigitsFit s) {o} (h : scan_name nums s = ok o) :
    ParseOut (scanName nums (chars s) .anonymous .start "") o := by
  rw [scan_name] at h
  peel h as g, hg
  have hS := scan_name_go_eq hs hfit hg
  cases g with
  | none =>
    cases Result.ok_injective h
    exact ⟨hS.symm, by simp⟩
  | some t =>
    obtain ⟨n, st, cur⟩ := t
    obtain ⟨hX, hn, hc, hsuf⟩ := hS
    rw [hX]
    cases st with
    | Start =>
      cases Result.ok_injective h
      exact ⟨rfl, by simp⟩
    | Plain =>
      dsimp only at h
      peel h as n1, hn1
      cases Result.ok_injective h
      obtain ⟨hr, hw⟩ := name_push_plain_eq hn hc
        (fun hnum => hfit hnum _ hsuf) hn1
      exact ⟨by simp only [Option.map_some, hr]; rfl, by rintro r ⟨rfl⟩; exact hw⟩
    | Esc =>
      cases Result.ok_injective h
      exact ⟨rfl, by simp⟩
    | Closed =>
      cases Result.ok_injective h
      exact ⟨rfl, by rintro r ⟨rfl⟩; exact hn⟩

/-- **`parse_mod_name` is `parseModName`.** -/
theorem parse_mod_name_eq {s : alloc.vec.Vec Std.U32} (hs : StrWF s) {o}
    (h : parse_mod_name s = ok o) : ParseOut (parseModName (absString s)) o := by
  rw [parse_mod_name] at h
  have := scan_name_eq hs (by simp) h
  rwa [parseModName, absString_toList']

/-- **`parse_const_name` is `parseConstName`**, no run of digits of the input past the word
(`digits_value` stops at `u64::MAX`, upstream's `toNat!` does not). -/
theorem parse_const_name_eq {s : alloc.vec.Vec Std.U32} (hs : StrWF s) (hfit : DigitsFit s) {o}
    (h : parse_const_name s = ok o) : ParseOut (parseConstName (absString s)) o := by
  rw [parse_const_name] at h
  have := scan_name_eq hs (fun _ => hfit) h
  rwa [parseConstName, absString_toList']

end ConRon.Refine2.Frontend.Olean
