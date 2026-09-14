/-
`ConRon.Refine.PinsDec` against `ConRon.Dump.parsePins` — half (B) of task
#64's decoder refinement, the tokenizer bridge.

`PinsDec` walks a byte suffix; `parsePins` splits the text into lines, each
line into space-separated tokens, and reads the tokens out of an array with a
cursor.  The bridge is the pair of invariants

* **lines**: the bytes left at a record boundary are the characters of the
  lines `runLines` has left, joined by `'\n'`;
* **fields**: inside a record, the bytes left are the characters of the tokens
  `st.toks.drop st.pos` holds, joined by `' '`.

Both are maintained by `Refine/PinsSplit.lean`'s two `splitOn` lemmas, and both
are *equalities*, not inequalities: the decoder is the stricter of the two
readers (single spaces, one newline per record, nothing after the footer), so
whenever it accepts, the reader sees exactly the tokens the decoder read.

`parsePins_of_decode` is this file's product and the whole of (B).
-/
import ConRon.Refine.PinsAscii
import ConRon.Refine.PinsSplit

namespace ConRon.Refine.PinsRead

open ConRon.Dump ConRon.Refine.PinsDec

/-- A byte string as the text it is the UTF-8 of, when it is ASCII. -/
def text (bs : Bytes) : String := String.ofList (bs.map Char.ofNat)

/-! ## Bytes as characters

Every byte the decoder accepts is ASCII, so `Char.ofNat` is injective on them
and the byte-level side conditions (`32 ∉ f`, `10 ∉ f`) become the character
side conditions `Refine/PinsSplit.lean`'s two lemmas ask for. -/

/-- `Char.ofNat` is a section of `Char.toNat` on the ASCII range. -/
theorem toNat_ofNat {n : Nat} (h : n < 128) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl (by omega)
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

/-- Distinct ASCII bytes are distinct characters. -/
theorem ofNat_ne {a b : Nat} (ha : a < 128) (hb : b < 128) (h : a ≠ b) :
    Char.ofNat a ≠ Char.ofNat b := by
  intro he
  exact h (by rw [← toNat_ofNat ha, ← toNat_ofNat hb, he])

theorem ofNat_space : Char.ofNat 32 = ' ' := by decide
theorem ofNat_newline : Char.ofNat 10 = '\n' := by decide

/-- The characters of a byte string. -/
abbrev chars (bs : Bytes) : List Char := bs.map Char.ofNat

theorem text_eq (bs : Bytes) : text bs = String.ofList (chars bs) := rfl

theorem toList_text (bs : Bytes) : (text bs).toList = chars bs := String.toList_ofList

/-- A byte that is not `32` is not the space character. -/
theorem not_mem_space {f : Bytes} (h32 : 32 ∉ f) (hasc : ∀ b ∈ f, b < 128) :
    ' ' ∉ chars f := by
  intro hm
  obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
  have hb32 : (Char.ofNat b).toNat = 32 := by rw [he]; decide
  rw [toNat_ofNat (hasc b hb)] at hb32
  exact h32 (hb32 ▸ hb)

/-- A byte that is not `10` is not the newline character. -/
theorem not_mem_newline {f : Bytes} (h10 : 10 ∉ f) (hasc : ∀ b ∈ f, b < 128) :
    '\n' ∉ chars f := by
  intro hm
  obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
  have hb10 : (Char.ofNat b).toNat = 10 := by rw [he]; decide
  rw [toNat_ofNat (hasc b hb)] at hb10
  exact h10 (hb10 ▸ hb)

/-! ### The two token equations, on bytes -/

/-- A field with no space in it is one token. -/
theorem splitOn_field {f : Bytes} (h32 : 32 ∉ f) (hasc : ∀ b ∈ f, b < 128) :
    (text f).splitOn " " = [text f] := by
  rw [PinsSplit.space_eq, text_eq]
  exact PinsSplit.splitOn_of_not_mem (not_mem_space h32 hasc)

/-- A field, a space, and a rest: the field, then the rest's own tokens. -/
theorem splitOn_field_cons {f l : Bytes} (h32 : 32 ∉ f)
    (hasc : ∀ b ∈ f, b < 128) :
    (text (f ++ 32 :: l)).splitOn " " = text f :: (text l).splitOn " " := by
  have : chars (f ++ 32 :: l) = chars f ++ ' ' :: chars l := by
    simp [chars]
  rw [PinsSplit.space_eq, text_eq, this]
  exact PinsSplit.splitOn_append_cons (not_mem_space h32 hasc)

/-- A line, a newline, and a rest. -/
theorem splitOn_line_cons {l r : Bytes} (h10 : 10 ∉ l)
    (hasc : ∀ b ∈ l, b < 128) :
    (text (l ++ 10 :: r)).splitOn "\n" = text l :: (text r).splitOn "\n" := by
  have : chars (l ++ 10 :: r) = chars l ++ '\n' :: chars r := by
    simp [chars]
  rw [PinsSplit.newline_eq, text_eq, this]
  exact PinsSplit.splitOn_append_cons (not_mem_newline h10 hasc)

/-! ## Splitting a byte list at its first separator -/

/-- Two decompositions of the same byte string at a newline agree. -/
theorem newline_inj : ∀ {a b r s : Bytes}, 10 ∉ a → 10 ∉ b →
    a ++ 10 :: r = b ++ 10 :: s → a = b ∧ r = s
  | [], [], _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, _, hb, h => by
      simp at h; exact absurd (h.1 ▸ List.mem_cons_self ..) hb
  | _ :: _, [], _, _, ha, _, h => by
      simp at h; exact absurd (h.1 ▸ List.mem_cons_self ..) ha
  | x :: a, y :: b, r, s, ha, hb, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := newline_inj (fun m => ha (List.mem_cons_of_mem _ m))
        (fun m => hb (List.mem_cons_of_mem _ m)) h
      exact ⟨rfl, rfl⟩

/-- A field ending at a space sits inside the line it started in. -/
theorem split_at_space {l f r s : Bytes} (hf : 10 ∉ f)
    (h : l ++ 10 :: r = f ++ 32 :: s) :
    ∃ l₂, l = f ++ 32 :: l₂ ∧ s = l₂ ++ 10 :: r := by
  rcases List.append_eq_append_iff.mp h with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
  · -- `f = l ++ c`, `10 :: r = c ++ 32 :: s`
    match c, hc2 with
    | [], hc2 => simp at hc2
    | c₀ :: c, hc2 =>
      simp only [List.cons_append, List.cons.injEq] at hc2
      exact absurd (hc1 ▸ List.mem_append_right _ (hc2.1 ▸ List.mem_cons_self ..)) hf
  · -- `l = f ++ c`, `32 :: s = c ++ 10 :: r`
    match c, hc2 with
    | [], hc2 => simp at hc2
    | c₀ :: c, hc2 =>
      simp only [List.cons_append, List.cons.injEq] at hc2
      exact ⟨c, by rw [hc1, hc2.1], hc2.2⟩

/-! ## The reader's state, against the decoder's -/

/-- The reader's arrays are the decoder's tables. -/
structure Match (st : RState) (tb : Tables) : Prop where
  names : st.names.toList = tb.names
  levels : st.levels.toList = tb.levels
  pws : st.pws.toList = tb.pws
  exprs : st.exprs.toList = tb.exprs
  sets : st.pinSets.toList = tb.sets

/-- The decoder is at the start of a field of the current line, and the
reader's cursor is on the same field.  `bs` is the decoder's byte suffix and
`rest` what follows the line's newline — `none` when the line has no newline
at all, which is the shape the *last* line of an unterminated text has and
which no record can be read from. -/
def AtField (st : RState) (bs : Bytes) (rest : Option Bytes) : Prop :=
  ∃ l, (match rest with | some r => bs = l ++ 10 :: r | none => bs = l) ∧
    10 ∉ l ∧ (∀ b ∈ l, b < 128) ∧
    st.toks.toList.drop st.pos = (text l).splitOn " "

/-- The decoder is *on* a separator: either the line's newline, and then the
reader has consumed the whole line, or a space, and then another field
follows. -/
def AtSep (st : RState) (bs : Bytes) (rest : Option Bytes) : Prop :=
  (∃ r, rest = some r ∧ bs = 10 :: r ∧ st.pos = st.toks.size) ∨
    (∃ bs', bs = 32 :: bs' ∧ AtField st bs' rest)

theorem atSep_space {st : RState} {bs bs' : Bytes} {rest : Option Bytes}
    (h : AtSep st bs rest) (hs : afterSpace bs = some bs') :
    AtField st bs' rest := by
  rcases h with ⟨r, -, rfl, -⟩ | ⟨c, rfl, hc⟩
  · simp [afterSpace] at hs
  · simp [afterSpace] at hs; exact hs ▸ hc

theorem atSep_newline {st : RState} {bs bs' : Bytes} {rest : Option Bytes}
    (h : AtSep st bs rest) (hs : afterNewline bs = some bs') :
    rest = some bs' ∧ st.pos = st.toks.size := by
  rcases h with ⟨r, hr, rfl, hd⟩ | ⟨c, rfl, -⟩
  · simp [afterNewline] at hs; exact ⟨by rw [hr, hs], hd⟩
  · simp [afterNewline] at hs

/-! ## One field -/

theorem nextTok_eq {st : RState} {t : String} (h : st.toks[st.pos]? = some t) :
    nextTok st = .ok (t, { st with pos := st.pos + 1 }) := by
  have hlt : st.pos < st.toks.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at h
    simp at h
  have ht : st.toks[st.pos]'hlt = t := by
    rw [Array.getElem?_eq_getElem hlt] at h; exact Option.some.inj h
  simp only [nextTok, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, MonadStateOf.set, pure, StateT.pure, Except.bind, Except.pure,
    hlt, dif_pos, ht]

/-- **The field step.**  A byte reader that consumed the field `f` and stopped
on a separator leaves the reader's cursor on the token `text f`, one step
before the separator's own position. -/
theorem field_step {st : RState} {bs f bs' : Bytes} {rest : Option Bytes}
    (hat : AtField st bs rest) (hcons : bs = f ++ bs')
    (h32 : 32 ∉ f) (h10 : 10 ∉ f)
    (hsep : byteAt bs' = 32 ∨ byteAt bs' = 10) :
    st.toks[st.pos]? = some (text f) ∧
      AtSep { st with pos := st.pos + 1 } bs' rest := by
  obtain ⟨l, hl, hl10, hlasc, htoks⟩ := hat
  /- The field is a prefix of the line, whatever the line's shape. -/
  have key : ∀ {s : Bytes}, l = f ++ 32 :: s →
      st.toks[st.pos]? = some (text f) ∧
        { st with pos := st.pos + 1 }.toks.toList.drop (st.pos + 1)
          = (text s).splitOn " " ∧ 10 ∉ s ∧ (∀ b ∈ s, b < 128) := by
    intro s hl2a
    have hfasc : ∀ b ∈ f, b < 128 := fun b hb =>
      hlasc b (hl2a ▸ List.mem_append_left _ hb)
    have h2asc : ∀ b ∈ s, b < 128 := fun b hb =>
      hlasc b (hl2a ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hb))
    have h210 : 10 ∉ s := fun hb =>
      hl10 (hl2a ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hb))
    rw [hl2a, splitOn_field_cons h32 hfasc] at htoks
    refine ⟨?_, ?_, h210, h2asc⟩
    · rw [← Array.getElem?_toList, ← List.head?_drop, htoks]; rfl
    · simp only [← List.tail_drop, htoks, List.tail_cons]
  match rest, hl with
  | none, hl =>
    -- the line runs to the end of the text: only a space can follow a field
    match bs', hsep with
    | [], hsep => simp [byteAt] at hsep
    | c :: s, hsep =>
      simp only [byteAt] at hsep
      have heq : l = f ++ c :: s := by rw [← hl, hcons]
      rcases hsep with rfl | rfl
      · obtain ⟨h1, h2, h3, h4⟩ := key heq
        exact ⟨h1, Or.inr ⟨s, rfl, ⟨s, rfl, h3, h4, h2⟩⟩⟩
      · exact absurd (heq ▸ List.mem_append_right _ (List.mem_cons_self ..)) hl10
  | some r, hl =>
    have heq : l ++ 10 :: r = f ++ bs' := by rw [← hl, hcons]
    match bs', hsep with
    | [], hsep => simp [byteAt] at hsep
    | c :: s, hsep =>
      simp only [byteAt] at hsep
      rcases hsep with rfl | rfl
      · -- a space: another field follows on the same line
        obtain ⟨l₂, hl2a, hl2b⟩ := split_at_space h10 heq
        obtain ⟨h1, h2, h3, h4⟩ := key hl2a
        exact ⟨h1, Or.inr ⟨s, rfl, ⟨l₂, hl2b, h3, h4, h2⟩⟩⟩
      · -- the newline: the field was the line's last
        obtain ⟨rfl, rfl⟩ := newline_inj hl10 h10 heq
        rw [splitOn_field h32 hlasc] at htoks
        refine ⟨?_, Or.inl ⟨_, rfl, rfl, ?_⟩⟩
        · rw [← Array.getElem?_toList, ← List.head?_drop, htoks]; rfl
        · have hlen := congrArg List.length htoks
          simp only [List.length_drop, List.length_cons, List.length_nil,
            Array.length_toList] at hlen
          have hlt : st.pos < st.toks.size := by
            by_contra hc
            rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hc)] at htoks
            simp at htoks
          simp only; omega

/-- The reader's cursor is the only thing a field reader moves. -/
theorem Match.pos {st : RState} {tb : Tables} (h : Match st tb) (k : Nat) :
    Match { st with pos := k } tb :=
  ⟨h.names, h.levels, h.pws, h.exprs, h.sets⟩

/-- `nextTok` on a field the byte reader consumed. -/
theorem tok_step {st : RState} {bs f bs' : Bytes} {rest : Option Bytes}
    (hat : AtField st bs rest) (hcons : bs = f ++ bs')
    (h32 : 32 ∉ f) (h10 : 10 ∉ f)
    (hsep : byteAt bs' = 32 ∨ byteAt bs' = 10) :
    nextTok st = .ok (text f, { st with pos := st.pos + 1 }) ∧
      AtSep { st with pos := st.pos + 1 } bs' rest :=
  ⟨nextTok_eq (field_step hat hcons h32 h10 hsep).1,
   (field_step hat hcons h32 h10 hsep).2⟩

/-! ## The scalar readers -/

/-- The value of a digit run — `Nat.ofDigitChars`' loop, on bytes. -/
def digitsVal (acc : Nat) (f : Bytes) : Nat :=
  f.foldl (fun a b => 10 * a + (b - 48)) acc

theorem digitsVal_cons (acc : Nat) (b : Nat) (f : Bytes) :
    digitsVal acc (b :: f) = digitsVal (10 * acc + (b - 48)) f := by
  simp only [digitsVal, List.foldl_cons]

theorem digit_lt {b : Nat} (h : isDigit b = true) : 48 ≤ b ∧ b ≤ 57 := by
  simp [isDigit] at h; omega

theorem digits_asc {f : Bytes} (h : ∀ b ∈ f, isDigit b = true) :
    ∀ b ∈ f, b < 128 := fun b hb => by have := digit_lt (h b hb); omega

theorem digits_ne_space {f : Bytes} (h : ∀ b ∈ f, isDigit b = true) : 32 ∉ f :=
  fun hb => by have := digit_lt (h 32 hb); omega

theorem digits_ne_newline {f : Bytes} (h : ∀ b ∈ f, isDigit b = true) : 10 ∉ f :=
  fun hb => by have := digit_lt (h 10 hb); omega

/-- An ASCII digit byte is a digit character. -/
theorem isDigit_ofNat {b : Nat} (h : isDigit b = true) :
    (Char.ofNat b).isDigit = true := by
  obtain ⟨h1, h2⟩ := digit_lt h
  have hb : (Char.ofNat b).toNat = b := toNat_ofNat (by omega)
  have h0 : ('0' : Char).toNat = 48 := by decide
  have h9 : ('9' : Char).toNat = 57 := by decide
  rw [Char.isDigit_iff_toNat, hb, h0, h9]
  omega

/-- `Nat.ofDigitChars` on the characters of a digit run is `digitsVal`. -/
theorem ofDigitChars_chars : ∀ {f : Bytes} (acc : Nat), (∀ b ∈ f, b < 128) →
    Nat.ofDigitChars 10 (chars f) acc = digitsVal acc f
  | [], _, _ => rfl
  | b :: f, acc, h => by
    have hb : (Char.ofNat b).toNat = b := toNat_ofNat (h b (List.mem_cons_self ..))
    simp only [chars, List.map_cons, Nat.ofDigitChars, List.foldl_cons] at *
    rw [hb, show ('0' : Char).toNat = 48 from rfl,
      show (List.foldl (fun sofar c => 10 * sofar + (c.toNat - 48)) (10 * acc + (b - 48))
        (List.map Char.ofNat f))
          = Nat.ofDigitChars 10 (chars f) (10 * acc + (b - 48)) from rfl,
      ofDigitChars_chars _ (fun c hc => h c (List.mem_cons_of_mem _ hc)),
      digitsVal_cons]

/-- `String.toNat?` agrees with `digitsVal` on a nonempty digit run. -/
theorem toNat?_digits {f : Bytes} (hne : f ≠ []) (hd : ∀ b ∈ f, isDigit b = true) :
    (text f).toNat? = some (digitsVal 0 f) := by
  have hasc := digits_asc hd
  have hlist : (text f).toList = chars f := String.toList_ofList
  have hdig : ∀ c ∈ (text f).toList, c.isDigit = true := by
    rw [hlist]; intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact isDigit_ofNat (hd b hb)
  have hnonempty : text f ≠ "" := by
    rw [text_eq, Ne, String.ofList_eq_empty_iff]
    simpa [chars] using hne
  have hnat := String.toNat?_eq_some_ofDigitChars
    (String.isNat_of_isDigit hnonempty hdig)
  rw [hnat, hlist, List.filter_eq_self.mpr (by
    intro c hc
    have := hdig c (hlist ▸ hc)
    simp only [bne_iff_ne, ne_eq]
    rintro rfl
    simp at this), ofDigitChars_chars 0 hasc]

/-! ### What the byte readers consume -/

theorem readNatFrom_spec : ∀ {bs : Bytes} {acc n : Nat} {rest : Bytes},
    readNatFrom bs acc = some (n, rest) →
    ∃ f, bs = f ++ rest ∧ (∀ b ∈ f, isDigit b = true) ∧
      (byteAt rest = 32 ∨ byteAt rest = 10) ∧ n = digitsVal acc f
  | [], _, _, _, h => by simp [readNatFrom] at h
  | b :: bs, acc, n, rest, h => by
    rw [readNatFrom] at h
    by_cases hb : isDigit b = true
    · rw [if_pos hb] at h
      by_cases hg : acc > 1000000000000000000
      · rw [if_pos hg] at h; simp at h
      · rw [if_neg hg] at h
        obtain ⟨f, hf, hfd, hsep, hval⟩ := readNatFrom_spec h
        refine ⟨b :: f, by rw [hf]; rfl, ?_, hsep, ?_⟩
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hb
          · exact hfd c hc
        · rw [digitsVal_cons, Nat.mul_comm 10 acc]; exact hval
    · rw [if_neg hb] at h
      by_cases hs : b = 32 ∨ b = 10
      · rw [if_pos (by rcases hs with rfl | rfl <;> simp)] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rfl, by simp, by simpa [byteAt] using hs, rfl⟩
      · rw [if_neg (by simpa using hs)] at h; simp at h

theorem readBigNatFrom_spec : ∀ {bs : Bytes} {acc n : Nat} {rest : Bytes},
    readBigNatFrom bs acc = some (n, rest) →
    ∃ f, bs = f ++ rest ∧ (∀ b ∈ f, isDigit b = true) ∧
      (byteAt rest = 32 ∨ byteAt rest = 10) ∧ n = digitsVal acc f
  | [], _, _, _, h => by simp [readBigNatFrom] at h
  | b :: bs, acc, n, rest, h => by
    rw [readBigNatFrom] at h
    by_cases hb : isDigit b = true
    · rw [if_pos hb] at h
      obtain ⟨f, hf, hfd, hsep, hval⟩ := readBigNatFrom_spec h
      refine ⟨b :: f, by rw [hf]; rfl, ?_, hsep, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hb
        · exact hfd c hc
      · rw [digitsVal_cons, Nat.mul_comm 10 acc]; exact hval
    · rw [if_neg hb] at h
      by_cases hs : b = 32 ∨ b = 10
      · rw [if_pos (by rcases hs with rfl | rfl <;> simp)] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rfl, by simp, by simpa [byteAt] using hs, rfl⟩
      · rw [if_neg (by simpa using hs)] at h; simp at h

/-- A digit field: nonempty, all digits, ending on a separator. -/
def DigitField (bs : Bytes) (n : Nat) (rest : Bytes) : Prop :=
  ∃ f, bs = f ++ rest ∧ f ≠ [] ∧ (∀ b ∈ f, isDigit b = true) ∧
    (byteAt rest = 32 ∨ byteAt rest = 10) ∧ (text f).toNat? = some n

theorem readNat_spec {bs : Bytes} {n : Nat} {rest : Bytes}
    (h : readNat bs = some (n, rest)) : DigitField bs n rest := by
  rw [readNat] at h
  by_cases hd : isDigit (byteAt bs) = true
  · rw [if_pos hd] at h
    obtain ⟨f, hf, hfd, hsep, hval⟩ := readNatFrom_spec h
    have hne : f ≠ [] := by
      rintro rfl
      rw [List.nil_append] at hf
      subst hf
      rcases hsep with hs | hs <;> rw [hs] at hd <;> simp [isDigit] at hd
    exact ⟨f, hf, hne, hfd, hsep, by rw [toNat?_digits hne hfd, hval]⟩
  · rw [if_neg hd] at h; simp at h

theorem readIndex_spec {bs : Bytes} {n : Nat} {rest : Bytes}
    (h : readIndex bs = some (n, rest)) : DigitField bs n rest :=
  readNat_spec h

theorem readBigNat_spec {bs : Bytes} {n : Nat} {rest : Bytes}
    (h : readBigNat bs = some (n, rest)) : DigitField bs n rest := by
  rw [readBigNat] at h
  by_cases hd : isDigit (byteAt bs) = true
  · rw [if_pos hd] at h
    obtain ⟨f, hf, hfd, hsep, hval⟩ := readBigNatFrom_spec h
    have hne : f ≠ [] := by
      rintro rfl
      rw [List.nil_append] at hf
      subst hf
      rcases hsep with hs | hs <;> rw [hs] at hd <;> simp [isDigit] at hd
    exact ⟨f, hf, hne, hfd, hsep, by rw [toNat?_digits hne hfd, hval]⟩
  · rw [if_neg hd] at h; simp at h

/-- **One field's worth of reading.**  The reader action `p` returns what the
byte reader returned, moves only its cursor, and lands on the separator the
byte reader stopped at. -/
def Step {α : Type} (p : R α) (st : RState) (a : α) (bs' : Bytes)
    (rest : Option Bytes) : Prop :=
  ∃ k, p st = .ok (a, { st with pos := k }) ∧ AtSep { st with pos := k } bs' rest

/-- `natTok` reads a digit field. -/
theorem natTok_step {st : RState} {bs : Bytes} {rest : Option Bytes} {n : Nat}
    {bs' : Bytes}
    (hat : AtField st bs rest) (h : DigitField bs n bs') :
    Step natTok st n bs' rest := by
  obtain ⟨f, hf, -, hfd, hsep, hval⟩ := h
  obtain ⟨h1, h2⟩ := tok_step hat hf (digits_ne_space hfd) (digits_ne_newline hfd) hsep
  refine ⟨st.pos + 1, ?_, h2⟩
  simp only [natTok, bind, StateT.bind, Except.bind, h1, hval, pure, StateT.pure,
    Except.pure]

/-! ## Strings (FORMAT.md §3's escape) -/

theorem decString_eq (l : List Nat) : decString l = text l := rfl

theorem decString_nil : decString [] = "" := by
  simp [decString]

theorem decString_cons (b : Nat) (l : List Nat) :
    decString (b :: l) = String.singleton (Char.ofNat b) ++ decString l := by
  simp only [decString, List.map_cons, String.ofList_cons]

theorem length_decString (l : List Nat) : (decString l).length = l.length := by
  simp [decString]

theorem beq_ofNat {b n : Nat} (hb : b < 128) (hn : n < 128) :
    (Char.ofNat b == Char.ofNat n) = (b == n) := by
  by_cases h : b = n
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr (ofNat_ne hb hn h), beq_eq_false_iff_ne.mpr h]

theorem beq_semicolon {b : Nat} (hb : b < 128) :
    (Char.ofNat b == ';') = (b == 59) := by
  rw [show (';' : Char) = Char.ofNat 59 from by decide, beq_ofNat hb (by omega)]

theorem beq_backslash {b : Nat} (hb : b < 128) :
    (Char.ofNat b == '\\') = (b == 92) := by
  rw [show ('\\' : Char) = Char.ofNat 92 from by decide, beq_ofNat hb (by omega)]

theorem hexDigit_lt {b : Nat} (h : hexDigit b ≠ 16) :
    (48 ≤ b ∧ b ≤ 57) ∨ (97 ≤ b ∧ b ≤ 102) := by
  by_cases h1 : 48 ≤ b ∧ b ≤ 57
  · exact Or.inl h1
  · by_cases h2 : 97 ≤ b ∧ b ≤ 102
    · exact Or.inr h2
    · exact absurd (show hexDigit b = 16 by simp [hexDigit, h1, h2]) h

theorem hexDigit?_eq {b : Nat} (h : hexDigit b ≠ 16) :
    hexDigit? (Char.ofNat b) = some (hexDigit b) := by
  have hr := hexDigit_lt h
  have hb : (Char.ofNat b).toNat = b := toNat_ofNat (by omega)
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : (decide (48 ≤ b) && decide (b ≤ 57)) = true := by simp; omega
    simp [hexDigit?, hexDigit, hb, e1]
  · have e1 : (decide (48 ≤ b) && decide (b ≤ 57)) = false := by simp; omega
    have e2 : (decide (97 ≤ b) && decide (b ≤ 102)) = true := by simp; omega
    simp [hexDigit?, hexDigit, hb, e1, e2]

theorem isValidChar_eq {v : Nat} (h : PinsDec.isValidChar v = true) :
    Nat.isValidChar v := by
  simp only [PinsDec.isValidChar] at h
  split at h
  · exact Or.inl (by omega)
  · simp at h; exact Or.inr ⟨by omega, by omega⟩

/-- **What `unescape_from` consumed, and what `unescapeGo` makes of it.** -/
theorem unescapeFrom_spec : ∀ {bs : Bytes} {v : Nat} {inEsc : Bool}
    {out s : List Nat} {rest : Bytes},
    unescapeFrom bs v inEsc out = some (s, rest) →
    ∃ f s', bs = f ++ rest ∧ (∀ b ∈ f, 33 ≤ b ∧ b ≤ 126) ∧
      (byteAt rest = 32 ∨ byteAt rest = 10) ∧ s = out ++ s' ∧
      ∀ acc : String, unescapeGo (chars f) v inEsc acc = .ok (acc ++ decString s')
  | [], _, _, _, _, _, h => by simp [unescapeFrom] at h
  | b :: r, v, inEsc, out, s, rest, h => by
    rw [unescapeFrom] at h
    by_cases hsep : b = 32 ∨ b = 10
    · rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)] at h
      cases inEsc with
      | true => simp at h
      | false =>
        simp only [Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], [], rfl, by simp, by simpa [byteAt] using hsep, by simp,
          fun acc => by simp [chars, unescapeGo, decString_nil]⟩
    · rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)] at h
      cases inEsc with
      | true =>
        rw [if_pos rfl] at h
        by_cases h59 : b = 59
        · subst h59
          rw [if_pos rfl] at h
          by_cases hv : PinsDec.isValidChar v = true
          · rw [if_pos hv] at h
            obtain ⟨f, s', hf, hfr, hsp, hs, hgo⟩ := unescapeFrom_spec h
            refine ⟨59 :: f, v :: s', by rw [hf]; rfl, ?_, hsp, by simp [hs], ?_⟩
            · intro c hc
              rcases List.mem_cons.mp hc with rfl | hc
              · omega
              · exact hfr c hc
            · intro acc
              rw [show chars (59 :: f) = ';' :: chars f from by simp [chars]]
              rw [unescapeGo, if_pos rfl, if_pos (by simp), if_pos (isValidChar_eq hv),
                String.push_eq_append, hgo, decString_cons, String.append_assoc]
          · rw [if_neg hv] at h; simp at h
        · rw [if_neg h59] at h
          by_cases hd : hexDigit b = 16 ∨ v > 1114111
          · rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)] at h
            simp at h
          · rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)] at h
            simp only [not_or, Nat.not_lt] at hd
            have hrange := hexDigit_lt hd.1
            obtain ⟨f, s', hf, hfr, hsp, hs, hgo⟩ := unescapeFrom_spec h
            refine ⟨b :: f, s', by rw [hf]; rfl, ?_, hsp, hs, ?_⟩
            · intro c hc
              rcases List.mem_cons.mp hc with rfl | hc
              · omega
              · exact hfr c hc
            · intro acc
              rw [show chars (b :: f) = Char.ofNat b :: chars f from rfl]
              rw [unescapeGo, if_pos rfl, if_neg (by
                rw [beq_semicolon (by omega)]; simpa using h59), hexDigit?_eq hd.1]
              exact hgo acc
      | false =>
        rw [if_neg (by simp)] at h
        by_cases h92 : b = 92
        · subst h92
          rw [if_pos rfl] at h
          obtain ⟨f, s', hf, hfr, hsp, hs, hgo⟩ := unescapeFrom_spec h
          refine ⟨92 :: f, s', by rw [hf]; rfl, ?_, hsp, hs, ?_⟩
          · intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · omega
            · exact hfr c hc
          · intro acc
            rw [show chars (92 :: f) = '\\' :: chars f from by simp [chars]]
            rw [unescapeGo, if_neg (by simp), if_pos (by simp), hgo]
        · rw [if_neg h92] at h
          by_cases hr : b < 33 ∨ b > 126
          · rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)] at h
            simp at h
          · rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)] at h
            simp only [not_or, Nat.not_lt] at hr
            obtain ⟨f, s', hf, hfr, hsp, hs, hgo⟩ := unescapeFrom_spec h
            refine ⟨b :: f, b :: s', by rw [hf]; rfl, ?_, hsp, by simp [hs], ?_⟩
            · intro c hc
              rcases List.mem_cons.mp hc with rfl | hc
              · omega
              · exact hfr c hc
            · intro acc
              rw [show chars (b :: f) = Char.ofNat b :: chars f from rfl]
              rw [unescapeGo, if_neg (by simp), if_neg (by
                rw [beq_backslash (by omega)]; simpa using h92),
                String.push_eq_append, hgo, decString_cons, String.append_assoc]

theorem set_pos_set_pos (st : RState) (k k' : Nat) :
    ({ { st with pos := k } with pos := k' } : RState) = { st with pos := k' } := rfl

/-- `strTok` reads the count field and the escaped text field. -/
theorem strTok_step {st : RState} {bs : Bytes} {rest : Option Bytes}
    {s : List Nat} {bs' : Bytes}
    (hat : AtField st bs rest) (h : readString bs = some (s, bs')) :
    Step strTok st (decString s) bs' rest := by
  rw [readString] at h
  split at h
  · simp at h
  · rename_i n r hri
    split at h
    · simp at h
    · rename_i r₂ hsp
      split at h
      · simp at h
      · rename_i s₀ r₃ hun
        split at h
        · rename_i hlen
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨k₁, hnat, hsep₁⟩ := natTok_step hat (readIndex_spec hri)
          have hat₂ := atSep_space hsep₁ hsp
          obtain ⟨f, s', hf, hfr, hsp₂, hs, hgo⟩ := unescapeFrom_spec hun
          have h32 : 32 ∉ f := fun hb => by have := hfr 32 hb; omega
          have h10 : 10 ∉ f := fun hb => by have := hfr 10 hb; omega
          obtain ⟨htok, hsep₂⟩ := tok_step hat₂ hf h32 h10 hsp₂
          rw [List.nil_append] at hs
          refine ⟨k₁ + 1, ?_, by rw [set_pos_set_pos] at hsep₂; exact hsep₂⟩
          rw [set_pos_set_pos] at htok
          have hgo' : unescapeGo (text f).toList 0 false "" = .ok (decString s₀) := by
            rw [toList_text, hgo, hs]; simp
          simp only [strTok, bind, StateT.bind, Except.bind, hnat, htok, hgo',
            length_decString, hlen, beq_self_eq_true, if_true, pure, StateT.pure,
            Except.pure]
        · simp at h

/-! ## Backward references -/

theorem getElem_of_toList {α : Type} {arr : Array α} {l : List α} {i : Nat} {a : α}
    (hl : arr.toList = l) (h : l[i]? = some a) : ∃ hi : i < arr.size, arr[i]'hi = a := by
  have harr : arr[i]? = some a := by rw [← Array.getElem?_toList, hl]; exact h
  have hi : i < arr.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at harr
    simp at harr
  exact ⟨hi, by rw [Array.getElem?_eq_getElem hi] at harr; exact Option.some.inj harr⟩

theorem nameRef_step {st : RState} {tb : Tables} {bs : Bytes}
    {rest : Option Bytes} {n : ConLeche.Name} {bs' : Bytes} (hm : Match st tb)
    (hat : AtField st bs rest)
    (h : PinsDec.nameRef bs tb = some (n, bs')) :
    Step ConRon.Dump.nameRef st n bs' rest := by
  rw [PinsDec.nameRef] at h
  cases hri : readIndex bs with
  | none => simp [hri] at h
  | some p =>
    obtain ⟨k, r⟩ := p
    cases hidx : tb.names[k]? with
    | none => simp [hri, hidx] at h
    | some m =>
      simp only [hri, hidx, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨k₁, hnat, hsep⟩ := natTok_step hat (readIndex_spec hri)
      obtain ⟨hi, hv⟩ := getElem_of_toList hm.names hidx
      refine ⟨k₁, ?_, hsep⟩
      simp only [ConRon.Dump.nameRef, bind, StateT.bind, Except.bind, hnat, get,
        getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
        dif_pos hi, hv]

theorem levelRef_step {st : RState} {tb : Tables} {bs : Bytes}
    {rest : Option Bytes} {u : ConLeche.Level} {bs' : Bytes} (hm : Match st tb)
    (hat : AtField st bs rest)
    (h : PinsDec.levelRef bs tb = some (u, bs')) :
    Step ConRon.Dump.levelRef st u bs' rest := by
  rw [PinsDec.levelRef] at h
  cases hri : readIndex bs with
  | none => simp [hri] at h
  | some p =>
    obtain ⟨k, r⟩ := p
    cases hidx : tb.levels[k]? with
    | none => simp [hri, hidx] at h
    | some m =>
      simp only [hri, hidx, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨k₁, hnat, hsep⟩ := natTok_step hat (readIndex_spec hri)
      obtain ⟨hi, hv⟩ := getElem_of_toList hm.levels hidx
      refine ⟨k₁, ?_, hsep⟩
      simp only [ConRon.Dump.levelRef, bind, StateT.bind, Except.bind, hnat, get,
        getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
        dif_pos hi, hv]

theorem pwRef_step {st : RState} {tb : Tables} {bs : Bytes}
    {rest : Option Bytes} {w : ConLeche.PropWhen} {bs' : Bytes}
    (hm : Match st tb) (hat : AtField st bs rest)
    (h : PinsDec.pwRef bs tb = some (w, bs')) :
    Step ConRon.Dump.pwRef st w bs' rest := by
  rw [PinsDec.pwRef] at h
  cases hri : readIndex bs with
  | none => simp [hri] at h
  | some p =>
    obtain ⟨k, r⟩ := p
    cases hidx : tb.pws[k]? with
    | none => simp [hri, hidx] at h
    | some m =>
      simp only [hri, hidx, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨k₁, hnat, hsep⟩ := natTok_step hat (readIndex_spec hri)
      obtain ⟨hi, hv⟩ := getElem_of_toList hm.pws hidx
      refine ⟨k₁, ?_, hsep⟩
      simp only [ConRon.Dump.pwRef, bind, StateT.bind, Except.bind, hnat, get,
        getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
        dif_pos hi, hv]

theorem exprRef_step {st : RState} {tb : Tables} {bs : Bytes}
    {rest : Option Bytes} {e : ConLeche.Expr} {bs' : Bytes} (hm : Match st tb)
    (hat : AtField st bs rest)
    (h : PinsDec.exprRef bs tb = some (e, bs')) :
    Step ConRon.Dump.exprRef st e bs' rest := by
  rw [PinsDec.exprRef] at h
  cases hri : readIndex bs with
  | none => simp [hri] at h
  | some p =>
    obtain ⟨k, r⟩ := p
    cases hidx : tb.exprs[k]? with
    | none => simp [hri, hidx] at h
    | some m =>
      simp only [hri, hidx, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨k₁, hnat, hsep⟩ := natTok_step hat (readIndex_spec hri)
      obtain ⟨hi, hv⟩ := getElem_of_toList hm.exprs hidx
      refine ⟨k₁, ?_, hsep⟩
      simp only [ConRon.Dump.exprRef, bind, StateT.bind, Except.bind, hnat, get,
        getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
        dif_pos hi, hv]

theorem expectId_step {st : RState} {bs : Bytes} {rest : Option Bytes}
    {want : Nat} {what : String} {bs' : Bytes} (hat : AtField st bs rest)
    (h : PinsDec.expectId bs want = some bs') :
    Step (ConRon.Dump.expectId want what) st () bs' rest := by
  rw [PinsDec.expectId] at h
  cases hri : readIndex bs with
  | none => simp [hri] at h
  | some p =>
    obtain ⟨got, r⟩ := p
    by_cases hw : got = want
    · subst hw
      simp only [hri, if_true, Option.some.injEq] at h
      subst h
      obtain ⟨k₁, hnat, hsep⟩ := natTok_step hat (readIndex_spec hri)
      refine ⟨k₁, ?_, hsep⟩
      simp only [ConRon.Dump.expectId, bind, StateT.bind, Except.bind, hnat,
        beq_self_eq_true, if_true, pure, StateT.pure, Except.pure]
    · simp [hri, hw] at h

/-! ## Counted lists -/

/-- `p` reads the field `d` reads: the contract a list element has to meet. -/
def Reads {α : Type} (p : R α) (d : Bytes → Tables → Option (α × Bytes)) : Prop :=
  ∀ {st : RState} {tb : Tables} {bs : Bytes} {rest : Option Bytes} {a : α}
    {bs' : Bytes}, Match st tb → AtField st bs rest → d bs tb = some (a, bs') →
    Step p st a bs' rest

theorem reads_nameRef : Reads ConRon.Dump.nameRef PinsDec.nameRef :=
  fun hm hat h => nameRef_step hm hat h

theorem reads_levelRef : Reads ConRon.Dump.levelRef PinsDec.levelRef :=
  fun hm hat h => levelRef_step hm hat h

theorem reads_exprRef : Reads ConRon.Dump.exprRef PinsDec.exprRef :=
  fun hm hat h => exprRef_step hm hat h

/-- The shape all five of `PinsDec`'s counted lists share. -/
def listFrom {α : Type} (d : Bytes → Tables → Option (α × Bytes)) (bs : Bytes)
    (tb : Tables) : Nat → List α → Option (List α × Bytes)
  | 0, out => some (out, bs)
  | k + 1, out =>
    match afterSpace bs with
    | none => none
    | some r => match d r tb with
      | none => none
      | some (a, r) => listFrom d r tb k (out ++ [a])

/-- A counted list: the count field, then that many elements. -/
def listOf {α : Type} (d : Bytes → Tables → Option (α × Bytes)) (bs : Bytes)
    (tb : Tables) : Option (List α × Bytes) :=
  match readIndex bs with
  | none => none
  | some (n, r) => listFrom d r tb n []

theorem nameListFrom_eq (tb : Tables) : ∀ (k : Nat) (bs : Bytes)
    (out : List ConLeche.Name),
    nameListFrom bs tb k out = listFrom PinsDec.nameRef bs tb k out
  | 0, _, _ => rfl
  | k + 1, bs, out => by
    rw [nameListFrom, listFrom]
    cases hs : afterSpace bs with
    | none => simp
    | some r =>
      simp only []
      cases hn : PinsDec.nameRef r tb with
      | none => simp
      | some q =>
        obtain ⟨a, r'⟩ := q
        simp only []
        exact nameListFrom_eq tb k r' (out ++ [a])

theorem levelListFrom_eq (tb : Tables) : ∀ (k : Nat) (bs : Bytes)
    (out : List ConLeche.Level),
    levelListFrom bs tb k out = listFrom PinsDec.levelRef bs tb k out
  | 0, _, _ => rfl
  | k + 1, bs, out => by
    rw [levelListFrom, listFrom]
    cases hs : afterSpace bs with
    | none => simp
    | some r =>
      simp only []
      cases hn : PinsDec.levelRef r tb with
      | none => simp
      | some q =>
        obtain ⟨a, r'⟩ := q
        simp only []
        exact levelListFrom_eq tb k r' (out ++ [a])

theorem exprListFrom_eq (tb : Tables) : ∀ (k : Nat) (bs : Bytes)
    (out : List ConLeche.Expr),
    exprListFrom bs tb k out = listFrom PinsDec.exprRef bs tb k out
  | 0, _, _ => rfl
  | k + 1, bs, out => by
    rw [exprListFrom, listFrom]
    cases hs : afterSpace bs with
    | none => simp
    | some r =>
      simp only []
      cases hn : PinsDec.exprRef r tb with
      | none => simp
      | some q =>
        obtain ⟨a, r'⟩ := q
        simp only []
        exact exprListFrom_eq tb k r' (out ++ [a])

theorem pinsEightFrom_eq (tb : Tables) : ∀ (k : Nat) (bs : Bytes)
    (out : List ConLeche.Expr),
    pinsEightFrom bs tb k out = listFrom PinsDec.exprRef bs tb k out
  | 0, _, _ => rfl
  | k + 1, bs, out => by
    rw [pinsEightFrom, listFrom]
    cases hs : afterSpace bs with
    | none => simp
    | some r =>
      simp only []
      cases hn : PinsDec.exprRef r tb with
      | none => simp
      | some q =>
        obtain ⟨a, r'⟩ := q
        simp only []
        exact pinsEightFrom_eq tb k r' (out ++ [a])

theorem proofsEightFrom_eq (tb : Tables) : ∀ (k : Nat) (bs : Bytes)
    (out : List (List ConLeche.Expr)),
    proofsEightFrom bs tb k out = listFrom exprList bs tb k out
  | 0, _, _ => rfl
  | k + 1, bs, out => by
    rw [proofsEightFrom, listFrom]
    cases hs : afterSpace bs with
    | none => simp
    | some r =>
      simp only []
      cases hn : exprList r tb with
      | none => simp
      | some q =>
        obtain ⟨a, r'⟩ := q
        simp only []
        exact proofsEightFrom_eq tb k r' (out ++ [a])

theorem nameList_eq (bs : Bytes) (tb : Tables) :
    nameList bs tb = listOf PinsDec.nameRef bs tb := by
  rw [nameList, listOf]
  cases hri : readIndex bs with
  | none => simp
  | some q =>
    obtain ⟨n, r⟩ := q
    simp only []
    exact nameListFrom_eq tb n r []

theorem levelList_eq (bs : Bytes) (tb : Tables) :
    levelList bs tb = listOf PinsDec.levelRef bs tb := by
  rw [levelList, listOf]
  cases hri : readIndex bs with
  | none => simp
  | some q =>
    obtain ⟨n, r⟩ := q
    simp only []
    exact levelListFrom_eq tb n r []

theorem exprList_eq (bs : Bytes) (tb : Tables) :
    exprList bs tb = listOf PinsDec.exprRef bs tb := by
  rw [exprList, listOf]
  cases hri : readIndex bs with
  | none => simp
  | some q =>
    obtain ⟨n, r⟩ := q
    simp only []
    exact exprListFrom_eq tb n r []

/-- `listTok`'s inner loop against `listFrom`. -/
theorem listTok_go_step {α : Type} {p : R α}
    {d : Bytes → Tables → Option (α × Bytes)} (hp : Reads p d) :
    ∀ (k : Nat) {st : RState} {tb : Tables} {bs : Bytes} {rest : Option Bytes}
      {acc : Array α} {res : List α} {bs' : Bytes}, Match st tb → AtSep st bs rest →
      listFrom d bs tb k acc.toList = some (res, bs') →
      ∃ j arr, listTok.go p k acc st = .ok (arr, { st with pos := j }) ∧
        arr.toList = res ∧ AtSep { st with pos := j } bs' rest
  | 0, st, _, bs, rest, acc, res, bs', _, hsep, h => by
    simp only [listFrom, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨st.pos, acc, rfl, rfl, hsep⟩
  | k + 1, st, tb, bs, rest, acc, res, bs', hm, hsep, h => by
    rw [listFrom] at h
    cases hspace : afterSpace bs with
    | none => simp [hspace] at h
    | some r =>
      cases hd : d r tb with
      | none => simp [hspace, hd] at h
      | some q =>
        obtain ⟨a, r₂⟩ := q
        simp only [hspace, hd] at h
        obtain ⟨j₁, hpst, hsep₁⟩ := hp hm (atSep_space hsep hspace) hd
        obtain ⟨j₂, arr, hgo, harr, hsep₂⟩ :=
          listTok_go_step hp k (acc := acc.push a) (hm.pos j₁) hsep₁
            (by rw [Array.toList_push]; exact h)
        rw [set_pos_set_pos] at hgo hsep₂
        refine ⟨j₂, arr, ?_, harr, hsep₂⟩
        rw [listTok.go.eq_2]
        simp only [bind, StateT.bind, Except.bind, hpst, hgo]

/-- `listTok p` reads the counted list `listOf d`. -/
theorem listTok_step {α : Type} {p : R α}
    {d : Bytes → Tables → Option (α × Bytes)} (hp : Reads p d)
    {st : RState} {tb : Tables} {bs : Bytes} {rest : Option Bytes} {res : List α}
    {bs' : Bytes} (hm : Match st tb) (hat : AtField st bs rest)
    (h : listOf d bs tb = some (res, bs')) : Step (listTok p) st res bs' rest := by
  rw [listOf] at h
  cases hri : readIndex bs with
  | none => simp [hri] at h
  | some q =>
    obtain ⟨n, r⟩ := q
    simp only [hri] at h
    obtain ⟨k₁, hnat, hsep⟩ := natTok_step hat (readIndex_spec hri)
    obtain ⟨j, arr, hgo, harr, hsep₂⟩ :=
      listTok_go_step hp n (acc := #[]) (hm.pos k₁) hsep (by simpa using h)
    rw [set_pos_set_pos] at hgo hsep₂
    refine ⟨j, ?_, hsep₂⟩
    simp only [listTok, bind, StateT.bind, Except.bind, hnat, hgo, harr, pure,
      StateT.pure, Except.pure]

/-! ## The records -/

theorem byteAt_afterSpace {r r' : Bytes} (h : afterSpace r = some r') :
    byteAt r = 32 := by
  unfold afterSpace at h
  split at h
  · rfl
  · simp at h

theorem byteAt_afterNewline {r r' : Bytes} (h : afterNewline r = some r') :
    byteAt r = 10 := by
  unfold afterNewline at h
  split at h
  · rfl
  · simp at h

/-- A record's one-letter kind field. -/
theorem letter_step {st : RState} {bs : Bytes} {rest : Option Bytes} {k : Nat}
    {r : Bytes}
    (hsep : AtSep st bs rest) (hs : afterSpace bs = some (k :: r))
    (hk : 33 ≤ k ∧ k ≤ 126) (hnext : byteAt r = 32 ∨ byteAt r = 10) :
    Step nextTok st (text [k]) r rest := by
  obtain ⟨h1, h2⟩ := tok_step (atSep_space hsep hs) (f := [k]) (bs' := r) rfl
    (by simp; omega) (by simp; omega) hnext
  exact ⟨st.pos + 1, h1, h2⟩

theorem match_push_names {st : RState} {tb : Tables} (hm : Match st tb)
    (v : ConLeche.Name) (k : Nat) :
    Match { st with pos := k, names := st.names.push v }
      { tb with names := tb.names ++ [v] } :=
  ⟨by simp [hm.names], hm.levels, hm.pws, hm.exprs, hm.sets⟩

theorem match_push_levels {st : RState} {tb : Tables} (hm : Match st tb)
    (v : ConLeche.Level) (k : Nat) :
    Match { st with pos := k, levels := st.levels.push v }
      { tb with levels := tb.levels ++ [v] } :=
  ⟨hm.names, by simp [hm.levels], hm.pws, hm.exprs, hm.sets⟩

theorem match_push_pws {st : RState} {tb : Tables} (hm : Match st tb)
    (v : ConLeche.PropWhen) (k : Nat) :
    Match { st with pos := k, pws := st.pws.push v }
      { tb with pws := tb.pws ++ [v] } :=
  ⟨hm.names, hm.levels, by simp [hm.pws], hm.exprs, hm.sets⟩

theorem match_push_exprs {st : RState} {tb : Tables} (hm : Match st tb)
    (v : ConLeche.Expr) (k : Nat) :
    Match { st with pos := k, exprs := st.exprs.push v }
      { tb with exprs := tb.exprs ++ [v] } :=
  ⟨hm.names, hm.levels, hm.pws, by simp [hm.exprs], hm.sets⟩

theorem match_push_sets {st : RState} {tb : Tables} (hm : Match st tb)
    (v : ConLeche.NatOpPinSet) (k : Nat) :
    Match { st with pos := k, pinSets := st.pinSets.push v }
      { tb with sets := tb.sets ++ [v] } :=
  ⟨hm.names, hm.levels, hm.pws, hm.exprs, by simp [hm.sets]⟩

set_option linter.unusedSimpArgs false

/-! `reader_simp` is the `StateT RState (Except String)` plumbing, the kind
dispatch's string comparisons and the boolean reductions every record proof
unfolds; its arguments are the record's own field equations. -/

open Lean.Parser.Tactic in
syntax "reader_simp" "[" simpLemma,* "]" : tactic

open Lean.Parser.Tactic in
macro_rules
  | `(tactic| reader_simp [$ts,*]) =>
    `(tactic| simp only [parseRecord, ite_apply, bind, StateT.bind, Except.bind, get,
        getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, modify,
        modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, String.reduceBEq,
        Bool.false_and, Bool.and_false, Bool.and_true, Bool.true_and, if_true,
        if_false, Bool.false_eq_true, reduceIte,
        ConLeche.Expr.mkBvar_eq, ConLeche.Expr.mkFVar_eq,
        ConLeche.Expr.mkSort_eq, ConLeche.Expr.mkConst_eq,
        ConLeche.Expr.mkApp_eq, ConLeche.Expr.mkLam_eq,
        ConLeche.Expr.mkForallE_eq, ConLeche.Expr.mkLetE_eq,
        ConLeche.Expr.mkLit_eq, ConLeche.Expr.mkProj_eq,
        $ts,*])

/-- **A record.**  `parseRecord` reads the record `recordStep` read, ending
exactly at the end of its line. -/
def RecordOk (p : R Unit) (st : RState) (tb' : Tables) : Prop :=
  ∃ st', p st = .ok ((), st') ∧ Match st' tb' ∧ st'.pos = st'.toks.size

theorem recordName_step {st : RState} {tb tb' : Tables} {bs bs' : Bytes}
    {rest : Option Bytes} (hm : Match st tb) (hat : AtField st bs rest)
    (h : recordName bs tb = some (tb', bs')) :
    rest = some bs' ∧ RecordOk (parseRecord "N") st tb' := by
  have hsize : st.names.size = tb.names.length := by rw [← hm.names]; simp
  rw [recordName] at h
  cases hexp : PinsDec.expectId bs tb.names.length with
  | none => simp [hexp] at h
  | some r =>
    simp only [hexp] at h
    obtain ⟨k₁, e₁, s₁⟩ := expectId_step (what := "name") hat hexp
    rw [← hsize] at e₁
    cases hsp : afterSpace r with
    | none => simp [hsp] at h
    | some r₂ =>
      simp only [hsp] at h
      cases r₂ with
      | nil => simp only [] at h; simp at h
      | cons kk r₃ =>
        simp only [] at h
        by_cases h97 : kk = 97
        · subst h97
          rw [if_pos rfl] at h
          cases hnl : afterNewline r₃ with
          | none => simp [hnl] at h
          | some r₄ =>
            simp only [hnl, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
              (Or.inr (byteAt_afterNewline hnl))
            rw [set_pos_set_pos] at e₂ s₂
            obtain ⟨hbs, hdone⟩ := atSep_newline s₂ hnl
            refine ⟨hbs, _, ?_, match_push_names hm _ k₂, hdone⟩
            reader_simp [e₁, e₂, show text [97] = "a" from by decide]
        · rw [if_neg h97] at h
          by_cases h115 : kk = 115
          · subst h115
            rw [if_pos rfl, recordNameStr] at h
            cases hsp2 : afterSpace r₃ with
            | none => simp [hsp2] at h
            | some r₄ =>
              simp only [hsp2] at h
              cases hnr : PinsDec.nameRef r₄ tb with
              | none => simp [hnr] at h
              | some q =>
                obtain ⟨pre, r₅⟩ := q
                simp only [hnr] at h
                cases hsp3 : afterSpace r₅ with
                | none => simp [hsp3] at h
                | some r₆ =>
                  simp only [hsp3] at h
                  cases hrs : readString r₆ with
                  | none => simp [hrs] at h
                  | some q₂ =>
                    obtain ⟨sv, r₇⟩ := q₂
                    simp only [hrs] at h
                    cases hnl : afterNewline r₇ with
                    | none => simp [hnl] at h
                    | some r₈ =>
                      simp only [hnl, Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                        (Or.inl (byteAt_afterSpace hsp2))
                      rw [set_pos_set_pos] at e₂ s₂
                      obtain ⟨k₃, e₃, s₃⟩ :=
                        nameRef_step (hm.pos k₂) (atSep_space s₂ hsp2) hnr
                      rw [set_pos_set_pos] at e₃ s₃
                      obtain ⟨k₄, e₄, s₄⟩ :=
                        strTok_step (atSep_space s₃ hsp3) hrs
                      rw [set_pos_set_pos] at e₄ s₄
                      obtain ⟨hbs, hdone⟩ := atSep_newline s₄ hnl
                      refine ⟨hbs, _, ?_, match_push_names hm _ k₄, hdone⟩
                      reader_simp [e₁, e₂, e₃, e₄,
                        show text [115] = "s" from by decide]
          · rw [if_neg h115] at h
            by_cases h110 : kk = 110
            · subst h110
              rw [if_pos rfl, recordNameNum] at h
              cases hsp2 : afterSpace r₃ with
              | none => simp [hsp2] at h
              | some r₄ =>
                simp only [hsp2] at h
                cases hnr : PinsDec.nameRef r₄ tb with
                | none => simp [hnr] at h
                | some q =>
                  obtain ⟨pre, r₅⟩ := q
                  simp only [hnr] at h
                  cases hsp3 : afterSpace r₅ with
                  | none => simp [hsp3] at h
                  | some r₆ =>
                    simp only [hsp3] at h
                    cases hrn : readNat r₆ with
                    | none => simp [hrn] at h
                    | some q₂ =>
                      obtain ⟨nv, r₇⟩ := q₂
                      simp only [hrn] at h
                      cases hnl : afterNewline r₇ with
                      | none => simp [hnl] at h
                      | some r₈ =>
                        simp only [hnl, Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                          (Or.inl (byteAt_afterSpace hsp2))
                        rw [set_pos_set_pos] at e₂ s₂
                        obtain ⟨k₃, e₃, s₃⟩ :=
                          nameRef_step (hm.pos k₂) (atSep_space s₂ hsp2) hnr
                        rw [set_pos_set_pos] at e₃ s₃
                        obtain ⟨k₄, e₄, s₄⟩ :=
                          natTok_step (atSep_space s₃ hsp3) (readNat_spec hrn)
                        rw [set_pos_set_pos] at e₄ s₄
                        obtain ⟨hbs, hdone⟩ := atSep_newline s₄ hnl
                        refine ⟨hbs, _, ?_, match_push_names hm _ k₄, hdone⟩
                        reader_simp [e₁, e₂, e₃, e₄,
                          show text [110] = "n" from by decide]
            · rw [if_neg h110] at h; simp at h

theorem recordLevel_step {st : RState} {tb tb' : Tables} {bs bs' : Bytes}
    {rest : Option Bytes} (hm : Match st tb) (hat : AtField st bs rest)
    (h : recordLevel bs tb = some (tb', bs')) :
    rest = some bs' ∧ RecordOk (parseRecord "L") st tb' := by
  have hsize : st.levels.size = tb.levels.length := by rw [← hm.levels]; simp
  rw [recordLevel] at h
  cases hexp : PinsDec.expectId bs tb.levels.length with
  | none => simp [hexp] at h
  | some r =>
    simp only [hexp] at h
    obtain ⟨k₁, e₁, s₁⟩ := expectId_step (what := "level") hat hexp
    rw [← hsize] at e₁
    cases hsp : afterSpace r with
    | none => simp [hsp] at h
    | some r₂ =>
      simp only [hsp] at h
      cases r₂ with
      | nil => simp only [] at h; simp at h
      | cons kk r₃ =>
        simp only [] at h
        by_cases h122 : kk = 122
        · subst h122
          rw [if_pos rfl] at h
          split at h
          · simp at h
          · rename_i r₄ hnl
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
              (Or.inr (byteAt_afterNewline hnl))
            rw [set_pos_set_pos] at e₂ s₂
            obtain ⟨hbs, hdone⟩ := atSep_newline s₂ hnl
            refine ⟨hbs, _, ?_, match_push_levels hm _ k₂, hdone⟩
            reader_simp [e₁, e₂, show text [122] = "z" from by decide]
        · rw [if_neg h122] at h
          by_cases h115 : kk = 115
          · subst h115
            rw [if_pos rfl, recordLevelSucc] at h
            split at h
            · simp at h
            · rename_i r₄ hsp2
              split at h
              · simp at h
              · rename_i u r₅ hlr
                split at h
                · simp at h
                · rename_i r₆ hnl
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                    (Or.inl (byteAt_afterSpace hsp2))
                  rw [set_pos_set_pos] at e₂ s₂
                  obtain ⟨k₃, e₃, s₃⟩ :=
                    levelRef_step (hm.pos k₂) (atSep_space s₂ hsp2) hlr
                  rw [set_pos_set_pos] at e₃ s₃
                  obtain ⟨hbs, hdone⟩ := atSep_newline s₃ hnl
                  refine ⟨hbs, _, ?_, match_push_levels hm _ k₃, hdone⟩
                  reader_simp [e₁, e₂, e₃, show text [115] = "s" from by decide]
          · rw [if_neg h115] at h
            by_cases hmi : kk = 109 ∨ kk = 105
            · rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega),
                recordLevelBinop] at h
              split at h
              · simp at h
              · rename_i r₄ hsp2
                split at h
                · simp at h
                · rename_i u r₅ hlr
                  split at h
                  · simp at h
                  · rename_i r₆ hsp3
                    split at h
                    · simp at h
                    · rename_i v r₇ hlr2
                      split at h
                      · simp at h
                      · rename_i r₈ hnl
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                          (Or.inl (byteAt_afterSpace hsp2))
                        rw [set_pos_set_pos] at e₂ s₂
                        obtain ⟨k₃, e₃, s₃⟩ :=
                          levelRef_step (hm.pos k₂) (atSep_space s₂ hsp2) hlr
                        rw [set_pos_set_pos] at e₃ s₃
                        obtain ⟨k₄, e₄, s₄⟩ :=
                          levelRef_step (hm.pos k₃) (atSep_space s₃ hsp3) hlr2
                        rw [set_pos_set_pos] at e₄ s₄
                        obtain ⟨hbs, hdone⟩ := atSep_newline s₄ hnl
                        refine ⟨hbs, _, ?_, match_push_levels hm _ k₄, hdone⟩
                        rcases hmi with rfl | rfl
                        · reader_simp [e₁, e₂, e₃, e₄, decide_true,
                            show text [109] = "m" from by decide]
                        · reader_simp [e₁, e₂, e₃, e₄,
                            show (decide ((105 : Nat) = 109)) = false from by decide,
                            show text [105] = "i" from by decide]
            · rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)] at h
              by_cases h112 : kk = 112
              · subst h112
                rw [if_pos rfl, recordLevelParam] at h
                split at h
                · simp at h
                · rename_i r₄ hsp2
                  split at h
                  · simp at h
                  · rename_i n r₅ hnr
                    split at h
                    · simp at h
                    · rename_i r₆ hnl
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                        (Or.inl (byteAt_afterSpace hsp2))
                      rw [set_pos_set_pos] at e₂ s₂
                      obtain ⟨k₃, e₃, s₃⟩ :=
                        nameRef_step (hm.pos k₂) (atSep_space s₂ hsp2) hnr
                      rw [set_pos_set_pos] at e₃ s₃
                      obtain ⟨hbs, hdone⟩ := atSep_newline s₃ hnl
                      refine ⟨hbs, _, ?_, match_push_levels hm _ k₃, hdone⟩
                      reader_simp [e₁, e₂, e₃, show text [112] = "p" from by decide]
              · rw [if_neg h112] at h; simp at h

theorem recordPw_step {st : RState} {tb tb' : Tables} {bs bs' : Bytes}
    {rest : Option Bytes} (hm : Match st tb) (hat : AtField st bs rest)
    (h : recordPw bs tb = some (tb', bs')) :
    rest = some bs' ∧ RecordOk (parseRecord "W") st tb' := by
  have hsize : st.pws.size = tb.pws.length := by rw [← hm.pws]; simp
  rw [recordPw] at h
  cases hexp : PinsDec.expectId bs tb.pws.length with
  | none => simp [hexp] at h
  | some r =>
    simp only [hexp] at h
    obtain ⟨k₁, e₁, s₁⟩ := expectId_step (what := "propwhen") hat hexp
    rw [← hsize] at e₁
    cases hsp : afterSpace r with
    | none => simp [hsp] at h
    | some r₂ =>
      simp only [hsp] at h
      cases r₂ with
      | nil => simp only [] at h; simp at h
      | cons kk r₃ =>
        simp only [] at h
        by_cases h110 : kk = 110
        · subst h110
          rw [if_pos rfl] at h
          split at h
          · simp at h
          · rename_i r₄ hnl
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
              (Or.inr (byteAt_afterNewline hnl))
            rw [set_pos_set_pos] at e₂ s₂
            obtain ⟨hbs, hdone⟩ := atSep_newline s₂ hnl
            refine ⟨hbs, _, ?_, match_push_pws hm _ k₂, hdone⟩
            reader_simp [e₁, e₂, show text [110] = "n" from by decide]
        · rw [if_neg h110] at h
          by_cases h122 : kk = 122
          · subst h122
            rw [if_pos rfl, recordPwZero] at h
            split at h
            · simp at h
            · rename_i r₄ hsp2
              split at h
              · simp at h
              · rename_i ps r₅ hnl2
                split at h
                · simp at h
                · rename_i r₆ hnl
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                    (Or.inl (byteAt_afterSpace hsp2))
                  rw [set_pos_set_pos] at e₂ s₂
                  rw [nameList_eq] at hnl2
                  obtain ⟨k₃, e₃, s₃⟩ :=
                    listTok_step reads_nameRef (hm.pos k₂) (atSep_space s₂ hsp2) hnl2
                  rw [set_pos_set_pos] at e₃ s₃
                  obtain ⟨hbs, hdone⟩ := atSep_newline s₃ hnl
                  refine ⟨hbs, _, ?_, match_push_pws hm _ k₃, hdone⟩
                  reader_simp [e₁, e₂, e₃, show text [122] = "z" from by decide]
          · rw [if_neg h122] at h; simp at h

theorem recordExpr_step {st : RState} {tb tb' : Tables} {bs bs' : Bytes}
    {rest : Option Bytes} (hm : Match st tb) (hat : AtField st bs rest)
    (h : recordExpr bs tb = some (tb', bs')) :
    rest = some bs' ∧ RecordOk (parseRecord "E") st tb' := by
  have hsize : st.exprs.size = tb.exprs.length := by rw [← hm.exprs]; simp
  rw [recordExpr] at h
  cases hexp : PinsDec.expectId bs tb.exprs.length with
  | none => simp [hexp] at h
  | some r =>
    simp only [hexp] at h
    obtain ⟨k₁, e₁, s₁⟩ := expectId_step (what := "expr") hat hexp
    rw [← hsize] at e₁
    cases hsp : afterSpace r with
    | none => simp [hsp] at h
    | some r₂ =>
      simp only [hsp] at h
      cases r₂ with
      | nil => simp only [] at h; simp at h
      | cons kk r₃ =>
        simp only [] at h
        -- `b`: a bound variable
        by_cases h98 : kk = 98
        · subst h98
          rw [if_pos rfl, recordExprBvar] at h
          split at h
          · simp at h
          · rename_i r₄ hsp2
            split at h
            · simp at h
            · rename_i nv r₅ hrn
              split at h
              · simp at h
              · rename_i r₆ hnl
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                  (Or.inl (byteAt_afterSpace hsp2))
                rw [set_pos_set_pos] at e₂ s₂
                obtain ⟨k₃, e₃, s₃⟩ :=
                  natTok_step (atSep_space s₂ hsp2) (readNat_spec hrn)
                rw [set_pos_set_pos] at e₃ s₃
                obtain ⟨hbs, hdone⟩ := atSep_newline s₃ hnl
                refine ⟨hbs, _, ?_, match_push_exprs hm _ k₃, hdone⟩
                reader_simp [e₁, e₂, e₃, show text [98] = "b" from by decide]
        rw [if_neg h98] at h
        -- `v`: a free variable
        by_cases h118 : kk = 118
        · subst h118
          rw [if_pos rfl, recordExprFvar] at h
          split at h
          · simp at h
          · rename_i r₄ hsp2
            split at h
            · simp at h
            · rename_i iv r₅ hrn
              split at h
              · simp at h
              · rename_i r₆ hsp3
                split at h
                · simp at h
                · rename_i ty r₇ her
                  split at h
                  · simp at h
                  · rename_i r₈ hnl
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                      (Or.inl (byteAt_afterSpace hsp2))
                    rw [set_pos_set_pos] at e₂ s₂
                    obtain ⟨k₃, e₃, s₃⟩ :=
                      natTok_step (atSep_space s₂ hsp2) (readNat_spec hrn)
                    rw [set_pos_set_pos] at e₃ s₃
                    obtain ⟨k₄, e₄, s₄⟩ :=
                      exprRef_step (hm.pos k₃) (atSep_space s₃ hsp3) her
                    rw [set_pos_set_pos] at e₄ s₄
                    obtain ⟨hbs, hdone⟩ := atSep_newline s₄ hnl
                    refine ⟨hbs, _, ?_, match_push_exprs hm _ k₄, hdone⟩
                    reader_simp [e₁, e₂, e₃, e₄,
                      show text [118] = "v" from by decide]
        rw [if_neg h118] at h
        -- `s`: a sort
        by_cases h115 : kk = 115
        · subst h115
          rw [if_pos rfl, recordExprSort] at h
          split at h
          · simp at h
          · rename_i r₄ hsp2
            split at h
            · simp at h
            · rename_i u r₅ hlr
              split at h
              · simp at h
              · rename_i r₆ hnl
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                  (Or.inl (byteAt_afterSpace hsp2))
                rw [set_pos_set_pos] at e₂ s₂
                obtain ⟨k₃, e₃, s₃⟩ :=
                  levelRef_step (hm.pos k₂) (atSep_space s₂ hsp2) hlr
                rw [set_pos_set_pos] at e₃ s₃
                obtain ⟨hbs, hdone⟩ := atSep_newline s₃ hnl
                refine ⟨hbs, _, ?_, match_push_exprs hm _ k₃, hdone⟩
                reader_simp [e₁, e₂, e₃, show text [115] = "s" from by decide]
        rw [if_neg h115] at h
        -- `c`: a constant
        by_cases h99 : kk = 99
        · subst h99
          rw [if_pos rfl, recordExprConst] at h
          split at h
          · simp at h
          · rename_i r₄ hsp2
            split at h
            · simp at h
            · rename_i nn r₅ hnr
              split at h
              · simp at h
              · rename_i r₆ hsp3
                split at h
                · simp at h
                · rename_i us r₇ hll
                  split at h
                  · simp at h
                  · rename_i r₈ hnl
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                      (Or.inl (byteAt_afterSpace hsp2))
                    rw [set_pos_set_pos] at e₂ s₂
                    obtain ⟨k₃, e₃, s₃⟩ :=
                      nameRef_step (hm.pos k₂) (atSep_space s₂ hsp2) hnr
                    rw [set_pos_set_pos] at e₃ s₃
                    rw [levelList_eq] at hll
                    obtain ⟨k₄, e₄, s₄⟩ :=
                      listTok_step reads_levelRef (hm.pos k₃) (atSep_space s₃ hsp3) hll
                    rw [set_pos_set_pos] at e₄ s₄
                    obtain ⟨hbs, hdone⟩ := atSep_newline s₄ hnl
                    refine ⟨hbs, _, ?_, match_push_exprs hm _ k₄, hdone⟩
                    reader_simp [e₁, e₂, e₃, e₄,
                      show text [99] = "c" from by decide]
        rw [if_neg h99] at h
        -- `a`: an application
        by_cases h97 : kk = 97
        · subst h97
          rw [if_pos rfl, recordExprApp] at h
          split at h
          · simp at h
          · rename_i r₄ hsp2
            split at h
            · simp at h
            · rename_i fn r₅ her
              split at h
              · simp at h
              · rename_i r₆ hsp3
                split at h
                · simp at h
                · rename_i ag r₇ her2
                  split at h
                  · simp at h
                  · rename_i r₈ hnl
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                      (Or.inl (byteAt_afterSpace hsp2))
                    rw [set_pos_set_pos] at e₂ s₂
                    obtain ⟨k₃, e₃, s₃⟩ :=
                      exprRef_step (hm.pos k₂) (atSep_space s₂ hsp2) her
                    rw [set_pos_set_pos] at e₃ s₃
                    obtain ⟨k₄, e₄, s₄⟩ :=
                      exprRef_step (hm.pos k₃) (atSep_space s₃ hsp3) her2
                    rw [set_pos_set_pos] at e₄ s₄
                    obtain ⟨hbs, hdone⟩ := atSep_newline s₄ hnl
                    refine ⟨hbs, _, ?_, match_push_exprs hm _ k₄, hdone⟩
                    reader_simp [e₁, e₂, e₃, e₄,
                      show text [97] = "a" from by decide]
        rw [if_neg h97] at h
        -- `l` and `f`: the two binders
        by_cases hlf : kk = 108 ∨ kk = 102
        · rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega),
            recordExprBinder] at h
          split at h
          · simp at h
          · rename_i r₄ hsp2
            split at h
            · simp at h
            · rename_i ty r₅ her
              split at h
              · simp at h
              · rename_i r₆ hsp3
                split at h
                · simp at h
                · rename_i bd r₇ her2
                  split at h
                  · simp at h
                  · rename_i r₈ hsp4
                    split at h
                    · simp at h
                    · rename_i pw r₉ hpr
                      split at h
                      · simp at h
                      · rename_i r₁₀ hnl
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                          (Or.inl (byteAt_afterSpace hsp2))
                        rw [set_pos_set_pos] at e₂ s₂
                        obtain ⟨k₃, e₃, s₃⟩ :=
                          exprRef_step (hm.pos k₂) (atSep_space s₂ hsp2) her
                        rw [set_pos_set_pos] at e₃ s₃
                        obtain ⟨k₄, e₄, s₄⟩ :=
                          exprRef_step (hm.pos k₃) (atSep_space s₃ hsp3) her2
                        rw [set_pos_set_pos] at e₄ s₄
                        obtain ⟨k₅, e₅, s₅⟩ :=
                          pwRef_step (hm.pos k₄) (atSep_space s₄ hsp4) hpr
                        rw [set_pos_set_pos] at e₅ s₅
                        obtain ⟨hbs, hdone⟩ := atSep_newline s₅ hnl
                        refine ⟨hbs, _, ?_, match_push_exprs hm _ k₅, hdone⟩
                        rcases hlf with rfl | rfl
                        · reader_simp [e₁, e₂, e₃, e₄, e₅, decide_true,
                            show text [108] = "l" from by decide]
                        · reader_simp [e₁, e₂, e₃, e₄, e₅,
                            show (decide ((102 : Nat) = 108)) = false from by decide,
                            show text [102] = "f" from by decide]
        rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)] at h
        -- `t`: a `let`
        by_cases h116 : kk = 116
        · subst h116
          rw [if_pos rfl, recordExprLet] at h
          split at h
          · simp at h
          · rename_i r₄ hsp2
            split at h
            · simp at h
            · rename_i ty r₅ her
              split at h
              · simp at h
              · rename_i r₆ hsp3
                split at h
                · simp at h
                · rename_i vl r₇ her2
                  split at h
                  · simp at h
                  · rename_i r₈ hsp4
                    split at h
                    · simp at h
                    · rename_i bd r₉ her3
                      split at h
                      · simp at h
                      · rename_i r₁₀ hnl
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                          (Or.inl (byteAt_afterSpace hsp2))
                        rw [set_pos_set_pos] at e₂ s₂
                        obtain ⟨k₃, e₃, s₃⟩ :=
                          exprRef_step (hm.pos k₂) (atSep_space s₂ hsp2) her
                        rw [set_pos_set_pos] at e₃ s₃
                        obtain ⟨k₄, e₄, s₄⟩ :=
                          exprRef_step (hm.pos k₃) (atSep_space s₃ hsp3) her2
                        rw [set_pos_set_pos] at e₄ s₄
                        obtain ⟨k₅, e₅, s₅⟩ :=
                          exprRef_step (hm.pos k₄) (atSep_space s₄ hsp4) her3
                        rw [set_pos_set_pos] at e₅ s₅
                        obtain ⟨hbs, hdone⟩ := atSep_newline s₅ hnl
                        refine ⟨hbs, _, ?_, match_push_exprs hm _ k₅, hdone⟩
                        reader_simp [e₁, e₂, e₃, e₄, e₅,
                          show text [116] = "t" from by decide]
        rw [if_neg h116] at h
        -- `n`: a natural-number literal
        by_cases h110 : kk = 110
        · subst h110
          rw [if_pos rfl, recordExprNatLit] at h
          split at h
          · simp at h
          · rename_i r₄ hsp2
            split at h
            · simp at h
            · rename_i nv r₅ hrn
              split at h
              · simp at h
              · rename_i r₆ hnl
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                  (Or.inl (byteAt_afterSpace hsp2))
                rw [set_pos_set_pos] at e₂ s₂
                obtain ⟨k₃, e₃, s₃⟩ :=
                  natTok_step (atSep_space s₂ hsp2) (readBigNat_spec hrn)
                rw [set_pos_set_pos] at e₃ s₃
                obtain ⟨hbs, hdone⟩ := atSep_newline s₃ hnl
                refine ⟨hbs, _, ?_, match_push_exprs hm _ k₃, hdone⟩
                reader_simp [e₁, e₂, e₃, show text [110] = "n" from by decide]
        rw [if_neg h110] at h
        -- `g`: a string literal
        by_cases h103 : kk = 103
        · subst h103
          rw [if_pos rfl, recordExprStrLit] at h
          split at h
          · simp at h
          · rename_i r₄ hsp2
            split at h
            · simp at h
            · rename_i sv r₅ hrs
              split at h
              · simp at h
              · rename_i r₆ hnl
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                  (Or.inl (byteAt_afterSpace hsp2))
                rw [set_pos_set_pos] at e₂ s₂
                obtain ⟨k₃, e₃, s₃⟩ := strTok_step (atSep_space s₂ hsp2) hrs
                rw [set_pos_set_pos] at e₃ s₃
                obtain ⟨hbs, hdone⟩ := atSep_newline s₃ hnl
                refine ⟨hbs, _, ?_, match_push_exprs hm _ k₃, hdone⟩
                reader_simp [e₁, e₂, e₃, show text [103] = "g" from by decide]
        rw [if_neg h103] at h
        -- `p`: a projection
        by_cases h112 : kk = 112
        · subst h112
          rw [if_pos rfl, recordExprProj] at h
          split at h
          · simp at h
          · rename_i r₄ hsp2
            split at h
            · simp at h
            · rename_i sn r₅ hnr
              split at h
              · simp at h
              · rename_i r₆ hsp3
                split at h
                · simp at h
                · rename_i iv r₇ hrn
                  split at h
                  · simp at h
                  · rename_i r₈ hsp4
                    split at h
                    · simp at h
                    · rename_i sv r₉ her
                      split at h
                      · simp at h
                      · rename_i r₁₀ hnl
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        obtain ⟨k₂, e₂, s₂⟩ := letter_step s₁ hsp (by omega)
                          (Or.inl (byteAt_afterSpace hsp2))
                        rw [set_pos_set_pos] at e₂ s₂
                        obtain ⟨k₃, e₃, s₃⟩ :=
                          nameRef_step (hm.pos k₂) (atSep_space s₂ hsp2) hnr
                        rw [set_pos_set_pos] at e₃ s₃
                        obtain ⟨k₄, e₄, s₄⟩ :=
                          natTok_step (atSep_space s₃ hsp3) (readNat_spec hrn)
                        rw [set_pos_set_pos] at e₄ s₄
                        obtain ⟨k₅, e₅, s₅⟩ :=
                          exprRef_step (hm.pos k₄) (atSep_space s₄ hsp4) her
                        rw [set_pos_set_pos] at e₅ s₅
                        obtain ⟨hbs, hdone⟩ := atSep_newline s₅ hnl
                        refine ⟨hbs, _, ?_, match_push_exprs hm _ k₅, hdone⟩
                        reader_simp [e₁, e₂, e₃, e₄, e₅,
                          show text [112] = "p" from by decide]
        rw [if_neg h112] at h
        simp at h

theorem listFrom_zero {α : Type} {d : Bytes → Tables → Option (α × Bytes)}
    {bs : Bytes} {tb : Tables} {out res : List α} {bs' : Bytes}
    (h : listFrom d bs tb 0 out = some (res, bs')) : res = out ∧ bs' = bs := by
  simp only [listFrom, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem listFrom_succ {α : Type} {d : Bytes → Tables → Option (α × Bytes)}
    {bs : Bytes} {tb : Tables} {k : Nat} {out res : List α} {bs' : Bytes}
    (h : listFrom d bs tb (k + 1) out = some (res, bs')) :
    ∃ r a r₂, afterSpace bs = some r ∧ d r tb = some (a, r₂) ∧
      listFrom d r₂ tb k (out ++ [a]) = some (res, bs') := by
  rw [listFrom] at h
  split at h
  · simp at h
  · rename_i r hs
    split at h
    · simp at h
    · rename_i a r₂ hd
      exact ⟨r, a, r₂, hs, hd, h⟩

/-- One element of a counted list, on both sides at once. -/
theorem list_peel {α : Type} {p : R α} {d : Bytes → Tables → Option (α × Bytes)}
    (hp : Reads p d) {st : RState} {tb : Tables} {bs : Bytes}
    {rest : Option Bytes} {k : Nat} {out res : List α} {bs' : Bytes}
    (hm : Match st tb) (hsep : AtSep st bs rest)
    (h : listFrom d bs tb (k + 1) out = some (res, bs')) :
    ∃ (a : α) (r₂ : Bytes) (j : Nat), p st = .ok (a, { st with pos := j }) ∧
      AtSep { st with pos := j } r₂ rest ∧
      listFrom d r₂ tb k (out ++ [a]) = some (res, bs') := by
  obtain ⟨r, a, r₂, hs, hd, hrest⟩ := listFrom_succ h
  obtain ⟨j, e, s⟩ := hp hm (atSep_space hsep hs) hd
  exact ⟨a, r₂, j, e, s, hrest⟩

theorem reads_exprList : Reads (listTok ConRon.Dump.exprRef) exprList :=
  fun hm hat h => listTok_step reads_exprRef hm hat (by rw [← exprList_eq]; exact h)

theorem recordPinSet_step {st : RState} {tb tb' : Tables} {bs bs' : Bytes}
    {rest : Option Bytes} (hm : Match st tb) (hat : AtField st bs rest)
    (h : recordPinSet bs tb = some (tb', bs')) :
    rest = some bs' ∧ RecordOk (parseRecord "S") st tb' := by
  rw [recordPinSet] at h
  split at h
  · simp at h
  · rename_i tc r₁ hrs
    split at h
    · simp at h
    · rename_i pins r₂ hpe
      split at h
      · simp at h
      · rename_i proofs r₃ hqe
        split at h
        · simp at h
        · rename_i r₄ hnl
          obtain ⟨k₀, e₀, s₀⟩ := strTok_step hat hrs
          rw [pinsEight, pinsEightFrom_eq] at hpe
          obtain ⟨p0, ra0, j0, ep0, sp0, hl0⟩ :=
            list_peel reads_exprRef (hm.pos k₀) s₀ hpe
          obtain ⟨p1, ra1, j1, ep1, sp1, hl1⟩ :=
            list_peel reads_exprRef (hm.pos j0) sp0 hl0
          rw [set_pos_set_pos] at ep1 sp1
          obtain ⟨p2, ra2, j2, ep2, sp2, hl2⟩ :=
            list_peel reads_exprRef (hm.pos j1) sp1 hl1
          rw [set_pos_set_pos] at ep2 sp2
          obtain ⟨p3, ra3, j3, ep3, sp3, hl3⟩ :=
            list_peel reads_exprRef (hm.pos j2) sp2 hl2
          rw [set_pos_set_pos] at ep3 sp3
          obtain ⟨p4, ra4, j4, ep4, sp4, hl4⟩ :=
            list_peel reads_exprRef (hm.pos j3) sp3 hl3
          rw [set_pos_set_pos] at ep4 sp4
          obtain ⟨p5, ra5, j5, ep5, sp5, hl5⟩ :=
            list_peel reads_exprRef (hm.pos j4) sp4 hl4
          rw [set_pos_set_pos] at ep5 sp5
          obtain ⟨p6, ra6, j6, ep6, sp6, hl6⟩ :=
            list_peel reads_exprRef (hm.pos j5) sp5 hl5
          rw [set_pos_set_pos] at ep6 sp6
          obtain ⟨p7, ra7, j7, ep7, sp7, hl7⟩ :=
            list_peel reads_exprRef (hm.pos j6) sp6 hl6
          rw [set_pos_set_pos] at ep7 sp7
          obtain ⟨hpins, hra⟩ := listFrom_zero hl7
          rw [← hra] at sp7
          rw [proofsEight, proofsEightFrom_eq] at hqe
          obtain ⟨q0, rb0, n0, eq0, sq0, hk0⟩ :=
            list_peel reads_exprList (hm.pos j7) sp7 hqe
          rw [set_pos_set_pos] at eq0 sq0
          obtain ⟨q1, rb1, n1, eq1, sq1, hk1⟩ :=
            list_peel reads_exprList (hm.pos n0) sq0 hk0
          rw [set_pos_set_pos] at eq1 sq1
          obtain ⟨q2, rb2, n2, eq2, sq2, hk2⟩ :=
            list_peel reads_exprList (hm.pos n1) sq1 hk1
          rw [set_pos_set_pos] at eq2 sq2
          obtain ⟨q3, rb3, n3, eq3, sq3, hk3⟩ :=
            list_peel reads_exprList (hm.pos n2) sq2 hk2
          rw [set_pos_set_pos] at eq3 sq3
          obtain ⟨q4, rb4, n4, eq4, sq4, hk4⟩ :=
            list_peel reads_exprList (hm.pos n3) sq3 hk3
          rw [set_pos_set_pos] at eq4 sq4
          obtain ⟨q5, rb5, n5, eq5, sq5, hk5⟩ :=
            list_peel reads_exprList (hm.pos n4) sq4 hk4
          rw [set_pos_set_pos] at eq5 sq5
          obtain ⟨q6, rb6, n6, eq6, sq6, hk6⟩ :=
            list_peel reads_exprList (hm.pos n5) sq5 hk5
          rw [set_pos_set_pos] at eq6 sq6
          obtain ⟨q7, rb7, n7, eq7, sq7, hk7⟩ :=
            list_peel reads_exprList (hm.pos n6) sq6 hk6
          rw [set_pos_set_pos] at eq7 sq7
          obtain ⟨hproofs, hrb⟩ := listFrom_zero hk7
          rw [← hrb] at sq7
          have hpins' : pins = [p0, p1, p2, p3, p4, p5, p6, p7] := by rw [hpins]; simp
          have hproofs' : proofs = [q0, q1, q2, q3, q4, q5, q6, q7] := by
            rw [hproofs]; simp
          rw [hpins', hproofs'] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hbs, hdone⟩ := atSep_newline sq7 hnl
          refine ⟨hbs, _, ?_, match_push_sets hm _ n7, hdone⟩
          reader_simp [e₀, ep0, ep1, ep2, ep3, ep4, ep5, ep6, ep7,
            eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]

/-! ## The pass -/

theorem text_nil : text ([] : Bytes) = "" := by simp [text]

theorem splitOn_text_nil : (text ([] : Bytes)).splitOn "\n" = [text []] := by
  rw [PinsSplit.newline_eq, text_eq]
  exact PinsSplit.splitOn_of_not_mem (by simp)

theorem isEmpty_text_cons (b : Nat) (l : Bytes) :
    (text (b :: l)).isEmpty = false := by
  rw [Bool.eq_false_iff, ne_eq, String.isEmpty_iff, text_eq]
  simp

theorem text_ne_end {k : Nat} : (text [k] == "end") = false := by
  rw [beq_eq_false_iff_ne]
  intro he
  have := congrArg (fun s => s.toList.length) he
  simp [toList_text] at this

/-- A byte string either has a first newline or has none at all. -/
theorem split_line : ∀ (bs : Bytes),
    (∃ line r, bs = line ++ 10 :: r ∧ 10 ∉ line) ∨ 10 ∉ bs
  | [] => Or.inr (by simp)
  | b :: bs => by
    by_cases hb : b = 10
    · exact Or.inl ⟨[], bs, by rw [hb]; rfl, by simp⟩
    · rcases split_line bs with ⟨line, r, hr, h10⟩ | h10
      · refine Or.inl ⟨b :: line, r, by rw [hr]; rfl, ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun hh => hb hh.symm, h10⟩
      · refine Or.inr ?_
        simp only [List.mem_cons, not_or]
        exact ⟨fun hh => hb hh.symm, h10⟩

theorem recordStep_kind {k : Nat} {bs : Bytes} {tb : Tables} {x : Tables × Bytes}
    (h : recordStep k bs tb = some x) :
    k = 78 ∨ k = 76 ∨ k = 87 ∨ k = 69 ∨ k = 83 := by
  rw [recordStep] at h
  by_cases h78 : k = 78
  · exact Or.inl h78
  rw [if_neg h78] at h
  by_cases h76 : k = 76
  · exact Or.inr (Or.inl h76)
  rw [if_neg h76] at h
  by_cases h87 : k = 87
  · exact Or.inr (Or.inr (Or.inl h87))
  rw [if_neg h87] at h
  by_cases h69 : k = 69
  · exact Or.inr (Or.inr (Or.inr (Or.inl h69)))
  rw [if_neg h69] at h
  by_cases h83 : k = 83
  · exact Or.inr (Or.inr (Or.inr (Or.inr h83)))
  rw [if_neg h83] at h; simp at h

theorem recordStep_step {st : RState} {tb tb' : Tables} {k : Nat} {bs bs' : Bytes}
    {rest : Option Bytes} (hm : Match st tb) (hat : AtField st bs rest)
    (h : recordStep k bs tb = some (tb', bs')) :
    rest = some bs' ∧ RecordOk (parseRecord (text [k])) st tb' := by
  rw [recordStep] at h
  by_cases h78 : k = 78
  · subst h78; rw [if_pos rfl] at h
    rw [show text [78] = "N" from by decide]; exact recordName_step hm hat h
  rw [if_neg h78] at h
  by_cases h76 : k = 76
  · subst h76; rw [if_pos rfl] at h
    rw [show text [76] = "L" from by decide]; exact recordLevel_step hm hat h
  rw [if_neg h76] at h
  by_cases h87 : k = 87
  · subst h87; rw [if_pos rfl] at h
    rw [show text [87] = "W" from by decide]; exact recordPw_step hm hat h
  rw [if_neg h87] at h
  by_cases h69 : k = 69
  · subst h69; rw [if_pos rfl] at h
    rw [show text [69] = "E" from by decide]; exact recordExpr_step hm hat h
  rw [if_neg h69] at h
  by_cases h83 : k = 83
  · subst h83; rw [if_pos rfl] at h
    rw [show text [83] = "S" from by decide]; exact recordPinSet_step hm hat h
  rw [if_neg h83] at h; simp at h

theorem runFooter_shape {bs : Bytes} {tb : Tables}
    {ps : List ConLeche.NatOpPinSet} (h : runFooter bs tb = some ps) :
    ∃ bs₂, bs = 110 :: 100 :: bs₂ := by
  unfold runFooter at h
  split at h
  · exact ⟨_, rfl⟩
  · simp at h

open Lean.Parser.Tactic in
syntax "lines_simp" "[" simpLemma,* "]" : tactic

open Lean.Parser.Tactic in
macro_rules
  | `(tactic| lines_simp [$ts,*]) =>
    `(tactic| simp only [ite_apply, bind, StateT.bind, Except.bind, get, getThe,
        MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
        String.reduceBEq, Bool.false_and, Bool.and_false, Bool.and_true,
        Bool.true_and, if_true, if_false, Bool.false_eq_true, reduceIte, $ts,*])

theorem afterSpace_eq {r r' : Bytes} (h : afterSpace r = some r') :
    r = 32 :: r' := by
  cases r with
  | nil => simp [afterSpace] at h
  | cons b r₀ =>
    have hb : b = 32 := byteAt_afterSpace h
    subst hb
    simp only [afterSpace, Option.some.injEq] at h
    rw [h]

theorem afterNewline_eq {r r' : Bytes} (h : afterNewline r = some r') :
    r = 10 :: r' := by
  cases r with
  | nil => simp [afterNewline] at h
  | cons b r₀ =>
    have hb : b = 10 := byteAt_afterNewline h
    subst hb
    simp only [afterNewline, Option.some.injEq] at h
    rw [h]

/-- The state `runLines` opens a line in: the line's tokens, cursor at zero. -/
def lineState (st : RState) (l : String) : RState :=
  { st with lineNo := st.lineNo + 1, toks := (l.splitOn " ").toArray,
            pos := 0 }

theorem modify_line (st : RState) (l : String) :
    (modify fun s =>
        { s with lineNo := s.lineNo + 1, toks := (l.splitOn " ").toArray,
                 pos := 0 } : R Unit) st = .ok ((), lineState st l) := by
  simp only [lineState, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, StateT.pure, Except.pure]

theorem lineState_match {st : RState} {tb : Tables} (hm : Match st tb)
    (l : String) : Match (lineState st l) tb :=
  ⟨hm.names, hm.levels, hm.pws, hm.exprs, hm.sets⟩

theorem lineState_pinSets (st : RState) (l : String) :
    (lineState st l).pinSets = st.pinSets := rfl

theorem lineState_toks (st : RState) (line : Bytes) :
    (lineState st (text line)).toks.toList.drop (lineState st (text line)).pos
      = (text line).splitOn " " := by
  simp [lineState]

/-- **The record pass.**  `runLines` reads the lines `runRecords` read. -/
theorem runRecords_step : ∀ (fuel : Nat) {st : RState} {tb : Tables} {bytes : Bytes}
    {ps : List ConLeche.NatOpPinSet}, Match st tb → (∀ b ∈ bytes, b < 128) →
    runRecords fuel bytes tb = some ps →
    ∃ st', runLines ((text bytes).splitOn "\n") st = .ok ((), st') ∧
      st'.pinSets.toList = ps
  | 0, _, _, _, _, _, _, h => by simp [runRecords] at h
  | _ + 1, _, _, [], _, _, _, h => by simp [runRecords] at h
  | fuel + 1, st, tb, k :: bs, ps, hm, hasc, h => by
    rw [runRecords] at h
    by_cases hk : k = 101
    · -- the footer
      subst hk
      rw [if_pos rfl] at h
      obtain ⟨bs₂, rfl⟩ := runFooter_shape h
      rw [runFooter] at h
      split at h
      · simp at h
      · rename_i rA hsp
        split at h
        · simp at h
        · rename_i n rB hri
          split at h
          · simp at h
          · rename_i rC hnl
            split at h
            · simp at h
            · rename_i hcond
              simp only [Option.some.injEq] at h
              subst h
              have hc1 : rC = [] := by
                by_contra hx; exact hcond (by simp [hx])
              have hc2 : n = tb.sets.length := by
                by_contra hx; exact hcond (by simp [hx])
              subst hc1
              have hbs₂ := afterSpace_eq hsp
              subst hbs₂
              have hrB := afterNewline_eq hnl
              subst hrB
              obtain ⟨dg, hdg, -, hdgd, -, -⟩ := readIndex_spec hri
              subst hdg
              have hline10 : 10 ∉ (101 :: 110 :: 100 :: 32 :: dg) := by
                simp only [List.mem_cons, not_or]
                refine ⟨by omega, by omega, by omega, by omega, ?_⟩
                exact digits_ne_newline hdgd
              have hlineasc : ∀ b ∈ (101 :: 110 :: 100 :: 32 :: dg), b < 128 := by
                intro b hb
                refine hasc b ?_
                simp only [List.mem_cons] at hb ⊢
                rcases hb with rfl | rfl | rfl | rfl | hb
                · exact Or.inl rfl
                · exact Or.inr (Or.inl rfl)
                · exact Or.inr (Or.inr (Or.inl rfl))
                · exact Or.inr (Or.inr (Or.inr (by simp)))
                · exact Or.inr (Or.inr (Or.inr (by simp [hb])))
              have hbytes : (101 :: 110 :: 100 :: 32 :: (dg ++ [10]) : Bytes)
                  = (101 :: 110 :: 100 :: 32 :: dg) ++ 10 :: [] := by simp
              have hsplit :
                  (text (101 :: 110 :: 100 :: 32 :: (dg ++ [10]))).splitOn "\n"
                    = text (101 :: 110 :: 100 :: 32 :: dg)
                      :: (text ([] : Bytes)).splitOn "\n" := by
                rw [hbytes]; exact splitOn_line_cons hline10 hlineasc
              have hat₁ :
                  AtField (lineState st (text (101 :: 110 :: 100 :: 32 :: dg)))
                    (101 :: 110 :: 100 :: 32 :: (dg ++ [10])) (some []) :=
                ⟨101 :: 110 :: 100 :: 32 :: dg, hbytes, hline10, hlineasc,
                  lineState_toks st _⟩
              obtain ⟨htok, hsep₂⟩ := tok_step hat₁ (f := [101, 110, 100])
                (bs' := 32 :: (dg ++ [10])) rfl (by simp) (by simp) (Or.inl rfl)
              obtain ⟨k₃, enat, hsep₃⟩ :=
                natTok_step (atSep_space hsep₂ rfl) (readIndex_spec hri)
              rw [set_pos_set_pos] at enat hsep₃
              obtain ⟨-, hdone⟩ := atSep_newline hsep₃ rfl
              refine ⟨{ lineState st (text (101 :: 110 :: 100 :: 32 :: dg)) with
                  pos := k₃ }, ?_, ?_⟩
              · rw [hsplit, splitOn_text_nil, runLines]
                lines_simp [modify_line, isEmpty_text_cons, htok,
                  show text [101, 110, 100] = "end" from by decide, enat]
                have hdone' : k₃
                    = (lineState st (text (101 :: 110 :: 100 :: 32 :: dg))).toks.size :=
                  hdone
                lines_simp [lineState_pinSets,
                  show st.pinSets.size = tb.sets.length from by
                    simpa using congrArg List.length hm.sets,
                  hc2, bne_self_eq_false,
                  show (k₃ != (lineState st
                      (text (101 :: 110 :: 100 :: 32 :: dg))).toks.size) = false from by
                    simp [hdone'],
                  show ([text ([] : Bytes)].any fun x => !x.isEmpty) = false from by
                    simp [text_nil]]
              · exact hm.sets
    · -- a record
      rw [if_neg hk] at h
      split at h
      · simp at h
      · rename_i body hsp
        split at h
        · simp at h
        · rename_i tb₂ r hrec
          have hbs := afterSpace_eq hsp
          subst hbs
          have hkind := recordStep_kind hrec
          have hk10 : k ≠ 10 := by rcases hkind with rfl|rfl|rfl|rfl|rfl <;> omega
          rcases split_line body with ⟨bodyline, r₀, hbl, hbl10⟩ | hnone
          · subst hbl
            have hline10 : 10 ∉ (k :: 32 :: bodyline) := by
              simp only [List.mem_cons, not_or]
              exact ⟨fun hh => hk10 hh.symm, by omega, hbl10⟩
            have hlineasc : ∀ b ∈ (k :: 32 :: bodyline), b < 128 := by
              intro b hb
              refine hasc b ?_
              simp only [List.mem_cons] at hb ⊢
              rcases hb with rfl | rfl | hb
              · exact Or.inl rfl
              · exact Or.inr (by simp)
              · exact Or.inr (by simp [hb])
            have hbytes : (k :: 32 :: (bodyline ++ 10 :: r₀) : Bytes)
                = (k :: 32 :: bodyline) ++ 10 :: r₀ := by simp
            have hsplit : (text (k :: 32 :: (bodyline ++ 10 :: r₀))).splitOn "\n"
                = text (k :: 32 :: bodyline) :: (text r₀).splitOn "\n" := by
              rw [hbytes]; exact splitOn_line_cons hline10 hlineasc
            have hat₁ : AtField (lineState st (text (k :: 32 :: bodyline)))
                (k :: 32 :: (bodyline ++ 10 :: r₀)) (some r₀) :=
              ⟨k :: 32 :: bodyline, hbytes, hline10, hlineasc, lineState_toks st _⟩
            obtain ⟨htok, hsep₂⟩ := tok_step hat₁ (f := [k])
              (bs' := 32 :: (bodyline ++ 10 :: r₀)) rfl
              (by simp only [List.mem_singleton]; omega)
              (by simp only [List.mem_singleton]; omega) (Or.inl rfl)
            obtain ⟨hrest, st₃, erec, hm₃, hdone⟩ :=
              recordStep_step ((lineState_match hm _).pos _)
                (atSep_space hsep₂ rfl) hrec
            have hr : r₀ = r := by simpa using hrest
            subst hr
            obtain ⟨st', hrun, hps⟩ := runRecords_step fuel hm₃ (fun b hb =>
              hasc b (by
                simp only [List.mem_cons]
                refine Or.inr (Or.inr ?_)
                simp only [List.mem_append, List.mem_cons]
                exact Or.inr (Or.inr hb))) h
            refine ⟨st', ?_, hps⟩
            rw [hsplit, runLines]
            lines_simp [modify_line, isEmpty_text_cons, htok, text_ne_end, erec,
              show (st₃.pos != st₃.toks.size) = false from by simp [hdone], hrun]
          · -- the line has no newline: no record can end on it
            have hline10 : 10 ∉ (k :: 32 :: body) := by
              simp only [List.mem_cons, not_or]
              exact ⟨fun hh => hk10 hh.symm, by omega, hnone⟩
            have hlineasc : ∀ b ∈ (k :: 32 :: body), b < 128 := by
              intro b hb
              refine hasc b ?_
              simp only [List.mem_cons] at hb ⊢
              rcases hb with rfl | rfl | hb
              · exact Or.inl rfl
              · exact Or.inr (by simp)
              · exact Or.inr (by simp [hb])
            have hat₁ : AtField (lineState st (text (k :: 32 :: body)))
                (k :: 32 :: body) none :=
              ⟨k :: 32 :: body, rfl, hline10, hlineasc, lineState_toks st _⟩
            obtain ⟨-, hsep₂⟩ := tok_step hat₁ (f := [k]) (bs' := 32 :: body) rfl
              (by simp only [List.mem_singleton]; omega)
              (by simp only [List.mem_singleton]; omega) (Or.inl rfl)
            obtain ⟨hrest, -⟩ :=
              recordStep_step ((lineState_match hm _).pos _)
                (atSep_space hsep₂ rfl) hrec
            exact absurd hrest (by simp)

theorem startsWith_eq : ∀ {bs p : Bytes}, startsWith bs p = true →
    bs = p ++ bs.drop p.length
  | _, [], _ => by simp
  | [], _ :: _, h => by simp [startsWith] at h
  | b :: bs, c :: p, h => by
    simp only [startsWith, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    have hrec := startsWith_eq h2
    simp only [List.cons_append, List.length_cons, List.drop_succ_cons]
    exact congrArg (b :: ·) hrec

/-- **(B): `PinsDec` refines the reader.**  If the byte decoder accepts `bs`
and returns `ps`, then `ConRon.Dump.parsePins` accepts the text of `bs` and
returns the same list of variants. -/
theorem parsePins_of_decode {bs : Bytes} {ps : List ConLeche.NatOpPinSet}
    (h : decode bs = some ps) (hasc : ∀ b ∈ bs, b < 128) :
    ConRon.Dump.parsePins (text bs) = .ok ps := by
  rw [decode] at h
  by_cases hsw : startsWith bs headerBytes = true
  · rw [if_pos hsw] at h
    obtain ⟨rest, hrest⟩ : ∃ r, r = bs.drop headerBytes.length := ⟨_, rfl⟩
    rw [← hrest] at h
    have hbs : bs = [99, 111, 110, 45, 114, 111, 110, 45, 112, 105, 110, 115,
        47, 49] ++ 10 :: rest := by
      rw [hrest]; exact startsWith_eq hsw
    have hascr : ∀ b ∈ rest, b < 128 := by
      intro b hb
      refine hasc b ?_
      rw [hbs]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hb)
    have hsplit := splitOn_line_cons (l := [99, 111, 110, 45, 114, 111, 110, 45,
      112, 105, 110, 115, 47, 49]) (r := rest) (by decide) (by decide)
    obtain ⟨st', hrun, hps⟩ := runRecords_step bs.length
      (tb := tablesNew) (st := { lineNo := 1 })
      ⟨rfl, rfl, rfl, rfl, rfl⟩ hascr h
    rw [ConRon.Dump.parsePins, hbs, hsplit,
      show text [99, 111, 110, 45, 114, 111, 110, 45, 112, 105, 110, 115, 47, 49]
        = ConRon.Dump.pinsHeader from by decide]
    simp only [bne_self_eq_false, Bool.false_eq_true, if_false, StateT.run, hrun,
      hps]
  · rw [if_neg hsw] at h; simp at h

end ConRon.Refine.PinsRead


