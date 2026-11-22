import ConRon.Refine2.Frontend.Text
import ConLeche.Driver.Cli
import Batteries.Data.String.Lemmas

/-!
# `ConRon.MainTheorem.Args` — the argument strings, as the extracted parser reads them

**Task #171, slice 2** (DESIGN.md §3.9).  con-leche's main theorems name the `.olean` runs'
lookup and roots by their argument strings: `Driver.searchPathOf dirs` (the nonempty
`:`-separated directories of `dirs`, by `String.splitOn`) and `Olean.parseModName root`.  The
extracted parser (`driver::cli`) reads code points.  This module bridges the two:

| lemma | what it says |
|---|---|
| `splitOn_one` | `String.splitOn` at a one-character separator is `List.splitOn` |
| `push_dirs_search` | `cli::push_dirs` of `--search-path=` ++ `dirs` is `searchPathOf dirs` |
| `parse_mod_name_some` | `files::parse_mod_name` of `root`'s code points is `parseModName root`, well formed |
| `cps_beq_eq`, `cps_starts_with_eq` | the parser's word tests answer, as list tests |
| `parse_one_*`, `loop_word`, `loop_end`, `help_word`, `help_end` | one argument of `cli::parse_args` and `cli::help_wanted` |
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated
open ConRon.Refine (absString absName StrWF NameWF)


namespace ConRon.Args
section Split
open String

theorem splitOnAux_one (c : Char) : ∀ (r l m : List Char) (acc : List String),
    String.splitOnAux (ofList (l ++ m ++ r)) (String.singleton c) ⟨utf8Len l⟩
      ⟨utf8Len l + utf8Len m⟩ 0 acc
      = acc.reverse ++ (List.splitOnPPrepend (· == c) r m.reverse).map ofList := by
  intro r
  induction r with
  | nil =>
    intro l m acc
    rw [String.splitOnAux]
    simp only [List.append_nil]
    have hend : Pos.Raw.atEnd (ofList (l ++ m)) ⟨utf8Len l + utf8Len m⟩ := by
      rw [String.atEnd_iff, rawEndPos_ofList, Pos.Raw.mk_le_mk, utf8Len_append]
    rw [ite_eq_left hend]
    simpa using extract_of_valid l m []
  | cons c' r ih =>
    intro l m acc
    rw [String.splitOnAux]
    have hne : ¬ (Pos.Raw.atEnd (ofList (l ++ m ++ c' :: r)) ⟨utf8Len l + utf8Len m⟩) := by
      rw [String.atEnd_iff, rawEndPos_ofList, Pos.Raw.mk_le_mk]
      simp only [utf8Len_append, utf8Len_cons]
      have := Char.utf8Size_pos c'
      omega
    rw [ite_eq_right hne]
    have hg : Pos.Raw.get (ofList (l ++ m ++ c' :: r)) ⟨utf8Len l + utf8Len m⟩ = c' := by
      simpa [List.append_assoc] using get_of_valid (l ++ m) (c' :: r)
    have hgs : Pos.Raw.get (String.singleton c) 0 = c := by
      simpa using get_of_valid [] [c]
    have hn : Pos.Raw.next (ofList (l ++ m ++ c' :: r)) ⟨utf8Len l + utf8Len m⟩ =
        ⟨utf8Len l + utf8Len m + c'.utf8Size⟩ := by
      simpa [List.append_assoc] using next_of_valid (l ++ m) c' r
    rw [hg, hgs, List.splitOnPPrepend_cons_eq_ite]
    by_cases hc : c' = c
    · subst hc
      simp only [beq_self_eq_true, ite_true, hn]
      have hns : Pos.Raw.next (String.singleton c') 0 = ⟨c'.utf8Size⟩ := by
        simpa using next_of_valid [] c' []
      have hend : Pos.Raw.atEnd (String.singleton c') ⟨c'.utf8Size⟩ := by
        rw [show String.singleton c' = ofList [c'] by simp, String.atEnd_iff, rawEndPos_ofList]
        simp
      rw [hns, ite_eq_left hend]
      have hu : Pos.Raw.unoffsetBy ⟨utf8Len l + utf8Len m + c'.utf8Size⟩ ⟨c'.utf8Size⟩
          = ⟨utf8Len l + utf8Len m⟩ := by
        simp [Pos.Raw.unoffsetBy]
      rw [hu, extract_of_valid l m (c' :: r)]
      have := ih (l ++ m ++ [c']) [] (ofList m :: acc)
      simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append,
        utf8Len_append, utf8Len_cons, utf8Len_nil, Nat.add_zero, Nat.zero_add, List.reverse_nil] at this ⊢
      rw [show utf8Len l + (utf8Len m + c'.utf8Size) = utf8Len l + utf8Len m + c'.utf8Size by omega] at this
      rw [this, List.splitOnPPrepend_nil_right]
      simp
    · have hb : (c' == c) = false := by simpa using hc
      simp only [hb, Bool.false_eq_true, ite_false]
      have hu : Pos.Raw.unoffsetBy ⟨utf8Len l + utf8Len m⟩ 0 = ⟨utf8Len l + utf8Len m⟩ := by
        simp [Pos.Raw.unoffsetBy]
      rw [hu, hn]
      have := ih l (m ++ [c']) acc
      simp only [List.append_assoc, List.cons_append, List.nil_append,
        utf8Len_append, utf8Len_cons, utf8Len_nil, Nat.zero_add, List.reverse_append,
        List.reverse_cons, List.reverse_nil] at this ⊢
      rw [show utf8Len l + (utf8Len m + c'.utf8Size) = utf8Len l + utf8Len m + c'.utf8Size by omega] at this
      rw [this]

/-- **`splitOn` at a one-character separator** is the list split. -/
theorem splitOn_one (s : String) (c : Char) :
    s.splitOn (String.singleton c) = (s.toList.splitOn c).map ofList := by
  rw [String.splitOn, ite_eq_right (by simp)]
  have := splitOnAux_one c s.toList [] [] []
  simp only [List.nil_append, utf8Len_nil, Nat.add_zero, List.reverse_nil, ofList_toList] at this
  refine this.trans ?_
  rw [List.splitOnPPrepend_nil_right]
  rfl
end Split
end ConRon.Args

namespace ConRon.Args

theorem ofList_ne (l : List Char) : (String.ofList l != "") = (l != []) := by
  have : (String.ofList l = "") ↔ l = [] := by
    constructor
    · intro h; have := congrArg String.toList h; simpa using this
    · intro h; subst h; rfl
  by_cases h : l = []
  · subst h; rfl
  · have h2 : ¬ String.ofList l = "" := fun e => h (this.mp e)
    rw [bne_iff_ne.mpr h2, bne_iff_ne.mpr h]

theorem absString_ne (v : alloc.vec.Vec Std.U32) :
    (absString v != "") = (v.val != []) := by
  rw [absString, ofList_ne]
  cases v.val <;> rfl

theorem u32_eq_char {c n : Std.U32} {x y : Char} (hc : c.val = x.toNat) (hn : n.val = y.toNat) :
    c = n ↔ x = y := by
  constructor
  · intro h; subst h; exact Char.toNat_inj.mp (by omega)
  · intro h; subst h; exact UScalar.eq_of_val_eq (by rw [hc, hn])

theorem absString_push {v w : alloc.vec.Vec Std.U32} {c : Std.U32} {x : Char} (hx : c.val = x.toNat)
    (h : alloc.vec.Vec.push v c = ok w) : absString w = (absString v).push x := by
  unfold absString
  rw [ConRon.Refine.vec_push_val h, List.map_append]
  simp only [List.map_cons, List.map_nil, hx, Char.ofNat_toNat]
  rw [String.push_eq_append]
  simp

theorem vec_index_ok' {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (hi : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok v.val[i.val] := by
  simp only [alloc.vec.Vec.index_slice_index]
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hi)
  rw [hy, hyv]

theorem len_pos {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.len v > 0#usize) ↔ v.val ≠ [] := by
  have := alloc.vec.Vec.len_val v
  cases h : v.val <;> simp [alloc.vec.Vec.length, h] at this ⊢

theorem push_dirs_loop_val {cs : List Char} {v : alloc.vec.Vec Std.U32}
    (hs : v.val.map UScalar.val = cs.map Char.toNat) :
    ∀ (k : Nat) (i : Std.Usize) out cur, v.val.length - i.val = k → i.val ≤ v.val.length →
      ∀ {r}, driver.cli.push_dirs_loop v out cur i = ok r →
      (r.1.val ++ (if r.2.val = [] then [] else [r.2])).map absString =
        out.val.map absString ++ (((List.splitOnPPrepend (· == ':') (cs.drop i.val)
          (absString cur).toList.reverse).map String.ofList).filter (· != "")) := by
  have hlen : v.val.length = cs.length := by
    have := congrArg List.length hs; simpa using this
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro i out cur hk hi r h
  rw [driver.cli.push_dirs_loop] at h
  by_cases hlt : i.val < v.val.length
  · have hlt' : i < alloc.vec.Vec.len v := by scalar_tac
    rw [ite_eq_left hlt', vec_index_ok' hlt, bind_ok] at h
    have hic : i.val < cs.length := by omega
    have hc : (v.val[i.val]).val = (cs[i.val]).toNat := by
      have := congrArg (fun l => l[i.val]?) hs
      simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hic,
        Option.map_some, Option.some.injEq] at this
      exact this
    rw [List.drop_eq_getElem_cons hic, List.splitOnPPrepend_cons_eq_ite]
    generalize v.val[i.val] = c at hc h
    generalize cs[i.val] = x at hc
    have e58 := u32_eq_char hc (n := 58#u32) (y := ':') rfl
    obtain ⟨⟨out1, cur1⟩, hif, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hv : i2.val = i.val + 1 := by have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
    have := ih _ (by omega) i2 out1 cur1 rfl (by omega) h
    rw [hv] at this
    rw [this]
    by_cases h1 : c = 58#u32
    · rw [ite_eq_left h1] at hif
      rw [ite_eq_left (by simpa using e58.mp h1)]
      obtain ⟨out2, hout2, hif⟩ := ConRon.Refine.bind_eq_ok_iff.mp hif
      simp only [Result.ok.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl⟩ := hif
      rw [show absString (alloc.vec.Vec.new Std.U32) = "" from rfl, String.toList_empty,
        List.reverse_nil, List.splitOnPPrepend_nil_right]
      simp only [List.reverse_reverse, String.ofList_toList,
        List.map_cons, List.filter_cons, absString_ne]
      by_cases h0 : cur.val = []
      · have hn : ¬ alloc.vec.Vec.len cur > 0#usize := fun h' => (len_pos cur).mp h' h0
        rw [ite_eq_right hn] at hout2
        cases Result.ok_injective hout2
        simp [h0]
      · rw [ite_eq_left ((len_pos cur).mpr h0)] at hout2
        rw [ConRon.Refine.vec_push_val hout2]
        simp [h0]
    · rw [ite_eq_right h1] at hif
      rw [ite_eq_right (by simpa using fun h' => h1 (e58.mpr h'))]
      obtain ⟨cur2, hcur2, hif⟩ := ConRon.Refine.bind_eq_ok_iff.mp hif
      simp only [Result.ok.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl⟩ := hif
      rw [absString_push hc hcur2]
      simp
  · have hge : ¬ i < alloc.vec.Vec.len v := by scalar_tac
    rw [ite_eq_right hge] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega), List.splitOnPPrepend_nil]
    simp only [List.reverse_reverse, String.ofList_toList, List.map_cons, List.map_nil,
      List.filter_cons, List.filter_nil, absString_ne]
    by_cases h0 : cur.val = [] <;> simp [h0]

end ConRon.Args

namespace ConRon.Args

/-- The twin's scan state of the Rust's. -/
def absScan : frontend.olean.files.NameScan → ConLeche.Frontend.Olean.NameScan
  | .Start => .start
  | .Plain => .plain
  | .Esc => .esc
  | .Closed => .closed



theorem absString_new : absString (alloc.vec.Vec.new Std.U32) = "" := rfl



end ConRon.Args

namespace ConRon.Args
open ConLeche.Frontend.Olean (scanName)

theorem char_valid (x : Char) : Nat.isValidChar x.toNat := x.valid



theorem strwf_push {v w : alloc.vec.Vec Std.U32} {c : Std.U32} {x : Char} (hx : c.val = x.toNat)
    (hv : StrWF v) (h : alloc.vec.Vec.push v c = ok w) : StrWF w := by
  intro d hd
  rw [ConRon.Refine.vec_push_val h] at hd
  rcases List.mem_append.mp hd with hd | hd
  · exact hv d hd
  · simp at hd; subst hd; rw [hx]; exact char_valid x

theorem strwf_new : StrWF (alloc.vec.Vec.new Std.U32) := by intro d hd; simp at hd

theorem scan_loop {cs : List Char} {s : alloc.vec.Vec Std.U32}
    (hs : s.val.map UScalar.val = cs.map Char.toNat) :
    ∀ (k : Nat) (i : Std.Usize) n st cur, s.val.length - i.val = k → i.val ≤ s.val.length →
      NameWF n → StrWF cur → ∀ r,
      frontend.olean.files.scan_name_go_loop false s n st cur i = ok (some r) →
      NameWF r.1 ∧ StrWF r.2.2 ∧
      scanName false (cs.drop i.val) (absName n) (absScan st) (absString cur) =
        scanName false [] (absName r.1) (absScan r.2.1) (absString r.2.2) := by
  have hlen : s.val.length = cs.length := by
    have := congrArg List.length hs; simpa using this
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro i n st cur hk hi hn hcur r h
  rw [frontend.olean.files.scan_name_go_loop] at h
  by_cases hlt : i.val < s.val.length
  · have hlt' : i < alloc.vec.Vec.len s := by scalar_tac
    rw [ite_eq_left hlt'] at h
    rw [vec_index_ok' hlt, bind_ok] at h
    have hic : i.val < cs.length := by omega
    have hc : (s.val[i.val]).val = (cs[i.val]).toNat := by
      have := congrArg (fun l => l[i.val]?) hs
      simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hic,
        Option.map_some, Option.some.injEq] at this
      exact this
    have hdrop : cs.drop i.val = cs[i.val] :: cs.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hic]
    rw [hdrop]
    generalize s.val[i.val] = c at hc h
    generalize cs[i.val] = x at hc
    have e171 := u32_eq_char hc (n := 171#u32) (y := '«') rfl
    have e46 := u32_eq_char hc (n := 46#u32) (y := '.') rfl
    have e187 := u32_eq_char hc (n := 187#u32) (y := '»') rfl
    have hnext : ∀ {i2 : Std.Usize}, i + 1#usize = ok i2 → i2.val = i.val + 1 ∧
        s.val.length - i2.val < k ∧ i2.val ≤ s.val.length := by
      intro i2 h2
      have := ConRon.Refine.Nat.uadd_val h2
      simp at this
      omega
    cases st with
    | Start =>
      simp only [absScan, scanName]
      dsimp only at h
      by_cases h1 : c = 171#u32
      · rw [ite_eq_left h1] at h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hv, hk2, hle⟩ := hnext hi2
        rw [ite_eq_left (by simpa using e171.mp h1)]
        have := ih _ (hk ▸ hk2) i2 n _ _ rfl hle hn strwf_new r h
        rw [hv, absString_new] at this
        simpa only [absScan] using this
      · rw [ite_eq_right h1] at h
        rw [ite_eq_right (by simpa using fun h' => h1 (e171.mpr h'))]
        by_cases h2 : c = 46#u32
        · rw [ite_eq_left h2] at h; simp at h
        · rw [ite_eq_right h2] at h
          rw [ite_eq_right (by simpa using fun h' => h2 (e46.mpr h'))]
          obtain ⟨cur1, hcur1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hv, hk2, hle⟩ := hnext hi2
          have := ih _ (hk ▸ hk2) i2 n _ _ rfl hle hn (strwf_push hc strwf_new hcur1) r h
          rw [hv, absString_push hc hcur1, absString_new] at this
          simpa [absScan] using this
    | Plain =>
      simp only [absScan, scanName]
      dsimp only at h
      obtain ⟨⟨n1, st1, cur1⟩, hif, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hv, hk2, hle⟩ := hnext hi2
      by_cases h1 : c = 46#u32
      · rw [ite_eq_left h1] at hif
        simp only [core.mem.replace, frontend.olean.files.name_push_plain, Bool.false_eq_true,
          ite_false] at hif
        obtain ⟨n2, hn2, hif⟩ := ConRon.Refine.bind_eq_ok_iff.mp hif
        simp only [Result.ok.injEq, Prod.mk.injEq] at hif
        obtain ⟨rfl, rfl, rfl⟩ := hif
        rw [ite_eq_left (by simpa using e46.mp h1)]
        have := ih _ (hk ▸ hk2) i2 n2 _ _ rfl hle (ConRon.Refine.NameWF.str hn hcur hn2) strwf_new r h
        rw [hv, ConRon.Refine.Name.mk_str_refines hn2, absString_new] at this
        simpa [ConLeche.Frontend.Olean.Name.pushPlain, absScan] using this
      · rw [ite_eq_right h1] at hif
        obtain ⟨cur2, hcur2, hif⟩ := ConRon.Refine.bind_eq_ok_iff.mp hif
        simp only [Result.ok.injEq, Prod.mk.injEq] at hif
        obtain ⟨rfl, rfl, rfl⟩ := hif
        rw [ite_eq_right (by simpa using fun h' => h1 (e46.mpr h'))]
        have := ih _ (hk ▸ hk2) i2 n _ _ rfl hle hn (strwf_push hc hcur hcur2) r h
        rw [hv, absString_push hc hcur2] at this
        simpa only [absScan] using this
    | Esc =>
      simp only [absScan, scanName]
      dsimp only at h
      by_cases h1 : c = 187#u32
      · rw [ite_eq_left h1] at h
        rw [ite_eq_left (by simpa using e187.mp h1)]
        by_cases h0 : alloc.vec.Vec.len cur = 0#usize
        · rw [ite_eq_left h0] at h; simp at h
        · rw [ite_eq_right h0] at h
          simp only [core.mem.replace] at h
          obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hv, hk2, hle⟩ := hnext hi2
          have hne : (absString cur).isEmpty = false := by
            have : cur.val ≠ [] := by
              intro he; apply h0; have := alloc.vec.Vec.len_val cur
              simp [alloc.vec.Vec.length, he] at this; scalar_tac
            simp [absString, this]
          rw [hne]
          have := ih _ (hk ▸ hk2) i2 n1 _ _ rfl hle (ConRon.Refine.NameWF.str hn hcur hn1) strwf_new r h
          rw [hv, ConRon.Refine.Name.mk_str_refines hn1, absString_new] at this
          simpa [absScan] using this
      · rw [ite_eq_right h1] at h
        rw [ite_eq_right (by simpa using fun h' => h1 (e187.mpr h'))]
        obtain ⟨cur1, hcur1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hv, hk2, hle⟩ := hnext hi2
        have := ih _ (hk ▸ hk2) i2 n _ _ rfl hle hn (strwf_push hc hcur hcur1) r h
        rw [hv, absString_push hc hcur1] at this
        simpa only [absScan] using this
    | Closed =>
      simp only [absScan, scanName]
      dsimp only at h
      by_cases h1 : c = 46#u32
      · rw [ite_eq_left h1] at h
        rw [ite_eq_left (by simpa using e46.mp h1)]
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hv, hk2, hle⟩ := hnext hi2
        have := ih _ (hk ▸ hk2) i2 n _ _ rfl hle hn strwf_new r h
        rw [hv, absString_new] at this
        simpa only [absScan] using this
      · rw [ite_eq_right h1] at h; simp at h
  · have hge : ¬ i < alloc.vec.Vec.len s := by scalar_tac
    rw [ite_eq_right hge] at h
    cases Result.ok_injective h
    refine ⟨hn, hcur, ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]

/-- **A module name the Rust parses is the one `parseModName` reads**, well formed. -/
theorem parse_mod_name_some {root : String} {f : alloc.vec.Vec Std.U32}
    (hf : f.val.map UScalar.val = root.toList.map Char.toNat) {nm : kernel.name.Name}
    (h : frontend.olean.files.parse_mod_name f = ok (some nm)) :
    NameWF nm ∧ ConLeche.Frontend.Olean.parseModName root = some (absName nm) := by
  simp only [frontend.olean.files.parse_mod_name, frontend.olean.files.scan_name,
    frontend.olean.files.scan_name_go] at h
  obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n0, hn0, ho⟩ := ConRon.Refine.bind_eq_ok_iff.mp ho
  have hwf0 := ConRon.Refine.Name.anonymous_wf hn0
  have hab0 := ConRon.Refine.Name.anonymous_refines hn0
  cases o with
  | none => simp at h
  | some r =>
    obtain ⟨n', st', cur'⟩ := r
    obtain ⟨hw, hc, he⟩ := scan_loop hf _ 0#usize n0 _ _ rfl (by simp) hwf0 strwf_new _ ho
    simp only [List.drop_zero, show (0#usize : Std.Usize).val = 0 from rfl, hab0, absString_new,
      absScan] at he
    unfold ConLeche.Frontend.Olean.parseModName
    rw [he]
    dsimp only at h
    cases st' with
    | Start => simp at h
    | Esc => simp at h
    | Closed =>
      have h' : ok (some n') = ok (some nm) := h
      simp only [Result.ok.injEq, Option.some.injEq] at h'
      subst h'

      exact ⟨hw, rfl⟩
    | Plain =>
      have h' : frontend.olean.files.name_push_plain n' cur' false >>= (fun n1 => ok (some n1)) = ok (some nm) := h
      simp only [frontend.olean.files.name_push_plain, Bool.false_eq_true, ite_false] at h'
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h'
      simp only [Result.ok.injEq, Option.some.injEq] at h
      subst h
      refine ⟨ConRon.Refine.NameWF.str hw hc hn1, ?_⟩
      simp [ConLeche.Frontend.Olean.scanName, ConLeche.Frontend.Olean.Name.pushPlain,
        ConRon.Refine.Name.mk_str_refines hn1]

end ConRon.Args

namespace ConRon.Args

/-- **`--search-path=` + `dirs`, as the Rust reads it, is `searchPathOf dirs`**: the nonempty
`:`-separated directories. -/
theorem push_dirs_search {dirs : String} {v : alloc.vec.Vec Std.U32}
    (hs : v.val.map UScalar.val = ("--search-path=" ++ dirs).toList.map Char.toNat)
    {r : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    (h : driver.cli.push_dirs (alloc.vec.Vec.new _) v 14#usize = ok r) :
    r.val.map (fun d => (⟨absString d⟩ : System.FilePath)) = ConLeche.Driver.searchPathOf dirs := by
  rw [driver.cli.push_dirs] at h
  obtain ⟨⟨out1, cur⟩, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hlen : 14 ≤ v.val.length := by
    have := congrArg List.length hs
    simp only [List.length_map, String.toList_append, List.length_append] at this
    rw [this]
    exact Nat.le_add_right _ _
  have key := push_dirs_loop_val hs _ 14#usize _ _ rfl (by simpa using hlen) hl
  replace h : (if alloc.vec.Vec.len cur > 0#usize then alloc.vec.Vec.push out1 cur else ok out1) = ok r := h
  have hr : r.val = out1.val ++ (if cur.val = [] then [] else [cur]) := by
    by_cases h0 : cur.val = []
    · rw [ite_eq_right (fun h' => (len_pos cur).mp h' h0)] at h
      cases Result.ok_injective h; simp [h0]
    · rw [ite_eq_left ((len_pos cur).mpr h0)] at h
      rw [ConRon.Refine.vec_push_val h]; simp [h0]
  have hdrop : (("--search-path=" ++ dirs).toList).drop 14 = dirs.toList := by
    simp [String.toList_append]
  simp only [show (14#usize : Std.Usize).val = 14 from rfl, hdrop, absString_new,
    String.toList_empty, List.reverse_nil] at key
  simp only [ConLeche.Driver.searchPathOf]
  rw [hr, show (":" : String) = String.singleton ':' from rfl, splitOn_one]
  have : List.map (fun d => (⟨absString d⟩ : System.FilePath)) (out1.val ++ (if cur.val = [] then [] else [cur]))
      = ((out1.val ++ (if cur.val = [] then [] else [cur])).map absString).map System.FilePath.mk := by
    rw [List.map_map]; rfl
  rw [this, key, List.splitOn, List.splitOnPPrepend_nil_right]
  rfl

end ConRon.Args

namespace ConRon.Args

theorem vec_index_ok'' {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (hi : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok v.val[i.val] := by
  simp only [alloc.vec.Vec.index_slice_index]
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hi)
  rw [hy, hyv]

/-- `cps_beq` answers, and its answer is list equality. -/
theorem cps_beq_eq (s : alloc.vec.Vec Std.U32) (lit : Slice Std.U32) :
    frontend.text.cps_beq s lit = ok (s.val == lit.val) := by
  rw [frontend.text.cps_beq]
  split
  · rename_i hne
    have hl : s.val.length ≠ lit.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hne
    have : (s.val == lit.val) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact hl (congrArg List.length h)
    rw [this]
  · rename_i hne
    have hl : s.val.length = lit.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hne
    suffices ∀ (N : Nat) (i : Std.Usize), s.val.length - i.val = N → i.val ≤ s.val.length →
        frontend.text.cps_beq_loop s lit (alloc.vec.Vec.len s) i =
          ok (s.val.drop i.val == lit.val.drop i.val) by
      simpa using this _ 0#usize rfl (by simp)
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro i hN hi
    rw [frontend.text.cps_beq_loop]
    by_cases hlt : i.val < s.val.length
    · have hlt' : i < alloc.vec.Vec.len s := by scalar_tac
      rw [ite_eq_left hlt']
      have hl2 : i.val < lit.val.length := by omega
      rw [ConRon.Args.vec_index_ok'' hlt, bind_ok]
      obtain ⟨c2, hc2⟩ : ∃ c2, Slice.index_usize lit i = ok c2 ∧ c2 = lit.val[i.val] := by
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Slice.index_usize_spec lit i hl2)
        exact ⟨y, hy, hyv⟩
      rw [hc2.1, bind_ok, hc2.2, List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hl2,
        List.cons_beq_cons]
      by_cases he : s.val[i.val] = lit.val[i.val]
      · rw [he]; simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, beq_self_eq_true,
          Bool.true_and]
        obtain ⟨i3, hi3⟩ : ∃ i3 : Std.Usize, i + 1#usize = ok i3 ∧ i3.val = i.val + 1 := by
          obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
            (Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
          exact ⟨y, hy, by simpa using hyv⟩
        rw [hi3.1, bind_ok, ih _ (by omega) i3 rfl (by omega), hi3.2]
      · have : (s.val[i.val] != lit.val[i.val]) = true := by simpa using he
        rw [ite_eq_left this]
        simp [he]
    · have hge : ¬ i < alloc.vec.Vec.len s := by scalar_tac
      rw [ite_eq_right hge, List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
      rfl

/-- `cps_starts_with` answers, and its answer is the prefix test. -/
theorem cps_starts_with_eq (s : alloc.vec.Vec Std.U32) (lit : Slice Std.U32) :
    frontend.text.cps_starts_with s lit = ok (s.val.take lit.val.length == lit.val) := by
  rw [frontend.text.cps_starts_with]
  split
  · rename_i hne
    have hl : s.val.length < lit.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hne
    have : (s.val.take lit.val.length == lit.val) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have := congrArg List.length h; simp at this; omega
    rw [this]
  · rename_i hne
    have hl : lit.val.length ≤ s.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hne
    have hn : (Slice.len lit).val = lit.val.length := by simp [Slice.len]
    suffices ∀ (N : Nat) (i : Std.Usize), lit.val.length - i.val = N → i.val ≤ lit.val.length →
        frontend.text.cps_starts_with_loop s lit (Slice.len lit) i =
          ok ((s.val.take lit.val.length).drop i.val == lit.val.drop i.val) by
      simpa using this _ 0#usize rfl (by simp)
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro i hN hi
    rw [frontend.text.cps_starts_with_loop]
    by_cases hlt : i.val < lit.val.length
    · have hlt' : i < Slice.len lit := by scalar_tac
      rw [ite_eq_left hlt']
      have hl1 : i.val < s.val.length := by omega
      rw [vec_index_ok'' hl1, bind_ok]
      obtain ⟨c2, hc2⟩ : ∃ c2, Slice.index_usize lit i = ok c2 ∧ c2 = lit.val[i.val] := by
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Slice.index_usize_spec lit i hlt)
        exact ⟨y, hy, hyv⟩
      have htl : i.val < (s.val.take lit.val.length).length := by simp; omega
      rw [hc2.1, bind_ok, hc2.2, List.drop_eq_getElem_cons htl, List.drop_eq_getElem_cons hlt,
        List.cons_beq_cons, List.getElem_take]
      by_cases he : s.val[i.val] = lit.val[i.val]
      · rw [he]; simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, beq_self_eq_true,
          Bool.true_and]
        obtain ⟨i3, hi3⟩ : ∃ i3 : Std.Usize, i + 1#usize = ok i3 ∧ i3.val = i.val + 1 := by
          obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
            (Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
          exact ⟨y, hy, by simpa using hyv⟩
        rw [hi3.1, bind_ok, ih _ (by omega) i3 rfl (by omega), hi3.2]
      · have : (s.val[i.val] != lit.val[i.val]) = true := by simpa using he
        rw [ite_eq_left this]
        simp [he]
    · have hge : ¬ i < Slice.len lit := by scalar_tac
      rw [ite_eq_right hge, List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by omega)]
      rfl

/-! ### The words the parser compares -/

theorem w_end_val : (Array.to_slice driver.cli.W_END).val = [45#u32, 45#u32] := by
  simp [driver.cli.W_END, Array.to_slice]

theorem w_help_val : (Array.to_slice driver.cli.W_HELP).val = [45#u32, 45#u32, 104#u32, 101#u32, 108#u32, 112#u32] := by
  simp [driver.cli.W_HELP, Array.to_slice]

theorem w_verified_val : (Array.to_slice driver.cli.W_VERIFIED).val = [45#u32, 45#u32, 118#u32, 101#u32, 114#u32, 105#u32, 102#u32, 105#u32, 101#u32, 100#u32] := by
  simp [driver.cli.W_VERIFIED, Array.to_slice]

theorem w_trusted_val : (Array.to_slice driver.cli.W_TRUSTED).val = [45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32] := by
  simp [driver.cli.W_TRUSTED, Array.to_slice]

theorem w_progress_val : (Array.to_slice driver.cli.W_PROGRESS).val = [45#u32, 45#u32, 112#u32, 114#u32, 111#u32, 103#u32, 114#u32, 101#u32, 115#u32, 115#u32] := by
  simp [driver.cli.W_PROGRESS, Array.to_slice]

theorem w_olean_val : (Array.to_slice driver.cli.W_OLEAN).val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32] := by
  simp [driver.cli.W_OLEAN, Array.to_slice]

theorem w_check_graph_val : (Array.to_slice driver.cli.W_CHECK_GRAPH).val = [45#u32, 45#u32, 99#u32, 104#u32, 101#u32, 99#u32, 107#u32, 45#u32, 103#u32, 114#u32, 97#u32, 112#u32, 104#u32] := by
  simp [driver.cli.W_CHECK_GRAPH, Array.to_slice]

theorem w_module_val : (Array.to_slice driver.cli.W_MODULE).val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 101#u32] := by
  simp [driver.cli.W_MODULE, Array.to_slice]

theorem w_modular_val : (Array.to_slice driver.cli.W_MODULAR).val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 97#u32, 114#u32] := by
  simp [driver.cli.W_MODULAR, Array.to_slice]

theorem w_compare_val : (Array.to_slice driver.cli.W_COMPARE).val = [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32] := by
  simp [driver.cli.W_COMPARE, Array.to_slice]

theorem w_jobs_val : (Array.to_slice driver.cli.W_JOBS).val = [45#u32, 45#u32, 106#u32, 111#u32, 98#u32, 115#u32] := by
  simp [driver.cli.W_JOBS, Array.to_slice]

theorem w_progress_eq_val : (Array.to_slice driver.cli.W_PROGRESS_EQ).val = [45#u32, 45#u32, 112#u32, 114#u32, 111#u32, 103#u32, 114#u32, 101#u32, 115#u32, 115#u32, 61#u32] := by
  simp [driver.cli.W_PROGRESS_EQ, Array.to_slice]

theorem w_jobs_eq_val : (Array.to_slice driver.cli.W_JOBS_EQ).val = [45#u32, 45#u32, 106#u32, 111#u32, 98#u32, 115#u32, 61#u32] := by
  simp [driver.cli.W_JOBS_EQ, Array.to_slice]

theorem w_max_nat_size_eq_val : (Array.to_slice driver.cli.W_MAX_NAT_SIZE_EQ).val = [45#u32, 45#u32, 109#u32, 97#u32, 120#u32, 45#u32, 110#u32, 97#u32, 116#u32, 45#u32, 115#u32, 105#u32, 122#u32, 101#u32, 61#u32] := by
  simp [driver.cli.W_MAX_NAT_SIZE_EQ, Array.to_slice]

theorem w_constant_eq_val : (Array.to_slice driver.cli.W_CONSTANT_EQ).val = [45#u32, 45#u32, 99#u32, 111#u32, 110#u32, 115#u32, 116#u32, 97#u32, 110#u32, 116#u32, 61#u32] := by
  simp [driver.cli.W_CONSTANT_EQ, Array.to_slice]

theorem w_search_path_eq_val : (Array.to_slice driver.cli.W_SEARCH_PATH_EQ).val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] := by
  simp [driver.cli.W_SEARCH_PATH_EQ, Array.to_slice]

theorem w_trusted_search_path_eq_val : (Array.to_slice driver.cli.W_TRUSTED_SEARCH_PATH_EQ).val = [45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] := by
  simp [driver.cli.W_TRUSTED_SEARCH_PATH_EQ, Array.to_slice]

theorem w_schedule_val : (Array.to_slice driver.cli.W_SCHEDULE).val = [45#u32, 45#u32, 115#u32, 99#u32, 104#u32, 101#u32, 100#u32, 117#u32, 108#u32, 101#u32] := by
  simp [driver.cli.W_SCHEDULE, Array.to_slice]

theorem w_worker_stack_size_eq_val : (Array.to_slice driver.cli.W_WORKER_STACK_SIZE_EQ).val = [45#u32, 45#u32, 119#u32, 111#u32, 114#u32, 107#u32, 101#u32, 114#u32, 45#u32, 115#u32, 116#u32, 97#u32, 99#u32, 107#u32, 45#u32, 115#u32, 105#u32, 122#u32, 101#u32, 61#u32] := by
  simp [driver.cli.W_WORKER_STACK_SIZE_EQ, Array.to_slice]

macro "parse_one_word" hs:term "," hv:term : tactic => `(tactic| (
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp $hs
  rw [driver.cli.parse_one, ConRon.Args.vec_index_ok'' hi, hx]
  simp only [bind_ok, lift, ConRon.Args.cps_beq_eq, $hv:term, w_end_val, w_help_val, w_verified_val, w_trusted_val, w_progress_val, w_olean_val, w_check_graph_val, w_module_val, w_modular_val, w_compare_val, w_jobs_val, w_progress_eq_val, w_jobs_eq_val, w_max_nat_size_eq_val, w_constant_eq_val, w_search_path_eq_val, w_trusted_search_path_eq_val, w_schedule_val, w_worker_stack_size_eq_val]
  simp (config := { decide := true }) only [ite_true, ite_false]))

variable {a : driver.cli.Args} {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {i : Std.Usize}
  {s : alloc.vec.Vec Std.U32}

theorem parse_one_olean (hs : argv.val[i.val]? = some s)
    (hv : s.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32]) :
    driver.cli.parse_one a argv i = ok { a with olean := true } := by
  parse_one_word hs, hv

theorem parse_one_module (hs : argv.val[i.val]? = some s)
    (hv : s.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 101#u32]) :
    driver.cli.parse_one a argv i = ok { a with module := true } := by
  parse_one_word hs, hv

theorem parse_one_modular (hs : argv.val[i.val]? = some s)
    (hv : s.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 97#u32, 114#u32]) :
    driver.cli.parse_one a argv i = ok { a with modular := true } := by
  parse_one_word hs, hv

theorem parse_one_check_graph (hs : argv.val[i.val]? = some s)
    (hv : s.val = [45#u32, 45#u32, 99#u32, 104#u32, 101#u32, 99#u32, 107#u32, 45#u32, 103#u32,
      114#u32, 97#u32, 112#u32, 104#u32]) :
    driver.cli.parse_one a argv i = ok { a with check_graph := true } := by
  parse_one_word hs, hv

/-- **`--search-path=DIRS`**: the directories, after the ones before. -/
theorem parse_one_search {T : List Std.U32} (hs : argv.val[i.val]? = some s)
    (hv : s.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32,
      112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ T) :
    driver.cli.parse_one a argv i = (do
      let v ← driver.cli.push_dirs a.search_path s 14#usize
      ok { a with search_path := v }) := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hs
  rw [driver.cli.parse_one, ConRon.Args.vec_index_ok'' hi, hx]
  simp only [bind_ok, lift, ConRon.Args.cps_beq_eq, hv, w_verified_val, w_trusted_val, w_progress_val, w_olean_val, w_check_graph_val, w_module_val, w_modular_val, w_compare_val, w_jobs_val, w_progress_eq_val, w_jobs_eq_val, w_max_nat_size_eq_val, w_constant_eq_val, w_search_path_eq_val, w_trusted_search_path_eq_val, w_schedule_val, w_worker_stack_size_eq_val, driver.cli.parse_valued,
    ConRon.Args.cps_starts_with_eq, List.cons_append, List.cons_beq_cons, List.take_succ_cons,
    List.length_cons, List.length_nil]
  simp

/-- **A word that is not `--`**: the loop goes on after `parse_one`'s answer. -/
theorem loop_word {a' : driver.cli.Args} (hs : argv.val[i.val]? = some s)
    (hne : s.val ≠ [45#u32, 45#u32]) {i2 : Std.Usize}
    (h1 : driver.cli.parse_one a argv i = ok a') (hi2 : i + 1#usize = ok i2) :
    driver.cli.parse_args_loop argv a i = driver.cli.parse_args_loop argv a' i2 := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hs
  rw [driver.cli.parse_args_loop]
  have hlt : ¬ i >= alloc.vec.Vec.len argv := by scalar_tac
  rw [ite_eq_right hlt, ConRon.Args.vec_index_ok'' hi, hx]
  simp only [bind_ok, lift, ConRon.Args.cps_beq_eq, w_end_val]
  have : (s.val == [45#u32, 45#u32]) = false := by simpa using hne
  rw [this]
  simp only [Bool.false_eq_true, ite_false, h1, bind_ok, hi2]

/-- **`--`**: every argument after it is a file. -/
theorem loop_end (hs : argv.val[i.val]? = some s) (hv : s.val = [45#u32, 45#u32]) {i2 : Std.Usize}
    (hi2 : i + 1#usize = ok i2) :
    driver.cli.parse_args_loop argv a i = (do
      let v1 ← driver.cli.push_files a.files argv i2
      driver.cli.closed { a with files := v1 }) := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hs
  rw [driver.cli.parse_args_loop]
  have hlt : ¬ i >= alloc.vec.Vec.len argv := by scalar_tac
  rw [ite_eq_right hlt, ConRon.Args.vec_index_ok'' hi, hx]
  simp only [bind_ok, lift, ConRon.Args.cps_beq_eq, w_end_val, hv, beq_self_eq_true, ite_true, hi2]

/-- `--help` is not before a word that is neither `--` nor `--help`. -/
theorem help_word (hs : argv.val[i.val]? = some s) (hne : s.val ≠ [45#u32, 45#u32])
    (hnh : s.val ≠ [45#u32, 45#u32, 104#u32, 101#u32, 108#u32, 112#u32]) {i2 : Std.Usize}
    (hi2 : i + 1#usize = ok i2) :
    driver.cli.help_wanted_loop argv i = driver.cli.help_wanted_loop argv i2 := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hs
  rw [driver.cli.help_wanted_loop]
  have hlt : ¬ i >= alloc.vec.Vec.len argv := by scalar_tac
  rw [ite_eq_right hlt, ConRon.Args.vec_index_ok'' hi, hx]
  have h1 : (s.val == [45#u32, 45#u32]) = false := by simpa using hne
  have h2 : (s.val == [45#u32, 45#u32, 104#u32, 101#u32, 108#u32, 112#u32]) = false := by
    simpa using hnh
  simp only [bind_ok, lift, ConRon.Args.cps_beq_eq, w_end_val, w_help_val, h1, h2,
    Bool.false_eq_true, ite_false, hi2]

/-- **`--`**: no `--help` after it counts. -/
theorem help_end (hs : argv.val[i.val]? = some s) (hv : s.val = [45#u32, 45#u32]) :
    driver.cli.help_wanted_loop argv i = ok false := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hs
  rw [driver.cli.help_wanted_loop]
  have hlt : ¬ i >= alloc.vec.Vec.len argv := by scalar_tac
  rw [ite_eq_right hlt, ConRon.Args.vec_index_ok'' hi, hx]
  simp only [bind_ok, lift, ConRon.Args.cps_beq_eq, w_end_val, hv, beq_self_eq_true, ite_true]

/-- **`--search-path=DIRS` in the loop**: the directories pushed, then the loop goes on. -/
theorem loop_search {T : List Std.U32} (hs : argv.val[i.val]? = some s)
    (hv : s.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32,
      112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ T) {i2 : Std.Usize}
    (hi2 : i + 1#usize = ok i2) :
    driver.cli.parse_args_loop argv a i = (do
      let v ← driver.cli.push_dirs a.search_path s 14#usize
      driver.cli.parse_args_loop argv { a with search_path := v } i2) := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hs
  rw [driver.cli.parse_args_loop]
  have hlt : ¬ i >= alloc.vec.Vec.len argv := by scalar_tac
  rw [ite_eq_right hlt, ConRon.Args.vec_index_ok'' hi, hx]
  have hne : (s.val == [45#u32, 45#u32]) = false := by rw [hv]; simp
  simp only [bind_ok, lift, ConRon.Args.cps_beq_eq, w_end_val, hne, Bool.false_eq_true, ite_false,
    parse_one_search hs hv]
  cases driver.cli.push_dirs a.search_path s 14#usize <;> simp [hi2]

end ConRon.Args
