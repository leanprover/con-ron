/-
# `ConRon.Refine2.Frontend.Olean.Files` — where a module's files are

**Task #142, Theorem 2.**  `olean/files.rs`'s search against the twin's `locateIn`,
`locateHits`, `findModule`, and `locate_of` against upstream's `locateOf`.  A function that
reaches a file read claims its accept (`FsRel`); `locate_of` reads no file and claims both
outcomes, a failure at kind `internal` against the twin's.

The tests `file_twice`, `file_twice_at`, `file_at_differs`, `file_differs_from`, `file_other`
carry no theorem: they choose between two messages of one failure, and a message is not
compared.
-/
import ConRon.Refine2.Frontend.Olean.ModFilesRel
import ConRon.Refine2.Frontend.Olean.Region
import ConRon.Refine2.Frontend.Olean.Contract

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.files
open frontend.olean.region (part_of_bytes)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Refine (absString absName StrWF NameWF vec_push_val)
open ConRon.Refine2.Lockstep (LSP)
open ConRon.Refine2 (AErrKind absAErrKind)
open ConLeche.Frontend.Olean (locateOf partExts)
open Arena.Frontend.Olean (locateIn locateHits findModule)

/-! ## The relations -/

theorem vec_len_val {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.len v).val = v.val.length := by
  simp


/-- A file of a directory, as the twin's. -/
abbrev absFile (o : Option (alloc.vec.Vec Std.U32)) : Option String := o.map absString

/-- One directory's answer, as the twin's. -/
def absHit (h : Hit) : System.FilePath × List (Option String) :=
  (⟨absString h.dir⟩, h.files.val.map absFile)

/-- A list of files whose strings are code points. -/
def FilesWF (l : List (Option (alloc.vec.Vec Std.U32))) : Prop :=
  ∀ x ∈ l, ∀ s, x = some s → StrWF s

/-- What `locate_in` leaves true of a hit: its three files, as code points. -/
structure HitWF (h : Hit) : Prop where
  three : h.files.val.length = 3
  wf : FilesWF h.files.val

/-- A location, as upstream's. -/
def absLocated (l : Located) : ConLeche.Frontend.Olean.Located :=
  ⟨⟨absString l.dir⟩, l.has_server, l.has_private⟩

/-! ## `file_some`, `hit_holds_any`, `hits_add` -/

theorem file_some_eq {o : Option (alloc.vec.Vec Std.U32)} {b : Bool} (h : file_some o = ok b) :
    b = (absFile o).isSome := by
  cases o <;> exact (Result.ok_injective h).symm

theorem hit_holds_any_loop_eq (h : Hit) (i : Std.Usize) {b : Bool}
    (hr : hit_holds_any_loop h i = ok b) :
    b = ((h.files.val.drop i.val).map absFile).any (·.isSome) := by
  rw [hit_holds_any_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len h.files
  · rw [ite_eq_left hlt] at hr
    peel hr as o, ho
    obtain ⟨hi, rfl⟩ := vec_index_eq ho
    peel hr as c, hc
    have ec := file_some_eq hc
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.any_cons, ← ec]
    by_cases hb : c = true
    · rw [ite_eq_left hb] at hr
      cases Result.ok_injective hr
      simp [hb]
    · rw [ite_eq_right hb] at hr
      peel hr as i2, hi2
      have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
      have := hit_holds_any_loop_eq h i2 hr
      rw [hi2v] at this
      rw [this]; simp [hb]
  · rw [ite_eq_right hlt] at hr
    cases Result.ok_injective hr
    have : h.files.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len h.files).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le this]; rfl
termination_by h.files.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len h.files).val := hlt
  rw [vec_len_val] at this
  omega

/-- **`hit_holds_any` is `h.2.any (·.isSome)`.** -/
theorem hit_holds_any_eq {h : Hit} {b : Bool} (hr : hit_holds_any h = ok b) :
    b = (absHit h).2.any (·.isSome) := by
  rw [hit_holds_any] at hr
  simpa [absHit] using hit_holds_any_loop_eq h _ hr

/-- **`hits_add` is one element of the twin's `filter`.** -/
theorem hits_add_eq {out out' : alloc.vec.Vec Hit} {h : Hit} (hr : hits_add out h = ok out') :
    out'.val.map absHit = out.val.map absHit ++
      [absHit h].filter fun h => h.2.any (·.isSome) := by
  rw [hits_add] at hr
  peel hr as b, hb
  have eb := hit_holds_any_eq hb
  by_cases hc : b = true
  · rw [ite_eq_left hc] at hr
    have e2 : (absHit h).2.any (·.isSome) = true := by rw [← eb]; exact hc
    simp [vec_push_val hr, e2]
  · rw [ite_eq_right hc] at hr
    cases Result.ok_injective hr
    have e2 : (absHit h).2.any (·.isSome) = false := by rw [← eb]; simpa using hc
    simp [e2]

/-! ## The comparisons -/

/-- **`file_opt_eq` is `Option String`'s `==`**, on code points. -/
theorem file_opt_eq_eq {a b : Option (alloc.vec.Vec Std.U32)} {c : Bool}
    (ha : ∀ s, a = some s → StrWF s) (hb : ∀ s, b = some s → StrWF s)
    (h : file_opt_eq a b = ok c) : c = decide (absFile a = absFile b) := by
  cases a with
  | none =>
    cases b with
    | none => cases Result.ok_injective h; rfl
    | some y => cases Result.ok_injective h; rfl
  | some x =>
    cases b with
    | none => cases Result.ok_injective h; rfl
    | some y =>
      have := ConRon.Refine.Name.str_eq_refines (ha x rfl) (hb y rfl) h
      rw [this]
      simp [absFile]

theorem file_lists_eq_loop_eq (a b : alloc.vec.Vec (Option (alloc.vec.Vec Std.U32))) (i : Std.Usize)
    {c : Bool} (ha : FilesWF a.val) (hb : FilesWF b.val) (hl : a.val.length = b.val.length)
    (h : file_lists_eq_loop a b i = ok c) :
    c = decide ((a.val.drop i.val).map absFile = (b.val.drop i.val).map absFile) := by
  rw [file_lists_eq_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len a
  · rw [ite_eq_left hlt] at h
    peel h as x, hx
    obtain ⟨hi, rfl⟩ := vec_index_eq hx
    peel h as y, hy
    obtain ⟨hj, rfl⟩ := vec_index_eq hy
    peel h as e, he
    have ee := file_opt_eq_eq (ha _ (List.getElem_mem hi)) (hb _ (List.getElem_mem hj)) he
    rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj, List.map_cons, List.map_cons]
    by_cases hc : e = true
    · rw [ite_eq_left hc] at h
      peel h as i2, hi2
      have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
      have := file_lists_eq_loop_eq a b i2 ha hb hl h
      rw [hi2v] at this
      rw [this]
      have : absFile a.val[i.val] = absFile b.val[i.val] := by
        rw [hc] at ee; exact of_decide_eq_true ee.symm
      simp [this]
    · rw [ite_eq_right hc] at h
      cases Result.ok_injective h
      have : absFile a.val[i.val] ≠ absFile b.val[i.val] := by
        intro hq; rw [ee] at hc; exact hc (decide_eq_true hq)
      simp [this]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have h1 : a.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len a).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le h1, List.drop_of_length_le (by omega)]
    simp
termination_by a.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len a).val := hlt
  rw [vec_len_val] at this
  omega

/-- **`file_lists_eq` is `List (Option String)`'s `==`**, on code points. -/
theorem file_lists_eq_eq {a b : alloc.vec.Vec (Option (alloc.vec.Vec Std.U32))} {c : Bool}
    (ha : FilesWF a.val) (hb : FilesWF b.val) (h : file_lists_eq a b = ok c) :
    c = decide (a.val.map absFile = b.val.map absFile) := by
  rw [file_lists_eq] at h
  by_cases hne : (alloc.vec.Vec.len a != alloc.vec.Vec.len b) = true
  · rw [ite_eq_left hne] at h
    cases Result.ok_injective h
    have : a.val.length ≠ b.val.length := by
      intro he
      simp only [bne_iff_ne, ne_eq] at hne
      exact hne (UScalar.eq_of_val_eq (by rw [vec_len_val, vec_len_val, he]))
    symm
    simp only [decide_eq_false_iff_not]
    intro hq
    exact this (by simpa using congrArg List.length hq)
  · rw [ite_eq_right hne] at h
    have hl : a.val.length = b.val.length := by
      simp only [bne_iff_ne, ne_eq, not_not] at hne
      have := congrArg UScalar.val hne
      rwa [vec_len_val, vec_len_val] at this
    simpa using file_lists_eq_loop_eq a b _ ha hb hl h

/-! ## The locations -/

/-- The twin's hits a list of positions stands for. -/
def locsHits (hits : alloc.vec.Vec Hit) (locs : List Std.Usize) :
    List (System.FilePath × List (Option String)) :=
  locs.filterMap fun j => (hits.val[j.val]?).map absHit

theorem hit_seen_loop_eq (hits : alloc.vec.Vec Hit) (locs : alloc.vec.Vec Std.Usize) (h : Hit)
    (i : Std.Usize) {b : Bool} (hw : ∀ x ∈ hits.val, HitWF x) (hh : HitWF h)
    (hr : hit_seen_loop hits locs h i = ok b) :
    b = (locsHits hits (locs.val.drop i.val)).any (·.2 == (absHit h).2) := by
  rw [hit_seen_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len locs
  · rw [ite_eq_left hlt] at hr
    peel hr as j, hj
    obtain ⟨hi, rfl⟩ := vec_index_eq hj
    peel hr as h1, hh1
    obtain ⟨hk, rfl⟩ := vec_index_eq hh1
    peel hr as c, hc
    have ec := file_lists_eq_eq (hw _ (List.getElem_mem hk)).wf hh.wf hc
    rw [List.drop_eq_getElem_cons hi]
    simp only [locsHits, List.filterMap_cons, List.getElem?_eq_getElem hk, Option.map_some]
    rw [List.any_cons]
    have e1 : ((absHit hits.val[(locs.val[i.val]).val]).2 == (absHit h).2) = c := by
      rw [ec]; exact beq_eq_decide _ _
    rw [e1]
    by_cases hb : c = true
    · rw [ite_eq_left hb] at hr
      cases Result.ok_injective hr
      simp [hb]
    · rw [ite_eq_right hb] at hr
      peel hr as i3, hi3
      have hi3v : i3.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi3]; rfl
      have := hit_seen_loop_eq hits locs h i3 hw hh hr
      rw [hi3v] at this
      rw [this]
      simp [hb, locsHits]
  · rw [ite_eq_right hlt] at hr
    cases Result.ok_injective hr
    have : locs.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len locs).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le this]; rfl
termination_by locs.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len locs).val := hlt
  rw [vec_len_val] at this
  omega

/-- **`hit_seen` is `acc.any (·.2 == h.2)`.** -/
theorem hit_seen_eq {hits : alloc.vec.Vec Hit} {locs : alloc.vec.Vec Std.Usize} {h : Hit} {b : Bool}
    (hw : ∀ x ∈ hits.val, HitWF x) (hh : HitWF h) (hr : hit_seen hits locs h = ok b) :
    b = (locsHits hits locs.val).any (·.2 == (absHit h).2) := by
  rw [hit_seen] at hr
  simpa using hit_seen_loop_eq hits locs h _ hw hh hr

/-- A step of upstream's walk over the hits. -/
@[reducible] def locsStep (acc : Array (System.FilePath × List (Option String)))
    (h : System.FilePath × List (Option String)) : Array (System.FilePath × List (Option String)) :=
  if acc.any (·.2 == h.2) then acc else acc.push h

theorem hit_locations_loop_eq (hits : alloc.vec.Vec Hit) (locs : alloc.vec.Vec Std.Usize)
    (i : Std.Usize) {o : alloc.vec.Vec Std.Usize} (hw : ∀ x ∈ hits.val, HitWF x)
    (hl : (locsHits hits locs.val).length = locs.val.length)
    (hr : hit_locations_loop hits locs i = ok o) :
    (locsHits hits o.val).toArray =
        ((hits.val.drop i.val).map absHit).foldl locsStep (locsHits hits locs.val).toArray ∧
      (locsHits hits o.val).length = o.val.length := by
  rw [hit_locations_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len hits
  · rw [ite_eq_left hlt] at hr
    peel hr as h, hh
    obtain ⟨hi, rfl⟩ := vec_index_eq hh
    peel hr as b, hb
    have eb := hit_seen_eq hw (hw _ (List.getElem_mem hi)) hb
    peel hr as locs1, hl1
    peel hr as i2, hi2
    have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldl_cons]
    by_cases hc : b = true
    · rw [ite_eq_left hc] at hl1
      cases Result.ok_injective hl1
      have := hit_locations_loop_eq hits locs i2 hw hl hr
      rw [hi2v] at this
      have e : locsStep (locsHits hits locs.val).toArray (absHit hits.val[i.val]) =
          (locsHits hits locs.val).toArray := by
        simp only [locsStep, List.any_toArray, ← eb, hc, ↓reduceIte]
      rw [e]; exact this
    · rw [ite_eq_right hc] at hl1
      have ev := vec_push_val hl1
      have eh : locsHits hits locs1.val = locsHits hits locs.val ++ [absHit hits.val[i.val]] := by
        rw [ev]; simp [locsHits, List.filterMap_append, hi]
      have := hit_locations_loop_eq hits locs1 i2 hw (by rw [eh, ev]; simp [hl]) hr
      rw [hi2v] at this
      have e : locsStep (locsHits hits locs.val).toArray (absHit hits.val[i.val]) =
          (locsHits hits locs1.val).toArray := by
        simp only [locsStep, List.any_toArray, ← eb, hc]
        rw [eh]; simp
      rw [e]; exact this
  · rw [ite_eq_right hlt] at hr
    cases Result.ok_injective hr
    have : hits.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len hits).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le this]
    exact ⟨rfl, hl⟩
termination_by hits.val.length - i.val
decreasing_by
  all_goals
    have : i.val < (alloc.vec.Vec.len hits).val := hlt
    rw [vec_len_val] at this
    omega

/-- **`hit_locations` is upstream's walk**: the locations it answers stand for its array, and
there are as many. -/
theorem hit_locations_eq {hits : alloc.vec.Vec Hit} {o : alloc.vec.Vec Std.Usize}
    (hw : ∀ x ∈ hits.val, HitWF x) (hr : hit_locations hits = ok o) :
    (locsHits hits o.val).toArray = (hits.val.map absHit).foldl locsStep #[] ∧
      (locsHits hits o.val).length = o.val.length := by
  rw [hit_locations] at hr
  have := hit_locations_loop_eq hits _ _ hw (by simp [locsHits, alloc.vec.Vec.new]) hr
  simpa [locsHits, alloc.vec.Vec.new] using this

/-! ## `locateOf`, by its outcomes -/

section locateOf
open ConLeche.Frontend.Olean (Located)
variable {m : ConLeche.Name} {hits : Array (System.FilePath × List (Option String))}

theorem locateOf_empty (h : hits = #[]) : ∃ msg, locateOf m hits = .error (.internal msg) := by
  subst h; exact ⟨_, rfl⟩

theorem locateOf_many {x} (h0 : hits[0]? = some x) (hm : 1 < (hits.foldl locsStep #[]).size) :
    ∃ msg, locateOf m hits = .error (.internal msg) := by
  obtain ⟨d, fs⟩ := x
  simp only [locateOf, Id.run, h0, pure]
  rw [ite_eq_left hm]
  split <;> exact ⟨_, rfl⟩

theorem locateOf_some {d o s p} (h0 : hits[0]? = some (d, [o, s, p]))
    (hm : ¬ 1 < (hits.foldl locsStep #[]).size) (ho : o.isSome = true) :
    locateOf m hits = .ok ⟨d, s.isSome, p.isSome⟩ := by
  simp only [locateOf, Id.run, h0, pure]
  rw [ite_eq_right hm]
  have : o.isNone = false := by cases o <;> simp_all
  simp [this]

theorem locateOf_none {d s p} (h0 : hits[0]? = some (d, [none, s, p]))
    (hm : ¬ 1 < (hits.foldl locsStep #[]).size) :
    ∃ msg, locateOf m hits = .error (.internal msg) := by
  simp only [locateOf, Id.run, h0, pure]
  rw [ite_eq_right hm]
  exact ⟨_, rfl⟩

end locateOf

/-! ## `locate_of` -/

/-- What `locate_of` and `located_at` claim: an `Ok` is the location, an `Err` at kind
`internal` a failure of upstream's. -/
def LocOut (X : Except ConLeche.CheckError ConLeche.Frontend.Olean.Located)
    (o : core.result.Result Located kernel.core_types.CheckError) : Prop :=
  match o with
  | .Ok l => X = .ok (absLocated l)
  | .Err e => absAErrKind e = some .internal ∧ ∃ msg, X = .error (.internal msg)

theorem LocOut.err {X} {e} (hk : absAErrKind e = some .internal)
    (h : ∃ msg, X = .error (.internal msg)) : LocOut X (.Err e) := ⟨hk, h⟩

/-- `Err` at kind `internal`, whatever precedes it. -/
macro "internal_tail" h:ident " as " p:rcasesPat : tactic => `(tactic|
  (obtain $p:rcasesPat := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) _ $h:ident))

theorem located_at_eq {mt pre : alloc.vec.Vec Std.U32} {h0 : Hit} {o} {X}
    (hw : HitWF h0)
    (hsome : ∀ (f0 f1 f2 : Option String), (absHit h0).2 = [f0, f1, f2] → f0.isSome = true →
      X = .ok ⟨(absHit h0).1, f1.isSome, f2.isSome⟩)
    (hnone : ∀ (f1 f2 : Option String), (absHit h0).2 = [none, f1, f2] →
      ∃ msg, X = .error (.internal msg))
    (h : located_at mt pre h0 = ok o) : LocOut X o := by
  rw [located_at] at h
  have hs : ∃ f0 f1 f2, h0.files.val = [f0, f1, f2] := by
    match hf : h0.files.val, hw.three with
    | [f0, f1, f2], _ => exact ⟨f0, f1, f2, rfl⟩
  obtain ⟨f0, f1, f2, hf⟩ := hs
  have ha : (absHit h0).2 = [absFile f0, absFile f1, absFile f2] := by simp [absHit, hf]
  have ix : ∀ {i : Std.Usize} {x}, alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) h0.files i = ok x →
      x = (h0.files.val[i.val]?).getD none := by
    intro i x hx
    obtain ⟨hi, rfl⟩ := vec_index_eq hx
    simp [hi]
  peel h as o0, ho0
  have e0 := ix ho0
  rw [hf] at e0
  peel h as a0, ha0
  peel h as o1, ho1
  have e1 := ix ho1
  rw [hf] at e1
  peel h as a1, ha1
  peel h as o2, ho2
  have e2 := ix ho2
  rw [hf] at e2
  peel h as a2, ha2
  cases show o0 = f0 from e0
  cases show o1 = f1 from e1
  cases show o2 = f2 from e2
  have ea0 := file_some_eq ha0
  have ea1 := file_some_eq ha1
  have ea2 := file_some_eq ha2
  by_cases hc : a0 = true
  · rw [ite_eq_left hc] at h
    peel h as v, hv
    cases Result.ok_injective h
    cases ConRon.Refine.Expr.str_copy_eq hv
    have := hsome _ _ _ ha (by rw [← ea0]; exact hc)
    show X = _
    rw [this, ← ea1, ← ea2]
    rfl
  · rw [ite_eq_right hc] at h
    internal_tail h as ⟨_, rfl, hk⟩
    have hn : f0 = none := by
      cases f0 with
      | none => rfl
      | some _ => simp [ea0] at hc
    subst hn
    exact LocOut.err hk (hnone _ _ ha)

/-- **`locate_of` is upstream's `locateOf`**, the messages not compared.  `file_twice` only
chooses between two messages of one failure. -/
theorem locate_of_eq {mt : alloc.vec.Vec Std.U32} {hits : alloc.vec.Vec Hit} {o} (mN : ConLeche.Name)
    (hw : ∀ x ∈ hits.val, HitWF x) (h : locate_of mt hits = ok o) :
    LocOut (locateOf mN (hits.val.map absHit).toArray) o := by
  rw [locate_of] at h
  peel h as s0, -
  peel h as v0, -
  peel h as pre, -
  by_cases h0 : alloc.vec.Vec.len hits = 0#usize
  · rw [ite_eq_left h0] at h
    internal_tail h as ⟨_, rfl, hk⟩
    have hnil : hits.val = [] := by
      have := congrArg UScalar.val h0
      rw [vec_len_val] at this
      exact List.eq_nil_of_length_eq_zero this
    rw [hnil]
    exact LocOut.err hk (locateOf_empty rfl)
  rw [ite_eq_right h0] at h
  have hne : 0 < hits.val.length := by
    apply Nat.pos_of_ne_zero
    intro he
    apply h0
    apply UScalar.eq_of_val_eq
    rw [vec_len_val, he]; rfl
  have h00 : (hits.val.map absHit).toArray[0]? = some (absHit (hits.val[0]'hne)) := by
    rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hne]; rfl
  peel h as locs, hlocs
  obtain ⟨elocs, elen⟩ := hit_locations_eq hw hlocs
  have hsize : ((hits.val.map absHit).toArray.foldl locsStep #[]).size = locs.val.length := by
    rw [List.foldl_toArray, ← elocs, ← elen]
    simp
  by_cases hm : alloc.vec.Vec.len locs > 1#usize
  · rw [ite_eq_left hm] at h
    have hm' : 1 < locs.val.length := by
      have : (1#usize : Std.Usize).val < (alloc.vec.Vec.len locs).val := hm
      rw [vec_len_val] at this
      simpa using this
    peel h as b, -
    have ht := locateOf_many (m := mN) h00 (by rw [hsize]; exact hm')
    by_cases hb : b = true
    · rw [ite_eq_left hb] at h
      internal_tail h as ⟨_, rfl, hk⟩
      exact LocOut.err hk ht
    · rw [ite_eq_right hb] at h
      internal_tail h as ⟨_, rfl, hk⟩
      exact LocOut.err hk ht
  rw [ite_eq_right hm] at h
  have hm' : ¬ 1 < ((hits.val.map absHit).toArray.foldl locsStep #[]).size := by
    rw [hsize]
    intro hc
    apply hm
    show (1#usize : Std.Usize).val < (alloc.vec.Vec.len locs).val
    rw [vec_len_val]
    simpa using hc
  peel h as h1, hh1
  obtain ⟨_, rfl⟩ := vec_index_eq hh1
  exact located_at_eq (hw _ (List.getElem_mem _))
    (fun f0 f1 f2 hf hs =>
      locateOf_some (h00.trans (congrArg some (Prod.ext rfl hf))) hm' hs)
    (fun f1 f2 hf =>
      locateOf_none (h00.trans (congrArg some (Prod.ext rfl hf))) hm') h

/-! ## The file names -/

theorem absString_lit {v : alloc.vec.Vec Std.U32} {l : List Std.U32} {str : String}
    (hv : v.val = l) (hl : String.ofList (l.map fun c => Char.ofNat c.val) = str) :
    absString v = str := by
  rw [absString, hv, hl]

theorem ext0 : String.ofList ((Array.to_slice part_ext.M).val.map fun c => Char.ofNat c.val) = "olean" := by
  have e : (Array.to_slice part_ext.M).val.map (fun c => Char.ofNat c.val) = ['o', 'l', 'e', 'a', 'n'] := by
    unfold part_ext.M; decide
  rw [e]

theorem ext1 : String.ofList ((Array.to_slice part_ext.M_1).val.map fun c => Char.ofNat c.val) = "olean.server" := by
  have e : (Array.to_slice part_ext.M_1).val.map (fun c => Char.ofNat c.val) =
      ['o', 'l', 'e', 'a', 'n', '.', 's', 'e', 'r', 'v', 'e', 'r'] := by
    unfold part_ext.M_1; decide
  rw [e]

theorem ext2 : String.ofList ((Array.to_slice part_ext.M_2).val.map fun c => Char.ofNat c.val) = "olean.private" := by
  have e : (Array.to_slice part_ext.M_2).val.map (fun c => Char.ofNat c.val) =
      ['o', 'l', 'e', 'a', 'n', '.', 'p', 'r', 'i', 'v', 'a', 't', 'e'] := by
    unfold part_ext.M_2; decide
  rw [e]

theorem part_ext_eq {i : Std.Usize} {v} (hi : i.val < 3) (h : part_ext i = ok v) :
    absString v = partExts[i.val]'(by simpa [partExts] using hi) := by
  rw [part_ext] at h
  by_cases h0 : i = 0#usize
  · rw [ite_eq_left h0] at h
    peel h as s1, hs1
    have ev := ConRon.Refine.code_points_val h
    cases Result.ok_injective (show ok _ = ok s1 from hs1)
    subst h0
    exact absString_lit ev ext0
  rw [ite_eq_right h0] at h
  have hv0 : i.val ≠ 0 := fun he => h0 (UScalar.eq_of_val_eq (by rw [he]; rfl))
  by_cases h1 : i = 1#usize
  · rw [ite_eq_left h1] at h
    peel h as s1, hs1
    have ev := ConRon.Refine.code_points_val h
    cases Result.ok_injective (show ok _ = ok s1 from hs1)
    subst h1
    exact absString_lit ev ext1
  rw [ite_eq_right h1] at h
  have hv1 : i.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq (by rw [he]; rfl))
  peel h as s1, hs1
  have ev := ConRon.Refine.code_points_val h
  cases Result.ok_injective (show ok _ = ok s1 from hs1)
  have e2 : i.val = 2 := by omega
  simp only [e2]
  exact absString_lit ev ext2

/-! ## `mod_file`'s side of a request -/

theorem mod_file_name {pers ar d m e p} (h : mod_file pers ar d m e = ok (.Ok p)) :
    ∃ n, arena.env.read_name pers ar m = ok (.Ok n) := by
  rw [mod_file] at h
  peel h as r, hr
  cases r with
  | Ok n => exact ⟨n, hr⟩
  | Err e => cases Result.ok_injective h

theorem pathRel_of {pers ar m n} {d e p : alloc.vec.Vec Std.U32}
    (hn : arena.env.read_name pers ar m = ok (.Ok n)) (h : mod_file pers ar d m e = ok (.Ok p)) :
    PathRel p (ConLeche.Frontend.Olean.modFile ⟨absString d⟩ (absName n) (absString e)) :=
  ⟨pers, ar, d, m, e, n, h, hn, rfl⟩

/-! ## The search -/

/-- The twin's reading of one file in a directory. -/
@[reducible] def locStep (fs : Arena.Frontend.Olean.OleanFs) (m : ConLeche.Name) (d : System.FilePath)
    (e : String) : Except String (Option String) := do
  let p := ConLeche.Frontend.Olean.modFile d m e
  if ← fs.pathExists p then
    return some (← fs.realPath p).toString
  else return none

section search

variable {F : Type} {inst : OleanFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
  {pers : arena.store.PersTier} {ar : arena.store.EStore} {m : arena.handle.NIdx}
  {n : kernel.name.Name}

/-- **`locate_file`'s accept is one step of the twin's `locateIn`.** -/
theorem locate_file_ok {d i x} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n)) (hi : i.val < 3)
    (h : locate_file inst fsv pers ar m d i = ok (.Ok x)) :
    locStep fs (absName n) ⟨absString d⟩ (partExts[i.val]'(by simpa [partExts] using hi)) = .ok (absFile x) ∧
      ∀ s, x = some s → StrWF s := by
  rw [locate_file] at h
  peel h as v, hv
  rw [← part_ext_eq hi hv]
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok p =>
    have hrel := pathRel_of hn hr
    dsimp only at h
    peel h as r1, hr1
    cases r1 with
    | Err e => cases Result.ok_injective h
    | Ok b =>
      have e1 := hfs.pathExists hrel b hr1
      dsimp only at h
      by_cases hb : b = true
      · rw [ite_eq_left hb] at h
        peel h as r2, hr2
        cases r2 with
        | Err e => cases Result.ok_injective h
        | Ok rp =>
          cases Result.ok_injective h
          obtain ⟨e2, hw⟩ := hfs.realPath hrel rp hr2
          refine ⟨?_, by rintro s ⟨rfl⟩; exact hw⟩
          simp only [locStep, e1, e2, hb]
          rfl
      · rw [ite_eq_right hb] at h
        cases Result.ok_injective h
        refine ⟨?_, by simp⟩
        simp only [locStep, e1, hb]
        rfl

theorem locate_in_loop_ok {d} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n)) (files : alloc.vec.Vec (Option (alloc.vec.Vec Std.U32)))
    (i : Std.Usize) {o} (hi : i.val ≤ 3) (hw : FilesWF files.val)
    (h : locate_in_loop inst fsv pers ar m d files i = ok (.Ok o)) :
    ∃ ys, (partExts.drop i.val).mapM (locStep fs (absName n) ⟨absString d⟩) = .ok ys ∧
      o.files.val.map absFile = files.val.map absFile ++ ys ∧ FilesWF o.files.val ∧
      o.files.val.length + i.val = files.val.length + 3 ∧ o.dir = d := by
  rw [locate_in_loop] at h
  by_cases hlt : i < 3#usize
  · rw [ite_eq_left hlt] at h
    have hlt' : i.val < 3 := by
      have : i.val < (3#usize : Std.Usize).val := hlt
      simpa using this
    peel h as r, hr
    cases r with
    | Err e => cases Result.ok_injective h
    | Ok x =>
      obtain ⟨e1, hx⟩ := locate_file_ok hfs hn hlt' hr
      dsimp only at h
      peel h as files1, hf1
      peel h as i1, hi1
      have hi1v : i1.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi1]; rfl
      have ev := vec_push_val hf1
      have hw1 : FilesWF files1.val := by
        rw [ev]
        intro y hy s hs
        rcases List.mem_append.mp hy with hy | hy
        · exact hw y hy s hs
        · rw [List.mem_singleton.mp hy] at hs; exact hx s hs
      obtain ⟨ys, hys, e2, hw2, hl, hd⟩ := locate_in_loop_ok hfs hn files1 i1 (by omega) hw1 h
      rw [hi1v] at hys hl
      refine ⟨absFile x :: ys, ?_, ?_, hw2, ?_, hd⟩
      · rw [List.drop_eq_getElem_cons (by simpa [partExts] using hlt'), List.mapM_cons, e1, hys]
        rfl
      · rw [e2, ev]; simp
      · rw [ev] at hl; simp at hl; omega
  · rw [ite_eq_right hlt] at h
    peel h as v, hv
    cases Result.ok_injective h
    have h3 : i.val = 3 := by
      have : ¬ i.val < (3#usize : Std.Usize).val := hlt
      simp at this; omega
    refine ⟨[], ?_, by simp, hw, by show files.val.length + i.val = _; omega, ConRon.Refine.Expr.str_copy_eq hv⟩
    rw [h3]; rfl
termination_by 3 - i.val
decreasing_by omega

/-- **`locate_in`'s accept is the twin's `locateIn`.** -/
theorem locate_in_ok {d h} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (hr : locate_in inst fsv pers ar m d = ok (.Ok h)) :
    locateIn fs (absName n) ⟨absString d⟩ = .ok (absHit h) ∧ HitWF h := by
  rw [locate_in] at hr
  have hnew : (alloc.vec.Vec.with_capacity (Option (alloc.vec.Vec Std.U32)) 3#usize).val = [] := rfl
  obtain ⟨ys, hys, e, hw, hl, hd⟩ := locate_in_loop_ok hfs hn _ _ (by decide)
    (by rw [hnew]; simp [FilesWF]) hr
  rw [hnew] at e hl
  refine ⟨?_, ⟨by simpa using hl, hw⟩⟩
  simp only [locateIn, absHit, hd, e]
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hys
  show (partExts.mapM (locStep fs (absName n) ⟨absString d⟩) >>= fun files => pure (_, files)) = _
  rw [hys]
  rfl

/-- The twin's filter. -/
@[reducible] def hitHolds (h : System.FilePath × List (Option String)) : Bool := h.2.any (·.isSome)

theorem locate_hits_loop_ok {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n)) (out : alloc.vec.Vec Hit) (i : Std.Usize) {o}
    (hw : ∀ x ∈ out.val, HitWF x)
    (h : locate_hits_loop inst fsv pers ar sp m out i = ok (.Ok o)) :
    ∃ ys, ((absSearchPath sp).drop i.val).mapM (locateIn fs (absName n)) = .ok ys ∧
      o.val.map absHit = out.val.map absHit ++ ys.filter hitHolds ∧ ∀ x ∈ o.val, HitWF x := by
  rw [locate_hits_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len sp
  · rw [ite_eq_left hlt] at h
    peel h as v, hv
    obtain ⟨hi, rfl⟩ := vec_index_eq hv
    peel h as r, hr
    cases r with
    | Err e => cases Result.ok_injective h
    | Ok x =>
      obtain ⟨e1, hx⟩ := locate_in_ok hfs hn hr
      dsimp only at h
      peel h as out1, ho1
      peel h as i2, hi2
      have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
      have ea := hits_add_eq ho1
      have hw1 : ∀ y ∈ out1.val, HitWF y := by
        rw [hits_add] at ho1
        peel ho1 as b, -
        by_cases hb : b = true
        · rw [ite_eq_left hb] at ho1
          rw [vec_push_val ho1]
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hw y hy
          · rw [List.mem_singleton.mp hy]; exact hx
        · rw [ite_eq_right hb] at ho1
          cases Result.ok_injective ho1
          exact hw
      obtain ⟨ys, hys, e2, hw2⟩ := locate_hits_loop_ok hfs hn out1 i2 hw1 h
      rw [hi2v] at hys
      refine ⟨absHit x :: ys, ?_, ?_, hw2⟩
      · have hd : (absSearchPath sp).drop i.val =
            (⟨absString sp.val[i.val]⟩ : System.FilePath) :: (absSearchPath sp).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons (by simpa [absSearchPath] using hi)]
          simp [absSearchPath]
        rw [hd, List.mapM_cons, e1, hys]
        rfl
      · rw [e2, ea, List.filter_cons]
        by_cases hc : hitHolds (absHit x) = true <;> simp [hc]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hle : sp.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len sp).val := hlt
      rw [vec_len_val] at this; omega
    refine ⟨[], ?_, by simp, hw⟩
    rw [List.drop_of_length_le (by simpa [absSearchPath] using hle)]
    rfl
termination_by sp.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len sp).val := hlt
  rw [vec_len_val] at this
  omega

/-- **`locate_hits`'s accept is the twin's `locateHits`.** -/
theorem locate_hits_ok {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {o} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : locate_hits inst fsv pers ar sp m = ok (.Ok o)) :
    locateHits fs (absSearchPath sp) (absName n) = .ok (o.val.map absHit).toArray ∧
      ∀ x ∈ o.val, HitWF x := by
  rw [locate_hits] at h
  obtain ⟨ys, hys, e, hw⟩ := locate_hits_loop_ok hfs hn _ _ (by simp [alloc.vec.Vec.new]) h
  refine ⟨?_, hw⟩
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hys
  show ((absSearchPath sp).mapM (locateIn fs (absName n)) >>= fun hs => pure _) = _
  rw [hys, e]
  simp [alloc.vec.Vec.new]

/-- **`find_module`'s accept is the twin's `findModule`.** -/
theorem find_module_ok {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {l} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : find_module inst fsv pers ar sp m = ok (.Ok l)) :
    findModule fs (absSearchPath sp) (absName n) = .ok (absLocated l) := by
  rw [find_module] at h
  peel h as mt, -
  peel h as r, hr
  cases r with
  | Err le =>
    cases le with
    | Err e => cases Result.ok_injective h
    | Fs e =>
      dsimp only at h
      internal_tail h as ⟨_, he, -⟩
      cases he
  | Ok hits =>
    obtain ⟨e1, hw⟩ := locate_hits_ok hfs hn hr
    have e2 : LocOut _ _ := locate_of_eq (absName n) hw h
    have e3 : locateOf (absName n) (hits.val.map absHit).toArray = .ok (absLocated l) := e2
    simp only [findModule, e1, e3]

/-- **`read_part`'s accept is the twin's `readPart`**, and what `part_of_bytes` leaves true. -/
theorem read_part_ok {p q} {pt : frontend.olean.region.Part} (hfs : FsRel inst fsv fs)
    (hrel : PathRel p q) (h : read_part inst fsv p = ok (.Ok pt)) :
    Arena.Frontend.Olean.readPart fs q = .ok (absPart pt) ∧ PartFits pt := by
  rw [read_part] at h
  peel h as r, hr
  cases r with
  | Err e =>
    dsimp only at h
    peel h as ce, -
    cases Result.ok_injective h
  | Ok b =>
    have e1 := hfs.readBinFile hrel b hr
    have := part_of_bytes_eq (q.toString) h
    obtain ⟨e2, -, hf⟩ := this
    refine ⟨?_, hf⟩
    simp only [Arena.Frontend.Olean.readPart, e1, e2]

end search

end ConRon.Refine2.Frontend.Olean
