/-
# `ConRon.Refine2.Frontend.Olean.FastBuild` — the memo and the build pass of `olean/fast.rs`

**Task #142, Theorem 2.**  The memo holds words against the twin's handles (`DSRel`); the
word `0` is the twin's `default`.  The upward sweep threads the store and the memo, in the
judgement `BS`.  `run_passes_refines` is both passes.

The Rust's `(c / 8) as usize` is the identity on a location of the region and truncates
past `usize`, which no location is, so `SubRel` holds of the memo at `subT`, the twin's
memo read through that truncation, and the node functions cannot tell `subT` from
`DS.sub`, for they only ask at locations (`nameNode_congr`).
-/
import ConRon.Refine2.Frontend.Olean.Fast

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_loc)
open frontend.olean.spec (name_node level_node levels_node expr_node)
open frontend.olean.fast (marks_at marked build_kind_name build_kind_level build_kind_levels
  build_kind_expr build_slot build_marked build_pass build_pass_loop run_passes ds_fresh
  K_NAME K_LEVEL K_LEVELS K_EXPR mark_roots mark_pass failed_m max_loc)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (Sub nameIn levelIn levelsIn exprIn nameNode levelNode levelsNode
  exprNode buildSlot buildPass runPasses)
open ConLeche.Frontend.Olean (marksAt markRoot markPass failedM maxLoc kName kLevel kLevels kExpr)
open ConRon.Refine.HashMap (uscalar_add_eq uscalar_div_eq)

/-- The memo of the twin. -/
abbrev TDS := ConRon.Arena.Frontend.Olean.DS

/-! ## The memo -/

/-- A memo word, as a handle of the twin. -/
abbrev wN (w : Std.U32) := absNIdx ⟨w⟩
/-- A memo word, as a handle of the twin. -/
abbrev wL (w : Std.U32) := absLIdx ⟨w⟩
/-- A memo word, as a handle of the twin. -/
abbrev wLs (w : Std.U32) := absLsIdx ⟨w⟩
/-- A memo word, as a handle of the twin. -/
abbrev wE (w : Std.U32) := absEIdx ⟨w⟩

/-- **The memo, word for word.** -/
structure DSRel (d : frontend.olean.fast.DS) (t : TDS) : Prop where
  names : d.names.val.map wN = t.names.toList
  levels : d.levels.val.map wL = t.levels.toList
  exprs : d.exprs.val.map wE = t.exprs.toList
  lists : d.lists.val.map wLs = t.lists.toList

/-- A read of a word of the memo. -/
theorem getD_of_map {β : Type} {A : Std.U32 → β} {l : List Std.U32} {a : Array β}
    (h : l.map A = a.toList) {i : Nat} {x : Std.U32} {d : β} (hi : i < l.length) (hx : x = l[i]) :
    a.getD i d = A x := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← h, List.getElem?_map,
    List.getElem?_eq_getElem hi, ← hx]
  rfl

/-- What `as usize` keeps of a number. -/
abbrev tr (n : Nat) : Nat := n % 2 ^ UScalarTy.Usize.numBits

theorem tr_of_le {n : Nat} (h : n ≤ Std.Usize.max) : tr n = n := by
  apply Nat.mod_eq_of_lt
  have hpos : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
  have hmax : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    simp only [Std.Usize.max, Std.Usize.numBits]
    omega
  omega

/-- The twin's memo read through the Rust's `as usize`. -/
def subT (t : TDS) : Sub :=
  ⟨fun c => some (t.names.getD (tr (c / 8)) default),
   fun c => some (t.levels.getD (tr (c / 8)) default),
   fun c => some (t.lists.getD (tr (c / 8)) default),
   fun c => some (t.exprs.getD (tr (c / 8)) default)⟩

/-- A word of the memo at a location, whatever the location. -/
theorem word_at {β : Type} {A : Std.U32 → β} {v : alloc.vec.Vec Std.U32} {a : Array β}
    (h : v.val.map A = a.toList) {c i : Std.U64} {x : Std.U32} {d : β} (hi : c / 8#u64 = ok i)
    (hx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32) v
      (UScalar.cast UScalarTy.Usize i) = ok x) :
    a.getD (tr (c.val / 8)) d = A x := by
  obtain ⟨hlt, he⟩ := vec_index_eq hx
  have hv := uscalar_div_eq hi
  rw [u64_val_lit8] at hv
  have hc : (UScalar.cast UScalarTy.Usize i).val = tr (c.val / 8) := by
    rw [UScalar.cast_val_eq, hv]
  refine getD_of_map h (by rw [← hc]; exact hlt) ?_
  simp only [he, hc]

/-- **The memo as `Sub`**, read through the truncation. -/
theorem ds_subrel {d : frontend.olean.fast.DS} {t : TDS} (h : DSRel d t) :
    SubRel frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecSub d (subT t) where
  nm c o hc := by
    simp only [frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecSub.sub_name, lift, bind_ok] at hc
    peel hc as i, hi
    peel hc as x, hx
    peel hc as n, hn
    cases Result.ok_injective hc
    cases Result.ok_injective hn
    simp only [Option.map_some, subT, word_at h.names hi hx]
  lv c o hc := by
    simp only [frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecSub.sub_level, lift, bind_ok] at hc
    peel hc as i, hi
    peel hc as x, hx
    peel hc as n, hn
    cases Result.ok_injective hc
    cases Result.ok_injective hn
    simp only [Option.map_some, subT, word_at h.levels hi hx]
  lvs c o hc := by
    simp only [frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecSub.sub_levels, lift, bind_ok] at hc
    peel hc as i, hi
    peel hc as x, hx
    peel hc as n, hn
    cases Result.ok_injective hc
    cases Result.ok_injective hn
    simp only [Option.map_some, subT, word_at h.lists hi hx]
  ex c o hc := by
    simp only [frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecSub.sub_expr, lift, bind_ok] at hc
    peel hc as i, hi
    peel hc as x, hx
    peel hc as n, hn
    cases Result.ok_injective hc
    cases Result.ok_injective hn
    simp only [Option.map_some, subT, word_at h.exprs hi hx]

/-! ## The node functions only ask at locations -/

theorem down_fits {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {g c : Nat} {v : UInt64} (h : (absRegion bs r).down g v = some c) : c + 8 ≤ bs.val.length := by
  simp only [ConLeche.Frontend.Olean.Region.down, ConLeche.Frontend.Olean.Region.loc] at h
  split at h
  · rename_i hl
    split at hl
    · cases hl
    · split at hl
      · cases hl
      · rename_i hg
        have e := Option.some.inj hl
        have hne : (absRegion bs r).locGo v (absRegion bs r).segs.size ≠ 0 := by simpa using hg
        split at h
        · cases Option.some.inj h
          rw [← e]
          rcases locGo_fits hr v (absRegion bs r).segs.size with h0 | h1
          · exact absurd h0 hne
          · exact h1
        · cases h
  · cases h

/-- Two `Sub`s that agree at every location of the bytes. -/
structure Agree (L : Nat) (a b : Sub) : Prop where
  nm : ∀ c, c + 8 ≤ L → a.name c = b.name c
  lv : ∀ c, c + 8 ≤ L → a.level c = b.level c
  lvs : ∀ c, c + 8 ≤ L → a.levels c = b.levels c
  ex : ∀ c, c + 8 ≤ L → a.expr c = b.expr c

section congr
variable {bs : Slice Std.U8} {r : frontend.olean.region.Region} {a b : Sub}
  (hr : RegionFits bs r) (H : Agree bs.val.length a b)
include hr H

theorem nameIn_congr {P g v} : nameIn P (absRegion bs r) g v a = nameIn P (absRegion bs r) g v b := by
  simp only [nameIn]
  split
  · rfl
  · generalize hd : (absRegion bs r).down g v = o
    cases o with
    | none => rfl
    | some c => exact H.nm c (down_fits hr hd)

theorem levelIn_congr {P g v} : levelIn P (absRegion bs r) g v a = levelIn P (absRegion bs r) g v b := by
  simp only [levelIn]
  split
  · rfl
  · generalize hd : (absRegion bs r).down g v = o
    cases o with
    | none => rfl
    | some c => exact H.lv c (down_fits hr hd)

theorem levelsIn_congr {P g v} : levelsIn P (absRegion bs r) g v a = levelsIn P (absRegion bs r) g v b := by
  simp only [levelsIn]
  split
  · rfl
  · generalize hd : (absRegion bs r).down g v = o
    cases o with
    | none => rfl
    | some c => exact H.lvs c (down_fits hr hd)

theorem exprIn_congr {g v} : exprIn (absRegion bs r) g v a = exprIn (absRegion bs r) g v b := by
  simp only [exprIn]
  generalize hd : (absRegion bs r).down g v = o
  cases o with
  | none => rfl
  | some c => exact H.ex c (down_fits hr hd)

theorem nameNode_congr {P g} : nameNode P (absRegion bs r) g a = nameNode P (absRegion bs r) g b := by
  simp only [nameNode, nameIn_congr hr H]

theorem levelNode_congr {P g} : levelNode P (absRegion bs r) g a = levelNode P (absRegion bs r) g b := by
  simp only [levelNode, nameIn_congr hr H, levelIn_congr hr H]

theorem levelsNode_congr {P g} : levelsNode P (absRegion bs r) g a = levelsNode P (absRegion bs r) g b := by
  simp only [levelsNode, levelIn_congr hr H, levelsIn_congr hr H]

theorem exprNode_congr {P g} : exprNode P (absRegion bs r) g a = exprNode P (absRegion bs r) g b := by
  simp only [exprNode, nameIn_congr hr H, levelIn_congr hr H, levelsIn_congr hr H, exprIn_congr hr H]

end congr

/-- The truncation changes nothing at a location. -/
theorem subT_agree {L : Nat} (hL : L ≤ Std.Usize.max) (t : TDS) :
    Agree L (subT t) (ConRon.Arena.Frontend.Olean.DS.sub t) := by
  have hc : ∀ c, c + 8 ≤ L → tr (c / 8) = c / 8 := fun c hc => tr_of_le (by omega)
  refine ⟨fun c h => ?_, fun c h => ?_, fun c h => ?_, fun c h => ?_⟩ <;>
    simp only [subT, ConRon.Arena.Frontend.Olean.DS.sub, hc c h]

theorem bytes_le_max (bs : Slice Std.U8) : bs.val.length ≤ Std.Usize.max := by scalar_tac

/-- **The node functions on the memo.** -/
theorem ds_name_node {d : frontend.olean.fast.DS} {t : TDS} {pk bs r g pers st lst}
    (hr : RegionFits bs r) (h : DSRel d t) :
    RS pers (EqA absNIdx) st lst
      (name_node frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecSub pk pers st.store bs r g d)
      (nameNode (absPins pk) (absRegion bs r) g.val (ConRon.Arena.Frontend.Olean.DS.sub t)) := by
  rw [← nameNode_congr hr (subT_agree (bytes_le_max bs) t)]
  exact name_node_refines hr (ds_subrel h)

theorem ds_level_node {d : frontend.olean.fast.DS} {t : TDS} {pk bs r g pers st lst}
    (hr : RegionFits bs r) (h : DSRel d t) :
    RS pers (EqA absLIdx) st lst
      (level_node frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecSub pk pers st.store bs r g d)
      (levelNode (absPins pk) (absRegion bs r) g.val (ConRon.Arena.Frontend.Olean.DS.sub t)) := by
  rw [← levelNode_congr hr (subT_agree (bytes_le_max bs) t)]
  exact level_node_refines (ds_subrel h)

theorem ds_levels_node {d : frontend.olean.fast.DS} {t : TDS} {pk bs r g pers st lst}
    (hr : RegionFits bs r) (h : DSRel d t) :
    RS pers (EqA absLsIdx) st lst
      (levels_node frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecSub pk pers st.store bs r g d)
      (levelsNode (absPins pk) (absRegion bs r) g.val (ConRon.Arena.Frontend.Olean.DS.sub t)) := by
  rw [← levelsNode_congr hr (subT_agree (bytes_le_max bs) t)]
  exact levels_node_refines (ds_subrel h)

theorem ds_expr_node {d : frontend.olean.fast.DS} {t : TDS} {pk bs r g pers st lst}
    (hr : RegionFits bs r) (h : DSRel d t) :
    RS pers (EqA absEIdx) st lst
      (expr_node frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecSub pk pers st.store bs r g d)
      (exprNode (absPins pk) (absRegion bs r) g.val (ConRon.Arena.Frontend.Olean.DS.sub t)) := by
  rw [← exprNode_congr hr (subT_agree (bytes_le_max bs) t)]
  exact expr_node_refines hr (ds_subrel h)

/-! ## Writes of the memo -/

theorem dsrel_name {d t} {v : alloc.vec.Vec Std.U32} {p : Nat} {a : arena.handle.NIdx} (h : DSRel d t)
    (hv : v.val = d.names.val.set p a.word) :
    DSRel { d with names := v } (ConRon.Arena.Frontend.Olean.DS.setName t p (absNIdx a)) := by
  cases t
  exact ⟨by simp [hv, ConRon.Arena.Frontend.Olean.DS.setName, List.map_set, h.names], h.levels, h.exprs, h.lists⟩

theorem dsrel_level {d t} {v : alloc.vec.Vec Std.U32} {p : Nat} {a : arena.handle.LIdx} (h : DSRel d t)
    (hv : v.val = d.levels.val.set p a.word) :
    DSRel { d with levels := v } (ConRon.Arena.Frontend.Olean.DS.setLevel t p (absLIdx a)) := by
  cases t
  exact ⟨h.names, by simp [hv, ConRon.Arena.Frontend.Olean.DS.setLevel, List.map_set, h.levels], h.exprs, h.lists⟩

theorem dsrel_lists {d t} {v : alloc.vec.Vec Std.U32} {p : Nat} {a : arena.handle.LsIdx} (h : DSRel d t)
    (hv : v.val = d.lists.val.set p a.word) :
    DSRel { d with lists := v } (ConRon.Arena.Frontend.Olean.DS.setLevels t p (absLsIdx a)) := by
  cases t
  exact ⟨h.names, h.levels, h.exprs, by simp [hv, ConRon.Arena.Frontend.Olean.DS.setLevels, List.map_set, h.lists]⟩

theorem dsrel_expr {d t} {v : alloc.vec.Vec Std.U32} {p : Nat} {a : arena.handle.EIdx} (h : DSRel d t)
    (hv : v.val = d.exprs.val.set p a.word) :
    DSRel { d with exprs := v } (ConRon.Arena.Frontend.Olean.DS.setExpr t p (absEIdx a)) := by
  cases t
  exact ⟨h.names, h.levels, by simp [hv, ConRon.Arena.Frontend.Olean.DS.setExpr, List.map_set, h.exprs], h.lists⟩

/-- **`ds_fresh` is `DS.fresh`.** -/
theorem ds_fresh_rel {n : Std.Usize} {d} (h : ds_fresh n = ok d) :
    DSRel d (ConRon.Arena.Frontend.Olean.DS.fresh n.val) := by
  rw [ds_fresh, alloc.vec.Vec.resize] at h
  have hl : ∀ {names : alloc.vec.Vec Std.U32}, names.val = List.replicate n.val 0#u32 →
      ∀ {β : Type} [Inhabited β] (W : Std.U32 → β), W 0#u32 = default →
      names.val.map W = (Array.replicate n.val (default : β)).toList := by
    intro names hn β _ W hW
    rw [hn, List.map_replicate, hW]
    simp
  split at h
  · rename_i hlt
    simp at hlt
  · peel h as x, hx
    peel hx as y, hy
    have hx0 : 0#u32 = y := Result.ok_injective hy
    subst hx0
    cases Result.ok_injective hx
    cases Result.ok_injective h
    have e0 : ∀ (l : List Std.U32) (hl), (alloc.vec.Vec.from l hl).val = l := fun l hl => Slice.from_val _ _
    have e1 : (alloc.vec.Vec.new Std.U32).val = [] := Slice.from_val _ _
    have hn : (alloc.vec.Vec.from ((alloc.vec.Vec.new Std.U32).val.resize n.val 0#u32) (by scalar_tac)).val
        = List.replicate n.val 0#u32 := by
      rw [e0, e1]; simp [List.resize]
    exact ⟨hl hn _ rfl, hl hn _ rfl, hl hn _ rfl, hl hn _ rfl⟩

/-! ## `BS`: a read that threads the store and the memo -/

/-- **The lockstep judgement of the upward sweep.** -/
def BS (pers : arena.store.PersTier) (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result Unit frontend.olean.spec.RdErr × arena.store.EStore × frontend.olean.fast.DS))
    (x : AM (Option TDS)) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st → ∀ o s' d', m = ok (o, s', d') →
    RdOut pers (fun _ t' => DSRel d' t') (withStore st s') o (x.run lst)

theorem BS.pure_step {γ : Type} {pers st lst} {f : Result γ} {k} {x : AM (Option TDS)}
    (h : ∀ a, f = ok a → BS pers st lst (k a) x) : BS pers st lst (Std.bind f k) x := by
  intro hrel hinv o s' d' hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a h1 hrel hinv o s' d' h2

theorem BS.leaf {pers st lst} {d} {t : TDS} (h : DSRel d t) :
    BS pers st lst (ok (.Ok (), st.store, d)) (pure (some t)) := by
  intro hrel hinv o s' d' hm
  cases Result.ok_injective hm
  exact ⟨t, lst, rfl, h, hrel, hinv⟩

/-- The twin's run moved along an equation. -/
theorem BS.of_eq {pers st lst} {m} {x y : AM (Option TDS)} (h : BS pers st lst m x) (hxy : y = x) :
    BS pers st lst m y := by
  rw [hxy]; exact h

/-- An error answer survives a bind that passes `none` on. -/
theorem rdout_err_bind {α α' β β' : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {R' : α' → β' → Prop} {st' : arena.monad.AState} {lst : AState}
    {e : frontend.olean.spec.RdErr} {y : AM (Option β)} {h : Option β → AM (Option β')}
    (hy : RdOut pers R st' (.Err e) (y.run lst)) (h0 : h none = pure none) :
    RdOut pers R' st' (.Err e) ((y >>= h).run lst) := by
  cases e with
  | Bad =>
    obtain ⟨lst1, hx, h2, h3⟩ := hy
    rw [am_bind_ok hx, h0]
    exact ⟨lst1, rfl, h2, h3⟩
  | Err e =>
    intro k' hk'
    obtain ⟨le, hle, hkk⟩ := hy k' hk'
    refine ⟨le, ?_, hkk⟩
    rw [StateT.run_bind, hle]; rfl

/-- The twin's continuation of a step of the sweep. -/
@[reducible] def seqK (g : TDS → AM (Option TDS)) : Option TDS → AM (Option TDS)
  | none => pure none
  | some t => g t

/-- **A step of the sweep, then the rest.** -/
theorem BS.bind {pers st lst} {f} {x : AM (Option TDS)} {g : TDS → AM (Option TDS)}
    {KR : arena.store.EStore → frontend.olean.fast.DS → Result (core.result.Result Unit frontend.olean.spec.RdErr × arena.store.EStore × frontend.olean.fast.DS)}
    (hf : BS pers st lst f x)
    (hk : ∀ s1 d1 t1 lst1, DSRel d1 t1 → BS pers (withStore st s1) lst1 (KR s1 d1) (g t1)) :
    BS pers st lst
      (do
        let (r1, ar1, d1) ← f
        match r1 with
        | .Ok _ => KR ar1 d1
        | .Err _ => ok (r1, ar1, d1))
      (x >>= seqK g) := by
  intro hrel hinv o s' d' hm
  obtain ⟨⟨r1, ar1, d1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hF := hf hrel hinv r1 ar1 d1 h1
  cases r1 with
  | Ok u =>
    obtain ⟨b, lst1, hx, hR, h3, h4⟩ := hF
    rw [am_bind_ok hx]
    exact hk ar1 d1 b lst1 hR h3 h4 o s' d' h2
  | Err e =>
    cases Result.ok_injective h2
    exact rdout_err_bind hF rfl

/-! ## One kind of a slot -/

/-- The twin's value of one kind. -/
@[reducible] def contS {β : Type} (tset : β → TDS) : Option β → AM (Option TDS)
  | none => pure none
  | some v => pure (some (tset v))

/-- The twin's value of one kind of a slot. -/
def kindT {β : Type} (c : Bool) (y : AM (Option β)) (tset : β → TDS) (t : TDS) : AM (Option TDS) :=
  if c then y >>= contS tset else pure (some t)

set_option hygiene false in
/-- **One kind of a slot**: the mark, the node function, and the write of the memo.  A
script, not a lemma: the Rust's `match`es are its own matchers.  It reads `hd` and `hp`. -/
macro "kind_tac " hn:term " , " hu:term : tactic =>
  `(tactic| (
    refine BS.pure_step fun b hb => ?_
    rw [← marked_eq hb, kindT]
    cases b with
    | false => exact BS.leaf hd
    | true =>
      refine BS.pure_step fun i hi => ?_
      rw [← mul8_val hi]
      simp only [↓reduceIte]
      intro hrel hinv o s' d' hm
      obtain ⟨⟨r1, ar1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
      have hF := $hn:term hrel hinv r1 ar1 h1
      cases r1 with
      | Ok a =>
        obtain ⟨b, lst1, hx, hR, h3, h4⟩ := hF
        cases hR
        rw [am_bind_ok hx]
        simp only [lift, bind_ok] at h2
        peel h2 as q, hq
        obtain ⟨y, f⟩ := q
        obtain ⟨hlt, -, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hq
        cases Result.ok_injective h2
        refine ⟨_, lst1, rfl, $hu:term hd (by rw [alloc.vec.Vec.set_val_eq, ConRon.Refine.ExprOps.u64_cast_usize_val hp]), h3, h4⟩
      | Err e =>
        cases Result.ok_injective h2
        exact rdout_err_bind hF rfl))

theorem kind_name {pk bs r pers st lst} {m : alloc.vec.Vec Std.U8} {p : Std.U64} {d t}
    (hr : RegionFits bs r) (hp : p.val ≤ Std.Usize.max) (hd : DSRel d t) :
    BS pers st lst (build_kind_name pk pers st.store bs r m d p)
      (kindT (ConLeche.Frontend.Olean.marked (absM m) kName p.val)
        (nameNode (absPins pk) (absRegion bs r) (8 * p.val) (ConRon.Arena.Frontend.Olean.DS.sub t))
        (ConRon.Arena.Frontend.Olean.DS.setName t p.val) t) := by
  rw [build_kind_name, ← absByte_k_name]
  kind_tac (ds_name_node hr hd), dsrel_name

theorem kind_level {pk bs r pers st lst} {m : alloc.vec.Vec Std.U8} {p : Std.U64} {d t}
    (hr : RegionFits bs r) (hp : p.val ≤ Std.Usize.max) (hd : DSRel d t) :
    BS pers st lst (build_kind_level pk pers st.store bs r m d p)
      (kindT (ConLeche.Frontend.Olean.marked (absM m) kLevel p.val)
        (levelNode (absPins pk) (absRegion bs r) (8 * p.val) (ConRon.Arena.Frontend.Olean.DS.sub t))
        (ConRon.Arena.Frontend.Olean.DS.setLevel t p.val) t) := by
  rw [build_kind_level, ← absByte_k_level]
  kind_tac (ds_level_node hr hd), dsrel_level

theorem kind_levels {pk bs r pers st lst} {m : alloc.vec.Vec Std.U8} {p : Std.U64} {d t}
    (hr : RegionFits bs r) (hp : p.val ≤ Std.Usize.max) (hd : DSRel d t) :
    BS pers st lst (build_kind_levels pk pers st.store bs r m d p)
      (kindT (ConLeche.Frontend.Olean.marked (absM m) kLevels p.val)
        (levelsNode (absPins pk) (absRegion bs r) (8 * p.val) (ConRon.Arena.Frontend.Olean.DS.sub t))
        (ConRon.Arena.Frontend.Olean.DS.setLevels t p.val) t) := by
  rw [build_kind_levels, ← absByte_k_levels]
  kind_tac (ds_levels_node hr hd), dsrel_lists

theorem kind_expr {pk bs r pers st lst} {m : alloc.vec.Vec Std.U8} {p : Std.U64} {d t}
    (hr : RegionFits bs r) (hp : p.val ≤ Std.Usize.max) (hd : DSRel d t) :
    BS pers st lst (build_kind_expr pk pers st.store bs r m d p)
      (kindT (ConLeche.Frontend.Olean.marked (absM m) kExpr p.val)
        (exprNode (absPins pk) (absRegion bs r) (8 * p.val) (ConRon.Arena.Frontend.Olean.DS.sub t))
        (ConRon.Arena.Frontend.Olean.DS.setExpr t p.val) t) := by
  rw [build_kind_expr, ← absByte_k_expr]
  kind_tac (ds_expr_node hr hd), dsrel_expr

/-! ## A slot, the sweep -/

/-- A kind of a slot, then the rest. -/
theorem kind_seq {β : Type} (c : Bool) (y : AM (Option β)) (tset : β → TDS) (t : TDS)
    (g : TDS → AM (Option TDS)) :
    kindT c y tset t >>= seqK g =
      if c then y >>= (fun o => match o with
        | none => pure none
        | some v => g (tset v))
      else g t := by
  unfold kindT
  cases c with
  | false => simp
  | true =>
    simp only [↓reduceIte, bind_assoc]
    congr 1
    funext o
    cases o <;> simp

/-- `buildSlot`, a kind at a time. -/
theorem buildSlot_eq (P : ConRon.Arena.Frontend.Olean.OleanPins) (R : ConLeche.Frontend.Olean.Region)
    (M : ByteArray) (t : TDS) (p : Nat) :
    buildSlot P R M t p =
      kindT (ConLeche.Frontend.Olean.marked M kName p) (nameNode P R (8 * p) (ConRon.Arena.Frontend.Olean.DS.sub t))
        (ConRon.Arena.Frontend.Olean.DS.setName t p) t >>= seqK fun t1 =>
      kindT (ConLeche.Frontend.Olean.marked M kLevel p) (levelNode P R (8 * p) (ConRon.Arena.Frontend.Olean.DS.sub t1))
        (ConRon.Arena.Frontend.Olean.DS.setLevel t1 p) t1 >>= seqK fun t2 =>
      kindT (ConLeche.Frontend.Olean.marked M kLevels p) (levelsNode P R (8 * p) (ConRon.Arena.Frontend.Olean.DS.sub t2))
        (ConRon.Arena.Frontend.Olean.DS.setLevels t2 p) t2 >>= seqK fun t3 =>
      kindT (ConLeche.Frontend.Olean.marked M kExpr p) (exprNode P R (8 * p) (ConRon.Arena.Frontend.Olean.DS.sub t3))
        (ConRon.Arena.Frontend.Olean.DS.setExpr t3 p) t3 := by
  simp only [kind_seq, buildSlot, pure_bind]
  simp only [kindT]
  repeat' first
    | rfl
    | (refine ite_congr rfl (fun _ => ?_) (fun _ => ?_))
    | (refine congrArg (Bind.bind _) (funext fun o => ?_); cases o)

/-- **`build_slot` is `buildSlot`.** -/
theorem build_slot_bs {pk bs r pers st lst} {m : alloc.vec.Vec Std.U8} {p : Std.U64} {d t}
    (hr : RegionFits bs r) (hp : p.val ≤ Std.Usize.max) (hd : DSRel d t) :
    BS pers st lst (build_slot pk pers st.store bs r m d p)
      (buildSlot (absPins pk) (absRegion bs r) (absM m) t p.val) := by
  rw [build_slot, buildSlot_eq]
  refine BS.bind (kind_name hr hp hd) fun s1 d1 t1 lst1 h1 => ?_
  refine BS.bind (kind_level hr hp h1) fun s2 d2 t2 lst2 h2 => ?_
  refine BS.bind (kind_levels hr hp h2) fun s3 d3 t3 lst3 h3 => ?_
  exact kind_expr hr hp h3

/-- `build_marked`, the test of a slot of `buildPass`. -/
theorem build_marked_bs {pk bs r pers st lst} {m : alloc.vec.Vec Std.U8} {p : Std.U64} {d t}
    (hr : RegionFits bs r) (hp : p.val ≤ Std.Usize.max) (hd : DSRel d t) :
    BS pers st lst (build_marked pk pers st.store bs r m d p)
      (if (marksAt (absM m) p.val != 0) = true then
        buildSlot (absPins pk) (absRegion bs r) (absM m) t p.val
       else pure (some t)) := by
  rw [build_marked]
  refine BS.pure_step fun i hi => ?_
  rw [← marks_at_eq hi, ← absByte_bne_zero]
  split
  · exact build_slot_bs hr hp hd
  · exact BS.leaf hd

/-- **`build_pass` is `buildPass`.** -/
theorem build_pass_loop_bs {pk bs r pers} {m : alloc.vec.Vec Std.U8} {n : Std.U64}
    (hr : RegionFits bs r) (hn : n.val ≤ Std.Usize.max) :
    ∀ (f : Nat) {st lst} {p : Std.U64} {d t}, n.val - p.val ≤ f → DSRel d t →
      BS pers st lst (build_pass_loop pk pers st.store bs r m n d p)
        (buildPass (absPins pk) (absRegion bs r) (absM m) n.val t p.val) := by
  intro f
  induction f with
  | zero =>
    intro st lst p d t hf hd
    rw [build_pass_loop, buildPass, ite_eq_right (by scalar_tac), ite_eq_right (by omega)]
    exact BS.leaf hd
  | succ f ih =>
    intro st lst p d t hf hd
    rw [build_pass_loop, buildPass]
    by_cases hlt : p < n
    · have hlt' : p.val < n.val := hlt
      rw [ite_eq_left hlt, ite_eq_left hlt']
      refine BS.of_eq (BS.bind (build_marked_bs hr (by omega) hd)
        (g := fun t1 => buildPass (absPins pk) (absRegion bs r) (absM m) n.val t1 (p.val + 1))
        fun s1 d1 t1 lst1 h1 => ?_) ?_
      rotate_left
      · split
        · rfl
        · simp
      refine BS.pure_step fun p1 hp1 => ?_
      have hv := uscalar_add_eq hp1
      have l : (1#u64 : Std.U64).val = 1 := by decide
      rw [show p.val + 1 = p1.val by omega]
      exact ih (st := withStore st s1) (by omega) h1
    · have hlt' : ¬ p.val < n.val := hlt
      rw [ite_eq_right hlt, ite_eq_right hlt']
      exact BS.leaf hd

/-! ## Both passes -/

/-- `RS` from `BS`: the memo is the answer. -/
theorem RS.of_BS {pers st lst} {f} {x : AM (Option TDS)} (h : BS pers st lst f x) :
    RS pers DSRel st lst
      (do
        let (r1, ar1, st1) ← f
        match r1 with
        | .Ok _ => ok (.Ok st1, ar1)
        | .Err e => ok (.Err e, ar1)) x := by
  intro hrel hinv o s' hm
  obtain ⟨⟨r1, ar1, d1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hF := h hrel hinv r1 ar1 d1 h1
  cases r1 with
  | Ok u =>
    cases Result.ok_injective h2
    exact hF
  | Err e =>
    cases Result.ok_injective h2
    cases e with
    | Bad => exact hF
    | Err e => exact hF

theorem usize_max_ge : 4294967295 ≤ Std.Usize.max := by scalar_tac

/-- **`run_passes` is `runPasses`.** -/
theorem run_passes_refines {pk bs r pers st lst} {names exprs : alloc.vec.Vec Std.U64}
    (hr : RegionFits bs r) :
    RS pers DSRel st lst (run_passes pk pers st.store bs r names exprs)
      (runPasses (absPins pk) (absRegion bs r) (names.val.map absWord) (exprs.val.map absWord)) := by
  rw [run_passes]
  simp only [runPasses]
  refine RS.pure_step fun i hi => RS.pure_step fun i1 hi1 => RS.pure_step fun i2 hi2 =>
    RS.pure_step fun n hn => ?_
  have e1 := max_loc_eq (bs := bs) hi
  have e2 := max_loc_eq (bs := bs) hi1
  have l0 : (0#u64 : Std.U64).val = 0 := by decide
  rw [l0] at e1
  rw [e1] at e2
  have v2 := uscalar_div_eq hi2
  rw [u64_val_lit8] at v2
  have v3 := uscalar_add_eq hn
  have l1 : (1#u64 : Std.U64).val = 1 := by decide
  have hLn : n.val = maxLoc (absRegion bs r) (exprs.val.map absWord)
      (maxLoc (absRegion bs r) (names.val.map absWord) 0) / 8 + 1 := by omega
  have hle := maxLoc_le hr (exprs.val.map absWord) (maxLoc_le hr (names.val.map absWord) (Nat.zero_le _))
  have hL := bytes_le_max bs
  have hmx := usize_max_ge
  have hnm : n.val ≤ Std.Usize.max := by omega
  have hc := ConRon.Refine.ExprOps.u64_cast_usize_val hnm
  rw [← hLn]
  simp only [lift, bind_ok]
  refine RS.pure_step fun m hm => ?_
  have ez := zeros_eq hm
  rw [hc] at ez
  rw [← ez]
  refine RS.pure_step fun q1 hq1 => ?_
  obtain ⟨b, m1⟩ := q1
  rw [← absByte_k_name, mark_roots_eq hr hq1]
  cases b with
  | false => exact RS.none
  | true =>
    simp only [↓reduceIte, rootAbs]
    refine RS.pure_step fun q2 hq2 => ?_
    obtain ⟨b1, m2⟩ := q2
    rw [← absByte_k_expr, mark_roots_eq hr hq2]
    cases b1 with
    | false => exact RS.none
    | true =>
      simp only [↓reduceIte, rootAbs]
      refine RS.pure_step fun m3 hm3 => ?_
      have em := mark_pass_ms hr m3 hm3
      rw [← em]
      refine RS.pure_step fun b2 hb2 => ?_
      rw [← failed_m_eq hb2]
      cases b2 with
      | true => exact RS.none
      | false =>
        simp only [↓reduceIte, Bool.false_eq_true]
        refine RS.pure_step fun d0 hd0 => ?_
        have hf := ds_fresh_rel hd0
        rw [hc] at hf
        have hb := build_pass_loop_bs (pk := pk) (pers := pers) (m := m3) hr hnm _ (st := st) (lst := lst)
          (p := 0#u64) (Nat.le_refl _) hf
        exact RS.of_BS (by rw [build_pass]; exact hb)

end ConRon.Refine2.Frontend.Olean
