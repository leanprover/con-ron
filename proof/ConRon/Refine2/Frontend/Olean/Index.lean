/-
# `ConRon.Refine2.Frontend.Olean.Index` — `olean/index.rs`: the worker's reads

**Task #166, Theorem 2.**  The names a module's environment holds, against the twin's
(`Arena/Frontend/Olean/Index.lean`).

**The relations.**  A `Copy` is upstream's (`absCopy`); the name index is `NameIndexRel`: the
parts abstracted, `first` an `NMapRel` (its copies fitting a `usize`, `CopyFits`), `more` as a
list.  A `HashMap2` keyed by copies is a `Std.HashMap Copy` (`CMapRel`).  The store-free
functions are equations; the reads claim their accept (`AS`).

**`usize` casts.**  `index.rs` turns a copy's `u64` fields back into `usize` indices; a
cast keeps the value when it fits a `usize`, which every copy the index makes does (it is a
`usize` position, cast up): `CopyFits`, carried by `NameIndexRel`.
-/
import ConRon.Refine2.Frontend.Olean.Levels
import ConRon.Refine2.Frontend.Olean.PartNames
import ConRon.Arena.Frontend.Olean.Index

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.index

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap2 (Inv toFun)
open ConRon.Refine.HashMap (Eq2Fwd)

/-! ## Casts -/

/-- A `usize` cast up to a `u64` keeps its value. -/
theorem cast_u64_val (x : Std.Usize) : (UScalar.cast .U64 x : Std.U64).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_greater_numBits_eq _ _ ?_
  rw [UScalarTy.Usize_numBits_eq, UScalarTy.U64_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> omega

/-- A `u64` cast down to a `usize` keeps its value when it fits. -/
theorem cast_usize_val {x : Std.U64} (h : x.val ≤ Std.Usize.max) :
    (UScalar.cast .Usize x : Std.Usize).val = x.val := by
  rw [Std.UScalar.cast_val_eq, Std.UScalarTy.Usize_numBits_eq]
  refine Nat.mod_eq_of_lt ?_
  have hmax : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
    simp only [Std.Usize.max, Std.Usize.numBits, Std.UScalarTy.Usize_numBits_eq]
  have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  omega

theorem usize_le_max (x : Std.Usize) : x.val ≤ Std.Usize.max := by
  have := x.hmax
  simp only [Std.Usize.max, Std.Usize.numBits] at *
  omega

theorem vec_len_le_max {α : Type} (v : alloc.vec.Vec α) : v.val.length ≤ Std.Usize.max :=
  v.property

theorem lt_of_not_lt_len {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (h : ¬ i < alloc.vec.Vec.len v) : v.val.length ≤ i.val := by
  have : ¬ i.val < (alloc.vec.Vec.len v).val := h
  rw [vec_len_val] at this; omega

theorem lt_of_lt_len {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (h : i < alloc.vec.Vec.len v) : i.val < v.val.length := by
  have : i.val < (alloc.vec.Vec.len v).val := h
  rwa [vec_len_val] at this

theorem usize_succ {i j : Std.Usize} (h : i + 1#usize = ok j) : j.val = i.val + 1 := by
  rw [ConRon.Refine.Nat.uadd_val h]; rfl

/-! ## Copies -/

deriving instance DecidableEq for frontend.olean.index.Copy

/-- `index::Copy`, as upstream's. -/
@[reducible] def absCopy (c : frontend.olean.index.Copy) : ConLeche.Frontend.Olean.Copy :=
  ⟨c.module.val, c.pos.val⟩

theorem absCopy_inj {a b : frontend.olean.index.Copy} (h : absCopy a = absCopy b) : a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [absCopy, ConLeche.Frontend.Olean.Copy.mk.injEq] at h
  rw [UScalar.eq_of_val_eq h.1, UScalar.eq_of_val_eq h.2]

theorem copy_beq_iff (a b : ConLeche.Frontend.Olean.Copy) : (a == b) = true ↔ a = b := by
  cases a; cases b
  show (_ && _) = true ↔ _
  simp

instance : LawfulBEq ConLeche.Frontend.Olean.Copy where
  eq_of_beq h := (copy_beq_iff _ _).1 h
  rfl := (copy_beq_iff _ _).2 rfl

/-- The hash of copies. -/
abbrev hC := frontend.olean.index.Copy.Insts.Con_ron_coreRonHashmapHashable
/-- The equality of copies. -/
abbrev eC := frontend.olean.index.Copy.Insts.Con_ron_coreRonHashmapEq2

/-- **`Copy`'s `eq2` is equality.** -/
theorem copy_eq2 : Eq2Fwd eC (fun _ => True) := by
  intro a b c _ _ h
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  change Copy.Insts.Con_ron_coreRonHashmapEq2.eq2 _ _ = ok c at h
  rw [Copy.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  by_cases e : a1 = b1
  · rw [ite_eq_left e] at h
    cases Result.ok_injective h
    subst e
    by_cases e2 : a2 = b2 <;> simp [e2]
  · rw [ite_eq_right e] at h
    cases Result.ok_injective h
    simp [e]

/-- **`Copy`'s `dup2` is the identity.** -/
theorem copy_dup2_ok {c x : frontend.olean.index.Copy}
    (h : Copy.Insts.Con_ron_coreRonHashmapDup.dup2 c = ok x) : x = c :=
  (Result.ok_injective (show ok c = ok x from h)).symm

/-- A copy whose fields fit a `usize`. -/
def CopyFits (c : frontend.olean.index.Copy) : Prop :=
  c.module.val ≤ Std.Usize.max ∧ c.pos.val ≤ Std.Usize.max

/-! ## Tables keyed by copies -/

/-- **A `HashMap2` keyed by copies**, as a `Std.HashMap` of upstream's copies, the values
related by `R`. -/
structure CMapRel {V V' : Type} (R : V → V' → Prop) (m : ron.hashmap2.HashMap2 frontend.olean.index.Copy V)
    (s : _root_.Std.HashMap ConLeche.Frontend.Olean.Copy V') : Prop where
  inv : Inv hC m
  get : ∀ k, Option.Rel R (toFun m k) s[absCopy k]?

section CMapRel
variable {V V' : Type} {R : V → V' → Prop} {m : ron.hashmap2.HashMap2 frontend.olean.index.Copy V}
  {s : _root_.Std.HashMap ConLeche.Frontend.Olean.Copy V'}

theorem CMapRel.get_eq (h : CMapRel R m s) {k : frontend.olean.index.Copy} {o : Option V}
    (hg : ron.hashmap2.HashMap2.get hC eC m k = ok o) : Option.Rel R o s[absCopy k]? := by
  rw [ConRon.Refine.HashMap2.get_refines_gen copy_eq2 h.inv (fun _ _ => trivial) trivial hg]
  exact h.get k

theorem CMapRel.insert (h : CMapRel R m s) {k : frontend.olean.index.Copy} {v : V} {v' : V'}
    (hv : R v v') {old} {m'} (hi : ron.hashmap2.HashMap2.insert hC eC m k v = ok (old, m')) :
    CMapRel R m' (s.insert (absCopy k) v') := by
  obtain ⟨hinv, -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen copy_eq2
    h.inv (fun _ _ => trivial) trivial hi
  refine ⟨hinv, fun k1 => ?_⟩
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
  by_cases hk : k1 = k
  · subst hk; simpa using Option.Rel.some hv
  · have hne : (absCopy k == absCopy k1) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (absCopy_inj he).symm
    rw [ite_eq_right hk, hne]
    simpa using h.get k1

theorem CMapRel.with_capacity {c : Std.Usize}
    (hn : ron.hashmap2.HashMap2.with_capacity frontend.olean.index.Copy V c = ok m) :
    CMapRel R m {} := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.with_capacity_refines (HashableInst := hC) hn
  exact ⟨hinv, fun k => by rw [hnone]; simp⟩

end CMapRel

/-! ## The name index -/

/-- A later copy, as the twin's. -/
@[reducible] def absMore (p : arena.handle.NIdx × frontend.olean.index.Copy) :
    NIdx × ConLeche.Frontend.Olean.Copy := (absNIdx p.1, absCopy p.2)

/-- `first`: an `NMapRel` whose copies fit. -/
structure FirstRel (m : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.olean.index.Copy)
    (s : _root_.Std.HashMap NIdx ConLeche.Frontend.Olean.Copy) : Prop where
  rel : NMapRel absCopy m s
  fits : ∀ k c, toFun m k = some c → CopyFits c

/-- **`index::NameIndex` against the twin's.** -/
structure NameIndexRel (ix : frontend.olean.index.NameIndex) (ix' : Arena.Frontend.Olean.NameIndex) :
    Prop where
  parts : ix.parts.val.map absNamePositions = ix'.parts.toList
  first : FirstRel ix.first ix'.first
  more : ix.more.val.map absMore = ix'.more.toList
  fitsM : ∀ p ∈ ix.more.val, CopyFits p.2

theorem FirstRel.get_eq {m s} (h : FirstRel m s) {k : arena.handle.NIdx} {o}
    (hg : ron.hashmap2.HashMap2.get hN eN m k = ok o) :
    o.map absCopy = s[absNIdx k]? ∧ ∀ c, o = some c → CopyFits c := by
  have e := ConRon.Refine.HashMap2.get_refines_gen nidx_eq2 h.rel.inv (fun _ _ => trivial) trivial hg
  refine ⟨by rw [e]; exact h.rel.get k, fun c hc => h.fits k c (by rw [← e]; exact hc)⟩

theorem FirstRel.insert {m s} (h : FirstRel m s) {k : arena.handle.NIdx} {v} {old} {m'}
    (hv : CopyFits v) (hi : ron.hashmap2.HashMap2.insert hN eN m k v = ok (old, m')) :
    FirstRel m' (s.insert (absNIdx k) (absCopy v)) := by
  obtain ⟨-, -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2
    h.rel.inv (fun _ _ => trivial) trivial hi
  refine ⟨h.rel.insert hi, fun k1 c hc => ?_⟩
  rw [hupd, Function.update_apply] at hc
  by_cases hk : k1 = k
  · rw [ite_eq_left hk] at hc; cases hc; exact hv
  · rw [ite_eq_right hk] at hc; exact h.fits k1 c hc

/-- **`name_index_at` is `NameIndex.at`**, at a copy that fits. -/
theorem name_index_at_eq {ix ix'} (hix : NameIndexRel ix ix') {c : frontend.olean.index.Copy}
    (hc : CopyFits c) {o} (h : name_index_at ix c = ok o) :
    o.map absNamePosition = ix'.at (absCopy c) := by
  rw [name_index_at] at h
  peel h as m, hm
  have em : m.val = c.module.val := by rw [← Result.ok_injective hm]; exact cast_usize_val hc.1
  have hp : ix'.parts[c.module.val]? = (ix.parts.val[c.module.val]?).map absNamePositions := by
    have := congrArg (·[c.module.val]?) hix.parts
    simp only [List.getElem?_map] at this
    rw [← Array.getElem?_toList]; exact this.symm
  rw [Arena.Frontend.Olean.NameIndex.at, hp]
  by_cases h1 : m < alloc.vec.Vec.len ix.parts
  · rw [ite_eq_left h1] at h
    have h1' := lt_of_lt_len h1
    peel h as p, hpp
    have ep : p.val = c.pos.val := by rw [← Result.ok_injective hpp]; exact cast_usize_val hc.2
    peel h as np, hnp
    obtain ⟨_, rfl⟩ := vec_index_eq hnp
    simp only [← em, List.getElem?_eq_getElem h1', Option.map_some, Option.bind_some,
      absNamePositions_consts_getElem?]
    by_cases h2 : p < alloc.vec.Vec.len (ix.parts.val[m.val]).consts
    · rw [ite_eq_left h2] at h
      have h2' := lt_of_lt_len h2
      peel h as q, hq
      obtain ⟨_, rfl⟩ := vec_index_eq hq
      cases Result.ok_injective h
      simp [← ep, List.getElem?_eq_getElem h2']
    · rw [ite_eq_right h2] at h
      cases Result.ok_injective h
      have := lt_of_not_lt_len h2
      simp [← ep, List.getElem?_eq_none this]
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    have := lt_of_not_lt_len h1
    rw [em] at this
    simp [List.getElem?_eq_none this]

/-- **`name_index_loc` is `(ix.at c).map (·.loc)`.** -/
theorem name_index_loc_eq {ix ix'} (hix : NameIndexRel ix ix') {c : frontend.olean.index.Copy}
    (hc : CopyFits c) {o} (h : name_index_loc ix c = ok o) :
    o.map (·.val) = (ix'.at (absCopy c)).map (·.loc) := by
  rw [name_index_loc] at h
  peel h as o1, h1
  rw [← name_index_at_eq hix hc h1]
  cases o1 <;> cases Result.ok_injective h <;> rfl

/-! ### `name_index_of` -/

/-- The twin's inner step of `nameIndexOf`. -/
def nioInner (i : Nat) (acc : Std.HashMap NIdx ConLeche.Frontend.Olean.Copy ×
    _root_.Array (NIdx × ConLeche.Frontend.Olean.Copy) × Nat) (q : Arena.Frontend.Olean.NamePosition) :
    Std.HashMap NIdx ConLeche.Frontend.Olean.Copy × _root_.Array (NIdx × ConLeche.Frontend.Olean.Copy) × Nat :=
  if acc.1.contains q.name then (acc.1, acc.2.1.push (q.name, ⟨i, acc.2.2⟩), acc.2.2 + 1)
  else (acc.1.insert q.name ⟨i, acc.2.2⟩, acc.2.1, acc.2.2 + 1)

/-- The twin's outer step of `nameIndexOf`. -/
def nioOuter (acc : Std.HashMap NIdx ConLeche.Frontend.Olean.Copy ×
    _root_.Array (NIdx × ConLeche.Frontend.Olean.Copy) × Nat) (p : Arena.Frontend.Olean.NamePositions) :
    Std.HashMap NIdx ConLeche.Frontend.Olean.Copy × _root_.Array (NIdx × ConLeche.Frontend.Olean.Copy) × Nat :=
  let r := p.consts.foldl (nioInner acc.2.2) (acc.1, acc.2.1, 0)
  (r.1, r.2.1, acc.2.2 + 1)

theorem nameIndexOf_eq (parts : _root_.Array Arena.Frontend.Olean.NamePositions) :
    Arena.Frontend.Olean.nameIndexOf parts =
      let r := parts.foldl nioOuter ({}, #[], 0)
      { parts, first := r.1, more := r.2.1 } := rfl

theorem name_index_of_loop1_loop0_eq (first : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.olean.index.Copy)
    (more : alloc.vec.Vec (arena.handle.NIdx × frontend.olean.index.Copy)) (i : Std.Usize)
    (cs : alloc.vec.Vec frontend.olean.reads.NamePosition) (k : Std.Usize) {F M}
    (hF : FirstRel first F) (hM : more.val.map absMore = M.toList) (hfM : ∀ p ∈ more.val, CopyFits p.2)
    {o} (h : name_index_of_loop1_loop0 first more i cs k = ok o) :
    let r := ((cs.val.drop k.val).map absNamePosition).foldl (nioInner i.val) (F, M, k.val)
    FirstRel o.1 r.1 ∧ o.2.val.map absMore = r.2.1.toList ∧ ∀ p ∈ o.2.val, CopyFits p.2 := by
  rw [name_index_of_loop1_loop0] at h
  by_cases hlt : k < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    have hk := lt_of_lt_len hlt
    peel h as i2, hi2
    cases Result.ok_injective hi2
    peel h as i3, hi3
    cases Result.ok_injective hi3
    have fits : CopyFits ⟨UScalar.cast .U64 i, UScalar.cast .U64 k⟩ := by
      simp only [CopyFits, cast_u64_val]; exact ⟨usize_le_max i, usize_le_max k⟩
    have eabs : absCopy ⟨UScalar.cast .U64 i, UScalar.cast .U64 k⟩ = ⟨i.val, k.val⟩ := by
      simp [absCopy]
    peel h as np, hnp
    obtain ⟨_, rfl⟩ := vec_index_eq hnp
    peel h as b, hb
    have eb := hF.rel.contains_eq hb
    rw [List.drop_eq_getElem_cons hk, List.map_cons, List.foldl_cons]
    peel h as q, hq
    obtain ⟨first1, more1⟩ := q
    peel h as k1, hk1
    have ek1 := usize_succ hk1
    by_cases cb : b = true
    · rw [ite_eq_left cb] at hq
      peel hq as n, hn
      cases nidx_dup2_ok hn
      peel hq as more2, hmore2
      have e := Result.ok_injective hq
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      subst e1 e2
      have hM' : more2.val.map absMore = (M.push (absNIdx cs.val[k.val].name, ⟨i.val, k.val⟩)).toList := by
        rw [ConRon.Refine.vec_push_val hmore2]; simp [hM, eabs]
      have hfM' : ∀ p ∈ more2.val, CopyFits p.2 := by
        rw [ConRon.Refine.vec_push_val hmore2]
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hfM p hp
        · rw [List.mem_singleton.mp hp]; exact fits
      have ih := name_index_of_loop1_loop0_eq first more2 i cs k1 hF hM' hfM' h
      rw [ek1] at ih
      have : nioInner i.val (F, M, k.val) (absNamePosition cs.val[k.val]) =
          (F, M.push (absNIdx cs.val[k.val].name, ⟨i.val, k.val⟩), k.val + 1) := by
        simp [nioInner, ← eb, cb]
      rw [this]; exact ih
    · rw [ite_eq_right cb] at hq
      peel hq as n, hn
      cases nidx_dup2_ok hn
      peel hq as q2, hq2
      obtain ⟨old, first2⟩ := q2
      have e := Result.ok_injective hq
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      subst e1 e2
      have hF' := hF.insert fits hq2
      rw [eabs] at hF'
      have ih := name_index_of_loop1_loop0_eq first2 more i cs k1 hF' hM hfM h
      rw [ek1] at ih
      have : nioInner i.val (F, M, k.val) (absNamePosition cs.val[k.val]) =
          (F.insert (absNIdx cs.val[k.val].name) ⟨i.val, k.val⟩, M, k.val + 1) := by
        have cb' : b = false := by simpa using cb
        simp [nioInner, ← eb, cb']
      rw [this]; exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    exact ⟨hF, hM, hfM⟩
termination_by cs.val.length - k.val
decreasing_by
  all_goals
    have := lt_of_lt_len hlt
    omega

theorem name_index_of_loop1_eq (parts : alloc.vec.Vec frontend.olean.reads.NamePositions)
    (first : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.olean.index.Copy)
    (more : alloc.vec.Vec (arena.handle.NIdx × frontend.olean.index.Copy)) (i : Std.Usize) {F M}
    (hF : FirstRel first F) (hM : more.val.map absMore = M.toList) (hfM : ∀ p ∈ more.val, CopyFits p.2)
    {o} (h : name_index_of_loop1 parts first more i = ok o) :
    let r := ((parts.val.drop i.val).map absNamePositions).foldl nioOuter (F, M, i.val)
    FirstRel o.1 r.1 ∧ o.2.val.map absMore = r.2.1.toList ∧ ∀ p ∈ o.2.val, CopyFits p.2 := by
  rw [name_index_of_loop1] at h
  by_cases hlt : i < alloc.vec.Vec.len parts
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as np, hnp
    obtain ⟨_, rfl⟩ := vec_index_eq hnp
    peel h as q, hq
    obtain ⟨first1, more1⟩ := q
    peel h as i2, hi2
    have ei2 := usize_succ hi2
    obtain ⟨h1, h2, h3⟩ := name_index_of_loop1_loop0_eq first more i _ 0#usize hF hM hfM hq
    have ih := name_index_of_loop1_eq parts first1 more1 i2 h1 h2 h3 h
    rw [ei2] at ih
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldl_cons]
    have e0 : (0#usize : Std.Usize).val = 0 := rfl
    simp only [e0, List.drop_zero] at ih ⊢
    have : nioOuter (F, M, i.val) (absNamePositions parts.val[i.val]) =
        ((((parts.val[i.val]).consts.val.map absNamePosition).foldl (nioInner i.val) (F, M, 0)).1,
         (((parts.val[i.val]).consts.val.map absNamePosition).foldl (nioInner i.val) (F, M, 0)).2.1,
         i.val + 1) := by
      simp [nioOuter, absNamePositions]
    rw [this]; exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    exact ⟨hF, hM, hfM⟩
termination_by parts.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`name_index_of` is `nameIndexOf`.** -/
theorem name_index_of_eq {parts : alloc.vec.Vec frontend.olean.reads.NamePositions} {ix}
    (h : name_index_of parts = ok ix) :
    NameIndexRel ix (Arena.Frontend.Olean.nameIndexOf (parts.val.map absNamePositions).toArray) := by
  rw [name_index_of] at h
  peel h as total, -
  peel h as first, hfirst
  peel h as q, hq
  obtain ⟨first1, more⟩ := q
  cases Result.ok_injective h
  have hF : FirstRel first {} := ⟨NMapRel.with_capacity hfirst, fun k c hc => by
    obtain ⟨-, -, hnone⟩ := ConRon.Refine.HashMap2.with_capacity_refines (HashableInst := hN) hfirst
    rw [hnone] at hc; cases hc⟩
  have e0 : (alloc.vec.Vec.new (arena.handle.NIdx × frontend.olean.index.Copy)).val = [] := rfl
  obtain ⟨h1, h2, h3⟩ := name_index_of_loop1_eq parts first _ 0#usize hF
    (M := #[]) (by rw [e0]; rfl) (by rw [e0]; simp) hq
  rw [nameIndexOf_eq]
  simp only [List.foldl_toArray] at *
  exact ⟨by simp, h1, h2, h3⟩

/-! ## Duplicates -/

/-- **`stmt_rec_dup` is the identity.** -/
theorem stmt_rec_dup_eq {s r : frontend.olean.spec.StmtRec} (h : stmt_rec_dup s = ok r) : r = s := by
  rw [stmt_rec_dup] at h
  peel h as n, hn
  cases nidx_dup2_ok hn
  peel h as v, hv
  have := ConRon.Refine2.nidx_vec_dup_val hv
  peel h as e, he
  cases eidx_dup2_ok he
  cases Result.ok_injective h
  rw [alloc.vec.Vec.ext _ _ this]

theorem c_kind_names_dup_loop_eq (rules rs : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × Unit))
    (i : Std.Usize) {o} (h : c_kind_names_dup_loop rules rs i = ok o) :
    o.val = rs.val ++ rules.val.drop i.val := by
  rw [c_kind_names_dup_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len rules
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as x, hx
    obtain ⟨_, hxe⟩ := vec_index_eq hx
    obtain ⟨n, j, u⟩ := x
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as rs1, hrs1
    peel h as i3, hi3
    have ei3 := usize_succ hi3
    have := c_kind_names_dup_loop_eq rules rs1 i3 h
    rw [this, ConRon.Refine.vec_push_val hrs1, usize_succ hi3, List.drop_eq_getElem_cons hi, ← hxe]
    simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    simp
termination_by rules.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`c_kind_names_dup` is the identity.** -/
theorem c_kind_names_dup_eq {k r : frontend.olean.spec.CKindF arena.handle.NIdx Unit}
    (h : c_kind_names_dup k = ok r) : r = k := by
  cases k with
  | Ax u => exact (Result.ok_injective h).symm
  | Defn v hh s =>
    rw [c_kind_names_dup] at h
    peel h as hr, hhr
    cases hints_dup_val hhr
    peel h as v1, hv1
    cases ConRon.Refine.Expr.str_copy_eq hv1
    cases Result.ok_injective h
    rfl
  | Thm v all =>
    rw [c_kind_names_dup] at h
    peel h as v1, hv1
    have := ConRon.Refine2.nidx_vec_dup_val hv1
    cases Result.ok_injective h
    rw [alloc.vec.Vec.ext _ _ this]
  | Opaq v u => exact (Result.ok_injective h).symm
  | Quot s =>
    rw [c_kind_names_dup] at h
    peel h as v1, hv1
    cases ConRon.Refine.Expr.str_copy_eq hv1
    cases Result.ok_injective h
    rfl
  | Induct np ni all cs nn ir iu irf =>
    rw [c_kind_names_dup] at h
    peel h as v1, hv1
    peel h as v2, hv2
    have e1 := ConRon.Refine2.nidx_vec_dup_val hv1
    have e2 := ConRon.Refine2.nidx_vec_dup_val hv2
    cases Result.ok_injective h
    rw [alloc.vec.Vec.ext _ _ e1, alloc.vec.Vec.ext _ _ e2]
  | Ctor ind ci np nf iu =>
    rw [c_kind_names_dup] at h
    peel h as n, hn
    cases nidx_dup2_ok hn
    cases Result.ok_injective h
    rfl
  | Recur all np ni nmo nmi rules k2 iu =>
    rw [c_kind_names_dup] at h
    peel h as rs1, hrs1
    have e1 := c_kind_names_dup_loop_eq rules _ 0#usize hrs1
    peel h as v1, hv1
    have e2 := ConRon.Refine2.nidx_vec_dup_val hv1
    cases Result.ok_injective h
    have e0 : (alloc.vec.Vec.with_capacity (arena.handle.NIdx × Std.U64 × Unit)
      (alloc.vec.Vec.len rules)).val = [] := rfl
    rw [e0] at e1
    rw [alloc.vec.Vec.ext _ _ e2, alloc.vec.Vec.ext rs1 rules (by simpa using e1)]

/-! ## The header's loads, by position -/

/-- **`header_loads_name_at` is `HeaderLoads.nameAt`**, at a position that fits. -/
theorem header_loads_name_at_eq {pk : frontend.olean.spec.OleanPins} {ld ld'} (hld : HeaderLoadsRel ld ld')
    {i : Std.U64} (hi : i.val ≤ Std.Usize.max) {n} (h : header_loads_name_at pk ld i = ok n) :
    absNIdx n = ld'.nameAt (absPins pk) i.val := by
  rw [header_loads_name_at] at h
  peel h as k, hk
  have ei : k.val = i.val := by rw [← Result.ok_injective hk]; exact cast_usize_val hi
  have ho : ld'.order[i.val]? = (ld.order.val[i.val]?).map absNIdx := by
    have := congrArg (·[i.val]?) hld.order
    simp only [List.getElem?_map] at this
    rw [← Array.getElem?_toList]; exact this.symm
  rw [Arena.Frontend.Olean.HeaderLoads.nameAt, ho]
  by_cases h1 : k < alloc.vec.Vec.len ld.order
  · rw [ite_eq_left h1] at h
    have h1' := lt_of_lt_len h1
    rw [ei] at h1'
    peel h as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    cases nidx_dup2_ok h
    simp [ei, List.getElem?_eq_getElem h1']
  · rw [ite_eq_right h1] at h
    cases nidx_dup2_ok h
    have := lt_of_not_lt_len h1
    rw [ei] at this
    simp [List.getElem?_eq_none this, absPins]

/-- **`header_loads_level_at` is `HeaderLoads.levelAt`**, at a position that fits. -/
theorem header_loads_level_at_eq {ld ld'} (hld : HeaderLoadsRel ld ld')
    {i : Std.U64} (hi : i.val ≤ Std.Usize.max) {l} (h : header_loads_level_at ld i = ok l) :
    absLevel l = ld'.levelAt i.val := by
  rw [header_loads_level_at] at h
  peel h as k, hk
  have ei : k.val = i.val := by rw [← Result.ok_injective hk]; exact cast_usize_val hi
  have ho : ld'.flags[i.val]? = (ld.flags.val[i.val]?).map absLoadFlags := by
    have := congrArg (·[i.val]?) hld.flags
    simp only [List.getElem?_map] at this
    rw [← Array.getElem?_toList]; exact this.symm
  rw [Arena.Frontend.Olean.HeaderLoads.levelAt, ho]
  by_cases h1 : k < alloc.vec.Vec.len ld.flags
  · rw [ite_eq_left h1] at h
    have h1' := lt_of_lt_len h1
    rw [ei] at h1'
    peel h as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    rw [load_flags_level_eq h]
    simp [ei, List.getElem?_eq_getElem h1']
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    have := lt_of_not_lt_len h1
    rw [ei] at this
    simp [List.getElem?_eq_none this, absLevel]
    rfl

/-! ## The doubly held names -/

theorem map_set_eq_modify {α β : Type} (A : α → β) (l : List α) (k : Nat) (x : α) (f : β → β)
    (hk : k < l.length) (hx : A x = f (A l[k])) : (l.set k x).map A = (l.map A).modify k f := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_set, List.getElem?_modify]
  by_cases e : k = j
  · subst e; simp [hk, hx]
  · simp [e]

/-- **`first_or` is `(ix.first[n]?).getD c`.** -/
theorem first_or_eq {ix ix'} (hix : NameIndexRel ix ix') {n : arena.handle.NIdx}
    {c : frontend.olean.index.Copy} {r} (h : first_or ix n c = ok r) :
    absCopy r = (ix'.first[absNIdx n]?).getD (absCopy c) ∧ (CopyFits c → CopyFits r) := by
  rw [first_or] at h
  peel h as o, ho
  obtain ⟨e, hf⟩ := hix.first.get_eq ho
  rw [← e]
  cases o with
  | none => cases copy_dup2_ok h; exact ⟨rfl, id⟩
  | some f => cases copy_dup2_ok h; exact ⟨rfl, fun _ => hf _ rfl⟩

/-- **`at_of` is `at[n]?`.** -/
theorem at_of_eq {at_ : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64} {A : Std.HashMap NIdx Nat}
    (ha : NMapRel (fun x : Std.U64 => x.val) at_ A) {n : arena.handle.NIdx} {o}
    (h : at_of at_ n = ok o) :
    o.map (·.val) = A[absNIdx n]? ∧ ∀ k, o = some k → toFun at_ n = some k := by
  rw [at_of] at h
  peel h as o1, h1
  have e := ConRon.Refine.HashMap2.get_refines_gen nidx_eq2 ha.inv (fun _ _ => trivial) trivial h1
  have hA := ha.get_eq h1
  cases o1 with
  | none => cases Result.ok_injective h; exact ⟨hA, fun _ h => by cases h⟩
  | some k => cases Result.ok_injective h; exact ⟨hA, fun _ h => by rw [← e, h]⟩

/-- A name's copies, as the twin's. -/
@[reducible] def absCC (p : arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy) :
    NIdx × _root_.Array ConLeche.Frontend.Olean.Copy := (absNIdx p.1, (p.2.val.map absCopy).toArray)

/-- The twin's step of `clashCopies`. -/
def ccStep (ix' : Arena.Frontend.Olean.NameIndex)
    (acc : Std.HashMap NIdx Nat × _root_.Array (NIdx × _root_.Array ConLeche.Frontend.Olean.Copy))
    (p : NIdx × ConLeche.Frontend.Olean.Copy) :
    Std.HashMap NIdx Nat × _root_.Array (NIdx × _root_.Array ConLeche.Frontend.Olean.Copy) :=
  match acc.1[p.1]? with
  | some k => (acc.1, acc.2.modify k fun q => (q.1, q.2.push p.2))
  | none => (acc.1.insert p.1 acc.2.size, acc.2.push (p.1, #[(ix'.first[p.1]?).getD p.2, p.2]))

theorem clashCopies_eq (ix' : Arena.Frontend.Olean.NameIndex) :
    Arena.Frontend.Olean.clashCopies ix' = (ix'.more.toList.foldl (ccStep ix') ({}, #[])).2 := by
  rw [Arena.Frontend.Olean.clashCopies, ← Array.foldl_toList]
  rfl

/-- The lists of copies so far, and the table of their positions. -/
structure CCRel (tb : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64)
    (ov : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy))
    (A : Std.HashMap NIdx Nat) (O : _root_.Array (NIdx × _root_.Array ConLeche.Frontend.Olean.Copy)) :
    Prop where
  tbl : NMapRel (fun x : Std.U64 => x.val) tb A
  lt : ∀ n k, toFun tb n = some k → k.val < ov.val.length
  rel : ov.val.map absCC = O.toList
  fits : ∀ p ∈ ov.val, ∀ c ∈ p.2.val, CopyFits c

/-- **`clash_copies_step` is the twin's step.** -/
theorem clash_copies_step_eq {ix ix'} (hix : NameIndexRel ix ix') {at_ out A O}
    (hr : CCRel at_ out A O) {n : arena.handle.NIdx} {c : frontend.olean.index.Copy} (hc : CopyFits c)
    {o} (h : clash_copies_step ix at_ out n c = ok o) :
    CCRel o.1 o.2 (ccStep ix' (A, O) (absNIdx n, absCopy c)).1 (ccStep ix' (A, O) (absNIdx n, absCopy c)).2 := by
  rw [clash_copies_step] at h
  peel h as a, ha
  obtain ⟨ea, ha'⟩ := at_of_eq hr.tbl ha
  cases a with
  | none =>
    have eA : A[absNIdx n]? = none := by rw [← ea]; rfl
    peel h as c1, hc1
    obtain ⟨ec1, fc1⟩ := first_or_eq hix hc1
    peel h as cs1, hcs1
    peel h as c2, hc2
    cases copy_dup2_ok hc2
    peel h as cs2, hcs2
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as i1, hi1
    have ei1 : i1.val = out.val.length := by
      rw [← Result.ok_injective hi1, cast_u64_val, vec_len_val]
    peel h as q, hq
    obtain ⟨old, at1⟩ := q
    peel h as out1, hout1
    cases Result.ok_injective h
    have ecs : cs2.val = [c1, c] := by
      rw [ConRon.Refine.vec_push_val hcs2, ConRon.Refine.vec_push_val hcs1]; rfl
    have eO : O.size = out.val.length := by
      rw [← Array.length_toList, ← hr.rel, List.length_map]
    simp only [ccStep, eA]
    obtain ⟨-, -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2
      hr.tbl.inv (fun _ _ => trivial) trivial hq
    have hins := hr.tbl.insert hq
    rw [ei1, ← eO] at hins
    refine ⟨hins, fun n' k hk => ?_, ?_, ?_⟩
    · rw [hupd, Function.update_apply] at hk
      rw [ConRon.Refine.vec_push_val hout1, List.length_append]
      by_cases e : n' = n
      · rw [ite_eq_left e] at hk; cases hk; simp [ei1]
      · rw [ite_eq_right e] at hk; have := hr.lt n' k hk; simp; omega
    · rw [ConRon.Refine.vec_push_val hout1, List.map_append, hr.rel]
      simp [absCC, ecs, ec1]
    · rw [ConRon.Refine.vec_push_val hout1]
      intro p hp c' hc'
      rcases List.mem_append.mp hp with hp | hp
      · exact hr.fits p hp c' hc'
      · rw [List.mem_singleton.mp hp] at hc'
        simp only [ecs, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl
        · exact fc1 hc
        · exact hc
  | some k =>
    have hk := hr.lt n k (ha' k rfl)
    have eA : A[absNIdx n]? = some k.val := by rw [← ea]; rfl
    peel h as i, hi
    have ei : i.val = k.val := by
      rw [← Result.ok_injective hi]
      exact cast_usize_val (by have := vec_len_le_max out; omega)
    peel h as q, hq
    obtain ⟨⟨n1, v⟩, back⟩ := q
    have : Inhabited (arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy) :=
      ⟨(n, alloc.vec.Vec.new _)⟩
    obtain ⟨hlt, hx, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hq
    peel h as c1, hc1
    cases copy_dup2_ok hc1
    peel h as v1, hv1
    cases Result.ok_injective h
    have hk' : k.val < O.size := by
      rw [← Array.length_toList, ← hr.rel, List.length_map]; exact hk
    simp only [ccStep, eA]
    have hlt' : i.val < out.val.length := hlt
    have hxe : (n1, v) = out.val[i.val] := by rw [hx]; simp [hlt']
    refine ⟨hr.tbl, fun n' k' hk' => ?_, ?_, ?_⟩
    · rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hr.lt n' k' hk'
    · rw [Array.toList_modify, ← hr.rel, alloc.vec.Vec.set_val_eq, ← ei]
      apply map_set_eq_modify _ _ _ _ _ hlt'
      rw [← hxe]
      simp [ConRon.Refine.vec_push_val hv1]
    · rw [alloc.vec.Vec.set_val_eq]
      intro p hp c' hc'
      rcases List.mem_or_eq_of_mem_set hp with hp | hp
      · exact hr.fits p hp c' hc'
      · subst hp
        rw [ConRon.Refine.vec_push_val hv1] at hc'
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact hr.fits _ (hxe ▸ List.getElem_mem hlt') c' hc'
        · rw [List.mem_singleton.mp hc']; exact hc

theorem clash_copies_loop_eq {ix ix'} (hix : NameIndexRel ix ix')
    (at_ : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64)
    (out : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy)) (i : Std.Usize)
    {A O} (hr : CCRel at_ out A O) {o} (h : clash_copies_loop ix at_ out i = ok o) :
    o.val.map absCC = (((ix.more.val.drop i.val).map absMore).foldl (ccStep ix') (A, O)).2.toList ∧
      ∀ p ∈ o.val, ∀ c ∈ p.2.val, CopyFits c := by
  rw [clash_copies_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len ix.more
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as p, hp
    obtain ⟨_, hpe⟩ := vec_index_eq hp
    obtain ⟨n, c⟩ := p
    have hc : CopyFits c := hix.fitsM (n, c) (by rw [hpe]; exact List.getElem_mem hi)
    peel h as q, hq
    obtain ⟨at1, out1⟩ := q
    peel h as i2, hi2
    have ei2 := usize_succ hi2
    have hs := clash_copies_step_eq hix hr hc hq
    have ih := clash_copies_loop_eq hix at1 out1 i2 hs h
    rw [ei2] at ih
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldl_cons, ← hpe]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    exact ⟨hr.rel, hr.fits⟩
termination_by ix.more.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`clash_copies` is `clashCopies`**, and its copies fit. -/
theorem clash_copies_eq {ix ix'} (hix : NameIndexRel ix ix') {o} (h : clash_copies ix = ok o) :
    o.val.map absCC = (Arena.Frontend.Olean.clashCopies ix').toList ∧
      ∀ p ∈ o.val, ∀ c ∈ p.2.val, CopyFits c := by
  rw [clash_copies] at h
  peel h as at_, hat
  have hr : CCRel at_ (alloc.vec.Vec.new _) {} #[] := by
    obtain ⟨-, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines (HashableInst := hN) hat
    have e0 : (alloc.vec.Vec.new (arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy)).val = [] := rfl
    exact ⟨NMapRel.new hat, (fun n k hk => by rw [hnone] at hk; cases hk), by rw [e0]; rfl,
      (fun p hp => by rw [e0] at hp; cases hp)⟩
  have := clash_copies_loop_eq hix at_ _ 0#usize hr h
  rw [clashCopies_eq, ← hix.more]
  simpa using this

/-! ## Every copy -/

theorem all_copies_loop0_loop0_eq (cc : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy))
    (out : alloc.vec.Vec frontend.olean.index.Copy) (i k : Std.Usize) (hi : i.val < cc.val.length)
    {o} (h : frontend.olean.index.all_copies_loop0_loop0 cc out i k = ok o) :
    o.val = out.val ++ (cc.val[i.val].2.val.drop k.val) := by
  rw [all_copies_loop0_loop0] at h
  peel h as p, hp
  obtain ⟨_, hpe⟩ := vec_index_eq hp
  obtain ⟨n, v⟩ := p
  change (if k < alloc.vec.Vec.len v then _ else ok out) = ok o at h
  by_cases hlt : k < alloc.vec.Vec.len v
  · rw [ite_eq_left hlt] at h
    have hk := lt_of_lt_len hlt
    peel h as c, hc
    obtain ⟨_, rfl⟩ := vec_index_eq hc
    peel h as c1, hc1
    cases copy_dup2_ok hc1
    peel h as out1, hout1
    peel h as k1, hk1
    have ek1 := usize_succ hk1
    have ih := all_copies_loop0_loop0_eq cc out1 i k1 hi h
    rw [ih, ek1, ConRon.Refine.vec_push_val hout1, ← hpe, List.drop_eq_getElem_cons hk]
    simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [← hpe, List.drop_of_length_le (lt_of_not_lt_len hlt)]
    simp
termination_by cc.val[i.val].2.val.length - k.val
decreasing_by
  have := lt_of_lt_len hlt
  have h2 : v.val.length = (cc.val[i.val]).2.val.length := by rw [← hpe]
  omega

theorem all_copies_loop0_eq (cc : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy))
    (out : alloc.vec.Vec frontend.olean.index.Copy) (i : Std.Usize)
    {o} (h : frontend.olean.index.all_copies_loop0 cc out i = ok o) :
    o.val = out.val ++ (cc.val.drop i.val).flatMap (·.2.val) := by
  rw [all_copies_loop0] at h
  by_cases hlt : i < alloc.vec.Vec.len cc
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as out1, hout1
    peel h as i2, hi2
    have ei2 := usize_succ hi2
    have ih := all_copies_loop0_eq cc out1 i2 h
    rw [ih, ei2, all_copies_loop0_loop0_eq cc out i 0#usize hi hout1,
      List.drop_eq_getElem_cons hi (l := cc.val), List.flatMap_cons]
    simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    simp
termination_by cc.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`all_copies` is `cc.flatMap (·.2)`.** -/
theorem all_copies_eq {cc : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy)}
    {o} (h : all_copies cc = ok o) : o.val = cc.val.flatMap (·.2.val) := by
  simpa using all_copies_loop0_eq cc _ 0#usize h

/-! ## The copies' statements -/

/-- A copy's statement and kind, against the twin's. -/
def InfoRel (x : frontend.olean.spec.StmtRec × frontend.olean.spec.CKindF arena.handle.NIdx Unit)
    (y : Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) : Prop :=
  absStmtRec x.1 = y.1 ∧ KindNamesRel x.2 y.2

/-- A copy with its statement and kind, against the twin's. -/
def CopyInfoRel (x : frontend.olean.index.Copy × frontend.olean.spec.StmtRec ×
      frontend.olean.spec.CKindF arena.handle.NIdx Unit)
    (y : ConLeche.Frontend.Olean.Copy × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) :
    Prop :=
  absCopy x.1 = y.1 ∧ InfoRel x.2 y.2

/-- The twin's `(infos[c]?).map fun (s, k) => (c, s, k)`. -/
def infoOf (I : Std.HashMap ConLeche.Frontend.Olean.Copy
      (Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit))
    (c : ConLeche.Frontend.Olean.Copy) :
    Option (ConLeche.Frontend.Olean.Copy × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) :=
  (I[c]?).map fun x => (c, x.1, x.2)

/-- **`info_of` is the twin's lookup.** -/
theorem info_of_eq {infos I} (hI : CMapRel InfoRel infos I) {c : frontend.olean.index.Copy} {o}
    (h : info_of infos c = ok o) : Option.Rel CopyInfoRel o (infoOf I (absCopy c)) := by
  rw [info_of] at h
  peel h as o1, h1
  have e := hI.get_eq h1
  rw [infoOf]
  generalize I[absCopy c]? = y at e ⊢
  cases o1 with
  | none =>
    cases Result.ok_injective h
    cases e with
    | none => exact .none
  | some x =>
    obtain ⟨s, k⟩ := x
    dsimp only at h
    peel h as c1, hc1
    cases copy_dup2_ok hc1
    peel h as s1, hs1
    cases stmt_rec_dup_eq hs1
    peel h as k1, hk1
    cases c_kind_names_dup_eq hk1
    cases Result.ok_injective h
    cases e with
    | some hr => exact .some ⟨rfl, hr⟩

/-- A clash, against the twin's. -/
structure ClashRel (c : frontend.olean.index.Clash) (c' : Arena.Frontend.Olean.Clash) : Prop where
  «name» : absNIdx c.name = c'.name
  copies : List.Forall₂ CopyInfoRel c.copies.val c'.copies.toList

theorem clashes_of_loop0_loop0_eq {infos I} (hI : CMapRel InfoRel infos I)
    (cs : alloc.vec.Vec frontend.olean.index.Copy) (copies : alloc.vec.Vec _) (k : Std.Usize) {C}
    (hC : List.Forall₂ CopyInfoRel copies.val C) {o}
    (h : clashes_of_loop0_loop0 infos cs copies k = ok o) :
    List.Forall₂ CopyInfoRel o.val (C ++ (cs.val.drop k.val).filterMap fun c => infoOf I (absCopy c)) := by
  rw [clashes_of_loop0_loop0] at h
  by_cases hlt : k < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    have hk := lt_of_lt_len hlt
    peel h as c, hc
    obtain ⟨_, rfl⟩ := vec_index_eq hc
    peel h as x, hx
    have ex := info_of_eq hI hx
    peel h as copies1, hcopies1
    peel h as k1, hk1
    have ek1 := usize_succ hk1
    rw [List.drop_eq_getElem_cons hk, List.filterMap_cons]
    generalize infoOf I (absCopy cs.val[k.val]) = y at ex ⊢
    cases ex with
    | none =>
      cases Result.ok_injective hcopies1
      have ih := clashes_of_loop0_loop0_eq hI cs copies k1 hC h
      rw [ek1] at ih
      simpa using ih
    | some hr =>
      rename_i a b
      have hC' : List.Forall₂ CopyInfoRel copies1.val (C ++ [b]) := by
        rw [ConRon.Refine.vec_push_val hcopies1]
        exact List.rel_append hC (List.Forall₂.cons hr .nil)
      have ih := clashes_of_loop0_loop0_eq hI cs copies1 k1 hC' h
      rw [ek1] at ih
      simpa using ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    simpa using hC
termination_by cs.val.length - k.val
decreasing_by
  all_goals
    have := lt_of_lt_len hlt
    omega


/-- The twin's clash of a name's copies. -/
def clashOfT (I : Std.HashMap ConLeche.Frontend.Olean.Copy
      (Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit))
    (p : NIdx × _root_.Array ConLeche.Frontend.Olean.Copy) : Arena.Frontend.Olean.Clash :=
  ⟨p.1, p.2.filterMap (infoOf I)⟩

theorem clashes_of_loop0_eq {infos I} (hI : CMapRel InfoRel infos I)
    (cc : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy))
    (out : alloc.vec.Vec frontend.olean.index.Clash) (i : Std.Usize) {C}
    (hC : List.Forall₂ ClashRel out.val C) {o} (h : clashes_of_loop0 cc infos out i = ok o) :
    List.Forall₂ ClashRel o.val (C ++ (cc.val.drop i.val).map (clashOfT I ∘ absCC)) := by
  rw [clashes_of_loop0] at h
  by_cases hlt : i < alloc.vec.Vec.len cc
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as p, hp
    obtain ⟨_, hpe⟩ := vec_index_eq hp
    obtain ⟨n, cs⟩ := p
    peel h as copies1, hcopies1
    have e0 : (alloc.vec.Vec.with_capacity (frontend.olean.index.Copy × frontend.olean.spec.StmtRec ×
      frontend.olean.spec.CKindF arena.handle.NIdx Unit) (alloc.vec.Vec.len cs)).val = [] := rfl
    have hcp := clashes_of_loop0_loop0_eq hI cs _ 0#usize (C := []) (by rw [e0]; exact .nil) hcopies1
    peel h as q, hq
    obtain ⟨_, hqe⟩ := vec_index_eq hq
    rw [← hpe] at hqe
    obtain ⟨n2, cs2⟩ := q
    cases hqe
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as out1, hout1
    peel h as i3, hi3
    have ei3 := usize_succ hi3
    have hC' : List.Forall₂ ClashRel out1.val (C ++ [clashOfT I (absCC (n, cs))]) := by
      rw [ConRon.Refine.vec_push_val hout1]
      refine List.rel_append hC (List.Forall₂.cons ⟨rfl, ?_⟩ .nil)
      simpa [clashOfT, absCC, Array.toList_filterMap] using hcp
    have ih := clashes_of_loop0_eq hI cc out1 i3 hC' h
    rw [ei3] at ih
    rw [List.drop_eq_getElem_cons hi, List.map_cons, ← hpe]
    simpa using ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    simpa using hC
termination_by cc.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`clashes_of` is the twin's `cc.map`.** -/
theorem clashes_of_eq {infos I} (hI : CMapRel InfoRel infos I)
    {cc : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy)} {o}
    (h : clashes_of cc infos = ok o) :
    List.Forall₂ ClashRel o.val (cc.val.map (clashOfT I ∘ absCC)) := by
  rw [clashes_of] at h
  have e0 : (alloc.vec.Vec.with_capacity frontend.olean.index.Clash (alloc.vec.Vec.len cc)).val = [] := rfl
  simpa using clashes_of_loop0_eq hI cc _ 0#usize (C := []) (by rw [e0]; exact .nil) h

/-! ## Freshness and the module system -/

theorem first_loaded_loop_none {ix ix'} (hix : NameIndexRel ix ix')
    (own : frontend.olean.reads.NamePositions) (i : Std.Usize)
    (h : first_loaded_loop ix own i = ok none) :
    ∀ q ∈ (own.consts.val.drop i.val).map absNamePosition, ix'.first.contains q.name = false := by
  rw [first_loaded_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len own.consts
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as np, hnp
    obtain ⟨_, rfl⟩ := vec_index_eq hnp
    peel h as b, hb
    have eb := hix.first.rel.contains_eq hb
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h; exact absurd (Result.ok_injective h) (by simp)
    · rw [ite_eq_right cb] at h
      peel h as i2, hi2
      have ei2 := usize_succ hi2
      have ih := first_loaded_loop_none hix own i2 h
      rw [usize_succ hi2] at ih
      rw [List.drop_eq_getElem_cons hi, List.map_cons]
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · simp only [absNamePosition_name]; rw [← eb]; simpa using cb
      · exact ih q hq
  · intro q hq
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)] at hq
    cases hq
termination_by own.consts.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`first_loaded`'s `None` is `find?`'s `none`.** -/
theorem first_loaded_none {ix ix'} (hix : NameIndexRel ix ix') {own : frontend.olean.reads.NamePositions}
    (h : first_loaded ix own = ok none) :
    (absNamePositions own).consts.find? (fun q => ix'.first.contains q.name) = none := by
  have := first_loaded_loop_none hix own 0#usize h
  rw [Array.find?_eq_none]
  intro q hq
  simpa using this q (by simpa using hq)

/-- **`part_is_module` is `(ix.parts[k]?).any (·.header.isModule)`**, at a position that fits. -/
theorem part_is_module_eq {ix ix'} (hix : NameIndexRel ix ix') {k : Std.U64} (hk : k.val ≤ Std.Usize.max)
    {b} (h : part_is_module ix k = ok b) : b = (ix'.parts[k.val]?).any (·.header.isModule) := by
  rw [part_is_module] at h
  peel h as i, hi
  have ei : i.val = k.val := by rw [← Result.ok_injective hi]; exact cast_usize_val hk
  have hp : ix'.parts[k.val]? = (ix.parts.val[k.val]?).map absNamePositions := by
    have := congrArg (·[k.val]?) hix.parts
    simp only [List.getElem?_map] at this
    rw [← Array.getElem?_toList]; exact this.symm
  rw [hp]
  by_cases h1 : i < alloc.vec.Vec.len ix.parts
  · rw [ite_eq_left h1] at h
    have h1' := lt_of_lt_len h1
    peel h as np, hnp
    obtain ⟨_, rfl⟩ := vec_index_eq hnp
    cases Result.ok_injective h
    simp [← ei, List.getElem?_eq_getElem (show i.val < ix.parts.val.length by omega)]
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    have := lt_of_not_lt_len h1
    rw [ei] at this
    simp [List.getElem?_eq_none this]

/-- The positions of `HeaderLoads.index` fit a `usize`. -/
def IndexFits (ld : frontend.olean.levels.HeaderLoads) : Prop :=
  ∀ n k, toFun ld.index n = some k → k.val ≤ Std.Usize.max

/-- The twin's `importsModulesOk` test of an import. -/
def classicT (ld' : Arena.Frontend.Olean.HeaderLoads) (ix' : Arena.Frontend.Olean.NameIndex)
    (i : ConLeche.Frontend.Olean.ImportF NIdx) : Bool :=
  match ld'.index[i.module]? with
  | some k => !((ix'.parts[k]?).any (·.header.isModule))
  | none => false

/-- **`classic_import` is the twin's test.** -/
theorem classic_import_eq {ld ld' ix ix'} (hld : HeaderLoadsRel ld ld') (hfit : IndexFits ld)
    (hix : NameIndexRel ix ix') {i : frontend.olean.spec.ImportF arena.handle.NIdx} {b}
    (h : classic_import ld ix i = ok b) : b = classicT ld' ix' (absImportF absNIdx i) := by
  rw [classic_import] at h
  peel h as o, ho
  have e := hld.index.get_eq ho
  have e2 := ConRon.Refine.HashMap2.get_refines_gen nidx_eq2 hld.index.inv (fun _ _ => trivial) trivial ho
  rw [classicT]
  simp only [absImportF]
  rw [← e]
  cases o with
  | none => cases Result.ok_injective h; rfl
  | some k =>
    peel h as b1, hb1
    cases Result.ok_injective h
    rw [part_is_module_eq hix (hfit _ _ (by rw [← e2])) hb1]
    simp

theorem first_classic_loop_none {ld ld' ix ix'} (hld : HeaderLoadsRel ld ld') (hfit : IndexFits ld)
    (hix : NameIndexRel ix ix') (imports : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))
    (i : Std.Usize) (h : first_classic_loop ld ix imports i = ok none) :
    ∀ x ∈ (imports.val.drop i.val).map (absImportF absNIdx), classicT ld' ix' x = false := by
  rw [first_classic_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len imports
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    peel h as b, hb
    have eb := classic_import_eq hld hfit hix hb
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h; exact absurd (Result.ok_injective h) (by simp)
    · rw [ite_eq_right cb] at h
      peel h as i2, hi2
      have ei2 := usize_succ hi2
      have ih := first_classic_loop_none hld hfit hix imports i2 h
      rw [usize_succ hi2] at ih
      rw [List.drop_eq_getElem_cons hi, List.map_cons]
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [← eb]; simpa using cb
      · exact ih q hq
  · intro q hq
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)] at hq
    cases hq
termination_by imports.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`first_classic`'s `None` is `find?`'s `none`.** -/
theorem first_classic_none {ld ld' ix ix'} (hld : HeaderLoadsRel ld ld') (hfit : IndexFits ld)
    (hix : NameIndexRel ix ix') {imports : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    (h : first_classic ld ix imports = ok none) :
    (absImports imports).find? (classicT ld' ix') = none := by
  have := first_classic_loop_none hld hfit hix imports 0#usize h
  rw [Array.find?_eq_none]
  intro q hq
  simpa using this q (by simpa using hq)

/-! ## The worker's own part -/

theorem name_positions_with_imports_loop_eq
    (x imports : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) (i : Std.Usize) {o}
    (h : name_positions_with_imports_loop x imports i = ok o) : o.val = imports.val ++ x.val.drop i.val := by
  rw [name_positions_with_imports_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len x
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as y, hy
    obtain ⟨_, rfl⟩ := vec_index_eq hy
    peel h as y1, hy1
    cases import_rec_dup_eq hy1
    peel h as imports1, himports1
    peel h as i2, hi2
    have ei2 := usize_succ hi2
    rw [name_positions_with_imports_loop_eq x imports1 i2 h, ei2,
      ConRon.Refine.vec_push_val himports1, List.drop_eq_getElem_cons hi]
    simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    simp
termination_by x.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`name_positions_with_imports` is `NamePositions.withImports`.** -/
theorem name_positions_with_imports_eq {own : frontend.olean.reads.NamePositions}
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)} {o}
    (h : name_positions_with_imports own x = ok o) :
    absNamePositions o = (absNamePositions own).withImports (absImports x) := by
  rw [name_positions_with_imports] at h
  rw [Arena.Frontend.Olean.NamePositions.withImports]
  by_cases h0 : alloc.vec.Vec.len x = 0#usize
  · rw [ite_eq_left h0] at h
    cases Result.ok_injective h
    have : x.val = [] := by
      have := congrArg (·.val) h0
      simp only [vec_len_val] at this
      exact List.eq_nil_of_length_eq_zero this
    simp [absImports, this]
  · rw [ite_eq_right h0] at h
    peel h as imps, himps
    cases Result.ok_injective h
    have e := name_positions_with_imports_loop_eq x _ 0#usize himps
    have hne : (absImports x).isEmpty = false := by
      have : x.val ≠ [] := fun he => h0 (by
        apply UScalar.eq_of_val_eq; rw [vec_len_val, he]; rfl)
      simpa [absImports] using this
    rw [hne]
    simp [absNamePositions, absModHeader, absImports, e]

end ConRon.Refine2.Frontend.Olean
