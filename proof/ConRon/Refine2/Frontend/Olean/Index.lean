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
import ConRon.Refine2.Frontend.Olean.MergeF
import ConRon.Refine2.Frontend.Olean.Stmts
import ConRon.Refine2.Frontend.Olean.ReadKinds
import ConRon.Arena.Frontend.Olean.Index

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.index

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap2 (Inv toFun)
open ConRon.Refine.HashMap (Eq2Fwd)
open Arena.Frontend.Olean (isPropCheapHeadOf)

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

/-- The twin's `importsModulesOk` test of an import. -/
def classicT (ld' : Arena.Frontend.Olean.HeaderLoads) (ix' : Arena.Frontend.Olean.NameIndex)
    (i : ConLeche.Frontend.Olean.ImportF NIdx) : Bool :=
  match ld'.index[i.module]? with
  | some k => !((ix'.parts[k]?).any (·.header.isModule))
  | none => false

/-- **`classic_import` is the twin's test.** -/
theorem classic_import_eq {ld ld' ix ix'} (hld : HeaderLoadsRel ld ld') (hw : IndexFits ld')
    (hix : NameIndexRel ix ix') {i : frontend.olean.spec.ImportF arena.handle.NIdx} {b}
    (h : classic_import ld ix i = ok b) : b = classicT ld' ix' (absImportF absNIdx i) := by
  rw [classic_import] at h
  peel h as o, ho
  have e := hld.index.get_eq ho
  rw [classicT]
  simp only [absImportF]
  rw [← e]
  cases o with
  | none => cases Result.ok_injective h; rfl
  | some k =>
    peel h as b1, hb1
    cases Result.ok_injective h
    have hk : k.val ≤ Std.Usize.max := by
      have e3 : ld'.index[absNIdx i.module]? = some k.val := by rw [← e]; rfl
      have := hw _ _ e3
      have := order_fits hld
      omega
    rw [part_is_module_eq hix hk hb1]
    simp

theorem first_classic_loop_none {ld ld' ix ix'} (hld : HeaderLoadsRel ld ld') (hw : IndexFits ld')
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
    have eb := classic_import_eq hld hw hix hb
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h; exact absurd (Result.ok_injective h) (by simp)
    · rw [ite_eq_right cb] at h
      peel h as i2, hi2
      have ei2 := usize_succ hi2
      have ih := first_classic_loop_none hld hw hix imports i2 h
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
theorem first_classic_none {ld ld' ix ix'} (hld : HeaderLoadsRel ld ld') (hw : IndexFits ld')
    (hix : NameIndexRel ix ix') {imports : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    (h : first_classic ld ix imports = ok none) :
    (absImports imports).find? (classicT ld' ix') = none := by
  have := first_classic_loop_none hld hw hix imports 0#usize h
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

/-! ## Copies by module -/

/-- The twin's `max` step of `byModule`. -/
def bmTop (t : Nat) (c : ConLeche.Frontend.Olean.Copy) : Nat := max t (c.mod + 1)

/-- The twin's bucket step of `byModule`. -/
def bmPush (b : _root_.Array (_root_.Array ConLeche.Frontend.Olean.Copy)) (c : ConLeche.Frontend.Olean.Copy) :
    _root_.Array (_root_.Array ConLeche.Frontend.Olean.Copy) := b.modify c.mod (·.push c)

/-- A bucket, as the twin's. -/
@[reducible] def absB (v : alloc.vec.Vec frontend.olean.index.Copy) : _root_.Array ConLeche.Frontend.Olean.Copy :=
  (v.val.map absCopy).toArray

/-- A module's copies, as the twin's. -/
@[reducible] def absBM (p : Std.U64 × alloc.vec.Vec frontend.olean.index.Copy) :
    Nat × _root_.Array ConLeche.Frontend.Olean.Copy := (p.1.val, absB p.2)

theorem byModule_eq (cs : _root_.Array ConLeche.Frontend.Olean.Copy) :
    Arena.Frontend.Olean.byModule cs =
      ((cs.toList.foldl bmPush (Array.replicate (cs.toList.foldl bmTop 0) #[])).zipIdx.filter
        (·.1.size > 0)).map (fun p => (p.2, p.1)) := by
  rw [Arena.Frontend.Olean.byModule, ← Array.foldl_toList, ← Array.foldl_toList]
  rfl

theorem bmTop_le (l : List ConLeche.Frontend.Olean.Copy) (t : Nat) : t ≤ l.foldl bmTop t := by
  induction l generalizing t with
  | nil => simp
  | cons c l ih => simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem bmTop_gt (l : List ConLeche.Frontend.Olean.Copy) (t : Nat) :
    ∀ c ∈ l, c.mod < l.foldl bmTop t := by
  induction l generalizing t with
  | nil => simp
  | cons c l ih =>
    intro c' hc
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.lt_of_lt_of_le (by simp [bmTop]) (bmTop_le l _)
    · exact ih _ c' hc

theorem by_module_loop0_eq (cs : alloc.vec.Vec frontend.olean.index.Copy) (top : Std.U64) (i : Std.Usize)
    {o} (h : by_module_loop0 cs top i = ok o) :
    o.val = ((cs.val.drop i.val).map absCopy).foldl bmTop top.val := by
  rw [by_module_loop0] at h
  by_cases hlt : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as c, hc
    obtain ⟨_, rfl⟩ := vec_index_eq hc
    peel h as i2, hi2
    have ei2 := ConRon.Refine.Nat.uadd_val hi2
    peel h as top1, htop1
    peel h as i3, hi3
    have ei3 := usize_succ hi3
    have ih := by_module_loop0_eq cs top1 i3 h
    rw [ih, ei3, List.drop_eq_getElem_cons hi, List.map_cons, List.foldl_cons]
    congr 1
    simp only [bmTop]
    by_cases g : i2 > top
    · rw [ite_eq_left g] at htop1
      have := ConRon.Refine.Nat.uadd_val htop1
      have g' : top.val < i2.val := g
      rw [this]; simp at ei2 this ⊢; omega
    · rw [ite_eq_right g] at htop1
      cases Result.ok_injective htop1
      have g' : ¬ top.val < i2.val := g
      simp at ei2; omega
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    rfl
termination_by cs.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

theorem by_module_loop1_eq (top : Std.U64) (buckets : alloc.vec.Vec (alloc.vec.Vec frontend.olean.index.Copy))
    (b : Std.U64) {o} (h : by_module_loop1 top buckets b = ok o) :
    o.val = buckets.val ++ List.replicate (top.val - b.val) (alloc.vec.Vec.new _) := by
  rw [by_module_loop1] at h
  by_cases hlt : b < top
  · rw [ite_eq_left hlt] at h
    have hlt' : b.val < top.val := hlt
    peel h as buckets1, hb1
    peel h as b1, hbb1
    have eb1 := ConRon.Refine.Nat.uadd_val hbb1
    have ih := by_module_loop1_eq top buckets1 b1 h
    rw [ih, ConRon.Refine.vec_push_val hb1, eb1]
    have : top.val - b.val = (top.val - (b.val + (1#u64 : Std.U64).val)) + 1 := by simp; omega
    rw [this, List.replicate_succ]
    simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hlt' : ¬ b.val < top.val := hlt
    rw [show top.val - b.val = 0 by omega]
    simp
termination_by top.val - b.val
decreasing_by
  have := ConRon.Refine.Nat.uadd_val hbb1
  simp at this
  omega

theorem by_module_loop2_eq (cs : alloc.vec.Vec frontend.olean.index.Copy)
    (buckets : alloc.vec.Vec (alloc.vec.Vec frontend.olean.index.Copy)) (j : Std.Usize)
    (hlen : ∀ c ∈ cs.val, c.module.val < buckets.val.length)
    (hfit : ∀ v ∈ buckets.val, ∀ c ∈ v.val, CopyFits c) (hcs : ∀ c ∈ cs.val, CopyFits c)
    {o} (h : by_module_loop2 cs buckets j = ok o) :
    o.val.map absB = (((cs.val.drop j.val).map absCopy).foldl bmPush (buckets.val.map absB).toArray).toList ∧
      ∀ v ∈ o.val, ∀ c ∈ v.val, CopyFits c := by
  rw [by_module_loop2] at h
  by_cases hlt : j < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    have hj := lt_of_lt_len hlt
    peel h as c, hc
    obtain ⟨_, rfl⟩ := vec_index_eq hc
    have hcm := hlen _ (List.getElem_mem hj)
    peel h as i1, hi1
    have ei1 : i1.val = (cs.val[j.val]).module.val := by
      rw [← Result.ok_injective hi1]
      exact cast_usize_val (by have := vec_len_le_max buckets; omega)
    peel h as q, hq
    obtain ⟨v, back⟩ := q
    have : Inhabited (alloc.vec.Vec frontend.olean.index.Copy) := ⟨alloc.vec.Vec.new _⟩
    obtain ⟨hlt1, hv, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hq
    peel h as c1, hc1
    cases copy_dup2_ok hc1
    peel h as v1, hv1
    peel h as j1, hj1
    have ej1 := usize_succ hj1
    have hlt1' : i1.val < buckets.val.length := hlt1
    have hve : v = buckets.val[i1.val] := by rw [hv]; simp [hlt1']
    have hlen' : ∀ c ∈ cs.val, c.module.val < (alloc.vec.Vec.set buckets i1 v1).val.length := by
      rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen
    have hfit' : ∀ w ∈ (alloc.vec.Vec.set buckets i1 v1).val, ∀ c ∈ w.val, CopyFits c := by
      rw [alloc.vec.Vec.set_val_eq]
      intro w hw c' hc'
      rcases List.mem_or_eq_of_mem_set hw with hw | rfl
      · exact hfit w hw c' hc'
      · rw [ConRon.Refine.vec_push_val hv1] at hc'
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact hfit _ (hve ▸ List.getElem_mem hlt1') c' hc'
        · rw [List.mem_singleton.mp hc']; exact hcs _ (List.getElem_mem hj)
    have ih := by_module_loop2_eq cs _ j1 hlen' hfit' hcs h
    rw [ej1] at ih
    refine ⟨?_, ih.2⟩
    rw [ih.1, List.drop_eq_getElem_cons hj, List.map_cons, List.foldl_cons]
    congr 2
    apply Array.ext'
    rw [alloc.vec.Vec.set_val_eq, bmPush, Array.toList_modify, List.toList_toArray]
    simp only [absCopy]
    rw [← ei1]
    apply map_set_eq_modify _ _ _ _ _ hlt1'
    simp [absB, ConRon.Refine.vec_push_val hv1, ei1, hve]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    exact ⟨by simp, hfit⟩
termination_by cs.val.length - j.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

theorem by_module_loop3_eq (buckets : alloc.vec.Vec (alloc.vec.Vec frontend.olean.index.Copy))
    (out : alloc.vec.Vec (Std.U64 × alloc.vec.Vec frontend.olean.index.Copy)) (k : Std.Usize)
    (hfit : ∀ v ∈ buckets.val, ∀ c ∈ v.val, CopyFits c)
    (hout : ∀ p ∈ out.val, p.1.val ≤ Std.Usize.max ∧ ∀ c ∈ p.2.val, CopyFits c)
    {o} (h : by_module_loop3 buckets out k = ok o) :
    o.val.map absBM = out.val.map absBM ++ ((((buckets.val.drop k.val).map absB).zipIdx k.val).filter
        (·.1.size > 0)).map (fun p => (p.2, p.1)) ∧
      ∀ p ∈ o.val, p.1.val ≤ Std.Usize.max ∧ ∀ c ∈ p.2.val, CopyFits c := by
  rw [by_module_loop3] at h
  by_cases hlt : k < alloc.vec.Vec.len buckets
  · rw [ite_eq_left hlt] at h
    have hk := lt_of_lt_len hlt
    peel h as v, hv
    obtain ⟨_, rfl⟩ := vec_index_eq hv
    peel h as q, hq
    obtain ⟨buckets1, out1⟩ := q
    peel h as k1, hk1
    have ek1 := usize_succ hk1
    have hdrop : buckets1.val.drop (k.val + 1) = buckets.val.drop (k.val + 1) ∧
        buckets1.val.length = buckets.val.length ∧
        (∀ v ∈ buckets1.val, ∀ c ∈ v.val, CopyFits c) ∧
        out1.val.map absBM = out.val.map absBM ++
          ((([absB buckets.val[k.val]].zipIdx k.val).filter (·.1.size > 0)).map (fun p => (p.2, p.1))) ∧
        ∀ p ∈ out1.val, p.1.val ≤ Std.Usize.max ∧ ∀ c ∈ p.2.val, CopyFits c := by
      by_cases g : alloc.vec.Vec.len buckets.val[k.val] > 0#usize
      · rw [ite_eq_left g] at hq
        have g' : 0 < buckets.val[k.val].val.length := by
          have : (0#usize : Std.Usize).val < (alloc.vec.Vec.len buckets.val[k.val]).val := g
          rw [vec_len_val] at this; simpa using this
        peel hq as i2, hi2
        have ei2 : i2.val = k.val := by rw [← Result.ok_injective hi2, cast_u64_val]
        peel hq as r, hr
        obtain ⟨v1, back⟩ := r
        have : Inhabited (alloc.vec.Vec frontend.olean.index.Copy) := ⟨alloc.vec.Vec.new _⟩
        obtain ⟨-, hv1, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hr
        have hv1' : v1 = buckets.val[k.val] := by rw [hv1]; simp [hk]
        subst hv1'
        simp only [core.mem.replace] at hq
        peel hq as out2, hout2
        have e := Result.ok_injective hq
        simp only [Prod.mk.injEq] at e
        obtain ⟨e1, e2⟩ := e
        subst e1 e2
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [alloc.vec.Vec.set_val_eq, List.drop_set_of_lt]; omega
        · rw [alloc.vec.Vec.set_val_eq, List.length_set]
        · rw [alloc.vec.Vec.set_val_eq]
          intro w hw c' hc'
          rcases List.mem_or_eq_of_mem_set hw with hw | rfl
          · exact hfit w hw c' hc'
          · cases hc'
        · rw [ConRon.Refine.vec_push_val hout2]
          simp [List.zipIdx_cons, ei2, g']
        · rw [ConRon.Refine.vec_push_val hout2]
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hout p hp
          · rw [List.mem_singleton.mp hp]
            exact ⟨by rw [ei2]; exact usize_le_max k, hfit _ (List.getElem_mem hk)⟩
      · rw [ite_eq_right g] at hq
        have e := Result.ok_injective hq
        simp only [Prod.mk.injEq] at e
        obtain ⟨e1, e2⟩ := e
        subst e1 e2
        have g' : buckets.val[k.val].val.length = 0 := by
          have : ¬ (0#usize : Std.Usize).val < (alloc.vec.Vec.len buckets.val[k.val]).val := g
          rw [vec_len_val] at this; exact Nat.eq_zero_of_not_pos (by simpa using this)
        refine ⟨rfl, rfl, hfit, ?_, hout⟩
        simp [List.zipIdx_cons, g']
    obtain ⟨hd, hl1, hf1, ho1, hp1⟩ := hdrop
    have ih := by_module_loop3_eq buckets1 out1 k1 hf1 hp1 h
    rw [ek1, hd] at ih
    refine ⟨?_, ih.2⟩
    rw [ih.1, ho1, List.drop_eq_getElem_cons hk, List.map_cons, List.zipIdx_cons]
    simp [List.filter_cons]
    split <;> simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    exact ⟨by simp, hout⟩
termination_by buckets.val.length - k.val
decreasing_by
  have := lt_of_lt_len hlt
  rw [hl1]
  omega


/-- **`by_module` is `byModule`**, its positions fitting a `usize` and its copies the input's. -/
theorem by_module_eq {cs : alloc.vec.Vec frontend.olean.index.Copy} (hcs : ∀ c ∈ cs.val, CopyFits c)
    {o} (h : by_module cs = ok o) :
    o.val.map absBM = (Arena.Frontend.Olean.byModule (cs.val.map absCopy).toArray).toList ∧
      ∀ p ∈ o.val, p.1.val ≤ Std.Usize.max ∧ ∀ c ∈ p.2.val, CopyFits c := by
  rw [by_module] at h
  peel h as top, htop
  have et := by_module_loop0_eq cs 0#u64 0#usize htop
  peel h as i, -
  peel h as b1, hb1
  have eb1 := by_module_loop1_eq top _ 0#u64 hb1
  have e0 : (alloc.vec.Vec.with_capacity (alloc.vec.Vec frontend.olean.index.Copy) i).val = [] := rfl
  rw [e0, List.nil_append] at eb1
  have ez : (0#u64 : Std.U64).val = 0 := rfl
  rw [ez, Nat.sub_zero] at eb1
  have hlen : ∀ c ∈ cs.val, c.module.val < b1.val.length := by
    intro c hc
    rw [eb1, List.length_replicate, et]
    exact bmTop_gt _ _ (absCopy c) (List.mem_map_of_mem hc)
  have hfit : ∀ v ∈ b1.val, ∀ c ∈ v.val, CopyFits c := by
    intro v hv c hc
    rw [eb1] at hv
    rw [List.eq_of_mem_replicate hv] at hc
    cases hc
  peel h as b2, hb2
  obtain ⟨e2, f2⟩ := by_module_loop2_eq cs b1 0#usize hlen hfit hcs hb2
  have e3 := by_module_loop3_eq b2 _ 0#usize f2 (by intro p hp; cases hp) h
  refine ⟨?_, e3.2⟩
  have z : (0#usize : Std.Usize).val = 0 := rfl
  have er : (b1.val.map absB).toArray = Array.replicate top.val #[] := by
    apply Array.ext'; rw [eb1]; simp [absB]
  rw [er, z, List.drop_zero] at e2
  rw [z, ez, List.drop_zero] at et
  rw [et] at e2
  rw [e3.1, byModule_eq, z, List.drop_zero]
  have e4 : (alloc.vec.Vec.new (Std.U64 × alloc.vec.Vec frontend.olean.index.Copy)).val = [] := rfl
  rw [e4, List.toList_toArray]
  simp only [Array.toList_map, Array.toList_filter, Array.toList_zipIdx, ← e2, List.map_nil,
    List.nil_append]

/-! ## `isPropCheap`'s head types -/

/-- The twin's step of `headTysOf`. -/
def htStep (ix' : Arena.Frontend.Olean.NameIndex)
    (I : Std.HashMap ConLeche.Frontend.Olean.Copy
      (Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit))
    (m : Std.HashMap NIdx EIdx) (c : ConLeche.Frontend.Olean.Copy) : Std.HashMap NIdx EIdx :=
  match ix'.at c with
  | none => m
  | some q =>
    match (ix'.first[q.name]?).bind (I[·]?) with
    | some x => m.insert q.name x.1.type
    | none => m

theorem headTysOf_eq (ix' : Arena.Frontend.Olean.NameIndex) I (heads : _root_.Array ConLeche.Frontend.Olean.Copy) :
    Arena.Frontend.Olean.headTysOf ix' I heads = heads.toList.foldl (htStep ix' I) {} := by
  rw [Arena.Frontend.Olean.headTysOf, ← Array.foldl_toList]
  rfl

/-- **`head_ty_step` is the twin's step.** -/
theorem head_ty_step_eq {ix ix'} (hix : NameIndexRel ix ix') {infos I} (hI : CMapRel InfoRel infos I)
    {m M} (hm : NMapRel absEIdx m M) {c : frontend.olean.index.Copy} (hc : CopyFits c) {o}
    (h : head_ty_step ix infos m c = ok o) : NMapRel absEIdx o (htStep ix' I M (absCopy c)) := by
  rw [head_ty_step] at h
  peel h as q, hq
  have eq := name_index_at_eq hix hc hq
  rw [htStep, ← eq]
  cases q with
  | none => cases Result.ok_injective h; exact hm
  | some q =>
    simp only [Option.map_some]
    peel h as f, hf
    obtain ⟨ef, ff⟩ := hix.first.get_eq hf
    simp only [absNamePosition_name, ← ef]
    cases f with
    | none => cases Result.ok_injective h; exact hm
    | some f =>
      simp only [Option.map_some, Option.bind_some]
      peel h as x, hx
      have ex := hI.get_eq hx
      generalize I[absCopy f]? = y at ex ⊢
      cases ex with
      | none => cases Result.ok_injective h; exact hm
      | some hr =>
        rename_i a b
        obtain ⟨sr, k⟩ := a
        peel h as n, hn
        cases nidx_dup2_ok hn
        peel h as e, he
        cases eidx_dup2_ok he
        peel h as r, hr2
        obtain ⟨old, m1⟩ := r
        cases Result.ok_injective h
        have := hm.insert hr2
        have eb : b.1.type = absEIdx sr.ty := by rw [← hr.1]; rfl
        simp only [eb]
        exact this

theorem head_tys_of_loop_eq {ix ix'} (hix : NameIndexRel ix ix') {infos I} (hI : CMapRel InfoRel infos I)
    (heads : alloc.vec.Vec frontend.olean.index.Copy) (hfit : ∀ c ∈ heads.val, CopyFits c)
    (m : ron.hashmap2.HashMap2 arena.handle.NIdx arena.handle.EIdx) {M} (hm : NMapRel absEIdx m M)
    (i : Std.Usize) {o} (h : head_tys_of_loop ix infos heads m i = ok o) :
    NMapRel absEIdx o (((heads.val.drop i.val).map absCopy).foldl (htStep ix' I) M) := by
  rw [head_tys_of_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len heads
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as c, hc
    obtain ⟨_, rfl⟩ := vec_index_eq hc
    peel h as m1, hm1
    have hs := head_ty_step_eq hix hI hm (hfit _ (List.getElem_mem hi)) hm1
    peel h as i2, hi2
    have ei2 := usize_succ hi2
    have ih := head_tys_of_loop_eq hix hI heads hfit m1 hs i2 h
    rw [ei2] at ih
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldl_cons]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    exact hm
termination_by heads.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`head_tys_of` is `headTysOf`.** -/
theorem head_tys_of_eq {ix ix'} (hix : NameIndexRel ix ix') {infos I} (hI : CMapRel InfoRel infos I)
    {heads : alloc.vec.Vec frontend.olean.index.Copy} (hfit : ∀ c ∈ heads.val, CopyFits c) {o}
    (h : head_tys_of ix infos heads = ok o) :
    NMapRel absEIdx o.m (Arena.Frontend.Olean.headTysOf ix' I (heads.val.map absCopy).toArray) := by
  rw [head_tys_of] at h
  peel h as m, hm
  peel h as m1, hm1
  cases Result.ok_injective h
  have := head_tys_of_loop_eq hix hI heads hfit m (NMapRel.with_capacity hm) 0#usize hm1
  rw [headTysOf_eq]
  simpa using this

/-- **`HeadTys` answers the twin's table.** -/
theorem head_tys_rel {h : frontend.olean.index.HeadTys} {M : Std.HashMap NIdx EIdx}
    (hm : NMapRel absEIdx h.m M) :
    HeadTyRel HeadTys.Insts.Con_ron_coreFrontendOleanMergeHeadTy h (M[·]?) := by
  intro n o hn
  change HeadTys.Insts.Con_ron_coreFrontendOleanMergeHeadTy.head_ty h n = ok o at hn
  rw [HeadTys.Insts.Con_ron_coreFrontendOleanMergeHeadTy.head_ty] at hn
  peel hn as o1, h1
  have e := hm.get_eq h1
  show M[absNIdx n]? = _
  rw [← e]
  cases o1 with
  | none => cases Result.ok_injective hn; rfl
  | some t =>
    peel hn as t1, ht1
    cases eidx_dup2_ok ht1
    cases Result.ok_injective hn
    rfl

/-! ## The heads of the axiom clashes -/

/-- The twin's step of `clashHeads`. -/
def chStep (ix' : Arena.Frontend.Olean.NameIndex) (acc : _root_.Array ConLeche.Frontend.Olean.Copy)
    (cl : Arena.Frontend.Olean.Clash) : AM (_root_.Array ConLeche.Frontend.Olean.Copy) := do
  match cl.copies[0]? with
  | some (_, cv, ConLeche.Frontend.Olean.CKindF.ax _) =>
    match (← isPropCheapHeadOf cv.type).bind (ix'.first[·]?) with
    | some c => pure (acc.push c)
    | none => pure acc
  | _ => pure acc

theorem clashHeads_eq (ix' : Arena.Frontend.Olean.NameIndex) (clashes : _root_.Array Arena.Frontend.Olean.Clash) :
    Arena.Frontend.Olean.clashHeads ix' clashes = clashes.toList.foldlM (chStep ix') #[] := by
  rw [Arena.Frontend.Olean.clashHeads, Array.foldlM_toList]
  rfl

/-- The heads so far, against the twin's. -/
def HeadsRel (acc : alloc.vec.Vec frontend.olean.index.Copy) (A : _root_.Array ConLeche.Frontend.Olean.Copy) :
    Prop :=
  acc.val.map absCopy = A.toList ∧ ∀ c ∈ acc.val, CopyFits c

/-- One clash's head onto the heads so far. -/
def HeadStepRel (acc : alloc.vec.Vec frontend.olean.index.Copy) (o : Option frontend.olean.index.Copy)
    (A : _root_.Array ConLeche.Frontend.Olean.Copy) : Prop :=
  (match o with | none => acc.val | some c => acc.val ++ [c]).map absCopy = A.toList ∧
    ∀ c, o = some c → CopyFits c

theorem forall₂_length' {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : l.length = l'.length := List.Forall₂.length_eq h

/-- **`clash_head` is the twin's step**, onto any heads so far. -/
theorem clash_head_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {ix ix'} (hix : NameIndexRel ix ix') {cl : frontend.olean.index.Clash} {cl' : Arena.Frontend.Olean.Clash}
    (hcl : ClashRel cl cl') {acc A} (hA : HeadsRel acc A) :
    CR pers (HeadStepRel acc) st lst (clash_head pers st.store ix cl) (chStep ix' A cl') := by
  rw [clash_head, chStep]
  have hlen := forall₂_length' hcl.copies
  by_cases h0 : alloc.vec.Vec.len cl.copies = 0#usize
  · rw [ite_eq_left h0]
    have : cl.copies.val.length = 0 := by
      have := congrArg (·.val) h0; simpa [vec_len_val] using this
    have e : cl'.copies[0]? = none := by
      rw [← Array.getElem?_toList, List.getElem?_eq_none (by omega)]
    rw [e]
    exact CR.pure ⟨by simpa using hA.1, fun _ h => by cases h⟩
  · rw [ite_eq_right h0]
    have hpos : 0 < cl.copies.val.length := by
      rcases Nat.eq_zero_or_pos cl.copies.val.length with hz | hp
      · exact absurd (UScalar.eq_of_val_eq (by rw [vec_len_val, hz]; rfl)) h0
      · exact hp
    obtain ⟨y, hy, hr⟩ := forall₂_getElem? hcl.copies (List.getElem?_eq_getElem hpos)
    have e : cl'.copies[0]? = some y := by rw [← Array.getElem?_toList]; exact hy
    rw [e]
    refine CR.pure_step fun x hx => ?_
    obtain ⟨_, hxe⟩ := vec_index_eq hx
    have hxe' : x = cl.copies.val[0] := hxe
    rw [← hxe'] at hr
    obtain ⟨c0, sr, cf⟩ := x
    dsimp only [Std.uncurry]
    obtain ⟨c0', cv, k'⟩ := y
    obtain ⟨-, hs, hk⟩ := hr
    simp only at hs hk
    have nonax : ∀ (r : Result (core.result.Result (Option frontend.olean.index.Copy) kernel.core_types.CheckError)),
        r = ok (.Ok none) → CR pers (HeadStepRel acc) st lst r (pure A : AM _) := by
      intro r hr; rw [hr]; exact CR.pure ⟨by simpa using hA.1, fun _ h => by cases h⟩
    cases cf <;> cases k'
    case Ax.ax u u' =>
      rw [← hs]
      refine CR.bind (is_prop_cheap_head_of_rel sr.ty) (fun _ => rfl) fun o o' lst1 ho => ?_
      cases ho
      cases o with
      | none => exact CR.pure ⟨by simpa using hA.1, fun _ h => by cases h⟩
      | some n =>
        refine CR.pure_step fun f hf => ?_
        obtain ⟨ef, ff⟩ := hix.first.get_eq hf
        simp only [Option.map_some, Option.bind_some, ← ef]
        cases f with
        | none => exact CR.pure ⟨by simpa using hA.1, fun _ h => by cases h⟩
        | some f =>
          refine CR.pure_step fun f1 hf1 => ?_
          cases copy_dup2_ok hf1
          exact CR.pure ⟨by simp [hA.1], fun c h => by cases h; exact ff f rfl⟩
    all_goals first | exact (hk : False).elim | exact nonax _ rfl


theorem clash_heads_loop_rel {pers : arena.store.PersTier} {ix ix'} (hix : NameIndexRel ix ix')
    (clashes : alloc.vec.Vec frontend.olean.index.Clash) {CL : List Arena.Frontend.Olean.Clash}
    (hcl : List.Forall₂ ClashRel clashes.val CL)
    (acc : alloc.vec.Vec frontend.olean.index.Copy) (i : Std.Usize) {A} (hA : HeadsRel acc A)
    (st : arena.monad.AState) (lst : AState) :
    CR pers HeadsRel st lst (clash_heads_loop pers st.store ix clashes acc i)
      ((CL.drop i.val).foldlM (chStep ix') A) := by
  rw [clash_heads_loop]
  have hlen := forall₂_length' hcl
  by_cases hlt : i < alloc.vec.Vec.len clashes
  · rw [ite_eq_left hlt]
    have hi := lt_of_lt_len hlt
    refine CR.pure_step fun c hc => ?_
    obtain ⟨_, rfl⟩ := vec_index_eq hc
    obtain ⟨y, hy, hr⟩ := forall₂_getElem? hcl (List.getElem?_eq_getElem hi)
    have hi' : i.val < CL.length := by omega
    have hye : CL[i.val] = y := by rw [List.getElem?_eq_getElem hi'] at hy; exact Option.some.inj hy
    rw [List.drop_eq_getElem_cons hi', List.foldlM_cons, hye]
    refine CR.bind (clash_head_rel hix hr hA) (fun _ => rfl) fun o A' lst1 ho => ?_
    refine CR.pure_step fun acc1 hacc1 => ?_
    have hA1 : HeadsRel acc1 A' := by
      cases o with
      | none => cases Result.ok_injective hacc1; exact ⟨by simpa using ho.1, hA.2⟩
      | some c1 =>
        refine ⟨?_, ?_⟩
        · rw [ConRon.Refine.vec_push_val hacc1]; simpa using ho.1
        · rw [ConRon.Refine.vec_push_val hacc1]
          intro c' hc'
          rcases List.mem_append.mp hc' with hc' | hc'
          · exact hA.2 c' hc'
          · rw [List.mem_singleton.mp hc']; exact ho.2 c1 rfl
    refine CR.pure_step fun i2 hi2 => ?_
    have ei2 := usize_succ hi2
    have ih := clash_heads_loop_rel (pers := pers) hix clashes hcl acc1 i2 hA1 st lst1
    rw [ei2] at ih
    exact ih
  · rw [ite_eq_right hlt]
    rw [List.drop_of_length_le (by have := lt_of_not_lt_len hlt; omega)]
    exact CR.pure hA
termination_by clashes.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`clash_heads` is `clashHeads`.** -/
theorem clash_heads_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {ix ix'} (hix : NameIndexRel ix ix') {clashes : alloc.vec.Vec frontend.olean.index.Clash}
    {CL : _root_.Array Arena.Frontend.Olean.Clash} (hcl : List.Forall₂ ClashRel clashes.val CL.toList) :
    CR pers HeadsRel st lst (clash_heads pers st.store ix clashes) (Arena.Frontend.Olean.clashHeads ix' CL) := by
  rw [clashHeads_eq]
  have e0 : (alloc.vec.Vec.new frontend.olean.index.Copy).val = [] := rfl
  simpa using clash_heads_loop_rel hix clashes hcl _ 0#usize (A := #[])
    ⟨by rw [e0]; rfl, fun c hc => by rw [e0] at hc; cases hc⟩ st lst

/-! ## `CA`: the accept of a read of the store -/

/-- **The accept of a read of the store**: the Rust's `Ok` over `st.store` is a run of the twin,
in a related state.  An `Err` claims nothing (the checks' rejects). -/
def CA {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result α kernel.core_types.CheckError)) (x : AM β) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st →
    ∀ a, m = ok (.Ok a) → ∃ b lst', x.run lst = .ok (b, lst') ∧ R a b ∧
      AStateRel₀ pers st lst' ∧ AStateInv pers st

theorem CR.ca {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {m} {x : AM β} (h : CR pers R st lst m x) :
    CA pers R st lst m x := fun hrel hinv _ hm => h hrel hinv _ hm

theorem CA.pure {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {a : α} {b : β} (hR : R a b) :
    CA pers R st lst (ok (.Ok a)) (Pure.pure b) := (CR.pure hR).ca

theorem CA.err {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {e} {x : AM β} :
    CA pers R st lst (ok (.Err e : core.result.Result α _)) x := by
  intro _ _ a h; cases Result.ok_injective h

theorem CA.pure_step {α β γ : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {f : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError)}
    {x : AM β} (h : ∀ a, f = ok a → CA pers R st lst (k a) x) :
    CA pers R st lst (Std.bind f k) x := by
  intro hrel hinv o hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a h1 hrel hinv o h2

theorem CA.bind {α₁ β₁ α β : Type} {pers : arena.store.PersTier} {R₁ : α₁ → β₁ → Prop}
    {R : α → β → Prop} {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result α₁ kernel.core_types.CheckError)}
    {k : core.result.Result α₁ kernel.core_types.CheckError →
      Result (core.result.Result α kernel.core_types.CheckError)}
    {x : AM β₁} {g : β₁ → AM β}
    (hf : CA pers R₁ st lst f x)
    (he : ∀ e, k (.Err e) = ok (.Err e))
    (hk : ∀ a b lst1, R₁ a b → CA pers R st lst1 (k (.Ok a)) (g b)) :
    CA pers R st lst (Std.bind f k) (x >>= g) := by
  intro hrel hinv o hm
  obtain ⟨r, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  cases r with
  | Ok a =>
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := hf hrel hinv a hf1
    rw [am_bind_ok hx]
    exact hk a b lst1 hR hrel1 hinv1 o hk1
  | Err e => rw [he e] at hk1; cases Result.ok_injective hk1

/-- The twin's result dropped. -/
theorem CA.discard {β : Type} {pers : arena.store.PersTier} {R : Unit → β → Prop}
    {st : arena.monad.AState} {lst : AState} {m : Result (core.result.Result Unit kernel.core_types.CheckError)}
    {x : AM β} (h : CA pers R st lst m x) :
    CA pers (fun _ _ => True) st lst m (do let _ ← x; Pure.pure ()) := by
  intro hrel hinv a hm
  obtain ⟨b, lst1, hx, -, hrel1, hinv1⟩ := h hrel hinv a hm
  exact ⟨(), lst1, by rw [am_bind_ok hx]; rfl, trivial, hrel1, hinv1⟩

/-! ## The clash rule -/

/-- The twin's step of `clashOk`. -/
def ccoStep (pk : Arena.Frontend.Olean.OleanPins) (ld : Arena.Frontend.Olean.HeaderLoads)
    (headTy : NIdx → Option EIdx) (c : Arena.Frontend.Olean.Clash)
    (kept next : ConLeche.Frontend.Olean.Copy × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) :
    AM (ConLeche.Frontend.Olean.Copy × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) := do
  let (_, cv₁, k₁) := next
  let (_, cv₂, k₂) := kept
  if ← Arena.Frontend.Olean.subsumesF pk headTy cv₁ k₁ cv₂ k₂ then pure next
  else if ← Arena.Frontend.Olean.subsumesF pk headTy cv₂ k₂ cv₁ k₁ then pure kept
  else fail (.invalid s!"modules {← readName (ld.nameAt pk kept.1.mod)} and \
    {← readName (ld.nameAt pk next.1.mod)} store different constants named \
    {← readName c.name}, and both are loaded")

theorem clashOk_eq (pk ld headTy) (c : Arena.Frontend.Olean.Clash) :
    Arena.Frontend.Olean.clashOk pk ld headTy c =
      (match c.copies.toList with
      | [] => Pure.pure ()
      | k :: rest => do let _ ← rest.foldlM (ccoStep pk ld headTy c) k; Pure.pure ()) := rfl

/-- **`clash_step`'s accept is the twin's step.** -/
theorem clash_step_ok {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (pk : frontend.olean.spec.OleanPins) {ld ld'} {h : frontend.olean.index.HeadTys}
    {headTy : NIdx → Option EIdx}
    (hH : HeadTyRel HeadTys.Insts.Con_ron_coreFrontendOleanMergeHeadTy h headTy)
    {c : frontend.olean.index.Clash} (c' : Arena.Frontend.Olean.Clash) {C}
    (hc : List.Forall₂ CopyInfoRel c.copies.val C) {kept i : Std.Usize}
    (hk : kept.val < C.length) (hi : i.val < C.length) :
    CA pers (fun (k : Std.Usize) b => ∃ hk : k.val < C.length, b = C[k.val]) st lst
      (clash_step pk pers st.store ld h c kept i)
      (ccoStep (absPins pk) ld' headTy c' C[kept.val] C[i.val]) := by
  rw [clash_step]
  have hlen := forall₂_length' hc
  refine CA.pure_step fun nx hnx => ?_
  obtain ⟨_, hnxe⟩ := vec_index_eq hnx
  refine CA.pure_step fun kp hkp => ?_
  obtain ⟨_, hkpe⟩ := vec_index_eq hkp
  obtain ⟨y1, hy1, hr1⟩ := forall₂_getElem? hc (List.getElem?_eq_getElem (show i.val < c.copies.val.length by omega))
  obtain ⟨y2, hy2, hr2⟩ := forall₂_getElem? hc (List.getElem?_eq_getElem (show kept.val < c.copies.val.length by omega))
  rw [List.getElem?_eq_getElem hi] at hy1
  rw [List.getElem?_eq_getElem hk] at hy2
  have ey1 : C[i.val] = y1 := Option.some.inj hy1
  have ey2 : C[kept.val] = y2 := Option.some.inj hy2
  rw [ey1, ey2]
  rw [← hnxe] at hr1
  rw [← hkpe] at hr2
  obtain ⟨c1, sr, cf⟩ := nx
  obtain ⟨c2, sr1, cf1⟩ := kp
  obtain ⟨c1', cv1, k1'⟩ := y1
  obtain ⟨c2', cv2, k2'⟩ := y2
  obtain ⟨-, hs1, hk1⟩ := hr1
  obtain ⟨-, hs2, hk2⟩ := hr2
  simp only at hs1 hk1 hs2 hk2
  subst hs1 hs2
  dsimp only [Std.uncurry]
  rw [ccoStep]
  dsimp only
  refine CA.bind (subsumes_f_rel pk hH sr sr1 hk1 hk2).ca (fun _ => rfl) fun b b' lst1 hb => ?_
  cases hb
  cases b with
  | true => exact CA.pure ⟨hi, ey1.symm⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine CA.bind (subsumes_f_rel pk hH sr1 sr hk2 hk1).ca (fun _ => rfl) fun b b' lst2 hb => ?_
    cases hb
    cases b with
    | true => exact CA.pure ⟨hk, ey2.symm⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact CA.pure_step fun _ _ => CA.err


theorem clash_ok_loop_ok {pers : arena.store.PersTier} (pk : frontend.olean.spec.OleanPins) {ld ld'}
    {h : frontend.olean.index.HeadTys} {headTy : NIdx → Option EIdx}
    (hH : HeadTyRel HeadTys.Insts.Con_ron_coreFrontendOleanMergeHeadTy h headTy)
    (c : frontend.olean.index.Clash) (c' : Arena.Frontend.Olean.Clash) {C}
    (hc : List.Forall₂ CopyInfoRel c.copies.val C) (kept i : Std.Usize) (hk : kept.val < C.length)
    (st : arena.monad.AState) (lst : AState) :
    CA pers (fun _ _ => True) st lst (clash_ok_loop pk pers st.store ld h c kept i)
      ((C.drop i.val).foldlM (ccoStep (absPins pk) ld' headTy c') C[kept.val]) := by
  rw [clash_ok_loop]
  have hlen := forall₂_length' hc
  by_cases hlt : i < alloc.vec.Vec.len c.copies
  · rw [ite_eq_left hlt]
    have hi := lt_of_lt_len hlt
    have hi' : i.val < C.length := by omega
    rw [List.drop_eq_getElem_cons hi', List.foldlM_cons]
    refine CA.bind (clash_step_ok (ld := ld) pk hH c' hc hk hi') (fun _ => rfl) fun k b lst1 hkb => ?_
    obtain ⟨hk1, rfl⟩ := hkb
    refine CA.pure_step fun i2 hi2 => ?_
    have ei2 := usize_succ hi2
    have ih := clash_ok_loop_ok (pers := pers) (ld := ld) (ld' := ld') pk hH c c' hc k i2 hk1 st lst1
    rw [ei2] at ih
    exact ih
  · rw [ite_eq_right hlt, List.drop_of_length_le (by have := lt_of_not_lt_len hlt; omega)]
    exact CA.pure trivial
termination_by c.copies.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`clash_ok`'s accept is `clashOk`'s.** -/
theorem clash_ok_ok {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (pk : frontend.olean.spec.OleanPins) {ld ld'}
    {h : frontend.olean.index.HeadTys} {headTy : NIdx → Option EIdx}
    (hH : HeadTyRel HeadTys.Insts.Con_ron_coreFrontendOleanMergeHeadTy h headTy)
    {c : frontend.olean.index.Clash} {c' : Arena.Frontend.Olean.Clash} (hc : ClashRel c c') :
    CA pers (fun _ _ => True) st lst (clash_ok pk pers st.store ld h c)
      (Arena.Frontend.Olean.clashOk (absPins pk) ld' headTy c') := by
  rw [clash_ok, clashOk_eq]
  have hlen := forall₂_length' hc.copies
  cases hC : c'.copies.toList with
  | nil =>
    rw [hC] at hlen
    rw [clash_ok_loop, ite_eq_right (by
      intro hl; have := lt_of_lt_len hl; have e1 : (1#usize : Std.Usize).val = 1 := rfl
      simp only [List.length_nil] at hlen; omega)]
    exact CA.pure trivial
  | cons k rest =>
    have hcs := hc.copies
    rw [hC] at hcs
    have := clash_ok_loop_ok (pers := pers) (ld := ld) (ld' := ld') pk hH c c' hcs 0#usize 1#usize
      (by simp) st lst
    simpa using this.discard

theorem list_forM_cons {m : Type → Type} [Monad m] {α : Type} (a : α) (l : List α) (f : α → m PUnit) :
    (a :: l).forM f = (do f a; l.forM f) := rfl

theorem clashes_ok_loop_ok {pers : arena.store.PersTier} (pk : frontend.olean.spec.OleanPins) {ld ld'}
    {h : frontend.olean.index.HeadTys} {headTy : NIdx → Option EIdx}
    (hH : HeadTyRel HeadTys.Insts.Con_ron_coreFrontendOleanMergeHeadTy h headTy)
    (clashes : alloc.vec.Vec frontend.olean.index.Clash) {CL}
    (hcl : List.Forall₂ ClashRel clashes.val CL) (i : Std.Usize) (st : arena.monad.AState) (lst : AState) :
    CA pers (fun _ _ => True) st lst (clashes_ok_loop pk pers st.store ld h clashes i)
      ((CL.drop i.val).forM (Arena.Frontend.Olean.clashOk (absPins pk) ld' headTy)) := by
  rw [clashes_ok_loop]
  have hlen := forall₂_length' hcl
  by_cases hlt : i < alloc.vec.Vec.len clashes
  · rw [ite_eq_left hlt]
    have hi := lt_of_lt_len hlt
    have hi' : i.val < CL.length := by omega
    refine CA.pure_step fun c hc => ?_
    obtain ⟨_, rfl⟩ := vec_index_eq hc
    obtain ⟨y, hy, hr⟩ := forall₂_getElem? hcl (List.getElem?_eq_getElem hi)
    have ey : CL[i.val] = y := by rw [List.getElem?_eq_getElem hi'] at hy; exact Option.some.inj hy
    rw [List.drop_eq_getElem_cons hi', list_forM_cons, ey]
    refine CA.bind (clash_ok_ok (ld := ld) (ld' := ld') pk hH hr) (fun _ => rfl) fun _ _ lst1 _ => ?_
    refine CA.pure_step fun i2 hi2 => ?_
    have ei2 := usize_succ hi2
    have ih := clashes_ok_loop_ok (pers := pers) (ld := ld) (ld' := ld') pk hH clashes hcl i2 st lst1
    rw [ei2] at ih
    exact ih
  · rw [ite_eq_right hlt, List.drop_of_length_le (by have := lt_of_not_lt_len hlt; omega)]
    exact CA.pure trivial
termination_by clashes.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`clashes_ok`'s accept is the twin's `forM`.** -/
theorem clashes_ok_ok {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (pk : frontend.olean.spec.OleanPins) {ld ld'}
    {h : frontend.olean.index.HeadTys} {headTy : NIdx → Option EIdx}
    (hH : HeadTyRel HeadTys.Insts.Con_ron_coreFrontendOleanMergeHeadTy h headTy)
    {clashes : alloc.vec.Vec frontend.olean.index.Clash} {CL : _root_.Array Arena.Frontend.Olean.Clash}
    (hcl : List.Forall₂ ClashRel clashes.val CL.toList) :
    CA pers (fun _ _ => True) st lst (clashes_ok pk pers st.store ld h clashes)
      (CL.toList.forM (Arena.Frontend.Olean.clashOk (absPins pk) ld' headTy)) := by
  simpa using clashes_ok_loop_ok (pers := pers) (ld := ld) (ld' := ld') pk hH clashes hcl 0#usize st lst

/-! ## Freshness and the module system, accepted -/

/-- **`fresh_ok`'s accept is `freshOk`'s.** -/
theorem fresh_ok_ok {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (pk : frontend.olean.spec.OleanPins) (m : arena.handle.NIdx) {ld} (ld' : Arena.Frontend.Olean.HeaderLoads)
    {ix ix'} (hix : NameIndexRel ix ix') (own : frontend.olean.reads.NamePositions) :
    CA pers (fun _ _ => True) st lst (fresh_ok pk pers st.store m ld ix own)
      (Arena.Frontend.Olean.freshOk (absPins pk) (absNIdx m) ld' ix' (absNamePositions own)) := by
  intro hrel hinv a hm
  rw [fresh_ok] at hm
  peel hm as o, ho
  cases o with
  | none =>
    have e := first_loaded_none hix ho
    refine ⟨(), lst, ?_, trivial, hrel, hinv⟩
    simp only [Arena.Frontend.Olean.freshOk, e]
    rfl
  | some i =>
    exfalso
    repeat (peel hm as _, _)
    cases Result.ok_injective hm

/-- **`imports_modules_ok`'s accept is `importsModulesOk`'s.** -/
theorem imports_modules_ok_ok {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (m : arena.handle.NIdx) (is_module : Bool) {ld ld'} (hld : HeaderLoadsRel ld ld') (hw : IndexFits ld')
    {ix ix'} (hix : NameIndexRel ix ix') (imports : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) :
    CA pers (fun _ _ => True) st lst (imports_modules_ok pers st.store m is_module ld ix imports)
      (Arena.Frontend.Olean.importsModulesOk (absNIdx m) is_module ld' ix' (absImports imports)) := by
  intro hrel hinv a hm
  rw [imports_modules_ok] at hm
  refine ⟨(), lst, ?_, trivial, hrel, hinv⟩
  cases is_module with
  | false => rfl
  | true =>
    rw [ite_eq_left rfl] at hm
    peel hm as o, ho
    cases o with
    | none =>
      have e := first_classic_none hld hw hix ho
      unfold Arena.Frontend.Olean.importsModulesOk
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i i heq
        exact absurd (e.symm.trans heq) (by simp)
      · rfl
    | some i =>
      exfalso
      repeat (peel hm as _, _)
      cases Result.ok_injective hm

/-! ## The copies' statements, read -/

theorem read_infos_of_loop0_eq {ix ix'} (hix : NameIndexRel ix ix')
    (cs : alloc.vec.Vec frontend.olean.index.Copy) (hcs : ∀ c ∈ cs.val, CopyFits c)
    (locs : alloc.vec.Vec Std.U64) (j : Std.Usize) {o} (h : read_infos_of_loop0 ix cs locs j = ok o) :
    o.val.map (·.val) = locs.val.map (·.val) ++
      ((cs.val.drop j.val).map absCopy).filterMap fun c => (ix'.at c).map (·.loc) := by
  rw [read_infos_of_loop0] at h
  by_cases hlt : j < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    have hj := lt_of_lt_len hlt
    peel h as c, hc
    obtain ⟨_, rfl⟩ := vec_index_eq hc
    peel h as l, hl
    have el := name_index_loc_eq hix (hcs _ (List.getElem_mem hj)) hl
    peel h as locs1, hlocs1
    peel h as j1, hj1
    have ej1 := usize_succ hj1
    have ih := read_infos_of_loop0_eq hix cs hcs locs1 j1 h
    rw [ih, ej1, List.drop_eq_getElem_cons hj, List.map_cons, List.filterMap_cons, ← el]
    cases l with
    | none => cases Result.ok_injective hlocs1; simp
    | some l => rw [ConRon.Refine.vec_push_val hlocs1]; simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len hlt)]
    simp
termination_by cs.val.length - j.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

theorem read_infos_of_loop1_eq (cs : alloc.vec.Vec frontend.olean.index.Copy)
    (ss : alloc.vec.Vec frontend.olean.spec.StmtRec)
    (ks : alloc.vec.Vec (frontend.olean.spec.CKindF arena.handle.NIdx Unit)) (out : alloc.vec.Vec _)
    (k : Std.Usize) {o} (h : read_infos_of_loop1 cs ss ks out k = ok o) :
    o.val = out.val ++ ((cs.val.zip (ss.val.zip ks.val)).drop k.val) := by
  rw [read_infos_of_loop1] at h
  by_cases hlt : k < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    have hk := lt_of_lt_len hlt
    peel h as c, hc
    obtain ⟨_, rfl⟩ := vec_index_eq hc
    peel h as c1, hc1
    cases copy_dup2_ok hc1
    peel h as sr, hsr
    obtain ⟨hks, rfl⟩ := vec_index_eq hsr
    peel h as sr1, hsr1
    cases stmt_rec_dup_eq hsr1
    peel h as cf, hcf
    obtain ⟨hkk, rfl⟩ := vec_index_eq hcf
    peel h as cf1, hcf1
    cases c_kind_names_dup_eq hcf1
    peel h as out1, hout1
    peel h as k1, hk1
    have ek1 := usize_succ hk1
    have ih := read_infos_of_loop1_eq cs ss ks out1 k1 h
    have hz : k.val < (cs.val.zip (ss.val.zip ks.val)).length := by simp; omega
    rw [ih, ek1, ConRon.Refine.vec_push_val hout1, List.drop_eq_getElem_cons hz]
    simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (by have := lt_of_not_lt_len hlt; simp; omega)]
    simp
termination_by cs.val.length - k.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

theorem forall₂_zip_infos : ∀ (cs : List frontend.olean.index.Copy) (ss : List frontend.olean.spec.StmtRec)
    (ks : List (frontend.olean.spec.CKindF arena.handle.NIdx Unit)) (b : List Arena.Frontend.Olean.StmtRec)
    (bk : List (ConLeche.Frontend.Olean.CKindF NIdx Unit)),
    List.Forall₂ (EqA absStmtRec) ss b → List.Forall₂ KindNamesRel ks bk →
    List.Forall₂ CopyInfoRel (cs.zip (ss.zip ks)) ((cs.map absCopy).zip (b.zip bk))
  | [], _, _, _, _, _, _ => by simp
  | _ :: _, [], _, _, _, hb, _ => by cases hb; simp
  | _ :: _, _ :: _, [], _, _, hb, hk => by cases hb; cases hk; simp
  | c :: cs, s :: ss, k :: ks, _, _, hb, hk => by
    cases hb with
    | cons hs hb =>
      cases hk with
      | cons hk1 hk =>
        simp only [List.zip_cons_cons, List.map_cons]
        exact .cons ⟨rfl, hs.symm, hk1⟩ (forall₂_zip_infos cs ss ks _ _ hb hk)


/-- The twin's insertion of one read copy. -/
def insStep (m : Std.HashMap ConLeche.Frontend.Olean.Copy
      (Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit))
    (x : ConLeche.Frontend.Olean.Copy × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) :
    Std.HashMap ConLeche.Frontend.Olean.Copy
      (Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) :=
  m.insert x.1 (x.2.1, x.2.2)

/-- The twin's insertion of one module's read copies. -/
def insAll (m : Std.HashMap ConLeche.Frontend.Olean.Copy
      (Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit))
    (r : _root_.Array (ConLeche.Frontend.Olean.Copy × Arena.Frontend.Olean.StmtRec ×
      ConLeche.Frontend.Olean.CKindF NIdx Unit)) :
    Std.HashMap ConLeche.Frontend.Olean.Copy
      (Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit) :=
  r.toList.foldl insStep m

theorem readInfos_eq (fs pk sp ld ix) (cs : _root_.Array ConLeche.Frontend.Olean.Copy) :
    Arena.Frontend.Olean.readInfos fs pk sp ld ix cs =
      (do let rs ← (Arena.Frontend.Olean.byModule cs).toList.mapM
            (fun p => Arena.Frontend.Olean.readInfosOf fs pk sp ld ix p.1 p.2)
          Pure.pure (rs.foldl insAll {})) := by
  simp only [Arena.Frontend.Olean.readInfos, ← Array.foldl_toList]
  rfl

theorem read_infos_loop0_loop0_eq
    (m : ron.hashmap2.HashMap2 frontend.olean.index.Copy
      (frontend.olean.spec.StmtRec × frontend.olean.spec.CKindF arena.handle.NIdx Unit)) {M}
    (hm : CMapRel InfoRel m M) (r : alloc.vec.Vec _) {R} (hr : List.Forall₂ CopyInfoRel r.val R)
    (k : Std.Usize) {o} (h : read_infos_loop0_loop0 m r k = ok o) :
    CMapRel InfoRel o ((R.drop k.val).foldl insStep M) := by
  rw [read_infos_loop0_loop0] at h
  have hlen := forall₂_length' hr
  by_cases hlt : k < alloc.vec.Vec.len r
  · rw [ite_eq_left hlt] at h
    have hk := lt_of_lt_len hlt
    peel h as x, hx
    obtain ⟨_, hxe⟩ := vec_index_eq hx
    obtain ⟨y, hy, hxy⟩ := forall₂_getElem? hr (List.getElem?_eq_getElem hk)
    have hk' : k.val < R.length := by omega
    have ey : R[k.val] = y := by rw [List.getElem?_eq_getElem hk'] at hy; exact Option.some.inj hy
    rw [← hxe] at hxy
    obtain ⟨c, sr, cf⟩ := x
    dsimp only [Std.uncurry] at h
    peel h as c1, hc1
    cases copy_dup2_ok hc1
    peel h as sr1, hsr1
    cases stmt_rec_dup_eq hsr1
    peel h as cf1, hcf1
    cases c_kind_names_dup_eq hcf1
    peel h as q, hq
    obtain ⟨old, m1⟩ := q
    peel h as k1, hk1
    have ek1 := usize_succ hk1
    obtain ⟨y1, y2, y3⟩ := y
    obtain ⟨e1, e2⟩ := hxy
    simp only at e1
    have hm1 := hm.insert (v' := (y2, y3)) e2 hq
    have ih := read_infos_loop0_loop0_eq m1 hm1 r hr k1 h
    rw [ek1] at ih
    rw [List.drop_eq_getElem_cons hk', List.foldl_cons, ey]
    simpa [insStep, e1] using ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (by have := lt_of_not_lt_len hlt; omega)]
    exact hm
termination_by r.val.length - k.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

theorem list_mapM_cons {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} (a : α) (l : List α) (f : α → m β) :
    (a :: l).mapM f = (do let b ← f a; let bs ← l.mapM f; Pure.pure (b :: bs)) := by
  simp [List.mapM_cons]

section reads
variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}

/-- **`read_infos_of`'s accept is `readInfosOf`'s.** -/
theorem read_infos_of_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {ld ld'} (hld : HeaderLoadsRel ld ld') {ix ix'} (hix : NameIndexRel ix ix') {i : Std.U64}
    (hi : i.val ≤ Std.Usize.max) {cs : alloc.vec.Vec frontend.olean.index.Copy}
    (hcs : ∀ c ∈ cs.val, CopyFits c) :
    AS pers (fun v A => List.Forall₂ CopyInfoRel v.val A.toList) st lst
      (read_infos_of inst fsv pk pers st.store sp ld ix i cs)
      (Arena.Frontend.Olean.readInfosOf fs (absPins pk) (absRoots sp) ld' ix' i.val
        (cs.val.map absCopy).toArray) := by
  intro hrel hinv a s' h
  rw [read_infos_of] at h
  peel h as m, hm
  have em := header_loads_name_at_eq hld hi hm
  peel h as level, hlevel
  have el := header_loads_level_at_eq hld hi hlevel
  peel h as locs1, hlocs1
  have elocs := read_infos_of_loop0_eq hix cs hcs _ 0#usize hlocs1
  have e0 : (alloc.vec.Vec.with_capacity Std.U64 (alloc.vec.Vec.len cs)).val = [] := rfl
  rw [e0] at elocs
  have z : (0#usize : Std.Usize).val = 0 := rfl
  simp only [List.map_nil, List.nil_append, z, List.drop_zero] at elocs
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok f =>
    obtain ⟨n, hn⟩ := read_files_name hr
    obtain ⟨f', hf', hfr⟩ := read_files_refines hfs hn hr
    peel h as q1, hq1
    obtain ⟨r1, ar1⟩ := q1
    have hs := read_stmts_refines hfr (level := level) (cs := locs1) hrel hinv r1 ar1 hq1
    cases r1 with
    | Err re => cases re <;> (repeat (peel h as _, _)) <;> cases Result.ok_injective h
    | Ok ss =>
      obtain ⟨b, lst1, hx1, hb, hrel1, hinv1⟩ := hs
      peel h as q2, hq2
      obtain ⟨r2, ar2⟩ := q2
      have hk := read_kinds_refines (st := withStore st ar1) hfr (level := level) (cs := locs1)
        hrel1 hinv1 r2 ar2 hq2
      cases r2 with
      | Err re => cases re <;> (repeat (peel h as _, _)) <;> cases Result.ok_injective h
      | Ok ks =>
        obtain ⟨bk, lst2, hx2, hbk, hrel2, hinv2⟩ := hk
        have ls := forall₂_length' hb
        have lk := forall₂_length' hbk
        dsimp only [Std.uncurry] at h
        by_cases c1 : (alloc.vec.Vec.len ss != alloc.vec.Vec.len cs) = true
        · rw [ite_eq_left c1] at h
          repeat (peel h as _, _)
          cases Result.ok_injective h
        · rw [ite_eq_right c1] at h
          by_cases c2 : (alloc.vec.Vec.len ks != alloc.vec.Vec.len cs) = true
          · rw [ite_eq_left c2] at h
            repeat (peel h as _, _)
            cases Result.ok_injective h
          · rw [ite_eq_right c2] at h
            peel h as out1, hout1
            have e := Result.ok_injective h
            simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            have eo := read_infos_of_loop1_eq cs ss ks _ 0#usize hout1
            have e0' : (alloc.vec.Vec.with_capacity (frontend.olean.index.Copy × frontend.olean.spec.StmtRec ×
              frontend.olean.spec.CKindF arena.handle.NIdx Unit) (alloc.vec.Vec.len cs)).val = [] := rfl
            rw [e0'] at eo
            simp only [List.nil_append, z, List.drop_zero] at eo
            have hss : ss.val.length = cs.val.length := by
              have : ¬ ((alloc.vec.Vec.len ss).val ≠ (alloc.vec.Vec.len cs).val) := by
                intro hne; exact c1 (by simpa [bne_iff_ne] using fun h => hne (congrArg _ h))
              simp only [vec_len_val] at this; omega
            have hks : ks.val.length = cs.val.length := by
              have : ¬ ((alloc.vec.Vec.len ks).val ≠ (alloc.vec.Vec.len cs).val) := by
                intro hne; exact c2 (by simpa [bne_iff_ne] using fun h => hne (congrArg _ h))
              simp only [vec_len_val] at this; omega
            refine ⟨((cs.val.map absCopy).zip (b.zip bk)).toArray, lst2, ?_, ?_, hrel2, hinv2⟩
            · simp only [Arena.Frontend.Olean.readInfosOf]
              rw [← em, ← el, am_bind_ok (read_name_run hrel hn)]
              simp only [hf', Arena.Frontend.Olean.liftE, ← elocs]
              rw [pure_bind, am_bind_ok hx1]
              simp only []
              rw [am_bind_ok hx2]
              have c3 : (b.length == (cs.val.map absCopy).toArray.size && bk.length == (cs.val.map absCopy).toArray.size) = true := by
                simp; omega
              simp only [c3, ↓reduceIte]
              simp
              rfl
            · show List.Forall₂ _ _ _
              rw [eo]
              simpa using forall₂_zip_infos cs.val ss.val ks.val b bk hb hbk


theorem read_infos_loop0_refines (hfs : FsRel inst fsv fs) {pk pers} {sp : frontend.olean.files.Roots}
    {ld ld'} (hld : HeaderLoadsRel ld ld') {ix ix'} (hix : NameIndexRel ix ix')
    (groups : alloc.vec.Vec (Std.U64 × alloc.vec.Vec frontend.olean.index.Copy))
    (hfit : ∀ p ∈ groups.val, p.1.val ≤ Std.Usize.max ∧ ∀ c ∈ p.2.val, CopyFits c)
    (m : ron.hashmap2.HashMap2 frontend.olean.index.Copy
      (frontend.olean.spec.StmtRec × frontend.olean.spec.CKindF arena.handle.NIdx Unit)) {M}
    (hm : CMapRel InfoRel m M) (i : Std.Usize) (st : arena.monad.AState) (lst : AState) :
    AS pers (fun o rs => CMapRel InfoRel o (rs.foldl insAll M)) st lst
      (read_infos_loop0 inst fsv pk pers st.store sp ld ix groups m i)
      (((groups.val.map absBM).drop i.val).mapM
        (fun p => Arena.Frontend.Olean.readInfosOf fs (absPins pk) (absRoots sp) ld' ix' p.1 p.2)) := by
  intro hrel hinv a s' h
  rw [read_infos_loop0] at h
  by_cases hlt : i < alloc.vec.Vec.len groups
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as g, hg
    obtain ⟨_, hge⟩ := vec_index_eq hg
    have hgf := hfit g (by rw [hge]; exact List.getElem_mem hi)
    obtain ⟨i2, v⟩ := g
    dsimp only [Std.uncurry] at h
    peel h as q, hq
    obtain ⟨r, ar1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective h
    | Ok r1 =>
      obtain ⟨b, lst1, hx, hb, hrel1, hinv1⟩ :=
        read_infos_of_refines hfs hld hix hgf.1 hgf.2 hrel hinv r1 ar1 hq
      peel h as m1, hm1
      have hm1' := read_infos_loop0_loop0_eq m hm r1 hb 0#usize hm1
      peel h as i3, hi3
      have ei3 := usize_succ hi3
      obtain ⟨rs, lst2, hx2, hrs, hrel2, hinv2⟩ :=
        read_infos_loop0_refines hfs hld hix groups hfit m1 hm1' i3 (withStore st ar1) lst1 hrel1 hinv1 a s' h
      rw [ei3] at hx2
      refine ⟨b :: rs, lst2, ?_, ?_, hrel2, hinv2⟩
      · rw [List.drop_eq_getElem_cons (by simpa using hi), list_mapM_cons, List.getElem_map, ← hge]
        rw [am_bind_ok hx]
        rw [am_bind_ok hx2]
        rfl
      · simpa [insAll] using hrs
  · rw [ite_eq_right hlt] at h
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨[], lst, ?_, by simpa using hm, hrel, hinv⟩
    rw [List.drop_of_length_le (by have := lt_of_not_lt_len hlt; simpa using this)]
    rfl
termination_by groups.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`read_infos`'s accept is `readInfos`'.** -/
theorem read_infos_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {ld ld'} (hld : HeaderLoadsRel ld ld') {ix ix'} (hix : NameIndexRel ix ix')
    {cs : alloc.vec.Vec frontend.olean.index.Copy} (hcs : ∀ c ∈ cs.val, CopyFits c) :
    AS pers (CMapRel InfoRel) st lst (read_infos inst fsv pk pers st.store sp ld ix cs)
      (Arena.Frontend.Olean.readInfos fs (absPins pk) (absRoots sp) ld' ix' (cs.val.map absCopy).toArray) := by
  intro hrel hinv a s' h
  rw [read_infos] at h
  peel h as groups, hgroups
  obtain ⟨eg, fg⟩ := by_module_eq hcs hgroups
  peel h as m, hm
  obtain ⟨rs, lst1, hx, hrs, hrel1, hinv1⟩ :=
    read_infos_loop0_refines hfs hld hix groups fg m (M := {}) (CMapRel.with_capacity hm) 0#usize st lst
      hrel hinv a s' h
  refine ⟨_, lst1, ?_, hrs, hrel1, hinv1⟩
  rw [readInfos_eq, ← eg]
  rw [am_bind_ok (by simpa using hx)]
  rfl

end reads

/-! ## The loaded parts' names -/

/-- `headerFixpoint` returns the loads of a fixpoint state. -/
theorem headerFixpoint_ofState {fs pk sp b imps} {lst lst' : AState} {ld' : Arena.Frontend.Olean.HeaderLoads}
    (h : (Arena.Frontend.Olean.headerFixpoint fs pk sp b imps).run lst = .ok (ld', lst')) :
    ∃ s, ld' = Arena.Frontend.Olean.HeaderLoads.ofState s := by
  unfold Arena.Frontend.Olean.headerFixpoint at h
  rw [StateT.run_bind] at h
  cases hr : (Arena.Frontend.Olean.levelsGo fs pk sp (!b) ConLeche.Frontend.Olean.closureFuel
      (Arena.Frontend.Olean.LvWork.ofImports { importAll := true, isExported := b } imps) {}).run lst with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    obtain ⟨s, l⟩ := p
    exact ⟨s, (Prod.mk.inj (Except.ok.inj h)).1.symm⟩

theorem ofStateGo_flags_size (fm : Std.HashMap NIdx ConLeche.Frontend.Olean.LoadFlags) :
    ∀ (ms : List NIdx) (i : Nat) im fl is ix,
      (Arena.Frontend.Olean.HeaderLoads.ofStateGo fm ms i im fl is ix).1.size = fl.size + ms.length
  | [], _, _, _, _, _ => by simp [Arena.Frontend.Olean.HeaderLoads.ofStateGo]
  | m :: ms, i, im, fl, is, ix => by
    rw [Arena.Frontend.Olean.HeaderLoads.ofStateGo, ofStateGo_flags_size fm ms]
    simp; omega

theorem ofState_sizes (s : Arena.Frontend.Olean.LvState) :
    (Arena.Frontend.Olean.HeaderLoads.ofState s).order.size =
      (Arena.Frontend.Olean.HeaderLoads.ofState s).flags.size := by
  simp only [Arena.Frontend.Olean.HeaderLoads.ofState, ofStateGo_flags_size]
  simp

section reads
variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}

/-- The twin's read of one loaded part. -/
def partT (fs : Arena.Frontend.Olean.OleanFs) (pk : Arena.Frontend.Olean.OleanPins)
    (sp : ConLeche.Frontend.Olean.Roots) (p : NIdx × ConLeche.Frontend.Olean.LoadFlags) :
    AM Arena.Frontend.Olean.NamePositions :=
  Arena.Frontend.Olean.readPartNames fs pk sp p.1 p.2.level

theorem loaded_parts_loop_refines (hfs : FsRel inst fsv fs) {pk pers} {sp : frontend.olean.files.Roots}
    {ld ld'} (hld : HeaderLoadsRel ld ld') (hsz : ld'.order.size = ld'.flags.size)
    (parts : alloc.vec.Vec frontend.olean.reads.NamePositions) (i : Std.Usize)
    (st : arena.monad.AState) (lst : AState) :
    AS pers (fun o rs => o.val.map absNamePositions = parts.val.map absNamePositions ++ rs) st lst
      (loaded_parts_loop inst fsv pk pers st.store sp ld.order ld.flags ld.imports ld.index parts i)
      (((ld'.order.zip ld'.flags).toList.drop i.val).mapM (partT fs (absPins pk) (absRoots sp))) := by
  intro hrel hinv a s' h
  rw [loaded_parts_loop] at h
  have ho := congrArg List.length hld.order
  have hf := congrArg List.length hld.flags
  simp only [List.length_map, Array.length_toList] at ho hf
  by_cases hlt : i < alloc.vec.Vec.len ld.order
  · rw [ite_eq_left hlt] at h
    have hi := lt_of_lt_len hlt
    peel h as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    peel h as i2, hi2
    have ei2 : i2.val = i.val := by rw [← Result.ok_injective hi2, cast_u64_val]
    peel h as ol, hol
    have el := header_loads_level_at_eq (ld := ld) hld (by rw [ei2]; exact usize_le_max i) hol
    peel h as q, hq
    obtain ⟨r, ar1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective h
    | Ok p =>
      obtain ⟨b, lst1, hx, hb, hrel1, hinv1⟩ :=
        read_part_names_refines (m := ld.order.val[i.val]) (level := ol) hfs hrel hinv p ar1 hq
      peel h as parts1, hparts1
      peel h as i3, hi3
      have ei3 := usize_succ hi3
      obtain ⟨rs, lst2, hx2, hrs, hrel2, hinv2⟩ :=
        loaded_parts_loop_refines hfs hld hsz parts1 i3 (withStore st ar1) lst1 hrel1 hinv1 a s' h
      rw [ei3] at hx2
      have hz : i.val < (ld'.order.zip ld'.flags).toList.length := by simp; omega
      refine ⟨b :: rs, lst2, ?_, ?_, hrel2, hinv2⟩
      · rw [List.drop_eq_getElem_cons hz, list_mapM_cons]
        have e1 : (ld'.order.zip ld'.flags).toList[i.val] =
            (absNIdx ld.order.val[i.val], (ld'.flags[i.val]'(by omega))) := by
          simp only [Array.toList_zip, List.getElem_zip]
          congr 1
          have := congrArg (·[i.val]?) hld.order
          simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some] at this
          rw [Array.getElem_toList]
          rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by omega)] at this
          exact (Option.some.inj this).symm
        have e2 : absLevel ol = (ld'.flags[i.val]'(by omega)).level := by
          rw [el, Arena.Frontend.Olean.HeaderLoads.levelAt, ei2, Array.getElem?_eq_getElem (by omega)]
          rfl
        rw [e1, partT]
        simp only
        rw [← e2, am_bind_ok hx, am_bind_ok hx2]
        rfl
      · show List.map _ _ = _
        rw [hrs, ConRon.Refine.vec_push_val hparts1, hb]
        simp
  · rw [ite_eq_right hlt] at h
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨[], lst, ?_, by simp, hrel, hinv⟩
    rw [List.drop_of_length_le (by have := lt_of_not_lt_len hlt; simp; omega)]
    rfl
termination_by ld.order.val.length - i.val
decreasing_by
  have := lt_of_lt_len hlt
  omega

/-- **`loaded_parts`' accept is the twin's `mapM`.** -/
theorem loaded_parts_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {ld ld'} (hld : HeaderLoadsRel ld ld') (hsz : ld'.order.size = ld'.flags.size) :
    AS pers (fun o rs => o.val.map absNamePositions = rs) st lst
      (loaded_parts inst fsv pk pers st.store sp ld)
      ((ld'.order.zip ld'.flags).toList.mapM (partT fs (absPins pk) (absRoots sp))) := by
  intro hrel hinv a s' h
  rw [loaded_parts] at h
  obtain ⟨rs, lst1, hx, hrs, hrel1, hinv1⟩ :=
    loaded_parts_loop_refines hfs hld hsz _ 0#usize st lst hrel hinv a s' h
  have e0 : (alloc.vec.Vec.with_capacity frontend.olean.reads.NamePositions (alloc.vec.Vec.len ld.order)).val = [] := rfl
  rw [e0] at hrs
  exact ⟨rs, lst1, by simpa using hx, by simpa using hrs, hrel1, hinv1⟩


/-! ## The worker's reads -/

/-- Every copy of every clash fits a `usize`, as the index makes them. -/
def ClashesFit (wr : frontend.olean.index.WorkerReads) : Prop :=
  ∀ cl ∈ wr.clashes.val, ∀ x ∈ cl.copies.val, CopyFits x.1

/-- **`index::WorkerReads` against the twin's**, with the positions the reach reads back as a
`usize` fitting one: the load positions (`fits`) and the clashes' copies (`clashFits`). -/
structure WorkerReadsRel (w : frontend.olean.index.WorkerReads) (w' : Arena.Frontend.Olean.WorkerReads) :
    Prop where
  own : absNamePositions w.own = w'.own
  loads : HeaderLoadsRel w.loads w'.loads
  pub : AccA w.pub_ w'.pub
  index : NameIndexRel w.index w'.index
  clashes : List.Forall₂ ClashRel w.clashes.val w'.clashes.toList
  fits : IndexFits w'.loads
  clashFits : ClashesFit w

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ {x}, x ∈ l1 → ∃ y ∈ l2, R x y
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons (a := a) (b := b) hab hrest, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self .., hab⟩
    · obtain ⟨y, hy, h⟩ := forall₂_mem_left hrest hx
      exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

/-- **The clashes' copies fit**, as the index's copies do. -/
theorem clashes_fit {cc : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec frontend.olean.index.Copy)}
    (fcc : ∀ p ∈ cc.val, ∀ c ∈ p.2.val, CopyFits c) {I}
    {clashes : alloc.vec.Vec frontend.olean.index.Clash}
    (hcl : List.Forall₂ ClashRel clashes.val (cc.val.map (clashOfT I ∘ absCC))) :
    ∀ cl ∈ clashes.val, ∀ x ∈ cl.copies.val, CopyFits x.1 := by
  intro cl hcl' x hx
  obtain ⟨y, hy, hr⟩ := forall₂_mem_left hcl hcl'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  obtain ⟨z, hz, hxz⟩ := forall₂_mem_left hr.copies hx
  simp only [Function.comp, clashOfT, absCC, Array.toList_filterMap, List.mem_filterMap] at hz
  obtain ⟨c', hc', hz⟩ := hz
  simp only [List.mem_map] at hc'
  obtain ⟨c, hc, rfl⟩ := hc'
  simp only [infoOf, Option.map_eq_some_iff] at hz
  obtain ⟨_, -, rfl⟩ := hz
  have : x.1 = c := absCopy_inj hxz.1
  rw [this]
  exact fcc p hp c hc

/-- **Theorem 2 of the worker's reads**: `worker_reads`' accept is `workerReads`'. -/
theorem worker_reads_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {m : arena.handle.NIdx} {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)} :
    AS pers WorkerReadsRel st lst (worker_reads inst fsv pk pers st.store sp m x)
      (Arena.Frontend.Olean.workerReads fs (absPins pk) (absRoots sp) (absNIdx m) (absImports x)) := by
  intro hrel hinv a s' h
  rw [worker_reads] at h
  -- the own part
  peel h as q1, hq1
  obtain ⟨r1, ar1⟩ := q1
  cases r1 with
  | Err e => cases Result.ok_injective h
  | Ok o =>
  obtain ⟨b0, lst1, hx1, hb0, hrel1, hinv1⟩ :=
    read_part_names_refines (m := m) (level := .Private) hfs hrel hinv o ar1 hq1
  peel h as own, hown
  have eown := name_positions_with_imports_eq hown
  rw [← hb0] at eown
  -- the header fixpoint
  peel h as q2, hq2
  obtain ⟨r2, ar2⟩ := q2
  cases r2 with
  | Err e => cases Result.ok_injective h
  | Ok ld =>
  obtain ⟨ld', lst2, hx2, hld, hrel2, hinv2⟩ :=
    header_fixpoint_refines (st := withStore st ar1) (is_module := own.header.is_module)
      (imports := own.header.imports) (sp_dirs := sp) (pk := pk) hfs hrel1 hinv1 ld ar2 hq2
  obtain ⟨s0, hs0⟩ := headerFixpoint_ofState hx2
  have hsz : ld'.order.size = ld'.flags.size := by rw [hs0]; exact ofState_sizes s0
  have hw : IndexFits ld' := by rw [hs0]; exact ofState_index_fits s0
  -- the loaded parts
  peel h as q3, hq3
  obtain ⟨r3, ar3⟩ := q3
  cases r3 with
  | Err e => cases Result.ok_injective h
  | Ok parts =>
  obtain ⟨rs, lst3, hx3, hrs, hrel3, hinv3⟩ :=
    loaded_parts_refines (st := withStore st ar2) hfs hld hsz hrel2 hinv2 parts ar3 hq3
  peel h as ix, hixq
  have hix := name_index_of_eq hixq
  rw [hrs] at hix
  -- the module system
  peel h as r4, hr4
  cases r4 with
  | Err e => cases Result.ok_injective h
  | Ok u4 =>
  obtain ⟨_, lst4, hx4, -, hrel4, hinv4⟩ :=
    imports_modules_ok_ok (st := withStore st ar3) (lst := lst3) m own.header.is_module hld hw hix
      own.header.imports hrel3 hinv3 u4 hr4
  -- the doubly held names and their statements
  peel h as cc, hcc
  obtain ⟨ecc, fcc⟩ := clash_copies_eq hix hcc
  peel h as v, hv
  have ev := all_copies_eq hv
  have hvfit : ∀ c ∈ v.val, CopyFits c := by
    intro c hc
    rw [ev, List.mem_flatMap] at hc
    obtain ⟨p, hp, hc⟩ := hc
    exact fcc p hp c hc
  peel h as q5, hq5
  obtain ⟨r5, ar4⟩ := q5
  cases r5 with
  | Err e => cases Result.ok_injective h
  | Ok infos =>
  obtain ⟨I, lst5, hx5, hI, hrel5, hinv5⟩ :=
    read_infos_refines (st := withStore st ar3) (lst := lst4) hfs hld hix hvfit hrel4 hinv4 infos ar4 hq5
  peel h as clashes, hclashes
  have hcl := clashes_of_eq hI hclashes
  -- the heads
  peel h as r6, hr6
  cases r6 with
  | Err e => cases Result.ok_injective h
  | Ok heads =>
  have hCL : List.Forall₂ ClashRel clashes.val
      ((Arena.Frontend.Olean.clashCopies (Arena.Frontend.Olean.nameIndexOf rs.toArray)).map
        (clashOfT I)).toList := by
    rw [Array.toList_map, ← ecc, List.map_map]; exact hcl
  obtain ⟨H, lst6, hx6, hH, hrel6, hinv6⟩ :=
    (clash_heads_rel (st := withStore st ar4) (lst := lst5) (pers := pers) hix hCL).ca hrel5 hinv5 heads hr6
  peel h as q7, hq7
  obtain ⟨r7, ar5⟩ := q7
  cases r7 with
  | Err e => cases Result.ok_injective h
  | Ok hinfos =>
  obtain ⟨I2, lst7, hx7, hI2, hrel7, hinv7⟩ :=
    read_infos_refines (st := withStore st ar4) (lst := lst6) hfs hld hix hH.2 hrel6 hinv6 hinfos ar5 hq7
  peel h as ht, hht
  have hTy := head_tys_rel (head_tys_of_eq hix hI2 hH.2 hht)
  -- the clash rule and freshness
  peel h as r8, hr8
  cases r8 with
  | Err e => cases Result.ok_injective h
  | Ok u8 =>
  obtain ⟨_, lst8, hx8, -, hrel8, hinv8⟩ :=
    clashes_ok_ok (st := withStore st ar5) (lst := lst7) (ld := ld) (ld' := ld') pk hTy hCL hrel7 hinv7 u8 hr8
  peel h as r9, hr9
  cases r9 with
  | Err e => cases Result.ok_injective h
  | Ok u9 =>
  obtain ⟨_, lst9, hx9, -, hrel9, hinv9⟩ :=
    fresh_ok_ok (st := withStore st ar5) (lst := lst8) (ld := ld) pk m ld' hix own hrel8 hinv8 u9 hr9
  peel h as pub, hpub
  have hP := pub_closures_eq hld hw hpub
  have e := Result.ok_injective h
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  refine ⟨⟨absNamePositions own, ld', Arena.Frontend.Olean.pubClosures ld',
      Arena.Frontend.Olean.nameIndexOf rs.toArray,
      (Arena.Frontend.Olean.clashCopies (Arena.Frontend.Olean.nameIndexOf rs.toArray)).map
        (clashOfT I)⟩, lst9, ?_, ⟨rfl, hld, hP, hix, hCL, hw, clashes_fit fcc hcl⟩, hrel9, hinv9⟩
  unfold Arena.Frontend.Olean.workerReads
  refine (am_bind_ok hx1).trans ?_
  rw [← eown]
  refine (am_bind_ok hx2).trans ?_
  refine (am_bind_ok hx3).trans ?_
  refine (am_bind_ok hx4).trans ?_
  have ev' : (v.val.map absCopy).toArray =
      (Arena.Frontend.Olean.clashCopies (Arena.Frontend.Olean.nameIndexOf rs.toArray)).flatMap (·.2) := by
    apply Array.ext'
    rw [Array.toList_flatMap, ← ecc, ev]
    simp [List.map_flatMap, List.flatMap_map]
  rw [ev'] at hx5
  refine (am_bind_ok hx5).trans ?_
  refine (am_bind_ok hx6).trans ?_
  have eH : (heads.val.map absCopy).toArray = H := by
    apply Array.ext'; simpa using hH.1
  rw [eH] at hx7 hx8
  refine (am_bind_ok hx7).trans ?_
  refine (am_bind_ok hx8).trans ?_
  refine (am_bind_ok hx9).trans ?_
  rfl

end reads

end ConRon.Refine2.Frontend.Olean
