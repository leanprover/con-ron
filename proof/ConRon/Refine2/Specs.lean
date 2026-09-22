/-
# `ConRon.Refine2.Specs` — the inversion layer, keyed on the Rust equation

**Deliverable 1 of task #97 P5, part 5.**  Task #97s round 3's per-crate
budget: *"an inversion layer keyed on the Rust equation — here 92 code lines
for nine primitives, i.e. ≈ 10 lines per primitive, each a mechanical
restatement of an existential the abstraction tier proves anyway"*.  This is
that layer for the arena, over the real `EStore` rather than the spike's
`MiniAbs`.

Every lemma has the SAME shape and it is the shape `grind` can use
(`AUTOMATION.md`'s three keying rules, `Refine/README.md`):

* the **Rust equation comes first** — `arena.monad.view_app pers st h = ok o`
  — because `@[grind →]` takes its E-matching pattern from the hypotheses in
  order, and the Rust call is what the normaliser has just produced;
* the conclusion is an **equation or a named relation**, never an
  existential;
* there is **one lemma per primitive**, not per call site.

## The three floors

    arena::store::Tbl.{node, der_at, find}        ← `TblRel` / `TblInv`
    arena::store::{NTables,LTables,LsTables,ETables}.*  ← the tier relations
    arena::store::{NStore,LStore,LsStore,EStore}.*      ← `StoreRel`, the tier select
    arena::monad::*                               ← `SimR` / `Sim` in `AM`

The bottom floor is where the representation lives (a `Vec` of pairs against
two `Array`s, a `ron::HashMap2` against a `Std.HashMap`); the two above it are
`if` chains that match the twin's clause for clause, which is what task
#97-P4a's "Rust-shaped Lean" bought.
-/
import ConRon.Refine2.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn toFun)

/-! ## Floor 0: the `Vec` read, and the handle's index

`Refine/HashMap.lean`'s `vec_index_eq` needs `[Inhabited α]`, which a
generated node-record type does not have; this is the same inversion at
`getElem?`, which needs none. -/

theorem vec_index_some {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    simp only [Result.ok.injEq] at h
    rw [h]

/-- A handle's index, as the twin's `idxNat`.  **Unconditional**, and that is
worth a line: `Refine/Scalars.lean`'s side condition does not arise here
because the cast is a `u32 → usize` widening (`U32.cast_Usize_val_eq`) and not
the `u64 → usize` narrowing the `Expr`-tree tier had to guard. -/
theorem word_idx_nat_val {w : Std.U32} {r : Std.Usize}
    (h : arena.handle.word_idx_nat w = ok r) : r.val = w.val % 134217728 := by
  rw [arena.handle.word_idx_nat] at h
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  have hyv : y.val = w.val % 134217728 :=
    ConRon.Refine.Nat.urem_val
      (by rw [arena.handle.word_index, arena.handle.IDX_CAP] at hy; exact hy)
  rw [← h, Std.U32.cast_Usize_val_eq, hyv]

theorem eidx_idxNat {i : arena.handle.EIdx} {r : Std.Usize}
    (h : arena.handle.EIdx.idx_nat i = ok r) : (absEIdx i).idxNat = r.val := by
  rw [arena.handle.EIdx.idx_nat] at h
  rw [word_idx_nat_val h]
  show ((absEIdx i).index).toNat = _
  simp [Idx.index, absEIdx, absU32]

theorem nidx_idxNat {i : arena.handle.NIdx} {r : Std.Usize}
    (h : arena.handle.NIdx.idx_nat i = ok r) : (absNIdx i).idxNat = r.val := by
  rw [arena.handle.NIdx.idx_nat] at h
  rw [word_idx_nat_val h]
  show ((absNIdx i).index).toNat = _
  simp [Idx.index, absNIdx, absU32]

theorem lidx_idxNat {i : arena.handle.LIdx} {r : Std.Usize}
    (h : arena.handle.LIdx.idx_nat i = ok r) : (absLIdx i).idxNat = r.val := by
  rw [arena.handle.LIdx.idx_nat] at h
  rw [word_idx_nat_val h]
  show ((absLIdx i).index).toNat = _
  simp [Idx.index, absLIdx, absU32]

theorem lsidx_idxNat {i : arena.handle.LsIdx} {r : Std.Usize}
    (h : arena.handle.LsIdx.idx_nat i = ok r) : (absLsIdx i).idxNat = r.val := by
  rw [arena.handle.LsIdx.idx_nat] at h
  rw [word_idx_nat_val h]
  show ((absLsIdx i).index).toNat = _
  simp [Idx.index, absLsIdx, absU32]

theorem bmidx_idxNat {i : arena.handle.BMIdx} {r : Std.Usize}
    (h : arena.handle.BMIdx.idx_nat i = ok r) : (absBMIdx i).idxNat = r.val := by
  rw [arena.handle.BMIdx.idx_nat] at h
  rw [word_idx_nat_val h]
  show ((absBMIdx i).index).toNat = _
  simp [Idx.index, absBMIdx, absU32]

/-! ## Floor 1: one table

`Tbl.node` and `Tbl.der_at` read the interleaved `Vec` of pairs; the twin
reads its two `Array`s.  `Tbl.find` is the cons probe, which is
`Refine/HashMap2.lean`'s `get_refines_wf` under `TblInv`'s two clauses. -/

section Tbl

variable {A I D α ι δ ω : Type} [DecidableEq A] [BEq α] [Hashable α]
  {P : A → Prop} {absA : A → α} {absI : I → ι} {absD : D → δ} {obsD : δ → ω}
  {rt : arena.store.Tbl A I D} {lt : Tbl α ι δ}
  {hH : ron.hashmap.Hashable A} {hE : ron.hashmap.Eq2 A}
  {hDA : ron.hashmap.Dup A} {hDI : ron.hashmap.Dup I} {hDD : ron.hashmap.Dup D}
  {hDf : arena.store.DerDefault D}

/-- The node column, one element. -/
theorem tbl_node_abs (hrel : TblRel P absA absI absD obsD rt lt) {n : Std.Usize}
    {o : Option A}
    (h : arena.store.Tbl.node hH hE hDA hDI hDD hDf rt n = ok o) :
    lt.node? n.val = o.map absA := by
  rw [arena.store.Tbl.node] at h
  have hnodes : lt.node? n.val = (rt.rows.val[n.val]?).map (fun p => absA p.1) := by
    show lt.nodes[n.val]? = _
    rw [← Array.getElem?_toList, hrel.nodes, List.getElem?_map]
  split at h
  · rename_i hge
    simp only [Result.ok.injEq] at h
    subst h
    rw [hnodes, List.getElem?_eq_none (by scalar_tac)]
    rfl
  · rename_i hlt
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨a, d⟩ := p
    have h2 : some a = o := Result.ok_injective h
    rw [hnodes, vec_index_some hp, ← h2]
    rfl

/-- The derived column, one element.  Out of range the Rust answers
`D::der_default()` and the twin `default`, which is the hypothesis `hdf`:
`u64`'s is `0` and `LDer`'s is `⟨0, false⟩`, and `deriving Inhabited` gives
the twin the same two. -/
theorem tbl_der_at_abs [Inhabited δ] (hrel : TblRel P absA absI absD obsD rt lt)
    (hdup : DupId hDD)
    (hdf : ∀ d, hDf.der_default = ok d → absD d = default)
    {n : Std.Usize} {d : D}
    (h : arena.store.Tbl.der_at hH hE hDA hDI hDD hDf rt n = ok d) :
    obsD (lt.derAt n.val) = obsD (absD d) := by
  rw [arena.store.Tbl.der_at] at h
  have hder : (lt.der[n.val]?).map obsD
      = (rt.rows.val[n.val]?).map (fun p => obsD (absD p.2)) := by
    rw [← Array.getElem?_toList, ← List.getElem?_map, hrel.der, List.getElem?_map]
  show obsD (lt.der.getD n.val default) = obsD (absD d)
  rw [Array.getD_eq_getD_getElem?]
  split at h
  · rename_i hge
    rw [List.getElem?_eq_none (by scalar_tac)] at hder
    have hl : lt.der[n.val]? = none := by
      cases hc : lt.der[n.val]? with
      | none => rfl
      | some x => rw [hc] at hder; simp at hder
    rw [hl, hdf d h]
    rfl
  · rename_i hlt
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨a, d0⟩ := p
    rw [vec_index_some hp] at hder
    rw [hdup d0 d h]
    cases hc : lt.der[n.val]? with
    | none => rw [hc] at hder; simp at hder
    | some x =>
      rw [hc] at hder
      simp only [Option.map_some, Option.some.injEq] at hder
      simpa using hder

/-- The cons probe. -/
theorem tbl_find_abs (hrel : TblRel P absA absI absD obsD rt lt)
    (hinv : TblInv hH P rt) (heq : Eq2Fwd hE P) (hdup : DupId hDI)
    {a : A} (hk : P a) {o : Option I}
    (h : arena.store.Tbl.find hH hE hDA hDI hDD hDf rt a = ok o) :
    lt.find? (absA a) = o.map absI := by
  rw [arena.store.Tbl.find] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hto := ConRon.Refine.HashMap2.get_refines_wf heq hinv.inv hinv.keys hk hr
  have hrelk := hrel.cons a hk
  show lt.cons[absA a]? = o.map absI
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at h
    have h2 : (none : Option I) = o := Result.ok_injective h
    rw [← h2]
  | some i =>
    rw [hrc] at h
    obtain ⟨i', hi', h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some i' = o := Result.ok_injective h
    rw [← h2, hdup i i' hi']

end Tbl

/-! ## The handle the push builds -/

/-- `arena::handle::word_mk` against `Idx.mk`'s word. -/
theorem word_mk_abs {tag tier idx w : Std.U32}
    (h : arena.handle.word_mk tag tier idx = ok w) :
    absU32 tag * 268435456 + absU32 tier * 134217728 + absU32 idx = absU32 w := by
  rw [arena.handle.word_mk, arena.handle.TAG_SPAN, arena.handle.IDX_CAP] at h
  obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e0 := absU32_mul hi
  have e1 := absU32_mul hi1
  have e2 := absU32_add hi2
  have e3 := absU32_add h
  have c0 : absU32 (268435456#u32 : Std.U32) = 268435456 := rfl
  have c1 : absU32 (134217728#u32 : Std.U32) = 134217728 := rfl
  rw [← e3, ← e2, ← e0, ← e1, c0, c1]

theorem eidx_pack_abs {tag tier idx : Std.U32} {h : arena.handle.EIdx}
    (hp : arena.handle.EIdx.pack tag tier idx = ok h) :
    absEIdx h = Idx.mk (absU32 tag) (absU32 tier) (absU32 idx) := by
  rw [arena.handle.EIdx.pack] at hp
  obtain ⟨w, hw, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
  have h2 : arena.handle.EIdx.mk w = h := Result.ok_injective hp
  subst h2
  rw [Idx.mk, absEIdx, ← word_mk_abs hw]

theorem nidx_pack_abs {tag tier idx : Std.U32} {h : arena.handle.NIdx}
    (hp : arena.handle.NIdx.pack tag tier idx = ok h) :
    absNIdx h = Idx.mk (absU32 tag) (absU32 tier) (absU32 idx) := by
  rw [arena.handle.NIdx.pack] at hp
  obtain ⟨w, hw, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
  have h2 : arena.handle.NIdx.mk w = h := Result.ok_injective hp
  subst h2
  rw [Idx.mk, absNIdx, ← word_mk_abs hw]

theorem lidx_pack_abs {tag tier idx : Std.U32} {h : arena.handle.LIdx}
    (hp : arena.handle.LIdx.pack tag tier idx = ok h) :
    absLIdx h = Idx.mk (absU32 tag) (absU32 tier) (absU32 idx) := by
  rw [arena.handle.LIdx.pack] at hp
  obtain ⟨w, hw, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
  have h2 : arena.handle.LIdx.mk w = h := Result.ok_injective hp
  subst h2
  rw [Idx.mk, absLIdx, ← word_mk_abs hw]

theorem lsidx_pack_abs {tag tier idx : Std.U32} {h : arena.handle.LsIdx}
    (hp : arena.handle.LsIdx.pack tag tier idx = ok h) :
    absLsIdx h = Idx.mk (absU32 tag) (absU32 tier) (absU32 idx) := by
  rw [arena.handle.LsIdx.pack] at hp
  obtain ⟨w, hw, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
  have h2 : arena.handle.LsIdx.mk w = h := Result.ok_injective hp
  subst h2
  rw [Idx.mk, absLsIdx, ← word_mk_abs hw]

/-- The datum store has ONE constructor, so `BMIdx::pack` takes no tag and the
twin writes `Idx.mk 0 tier _` (task #97-P6-16). -/
theorem bmidx_pack_abs {tier idx : Std.U32} {h : arena.handle.BMIdx}
    (hp : arena.handle.BMIdx.pack tier idx = ok h) :
    absBMIdx h = Idx.mk 0 (absU32 tier) (absU32 idx) := by
  rw [arena.handle.BMIdx.pack] at hp
  obtain ⟨w, hw, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
  have h2 : arena.handle.BMIdx.mk w = h := Result.ok_injective hp
  subst h2
  have hz : absU32 (0#u32 : Std.U32) = 0 := rfl
  rw [Idx.mk, absBMIdx, ← word_mk_abs hw, hz]

/-- The `as u32` on the array length, against the twin's `UInt32.ofNat size`:
**unconditional**, and `Refine2/AbsStore.lean`'s note on the capacity
invariant is why — `UScalar.cast .U32` truncates by `2 ^ 32` and
`UInt32.ofNat` by the same modulus. -/
theorem cast_u32_size {i : Std.Usize} {r : Std.U32}
    (h : lift (UScalar.cast .U32 i) = ok r) : absU32 r = UInt32.ofNat i.val := by
  simp only [lift, Result.ok.injEq] at h
  subst h
  apply UInt32.toNat_inj.mp
  rw [absU32_toNat, UScalar.cast_val_eq]
  simp

/-! ### The derived word's three OBSERVABLE fields, read off the port's word

`Refine/Expr.lean`'s `pack_bits` already says what the port's `pack_data`
packed, on `.val`; con-leche's `bvarOfData_pack` / `fvarOfData_pack` /
`lpOfData_pack` say the same of the twin's `packData`.  The lemma below is the
bridge between the two spellings — `derObsE` of an abstracted port word IS the
three `Nat` fields — and with it every `der_of_*` arm is those two roundtrips
plus the arm's own bound on the two ranges.  **The hash never appears**, which
is the point of `derObsE` (`Refine2/AbsStore.lean`'s note). -/

/-- `derObsE` read off a `Std.U64` through `absU64`: the three fields are the
`Nat` fields of the word. -/
theorem derObsE_absU64 (w : Std.U64) :
    derObsE (absU64 w)
      = (UInt64.ofNat (w.val / 65536 % 32768), UInt64.ofNat (w.val / 2 % 32768),
          decide (w.val % 2 = 1)) := by
  rw [derObsE]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show ConLeche.bvarOfData (absU64 w) = _
    rw [ConLeche.bvarOfData]
    have hb : w.val / 65536 % 32768 < 2 ^ 64 := by have := u64_val_lt w; omega
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' hb, UInt64.toNat_mod, UInt64.toNat_div,
      absU64_toNat]
    rfl
  · show ConLeche.fvarOfData (absU64 w) = _
    rw [ConLeche.fvarOfData]
    have hb : w.val / 2 % 32768 < 2 ^ 64 := by have := u64_val_lt w; omega
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' hb, UInt64.toNat_mod, UInt64.toNat_div,
      absU64_toNat]
    rfl
  · show ConLeche.lpOfData (absU64 w) = _
    rw [ConLeche.lpOfData]
    have : (absU64 w % 2).toNat = w.val % 2 := by
      rw [UInt64.toNat_mod, absU64_toNat]; rfl
    by_cases hc : w.val % 2 = 1
    · simp only [hc, decide_true]
      have h2 : (absU64 w % 2) = 1 := by
        apply UInt64.toNat_inj.mp; rw [this, hc]; rfl
      simp [h2]
    · simp only [hc, decide_false]
      have h2 : (absU64 w % 2) ≠ 1 := by
        intro hcc
        exact hc (by rw [← this, hcc]; rfl)
      simp [h2]

/-! ## Floor 1b: the three WRITING operations of one table

What `intern` does below the tier select, and the piece task #97-P5-0's
"what the 62 open ones wait on is now ONE piece of plumbing" named.  Three
lemmas over the generic `Tbl`, and the eighteen arrays instantiate them. -/

section Tbl

variable {A I D α ι δ ω : Type} [DecidableEq A] [BEq α] [Hashable α]
  [LawfulBEq α] [LawfulHashable α]
  {P : A → Prop} {absA : A → α} {absI : I → ι} {absD : D → δ} {obsD : δ → ω}
  {rt : arena.store.Tbl A I D} {lt : Tbl α ι δ}
  {hH : ron.hashmap.Hashable A} {hE : ron.hashmap.Eq2 A}
  {hDA : ron.hashmap.Dup A} {hDI : ron.hashmap.Dup I} {hDD : ron.hashmap.Dup D}
  {hDf : arena.store.DerDefault D}

omit [LawfulBEq α] [LawfulHashable α] in
/-- How long the constructor's array is — the index the pushed handle gets. -/
theorem tbl_size_abs (hrel : TblRel P absA absI absD obsD rt lt) {n : Std.Usize}
    (h : arena.store.Tbl.size hH hE hDA hDI hDD hDf rt = ok n) : n.val = lt.size := by
  rw [arena.store.Tbl.size, Result.ok.injEq] at h
  subst h
  show rt.rows.val.length = lt.nodes.size
  rw [← Array.length_toList, hrel.nodes, List.length_map]

/-- **`Tbl::push`**: the cons insert, then the two columns.  The twin's
`Tbl.push` is one `match` that appends to both arrays and inserts; the port's
is `dup2`, `HashMap2::insert`, `Vec::push` of the PAIR (task #97-P6-10's
interleaved column), which is why the two `map`s of `TblRel` split it. -/
theorem tbl_push_abs (hrel : TblRel P absA absI absD obsD rt lt)
    (hinv : TblInv hH P rt) (heq : Eq2Fwd hE P) (hdupA : DupId hDA)
    (hinjA : ∀ a b, P a → P b → absA a = absA b → a = b)
    {a : A} (hk : P a) {d : D} {dl : δ} (hdl : obsD dl = obsD (absD d)) {i : I} {rt'}
    (h : arena.store.Tbl.push hH hE hDA hDI hDD hDf rt a d i = ok rt') :
    TblRel P absA absI absD obsD rt' (lt.push (absA a) dl (absI i)) ∧
      TblInv hH P rt' := by
  rw [arena.store.Tbl.push] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [hdupA a t ht] at h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨old, hm⟩ := p
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hrt : arena.store.Tbl.mk v hm = rt' := Result.ok_injective h
  subst hrt
  obtain ⟨hcons, hkeys⟩ :=
    ConRon.Refine.HashMap2.Rel_insert_wf heq hinjA hinv.inv hinv.keys hrel.cons hk hp
  have hinv' := (ConRon.Refine.HashMap2.insert_refines_wf heq hinv.inv hinv.keys hk hp).1
  have hvv := ConRon.Refine.vec_push_val hv
  refine ⟨⟨?_, ?_, hcons⟩, ⟨hinv', hkeys⟩⟩
  · show (lt.nodes.push (absA a)).toList = _
    rw [Array.toList_push, hrel.nodes, hvv, List.map_append]
    rfl
  · show ((lt.der.push dl).toList).map obsD = _
    rw [Array.toList_push, List.map_append, hrel.der, hvv, List.map_append]
    simp only [List.map_cons, List.map_nil, hdl]

/-- **`Tbl::find_slot`** (task #97-survey's N2, the fused find-or-insert): the
probe that answers what `Tbl::find` answers *and* hands back the slot, plus —
its last component — the identification that `find_slot` then `push_at` is
`push`.  `find_slot` mutates the table (`ensure_slots` may allocate), which is
why the relation has to be re-established for `rt1`; `toFun` is unchanged, so
it is the same relation. -/
theorem tbl_find_slot_abs (hrel : TblRel P absA absI absD obsD rt lt)
    (hinv : TblInv hH P rt) (heq : Eq2Fwd hE P) (hdupA : DupId hDA)
    (hdupI : DupId hDI) (hinjA : ∀ a b, P a → P b → absA a = absA b → a = b)
    {a : A} (hk : P a) {at1 : Std.Usize} {o : Option I} {rt1}
    (h : arena.store.Tbl.find_slot hH hE hDA hDI hDD hDf rt a = ok ((at1, o), rt1)) :
    TblRel P absA absI absD obsD rt1 lt ∧ TblInv hH P rt1 ∧
      lt.find? (absA a) = o.map absI ∧
      (o = none → ∀ (d : D) (dl : δ), obsD dl = obsD (absD d) → ∀ (i : I) rt2,
        arena.store.Tbl.push_at hH hE hDA hDI hDD hDf rt1 at1 a d i = ok rt2 →
        TblRel P absA absI absD obsD rt2 (lt.push (absA a) dl (absI i)) ∧
          TblInv hH P rt2) := by
  rw [arena.store.Tbl.find_slot] at h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨pr, hmq⟩ := q
  have he := Result.ok_injective h
  have hat : pr = (at1, o) := congrArg Prod.fst he
  have hrt1 : rt1 = { rt with cons := hmq } := (congrArg Prod.snd he).symm
  subst hrt1
  subst hat
  obtain ⟨hinv1, hkeys1, htf1, -, hoval, hid⟩ :=
    ConRon.Refine.HashMap2.find_slot_spec hdupI heq hinv.inv hinv.keys hk hq
  have hcons1 : RelOn P hmq lt.cons absA absI := by
    intro k hkk; rw [htf1]; exact hrel.cons k hkk
  refine ⟨⟨hrel.nodes, hrel.der, hcons1⟩, ⟨hinv1, hkeys1⟩, ?_, ?_⟩
  · show lt.cons[absA a]? = o.map absI
    rw [← hrel.cons a hk, ← hoval]
  · intro hnone d dl hdl i rt2 h2
    rw [arena.store.Tbl.push_at] at h2
    obtain ⟨t, ht, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
    rw [hdupA a t ht] at h2
    obtain ⟨hm2, hins, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
    obtain ⟨v, hv, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
    have hrt2 : arena.store.Tbl.mk v hm2 = rt2 := Result.ok_injective h2
    subst hrt2
    have hfull := hid hnone i hm2 hins
    obtain ⟨hcons2, hkeys2⟩ :=
      ConRon.Refine.HashMap2.Rel_insert_wf heq hinjA hinv.inv hinv.keys hrel.cons hk hfull
    have hinv2 :=
      (ConRon.Refine.HashMap2.insert_refines_wf heq hinv.inv hinv.keys hk hfull).1
    have hvv := ConRon.Refine.vec_push_val hv
    refine ⟨⟨?_, ?_, hcons2⟩, ⟨hinv2, hkeys2⟩⟩
    · show (lt.nodes.push (absA a)).toList = _
      rw [Array.toList_push, hrel.nodes, hvv, List.map_append]
      rfl
    · show ((lt.der.push dl).toList).map obsD = _
      rw [Array.toList_push, List.map_append, hrel.der, hvv, List.map_append]
      simp only [List.map_cons, List.map_nil, hdl]

end Tbl

/-! ## Floor 2: the expression tier's projections

Eleven readers of `ETables`, each `Tbl.node` at one array plus the handle's
own index; `getBind` dispatches on the tag first, exactly as the twin's does.
The `dup2`s the Rust writes on the way out are the identity
(`Refine2/Inv.lean`'s five `dupId_*`), so each is one `rw` after the node
read. -/

/-- A `(EIdx × EIdx)` pair, abstracted. -/
def absPairE (p : arena.handle.EIdx × arena.handle.EIdx) : EIdx × EIdx :=
  (absEIdx p.1, absEIdx p.2)
/-- A `const` node's two fields. -/
def absConstT (p : arena.handle.NIdx × arena.handle.LsIdx) : NIdx × LsIdx :=
  (absNIdx p.1, absLsIdx p.2)
/-- A binder's three fields, the datum as a HANDLE. -/
def absBindI (p : arena.handle.EIdx × arena.handle.EIdx × arena.handle.BMIdx) :
    EIdx × EIdx × BMIdx :=
  (absEIdx p.1, absEIdx p.2.1, absBMIdx p.2.2)
/-- A binder's three fields, the datum DECODED. -/
def absBindM (p : arena.handle.EIdx × arena.handle.EIdx × kernel.expr.BinderMeta) :
    EIdx × EIdx × ConLeche.BinderMeta :=
  (absEIdx p.1, absEIdx p.2.1, ConRon.Refine.absBinderMeta p.2.2)
/-- A `letE` node's three fields. -/
def absLetT (p : arena.handle.EIdx × arena.handle.EIdx × arena.handle.EIdx) :
    EIdx × EIdx × EIdx :=
  (absEIdx p.1, absEIdx p.2.1, absEIdx p.2.2)
/-- A `proj` node's three fields. -/
def absProjT (p : arena.handle.NIdx × Std.U64 × arena.handle.EIdx) :
    NIdx × Nat × EIdx :=
  (absNIdx p.1, absU p.2.1, absEIdx p.2.2)

attribute [simp] absPairE absConstT absBindI absBindM absLetT absProjT

theorem etables_get_app_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o}
    (h : arena.store.ETables.get_app rt i = ok o) :
    lt.getApp (absEIdx i) = o.map absPairE := by
  rw [arena.store.ETables.get_app] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.apps hp
  rw [ETables.getApp, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option (arena.handle.EIdx × arena.handle.EIdx)) = o :=
      Result.ok_injective h
    rw [← h2]; rfl
  | some r =>
    rw [hpc] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some (x, y) = o := Result.ok_injective h
    rw [← h2, dupId_eidx _ _ hx, dupId_eidx _ _ hy]
    rfl

theorem etables_get_sort_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o : Option arena.handle.LIdx}
    (h : arena.store.ETables.get_sort rt i = ok o) :
    lt.getSort (absEIdx i) = o.map absLIdx := by
  rw [arena.store.ETables.get_sort] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.sorts hp
  rw [ETables.getSort, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option arena.handle.LIdx) = o := Result.ok_injective h
    subst h2
    rfl
  | some r =>
    rw [hpc] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some x = o := Result.ok_injective h
    subst h2
    rw [dupId_lidx _ _ hx]
    rfl

theorem etables_get_const_name_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o : Option arena.handle.NIdx}
    (h : arena.store.ETables.get_const_name rt i = ok o) :
    lt.getConstName (absEIdx i) = o.map absNIdx := by
  rw [arena.store.ETables.get_const_name] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.consts hp
  rw [ETables.getConstName, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option arena.handle.NIdx) = o := Result.ok_injective h
    subst h2
    rfl
  | some r =>
    rw [hpc] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some x = o := Result.ok_injective h
    subst h2
    rw [dupId_nidx _ _ hx]
    rfl

theorem etables_get_fvar_ty_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o : Option arena.handle.EIdx}
    (h : arena.store.ETables.get_fvar_ty rt i = ok o) :
    lt.getFVarTy (absEIdx i) = o.map absEIdx := by
  rw [arena.store.ETables.get_fvar_ty] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.fvars hp
  rw [ETables.getFVarTy, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective h
    subst h2
    rfl
  | some r =>
    rw [hpc] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some x = o := Result.ok_injective h
    subst h2
    rw [dupId_eidx _ _ hx]
    rfl

theorem etables_get_bvar_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o : Option Std.U64}
    (h : arena.store.ETables.get_bvar rt i = ok o) :
    lt.getBVar (absEIdx i) = o.map absU := by
  rw [arena.store.ETables.get_bvar] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.bvars hp
  rw [ETables.getBVar, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option Std.U64) = o := Result.ok_injective h
    subst h2
    rfl
  | some r =>
    rw [hpc] at h
    have h2 : some r.i = o := Result.ok_injective h
    subst h2
    rfl

theorem etables_get_fvar_idx_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o : Option Std.U64}
    (h : arena.store.ETables.get_fvar_idx rt i = ok o) :
    lt.getFVarIdx (absEIdx i) = o.map absU := by
  rw [arena.store.ETables.get_fvar_idx] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.fvars hp
  rw [ETables.getFVarIdx, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option Std.U64) = o := Result.ok_injective h
    subst h2
    rfl
  | some r =>
    rw [hpc] at h
    have h2 : some r.idx = o := Result.ok_injective h
    subst h2
    rfl

theorem etables_get_const_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o}
    (h : arena.store.ETables.get_const rt i = ok o) :
    lt.getConst (absEIdx i) = o.map absConstT := by
  rw [arena.store.ETables.get_const] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.consts hp
  rw [ETables.getConst, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option (arena.handle.NIdx × arena.handle.LsIdx)) = o :=
      Result.ok_injective h
    subst h2
    rfl
  | some r =>
    rw [hpc] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some (x, y) = o := Result.ok_injective h
    subst h2
    rw [dupId_nidx _ _ hx, dupId_lsidx _ _ hy]
    rfl

theorem etables_get_let_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o}
    (h : arena.store.ETables.get_let rt i = ok o) :
    lt.getLet (absEIdx i) = o.map absLetT := by
  rw [arena.store.ETables.get_let] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.lets hp
  rw [ETables.getLet, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option (arena.handle.EIdx × arena.handle.EIdx ×
      arena.handle.EIdx)) = o := Result.ok_injective h
    subst h2
    rfl
  | some r =>
    rw [hpc] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨z, hz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some (x, y, z) = o := Result.ok_injective h
    subst h2
    rw [dupId_eidx _ _ hx, dupId_eidx _ _ hy, dupId_eidx _ _ hz]
    rfl

theorem etables_get_proj_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o}
    (h : arena.store.ETables.get_proj rt i = ok o) :
    lt.getProj (absEIdx i) = o.map absProjT := by
  rw [arena.store.ETables.get_proj] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.projs hp
  rw [ETables.getProj, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option (arena.handle.NIdx × Std.U64 ×
      arena.handle.EIdx)) = o := Result.ok_injective h
    subst h2
    rfl
  | some r =>
    rw [hpc] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some (x, r.i, y) = o := Result.ok_injective h
    subst h2
    rw [dupId_nidx _ _ hx, dupId_eidx _ _ hy]
    rfl

/-! ## Floor 3: the tier select

`EStore.view_X` is the handle's tier bit, then `pers_get_X`'s `shared_on`
select, then the tier's own projection.  The twin has the first and the third
and NOT the second — task #97-LC §1's ruling — so the middle one is exactly
where `Refine2/AbsStore.lean`'s `rPersE` stands, and each of these ten proofs
says so in one `simp only [rPersE, hs]`. -/

theorem estore_view_app_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o : Option (arena.handle.EIdx × arena.handle.EIdx)}
    (h : arena.store.EStore.view_app rs pers i = ok o) :
    ls.viewApp (absEIdx i) = o.map absPairE := by
  rw [arena.store.EStore.view_app] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewApp]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetApp]
    rw [arena.store.EStore.pers_get_app] at h
    have h3 : arena.store.ETables.get_app (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_app_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_app_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option (arena.handle.EIdx × arena.handle.EIdx)) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_sort_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o : Option arena.handle.LIdx}
    (h : arena.store.EStore.view_sort rs pers i = ok o) :
    ls.viewSort (absEIdx i) = o.map absLIdx := by
  rw [arena.store.EStore.view_sort] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewSort]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetSort]
    rw [arena.store.EStore.pers_get_sort] at h
    have h3 : arena.store.ETables.get_sort (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_sort_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_sort_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option arena.handle.LIdx) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_const_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o : Option (arena.handle.NIdx × arena.handle.LsIdx)}
    (h : arena.store.EStore.view_const rs pers i = ok o) :
    ls.viewConst (absEIdx i) = o.map absConstT := by
  rw [arena.store.EStore.view_const] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewConst]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetConst]
    rw [arena.store.EStore.pers_get_const] at h
    have h3 : arena.store.ETables.get_const (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_const_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_const_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option (arena.handle.NIdx × arena.handle.LsIdx)) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_const_name_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o : Option arena.handle.NIdx}
    (h : arena.store.EStore.view_const_name rs pers i = ok o) :
    ls.viewConstName (absEIdx i) = o.map absNIdx := by
  rw [arena.store.EStore.view_const_name] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewConstName]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetConstName]
    rw [arena.store.EStore.pers_get_const_name] at h
    have h3 : arena.store.ETables.get_const_name (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_const_name_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_const_name_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option arena.handle.NIdx) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_bvar_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o : Option Std.U64}
    (h : arena.store.EStore.view_bvar rs pers i = ok o) :
    ls.viewBVar (absEIdx i) = o.map absU := by
  rw [arena.store.EStore.view_bvar] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewBVar]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetBVar]
    rw [arena.store.EStore.pers_get_bvar] at h
    have h3 : arena.store.ETables.get_bvar (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_bvar_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_bvar_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option Std.U64) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_fvar_idx_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o : Option Std.U64}
    (h : arena.store.EStore.view_fvar_idx rs pers i = ok o) :
    ls.viewFVarIdx (absEIdx i) = o.map absU := by
  rw [arena.store.EStore.view_fvar_idx] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewFVarIdx]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetFVarIdx]
    rw [arena.store.EStore.pers_get_fvar_idx] at h
    have h3 : arena.store.ETables.get_fvar_idx (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_fvar_idx_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_fvar_idx_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option Std.U64) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_fvar_ty_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o : Option arena.handle.EIdx}
    (h : arena.store.EStore.view_fvar_ty rs pers i = ok o) :
    ls.viewFVarTy (absEIdx i) = o.map absEIdx := by
  rw [arena.store.EStore.view_fvar_ty] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewFVarTy]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetFVarTy]
    rw [arena.store.EStore.pers_get_fvar_ty] at h
    have h3 : arena.store.ETables.get_fvar_ty (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_fvar_ty_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_fvar_ty_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_let_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o : Option (arena.handle.EIdx × arena.handle.EIdx × arena.handle.EIdx)}
    (h : arena.store.EStore.view_let rs pers i = ok o) :
    ls.viewLet (absEIdx i) = o.map absLetT := by
  rw [arena.store.EStore.view_let] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewLet]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetLet]
    rw [arena.store.EStore.pers_get_let] at h
    have h3 : arena.store.ETables.get_let (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_let_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_let_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option (arena.handle.EIdx × arena.handle.EIdx × arena.handle.EIdx)) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_proj_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o : Option (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)}
    (h : arena.store.EStore.view_proj rs pers i = ok o) :
    ls.viewProj (absEIdx i) = o.map absProjT := by
  rw [arena.store.EStore.view_proj] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewProj]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetProj]
    rw [arena.store.EStore.pers_get_proj] at h
    have h3 : arena.store.ETables.get_proj (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_proj_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_proj_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)) = o := Result.ok_injective h
      subst h2
      rfl

/-! ## Floor 4: `arena::monad`, in `AM`

The monad wrappers are `EStore`'s readers under a state read, and the twin's
are the same under `get`, so each is the floor-3 lemma plus one `rfl`-level
step for the `StateT` plumbing.  `SimR` (`Refine2/Shape.lean`) is the shape:
*the twin answers the abstracted value and leaves the state alone*. -/

/-- The `StateT` plumbing, once: a twin reader is `get` then `pure`. -/
theorem run_get_pure {β : Type} (f : AState → β) (lst : AState) :
    ((do let s ← get; pure (f s) : AM β)).run lst = .ok (f lst, lst) := rfl

/-- `arena::monad::view_app` against `Arena.viewApp`. -/
@[grind →] theorem view_app_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_app pers st h = ok o) :
    SimR (Option.map absPairE) lst o (Arena.viewApp (absEIdx h)) := by
  rw [arena.monad.view_app] at hrun
  show (Arena.viewApp (absEIdx h)).run lst = _
  rw [show (Arena.viewApp (absEIdx h)).run lst
        = .ok (lst.store.viewApp (absEIdx h), lst) from rfl,
    estore_view_app_abs hrel.store hrun]

/-- `arena::monad::view_sort` against `Arena.viewSort`. -/
@[grind →] theorem view_sort_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_sort pers st h = ok o) :
    SimR (Option.map absLIdx) lst o (Arena.viewSort (absEIdx h)) := by
  rw [arena.monad.view_sort] at hrun
  show (Arena.viewSort (absEIdx h)).run lst = _
  rw [show (Arena.viewSort (absEIdx h)).run lst
        = .ok (lst.store.viewSort (absEIdx h), lst) from rfl,
    estore_view_sort_abs hrel.store hrun]

/-- `arena::monad::view_const` against `Arena.viewConst`. -/
@[grind →] theorem view_const_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_const pers st h = ok o) :
    SimR (Option.map absConstT) lst o (Arena.viewConst (absEIdx h)) := by
  rw [arena.monad.view_const] at hrun
  show (Arena.viewConst (absEIdx h)).run lst = _
  rw [show (Arena.viewConst (absEIdx h)).run lst
        = .ok (lst.store.viewConst (absEIdx h), lst) from rfl,
    estore_view_const_abs hrel.store hrun]

/-- `arena::monad::view_const_name` against `Arena.viewConstName`. -/
@[grind →] theorem view_const_name_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_const_name pers st h = ok o) :
    SimR (Option.map absNIdx) lst o (Arena.viewConstName (absEIdx h)) := by
  rw [arena.monad.view_const_name] at hrun
  show (Arena.viewConstName (absEIdx h)).run lst = _
  rw [show (Arena.viewConstName (absEIdx h)).run lst
        = .ok (lst.store.viewConstName (absEIdx h), lst) from rfl,
    estore_view_const_name_abs hrel.store hrun]

/-- `arena::monad::view_bvar` against `Arena.viewBVar`. -/
@[grind →] theorem view_bvar_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_bvar pers st h = ok o) :
    SimR (Option.map absU) lst o (Arena.viewBVar (absEIdx h)) := by
  rw [arena.monad.view_bvar] at hrun
  show (Arena.viewBVar (absEIdx h)).run lst = _
  rw [show (Arena.viewBVar (absEIdx h)).run lst
        = .ok (lst.store.viewBVar (absEIdx h), lst) from rfl,
    estore_view_bvar_abs hrel.store hrun]

/-- `arena::monad::view_fvar_idx` against `Arena.viewFVarIdx`. -/
@[grind →] theorem view_fvar_idx_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_fvar_idx pers st h = ok o) :
    SimR (Option.map absU) lst o (Arena.viewFVarIdx (absEIdx h)) := by
  rw [arena.monad.view_fvar_idx] at hrun
  show (Arena.viewFVarIdx (absEIdx h)).run lst = _
  rw [show (Arena.viewFVarIdx (absEIdx h)).run lst
        = .ok (lst.store.viewFVarIdx (absEIdx h), lst) from rfl,
    estore_view_fvar_idx_abs hrel.store hrun]

/-- `arena::monad::view_fvar_ty` against `Arena.viewFVarTy`. -/
@[grind →] theorem view_fvar_ty_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_fvar_ty pers st h = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.viewFVarTy (absEIdx h)) := by
  rw [arena.monad.view_fvar_ty] at hrun
  show (Arena.viewFVarTy (absEIdx h)).run lst = _
  rw [show (Arena.viewFVarTy (absEIdx h)).run lst
        = .ok (lst.store.viewFVarTy (absEIdx h), lst) from rfl,
    estore_view_fvar_ty_abs hrel.store hrun]

/-- `arena::monad::view_let` against `Arena.viewLet`. -/
@[grind →] theorem view_let_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_let pers st h = ok o) :
    SimR (Option.map absLetT) lst o (Arena.viewLet (absEIdx h)) := by
  rw [arena.monad.view_let] at hrun
  show (Arena.viewLet (absEIdx h)).run lst = _
  rw [show (Arena.viewLet (absEIdx h)).run lst
        = .ok (lst.store.viewLet (absEIdx h), lst) from rfl,
    estore_view_let_abs hrel.store hrun]

/-- `arena::monad::view_proj` against `Arena.viewProj`. -/
@[grind →] theorem view_proj_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_proj pers st h = ok o) :
    SimR (Option.map absProjT) lst o (Arena.viewProj (absEIdx h)) := by
  rw [arena.monad.view_proj] at hrun
  show (Arena.viewProj (absEIdx h)).run lst = _
  rw [show (Arena.viewProj (absEIdx h)).run lst
        = .ok (lst.store.viewProj (absEIdx h), lst) from rfl,
    estore_view_proj_abs hrel.store hrun]

/-! ### The one named failure primitive

Task #97s's template rule 7 on the Rust side: `arena::monad::fail` is `Err`
spelled once, so its inversion is one line and every failure site of the tier
goes through it.  `failDanglingE`/`failDanglingLs` are the two `#[cold]` arms
of `view` (task #97-P6-10), and their `AErrSim` is `internal`. -/

@[grind →] theorem fail_run {T : Type} {e : kernel.core_types.CheckError} {o}
    (hrun : arena.monad.fail T e = ok o) : o = .Err e := by
  rw [arena.monad.fail] at hrun
  exact (Result.ok_injective hrun).symm

/-- The twin's `fail` throws, which is the whole of the error half. -/
theorem arena_fail_run {γ : Type} (e : Arena.CheckError) (lst : AState) :
    (Arena.fail e : AM γ).run lst = .error e := rfl

/-- A Rust `Internal` decline is matched by the twin's `failDanglingE`. -/
theorem failDanglingE_errSim {γ : Type} {v : alloc.vec.Vec Std.U32}
    (lst : AState) :
    AErrSim (kernel.core_types.CheckError.Internal v)
      ((Arena.failDanglingE : AM γ).run lst) :=
  AErrSim.internal (by rfl)

/-- The same at the level-list handle. -/
theorem failDanglingLs_errSim {γ : Type} {v : alloc.vec.Vec Std.U32}
    (lst : AState) :
    AErrSim (kernel.core_types.CheckError.Internal v)
      ((Arena.failDanglingLs : AM γ).run lst) :=
  AErrSim.internal (by rfl)

/-! ### The memo probes

Thirteen tables, one lemma each: `HashMap2.get` under `MemosInv`'s `Inv` and
the key type's `Eq2Fwd` is the abstract map's read, and `MemosRel`'s clause at
that table is what carries it to the twin's `Std.HashMap`.  `KeysOk` is
vacuous at `P := fun _ => True` (`HashMap2.KeysOk_true`), which is why
`MemosInv` has no keys clause. -/

/-- `arena::monad::inst1_get` against `Arena.inst1Get`. -/
@[grind →] theorem inst1_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.inst1_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.inst1Get (absEIdxNat k)) := by
  rw [arena.monad.inst1_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.inst1C
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.inst1C k trivial
  show (Arena.inst1Get (absEIdxNat k)).run lst = _
  rw [show (Arena.inst1Get (absEIdxNat k)).run lst
        = .ok (lst.memos.inst1C[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::monad::inst_l_get` against `Arena.instLGet`. -/
@[grind →] theorem inst_l_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.inst_l_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.instLGet (absEIdxNat k)) := by
  rw [arena.monad.inst_l_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.instLC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.instLC k trivial
  show (Arena.instLGet (absEIdxNat k)).run lst = _
  rw [show (Arena.instLGet (absEIdxNat k)).run lst
        = .ok (lst.memos.instLC[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::monad::lift_get` against `Arena.liftGet`. -/
@[grind →] theorem lift_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.lift_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.liftGet (absEIdxNat k)) := by
  rw [arena.monad.lift_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.liftC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.liftC k trivial
  show (Arena.liftGet (absEIdxNat k)).run lst = _
  rw [show (Arena.liftGet (absEIdxNat k)).run lst
        = .ok (lst.memos.liftC[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::monad::reset_get` against `Arena.resetGet`. -/
@[grind →] theorem reset_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.reset_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.resetGet (absEIdxNat k)) := by
  rw [arena.monad.reset_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.resetC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.resetC k trivial
  show (Arena.resetGet (absEIdxNat k)).run lst = _
  rw [show (Arena.resetGet (absEIdxNat k)).run lst
        = .ok (lst.memos.resetC[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::monad::rename_get` against `Arena.renameGet`. -/
@[grind →] theorem rename_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.rename_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.renameGet (absEIdxNat k)) := by
  rw [arena.monad.rename_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.renameC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.renameC k trivial
  show (Arena.renameGet (absEIdxNat k)).run lst = _
  rw [show (Arena.renameGet (absEIdxNat k)).run lst
        = .ok (lst.memos.renameC[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::monad::abs1_get` against `Arena.abs1Get`. -/
@[grind →] theorem abs1_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.abs1_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.abs1Get (absEIdxNat k)) := by
  rw [arena.monad.abs1_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.abs1C
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.abs1C k trivial
  show (Arena.abs1Get (absEIdxNat k)).run lst = _
  rw [show (Arena.abs1Get (absEIdxNat k)).run lst
        = .ok (lst.memos.abs1C[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::monad::lower_get` against `Arena.lowerGet`. -/
@[grind →] theorem lower_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.lower_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.lowerGet (absEIdxNat k)) := by
  rw [arena.monad.lower_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.lowerC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.lowerC k trivial
  show (Arena.lowerGet (absEIdxNat k)).run lst = _
  rw [show (Arena.lowerGet (absEIdxNat k)).run lst
        = .ok (lst.memos.lowerC[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::monad::inst1_l_get` against `Arena.inst1LGet`. -/
@[grind →] theorem inst1_l_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.inst1_l_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.inst1LGet (absEIdxNat k)) := by
  rw [arena.monad.inst1_l_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.inst1LC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.inst1LC k trivial
  show (Arena.inst1LGet (absEIdxNat k)).run lst = _
  rw [show (Arena.inst1LGet (absEIdxNat k)).run lst
        = .ok (lst.memos.inst1LC[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::monad::inst_lp_get` against `Arena.instLPGet`. -/
@[grind →] theorem inst_lp_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.inst_lp_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.instLPGet (absEIdxNat k)) := by
  rw [arena.monad.inst_lp_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxNat_eq2 hinv.memos.instLPC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.instLPC k trivial
  show (Arena.instLPGet (absEIdxNat k)).run lst = _
  rw [show (Arena.instLPGet (absEIdxNat k)).run lst
        = .ok (lst.memos.instLPC[absEIdxNat k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::monad::bvar_b_get` against `Arena.bvarBGet`. -/
@[grind →] theorem bvar_b_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.EIdx} {o : Option Std.U64}
    (hrun : arena.monad.bvar_b_get st k = ok o) :
    SimR (Option.map absU) lst o (Arena.bvarBGet (absEIdx k)) := by
  rw [arena.monad.bvar_b_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hinv.memos.bvarBC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.bvarBC k trivial
  show (Arena.bvarBGet (absEIdx k)).run lst = _
  rw [show (Arena.bvarBGet (absEIdx k)).run lst
        = .ok (lst.memos.bvarBC[absEIdx k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option Std.U64) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    have h2 : some r = o := Result.ok_injective hrun
    subst h2
    rfl

/-- `arena::monad::fvar_b_get` against `Arena.fvarBGet`. -/
@[grind →] theorem fvar_b_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.EIdx} {o : Option Std.U64}
    (hrun : arena.monad.fvar_b_get st k = ok o) :
    SimR (Option.map absU) lst o (Arena.fvarBGet (absEIdx k)) := by
  rw [arena.monad.fvar_b_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hinv.memos.fvarBC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.fvarBC k trivial
  show (Arena.fvarBGet (absEIdx k)).run lst = _
  rw [show (Arena.fvarBGet (absEIdx k)).run lst
        = .ok (lst.memos.fvarBC[absEIdx k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option Std.U64) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    have h2 : some r = o := Result.ok_injective hrun
    subst h2
    rfl

/-- `arena::monad::inst_lp_l_get` against `Arena.instLPLGet`. -/
@[grind →] theorem inst_lp_l_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.LIdx} {o : Option arena.handle.LIdx}
    (hrun : arena.monad.inst_lp_l_get st k = ok o) :
    SimR (Option.map absLIdx) lst o (Arena.instLPLGet (absLIdx k)) := by
  rw [arena.monad.inst_lp_l_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lidx_eq2 hinv.memos.instLPLC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.instLPLC k trivial
  show (Arena.instLPLGet (absLIdx k)).run lst = _
  rw [show (Arena.instLPLGet (absLIdx k)).run lst
        = .ok (lst.memos.instLPLC[absLIdx k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.LIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_lidx _ _ hx]

/-- `arena::monad::inst_lp_ls_get` against `Arena.instLPLsGet`. -/
@[grind →] theorem inst_lp_ls_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.LsIdx} {o : Option arena.handle.LsIdx}
    (hrun : arena.monad.inst_lp_ls_get st k = ok o) :
    SimR (Option.map absLsIdx) lst o (Arena.instLPLsGet (absLsIdx k)) := by
  rw [arena.monad.inst_lp_ls_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lsidx_eq2 hinv.memos.instLPLsC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.memos.instLPLsC k trivial
  show (Arena.instLPLsGet (absLsIdx k)).run lst = _
  rw [show (Arena.instLPLsGet (absLsIdx k)).run lst
        = .ok (lst.memos.instLPLsC[absLsIdx k]?, lst) from rfl, ← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.LsIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_lsidx _ _ hx]

/-! ## The derived word: the ten-way dispatch

`ETables.der_at` reads the handle's tag ONCE and compares it against the ten
`ETAG_*` constants; the twin writes `i.tag == ETag.bvar` ten times.  The two
agree through `eidx_tag_abs` plus the ten one-line `etag_*_abs` equations, and
each arm is then `tbl_der_at_abs` at that array.  This is the shape
`ETables.get` will take when `view` is closed, so it is worth reading as the
template: **ten arms, five lines each, and the same five lines ten times.**

`arena::handle::ETAG_*` is `@[irreducible]` (Aeneas emits every `const` that
way), which is the constant round 3's soundness trap was about — hence the
`attribute [-grind]` line at the top of this file and the explicit
`rw [arena.handle.ETAG_*]` rather than a `decide`. -/

/-- `U64`'s `dup2` is the identity. -/
theorem dupId_u64 : DupId U64.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm

/-- `LDer`'s `dup2` is the identity. -/
theorem dupId_lder : DupId arena.store.LDer.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm

/-- `u64`'s out-of-range derived word is `0`, and the twin's `default` is
too — which is `tbl_der_at_abs`'s `hdf` hypothesis at the expression and name
stores. -/
theorem derDefault_u64 : ∀ d : Std.U64,
    U64.Insts.Con_ron_coreArenaStoreDerDefault.der_default = ok d →
    absU64 d = default := by
  intro d h
  rw [U64.Insts.Con_ron_coreArenaStoreDerDefault.der_default] at h
  rw [← Result.ok_injective h]
  rfl

/-- `LDer`'s out-of-range value is `⟨0, false⟩`, and the twin's `deriving
Inhabited` gives `⟨default, default⟩` — the same two. -/
theorem derDefault_lder : ∀ d : arena.store.LDer,
    arena.store.LDer.Insts.Con_ron_coreArenaStoreDerDefault.der_default = ok d →
    absLDer d = default := by
  intro d h
  rw [arena.store.LDer.Insts.Con_ron_coreArenaStoreDerDefault.der_default] at h
  rw [← Result.ok_injective h]
  rfl

/-- The tag comparison, once: the twin's `h.tag == ETag.C` is the Rust's
`t = ETAG_C`, given that the constant abstracts to the tag. -/
theorem etag_dec {t c : Std.U32} {lc : UInt32} (hc : absU32 c = lc) :
    ((absU32 t == lc) = true) ↔ (t = c) := by
  rw [← hc, beq_iff_eq]
  exact ⟨fun h => absU32_inj h, fun h => by rw [h]⟩

theorem etag_bvar_abs : absU32 arena.handle.ETAG_BVAR = ETag.bvar := by
  rw [arena.handle.ETAG_BVAR]; rfl

theorem etag_fvar_abs : absU32 arena.handle.ETAG_FVAR = ETag.fvar := by
  rw [arena.handle.ETAG_FVAR]; rfl

theorem etag_sort_abs : absU32 arena.handle.ETAG_SORT = ETag.sort := by
  rw [arena.handle.ETAG_SORT]; rfl

theorem etag_const_abs : absU32 arena.handle.ETAG_CONST = ETag.const := by
  rw [arena.handle.ETAG_CONST]; rfl

theorem etag_app_abs : absU32 arena.handle.ETAG_APP = ETag.app := by
  rw [arena.handle.ETAG_APP]; rfl

theorem etag_lam_abs : absU32 arena.handle.ETAG_LAM = ETag.lam := by
  rw [arena.handle.ETAG_LAM]; rfl

theorem etag_forallE_abs : absU32 arena.handle.ETAG_FORALL_E = ETag.forallE := by
  rw [arena.handle.ETAG_FORALL_E]; rfl

theorem etag_letE_abs : absU32 arena.handle.ETAG_LET_E = ETag.letE := by
  rw [arena.handle.ETAG_LET_E]; rfl

theorem etag_lit_abs : absU32 arena.handle.ETAG_LIT = ETag.lit := by
  rw [arena.handle.ETAG_LIT]; rfl

theorem etag_proj_abs : absU32 arena.handle.ETAG_PROJ = ETag.proj := by
  rw [arena.handle.ETAG_PROJ]; rfl

/-- `arena::store::ETables.der_at` against `ETables.derAt`. -/
theorem etables_der_at_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {d : Std.U64}
    (h : arena.store.ETables.der_at rt i = ok d) :
    derObsE (lt.derAt (absEIdx i)) = derObsE (absU64 d) := by
  rw [arena.store.ETables.der_at] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ETables.derAt, eidx_tag_abs ht]
  by_cases hb0 : t = arena.handle.ETAG_BVAR
  · rw [if_pos ((etag_dec etag_bvar_abs).mpr hb0)]
    rw [if_pos hb0] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [eidx_idxNat hn]
    exact tbl_der_at_abs hrel.bvars dupId_u64 derDefault_u64 h
  rw [if_neg (fun hx => hb0 ((etag_dec etag_bvar_abs).mp hx))]
  rw [if_neg hb0] at h
  by_cases hb1 : t = arena.handle.ETAG_FVAR
  · rw [if_pos ((etag_dec etag_fvar_abs).mpr hb1)]
    rw [if_pos hb1] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [eidx_idxNat hn]
    exact tbl_der_at_abs hrel.fvars dupId_u64 derDefault_u64 h
  rw [if_neg (fun hx => hb1 ((etag_dec etag_fvar_abs).mp hx))]
  rw [if_neg hb1] at h
  by_cases hb2 : t = arena.handle.ETAG_SORT
  · rw [if_pos ((etag_dec etag_sort_abs).mpr hb2)]
    rw [if_pos hb2] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [eidx_idxNat hn]
    exact tbl_der_at_abs hrel.sorts dupId_u64 derDefault_u64 h
  rw [if_neg (fun hx => hb2 ((etag_dec etag_sort_abs).mp hx))]
  rw [if_neg hb2] at h
  by_cases hb3 : t = arena.handle.ETAG_CONST
  · rw [if_pos ((etag_dec etag_const_abs).mpr hb3)]
    rw [if_pos hb3] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [eidx_idxNat hn]
    exact tbl_der_at_abs hrel.consts dupId_u64 derDefault_u64 h
  rw [if_neg (fun hx => hb3 ((etag_dec etag_const_abs).mp hx))]
  rw [if_neg hb3] at h
  by_cases hb4 : t = arena.handle.ETAG_APP
  · rw [if_pos ((etag_dec etag_app_abs).mpr hb4)]
    rw [if_pos hb4] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [eidx_idxNat hn]
    exact tbl_der_at_abs hrel.apps dupId_u64 derDefault_u64 h
  rw [if_neg (fun hx => hb4 ((etag_dec etag_app_abs).mp hx))]
  rw [if_neg hb4] at h
  by_cases hb5 : t = arena.handle.ETAG_LAM
  · rw [if_pos ((etag_dec etag_lam_abs).mpr hb5)]
    rw [if_pos hb5] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [eidx_idxNat hn]
    exact tbl_der_at_abs hrel.lams dupId_u64 derDefault_u64 h
  rw [if_neg (fun hx => hb5 ((etag_dec etag_lam_abs).mp hx))]
  rw [if_neg hb5] at h
  by_cases hb6 : t = arena.handle.ETAG_FORALL_E
  · rw [if_pos ((etag_dec etag_forallE_abs).mpr hb6)]
    rw [if_pos hb6] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [eidx_idxNat hn]
    exact tbl_der_at_abs hrel.foralls dupId_u64 derDefault_u64 h
  rw [if_neg (fun hx => hb6 ((etag_dec etag_forallE_abs).mp hx))]
  rw [if_neg hb6] at h
  by_cases hb7 : t = arena.handle.ETAG_LET_E
  · rw [if_pos ((etag_dec etag_letE_abs).mpr hb7)]
    rw [if_pos hb7] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [eidx_idxNat hn]
    exact tbl_der_at_abs hrel.lets dupId_u64 derDefault_u64 h
  rw [if_neg (fun hx => hb7 ((etag_dec etag_letE_abs).mp hx))]
  rw [if_neg hb7] at h
  by_cases hb8 : t = arena.handle.ETAG_LIT
  · rw [if_pos ((etag_dec etag_lit_abs).mpr hb8)]
    rw [if_pos hb8] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [eidx_idxNat hn]
    exact tbl_der_at_abs hrel.lits dupId_u64 derDefault_u64 h
  rw [if_neg (fun hx => hb8 ((etag_dec etag_lit_abs).mp hx))]
  rw [if_neg hb8] at h
  by_cases hb9 : t = arena.handle.ETAG_PROJ
  · rw [if_pos ((etag_dec etag_proj_abs).mpr hb9)]
    rw [if_pos hb9] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [eidx_idxNat hn]
    exact tbl_der_at_abs hrel.projs dupId_u64 derDefault_u64 h
  rw [if_neg (fun hx => hb9 ((etag_dec etag_proj_abs).mp hx))]
  rw [if_neg hb9] at h
  have h2 : (0#u64 : Std.U64) = d := Result.ok_injective h
  rw [← h2]
  rfl

/-- `arena::store::EStore.derived` against `EStore.derived` — the tier select
over the ten-way dispatch, and `pers_der_at`'s `shared_on` is `rPersE` again
(task #97-LC §1). -/
theorem estore_derived_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {d : Std.U64}
    (h : arena.store.EStore.derived rs pers i = ok d) :
    derObsE (ls.derived (absEIdx i)) = derObsE (absU64 d) := by
  rw [arena.store.EStore.derived] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.derived]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv])]
    rw [arena.store.EStore.pers_der_at] at h
    have h3 : arena.store.ETables.der_at (rPersE pers rs) i = ok d := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_der_at_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_der_at_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (0#u64 : Std.U64) = d := Result.ok_injective h
      rw [← h2]
      rfl

/-- `arena::monad::derived_e` against `Arena.derivedE` — the packed derived
word, in `O(1)` off the derived column. -/
@[grind →] theorem derived_e_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {d : Std.U64}
    (hrun : arena.monad.derived_e pers st h = ok d) :
    SimRO absU64 derObsE lst d (Arena.derivedE (absEIdx h)) := by
  rw [arena.monad.derived_e] at hrun
  exact SimRO.mk rfl (estore_derived_abs hrel.store hrun)

/-! ## `view`: the ten-way decode

`ETables.get`'s ten arms in the twin's own order — the five leading
constructor reads, **`isBind` answering `none`** (task #97-P6-16: a binder's
datum carries its own tier bit, so one tier cannot resolve it), then `letE`,
`lit`, `proj` and the final `none`.  The Rust is that function clause for
clause, so the proof is `der_at`'s ten-arm peel again with a node-view
construction at the end of each arm.

`EStore.view` then dispatches the two binder tags through `viewBind`, which is
`viewBindI` followed by `viewBM` — the one place two tier selects meet — and
`monad::view` is that under a state read with `view`'s own `Internal`
decline. -/

/-- `arena::handle::e_tag_is_bind` against `ETag.isBind`. -/
theorem etag_isBind_abs {t : Std.U32} {b : Bool}
    (h : arena.handle.e_tag_is_bind t = ok b) : ETag.isBind (absU32 t) = b := by
  rw [arena.handle.e_tag_is_bind] at h
  rw [ETag.isBind]
  by_cases hl : t = arena.handle.ETAG_LAM
  · rw [if_pos hl] at h
    have h2 : true = b := Result.ok_injective h
    rw [← h2, (etag_dec etag_lam_abs).mpr hl]
    rfl
  · rw [if_neg hl] at h
    have h2 : decide (t = arena.handle.ETAG_FORALL_E) = b := Result.ok_injective h
    have hlf : (absU32 t == ETag.lam) = false := by
      by_contra hc
      exact hl ((etag_dec etag_lam_abs).mp (by simpa using hc))
    rw [hlf, ← h2]
    simp only [Bool.false_or]
    by_cases hf : t = arena.handle.ETAG_FORALL_E
    · rw [(etag_dec etag_forallE_abs).mpr hf, decide_eq_true hf]
    · have hff : (absU32 t == ETag.forallE) = false := by
        by_contra hc
        exact hf ((etag_dec etag_forallE_abs).mp (by simpa using hc))
      rw [hff, decide_eq_false hf]

/-- `arena::store::ETables.get` against `ETables.get`. -/
theorem etables_get_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o : Option arena.store.ENodeView}
    (h : arena.store.ETables.get rt i = ok o) :
    lt.get (absEIdx i) = o.map absENodeView := by
  rw [arena.store.ETables.get] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ETables.get, eidx_tag_abs ht]
  by_cases hb0 : t = arena.handle.ETAG_BVAR
  · rw [if_pos ((etag_dec etag_bvar_abs).mpr hb0)]
    rw [if_pos hb0] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.bvars hp
    rw [eidx_idxNat hm, hnode]
    cases hpc : p with
    | none =>
      rw [hpc] at h
      have h2 : (none : Option arena.store.ENodeView) = o :=
        Result.ok_injective h
      subst h2
      rfl
    | some r =>
      rw [hpc] at h
      have h2 : some _ = o := Result.ok_injective h
      subst h2
      rfl
  rw [if_neg (fun hx => hb0 ((etag_dec etag_bvar_abs).mp hx))]
  rw [if_neg hb0] at h
  by_cases hb1 : t = arena.handle.ETAG_FVAR
  · rw [if_pos ((etag_dec etag_fvar_abs).mpr hb1)]
    rw [if_pos hb1] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.fvars hp
    rw [eidx_idxNat hm, hnode]
    cases hpc : p with
    | none =>
      rw [hpc] at h
      have h2 : (none : Option arena.store.ENodeView) = o :=
        Result.ok_injective h
      subst h2
      rfl
    | some r =>
      rw [hpc] at h
      obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some _ = o := Result.ok_injective h
      subst h2
      rw [dupId_eidx _ _ hx0]
      rfl
  rw [if_neg (fun hx => hb1 ((etag_dec etag_fvar_abs).mp hx))]
  rw [if_neg hb1] at h
  by_cases hb2 : t = arena.handle.ETAG_SORT
  · rw [if_pos ((etag_dec etag_sort_abs).mpr hb2)]
    rw [if_pos hb2] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.sorts hp
    rw [eidx_idxNat hm, hnode]
    cases hpc : p with
    | none =>
      rw [hpc] at h
      have h2 : (none : Option arena.store.ENodeView) = o :=
        Result.ok_injective h
      subst h2
      rfl
    | some r =>
      rw [hpc] at h
      obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some _ = o := Result.ok_injective h
      subst h2
      rw [dupId_lidx _ _ hx0]
      rfl
  rw [if_neg (fun hx => hb2 ((etag_dec etag_sort_abs).mp hx))]
  rw [if_neg hb2] at h
  by_cases hb3 : t = arena.handle.ETAG_CONST
  · rw [if_pos ((etag_dec etag_const_abs).mpr hb3)]
    rw [if_pos hb3] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.consts hp
    rw [eidx_idxNat hm, hnode]
    cases hpc : p with
    | none =>
      rw [hpc] at h
      have h2 : (none : Option arena.store.ENodeView) = o :=
        Result.ok_injective h
      subst h2
      rfl
    | some r =>
      rw [hpc] at h
      obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some _ = o := Result.ok_injective h
      subst h2
      rw [dupId_nidx _ _ hx0, dupId_lsidx _ _ hx1]
      rfl
  rw [if_neg (fun hx => hb3 ((etag_dec etag_const_abs).mp hx))]
  rw [if_neg hb3] at h
  by_cases hb4 : t = arena.handle.ETAG_APP
  · rw [if_pos ((etag_dec etag_app_abs).mpr hb4)]
    rw [if_pos hb4] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.apps hp
    rw [eidx_idxNat hm, hnode]
    cases hpc : p with
    | none =>
      rw [hpc] at h
      have h2 : (none : Option arena.store.ENodeView) = o :=
        Result.ok_injective h
      subst h2
      rfl
    | some r =>
      rw [hpc] at h
      obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some _ = o := Result.ok_injective h
      subst h2
      rw [dupId_eidx _ _ hx0, dupId_eidx _ _ hx1]
      rfl
  rw [if_neg (fun hx => hb4 ((etag_dec etag_app_abs).mp hx))]
  rw [if_neg hb4] at h
  obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [etag_isBind_abs hbb]
  split at h <;> rename_i hbv
  · rw [if_pos hbv]
    have h2 : (none : Option arena.store.ENodeView) = o := Result.ok_injective h
    subst h2
    rfl
  rw [if_neg hbv]
  by_cases hb5 : t = arena.handle.ETAG_LET_E
  · rw [if_pos ((etag_dec etag_letE_abs).mpr hb5)]
    rw [if_pos hb5] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.lets hp
    rw [eidx_idxNat hm, hnode]
    cases hpc : p with
    | none =>
      rw [hpc] at h
      have h2 : (none : Option arena.store.ENodeView) = o :=
        Result.ok_injective h
      subst h2
      rfl
    | some r =>
      rw [hpc] at h
      obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x2, hx2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some _ = o := Result.ok_injective h
      subst h2
      rw [dupId_eidx _ _ hx0, dupId_eidx _ _ hx1, dupId_eidx _ _ hx2]
      rfl
  rw [if_neg (fun hx => hb5 ((etag_dec etag_letE_abs).mp hx))]
  rw [if_neg hb5] at h
  by_cases hb6 : t = arena.handle.ETAG_LIT
  · rw [if_pos ((etag_dec etag_lit_abs).mpr hb6)]
    rw [if_pos hb6] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.lits hp
    rw [eidx_idxNat hm, hnode]
    cases hpc : p with
    | none =>
      rw [hpc] at h
      have h2 : (none : Option arena.store.ENodeView) = o :=
        Result.ok_injective h
      subst h2
      rfl
    | some r =>
      rw [hpc] at h
      obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some _ = o := Result.ok_injective h
      subst h2
      rw [ConRon.Refine.Expr.literal_dup_eq hx0]
      rfl
  rw [if_neg (fun hx => hb6 ((etag_dec etag_lit_abs).mp hx))]
  rw [if_neg hb6] at h
  by_cases hb7 : t = arena.handle.ETAG_PROJ
  · rw [if_pos ((etag_dec etag_proj_abs).mpr hb7)]
    rw [if_pos hb7] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.projs hp
    rw [eidx_idxNat hm, hnode]
    cases hpc : p with
    | none =>
      rw [hpc] at h
      have h2 : (none : Option arena.store.ENodeView) = o :=
        Result.ok_injective h
      subst h2
      rfl
    | some r =>
      rw [hpc] at h
      obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some _ = o := Result.ok_injective h
      subst h2
      rw [dupId_nidx _ _ hx0, dupId_eidx _ _ hx1]
      rfl
  rw [if_neg (fun hx => hb7 ((etag_dec etag_proj_abs).mp hx))]
  rw [if_neg hb7] at h
  have h2 : (none : Option arena.store.ENodeView) = o := Result.ok_injective h
  subst h2
  rfl


/-- A binder-datum handle's tier bit. -/
theorem bmidx_is_persistent_abs {i : arena.handle.BMIdx} {b : Bool}
    (h : arena.handle.BMIdx.is_persistent i = ok b) :
    (absBMIdx i).isPersistent = b := by
  rw [arena.handle.BMIdx.is_persistent] at h
  have hp := word_is_persistent_abs h
  simpa [Idx.isPersistent, Idx.tier, absBMIdx] using hp

/-! ### The binder arms: two tier selects meeting

`ETables.get_bind` is the tag dispatch between the `lams` and the `foralls`
array, `ETables.get_bm` reads the binder-datum store, and `EStore.view_bind`
is the first followed by the second — the one place where a handle's tier bit
and its DATUM's tier bit are both consulted (task #97-P6-16).

**`get_bind` needs the caller's guard, and that is finding 3 again.**  The
twin's `ETables.getBind` has a third arm answering `none` at a non-binder
tag; the Rust's has two, so at a `bvar` handle it reads the `foralls` array
where the twin answers `none`.  Every caller guards it with `e_tag_is_bind`
(that is what `EStore::view` does), so the two never differ in the program —
but the LEMMA is false without the guard, and it is stated with it. -/

theorem etables_get_bm_abs {rt lt} (hrel : ETablesRel rt lt)
    {m : arena.handle.BMIdx} {o}
    (h : arena.store.ETables.get_bm rt m = ok o) :
    lt.getBM (absBMIdx m) = o.map ConRon.Refine.absBinderMeta := by
  rw [arena.store.ETables.get_bm] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.bms hp
  rw [ETables.getBM, bmidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option kernel.expr.BinderMeta) = o := Result.ok_injective h
    subst h2
    rfl
  | some r =>
    rw [hpc] at h
    obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some bm = o := Result.ok_injective h
    subst h2
    rw [ConRon.Refine.PropWhen.dup_eq hpw] at hbm
    have h3 : bm = ⟨r.pw⟩ := by
      rw [kernel.expr.binder_meta] at hbm
      exact (Result.ok_injective hbm).symm
    subst h3
    rfl

theorem etables_get_bind_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o}
    (hbind : ETag.isBind (absEIdx i).tag = true)
    (h : arena.store.ETables.get_bind rt i = ok o) :
    lt.getBind (absEIdx i) = o.map absBindI := by
  rw [arena.store.ETables.get_bind] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [eidx_tag_abs ht] at hbind
  rw [ETables.getBind, eidx_tag_abs ht]
  by_cases hl : t = arena.handle.ETAG_LAM
  · rw [if_pos ((etag_dec etag_lam_abs).mpr hl)]
    rw [if_pos hl] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.lams hp
    rw [eidx_idxNat hn, hnode]
    cases hpc : p with
    | none =>
      rw [hpc] at h
      have h2 : (none : Option (arena.handle.EIdx × arena.handle.EIdx ×
        arena.handle.BMIdx)) = o := Result.ok_injective h
      subst h2
      rfl
    | some r =>
      rw [hpc] at h
      obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x2, hx2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some _ = o := Result.ok_injective h
      subst h2
      rw [dupId_eidx _ _ hx0, dupId_eidx _ _ hx1, dupId_bmidx _ _ hx2]
      rfl
  · have hlf : (absU32 t == ETag.lam) = false := by
      by_contra hc
      exact hl ((etag_dec etag_lam_abs).mp (by simpa using hc))
    have hf : t = arena.handle.ETAG_FORALL_E := by
      rw [ETag.isBind, hlf, Bool.false_or] at hbind
      exact (etag_dec etag_forallE_abs).mp hbind
    rw [if_neg (by rw [hlf]; simp), if_pos ((etag_dec etag_forallE_abs).mpr hf)]
    rw [if_neg hl] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.foralls hp
    rw [eidx_idxNat hn, hnode]
    cases hpc : p with
    | none =>
      rw [hpc] at h
      have h2 : (none : Option (arena.handle.EIdx × arena.handle.EIdx ×
        arena.handle.BMIdx)) = o := Result.ok_injective h
      subst h2
      rfl
    | some r =>
      rw [hpc] at h
      obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x2, hx2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some _ = o := Result.ok_injective h
      subst h2
      rw [dupId_eidx _ _ hx0, dupId_eidx _ _ hx1, dupId_bmidx _ _ hx2]
      rfl

theorem estore_view_bm_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {m : arena.handle.BMIdx} {o}
    (h : arena.store.EStore.view_bm rs pers m = ok o) :
    ls.viewBM (absBMIdx m) = o.map ConRon.Refine.absBinderMeta := by
  rw [arena.store.EStore.view_bm] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := bmidx_is_persistent_abs hb
  rw [EStore.viewBM]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absBMIdx m).isPersistent = true by rw [hb2, hbv]),
      EStore.persGetBM]
    rw [arena.store.EStore.pers_get_bm] at h
    have h3 : arena.store.ETables.get_bm (rPersE pers rs) m = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_bm_abs hrel.perst h3
  · rw [if_neg (show ¬ (absBMIdx m).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_bm_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option kernel.expr.BinderMeta) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_bind_i_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o}
    (hbind : ETag.isBind (absEIdx i).tag = true)
    (h : arena.store.EStore.view_bind_i rs pers i = ok o) :
    ls.viewBindI (absEIdx i) = o.map absBindI := by
  rw [arena.store.EStore.view_bind_i] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewBindI]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]),
      EStore.persGetBind]
    rw [arena.store.EStore.pers_get_bind] at h
    have h3 : arena.store.ETables.get_bind (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_bind_abs hrel.perst hbind h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_bind_abs hrel.scrt hbind h
    · rw [if_neg hs]
      have h2 : (none : Option (arena.handle.EIdx × arena.handle.EIdx ×
        arena.handle.BMIdx)) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_bind_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o}
    (hbind : ETag.isBind (absEIdx i).tag = true)
    (h : arena.store.EStore.view_bind rs pers i = ok o) :
    ls.viewBind (absEIdx i) = o.map absBindM := by
  rw [arena.store.EStore.view_bind] at h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hqa := estore_view_bind_i_abs hrel hbind hq
  rw [EStore.viewBind, hqa]
  cases hqc : q with
  | none =>
    rw [hqc] at h
    have h2 : (none : Option (arena.handle.EIdx × arena.handle.EIdx ×
      kernel.expr.BinderMeta)) = o := Result.ok_injective h
    subst h2
    rfl
  | some tt =>
    rw [hqc] at h
    obtain ⟨ty, bo, mi⟩ := tt
    obtain ⟨u, hu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hua := estore_view_bm_abs hrel hu
    simp only [Option.map_some, absBindI]
    rw [hua]
    cases huc : u with
    | none =>
      rw [huc] at h
      have h2 : (none : Option (arena.handle.EIdx × arena.handle.EIdx ×
        kernel.expr.BinderMeta)) = o := Result.ok_injective h
      subst h2
      rfl
    | some mm =>
      rw [huc] at h
      have h2 : some (ty, bo, mm) = o := Result.ok_injective h
      subst h2
      rfl

theorem e_bind_view_abs {t : Std.U32} {ty bo : arena.handle.EIdx}
    {m : kernel.expr.BinderMeta} {v : arena.store.ENodeView}
    (h : arena.store.e_bind_view t ty bo m = ok v) :
    eBindView (absU32 t) (absEIdx ty) (absEIdx bo)
      (ConRon.Refine.absBinderMeta m) = absENodeView v := by
  rw [arena.store.e_bind_view] at h
  rw [eBindView]
  by_cases hl : t = arena.handle.ETAG_LAM
  · rw [if_pos ((etag_dec etag_lam_abs).mpr hl)]
    rw [if_pos hl] at h
    have h2 : arena.store.ENodeView.Lam ty bo m = v := Result.ok_injective h
    subst h2
    rfl
  · rw [if_neg (fun hx => hl ((etag_dec etag_lam_abs).mp hx))]
    rw [if_neg hl] at h
    have h2 : arena.store.ENodeView.ForallE ty bo m = v := Result.ok_injective h
    subst h2
    rfl

theorem estore_view_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o}
    (h : arena.store.EStore.view rs pers i = ok o) :
    ls.view (absEIdx i) = o.map absENodeView := by
  rw [arena.store.EStore.view] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [EStore.view, eidx_tag_abs ht, etag_isBind_abs hbb]
  split at h <;> rename_i hbv
  · rw [if_pos hbv]
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqa := estore_view_bind_abs hrel
      (by rw [eidx_tag_abs ht, etag_isBind_abs hbb]; exact hbv) hq
    rw [hqa]
    cases hqc : q with
    | none =>
      rw [hqc] at h
      have h2 : (none : Option arena.store.ENodeView) = o := Result.ok_injective h
      subst h2
      rfl
    | some tt =>
      rw [hqc] at h
      obtain ⟨ty, bo, mm⟩ := tt
      obtain ⟨ev, hev, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some ev = o := Result.ok_injective h
      subst h2
      simp only [Option.map_some, absBindM]
      rw [e_bind_view_abs hev]
  · rw [if_neg hbv]
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hb2 := eidx_is_persistent_abs hb1
    split at h <;> rename_i hpv
    · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hpv])]
      rw [arena.store.EStore.pers_get] at h
      have h3 : arena.store.ETables.get (rPersE pers rs) i = ok o := by
        unfold rPersE
        split at h <;> rename_i hs
        · rw [if_pos hs]; exact h
        · rw [if_neg hs]; exact h
      exact etables_get_abs hrel.perst h3
    · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by
            rw [hb2]; simpa using hpv), hrel.scratchOn]
      split at h <;> rename_i hs
      · rw [if_pos hs]
        exact etables_get_abs hrel.scrt h
      · rw [if_neg hs]
        have h2 : (none : Option arena.store.ENodeView) = o := Result.ok_injective h
        subst h2
        rfl

/-! ### `arena::monad`'s `view` and the binder readers

`view` is the one reader of the tier with an ERROR arm — the dangling-handle
`Internal` decline both sides spell — so it is `AOut` and not `SimR`, and its
success arm leaves the state where it found it (`Ext.refl`).

The three binder readers carry finding 3's guard, for the reason
`etables_get_bind_abs` does: the twin's `getBind` has a third arm answering
`none` at a non-binder tag and the Rust's has two. -/

/-- `arena::monad::view` against `Arena.view`. -/
@[grind →] theorem view_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view pers st h = ok o) :
    AOut absENodeView (fun _ => True) pers lst o st
      ((Arena.view (absEIdx h)).run lst) := by
  rw [arena.monad.view] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hqa := estore_view_abs hrel.store hq
  have hrunL : (Arena.view (absEIdx h)).run lst
      = (match lst.store.view (absEIdx h) with
         | some v => Except.ok (v, lst)
         | none => Except.error (Arena.CheckError.internal
             "arena: dangling expression handle")) := by
    show ((match lst.store.view (absEIdx h) with
            | some v => (pure v : AM ENodeView)
            | none => Arena.fail
                (.internal "arena: dangling expression handle")).run lst) = _
    cases lst.store.view (absEIdx h) <;> rfl
  cases hqc : q with
  | none =>
    rw [hqc] at hrun
    obtain ⟨s, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 : core.result.Result.Err
        (kernel.core_types.CheckError.Internal v) = o := Result.ok_injective hrun
    subst h2
    refine AErrSim.internal (s := "arena: dangling expression handle") ?_
    rw [hrunL, hqa, hqc]
    rfl
  | some v =>
    rw [hqc] at hrun
    have h2 : core.result.Result.Ok v = o := Result.ok_injective hrun
    subst h2
    refine AOut.ok (lst' := lst) ?_ hrel hinv (Ext.refl _) trivial
    rw [hrunL, hqa, hqc]
    rfl

/-- `arena::monad::view_bind_i` against `Arena.viewBindI` (task #97-P6-16: the
binder projection that stops at the datum's HANDLE). -/
@[grind →] theorem view_bind_i_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hbind : ETag.isBind (absEIdx h).tag = true)
    (hrun : arena.monad.view_bind_i pers st h = ok o) :
    SimR (Option.map absBindI) lst o (Arena.viewBindI (absEIdx h)) := by
  rw [arena.monad.view_bind_i] at hrun
  show (Arena.viewBindI (absEIdx h)).run lst = _
  rw [show (Arena.viewBindI (absEIdx h)).run lst
        = .ok (lst.store.viewBindI (absEIdx h), lst) from rfl,
    estore_view_bind_i_abs hrel.store hbind hrun]

/-- `arena::monad::view_bind` against `Arena.viewBind` — `viewBindI` then
`viewBM`, the two tier selects meeting. -/
@[grind →] theorem view_bind_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hbind : ETag.isBind (absEIdx h).tag = true)
    (hrun : arena.monad.view_bind pers st h = ok o) :
    SimR (Option.map absBindM) lst o (Arena.viewBind (absEIdx h)) := by
  rw [arena.monad.view_bind] at hrun
  show (Arena.viewBind (absEIdx h)).run lst = _
  rw [show (Arena.viewBind (absEIdx h)).run lst
        = .ok (lst.store.viewBind (absEIdx h), lst) from rfl,
    estore_view_bind_abs hrel.store hbind hrun]

/-- **`Arena.viewBM` has no `arena::monad` wrapper** — a shape difference, and
a small one: `arena/monad.rs` stops at `view_bind`/`view_bind_i` and its
binder-datum read goes straight to `EStore::view_bm`, where the twin's
`Monad.lean` names a `viewBM` of its own.  Both are the same store read under
the same state, so the refinement states the lemma at the STORE function and
the twin's monadic wrapper is `rfl` over it. -/
@[grind →] theorem view_bm_run {pers st lst} (hrel : AStateRel pers st lst)
    {m : arena.handle.BMIdx} {o}
    (hrun : arena.store.EStore.view_bm st.store pers m = ok o) :
    SimR (Option.map ConRon.Refine.absBinderMeta) lst o
      (Arena.viewBM (absBMIdx m)) := by
  show (Arena.viewBM (absBMIdx m)).run lst = _
  rw [show (Arena.viewBM (absBMIdx m)).run lst
        = .ok (lst.store.viewBM (absBMIdx m), lst) from rfl,
    estore_view_bm_abs hrel.store hrun]

/-! ## The rest of the layer: stated, not yet closed

The brief's ask is *one `_run` lemma per primitive of `arena::monad` /
`arena::store`*, and these are the ones whose PROOF needs a floor this task
did not build: `EStore.view`'s ten-way `ETables.get` (and the two binder arms
that meet `viewBM`'s own tier select), `ETables.der_at`'s ten-way derived
dispatch, and — the big one — `EStore.intern`'s probe-then-push, whose
abstraction obligation is `HashMap2.Rel_insert_wf` on the cons table PLUS the
`Array.push` on the two columns PLUS the handle `Idx.mk` at the tier, at each
of the eighteen arrays.

Every statement below is the shape the ExprOps tier consumes, so writing them
here is what lets `Refine2/ExprOps/*` be stated and proved against a fixed
interface; the `sorry`s are named in the task's report and are the next
round's work.  **The statements are not weakened**: each is the full-outcome
claim of DESIGN §8.2 at the abstraction the twin has. -/

/-! ## The three remaining tier bits and the three remaining tag constants -/

theorem nidx_is_persistent_abs {i : arena.handle.NIdx} {b : Bool}
    (h : arena.handle.NIdx.is_persistent i = ok b) :
    (absNIdx i).isPersistent = b := by
  rw [arena.handle.NIdx.is_persistent] at h
  have hp := word_is_persistent_abs h
  simpa [Idx.isPersistent, Idx.tier, absNIdx] using hp

theorem lidx_is_persistent_abs {i : arena.handle.LIdx} {b : Bool}
    (h : arena.handle.LIdx.is_persistent i = ok b) :
    (absLIdx i).isPersistent = b := by
  rw [arena.handle.LIdx.is_persistent] at h
  have hp := word_is_persistent_abs h
  simpa [Idx.isPersistent, Idx.tier, absLIdx] using hp

theorem lsidx_is_persistent_abs {i : arena.handle.LsIdx} {b : Bool}
    (h : arena.handle.LsIdx.is_persistent i = ok b) :
    (absLsIdx i).isPersistent = b := by
  rw [arena.handle.LsIdx.is_persistent] at h
  have hp := word_is_persistent_abs h
  simpa [Idx.isPersistent, Idx.tier, absLsIdx] using hp

theorem lsidx_tag_abs {i : arena.handle.LsIdx} {t : Std.U32}
    (h : arena.handle.LsIdx.tag i = ok t) : (absLsIdx i).tag = absU32 t := by
  rw [arena.handle.LsIdx.tag] at h
  exact word_tag_abs h

theorem ntag_anonymous_abs : absU32 arena.handle.NTAG_ANONYMOUS = NTag.anonymous := by
  rw [arena.handle.NTAG_ANONYMOUS]; rfl
theorem ntag_str_abs : absU32 arena.handle.NTAG_STR = NTag.str := by
  rw [arena.handle.NTAG_STR]; rfl
theorem ntag_num_abs : absU32 arena.handle.NTAG_NUM = NTag.num := by
  rw [arena.handle.NTAG_NUM]; rfl

theorem ltag_zero_abs : absU32 arena.handle.LTAG_ZERO = LTag.zero := by
  rw [arena.handle.LTAG_ZERO]; rfl
theorem ltag_succ_abs : absU32 arena.handle.LTAG_SUCC = LTag.succ := by
  rw [arena.handle.LTAG_SUCC]; rfl
theorem ltag_max_abs : absU32 arena.handle.LTAG_MAX = LTag.max := by
  rw [arena.handle.LTAG_MAX]; rfl
theorem ltag_imax_abs : absU32 arena.handle.LTAG_IMAX = LTag.imax := by
  rw [arena.handle.LTAG_IMAX]; rfl
theorem ltag_param_abs : absU32 arena.handle.LTAG_PARAM = LTag.param := by
  rw [arena.handle.LTAG_PARAM]; rfl

theorem lstag_list_abs : absU32 arena.handle.LSTAG_LIST = LsTag.list := by
  rw [arena.handle.LSTAG_LIST]; rfl

/-! ## `arena::store::lidx_vec_dup` is the identity on the list -/

theorem lidx_vec_dup_from_val {us : alloc.vec.Vec arena.handle.LIdx} :
    ∀ k : Nat, ∀ (i : Std.Usize) (out r : alloc.vec.Vec arena.handle.LIdx),
      us.val.length - i.val ≤ k →
      arena.store.lidx_vec_dup_from us i out = ok r →
      r.val = out.val ++ us.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out r hk h
    rw [arena.store.lidx_vec_dup_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len us by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac), List.append_nil]
  | succ k ih =>
    intro i out r hk h
    rw [arena.store.lidx_vec_dup_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ us.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len us by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac), List.append_nil]
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len us by scalar_tac)] at h
      have hlt : i.val < us.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := us.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := ConRon.Refine.usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec us i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, ConRon.Refine.bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨d, hd, h⟩ := h
      rw [dupId_lidx _ _ hd] at h
      obtain ⟨o1, ho1, h⟩ := h
      simp only [hw, Result.ok.injEq, exists_eq_left'] at h
      have hrec := ih w o1 r (by scalar_tac) h
      rw [hrec, ConRon.Refine.vec_push_val ho1, hwv, List.drop_eq_getElem_cons hlt]
      simp

theorem lidx_vec_dup_eq {us r : alloc.vec.Vec arena.handle.LIdx}
    (h : arena.store.lidx_vec_dup us = ok r) : r.val = us.val := by
  rw [arena.store.lidx_vec_dup] at h
  have := lidx_vec_dup_from_val us.val.length 0#usize
    (alloc.vec.Vec.with_capacity arena.handle.LIdx (alloc.vec.Vec.len us)) r
    (by scalar_tac) h
  simpa [alloc.vec.Vec.with_capacity] using this

/-! ## The name, level and level-list tiers -/

theorem ntables_get_abs {rt lt} (hrel : NTablesRel rt lt)
    {i : arena.handle.NIdx} {o : Option arena.store.NNodeView}
    (h : arena.store.NTables.get rt i = ok o) :
    lt.get (absNIdx i) = o.map absNNodeView := by
  rw [arena.store.NTables.get] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [NTables.get, nidx_tag_abs ht]
  by_cases ha : t = arena.handle.NTAG_ANONYMOUS
  · rw [if_pos ((etag_dec ntag_anonymous_abs).mpr ha)]
    rw [if_pos ha] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.anons hp
    rw [nidx_idxNat hm, hnode]
    cases hpc : p with
    | none => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
    | some r => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
  · rw [if_neg (fun hx => ha ((etag_dec ntag_anonymous_abs).mp hx))]
    rw [if_neg ha] at h
    by_cases hs : t = arena.handle.NTAG_STR
    · rw [if_pos ((etag_dec ntag_str_abs).mpr hs)]
      rw [if_pos hs] at h
      obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnode := tbl_node_abs hrel.strs hp
      rw [nidx_idxNat hm, hnode]
      cases hpc : p with
      | none => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
      | some r =>
        rw [hpc] at h
        obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have h2 := Result.ok_injective h
        subst h2
        rw [dupId_nidx _ _ hx0, ConRon.Refine.Expr.str_copy_eq hx1]
        rfl
    · rw [if_neg (fun hx => hs ((etag_dec ntag_str_abs).mp hx))]
      rw [if_neg hs] at h
      by_cases hn : t = arena.handle.NTAG_NUM
      · rw [if_pos ((etag_dec ntag_num_abs).mpr hn)]
        rw [if_pos hn] at h
        obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hnode := tbl_node_abs hrel.nums hp
        rw [nidx_idxNat hm, hnode]
        cases hpc : p with
        | none => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
        | some r =>
          rw [hpc] at h
          obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have h2 := Result.ok_injective h
          subst h2
          rw [dupId_nidx _ _ hx0]
          rfl
      · rw [if_neg (fun hx => hn ((etag_dec ntag_num_abs).mp hx))]
        rw [if_neg hn] at h
        have h2 := Result.ok_injective h
        subst h2
        rfl

theorem ltables_get_abs {rt lt} (hrel : LTablesRel rt lt)
    {i : arena.handle.LIdx} {o : Option arena.store.LNodeView}
    (h : arena.store.LTables.get rt i = ok o) :
    lt.get (absLIdx i) = o.map absLNodeView := by
  rw [arena.store.LTables.get] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [LTables.get, lidx_tag_abs ht]
  by_cases h0 : t = arena.handle.LTAG_ZERO
  · rw [if_pos ((etag_dec ltag_zero_abs).mpr h0), if_pos h0] at *
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.zeros hp
    rw [lidx_idxNat hm, hnode]
    cases hpc : p with
    | none => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
    | some r => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
  · rw [if_neg (fun hx => h0 ((etag_dec ltag_zero_abs).mp hx))]
    rw [if_neg h0] at h
    by_cases h1 : t = arena.handle.LTAG_SUCC
    · rw [if_pos ((etag_dec ltag_succ_abs).mpr h1)]
      rw [if_pos h1] at h
      obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnode := tbl_node_abs hrel.succs hp
      rw [lidx_idxNat hm, hnode]
      cases hpc : p with
      | none => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
      | some r =>
        rw [hpc] at h
        obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have h2 := Result.ok_injective h
        subst h2
        rw [dupId_lidx _ _ hx0]; rfl
    · rw [if_neg (fun hx => h1 ((etag_dec ltag_succ_abs).mp hx))]
      rw [if_neg h1] at h
      by_cases h2t : t = arena.handle.LTAG_MAX
      · rw [if_pos ((etag_dec ltag_max_abs).mpr h2t)]
        rw [if_pos h2t] at h
        obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hnode := tbl_node_abs hrel.maxs hp
        rw [lidx_idxNat hm, hnode]
        cases hpc : p with
        | none => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
        | some r =>
          rw [hpc] at h
          obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have h2 := Result.ok_injective h
          subst h2
          rw [dupId_lidx _ _ hx0, dupId_lidx _ _ hx1]; rfl
      · rw [if_neg (fun hx => h2t ((etag_dec ltag_max_abs).mp hx))]
        rw [if_neg h2t] at h
        by_cases h3 : t = arena.handle.LTAG_IMAX
        · rw [if_pos ((etag_dec ltag_imax_abs).mpr h3)]
          rw [if_pos h3] at h
          obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hnode := tbl_node_abs hrel.imaxs hp
          rw [lidx_idxNat hm, hnode]
          cases hpc : p with
          | none => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
          | some r =>
            rw [hpc] at h
            obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            have h2 := Result.ok_injective h
            subst h2
            rw [dupId_lidx _ _ hx0, dupId_lidx _ _ hx1]; rfl
        · rw [if_neg (fun hx => h3 ((etag_dec ltag_imax_abs).mp hx))]
          rw [if_neg h3] at h
          by_cases h4 : t = arena.handle.LTAG_PARAM
          · rw [if_pos ((etag_dec ltag_param_abs).mpr h4)]
            rw [if_pos h4] at h
            obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            have hnode := tbl_node_abs hrel.params hp
            rw [lidx_idxNat hm, hnode]
            cases hpc : p with
            | none => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
            | some r =>
              rw [hpc] at h
              obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
              have h2 := Result.ok_injective h
              subst h2
              rw [dupId_nidx _ _ hx0]; rfl
          · rw [if_neg (fun hx => h4 ((etag_dec ltag_param_abs).mp hx))]
            rw [if_neg h4] at h
            have h2 := Result.ok_injective h
            subst h2
            rfl

theorem lstables_get_abs {rt lt} (hrel : LsTablesRel rt lt)
    {i : arena.handle.LsIdx} {o}
    (h : arena.store.LsTables.get rt i = ok o) :
    lt.get (absLsIdx i) = o.map absLsNodeView := by
  rw [arena.store.LsTables.get] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [LsTables.get, lsidx_tag_abs ht]
  by_cases h0 : t = arena.handle.LSTAG_LIST
  · rw [if_pos ((etag_dec lstag_list_abs).mpr h0)]
    rw [if_pos h0] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.lists hp
    rw [lsidx_idxNat hm, hnode]
    cases hpc : p with
    | none => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
    | some r =>
      rw [hpc] at h
      obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := Result.ok_injective h
      subst h2
      simp [absLsNodeView, lidx_vec_dup_eq hx0]
  · rw [if_neg (fun hx => h0 ((etag_dec lstag_list_abs).mp hx))]
    rw [if_neg h0] at h
    have h2 := Result.ok_injective h
    subst h2
    rfl

theorem lstables_get_len_abs {rt lt} (hrel : LsTablesRel rt lt)
    {i : arena.handle.LsIdx} {o}
    (h : arena.store.LsTables.get_len rt i = ok o) :
    lt.getLen (absLsIdx i) = o.map absSz := by
  rw [arena.store.LsTables.get_len] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [LsTables.getLen, lsidx_tag_abs ht]
  by_cases h0 : t = arena.handle.LSTAG_LIST
  · rw [if_pos ((etag_dec lstag_list_abs).mpr h0)]
    rw [if_pos h0] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnode := tbl_node_abs hrel.lists hp
    rw [lsidx_idxNat hm, hnode]
    cases hpc : p with
    | none => rw [hpc] at h; have h2 := Result.ok_injective h; subst h2; rfl
    | some r =>
      rw [hpc] at h
      have h2 := Result.ok_injective h
      subst h2
      simp [absSz, absListNode]
  · rw [if_neg (fun hx => h0 ((etag_dec lstag_list_abs).mp hx))]
    rw [if_neg h0] at h
    have h2 := Result.ok_injective h
    subst h2
    rfl

theorem ltables_der_at_abs {rt lt} (hrel : LTablesRel rt lt)
    {i : arena.handle.LIdx} {d : arena.store.LDer}
    (h : arena.store.LTables.der_at rt i = ok d) :
    derObsL (lt.derAt (absLIdx i)) = derObsL (absLDer d) := by
  rw [arena.store.LTables.der_at] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [LTables.derAt, lidx_tag_abs ht]
  by_cases h0 : t = arena.handle.LTAG_ZERO
  · rw [if_pos ((etag_dec ltag_zero_abs).mpr h0)]
    rw [if_pos h0] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [lidx_idxNat hm]
    exact tbl_der_at_abs hrel.zeros dupId_lder derDefault_lder h
  · rw [if_neg (fun hx => h0 ((etag_dec ltag_zero_abs).mp hx))]
    rw [if_neg h0] at h
    by_cases h1 : t = arena.handle.LTAG_SUCC
    · rw [if_pos ((etag_dec ltag_succ_abs).mpr h1)]
      rw [if_pos h1] at h
      obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [lidx_idxNat hm]
      exact tbl_der_at_abs hrel.succs dupId_lder derDefault_lder h
    · rw [if_neg (fun hx => h1 ((etag_dec ltag_succ_abs).mp hx))]
      rw [if_neg h1] at h
      by_cases h2 : t = arena.handle.LTAG_MAX
      · rw [if_pos ((etag_dec ltag_max_abs).mpr h2)]
        rw [if_pos h2] at h
        obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        rw [lidx_idxNat hm]
        exact tbl_der_at_abs hrel.maxs dupId_lder derDefault_lder h
      · rw [if_neg (fun hx => h2 ((etag_dec ltag_max_abs).mp hx))]
        rw [if_neg h2] at h
        by_cases h3 : t = arena.handle.LTAG_IMAX
        · rw [if_pos ((etag_dec ltag_imax_abs).mpr h3)]
          rw [if_pos h3] at h
          obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          rw [lidx_idxNat hm]
          exact tbl_der_at_abs hrel.imaxs dupId_lder derDefault_lder h
        · rw [if_neg (fun hx => h3 ((etag_dec ltag_imax_abs).mp hx))]
          rw [if_neg h3] at h
          by_cases h4 : t = arena.handle.LTAG_PARAM
          · rw [if_pos ((etag_dec ltag_param_abs).mpr h4)]
            rw [if_pos h4] at h
            obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            rw [lidx_idxNat hm]
            exact tbl_der_at_abs hrel.params dupId_lder derDefault_lder h
          · rw [if_neg (fun hx => h4 ((etag_dec ltag_param_abs).mp hx))]
            rw [if_neg h4] at h
            rw [derDefault_lder _ h]

/-! ## The tier select at the three inner stores -/

theorem nstore_view_abs {pers rs ls} (hrel : NStoreRel pers rs ls)
    {i : arena.handle.NIdx} {o}
    (h : arena.store.NStore.view rs pers i = ok o) :
    ls.view (absNIdx i) = o.map absNNodeView := by
  rw [arena.store.NStore.view] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := nidx_is_persistent_abs hb
  rw [NStore.view]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absNIdx i).isPersistent = true by rw [hb2, hbv])]
    rw [arena.store.NStore.pers_get] at h
    have h3 : arena.store.NTables.get (rPersN pers rs) i = ok o := by
      unfold rPersN
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact ntables_get_abs hrel.perst h3
  · rw [if_neg (show ¬ (absNIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]; exact ntables_get_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 := Result.ok_injective h
      subst h2
      rfl

theorem lstore_view_abs {pers rs ls} (hrel : LStoreRel pers rs ls)
    {i : arena.handle.LIdx} {o}
    (h : arena.store.LStore.view rs pers i = ok o) :
    ls.view (absLIdx i) = o.map absLNodeView := by
  rw [arena.store.LStore.view] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := lidx_is_persistent_abs hb
  rw [LStore.view]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absLIdx i).isPersistent = true by rw [hb2, hbv])]
    rw [arena.store.LStore.pers_get] at h
    have h3 : arena.store.LTables.get (rPersL pers rs) i = ok o := by
      unfold rPersL
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact ltables_get_abs hrel.perst h3
  · rw [if_neg (show ¬ (absLIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]; exact ltables_get_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 := Result.ok_injective h
      subst h2
      rfl

theorem lsstore_view_abs {pers rs ls} (hrel : LsStoreRel pers rs ls)
    {i : arena.handle.LsIdx} {o}
    (h : arena.store.LsStore.view rs pers i = ok o) :
    ls.view (absLsIdx i) = o.map absLsNodeView := by
  rw [arena.store.LsStore.view] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := lsidx_is_persistent_abs hb
  rw [LsStore.view]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absLsIdx i).isPersistent = true by rw [hb2, hbv])]
    rw [arena.store.LsStore.pers_get] at h
    have h3 : arena.store.LsTables.get (rPersLs pers rs) i = ok o := by
      unfold rPersLs
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact lstables_get_abs hrel.perst h3
  · rw [if_neg (show ¬ (absLsIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]; exact lstables_get_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 := Result.ok_injective h
      subst h2
      rfl

theorem lsstore_view_len_abs {pers rs ls} (hrel : LsStoreRel pers rs ls)
    {i : arena.handle.LsIdx} {o}
    (h : arena.store.LsStore.view_len rs pers i = ok o) :
    ls.viewLen (absLsIdx i) = o.map absSz := by
  rw [arena.store.LsStore.view_len] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := lsidx_is_persistent_abs hb
  rw [LsStore.viewLen]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absLsIdx i).isPersistent = true by rw [hb2, hbv]),
      LsStore.persGetLen]
    rw [arena.store.LsStore.pers_get_len] at h
    have h3 : arena.store.LsTables.get_len (rPersLs pers rs) i = ok o := by
      unfold rPersLs
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact lstables_get_len_abs hrel.perst h3
  · rw [if_neg (show ¬ (absLsIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]; exact lstables_get_len_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 := Result.ok_injective h
      subst h2
      rfl

theorem lstore_derived_abs {pers rs ls} (hrel : LStoreRel pers rs ls)
    {i : arena.handle.LIdx} {d}
    (h : arena.store.LStore.derived rs pers i = ok d) :
    derObsL (ls.derived (absLIdx i)) = derObsL (absLDer d) := by
  rw [arena.store.LStore.derived] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := lidx_is_persistent_abs hb
  rw [LStore.derived]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absLIdx i).isPersistent = true by rw [hb2, hbv])]
    rw [arena.store.LStore.pers_der_at] at h
    have h3 : arena.store.LTables.der_at (rPersL pers rs) i = ok d := by
      unfold rPersL
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact ltables_der_at_abs hrel.perst h3
  · rw [if_neg (show ¬ (absLIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]; exact ltables_der_at_abs hrel.scrt h
    · rw [if_neg hs]
      rw [derDefault_lder _ h]

/-! ## The five monad readers -/

theorem derived_l_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.LIdx} {d : arena.store.LDer}
    (hrun : arena.monad.derived_l pers st h = ok d) :
    SimRO absLDer derObsL lst d (Arena.derivedL (absLIdx h)) := by
  rw [arena.monad.derived_l, arena.store.EStore.lder] at hrun
  obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ls] at hl
  have hl2 : l = st.store.lss.ls := (Result.ok_injective hl).symm
  subst hl2
  exact SimRO.mk rfl (by
    rw [EStore.lder, EStore.ls]
    exact lstore_derived_abs hrel.store.lss.lvl hrun)

theorem view_ls_len_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.view_ls_len pers st h = ok o) :
    SimR (Option.map absSz) lst o (Arena.viewLsLen (absLsIdx h)) := by
  rw [arena.monad.view_ls_len] at hrun
  obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ls_s] at hl
  have hl2 : l = st.store.lss := (Result.ok_injective hl).symm
  subst hl2
  show (Arena.viewLsLen (absLsIdx h)).run lst = _
  rw [show (Arena.viewLsLen (absLsIdx h)).run lst
        = .ok (lst.store.lss.viewLen (absLsIdx h), lst) from rfl,
    lsstore_view_len_abs hrel.store.lss hrun]

theorem view_n_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.NIdx} {o}
    (hrun : arena.monad.view_n pers st h = ok o) :
    AOut absNNodeView (fun _ => True) pers lst o st
      ((Arena.viewN (absNIdx h)).run lst) := by
  rw [arena.monad.view_n] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ns] at hn
  have hn2 : n = st.store.lss.ls.ns := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hview := nstore_view_abs hrel.store.lss.lvl.ns hv
  have hrunl : (Arena.viewN (absNIdx h)).run lst
      = match lst.store.ns.view (absNIdx h) with
        | some x => Except.ok (x, lst)
        | none => Except.error (.internal "arena: dangling name handle") := by
    show (match lst.store.ns.view (absNIdx h) with
          | some v => (pure v : AM _)
          | none => Arena.fail (.internal "arena: dangling name handle")).run lst = _
    cases lst.store.ns.view (absNIdx h) <;> rfl
  cases hvc : v with
  | none =>
    rw [hvc] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := fail_run hrun
    subst ho
    rw [hvc] at hview
    refine AOut.err ?_
    rw [hrunl, EStore.ns, hview]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    rw [hvc] at hview
    refine AOut.ok (lst' := lst) ?_ hrel hinv (Ext.refl _) trivial
    rw [hrunl, EStore.ns, hview]
    rfl

theorem view_l_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LIdx} {o}
    (hrun : arena.monad.view_l pers st h = ok o) :
    AOut absLNodeView (fun _ => True) pers lst o st
      ((Arena.viewL (absLIdx h)).run lst) := by
  rw [arena.monad.view_l] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ls] at hn
  have hn2 : n = st.store.lss.ls := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hview := lstore_view_abs hrel.store.lss.lvl hv
  have hrunl : (Arena.viewL (absLIdx h)).run lst
      = match lst.store.ls.view (absLIdx h) with
        | some x => Except.ok (x, lst)
        | none => Except.error (.internal "arena: dangling level handle") := by
    show (match lst.store.ls.view (absLIdx h) with
          | some v => (pure v : AM _)
          | none => Arena.fail (.internal "arena: dangling level handle")).run lst = _
    cases lst.store.ls.view (absLIdx h) <;> rfl
  cases hvc : v with
  | none =>
    rw [hvc] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := fail_run hrun
    subst ho
    rw [hvc] at hview
    refine AOut.err ?_
    rw [hrunl, EStore.ls, hview]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    rw [hvc] at hview
    refine AOut.ok (lst' := lst) ?_ hrel hinv (Ext.refl _) trivial
    rw [hrunl, EStore.ls, hview]
    rfl

theorem view_ls_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.view_ls pers st h = ok o) :
    AOut absLsNodeView (fun _ => True) pers lst o st
      ((Arena.viewLs (absLsIdx h)).run lst) := by
  rw [arena.monad.view_ls] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ls_s] at hn
  have hn2 : n = st.store.lss := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hview := lsstore_view_abs hrel.store.lss hv
  have hrunl : (Arena.viewLs (absLsIdx h)).run lst
      = match lst.store.lss.view (absLsIdx h) with
        | some x => Except.ok (x, lst)
        | none => Except.error (.internal "arena: dangling level-list handle") := by
    show (match lst.store.lss.view (absLsIdx h) with
          | some v => (pure v : AM _)
          | none => Arena.fail (.internal "arena: dangling level-list handle")).run lst = _
    cases lst.store.lss.view (absLsIdx h) <;> rfl
  cases hvc : v with
  | none =>
    rw [hvc] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := fail_run hrun
    subst ho
    rw [hvc] at hview
    refine AOut.err ?_
    rw [hrunl, hview]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    rw [hvc] at hview
    refine AOut.ok (lst' := lst) ?_ hrel hinv (Ext.refl _) trivial
    rw [hrunl, hview]
    rfl

/-- `arena::monad::read_name` against `Arena.readName` — the readback IS
`denoteN`, so this is an equation and not a simulation (DESIGN §8.3 lesson
4). -/
theorem read_name_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.NIdx} {o}
    (hrun : arena.monad.read_name pers st h = ok o) :
    AOut ConRon.Refine.absName (fun _ => True) pers lst o st
      ((Arena.readName (absNIdx h)).run lst) := by
  sorry

/-- `arena::monad::read_level` against `Arena.readLevel`. -/
theorem read_level_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.LIdx} {o}
    (hrun : arena.monad.read_level pers st h = ok o) :
    AOut ConRon.Refine.absLevel (fun _ => True) pers lst o st
      ((Arena.readLevel (absLIdx h)).run lst) := by
  sorry

/-- `arena::monad::read_levels` against `Arena.readLevels`. -/
theorem read_levels_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.read_levels pers st h = ok o) :
    AOut ConRon.Refine.absLevels (fun _ => True) pers lst o st
      ((Arena.readLevels (absLsIdx h)).run lst) := by
  sorry

/-- `arena::monad::read_names` against `Arena.readNames`. -/
theorem read_names_run {pers st lst} (hrel : AStateRel pers st lst)
    {ks : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.monad.read_names pers st ks = ok o) :
    AOut ConRon.Refine.absNames (fun _ => True) pers lst o st
      ((Arena.readNames (ks.val.map absNIdx)).run lst) := by
  sorry

/-! ### The memoised readbacks (task #97-P6-13)

`read_level_m` / `read_name_m` / `read_levels_m` probe the per-declaration
readback cache and INSERT on a miss, so they thread the state: `Sim`, not
`SimR`.  What their proof needs beyond the probe is the insert half — the same
`HashMap2.Rel_insert_wf` the memo writes need. -/

/-- `arena::monad::read_level_m` against `Arena.readLevelM`. -/
theorem read_level_m_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LIdx} {o}
    (hrun : arena.monad.read_level_m pers st h = ok o) :
    Sim ConRon.Refine.absLevel (fun _ => True) pers lst o (Arena.readLevelM (absLIdx h)) := by
  sorry

/-- `arena::monad::read_name_m` against `Arena.readNameM`. -/
theorem read_name_m_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.NIdx} {o}
    (hrun : arena.monad.read_name_m pers st h = ok o) :
    Sim ConRon.Refine.absName (fun _ => True) pers lst o (Arena.readNameM (absNIdx h)) := by
  sorry

/-- `arena::monad::read_levels_m` against `Arena.readLevelsM`. -/
theorem read_levels_m_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.read_levels_m pers st h = ok o) :
    Sim ConRon.Refine.absLevels (fun _ => True) pers lst o (Arena.readLevelsM (absLsIdx h)) := by
  sorry

/-- `arena::monad::read_names_m` against `Arena.readNamesM`. -/
theorem read_names_m_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {ks : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.monad.read_names_m pers st ks = ok o) :
    Sim ConRon.Refine.absNames (fun _ => True) pers lst o
      (Arena.readNamesM (ks.val.map absNIdx)) := by
  sorry

/-! ### `intern`: the probe, the push and the handle

The expensive floor this task did not build.  `EStore.intern` probes the
persistent cons table, then the scratch one, then appends to the tier the
state is in; the twin does the same, clause for clause
(`Arena/Store.lean`'s `EStore.intern`), and the capacity test that keeps it
total sits at the monadic wrapper on both sides (`Arena/Monad.lean`'s
`internE`, `arena::monad::intern_e`) — DESIGN §8.3's "the Rust raises `Native`
at the limit, the Lean `throw`s the same kind".

What each of these needs, once: `tbl_find_abs` (have it), `HashMap2`'s
`Rel_insert_wf` / `insert_refines_wf` on the cons table (have them, in
`Refine/HashMap2WF.lean`), `Array.push` on the node and derived columns
against the Rust's one `Vec::push` of a pair (`Refine/Abs.lean`'s
`push_new_val`), and `Idx.mk tag tier (UInt32.ofNat size)` against
`Idx::pack(tag, tier, rows.len() as u32)` — which `Refine2/AbsStore.lean`'s
module note shows needs NO capacity hypothesis. -/

/-- `arena::monad::intern_e` against `Arena.internE`. -/
theorem intern_e_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.ENodeView) {o}
    (hrun : arena.monad.intern_e pers st v = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internE (absENodeView v)) := by
  sorry

/-! ### `intern`, the `bvar` constructor: the pattern the other twenty-four follow

Written out once, end to end, so that the remaining twenty-four are the same
proof at another array.  Its shape is:

1. the persistent cons probe under the `shared_on` select (`rPersE` again,
   and `tbl_find_abs` at that tier's table);
2. the twin's `intern` at a non-binder view is `internAt` at the datum handle
   `0`, so the two `match`es on the probe line up clause for clause;
3. a persistent HIT returns the handle and leaves both stores alone — the
   port's `{ self with pers := e, shared_on := b }` is `self` by structure
   eta;
4. a MISS in the scratch tier is `tbl_find_slot_abs`, whose first component
   re-establishes the relation for the table `find_slot` handed back;
5. a miss in both is `Tbl::full` — whose `true` arm is `Native` and claims
   nothing — then `der_of_bvar`, `size`, the `u32` cast, `pack` and
   `push_at`, which is `tbl_find_slot_abs`'s last component;
6. and the persistent-append arm, which **needs finding 8**: the port declines
   a frozen tier with `Internal` where the twin appends, so the hypothesis
   `shared_on → scratch_on` is what makes that arm unreachable.

`intern_e_bvar_run` then wraps it in `Arena.internE`'s capacity test, and
**needs finding 9**: the port tests `Tbl::full` only when it is about to
append, where the twin's `internE` tests `sizeOf` before probing, so on a
cons HIT at a full array the port answers `Ok` and the twin throws `native`.
`hcap` is that hypothesis; the proper fix is a one-line twin change (test
after the probe, as the port does), and it belongs in the next twin
catch-up. -/

/-! ## `der_of_*`, the `bvar` arm -/

/-- `arena::store::EStore.der_of_bvar` against `EStore.derOfBVar`, UP TO the
hash: `pack_bits` on the port's side, `bvarOfData_pack` and its two siblings
on the twin's, and `derObsE_absU64` is the bridge. -/
theorem der_of_bvar_obs {rs : arena.store.EStore} {ls : EStore} {i : Std.U64}
    {d : Std.U64} (h : arena.store.EStore.der_of_bvar rs i = ok d) :
    derObsE (ls.derOfBVar (absU i)) = derObsE (absU64 d) := by
  rw [arena.store.EStore.der_of_bvar] at h
  obtain ⟨i1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hh, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hi3v := ConRon.Refine.Expr.sat_succ_val hi3
  have hb : i3.val < 32768 := by rw [hi3v]; simp [ConLeche.satRange]
  have hf : (0#u64 : Std.U64).val < 32768 := by simp
  obtain ⟨hbv, hfv, hlv⟩ := ConRon.Refine.Expr.pack_bits hb hf h
  rw [EStore.derOfBVar, derObsE_absU64, derObsE, hbv, hfv, hlv]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show ConLeche.bvarOfData _ = _
    rw [ConLeche.bvarOfData_pack _ _ _ _ (ConLeche.satSucc_lt _) (by decide),
      ConLeche.satSucc, hi3v]
  · show ConLeche.fvarOfData _ = _
    rw [ConLeche.fvarOfData_pack _ _ _ _ (ConLeche.satSucc_lt _) (by decide)]
    rfl
  · show ConLeche.lpOfData _ = _
    rw [ConLeche.lpOfData_pack _ _ _ _ (ConLeche.satSucc_lt _) (by decide)]
    simp

theorem tier_s_abs : absU32 arena.handle.TIER_S = Idx.tierS := by
  rw [arena.handle.TIER_S]; rfl
theorem tier_p_abs : absU32 arena.handle.TIER_P = Idx.tierP := by
  rw [arena.handle.TIER_P]; rfl

theorem dupId_bvarnode :
    DupId arena.store.BVarNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm

theorem absBVarNode_inj :
    ∀ a b : arena.store.BVarNode, BVarNodeWF a → BVarNodeWF b →
      absBVarNode a = absBVarNode b → a = b := by
  intro a b _ _ h
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b
  have hx : x.val = y.val := congrArg BVarNode.i h
  simp [UScalar.eq_imp _ _ hx]

theorem estore_intern_bvar_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {i : Std.U64} {r} {rs'}
    (h : arena.store.EStore.intern_bvar rs pers i = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.bvar (absU i))).2 ∧
        StoreRel pers rs' (ls.intern (.bvar (absU i))).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_bvar] at h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, bb, hit⟩ := q
  -- the persistent probe, under the `shared_on` select
  have hE : e = rs.pers ∧ bb = rs.shared_on ∧
      ls.pers.bvars.find? ⟨absU i⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hs <;>
      obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
      obtain ⟨h1, h2, h3⟩ := hq
    · refine ⟨h1.symm, by rw [← h2, hs], ?_⟩
      have := tbl_find_abs hrel.perst.bvars hinv.perst.bvars bvar_eq2 dupId_eidx
        (P := BVarNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
      rw [← h3]; exact this
    · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      have := tbl_find_abs hrel.perst.bvars hinv.perst.bvars bvar_eq2 dupId_eidx
        (P := BVarNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
      rw [← h3]; exact this
  obtain ⟨hE1, hE2, hE3⟩ := hE
  subst hE1; subst hE2
  -- the twin's `intern` at a non-binder view is `internAt` at handle 0
  have htw : ls.intern (.bvar (absU i)) = ls.internAt (.bvar (absU i)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  have hfind : ls.pers.find? (ENodeView.bvar (absU i)) (Idx.ofWord 0)
      = ls.pers.bvars.find? ⟨absU i⟩ := rfl
  rw [hfind, hE3]
  cases hitc : hit with
  | some hp =>
    rw [hitc] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv⟩
    · intro ee hbad; simp at hbad
  | none =>
    rw [hitc] at h
    simp only [Option.map_none]
    rw [hrel.scratchOn]
    split at h <;> rename_i hsc
    · -- the scratch tier
      rw [if_pos hsc]
      obtain ⟨p2, hfs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨⟨slot, o⟩, t⟩ := p2
      obtain ⟨hrelT, hinvT, hfindT, hpushT⟩ :=
        tbl_find_slot_abs hrel.scrt.bvars hinv.scrt.bvars bvar_eq2 dupId_bvarnode
          dupId_eidx absBVarNode_inj (P := BVarNodeWF) trivial hfs
      have hfind2 : ls.scr.find? (ENodeView.bvar (absU i)) (Idx.ofWord 0)
          = ls.scr.bvars.find? ⟨absU i⟩ := rfl
      simp only [absBVarNode] at hfindT
      rw [hfind2, hfindT]
      cases hoc : o with
      | some hs =>
        rw [hoc] at h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs'⟩ := he
        subst hr; subst hs'
        refine ⟨?_, ?_⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨rfl, { hrel with scrt := { hrel.scrt with bvars := hrelT } },
            { hinv with scrt := { hinv.scrt with bvars := hinvT } }⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · -- the array is full: `Native`, which claims nothing
          obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, -⟩ := he
          subst hr
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl⟩
        · -- the append
          obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          rw [dupId_eidx _ _ he1] at h
          obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs'⟩ := he
          subst hr; subst hs'
          have hhandle : absEIdx hnew
              = Idx.mk ETag.bvar Idx.tierS (UInt32.ofNat ls.scr.bvars.size) := by
            rw [eidx_pack_abs hpk, etag_bvar_abs, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d (ls.derOfBVar (absU i)) (der_of_bvar_obs (ls := ls) hd)
              hnew t1 ht1
          simp only [absBVarNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with bvars := hrel1 }, rfl⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with bvars := hinv1 }⟩⟩
    · -- the persistent tier
      rw [if_neg hsc]
      have hsh : rs.shared_on = false := by
        by_contra hc
        exact hsc (hfrozen (by simpa using hc))
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, -⟩ := he
        subst hr
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl⟩
      · obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        rw [dupId_eidx _ _ he1] at h
        obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs'⟩ := he
        subst hr; subst hs'
        have hrelP : TblRel BVarNodeWF absBVarNode absEIdx absU64 derObsE
            rs.pers.bvars ls.pers.bvars := by rw [← hpersE]; exact hrel.perst.bvars
        have hinvP : TblInv
            arena.store.BVarNode.Insts.Con_ron_coreRonHashmapHashable
            BVarNodeWF rs.pers.bvars := by
          rw [← hpersE]; exact hinv.perst.bvars
        have hhandle : absEIdx hnew
            = Idx.mk ETag.bvar Idx.tierP (UInt32.ofNat ls.pers.bvars.size) := by
          rw [eidx_pack_abs hpk, etag_bvar_abs, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP bvar_eq2 dupId_bvarnode absBVarNode_inj
            (P := BVarNodeWF) trivial (dl := ls.derOfBVar (absU i))
            (der_of_bvar_obs (ls := ls) hd) ht1
        simp only [absBVarNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        exact ⟨hhandle, ⟨hrel.lss, { hrelPerst with bvars := hrel1 }, hrel.scrt, rfl⟩,
          ⟨hinv.lss, { hinvPerst with bvars := hinv1 }, hinv.scrt⟩⟩

/-! ## `arena::monad::intern_e_bvar` -/

/-- `Arena.internE`'s run at a view whose array is below the cap and which
needs no binder datum. -/
theorem internE_run_of_cap {lst : AState} {v : ENodeView}
    (hbm : EStore.eViewNeedsBM v = false)
    (hcap : (if lst.store.scratchOn then lst.store.scr.sizeOf v
              else lst.store.pers.sizeOf v) < Idx.idxCap) :
    (Arena.internE v).run lst
      = .ok ((lst.store.intern v).2,
             { lst with store := (lst.store.intern v).1 }) := by
  rw [Arena.internE]
  simp only [hbm, Bool.not_false, Bool.true_or, Bool.and_true, decide_eq_true_eq]
  show StateT.run
      (if (if lst.store.scratchOn then lst.store.scr.sizeOf v
            else lst.store.pers.sizeOf v) < Idx.idxCap then
         ((do set ({ lst with store := (lst.store.intern v).1 } : AState)
              pure (lst.store.intern v).2) : AM EIdx)
       else Arena.fail (.native "arena: expression constructor array full")) lst = _
  rw [if_pos hcap]
  rfl

theorem intern_e_bvar_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (i : Std.U64)
    (hcap : (if lst.store.scratchOn
              then lst.store.scr.sizeOf (.bvar (absU i))
              else lst.store.pers.sizeOf (.bvar (absU i))) < Idx.idxCap)
    {o}
    (hrun : arena.monad.intern_e_bvar pers st i = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internBVarE (absU i)) := by
  rw [arena.monad.intern_e_bvar] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_bvar_abs (ls := lst.store) hrel.store hinv.store hfrozen hp
  show AOut absEIdx (fun _ => True) pers lst r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv'⟩ := hok hh hr
    refine AOut.ok
      (lst' := { lst with store := (lst.store.intern (.bvar (absU i))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
      (EStore.intern_ext _ _) trivial
    rw [Arena.internBVarE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut.err (AErrSim.of_none (herr ee hr))


/-- `arena::monad::intern_e_fvar` against `Arena.internFVarE`. -/
theorem intern_e_fvar_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (idx : Std.U64) (ty : arena.handle.EIdx) {o}
    (hrun : arena.monad.intern_e_fvar pers st idx ty = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internFVarE (absU idx) (absEIdx ty)) := by
  sorry

/-- `arena::monad::intern_e_sort` against `Arena.internSortE`. -/
theorem intern_e_sort_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (u : arena.handle.LIdx) {o}
    (hrun : arena.monad.intern_e_sort pers st u = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internSortE (absLIdx u)) := by
  sorry

/-- `arena::monad::intern_e_const` against `Arena.internConstE`. -/
theorem intern_e_const_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (us : arena.handle.LsIdx) {o}
    (hrun : arena.monad.intern_e_const pers st n us = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internConstE (absNIdx n) (absLsIdx us)) := by
  sorry

/-- `arena::monad::intern_e_app` against `Arena.internAppE`. -/
theorem intern_e_app_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (f : arena.handle.EIdx) (a : arena.handle.EIdx) {o}
    (hrun : arena.monad.intern_e_app pers st f a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internAppE (absEIdx f) (absEIdx a)) := by
  sorry

/-- `arena::monad::intern_e_lam` against `Arena.internLamE`. -/
theorem intern_e_lam_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) {o}
    (hrun : arena.monad.intern_e_lam pers st ty b m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internLamE (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)) := by
  sorry

/-- `arena::monad::intern_e_forall_e` against `Arena.internForallEE`. -/
theorem intern_e_forall_e_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (m : kernel.expr.BinderMeta) {o}
    (hrun : arena.monad.intern_e_forall_e pers st ty b m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internForallEE (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)) := by
  sorry

/-- `arena::monad::intern_e_lam_i` against `Arena.internLamIE`. -/
theorem intern_e_lam_i_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (mi : arena.handle.BMIdx) {o}
    (hrun : arena.monad.intern_e_lam_i pers st ty b mi = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internLamIE (absEIdx ty) (absEIdx b) (absBMIdx mi)) := by
  sorry

/-- `arena::monad::intern_e_forall_e_i` against `Arena.internForallEIE`. -/
theorem intern_e_forall_e_i_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (mi : arena.handle.BMIdx) {o}
    (hrun : arena.monad.intern_e_forall_e_i pers st ty b mi = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internForallEIE (absEIdx ty) (absEIdx b) (absBMIdx mi)) := by
  sorry

/-- `arena::monad::intern_e_bind_i` against `Arena.internBindIE`. -/
theorem intern_e_bind_i_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (tag : Std.U32) (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (mi : arena.handle.BMIdx) {o}
    (hrun : arena.monad.intern_e_bind_i pers st tag ty b mi = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internBindIE (absU32 tag) (absEIdx ty) (absEIdx b) (absBMIdx mi)) := by
  sorry

/-- `arena::monad::intern_e_let_e` against `Arena.internLetEE`. -/
theorem intern_e_let_e_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (ty : arena.handle.EIdx) (val : arena.handle.EIdx) (b : arena.handle.EIdx) {o}
    (hrun : arena.monad.intern_e_let_e pers st ty val b = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internLetEE (absEIdx ty) (absEIdx val) (absEIdx b)) := by
  sorry

/-- `arena::monad::intern_e_lit` against `Arena.internLitE`. -/
theorem intern_e_lit_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (l : kernel.expr.Literal) {o}
    (hrun : arena.monad.intern_e_lit pers st l = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internLitE (ConRon.Refine.absLiteral l)) := by
  sorry

/-- `arena::monad::intern_e_proj` against `Arena.internProjE`. -/
theorem intern_e_proj_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (i : Std.U64) (e : arena.handle.EIdx) {o}
    (hrun : arena.monad.intern_e_proj pers st n i e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internProjE (absNIdx n) (absU i) (absEIdx e)) := by
  sorry

/-- `arena::monad::intern_n_node` against `Arena.internNNode`. -/
theorem intern_n_node_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.NNodeView) {o}
    (hrun : arena.monad.intern_n_node pers st v = ok o) :
    Sim absNIdx (fun _ => True) pers lst o (Arena.internNNode (absNNodeView v)) := by
  sorry

/-- `arena::monad::intern_l_node` against `Arena.internLNode`. -/
theorem intern_l_node_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.LNodeView) {o}
    (hrun : arena.monad.intern_l_node pers st v = ok o) :
    Sim absLIdx (fun _ => True) pers lst o (Arena.internLNode (absLNodeView v)) := by
  sorry

/-- `arena::monad::intern_ls_node` against `Arena.internLsNode`. -/
theorem intern_ls_node_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (v : alloc.vec.Vec arena.handle.LIdx) {o}
    (hrun : arena.monad.intern_ls_node pers st v = ok o) :
    Sim absLsIdx (fun _ => True) pers lst o (Arena.internLsNode (absLsNodeView v)) := by
  sorry

/-- `arena::monad::intern_persistent_e` against `Arena.internPersistentE`. -/
theorem intern_persistent_e_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.ENodeView) {o}
    (hrun : arena.monad.intern_persistent_e pers st v = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internPersistentE (absENodeView v)) := by
  sorry

/-- `arena::monad::intern_persistent_n` against `Arena.internPersistentN`. -/
theorem intern_persistent_n_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.NNodeView) {o}
    (hrun : arena.monad.intern_persistent_n pers st v = ok o) :
    Sim absNIdx (fun _ => True) pers lst o (Arena.internPersistentN (absNNodeView v)) := by
  sorry

/-- `arena::monad::intern_persistent_l` against `Arena.internPersistentL`. -/
theorem intern_persistent_l_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.LNodeView) {o}
    (hrun : arena.monad.intern_persistent_l pers st v = ok o) :
    Sim absLIdx (fun _ => True) pers lst o (Arena.internPersistentL (absLNodeView v)) := by
  sorry

/-- `arena::monad::intern_persistent_ls` against `Arena.internPersistentLs`. -/
theorem intern_persistent_ls_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) (v : alloc.vec.Vec arena.handle.LIdx) {o}
    (hrun : arena.monad.intern_persistent_ls pers st v = ok o) :
    Sim absLsIdx (fun _ => True) pers lst o (Arena.internPersistentLs (absLsNodeView v)) := by
  sorry

/-- `arena::monad::intern_name` against `Arena.internName` — a structural
walk over a transient `Name`, so no fuel (DESIGN §8.3: "the tree is a value,
not a DAG"). -/
theorem intern_name_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {n : kernel.name.Name} {o}
    (hwf : ConRon.Refine.NameWF n)
    (hrun : arena.monad.intern_name pers st n = ok o) :
    Sim absNIdx (fun _ => True) pers lst o
      (Arena.internName (ConRon.Refine.absName n)) := by
  sorry

/-- `arena::monad::intern_level` against `Arena.internLevel`. -/
theorem intern_level_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {l : kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelWF l)
    (hrun : arena.monad.intern_level pers st l = ok o) :
    Sim absLIdx (fun _ => True) pers lst o
      (Arena.internLevel (ConRon.Refine.absLevel l)) := by
  sorry

/-- `arena::monad::intern_level_list` against `Arena.internLevelList`. -/
theorem intern_level_list_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {us : alloc.vec.Vec kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelsWF us)
    (hrun : arena.monad.intern_level_list pers st us = ok o) :
    Sim (fun v : alloc.vec.Vec arena.handle.LIdx => v.val.map absLIdx)
      (fun _ => True) pers lst o
      (Arena.internLevelList (ConRon.Refine.absLevels us)) := by
  sorry

/-- `arena::monad::intern_levels` against `Arena.internLevels`. -/
theorem intern_levels_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {us : alloc.vec.Vec kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelsWF us)
    (hrun : arena.monad.intern_levels pers st us = ok o) :
    Sim absLsIdx (fun _ => True) pers lst o
      (Arena.internLevels (ConRon.Refine.absLevels us)) := by
  sorry

/-! ### The memo writes and the per-call clears

`SimS` (`Refine2/Shape.lean`): a Rust `Result AState` with no inner `Result`,
so no error arm.  Each write is `HashMap2.Rel_insert_wf` at one table and
`AStateRel`'s other twenty-six clauses carried across unchanged — which is
where the record shape of `MemosRel`/`CachesRel` pays for itself.  Each clear
is `reset_map`, whose VALUE is `HashMap2` empty (task #97-P6-1: the bucket
array is kept, the entries are not), against the twin's `∅`.

**The other twenty-six clauses cost nothing to carry**, and that is the one
thing worth naming here: `{ hrel with memos := { hrel.memos with inst1C := h1 } }`
is a structure-instance UPDATE on the proof, and it typechecks because
`{ rm with inst1_c := hm }.inst_l_c` reduces to `rm.inst_l_c` by iota — so the
twelve untouched `RelOn`s and the twelve untouched `Inv`s are reused, not
re-proved.  Each lemma is therefore nine lines and the same nine lines
twenty-four times. -/

/-! ## Injectivity of the memo key abstractions -/

theorem absU_inj_u64 : Function.Injective (fun x : Std.U64 => absU x) := by
  intro a b h; exact UScalar.eq_imp _ _ h

theorem absEIdxNat_inj : Function.Injective absEIdxNat := by
  intro a b h
  obtain ⟨ha, da⟩ := a; obtain ⟨hb, db⟩ := b
  simp only [absEIdxNat, Prod.mk.injEq] at h
  have h1 := absEIdx_inj h.1
  have h2 := absU_inj_u64 h.2
  simp [h1, h2]

/-! ## One memo table: the insert and the clear -/

theorem memo_insert_step {K K' V V' : Type} [DecidableEq K] [BEq K'] [Hashable K']
    [LawfulBEq K'] [LawfulHashable K']
    {HashableInst : ron.hashmap.Hashable K} {Eq2Inst : ron.hashmap.Eq2 K}
    {m : ron.hashmap2.HashMap2 K V} {s : _root_.Std.HashMap K' V'}
    {absK : K → K'} {absV : V → V'}
    (heq : Eq2Fwd Eq2Inst (fun _ => True)) (hinj : Function.Injective absK)
    (hinv : Inv HashableInst m)
    (hrel : RelOn (fun _ => True) m s absK absV)
    {key : K} {value : V} {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.insert HashableInst Eq2Inst m key value
          = ok (old, m')) :
    RelOn (fun _ => True) m' (s.insert (absK key) (absV value)) absK absV ∧
      Inv HashableInst m' :=
  ⟨(ConRon.Refine.HashMap2.Rel_insert_wf heq (fun _ _ _ _ hab => hinj hab) hinv
      ConRon.Refine.HashMap2.KeysOk_true hrel trivial h).1,
   (ConRon.Refine.HashMap2.insert_refines_wf heq hinv
      ConRon.Refine.HashMap2.KeysOk_true trivial h).1⟩

theorem memo_clear_step {K K' V V' : Type} [DecidableEq K] [BEq K'] [Hashable K']
    {HashableInst : ron.hashmap.Hashable K}
    {m : ron.hashmap2.HashMap2 K V} {absK : K → K'} {absV : V → V'}
    (hinv : Inv HashableInst m) {m' : ron.hashmap2.HashMap2 K V}
    (h : arena.core_state.reset_map m = ok m') :
    RelOn (fun _ => True) m' (∅ : _root_.Std.HashMap K' V') absK absV ∧
      Inv HashableInst m' := by
  rw [arena.core_state.reset_map] at h
  obtain ⟨hinv', -, hnone⟩ := ConRon.Refine.HashMap2.clear_fit_refines hinv h
  exact ⟨ConRon.Refine.HashMap2.RelOn_empty hnone, hinv'⟩

/-! ## The thirteen memo writes and the eleven clears -/

/-- `arena::monad::inst1_set` against `Arena.inst1Set`. -/
theorem inst1_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst1_set st k r = ok st') :
    SimS pers lst st' (Arena.inst1Set (absEIdxNat k) (absEIdx r)) := by
  rw [arena.monad.inst1_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with inst1_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.inst1C
    hrel.memos.inst1C hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with inst1C := h1 } }
    { hinv with memos := { hinv.memos with inst1C := h2 } } (Ext.refl _)

/-- `arena::monad::inst_l_set` against `Arena.instLSet`. -/
theorem inst_l_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst_l_set st k r = ok st') :
    SimS pers lst st' (Arena.instLSet (absEIdxNat k) (absEIdx r)) := by
  rw [arena.monad.inst_l_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with inst_l_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.instLC
    hrel.memos.instLC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with instLC := h1 } }
    { hinv with memos := { hinv.memos with instLC := h2 } } (Ext.refl _)

/-- `arena::monad::lift_set` against `Arena.liftSet`. -/
theorem lift_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.lift_set st k r = ok st') :
    SimS pers lst st' (Arena.liftSet (absEIdxNat k) (absEIdx r)) := by
  rw [arena.monad.lift_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with lift_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.liftC
    hrel.memos.liftC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with liftC := h1 } }
    { hinv with memos := { hinv.memos with liftC := h2 } } (Ext.refl _)

/-- `arena::monad::reset_set` against `Arena.resetSet`. -/
theorem reset_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.reset_set st k r = ok st') :
    SimS pers lst st' (Arena.resetSet (absEIdxNat k) (absEIdx r)) := by
  rw [arena.monad.reset_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with reset_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.resetC
    hrel.memos.resetC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with resetC := h1 } }
    { hinv with memos := { hinv.memos with resetC := h2 } } (Ext.refl _)

/-- `arena::monad::rename_set` against `Arena.renameSet`. -/
theorem rename_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.rename_set st k r = ok st') :
    SimS pers lst st' (Arena.renameSet (absEIdxNat k) (absEIdx r)) := by
  rw [arena.monad.rename_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with rename_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.renameC
    hrel.memos.renameC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with renameC := h1 } }
    { hinv with memos := { hinv.memos with renameC := h2 } } (Ext.refl _)

/-- `arena::monad::abs1_set` against `Arena.abs1Set`. -/
theorem abs1_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.abs1_set st k r = ok st') :
    SimS pers lst st' (Arena.abs1Set (absEIdxNat k) (absEIdx r)) := by
  rw [arena.monad.abs1_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with abs1_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.abs1C
    hrel.memos.abs1C hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with abs1C := h1 } }
    { hinv with memos := { hinv.memos with abs1C := h2 } } (Ext.refl _)

/-- `arena::monad::lower_set` against `Arena.lowerSet`. -/
theorem lower_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.lower_set st k r = ok st') :
    SimS pers lst st' (Arena.lowerSet (absEIdxNat k) (absEIdx r)) := by
  rw [arena.monad.lower_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with lower_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.lowerC
    hrel.memos.lowerC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with lowerC := h1 } }
    { hinv with memos := { hinv.memos with lowerC := h2 } } (Ext.refl _)

/-- `arena::monad::inst1_l_set` against `Arena.inst1LSet`. -/
theorem inst1_l_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst1_l_set st k r = ok st') :
    SimS pers lst st' (Arena.inst1LSet (absEIdxNat k) (absEIdx r)) := by
  rw [arena.monad.inst1_l_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with inst1_l_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.inst1LC
    hrel.memos.inst1LC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with inst1LC := h1 } }
    { hinv with memos := { hinv.memos with inst1LC := h2 } } (Ext.refl _)

/-- `arena::monad::inst_lp_set` against `Arena.instLPSet`. -/
theorem inst_lp_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst_lp_set st k r = ok st') :
    SimS pers lst st' (Arena.instLPSet (absEIdxNat k) (absEIdx r)) := by
  rw [arena.monad.inst_lp_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_eidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with inst_lp_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxNat_eq2 absEIdxNat_inj hinv.memos.instLPC
    hrel.memos.instLPC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with instLPC := h1 } }
    { hinv with memos := { hinv.memos with instLPC := h2 } } (Ext.refl _)

/-- `arena::monad::bvar_b_set` against `Arena.bvarBSet`. -/
theorem bvar_b_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.EIdx} {r : Std.U64} {st'}
    (hrun : arena.monad.bvar_b_set st k r = ok st') :
    SimS pers lst st' (Arena.bvarBSet (absEIdx k) (absU r)) := by
  rw [arena.monad.bvar_b_set] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  have hst : st' = { st with memos := { st.memos with bvar_b_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj hinv.memos.bvarBC
    hrel.memos.bvarBC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with bvarBC := h1 } }
    { hinv with memos := { hinv.memos with bvarBC := h2 } } (Ext.refl _)

/-- `arena::monad::fvar_b_set` against `Arena.fvarBSet`. -/
theorem fvar_b_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.EIdx} {r : Std.U64} {st'}
    (hrun : arena.monad.fvar_b_set st k r = ok st') :
    SimS pers lst st' (Arena.fvarBSet (absEIdx k) (absU r)) := by
  rw [arena.monad.fvar_b_set] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  have hst : st' = { st with memos := { st.memos with fvar_b_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj hinv.memos.fvarBC
    hrel.memos.fvarBC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with fvarBC := h1 } }
    { hinv with memos := { hinv.memos with fvarBC := h2 } } (Ext.refl _)

/-- `arena::monad::inst_lp_l_set` against `Arena.instLPLSet`. -/
theorem inst_lp_l_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.LIdx} {r : arena.handle.LIdx} {st'}
    (hrun : arena.monad.inst_lp_l_set st k r = ok st') :
    SimS pers lst st' (Arena.instLPLSet (absLIdx k) (absLIdx r)) := by
  rw [arena.monad.inst_lp_l_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_lidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with inst_lp_l_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step lidx_eq2 absLIdx_inj hinv.memos.instLPLC
    hrel.memos.instLPLC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with instLPLC := h1 } }
    { hinv with memos := { hinv.memos with instLPLC := h2 } } (Ext.refl _)

/-- `arena::monad::inst_lp_ls_set` against `Arena.instLPLsSet`. -/
theorem inst_lp_ls_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.LsIdx} {r : arena.handle.LsIdx} {st'}
    (hrun : arena.monad.inst_lp_ls_set st k r = ok st') :
    SimS pers lst st' (Arena.instLPLsSet (absLsIdx k) (absLsIdx r)) := by
  rw [arena.monad.inst_lp_ls_set] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  rw [dupId_lsidx _ _ he] at hp
  have hst : st' = { st with memos := { st.memos with inst_lp_ls_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step lsidx_eq2 absLsIdx_inj hinv.memos.instLPLsC
    hrel.memos.instLPLsC hp
  exact SimS.mk rfl { hrel with memos := { hrel.memos with instLPLsC := h1 } }
    { hinv with memos := { hinv.memos with instLPLsC := h2 } } (Ext.refl _)

/-- `arena::monad::inst1_clear` against `Arena.inst1Clear`. -/
theorem inst1_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst1_clear st = ok st') :
    SimS pers lst st' Arena.inst1Clear := by
  rw [arena.monad.inst1_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with inst1_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.inst1C hp0
  exact SimS.mk rfl { hrel with memos := { hrel.memos with inst1C := g0 } }
    { hinv with memos := { hinv.memos with inst1C := i0 } } (Ext.refl _)

/-- `arena::monad::inst_l_clear` against `Arena.instLClear`. -/
theorem inst_l_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst_l_clear st = ok st') :
    SimS pers lst st' Arena.instLClear := by
  rw [arena.monad.inst_l_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with inst_l_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.instLC hp0
  exact SimS.mk rfl { hrel with memos := { hrel.memos with instLC := g0 } }
    { hinv with memos := { hinv.memos with instLC := i0 } } (Ext.refl _)

/-- `arena::monad::lift_clear` against `Arena.liftClear`. -/
theorem lift_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.lift_clear st = ok st') :
    SimS pers lst st' Arena.liftClear := by
  rw [arena.monad.lift_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with lift_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.liftC hp0
  exact SimS.mk rfl { hrel with memos := { hrel.memos with liftC := g0 } }
    { hinv with memos := { hinv.memos with liftC := i0 } } (Ext.refl _)

/-- `arena::monad::reset_clear` against `Arena.resetClear`. -/
theorem reset_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.reset_clear st = ok st') :
    SimS pers lst st' Arena.resetClear := by
  rw [arena.monad.reset_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with reset_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.resetC hp0
  exact SimS.mk rfl { hrel with memos := { hrel.memos with resetC := g0 } }
    { hinv with memos := { hinv.memos with resetC := i0 } } (Ext.refl _)

/-- `arena::monad::rename_clear` against `Arena.renameClear`. -/
theorem rename_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.rename_clear st = ok st') :
    SimS pers lst st' Arena.renameClear := by
  rw [arena.monad.rename_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with rename_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.renameC hp0
  exact SimS.mk rfl { hrel with memos := { hrel.memos with renameC := g0 } }
    { hinv with memos := { hinv.memos with renameC := i0 } } (Ext.refl _)

/-- `arena::monad::abs1_clear` against `Arena.abs1Clear`. -/
theorem abs1_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.abs1_clear st = ok st') :
    SimS pers lst st' Arena.abs1Clear := by
  rw [arena.monad.abs1_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with abs1_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.abs1C hp0
  exact SimS.mk rfl { hrel with memos := { hrel.memos with abs1C := g0 } }
    { hinv with memos := { hinv.memos with abs1C := i0 } } (Ext.refl _)

/-- `arena::monad::lower_clear` against `Arena.lowerClear`. -/
theorem lower_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.lower_clear st = ok st') :
    SimS pers lst st' Arena.lowerClear := by
  rw [arena.monad.lower_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with lower_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.lowerC hp0
  exact SimS.mk rfl { hrel with memos := { hrel.memos with lowerC := g0 } }
    { hinv with memos := { hinv.memos with lowerC := i0 } } (Ext.refl _)

/-- `arena::monad::inst1_l_clear` against `Arena.inst1LClear`. -/
theorem inst1_l_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst1_l_clear st = ok st') :
    SimS pers lst st' Arena.inst1LClear := by
  rw [arena.monad.inst1_l_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with inst1_l_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.inst1LC hp0
  exact SimS.mk rfl { hrel with memos := { hrel.memos with inst1LC := g0 } }
    { hinv with memos := { hinv.memos with inst1LC := i0 } } (Ext.refl _)

/-- `arena::monad::inst_lp_clear` against `Arena.instLPClear`. -/
theorem inst_lp_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst_lp_clear st = ok st') :
    SimS pers lst st' Arena.instLPClear := by
  rw [arena.monad.inst_lp_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with inst_lp_c := hm0, inst_lp_l_c := hm1, inst_lp_ls_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.instLPC hp0
  obtain ⟨g1, i1⟩ := memo_clear_step (absK := absLIdx) (absV := absLIdx)
    hinv.memos.instLPLC hp1
  obtain ⟨g2, i2⟩ := memo_clear_step (absK := absLsIdx) (absV := absLsIdx)
    hinv.memos.instLPLsC hp2
  exact SimS.mk rfl { hrel with memos := { hrel.memos with instLPC := g0, instLPLC := g1, instLPLsC := g2 } }
    { hinv with memos := { hinv.memos with instLPC := i0, instLPLC := i1, instLPLsC := i2 } } (Ext.refl _)

/-- `arena::monad::bvar_b_clear` against `Arena.bvarBClear`. -/
theorem bvar_b_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.bvar_b_clear st = ok st') :
    SimS pers lst st' Arena.bvarBClear := by
  rw [arena.monad.bvar_b_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with bvar_b_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdx) (absV := absU)
    hinv.memos.bvarBC hp0
  exact SimS.mk rfl { hrel with memos := { hrel.memos with bvarBC := g0 } }
    { hinv with memos := { hinv.memos with bvarBC := i0 } } (Ext.refl _)

/-- `arena::monad::fvar_b_clear` against `Arena.fvarBClear`. -/
theorem fvar_b_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.fvar_b_clear st = ok st') :
    SimS pers lst st' Arena.fvarBClear := by
  rw [arena.monad.fvar_b_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with fvar_b_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdx) (absV := absU)
    hinv.memos.fvarBC hp0
  exact SimS.mk rfl { hrel with memos := { hrel.memos with fvarBC := g0 } }
    { hinv with memos := { hinv.memos with fvarBC := i0 } } (Ext.refl _)
/-! ## Axiom census (DESIGN.md §5, the P5 gate)

Three standard axioms and nothing else on the closed layer: no `sorryAx`
(the lemmas named here are the proved ones), and in particular **no
`bv_decide` axiom** — `Arena/Handle.lean`'s own note is why the handle
packing is written with `*`, `/` and `%` rather than `>>>`/`&&&`, and this is
the census that would have caught it. -/

/-- info: 'ConRon.Refine2.tbl_node_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tbl_node_abs

/-- info: 'ConRon.Refine2.tbl_find_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tbl_find_abs

/-- info: 'ConRon.Refine2.tbl_der_at_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tbl_der_at_abs

/-- info: 'ConRon.Refine2.etables_get_app_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms etables_get_app_abs

/-- info: 'ConRon.Refine2.estore_view_app_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_view_app_abs

/-- info: 'ConRon.Refine2.view_app_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_app_run

/-- info: 'ConRon.Refine2.inst1_get_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inst1_get_run

/-- info: 'ConRon.Refine2.bvar_b_get_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bvar_b_get_run

/-- info: 'ConRon.Refine2.eidx_idxNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eidx_idxNat

/-- info: 'ConRon.Refine2.fail_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fail_run

/-- info: 'ConRon.Refine2.etables_get_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms etables_get_abs

/-- info: 'ConRon.Refine2.etables_der_at_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms etables_der_at_abs

/-- info: 'ConRon.Refine2.etables_get_bind_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms etables_get_bind_abs

/-- info: 'ConRon.Refine2.estore_view_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_view_abs

/-- info: 'ConRon.Refine2.estore_view_bind_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_view_bind_abs

/-- info: 'ConRon.Refine2.view_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_run

/-- info: 'ConRon.Refine2.derived_e_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms derived_e_run

/-- info: 'ConRon.Refine2.etag_isBind_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms etag_isBind_abs

/-- info: 'ConRon.Refine2.inst1_set_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inst1_set_run

/-- info: 'ConRon.Refine2.inst_lp_clear_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inst_lp_clear_run

/-- info: 'ConRon.Refine2.ntables_get_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ntables_get_abs

/-- info: 'ConRon.Refine2.ltables_get_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ltables_get_abs

/-- info: 'ConRon.Refine2.lstables_get_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lstables_get_abs

/-- info: 'ConRon.Refine2.lidx_vec_dup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lidx_vec_dup_eq

/-- info: 'ConRon.Refine2.view_n_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_n_run

/-- info: 'ConRon.Refine2.view_l_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_l_run

/-- info: 'ConRon.Refine2.view_ls_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_ls_run

/-- info: 'ConRon.Refine2.derived_l_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms derived_l_run

/-- info: 'ConRon.Refine2.tbl_push_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tbl_push_abs

/-- info: 'ConRon.Refine2.tbl_find_slot_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tbl_find_slot_abs

/-- info: 'ConRon.Refine2.tbl_size_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tbl_size_abs

/-- info: 'ConRon.Refine2.eidx_pack_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eidx_pack_abs

/-- info: 'ConRon.Refine2.cast_u32_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cast_u32_size

/-- info: 'ConRon.Refine2.derObsE_absU64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms derObsE_absU64

/-- info: 'ConRon.Refine2.der_of_bvar_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms der_of_bvar_obs

/-- info: 'ConRon.Refine2.estore_intern_bvar_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_bvar_abs

/-- info: 'ConRon.Refine2.internE_run_of_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internE_run_of_cap

/-- info: 'ConRon.Refine2.intern_e_bvar_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_bvar_run


end ConRon.Refine2
