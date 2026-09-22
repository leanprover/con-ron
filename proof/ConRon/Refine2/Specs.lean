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

/-- The node column's record is well formed — `TblInv`'s `nodesP` at one
index, which is what the binder datum's `hasParams` reader needs. -/
theorem tbl_node_wf (hinv : TblInv hH P rt) {n : Std.Usize} {o : Option A}
    (h : arena.store.Tbl.node hH hE hDA hDI hDD hDf rt n = ok o) :
    ∀ a, o = some a → P a := by
  rw [arena.store.Tbl.node] at h
  split at h
  · simp only [Result.ok.injEq] at h
    intro a ha; rw [← h] at ha; simp at ha
  · obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some q.1 = o := Result.ok_injective h
    intro a ha
    rw [← h2] at ha
    simp only [Option.some.injEq] at ha
    rw [← ha]
    exact hinv.nodesP q (List.mem_of_getElem? (vec_index_some hq))

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
  refine ⟨⟨?_, ?_, hcons⟩, ⟨hinv', hkeys, ?_⟩⟩
  · show (lt.nodes.push (absA a)).toList = _
    rw [Array.toList_push, hrel.nodes, hvv, List.map_append]
    rfl
  · show ((lt.der.push dl).toList).map obsD = _
    rw [Array.toList_push, List.map_append, hrel.der, hvv, List.map_append]
    simp only [List.map_cons, List.map_nil, hdl]
  · intro q hq
    show P q.1
    rw [hvv] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hinv.nodesP q hq
    · simp only [List.mem_singleton] at hq; rw [hq]; exact hk

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
  refine ⟨⟨hrel.nodes, hrel.der, hcons1⟩, ⟨hinv1, hkeys1, hinv.nodesP⟩, ?_, ?_⟩
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
    refine ⟨⟨?_, ?_, hcons2⟩, ⟨hinv2, hkeys2, ?_⟩⟩
    · show (lt.nodes.push (absA a)).toList = _
      rw [Array.toList_push, hrel.nodes, hvv, List.map_append]
      rfl
    · show ((lt.der.push dl).toList).map obsD = _
      rw [Array.toList_push, List.map_append, hrel.der, hvv, List.map_append]
      simp only [List.map_cons, List.map_nil, hdl]
    · intro q hq
      show P q.1
      rw [hvv] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hinv.nodesP q hq
      · simp only [List.mem_singleton] at hq; rw [hq]; exact hk

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

/-- The same at a twin action that READS the state and then continues: the
`get` is the identity on the run.  Every `do let s ← get; …` of the twin goes
through it, and it is what lets a `rfl`-level unfolding of a monadic body be
stated without spelling the body twice. -/
theorem run_get_bind {β : Type} (f : AState → AM β) (lst : AState) :
    ((do let s ← get; f s : AM β)).run lst = (f lst).run lst := rfl

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

/-- **`Arena.view` is a READER**: its run leaves the state alone.  `view_run`
concludes `AOut`, whose post-state is existentially quantified, so every
caller that binds a view and then continues at the SAME state needs this to
collapse the existential.  The `ExprOps` and Core tiers want it at every
`match ← view h` — which is most of the crate. -/
theorem view_run_state {lst lst' : AState} {hh : EIdx} {v : ENodeView}
    (h : (Arena.view hh).run lst = .ok (v, lst')) : lst' = lst := by
  rw [show (Arena.view hh).run lst
      = (match lst.store.view hh with
         | some w => Except.ok (w, lst)
         | none => Except.error (Arena.CheckError.internal
             "arena: dangling expression handle")) by
    show ((match lst.store.view hh with
            | some w => (pure w : AM ENodeView)
            | none => Arena.fail
                (.internal "arena: dangling expression handle")).run lst) = _
    cases lst.store.view hh <;> rfl] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact h.2.symm
  · simp at h

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

/-! ## `Arena.internE` after task #97-P3-1's probe-first fix

Task #97-P5-1's **finding 9** — "the capacity test is on the wrong side of the
probe in the twin", which made "Rust `Ok` ⇒ twin `ok`" false on a cons hit at a
full array — was fixed in the twin at task #97-P3-1: `internE` probes with
`EStore.find?` first and tests `Idx.idxCap` only on the miss.  So `hcap` is no
longer a hypothesis of the twenty-five `intern_*` statements; it is the MISS
PATH's own side condition, and on the miss path the port's `Tbl::full` is
`true` exactly when the twin's test fails — and answers `Native`, which claims
nothing.  What the wrapper needs instead is that a cons HIT moves nothing,
which is `intern_of_find` below. -/

/-- A cons hit interns nothing: the datum is already interned (it is part of
the key the probe matched) and `internAt` returns at the first `match`. -/
theorem internBM_of_findBM {st : EStore} {m : ConLeche.BinderMeta} {i : BMIdx}
    (hf : st.findBM m = some i) : st.internBM m = (st, i) := by
  rw [EStore.findBM] at hf
  cases hp : st.persFindBM m with
  | some j =>
    rw [hp] at hf
    simp only [Option.some.injEq] at hf
    subst hf
    exact EStore.internBM_hit_pers hp
  | none =>
    rw [hp] at hf
    by_cases hon : st.scratchOn = true
    · rw [if_pos hon] at hf
      exact EStore.internBM_hit_scr hp hon hf
    · rw [if_neg hon] at hf; simp at hf

theorem internBMOfView_of_findBMOfView {st : EStore} {v : ENodeView} {mi : BMIdx}
    (hf : st.findBMOfView v = some mi) : st.internBMOfView v = (st, mi) := by
  cases v
  case lam ty b m => exact internBM_of_findBM hf
  case forallE ty b m => exact internBM_of_findBM hf
  all_goals
    (have h0 : (Idx.ofWord 0 : BMIdx) = mi := by
       have : some (Idx.ofWord 0 : BMIdx) = some mi := hf
       simpa using this
     exact congrArg (Prod.mk st) h0)

/-- **A cons hit moves nothing** — the twin's `intern` at a handle its own
`find?` already answers is the identity on the store.  This is what
`internE`'s probe-first shape (task #97-P3-1) needs of the store tier. -/
theorem internAt_of_findAt {st : EStore} {v : ENodeView} {mi : BMIdx} {h : EIdx}
    (hfa : st.findAt v mi = some h) : st.internAt v mi = (st, h) := by
  unfold EStore.findAt at hfa
  unfold EStore.internAt
  cases hp : st.pers.find? v mi with
  | some j =>
    simp only [hp, Option.some.injEq] at hfa
    simp only [hp, hfa]
  | none =>
    simp only [hp] at hfa ⊢
    by_cases hon : st.scratchOn = true
    · simp only [hon, if_true] at hfa ⊢
      cases hs : st.scr.find? v mi with
      | some j =>
        simp only [hs, Option.some.injEq] at hfa
        simp only [hs, hfa]
      | none => simp only [hs] at hfa; simp at hfa
    · simp only [hon, if_false] at hfa; simp at hfa

theorem intern_of_find {st : EStore} {v : ENodeView} {h : EIdx}
    (hf : st.find? v = some h) : st.intern v = (st, h) := by
  rw [EStore.find?] at hf
  cases hm : st.findBMOfView v with
  | none => rw [hm] at hf; simp at hf
  | some mi =>
    rw [hm] at hf
    have hfa : st.findAt v mi = some h := hf
    rw [EStore.intern, internBMOfView_of_findBMOfView hm]
    show st.internAt v mi = (st, h)
    exact internAt_of_findAt hfa

/-- `Arena.internE`'s run.  Two arms, and only the second has a side
condition: on a cons HIT the store does not move (`intern_of_find`), and on a
MISS the capacity test is the twin's own — where the port's `Tbl::full` reads
`true` on exactly the same input and answers `Native`, which claims nothing. -/
/-- `Arena.internE`'s run at a view whose array is below the cap and which
needs no binder datum. -/
theorem internE_run_of_cap {lst : AState} {v : ENodeView}
    (hbm : EStore.eViewNeedsBM v = false)
    (hcap : lst.store.find? v = none →
      (if lst.store.scratchOn then lst.store.scr.sizeOf v
        else lst.store.pers.sizeOf v) < Idx.idxCap) :
    (Arena.internE v).run lst
      = .ok ((lst.store.intern v).2,
             { lst with store := (lst.store.intern v).1 }) := by
  rw [Arena.internE, run_get_bind]
  cases hf : lst.store.find? v with
  | some h =>
    rw [intern_of_find hf]
    rfl
  | none =>
    simp only [hbm, Bool.not_false, Bool.true_or, Bool.and_true,
      decide_eq_true_eq]
    rw [if_pos (hcap hf)]
    cases hi : lst.store.intern v with
    | mk st1 h1 => rfl

theorem intern_e_bvar_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (i : Std.U64)
    (hcap : lst.store.find? (.bvar (absU i)) = none →
      (if lst.store.scratchOn
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


/-! ## The level-list tier's derived column, and the three inner `der` readers

`der_of_sort` reads `EStore.lder` and `der_of_const` reads `EStore.lsder`, so
the `sort` and `const` arms need the level and the level-list tiers' derived
records — UP TO `derObsL`, which is `hasParam` and nothing else.  The `L`
half is `lstore_derived_abs` above; the `Ls` half is the same proof at a
one-constructor tier. -/

theorem lstables_der_at_abs {rt lt} (hrel : LsTablesRel rt lt)
    {i : arena.handle.LsIdx} {d : arena.store.LDer}
    (h : arena.store.LsTables.der_at rt i = ok d) :
    derObsL (lt.derAt (absLsIdx i)) = derObsL (absLDer d) := by
  rw [arena.store.LsTables.der_at] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [LsTables.derAt, lsidx_tag_abs ht]
  by_cases h0 : t = arena.handle.LSTAG_LIST
  · rw [if_pos ((etag_dec lstag_list_abs).mpr h0)]
    rw [if_pos h0] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [lsidx_idxNat hm]
    exact tbl_der_at_abs hrel.lists dupId_lder derDefault_lder h
  · rw [if_neg (fun hx => h0 ((etag_dec lstag_list_abs).mp hx))]
    rw [if_neg h0] at h
    rw [derDefault_lder _ h]

theorem lsstore_derived_abs {pers rs ls} (hrel : LsStoreRel pers rs ls)
    {i : arena.handle.LsIdx} {d}
    (h : arena.store.LsStore.derived rs pers i = ok d) :
    derObsL (ls.derived (absLsIdx i)) = derObsL (absLDer d) := by
  rw [arena.store.LsStore.derived] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := lsidx_is_persistent_abs hb
  rw [LsStore.derived]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absLsIdx i).isPersistent = true by rw [hb2, hbv])]
    rw [arena.store.LsStore.pers_der_at] at h
    have h3 : arena.store.LsTables.der_at (rPersLs pers rs) i = ok d := by
      unfold rPersLs
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact lstables_der_at_abs hrel.perst h3
  · rw [if_neg (show ¬ (absLsIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]; exact lstables_der_at_abs hrel.scrt h
    · rw [if_neg hs]
      rw [derDefault_lder _ h]

/-- `arena::store::EStore.lder` against `EStore.lder`, up to `derObsL`. -/
theorem estore_lder_obs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.LIdx} {d}
    (h : arena.store.EStore.lder rs pers i = ok d) :
    derObsL (ls.lder (absLIdx i)) = derObsL (absLDer d) := by
  rw [arena.store.EStore.lder] at h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [arena.store.EStore.ls] at hl
  have hl2 : l = rs.lss.ls := (Result.ok_injective hl).symm
  subst hl2
  rw [EStore.lder, EStore.ls]
  exact lstore_derived_abs hrel.lss.lvl h

/-- `arena::store::EStore.lsder` against `EStore.lsder`, up to `derObsL`. -/
theorem estore_lsder_obs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.LsIdx} {d}
    (h : arena.store.EStore.lsder rs pers i = ok d) :
    derObsL (ls.lsder (absLsIdx i)) = derObsL (absLDer d) := by
  rw [arena.store.EStore.lsder] at h
  rw [EStore.lsder]
  exact lsstore_derived_abs hrel.lss h


/-! ## The `der_of_*` family, once and for all

Eleven arms, and the same two steps in each: the port packs a word and the
twin packs a word, and the OBSERVED fields — `bvarOfData`, `fvarOfData`,
`lpOfData`, DESIGN §8.3's lesson-20 cutoffs — are what was packed on both
sides (`Refine/Expr.lean`'s `pack_bits`, con-leche's `bvarOfData_pack` and
its two siblings).  **The hash never appears**, which is `Refine2/AbsStore.lean`'s
finding and the reason `TblRel` carries `derObsE` rather than a value
equation.  `derObsE_pack` is that step once; `derObsE_fields` is its inverse,
for the five arms that read a CHILD's word back. -/

/-- The packing step, from the twin's `packData` to the port's `pack_data`:
equal range fields and equal flag give equal OBSERVATIONS. -/
theorem derObsE_pack {ph pb pf : Std.U64} {plp : Bool} {p : Std.U64}
    {b f : UInt64} {lp : Bool} (hs : UInt64)
    (hb : b.toNat = pb.val) (hf : f.toNat = pf.val) (hl : lp = plp)
    (hbr : pb.val < 32768) (hfr : pf.val < 32768)
    (hpk : kernel.expr.pack_data ph pb pf plp = ok p) :
    derObsE (ConLeche.packData hs b f lp) = derObsE (absU64 p) := by
  obtain ⟨h1, h2, h3⟩ := ConRon.Refine.Expr.pack_bits hbr hfr hpk
  rw [derObsE_absU64, derObsE]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show ConLeche.bvarOfData _ = _
    rw [ConLeche.bvarOfData_pack _ _ _ _ (by omega) (by omega), h1]
    apply UInt64.toNat_inj.mp
    rw [hb, UInt64.toNat_ofNat_of_lt' (show pb.val < 2 ^ 64 by scalar_tac)]
  · show ConLeche.fvarOfData _ = _
    rw [ConLeche.fvarOfData_pack _ _ _ _ (by omega) (by omega), h2]
    apply UInt64.toNat_inj.mp
    rw [hf, UInt64.toNat_ofNat_of_lt' (show pf.val < 2 ^ 64 by scalar_tac)]
  · show ConLeche.lpOfData _ = _
    rw [ConLeche.lpOfData_pack _ _ _ _ (by omega) (by omega), hl, h3]
    cases plp <;> simp

/-- The reading step: what an OBSERVED equality says about the three fields,
at the `Nat` level the port's own forward readings live at. -/
theorem derObsE_fields {w : UInt64} {p : Std.U64}
    (h : derObsE w = derObsE (absU64 p)) :
    (ConLeche.bvarOfData w).toNat = p.val / 65536 % 32768 ∧
      (ConLeche.fvarOfData w).toNat = p.val / 2 % 32768 ∧
      ConLeche.lpOfData w = decide (p.val % 2 = 1) := by
  rw [derObsE_absU64, derObsE] at h
  have h1 : ConLeche.bvarOfData w = UInt64.ofNat (p.val / 65536 % 32768) :=
    congrArg (fun q => q.1) h
  have h2 : ConLeche.fvarOfData w = UInt64.ofNat (p.val / 2 % 32768) :=
    congrArg (fun q => q.2.1) h
  have h3 : ConLeche.lpOfData w = decide (p.val % 2 = 1) :=
    congrArg (fun q => q.2.2) h
  have hp := u64_val_lt p
  have hr1 : p.val / 65536 % 32768 < 2 ^ 64 := by omega
  have hr2 : p.val / 2 % 32768 < 2 ^ 64 := by omega
  exact ⟨by rw [h1]; exact UInt64.toNat_ofNat_of_lt' hr1,
    by rw [h2]; exact UInt64.toNat_ofNat_of_lt' hr2, h3⟩

/-! ### The `sort` arm -/

theorem der_of_sort_obs {pers} {rs : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls) {u : arena.handle.LIdx} {d : Std.U64}
    (h : arena.store.EStore.der_of_sort rs pers u = ok d) :
    derObsE (ls.derOfSort (absLIdx u)) = derObsE (absU64 d) := by
  rw [arena.store.EStore.der_of_sort] at h
  obtain ⟨du, hdu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hh, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hl : (ls.lder (absLIdx u)).hasParam = du.has_param := estore_lder_obs hrel hdu
  rw [EStore.derOfSort]
  exact derObsE_pack _ (by simp) (by simp) hl (by simp) (by simp) h

/-! ### The `const` arm -/

theorem der_of_const_obs {pers} {rs : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls) {n : arena.handle.NIdx} {us : arena.handle.LsIdx}
    {d : Std.U64}
    (h : arena.store.EStore.der_of_const rs pers n us = ok d) :
    derObsE (ls.derOfConst (absNIdx n) (absLsIdx us)) = derObsE (absU64 d) := by
  rw [arena.store.EStore.der_of_const] at h
  obtain ⟨dus, hdus, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j0, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hh, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hl : (ls.lsder (absLsIdx us)).hasParam = dus.has_param :=
    estore_lsder_obs hrel hdus
  rw [EStore.derOfConst]
  exact derObsE_pack _ (by simp) (by simp) hl (by simp) (by simp) h

/-! ### The `lit` arm -/

theorem der_of_lit_obs {rs : arena.store.EStore} {ls : EStore}
    {l : kernel.expr.Literal} {d : Std.U64}
    (h : arena.store.EStore.der_of_lit rs l = ok d) :
    derObsE (ls.derOfLit (ConRon.Refine.absLiteral l)) = derObsE (absU64 d) := by
  rw [arena.store.EStore.der_of_lit] at h
  obtain ⟨j0, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hh, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [EStore.derOfLit]
  exact derObsE_pack _ (by simp) (by simp) rfl (by simp) (by simp) h

/-! ### The `proj` arm — the first that reads a child's word BACK -/

theorem der_of_proj_obs {pers} {rs : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls) {s : arena.handle.NIdx} {i : Std.U64}
    {e : arena.handle.EIdx} {d : Std.U64}
    (h : arena.store.EStore.der_of_proj rs pers s i e = ok d) :
    derObsE (ls.derOfProj (absNIdx s) (absU i) (absEIdx e)) = derObsE (absU64 d) := by
  rw [arena.store.EStore.der_of_proj] at h
  obtain ⟨de, hde, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j3, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j4, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j5, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j6, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hh, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i7, hi7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i8, hi8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bl, hbl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hb, hf, hlp⟩ := derObsE_fields (estore_derived_abs hrel hde)
  have h7 := ConRon.Refine.Expr.bvar_of_data_val hi7
  have h8 := ConRon.Refine.Expr.fvar_of_data_val hi8
  have hbeq := ConRon.Refine.Expr.lp_of_data_val hbl
  rw [EStore.derOfProj]
  refine derObsE_pack _ (by omega) (by omega) ?_ (by omega) (by omega) h
  rw [hlp, hbeq]
  by_cases hc : de.val % 2 = 1 <;> simp [hc]

/-! ### The `app` arm — two children, and `max` on both ranges -/

theorem der_of_app_obs {pers} {rs : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls) {f a : arena.handle.EIdx} {d : Std.U64}
    (h : arena.store.EStore.der_of_app rs pers f a = ok d) :
    derObsE (ls.derOfApp (absEIdx f) (absEIdx a)) = derObsE (absU64 d) := by
  rw [arena.store.EStore.der_of_app] at h
  obtain ⟨df, hdf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨da, hda, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j3, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j4, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hh, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i5, hi5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i6, hi6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i7, hi7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i8, hi8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i9, hi9, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bf, hbf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbF, hfF, hlF⟩ := derObsE_fields (estore_derived_abs hrel hdf)
  obtain ⟨hbA, hfA, hlA⟩ := derObsE_fields (estore_derived_abs hrel hda)
  have e4 := ConRon.Refine.Expr.bvar_of_data_val hi4
  have e5 := ConRon.Refine.Expr.bvar_of_data_val hi5
  have e6 := ConRon.Refine.Expr.max_u64_val hi6
  have e7 := ConRon.Refine.Expr.fvar_of_data_val hi7
  have e8 := ConRon.Refine.Expr.fvar_of_data_val hi8
  have e9 := ConRon.Refine.Expr.max_u64_val hi9
  have ebF := ConRon.Refine.Expr.lp_of_data_val hbf
  rw [EStore.derOfApp]
  refine derObsE_pack _ ?_ ?_ ?_ (by omega) (by omega) h
  · rw [ConLeche.toNat_max]; omega
  · rw [ConLeche.toNat_max]; omega
  · rw [hlF, hlA]
    by_cases hc : bf = true
    · rw [if_pos hc] at hb1
      have hb1' : b1 = true := (Result.ok_injective hb1).symm
      have hdf1 : df.val % 2 = 1 := by
        have h' : (df.val % 2 == 1) = true := by rw [← ebF]; exact hc
        simpa using h'
      rw [hb1', hdf1]; simp
    · rw [if_neg hc] at hb1
      have hdf0 : ¬ (df.val % 2 = 1) := by
        intro hcc; exact hc (by rw [ebF]; simpa using hcc)
      rw [ConRon.Refine.Expr.lp_of_data_val hb1]
      simp only [decide_eq_false hdf0, Bool.false_or]
      by_cases hc2 : da.val % 2 = 1 <;> simp [hc2]

/-- con-leche's `satPred` at the `Nat` level the port's `sat_pred_val` lives
at.  The twin's zero arm is invisible there: `0 - 1 = 0` in `Nat`. -/
theorem satPred_toNat {x : UInt64} :
    (ConLeche.satPred x).toNat = if x.toNat = 32767 then 32767 else x.toNat - 1 := by
  rw [ConLeche.satPred]
  split <;> rename_i c1
  · have hx : x.toNat = 32767 := by simpa [← UInt64.toNat_inj] using c1
    rw [if_pos hx]; rfl
  · have c1' : x.toNat ≠ 32767 := by
      intro hcc; exact c1 (by simpa [← UInt64.toNat_inj] using hcc)
    rw [if_neg c1']
    split <;> rename_i c2
    · have hz : x.toNat = 0 := by simpa [← UInt64.toNat_inj] using c2
      rw [hz]; rfl
    · have c2' : x.toNat ≠ 0 := by
        intro hcc; exact c2 (by simpa [← UInt64.toNat_inj] using hcc)
      exact ConLeche.toNat_sub_one c2'

/-! ### The `letE` arm — three children, `max` and `satPred` -/

theorem der_of_let_obs {pers} {rs : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls) {ty val bo : arena.handle.EIdx} {d : Std.U64}
    (h : arena.store.EStore.der_of_let_at rs pers ty val bo = ok d) :
    derObsE (ls.derOfLetAt (absEIdx ty) (absEIdx val) (absEIdx bo))
      = derObsE (absU64 d) := by
  rw [arena.store.EStore.der_of_let_at] at h
  obtain ⟨dt, hdt, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨dv, hdv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨db, hdb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [arena.store.der_of_let] at h
  obtain ⟨j1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j3, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j4, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j5, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j6, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hh, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i6, hi6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i7, hi7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i8, hi8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i9, hi9, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i10, hi10, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i11, hi11, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i12, hi12, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i13, hi13, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i14, hi14, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i15, hi15, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i16, hi16, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bt, hbt, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbT, hfT, hlT⟩ := derObsE_fields (estore_derived_abs hrel hdt)
  obtain ⟨hbV, hfV, hlV⟩ := derObsE_fields (estore_derived_abs hrel hdv)
  obtain ⟨hbB, hfB, hlB⟩ := derObsE_fields (estore_derived_abs hrel hdb)
  have e6 := ConRon.Refine.Expr.bvar_of_data_val hi6
  have e7 := ConRon.Refine.Expr.bvar_of_data_val hi7
  have e8 := ConRon.Refine.Expr.max_u64_val hi8
  have e9 := ConRon.Refine.Expr.bvar_of_data_val hi9
  have e10 := ConRon.Refine.Expr.sat_pred_val hi10
  have e11 := ConRon.Refine.Expr.max_u64_val hi11
  have e12 := ConRon.Refine.Expr.fvar_of_data_val hi12
  have e13 := ConRon.Refine.Expr.fvar_of_data_val hi13
  have e14 := ConRon.Refine.Expr.max_u64_val hi14
  have e15 := ConRon.Refine.Expr.fvar_of_data_val hi15
  have e16 := ConRon.Refine.Expr.max_u64_val hi16
  have ebT := ConRon.Refine.Expr.lp_of_data_val hbt
  -- the `satPred` field: `ConLeche.satRange` is kept UNFOLDED on both sides,
  -- so that the two `ite`s' `Decidable` instances match and `if_pos` fires
  have hi10lt : i10.val < 32768 := by
    by_cases hc : i9.val = ConLeche.satRange
    · rw [e10, if_pos hc]; simp [ConLeche.satRange]
    · rw [e10, if_neg hc]; omega
  have hi8 : i8.val < 32768 := by omega
  have hr11 : i11.val < 32768 := by omega
  have hr14 : i14.val < 32768 := by omega
  have hr16 : i16.val < 32768 := by omega
  have hsp10 : (ConLeche.satPred (ConLeche.bvarOfData (ls.derived (absEIdx bo)))).toNat
      = i10.val := by
    rw [satPred_toNat, hbB, ← e9, e10]
    by_cases hc : i9.val = ConLeche.satRange
    · rw [if_pos hc, if_pos (show i9.val = 32767 from hc)]; rfl
    · rw [if_neg hc, if_neg (show ¬ (i9.val = 32767) from hc)]
  rw [EStore.derOfLetAt, derOfLet]
  refine derObsE_pack _ ?_ ?_ ?_ hr11 hr16 h
  · rw [ConLeche.toNat_max, ConLeche.toNat_max, hsp10, hbT, hbV]; omega
  · rw [ConLeche.toNat_max, ConLeche.toNat_max, hfT, hfV, hfB]; omega
  · rw [hlT, hlV, hlB]
    by_cases hc : bt = true
    · rw [if_pos hc] at hb1
      have hb1' : b1 = true := (Result.ok_injective hb1).symm
      have hdt1 : dt.val % 2 = 1 := by
        have h' : (dt.val % 2 == 1) = true := by rw [← ebT]; exact hc
        simpa using h'
      rw [hb1', hdt1]; simp
    · rw [if_neg hc] at hb1
      obtain ⟨b2, hb2, hb1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb1
      have ebV := ConRon.Refine.Expr.lp_of_data_val hb2
      have hdt0 : ¬ (dt.val % 2 = 1) := by
        intro hcc; exact hc (by rw [ebT]; simpa using hcc)
      simp only [decide_eq_false hdt0, Bool.false_or]
      by_cases hc2 : b2 = true
      · rw [if_pos hc2] at hb1
        have hb1' : b1 = true := (Result.ok_injective hb1).symm
        have hdv1 : dv.val % 2 = 1 := by
          have h' : (dv.val % 2 == 1) = true := by rw [← ebV]; exact hc2
          simpa using h'
        rw [hb1', hdv1]; simp
      · rw [if_neg hc2] at hb1
        have hdv0 : ¬ (dv.val % 2 = 1) := by
          intro hcc; exact hc2 (by rw [ebV]; simpa using hcc)
        simp only [decide_eq_false hdv0, Bool.false_or]
        rw [ConRon.Refine.Expr.lp_of_data_val hb1]
        by_cases hc3 : db.val % 2 = 1 <;> simp [hc3]


/-! ## `der_of_*`, the `fvar` arm

The first arm that reads a CHILD's derived word, and so the first that needs
`estore_derived_abs` — up to `derObsE`, which is exactly the observation the
`lp` field is read through. -/

theorem der_of_fvar_obs {pers} {rs : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls) {idx : Std.U64} {ty : arena.handle.EIdx}
    {d : Std.U64}
    (h : arena.store.EStore.der_of_fvar rs pers idx ty = ok d) :
    derObsE (ls.derOfFVar (absU idx) (absEIdx ty)) = derObsE (absU64 d) := by
  rw [arena.store.EStore.der_of_fvar] at h
  obtain ⟨dt, hdt, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i3, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i4, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hh, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i5, hi5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bl, hbl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hi5v := ConRon.Refine.Expr.sat_succ_val hi5
  have hf : i5.val < 32768 := by rw [hi5v]; simp [ConLeche.satRange]
  have hb : (0#u64 : Std.U64).val < 32768 := by simp
  obtain ⟨hbv, hfv, hlv⟩ := ConRon.Refine.Expr.pack_bits hb hf h
  have hdtobs := estore_derived_abs hrel hdt
  rw [derObsE_absU64] at hdtobs
  have hlp : ConLeche.lpOfData (ls.derived (absEIdx ty)) = decide (dt.val % 2 = 1) :=
    congrArg (fun p => p.2.2) hdtobs
  rw [EStore.derOfFVar, derObsE_absU64, derObsE, hbv, hfv, hlv]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show ConLeche.bvarOfData _ = _
    rw [ConLeche.bvarOfData_pack _ _ _ _ (by decide) (ConLeche.satSucc_lt _)]
    rfl
  · show ConLeche.fvarOfData _ = _
    rw [ConLeche.fvarOfData_pack _ _ _ _ (by decide) (ConLeche.satSucc_lt _),
      ConLeche.satSucc, hi5v]
  · show ConLeche.lpOfData _ = _
    rw [ConLeche.lpOfData_pack _ _ _ _ (by decide) (ConLeche.satSucc_lt _), hlp,
      ConRon.Refine.Expr.lp_of_data_val hbl]
    simp


theorem dupId_fvarnode :
    DupId arena.store.FVarNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hty : e = a.ty := dupId_eidx _ _ he
  subst hty
  exact (Result.ok_injective h).symm

theorem absFVarNode_inj :
    ∀ a b : arena.store.FVarNode, FVarNodeWF a → FVarNodeWF b →
      absFVarNode a = absFVarNode b → a = b := by
  intro a b _ _ h
  obtain ⟨x, xt⟩ := a; obtain ⟨y, yt⟩ := b
  have hx : x.val = y.val := congrArg (fun r => (FVarNode.idx r : Nat)) h
  have ht : absEIdx xt = absEIdx yt := congrArg FVarNode.ty h
  simp [UScalar.eq_imp _ _ hx, absEIdx_inj ht]

/-- `arena::store::EStore.intern_fvar` against `EStore.intern` at the `fvar`
view.  §3b's six arms, plus the `sk` prologue **finding 7** names: the port
skips the persistent cons probe when a child is scratch, where the twin
always probes, and the two agree only because a persistent node's children
are persistent — `Arena/WF.lean`'s `childOK`, a `StoreWF` clause and
therefore Theorem 1's.  It arrives here as `hchild`. -/
theorem estore_intern_fvar_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {idx : Std.U64} {ty : arena.handle.EIdx}
    (hchild : (absEIdx ty).isPersistent = false →
      ls.pers.fvars.find? ⟨absU idx, absEIdx ty⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_fvar rs pers idx ty = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.fvar (absU idx) (absEIdx ty))).2 ∧
        StoreRel pers rs' (ls.intern (.fvar (absU idx) (absEIdx ty))).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_fvar] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧ (sk = true → (absEIdx ty).isPersistent = false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := eidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      intro hsk
      split at hb2 <;> rename_i hbb <;>
        simp only [Result.ok.injEq] at hb2
      · rw [← e2, ← hb2] at hsk; simp at hsk
      · rw [hp1]; simpa using hbb
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      intro hsk; rw [← e2] at hsk; simp at hsk
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.pers.fvars.find? ⟨absU idx, absEIdx ty⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4]; simpa using hchild (hskp hsk)⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.fvars hinv.perst.fvars fvar_eq2 dupId_eidx
          (P := FVarNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.fvars hinv.perst.fvars fvar_eq2 dupId_eidx
          (P := FVarNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.fvar (absU idx) (absEIdx ty))
      = ls.internAt (.fvar (absU idx) (absEIdx ty)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  have hfind : ls.pers.find? (ENodeView.fvar (absU idx) (absEIdx ty)) (Idx.ofWord 0)
      = ls.pers.fvars.find? ⟨absU idx, absEIdx ty⟩ := rfl
  rw [hfind, hE4]
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
        tbl_find_slot_abs hrel.scrt.fvars hinv.scrt.fvars fvar_eq2 dupId_fvarnode
          dupId_eidx absFVarNode_inj (P := FVarNodeWF) trivial hfs
      have hfind2 : ls.scr.find? (ENodeView.fvar (absU idx) (absEIdx ty)) (Idx.ofWord 0)
          = ls.scr.fvars.find? ⟨absU idx, absEIdx ty⟩ := rfl
      simp only [absFVarNode] at hfindT
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
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with fvars := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with fvars := hinvT }⟩⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
          have hrelS : StoreRel pers
              { rs with scr := { rs.scr with fvars := t }, scratch_on := true } ls :=
            ⟨hrel.lss, hrel.perst, { hrel.scrt with fvars := hrelT },
              hrel.scratchOn.trans hsc⟩
          have hhandle : absEIdx hnew
              = Idx.mk ETag.fvar Idx.tierS (UInt32.ofNat ls.scr.fvars.size) := by
            rw [eidx_pack_abs hpk, etag_fvar_abs, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d (ls.derOfFVar (absU idx) (absEIdx ty))
              (der_of_fvar_obs (ls := ls) hrelS hd) hnew t1 ht1
          simp only [absFVarNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with fvars := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with fvars := hinv1 }⟩⟩
    · -- the persistent tier
      rw [if_neg hsc]
      have hsh : rs.shared_on = false := by
        by_contra hc
        exact hsc (hfrozen (by simpa using hc))
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
        have hrelP : TblRel FVarNodeWF absFVarNode absEIdx absU64 derObsE
            rs.pers.fvars ls.pers.fvars := by rw [← hpersE]; exact hrel.perst.fvars
        have hinvP : TblInv
            arena.store.FVarNode.Insts.Con_ron_coreRonHashmapHashable
            FVarNodeWF rs.pers.fvars := by
          rw [← hpersE]; exact hinv.perst.fvars
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        have hrelS : StoreRel pers
            { rs with scratch_on := false, shared_on := false } ls := by
          refine ⟨hrel.lss, ?_, hrel.scrt, ?_⟩
          · show ETablesRel (rPersE pers { rs with scratch_on := false, shared_on := false })
              ls.pers
            unfold rPersE; rw [if_neg (by simp)]; exact hrelPerst
          · rw [hrel.scratchOn]; simpa using hsc
        have hhandle : absEIdx hnew
            = Idx.mk ETag.fvar Idx.tierP (UInt32.ofNat ls.pers.fvars.size) := by
          rw [eidx_pack_abs hpk, etag_fvar_abs, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP fvar_eq2 dupId_fvarnode absFVarNode_inj
            (P := FVarNodeWF) trivial (dl := ls.derOfFVar (absU idx) (absEIdx ty))
            (der_of_fvar_obs (ls := ls) hrelS hd) ht1
        simp only [absFVarNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with fvars := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with fvars := hinv1 }


/-! ## The node records: `Dup` is the identity, and `abs` is injective

Two obligations per constructor array, which `tbl_find_slot_abs` and
`tbl_push_abs` take: the port's `Dup::dup2` gives the value back (it is a
field-wise copy through the handles' own `dup2`), and the record's
abstraction is injective on well-formed records — the four that carry a
CACHED VALUE (`StrNode`'s code points, `ListNode`'s handle vector, `LitNode`'s
`Literal`, `BMNode`'s `PropWhen`) are the reason `TblRel` is `RelOn P`. -/

theorem dupId_sortnode :
    DupId arena.store.SortNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.u := dupId_lidx _ _ hx
  subst e1
  exact (Result.ok_injective h).symm

theorem absSortNode_inj :
    ∀ a b : arena.store.SortNode, SortNodeWF a → SortNodeWF b →
      absSortNode a = absSortNode b → a = b := by
  intro a b _ _ h
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b
  have h1 : absLIdx x = absLIdx y := congrArg SortNode.u h
  simp [absLIdx_inj h1]

theorem dupId_constnode :
    DupId arena.store.ConstNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.n := dupId_nidx _ _ hx
  subst e1
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e2 : y = a.us := dupId_lsidx _ _ hy
  subst e2
  exact (Result.ok_injective h).symm

theorem absConstNode_inj :
    ∀ a b : arena.store.ConstNode, ConstNodeWF a → ConstNodeWF b →
      absConstNode a = absConstNode b → a = b := by
  intro a b _ _ h
  obtain ⟨x, xs⟩ := a; obtain ⟨y, ys⟩ := b
  have h1 : absNIdx x = absNIdx y := congrArg ConstNode.n h
  have h2 : absLsIdx xs = absLsIdx ys := congrArg ConstNode.us h
  simp [absNIdx_inj h1, absLsIdx_inj h2]

theorem dupId_appnode :
    DupId arena.store.AppNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.f := dupId_eidx _ _ hx
  subst e1
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e2 : y = a.a := dupId_eidx _ _ hy
  subst e2
  exact (Result.ok_injective h).symm

theorem absAppNode_inj :
    ∀ a b : arena.store.AppNode, AppNodeWF a → AppNodeWF b →
      absAppNode a = absAppNode b → a = b := by
  intro a b _ _ h
  obtain ⟨x, xa⟩ := a; obtain ⟨y, ya⟩ := b
  have h1 : absEIdx x = absEIdx y := congrArg AppNode.f h
  have h2 : absEIdx xa = absEIdx ya := congrArg AppNode.a h
  simp [absEIdx_inj h1, absEIdx_inj h2]

theorem dupId_projnode :
    DupId arena.store.ProjNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.n := dupId_nidx _ _ hx
  subst e1
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e2 : y = a.e := dupId_eidx _ _ hy
  subst e2
  exact (Result.ok_injective h).symm

theorem absProjNode_inj :
    ∀ a b : arena.store.ProjNode, ProjNodeWF a → ProjNodeWF b →
      absProjNode a = absProjNode b → a = b := by
  intro a b _ _ h
  obtain ⟨n1, i1, e1⟩ := a; obtain ⟨n2, i2, e2⟩ := b
  have h1 : absNIdx n1 = absNIdx n2 := congrArg ProjNode.n h
  have h2 : i1.val = i2.val := congrArg (fun r => (ProjNode.i r : Nat)) h
  have h3 : absEIdx e1 = absEIdx e2 := congrArg ProjNode.e h
  simp [absNIdx_inj h1, UScalar.eq_imp _ _ h2, absEIdx_inj h3]

theorem dupId_letnode :
    DupId arena.store.LetNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.ty := dupId_eidx _ _ hx
  subst e1
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e2 : y = a.val := dupId_eidx _ _ hy
  subst e2
  obtain ⟨z, hz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e3 : z = a.body := dupId_eidx _ _ hz
  subst e3
  exact (Result.ok_injective h).symm

theorem absLetNode_inj :
    ∀ a b : arena.store.LetNode, LetNodeWF a → LetNodeWF b →
      absLetNode a = absLetNode b → a = b := by
  intro a b _ _ h
  obtain ⟨t1, v1, b1⟩ := a; obtain ⟨t2, v2, b2⟩ := b
  have h1 : absEIdx t1 = absEIdx t2 := congrArg LetNode.ty h
  have h2 : absEIdx v1 = absEIdx v2 := congrArg LetNode.val h
  have h3 : absEIdx b1 = absEIdx b2 := congrArg LetNode.body h
  simp [absEIdx_inj h1, absEIdx_inj h2, absEIdx_inj h3]

theorem dupId_bindnode :
    DupId arena.store.BindNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.ty := dupId_eidx _ _ hx
  subst e1
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e2 : y = a.body := dupId_eidx _ _ hy
  subst e2
  obtain ⟨z, hz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e3 : z = a.m := dupId_bmidx _ _ hz
  subst e3
  exact (Result.ok_injective h).symm

theorem absBindNode_inj :
    ∀ a b : arena.store.BindNode, BindNodeWF a → BindNodeWF b →
      absBindNode a = absBindNode b → a = b := by
  intro a b _ _ h
  obtain ⟨t1, b1, m1⟩ := a; obtain ⟨t2, b2, m2⟩ := b
  have h1 : absEIdx t1 = absEIdx t2 := congrArg BindNode.ty h
  have h2 : absEIdx b1 = absEIdx b2 := congrArg BindNode.body h
  have h3 : absBMIdx m1 = absBMIdx m2 := congrArg BindNode.m h
  simp [absEIdx_inj h1, absEIdx_inj h2, absBMIdx_inj h3]

theorem dupId_litnode :
    DupId arena.store.LitNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.l := ConRon.Refine.Expr.literal_dup_eq hx
  subst e1
  exact (Result.ok_injective h).symm

theorem absLitNode_inj :
    ∀ a b : arena.store.LitNode, LitNodeWF a → LitNodeWF b →
      absLitNode a = absLitNode b → a = b := by
  intro a b ha hb h
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b
  have h1 : ConRon.Refine.absLiteral x = ConRon.Refine.absLiteral y :=
    congrArg LitNode.l h
  have h2 : x = y := ConRon.Refine.Expr.absLiteral_inj ha hb h1
  subst h2; rfl

theorem dupId_bmnode :
    DupId arena.store.BMNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.pw := ConRon.Refine.PropWhen.dup_eq hx
  subst e1
  exact (Result.ok_injective h).symm

theorem absBMNode_inj :
    ∀ a b : arena.store.BMNode, BMNodeWF a → BMNodeWF b →
      absBMNode a = absBMNode b → a = b := by
  intro a b ha hb h
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b
  have h1 : ConRon.Refine.absPropWhen x = ConRon.Refine.absPropWhen y :=
    congrArg BMNode.pw h
  have h2 : x = y := ConRon.Refine.PropWhen.absPropWhen_injective ha hb h1
  subst h2; rfl


/-- `arena::store::EStore.intern_sort` against `EStore.intern` at the
`sort` view: §3b's six-arm peel at the `sorts` array, with finding 7's
`sk` prologue — the port skips the persistent cons probe when a child is
scratch, and the two agree only under `StoreWF`'s persistent-children clause,
which arrives here as `hchild`. -/
theorem estore_intern_sort_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {u : arena.handle.LIdx}
    (hchild : (absLIdx u).isPersistent = false →
      ls.pers.sorts.find? ⟨absLIdx u⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_sort rs pers u = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.sort (absLIdx u))).2 ∧
        StoreRel pers rs' (ls.intern (.sort (absLIdx u))).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_sort] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧ (sk = true → (absLIdx u).isPersistent = false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := lidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      intro hsk
      split at hb2 <;> rename_i hbb <;>
        simp only [Result.ok.injEq] at hb2
      · rw [← e2, ← hb2] at hsk; simp at hsk
      · rw [hp1]; simpa using hbb
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      intro hsk; rw [← e2] at hsk; simp at hsk
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.pers.sorts.find? ⟨absLIdx u⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4]; simpa using hchild (hskp hsk)⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.sorts hinv.perst.sorts sort_eq2 dupId_eidx
          (P := SortNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.sorts hinv.perst.sorts sort_eq2 dupId_eidx
          (P := SortNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.sort (absLIdx u))
      = ls.internAt (.sort (absLIdx u)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  have hfind : ls.pers.find? (ENodeView.sort (absLIdx u)) (Idx.ofWord 0)
      = ls.pers.sorts.find? ⟨absLIdx u⟩ := rfl
  rw [hfind, hE4]
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
        tbl_find_slot_abs hrel.scrt.sorts hinv.scrt.sorts sort_eq2 dupId_sortnode
          dupId_eidx absSortNode_inj (P := SortNodeWF) trivial hfs
      have hfind2 : ls.scr.find? (ENodeView.sort (absLIdx u)) (Idx.ofWord 0)
          = ls.scr.sorts.find? ⟨absLIdx u⟩ := rfl
      simp only [absSortNode] at hfindT
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
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with sorts := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with sorts := hinvT }⟩⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
          have hrelS : StoreRel pers
              { rs with scr := { rs.scr with sorts := t }, scratch_on := true } ls :=
            ⟨hrel.lss, hrel.perst, { hrel.scrt with sorts := hrelT },
              hrel.scratchOn.trans hsc⟩
          have hhandle : absEIdx hnew
              = Idx.mk ETag.sort Idx.tierS (UInt32.ofNat ls.scr.sorts.size) := by
            rw [eidx_pack_abs hpk, etag_sort_abs, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d (ls.derOfSort (absLIdx u))
              (der_of_sort_obs (ls := ls) hrelS hd) hnew t1 ht1
          simp only [absSortNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with sorts := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with sorts := hinv1 }⟩⟩
    · -- the persistent tier
      rw [if_neg hsc]
      have hsh : rs.shared_on = false := by
        by_contra hc
        exact hsc (hfrozen (by simpa using hc))
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
        have hrelP : TblRel SortNodeWF absSortNode absEIdx absU64 derObsE
            rs.pers.sorts ls.pers.sorts := by rw [← hpersE]; exact hrel.perst.sorts
        have hinvP : TblInv
            arena.store.SortNode.Insts.Con_ron_coreRonHashmapHashable
            SortNodeWF rs.pers.sorts := by
          rw [← hpersE]; exact hinv.perst.sorts
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        have hrelS : StoreRel pers
            { rs with scratch_on := false, shared_on := false } ls := by
          refine ⟨hrel.lss, ?_, hrel.scrt, ?_⟩
          · show ETablesRel (rPersE pers { rs with scratch_on := false, shared_on := false })
              ls.pers
            unfold rPersE; rw [if_neg (by simp)]; exact hrelPerst
          · rw [hrel.scratchOn]; simpa using hsc
        have hhandle : absEIdx hnew
            = Idx.mk ETag.sort Idx.tierP (UInt32.ofNat ls.pers.sorts.size) := by
          rw [eidx_pack_abs hpk, etag_sort_abs, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP sort_eq2 dupId_sortnode absSortNode_inj
            (P := SortNodeWF) trivial (dl := ls.derOfSort (absLIdx u))
            (der_of_sort_obs (ls := ls) hrelS hd) ht1
        simp only [absSortNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with sorts := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with sorts := hinv1 }



/-- `arena::store::EStore.intern_const` against `EStore.intern` at the
`const` view: §3b's six-arm peel at the `consts` array, with finding 7's
`sk` prologue — the port skips the persistent cons probe when a child is
scratch, and the two agree only under `StoreWF`'s persistent-children clause,
which arrives here as `hchild`. -/
theorem estore_intern_const_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {n : arena.handle.NIdx} {us : arena.handle.LsIdx}
    (hchild : ((absNIdx n).isPersistent = false ∨ (absLsIdx us).isPersistent = false) →
      ls.pers.consts.find? ⟨absNIdx n, absLsIdx us⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_const rs pers n us = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.const (absNIdx n) (absLsIdx us))).2 ∧
        StoreRel pers rs' (ls.intern (.const (absNIdx n) (absLsIdx us))).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_const] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧ (sk = true → (absNIdx n).isPersistent = false ∨ (absLsIdx us).isPersistent = false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := nidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      intro hsk
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := lsidx_is_persistent_abs hb3
        simp only [Result.ok.injEq] at hb2
        right; rw [hp3]; rw [← e2, ← hb2] at hsk; simpa using hsk
      · simp only [Result.ok.injEq] at hb2
        left; rw [hp1]; simpa using hbb
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      intro hsk; rw [← e2] at hsk; simp at hsk
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.pers.consts.find? ⟨absNIdx n, absLsIdx us⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4]; simpa using hchild (hskp hsk)⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.consts hinv.perst.consts const_eq2 dupId_eidx
          (P := ConstNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.consts hinv.perst.consts const_eq2 dupId_eidx
          (P := ConstNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.const (absNIdx n) (absLsIdx us))
      = ls.internAt (.const (absNIdx n) (absLsIdx us)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  have hfind : ls.pers.find? (ENodeView.const (absNIdx n) (absLsIdx us)) (Idx.ofWord 0)
      = ls.pers.consts.find? ⟨absNIdx n, absLsIdx us⟩ := rfl
  rw [hfind, hE4]
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
        tbl_find_slot_abs hrel.scrt.consts hinv.scrt.consts const_eq2 dupId_constnode
          dupId_eidx absConstNode_inj (P := ConstNodeWF) trivial hfs
      have hfind2 : ls.scr.find? (ENodeView.const (absNIdx n) (absLsIdx us)) (Idx.ofWord 0)
          = ls.scr.consts.find? ⟨absNIdx n, absLsIdx us⟩ := rfl
      simp only [absConstNode] at hfindT
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
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with consts := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with consts := hinvT }⟩⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
          have hrelS : StoreRel pers
              { rs with scr := { rs.scr with consts := t }, scratch_on := true } ls :=
            ⟨hrel.lss, hrel.perst, { hrel.scrt with consts := hrelT },
              hrel.scratchOn.trans hsc⟩
          have hhandle : absEIdx hnew
              = Idx.mk ETag.const Idx.tierS (UInt32.ofNat ls.scr.consts.size) := by
            rw [eidx_pack_abs hpk, etag_const_abs, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d (ls.derOfConst (absNIdx n) (absLsIdx us))
              (der_of_const_obs (ls := ls) hrelS hd) hnew t1 ht1
          simp only [absConstNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with consts := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with consts := hinv1 }⟩⟩
    · -- the persistent tier
      rw [if_neg hsc]
      have hsh : rs.shared_on = false := by
        by_contra hc
        exact hsc (hfrozen (by simpa using hc))
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
        have hrelP : TblRel ConstNodeWF absConstNode absEIdx absU64 derObsE
            rs.pers.consts ls.pers.consts := by rw [← hpersE]; exact hrel.perst.consts
        have hinvP : TblInv
            arena.store.ConstNode.Insts.Con_ron_coreRonHashmapHashable
            ConstNodeWF rs.pers.consts := by
          rw [← hpersE]; exact hinv.perst.consts
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        have hrelS : StoreRel pers
            { rs with scratch_on := false, shared_on := false } ls := by
          refine ⟨hrel.lss, ?_, hrel.scrt, ?_⟩
          · show ETablesRel (rPersE pers { rs with scratch_on := false, shared_on := false })
              ls.pers
            unfold rPersE; rw [if_neg (by simp)]; exact hrelPerst
          · rw [hrel.scratchOn]; simpa using hsc
        have hhandle : absEIdx hnew
            = Idx.mk ETag.const Idx.tierP (UInt32.ofNat ls.pers.consts.size) := by
          rw [eidx_pack_abs hpk, etag_const_abs, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP const_eq2 dupId_constnode absConstNode_inj
            (P := ConstNodeWF) trivial (dl := ls.derOfConst (absNIdx n) (absLsIdx us))
            (der_of_const_obs (ls := ls) hrelS hd) ht1
        simp only [absConstNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with consts := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with consts := hinv1 }



/-- `arena::store::EStore.intern_app` against `EStore.intern` at the
`app` view: §3b's six-arm peel at the `apps` array, with finding 7's
`sk` prologue — the port skips the persistent cons probe when a child is
scratch, and the two agree only under `StoreWF`'s persistent-children clause,
which arrives here as `hchild`. -/
theorem estore_intern_app_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {f a : arena.handle.EIdx}
    (hchild : ((absEIdx f).isPersistent = false ∨ (absEIdx a).isPersistent = false) →
      ls.pers.apps.find? ⟨absEIdx f, absEIdx a⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_app rs pers f a = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.app (absEIdx f) (absEIdx a))).2 ∧
        StoreRel pers rs' (ls.intern (.app (absEIdx f) (absEIdx a))).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_app] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧ (sk = true → (absEIdx f).isPersistent = false ∨ (absEIdx a).isPersistent = false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := eidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      intro hsk
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := eidx_is_persistent_abs hb3
        simp only [Result.ok.injEq] at hb2
        right; rw [hp3]; rw [← e2, ← hb2] at hsk; simpa using hsk
      · simp only [Result.ok.injEq] at hb2
        left; rw [hp1]; simpa using hbb
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      intro hsk; rw [← e2] at hsk; simp at hsk
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.pers.apps.find? ⟨absEIdx f, absEIdx a⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4]; simpa using hchild (hskp hsk)⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.apps hinv.perst.apps app_eq2 dupId_eidx
          (P := AppNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.apps hinv.perst.apps app_eq2 dupId_eidx
          (P := AppNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.app (absEIdx f) (absEIdx a))
      = ls.internAt (.app (absEIdx f) (absEIdx a)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  have hfind : ls.pers.find? (ENodeView.app (absEIdx f) (absEIdx a)) (Idx.ofWord 0)
      = ls.pers.apps.find? ⟨absEIdx f, absEIdx a⟩ := rfl
  rw [hfind, hE4]
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
        tbl_find_slot_abs hrel.scrt.apps hinv.scrt.apps app_eq2 dupId_appnode
          dupId_eidx absAppNode_inj (P := AppNodeWF) trivial hfs
      have hfind2 : ls.scr.find? (ENodeView.app (absEIdx f) (absEIdx a)) (Idx.ofWord 0)
          = ls.scr.apps.find? ⟨absEIdx f, absEIdx a⟩ := rfl
      simp only [absAppNode] at hfindT
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
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with apps := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with apps := hinvT }⟩⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
          have hrelS : StoreRel pers
              { rs with scr := { rs.scr with apps := t }, scratch_on := true } ls :=
            ⟨hrel.lss, hrel.perst, { hrel.scrt with apps := hrelT },
              hrel.scratchOn.trans hsc⟩
          have hhandle : absEIdx hnew
              = Idx.mk ETag.app Idx.tierS (UInt32.ofNat ls.scr.apps.size) := by
            rw [eidx_pack_abs hpk, etag_app_abs, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d (ls.derOfApp (absEIdx f) (absEIdx a))
              (der_of_app_obs (ls := ls) hrelS hd) hnew t1 ht1
          simp only [absAppNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with apps := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with apps := hinv1 }⟩⟩
    · -- the persistent tier
      rw [if_neg hsc]
      have hsh : rs.shared_on = false := by
        by_contra hc
        exact hsc (hfrozen (by simpa using hc))
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
        have hrelP : TblRel AppNodeWF absAppNode absEIdx absU64 derObsE
            rs.pers.apps ls.pers.apps := by rw [← hpersE]; exact hrel.perst.apps
        have hinvP : TblInv
            arena.store.AppNode.Insts.Con_ron_coreRonHashmapHashable
            AppNodeWF rs.pers.apps := by
          rw [← hpersE]; exact hinv.perst.apps
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        have hrelS : StoreRel pers
            { rs with scratch_on := false, shared_on := false } ls := by
          refine ⟨hrel.lss, ?_, hrel.scrt, ?_⟩
          · show ETablesRel (rPersE pers { rs with scratch_on := false, shared_on := false })
              ls.pers
            unfold rPersE; rw [if_neg (by simp)]; exact hrelPerst
          · rw [hrel.scratchOn]; simpa using hsc
        have hhandle : absEIdx hnew
            = Idx.mk ETag.app Idx.tierP (UInt32.ofNat ls.pers.apps.size) := by
          rw [eidx_pack_abs hpk, etag_app_abs, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP app_eq2 dupId_appnode absAppNode_inj
            (P := AppNodeWF) trivial (dl := ls.derOfApp (absEIdx f) (absEIdx a))
            (der_of_app_obs (ls := ls) hrelS hd) ht1
        simp only [absAppNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with apps := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with apps := hinv1 }



/-- `arena::store::EStore.intern_proj` against `EStore.intern` at the
`proj` view: §3b's six-arm peel at the `projs` array, with finding 7's
`sk` prologue — the port skips the persistent cons probe when a child is
scratch, and the two agree only under `StoreWF`'s persistent-children clause,
which arrives here as `hchild`. -/
theorem estore_intern_proj_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {n : arena.handle.NIdx} {i : Std.U64} {ep : arena.handle.EIdx}
    (hchild : ((absNIdx n).isPersistent = false ∨ (absEIdx ep).isPersistent = false) →
      ls.pers.projs.find? ⟨absNIdx n, absU i, absEIdx ep⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_proj rs pers n i ep = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.proj (absNIdx n) (absU i) (absEIdx ep))).2 ∧
        StoreRel pers rs' (ls.intern (.proj (absNIdx n) (absU i) (absEIdx ep))).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_proj] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧ (sk = true → (absNIdx n).isPersistent = false ∨ (absEIdx ep).isPersistent = false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := nidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      intro hsk
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := eidx_is_persistent_abs hb3
        simp only [Result.ok.injEq] at hb2
        right; rw [hp3]; rw [← e2, ← hb2] at hsk; simpa using hsk
      · simp only [Result.ok.injEq] at hb2
        left; rw [hp1]; simpa using hbb
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      intro hsk; rw [← e2] at hsk; simp at hsk
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.pers.projs.find? ⟨absNIdx n, absU i, absEIdx ep⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4]; simpa using hchild (hskp hsk)⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.projs hinv.perst.projs proj_eq2 dupId_eidx
          (P := ProjNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.projs hinv.perst.projs proj_eq2 dupId_eidx
          (P := ProjNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.proj (absNIdx n) (absU i) (absEIdx ep))
      = ls.internAt (.proj (absNIdx n) (absU i) (absEIdx ep)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  have hfind : ls.pers.find? (ENodeView.proj (absNIdx n) (absU i) (absEIdx ep)) (Idx.ofWord 0)
      = ls.pers.projs.find? ⟨absNIdx n, absU i, absEIdx ep⟩ := rfl
  rw [hfind, hE4]
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
        tbl_find_slot_abs hrel.scrt.projs hinv.scrt.projs proj_eq2 dupId_projnode
          dupId_eidx absProjNode_inj (P := ProjNodeWF) trivial hfs
      have hfind2 : ls.scr.find? (ENodeView.proj (absNIdx n) (absU i) (absEIdx ep)) (Idx.ofWord 0)
          = ls.scr.projs.find? ⟨absNIdx n, absU i, absEIdx ep⟩ := rfl
      simp only [absProjNode] at hfindT
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
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with projs := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with projs := hinvT }⟩⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
          have hrelS : StoreRel pers
              { rs with scr := { rs.scr with projs := t }, scratch_on := true } ls :=
            ⟨hrel.lss, hrel.perst, { hrel.scrt with projs := hrelT },
              hrel.scratchOn.trans hsc⟩
          have hhandle : absEIdx hnew
              = Idx.mk ETag.proj Idx.tierS (UInt32.ofNat ls.scr.projs.size) := by
            rw [eidx_pack_abs hpk, etag_proj_abs, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d (ls.derOfProj (absNIdx n) (absU i) (absEIdx ep))
              (der_of_proj_obs (ls := ls) hrelS hd) hnew t1 ht1
          simp only [absProjNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with projs := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with projs := hinv1 }⟩⟩
    · -- the persistent tier
      rw [if_neg hsc]
      have hsh : rs.shared_on = false := by
        by_contra hc
        exact hsc (hfrozen (by simpa using hc))
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
        have hrelP : TblRel ProjNodeWF absProjNode absEIdx absU64 derObsE
            rs.pers.projs ls.pers.projs := by rw [← hpersE]; exact hrel.perst.projs
        have hinvP : TblInv
            arena.store.ProjNode.Insts.Con_ron_coreRonHashmapHashable
            ProjNodeWF rs.pers.projs := by
          rw [← hpersE]; exact hinv.perst.projs
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        have hrelS : StoreRel pers
            { rs with scratch_on := false, shared_on := false } ls := by
          refine ⟨hrel.lss, ?_, hrel.scrt, ?_⟩
          · show ETablesRel (rPersE pers { rs with scratch_on := false, shared_on := false })
              ls.pers
            unfold rPersE; rw [if_neg (by simp)]; exact hrelPerst
          · rw [hrel.scratchOn]; simpa using hsc
        have hhandle : absEIdx hnew
            = Idx.mk ETag.proj Idx.tierP (UInt32.ofNat ls.pers.projs.size) := by
          rw [eidx_pack_abs hpk, etag_proj_abs, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP proj_eq2 dupId_projnode absProjNode_inj
            (P := ProjNodeWF) trivial (dl := ls.derOfProj (absNIdx n) (absU i) (absEIdx ep))
            (der_of_proj_obs (ls := ls) hrelS hd) ht1
        simp only [absProjNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with projs := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with projs := hinv1 }



/-- `arena::store::EStore.intern_let_e` against `EStore.intern` at the
`let_e` view: §3b's six-arm peel at the `lets` array, with finding 7's
`sk` prologue — the port skips the persistent cons probe when a child is
scratch, and the two agree only under `StoreWF`'s persistent-children clause,
which arrives here as `hchild`. -/
theorem estore_intern_let_e_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {ty val bo : arena.handle.EIdx}
    (hchild : ((absEIdx ty).isPersistent = false ∨ (absEIdx val).isPersistent = false ∨ (absEIdx bo).isPersistent = false) →
      ls.pers.lets.find? ⟨absEIdx ty, absEIdx val, absEIdx bo⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_let_e rs pers ty val bo = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))).2 ∧
        StoreRel pers rs' (ls.intern (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_let_e] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧ (sk = true → (absEIdx ty).isPersistent = false ∨ (absEIdx val).isPersistent = false ∨ (absEIdx bo).isPersistent = false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := eidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      intro hsk
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := eidx_is_persistent_abs hb3
        split at hb2 <;> rename_i hbb2
        · obtain ⟨b4, hb4, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
          have hp4 := eidx_is_persistent_abs hb4
          simp only [Result.ok.injEq] at hb2
          right; right; rw [hp4]; rw [← e2, ← hb2] at hsk; simpa using hsk
        · simp only [Result.ok.injEq] at hb2
          right; left; rw [hp3]; simpa using hbb2
      · simp only [Result.ok.injEq] at hb2
        left; rw [hp1]; simpa using hbb
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      intro hsk; rw [← e2] at hsk; simp at hsk
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.pers.lets.find? ⟨absEIdx ty, absEIdx val, absEIdx bo⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4]; simpa using hchild (hskp hsk)⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.lets hinv.perst.lets let_eq2 dupId_eidx
          (P := LetNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.lets hinv.perst.lets let_eq2 dupId_eidx
          (P := LetNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))
      = ls.internAt (.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  have hfind : ls.pers.find? (ENodeView.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) (Idx.ofWord 0)
      = ls.pers.lets.find? ⟨absEIdx ty, absEIdx val, absEIdx bo⟩ := rfl
  rw [hfind, hE4]
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
        tbl_find_slot_abs hrel.scrt.lets hinv.scrt.lets let_eq2 dupId_letnode
          dupId_eidx absLetNode_inj (P := LetNodeWF) trivial hfs
      have hfind2 : ls.scr.find? (ENodeView.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) (Idx.ofWord 0)
          = ls.scr.lets.find? ⟨absEIdx ty, absEIdx val, absEIdx bo⟩ := rfl
      simp only [absLetNode] at hfindT
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
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with lets := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lets := hinvT }⟩⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
          have hrelS : StoreRel pers
              { rs with scr := { rs.scr with lets := t }, scratch_on := true } ls :=
            ⟨hrel.lss, hrel.perst, { hrel.scrt with lets := hrelT },
              hrel.scratchOn.trans hsc⟩
          have hhandle : absEIdx hnew
              = Idx.mk ETag.letE Idx.tierS (UInt32.ofNat ls.scr.lets.size) := by
            rw [eidx_pack_abs hpk, etag_letE_abs, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d (ls.derOfLetAt (absEIdx ty) (absEIdx val) (absEIdx bo))
              (der_of_let_obs (ls := ls) hrelS hd) hnew t1 ht1
          simp only [absLetNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with lets := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lets := hinv1 }⟩⟩
    · -- the persistent tier
      rw [if_neg hsc]
      have hsh : rs.shared_on = false := by
        by_contra hc
        exact hsc (hfrozen (by simpa using hc))
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
        have hrelP : TblRel LetNodeWF absLetNode absEIdx absU64 derObsE
            rs.pers.lets ls.pers.lets := by rw [← hpersE]; exact hrel.perst.lets
        have hinvP : TblInv
            arena.store.LetNode.Insts.Con_ron_coreRonHashmapHashable
            LetNodeWF rs.pers.lets := by
          rw [← hpersE]; exact hinv.perst.lets
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        have hrelS : StoreRel pers
            { rs with scratch_on := false, shared_on := false } ls := by
          refine ⟨hrel.lss, ?_, hrel.scrt, ?_⟩
          · show ETablesRel (rPersE pers { rs with scratch_on := false, shared_on := false })
              ls.pers
            unfold rPersE; rw [if_neg (by simp)]; exact hrelPerst
          · rw [hrel.scratchOn]; simpa using hsc
        have hhandle : absEIdx hnew
            = Idx.mk ETag.letE Idx.tierP (UInt32.ofNat ls.pers.lets.size) := by
          rw [eidx_pack_abs hpk, etag_letE_abs, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP let_eq2 dupId_letnode absLetNode_inj
            (P := LetNodeWF) trivial (dl := ls.derOfLetAt (absEIdx ty) (absEIdx val) (absEIdx bo))
            (der_of_let_obs (ls := ls) hrelS hd) ht1
        simp only [absLetNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with lets := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with lets := hinv1 }



/-- `arena::store::EStore.intern_lit` against `EStore.intern` at the `lit`
view.  The one expression constructor with NO handle child, so the port has
no `sk` prologue and finding 7's hypothesis does not arise; what it does have
is a cons key carrying a VALUE, so `TblRel`'s `RelOn P` asks the caller for
`LiteralWF` (task #97-P5-1 §8's "the cons key's own WF is a hypothesis the
caller owes"). -/
theorem estore_intern_lit_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {l : kernel.expr.Literal}
    (hwf : ConRon.Refine.LiteralWF l) {r} {rs'}
    (h : arena.store.EStore.intern_lit rs pers l = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.lit (ConRon.Refine.absLiteral l))).2 ∧
        StoreRel pers rs' (ls.intern (.lit (ConRon.Refine.absLiteral l))).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_lit] at h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, bb, hit⟩ := q
  -- the persistent probe, under the `shared_on` select
  have hE : e = rs.pers ∧ bb = rs.shared_on ∧
      ls.pers.lits.find? ⟨ConRon.Refine.absLiteral l⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hs <;>
      obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
      obtain ⟨h1, h2, h3⟩ := hq
    · refine ⟨h1.symm, by rw [← h2, hs], ?_⟩
      have := tbl_find_abs hrel.perst.lits hinv.perst.lits lit_eq2 dupId_eidx
        (P := LitNodeWF) hwf (by unfold rPersE; rw [if_pos hs]; exact hf)
      rw [← h3]; exact this
    · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      have := tbl_find_abs hrel.perst.lits hinv.perst.lits lit_eq2 dupId_eidx
        (P := LitNodeWF) hwf (by unfold rPersE; rw [if_neg hs]; exact hf)
      rw [← h3]; exact this
  obtain ⟨hE1, hE2, hE3⟩ := hE
  subst hE1; subst hE2
  -- the twin's `intern` at a non-binder view is `internAt` at handle 0
  have htw : ls.intern (.lit (ConRon.Refine.absLiteral l)) = ls.internAt (.lit (ConRon.Refine.absLiteral l)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  have hfind : ls.pers.find? (ENodeView.lit (ConRon.Refine.absLiteral l)) (Idx.ofWord 0)
      = ls.pers.lits.find? ⟨ConRon.Refine.absLiteral l⟩ := rfl
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
        tbl_find_slot_abs hrel.scrt.lits hinv.scrt.lits lit_eq2 dupId_litnode
          dupId_eidx absLitNode_inj (P := LitNodeWF) hwf hfs
      have hfind2 : ls.scr.find? (ENodeView.lit (ConRon.Refine.absLiteral l)) (Idx.ofWord 0)
          = ls.scr.lits.find? ⟨ConRon.Refine.absLiteral l⟩ := rfl
      simp only [absLitNode] at hfindT
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
          exact ⟨rfl, { hrel with scrt := { hrel.scrt with lits := hrelT } },
            { hinv with scrt := { hinv.scrt with lits := hinvT } }⟩
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
              = Idx.mk ETag.lit Idx.tierS (UInt32.ofNat ls.scr.lits.size) := by
            rw [eidx_pack_abs hpk, etag_lit_abs, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d (ls.derOfLit (ConRon.Refine.absLiteral l)) (der_of_lit_obs (ls := ls) hd)
              hnew t1 ht1
          simp only [absLitNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with lits := hrel1 }, rfl⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lits := hinv1 }⟩⟩
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
        have hrelP : TblRel LitNodeWF absLitNode absEIdx absU64 derObsE
            rs.pers.lits ls.pers.lits := by rw [← hpersE]; exact hrel.perst.lits
        have hinvP : TblInv
            arena.store.LitNode.Insts.Con_ron_coreRonHashmapHashable
            LitNodeWF rs.pers.lits := by
          rw [← hpersE]; exact hinv.perst.lits
        have hhandle : absEIdx hnew
            = Idx.mk ETag.lit Idx.tierP (UInt32.ofNat ls.pers.lits.size) := by
          rw [eidx_pack_abs hpk, etag_lit_abs, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP lit_eq2 dupId_litnode absLitNode_inj
            (P := LitNodeWF) hwf (dl := ls.derOfLit (ConRon.Refine.absLiteral l))
            (der_of_lit_obs (ls := ls) hd) ht1
        simp only [absLitNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        exact ⟨hhandle, ⟨hrel.lss, { hrelPerst with lits := hrel1 }, hrel.scrt, rfl⟩,
          ⟨hinv.lss, { hinvPerst with lits := hinv1 }, hinv.scrt⟩⟩


/-- `arena::store::EStore.intern_bm` against `EStore.internBM` — the binder
datum store (task #97-P6-16): one constructor, no children (so no `sk`
prologue), a `BMIdx` whose `pack` takes no tag, and a derived column that is a
pure hash, which is why `ETablesRel`'s `bms` row observes NOTHING and the
`der` obligation here is `rfl`.  The cons key carries a `PropWhen`, so
`RelOn P` asks the caller for `PropWhenWF`. -/
theorem estore_intern_bm_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {m : kernel.expr.BinderMeta}
    (hwf : ConRon.Refine.PropWhenWF m.pw) {r} {rs'}
    (h : arena.store.EStore.intern_bm rs pers m = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absBMIdx hh = (ls.internBM (ConRon.Refine.absBinderMeta m)).2 ∧
        StoreRel pers rs' (ls.internBM (ConRon.Refine.absBinderMeta m)).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_bm] at h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, bb, hit⟩ := q
  -- the persistent probe, under the `shared_on` select
  have hE : e = rs.pers ∧ bb = rs.shared_on ∧
      ls.pers.bms.find? ⟨ConRon.Refine.absPropWhen m.pw⟩ = hit.map absBMIdx := by
    split at hq <;> rename_i hs <;>
      obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
      obtain ⟨h1, h2, h3⟩ := hq
    · refine ⟨h1.symm, by rw [← h2, hs], ?_⟩
      have := tbl_find_abs hrel.perst.bms hinv.perst.bms bm_eq2 dupId_bmidx
        (P := BMNodeWF) (show BMNodeWF ⟨m.pw⟩ from hwf) (by unfold rPersE; rw [if_pos hs]; exact hf)
      rw [← h3]; exact this
    · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      have := tbl_find_abs hrel.perst.bms hinv.perst.bms bm_eq2 dupId_bmidx
        (P := BMNodeWF) (show BMNodeWF ⟨m.pw⟩ from hwf) (by unfold rPersE; rw [if_neg hs]; exact hf)
      rw [← h3]; exact this
  obtain ⟨hE1, hE2, hE3⟩ := hE
  subst hE1; subst hE2
  -- the twin's `intern` at a non-binder view is `internAt` at handle 0
  rw [EStore.internBM]
  have hfind : ls.persFindBM (ConRon.Refine.absBinderMeta m)
      = ls.pers.bms.find? ⟨ConRon.Refine.absPropWhen m.pw⟩ := rfl
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
        tbl_find_slot_abs hrel.scrt.bms hinv.scrt.bms bm_eq2 dupId_bmnode
          dupId_bmidx absBMNode_inj (P := BMNodeWF) (show BMNodeWF ⟨m.pw⟩ from hwf) hfs
      have hfind2 : ls.scr.findBM (ConRon.Refine.absBinderMeta m)
          = ls.scr.bms.find? ⟨ConRon.Refine.absPropWhen m.pw⟩ := rfl
      simp only [absBMNode] at hfindT
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
          exact ⟨rfl, { hrel with scrt := { hrel.scrt with bms := hrelT } },
            { hinv with scrt := { hinv.scrt with bms := hinvT } }⟩
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
          rw [dupId_bmidx _ _ he1] at h
          obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs'⟩ := he
          subst hr; subst hs'
          have hhandle : absBMIdx hnew
              = Idx.mk 0 Idx.tierS (UInt32.ofNat ls.scr.bms.size) := by
            rw [bmidx_pack_abs hpk, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d (hash (ConRon.Refine.absPropWhen m.pw)) rfl hnew t1 ht1
          simp only [absBMNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with bms := hrel1 }, rfl⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with bms := hinv1 }⟩⟩
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
        rw [dupId_bmidx _ _ he1] at h
        obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs'⟩ := he
        subst hr; subst hs'
        have hrelP : TblRel BMNodeWF absBMNode absBMIdx absU64 derObsN
            rs.pers.bms ls.pers.bms := by rw [← hpersE]; exact hrel.perst.bms
        have hinvP : TblInv
            arena.store.BMNode.Insts.Con_ron_coreRonHashmapHashable
            BMNodeWF rs.pers.bms := by
          rw [← hpersE]; exact hinv.perst.bms
        have hhandle : absBMIdx hnew
            = Idx.mk 0 Idx.tierP (UInt32.ofNat ls.pers.bms.size) := by
          rw [bmidx_pack_abs hpk, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP bm_eq2 dupId_bmnode absBMNode_inj
            (P := BMNodeWF) (show BMNodeWF ⟨m.pw⟩ from hwf) (dl := hash (ConRon.Refine.absPropWhen m.pw))
            rfl ht1
        simp only [absBMNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        exact ⟨hhandle, ⟨hrel.lss, { hrelPerst with bms := hrel1 }, hrel.scrt, rfl⟩,
          ⟨hinv.lss, { hinvPerst with bms := hinv1 }, hinv.scrt⟩⟩


/-! ## The binder datum's two derived scalars, and the `lam`/`forallE` arm

`derOfBind`'s `pm` is the datum's has-a-parameter bit, and it reaches the
parent word's `lpOfData` — so it IS observed, where the datum's hash is not.
It is read off the datum's RECORD (`getBMDer`'s `r.pw.hasParams`), which is
why `TblInv` had to grow its `nodesP` clause: `prop_when::has_params` refines
`PropWhen.hasParams` only on a well-formed value. -/

theorem etables_get_bm_der_abs {rt lt} (hrel : ETablesRel rt lt)
    (hinv : ETablesInv rt) {i : arena.handle.BMIdx} {bd : Std.U64 × Bool}
    (h : arena.store.ETables.get_bm_der rt i = ok bd) :
    (lt.getBMDer (absBMIdx i)).2 = bd.2 := by
  rw [arena.store.ETables.get_bm_der] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.bms ho
  cases o with
  | none =>
    have he := Result.ok_injective h
    rw [ETables.getBMDer, bmidx_idxNat hn, hnode, ← he]
    rfl
  | some r =>
    obtain ⟨d2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨bb, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have he := Result.ok_injective h
    have hwf : BMNodeWF r := tbl_node_wf hinv.bms ho r rfl
    have hp := ConRon.Refine.PropWhen.has_params_shape
      (ConRon.Refine.PropWhen.wf_shape hwf) hb
    rw [ETables.getBMDer, bmidx_idxNat hn, hnode, ← he]
    exact hp.symm

theorem estore_bm_der_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs) {i : arena.handle.BMIdx} {bd : Std.U64 × Bool}
    (h : arena.store.EStore.bm_der rs pers i = ok bd) :
    (ls.bmDer (absBMIdx i)).2 = bd.2 := by
  rw [arena.store.EStore.bm_der] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := bmidx_is_persistent_abs hb
  rw [EStore.bmDer]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absBMIdx i).isPersistent = true by rw [hb2, hbv])]
    rw [arena.store.EStore.pers_get_bm_der] at h
    have h3 : arena.store.ETables.get_bm_der (rPersE pers rs) i = ok bd := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_bm_der_abs hrel.perst hinv.perst h3
  · rw [if_neg (show ¬ (absBMIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_bm_der_abs hrel.scrt hinv.scrt h
    · rw [if_neg hs]
      have he := Result.ok_injective h
      rw [← he]

/-- `arena::store::EStore.der_of_bind_at_i` against `EStore.derOfBindAtI` —
the `lam` (tag 19) and `forallE` (23) arms at a datum HANDLE. -/
theorem der_of_bind_i_obs {pers} {rs : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls) (hinv : StoreInv pers rs)
    {tag : Std.U64} {ty bo : arena.handle.EIdx} {mi : arena.handle.BMIdx}
    {d : Std.U64}
    (h : arena.store.EStore.der_of_bind_at_i rs pers tag ty bo mi = ok d) :
    derObsE (ls.derOfBindAtI (absU64 tag) (absEIdx ty) (absEIdx bo) (absBMIdx mi))
      = derObsE (absU64 d) := by
  rw [arena.store.EStore.der_of_bind_at_i] at h
  obtain ⟨bd, hbd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨dt, hdt, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨db, hdb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hpm := estore_bm_der_abs hrel hinv hbd
  obtain ⟨hm, pm⟩ := bd
  replace h : arena.store.der_of_bind tag dt db hm pm = ok d := h
  rw [arena.store.der_of_bind] at h
  obtain ⟨j1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j3, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j4, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨j5, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hh, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i5, hi5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i6, hi6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i7, hi7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i8, hi8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i9, hi9, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i10, hi10, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i11, hi11, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bt, hbt, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨pm1, hpm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbT, hfT, hlT⟩ := derObsE_fields (estore_derived_abs hrel hdt)
  obtain ⟨hbB, hfB, hlB⟩ := derObsE_fields (estore_derived_abs hrel hdb)
  have e5 := ConRon.Refine.Expr.bvar_of_data_val hi5
  have e6 := ConRon.Refine.Expr.bvar_of_data_val hi6
  have e7 := ConRon.Refine.Expr.sat_pred_val hi7
  have e8 := ConRon.Refine.Expr.max_u64_val hi8
  have e9 := ConRon.Refine.Expr.fvar_of_data_val hi9
  have e10 := ConRon.Refine.Expr.fvar_of_data_val hi10
  have e11 := ConRon.Refine.Expr.max_u64_val hi11
  have ebT := ConRon.Refine.Expr.lp_of_data_val hbt
  have hi7lt : i7.val < 32768 := by
    by_cases hc : i6.val = ConLeche.satRange
    · rw [e7, if_pos hc]; simp [ConLeche.satRange]
    · rw [e7, if_neg hc]; omega
  have hr8 : i8.val < 32768 := by omega
  have hr11 : i11.val < 32768 := by omega
  have hsp : (ConLeche.satPred (ConLeche.bvarOfData (ls.derived (absEIdx bo)))).toNat
      = i7.val := by
    rw [satPred_toNat, hbB, ← e6, e7]
    by_cases hc : i6.val = ConLeche.satRange
    · rw [if_pos hc, if_pos (show i6.val = 32767 from hc)]; rfl
    · rw [if_neg hc, if_neg (show ¬ (i6.val = 32767) from hc)]
  rw [EStore.derOfBindAtI, derOfBind]
  refine derObsE_pack _ ?_ ?_ ?_ hr8 hr11 h
  · rw [ConLeche.toNat_max, hsp, hbT]; omega
  · rw [ConLeche.toNat_max, hfT, hfB]; omega
  · rw [hlT, hlB, hpm]
    by_cases hc : bt = true
    · rw [if_pos hc] at hpm1
      have hp' : pm1 = true := (Result.ok_injective hpm1).symm
      have hdt1 : dt.val % 2 = 1 := by
        have h' : (dt.val % 2 == 1) = true := by rw [← ebT]; exact hc
        simpa using h'
      rw [hp', hdt1]; simp
    · rw [if_neg hc] at hpm1
      obtain ⟨b2, hb2, hpm1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hpm1
      have ebB := ConRon.Refine.Expr.lp_of_data_val hb2
      have hdt0 : ¬ (dt.val % 2 = 1) := by
        intro hcc; exact hc (by rw [ebT]; simpa using hcc)
      simp only [decide_eq_false hdt0, Bool.false_or]
      by_cases hc2 : b2 = true
      · rw [if_pos hc2] at hpm1
        have hp' : pm1 = true := (Result.ok_injective hpm1).symm
        have hdb1 : db.val % 2 = 1 := by
          have h' : (db.val % 2 == 1) = true := by rw [← ebB]; exact hc2
          simpa using h'
        rw [hp', hdb1]; simp
      · rw [if_neg hc2] at hpm1
        have hp' : pm1 = pm := (Result.ok_injective hpm1).symm
        have hdb0 : ¬ (db.val % 2 = 1) := by
          intro hcc; exact hc2 (by rw [ebB]; simpa using hcc)
        simp only [decide_eq_false hdb0, Bool.false_or, hp']


/-- `arena::store::EStore.intern_lam_i` against `EStore.internLamI` — the
binder arm at a datum HANDLE (task #97-P6-16).  Three children, the third a
`BMIdx`, so finding 7's `sk` disjunction has three arms; the twin's
`findBind`/`pushBind` are the tag's own array by `rfl`. -/
theorem estore_intern_lam_i_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {ty bo : arena.handle.EIdx} {mi : arena.handle.BMIdx}
    (hchild : ((absEIdx ty).isPersistent = false ∨
        (absEIdx bo).isPersistent = false ∨ (absBMIdx mi).isPersistent = false) →
      ls.pers.lams.find? ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_lam_i rs pers ty bo mi = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.internLamI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).2 ∧
        StoreRel pers rs' (ls.internLamI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_lam_i] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧ (sk = true →
      (absEIdx ty).isPersistent = false ∨ (absEIdx bo).isPersistent = false ∨
        (absBMIdx mi).isPersistent = false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := eidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      intro hsk
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := eidx_is_persistent_abs hb3
        split at hb2 <;> rename_i hbb2
        · obtain ⟨b4, hb4, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
          have hp4 := bmidx_is_persistent_abs hb4
          simp only [Result.ok.injEq] at hb2
          right; right; rw [hp4]; rw [← e2, ← hb2] at hsk; simpa using hsk
        · simp only [Result.ok.injEq] at hb2
          right; left; rw [hp3]; simpa using hbb2
      · simp only [Result.ok.injEq] at hb2
        left; rw [hp1]; simpa using hbb
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      intro hsk; rw [← e2] at hsk; simp at hsk
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.pers.lams.find? ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4]; simpa using hchild (hskp hsk)⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.lams hinv.perst.lams bind_eq2 dupId_eidx
          (P := BindNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.lams hinv.perst.lams bind_eq2 dupId_eidx
          (P := BindNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  simp only [EStore.internLamI, EStore.internBindI]
  have hfind : ls.pers.findBind ETag.lam ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩
      = ls.pers.lams.find? ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ := rfl
  rw [hfind, hE4]
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
        tbl_find_slot_abs hrel.scrt.lams hinv.scrt.lams bind_eq2 dupId_bindnode
          dupId_eidx absBindNode_inj (P := BindNodeWF) trivial hfs
      have hfind2 : ls.scr.findBind ETag.lam ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩
          = ls.scr.lams.find? ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ := rfl
      simp only [absBindNode] at hfindT
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
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with lams := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lams := hinvT }⟩⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
          have hrelS : StoreRel pers
              { rs with scr := { rs.scr with lams := t }, scratch_on := true } ls :=
            ⟨hrel.lss, hrel.perst, { hrel.scrt with lams := hrelT },
              hrel.scratchOn.trans hsc⟩
          have hinvS : StoreInv pers
              { rs with scr := { rs.scr with lams := t }, scratch_on := true } :=
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lams := hinvT }⟩
          have hhandle : absEIdx hnew
              = Idx.mk ETag.lam Idx.tierS (UInt32.ofNat ls.scr.lams.size) := by
            rw [eidx_pack_abs hpk, etag_lam_abs, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          have hder := der_of_bind_i_obs (ls := ls) hrelS hinvS hd
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d _ hder hnew t1 ht1
          simp only [absBindNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with lams := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lams := hinv1 }⟩⟩
    · -- the persistent tier
      rw [if_neg hsc]
      have hsh : rs.shared_on = false := by
        by_contra hc
        exact hsc (hfrozen (by simpa using hc))
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
        have hrelP : TblRel BindNodeWF absBindNode absEIdx absU64 derObsE
            rs.pers.lams ls.pers.lams := by rw [← hpersE]; exact hrel.perst.lams
        have hinvP : TblInv
            arena.store.BindNode.Insts.Con_ron_coreRonHashmapHashable
            BindNodeWF rs.pers.lams := by
          rw [← hpersE]; exact hinv.perst.lams
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        have hrelS : StoreRel pers
            { rs with scratch_on := false, shared_on := false } ls := by
          refine ⟨hrel.lss, ?_, hrel.scrt, ?_⟩
          · show ETablesRel (rPersE pers { rs with scratch_on := false, shared_on := false })
              ls.pers
            unfold rPersE; rw [if_neg (by simp)]; exact hrelPerst
          · rw [hrel.scratchOn]; simpa using hsc
        have hinvS : StoreInv pers
            { rs with scratch_on := false, shared_on := false } := by
          refine ⟨hinv.lss, ?_, hinv.scrt⟩
          show ETablesInv (rPersE pers { rs with scratch_on := false, shared_on := false })
          unfold rPersE; rw [if_neg (by simp)]; exact hinvPerst
        have hhandle : absEIdx hnew
            = Idx.mk ETag.lam Idx.tierP (UInt32.ofNat ls.pers.lams.size) := by
          rw [eidx_pack_abs hpk, etag_lam_abs, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        have hder := der_of_bind_i_obs (ls := ls) hrelS hinvS hd
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP bind_eq2 dupId_bindnode absBindNode_inj
            (P := BindNodeWF) trivial hder ht1
        simp only [absBindNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with lams := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with lams := hinv1 }


/-! ## The node records: `Dup` is the identity, and `abs` is injective

Two obligations per constructor array, which `tbl_find_slot_abs` and
`tbl_push_abs` take: the port's `Dup::dup2` gives the value back (it is a
field-wise copy through the handles' own `dup2`), and the record's
abstraction is injective on well-formed records — the four that carry a
CACHED VALUE (`StrNode`'s code points, `ListNode`'s handle vector, `LitNode`'s
`Literal`, `BMNode`'s `PropWhen`) are the reason `TblRel` is `RelOn P`. -/


/-- `arena::store::EStore.intern_forall_e_i` against `EStore.internForallEI` — the
binder arm at a datum HANDLE (task #97-P6-16).  Three children, the third a
`BMIdx`, so finding 7's `sk` disjunction has three arms; the twin's
`findBind`/`pushBind` are the tag's own array by `rfl`. -/
theorem estore_intern_forall_e_i_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    (hfrozen : rs.shared_on = true → rs.scratch_on = true)
    {ty bo : arena.handle.EIdx} {mi : arena.handle.BMIdx}
    (hchild : ((absEIdx ty).isPersistent = false ∨
        (absEIdx bo).isPersistent = false ∨ (absBMIdx mi).isPersistent = false) →
      ls.pers.foralls.find? ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_forall_e_i rs pers ty bo mi = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.internForallEI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).2 ∧
        StoreRel pers rs' (ls.internForallEI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).1 ∧
        StoreInv pers rs') ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_forall_e_i] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧ (sk = true →
      (absEIdx ty).isPersistent = false ∨ (absEIdx bo).isPersistent = false ∨
        (absBMIdx mi).isPersistent = false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := eidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      intro hsk
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := eidx_is_persistent_abs hb3
        split at hb2 <;> rename_i hbb2
        · obtain ⟨b4, hb4, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
          have hp4 := bmidx_is_persistent_abs hb4
          simp only [Result.ok.injEq] at hb2
          right; right; rw [hp4]; rw [← e2, ← hb2] at hsk; simpa using hsk
        · simp only [Result.ok.injEq] at hb2
          right; left; rw [hp3]; simpa using hbb2
      · simp only [Result.ok.injEq] at hb2
        left; rw [hp1]; simpa using hbb
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      intro hsk; rw [← e2] at hsk; simp at hsk
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.pers.foralls.find? ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4]; simpa using hchild (hskp hsk)⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.foralls hinv.perst.foralls bind_eq2 dupId_eidx
          (P := BindNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.foralls hinv.perst.foralls bind_eq2 dupId_eidx
          (P := BindNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  simp only [EStore.internForallEI, EStore.internBindI]
  have hfind : ls.pers.findBind ETag.forallE ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩
      = ls.pers.foralls.find? ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ := rfl
  rw [hfind, hE4]
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
        tbl_find_slot_abs hrel.scrt.foralls hinv.scrt.foralls bind_eq2 dupId_bindnode
          dupId_eidx absBindNode_inj (P := BindNodeWF) trivial hfs
      have hfind2 : ls.scr.findBind ETag.forallE ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩
          = ls.scr.foralls.find? ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ := rfl
      simp only [absBindNode] at hfindT
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
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with foralls := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with foralls := hinvT }⟩⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
          have hrelS : StoreRel pers
              { rs with scr := { rs.scr with foralls := t }, scratch_on := true } ls :=
            ⟨hrel.lss, hrel.perst, { hrel.scrt with foralls := hrelT },
              hrel.scratchOn.trans hsc⟩
          have hinvS : StoreInv pers
              { rs with scr := { rs.scr with foralls := t }, scratch_on := true } :=
            ⟨hinv.lss, hinv.perst, { hinv.scrt with foralls := hinvT }⟩
          have hhandle : absEIdx hnew
              = Idx.mk ETag.forallE Idx.tierS (UInt32.ofNat ls.scr.foralls.size) := by
            rw [eidx_pack_abs hpk, etag_forallE_abs, tier_s_abs, cast_u32_size hn3,
              tbl_size_abs hrelT hn2]
          have hder := der_of_bind_i_obs (ls := ls) hrelS hinvS hd
          obtain ⟨hrel1, hinv1⟩ :=
            hpushT hoc d _ hder hnew t1 ht1
          simp only [absBindNode] at hrel1
          rw [hhandle] at hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with foralls := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with foralls := hinv1 }⟩⟩
    · -- the persistent tier
      rw [if_neg hsc]
      have hsh : rs.shared_on = false := by
        by_contra hc
        exact hsc (hfrozen (by simpa using hc))
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
        have hrelP : TblRel BindNodeWF absBindNode absEIdx absU64 derObsE
            rs.pers.foralls ls.pers.foralls := by rw [← hpersE]; exact hrel.perst.foralls
        have hinvP : TblInv
            arena.store.BindNode.Insts.Con_ron_coreRonHashmapHashable
            BindNodeWF rs.pers.foralls := by
          rw [← hpersE]; exact hinv.perst.foralls
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        have hrelS : StoreRel pers
            { rs with scratch_on := false, shared_on := false } ls := by
          refine ⟨hrel.lss, ?_, hrel.scrt, ?_⟩
          · show ETablesRel (rPersE pers { rs with scratch_on := false, shared_on := false })
              ls.pers
            unfold rPersE; rw [if_neg (by simp)]; exact hrelPerst
          · rw [hrel.scratchOn]; simpa using hsc
        have hinvS : StoreInv pers
            { rs with scratch_on := false, shared_on := false } := by
          refine ⟨hinv.lss, ?_, hinv.scrt⟩
          show ETablesInv (rPersE pers { rs with scratch_on := false, shared_on := false })
          unfold rPersE; rw [if_neg (by simp)]; exact hinvPerst
        have hhandle : absEIdx hnew
            = Idx.mk ETag.forallE Idx.tierP (UInt32.ofNat ls.pers.foralls.size) := by
          rw [eidx_pack_abs hpk, etag_forallE_abs, tier_p_abs, cast_u32_size hn3,
            tbl_size_abs hrelP hn2]
        have hder := der_of_bind_i_obs (ls := ls) hrelS hinvS hd
        obtain ⟨hrel1, hinv1⟩ :=
          tbl_push_abs hrelP hinvP bind_eq2 dupId_bindnode absBindNode_inj
            (P := BindNodeWF) trivial hder ht1
        simp only [absBindNode] at hrel1
        rw [hhandle] at hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with foralls := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with foralls := hinv1 }


/-! ## The node records: `Dup` is the identity, and `abs` is injective

Two obligations per constructor array, which `tbl_find_slot_abs` and
`tbl_push_abs` take: the port's `Dup::dup2` gives the value back (it is a
field-wise copy through the handles' own `dup2`), and the record's
abstraction is injective on well-formed records — the four that carry a
CACHED VALUE (`StrNode`'s code points, `ListNode`'s handle vector, `LitNode`'s
`Literal`, `BMNode`'s `PropWhen`) are the reason `TblRel` is `RelOn P`. -/


/-- `arena::monad::intern_e_fvar` against `internFVarE`. -/
theorem intern_e_fvar_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (idx : Std.U64) (ty : arena.handle.EIdx)
    (hchild : (absEIdx ty).isPersistent = false →
      lst.store.pers.fvars.find? ⟨absU idx, absEIdx ty⟩ = none)
    (hcap : lst.store.find? (.fvar (absU idx) (absEIdx ty)) = none →
      (if lst.store.scratchOn
        then lst.store.scr.sizeOf (.fvar (absU idx) (absEIdx ty))
        else lst.store.pers.sizeOf (.fvar (absU idx) (absEIdx ty))) < Idx.idxCap)
    {o}
    (hrun : arena.monad.intern_e_fvar pers st idx ty = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internFVarE (absU idx) (absEIdx ty)) := by
  rw [arena.monad.intern_e_fvar] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_fvar_abs (ls := lst.store) hrel.store hinv.store hfrozen hchild hp
  show AOut absEIdx (fun _ => True) pers lst r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv'⟩ := hok hh hr
    refine AOut.ok
      (lst' := { lst with store := (lst.store.intern (.fvar (absU idx) (absEIdx ty))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
      (EStore.intern_ext _ _) trivial
    rw [Arena.internFVarE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_e_sort` against `internSortE`. -/
theorem intern_e_sort_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (u : arena.handle.LIdx)
    (hchild : (absLIdx u).isPersistent = false →
      lst.store.pers.sorts.find? ⟨absLIdx u⟩ = none)
    (hcap : lst.store.find? (.sort (absLIdx u)) = none →
      (if lst.store.scratchOn
        then lst.store.scr.sizeOf (.sort (absLIdx u))
        else lst.store.pers.sizeOf (.sort (absLIdx u))) < Idx.idxCap)
    {o}
    (hrun : arena.monad.intern_e_sort pers st u = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internSortE (absLIdx u)) := by
  rw [arena.monad.intern_e_sort] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_sort_abs (ls := lst.store) hrel.store hinv.store hfrozen hchild hp
  show AOut absEIdx (fun _ => True) pers lst r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv'⟩ := hok hh hr
    refine AOut.ok
      (lst' := { lst with store := (lst.store.intern (.sort (absLIdx u))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
      (EStore.intern_ext _ _) trivial
    rw [Arena.internSortE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_e_const` against `internConstE`. -/
theorem intern_e_const_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (n : arena.handle.NIdx) (us : arena.handle.LsIdx)
    (hchild : ((absNIdx n).isPersistent = false ∨ (absLsIdx us).isPersistent = false) →
      lst.store.pers.consts.find? ⟨absNIdx n, absLsIdx us⟩ = none)
    (hcap : lst.store.find? (.const (absNIdx n) (absLsIdx us)) = none →
      (if lst.store.scratchOn
        then lst.store.scr.sizeOf (.const (absNIdx n) (absLsIdx us))
        else lst.store.pers.sizeOf (.const (absNIdx n) (absLsIdx us))) < Idx.idxCap)
    {o}
    (hrun : arena.monad.intern_e_const pers st n us = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internConstE (absNIdx n) (absLsIdx us)) := by
  rw [arena.monad.intern_e_const] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_const_abs (ls := lst.store) hrel.store hinv.store hfrozen hchild hp
  show AOut absEIdx (fun _ => True) pers lst r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv'⟩ := hok hh hr
    refine AOut.ok
      (lst' := { lst with store := (lst.store.intern (.const (absNIdx n) (absLsIdx us))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
      (EStore.intern_ext _ _) trivial
    rw [Arena.internConstE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_e_app` against `internAppE`. -/
theorem intern_e_app_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (f a : arena.handle.EIdx)
    (hchild : ((absEIdx f).isPersistent = false ∨ (absEIdx a).isPersistent = false) →
      lst.store.pers.apps.find? ⟨absEIdx f, absEIdx a⟩ = none)
    (hcap : lst.store.find? (.app (absEIdx f) (absEIdx a)) = none →
      (if lst.store.scratchOn
        then lst.store.scr.sizeOf (.app (absEIdx f) (absEIdx a))
        else lst.store.pers.sizeOf (.app (absEIdx f) (absEIdx a))) < Idx.idxCap)
    {o}
    (hrun : arena.monad.intern_e_app pers st f a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internAppE (absEIdx f) (absEIdx a)) := by
  rw [arena.monad.intern_e_app] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_app_abs (ls := lst.store) hrel.store hinv.store hfrozen hchild hp
  show AOut absEIdx (fun _ => True) pers lst r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv'⟩ := hok hh hr
    refine AOut.ok
      (lst' := { lst with store := (lst.store.intern (.app (absEIdx f) (absEIdx a))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
      (EStore.intern_ext _ _) trivial
    rw [Arena.internAppE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_e_let_e` against `internLetEE`. -/
theorem intern_e_let_e_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (ty val bo : arena.handle.EIdx)
    (hchild : ((absEIdx ty).isPersistent = false ∨ (absEIdx val).isPersistent = false ∨ (absEIdx bo).isPersistent = false) →
      lst.store.pers.lets.find? ⟨absEIdx ty, absEIdx val, absEIdx bo⟩ = none)
    (hcap : lst.store.find? (.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) = none →
      (if lst.store.scratchOn
        then lst.store.scr.sizeOf (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))
        else lst.store.pers.sizeOf (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))) < Idx.idxCap)
    {o}
    (hrun : arena.monad.intern_e_let_e pers st ty val bo = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internLetEE (absEIdx ty) (absEIdx val) (absEIdx bo)) := by
  rw [arena.monad.intern_e_let_e] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_let_e_abs (ls := lst.store) hrel.store hinv.store hfrozen hchild hp
  show AOut absEIdx (fun _ => True) pers lst r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv'⟩ := hok hh hr
    refine AOut.ok
      (lst' := { lst with store := (lst.store.intern (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
      (EStore.intern_ext _ _) trivial
    rw [Arena.internLetEE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_e_proj` against `internProjE`. -/
theorem intern_e_proj_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (n : arena.handle.NIdx) (i : Std.U64) (ep : arena.handle.EIdx)
    (hchild : ((absNIdx n).isPersistent = false ∨ (absEIdx ep).isPersistent = false) →
      lst.store.pers.projs.find? ⟨absNIdx n, absU i, absEIdx ep⟩ = none)
    (hcap : lst.store.find? (.proj (absNIdx n) (absU i) (absEIdx ep)) = none →
      (if lst.store.scratchOn
        then lst.store.scr.sizeOf (.proj (absNIdx n) (absU i) (absEIdx ep))
        else lst.store.pers.sizeOf (.proj (absNIdx n) (absU i) (absEIdx ep))) < Idx.idxCap)
    {o}
    (hrun : arena.monad.intern_e_proj pers st n i ep = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internProjE (absNIdx n) (absU i) (absEIdx ep)) := by
  rw [arena.monad.intern_e_proj] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_proj_abs (ls := lst.store) hrel.store hinv.store hfrozen hchild hp
  show AOut absEIdx (fun _ => True) pers lst r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv'⟩ := hok hh hr
    refine AOut.ok
      (lst' := { lst with store := (lst.store.intern (.proj (absNIdx n) (absU i) (absEIdx ep))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
      (EStore.intern_ext _ _) trivial
    rw [Arena.internProjE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_e_lit` against `internLitE`. -/
theorem intern_e_lit_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (l : kernel.expr.Literal)
    (hwf : ConRon.Refine.LiteralWF l)
    (hcap : lst.store.find? (.lit (ConRon.Refine.absLiteral l)) = none →
      (if lst.store.scratchOn
        then lst.store.scr.sizeOf (.lit (ConRon.Refine.absLiteral l))
        else lst.store.pers.sizeOf (.lit (ConRon.Refine.absLiteral l))) < Idx.idxCap)
    {o}
    (hrun : arena.monad.intern_e_lit pers st l = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internLitE (ConRon.Refine.absLiteral l)) := by
  rw [arena.monad.intern_e_lit] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_lit_abs (ls := lst.store) hrel.store hinv.store hfrozen hwf hp
  show AOut absEIdx (fun _ => True) pers lst r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv'⟩ := hok hh hr
    refine AOut.ok
      (lst' := { lst with store := (lst.store.intern (.lit (ConRon.Refine.absLiteral l))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
      (EStore.intern_ext _ _) trivial
    rw [Arena.internLitE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut.err (AErrSim.of_none (herr ee hr))

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



/-! ## The axiom census, task #97-P5-2

Forty-one more rows, over the ten expression arrays `intern` gained this
round, the `der_of_*` family that feeds them and the probe-first `internE`
that finding 9's twin fix (task #97-P3-1) made statable.  Every one reads
`[propext, Classical.choice, Quot.sound]` and nothing else — no `sorryAx` on
a closed lemma, and still no `bv_decide` axiom anywhere, which the handle
packing's `*`/`/`/`%` spelling is what buys. -/

/-- info: 'ConRon.Refine2.lstables_der_at_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lstables_der_at_abs

/-- info: 'ConRon.Refine2.lsstore_derived_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lsstore_derived_abs

/-- info: 'ConRon.Refine2.estore_lder_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_lder_obs

/-- info: 'ConRon.Refine2.estore_lsder_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_lsder_obs

/-- info: 'ConRon.Refine2.derObsE_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms derObsE_pack

/-- info: 'ConRon.Refine2.derObsE_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms derObsE_fields

/-- info: 'ConRon.Refine2.satPred_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms satPred_toNat

/-- info: 'ConRon.Refine2.der_of_fvar_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms der_of_fvar_obs

/-- info: 'ConRon.Refine2.der_of_sort_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms der_of_sort_obs

/-- info: 'ConRon.Refine2.der_of_const_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms der_of_const_obs

/-- info: 'ConRon.Refine2.der_of_lit_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms der_of_lit_obs

/-- info: 'ConRon.Refine2.der_of_proj_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms der_of_proj_obs

/-- info: 'ConRon.Refine2.der_of_app_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms der_of_app_obs

/-- info: 'ConRon.Refine2.der_of_let_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms der_of_let_obs

/-- info: 'ConRon.Refine2.etables_get_bm_der_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms etables_get_bm_der_abs

/-- info: 'ConRon.Refine2.estore_bm_der_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_bm_der_abs

/-- info: 'ConRon.Refine2.der_of_bind_i_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms der_of_bind_i_obs

/-- info: 'ConRon.Refine2.tbl_node_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tbl_node_wf

/-- info: 'ConRon.Refine2.dupId_fvarnode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dupId_fvarnode

/-- info: 'ConRon.Refine2.absFVarNode_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms absFVarNode_inj

/-- info: 'ConRon.Refine2.dupId_litnode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dupId_litnode

/-- info: 'ConRon.Refine2.absLitNode_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms absLitNode_inj

/-- info: 'ConRon.Refine2.dupId_bmnode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dupId_bmnode

/-- info: 'ConRon.Refine2.absBMNode_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms absBMNode_inj

/-- info: 'ConRon.Refine2.estore_intern_fvar_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_fvar_abs

/-- info: 'ConRon.Refine2.estore_intern_sort_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_sort_abs

/-- info: 'ConRon.Refine2.estore_intern_const_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_const_abs

/-- info: 'ConRon.Refine2.estore_intern_app_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_app_abs

/-- info: 'ConRon.Refine2.estore_intern_proj_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_proj_abs

/-- info: 'ConRon.Refine2.estore_intern_let_e_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_let_e_abs

/-- info: 'ConRon.Refine2.estore_intern_lit_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_lit_abs

/-- info: 'ConRon.Refine2.estore_intern_lam_i_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_lam_i_abs

/-- info: 'ConRon.Refine2.estore_intern_forall_e_i_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_forall_e_i_abs

/-- info: 'ConRon.Refine2.estore_intern_bm_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_bm_abs

/-- info: 'ConRon.Refine2.run_get_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_get_bind

/-- info: 'ConRon.Refine2.view_run_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_run_state

/-- info: 'ConRon.Refine2.internBM_of_findBM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internBM_of_findBM

/-- info: 'ConRon.Refine2.internBMOfView_of_findBMOfView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internBMOfView_of_findBMOfView

/-- info: 'ConRon.Refine2.internAt_of_findAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internAt_of_findAt

/-- info: 'ConRon.Refine2.intern_of_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_of_find

/-- info: 'ConRon.Refine2.internE_run_of_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internE_run_of_cap

/-- info: 'ConRon.Refine2.intern_e_fvar_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_fvar_run

/-- info: 'ConRon.Refine2.intern_e_sort_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_sort_run

/-- info: 'ConRon.Refine2.intern_e_const_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_const_run

/-- info: 'ConRon.Refine2.intern_e_app_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_app_run

/-- info: 'ConRon.Refine2.intern_e_let_e_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_let_e_run

/-- info: 'ConRon.Refine2.intern_e_lit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_lit_run

/-- info: 'ConRon.Refine2.intern_e_proj_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_proj_run

end ConRon.Refine2
