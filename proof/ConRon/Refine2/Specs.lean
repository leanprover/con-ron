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
import ConRon.Arena.PersistentRun

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn toFun sl_v)

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

omit [LawfulBEq α] [LawfulHashable α] in
/-- **`Tbl::full = false` IS the twin's capacity test** — task #97-P5-3
round 2's finding 14, second half, mechanised.  The port tests
`self.rows.len() >= IDX_CAP` before it appends and `TblRel` equates the two
lengths, so the port's own `false` answer proves the twin's
`< Idx.idxCap`.  This is the lemma that turns `hcap` from a HYPOTHESIS of the
eight non-binder `intern_e_*_run` into a CONCLUSION of the
`estore_intern_*_abs` beneath them, which is what lets an interning walk —
whose intermediate states no caller can name — be stated at all. -/
theorem tbl_not_full_size (hrel : TblRel P absA absI absD obsD rt lt) {b : Bool}
    (h : arena.store.Tbl.full hH hE hDA hDI hDD hDf rt = ok b) (hb : ¬ (b = true)) :
    lt.size < Idx.idxCap := by
  have hbf : b = false := by simpa using hb
  subst hbf
  rw [arena.store.Tbl.full] at h
  obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [lift, Result.ok.injEq] at hi1
  subst hi1
  split at h <;> rename_i hge
  · simp at h
  · have hlen : (alloc.vec.Vec.len rt.rows).val = lt.size := by
      show rt.rows.val.length = lt.nodes.size
      rw [← Array.length_toList, hrel.nodes, List.length_map]
    have hcap : (UScalar.cast .Usize arena.handle.IDX_CAP).val = Idx.idxCap := by
      rw [Std.U32.cast_Usize_val_eq, arena.handle.IDX_CAP]; rfl
    have hlt : (alloc.vec.Vec.len rt.rows).val
        < (UScalar.cast .Usize arena.handle.IDX_CAP).val := by
      simpa using hge
    omega

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

/-! ## Finding 14's two side conditions, as CONCLUSIONS (task #97-P5-3 round 3)

Task #97-P5-3 round 2's **finding 14**: what gates an interning WALK is not a
missing `Arena/` primitive but the QUANTIFIER of the two side conditions every
`intern_e_*_run` carries.  A one-node wrapper's caller can name the state the
call is made at and discharge them; a walk interns at states it created two
recursive calls ago and cannot.  The fix is to stop asking:

* **`hcap` is the port's own business** and `tbl_not_full_size` above says so —
  the port tests the same bound before it appends, so its success proves the
  twin's.  `ECapAt` names the predicate so it can travel as a conjunct of the
  `estore_intern_*_abs` success arm rather than as a hypothesis of the wrapper.
* **`hchild` is free at a well-formed store** — `EWFAt.consP` says a
  persistent cons hit decodes to a PERSISTENT node and `childOK` says a
  persistent node's children are persistent, so a view with a scratch child is
  not in the persistent table.  One generic lemma per child kind, and the six
  per-constructor corollaries below are `rfl` on top of them.

The two BINDER arrays used to be the one place this did NOT reach, because of
a twin debt task #97-P5-2 §10 booked and task #97-P5-3 round 3 stated as
**finding 15**: `Arena/Monad.lean`'s `internLamIE` / `internForallEIE` tested
capacity BEFORE the cons probe (and on BOTH tiers), so on a cons hit at a full
array the twin failed where the port answers `Ok` and no hypothesis-free
statement was true.  **Task #97-P5-Twin fixed the twin** — they probe
`EStore.findBindI` first and test the one tier the append goes to — so
`EBindCapAt` below is `ECapAt` at those two arrays, and it is a side condition
of the MISS path like every other. -/

/-- The capacity side condition the probe-first `Arena.internE` tests on its
MISS path (task #97-P5-2 finding 9's replacement), named so that it can be
CONCLUDED rather than assumed. -/
def ECapAt (st : EStore) (v : ENodeView) : Prop :=
  st.find? v = none →
    (if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap

/-- `ECapAt` is VACUOUS wherever the port's cons probe hit: the twin's own
`find?` answers `some` at the same view, and the side condition is on the miss
path. -/
theorem ECapAt.of_find_ne {st : EStore} {v : ENodeView} (h : st.find? v ≠ none) :
    ECapAt st v := fun hn => absurd hn h

/-- `find?`'s two steps, at a view whose datum handle is already known: the
persistent probe answers, so the whole probe answers. -/
theorem find?_eq_of_pers {st : EStore} {v : ENodeView} {mi : BMIdx} {j : EIdx}
    (hbm : st.findBMOfView v = some mi) (hp : st.persFindMaybe v mi = some j) :
    st.find? v = some j := by
  simp only [EStore.find?, hbm, EStore.findAt, hp]

/-- `find?`'s two steps, the scratch half. -/
theorem find?_eq_of_scr {st : EStore} {v : ENodeView} {mi : BMIdx} {j : EIdx}
    (hbm : st.findBMOfView v = some mi) (hp : st.persFindMaybe v mi = none)
    (hon : st.scratchOn = true) (hs : st.scr.find? v mi = some j) :
    st.find? v = some j := by
  simp only [EStore.find?, hbm, EStore.findAt, hp, hon, if_true, hs]

/-- `ECapAt` on the SCRATCH append arm: the port's `Tbl::full` answered
`false` at the scratch array, which `tbl_not_full_size` reads as the twin's
own bound. -/
theorem ECapAt.of_scr_size {st : EStore} {v : ENodeView} (hon : st.scratchOn = true)
    (h : st.scr.sizeOf v < Idx.idxCap) : ECapAt st v := by
  intro _; rw [if_pos hon]; exact h

/-- `ECapAt` on the PERSISTENT append arm. -/
theorem ECapAt.of_pers_size {st : EStore} {v : ENodeView} (hoff : st.scratchOn = false)
    (h : st.pers.sizeOf v < Idx.idxCap) : ECapAt st v := by
  intro _; rw [if_neg (by rw [hoff]; simp)]; exact h

/-- `ECapAt` at the two BINDER arrays (task #97-P5-Twin).  The cons key there
is the datum's HANDLE, so the twin's probe is `EStore.findBindI` rather than
`EStore.find?` and the array is picked by the tag; everything else is
`ECapAt`'s own shape — the bound is tested only on the MISS, and only at the
tier the append goes to. -/
def EBindCapAt (st : EStore) (tag : UInt32) (ty b : EIdx) (mi : BMIdx) : Prop :=
  st.findBindI tag ty b mi = none →
    (if st.scratchOn then st.scr.bindSizeOf tag else st.pers.bindSizeOf tag)
      < Idx.idxCap

/-- `EBindCapAt` is VACUOUS wherever the binder cons probe hit. -/
theorem EBindCapAt.of_find_ne {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} (h : st.findBindI tag ty b mi ≠ none) :
    EBindCapAt st tag ty b mi := fun hn => absurd hn h

/-- `EBindCapAt` on the SCRATCH append arm. -/
theorem EBindCapAt.of_scr_size {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} (hon : st.scratchOn = true)
    (h : st.scr.bindSizeOf tag < Idx.idxCap) : EBindCapAt st tag ty b mi := by
  intro _; rw [if_pos hon]; exact h

/-- `EBindCapAt` on the PERSISTENT append arm. -/
theorem EBindCapAt.of_pers_size {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} (hoff : st.scratchOn = false)
    (h : st.pers.bindSizeOf tag < Idx.idxCap) : EBindCapAt st tag ty b mi := by
  intro _; rw [if_neg (by rw [hoff]; simp)]; exact h

/-! ### Finding 14's first half and the six per-constructor `hchild_*` corollaries

Moved to `Arena/WFSkip.lean` (task #97-T2-LOCKSTEP D2), statements unchanged:
they are Theorem 1's (`StoreWF`), and since D2 the twin skips the persistent
probe exactly where the Rust does, so no `estore_intern_*_abs` needs them. -/

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

/-! ### From the lockstep outcome back to the deprecated one, at a reader

Task #97-T2-LOCKSTEP: the `₀` lemmas are the statements; a deprecated `AOut`/
`Sim`/`SimS` shim is the `₀` lemma plus the twin's two facts about its own run
(`Sim₀.toSim`).  At a twin action that leaves the STORE alone — a reader, a
memo or cache write — those facts are the pre-state's `StoreWF` and
`Ext.refl`, which is all these two say. -/

theorem AOut₀.toAOut_of_store {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst : AState} {o : core.result.Result α kernel.core_types.CheckError}
    {st' : arena.monad.AState} {x : Except Arena.CheckError (β × AState)}
    (h : AOut₀ A pers o st' x) (hwf : StoreWF lst.store)
    (hx : ∀ b lst', x = .ok (b, lst') → lst'.store = lst.store) :
    AOut A (fun _ => True) pers lst o st' x := by
  cases o with
  | Err e => exact h
  | Ok r =>
    obtain ⟨lst', hx', h1, h2⟩ := h
    have hs := hx _ _ hx'
    exact ⟨lst', hx', h1.of₀ (by rw [hs]; exact hwf), h2,
      by rw [hs]; exact Ext.refl _, trivial⟩

theorem Sim₀.toSim_of_store {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst : AState}
    {o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState}
    {x : AM β} (h : Sim₀ A pers lst o x) (hwf : StoreWF lst.store)
    (hx : ∀ b lst', x.run lst = .ok (b, lst') → lst'.store = lst.store) :
    Sim A (fun _ => True) pers lst o x :=
  AOut₀.toAOut_of_store h hwf hx

/-- `arena::monad::view_app` against `Arena.viewApp`. -/
@[grind →] theorem view_app_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_app pers st h = ok o) :
    SimR (Option.map absPairE) lst o (Arena.viewApp (absEIdx h)) := by
  rw [arena.monad.view_app] at hrun
  show (Arena.viewApp (absEIdx h)).run lst = _
  rw [show (Arena.viewApp (absEIdx h)).run lst
        = .ok (lst.store.viewApp (absEIdx h), lst) from rfl,
    estore_view_app_abs hrel.store hrun]

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_app_run₀`. -/
@[grind →] theorem view_app_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_app pers st h = ok o) :
    SimR (Option.map absPairE) lst o (Arena.viewApp (absEIdx h)) := by
  apply view_app_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::view_sort` against `Arena.viewSort`. -/
@[grind →] theorem view_sort_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_sort pers st h = ok o) :
    SimR (Option.map absLIdx) lst o (Arena.viewSort (absEIdx h)) := by
  rw [arena.monad.view_sort] at hrun
  show (Arena.viewSort (absEIdx h)).run lst = _
  rw [show (Arena.viewSort (absEIdx h)).run lst
        = .ok (lst.store.viewSort (absEIdx h), lst) from rfl,
    estore_view_sort_abs hrel.store hrun]

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_sort_run₀`. -/
@[grind →] theorem view_sort_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_sort pers st h = ok o) :
    SimR (Option.map absLIdx) lst o (Arena.viewSort (absEIdx h)) := by
  apply view_sort_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::view_const` against `Arena.viewConst`. -/
@[grind →] theorem view_const_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_const pers st h = ok o) :
    SimR (Option.map absConstT) lst o (Arena.viewConst (absEIdx h)) := by
  rw [arena.monad.view_const] at hrun
  show (Arena.viewConst (absEIdx h)).run lst = _
  rw [show (Arena.viewConst (absEIdx h)).run lst
        = .ok (lst.store.viewConst (absEIdx h), lst) from rfl,
    estore_view_const_abs hrel.store hrun]

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_const_run₀`. -/
@[grind →] theorem view_const_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_const pers st h = ok o) :
    SimR (Option.map absConstT) lst o (Arena.viewConst (absEIdx h)) := by
  apply view_const_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::view_const_name` against `Arena.viewConstName`. -/
@[grind →] theorem view_const_name_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_const_name pers st h = ok o) :
    SimR (Option.map absNIdx) lst o (Arena.viewConstName (absEIdx h)) := by
  rw [arena.monad.view_const_name] at hrun
  show (Arena.viewConstName (absEIdx h)).run lst = _
  rw [show (Arena.viewConstName (absEIdx h)).run lst
        = .ok (lst.store.viewConstName (absEIdx h), lst) from rfl,
    estore_view_const_name_abs hrel.store hrun]

/-- `arena::monad::view_bvar` against `Arena.viewBVar`. -/
@[grind →] theorem view_bvar_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_bvar pers st h = ok o) :
    SimR (Option.map absU) lst o (Arena.viewBVar (absEIdx h)) := by
  rw [arena.monad.view_bvar] at hrun
  show (Arena.viewBVar (absEIdx h)).run lst = _
  rw [show (Arena.viewBVar (absEIdx h)).run lst
        = .ok (lst.store.viewBVar (absEIdx h), lst) from rfl,
    estore_view_bvar_abs hrel.store hrun]

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_bvar_run₀`. -/
@[grind →] theorem view_bvar_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_bvar pers st h = ok o) :
    SimR (Option.map absU) lst o (Arena.viewBVar (absEIdx h)) := by
  apply view_bvar_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::view_fvar_idx` against `Arena.viewFVarIdx`. -/
@[grind →] theorem view_fvar_idx_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_fvar_idx pers st h = ok o) :
    SimR (Option.map absU) lst o (Arena.viewFVarIdx (absEIdx h)) := by
  rw [arena.monad.view_fvar_idx] at hrun
  show (Arena.viewFVarIdx (absEIdx h)).run lst = _
  rw [show (Arena.viewFVarIdx (absEIdx h)).run lst
        = .ok (lst.store.viewFVarIdx (absEIdx h), lst) from rfl,
    estore_view_fvar_idx_abs hrel.store hrun]

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_fvar_idx_run₀`. -/
@[grind →] theorem view_fvar_idx_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_fvar_idx pers st h = ok o) :
    SimR (Option.map absU) lst o (Arena.viewFVarIdx (absEIdx h)) := by
  apply view_fvar_idx_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::view_fvar_ty` against `Arena.viewFVarTy`. -/
@[grind →] theorem view_fvar_ty_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_fvar_ty pers st h = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.viewFVarTy (absEIdx h)) := by
  rw [arena.monad.view_fvar_ty] at hrun
  show (Arena.viewFVarTy (absEIdx h)).run lst = _
  rw [show (Arena.viewFVarTy (absEIdx h)).run lst
        = .ok (lst.store.viewFVarTy (absEIdx h), lst) from rfl,
    estore_view_fvar_ty_abs hrel.store hrun]

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_fvar_ty_run₀`. -/
@[grind →] theorem view_fvar_ty_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_fvar_ty pers st h = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.viewFVarTy (absEIdx h)) := by
  apply view_fvar_ty_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::view_let` against `Arena.viewLet`. -/
@[grind →] theorem view_let_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_let pers st h = ok o) :
    SimR (Option.map absLetT) lst o (Arena.viewLet (absEIdx h)) := by
  rw [arena.monad.view_let] at hrun
  show (Arena.viewLet (absEIdx h)).run lst = _
  rw [show (Arena.viewLet (absEIdx h)).run lst
        = .ok (lst.store.viewLet (absEIdx h), lst) from rfl,
    estore_view_let_abs hrel.store hrun]

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_let_run₀`. -/
@[grind →] theorem view_let_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_let pers st h = ok o) :
    SimR (Option.map absLetT) lst o (Arena.viewLet (absEIdx h)) := by
  apply view_let_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::view_proj` against `Arena.viewProj`. -/
@[grind →] theorem view_proj_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_proj pers st h = ok o) :
    SimR (Option.map absProjT) lst o (Arena.viewProj (absEIdx h)) := by
  rw [arena.monad.view_proj] at hrun
  show (Arena.viewProj (absEIdx h)).run lst = _
  rw [show (Arena.viewProj (absEIdx h)).run lst
        = .ok (lst.store.viewProj (absEIdx h), lst) from rfl,
    estore_view_proj_abs hrel.store hrun]

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_proj_run₀`. -/
@[grind →] theorem view_proj_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view_proj pers st h = ok o) :
    SimR (Option.map absProjT) lst o (Arena.viewProj (absEIdx h)) := by
  apply view_proj_run₀ (hrel := hrel.to₀) <;> assumption

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
@[grind →] theorem inst1_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst1_get_run₀`. -/
@[grind →] theorem inst1_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.inst1_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.inst1Get (absEIdxNat k)) := by
  apply inst1_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::inst_l_get` against `Arena.instLGet`. -/
@[grind →] theorem inst_l_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst_l_get_run₀`. -/
@[grind →] theorem inst_l_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.inst_l_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.instLGet (absEIdxNat k)) := by
  apply inst_l_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::lift_get` against `Arena.liftGet`. -/
@[grind →] theorem lift_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `lift_get_run₀`. -/
@[grind →] theorem lift_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.lift_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.liftGet (absEIdxNat k)) := by
  apply lift_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::reset_get` against `Arena.resetGet`. -/
@[grind →] theorem reset_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `reset_get_run₀`. -/
@[grind →] theorem reset_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.reset_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.resetGet (absEIdxNat k)) := by
  apply reset_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::rename_get` against `Arena.renameGet`. -/
@[grind →] theorem rename_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `rename_get_run₀`. -/
@[grind →] theorem rename_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.rename_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.renameGet (absEIdxNat k)) := by
  apply rename_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::abs1_get` against `Arena.abs1Get`. -/
@[grind →] theorem abs1_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `abs1_get_run₀`. -/
@[grind →] theorem abs1_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.abs1_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.abs1Get (absEIdxNat k)) := by
  apply abs1_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::lower_get` against `Arena.lowerGet`. -/
@[grind →] theorem lower_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `lower_get_run₀`. -/
@[grind →] theorem lower_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.lower_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.lowerGet (absEIdxNat k)) := by
  apply lower_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::inst1_l_get` against `Arena.inst1LGet`. -/
@[grind →] theorem inst1_l_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst1_l_get_run₀`. -/
@[grind →] theorem inst1_l_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.inst1_l_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.inst1LGet (absEIdxNat k)) := by
  apply inst1_l_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::inst_lp_get` against `Arena.instLPGet`. -/
@[grind →] theorem inst_lp_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst_lp_get_run₀`. -/
@[grind →] theorem inst_lp_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {o : Option arena.handle.EIdx}
    (hrun : arena.monad.inst_lp_get st k = ok o) :
    SimR (Option.map absEIdx) lst o (Arena.instLPGet (absEIdxNat k)) := by
  apply inst_lp_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::bvar_b_get` against `Arena.bvarBGet`. -/
@[grind →] theorem bvar_b_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `bvar_b_get_run₀`. -/
@[grind →] theorem bvar_b_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.EIdx} {o : Option Std.U64}
    (hrun : arena.monad.bvar_b_get st k = ok o) :
    SimR (Option.map absU) lst o (Arena.bvarBGet (absEIdx k)) := by
  apply bvar_b_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::fvar_b_get` against `Arena.fvarBGet`. -/
@[grind →] theorem fvar_b_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `fvar_b_get_run₀`. -/
@[grind →] theorem fvar_b_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.EIdx} {o : Option Std.U64}
    (hrun : arena.monad.fvar_b_get st k = ok o) :
    SimR (Option.map absU) lst o (Arena.fvarBGet (absEIdx k)) := by
  apply fvar_b_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::inst_lp_l_get` against `Arena.instLPLGet`. -/
@[grind →] theorem inst_lp_l_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst_lp_l_get_run₀`. -/
@[grind →] theorem inst_lp_l_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.LIdx} {o : Option arena.handle.LIdx}
    (hrun : arena.monad.inst_lp_l_get st k = ok o) :
    SimR (Option.map absLIdx) lst o (Arena.instLPLGet (absLIdx k)) := by
  apply inst_lp_l_get_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::inst_lp_ls_get` against `Arena.instLPLsGet`. -/
@[grind →] theorem inst_lp_ls_get_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst_lp_ls_get_run₀`. -/
@[grind →] theorem inst_lp_ls_get_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.LsIdx} {o : Option arena.handle.LsIdx}
    (hrun : arena.monad.inst_lp_ls_get st k = ok o) :
    SimR (Option.map absLsIdx) lst o (Arena.instLPLsGet (absLsIdx k)) := by
  apply inst_lp_ls_get_run₀ (hrel := hrel.to₀) <;> assumption

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
@[grind →] theorem derived_e_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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
@[grind →] theorem view_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view pers st h = ok o) :
    AOut₀ absENodeView pers o st
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
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_run₀`. -/
@[grind →] theorem view_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.EIdx} {o}
    (hrun : arena.monad.view pers st h = ok o) :
    AOut absENodeView (fun _ => True) pers lst o st
      ((Arena.view (absEIdx h)).run lst) := by
  exact AOut₀.toAOut_of_store (view_run₀ hrel.to₀ hinv hrun) hrel.storeWF
    (fun _ _ hx => by rw [view_run_state hx])

/-- `arena::monad::view_bind_i` against `Arena.viewBindI` (task #97-P6-16: the
binder projection that stops at the datum's HANDLE). -/
@[grind →] theorem view_bind_i_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hbind : ETag.isBind (absEIdx h).tag = true)
    (hrun : arena.monad.view_bind_i pers st h = ok o) :
    SimR (Option.map absBindI) lst o (Arena.viewBindI (absEIdx h)) := by
  rw [arena.monad.view_bind_i] at hrun
  show (Arena.viewBindI (absEIdx h)).run lst = _
  rw [show (Arena.viewBindI (absEIdx h)).run lst
        = .ok (lst.store.viewBindI (absEIdx h), lst) from rfl,
    estore_view_bind_i_abs hrel.store hbind hrun]

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_bind_i_run₀`. -/
@[grind →] theorem view_bind_i_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hbind : ETag.isBind (absEIdx h).tag = true)
    (hrun : arena.monad.view_bind_i pers st h = ok o) :
    SimR (Option.map absBindI) lst o (Arena.viewBindI (absEIdx h)) := by
  apply view_bind_i_run₀ (hrel := hrel.to₀) <;> assumption

/-- `arena::monad::view_bind` against `Arena.viewBind` — `viewBindI` then
`viewBM`, the two tier selects meeting. -/
@[grind →] theorem view_bind_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.EIdx} {o}
    (hbind : ETag.isBind (absEIdx h).tag = true)
    (hrun : arena.monad.view_bind pers st h = ok o) :
    SimR (Option.map absBindM) lst o (Arena.viewBind (absEIdx h)) := by
  rw [arena.monad.view_bind] at hrun
  show (Arena.viewBind (absEIdx h)).run lst = _
  rw [show (Arena.viewBind (absEIdx h)).run lst
        = .ok (lst.store.viewBind (absEIdx h), lst) from rfl,
    estore_view_bind_abs hrel.store hbind hrun]

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_bind_run₀`. -/
@[grind →] theorem view_bind_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {o}
    (hbind : ETag.isBind (absEIdx h).tag = true)
    (hrun : arena.monad.view_bind pers st h = ok o) :
    SimR (Option.map absBindM) lst o (Arena.viewBind (absEIdx h)) := by
  apply view_bind_run₀ (hrel := hrel.to₀) <;> assumption

/-- **`Arena.viewBM` has no `arena::monad` wrapper** — a shape difference, and
a small one: `arena/monad.rs` stops at `view_bind`/`view_bind_i` and its
binder-datum read goes straight to `EStore::view_bm`, where the twin's
`Monad.lean` names a `viewBM` of its own.  Both are the same store read under
the same state, so the refinement states the lemma at the STORE function and
the twin's monadic wrapper is `rfl` over it. -/
@[grind →] theorem view_bm_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

theorem derived_l_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `derived_l_run₀`. -/
theorem derived_l_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.LIdx} {d : arena.store.LDer}
    (hrun : arena.monad.derived_l pers st h = ok d) :
    SimRO absLDer derObsL lst d (Arena.derivedL (absLIdx h)) := by
  apply derived_l_run₀ (hrel := hrel.to₀) <;> assumption

theorem view_ls_len_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
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

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_ls_len_run₀`. -/
theorem view_ls_len_run {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.view_ls_len pers st h = ok o) :
    SimR (Option.map absSz) lst o (Arena.viewLsLen (absLsIdx h)) := by
  apply view_ls_len_run₀ (hrel := hrel.to₀) <;> assumption

theorem view_n_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.NIdx} {o}
    (hrun : arena.monad.view_n pers st h = ok o) :
    AOut₀ absNNodeView pers o st
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
    refine AOut₀.err ?_
    rw [hrunl, EStore.ns, hview]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    rw [hvc] at hview
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    rw [hrunl, EStore.ns, hview]
    rfl

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `view_n_run₀`. -/
theorem view_n_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.NIdx} {o}
    (hrun : arena.monad.view_n pers st h = ok o) :
    AOut absNNodeView (fun _ => True) pers lst o st
      ((Arena.viewN (absNIdx h)).run lst) := by
  refine AOut₀.toAOut_of_store (view_n_run₀ hrel.to₀ hinv hrun) hrel.storeWF ?_
  intro b lst' hx
  simp only [Arena.viewN, run_get_bind] at hx
  split at hx
  · cases hx; rfl
  · cases hx

theorem view_l_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LIdx} {o}
    (hrun : arena.monad.view_l pers st h = ok o) :
    AOut₀ absLNodeView pers o st
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
    refine AOut₀.err ?_
    rw [hrunl, EStore.ls, hview]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    rw [hvc] at hview
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    rw [hrunl, EStore.ls, hview]
    rfl

theorem view_ls_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.view_ls pers st h = ok o) :
    AOut₀ absLsNodeView pers o st
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
    refine AOut₀.err ?_
    rw [hrunl, hview]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    rw [hvc] at hview
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    rw [hrunl, hview]
    rfl

/-! ## The readbacks (task #97-P5-Specs)

**The eight `read_*` of DESIGN §10's list, closed.**  `arena::monad::read_name`
and its siblings are the one family of this file that is an EQUATION and not a
simulation (DESIGN §8.3 lesson 4, "intern the representation, not the
algorithm"): the twin's readback IS `Arena/Denote.lean`'s `denoteN` /
`denoteL` / `denoteLs`, and the port's `denote_n_aux` / `denote_l_aux` mirror
those fuel-indexed definitions clause for clause.  So the proof is a parallel
fuel induction and nothing else:

    denote_n_aux_abs : fuel.val = n → denote_n_aux pers rs fuel i = ok o →
      o.map absName = denoteNAux ls n (absNIdx i)

— a **bi-directional** statement, which is what pays for both arms at once:
the twin errs exactly where the port answers `none`, so the `Internal` arm and
the `Ok` arm come out of the same equation.

**The fuel matches on the nose** and has to: the twin's is `st.nodeCount + 1`
and the port's is `NStore::node_count + 1`, so `ntables_count_abs` (three
`tbl_size_abs`, one per constructor array) and `nstore_node_count_abs` are
what make the two inductions the same induction.  A weaker bound would close
the success arm and lose the failure arm.

**One hypothesis was added to the four plain readbacks**: `AStateInv pers st`,
which `AOut`'s success arm asks for and the stated form did not carry — the
four sibling `view_*_run` above all take it, so this is the statement catching
up with its own shape rather than a weakening.

The `str` arm is the only non-structural step of the WF companion
(`denote_n_wf`, needed by the memoised four): `Refine.Name.mk_str_wf` wants
`StrWF` of the STORED code points, which is `TblInv`'s `nodesP` at the `strs`
array, read off by `ntables_get_wf`.

`read_names` is the one with a cursor: the port pushes into a `Vec` where the
twin conses, so the induction carries the accumulator. -/

/-- `arena::monad::denote_n_aux` against `Arena.denoteNAux`, at the same fuel. -/
theorem denote_n_aux_abs {pers rs ls} (hrel : NStoreRel pers rs ls) :
    ∀ (n : Nat) (fuel : Std.U64) (i : arena.handle.NIdx)
      {o : Option kernel.name.Name}, fuel.val = n →
      arena.monad.denote_n_aux pers rs fuel i = ok o →
      o.map ConRon.Refine.absName = denoteNAux ls n (absNIdx i) := by
  intro n
  induction n with
  | zero =>
    intro fuel i o hn hrun
    rw [arena.monad.denote_n_aux, if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) :
      fuel = 0#u64)] at hrun
    rw [← Result.ok_injective hrun]
    rfl
  | succ k ih =>
    intro fuel i o hn hrun
    rw [arena.monad.denote_n_aux, if_neg (by
      intro hc; rw [hc] at hn; simp at hn)] at hrun
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hview := nstore_view_abs hrel hv
    rw [denoteNAux, hview]
    cases v with
    | none =>
      simp only [Option.map_none, Option.bind_none]
      rw [← Result.ok_injective hrun]; rfl
    | some nv =>
      simp only [Option.map_some, Option.bind_some]
      cases nv with
      | Anonymous =>
        obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [← Result.ok_injective hrun]
        show Option.map _ (some nm) = _
        rw [Option.map_some, ConRon.Refine.Name.anonymous_refines hnm]
        rfl
      | Str p s =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hih := ih f1 p hf1v ho1
        show _ = (denoteNAux ls k (absNIdx p)).map _
        rw [← hih]
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; rfl
        | some q =>
          obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          rw [← Result.ok_injective hrun]
          show Option.map _ (some nm) = _
          rw [Option.map_some, ConRon.Refine.Name.mk_str_refines hnm]
          rfl
      | Num p m =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hih := ih f1 p hf1v ho1
        show _ = (denoteNAux ls k (absNIdx p)).map _
        rw [← hih]
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; rfl
        | some q =>
          obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          rw [← Result.ok_injective hrun]
          show Option.map _ (some nm) = _
          rw [Option.map_some, ConRon.Refine.Name.mk_num_refines hnm]
          rfl

theorem usize_cast_u64_val' (x : Std.Usize) :
    (Std.UScalar.cast .U64 x).val = x.val := by
  apply Std.UScalar.cast_val_mod_pow_greater_numBits_eq
  show UScalarTy.Usize.numBits ≤ UScalarTy.U64.numBits
  simp only [UScalarTy.numBits]
  cases System.Platform.numBits_eq with
  | inl hp => omega
  | inr hp => omega

theorem ntables_count_abs {rt lt} (hrel : NTablesRel rt lt) {n : Std.Usize}
    (h : arena.store.NTables.count rt = ok n) : n.val = lt.count := by
  rw [arena.store.NTables.count] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ab, hab, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have ha' := tbl_size_abs hrel.anons ha
  have hb' := tbl_size_abs hrel.strs hb
  have hc' := tbl_size_abs hrel.nums hc
  have hab' := ConRon.Refine.Nat.uadd_val hab
  have h' := ConRon.Refine.Nat.uadd_val h
  show n.val = lt.anons.size + lt.strs.size + lt.nums.size
  omega

theorem nstore_node_count_abs {pers rs ls} (hrel : NStoreRel pers rs ls)
    {n : Std.Usize} (h : arena.store.NStore.node_count rs pers = ok n) :
    n.val = ls.nodeCount := by
  rw [arena.store.NStore.node_count] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have ha' : a.val = ls.pers.count := by
    rw [arena.store.NStore.pers_count] at ha
    have hp := hrel.perst
    rw [rPersN] at hp
    split at ha <;> rename_i hs
    · rw [if_pos hs] at hp; exact ntables_count_abs hp ha
    · rw [if_neg hs] at hp; exact ntables_count_abs hp ha
  have hb' : b.val = ls.scr.count := by
    rw [arena.store.NStore.scr_count] at hb
    exact ntables_count_abs hrel.scrt hb
  have h' := ConRon.Refine.Nat.uadd_val h
  show n.val = ls.pers.count + ls.scr.count
  omega

theorem denote_n_abs {pers rs ls} (hrel : NStoreRel pers rs ls)
    {i : arena.handle.NIdx} {o : Option kernel.name.Name}
    (h : arena.monad.denote_n pers rs i = ok o) :
    o.map ConRon.Refine.absName = denoteN ls (absNIdx i) := by
  rw [arena.monad.denote_n] at h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c2, hc2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hcv := nstore_node_count_abs hrel hc
  have hc1v : c1.val = c.val := by
    simp only [lift, Result.ok.injEq] at hc1
    rw [← hc1]; exact usize_cast_u64_val' c
  have hc2v : c2.val = ls.nodeCount + 1 := by
    have := ConRon.Refine.Nat.uadd_val hc2
    rw [this, hc1v, hcv]; rfl
  rw [denoteN]
  exact denote_n_aux_abs hrel _ c2 i hc2v h

theorem read_name_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.NIdx} {o}
    (hrun : arena.monad.read_name pers st h = ok o) :
    AOut₀ ConRon.Refine.absName pers o st
      ((Arena.readName (absNIdx h)).run lst) := by
  rw [arena.monad.read_name] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ns] at hn
  have hn2 : n = st.store.lss.ls.ns := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hd := denote_n_abs hrel.store.lss.lvl.ns hv
  have hrunl : (Arena.readName (absNIdx h)).run lst
      = match denoteN lst.store.ns (absNIdx h) with
        | some x => Except.ok (x, lst)
        | none => Except.error (.internal "arena: dangling name handle") := by
    show (match denoteN lst.store.ns (absNIdx h) with
          | some x => (pure x : AM _)
          | none => Arena.fail (.internal "arena: dangling name handle")).run lst = _
    cases denoteN lst.store.ns (absNIdx h) <;> rfl
  cases hvc : v with
  | none =>
    rw [hvc] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := fail_run hrun
    subst ho
    rw [hvc] at hd
    refine AOut₀.err ?_
    rw [hrunl, EStore.ns, ← hd]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    rw [hvc] at hd
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    rw [hrunl, EStore.ns, ← hd]
    rfl

theorem denote_l_aux_abs {pers rs ls} (hrel : LStoreRel pers rs ls) :
    ∀ (n : Nat) (fuel : Std.U64) (i : arena.handle.LIdx)
      {o : Option kernel.level.Level}, fuel.val = n →
      arena.monad.denote_l_aux pers rs fuel i = ok o →
      o.map ConRon.Refine.absLevel = denoteLAux ls n (absLIdx i) := by
  intro n
  induction n with
  | zero =>
    intro fuel i o hn hrun
    rw [arena.monad.denote_l_aux, if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) :
      fuel = 0#u64)] at hrun
    rw [← Result.ok_injective hrun]; rfl
  | succ k ih =>
    intro fuel i o hn hrun
    rw [arena.monad.denote_l_aux, if_neg (by intro hc; rw [hc] at hn; simp at hn)] at hrun
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hview := lstore_view_abs hrel hv
    rw [denoteLAux, hview]
    cases v with
    | none =>
      simp only [Option.map_none, Option.bind_none]
      rw [← Result.ok_injective hrun]; rfl
    | some lv =>
      simp only [Option.map_some, Option.bind_some]
      cases lv with
      | Zero =>
        obtain ⟨u, hu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [← Result.ok_injective hrun]
        show Option.map _ (some u) = _
        rw [Option.map_some, ConRon.Refine.level_zero_inv hu]
        rfl
      | Succ a =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hih := ih f1 a hf1v ho1
        show _ = (denoteLAux ls k (absLIdx a)).map _
        rw [← hih]
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; rfl
        | some q =>
          obtain ⟨u, hu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          rw [← Result.ok_injective hrun]
          show Option.map _ (some u) = _
          obtain ⟨hh, rfl⟩ := ConRon.Refine.level_succ_inv hu
          rfl
      | Max a b =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hiha := ih f1 a hf1v ho1
        show _ = opt2 _ (denoteLAux ls k (absLIdx a)) (denoteLAux ls k (absLIdx b))
        rw [← hiha]
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; rfl
        | some q =>
          obtain ⟨o2, ho2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hihb := ih f1 b hf1v ho2
          rw [← hihb]
          cases o2 with
          | none => rw [← Result.ok_injective hrun]; rfl
          | some r =>
            obtain ⟨u, hu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            rw [← Result.ok_injective hrun]
            show Option.map _ (some u) = _
            obtain ⟨hh, rfl⟩ := ConRon.Refine.level_max_inv hu
            rfl
      | Imax a b =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hiha := ih f1 a hf1v ho1
        show _ = opt2 _ (denoteLAux ls k (absLIdx a)) (denoteLAux ls k (absLIdx b))
        rw [← hiha]
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; rfl
        | some q =>
          obtain ⟨o2, ho2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hihb := ih f1 b hf1v ho2
          rw [← hihb]
          cases o2 with
          | none => rw [← Result.ok_injective hrun]; rfl
          | some r =>
            obtain ⟨u, hu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            rw [← Result.ok_injective hrun]
            show Option.map _ (some u) = _
            obtain ⟨hh, rfl⟩ := ConRon.Refine.level_imax_inv hu
            rfl
      | Param nm =>
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hd := denote_n_abs hrel.ns ho1
        show _ = (denoteN ls.ns (absNIdx nm)).map _
        rw [← hd]
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; rfl
        | some q =>
          obtain ⟨u, hu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          rw [← Result.ok_injective hrun]
          show Option.map _ (some u) = _
          obtain ⟨hh, rfl⟩ := ConRon.Refine.level_param_inv hu
          rfl

theorem ltables_count_abs {rt lt} (hrel : LTablesRel rt lt) {n : Std.Usize}
    (h : arena.store.LTables.count rt = ok n) : n.val = lt.count := by
  rw [arena.store.LTables.count] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ab, hab, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨abc, habc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨abcd, habcd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have ha' := tbl_size_abs hrel.zeros ha
  have hb' := tbl_size_abs hrel.succs hb
  have hc' := tbl_size_abs hrel.maxs hc
  have hd' := tbl_size_abs hrel.imaxs hd
  have he' := tbl_size_abs hrel.params he
  have h1 := ConRon.Refine.Nat.uadd_val hab
  have h2 := ConRon.Refine.Nat.uadd_val habc
  have h3 := ConRon.Refine.Nat.uadd_val habcd
  have h4 := ConRon.Refine.Nat.uadd_val h
  show n.val = lt.zeros.size + lt.succs.size + lt.maxs.size + lt.imaxs.size + lt.params.size
  omega

theorem lstore_node_count_abs {pers rs ls} (hrel : LStoreRel pers rs ls)
    {n : Std.Usize} (h : arena.store.LStore.node_count rs pers = ok n) :
    n.val = ls.nodeCount := by
  rw [arena.store.LStore.node_count] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have ha' : a.val = ls.pers.count := by
    rw [arena.store.LStore.pers_count] at ha
    have hp := hrel.perst
    rw [rPersL] at hp
    split at ha <;> rename_i hs
    · rw [if_pos hs] at hp; exact ltables_count_abs hp ha
    · rw [if_neg hs] at hp; exact ltables_count_abs hp ha
  have hb' : b.val = ls.scr.count := by
    rw [arena.store.LStore.scr_count] at hb
    exact ltables_count_abs hrel.scrt hb
  have h' := ConRon.Refine.Nat.uadd_val h
  show n.val = ls.pers.count + ls.scr.count
  omega

theorem denote_l_abs {pers rs ls} (hrel : LStoreRel pers rs ls)
    {i : arena.handle.LIdx} {o : Option kernel.level.Level}
    (h : arena.monad.denote_l pers rs i = ok o) :
    o.map ConRon.Refine.absLevel = denoteL ls (absLIdx i) := by
  rw [arena.monad.denote_l] at h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c2, hc2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hcv := lstore_node_count_abs hrel hc
  have hc1v : c1.val = c.val := by
    simp only [lift, Result.ok.injEq] at hc1
    rw [← hc1]; exact usize_cast_u64_val' c
  have hc2v : c2.val = ls.nodeCount + 1 := by
    have := ConRon.Refine.Nat.uadd_val hc2
    rw [this, hc1v, hcv]; rfl
  rw [denoteL]
  exact denote_l_aux_abs hrel _ c2 i hc2v h

theorem read_level_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LIdx} {o}
    (hrun : arena.monad.read_level pers st h = ok o) :
    AOut₀ ConRon.Refine.absLevel pers o st
      ((Arena.readLevel (absLIdx h)).run lst) := by
  rw [arena.monad.read_level] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ls] at hn
  have hn2 : n = st.store.lss.ls := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hd := denote_l_abs hrel.store.lss.lvl hv
  have hrunl : (Arena.readLevel (absLIdx h)).run lst
      = match denoteL lst.store.ls (absLIdx h) with
        | some x => Except.ok (x, lst)
        | none => Except.error (.internal "arena: dangling level handle") := by
    show (match denoteL lst.store.ls (absLIdx h) with
          | some x => (pure x : AM _)
          | none => Arena.fail (.internal "arena: dangling level handle")).run lst = _
    cases denoteL lst.store.ls (absLIdx h) <;> rfl
  cases hvc : v with
  | none =>
    rw [hvc] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := fail_run hrun
    subst ho
    rw [hvc] at hd
    refine AOut₀.err ?_
    rw [hrunl, EStore.ls, ← hd]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    rw [hvc] at hd
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    rw [hrunl, EStore.ls, ← hd]
    rfl

theorem denote_l_list_from_abs {pers rs ls} (hrel : LStoreRel pers rs ls)
    {us : alloc.vec.Vec arena.handle.LIdx} :
    ∀ k (i : Std.Usize) (out : alloc.vec.Vec kernel.level.Level),
      us.length - i.val ≤ k → ∀ {o},
      arena.monad.denote_l_list_from pers rs us i out = ok o →
      o.map (fun v => v.val.map ConRon.Refine.absLevel)
        = (denoteLList ls ((us.val.drop i.val).map absLIdx)).map
            (fun t => out.val.map ConRon.Refine.absLevel ++ t) := by
  intro k
  induction k with
  | zero =>
    intro i out hk o hrun
    rw [arena.monad.denote_l_list_from.eq_def] at hrun; simp only [] at hrun
    rw [if_pos (by scalar_tac)] at hrun
    rw [List.drop_eq_nil_of_le (by scalar_tac)]
    rw [← Result.ok_injective hrun]
    simp [denoteLList]
  | succ k ih =>
    intro i out hk o hrun
    rw [arena.monad.denote_l_list_from.eq_def] at hrun; simp only [] at hrun
    split at hrun
    · rw [List.drop_eq_nil_of_le (by scalar_tac)]
      rw [← Result.ok_injective hrun]
      simp [denoteLList]
    · rename_i hlt
      have hb : i.val < us.length := by scalar_tac
      obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hlv : us.val[i.val]? = some l := vec_index_some hl
      have hlv' : us.val[i.val] = l := by
        have := List.getElem?_eq_getElem hb
        rw [this] at hlv; exact (Option.some.injEq _ _ ▸ hlv)
      obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hd := denote_l_abs hrel ho1
      rw [List.drop_eq_getElem_cons hb, List.map_cons, denoteLList, hlv', ← hd]
      cases o1 with
      | none =>
        rw [← Result.ok_injective hrun]
        simp only [Option.map_none, opt2]
      | some l1 =>
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hout1v : out1.val = out.val ++ [l1] :=
          ConRon.Refine.vec_push_val hout1
        have hih := ih i2 out1 (by scalar_tac) hrun
        rw [hi2v] at hih
        rw [hih, hout1v]
        simp only [opt2, Option.map_some, List.map_append,
          List.map_cons, List.map_nil]
        cases denoteLList ls ((us.val.drop (i.val + 1)).map absLIdx) with
        | none => rfl
        | some t => simp

theorem denote_l_list_abs {pers rs ls} (hrel : LStoreRel pers rs ls)
    {us : alloc.vec.Vec arena.handle.LIdx} {o}
    (h : arena.monad.denote_l_list pers rs us = ok o) :
    o.map (fun v => v.val.map ConRon.Refine.absLevel)
      = denoteLList ls (us.val.map absLIdx) := by
  rw [arena.monad.denote_l_list] at h
  have hh := denote_l_list_from_abs hrel us.length 0#usize
    (alloc.vec.Vec.new kernel.level.Level) (by scalar_tac) h
  simpa using hh

theorem denote_ls_abs {pers rs ls} (hrel : LsStoreRel pers rs ls)
    {i : arena.handle.LsIdx} {o}
    (h : arena.monad.denote_ls pers rs i = ok o) :
    o.map (fun v => v.val.map ConRon.Refine.absLevel) = denoteLs ls (absLsIdx i) := by
  rw [arena.monad.denote_ls] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hview := lsstore_view_abs hrel hv
  rw [denoteLs, hview]
  cases v with
  | none => rw [← Result.ok_injective h]; rfl
  | some us =>
    simp only [Option.map_some]
    exact denote_l_list_abs hrel.lvl h

theorem read_levels_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.read_levels pers st h = ok o) :
    AOut₀ ConRon.Refine.absLevels pers o st
      ((Arena.readLevels (absLsIdx h)).run lst) := by
  rw [arena.monad.read_levels] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ls_s] at hn
  have hn2 : n = st.store.lss := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hd := denote_ls_abs hrel.store.lss hv
  have hrunl : (Arena.readLevels (absLsIdx h)).run lst
      = match denoteLs lst.store.lss (absLsIdx h) with
        | some x => Except.ok (x, lst)
        | none => Except.error (.internal "arena: dangling level-list handle") := by
    show (match denoteLs lst.store.lss (absLsIdx h) with
          | some x => (pure x : AM _)
          | none => Arena.fail (.internal "arena: dangling level-list handle")).run lst = _
    cases denoteLs lst.store.lss (absLsIdx h) <;> rfl
  cases hvc : v with
  | none =>
    rw [hvc] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := fail_run hrun
    subst ho
    rw [hvc] at hd
    refine AOut₀.err ?_
    rw [hrunl, ← hd]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    rw [hvc] at hd
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    rw [hrunl, ← hd]
    rfl

/-- `denoteN` over a list of handles. -/
def denoteNList (st : NStore) : List NIdx → Option (List ConLeche.Name)
  | [] => some []
  | h :: hs => opt2 List.cons (denoteN st h) (denoteNList st hs)

theorem readNames_run (lst : AState) : ∀ (l : List NIdx),
    (Arena.readNames l).run lst
      = match denoteNList lst.store.ns l with
        | some xs => Except.ok (xs, lst)
        | none => Except.error (.internal "arena: dangling name handle") := by
  intro l
  induction l with
  | nil => rfl
  | cons h hs ih =>
    show (do let x ← Arena.readName h; let xs ← Arena.readNames hs;
             pure (x :: xs) : AM _).run lst = _
    rw [StateT.run_bind]
    have hr : (Arena.readName h).run lst
        = match denoteN lst.store.ns h with
          | some x => Except.ok (x, lst)
          | none => Except.error (.internal "arena: dangling name handle") := by
      show (match denoteN lst.store.ns h with
            | some x => (pure x : AM _)
            | none => Arena.fail (.internal "arena: dangling name handle")).run lst = _
      cases denoteN lst.store.ns h <;> rfl
    rw [hr, denoteNList]
    cases hd : denoteN lst.store.ns h with
    | none => simp only [opt2]; rfl
    | some x =>
      show (Except.ok (x, lst) : Except _ _) >>= _ = _
      show (do let xs ← Arena.readNames hs; pure (x :: xs) : AM _).run lst = _
      rw [StateT.run_bind, ih]
      cases denoteNList lst.store.ns hs with
      | none => simp only [opt2]; rfl
      | some xs => simp only [opt2]; rfl

theorem read_name_abs₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {h : arena.handle.NIdx} {r}
    (hrun : arena.monad.read_name pers st h = ok r) :
    match denoteN lst.store.ns (absNIdx h) with
    | some x => ∃ y, r = .Ok y ∧ ConRon.Refine.absName y = x
    | none => ∃ e, r = .Err e ∧ absAErrKind e = some .internal := by
  rw [arena.monad.read_name] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ns] at hn
  have hn2 : n = st.store.lss.ls.ns := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hd := denote_n_abs hrel.store.lss.lvl.ns hv
  cases hvc : v with
  | none =>
    rw [hvc] at hrun hd
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := fail_run hrun
    subst ho
    show match denoteN lst.store.ns (absNIdx h) with | some _ => _ | none => _
    rw [EStore.ns, ← hd]
    exact ⟨_, rfl, rfl⟩
  | some w =>
    rw [hvc] at hrun hd
    have ho := Result.ok_injective hrun
    subst ho
    show match denoteN lst.store.ns (absNIdx h) with | some _ => _ | none => _
    rw [EStore.ns, ← hd]
    exact ⟨w, rfl, rfl⟩

theorem read_names_from_abs₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    {ks : alloc.vec.Vec arena.handle.NIdx} :
    ∀ k (i : Std.Usize) (out : alloc.vec.Vec kernel.name.Name),
      ks.length - i.val ≤ k → ∀ {o},
      arena.monad.read_names_from pers st ks i out = ok o →
      match denoteNList lst.store.ns ((ks.val.drop i.val).map absNIdx) with
      | some xs => ∃ v, o = .Ok v ∧ v.val.map ConRon.Refine.absName
          = out.val.map ConRon.Refine.absName ++ xs
      | none => ∃ e, o = .Err e ∧ absAErrKind e = some .internal := by
  intro k
  induction k with
  | zero =>
    intro i out hk o hrun
    rw [arena.monad.read_names_from.eq_def] at hrun; simp only [] at hrun
    rw [if_pos (by scalar_tac)] at hrun
    rw [List.drop_eq_nil_of_le (by scalar_tac), List.map_nil]
    exact ⟨out, (Result.ok_injective hrun).symm, by simp⟩
  | succ k ih =>
    intro i out hk o hrun
    rw [arena.monad.read_names_from.eq_def] at hrun; simp only [] at hrun
    split at hrun
    · rw [List.drop_eq_nil_of_le (by scalar_tac), List.map_nil]
      exact ⟨out, (Result.ok_injective hrun).symm, by simp⟩
    · rename_i hlt
      have hb : i.val < ks.length := by scalar_tac
      obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hnv : ks.val[i.val] = n := by
        have h1 : ks.val[i.val]? = some n := vec_index_some hn
        rw [List.getElem?_eq_getElem hb] at h1
        exact (Option.some.injEq _ _ ▸ h1)
      obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hra := read_name_abs₀ hrel hr
      rw [List.drop_eq_getElem_cons hb, List.map_cons, denoteNList, hnv]
      cases hdn : denoteN lst.store.ns (absNIdx n) with
      | none =>
        rw [hdn] at hra
        obtain ⟨e, rfl, hek⟩ := hra
        simp only [opt2]
        refine ⟨e, ?_, hek⟩
        exact (Result.ok_injective hrun).symm
      | some x =>
        rw [hdn] at hra
        obtain ⟨y, rfl, hy⟩ := hra
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hout1v : out1.val = out.val ++ [y] := ConRon.Refine.vec_push_val hout1
        have hih := ih i2 out1 (by scalar_tac) hrun
        rw [hi2v] at hih
        cases hdl : denoteNList lst.store.ns ((ks.val.drop (i.val + 1)).map absNIdx) with
        | none =>
          rw [hdl] at hih
          simp only [opt2]
          exact hih
        | some xs =>
          rw [hdl] at hih
          obtain ⟨v, rfl, hv⟩ := hih
          simp only [opt2]
          refine ⟨v, rfl, ?_⟩
          rw [hv, hout1v]
          simp only [List.map_append, List.map_cons, List.map_nil,
            List.append_assoc, List.cons_append, List.nil_append, hy]

theorem read_names_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {ks : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.monad.read_names pers st ks = ok o) :
    AOut₀ ConRon.Refine.absNames pers o st
      ((Arena.readNames (ks.val.map absNIdx)).run lst) := by
  rw [arena.monad.read_names] at hrun
  have hh := read_names_from_abs₀ hrel ks.length 0#usize
    (alloc.vec.Vec.new kernel.name.Name) (by scalar_tac) hrun
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hh
  rw [readNames_run]
  cases hdl : denoteNList lst.store.ns (ks.val.map absNIdx) with
  | none =>
    rw [hdl] at hh
    obtain ⟨e, rfl, hek⟩ := hh
    exact AOut₀.err (AErrSim.mk rfl (by rw [hek]; rfl))
  | some xs =>
    rw [hdl] at hh
    obtain ⟨v, rfl, hv⟩ := hh
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    show Except.ok (xs, lst) = Except.ok (ConRon.Refine.absNames v, lst)
    rw [ConRon.Refine.absNames, hv]
    simp

/-- A name node view is well formed when its cached code points are. -/
def NNodeViewWF : arena.store.NNodeView → Prop
  | .Anonymous => True
  | .Str _ s => ConRon.Refine.StrWF s
  | .Num _ _ => True

theorem ntables_get_wf {rt} (hinv : NTablesInv rt)
    {i : arena.handle.NIdx} {o : Option arena.store.NNodeView}
    (h : arena.store.NTables.get rt i = ok o) : ∀ v, o = some v → NNodeViewWF v := by
  rw [arena.store.NTables.get] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases hpc : p with
    | none => rw [hpc] at h; rw [← Result.ok_injective h]; intro v hv; simp at hv
    | some r =>
      rw [hpc] at h; rw [← Result.ok_injective h]
      intro v hv; simp only [Option.some.injEq] at hv; rw [← hv]; trivial
  · split at h
    · obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnwf := tbl_node_wf hinv.strs hp
      cases hpc : p with
      | none => rw [hpc] at h; rw [← Result.ok_injective h]; intro v hv; simp at hv
      | some r =>
        rw [hpc] at h
        obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        rw [← Result.ok_injective h]
        intro v hv; simp only [Option.some.injEq] at hv; rw [← hv]
        show ConRon.Refine.StrWF x1
        rw [ConRon.Refine.Expr.str_copy_eq hx1]
        exact hnwf r hpc
    · split at h
      · obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        cases hpc : p with
        | none => rw [hpc] at h; rw [← Result.ok_injective h]; intro v hv; simp at hv
        | some r =>
          rw [hpc] at h
          obtain ⟨x0, hx0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          rw [← Result.ok_injective h]
          intro v hv; simp only [Option.some.injEq] at hv; rw [← hv]; trivial
      · rw [← Result.ok_injective h]; intro v hv; simp at hv

theorem nstore_view_wf {pers rs} (hinv : NStoreInv pers rs)
    {i : arena.handle.NIdx} {o : Option arena.store.NNodeView}
    (h : arena.store.NStore.view rs pers i = ok o) :
    ∀ v, o = some v → NNodeViewWF v := by
  rw [arena.store.NStore.view] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · rw [arena.store.NStore.pers_get] at h
    have hp := hinv.perst
    rw [rPersN] at hp
    split at h <;> rename_i hs
    · rw [if_pos hs] at hp; exact ntables_get_wf hp h
    · rw [if_neg hs] at hp; exact ntables_get_wf hp h
  · split at h
    · exact ntables_get_wf hinv.scrt h
    · rw [← Result.ok_injective h]; intro v hv; simp at hv

theorem denote_n_aux_wf {pers rs} (hinv : NStoreInv pers rs) :
    ∀ (n : Nat) (fuel : Std.U64) (i : arena.handle.NIdx)
      {o : Option kernel.name.Name}, fuel.val = n →
      arena.monad.denote_n_aux pers rs fuel i = ok o →
      ∀ x, o = some x → ConRon.Refine.NameWF x := by
  intro n
  induction n with
  | zero =>
    intro fuel i o hn hrun
    rw [arena.monad.denote_n_aux, if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) :
      fuel = 0#u64)] at hrun
    rw [← Result.ok_injective hrun]; intro x hx; simp at hx
  | succ k ih =>
    intro fuel i o hn hrun
    rw [arena.monad.denote_n_aux, if_neg (by intro hc; rw [hc] at hn; simp at hn)] at hrun
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hvw := nstore_view_wf hinv hv
    cases hvc : v with
    | none => rw [hvc] at hrun; rw [← Result.ok_injective hrun]; intro x hx; simp at hx
    | some nv =>
      rw [hvc] at hrun hvw
      have hnvw : NNodeViewWF nv := hvw nv rfl
      cases nv with
      | Anonymous =>
        obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [← Result.ok_injective hrun]
        intro x hx; simp only [Option.some.injEq] at hx; rw [← hx]
        exact ConRon.Refine.Name.anonymous_wf hnm
      | Str p s =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hih := ih f1 p hf1v ho1
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; intro x hx; simp at hx
        | some q =>
          obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          rw [← Result.ok_injective hrun]
          intro x hx; simp only [Option.some.injEq] at hx; rw [← hx]
          exact ConRon.Refine.Name.mk_str_wf (hih q rfl) hnvw hnm
      | Num p m =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hih := ih f1 p hf1v ho1
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; intro x hx; simp at hx
        | some q =>
          obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          rw [← Result.ok_injective hrun]
          intro x hx; simp only [Option.some.injEq] at hx; rw [← hx]
          exact ConRon.Refine.Name.mk_num_wf (hih q rfl) hnm

theorem denote_n_wf {pers rs} (hinv : NStoreInv pers rs)
    {i : arena.handle.NIdx} {o : Option kernel.name.Name}
    (h : arena.monad.denote_n pers rs i = ok o) :
    ∀ x, o = some x → ConRon.Refine.NameWF x := by
  rw [arena.monad.denote_n] at h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c2, hc2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact denote_n_aux_wf hinv c2.val c2 i rfl h

theorem denote_l_aux_wf {pers rs} (hinv : LStoreInv pers rs) :
    ∀ (n : Nat) (fuel : Std.U64) (i : arena.handle.LIdx)
      {o : Option kernel.level.Level}, fuel.val = n →
      arena.monad.denote_l_aux pers rs fuel i = ok o →
      ∀ x, o = some x → ConRon.Refine.LevelWF x := by
  intro n
  induction n with
  | zero =>
    intro fuel i o hn hrun
    rw [arena.monad.denote_l_aux, if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) :
      fuel = 0#u64)] at hrun
    rw [← Result.ok_injective hrun]; intro x hx; simp at hx
  | succ k ih =>
    intro fuel i o hn hrun
    rw [arena.monad.denote_l_aux, if_neg (by intro hc; rw [hc] at hn; simp at hn)] at hrun
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases hvc : v with
    | none => rw [hvc] at hrun; rw [← Result.ok_injective hrun]; intro x hx; simp at hx
    | some lv =>
      rw [hvc] at hrun
      have hfuel : ∀ {f1 : Std.U64}, fuel - 1#u64 = ok f1 → f1.val = k := by
        intro f1 hf1
        have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
          (ConRon.Refine.Nat.usub_val hf1).2
        rw [h1, hn]; rfl
      cases lv with
      | Zero =>
        obtain ⟨u, hu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [← Result.ok_injective hrun]
        intro x hx; simp only [Option.some.injEq] at hx; rw [← hx]
        exact ConRon.Refine.Level.zero_wf hu
      | Succ a =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hih := ih f1 a (hfuel hf1) ho1
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; intro x hx; simp at hx
        | some q =>
          obtain ⟨u, hu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          rw [← Result.ok_injective hrun]
          intro x hx; simp only [Option.some.injEq] at hx; rw [← hx]
          exact ConRon.Refine.Level.succ_wf (hih q rfl) hu
      | Max a b =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hiha := ih f1 a (hfuel hf1) ho1
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; intro x hx; simp at hx
        | some q =>
          obtain ⟨o2, ho2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hihb := ih f1 b (hfuel hf1) ho2
          cases o2 with
          | none => rw [← Result.ok_injective hrun]; intro x hx; simp at hx
          | some r =>
            obtain ⟨u, hu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            rw [← Result.ok_injective hrun]
            intro x hx; simp only [Option.some.injEq] at hx; rw [← hx]
            exact ConRon.Refine.Level.max_wf (hiha q rfl) (hihb r rfl) hu
      | Imax a b =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hiha := ih f1 a (hfuel hf1) ho1
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; intro x hx; simp at hx
        | some q =>
          obtain ⟨o2, ho2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hihb := ih f1 b (hfuel hf1) ho2
          cases o2 with
          | none => rw [← Result.ok_injective hrun]; intro x hx; simp at hx
          | some r =>
            obtain ⟨u, hu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            rw [← Result.ok_injective hrun]
            intro x hx; simp only [Option.some.injEq] at hx; rw [← hx]
            exact ConRon.Refine.Level.imax_wf (hiha q rfl) (hihb r rfl) hu
      | Param nm =>
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hnw := denote_n_wf hinv.ns ho1
        cases o1 with
        | none => rw [← Result.ok_injective hrun]; intro x hx; simp at hx
        | some q =>
          obtain ⟨u, hu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          rw [← Result.ok_injective hrun]
          intro x hx; simp only [Option.some.injEq] at hx; rw [← hx]
          exact ConRon.Refine.Level.param_wf (hnw q rfl) hu

theorem denote_l_wf {pers rs} (hinv : LStoreInv pers rs)
    {i : arena.handle.LIdx} {o : Option kernel.level.Level}
    (h : arena.monad.denote_l pers rs i = ok o) :
    ∀ x, o = some x → ConRon.Refine.LevelWF x := by
  rw [arena.monad.denote_l] at h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c2, hc2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact denote_l_aux_wf hinv c2.val c2 i rfl h

theorem denote_l_list_from_wf {pers rs} (hinv : LStoreInv pers rs)
    {us : alloc.vec.Vec arena.handle.LIdx} :
    ∀ k (i : Std.Usize) (out : alloc.vec.Vec kernel.level.Level),
      us.length - i.val ≤ k → ConRon.Refine.LevelsWF out → ∀ {o},
      arena.monad.denote_l_list_from pers rs us i out = ok o →
      ∀ v, o = some v → ConRon.Refine.LevelsWF v := by
  intro k
  induction k with
  | zero =>
    intro i out hk hout o hrun
    rw [arena.monad.denote_l_list_from.eq_def] at hrun; simp only [] at hrun
    rw [if_pos (by scalar_tac)] at hrun
    rw [← Result.ok_injective hrun]
    intro v hv; simp only [Option.some.injEq] at hv; rw [← hv]; exact hout
  | succ k ih =>
    intro i out hk hout o hrun
    rw [arena.monad.denote_l_list_from.eq_def] at hrun; simp only [] at hrun
    split at hrun
    · rw [← Result.ok_injective hrun]
      intro v hv; simp only [Option.some.injEq] at hv; rw [← hv]; exact hout
    · rename_i hlt
      have hb : i.val < us.length := by scalar_tac
      obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hlw := denote_l_wf hinv ho1
      cases o1 with
      | none => rw [← Result.ok_injective hrun]; intro v hv; simp at hv
      | some l1 =>
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hout1v : out1.val = out.val ++ [l1] := ConRon.Refine.vec_push_val hout1
        have hout1w : ConRon.Refine.LevelsWF out1 := by
          intro u hu
          rw [hout1v] at hu
          rcases List.mem_append.mp hu with h1 | h1
          · exact hout u h1
          · simp only [List.mem_singleton] at h1; rw [h1]; exact hlw l1 rfl
        exact ih i2 out1 (by scalar_tac) hout1w hrun

theorem denote_ls_wf {pers rs} (hinv : LsStoreInv pers rs)
    {i : arena.handle.LsIdx} {o}
    (h : arena.monad.denote_ls pers rs i = ok o) :
    ∀ v, o = some v → ConRon.Refine.LevelsWF v := by
  rw [arena.monad.denote_ls] at h
  obtain ⟨w, hw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases w with
  | none => rw [← Result.ok_injective h]; intro v hv; simp at hv
  | some us =>
    have h' : arena.monad.denote_l_list_from pers rs.ls us 0#usize
        (alloc.vec.Vec.new kernel.level.Level) = ok o := h
    exact denote_l_list_from_wf hinv.lvl us.length 0#usize
      (alloc.vec.Vec.new kernel.level.Level) (by scalar_tac)
      (by intro u hu; simp at hu) h'

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
6. and the persistent-append arm, whose frozen-tier guard (`M_FROZEN`) is
   `Native` since task #97-P5-Usize §3, so it claims nothing either — finding
   8's hypothesis `shared_on → scratch_on` is retired (task #97-P5-Unfreeze).

`intern_e_bvar_run` then wraps it in `Arena.internE`'s capacity test, and
**needs finding 9**: the port tests `Tbl::full` only when it is about to
append, where the twin's `internE` tests `sizeOf` before probing, so on a
cons HIT at a full array the port answers `Ok` and the twin throws `native`.
`hcap` is that hypothesis; the proper fix is a one-line twin change (test
after the probe, as the port does), and it belongs in the next twin
catch-up. -/

/-- The frozen-tier guard's arm (`M_FROZEN`, `Native` since task #97-P5-Usize
§3): an error that claims nothing, and the store it hands back. -/
theorem frozen_native_arm {α σ : Type} {st st' : σ}
    {r : core.result.Result α kernel.core_types.CheckError}
    (h : (do
        let s ← lift (Array.to_slice arena.store.M_FROZEN)
        let v ← kernel.core_types.code_points s
        ok (core.result.Result.Err (kernel.core_types.CheckError.Native v), st))
      = ok (r, st')) :
    (∃ v, r = .Err (.Native v)) ∧ st' = st := by
  obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have he := Result.ok_injective h
  simp only [Prod.mk.injEq] at he
  exact ⟨⟨v1, he.1.symm⟩, he.2.symm⟩

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
    {i : Std.U64} {r} {rs'}
    (h : arena.store.EStore.intern_bvar rs pers i = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.bvar (absU i))).2 ∧
        StoreRel pers rs' (ls.intern (.bvar (absU i))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.bvar (absU i))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) := by
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
  have hfind : ls.persFindMaybe (ENodeView.bvar (absU i)) (Idx.ofWord 0)
      = ls.pers.bvars.find? ⟨absU i⟩ := by
    rw [EStore.persFindMaybe_of_noskip rfl]; rfl
  rw [hfind, hE3]
  cases hitc : hit with
  | some hp =>
    rw [hitc] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ?_⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv,
        ECapAt.of_find_ne (by
          have hpp : ls.persFindMaybe (ENodeView.bvar (absU i)) (Idx.ofWord 0)
              = some (absEIdx hp) := by rw [hfind, hE3, hitc]; rfl
          rw [find?_eq_of_pers rfl hpp]; simp)⟩
    · intro ee hbad; simp at hbad
    · exact ⟨rfl, rfl, rfl⟩
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
        refine ⟨?_, ?_, ?_⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨rfl, { hrel with scrt := { hrel.scrt with bvars := hrelT } },
            { hinv with scrt := { hinv.scrt with bvars := hinvT } },
            ECapAt.of_find_ne (by
              have hpn : ls.persFindMaybe (ENodeView.bvar (absU i)) (Idx.ofWord 0) = none := by
                rw [hfind, hE3, hitc]; rfl
              have hss : ls.scr.find? (ENodeView.bvar (absU i)) (Idx.ofWord 0)
                  = some (absEIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
              rw [find?_eq_of_scr rfl hpn (hrel.scratchOn.trans hsc) hss]; simp)⟩
        · intro ee hbad; simp at hbad
        · exact ⟨rfl, rfl, rfl⟩
      | none =>
        rw [hoc] at h
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · -- the array is full: `Native`, which claims nothing
          obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs2⟩ := he
          subst hr; subst hs2
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl, rfl⟩⟩
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
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with bvars := hrel1 }, rfl⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with bvars := hinv1 }⟩,
            ECapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (tbl_not_full_size hrelT hb1 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, by simp [hfz, hsc]⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs2⟩ := he
        subst hr; subst hs2
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨hsh.symm, rfl, rfl⟩⟩
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
        refine ⟨?_, by intro ee hbad; simp at hbad, ⟨hsh.symm, rfl, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        have hrelPerst : ETablesRel rs.pers ls.pers := by
          rw [← hpersE]; exact hrel.perst
        have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
        exact ⟨hhandle, ⟨hrel.lss, { hrelPerst with bvars := hrel1 }, hrel.scrt, rfl⟩,
          ⟨hinv.lss, { hinvPerst with bvars := hinv1 }, hinv.scrt⟩,
          ECapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
            (tbl_not_full_size hrelP hb1 hfull)⟩

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
  cases hp : st.persFindMaybe v mi with
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

/-! `Arena.internE`'s run has two arms, and only the second has a side
condition: on a cons HIT the store does not move (`intern_of_find`), and on a
MISS the capacity test is the twin's own — where the port's `Tbl::full` reads
`true` on exactly the same input and answers `Native`, which claims nothing. -/

/-- **The datum array's own `ECapAt`**, at the `BinderMeta` the port's
`intern_bm` is called with: the bound is tested only where `internBM`
APPENDS, i.e. where its own two-tier probe misses.  `ECapBMAt st (.lam ty b m)`
IS this at `m` (`findBMOfView` of a binder view is `findBM` of its datum), so
the two names are one predicate seen from the view side and the datum side. -/
def ECapBMOf (st : EStore) (m : ConLeche.BinderMeta) : Prop :=
  st.findBM m = none → st.capOKBM

/-- `ECapBMOf` is VACUOUS wherever the port's datum probe hit. -/
theorem ECapBMOf.of_find_ne {st : EStore} {m : ConLeche.BinderMeta}
    (h : st.findBM m ≠ none) : ECapBMOf st m := fun hn => absurd hn h

/-- `findBM`'s two steps: the persistent probe answers. -/
theorem findBM_eq_of_pers {st : EStore} {m : ConLeche.BinderMeta} {i : BMIdx}
    (hp : st.persFindBM m = some i) : st.findBM m = some i := by
  simp only [EStore.findBM, hp]

/-- `findBM`'s two steps, the scratch half. -/
theorem findBM_eq_of_scr {st : EStore} {m : ConLeche.BinderMeta} {i : BMIdx}
    (hp : st.persFindBM m = none) (hon : st.scratchOn = true)
    (hs : st.scr.findBM m = some i) : st.findBM m = some i := by
  simp only [EStore.findBM, hp, hon, if_true, hs]

/-- `ECapBMOf` on the SCRATCH append arm: the port's `Tbl::full` answered
`false` at `scr.bms`. -/
theorem ECapBMOf.of_scr_size {st : EStore} {m : ConLeche.BinderMeta}
    (hon : st.scratchOn = true) (h : st.scr.bmSize < Idx.idxCap) :
    ECapBMOf st m := by
  intro _; simp only [EStore.capOKBM, hon, if_true]; exact h

/-- `ECapBMOf` on the PERSISTENT append arm. -/
theorem ECapBMOf.of_pers_size {st : EStore} {m : ConLeche.BinderMeta}
    (hoff : st.scratchOn = false) (h : st.pers.bmSize < Idx.idxCap) :
    ECapBMOf st m := by
  intro _
  simp only [EStore.capOKBM, hoff, Bool.false_eq_true, if_false]; exact h

/-- `Arena.internE`'s SECOND miss-path test, at a binder view: the datum
array has room.  Named beside `ECapAt` for the same reason — so it can be
concluded rather than assumed where the port's own `intern_bm` proves it.

**Guarded by the DATUM probe, not by the tag** (task #97-P5-Twin round 2):
`internBM` appends only where `findBMOfView` misses, which is where the port's
`intern_bm` tests `full`, so this is exactly the port's own decision.  A
non-binder view answers `some (Idx.ofWord 0)` there and the implication is
vacuous, which is why no `eViewNeedsBM` appears. -/
def ECapBMAt (st : EStore) (v : ENodeView) : Prop :=
  st.findBMOfView v = none → st.capOKBM

/-- A non-binder view never reaches the datum array. -/
theorem ECapBMAt.of_findBMOfView {st : EStore} {v : ENodeView} {mi : BMIdx}
    (h : st.findBMOfView v = some mi) : ECapBMAt st v := by
  intro hf; rw [h] at hf; exact absurd hf (by simp)

/-- A non-binder view never reaches the datum array: `findBMOfView` answers
`some (Idx.ofWord 0)` at all eight of them, by definition. -/
theorem ECapBMAt.of_no_bm {st : EStore} {v : ENodeView}
    (h : EStore.eViewNeedsBM v = false) : ECapBMAt st v := by
  cases v
  case lam => exact absurd h (by simp [EStore.eViewNeedsBM])
  case forallE => exact absurd h (by simp [EStore.eViewNeedsBM])
  all_goals exact ECapBMAt.of_findBMOfView (mi := Idx.ofWord 0) rfl

/-- `Arena.internE` at a NON-binder view IS `Arena.internNodeE` (task
#97-T2-LOCKSTEP D6: the two binder arms are the Rust's datum-then-node
sequence, and the eight others share one body). -/
theorem internE_eq_node {v : ENodeView} (hbm : EStore.eViewNeedsBM v = false) :
    Arena.internE v = Arena.internNodeE v := by
  cases v <;> first | rfl | exact absurd hbm (by simp [EStore.eViewNeedsBM])

/-- `Arena.internNodeE`'s run: on a cons hit the store does not move, on a
miss the node array's test is the only one. -/
theorem internNodeE_run_of_cap {lst : AState} {v : ENodeView}
    (hcap : ECapAt lst.store v) :
    (Arena.internNodeE v).run lst
      = .ok ((lst.store.intern v).2,
             { lst with store := (lst.store.intern v).1 }) := by
  rw [Arena.internNodeE, run_get_bind]
  cases hf : lst.store.find? v with
  | some h =>
    rw [intern_of_find hf]
    rfl
  | none =>
    simp only []
    rw [if_pos (hcap hf)]
    cases hi : lst.store.intern v with
    | mk st1 h1 => rfl

/-- `Arena.internE`'s run at a NON-binder view: `internNodeE_run_of_cap`. -/
theorem internE_run_of_cap {lst : AState} {v : ENodeView}
    (hbm : EStore.eViewNeedsBM v = false) (hcap : ECapAt lst.store v) :
    (Arena.internE v).run lst
      = .ok ((lst.store.intern v).2,
             { lst with store := (lst.store.intern v).1 }) := by
  rw [internE_eq_node hbm]; exact internNodeE_run_of_cap hcap

/-! ## Finding 16's clause, at an `intern` wrapper (task #97-P5-Specs)

`Refine2/AbsState.lean`'s `AStateRel` now carries `StoreWF` on the TWIN store,
so every producer of the relation owes it.  `Arena/WFProofs.lean`'s
`EStore.intern_wf` is the discharge at an intern and it wants two things:

* **`capOK`** — which is task #97-P5-3 round 3 §1's `ECapAt` on the MISS path
  and vacuous on the hit path, because `intern_of_find` says the store does
  not move there.  So the port's own `Tbl::full` pays for it, exactly as
  round 3 predicted (*"finding 14's real dividend is that it makes this
  clause provable"*).
* **`ViewOK`** — the children decode.  That one is NOT free and is not the
  port's to give: a walk that interns `app f a` knows `f` and `a` decode
  because it just interned them (`EStore.intern_spec`'s `view` conjunct), and
  nothing weaker proves it.  It therefore becomes a hypothesis of the eight
  non-binder wrappers and the two binder dispatchers — one hypothesis, in the
  shape `EStore.ViewOK` already has, so a caller discharges it with the
  builders below. -/

/-- The clause at `EStore.intern`: `intern_wf` on the miss, and on the hit the
store does not move at all (`intern_of_find`), so there is nothing to prove. -/
theorem intern_storeWF {st : EStore} {v : ENodeView} (hwf : StoreWF st)
    (hview : st.ViewOK v) (hcap : ECapAt st v) (hbm : ECapBMAt st v) :
    StoreWF (st.intern v).1 := by
  cases hf : st.find? v with
  | some h => rw [intern_of_find hf]; exact hwf
  | none => exact EStore.intern_wf hwf hview ⟨hcap hf, hbm⟩

/-- **The inversion of `Arena.internNodeE`'s run**: a successful run passed the
node array's test and ended at `EStore.intern`.  It is the twin-side fact the
deprecated shims below need to rebuild `StoreWF` and `Ext` (task
#97-T2-LOCKSTEP); no lockstep statement uses it. -/
theorem internNodeE_run_inv {lst lst' : AState} {v : ENodeView} {h : EIdx}
    (hrun : (Arena.internNodeE v).run lst = .ok (h, lst')) :
    ECapAt lst.store v ∧ lst' = { lst with store := (lst.store.intern v).1 } := by
  rw [Arena.internNodeE, run_get_bind] at hrun
  cases hf : lst.store.find? v with
  | some i =>
    simp only [hf] at hrun
    have he : (i, lst) = (h, lst') := Except.ok.inj hrun
    simp only [Prod.mk.injEq] at he
    refine ⟨ECapAt.of_find_ne (by rw [hf]; simp), ?_⟩
    rw [intern_of_find hf, ← he.2]
  | none =>
    simp only [hf] at hrun
    by_cases hc : (if lst.store.scratchOn then lst.store.scr.sizeOf v
          else lst.store.pers.sizeOf v) < Idx.idxCap
    · rw [if_pos hc] at hrun
      refine ⟨fun _ => hc, ?_⟩
      cases hi : lst.store.intern v with
      | mk st1 h1 =>
        rw [hi] at hrun
        have he : (h1, ({ lst with store := st1 } : AState)) = (h, lst') :=
          Except.ok.inj hrun
        simp only [Prod.mk.injEq] at he
        rw [← he.2]
    · rw [if_neg hc, arena_fail_run] at hrun; exact absurd hrun (by simp)

/-- The twin's own two facts at a successful non-binder `internE` (task
#97-T2-LOCKSTEP): what `Sim₀.toSim` wants of a deprecated intern shim. -/
theorem internNodeE_run_wf {lst lst' : AState} {v : ENodeView} {h : EIdx}
    (hwf : StoreWF lst.store) (hview : lst.store.ViewOK v)
    (hrun : (Arena.internNodeE v).run lst = .ok (h, lst'))
    (hbm : EStore.eViewNeedsBM v = false) :
    StoreWF lst'.store ∧ Ext lst.store lst'.store := by
  obtain ⟨hc, rfl⟩ := internNodeE_run_inv hrun
  exact ⟨intern_storeWF hwf hview hc (ECapBMAt.of_no_bm hbm), EStore.intern_ext _ _⟩

/-! ### The ten `ViewOK` builders

One per constructor, so that a caller says what it knows (a child's `view`
is `some`) rather than assembling a four-field structure.  `bvar` and `lit`
have no children at all and need no hypothesis. -/

theorem viewOK_bvar {st : EStore} (k : Nat) : st.ViewOK (.bvar k) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc,
   by intro c hc; simp [ENodeView.nchildren] at hc,
   by intro c hc; simp [ENodeView.lchildren] at hc,
   by intro c hc; simp [ENodeView.lschildren] at hc⟩

theorem viewOK_lit {st : EStore} (l : ConLeche.Literal) : st.ViewOK (.lit l) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc,
   by intro c hc; simp [ENodeView.nchildren] at hc,
   by intro c hc; simp [ENodeView.lchildren] at hc,
   by intro c hc; simp [ENodeView.lschildren] at hc⟩

theorem viewOK_fvar {st : EStore} {k : Nat} {ty : EIdx}
    (hty : (st.view ty).isSome = true) : st.ViewOK (.fvar k ty) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc; subst hc; exact hty,
   by intro c hc; simp [ENodeView.nchildren] at hc,
   by intro c hc; simp [ENodeView.lchildren] at hc,
   by intro c hc; simp [ENodeView.lschildren] at hc⟩

theorem viewOK_sort {st : EStore} {u : LIdx}
    (hu : (st.ls.view u).isSome = true) : st.ViewOK (.sort u) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc,
   by intro c hc; simp [ENodeView.nchildren] at hc,
   by intro c hc; simp [ENodeView.lchildren] at hc; subst hc; exact hu,
   by intro c hc; simp [ENodeView.lschildren] at hc⟩

theorem viewOK_const {st : EStore} {n : NIdx} {us : LsIdx}
    (hn : (st.ns.view n).isSome = true) (hus : (st.lss.view us).isSome = true) :
    st.ViewOK (.const n us) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc,
   by intro c hc; simp [ENodeView.nchildren] at hc; subst hc; exact hn,
   by intro c hc; simp [ENodeView.lchildren] at hc,
   by intro c hc; simp [ENodeView.lschildren] at hc; subst hc; exact hus⟩

theorem viewOK_app {st : EStore} {f a : EIdx} (hf : (st.view f).isSome = true)
    (ha : (st.view a).isSome = true) : st.ViewOK (.app f a) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact hf
      · exact ha,
   by intro c hc; simp [ENodeView.nchildren] at hc,
   by intro c hc; simp [ENodeView.lchildren] at hc,
   by intro c hc; simp [ENodeView.lschildren] at hc⟩

theorem viewOK_letE {st : EStore} {ty v b : EIdx} (hty : (st.view ty).isSome = true)
    (hv : (st.view v).isSome = true) (hb : (st.view b).isSome = true) :
    st.ViewOK (.letE ty v b) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl | rfl
      · exact hty
      · exact hv
      · exact hb,
   by intro c hc; simp [ENodeView.nchildren] at hc,
   by intro c hc; simp [ENodeView.lchildren] at hc,
   by intro c hc; simp [ENodeView.lschildren] at hc⟩

theorem viewOK_proj {st : EStore} {n : NIdx} {i : Nat} {e : EIdx}
    (hn : (st.ns.view n).isSome = true) (he : (st.view e).isSome = true) :
    st.ViewOK (.proj n i e) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc; subst hc; exact he,
   by intro c hc; simp [ENodeView.nchildren] at hc; subst hc; exact hn,
   by intro c hc; simp [ENodeView.lchildren] at hc,
   by intro c hc; simp [ENodeView.lschildren] at hc⟩

theorem viewOK_lam {st : EStore} {ty b : EIdx} {m : ConLeche.BinderMeta}
    (hty : (st.view ty).isSome = true) (hb : (st.view b).isSome = true) :
    st.ViewOK (.lam ty b m) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact hty
      · exact hb,
   by intro c hc; simp [ENodeView.nchildren] at hc,
   by intro c hc; simp [ENodeView.lchildren] at hc,
   by intro c hc; simp [ENodeView.lschildren] at hc⟩

theorem viewOK_forallE {st : EStore} {ty b : EIdx} {m : ConLeche.BinderMeta}
    (hty : (st.view ty).isSome = true) (hb : (st.view b).isSome = true) :
    st.ViewOK (.forallE ty b m) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact hty
      · exact hb,
   by intro c hc; simp [ENodeView.nchildren] at hc,
   by intro c hc; simp [ENodeView.lchildren] at hc,
   by intro c hc; simp [ENodeView.lschildren] at hc⟩

theorem intern_e_bvar_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (i : Std.U64)
    {o}
    (hrun : arena.monad.intern_e_bvar pers st i = ok o) :
    Sim₀ absEIdx pers lst o (Arena.internBVarE (absU i)) := by
  rw [arena.monad.intern_e_bvar] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_bvar_abs (ls := lst.store) hrel.store hinv.store hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.intern (.bvar (absU i))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [Arena.internBVarE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_bvar_run₀`. -/
theorem intern_e_bvar_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (i : Std.U64)
    {o}
    (hrun : arena.monad.intern_e_bvar pers st i = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internBVarE (absU i)) :=
  (intern_e_bvar_run₀ hrel.to₀ hinv i hrun).toSim
    (fun _ _ hx => internNodeE_run_wf hrel.storeWF (viewOK_bvar _) hx rfl) (fun _ _ => trivial)

/-- **The port's `intern_e_bvar` leaves the two tier flags alone.**  Finding 14
takes `hcap` and `hchild` off an interning walk's hypothesis list; `hfrozen`
(finding 8) was the third — retired in task #97-P5-Unfreeze — and this is
`estore_intern_bvar_abs`'s third conjunct, lifted to the monad.  The other
seven non-binder arrays want the same one-line addition; this round made it
only here, at `bvar_range`'s leaf (task #97-P5-3 round 3 §4). -/
theorem intern_e_bvar_flags₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {i : Std.U64} {o} (hrun : arena.monad.intern_e_bvar pers st i = ok o) :
    o.2.store.shared_on = st.store.shared_on ∧
      o.2.store.scratch_on = st.store.scratch_on := by
  rw [arena.monad.intern_e_bvar] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  exact ⟨(estore_intern_bvar_abs (ls := lst.store) hrel.store hinv.store hp).2.2.1,
    (estore_intern_bvar_abs (ls := lst.store) hrel.store hinv.store hp).2.2.2.1⟩

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_bvar_flags₀`. -/
theorem intern_e_bvar_flags {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    {i : Std.U64} {o} (hrun : arena.monad.intern_e_bvar pers st i = ok o) :
    o.2.store.shared_on = st.store.shared_on ∧
      o.2.store.scratch_on = st.store.scratch_on := by
  apply intern_e_bvar_flags₀ (hrel := hrel.to₀) <;> assumption


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
skips the persistent cons probe when a child is scratch, and since task
#97-T2-LOCKSTEP D2 the twin's `persFindMaybe` skips it at the same test, so
the two agree with no hypothesis about either store. -/
theorem estore_intern_fvar_abs₀ {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {idx : Std.U64} {ty : arena.handle.EIdx}
    {r} {rs'}
    (h : arena.store.EStore.intern_fvar rs pers idx ty = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.fvar (absU idx) (absEIdx ty))).2 ∧
        StoreRel pers rs' (ls.intern (.fvar (absU idx) (absEIdx ty))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.fvar (absU idx) (absEIdx ty))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) := by
  rw [arena.store.EStore.intern_fvar] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧
      sk = (if rs.scratch_on then EStore.eRecHasScratchChild (ENodeView.fvar (absU idx) (absEIdx ty)) (Idx.ofWord 0) else false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := eidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      rw [if_pos hs, ← e2]
      simp only [EStore.eRecHasScratchChild, EStore.eViewHasScratchChild,
        EStore.bindHasScratchChild, hp1]
      split at hb2 <;> rename_i hbb <;> simp only [Result.ok.injEq] at hb2 <;>
        simp [hbb, ← hb2]
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      rw [if_neg hs, ← e2]
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the twin skips exactly where the port does (task #97-T2-LOCKSTEP D2)
  have hskeq : sk = (if ls.scratchOn then EStore.eRecHasScratchChild (ENodeView.fvar (absU idx) (absEIdx ty)) (Idx.ofWord 0) else false) := by
    rw [hrel.scratchOn]; exact hskp
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.persFindMaybe (ENodeView.fvar (absU idx) (absEIdx ty)) (Idx.ofWord 0) = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_pos hsk]; rfl⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.fvars hinv.perst.fvars fvar_eq2 dupId_eidx
          (P := FVarNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.fvars hinv.perst.fvars fvar_eq2 dupId_eidx
          (P := FVarNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.fvar (absU idx) (absEIdx ty))
      = ls.internAt (.fvar (absU idx) (absEIdx ty)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  rw [hE4]
  cases hitc : hit with
  | some hp =>
    rw [hitc] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ⟨rfl, rfl, rfl⟩⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv,
        ECapAt.of_find_ne (by
          have hpp : ls.persFindMaybe (ENodeView.fvar (absU idx) (absEIdx ty)) (Idx.ofWord 0)
              = some (absEIdx hp) := by rw [hE4, hitc]; rfl
          rw [find?_eq_of_pers rfl hpp]; simp)⟩
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
        refine ⟨?_, ?_, ⟨rfl, hsc.symm, rfl⟩⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with fvars := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with fvars := hinvT }⟩,
            ECapAt.of_find_ne (by
              have hpn : ls.persFindMaybe (ENodeView.fvar (absU idx) (absEIdx ty)) (Idx.ofWord 0) = none := by
                rw [hE4, hitc]; rfl
              have hss : ls.scr.find? (ENodeView.fvar (absU idx) (absEIdx ty)) (Idx.ofWord 0)
                  = some (absEIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
              rw [find?_eq_of_scr rfl hpn (hrel.scratchOn.trans hsc) hss]; simp)⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hsr⟩ := he
          subst hr; subst hsr
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
            ⟨rfl, hsc.symm, rfl⟩⟩
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
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, hsc.symm, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with fvars := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with fvars := hinv1 }⟩,
            ECapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (tbl_not_full_size hrelT hb2 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, by simp [hfz, hsc]⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hsr⟩ := he
        subst hr; subst hsr
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
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
        refine ⟨?_, by intro ee hbad; simp at hbad,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩,
          ECapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
            (tbl_not_full_size hrelP hb2 hfull)⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with fvars := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with fvars := hinv1 }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `estore_intern_fvar_abs₀` (its `hchild` has been
unused since D2). -/
theorem estore_intern_fvar_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {idx : Std.U64} {ty : arena.handle.EIdx}
    -- unused since D2; removed in slice 3
    (hchild : (absEIdx ty).isPersistent = false →
      ls.pers.fvars.find? ⟨absU idx, absEIdx ty⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_fvar rs pers idx ty = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.fvar (absU idx) (absEIdx ty))).2 ∧
        StoreRel pers rs' (ls.intern (.fvar (absU idx) (absEIdx ty))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.fvar (absU idx) (absEIdx ty))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) :=
  estore_intern_fvar_abs₀ hrel hinv h


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
scratch, and since task #97-T2-LOCKSTEP D2 the twin's `persFindMaybe` skips
it at the same test, so the two agree with no hypothesis. -/
theorem estore_intern_sort_abs₀ {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {u : arena.handle.LIdx}
    {r} {rs'}
    (h : arena.store.EStore.intern_sort rs pers u = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.sort (absLIdx u))).2 ∧
        StoreRel pers rs' (ls.intern (.sort (absLIdx u))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.sort (absLIdx u))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) := by
  rw [arena.store.EStore.intern_sort] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧
      sk = (if rs.scratch_on then EStore.eRecHasScratchChild (ENodeView.sort (absLIdx u)) (Idx.ofWord 0) else false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := lidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      rw [if_pos hs, ← e2]
      simp only [EStore.eRecHasScratchChild, EStore.eViewHasScratchChild,
        EStore.bindHasScratchChild, hp1]
      split at hb2 <;> rename_i hbb <;> simp only [Result.ok.injEq] at hb2 <;>
        simp [hbb, ← hb2]
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      rw [if_neg hs, ← e2]
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the twin skips exactly where the port does (task #97-T2-LOCKSTEP D2)
  have hskeq : sk = (if ls.scratchOn then EStore.eRecHasScratchChild (ENodeView.sort (absLIdx u)) (Idx.ofWord 0) else false) := by
    rw [hrel.scratchOn]; exact hskp
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.persFindMaybe (ENodeView.sort (absLIdx u)) (Idx.ofWord 0) = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_pos hsk]; rfl⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.sorts hinv.perst.sorts sort_eq2 dupId_eidx
          (P := SortNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.sorts hinv.perst.sorts sort_eq2 dupId_eidx
          (P := SortNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.sort (absLIdx u))
      = ls.internAt (.sort (absLIdx u)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  rw [hE4]
  cases hitc : hit with
  | some hp =>
    rw [hitc] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ⟨rfl, rfl, rfl⟩⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv,
        ECapAt.of_find_ne (by
          have hpp : ls.persFindMaybe (ENodeView.sort (absLIdx u)) (Idx.ofWord 0)
              = some (absEIdx hp) := by rw [hE4, hitc]; rfl
          rw [find?_eq_of_pers rfl hpp]; simp)⟩
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
        refine ⟨?_, ?_, ⟨rfl, hsc.symm, rfl⟩⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with sorts := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with sorts := hinvT }⟩,
            ECapAt.of_find_ne (by
              have hpn : ls.persFindMaybe (ENodeView.sort (absLIdx u)) (Idx.ofWord 0) = none := by
                rw [hE4, hitc]; rfl
              have hss : ls.scr.find? (ENodeView.sort (absLIdx u)) (Idx.ofWord 0)
                  = some (absEIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
              rw [find?_eq_of_scr rfl hpn (hrel.scratchOn.trans hsc) hss]; simp)⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hsr⟩ := he
          subst hr; subst hsr
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
            ⟨rfl, hsc.symm, rfl⟩⟩
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
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, hsc.symm, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with sorts := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with sorts := hinv1 }⟩,
            ECapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (tbl_not_full_size hrelT hb2 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, by simp [hfz, hsc]⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hsr⟩ := he
        subst hr; subst hsr
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
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
        refine ⟨?_, by intro ee hbad; simp at hbad,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩,
          ECapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
            (tbl_not_full_size hrelP hb2 hfull)⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with sorts := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with sorts := hinv1 }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `estore_intern_sort_abs₀` (its `hchild` has been
unused since D2). -/
theorem estore_intern_sort_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {u : arena.handle.LIdx}
    -- unused since D2; removed in slice 3
    (hchild : (absLIdx u).isPersistent = false →
      ls.pers.sorts.find? ⟨absLIdx u⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_sort rs pers u = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.sort (absLIdx u))).2 ∧
        StoreRel pers rs' (ls.intern (.sort (absLIdx u))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.sort (absLIdx u))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) :=
  estore_intern_sort_abs₀ hrel hinv h



/-- `arena::store::EStore.intern_const` against `EStore.intern` at the
`const` view: §3b's six-arm peel at the `consts` array, with finding 7's
`sk` prologue — the port skips the persistent cons probe when a child is
scratch, and since task #97-T2-LOCKSTEP D2 the twin's `persFindMaybe` skips
it at the same test, so the two agree with no hypothesis. -/
theorem estore_intern_const_abs₀ {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {n : arena.handle.NIdx} {us : arena.handle.LsIdx}
    {r} {rs'}
    (h : arena.store.EStore.intern_const rs pers n us = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.const (absNIdx n) (absLsIdx us))).2 ∧
        StoreRel pers rs' (ls.intern (.const (absNIdx n) (absLsIdx us))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.const (absNIdx n) (absLsIdx us))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) := by
  rw [arena.store.EStore.intern_const] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧
      sk = (if rs.scratch_on then EStore.eRecHasScratchChild (ENodeView.const (absNIdx n) (absLsIdx us)) (Idx.ofWord 0) else false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := nidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      rw [if_pos hs, ← e2]
      simp only [EStore.eRecHasScratchChild, EStore.eViewHasScratchChild,
        EStore.bindHasScratchChild, hp1]
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := lsidx_is_persistent_abs hb3
        simp only [Result.ok.injEq] at hb2
        simp [hbb, hp3, ← hb2]
      · simp only [Result.ok.injEq] at hb2
        simp [hbb, ← hb2]
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      rw [if_neg hs, ← e2]
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the twin skips exactly where the port does (task #97-T2-LOCKSTEP D2)
  have hskeq : sk = (if ls.scratchOn then EStore.eRecHasScratchChild (ENodeView.const (absNIdx n) (absLsIdx us)) (Idx.ofWord 0) else false) := by
    rw [hrel.scratchOn]; exact hskp
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.persFindMaybe (ENodeView.const (absNIdx n) (absLsIdx us)) (Idx.ofWord 0) = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_pos hsk]; rfl⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.consts hinv.perst.consts const_eq2 dupId_eidx
          (P := ConstNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.consts hinv.perst.consts const_eq2 dupId_eidx
          (P := ConstNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.const (absNIdx n) (absLsIdx us))
      = ls.internAt (.const (absNIdx n) (absLsIdx us)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  rw [hE4]
  cases hitc : hit with
  | some hp =>
    rw [hitc] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ⟨rfl, rfl, rfl⟩⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv,
        ECapAt.of_find_ne (by
          have hpp : ls.persFindMaybe (ENodeView.const (absNIdx n) (absLsIdx us)) (Idx.ofWord 0)
              = some (absEIdx hp) := by rw [hE4, hitc]; rfl
          rw [find?_eq_of_pers rfl hpp]; simp)⟩
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
        refine ⟨?_, ?_, ⟨rfl, hsc.symm, rfl⟩⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with consts := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with consts := hinvT }⟩,
            ECapAt.of_find_ne (by
              have hpn : ls.persFindMaybe (ENodeView.const (absNIdx n) (absLsIdx us)) (Idx.ofWord 0) = none := by
                rw [hE4, hitc]; rfl
              have hss : ls.scr.find? (ENodeView.const (absNIdx n) (absLsIdx us)) (Idx.ofWord 0)
                  = some (absEIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
              rw [find?_eq_of_scr rfl hpn (hrel.scratchOn.trans hsc) hss]; simp)⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hsr⟩ := he
          subst hr; subst hsr
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
            ⟨rfl, hsc.symm, rfl⟩⟩
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
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, hsc.symm, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with consts := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with consts := hinv1 }⟩,
            ECapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (tbl_not_full_size hrelT hb2 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, by simp [hfz, hsc]⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hsr⟩ := he
        subst hr; subst hsr
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
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
        refine ⟨?_, by intro ee hbad; simp at hbad,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩,
          ECapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
            (tbl_not_full_size hrelP hb2 hfull)⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with consts := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with consts := hinv1 }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `estore_intern_const_abs₀` (its `hchild` has been
unused since D2). -/
theorem estore_intern_const_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {n : arena.handle.NIdx} {us : arena.handle.LsIdx}
    -- unused since D2; removed in slice 3
    (hchild : ((absNIdx n).isPersistent = false ∨ (absLsIdx us).isPersistent = false) →
      ls.pers.consts.find? ⟨absNIdx n, absLsIdx us⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_const rs pers n us = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.const (absNIdx n) (absLsIdx us))).2 ∧
        StoreRel pers rs' (ls.intern (.const (absNIdx n) (absLsIdx us))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.const (absNIdx n) (absLsIdx us))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) :=
  estore_intern_const_abs₀ hrel hinv h



/-- `arena::store::EStore.intern_app` against `EStore.intern` at the
`app` view: §3b's six-arm peel at the `apps` array, with finding 7's
`sk` prologue — the port skips the persistent cons probe when a child is
scratch, and since task #97-T2-LOCKSTEP D2 the twin's `persFindMaybe` skips
it at the same test, so the two agree with no hypothesis. -/
theorem estore_intern_app_abs₀ {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {f a : arena.handle.EIdx}
    {r} {rs'}
    (h : arena.store.EStore.intern_app rs pers f a = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.app (absEIdx f) (absEIdx a))).2 ∧
        StoreRel pers rs' (ls.intern (.app (absEIdx f) (absEIdx a))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.app (absEIdx f) (absEIdx a))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) := by
  rw [arena.store.EStore.intern_app] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧
      sk = (if rs.scratch_on then EStore.eRecHasScratchChild (ENodeView.app (absEIdx f) (absEIdx a)) (Idx.ofWord 0) else false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := eidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      rw [if_pos hs, ← e2]
      simp only [EStore.eRecHasScratchChild, EStore.eViewHasScratchChild,
        EStore.bindHasScratchChild, hp1]
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := eidx_is_persistent_abs hb3
        simp only [Result.ok.injEq] at hb2
        simp [hbb, hp3, ← hb2]
      · simp only [Result.ok.injEq] at hb2
        simp [hbb, ← hb2]
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      rw [if_neg hs, ← e2]
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the twin skips exactly where the port does (task #97-T2-LOCKSTEP D2)
  have hskeq : sk = (if ls.scratchOn then EStore.eRecHasScratchChild (ENodeView.app (absEIdx f) (absEIdx a)) (Idx.ofWord 0) else false) := by
    rw [hrel.scratchOn]; exact hskp
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.persFindMaybe (ENodeView.app (absEIdx f) (absEIdx a)) (Idx.ofWord 0) = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_pos hsk]; rfl⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.apps hinv.perst.apps app_eq2 dupId_eidx
          (P := AppNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.apps hinv.perst.apps app_eq2 dupId_eidx
          (P := AppNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.app (absEIdx f) (absEIdx a))
      = ls.internAt (.app (absEIdx f) (absEIdx a)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  rw [hE4]
  cases hitc : hit with
  | some hp =>
    rw [hitc] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ⟨rfl, rfl, rfl⟩⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv,
        ECapAt.of_find_ne (by
          have hpp : ls.persFindMaybe (ENodeView.app (absEIdx f) (absEIdx a)) (Idx.ofWord 0)
              = some (absEIdx hp) := by rw [hE4, hitc]; rfl
          rw [find?_eq_of_pers rfl hpp]; simp)⟩
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
        refine ⟨?_, ?_, ⟨rfl, hsc.symm, rfl⟩⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with apps := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with apps := hinvT }⟩,
            ECapAt.of_find_ne (by
              have hpn : ls.persFindMaybe (ENodeView.app (absEIdx f) (absEIdx a)) (Idx.ofWord 0) = none := by
                rw [hE4, hitc]; rfl
              have hss : ls.scr.find? (ENodeView.app (absEIdx f) (absEIdx a)) (Idx.ofWord 0)
                  = some (absEIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
              rw [find?_eq_of_scr rfl hpn (hrel.scratchOn.trans hsc) hss]; simp)⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hsr⟩ := he
          subst hr; subst hsr
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
            ⟨rfl, hsc.symm, rfl⟩⟩
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
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, hsc.symm, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with apps := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with apps := hinv1 }⟩,
            ECapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (tbl_not_full_size hrelT hb2 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, by simp [hfz, hsc]⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hsr⟩ := he
        subst hr; subst hsr
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
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
        refine ⟨?_, by intro ee hbad; simp at hbad,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩,
          ECapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
            (tbl_not_full_size hrelP hb2 hfull)⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with apps := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with apps := hinv1 }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `estore_intern_app_abs₀` (its `hchild` has been
unused since D2). -/
theorem estore_intern_app_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {f a : arena.handle.EIdx}
    -- unused since D2; removed in slice 3
    (hchild : ((absEIdx f).isPersistent = false ∨ (absEIdx a).isPersistent = false) →
      ls.pers.apps.find? ⟨absEIdx f, absEIdx a⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_app rs pers f a = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.app (absEIdx f) (absEIdx a))).2 ∧
        StoreRel pers rs' (ls.intern (.app (absEIdx f) (absEIdx a))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.app (absEIdx f) (absEIdx a))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) :=
  estore_intern_app_abs₀ hrel hinv h



/-- `arena::store::EStore.intern_proj` against `EStore.intern` at the
`proj` view: §3b's six-arm peel at the `projs` array, with finding 7's
`sk` prologue — the port skips the persistent cons probe when a child is
scratch, and since task #97-T2-LOCKSTEP D2 the twin's `persFindMaybe` skips
it at the same test, so the two agree with no hypothesis. -/
theorem estore_intern_proj_abs₀ {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {n : arena.handle.NIdx} {i : Std.U64} {ep : arena.handle.EIdx}
    {r} {rs'}
    (h : arena.store.EStore.intern_proj rs pers n i ep = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.proj (absNIdx n) (absU i) (absEIdx ep))).2 ∧
        StoreRel pers rs' (ls.intern (.proj (absNIdx n) (absU i) (absEIdx ep))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.proj (absNIdx n) (absU i) (absEIdx ep))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) := by
  rw [arena.store.EStore.intern_proj] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧
      sk = (if rs.scratch_on then EStore.eRecHasScratchChild (ENodeView.proj (absNIdx n) (absU i) (absEIdx ep)) (Idx.ofWord 0) else false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := nidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      rw [if_pos hs, ← e2]
      simp only [EStore.eRecHasScratchChild, EStore.eViewHasScratchChild,
        EStore.bindHasScratchChild, hp1]
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := eidx_is_persistent_abs hb3
        simp only [Result.ok.injEq] at hb2
        simp [hbb, hp3, ← hb2]
      · simp only [Result.ok.injEq] at hb2
        simp [hbb, ← hb2]
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      rw [if_neg hs, ← e2]
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the twin skips exactly where the port does (task #97-T2-LOCKSTEP D2)
  have hskeq : sk = (if ls.scratchOn then EStore.eRecHasScratchChild (ENodeView.proj (absNIdx n) (absU i) (absEIdx ep)) (Idx.ofWord 0) else false) := by
    rw [hrel.scratchOn]; exact hskp
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.persFindMaybe (ENodeView.proj (absNIdx n) (absU i) (absEIdx ep)) (Idx.ofWord 0) = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_pos hsk]; rfl⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.projs hinv.perst.projs proj_eq2 dupId_eidx
          (P := ProjNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.projs hinv.perst.projs proj_eq2 dupId_eidx
          (P := ProjNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.proj (absNIdx n) (absU i) (absEIdx ep))
      = ls.internAt (.proj (absNIdx n) (absU i) (absEIdx ep)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  rw [hE4]
  cases hitc : hit with
  | some hp =>
    rw [hitc] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ⟨rfl, rfl, rfl⟩⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv,
        ECapAt.of_find_ne (by
          have hpp : ls.persFindMaybe (ENodeView.proj (absNIdx n) (absU i) (absEIdx ep)) (Idx.ofWord 0)
              = some (absEIdx hp) := by rw [hE4, hitc]; rfl
          rw [find?_eq_of_pers rfl hpp]; simp)⟩
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
        refine ⟨?_, ?_, ⟨rfl, hsc.symm, rfl⟩⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with projs := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with projs := hinvT }⟩,
            ECapAt.of_find_ne (by
              have hpn : ls.persFindMaybe (ENodeView.proj (absNIdx n) (absU i) (absEIdx ep)) (Idx.ofWord 0) = none := by
                rw [hE4, hitc]; rfl
              have hss : ls.scr.find? (ENodeView.proj (absNIdx n) (absU i) (absEIdx ep)) (Idx.ofWord 0)
                  = some (absEIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
              rw [find?_eq_of_scr rfl hpn (hrel.scratchOn.trans hsc) hss]; simp)⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hsr⟩ := he
          subst hr; subst hsr
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
            ⟨rfl, hsc.symm, rfl⟩⟩
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
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, hsc.symm, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with projs := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with projs := hinv1 }⟩,
            ECapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (tbl_not_full_size hrelT hb2 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, by simp [hfz, hsc]⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hsr⟩ := he
        subst hr; subst hsr
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
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
        refine ⟨?_, by intro ee hbad; simp at hbad,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩,
          ECapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
            (tbl_not_full_size hrelP hb2 hfull)⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with projs := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with projs := hinv1 }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `estore_intern_proj_abs₀` (its `hchild` has been
unused since D2). -/
theorem estore_intern_proj_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {n : arena.handle.NIdx} {i : Std.U64} {ep : arena.handle.EIdx}
    -- unused since D2; removed in slice 3
    (hchild : ((absNIdx n).isPersistent = false ∨ (absEIdx ep).isPersistent = false) →
      ls.pers.projs.find? ⟨absNIdx n, absU i, absEIdx ep⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_proj rs pers n i ep = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.proj (absNIdx n) (absU i) (absEIdx ep))).2 ∧
        StoreRel pers rs' (ls.intern (.proj (absNIdx n) (absU i) (absEIdx ep))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.proj (absNIdx n) (absU i) (absEIdx ep))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) :=
  estore_intern_proj_abs₀ hrel hinv h



/-- `arena::store::EStore.intern_let_e` against `EStore.intern` at the
`let_e` view: §3b's six-arm peel at the `lets` array, with finding 7's
`sk` prologue — the port skips the persistent cons probe when a child is
scratch, and since task #97-T2-LOCKSTEP D2 the twin's `persFindMaybe` skips
it at the same test, so the two agree with no hypothesis. -/
theorem estore_intern_let_e_abs₀ {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {ty val bo : arena.handle.EIdx}
    {r} {rs'}
    (h : arena.store.EStore.intern_let_e rs pers ty val bo = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))).2 ∧
        StoreRel pers rs' (ls.intern (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) := by
  rw [arena.store.EStore.intern_let_e] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧
      sk = (if rs.scratch_on then EStore.eRecHasScratchChild (ENodeView.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) (Idx.ofWord 0) else false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := eidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      rw [if_pos hs, ← e2]
      simp only [EStore.eRecHasScratchChild, EStore.eViewHasScratchChild,
        EStore.bindHasScratchChild, hp1]
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := eidx_is_persistent_abs hb3
        split at hb2 <;> rename_i hbb2
        · obtain ⟨b4, hb4, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
          have hp4 := eidx_is_persistent_abs hb4
          simp only [Result.ok.injEq] at hb2
          simp [hbb, hp3, hbb2, hp4, ← hb2]
        · simp only [Result.ok.injEq] at hb2
          simp [hbb, hp3, hbb2, ← hb2]
      · simp only [Result.ok.injEq] at hb2
        simp [hbb, ← hb2]
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      rw [if_neg hs, ← e2]
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the twin skips exactly where the port does (task #97-T2-LOCKSTEP D2)
  have hskeq : sk = (if ls.scratchOn then EStore.eRecHasScratchChild (ENodeView.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) (Idx.ofWord 0) else false) := by
    rw [hrel.scratchOn]; exact hskp
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.persFindMaybe (ENodeView.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) (Idx.ofWord 0) = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_pos hsk]; rfl⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.lets hinv.perst.lets let_eq2 dupId_eidx
          (P := LetNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.lets hinv.perst.lets let_eq2 dupId_eidx
          (P := LetNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4, EStore.persFindMaybe_eq_sk hskeq, if_neg hsk]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  have htw : ls.intern (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))
      = ls.internAt (.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) (Idx.ofWord 0) := rfl
  rw [htw, EStore.internAt]
  rw [hE4]
  cases hitc : hit with
  | some hp =>
    rw [hitc] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ⟨rfl, rfl, rfl⟩⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv,
        ECapAt.of_find_ne (by
          have hpp : ls.persFindMaybe (ENodeView.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) (Idx.ofWord 0)
              = some (absEIdx hp) := by rw [hE4, hitc]; rfl
          rw [find?_eq_of_pers rfl hpp]; simp)⟩
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
        refine ⟨?_, ?_, ⟨rfl, hsc.symm, rfl⟩⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with lets := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lets := hinvT }⟩,
            ECapAt.of_find_ne (by
              have hpn : ls.persFindMaybe (ENodeView.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) (Idx.ofWord 0) = none := by
                rw [hE4, hitc]; rfl
              have hss : ls.scr.find? (ENodeView.letE (absEIdx ty) (absEIdx val) (absEIdx bo)) (Idx.ofWord 0)
                  = some (absEIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
              rw [find?_eq_of_scr rfl hpn (hrel.scratchOn.trans hsc) hss]; simp)⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hsr⟩ := he
          subst hr; subst hsr
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
            ⟨rfl, hsc.symm, rfl⟩⟩
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
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, hsc.symm, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with lets := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lets := hinv1 }⟩,
            ECapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (tbl_not_full_size hrelT hb2 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, by simp [hfz, hsc]⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hsr⟩ := he
        subst hr; subst hsr
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
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
        refine ⟨?_, by intro ee hbad; simp at hbad,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩,
          ECapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
            (tbl_not_full_size hrelP hb2 hfull)⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with lets := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with lets := hinv1 }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `estore_intern_let_e_abs₀` (its `hchild` has been
unused since D2). -/
theorem estore_intern_let_e_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {ty val bo : arena.handle.EIdx}
    -- unused since D2; removed in slice 3
    (hchild : ((absEIdx ty).isPersistent = false ∨ (absEIdx val).isPersistent = false ∨ (absEIdx bo).isPersistent = false) →
      ls.pers.lets.find? ⟨absEIdx ty, absEIdx val, absEIdx bo⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_let_e rs pers ty val bo = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))).2 ∧
        StoreRel pers rs' (ls.intern (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) :=
  estore_intern_let_e_abs₀ hrel hinv h



/-- `arena::store::EStore.intern_lit` against `EStore.intern` at the `lit`
view.  The one expression constructor with NO handle child, so the port has
no `sk` prologue and finding 7's hypothesis does not arise; what it does have
is a cons key carrying a VALUE, so `TblRel`'s `RelOn P` asks the caller for
`LiteralWF` (task #97-P5-1 §8's "the cons key's own WF is a hypothesis the
caller owes"). -/
theorem estore_intern_lit_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {l : kernel.expr.Literal}
    (hwf : ConRon.Refine.LiteralWF l) {r} {rs'}
    (h : arena.store.EStore.intern_lit rs pers l = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.intern (.lit (ConRon.Refine.absLiteral l))).2 ∧
        StoreRel pers rs' (ls.intern (.lit (ConRon.Refine.absLiteral l))).1 ∧
        StoreInv pers rs' ∧ ECapAt ls (.lit (ConRon.Refine.absLiteral l))) ∧
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
  have hfind : ls.persFindMaybe (ENodeView.lit (ConRon.Refine.absLiteral l)) (Idx.ofWord 0)
      = ls.pers.lits.find? ⟨ConRon.Refine.absLiteral l⟩ := by
    rw [EStore.persFindMaybe_of_noskip rfl]; rfl
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
      exact ⟨rfl, hrel, hinv,
        ECapAt.of_find_ne (by
          have hpp : ls.persFindMaybe (ENodeView.lit (ConRon.Refine.absLiteral l)) (Idx.ofWord 0)
              = some (absEIdx hp) := by rw [hfind, hE3, hitc]; rfl
          rw [find?_eq_of_pers rfl hpp]; simp)⟩
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
            { hinv with scrt := { hinv.scrt with lits := hinvT } },
            ECapAt.of_find_ne (by
              have hpn : ls.persFindMaybe (ENodeView.lit (ConRon.Refine.absLiteral l)) (Idx.ofWord 0) = none := by
                rw [hfind, hE3, hitc]; rfl
              have hss : ls.scr.find? (ENodeView.lit (ConRon.Refine.absLiteral l)) (Idx.ofWord 0)
                  = some (absEIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
              rw [find?_eq_of_scr rfl hpn (hrel.scratchOn.trans hsc) hss]; simp)⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lits := hinv1 }⟩,
            ECapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (tbl_not_full_size hrelT hb1 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
          ⟨hinv.lss, { hinvPerst with lits := hinv1 }, hinv.scrt⟩,
          ECapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
            (tbl_not_full_size hrelP hb1 hfull)⟩


/-- `arena::store::EStore.intern_bm` against `EStore.internBM` — the binder
datum store (task #97-P6-16): one constructor, no children (so no `sk`
prologue), a `BMIdx` whose `pack` takes no tag, and a derived column that is a
pure hash, which is why `ETablesRel`'s `bms` row observes NOTHING and the
`der` obligation here is `rfl`.  The cons key carries a `PropWhen`, so
`RelOn P` asks the caller for `PropWhenWF`. -/
theorem estore_intern_bm_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {m : kernel.expr.BinderMeta}
    (hwf : ConRon.Refine.PropWhenWF m.pw) {r} {rs'}
    (h : arena.store.EStore.intern_bm rs pers m = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absBMIdx hh = (ls.internBM (ConRon.Refine.absBinderMeta m)).2 ∧
        StoreRel pers rs' (ls.internBM (ConRon.Refine.absBinderMeta m)).1 ∧
        StoreInv pers rs' ∧
        rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss ∧ ECapBMOf ls (ConRon.Refine.absBinderMeta m)) ∧
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
      exact ⟨rfl, hrel, hinv, rfl, rfl, rfl,
        ECapBMOf.of_find_ne (by
          have hpf : ls.persFindBM (ConRon.Refine.absBinderMeta m)
              = some (absBMIdx hp) := by rw [hfind, hE3, hitc]; rfl
          rw [findBM_eq_of_pers hpf]; simp)⟩
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
            { hinv with scrt := { hinv.scrt with bms := hinvT } },
            rfl, rfl, rfl,
            ECapBMOf.of_find_ne (by
              have hpn : ls.persFindBM (ConRon.Refine.absBinderMeta m) = none := by
                rw [hfind, hE3, hitc]; rfl
              have hss : ls.scr.findBM (ConRon.Refine.absBinderMeta m)
                  = some (absBMIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
              rw [findBM_eq_of_scr hpn (hrel.scratchOn.trans hsc) hss]; simp)⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨bfull, hbfull, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
            ⟨hinv.lss, hinv.perst, { hinv.scrt with bms := hinv1 }⟩,
            rfl, rfl, rfl,
            ECapBMOf.of_scr_size (hrel.scratchOn.trans hsc)
              (tbl_not_full_size hrelT hbfull hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨bfull, hbfull, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
          ⟨hinv.lss, { hinvPerst with bms := hinv1 }, hinv.scrt⟩,
          hsh.symm, rfl, rfl,
          ECapBMOf.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
            (tbl_not_full_size hrelP hbfull hfull)⟩


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
theorem estore_intern_lam_i_abs₀ {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {ty bo : arena.handle.EIdx} {mi : arena.handle.BMIdx}
    {r} {rs'}
    (h : arena.store.EStore.intern_lam_i rs pers ty bo mi = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.internLamI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).2 ∧
        StoreRel pers rs' (ls.internLamI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).1 ∧
        StoreInv pers rs' ∧
        EBindCapAt ls ETag.lam (absEIdx ty) (absEIdx bo) (absBMIdx mi)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) := by
  rw [arena.store.EStore.intern_lam_i] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧
      sk = (if rs.scratch_on then EStore.bindHasScratchChild (absEIdx ty) (absEIdx bo) (absBMIdx mi) else false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := eidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      rw [if_pos hs, ← e2]
      simp only [EStore.eRecHasScratchChild, EStore.eViewHasScratchChild,
        EStore.bindHasScratchChild, hp1]
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := eidx_is_persistent_abs hb3
        split at hb2 <;> rename_i hbb2
        · obtain ⟨b4, hb4, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
          have hp4 := bmidx_is_persistent_abs hb4
          simp only [Result.ok.injEq] at hb2
          simp [hbb, hp3, hbb2, hp4, ← hb2]
        · simp only [Result.ok.injEq] at hb2
          simp [hbb, hp3, hbb2, ← hb2]
      · simp only [Result.ok.injEq] at hb2
        simp [hbb, ← hb2]
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      rw [if_neg hs, ← e2]
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the twin skips exactly where the port does (task #97-T2-LOCKSTEP D2)
  have hskeq : sk = (if ls.scratchOn then EStore.bindHasScratchChild (absEIdx ty) (absEIdx bo) (absBMIdx mi) else false) := by
    rw [hrel.scratchOn]; exact hskp
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.persFindBindMaybe ETag.lam ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4, EStore.persFindBindMaybe_eq_sk hskeq, if_pos hsk]; rfl⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.lams hinv.perst.lams bind_eq2 dupId_eidx
          (P := BindNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4, EStore.persFindBindMaybe_eq_sk hskeq, if_neg hsk]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.lams hinv.perst.lams bind_eq2 dupId_eidx
          (P := BindNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4, EStore.persFindBindMaybe_eq_sk hskeq, if_neg hsk]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  simp only [EStore.internLamI, EStore.internBindI]
  rw [hE4]
  cases hitc : hit with
  | some hp =>
    rw [hitc] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ⟨rfl, rfl, rfl⟩⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      have hpf : ls.persFindBindMaybe ETag.lam ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩
          = some (absEIdx hp) := by rw [hE4, hitc]; rfl
      exact ⟨rfl, hrel, hinv,
        EBindCapAt.of_find_ne (by simp only [EStore.findBindI, hpf]; simp)⟩
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
        refine ⟨?_, ?_, ⟨rfl, hsc.symm, rfl⟩⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          have hpn : ls.persFindBindMaybe ETag.lam ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩
              = none := by rw [hE4, hitc]; rfl
          have hss : ls.scr.findBind ETag.lam ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩
              = some (absEIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with lams := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lams := hinvT }⟩,
            EBindCapAt.of_find_ne (by
              simp only [EStore.findBindI, hpn, hrel.scratchOn.trans hsc, if_true, hss]
              simp)⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hsr⟩ := he
          subst hr; subst hsr
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
            ⟨rfl, hsc.symm, rfl⟩⟩
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
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, hsc.symm, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with lams := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with lams := hinv1 }⟩,
            EBindCapAt.of_scr_size (hrel.scratchOn.trans hsc) (by
              simp only [ETables.bindSizeOf, ETag.lam]
              exact tbl_not_full_size hrelT hb2 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, by simp [hfz, hsc]⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hsr⟩ := he
        subst hr; subst hsr
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
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
        refine ⟨?_, by intro ee hbad; simp at hbad,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩,
          EBindCapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc)) (by
            simp only [ETables.bindSizeOf, ETag.lam]
            exact tbl_not_full_size hrelP hb2 hfull)⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with lams := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with lams := hinv1 }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `estore_intern_lam_i_abs₀` (its `hchild` has been
unused since D2). -/
theorem estore_intern_lam_i_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {ty bo : arena.handle.EIdx} {mi : arena.handle.BMIdx}
    -- unused since D2; removed in slice 3
    (hchild : ((absEIdx ty).isPersistent = false ∨
        (absEIdx bo).isPersistent = false ∨ (absBMIdx mi).isPersistent = false) →
      ls.pers.lams.find? ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_lam_i rs pers ty bo mi = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.internLamI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).2 ∧
        StoreRel pers rs' (ls.internLamI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).1 ∧
        StoreInv pers rs' ∧
        EBindCapAt ls ETag.lam (absEIdx ty) (absEIdx bo) (absBMIdx mi)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) :=
  estore_intern_lam_i_abs₀ hrel hinv h


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
theorem estore_intern_forall_e_i_abs₀ {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {ty bo : arena.handle.EIdx} {mi : arena.handle.BMIdx}
    {r} {rs'}
    (h : arena.store.EStore.intern_forall_e_i rs pers ty bo mi = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.internForallEI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).2 ∧
        StoreRel pers rs' (ls.internForallEI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).1 ∧
        StoreInv pers rs' ∧
        EBindCapAt ls ETag.forallE (absEIdx ty) (absEIdx bo) (absBMIdx mi)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) := by
  rw [arena.store.EStore.intern_forall_e_i] at h
  -- the `sk` prologue: `b` is the scratch flag, `sk` says a child is scratch
  obtain ⟨q0, hq0, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨bsc, sk⟩ := q0
  have hpro : bsc = rs.scratch_on ∧
      sk = (if rs.scratch_on then EStore.bindHasScratchChild (absEIdx ty) (absEIdx bo) (absBMIdx mi) else false) := by
    split at hq0 <;> rename_i hs
    · obtain ⟨b1, hb1, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      have hp1 := eidx_is_persistent_abs hb1
      obtain ⟨b2, hb2, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1, hs], ?_⟩
      rw [if_pos hs, ← e2]
      simp only [EStore.eRecHasScratchChild, EStore.eViewHasScratchChild,
        EStore.bindHasScratchChild, hp1]
      split at hb2 <;> rename_i hbb
      · obtain ⟨b3, hb3, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
        have hp3 := eidx_is_persistent_abs hb3
        split at hb2 <;> rename_i hbb2
        · obtain ⟨b4, hb4, hb2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb2
          have hp4 := bmidx_is_persistent_abs hb4
          simp only [Result.ok.injEq] at hb2
          simp [hbb, hp3, hbb2, hp4, ← hb2]
        · simp only [Result.ok.injEq] at hb2
          simp [hbb, hp3, hbb2, ← hb2]
      · simp only [Result.ok.injEq] at hb2
        simp [hbb, ← hb2]
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq0
      obtain ⟨e1, e2⟩ := hq0
      refine ⟨by rw [← e1]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      rw [if_neg hs, ← e2]
  obtain ⟨hbsc, hskp⟩ := hpro
  subst hbsc
  -- the twin skips exactly where the port does (task #97-T2-LOCKSTEP D2)
  have hskeq : sk = (if ls.scratchOn then EStore.bindHasScratchChild (absEIdx ty) (absEIdx bo) (absBMIdx mi) else false) := by
    rw [hrel.scratchOn]; exact hskp
  -- the persistent cons probe, under the `sk` skip and the `shared_on` select
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
  clear hbody
  obtain ⟨e, b1, pers1, hit⟩ := q
  have hE : e = rs.pers ∧ b1 = rs.shared_on ∧ pers1 = pers ∧
      ls.persFindBindMaybe ETag.forallE ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ = hit.map absEIdx := by
    split at hq <;> rename_i hsk
    · simp only [Result.ok.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, h2, h3, h4⟩ := hq
      exact ⟨h1.symm, h2.symm, h3.symm, by rw [← h4, EStore.persFindBindMaybe_eq_sk hskeq, if_pos hsk]; rfl⟩
    · split at hq <;> rename_i hs <;>
        obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
        obtain ⟨h1, h2, h3, h4⟩ := hq
      · refine ⟨h1.symm, by rw [← h2, hs], h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.foralls hinv.perst.foralls bind_eq2 dupId_eidx
          (P := BindNodeWF) trivial (by unfold rPersE; rw [if_pos hs]; exact hf)
        rw [← h4, EStore.persFindBindMaybe_eq_sk hskeq, if_neg hsk]; exact this
      · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, h3.symm, ?_⟩
        have := tbl_find_abs hrel.perst.foralls hinv.perst.foralls bind_eq2 dupId_eidx
          (P := BindNodeWF) trivial (by unfold rPersE; rw [if_neg hs]; exact hf)
        rw [← h4, EStore.persFindBindMaybe_eq_sk hskeq, if_neg hsk]; exact this
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
  rw [hE3] at h
  subst hE1; subst hE2
  simp only [EStore.internForallEI, EStore.internBindI]
  rw [hE4]
  cases hitc : hit with
  | some hp =>
    rw [hitc] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ⟨rfl, rfl, rfl⟩⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      have hpf : ls.persFindBindMaybe ETag.forallE ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩
          = some (absEIdx hp) := by rw [hE4, hitc]; rfl
      exact ⟨rfl, hrel, hinv,
        EBindCapAt.of_find_ne (by simp only [EStore.findBindI, hpf]; simp)⟩
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
        refine ⟨?_, ?_, ⟨rfl, hsc.symm, rfl⟩⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          have hpn : ls.persFindBindMaybe ETag.forallE ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩
              = none := by rw [hE4, hitc]; rfl
          have hss : ls.scr.findBind ETag.forallE ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩
              = some (absEIdx hs) := by rw [hfind2, hfindT, hoc]; rfl
          exact ⟨rfl, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with foralls := hrelT }, hrel.scratchOn.trans hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with foralls := hinvT }⟩,
            EBindCapAt.of_find_ne (by
              simp only [EStore.findBindI, hpn, hrel.scratchOn.trans hsc, if_true, hss]
              simp)⟩
        · intro ee hbad; simp at hbad
      | none =>
        rw [hoc] at h
        obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hsr⟩ := he
          subst hr; subst hsr
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
            ⟨rfl, hsc.symm, rfl⟩⟩
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
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, hsc.symm, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lss, hrel.perst,
              { hrel.scrt with foralls := hrel1 }, hsc⟩,
            ⟨hinv.lss, hinv.perst, { hinv.scrt with foralls := hinv1 }⟩,
            EBindCapAt.of_scr_size (hrel.scratchOn.trans hsc) (by
              simp only [ETables.bindSizeOf, ETag.forallE]
              exact tbl_not_full_size hrelT hb2 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      by_cases hfz : rs.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, by simp [hfz, hsc]⟩
      have hsh : rs.shared_on = false := by simpa using hfz
      rw [hsh] at h
      have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hsh]; rfl
      obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hsr⟩ := he
        subst hr; subst hsr
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
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
        refine ⟨?_, by intro ee hbad; simp at hbad,
          ⟨hsh.symm, (show rs.scratch_on = false by simpa using hsc).symm, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lss, ?_, hrel.scrt, ?_⟩,
          ⟨hinv.lss, ?_, hinv.scrt⟩,
          EBindCapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc)) (by
            simp only [ETables.bindSizeOf, ETag.forallE]
            exact tbl_not_full_size hrelP hb2 hfull)⟩
        · show ETablesRel (rPersE pers _) _
          unfold rPersE; rw [if_neg (by simp)]
          exact { hrelPerst with foralls := hrel1 }
        · simpa using hsc
        · show ETablesInv (rPersE pers _)
          unfold rPersE; rw [if_neg (by simp)]
          exact { hinvPerst with foralls := hinv1 }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `estore_intern_forall_e_i_abs₀` (its `hchild` has been
unused since D2). -/
theorem estore_intern_forall_e_i_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {ty bo : arena.handle.EIdx} {mi : arena.handle.BMIdx}
    -- unused since D2; removed in slice 3
    (hchild : ((absEIdx ty).isPersistent = false ∨
        (absEIdx bo).isPersistent = false ∨ (absBMIdx mi).isPersistent = false) →
      ls.pers.foralls.find? ⟨absEIdx ty, absEIdx bo, absBMIdx mi⟩ = none)
    {r} {rs'}
    (h : arena.store.EStore.intern_forall_e_i rs pers ty bo mi = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.internForallEI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).2 ∧
        StoreRel pers rs' (ls.internForallEI (absEIdx ty) (absEIdx bo) (absBMIdx mi)).1 ∧
        StoreInv pers rs' ∧
        EBindCapAt ls ETag.forallE (absEIdx ty) (absEIdx bo) (absBMIdx mi)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) :=
  estore_intern_forall_e_i_abs₀ hrel hinv h

/-! ## The binder arms' side conditions, CONCLUDED (task #97-P5-Mut round 2)

Task #97-P5-Twin round 2 §4 named the route and priced it at ~80 lines: the
port's `intern_lam_i` tests `Tbl::full` on the binder array exactly where it
appends, so `estore_intern_lam_i_abs` now concludes `EBindCapAt` at the store
it ran on, and what is left is to carry that from the SHIFTED store
`(ls.internBM m).1` and the datum handle `(ls.internBM m).2` back to `ECapAt ls
(.lam ty b m)`.  When the datum probe HIT the two guards are the same probe;
when it MISSED the handle is fresh, and "no cons key names a datum handle that
decodes nowhere" is `StoreWF`'s `bmKeyP`/`bmKeyS` read against `bmConsP`.  The
one fact about `Arena/` the round had expected to have to add — the appended
datum handle decodes nowhere BEFORE the append — is `getBM_eq_none_of_size` at
`pushBM_idxNat`, both already there, so nothing crosses the Arena boundary.

`hchild` falls the same way it does at the six non-binder arms: at a store
whose datum table answers `mi` for `m`, `pers.lams.find? ⟨ty, b, mi⟩` IS
`persFind? (.lam ty b m)`, and `persFind?_none_of_echild` plus
`persFindBM_of_view_pers` (a persistent binder names a persistent datum) close
the three disjuncts. -/

theorem persFindBM_none_of_findBM {st : EStore} {m : ConLeche.BinderMeta}
    (hf : st.findBM m = none) : st.persFindBM m = none := by
  cases hp : st.persFindBM m with
  | none => rfl
  | some i => simp [EStore.findBM, hp] at hf

/-- **The datum handle `internBM` APPENDS decodes nowhere in the store it was
appended to**: its index is the datum array's old size. -/
theorem viewBM_internBM_fresh {st : EStore} {m : ConLeche.BinderMeta}
    (hf : st.findBM m = none) (hcap : st.capOKBM) :
    st.viewBM (st.internBM m).2 = none := by
  have hp := persFindBM_none_of_findBM hf
  cases hon : st.scratchOn with
  | true =>
    have hs : st.scr.findBM m = none := by
      simpa [EStore.findBM, hp, hon] using hf
    have hc : st.scr.bms.size < Idx.idxCap := by
      simpa [EStore.capOKBM, hon, ETables.bmSize] using hcap
    rw [EStore.internBM_push_scr hp hon hs]
    have htr : (Idx.tierS : UInt32).toNat < 2 := by decide
    have hpS : (st.scr.pushBM m (hash m.pw) Idx.tierS).2.isPersistent = false := by
      simp only [Idx.isPersistent, ETables.pushBM_tier htr hc]; decide
    simp only [EStore.viewBM, EStore.persGetBM, hpS, hon, Bool.false_eq_true, if_false,
      if_true]
    exact ETables.getBM_eq_none_of_size (ETables.pushBM_idxNat htr hc)
  | false =>
    have hc : st.pers.bms.size < Idx.idxCap := by
      simpa [EStore.capOKBM, hon, ETables.bmSize] using hcap
    rw [EStore.internBM_push_pers hp hon]
    have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
    have hpP : (st.pers.pushBM m (hash m.pw) Idx.tierP).2.isPersistent = true := by
      simp only [Idx.isPersistent, ETables.pushBM_tier htr hc]; decide
    simp only [EStore.viewBM, EStore.persGetBM, hpP, if_true]
    exact ETables.getBM_eq_none_of_size (ETables.pushBM_idxNat htr hc)

/-- **No binder cons key names a datum handle that decodes nowhere** —
`bmKeyP`/`bmKeyS` against `bmConsP`/`viewBM_of_findBM`. -/
theorem findBindI_none_of_viewBM_none {st : EStore} (hwf : StoreWF st)
    {ty b : EIdx} {mi : BMIdx} (m : ConLeche.BinderMeta)
    (hv : st.viewBM mi = none) :
    st.findBindI ETag.lam ty b mi = none ∧ st.findBindI ETag.forallE ty b mi = none := by
  obtain ⟨rk, hw⟩ := hwf
  have kP : ∀ (v : ENodeView), v.bmOf = some m → st.pers.find? v mi = none := by
    intro v hbm
    cases hj : st.pers.find? v mi with
    | none => rfl
    | some j =>
      rcases hw.bmKeyP v mi j hj with h | ⟨m', hm'⟩
      · rw [hbm] at h; cases h
      · rw [((hw.bmConsP m' mi).mp hm').1] at hv; cases hv
  have kS : ∀ (v : ENodeView), v.bmOf = some m → st.scr.find? v mi = none := by
    intro v hbm
    cases hj : st.scr.find? v mi with
    | none => rfl
    | some j =>
      rcases hw.bmKeyS v mi j hj with h | ⟨m', hm'⟩
      · rw [hbm] at h; cases h
      · rw [hw.viewBM_of_findBM hm'] at hv; cases hv
  have hPL : st.pers.lams.find? ⟨ty, b, mi⟩ = none := kP (.lam ty b m) rfl
  have hSL : st.scr.lams.find? ⟨ty, b, mi⟩ = none := kS (.lam ty b m) rfl
  have hPF : st.pers.foralls.find? ⟨ty, b, mi⟩ = none := kP (.forallE ty b m) rfl
  have hSF : st.scr.foralls.find? ⟨ty, b, mi⟩ = none := kS (.forallE ty b m) rfl
  constructor
  · simp [EStore.findBindI, EStore.persFindBindMaybe, ETables.findBind, hPL, hSL]
  · simp [EStore.findBindI, EStore.persFindBindMaybe, ETables.findBind, ETag.lam, ETag.forallE, hPF, hSF]

/-- `internBM` moves neither binder array, nor the tier flag. -/
theorem findBindI_internBM (st : EStore) (m : ConLeche.BinderMeta) (tag : UInt32)
    (ty b : EIdx) (mi : BMIdx) :
    (st.internBM m).1.findBindI tag ty b mi = st.findBindI tag ty b mi := by
  rcases EStore.internBM_cases st m with he | he | he <;> rw [he] <;> rfl

theorem bindSize_internBM (st : EStore) (m : ConLeche.BinderMeta) (tag : UInt32) :
    (if (st.internBM m).1.scratchOn then (st.internBM m).1.scr.bindSizeOf tag
      else (st.internBM m).1.pers.bindSizeOf tag)
      = (if st.scratchOn then st.scr.bindSizeOf tag else st.pers.bindSizeOf tag) := by
  rcases EStore.internBM_cases st m with he | he | he <;> rw [he] <;> rfl

/-- At a datum handle the cons table answers, the node probe IS the binder
probe. -/
theorem findAt_lam_eq_findBindI (st : EStore) (ty b : EIdx) (m : ConLeche.BinderMeta)
    (mi : BMIdx) : st.findAt (.lam ty b m) mi = st.findBindI ETag.lam ty b mi := by
  simp only [EStore.findAt, EStore.findBindI, EStore.persFindMaybe,
    EStore.persFindBindMaybe, EStore.eRecHasScratchChild, ETables.find?, ETables.findBind,
    beq_self_eq_true, if_true]

theorem findAt_forallE_eq_findBindI (st : EStore) (ty b : EIdx) (m : ConLeche.BinderMeta)
    (mi : BMIdx) :
    st.findAt (.forallE ty b m) mi = st.findBindI ETag.forallE ty b mi := by
  simp only [EStore.findAt, EStore.findBindI, EStore.persFindMaybe,
    EStore.persFindBindMaybe, EStore.eRecHasScratchChild, ETables.find?, ETables.findBind,
    ETag.lam, ETag.forallE]
  rfl

/-- **`ECapAt` at a binder view, from the port's own test at the binder
array**, `lam` and `forallE` in one: the four side facts are each a one-line
instance at either constructor. -/
theorem ECapAt_bind_of {ls : EStore} (hwf : StoreWF ls) {tag : UInt32} {ty b : EIdx}
    {m : ConLeche.BinderMeta} {v : ENodeView}
    (hfov : ∀ st : EStore, st.findBMOfView v = st.findBM m)
    (hfa : ∀ (st : EStore) (mi : BMIdx), st.findAt v mi = st.findBindI tag ty b mi)
    (hsz : ∀ t : ETables, t.sizeOf v = t.bindSizeOf tag)
    (hfresh : ∀ st : EStore, StoreWF st → ∀ mi, st.viewBM mi = none →
      st.findBindI tag ty b mi = none)
    (hbm : ECapBMOf ls m)
    (hcap : EBindCapAt (ls.internBM m).1 tag ty b (ls.internBM m).2) :
    ECapAt ls v := by
  intro hfind
  rw [hsz, hsz]
  have hg : ls.findBindI tag ty b (ls.internBM m).2 = none := by
    cases hfb : ls.findBM m with
    | some mi0 =>
      rw [internBM_of_findBM hfb]
      simp only [EStore.find?, hfov, hfb] at hfind
      rw [← hfa]; exact hfind
    | none => exact hfresh ls hwf _ (viewBM_internBM_fresh hfb (hbm hfb))
  have := hcap (by rw [findBindI_internBM]; exact hg)
  rwa [bindSize_internBM] at this

theorem ECapAt_lam_of {ls : EStore} (hwf : StoreWF ls) {ty b : EIdx}
    {m : ConLeche.BinderMeta} (hbm : ECapBMOf ls m)
    (hcap : EBindCapAt (ls.internBM m).1 ETag.lam ty b (ls.internBM m).2) :
    ECapAt ls (.lam ty b m) :=
  ECapAt_bind_of hwf (fun _ => rfl) (fun st mi => findAt_lam_eq_findBindI st ty b m mi)
    (fun t => by simp [ETables.sizeOf, ETables.bindSizeOf])
    (fun _ h _ hv => (findBindI_none_of_viewBM_none h m hv).1) hbm hcap

theorem ECapAt_forallE_of {ls : EStore} (hwf : StoreWF ls) {ty b : EIdx}
    {m : ConLeche.BinderMeta} (hbm : ECapBMOf ls m)
    (hcap : EBindCapAt (ls.internBM m).1 ETag.forallE ty b (ls.internBM m).2) :
    ECapAt ls (.forallE ty b m) :=
  ECapAt_bind_of hwf (fun _ => rfl)
    (fun st mi => findAt_forallE_eq_findBindI st ty b m mi)
    (fun t => by simp [ETables.sizeOf, ETables.bindSizeOf, ETag.lam, ETag.forallE])
    (fun _ h _ hv => (findBindI_none_of_viewBM_none h m hv).2) hbm hcap

-- `persFind_bind_none_of_child` and `bind_child_disj` moved to
-- `Arena/WFSkip.lean` (task #97-T2-LOCKSTEP D2).

/-! ## `intern_lam` / `intern_forall_e`: the datum intern, then the binder array

Task #97-P5-3 round 2's **one named unfinished piece**.  The port's
`EStore::intern_lam` is `intern_bm` and then `intern_lam_i`; the twin's
`EStore.internLam` is `internBM` and then `internLamI`.  What the composition
needs beyond the two `_abs` lemmas is that **the port's `intern_bm` leaves
`shared_on` and `scratch_on` alone**, so that finding 8's `hfrozen` survives
into the second step — which is now the third conjunct of
`estore_intern_bm_abs`'s success arm.  (Task #97-P5-Unfreeze retired
`hfrozen`; the conjunct stays.) -/

/-- `EStore::intern_lam` against the twin's `internLam`. -/
theorem estore_intern_lam_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {ty bo : arena.handle.EIdx} {m : kernel.expr.BinderMeta}
    (hwf : StoreWF ls)
    (hpw : ConRon.Refine.PropWhenWF m.pw)
    {r} {rs'}
    (h : arena.store.EStore.intern_lam rs pers ty bo m = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh
            = (ls.internLam (absEIdx ty) (absEIdx bo)
                (ConRon.Refine.absBinderMeta m)).2 ∧
        StoreRel pers rs'
            (ls.internLam (absEIdx ty) (absEIdx bo)
              (ConRon.Refine.absBinderMeta m)).1 ∧
        StoreInv pers rs' ∧
        ECapBMOf ls (ConRon.Refine.absBinderMeta m) ∧
        ECapAt ls (.lam (absEIdx ty) (absEIdx bo) (ConRon.Refine.absBinderMeta m)) ∧
        rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_lam] at h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨rb, rs1⟩ := q
  obtain ⟨hok1, herr1⟩ := estore_intern_bm_abs (ls := ls) hrel hinv hpw hq
  cases hrb : rb with
  | Err ee =>
    rw [hrb] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨by intro hh hok; simp at hok, ?_⟩
    intro e2 he2
    simp only [core.result.Result.Err.injEq] at he2
    subst he2
    exact herr1 ee hrb
  | Ok mi =>
    rw [hrb] at h
    obtain ⟨hmi, hrel1, hinv1, hsh, hsc, hlss1, hcb⟩ := hok1 mi hrb
    -- `hchild`, from `StoreWF` at the shifted store
    have hwf1 : StoreWF (ls.internBM (ConRon.Refine.absBinderMeta m)).1 := by
      obtain ⟨rk, hw⟩ := hwf; exact (EStore.internBM_spec hw hcb).1
    have hfb1 : (ls.internBM (ConRon.Refine.absBinderMeta m)).1.findBM
        (ConRon.Refine.absBinderMeta m) = some (ls.internBM (ConRon.Refine.absBinderMeta m)).2 := by
      obtain ⟨rk, hw⟩ := hwf
      obtain ⟨-, -, -, -, -, -, hvbm1, htag1⟩ := EStore.internBM_spec hw hcb
      obtain ⟨rk1, hw1⟩ := hwf1
      exact hw1.findBM_of_viewBM htag1 hvbm1
    have hchild : ((absEIdx ty).isPersistent = false ∨ (absEIdx bo).isPersistent = false ∨
        ((ls.internBM (ConRon.Refine.absBinderMeta m)).2).isPersistent = false) →
      (ls.internBM (ConRon.Refine.absBinderMeta m)).1.pers.lams.find?
        ⟨absEIdx ty, absEIdx bo, (ls.internBM (ConRon.Refine.absBinderMeta m)).2⟩ = none :=
      fun hc => persFind_bind_none_of_child
        (v := .lam (absEIdx ty) (absEIdx bo) (ConRon.Refine.absBinderMeta m))
        hwf1 rfl hfb1 (bind_child_disj _ rfl hc)
    have htw : ls.internLam (absEIdx ty) (absEIdx bo) (ConRon.Refine.absBinderMeta m)
        = (ls.internBM (ConRon.Refine.absBinderMeta m)).1.internLamI (absEIdx ty)
            (absEIdx bo) (ls.internBM (ConRon.Refine.absBinderMeta m)).2 := rfl
    rw [htw, ← hmi]
    obtain ⟨hok2, herr2, hfl2⟩ := estore_intern_lam_i_abs
      (ls := (ls.internBM (ConRon.Refine.absBinderMeta m)).1) hrel1 hinv1
      (by rw [hmi]; exact hchild) h
    refine ⟨fun hh hokk => ?_, herr2⟩
    obtain ⟨a1, a2, a3, a4⟩ := hok2 hh hokk
    exact ⟨a1, a2, a3, hcb, ECapAt_lam_of hwf hcb (by rw [← hmi]; exact a4),
      by rw [hfl2.1, hsh], by rw [hfl2.2.1, hsc], by rw [hfl2.2.2, hlss1]⟩

/-- `EStore::intern_forall_e` against the twin's `internForallE`. -/
theorem estore_intern_forall_e_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {ty bo : arena.handle.EIdx} {m : kernel.expr.BinderMeta}
    (hwf : StoreWF ls)
    (hpw : ConRon.Refine.PropWhenWF m.pw)
    {r} {rs'}
    (h : arena.store.EStore.intern_forall_e rs pers ty bo m = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh
            = (ls.internForallE (absEIdx ty) (absEIdx bo)
                (ConRon.Refine.absBinderMeta m)).2 ∧
        StoreRel pers rs'
            (ls.internForallE (absEIdx ty) (absEIdx bo)
              (ConRon.Refine.absBinderMeta m)).1 ∧
        StoreInv pers rs' ∧
        ECapBMOf ls (ConRon.Refine.absBinderMeta m) ∧
        ECapAt ls (.forallE (absEIdx ty) (absEIdx bo) (ConRon.Refine.absBinderMeta m)) ∧
        rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on ∧
        rs'.lss = rs.lss) ∧
      (∀ e, r = .Err e → absAErrKind e = none) := by
  rw [arena.store.EStore.intern_forall_e] at h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨rb, rs1⟩ := q
  obtain ⟨hok1, herr1⟩ := estore_intern_bm_abs (ls := ls) hrel hinv hpw hq
  cases hrb : rb with
  | Err ee =>
    rw [hrb] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨by intro hh hok; simp at hok, ?_⟩
    intro e2 he2
    simp only [core.result.Result.Err.injEq] at he2
    subst he2
    exact herr1 ee hrb
  | Ok mi =>
    rw [hrb] at h
    obtain ⟨hmi, hrel1, hinv1, hsh, hsc, hlss1, hcb⟩ := hok1 mi hrb
    -- `hchild`, from `StoreWF` at the shifted store
    have hwf1 : StoreWF (ls.internBM (ConRon.Refine.absBinderMeta m)).1 := by
      obtain ⟨rk, hw⟩ := hwf; exact (EStore.internBM_spec hw hcb).1
    have hfb1 : (ls.internBM (ConRon.Refine.absBinderMeta m)).1.findBM
        (ConRon.Refine.absBinderMeta m) = some (ls.internBM (ConRon.Refine.absBinderMeta m)).2 := by
      obtain ⟨rk, hw⟩ := hwf
      obtain ⟨-, -, -, -, -, -, hvbm1, htag1⟩ := EStore.internBM_spec hw hcb
      obtain ⟨rk1, hw1⟩ := hwf1
      exact hw1.findBM_of_viewBM htag1 hvbm1
    have hchild : ((absEIdx ty).isPersistent = false ∨ (absEIdx bo).isPersistent = false ∨
        ((ls.internBM (ConRon.Refine.absBinderMeta m)).2).isPersistent = false) →
      (ls.internBM (ConRon.Refine.absBinderMeta m)).1.pers.foralls.find?
        ⟨absEIdx ty, absEIdx bo, (ls.internBM (ConRon.Refine.absBinderMeta m)).2⟩ = none :=
      fun hc => persFind_bind_none_of_child
        (v := .forallE (absEIdx ty) (absEIdx bo) (ConRon.Refine.absBinderMeta m))
        hwf1 rfl hfb1 (bind_child_disj _ rfl hc)
    have htw : ls.internForallE (absEIdx ty) (absEIdx bo) (ConRon.Refine.absBinderMeta m)
        = (ls.internBM (ConRon.Refine.absBinderMeta m)).1.internForallEI (absEIdx ty)
            (absEIdx bo) (ls.internBM (ConRon.Refine.absBinderMeta m)).2 := rfl
    rw [htw, ← hmi]
    obtain ⟨hok2, herr2, hfl2⟩ := estore_intern_forall_e_i_abs
      (ls := (ls.internBM (ConRon.Refine.absBinderMeta m)).1) hrel1 hinv1
      (by rw [hmi]; exact hchild) h
    refine ⟨fun hh hokk => ?_, herr2⟩
    obtain ⟨a1, a2, a3, a4⟩ := hok2 hh hokk
    exact ⟨a1, a2, a3, hcb, ECapAt_forallE_of hwf hcb (by rw [← hmi]; exact a4),
      by rw [hfl2.1, hsh], by rw [hfl2.2.1, hsc], by rw [hfl2.2.2, hlss1]⟩


/-! ## The node records: `Dup` is the identity, and `abs` is injective

Two obligations per constructor array, which `tbl_find_slot_abs` and
`tbl_push_abs` take: the port's `Dup::dup2` gives the value back (it is a
field-wise copy through the handles' own `dup2`), and the record's
abstraction is injective on well-formed records — the four that carry a
CACHED VALUE (`StrNode`'s code points, `ListNode`'s handle vector, `LitNode`'s
`Literal`, `BMNode`'s `PropWhen`) are the reason `TblRel` is `RelOn P`. -/


/-- `arena::monad::intern_e_fvar` against `internFVarE`. -/
theorem intern_e_fvar_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (idx : Std.U64) (ty : arena.handle.EIdx)
    {o}
    (hrun : arena.monad.intern_e_fvar pers st idx ty = ok o) :
    Sim₀ absEIdx pers lst o (Arena.internFVarE (absU idx) (absEIdx ty)) := by
  rw [arena.monad.intern_e_fvar] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_fvar_abs₀ (ls := lst.store) hrel.store hinv.store hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.intern (.fvar (absU idx) (absEIdx ty))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [Arena.internFVarE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_fvar_run₀`.
`arena::monad::intern_e_fvar` against `internFVarE`. -/
theorem intern_e_fvar_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (idx : Std.U64) (ty : arena.handle.EIdx)
    (hchild : (absEIdx ty).isPersistent = false →
      lst.store.pers.fvars.find? ⟨absU idx, absEIdx ty⟩ = none)
    (hview : lst.store.ViewOK (.fvar (absU idx) (absEIdx ty)))
    {o}
    (hrun : arena.monad.intern_e_fvar pers st idx ty = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internFVarE (absU idx) (absEIdx ty)) :=
  (intern_e_fvar_run₀ hrel.to₀ hinv idx ty hrun).toSim
    (fun _ _ hx => internNodeE_run_wf hrel.storeWF (hview) hx rfl) (fun _ _ => trivial)

/-- `arena::monad::intern_e_sort` against `internSortE`. -/
theorem intern_e_sort_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (u : arena.handle.LIdx)
    {o}
    (hrun : arena.monad.intern_e_sort pers st u = ok o) :
    Sim₀ absEIdx pers lst o (Arena.internSortE (absLIdx u)) := by
  rw [arena.monad.intern_e_sort] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_sort_abs₀ (ls := lst.store) hrel.store hinv.store hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.intern (.sort (absLIdx u))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [Arena.internSortE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_sort_run₀`.
`arena::monad::intern_e_sort` against `internSortE`. -/
theorem intern_e_sort_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (u : arena.handle.LIdx)
    (hchild : (absLIdx u).isPersistent = false →
      lst.store.pers.sorts.find? ⟨absLIdx u⟩ = none)
    (hview : lst.store.ViewOK (.sort (absLIdx u)))
    {o}
    (hrun : arena.monad.intern_e_sort pers st u = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internSortE (absLIdx u)) :=
  (intern_e_sort_run₀ hrel.to₀ hinv u hrun).toSim
    (fun _ _ hx => internNodeE_run_wf hrel.storeWF (hview) hx rfl) (fun _ _ => trivial)

/-- `arena::monad::intern_e_const` against `internConstE`. -/
theorem intern_e_const_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (n : arena.handle.NIdx) (us : arena.handle.LsIdx)
    {o}
    (hrun : arena.monad.intern_e_const pers st n us = ok o) :
    Sim₀ absEIdx pers lst o (Arena.internConstE (absNIdx n) (absLsIdx us)) := by
  rw [arena.monad.intern_e_const] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_const_abs₀ (ls := lst.store) hrel.store hinv.store hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.intern (.const (absNIdx n) (absLsIdx us))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [Arena.internConstE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_const_run₀`.
`arena::monad::intern_e_const` against `internConstE`. -/
theorem intern_e_const_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (n : arena.handle.NIdx) (us : arena.handle.LsIdx)
    (hchild : ((absNIdx n).isPersistent = false ∨ (absLsIdx us).isPersistent = false) →
      lst.store.pers.consts.find? ⟨absNIdx n, absLsIdx us⟩ = none)
    (hview : lst.store.ViewOK (.const (absNIdx n) (absLsIdx us)))
    {o}
    (hrun : arena.monad.intern_e_const pers st n us = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internConstE (absNIdx n) (absLsIdx us)) :=
  (intern_e_const_run₀ hrel.to₀ hinv n us hrun).toSim
    (fun _ _ hx => internNodeE_run_wf hrel.storeWF (hview) hx rfl) (fun _ _ => trivial)

/-- `arena::monad::intern_e_app` against `internAppE`. -/
theorem intern_e_app_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (f a : arena.handle.EIdx)
    {o}
    (hrun : arena.monad.intern_e_app pers st f a = ok o) :
    Sim₀ absEIdx pers lst o (Arena.internAppE (absEIdx f) (absEIdx a)) := by
  rw [arena.monad.intern_e_app] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_app_abs₀ (ls := lst.store) hrel.store hinv.store hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.intern (.app (absEIdx f) (absEIdx a))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [Arena.internAppE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_app_run₀`.
`arena::monad::intern_e_app` against `internAppE`. -/
theorem intern_e_app_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (f a : arena.handle.EIdx)
    (hchild : ((absEIdx f).isPersistent = false ∨ (absEIdx a).isPersistent = false) →
      lst.store.pers.apps.find? ⟨absEIdx f, absEIdx a⟩ = none)
    (hview : lst.store.ViewOK (.app (absEIdx f) (absEIdx a)))
    {o}
    (hrun : arena.monad.intern_e_app pers st f a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internAppE (absEIdx f) (absEIdx a)) :=
  (intern_e_app_run₀ hrel.to₀ hinv f a hrun).toSim
    (fun _ _ hx => internNodeE_run_wf hrel.storeWF (hview) hx rfl) (fun _ _ => trivial)

/-- `arena::monad::intern_e_let_e` against `internLetEE`. -/
theorem intern_e_let_e_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (ty val bo : arena.handle.EIdx)
    {o}
    (hrun : arena.monad.intern_e_let_e pers st ty val bo = ok o) :
    Sim₀ absEIdx pers lst o (Arena.internLetEE (absEIdx ty) (absEIdx val) (absEIdx bo)) := by
  rw [arena.monad.intern_e_let_e] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_let_e_abs₀ (ls := lst.store) hrel.store hinv.store hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.intern (.letE (absEIdx ty) (absEIdx val) (absEIdx bo))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [Arena.internLetEE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_let_e_run₀`.
`arena::monad::intern_e_let_e` against `internLetEE`. -/
theorem intern_e_let_e_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (ty val bo : arena.handle.EIdx)
    (hchild : ((absEIdx ty).isPersistent = false ∨ (absEIdx val).isPersistent = false ∨ (absEIdx bo).isPersistent = false) →
      lst.store.pers.lets.find? ⟨absEIdx ty, absEIdx val, absEIdx bo⟩ = none)
    (hview : lst.store.ViewOK (.letE (absEIdx ty) (absEIdx val) (absEIdx bo)))
    {o}
    (hrun : arena.monad.intern_e_let_e pers st ty val bo = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internLetEE (absEIdx ty) (absEIdx val) (absEIdx bo)) :=
  (intern_e_let_e_run₀ hrel.to₀ hinv ty val bo hrun).toSim
    (fun _ _ hx => internNodeE_run_wf hrel.storeWF (hview) hx rfl) (fun _ _ => trivial)

/-- `arena::monad::intern_e_proj` against `internProjE`. -/
theorem intern_e_proj_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (n : arena.handle.NIdx) (i : Std.U64) (ep : arena.handle.EIdx)
    {o}
    (hrun : arena.monad.intern_e_proj pers st n i ep = ok o) :
    Sim₀ absEIdx pers lst o (Arena.internProjE (absNIdx n) (absU i) (absEIdx ep)) := by
  rw [arena.monad.intern_e_proj] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_proj_abs₀ (ls := lst.store) hrel.store hinv.store hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.intern (.proj (absNIdx n) (absU i) (absEIdx ep))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [Arena.internProjE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_proj_run₀`.
`arena::monad::intern_e_proj` against `internProjE`. -/
theorem intern_e_proj_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (n : arena.handle.NIdx) (i : Std.U64) (ep : arena.handle.EIdx)
    (hchild : ((absNIdx n).isPersistent = false ∨ (absEIdx ep).isPersistent = false) →
      lst.store.pers.projs.find? ⟨absNIdx n, absU i, absEIdx ep⟩ = none)
    (hview : lst.store.ViewOK (.proj (absNIdx n) (absU i) (absEIdx ep)))
    {o}
    (hrun : arena.monad.intern_e_proj pers st n i ep = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internProjE (absNIdx n) (absU i) (absEIdx ep)) :=
  (intern_e_proj_run₀ hrel.to₀ hinv n i ep hrun).toSim
    (fun _ _ hx => internNodeE_run_wf hrel.storeWF (hview) hx rfl) (fun _ _ => trivial)

/-- `arena::monad::intern_e_lit` against `internLitE`. -/
theorem intern_e_lit_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (l : kernel.expr.Literal)
    (hwf : ConRon.Refine.LiteralWF l)
    {o}
    (hrun : arena.monad.intern_e_lit pers st l = ok o) :
    Sim₀ absEIdx pers lst o (Arena.internLitE (ConRon.Refine.absLiteral l)) := by
  rw [arena.monad.intern_e_lit] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_lit_abs (ls := lst.store) hrel.store hinv.store hwf hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.intern (.lit (ConRon.Refine.absLiteral l))).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [Arena.internLitE, internE_run_of_cap rfl hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_lit_run₀`.
`arena::monad::intern_e_lit` against `internLitE`. -/
theorem intern_e_lit_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (l : kernel.expr.Literal)
    (hwf : ConRon.Refine.LiteralWF l)
    {o}
    (hrun : arena.monad.intern_e_lit pers st l = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internLitE (ConRon.Refine.absLiteral l)) :=
  (intern_e_lit_run₀ hrel.to₀ hinv l hwf hrun).toSim
    (fun _ _ hx => internNodeE_run_wf hrel.storeWF (viewOK_lit _) hx rfl) (fun _ _ => trivial)

/-! ## The binder `intern` wrappers (task #97-P5-3 round 2)

Task #97-P5-2 §10 named these five as waiting on ONE lemma, and named it
right: `Ext st (st.internBindI tag ty b mi).1`, which `Arena/WFProofs.lean`
did not have.  It has it now (task #97a follow-up 4: `EStore.internBindI_ext`
and its `internLamI` / `internForallEI` instances), so the three that go
straight to `internBindI` are `intern_e_lit_run`'s proof at the binder array
— the hypotheses being finding 7's `hchild` (the skipped persistent probe),
finding 8's `hfrozen` (retired in task #97-P5-Unfreeze), and the twin's own
capacity test.

**Since task #97-P5-Twin that last one is `EBindCapAt`**, not a naked
conjunction over both tiers: the twin probes `EStore.findBindI` first and
tests `bindSizeOf` on the tier it is about to append to, which is the Rust's
own order (finding 15).  So these two runs have `internE_run_of_caps`'s two
arms — a cons HIT, where `internBindI_of_findBindI` says the store does not
move, and a MISS, which is the side condition. -/

/-- **A binder cons hit interns nothing** — the datum is part of the key the
probe matched, so `internBindI` returns at its first `match`.  This is what
the probe-first `internLamIE` / `internForallEIE` (task #97-P5-Twin) need of
the store tier, and it is `internAt_of_findAt` at the binder arrays. -/
theorem internBindI_of_findBindI {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {h : EIdx} (hf : st.findBindI tag ty b mi = some h) :
    st.internBindI tag ty b mi = (st, h) := by
  simp only [EStore.findBindI] at hf
  simp only [EStore.internBindI]
  cases hp : st.persFindBindMaybe tag ⟨ty, b, mi⟩ with
  | some j =>
    simp only [hp, Option.some.injEq] at hf
    simp only [hp, hf]
  | none =>
    simp only [hp] at hf ⊢
    by_cases hon : st.scratchOn = true
    · simp only [hon, if_true] at hf ⊢
      cases hs : st.scr.findBind tag ⟨ty, b, mi⟩ with
      | some j =>
        simp only [hs, Option.some.injEq] at hf
        simp only [hs, hf]
      | none => simp only [hs] at hf; simp at hf
    · simp only [hon, if_false] at hf; simp at hf

/-- **Finding 16's clause at the two BINDER arrays, on the MISS path only.**

Task #97-P5-Specs put `StoreWF` on the twin store into `AStateRel`, so the two
`_i` wrappers owe it of the store `internBindI` hands back.  They cannot prove
it: `internAt_wf_view` wants `findBMOfView w = some mi` — *"the datum handle is
the cons table's"* — and the `_i` family takes a raw `BMIdx`, so the claim is
FALSE at an arbitrary one.  It is therefore assumed, and the owner is
`Arena/WFProofs.lean`.

What task #97-P5-Twin's probe-first `internLamIE` buys is that it need only be
assumed on the **miss**: a cons hit interns nothing
(`internBindI_of_findBindI`), so the store does not move and `hrel.storeWF` is
the whole answer there.  That is `EBindCapAt`'s shape exactly, and the two
side conditions now read the same way. -/
def EBindWFAt (st : EStore) (tag : UInt32) (ty b : EIdx) (mi : BMIdx) : Prop :=
  st.findBindI tag ty b mi = none → StoreWF (st.internBindI tag ty b mi).1

/-- The unconditional form, at a well-formed store. -/
theorem EBindWFAt.apply {st : EStore} {tag : UInt32} {ty b : EIdx} {mi : BMIdx}
    (h : EBindWFAt st tag ty b mi) (hwf : StoreWF st) :
    StoreWF (st.internBindI tag ty b mi).1 := by
  cases hf : st.findBindI tag ty b mi with
  | some j => rw [internBindI_of_findBindI hf]; exact hwf
  | none => exact h hf

/-- `Arena.internLamIE`'s run: the cons hit moves nothing, and the miss is
below the `lams` array's cap. -/
theorem internLamIE_run_of_cap {lst : AState} {ty b : EIdx} {mi : BMIdx}
    (hcap : EBindCapAt lst.store ETag.lam ty b mi) :
    (Arena.internLamIE ty b mi).run lst
      = .ok ((lst.store.internLamI ty b mi).2,
             { lst with store := (lst.store.internLamI ty b mi).1 }) := by
  rw [Arena.internLamIE, run_get_bind]
  cases hf : lst.store.findBindI ETag.lam ty b mi with
  | some h =>
    rw [EStore.internLamI, internBindI_of_findBindI hf]
    rfl
  | none =>
    rw [if_pos (hcap hf)]
    show (match lst.store.internLamI ty b mi with
          | (st, h) => (do set { lst with store := st }; pure h : AM EIdx)).run lst = _
    cases hi : lst.store.internLamI ty b mi with
    | mk st1 h1 => rfl

/-- `Arena.internForallEIE`'s run, the same at the other array. -/
theorem internForallEIE_run_of_cap {lst : AState} {ty b : EIdx} {mi : BMIdx}
    (hcap : EBindCapAt lst.store ETag.forallE ty b mi) :
    (Arena.internForallEIE ty b mi).run lst
      = .ok ((lst.store.internForallEI ty b mi).2,
             { lst with store := (lst.store.internForallEI ty b mi).1 }) := by
  rw [Arena.internForallEIE, run_get_bind]
  cases hf : lst.store.findBindI ETag.forallE ty b mi with
  | some h =>
    rw [EStore.internForallEI, internBindI_of_findBindI hf]
    rfl
  | none =>
    rw [if_pos (hcap hf)]
    show (match lst.store.internForallEI ty b mi with
          | (st, h) => (do set { lst with store := st }; pure h : AM EIdx)).run lst = _
    cases hi : lst.store.internForallEI ty b mi with
    | mk st1 h1 => rfl

/-- The inversion of `Arena.internLamIE`'s run (task #97-T2-LOCKSTEP): it ends
at `internLamI`.  Twin-only; the deprecated shims' `StoreWF`/`Ext` need it. -/
theorem internLamIE_run_inv {lst lst' : AState} {ty b : EIdx} {mi : BMIdx} {h : EIdx}
    (hrun : (Arena.internLamIE ty b mi).run lst = .ok (h, lst')) :
    lst' = { lst with store := (lst.store.internLamI ty b mi).1 } := by
  rw [Arena.internLamIE, run_get_bind] at hrun
  cases hf : lst.store.findBindI ETag.lam ty b mi with
  | some i =>
    simp only [hf] at hrun
    have he : (i, lst) = (h, lst') := Except.ok.inj hrun
    simp only [Prod.mk.injEq] at he
    rw [← he.2, EStore.internLamI, internBindI_of_findBindI hf]
  | none =>
    simp only [hf] at hrun
    by_cases hc : (if lst.store.scratchOn then lst.store.scr.bindSizeOf ETag.lam
        else lst.store.pers.bindSizeOf ETag.lam) < Idx.idxCap
    · rw [if_pos hc] at hrun
      cases hi : lst.store.internLamI ty b mi with
      | mk st1 h1 =>
        rw [hi] at hrun
        have he : (h1, ({ lst with store := st1 } : AState)) = (h, lst') :=
          Except.ok.inj hrun
        simp only [Prod.mk.injEq] at he
        rw [← he.2]
    · rw [if_neg hc, arena_fail_run] at hrun; exact absurd hrun (by simp)

/-- The same at `Arena.internForallEIE`. -/
theorem internForallEIE_run_inv {lst lst' : AState} {ty b : EIdx} {mi : BMIdx}
    {h : EIdx} (hrun : (Arena.internForallEIE ty b mi).run lst = .ok (h, lst')) :
    lst' = { lst with store := (lst.store.internForallEI ty b mi).1 } := by
  rw [Arena.internForallEIE, run_get_bind] at hrun
  cases hf : lst.store.findBindI ETag.forallE ty b mi with
  | some i =>
    simp only [hf] at hrun
    have he : (i, lst) = (h, lst') := Except.ok.inj hrun
    simp only [Prod.mk.injEq] at he
    rw [← he.2, EStore.internForallEI, internBindI_of_findBindI hf]
  | none =>
    simp only [hf] at hrun
    by_cases hc : (if lst.store.scratchOn then lst.store.scr.bindSizeOf ETag.forallE
        else lst.store.pers.bindSizeOf ETag.forallE) < Idx.idxCap
    · rw [if_pos hc] at hrun
      cases hi : lst.store.internForallEI ty b mi with
      | mk st1 h1 =>
        rw [hi] at hrun
        have he : (h1, ({ lst with store := st1 } : AState)) = (h, lst') :=
          Except.ok.inj hrun
        simp only [Prod.mk.injEq] at he
        rw [← he.2]
    · rw [if_neg hc, arena_fail_run] at hrun; exact absurd hrun (by simp)

/-- `arena::monad::intern_e_lam_i` against `Arena.internLamIE`. -/
theorem intern_e_lam_i_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (mi : arena.handle.BMIdx)
    {o}
    (hrun : arena.monad.intern_e_lam_i pers st ty b mi = ok o) :
    Sim₀ absEIdx pers lst o
      (Arena.internLamIE (absEIdx ty) (absEIdx b) (absBMIdx mi)) := by
  rw [arena.monad.intern_e_lam_i] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_lam_i_abs₀ (ls := lst.store) hrel.store hinv.store hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store :=
        (lst.store.internLamI (absEIdx ty) (absEIdx b) (absBMIdx mi)).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [internLamIE_run_of_cap hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_e_forall_e_i` against `Arena.internForallEIE`. -/
theorem intern_e_forall_e_i_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (mi : arena.handle.BMIdx)
    {o}
    (hrun : arena.monad.intern_e_forall_e_i pers st ty b mi = ok o) :
    Sim₀ absEIdx pers lst o
      (Arena.internForallEIE (absEIdx ty) (absEIdx b) (absBMIdx mi)) := by
  rw [arena.monad.intern_e_forall_e_i] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_forall_e_i_abs₀ (ls := lst.store) hrel.store hinv.store
      hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store :=
        (lst.store.internForallEI (absEIdx ty) (absEIdx b) (absBMIdx mi)).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [internForallEIE_run_of_cap hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_e_bind_i` against `Arena.internBindIE` — the tag
dispatch, and nothing but. -/
theorem intern_e_bind_i_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (tag : Std.U32) (ty : arena.handle.EIdx) (b : arena.handle.EIdx)
    (mi : arena.handle.BMIdx)
    {o}
    (hrun : arena.monad.intern_e_bind_i pers st tag ty b mi = ok o) :
    Sim₀ absEIdx pers lst o
      (Arena.internBindIE (absU32 tag) (absEIdx ty) (absEIdx b) (absBMIdx mi)) := by
  rw [arena.monad.intern_e_bind_i] at hrun
  show AOut₀ absEIdx pers o.1 o.2
    ((Arena.internBindIE (absU32 tag) (absEIdx ty) (absEIdx b) (absBMIdx mi)).run lst)
  rw [Arena.internBindIE]
  by_cases hc : tag = arena.handle.ETAG_LAM
  · subst hc
    rw [if_pos rfl] at hrun
    rw [if_pos (show (absU32 arena.handle.ETAG_LAM == ETag.lam) = true by
      rw [etag_lam_abs]; simp)]
    exact intern_e_lam_i_run₀ hrel hinv ty b mi hrun
  · rw [if_neg hc] at hrun
    have hne : absU32 tag ≠ ETag.lam := by
      rw [← etag_lam_abs]
      intro hcc; exact hc (absU32_inj hcc)
    rw [if_neg (show ¬ ((absU32 tag == ETag.lam) = true) by simp [hne])]
    exact intern_e_forall_e_i_run₀ hrel hinv ty b mi hrun

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_bind_i_run₀`.
`arena::monad::intern_e_bind_i` against `Arena.internBindIE` — the tag
dispatch, and nothing but. -/
theorem intern_e_bind_i_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (tag : Std.U32) (ty : arena.handle.EIdx) (b : arena.handle.EIdx)
    (mi : arena.handle.BMIdx)
    (hchildL : absU32 tag = ETag.lam →
      ((absEIdx ty).isPersistent = false ∨
        (absEIdx b).isPersistent = false ∨ (absBMIdx mi).isPersistent = false) →
      lst.store.pers.lams.find? ⟨absEIdx ty, absEIdx b, absBMIdx mi⟩ = none)
    (hchildF : absU32 tag ≠ ETag.lam →
      ((absEIdx ty).isPersistent = false ∨
        (absEIdx b).isPersistent = false ∨ (absBMIdx mi).isPersistent = false) →
      lst.store.pers.foralls.find? ⟨absEIdx ty, absEIdx b, absBMIdx mi⟩ = none)
    (hwfL : absU32 tag = ETag.lam →
      EBindWFAt lst.store ETag.lam (absEIdx ty) (absEIdx b) (absBMIdx mi))
    (hwfF : absU32 tag ≠ ETag.lam →
      EBindWFAt lst.store ETag.forallE (absEIdx ty) (absEIdx b) (absBMIdx mi))
    {o}
    (hrun : arena.monad.intern_e_bind_i pers st tag ty b mi = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (Arena.internBindIE (absU32 tag) (absEIdx ty) (absEIdx b) (absBMIdx mi)) := by
  refine (intern_e_bind_i_run₀ hrel.to₀ hinv tag ty b mi hrun).toSim ?_
    (fun _ _ => trivial)
  intro b' lst' hx
  rw [Arena.internBindIE] at hx
  split at hx
  · rename_i hc
    have hl : absU32 tag = ETag.lam := by simpa using hc
    rw [internLamIE_run_inv hx]
    exact ⟨(hwfL hl).apply hrel.storeWF, EStore.internLamI_ext _ _ _ _⟩
  · rename_i hc
    have hl : absU32 tag ≠ ETag.lam := by simpa using hc
    rw [internForallEIE_run_inv hx]
    exact ⟨(hwfF hl).apply hrel.storeWF, EStore.internForallEI_ext _ _ _ _⟩

/-! ## `intern` at a binder view IS the datum intern then `internBindI`

**The other half of what `intern_e_lam_run` / `intern_e_forall_e_run` need**,
and the half that is about `Arena/` alone.  Task #97-P5-2 §10 named the route
— `Bridge/StoreBind.lean`'s `EStore.internBindI_eq_internAt` — and `Refine2`
does not import `Bridge`, so the four lemmas are restated here at underscore
names (nothing clashes if the two tiers ever meet).  `intern_lam_eq` /
`intern_forall_e_eq` are the conclusion: the twin's `internLamE ty b m` and
the port's `EStore::intern_lam` do the same two steps in the same order, at a
well-formed store whose datum array is below cap.

**What is still missing for the two `_run` lemmas** is `estore_intern_lam_abs`
— `estore_intern_bm_abs` composed with `estore_intern_lam_i_abs` — and the
one fact that composition needs and no lemma states: the port's `intern_bm`
leaves `shared_on` and `scratch_on` alone, so that finding 8's `hfrozen`
survives into the second step.  That is ~30 lines in the same file and is
this round's one named unfinished piece. -/

/-- `ETag.isBind` is the disjunction it is defined as. -/
theorem ETag_isBind_eq {tag : UInt32} (h : ETag.isBind tag = true) :
    tag = ETag.lam ∨ tag = ETag.forallE := by
  simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at h
  exact h

/-! ## `internBindI` IS `internAt`, once more

The three components are `Bridge/StoreBind.lean`'s and are facts about
`Arena/` alone; they are restated here because `Refine2` does not import
`Bridge` and this tier may not edit `Arena/`.  Underscore names, so that
nothing clashes if the two tiers ever meet. -/

theorem ETables_findBind_eq_find? (t : ETables) {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true) :
    t.findBind tag ⟨ty, b, mi⟩ = t.find? (eBindView tag ty b m) mi := by
  rcases ETag_isBind_eq htag with rfl | rfl
  · rfl
  · rfl

theorem ETables_pushBind_eq_push (t : ETables) {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {m : ConLeche.BinderMeta} (d : UInt64) (tier : UInt32)
    (htag : ETag.isBind tag = true) :
    t.pushBind tag ⟨ty, b, mi⟩ d tier = t.push (eBindView tag ty b m) d mi tier := by
  rcases ETag_isBind_eq htag with rfl | rfl
  · rfl
  · rfl

theorem EStore_derOfBindAtI_eq_derOfView {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true)
    (hder : st.bmDer mi = (hash m.pw, m.pw.hasParams)) :
    st.derOfBindAtI (if tag == ETag.lam then 19 else 23) ty b mi
      = st.derOfView (eBindView tag ty b m) := by
  rcases ETag_isBind_eq htag with rfl | rfl
  · show st.derOfBindAtI 19 ty b mi = st.derOfBindAt 19 ty b m
    simp only [EStore.derOfBindAtI, EStore.derOfBindAt, hder]
  · show st.derOfBindAtI 23 ty b mi = st.derOfBindAt 23 ty b m
    simp only [EStore.derOfBindAtI, EStore.derOfBindAt, hder]

/-- The skipping binder probe is the skipping view probe (task #97-T2-LOCKSTEP
D2): the same test at the same three handles, the same key. -/
theorem EStore_persFindBindMaybe_eq_persFindMaybe (st : EStore) {tag : UInt32}
    {ty b : EIdx} {mi : BMIdx} {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true) :
    st.persFindBindMaybe tag ⟨ty, b, mi⟩ = st.persFindMaybe (eBindView tag ty b m) mi := by
  rcases ETag_isBind_eq htag with rfl | rfl
  · rfl
  · rfl

theorem EStore_internBindI_eq_internAt {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {m : ConLeche.BinderMeta} (htag : ETag.isBind tag = true)
    (hder : st.bmDer mi = (hash m.pw, m.pw.hasParams)) :
    st.internBindI tag ty b mi = st.internAt (eBindView tag ty b m) mi := by
  simp only [EStore.internBindI, EStore.internAt,
    EStore_persFindBindMaybe_eq_persFindMaybe (m := m) _ htag,
    EStore_derOfBindAtI_eq_derOfView htag hder,
    ETables_findBind_eq_find? (m := m) _ htag,
    ETables_pushBind_eq_push (m := m) _ _ _ htag]

/-- The datum just interned decodes to the datum it was asked for, so its
derived pair is the one `derOfBindAtI` reads. -/
theorem bmDer_internBM {st : EStore} {m : ConLeche.BinderMeta} (hwf : StoreWF st)
    (hcap : ECapBMOf st m) :
    (st.internBM m).1.bmDer (st.internBM m).2 = (hash m.pw, m.pw.hasParams) := by
  obtain ⟨rk, hw⟩ := hwf
  obtain ⟨hwf', -, -, -, -, -, hview, -⟩ := EStore.internBM_spec hw hcap
  obtain ⟨rk', hw'⟩ := hwf'
  exact hw'.bmDerExact _ _ hview

/-- **`intern` at a binder view IS the datum intern followed by
`internBindI`** — the twin's `internLamE` against the port's
`EStore::intern_lam`. -/
theorem intern_lam_eq {st : EStore} {ty b : EIdx} {m : ConLeche.BinderMeta}
    (hwf : StoreWF st) (hcap : ECapBMOf st m) :
    st.intern (.lam ty b m) = st.internLam ty b m := by
  show (st.internBM m).1.internAt (.lam ty b m) (st.internBM m).2
    = (st.internBM m).1.internLamI ty b (st.internBM m).2
  rw [EStore.internLamI,
    EStore_internBindI_eq_internAt (m := m) (by simp [ETag.isBind])
      (bmDer_internBM hwf hcap)]
  rfl

theorem intern_forall_e_eq {st : EStore} {ty b : EIdx} {m : ConLeche.BinderMeta}
    (hwf : StoreWF st) (hcap : ECapBMOf st m) :
    st.intern (.forallE ty b m) = st.internForallE ty b m := by
  show (st.internBM m).1.internAt (.forallE ty b m) (st.internBM m).2
    = (st.internBM m).1.internForallEI ty b (st.internBM m).2
  rw [EStore.internForallEI,
    EStore_internBindI_eq_internAt (m := m)
      (by simp [ETag.isBind, ETag.lam, ETag.forallE])
      (bmDer_internBM hwf hcap)]
  rfl

/-- info: 'ConRon.Refine2.intern_lam_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_lam_eq

/-- info: 'ConRon.Refine2.intern_forall_e_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_forall_e_eq

/-! ### The two binder DISPATCHERS, in the Rust's order (task #97-T2-LOCKSTEP D6)

`Arena.internLamE` / `internForallEE` are `internE` at a binder view, and
`internE`'s binder arm is now the port's `EStore::intern_lam` step for step:
`internBME` (the port's `intern_bm`, capacity tested on the datum miss only)
and then `internLamIE` / `internForallEIE` at the datum HANDLE (the port's
`intern_lam_i` / `intern_forall_e_i`, which `intern_e_lam_i_run₀` already
relates).  So the lockstep statements below need no `StoreWF`: they are the
two `_abs` lemmas composed, exactly as the port composes the two functions.

The twin used to probe `find?` over the whole view and then run
`EStore.intern`, and that is where the two twin/Rust divergences slice 3
recorded here came from — the node-array test on a datum MISS (the port first
probes at the fresh handle, which a stale key in `lams` can hit: port `Ok`,
twin `native`), and the derived word recomputed from `m` rather than read off
the datum's stored row.  **Both are fixed in the twin (D6)**, by the arm itself.
What `StoreWF` still buys is the equation to the twin's own composed store step
(`intern_lam_eq`), which only the deprecated shims and
`Refine2/ExprOps/Mut.lean`'s `WOutE` wrappers use. -/

/-- `Arena.internBME`'s run: a datum hit moves nothing, a miss is below the
datum array's cap. -/
theorem internBME_run_of_cap {lst : AState} {m : ConLeche.BinderMeta}
    (hcap : ECapBMOf lst.store m) :
    (Arena.internBME m).run lst
      = .ok ((lst.store.internBM m).2,
             { lst with store := (lst.store.internBM m).1 }) := by
  rw [Arena.internBME, run_get_bind]
  cases hf : lst.store.findBM m with
  | some i =>
    rw [internBM_of_findBM hf]
    rfl
  | none =>
    have hc : (if lst.store.scratchOn = true then lst.store.scr.bmSize
        else lst.store.pers.bmSize) < Idx.idxCap := hcap hf
    simp only []
    rw [if_pos hc]
    cases hi : lst.store.internBM m with
    | mk st1 h1 => rfl

/-- The inversion of `Arena.internBME`'s run. -/
theorem internBME_run_inv {lst lst' : AState} {m : ConLeche.BinderMeta} {i : BMIdx}
    (hrun : (Arena.internBME m).run lst = .ok (i, lst')) :
    ECapBMOf lst.store m ∧ i = (lst.store.internBM m).2 ∧
      lst' = { lst with store := (lst.store.internBM m).1 } := by
  have hcap : ECapBMOf lst.store m := by
    intro hf
    rw [Arena.internBME, run_get_bind] at hrun
    simp only [hf] at hrun
    by_cases hc : (if lst.store.scratchOn then lst.store.scr.bmSize
        else lst.store.pers.bmSize) < Idx.idxCap
    · exact hc
    · rw [if_neg hc, arena_fail_run] at hrun; exact absurd hrun (by simp)
  rw [internBME_run_of_cap hcap] at hrun
  have he := Except.ok.inj hrun
  simp only [Prod.mk.injEq] at he
  exact ⟨hcap, he.1.symm, he.2.symm⟩

/-- A successful `Arena.internLamIE` passed the `lams` array's test. -/
theorem internLamIE_run_cap {lst lst' : AState} {ty b : EIdx} {mi : BMIdx} {h : EIdx}
    (hrun : (Arena.internLamIE ty b mi).run lst = .ok (h, lst')) :
    EBindCapAt lst.store ETag.lam ty b mi := by
  intro hf
  rw [Arena.internLamIE, run_get_bind] at hrun
  simp only [hf] at hrun
  by_cases hc : (if lst.store.scratchOn then lst.store.scr.bindSizeOf ETag.lam
      else lst.store.pers.bindSizeOf ETag.lam) < Idx.idxCap
  · exact hc
  · rw [if_neg hc, arena_fail_run] at hrun; exact absurd hrun (by simp)

/-- The same at `Arena.internForallEIE`. -/
theorem internForallEIE_run_cap {lst lst' : AState} {ty b : EIdx} {mi : BMIdx} {h : EIdx}
    (hrun : (Arena.internForallEIE ty b mi).run lst = .ok (h, lst')) :
    EBindCapAt lst.store ETag.forallE ty b mi := by
  intro hf
  rw [Arena.internForallEIE, run_get_bind] at hrun
  simp only [hf] at hrun
  by_cases hc : (if lst.store.scratchOn then lst.store.scr.bindSizeOf ETag.forallE
      else lst.store.pers.bindSizeOf ETag.forallE) < Idx.idxCap
  · exact hc
  · rw [if_neg hc, arena_fail_run] at hrun; exact absurd hrun (by simp)

/-- The binder arm's run, as the two monadic steps it is. -/
theorem internLamE_run_split {lst : AState} {ty b : EIdx} {m : ConLeche.BinderMeta}
    (hcap : ECapBMOf lst.store m) :
    (Arena.internE (.lam ty b m)).run lst
      = (Arena.internLamIE ty b (lst.store.internBM m).2).run
          { lst with store := (lst.store.internBM m).1 } := by
  show (Arena.internBME m >>= fun mi => Arena.internLamIE ty b mi).run lst = _
  rw [StateT.run_bind, internBME_run_of_cap hcap]
  rfl

theorem internForallEE_run_split {lst : AState} {ty b : EIdx} {m : ConLeche.BinderMeta}
    (hcap : ECapBMOf lst.store m) :
    (Arena.internE (.forallE ty b m)).run lst
      = (Arena.internForallEIE ty b (lst.store.internBM m).2).run
          { lst with store := (lst.store.internBM m).1 } := by
  show (Arena.internBME m >>= fun mi => Arena.internForallEIE ty b mi).run lst = _
  rw [StateT.run_bind, internBME_run_of_cap hcap]
  rfl

/-- A successful binder arm passed the datum step's test. -/
theorem internBind_run_bm {lst lst' : AState} {m : ConLeche.BinderMeta} {h : EIdx}
    {k : BMIdx → AM EIdx}
    (hrun : (Arena.internBME m >>= k).run lst = .ok (h, lst')) :
    ECapBMOf lst.store m := by
  rw [StateT.run_bind] at hrun
  cases h1 : (Arena.internBME m).run lst with
  | error e => rw [h1] at hrun; cases hrun
  | ok p => exact (internBME_run_inv h1).1

/-- **The inversion of the binder arm's run**: both steps succeeded, so both
of the port's tests held where the port makes them. -/
theorem internLamE_run_inv {lst lst' : AState} {ty b : EIdx} {m : ConLeche.BinderMeta}
    {h : EIdx} (hrun : (Arena.internE (.lam ty b m)).run lst = .ok (h, lst')) :
    ECapBMOf lst.store m ∧
      EBindCapAt (lst.store.internBM m).1 ETag.lam ty b (lst.store.internBM m).2 ∧
      lst' = { lst with store := ((lst.store.internBM m).1.internLamI ty b
        (lst.store.internBM m).2).1 } := by
  have hbm : ECapBMOf lst.store m := internBind_run_bm (k := Arena.internLamIE ty b) hrun
  rw [internLamE_run_split hbm] at hrun
  exact ⟨hbm, internLamIE_run_cap hrun, by rw [internLamIE_run_inv hrun]⟩

theorem internForallEE_run_inv {lst lst' : AState} {ty b : EIdx}
    {m : ConLeche.BinderMeta} {h : EIdx}
    (hrun : (Arena.internE (.forallE ty b m)).run lst = .ok (h, lst')) :
    ECapBMOf lst.store m ∧
      EBindCapAt (lst.store.internBM m).1 ETag.forallE ty b (lst.store.internBM m).2 ∧
      lst' = { lst with store := ((lst.store.internBM m).1.internForallEI ty b
        (lst.store.internBM m).2).1 } := by
  have hbm : ECapBMOf lst.store m :=
    internBind_run_bm (k := Arena.internForallEIE ty b) hrun
  rw [internForallEE_run_split hbm] at hrun
  exact ⟨hbm, internForallEIE_run_cap hrun, by rw [internForallEIE_run_inv hrun]⟩

/-- `ECapAt` at a binder view gives the node step's own test at the datum
handle `internBM` answers — no `StoreWF`: on a datum hit the node probe IS
`find?`'s second step, and on a datum miss `find?` already missed. -/
theorem EBindCapAt_internBM_of_ECapAt {ls : EStore} {tag : UInt32} {ty b : EIdx}
    {m : ConLeche.BinderMeta} {v : ENodeView}
    (hfov : ∀ st : EStore, st.findBMOfView v = st.findBM m)
    (hfa : ∀ (st : EStore) (mi : BMIdx), st.findAt v mi = st.findBindI tag ty b mi)
    (hsz : ∀ t : ETables, t.sizeOf v = t.bindSizeOf tag)
    (hcap : ECapAt ls v) :
    EBindCapAt (ls.internBM m).1 tag ty b (ls.internBM m).2 := by
  intro hf
  rw [findBindI_internBM] at hf
  rw [bindSize_internBM]
  have hfind : ls.find? v = none := by
    cases hfb : ls.findBM m with
    | some mi0 =>
      rw [internBM_of_findBM hfb] at hf
      simp only [EStore.find?, hfov, hfb]
      rw [hfa]; exact hf
    | none => simp only [EStore.find?, hfov, hfb]
  have := hcap hfind
  rwa [hsz, hsz] at this

/-- The binder arm's run at a `StoreWF` store, as the twin's composed store
step `EStore.intern`: what the deprecated shims and the `WOutE` wrappers of
`Refine2/ExprOps/Mut.lean` state their outcome with. -/
theorem internE_run_of_caps {lst : AState} {v : ENodeView} (hwf : StoreWF lst.store)
    (hcap : ECapAt lst.store v) (hbm : ECapBMAt lst.store v) :
    (Arena.internE v).run lst
      = .ok ((lst.store.intern v).2,
             { lst with store := (lst.store.intern v).1 }) := by
  cases v
  case lam ty b m =>
    have hbm' : ECapBMOf lst.store m := hbm
    rw [internLamE_run_split hbm', internLamIE_run_of_cap
      (EBindCapAt_internBM_of_ECapAt (fun _ => rfl) (fun st mi => findAt_lam_eq_findBindI st ty b m mi)
        (fun t => by simp [ETables.sizeOf, ETables.bindSizeOf]) hcap),
      intern_lam_eq hwf hbm']
    rfl
  case forallE ty b m =>
    have hbm' : ECapBMOf lst.store m := hbm
    rw [internForallEE_run_split hbm', internForallEIE_run_of_cap
      (EBindCapAt_internBM_of_ECapAt (fun _ => rfl)
        (fun st mi => findAt_forallE_eq_findBindI st ty b m mi)
        (fun t => by simp [ETables.sizeOf, ETables.bindSizeOf, ETag.lam, ETag.forallE])
        hcap),
      intern_forall_e_eq hwf hbm']
    rfl
  all_goals exact internE_run_of_cap rfl hcap

/-- `arena::monad::intern_e_lam` against `Arena.internLamE` — **lockstep**
(task #97-T2-LOCKSTEP D6): the port's `intern_bm` against `internBME`
(`estore_intern_bm_abs`), then its `intern_lam_i` against `internLamIE` at
the handle both answered (`estore_intern_lam_i_abs₀`). -/
theorem intern_e_lam_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (m : kernel.expr.BinderMeta)
    (hpw : ConRon.Refine.PropWhenWF m.pw)
    {o}
    (hrun : arena.monad.intern_e_lam pers st ty b m = ok o) :
    Sim₀ absEIdx pers lst o
      (Arena.internLamE (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.monad.intern_e_lam] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  show AOut₀ absEIdx pers r { st with store := e } _
  rw [arena.store.EStore.intern_lam] at hp
  obtain ⟨q, hq, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
  obtain ⟨rb, rs1⟩ := q
  obtain ⟨hok1, herr1⟩ :=
    estore_intern_bm_abs (ls := lst.store) hrel.store hinv.store hpw hq
  cases hrb : rb with
  | Err ee =>
    rw [hrb] at hp
    have he := Result.ok_injective hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, -⟩ := he
    subst hr
    exact AOut₀.err (AErrSim.of_none (herr1 ee hrb))
  | Ok mi =>
    rw [hrb] at hp
    obtain ⟨hmi, hrel1, hinv1, -, -, -, hcb⟩ := hok1 mi hrb
    obtain ⟨hok2, herr2, -⟩ :=
      estore_intern_lam_i_abs₀
        (ls := (lst.store.internBM (ConRon.Refine.absBinderMeta m)).1) hrel1 hinv1 hp
    cases hr : r with
    | Ok hh =>
      obtain ⟨hhd, hrel', hinv', hcap⟩ := hok2 hh hr
      rw [hmi] at hhd hrel' hcap
      refine AOut₀.ok
        (lst' := { lst with store :=
          ((lst.store.internBM (ConRon.Refine.absBinderMeta m)).1.internLamI
            (absEIdx ty) (absEIdx b)
            (lst.store.internBM (ConRon.Refine.absBinderMeta m)).2).1 }) ?_
        ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
        ⟨hinv', hinv.memos, hinv.caches⟩
      rw [Arena.internLamE, internLamE_run_split hcb, internLamIE_run_of_cap hcap, hhd]
    | Err ee => exact AOut₀.err (AErrSim.of_none (herr2 ee hr))

/-- `arena::monad::intern_e_forall_e` against `Arena.internForallEE` —
lockstep, at the other array. -/
theorem intern_e_forall_e_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (m : kernel.expr.BinderMeta)
    (hpw : ConRon.Refine.PropWhenWF m.pw)
    {o}
    (hrun : arena.monad.intern_e_forall_e pers st ty b m = ok o) :
    Sim₀ absEIdx pers lst o
      (Arena.internForallEE (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.monad.intern_e_forall_e] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  show AOut₀ absEIdx pers r { st with store := e } _
  rw [arena.store.EStore.intern_forall_e] at hp
  obtain ⟨q, hq, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
  obtain ⟨rb, rs1⟩ := q
  obtain ⟨hok1, herr1⟩ :=
    estore_intern_bm_abs (ls := lst.store) hrel.store hinv.store hpw hq
  cases hrb : rb with
  | Err ee =>
    rw [hrb] at hp
    have he := Result.ok_injective hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, -⟩ := he
    subst hr
    exact AOut₀.err (AErrSim.of_none (herr1 ee hrb))
  | Ok mi =>
    rw [hrb] at hp
    obtain ⟨hmi, hrel1, hinv1, -, -, -, hcb⟩ := hok1 mi hrb
    obtain ⟨hok2, herr2, -⟩ :=
      estore_intern_forall_e_i_abs₀
        (ls := (lst.store.internBM (ConRon.Refine.absBinderMeta m)).1) hrel1 hinv1 hp
    cases hr : r with
    | Ok hh =>
      obtain ⟨hhd, hrel', hinv', hcap⟩ := hok2 hh hr
      rw [hmi] at hhd hrel' hcap
      refine AOut₀.ok
        (lst' := { lst with store :=
          ((lst.store.internBM (ConRon.Refine.absBinderMeta m)).1.internForallEI
            (absEIdx ty) (absEIdx b)
            (lst.store.internBM (ConRon.Refine.absBinderMeta m)).2).1 }) ?_
        ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
        ⟨hinv', hinv.memos, hinv.caches⟩
      rw [Arena.internForallEE, internForallEE_run_split hcb,
        internForallEIE_run_of_cap hcap, hhd]
    | Err ee => exact AOut₀.err (AErrSim.of_none (herr2 ee hr))

/-- The twin's own two facts at a successful binder `internE`, at a `StoreWF`
store (task #97-T2-LOCKSTEP D6): what `Sim₀.toSim` wants of the two
deprecated binder shims.  `StoreWF` is used twice — `ECapAt` from the node
step's test (`ECapAt_lam_of`: a stale cons key cannot name the fresh datum),
and the node step as the twin's composed `EStore.intern` (`intern_lam_eq`). -/
theorem internLamE_run_wf {lst lst' : AState} {ty b : EIdx} {m : ConLeche.BinderMeta}
    {h : EIdx} (hwf : StoreWF lst.store) (hview : lst.store.ViewOK (.lam ty b m))
    (hrun : (Arena.internE (.lam ty b m)).run lst = .ok (h, lst')) :
    StoreWF lst'.store ∧ Ext lst.store lst'.store := by
  obtain ⟨hbm, hcap, rfl⟩ := internLamE_run_inv hrun
  have hiv := intern_lam_eq (ty := ty) (b := b) hwf hbm
  show StoreWF (lst.store.internLam ty b m).1 ∧ Ext lst.store (lst.store.internLam ty b m).1
  rw [← hiv]
  exact ⟨intern_storeWF hwf hview (ECapAt_lam_of hwf hbm hcap) hbm, EStore.intern_ext _ _⟩

theorem internForallEE_run_wf {lst lst' : AState} {ty b : EIdx}
    {m : ConLeche.BinderMeta} {h : EIdx} (hwf : StoreWF lst.store)
    (hview : lst.store.ViewOK (.forallE ty b m))
    (hrun : (Arena.internE (.forallE ty b m)).run lst = .ok (h, lst')) :
    StoreWF lst'.store ∧ Ext lst.store lst'.store := by
  obtain ⟨hbm, hcap, rfl⟩ := internForallEE_run_inv hrun
  have hiv := intern_forall_e_eq (ty := ty) (b := b) hwf hbm
  show StoreWF (lst.store.internForallE ty b m).1 ∧
    Ext lst.store (lst.store.internForallE ty b m).1
  rw [← hiv]
  exact ⟨intern_storeWF hwf hview (ECapAt_forallE_of hwf hbm hcap) hbm,
    EStore.intern_ext _ _⟩

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_lam_run₀`.
`arena::monad::intern_e_lam` against `Arena.internLamE`. -/
theorem intern_e_lam_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (m : kernel.expr.BinderMeta)
    (hpw : ConRon.Refine.PropWhenWF m.pw)
    (hview : lst.store.ViewOK (.lam (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)))
    {o}
    (hrun : arena.monad.intern_e_lam pers st ty b m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (Arena.internLamE (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)) :=
  (intern_e_lam_run₀ hrel.to₀ hinv ty b m hpw hrun).toSim
    (fun _ _ hx => internLamE_run_wf hrel.storeWF hview hx) (fun _ _ => trivial)

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_forall_e_run₀`.
`arena::monad::intern_e_forall_e` against `Arena.internForallEE`. -/
theorem intern_e_forall_e_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (ty : arena.handle.EIdx) (b : arena.handle.EIdx) (m : kernel.expr.BinderMeta)
    (hpw : ConRon.Refine.PropWhenWF m.pw)
    (hview : lst.store.ViewOK (.forallE (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)))
    {o}
    (hrun : arena.monad.intern_e_forall_e pers st ty b m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (Arena.internForallEE (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)) :=
  (intern_e_forall_e_run₀ hrel.to₀ hinv ty b m hpw hrun).toSim
    (fun _ _ hx => internForallEE_run_wf hrel.storeWF hview hx) (fun _ _ => trivial)

/-- **`arena::monad::intern_e` against `Arena.internE`, lockstep** (task
#97-T2-LOCKSTEP D6) — the ten-way dispatcher, each arm its wrapper's `₀`
lemma.  No `StoreWF`, no `ViewOK`, no `hchild`: what survives is what is the
port's INPUT's to give — the literal's own well-formedness and the binder
datum's `PropWhen` shape. -/
theorem intern_e_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (v : arena.store.ENodeView)
    (hlit : ∀ l, v = .Lit l → ConRon.Refine.LiteralWF l)
    (hpw : ∀ ty b m, v = .Lam ty b m ∨ v = .ForallE ty b m →
      ConRon.Refine.PropWhenWF m.pw)
    {o}
    (hrun : arena.monad.intern_e pers st v = ok o) :
    Sim₀ absEIdx pers lst o (Arena.internE (absENodeView v)) := by
  cases v with
  | BVar i => exact intern_e_bvar_run₀ hrel hinv i hrun
  | FVar idx ty => exact intern_e_fvar_run₀ hrel hinv idx ty hrun
  | «Sort» u => exact intern_e_sort_run₀ hrel hinv u hrun
  | Const n us => exact intern_e_const_run₀ hrel hinv n us hrun
  | App f a => exact intern_e_app_run₀ hrel hinv f a hrun
  | Lam ty b m => exact intern_e_lam_run₀ hrel hinv ty b m (hpw ty b m (Or.inl rfl)) hrun
  | ForallE ty b m =>
    exact intern_e_forall_e_run₀ hrel hinv ty b m (hpw ty b m (Or.inr rfl)) hrun
  | LetE ty val b => exact intern_e_let_e_run₀ hrel hinv ty val b hrun
  | Lit l => exact intern_e_lit_run₀ hrel hinv l (hlit l rfl) hrun
  | Proj n i e => exact intern_e_proj_run₀ hrel hinv n i e hrun

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_e_run₀`.
**`arena::monad::intern_e` against `Arena.internE`** — the ten-way
dispatcher, and nothing but.

`EStore::intern` is a `match` on the view that calls `intern_bvar` …
`intern_proj`, and `arena::monad::intern_e_bvar` … `intern_e_proj` wrap the
same ten at the same place, so **each arm is definitionally its wrapper** and
the proof is `cases v` above ten `exact`s.

What the arms need is the interesting part, and it is where finding 16's
clause pays a second time: **`hchild` is gone at all ten**, because round 3
§2's `hchild_*` derive it from `StoreWF` and `hrel.storeWF` is that now — at
the two binder arms since task #97-P5-Mut round 2, which also made their
`ECapAt` a conclusion of `estore_intern_{lam,forall_e}_abs`.  What survives
as a hypothesis is what genuinely is not the port's to give — `ViewOK` (the
children decode), the literal's own well-formedness and the binder datum's
`PropWhen` shape. -/
theorem intern_e_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (v : arena.store.ENodeView)
    (hview : lst.store.ViewOK (absENodeView v))
    (hlit : ∀ l, v = .Lit l → ConRon.Refine.LiteralWF l)
    (hpw : ∀ ty b m, v = .Lam ty b m ∨ v = .ForallE ty b m →
      ConRon.Refine.PropWhenWF m.pw)
    {o}
    (hrun : arena.monad.intern_e pers st v = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (Arena.internE (absENodeView v)) := by
  cases v with
  | BVar i => exact intern_e_bvar_run hrel hinv i hrun
  | FVar idx ty =>
    exact intern_e_fvar_run hrel hinv idx ty
      (fun h => hchild_fvar hrel.storeWF h) hview hrun
  | «Sort» u =>
    exact intern_e_sort_run hrel hinv u
      (fun h => hchild_sort hrel.storeWF h) hview hrun
  | Const n us =>
    exact intern_e_const_run hrel hinv n us
      (fun h => hchild_const hrel.storeWF h) hview hrun
  | App f a =>
    exact intern_e_app_run hrel hinv f a
      (fun h => hchild_app hrel.storeWF h) hview hrun
  | Lam ty b m =>
    exact intern_e_lam_run hrel hinv ty b m
      (hpw ty b m (Or.inl rfl)) hview hrun
  | ForallE ty b m =>
    exact intern_e_forall_e_run hrel hinv ty b m
      (hpw ty b m (Or.inr rfl)) hview hrun
  | LetE ty val b =>
    exact intern_e_let_e_run hrel hinv ty val b
      (fun h => hchild_let_e hrel.storeWF h) hview hrun
  | Lit l => exact intern_e_lit_run hrel hinv l (hlit l rfl) hrun
  | Proj n i e =>
    exact intern_e_proj_run hrel hinv n i e
      (fun h => hchild_proj hrel.storeWF h) hview hrun

/-! ## The name, level and level-list tiers' `intern` (task #97-P5-Specs
round 2)

The expression tier's eight `estore_intern_*_abs` are one 190-line proof per
constructor, because `EStore::intern_bvar` … `intern_proj` are eight separate
Rust functions.  **The three tiers below are not shaped that way**:
`NTables::find` / `full_of` / `push` (and the level and level-list twins) each
dispatch on the view inside ONE function, exactly where the twin's
`NTables.find?` / `sizeOf` / `push` do — so the per-constructor work collapses
into three tier lemmas with a `cases v` inside, and the store-level `intern`
proof has no case split at all.

The one place that does not collapse is `NNodeView::Str`: `NStore::intern`
routes it through `intern_str` rather than `intern_other`, to avoid rebuilding
the cons key (`NTables::find` would `str_copy` it again).  The twin makes no
such distinction, so the control flow is written out a second time there, at
the `Tbl` lemmas instead of the `NTables` ones. -/

theorem dupId_anonnode :
    DupId arena.store.AnonNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm

theorem dupId_strnode :
    DupId arena.store.StrNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.pre := dupId_nidx _ _ hx
  subst e1
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e2 : y = a.s := ConRon.Refine.Expr.str_copy_eq hy
  subst e2
  exact (Result.ok_injective h).symm

theorem dupId_numnode :
    DupId arena.store.NumNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.pre := dupId_nidx _ _ hx
  subst e1
  exact (Result.ok_injective h).symm

theorem absAnonNode_inj :
    ∀ a b : arena.store.AnonNode, AnonNodeWF a → AnonNodeWF b →
      absAnonNode a = absAnonNode b → a = b := by
  intro a b _ _ _; rfl

theorem absStrNode_inj :
    ∀ a b : arena.store.StrNode, StrNodeWF a → StrNodeWF b →
      absStrNode a = absStrNode b → a = b := by
  intro a b ha hb h
  obtain ⟨x, xs⟩ := a; obtain ⟨y, ys⟩ := b
  have h1 : absNIdx x = absNIdx y := congrArg StrNode.pre h
  have h2 : ConRon.Refine.absString xs = ConRon.Refine.absString ys :=
    congrArg StrNode.s h
  have h3 : xs = ys := ConRon.Refine.Name.absString_inj ha hb h2
  rw [absNIdx_inj h1, h3]

theorem absNumNode_inj :
    ∀ a b : arena.store.NumNode, NumNodeWF a → NumNodeWF b →
      absNumNode a = absNumNode b → a = b := by
  intro a b _ _ h
  obtain ⟨x, xn⟩ := a; obtain ⟨y, yn⟩ := b
  have h1 : absNIdx x = absNIdx y := congrArg NumNode.pre h
  have h2 : xn.val = yn.val := congrArg (fun r => (NumNode.n r : Nat)) h
  simp [absNIdx_inj h1, UScalar.eq_imp _ _ h2]

/-- The name tier's cons probe, at the whole view: the Rust's `NTables::find`
dispatches on the view exactly where the twin's `NTables.find?` does, so one
lemma covers the three constructor arrays. -/
theorem ntables_find_abs {rt lt} (hrel : NTablesRel rt lt) (hinv : NTablesInv rt)
    {v : arena.store.NNodeView} (hvwf : NNodeViewWF v) {o}
    (h : arena.store.NTables.find rt v = ok o) :
    lt.find? (absNNodeView v) = o.map absNIdx := by
  cases v with
  | Anonymous =>
    simp only [arena.store.NTables.find] at h
    exact tbl_find_abs hrel.anons hinv.anons anon_eq2 dupId_nidx
      (P := AnonNodeWF) trivial h
  | Str p s =>
    simp only [arena.store.NTables.find] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨s1, hs1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_nidx _ _ hn, ConRon.Refine.Expr.str_copy_eq hs1] at h
    have hk : StrNodeWF ⟨p, s⟩ := hvwf
    exact tbl_find_abs hrel.strs hinv.strs str_eq2 dupId_nidx
      (P := StrNodeWF) hk h
  | Num p n =>
    simp only [arena.store.NTables.find] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_nidx _ _ hn1] at h
    exact tbl_find_abs hrel.nums hinv.nums num_eq2 dupId_nidx
      (P := NumNodeWF) trivial h

/-- `NTables::full_of = false` is the twin's `sizeOf < Idx.idxCap`, at the
array the view would land in. -/
theorem ntables_full_abs {rt lt} (hrel : NTablesRel rt lt)
    {v : arena.store.NNodeView} {b : Bool}
    (h : arena.store.NTables.full_of rt v = ok b) (hb : ¬ (b = true)) :
    lt.sizeOf (absNNodeView v) < Idx.idxCap := by
  cases v with
  | Anonymous =>
    simp only [arena.store.NTables.full_of] at h
    exact tbl_not_full_size hrel.anons h hb
  | Str p s =>
    simp only [arena.store.NTables.full_of] at h
    exact tbl_not_full_size hrel.strs h hb
  | Num p n =>
    simp only [arena.store.NTables.full_of] at h
    exact tbl_not_full_size hrel.nums h hb

/-- `NTables::push`, at the whole view. -/
theorem ntables_push_abs {rt lt} (hrel : NTablesRel rt lt) (hinv : NTablesInv rt)
    {v : arena.store.NNodeView} (hvwf : NNodeViewWF v) {d : Std.U64} (dl : UInt64)
    {tier : Std.U32} {i : arena.handle.NIdx} {rt'}
    (h : arena.store.NTables.push rt v d tier = ok (i, rt')) :
    absNIdx i = (lt.push (absNNodeView v) dl (absU32 tier)).2 ∧
      NTablesRel rt' (lt.push (absNNodeView v) dl (absU32 tier)).1 ∧
      NTablesInv rt' := by
  cases v with
  | Anonymous =>
    simp only [arena.store.NTables.push] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_nidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    have hhandle : absNIdx hnew
        = Idx.mk NTag.anonymous (absU32 tier) (UInt32.ofNat lt.anons.size) := by
      rw [nidx_pack_abs hpk, ntag_anonymous_abs, cast_u32_size hn2,
        tbl_size_abs hrel.anons hn1]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.anons hinv.anons anon_eq2 dupId_anonnode absAnonNode_inj
        (P := AnonNodeWF) trivial (dl := dl) rfl ht1
    simp only [absAnonNode] at hrel1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with anons := hrel1 }, { hinv with anons := hinv1 }⟩
  | Str p s =>
    simp only [arena.store.NTables.push] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_nidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    have hhandle : absNIdx hnew
        = Idx.mk NTag.str (absU32 tier) (UInt32.ofNat lt.strs.size) := by
      rw [nidx_pack_abs hpk, ntag_str_abs, cast_u32_size hn2,
        tbl_size_abs hrel.strs hn1]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.strs hinv.strs str_eq2 dupId_strnode absStrNode_inj
        (P := StrNodeWF) (show StrNodeWF ⟨p, s⟩ from hvwf) (dl := dl) rfl ht1
    simp only [absStrNode] at hrel1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with strs := hrel1 }, { hinv with strs := hinv1 }⟩
  | Num p n =>
    simp only [arena.store.NTables.push] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_nidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    have hhandle : absNIdx hnew
        = Idx.mk NTag.num (absU32 tier) (UInt32.ofNat lt.nums.size) := by
      rw [nidx_pack_abs hpk, ntag_num_abs, cast_u32_size hn2,
        tbl_size_abs hrel.nums hn1]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.nums hinv.nums num_eq2 dupId_numnode absNumNode_inj
        (P := NumNodeWF) trivial (dl := dl) rfl ht1
    simp only [absNumNode] at hrel1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with nums := hrel1 }, { hinv with nums := hinv1 }⟩

/-! ## The name tier's `intern`: the capacity side condition, and the walk -/

/-- `ECapAt` at the name store: the miss-path capacity test `Arena.internNNode`
makes, so that it can be CONCLUDED by the port's own `Tbl::full` rather than
assumed (task #97-P5-3 round 3's finding 14, one tier down). -/
def NCapAt (st : NStore) (v : NNodeView) : Prop :=
  st.find? v = none →
    (if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap

theorem NCapAt.of_find_ne {st : NStore} {v : NNodeView} (h : st.find? v ≠ none) :
    NCapAt st v := fun hn => absurd hn h

theorem NCapAt.of_scr_size {st : NStore} {v : NNodeView} (hon : st.scratchOn = true)
    (h : st.scr.sizeOf v < Idx.idxCap) : NCapAt st v := by
  intro _; rw [if_pos hon]; exact h

theorem NCapAt.of_pers_size {st : NStore} {v : NNodeView} (hoff : st.scratchOn = false)
    (h : st.pers.sizeOf v < Idx.idxCap) : NCapAt st v := by
  intro _; rw [if_neg (by rw [hoff]; simp)]; exact h

/-- The name store's persistent probe, under the `shared_on` select. -/
theorem nstore_pers_find_abs {pers rs ls} (hrel : NStoreRel pers rs ls)
    (hinv : NStoreInv pers rs) {v : arena.store.NNodeView} (hvwf : NNodeViewWF v)
    {o} (h : arena.store.NStore.pers_find rs pers v = ok o) :
    ls.pers.find? (absNNodeView v) = o.map absNIdx := by
  rw [arena.store.NStore.pers_find] at h
  have hx := hrel.perst; have hy := hinv.perst
  unfold rPersN at hx hy
  split at h <;> rename_i hs
  · rw [if_pos hs] at hx hy; exact ntables_find_abs hx hy hvwf h
  · rw [if_neg hs] at hx hy; exact ntables_find_abs hx hy hvwf h

/-- `arena::store::NStore.intern_other` against `NStore.intern`.  The name
tier's `intern` is `EStore.intern`'s shape with no binder datum and — because
`NTables::find`, `full_of` and `push` each dispatch on the view in ONE
function where the expression tier has ten — **no case split at all**: the
three constructor arrays are `ntables_find_abs`, `ntables_full_abs` and
`ntables_push_abs` above, and this lemma is only the control flow. -/
theorem nstore_intern_other_abs {pers rs ls} (hrel : NStoreRel pers rs ls)
    (hinv : NStoreInv pers rs)
    {v : arena.store.NNodeView} (hvwf : NNodeViewWF v) {r} {rs'}
    (h : arena.store.NStore.intern_other rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absNIdx hh = (ls.intern (absNNodeView v)).2 ∧
        NStoreRel pers rs' (ls.intern (absNNodeView v)).1 ∧
        NStoreInv pers rs' ∧ NCapAt ls (absNNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.NStore.intern_other] at h
  obtain ⟨hit, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hE3 := nstore_pers_find_abs hrel hinv hvwf hq
  simp only [NStore.intern]
  cases hitc : hit with
  | some hp =>
    simp only [hitc] at h
    have hpp : ls.pers.find? (absNNodeView v) = some (absNIdx hp) := by
      rw [hE3, hitc]; rfl
    simp only [hpp]
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ?_⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      refine ⟨rfl, hrel, hinv, NCapAt.of_find_ne ?_⟩
      have hf : ls.find? (absNNodeView v) = some (absNIdx hp) := by
        simp only [NStore.find?, hpp]
      rw [hf]; simp
    · intro ee hbad; simp at hbad
    · exact ⟨rfl, rfl⟩
  | none =>
    simp only [hitc] at h
    have hpn : ls.pers.find? (absNNodeView v) = none := by rw [hE3, hitc]; rfl
    simp only [hpn, hrel.scratchOn]
    split at h <;> rename_i hsc
    · -- the scratch tier
      rw [if_pos hsc]
      obtain ⟨o, hfs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hE4 : ls.scr.find? (absNNodeView v) = o.map absNIdx :=
        ntables_find_abs hrel.scrt hinv.scrt hvwf hfs
      cases hoc : o with
      | some hs =>
        simp only [hoc] at h
        have hss : ls.scr.find? (absNNodeView v) = some (absNIdx hs) := by
          rw [hE4, hoc]; rfl
        simp only [hss]
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs'⟩ := he
        subst hr; subst hs'
        refine ⟨?_, ?_, ?_⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          refine ⟨rfl, hrel, hinv, NCapAt.of_find_ne ?_⟩
          have hf : ls.find? (absNNodeView v) = some (absNIdx hs) := by
            simp only [NStore.find?, hpn]
            rw [if_pos (hrel.scratchOn.trans hsc), hss]
          rw [hf]; simp
        · intro ee hbad; simp at hbad
        · exact ⟨rfl, rfl⟩
      | none =>
        simp only [hoc] at h
        have hsn : ls.scr.find? (absNNodeView v) = none := by rw [hE4, hoc]; rfl
        simp only [hsn]
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · -- the array is full: `Native`, which claims nothing
          obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs2⟩ := he
          subst hr; subst hs2
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
        · -- the append
          obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨pr, hpu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hnew, t1⟩ := pr
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs'⟩ := he
          subst hr; subst hs'
          obtain ⟨hhandle, hrel1, hinv1⟩ :=
            ntables_push_abs hrel.scrt hinv.scrt hvwf
              (ls.derOfView (absNNodeView v)) hpu
          rw [tier_s_abs] at hhandle hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.perst, hrel1, rfl⟩, ⟨hinv.perst, hinv1⟩,
            NCapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (ntables_full_abs hrel.scrt hb1 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      split at h <;> rename_i hsh2
      · -- the frozen tier: `Native`, which claims nothing
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          by simp [hsh2, hsc]⟩
      · have hsh : rs.shared_on = false := by simpa using hsh2
        have hpersN : rPersN pers rs = rs.pers := by unfold rPersN; rw [hsh]; rfl
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hrelP : NTablesRel rs.pers ls.pers := by rw [← hpersN]; exact hrel.perst
        have hinvP : NTablesInv rs.pers := by rw [← hpersN]; exact hinv.perst
        have hbf : arena.store.NTables.full_of rs.pers v = ok b1 := by
          rw [arena.store.NStore.pers_full_of] at hb1
          rw [if_neg hsh2] at hb1; exact hb1
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs2⟩ := he
          subst hr; subst hs2
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
        · obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨pr, hpu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hnew, t1⟩ := pr
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs'⟩ := he
          subst hr; subst hs'
          obtain ⟨hhandle, hrel1, hinv1⟩ :=
            ntables_push_abs hrelP hinvP hvwf (ls.derOfView (absNNodeView v)) hpu
          rw [tier_p_abs] at hhandle hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          refine ⟨hhandle, ⟨?_, hrel.scrt, rfl⟩, ⟨?_, hinv.scrt⟩,
            NCapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
              (ntables_full_abs hrelP hbf hfull)⟩
          · unfold rPersN; rw [hsh]; exact hrel1
          · unfold rPersN; rw [hsh]; exact hinv1

/-! ### The `str` constructor's own path

`NStore::intern` does not route `NNodeView::Str` through `intern_other`: it
computes the derived word from the prefix and the code points and calls
`intern_str`, which is `intern_other` specialised to the `strs` array — the
cons key is built once instead of being rebuilt by `NTables::find`'s own
`str_copy`.  So the `str` arm gets the control flow written out a second time,
at the `Tbl` lemmas rather than the `NTables` ones.  The twin does not
distinguish the two: `NStore.intern` is one function, and `NTables.find?` /
`push` at a `.str` view ARE the `strs` array's, definitionally. -/

/-- `NStore::pers_strs_find`, the `str` arm's persistent probe. -/
theorem nstore_pers_strs_find_abs {pers rs ls} (hrel : NStoreRel pers rs ls)
    (hinv : NStoreInv pers rs) {p : arena.handle.NIdx}
    {s : alloc.vec.Vec Std.U32} (hvwf : ConRon.Refine.StrWF s) {o}
    (h : arena.store.NStore.pers_strs_find rs pers ⟨p, s⟩ = ok o) :
    ls.pers.find? (.str (absNIdx p) (ConRon.Refine.absString s)) = o.map absNIdx := by
  rw [arena.store.NStore.pers_strs_find] at h
  have hx := hrel.perst; have hy := hinv.perst
  unfold rPersN at hx hy
  split at h <;> rename_i hs
  · rw [if_pos hs] at hx hy
    exact tbl_find_abs hx.strs hy.strs str_eq2 dupId_nidx
      (P := StrNodeWF) (show StrNodeWF ⟨p, s⟩ from hvwf) h
  · rw [if_neg hs] at hx hy
    exact tbl_find_abs hx.strs hy.strs str_eq2 dupId_nidx
      (P := StrNodeWF) (show StrNodeWF ⟨p, s⟩ from hvwf) h

/-- `arena::store::NStore.intern_str` against `NStore.intern` at a `.str`
view. -/
theorem nstore_intern_str_abs {pers rs ls} (hrel : NStoreRel pers rs ls)
    (hinv : NStoreInv pers rs)
    {p : arena.handle.NIdx} {s : alloc.vec.Vec Std.U32}
    (hvwf : ConRon.Refine.StrWF s) {d : Std.U64} {r} {rs'}
    (h : arena.store.NStore.intern_str rs pers ⟨p, s⟩ d = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absNIdx hh = (ls.intern (NNodeView.str (absNIdx p) (ConRon.Refine.absString s))).2 ∧
        NStoreRel pers rs' (ls.intern (NNodeView.str (absNIdx p) (ConRon.Refine.absString s))).1 ∧
        NStoreInv pers rs' ∧ NCapAt ls (NNodeView.str (absNIdx p) (ConRon.Refine.absString s))) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.NStore.intern_str] at h
  obtain ⟨hit, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hE3 := nstore_pers_strs_find_abs hrel hinv hvwf hq
  simp only [NStore.intern]
  cases hitc : hit with
  | some hp =>
    simp only [hitc] at h
    have hpp : ls.pers.find? (NNodeView.str (absNIdx p) (ConRon.Refine.absString s)) = some (absNIdx hp) := by
      rw [hE3, hitc]; rfl
    simp only [hpp]
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ?_⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      refine ⟨rfl, hrel, hinv, NCapAt.of_find_ne ?_⟩
      have hf : ls.find? (NNodeView.str (absNIdx p) (ConRon.Refine.absString s)) = some (absNIdx hp) := by
        simp only [NStore.find?, hpp]
      rw [hf]; simp
    · intro ee hbad; simp at hbad
    · exact ⟨rfl, rfl⟩
  | none =>
    simp only [hitc] at h
    have hpn : ls.pers.find? (NNodeView.str (absNIdx p) (ConRon.Refine.absString s)) = none := by rw [hE3, hitc]; rfl
    simp only [hpn, hrel.scratchOn]
    split at h <;> rename_i hsc
    · -- the scratch tier
      rw [if_pos hsc]
      obtain ⟨o, hfs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hE4 : ls.scr.find? (NNodeView.str (absNIdx p) (ConRon.Refine.absString s))
          = o.map absNIdx :=
        tbl_find_abs hrel.scrt.strs hinv.scrt.strs str_eq2 dupId_nidx
          (P := StrNodeWF) (show StrNodeWF ⟨p, s⟩ from hvwf) hfs
      cases hoc : o with
      | some hs =>
        simp only [hoc] at h
        have hss : ls.scr.find? (NNodeView.str (absNIdx p) (ConRon.Refine.absString s)) = some (absNIdx hs) := by
          rw [hE4, hoc]; rfl
        simp only [hss]
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs'⟩ := he
        subst hr; subst hs'
        refine ⟨?_, ?_, ?_⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          refine ⟨rfl, hrel, hinv, NCapAt.of_find_ne ?_⟩
          have hf : ls.find? (NNodeView.str (absNIdx p) (ConRon.Refine.absString s)) = some (absNIdx hs) := by
            simp only [NStore.find?, hpn]
            rw [if_pos (hrel.scratchOn.trans hsc), hss]
          rw [hf]; simp
        · intro ee hbad; simp at hbad
        · exact ⟨rfl, rfl⟩
      | none =>
        simp only [hoc] at h
        have hsn : ls.scr.find? (NNodeView.str (absNIdx p) (ConRon.Refine.absString s)) = none := by rw [hE4, hoc]; rfl
        simp only [hsn]
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · -- the array is full: `Native`, which claims nothing
          obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs2⟩ := he
          subst hr; subst hs2
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
        · -- the append
          obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          rw [dupId_nidx _ _ he1] at h
          obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs'⟩ := he
          subst hr; subst hs'
          have hhandle : absNIdx hnew
              = Idx.mk NTag.str Idx.tierS (UInt32.ofNat ls.scr.strs.size) := by
            rw [nidx_pack_abs hpk, ntag_str_abs, tier_s_abs, cast_u32_size hn2,
              tbl_size_abs hrel.scrt.strs hn1]
          obtain ⟨hrelT, hinvT⟩ :=
            tbl_push_abs hrel.scrt.strs hinv.scrt.strs str_eq2 dupId_strnode
              absStrNode_inj (P := StrNodeWF) (show StrNodeWF ⟨p, s⟩ from hvwf)
              (dl := ls.derOfView
                (NNodeView.str (absNIdx p) (ConRon.Refine.absString s))) rfl ht1
          simp only [absStrNode] at hrelT
          rw [hhandle] at hrelT
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.perst, { hrel.scrt with strs := hrelT }, rfl⟩,
            ⟨hinv.perst, { hinv.scrt with strs := hinvT }⟩,
            NCapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (tbl_not_full_size hrel.scrt.strs hb1 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      split at h <;> rename_i hsh2
      · -- the frozen tier: `Native`, which claims nothing
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          by simp [hsh2, hsc]⟩
      · have hsh : rs.shared_on = false := by simpa using hsh2
        have hpersN : rPersN pers rs = rs.pers := by unfold rPersN; rw [hsh]; rfl
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hrelP : NTablesRel rs.pers ls.pers := by rw [← hpersN]; exact hrel.perst
        have hinvP : NTablesInv rs.pers := by rw [← hpersN]; exact hinv.perst

        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs2⟩ := he
          subst hr; subst hs2
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
        · obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          rw [dupId_nidx _ _ he1] at h
          obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs'⟩ := he
          subst hr; subst hs'
          have hhandle : absNIdx hnew
              = Idx.mk NTag.str Idx.tierP (UInt32.ofNat ls.pers.strs.size) := by
            rw [nidx_pack_abs hpk, ntag_str_abs, tier_p_abs, cast_u32_size hn2,
              tbl_size_abs hrelP.strs hn1]
          obtain ⟨hrelT, hinvT⟩ :=
            tbl_push_abs hrelP.strs hinvP.strs str_eq2 dupId_strnode
              absStrNode_inj (P := StrNodeWF) (show StrNodeWF ⟨p, s⟩ from hvwf)
              (dl := ls.derOfView
                (NNodeView.str (absNIdx p) (ConRon.Refine.absString s))) rfl ht1
          simp only [absStrNode] at hrelT
          rw [hhandle] at hrelT
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          refine ⟨hhandle, ⟨?_, hrel.scrt, rfl⟩, ⟨?_, hinv.scrt⟩,
            NCapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
              (tbl_not_full_size hrelP.strs hb1 hfull)⟩
          · unfold rPersN; rw [hsh]; exact { hrelP with strs := hrelT }
          · unfold rPersN; rw [hsh]; exact { hinvP with strs := hinvT }

/-- `arena::store::NStore.intern` against `NStore.intern`: the ten-way
dispatcher's name-tier twin, two arms wide.  `Anonymous` and `Num` go through
`intern_other`; `Str` computes its derived word first and goes through
`intern_str`. -/
theorem nstore_intern_abs {pers rs ls} (hrel : NStoreRel pers rs ls)
    (hinv : NStoreInv pers rs)
    {v : arena.store.NNodeView} (hvwf : NNodeViewWF v) {r} {rs'}
    (h : arena.store.NStore.intern rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absNIdx hh = (ls.intern (absNNodeView v)).2 ∧
        NStoreRel pers rs' (ls.intern (absNNodeView v)).1 ∧
        NStoreInv pers rs' ∧ NCapAt ls (absNNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  cases v with
  | Anonymous =>
    simp only [arena.store.NStore.intern] at h
    exact nstore_intern_other_abs hrel hinv hvwf h
  | Str p s =>
    simp only [arena.store.NStore.intern] at h
    obtain ⟨i, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨d, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact nstore_intern_str_abs hrel hinv hvwf h
  | Num p n =>
    simp only [arena.store.NStore.intern] at h
    exact nstore_intern_other_abs hrel hinv hvwf h

/-! ### The persistent tier's own `intern`

`NStore::intern_persistent` is `intern_other`'s `else` branch: probe the
persistent cons table, test the persistent array, append there whatever tier
the store is in (DESIGN §8.3's promotion).  It needed `shared_on = false`
until the frozen-tier guard became `Native` (task #97-P5-Usize §3); now the
frozen arm claims nothing, like a full array, and the hypothesis is gone
(task #97-P5-Unfreeze).  The persistent probe reads `rPersN` either way. -/

/-- `NCapAt` at the persistent tier. -/
def NCapPAt (st : NStore) (v : NNodeView) : Prop :=
  st.pers.find? v = none → st.pers.sizeOf v < Idx.idxCap

theorem NCapPAt.of_find_ne {st : NStore} {v : NNodeView}
    (h : st.pers.find? v ≠ none) : NCapPAt st v := fun hn => absurd hn h

theorem nstore_intern_persistent_abs {pers rs ls} (hrel : NStoreRel pers rs ls)
    (hinv : NStoreInv pers rs)
    {v : arena.store.NNodeView} (hvwf : NNodeViewWF v) {r} {rs'}
    (h : arena.store.NStore.intern_persistent rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absNIdx hh = (ls.internPersistent (absNNodeView v)).2 ∧
        NStoreRel pers rs' (ls.internPersistent (absNNodeView v)).1 ∧
        NStoreInv pers rs' ∧ NCapPAt ls (absNNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.NStore.intern_persistent] at h
  obtain ⟨hit, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hE3 := nstore_pers_find_abs hrel hinv hvwf hq
  simp only [NStore.internPersistent]
  cases hitc : hit with
  | some hp =>
    simp only [hitc] at h
    have hpp : ls.pers.find? (absNNodeView v) = some (absNIdx hp) := by
      rw [hE3, hitc]; rfl
    simp only [hpp]
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ?_⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv, NCapPAt.of_find_ne (by rw [hpp]; simp)⟩
    · intro ee hbad; simp at hbad
    · exact ⟨rfl, rfl⟩
  | none =>
    simp only [hitc] at h
    have hpn : ls.pers.find? (absNNodeView v) = none := by rw [hE3, hitc]; rfl
    simp only [hpn]
    split at h <;> rename_i hsh2
    · -- the frozen tier: `Native`, which claims nothing
      obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
      exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
    · have hshared : rs.shared_on = false := by simpa using hsh2
      have hpersN : rPersN pers rs = rs.pers := by unfold rPersN; rw [hshared]; rfl
      have hrelP : NTablesRel rs.pers ls.pers := by rw [← hpersN]; exact hrel.perst
      have hinvP : NTablesInv rs.pers := by rw [← hpersN]; exact hinv.perst
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hbf : arena.store.NTables.full_of rs.pers v = ok b1 := by
        rw [arena.store.NStore.pers_full_of] at hb1
        rw [if_neg hsh2] at hb1; exact hb1
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs2⟩ := he
        subst hr; subst hs2
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
      · obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨pr, hpu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hnew, t1⟩ := pr
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs'⟩ := he
        subst hr; subst hs'
        obtain ⟨hhandle, hrel1, hinv1⟩ :=
          ntables_push_abs hrelP hinvP hvwf (ls.derOfView (absNNodeView v)) hpu
        rw [tier_p_abs] at hhandle hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨?_, hrel.scrt, hrel.scratchOn⟩, ⟨?_, hinv.scrt⟩,
          fun _ => ntables_full_abs hrelP hbf hfull⟩
        · unfold rPersN; rw [hshared]; exact hrel1
        · unfold rPersN; rw [hshared]; exact hinv1

/-! ### Through the nesting, and the monad wrapper

`EStore::intern_name` is three one-line wrappers over `NStore::intern`, and
the twin's `EStore.internName` is the same three; nothing but the record
update happens at each level. -/

theorem estore_intern_name_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {v : arena.store.NNodeView} (hvwf : NNodeViewWF v) {r} {rs'}
    (h : arena.store.EStore.intern_name rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absNIdx hh = (ls.internName (absNNodeView v)).2 ∧
        StoreRel pers rs' (ls.internName (absNNodeView v)).1 ∧
        StoreInv pers rs' ∧ NCapAt ls.ns (absNNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.EStore.intern_name] at h
  obtain ⟨p1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r1, lss1⟩ := p1
  rw [arena.store.LsStore.intern_name] at h1
  obtain ⟨p2, h2, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
  obtain ⟨r2, l2⟩ := p2
  rw [arena.store.LStore.intern_name] at h2
  obtain ⟨p3, h3, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
  obtain ⟨r3, n3⟩ := p3
  have e2 := Result.ok_injective h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨e2a, e2b⟩ := e2
  subst e2a; subst e2b
  have e1 := Result.ok_injective h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨e1a, e1b⟩ := e1
  subst e1a; subst e1b
  have e0 := Result.ok_injective h
  simp only [Prod.mk.injEq] at e0
  obtain ⟨e0a, e0b⟩ := e0
  subst e0a; subst e0b
  obtain ⟨hok, herr, -⟩ :=
    nstore_intern_abs (ls := ls.ns) hrel.lss.lvl.ns hinv.lss.lvl.ns hvwf h3
  refine ⟨?_, herr, rfl, rfl⟩
  intro hh hoc
  obtain ⟨hhd, hrel1, hinv1, hcap⟩ := hok hh hoc
  exact ⟨hhd,
    ⟨⟨⟨hrel1, hrel.lss.lvl.perst, hrel.lss.lvl.scrt, hrel.lss.lvl.scratchOn⟩,
      hrel.lss.perst, hrel.lss.scrt, hrel.lss.scratchOn⟩,
     hrel.perst, hrel.scrt, hrel.scratchOn⟩,
    ⟨⟨⟨hinv1, hinv.lss.lvl.perst, hinv.lss.lvl.scrt⟩, hinv.lss.perst, hinv.lss.scrt⟩,
      hinv.perst, hinv.scrt⟩,
    hcap⟩

/-- The twin's name intern at a cons HIT does not move the store. -/
theorem NStore_intern_of_find {st : NStore} {v : NNodeView} {h : NIdx}
    (hf : st.find? v = some h) : st.intern v = (st, h) := by
  simp only [NStore.find?] at hf
  simp only [NStore.intern]
  split at hf
  · simp only [Option.some.injEq] at hf; rw [hf]
  · split at hf
    · rename_i hon
      rw [if_pos hon]
      cases hs : st.scr.find? v with
      | some i =>
        simp only [hs, Option.some.injEq] at hf
        rw [hf]
      | none => simp only [hs] at hf; simp at hf
    · simp at hf

theorem EStore_internName_of_find {st : EStore} {v : NNodeView} {h : NIdx}
    (hf : st.ns.find? v = some h) : st.internName v = (st, h) := by
  have h1 : st.lss.ls.ns.intern v = (st.lss.ls.ns, h) := NStore_intern_of_find hf
  simp only [EStore.internName, LsStore.internName, LStore.internName, h1]

/-- Finding 16's clause at the name intern: `intern_wf` on the miss, and on
the hit the store does not move at all. -/
theorem internName_storeWF {st : EStore} {v : NNodeView} (hwf : StoreWF st)
    (hview : st.ns.ViewOK v) (hcap : NCapAt st.ns v) :
    StoreWF (st.internName v).1 := by
  cases hf : st.ns.find? v with
  | some h => rw [EStore_internName_of_find hf]; exact hwf
  | none => exact EStore.internName_wf hwf hview (hcap hf)

/-- `Arena.internNNode`'s run: probe first, then the one capacity test. -/
theorem internNNode_run_of_cap {lst : AState} {v : NNodeView}
    (hcap : NCapAt lst.store.ns v) :
    (Arena.internNNode v).run lst
      = .ok ((lst.store.internName v).2,
             { lst with store := (lst.store.internName v).1 }) := by
  simp only [Arena.internNNode, run_get_bind]
  cases hf : lst.store.ns.find? v with
  | some h => rw [EStore_internName_of_find hf]; rfl
  | none =>
    rw [if_pos (hcap hf)]
    cases hi : lst.store.internName v with
    | mk st1 h1 => rfl

/-- `arena::monad::intern_n_node` against `Arena.internNNode`. -/
theorem intern_n_node_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (v : arena.store.NNodeView) (hvwf : NNodeViewWF v)
    (hrun : arena.monad.intern_n_node pers st v = ok o) :
    Sim₀ absNIdx pers lst o (Arena.internNNode (absNNodeView v)) := by
  rw [arena.monad.intern_n_node] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_name_abs (ls := lst.store) hrel.store hinv.store hvwf hp
  show AOut₀ absNIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.internName (absNNodeView v)).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [internNNode_run_of_cap hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-! ## The level tier's three writing operations

The shape of §the name tier, five constructor arrays wide.  The one thing
that is NOT the name tier's: the derived record is OBSERVED (`derObsL` is the
has-a-parameter bit), so `Tbl::push` carries a real obligation here, and
`lstore_der_of_view_abs` below is what discharges it. -/

theorem dupId_zeronode :
    DupId arena.store.ZeroNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm

theorem dupId_succnode :
    DupId arena.store.SuccNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.u := dupId_lidx _ _ hx
  subst e1
  exact (Result.ok_injective h).symm

theorem dupId_binlnode :
    DupId arena.store.BinLNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.u := dupId_lidx _ _ hx
  subst e1
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e2 : y = a.v := dupId_lidx _ _ hy
  subst e2
  exact (Result.ok_injective h).symm

theorem dupId_paramnode :
    DupId arena.store.ParamNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.n := dupId_nidx _ _ hx
  subst e1
  exact (Result.ok_injective h).symm

theorem absZeroNode_inj :
    ∀ a b : arena.store.ZeroNode, ZeroNodeWF a → ZeroNodeWF b →
      absZeroNode a = absZeroNode b → a = b := by
  intro a b _ _ _; rfl

theorem absSuccNode_inj :
    ∀ a b : arena.store.SuccNode, SuccNodeWF a → SuccNodeWF b →
      absSuccNode a = absSuccNode b → a = b := by
  intro a b _ _ h
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b
  have h1 : absLIdx x = absLIdx y := congrArg SuccNode.u h
  simp [absLIdx_inj h1]

theorem absBinLNode_inj :
    ∀ a b : arena.store.BinLNode, BinLNodeWF a → BinLNodeWF b →
      absBinLNode a = absBinLNode b → a = b := by
  intro a b _ _ h
  obtain ⟨x, xv⟩ := a; obtain ⟨y, yv⟩ := b
  have h1 : absLIdx x = absLIdx y := congrArg BinLNode.u h
  have h2 : absLIdx xv = absLIdx yv := congrArg BinLNode.v h
  simp [absLIdx_inj h1, absLIdx_inj h2]

theorem absParamNode_inj :
    ∀ a b : arena.store.ParamNode, ParamNodeWF a → ParamNodeWF b →
      absParamNode a = absParamNode b → a = b := by
  intro a b _ _ h
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b
  have h1 : absNIdx x = absNIdx y := congrArg ParamNode.n h
  simp [absNIdx_inj h1]

/-- The level tier's cons probe, at the whole view. -/
theorem ltables_find_abs {rt lt} (hrel : LTablesRel rt lt) (hinv : LTablesInv rt)
    {v : arena.store.LNodeView} {o}
    (h : arena.store.LTables.find rt v = ok o) :
    lt.find? (absLNodeView v) = o.map absLIdx := by
  cases v with
  | Zero =>
    simp only [arena.store.LTables.find] at h
    exact tbl_find_abs hrel.zeros hinv.zeros zero_eq2 dupId_lidx
      (P := ZeroNodeWF) trivial h
  | Succ u =>
    simp only [arena.store.LTables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ hx] at h
    exact tbl_find_abs hrel.succs hinv.succs succ_eq2 dupId_lidx
      (P := SuccNodeWF) trivial h
  | Max u w =>
    simp only [arena.store.LTables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ hx] at h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ hy] at h
    exact tbl_find_abs hrel.maxs hinv.maxs binl_eq2 dupId_lidx
      (P := BinLNodeWF) trivial h
  | Imax u w =>
    simp only [arena.store.LTables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ hx] at h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ hy] at h
    exact tbl_find_abs hrel.imaxs hinv.imaxs binl_eq2 dupId_lidx
      (P := BinLNodeWF) trivial h
  | Param n =>
    simp only [arena.store.LTables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_nidx _ _ hx] at h
    exact tbl_find_abs hrel.params hinv.params param_eq2 dupId_lidx
      (P := ParamNodeWF) trivial h

/-- `LTables::full_of = false` is the twin's `sizeOf < Idx.idxCap`. -/
theorem ltables_full_abs {rt lt} (hrel : LTablesRel rt lt)
    {v : arena.store.LNodeView} {b : Bool}
    (h : arena.store.LTables.full_of rt v = ok b) (hb : ¬ (b = true)) :
    lt.sizeOf (absLNodeView v) < Idx.idxCap := by
  cases v with
  | Zero =>
    simp only [arena.store.LTables.full_of] at h
    exact tbl_not_full_size hrel.zeros h hb
  | Succ u =>
    simp only [arena.store.LTables.full_of] at h
    exact tbl_not_full_size hrel.succs h hb
  | Max u w =>
    simp only [arena.store.LTables.full_of] at h
    exact tbl_not_full_size hrel.maxs h hb
  | Imax u w =>
    simp only [arena.store.LTables.full_of] at h
    exact tbl_not_full_size hrel.imaxs h hb
  | Param n =>
    simp only [arena.store.LTables.full_of] at h
    exact tbl_not_full_size hrel.params h hb

/-- `LTables::push`, at the whole view. -/
theorem ltables_push_abs {rt lt} (hrel : LTablesRel rt lt) (hinv : LTablesInv rt)
    {v : arena.store.LNodeView} {d : arena.store.LDer} {dl : LDer}
    (hdl : derObsL dl = derObsL (absLDer d))
    {tier : Std.U32} {i : arena.handle.LIdx} {rt'}
    (h : arena.store.LTables.push rt v d tier = ok (i, rt')) :
    absLIdx i = (lt.push (absLNodeView v) dl (absU32 tier)).2 ∧
      LTablesRel rt' (lt.push (absLNodeView v) dl (absU32 tier)).1 ∧
      LTablesInv rt' := by
  cases v with
  | Zero =>
    simp only [arena.store.LTables.push] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    have hhandle : absLIdx hnew
        = Idx.mk LTag.zero (absU32 tier) (UInt32.ofNat lt.zeros.size) := by
      rw [lidx_pack_abs hpk, ltag_zero_abs, cast_u32_size hn2,
        tbl_size_abs hrel.zeros hn1]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.zeros hinv.zeros zero_eq2 dupId_zeronode absZeroNode_inj
        (P := ZeroNodeWF) trivial (dl := dl) hdl ht1
    simp only [absZeroNode] at hrel1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with zeros := hrel1 }, { hinv with zeros := hinv1 }⟩
  | Succ u =>
    simp only [arena.store.LTables.push] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    have hhandle : absLIdx hnew
        = Idx.mk LTag.succ (absU32 tier) (UInt32.ofNat lt.succs.size) := by
      rw [lidx_pack_abs hpk, ltag_succ_abs, cast_u32_size hn2,
        tbl_size_abs hrel.succs hn1]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.succs hinv.succs succ_eq2 dupId_succnode absSuccNode_inj
        (P := SuccNodeWF) trivial (dl := dl) hdl ht1
    simp only [absSuccNode] at hrel1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with succs := hrel1 }, { hinv with succs := hinv1 }⟩
  | Max u w =>
    simp only [arena.store.LTables.push] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    have hhandle : absLIdx hnew
        = Idx.mk LTag.max (absU32 tier) (UInt32.ofNat lt.maxs.size) := by
      rw [lidx_pack_abs hpk, ltag_max_abs, cast_u32_size hn2,
        tbl_size_abs hrel.maxs hn1]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.maxs hinv.maxs binl_eq2 dupId_binlnode absBinLNode_inj
        (P := BinLNodeWF) trivial (dl := dl) hdl ht1
    simp only [absBinLNode] at hrel1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with maxs := hrel1 }, { hinv with maxs := hinv1 }⟩
  | Imax u w =>
    simp only [arena.store.LTables.push] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    have hhandle : absLIdx hnew
        = Idx.mk LTag.imax (absU32 tier) (UInt32.ofNat lt.imaxs.size) := by
      rw [lidx_pack_abs hpk, ltag_imax_abs, cast_u32_size hn2,
        tbl_size_abs hrel.imaxs hn1]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.imaxs hinv.imaxs binl_eq2 dupId_binlnode absBinLNode_inj
        (P := BinLNodeWF) trivial (dl := dl) hdl ht1
    simp only [absBinLNode] at hrel1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with imaxs := hrel1 }, { hinv with imaxs := hinv1 }⟩
  | Param n =>
    simp only [arena.store.LTables.push] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    have hhandle : absLIdx hnew
        = Idx.mk LTag.param (absU32 tier) (UInt32.ofNat lt.params.size) := by
      rw [lidx_pack_abs hpk, ltag_param_abs, cast_u32_size hn2,
        tbl_size_abs hrel.params hn1]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.params hinv.params param_eq2 dupId_paramnode absParamNode_inj
        (P := ParamNodeWF) trivial (dl := dl) hdl ht1
    simp only [absParamNode] at hrel1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with params := hrel1 }, { hinv with params := hinv1 }⟩
/-! ## The level tier's `intern` -/

/-- `ECapAt` at the level store: the miss-path capacity test `Arena.internLNode`
makes, so that it can be CONCLUDED by the port's own `Tbl::full` rather than
assumed (task #97-P5-3 round 3's finding 14, one tier down). -/
def LCapAt (st : LStore) (v : LNodeView) : Prop :=
  st.find? v = none →
    (if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap

theorem LCapAt.of_find_ne {st : LStore} {v : LNodeView} (h : st.find? v ≠ none) :
    LCapAt st v := fun hn => absurd hn h

theorem LCapAt.of_scr_size {st : LStore} {v : LNodeView} (hon : st.scratchOn = true)
    (h : st.scr.sizeOf v < Idx.idxCap) : LCapAt st v := by
  intro _; rw [if_pos hon]; exact h

theorem LCapAt.of_pers_size {st : LStore} {v : LNodeView} (hoff : st.scratchOn = false)
    (h : st.pers.sizeOf v < Idx.idxCap) : LCapAt st v := by
  intro _; rw [if_neg (by rw [hoff]; simp)]; exact h

/-- The level store's persistent probe, under the `shared_on` select. -/
theorem lstore_pers_find_abs {pers rs ls} (hrel : LStoreRel pers rs ls)
    (hinv : LStoreInv pers rs) {v : arena.store.LNodeView}
    {o} (h : arena.store.LStore.pers_find rs pers v = ok o) :
    ls.pers.find? (absLNodeView v) = o.map absLIdx := by
  rw [arena.store.LStore.pers_find] at h
  have hx := hrel.perst; have hy := hinv.perst
  unfold rPersL at hx hy
  split at h <;> rename_i hs
  · rw [if_pos hs] at hx hy; exact ltables_find_abs hx hy h
  · rw [if_neg hs] at hx hy; exact ltables_find_abs hx hy h


/-- `LStore::der_of_view` against `LStore.derOfView`, up to the hash: the
has-a-parameter bit is the only OBSERVED field (`derObsL`), and the port's
two-branch `if du.has_param` at `max`/`imax` is the twin's `||`. -/
theorem lstore_der_of_view_abs {pers rs ls} (hrel : LStoreRel pers rs ls)
    {v : arena.store.LNodeView} {d : arena.store.LDer}
    (h : arena.store.LStore.der_of_view rs pers v = ok d) :
    derObsL (ls.derOfView (absLNodeView v)) = derObsL (absLDer d) := by
  cases v with
  | Zero =>
    simp only [arena.store.LStore.der_of_view] at h
    rw [← Result.ok_injective h]; rfl
  | Succ u =>
    simp only [arena.store.LStore.der_of_view] at h
    obtain ⟨du, hdu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hu := lstore_derived_abs hrel hdu
    rw [← Result.ok_injective h]
    exact hu
  | Max u w =>
    simp only [arena.store.LStore.der_of_view] at h
    obtain ⟨du, hdu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨dw, hdw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hu := lstore_derived_abs hrel hdu
    have hw := lstore_derived_abs hrel hdw
    split at h <;> rename_i hp
    · rw [← Result.ok_injective h]
      show ((ls.derived (absLIdx u)).hasParam || (ls.derived (absLIdx w)).hasParam) = true
      rw [show (ls.derived (absLIdx u)).hasParam = true from hu.trans hp]
      rfl
    · rw [← Result.ok_injective h]
      show ((ls.derived (absLIdx u)).hasParam || (ls.derived (absLIdx w)).hasParam)
        = dw.has_param
      rw [show (ls.derived (absLIdx u)).hasParam = false from
        hu.trans (by simp only [derObsL, absLDer]; simpa using hp)]
      exact hw
  | Imax u w =>
    simp only [arena.store.LStore.der_of_view] at h
    obtain ⟨du, hdu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨dw, hdw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hu := lstore_derived_abs hrel hdu
    have hw := lstore_derived_abs hrel hdw
    split at h <;> rename_i hp
    · rw [← Result.ok_injective h]
      show ((ls.derived (absLIdx u)).hasParam || (ls.derived (absLIdx w)).hasParam) = true
      rw [show (ls.derived (absLIdx u)).hasParam = true from hu.trans hp]
      rfl
    · rw [← Result.ok_injective h]
      show ((ls.derived (absLIdx u)).hasParam || (ls.derived (absLIdx w)).hasParam)
        = dw.has_param
      rw [show (ls.derived (absLIdx u)).hasParam = false from
        hu.trans (by simp only [derObsL, absLDer]; simpa using hp)]
      exact hw
  | Param n =>
    simp only [arena.store.LStore.der_of_view] at h
    obtain ⟨i, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]; rfl

/-- `arena::store::LStore.intern` against `LStore.intern`.  The level tier
has no `intern_str`-style special case, so ONE lemma covers all five
constructors — and, like the name tier, with no case split: `ltables_find_abs`,
`ltables_full_abs` and `ltables_push_abs` do the dispatch. -/
theorem lstore_intern_abs {pers rs ls} (hrel : LStoreRel pers rs ls)
    (hinv : LStoreInv pers rs)
    {v : arena.store.LNodeView} {r} {rs'}
    (h : arena.store.LStore.intern rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absLIdx hh = (ls.intern (absLNodeView v)).2 ∧
        LStoreRel pers rs' (ls.intern (absLNodeView v)).1 ∧
        LStoreInv pers rs' ∧ LCapAt ls (absLNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.LStore.intern] at h
  obtain ⟨hit, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hE3 := lstore_pers_find_abs hrel hinv hq
  simp only [LStore.intern]
  cases hitc : hit with
  | some hp =>
    simp only [hitc] at h
    have hpp : ls.pers.find? (absLNodeView v) = some (absLIdx hp) := by
      rw [hE3, hitc]; rfl
    simp only [hpp]
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ?_⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      refine ⟨rfl, hrel, hinv, LCapAt.of_find_ne ?_⟩
      have hf : ls.find? (absLNodeView v) = some (absLIdx hp) := by
        simp only [LStore.find?, hpp]
      rw [hf]; simp
    · intro ee hbad; simp at hbad
    · exact ⟨rfl, rfl⟩
  | none =>
    simp only [hitc] at h
    have hpn : ls.pers.find? (absLNodeView v) = none := by rw [hE3, hitc]; rfl
    simp only [hpn, hrel.scratchOn]
    split at h <;> rename_i hsc
    · -- the scratch tier
      rw [if_pos hsc]
      obtain ⟨o, hfs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hE4 : ls.scr.find? (absLNodeView v) = o.map absLIdx :=
        ltables_find_abs hrel.scrt hinv.scrt hfs
      cases hoc : o with
      | some hs =>
        simp only [hoc] at h
        have hss : ls.scr.find? (absLNodeView v) = some (absLIdx hs) := by
          rw [hE4, hoc]; rfl
        simp only [hss]
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs'⟩ := he
        subst hr; subst hs'
        refine ⟨?_, ?_, ?_⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          refine ⟨rfl, hrel, hinv, LCapAt.of_find_ne ?_⟩
          have hf : ls.find? (absLNodeView v) = some (absLIdx hs) := by
            simp only [LStore.find?, hpn]
            rw [if_pos (hrel.scratchOn.trans hsc), hss]
          rw [hf]; simp
        · intro ee hbad; simp at hbad
        · exact ⟨rfl, rfl⟩
      | none =>
        simp only [hoc] at h
        have hsn : ls.scr.find? (absLNodeView v) = none := by rw [hE4, hoc]; rfl
        simp only [hsn]
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · -- the array is full: `Native`, which claims nothing
          obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs2⟩ := he
          subst hr; subst hs2
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
        · -- the append
          obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨pr, hpu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hnew, t1⟩ := pr
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs'⟩ := he
          subst hr; subst hs'
          obtain ⟨hhandle, hrel1, hinv1⟩ :=
            ltables_push_abs hrel.scrt hinv.scrt
              (dl := ls.derOfView (absLNodeView v))
              (lstore_der_of_view_abs hrel hd) hpu
          rw [tier_s_abs] at hhandle hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.ns, hrel.perst, hrel1, rfl⟩,
            ⟨hinv.ns, hinv.perst, hinv1⟩,
            LCapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (ltables_full_abs hrel.scrt hb1 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      split at h <;> rename_i hsh2
      · -- the frozen tier: `Native`, which claims nothing
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          by simp [hsh2, hsc]⟩
      · have hsh : rs.shared_on = false := by simpa using hsh2
        have hpersL : rPersL pers rs = rs.pers := by unfold rPersL; rw [hsh]; rfl
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hrelP : LTablesRel rs.pers ls.pers := by rw [← hpersL]; exact hrel.perst
        have hinvP : LTablesInv rs.pers := by rw [← hpersL]; exact hinv.perst
        have hbf : arena.store.LTables.full_of rs.pers v = ok b1 := by
          rw [arena.store.LStore.pers_full_of] at hb1
          rw [if_neg hsh2] at hb1; exact hb1
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs2⟩ := he
          subst hr; subst hs2
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
        · obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨pr, hpu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hnew, t1⟩ := pr
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs'⟩ := he
          subst hr; subst hs'
          obtain ⟨hhandle, hrel1, hinv1⟩ :=
            ltables_push_abs hrelP hinvP (dl := ls.derOfView (absLNodeView v))
              (lstore_der_of_view_abs hrel hd) hpu
          rw [tier_p_abs] at hhandle hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          refine ⟨hhandle, ⟨hrel.ns, ?_, hrel.scrt, rfl⟩, ⟨hinv.ns, ?_, hinv.scrt⟩,
            LCapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
              (ltables_full_abs hrelP hbf hfull)⟩
          · unfold rPersL; rw [hsh]; exact hrel1
          · unfold rPersL; rw [hsh]; exact hinv1

/-! ### Through the nesting, and the monad wrapper -/

theorem estore_intern_level_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {v : arena.store.LNodeView} {r} {rs'}
    (h : arena.store.EStore.intern_level rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absLIdx hh = (ls.internLevel (absLNodeView v)).2 ∧
        StoreRel pers rs' (ls.internLevel (absLNodeView v)).1 ∧
        StoreInv pers rs' ∧ LCapAt ls.ls (absLNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.EStore.intern_level] at h
  obtain ⟨p1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r1, lss1⟩ := p1
  rw [arena.store.LsStore.intern_level] at h1
  obtain ⟨p2, h2, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
  obtain ⟨r2, l2⟩ := p2
  have e1 := Result.ok_injective h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨e1a, e1b⟩ := e1
  subst e1a; subst e1b
  have e0 := Result.ok_injective h
  simp only [Prod.mk.injEq] at e0
  obtain ⟨e0a, e0b⟩ := e0
  subst e0a; subst e0b
  obtain ⟨hok, herr, -⟩ :=
    lstore_intern_abs (ls := ls.ls) hrel.lss.lvl hinv.lss.lvl h2
  refine ⟨?_, herr, rfl, rfl⟩
  intro hh hoc
  obtain ⟨hhd, hrel1, hinv1, hcap⟩ := hok hh hoc
  exact ⟨hhd,
    ⟨⟨hrel1, hrel.lss.perst, hrel.lss.scrt, hrel.lss.scratchOn⟩,
     hrel.perst, hrel.scrt, hrel.scratchOn⟩,
    ⟨⟨hinv1, hinv.lss.perst, hinv.lss.scrt⟩, hinv.perst, hinv.scrt⟩,
    hcap⟩

theorem LStore_intern_of_find {st : LStore} {v : LNodeView} {h : LIdx}
    (hf : st.find? v = some h) : st.intern v = (st, h) := by
  simp only [LStore.find?] at hf
  simp only [LStore.intern]
  split at hf
  · simp only [Option.some.injEq] at hf; rw [hf]
  · split at hf
    · rename_i hon
      rw [if_pos hon]
      cases hs : st.scr.find? v with
      | some i =>
        simp only [hs, Option.some.injEq] at hf
        rw [hf]
      | none => simp only [hs] at hf; simp at hf
    · simp at hf

theorem EStore_internLevel_of_find {st : EStore} {v : LNodeView} {h : LIdx}
    (hf : st.ls.find? v = some h) : st.internLevel v = (st, h) := by
  have h1 : st.lss.ls.intern v = (st.lss.ls, h) := LStore_intern_of_find hf
  simp only [EStore.internLevel, LsStore.internLevel, h1]

theorem internLevel_storeWF {st : EStore} {v : LNodeView} (hwf : StoreWF st)
    (hview : st.ls.ViewOK v) (hcap : LCapAt st.ls v) :
    StoreWF (st.internLevel v).1 := by
  cases hf : st.ls.find? v with
  | some h => rw [EStore_internLevel_of_find hf]; exact hwf
  | none => exact EStore.internLevel_wf hwf hview (hcap hf)

theorem internLNode_run_of_cap {lst : AState} {v : LNodeView}
    (hcap : LCapAt lst.store.ls v) :
    (Arena.internLNode v).run lst
      = .ok ((lst.store.internLevel v).2,
             { lst with store := (lst.store.internLevel v).1 }) := by
  simp only [Arena.internLNode, run_get_bind]
  cases hf : lst.store.ls.find? v with
  | some h => rw [EStore_internLevel_of_find hf]; rfl
  | none =>
    rw [if_pos (hcap hf)]
    cases hi : lst.store.internLevel v with
    | mk st1 h1 => rfl

/-- `arena::monad::intern_l_node` against `Arena.internLNode`. -/
theorem intern_l_node_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (v : arena.store.LNodeView)
    (hrun : arena.monad.intern_l_node pers st v = ok o) :
    Sim₀ absLIdx pers lst o (Arena.internLNode (absLNodeView v)) := by
  rw [arena.monad.intern_l_node] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_level_abs (ls := lst.store) hrel.store hinv.store hp
  show AOut₀ absLIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.internLevel (absLNodeView v)).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [internLNode_run_of_cap hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-! ## The level-list tier

One constructor array, so `LsTables::find` / `full_of` / `push` have no
dispatch at all; what is new here is that the node record holds a `Vec` —
`lidx_vec_dup` is its `dup2` and `lidx_vec_dup_eq` says it is the identity —
and that the derived record is computed by a LOOP over the list, so
`lsstore_der_of_view_abs` is a fuel induction rather than a case split. -/

theorem dupId_listnode :
    DupId arena.store.ListNode.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 : x = a.us := alloc.vec.Vec.ext _ _ (lidx_vec_dup_eq hx)
  subst e1
  exact (Result.ok_injective h).symm

theorem absListNode_inj :
    ∀ a b : arena.store.ListNode, ListNodeWF a → ListNodeWF b →
      absListNode a = absListNode b → a = b := by
  intro a b _ _ h
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b
  have h1 : x.val.map absLIdx = y.val.map absLIdx := congrArg ListNode.us h
  have h2 : x.val = y.val := by
    have hinj : Function.Injective absLIdx := fun _ _ hh => absLIdx_inj hh
    exact List.map_injective_iff.mpr hinj h1
  simp [alloc.vec.Vec.ext _ _ h2]

theorem lstables_find_abs {rt lt} (hrel : LsTablesRel rt lt) (hinv : LsTablesInv rt)
    {v : alloc.vec.Vec arena.handle.LIdx} {o}
    (h : arena.store.LsTables.find rt v = ok o) :
    lt.find? (absLsNodeView v) = o.map absLsIdx := by
  rw [arena.store.LsTables.find] at h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [alloc.vec.Vec.ext _ _ (lidx_vec_dup_eq hv1)] at h
  exact tbl_find_abs hrel.lists hinv.lists list_eq2 dupId_lsidx
    (P := ListNodeWF) trivial h

theorem lstables_full_abs' {rt lt} (hrel : LsTablesRel rt lt)
    {v : alloc.vec.Vec arena.handle.LIdx} {b : Bool}
    (h : arena.store.LsTables.full_of rt v = ok b) (hb : ¬ (b = true)) :
    lt.sizeOf (absLsNodeView v) < Idx.idxCap := by
  rw [arena.store.LsTables.full_of] at h
  exact tbl_not_full_size hrel.lists h hb

theorem lstables_push_abs {rt lt} (hrel : LsTablesRel rt lt) (hinv : LsTablesInv rt)
    {v : alloc.vec.Vec arena.handle.LIdx} {d : arena.store.LDer} {dl : LDer}
    (hdl : derObsL dl = derObsL (absLDer d))
    {tier : Std.U32} {i : arena.handle.LsIdx} {rt'}
    (h : arena.store.LsTables.push rt v d tier = ok (i, rt')) :
    absLsIdx i = (lt.push (absLsNodeView v) dl (absU32 tier)).2 ∧
      LsTablesRel rt' (lt.push (absLsNodeView v) dl (absU32 tier)).1 ∧
      LsTablesInv rt' := by
  rw [arena.store.LsTables.push] at h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [dupId_lsidx _ _ he1] at h
  obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have he := Result.ok_injective h
  simp only [Prod.mk.injEq] at he
  obtain ⟨hr, hs'⟩ := he
  subst hr; subst hs'
  have hhandle : absLsIdx hnew
      = Idx.mk LsTag.list (absU32 tier) (UInt32.ofNat lt.lists.size) := by
    rw [lsidx_pack_abs hpk, lstag_list_abs, cast_u32_size hn2,
      tbl_size_abs hrel.lists hn1]
  obtain ⟨hrel1, hinv1⟩ :=
    tbl_push_abs hrel.lists hinv.lists list_eq2 dupId_listnode absListNode_inj
      (P := ListNodeWF) trivial (dl := dl) hdl ht1
  simp only [absListNode] at hrel1
  rw [hhandle] at hrel1
  exact ⟨hhandle, ⟨hrel1⟩, ⟨hinv1⟩⟩

/-- `LsStore::der_of_view_from` against `LsStore.derOfView` on the suffix, up
to the hash: the observed field is the has-a-parameter bit, and the port's
`if hu.has_param` is the twin's `||`. -/
theorem lsstore_der_of_view_from_abs {pers rs ls} (hrel : LsStoreRel pers rs ls)
    {v : alloc.vec.Vec arena.handle.LIdx} :
    ∀ k (i : Std.Usize), v.length - i.val ≤ k → ∀ {d},
      arena.store.LsStore.der_of_view_from rs pers v i = ok d →
      derObsL (ls.derOfView ((v.val.drop i.val).map absLIdx))
        = derObsL (absLDer d) := by
  intro k
  induction k with
  | zero =>
    intro i hk d h
    rw [arena.store.LsStore.der_of_view_from.eq_def] at h; simp only [] at h
    rw [if_pos (by scalar_tac)] at h
    rw [List.drop_eq_nil_of_le (by scalar_tac), ← Result.ok_injective h]
    rfl
  | succ k ih =>
    intro i hk d h
    rw [arena.store.LsStore.der_of_view_from.eq_def] at h; simp only [] at h
    split at h
    · rw [List.drop_eq_nil_of_le (by scalar_tac), ← Result.ok_injective h]
      rfl
    · rename_i hlt
      have hb : i.val < v.length := by scalar_tac
      obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hlv : v.val[i.val]? = some l := vec_index_some hl
      have hlv' : v.val[i.val] = l := by
        have hg := List.getElem?_eq_getElem hb
        rw [hg] at hlv; exact (Option.some.injEq _ _ ▸ hlv)
      obtain ⟨hu, hhu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := by
        have hx := ConRon.Refine.Nat.uadd_val hi2; simpa using hx
      obtain ⟨hr, hhr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i3, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hih := ih i2 (by scalar_tac) hhr
      rw [hi2v] at hih
      have hud := lstore_derived_abs hrel.lvl hhu
      rw [List.drop_eq_getElem_cons hb, List.map_cons, hlv']
      show ((ls.ls.derived (absLIdx l)).hasParam
        || derObsL (ls.derOfView ((v.val.drop (i.val + 1)).map absLIdx))) = _
      rw [hih]
      split at h <;> rename_i hp
      · rw [← Result.ok_injective h]
        rw [show (ls.ls.derived (absLIdx l)).hasParam = true from
          hud.trans (by simp only [derObsL, absLDer]; exact hp)]
        rfl
      · rw [← Result.ok_injective h]
        rw [show (ls.ls.derived (absLIdx l)).hasParam = false from
          hud.trans (by simp only [derObsL, absLDer]; simpa using hp)]
        rfl

theorem lsstore_der_of_view_abs {pers rs ls} (hrel : LsStoreRel pers rs ls)
    {v : alloc.vec.Vec arena.handle.LIdx} {d}
    (h : arena.store.LsStore.der_of_view rs pers v = ok d) :
    derObsL (ls.derOfView (absLsNodeView v)) = derObsL (absLDer d) := by
  rw [arena.store.LsStore.der_of_view] at h
  have hh := lsstore_der_of_view_from_abs hrel v.length 0#usize (by scalar_tac) h
  simpa [absLsNodeView] using hh

/-! ### The level-list tier's `intern` -/

/-- `ECapAt` at the level-list store. -/
def LsCapAt (st : LsStore) (v : LsNodeView) : Prop :=
  st.find? v = none →
    (if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap

theorem LsCapAt.of_find_ne {st : LsStore} {v : LsNodeView} (h : st.find? v ≠ none) :
    LsCapAt st v := fun hn => absurd hn h

theorem LsCapAt.of_scr_size {st : LsStore} {v : LsNodeView} (hon : st.scratchOn = true)
    (h : st.scr.sizeOf v < Idx.idxCap) : LsCapAt st v := by
  intro _; rw [if_pos hon]; exact h

theorem LsCapAt.of_pers_size {st : LsStore} {v : LsNodeView} (hoff : st.scratchOn = false)
    (h : st.pers.sizeOf v < Idx.idxCap) : LsCapAt st v := by
  intro _; rw [if_neg (by rw [hoff]; simp)]; exact h

/-- The level-list store's persistent probe, under the `shared_on` select. -/
theorem lsstore_pers_find_abs {pers rs ls} (hrel : LsStoreRel pers rs ls)
    (hinv : LsStoreInv pers rs) {v : alloc.vec.Vec arena.handle.LIdx}
    {o} (h : arena.store.LsStore.pers_find rs pers v = ok o) :
    ls.pers.find? (absLsNodeView v) = o.map absLsIdx := by
  rw [arena.store.LsStore.pers_find] at h
  have hx := hrel.perst; have hy := hinv.perst
  unfold rPersLs at hx hy
  split at h <;> rename_i hs
  · rw [if_pos hs] at hx hy; exact lstables_find_abs hx hy h
  · rw [if_neg hs] at hx hy; exact lstables_find_abs hx hy h


/-- `arena::store::LsStore.intern` against `LsStore.intern`: the same control
flow at the one constructor array the level-list tier has. -/
theorem lsstore_intern_abs {pers rs ls} (hrel : LsStoreRel pers rs ls)
    (hinv : LsStoreInv pers rs)
    {v : alloc.vec.Vec arena.handle.LIdx} {r} {rs'}
    (h : arena.store.LsStore.intern rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absLsIdx hh = (ls.intern (absLsNodeView v)).2 ∧
        LsStoreRel pers rs' (ls.intern (absLsNodeView v)).1 ∧
        LsStoreInv pers rs' ∧ LsCapAt ls (absLsNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.LsStore.intern] at h
  obtain ⟨hit, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hE3 := lsstore_pers_find_abs hrel hinv hq
  simp only [LsStore.intern]
  cases hitc : hit with
  | some hp =>
    simp only [hitc] at h
    have hpp : ls.pers.find? (absLsNodeView v) = some (absLsIdx hp) := by
      rw [hE3, hitc]; rfl
    simp only [hpp]
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ?_⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      refine ⟨rfl, hrel, hinv, LsCapAt.of_find_ne ?_⟩
      have hf : ls.find? (absLsNodeView v) = some (absLsIdx hp) := by
        simp only [LsStore.find?, hpp]
      rw [hf]; simp
    · intro ee hbad; simp at hbad
    · exact ⟨rfl, rfl⟩
  | none =>
    simp only [hitc] at h
    have hpn : ls.pers.find? (absLsNodeView v) = none := by rw [hE3, hitc]; rfl
    simp only [hpn, hrel.scratchOn]
    split at h <;> rename_i hsc
    · -- the scratch tier
      rw [if_pos hsc]
      obtain ⟨o, hfs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hE4 : ls.scr.find? (absLsNodeView v) = o.map absLsIdx :=
        lstables_find_abs hrel.scrt hinv.scrt hfs
      cases hoc : o with
      | some hs =>
        simp only [hoc] at h
        have hss : ls.scr.find? (absLsNodeView v) = some (absLsIdx hs) := by
          rw [hE4, hoc]; rfl
        simp only [hss]
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs'⟩ := he
        subst hr; subst hs'
        refine ⟨?_, ?_, ?_⟩
        · intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          refine ⟨rfl, hrel, hinv, LsCapAt.of_find_ne ?_⟩
          have hf : ls.find? (absLsNodeView v) = some (absLsIdx hs) := by
            simp only [LsStore.find?, hpn]
            rw [if_pos (hrel.scratchOn.trans hsc), hss]
          rw [hf]; simp
        · intro ee hbad; simp at hbad
        · exact ⟨rfl, rfl⟩
      | none =>
        simp only [hoc] at h
        have hsn : ls.scr.find? (absLsNodeView v) = none := by rw [hE4, hoc]; rfl
        simp only [hsn]
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        split at h <;> rename_i hfull
        · -- the array is full: `Native`, which claims nothing
          obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs2⟩ := he
          subst hr; subst hs2
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
        · -- the append
          obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨pr, hpu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hnew, t1⟩ := pr
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs'⟩ := he
          subst hr; subst hs'
          obtain ⟨hhandle, hrel1, hinv1⟩ :=
            lstables_push_abs hrel.scrt hinv.scrt
              (dl := ls.derOfView (absLsNodeView v))
              (lsstore_der_of_view_abs hrel hd) hpu
          rw [tier_s_abs] at hhandle hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          exact ⟨hhandle, ⟨hrel.lvl, hrel.perst, hrel1, rfl⟩,
            ⟨hinv.lvl, hinv.perst, hinv1⟩,
            LsCapAt.of_scr_size (hrel.scratchOn.trans hsc)
              (lstables_full_abs' hrel.scrt hb1 hfull)⟩
    · -- the persistent tier
      rw [if_neg hsc]
      split at h <;> rename_i hsh2
      · -- the frozen tier: `Native`, which claims nothing
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
          by simp [hsh2, hsc]⟩
      · have hsh : rs.shared_on = false := by simpa using hsh2
        have hpersLs : rPersLs pers rs = rs.pers := by unfold rPersLs; rw [hsh]; rfl
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hrelP : LsTablesRel rs.pers ls.pers := by rw [← hpersLs]; exact hrel.perst
        have hinvP : LsTablesInv rs.pers := by rw [← hpersLs]; exact hinv.perst
        have hbf : arena.store.LsTables.full_of rs.pers v = ok b1 := by
          rw [arena.store.LsStore.pers_full_of] at hb1
          rw [if_neg hsh2] at hb1; exact hb1
        split at h <;> rename_i hfull
        · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs2⟩ := he
          subst hr; subst hs2
          exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
        · obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨pr, hpu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨hnew, t1⟩ := pr
          have he := Result.ok_injective h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hr, hs'⟩ := he
          subst hr; subst hs'
          obtain ⟨hhandle, hrel1, hinv1⟩ :=
            lstables_push_abs hrelP hinvP (dl := ls.derOfView (absLsNodeView v))
              (lsstore_der_of_view_abs hrel hd) hpu
          rw [tier_p_abs] at hhandle hrel1
          refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
          intro hh hok
          simp only [core.result.Result.Ok.injEq] at hok
          subst hok
          refine ⟨hhandle, ⟨hrel.lvl, ?_, hrel.scrt, rfl⟩, ⟨hinv.lvl, ?_, hinv.scrt⟩,
            LsCapAt.of_pers_size (hrel.scratchOn.trans (by simpa using hsc))
              (lstables_full_abs' hrelP hbf hfull)⟩
          · unfold rPersLs; rw [hsh]; exact hrel1
          · unfold rPersLs; rw [hsh]; exact hinv1

/-! ### Through the nesting, and the monad wrapper -/

theorem estore_intern_levels_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {v : alloc.vec.Vec arena.handle.LIdx} {r} {rs'}
    (h : arena.store.EStore.intern_levels rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absLsIdx hh = (ls.internLevels (absLsNodeView v)).2 ∧
        StoreRel pers rs' (ls.internLevels (absLsNodeView v)).1 ∧
        StoreInv pers rs' ∧ LsCapAt ls.lss (absLsNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.EStore.intern_levels] at h
  obtain ⟨p1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r1, lss1⟩ := p1
  have e0 := Result.ok_injective h
  simp only [Prod.mk.injEq] at e0
  obtain ⟨e0a, e0b⟩ := e0
  subst e0a; subst e0b
  obtain ⟨hok, herr, -⟩ :=
    lsstore_intern_abs (ls := ls.lss) hrel.lss hinv.lss h1
  refine ⟨?_, herr, rfl, rfl⟩
  intro hh hoc
  obtain ⟨hhd, hrel1, hinv1, hcap⟩ := hok hh hoc
  exact ⟨hhd, ⟨hrel1, hrel.perst, hrel.scrt, hrel.scratchOn⟩,
    ⟨hinv1, hinv.perst, hinv.scrt⟩, hcap⟩

theorem LsStore_intern_of_find {st : LsStore} {v : LsNodeView} {h : LsIdx}
    (hf : st.find? v = some h) : st.intern v = (st, h) := by
  simp only [LsStore.find?] at hf
  simp only [LsStore.intern]
  split at hf
  · simp only [Option.some.injEq] at hf; rw [hf]
  · split at hf
    · rename_i hon
      rw [if_pos hon]
      cases hs : st.scr.find? v with
      | some i =>
        simp only [hs, Option.some.injEq] at hf
        rw [hf]
      | none => simp only [hs] at hf; simp at hf
    · simp at hf

theorem EStore_internLevels_of_find {st : EStore} {v : LsNodeView} {h : LsIdx}
    (hf : st.lss.find? v = some h) : st.internLevels v = (st, h) := by
  have h1 : st.lss.intern v = (st.lss, h) := LsStore_intern_of_find hf
  simp only [EStore.internLevels, h1]

theorem internLevels_storeWF {st : EStore} {v : LsNodeView} (hwf : StoreWF st)
    (hview : st.lss.ViewOK v) (hcap : LsCapAt st.lss v) :
    StoreWF (st.internLevels v).1 := by
  cases hf : st.lss.find? v with
  | some h => rw [EStore_internLevels_of_find hf]; exact hwf
  | none => exact EStore.internLevels_wf hwf hview (hcap hf)

theorem internLsNode_run_of_cap {lst : AState} {v : LsNodeView}
    (hcap : LsCapAt lst.store.lss v) :
    (Arena.internLsNode v).run lst
      = .ok ((lst.store.internLevels v).2,
             { lst with store := (lst.store.internLevels v).1 }) := by
  simp only [Arena.internLsNode, run_get_bind]
  cases hf : lst.store.lss.find? v with
  | some h => rw [EStore_internLevels_of_find hf]; rfl
  | none =>
    rw [if_pos (hcap hf)]
    cases hi : lst.store.internLevels v with
    | mk st1 h1 => rfl

/-- `arena::monad::intern_ls_node` against `Arena.internLsNode`. -/
theorem intern_ls_node_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (v : alloc.vec.Vec arena.handle.LIdx)
    (hrun : arena.monad.intern_ls_node pers st v = ok o) :
    Sim₀ absLsIdx pers lst o
      (Arena.internLsNode (absLsNodeView v)) := by
  rw [arena.monad.intern_ls_node] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_levels_abs (ls := lst.store) hrel.store hinv.store hp
  show AOut₀ absLsIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with store := (lst.store.internLevels (absLsNodeView v)).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [internLsNode_run_of_cap hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-! ### The promote window's relation, and its `Sim`

**Task #97-P5-Fresh.**  `Arena/WF.lean`'s section note has the ruling and the
parallel-checking argument: `NWFAt.fresh` holds only LOCALLY, so a lemma about
`internPersistent` cannot conclude `StoreWF` and therefore cannot conclude
`AStateRel`.  What it concludes instead is the sibling below — `AStateRel`
with `storeWF` at the weak invariant `StoreWF'`, and `AOut`/`Sim` rebuilt on
it.  Everything else about the shape is unchanged, and `AStateRelW.of_rel`
lets a caller that holds the STRONG relation feed a lemma that wants the weak
one, which is what keeps the restatement additive: no existing lemma moves.

These belong beside `AOut`/`Sim` in `Refine2/Shape.lean`; they are here
because `Refine2/Shape.lean` is not this task's lane and the definitions are
purely additive.  Moving them up is a two-line follow-up. -/

/-- `AStateRel` at the promote window's invariant. -/
structure AStateRelW (pers : arena.store.PersTier) (rs : arena.monad.AState)
    (ls : AState) : Prop where
  store : StoreRel pers rs.store ls.store
  memos : MemosRel rs.memos ls.memos
  caches : CachesRel rs.caches ls.caches
  pins : PinsRel rs.pins ls.pins
  storeWF : StoreWF' ls.store

/-- The strong relation is the weak one: two clauses of the twin's store
invariant forgotten, nothing else. -/
theorem AStateRelW.of_rel {pers rs ls} (h : AStateRel pers rs ls) :
    AStateRelW pers rs ls :=
  ⟨h.store, h.memos, h.caches, h.pins, StoreWF'.of_wf h.storeWF⟩

/-- `AOut` at the promote window's relation. -/
def AOutW {α β : Type} (A : α → β) (WF : α → Prop)
    (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError (β × AState)) : Prop :=
  match o with
  | .Ok r => ∃ lst', x = .ok (A r, lst') ∧ AStateRelW pers st' lst' ∧
      AStateInv pers st' ∧ Ext lst.store lst'.store ∧ WF r
  | .Err e => AErrSim e x

theorem AOutW.ok {α β : Type} {A : α → β} {WF : α → Prop} {r : α}
    {pers : arena.store.PersTier} {lst lst' : AState} {st' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)}
    (hx : x = .ok (A r, lst')) (hrel : AStateRelW pers st' lst')
    (hinv : AStateInv pers st') (hext : Ext lst.store lst'.store) (hr : WF r) :
    AOutW A WF pers lst (.Ok r) st' x :=
  ⟨lst', hx, hrel, hinv, hext, hr⟩

theorem AOutW.err {α β : Type} {A : α → β} {WF : α → Prop}
    {e : kernel.core_types.CheckError} {pers : arena.store.PersTier}
    {lst : AState} {st' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)} (h : AErrSim e x) :
    AOutW A WF pers lst (.Err e) st' x := h

/-- `Sim` at the promote window's relation. -/
def SimW {α β : Type} (A : α → β) (WF : α → Prop)
    (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState)
    (x : AM β) : Prop :=
  AOutW A WF pers lst o.1 o.2 (x.run lst)

/-! ### The persistent tier's capacity predicates at the level and level-list
stores -/

/-- `LCapAt` at the persistent tier. -/
def LCapPAt (st : LStore) (v : LNodeView) : Prop :=
  st.pers.find? v = none → st.pers.sizeOf v < Idx.idxCap

theorem LCapPAt.of_find_ne {st : LStore} {v : LNodeView}
    (h : st.pers.find? v ≠ none) : LCapPAt st v := fun hn => absurd hn h

/-- `LsCapAt` at the persistent tier. -/
def LsCapPAt (st : LsStore) (v : LsNodeView) : Prop :=
  st.pers.find? v = none → st.pers.sizeOf v < Idx.idxCap

theorem LsCapPAt.of_find_ne {st : LsStore} {v : LsNodeView}
    (h : st.pers.find? v ≠ none) : LsCapPAt st v := fun hn => absurd hn h

/-! ### The level and level-list tiers' `intern_persistent`

`NStore::intern_persistent`'s control flow verbatim, at the other two
constructor-array tiers; the one thing that is not the name tier's is the
derived record, which is OBSERVED below the name store, so
`lstore_der_of_view_abs` / `lsstore_der_of_view_abs` carry the `push`
obligation here where `derObsN = Unit` made it `rfl`. -/

theorem lstore_intern_persistent_abs {pers rs ls} (hrel : LStoreRel pers rs ls)
    (hinv : LStoreInv pers rs)
    {v : arena.store.LNodeView} {r} {rs'}
    (h : arena.store.LStore.intern_persistent rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absLIdx hh = (ls.internPersistent (absLNodeView v)).2 ∧
        LStoreRel pers rs' (ls.internPersistent (absLNodeView v)).1 ∧
        LStoreInv pers rs' ∧ LCapPAt ls (absLNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.LStore.intern_persistent] at h
  obtain ⟨hit, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hE3 := lstore_pers_find_abs hrel hinv hq
  simp only [LStore.internPersistent]
  cases hitc : hit with
  | some hp =>
    simp only [hitc] at h
    have hpp : ls.pers.find? (absLNodeView v) = some (absLIdx hp) := by
      rw [hE3, hitc]; rfl
    simp only [hpp]
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ?_⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv, LCapPAt.of_find_ne (by rw [hpp]; simp)⟩
    · intro ee hbad; simp at hbad
    · exact ⟨rfl, rfl⟩
  | none =>
    simp only [hitc] at h
    have hpn : ls.pers.find? (absLNodeView v) = none := by rw [hE3, hitc]; rfl
    simp only [hpn]
    split at h <;> rename_i hsh2
    · -- the frozen tier: `Native`, which claims nothing
      obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
      exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
    · have hshared : rs.shared_on = false := by simpa using hsh2
      have hpersL : rPersL pers rs = rs.pers := by unfold rPersL; rw [hshared]; rfl
      have hrelP : LTablesRel rs.pers ls.pers := by rw [← hpersL]; exact hrel.perst
      have hinvP : LTablesInv rs.pers := by rw [← hpersL]; exact hinv.perst
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hbf : arena.store.LTables.full_of rs.pers v = ok b1 := by
        rw [arena.store.LStore.pers_full_of] at hb1
        rw [if_neg hsh2] at hb1; exact hb1
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs2⟩ := he
        subst hr; subst hs2
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
      · obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨pr, hpu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hnew, t1⟩ := pr
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs'⟩ := he
        subst hr; subst hs'
        obtain ⟨hhandle, hrel1, hinv1⟩ :=
          ltables_push_abs hrelP hinvP (dl := ls.derOfView (absLNodeView v))
            (lstore_der_of_view_abs hrel hd) hpu
        rw [tier_p_abs] at hhandle hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.ns, ?_, hrel.scrt, hrel.scratchOn⟩,
          ⟨hinv.ns, ?_, hinv.scrt⟩,
          fun _ => ltables_full_abs hrelP hbf hfull⟩
        · unfold rPersL; rw [hshared]; exact hrel1
        · unfold rPersL; rw [hshared]; exact hinv1

theorem lsstore_intern_persistent_abs {pers rs ls} (hrel : LsStoreRel pers rs ls)
    (hinv : LsStoreInv pers rs)
    {v : alloc.vec.Vec arena.handle.LIdx} {r} {rs'}
    (h : arena.store.LsStore.intern_persistent rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absLsIdx hh = (ls.internPersistent (absLsNodeView v)).2 ∧
        LsStoreRel pers rs' (ls.internPersistent (absLsNodeView v)).1 ∧
        LsStoreInv pers rs' ∧ LsCapPAt ls (absLsNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.LsStore.intern_persistent] at h
  obtain ⟨hit, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hE3 := lsstore_pers_find_abs hrel hinv hq
  simp only [LsStore.internPersistent]
  cases hitc : hit with
  | some hp =>
    simp only [hitc] at h
    have hpp : ls.pers.find? (absLsNodeView v) = some (absLsIdx hp) := by
      rw [hE3, hitc]; rfl
    simp only [hpp]
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs'⟩ := he
    subst hr; subst hs'
    refine ⟨?_, ?_, ?_⟩
    · intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨rfl, hrel, hinv, LsCapPAt.of_find_ne (by rw [hpp]; simp)⟩
    · intro ee hbad; simp at hbad
    · exact ⟨rfl, rfl⟩
  | none =>
    simp only [hitc] at h
    have hpn : ls.pers.find? (absLsNodeView v) = none := by rw [hE3, hitc]; rfl
    simp only [hpn]
    split at h <;> rename_i hsh2
    · -- the frozen tier: `Native`, which claims nothing
      obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
      exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
    · have hshared : rs.shared_on = false := by simpa using hsh2
      have hpersLs : rPersLs pers rs = rs.pers := by unfold rPersLs; rw [hshared]; rfl
      have hrelP : LsTablesRel rs.pers ls.pers := by rw [← hpersLs]; exact hrel.perst
      have hinvP : LsTablesInv rs.pers := by rw [← hpersLs]; exact hinv.perst
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hbf : arena.store.LsTables.full_of rs.pers v = ok b1 := by
        rw [arena.store.LsStore.pers_full_of] at hb1
        rw [if_neg hsh2] at hb1; exact hb1
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs2⟩ := he
        subst hr; subst hs2
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, ⟨rfl, rfl⟩⟩
      · obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨pr, hpu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hnew, t1⟩ := pr
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs'⟩ := he
        subst hr; subst hs'
        obtain ⟨hhandle, hrel1, hinv1⟩ :=
          lstables_push_abs hrelP hinvP (dl := ls.derOfView (absLsNodeView v))
            (lsstore_der_of_view_abs hrel hd) hpu
        rw [tier_p_abs] at hhandle hrel1
        refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ⟨hrel.lvl, ?_, hrel.scrt, hrel.scratchOn⟩,
          ⟨hinv.lvl, ?_, hinv.scrt⟩,
          fun _ => lstables_full_abs' hrelP hbf hfull⟩
        · unfold rPersLs; rw [hshared]; exact hrel1
        · unfold rPersLs; rw [hshared]; exact hinv1


/-! ### Through the nesting, and the monad wrappers

The three `EStore::intern_*_persistent` are the same one-line wrappers their
non-persistent siblings are.  (Finding 17's first half, `shared_on = false`,
is retired: the frozen persistent tier answers `Native` — task
#97-P5-Unfreeze.) -/

theorem estore_intern_name_persistent_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {v : arena.store.NNodeView} (hvwf : NNodeViewWF v) {r} {rs'}
    (h : arena.store.EStore.intern_name_persistent rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absNIdx hh = (ls.internNamePersistent (absNNodeView v)).2 ∧
        StoreRel pers rs' (ls.internNamePersistent (absNNodeView v)).1 ∧
        StoreInv pers rs' ∧ NCapPAt ls.ns (absNNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.EStore.intern_name_persistent] at h
  obtain ⟨p1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r1, lss1⟩ := p1
  rw [arena.store.LsStore.intern_name_persistent] at h1
  obtain ⟨p2, h2, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
  obtain ⟨r2, l2⟩ := p2
  rw [arena.store.LStore.intern_name_persistent] at h2
  obtain ⟨p3, h3, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
  obtain ⟨r3, n3⟩ := p3
  have e2 := Result.ok_injective h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨e2a, e2b⟩ := e2
  subst e2a; subst e2b
  have e1 := Result.ok_injective h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨e1a, e1b⟩ := e1
  subst e1a; subst e1b
  have e0 := Result.ok_injective h
  simp only [Prod.mk.injEq] at e0
  obtain ⟨e0a, e0b⟩ := e0
  subst e0a; subst e0b
  obtain ⟨hok, herr, -⟩ :=
    nstore_intern_persistent_abs (ls := ls.ns) hrel.lss.lvl.ns hinv.lss.lvl.ns
      hvwf h3
  refine ⟨?_, herr, rfl, rfl⟩
  intro hh hoc
  obtain ⟨hhd, hrel1, hinv1, hcap⟩ := hok hh hoc
  exact ⟨hhd,
    ⟨⟨⟨hrel1, hrel.lss.lvl.perst, hrel.lss.lvl.scrt, hrel.lss.lvl.scratchOn⟩,
      hrel.lss.perst, hrel.lss.scrt, hrel.lss.scratchOn⟩,
     hrel.perst, hrel.scrt, hrel.scratchOn⟩,
    ⟨⟨⟨hinv1, hinv.lss.lvl.perst, hinv.lss.lvl.scrt⟩, hinv.lss.perst, hinv.lss.scrt⟩,
      hinv.perst, hinv.scrt⟩,
    hcap⟩

theorem estore_intern_level_persistent_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {v : arena.store.LNodeView} {r} {rs'}
    (h : arena.store.EStore.intern_level_persistent rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absLIdx hh = (ls.internLevelPersistent (absLNodeView v)).2 ∧
        StoreRel pers rs' (ls.internLevelPersistent (absLNodeView v)).1 ∧
        StoreInv pers rs' ∧ LCapPAt ls.ls (absLNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.EStore.intern_level_persistent] at h
  obtain ⟨p1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r1, lss1⟩ := p1
  rw [arena.store.LsStore.intern_level_persistent] at h1
  obtain ⟨p2, h2, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
  obtain ⟨r2, l2⟩ := p2
  have e1 := Result.ok_injective h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨e1a, e1b⟩ := e1
  subst e1a; subst e1b
  have e0 := Result.ok_injective h
  simp only [Prod.mk.injEq] at e0
  obtain ⟨e0a, e0b⟩ := e0
  subst e0a; subst e0b
  obtain ⟨hok, herr, -⟩ :=
    lstore_intern_persistent_abs (ls := ls.ls) hrel.lss.lvl hinv.lss.lvl h2
  refine ⟨?_, herr, rfl, rfl⟩
  intro hh hoc
  obtain ⟨hhd, hrel1, hinv1, hcap⟩ := hok hh hoc
  exact ⟨hhd,
    ⟨⟨hrel1, hrel.lss.perst, hrel.lss.scrt, hrel.lss.scratchOn⟩,
     hrel.perst, hrel.scrt, hrel.scratchOn⟩,
    ⟨⟨hinv1, hinv.lss.perst, hinv.lss.scrt⟩, hinv.perst, hinv.scrt⟩,
    hcap⟩

theorem estore_intern_levels_persistent_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {v : alloc.vec.Vec arena.handle.LIdx} {r} {rs'}
    (h : arena.store.EStore.intern_levels_persistent rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absLsIdx hh = (ls.internLevelsPersistent (absLsNodeView v)).2 ∧
        StoreRel pers rs' (ls.internLevelsPersistent (absLsNodeView v)).1 ∧
        StoreInv pers rs' ∧ LsCapPAt ls.lss (absLsNodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.EStore.intern_levels_persistent] at h
  obtain ⟨p1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r1, lss1⟩ := p1
  have e0 := Result.ok_injective h
  simp only [Prod.mk.injEq] at e0
  obtain ⟨e0a, e0b⟩ := e0
  subst e0a; subst e0b
  obtain ⟨hok, herr, -⟩ :=
    lsstore_intern_persistent_abs (ls := ls.lss) hrel.lss hinv.lss h1
  refine ⟨?_, herr, rfl, rfl⟩
  intro hh hoc
  obtain ⟨hhd, hrel1, hinv1, hcap⟩ := hok hh hoc
  exact ⟨hhd, ⟨hrel1, hrel.perst, hrel.scrt, hrel.scratchOn⟩,
    ⟨hinv1, hinv.perst, hinv.scrt⟩, hcap⟩

/-! ### The twin's side: a promote-intern at a cons HIT moves nothing -/

theorem EStore_internNamePersistent_of_persFind {st : EStore} {v : NNodeView}
    {h : NIdx} (hf : st.ns.pers.find? v = some h) :
    st.internNamePersistent v = (st, h) := by
  have h1 : st.lss.ls.ns.internPersistent v = (st.lss.ls.ns, h) := by
    simp only [NStore.internPersistent, show st.lss.ls.ns.pers.find? v = some h from hf]
  simp only [EStore.internNamePersistent, LsStore.internNamePersistent,
    LStore.internNamePersistent, h1]

theorem EStore_internLevelPersistent_of_persFind {st : EStore} {v : LNodeView}
    {h : LIdx} (hf : st.ls.pers.find? v = some h) :
    st.internLevelPersistent v = (st, h) := by
  have h1 : st.lss.ls.internPersistent v = (st.lss.ls, h) := by
    simp only [LStore.internPersistent, show st.lss.ls.pers.find? v = some h from hf]
  simp only [EStore.internLevelPersistent, LsStore.internLevelPersistent, h1]

theorem EStore_internLevelsPersistent_of_persFind {st : EStore} {v : LsNodeView}
    {h : LsIdx} (hf : st.lss.pers.find? v = some h) :
    st.internLevelsPersistent v = (st, h) := by
  have h1 : st.lss.internPersistent v = (st.lss, h) := by
    simp only [LsStore.internPersistent, hf]
  simp only [EStore.internLevelsPersistent, h1]

/-! ### Finding 17's clause at the three nested promote-interns -/

theorem internNamePersistent_storeWF' {st : EStore} {v : NNodeView}
    (hwf : StoreWF' st) (hview : st.ns.ViewOK v) (hp : NViewPers v)
    (hcap : NCapPAt st.ns v) : StoreWF' (st.internNamePersistent v).1 := by
  cases hf : st.ns.pers.find? v with
  | some h => rw [EStore_internNamePersistent_of_persFind hf]; exact hwf
  | none => exact EStore.internNamePersistent_wf' hwf hview hp (hcap hf)

/-! ### The twin actions' runs -/

theorem internPersistentN_run_of_cap {lst : AState} {v : NNodeView}
    (hcap : NCapPAt lst.store.ns v) :
    (Arena.internPersistentN v).run lst
      = .ok ((lst.store.internNamePersistent v).2,
             { lst with store := (lst.store.internNamePersistent v).1 }) := by
  simp only [Arena.internPersistentN, run_get_bind]
  cases hf : lst.store.ns.pers.find? v with
  | some h => rw [EStore_internNamePersistent_of_persFind hf]; rfl
  | none =>
    rw [if_pos (hcap hf)]
    cases hi : lst.store.internNamePersistent v with
    | mk st1 h1 => rfl

theorem internPersistentL_run_of_cap {lst : AState} {v : LNodeView}
    (hcap : LCapPAt lst.store.ls v) :
    (Arena.internPersistentL v).run lst
      = .ok ((lst.store.internLevelPersistent v).2,
             { lst with store := (lst.store.internLevelPersistent v).1 }) := by
  simp only [Arena.internPersistentL, run_get_bind]
  cases hf : lst.store.ls.pers.find? v with
  | some h => rw [EStore_internLevelPersistent_of_persFind hf]; rfl
  | none =>
    rw [if_pos (hcap hf)]
    cases hi : lst.store.internLevelPersistent v with
    | mk st1 h1 => rfl

theorem internPersistentLs_run_of_cap {lst : AState} {v : LsNodeView}
    (hcap : LsCapPAt lst.store.lss v) :
    (Arena.internPersistentLs v).run lst
      = .ok ((lst.store.internLevelsPersistent v).2,
             { lst with store := (lst.store.internLevelsPersistent v).1 }) := by
  simp only [Arena.internPersistentLs, run_get_bind]
  cases hf : lst.store.lss.pers.find? v with
  | some h => rw [EStore_internLevelsPersistent_of_persFind hf]; rfl
  | none =>
    rw [if_pos (hcap hf)]
    cases hi : lst.store.internLevelsPersistent v with
    | mk st1 h1 => rfl

/-! ### The four `intern_persistent_*_run`

**Finding 17, discharged** (task #97-P5-Fresh).  Three things changed against
the statements round 2 left `sorry`:

* the conclusion is `SimW`, not `Sim` — `internPersistent` breaks `fresh`, so
  the twin post-state satisfies the promote window's invariant and not
  `StoreWF` (`Arena/WF.lean`'s note has the ruling and the parallel-checking
  argument); the hypothesis is `AStateRelW` for the same reason, so that a
  walk can chain one promote-intern after another;
* `shared_on = false`, which was finding 17's cheap half — retired in task
  #97-P5-Unfreeze, since the frozen persistent tier answers `Native`, which
  claims nothing;
* `ViewOK` and `…ViewPers` — the view's handles decode, and they are already
  PERSISTENT.  The second is `Arena/Store.lean`'s *"added precondition"*:
  `childOK` carries `i.isPersistent → c.isPersistent` and a promotion has it by
  construction, because it promotes the children first.  It is not free the way
  it is for `intern`, where `scrOff` gives it.

The `WF` slot is not `fun _ => True` any more: **the handle a promote-intern
answers is persistent**, which is the whole purpose of the operation and what
the walk above it needs at the next node's `…ViewPers`. -/

/-! ### The E tier's own `intern_persistent`

`EStore::intern_persistent` is view-GENERIC where the non-persistent
expression tier has ten entry points, so it wants the generic
`etables_{find,full_of,push}_abs` (ten arms each) and `estore_der_of_view_obs`
under them, plus the binder DATUM's own promote-intern.  Task #97-P5-Fresh §7
priced exactly this; `Arena/WFProofs.lean`'s new section is the twin half.

**The datum array's capacity is no longer a hypothesis here** (task
#97-T2-LOCKSTEP, audit D3).  `intern_bm_persistent` tests `Tbl::full` only
where IT appends; the twin's `internPersistentE` used to test `bms` on every
binder-node miss, so the corner was carried as `hbmcap`.  The twin now runs
the datum step first with its own miss-path test, as the port does, and both
capacity facts are CONCLUSIONS of `estore_intern_persistent_abs`.  The old
`hbmcap` arguments stay in the signatures, unused, until slice 3. -/

/-- An expression node view is well formed when its literal is: the other nine
constructor records carry only handles and scalars, so their `*NodeWF` is
`True` and only `lit` has anything to say. -/
def ENodeViewWF : arena.store.ENodeView → Prop
  | .Lit l => ConRon.Refine.LiteralWF l
  | .Lam _ _ m => ConRon.Refine.PropWhenWF m.pw
  | .ForallE _ _ m => ConRon.Refine.PropWhenWF m.pw
  | _ => True

/-- `arena::store::ETables.find` against `ETables.find?` — the GENERIC probe,
which the persistent tier's `intern` needs because `EStore::intern_persistent`
is view-generic where the non-persistent tier has ten entry points. -/
theorem etables_find_abs {rt lt} (hrel : ETablesRel rt lt) (hinv : ETablesInv rt)
    {v : arena.store.ENodeView} (hvwf : ENodeViewWF v) {mi : arena.handle.BMIdx}
    {o : Option arena.handle.EIdx}
    (h : arena.store.ETables.find rt v mi = ok o) :
    lt.find? (absENodeView v) (absBMIdx mi) = o.map absEIdx := by
  cases v with
  | BVar i =>
    simp only [arena.store.ETables.find] at h
    exact tbl_find_abs hrel.bvars hinv.bvars bvar_eq2 dupId_eidx
      (P := BVarNodeWF) trivial h
  | FVar idx ty =>
    simp only [arena.store.ETables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hx] at h
    exact tbl_find_abs hrel.fvars hinv.fvars fvar_eq2 dupId_eidx
      (P := FVarNodeWF) trivial h
  | «Sort» u =>
    simp only [arena.store.ETables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ hx] at h
    exact tbl_find_abs hrel.sorts hinv.sorts sort_eq2 dupId_eidx
      (P := SortNodeWF) trivial h
  | Const n us =>
    simp only [arena.store.ETables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_nidx _ _ hx] at h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lsidx _ _ hy] at h
    exact tbl_find_abs hrel.consts hinv.consts const_eq2 dupId_eidx
      (P := ConstNodeWF) trivial h
  | App f a =>
    simp only [arena.store.ETables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hx] at h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hy] at h
    exact tbl_find_abs hrel.apps hinv.apps app_eq2 dupId_eidx
      (P := AppNodeWF) trivial h
  | Lam ty b m =>
    simp only [arena.store.ETables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hx] at h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hy] at h
    obtain ⟨z, hz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_bmidx _ _ hz] at h
    exact tbl_find_abs hrel.lams hinv.lams bind_eq2 dupId_eidx
      (P := BindNodeWF) trivial h
  | ForallE ty b m =>
    simp only [arena.store.ETables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hx] at h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hy] at h
    obtain ⟨z, hz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_bmidx _ _ hz] at h
    exact tbl_find_abs hrel.foralls hinv.foralls bind_eq2 dupId_eidx
      (P := BindNodeWF) trivial h
  | LetE ty val b =>
    simp only [arena.store.ETables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hx] at h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hy] at h
    obtain ⟨z, hz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hz] at h
    exact tbl_find_abs hrel.lets hinv.lets let_eq2 dupId_eidx
      (P := LetNodeWF) trivial h
  | Lit l =>
    simp only [arena.store.ETables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [ConRon.Refine.Expr.literal_dup_eq hx] at h
    exact tbl_find_abs hrel.lits hinv.lits lit_eq2 dupId_eidx
      (P := LitNodeWF) hvwf h
  | Proj n i e =>
    simp only [arena.store.ETables.find] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_nidx _ _ hx] at h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hy] at h
    exact tbl_find_abs hrel.projs hinv.projs proj_eq2 dupId_eidx
      (P := ProjNodeWF) trivial h


/-- `arena::store::ETables.full_of = false` IS the twin's capacity test at the
view's own array — `tbl_not_full_size` (finding 14's second half) made
view-generic. -/
theorem etables_not_full_size {rt lt} (hrel : ETablesRel rt lt)
    {v : arena.store.ENodeView} {b : Bool}
    (h : arena.store.ETables.full_of rt v = ok b) (hb : ¬ (b = true)) :
    lt.sizeOf (absENodeView v) < Idx.idxCap := by
  cases v <;> simp only [arena.store.ETables.full_of] at h
  · exact tbl_not_full_size hrel.bvars h hb
  · exact tbl_not_full_size hrel.fvars h hb
  · exact tbl_not_full_size hrel.sorts h hb
  · exact tbl_not_full_size hrel.consts h hb
  · exact tbl_not_full_size hrel.apps h hb
  · exact tbl_not_full_size hrel.lams h hb
  · exact tbl_not_full_size hrel.foralls h hb
  · exact tbl_not_full_size hrel.lets h hb
  · exact tbl_not_full_size hrel.lits h hb
  · exact tbl_not_full_size hrel.projs h hb


/-- `arena::store::ETables.push` at the PERSISTENT tier against
`ETables.push`, view-generic: the array's length is the new handle's index,
the tag is the constructor's, and the tier is `TIER_P`. -/
theorem etables_push_pers_abs {rt lt} (hrel : ETablesRel rt lt) (hinv : ETablesInv rt)
    {v : arena.store.ENodeView} (hvwf : ENodeViewWF v)
    {d : Std.U64} {dl : UInt64} (hdl : derObsE dl = derObsE (absU64 d))
    {mi : arena.handle.BMIdx} {p}
    (h : arena.store.ETables.push rt v d mi arena.handle.TIER_P = ok p) :
    absEIdx p.1 = (lt.push (absENodeView v) dl (absBMIdx mi) Idx.tierP).2 ∧
      ETablesRel p.2 (lt.push (absENodeView v) dl (absBMIdx mi) Idx.tierP).1 ∧
      ETablesInv p.2 := by
  cases v with
  | BVar i =>
    simp only [arena.store.ETables.push] at h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl : (hnew, { rt with bvars := t1 }) = p := Result.ok_injective h
    have hhandle : absEIdx hnew
        = Idx.mk ETag.bvar Idx.tierP (UInt32.ofNat lt.bvars.size) := by
      rw [eidx_pack_abs hpk, etag_bvar_abs, tier_p_abs, cast_u32_size hn3,
        tbl_size_abs hrel.bvars hn2]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.bvars hinv.bvars bvar_eq2 dupId_bvarnode absBVarNode_inj
        (P := BVarNodeWF) trivial hdl ht1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with bvars := hrel1 }, { hinv with bvars := hinv1 }⟩
  | FVar idx ty =>
    simp only [arena.store.ETables.push] at h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl : (hnew, { rt with fvars := t1 }) = p := Result.ok_injective h
    have hhandle : absEIdx hnew
        = Idx.mk ETag.fvar Idx.tierP (UInt32.ofNat lt.fvars.size) := by
      rw [eidx_pack_abs hpk, etag_fvar_abs, tier_p_abs, cast_u32_size hn3,
        tbl_size_abs hrel.fvars hn2]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.fvars hinv.fvars fvar_eq2 dupId_fvarnode absFVarNode_inj
        (P := FVarNodeWF) trivial hdl ht1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with fvars := hrel1 }, { hinv with fvars := hinv1 }⟩
  | «Sort» u =>
    simp only [arena.store.ETables.push] at h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl : (hnew, { rt with sorts := t1 }) = p := Result.ok_injective h
    have hhandle : absEIdx hnew
        = Idx.mk ETag.sort Idx.tierP (UInt32.ofNat lt.sorts.size) := by
      rw [eidx_pack_abs hpk, etag_sort_abs, tier_p_abs, cast_u32_size hn3,
        tbl_size_abs hrel.sorts hn2]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.sorts hinv.sorts sort_eq2 dupId_sortnode absSortNode_inj
        (P := SortNodeWF) trivial hdl ht1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with sorts := hrel1 }, { hinv with sorts := hinv1 }⟩
  | Const n us =>
    simp only [arena.store.ETables.push] at h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl : (hnew, { rt with consts := t1 }) = p := Result.ok_injective h
    have hhandle : absEIdx hnew
        = Idx.mk ETag.const Idx.tierP (UInt32.ofNat lt.consts.size) := by
      rw [eidx_pack_abs hpk, etag_const_abs, tier_p_abs, cast_u32_size hn3,
        tbl_size_abs hrel.consts hn2]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.consts hinv.consts const_eq2 dupId_constnode absConstNode_inj
        (P := ConstNodeWF) trivial hdl ht1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with consts := hrel1 }, { hinv with consts := hinv1 }⟩
  | App f a =>
    simp only [arena.store.ETables.push] at h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl : (hnew, { rt with apps := t1 }) = p := Result.ok_injective h
    have hhandle : absEIdx hnew
        = Idx.mk ETag.app Idx.tierP (UInt32.ofNat lt.apps.size) := by
      rw [eidx_pack_abs hpk, etag_app_abs, tier_p_abs, cast_u32_size hn3,
        tbl_size_abs hrel.apps hn2]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.apps hinv.apps app_eq2 dupId_appnode absAppNode_inj
        (P := AppNodeWF) trivial hdl ht1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with apps := hrel1 }, { hinv with apps := hinv1 }⟩
  | Lam ty b m =>
    simp only [arena.store.ETables.push] at h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl : (hnew, { rt with lams := t1 }) = p := Result.ok_injective h
    have hhandle : absEIdx hnew
        = Idx.mk ETag.lam Idx.tierP (UInt32.ofNat lt.lams.size) := by
      rw [eidx_pack_abs hpk, etag_lam_abs, tier_p_abs, cast_u32_size hn3,
        tbl_size_abs hrel.lams hn2]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.lams hinv.lams bind_eq2 dupId_bindnode absBindNode_inj
        (P := BindNodeWF) trivial hdl ht1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with lams := hrel1 }, { hinv with lams := hinv1 }⟩
  | ForallE ty b m =>
    simp only [arena.store.ETables.push] at h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl : (hnew, { rt with foralls := t1 }) = p := Result.ok_injective h
    have hhandle : absEIdx hnew
        = Idx.mk ETag.forallE Idx.tierP (UInt32.ofNat lt.foralls.size) := by
      rw [eidx_pack_abs hpk, etag_forallE_abs, tier_p_abs, cast_u32_size hn3,
        tbl_size_abs hrel.foralls hn2]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.foralls hinv.foralls bind_eq2 dupId_bindnode absBindNode_inj
        (P := BindNodeWF) trivial hdl ht1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with foralls := hrel1 }, { hinv with foralls := hinv1 }⟩
  | LetE ty val b =>
    simp only [arena.store.ETables.push] at h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl : (hnew, { rt with lets := t1 }) = p := Result.ok_injective h
    have hhandle : absEIdx hnew
        = Idx.mk ETag.letE Idx.tierP (UInt32.ofNat lt.lets.size) := by
      rw [eidx_pack_abs hpk, etag_letE_abs, tier_p_abs, cast_u32_size hn3,
        tbl_size_abs hrel.lets hn2]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.lets hinv.lets let_eq2 dupId_letnode absLetNode_inj
        (P := LetNodeWF) trivial hdl ht1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with lets := hrel1 }, { hinv with lets := hinv1 }⟩
  | Lit l =>
    simp only [arena.store.ETables.push] at h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl : (hnew, { rt with lits := t1 }) = p := Result.ok_injective h
    have hhandle : absEIdx hnew
        = Idx.mk ETag.lit Idx.tierP (UInt32.ofNat lt.lits.size) := by
      rw [eidx_pack_abs hpk, etag_lit_abs, tier_p_abs, cast_u32_size hn3,
        tbl_size_abs hrel.lits hn2]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.lits hinv.lits lit_eq2 dupId_litnode absLitNode_inj
        (P := LitNodeWF) hvwf hdl ht1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with lits := hrel1 }, { hinv with lits := hinv1 }⟩
  | Proj n i e =>
    simp only [arena.store.ETables.push] at h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n3, hn3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hnew, hpk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1] at h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl : (hnew, { rt with projs := t1 }) = p := Result.ok_injective h
    have hhandle : absEIdx hnew
        = Idx.mk ETag.proj Idx.tierP (UInt32.ofNat lt.projs.size) := by
      rw [eidx_pack_abs hpk, etag_proj_abs, tier_p_abs, cast_u32_size hn3,
        tbl_size_abs hrel.projs hn2]
    obtain ⟨hrel1, hinv1⟩ :=
      tbl_push_abs hrel.projs hinv.projs proj_eq2 dupId_projnode absProjNode_inj
        (P := ProjNodeWF) trivial hdl ht1
    rw [hhandle] at hrel1
    exact ⟨hhandle, { hrel with projs := hrel1 }, { hinv with projs := hinv1 }⟩


theorem der_of_bind_obs {pers} {rs : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls)
    {tag : Std.U64} {ty bo : arena.handle.EIdx} {m : kernel.expr.BinderMeta}
    (hwf : ConRon.Refine.PropWhenWF m.pw) {d : Std.U64}
    (h : arena.store.EStore.der_of_bind_at rs pers tag ty bo m = ok d) :
    derObsE (ls.derOfBindAt (absU64 tag) (absEIdx ty) (absEIdx bo)
        (ConRon.Refine.absBinderMeta m))
      = derObsE (absU64 d) := by
  rw [arena.store.EStore.der_of_bind_at] at h
  obtain ⟨dt, hdt, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨db, hdb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hm, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨pm, hpmv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hpm : (ConRon.Refine.absBinderMeta m).pw.hasParams = pm :=
    (ConRon.Refine.PropWhen.has_params_shape
      (ConRon.Refine.PropWhen.wf_shape hwf) hpmv).symm
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
  rw [EStore.derOfBindAt, derOfBind]
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




/-- `arena::store::EStore.der_of_view` against `EStore.derOfView`, up to the
observation `derObsE`: the ten arms' `der_of_*_obs`, dispatched. -/
theorem estore_der_of_view_obs {pers} {rs : arena.store.EStore} {ls : EStore}
    (hrel : StoreRel pers rs ls) {v : arena.store.ENodeView} (hvwf : ENodeViewWF v)
    {d : Std.U64}
    (h : arena.store.EStore.der_of_view rs pers v = ok d) :
    derObsE (ls.derOfView (absENodeView v)) = derObsE (absU64 d) := by
  have h19 : absU64 (19#u64 : Std.U64) = (19 : UInt64) := rfl
  have h23 : absU64 (23#u64 : Std.U64) = (23 : UInt64) := rfl
  cases v <;> simp only [arena.store.EStore.der_of_view] at h
  · exact der_of_bvar_obs (ls := ls) h
  · exact der_of_fvar_obs hrel h
  · exact der_of_sort_obs hrel h
  · exact der_of_const_obs hrel h
  · exact der_of_app_obs hrel h
  · have hb := der_of_bind_obs (ls := ls) hrel hvwf h
    rw [h19] at hb; exact hb
  · have hb := der_of_bind_obs (ls := ls) hrel hvwf h
    rw [h23] at hb; exact hb
  · exact der_of_let_obs hrel h
  · exact der_of_lit_obs (ls := ls) h
  · exact der_of_proj_obs hrel h


/-! ### The PERSISTENT tier's `intern`, at the datum and at the node

`EStore::intern_persistent` is `intern_other`'s shape at the expression tier:
probe the persistent cons table, test the persistent array, append there
whatever tier the store is in.  Like the three tiers below it, its frozen
arm is `Native` and needs no hypothesis (task #97-P5-Unfreeze), and unlike
them it has a BINDER DATUM to intern first. -/

theorem estore_intern_bm_persistent_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {m : kernel.expr.BinderMeta} (hwf : ConRon.Refine.PropWhenWF m.pw) {r} {rs'}
    (h : arena.store.EStore.intern_bm_persistent rs pers m = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absBMIdx hh = (ls.internBMPersistent (ConRon.Refine.absBinderMeta m)).2 ∧
        StoreRel pers rs' (ls.internBMPersistent (ConRon.Refine.absBinderMeta m)).1 ∧
        StoreInv pers rs' ∧
        (ls.persFindBM (ConRon.Refine.absBinderMeta m) = none → ls.capOKBMPersistent)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  rw [arena.store.EStore.intern_bm_persistent] at h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, bb, hit⟩ := q
  have hE : e = rs.pers ∧ bb = rs.shared_on ∧
      ls.pers.bms.find? ⟨ConRon.Refine.absPropWhen m.pw⟩ = hit.map absBMIdx := by
    split at hq <;> rename_i hs <;>
      obtain ⟨hit1, hf, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq <;>
      simp only [Result.ok.injEq, Prod.mk.injEq] at hq <;>
      obtain ⟨h1, h2, h3⟩ := hq
    · refine ⟨h1.symm, by rw [← h2, hs], ?_⟩
      rw [← h3]
      exact tbl_find_abs hrel.perst.bms hinv.perst.bms bm_eq2 dupId_bmidx
        (P := BMNodeWF) (show BMNodeWF ⟨m.pw⟩ from hwf)
        (by unfold rPersE; rw [if_pos hs]; exact hf)
    · refine ⟨h1.symm, by rw [← h2]; exact (Bool.not_eq_true _ ▸ hs).symm, ?_⟩
      rw [← h3]
      exact tbl_find_abs hrel.perst.bms hinv.perst.bms bm_eq2 dupId_bmidx
        (P := BMNodeWF) (show BMNodeWF ⟨m.pw⟩ from hwf)
        (by unfold rPersE; rw [if_neg hs]; exact hf)
  obtain ⟨hE1, hE2, hE3⟩ := hE
  subst hE1; subst hE2
  rw [EStore.internBMPersistent]
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
    refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
    intro hh hok
    simp only [core.result.Result.Ok.injEq] at hok
    subst hok
    exact ⟨rfl, hrel, hinv, by simp⟩
  | none =>
    rw [hitc] at h
    simp only [Option.map_none]
    by_cases hfz : rs.shared_on = true
    · -- the frozen tier: `Native`, which claims nothing
      rw [hfz] at h
      obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
      exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
        ⟨hfz.symm, rfl⟩⟩
    have hshared : rs.shared_on = false := by simpa using hfz
    have hpersE : rPersE pers rs = rs.pers := by unfold rPersE; rw [hshared]; rfl
    have hrelP : TblRel BMNodeWF absBMNode absBMIdx absU64 derObsN rs.pers.bms
        ls.pers.bms := by rw [← hpersE]; exact hrel.perst.bms
    have hinvP : TblInv arena.store.BMNode.Insts.Con_ron_coreRonHashmapHashable
        BMNodeWF rs.pers.bms := by rw [← hpersE]; exact hinv.perst.bms
    have hrelPerst : ETablesRel rs.pers ls.pers := by rw [← hpersE]; exact hrel.perst
    have hinvPerst : ETablesInv rs.pers := by rw [← hpersE]; exact hinv.perst
    simp only [hshared] at h
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    split at h <;> rename_i hfull
    · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have he := Result.ok_injective h
      simp only [Prod.mk.injEq] at he
      obtain ⟨hr, hs2⟩ := he
      subst hr; subst hs2
      exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl,
        ⟨hshared.symm, rfl⟩⟩
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
      have hhandle : absBMIdx hnew
          = Idx.mk 0 Idx.tierP (UInt32.ofNat ls.pers.bms.size) := by
        rw [bmidx_pack_abs hpk, tier_p_abs, cast_u32_size hn3,
          tbl_size_abs hrelP hn2]
      obtain ⟨hrel1, hinv1⟩ :=
        tbl_push_abs hrelP hinvP bm_eq2 dupId_bmnode absBMNode_inj
          (P := BMNodeWF) (show BMNodeWF ⟨m.pw⟩ from hwf)
          (dl := hash (ConRon.Refine.absPropWhen m.pw)) rfl ht1
      simp only [absBMNode] at hrel1
      rw [hhandle] at hrel1
      refine ⟨?_, by intro ee hbad; simp at hbad, ⟨hshared.symm, rfl⟩⟩
      intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      exact ⟨hhandle, ⟨hrel.lss, { hrelPerst with bms := hrel1 }, hrel.scrt,
          hrel.scratchOn⟩,
        ⟨hinv.lss, { hinvPerst with bms := hinv1 }, hinv.scrt⟩,
        fun _ => tbl_not_full_size hrelP hb1 hfull⟩


/-- `arena::store::EStore.intern_bm_of_view_persistent` against
`EStore.internBMOfViewPersistent`: eight arms hand back the zero handle and
leave the store alone; the two binder arms are the datum's own promote-intern. -/
theorem estore_intern_bm_of_view_persistent_abs {pers rs ls}
    (hrel : StoreRel pers rs ls) (hinv : StoreInv pers rs)
    {v : arena.store.ENodeView} (hvwf : ENodeViewWF v) {r} {rs'}
    (h : arena.store.EStore.intern_bm_of_view_persistent rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absBMIdx hh = (ls.internBMOfViewPersistent (absENodeView v)).2 ∧
        StoreRel pers rs' (ls.internBMOfViewPersistent (absENodeView v)).1 ∧
        StoreInv pers rs' ∧ ls.persCapBM (absENodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  have hzero : ∀ {b : arena.handle.BMIdx},
      arena.handle.BMIdx.of_word 0#u32 = ok b → absBMIdx b = Idx.ofWord 0 := by
    intro b hb
    obtain rfl : arena.handle.BMIdx.mk 0#u32 = b := Result.ok_injective hb
    rfl
  cases v
  case Lam ty b m =>
    simp only [arena.store.EStore.intern_bm_of_view_persistent] at h
    obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [ConRon.Refine.Expr.binder_meta_dup_eq hbm] at h
    exact estore_intern_bm_persistent_abs hrel hinv hvwf h
  case ForallE ty b m =>
    simp only [arena.store.EStore.intern_bm_of_view_persistent] at h
    obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [ConRon.Refine.Expr.binder_meta_dup_eq hbm] at h
    exact estore_intern_bm_persistent_abs hrel hinv hvwf h
  all_goals
    (simp only [arena.store.EStore.intern_bm_of_view_persistent] at h
     obtain ⟨b0, hb0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
     have he := Result.ok_injective h
     simp only [Prod.mk.injEq] at he
     obtain ⟨hr, hs⟩ := he
     subst hr; subst hs
     refine ⟨?_, by intro ee hbad; simp at hbad, ⟨rfl, rfl⟩⟩
     intro hh hok
     simp only [core.result.Result.Ok.injEq] at hok
     subst hok
     exact ⟨hzero hb0, hrel, hinv, trivial⟩)


/- `ECapPAt` (the node test stated at the ORIGINAL store's `persFind?`) was
retired at audit D3: the twin now makes both of the Rust's capacity tests where
the Rust makes them, and `EStore.persCapBM` / `EStore.persCapNode`
(`Arena/Store.lean`) are those two tests, concluded below from the port's own
`full` answers. -/

/-- `arena::store::EStore.intern_persistent` against `EStore.internPersistent`
— the whole control flow, view-generic: the datum's promote-intern, the
persistent cons probe, the frozen check, the capacity check, the append. -/
theorem estore_intern_persistent_abs' {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs)
    {v : arena.store.ENodeView} (hvwf : ENodeViewWF v)
    {r} {rs'}
    (h : arena.store.EStore.intern_persistent rs pers v = ok (r, rs')) :
    (∀ hh, r = .Ok hh →
        absEIdx hh = (ls.internPersistent (absENodeView v)).2 ∧
        StoreRel pers rs' (ls.internPersistent (absENodeView v)).1 ∧
        StoreInv pers rs' ∧ ls.persCapBM (absENodeView v) ∧
        ls.persCapNode (absENodeView v)) ∧
      (∀ e, r = .Err e → absAErrKind e = none) ∧
      (rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) := by
  -- audit D3: the twin makes the Rust's two capacity tests where the Rust
  -- makes them, so both are CONCLUDED below from the port's own `full`
  -- answers, at the stores the port tests them on — no `StoreWF'`, no
  -- `hbmcap`.
  rw [arena.store.EStore.intern_persistent] at h
  obtain ⟨p1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r1, rs1⟩ := p1
  obtain ⟨hok1, herr1, hfl1⟩ :=
    estore_intern_bm_of_view_persistent_abs (ls := ls) hrel hinv hvwf h1
  obtain ⟨st1, hst1⟩ :
      ∃ s, s = (ls.internBMOfViewPersistent (absENodeView v)).1 := ⟨_, rfl⟩
  obtain ⟨mi1, hmi1⟩ :
      ∃ s, s = (ls.internBMOfViewPersistent (absENodeView v)).2 := ⟨_, rfl⟩
  have hun : ls.internPersistent (absENodeView v) =
      (match st1.pers.find? (absENodeView v) mi1 with
       | some i => (st1, i)
       | none =>
         ({ st1 with pers := (st1.pers.push (absENodeView v)
              (st1.derOfView (absENodeView v)) mi1 Idx.tierP).1 },
           (st1.pers.push (absENodeView v) (st1.derOfView (absENodeView v)) mi1
             Idx.tierP).2)) := by
    rw [hst1, hmi1]; rfl
  have hcapN : ls.persCapNode (absENodeView v) ↔
      (st1.pers.find? (absENodeView v) mi1 = none →
        st1.pers.sizeOf (absENodeView v) < Idx.idxCap) := by
    rw [hst1, hmi1]; rfl
  cases hr1 : r1 with
  | Err e =>
    simp only [hr1] at h
    have he := Result.ok_injective h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hr, hs⟩ := he
    subst hr; subst hs
    exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; exact herr1 e hr1,
      hfl1⟩
  | Ok mi =>
    simp only [hr1] at h
    obtain ⟨hmid, hrel1, hinv1, hcapBM⟩ := hok1 mi hr1
    rw [← hmi1] at hmid
    rw [← hst1] at hrel1
    obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hfind : st1.pers.find? (absENodeView v) mi1 = o.map absEIdx := by
      rw [arena.store.EStore.pers_find] at ho
      have ho' : arena.store.ETables.find (rPersE pers rs1) v mi = ok o := by
        unfold rPersE
        split at ho <;> rename_i hs
        · rw [if_pos hs]; exact ho
        · rw [if_neg hs]; exact ho
      rw [← hmid]
      exact etables_find_abs hrel1.perst hinv1.perst hvwf ho'
    rw [hun, hfind]
    cases hoc : o with
    | some i =>
      simp only [hoc] at h
      have he := Result.ok_injective h
      simp only [Prod.mk.injEq] at he
      obtain ⟨hr, hs⟩ := he
      subst hr; subst hs
      refine ⟨?_, by intro ee hbad; simp at hbad, hfl1⟩
      intro hh hok
      simp only [core.result.Result.Ok.injEq] at hok
      subst hok
      refine ⟨rfl, hrel1, hinv1, hcapBM, hcapN.mpr fun hn => ?_⟩
      simp only [hoc] at hfind
      rw [hfind] at hn; simp at hn
    | none =>
      simp only [Option.map_none]
      simp only [hoc] at h
      by_cases hfz : rs1.shared_on = true
      · -- the frozen tier: `Native`, which claims nothing
        rw [if_pos hfz] at h
        obtain ⟨⟨v1, rfl⟩, rfl⟩ := frozen_native_arm h
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, hfl1⟩
      have hshared1 : rs1.shared_on = false := by simpa using hfz
      have hpersE1 : rPersE pers rs1 = rs1.pers := by
        unfold rPersE; rw [hshared1]; rfl
      simp only [hshared1, Bool.false_eq_true, if_false] at h
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnf : b1 = false → st1.pers.sizeOf (absENodeView v) < Idx.idxCap := by
        intro hbf
        rw [arena.store.EStore.pers_full_of] at hb1
        simp only [hshared1, Bool.false_eq_true, if_false] at hb1
        exact etables_not_full_size (by rw [← hpersE1]; exact hrel1.perst) hb1
          (by rw [hbf]; simp)
      split at h <;> rename_i hfull
      · obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs⟩ := he
        subst hr; subst hs
        exact ⟨by intro hh hok; simp at hok, by intro ee hee; cases hee; rfl, hfl1⟩
      · obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨p2, hp2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨enew, tb1⟩ := p2
        have he := Result.ok_injective h
        simp only [Prod.mk.injEq] at he
        obtain ⟨hr, hs⟩ := he
        subst hr; subst hs
        have hcapn : st1.pers.sizeOf (absENodeView v) < Idx.idxCap :=
          hnf (by simpa using hfull)
        have hder : derObsE (st1.derOfView (absENodeView v)) = derObsE (absU64 d) :=
          estore_der_of_view_obs (ls := st1) hrel1 hvwf hd
        obtain ⟨hhandle, hrelT, hinvT⟩ :=
          etables_push_pers_abs (rt := rs1.pers) (lt := st1.pers)
            (by rw [← hpersE1]; exact hrel1.perst)
            (by rw [← hpersE1]; exact hinv1.perst) hvwf hder hp2
        rw [hmid] at hhandle hrelT
        refine ⟨?_, by intro ee hbad; simp at hbad, ⟨hshared1.symm.trans hfl1.1, hfl1.2⟩⟩
        intro hh hok
        simp only [core.result.Result.Ok.injEq] at hok
        subst hok
        refine ⟨hhandle, ?_, ?_, hcapBM, hcapN.mpr fun _ => hcapn⟩
        · exact ⟨hrel1.lss, by unfold rPersE; simpa using hrelT, hrel1.scrt,
            hrel1.scratchOn⟩
        · exact ⟨hinv1.lss, by unfold rPersE; simpa using hinvT, hinv1.scrt⟩


/-- `Arena.internPersistentE`'s run, in the Rust's order (audit D3): the
datum's promote-intern with its miss-path test, the node probe, the node's
miss-path test — `Arena.internPersistentE_run_eq`. -/
theorem internPersistentE_run_of_cap {lst : AState} {v : ENodeView}
    (hbmcap : lst.store.persCapBM v) (hcap : lst.store.persCapNode v) :
    (Arena.internPersistentE v).run lst
      = .ok ((lst.store.internPersistent v).2,
             { lst with store := (lst.store.internPersistent v).1 }) :=
  ConRon.Arena.internPersistentE_run_eq hbmcap hcap

/-- `arena::monad::intern_persistent_e` against `Arena.internPersistentE`. -/
theorem intern_persistent_e_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (v : arena.store.ENodeView) (hvwf : ENodeViewWF v)
    {o} (hrun : arena.monad.intern_persistent_e pers st v = ok o) :
    Sim₀ absEIdx pers lst o
      (Arena.internPersistentE (absENodeView v)) := by
  rw [arena.monad.intern_persistent_e] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_persistent_abs' (ls := lst.store) hrel.store hinv.store hvwf hp
  show AOut₀ absEIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hbmcap, hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with
        store := (lst.store.internPersistent (absENodeView v)).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [internPersistentE_run_of_cap hbmcap hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_persistent_n` against `Arena.internPersistentN`. -/
theorem intern_persistent_n_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (v : arena.store.NNodeView) (hvwf : NNodeViewWF v)
    {o} (hrun : arena.monad.intern_persistent_n pers st v = ok o) :
    Sim₀ absNIdx pers lst o
      (Arena.internPersistentN (absNNodeView v)) := by
  rw [arena.monad.intern_persistent_n] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_name_persistent_abs (ls := lst.store) hrel.store hinv.store
      hvwf hp
  show AOut₀ absNIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with
        store := (lst.store.internNamePersistent (absNNodeView v)).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [internPersistentN_run_of_cap hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_persistent_n_run₀`.
 `arena::monad::intern_persistent_n` against `Arena.internPersistentN`. -/
theorem intern_persistent_n_run {pers st lst} (hrel : AStateRelW pers st lst)
    (hinv : AStateInv pers st)
    (v : arena.store.NNodeView) (hvwf : NNodeViewWF v)
    (hview : lst.store.ns.ViewOK (absNNodeView v))
    (hpers : NViewPers (absNNodeView v)) {o}
    (hrun : arena.monad.intern_persistent_n pers st v = ok o) :
    SimW absNIdx (fun r => (absNIdx r).isPersistent = true) pers lst o
      (Arena.internPersistentN (absNNodeView v)) := by
  rw [arena.monad.intern_persistent_n] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_name_persistent_abs (ls := lst.store) hrel.store hinv.store
      hvwf hp
  show AOutW absNIdx _ pers lst r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOutW.ok
      (lst' := { lst with
        store := (lst.store.internNamePersistent (absNNodeView v)).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins,
        internNamePersistent_storeWF' hrel.storeWF hview hpers hcap⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
      (EStore.internNamePersistent_ext _ _) ?_
    · rw [internPersistentN_run_of_cap hcap, hhd]
    · rw [hhd]
      exact NStore.internPersistent_pers hrel.storeWF.nsWF hcap
  | Err ee => exact AOutW.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_persistent_l` against `Arena.internPersistentL`. -/
theorem intern_persistent_l_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (v : arena.store.LNodeView)
    {o} (hrun : arena.monad.intern_persistent_l pers st v = ok o) :
    Sim₀ absLIdx pers lst o
      (Arena.internPersistentL (absLNodeView v)) := by
  rw [arena.monad.intern_persistent_l] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_level_persistent_abs (ls := lst.store) hrel.store hinv.store
      hp
  show AOut₀ absLIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with
        store := (lst.store.internLevelPersistent (absLNodeView v)).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [internPersistentL_run_of_cap hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-- `arena::monad::intern_persistent_ls` against `Arena.internPersistentLs`. -/
theorem intern_persistent_ls_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (v : alloc.vec.Vec arena.handle.LIdx)
    {o} (hrun : arena.monad.intern_persistent_ls pers st v = ok o) :
    Sim₀ absLsIdx pers lst o
      (Arena.internPersistentLs (absLsNodeView v)) := by
  rw [arena.monad.intern_persistent_ls] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, -⟩ :=
    estore_intern_levels_persistent_abs (ls := lst.store) hrel.store hinv.store
      hp
  show AOut₀ absLsIdx pers r { st with store := e } _
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap⟩ := hok hh hr
    refine AOut₀.ok
      (lst' := { lst with
        store := (lst.store.internLevelsPersistent (absLsNodeView v)).1 }) ?_
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins⟩
      ⟨hinv', hinv.memos, hinv.caches⟩
    rw [internPersistentLs_run_of_cap hcap, hhd]
  | Err ee => exact AOut₀.err (AErrSim.of_none (herr ee hr))

/-! ### The four transient-tree walks

`intern_{name,level,level_list,levels}` are structural over the TRANSIENT
tree — DESIGN §8.3's *"the tree is a value, not a DAG"* — so there is no fuel
and no memo: the induction is `Refine/{Name,Level}.lean`'s `NameWF.ind_node` /
`LevelWF.ind_node`, and the one loop (`intern_level_list_from`'s cursor over a
`Vec<Level>`) is `read_names_m_from_abs`'s shape.

Three things the walks need that a single `intern_*_node_run` did not, and
each is proved once here:

* **the handle a walk answers DECODES in the state it answered in.**  A step
  hands the next node view a handle the PREVIOUS step made, and
  `intern_*_node_run`'s `hview` is exactly *"this handle decodes"* — which
  `AOut`'s `WF` slot cannot say, because it sees the Rust value and not the
  twin post-state.  So it is a TWIN-ONLY lemma
  (`intern{Name,Level,LevelList,Levels}_run_denote`, a structural induction on
  the twin's own `ConLeche.Name`/`Level`), and it says the stronger and more
  useful thing: *interning a transient tree and denoting the handle is the
  identity*.  `Ext` carries it across the sibling that is interned next, which
  is why the level tier's binary arms cost nothing extra.
* **the tier flags do not move.**  An intern appends to one constructor
  array: every store a `*::intern*` returns is `self`, `{ self with pers := … }`
  or `{ self with scr := … }`, which is what `FlagsEq` records.  (It used to
  carry `intern_*_node_run`'s per-store frozen-tier side condition across a
  step; task #97-P5-Unfreeze retired that condition, and `FlagsEq` stays as a
  frame fact.)
* **the steps compose.**  `AOut.errBind` and `AOut.rebase` are
  `Refine2/ExprOps/Mut.lean`'s two composition lemmas one tier lower; they
  belong in `Refine2/Shape.lean` and are here because `Shape.lean` was not this
  task's lane.

The walks are proved in a `'` form that also concludes `FlagsEq`, because the
induction needs it; the `_run` statement is its first projection and the
`_flags` one its second, which is the shape `intern_e_bvar_run` /
`intern_e_bvar_flags` already has at the expression tier. -/

theorem internNNode_run_inv {lst lst' : AState} {v : NNodeView} {h : NIdx}
    (hrun : (Arena.internNNode v).run lst = .ok (h, lst')) :
    NCapAt lst.store.ns v ∧ h = (lst.store.internName v).2 ∧
      lst' = { lst with store := (lst.store.internName v).1 } := by
  simp only [Arena.internNNode, run_get_bind] at hrun
  cases hf : lst.store.ns.find? v with
  | some i =>
    simp only [hf] at hrun
    rw [EStore_internName_of_find hf]
    have he : (i, lst) = (h, lst') := Except.ok.inj hrun
    simp only [Prod.mk.injEq] at he
    exact ⟨NCapAt.of_find_ne (by rw [hf]; simp), he.1.symm, he.2.symm⟩
  | none =>
    simp only [hf] at hrun
    by_cases hc : (if lst.store.ns.scratchOn = true then lst.store.ns.scr.sizeOf v
        else lst.store.ns.pers.sizeOf v) < Idx.idxCap
    · rw [if_pos hc] at hrun
      have he : ((lst.store.internName v).2,
          ({ lst with store := (lst.store.internName v).1 } : AState)) = (h, lst') :=
        Except.ok.inj hrun
      simp only [Prod.mk.injEq] at he
      exact ⟨fun _ => hc, he.1.symm, he.2.symm⟩
    · rw [if_neg hc] at hrun
      rw [arena_fail_run] at hrun; exact absurd hrun (by simp)

theorem StoreWF.nsWF' {st : EStore} (h : StoreWF st) : NStoreWF st.ns := by
  obtain ⟨rk, hw⟩ := h; exact hw.nsWF

theorem internNNode_run_view {lst lst' : AState} {v : NNodeView} {h : NIdx}
    (hwf : StoreWF lst.store) (hview : lst.store.ns.ViewOK v)
    (hrun : (Arena.internNNode v).run lst = .ok (h, lst')) :
    lst'.store.ns.view h = some v ∧ StoreWF lst'.store ∧ Ext lst.store lst'.store := by
  obtain ⟨hcap, rfl, rfl⟩ := internNNode_run_inv hrun
  refine ⟨?_, internName_storeWF hwf hview hcap, EStore.internName_ext _ _⟩
  cases hf : lst.store.ns.find? v with
  | some i =>
    rw [EStore_internName_of_find hf]
    exact NStore.view_of_find (StoreWF.nsWF' hwf) hf
  | none => exact NStore.intern_view_spec (StoreWF.nsWF' hwf) hview (hcap hf)

theorem internName_run_denote : ∀ (n : ConLeche.Name) {lst lst' : AState} {h : NIdx},
    StoreWF lst.store →
    (Arena.internName n).run lst = .ok (h, lst') →
    denoteN lst'.store.ns h = some n ∧ StoreWF lst'.store ∧ Ext lst.store lst'.store := by
  intro n
  induction n with
  | anonymous =>
    intro lst lst' h hwf hrun
    obtain ⟨hv, hwf', hext⟩ :=
      internNNode_run_view hwf (by intro c hc; simp [NNodeView.children] at hc) hrun
    refine ⟨?_, hwf', hext⟩
    obtain ⟨rk, hw⟩ := (StoreWF.nsWF' hwf')
    rw [denoteN_unfold hw hv]; rfl
  | str p s ih =>
    intro lst lst' h hwf hrun
    rw [Arena.internName, StateT.run_bind] at hrun
    cases hx : (Arena.internName p).run lst with
    | error e => rw [hx] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
    | ok q =>
      obtain ⟨hp, lst1⟩ := q
      rw [hx] at hrun
      obtain ⟨hdp, hwf1, hext1⟩ := ih hwf hx
      replace hrun : StateT.run (Arena.internNNode (NNodeView.str hp s)) lst1
          = Except.ok (h, lst') := hrun
      obtain ⟨v1, hv1⟩ := denoteN_view hdp
      have hvo : lst1.store.ns.ViewOK (NNodeView.str hp s) := by
        intro c hc
        simp only [NNodeView.children, List.mem_singleton] at hc
        subst hc; rw [hv1]; rfl
      obtain ⟨hv, hwf', hext⟩ := internNNode_run_view hwf1 hvo hrun
      refine ⟨?_, hwf', hext1.trans hext⟩
      obtain ⟨rk, hw⟩ := StoreWF.nsWF' hwf'
      rw [denoteN_unfold hw hv]
      show (denoteN lst'.store.ns hp).map _ = _
      rw [show denoteN lst'.store.ns hp = some p from hext.lss.ls.ns hp p hdp]
      rfl
  | num p k ih =>
    intro lst lst' h hwf hrun
    rw [Arena.internName, StateT.run_bind] at hrun
    cases hx : (Arena.internName p).run lst with
    | error e => rw [hx] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
    | ok q =>
      obtain ⟨hp, lst1⟩ := q
      rw [hx] at hrun
      obtain ⟨hdp, hwf1, hext1⟩ := ih hwf hx
      replace hrun : StateT.run (Arena.internNNode (NNodeView.num hp k)) lst1
          = Except.ok (h, lst') := hrun
      obtain ⟨v1, hv1⟩ := denoteN_view hdp
      have hvo : lst1.store.ns.ViewOK (NNodeView.num hp k) := by
        intro c hc
        simp only [NNodeView.children, List.mem_singleton] at hc
        subst hc; rw [hv1]; rfl
      obtain ⟨hv, hwf', hext⟩ := internNNode_run_view hwf1 hvo hrun
      refine ⟨?_, hwf', hext1.trans hext⟩
      obtain ⟨rk, hw⟩ := StoreWF.nsWF' hwf'
      rw [denoteN_unfold hw hv]
      show (denoteN lst'.store.ns hp).map _ = _
      rw [show denoteN lst'.store.ns hp = some p from hext.lss.ls.ns hp p hdp]
      rfl


theorem StoreWF.lsWF' {st : EStore} (h : StoreWF st) : LStoreWF st.ls := by
  obtain ⟨rk, hw⟩ := h; exact hw.lsWF

theorem StoreWF.lssWF' {st : EStore} (h : StoreWF st) : LsStoreWF st.lss := by
  obtain ⟨rk, hw⟩ := h; exact hw.lssWF

theorem internLNode_run_inv {lst lst' : AState} {v : LNodeView} {h : LIdx}
    (hrun : (Arena.internLNode v).run lst = .ok (h, lst')) :
    LCapAt lst.store.ls v ∧ h = (lst.store.internLevel v).2 ∧
      lst' = { lst with store := (lst.store.internLevel v).1 } := by
  simp only [Arena.internLNode, run_get_bind] at hrun
  cases hf : lst.store.ls.find? v with
  | some i =>
    simp only [hf] at hrun
    rw [EStore_internLevel_of_find hf]
    have he : (i, lst) = (h, lst') := Except.ok.inj hrun
    simp only [Prod.mk.injEq] at he
    exact ⟨LCapAt.of_find_ne (by rw [hf]; simp), he.1.symm, he.2.symm⟩
  | none =>
    simp only [hf] at hrun
    by_cases hc : (if lst.store.ls.scratchOn = true then lst.store.ls.scr.sizeOf v
        else lst.store.ls.pers.sizeOf v) < Idx.idxCap
    · rw [if_pos hc] at hrun
      have he : ((lst.store.internLevel v).2,
          ({ lst with store := (lst.store.internLevel v).1 } : AState)) = (h, lst') :=
        Except.ok.inj hrun
      simp only [Prod.mk.injEq] at he
      exact ⟨fun _ => hc, he.1.symm, he.2.symm⟩
    · rw [if_neg hc] at hrun
      rw [arena_fail_run] at hrun; exact absurd hrun (by simp)

theorem internLNode_run_view {lst lst' : AState} {v : LNodeView} {h : LIdx}
    (hwf : StoreWF lst.store) (hview : lst.store.ls.ViewOK v)
    (hrun : (Arena.internLNode v).run lst = .ok (h, lst')) :
    lst'.store.ls.view h = some v ∧ StoreWF lst'.store ∧ Ext lst.store lst'.store := by
  obtain ⟨hcap, rfl, rfl⟩ := internLNode_run_inv hrun
  refine ⟨?_, internLevel_storeWF hwf hview hcap, EStore.internLevel_ext _ _⟩
  cases hf : lst.store.ls.find? v with
  | some i =>
    rw [EStore_internLevel_of_find hf]
    exact LStore.view_of_find (StoreWF.lsWF' hwf) hf
  | none => exact LStore.intern_view_spec (StoreWF.lsWF' hwf) hview (hcap hf)

theorem internLsNode_run_inv {lst lst' : AState} {v : LsNodeView} {h : LsIdx}
    (hrun : (Arena.internLsNode v).run lst = .ok (h, lst')) :
    LsCapAt lst.store.lss v ∧ h = (lst.store.internLevels v).2 ∧
      lst' = { lst with store := (lst.store.internLevels v).1 } := by
  simp only [Arena.internLsNode, run_get_bind] at hrun
  cases hf : lst.store.lss.find? v with
  | some i =>
    simp only [hf] at hrun
    rw [EStore_internLevels_of_find hf]
    have he : (i, lst) = (h, lst') := Except.ok.inj hrun
    simp only [Prod.mk.injEq] at he
    exact ⟨LsCapAt.of_find_ne (by rw [hf]; simp), he.1.symm, he.2.symm⟩
  | none =>
    simp only [hf] at hrun
    by_cases hc : (if lst.store.lss.scratchOn = true then lst.store.lss.scr.sizeOf v
        else lst.store.lss.pers.sizeOf v) < Idx.idxCap
    · rw [if_pos hc] at hrun
      have he : ((lst.store.internLevels v).2,
          ({ lst with store := (lst.store.internLevels v).1 } : AState)) = (h, lst') :=
        Except.ok.inj hrun
      simp only [Prod.mk.injEq] at he
      exact ⟨fun _ => hc, he.1.symm, he.2.symm⟩
    · rw [if_neg hc] at hrun
      rw [arena_fail_run] at hrun; exact absurd hrun (by simp)

theorem internLsNode_run_view {lst lst' : AState} {v : LsNodeView} {h : LsIdx}
    (hwf : StoreWF lst.store) (hview : lst.store.lss.ViewOK v)
    (hrun : (Arena.internLsNode v).run lst = .ok (h, lst')) :
    lst'.store.lss.view h = some v ∧ StoreWF lst'.store ∧ Ext lst.store lst'.store := by
  obtain ⟨hcap, rfl, rfl⟩ := internLsNode_run_inv hrun
  refine ⟨?_, internLevels_storeWF hwf hview hcap, EStore.internLevels_ext _ _⟩
  cases hf : lst.store.lss.find? v with
  | some i =>
    rw [EStore_internLevels_of_find hf]
    exact LsStore.view_of_find (StoreWF.lssWF' hwf) hf
  | none => exact LsStore.intern_view_spec (StoreWF.lssWF' hwf) hview (hcap hf)

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_n_node_run₀`.
 `arena::monad::intern_n_node` against `Arena.internNNode`. -/
theorem intern_n_node_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (v : arena.store.NNodeView) (hvwf : NNodeViewWF v)
    (hview : lst.store.ns.ViewOK (absNNodeView v)) {o}
    (hrun : arena.monad.intern_n_node pers st v = ok o) :
    Sim absNIdx (fun _ => True) pers lst o (Arena.internNNode (absNNodeView v)) :=
  (intern_n_node_run₀ hrel.to₀ hinv v hvwf hrun).toSim
    (fun _ _ hx => (internNNode_run_view hrel.storeWF hview hx).2) (fun _ _ => trivial)

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_l_node_run₀`.
 `arena::monad::intern_l_node` against `Arena.internLNode`. -/
theorem intern_l_node_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (v : arena.store.LNodeView)
    (hview : lst.store.ls.ViewOK (absLNodeView v)) {o}
    (hrun : arena.monad.intern_l_node pers st v = ok o) :
    Sim absLIdx (fun _ => True) pers lst o (Arena.internLNode (absLNodeView v)) :=
  (intern_l_node_run₀ hrel.to₀ hinv v hrun).toSim
    (fun _ _ hx => (internLNode_run_view hrel.storeWF hview hx).2) (fun _ _ => trivial)

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_ls_node_run₀`.
 `arena::monad::intern_ls_node` against `Arena.internLsNode`. -/
theorem intern_ls_node_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    (v : alloc.vec.Vec arena.handle.LIdx)
    (hview : lst.store.lss.ViewOK (absLsNodeView v)) {o}
    (hrun : arena.monad.intern_ls_node pers st v = ok o) :
    Sim absLsIdx (fun _ => True) pers lst o
      (Arena.internLsNode (absLsNodeView v)) :=
  (intern_ls_node_run₀ hrel.to₀ hinv v hrun).toSim
    (fun _ _ hx => (internLsNode_run_view hrel.storeWF hview hx).2) (fun _ _ => trivial)


theorem internLevel_run_denote : ∀ (u : ConLeche.Level) {lst lst' : AState} {h : LIdx},
    StoreWF lst.store →
    (Arena.internLevel u).run lst = .ok (h, lst') →
    denoteL lst'.store.ls h = some u ∧ StoreWF lst'.store ∧ Ext lst.store lst'.store := by
  intro u
  induction u with
  | zero =>
    intro lst lst' h hwf hrun
    have hvo : lst.store.ls.ViewOK (LNodeView.zero) := by
      constructor
      · intro c hc; simp [LNodeView.lchildren] at hc
      · intro c hc; simp [LNodeView.nchildren] at hc
    obtain ⟨hv, hwf', hext⟩ := internLNode_run_view hwf hvo hrun
    refine ⟨?_, hwf', hext⟩
    obtain ⟨rk, hw⟩ := StoreWF.lsWF' hwf'
    rw [denoteL_unfold hw hv]; rfl
  | succ a ih =>
    intro lst lst' h hwf hrun
    rw [Arena.internLevel, StateT.run_bind] at hrun
    cases hx : (Arena.internLevel a).run lst with
    | error e => rw [hx] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
    | ok q =>
      obtain ⟨ha, lst1⟩ := q
      rw [hx] at hrun
      obtain ⟨hda, hwf1, hext1⟩ := ih hwf hx
      replace hrun : StateT.run (Arena.internLNode (LNodeView.succ ha)) lst1
          = Except.ok (h, lst') := hrun
      obtain ⟨v1, hv1⟩ := denoteL_view hda
      have hvo : lst1.store.ls.ViewOK (LNodeView.succ ha) := by
        constructor
        · intro c hc
          simp only [LNodeView.lchildren, List.mem_singleton] at hc
          subst hc; rw [hv1]; rfl
        · intro c hc; simp [LNodeView.nchildren] at hc
      obtain ⟨hv, hwf', hext⟩ := internLNode_run_view hwf1 hvo hrun
      refine ⟨?_, hwf', hext1.trans hext⟩
      obtain ⟨rk, hw⟩ := StoreWF.lsWF' hwf'
      rw [denoteL_unfold hw hv]
      show (denoteL lst'.store.ls ha).map _ = _
      rw [show denoteL lst'.store.ls ha = some a from hext.lss.ls.lvl ha a hda]
      rfl
  | max a b iha ihb =>
    intro lst lst' h hwf hrun
    rw [Arena.internLevel, StateT.run_bind] at hrun
    cases hx : (Arena.internLevel a).run lst with
    | error e => rw [hx] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
    | ok q =>
      obtain ⟨ha, lst1⟩ := q
      rw [hx] at hrun
      obtain ⟨hda, hwf1, hext1⟩ := iha hwf hx
      replace hrun : ((Arena.internLevel b) >>= fun hb =>
          Arena.internLNode (LNodeView.max ha hb)).run lst1 = Except.ok (h, lst') := hrun
      rw [StateT.run_bind] at hrun
      cases hy : (Arena.internLevel b).run lst1 with
      | error e => rw [hy] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
      | ok q2 =>
        obtain ⟨hb, lst2⟩ := q2
        rw [hy] at hrun
        obtain ⟨hdb, hwf2, hext2⟩ := ihb hwf1 hy
        replace hrun : StateT.run (Arena.internLNode (LNodeView.max ha hb)) lst2
            = Except.ok (h, lst') := hrun
        have hda2 : denoteL lst2.store.ls ha = some a := hext2.lss.ls.lvl ha a hda
        obtain ⟨v1, hv1⟩ := denoteL_view hda2
        obtain ⟨v2, hv2⟩ := denoteL_view hdb
        have hvo : lst2.store.ls.ViewOK (LNodeView.max ha hb) := by
          constructor
          · intro c hc
            simp only [LNodeView.lchildren, List.mem_cons,
              List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · rw [hv1]; rfl
            · rw [hv2]; rfl
          · intro c hc; simp [LNodeView.nchildren] at hc
        obtain ⟨hv, hwf', hext⟩ := internLNode_run_view hwf2 hvo hrun
        refine ⟨?_, hwf', (hext1.trans hext2).trans hext⟩
        obtain ⟨rk, hw⟩ := StoreWF.lsWF' hwf'
        rw [denoteL_unfold hw hv]
        show opt2 ConLeche.Level.max (denoteL lst'.store.ls ha) (denoteL lst'.store.ls hb) = _
        rw [show denoteL lst'.store.ls ha = some a from hext.lss.ls.lvl ha a hda2,
          show denoteL lst'.store.ls hb = some b from hext.lss.ls.lvl hb b hdb]
        rfl
  | imax a b iha ihb =>
    intro lst lst' h hwf hrun
    rw [Arena.internLevel, StateT.run_bind] at hrun
    cases hx : (Arena.internLevel a).run lst with
    | error e => rw [hx] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
    | ok q =>
      obtain ⟨ha, lst1⟩ := q
      rw [hx] at hrun
      obtain ⟨hda, hwf1, hext1⟩ := iha hwf hx
      replace hrun : ((Arena.internLevel b) >>= fun hb =>
          Arena.internLNode (LNodeView.imax ha hb)).run lst1 = Except.ok (h, lst') := hrun
      rw [StateT.run_bind] at hrun
      cases hy : (Arena.internLevel b).run lst1 with
      | error e => rw [hy] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
      | ok q2 =>
        obtain ⟨hb, lst2⟩ := q2
        rw [hy] at hrun
        obtain ⟨hdb, hwf2, hext2⟩ := ihb hwf1 hy
        replace hrun : StateT.run (Arena.internLNode (LNodeView.imax ha hb)) lst2
            = Except.ok (h, lst') := hrun
        have hda2 : denoteL lst2.store.ls ha = some a := hext2.lss.ls.lvl ha a hda
        obtain ⟨v1, hv1⟩ := denoteL_view hda2
        obtain ⟨v2, hv2⟩ := denoteL_view hdb
        have hvo : lst2.store.ls.ViewOK (LNodeView.imax ha hb) := by
          constructor
          · intro c hc
            simp only [LNodeView.lchildren, List.mem_cons,
              List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · rw [hv1]; rfl
            · rw [hv2]; rfl
          · intro c hc; simp [LNodeView.nchildren] at hc
        obtain ⟨hv, hwf', hext⟩ := internLNode_run_view hwf2 hvo hrun
        refine ⟨?_, hwf', (hext1.trans hext2).trans hext⟩
        obtain ⟨rk, hw⟩ := StoreWF.lsWF' hwf'
        rw [denoteL_unfold hw hv]
        show opt2 ConLeche.Level.imax (denoteL lst'.store.ls ha) (denoteL lst'.store.ls hb) = _
        rw [show denoteL lst'.store.ls ha = some a from hext.lss.ls.lvl ha a hda2,
          show denoteL lst'.store.ls hb = some b from hext.lss.ls.lvl hb b hdb]
        rfl
  | param n =>
    intro lst lst' h hwf hrun
    rw [Arena.internLevel, StateT.run_bind] at hrun
    cases hx : (Arena.internName n).run lst with
    | error e => rw [hx] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
    | ok q =>
      obtain ⟨hn, lst1⟩ := q
      rw [hx] at hrun
      obtain ⟨hdn, hwf1, hext1⟩ := internName_run_denote n hwf hx
      replace hrun : StateT.run (Arena.internLNode (LNodeView.param hn)) lst1
          = Except.ok (h, lst') := hrun
      obtain ⟨v1, hv1⟩ := denoteN_view hdn
      have hvo : lst1.store.ls.ViewOK (LNodeView.param hn) := by
        constructor
        · intro c hc; simp [LNodeView.lchildren] at hc
        · intro c hc
          simp only [LNodeView.nchildren, List.mem_singleton] at hc
          subst hc
          show (lst1.store.ns.view _).isSome = true
          rw [hv1]; rfl
      obtain ⟨hv, hwf', hext⟩ := internLNode_run_view hwf1 hvo hrun
      refine ⟨?_, hwf', hext1.trans hext⟩
      obtain ⟨rk, hw⟩ := StoreWF.lsWF' hwf'
      rw [denoteL_unfold hw hv]
      show (denoteN lst'.store.ls.ns hn).map _ = _
      rw [show denoteN lst'.store.ls.ns hn = some n from hext.lss.ls.ns hn n hdn]
      rfl


theorem denoteLList_isSome {st : LStore} : ∀ {hs : List LIdx} {us : List ConLeche.Level},
    denoteLList st hs = some us → ∀ c ∈ hs, (st.view c).isSome = true := by
  intro hs
  induction hs with
  | nil => intro us _ c hc; simp at hc
  | cons a rest ih =>
    intro us h c hc
    simp only [denoteLList] at h
    cases hda : denoteL st a with
    | none => rw [hda] at h; simp [opt2] at h
    | some x =>
      cases hdas : denoteLList st rest with
      | none => rw [hda, hdas] at h; simp [opt2] at h
      | some xs =>
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · obtain ⟨v, hv⟩ := denoteL_view hda; rw [hv]; rfl
        · exact ih hdas c hc

theorem denoteLList_of_ext {a b : LStore} (h : LExt a b) :
    ∀ {hs : List LIdx} {us : List ConLeche.Level},
      denoteLList a hs = some us → denoteLList b hs = some us := by
  intro hs
  induction hs with
  | nil => intro us hu; exact hu
  | cons c cs ih =>
    intro us hu
    simp only [denoteLList] at hu ⊢
    cases hdc : denoteL a c with
    | none => rw [hdc] at hu; simp [opt2] at hu
    | some x =>
      cases hdcs : denoteLList a cs with
      | none => rw [hdc, hdcs] at hu; simp [opt2] at hu
      | some xs =>
        rw [hdc, hdcs] at hu
        rw [h.lvl c x hdc, ih hdcs]
        exact hu

theorem internLevelList_run_denote :
    ∀ (us : List ConLeche.Level) {lst lst' : AState} {hs : List LIdx},
      StoreWF lst.store →
      (Arena.internLevelList us).run lst = .ok (hs, lst') →
      denoteLList lst'.store.ls hs = some us ∧ StoreWF lst'.store ∧
        Ext lst.store lst'.store := by
  intro us
  induction us with
  | nil =>
    intro lst lst' hs hwf hrun
    have he : (([] : List LIdx), lst) = (hs, lst') := Except.ok.inj hrun
    simp only [Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := he
    subst h1; subst h2
    exact ⟨rfl, hwf, Ext.refl _⟩
  | cons u us ih =>
    intro lst lst' hs hwf hrun
    rw [Arena.internLevelList, StateT.run_bind] at hrun
    cases hx : (Arena.internLevel u).run lst with
    | error e => rw [hx] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
    | ok q =>
      obtain ⟨hu, lst1⟩ := q
      rw [hx] at hrun
      obtain ⟨hdu, hwf1, hext1⟩ := internLevel_run_denote u hwf hx
      replace hrun : ((Arena.internLevelList us) >>= fun hus =>
          (pure (hu :: hus) : AM (List LIdx))).run lst1 = Except.ok (hs, lst') := hrun
      rw [StateT.run_bind] at hrun
      cases hy : (Arena.internLevelList us).run lst1 with
      | error e => rw [hy] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
      | ok q2 =>
        obtain ⟨hus, lst2⟩ := q2
        rw [hy] at hrun
        obtain ⟨hdus, hwf2, hext2⟩ := ih hwf1 hy
        have he : ((hu :: hus), lst2) = (hs, lst') := Except.ok.inj hrun
        simp only [Prod.mk.injEq] at he
        obtain ⟨h1, h2⟩ := he
        subst h1; subst h2
        refine ⟨?_, hwf2, hext1.trans hext2⟩
        simp only [denoteLList]
        rw [show denoteL lst2.store.ls hu = some u from hext2.lss.ls.lvl hu u hdu, hdus]
        rfl

theorem internLevels_run_denote (us : List ConLeche.Level) {lst lst' : AState}
    {h : LsIdx} (hwf : StoreWF lst.store)
    (hrun : (Arena.internLevels us).run lst = .ok (h, lst')) :
    denoteLs lst'.store.lss h = some us ∧ StoreWF lst'.store ∧
      Ext lst.store lst'.store := by
  rw [Arena.internLevels, StateT.run_bind] at hrun
  cases hx : (Arena.internLevelList us).run lst with
  | error e => rw [hx] at hrun; exact absurd hrun (by simp [Bind.bind, Except.bind])
  | ok q =>
    obtain ⟨hs, lst1⟩ := q
    rw [hx] at hrun
    obtain ⟨hdus, hwf1, hext1⟩ := internLevelList_run_denote us hwf hx
    replace hrun : StateT.run (Arena.internLsNode hs) lst1 = Except.ok (h, lst') := hrun
    have hvo : lst1.store.lss.ViewOK hs := denoteLList_isSome hdus
    obtain ⟨hv, hwf', hext⟩ := internLsNode_run_view hwf1 hvo hrun
    refine ⟨?_, hwf', hext1.trans hext⟩
    rw [denoteLs_unfold hv]
    exact denoteLList_of_ext hext.lss.ls hdus

/-! ### The tier flags, unmoved

The Rust `EStore`, `LsStore`, `LStore` and `NStore` each carry their own
`shared_on`/`scratch_on` (round 2 §5), and an intern touches none of them: every
store a `*::intern*` returns is `self` or `{ self with pers := … }` or
`{ self with scr := … }`.  (This once carried `intern_{n,l,ls}_node_run`'s
frozen-tier side condition across a walk; that condition is retired, task
#97-P5-Unfreeze.) -/

/-- The four stores' tier flags, unmoved. -/
structure FlagsEq (rs rs' : arena.store.EStore) : Prop where
  eSh : rs'.shared_on = rs.shared_on
  eScr : rs'.scratch_on = rs.scratch_on
  lssSh : rs'.lss.shared_on = rs.lss.shared_on
  lssScr : rs'.lss.scratch_on = rs.lss.scratch_on
  lsSh : rs'.lss.ls.shared_on = rs.lss.ls.shared_on
  lsScr : rs'.lss.ls.scratch_on = rs.lss.ls.scratch_on
  nsSh : rs'.lss.ls.ns.shared_on = rs.lss.ls.ns.shared_on
  nsScr : rs'.lss.ls.ns.scratch_on = rs.lss.ls.ns.scratch_on

theorem FlagsEq.refl (rs : arena.store.EStore) : FlagsEq rs rs :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FlagsEq.trans {a b c : arena.store.EStore} (h1 : FlagsEq a b)
    (h2 : FlagsEq b c) : FlagsEq a c :=
  ⟨h2.eSh.trans h1.eSh, h2.eScr.trans h1.eScr,
   h2.lssSh.trans h1.lssSh, h2.lssScr.trans h1.lssScr,
   h2.lsSh.trans h1.lsSh, h2.lsScr.trans h1.lsScr,
   h2.nsSh.trans h1.nsSh, h2.nsScr.trans h1.nsScr⟩

theorem nstore_intern_other_flags {pers rs v r rs'}
    (h : arena.store.NStore.intern_other rs pers v = ok (r, rs')) :
    rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on := by
  rw [arena.store.NStore.intern_other] at h
  repeat' (first
    | exact ⟨rfl, rfl⟩
    | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h)
    | split at h
    | (obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h :
        _ ∧ _)))

theorem nstore_intern_str_flags {pers rs k d r rs'}
    (h : arena.store.NStore.intern_str rs pers k d = ok (r, rs')) :
    rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on := by
  rw [arena.store.NStore.intern_str] at h
  repeat' (first
    | exact ⟨rfl, rfl⟩
    | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h)
    | split at h
    | (obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h :
        _ ∧ _)))

theorem nstore_intern_flags {pers rs v r rs'}
    (h : arena.store.NStore.intern rs pers v = ok (r, rs')) :
    rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on := by
  cases v with
  | Anonymous =>
    simp only [arena.store.NStore.intern] at h; exact nstore_intern_other_flags h
  | Str p s =>
    simp only [arena.store.NStore.intern] at h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact nstore_intern_str_flags h
  | Num p n =>
    simp only [arena.store.NStore.intern] at h; exact nstore_intern_other_flags h

theorem lstore_intern_flags {pers rs v r rs'}
    (h : arena.store.LStore.intern rs pers v = ok (r, rs')) :
    rs'.ns = rs.ns ∧ rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on := by
  rw [arena.store.LStore.intern] at h
  repeat' (first
    | exact ⟨rfl, rfl, rfl⟩
    | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h)
    | split at h
    | (obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h :
        _ ∧ _)))

theorem lsstore_intern_flags {pers rs v r rs'}
    (h : arena.store.LsStore.intern rs pers v = ok (r, rs')) :
    rs'.ls = rs.ls ∧ rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on := by
  rw [arena.store.LsStore.intern] at h
  repeat' (first
    | exact ⟨rfl, rfl, rfl⟩
    | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h)
    | split at h
    | (obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h :
        _ ∧ _)))


theorem intern_n_node_flags {pers st v o}
    (h : arena.monad.intern_n_node pers st v = ok o) : FlagsEq st.store o.2.store := by
  rw [arena.monad.intern_n_node] at h
  obtain ⟨p, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r, e⟩ := p
  obtain rfl : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective h
  rw [arena.store.EStore.intern_name] at h1
  obtain ⟨p1, h2, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
  obtain ⟨r1, lss1⟩ := p1
  obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h1 : _ ∧ _)
  rw [arena.store.LsStore.intern_name] at h2
  obtain ⟨p2, h3, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
  obtain ⟨r2, l2⟩ := p2
  obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h2 : _ ∧ _)
  rw [arena.store.LStore.intern_name] at h3
  obtain ⟨p3, h4, h3⟩ := ConRon.Refine.bind_eq_ok_iff.mp h3
  obtain ⟨r3, n3⟩ := p3
  obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h3 : _ ∧ _)
  obtain ⟨hsh, hscr⟩ := nstore_intern_flags h4
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsh, hscr⟩

theorem intern_l_node_flags {pers st v o}
    (h : arena.monad.intern_l_node pers st v = ok o) : FlagsEq st.store o.2.store := by
  rw [arena.monad.intern_l_node] at h
  obtain ⟨p, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r, e⟩ := p
  obtain rfl : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective h
  rw [arena.store.EStore.intern_level] at h1
  obtain ⟨p1, h2, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
  obtain ⟨r1, lss1⟩ := p1
  obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h1 : _ ∧ _)
  rw [arena.store.LsStore.intern_level] at h2
  obtain ⟨p2, h3, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
  obtain ⟨r2, l2⟩ := p2
  obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h2 : _ ∧ _)
  obtain ⟨hns, hsh, hscr⟩ := lstore_intern_flags h3
  exact ⟨rfl, rfl, rfl, rfl, hsh, hscr, by rw [hns], by rw [hns]⟩

theorem intern_ls_node_flags {pers st v o}
    (h : arena.monad.intern_ls_node pers st v = ok o) : FlagsEq st.store o.2.store := by
  rw [arena.monad.intern_ls_node] at h
  obtain ⟨p, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r, e⟩ := p
  obtain rfl : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective h
  rw [arena.store.EStore.intern_levels] at h1
  obtain ⟨p1, h2, h1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h1
  obtain ⟨r1, lss1⟩ := p1
  obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h1 : _ ∧ _)
  obtain ⟨hls, hsh, hscr⟩ := lsstore_intern_flags h2
  exact ⟨rfl, rfl, hsh, hscr, by rw [hls], by rw [hls], by rw [hls], by rw [hls]⟩




/-- A twin bind whose first step is known: `run` of `do let y ← x; f y` at a
state where `x` answers `v` is `run` of `f v` at the state it answered in. -/
theorem run_bind_ok {β δ : Type} {x : AM β} {lst lst1 : AState} {v : β}
    (h : x.run lst = .ok (v, lst1)) (f : β → AM δ) :
    (do let y ← x; f y).run lst = (f v).run lst1 := by
  rw [StateT.run_bind, h]; rfl

/-! ### Composing a walk's steps

`Refine2/ExprOps/Mut.lean` has both of these (`aout_err_bind_v`,
`aout_rebase`) under its own names; they belong in `Refine2/Shape.lean` beside
`AOut`, and they are here — one tier lower than their first use — because
`Shape.lean` was not this task's lane.  The names are `AOut.*` so that the two
copies do not collide. -/

/-- The error arm travels through a bind. -/
theorem AOut.errBind {β γ δ : Type} {A : γ → β} {C : Type} {AC : C → δ}
    {e : kernel.core_types.CheckError} {pers : arena.store.PersTier}
    {lstA lstB : AState} {stA stB : arena.monad.AState}
    {x : AM β} {f : β → AM δ}
    (h : AOut A (fun _ => True) pers lstA (.Err e) stA (x.run lstA)) :
    AOut AC (fun _ => True) pers lstB (.Err e) stB
      ((do let v ← x; f v).run lstA) := by
  refine AOut.err ?_
  rw [StateT.run_bind]
  exact AErrSim.bind h _

/-- An outcome measured from a later state is one measured from an earlier
one, `Ext` composed. -/
theorem AOut.rebase {γ δ : Type} {AC : γ → δ} {pers : arena.store.PersTier}
    {lst lst1 : AState} {st2 : arena.monad.AState}
    {o : core.result.Result γ kernel.core_types.CheckError}
    {y : Except Arena.CheckError (δ × AState)}
    (hext : Ext lst.store lst1.store)
    (h : AOut AC (fun _ => True) pers lst1 o st2 y) :
    AOut AC (fun _ => True) pers lst o st2 y := by
  cases o with
  | Err e => exact h
  | Ok c =>
    obtain ⟨lst2, hy, hrel2, hinv2, hext2, -⟩ := h
    exact AOut.ok hy hrel2 hinv2 (Ext.trans hext hext2) trivial

/-- The error arm travels through a bind (the lockstep form). -/
theorem AOut₀.errBind {β γ δ : Type} {A : γ → β} {C : Type} {AC : C → δ}
    {e : kernel.core_types.CheckError} {pers : arena.store.PersTier}
    {lstA : AState} {stA stB : arena.monad.AState}
    {x : AM β} {f : β → AM δ}
    (h : AOut₀ A pers (.Err e) stA (x.run lstA)) :
    AOut₀ AC pers (.Err e) stB ((do let v ← x; f v).run lstA) := by
  refine AOut₀.err ?_
  rw [StateT.run_bind]
  exact AErrSim.bind h _


theorem intern_name_run'₀ :
    ∀ (n : kernel.name.Name) (_hwf : ConRon.Refine.NameWF n)
      {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState} {o},
      AStateRel₀ pers st lst → AStateInv pers st →
      arena.monad.intern_name pers st n = ok o →
      Sim₀ absNIdx pers lst o
        (Arena.internName (ConRon.Refine.absName n)) ∧
      FlagsEq st.store o.2.store := by
  intro n hwf
  induction n, hwf using ConRon.Refine.NameWF.ind_node with
  | anonymous hh w =>
    intro pers st lst o hrel hinv hrun
    rw [arena.monad.intern_name, ConRon.Refine.bind_arc_deref] at hrun
    replace hrun : arena.monad.intern_n_node pers st arena.store.NNodeView.Anonymous
        = ok o := hrun
    refine ⟨?_, intern_n_node_flags hrun⟩
    have hsim := intern_n_node_run₀ hrel hinv arena.store.NNodeView.Anonymous
      trivial hrun
    exact hsim
  | str hh pre s w ih =>
    intro pers st lst o hrel hinv hrun
    rw [arena.monad.intern_name, ConRon.Refine.bind_arc_deref] at hrun
    replace hrun : (do
        let (r, st1) ← arena.monad.intern_name pers st pre
        match r with
        | .Ok hp => do
            let v ← kernel.expr.str_copy s
            arena.monad.intern_n_node pers st1 (arena.store.NNodeView.Str hp v)
        | .Err _ => ok (r, st1)) = ok o := hrun
    obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r1, st1⟩ := p1
    obtain ⟨hsim1, hfl1⟩ := ih w.str_kids.1 hrel hinv hp1
    cases hr : r1 with
    | Err e =>
      simp only [hr] at hrun
      obtain rfl : ((core.result.Result.Err e :
          core.result.Result arena.handle.NIdx kernel.core_types.CheckError), st1) = o :=
        Result.ok_injective hrun
      refine ⟨?_, hfl1⟩
      show AOut₀ absNIdx pers _ _ _
      rw [show ConRon.Refine.absName
            (kernel.name.Name.mk (kernel.name.NameNode.mk hh (.Str pre s)))
          = ConLeche.Name.str (ConRon.Refine.absName pre) (ConRon.Refine.absString s)
        from rfl, Arena.internName]
      exact AOut₀.errBind (hr ▸ hsim1)
    | Ok hp =>
      simp only [hr] at hrun
      obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [ConRon.Refine.Expr.str_copy_eq hv] at hrun
      obtain ⟨lst1, hy1, hrel1, hinv1⟩ :=
        (hr ▸ hsim1 : AOut₀ _ _ (.Ok hp) _ _)
      have hsim2 := intern_n_node_run₀ hrel1 hinv1
        (arena.store.NNodeView.Str hp s) w.str_kids.2 hrun
      refine ⟨?_, hfl1.trans (intern_n_node_flags hrun)⟩
      show AOut₀ absNIdx pers _ _ _
      rw [show ConRon.Refine.absName
            (kernel.name.Name.mk (kernel.name.NameNode.mk hh (.Str pre s)))
          = ConLeche.Name.str (ConRon.Refine.absName pre) (ConRon.Refine.absString s)
        from rfl, Arena.internName, run_bind_ok hy1]
      exact hsim2
  | num hh pre m w ih =>
    intro pers st lst o hrel hinv hrun
    rw [arena.monad.intern_name, ConRon.Refine.bind_arc_deref] at hrun
    replace hrun : (do
        let (r, st1) ← arena.monad.intern_name pers st pre
        match r with
        | .Ok hp => arena.monad.intern_n_node pers st1 (arena.store.NNodeView.Num hp m)
        | .Err _ => ok (r, st1)) = ok o := hrun
    obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r1, st1⟩ := p1
    obtain ⟨hsim1, hfl1⟩ := ih w.num_kids hrel hinv hp1
    cases hr : r1 with
    | Err e =>
      simp only [hr] at hrun
      obtain rfl : ((core.result.Result.Err e :
          core.result.Result arena.handle.NIdx kernel.core_types.CheckError), st1) = o :=
        Result.ok_injective hrun
      refine ⟨?_, hfl1⟩
      show AOut₀ absNIdx pers _ _ _
      rw [show ConRon.Refine.absName
            (kernel.name.Name.mk (kernel.name.NameNode.mk hh (.Num pre m)))
          = ConLeche.Name.num (ConRon.Refine.absName pre) m.val from rfl, Arena.internName]
      exact AOut₀.errBind (hr ▸ hsim1)
    | Ok hp =>
      simp only [hr] at hrun
      obtain ⟨lst1, hy1, hrel1, hinv1⟩ :=
        (hr ▸ hsim1 : AOut₀ _ _ (.Ok hp) _ _)
      have hsim2 := intern_n_node_run₀ hrel1 hinv1
        (arena.store.NNodeView.Num hp m) trivial hrun
      refine ⟨?_, hfl1.trans (intern_n_node_flags hrun)⟩
      show AOut₀ absNIdx pers _ _ _
      rw [show ConRon.Refine.absName
            (kernel.name.Name.mk (kernel.name.NameNode.mk hh (.Num pre m)))
          = ConLeche.Name.num (ConRon.Refine.absName pre) m.val from rfl,
        Arena.internName, run_bind_ok hy1]
      exact hsim2

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_name_run'₀`. -/
theorem intern_name_run' :
    ∀ (n : kernel.name.Name) (_hwf : ConRon.Refine.NameWF n)
      {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState} {o},
      AStateRel pers st lst → AStateInv pers st →
      arena.monad.intern_name pers st n = ok o →
      Sim absNIdx (fun _ => True) pers lst o
        (Arena.internName (ConRon.Refine.absName n)) ∧
      FlagsEq st.store o.2.store := by
  intro n hwf pers st lst o hrel hinv hrun
  obtain ⟨h1, h2⟩ := intern_name_run'₀ n hwf hrel.to₀ hinv hrun
  exact ⟨h1.toSim (fun _ _ hx => (internName_run_denote _ hrel.storeWF hx).2)
    (fun _ _ => trivial), h2⟩


theorem intern_level_run'₀ :
    ∀ (l : kernel.level.Level) (_hwf : ConRon.Refine.LevelWF l)
      {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState} {o},
      AStateRel₀ pers st lst → AStateInv pers st →
      arena.monad.intern_level pers st l = ok o →
      Sim₀ absLIdx pers lst o
        (Arena.internLevel (ConRon.Refine.absLevel l)) ∧
      FlagsEq st.store o.2.store := by
  intro l hwf
  induction l, hwf using ConRon.Refine.LevelWF.ind_node with
  | zero hh w =>
    intro pers st lst o hrel hinv hrun
    rw [arena.monad.intern_level, ConRon.Refine.bind_arc_deref] at hrun
    replace hrun : arena.monad.intern_l_node pers st arena.store.LNodeView.Zero
        = ok o := hrun
    refine ⟨?_, intern_l_node_flags hrun⟩
    exact intern_l_node_run₀ hrel hinv arena.store.LNodeView.Zero hrun
  | succ hh a w ih =>
    intro pers st lst o hrel hinv hrun
    rw [arena.monad.intern_level, ConRon.Refine.bind_arc_deref] at hrun
    replace hrun : (do
        let (r, st1) ← arena.monad.intern_level pers st a
        match r with
        | .Ok hu => arena.monad.intern_l_node pers st1 (arena.store.LNodeView.Succ hu)
        | .Err _ => ok (r, st1)) = ok o := hrun
    obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r1, st1⟩ := p1
    obtain ⟨hsim1, hfl1⟩ := ih (ConRon.Refine.Level.LevelWF.succ_inv w) hrel hinv hp1
    cases hr : r1 with
    | Err e =>
      simp only [hr] at hrun
      obtain rfl : ((core.result.Result.Err e :
          core.result.Result arena.handle.LIdx kernel.core_types.CheckError), st1) = o :=
        Result.ok_injective hrun
      refine ⟨?_, hfl1⟩
      show AOut₀ absLIdx pers _ _ _
      rw [show ConRon.Refine.absLevel
            (kernel.level.Level.mk (kernel.level.LevelNode.mk hh (.Succ a)))
          = ConLeche.Level.succ (ConRon.Refine.absLevel a) from rfl, Arena.internLevel]
      exact AOut₀.errBind (hr ▸ hsim1)
    | Ok hu =>
      simp only [hr] at hrun
      obtain ⟨lst1, hy1, hrel1, hinv1⟩ :=
        (hr ▸ hsim1 : AOut₀ _ _ (.Ok hu) _ _)
      have hsim2 := intern_l_node_run₀ hrel1 hinv1
        (arena.store.LNodeView.Succ hu) hrun
      refine ⟨?_, hfl1.trans (intern_l_node_flags hrun)⟩
      show AOut₀ absLIdx pers _ _ _
      rw [show ConRon.Refine.absLevel
            (kernel.level.Level.mk (kernel.level.LevelNode.mk hh (.Succ a)))
          = ConLeche.Level.succ (ConRon.Refine.absLevel a) from rfl,
        Arena.internLevel, run_bind_ok hy1]
      exact hsim2
  | max hh a b w iha ihb =>
    intro pers st lst o hrel hinv hrun
    rw [arena.monad.intern_level, ConRon.Refine.bind_arc_deref] at hrun
    replace hrun : (do
        let (r, st1) ← arena.monad.intern_level pers st a
        match r with
        | .Ok hu => do
            let (r1, st2) ← arena.monad.intern_level pers st1 b
            match r1 with
            | .Ok hv => arena.monad.intern_l_node pers st2 (arena.store.LNodeView.Max hu hv)
            | .Err _ => ok (r1, st2)
        | .Err _ => ok (r, st1)) = ok o := hrun
    obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r1, st1⟩ := p1
    obtain ⟨hsim1, hfl1⟩ :=
      iha (ConRon.Refine.Level.LevelWF.max_inv w).1 hrel hinv hp1
    have habs : ConRon.Refine.absLevel
        (kernel.level.Level.mk (kernel.level.LevelNode.mk hh (.Max a b)))
      = ConLeche.Level.max (ConRon.Refine.absLevel a) (ConRon.Refine.absLevel b) := rfl
    cases hr : r1 with
    | Err e =>
      simp only [hr] at hrun
      obtain rfl : ((core.result.Result.Err e :
          core.result.Result arena.handle.LIdx kernel.core_types.CheckError), st1) = o :=
        Result.ok_injective hrun
      refine ⟨?_, hfl1⟩
      show AOut₀ absLIdx pers _ _ _
      rw [habs, Arena.internLevel]
      exact AOut₀.errBind (hr ▸ hsim1)
    | Ok hu =>
      simp only [hr] at hrun
      obtain ⟨lst1, hy1, hrel1, hinv1⟩ :=
        (hr ▸ hsim1 : AOut₀ _ _ (.Ok hu) _ _)
      obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r2, st2⟩ := p2
      obtain ⟨hsim2, hfl2⟩ :=
        ihb (ConRon.Refine.Level.LevelWF.max_inv w).2 hrel1 hinv1 hp2
      cases hr2 : r2 with
      | Err e =>
        simp only [hr2] at hrun
        obtain rfl : ((core.result.Result.Err e :
            core.result.Result arena.handle.LIdx kernel.core_types.CheckError), st2) = o :=
          Result.ok_injective hrun
        refine ⟨?_, hfl1.trans hfl2⟩
        show AOut₀ absLIdx pers _ _ _
        rw [habs, Arena.internLevel, run_bind_ok hy1]
        exact AOut₀.errBind (hr2 ▸ hsim2)
      | Ok hv =>
        simp only [hr2] at hrun
        obtain ⟨lst2, hy2, hrel2, hinv2⟩ :=
          (hr2 ▸ hsim2 : AOut₀ _ _ (.Ok hv) _ _)
        have hsim3 := intern_l_node_run₀ hrel2 hinv2
          (arena.store.LNodeView.Max hu hv) hrun
        refine ⟨?_, (hfl1.trans hfl2).trans (intern_l_node_flags hrun)⟩
        show AOut₀ absLIdx pers _ _ _
        rw [habs, Arena.internLevel, run_bind_ok hy1, run_bind_ok hy2]
        exact hsim3
  | imax hh a b w iha ihb =>
    intro pers st lst o hrel hinv hrun
    rw [arena.monad.intern_level, ConRon.Refine.bind_arc_deref] at hrun
    replace hrun : (do
        let (r, st1) ← arena.monad.intern_level pers st a
        match r with
        | .Ok hu => do
            let (r1, st2) ← arena.monad.intern_level pers st1 b
            match r1 with
            | .Ok hv => arena.monad.intern_l_node pers st2 (arena.store.LNodeView.Imax hu hv)
            | .Err _ => ok (r1, st2)
        | .Err _ => ok (r, st1)) = ok o := hrun
    obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r1, st1⟩ := p1
    obtain ⟨hsim1, hfl1⟩ :=
      iha (ConRon.Refine.Level.LevelWF.imax_inv w).1 hrel hinv hp1
    have habs : ConRon.Refine.absLevel
        (kernel.level.Level.mk (kernel.level.LevelNode.mk hh (.Imax a b)))
      = ConLeche.Level.imax (ConRon.Refine.absLevel a) (ConRon.Refine.absLevel b) := rfl
    cases hr : r1 with
    | Err e =>
      simp only [hr] at hrun
      obtain rfl : ((core.result.Result.Err e :
          core.result.Result arena.handle.LIdx kernel.core_types.CheckError), st1) = o :=
        Result.ok_injective hrun
      refine ⟨?_, hfl1⟩
      show AOut₀ absLIdx pers _ _ _
      rw [habs, Arena.internLevel]
      exact AOut₀.errBind (hr ▸ hsim1)
    | Ok hu =>
      simp only [hr] at hrun
      obtain ⟨lst1, hy1, hrel1, hinv1⟩ :=
        (hr ▸ hsim1 : AOut₀ _ _ (.Ok hu) _ _)
      obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r2, st2⟩ := p2
      obtain ⟨hsim2, hfl2⟩ :=
        ihb (ConRon.Refine.Level.LevelWF.imax_inv w).2 hrel1 hinv1 hp2
      cases hr2 : r2 with
      | Err e =>
        simp only [hr2] at hrun
        obtain rfl : ((core.result.Result.Err e :
            core.result.Result arena.handle.LIdx kernel.core_types.CheckError), st2) = o :=
          Result.ok_injective hrun
        refine ⟨?_, hfl1.trans hfl2⟩
        show AOut₀ absLIdx pers _ _ _
        rw [habs, Arena.internLevel, run_bind_ok hy1]
        exact AOut₀.errBind (hr2 ▸ hsim2)
      | Ok hv =>
        simp only [hr2] at hrun
        obtain ⟨lst2, hy2, hrel2, hinv2⟩ :=
          (hr2 ▸ hsim2 : AOut₀ _ _ (.Ok hv) _ _)
        have hsim3 := intern_l_node_run₀ hrel2 hinv2
          (arena.store.LNodeView.Imax hu hv) hrun
        refine ⟨?_, (hfl1.trans hfl2).trans (intern_l_node_flags hrun)⟩
        show AOut₀ absLIdx pers _ _ _
        rw [habs, Arena.internLevel, run_bind_ok hy1, run_bind_ok hy2]
        exact hsim3
  | param hh n w =>
    intro pers st lst o hrel hinv hrun
    rw [arena.monad.intern_level, ConRon.Refine.bind_arc_deref] at hrun
    replace hrun : (do
        let (r, st1) ← arena.monad.intern_name pers st n
        match r with
        | .Ok hn => arena.monad.intern_l_node pers st1 (arena.store.LNodeView.Param hn)
        | .Err e => ok ((.Err e : core.result.Result arena.handle.LIdx _), st1))
        = ok o := hrun
    obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r1, st1⟩ := p1
    obtain ⟨hsim1, hfl1⟩ :=
      intern_name_run'₀ n (ConRon.Refine.Level.LevelWF.param_inv w) hrel hinv hp1
    have habs : ConRon.Refine.absLevel
        (kernel.level.Level.mk (kernel.level.LevelNode.mk hh (.Param n)))
      = ConLeche.Level.param (ConRon.Refine.absName n) := rfl
    cases hr : r1 with
    | Err e =>
      simp only [hr] at hrun
      obtain rfl : ((core.result.Result.Err e :
          core.result.Result arena.handle.LIdx kernel.core_types.CheckError), st1) = o :=
        Result.ok_injective hrun
      refine ⟨?_, hfl1⟩
      show AOut₀ absLIdx pers _ _ _
      rw [habs, Arena.internLevel]
      exact AOut₀.errBind (hr ▸ hsim1)
    | Ok hn =>
      simp only [hr] at hrun
      obtain ⟨lst1, hy1, hrel1, hinv1⟩ :=
        (hr ▸ hsim1 : AOut₀ _ _ (.Ok hn) _ _)
      have hsim2 := intern_l_node_run₀ hrel1 hinv1
        (arena.store.LNodeView.Param hn) hrun
      refine ⟨?_, hfl1.trans (intern_l_node_flags hrun)⟩
      show AOut₀ absLIdx pers _ _ _
      rw [habs, Arena.internLevel, run_bind_ok hy1]
      exact hsim2

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_level_run'₀`. -/
theorem intern_level_run' :
    ∀ (l : kernel.level.Level) (_hwf : ConRon.Refine.LevelWF l)
      {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState} {o},
      AStateRel pers st lst → AStateInv pers st →
      arena.monad.intern_level pers st l = ok o →
      Sim absLIdx (fun _ => True) pers lst o
        (Arena.internLevel (ConRon.Refine.absLevel l)) ∧
      FlagsEq st.store o.2.store := by
  intro l hwf pers st lst o hrel hinv hrun
  obtain ⟨h1, h2⟩ := intern_level_run'₀ l hwf hrel.to₀ hinv hrun
  exact ⟨h1.toSim (fun _ _ hx => (internLevel_run_denote _ hrel.storeWF hx).2)
    (fun _ _ => trivial), h2⟩


/-! ### The level-list cursor

`intern_level_list_from` carries an accumulator the twin's `internLevelList`
does not, so the induction is `read_names_m_from_abs`'s (round 1 §4): a fuel
`k ≥ us.length - i`, the twin's run taken at the DROP of the cursor, and the
port's `out` prepended to it. -/

/-- `prependOut` at a list of level handles. -/
def prependOutL (pre : List LIdx)
    (x : Except Arena.CheckError (List LIdx × AState)) :
    Except Arena.CheckError (List LIdx × AState) :=
  match x with
  | .ok p => .ok (pre ++ p.1, p.2)
  | .error e => .error e

@[simp] theorem prependOutL_nil (x) : prependOutL [] x = x := by
  cases x with
  | error e => rfl
  | ok p => obtain ⟨a, b⟩ := p; rfl

theorem internLevelList_run_cons (lst : AState) (u : ConLeche.Level)
    (us : List ConLeche.Level) :
    (Arena.internLevelList (u :: us)).run lst
      = ((Arena.internLevel u).run lst).bind fun p =>
          ((Arena.internLevelList us).run p.2).bind fun q => Except.ok (p.1 :: q.1, q.2) := by
  show (do let hu ← Arena.internLevel u; let hus ← Arena.internLevelList us;
           pure (hu :: hus) : AM _).run lst = _
  rw [StateT.run_bind]
  congr 1

theorem intern_level_list_from_run'₀ {pers} {us : alloc.vec.Vec kernel.level.Level}
    (hwf : ConRon.Refine.LevelsWF us) :
    ∀ k {st : arena.monad.AState} {lst : AState}, AStateRel₀ pers st lst →
      AStateInv pers st →
      ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.LIdx),
      us.length - i.val ≤ k → ∀ {o},
      arena.monad.intern_level_list_from pers st us i out = ok o →
      AOut₀ (fun v : alloc.vec.Vec arena.handle.LIdx => v.val.map absLIdx)
        pers o.1 o.2
        (prependOutL (out.val.map absLIdx)
          ((Arena.internLevelList
            ((us.val.drop i.val).map ConRon.Refine.absLevel)).run lst)) ∧
      FlagsEq st.store o.2.store := by
  intro k
  induction k with
  | zero =>
    intro st lst hrel hinv i out hk o hrun
    rw [arena.monad.intern_level_list_from.eq_def] at hrun; simp only [] at hrun
    rw [if_pos (by scalar_tac)] at hrun
    rw [List.drop_eq_nil_of_le (by scalar_tac), List.map_nil]
    have ho : ((core.result.Result.Ok out : core.result.Result _ _), st) = o :=
      Result.ok_injective hrun
    rw [← ho]
    refine ⟨?_, FlagsEq.refl _⟩
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    show prependOutL _ (Except.ok (([] : List LIdx), lst)) = _
    show Except.ok (out.val.map absLIdx ++ [], lst) = _
    rw [List.append_nil]
  | succ k ih =>
    intro st lst hrel hinv i out hk o hrun
    rw [arena.monad.intern_level_list_from.eq_def] at hrun; simp only [] at hrun
    split at hrun
    · rw [List.drop_eq_nil_of_le (by scalar_tac), List.map_nil]
      have ho : ((core.result.Result.Ok out : core.result.Result _ _), st) = o :=
        Result.ok_injective hrun
      rw [← ho]
      refine ⟨?_, FlagsEq.refl _⟩
      refine AOut₀.ok (lst' := lst) ?_ hrel hinv
      show prependOutL _ (Except.ok (([] : List LIdx), lst)) = _
      show Except.ok (out.val.map absLIdx ++ [], lst) = _
      rw [List.append_nil]
    · rename_i hlt
      have hb : i.val < us.length := by scalar_tac
      obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hlv : us.val[i.val] = l := by
        have h1 : us.val[i.val]? = some l := vec_index_some hl
        rw [List.getElem?_eq_getElem hb] at h1
        exact (Option.some.injEq _ _ ▸ h1)
      obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r, st1⟩ := p1
      have hlwf : ConRon.Refine.LevelWF l := by
        rw [← hlv]; exact hwf _ (List.getElem_mem hb)
      obtain ⟨hstep, hfl1⟩ := intern_level_run'₀ l hlwf hrel hinv hp1
      rw [List.drop_eq_getElem_cons hb, List.map_cons, hlv, internLevelList_run_cons]
      cases hrc : r with
      | Err e =>
        rw [hrc] at hstep
        simp only [hrc] at hrun
        have herr : AErrSim e ((Arena.internLevel (ConRon.Refine.absLevel l)).run lst) :=
          hstep
        have ho : ((core.result.Result.Err e : core.result.Result _ _), st1) = o :=
          Result.ok_injective hrun
        rw [← ho]
        refine ⟨?_, hfl1⟩
        refine AOut₀.err ?_
        intro kk hkk
        obtain ⟨le, hle, hk2⟩ := herr kk hkk
        exact ⟨le, by rw [hle]; rfl, hk2⟩
      | Ok x =>
        rw [hrc] at hstep
        simp only [hrc] at hrun
        obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hstep
        rw [hx1]
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hout1v : out1.val = out.val ++ [x] := ConRon.Refine.vec_push_val hout1
        obtain ⟨hih, hfl2⟩ := ih hrel1 hinv1 i2 out1 (by scalar_tac) hrun
        rw [hi2v] at hih
        refine ⟨?_, hfl1.trans hfl2⟩
        show AOut₀ _ pers o.1 o.2
          (prependOutL _ (((Arena.internLevelList
            ((us.val.drop (i.val + 1)).map ConRon.Refine.absLevel)).run lst1).bind _))
        cases hy : (Arena.internLevelList
            ((us.val.drop (i.val + 1)).map ConRon.Refine.absLevel)).run lst1 with
        | error e =>
          rw [hy] at hih
          cases hoc : o.1 with
          | Ok v =>
            rw [hoc] at hih
            obtain ⟨lst2, hcontra, -⟩ := hih
            exact absurd hcontra (by simp [prependOutL])
          | Err e2 =>
            rw [hoc] at hih
            have herr : AErrSim e2 (prependOutL (out1.val.map absLIdx)
              (Except.error e)) := hih
            refine AOut₀.err ?_
            intro kk hkk
            obtain ⟨le, hle, hk2⟩ := herr kk hkk
            refine ⟨le, ?_, hk2⟩
            have hee : (Except.error e : Except Arena.CheckError (List LIdx × AState))
                = Except.error le := by
              have := hle; simp only [prependOutL] at this; exact this
            simp only [Except.error.injEq] at hee
            rw [← hee]; rfl
        | ok q =>
          rw [hy] at hih
          cases hoc : o.1 with
          | Err e2 =>
            rw [hoc] at hih
            have herr : AErrSim e2 (prependOutL (out1.val.map absLIdx)
              (Except.ok q)) := hih
            refine AOut₀.err ?_
            intro kk hkk
            obtain ⟨le, hle, -⟩ := herr kk hkk
            simp only [prependOutL] at hle
            exact absurd hle (by simp)
          | Ok v =>
            rw [hoc] at hih
            obtain ⟨lst2, hv2, hrel2, hinv2⟩ := hih
            simp only [prependOutL, Except.ok.injEq, Prod.mk.injEq] at hv2
            refine AOut₀.ok (lst' := lst2) ?_ hrel2 hinv2
            show Except.ok (out.val.map absLIdx ++ (absLIdx x :: q.1), q.2) = _
            rw [← hv2.2]
            have hq1 : out1.val.map absLIdx ++ q.1 = v.val.map absLIdx := hv2.1
            rw [hout1v] at hq1
            simp only [List.map_append, List.map_cons, List.map_nil,
              List.append_assoc, List.cons_append, List.nil_append] at hq1
            rw [hq1]

theorem intern_level_list_run'₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {us : alloc.vec.Vec kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelsWF us)
    (hrun : arena.monad.intern_level_list pers st us = ok o) :
    Sim₀ (fun v : alloc.vec.Vec arena.handle.LIdx => v.val.map absLIdx)
      pers lst o
      (Arena.internLevelList (ConRon.Refine.absLevels us)) ∧
    FlagsEq st.store o.2.store := by
  rw [arena.monad.intern_level_list] at hrun
  obtain ⟨h1, h2⟩ := intern_level_list_from_run'₀ hwf us.length hrel hinv 0#usize
    (alloc.vec.Vec.new arena.handle.LIdx) (by simp) hrun
  refine ⟨?_, h2⟩
  show AOut₀ _ pers o.1 o.2 _
  have he : (alloc.vec.Vec.new arena.handle.LIdx).val.map absLIdx = [] := by
    simp [alloc.vec.Vec.new]
  rw [he, prependOutL_nil] at h1
  have hd : ((us.val.drop (0#usize).val).map ConRon.Refine.absLevel)
      = ConRon.Refine.absLevels us := by
    simp [ConRon.Refine.absLevels]
  rw [hd] at h1
  exact h1

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_level_list_run'₀`. -/
theorem intern_level_list_run' {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    {us : alloc.vec.Vec kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelsWF us)
    (hrun : arena.monad.intern_level_list pers st us = ok o) :
    Sim (fun v : alloc.vec.Vec arena.handle.LIdx => v.val.map absLIdx)
      (fun _ => True) pers lst o
      (Arena.internLevelList (ConRon.Refine.absLevels us)) ∧
    FlagsEq st.store o.2.store := by
  obtain ⟨h1, h2⟩ := intern_level_list_run'₀ hrel.to₀ hinv hwf hrun
  exact ⟨h1.toSim (fun _ _ hx => (internLevelList_run_denote _ hrel.storeWF hx).2)
    (fun _ _ => trivial), h2⟩


theorem intern_levels_run'₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {us : alloc.vec.Vec kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelsWF us)
    (hrun : arena.monad.intern_levels pers st us = ok o) :
    Sim₀ absLsIdx pers lst o
      (Arena.internLevels (ConRon.Refine.absLevels us)) ∧
    FlagsEq st.store o.2.store := by
  rw [arena.monad.intern_levels] at hrun
  obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := p1
  obtain ⟨hsim1, hfl1⟩ := intern_level_list_run'₀ hrel hinv hwf hp1
  cases hr : r1 with
  | Err e =>
    simp only [hr] at hrun
    obtain rfl : ((core.result.Result.Err e :
        core.result.Result arena.handle.LsIdx kernel.core_types.CheckError), st1) = o :=
      Result.ok_injective hrun
    refine ⟨?_, hfl1⟩
    show AOut₀ absLsIdx pers _ _ _
    rw [Arena.internLevels]
    exact AOut₀.errBind (hr ▸ hsim1)
  | Ok hs =>
    simp only [hr] at hrun
    obtain ⟨lst1, hy1, hrel1, hinv1⟩ :=
      (hr ▸ hsim1 : AOut₀ _ _ (.Ok hs) _ _)
    have hsim2 := intern_ls_node_run₀ hrel1 hinv1 hs hrun
    refine ⟨?_, hfl1.trans (intern_ls_node_flags hrun)⟩
    show AOut₀ absLsIdx pers _ _ _
    rw [Arena.internLevels, run_bind_ok hy1]
    exact hsim2

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `intern_levels_run'₀`. -/
theorem intern_levels_run' {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st)
    {us : alloc.vec.Vec kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelsWF us)
    (hrun : arena.monad.intern_levels pers st us = ok o) :
    Sim absLsIdx (fun _ => True) pers lst o
      (Arena.internLevels (ConRon.Refine.absLevels us)) ∧
    FlagsEq st.store o.2.store := by
  obtain ⟨h1, h2⟩ := intern_levels_run'₀ hrel.to₀ hinv hwf hrun
  exact ⟨h1.toSim (fun _ _ hx => (internLevels_run_denote _ hrel.storeWF hx).2)
    (fun _ _ => trivial), h2⟩

/-! #### The four statements, and their flag halves -/

/-- `arena::monad::intern_name` against `Arena.internName` — a structural
walk over a transient `Name`, so no fuel (DESIGN §8.3: "the tree is a value,
not a DAG"). -/
theorem intern_name_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {n : kernel.name.Name} {o}
    (hwf : ConRon.Refine.NameWF n)
    (hrun : arena.monad.intern_name pers st n = ok o) :
    Sim₀ absNIdx pers lst o
      (Arena.internName (ConRon.Refine.absName n)) :=
  (intern_name_run'₀ n hwf hrel hinv hrun).1

/-- The name walk moves no tier flag. -/
theorem intern_name_flags₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {n : kernel.name.Name} {o}
    (hwf : ConRon.Refine.NameWF n)
    (hrun : arena.monad.intern_name pers st n = ok o) :
    FlagsEq st.store o.2.store :=
  (intern_name_run'₀ n hwf hrel hinv hrun).2

/-- `arena::monad::intern_level` against `Arena.internLevel`. -/
theorem intern_level_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {l : kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelWF l)
    (hrun : arena.monad.intern_level pers st l = ok o) :
    Sim₀ absLIdx pers lst o
      (Arena.internLevel (ConRon.Refine.absLevel l)) :=
  (intern_level_run'₀ l hwf hrel hinv hrun).1

/-- The level walk moves no tier flag. -/
theorem intern_level_flags₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {l : kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelWF l)
    (hrun : arena.monad.intern_level pers st l = ok o) :
    FlagsEq st.store o.2.store :=
  (intern_level_run'₀ l hwf hrel hinv hrun).2

/-- `arena::monad::intern_level_list` against `Arena.internLevelList`. -/
theorem intern_level_list_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {us : alloc.vec.Vec kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelsWF us)
    (hrun : arena.monad.intern_level_list pers st us = ok o) :
    Sim₀ (fun v : alloc.vec.Vec arena.handle.LIdx => v.val.map absLIdx)
      pers lst o
      (Arena.internLevelList (ConRon.Refine.absLevels us)) :=
  (intern_level_list_run'₀ hrel hinv hwf hrun).1

/-- The level-list walk moves no tier flag. -/
theorem intern_level_list_flags₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {us : alloc.vec.Vec kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelsWF us)
    (hrun : arena.monad.intern_level_list pers st us = ok o) :
    FlagsEq st.store o.2.store :=
  (intern_level_list_run'₀ hrel hinv hwf hrun).2

/-- `arena::monad::intern_levels` against `Arena.internLevels` — the list
walk, then the list node, so all three tiers. -/
theorem intern_levels_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {us : alloc.vec.Vec kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelsWF us)
    (hrun : arena.monad.intern_levels pers st us = ok o) :
    Sim₀ absLsIdx pers lst o
      (Arena.internLevels (ConRon.Refine.absLevels us)) :=
  (intern_levels_run'₀ hrel hinv hwf hrun).1

/-- The levels walk moves no tier flag. -/
theorem intern_levels_flags₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {us : alloc.vec.Vec kernel.level.Level} {o}
    (hwf : ConRon.Refine.LevelsWF us)
    (hrun : arena.monad.intern_levels pers st us = ok o) :
    FlagsEq st.store o.2.store :=
  (intern_levels_run'₀ hrel hinv hwf hrun).2

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

/-! ## The memoised readbacks (task #97-P6-13, closed by task #97-P5-Specs)

`read_level_m` / `read_name_m` / `read_levels_m` / `read_names_m` probe the
per-declaration readback cache and INSERT on a miss, so they thread the state:
`Sim`, not `SimR`.  They live HERE rather than beside the four plain readbacks
because what they need beyond the probe is the insert half — `memo_insert_step`
just above — and one clause more:

**`CachesInv`'s VALUE clause.**  `readNVals`/`readLVals`/`readLsVals` say
*"every cached tree is well formed"*, and it is the one memo obligation that is
about values rather than keys.  `memo_insert_vals` re-establishes it across an
`insert` through `toFun` rather than through the slot list, because
`insert_refines_wf` states its effect as `toFun m' = Function.update (toFun m)
key (some value)` and `HashMap2`'s `Inv.nodup` turns a slot back into a `toFun`
answer.  The value's own well-formedness is `denote_n_wf` / `denote_l_wf` /
`denote_ls_wf`, proved with the readbacks above.

`read_names_m` is the one with a cursor AND a threaded state: the port pushes
into a `Vec` where the twin conses, and the memo grows along the loop, so the
induction generalises over the state pair and `prependOut` is what puts the two
runs on the same footing. -/

/-- The readback memo's VALUE clause across an insert: `CachesInv`'s
`readLVals`/`readNVals`/`readLsVals` are the one memo obligation that is about
values rather than keys, and `HashMap2`'s `insert` spec states its effect on
`toFun`, so the route is `toFun`, not the slot list. -/
theorem memo_insert_vals {K V : Type} [DecidableEq K]
    {HashableInst : ron.hashmap.Hashable K}
    {m m' : ron.hashmap2.HashMap2 K V} {P : V → Prop} {key : K} {value : V}
    (hinv' : Inv HashableInst m')
    (hupd : toFun m' = Function.update (toFun m) key (some value))
    (hm : ∀ p ∈ sl_v m, P p.2) (hv : P value) : ∀ p ∈ sl_v m', P p.2 := by
  intro p hp
  have h1 : toFun m' p.1 = some p.2 :=
    ConRon.Refine.HashMap.lookupK_eq_some_of_mem hinv'.nodup hp
  rw [hupd, Function.update_apply] at h1
  by_cases hk : p.1 = key
  · rw [if_pos hk] at h1
    simp only [Option.some.injEq] at h1
    rw [← h1]; exact hv
  · rw [if_neg hk] at h1
    exact hm p (ConRon.Refine.HashMap.lookupK_mem h1)

theorem readNameM_run (lst : AState) (h : NIdx) :
    (Arena.readNameM h).run lst
      = match lst.caches.readNC[h]? with
        | some x => Except.ok (x, lst)
        | none =>
          match denoteN lst.store.ns h with
          | none => Except.error (.internal "arena: dangling name handle")
          | some x => Except.ok (x,
              { lst with caches := { lst.caches with
                  readNC := lst.caches.readNC.insert h x } }) := by
  show (match lst.caches.readNC[h]? with
        | some x => (pure x : AM _)
        | none =>
          match denoteN lst.store.ns h with
          | none => Arena.fail (.internal "arena: dangling name handle")
          | some x => (do
              set { ({ lst with caches := { lst.caches with readNC := ∅ } } : AState)
                with caches := { ({ lst with caches :=
                  { lst.caches with readNC := ∅ } } : AState).caches with
                  readNC := lst.caches.readNC.insert h x } }
              pure x : AM _)).run lst = _
  cases lst.caches.readNC[h]? with
  | some x => rfl
  | none =>
    cases denoteN lst.store.ns h with
    | none => rfl
    | some x => rfl

theorem read_name_m_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.NIdx} {o}
    (hrun : arena.monad.read_name_m pers st h = ok o) :
    Sim₀ ConRon.Refine.absName pers lst o
      (Arena.readNameM (absNIdx h)) := by
  rw [arena.monad.read_name_m] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hinv.caches.readNC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.readNC h trivial
  rw [← hto] at hrelk
  show AOut₀ _ pers o.1 o.2 _
  rw [readNameM_run]
  cases hrc : r with
  | some x =>
    rw [hrc] at hrun hrelk
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok n, st) = o := Result.ok_injective hrun
    rw [← ho]
    simp only [Option.map_some] at hrelk
    rw [← hrelk]
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    rw [ConRon.Refine.Name.dup_refines hn]
  | none =>
    rw [hrc] at hrun hrelk
    simp only [Option.map_none] at hrelk
    rw [← hrelk]
    obtain ⟨ns, hns, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ns] at hns
    have hns2 : ns = st.store.lss.ls.ns := (Result.ok_injective hns).symm
    subst hns2
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hd := denote_n_abs hrel.store.lss.lvl.ns hv
    have hdw := denote_n_wf hinv.store.lss.lvl.ns hv
    cases hvc : v with
    | none =>
      rw [hvc] at hrun hd
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrre := fail_run hrr
      subst hrre
      have ho : ((core.result.Result.Err
        (kernel.core_types.CheckError.Internal w)), st) = o := Result.ok_injective hrun
      rw [← ho]
      show AErrSim _ _
      rw [EStore.ns, ← hd]
      exact AErrSim.internal rfl
    | some x =>
      rw [hvc] at hrun hd hdw
      obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨n2, hn2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨old, hm⟩ := p
      rw [dupId_nidx _ _ hk1] at hp
      have hn2e : n2 = x := (Result.ok_injective (by rw [← hn2]; simp)).symm
      subst hn2e
      have ho : (core.result.Result.Ok n2,
        ({ st with caches := { st.caches with read_n_c := hm } } :
          arena.monad.AState)) = o := Result.ok_injective hrun
      rw [← ho]
      obtain ⟨h1, h2⟩ := memo_insert_step nidx_eq2 absNIdx_inj hinv.caches.readNC
        hrel.caches.readNC hp
      have hins := ConRon.Refine.HashMap2.insert_refines_wf nidx_eq2
        hinv.caches.readNC ConRon.Refine.HashMap2.KeysOk_true trivial hp
      have hvals := memo_insert_vals h2 hins.2.2.1 hinv.caches.readNVals (hdw n2 rfl)
      show AOut₀ _ pers _ _ _
      rw [EStore.ns, ← hd]
      refine AOut₀.ok (lst' := { lst with caches := { lst.caches with
          readNC := lst.caches.readNC.insert (absNIdx h) (ConRon.Refine.absName n2) } })
        rfl
        { hrel with caches := { hrel.caches with readNC := h1 } }
        { hinv with caches := { hinv.caches with readNC := h2, readNVals := hvals } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `read_name_m_run₀`. -/
theorem read_name_m_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.NIdx} {o}
    (hrun : arena.monad.read_name_m pers st h = ok o) :
    Sim ConRon.Refine.absName (fun _ => True) pers lst o
      (Arena.readNameM (absNIdx h)) := by
  refine Sim₀.toSim_of_store (read_name_m_run₀ hrel.to₀ hinv hrun) hrel.storeWF ?_
  intro b lst' hx
  rw [readNameM_run] at hx
  split at hx
  · cases hx; rfl
  · split at hx
    · cases hx
    · cases hx; rfl

/-- `arena::monad::level_list_dup` is the identity on the list (DESIGN §3.2:
a `dup` is `Arc::clone`, and the model makes it the identity). -/
theorem level_list_dup_from_val {us : alloc.vec.Vec kernel.level.Level} :
    ∀ k (i : Std.Usize) (out : alloc.vec.Vec kernel.level.Level),
      us.length - i.val ≤ k → ∀ {v},
      arena.monad.level_list_dup_from us i out = ok v →
      v.val = out.val ++ us.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out hk v hrun
    rw [arena.monad.level_list_dup_from.eq_def] at hrun; simp only [] at hrun
    rw [if_pos (by scalar_tac)] at hrun
    rw [← Result.ok_injective hrun, List.drop_eq_nil_of_le (by scalar_tac)]
    simp
  | succ k ih =>
    intro i out hk v hrun
    rw [arena.monad.level_list_dup_from.eq_def] at hrun; simp only [] at hrun
    split at hrun
    · rw [← Result.ok_injective hrun, List.drop_eq_nil_of_le (by scalar_tac)]
      simp
    · rename_i hlt
      have hb : i.val < us.length := by scalar_tac
      obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨l1, hl1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v : i2.val = i.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
      have hlv : us.val[i.val] = l := by
        have h1 : us.val[i.val]? = some l := vec_index_some hl
        rw [List.getElem?_eq_getElem hb] at h1
        exact (Option.some.injEq _ _ ▸ h1)
      have hl1e : l1 = l := by
        rw [ConRon.Refine.level_dup_eq] at hl1; exact (Result.ok_injective hl1).symm
      have hout1v : out1.val = out.val ++ [l1] := ConRon.Refine.vec_push_val hout1
      have hih := ih i2 out1 (by scalar_tac) hrun
      rw [hih, hout1v, hi2v, List.drop_eq_getElem_cons hb, hlv, hl1e]
      simp

theorem level_list_dup_val {us v : alloc.vec.Vec kernel.level.Level}
    (h : arena.monad.level_list_dup us = ok v) : v.val = us.val := by
  rw [arena.monad.level_list_dup] at h
  have hh := level_list_dup_from_val us.length 0#usize
    (alloc.vec.Vec.new kernel.level.Level) (by scalar_tac) h
  simpa using hh

theorem readLevelM_run (lst : AState) (h : LIdx) :
    (Arena.readLevelM h).run lst
      = match lst.caches.readLC[h]? with
        | some x => Except.ok (x, lst)
        | none =>
          match denoteL lst.store.ls h with
          | none => Except.error (.internal "arena: dangling level handle")
          | some x => Except.ok (x,
              { lst with caches := { lst.caches with
                  readLC := lst.caches.readLC.insert h x } }) := by
  show (match lst.caches.readLC[h]? with
        | some x => (pure x : AM _)
        | none =>
          match denoteL lst.store.ls h with
          | none => Arena.fail (.internal "arena: dangling level handle")
          | some x => (do
              set { ({ lst with caches := { lst.caches with readLC := ∅ } } : AState)
                with caches := { ({ lst with caches :=
                  { lst.caches with readLC := ∅ } } : AState).caches with
                  readLC := lst.caches.readLC.insert h x } }
              pure x : AM _)).run lst = _
  cases lst.caches.readLC[h]? with
  | some x => rfl
  | none => cases denoteL lst.store.ls h <;> rfl

theorem read_level_m_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LIdx} {o}
    (hrun : arena.monad.read_level_m pers st h = ok o) :
    Sim₀ ConRon.Refine.absLevel pers lst o
      (Arena.readLevelM (absLIdx h)) := by
  rw [arena.monad.read_level_m] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lidx_eq2 hinv.caches.readLC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.readLC h trivial
  rw [← hto] at hrelk
  show AOut₀ _ pers o.1 o.2 _
  rw [readLevelM_run]
  cases hrc : r with
  | some x =>
    rw [hrc] at hrun hrelk
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok n, st) = o := Result.ok_injective hrun
    rw [← ho]
    simp only [Option.map_some] at hrelk
    rw [← hrelk]
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    have hne : n = x := by
      rw [ConRon.Refine.level_dup_eq] at hn; exact (Result.ok_injective hn).symm
    rw [hne]
  | none =>
    rw [hrc] at hrun hrelk
    simp only [Option.map_none] at hrelk
    rw [← hrelk]
    obtain ⟨ls0, hls0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ls] at hls0
    have hls2 : ls0 = st.store.lss.ls := (Result.ok_injective hls0).symm
    subst hls2
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hd := denote_l_abs hrel.store.lss.lvl hv
    have hdw := denote_l_wf hinv.store.lss.lvl hv
    cases hvc : v with
    | none =>
      rw [hvc] at hrun hd
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrre := fail_run hrr
      subst hrre
      have ho : ((core.result.Result.Err
        (kernel.core_types.CheckError.Internal w)), st) = o := Result.ok_injective hrun
      rw [← ho]
      show AErrSim _ _
      rw [EStore.ls, ← hd]
      exact AErrSim.internal rfl
    | some x =>
      rw [hvc] at hrun hd hdw
      obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨l3, hl3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨old, hm⟩ := p
      rw [dupId_lidx _ _ hk1] at hp
      have hl3e : l3 = x := by
        rw [ConRon.Refine.level_dup_eq] at hl3; exact (Result.ok_injective hl3).symm
      subst hl3e
      have ho : (core.result.Result.Ok l3,
        ({ st with caches := { st.caches with read_l_c := hm } } :
          arena.monad.AState)) = o := Result.ok_injective hrun
      rw [← ho]
      obtain ⟨h1, h2⟩ := memo_insert_step lidx_eq2 absLIdx_inj hinv.caches.readLC
        hrel.caches.readLC hp
      have hins := ConRon.Refine.HashMap2.insert_refines_wf lidx_eq2
        hinv.caches.readLC ConRon.Refine.HashMap2.KeysOk_true trivial hp
      have hvals := memo_insert_vals h2 hins.2.2.1 hinv.caches.readLVals (hdw l3 rfl)
      show AOut₀ _ pers _ _ _
      rw [EStore.ls, ← hd]
      refine AOut₀.ok (lst' := { lst with caches := { lst.caches with
          readLC := lst.caches.readLC.insert (absLIdx h) (ConRon.Refine.absLevel l3) } })
        rfl
        { hrel with caches := { hrel.caches with readLC := h1 } }
        { hinv with caches := { hinv.caches with readLC := h2, readLVals := hvals } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `read_level_m_run₀`. -/
theorem read_level_m_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LIdx} {o}
    (hrun : arena.monad.read_level_m pers st h = ok o) :
    Sim ConRon.Refine.absLevel (fun _ => True) pers lst o
      (Arena.readLevelM (absLIdx h)) := by
  refine Sim₀.toSim_of_store (read_level_m_run₀ hrel.to₀ hinv hrun) hrel.storeWF ?_
  intro b lst' hx
  rw [readLevelM_run] at hx
  split at hx
  · cases hx; rfl
  · split at hx
    · cases hx
    · cases hx; rfl

theorem readLevelsM_run (lst : AState) (h : LsIdx) :
    (Arena.readLevelsM h).run lst
      = match lst.caches.readLsC[h]? with
        | some x => Except.ok (x, lst)
        | none =>
          match denoteLs lst.store.lss h with
          | none => Except.error (.internal "arena: dangling level-list handle")
          | some x => Except.ok (x,
              { lst with caches := { lst.caches with
                  readLsC := lst.caches.readLsC.insert h x } }) := by
  show (match lst.caches.readLsC[h]? with
        | some x => (pure x : AM _)
        | none =>
          match denoteLs lst.store.lss h with
          | none => (Arena.failDanglingLs : AM _)
          | some x => (do
              set { ({ lst with caches := { lst.caches with readLsC := ∅ } } : AState)
                with caches := { ({ lst with caches :=
                  { lst.caches with readLsC := ∅ } } : AState).caches with
                  readLsC := lst.caches.readLsC.insert h x } }
              pure x : AM _)).run lst = _
  cases lst.caches.readLsC[h]? with
  | some x => rfl
  | none => cases denoteLs lst.store.lss h <;> rfl

theorem read_levels_m_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.read_levels_m pers st h = ok o) :
    Sim₀ ConRon.Refine.absLevels pers lst o
      (Arena.readLevelsM (absLsIdx h)) := by
  rw [arena.monad.read_levels_m] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lsidx_eq2 hinv.caches.readLsC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.readLsC h trivial
  rw [← hto] at hrelk
  show AOut₀ _ pers o.1 o.2 _
  rw [readLevelsM_run]
  cases hrc : r with
  | some x =>
    rw [hrc] at hrun hrelk
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok n, st) = o := Result.ok_injective hrun
    rw [← ho]
    simp only [Option.map_some] at hrelk
    rw [← hrelk]
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    show Except.ok (ConRon.Refine.absLevels x, lst)
      = Except.ok (ConRon.Refine.absLevels n, lst)
    rw [ConRon.Refine.absLevels, ConRon.Refine.absLevels, level_list_dup_val hn]
  | none =>
    rw [hrc] at hrun hrelk
    simp only [Option.map_none] at hrelk
    rw [← hrelk]
    obtain ⟨ls0, hls0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ls_s] at hls0
    have hls2 : ls0 = st.store.lss := (Result.ok_injective hls0).symm
    subst hls2
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hd := denote_ls_abs hrel.store.lss hv
    have hdw := denote_ls_wf hinv.store.lss hv
    cases hvc : v with
    | none =>
      rw [hvc] at hrun hd
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrre := fail_run hrr
      subst hrre
      have ho : ((core.result.Result.Err
        (kernel.core_types.CheckError.Internal w)), st) = o := Result.ok_injective hrun
      rw [← ho]
      show AErrSim _ _
      rw [← hd]
      exact AErrSim.internal rfl
    | some x =>
      rw [hvc] at hrun hd hdw
      obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨l3, hl3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨old, hm⟩ := p
      rw [dupId_lsidx _ _ hk1] at hp
      have ho : (core.result.Result.Ok x,
        ({ st with caches := { st.caches with read_ls_c := hm } } :
          arena.monad.AState)) = o := Result.ok_injective hrun
      rw [← ho]
      have hl3v : l3.val = x.val := level_list_dup_val hl3
      have hrelLs : RelOn (fun _ => True) st.caches.read_ls_c
          lst.caches.readLsC absLsIdx ConRon.Refine.absLevels := hrel.caches.readLsC
      obtain ⟨h1, h2⟩ := memo_insert_step lsidx_eq2 absLsIdx_inj hinv.caches.readLsC
        hrelLs hp
      have hins := ConRon.Refine.HashMap2.insert_refines_wf lsidx_eq2
        hinv.caches.readLsC ConRon.Refine.HashMap2.KeysOk_true trivial hp
      have hxw : ConRon.Refine.LevelsWF l3 := by
        intro u hu; rw [hl3v] at hu; exact hdw x rfl u hu
      have hvals := memo_insert_vals h2 hins.2.2.1 hinv.caches.readLsVals hxw
      have habs : ConRon.Refine.absLevels l3 = ConRon.Refine.absLevels x := by
        rw [ConRon.Refine.absLevels, ConRon.Refine.absLevels, hl3v]
      show AOut₀ _ pers _ _ _
      rw [← hd]
      refine AOut₀.ok (lst' := { lst with caches := { lst.caches with
          readLsC := lst.caches.readLsC.insert (absLsIdx h)
            (ConRon.Refine.absLevels x) } })
        rfl
        { hrel with caches := { hrel.caches with readLsC := habs ▸ h1 } }
        { hinv with caches := { hinv.caches with readLsC := h2, readLsVals := hvals } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `read_levels_m_run₀`. -/
theorem read_levels_m_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.read_levels_m pers st h = ok o) :
    Sim ConRon.Refine.absLevels (fun _ => True) pers lst o
      (Arena.readLevelsM (absLsIdx h)) := by
  refine Sim₀.toSim_of_store (read_levels_m_run₀ hrel.to₀ hinv hrun) hrel.storeWF ?_
  intro b lst' hx
  rw [readLevelsM_run] at hx
  split at hx
  · cases hx; rfl
  · split at hx
    · cases hx
    · cases hx; rfl

/-- The port's `read_names_m_from` carries an accumulator the twin does not;
this is what puts the two runs on the same footing. -/
def prependOut (pre : List ConLeche.Name)
    (x : Except Arena.CheckError (List ConLeche.Name × AState)) :
    Except Arena.CheckError (List ConLeche.Name × AState) :=
  match x with
  | .ok p => .ok (pre ++ p.1, p.2)
  | .error e => .error e

@[simp] theorem prependOut_nil (x) : prependOut [] x = x := by
  cases x with
  | error e => rfl
  | ok p => show Except.ok ([] ++ p.1, p.2) = _; rw [List.nil_append]

theorem readNamesM_run_cons (lst : AState) (h : NIdx) (hs : List NIdx) :
    (Arena.readNamesM (h :: hs)).run lst
      = ((Arena.readNameM h).run lst).bind fun p =>
          ((Arena.readNamesM hs).run p.2).bind fun q => Except.ok (p.1 :: q.1, q.2) := by
  show (do let x ← Arena.readNameM h; let xs ← Arena.readNamesM hs;
           pure (x :: xs) : AM _).run lst = _
  rw [StateT.run_bind]
  congr 1

/-- `Arena.readNamesM` leaves the store alone: it reads and fills the cache. -/
theorem readNamesM_store : ∀ (l : List NIdx) (lst : AState) (b : List ConLeche.Name)
    (lst' : AState), (Arena.readNamesM l).run lst = .ok (b, lst') →
    lst'.store = lst.store
  | [], lst, b, lst', hx => by cases hx; rfl
  | h :: hs, lst, b, lst', hx => by
    rw [readNamesM_run_cons] at hx
    have h1 : ∀ c lst1, (Arena.readNameM h).run lst = .ok (c, lst1) →
        lst1.store = lst.store := by
      intro c lst1 hx1
      rw [readNameM_run] at hx1
      split at hx1
      · cases hx1; rfl
      · split at hx1
        · cases hx1
        · cases hx1; rfl
    cases hr : (Arena.readNameM h).run lst with
    | error e => rw [hr] at hx; cases hx
    | ok p =>
      rw [hr] at hx
      cases hq : (Arena.readNamesM hs).run p.2 with
      | error e => simp only [hq, Except.bind] at hx; cases hx
      | ok q =>
        simp only [hq, Except.bind] at hx
        cases hx
        rw [readNamesM_store hs p.2 q.1 q.2 hq, h1 p.1 p.2 hr]

theorem read_names_m_from_abs₀ {pers} {ks : alloc.vec.Vec arena.handle.NIdx} :
    ∀ k {st : arena.monad.AState} {lst : AState}, AStateRel₀ pers st lst →
      AStateInv pers st → ∀ (i : Std.Usize) (out : alloc.vec.Vec kernel.name.Name),
      ks.length - i.val ≤ k → ∀ {o},
      arena.monad.read_names_m_from pers st ks i out = ok o →
      AOut₀ (fun v : alloc.vec.Vec kernel.name.Name => v.val.map ConRon.Refine.absName)
        pers o.1 o.2
        (prependOut (out.val.map ConRon.Refine.absName)
          ((Arena.readNamesM ((ks.val.drop i.val).map absNIdx)).run lst)) := by
  intro k
  induction k with
  | zero =>
    intro st lst hrel hinv i out hk o hrun
    rw [arena.monad.read_names_m_from.eq_def] at hrun; simp only [] at hrun
    rw [if_pos (by scalar_tac)] at hrun
    rw [List.drop_eq_nil_of_le (by scalar_tac), List.map_nil]
    have ho : ((core.result.Result.Ok out : core.result.Result _ _), st) = o :=
      Result.ok_injective hrun
    rw [← ho]
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    show prependOut _ (Except.ok (([] : List ConLeche.Name), lst)) = _
    show Except.ok (out.val.map ConRon.Refine.absName ++ [], lst) = _
    rw [List.append_nil]
  | succ k ih =>
    intro st lst hrel hinv i out hk o hrun
    rw [arena.monad.read_names_m_from.eq_def] at hrun; simp only [] at hrun
    split at hrun
    · rw [List.drop_eq_nil_of_le (by scalar_tac), List.map_nil]
      have ho : ((core.result.Result.Ok out : core.result.Result _ _), st) = o :=
        Result.ok_injective hrun
      rw [← ho]
      refine AOut₀.ok (lst' := lst) ?_ hrel hinv
      show prependOut _ (Except.ok (([] : List ConLeche.Name), lst)) = _
      show Except.ok (out.val.map ConRon.Refine.absName ++ [], lst) = _
      rw [List.append_nil]
    · rename_i hlt
      have hb : i.val < ks.length := by scalar_tac
      obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hnv : ks.val[i.val] = n := by
        have h1 : ks.val[i.val]? = some n := vec_index_some hn
        rw [List.getElem?_eq_getElem hb] at h1
        exact (Option.some.injEq _ _ ▸ h1)
      obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r, st1⟩ := p1
      have hstep := read_name_m_run₀ hrel hinv hp1
      rw [List.drop_eq_getElem_cons hb, List.map_cons, hnv, readNamesM_run_cons]
      cases hrc : r with
      | Err e =>
        rw [hrc] at hstep
        simp only [hrc] at hrun
        have herr : AErrSim e ((Arena.readNameM (absNIdx n)).run lst) := hstep
        have ho : ((core.result.Result.Err e : core.result.Result _ _), st1) = o :=
          Result.ok_injective hrun
        rw [← ho]
        refine AOut₀.err ?_
        intro kk hkk
        obtain ⟨le, hle, hk2⟩ := herr kk hkk
        exact ⟨le, by rw [hle]; rfl, hk2⟩
      | Ok x =>
        rw [hrc] at hstep
        simp only [hrc] at hrun
        obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hstep
        rw [hx1]
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hout1v : out1.val = out.val ++ [x] := ConRon.Refine.vec_push_val hout1
        have hih := ih hrel1 hinv1 i2 out1 (by scalar_tac) hrun
        rw [hi2v] at hih
        show AOut₀ _ pers o.1 o.2
          (prependOut _ (((Arena.readNamesM
            ((ks.val.drop (i.val + 1)).map absNIdx)).run lst1).bind _))
        cases hy : (Arena.readNamesM ((ks.val.drop (i.val + 1)).map absNIdx)).run lst1 with
        | error e =>
          rw [hy] at hih
          cases hoc : o.1 with
          | Ok v =>
            rw [hoc] at hih
            obtain ⟨lst2, hcontra, -⟩ := hih
            exact absurd hcontra (by simp [prependOut])
          | Err e2 =>
            rw [hoc] at hih
            have herr : AErrSim e2 (prependOut (out1.val.map ConRon.Refine.absName)
              (Except.error e)) := hih
            refine AOut₀.err ?_
            intro kk hkk
            obtain ⟨le, hle, hk2⟩ := herr kk hkk
            refine ⟨le, ?_, hk2⟩
            have : (Except.error e : Except Arena.CheckError (List ConLeche.Name × AState))
                = Except.error le := by
              have := hle; simp only [prependOut] at this; exact this
            simp only [Except.error.injEq] at this
            rw [← this]; rfl
        | ok q =>
          rw [hy] at hih
          cases hoc : o.1 with
          | Err e2 =>
            rw [hoc] at hih
            have herr : AErrSim e2 (prependOut (out1.val.map ConRon.Refine.absName)
              (Except.ok q)) := hih
            refine AOut₀.err ?_
            intro kk hkk
            obtain ⟨le, hle, -⟩ := herr kk hkk
            simp only [prependOut] at hle
            exact absurd hle (by simp)
          | Ok v =>
            rw [hoc] at hih
            obtain ⟨lst2, hv2, hrel2, hinv2⟩ := hih
            simp only [prependOut, Except.ok.injEq, Prod.mk.injEq] at hv2
            refine AOut₀.ok (lst' := lst2) ?_ hrel2 hinv2
            show Except.ok (out.val.map ConRon.Refine.absName
              ++ (ConRon.Refine.absName x :: q.1), q.2) = _
            rw [← hv2.2]
            have hq1 : out1.val.map ConRon.Refine.absName ++ q.1
                = v.val.map ConRon.Refine.absName := hv2.1
            rw [hout1v] at hq1
            simp only [List.map_append, List.map_cons, List.map_nil,
              List.append_assoc, List.cons_append, List.nil_append] at hq1
            rw [hq1]

theorem read_names_m_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {ks : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.monad.read_names_m pers st ks = ok o) :
    Sim₀ ConRon.Refine.absNames pers lst o
      (Arena.readNamesM (ks.val.map absNIdx)) := by
  rw [arena.monad.read_names_m] at hrun
  have hh := read_names_m_from_abs₀ ks.length hrel hinv 0#usize
    (alloc.vec.Vec.new kernel.name.Name) (by scalar_tac) hrun
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hh
  rw [show ((alloc.vec.Vec.new kernel.name.Name).val.map ConRon.Refine.absName)
        = ([] : List ConLeche.Name) from rfl, prependOut_nil] at hh
  exact hh

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `read_names_m_run₀`. -/
theorem read_names_m_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {ks : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.monad.read_names_m pers st ks = ok o) :
    Sim ConRon.Refine.absNames (fun _ => True) pers lst o
      (Arena.readNamesM (ks.val.map absNIdx)) := by
  exact Sim₀.toSim_of_store (read_names_m_run₀ hrel.to₀ hinv hrun) hrel.storeWF
    (fun _ _ hx => readNamesM_store _ _ _ _ hx)

/-! ## The thirteen memo writes and the eleven clears -/

/-- `arena::monad::inst1_set` against `Arena.inst1Set`. -/
theorem inst1_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst1_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.inst1Set (absEIdxNat k) (absEIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with inst1C := h1 } }
    { hinv with memos := { hinv.memos with inst1C := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst1_set_run₀`. -/
theorem inst1_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst1_set st k r = ok st') :
    SimS pers lst st' (Arena.inst1Set (absEIdxNat k) (absEIdx r)) :=
  SimS₀.toSimS (by apply inst1_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::inst_l_set` against `Arena.instLSet`. -/
theorem inst_l_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst_l_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.instLSet (absEIdxNat k) (absEIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with instLC := h1 } }
    { hinv with memos := { hinv.memos with instLC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst_l_set_run₀`. -/
theorem inst_l_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst_l_set st k r = ok st') :
    SimS pers lst st' (Arena.instLSet (absEIdxNat k) (absEIdx r)) :=
  SimS₀.toSimS (by apply inst_l_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::lift_set` against `Arena.liftSet`. -/
theorem lift_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.lift_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.liftSet (absEIdxNat k) (absEIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with liftC := h1 } }
    { hinv with memos := { hinv.memos with liftC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `lift_set_run₀`. -/
theorem lift_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.lift_set st k r = ok st') :
    SimS pers lst st' (Arena.liftSet (absEIdxNat k) (absEIdx r)) :=
  SimS₀.toSimS (by apply lift_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::reset_set` against `Arena.resetSet`. -/
theorem reset_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.reset_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.resetSet (absEIdxNat k) (absEIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with resetC := h1 } }
    { hinv with memos := { hinv.memos with resetC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `reset_set_run₀`. -/
theorem reset_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.reset_set st k r = ok st') :
    SimS pers lst st' (Arena.resetSet (absEIdxNat k) (absEIdx r)) :=
  SimS₀.toSimS (by apply reset_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::rename_set` against `Arena.renameSet`. -/
theorem rename_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.rename_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.renameSet (absEIdxNat k) (absEIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with renameC := h1 } }
    { hinv with memos := { hinv.memos with renameC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `rename_set_run₀`. -/
theorem rename_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.rename_set st k r = ok st') :
    SimS pers lst st' (Arena.renameSet (absEIdxNat k) (absEIdx r)) :=
  SimS₀.toSimS (by apply rename_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::abs1_set` against `Arena.abs1Set`. -/
theorem abs1_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.abs1_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.abs1Set (absEIdxNat k) (absEIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with abs1C := h1 } }
    { hinv with memos := { hinv.memos with abs1C := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `abs1_set_run₀`. -/
theorem abs1_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.abs1_set st k r = ok st') :
    SimS pers lst st' (Arena.abs1Set (absEIdxNat k) (absEIdx r)) :=
  SimS₀.toSimS (by apply abs1_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::lower_set` against `Arena.lowerSet`. -/
theorem lower_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.lower_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.lowerSet (absEIdxNat k) (absEIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with lowerC := h1 } }
    { hinv with memos := { hinv.memos with lowerC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `lower_set_run₀`. -/
theorem lower_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.lower_set st k r = ok st') :
    SimS pers lst st' (Arena.lowerSet (absEIdxNat k) (absEIdx r)) :=
  SimS₀.toSimS (by apply lower_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::inst1_l_set` against `Arena.inst1LSet`. -/
theorem inst1_l_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst1_l_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.inst1LSet (absEIdxNat k) (absEIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with inst1LC := h1 } }
    { hinv with memos := { hinv.memos with inst1LC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst1_l_set_run₀`. -/
theorem inst1_l_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst1_l_set st k r = ok st') :
    SimS pers lst st' (Arena.inst1LSet (absEIdxNat k) (absEIdx r)) :=
  SimS₀.toSimS (by apply inst1_l_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::inst_lp_set` against `Arena.instLPSet`. -/
theorem inst_lp_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst_lp_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.instLPSet (absEIdxNat k) (absEIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with instLPC := h1 } }
    { hinv with memos := { hinv.memos with instLPC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst_lp_set_run₀`. -/
theorem inst_lp_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {r : arena.handle.EIdx} {st'}
    (hrun : arena.monad.inst_lp_set st k r = ok st') :
    SimS pers lst st' (Arena.instLPSet (absEIdxNat k) (absEIdx r)) :=
  SimS₀.toSimS (by apply inst_lp_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::bvar_b_set` against `Arena.bvarBSet`. -/
theorem bvar_b_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.EIdx} {r : Std.U64} {st'}
    (hrun : arena.monad.bvar_b_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.bvarBSet (absEIdx k) (absU r)) := by
  rw [arena.monad.bvar_b_set] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  have hst : st' = { st with memos := { st.memos with bvar_b_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj hinv.memos.bvarBC
    hrel.memos.bvarBC hp
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with bvarBC := h1 } }
    { hinv with memos := { hinv.memos with bvarBC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `bvar_b_set_run₀`. -/
theorem bvar_b_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.EIdx} {r : Std.U64} {st'}
    (hrun : arena.monad.bvar_b_set st k r = ok st') :
    SimS pers lst st' (Arena.bvarBSet (absEIdx k) (absU r)) :=
  SimS₀.toSimS (by apply bvar_b_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::fvar_b_set` against `Arena.fvarBSet`. -/
theorem fvar_b_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.EIdx} {r : Std.U64} {st'}
    (hrun : arena.monad.fvar_b_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.fvarBSet (absEIdx k) (absU r)) := by
  rw [arena.monad.fvar_b_set] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm⟩ := p
  have hst : st' = { st with memos := { st.memos with fvar_b_c := hm } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj hinv.memos.fvarBC
    hrel.memos.fvarBC hp
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with fvarBC := h1 } }
    { hinv with memos := { hinv.memos with fvarBC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `fvar_b_set_run₀`. -/
theorem fvar_b_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.EIdx} {r : Std.U64} {st'}
    (hrun : arena.monad.fvar_b_set st k r = ok st') :
    SimS pers lst st' (Arena.fvarBSet (absEIdx k) (absU r)) :=
  SimS₀.toSimS (by apply fvar_b_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::inst_lp_l_set` against `Arena.instLPLSet`. -/
theorem inst_lp_l_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.LIdx} {r : arena.handle.LIdx} {st'}
    (hrun : arena.monad.inst_lp_l_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.instLPLSet (absLIdx k) (absLIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with instLPLC := h1 } }
    { hinv with memos := { hinv.memos with instLPLC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst_lp_l_set_run₀`. -/
theorem inst_lp_l_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.LIdx} {r : arena.handle.LIdx} {st'}
    (hrun : arena.monad.inst_lp_l_set st k r = ok st') :
    SimS pers lst st' (Arena.instLPLSet (absLIdx k) (absLIdx r)) :=
  SimS₀.toSimS (by apply inst_lp_l_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::inst_lp_ls_set` against `Arena.instLPLsSet`. -/
theorem inst_lp_ls_set_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.LsIdx} {r : arena.handle.LsIdx} {st'}
    (hrun : arena.monad.inst_lp_ls_set st k r = ok st') :
    SimS₀ pers lst st' (Arena.instLPLsSet (absLsIdx k) (absLsIdx r)) := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with instLPLsC := h1 } }
    { hinv with memos := { hinv.memos with instLPLsC := h2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst_lp_ls_set_run₀`. -/
theorem inst_lp_ls_set_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.handle.LsIdx} {r : arena.handle.LsIdx} {st'}
    (hrun : arena.monad.inst_lp_ls_set st k r = ok st') :
    SimS pers lst st' (Arena.instLPLsSet (absLsIdx k) (absLsIdx r)) :=
  SimS₀.toSimS (by apply inst_lp_ls_set_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::inst1_clear` against `Arena.inst1Clear`. -/
theorem inst1_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst1_clear st = ok st') :
    SimS₀ pers lst st' Arena.inst1Clear := by
  rw [arena.monad.inst1_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with inst1_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.inst1C hp0
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with inst1C := g0 } }
    { hinv with memos := { hinv.memos with inst1C := i0 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst1_clear_run₀`. -/
theorem inst1_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst1_clear st = ok st') :
    SimS pers lst st' Arena.inst1Clear :=
  SimS₀.toSimS (by apply inst1_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::inst_l_clear` against `Arena.instLClear`. -/
theorem inst_l_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst_l_clear st = ok st') :
    SimS₀ pers lst st' Arena.instLClear := by
  rw [arena.monad.inst_l_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with inst_l_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.instLC hp0
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with instLC := g0 } }
    { hinv with memos := { hinv.memos with instLC := i0 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst_l_clear_run₀`. -/
theorem inst_l_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst_l_clear st = ok st') :
    SimS pers lst st' Arena.instLClear :=
  SimS₀.toSimS (by apply inst_l_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::lift_clear` against `Arena.liftClear`. -/
theorem lift_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.lift_clear st = ok st') :
    SimS₀ pers lst st' Arena.liftClear := by
  rw [arena.monad.lift_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with lift_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.liftC hp0
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with liftC := g0 } }
    { hinv with memos := { hinv.memos with liftC := i0 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `lift_clear_run₀`. -/
theorem lift_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.lift_clear st = ok st') :
    SimS pers lst st' Arena.liftClear :=
  SimS₀.toSimS (by apply lift_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::reset_clear` against `Arena.resetClear`. -/
theorem reset_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.reset_clear st = ok st') :
    SimS₀ pers lst st' Arena.resetClear := by
  rw [arena.monad.reset_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with reset_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.resetC hp0
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with resetC := g0 } }
    { hinv with memos := { hinv.memos with resetC := i0 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `reset_clear_run₀`. -/
theorem reset_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.reset_clear st = ok st') :
    SimS pers lst st' Arena.resetClear :=
  SimS₀.toSimS (by apply reset_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::rename_clear` against `Arena.renameClear`. -/
theorem rename_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.rename_clear st = ok st') :
    SimS₀ pers lst st' Arena.renameClear := by
  rw [arena.monad.rename_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with rename_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.renameC hp0
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with renameC := g0 } }
    { hinv with memos := { hinv.memos with renameC := i0 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `rename_clear_run₀`. -/
theorem rename_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.rename_clear st = ok st') :
    SimS pers lst st' Arena.renameClear :=
  SimS₀.toSimS (by apply rename_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::abs1_clear` against `Arena.abs1Clear`. -/
theorem abs1_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.abs1_clear st = ok st') :
    SimS₀ pers lst st' Arena.abs1Clear := by
  rw [arena.monad.abs1_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with abs1_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.abs1C hp0
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with abs1C := g0 } }
    { hinv with memos := { hinv.memos with abs1C := i0 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `abs1_clear_run₀`. -/
theorem abs1_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.abs1_clear st = ok st') :
    SimS pers lst st' Arena.abs1Clear :=
  SimS₀.toSimS (by apply abs1_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::lower_clear` against `Arena.lowerClear`. -/
theorem lower_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.lower_clear st = ok st') :
    SimS₀ pers lst st' Arena.lowerClear := by
  rw [arena.monad.lower_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with lower_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.lowerC hp0
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with lowerC := g0 } }
    { hinv with memos := { hinv.memos with lowerC := i0 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `lower_clear_run₀`. -/
theorem lower_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.lower_clear st = ok st') :
    SimS pers lst st' Arena.lowerClear :=
  SimS₀.toSimS (by apply lower_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::inst1_l_clear` against `Arena.inst1LClear`. -/
theorem inst1_l_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst1_l_clear st = ok st') :
    SimS₀ pers lst st' Arena.inst1LClear := by
  rw [arena.monad.inst1_l_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with inst1_l_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdxNat) (absV := absEIdx)
    hinv.memos.inst1LC hp0
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with inst1LC := g0 } }
    { hinv with memos := { hinv.memos with inst1LC := i0 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst1_l_clear_run₀`. -/
theorem inst1_l_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst1_l_clear st = ok st') :
    SimS pers lst st' Arena.inst1LClear :=
  SimS₀.toSimS (by apply inst1_l_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::inst_lp_clear` against `Arena.instLPClear`. -/
theorem inst_lp_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst_lp_clear st = ok st') :
    SimS₀ pers lst st' Arena.instLPClear := by
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
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with instLPC := g0, instLPLC := g1, instLPLsC := g2 } }
    { hinv with memos := { hinv.memos with instLPC := i0, instLPLC := i1, instLPLsC := i2 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `inst_lp_clear_run₀`. -/
theorem inst_lp_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.inst_lp_clear st = ok st') :
    SimS pers lst st' Arena.instLPClear :=
  SimS₀.toSimS (by apply inst_lp_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::bvar_b_clear` against `Arena.bvarBClear`. -/
theorem bvar_b_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.bvar_b_clear st = ok st') :
    SimS₀ pers lst st' Arena.bvarBClear := by
  rw [arena.monad.bvar_b_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with bvar_b_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdx) (absV := absU)
    hinv.memos.bvarBC hp0
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with bvarBC := g0 } }
    { hinv with memos := { hinv.memos with bvarBC := i0 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `bvar_b_clear_run₀`. -/
theorem bvar_b_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.bvar_b_clear st = ok st') :
    SimS pers lst st' Arena.bvarBClear :=
  SimS₀.toSimS (by apply bvar_b_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)

/-- `arena::monad::fvar_b_clear` against `Arena.fvarBClear`. -/
theorem fvar_b_clear_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.fvar_b_clear st = ok st') :
    SimS₀ pers lst st' Arena.fvarBClear := by
  rw [arena.monad.fvar_b_clear] at hrun
  obtain ⟨hm0, hp0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : st' = { st with memos := { st.memos with fvar_b_c := hm0 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨g0, i0⟩ := memo_clear_step (absK := absEIdx) (absV := absU)
    hinv.memos.fvarBC hp0
  exact SimS₀.mk rfl { hrel with memos := { hrel.memos with fvarBC := g0 } }
    { hinv with memos := { hinv.memos with fvarBC := i0 } }

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): use `fvar_b_clear_run₀`. -/
theorem fvar_b_clear_run {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {st'}
    (hrun : arena.monad.fvar_b_clear st = ok st') :
    SimS pers lst st' Arena.fvarBClear :=
  SimS₀.toSimS (by apply fvar_b_clear_run₀ (hrel := hrel.to₀) <;> assumption)
    (fun _ hx => by cases hx; exact ⟨hrel.storeWF, Ext.refl _⟩)
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

/-- info: 'ConRon.Refine2.derived_e_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms derived_e_run₀

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

/-- info: 'ConRon.Refine2.view_l_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_l_run₀

/-- info: 'ConRon.Refine2.view_ls_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_ls_run₀

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

/-! ## The tag/view agreement (task #97-P5-3, task #97-P5-Arms)

`EStore_view_tagOf` is the lemma task #97-P5-2 §10 argued for and did not
mechanise: **`view` answers the view whose constructor is the handle's own
tag, UNCONDITIONALLY** — no `StoreWF`.  It is what makes the eight tag-first
readers of `ExprOps/Read.lean` provable at `EResolves` alone rather than at
`StoreWF`, and the Core tier's gated arms want the same.

Two tiers found it independently (this one and `Refine2/Core/Arms/Sort.lean`,
whose own note says "this belongs in `Refine2/Specs.lean` beside `view_run`;
it is here because this tier may not edit that file").  The text below is that
tier's, verbatim, at its own names — **so the migration is a deletion there
and nothing here**. -/

/-- **`ETables.get` answers the view whose constructor is the tag it tested** —
the ten-way half of the agreement, once.  `ENodeView.tagOf` is
`Arena/WFProofs.lean`'s and `tag_cases` is its ten-way `if` splitter, so the
proof is the same six lines eight times. -/
theorem ETables_get_tagOf {t : ETables} {i : EIdx} {v : ENodeView}
    (h : t.get i = some v) : i.tag = v.tagOf := by
  simp only [ETables.get] at h
  tag_cases h
  · revert h
    cases t.bvars.node? i.idxNat with
    | none => simp
    | some r =>
      intro h; simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]; exact eq_of_beq hc
  · revert h
    cases t.fvars.node? i.idxNat with
    | none => simp
    | some r =>
      intro h; simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]; exact eq_of_beq hc
  · revert h
    cases t.sorts.node? i.idxNat with
    | none => simp
    | some r =>
      intro h; simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]; exact eq_of_beq hc
  · revert h
    cases t.consts.node? i.idxNat with
    | none => simp
    | some r =>
      intro h; simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]; exact eq_of_beq hc
  · revert h
    cases t.apps.node? i.idxNat with
    | none => simp
    | some r =>
      intro h; simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]; exact eq_of_beq hc
  · simp at h
  · revert h
    cases t.lets.node? i.idxNat with
    | none => simp
    | some r =>
      intro h; simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]; exact eq_of_beq hc
  · revert h
    cases t.lits.node? i.idxNat with
    | none => simp
    | some r =>
      intro h; simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]; exact eq_of_beq hc
  · revert h
    cases t.projs.node? i.idxNat with
    | none => simp
    | some r =>
      intro h; simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]; exact eq_of_beq hc
  · simp at h

/-- **`view` answers the view whose constructor is the handle's own tag,
UNCONDITIONALLY** — task #97-P5-2 §10's `estore_view_tagOf`, which that section
predicted is free of `StoreWF` and which this tier needs in both its halves.
The binder arm is the one that is not `ETables_get_tagOf`: `view` builds
`eBindView i.tag …`, whose `tagOf` is `i.tag` exactly under `ETag.isBind`.

**This belongs in `Refine2/Specs.lean`** beside `view_run`; it is here because
this tier may not edit that file, and the migration is the two lines that
name it. -/
theorem EStore_view_tagOf {st : EStore} {i : EIdx} {v : ENodeView}
    (h : st.view i = some v) : i.tag = v.tagOf := by
  rw [EStore.view] at h
  by_cases hb : ETag.isBind i.tag = true
  · rw [if_pos hb] at h
    split at h
    · exact absurd h (by simp)
    · rename_i ty b m _
      simp only [Option.some.injEq] at h
      rw [← h, eBindView]
      by_cases hl : i.tag == ETag.lam
      · rw [if_pos hl]; exact eq_of_beq hl
      · rw [if_neg hl]
        simp only [ETag.isBind, Bool.or_eq_true] at hb
        rcases hb with hx | hx
        · exact absurd hx hl
        · exact eq_of_beq hx
  · rw [if_neg hb] at h
    by_cases hp : i.isPersistent
    · rw [if_pos hp] at h; exact ETables_get_tagOf h
    · rw [if_neg hp] at h
      by_cases hs : st.scratchOn
      · rw [if_pos hs] at h; exact ETables_get_tagOf h
      · rw [if_neg hs] at h; exact absurd h (by simp)

/-- info: 'ConRon.Refine2.EStore_view_tagOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EStore_view_tagOf


/-- info: 'ConRon.Refine2.internLamIE_run_of_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internLamIE_run_of_cap

/-- info: 'ConRon.Refine2.internForallEIE_run_of_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internForallEIE_run_of_cap

/-- info: 'ConRon.Refine2.intern_e_lam_i_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_lam_i_run₀

/-- info: 'ConRon.Refine2.intern_e_forall_e_i_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_forall_e_i_run₀

/-- info: 'ConRon.Refine2.intern_e_bind_i_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_bind_i_run

/-! ## The axiom census, task #97-P5-3 round 3

Finding 14's two halves and the binder composition of §2. -/

/-- info: 'ConRon.Refine2.tbl_not_full_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tbl_not_full_size

/-- info: 'ConRon.Arena.persFind?_none_of_echild' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms persFind?_none_of_echild

/-- info: 'ConRon.Arena.hchild_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hchild_const

/-- info: 'ConRon.Arena.hchild_let_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hchild_let_e

/-- info: 'ConRon.Refine2.internE_run_of_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internE_run_of_caps

/-- info: 'ConRon.Refine2.estore_intern_lam_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_lam_abs

/-- info: 'ConRon.Refine2.estore_intern_forall_e_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_forall_e_abs

/-- info: 'ConRon.Refine2.intern_e_lam_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_lam_run

/-- info: 'ConRon.Refine2.intern_e_forall_e_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_forall_e_run

/-! ### Task #97-P5-Specs: the eight readbacks and their machinery -/

/-- info: 'ConRon.Refine2.denote_n_aux_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms denote_n_aux_abs

/-- info: 'ConRon.Refine2.denote_n_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms denote_n_abs

/-- info: 'ConRon.Refine2.read_name_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_name_run₀

/-- info: 'ConRon.Refine2.denote_l_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms denote_l_abs

/-- info: 'ConRon.Refine2.read_level_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_level_run₀

/-- info: 'ConRon.Refine2.denote_ls_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms denote_ls_abs

/-- info: 'ConRon.Refine2.read_levels_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_levels_run₀

/-- info: 'ConRon.Refine2.read_names_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_names_run₀

/-- info: 'ConRon.Refine2.denote_n_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms denote_n_wf

/-- info: 'ConRon.Refine2.denote_l_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms denote_l_wf

/-- info: 'ConRon.Refine2.denote_ls_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms denote_ls_wf

/-- info: 'ConRon.Refine2.memo_insert_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memo_insert_vals

/-- info: 'ConRon.Refine2.read_name_m_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_name_m_run

/-- info: 'ConRon.Refine2.read_level_m_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_level_m_run

/-- info: 'ConRon.Refine2.read_levels_m_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_levels_m_run

/-- info: 'ConRon.Refine2.read_names_m_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_names_m_run

/-- info: 'ConRon.Refine2.intern_e_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_run

/-! ### Task #97-P5-Fresh: the promote window -/

/-- info: 'ConRon.Refine2.lstore_intern_persistent_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lstore_intern_persistent_abs

/-- info: 'ConRon.Refine2.lsstore_intern_persistent_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lsstore_intern_persistent_abs

/-- info: 'ConRon.Refine2.estore_intern_name_persistent_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_name_persistent_abs

/-- info: 'ConRon.Refine2.estore_intern_level_persistent_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_level_persistent_abs

/-- info: 'ConRon.Refine2.estore_intern_levels_persistent_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_levels_persistent_abs

/-- info: 'ConRon.Refine2.intern_persistent_n_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_persistent_n_run

/-- info: 'ConRon.Refine2.intern_persistent_l_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_persistent_l_run₀

/-- info: 'ConRon.Refine2.intern_persistent_ls_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_persistent_ls_run₀


/-! ### Task #97-P5-Specs round 3: the four transient-tree walks -/

/-- info: 'ConRon.Refine2.internName_run_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internName_run_denote

/-- info: 'ConRon.Refine2.internLevel_run_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internLevel_run_denote

/-- info: 'ConRon.Refine2.internLevelList_run_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internLevelList_run_denote

/-- info: 'ConRon.Refine2.internLevels_run_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms internLevels_run_denote

/-- info: 'ConRon.Refine2.intern_n_node_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_n_node_flags

/-- info: 'ConRon.Refine2.intern_l_node_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_l_node_flags

/-- info: 'ConRon.Refine2.intern_ls_node_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_ls_node_flags

/-- info: 'ConRon.Refine2.intern_name_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_name_run₀

/-- info: 'ConRon.Refine2.intern_level_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_level_run₀

/-- info: 'ConRon.Refine2.intern_level_list_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_level_list_run₀

/-- info: 'ConRon.Refine2.intern_levels_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_levels_run₀


/-! ### Task #97-P5-Specs round 3: the E tier's own `intern_persistent` -/

/-- info: 'ConRon.Refine2.etables_find_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms etables_find_abs

/-- info: 'ConRon.Refine2.etables_not_full_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms etables_not_full_size

/-- info: 'ConRon.Refine2.etables_push_pers_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms etables_push_pers_abs

/-- info: 'ConRon.Refine2.estore_der_of_view_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_der_of_view_obs

/-- info: 'ConRon.Refine2.estore_intern_bm_persistent_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_bm_persistent_abs

/-- info: 'ConRon.Refine2.estore_intern_persistent_abs'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_intern_persistent_abs'

/-- info: 'ConRon.Refine2.intern_persistent_e_run₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_persistent_e_run₀


end ConRon.Refine2
