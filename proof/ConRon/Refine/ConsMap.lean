/-
# `ConRon.Refine.ConsMap` — the key-free cons table as a view of `HashMap2` (task #148)

`arena::cons_map::ConsMap<I>` is `ron::hashmap2::HashMap2<A, I>` with the key
cut out of the slot: a slot is `(g, h)`, and its key is the node record
`rows[h.row()].0` that the owning `Tbl` holds.  Every function of the module
is `HashMap2`'s function of the same name with "the slot's key" read as "the
slot's row's key".

So this file proves nothing about hashing.  It defines the **view** of a
`ConsMap` over a row vector — a `HashMap2 A I` whose slot `j` is
`Live(epoch, key, h)` when slot `j` of the `ConsMap` carries the current
epoch and its handle names the row `key` heads, and `Vacant` otherwise — and
shows, one function at a time, that each `ConsMap` operation that succeeds is
the `HashMap2` operation of the same name on the view (`*_sim`).
`Refine/HashMap2.lean`'s invariant, abstract map and specifications then apply
to the view as they stand.

The view forgets which slots are *stale*, so two facts of the `ConsMap`
itself are carried beside `HashMap2.Inv` (`KInv`): every stamp is at most the
epoch (what makes `clear`'s epoch bump empty the table — `HashMap2`'s
`Inv.stamps`, which the view cannot see), and every slot of the current epoch
names a row (what makes the view stable when the rows grow, `view_push`).

`clear`/`clear_fit` are proved directly (`clear_fit_spec`): their output is
not the `HashMap2` operation's on the view — the view of a stale slot is
`Vacant`, `HashMap2`'s is a stale `Live` — but both are the empty map.
-/
import ConRon.Refine.HashMap2WF

open Aeneas Aeneas.Std Result
open ConRon.Generated
open ConRon.Refine.HashMap (bind_eq_ok_iff uscalar_add_eq uscalar_sub_eq uscalar_div_eq
  vec_len_eq_zero_iff vec_push_eq DupId)
open ConRon.Refine.HashMap2 (Inv Inv0 KeysOk toFun sl_v slotKV liveAt ite_eq_ok
  pow2_at_least_spec max_load_for_spec dead_table_inv vacant_table_inv)

namespace ConRon.Refine.ConsMap

variable {A D I : Type}

/-! ## Vector plumbing -/

theorem vec_index_iff {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α} :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x ↔
      v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
  rcases v.val[i.val]? with _ | y <;> simp

theorem vec_index_mut_iff {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    {f : α → alloc.vec.Vec α} :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (x, f) ↔
      v.val[i.val]? = some x ∧ f = alloc.vec.Vec.set v i := by
  rw [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize]
  simp only [bind_tc_eq, bind_eq_ok_iff]
  constructor
  · rintro ⟨y, hy, h⟩
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨?_, rfl⟩
    rw [← alloc.vec.Vec.index_slice_index] at hy
    exact vec_index_iff.mp hy
  · rintro ⟨hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    rw [← alloc.vec.Vec.index_slice_index]
    exact vec_index_iff.mpr hx

/-- `Vec.map`, for the view. -/
def vmap {α β : Type} (f : α → β) (v : alloc.vec.Vec α) : alloc.vec.Vec β :=
  alloc.vec.Vec.from (v.val.map f) (by simpa using v.property)

@[simp] theorem vmap_val {α β : Type} (f : α → β) (v : alloc.vec.Vec α) :
    (vmap f v).val = v.val.map f := by simp [vmap]

theorem vmap_len {α β : Type} (f : α → β) (v : alloc.vec.Vec α) :
    alloc.vec.Vec.len (vmap f v) = alloc.vec.Vec.len v := by
  apply UScalar.eq_of_val_eq; simp

theorem vmap_set {α β : Type} (f : α → β) (v : alloc.vec.Vec α) (i : Std.Usize) (x : α) :
    vmap f (alloc.vec.Vec.set v i x) = alloc.vec.Vec.set (vmap f v) i (f x) := by
  apply alloc.vec.Vec.ext; simp [List.map_set]

theorem vmap_index {α β : Type} {f : α → β} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice β) (vmap f v) i = ok (f x) := by
  rw [vec_index_iff] at h ⊢
  simp [h]

theorem vmap_index_mut {α β : Type} {f : α → β} {v : alloc.vec.Vec α} {i : Std.Usize}
    {x : α} {g : α → alloc.vec.Vec α}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (x, g)) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice β) (vmap f v) i
      = ok (f x, alloc.vec.Vec.set (vmap f v) i) ∧ g = alloc.vec.Vec.set v i := by
  rw [vec_index_mut_iff] at h
  obtain ⟨hx, rfl⟩ := h
  refine ⟨vec_index_mut_iff.mpr ⟨by simp [hx], rfl⟩, rfl⟩

/-! ## The view -/

variable (hCH : arena.cons_map.ConsHandle I)

open Classical in
/-- **The key a handle names**: the record heading row `h.row()`, if the row
exists. -/
noncomputable def keyOf (rows : alloc.vec.Vec (A × D)) (h : I) : Option A :=
  if hx : ∃ r, hCH.row h = ok r then (rows.val[(Classical.choose hx).val]?).map Prod.fst
  else none

/-- One slot of the view: live (with its row's key) exactly when it carries
the epoch `e` and names a row. -/
noncomputable def viewSlot (rows : alloc.vec.Vec (A × D)) (e : Std.U32)
    (s : arena.cons_map.CSlot I) : ron.hashmap2.Slot A I :=
  if s.g = e then
    match keyOf hCH rows s.h with
    | some a => .Live e a s.h
    | none => .Vacant
  else .Vacant

/-- **The view**: the `HashMap2` this `ConsMap` is, over `rows`. -/
noncomputable def view (rows : alloc.vec.Vec (A × D)) (t : arena.cons_map.ConsMap I) :
    ron.hashmap2.HashMap2 A I :=
  { num_entries := t.num_entries, max_load := t.max_load, epoch := t.epoch,
    fit_hw := t.fit_hw, slots := vmap (viewSlot hCH rows t.epoch) t.slots }

/-- **What the view cannot see.**  Every stamp is at most the epoch, and every
slot of the current epoch names a row. -/
structure KInvS (rows : alloc.vec.Vec (A × D)) (e : Std.U32)
    (l : List (arena.cons_map.CSlot I)) : Prop where
  stamps : ∀ s ∈ l, s.g.val ≤ e.val
  named : ∀ s ∈ l, s.g = e → (keyOf hCH rows s.h).isSome

/-- `KInvS` of a table. -/
def KInv (rows : alloc.vec.Vec (A × D)) (t : arena.cons_map.ConsMap I) : Prop :=
  KInvS hCH rows t.epoch t.slots.val

variable {hCH}

theorem keyOf_eq {rows : alloc.vec.Vec (A × D)} {h : I} {r : Std.Usize}
    (hr : hCH.row h = ok r) : keyOf hCH rows h = (rows.val[r.val]?).map Prod.fst := by
  have hx : ∃ r, hCH.row h = ok r := ⟨r, hr⟩
  rw [keyOf, dite_eq_left hx]
  have he : r = Classical.choose hx :=
    Result.ok_injective (hr.symm.trans (Classical.choose_spec hx))
  rw [← he]

theorem keyOf_of_index {rows : alloc.vec.Vec (A × D)} {h : I} {r : Std.Usize} {a : A} {d : D}
    (hr : hCH.row h = ok r)
    (hi : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (A × D)) rows r
      = ok (a, d)) : keyOf hCH rows h = some a := by
  rw [keyOf_eq hr, vec_index_iff.mp hi]; rfl

theorem viewSlot_ne {rows : alloc.vec.Vec (A × D)} {e : Std.U32}
    {s : arena.cons_map.CSlot I} (h : ¬ s.g = e) : viewSlot hCH rows e s = .Vacant := by
  rw [viewSlot, ite_eq_right h]

theorem viewSlot_live {rows : alloc.vec.Vec (A × D)} {e : Std.U32}
    {s : arena.cons_map.CSlot I} {a : A} (h : s.g = e) (hk : keyOf hCH rows s.h = some a) :
    viewSlot hCH rows e s = .Live e a s.h := by
  rw [viewSlot, ite_eq_left h, hk]

theorem viewSlot_mk {rows : alloc.vec.Vec (A × D)} {e : Std.U32} {h : I} {a : A}
    (hk : keyOf hCH rows h = some a) :
    viewSlot hCH rows e { g := e, h := h } = .Live e a h :=
  viewSlot_live rfl hk

theorem viewSlot_zero {rows : alloc.vec.Vec (A × D)} {e : Std.U32} {h : I}
    (he : 1 ≤ e.val) : viewSlot hCH rows e { g := 0#u32, h := h } = .Vacant := by
  apply viewSlot_ne
  intro hc
  have := congrArg UScalar.val hc
  simp at this; omega

/-- A slot's view is never live at another epoch than `e`. -/
theorem viewSlot_cases (rows : alloc.vec.Vec (A × D)) (e : Std.U32)
    (s : arena.cons_map.CSlot I) :
    viewSlot hCH rows e s = .Vacant ∨
      ∃ a, s.g = e ∧ keyOf hCH rows s.h = some a ∧ viewSlot hCH rows e s = .Live e a s.h := by
  by_cases hg : s.g = e
  · cases hk : keyOf hCH rows s.h with
    | none => left; rw [viewSlot, ite_eq_left hg, hk]
    | some a => right; exact ⟨a, hg, rfl, viewSlot_live hg hk⟩
  · left; exact viewSlot_ne hg

@[simp] theorem view_slots_val (rows : alloc.vec.Vec (A × D)) (t : arena.cons_map.ConsMap I) :
    (view hCH rows t).slots.val = t.slots.val.map (viewSlot hCH rows t.epoch) := by
  simp [view]

@[simp] theorem view_epoch (rows : alloc.vec.Vec (A × D)) (t : arena.cons_map.ConsMap I) :
    (view hCH rows t).epoch = t.epoch := rfl

@[simp] theorem view_num_entries (rows : alloc.vec.Vec (A × D))
    (t : arena.cons_map.ConsMap I) : (view hCH rows t).num_entries = t.num_entries := rfl

@[simp] theorem view_max_load (rows : alloc.vec.Vec (A × D)) (t : arena.cons_map.ConsMap I) :
    (view hCH rows t).max_load = t.max_load := rfl

theorem view_len (rows : alloc.vec.Vec (A × D)) (t : arena.cons_map.ConsMap I) :
    alloc.vec.Vec.len (view hCH rows t).slots = alloc.vec.Vec.len t.slots :=
  vmap_len _ _

/-! ## The rows grow: the view does not move -/

/-- Appending a row changes the key of no slot that named a row before. -/
theorem keyOf_push {rows rows' : alloc.vec.Vec (A × D)} {x : A × D}
    (hp : rows'.val = rows.val ++ [x]) {h : I} {a : A} (hk : keyOf hCH rows h = some a) :
    keyOf hCH rows' h = some a := by
  have hx : ∃ r, hCH.row h = ok r := by
    by_contra hc; rw [keyOf, dite_eq_right hc] at hk; simp at hk
  obtain ⟨r, hr⟩ := hx
  rw [keyOf_eq hr] at hk ⊢
  rw [hp]
  have hlt : r.val < rows.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hk; simp at hk
  rw [List.getElem?_append_left hlt]; exact hk

theorem viewSlot_push {rows rows' : alloc.vec.Vec (A × D)} {x : A × D}
    (hp : rows'.val = rows.val ++ [x]) {e : Std.U32} {s : arena.cons_map.CSlot I}
    (hn : s.g = e → (keyOf hCH rows s.h).isSome) :
    viewSlot hCH rows' e s = viewSlot hCH rows e s := by
  by_cases hg : s.g = e
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hn hg)
    rw [viewSlot_live hg ha, viewSlot_live hg (keyOf_push hp ha)]
  · rw [viewSlot_ne hg, viewSlot_ne hg]

theorem view_push {rows rows' : alloc.vec.Vec (A × D)} {x : A × D}
    (hp : rows'.val = rows.val ++ [x]) {t : arena.cons_map.ConsMap I}
    (hk : KInv hCH rows t) : view hCH rows' t = view hCH rows t := by
  simp only [view]
  congr 1
  apply alloc.vec.Vec.ext
  simp only [vmap_val]
  apply List.map_congr_left
  intro s hs
  exact viewSlot_push hp (hk.named s hs)

theorem KInv_push {rows rows' : alloc.vec.Vec (A × D)} {x : A × D}
    (hp : rows'.val = rows.val ++ [x]) {t : arena.cons_map.ConsMap I}
    (hk : KInv hCH rows t) : KInv hCH rows' t := by
  refine ⟨hk.stamps, fun s hs hg => ?_⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hk.named s hs hg)
  rw [keyOf_push hp ha]; rfl

/-! ## `KInvS` under the writes the module makes -/

theorem KInvS_set {rows : alloc.vec.Vec (A × D)} {e : Std.U32}
    {l : List (arena.cons_map.CSlot I)} (hk : KInvS hCH rows e l) (j : Nat)
    {x : arena.cons_map.CSlot I} (hx1 : x.g.val ≤ e.val)
    (hx2 : x.g = e → (keyOf hCH rows x.h).isSome) : KInvS hCH rows e (l.set j x) := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rcases List.mem_or_eq_of_mem_set hs with hs | hs
    · exact hk.stamps s hs
    · rw [hs]; exact hx1
  · rcases List.mem_or_eq_of_mem_set hs with hs | hs
    · exact hk.named s hs
    · rw [hs]; exact hx2

theorem KInvS_filler {rows : alloc.vec.Vec (A × D)} {e : Std.U32} (he : 1 ≤ e.val)
    {l : List (arena.cons_map.CSlot I)} (hl : ∀ s ∈ l, s.g = 0#u32) :
    KInvS hCH rows e l := by
  refine ⟨fun s hs => by rw [hl s hs]; simp, fun s hs hg => ?_⟩
  have h0 := hl s hs
  rw [h0] at hg
  have : (0#u32 : Std.U32).val = e.val := by rw [hg]
  simp at this; omega

/-! ## `probe` -/

variable {hA : ron.hashmap.Hashable A} {hE : ron.hashmap.Eq2 A} {hDI : ron.hashmap.Dup I}

theorem next_index_eq {i n : Std.Usize} :
    arena.cons_map.next_index i n = ron.hashmap2.next_index i n := by
  rw [arena.cons_map.next_index, ron.hashmap2.next_index]

theorem home_index_eq {h : Std.U64} {n : Std.Usize} :
    arena.cons_map.home_index h n = ron.hashmap2.home_index h n := by
  rw [arena.cons_map.home_index, ron.hashmap2.home_index]

/-- **`probe` on the view**: the `ConsMap` probe, when it succeeds, answers
what `HashMap2`'s probe answers on the view. -/
theorem probe_sim (rows : alloc.vec.Vec (A × D)) (slots : alloc.vec.Vec (arena.cons_map.CSlot I))
    (e : Std.U32) (key : A) (n : Std.Usize) (F : Nat) :
    ∀ (i fuel : Std.Usize) (r : Std.Usize × Bool), fuel.val = F →
      arena.cons_map.probe hE hCH rows slots e key i n fuel = ok r →
      ron.hashmap2.probe hE (vmap (viewSlot hCH rows e) slots) e key i n fuel = ok r := by
  induction F with
  | zero =>
    intro i fuel r hF h
    have h0 : fuel = 0#usize := by scalar_tac
    rw [arena.cons_map.probe.eq_def, ite_eq_left h0] at h
    rw [ron.hashmap2.probe.eq_def, ite_eq_left h0]
    exact h
  | succ F ih =>
    intro i fuel r hF h
    have h0 : ¬ fuel = 0#usize := by scalar_tac
    rw [arena.cons_map.probe.eq_def, ite_eq_right h0] at h
    rw [ron.hashmap2.probe.eq_def, ite_eq_right h0]
    obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
    refine bind_eq_ok_iff.mpr ⟨_, vmap_index hs, ?_⟩
    by_cases hg : s.g = e
    · have hne : (s.g != e) = false := by simp [hg]
      rw [hne] at h
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨t, d⟩ := p
      have hkey := keyOf_of_index hr1 hp
      rw [viewSlot_live hg hkey]
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      refine bind_eq_ok_iff.mpr ⟨b, hb, ?_⟩
      by_cases hbt : b = true
      · rw [ite_eq_left hbt] at h ⊢; exact h
      · rw [ite_eq_right hbt] at h ⊢
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        rw [next_index_eq] at hi2
        refine bind_eq_ok_iff.mpr ⟨i2, hi2, bind_eq_ok_iff.mpr ⟨i3, hi3, ?_⟩⟩
        exact ih i2 i3 r (by rw [uscalar_sub_eq hi3, hF]; simp) h
    · have hne : (s.g != e) = true := by simp [hg]
      rw [ite_eq_left hne] at h
      rw [viewSlot_ne hg]
      exact h

/-- A probe that answers `found` stopped at a slot of the current epoch that
names a row. -/
theorem probe_true (rows : alloc.vec.Vec (A × D))
    (slots : alloc.vec.Vec (arena.cons_map.CSlot I))
    (e : Std.U32) (key : A) (n : Std.Usize) (F : Nat) :
    ∀ (i fuel at1 : Std.Usize), fuel.val = F →
      arena.cons_map.probe hE hCH rows slots e key i n fuel = ok (at1, true) →
      ∃ s, slots.val[at1.val]? = some s ∧ s.g = e ∧ (keyOf hCH rows s.h).isSome := by
  induction F with
  | zero =>
    intro i fuel at1 hF h
    have h0 : fuel = 0#usize := by scalar_tac
    rw [arena.cons_map.probe.eq_def, ite_eq_left h0] at h
    simp at h
  | succ F ih =>
    intro i fuel at1 hF h
    have h0 : ¬ fuel = 0#usize := by scalar_tac
    rw [arena.cons_map.probe.eq_def, ite_eq_right h0] at h
    obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
    by_cases hg : s.g = e
    · have hne : (s.g != e) = false := by simp [hg]
      rw [hne] at h
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨t, d⟩ := p
      have hkey := keyOf_of_index hr1 hp
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      by_cases hbt : b = true
      · rw [ite_eq_left hbt] at h
        have e1 := Result.ok_injective h
        have ea : at1 = i := (congrArg Prod.fst e1).symm
        subst ea
        exact ⟨s, vec_index_iff.mp hs, hg, by rw [hkey]; rfl⟩
      · rw [ite_eq_right hbt] at h
        obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        exact ih i2 i3 at1 (by rw [uscalar_sub_eq hi3, hF]; simp) h
    · have hne : (s.g != e) = true := by simp [hg]
      rw [ite_eq_left hne] at h
      simp at h

/-! ## Construction -/

theorem pow2_at_least_sim (F : Nat) :
    ∀ (n cap fuel r : Std.Usize), fuel.val = F →
      arena.cons_map.pow2_at_least n cap fuel = ok r →
      ron.hashmap2.pow2_at_least n cap fuel = ok r := by
  induction F with
  | zero =>
    intro n cap fuel r hF h
    have h0 : fuel = 0#usize := by scalar_tac
    rw [arena.cons_map.pow2_at_least.eq_def, ite_eq_left h0] at h
    rw [ron.hashmap2.pow2_at_least.eq_def, ite_eq_left h0]
    exact h
  | succ F ih =>
    intro n cap fuel r hF h
    have h0 : ¬ fuel = 0#usize := by scalar_tac
    rw [arena.cons_map.pow2_at_least.eq_def, ite_eq_right h0] at h
    rw [ron.hashmap2.pow2_at_least.eq_def, ite_eq_right h0]
    by_cases hc : cap ≥ n
    · rw [ite_eq_left hc] at h ⊢; exact h
    · rw [ite_eq_right hc] at h ⊢
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      refine bind_eq_ok_iff.mpr ⟨i, hi, ?_⟩
      by_cases hc2 : cap > i
      · rw [ite_eq_left hc2] at h ⊢; exact h
      · rw [ite_eq_right hc2] at h ⊢
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        refine bind_eq_ok_iff.mpr ⟨i1, hi1, bind_eq_ok_iff.mpr ⟨i2, hi2, ?_⟩⟩
        exact ih n i1 i2 r (by rw [uscalar_sub_eq hi2, hF]; simp) h

/-- `allocate_slots` appends filler slots: stamp `0`. -/
theorem allocate_slots_spec {slots slots' : alloc.vec.Vec (arena.cons_map.CSlot I)}
    {n : Std.Usize}
    (h : arena.cons_map.ConsMap.allocate_slots hDI hCH slots n = ok slots') :
    ∃ len : Std.Usize, alloc.vec.Vec.len slots + n = ok len ∧
      ∃ x : arena.cons_map.CSlot I, x.g = 0#u32 ∧
        slots'.val = slots.val ++ List.replicate n.val x := by
  rw [arena.cons_map.ConsMap.allocate_slots] at h
  obtain ⟨len, hlen, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x, -, h⟩ := bind_eq_ok_iff.mp h
  have hl : len.val = slots.val.length + n.val := by
    rw [uscalar_add_eq hlen]; simp
  refine ⟨len, hlen, ?_⟩
  rw [alloc.vec.Vec.resize] at h
  split at h
  · rename_i hlt
    exfalso; simp at hlt; omega
  · obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
    simp only [arena.cons_map.CSlot.Insts.CoreCloneClone,
      arena.cons_map.CSlot.Insts.CoreCloneClone.clone] at hy
    obtain ⟨hy', -, hy⟩ := bind_eq_ok_iff.mp hy
    refine ⟨y, by rw [← Result.ok_injective hy], ?_⟩
    rw [← Result.ok_injective h]
    simp only [alloc.vec.Vec.from_val, List.resize, hl]
    simp

/-- `HashMap2`'s `new_with_capacity_pow2`, whenever `0 + c` and the load bound
compute. -/
theorem hm2_new_with_capacity_pow2_ok {c len ml : Std.Usize}
    (hlen : alloc.vec.Vec.len (alloc.vec.Vec.with_capacity (ron.hashmap2.Slot A I) c) + c
      = ok len)
    (hml : ron.hashmap2.max_load_for c = ok ml) :
    ∃ sl : alloc.vec.Vec (ron.hashmap2.Slot A I),
      sl.val = List.replicate c.val .Vacant ∧
      ron.hashmap2.HashMap2.new_with_capacity_pow2 A I c
        = ok { num_entries := 0#usize, max_load := ml, epoch := 1#u32, fit_hw := 0#usize,
               slots := sl } := by
  have hl : len.val = c.val := by
    rw [uscalar_add_eq hlen]; simp [alloc.vec.Vec.with_capacity]
  have hres : alloc.vec.Vec.resize (ron.hashmap2.Slot.Insts.CoreCloneClone A I)
      (alloc.vec.Vec.with_capacity (ron.hashmap2.Slot A I) c) len .Vacant
      = ok (alloc.vec.Vec.from (List.replicate c.val .Vacant) (by
          have := len.hBounds; simp; scalar_tac)) := by
    rw [alloc.vec.Vec.resize]
    split
    · rename_i hlt; exfalso; simp [alloc.vec.Vec.with_capacity] at hlt
    · simp only [ron.hashmap2.Slot.Insts.CoreCloneClone.clone, bind_tc_ok]
      congr 1
      apply alloc.vec.Vec.ext
      simp [alloc.vec.Vec.with_capacity, List.resize, hl]
  refine ⟨alloc.vec.Vec.from (List.replicate c.val .Vacant) (by
          have := len.hBounds; simp; scalar_tac), by simp, ?_⟩
  rw [ron.hashmap2.HashMap2.new_with_capacity_pow2]
  refine bind_eq_ok_iff.mpr ⟨_, ?_, bind_eq_ok_iff.mpr ⟨ml, hml, rfl⟩⟩
  rw [ron.hashmap2.HashMap2.allocate_slots]
  exact bind_eq_ok_iff.mpr ⟨len, hlen, hres⟩

theorem max_load_for_eq {c : Std.Usize} :
    arena.cons_map.max_load_for c = ron.hashmap2.max_load_for c := by
  rw [arena.cons_map.max_load_for, ron.hashmap2.max_load_for, arena.cons_map.LOAD_DEN,
    arena.cons_map.LOAD_NUM, ron.hashmap2.LOAD_DEN, ron.hashmap2.LOAD_NUM]

/-- `new_with_capacity_pow2`: the fresh table's view, at any positive epoch,
is `HashMap2`'s fresh table. -/
theorem new_with_capacity_pow2_sim (rows : alloc.vec.Vec (A × D)) {c : Std.Usize}
    {t : arena.cons_map.ConsMap I}
    (h : arena.cons_map.ConsMap.new_with_capacity_pow2 hDI hCH c = ok t) :
    ∃ m, ron.hashmap2.HashMap2.new_with_capacity_pow2 A I c = ok m ∧
      m.num_entries = t.num_entries ∧ m.max_load = t.max_load ∧ m.fit_hw = t.fit_hw ∧
      m.epoch = t.epoch ∧
      (∀ e : Std.U32, 1 ≤ e.val → m.slots = vmap (viewSlot hCH rows e) t.slots) ∧
      (∀ s ∈ t.slots.val, s.g = 0#u32) ∧ t.slots.val.length = c.val := by
  rw [arena.cons_map.ConsMap.new_with_capacity_pow2] at h
  obtain ⟨slots, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ml, hml, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨len, hlen, x, hx0, hx⟩ := allocate_slots_spec hs
  have ht := Result.ok_injective h
  subst ht
  have hsv : slots.val = List.replicate c.val x := by
    simpa [alloc.vec.Vec.with_capacity] using hx
  rw [max_load_for_eq] at hml
  obtain ⟨sl, hsl, hm⟩ := hm2_new_with_capacity_pow2_ok (A := A) (I := I) (len := len)
    (by simpa [alloc.vec.Vec.with_capacity] using hlen) hml
  refine ⟨_, hm, rfl, rfl, rfl, rfl, fun e he => ?_, fun s hs' => ?_, by simp [hsv]⟩
  · apply alloc.vec.Vec.ext
    simp only [vmap_val, hsl, hsv, List.map_replicate]
    have : x = { g := 0#u32, h := x.h } := by cases x; simp_all
    rw [this, viewSlot_zero he]
  · rw [hsv] at hs'
    rw [List.eq_of_mem_replicate hs', hx0]

theorem hm2_eq {m m' : ron.hashmap2.HashMap2 A I} (h1 : m.num_entries = m'.num_entries)
    (h2 : m.max_load = m'.max_load) (h3 : m.epoch = m'.epoch) (h4 : m.fit_hw = m'.fit_hw)
    (h5 : m.slots = m'.slots) : m = m' := by
  cases m; cases m'; simp_all

theorem ensure_slots_sim (rows : alloc.vec.Vec (A × D)) {t t' : arena.cons_map.ConsMap I}
    (hep : 1 ≤ t.epoch.val) (hk : KInv hCH rows t)
    (h : arena.cons_map.ConsMap.ensure_slots hDI hCH t = ok t') :
    ron.hashmap2.HashMap2.ensure_slots (view hCH rows t) = ok (view hCH rows t') ∧
      KInv hCH rows t' ∧ t'.epoch = t.epoch ∧ t'.num_entries = t.num_entries := by
  rw [arena.cons_map.ConsMap.ensure_slots] at h
  rw [ron.hashmap2.HashMap2.ensure_slots, view_len]
  split at h
  · rename_i h0
    rw [ite_eq_left h0]
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨want, hwant, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨tb, htb, h⟩ := bind_eq_ok_iff.mp h
    have ht := Result.ok_injective h
    subst ht
    obtain ⟨m, hm, -, hml, -, -, hsl, hg0, -⟩ := new_with_capacity_pow2_sim rows htb
    rw [arena.cons_map.MIN_CAPACITY, arena.cons_map.POW2_FUEL] at hwant
    have hwant' := pow2_at_least_sim _ i2 _ _ want rfl hwant
    refine ⟨bind_eq_ok_iff.mpr ⟨i1, hi1, bind_eq_ok_iff.mpr ⟨i2, hi2,
      bind_eq_ok_iff.mpr ⟨want, ?_, bind_eq_ok_iff.mpr ⟨m, hm, ?_⟩⟩⟩⟩,
      KInvS_filler hep hg0, rfl, rfl⟩
    · rw [ron.hashmap2.MIN_CAPACITY, ron.hashmap2.POW2_FUEL]; exact hwant'
    · exact congrArg ok (hm2_eq rfl hml rfl rfl (hsl t.epoch hep))
  · rename_i h0
    rw [ite_eq_right h0]
    rw [← Result.ok_injective h]
    exact ⟨rfl, hk, rfl, rfl⟩

/-! ## Writing a slot -/

theorem KInv_set {rows : alloc.vec.Vec (A × D)} {t : arena.cons_map.ConsMap I}
    (hk : KInv hCH rows t) (i : Std.Usize) {value : I} {key : A}
    (hkey : keyOf hCH rows value = some key) (n : Std.Usize) :
    KInv hCH rows
      { t with num_entries := n,
               slots := alloc.vec.Vec.set t.slots i { g := t.epoch, h := value } } := by
  show KInvS hCH rows t.epoch (alloc.vec.Vec.set t.slots i _).val
  rw [alloc.vec.Vec.set_val_eq]
  exact KInvS_set hk i.val (le_refl _) (fun _ => by rw [hkey]; rfl)

theorem view_set {rows : alloc.vec.Vec (A × D)} {t : arena.cons_map.ConsMap I}
    (i : Std.Usize) {value : I} {key : A} (hkey : keyOf hCH rows value = some key)
    (n : Std.Usize) :
    view hCH rows
        { t with num_entries := n,
                 slots := alloc.vec.Vec.set t.slots i { g := t.epoch, h := value } } =
      { view hCH rows t with
          num_entries := n,
          slots := alloc.vec.Vec.set (view hCH rows t).slots i (.Live t.epoch key value) } := by
  simp only [view]
  rw [vmap_set, viewSlot_mk hkey]

theorem insert_no_resize_sim (rows : alloc.vec.Vec (A × D)) {t t' : arena.cons_map.ConsMap I}
    {key : A} {value : I} {o : Option I}
    (hkey : keyOf hCH rows value = some key) (hk : KInv hCH rows t)
    (h : arena.cons_map.ConsMap.insert_no_resize hDI hCH hA hE t rows key value = ok (o, t')) :
    ron.hashmap2.HashMap2.insert_no_resize hA hE (view hCH rows t) key value
        = ok (o, view hCH rows t') ∧
      KInv hCH rows t' ∧ t'.epoch = t.epoch := by
  rw [arena.cons_map.ConsMap.insert_no_resize] at h
  obtain ⟨hv, hhash, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q, hpr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i2, b⟩ := q
  obtain ⟨p, hmut, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c, back⟩ := p
  obtain ⟨hmut', rfl⟩ := vmap_index_mut (f := viewSlot hCH rows t.epoch) hmut
  have hpr' := probe_sim rows t.slots t.epoch key _ _ i1 _ _ rfl hpr
  have hc : t.slots.val[i2.val]? = some c := (vec_index_mut_iff.mp hmut).1
  rw [home_index_eq] at hi1
  simp only [core.mem.replace] at h
  cases b with
  | true =>
    obtain ⟨s, hs, hsg, hsk⟩ := probe_true rows t.slots t.epoch key _ _ i1 _ _ rfl hpr
    rw [hc] at hs
    cases hs
    obtain ⟨k, hk'⟩ := Option.isSome_iff_exists.mp hsk
    simp only [ite_true] at h
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨?_, KInv_set hk i2 hkey t.num_entries, rfl⟩
    rw [ron.hashmap2.HashMap2.insert_no_resize, view_len]
    refine bind_eq_ok_iff.mpr ⟨hv, hhash, bind_eq_ok_iff.mpr ⟨i1, hi1,
      bind_eq_ok_iff.mpr ⟨(i2, true), hpr', bind_eq_ok_iff.mpr ⟨_, hmut', ?_⟩⟩⟩⟩
    simp only [core.mem.replace, ite_true]
    rw [viewSlot_live hsg hk']
    exact congrArg ok (Prod.ext rfl (view_set i2 hkey t.num_entries).symm)
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨?_, KInv_set hk i2 hkey i3, rfl⟩
    rw [ron.hashmap2.HashMap2.insert_no_resize, view_len]
    refine bind_eq_ok_iff.mpr ⟨hv, hhash, bind_eq_ok_iff.mpr ⟨i1, hi1,
      bind_eq_ok_iff.mpr ⟨(i2, false), hpr', bind_eq_ok_iff.mpr ⟨_, hmut', ?_⟩⟩⟩⟩
    simp only [core.mem.replace, Bool.false_eq_true, ite_false]
    exact bind_eq_ok_iff.mpr ⟨i3, hi3, congrArg ok (Prod.ext rfl (view_set i2 hkey i3).symm)⟩

/-! ## Resizing -/

/-- `move_slots` on the view.  The rows are fixed for the whole walk; each
entry of the current epoch is re-inserted under its row's key. -/
theorem move_slots_sim (rows : alloc.vec.Vec (A × D)) (epoch : Std.U32) (hep : 1 ≤ epoch.val)
    (N : Nat) :
    ∀ (nt nt' : arena.cons_map.ConsMap I) (slots slots' : alloc.vec.Vec (arena.cons_map.CSlot I))
      (lo hi : Std.Usize),
      hi.val - lo.val = N → nt.epoch = epoch → KInv hCH rows nt →
      arena.cons_map.ConsMap.move_slots hDI hCH hA hE rows nt slots lo hi epoch
        = ok (nt', slots') →
      ron.hashmap2.HashMap2.move_slots hA hE (view hCH rows nt)
          (vmap (viewSlot hCH rows epoch) slots) lo hi epoch
        = ok (view hCH rows nt', vmap (viewSlot hCH rows epoch) slots') ∧
      KInv hCH rows nt' ∧ nt'.epoch = epoch := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro nt nt' slots slots' lo hi hN hnt hk h
    rw [arena.cons_map.ConsMap.move_slots.eq_def] at h
    rw [ron.hashmap2.HashMap2.move_slots.eq_def]
    split at h
    · rename_i hgt
      rw [ite_eq_left hgt]
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      have hnv : n.val = hi.val - lo.val := uscalar_sub_eq hn
      split at h
      · rename_i h1
        obtain ⟨p, hmut, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨c, back⟩ := p
        obtain ⟨hmut', rfl⟩ := vmap_index_mut (f := viewSlot hCH rows epoch) hmut
        obtain ⟨x, -, h⟩ := bind_eq_ok_iff.mp h
        rw [core.mem.replace] at h
        change (if c.g = epoch then _ else _) = _ at h
        have hvac : vmap (viewSlot hCH rows epoch)
            (alloc.vec.Vec.set slots lo { g := 0#u32, h := x })
            = alloc.vec.Vec.set (vmap (viewSlot hCH rows epoch) slots) lo .Vacant := by
          rw [vmap_set, viewSlot_zero hep]
        by_cases hg : c.g = epoch
        · simp only [hg, ite_true] at h
          obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨pp, hpp, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨k, d⟩ := pp
          obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, nt1⟩ := q
          have e := Result.ok_injective h
          simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          have hkey := keyOf_of_index hr hpp
          obtain ⟨hins', hk1, hep1⟩ := insert_no_resize_sim rows hkey hk hins
          refine ⟨bind_eq_ok_iff.mpr ⟨n, hn, ?_⟩, hk1, hep1.trans hnt⟩
          rw [ite_eq_left h1]
          refine bind_eq_ok_iff.mpr ⟨_, hmut', ?_⟩
          rw [viewSlot_live hg hkey]
          change (if epoch = epoch then (do
              let (_, ntable1) ← ron.hashmap2.HashMap2.insert_no_resize hA hE (view hCH rows nt) k c.h
              ok (ntable1, alloc.vec.Vec.set (vmap (viewSlot hCH rows epoch) slots) lo .Vacant))
            else ok (view hCH rows nt,
              alloc.vec.Vec.set (vmap (viewSlot hCH rows epoch) slots) lo .Vacant)) = _
          rw [ite_eq_left rfl]
          exact bind_eq_ok_iff.mpr ⟨(o, _), hins',
            by rw [hvac]; rfl⟩
        · rw [ite_eq_right hg] at h
          have e := Result.ok_injective h
          simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          refine ⟨bind_eq_ok_iff.mpr ⟨n, hn, ?_⟩, hk, hnt⟩
          rw [ite_eq_left h1]
          refine bind_eq_ok_iff.mpr ⟨_, hmut', ?_⟩
          simp only [core.mem.replace]
          rw [viewSlot_ne hg]
          rw [hvac]
          rfl
      · rename_i h1
        have hn2 : 2 ≤ n.val := by
          have : n.val ≠ 1 := by scalar_tac
          have : n.val ≠ 0 := by scalar_tac
          omega
        obtain ⟨i, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨mid, hmid, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨q, h1s, h2s⟩ := bind_eq_ok_iff.mp h
        obtain ⟨nt1, slots1⟩ := q
        have hiv : i.val = n.val / 2 := by
          rw [uscalar_div_eq hi2, show (2#usize : Std.Usize).val = 2 by scalar_tac]
        have hmv : mid.val = lo.val + i.val := uscalar_add_eq hmid
        obtain ⟨r1, hk1, he1⟩ := ih (mid.val - lo.val) (by omega) nt nt1 slots slots1 lo mid rfl
          hnt hk h1s
        obtain ⟨r2, hk2, he2⟩ := ih (hi.val - mid.val) (by omega) nt1 nt' slots1 slots' mid hi
          rfl he1 hk1 h2s
        refine ⟨bind_eq_ok_iff.mpr ⟨n, hn, ?_⟩, hk2, he2⟩
        rw [ite_eq_right h1]
        exact bind_eq_ok_iff.mpr ⟨i, hi2, bind_eq_ok_iff.mpr ⟨mid, hmid,
          bind_eq_ok_iff.mpr ⟨_, r1, r2⟩⟩⟩
    · rename_i hgt
      rw [ite_eq_right hgt]
      have e := Result.ok_injective h
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨rfl, hk, hnt⟩

/-- `try_resize` on the view. -/
theorem try_resize_sim (rows : alloc.vec.Vec (A × D)) {t t' : arena.cons_map.ConsMap I}
    (hep : 1 ≤ t.epoch.val)
    (h : arena.cons_map.ConsMap.try_resize hDI hCH hA hE t rows = ok t') :
    ron.hashmap2.HashMap2.try_resize hA hE (view hCH rows t) = ok (view hCH rows t') ∧
      KInv hCH rows t' ∧ t'.epoch = t.epoch ∧ t'.num_entries = t.num_entries := by
  rw [arena.cons_map.ConsMap.try_resize] at h
  obtain ⟨c2, hc2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨nt, hnt, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q, hmv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨nt1, sl1⟩ := q
  have ht := Result.ok_injective h
  subst ht
  obtain ⟨m, hm, hne, hml, hfw, -, hsl, hg0, -⟩ := new_with_capacity_pow2_sim rows hnt
  have hk0 : KInv hCH rows { nt with epoch := t.epoch } := KInvS_filler hep hg0
  obtain ⟨hmv', hk1, hep1⟩ :=
    move_slots_sim rows t.epoch hep _ { nt with epoch := t.epoch } _ _ _ _ _ rfl rfl hk0 hmv
  have hv0 : { m with epoch := t.epoch } = view hCH rows { nt with epoch := t.epoch } :=
    hm2_eq hne hml rfl hfw (hsl t.epoch hep)
  refine ⟨?_, ?_, rfl, rfl⟩
  · rw [ron.hashmap2.HashMap2.try_resize, view_len]
    refine bind_eq_ok_iff.mpr ⟨c2, hc2, bind_eq_ok_iff.mpr ⟨m, hm,
      bind_eq_ok_iff.mpr ⟨(view hCH rows nt1, _), by rw [← hv0] at hmv'; exact hmv', ?_⟩⟩⟩
    simp only [view, hep1]
    rfl
  · show KInvS hCH rows t.epoch nt1.slots.val
    have := hk1
    unfold KInv at this
    rw [hep1] at this
    exact this

/-! ## The public operations -/

theorem insert_sim (rows : alloc.vec.Vec (A × D)) {t t' : arena.cons_map.ConsMap I}
    {key : A} {value : I} {o : Option I}
    (hkey : keyOf hCH rows value = some key) (hep : 1 ≤ t.epoch.val) (hk : KInv hCH rows t)
    (h : arena.cons_map.ConsMap.insert hDI hCH hA hE t rows key value = ok (o, t')) :
    ron.hashmap2.HashMap2.insert hA hE (view hCH rows t) key value = ok (o, view hCH rows t') ∧
      KInv hCH rows t' := by
  rw [arena.cons_map.ConsMap.insert] at h
  obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨old, t2⟩ := q
  obtain ⟨he1, hk1, hep1, -⟩ := ensure_slots_sim rows hep hk ht1
  obtain ⟨hi1, hk2, hep2⟩ := insert_no_resize_sim rows hkey hk1 hins
  rw [ron.hashmap2.HashMap2.insert]
  change (if t2.num_entries > t2.max_load then _ else _) = _ at h
  by_cases hgt : t2.num_entries > t2.max_load
  · rw [ite_eq_left hgt] at h
    obtain ⟨t3, ht3, h⟩ := bind_eq_ok_iff.mp h
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨hr, hk3, -, -⟩ := try_resize_sim rows (by rw [hep2, hep1]; exact hep) ht3
    refine ⟨bind_eq_ok_iff.mpr ⟨_, he1, bind_eq_ok_iff.mpr ⟨(_, view hCH rows t2), hi1, ?_⟩⟩, hk3⟩
    change (if (view hCH rows t2).num_entries > (view hCH rows t2).max_load then _ else _) = _
    rw [ite_eq_left (show (view hCH rows t2).num_entries > (view hCH rows t2).max_load from hgt)]
    exact bind_eq_ok_iff.mpr ⟨_, hr, rfl⟩
  · rw [ite_eq_right hgt] at h
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨bind_eq_ok_iff.mpr ⟨_, he1, bind_eq_ok_iff.mpr ⟨(_, view hCH rows t2), hi1, ?_⟩⟩, hk2⟩
    change (if (view hCH rows t2).num_entries > (view hCH rows t2).max_load then _ else _) = _
    rw [ite_eq_right (show ¬ (view hCH rows t2).num_entries > (view hCH rows t2).max_load from hgt)]

theorem insert_at_sim (rows : alloc.vec.Vec (A × D)) {t t' : arena.cons_map.ConsMap I}
    {at1 : Std.Usize} {key : A} {value : I}
    (hkey : keyOf hCH rows value = some key) (hep : 1 ≤ t.epoch.val) (hk : KInv hCH rows t)
    (h : arena.cons_map.ConsMap.insert_at hDI hCH hA hE t rows at1 value = ok t') :
    ron.hashmap2.HashMap2.insert_at hA hE (view hCH rows t) at1 key value = ok (view hCH rows t') ∧
      KInv hCH rows t' := by
  rw [arena.cons_map.ConsMap.insert_at] at h
  obtain ⟨p, hmut, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c, back⟩ := p
  obtain ⟨hmut', rfl⟩ := vmap_index_mut (f := viewSlot hCH rows t.epoch) hmut
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  have hk1 := KInv_set hk at1 hkey i
  have hv1 := view_set (t := t) at1 hkey i
  rw [ron.hashmap2.HashMap2.insert_at]
  by_cases hgt : i > t.max_load
  · rw [ite_eq_left hgt] at h
    obtain ⟨hr, hk2, -, -⟩ := try_resize_sim
      (t := { t with
        num_entries := i, slots := alloc.vec.Vec.set t.slots at1 { g := t.epoch, h := value } })
      rows hep h
    refine ⟨bind_eq_ok_iff.mpr ⟨_, hmut', bind_eq_ok_iff.mpr ⟨i, hi, ?_⟩⟩, hk2⟩
    rw [ite_eq_left (show i > (view hCH rows t).max_load from hgt)]
    rw [hv1] at hr
    exact hr
  · rw [ite_eq_right hgt] at h
    rw [← Result.ok_injective h]
    refine ⟨bind_eq_ok_iff.mpr ⟨_, hmut', bind_eq_ok_iff.mpr ⟨i, hi, ?_⟩⟩, hk1⟩
    rw [ite_eq_right (show ¬ i > (view hCH rows t).max_load from hgt)]
    exact congrArg ok hv1.symm

theorem find_slot_sim (rows : alloc.vec.Vec (A × D)) {t t' : arena.cons_map.ConsMap I}
    {key : A} {at1 : Std.Usize} {o : Option I} (hep : 1 ≤ t.epoch.val) (hk : KInv hCH rows t)
    (h : arena.cons_map.ConsMap.find_slot hDI hCH hA hE t rows key = ok ((at1, o), t')) :
    ron.hashmap2.HashMap2.find_slot hA hE hDI (view hCH rows t) key
        = ok ((at1, o), view hCH rows t') ∧
      KInv hCH rows t' ∧ t'.epoch = t.epoch := by
  rw [arena.cons_map.ConsMap.find_slot] at h
  obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨he1, hk1, hep1, -⟩ := ensure_slots_sim rows hep hk ht1
  obtain ⟨hv, hhash, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q, hpr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i2, b⟩ := q
  have hpr' := probe_sim rows t1.slots t1.epoch key _ _ i1 _ _ rfl hpr
  rw [home_index_eq] at hi1
  rw [ron.hashmap2.HashMap2.find_slot]
  cases b with
  | true =>
    change (if true = true then _ else _) = _ at h
    rw [ite_eq_left rfl] at h
    obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv2, h⟩ := bind_eq_ok_iff.mp h
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    obtain ⟨s, hs, hsg, hsk⟩ := probe_true rows t1.slots t1.epoch key _ _ i1 _ _ rfl hpr
    rw [vec_index_iff.mp hc] at hs
    cases hs
    obtain ⟨k, hk'⟩ := Option.isSome_iff_exists.mp hsk
    refine ⟨bind_eq_ok_iff.mpr ⟨_, he1, ?_⟩, hk1, hep1⟩
    rw [view_len]
    refine bind_eq_ok_iff.mpr ⟨hv, hhash, bind_eq_ok_iff.mpr ⟨i1, hi1,
      bind_eq_ok_iff.mpr ⟨(i2, true), hpr', ?_⟩⟩⟩
    change (if true = true then _ else _) = _
    rw [ite_eq_left rfl]
    refine bind_eq_ok_iff.mpr ⟨_, vmap_index hc, ?_⟩
    rw [viewSlot_live hsg hk']
    exact bind_eq_ok_iff.mpr ⟨v, hv2, rfl⟩
  | false =>
    change (if false = true then _ else _) = _ at h
    rw [ite_eq_right (by simp)] at h
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    refine ⟨bind_eq_ok_iff.mpr ⟨_, he1, ?_⟩, hk1, hep1⟩
    rw [view_len]
    refine bind_eq_ok_iff.mpr ⟨hv, hhash, bind_eq_ok_iff.mpr ⟨i1, hi1,
      bind_eq_ok_iff.mpr ⟨(i2, false), hpr', ?_⟩⟩⟩
    change (if false = true then _ else _) = _
    rw [ite_eq_right (by simp)]

theorem get_sim (rows : alloc.vec.Vec (A × D)) {t : arena.cons_map.ConsMap I} (hdup : DupId hDI)
    {key : A} {o : Option I}
    (h : arena.cons_map.ConsMap.get hDI hCH hA hE t rows key = ok o) :
    ron.hashmap2.HashMap2.get hA hE (view hCH rows t) key = ok o := by
  rw [arena.cons_map.ConsMap.get] at h
  rw [ron.hashmap2.HashMap2.get, view_len]
  split at h
  · rename_i h0
    rw [ite_eq_left h0]; exact h
  · rename_i h0
    rw [ite_eq_right h0]
    obtain ⟨hv, hhash, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨q, hpr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i2, b⟩ := q
    have hpr' := probe_sim rows t.slots t.epoch key _ _ i1 _ _ rfl hpr
    rw [home_index_eq] at hi1
    refine bind_eq_ok_iff.mpr ⟨hv, hhash, bind_eq_ok_iff.mpr ⟨i1, hi1,
      bind_eq_ok_iff.mpr ⟨(i2, b), hpr', ?_⟩⟩⟩
    change (if b = true then _ else _) = _ at h
    change (if b = true then _ else _) = _
    cases b with
    | true =>
      rw [ite_eq_left rfl] at h ⊢
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨s, hs, hsg, hsk⟩ := probe_true rows t.slots t.epoch key _ _ i1 _ _ rfl hpr
      rw [vec_index_iff.mp hc] at hs
      cases hs
      obtain ⟨k, hk'⟩ := Option.isSome_iff_exists.mp hsk
      refine bind_eq_ok_iff.mpr ⟨_, vmap_index hc, ?_⟩
      rw [viewSlot_live hsg hk', ← Result.ok_injective h, hdup _ _ hv2]
    | false =>
      rw [ite_eq_right (by simp)] at h ⊢
      exact h

theorem new_sim (rows : alloc.vec.Vec (A × D)) {t : arena.cons_map.ConsMap I}
    (h : arena.cons_map.ConsMap.new hDI hCH = ok t) :
    ron.hashmap2.HashMap2.new A I = ok (view hCH rows t) ∧ KInv hCH rows t := by
  rw [arena.cons_map.ConsMap.new] at h
  have ht := Result.ok_injective h
  subst ht
  refine ⟨?_, ⟨by simp, by simp⟩⟩
  rw [ron.hashmap2.HashMap2.new]
  congr 1

/-! ## `clear` and `clear_fit`, directly

Not a simulation: `HashMap2::clear` leaves stale `Live` slots, which the view
of the cleared `ConsMap` reads as `Vacant`.  Both are the empty map, and the
view of the cleared table satisfies `Inv` by `HashMap2`'s own
`vacant_table_inv`.  The conclusions hold over ANY row vector, because a
table with no slot of its epoch names no row — which is what lets `Tbl::reset`
replace the rows. -/

theorem view_all_vacant {rows : alloc.vec.Vec (A × D)} {t : arena.cons_map.ConsMap I}
    (h : ∀ s ∈ t.slots.val, ¬ s.g = t.epoch) :
    ∀ j : Nat, (view hCH rows t).slots.val[j]! = ron.hashmap2.Slot.Vacant := by
  intro j
  rw [view_slots_val]
  by_cases hj : j < t.slots.val.length
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
    simp only [Option.map_some, Option.getD_some]
    exact viewSlot_ne (h _ (List.getElem_mem hj))
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl

theorem dead_view_inv [DecidableEq A] (rows : alloc.vec.Vec (A × D)) {t : arena.cons_map.ConsMap I}
    (hdead : ∀ s ∈ t.slots.val, ¬ s.g = t.epoch) (hn : t.num_entries.val = 0)
    (hpow : 0 < t.slots.val.length → ∃ e, t.slots.val.length = 2 ^ e)
    (hmin : 0 < t.slots.val.length → 32 ≤ t.slots.val.length)
    (hml : 0 < t.slots.val.length → t.max_load.val = 3 * (t.slots.val.length / 4))
    (hep : 1 ≤ t.epoch.val) :
    Inv hA (view hCH rows t) ∧ sl_v (view hCH rows t) = [] ∧
      ∀ k, toFun (view hCH rows t) k = none := by
  have hv := view_all_vacant (hCH := hCH) (rows := rows) hdead
  have hlen : (view hCH rows t).slots.val.length = t.slots.val.length := by simp
  have hsl : sl_v (view hCH rows t) = [] :=
    ConRon.Refine.HashMap2.sl_v_eq_nil_of_no_live (fun j => by rw [slotKV, hv j]; rfl)
  exact vacant_table_inv hv hsl hn (Nat.zero_le _) (by rw [hlen]; exact hpow)
    (by rw [hlen]; exact hmin) (by rw [hlen]; exact hml) hep

theorem vacate_slots_spec (N : Nat) :
    ∀ (slots slots' : alloc.vec.Vec (arena.cons_map.CSlot I)) (lo hi : Std.Usize),
      hi.val - lo.val = N →
      arena.cons_map.ConsMap.vacate_slots hDI hCH slots lo hi = ok slots' →
      slots'.val.length = slots.val.length ∧
      (∀ j, lo.val ≤ j → j < hi.val → ∀ s, slots'.val[j]? = some s → s.g = 0#u32) ∧
      (∀ j, (j < lo.val ∨ hi.val ≤ j) → slots'.val[j]? = slots.val[j]?) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro slots slots' lo hi hN h
    rw [arena.cons_map.ConsMap.vacate_slots.eq_def] at h
    split at h
    · rename_i hgt
      have hlt : lo.val < hi.val := by scalar_tac
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      have hnv : n.val = hi.val - lo.val := uscalar_sub_eq hn
      split at h
      · rename_i h1
        have hn1 : hi.val = lo.val + 1 := by
          have : n.val = 1 := by scalar_tac
          omega
        obtain ⟨x, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hp, hb⟩ := bind_eq_ok_iff.mp h
        obtain ⟨y, f⟩ := p
        obtain ⟨hy, rfl⟩ := vec_index_mut_iff.mp hp
        have hlo : lo.val < slots.val.length := by
          by_contra hc; rw [List.getElem?_eq_none (by omega)] at hy; simp at hy
        rw [← Result.ok_injective hb, alloc.vec.Vec.set_val_eq]
        refine ⟨by simp, ?_, ?_⟩
        · intro j hj1 hj2 s hs
          have : j = lo.val := by omega
          subst this
          rw [List.getElem?_set_self hlo] at hs
          cases hs; rfl
        · intro j hj
          exact List.getElem?_set_ne (by omega)
      · rename_i h1
        have hn2 : 2 ≤ n.val := by
          have : n.val ≠ 1 := by scalar_tac
          omega
        obtain ⟨i, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨mid, hmid, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨slots1, hs1, h2⟩ := bind_eq_ok_iff.mp h
        have hiv : i.val = n.val / 2 := by
          rw [uscalar_div_eq hi2, show (2#usize : Std.Usize).val = 2 by scalar_tac]
        have hmv : mid.val = lo.val + i.val := uscalar_add_eq hmid
        obtain ⟨l1, c1, f1⟩ := ih (mid.val - lo.val) (by omega) slots slots1 lo mid rfl hs1
        obtain ⟨l2, c2, f2⟩ := ih (hi.val - mid.val) (by omega) slots1 slots' mid hi rfl h2
        refine ⟨by omega, ?_, ?_⟩
        · intro j hj1 hj2 s hs
          by_cases hjm : j < mid.val
          · rw [f2 j (Or.inl hjm)] at hs; exact c1 j hj1 hjm s hs
          · exact c2 j (by omega) hj2 s hs
        · intro j hj
          rw [f2 j (by omega), f1 j (by omega)]
    · rename_i hgt
      have : hi.val ≤ lo.val := by scalar_tac
      rw [← Result.ok_injective h]
      exact ⟨rfl, fun j hj1 hj2 => by omega, fun _ _ => rfl⟩

theorem clear_spec [DecidableEq A] (rows : alloc.vec.Vec (A × D)) {t t' : arena.cons_map.ConsMap I}
    (hinv : Inv hA (view hCH rows t)) (hk : KInv hCH rows t)
    (h : arena.cons_map.ConsMap.clear hDI hCH t = ok t') (rows' : alloc.vec.Vec (A × D)) :
    Inv hA (view hCH rows' t') ∧ sl_v (view hCH rows' t') = [] ∧
      (∀ k, toFun (view hCH rows' t') k = none) ∧ KInv hCH rows' t' := by
  have hlen0 : (view hCH rows t).slots.val.length = t.slots.val.length := by simp
  rw [arena.cons_map.ConsMap.clear] at h
  split at h
  · -- the `EPOCH_MAX` wrap: every slot becomes a filler, the epoch restarts
    obtain ⟨v, hv, hm⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hlen, hnil, -⟩ := vacate_slots_spec ((alloc.vec.Vec.len t.slots).val - 0)
      t.slots v 0#usize (alloc.vec.Vec.len t.slots) rfl hv
    have ht := Result.ok_injective hm
    subst ht
    have hz : ∀ s ∈ v.val, s.g = 0#u32 := by
      intro s hs
      obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hs
      exact hnil j (by simp) (by rw [alloc.vec.Vec.len_val]; rw [hlen] at hj; exact hj) s
        (by rw [List.getElem?_eq_getElem hj, hjs])
    have hdead : ∀ s ∈ v.val, ¬ s.g = 1#u32 := by
      intro s hs hc; rw [hz s hs] at hc; simp at hc
    obtain ⟨h1, h2, h3⟩ := dead_view_inv (hA := hA)
      (t := { t with num_entries := 0#usize, epoch := 1#u32, slots := v }) rows' hdead rfl
      (by intro hp; rw [hlen] at hp ⊢; rw [← hlen0] at hp ⊢; exact hinv.pow2 hp)
      (by intro hp; rw [hlen] at hp ⊢; rw [← hlen0] at hp ⊢; exact hinv.min_cap hp)
      (by intro hp; rw [hlen] at hp ⊢; rw [← hlen0] at hp ⊢; exact hinv.max_load_eq hp)
      (by simp)
    exact ⟨h1, h2, h3, KInvS_filler (by simp) hz⟩
  · -- the common path: `epoch += 1`, and no slot carries the new stamp
    obtain ⟨i, hi, hm⟩ := bind_eq_ok_iff.mp h
    have hiv : i.val = t.epoch.val + 1 := by rw [uscalar_add_eq hi]; simp
    have ht := Result.ok_injective hm
    subst ht
    have hdead : ∀ s ∈ t.slots.val, ¬ s.g = i := by
      intro s hs hc
      have := hk.stamps s hs
      rw [hc] at this; omega
    obtain ⟨h1, h2, h3⟩ := dead_view_inv (hA := hA)
      (t := { t with num_entries := 0#usize, epoch := i }) rows' hdead rfl
      (by rw [← hlen0]; exact hinv.pow2) (by rw [← hlen0]; exact hinv.min_cap)
      (by rw [← hlen0]; exact hinv.max_load_eq) (by show 1 ≤ i.val; omega)
    refine ⟨h1, h2, h3, fun s hs => ?_, fun s hs hc => absurd hc (hdead s hs)⟩
    have := hk.stamps s hs
    show s.g.val ≤ i.val
    omega

theorem clear_fit_spec [DecidableEq A] (rows : alloc.vec.Vec (A × D)) {t t' : arena.cons_map.ConsMap I}
    (hinv : Inv hA (view hCH rows t)) (hk : KInv hCH rows t)
    (h : arena.cons_map.ConsMap.clear_fit hDI hCH t = ok t') (rows' : alloc.vec.Vec (A × D)) :
    Inv hA (view hCH rows' t') ∧ sl_v (view hCH rows' t') = [] ∧
      (∀ k, toFun (view hCH rows' t') k = none) ∧ KInv hCH rows' t' := by
  rw [arena.cons_map.ConsMap.clear_fit] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨decayed, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hw, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i2, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨want, -, h⟩ := bind_eq_ok_iff.mp h
  have hinv' : Inv hA (view hCH rows { t with fit_hw := hw }) :=
    ConRon.Refine.HashMap2.Inv_fit_hw hinv hw
  have hk' : KInv hCH rows { t with fit_hw := hw } := hk
  have hlazy : ok (α := arena.cons_map.ConsMap I)
        { num_entries := 0#usize, max_load := 0#usize, epoch := 1#u32, fit_hw := hw,
          slots := alloc.vec.Vec.new (arena.cons_map.CSlot I) } = ok t' →
      Inv hA (view hCH rows' t') ∧ sl_v (view hCH rows' t') = [] ∧
        (∀ k, toFun (view hCH rows' t') k = none) ∧ KInv hCH rows' t' := by
    intro hok
    have ht := Result.ok_injective hok
    subst ht
    obtain ⟨h1, h2, h3⟩ := dead_view_inv (hA := hA)
      (t := { num_entries := 0#usize, max_load := 0#usize, epoch := 1#u32, fit_hw := hw,
              slots := alloc.vec.Vec.new (arena.cons_map.CSlot I) })
      rows' (by simp) rfl (by simp) (by simp) (by simp) (by simp)
    exact ⟨h1, h2, h3, by simp, by simp⟩
  split at h
  · exact clear_spec rows hinv' hk' h rows'
  · split at h
    · obtain ⟨i3, -, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · exact clear_spec rows hinv' hk' h rows'
      · exact hlazy h
    · exact hlazy h

