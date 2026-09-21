/-
The abstract-map specification of `ron::HashMap2` (DESIGN.md §3.3, task
#97-P6-4b §4 "The owed proof", task #97-HM2), proved on the generated model
`ConRon.Generated.ron.hashmap2.*`.

`ron::HashMap2` is the *same abstract object* as `ron::hashmap`'s `HashMap` —
a partial map from `K` to `V` over the same `Hashable`/`Eq2`/`Dup`
dictionaries — over an **open-addressed, epoch-stamped, flat slot vector**
instead of chained buckets.  Task #97-P6-4b's ledger says the mathematical
specification survives the change unaltered, and that is what this file
realizes: `lookupK`, `eraseK` and their eleven list lemmas are *imported* from
`Refine/HashMap.lean` rather than restated, and `toFun m k = lookupK ⟦table⟧ k`
is the same equation over a different `⟦·⟧`.

What moves, and only what moves:

* **`alv`/`alvO`/`al_v`/`AList.recTail` → `sl_v`** — the live slots, in index
  order, a `List.filterMap` over `slots`.  The nested inductive that forced
  `AList.recTail` is gone, and with it the induction principle.
* **the three `list_*` specs → one `probe_spec`** — "`probe` returns the key's
  slot if it is live in its run, and otherwise the first free slot of the
  run".  This is the one new lemma with content, and it carries the walk
  (`probe_walk`) that every other operation reads its run facts from.
* **`Inv` gains a run clause** (`run`: every live key is reachable from its
  home slot by a run of live slots), **an epoch clause** (`epoch_pos`,
  `stamps`: no slot carries a stamp above the table's epoch, which is what
  makes the O(1) `clear` correct) and **a load clause** (`fit` +
  `max_load_eq`: `num_entries ≤ max_load = 3·⌊n/4⌋ < n`, which is what
  discharges `probe`'s `fuel == 0` arm).
* **`clear_refines` shrinks**: `clear` is two field writes and the epoch
  clause does the work; the wrap arm reuses the vacate walk.
* **`remove_refines` grows**: backward-shift deletion has to be shown to
  preserve the run clause, a cyclic-interval argument (`wraps_past`) the
  chained map never needed.  `RepairInv` is Knuth algorithm R's loop
  invariant and `repair_spec` its three-arm step analysis; `RepairInv.stop`
  is `repair`'s own `fuel == 0` obligation, the module's second.

**Two deliberate departures from `Refine/HashMap.lean`'s own shape**, and
both are what keeps this file near the 1 900–2 300 lines task #97-P6-4b
priced despite `remove` costing half again what it thought:

1. **The `Eq2Fwd`/`KeysOk` form is proved once and the `Eq2Spec` form is a
   corollary.**  `HashMap.lean` proves the unrestricted form and
   `HashMapWF.lean` re-proves the restricted one by copying the scripts; the
   restricted form is strictly more general (`Eq2Fwd_of_Eq2Spec` at
   `P := fun _ => True`), so every lemma here is proved once, in the general
   form, and the unrestricted `*_refines` of `HashMap.lean`'s API are
   one-liners over it.  `Refine/HashMap2WF.lean` carries the `_wf` names and
   the `RelOn` bridge, statement for statement as `HashMapWF.lean` gives them.
2. **`Inv.run`'s home index is existentially indexed, not modular.**  The
   clause reads "`j` is `D` steps forward of the key's home slot, `D < n`, and
   every slot strictly closer to the home is live", which is `cyc`-free and
   therefore `omega`-friendly.  `cyc`/`wraps_past` appear only in the
   `remove`/`repair` section, which is the one place the code computes a
   cyclic distance — and `RepairInv` carries its scan distance the same way,
   as a parameter with `1 ≤ D ≤ n`, because `cyc n hole j` is *wrong* at the
   wrap: it reads `0` when `j` comes back round to `hole`, which is precisely
   where the scan ends.

**No assumption whatsoever is made about `hash64`** — exactly as in
`HashMap.lean`, and for the same reason: the invariant says only that a key
sits where *this* function puts it.  Task #97-P6-4b's `home_index` finalizer
is therefore invisible here, as its section predicted.

**The saturation corner.**  `try_resize` sets `saturated := true` when the
slot count exceeds `usize::MAX / 2`; from then on `insert` never resizes, so
`num_entries` can reach `slots.len()`, the probe's `fuel == 0` arm becomes
reachable and an `insert` overwrites a live entry — i.e. the specification is
*false* in that corner.  It needs a table of `2^63` slots (`2^63 · 20` bytes)
and is unreachable, but it is a model state, so the growing operations
(`try_resize_spec`, `insert_refines`) carry the hypothesis
`2 * m.slots.val.length ≤ Usize.max` — "the table can still double" — which
is exactly what excludes it.  Every non-growing operation is unconditional.
See DESIGN.md's `Task #97-HM2` section.

Naming: `Refine/README.md`'s rule — the public entry points get
`<fn>_refines`, the private Rust helpers `<fn>_spec`.
-/
import ConRon.Refine.HashMapWF

open Aeneas Aeneas.Std Result
open ConRon.Generated

open ConRon.Refine.HashMap (lookupK lookupK_nil lookupK_cons lookupK_eq_none_iff
  lookupK_eq_none_of_not_mem lookupK_mem lookupK_eq_some_of_mem lookupK_congr
  lookupK_append lookupK_perm eraseK eraseK_nil eraseK_cons eraseK_sublist
  eraseK_eq_self lookupK_eraseK length_eraseK_of_nodup bind_eq_ok_iff
  uscalar_add_eq uscalar_sub_eq uscalar_mul_eq uscalar_div_eq vec_index_eq
  vec_index_mut_eq vec_len_eq_zero_iff vec_push_eq vec_len_congr
  getElem!_set_self getElem!_set_ne Eq2Spec Eq2Fwd Eq2Fwd_of_Eq2Spec eq2_ite
  DupId take_one_drop)

namespace ConRon.Refine.HashMap2

attribute [local simp] bind_eq_ok_iff lookupK_nil lookupK_cons eraseK_nil eraseK_cons

variable {K V : Type} [DecidableEq K]
  {HashableInst : ron.hashmap.Hashable K} {Eq2Inst : ron.hashmap.Eq2 K}

omit [DecidableEq K] in
instance : Inhabited (ron.hashmap2.Slot K V) := ⟨.Vacant⟩


/-! ## `List.filterMap`, read one slot at a time

`sl_v` is a `filterMap` over the slot vector, so the three moves every proof
below makes on it are the three below: split the list at one index, replace
that index, and recover the index of a member. -/

section ListPlumbing

variable {α β : Type}

/-- Split an `if` inside the generated code *up to definitional equality*.
The generated bodies bind their tuples with pattern `let`s, which `split` will
not see through; a lemma applied to the hypothesis unifies through them by
`whnf`, which is why every arm below is peeled with a lemma and not a
tactic. -/
theorem ite_eq_ok {α : Type} {c : Prop} [Decidable c] {x y : Result α} {r : α}
    (h : (if c then x else y) = ok r) : (c ∧ x = ok r) ∨ (¬ c ∧ y = ok r) := by
  by_cases hc : c
  · exact Or.inl ⟨hc, by simpa [hc] using h⟩
  · exact Or.inr ⟨hc, by simpa [hc] using h⟩

theorem filterMap_cons_eq (f : α → Option β) (a : α) (l : List α) :
    (a :: l).filterMap f = (f a).toList ++ l.filterMap f := by
  cases h : f a <;> simp [h]

theorem filterMap_set {l : List α} {f : α → Option β} {i : Nat} (hi : i < l.length) (x : α) :
    (l.set i x).filterMap f
      = (l.take i).filterMap f ++ ((f x).toList ++ (l.drop (i + 1)).filterMap f) := by
  rw [List.set_eq_take_append_cons_drop, if_pos hi, List.filterMap_append, filterMap_cons_eq]

theorem filterMap_split [Inhabited α] {l : List α} {f : α → Option β} {i : Nat}
    (hi : i < l.length) :
    l.filterMap f
      = (l.take i).filterMap f ++ ((f l[i]!).toList ++ (l.drop (i + 1)).filterMap f) := by
  conv_lhs => rw [← List.set_getElem_self hi]
  rw [filterMap_set hi, List.getElem!_of_getElem? (List.getElem?_eq_getElem hi)]

/-- Replacing one slot: the new list is the new entry against everything the
replaced slot did not contribute.  `y` is the neutral slot (`Slot.Vacant`,
whose `f` is `none`), so the right-hand side is independent of what stood at
`i` before. -/
theorem filterMap_set_perm {l : List α} {f : α → Option β} {i : Nat}
    (hi : i < l.length) (x y : α) (hy : f y = none) :
    ((l.set i x).filterMap f).Perm ((f x).toList ++ (l.set i y).filterMap f) := by
  rw [filterMap_set hi x, filterMap_set hi y, hy]
  simpa using List.perm_append_comm_assoc ((l.take i).filterMap f) ((f x).toList)
    ((l.drop (i + 1)).filterMap f)

theorem filterMap_perm [Inhabited α] {l : List α} {f : α → Option β} {i : Nat}
    (hi : i < l.length) (y : α) (hy : f y = none) :
    (l.filterMap f).Perm ((f l[i]!).toList ++ (l.set i y).filterMap f) := by
  conv_lhs => rw [← List.set_getElem_self hi]
  rw [List.getElem!_of_getElem? (List.getElem?_eq_getElem hi)]
  exact filterMap_set_perm hi _ y hy

theorem mem_filterMap_index [Inhabited α] {l : List α} {f : α → Option β} {b : β}
    (h : b ∈ l.filterMap f) : ∃ i, i < l.length ∧ f l[i]! = some b := by
  obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.1 h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
  exact ⟨i, hi, by rwa [List.getElem!_of_getElem? (List.getElem?_eq_getElem hi)]⟩

theorem mem_filterMap_of_index [Inhabited α] {l : List α} {f : α → Option β} {b : β}
    {i : Nat} (hi : i < l.length) (h : f l[i]! = some b) : b ∈ l.filterMap f := by
  rw [List.getElem!_of_getElem? (List.getElem?_eq_getElem hi)] at h
  exact List.mem_filterMap.2 ⟨l[i], List.getElem_mem hi, h⟩

theorem getElem!_cons_succ [Inhabited α] (a : α) (l : List α) (i : Nat) :
    (a :: l)[i + 1]! = l[i]! := by
  simp [List.getElem!_eq_getElem?_getD]

theorem length_filterMap_le {l : List α} {f : α → Option β} :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a r ih => cases h : f a <;> simp [h] <;> omega

/-- If the `filterMap` is shorter than the list, some element maps to `none` —
which is how "`num_entries < capacity`" becomes "some slot is free", the fact
that discharges `probe`'s `fuel == 0` arm. -/
theorem exists_none_of_length_lt [Inhabited α] {l : List α} {f : α → Option β}
    (h : (l.filterMap f).length < l.length) : ∃ i, i < l.length ∧ f l[i]! = none := by
  induction l with
  | nil => simp at h
  | cons a r ih =>
    cases hfa : f a with
    | none => exact ⟨0, by simp, by simpa using hfa⟩
    | some b =>
      simp only [List.filterMap_cons, hfa, List.length_cons] at h
      obtain ⟨i, hi, hf⟩ := ih (by omega)
      exact ⟨i + 1, by simpa using hi, by rwa [getElem!_cons_succ]⟩

end ListPlumbing


/-! ## The model of a slot and of the table -/

/-- **A slot's entry, if it is live.**  A `Live` slot counts only if its stamp
is the table's current `epoch`; a stale stamp is free space, indistinguishable
from `Vacant` to every operation.  This is the whole of the epoch scheme, and
it is why `clear` is `epoch += 1`. -/
def liveAt (e : Std.U32) : ron.hashmap2.Slot K V → Option (K × V)
  | .Vacant => none
  | .Live g k v => if g = e then some (k, v) else none

omit [DecidableEq K] in
@[local simp] theorem liveAt_vacant (e : Std.U32) :
    liveAt (K := K) (V := V) e .Vacant = none := rfl

omit [DecidableEq K] in
@[local simp] theorem liveAt_live (e g : Std.U32) (k : K) (v : V) :
    liveAt e (.Live g k v) = if g = e then some (k, v) else none := rfl

omit [DecidableEq K] in
/-- The default slot is `Vacant`: this is what `slots[j]!` gives outside the
range, which is *every* `j` on an unallocated table (task #35's lazy
allocation, kept). -/
@[local simp] theorem liveAt_default (e : Std.U32) :
    liveAt (K := K) (V := V) e default = none := rfl

omit [DecidableEq K] in
theorem liveAt_epoch {e g : Std.U32} {k : K} {v : V} {p : K × V}
    (h : liveAt e (.Live g k v) = some p) : g = e ∧ p = (k, v) := by
  simp only [liveAt_live] at h
  split at h
  · rename_i hg; exact ⟨hg, by simpa using h.symm⟩
  · simp at h

omit [DecidableEq K] in
/-- A slot that reads live at `e` *is* a `Live` slot stamped `e`. -/
theorem liveAt_inv {e : Std.U32} {s : ron.hashmap2.Slot K V} {k : K} {v : V}
    (h : liveAt e s = some (k, v)) : s = .Live e k v := by
  cases s with
  | Vacant => simp at h
  | Live g k' v' =>
    obtain ⟨hge, hkv⟩ := liveAt_epoch h
    have h1 : k = k' := congrArg Prod.fst hkv
    have h2 : v = v' := congrArg Prod.snd hkv
    rw [hge, h1, h2]

/-- **The whole table as one association list**: the live slots, in index
order.  The replacement for `al_v`, and the only place the representation is
mentioned. -/
def sl_v (m : ron.hashmap2.HashMap2 K V) : List (K × V) :=
  m.slots.val.filterMap (liveAt m.epoch)

/-- The entry at slot `j`, if it is live.  `Vacant` outside the range. -/
def slotKV (m : ron.hashmap2.HashMap2 K V) (j : Nat) : Option (K × V) :=
  liveAt m.epoch m.slots.val[j]!

/-- Is slot `j` live?  The run clause of `Inv` is a conjunction of these. -/
def isLive (m : ron.hashmap2.HashMap2 K V) (j : Nat) : Prop := (slotKV m j).isSome

/-- The entries of every slot but `i` — the analogue of `HashMap.lean`'s
`restOf`, written as "the table with slot `i` vacated" so that a member's
index is recoverable. -/
def rest (m : ron.hashmap2.HashMap2 K V) (i : Nat) : List (K × V) :=
  (m.slots.val.set i .Vacant).filterMap (liveAt m.epoch)

/-- The home slot of `k` among `n` slots.  A plain function of the key: the
proofs never look inside it, and in particular task #97-P6-4b's multiply-xor
finalizer is invisible to every statement below. -/
def homeAt (HashableInst : ron.hashmap.Hashable K) (n : Std.Usize) (k : K) :
    Result Std.Usize := do
  let h ← HashableInst.hash64 k
  ron.hashmap2.home_index h n

/-- `d` steps forward of `a` among `n` slots. -/
def idx (n a d : Nat) : Nat := (a + d) % n

/-- The number of forward steps from `a` to `b` among `n` slots — Knuth's
algorithm R's distance, and the only place a *cyclic* quantity is needed
(`wraps_past`, in the `remove` section). -/
def cyc (n a b : Nat) : Nat := (b + n - a) % n


/-! ## The table invariant -/

/-- **The table invariant.**

The five clauses `HashMap.lean`'s `Inv` has, with `slot_inv` replaced by
`run`, and three new ones:

* `pow2`, `min_cap` — the capacity is a power of two of at least
  `MIN_CAPACITY`, *or zero* (the unallocated table of `new`, task #35);
* `max_load_eq`, `fit` — `num_entries ≤ max_load = 3·⌊n/4⌋`, hence
  `num_entries < n`: **there is always a free slot**, which is what makes
  `probe`'s `fuel == 0` arm unreachable;
* `sat` — the table has not saturated (`try_resize`'s `usize::MAX / 2`
  branch); see the module note;
* `epoch_pos`, `stamps` — the epoch is at least 1 and no slot carries a stamp
  above it, which is exactly what makes `clear`'s `epoch += 1` empty the
  table;
* `nodup`, `entries` — keys are pairwise distinct and `num_entries` counts
  them, verbatim from `HashMap.lean`;
* `run` — **every live key is reachable from its home slot by a run of live
  slots**.  Stated as "`j` is `D` steps forward of the home, `D < n`, and
  every slot strictly closer to the home is live", which also pins the home
  index inside the range (the `i.val < n` conjunct), the fact `repair`'s
  cyclic-interval argument needs and that no property of `hash64` would
  give. -/
structure Inv0 (HashableInst : ron.hashmap.Hashable K) (m : ron.hashmap2.HashMap2 K V) :
    Prop where
  pow2 : 0 < m.slots.val.length → ∃ e, m.slots.val.length = 2 ^ e
  min_cap : 0 < m.slots.val.length → 32 ≤ m.slots.val.length
  max_load_eq : 0 < m.slots.val.length → m.max_load.val = 3 * (m.slots.val.length / 4)
  sat : m.saturated = false
  epoch_pos : 1 ≤ m.epoch.val
  stamps : ∀ (j : Nat) (g : Std.U32) (k : K) (v : V),
      m.slots.val[j]! = .Live g k v → g.val ≤ m.epoch.val
  nodup : ((sl_v m).map Prod.fst).Nodup
  entries : m.num_entries.val = (sl_v m).length
  run : ∀ (j : Nat) (k : K) (v : V) (i : Std.Usize),
      j < m.slots.val.length → slotKV m j = some (k, v) →
      homeAt HashableInst (alloc.vec.Vec.len m.slots) k = ok i →
      i.val < m.slots.val.length ∧
      ∃ D, D < m.slots.val.length ∧ j = idx m.slots.val.length i.val D ∧
        ∀ d, d < D → isLive m (idx m.slots.val.length i.val d)

/-- `Inv0` and the **load** clause.  The two are separated because
`insert_no_resize` transiently breaks exactly this one — it writes an entry
and leaves `insert`'s doubling to put `num_entries` back under `max_load` —
and nothing else. -/
structure Inv (HashableInst : ron.hashmap.Hashable K) (m : ron.hashmap2.HashMap2 K V) :
    Prop extends Inv0 HashableInst m where
  fit : m.num_entries.val ≤ m.max_load.val

/-- **Every key the table holds satisfies `P`** — `HashMapWF.lean`'s side
condition, verbatim, over `sl_v`. -/
def KeysOk (P : K → Prop) (m : ron.hashmap2.HashMap2 K V) : Prop := ∀ p ∈ sl_v m, P p.1

/-- **The abstract map**: the partial function the table denotes.  The same
equation `HashMap.lean` gives, over `sl_v` instead of `al_v`; it mentions
neither the hash function nor the probe. -/
def toFun (m : ron.hashmap2.HashMap2 K V) (k : K) : Option V := lookupK (sl_v m) k


/-! ## Cyclic index arithmetic

`idx n a d` is "`d` steps forward of `a`", and that is the only shape the
invariant and the probe need: `Inv.run` names the distance rather than
computing it, so nothing below has to reduce a `%` that `omega` cannot see. -/

section Cyc

variable {n a b c d d' : Nat}

theorem idx_lt (hn : 0 < n) : idx n a d < n := Nat.mod_lt _ hn

theorem idx_zero (ha : a < n) : idx n a 0 = a := by simp [idx, Nat.mod_eq_of_lt ha]

theorem idx_succ : idx n a (d + 1) = (idx n a d + 1) % n := by
  rw [idx, idx, Nat.mod_add_mod, ← Nat.add_assoc]

/-- One wrap at most: `a % n + d` is below `2n`, so the modulus subtracts `n`
once or not at all.  Everything `idx_inj` needs. -/
theorem idx_cases (hn : 0 < n) (hd : d < n) :
    idx n a d = a % n + d ∨ idx n a d + n = a % n + d := by
  have hr : a % n < n := Nat.mod_lt _ hn
  have e1 : idx n a d = (a % n + d) % n := by rw [idx, Nat.mod_add_mod]
  rcases Nat.lt_or_ge (a % n + d) n with h1 | h1
  · exact Or.inl (by rw [e1, Nat.mod_eq_of_lt h1])
  · right
    rw [e1, Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    omega

theorem idx_inj (hn : 0 < n) (hd : d < n) (hd' : d' < n) (h : idx n a d = idx n a d') :
    d = d' := by
  rcases idx_cases (a := a) hn hd with e1 | e1 <;>
    rcases idx_cases (a := a) hn hd' with e2 | e2 <;> omega

/-- Every slot is `d` steps forward of every other, for exactly one `d < n`:
this is what turns "the probe walked `n` slots" into "the probe walked *every*
slot", and hence into the contradiction with the free slot. -/
theorem idx_surj {j : Nat} (hn : 0 < n) (hj : j < n) : ∃ d, d < n ∧ idx n a d = j := by
  have hr : a % n < n := Nat.mod_lt _ hn
  rcases Nat.lt_or_ge j (a % n) with h1 | h1
  · refine ⟨j + n - a % n, by omega, ?_⟩
    rw [idx, ← Nat.mod_add_mod, show a % n + (j + n - a % n) = j + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  · refine ⟨j - a % n, by omega, ?_⟩
    rw [idx, ← Nat.mod_add_mod, show a % n + (j - a % n) = j by omega, Nat.mod_eq_of_lt hj]

/-! `cyc` is the same distance `idx` counts, computed instead of named — it is
what `wraps_past` compares, so the `remove`/`repair` section needs the two
round-trips and the triangle identity below, and nothing else. -/

theorem cyc_lt (hn : 0 < n) : cyc n a b < n := Nat.mod_lt _ hn

theorem cyc_self (ha : a < n) : cyc n a a = 0 := by
  rw [cyc, show a + n - a = n by omega, Nat.mod_self]

theorem idx_cyc (ha : a < n) (hb : b < n) : idx n a (cyc n a b) = b := by
  rw [idx, cyc, Nat.add_mod_mod, show a + (b + n - a) = b + n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hb]

theorem cyc_idx (hn : 0 < n) (ha : a < n) (hd : d < n) : cyc n a (idx n a d) = d :=
  idx_inj hn (cyc_lt hn) hd (by rw [idx_cyc ha (idx_lt hn)])

theorem cyc_eq_zero (ha : a < n) (hb : b < n) (h : cyc n a b = 0) : a = b := by
  have hi := idx_cyc ha hb
  rwa [h, idx_zero ha] at hi

/-- **The triangle identity.**  Going `a → c` is going `a → b` then `b → c`,
modulo one wrap; `cyc_cases` is the `omega`-shaped form every step of the
repair walk uses. -/
theorem cyc_trans (ha : a < n) (hb : b < n) (_hc : c < n) :
    cyc n a c = (cyc n a b + cyc n b c) % n := by
  have e : (b + n - a) + (c + n - b) = (c + n - a) + n := by omega
  calc cyc n a c = ((c + n - a) + n) % n := by rw [cyc, Nat.add_mod_right]
    _ = ((b + n - a) + (c + n - b)) % n := by rw [e]
    _ = ((b + n - a) % n + (c + n - b) % n) % n := by rw [Nat.add_mod]
    _ = (cyc n a b + cyc n b c) % n := rfl

theorem cyc_cases (hn : 0 < n) (ha : a < n) (hb : b < n) (hc : c < n) :
    cyc n a c = cyc n a b + cyc n b c ∨ cyc n a c + n = cyc n a b + cyc n b c := by
  have h1 : cyc n a b < n := cyc_lt hn
  have h2 : cyc n b c < n := cyc_lt hn
  have h3 : cyc n a c < n := cyc_lt hn
  have ht := cyc_trans (n := n) ha hb hc
  rcases Nat.lt_or_ge (cyc n a b + cyc n b c) n with hlt | hge
  · exact Or.inl (by rw [ht, Nat.mod_eq_of_lt hlt])
  · right
    rw [ht, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h3 ⊢
    omega

/-- One step forward moves every other slot one step closer. -/
theorem cyc_step (hn : 1 < n) {j q : Nat} (hj : j < n) (hq : q < n) (hne : q ≠ j) :
    cyc n (idx n j 1) q + 1 = cyc n j q := by
  have h1 : cyc n j (idx n j 1) = 1 := cyc_idx (by omega) hj (by omega)
  have h2 : cyc n j q < n := cyc_lt (by omega)
  have h3 : cyc n (idx n j 1) q < n := cyc_lt (by omega)
  have hz : cyc n j q ≠ 0 := fun hc => hne (cyc_eq_zero hj hq hc).symm
  rcases cyc_cases (n := n) (b := idx n j 1) (by omega) hj
    (idx_lt (a := j) (d := 1) (by omega)) hq with he | he <;> omega

/-- The capacity is a multiple of four and `max_load` is strictly below it:
this is the arithmetic behind "there is always a free slot". -/
theorem cap_div_four (h2 : ∃ e, n = 2 ^ e) (h32 : 32 ≤ n) :
    4 * (n / 4) = n ∧ 3 * (n / 4) < n := by
  obtain ⟨e, rfl⟩ := h2
  have he : 5 ≤ e := by
    by_contra hc
    have h1 : e ≤ 4 := by omega
    have h2 : (2 : Nat) ^ e ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) h1
    simp at h2; omega
  have hsplit : (2 : Nat) ^ e = 4 * 2 ^ (e - 2) := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    congr 1; omega
  have hpos : 0 < (2 : Nat) ^ (e - 2) := Nat.pow_pos (by omega)
  have hq : (2 : Nat) ^ e / 4 = 2 ^ (e - 2) := by rw [hsplit]; omega
  rw [hq]; omega

end Cyc


/-! ## The abstract map and the slots -/

variable {m : ron.hashmap2.HashMap2 K V}

omit [DecidableEq K] in
/-- Outside the slot vector every read is `Vacant`, which is *every* read on
the unallocated table `new` returns (task #35's lazy allocation, kept). -/
@[local simp] theorem slotKV_of_ge {j : Nat} (hj : m.slots.val.length ≤ j) :
    slotKV m j = none := by
  rw [slotKV, List.getElem!_eq_getElem?_getD, List.getElem?_eq_none hj]; rfl

omit [DecidableEq K] in
theorem slotKV_lt {j : Nat} {p : K × V} (h : slotKV m j = some p) :
    j < m.slots.val.length := by
  by_contra hc
  rw [slotKV_of_ge (by omega)] at h; simp at h

omit [DecidableEq K] in
theorem mem_sl_v_of_slot {j : Nat} {p : K × V} (hj : j < m.slots.val.length)
    (h : slotKV m j = some p) : p ∈ sl_v m :=
  mem_filterMap_of_index hj h

omit [DecidableEq K] in
theorem slot_of_mem_sl_v {p : K × V} (h : p ∈ sl_v m) :
    ∃ j, j < m.slots.val.length ∧ slotKV m j = some p :=
  mem_filterMap_index h

omit [DecidableEq K] in
/-- The table is one entry against all the others. -/
theorem sl_v_perm_rest {i : Nat} (hi : i < m.slots.val.length) :
    (sl_v m).Perm ((slotKV m i).toList ++ rest m i) :=
  filterMap_perm hi .Vacant rfl

omit [DecidableEq K] in
/-- The same, with slot `i` replaced: the `rest` is the *same* list, which is
what makes one permutation carry lookup, length and nodup at once (the shape
`HashMap.lean`'s `al_v_set_perm_rest` has). -/
theorem sl_v_set_perm_rest {i : Nat} (hi : i < m.slots.val.length)
    (x : ron.hashmap2.Slot K V) :
    ((m.slots.val.set i x).filterMap (liveAt m.epoch)).Perm
      ((liveAt m.epoch x).toList ++ rest m i) :=
  filterMap_set_perm hi x .Vacant rfl

omit [DecidableEq K] in
theorem mem_rest {i : Nat} {p : K × V} (h : p ∈ rest m i) :
    ∃ j, j ≠ i ∧ j < m.slots.val.length ∧ slotKV m j = some p := by
  obtain ⟨j, hj, hf⟩ := mem_filterMap_index h
  rw [List.length_set] at hj
  have hne : j ≠ i := by
    rintro rfl
    rw [getElem!_set_self _ hj] at hf; simp at hf
  exact ⟨j, hne, hj, by rwa [getElem!_set_ne _ hne] at hf⟩

omit [DecidableEq K] in
theorem mem_rest_of {i j : Nat} {p : K × V} (hne : j ≠ i) (hj : j < m.slots.val.length)
    (h : slotKV m j = some p) : p ∈ rest m i := by
  refine mem_filterMap_of_index (by rw [List.length_set]; exact hj) ?_
  rwa [getElem!_set_ne _ hne]

omit [DecidableEq K] in
theorem rest_subset {i : Nat} {p : K × V} (h : p ∈ rest m i) : p ∈ sl_v m := by
  obtain ⟨j, -, hj, hs⟩ := mem_rest h
  exact mem_sl_v_of_slot hj hs

omit [DecidableEq K] in
/-- Writing one slot: what the *other* slots read.  The three lemmas below are
the whole interface between an operation that sets a slot and `sl_v`. -/
theorem slotKV_set_ne {m' : ron.hashmap2.HashMap2 K V} {i j : Nat}
    {x : ron.hashmap2.Slot K V} (he : m'.epoch = m.epoch)
    (hs : m'.slots.val = m.slots.val.set i x) (hne : j ≠ i) :
    slotKV m' j = slotKV m j := by
  rw [slotKV, slotKV, he, hs, getElem!_set_ne _ hne]

omit [DecidableEq K] in
theorem slotKV_set_self {m' : ron.hashmap2.HashMap2 K V} {i : Nat}
    {x : ron.hashmap2.Slot K V} (he : m'.epoch = m.epoch)
    (hs : m'.slots.val = m.slots.val.set i x) (hi : i < m.slots.val.length) :
    slotKV m' i = liveAt m.epoch x := by
  rw [slotKV, he, hs, getElem!_set_self _ hi]

omit [DecidableEq K] in
theorem sl_v_set {m' : ron.hashmap2.HashMap2 K V} {i : Nat} {x : ron.hashmap2.Slot K V}
    (he : m'.epoch = m.epoch) (hs : m'.slots.val = m.slots.val.set i x)
    (hi : i < m.slots.val.length) :
    (sl_v m').Perm ((liveAt m.epoch x).toList ++ rest m i) := by
  rw [sl_v, he, hs]
  exact filterMap_set_perm hi x .Vacant rfl

/-- Under `Inv`, a live slot's entry *is* the abstract map's answer.  This is
where the slot structure and `toFun` meet on the found side. -/
theorem toFun_eq_of_slot (hinv : Inv HashableInst m) {j : Nat} {k : K} {v : V}
    (hj : j < m.slots.val.length) (h : slotKV m j = some (k, v)) : toFun m k = some v :=
  lookupK_eq_some_of_mem hinv.nodup (mem_sl_v_of_slot hj h)

/-- …and a key held by no live slot is not in the map. -/
theorem toFun_eq_none_of_no_slot {k : K}
    (h : ∀ j, j < m.slots.val.length → ∀ v, slotKV m j ≠ some (k, v)) : toFun m k = none := by
  refine lookupK_eq_none_of_not_mem ?_
  intro hmem
  obtain ⟨⟨k', v⟩, hp, hfst⟩ := List.mem_map.1 hmem
  simp only at hfst
  subst hfst
  obtain ⟨j, hj, hs⟩ := slot_of_mem_sl_v hp
  exact h j hj v hs

omit [DecidableEq K] in
/-- `num_entries` is below the capacity, hence **some slot is free** — the
fact that discharges `probe`'s `fuel == 0` arm. -/
theorem num_entries_lt (hinv : Inv HashableInst m) (hpos : 0 < m.slots.val.length) :
    m.num_entries.val < m.slots.val.length := by
  have h := hinv.fit
  rw [hinv.max_load_eq hpos] at h
  exact lt_of_le_of_lt h (cap_div_four (hinv.pow2 hpos) (hinv.min_cap hpos)).2

omit [DecidableEq K] in
theorem exists_free_slot (hinv : Inv HashableInst m) (hpos : 0 < m.slots.val.length) :
    ∃ j, j < m.slots.val.length ∧ slotKV m j = none := by
  have hlt : (sl_v m).length < m.slots.val.length := by
    rw [← hinv.entries]; exact num_entries_lt hinv hpos
  exact exists_none_of_length_lt hlt


/-! ## The probe

`probe_walk` is the shape of the walk — the recursion read forwards — and
`probe_spec` is what every operation uses: under `Inv`, the probe answers the
abstract map, and its `fuel == 0` arm is unreachable. -/

omit [DecidableEq K] in
theorem next_index_spec {i n r : Std.Usize} (hi : i.val < n.val)
    (h : ron.hashmap2.next_index i n = ok r) : r.val = (i.val + 1) % n.val := by
  rw [ron.hashmap2.next_index] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨j, hj, h⟩ := h
  have hjv : j.val = i.val + 1 := by rw [uscalar_add_eq hj]; simp
  split at h
  · rename_i hge
    have hn : i.val + 1 = n.val := by scalar_tac
    rw [← Result.ok_injective h]
    simp [← hn]
  · rename_i hge
    have hn : j.val < n.val := by scalar_tac
    rw [← Result.ok_injective h, hjv, Nat.mod_eq_of_lt (by omega)]

/-- **The probe walk.**  Read forwards: `probe` steps one slot at a time from
`i`, over live slots whose key is not `key`, and stops at the first slot that
is either `key`'s own (`b = true`) or free (`b = false`) — or when the fuel
runs out, which is the `d = F` disjunct `probe_spec` then shows impossible.

The `fuel == 0` arm returns `(i, false)`, and that is why the disjunct has to
be carried at all: nothing whatever is known about the slot that arm names. -/
theorem probe_walk {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    {slots : alloc.vec.Vec (ron.hashmap2.Slot K V)} {e : Std.U32} {key : K}
    (hk : P key)
    (hkeys : ∀ (j : Nat) (p : K × V), liveAt e slots.val[j]! = some p → P p.1)
    {n : Std.Usize} (hpos : 0 < n.val) (F : Nat) :
    ∀ (i fuel at1 : Std.Usize) (b : Bool),
      fuel.val = F → i.val < n.val →
      ron.hashmap2.probe Eq2Inst slots e key i n fuel = ok (at1, b) →
      ∃ d : Nat, d ≤ F ∧ at1.val = idx n.val i.val d ∧
        (∀ d', d' < d →
          ∃ p, liveAt e slots.val[idx n.val i.val d']! = some p ∧ p.1 ≠ key) ∧
        (b = true → ∃ w, liveAt e slots.val[at1.val]! = some (key, w)) ∧
        (b = false → d = F ∨ liveAt e slots.val[at1.val]! = none) := by
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro i fuel at1 b hF hi h
    rw [ron.hashmap2.probe.eq_def] at h
    split at h
    · -- the fuel is gone: `(i, false)`, and nothing is known about slot `i`
      rename_i h0
      have hF0 : F = 0 := by rw [← hF]; scalar_tac
      have e1 := Result.ok_injective h
      have ea : at1 = i := (congrArg Prod.fst e1).symm
      have eb : b = false := (congrArg Prod.snd e1).symm
      subst ea; subst eb
      exact ⟨0, by omega, (idx_zero hi).symm, by omega, by simp, fun _ => Or.inl hF0.symm⟩
    · rename_i h0
      have hFne : F ≠ 0 := by rw [← hF]; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨s, hs, h⟩ := h
      obtain ⟨hilt, hseq⟩ := vec_index_eq hs
      cases hsc : s with
      | Vacant =>
        rw [hsc] at h hseq
        simp only at h
        have e1 := Result.ok_injective h
        have ea : at1 = i := (congrArg Prod.fst e1).symm
        have eb : b = false := (congrArg Prod.snd e1).symm
        subst ea; subst eb
        refine ⟨0, by omega, (idx_zero hi).symm, by omega, by simp, fun _ => Or.inr ?_⟩
        rw [← hseq]; rfl
      | Live g ckey cval =>
        rw [hsc] at h hseq
        simp only at h
        split at h
        · -- a stale stamp: free space, and the probe stops
          rename_i hne
          have hgne : ¬ (g = e) := by rw [UScalar.eq_equiv]; simpa using hne
          have e1 := Result.ok_injective h
          have ea : at1 = i := (congrArg Prod.fst e1).symm
          have eb : b = false := (congrArg Prod.snd e1).symm
          subst ea; subst eb
          refine ⟨0, by omega, (idx_zero hi).symm, by omega, by simp, fun _ => Or.inr ?_⟩
          rw [← hseq]; simp [hgne]
        · rename_i hne
          have hge : g = e := UScalar.val_eq_imp _ _ (by simpa using hne)
          have hPc : P ckey := hkeys i.val (ckey, cval) (by rw [← hseq]; simp [hge])
          rcases eq2_ite heq hPc hk h with ⟨hkc, h⟩ | ⟨hkc, h⟩
          · -- the key's own slot
            have e1 := Result.ok_injective h
            have ea : at1 = i := (congrArg Prod.fst e1).symm
            have eb : b = true := (congrArg Prod.snd e1).symm
            subst ea; subst eb
            refine ⟨0, by omega, (idx_zero hi).symm, by omega, fun _ => ⟨cval, ?_⟩, by simp⟩
            rw [← hseq]; simp [hge, hkc]
          · -- a live slot holding another key: step forward
            simp only [bind_eq_ok_iff] at h
            obtain ⟨i1, hi1, fuel1, hfuel1, hrec⟩ := h
            have hi1v : i1.val = (i.val + 1) % n.val := next_index_spec hi hi1
            have hfv : fuel1.val = F - 1 := by rw [uscalar_sub_eq hfuel1, hF]; simp
            have hi1lt : i1.val < n.val := by rw [hi1v]; exact Nat.mod_lt _ hpos
            obtain ⟨d, hd, hat, hwalk, htrue, hfalse⟩ :=
              ih (F - 1) (by omega) i1 fuel1 at1 b hfv hi1lt hrec
            have hidx : ∀ d', idx n.val i1.val d' = idx n.val i.val (d' + 1) := by
              intro d'
              rw [idx, idx, hi1v, Nat.mod_add_mod]
              congr 1; omega
            refine ⟨d + 1, by omega, by rw [hat, hidx], ?_, htrue, ?_⟩
            · intro d' hd'
              cases d' with
              | zero =>
                refine ⟨(ckey, cval), ?_, hkc⟩
                rw [idx_zero hi, ← hseq]; simp [hge]
              | succ d'' =>
                obtain ⟨p, hp1, hp2⟩ := hwalk d'' (by omega)
                exact ⟨p, by rwa [hidx] at hp1, hp2⟩
            · intro hb
              rcases hfalse hb with hd0 | hnone
              · exact Or.inl (by omega)
              · exact Or.inr hnone

omit [DecidableEq K] in
/-- The probe reads its start slot before anything else, so a successful probe
with fuel to spare puts the home index inside the vector.  This is where the
bound on `home_index`'s result comes from — no property of `hash64` is used. -/
theorem probe_start_lt {slots : alloc.vec.Vec (ron.hashmap2.Slot K V)} {e : Std.U32}
    {key : K} {i n fuel at1 : Std.Usize} {b : Bool} (hfuel : fuel.val ≠ 0)
    (h : ron.hashmap2.probe Eq2Inst slots e key i n fuel = ok (at1, b)) :
    i.val < slots.val.length := by
  rw [ron.hashmap2.probe.eq_def] at h
  split at h
  · exact absurd (by scalar_tac : fuel.val = 0) hfuel
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨s, hs, -⟩ := h
    exact (vec_index_eq hs).1

omit [DecidableEq K] in
theorem KeysOk.slot {P : K → Prop} (hkeys : KeysOk P m) {j : Nat} {p : K × V}
    (h : slotKV m j = some p) : P p.1 :=
  hkeys p (mem_sl_v_of_slot (slotKV_lt h) h)

/-- **`probe`, under the invariant** — the replacement for `HashMap.lean`'s
three `list_*` specs, and the one lemma of this file with real content.

Three things come out, and the operations below use exactly these:

* the slot the probe names is **inside the vector**;
* on `found`, it is the key's own slot, and the abstract map says so;
* on **not found**, it is **free**, the abstract map says the key is absent,
  *and* every slot strictly between the key's home and it is live — which is
  precisely the run clause an `insert` there has to establish.

**The `fuel == 0` obligation of `probe`'s doc comment is discharged here.**
`Inv.fit` puts `num_entries` below the capacity, so `exists_free_slot` gives a
free slot; the walk visits `d` distinct slots and `idx_surj` says that at
`d = slots.len()` it has visited *all* of them, the free one included —
contradicting the walk's own "every slot before the stop is live".  So the
walk stops strictly before the fuel does. -/
theorem probe_spec {P : K → Prop} (heq : Eq2Fwd Eq2Inst P) (hinv : Inv HashableInst m)
    (hkeys : KeysOk P m) {key : K} (hk : P key) {i at1 : Std.Usize} {b : Bool}
    (hpos : 0 < m.slots.val.length)
    (hhome : homeAt HashableInst (alloc.vec.Vec.len m.slots) key = ok i)
    (h : ron.hashmap2.probe Eq2Inst m.slots m.epoch key i
           (alloc.vec.Vec.len m.slots) (alloc.vec.Vec.len m.slots) = ok (at1, b)) :
    at1.val < m.slots.val.length ∧ i.val < m.slots.val.length ∧
    (b = true → ∃ w, slotKV m at1.val = some (key, w) ∧ toFun m key = some w) ∧
    (b = false → slotKV m at1.val = none ∧ toFun m key = none ∧
      ∃ d, d < m.slots.val.length ∧ at1.val = idx m.slots.val.length i.val d ∧
        ∀ d', d' < d → isLive m (idx m.slots.val.length i.val d')) := by
  have hlen : (alloc.vec.Vec.len m.slots).val = m.slots.val.length := alloc.vec.Vec.len_val _
  have hfuel : (alloc.vec.Vec.len m.slots).val ≠ 0 := by omega
  have hilt : i.val < m.slots.val.length := probe_start_lt hfuel h
  obtain ⟨d, hd, hat, hwalk, htrue, hfalse⟩ :=
    probe_walk heq (slots := m.slots) (e := m.epoch) (key := key) hk
      (fun j p hp => hkeys.slot (m := m) (j := j) hp)
      (n := alloc.vec.Vec.len m.slots) (by omega) (alloc.vec.Vec.len m.slots).val
      i (alloc.vec.Vec.len m.slots) at1 b rfl (by omega) h
  rw [hlen] at hd hat hwalk
  have hatlt : at1.val < m.slots.val.length := by rw [hat]; exact idx_lt hpos
  refine ⟨hatlt, hilt, ?_, ?_⟩
  · intro hb
    obtain ⟨w, hw⟩ := htrue hb
    exact ⟨w, hw, toFun_eq_of_slot hinv hatlt hw⟩
  · intro hb
    -- the fuel cannot have run out: the walk would then have visited a free slot
    have hdlt : d < m.slots.val.length := by
      rcases Nat.lt_or_ge d m.slots.val.length with hh | hh
      · exact hh
      · exfalso
        obtain ⟨j, hj, hfree⟩ := exists_free_slot hinv hpos
        obtain ⟨d', hd', hidxj⟩ := idx_surj (a := i.val) hpos hj
        obtain ⟨p, hp, -⟩ := hwalk d' (by omega)
        rw [hidxj] at hp
        rw [show liveAt m.epoch m.slots.val[j]! = slotKV m j from rfl, hfree] at hp
        simp at hp
    have hnone : slotKV m at1.val = none := by
      rcases hfalse hb with hdF | hn
      · exact absurd hdF (by omega)
      · exact hn
    refine ⟨hnone, ?_, d, hdlt, hat, fun d' hd' => ?_⟩
    · -- the key is not in the table at all
      refine toFun_eq_none_of_no_slot ?_
      intro j hj w hs
      obtain ⟨-, D, hD, hjD, hrun⟩ := hinv.run j key w i hj hs hhome
      rcases Nat.lt_or_ge D d with hDd | hDd
      · obtain ⟨p, hp, hpk⟩ := hwalk D hDd
        rw [← hjD] at hp
        rw [show liveAt m.epoch m.slots.val[j]! = slotKV m j from rfl, hs] at hp
        have hpv : p = (key, w) := (Option.some.inj hp).symm
        exact hpk (by rw [hpv])
      · rcases Nat.eq_or_lt_of_le hDd with hDd' | hDd'
        · rw [hat, hDd', ← hjD, hs] at hnone; simp at hnone
        · have := hrun d hDd'
          rw [isLive, ← hat, hnone] at this; simp at this
    · obtain ⟨p, hp, -⟩ := hwalk d' hd'
      rw [isLive, show slotKV m (idx m.slots.val.length i.val d')
        = liveAt m.epoch m.slots.val[idx m.slots.val.length i.val d']! from rfl, hp]
      simp


/-! ## `get`, `contains_key`, `len`, `is_empty`, `capacity` -/

omit [DecidableEq K] in
theorem sl_v_of_slots_nil (h : m.slots.val = []) : sl_v m = [] := by simp [sl_v, h]

/-- `get` answers the abstract map.  The `slots.len() == 0` guard is the
unallocated table of `new` (task #35): it binds nothing, and `home_index`
would underflow on it. -/
theorem get_refines_gen {P : K → Prop} (heq : Eq2Fwd Eq2Inst P) (hinv : Inv HashableInst m)
    (hkeys : KeysOk P m) {key : K} (hk : P key) {r : Option V}
    (h : ron.hashmap2.HashMap2.get HashableInst Eq2Inst m key = ok r) :
    r = toFun m key := by
  rw [ron.hashmap2.HashMap2.get] at h
  split at h
  · rename_i h0
    rw [← Result.ok_injective h, toFun, sl_v_of_slots_nil (vec_len_eq_zero_iff.mp h0)]
    rfl
  · rename_i h0
    have hpos : 0 < m.slots.val.length := by
      rcases Nat.eq_zero_or_pos m.slots.val.length with hz | hp
      · exact absurd (vec_len_eq_zero_iff.mpr (List.eq_nil_of_length_eq_zero hz)) h0
      · exact hp
    simp only [bind_eq_ok_iff] at h
    obtain ⟨hw, hhash, i1, hbi, q, hprobe, h⟩ := h
    obtain ⟨i2, b⟩ := q
    have hhome : homeAt HashableInst (alloc.vec.Vec.len m.slots) key = ok i1 := by
      simp only [homeAt, bind_eq_ok_iff]; exact ⟨hw, hhash, hbi⟩
    obtain ⟨hatlt, hilt, htrue, hfalse⟩ := probe_spec heq hinv hkeys hk hpos hhome hprobe
    have h : (if b = true then
        (do
          let s ← alloc.vec.Vec.index
            (core.slice.index.SliceIndexUsizeSlice (ron.hashmap2.Slot K V)) m.slots i2
          match s with
          | ron.hashmap2.Slot.Vacant => (ok none : Result (Option V))
          | ron.hashmap2.Slot.Live _ _ v => ok (some v))
      else ok none) = ok r := h
    split at h
    · rename_i hb
      obtain ⟨w, hslot, htf⟩ := htrue hb
      simp only [bind_eq_ok_iff] at h
      obtain ⟨s, hs, h⟩ := h
      obtain ⟨-, hseq⟩ := vec_index_eq hs
      subst hseq
      rw [slotKV] at hslot
      cases hsc : m.slots.val[i2.val]! with
      | Vacant => rw [hsc] at hslot; simp at hslot
      | Live g k' v =>
        rw [hsc] at h hslot
        obtain ⟨hge, hkv⟩ := liveAt_epoch hslot
        simp only at h
        have hv : v = w := by simpa using (congrArg Prod.snd hkv).symm
        rw [← Result.ok_injective h, htf, hv]
    · rename_i hb
      obtain ⟨-, htf, -⟩ := hfalse (by simpa using hb)
      rw [← Result.ok_injective h, htf]

theorem contains_key_refines_gen {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv HashableInst m) (hkeys : KeysOk P m) {key : K} (hk : P key) {b : Bool}
    (h : ron.hashmap2.HashMap2.contains_key HashableInst Eq2Inst m key = ok b) :
    b = (toFun m key).isSome := by
  rw [ron.hashmap2.HashMap2.contains_key] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, hb⟩ := h
  rw [← get_refines_gen heq hinv hkeys hk hget]
  cases o <;> simp at hb <;> simp [← hb]

/-- The support of the abstract map. -/
def support (m : ron.hashmap2.HashMap2 K V) : Finset K := ((sl_v m).map Prod.fst).toFinset

theorem mem_support_iff {k : K} : k ∈ support m ↔ (toFun m k).isSome := by
  rw [support, List.mem_toFinset, toFun]
  cases hl : lookupK (sl_v m) k with
  | none => simp [lookupK_eq_none_iff.1 hl]
  | some v =>
    simp only [Option.isSome_some, iff_true]
    exact List.mem_map.2 ⟨(k, v), lookupK_mem hl, rfl⟩

theorem card_support (hinv : Inv HashableInst m) : (support m).card = (sl_v m).length := by
  rw [support, List.toFinset_card_of_nodup hinv.nodup, List.length_map]

theorem len_refines (hinv : Inv HashableInst m) {n : Std.Usize}
    (h : ron.hashmap2.HashMap2.len m = ok n) :
    n.val = (sl_v m).length ∧ n.val = (support m).card := by
  rw [ron.hashmap2.HashMap2.len] at h
  rw [← Result.ok_injective h, hinv.entries, card_support hinv]
  exact ⟨rfl, rfl⟩

theorem toFun_eq_none_iff : (∀ k, toFun m k = none) ↔ sl_v m = [] := by
  constructor
  · intro h
    rcases hl : sl_v m with _ | ⟨x, r⟩
    · rfl
    · exfalso
      have := h x.1
      rw [toFun, hl, lookupK_cons, if_pos rfl] at this
      simp at this
  · intro h k; simp [toFun, h]

theorem is_empty_refines (hinv : Inv HashableInst m) {b : Bool}
    (h : ron.hashmap2.HashMap2.is_empty m = ok b) :
    b = true ↔ ∀ k, toFun m k = none := by
  rw [ron.hashmap2.HashMap2.is_empty] at h
  rw [← Result.ok_injective h, toFun_eq_none_iff]
  have hent := hinv.entries
  simp only [decide_eq_true_eq]
  constructor
  · intro hz
    have h0 : (sl_v m).length = 0 := by rw [← hent, hz]; simp
    exact List.eq_nil_of_length_eq_zero h0
  · intro hz
    have h0 : m.num_entries.val = 0 := by rw [hent, hz]; simp
    scalar_tac

omit [DecidableEq K] in
/-- The one representation query, as `ron::hashmap::HashMap::capacity` is —
and a capacity is invisible to `toFun`, which is what makes `clear_fit`'s
re-sizing a representation choice and nothing else (DESIGN.md §3.2). -/
theorem capacity_refines {c : Std.Usize} (h : ron.hashmap2.HashMap2.capacity m = ok c) :
    c.val = m.slots.val.length := by
  rw [ron.hashmap2.HashMap2.capacity] at h
  rw [← Result.ok_injective h]
  exact alloc.vec.Vec.len_val _


/-! ## Construction: `allocate_slots`, `new`, `ensure_slots`, `with_capacity`

Near-verbatim from `HashMap.lean`, as task #97-P6-4b's table predicted: the
same halving recursion over the same `Vec`, with `Slot::Vacant` for
`AList::Nil`.  The one change is the leaf, which task #97-P6-7 turned into a
block of eight pushes. -/

omit [DecidableEq K] in
@[local simp] theorem getElem!_replicate_vacant (n j : Nat) :
    (List.replicate n (ron.hashmap2.Slot.Vacant : ron.hashmap2.Slot K V))[j]! =
      ron.hashmap2.Slot.Vacant := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

omit [DecidableEq K] in
@[local simp] theorem filterMap_replicate_vacant (e : Std.U32) (n : Nat) :
    (List.replicate n (ron.hashmap2.Slot.Vacant : ron.hashmap2.Slot K V)).filterMap
      (liveAt e) = [] := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ]; simp [ih]

omit [DecidableEq K] in
/-- `allocate_slots slots n` appends `n` `Vacant` slots.  Task #97-P6-7's
eight-push leaf is one more arm than `ron::hashmap`'s and nothing else. -/
theorem allocate_slots_spec (N : Nat) :
    ∀ (slots slots' : alloc.vec.Vec (ron.hashmap2.Slot K V)) (n : Std.Usize), n.val = N →
      ron.hashmap2.HashMap2.allocate_slots slots n = ok slots' →
      slots'.val = slots.val ++ List.replicate n.val ron.hashmap2.Slot.Vacant := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro slots slots' n hN h
    rw [ron.hashmap2.HashMap2.allocate_slots.eq_def] at h
    split at h
    · -- the block leaf: eight pushes, then two halves of what is left
      rename_i h8
      have hn8 : 8 ≤ n.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨s1, hs1, h⟩ := h
      obtain ⟨s2, hs2, h⟩ := h
      obtain ⟨s3, hs3, h⟩ := h
      obtain ⟨s4, hs4, h⟩ := h
      obtain ⟨s5, hs5, h⟩ := h
      obtain ⟨s6, hs6, h⟩ := h
      obtain ⟨s7, hs7, h⟩ := h
      obtain ⟨s8, hs8, h⟩ := h
      obtain ⟨i, hi, h⟩ := h
      obtain ⟨half, hhalf, h⟩ := h
      obtain ⟨s9, hs9, h⟩ := h
      obtain ⟨i1, hi1, h⟩ := h
      have e8 : s8.val = slots.val ++ List.replicate 8 ron.hashmap2.Slot.Vacant := by
        rw [vec_push_eq hs8, vec_push_eq hs7, vec_push_eq hs6, vec_push_eq hs5,
          vec_push_eq hs4, vec_push_eq hs3, vec_push_eq hs2, vec_push_eq hs1]
        simp [List.replicate_succ]
      have hiv : i.val = n.val - 8 := by
        rw [uscalar_sub_eq hi]; simp
      have hhv : half.val = i.val / 2 := by rw [uscalar_div_eq hhalf]; simp
      have hi1v : i1.val = i.val - half.val := uscalar_sub_eq hi1
      have e9 := ih half.val (by omega) s8 s9 half rfl hs9
      have e10 := ih i1.val (by omega) s9 slots' i1 rfl h
      rw [e10, e9, e8, List.append_assoc, List.append_assoc, ← List.replicate_add,
        ← List.replicate_add]
      congr 2
      omega
    · split at h
      · rename_i h0
        rw [← Result.ok_injective h, show n.val = 0 by scalar_tac]; simp
      · rename_i h8 h0
        have hn1 : 1 ≤ n.val := by scalar_tac
        simp only [bind_eq_ok_iff] at h
        obtain ⟨s1, hs1, i, hi, h⟩ := h
        have hiv : i.val = n.val - 1 := by rw [uscalar_sub_eq hi]; simp
        have e1 := ih i.val (by omega) s1 slots' i rfl h
        rw [e1, vec_push_eq hs1, List.append_assoc, show n.val = i.val + 1 by omega,
          List.replicate_succ]
        simp

omit [DecidableEq K] in
theorem max_load_for_spec {c r : Std.Usize} (h : ron.hashmap2.max_load_for c = ok r) :
    r.val = 3 * (c.val / 4) := by
  rw [ron.hashmap2.max_load_for] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨q, hq, hr⟩ := h
  have hden : (ron.hashmap2.LOAD_DEN : Std.Usize).val = 4 := by
    rw [ron.hashmap2.LOAD_DEN]; rfl
  have hnum : (ron.hashmap2.LOAD_NUM : Std.Usize).val = 3 := by
    rw [ron.hashmap2.LOAD_NUM]; rfl
  have hqv : q.val = c.val / 4 := by rw [uscalar_div_eq hq, hden]
  rw [uscalar_mul_eq hr, hqv, hnum]
  omega

omit [DecidableEq K] in
theorem new_with_capacity_pow2_spec {c : Std.Usize} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.new_with_capacity_pow2 K V c = ok m') :
    m'.slots.val = List.replicate c.val ron.hashmap2.Slot.Vacant ∧
    m'.num_entries = 0#usize ∧ m'.max_load.val = 3 * (c.val / 4) ∧
    m'.epoch = 1#u32 ∧ m'.saturated = false ∧ m'.fit_hw = 0#usize := by
  rw [ron.hashmap2.HashMap2.new_with_capacity_pow2] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨slots, hs, i, hi, hm⟩ := h
  have hsv := allocate_slots_spec c.val _ _ c rfl hs
  rw [← Result.ok_injective hm]
  refine ⟨?_, rfl, max_load_for_spec hi, rfl, rfl, rfl⟩
  simpa [alloc.vec.Vec.with_capacity] using hsv

omit [DecidableEq K] in
/-- A table no slot of which is live is the empty map.  `clear`'s epoch bump
leaves *stale* `Live` slots behind, so this — not "every slot is `Vacant`" —
is the shape the empty table takes. -/
theorem sl_v_eq_nil_of_no_live {m' : ron.hashmap2.HashMap2 K V}
    (h : ∀ j : Nat, slotKV m' j = none) : sl_v m' = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro p hp
  obtain ⟨j, hj, hf⟩ := slot_of_mem_sl_v hp
  rw [h j] at hf; simp at hf

/-- **A dead table is the empty map and satisfies `Inv`.**  The four empty
tables of the module go through this: `new_with_capacity_pow2`,
`ensure_slots`' first allocation, `clear`'s epoch bump and `clear_fit`'s
re-make. -/
theorem dead_table_inv {m' : ron.hashmap2.HashMap2 K V}
    (hdead : ∀ j : Nat, slotKV m' j = none)
    (hstamps : ∀ (j : Nat) (g : Std.U32) (k : K) (v : V),
      m'.slots.val[j]! = .Live g k v → g.val ≤ m'.epoch.val)
    (hn : m'.num_entries.val = 0) (hfit : 0 ≤ m'.max_load.val)
    (hpow : 0 < m'.slots.val.length → ∃ e, m'.slots.val.length = 2 ^ e)
    (hmin : 0 < m'.slots.val.length → 32 ≤ m'.slots.val.length)
    (hml : 0 < m'.slots.val.length → m'.max_load.val = 3 * (m'.slots.val.length / 4))
    (hsat : m'.saturated = false) (hep : 1 ≤ m'.epoch.val) :
    Inv HashableInst m' ∧ sl_v m' = [] ∧ ∀ k, toFun m' k = none := by
  have hsl : sl_v m' = [] := sl_v_eq_nil_of_no_live hdead
  refine ⟨⟨⟨hpow, hmin, hml, hsat, hep, hstamps, ?_, ?_, ?_⟩, by omega⟩, hsl,
    fun k => by simp [toFun, hsl]⟩
  · rw [hsl]; simp
  · rw [hsl, hn]; simp
  · intro j k v i hj hslot _
    rw [hdead j] at hslot; simp at hslot

/-- The same for a table of `Vacant` slots — the three *allocating* cases. -/
theorem vacant_table_inv {m' : ron.hashmap2.HashMap2 K V}
    (hs : ∀ j : Nat, m'.slots.val[j]! = ron.hashmap2.Slot.Vacant)
    (_hsl : sl_v m' = []) (hn : m'.num_entries.val = 0) (hfit : 0 ≤ m'.max_load.val)
    (hpow : 0 < m'.slots.val.length → ∃ e, m'.slots.val.length = 2 ^ e)
    (hmin : 0 < m'.slots.val.length → 32 ≤ m'.slots.val.length)
    (hml : 0 < m'.slots.val.length → m'.max_load.val = 3 * (m'.slots.val.length / 4))
    (hsat : m'.saturated = false) (hep : 1 ≤ m'.epoch.val) :
    Inv HashableInst m' ∧ sl_v m' = [] ∧ ∀ k, toFun m' k = none :=
  dead_table_inv (fun j => by rw [slotKV, hs j]; rfl)
    (fun j g k v hx => by rw [hs j] at hx; simp at hx) hn hfit hpow hmin hml hsat hep

theorem empty_table_inv {c : Std.Usize} {m' : ron.hashmap2.HashMap2 K V}
    (hc2 : ∃ e, c.val = 2 ^ e) (hc32 : 32 ≤ c.val)
    (h : ron.hashmap2.HashMap2.new_with_capacity_pow2 K V c = ok m') :
    Inv HashableInst m' ∧ sl_v m' = [] ∧ (∀ k, toFun m' k = none) ∧
      m'.slots.val.length = c.val := by
  obtain ⟨hs, hn, hml, hep, hsat, -⟩ := new_with_capacity_pow2_spec h
  have hlen : m'.slots.val.length = c.val := by rw [hs]; simp
  have hsl : sl_v m' = [] := by rw [sl_v, hs]; simp
  obtain ⟨hinv, h1, h2⟩ := vacant_table_inv (HashableInst := HashableInst)
    (fun j => by rw [hs]; exact getElem!_replicate_vacant _ _) hsl (by rw [hn]; rfl) (by omega)
    (fun _ => by rw [hlen]; exact hc2) (fun _ => by rw [hlen]; exact hc32)
    (fun _ => by rw [hml, hlen]) hsat (by rw [hep]; rfl)
  exact ⟨hinv, h1, h2, hlen⟩

/-- An **unallocated** table — `slots = []` — satisfies `Inv` and denotes `∅`.
This is `new`'s table (task #35's lazy allocation, kept): `pow2`, `min_cap`
and `max_load_eq` are the three clauses the empty capacity needs the
`0 < length` guard for, and the rest hold outright. -/
theorem unallocated_inv (hs : m.slots.val = []) (hn : m.num_entries.val = 0)
    (hml : m.max_load.val = 0) (hsat : m.saturated = false) (hep : 1 ≤ m.epoch.val) :
    Inv HashableInst m ∧ sl_v m = [] ∧ ∀ k, toFun m k = none := by
  refine vacant_table_inv (fun j => ?_) (sl_v_of_slots_nil hs) hn (by omega)
    (fun hp => by rw [hs] at hp; simp at hp) (fun hp => by rw [hs] at hp; simp at hp)
    (fun hp => by rw [hs] at hp; simp at hp) hsat hep
  rw [hs, List.getElem!_eq_getElem?_getD]; rfl

theorem new_refines {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.new K V = ok m') :
    Inv HashableInst m' ∧ sl_v m' = [] ∧ ∀ k, toFun m' k = none := by
  rw [ron.hashmap2.HashMap2.new] at h
  have hm := Result.ok_injective h
  refine unallocated_inv (HashableInst := HashableInst) ?_ ?_ ?_ ?_ ?_ <;> rw [← hm] <;> rfl

/-- `ensure_slots` gives an unallocated table its slots and leaves an
allocated one alone; either way the abstract map, the entry count, the epoch
and the `saturated` flag are untouched, and the result *is* allocated — which
is the hypothesis `try_resize_spec` needs.  **The epoch is not reset**: a
table cleared before its first insert must not make its stale nothing live
again. -/
theorem ensure_slots_spec (hinv : Inv HashableInst m) {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.ensure_slots m = ok m') :
    Inv HashableInst m' ∧ 0 < m'.slots.val.length ∧ sl_v m' = sl_v m ∧
      m'.num_entries = m.num_entries ∧ m'.saturated = m.saturated ∧
      m'.epoch = m.epoch ∧
      (m'.slots.val.length = 32 ∨ m'.slots.val.length = m.slots.val.length) := by
  rw [ron.hashmap2.HashMap2.ensure_slots] at h
  split at h
  · rename_i h0
    have hs : m.slots.val = [] := vec_len_eq_zero_iff.mp h0
    have hav : sl_v m = [] := sl_v_of_slots_nil hs
    have hn : m.num_entries.val = 0 := by rw [hinv.entries, hav]; simp
    obtain ⟨t, ht, hok⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hts, htn, html, -, -, -⟩ := new_with_capacity_pow2_spec ht
    have hm := Result.ok_injective hok
    have hslots : m'.slots = t.slots := by rw [← hm]
    have hent : m'.num_entries = m.num_entries := by rw [← hm]
    have hsat : m'.saturated = m.saturated := by rw [← hm]
    have hep : m'.epoch = m.epoch := by rw [← hm]
    have hmlv : m'.max_load = t.max_load := by rw [← hm]
    have hcap : (ron.hashmap2.MIN_CAPACITY : Std.Usize).val = 32 := by
      rw [ron.hashmap2.MIN_CAPACITY]; rfl
    have hlen : m'.slots.val.length = 32 := by rw [hslots, hts, List.length_replicate, hcap]
    have hsl : sl_v m' = [] := by rw [sl_v, hslots, hts]; simp
    obtain ⟨hinv', -, -⟩ := vacant_table_inv (HashableInst := HashableInst)
      (fun j => by rw [hslots, hts]; exact getElem!_replicate_vacant _ _) hsl
      (by rw [hent, hn]) (by omega)
      (fun _ => ⟨5, by rw [hlen]; norm_num⟩) (fun _ => by omega)
      (fun _ => by rw [hmlv, html, hcap, hlen]) (by rw [hsat]; exact hinv.sat)
      (by rw [hep]; exact hinv.epoch_pos)
    exact ⟨hinv', by omega, by rw [hsl, hav], hent, hsat, hep, Or.inl hlen⟩
  · rename_i h0
    have hm := Result.ok_injective h
    subst hm
    have hpos : 0 < m.slots.val.length := by
      rcases Nat.eq_zero_or_pos m.slots.val.length with hz | hp
      · exact absurd (vec_len_eq_zero_iff.mpr (List.eq_nil_of_length_eq_zero hz)) h0
      · exact hp
    exact ⟨hinv, hpos, rfl, rfl, rfl, rfl, Or.inr rfl⟩

omit [DecidableEq K] in
/-- Verbatim from `HashMap.lean`: `pow2_at_least` is the same function under
a different module path. -/
theorem pow2_at_least_spec (F : Nat) :
    ∀ (n cap fuel c : Std.Usize), fuel.val = F → (∃ e, cap.val = 2 ^ e) → 32 ≤ cap.val →
      ron.hashmap2.pow2_at_least n cap fuel = ok c → (∃ e, c.val = 2 ^ e) ∧ 32 ≤ c.val := by
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro n cap fuel c hF h2 h32 h
    rw [ron.hashmap2.pow2_at_least.eq_def] at h
    split at h
    · rw [← Result.ok_injective h]; exact ⟨h2, h32⟩
    · split at h
      · rw [← Result.ok_injective h]; exact ⟨h2, h32⟩
      · rename_i hfuel _
        simp only [bind_eq_ok_iff] at h
        obtain ⟨lim, -, h⟩ := h
        split at h
        · rw [← Result.ok_injective h]; exact ⟨h2, h32⟩
        · simp only [bind_eq_ok_iff] at h
          obtain ⟨cap2, hcap2, fuel1, hfuel1, h⟩ := h
          obtain ⟨e, he⟩ := h2
          refine ih fuel1.val ?_ n cap2 fuel1 c rfl ⟨e + 1, ?_⟩ ?_ h
          · rw [uscalar_sub_eq hfuel1, show (1#usize : Std.Usize).val = 1 by scalar_tac]
            have : fuel.val ≠ 0 := by scalar_tac
            omega
          · rw [uscalar_mul_eq hcap2, he, show (2#usize : Std.Usize).val = 2 by scalar_tac]
            ring
          · rw [uscalar_mul_eq hcap2, show (2#usize : Std.Usize).val = 2 by scalar_tac]
            omega

theorem with_capacity_refines {c : Std.Usize} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.with_capacity K V c = ok m') :
    Inv HashableInst m' ∧ sl_v m' = [] ∧ ∀ k, toFun m' k = none := by
  rw [ron.hashmap2.HashMap2.with_capacity] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨cap, hcap, h⟩ := h
  have hmin : (ron.hashmap2.MIN_CAPACITY : Std.Usize).val = 32 := by
    rw [ron.hashmap2.MIN_CAPACITY]; rfl
  obtain ⟨h2, h32⟩ := pow2_at_least_spec ron.hashmap2.POW2_FUEL.val c
    ron.hashmap2.MIN_CAPACITY ron.hashmap2.POW2_FUEL cap rfl ⟨5, by rw [hmin]; norm_num⟩
    (by omega) hcap
  obtain ⟨hinv, h1, h2', -⟩ := empty_table_inv h2 h32 h
  exact ⟨hinv, h1, h2'⟩


/-! ## `clear` and `clear_fit`

**This is the section task #97-P6-4b said would shrink, and it does.**
`clear` is two field writes: the epoch goes up by one and, by `Inv.stamps`,
*no slot carries the new stamp* — so the table is empty without a single slot
being touched.  The `EPOCH_MAX` wrap arm reuses the vacate walk, which is
`allocate_slots_spec`'s induction again.

`clear_fit` (task #97-P6-7's decaying high-water mark) adds nothing to the
specification at all: its three arms are `clear` twice and a fresh table, and
`fit_hw` is not a field `Inv` or `toFun` mentions — a capacity choice is
invisible to the abstract map (DESIGN.md §3.2), which is exactly what
`Inv_fit_hw` below says. -/

omit [DecidableEq K] in
theorem vacate_slots_spec (N : Nat) :
    ∀ (slots slots' : alloc.vec.Vec (ron.hashmap2.Slot K V)) (lo hi : Std.Usize),
      hi.val - lo.val = N →
      ron.hashmap2.HashMap2.vacate_slots slots lo hi = ok slots' →
      slots'.val.length = slots.val.length ∧
      (∀ j, lo.val ≤ j → j < hi.val → slots'.val[j]! = ron.hashmap2.Slot.Vacant) ∧
      (∀ j, (j < lo.val ∨ hi.val ≤ j) → slots'.val[j]! = slots.val[j]!) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro slots slots' lo hi hN h
    rw [ron.hashmap2.HashMap2.vacate_slots.eq_def] at h
    split at h
    · rename_i hgt
      have hlt : lo.val < hi.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨n, hn, h⟩ := h
      have hnv : n.val = hi.val - lo.val := uscalar_sub_eq hn
      split at h
      · rename_i h1
        have hn1 : hi.val = lo.val + 1 := by
          have : n.val = 1 := by scalar_tac
          omega
        simp only [bind_eq_ok_iff] at h
        obtain ⟨p, hp, hb⟩ := h
        obtain ⟨x, f⟩ := p
        obtain ⟨hlo, -, rfl⟩ := vec_index_mut_eq hp
        rw [← Result.ok_injective hb, alloc.vec.Vec.set_val_eq]
        refine ⟨by simp, ?_, ?_⟩
        · intro j hj1 hj2
          have : j = lo.val := by omega
          subst this
          exact getElem!_set_self _ hlo
        · intro j hj
          exact getElem!_set_ne _ (by omega)
      · rename_i h1
        have hn2 : 2 ≤ n.val := by
          have : n.val ≠ 1 := by scalar_tac
          omega
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i, hi2, mid, hmid, slots1, hs1, h2⟩ := h
        have hiv : i.val = n.val / 2 := by
          rw [uscalar_div_eq hi2, show (2#usize : Std.Usize).val = 2 by scalar_tac]
        have hmv : mid.val = lo.val + i.val := uscalar_add_eq hmid
        obtain ⟨l1, c1, f1⟩ := ih (mid.val - lo.val) (by omega) slots slots1 lo mid rfl hs1
        obtain ⟨l2, c2, f2⟩ := ih (hi.val - mid.val) (by omega) slots1 slots' mid hi rfl h2
        refine ⟨by omega, ?_, ?_⟩
        · intro j hj1 hj2
          by_cases hjm : j < mid.val
          · rw [f2 j (Or.inl hjm)]; exact c1 j hj1 hjm
          · exact c2 j (by omega) hj2
        · intro j hj
          rw [f2 j (by omega), f1 j (by omega)]
    · rename_i hgt
      have : hi.val ≤ lo.val := by scalar_tac
      rw [← Result.ok_injective h]
      exact ⟨rfl, fun j hj1 hj2 => by omega, fun _ _ => rfl⟩

omit [DecidableEq K] in
/-- `fit_hw` is the capacity policy's one word of state and nothing else: it
is in no clause of `Inv` and in no equation of `toFun`. -/
theorem Inv_fit_hw {m' : ron.hashmap2.HashMap2 K V} (h : Inv HashableInst m')
    (w : Std.Usize) : Inv HashableInst { m' with fit_hw := w } :=
  ⟨⟨h.pow2, h.min_cap, h.max_load_eq, h.sat, h.epoch_pos, h.stamps, h.nodup,
    h.entries, h.run⟩, h.fit⟩

omit [DecidableEq K] in
@[local simp] theorem sl_v_fit_hw {m' : ron.hashmap2.HashMap2 K V} (w : Std.Usize) :
    sl_v { m' with fit_hw := w } = sl_v m' := rfl

/-- **`clear` empties the table.**  On the common path it writes two fields;
`Inv.stamps` — no slot's stamp exceeds the epoch — is what makes the new
epoch match nothing, and that clause exists for this proof alone. -/
theorem clear_refines (hinv : Inv HashableInst m) {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.clear m = ok m') :
    Inv HashableInst m' ∧ sl_v m' = [] ∧ ∀ k, toFun m' k = none := by
  rw [ron.hashmap2.HashMap2.clear] at h
  split at h
  · -- the `EPOCH_MAX` wrap: vacate the slots the hard way and restart at 1
    simp only [bind_eq_ok_iff] at h
    obtain ⟨v, hv, hm⟩ := h
    obtain ⟨hlen, hnil, -⟩ := vacate_slots_spec ((alloc.vec.Vec.len m.slots).val - 0)
      m.slots v 0#usize (alloc.vec.Vec.len m.slots) rfl hv
    have hslots : m'.slots = v := by rw [← Result.ok_injective hm]
    have hent : m'.num_entries.val = 0 := by rw [← Result.ok_injective hm]; rfl
    have hep : m'.epoch = 1#u32 := by rw [← Result.ok_injective hm]
    have hsat : m'.saturated = m.saturated := by rw [← Result.ok_injective hm]
    have hml : m'.max_load = m.max_load := by rw [← Result.ok_injective hm]
    have hlen' : m'.slots.val.length = m.slots.val.length := by rw [hslots]; exact hlen
    have hvac : ∀ j : Nat, m'.slots.val[j]! = ron.hashmap2.Slot.Vacant := by
      intro j
      by_cases hj : j < m'.slots.val.length
      · rw [hslots]
        exact hnil j (by scalar_tac)
          (by rw [alloc.vec.Vec.len_val]; rw [hlen'] at hj; exact hj)
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    exact vacant_table_inv hvac (sl_v_eq_nil_of_no_live (fun j => by rw [slotKV, hvac j]; rfl))
      hent (by omega) (by rw [hlen']; exact hinv.pow2) (by rw [hlen']; exact hinv.min_cap)
      (by rw [hlen', hml]; exact hinv.max_load_eq) (by rw [hsat]; exact hinv.sat)
      (by rw [hep]; rfl)
  · -- the common path: `epoch += 1`, and no slot carries the new stamp
    rename_i h0
    simp only [bind_eq_ok_iff] at h
    obtain ⟨i, hi, hm⟩ := h
    have hiv : i.val = m.epoch.val + 1 := by rw [uscalar_add_eq hi]; simp
    have hslots : m'.slots = m.slots := by rw [← Result.ok_injective hm]
    have hent : m'.num_entries.val = 0 := by rw [← Result.ok_injective hm]; rfl
    have hep : m'.epoch = i := by rw [← Result.ok_injective hm]
    have hsat : m'.saturated = m.saturated := by rw [← Result.ok_injective hm]
    have hml : m'.max_load = m.max_load := by rw [← Result.ok_injective hm]
    have hstamps : ∀ (j : Nat) (g : Std.U32) (k : K) (v : V),
        m'.slots.val[j]! = .Live g k v → g.val ≤ m'.epoch.val := by
      intro j g k v hx
      rw [hslots] at hx
      have := hinv.stamps j g k v hx
      rw [hep, hiv]; omega
    refine dead_table_inv ?_ hstamps hent (by omega) (by rw [hslots]; exact hinv.pow2)
      (by rw [hslots]; exact hinv.min_cap) (by rw [hslots, hml]; exact hinv.max_load_eq)
      (by rw [hsat]; exact hinv.sat) (by rw [hep, hiv]; omega)
    intro j
    rw [slotKV]
    cases hsc : m'.slots.val[j]! with
    | Vacant => rfl
    | Live g k v =>
      have hg : g.val ≤ m.epoch.val := hinv.stamps j g k v (by rw [← hslots]; exact hsc)
      have hne : ¬ (g = m'.epoch) := by
        rw [UScalar.eq_equiv, hep, hiv]; omega
      simp [hne]

/-- **`clear_fit` denotes the empty map too.**  Its three arms are `clear`,
`clear`, and a fresh table of `want` slots; which one runs is a capacity
decision, and a capacity is invisible to `toFun`. -/
theorem clear_fit_refines (hinv : Inv HashableInst m) {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.clear_fit m = ok m') :
    Inv HashableInst m' ∧ sl_v m' = [] ∧ ∀ k, toFun m' k = none := by
  rw [ron.hashmap2.HashMap2.clear_fit] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i, -, decayed, -, hw, -, i1, -, i2, -, want, hwant, h⟩ := h
  have hmin : (ron.hashmap2.MIN_CAPACITY : Std.Usize).val = 32 := by
    rw [ron.hashmap2.MIN_CAPACITY]; rfl
  obtain ⟨hw2, hw32⟩ := pow2_at_least_spec ron.hashmap2.POW2_FUEL.val i2
    ron.hashmap2.MIN_CAPACITY ron.hashmap2.POW2_FUEL want rfl ⟨5, by rw [hmin]; norm_num⟩
    (by omega) hwant
  have hremake : ∀ {t : ron.hashmap2.HashMap2 K V},
      ron.hashmap2.HashMap2.new_with_capacity_pow2 K V want = ok t →
      ok (α := ron.hashmap2.HashMap2 K V)
        { t with num_entries := 0#usize, epoch := 1#u32, saturated := false, fit_hw := hw }
        = ok m' →
      Inv HashableInst m' ∧ sl_v m' = [] ∧ ∀ k, toFun m' k = none := by
    intro t ht hok
    obtain ⟨hts, -, html, -, -, -⟩ := new_with_capacity_pow2_spec ht
    have hslots : m'.slots.val = List.replicate want.val ron.hashmap2.Slot.Vacant := by
      rw [← Result.ok_injective hok]; exact hts
    have hlen : m'.slots.val.length = want.val := by rw [hslots]; simp
    have hmlv : m'.max_load = t.max_load := by rw [← Result.ok_injective hok]
    refine vacant_table_inv (fun j => by rw [hslots]; exact getElem!_replicate_vacant _ _)
      (by rw [sl_v, hslots]; simp) (by rw [← Result.ok_injective hok]; rfl) (by omega)
      (fun _ => by rw [hlen]; exact hw2) (fun _ => by rw [hlen]; exact hw32)
      (fun _ => by rw [hmlv, html, hlen]) (by rw [← Result.ok_injective hok])
      (by rw [← Result.ok_injective hok]; rfl)
  split at h
  · exact clear_refines (Inv_fit_hw hinv hw) h
  · split at h
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨i3, -, h⟩ := h
      split at h
      · exact clear_refines (Inv_fit_hw hinv hw) h
      · simp only [bind_eq_ok_iff] at h
        obtain ⟨t, ht, hok⟩ := h
        exact hremake ht hok
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨t, ht, hok⟩ := h
      exact hremake ht hok


/-! ## `dup`, the pin loop's pre-attempt snapshot

`HashMap.lean`'s argument transfers unchanged and is shorter: there is no
chain to rebuild, so `dup_slot` replaces `dup_alist` and the nested induction
goes with it.  **In the model the copy is the identity** — every `Dup` the
port instantiates copies by a pointer bump or by rebuilding a `Vec` element by
element, and each is already proved to return its argument — so `dup_spec`
proves `m' = m` and every consequence (`Inv`, `toFun`, `sl_v`, `KeysOk`) is a
rewrite.  Stale slots are copied too: they are not part of the abstract map,
and reproducing the table exactly is what makes the copy behave identically. -/

section Dup

variable {DupK : ron.hashmap.Dup K} {DupV : ron.hashmap.Dup V}

omit [DecidableEq K] in
theorem dup_slot_id (hK : DupId DupK) (hV : DupId DupV)
    {s s' : ron.hashmap2.Slot K V}
    (h : ron.hashmap2.dup_slot DupK DupV s = ok s') : s' = s := by
  rw [ron.hashmap2.dup_slot.eq_def] at h
  cases hsc : s with
  | Vacant => rw [hsc] at h; exact (Result.ok_injective h).symm
  | Live g k v =>
    rw [hsc] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨a, ha, b, hb, hs⟩ := h
    rw [hK _ _ ha, hV _ _ hb] at hs
    exact (Result.ok_injective hs).symm

omit [DecidableEq K] in
/-- `dup`'s slot walk, halving exactly as `allocate_slots` does. -/
theorem dup_slots_spec (hK : DupId DupK) (hV : DupId DupV) (N : Nat) :
    ∀ (src out out' : alloc.vec.Vec (ron.hashmap2.Slot K V)) (lo hi : Std.Usize),
      hi.val - lo.val = N → hi.val ≤ src.val.length →
      ron.hashmap2.HashMap2.dup_slots DupK DupV src out lo hi = ok out' →
      out'.val = out.val ++ (src.val.drop lo.val).take (hi.val - lo.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro src out out' lo hi hN hhi h
    rw [ron.hashmap2.HashMap2.dup_slots.eq_def] at h
    split at h
    · rename_i hgt
      have hlt : lo.val < hi.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨n, hn, h⟩ := h
      have hnv : n.val = hi.val - lo.val := uscalar_sub_eq hn
      split at h
      · rename_i h1
        have hn1 : hi.val = lo.val + 1 := by
          have : n.val = 1 := by scalar_tac
          omega
        simp only [bind_eq_ok_iff] at h
        obtain ⟨a, ha, a1, ha1, hp⟩ := h
        obtain ⟨hlo, rfl⟩ := vec_index_eq ha
        rw [vec_push_eq hp, dup_slot_id hK hV ha1, hn1,
          show lo.val + 1 - lo.val = 1 by omega, take_one_drop hlo]
      · rename_i h1
        have hn2 : 2 ≤ n.val := by
          have : n.val ≠ 1 := by scalar_tac
          omega
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i, hi2, mid, hmid, out1, hs1, h2⟩ := h
        have hiv : i.val = n.val / 2 := by
          rw [uscalar_div_eq hi2, show (2#usize : Std.Usize).val = 2 by scalar_tac]
        have hmv : mid.val = lo.val + i.val := uscalar_add_eq hmid
        have e1 := ih (mid.val - lo.val) (by omega) src out out1 lo mid rfl (by omega) hs1
        have e2 := ih (hi.val - mid.val) (by omega) src out1 out' mid hi rfl hhi h2
        rw [e2, e1, List.append_assoc,
          show hi.val - lo.val = (mid.val - lo.val) + (hi.val - mid.val) by omega,
          List.take_add, List.drop_drop,
          show lo.val + (mid.val - lo.val) = mid.val by omega]
    · rename_i hgt
      have hle : hi.val ≤ lo.val := by scalar_tac
      rw [← Result.ok_injective h, show hi.val - lo.val = 0 by omega]
      simp

omit [DecidableEq K] in
/-- **The snapshot is the table.** -/
theorem dup_spec (hK : DupId DupK) (hV : DupId DupV) {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.dup DupK DupV m = ok m') : m' = m := by
  rw [ron.hashmap2.HashMap2.dup] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨slots, hs, hm⟩ := h
  have hv : slots.val = m.slots.val := by
    have := dup_slots_spec hK hV
      ((alloc.vec.Vec.len m.slots).val - (0#usize : Std.Usize).val) m.slots
      (alloc.vec.Vec.with_capacity (ron.hashmap2.Slot K V)
        (alloc.vec.Vec.len m.slots)) slots 0#usize (alloc.vec.Vec.len m.slots)
      rfl (by simp) hs
    simpa [alloc.vec.Vec.with_capacity] using this
  rw [← Result.ok_injective hm, alloc.vec.Vec.ext _ _ hv]

theorem dup_toFun (hK : DupId DupK) (hV : DupId DupV) {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.dup DupK DupV m = ok m') (k : K) :
    toFun m' k = toFun m k := by rw [dup_spec hK hV h]

omit [DecidableEq K] in
theorem dup_sl_v (hK : DupId DupK) (hV : DupId DupV) {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.dup DupK DupV m = ok m') : sl_v m' = sl_v m := by
  rw [dup_spec hK hV h]

omit [DecidableEq K] in
theorem dup_inv (hK : DupId DupK) (hV : DupId DupV) {m' : ron.hashmap2.HashMap2 K V}
    (hinv : Inv HashableInst m) (h : ron.hashmap2.HashMap2.dup DupK DupV m = ok m') :
    Inv HashableInst m' := by rw [dup_spec hK hV h]; exact hinv

end Dup


/-! ## `insert`

`insert_no_resize` is `HashMap.lean`'s lemma of the same name with
`probe_spec` where `list_insert_spec` stood: **one probe decides both arms**,
and the slot it returns is either the key's own or the first free slot of its
run, so writing `Live(epoch, k, v)` there is correct either way.

It is the one operation that breaks the load clause — it adds an entry without
checking — so it concludes `Inv0` and the entry count, and `insert` puts `fit`
back from the resize. -/

/-- The entry written by `insert_no_resize`. -/
theorem insert_no_resize_spec {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv HashableInst m) (hkeys : KeysOk P m) {key : K} {value : V} (hk : P key)
    (hpos : 0 < m.slots.val.length) {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.insert_no_resize HashableInst Eq2Inst m key value
          = ok (old, m')) :
    Inv0 HashableInst m' ∧ old = toFun m key ∧
    (∀ k', toFun m' k' = if k' = key then some value else toFun m k') ∧
    m'.slots.val.length = m.slots.val.length ∧
    m'.max_load = m.max_load ∧ m'.saturated = m.saturated ∧ m'.epoch = m.epoch ∧
    m'.num_entries.val = m.num_entries.val + (if old.isSome then 0 else 1) ∧
    (sl_v m').length = (sl_v m).length + (if old.isSome then 0 else 1) ∧
    (old = none → (sl_v m').Perm ((key, value) :: sl_v m)) ∧ KeysOk P m' := by
  rw [ron.hashmap2.HashMap2.insert_no_resize] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨hw, hhash, i1, hbi, q, hprobe, h⟩ := h
  obtain ⟨i2, b⟩ := q
  replace h := bind_eq_ok_iff.mp h
  obtain ⟨p, hmut, h⟩ := h
  obtain ⟨s, back⟩ := p
  obtain ⟨hlt, hseq, hback⟩ := vec_index_mut_eq hmut
  have hhome : homeAt HashableInst (alloc.vec.Vec.len m.slots) key = ok i1 := by
    simp only [homeAt, bind_eq_ok_iff]; exact ⟨hw, hhash, hbi⟩
  obtain ⟨hatlt, hilt, htrue, hfalse⟩ := probe_spec heq hinv hkeys hk hpos hhome hprobe
  subst hback
  set X : ron.hashmap2.Slot K V := .Live m.epoch key value with hX
  have hXlive : liveAt m.epoch X = some (key, value) := by rw [hX]; simp
  -- the shape of the result, in both arms
  have key0 : m'.slots.val = m.slots.val.set i2.val X ∧ m'.max_load = m.max_load ∧
      m'.saturated = m.saturated ∧ m'.epoch = m.epoch ∧ m'.num_entries.val =
        m.num_entries.val + (if old.isSome then 0 else 1) ∧
      old = (slotKV m i2.val).map Prod.snd := by
    by_cases hb : b = true
    · subst hb
      obtain ⟨w, hslot, htf⟩ := htrue rfl
      rw [slotKV, ← hseq] at hslot
      cases hsc : s with
      | Vacant => rw [hsc] at hslot; simp at hslot
      | Live g k' v =>
        rw [hsc] at h hslot
        obtain ⟨hge, hkv⟩ := liveAt_epoch hslot
        have e := Result.ok_injective h
        have eold : old = some v := (congrArg Prod.fst e).symm
        have es : m' = { m with slots := alloc.vec.Vec.set m.slots i2 X } :=
          (congrArg Prod.snd e).symm
        refine ⟨by rw [es]; exact alloc.vec.Vec.set_val_eq _ _ _, by rw [es], by rw [es],
          by rw [es], by rw [es, eold]; simp, ?_⟩
        rw [eold, slotKV, ← hseq, hsc]
        simp [hge]
    · have hbf : b = false := by simpa using hb
      subst hbf
      obtain ⟨hnone, -, -⟩ := hfalse rfl
      replace h := bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, hok⟩ := h
      have e := Result.ok_injective hok
      have eold : old = none := (congrArg Prod.fst e).symm
      have es : m' =
          { m with num_entries := i3, slots := alloc.vec.Vec.set m.slots i2 X } :=
        (congrArg Prod.snd e).symm
      refine ⟨by rw [es]; exact alloc.vec.Vec.set_val_eq _ _ _, by rw [es], by rw [es],
        by rw [es], ?_, by rw [eold, hnone]; rfl⟩
      rw [es, eold]
      simpa using uscalar_add_eq hi3
  obtain ⟨hsv, hml, hsat, hep, hent, hold⟩ := key0
  have hlen : m'.slots.val.length = m.slots.val.length := by rw [hsv, List.length_set]
  have hlenv : alloc.vec.Vec.len m'.slots = alloc.vec.Vec.len m.slots := vec_len_congr hlen
  set R := rest m i2.val with hR
  have PM : (sl_v m).Perm ((slotKV m i2.val).toList ++ R) := sl_v_perm_rest hlt
  have PM' : (sl_v m').Perm ((key, value) :: R) := by
    have := sl_v_set (m := m) (m' := m') hep hsv hlt
    rwa [hXlive] at this
  have ND := hinv.nodup
  rw [(PM.map Prod.fst).nodup_iff, List.map_append, List.nodup_append] at ND
  obtain ⟨NDa, NDr, NDd⟩ := ND
  -- a live slot at `i2` can only be the key's own: that is what `found` means
  have hpk : ∀ pw : K × V, slotKV m i2.val = some pw → pw.1 = key := by
    intro pw hs2
    have hbt : b = true := by
      by_contra hb
      obtain ⟨hnone, -, -⟩ := hfalse (by simpa using hb)
      rw [hs2] at hnone; simp at hnone
    obtain ⟨w, hslot, -⟩ := htrue hbt
    rw [hs2] at hslot
    exact congrArg Prod.fst (Option.some.inj hslot)
  -- the key is nowhere else
  have hkR : key ∉ R.map Prod.fst := by
    cases hs2 : slotKV m i2.val with
    | none =>
      have hbf : b = false := by
        by_contra hc
        obtain ⟨w, hslot, -⟩ := htrue (by simpa using hc)
        rw [hs2] at hslot; simp at hslot
      obtain ⟨-, htf, -⟩ := hfalse hbf
      intro hmem
      obtain ⟨⟨k0, w⟩, hp, hfst⟩ := List.mem_map.1 hmem
      simp only at hfst
      subst hfst
      rw [toFun, lookupK_eq_none_iff] at htf
      exact htf (List.mem_map.2 ⟨(k0, w), rest_subset hp, rfl⟩)
    | some pw =>
      rw [hs2] at NDd
      intro hmem
      exact NDd pw.1 (by simp) key hmem (hpk pw hs2)
  have hRk : lookupK R key = none := lookupK_eq_none_of_not_mem hkR
  have NDnew : ((sl_v m').map Prod.fst).Nodup := by
    rw [(PM'.map Prod.fst).nodup_iff, List.map_cons, List.nodup_cons]
    exact ⟨hkR, NDr⟩
  have hOld : old = toFun m key := by
    rw [hold, toFun, lookupK_perm PM hinv.nodup, lookupK_append, hRk]
    cases hs2 : slotKV m i2.val with
    | none => simp
    | some pw =>
      have hpw := hpk pw hs2
      obtain ⟨k0, v0⟩ := pw
      simp only at hpw
      subst hpw
      simp
  have hToFun : ∀ k', toFun m' k' = if k' = key then some value else toFun m k' := by
    intro k'
    rw [toFun, toFun, lookupK_perm PM' NDnew, lookupK_perm PM hinv.nodup, lookupK_append,
      lookupK_cons]
    by_cases hk' : k' = key
    · subst hk'; simp
    · rw [if_neg (Ne.symm hk'), if_neg hk']
      cases hs2 : slotKV m i2.val with
      | none => simp
      | some pw =>
        have hpw := hpk pw hs2
        obtain ⟨k0, v0⟩ := pw
        simp only at hpw
        subst hpw
        simp [Ne.symm hk']
  -- `isLive` only grows
  have hgrow : ∀ t : Nat, isLive m t → isLive m' t := by
    intro t ht
    by_cases htz : t = i2.val
    · subst htz
      rw [isLive, slotKV_set_self hep hsv hlt, hXlive]; simp
    · rwa [isLive, slotKV_set_ne hep hsv htz]
  -- the entry count, one place
  have hcnt : (slotKV m i2.val).toList.length + (if old.isSome then 0 else 1) = 1 := by
    cases hs2 : slotKV m i2.val with
    | none => rw [show old = none by rw [hold, hs2]; rfl]; simp
    | some pw => rw [show old = some pw.2 by rw [hold, hs2]; rfl]; simp
  have hlen1 : (sl_v m').length = R.length + 1 := by rw [PM'.length_eq]; simp
  have hlen2 : (sl_v m).length = (slotKV m i2.val).toList.length + R.length := by
    rw [PM.length_eq]; simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, NDnew, ?_, ?_⟩, hOld, hToFun, hlen, hml, hsat, hep,
    hent, ?_, ?_, ?_⟩
  · rw [hlen]; exact hinv.pow2
  · rw [hlen]; exact hinv.min_cap
  · rw [hlen, hml]; exact hinv.max_load_eq
  · rw [hsat]; exact hinv.sat
  · rw [hep]; exact hinv.epoch_pos
  · intro j g k0 v0 hx
    rw [hep]
    by_cases hj : j = i2.val
    · subst hj
      rw [hsv, getElem!_set_self _ hlt, hX] at hx
      injection hx with h1 h2 h3
      rw [← h1]
    · rw [hsv, getElem!_set_ne _ hj] at hx
      exact hinv.stamps j g k0 v0 hx
  · -- `entries`
    rw [hent, hinv.entries, hlen1, hlen2]; omega
  · -- `run`
    intro j k0 v0 i hj hs2 hhome2
    rw [hlenv] at hhome2
    rw [hlen] at hj
    by_cases hjz : j = i2.val
    · subst hjz
      rw [slotKV_set_self hep hsv hlt, hXlive] at hs2
      have hkk : k0 = key := (congrArg Prod.fst (Option.some.inj hs2)).symm
      subst hkk
      have hii : i = i1 := Result.ok_injective (hhome2.symm.trans hhome)
      subst hii
      by_cases hb : b = true
      · obtain ⟨w, hslot, -⟩ := htrue hb
        obtain ⟨-, D, hD, hjD, hrun⟩ := hinv.run i2.val k0 w i hlt hslot hhome2
        exact ⟨by rw [hlen]; exact hilt, D, by rw [hlen]; exact hD,
          by rw [hlen]; exact hjD, fun d hd => hgrow _ (by rw [hlen] at *; exact hrun d hd)⟩
      · obtain ⟨-, -, D, hD, hjD, hrun⟩ := hfalse (by simpa using hb)
        exact ⟨by rw [hlen]; exact hilt, D, by rw [hlen]; exact hD,
          by rw [hlen]; exact hjD, fun d hd => hgrow _ (by rw [hlen] at *; exact hrun d hd)⟩
    · rw [slotKV_set_ne hep hsv hjz] at hs2
      obtain ⟨hib, D, hD, hjD, hrun⟩ := hinv.run j k0 v0 i hj hs2 hhome2
      exact ⟨by rw [hlen]; exact hib, D, by rw [hlen]; exact hD, by rw [hlen]; exact hjD,
        fun d hd => hgrow _ (by rw [hlen] at *; exact hrun d hd)⟩
  · -- the length of `sl_v`
    rw [hlen1, hlen2]; omega
  · -- the permutation, on a fresh key
    intro hnone
    refine PM'.trans ?_
    have hs2 : slotKV m i2.val = none := by
      cases hs3 : slotKV m i2.val with
      | none => rfl
      | some pw => rw [hold, hs3] at hnone; simp at hnone
    refine List.Perm.cons _ ?_
    rw [hs2] at PM
    simpa using PM.symm
  · -- `KeysOk`
    intro p hp
    rcases List.mem_cons.1 (PM'.mem_iff.1 hp) with hc | hc
    · rw [hc]; exact hk
    · exact hkeys p (rest_subset hc)


/-! ## Growth: `move_slots`, `try_resize`

`HashMap.lean`'s `move_elements` walk over a range of buckets becomes the same
walk over a range of *slots*; `slotsLive` is `slotsFlat` with `filterMap` for
`map alv |>.flatten`, and the five lemmas below are its five, line for line.
The one addition is the **room** hypothesis: the new table has to keep
`num_entries ≤ max_load` through the whole move, because `insert_no_resize`
probes and a probe needs a free slot.  `try_resize` supplies it from
`n ≤ 3·⌊2n/4⌋`. -/

/-- The live entries of the slots `[lo, lo + n)`, at stamp `e`. -/
def slotsLive (s : List (ron.hashmap2.Slot K V)) (e : Std.U32) (lo n : Nat) :
    List (K × V) := ((s.drop lo).take n).filterMap (liveAt e)

section SlotsLive

variable {s s' : List (ron.hashmap2.Slot K V)} {e : Std.U32} {lo n : Nat}

omit [DecidableEq K] in
@[local simp] theorem slotsLive_zero : slotsLive s e lo 0 = [] := by simp [slotsLive]

omit [DecidableEq K] in
theorem slotsLive_all : slotsLive s e 0 s.length = s.filterMap (liveAt e) := by
  simp [slotsLive]

omit [DecidableEq K] in
theorem slotsLive_add (n₁ n₂ : Nat) :
    slotsLive s e lo (n₁ + n₂) = slotsLive s e lo n₁ ++ slotsLive s e (lo + n₁) n₂ := by
  simp [slotsLive, List.take_add, List.drop_drop, List.filterMap_append]

omit [DecidableEq K] in
theorem slotsLive_one (h : lo < s.length) :
    slotsLive s e lo 1 = (liveAt e s[lo]!).toList := by
  rw [slotsLive, take_one_drop h]
  simp [filterMap_cons_eq]

omit [DecidableEq K] in
theorem slotsLive_congr (hlen : s'.length = s.length)
    (h : ∀ j, lo ≤ j → j < lo + n → s'[j]! = s[j]!) :
    slotsLive s' e lo n = slotsLive s e lo n := by
  have hw : (s'.drop lo).take n = (s.drop lo).take n := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_take, List.getElem_drop]
      have hi1 : lo + i < s'.length := by
        simp only [List.length_take, List.length_drop] at h1; omega
      have hi2 : lo + i < s.length := by omega
      have hin : i < n := by simp only [List.length_take, List.length_drop] at h1; omega
      rw [← List.getElem!_of_getElem? (List.getElem?_eq_getElem hi1),
          ← List.getElem!_of_getElem? (List.getElem?_eq_getElem hi2)]
      exact h (lo + i) (by omega) (by omega)
  rw [slotsLive, slotsLive, hw]

end SlotsLive

/-- **The rehash walk.**  Every live entry of `[lo, hi)` moves into `ntable`
and the slot it came from is vacated; stale entries are dropped on the floor,
which is the one place the epoch scheme ever frees what a cleared entry
held. -/
theorem move_slots_spec {P : K → Prop} (heq : Eq2Fwd Eq2Inst P) (N : Nat) :
    ∀ (nt nt' : ron.hashmap2.HashMap2 K V)
      (slots slots' : alloc.vec.Vec (ron.hashmap2.Slot K V)) (lo hi : Std.Usize)
      (epoch : Std.U32),
      hi.val - lo.val = N → hi.val ≤ slots.val.length → nt.epoch = epoch →
      Inv0 HashableInst nt → KeysOk P nt → 0 < nt.slots.val.length →
      nt.num_entries.val + (hi.val - lo.val) ≤ nt.max_load.val →
      (∀ x ∈ slotsLive slots.val epoch lo.val (hi.val - lo.val), P x.1) →
      ((slotsLive slots.val epoch lo.val (hi.val - lo.val)).map Prod.fst).Nodup →
      (∀ x ∈ slotsLive slots.val epoch lo.val (hi.val - lo.val),
          x.1 ∉ (sl_v nt).map Prod.fst) →
      ron.hashmap2.HashMap2.move_slots HashableInst Eq2Inst nt slots lo hi epoch
        = ok (nt', slots') →
      Inv0 HashableInst nt' ∧ KeysOk P nt' ∧
      (sl_v nt').Perm (slotsLive slots.val epoch lo.val (hi.val - lo.val) ++ sl_v nt) ∧
      nt'.slots.val.length = nt.slots.val.length ∧
      nt'.max_load = nt.max_load ∧ nt'.saturated = nt.saturated ∧ nt'.epoch = nt.epoch ∧
      nt'.num_entries.val ≤ nt.num_entries.val + (hi.val - lo.val) ∧
      slots'.val.length = slots.val.length ∧
      (∀ j, (j < lo.val ∨ hi.val ≤ j) → slots'.val[j]! = slots.val[j]!) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro nt nt' slots slots' lo hi epoch hN hbound hne hinv hkeys hpos hroom hP hnd hdisj h
    rw [ron.hashmap2.HashMap2.move_slots.eq_def] at h
    split at h
    · rename_i hgt
      have hlolt : lo.val < hi.val := by scalar_tac
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      have hnv : n.val = hi.val - lo.val := uscalar_sub_eq hn
      split at h
      · -- one slot
        rename_i h1
        have hhi1 : hi.val = lo.val + 1 := by
          have : n.val = 1 := by scalar_tac
          omega
        obtain ⟨p, hidx, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨sl, back⟩ := p
        obtain ⟨hlt, hseq, hback⟩ := vec_index_mut_eq hidx
        subst hback
        have hflat : slotsLive slots.val epoch lo.val (hi.val - lo.val)
            = (liveAt epoch slots.val[lo.val]!).toList := by
          rw [show hi.val - lo.val = 1 by omega, slotsLive_one hlt]
        have hfin : ∀ (nt1 : ron.hashmap2.HashMap2 K V),
            slots' = alloc.vec.Vec.set slots lo ron.hashmap2.Slot.Vacant →
            slots'.val.length = slots.val.length ∧
              (∀ j, (j < lo.val ∨ hi.val ≤ j) → slots'.val[j]! = slots.val[j]!) := by
          intro _ hs
          refine ⟨by rw [hs, alloc.vec.Vec.set_val_eq, List.length_set], ?_⟩
          intro j hj
          rw [hs, alloc.vec.Vec.set_val_eq]
          exact getElem!_set_ne _ (by omega)
        -- read the one slot
        cases hsc : sl with
        | Vacant =>
          rw [hsc] at h hseq
          have e := Result.ok_injective h
          have ent : nt' = nt := (congrArg Prod.fst e).symm
          have esl : slots' = alloc.vec.Vec.set slots lo ron.hashmap2.Slot.Vacant :=
            (congrArg Prod.snd e).symm
          obtain ⟨hl1, hl2⟩ := hfin nt esl
          rw [hflat, ← hseq]
          subst ent
          exact ⟨hinv, hkeys, by simp, rfl, rfl, rfl, rfl, by omega, hl1, hl2⟩
        | Live g k v =>
          rw [hsc] at h hseq
          rcases ite_eq_ok h with ⟨hg, h⟩ | ⟨hg, h⟩
          · -- a live entry: move it
            have hlive : liveAt epoch slots.val[lo.val]! = some (k, v) := by
              rw [← hseq]; simp [hg]
            rw [hflat, hlive] at hP hnd hdisj ⊢
            obtain ⟨q, hins, hok⟩ := bind_eq_ok_iff.mp h
            obtain ⟨o, nt1⟩ := q
            have hinvF : Inv HashableInst nt := ⟨hinv, by omega⟩
            obtain ⟨hinv1, hold, htf, hlen1, hml1, hsat1, hep1, hent1, -, hperm1, hkeys1⟩ :=
              insert_no_resize_spec heq hinvF hkeys (hP (k, v) (by simp)) hpos hins
            have hknt : k ∉ (sl_v nt).map Prod.fst := hdisj (k, v) (by simp)
            have honone : o = none := by
              rw [hold, toFun]; exact lookupK_eq_none_of_not_mem hknt
            have P1 : (sl_v nt1).Perm ((k, v) :: sl_v nt) := hperm1 honone
            have e := Result.ok_injective hok
            have ent : nt' = nt1 := (congrArg Prod.fst e).symm
            have esl : slots' = alloc.vec.Vec.set slots lo ron.hashmap2.Slot.Vacant :=
              (congrArg Prod.snd e).symm
            obtain ⟨hl1, hl2⟩ := hfin nt1 esl
            subst ent
            refine ⟨hinv1, hkeys1, by simpa using P1, hlen1, hml1, hsat1, ?_, ?_, hl1, hl2⟩
            · rw [hep1, hne]
            · rw [hent1, honone]; simp; omega
          · -- a stale entry: dropped
            have hlive : liveAt epoch slots.val[lo.val]! = none := by
              rw [← hseq]; simp [hg]
            have e := Result.ok_injective h
            have ent : nt' = nt := (congrArg Prod.fst e).symm
            have esl : slots' = alloc.vec.Vec.set slots lo ron.hashmap2.Slot.Vacant :=
              (congrArg Prod.snd e).symm
            obtain ⟨hl1, hl2⟩ := hfin nt esl
            rw [hflat, hlive]
            subst ent
            exact ⟨hinv, hkeys, by simp, rfl, rfl, rfl, rfl, by omega, hl1, hl2⟩
      · -- two halves
        rename_i h1
        have hn2 : 2 ≤ n.val := by
          have : n.val ≠ 1 := by scalar_tac
          omega
        obtain ⟨i, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨mid, hmid, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨q, hrec1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨nt1, slots1⟩ := q
        have hiv : i.val = n.val / 2 := by
          rw [uscalar_div_eq hi2, show (2#usize : Std.Usize).val = 2 by scalar_tac]
        have hmv2 : mid.val = lo.val + i.val := uscalar_add_eq hmid
        have hmid1 : lo.val < mid.val := by omega
        have hmid2 : mid.val < hi.val := by omega
        have h2 : ron.hashmap2.HashMap2.move_slots HashableInst Eq2Inst nt1 slots1 mid hi
            epoch = ok (nt', slots') := h
        have hsplit : slotsLive slots.val epoch lo.val (hi.val - lo.val)
            = slotsLive slots.val epoch lo.val (mid.val - lo.val)
              ++ slotsLive slots.val epoch mid.val (hi.val - mid.val) := by
          rw [show hi.val - lo.val = (mid.val - lo.val) + (hi.val - mid.val) by omega,
            slotsLive_add, show lo.val + (mid.val - lo.val) = mid.val by omega]
        rw [hsplit, List.map_append, List.nodup_append] at hnd
        obtain ⟨ND1, ND2, NDd⟩ := hnd
        obtain ⟨hinv1, hkeys1, P1, hlenA, hmlA, hsatA, hepA, hentA, hlen1, f1⟩ :=
          ih (mid.val - lo.val) (by omega) nt nt1 slots slots1 lo mid epoch rfl (by omega)
            hne hinv hkeys hpos (by omega)
            (fun x hx => hP x (by rw [hsplit]; exact List.mem_append_left _ hx)) ND1
            (fun x hx => hdisj x (by rw [hsplit]; exact List.mem_append_left _ hx)) hrec1
        have hF2 : slotsLive slots1.val epoch mid.val (hi.val - mid.val)
            = slotsLive slots.val epoch mid.val (hi.val - mid.val) :=
          slotsLive_congr hlen1 (fun j _ hj2 => f1 j (Or.inr (by omega)))
        have hdisj2 : ∀ x ∈ slotsLive slots1.val epoch mid.val (hi.val - mid.val),
            x.1 ∉ (sl_v nt1).map Prod.fst := by
          intro x hx hmem
          rw [hF2] at hx
          obtain ⟨⟨k0, w⟩, hmem', hfst⟩ := List.mem_map.1 hmem
          simp only at hfst
          have hin : (k0, w) ∈ slotsLive slots.val epoch lo.val (mid.val - lo.val)
              ++ sl_v nt := P1.mem_iff.1 hmem'
          rcases List.mem_append.1 hin with hc | hc
          · exact NDd x.1 (hfst ▸ List.mem_map.2 ⟨(k0, w), hc, rfl⟩)
              x.1 (List.mem_map.2 ⟨x, hx, rfl⟩) rfl
          · exact hdisj x (by rw [hsplit]; exact List.mem_append_right _ hx)
              (hfst ▸ List.mem_map.2 ⟨(k0, w), hc, rfl⟩)
        have hP2 : ∀ x ∈ slotsLive slots1.val epoch mid.val (hi.val - mid.val), P x.1 := by
          rw [hF2]
          exact fun x hx => hP x (by rw [hsplit]; exact List.mem_append_right _ hx)
        have hND2 : ((slotsLive slots1.val epoch mid.val
            (hi.val - mid.val)).map Prod.fst).Nodup := by rw [hF2]; exact ND2
        obtain ⟨hinv', hkeys', P2, hlenB, hmlB, hsatB, hepB, hentB, hlen2, f2⟩ :=
          ih (hi.val - mid.val) (by omega) nt1 nt' slots1 slots' mid hi epoch rfl
            (by omega) (by rw [hepA, hne]) hinv1 hkeys1 (by rw [hlenA]; exact hpos)
            (by rw [hmlA]; omega) hP2 hND2 hdisj2 h2
        refine ⟨hinv', hkeys', ?_, by rw [hlenB, hlenA], by rw [hmlB, hmlA],
          by rw [hsatB, hsatA], by rw [hepB, hepA], by omega, by rw [hlen2, hlen1], ?_⟩
        · rw [hsplit]
          refine P2.trans ?_
          rw [hF2]
          refine (List.Perm.append_left _ P1).trans ?_
          rw [List.append_assoc]
          exact List.perm_append_comm_assoc _ _ _
        · intro j hj
          rw [f2 j (by omega), f1 j (by omega)]
    · rename_i hgt
      have hle : hi.val ≤ lo.val := by scalar_tac
      have e := Result.ok_injective h
      have ent : nt = nt' := congrArg Prod.fst e
      have esl : slots = slots' := congrArg Prod.snd e
      subst ent; subst esl
      refine ⟨hinv, hkeys, ?_, rfl, rfl, rfl, rfl, by omega, rfl, fun _ _ => rfl⟩
      rw [show hi.val - lo.val = 0 by omega, slotsLive_zero]
      simp

omit [DecidableEq K] in
/-- `Inv0` depends on the table only through the five fields it mentions. -/
theorem Inv0_congr {m1 m2 : ron.hashmap2.HashMap2 K V} (h : Inv0 HashableInst m1)
    (hs : m2.slots = m1.slots) (he : m2.epoch = m1.epoch) (hml : m2.max_load = m1.max_load)
    (hsat : m2.saturated = m1.saturated) (hn : m2.num_entries = m1.num_entries) :
    Inv0 HashableInst m2 := by
  have hsl : sl_v m2 = sl_v m1 := by rw [sl_v, sl_v, hs, he]
  have hkv : ∀ j : Nat, slotKV m2 j = slotKV m1 j := fun j => by rw [slotKV, slotKV, hs, he]
  have hlv : ∀ j : Nat, isLive m2 j ↔ isLive m1 j := fun j => by rw [isLive, isLive, hkv]
  refine ⟨by rw [hs]; exact h.pow2, by rw [hs]; exact h.min_cap,
    by rw [hs, hml]; exact h.max_load_eq, by rw [hsat]; exact h.sat,
    by rw [he]; exact h.epoch_pos, ?_, by rw [hsl]; exact h.nodup,
    by rw [hn, hsl]; exact h.entries, ?_⟩
  · intro j g k v hx
    rw [hs] at hx
    rw [he]
    exact h.stamps j g k v hx
  · intro j k v i hj hslot hhome
    rw [hs] at hj hhome
    rw [hkv] at hslot
    obtain ⟨hib, D, hD, hjD, hrun⟩ := h.run j k v i hj hslot hhome
    exact ⟨by rw [hs]; exact hib, D, by rw [hs]; exact hD, by rw [hs]; exact hjD,
      fun d hd => (hlv _).2 (by rw [hs]; exact hrun d hd)⟩

omit [DecidableEq K] in
theorem usize_max_ge_64 : 64 ≤ Std.Usize.max := by
  rcases Std.Usize.bounds_eq with hb | hb <;> rw [hb] <;>
    simp [Std.U32.max, Std.U64.max, Std.U32.numBits, Std.U64.numBits]

/-- **Doubling and rehashing.**  The `saturated` arm — the table cannot grow
past `usize::MAX / 2` — is what the `2 * n ≤ usize::MAX` hypothesis excludes;
see the module note. -/
theorem try_resize_spec {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv0 HashableInst m) (hkeys : KeysOk P m) (hpos : 0 < m.slots.val.length)
    (hcap : 2 * m.slots.val.length ≤ Std.Usize.max) {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.try_resize HashableInst Eq2Inst m = ok m') :
    Inv HashableInst m' ∧ KeysOk P m' ∧ (∀ k, toFun m' k = toFun m k) := by
  rw [ron.hashmap2.HashMap2.try_resize] at h
  obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
  have hcapv : (alloc.vec.Vec.len m.slots).val = m.slots.val.length :=
    alloc.vec.Vec.len_val _
  have hlimv : lim.val = Std.Usize.max / 2 := by
    rw [uscalar_div_eq hlim, show (2#usize : Std.Usize).val = 2 by scalar_tac]
    congr 1
  rcases ite_eq_ok h with ⟨hle, h⟩ | ⟨hgt, h⟩
  · obtain ⟨cap2, hcap2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨nt, hnt, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨q, hmv, hok⟩ := bind_eq_ok_iff.mp h
    obtain ⟨nt1, sl1⟩ := q
    have hcap2v : cap2.val = m.slots.val.length * 2 := by
      rw [uscalar_mul_eq hcap2, hcapv, show (2#usize : Std.Usize).val = 2 by scalar_tac]
    obtain ⟨e0, he0⟩ := hinv.pow2 hpos
    have h32 := hinv.min_cap hpos
    obtain ⟨hdiv, -⟩ := cap_div_four (hinv.pow2 hpos) h32
    have hc2pow : ∃ e, cap2.val = 2 ^ e := ⟨e0 + 1, by rw [hcap2v, he0]; ring⟩
    have hc232 : 32 ≤ cap2.val := by omega
    obtain ⟨hts, htn, html, htep, htsat, -⟩ := new_with_capacity_pow2_spec hnt
    have htlen : nt.slots.val.length = cap2.val := by rw [hts]; simp
    -- the fresh table, with this table's epoch
    set nt0 : ron.hashmap2.HashMap2 K V := { nt with epoch := m.epoch } with hnt0
    have hnt0s : nt0.slots.val = List.replicate cap2.val ron.hashmap2.Slot.Vacant := hts
    have hsl0 : sl_v nt0 = [] := by rw [sl_v, hnt0s]; simp
    obtain ⟨hinv0, -, -⟩ := vacant_table_inv (HashableInst := HashableInst)
      (fun j => by rw [hnt0s]; exact getElem!_replicate_vacant _ _) hsl0
      (by rw [hnt0, htn]; rfl) (by omega)
      (fun _ => by rw [show nt0.slots.val.length = cap2.val by rw [hnt0s]; simp]; exact hc2pow)
      (fun _ => by rw [show nt0.slots.val.length = cap2.val by rw [hnt0s]; simp]; exact hc232)
      (fun _ => by
        rw [show nt0.max_load = nt.max_load from rfl, html,
          show nt0.slots.val.length = cap2.val by rw [hnt0s]; simp])
      (by rw [hnt0]; exact htsat) hinv.epoch_pos
    have hroom : nt0.num_entries.val + ((alloc.vec.Vec.len m.slots).val
        - (0#usize : Std.Usize).val) ≤ nt0.max_load.val := by
      have h0 : nt0.num_entries.val = 0 := by
        rw [show nt0.num_entries = 0#usize from htn]; rfl
      have hz : (0#usize : Std.Usize).val = 0 := by scalar_tac
      have hmlv0 : nt0.max_load.val = 3 * (cap2.val / 4) := by
        rw [show nt0.max_load = nt.max_load from rfl, html]
      rw [h0, hz, hcapv, hmlv0, hcap2v]
      omega
    have hflat : slotsLive m.slots.val m.epoch 0 ((alloc.vec.Vec.len m.slots).val - 0)
        = sl_v m := by
      rw [hcapv, Nat.sub_zero, sl_v]
      exact slotsLive_all
    obtain ⟨hinv1, hkeys1, P1, hlenA, hmlA, hsatA, hepA, -, -, -⟩ :=
      move_slots_spec heq ((alloc.vec.Vec.len m.slots).val - (0#usize : Std.Usize).val)
        nt0 nt1 m.slots sl1 0#usize (alloc.vec.Vec.len m.slots) m.epoch rfl (by rw [hcapv])
        rfl hinv0.toInv0 (by intro p hp; rw [hsl0] at hp; simp at hp)
        (by rw [show nt0.slots.val.length = cap2.val by rw [hnt0s]; simp]; omega)
        hroom
        (by rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat]; exact hkeys)
        (by rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat]; exact hinv.nodup)
        (by rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat, hsl0]; simp) hmv
    rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat, hsl0] at P1
    have Pfin : (sl_v nt1).Perm (sl_v m) := by simpa using P1
    -- the result is `nt1`'s slot vector under this table's other fields
    have hslots : m'.slots = nt1.slots := by rw [← Result.ok_injective hok]
    have hmlv : m'.max_load = nt1.max_load := by rw [← Result.ok_injective hok]
    have hent : m'.num_entries = m.num_entries := by rw [← Result.ok_injective hok]
    have hep : m'.epoch = m.epoch := by rw [← Result.ok_injective hok]
    have hsatv : m'.saturated = m.saturated := by rw [← Result.ok_injective hok]
    have hepnt1 : nt1.epoch = m.epoch := by rw [hepA]
    have hslv : sl_v m' = sl_v nt1 := by rw [sl_v, sl_v, hslots, hep, hepnt1]
    have hnumeq : m'.num_entries = nt1.num_entries := by
      refine UScalar.val_eq_imp _ _ ?_
      rw [hent, hinv.entries, hinv1.entries, Pfin.length_eq]
    have hlen1 : nt1.slots.val.length = cap2.val := by
      rw [hlenA, show nt0.slots.val.length = cap2.val by rw [hnt0s]; simp]
    have hsatf : m'.saturated = nt1.saturated := by
      rw [hsatv, hsatA, hinv.sat]; exact htsat.symm
    refine ⟨⟨Inv0_congr hinv1 hslots (by rw [hep, hepnt1]) hmlv hsatf hnumeq, ?_⟩, ?_, ?_⟩
    · -- `fit`: the doubled table has room for everything the old one held
      rw [hent, hinv.entries, hmlv, hmlA,
        show nt0.max_load = nt.max_load from rfl, html, hcap2v]
      have hle2 : (sl_v m).length ≤ m.slots.val.length := length_filterMap_le
      have : m.slots.val.length * 2 / 4 = m.slots.val.length / 2 := by omega
      omega
    · intro p hp
      rw [hslv] at hp
      exact hkeys p (Pfin.mem_iff.1 hp)
    · intro k
      rw [toFun, toFun, hslv, lookupK_perm Pfin hinv1.nodup]
  · exfalso
    have : lim.val < (alloc.vec.Vec.len m.slots).val := by scalar_tac
    omega


/-! ## `insert`

Three steps and no surprises: allocate if the table has no slots (task #35),
write the entry, and grow if the load is past the threshold. -/

theorem insert_refines_gen {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv HashableInst m) (hkeys : KeysOk P m) {key : K} {value : V} (hk : P key)
    (hcap : 2 * m.slots.val.length ≤ Std.Usize.max)
    {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.insert HashableInst Eq2Inst m key value = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m key ∧
    toFun m' = Function.update (toFun m) key (some value) ∧ KeysOk P m' := by
  rw [ron.hashmap2.HashMap2.insert] at h
  obtain ⟨m0, hens, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hinv0, hpos0, hav0, hent0, hsat0, hep0, hcase0⟩ := ensure_slots_spec hinv hens
  have htf0 : toFun m0 = toFun m := by funext k'; rw [toFun, toFun, hav0]
  have hkeys0 : KeysOk P m0 := by intro p hp; rw [hav0] at hp; exact hkeys p hp
  have hcap0 : 2 * m0.slots.val.length ≤ Std.Usize.max := by
    rcases hcase0 with h32 | heq
    · rw [h32]; exact usize_max_ge_64
    · rw [heq]; exact hcap
  obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨old0, m1⟩ := q
  obtain ⟨hinv1, hold0, htf, hlen1, hml1, hsat1, hep1, hent1, -, -, hkeys1⟩ :=
    insert_no_resize_spec heq hinv0 hkeys0 hk hpos0 hins
  have hold : old0 = toFun m key := by rw [hold0, htf0]
  have hpos1 : 0 < m1.slots.val.length := by rw [hlen1]; exact hpos0
  have hcap1 : 2 * m1.slots.val.length ≤ Std.Usize.max := by rw [hlen1]; exact hcap0
  have hupd : toFun m1 = Function.update (toFun m) key (some value) := by
    funext k'; rw [htf k', htf0, Function.update_apply]
  rcases ite_eq_ok h with ⟨hover, h⟩ | ⟨hunder, h⟩
  · rcases ite_eq_ok h with ⟨hsatt, h⟩ | ⟨-, h⟩
    · -- saturated: excluded by `hcap`, since `try_resize` is what sets the flag
      exfalso
      rw [hsat1, hsat0] at hsatt
      exact absurd hinv.sat (by simp [hsatt])
    · obtain ⟨m2, hres, hok⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hinv2, hkeys2, htf2⟩ := try_resize_spec heq hinv1 hkeys1 hpos1 hcap1 hres
      have e := Result.ok_injective hok
      have e1 : old = old0 := (congrArg Prod.fst e).symm
      have e2 : m' = m2 := (congrArg Prod.snd e).symm
      rw [e1, e2]
      refine ⟨hinv2, hold, ?_, hkeys2⟩
      rw [← hupd]; funext k'; exact htf2 k'
  · have e := Result.ok_injective h
    have e1 : old = old0 := (congrArg Prod.fst e).symm
    have e2 : m' = m1 := (congrArg Prod.snd e).symm
    rw [e1, e2]
    have hle : m1.num_entries.val ≤ m1.max_load.val := by
      by_contra hc
      exact hunder (UScalar.lt_imp _ _ (by omega))
    exact ⟨⟨hinv1, hle⟩, hold, hupd, hkeys1⟩


/-! ## `remove`

**Backward-shift deletion** (Knuth, *TAOCP* 6.4 algorithm R).  The hole the
removal leaves would break the run of every key stored past it, so `repair`
pulls forward the first later entry whose home lies at or before the hole, and
repeats from the slot that entry vacated.

The loop invariant is `RepairInv` below, and it is the piece task
#97-P6-4b priced at "~350 lines, the expensive one": it is a *cyclic-interval*
argument, the only one in this file, and the only place `cyc` and
`wraps_past` are used.  `probe_spec` is not enough for it, because the run
clause has to be re-established rather than read off. -/

omit [DecidableEq K] in
theorem uscalar_rem_eq {ty : UScalarTy} {x y z : UScalar ty} (h : x % y = ok z) :
    z.val = x.val % y.val := by
  by_cases hy : y.val = 0
  · exfalso
    rw [show x % y = UScalar.rem x y from rfl, UScalar.rem, if_neg (by simp [hy])] at h
    simp at h
  · rw [show x % y = UScalar.rem x y from rfl, UScalar.rem, if_pos (by simp [hy])] at h
    rw [← Result.ok_injective h]
    simp only [UScalar.val]
    exact BitVec.toNat_umod

omit [DecidableEq K] in
/-- The three scalar-returning reads `repair` uses so that its loans die at
the join (`hashmap2.rs`'s note on task #97-P4a's second extraction rule). -/
theorem slot_live_spec {s : ron.hashmap2.Slot K V} {e : Std.U32} {bl : Bool}
    (h : ron.hashmap2.slot_live s e = ok bl) : bl = (liveAt e s).isSome := by
  rw [ron.hashmap2.slot_live.eq_def] at h
  cases hsc : s with
  | Vacant => rw [hsc] at h; simp only at h; rw [← Result.ok_injective h]; simp
  | Live g k v =>
    rw [hsc] at h
    simp only at h
    rw [← Result.ok_injective h]
    by_cases hg : g = e <;> simp [hg, liveAt]

omit [DecidableEq K] in
theorem slot_home_spec {s : ron.hashmap2.Slot K V} {g : Std.U32} {k : K} {v : V}
    {n i : Std.Usize} (hsc : s = .Live g k v)
    (h : ron.hashmap2.slot_home HashableInst s n = ok i) : homeAt HashableInst n k = ok i := by
  rw [ron.hashmap2.slot_home.eq_def, hsc] at h
  exact h

omit [DecidableEq K] in
/-- **Algorithm R's test**, read as a cyclic comparison: the entry at `j`,
whose home is `hh`, may be moved back into `hole` exactly when `hh` is *not*
cyclically inside `(hole, j]`. -/
theorem wraps_past_spec {hh hole j n : Std.Usize} {bl : Bool}
    (h : ron.hashmap2.wraps_past hh hole j n = ok bl) :
    (bl = true ↔ cyc n.val hole.val j.val ≤ cyc n.val hh.val j.val) := by
  rw [ron.hashmap2.wraps_past] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i, hi, i1, hi1, dh, hdh, i2, hi2, dk, hdk, hok⟩ := h
  have hiv : i.val = j.val + n.val := uscalar_add_eq hi
  have hdhv : dh.val = cyc n.val hh.val j.val := by
    rw [uscalar_rem_eq hdh, uscalar_sub_eq hi1, hiv, cyc]
  have hdkv : dk.val = cyc n.val hole.val j.val := by
    rw [uscalar_rem_eq hdk, uscalar_sub_eq hi2, hiv, cyc]
  rw [← Result.ok_injective hok]
  simp only [decide_eq_true_eq, ge_iff_le, UScalar.le_equiv, hdhv, hdkv]

/-- Everything `Inv` asks for except the run clause — what `repair` carries
through untouched while it is rebuilding the run clause. -/
structure InvNoRun (HashableInst : ron.hashmap.Hashable K)
    (t : ron.hashmap2.HashMap2 K V) : Prop where
  pow2 : 0 < t.slots.val.length → ∃ e, t.slots.val.length = 2 ^ e
  min_cap : 0 < t.slots.val.length → 32 ≤ t.slots.val.length
  max_load_eq : 0 < t.slots.val.length → t.max_load.val = 3 * (t.slots.val.length / 4)
  fit : t.num_entries.val ≤ t.max_load.val
  sat : t.saturated = false
  epoch_pos : 1 ≤ t.epoch.val
  stamps : ∀ (p : Nat) (g : Std.U32) (k : K) (v : V),
      t.slots.val[p]! = .Live g k v → g.val ≤ t.epoch.val
  nodup : ((sl_v t).map Prod.fst).Nodup
  entries : t.num_entries.val = (sl_v t).length

omit [DecidableEq K] in
theorem InvNoRun.of_Inv {t : ron.hashmap2.HashMap2 K V} (h : Inv HashableInst t) :
    InvNoRun HashableInst t :=
  ⟨h.pow2, h.min_cap, h.max_load_eq, h.fit, h.sat, h.epoch_pos, h.stamps, h.nodup, h.entries⟩

omit [DecidableEq K] in
theorem Inv.of_InvNoRun {t : ron.hashmap2.HashMap2 K V} (h : InvNoRun HashableInst t)
    (hrun : ∀ (p : Nat) (k : K) (v : V) (i : Std.Usize),
      p < t.slots.val.length → slotKV t p = some (k, v) →
      homeAt HashableInst (alloc.vec.Vec.len t.slots) k = ok i →
      i.val < t.slots.val.length ∧
      ∃ D, D < t.slots.val.length ∧ p = idx t.slots.val.length i.val D ∧
        ∀ d, d < D → isLive t (idx t.slots.val.length i.val d)) :
    Inv HashableInst t :=
  ⟨⟨h.pow2, h.min_cap, h.max_load_eq, h.sat, h.epoch_pos, h.stamps, h.nodup, h.entries,
    hrun⟩, h.fit⟩

omit [DecidableEq K] in
/-- `Inv0.run`'s named distance, read as a cyclic one, and back.  `Inv` uses
the first form (it is `omega`-friendly); `RepairInv` uses the second (it is
what `wraps_past` compares). -/
theorem run_of_cyc {n a p : Nat} (hn : 0 < n) (ha : a < n) (hp : p < n)
    {Q : Nat → Prop} (h : ∀ q, q < n → cyc n a q < cyc n a p → Q q) :
    ∃ D, D < n ∧ p = idx n a D ∧ ∀ d, d < D → Q (idx n a d) := by
  have hcn : cyc n a p < n := cyc_lt hn
  refine ⟨cyc n a p, hcn, (idx_cyc ha hp).symm, fun d hd => ?_⟩
  exact h (idx n a d) (idx_lt hn) (by rw [cyc_idx hn ha (by omega)]; exact hd)

omit [DecidableEq K] in
theorem cyc_of_run {n a p D : Nat} (hn : 0 < n) (ha : a < n) {Q : Nat → Prop}
    (hD : D < n) (hpD : p = idx n a D) (h : ∀ d, d < D → Q (idx n a d)) :
    ∀ q, q < n → cyc n a q < cyc n a p → Q q := by
  intro q hq hlt
  have hcp : cyc n a p = D := by rw [hpD, cyc_idx hn ha hD]
  rw [← idx_cyc ha hq]
  exact h (cyc n a q) (by omega)

/-- **Algorithm R's loop invariant**, at `repair hole j` with `fuel` left.

* `free` — the hole is free;
* `scanned` — every slot strictly between `hole` and `j` (cyclically) is live;
  these are the entries the scan examined and decided to keep, and their homes
  lie in `(hole, p]`, so their runs never cross the hole;
* `runs` — every live entry's run from its home is live **except** that it may
  be broken at `hole`, and only for entries at cyclic distance at least
  `cyc n hole j` from the hole, i.e. at or past the scan point;
* `stop` — **`repair`'s own `fuel == 0` obligation**.  There is a free slot,
  other than the hole, within the remaining fuel of the scan point; the scan
  therefore meets one and returns before the fuel runs out.  It survives the
  step because the witness is neither `j` (which is live whenever the scan
  goes on) nor `hole` (excluded outright), so neither of the two writes an
  `act = 1` step performs can fill it, and the scan moves one slot closer to
  it while the fuel drops by one.  `remove` supplies it from `Inv.fit`: the
  table it hands `repair` has at least two free slots, the one it has just
  vacated and one more.

When the scan stops (slot `j` is not live) the exception in `runs` is vacuous
— an entry whose run crossed the hole would have to have `j` in its run — and
`runs` becomes `Inv0.run`. -/
structure RepairInv (HashableInst : ron.hashmap.Hashable K)
    (t : ron.hashmap2.HashMap2 K V) (hole j D fuel : Nat) : Prop where
  free : ¬ isLive t hole
  hole_lt : hole < t.slots.val.length
  j_lt : j < t.slots.val.length
  dist_pos : 0 < D
  dist_le : D ≤ t.slots.val.length
  dist_eq : j = idx t.slots.val.length hole D
  scanned : ∀ d, 0 < d → d < D → isLive t (idx t.slots.val.length hole d)
  runs : ∀ (p : Nat) (k : K) (v : V) (i : Std.Usize),
      p < t.slots.val.length → slotKV t p = some (k, v) →
      homeAt HashableInst (alloc.vec.Vec.len t.slots) k = ok i →
      i.val < t.slots.val.length ∧
      ∀ q, q < t.slots.val.length →
        cyc t.slots.val.length i.val q < cyc t.slots.val.length i.val p →
        isLive t q ∨ (q = hole ∧ D ≤ cyc t.slots.val.length hole p)
  stop : ∃ q, q < t.slots.val.length ∧ q ≠ hole ∧ ¬ isLive t q ∧
      cyc t.slots.val.length j q < fuel

omit [DecidableEq K] in
/-- **The cluster repair.**  `repair` preserves the entries of the table as a
multiset and restores the run clause.  This is task #97-P6-4b's "expensive
one", and the whole of it is the step analysis of `RepairInv` under the three
arms:

* `act = 0` (slot `j` is not live) — the scan stops, and `RepairInv`'s
  exception becomes vacuous: a live entry whose run crossed `hole` has
  `j` strictly inside `[home, p)`, so `j` would have to be live.
* `act = 2` (`¬ wraps_past`, i.e. the entry at `j` has its home cyclically
  inside `(hole, j]`) — the entry stays; `scanned` grows by `j` and `runs` is
  unchanged, because that entry's run lies inside `(hole, j)`, which
  `scanned` says is live.
* `act = 1` (`wraps_past`, i.e. the home of the entry at `j` is *not* in
  `(hole, j]`) — the entry moves back into `hole` and `j` becomes the new
  hole.  Its run shortens by exactly `cyc n hole j`, every slot of the shorter
  run was already live and is untouched, and every other entry's run gains a
  live slot at the old `hole` and may only break at the new one, which is `j`.

plus the `fuel == 0` arm, which `RepairInv.stop` makes unreachable — the
second fuel obligation of the module, and the reason `stop` is a clause at
all.

The three together are the cyclic-interval argument, and `idx_cases` /
`idx_inj` / `idx_surj` / `cyc_cases` above are the arithmetic they run on. -/
theorem repair_spec (F : Nat) :
    ∀ (t t' : ron.hashmap2.HashMap2 K V) (hole j n fuel : Std.Usize) (D : Nat),
      fuel.val = F → n = alloc.vec.Vec.len t.slots → 2 ≤ t.slots.val.length →
      InvNoRun HashableInst t →
      RepairInv HashableInst t hole.val j.val D fuel.val →
      ron.hashmap2.HashMap2.repair HashableInst Eq2Inst t hole j n fuel = ok t' →
      Inv HashableInst t' ∧ (sl_v t').Perm (sl_v t) ∧
        t'.slots.val.length = t.slots.val.length ∧
        t'.max_load = t.max_load ∧ t'.saturated = t.saturated ∧
        t'.epoch = t.epoch ∧ t'.num_entries = t.num_entries := by
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro t t' hole j n fuel D hF hn h2 hinv hrep h
    have hlenv : n.val = t.slots.val.length := by rw [hn]; exact alloc.vec.Vec.len_val _
    have hpos : 0 < t.slots.val.length := by omega
    have hholelt := hrep.hole_lt
    have hjlt := hrep.j_lt
    have hDpos := hrep.dist_pos
    have hDle := hrep.dist_le
    rw [ron.hashmap2.HashMap2.repair.eq_def] at h
    rcases ite_eq_ok h with ⟨hf0, h⟩ | ⟨hf0, h⟩
    · -- the fuel is gone: `RepairInv.stop` says the scan met a free slot first
      exfalso
      obtain ⟨q, -, -, -, hqc⟩ := hrep.stop
      have hfz : fuel.val = 0 := by scalar_tac
      omega
    · have hfne : fuel.val ≠ 0 := by
        intro hc
        exact hf0 (UScalar.val_eq_imp _ _ (by rw [hc]; rfl))
      obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨-, hseq⟩ := vec_index_eq hs
      obtain ⟨bl, hbl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨act, hact, h⟩ := bind_eq_ok_iff.mp h
      have hslot : liveAt t.epoch s = slotKV t j.val := by rw [slotKV, hseq]
      have hblv : bl = (slotKV t j.val).isSome := by rw [slot_live_spec hbl, hslot]
      have hcycj : cyc t.slots.val.length hole.val j.val
          = if D = t.slots.val.length then 0 else D := by
        rw [hrep.dist_eq]
        split
        · rename_i hD
          rw [hD, show idx t.slots.val.length hole.val t.slots.val.length = hole.val by
            rw [idx, Nat.add_mod_right, Nat.mod_eq_of_lt hholelt], cyc_self hholelt]
        · rename_i hD
          exact cyc_idx hpos hholelt (by have := hrep.dist_le; omega)
      rcases ite_eq_ok hact with ⟨hbt, hact⟩ | ⟨hbf, hact⟩
      · -- slot `j` is live: decide whether its entry may move back
        obtain ⟨hh, hhh, hact⟩ := bind_eq_ok_iff.mp hact
        obtain ⟨b1, hb1, hact⟩ := bind_eq_ok_iff.mp hact
        have hlivej : (slotKV t j.val).isSome := by rw [← hblv]; exact hbt
        have hjne : j.val ≠ hole.val := by
          intro hc
          rw [hc] at hlivej
          exact hrep.free hlivej
        have hDlt : D < t.slots.val.length := by
          have := hrep.dist_le
          rcases Nat.lt_or_ge D t.slots.val.length with hd | hd
          · exact hd
          · exfalso
            apply hjne
            rw [hrep.dist_eq, show D = t.slots.val.length by omega, idx,
              Nat.add_mod_right, Nat.mod_eq_of_lt hholelt]
        have hcycjD : cyc t.slots.val.length hole.val j.val = D := by
          rw [hcycj, if_neg (by omega)]
        rcases ite_eq_ok hact with ⟨hb1t, hact⟩ | ⟨hb1f, hact⟩
        · -- `act = 1`: the home of the entry at `j` is *not* cyclically inside
          -- `(hole, j]`, so the entry may be pulled back into the hole; `j`
          -- becomes the new hole and the scan restarts one slot on
          have hacte : act = 1#i32 := (Result.ok_injective hact).symm
          obtain ⟨kj, vj, hkv⟩ : ∃ kj vj, slotKV t j.val = some (kj, vj) := by
            cases hc : slotKV t j.val with
            | none => rw [hc] at hlivej; simp at hlivej
            | some pw => exact ⟨pw.1, pw.2, rfl⟩
          have hsl2 : liveAt t.epoch s = some (kj, vj) := by rw [hslot]; exact hkv
          have hscj : s = ron.hashmap2.Slot.Live t.epoch kj vj := liveAt_inv hsl2
          have hhome : homeAt HashableInst (alloc.vec.Vec.len t.slots) kj = ok hh := by
            rw [← hn]; exact slot_home_spec hscj hhh
          obtain ⟨hhlt, hrunj⟩ := hrep.runs j.val kj vj hh hjlt hkv hhome
          have hw : D ≤ cyc t.slots.val.length hh.val j.val := by
            have hb1v := wraps_past_spec hb1
            rw [hlenv] at hb1v
            have hc := hb1v.1 (by simpa using hb1t)
            rw [hcycjD] at hc
            exact hc
          -- the hole lies strictly inside the moved entry's run
          have huv : cyc t.slots.val.length hh.val hole.val
              < cyc t.slots.val.length hh.val j.val := by
            have e := cyc_cases (n := t.slots.val.length) (a := hh.val) (b := hole.val)
              (c := j.val) hpos hhlt hholelt hjlt
            rw [hcycjD] at e
            have b1 : cyc t.slots.val.length hh.val hole.val < t.slots.val.length :=
              cyc_lt hpos
            have b2 : cyc t.slots.val.length hh.val j.val < t.slots.val.length := cyc_lt hpos
            omega
          -- peel the two writes
          have hne0 : ¬ (act = 0#i32) := by rw [hacte]; simp
          replace h := ((ite_eq_ok h).resolve_left (fun hc => hne0 hc.1)).2
          replace h := ((ite_eq_ok h).resolve_right (fun hc => hc.1 hacte)).2
          obtain ⟨p1, hidx1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨s1, back⟩ := p1
          obtain ⟨-, hs1eq, hback⟩ := vec_index_mut_eq hidx1
          subst hback
          obtain ⟨p2, hidx2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨sh, back1⟩ := p2
          obtain ⟨-, -, hback1⟩ := vec_index_mut_eq hidx2
          subst hback1
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨f1, hf1, h⟩ := bind_eq_ok_iff.mp h
          have hs1 : s1 = s := by rw [hs1eq, hseq]
          subst hs1
          -- the new table
          set lb : List (ron.hashmap2.Slot K V) := t.slots.val.set j.val .Vacant with hlb
          set t1 : ron.hashmap2.HashMap2 K V :=
            { t with slots := alloc.vec.Vec.set (alloc.vec.Vec.set t.slots j .Vacant) hole s1 }
            with ht1
          have hjlb : j.val < lb.length := by rw [hlb, List.length_set]; omega
          have hholelb : hole.val < lb.length := by rw [hlb, List.length_set]; omega
          have ht1s : t1.slots.val = lb.set hole.val s1 := by
            rw [ht1, hlb]
            simp only [alloc.vec.Vec.set_val_eq]
          have hlen1 : t1.slots.val.length = t.slots.val.length := by
            rw [ht1s, List.length_set, hlb, List.length_set]
          have ht1e : t1.epoch = t.epoch := rfl
          -- what each slot of the new table reads
          have hkvhole : slotKV t1 hole.val = some (kj, vj) := by
            rw [slotKV, ht1s, getElem!_set_self _ hholelb, ht1e, hscj]
            simp
          have hkvj : slotKV t1 j.val = none := by
            rw [slotKV, ht1s, getElem!_set_ne _ hjne, hlb, getElem!_set_self _ (by omega)]
            rfl
          have hkvo : ∀ p : Nat, p ≠ j.val → p ≠ hole.val → slotKV t1 p = slotKV t p := by
            intro p hpj hph
            rw [slotKV, slotKV, ht1s, getElem!_set_ne _ hph, hlb, getElem!_set_ne _ hpj, ht1e]
          -- the entries are preserved as a multiset
          have hperm : (sl_v t1).Perm (sl_v t) := by
            have e1 : (sl_v t).Perm ((kj, vj) :: lb.filterMap (liveAt t.epoch)) := by
              have := filterMap_perm (l := t.slots.val) (f := liveAt t.epoch)
                (i := j.val) (by omega) .Vacant rfl
              rw [show liveAt t.epoch t.slots.val[j.val]! = some (kj, vj) from hkv] at this
              exact this
            have e2 : (lb.filterMap (liveAt t.epoch)).Perm
                ((lb.set hole.val .Vacant).filterMap (liveAt t.epoch)) := by
              have := filterMap_perm (l := lb) (f := liveAt t.epoch) (i := hole.val)
                hholelb .Vacant rfl
              rw [show liveAt t.epoch lb[hole.val]! = none by
                rw [hlb, getElem!_set_ne _ (Ne.symm hjne)]
                exact Option.not_isSome_iff_eq_none.mp hrep.free] at this
              simpa using this
            have e3 : (sl_v t1).Perm ((kj, vj) ::
                (lb.set hole.val .Vacant).filterMap (liveAt t.epoch)) := by
              have := filterMap_set_perm (l := lb) (f := liveAt t.epoch) (i := hole.val)
                hholelb s1 .Vacant rfl
              rw [show liveAt t.epoch s1 = some (kj, vj) from hsl2] at this
              rw [sl_v, ht1s, ht1e]
              simpa using this
            exact e3.trans (((e2.trans (List.Perm.refl _)).cons (kj, vj)).symm.trans e1.symm)
          -- the invariant clauses the walk does not touch
          have hinv1 : InvNoRun HashableInst t1 := by
            refine ⟨by rw [hlen1]; exact hinv.pow2, by rw [hlen1]; exact hinv.min_cap,
              by rw [hlen1]; exact hinv.max_load_eq, hinv.fit, hinv.sat, hinv.epoch_pos,
              ?_, ?_, ?_⟩
            · intro p g k v hx
              rw [ht1e]
              by_cases hph : p = hole.val
              · subst hph
                rw [ht1s, getElem!_set_self _ hholelb, hscj] at hx
                injection hx with e1 e2 e3
                have he : t.epoch.val = g.val := by rw [e1]
                omega
              · by_cases hpj : p = j.val
                · subst hpj
                  rw [ht1s, getElem!_set_ne _ hjne, hlb,
                    getElem!_set_self (l := t.slots.val) (i := j.val) _ hjlt] at hx
                  simp at hx
                · rw [ht1s, getElem!_set_ne _ hph, hlb, getElem!_set_ne _ hpj] at hx
                  exact hinv.stamps p g k v hx
            · exact (hperm.map Prod.fst).nodup_iff.2 hinv.nodup
            · rw [show t1.num_entries = t.num_entries from rfl, hinv.entries,
                hperm.length_eq]
          have hi2v : i2.val = (j.val + 1) % t.slots.val.length := by
            rw [next_index_spec (by omega) hi2, hlenv]
          have hf1v : f1.val = fuel.val - 1 := by rw [uscalar_sub_eq hf1]; simp
          have hhomelen : alloc.vec.Vec.len t1.slots = alloc.vec.Vec.len t.slots :=
            vec_len_congr hlen1
          -- the repair invariant, one hole on
          have hrep1 : RepairInv HashableInst t1 j.val i2.val 1 f1.val := by
            refine ⟨by simp [isLive, hkvj], by rw [hlen1]; omega,
              by rw [hlen1, hi2v]; exact Nat.mod_lt _ hpos, by omega, by rw [hlen1]; omega,
              by rw [hlen1, hi2v, idx], ?_, ?_, ?_⟩
            · intro d hd0 hd; omega
            · -- `runs`: the moved entry's run shortened, and every other run
              -- gained the old hole back
              intro p k v i0 hp hslotp hhome0
              rw [hlen1] at hp
              rw [hhomelen] at hhome0
              have hpj : p ≠ j.val := by
                intro hc; rw [hc, hkvj] at hslotp; simp at hslotp
              by_cases hph : p = hole.val
              · -- the moved entry
                subst hph
                rw [hkvhole] at hslotp
                have hkk : k = kj := (congrArg Prod.fst (Option.some.inj hslotp)).symm
                subst hkk
                have hi0 : i0 = hh := Result.ok_injective (hhome0.symm.trans hhome)
                subst hi0
                refine ⟨by rw [hlen1]; exact hhlt, fun q hq hqlt => ?_⟩
                rw [hlen1] at hq hqlt ⊢
                by_cases hqj : q = j.val
                · exact Or.inr ⟨hqj, by
                    have : cyc t.slots.val.length j.val hole.val ≠ 0 := fun hc =>
                      hjne (cyc_eq_zero hjlt hholelt hc)
                    omega⟩
                · refine Or.inl ?_
                  have hqlt2 : cyc t.slots.val.length i0.val q
                      < cyc t.slots.val.length i0.val j.val := by omega
                  rcases hrunj q hq hqlt2 with hl | ⟨hqh, -⟩
                  · rw [isLive, hkvo q hqj (by intro hc; rw [hc] at hqlt; omega)]
                    exact hl
                  · exact absurd hqlt (by rw [hqh]; omega)
              · -- every other entry
                rw [hkvo p hpj hph] at hslotp
                obtain ⟨hi0, hrun⟩ := hrep.runs p k v i0 hp hslotp hhome0
                refine ⟨by rw [hlen1]; exact hi0, fun q hq hqlt => ?_⟩
                rw [hlen1] at hq hqlt ⊢
                by_cases hqj : q = j.val
                · refine Or.inr ⟨hqj, ?_⟩
                  have : cyc t.slots.val.length j.val p ≠ 0 := fun hc =>
                    hpj (cyc_eq_zero hjlt hp hc).symm
                  omega
                rcases hrun q hq hqlt with hl | ⟨hqh, -⟩
                · refine Or.inl ?_
                  by_cases hqh2 : q = hole.val
                  · rw [isLive, hqh2, hkvhole]; simp
                  · rw [isLive, hkvo q hqj hqh2]; exact hl
                · exact Or.inl (by rw [isLive, hqh, hkvhole]; simp)
            · -- `stop`: the witness is neither of the two slots that changed
              obtain ⟨q, hq, hqh, hql, hqc⟩ := hrep.stop
              have hqj : q ≠ j.val := by
                intro hc; rw [hc] at hql; exact hql hlivej
              refine ⟨q, by rw [hlen1]; exact hq, hqj, ?_, ?_⟩
              · rw [isLive, hkvo q hqj hqh]; exact hql
              · have hstep := cyc_step (n := t.slots.val.length) (by omega) hjlt hq hqj
                have hidx1 : idx t.slots.val.length j.val 1 = i2.val := by rw [idx, hi2v]
                rw [hidx1] at hstep
                rw [hlen1]
                omega
          obtain ⟨hinv', hperm', hlenB, hmlB, hsatB, hepB, hentB⟩ :=
            ih f1.val (by omega) t1 t' j i2 n f1 1 rfl (by rw [hhomelen]; exact hn)
              (by rw [hlen1]; omega) hinv1 hrep1 h
          exact ⟨hinv', hperm'.trans hperm, by rw [hlenB, hlen1],
            by rw [hmlB], by rw [hsatB], by rw [hepB], by rw [hentB]⟩
        · -- `act = 2`: the entry's home is cyclically inside `(hole, j]`, so
          -- moving it back would break its own run; it stays, and the scan
          -- moves on with `hole` where it was
          have hacte : act = 2#i32 := (Result.ok_injective hact).symm
          obtain ⟨kj, vj, hkv⟩ : ∃ kj vj, slotKV t j.val = some (kj, vj) := by
            cases hc : slotKV t j.val with
            | none => rw [hc] at hlivej; simp at hlivej
            | some pw => exact ⟨pw.1, pw.2, rfl⟩
          have hsl2 : liveAt t.epoch s = some (kj, vj) := by rw [hslot]; exact hkv
          have hscj : s = ron.hashmap2.Slot.Live t.epoch kj vj := liveAt_inv hsl2
          have hhome : homeAt HashableInst (alloc.vec.Vec.len t.slots) kj = ok hh := by
            rw [← hn]; exact slot_home_spec hscj hhh
          obtain ⟨hhlt, -⟩ := hrep.runs j.val kj vj hh hjlt hkv hhome
          have hnw : cyc t.slots.val.length hh.val j.val < D := by
            have hb1v := wraps_past_spec hb1
            rw [hlenv] at hb1v
            have hc : ¬ (cyc t.slots.val.length hole.val j.val
                ≤ cyc t.slots.val.length hh.val j.val) := fun hc => hb1f (hb1v.2 hc)
            rw [hcycjD] at hc
            omega
          rcases ite_eq_ok h with ⟨h0, -⟩ | ⟨-, h⟩
          · exfalso; rw [hacte] at h0; simp at h0
          rcases ite_eq_ok h with ⟨h1, -⟩ | ⟨-, h⟩
          · exfalso; rw [hacte] at h1; simp at h1
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨f1, hf1, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = (j.val + 1) % t.slots.val.length := by
            rw [next_index_spec (by omega) hi2, hlenv]
          have hf1v : f1.val = fuel.val - 1 := by rw [uscalar_sub_eq hf1]; simp
          have hidxs : i2.val = idx t.slots.val.length hole.val (D + 1) := by
            rw [idx_succ, ← hrep.dist_eq, hi2v]
          refine ih f1.val (by omega) t t' hole i2 n f1 (D + 1) rfl hn h2 hinv ?_ h
          refine ⟨hrep.free, hholelt, by rw [hi2v]; exact Nat.mod_lt _ hpos, by omega,
            by omega, hidxs, ?_, ?_, ?_⟩
          · -- `scanned` grows by the slot just examined
            intro d hd0 hd
            rcases Nat.lt_or_ge d D with hlt | hge
            · exact hrep.scanned d hd0 hlt
            · rw [show d = D by omega, ← hrep.dist_eq]
              exact hlivej
          · -- `runs`: the entry at `j` cannot itself have the hole in its run
            intro p k v i0 hp hslotp hhome0
            obtain ⟨hi0, hrun⟩ := hrep.runs p k v i0 hp hslotp hhome0
            refine ⟨hi0, fun q hq hqlt => ?_⟩
            rcases hrun q hq hqlt with hl | ⟨hqh, hDle'⟩
            · exact Or.inl hl
            refine Or.inr ⟨hqh, ?_⟩
            rcases Nat.lt_or_ge D (cyc t.slots.val.length hole.val p) with hlt | hge
            · omega
            exfalso
            have hcp : cyc t.slots.val.length hole.val p = D := by omega
            have hpj : p = j.val := by
              rw [← idx_cyc (a := hole.val) hholelt hp, hcp, ← hrep.dist_eq]
            have hkk : k = kj := by
              rw [hpj, hkv] at hslotp
              exact (congrArg Prod.fst (Option.some.inj hslotp)).symm
            have hi0h : i0 = hh := by
              rw [hkk] at hhome0
              exact Result.ok_injective (hhome0.symm.trans hhome)
            rw [hqh, hpj, hi0h] at hqlt
            have e := cyc_cases (n := t.slots.val.length) (a := hh.val) (b := hole.val)
              (c := j.val) hpos hhlt hholelt hjlt
            rw [hcycjD] at e
            have b1 : cyc t.slots.val.length hh.val hole.val < t.slots.val.length :=
              cyc_lt hpos
            have b2 : cyc t.slots.val.length hh.val j.val < t.slots.val.length := cyc_lt hpos
            omega
          · -- `stop`: one slot closer, one unit of fuel less
            obtain ⟨q, hq, hqh, hql, hqc⟩ := hrep.stop
            refine ⟨q, hq, hqh, hql, ?_⟩
            have hqj : q ≠ j.val := by
              intro hc; rw [hc] at hql; exact hql hlivej
            have hstep := cyc_step (n := t.slots.val.length) (by omega) hjlt hq hqj
            have hidx1 : idx t.slots.val.length j.val 1 = i2.val := by
              rw [idx, hi2v]
            rw [hidx1] at hstep
            omega
      · -- `act = 0`: slot `j` is not live, the scan stops, and the run clause
        -- is restored
        have hnl : ¬ (slotKV t j.val).isSome := by rw [← hblv]; simpa using hbf
        have hacte : act = 0#i32 := (Result.ok_injective hact).symm
        rcases ite_eq_ok h with ⟨-, h⟩ | ⟨hne, h⟩
        · have ht : t' = t := (Result.ok_injective h).symm
          rw [ht]
          refine ⟨Inv.of_InvNoRun hinv ?_, List.Perm.refl _, rfl, rfl, rfl, rfl, rfl⟩
          intro p k v i hp hslotp hhome
          obtain ⟨hilt, hrun⟩ := hrep.runs p k v i hp hslotp hhome
          refine ⟨hilt, run_of_cyc hpos hilt hp ?_⟩
          intro q hq hqlt
          rcases hrun q hq hqlt with hlive | ⟨hqh, hD⟩
          · exact hlive
          · exfalso
            subst hqh
            -- the hole is inside `p`'s run and the scan has reached at least `p`
            have hcp : cyc t.slots.val.length hole.val p < t.slots.val.length :=
              cyc_lt hpos
            have hDlt : D < t.slots.val.length := by omega
            have hjne : j.val ≠ hole.val := by
              intro hc
              have hc0 : idx t.slots.val.length hole.val D
                  = idx t.slots.val.length hole.val 0 := by
                rw [← hrep.dist_eq, idx_zero hholelt]; exact hc
              have := idx_inj hpos hDlt hpos hc0
              omega
            have hcycjD : cyc t.slots.val.length hole.val j.val = D := by
              rw [hcycj, if_neg (by omega)]
            -- `cyc i hole + cyc hole p = cyc i p`, and likewise through `j`
            have e1 := cyc_cases (n := t.slots.val.length) (a := i.val) (b := hole.val)
              (c := p) hpos hilt hholelt hp
            have e2 := cyc_cases (n := t.slots.val.length) (a := i.val) (b := hole.val)
              (c := j.val) hpos hilt hholelt hjlt
            have b1 : cyc t.slots.val.length i.val hole.val < t.slots.val.length :=
              cyc_lt hpos
            have b2 : cyc t.slots.val.length i.val p < t.slots.val.length := cyc_lt hpos
            have b3 : cyc t.slots.val.length i.val j.val < t.slots.val.length := cyc_lt hpos
            rw [hcycjD] at e2
            have hlt2 : cyc t.slots.val.length i.val j.val
                ≤ cyc t.slots.val.length i.val p := by omega
            rcases Nat.lt_or_ge (cyc t.slots.val.length i.val j.val)
                (cyc t.slots.val.length i.val p) with hstrict | hge
            · rcases hrun j.val hjlt hstrict with hlivej | ⟨hjh, -⟩
              · exact hnl hlivej
              · exact hjne hjh
            · -- `j = p`, but `p` is live and `j` is not
              have hjp : j.val = p := by
                have := idx_cyc (a := i.val) (b := j.val) hilt hjlt
                have h2' := idx_cyc (a := i.val) (b := p) hilt hp
                rw [show cyc t.slots.val.length i.val j.val
                  = cyc t.slots.val.length i.val p by omega] at this
                rw [← this, h2']
              rw [hjp] at hnl
              exact hnl (by rw [hslotp]; simp)
        · exact absurd (by rw [hacte]) hne

/-- **`remove` unbinds the key.**  The `slots.len() == 0` guard is the
unallocated table, exactly as in `get`; a probe that does not find the key
leaves the table alone; and otherwise the slot is vacated and `repair` closes
the hole.  The vacated table is `∅` at that slot and the *same* multiset of
entries less one, which is the whole of the abstract step; `repair_spec` does
the representation work. -/
theorem remove_refines_gen {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv HashableInst m) (hkeys : KeysOk P m) {key : K} (hk : P key)
    {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.remove HashableInst Eq2Inst m key = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m key ∧
    toFun m' = Function.update (toFun m) key none ∧ KeysOk P m' := by
  rw [ron.hashmap2.HashMap2.remove] at h
  split at h
  · -- the unallocated table of `new` (task #35), exactly as in `get`
    rename_i h0
    have hav : sl_v m = [] := sl_v_of_slots_nil (vec_len_eq_zero_iff.mp h0)
    have e := Result.ok_injective h
    have e1 : old = none := (congrArg Prod.fst e).symm
    have e2 : m' = m := (congrArg Prod.snd e).symm
    subst e1; subst e2
    refine ⟨hinv, by simp [toFun, hav], ?_, hkeys⟩
    funext k'; simp [toFun, hav, Function.update_apply]
  · rename_i h0
    have hpos : 0 < m.slots.val.length := by
      rcases Nat.eq_zero_or_pos m.slots.val.length with hz | hp
      · exact absurd (vec_len_eq_zero_iff.mpr (List.eq_nil_of_length_eq_zero hz)) h0
      · exact hp
    simp only [bind_eq_ok_iff] at h
    obtain ⟨hw, hhash, i1, hbi, q, hprobe, h⟩ := h
    obtain ⟨i2, b⟩ := q
    have hhome : homeAt HashableInst (alloc.vec.Vec.len m.slots) key = ok i1 := by
      simp only [homeAt, bind_eq_ok_iff]; exact ⟨hw, hhash, hbi⟩
    obtain ⟨hatlt, hilt, htrue, hfalse⟩ := probe_spec heq hinv hkeys hk hpos hhome hprobe
    rcases ite_eq_ok h with ⟨hb, h⟩ | ⟨hb, h⟩
    · -- the key is live at `i2`: vacate the slot, then close the hole
      obtain ⟨w, hslot, htf⟩ := htrue (by simpa using hb)
      have hlenv : (alloc.vec.Vec.len m.slots).val = m.slots.val.length :=
        alloc.vec.Vec.len_val _
      obtain ⟨p1, hidx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨sl, back⟩ := p1
      obtain ⟨-, hseq, hback⟩ := vec_index_mut_eq hidx
      subst hback
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨self1, hrepair, hok⟩ := bind_eq_ok_iff.mp h
      have hsl2 : liveAt m.epoch sl = some (key, w) := by rw [hseq, ← slotKV]; exact hslot
      have hscj : sl = ron.hashmap2.Slot.Live m.epoch key w := liveAt_inv hsl2
      rw [hscj] at hok
      have e := Result.ok_injective hok
      have eold : old = some w := (congrArg Prod.fst e).symm
      have em : m' = self1 := (congrArg Prod.snd e).symm
      subst em
      -- the table with the key's slot vacated
      set t0 : ron.hashmap2.HashMap2 K V :=
        { m with num_entries := i3, slots := alloc.vec.Vec.set m.slots i2 .Vacant } with ht0
      have ht0s : t0.slots.val = m.slots.val.set i2.val .Vacant := by
        rw [ht0]; exact alloc.vec.Vec.set_val_eq _ _ _
      have ht0e : t0.epoch = m.epoch := rfl
      have ht0len : t0.slots.val.length = m.slots.val.length := by
        rw [ht0s, List.length_set]
      have ht0sl : sl_v t0 = rest m i2.val := by rw [sl_v, ht0s, ht0e, rest]
      have hi3v : i3.val = m.num_entries.val - 1 := by rw [uscalar_sub_eq hi3]; simp
      have hPM : (sl_v m).Perm ((key, w) :: sl_v t0) := by
        have := sl_v_perm_rest (m := m) hatlt
        rw [hslot] at this
        rw [ht0sl]
        simpa using this
      have hND := hinv.nodup
      rw [(hPM.map Prod.fst).nodup_iff, List.map_cons, List.nodup_cons] at hND
      obtain ⟨hkeyR, hNDR⟩ := hND
      have hfreei2 : slotKV t0 i2.val = none := by
        rw [slotKV, ht0e, ht0s, getElem!_set_self _ hatlt]; rfl
      have hother : ∀ p : Nat, p ≠ i2.val → slotKV t0 p = slotKV m p := by
        intro p hp
        rw [slotKV, slotKV, ht0e, ht0s, getElem!_set_ne _ hp]
      -- the invariant clauses `repair` carries through
      have hinv0 : InvNoRun HashableInst t0 := by
        refine ⟨by rw [ht0len]; exact hinv.pow2, by rw [ht0len]; exact hinv.min_cap,
          by rw [ht0len]; exact hinv.max_load_eq, ?_, hinv.sat, hinv.epoch_pos, ?_, ?_, ?_⟩
        · rw [show t0.num_entries = i3 from rfl, show t0.max_load = m.max_load from rfl, hi3v]
          have := hinv.fit; omega
        · intro p g k v hx
          rw [ht0e]
          by_cases hp : p = i2.val
          · subst hp; rw [ht0s, getElem!_set_self _ hatlt] at hx; simp at hx
          · rw [ht0s, getElem!_set_ne _ hp] at hx
            exact hinv.stamps p g k v hx
        · exact hNDR
        · rw [show t0.num_entries = i3 from rfl, hi3v, hinv.entries, hPM.length_eq,
            List.length_cons, ht0sl]
          omega
      have hi4v : i4.val = (i2.val + 1) % m.slots.val.length := by
        rw [next_index_spec (by omega) hi4, hlenv]
      have hrep : RepairInv HashableInst t0 i2.val i4.val 1 (alloc.vec.Vec.len m.slots).val := by
        obtain ⟨q, hq, hqfree⟩ := exists_free_slot hinv hpos
        have hqi2 : q ≠ i2.val := by
          intro hc; rw [hc, hslot] at hqfree; simp at hqfree
        refine ⟨by rw [isLive, hfreei2]; simp, by rw [ht0len]; exact hatlt,
          by rw [ht0len, hi4v]; exact Nat.mod_lt _ hpos, by omega, by rw [ht0len]; omega,
          by rw [ht0len, hi4v, idx], by intro d hd0 hd; omega, ?_,
          ⟨q, by rw [ht0len]; exact hq, hqi2, ?_, ?_⟩⟩
        · -- every run of the old table survives, save at the vacated slot
          intro p k v i0 hp hslotp hhome0
          rw [ht0len] at hp
          rw [show alloc.vec.Vec.len t0.slots = alloc.vec.Vec.len m.slots from
            vec_len_congr ht0len] at hhome0
          have hpi2 : p ≠ i2.val := by
            intro hc; rw [hc, hfreei2] at hslotp; simp at hslotp
          rw [hother p hpi2] at hslotp
          obtain ⟨hi0, D, hD, hpD, hrun⟩ := hinv.run p k v i0 hp hslotp hhome0
          refine ⟨by rw [ht0len]; exact hi0, fun q' hq' hqlt => ?_⟩
          rw [ht0len] at hq' hqlt ⊢
          by_cases hq'i : q' = i2.val
          · refine Or.inr ⟨hq'i, ?_⟩
            have : cyc m.slots.val.length i2.val p ≠ 0 := fun hc =>
              hpi2 (cyc_eq_zero hatlt hp hc).symm
            omega
          · refine Or.inl ?_
            rw [isLive, hother q' hq'i]
            exact cyc_of_run hpos hi0 hD hpD hrun q' hq' hqlt
        · rw [isLive, hother q hqi2, hqfree]; simp
        · rw [ht0len]
          have := cyc_lt (n := m.slots.val.length) (a := i4.val) (b := q) hpos
          omega
      obtain ⟨hinvf, hpermf, hlenf, -, -, -, -⟩ :=
        repair_spec (alloc.vec.Vec.len m.slots).val t0 m' i2 i4
          (alloc.vec.Vec.len m.slots) (alloc.vec.Vec.len m.slots) 1 rfl
          (by rw [show alloc.vec.Vec.len t0.slots = alloc.vec.Vec.len m.slots from
            vec_len_congr ht0len])
          (by rw [ht0len]; have := hinv.min_cap hpos; omega) hinv0 hrep hrepair
      have hlk : ∀ k', lookupK (sl_v m') k' = lookupK (sl_v t0) k' :=
        fun k' => lookupK_perm hpermf hinvf.nodup k'
      refine ⟨hinvf, by rw [eold, htf], ?_, ?_⟩
      · funext k'
        rw [Function.update_apply, toFun, toFun, hlk, lookupK_perm hPM hinv.nodup,
          lookupK_cons]
        by_cases hk' : k' = key
        · subst hk'; simp [lookupK_eq_none_of_not_mem hkeyR]
        · rw [if_neg (Ne.symm hk'), if_neg hk']
      · intro p hp
        have hx : p ∈ sl_v t0 := hpermf.mem_iff.1 hp
        rw [ht0sl] at hx
        exact hkeys p (rest_subset hx)
    · -- the key is not in the table: nothing moves
      obtain ⟨-, htf, -⟩ := hfalse (by simpa using hb)
      have e := Result.ok_injective h
      have e1 : old = none := (congrArg Prod.fst e).symm
      have e2 : m' = m := (congrArg Prod.snd e).symm
      subst e1; subst e2
      refine ⟨hinv, htf.symm, ?_, hkeys⟩
      funext k'
      rw [Function.update_apply]
      by_cases hk' : k' = key
      · subst hk'; simp [htf]
      · simp [hk']


/-! ## The unrestricted API

`HashMap.lean`'s nine entry points, statement for statement, as the
unrestricted (`Eq2Spec`, no `KeysOk`) specialisation of the lemmas above:
`Eq2Fwd_of_Eq2Spec` at `P := fun _ => True`, where `KeysOk` is vacuous.  A
consumer can swap `HashMap` for `HashMap2` in a relation statement without
changing the statement. -/

omit [DecidableEq K] in
theorem KeysOk_true : KeysOk (fun _ : K => True) m := fun _ _ => trivial

theorem get_refines (heq : Eq2Spec Eq2Inst) (hinv : Inv HashableInst m) {key : K}
    {r : Option V} (h : ron.hashmap2.HashMap2.get HashableInst Eq2Inst m key = ok r) :
    r = toFun m key :=
  get_refines_gen (Eq2Fwd_of_Eq2Spec heq) hinv KeysOk_true trivial h

theorem contains_key_refines (heq : Eq2Spec Eq2Inst) (hinv : Inv HashableInst m)
    {key : K} {b : Bool}
    (h : ron.hashmap2.HashMap2.contains_key HashableInst Eq2Inst m key = ok b) :
    b = (toFun m key).isSome :=
  contains_key_refines_gen (Eq2Fwd_of_Eq2Spec heq) hinv KeysOk_true trivial h

theorem insert_refines (heq : Eq2Spec Eq2Inst) (hinv : Inv HashableInst m)
    (hcap : 2 * m.slots.val.length ≤ Std.Usize.max) {key : K} {value : V}
    {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.insert HashableInst Eq2Inst m key value = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m key ∧
    toFun m' = Function.update (toFun m) key (some value) := by
  obtain ⟨h1, h2, h3, -⟩ :=
    insert_refines_gen (Eq2Fwd_of_Eq2Spec heq) hinv KeysOk_true trivial hcap h
  exact ⟨h1, h2, h3⟩

theorem remove_refines (heq : Eq2Spec Eq2Inst) (hinv : Inv HashableInst m) {key : K}
    {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.remove HashableInst Eq2Inst m key = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m key ∧
    toFun m' = Function.update (toFun m) key none := by
  obtain ⟨h1, h2, h3, -⟩ :=
    remove_refines_gen (Eq2Fwd_of_Eq2Spec heq) hinv KeysOk_true trivial h
  exact ⟨h1, h2, h3⟩


/-! ## The bridge to `Std.HashMap`

`HashMap.lean`'s `Rel` and its four lemmas, word for word over the new
`toFun` — which is the load-bearing claim of task #97-P6-4b §4: everything
downstream of `toFun` / `Rel` / `RelOn` is stated at the abstract map and does
not move. -/

section Bridge

variable {K' V' : Type} [BEq K'] [Hashable K'] {absK : K → K'} {absV : V → V'}

/-- `m` represents `s` under the abstractions `absK`, `absV`. -/
def Rel (m : ron.hashmap2.HashMap2 K V) (s : _root_.Std.HashMap K' V')
    (absK : K → K') (absV : V → V') : Prop :=
  ∀ k, (toFun m k).map absV = s[absK k]?

/-- The empty relation.  Compose with `new_refines`, `with_capacity_refines`,
`clear_refines` or `clear_fit_refines`, whose third component is exactly this
hypothesis. -/
theorem Rel_empty (h : ∀ k, toFun m k = none) :
    Rel m (∅ : _root_.Std.HashMap K' V') absK absV := by
  intro k; rw [h k, _root_.Std.HashMap.getElem?_empty]; rfl

theorem Rel_get {s : _root_.Std.HashMap K' V'} (heq : Eq2Spec Eq2Inst)
    (hinv : Inv HashableInst m) (hrel : Rel m s absK absV) {key : K} {r : Option V}
    (h : ron.hashmap2.HashMap2.get HashableInst Eq2Inst m key = ok r) :
    r.map absV = s[absK key]? := by
  rw [get_refines heq hinv h]; exact hrel key

theorem Rel_insert [LawfulBEq K'] [LawfulHashable K'] {s : _root_.Std.HashMap K' V'}
    (heq : Eq2Spec Eq2Inst) (hinj : Function.Injective absK) (hinv : Inv HashableInst m)
    (hcap : 2 * m.slots.val.length ≤ Std.Usize.max) (hrel : Rel m s absK absV)
    {key : K} {value : V} {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.insert HashableInst Eq2Inst m key value = ok (old, m')) :
    Rel m' (s.insert (absK key) (absV value)) absK absV := by
  obtain ⟨-, -, hupd⟩ := insert_refines heq hinv hcap h
  intro k'
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
  by_cases hk : k' = key
  · subst hk; simp
  · have hne : ¬(absK key = absK k') := fun hc => hk (hinj hc).symm
    rw [if_neg hk, if_neg (by simpa using hne)]
    exact hrel k'

theorem Rel_remove [LawfulBEq K'] [LawfulHashable K'] {s : _root_.Std.HashMap K' V'}
    (heq : Eq2Spec Eq2Inst) (hinj : Function.Injective absK) (hinv : Inv HashableInst m)
    (hrel : Rel m s absK absV) {key : K} {old : Option V}
    {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.remove HashableInst Eq2Inst m key = ok (old, m')) :
    Rel m' (s.erase (absK key)) absK absV := by
  obtain ⟨-, -, hupd⟩ := remove_refines heq hinv h
  intro k'
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_erase]
  by_cases hk : k' = key
  · subst hk; simp
  · have hne : ¬(absK key = absK k') := fun hc => hk (hinj hc).symm
    rw [if_neg hk, if_neg (by simpa using hne)]
    exact hrel k'

end Bridge

end ConRon.Refine.HashMap2

/-! ## Axiom census

Nothing but Lean's own three axioms, on every statement: no `sorry`, no
assumption about `hash64`, nothing from the `Arc` model (DESIGN.md §3.2), and
in particular **both fuel obligations are discharged, not assumed** —
`probe`'s `fuel == 0` arm (from `Inv.fit`, through `probe_spec`) and
`repair`'s (from `RepairInv.stop`, through `repair_spec`). -/

/-- info: 'ConRon.Refine.HashMap2.insert_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.insert_refines

/-- info: 'ConRon.Refine.HashMap2.get_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.get_refines

/-- info: 'ConRon.Refine.HashMap2.contains_key_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.contains_key_refines

/-- info: 'ConRon.Refine.HashMap2.new_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.new_refines

/-- info: 'ConRon.Refine.HashMap2.with_capacity_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.with_capacity_refines

/-- info: 'ConRon.Refine.HashMap2.clear_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.clear_refines

/-- info: 'ConRon.Refine.HashMap2.clear_fit_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.clear_fit_refines

/-- info: 'ConRon.Refine.HashMap2.len_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.len_refines

/-- info: 'ConRon.Refine.HashMap2.is_empty_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.is_empty_refines

/-- info: 'ConRon.Refine.HashMap2.capacity_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.capacity_refines

/-- info: 'ConRon.Refine.HashMap2.dup_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.dup_spec

/-- info: 'ConRon.Refine.HashMap2.probe_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.probe_spec

/-- info: 'ConRon.Refine.HashMap2.remove_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.remove_refines

/-- info: 'ConRon.Refine.HashMap2.repair_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.repair_spec

/-- info: 'ConRon.Refine.HashMap2.Rel_remove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.Rel_remove

