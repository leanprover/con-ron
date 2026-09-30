/-
The abstract-map specification of `ron::HashMap` (DESIGN.md §3.3, task #7's
"proposed proof spec", task #16), proved on the generated model
`ConRon.Generated.ron.hashmap.*`.

The development follows `vendor/aeneas/tests/lean/Hashmap/Properties.lean`
(the Aeneas tutorial's verified map, which the port was written to mirror) in
*strategy* — bucket invariant, the table as one association list, then the
abstract map — but not in *style*: the tutorial is written in Aeneas's
`⦃ ⦄` / `step` idiom, while DESIGN.md §3.5's refinement shape reasons forward
from a hypothesis `f x = ok y`, so every proof script here is new.

Two deliberate departures from the tutorial:

* **`toFun`, the abstract map, is defined without the hash function** — it is
  the lookup in `al_v m`, the flattened list of all buckets.  `Inv.slot_inv`
  is what ties it to the bucket a key's hash selects (`toFun_eq_bucket`).
  Consequently **no assumption whatsoever is made about `hash64`**: it may
  fail, and it may be constant.  That is what makes §3.2's "our hash differs
  from Lean's" verdict-neutral for the memo tables.
* **The bucket/rest decomposition is by permutation, not by position.**
  `al_v m ~ alv (bucket i) ++ restOf slots i` (`al_v_perm_rest`) and the same
  for the table with bucket `i` replaced (`al_v_set_perm_rest`); since keys are
  `Nodup`, `lookupK` is permutation-invariant, so one perm carries lookup,
  length and nodup at once.

**The unallocated table** (task #35).  `ron::HashMap::new` allocates no
buckets at all — the checker builds thousands of memo tables that never see an
insert — so `slots = []` is a reachable state and `Inv` has a case for it: the
two capacity fields `pow2`/`min_cap` are conditional on
`0 < m.slots.val.length`, `new_refines` goes through `unallocated_inv` instead
of `empty_table_inv`, `get_refines` and `remove_refines` each open with the
`slots.len() == 0` branch (`vec_len_eq_zero_iff`), and `insert_refines`
threads the new `ensure_slots_spec`, which is also where `try_resize_spec`'s
new `0 < length` hypothesis comes from.  Nothing about the *abstract* map
changed: an unallocated table denotes `∅`, which is what a `MIN_CAPACITY`
table of empty buckets denoted.

**The optional bucket tail** (task #41).  `AList.Cons`' third field is an
`Option (AList K V)`: the port stopped paying a heap block per entry to hold
the `Nil` that ended every chain (`ron/hashmap.rs`'s module note has the
measurement).  That makes `AList` a *nested* inductive, which Lean's
`induction` tactic declines, so this file carries its own three-case
induction principle `AList.recTail`, `alv` gained the one-entry case and a
companion `alvO` on tails (which is what keeps `alv_cons` stated for an
arbitrary tail, and with it every proof that rewrites with it), and the four
bucket walks induct with `using AList.recTail`.  Nothing else moved: the
abstract map, the invariant and every statement in this file are the same
text.  The same task's other change — `bucket_index` is `h & (n - 1)` where
it was `h % n` — needed **no** proof at all, because `bucketAt` is a black
box here (see its docstring).

The one semantic hypothesis is `Eq2Spec Eq2Inst` — `eq2` is decidable equality
on the key type.  The natural generalisation (and the one the `Expr` keys of
§3.2 will want) is "`eq2 a b = ok (decide (absK a = absK b))` for an
abstraction `absK`", i.e. `eq2` is exact modulo an abstraction; every proof
below goes through with `=` replaced by the kernel of `absK`, at the cost of
carrying a setoid instead of `DecidableEq K`.  The plain version is what the
`u64`-keyed memo tables need, so it is what is proved here.

Naming: the nine public entry points get `<fn>_refines` (`ConRon/Refine/
README.md`'s rule); the private Rust helpers get `<fn>_spec`.
-/
import ConRon.Generated

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine.HashMap

/-! ## Monadic plumbing -/

@[local simp] theorem bind_eq_ok_iff {α β : Type} {e : Result α} {f : α → Result β} {v : β} :
    ((do let x ← e; f x) = ok v) ↔ ∃ y, e = ok y ∧ f y = ok v := by
  constructor
  · cases e with
    | ret r => intro h; exact ⟨r, rfl, by simpa using h⟩
    | vis i k => intro h; simp at h
    | div => intro h; simp at h
  · rintro ⟨y, rfl, h⟩; simpa using h

section Scalars

variable {ty : UScalarTy}

theorem uscalar_add_eq {x y z : UScalar ty} (h : x + y = ok z) : z.val = x.val + y.val := by
  have := UScalar.add_equiv x y
  rw [h] at this; simpa using this.2.1

theorem uscalar_sub_eq {x y z : UScalar ty} (h : x - y = ok z) : z.val = x.val - y.val := by
  have := UScalar.sub_equiv x y
  rw [h] at this; simp at this; omega

theorem uscalar_mul_eq {x y z : UScalar ty} (h : x * y = ok z) : z.val = x.val * y.val := by
  have := UScalar.mul_equiv x y
  rw [show UScalar.mul x y = ok z from h] at this; simpa using this.2.1

theorem uscalar_div_eq {x y z : UScalar ty} (h : x / y = ok z) : z.val = x.val / y.val := by
  by_cases hy : y.val = 0
  · exfalso
    have hb : y.bv = 0#ty.numBits := by
      have h0 : y.bv.toNat = 0 := hy
      apply BitVec.toNat_injective
      simpa using h0
    rw [show x / y = UScalar.div x y from rfl, UScalar.div, if_neg (by simp [hb])] at h
    simp at h
  · obtain ⟨w, hw, hval, -⟩ := UScalar.div_bv_spec x hy
    rw [h] at hw
    rw [Result.ok_injective hw]; exact hval

end Scalars

variable {K V : Type} [DecidableEq K]
  {HashableInst : ron.hashmap.Hashable K} {Eq2Inst : ron.hashmap.Eq2 K}

/-! ## Association lists -/

/-- Lookup in an association list: the value of the *first* entry with key `k`. -/
def lookupK : List (K × V) → K → Option V
  | [], _ => none
  | (k', v) :: r, k => if k' = k then some v else lookupK r k

@[local simp] theorem lookupK_nil (k : K) : lookupK ([] : List (K × V)) k = none := rfl

@[local simp] theorem lookupK_cons (k' : K) (v : V) (r : List (K × V)) (k : K) :
    lookupK ((k', v) :: r) k = if k' = k then some v else lookupK r k := rfl

theorem lookupK_eq_none_iff {l : List (K × V)} {k : K} :
    lookupK l k = none ↔ k ∉ l.map Prod.fst := by
  induction l with
  | nil => simp
  | cons p r ih =>
    obtain ⟨k', v⟩ := p
    by_cases h : k' = k
    · simp [h]
    · simp [h, ih]; tauto

theorem lookupK_eq_none_of_not_mem {l : List (K × V)} {k : K} (h : k ∉ l.map Prod.fst) :
    lookupK l k = none := lookupK_eq_none_iff.2 h

theorem lookupK_mem {l : List (K × V)} {k : K} {v : V} (h : lookupK l k = some v) :
    (k, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p r ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hk : k' = k
    · subst hk; simp at h; simp [h]
    · simp [hk] at h; simp [ih h]

theorem lookupK_eq_some_of_mem {l : List (K × V)} {k : K} {v : V}
    (hnd : (l.map Prod.fst).Nodup) (h : (k, v) ∈ l) : lookupK l k = some v := by
  induction l with
  | nil => simp at h
  | cons p r ih =>
    obtain ⟨k', v'⟩ := p
    simp at hnd h
    rcases h with h | h
    · simp [h.1, h.2]
    · have hne : k' ≠ k := by
        rintro rfl
        exact hnd.1 v h
      simp [hne]; exact ih hnd.2 h

/-- Two association lists with the same entries for `k` agree on `k`. -/
theorem lookupK_congr {l L : List (K × V)} {k : K}
    (hndl : (l.map Prod.fst).Nodup)
    (hlL : ∀ x ∈ l, x ∈ L) (hLl : ∀ v, (k, v) ∈ L → (k, v) ∈ l) :
    lookupK L k = lookupK l k := by
  cases hL : lookupK L k with
  | none =>
    have hk := lookupK_eq_none_iff.1 hL
    refine (lookupK_eq_none_of_not_mem ?_).symm
    intro hmem
    obtain ⟨⟨k', v⟩, hmem', rfl⟩ := List.mem_map.1 hmem
    exact hk (List.mem_map_of_mem (f := Prod.fst) (hlL _ hmem'))
  | some v => exact (lookupK_eq_some_of_mem hndl (hLl v (lookupK_mem hL))).symm

theorem lookupK_append (l₁ l₂ : List (K × V)) (k : K) :
    lookupK (l₁ ++ l₂) k = (lookupK l₁ k).or (lookupK l₂ k) := by
  induction l₁ with
  | nil => simp
  | cons p r ih => obtain ⟨k', v⟩ := p; by_cases h : k' = k <;> simp [h, ih]

theorem lookupK_perm {l₁ l₂ : List (K × V)} (hp : l₁.Perm l₂)
    (hnd : (l₁.map Prod.fst).Nodup) (k : K) : lookupK l₁ k = lookupK l₂ k :=
  (lookupK_congr (l := l₁) (L := l₂) hnd
    (fun _ hx => hp.mem_iff.1 hx) (fun _ hx => hp.mem_iff.2 hx)).symm

/-! ## The model of a bucket and of the table -/

omit [DecidableEq K] in
instance : Inhabited (ron.hashmap.AList K V) := ⟨.Nil⟩

omit [DecidableEq K] in
/-- **The induction principle of a bucket** (task #41).  `AList.Cons`' tail is
an `Option (AList K V)` since the port stopped allocating a heap block per
entry to hold a `Nil` (`ron/hashmap.rs`'s module note), which makes `AList` a
*nested* inductive — and Lean's `induction` tactic declines those ("does not
support the type ... because it is a nested inductive type").  The recursion
below is the one the equation compiler does accept, and the three `list_*`
specs and `move_elements_from_list_spec` use it through `induction ... using`;
its three cases are exactly the three arms the generated code matches on. -/
theorem AList.recTail {motive : ron.hashmap.AList K V → Prop}
    (nil : motive .Nil)
    (last : ∀ k v, motive (.Cons k v none))
    (cons : ∀ k v tl, motive tl → motive (.Cons k v (some tl))) :
    ∀ l : ron.hashmap.AList K V, motive l
  | .Nil => nil
  | .Cons k v none => last k v
  | .Cons k v (some tl) => cons k v tl (AList.recTail nil last cons tl)

/-- A bucket as an association list. -/
def alv : ron.hashmap.AList K V → List (K × V)
  | .Cons k v none => [(k, v)]
  | .Cons k v (some tl) => (k, v) :: alv tl
  | .Nil => []

/-- A bucket *tail* as an association list: the missing tail is the empty one.
This is what keeps `alv_cons` stated for an arbitrary tail, and with it every
proof below that rewrites with it. -/
def alvO : Option (ron.hashmap.AList K V) → List (K × V)
  | none => []
  | some l => alv l

omit [DecidableEq K] in
@[local simp] theorem alv_nil : alv (ron.hashmap.AList.Nil : ron.hashmap.AList K V) = [] := rfl
omit [DecidableEq K] in
@[local simp] theorem alvO_none : alvO (none : Option (ron.hashmap.AList K V)) = [] := rfl
omit [DecidableEq K] in
@[local simp] theorem alvO_some (l : ron.hashmap.AList K V) : alvO (some l) = alv l := rfl
omit [DecidableEq K] in
@[local simp] theorem alv_cons (k : K) (v : V) (tl : Option (ron.hashmap.AList K V)) :
    alv (ron.hashmap.AList.Cons k v tl) = (k, v) :: alvO tl := by
  cases tl <;> rfl
omit [DecidableEq K] in
/-- The default bucket is the empty one: this is what `slots[j]!` gives outside
the range, which is *every* `j` on an unallocated table (task #35). -/
@[local simp] theorem alv_default : alv (default : ron.hashmap.AList K V) = [] := rfl
omit [DecidableEq K] in
/-- The whole table as one association list: the buckets, flattened. -/
def al_v (m : ron.hashmap.HashMap K V) : List (K × V) := (m.slots.val.map alv).flatten

/-- The bucket index `n`-slot table computes for `k`.  A plain function of the
key: the proofs never look inside it. -/
def bucketAt (HashableInst : ron.hashmap.Hashable K) (n : Std.Usize) (k : K) :
    Result Std.Usize := do
  let h ← HashableInst.hash64 k
  ron.hashmap.bucket_index h n

/-- The table invariant: the capacity is a power of two of at least
`MIN_CAPACITY` *or zero*, every key sits in the bucket its hash selects, keys
are pairwise distinct, and `num_entries` counts the entries.

The zero case is the **unallocated** table `ron::HashMap::new` returns since
task #35: `slots` is the empty `Vec` and the first `insert` allocates
(`ensure_slots`).  Hence the two capacity fields are conditional on
`0 < m.slots.val.length`, and the other three need no change — `slot_inv` is
vacuous when `slots` is empty (`m.slots.val[j]!` is then the default `Nil`),
`al_v m` is `[]`, and `num_entries` is `0`.  Only `try_resize_spec`, which
doubles the capacity, has to *know* the table is allocated; every other
consumer either preserves the length or is on the allocating path. -/
structure Inv (HashableInst : ron.hashmap.Hashable K) (m : ron.hashmap.HashMap K V) : Prop where
  pow2 : 0 < m.slots.val.length → ∃ e, m.slots.val.length = 2 ^ e
  min_cap : 0 < m.slots.val.length → 32 ≤ m.slots.val.length
  slot_inv : ∀ (j : Nat) (i : Std.Usize) (k : K),
      k ∈ (alv m.slots.val[j]!).map Prod.fst →
      bucketAt HashableInst (alloc.vec.Vec.len m.slots) k = ok i → i.val = j
  nodup : ((al_v m).map Prod.fst).Nodup
  entries : m.num_entries.val = (al_v m).length

/-- `eq2` decides equality on `K`.  The one semantic assumption of this file
(there is none on `hash64`). -/
def Eq2Spec (Eq2Inst : ron.hashmap.Eq2 K) : Prop :=
  ∀ a b : K, Eq2Inst.eq2 a b = ok (decide (a = b))

/-- **The abstract map**: the partial function the table denotes.  It mentions
neither the hash function nor the bucket structure — `Inv` is what ties the two
together (and is why no assumption on `hash64` is ever needed). -/
def toFun (m : ron.hashmap.HashMap K V) (k : K) : Option V := lookupK (al_v m) k

/-! ## The three bucket walks -/

/-! ## `Vec`, read forwards -/

omit [DecidableEq K] in
theorem vec_index_eq {α : Type} [Inhabited α] {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    i.val < v.val.length ∧ x = v.val[i.val]! := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · have hlt : i.val < v.val.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hi; simp at hi
    rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    exact ⟨hlt, by rw [← Result.ok_injective h, List.getElem!_of_getElem? hi]⟩

omit [DecidableEq K] in
theorem vec_index_mut_eq {α : Type} [Inhabited α] {v : alloc.vec.Vec α} {i : Std.Usize}
    {x : α} {f : α → alloc.vec.Vec α}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (x, f)) :
    i.val < v.val.length ∧ x = v.val[i.val]! ∧ f = alloc.vec.Vec.set v i := by
  rw [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨y, hy, hok⟩ := h
  simp only [Result.ok] at hok
  have hxy : y = x ∧ alloc.vec.Vec.set v i = f := by
    have := Result.ok_injective (α := α × (α → alloc.vec.Vec α)) hok
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨h1, h2⟩ := vec_index_eq (v := v) (i := i) (x := y) (by
    rw [alloc.vec.Vec.index_slice_index]; exact hy)
  exact ⟨h1, hxy.1 ▸ h2, hxy.2.symm⟩

omit [DecidableEq K] in
/-- A `Vec` is empty exactly when its `len` is `0`.  The `slots.len() == 0`
guards of `get`, `remove` and `ensure_slots` (task #35) test the left-hand
side; every proof below wants the right-hand one. -/
theorem vec_len_eq_zero_iff {α : Type} {v : alloc.vec.Vec α} :
    alloc.vec.Vec.len v = 0#usize ↔ v.val = [] := by
  constructor
  · intro h
    apply List.eq_nil_of_length_eq_zero
    have hv : (alloc.vec.Vec.len v).val = 0 := by rw [h]; rfl
    simpa using hv
  · intro h
    have hv : (alloc.vec.Vec.len v).val = 0 := by simp [h]
    scalar_tac

omit [DecidableEq K] in
theorem vec_push_eq {α : Type} {v v' : alloc.vec.Vec α} {x : α}
    (h : alloc.vec.Vec.push v x = ok v') : v'.val = v.val ++ [x] := by
  rw [alloc.vec.Vec.push] at h
  split at h
  · rw [← Result.ok_injective h]; simp
  · simp at h

/-! ## Ranges of buckets -/

/-- The entries of the buckets `[lo, lo + n)`. -/
def slotsFlat (s : List (ron.hashmap.AList K V)) (lo n : Nat) : List (K × V) :=
  (((s.drop lo).take n).map alv).flatten

omit [DecidableEq K] in
@[local simp] theorem slotsFlat_zero (s : List (ron.hashmap.AList K V)) (lo : Nat) :
    slotsFlat s lo 0 = [] := by simp [slotsFlat]

omit [DecidableEq K] in
theorem slotsFlat_all (s : List (ron.hashmap.AList K V)) :
    slotsFlat s 0 s.length = (s.map alv).flatten := by simp [slotsFlat]

omit [DecidableEq K] in
theorem slotsFlat_add (s : List (ron.hashmap.AList K V)) (lo n₁ n₂ : Nat) :
    slotsFlat s lo (n₁ + n₂) = slotsFlat s lo n₁ ++ slotsFlat s (lo + n₁) n₂ := by
  simp [slotsFlat, List.take_add, List.drop_drop]

omit [DecidableEq K] in
theorem slotsFlat_one {s : List (ron.hashmap.AList K V)} {lo : Nat} (h : lo < s.length) :
    slotsFlat s lo 1 = alv s[lo]! := by
  have : (s.drop lo).take 1 = [s[lo]!] := by
    simp [List.take_one, List.head?_drop, List.getElem?_eq_getElem h,
      List.getElem!_of_getElem? (List.getElem?_eq_getElem h)]
  simp [slotsFlat, this]

omit [DecidableEq K] in
theorem slotsFlat_congr {s s' : List (ron.hashmap.AList K V)} {lo n : Nat}
    (hlen : s'.length = s.length)
    (h : ∀ j, lo ≤ j → j < lo + n → s'[j]! = s[j]!) :
    slotsFlat s' lo n = slotsFlat s lo n := by
  have : (s'.drop lo).take n = (s.drop lo).take n := by
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
  simp [slotsFlat, this]

omit [DecidableEq K] in
theorem mem_slots_flatten {s : List (ron.hashmap.AList K V)} {x : K × V} :
    x ∈ (s.map alv).flatten ↔ ∃ j, ∃ _ : j < s.length, x ∈ alv s[j]! := by
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hx⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
    exact ⟨j, hj, by rwa [List.getElem!_of_getElem? (List.getElem?_eq_getElem hj)]⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨alv s[j]!, List.mem_map.2 ⟨s[j], List.getElem_mem hj,
      by rw [List.getElem!_of_getElem? (List.getElem?_eq_getElem hj)]⟩, hx⟩

omit [DecidableEq K] in
theorem slot_sublist_flatten {s : List (ron.hashmap.AList K V)} {j : Nat} (hj : j < s.length) :
    (alv s[j]!).Sublist (s.map alv).flatten :=
  List.sublist_flatten_of_mem (List.mem_map.2 ⟨s[j], List.getElem_mem hj,
    by rw [List.getElem!_of_getElem? (List.getElem?_eq_getElem hj)]⟩)

/-! ## The abstract map and the buckets -/

variable {m : ron.hashmap.HashMap K V}

omit [DecidableEq K] in
theorem bucket_nodup (hinv : Inv HashableInst m) {j : Nat} (hj : j < m.slots.val.length) :
    ((alv m.slots.val[j]!).map Prod.fst).Nodup :=
  List.Nodup.sublist ((slot_sublist_flatten hj).map Prod.fst) hinv.nodup

/-- Under `Inv`, the abstract map is the lookup in the bucket the hash selects.
This is the only place the bucket structure and `toFun` meet. -/
theorem toFun_eq_bucket (hinv : Inv HashableInst m) {k : K} {i : Std.Usize}
    (hi : i.val < m.slots.val.length)
    (hb : bucketAt HashableInst (alloc.vec.Vec.len m.slots) k = ok i) :
    toFun m k = lookupK (alv m.slots.val[i.val]!) k := by
  rw [toFun, al_v]
  refine lookupK_congr (bucket_nodup hinv hi) (fun x hx => (slot_sublist_flatten hi).subset hx) ?_
  intro v hv
  obtain ⟨j, hj, hx⟩ := mem_slots_flatten.1 hv
  have hij : i.val = j := hinv.slot_inv j i k (List.mem_map.2 ⟨(k, v), hx, rfl⟩) hb
  rw [hij]; exact hx

/-! ## `get`, `contains_key`, `len`, `is_empty` -/

/-! ## Construction: `allocate_slots`, `new`, `with_capacity` -/

omit [DecidableEq K] in
@[local simp] theorem getElem!_replicate_nil (n j : Nat) :
    (List.replicate n (ron.hashmap.AList.Nil : ron.hashmap.AList K V))[j]! = ron.hashmap.AList.Nil := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

omit [DecidableEq K] in
theorem allocate_slots_spec (N : Nat) :
    ∀ (slots slots' : alloc.vec.Vec (ron.hashmap.AList K V)) (n : Std.Usize), n.val = N →
      ron.hashmap.HashMap.allocate_slots slots n = ok slots' →
      slots'.val = slots.val ++ List.replicate n.val ron.hashmap.AList.Nil := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro slots slots' n hN h
    rw [ron.hashmap.HashMap.allocate_slots.eq_def] at h
    split at h
    · rename_i h0
      rw [← Result.ok_injective h, show n.val = 0 by scalar_tac]; simp
    · split at h
      · rename_i h1
        rw [vec_push_eq h, show n.val = 1 by scalar_tac]; simp
      · rename_i h0 h1
        have hn2 : 2 ≤ n.val := by scalar_tac
        simp only [bind_eq_ok_iff] at h
        obtain ⟨half, hhalf, slots1, hs1, i, hi, h2⟩ := h
        have hhv : half.val = n.val / 2 := by
          rw [uscalar_div_eq hhalf]; rfl
        have hiv : i.val = n.val - half.val := uscalar_sub_eq hi
        have e1 := ih half.val (by omega) slots slots1 half rfl hs1
        have e2 := ih i.val (by omega) slots1 slots' i rfl h2
        rw [e2, e1, List.append_assoc, ← List.replicate_add]
        congr 2
        omega

omit [DecidableEq K] in
theorem new_with_capacity_pow2_spec {c : Std.Usize} {m : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.new_with_capacity_pow2 K V c = ok m) :
    m.slots.val = List.replicate c.val ron.hashmap.AList.Nil ∧ m.num_entries = 0#usize ∧
    m.saturated = false := by
  rw [ron.hashmap.HashMap.new_with_capacity_pow2] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨slots, hs, i, _, hm⟩ := h
  have := allocate_slots_spec c.val _ _ c rfl hs
  rw [← Result.ok_injective hm]
  refine ⟨?_, rfl, rfl⟩
  simpa [alloc.vec.Vec.with_capacity] using this

theorem empty_table_inv {c : Std.Usize} {m : ron.hashmap.HashMap K V}
    (hc2 : ∃ e, c.val = 2 ^ e) (hc32 : 32 ≤ c.val)
    (h : ron.hashmap.HashMap.new_with_capacity_pow2 K V c = ok m) :
    Inv HashableInst m ∧ al_v m = [] ∧ ∀ k, toFun m k = none := by
  obtain ⟨hs, hn, -⟩ := new_with_capacity_pow2_spec h
  have hav : al_v m = [] := by simp [al_v, hs]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hav, fun k => by simp [toFun, hav]⟩
  · intro _; rw [hs]; simpa using hc2
  · intro _; rw [hs]; simpa using hc32
  · intro j i k hk _
    rw [hs, getElem!_replicate_nil] at hk; simp at hk
  · rw [hav]; simp
  · rw [hav, hn]; simp

/-- An unallocated table — `slots = []` — satisfies `Inv`, and denotes `∅`.
This is `new`'s table since task #35 (the module note of `ron/hashmap.rs`):
`pow2` and `min_cap` are the two fields the empty capacity needs the
`0 < length` guard for, and the other three hold outright. -/
theorem unallocated_inv (hs : m.slots.val = []) (hn : m.num_entries.val = 0) :
    Inv HashableInst m ∧ al_v m = [] ∧ ∀ k, toFun m k = none := by
  have hav : al_v m = [] := by simp [al_v, hs]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hav, fun k => by simp [toFun, hav]⟩
  · intro hpos; rw [hs] at hpos; simp at hpos
  · intro hpos; rw [hs] at hpos; simp at hpos
  · intro j i k hk _
    rw [hs] at hk; simp at hk
  · rw [hav]; simp
  · rw [hav, hn]; simp

theorem new_refines (h : ron.hashmap.HashMap.new K V = ok m) :
    Inv HashableInst m ∧ al_v m = [] ∧ ∀ k, toFun m k = none := by
  rw [ron.hashmap.HashMap.new] at h
  have hm := Result.ok_injective h
  refine unallocated_inv (HashableInst := HashableInst) ?_ ?_
  · rw [← hm]; rfl
  · rw [← hm]; rfl

omit [DecidableEq K] in
/-- `ensure_slots` gives an unallocated table its buckets and leaves an
allocated one alone; either way the abstract map, the entry count and the
`saturated` flag are untouched, and the result *is* allocated — which is the
hypothesis `try_resize_spec` needs. -/
theorem ensure_slots_spec (hinv : Inv HashableInst m) {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.ensure_slots m = ok m') :
    Inv HashableInst m' ∧ 0 < m'.slots.val.length ∧ al_v m' = al_v m ∧
      m'.num_entries = m.num_entries ∧ m'.saturated = m.saturated := by
  rw [ron.hashmap.HashMap.ensure_slots] at h
  split at h
  · -- The table had no buckets: it is `∅`, and the fresh table is `∅` too.
    rename_i h0
    have hs : m.slots.val = [] := vec_len_eq_zero_iff.mp h0
    have hav : al_v m = [] := by simp [al_v, hs]
    have hn : m.num_entries.val = 0 := by rw [hinv.entries, hav]; simp
    obtain ⟨t, ht, hok⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hts, htn, -⟩ := new_with_capacity_pow2_spec ht
    have hm := Result.ok_injective hok
    have hslots : m'.slots = t.slots := by rw [← hm]
    have hent : m'.num_entries = m.num_entries := by rw [← hm]
    have hsat : m'.saturated = m.saturated := by rw [← hm]
    have hlen : m'.slots.val.length = 32 := by
      rw [hslots, hts]; simp [ron.hashmap.MIN_CAPACITY]
    have hav' : al_v m' = [] := by
      rw [al_v, hslots, hts]; simp
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by omega, by rw [hav, hav'], hent, hsat⟩
    · intro _; exact ⟨5, by simp [hlen]⟩
    · intro _; omega
    · intro j i k hk _
      rw [hslots, hts, getElem!_replicate_nil] at hk; simp at hk
    · rw [hav']; simp
    · rw [hav', hent, hn]; simp
  · -- Already allocated: nothing moves.
    rename_i h0
    have hm := Result.ok_injective h
    subst hm
    have hpos : 0 < m.slots.val.length := by
      rcases Nat.eq_zero_or_pos m.slots.val.length with hz | hp
      · exact absurd (vec_len_eq_zero_iff.mpr (List.eq_nil_of_length_eq_zero hz)) h0
      · exact hp
    exact ⟨hinv, hpos, rfl, rfl, rfl⟩

omit [DecidableEq K] in
/-! ## `clear` -/

omit [DecidableEq K] in
theorem getElem!_set_self {α : Type} [Inhabited α] {l : List α} {i : Nat} (a : α)
    (h : i < l.length) : (l.set i a)[i]! = a := by
  rw [List.getElem!_of_getElem? (List.getElem?_set_self h)]

omit [DecidableEq K] in
theorem getElem!_set_ne {α : Type} [Inhabited α] {l : List α} {i j : Nat} (a : α)
    (h : j ≠ i) : (l.set i a)[j]! = l[j]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.getElem?_set_ne (Ne.symm h)]

omit [DecidableEq K] in
/-! ## The entries of one bucket against all the others -/

omit [DecidableEq K] in
theorem flatten_set_perm {α : Type} :
    ∀ (L : List (List α)) (i : Nat), i < L.length →
      ∀ (b : List α), ((L.set i b).flatten).Perm (b ++ (L.set i []).flatten) := by
  intro L
  induction L with
  | nil => intro i hi; simp at hi
  | cons x r ih =>
    intro i hi b
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.set_cons_succ, List.flatten_cons]
      refine (List.Perm.append_left x (ih i (by simpa using hi) b)).trans ?_
      exact List.perm_append_comm_assoc x b _

omit [DecidableEq K] in
theorem flatten_perm_self {α : Type} (L : List (List α)) (i : Nat) (hi : i < L.length) :
    (L.flatten).Perm (L[i]! ++ (L.set i []).flatten) := by
  have h := flatten_set_perm L i hi L[i]
  rw [List.set_getElem_self hi] at h
  rwa [List.getElem!_of_getElem? (List.getElem?_eq_getElem hi)]

omit [DecidableEq K] in
theorem mem_flatten_set_nil {α : Type} {L : List (List α)} {i : Nat} {x : α}
    (h : x ∈ (L.set i []).flatten) : ∃ j, ∃ hj : j < L.length, j ≠ i ∧ x ∈ L[j] := by
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.1 h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hl
  rw [List.length_set] at hj
  by_cases hji : j = i
  · subst hji; rw [List.getElem_set_self] at hx; simp at hx
  · exact ⟨j, hj, hji, by rwa [List.getElem_set_ne (Ne.symm hji)] at hx⟩

omit [DecidableEq K] in
@[local simp] theorem getElem!_map_alv {s : List (ron.hashmap.AList K V)} {j : Nat}
    (hj : j < s.length) : (s.map alv)[j]! = alv s[j]! := by
  rw [List.getElem!_of_getElem? (l := s.map alv)
        (by rw [List.getElem?_map, List.getElem?_eq_getElem hj]; rfl),
      List.getElem!_of_getElem? (List.getElem?_eq_getElem hj)]

/-- The entries of every bucket of `s` other than `i`. -/
def restOf (s : List (ron.hashmap.AList K V)) (i : Nat) : List (K × V) :=
  ((s.map alv).set i []).flatten

omit [DecidableEq K] in
theorem al_v_perm_rest {s : List (ron.hashmap.AList K V)} {i : Nat} (hi : i < s.length) :
    ((s.map alv).flatten).Perm (alv s[i]! ++ restOf s i) := by
  have h := flatten_perm_self (s.map alv) i (by simpa using hi)
  rwa [getElem!_map_alv hi] at h

omit [DecidableEq K] in
theorem al_v_set_perm_rest {s : List (ron.hashmap.AList K V)} {i : Nat} (hi : i < s.length)
    (b : ron.hashmap.AList K V) :
    (((s.set i b).map alv).flatten).Perm (alv b ++ restOf s i) := by
  rw [List.map_set]
  exact flatten_set_perm (s.map alv) i (by simpa using hi) (alv b)

omit [DecidableEq K] in
theorem mem_restOf {s : List (ron.hashmap.AList K V)} {i : Nat} {x : K × V}
    (h : x ∈ restOf s i) : ∃ j, j ≠ i ∧ ∃ _ : j < s.length, x ∈ alv s[j]! := by
  obtain ⟨j, hj, hji, hx⟩ := mem_flatten_set_nil h
  rw [List.length_map] at hj
  rw [List.getElem_map] at hx
  exact ⟨j, hji, hj, by rwa [List.getElem!_of_getElem? (List.getElem?_eq_getElem hj)]⟩

omit [DecidableEq K] in
theorem vec_len_congr {α : Type} {v w : alloc.vec.Vec α}
    (h : v.val.length = w.val.length) :
    alloc.vec.Vec.len v = alloc.vec.Vec.len w := by
  have h1 := alloc.vec.Vec.len_val v
  have h2 := alloc.vec.Vec.len_val w
  scalar_tac

/-! ## `insert` -/

/-! ## Growth: `move_elements`, `try_resize` -/

omit [DecidableEq K] in
theorem al_v_congr {m₁ m₂ : ron.hashmap.HashMap K V} (h : m₁.slots = m₂.slots) :
    al_v m₁ = al_v m₂ := by rw [al_v, al_v, h]

omit [DecidableEq K] in
theorem Inv_of_slots_eq {m₁ m₂ : ron.hashmap.HashMap K V} (h₁ : Inv HashableInst m₁)
    (hs : m₂.slots = m₁.slots) (he : m₂.num_entries.val = (al_v m₂).length) :
    Inv HashableInst m₂ where
  pow2 := by rw [hs]; exact h₁.pow2
  min_cap := by rw [hs]; exact h₁.min_cap
  slot_inv := by rw [hs]; exact h₁.slot_inv
  nodup := by rw [al_v_congr hs]; exact h₁.nodup
  entries := he

/-! ## `remove` -/

/-! ## `dup`, the pin loop's pre-attempt snapshot (task #67)

`CheckerOps.orElse` (`ConLeche/Kernel/CheckerBase.lean:36-53`) resumes its
error arm from the state the failed attempt *started* in — `k (some e) s`, not
the `s'` the attempt left behind — so the memo entries a failed Nat-op pin
attempt wrote are discarded with it.  con-leche gets that for free, `s` being a
value; the port threads one `&mut CState`, so
`kernel::checker::check_div_mod_pin_loop` restores from a snapshot instead, and
a snapshot of a memo table is `ron::HashMap::dup`: the three scalar fields
carried over and `slots` rebuilt bucket by bucket (`dup_slots`, which halves
its range exactly as `allocate_slots` and `clear_slots` do) with `dup_alist`
under the one-method `Dup` dictionary.

**In the model that copy is the identity.**  Every type the port instantiates
`Dup` at copies by a pointer bump (`kernel::name::dup` and friends, whose `P`
field the abstraction does not see — DESIGN.md §3.2) or by rebuilding a `Vec`
element by element (`env::levels_copy`), and each of those is already proved to
return its argument unchanged.  So rather than transport `Inv`, `toFun`,
`al_v`, `KeysOk` and the `Std.HashMap` bridge one at a time, `dup_spec` proves
the one fact that gives all of them at once: `dup m = ok m'` implies `m' = m`.
`DupId` is the hypothesis it runs on, discharged per dictionary in
`Refine/State.lean`. -/

section Dup

/-- **The hypothesis on a `Dup` dictionary**: `dup2` returns its argument *in
the model*.  Forward, as DESIGN.md §3.5 asks (`dup2` may fail; when it returns,
it returns a copy indistinguishable from the original).  `Refine/State.lean`
discharges it for the nine dictionaries `cached::state_c::dup` uses. -/
def DupId {α : Type} (DupInst : ron.hashmap.Dup α) : Prop :=
  ∀ a b : α, DupInst.dup2 a = ok b → b = a

variable {DupK : ron.hashmap.Dup K} {DupV : ron.hashmap.Dup V}

omit [DecidableEq K] in
/-- The one-element window a `Vec` walk copies at its base case. -/
theorem take_one_drop {α : Type} [Inhabited α] {s : List α} {lo : Nat}
    (h : lo < s.length) : (s.drop lo).take 1 = [s[lo]!] := by
  simp [List.take_one, List.head?_drop, List.getElem?_eq_getElem h,
    List.getElem!_of_getElem? (List.getElem?_eq_getElem h)]

end Dup

/-! ## The bridge to `Std.HashMap`

This is what the memo proofs of the checker will use: the port's table
`m` stands for a `Std.HashMap` `s` over abstracted keys and values.  The
`absK`-injectivity hypothesis is what lets a *distinct* port key stay a
distinct `Std.HashMap` key; `LawfulBEq K'` turns `Std.HashMap`'s `==` into
equality.  (Injectivity is only ever needed on the keys actually in play; a
`Set.InjOn` version is the natural generalisation and is a mechanical
weakening of the proofs below.) -/

section Bridge

variable {K' V' : Type} [BEq K'] [Hashable K'] {absK : K → K'} {absV : V → V'}

end Bridge

end ConRon.Refine.HashMap
