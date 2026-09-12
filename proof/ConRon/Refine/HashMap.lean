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
on the key type.  The natural generalisation (and the one the `ExprC` keys of
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

theorem list_get_spec (heq : Eq2Spec Eq2Inst) {ls : ron.hashmap.AList K V} {k : K}
    {r : Option V} (h : ron.hashmap.list_get Eq2Inst ls k = ok r) :
    r = lookupK (alv ls) k := by
  induction ls using AList.recTail with
  | nil => rw [ron.hashmap.list_get.eq_def] at h; simp at h; simp [← h]
  | last ckey cval =>
    rw [ron.hashmap.list_get.eq_def] at h
    simp [Eq2Spec] at heq
    simp [heq] at h
    by_cases hk : ckey = k
    · rw [if_pos hk] at h
      simp [hk, ← Result.ok_injective h]
    · rw [if_neg hk] at h
      simp at h
      simp [hk, ← h]
  | cons ckey cval tl ih =>
    rw [ron.hashmap.list_get.eq_def] at h
    simp [Eq2Spec] at heq
    simp [heq] at h
    by_cases hk : ckey = k
    · rw [if_pos hk] at h
      simp [hk, ← Result.ok_injective h]
    · rw [if_neg hk] at h
      simp [hk, ih h]


theorem list_insert_spec (heq : Eq2Spec Eq2Inst) {ls : ron.hashmap.AList K V} {k : K} {v : V}
    {old : Option V} {ls' : ron.hashmap.AList K V}
    (h : ron.hashmap.list_insert Eq2Inst ls k v = ok (old, ls')) :
    old = lookupK (alv ls) k ∧
    (alv ls').map Prod.fst =
      (if old.isSome then (alv ls).map Prod.fst else (alv ls).map Prod.fst ++ [k]) ∧
    (∀ k', lookupK (alv ls') k' = if k' = k then some v else lookupK (alv ls) k') ∧
    (old = none → alv ls' = alv ls ++ [(k, v)]) := by
  simp [Eq2Spec] at heq
  induction ls using AList.recTail generalizing old ls' with
  | nil =>
    rw [ron.hashmap.list_insert.eq_def] at h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, by simp, ?_, by simp⟩
    intro k'; by_cases hk : k' = k <;> simp [hk, eq_comm (a := k)]
  | last ckey cval =>
    rw [ron.hashmap.list_insert.eq_def] at h
    simp [heq] at h
    by_cases hk : ckey = k
    · rw [if_pos hk] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [hk], by simp, ?_, by simp⟩
      intro k'
      by_cases hk' : k' = k <;> simp [hk, hk', eq_comm (a := k)]
    · rw [if_neg hk] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [hk], by simp, ?_, by simp⟩
      intro k'
      by_cases hk' : k' = k
      · simp [hk', hk]
      · simp [hk', Ne.symm hk']
  | cons ckey cval tl ih =>
    rw [ron.hashmap.list_insert.eq_def] at h
    simp [heq] at h
    by_cases hk : ckey = k
    · rw [if_pos hk] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [hk], by simp, ?_, by simp⟩
      intro k'
      by_cases hk' : k' = k <;> simp [hk, hk', eq_comm (a := k)]
    · rw [if_neg hk] at h
      simp at h
      obtain ⟨tl1, hrec, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4⟩ := ih hrec
      refine ⟨by simp [hk, h1], by simp [h2]; split <;> simp, ?_, ?_⟩
      · intro k'
        by_cases hk' : k' = k <;> by_cases hc : ckey = k' <;>
          simp [hk, hk', hc, h3 k'] <;> simp_all
      · intro hnone; simp [h4 hnone]


/-- Drop every entry with key `k`. -/
def eraseK : List (K × V) → K → List (K × V)
  | [], _ => []
  | (k', v) :: r, k => if k' = k then eraseK r k else (k', v) :: eraseK r k

@[local simp] theorem eraseK_nil (k : K) : eraseK ([] : List (K × V)) k = [] := rfl

@[local simp] theorem eraseK_cons (k' : K) (v : V) (r : List (K × V)) (k : K) :
    eraseK ((k', v) :: r) k = if k' = k then eraseK r k else (k', v) :: eraseK r k := rfl

theorem eraseK_sublist (l : List (K × V)) (k : K) : (eraseK l k).Sublist l := by
  induction l with
  | nil => simp
  | cons p r ih =>
    obtain ⟨k', v⟩ := p
    by_cases hk : k' = k
    · simp [hk]; exact ih.trans (List.sublist_cons_self _ _)
    · simp [hk]; exact ih

theorem eraseK_eq_self {l : List (K × V)} {k : K} (h : k ∉ l.map Prod.fst) :
    eraseK l k = l := by
  induction l with
  | nil => simp
  | cons p r ih =>
    obtain ⟨k', v⟩ := p
    rw [List.map_cons, List.mem_cons, not_or] at h
    simp [Ne.symm h.1, ih h.2]

theorem lookupK_eraseK (l : List (K × V)) (k k' : K) :
    lookupK (eraseK l k) k' = if k' = k then none else lookupK l k' := by
  induction l with
  | nil => simp
  | cons p r ih =>
    obtain ⟨k'', v⟩ := p
    by_cases hk : k'' = k
    · subst hk
      by_cases hk' : k' = k''
      · subst hk'; simp [ih]
      · simp [hk', ih, Ne.symm hk']
    · by_cases hk' : k' = k
      · subst hk'; simp [hk, ih]
      · simp [hk, hk', ih]

theorem length_eraseK_of_nodup {l : List (K × V)} {k : K} {v : V}
    (hnd : (l.map Prod.fst).Nodup) (hmem : lookupK l k = some v) :
    (eraseK l k).length + 1 = l.length := by
  induction l with
  | nil => simp at hmem
  | cons p r ih =>
    obtain ⟨k', v'⟩ := p
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hk : k' = k
    · subst hk
      rw [eraseK_cons, if_pos rfl, eraseK_eq_self hnd.1]
      simp
    · rw [eraseK_cons, if_neg hk]
      rw [lookupK_cons, if_neg hk] at hmem
      simp [ih hnd.2 hmem]

theorem list_remove_spec (heq : Eq2Spec Eq2Inst) {ls : ron.hashmap.AList K V} {k : K}
    {ls' : ron.hashmap.AList K V} {old : Option V}
    (hnd : ((alv ls).map Prod.fst).Nodup)
    (h : ron.hashmap.list_remove Eq2Inst ls k = ok (ls', old)) :
    old = lookupK (alv ls) k ∧ alv ls' = eraseK (alv ls) k := by
  simp [Eq2Spec] at heq
  induction ls using AList.recTail generalizing ls' old with
  | nil => rw [ron.hashmap.list_remove.eq_def] at h; simp at h; simp [← h.1, ← h.2]
  | last ckey cval =>
    rw [ron.hashmap.list_remove.eq_def] at h
    simp [heq] at h
    by_cases hk : ckey = k
    · rw [if_pos hk] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      subst hk
      simp
    · rw [if_neg hk] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hk]
  | cons ckey cval tl ih =>
    rw [ron.hashmap.list_remove.eq_def] at h
    simp [heq] at h
    rw [alv_cons, List.map_cons, List.nodup_cons] at hnd
    simp only [alvO_some] at hnd
    by_cases hk : ckey = k
    · rw [if_pos hk] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      subst hk
      simp [eraseK_eq_self hnd.1]
    · rw [if_neg hk] at h
      simp at h
      obtain ⟨rest, hrec, rfl⟩ := h
      obtain ⟨h1, h2⟩ := ih hnd.2 hrec
      simp [hk, h1, h2]


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

theorem get_refines (heq : Eq2Spec Eq2Inst) (hinv : Inv HashableInst m) {k : K}
    {r : Option V} (h : ron.hashmap.HashMap.get HashableInst Eq2Inst m k = ok r) :
    r = toFun m k := by
  rw [ron.hashmap.HashMap.get] at h
  split at h
  · -- The unallocated table of `new` (task #35): it binds nothing, and
    -- `bucket_index` is never reached (its `n - 1` would underflow).
    rename_i h0
    have hav : al_v m = [] := by simp [al_v, vec_len_eq_zero_iff.mp h0]
    rw [← Result.ok_injective h]; simp [toFun, hav]
  simp only [bind_eq_ok_iff] at h
  obtain ⟨hk, hhash, i2, hbi, a, hidx, hget⟩ := h
  have hb : bucketAt HashableInst (alloc.vec.Vec.len m.slots) k = ok i2 := by
    simp only [bucketAt, bind_eq_ok_iff]; exact ⟨hk, hhash, hbi⟩
  obtain ⟨hlt, rfl⟩ := vec_index_eq hidx
  rw [toFun_eq_bucket hinv hlt hb]
  exact list_get_spec heq hget


theorem contains_key_refines (heq : Eq2Spec Eq2Inst) (hinv : Inv HashableInst m) {k : K}
    {b : Bool} (h : ron.hashmap.HashMap.contains_key HashableInst Eq2Inst m k = ok b) :
    b = (toFun m k).isSome := by
  rw [ron.hashmap.HashMap.contains_key] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, hb⟩ := h
  rw [← get_refines heq hinv hget]
  cases o <;> simp at hb <;> simp [← hb]

/-- The support of the abstract map. -/
def support (m : ron.hashmap.HashMap K V) : Finset K := ((al_v m).map Prod.fst).toFinset

theorem mem_support_iff {k : K} :
    k ∈ support m ↔ (toFun m k).isSome := by
  rw [support, List.mem_toFinset, toFun]
  cases hl : lookupK (al_v m) k with
  | none => simp [lookupK_eq_none_iff.1 hl]
  | some v => simp only [Option.isSome_some, iff_true]
              exact List.mem_map.2 ⟨(k, v), lookupK_mem hl, rfl⟩

theorem card_support (hinv : Inv HashableInst m) : (support m).card = (al_v m).length := by
  rw [support, List.toFinset_card_of_nodup hinv.nodup, List.length_map]

theorem len_refines (hinv : Inv HashableInst m) {n : Std.Usize}
    (h : ron.hashmap.HashMap.len m = ok n) :
    n.val = (al_v m).length ∧ n.val = (support m).card := by
  rw [ron.hashmap.HashMap.len] at h
  rw [← Result.ok_injective h, hinv.entries, card_support hinv]
  exact ⟨rfl, rfl⟩

theorem toFun_eq_none_iff :
    (∀ k, toFun m k = none) ↔ al_v m = [] := by
  constructor
  · intro h
    rcases hl : al_v m with _ | ⟨x, r⟩
    · rfl
    · exfalso
      have := h x.1
      rw [toFun, hl, lookupK_cons, if_pos rfl] at this
      simp at this
  · intro h k; simp [toFun, h]

theorem is_empty_refines (hinv : Inv HashableInst m) {b : Bool}
    (h : ron.hashmap.HashMap.is_empty m = ok b) :
    b = true ↔ ∀ k, toFun m k = none := by
  rw [ron.hashmap.HashMap.is_empty] at h
  rw [← Result.ok_injective h, toFun_eq_none_iff]
  have hent := hinv.entries
  simp only [decide_eq_true_eq]
  constructor
  · intro hz
    have h0 : (al_v m).length = 0 := by rw [← hent, hz]; simp
    exact List.eq_nil_of_length_eq_zero h0
  · intro hz
    have h0 : m.num_entries.val = 0 := by rw [hent, hz]; simp
    scalar_tac


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
theorem pow2_at_least_spec (F : Nat) :
    ∀ (n cap fuel c : Std.Usize), fuel.val = F → (∃ e, cap.val = 2 ^ e) → 32 ≤ cap.val →
      ron.hashmap.pow2_at_least n cap fuel = ok c → (∃ e, c.val = 2 ^ e) ∧ 32 ≤ c.val := by
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro n cap fuel c hF h2 h32 h
    rw [ron.hashmap.pow2_at_least.eq_def] at h
    split at h
    · rw [← Result.ok_injective h]; exact ⟨h2, h32⟩
    · split at h
      · rw [← Result.ok_injective h]; exact ⟨h2, h32⟩
      · rename_i hfuel _
        simp only [bind_eq_ok_iff] at h
        obtain ⟨lim, _, h⟩ := h
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

theorem with_capacity_refines {c : Std.Usize} (h : ron.hashmap.HashMap.with_capacity K V c = ok m) :
    Inv HashableInst m ∧ al_v m = [] ∧ ∀ k, toFun m k = none := by
  rw [ron.hashmap.HashMap.with_capacity] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨cap, hcap, h⟩ := h
  obtain ⟨h2, h32⟩ := pow2_at_least_spec ron.hashmap.POW2_FUEL.val c ron.hashmap.MIN_CAPACITY
    ron.hashmap.POW2_FUEL cap rfl ⟨5, by simp [ron.hashmap.MIN_CAPACITY]⟩
    (by simp [ron.hashmap.MIN_CAPACITY]) hcap
  exact empty_table_inv h2 h32 h


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
theorem al_v_eq_nil_of_slots_nil {m : ron.hashmap.HashMap K V}
    (h : ∀ j, j < m.slots.val.length → m.slots.val[j]! = ron.hashmap.AList.Nil) :
    al_v m = [] := by
  rw [al_v, List.eq_nil_iff_forall_not_mem]
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_slots_flatten.1 hx
  rw [h j hj] at hxj; simp at hxj

omit [DecidableEq K] in
theorem clear_slots_spec (N : Nat) :
    ∀ (slots slots' : alloc.vec.Vec (ron.hashmap.AList K V)) (lo hi : Std.Usize),
      hi.val - lo.val = N →
      ron.hashmap.HashMap.clear_slots slots lo hi = ok slots' →
      slots'.val.length = slots.val.length ∧
      (∀ j, lo.val ≤ j → j < hi.val → slots'.val[j]! = ron.hashmap.AList.Nil) ∧
      (∀ j, (j < lo.val ∨ hi.val ≤ j) → slots'.val[j]! = slots.val[j]!) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro slots slots' lo hi hN h
    rw [ron.hashmap.HashMap.clear_slots.eq_def] at h
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

theorem clear_refines (hinv : Inv HashableInst m) {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.clear m = ok m') :
    Inv HashableInst m' ∧ al_v m' = [] ∧ ∀ k, toFun m' k = none := by
  rw [ron.hashmap.HashMap.clear] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨v, hv, hm⟩ := h
  obtain ⟨hlen, hnil, -⟩ := clear_slots_spec ((alloc.vec.Vec.len m.slots).val - 0)
    m.slots v 0#usize (alloc.vec.Vec.len m.slots) rfl hv
  have hslots : m'.slots = v := by rw [← Result.ok_injective hm]
  have hent : m'.num_entries = 0#usize := by rw [← Result.ok_injective hm]
  have hlen' : m'.slots.val.length = m.slots.val.length := by rw [hslots]; exact hlen
  have hnil' : ∀ j, j < m'.slots.val.length → m'.slots.val[j]! = ron.hashmap.AList.Nil := by
    intro j hj
    have hj' : j < m.slots.val.length := by rw [hlen'] at hj; exact hj
    rw [hslots]
    exact hnil j (by scalar_tac) (by rw [alloc.vec.Vec.len_val]; exact hj')
  have hav : al_v m' = [] := al_v_eq_nil_of_slots_nil hnil'
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hav, fun k => by simp [toFun, hav]⟩
  · rw [hlen']; exact hinv.pow2
  · rw [hlen']; exact hinv.min_cap
  · intro j i k hk _
    exfalso
    revert hk
    have : m'.slots.val[j]! = ron.hashmap.AList.Nil := by
      by_cases hj : j < m'.slots.val.length
      · exact hnil' j hj
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [this]; simp
  · rw [hav]; simp
  · rw [hav, hent]; simp


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

theorem insert_no_resize_spec (heq : Eq2Spec Eq2Inst) (hinv : Inv HashableInst m)
    {k : K} {v : V} {old : Option V} {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.insert_no_resize HashableInst Eq2Inst m k v = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m k ∧
    (∀ k', toFun m' k' = if k' = k then some v else toFun m k') ∧
    m'.slots.val.length = m.slots.val.length ∧
    m'.max_load = m.max_load ∧ m'.saturated = m.saturated ∧
    (al_v m').length = (al_v m).length + (if old.isSome then 0 else 1) ∧
    (old = none → (al_v m').Perm ((k, v) :: al_v m)) := by
  rw [ron.hashmap.HashMap.insert_no_resize] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨hw, hhash, i2, hbi, p, hidx, h⟩ := h
  obtain ⟨a, back⟩ := p
  replace h := bind_eq_ok_iff.mp h
  have hb : bucketAt HashableInst (alloc.vec.Vec.len m.slots) k = ok i2 := by
    simp only [bucketAt, bind_eq_ok_iff]; exact ⟨hw, hhash, hbi⟩
  obtain ⟨hlt, ha, hback⟩ := vec_index_mut_eq hidx
  subst ha; subst hback
  obtain ⟨q, hins, h⟩ := h
  obtain ⟨old0, a1⟩ := q
  obtain ⟨L1, L2, L3, L4⟩ := list_insert_spec heq hins
  have key : m'.slots.val = m.slots.val.set i2.val a1 ∧ m'.max_load = m.max_load ∧
      m'.saturated = m.saturated ∧ old = old0 ∧
      m'.num_entries.val = m.num_entries.val + (if old0.isSome then 0 else 1) := by
    cases old0 with
    | none =>
      obtain ⟨i3, hi3, hok⟩ := bind_eq_ok_iff.mp h
      have e := Result.ok_injective hok
      have eold : old = none := (congrArg Prod.fst e).symm
      have es : m'.slots = alloc.vec.Vec.set m.slots i2 a1 :=
        (congrArg (fun z => (Prod.snd z).slots) e).symm
      have ene : m'.num_entries = i3 := (congrArg (fun z => (Prod.snd z).num_entries) e).symm
      refine ⟨by rw [es]; exact alloc.vec.Vec.set_val_eq _ _ _,
        (congrArg (fun z => (Prod.snd z).max_load) e).symm,
        (congrArg (fun z => (Prod.snd z).saturated) e).symm, eold, ?_⟩
      rw [ene]; simpa using uscalar_add_eq hi3
    | some wold =>
      have e := Result.ok_injective h
      have es : m'.slots = alloc.vec.Vec.set m.slots i2 a1 :=
        (congrArg (fun z => (Prod.snd z).slots) e).symm
      have ene : m'.num_entries = m.num_entries :=
        (congrArg (fun z => (Prod.snd z).num_entries) e).symm
      exact ⟨by rw [es]; exact alloc.vec.Vec.set_val_eq _ _ _,
        (congrArg (fun z => (Prod.snd z).max_load) e).symm,
        (congrArg (fun z => (Prod.snd z).saturated) e).symm,
        (congrArg Prod.fst e).symm, by rw [ene]; simp⟩
  obtain ⟨hs, hml, hsat, hold, hent⟩ := key
  subst hold
  set A := alv m.slots.val[i2.val]! with hA
  set R := restOf m.slots.val i2.val with hR
  have hlen : m'.slots.val.length = m.slots.val.length := by rw [hs, List.length_set]
  have hlenv : alloc.vec.Vec.len m'.slots = alloc.vec.Vec.len m.slots := vec_len_congr hlen
  have PM : (al_v m).Perm (A ++ R) := al_v_perm_rest hlt
  have PM' : (al_v m').Perm (alv a1 ++ R) := by
    rw [al_v, hs]; exact al_v_set_perm_rest hlt a1
  have ND := hinv.nodup
  rw [(PM.map Prod.fst).nodup_iff, List.map_append, List.nodup_append] at ND
  obtain ⟨NDa, NDr, NDd⟩ := ND
  have hkR : k ∉ R.map Prod.fst := by
    intro hk
    obtain ⟨⟨k0, w⟩, hmem, hfst⟩ := List.mem_map.1 hk
    simp only at hfst
    subst hfst
    obtain ⟨j, hji, hj, hx⟩ := mem_restOf hmem
    exact hji (hinv.slot_inv j i2 k0 (List.mem_map.2 ⟨(k0, w), hx, rfl⟩) hb).symm
  have hRk : lookupK R k = none := lookupK_eq_none_of_not_mem hkR
  have hOld : old = toFun m k := by
    rw [toFun, lookupK_perm PM hinv.nodup, lookupK_append, hRk, L1]
    cases lookupK A k <;> simp
  have NDa1 : ((alv a1).map Prod.fst).Nodup ∧
      ∀ x ∈ (alv a1).map Prod.fst, ∀ y ∈ R.map Prod.fst, x ≠ y := by
    by_cases hos : old.isSome = true
    · rw [L2, if_pos hos]; exact ⟨NDa, NDd⟩
    · have hnone : old = none := by cases old <;> simp_all
      have hkA : k ∉ A.map Prod.fst := lookupK_eq_none_iff.1 (by rw [← L1, hnone])
      rw [L2, if_neg hos]
      refine ⟨?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨NDa, by simp, ?_⟩
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        exact fun hc => hkA (hc ▸ hx)
      · intro x hx y hy
        rcases List.mem_append.1 hx with hx | hx
        · exact NDd x hx y hy
        · simp only [List.mem_singleton] at hx
          subst hx
          exact fun hc => hkR (hc ▸ hy)
  have NDnew : ((al_v m').map Prod.fst).Nodup := by
    rw [(PM'.map Prod.fst).nodup_iff, List.map_append, List.nodup_append]
    exact ⟨NDa1.1, NDr, NDa1.2⟩
  have hlenA1 : (alv a1).length = A.length + (if old.isSome = true then 0 else 1) := by
    have hL := congrArg List.length L2
    simp only [List.length_map] at hL
    rw [hL]; split <;> simp
  have hlenAv : (al_v m').length = (al_v m).length + (if old.isSome = true then 0 else 1) := by
    rw [PM'.length_eq, PM.length_eq, List.length_append, List.length_append, hlenA1]
    split <;> omega
  have hToFun : ∀ k', toFun m' k' = if k' = k then some v else toFun m k' := by
    intro k'
    rw [toFun, toFun, lookupK_perm PM' NDnew, lookupK_perm PM hinv.nodup,
      lookupK_append, lookupK_append, L3 k']
    by_cases hk' : k' = k
    · subst hk'; simp [hRk]
    · simp [hk']
  refine ⟨⟨?_, ?_, ?_, NDnew, ?_⟩, hOld, hToFun, hlen, hml, hsat, hlenAv, ?_⟩
  · rw [hlen]; exact hinv.pow2
  · rw [hlen]; exact hinv.min_cap
  · intro j i k0 hk0 hbk0
    rw [hlenv] at hbk0
    by_cases hj : j = i2.val
    · subst hj
      rw [hs, getElem!_set_self _ hlt, L2] at hk0
      by_cases hos : old.isSome = true
      · rw [if_pos hos] at hk0
        exact hinv.slot_inv i2.val i k0 hk0 hbk0
      · rw [if_neg hos] at hk0
        rcases List.mem_append.1 hk0 with hk0 | hk0
        · exact hinv.slot_inv i2.val i k0 hk0 hbk0
        · simp only [List.mem_singleton] at hk0
          subst hk0
          exact congrArg Std.UScalar.val (Result.ok_injective (hbk0.symm.trans hb))
    · rw [hs, getElem!_set_ne _ hj] at hk0
      exact hinv.slot_inv j i k0 hk0 hbk0
  · rw [hent, hinv.entries, hlenAv]
  · intro hnone
    refine PM'.trans (?_ : (alv a1 ++ R).Perm ((k, v) :: al_v m))
    rw [L4 hnone, List.append_assoc]
    refine (List.perm_append_comm_assoc A [(k, v)] R).trans ?_
    simpa using (PM.symm.cons (k, v))


/-! ## Growth: `move_elements`, `try_resize` -/

theorem move_elements_from_list_spec (heq : Eq2Spec Eq2Inst) :
    ∀ (ls : ron.hashmap.AList K V) (nt nt' : ron.hashmap.HashMap K V),
      Inv HashableInst nt → ((alv ls).map Prod.fst).Nodup →
      (∀ x ∈ alv ls, x.1 ∉ (al_v nt).map Prod.fst) →
      ron.hashmap.HashMap.move_elements_from_list HashableInst Eq2Inst nt ls = ok nt' →
      Inv HashableInst nt' ∧ (al_v nt').Perm (alv ls ++ al_v nt) ∧
      nt'.slots.val.length = nt.slots.val.length ∧
      nt'.max_load = nt.max_load ∧ nt'.saturated = nt.saturated := by
  intro ls
  induction ls using AList.recTail with
  | nil =>
    intro nt nt' hinv _ _ h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    simp only at h
    rw [← Result.ok_injective h]
    exact ⟨hinv, by simp, rfl, rfl, rfl⟩
  | last k v =>
    intro nt nt' hinv hnd hdisj h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    simp only at h
    obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, nt1⟩ := q
    obtain ⟨hinv1, hold, htf, hlen1, hml1, hsat1, -, hperm1⟩ :=
      insert_no_resize_spec heq hinv hins
    have hknt : k ∉ (al_v nt).map Prod.fst := hdisj (k, v) (by simp)
    have honone : o = none := by
      rw [hold, toFun]; exact lookupK_eq_none_of_not_mem hknt
    have P1 : (al_v nt1).Perm ((k, v) :: al_v nt) := hperm1 honone
    rw [← Result.ok_injective h]
    exact ⟨hinv1, by simpa using P1, hlen1, hml1, hsat1⟩
  | cons k v tl ih =>
    intro nt nt' hinv hnd hdisj h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    simp only at h
    obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, nt1⟩ := q
    have h2 : ron.hashmap.HashMap.move_elements_from_list HashableInst Eq2Inst nt1 tl
        = ok nt' := h
    obtain ⟨hinv1, hold, htf, hlen1, hml1, hsat1, -, hperm1⟩ :=
      insert_no_resize_spec heq hinv hins
    rw [alv_cons, List.map_cons, List.nodup_cons] at hnd
    have hnd1 : k ∉ (alv tl).map Prod.fst := hnd.1
    have hknt : k ∉ (al_v nt).map Prod.fst := hdisj (k, v) (by simp)
    have honone : o = none := by
      rw [hold, toFun]; exact lookupK_eq_none_of_not_mem hknt
    have P1 : (al_v nt1).Perm ((k, v) :: al_v nt) := hperm1 honone
    have hdisj2 : ∀ x ∈ alv tl, x.1 ∉ (al_v nt1).map Prod.fst := by
      intro x hx hmem
      obtain ⟨⟨k0, w⟩, hmem', hfst⟩ := List.mem_map.1 hmem
      simp only at hfst
      have : (k0, w) ∈ (k, v) :: al_v nt := P1.mem_iff.1 hmem'
      rcases List.mem_cons.1 this with hc | hc
      · have hk0 : k0 = k := by simpa using congrArg Prod.fst hc
        have hx1 : x.1 = k := by rw [← hfst, hk0]
        exact hnd1 (hx1 ▸ (List.mem_map.2 ⟨x, hx, rfl⟩ : x.1 ∈ (alv tl).map Prod.fst))
      · exact hdisj x (by simp [hx]) (hfst ▸ List.mem_map.2 ⟨(k0, w), hc, rfl⟩)
    obtain ⟨hinv', P2, hlen2, hml2, hsat2⟩ := ih nt1 nt' hinv1 hnd.2 hdisj2 h2
    refine ⟨hinv', ?_, by rw [hlen2, hlen1], by rw [hml2, hml1], by rw [hsat2, hsat1]⟩
    refine P2.trans ?_
    refine (List.Perm.append_left (alv tl) P1).trans ?_
    exact List.perm_middle (a := (k, v)) (l₁ := alv tl) (l₂ := al_v nt)


theorem move_elements_spec (heq : Eq2Spec Eq2Inst) (N : Nat) :
    ∀ (nt nt' : ron.hashmap.HashMap K V)
      (slots slots' : alloc.vec.Vec (ron.hashmap.AList K V)) (lo hi : Std.Usize),
      hi.val - lo.val = N → hi.val ≤ slots.val.length → Inv HashableInst nt →
      ((slotsFlat slots.val lo.val (hi.val - lo.val)).map Prod.fst).Nodup →
      (∀ x ∈ slotsFlat slots.val lo.val (hi.val - lo.val),
          x.1 ∉ (al_v nt).map Prod.fst) →
      ron.hashmap.HashMap.move_elements HashableInst Eq2Inst nt slots lo hi
        = ok (nt', slots') →
      Inv HashableInst nt' ∧
      (al_v nt').Perm (slotsFlat slots.val lo.val (hi.val - lo.val) ++ al_v nt) ∧
      nt'.slots.val.length = nt.slots.val.length ∧
      nt'.max_load = nt.max_load ∧ nt'.saturated = nt.saturated ∧
      slots'.val.length = slots.val.length ∧
      (∀ j, (j < lo.val ∨ hi.val ≤ j) → slots'.val[j]! = slots.val[j]!) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro nt nt' slots slots' lo hi hN hbound hinv hnd hdisj h
    rw [ron.hashmap.HashMap.move_elements.eq_def] at h
    split at h
    · rename_i hgt
      have hlolt : lo.val < hi.val := by scalar_tac
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      have hnv : n.val = hi.val - lo.val := uscalar_sub_eq hn
      split at h
      · rename_i h1
        have hhi1 : hi.val = lo.val + 1 := by
          have : n.val = 1 := by scalar_tac
          omega
        obtain ⟨p, hidx, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨a, back⟩ := p
        obtain ⟨hlt, ha, hback⟩ := vec_index_mut_eq hidx
        have h2 : (do
            let nt1 ← ron.hashmap.HashMap.move_elements_from_list HashableInst Eq2Inst nt a
            ok (nt1, back ron.hashmap.AList.Nil)) = ok (nt', slots') := h
        obtain ⟨nt1, hmv, hok⟩ := bind_eq_ok_iff.mp h2
        have e := Result.ok_injective hok
        have ent : nt1 = nt' := congrArg Prod.fst e
        have esl : back ron.hashmap.AList.Nil = slots' := congrArg Prod.snd e
        subst ent
        have hflat : slotsFlat slots.val lo.val (hi.val - lo.val) = alv a := by
          rw [show hi.val - lo.val = 1 by omega, slotsFlat_one hlt, ha]
        rw [hflat] at hnd hdisj
        obtain ⟨hinv', hperm, hlen', hml', hsat'⟩ :=
          move_elements_from_list_spec heq a nt nt1 hinv hnd hdisj hmv
        refine ⟨hinv', by rw [hflat]; exact hperm, hlen', hml', hsat', ?_, ?_⟩
        · rw [← esl, hback, alloc.vec.Vec.set_val_eq, List.length_set]
        · intro j hj
          rw [← esl, hback, alloc.vec.Vec.set_val_eq]
          exact getElem!_set_ne _ (by omega)
      · rename_i h1
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
        have h2 : ron.hashmap.HashMap.move_elements HashableInst Eq2Inst nt1 slots1 mid hi
            = ok (nt', slots') := h
        have hsplit : slotsFlat slots.val lo.val (hi.val - lo.val)
            = slotsFlat slots.val lo.val (mid.val - lo.val)
              ++ slotsFlat slots.val mid.val (hi.val - mid.val) := by
          rw [show hi.val - lo.val = (mid.val - lo.val) + (hi.val - mid.val) by omega,
            slotsFlat_add, show lo.val + (mid.val - lo.val) = mid.val by omega]
        rw [hsplit, List.map_append, List.nodup_append] at hnd
        obtain ⟨ND1, ND2, NDd⟩ := hnd
        obtain ⟨hinv1, P1, hlenA, hmlA, hsatA, hlen1, f1⟩ :=
          ih (mid.val - lo.val) (by omega) nt nt1 slots slots1 lo mid rfl (by omega) hinv
            (by rw [show mid.val - lo.val = mid.val - lo.val from rfl]; exact ND1)
            (fun x hx => hdisj x (by rw [hsplit]; exact List.mem_append_left _ hx)) hrec1
        have hF2 : slotsFlat slots1.val mid.val (hi.val - mid.val)
            = slotsFlat slots.val mid.val (hi.val - mid.val) :=
          slotsFlat_congr hlen1 (fun j _ hj2 => f1 j (Or.inr (by omega)))
        have hdisj2 : ∀ x ∈ slotsFlat slots1.val mid.val (hi.val - mid.val),
            x.1 ∉ (al_v nt1).map Prod.fst := by
          intro x hx hmem
          rw [hF2] at hx
          obtain ⟨⟨k0, w⟩, hmem', hfst⟩ := List.mem_map.1 hmem
          simp only at hfst
          have hin : (k0, w) ∈ slotsFlat slots.val lo.val (mid.val - lo.val) ++ al_v nt :=
            P1.mem_iff.1 hmem'
          rcases List.mem_append.1 hin with hc | hc
          · exact NDd x.1 (hfst ▸ List.mem_map.2 ⟨(k0, w), hc, rfl⟩)
              x.1 (List.mem_map.2 ⟨x, hx, rfl⟩) rfl
          · exact hdisj x (by rw [hsplit]; exact List.mem_append_right _ hx)
              (hfst ▸ List.mem_map.2 ⟨(k0, w), hc, rfl⟩)
        obtain ⟨hinv', P2, hlenB, hmlB, hsatB, hlen2, f2⟩ :=
          ih (hi.val - mid.val) (by omega) nt1 nt' slots1 slots' mid hi rfl (by omega) hinv1
            (by rw [hF2]; exact ND2) hdisj2 h2
        refine ⟨hinv', ?_, by rw [hlenB, hlenA], by rw [hmlB, hmlA], by rw [hsatB, hsatA],
          by rw [hlen2, hlen1], ?_⟩
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
      refine ⟨hinv, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
      rw [show hi.val - lo.val = 0 by omega, slotsFlat_zero]
      simp


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

/-- `try_resize` is the one operation that needs the table to be *allocated*:
it doubles `slots.len()`, and `0` doubled is still `0`.  `insert` supplies
`hpos` from `ensure_slots_spec` (task #35). -/
theorem try_resize_spec (heq : Eq2Spec Eq2Inst) (hinv : Inv HashableInst m)
    (hpos : 0 < m.slots.val.length) {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.try_resize HashableInst Eq2Inst m = ok m') :
    Inv HashableInst m' ∧ ∀ k, toFun m' k = toFun m k := by
  rw [ron.hashmap.HashMap.try_resize] at h
  obtain ⟨lim, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨cap2, hcap2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨nt, hnt, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨q, hmv, hok⟩ := bind_eq_ok_iff.mp h
    obtain ⟨nt1, sl1⟩ := q
    have e := Result.ok_injective hok
    have eslots : m'.slots = nt1.slots :=
      (congrArg (fun z : ron.hashmap.HashMap K V => z.slots) e).symm
    have ene : m'.num_entries = m.num_entries :=
      (congrArg (fun z : ron.hashmap.HashMap K V => z.num_entries) e).symm
    have hcapv : (alloc.vec.Vec.len m.slots).val = m.slots.val.length :=
      alloc.vec.Vec.len_val _
    have hcap2v : cap2.val = m.slots.val.length * 2 := by
      rw [uscalar_mul_eq hcap2, hcapv, show (2#usize : Std.Usize).val = 2 by scalar_tac]
    obtain ⟨e0, he0⟩ := hinv.pow2 hpos
    obtain ⟨hinvnt, hnil, -⟩ := empty_table_inv (HashableInst := HashableInst)
      ⟨e0 + 1, by rw [hcap2v, he0]; ring⟩ (by rw [hcap2v]; have := hinv.min_cap hpos; omega) hnt
    have hflat : slotsFlat m.slots.val 0 ((alloc.vec.Vec.len m.slots).val - 0) = al_v m := by
      rw [hcapv, Nat.sub_zero, al_v]
      exact slotsFlat_all _
    obtain ⟨hinv1, P1, -, -, -, -, -⟩ :=
      move_elements_spec heq ((alloc.vec.Vec.len m.slots).val - (0#usize : Std.Usize).val)
        nt nt1 m.slots sl1 0#usize (alloc.vec.Vec.len m.slots) rfl (by rw [hcapv]) hinvnt
        (by rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat]; exact hinv.nodup)
        (by rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat, hnil]; simp) hmv
    rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat, hnil] at P1
    have Pfin : (al_v nt1).Perm (al_v m) := by simpa using P1
    have hav : al_v m' = al_v nt1 := al_v_congr eslots
    refine ⟨Inv_of_slots_eq hinv1 eslots ?_, ?_⟩
    · rw [ene, hinv.entries, hav, Pfin.length_eq]
    · intro k
      rw [toFun, toFun, hav, lookupK_perm Pfin hinv1.nodup]
  · have e := Result.ok_injective h
    have eslots : m'.slots = m.slots :=
      (congrArg (fun z : ron.hashmap.HashMap K V => z.slots) e).symm
    have ene : m'.num_entries = m.num_entries :=
      (congrArg (fun z : ron.hashmap.HashMap K V => z.num_entries) e).symm
    have hav : al_v m' = al_v m := al_v_congr eslots
    refine ⟨Inv_of_slots_eq hinv eslots (by rw [ene, hinv.entries, hav]), ?_⟩
    intro k; rw [toFun, toFun, hav]


theorem insert_refines (heq : Eq2Spec Eq2Inst) (hinv : Inv HashableInst m)
    {k : K} {v : V} {old : Option V} {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m k ∧
    toFun m' = Function.update (toFun m) k (some v) := by
  rw [ron.hashmap.HashMap.insert] at h
  -- `insert` allocates first (task #35): the table `insert_no_resize` writes
  -- into is `m0`, which denotes the same map as `m` and *is* allocated.
  obtain ⟨m0, hens, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hinv0, hpos0, hav0, -, -⟩ := ensure_slots_spec hinv hens
  have htf0 : toFun m0 = toFun m := by funext k'; rw [toFun, toFun, hav0]
  obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨old0, m1⟩ := q
  obtain ⟨hinv1, hold0, htf, hlen1, -, -, -, -⟩ := insert_no_resize_spec heq hinv0 hins
  have hold : old0 = toFun m k := by rw [hold0, htf0]
  have hpos1 : 0 < m1.slots.val.length := by rw [hlen1]; exact hpos0
  have hupd : toFun m1 = Function.update (toFun m) k (some v) := by
    funext k'; rw [htf k', htf0, Function.update_apply]
  have h2 : (if m1.num_entries > m1.max_load then
        (if m1.saturated then ok (old0, m1)
         else do
           let s2 ← ron.hashmap.HashMap.try_resize HashableInst Eq2Inst m1
           ok (old0, s2))
      else ok (old0, m1)) = ok (old, m') := h
  split at h2
  · split at h2
    · have e := Result.ok_injective h2
      have e1 : old = old0 := (congrArg Prod.fst e).symm
      have e2 : m' = m1 := (congrArg Prod.snd e).symm
      rw [e1, e2]
      exact ⟨hinv1, hold, hupd⟩
    · obtain ⟨m2, hres, hok⟩ := bind_eq_ok_iff.mp h2
      obtain ⟨hinv2, htf2⟩ := try_resize_spec heq hinv1 hpos1 hres
      have e := Result.ok_injective hok
      have e1 : old = old0 := (congrArg Prod.fst e).symm
      have e2 : m' = m2 := (congrArg Prod.snd e).symm
      rw [e1, e2]
      refine ⟨hinv2, hold, ?_⟩
      rw [← hupd]; funext k'; exact htf2 k'
  · have e := Result.ok_injective h2
    have e1 : old = old0 := (congrArg Prod.fst e).symm
    have e2 : m' = m1 := (congrArg Prod.snd e).symm
    rw [e1, e2]
    exact ⟨hinv1, hold, hupd⟩

/-! ## `remove` -/

theorem remove_refines (heq : Eq2Spec Eq2Inst) (hinv : Inv HashableInst m)
    {k : K} {old : Option V} {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.remove HashableInst Eq2Inst m k = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m k ∧
    toFun m' = Function.update (toFun m) k none := by
  rw [ron.hashmap.HashMap.remove] at h
  split at h
  · -- The unallocated table of `new` (task #35), exactly as in `get`.
    rename_i h0
    have hav : al_v m = [] := by simp [al_v, vec_len_eq_zero_iff.mp h0]
    have e := Result.ok_injective h
    have e1 : old = none := (congrArg Prod.fst e).symm
    have e2 : m' = m := (congrArg Prod.snd e).symm
    subst e1; subst e2
    refine ⟨hinv, by simp [toFun, hav], ?_⟩
    funext k'; simp [toFun, hav, Function.update_apply]
  simp only [bind_eq_ok_iff] at h
  obtain ⟨hw, hhash, i2, hbi, p, hidx, h⟩ := h
  obtain ⟨slot, back⟩ := p
  have hb : bucketAt HashableInst (alloc.vec.Vec.len m.slots) k = ok i2 := by
    simp only [bucketAt, bind_eq_ok_iff]; exact ⟨hw, hhash, hbi⟩
  obtain ⟨hlt, hslot, hback⟩ := vec_index_mut_eq hidx
  subst hslot; subst hback
  obtain ⟨q, hrem, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨rest, removed⟩ := q
  obtain ⟨R1, R2⟩ := list_remove_spec heq (bucket_nodup hinv hlt) hrem
  have key : m'.slots.val = m.slots.val.set i2.val rest ∧ old = removed ∧
      m'.num_entries.val = m.num_entries.val - (if removed.isSome then 1 else 0) := by
    cases removed with
    | none =>
      have e := Result.ok_injective h
      have es : m'.slots = alloc.vec.Vec.set m.slots i2 rest :=
        (congrArg (fun z => (Prod.snd z).slots) e).symm
      have ene : m'.num_entries = m.num_entries :=
        (congrArg (fun z => (Prod.snd z).num_entries) e).symm
      exact ⟨by rw [es]; exact alloc.vec.Vec.set_val_eq _ _ _,
        (congrArg Prod.fst e).symm, by rw [ene]; simp⟩
    | some w =>
      obtain ⟨i3, hi3, hok⟩ := bind_eq_ok_iff.mp h
      have e := Result.ok_injective hok
      have es : m'.slots = alloc.vec.Vec.set m.slots i2 rest :=
        (congrArg (fun z => (Prod.snd z).slots) e).symm
      have ene : m'.num_entries = i3 :=
        (congrArg (fun z => (Prod.snd z).num_entries) e).symm
      refine ⟨by rw [es]; exact alloc.vec.Vec.set_val_eq _ _ _,
        (congrArg Prod.fst e).symm, ?_⟩
      rw [ene, uscalar_sub_eq hi3, show (1#usize : Std.Usize).val = 1 by scalar_tac]
      simp
  obtain ⟨hs, hold, hent⟩ := key
  subst hold
  set A := alv m.slots.val[i2.val]! with hA
  set R := restOf m.slots.val i2.val with hR
  have hlen : m'.slots.val.length = m.slots.val.length := by rw [hs, List.length_set]
  have hlenv : alloc.vec.Vec.len m'.slots = alloc.vec.Vec.len m.slots := vec_len_congr hlen
  have PM : (al_v m).Perm (A ++ R) := al_v_perm_rest hlt
  have PM' : (al_v m').Perm (alv rest ++ R) := by
    rw [al_v, hs]; exact al_v_set_perm_rest hlt rest
  have ND := hinv.nodup
  rw [(PM.map Prod.fst).nodup_iff, List.map_append, List.nodup_append] at ND
  obtain ⟨NDa, NDr, NDd⟩ := ND
  have hkR : k ∉ R.map Prod.fst := by
    intro hk
    obtain ⟨⟨k0, w⟩, hmem, hfst⟩ := List.mem_map.1 hk
    simp only at hfst
    subst hfst
    obtain ⟨j, hji, hj, hx⟩ := mem_restOf hmem
    exact hji (hinv.slot_inv j i2 k0 (List.mem_map.2 ⟨(k0, w), hx, rfl⟩) hb).symm
  have hRk : lookupK R k = none := lookupK_eq_none_of_not_mem hkR
  have hsub : ((alv rest).map Prod.fst).Sublist (A.map Prod.fst) := by
    rw [R2]; exact (eraseK_sublist A k).map Prod.fst
  have NDnew : ((al_v m').map Prod.fst).Nodup := by
    rw [(PM'.map Prod.fst).nodup_iff, List.map_append, List.nodup_append]
    exact ⟨List.Nodup.sublist hsub NDa, NDr,
      fun x hx y hy => NDd x (hsub.subset hx) y hy⟩
  have hOld : old = toFun m k := by
    rw [toFun, lookupK_perm PM hinv.nodup, lookupK_append, hRk, R1]
    cases lookupK A k <;> simp
  have hlenA1 : (alv rest).length + (if old.isSome then 1 else 0) = A.length := by
    cases hr : old with
    | none =>
      rw [R2, eraseK_eq_self (lookupK_eq_none_iff.1 (by rw [← R1, hr]))]
      simp
    | some w =>
      rw [R2]
      simpa using length_eraseK_of_nodup NDa (by rw [← R1, hr])
  have hlenAv : (al_v m').length + (if old.isSome then 1 else 0) = (al_v m).length := by
    rw [PM'.length_eq, PM.length_eq, List.length_append, List.length_append, ← hlenA1]
    omega
  have hToFun : toFun m' = Function.update (toFun m) k none := by
    funext k'
    rw [Function.update_apply, toFun, toFun, lookupK_perm PM' NDnew,
      lookupK_perm PM hinv.nodup, lookupK_append, lookupK_append, R2, lookupK_eraseK]
    by_cases hk' : k' = k
    · subst hk'; simp [hRk]
    · simp [hk']
  refine ⟨⟨?_, ?_, ?_, NDnew, ?_⟩, hOld, hToFun⟩
  · rw [hlen]; exact hinv.pow2
  · rw [hlen]; exact hinv.min_cap
  · intro j i k0 hk0 hbk0
    rw [hlenv] at hbk0
    by_cases hj : j = i2.val
    · subst hj
      rw [hs, getElem!_set_self _ hlt] at hk0
      exact hinv.slot_inv i2.val i k0 (hsub.subset hk0) hbk0
    · rw [hs, getElem!_set_ne _ hj] at hk0
      exact hinv.slot_inv j i k0 hk0 hbk0
  · rw [hent, hinv.entries]; omega


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

/-- `m` represents `s` under the abstractions `absK`, `absV`. -/
def Rel (m : ron.hashmap.HashMap K V) (s : _root_.Std.HashMap K' V')
    (absK : K → K') (absV : V → V') : Prop :=
  ∀ k, (toFun m k).map absV = s[absK k]?

/-- The empty relation.  Compose with `new_refines`, `with_capacity_refines` or
`clear_refines`, whose third component is exactly this hypothesis. -/
theorem Rel_empty (h : ∀ k, toFun m k = none) :
    Rel m (∅ : _root_.Std.HashMap K' V') absK absV := by
  intro k; rw [h k, _root_.Std.HashMap.getElem?_empty]; rfl

theorem Rel_get {s : _root_.Std.HashMap K' V'} (heq : Eq2Spec Eq2Inst)
    (hinv : Inv HashableInst m) (hrel : Rel m s absK absV) {k : K} {r : Option V}
    (h : ron.hashmap.HashMap.get HashableInst Eq2Inst m k = ok r) :
    r.map absV = s[absK k]? := by
  rw [get_refines heq hinv h]; exact hrel k

theorem Rel_insert [LawfulBEq K'] [LawfulHashable K'] {s : _root_.Std.HashMap K' V'}
    (heq : Eq2Spec Eq2Inst) (hinj : Function.Injective absK) (hinv : Inv HashableInst m)
    (hrel : Rel m s absK absV) {k : K} {v : V} {old : Option V}
    {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m')) :
    Rel m' (s.insert (absK k) (absV v)) absK absV := by
  obtain ⟨-, -, hupd⟩ := insert_refines heq hinv h
  intro k'
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
  by_cases hk : k' = k
  · subst hk; simp
  · have hne : ¬(absK k = absK k') := fun hc => hk (hinj hc).symm
    rw [if_neg hk, if_neg (by simpa using hne)]
    exact hrel k'

theorem Rel_remove [LawfulBEq K'] [LawfulHashable K'] {s : _root_.Std.HashMap K' V'}
    (heq : Eq2Spec Eq2Inst) (hinj : Function.Injective absK) (hinv : Inv HashableInst m)
    (hrel : Rel m s absK absV) {k : K} {old : Option V} {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.remove HashableInst Eq2Inst m k = ok (old, m')) :
    Rel m' (s.erase (absK k)) absK absV := by
  obtain ⟨-, -, hupd⟩ := remove_refines heq hinv h
  intro k'
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_erase]
  by_cases hk : k' = k
  · subst hk; simp
  · have hne : ¬(absK k = absK k') := fun hc => hk (hinj hc).symm
    rw [if_neg hk, if_neg (by simpa using hne)]
    exact hrel k'

end Bridge

end ConRon.Refine.HashMap

/-! ## Axiom census

Nothing but Lean's own three axioms: no `sorry`, nothing from the `Arc` model
(DESIGN.md §3.2), no assumption about `hash64`. -/

/-- info: 'ConRon.Refine.HashMap.insert_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap.insert_refines

/-- info: 'ConRon.Refine.HashMap.get_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap.get_refines
