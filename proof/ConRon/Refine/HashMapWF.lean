/-
Task #16's deferred `Eq2` generalisation, written for its first client (task
#46's `ConRon/Refine/State.lean`, the fourteen memo tables of
`cached::state_c::CState`).

`Refine/HashMap.lean` proves the abstract-map specification of
`ron::HashMap` from one semantic hypothesis,

    Eq2Spec Eq2Inst := ∀ a b, Eq2Inst.eq2 a b = ok (decide (a = b)),

and its own log entry (DESIGN.md, task #16, "The `Eq2` hypothesis, and its
generalisation") defers the generalisation to the first client.  This file is
it.  `Eq2Spec` is unusable by the real clients — whose keys are the port's
`Name`/`Level`/`Expr` and tuples thereof — for two independent reasons:

* it asserts that `beq` **cannot fail** (`eq2 a b` *is* an `ok`), i.e.
  totality, which DESIGN.md §3.5's forward style ("every lemma reasons from
  `f x = ok y`") never proves for any function of the port;
* it asserts exactness for **all** keys, while the port's `beq` is proved
  exact only for *well-formed* ones — `ConRon.Refine.Expr.beq_refines` needs
  `ExprWF a → ExprWF b`, and it is `absExpr_injective`, itself conditional on
  `ExprWF`, that turns its `decide (absExpr a = absExpr b)` into
  `decide (a = b)`.

So the right hypothesis is the **forward, key-restricted** one,
`Eq2Fwd Eq2Inst P`: *if* `eq2 a b` returns, and *if* both keys satisfy `P`,
then it returns the truth value of `a = b`.  Nothing else weakens: every
conclusion below is the one `HashMap.lean` proves, plus — on the operations
that build a new table — `KeysOk P`, i.e. "every key the table holds satisfies
`P`", which is what threads the restriction through a sequence of inserts.

The same restriction reaches the `Std.HashMap` bridge, and there it is not
merely convenient: `Rel m s absK absV := ∀ k, (toFun m k).map absV = s[absK k]?`
is *false* after the first insert for the clients' abstractions, because
`absK` is injective only on well-formed keys, so a non-well-formed `k'` with
`absK k' = absK k` has `toFun m' k' = none` while `s'[absK k']?` is `some`.
Hence `RelOn P`, which constrains only the `P`-keys, and `Rel_insert_wf` asks
for injectivity *on `P`* instead of `Function.Injective absK`.

`remove`/`contains_key`/`len`/`is_empty`/`clear`/`new`/`with_capacity` get no
`_wf` twin: the first two are the only ones that mention `Eq2Inst` at all and
no client calls them (the memo tables only `get` and `insert`), and the rest
never depended on `Eq2Spec`.  Add the twin when a client appears; the recipe
is the one below.

This material **belongs in `HashMap.lean` proper** once a second client
exists.  It is a separate file only so that task #46 need not edit a finished
1656-line file.  The proofs are `HashMap.lean`'s own scripts with the one
`simp [Eq2Spec] at heq; simp [heq] at h` step replaced by `eq2_ite`, which
peels the `let b ← eq2 ckey key; if b then _ else _` the generated code emits
and hands back the two branches.
-/
import ConRon.Refine.HashMap
import ConRon.Refine.Abs

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine.HashMap

/-! The `@[local simp]` lemmas of `HashMap.lean` are local to that file; the
scripts copied below need them, so re-enable exactly those. -/
attribute [local simp] bind_eq_ok_iff lookupK_nil lookupK_cons alv_nil alvO_none
  alvO_some alv_cons alv_default eraseK_nil eraseK_cons getElem!_replicate_nil
  getElem!_map_alv

variable {K V : Type} [DecidableEq K]
  {HashableInst : ron.hashmap.Hashable K} {Eq2Inst : ron.hashmap.Eq2 K}

/-! ## The two hypotheses -/

/-- **Forward, key-restricted exactness of the `Eq2` dictionary.**  Read it as
"`eq2` never lies about well-formed keys": it may fail, and it may say anything
about keys outside `P`, but when it returns a verdict on two `P`-keys that
verdict is `decide (a = b)`.  This is what a `beq_refines` lemma of the port
gives (`Refine/Expr.lean`), and `Eq2Spec Eq2Inst` is the special case
`P := fun _ => True` plus totality. -/
def Eq2Fwd (Eq2Inst : ron.hashmap.Eq2 K) (P : K → Prop) : Prop :=
  ∀ a b c, P a → P b → Eq2Inst.eq2 a b = ok c → c = decide (a = b)

/-- `Eq2Spec` is the unrestricted, total instance of `Eq2Fwd`. -/
theorem Eq2Fwd_of_Eq2Spec {P : K → Prop} (h : Eq2Spec Eq2Inst) : Eq2Fwd Eq2Inst P := by
  intro a b c _ _ hc
  rw [h a b] at hc
  exact (Result.ok_injective hc).symm

/-- **Every key the table holds satisfies `P`.**  The side condition that
makes `Eq2Fwd` usable: `get` and `insert` compare the key they are given
against the keys already in the bucket, so both must be `P`. -/
def KeysOk (P : K → Prop) (m : ron.hashmap.HashMap K V) : Prop := ∀ p ∈ al_v m, P p.1

variable {m : ron.hashmap.HashMap K V}

omit [DecidableEq K] in
/-- `KeysOk` transported along a permutation of the entries — which is the
shape in which every table-building operation of `HashMap.lean` states what it
did. -/
theorem KeysOk_of_perm {P : K → Prop} {m' : ron.hashmap.HashMap K V} {l : List (K × V)}
    (hp : (al_v m').Perm l) (hl : ∀ p ∈ l, P p.1) : KeysOk P m' :=
  fun p hpm => hl p (hp.mem_iff.mp hpm)

omit [DecidableEq K] in
/-- The keys of one bucket are keys of the table. -/
theorem KeysOk.bucket {P : K → Prop} (hkeys : KeysOk P m) {j : Nat}
    (hj : j < m.slots.val.length) : ∀ p ∈ alv m.slots.val[j]!, P p.1 :=
  fun p hp => hkeys p ((slot_sublist_flatten hj).subset hp)

omit [DecidableEq K] in
/-- The keys of every bucket but one are keys of the table. -/
theorem KeysOk.restOf {P : K → Prop} (hkeys : KeysOk P m) {i : Nat} {p : K × V}
    (hp : p ∈ restOf m.slots.val i) : P p.1 := by
  obtain ⟨j, -, hj, hx⟩ := mem_restOf hp
  exact KeysOk.bucket hkeys hj _ hx

omit [DecidableEq K] in
/-- The keys of a bucket tail are keys of the bucket. -/
theorem keys_tail {P : K → Prop} {ckey : K} {cval : V} {tl : ron.hashmap.AList K V}
    (hls : ∀ p ∈ alv (ron.hashmap.AList.Cons ckey cval (some tl)), P p.1) :
    ∀ p ∈ alv tl, P p.1 := fun p hp => hls p (by simp [hp])

/-! ## Peeling one `eq2` call

This is the *whole* difference from `HashMap.lean`'s scripts.  Both bucket
walks the generated code emits open with `let b ← Eq2Inst.eq2 ckey key; if b
then _ else _`; `HashMap.lean` rewrites that away with `simp [heq]` because
`Eq2Spec` is an unconditional equation.  With the forward form the bind has to
be peeled first (`bind_eq_ok_iff`, DESIGN.md task #16 hard spot 1) and only
then does `heq` apply — and it applies to the value that came *out*. -/

theorem eq2_ite {P : K → Prop} (heq : Eq2Fwd Eq2Inst P) {α : Type} {a b : K}
    {x y : Result α} {r : α} (ha : P a) (hb : P b)
    (h : (do let c ← Eq2Inst.eq2 a b; if c then x else y) = ok r) :
    (a = b ∧ x = ok r) ∨ (a ≠ b ∧ y = ok r) := by
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  rw [heq a b c ha hb hc] at h
  by_cases hab : a = b
  · exact Or.inl ⟨hab, by simpa [hab] using h⟩
  · exact Or.inr ⟨hab, by simpa [hab] using h⟩

/-! ## The two bucket walks -/

theorem list_get_spec_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    {ls : ron.hashmap.AList K V} {k : K} {r : Option V}
    (hls : ∀ p ∈ alv ls, P p.1) (hk : P k)
    (h : ron.hashmap.list_get Eq2Inst ls k = ok r) : r = lookupK (alv ls) k := by
  induction ls using AList.recTail with
  | nil => rw [ron.hashmap.list_get.eq_def] at h; simp at h; simp [← h]
  | last ckey cval =>
    rw [ron.hashmap.list_get.eq_def] at h
    simp only at h
    rcases eq2_ite heq (show P ckey from hls (ckey, cval) (by simp)) hk h with
      ⟨hkc, h⟩ | ⟨hkc, h⟩
    · simp [hkc, ← Result.ok_injective h]
    · simp [hkc, ← Result.ok_injective h]
  | cons ckey cval tl ih =>
    rw [ron.hashmap.list_get.eq_def] at h
    simp only at h
    rcases eq2_ite heq (show P ckey from hls (ckey, cval) (by simp)) hk h with
      ⟨hkc, h⟩ | ⟨hkc, h⟩
    · simp [hkc, ← Result.ok_injective h]
    · simp [hkc, ih (keys_tail hls) h]


theorem list_insert_spec_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    {ls : ron.hashmap.AList K V} {k : K} {v : V} {old : Option V}
    {ls' : ron.hashmap.AList K V} (hls : ∀ p ∈ alv ls, P p.1) (hk : P k)
    (h : ron.hashmap.list_insert Eq2Inst ls k v = ok (old, ls')) :
    old = lookupK (alv ls) k ∧
    (alv ls').map Prod.fst =
      (if old.isSome then (alv ls).map Prod.fst else (alv ls).map Prod.fst ++ [k]) ∧
    (∀ k', lookupK (alv ls') k' = if k' = k then some v else lookupK (alv ls) k') ∧
    (old = none → alv ls' = alv ls ++ [(k, v)]) := by
  induction ls using AList.recTail generalizing old ls' with
  | nil =>
    rw [ron.hashmap.list_insert.eq_def] at h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, by simp, ?_, by simp⟩
    intro k'; by_cases hkk : k' = k <;> simp [hkk, eq_comm (a := k)]
  | last ckey cval =>
    rw [ron.hashmap.list_insert.eq_def] at h
    simp only at h
    rcases eq2_ite heq (show P ckey from hls (ckey, cval) (by simp)) hk h with
      ⟨hkc, h⟩ | ⟨hkc, h⟩
    · simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [hkc], by simp, ?_, by simp⟩
      intro k'
      by_cases hk' : k' = k <;> simp [hkc, hk', eq_comm (a := k)]
    · simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [hkc], by simp, ?_, by simp⟩
      intro k'
      by_cases hk' : k' = k
      · simp [hk', hkc]
      · simp [hk', Ne.symm hk']
  | cons ckey cval tl ih =>
    rw [ron.hashmap.list_insert.eq_def] at h
    simp only at h
    rcases eq2_ite heq (show P ckey from hls (ckey, cval) (by simp)) hk h with
      ⟨hkc, h⟩ | ⟨hkc, h⟩
    · simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [hkc], by simp, ?_, by simp⟩
      intro k'
      by_cases hk' : k' = k <;> simp [hkc, hk', eq_comm (a := k)]
    · simp at h
      obtain ⟨tl1, hrec, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4⟩ := ih (keys_tail hls) hrec
      refine ⟨by simp [hkc, h1], by simp [h2]; split <;> simp, ?_, ?_⟩
      · intro k'
        by_cases hk' : k' = k <;> by_cases hc : ckey = k' <;>
          simp [hkc, hk', hc, h3 k'] <;> simp_all
      · intro hnone; simp [h4 hnone]


/-! ## `get` and `insert_no_resize` -/

theorem get_refines_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P) (hinv : Inv HashableInst m)
    (hkeys : KeysOk P m) {k : K} (hk : P k) {r : Option V}
    (h : ron.hashmap.HashMap.get HashableInst Eq2Inst m k = ok r) : r = toFun m k := by
  rw [ron.hashmap.HashMap.get] at h
  split at h
  · rename_i h0
    have hav : al_v m = [] := by simp [al_v, vec_len_eq_zero_iff.mp h0]
    rw [← Result.ok_injective h]; simp [toFun, hav]
  simp only [bind_eq_ok_iff] at h
  obtain ⟨hw, hhash, i2, hbi, a, hidx, hget⟩ := h
  have hb : bucketAt HashableInst (alloc.vec.Vec.len m.slots) k = ok i2 := by
    simp only [bucketAt, bind_eq_ok_iff]; exact ⟨hw, hhash, hbi⟩
  obtain ⟨hlt, rfl⟩ := vec_index_eq hidx
  rw [toFun_eq_bucket hinv hlt hb]
  exact list_get_spec_wf heq (KeysOk.bucket hkeys hlt) hk hget


theorem insert_no_resize_spec_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv HashableInst m) (hkeys : KeysOk P m) {k : K} {v : V} (hk : P k)
    {old : Option V} {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.insert_no_resize HashableInst Eq2Inst m k v = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m k ∧
    (∀ k', toFun m' k' = if k' = k then some v else toFun m k') ∧
    m'.slots.val.length = m.slots.val.length ∧
    m'.max_load = m.max_load ∧ m'.saturated = m.saturated ∧
    (al_v m').length = (al_v m).length + (if old.isSome then 0 else 1) ∧
    (old = none → (al_v m').Perm ((k, v) :: al_v m)) ∧ KeysOk P m' := by
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
  obtain ⟨L1, L2, L3, L4⟩ :=
    list_insert_spec_wf heq (KeysOk.bucket hkeys hlt) hk hins
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
  have hbA : ∀ p ∈ A, P p.1 := by rw [hA]; exact KeysOk.bucket hkeys hlt
  have hbR : ∀ p ∈ R, P p.1 := by rw [hR]; exact fun p hp => hkeys.restOf hp
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
  have hkeys' : KeysOk P m' := by
    intro p hp
    rcases List.mem_append.1 (PM'.mem_iff.1 hp) with hp | hp
    · have hfst : p.1 ∈ (alv a1).map Prod.fst := List.mem_map.2 ⟨p, hp, rfl⟩
      rw [L2] at hfst
      by_cases hos : old.isSome = true
      · rw [if_pos hos] at hfst
        obtain ⟨q, hq, hqf⟩ := List.mem_map.1 hfst
        exact hqf ▸ hbA q hq
      · rw [if_neg hos] at hfst
        rcases List.mem_append.1 hfst with hf | hf
        · obtain ⟨q, hq, hqf⟩ := List.mem_map.1 hf
          exact hqf ▸ hbA q hq
        · simp only [List.mem_singleton] at hf
          exact hf ▸ hk
    · exact hbR p hp
  refine ⟨⟨?_, ?_, ?_, NDnew, ?_⟩, hOld, hToFun, hlen, hml, hsat, hlenAv, ?_, hkeys'⟩
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

theorem move_elements_from_list_spec_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P) :
    ∀ (ls : ron.hashmap.AList K V) (nt nt' : ron.hashmap.HashMap K V),
      Inv HashableInst nt → KeysOk P nt → (∀ p ∈ alv ls, P p.1) →
      ((alv ls).map Prod.fst).Nodup →
      (∀ x ∈ alv ls, x.1 ∉ (al_v nt).map Prod.fst) →
      ron.hashmap.HashMap.move_elements_from_list HashableInst Eq2Inst nt ls = ok nt' →
      Inv HashableInst nt' ∧ (al_v nt').Perm (alv ls ++ al_v nt) ∧
      nt'.slots.val.length = nt.slots.val.length ∧
      nt'.max_load = nt.max_load ∧ nt'.saturated = nt.saturated := by
  intro ls
  induction ls using AList.recTail with
  | nil =>
    intro nt nt' hinv _ _ _ _ h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    simp only at h
    rw [← Result.ok_injective h]
    exact ⟨hinv, by simp, rfl, rfl, rfl⟩
  | last k v =>
    intro nt nt' hinv hkeys hlsP hnd hdisj h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    simp only at h
    obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, nt1⟩ := q
    obtain ⟨hinv1, hold, htf, hlen1, hml1, hsat1, -, hperm1, hkeys1⟩ :=
      insert_no_resize_spec_wf heq hinv hkeys (show P k from hlsP (k, v) (by simp)) hins
    have hknt : k ∉ (al_v nt).map Prod.fst := hdisj (k, v) (by simp)
    have honone : o = none := by
      rw [hold, toFun]; exact lookupK_eq_none_of_not_mem hknt
    have P1 : (al_v nt1).Perm ((k, v) :: al_v nt) := hperm1 honone
    rw [← Result.ok_injective h]
    exact ⟨hinv1, by simpa using P1, hlen1, hml1, hsat1⟩
  | cons k v tl ih =>
    intro nt nt' hinv hkeys hlsP hnd hdisj h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    simp only at h
    obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, nt1⟩ := q
    have h2 : ron.hashmap.HashMap.move_elements_from_list HashableInst Eq2Inst nt1 tl
        = ok nt' := h
    obtain ⟨hinv1, hold, htf, hlen1, hml1, hsat1, -, hperm1, hkeys1⟩ :=
      insert_no_resize_spec_wf heq hinv hkeys (show P k from hlsP (k, v) (by simp)) hins
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
    obtain ⟨hinv', P2, hlen2, hml2, hsat2⟩ :=
      ih nt1 nt' hinv1 hkeys1 (keys_tail hlsP) hnd.2 hdisj2 h2
    refine ⟨hinv', ?_, by rw [hlen2, hlen1], by rw [hml2, hml1], by rw [hsat2, hsat1]⟩
    refine P2.trans ?_
    refine (List.Perm.append_left (alv tl) P1).trans ?_
    exact List.perm_middle (a := (k, v)) (l₁ := alv tl) (l₂ := al_v nt)



theorem move_elements_spec_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P) (N : Nat) :
    ∀ (nt nt' : ron.hashmap.HashMap K V)
      (slots slots' : alloc.vec.Vec (ron.hashmap.AList K V)) (lo hi : Std.Usize),
      hi.val - lo.val = N → hi.val ≤ slots.val.length → Inv HashableInst nt →
      KeysOk P nt →
      (∀ x ∈ slotsFlat slots.val lo.val (hi.val - lo.val), P x.1) →
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
    intro nt nt' slots slots' lo hi hN hbound hinv hkeysnt hPfl hnd hdisj h
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
        rw [hflat] at hnd hdisj hPfl
        obtain ⟨hinv', hperm, hlen', hml', hsat'⟩ :=
          move_elements_from_list_spec_wf heq a nt nt1 hinv hkeysnt hPfl hnd hdisj hmv
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
        have hP1 : ∀ x ∈ slotsFlat slots.val lo.val (mid.val - lo.val), P x.1 :=
          fun x hx => hPfl x (by rw [hsplit]; exact List.mem_append_left _ hx)
        obtain ⟨hinv1, P1, hlenA, hmlA, hsatA, hlen1, f1⟩ :=
          ih (mid.val - lo.val) (by omega) nt nt1 slots slots1 lo mid rfl (by omega) hinv
            hkeysnt hP1
            (by rw [show mid.val - lo.val = mid.val - lo.val from rfl]; exact ND1)
            (fun x hx => hdisj x (by rw [hsplit]; exact List.mem_append_left _ hx)) hrec1
        have hkeys1 : KeysOk P nt1 := KeysOk_of_perm P1 (by
          intro p hp
          rcases List.mem_append.1 hp with hp | hp
          · exact hP1 p hp
          · exact hkeysnt p hp)
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
        have hP2 : ∀ x ∈ slotsFlat slots1.val mid.val (hi.val - mid.val), P x.1 := by
          rw [hF2]
          exact fun x hx =>
            hPfl x (by rw [hsplit]; exact List.mem_append_right _ hx)
        obtain ⟨hinv', P2, hlenB, hmlB, hsatB, hlen2, f2⟩ :=
          ih (hi.val - mid.val) (by omega) nt1 nt' slots1 slots' mid hi rfl (by omega) hinv1
            hkeys1 hP2 (by rw [hF2]; exact ND2) hdisj2 h2
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



/-- `try_resize` is the one operation that needs the table to be *allocated*:
it doubles `slots.len()`, and `0` doubled is still `0`.  `insert` supplies
`hpos` from `ensure_slots_spec` (task #35). -/
theorem try_resize_spec_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv HashableInst m) (hkeys : KeysOk P m)
    (hpos : 0 < m.slots.val.length) {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.try_resize HashableInst Eq2Inst m = ok m') :
    Inv HashableInst m' ∧ (∀ k, toFun m' k = toFun m k) ∧ KeysOk P m' := by
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
      move_elements_spec_wf heq ((alloc.vec.Vec.len m.slots).val - (0#usize : Std.Usize).val)
        nt nt1 m.slots sl1 0#usize (alloc.vec.Vec.len m.slots) rfl (by rw [hcapv]) hinvnt
        (by intro p hp; rw [hnil] at hp; simp at hp)
        (by rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat]; exact hkeys)
        (by rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat]; exact hinv.nodup)
        (by rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat, hnil]; simp) hmv
    rw [show (0#usize : Std.Usize).val = 0 by scalar_tac, hflat, hnil] at P1
    have Pfin : (al_v nt1).Perm (al_v m) := by simpa using P1
    have hav : al_v m' = al_v nt1 := al_v_congr eslots
    refine ⟨Inv_of_slots_eq hinv1 eslots ?_, ?_, ?_⟩
    · rw [ene, hinv.entries, hav, Pfin.length_eq]
    · intro k
      rw [toFun, toFun, hav, lookupK_perm Pfin hinv1.nodup]
    · intro p hp
      rw [hav] at hp
      exact hkeys p (Pfin.mem_iff.1 hp)
  · have e := Result.ok_injective h
    have eslots : m'.slots = m.slots :=
      (congrArg (fun z : ron.hashmap.HashMap K V => z.slots) e).symm
    have ene : m'.num_entries = m.num_entries :=
      (congrArg (fun z : ron.hashmap.HashMap K V => z.num_entries) e).symm
    have hav : al_v m' = al_v m := al_v_congr eslots
    refine ⟨Inv_of_slots_eq hinv eslots (by rw [ene, hinv.entries, hav]), ?_, ?_⟩
    · intro k; rw [toFun, toFun, hav]
    · intro p hp; rw [hav] at hp; exact hkeys p hp



theorem insert_refines_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv HashableInst m) (hkeys : KeysOk P m) {k : K} {v : V} (hk : P k)
    {old : Option V} {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m k ∧
    toFun m' = Function.update (toFun m) k (some v) ∧ KeysOk P m' := by
  rw [ron.hashmap.HashMap.insert] at h
  -- `insert` allocates first (task #35): the table `insert_no_resize` writes
  -- into is `m0`, which denotes the same map as `m` and *is* allocated.
  obtain ⟨m0, hens, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hinv0, hpos0, hav0, -, -⟩ := ensure_slots_spec hinv hens
  have htf0 : toFun m0 = toFun m := by funext k'; rw [toFun, toFun, hav0]
  have hkeys0 : KeysOk P m0 := by intro p hp; rw [hav0] at hp; exact hkeys p hp
  obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨old0, m1⟩ := q
  obtain ⟨hinv1, hold0, htf, hlen1, -, -, -, -, hkeys1⟩ :=
    insert_no_resize_spec_wf heq hinv0 hkeys0 hk hins
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
      exact ⟨hinv1, hold, hupd, hkeys1⟩
    · obtain ⟨m2, hres, hok⟩ := bind_eq_ok_iff.mp h2
      obtain ⟨hinv2, htf2, hkeys2⟩ := try_resize_spec_wf heq hinv1 hkeys1 hpos1 hres
      have e := Result.ok_injective hok
      have e1 : old = old0 := (congrArg Prod.fst e).symm
      have e2 : m' = m2 := (congrArg Prod.snd e).symm
      rw [e1, e2]
      refine ⟨hinv2, hold, ?_, hkeys2⟩
      rw [← hupd]; funext k'; exact htf2 k'
  · have e := Result.ok_injective h2
    have e1 : old = old0 := (congrArg Prod.fst e).symm
    have e2 : m' = m1 := (congrArg Prod.snd e).symm
    rw [e1, e2]
    exact ⟨hinv1, hold, hupd, hkeys1⟩



/-! ## The bridge to `Std.HashMap`, key-restricted

`HashMap.lean`'s `Rel m s absK absV := ∀ k, (toFun m k).map absV = s[absK k]?`
is the wrong relation for the clients, and not just inconveniently so: their
`absK` (`absName`, `absExpr`, …) is injective only on well-formed keys, so as
soon as one entry is inserted a *non*-well-formed `k'` with `absK k' = absK k`
has `toFun m' k' = none` — every stored key is well-formed, so `k'` is not
among them — while `s[absK k']?` is `some (absV v)`.  `Rel` is therefore false
after the first `insert`.  `RelOn P` constrains only the `P`-keys, and
correspondingly `Rel_insert_wf` asks for injectivity **on `P`** rather than
`Function.Injective absK`. -/

section Bridge

variable {K' V' : Type} [BEq K'] [Hashable K'] {absK : K → K'} {absV : V → V'}

/-- `m` represents `s` under `absK`, `absV` **on the keys satisfying `P`**. -/
def RelOn (P : K → Prop) (m : ron.hashmap.HashMap K V)
    (s : _root_.Std.HashMap K' V') (absK : K → K') (absV : V → V') : Prop :=
  ∀ k, P k → (toFun m k).map absV = s[absK k]?

/-- `Rel` is the case `P := fun _ => True`, so it is always the stronger one:
this is the only direction that holds. -/
theorem RelOn_of_Rel {P : K → Prop} {s : _root_.Std.HashMap K' V'}
    (h : Rel m s absK absV) : RelOn P m s absK absV := fun k _ => h k

/-- The empty relation.  Compose with `new_refines`, `with_capacity_refines` or
`clear_refines`, whose third component is exactly this hypothesis; their second
gives `KeysOk P` (from `al_v m = []`). -/
theorem RelOn_empty {P : K → Prop} (h : ∀ k, toFun m k = none) :
    RelOn P m (∅ : _root_.Std.HashMap K' V') absK absV := by
  intro k _; rw [h k, _root_.Std.HashMap.getElem?_empty]; rfl

theorem Rel_get_wf {P : K → Prop} {s : _root_.Std.HashMap K' V'}
    (heq : Eq2Fwd Eq2Inst P) (hinv : Inv HashableInst m) (hkeys : KeysOk P m)
    (hrel : RelOn P m s absK absV) {k : K} (hk : P k) {r : Option V}
    (h : ron.hashmap.HashMap.get HashableInst Eq2Inst m k = ok r) :
    r.map absV = s[absK k]? := by
  rw [get_refines_wf heq hinv hkeys hk h]; exact hrel k hk

theorem Rel_insert_wf [LawfulBEq K'] [LawfulHashable K'] {P : K → Prop}
    {s : _root_.Std.HashMap K' V'} (heq : Eq2Fwd Eq2Inst P)
    (hinj : ∀ a b, P a → P b → absK a = absK b → a = b) (hinv : Inv HashableInst m)
    (hkeys : KeysOk P m) (hrel : RelOn P m s absK absV) {k : K} {v : V} (hk : P k)
    {old : Option V} {m' : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m')) :
    RelOn P m' (s.insert (absK k) (absV v)) absK absV ∧ KeysOk P m' := by
  obtain ⟨-, -, hupd, hkeys'⟩ := insert_refines_wf heq hinv hkeys hk h
  refine ⟨?_, hkeys'⟩
  intro k' hk'
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
  by_cases hkk : k' = k
  · subst hkk; simp
  · have hne : ¬(absK k = absK k') := fun hc => hkk (hinj k k' hk hk' hc).symm
    rw [if_neg hkk, if_neg (by simpa using hne)]
    exact hrel k' hk'

end Bridge

end ConRon.Refine.HashMap

/-! ## Axiom census

As in `HashMap.lean`: nothing but Lean's own three axioms — no `sorry`, no new
assumption about `hash64`, and none about `eq2` beyond `Eq2Fwd`. -/

/-- info: 'ConRon.Refine.HashMap.insert_refines_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap.insert_refines_wf

/-- info: 'ConRon.Refine.HashMap.get_refines_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap.get_refines_wf

/-- info: 'ConRon.Refine.HashMap.Rel_insert_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap.Rel_insert_wf
