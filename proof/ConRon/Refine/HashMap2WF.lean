/-
`Refine/HashMapWF.lean`'s key-restricted API, for `ron::HashMap2`.

`HashMapWF.lean` exists because `Eq2Spec` — "`eq2 a b` *is* an `ok
(decide (a = b))`" — is unusable by the real clients, whose keys are the
port's `Name`/`Level`/`Expr` and tuples thereof: it asserts totality, which
DESIGN.md §3.5's forward style never proves, and exactness for *all* keys,
while the port's `beq` is exact only for well-formed ones.  The right
hypothesis is the forward, key-restricted `Eq2Fwd Eq2Inst P`, and the right
side condition is `KeysOk P` — "every key the table holds satisfies `P`".

**Both are `ConRon.Refine.HashMap`'s and `ConRon.Refine.HashMap2`'s own**:
`Eq2Fwd` is imported from `HashMapWF.lean` unchanged (it is a statement about
the `Eq2` dictionary, not about the table), and `KeysOk` is
`Refine/HashMap2.lean`'s, stated over `sl_v` instead of `al_v`.

**There is no second copy of any proof here.**  `HashMapWF.lean` re-proves
`HashMap.lean`'s scripts with `eq2_ite` where `simp [heq]` stood; for
`HashMap2` the restricted form is proved *once*, in `Refine/HashMap2.lean` —
it is the strictly more general one — and this file is the `_wf` naming of it
plus the `RelOn` bridge, statement for statement as `HashMapWF.lean` gives
them.  A consumer written against `HashMapWF` compiles against `HashMap2WF`
by changing the namespace.

`clear`/`new`/`with_capacity`/`len`/`is_empty`/`capacity`/`dup` get no `_wf`
twin here for the same reason they get none there: they never depended on the
`Eq2` dictionary.  `remove` and `contains_key` get one, which
`HashMapWF.lean` does not have — they cost nothing, being the same lemma
under another name.
-/
import ConRon.Refine.HashMap2

open Aeneas Aeneas.Std Result
open ConRon.Generated
open ConRon.Refine.HashMap (Eq2Spec Eq2Fwd Eq2Fwd_of_Eq2Spec)

namespace ConRon.Refine.HashMap2

variable {K V : Type} [DecidableEq K]
  {HashableInst : ron.hashmap.Hashable K} {Eq2Inst : ron.hashmap.Eq2 K}
  {m : ron.hashmap2.HashMap2 K V}

omit [DecidableEq K] in
/-- `KeysOk` transported along a permutation of the entries — the shape in
which every table-building operation states what it did. -/
theorem KeysOk_of_perm {P : K → Prop} {m' : ron.hashmap2.HashMap2 K V}
    {l : List (K × V)} (hp : (sl_v m').Perm l) (hl : ∀ p ∈ l, P p.1) : KeysOk P m' :=
  fun p hpm => hl p (hp.mem_iff.mp hpm)

/-! ## The operations, key-restricted -/

theorem get_refines_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P) (hinv : Inv HashableInst m)
    (hkeys : KeysOk P m) {key : K} (hk : P key) {r : Option V}
    (h : ron.hashmap2.HashMap2.get HashableInst Eq2Inst m key = ok r) : r = toFun m key :=
  get_refines_gen heq hinv hkeys hk h

theorem contains_key_refines_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv HashableInst m) (hkeys : KeysOk P m) {key : K} (hk : P key) {b : Bool}
    (h : ron.hashmap2.HashMap2.contains_key HashableInst Eq2Inst m key = ok b) :
    b = (toFun m key).isSome :=
  contains_key_refines_gen heq hinv hkeys hk h

/-- `insert_no_resize` concludes `Inv0` and not `Inv`: it writes an entry
without checking the load, and `insert`'s doubling is what puts the load
clause back. -/
theorem insert_no_resize_spec_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
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
    (old = none → (sl_v m').Perm ((key, value) :: sl_v m)) ∧ KeysOk P m' :=
  insert_no_resize_spec heq hinv hkeys hk hpos h

/-- `try_resize` is the one operation that needs the table to be *allocated*
(it doubles `slots.len()`, and `0` doubled is still `0`) and the one that can
saturate; `insert` supplies `hpos` from `ensure_slots_spec` (task #35) and
`hcap` from its own. -/
theorem try_resize_spec_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv0 HashableInst m) (hkeys : KeysOk P m) (hpos : 0 < m.slots.val.length)
    (hcap : 2 * m.slots.val.length ≤ Std.Usize.max) {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.try_resize HashableInst Eq2Inst m = ok m') :
    Inv HashableInst m' ∧ KeysOk P m' ∧ (∀ k, toFun m' k = toFun m k) :=
  try_resize_spec heq hinv hkeys hpos hcap h

theorem insert_refines_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv HashableInst m) (hkeys : KeysOk P m) {key : K} {value : V} (hk : P key)
    (hcap : 2 * m.slots.val.length ≤ Std.Usize.max) {old : Option V}
    {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.insert HashableInst Eq2Inst m key value = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m key ∧
    toFun m' = Function.update (toFun m) key (some value) ∧ KeysOk P m' :=
  insert_refines_gen heq hinv hkeys hk hcap h

theorem remove_refines_wf {P : K → Prop} (heq : Eq2Fwd Eq2Inst P)
    (hinv : Inv HashableInst m) (hkeys : KeysOk P m) {key : K} (hk : P key)
    {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.remove HashableInst Eq2Inst m key = ok (old, m')) :
    Inv HashableInst m' ∧ old = toFun m key ∧
    toFun m' = Function.update (toFun m) key none ∧ KeysOk P m' :=
  remove_refines_gen heq hinv hkeys hk h


/-! ## The bridge to `Std.HashMap`, key-restricted

`HashMap.lean`'s `Rel m s absK absV := ∀ k, (toFun m k).map absV = s[absK k]?`
is the wrong relation for the clients, and not just inconveniently so: their
`absK` (`absName`, `absExpr`, …) is injective only on well-formed keys, so as
soon as one entry is inserted a *non*-well-formed `k'` with `absK k' = absK k`
has `toFun m' k' = none` — every stored key is well-formed, so `k'` is not
among them — while `s[absK k']?` is `some (absV v)`.  `Rel` is therefore false
after the first `insert`.  `RelOn P` constrains only the `P`-keys, and
correspondingly `Rel_insert_wf` asks for injectivity **on `P`** rather than
`Function.Injective absK`.  Word for word `HashMapWF.lean`'s, over the new
`toFun`. -/

section Bridge

variable {K' V' : Type} [BEq K'] [Hashable K'] {absK : K → K'} {absV : V → V'}

/-- `m` represents `s` under `absK`, `absV` **on the keys satisfying `P`**. -/
def RelOn (P : K → Prop) (m : ron.hashmap2.HashMap2 K V)
    (s : _root_.Std.HashMap K' V') (absK : K → K') (absV : V → V') : Prop :=
  ∀ k, P k → (toFun m k).map absV = s[absK k]?

/-- `Rel` is the case `P := fun _ => True`, so it is always the stronger one:
this is the only direction that holds. -/
theorem RelOn_of_Rel {P : K → Prop} {s : _root_.Std.HashMap K' V'}
    (h : Rel m s absK absV) : RelOn P m s absK absV := fun k _ => h k

/-- The empty relation.  Compose with `new_refines`, `with_capacity_refines`,
`clear_refines` or `clear_fit_refines`, whose third component is exactly this
hypothesis; their second gives `KeysOk P` (from `sl_v m = []`). -/
theorem RelOn_empty {P : K → Prop} (h : ∀ k, toFun m k = none) :
    RelOn P m (∅ : _root_.Std.HashMap K' V') absK absV := by
  intro k _; rw [h k, _root_.Std.HashMap.getElem?_empty]; rfl

omit [DecidableEq K] in
theorem KeysOk_of_nil {P : K → Prop} (h : sl_v m = []) : KeysOk P m := by
  intro p hp; rw [h] at hp; simp at hp

theorem Rel_get_wf {P : K → Prop} {s : _root_.Std.HashMap K' V'}
    (heq : Eq2Fwd Eq2Inst P) (hinv : Inv HashableInst m) (hkeys : KeysOk P m)
    (hrel : RelOn P m s absK absV) {key : K} (hk : P key) {r : Option V}
    (h : ron.hashmap2.HashMap2.get HashableInst Eq2Inst m key = ok r) :
    r.map absV = s[absK key]? := by
  rw [get_refines_wf heq hinv hkeys hk h]; exact hrel key hk

theorem Rel_insert_wf [LawfulBEq K'] [LawfulHashable K'] {P : K → Prop}
    {s : _root_.Std.HashMap K' V'} (heq : Eq2Fwd Eq2Inst P)
    (hinj : ∀ a b, P a → P b → absK a = absK b → a = b) (hinv : Inv HashableInst m)
    (hkeys : KeysOk P m) (hrel : RelOn P m s absK absV)
    (hcap : 2 * m.slots.val.length ≤ Std.Usize.max) {key : K} {value : V} (hk : P key)
    {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.insert HashableInst Eq2Inst m key value = ok (old, m')) :
    RelOn P m' (s.insert (absK key) (absV value)) absK absV ∧ KeysOk P m' := by
  obtain ⟨-, -, hupd, hkeys'⟩ := insert_refines_wf heq hinv hkeys hk hcap h
  refine ⟨?_, hkeys'⟩
  intro k' hk'
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
  by_cases hkk : k' = key
  · subst hkk; simp
  · have hne : ¬(absK key = absK k') := fun hc => hkk (hinj key k' hk hk' hc).symm
    rw [if_neg hkk, if_neg (by simpa using hne)]
    exact hrel k' hk'

theorem Rel_remove_wf [LawfulBEq K'] [LawfulHashable K'] {P : K → Prop}
    {s : _root_.Std.HashMap K' V'} (heq : Eq2Fwd Eq2Inst P)
    (hinj : ∀ a b, P a → P b → absK a = absK b → a = b) (hinv : Inv HashableInst m)
    (hkeys : KeysOk P m) (hrel : RelOn P m s absK absV) {key : K} (hk : P key)
    {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.remove HashableInst Eq2Inst m key = ok (old, m')) :
    RelOn P m' (s.erase (absK key)) absK absV ∧ KeysOk P m' := by
  obtain ⟨-, -, hupd, hkeys'⟩ := remove_refines_wf heq hinv hkeys hk h
  refine ⟨?_, hkeys'⟩
  intro k' hk'
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_erase]
  by_cases hkk : k' = key
  · subst hkk; simp
  · have hne : ¬(absK key = absK k') := fun hc => hkk (hinj key k' hk hk' hc).symm
    rw [if_neg hkk, if_neg (by simpa using hne)]
    exact hrel k' hk'

end Bridge

end ConRon.Refine.HashMap2

/-! ## Axiom census

As in `HashMap2.lean`: nothing but Lean's own three axioms, on every
statement. -/

/-- info: 'ConRon.Refine.HashMap2.insert_refines_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.insert_refines_wf

/-- info: 'ConRon.Refine.HashMap2.get_refines_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.get_refines_wf

/-- info: 'ConRon.Refine.HashMap2.Rel_insert_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.Rel_insert_wf

/-- info: 'ConRon.Refine.HashMap2.remove_refines_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.remove_refines_wf

/-- info: 'ConRon.Refine.HashMap2.Rel_remove_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Refine.HashMap2.Rel_remove_wf
