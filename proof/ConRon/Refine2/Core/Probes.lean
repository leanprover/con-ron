/-
# `ConRon.Refine2.Core.Probes` — the knot's six memo probes and six memo writes

**Task #97-P5-Core, floor 0.**  `Refine2/Specs.lean` closed the thirteen
per-call `Memos` tables; the knot reads and writes the *per-declaration*
`Caches` instead, and those six pairs are not in `Specs.lean` because nothing
below the Core tier calls them.  This file is that floor: `whnf_core`, `whnf`,
`infer`, `infer_io`, `annot` and `defeq`, probe and write, plus the one
generic fact the writes need and the memo tier never did.

## What task #97-P5-1 predicted, and what the code actually does

That task's "what the Core tier needs" asks for **`map_find_slot_insert_at_abs`,
`find_slot` + `insert_at` on a bare memo table**, on the ground that task
#97-P6-13 "put `whnf_core` / `whnf` / `infer`'s probe-and-insert into the call
site rather than behind a named getter".

**It is not what `arena::core` does today.**  `find_slot` and `push_at` occur
in `arena/store.rs` and nowhere else in the crate — the fused find-or-insert
is the INTERN path's, task #97-survey's N2, and `Specs.lean`'s
`tbl_find_slot_abs` already covers it.  The knot's three grades call
`whnf_core_probe` / `whnf_core_set` and their siblings: **named functions over
`HashMap2::get` and `HashMap2::insert`**, i.e. exactly `Specs.lean`'s
`inst1_get_run` / `inst1_set_run` shape at a `Caches` table.  What #97-P6-13
inlined into the knot's slot was the twin's `memoEI` CLOSURE PAIR (the twin's
deviation 6), not the port's table operation.  So the lemma this tier wants is
the memo tier's lemma twelve more times, and the prediction is withdrawn.

## The one genuinely new fact: the tables agree on their SIZE

`Memos` has no capacity test; `Caches` does — DESIGN §8.3's lesson 10, "a cap,
not an eviction policy":

    // arena::core::whnf_core_set              -- ConRon/Arena/Core.lean
    if st.caches.whnf_core_c.len() < CACHE_CAP  let mp := if mp.size < cacheCap
    { () } else { ...= HashMap2::new() }                then mp else ∅

and the two branches must be the SAME branch, or the port clears a table the
twin keeps (or the other way round) and the two states stop being related.

`RelOn` does not give that.  It is a one-way probe agreement — *"on every
`P`-key the port's table answers what the twin's does"* — and says nothing
about keys outside the image of `absK`.  **`relOn_size` is the first place in
the tier where the relation has to be a BIJECTION**, and it is: `absU32` is
onto (`absU32_surj`, three lines) because a twin handle word is a `UInt32` and
a port handle word is a `U32`, which are the same 32 bits; every key
abstraction of `CachesRel` is a tuple of those, hence onto and injective.  The
lemma is then the two key lists — the port's `sl_v`, nodup by
`HashMap2.Inv`, and the twin's `Std.HashMap.keys`, nodup by
`distinct_keys` — shown equal as multisets through `absK`.

That is a fact about `RelOn` and belongs in `Refine/HashMap2WF.lean`; it is
here because this tier may not edit that file, and the three-line migration is
named in the task's report.
-/
import ConRon.Refine2.Specs
import ConRon.Arena.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn sl_v toFun support mem_support_iff
  card_support)

/-! ## The handle abstractions are onto

`absU32` is a bijection `Std.U32 ≃ UInt32` — the two are the same 32 bits —
and every `Caches` key abstraction is a tuple of it. -/

/-- Every twin word is some port word. -/
theorem absU32_surj : Function.Surjective absU32 := by
  intro w
  refine ⟨UScalar.ofNatCore (ty := .U32) w.toNat ?_, ?_⟩
  · have := w.toNat_lt
    simp only [UScalarTy.numBits]
    omega
  · apply UInt32.toNat_inj.mp
    rw [absU32_toNat]
    rfl

theorem absEIdx_surj : Function.Surjective absEIdx := by
  intro i
  obtain ⟨w⟩ := i
  obtain ⟨x, hx⟩ := absU32_surj w
  exact ⟨⟨x⟩, by simp [absEIdx, hx]⟩

theorem absEIdxPair_surj : Function.Surjective absEIdxPair := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := absEIdx_surj a
  obtain ⟨y, hy⟩ := absEIdx_surj b
  exact ⟨⟨x, y⟩, by simp [absEIdxPair, hx, hy]⟩

theorem absEIdxPair_inj : Function.Injective absEIdxPair := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [absEIdxPair, Prod.mk.injEq] at h
  simp [absEIdx_inj h.1, absEIdx_inj h.2]

/-! ## The size agreement

The fact `RelOn` does not carry, and which the six capacity tests need. -/

section Size

variable {K V K' V' : Type} [DecidableEq K] [BEq K'] [Hashable K']

/-- **A `RelOn` at a BIJECTIVE key abstraction relates the two SIZES.**  The
port's entry list is nodup by `HashMap2.Inv`, the twin's `keys` by
`Std.HashMap.distinct_keys`, and `absK` carries one onto the other: a port key
is in the table iff the twin's map has the abstracted key, by `RelOn` at that
key, and every twin key is an abstracted port key by surjectivity. -/
theorem relOn_size [LawfulBEq K'] [LawfulHashable K']
    {HashableInst : ron.hashmap.Hashable K}
    {m : ron.hashmap2.HashMap2 K V} {s : _root_.Std.HashMap K' V'}
    {absK : K → K'} {absV : V → V'}
    (hsurj : Function.Surjective absK) (hinj : Function.Injective absK)
    (hinv : Inv HashableInst m)
    (hrel : RelOn (fun _ => True) m s absK absV) :
    (sl_v m).length = s.size := by
  rw [← _root_.Std.HashMap.length_keys]
  have hmem : ∀ k : K, absK k ∈ s.keys ↔ k ∈ (sl_v m).map Prod.fst := by
    intro k
    have hr := hrel k trivial
    rw [_root_.Std.HashMap.mem_keys, _root_.Std.HashMap.mem_iff_isSome_getElem?,
      ← hr, Option.isSome_map, ← mem_support_iff (m := m) (k := k), support,
      List.mem_toFinset]
  have hnd1 : (((sl_v m).map Prod.fst).map absK).Nodup :=
    hinv.nodup.map (fun _ _ h => hinj h)
  have hnd2 : s.keys.Nodup := by
    have := (_root_.Std.HashMap.distinct_keys (m := s))
    simpa [List.Nodup, beq_iff_eq] using this
  have hperm : (((sl_v m).map Prod.fst).map absK).Perm s.keys := by
    rw [List.perm_ext_iff_of_nodup hnd1 hnd2]
    intro a
    constructor
    · intro ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      exact (hmem k).mpr hk
    · intro ha
      obtain ⟨k, rfl⟩ := hsurj a
      exact List.mem_map.2 ⟨k, (hmem k).mp ha, rfl⟩
  have := hperm.length_eq
  simpa using this

/-- `HashMap2::len` against the twin's `Std.HashMap.size`, through
`relOn_size`: the reading the six capacity tests are written against. -/
theorem cache_len_abs [LawfulBEq K'] [LawfulHashable K']
    {HashableInst : ron.hashmap.Hashable K}
    {m : ron.hashmap2.HashMap2 K V} {s : _root_.Std.HashMap K' V'}
    {absK : K → K'} {absV : V → V'}
    (hsurj : Function.Surjective absK) (hinj : Function.Injective absK)
    (hinv : Inv HashableInst m)
    (hrel : RelOn (fun _ => True) m s absK absV) {n : Std.Usize}
    (h : ron.hashmap2.HashMap2.len m = ok n) : n.val = s.size := by
  rw [(ConRon.Refine.HashMap2.len_refines hinv h).1]
  exact relOn_size hsurj hinj hinv hrel

end Size

/-! ## The capped memo write, once

The six `*_set` functions are one function at six tables, and the twin's six
`*Set` are one `do` block at six fields.  This packages the pair: the capacity
branch (`relOn_size`, above), then `new_refines` or the table itself, then
`Specs.lean`'s `memo_insert_step`. -/

/-- **One capped memo write.**  Given the table's relation and invariant, the
`len`/`CACHE_CAP` branch the port took and the map it ended with, the abstract
table the twin ends with is the twin's own `if … then mp else ∅` insert. -/
theorem cache_insert_step {K K' V V' : Type} [DecidableEq K] [BEq K'] [Hashable K']
    [LawfulBEq K'] [LawfulHashable K']
    {HashableInst : ron.hashmap.Hashable K} {Eq2Inst : ron.hashmap.Eq2 K}
    {m : ron.hashmap2.HashMap2 K V} {s : _root_.Std.HashMap K' V'}
    {absK : K → K'} {absV : V → V'}
    (heq : Eq2Fwd Eq2Inst (fun _ => True))
    (hsurj : Function.Surjective absK) (hinj : Function.Injective absK)
    (hinv : Inv HashableInst m) (hrel : RelOn (fun _ => True) m s absK absV)
    {n : Std.Usize} (hlen : ron.hashmap2.HashMap2.len m = ok n)
    {hm : ron.hashmap2.HashMap2 K V}
    (hfit : (if n < arena.core_state.CACHE_CAP then ok m
      else ron.hashmap2.HashMap2.new K V) = ok hm)
    {key : K} {value : V} {old : Option V} {m' : ron.hashmap2.HashMap2 K V}
    (h : ron.hashmap2.HashMap2.insert HashableInst Eq2Inst hm key value
          = ok (old, m')) :
    RelOn (fun _ => True) m'
      ((if s.size < Arena.cacheCap then s else ∅).insert (absK key) (absV value))
      absK absV ∧ Inv HashableInst m' := by
  have hsize : n.val = s.size := cache_len_abs hsurj hinj hinv hrel hlen
  have hcapv : (arena.core_state.CACHE_CAP : Std.Usize).val = Arena.cacheCap := by
    rw [arena.core_state.CACHE_CAP, Arena.cacheCap]
    rfl
  have hcap : (n < arena.core_state.CACHE_CAP) ↔ (s.size < Arena.cacheCap) := by
    rw [← hsize, ← hcapv]
    exact Std.UScalar.lt_equiv n _
  by_cases hb : n < arena.core_state.CACHE_CAP
  · rw [if_pos (hcap.mp hb)]
    rw [if_pos hb] at hfit
    have hfit' : m = hm := Result.ok_injective hfit
    subst hfit'
    exact memo_insert_step heq hinj hinv hrel h
  · rw [if_neg (fun hx => hb (hcap.mpr hx))]
    rw [if_neg hb] at hfit
    obtain ⟨hinv0, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
      (HashableInst := HashableInst) hfit
    exact memo_insert_step heq hinj hinv0
      (ConRon.Refine.HashMap2.RelOn_empty hnone) h


/-! ## The six probes

The twin has no named getter — DESIGN §8.4's deviation 6 put the probe INLINE
in the knot's slot, `match (← get).caches.whnfCoreC[e]? with` — so these are
stated as plain equations on the twin's field rather than as `SimR`s.  The
proof is `Specs.lean`'s `inst1_get_run` minus the monad plumbing:
`HashMap2.get_refines_wf` under `CachesInv`'s `Inv` and the key type's
`Eq2Fwd`, then `CachesRel`'s clause at that table. -/

section Probes

variable {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}

/-- `arena::core::whnf_core_probe` against `lst.caches.whnfCoreC[·]?`. -/
theorem whnf_core_probe_abs (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {e : arena.handle.EIdx}
    {o : Option arena.handle.EIdx}
    (hrun : arena.core.whnf_core_probe st e = ok o) :
    o.map absEIdx = lst.caches.whnfCoreC[absEIdx e]? := by
  rw [arena.core.whnf_core_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hinv.caches.whnfCoreC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.whnfCoreC e trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2; rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::core::whnf_probe` against `lst.caches.whnfC[·]?`. -/
theorem whnf_probe_abs (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {e : arena.handle.EIdx}
    {o : Option arena.handle.EIdx}
    (hrun : arena.core.whnf_probe st e = ok o) :
    o.map absEIdx = lst.caches.whnfC[absEIdx e]? := by
  rw [arena.core.whnf_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hinv.caches.whnfC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.whnfC e trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2; rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::core::infer_probe` against `lst.caches.inferC[·]?`. -/
theorem infer_probe_abs (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {e : arena.handle.EIdx}
    {o : Option arena.handle.EIdx}
    (hrun : arena.core.infer_probe st e = ok o) :
    o.map absEIdx = lst.caches.inferC[absEIdx e]? := by
  rw [arena.core.infer_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hinv.caches.inferC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.inferC e trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2; rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::core::infer_io_probe` against `lst.caches.inferIOC[·]?` — the io
grade's OWN table (DESIGN §8.3 lesson 9). -/
theorem infer_io_probe_abs (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {e : arena.handle.EIdx}
    {o : Option arena.handle.EIdx}
    (hrun : arena.core.infer_io_probe st e = ok o) :
    o.map absEIdx = lst.caches.inferIOC[absEIdx e]? := by
  rw [arena.core.infer_io_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hinv.caches.inferIOC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.inferIOC e trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2; rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::core::annot_probe` against `lst.caches.annotC[·]?`. -/
theorem annot_probe_abs (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {e : arena.handle.EIdx}
    {o : Option arena.handle.EIdx}
    (hrun : arena.core.annot_probe st e = ok o) :
    o.map absEIdx = lst.caches.annotC[absEIdx e]? := by
  rw [arena.core.annot_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hinv.caches.annotC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.annotC e trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2; rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

/-- `arena::core_state::eidx_pair` against the twin's `(a, b)`: the `defeq`
memo's key is the ORDERED pair, and `dup2` is the identity on a handle. -/
theorem eidx_pair_abs {a b : arena.handle.EIdx} {k : arena.core_state.EIdxPair}
    (h : arena.core_state.eidx_pair a b = ok k) :
    absEIdxPair k = (absEIdx a, absEIdx b) := by
  rw [arena.core_state.eidx_pair] at h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hk : arena.core_state.EIdxPair.mk x y = k := Result.ok_injective h
  subst hk
  rw [dupId_eidx _ _ hx, dupId_eidx _ _ hy]
  rfl

/-- `arena::core::defeq_probe` against `lst.caches.defeqC[·]?` — the verdict
table, both signs (con-leche's `defeqC` stores the `Bool`). -/
theorem defeq_probe_abs (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.core_state.EIdxPair} {o : Option Bool}
    (hrun : arena.core.defeq_probe st k = ok o) :
    o = lst.caches.defeqC[absEIdxPair k]? := by
  rw [arena.core.defeq_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidxPair_eq2 hinv.caches.defeqC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.defeqC k trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option Bool) = o := Result.ok_injective hrun
    subst h2; rfl
  | some r =>
    rw [hrc] at hrun
    have h2 : (some r) = o := Result.ok_injective hrun
    subst h2; rfl

end Probes

/-! ## The six memo writes

`Specs.lean`'s `inst1_set_run` with the capacity branch in front of it, which
is `cache_insert_step`.  `SimS` is the shape: the writes cannot fail and the
store is untouched, so `Ext.refl` closes the last component and the
twenty-six other clauses of `AStateRel` / `AStateInv` ride along by the
structure-instance UPDATE idiom task #97-P5-1 §2 named. -/

section Writes

variable {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}

/-- `arena::core::whnf_core_set` against `Arena.whnfCoreSet`. -/
theorem whnf_core_set_run (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.whnf_core_set st e r = ok st') :
    SimS pers lst st' (Arena.whnfCoreSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.whnf_core_set] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm, hfit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with whnf_core_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step eidx_eq2 absEIdx_surj absEIdx_inj
    hinv.caches.whnfCoreC hrel.caches.whnfCoreC hn hfit hp
  exact SimS.mk (lst' := { lst with caches := { lst.caches with
      whnfCoreC := (if lst.caches.whnfCoreC.size < cacheCap then
        lst.caches.whnfCoreC else ∅).insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with whnfCoreC := h1 } }
    { hinv with caches := { hinv.caches with whnfCoreC := h2 } } (Ext.refl _)

/-- `arena::core::whnf_set` against `Arena.whnfSet`. -/
theorem whnf_set_run (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.whnf_set st e r = ok st') :
    SimS pers lst st' (Arena.whnfSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.whnf_set] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm, hfit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with whnf_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step eidx_eq2 absEIdx_surj absEIdx_inj
    hinv.caches.whnfC hrel.caches.whnfC hn hfit hp
  exact SimS.mk (lst' := { lst with caches := { lst.caches with
      whnfC := (if lst.caches.whnfC.size < cacheCap then
        lst.caches.whnfC else ∅).insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with whnfC := h1 } }
    { hinv with caches := { hinv.caches with whnfC := h2 } } (Ext.refl _)

/-- `arena::core::infer_set` against `Arena.inferSet`. -/
theorem infer_set_run (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.infer_set st e r = ok st') :
    SimS pers lst st' (Arena.inferSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.infer_set] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm, hfit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with infer_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step eidx_eq2 absEIdx_surj absEIdx_inj
    hinv.caches.inferC hrel.caches.inferC hn hfit hp
  exact SimS.mk (lst' := { lst with caches := { lst.caches with
      inferC := (if lst.caches.inferC.size < cacheCap then
        lst.caches.inferC else ∅).insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with inferC := h1 } }
    { hinv with caches := { hinv.caches with inferC := h2 } } (Ext.refl _)

/-- `arena::core::infer_io_set` against `Arena.inferIOSet`. -/
theorem infer_io_set_run (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.infer_io_set st e r = ok st') :
    SimS pers lst st' (Arena.inferIOSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.infer_io_set] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm, hfit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with infer_io_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step eidx_eq2 absEIdx_surj absEIdx_inj
    hinv.caches.inferIOC hrel.caches.inferIOC hn hfit hp
  exact SimS.mk (lst' := { lst with caches := { lst.caches with
      inferIOC := (if lst.caches.inferIOC.size < cacheCap then
        lst.caches.inferIOC else ∅).insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with inferIOC := h1 } }
    { hinv with caches := { hinv.caches with inferIOC := h2 } } (Ext.refl _)

/-- `arena::core::annot_set` against `Arena.annotSet`. -/
theorem annot_set_run (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.annot_set st e r = ok st') :
    SimS pers lst st' (Arena.annotSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.annot_set] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm, hfit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with annot_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step eidx_eq2 absEIdx_surj absEIdx_inj
    hinv.caches.annotC hrel.caches.annotC hn hfit hp
  exact SimS.mk (lst' := { lst with caches := { lst.caches with
      annotC := (if lst.caches.annotC.size < cacheCap then
        lst.caches.annotC else ∅).insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with annotC := h1 } }
    { hinv with caches := { hinv.caches with annotC := h2 } } (Ext.refl _)

/-- `arena::core::defeq_set` against `Arena.defeqSet` — the ORDERED pair key,
built by `eidx_pair` on the port's side and written inline by the twin. -/
theorem defeq_set_run (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {a b : arena.handle.EIdx} {v : Bool} {st'}
    (hrun : arena.core.defeq_set st a b v = ok st') :
    SimS pers lst st' (Arena.defeqSet (absEIdx a) (absEIdx b) v) := by
  rw [arena.core.defeq_set] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm, hfit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  have hst : st' = { st with caches := { st.caches with defeq_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step eidxPair_eq2 absEIdxPair_surj
    absEIdxPair_inj hinv.caches.defeqC hrel.caches.defeqC hn hfit hp
  rw [eidx_pair_abs hk] at h1
  exact SimS.mk (lst' := { lst with caches := { lst.caches with
      defeqC := (if lst.caches.defeqC.size < cacheCap then
        lst.caches.defeqC else ∅).insert (absEIdx a, absEIdx b) v } })
    rfl { hrel with caches := { hrel.caches with defeqC := h1 } }
    { hinv with caches := { hinv.caches with defeqC := h2 } } (Ext.refl _)

end Writes

/-! ## The axiom census

Three standard axioms and nothing else, `Specs.lean`'s rule: no `sorryAx` on a
closed lemma, and no `bv_decide` axiom — `relOn_size` is `List.Perm` and
`absU32_surj` is `omega` after `UInt32.toNat`. -/

section Axioms

/-- info: 'ConRon.Refine2.absU32_surj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms absU32_surj

/-- info: 'ConRon.Refine2.relOn_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relOn_size

/-- info: 'ConRon.Refine2.cache_insert_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cache_insert_step

/-- info: 'ConRon.Refine2.whnf_core_probe_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_core_probe_abs

/-- info: 'ConRon.Refine2.defeq_probe_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms defeq_probe_abs

/-- info: 'ConRon.Refine2.eidx_pair_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eidx_pair_abs

/-- info: 'ConRon.Refine2.whnf_core_set_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_core_set_run

/-- info: 'ConRon.Refine2.defeq_set_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms defeq_set_run

end Axioms

end ConRon.Refine2
