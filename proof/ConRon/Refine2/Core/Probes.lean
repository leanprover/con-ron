/-
# `ConRon.Refine2.Core.Probes` — the knot's six memo probes and six memo writes

**Task #97-P5-Core, floor 0.**  `Refine2/Specs.lean` closed the thirteen
per-call `Memos` tables; the knot reads and writes the *per-declaration*
`Caches` instead, and those seven pairs are not in `Specs.lean` because nothing
below the Core tier calls them.  This file is that floor: `whnf_core`,
`whnf_core_cheap` (the official `cheap_proj` mode's own table, task #109),
`whnf`, `infer`, `infer_io`, `annot` and `defeq`, probe and write.

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

## The writes are the memo tier's, with no capacity test

Until task #115 every `Caches` write carried a capacity branch (DESIGN §8.3's
former lesson 10, `if len < CACHE_CAP … else HashMap2::new()`), and matching
the port's branch to the twin's needed the two tables' SIZES to agree, a
bijection argument (`relOn_size`, the `*_surj` lemmas) that lived here.  The
cap is gone, as it never existed in con-leche, and with it that argument: a
write is `Specs.lean`'s `memo_insert_step` at the table.
-/
import ConRon.Refine2.Specs
import ConRon.Arena.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn sl_v toFun)

/-! ## The `Caches` key abstractions are injective -/

theorem absEIdxPair_inj : Function.Injective absEIdxPair := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [absEIdxPair, Prod.mk.injEq] at h
  simp [absEIdx_inj h.1, absEIdx_inj h.2]

theorem absNLsKey_inj : Function.Injective absNLsKey := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [absNLsKey, Prod.mk.injEq] at h
  simp [absNIdx_inj h.1, absLsIdx_inj h.2]

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
theorem whnf_core_probe_abs (hrel : AStateRel₀ pers st lst)
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

/-- `arena::core::whnf_core_cheap_probe` (the official `cheap_proj` mode's table) against `lst.caches.whnfCoreCheapC[·]?`. -/
theorem whnf_core_cheap_probe_abs (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {e : arena.handle.EIdx}
    {o : Option arena.handle.EIdx}
    (hrun : arena.core.whnf_core_cheap_probe st e = ok o) :
    o.map absEIdx = lst.caches.whnfCoreCheapC[absEIdx e]? := by
  rw [arena.core.whnf_core_cheap_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hinv.caches.whnfCoreCheapC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.whnfCoreCheapC e trivial
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
theorem whnf_probe_abs (hrel : AStateRel₀ pers st lst)
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
theorem infer_probe_abs (hrel : AStateRel₀ pers st lst)
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
theorem infer_io_probe_abs (hrel : AStateRel₀ pers st lst)
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
theorem annot_probe_abs (hrel : AStateRel₀ pers st lst)
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
theorem defeq_probe_abs (hrel : AStateRel₀ pers st lst)
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

/-- `arena::core_state::nls_key` against the twin's `(n, us)` — the
`constTyC` / `constValC` key, built by the port and written inline by the
twin, `eidx_pair_abs` one store over. -/
theorem nls_key_abs {n : arena.handle.NIdx} {us : arena.handle.LsIdx}
    {k : arena.core_state.NLsKey} (h : arena.core_state.nls_key n us = ok k) :
    absNLsKey k = (absNIdx n, absLsIdx us) := by
  rw [arena.core_state.nls_key] at h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hk : arena.core_state.NLsKey.mk x y = k := Result.ok_injective h
  subst hk
  rw [dupId_nidx _ _ hx, dupId_lsidx _ _ hy]
  rfl

/-- `arena::core::const_val_probe` against `lst.caches.constValC[·]?` — the
delta step's memo, the seventh probe of the tier (task #97-P5-Core-2). -/
theorem const_val_probe_abs (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.core_state.NLsKey}
    {o : Option arena.handle.EIdx}
    (hrun : arena.core.const_val_probe st k = ok o) :
    o.map absEIdx = lst.caches.constValC[absNLsKey k]? := by
  rw [arena.core.const_val_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nlsKey_eq2 hinv.caches.constValC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.constValC k trivial
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

end Probes

/-! ## The six memo writes

`Specs.lean`'s `inst1_set_run` at a `Caches` table: `memo_insert_step`.  `SimS₀` is the shape (task #97-P5-Core round 4: the
lockstep relation, no `Ext`): the writes cannot fail and the
twenty-six other clauses of `AStateRel` / `AStateInv` ride along by the
structure-instance UPDATE idiom task #97-P5-1 §2 named. -/

section Writes

variable {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}

/-- `arena::core::whnf_core_set` against `Arena.whnfCoreSet`. -/
theorem whnf_core_set_run (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.whnf_core_set st e r = ok st') :
    SimS₀ pers lst st' (Arena.whnfCoreSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.whnf_core_set] at hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with whnf_core_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj
    hinv.caches.whnfCoreC hrel.caches.whnfCoreC hp
  exact SimS₀.mk (lst' := { lst with caches := { lst.caches with
      whnfCoreC := lst.caches.whnfCoreC.insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with whnfCoreC := h1 } }
    { hinv with caches := { hinv.caches with whnfCoreC := h2 } }

/-- `arena::core::whnf_core_cheap_set` against `Arena.whnfCoreCheapSet`. -/
theorem whnf_core_cheap_set_run (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.whnf_core_cheap_set st e r = ok st') :
    SimS₀ pers lst st' (Arena.whnfCoreCheapSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.whnf_core_cheap_set] at hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with whnf_core_cheap_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj
    hinv.caches.whnfCoreCheapC hrel.caches.whnfCoreCheapC hp
  exact SimS₀.mk (lst' := { lst with caches := { lst.caches with
      whnfCoreCheapC := lst.caches.whnfCoreCheapC.insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with whnfCoreCheapC := h1 } }
    { hinv with caches := { hinv.caches with whnfCoreCheapC := h2 } }

/-- `arena::core::whnf_set` against `Arena.whnfSet`. -/
theorem whnf_set_run (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.whnf_set st e r = ok st') :
    SimS₀ pers lst st' (Arena.whnfSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.whnf_set] at hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with whnf_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj
    hinv.caches.whnfC hrel.caches.whnfC hp
  exact SimS₀.mk (lst' := { lst with caches := { lst.caches with
      whnfC := lst.caches.whnfC.insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with whnfC := h1 } }
    { hinv with caches := { hinv.caches with whnfC := h2 } }

/-- `arena::core::infer_set` against `Arena.inferSet`. -/
theorem infer_set_run (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.infer_set st e r = ok st') :
    SimS₀ pers lst st' (Arena.inferSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.infer_set] at hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with infer_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj
    hinv.caches.inferC hrel.caches.inferC hp
  exact SimS₀.mk (lst' := { lst with caches := { lst.caches with
      inferC := lst.caches.inferC.insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with inferC := h1 } }
    { hinv with caches := { hinv.caches with inferC := h2 } }

/-- `arena::core::infer_io_set` against `Arena.inferIOSet`. -/
theorem infer_io_set_run (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.infer_io_set st e r = ok st') :
    SimS₀ pers lst st' (Arena.inferIOSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.infer_io_set] at hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with infer_io_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj
    hinv.caches.inferIOC hrel.caches.inferIOC hp
  exact SimS₀.mk (lst' := { lst with caches := { lst.caches with
      inferIOC := lst.caches.inferIOC.insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with inferIOC := h1 } }
    { hinv with caches := { hinv.caches with inferIOC := h2 } }

/-- `arena::core::annot_set` against `Arena.annotSet`. -/
theorem annot_set_run (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {e r : arena.handle.EIdx} {st'}
    (hrun : arena.core.annot_set st e r = ok st') :
    SimS₀ pers lst st' (Arena.annotSet (absEIdx e) (absEIdx r)) := by
  rw [arena.core.annot_set] at hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1, dupId_eidx _ _ he2] at hp
  have hst : st' = { st with caches := { st.caches with annot_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj
    hinv.caches.annotC hrel.caches.annotC hp
  exact SimS₀.mk (lst' := { lst with caches := { lst.caches with
      annotC := lst.caches.annotC.insert (absEIdx e) (absEIdx r) } })
    rfl { hrel with caches := { hrel.caches with annotC := h1 } }
    { hinv with caches := { hinv.caches with annotC := h2 } }

/-- `arena::core::defeq_set` against `Arena.defeqSet` — the ORDERED pair key,
built by `eidx_pair` on the port's side and written inline by the twin. -/
theorem defeq_set_run (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {a b : arena.handle.EIdx} {v : Bool} {st'}
    (hrun : arena.core.defeq_set st a b v = ok st') :
    SimS₀ pers lst st' (Arena.defeqSet (absEIdx a) (absEIdx b) v) := by
  rw [arena.core.defeq_set] at hrun
  obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  have hst : st' = { st with caches := { st.caches with defeq_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidxPair_eq2 absEIdxPair_inj
    hinv.caches.defeqC hrel.caches.defeqC hp
  rw [eidx_pair_abs hk] at h1
  exact SimS₀.mk (lst' := { lst with caches := { lst.caches with
      defeqC := lst.caches.defeqC.insert (absEIdx a, absEIdx b) v } })
    rfl { hrel with caches := { hrel.caches with defeqC := h1 } }
    { hinv with caches := { hinv.caches with defeqC := h2 } }

/-- **`arena::core::const_val_set`, as a STATE equation** (task
#97-P5-Core-2).  The other six writes have a named twin (`Arena.whnfCoreSet`
and its five siblings); the delta step's memo does not — the twin writes it
INLINE in `constValAt` — so this one is stated as the pair of facts a caller
actually consumes, and `const_val_at_refines` spells the twin's `do` block
itself. -/
theorem const_val_set_rel (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.core_state.NLsKey}
    {r : arena.handle.EIdx} {st'}
    (hrun : arena.core.const_val_set st k r = ok st') :
    AStateRel₀ pers st'
        { lst with caches := { lst.caches with
          constValC := lst.caches.constValC.insert (absNLsKey k) (absEIdx r) } }
      ∧ AStateInv pers st' := by
  rw [arena.core.const_val_set] at hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1] at hp
  have hst : st' = { st with caches := { st.caches with const_val_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step nlsKey_eq2 absNLsKey_inj
    hinv.caches.constValC hrel.caches.constValC hp
  exact ⟨{ hrel with caches := { hrel.caches with constValC := h1 } },
    { hinv with caches := { hinv.caches with constValC := h2 } }⟩

end Writes

/-! ## The axiom census

Three standard axioms and nothing else, `Specs.lean`'s rule: no `sorryAx` on a
closed lemma, and no `bv_decide` axiom. -/

section Axioms

/-- info: 'ConRon.Refine2.whnf_core_probe_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_core_probe_abs

/-- info: 'ConRon.Refine2.defeq_probe_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms defeq_probe_abs

/-- info: 'ConRon.Refine2.eidx_pair_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eidx_pair_abs

/-- info: 'ConRon.Refine2.whnf_core_set_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_core_set_run

/-- info: 'ConRon.Refine2.whnf_core_cheap_probe_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_core_cheap_probe_abs

/-- info: 'ConRon.Refine2.whnf_core_cheap_set_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_core_cheap_set_run

/-- info: 'ConRon.Refine2.defeq_set_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms defeq_set_run

/-- info: 'ConRon.Refine2.const_val_probe_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms const_val_probe_abs

/-- info: 'ConRon.Refine2.const_val_set_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms const_val_set_rel

end Axioms

end ConRon.Refine2
