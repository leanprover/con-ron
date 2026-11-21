/-
# `ConRon.Refine2.Modular.ReachParts` — `modular/reach.rs`: the parts, the views, the record reads

**Task #166, Theorem 2.**  The reach's reads against the twin's (`Arena/Modular/Reach.lean`).
The store-free functions are equations under the abstractions of `ReachRel.lean`; the ones that
reach a file read claim their accept (`ACS`, `AS`).  The cache lookups the twin fails on
(`cacheLost`) claim their `Ok` only.

**Casts.**  A load position read back as a `usize` keeps its value: it is a position of the
load order (`ReachEnvRel.fits`); a copy's fields fit (`FirstRel.fits`).
-/
import ConRon.Refine2.Modular.ReachRel

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.modular.reach

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Modular

open ConRon.Arena
open ConRon.Refine2.Frontend.Olean
open ConRon.Refine.HashMap2 (Inv toFun)
open ConLeche.Frontend.Olean (OLeanLevel CEntryF CKindF)

/-! ## Maps related pointwise -/

theorem NMapRel.congr {V V' : Type} {A : V → V'} {m : ron.hashmap2.HashMap2 arena.handle.NIdx V}
    {s t : _root_.Std.HashMap NIdx V'} (h : NMapRel A m s) (e : ∀ k : NIdx, s[k]? = t[k]?) :
    NMapRel A m t :=
  ⟨h.inv, fun k => (h.get k).trans (e _)⟩

theorem PMapRel.congr {V V' : Type} {R : V → V' → Prop}
    {m : ron.hashmap2.HashMap2 frontend.modular.reach.PartKey V}
    {s t : _root_.Std.HashMap ConRon.Arena.Modular.PartKey V'} (h : PMapRel R m s)
    (e : ∀ k : ConRon.Arena.Modular.PartKey, s[k]? = t[k]?) : PMapRel R m t :=
  ⟨h.inv, fun k => by rw [← e]; exact h.get k⟩

/-- An `Option.Rel`, by its two cases. -/
theorem orel_cases {V V' : Type} {R : V → V' → Prop} {a : Option V} {b : Option V'}
    (h : Option.Rel R a b) : (a = none ∧ b = none) ∨ ∃ x y, a = some x ∧ b = some y ∧ R x y := by
  cases h with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some hr => exact Or.inr ⟨_, _, rfl, rfl, hr⟩

/-! ## A view's keys and steps -/

/-- The twin's step of `viewKeys`' tail. -/
@[reducible] def vkF (p : NIdx × ConLeche.Frontend.Olean.LoadFlags) : ConRon.Arena.Modular.PartKey :=
  ⟨p.1, p.2.level⟩

theorem view_keys_loop_eq (order : alloc.vec.Vec arena.handle.NIdx)
    (flags : alloc.vec.Vec frontend.olean.levels.LoadFlags)
    (out : alloc.vec.Vec frontend.modular.reach.PartKey) (i : Std.Usize) {o}
    (h : view_keys_loop order flags out i = ok o) :
      o.val.map absPartKey = out.val.map absPartKey ++
        (((order.val.map absNIdx).zip (flags.val.map absLoadFlags)).drop i.val).map vkF := by
  rw [view_keys_loop] at h
  by_cases h1 : i < alloc.vec.Vec.len order
  · rw [ite_eq_left h1] at h
    by_cases h2 : i < alloc.vec.Vec.len flags
    · rw [ite_eq_left h2] at h
      have hi1 := lt_of_lt_len h1
      have hi2 := lt_of_lt_len h2
      peel h as n, hn
      obtain ⟨_, rfl⟩ := vec_index_eq hn
      peel h as n1, hn1
      cases nidx_dup2_ok hn1
      peel h as lf, hlf
      obtain ⟨_, rfl⟩ := vec_index_eq hlf
      peel h as ol, hol
      peel h as out1, hout1
      peel h as i3, hi3
      rw [view_keys_loop_eq order flags out1 i3 h, ConRon.Refine.vec_push_val hout1, usize_succ hi3]
      have hz : i.val < ((order.val.map absNIdx).zip (flags.val.map absLoadFlags)).length := by
        simp [List.length_zip]; omega
      rw [List.drop_eq_getElem_cons hz]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append, List.getElem_zip, List.getElem_map]
      congr 2
      simp only [absPartKey, vkF, load_flags_level_eq hol]
    · rw [ite_eq_right h2] at h
      cases Result.ok_injective h
      have := lt_of_not_lt_len h2
      rw [List.drop_of_length_le (by simp [List.length_zip]; omega)]
      simp
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    have := lt_of_not_lt_len h1
    rw [List.drop_of_length_le (by simp [List.length_zip]; omega)]
    simp
termination_by order.val.length - i.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hi3
  omega

/-- **`view_keys` is `viewKeys`.** -/
theorem view_keys_eq {h : arena.handle.NIdx} {ld : frontend.olean.levels.HeaderLoads}
    {ld' : Arena.Frontend.Olean.HeaderLoads} (hld : HeaderLoadsRel ld ld') {o}
    (hv : view_keys h ld = ok o) : o.val.map absPartKey = ConRon.Arena.Modular.viewKeys (absNIdx h) ld' := by
  rw [view_keys] at hv
  peel hv as i1, hi1
  peel hv as k, hk
  peel hv as out1, hout1
  have e0 : (alloc.vec.Vec.with_capacity frontend.modular.reach.PartKey i1).val = [] := rfl
  rw [view_keys_loop_eq _ _ out1 0#usize hv, ConRon.Refine.vec_push_val hout1, e0,
    ConRon.Arena.Modular.viewKeys, Array.toList_zip, ← hld.order, ← hld.flags]
  simp only [List.nil_append, List.map_cons, List.map_nil, (priv_key_eq hk).2, List.cons_append]
  rfl

/-- The twin's step of `viewStep`. -/
@[reducible] def vsF (k : ConRon.Arena.Modular.PartKey) (v : _root_.Std.HashMap NIdx ConRon.Arena.Modular.Spot)
    (q : Arena.Frontend.Olean.NamePosition) : _root_.Std.HashMap NIdx ConRon.Arena.Modular.Spot :=
  if v.contains q.name then v else v.insert q.name ⟨k, q⟩

theorem viewStep_eq (v : _root_.Std.HashMap NIdx ConRon.Arena.Modular.Spot)
    (k : ConRon.Arena.Modular.PartKey) (t : frontend.olean.reads.NamePositions) :
    ConRon.Arena.Modular.viewStep v k (absNamePositions t) =
      (t.consts.val.map absNamePosition).foldl (vsF k) v := by
  unfold ConRon.Arena.Modular.viewStep
  rw [← Array.foldl_toList]
  rfl

theorem view_step_loop_rel (k : frontend.modular.reach.PartKey) (t : frontend.olean.reads.NamePositions)
    (v : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.modular.reach.Spot)
    (V : _root_.Std.HashMap NIdx ConRon.Arena.Modular.Spot) (i : Std.Usize) {o}
    (hv : NMapRel absSpot v V) (h : view_step_loop v k t i = ok o) :
      NMapRel absSpot o (((t.consts.val.drop i.val).map absNamePosition).foldl (vsF (absPartKey k)) V) := by
  rw [view_step_loop] at h
  by_cases h1 : i < alloc.vec.Vec.len t.consts
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as np, hnp
    obtain ⟨_, rfl⟩ := vec_index_eq hnp
    peel h as b, hb
    have eb := hv.contains_eq hb
    peel h as v1, hv1
    peel h as i2, hi2
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldl_cons, ← usize_succ hi2]
    refine view_step_loop_rel k t v1 _ i2 ?_ h
    simp only [vsF, absNamePosition_name, ← eb]
    by_cases hb' : b = true
    · rw [ite_eq_left hb'] at hv1
      cases Result.ok_injective hv1
      simpa [hb'] using hv
    · rw [ite_eq_right hb'] at hv1
      peel hv1 as n, hn
      cases nidx_dup2_ok hn
      peel hv1 as pk, hpk
      cases partKey_dup2_ok hpk
      peel hv1 as np1, hnp1
      cases name_position_dup_ok hnp1
      peel hv1 as q, hq
      obtain ⟨_, m2⟩ := q
      cases Result.ok_injective hv1
      simpa [hb'] using hv.insert hq
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    simpa using hv
termination_by t.consts.val.length - i.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hi2
  omega

/-- **`view_step` is `viewStep`.** -/
theorem view_step_rel {v : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.modular.reach.Spot}
    {V : _root_.Std.HashMap NIdx ConRon.Arena.Modular.Spot} (hv : NMapRel absSpot v V)
    {k : frontend.modular.reach.PartKey} {t : frontend.olean.reads.NamePositions} {o}
    (h : view_step v k t = ok o) :
    NMapRel absSpot o (ConRon.Arena.Modular.viewStep V (absPartKey k) (absNamePositions t)) := by
  rw [viewStep_eq]
  simpa using view_step_loop_rel k t v V 0#usize hv h

/-! ## The index's tables -/

/-- A load position fits a `usize`. -/
theorem load_pos_fits {ld : frontend.olean.levels.HeaderLoads} {ld' : Arena.Frontend.Olean.HeaderLoads}
    (hld : HeaderLoadsRel ld ld') (hf : IndexFits ld') {m : NIdx} {j : Nat}
    (hj : ld'.index[m]? = some j) : j ≤ Std.Usize.max := by
  have h1 := hf m j hj
  have h2 : ld'.order.size = ld.order.val.length := by
    rw [← Array.length_toList, ← hld.order]; simp
  have := vec_len_le_max ld.order
  omega

/-- **`index_table` is `indexTable`.** -/
theorem index_table_eq {wr : frontend.olean.index.WorkerReads} {W : Arena.Frontend.Olean.WorkerReads}
    (hwr : WorkerReadsRel wr W) (hf : IndexFits W.loads) {k : frontend.modular.reach.PartKey} {o}
    (h : index_table wr k = ok o) :
    o.map absNamePositions = ConRon.Arena.Modular.indexTable W (absPartKey k) := by
  rw [index_table] at h
  peel h as o0, ho0
  have e0 := hwr.loads.index.get_eq ho0
  rw [ConRon.Arena.Modular.indexTable]
  cases o0 with
  | none =>
    cases Result.ok_injective h
    simp only [← e0, Option.map_none]
  | some i =>
    simp only [← e0, Option.map_some]
    have hfit := load_pos_fits hwr.loads hf e0.symm
    peel h as ol, hol
    have el := header_loads_level_at_eq hwr.loads hfit hol
    peel h as i1, hi1
    peel h as i2, hi2
    have v1 := level_index_val hi1
    have v2 := level_index_val hi2
    by_cases e : i1 = i2
    · rw [ite_eq_left e] at h
      have elv : ol = k.level := levelIdx_inj (by rw [← v1, ← v2, e])
      rw [← el, elv, beq_self_eq_true, ite_eq_left rfl]
      peel h as j, hj
      have ej : j.val = i.val := by rw [← Result.ok_injective hj]; exact cast_usize_val hfit
      have hp : W.index.parts[i.val]? = (wr.index.parts.val[i.val]?).map absNamePositions := by
        have := congrArg (·[i.val]?) hwr.index.parts
        simp only [List.getElem?_map] at this
        rw [← Array.getElem?_toList]; exact this.symm
      rw [hp]
      by_cases hl : j < alloc.vec.Vec.len wr.index.parts
      · rw [ite_eq_left hl] at h
        have hl' := lt_of_lt_len hl
        peel h as np, hnp
        obtain ⟨_, rfl⟩ := vec_index_eq hnp
        cases Result.ok_injective h
        rw [← ej, List.getElem?_eq_getElem hl']
      · rw [ite_eq_right hl] at h
        cases Result.ok_injective h
        have := lt_of_not_lt_len hl
        rw [ej] at this
        rw [List.getElem?_eq_none this]
    · rw [ite_eq_right e] at h
      cases Result.ok_injective h
      have : ol ≠ k.level := fun he => e (UScalar.eq_of_val_eq (by rw [v1, v2, he]))
      have : absLevel ol ≠ absLevel k.level := fun he => this (absLevel_inj he)
      rw [← el]
      simp [this]

/-- **`table_get` is `tableGet`.** -/
theorem table_get_eq {wr : frontend.olean.index.WorkerReads} {W : Arena.Frontend.Olean.WorkerReads}
    (hwr : WorkerReadsRel wr W) (hf : IndexFits W.loads) {c : frontend.modular.reach.ReachCache}
    {C : ConRon.Arena.Modular.ReachCache} (hc : ReachCacheRel c C) {k : frontend.modular.reach.PartKey} {o}
    (h : table_get wr c k = ok o) :
    o.map absNamePositions = ConRon.Arena.Modular.tableGet W C (absPartKey k) := by
  rw [table_get] at h
  peel h as o0, ho0
  have e0 := hc.tables.get_eq ho0
  rw [ConRon.Arena.Modular.tableGet]
  rcases orel_cases e0 with ⟨rfl, he⟩ | ⟨x, y, rfl, he, hr⟩
  · rw [he]
    exact index_table_eq hwr hf h
  · rw [he]
    cases Result.ok_injective h
    simp [hr]

/-! ## Lookups -/

theorem lookBuild_eq (t : frontend.olean.reads.NamePositions) :
    ConRon.Arena.Modular.lookBuild (absNamePositions t) =
      (t.consts.val.map absNamePosition).foldl (fun (l : _root_.Std.HashMap NIdx _) q => l.insert q.name q) {} := by
  unfold ConRon.Arena.Modular.lookBuild
  rw [← Array.foldl_toList]
  rfl

theorem look_build_loop_rel (v : alloc.vec.Vec frontend.olean.reads.NamePosition)
    (l : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.olean.reads.NamePosition)
    (L : _root_.Std.HashMap NIdx Arena.Frontend.Olean.NamePosition) (i : Std.Usize) {o}
    (hl : NMapRel absNamePosition l L) (h : look_build_loop v l i = ok o) :
      NMapRel absNamePosition o
        (((v.val.drop i.val).map absNamePosition).foldl (fun (l : _root_.Std.HashMap NIdx _) q => l.insert q.name q) L) := by
  rw [look_build_loop] at h
  by_cases h1 : i < alloc.vec.Vec.len v
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as np, hnp
    obtain ⟨_, rfl⟩ := vec_index_eq hnp
    peel h as n, hn
    cases nidx_dup2_ok hn
    peel h as np1, hnp1
    cases name_position_dup_ok hnp1
    peel h as q, hq
    obtain ⟨_, l1⟩ := q
    peel h as i2, hi2
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldl_cons, ← usize_succ hi2]
    refine look_build_loop_rel v l1 _ i2 ?_ h
    simpa using hl.insert hq
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    simpa using hl
termination_by v.val.length - i.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hi2
  omega

/-- **`look_build` is `lookBuild`.** -/
theorem look_build_rel {t : frontend.olean.reads.NamePositions} {o} (h : look_build t = ok o) :
    NMapRel absNamePosition o (ConRon.Arena.Modular.lookBuild (absNamePositions t)) := by
  rw [look_build] at h
  peel h as l, hl
  rw [lookBuild_eq]
  simpa using look_build_loop_rel t.consts l {} 0#usize (NMapRel.with_capacity hl) h

/-- **`look_at`'s `Ok` is `lookAt`'s.** -/
theorem look_at_eq {c : frontend.modular.reach.ReachCache} {C : ConRon.Arena.Modular.ReachCache}
    (hc : ReachCacheRel c C) {k : frontend.modular.reach.PartKey} {n : arena.handle.NIdx} {o}
    (h : look_at c k n = ok (.Ok o)) (lst : AState) :
    (ConRon.Arena.Modular.lookAt C (absPartKey k) (absNIdx n)).run lst =
      .ok (o.map absNamePosition, lst) := by
  rw [look_at] at h
  peel h as o0, ho0
  have e0 := hc.looks.get_eq ho0
  rcases orel_cases e0 with ⟨rfl, -⟩ | ⟨l, L, rfl, he, hr⟩
  · peel h as ce, -
    cases Result.ok_injective h
  · rw [ConRon.Arena.Modular.lookAt, he]
    dsimp only
    peel h as o1, ho1
    have e1 := hr.get_eq ho1
    cases o1 with
    | none =>
      cases Result.ok_injective h
      rw [← e1]; rfl
    | some q =>
      peel h as np, hnp
      cases name_position_dup_ok hnp
      cases Result.ok_injective h
      rw [← e1]; rfl

/-! ## Views, located copies, the importer's copies -/

/-- **`view_at`'s `Ok` is `viewAt`'s.** -/
theorem view_at_eq {c : frontend.modular.reach.ReachCache} {C : ConRon.Arena.Modular.ReachCache}
    (hc : ReachCacheRel c C) {h y : arena.handle.NIdx} {o}
    (hv : view_at c h y = ok (.Ok o)) (lst : AState) :
    (ConRon.Arena.Modular.viewAt C (absNIdx h) (absNIdx y)).run lst = .ok (o.map absSpot, lst) := by
  rw [view_at] at hv
  peel hv as o0, ho0
  have e0 := hc.views.get_eq ho0
  rcases orel_cases e0 with ⟨rfl, -⟩ | ⟨v, V, rfl, he, hr⟩
  · peel hv as ce, -
    cases Result.ok_injective hv
  · rw [ConRon.Arena.Modular.viewAt, he]
    dsimp only
    peel hv as o1, ho1
    have e1 := hr.get_eq ho1
    cases o1 with
    | none =>
      cases Result.ok_injective hv
      rw [← e1]; rfl
    | some s =>
      peel hv as s1, hs1
      cases spot_dup_ok hs1
      cases Result.ok_injective hv
      rw [← e1]; rfl

/-- **`located_at` is `locatedAt`.** -/
theorem located_at_eq {c : frontend.modular.reach.ReachCache} {C : ConRon.Arena.Modular.ReachCache}
    (hc : ReachCacheRel c C) {y : arena.handle.NIdx} {o} (h : located_at c y = ok o) :
    o.map absSpot = ConRon.Arena.Modular.locatedAt C (absNIdx y) := by
  rw [located_at] at h
  peel h as o0, ho0
  have e0 := hc.located.get_eq ho0
  rw [ConRon.Arena.Modular.locatedAt, ← e0]
  cases o0 with
  | none => cases Result.ok_injective h; rfl
  | some s =>
    peel h as s1, hs1
    cases spot_dup_ok hs1
    cases Result.ok_injective h
    rfl

/-- **`importer_spot` is `importerSpot`.** -/
theorem importer_spot_eq {pk : frontend.olean.spec.OleanPins} {wr : frontend.olean.index.WorkerReads}
    {env' : ConRon.Arena.Modular.ReachEnv} (hwr : WorkerReadsRel wr env'.wr) {y : arena.handle.NIdx} {o}
    (h : importer_spot pk wr y = ok o) :
    o.map (fun p => (p.1.val, absSpot p.2)) =
      ConRon.Arena.Modular.importerSpot (absPins pk) env' (absNIdx y) := by
  rw [importer_spot] at h
  peel h as o0, ho0
  obtain ⟨e0, hfit⟩ := hwr.index.first.get_eq ho0
  rw [ConRon.Arena.Modular.importerSpot, ← e0]
  cases o0 with
  | none => cases Result.ok_injective h; rfl
  | some cp =>
    have hc := hfit cp rfl
    peel h as o1, ho1
    have e1 := name_index_at_eq hwr.index hc ho1
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, ← e1]
    cases o1 with
    | none => cases Result.ok_injective h; rfl
    | some q =>
      peel h as n, hn
      have en := header_loads_name_at_eq hwr.loads hc.1 hn
      peel h as ol, hol
      have el := header_loads_level_at_eq hwr.loads hc.1 hol
      peel h as np, hnp
      cases name_position_dup_ok hnp
      cases Result.ok_injective h
      simp only [Option.map_some, Option.bind_some, absSpot, absPartKey, en, el]
      rfl

/-- **`record_spot` is `recordSpot`.** -/
theorem record_spot_eq {pk : frontend.olean.spec.OleanPins} {wr : frontend.olean.index.WorkerReads}
    {env' : ConRon.Arena.Modular.ReachEnv} (hwr : WorkerReadsRel wr env'.wr)
    {c : frontend.modular.reach.ReachCache} {C : ConRon.Arena.Modular.ReachCache}
    (hc : ReachCacheRel c C) {x : arena.handle.NIdx} {o} (h : record_spot pk wr c x = ok o) :
    o.map (fun p => (absSpot p.1, p.2)) =
      ConRon.Arena.Modular.recordSpot (absPins pk) env' C (absNIdx x) := by
  rw [record_spot] at h
  peel h as o0, ho0
  have e0 := importer_spot_eq hwr ho0
  rw [ConRon.Arena.Modular.recordSpot, ← e0]
  cases o0 with
  | some p =>
    cases Result.ok_injective h
    rfl
  | none =>
    peel h as o1, ho1
    have e1 := located_at_eq hc ho1
    simp only [Option.map_none, ← e1]
    cases o1 with
    | none => cases Result.ok_injective h; rfl
    | some s => cases Result.ok_injective h; rfl

end ConRon.Refine2.Modular
