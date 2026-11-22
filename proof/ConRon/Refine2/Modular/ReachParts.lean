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
import ConRon.Refine2.Frontend.Olean.Group
import ConRon.Refine2.Checker.Axioms
import ConRon.Refine2.Core.LS.Lits

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

/-! ## Recursor blocks -/

/-- A vector's element at `0`: its head. -/
theorem vec_index_zero_cons {α : Type} {v : alloc.vec.Vec α} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v 0#usize = ok x) :
    ∃ t, v.val = x :: t := by
  obtain ⟨hl, rfl⟩ := vec_index_eq h
  refine ⟨v.val.drop ((0#usize : Std.Usize).val + 1), ?_⟩
  rw [List.getElem_cons_drop]
  rfl

/-- **`rec_blocks_add` is `recBlocksAdd`.** -/
theorem rec_blocks_add_rel {m : ron.hashmap2.HashMap2 arena.handle.NIdx (alloc.vec.Vec Std.U64)}
    {M : _root_.Std.HashMap NIdx (_root_.Array Nat)} (hm : NMapRel absLocs m M) {l : Std.U64}
    {k : frontend.olean.spec.CKindF arena.handle.NIdx Unit} {k' : CKindF NIdx Unit}
    (hk : KindNamesRel k k') {o} (h : rec_blocks_add m l k = ok o) :
    NMapRel absLocs o (ConRon.Arena.Modular.recBlocksAdd M l.val k') := by
  unfold rec_blocks_add at h
  cases k <;> cases k' <;> simp only [KindNamesRel, KindRel] at hk
  all_goals try (cases Result.ok_injective h; exact hm)
  rename_i all np ni nmo nmi rules k2 iu all' np' ni' nmo' nmi' rules' k2' iu'
  obtain ⟨hall, -⟩ := hk
  dsimp only at h
  by_cases h0 : alloc.vec.Vec.len all > 0#usize
  · rw [ite_eq_left h0] at h
    have h0' : 0 < all.val.length := by
      have : (0#usize : Std.Usize).val < (alloc.vec.Vec.len all).val := h0
      simpa [vec_len_val] using this
    peel h as n, hn
    obtain ⟨t, ht⟩ := vec_index_zero_cons hn
    peel h as q, hq
    obtain ⟨old, m1⟩ := q
    obtain ⟨eold, hm1⟩ := hm.remove hq
    peel h as xs, hxs
    peel h as xs1, hxs1
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as q2, hq2
    obtain ⟨_, m2⟩ := q2
    cases Result.ok_injective h
    have ha : all' = absNIdx n :: t.map absNIdx := by rw [← hall, ht]; rfl
    rw [ha]
    simp only [ConRon.Arena.Modular.recBlocksAdd]
    have hv : absLocs xs1 = ((M[absNIdx n]?).getD #[]).push l.val := by
      rw [← eold]
      have e1 := ConRon.Refine.vec_push_val hxs1
      cases old with
      | none =>
        cases Result.ok_injective hxs
        simp [absLocs, e1, alloc.vec.Vec.new]
      | some ys =>
        cases Result.ok_injective hxs
        simp [absLocs, e1]
    refine NMapRel.congr (by simpa [hv] using hm1.insert hq2) fun k1 => ?_
    simp only [_root_.Std.HashMap.getElem?_insert, _root_.Std.HashMap.getElem?_erase]
    split <;> simp [*]
  · rw [ite_eq_right h0] at h
    cases Result.ok_injective h
    have : all.val = [] := by
      have : ¬ (0#usize : Std.Usize).val < (alloc.vec.Vec.len all).val := h0
      simpa [vec_len_val] using this
    rw [← hall, this]
    exact hm

/-! ## A group's parts -/

/-- The constructors an entry lists, the Rust's. -/
def rCtors (e : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx) : List NIdx :=
  match e.kind with
  | .Induct _ _ _ cs _ _ _ _ => cs.val.map absNIdx
  | _ => []

theorem rCtors_groupCtorNames {l : List (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {l' : List (CEntryF NIdx EIdx)} (h : List.Forall₂ (EntryRel absNIdx absEIdx ValRel) l l') :
    l.flatMap rCtors = ConRon.Arena.Modular.groupCtorNames l' := by
  induction h with
  | nil => rfl
  | @cons a b _ _ he _ ih =>
    simp only [ConRon.Arena.Modular.groupCtorNames] at ih ⊢
    rw [List.flatMap_cons, List.flatMap_cons, ih]
    congr 1
    have hk := he.kind
    unfold rCtors
    generalize a.kind = ak at hk ⊢
    generalize b.kind = bk at hk ⊢
    cases ak <;> cases bk <;> simp only [KindRel] at hk <;> first | rfl | exact hk.2.2.2.1

theorem group_ctor_names_loop0_loop0_eq (out cs : alloc.vec.Vec arena.handle.NIdx) (j : Std.Usize) {o}
    (h : group_ctor_names_loop0_loop0 out cs j = ok o) : o.val = out.val ++ cs.val.drop j.val := by
  rw [group_ctor_names_loop0_loop0] at h
  by_cases h1 : j < alloc.vec.Vec.len cs
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as out1, hout1
    peel h as j1, hj1
    rw [group_ctor_names_loop0_loop0_eq out1 cs j1 h, ConRon.Refine.vec_push_val hout1, usize_succ hj1,
      List.drop_eq_getElem_cons hi]
    simp
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    simp
termination_by cs.val.length - j.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hj1
  omega

theorem group_ctor_names_loop0_eq
    (tys : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx))
    (out : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) {o}
    (h : group_ctor_names_loop0 tys out i = ok o) :
    o.val.map absNIdx = out.val.map absNIdx ++ (tys.val.drop i.val).flatMap rCtors := by
  rw [group_ctor_names_loop0] at h
  by_cases h1 : i < alloc.vec.Vec.len tys
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as cf, hcf
    obtain ⟨_, rfl⟩ := vec_index_eq hcf
    rw [List.drop_eq_getElem_cons hi, List.flatMap_cons]
    split at h
    all_goals first
      | (rename_i cs _ _ _ _ heq
         have hr : rCtors tys.val[i.val] = cs.val.map absNIdx := by simp only [rCtors, heq]
         peel h as out1, hout1
         peel h as i2, hi2
         rw [hr, group_ctor_names_loop0_eq tys out1 i2 h, group_ctor_names_loop0_loop0_eq _ _ _ hout1,
           usize_succ hi2]
         simp)
      | (rename_i heq
         have hr : rCtors tys.val[i.val] = [] := by simp only [rCtors, heq]
         peel h as i2, hi2
         rw [hr, group_ctor_names_loop0_eq tys out i2 h, usize_succ hi2]
         simp)
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    simp
termination_by tys.val.length - i.val
decreasing_by
  all_goals
    have := lt_of_lt_len h1
    have := usize_succ hi2
    omega

/-- **`group_ctor_names` is `groupCtorNames`.** -/
theorem group_ctor_names_eq
    {tys : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {tys' : List (CEntryF NIdx EIdx)} (hr : List.Forall₂ (EntryRel absNIdx absEIdx ValRel) tys.val tys')
    {o} (h : group_ctor_names tys = ok o) :
    o.val.map absNIdx = ConRon.Arena.Modular.groupCtorNames tys' := by
  rw [group_ctor_names] at h
  rw [group_ctor_names_loop0_eq _ _ _ h, ← rCtors_groupCtorNames hr]
  simp [alloc.vec.Vec.new]

theorem group_rec_locs_loop_eq (xs out : alloc.vec.Vec Std.U64) (i : Std.Usize) {o}
    (h : group_rec_locs_loop xs out i = ok o) : o.val = out.val ++ xs.val.drop i.val := by
  rw [group_rec_locs_loop] at h
  by_cases h1 : i < alloc.vec.Vec.len xs
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    peel h as out1, hout1
    peel h as i3, hi3
    rw [group_rec_locs_loop_eq xs out1 i3 h, ConRon.Refine.vec_push_val hout1, usize_succ hi3,
      List.drop_eq_getElem_cons hi]
    simp
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    simp
termination_by xs.val.length - i.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hi3
  omega

/-- **`group_rec_locs` is `groupRecLocs`.** -/
theorem group_rec_locs_eq {rb : ron.hashmap2.HashMap2 arena.handle.NIdx (alloc.vec.Vec Std.U64)}
    {RB : _root_.Std.HashMap NIdx (_root_.Array Nat)} (hrb : NMapRel absLocs rb RB)
    {all : alloc.vec.Vec arena.handle.NIdx} {o} (h : group_rec_locs rb all = ok o) :
    o.val.map (·.val) = ConRon.Arena.Modular.groupRecLocs RB (all.val.map absNIdx) := by
  rw [group_rec_locs] at h
  rw [ConRon.Arena.Modular.groupRecLocs]
  by_cases h0 : alloc.vec.Vec.len all = 0#usize
  · rw [ite_eq_left h0] at h
    cases Result.ok_injective h
    have : all.val = [] := by
      have := congrArg (·.val) h0
      simp only [vec_len_val] at this
      exact List.eq_nil_of_length_eq_zero this
    simp [this, alloc.vec.Vec.new]
  · rw [ite_eq_right h0] at h
    peel h as n, hn
    obtain ⟨t, ht⟩ := vec_index_zero_cons hn
    peel h as o0, ho0
    have e0 := hrb.get_eq ho0
    have ha : (all.val.map absNIdx).head? = some (absNIdx n) := by rw [ht]; rfl
    rw [ha, Option.bind_some, ← e0]
    cases o0 with
    | none => cases Result.ok_injective h; simp [alloc.vec.Vec.new]
    | some xs =>
      rw [group_rec_locs_loop_eq _ _ _ h]
      simp [alloc.vec.Vec.with_capacity, absLocs]

/-! ## Lookups of several names -/

/-- **`look_loc` is a lookup's location.** -/
theorem look_loc_eq {l : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.olean.reads.NamePosition}
    {L : _root_.Std.HashMap NIdx Arena.Frontend.Olean.NamePosition} (hl : NMapRel absNamePosition l L)
    {n : arena.handle.NIdx} {o} (h : look_loc l n = ok o) :
    o.map (·.val) = (L[absNIdx n]?).map (·.loc) := by
  rw [look_loc] at h
  peel h as o0, ho0
  rw [← hl.get_eq ho0]
  cases o0 <;> cases Result.ok_injective h <;> rfl

theorem look_locs_in_loop_eq {l : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.olean.reads.NamePosition}
    {L : _root_.Std.HashMap NIdx Arena.Frontend.Olean.NamePosition} (hl : NMapRel absNamePosition l L)
    (ns : alloc.vec.Vec arena.handle.NIdx) (out : alloc.vec.Vec Std.U64) (i : Std.Usize) {o}
    (h : look_locs_in_loop l ns out i = ok o) :
    o.map (fun v => v.val.map (·.val)) =
      (((ns.val.drop i.val).map absNIdx).mapM fun n => (L[n]?).map (·.loc)).map
        (out.val.map (·.val) ++ ·) := by
  rw [look_locs_in_loop] at h
  by_cases h1 : i < alloc.vec.Vec.len ns
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    peel h as o0, ho0
    have e0 := look_loc_eq hl ho0
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.mapM_cons, ← e0]
    cases o0 with
    | none => cases Result.ok_injective h; rfl
    | some x =>
      peel h as out1, hout1
      peel h as i2, hi2
      have ih := look_locs_in_loop_eq hl ns out1 i2 h
      rw [usize_succ hi2, ConRon.Refine.vec_push_val hout1] at ih
      rw [ih]
      cases (((ns.val.drop (i.val + 1)).map absNIdx).mapM fun n => (L[n]?).map (·.loc)) <;> simp
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    simp
termination_by ns.val.length - i.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hi2
  omega

/-- **`look_locs_in` is `ns.mapM (look[·]?)`.** -/
theorem look_locs_in_eq {l : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.olean.reads.NamePosition}
    {L : _root_.Std.HashMap NIdx Arena.Frontend.Olean.NamePosition} (hl : NMapRel absNamePosition l L)
    {ns : alloc.vec.Vec arena.handle.NIdx} {o} (h : look_locs_in l ns = ok o) :
    o.map (fun v => v.val.map (·.val)) = (ns.val.map absNIdx).mapM fun n => (L[n]?).map (·.loc) := by
  rw [look_locs_in] at h
  rw [look_locs_in_loop_eq hl _ _ _ h]
  have e0 : (alloc.vec.Vec.with_capacity Std.U64 (alloc.vec.Vec.len ns)).val = [] := rfl
  rw [e0]
  simp

/-- **`look_locs`' `Ok` is `lookLocs`'.** -/
theorem look_locs_eq {c : frontend.modular.reach.ReachCache} {C : ConRon.Arena.Modular.ReachCache}
    (hc : ReachCacheRel c C) {k : frontend.modular.reach.PartKey} {ns : alloc.vec.Vec arena.handle.NIdx}
    {o} (h : look_locs c k ns = ok (.Ok o)) (lst : AState) :
    (ConRon.Arena.Modular.lookLocs C (absPartKey k) (ns.val.map absNIdx)).run lst =
      .ok (o.map (fun v => v.val.map (·.val)), lst) := by
  rw [look_locs] at h
  peel h as o0, ho0
  rcases orel_cases (hc.looks.get_eq ho0) with ⟨rfl, -⟩ | ⟨l, L, rfl, he, hr⟩
  · peel h as ce, -
    cases Result.ok_injective h
  · rw [ConRon.Arena.Modular.lookLocs, he]
    dsimp only
    peel h as o1, ho1
    cases Result.ok_injective h
    rw [look_locs_in_eq hr ho1]
    rfl

/-- **`rec_locs_at`'s `Ok` is `recLocsAt`'s.** -/
theorem rec_locs_at_eq {c : frontend.modular.reach.ReachCache} {C : ConRon.Arena.Modular.ReachCache}
    (hc : ReachCacheRel c C) {k : frontend.modular.reach.PartKey} {all : alloc.vec.Vec arena.handle.NIdx}
    {o} (h : rec_locs_at c k all = ok (.Ok o)) (lst : AState) :
    (ConRon.Arena.Modular.recLocsAt C (absPartKey k) (all.val.map absNIdx)).run lst =
      .ok (o.val.map (·.val), lst) := by
  rw [rec_locs_at] at h
  peel h as o0, ho0
  rcases orel_cases (hc.recBlocks.get_eq ho0) with ⟨rfl, -⟩ | ⟨l, L, rfl, he, hr⟩
  · peel h as ce, -
    cases Result.ok_injective h
  · rw [ConRon.Arena.Modular.recLocsAt, he]
    dsimp only
    peel h as o1, ho1
    cases Result.ok_injective h
    rw [group_rec_locs_eq hr ho1]
    rfl

/-! ## A copy's presentation -/

/-- **`group_of_kind` is `groupOfKind`.** -/
theorem group_of_kind_eq {x : arena.handle.NIdx} {k : frontend.olean.spec.CKindF arena.handle.NIdx Unit}
    {k' : CKindF NIdx Unit} (hk : KindNamesRel k k') {o} (h : group_of_kind x k = ok o) :
    o.map absNIdx = ConRon.Arena.Modular.groupOfKind (absNIdx x) k' := by
  unfold group_of_kind at h
  cases k <;> cases k' <;> simp only [KindNamesRel, KindRel] at hk <;>
    simp only [ConRon.Arena.Modular.groupOfKind] <;>
    try (cases Result.ok_injective h; rfl)
  · -- an inductive type
    peel h as n, hn
    cases nidx_dup2_ok hn
    cases Result.ok_injective h
    rfl
  · -- a constructor
    peel h as n, hn
    cases nidx_dup2_ok hn
    cases Result.ok_injective h
    rw [← hk.1]; rfl
  · -- a recursor
    rename_i all _ _ _ _ _ _ _ all' _ _ _ _ _ _ _
    rw [← hk.1]
    dsimp only at h
    by_cases h0 : alloc.vec.Vec.len all > 0#usize
    · rw [ite_eq_left h0] at h
      peel h as n, hn
      obtain ⟨t, ht⟩ := vec_index_zero_cons hn
      peel h as n1, hn1
      cases nidx_dup2_ok hn1
      cases Result.ok_injective h
      rw [ht]; rfl
    · rw [ite_eq_right h0] at h
      peel h as n, hn
      cases nidx_dup2_ok hn
      cases Result.ok_injective h
      have : all.val = [] := by
        have : ¬ (0#usize : Std.Usize).val < (alloc.vec.Vec.len all).val := h0
        simpa [vec_len_val] using this
      simp [this]

/-- **`axiom_of` is `axiomOf`.** -/
theorem axiom_of_eq {cv : frontend.olean.spec.StmtRec} {d} (h : axiom_of cv = ok d) :
    absIDeclaration d = ConRon.Arena.Modular.axiomOf (absStmtRec cv) := by
  rw [axiom_of] at h
  cases Result.ok_injective h
  rfl

/-! ## A group's merge -/

/-- Whether the Rust keeps a constant among a group's rest, as a value. -/
def rKeeps (all : alloc.vec.Vec arena.handle.NIdx)
    (e : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx) : Bool :=
  match e.kind with
  | .Recur all2 _ _ _ _ _ _ _ => all2.val.map absNIdx == all.val.map absNIdx
  | _ => true

theorem group_keeps_r {e : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    {all : alloc.vec.Vec arena.handle.NIdx} {b} (h : group_keeps e all = ok b) : b = rKeeps all e := by
  rw [group_keeps] at h
  unfold rKeeps
  generalize e.kind = ek at h ⊢
  cases ek <;> first | exact (Result.ok_injective h).symm | exact nidx_list_eq_abs h

theorem rKeeps_eq {e : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    {e' : CEntryF NIdx EIdx} (he : EntryRel absNIdx absEIdx ValRel e e')
    (all : alloc.vec.Vec arena.handle.NIdx) :
    rKeeps all e = ConRon.Arena.Modular.groupKeeps e' (all.val.map absNIdx) := by
  have hk := he.kind
  unfold rKeeps ConRon.Arena.Modular.groupKeeps
  generalize e.kind = ek at hk ⊢
  generalize e'.kind = ek' at hk ⊢
  cases ek <;> cases ek' <;> simp only [KindRel] at hk <;> first | rfl | simp only [← hk.1]

/-- A constant as a merge's entry, no uses. -/
@[reducible] def mkCE (e : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx) :
    frontend.olean.lazy.CEntry :=
  { c := e, uses := alloc.vec.Vec.new arena.handle.NIdx }

theorem mkCE_rel {e : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    {e' : CEntryF NIdx EIdx} (he : EntryRel absNIdx absEIdx ValRel e e') :
    CEntryRel (mkCE e) { c := e' } :=
  ⟨he, by simp [alloc.vec.Vec.new]⟩

theorem group_merged_loop0_eq
    (tys : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx))
    (cs : alloc.vec.Vec frontend.olean.lazy.CEntry) (i : Std.Usize) {o}
    (h : group_merged_loop0 tys cs i = ok o) : o.val = cs.val ++ (tys.val.drop i.val).map mkCE := by
  rw [group_merged_loop0] at h
  by_cases h1 : i < alloc.vec.Vec.len tys
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as cf, hcf
    obtain ⟨_, rfl⟩ := vec_index_eq hcf
    peel h as cf1, hcf1
    cases view_c_entry_dup_eq hcf1
    peel h as cs1, hcs1
    peel h as i2, hi2
    rw [group_merged_loop0_eq tys cs1 i2 h, ConRon.Refine.vec_push_val hcs1, usize_succ hi2,
      List.drop_eq_getElem_cons hi]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    simp
termination_by tys.val.length - i.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hi2
  omega

theorem group_merged_loop1_eq
    (rest : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx))
    (all : alloc.vec.Vec arena.handle.NIdx) (cs : alloc.vec.Vec frontend.olean.lazy.CEntry) (j : Std.Usize)
    {o} (h : group_merged_loop1 rest all cs j = ok o) :
    o.val = cs.val ++ ((rest.val.drop j.val).filter (rKeeps all)).map mkCE := by
  rw [group_merged_loop1] at h
  by_cases h1 : j < alloc.vec.Vec.len rest
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as cf, hcf
    obtain ⟨_, rfl⟩ := vec_index_eq hcf
    peel h as b, hb
    have eb := group_keeps_r hb
    peel h as cs1, hcs1
    peel h as j1, hj1
    rw [group_merged_loop1_eq rest all cs1 j1 h, usize_succ hj1, List.drop_eq_getElem_cons hi,
      List.filter_cons, ← eb]
    by_cases hb' : b = true
    · rw [ite_eq_left hb'] at hcs1
      peel hcs1 as cf1, hcf1
      cases view_c_entry_dup_eq hcf1
      rw [ConRon.Refine.vec_push_val hcs1]
      simp [hb']
    · rw [ite_eq_right hb'] at hcs1
      cases Result.ok_injective hcs1
      simp [hb']
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    simp
termination_by rest.val.length - j.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hj1
  omega

theorem forall₂_filter_keeps
    {l : List (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {l' : List (CEntryF NIdx EIdx)} (h : List.Forall₂ (EntryRel absNIdx absEIdx ValRel) l l')
    (all : alloc.vec.Vec arena.handle.NIdx) :
    List.Forall₂ (EntryRel absNIdx absEIdx ValRel) (l.filter (rKeeps all))
      (l'.filter (ConRon.Arena.Modular.groupKeeps · (all.val.map absNIdx))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b _ _ he _ ih =>
    rw [List.filter_cons, List.filter_cons, rKeeps_eq he all]
    split
    · exact List.Forall₂.cons he ih
    · exact ih

theorem forall₂_mkCE
    {l : List (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {l' : List (CEntryF NIdx EIdx)} (h : List.Forall₂ (EntryRel absNIdx absEIdx ValRel) l l') :
    List.Forall₂ CEntryRel (l.map mkCE) (l'.map fun c => ({ c } : Arena.Frontend.Olean.CEntry)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons he _ ih => exact List.Forall₂.cons (mkCE_rel he) ih

/-- **`group_merged` is `groupMerged`.** -/
theorem group_merged_rel {pk : frontend.olean.spec.OleanPins}
    {t : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx} {t' : CEntryF NIdx EIdx}
    (ht : EntryRel absNIdx absEIdx ValRel t t')
    {tys rest : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {tys' rest' : List (CEntryF NIdx EIdx)}
    (htys : List.Forall₂ (EntryRel absNIdx absEIdx ValRel) tys.val tys')
    (hrest : List.Forall₂ (EntryRel absNIdx absEIdx ValRel) rest.val rest')
    {all : alloc.vec.Vec arena.handle.NIdx} {mg} (h : group_merged pk t tys rest all = ok mg) :
    MergedRel mg (ConRon.Arena.Modular.groupMerged (absPins pk) t' tys' rest' (all.val.map absNIdx)) := by
  rw [group_merged] at h
  peel h as i1, -
  peel h as i3, -
  peel h as cs1, hcs1
  peel h as cs2, hcs2
  peel h as cs3, hcs3
  refine merged_of_list_rel ?_ h
  rw [group_merged_loop1_eq _ _ _ _ hcs3, group_merged_loop0_eq _ _ _ hcs2, ConRon.Refine.vec_push_val hcs1]
  simp only [alloc.vec.Vec.with_capacity, List.map_cons, List.map_append, List.cons_append]
  refine List.Forall₂.cons (mkCE_rel ht) ?_
  have e0 : ((0#usize : Std.Usize).val) = 0 := rfl
  rw [e0, List.drop_zero, List.drop_zero]
  exact List.rel_append (forall₂_mkCE htys) (forall₂_mkCE (forall₂_filter_keeps hrest all))

/-! ## The parts' reads -/

section reads
variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}

/-- The caches alone, as an `ACS` answer. -/
@[reducible] def CR (_ : Unit) (c : frontend.modular.reach.ReachCache) (C : ConRon.Arena.Modular.ReachCache) :
    Prop := ReachCacheRel c C

/-- **`table_of`'s accept is `tableOf`'s.** -/
theorem table_of_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {k : frontend.modular.reach.PartKey} :
    ACS pers CR st lst (table_of inst fsv pk pers st sp wr c k)
      (ConRon.Arena.Modular.tableOf fs (absPins pk) (absRoots sp) E C (absPartKey k)) := by
  intro hrel hinv a st' c' h
  rw [table_of] at h
  peel h as b, hb
  have eb := hc.tables.contains_eq hb
  unfold ConRon.Arena.Modular.tableOf
  by_cases hb' : b = true
  · rw [ite_eq_left hb'] at h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    refine ⟨C, lst, ?_, hc, hrel, hinv⟩
    rw [← eb, hb']
    rfl
  · rw [ite_eq_right hb'] at h
    have hb0 : C.tables.contains (absPartKey k) = false := by rw [← eb]; simpa using hb'
    peel h as o, ho
    have eo := index_table_eq henv.wr henv.fits ho
    dsimp only at h
    cases o with
    | some t0 =>
      have hs : core.option.Option.is_some (some t0) = true := rfl
      rw [ite_eq_left hs] at h
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      refine ⟨C, lst, ?_, hc, hrel, hinv⟩
      rw [hb0, ← eo]
      rfl
    | none =>
      have hs : ¬ (core.option.Option.is_some (none : Option frontend.olean.reads.NamePositions) = true) := by
        simp [core.option.Option.is_some]
      rw [ite_eq_right hs] at h
      peel h as q, hq
      obtain ⟨r, e⟩ := q
      cases r with
      | Err e1 => simp at h
      | Ok t =>
        obtain ⟨tb, lst1, hx, htb, hrel1, hinv1⟩ := read_part_names_refines hfs hrel hinv t e hq
        peel h as pk1, hpk1
        cases partKey_dup2_ok hpk1
        peel h as q2, hq2
        obtain ⟨_, hm⟩ := q2
        have e2 := Result.ok_injective h
        simp only [Prod.mk.injEq] at e2
        obtain ⟨-, rfl, rfl⟩ := e2
        have htab := hc.tables.insert (v' := absNamePositions t) rfl hq2
        refine ⟨{ C with tables := C.tables.insert (absPartKey k) (absNamePositions t) }, lst1, ?_,
          { hc with tables := htab }, hrel1, hinv1⟩
        rw [hb0, ← eo]
        simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.isSome_none, pure_bind]
        rw [am_bind_ok hx, htb]
        rfl

/-- **`look_of`'s accept is `lookOf`'s.** -/
theorem look_of_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {k : frontend.modular.reach.PartKey} :
    ACS pers CR st lst (look_of inst fsv pk pers st sp wr c k)
      (ConRon.Arena.Modular.lookOf fs (absPins pk) (absRoots sp) E C (absPartKey k)) := by
  intro hrel hinv a st' c' h
  rw [look_of] at h
  peel h as b, hb
  have eb := hc.looks.contains_eq hb
  unfold ConRon.Arena.Modular.lookOf
  by_cases hb' : b = true
  · rw [ite_eq_left hb'] at h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    refine ⟨C, lst, ?_, hc, hrel, hinv⟩
    rw [← eb, hb']
    rfl
  · rw [ite_eq_right hb'] at h
    have hb0 : C.looks.contains (absPartKey k) = false := by rw [← eb]; simpa using hb'
    peel h as q, hq
    obtain ⟨r, st1, c1⟩ := q
    cases r with
    | Err e => simp at h
    | Ok u =>
      obtain ⟨C1, lst1, hx, hc1, hrel1, hinv1⟩ := table_of_refines hfs henv hc hrel hinv u st1 c1 hq
      peel h as o, ho
      have eo := table_get_eq henv.wr henv.fits hc1 ho
      cases o with
      | none =>
        peel h as ce, -
        simp at h
      | some t =>
        peel h as l, hl
        have hL := look_build_rel hl
        peel h as pk1, hpk1
        cases partKey_dup2_ok hpk1
        peel h as q2, hq2
        obtain ⟨_, hm⟩ := q2
        have e2 := Result.ok_injective h
        simp only [Prod.mk.injEq] at e2
        obtain ⟨-, rfl, rfl⟩ := e2
        have hlk := hc1.looks.insert hL hq2
        refine ⟨{ C1 with looks := C1.looks.insert (absPartKey k) (ConRon.Arena.Modular.lookBuild (absNamePositions t)) }, lst1, ?_, { hc1 with looks := hlk }, hrel1, hinv1⟩
        rw [hb0]
        simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [am_bind_ok hx, ← eo]
        rfl

/-- **`put_part` accepts only the read's accept.** -/
theorem put_part_inv {T : Type} {pers st c k p} {r : core.result.Result T frontend.olean.spec.RdErr}
    {b : T} {c'} (h : put_part pers st c k p r = ok (.Ok b, c')) : r = .Ok b := by
  unfold put_part at h
  cases r with
  | Ok a =>
    peel h as pk1, -
    peel h as ⟨_, hm⟩, -
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
    rw [e.1]
  | Err re =>
    cases re with
    | Bad =>
      peel h as s, -
      peel h as pk1, -
      peel h as ⟨_, hm⟩, -
      peel h as ce, -
      simp at h
    | Err e => simp at h

/-- **`put_part` of an accept puts the part back.** -/
theorem put_part_rel {T : Type} {pers st} {c : frontend.modular.reach.ReachCache}
    {C : ConRon.Arena.Modular.ReachCache} (hc : ReachCacheRel c C) {k : frontend.modular.reach.PartKey}
    {p q} (hp : PartReadRel p q) {a b : T} {c'} (h : put_part pers st c k p (.Ok a) = ok (.Ok b, c')) :
    b = a ∧ ReachCacheRel c' { C with parts := C.parts.insert (absPartKey k) q } := by
  unfold put_part at h
  peel h as pk1, hpk1
  cases partKey_dup2_ok hpk1
  peel h as q2, hq2
  obtain ⟨_, hm⟩ := q2
  have e2 := Result.ok_injective h
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  exact ⟨rfl, { hc with parts := hc.parts.insert hp hq2 }⟩

/-- A view's bytes are there. -/
theorem view_bytes_ok (f : frontend.olean.view.ModFiles) (vb : frontend.olean.view.ViewBytes) :
    ∃ bs, frontend.olean.view.view_bytes f vb = ok bs := by
  cases vb <;> exact ⟨_, rfl⟩

/-- **A part's files read and its view cut**, as the twin's: the region of the view, which fits
its bytes. -/
theorem part_files_ok (hfs : FsRel inst fsv fs) {pers st lst} (hrel : AStateRel₀ pers st lst)
    {sp : frontend.olean.files.Roots} {k : frontend.modular.reach.PartKey} {f}
    (hr : frontend.olean.files.read_files inst fsv pers st.store sp k.module k.level = ok (.Ok f)) :
    ∃ mn f', ModFilesRel f f' ∧ ∀ {β} (g : ConLeche.Name → ConLeche.Frontend.Olean.ModFiles → AM β),
      (do
        let mn ← Arena.readName (absNIdx k.module)
        let f ← Arena.Frontend.Olean.liftE (Arena.Frontend.Olean.readFiles fs (absRoots sp) mn (absLevel k.level))
        g mn f).run lst = (g mn f').run lst := by
  obtain ⟨n, hn⟩ := read_files_name hr
  obtain ⟨f', e1, hf⟩ := read_files_refines hfs hn hr
  refine ⟨ConRon.Refine.absName n, f', hf, fun g => ?_⟩
  rw [am_bind_ok (read_name_run hrel hn)]
  simp only [e1, Arena.Frontend.Olean.liftE, pure_bind]

/-- **`take_part`'s accept is `takePart`'s.** -/
theorem take_part_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {c C} (hc : ReachCacheRel c C) {k : frontend.modular.reach.PartKey} :
    ACS pers (fun p c X => ReachCacheRel c X.1 ∧ PartReadRel p X.2) st lst
      (take_part inst fsv pk pers st sp c k)
      (ConRon.Arena.Modular.takePart fs (absPins pk) (absRoots sp) C (absPartKey k)) := by
  intro hrel hinv a st' c' h
  rw [take_part] at h
  peel h as q, hq
  obtain ⟨o, hm⟩ := q
  obtain ⟨eo, hpm⟩ := hc.parts.remove hq
  unfold ConRon.Arena.Modular.takePart
  rcases orel_cases eo with ⟨rfl, he⟩ | ⟨p, y, rfl, he, hp⟩
  · -- read the files
    peel h as r, hr
    cases r with
    | Err e => simp at h
    | Ok f =>
      obtain ⟨mn, f', hf, hrun⟩ := part_files_ok hfs hrel hr
      peel h as o1, ho1
      have hv := mod_files_view_region_eq hf ho1
      cases o1 with
      | none =>
        peel h as ⟨ce, e⟩, -
        simp at h
      | some vbp =>
        obtain ⟨vb, ad⟩ := vbp
        dsimp only at h
        peel h as r1, hr1
        peel h as sm, hsm
        have e2 := Result.ok_injective h
        simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
        obtain ⟨rfl, rfl, rfl⟩ := e2
        obtain ⟨bs, hbs⟩ := view_bytes_ok f vb
        obtain ⟨ey, hfit⟩ := hv bs r1 hbs hr1
        have hpc : PMapRel PartReadRel hm C.parts := hpm.congr fun x => by
          rw [_root_.Std.HashMap.getElem?_erase]
          split
          · rename_i hx
            rw [← (partKey_beq_iff _ _).1 hx, he]
          · rfl
        refine ⟨(C, absRegion bs r1, {}), lst, ?_, ⟨{ hc with parts := hpc },
          ⟨fun bs' hbs' => by rw [hbs] at hbs'; cases Result.ok_injective hbs'; exact ⟨rfl, hfit⟩,
           sm_empty_rel hsm⟩⟩, hrel, hinv⟩
        rw [he]
        dsimp only
        refine (hrun _).trans ?_
        rw [ey]
        rfl
  · -- the part is cached
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
    obtain ⟨rfl, rfl, rfl⟩ := e2
    obtain ⟨r', sm⟩ := y
    refine ⟨({ C with parts := C.parts.erase (absPartKey k) }, r', sm), lst, ?_,
      ⟨{ hc with parts := hpm }, hp⟩, hrel, hinv⟩
    rw [he]
    rfl

/-- **`part_entry`'s accept is `partEntry`'s.** -/
theorem part_entry_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {c C} (hc : ReachCacheRel c C) {k : frontend.modular.reach.PartKey} {l : Std.U64} :
    ACS pers (fun e c X => ReachCacheRel c X.1 ∧ EntryRel absNIdx absEIdx ValRel e X.2) st lst
      (part_entry inst fsv pk pers st sp c k l)
      (ConRon.Arena.Modular.partEntry fs (absPins pk) (absRoots sp) C (absPartKey k) l.val) := by
  intro hrel hinv a st' c' h
  rw [part_entry] at h
  peel h as q, hq
  obtain ⟨r, st1, c1⟩ := q
  cases r with
  | Err e => simp at h
  | Ok p =>
  obtain ⟨⟨C1, r', sm⟩, lst1, hx, ⟨hc1, hp⟩, hrel1, hinv1⟩ := take_part_refines hfs hc hrel hinv p st1 c1 hq
  peel h as bs, hbs
  obtain ⟨er, hfit⟩ := hp.region bs hbs
  peel h as q2, hq2
  obtain ⟨r1, e, s1⟩ := q2
  have hM := entry_with_refines (pk := pk) (c := l) hfit hp.memo hrel1 hinv1 r1 e s1 hq2
  peel h as q3, hq3
  obtain ⟨r2, c2⟩ := q3
  have e3 := Result.ok_injective h
  simp only [Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl, rfl⟩ := e3
  cases put_part_inv hq3
  obtain ⟨t, b, lst2, hx2, hR, hd, hrel2, hinv2⟩ := hM
  obtain ⟨-, hc2⟩ := put_part_rel hc1
    (show PartReadRel { p with memo := s1 } (r', t) from ⟨hp.region, hd⟩) hq3
  refine ⟨({ C1 with parts := C1.parts.insert (absPartKey k) (r', t) }, b), lst2, ?_, ⟨hc2, hR⟩,
    hrel2, hinv2⟩
  unfold ConRon.Arena.Modular.partEntry
  rw [am_bind_ok hx]
  dsimp only
  rw [show r' = absRegion bs p.region from er, am_bind_ok hx2]
  rfl

/-- **`stmt_at`'s accept is `stmtAt`'s.** -/
theorem stmt_at_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {c C} (hc : ReachCacheRel c C) {s : frontend.modular.reach.Spot} :
    ACS pers (fun e c X => ReachCacheRel c X.1 ∧ StmtKindRel e X.2) st lst
      (stmt_at inst fsv pk pers st sp c s)
      (ConRon.Arena.Modular.stmtAt fs (absPins pk) (absRoots sp) C (absSpot s)) := by
  intro hrel hinv a st' c' h
  rw [stmt_at] at h
  peel h as q, hq
  obtain ⟨r, st1, c1⟩ := q
  cases r with
  | Err e => simp at h
  | Ok p =>
  obtain ⟨⟨C1, r', sm⟩, lst1, hx, ⟨hc1, hp⟩, hrel1, hinv1⟩ := take_part_refines hfs hc hrel hinv p st1 c1 hq
  peel h as bs, hbs
  obtain ⟨er, hfit⟩ := hp.region bs hbs
  peel h as q2, hq2
  obtain ⟨r1, e, s1⟩ := q2
  have hM := stmt_with_refines (pk := pk) (c := s.pos.loc) hfit hp.memo hrel1 hinv1 r1 e s1 hq2
  peel h as q3, hq3
  obtain ⟨r2, c2⟩ := q3
  have e3 := Result.ok_injective h
  simp only [Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl, rfl⟩ := e3
  cases put_part_inv hq3
  obtain ⟨t, b, lst2, hx2, hR, hd, hrel2, hinv2⟩ := hM
  obtain ⟨-, hc2⟩ := put_part_rel hc1
    (show PartReadRel { p with memo := s1 } (r', t) from ⟨hp.region, hd⟩) hq3
  refine ⟨({ C1 with parts := C1.parts.insert (absPartKey s.part) (r', t) }, b), lst2, ?_, ⟨hc2, hR⟩,
    hrel2, hinv2⟩
  unfold ConRon.Arena.Modular.stmtAt
  rw [am_bind_ok hx]
  dsimp only
  rw [show r' = absRegion bs p.region from er]
  exact (am_bind_ok hx2).trans rfl

/-- `level_index` is `2` at the private level only. -/
theorem level_index_two {l : frontend.olean.view.OLeanLevel} {i : Std.U64}
    (h : frontend.modular.reach.level_index l = ok i) :
    (i = 2#u64) = (absLevel l = OLeanLevel.private) := by
  cases l <;> cases Result.ok_injective h <;> simp [absLevel]

/-- **`priv_spot`'s accept is `privSpot`'s.** -/
theorem priv_spot_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {s : frontend.modular.reach.Spot} :
    ACS pers (fun s c X => ReachCacheRel c X.1 ∧ X.2 = absSpot s) st lst
      (priv_spot inst fsv pk pers st sp wr c s)
      (ConRon.Arena.Modular.privSpot fs (absPins pk) (absRoots sp) E C (absSpot s)) := by
  intro hrel hinv a st' c' h
  rw [priv_spot] at h
  peel h as i, hi
  have ei := level_index_two hi
  unfold ConRon.Arena.Modular.privSpot
  by_cases h2 : i = 2#u64
  · rw [ite_eq_left h2] at h
    peel h as s1, hs1
    cases spot_dup_ok hs1
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
    obtain ⟨rfl, rfl, rfl⟩ := e2
    refine ⟨(C, absSpot s), lst, ?_, ⟨hc, rfl⟩, hrel, hinv⟩
    have : absLevel s.part.level = OLeanLevel.private := by rw [← ei]; exact h2
    simp only [absSpot, absPartKey, this, beq_self_eq_true, ↓reduceIte]
    rfl
  · rw [ite_eq_right h2] at h
    have hne : (absLevel s.part.level == OLeanLevel.private) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => h2 (by rw [ei]; exact he)
    peel h as k, hk
    obtain ⟨rfl, ek⟩ := priv_key_eq hk
    peel h as q, hq
    obtain ⟨r, st1, c1⟩ := q
    cases r with
    | Err e => simp at h
    | Ok u =>
      obtain ⟨C1, lst1, hx, hc1, hrel1, hinv1⟩ := look_of_refines hfs henv hc hrel hinv u st1 c1 hq
      peel h as r1, hr1
      cases r1 with
      | Err e => simp at h
      | Ok o =>
        have hl := look_at_eq hc1 hr1 lst1
        cases o with
        | none =>
          dsimp only at h
          repeat (peel h as _x, -)
          simp at h
        | some q =>
          have e2 := Result.ok_injective h
          simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
          obtain ⟨rfl, rfl, rfl⟩ := e2
          refine ⟨(C1, ⟨absPartKey ⟨s.part.module, .Private⟩, absNamePosition q⟩), lst1, ?_,
            ⟨hc1, rfl⟩, hrel1, hinv1⟩
          simp only [hne, Bool.false_eq_true, ↓reduceIte, pure_bind]
          rw [← ek, am_bind_ok hx]
          refine (am_bind_ok hl).trans ?_
          rfl

/-- **`view_add_one`'s accept is `viewAddOne`'s.** -/
theorem view_add_one_ok (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {v V} (hv : NMapRel absSpot v V) {k : frontend.modular.reach.PartKey}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) {st' c' v'}
    (h : view_add_one inst fsv pk pers st sp wr c v k = ok (.Ok (), st', c', v')) :
    ∃ C' V' lst', (ConRon.Arena.Modular.viewAddOne fs (absPins pk) (absRoots sp) E C V
        (absPartKey k)).run lst = .ok ((C', V'), lst') ∧ ReachCacheRel c' C' ∧ NMapRel absSpot v' V' ∧
      AStateRel₀ pers st' lst' ∧ AStateInv pers st' := by
  rw [view_add_one] at h
  peel h as q, hq
  obtain ⟨r, st1, c1⟩ := q
  cases r with
  | Err e => simp at h
  | Ok u =>
    obtain ⟨C1, lst1, hx, hc1, hrel1, hinv1⟩ := table_of_refines hfs henv hc hrel hinv u st1 c1 hq
    peel h as o, ho
    have eo := table_get_eq henv.wr henv.fits hc1 ho
    cases o with
    | none =>
      peel h as ce, -
      simp at h
    | some t =>
      peel h as v1, hv1
      have e2 := Result.ok_injective h
      simp only [Prod.mk.injEq] at e2
      obtain ⟨-, rfl, rfl, rfl⟩ := e2
      refine ⟨C1, _, lst1, ?_, hc1, view_step_rel hv hv1, hrel1, hinv1⟩
      unfold ConRon.Arena.Modular.viewAddOne
      rw [am_bind_ok hx, ← eo]
      rfl

theorem view_add_loop_ok (hfs : FsRel inst fsv fs) {pk pers} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) (ks : alloc.vec.Vec frontend.modular.reach.PartKey)
    (st : arena.monad.AState) (lst : AState) (c : frontend.modular.reach.ReachCache)
    (C : ConRon.Arena.Modular.ReachCache) (v : ron.hashmap2.HashMap2 arena.handle.NIdx frontend.modular.reach.Spot)
    (V : _root_.Std.HashMap NIdx ConRon.Arena.Modular.Spot) (i : Std.Usize)
    (hc : ReachCacheRel c C) (hv : NMapRel absSpot v V)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) {st' c' v'}
    (h : view_add_loop inst fsv pk pers st sp wr c v ks i = ok (.Ok (), st', c', v')) :
    ∃ C' V' lst', (ConRon.Arena.Modular.viewAdd fs (absPins pk) (absRoots sp) E C V
        ((ks.val.drop i.val).map absPartKey)).run lst = .ok ((C', V'), lst') ∧ ReachCacheRel c' C' ∧
      NMapRel absSpot v' V' ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st' := by
  rw [view_add_loop] at h
  by_cases h1 : i < alloc.vec.Vec.len ks
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as k, hk
    obtain ⟨_, rfl⟩ := vec_index_eq hk
    peel h as q, hq
    obtain ⟨r, st1, c1, v1⟩ := q
    cases r with
    | Err e => simp at h
    | Ok u =>
      obtain ⟨C1, V1, lst1, hx, hc1, hv1, hrel1, hinv1⟩ := view_add_one_ok hfs henv hc hv hrel hinv hq
      peel h as i2, hi2
      obtain ⟨C2, V2, lst2, hx2, hc2, hv2, hrel2, hinv2⟩ :=
        view_add_loop_ok hfs henv ks st1 lst1 c1 C1 v1 V1 i2 hc1 hv1 hrel1 hinv1 h
      refine ⟨C2, V2, lst2, ?_, hc2, hv2, hrel2, hinv2⟩
      rw [List.drop_eq_getElem_cons hi, List.map_cons, ConRon.Arena.Modular.viewAdd, am_bind_ok hx]
      rw [usize_succ hi2] at hx2
      exact hx2
  · rw [ite_eq_right h1] at h
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq] at e2
    obtain ⟨-, rfl, rfl, rfl⟩ := e2
    refine ⟨C, V, lst, ?_, hc, hv, hrel, hinv⟩
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    rfl
termination_by ks.val.length - i.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hi2
  omega

/-- **`view_add`'s accept is `viewAdd`'s.** -/
theorem view_add_ok (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {v V} (hv : NMapRel absSpot v V) {ks : alloc.vec.Vec frontend.modular.reach.PartKey}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) {st' c' v'}
    (h : view_add inst fsv pk pers st sp wr c v ks = ok (.Ok (), st', c', v')) :
    ∃ C' V' lst', (ConRon.Arena.Modular.viewAdd fs (absPins pk) (absRoots sp) E C V
        (ks.val.map absPartKey)).run lst = .ok ((C', V'), lst') ∧ ReachCacheRel c' C' ∧
      NMapRel absSpot v' V' ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st' := by
  rw [view_add] at h
  simpa using view_add_loop_ok hfs henv ks st lst c C v V 0#usize hc hv hrel hinv h

/-- **`home_loads`' accept is `homeLoads`'.** -/
theorem home_loads_ok (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {k : frontend.modular.reach.PartKey} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {ld st'} (h : home_loads inst fsv pk pers st sp wr c k = ok (.Ok ld, st')) :
    ∃ ld' lst', (ConRon.Arena.Modular.homeLoads fs (absPins pk) (absRoots sp) E C (absPartKey k)).run lst =
        .ok (ld', lst') ∧ HeaderLoadsRel ld ld' ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st' := by
  rw [home_loads] at h
  peel h as o, ho
  have eo := table_get_eq henv.wr henv.fits hc ho
  cases o with
  | none =>
    peel h as ce, -
    simp at h
  | some t =>
    peel h as q, hq
    obtain ⟨r, e⟩ := q
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq] at e2
    obtain ⟨rfl, rfl⟩ := e2
    obtain ⟨ld', lst1, hx, hld, hrel1, hinv1⟩ := header_fixpoint_refines hfs hrel hinv ld e hq
    refine ⟨ld', lst1, ?_, hld, hrel1, hinv1⟩
    unfold ConRon.Arena.Modular.homeLoads
    rw [← eo]
    exact hx

/-- **`view_of`'s accept is `viewOf`'s.** -/
theorem view_of_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {hm : arena.handle.NIdx} :
    ACS pers CR st lst (view_of inst fsv pk pers st sp wr c hm)
      (ConRon.Arena.Modular.viewOf fs (absPins pk) (absRoots sp) E C (absNIdx hm)) := by
  intro hrel hinv a st' c' h
  rw [view_of] at h
  peel h as b, hb
  have eb := hc.views.contains_eq hb
  unfold ConRon.Arena.Modular.viewOf
  by_cases hb' : b = true
  · rw [ite_eq_left hb'] at h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    refine ⟨C, lst, ?_, hc, hrel, hinv⟩
    rw [← eb, hb']
    rfl
  · rw [ite_eq_right hb'] at h
    have hb0 : C.views.contains (absNIdx hm) = false := by rw [← eb]; simpa using hb'
    peel h as k, hk
    obtain ⟨rfl, ek⟩ := priv_key_eq hk
    peel h as q, hq
    obtain ⟨r, st1, c1⟩ := q
    cases r with
    | Err e => simp at h
    | Ok u =>
      obtain ⟨C1, lst1, hx, hc1, hrel1, hinv1⟩ := table_of_refines hfs henv hc hrel hinv u st1 c1 hq
      peel h as q2, hq2
      obtain ⟨r1, st2⟩ := q2
      cases r1 with
      | Err e => simp at h
      | Ok ld =>
        obtain ⟨ld', lst2, hx2, hld, hrel2, hinv2⟩ := home_loads_ok hfs henv hc1 hrel1 hinv1 hq2
        peel h as v, hv
        peel h as v1, hv1
        have ek1 := view_keys_eq hld hv1
        peel h as q3, hq3
        obtain ⟨r2, st3, c2, v2⟩ := q3
        cases r2 with
        | Err e => simp at h
        | Ok u2 =>
          obtain ⟨C2, V2, lst3, hx3, hc2, hv2, hrel3, hinv3⟩ :=
            view_add_ok hfs henv hc1 (NMapRel.new (A := absSpot) hv) hrel2 hinv2 hq3
          peel h as n, hn
          cases nidx_dup2_ok hn
          peel h as q4, hq4
          obtain ⟨_, hmv⟩ := q4
          have e2 := Result.ok_injective h
          simp only [Prod.mk.injEq] at e2
          obtain ⟨-, rfl, rfl⟩ := e2
          refine ⟨{ C2 with views := C2.views.insert (absNIdx hm) V2 }, lst3, ?_,
            { hc2 with views := hc2.views.insert hv2 hq4 }, hrel3, hinv3⟩
          rw [hb0]
          simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
          rw [← ek, am_bind_ok hx, am_bind_ok hx2, ← ek1, am_bind_ok hx3]
          rfl

/-- **`locate`'s accept is `locate`'s.** -/
theorem locate_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {hm y : arena.handle.NIdx} :
    ACS pers (fun o c X => ReachCacheRel c X.1 ∧ X.2 = o.map absSpot) st lst
      (locate inst fsv pk pers st sp wr c hm y)
      (ConRon.Arena.Modular.locate fs (absPins pk) (absRoots sp) E C (absNIdx hm) (absNIdx y)) := by
  intro hrel hinv a st' c' h
  rw [locate] at h
  peel h as q, hq
  obtain ⟨r, st1, c1⟩ := q
  cases r with
  | Err e => simp at h
  | Ok u =>
    obtain ⟨C1, lst1, hx, hc1, hrel1, hinv1⟩ := view_of_refines hfs henv hc hrel hinv u st1 c1 hq
    peel h as i, hi
    peel h as r1, hr1
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq] at e2
    obtain ⟨rfl, rfl, rfl⟩ := e2
    have hc2 : ReachCacheRel { c1 with searches := i } { C1 with searches := C1.searches + 1 } :=
      { hc1 with searches := by rw [ConRon.Refine.Nat.uadd_val hi, hc1.searches]; rfl }
    have hl := view_at_eq hc2 hr1 lst1
    refine ⟨({ C1 with searches := C1.searches + 1 }, a.map absSpot), lst1, ?_, ⟨hc2, rfl⟩, hrel1, hinv1⟩
    unfold ConRon.Arena.Modular.locate
    rw [am_bind_ok hx]
    refine (am_bind_ok hl).trans ?_
    rfl

/-- **`entries_with`'s loop accepts as `entriesWith`** on what is left of the locations. -/
theorem entries_with_loop_ok {pk pers bs r} (hr : RegionFits bs r) (ls : alloc.vec.Vec Std.U64)
    (st : arena.monad.AState) (lst : AState) (m : frontend.olean.sparse.SM) (t : TSM)
    (out : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx))
    (i : Std.Usize) (hm : SMRel m t) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {v st' m'} (h : entries_with_loop pk pers st bs r m ls out i = ok (.Ok v, st', m')) :
    ∃ t' es lst', (ConRon.Arena.Modular.entriesWith (absPins pk) (absRegion bs r) t
        ((ls.val.drop i.val).map (·.val))).run lst = .ok ((t', some es), lst') ∧
      (∃ rest, v.val = out.val ++ rest ∧ List.Forall₂ (EntryRel absNIdx absEIdx ValRel) rest es) ∧
      SMRel m' t' ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st' := by
  rw [entries_with_loop] at h
  by_cases h1 : i < alloc.vec.Vec.len ls
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as l0, hl0
    obtain ⟨_, rfl⟩ := vec_index_eq hl0
    peel h as q, hq
    obtain ⟨r1, e, m1⟩ := q
    have hM := entry_with_refines (pk := pk) (c := ls.val[i.val]) hr hm hrel hinv r1 e m1 hq
    cases r1 with
    | Err e1 => simp at h
    | Ok e1 =>
      obtain ⟨t1, b, lst1, hx, hR, hd, hrel1, hinv1⟩ := hM
      peel h as out1, hout1
      peel h as i3, hi3
      obtain ⟨t', es, lst', hx2, ⟨rest, hv, hF⟩, hm', hrel', hinv'⟩ :=
        entries_with_loop_ok hr ls _ lst1 m1 t1 out1 i3 hd hrel1 hinv1 h
      refine ⟨t', b :: es, lst', ?_, ⟨e1 :: rest, ?_, List.Forall₂.cons hR hF⟩, hm', hrel', hinv'⟩
      · rw [List.drop_eq_getElem_cons hi, List.map_cons, ConRon.Arena.Modular.entriesWith,
          am_bind_ok hx]
        rw [usize_succ hi3] at hx2
        dsimp only
        rw [am_bind_ok hx2]
        rfl
      · rw [hv, ConRon.Refine.vec_push_val hout1]
        simp
  · rw [ite_eq_right h1] at h
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
    obtain ⟨rfl, rfl, rfl⟩ := e2
    refine ⟨t, [], lst, ?_, ⟨[], by simp, List.Forall₂.nil⟩, hm, hrel, hinv⟩
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    rfl
termination_by ls.val.length - i.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hi3
  omega

/-- **`entries_with` accepts as `entriesWith`.** -/
theorem entries_with_ok {pk pers bs r} (hr : RegionFits bs r) {ls : alloc.vec.Vec Std.U64}
    {st : arena.monad.AState} {lst : AState} {m : frontend.olean.sparse.SM} {t : TSM}
    (hm : SMRel m t) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {v st' m'} (h : entries_with pk pers st bs r m ls = ok (.Ok v, st', m')) :
    ∃ t' es lst', (ConRon.Arena.Modular.entriesWith (absPins pk) (absRegion bs r) t
        (ls.val.map (·.val))).run lst = .ok ((t', some es), lst') ∧
      List.Forall₂ (EntryRel absNIdx absEIdx ValRel) v.val es ∧
      SMRel m' t' ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st' := by
  rw [entries_with] at h
  obtain ⟨t', es, lst', hx, ⟨rest, hv, hF⟩, hm', hrel', hinv'⟩ :=
    entries_with_loop_ok hr ls st lst m t _ 0#usize hm hrel hinv h
  refine ⟨t', es, lst', by simpa using hx, ?_, hm', hrel', hinv'⟩
  rw [hv]
  simpa [alloc.vec.Vec.with_capacity] using hF

/-- **`part_entries`' accept is `partEntries`'.** -/
theorem part_entries_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {c C} (hc : ReachCacheRel c C) {k : frontend.modular.reach.PartKey} {ls : alloc.vec.Vec Std.U64} :
    ACS pers (fun v c X => ReachCacheRel c X.1 ∧ List.Forall₂ (EntryRel absNIdx absEIdx ValRel) v.val X.2)
      st lst (part_entries inst fsv pk pers st sp c k ls)
      (ConRon.Arena.Modular.partEntries fs (absPins pk) (absRoots sp) C (absPartKey k)
        (ls.val.map (·.val))) := by
  intro hrel hinv a st' c' h
  rw [part_entries] at h
  peel h as q, hq
  obtain ⟨r, st1, c1⟩ := q
  cases r with
  | Err e => simp at h
  | Ok p =>
  obtain ⟨⟨C1, r', sm⟩, lst1, hx, ⟨hc1, hp⟩, hrel1, hinv1⟩ := take_part_refines hfs hc hrel hinv p st1 c1 hq
  peel h as bs, hbs
  obtain ⟨er, hfit⟩ := hp.region bs hbs
  peel h as q2, hq2
  obtain ⟨r1, st2, s1⟩ := q2
  peel h as q3, hq3
  obtain ⟨r2, c2⟩ := q3
  have e3 := Result.ok_injective h
  simp only [Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl, rfl⟩ := e3
  cases put_part_inv hq3
  obtain ⟨t, es, lst2, hx2, hR, hd, hrel2, hinv2⟩ := entries_with_ok hfit hp.memo hrel1 hinv1 hq2
  obtain ⟨-, hc2⟩ := put_part_rel hc1
    (show PartReadRel { p with memo := s1 } (r', t) from ⟨hp.region, hd⟩) hq3
  refine ⟨({ C1 with parts := C1.parts.insert (absPartKey k) (r', t) }, es), lst2, ?_, ⟨hc2, hR⟩,
    hrel2, hinv2⟩
  unfold ConRon.Arena.Modular.partEntries
  rw [am_bind_ok hx]
  dsimp only
  rw [show r' = absRegion bs p.region from er]
  exact (am_bind_ok hx2).trans rfl

/-! ### Recursor blocks, read -/

theorem rec_blocks_at_loop_ok {pk pers bs r} (hr : RegionFits bs r) (t : frontend.olean.reads.NamePositions)
    (st : arena.monad.AState) (lst : AState)
    (m : ron.hashmap2.HashMap2 arena.handle.NIdx (alloc.vec.Vec Std.U64))
    (M : _root_.Std.HashMap NIdx (_root_.Array Nat)) (i : Std.Usize) (hm : NMapRel absLocs m M)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) {m' st'}
    (h : rec_blocks_at_loop pk pers st bs r t m i = ok (.Ok m', st')) :
    ∃ M' lst', (ConRon.Arena.Modular.recBlocksAt (absPins pk) (absRegion bs r) M
        ((t.consts.val.drop i.val).map absNamePosition)).run lst = .ok (some M', lst') ∧
      NMapRel absLocs m' M' ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st' := by
  rw [rec_blocks_at_loop] at h
  by_cases h1 : i < alloc.vec.Vec.len t.consts
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as np, hnp
    obtain ⟨_, rfl⟩ := vec_index_eq hnp
    rw [List.drop_eq_getElem_cons hi, List.map_cons, ConRon.Arena.Modular.recBlocksAt]
    by_cases h7 : (t.consts.val[i.val]).tag = 7#u64
    · rw [ite_eq_left h7] at h
      have h7' : ((absNamePosition t.consts.val[i.val]).tag == 7) = true := by
        simp [h7]
      peel h as q, hq
      obtain ⟨r1, e⟩ := q
      have hK := kind_names_at_refines (pk := pk) (c := t.consts.val[i.val].loc) hr hrel hinv r1 e hq
      cases r1 with
      | Err e1 => simp at h
      | Ok k =>
        obtain ⟨k', lst1, hx, hk, hrel1, hinv1⟩ := hK
        peel h as m1, hm1
        peel h as i2, hi2
        obtain ⟨M', lst', hx2, hm', hrel', hinv'⟩ :=
          rec_blocks_at_loop_ok hr t _ lst1 m1 _ i2 (rec_blocks_add_rel hm hk hm1) hrel1 hinv1 h
        refine ⟨M', lst', ?_, hm', hrel', hinv'⟩
        rw [usize_succ hi2] at hx2
        simp only [h7', ↓reduceIte]
        refine (am_bind_ok hx).trans ?_
        exact hx2
    · rw [ite_eq_right h7] at h
      have h7' : ((absNamePosition t.consts.val[i.val]).tag == 7) = false := by
        simp only [absNamePosition_tag, beq_eq_false_iff_ne]
        exact fun he => h7 (UScalar.eq_of_val_eq he)
      peel h as i2, hi2
      obtain ⟨M', lst', hx2, hm', hrel', hinv'⟩ :=
        rec_blocks_at_loop_ok hr t st lst m M i2 hm hrel hinv h
      refine ⟨M', lst', ?_, hm', hrel', hinv'⟩
      rw [usize_succ hi2] at hx2
      simp only [h7', Bool.false_eq_true, ↓reduceIte]
      exact hx2
  · rw [ite_eq_right h1] at h
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
    obtain ⟨rfl, rfl⟩ := e2
    refine ⟨M, lst, ?_, hm, hrel, hinv⟩
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    rfl
termination_by t.consts.val.length - i.val
decreasing_by
  all_goals
    have := lt_of_lt_len h1
    have := usize_succ hi2
    omega

/-- **`rec_blocks_at` accepts as `recBlocksAt`.** -/
theorem rec_blocks_at_ok {pk pers bs r} (hr : RegionFits bs r) {t : frontend.olean.reads.NamePositions}
    {st : arena.monad.AState} {lst : AState} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {m' st'} (h : rec_blocks_at pk pers st bs r t = ok (.Ok m', st')) :
    ∃ M' lst', (ConRon.Arena.Modular.recBlocksAt (absPins pk) (absRegion bs r) {}
        (absNamePositions t).consts.toList).run lst = .ok (some M', lst') ∧
      NMapRel absLocs m' M' ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st' := by
  rw [rec_blocks_at] at h
  peel h as m, hm
  have := rec_blocks_at_loop_ok hr t st lst m {} 0#usize (NMapRel.new hm) hrel hinv h
  simpa [absNamePositions] using this

/-- **`rec_blocks_of`'s accept is `recBlocksOf`'s.** -/
theorem rec_blocks_of_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {k : frontend.modular.reach.PartKey} :
    ACS pers CR st lst (rec_blocks_of inst fsv pk pers st sp wr c k)
      (ConRon.Arena.Modular.recBlocksOf fs (absPins pk) (absRoots sp) E C (absPartKey k)) := by
  intro hrel hinv a st' c' h
  rw [rec_blocks_of] at h
  peel h as b, hb
  have eb := hc.recBlocks.contains_eq hb
  unfold ConRon.Arena.Modular.recBlocksOf
  by_cases hb' : b = true
  · rw [ite_eq_left hb'] at h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    refine ⟨C, lst, ?_, hc, hrel, hinv⟩
    rw [← eb, hb']
    rfl
  · rw [ite_eq_right hb'] at h
    have hb0 : C.recBlocks.contains (absPartKey k) = false := by rw [← eb]; simpa using hb'
    peel h as q, hq
    obtain ⟨r, st1, c1⟩ := q
    cases r with
    | Err e => simp at h
    | Ok u =>
    obtain ⟨C1, lst1, hx, hc1, hrel1, hinv1⟩ := table_of_refines hfs henv hc hrel hinv u st1 c1 hq
    peel h as q2, hq2
    obtain ⟨r1, st2, c2⟩ := q2
    cases r1 with
    | Err e => simp at h
    | Ok p =>
    obtain ⟨⟨C2, r', sm⟩, lst2, hx2, ⟨hc2, hp⟩, hrel2, hinv2⟩ :=
      take_part_refines hfs hc1 hrel1 hinv1 p st2 c2 hq2
    peel h as q3, hq3
    obtain ⟨r2, st3⟩ := q3
    peel h as q4, hq4
    obtain ⟨r3, c3⟩ := q4
    cases r3 with
    | Err e => simp at h
    | Ok m =>
    cases put_part_inv hq4
    obtain ⟨-, hc3⟩ := put_part_rel hc2 hp hq4
    -- the read of the blocks
    rw [rec_blocks_read] at hq3
    peel hq3 as o, ho
    have eo := table_get_eq henv.wr henv.fits hc2 ho
    cases o with
    | none =>
      peel hq3 as ce, -
      simp at hq3
    | some t =>
    peel hq3 as bs, hbs
    obtain ⟨er, hfit⟩ := hp.region bs hbs
    obtain ⟨M, lst3, hx3, hM, hrel3, hinv3⟩ := rec_blocks_at_ok hfit hrel2 hinv2 hq3
    peel h as pk1, hpk1
    cases partKey_dup2_ok hpk1
    peel h as q5, hq5
    obtain ⟨_, hm5⟩ := q5
    have e5 := Result.ok_injective h
    simp only [Prod.mk.injEq] at e5
    obtain ⟨-, rfl, rfl⟩ := e5
    refine ⟨{ C2 with parts := C2.parts.insert (absPartKey k) (r', sm), recBlocks := C2.recBlocks.insert (absPartKey k) M }, lst3, ?_,
      { hc3 with recBlocks := hc3.recBlocks.insert hM hq5 }, hrel3, hinv3⟩
    rw [hb0]
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine (am_bind_ok hx).trans ?_
    refine (am_bind_ok hx2).trans ?_
    simp only [← eo, Option.map_some]
    rw [show r' = absRegion bs p.region from er]
    refine (am_bind_ok hx3).trans ?_
    rfl

/-- **`load_part`'s accept is `loadPart`'s.** -/
theorem load_part_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {c C} (hc : ReachCacheRel c C) {k : frontend.modular.reach.PartKey} :
    ACS pers CR st lst (load_part inst fsv pk pers st sp c k)
      (ConRon.Arena.Modular.loadPart fs (absPins pk) (absRoots sp) C (absPartKey k)) := by
  intro hrel hinv a st' c' h
  rw [load_part] at h
  peel h as b, hb
  have eb := hc.parts.contains_eq hb
  unfold ConRon.Arena.Modular.loadPart
  by_cases hb' : b = true
  · rw [ite_eq_left hb'] at h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    refine ⟨C, lst, ?_, hc, hrel, hinv⟩
    rw [← eb, hb']
    rfl
  · rw [ite_eq_right hb'] at h
    have hb0 : C.parts.contains (absPartKey k) = false := by rw [← eb]; simpa using hb'
    peel h as r, hr
    cases r with
    | Err e => simp at h
    | Ok f =>
    obtain ⟨mn, f', hf, hrun⟩ := part_files_ok hfs hrel hr
    peel h as o1, ho1
    have hv := mod_files_view_region_eq hf ho1
    cases o1 with
    | none =>
      peel h as ⟨ce, e⟩, -
      simp at h
    | some vbp =>
    obtain ⟨vb, ad⟩ := vbp
    peel h as r1, hr1
    obtain ⟨bs, hbs⟩ := view_bytes_ok f vb
    obtain ⟨ey, hfit⟩ := hv bs r1 hbs hr1
    have hpr : ∀ {sm}, frontend.olean.sparse.sm_empty = ok sm →
        PartReadRel { files := f, vb, region := r1, memo := sm } (absRegion bs r1, {}) :=
      fun hsm => ⟨fun bs' hbs' => by rw [hbs] at hbs'; cases Result.ok_injective hbs'; exact ⟨rfl, hfit⟩,
        sm_empty_rel hsm⟩
    peel h as b1, hb1
    have eb1 := hc.tables.contains_eq hb1
    by_cases hb1' : b1 = true
    · rw [ite_eq_left hb1'] at h
      peel h as pk1, hpk1
      cases partKey_dup2_ok hpk1
      peel h as sm, hsm
      peel h as q, hq
      obtain ⟨_, hm⟩ := q
      have e2 := Result.ok_injective h
      simp only [Prod.mk.injEq] at e2
      obtain ⟨-, rfl, rfl⟩ := e2
      refine ⟨{ C with parts := C.parts.insert (absPartKey k) (absRegion bs r1, {}) }, lst, ?_,
        { hc with parts := hc.parts.insert (hpr hsm) hq }, hrel, hinv⟩
      rw [hb0]
      simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      refine (hrun _).trans ?_
      rw [ey]
      dsimp only
      rw [← eb1, hb1']
      rfl
    · rw [ite_eq_right hb1'] at h
      have hb10 : C.tables.contains (absPartKey k) = false := by rw [← eb1]; simpa using hb1'
      peel h as bs2, hbs2
      rw [hbs] at hbs2
      cases Result.ok_injective hbs2
      peel h as q, hq
      obtain ⟨r2, e⟩ := q
      have hN := name_positions_at_refines (pk := pk) (root := ad) hfit hrel hinv r2 e hq
      cases r2 with
      | Err e2 =>
        cases e2 with
        | Bad => peel h as ⟨ce, e'⟩, -; simp at h
        | Err e3 => simp at h
      | Ok t =>
      obtain ⟨t', lst1, hx1, ht, hrel1, hinv1⟩ := hN
      peel h as pk1, hpk1
      cases partKey_dup2_ok hpk1
      peel h as sm, hsm
      peel h as q2, hq2
      obtain ⟨_, hm⟩ := q2
      peel h as q3, hq3
      obtain ⟨_, hm3⟩ := q3
      have e2 := Result.ok_injective h
      simp only [Prod.mk.injEq] at e2
      obtain ⟨-, rfl, rfl⟩ := e2
      have hP := hc.parts.insert (hpr hsm) hq2
      have hT := hc.tables.insert (v' := absNamePositions t) rfl hq3
      refine ⟨{ C with parts := C.parts.insert (absPartKey k) (absRegion bs r1, {}), tables := C.tables.insert (absPartKey k) (absNamePositions t) }, lst1, ?_,
        { hc with parts := hP, tables := hT }, hrel1, hinv1⟩
      rw [hb0]
      simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      refine (hrun _).trans ?_
      rw [ey]
      dsimp only
      rw [hb10]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [am_bind_ok hx1, ht]
      rfl

/-! ### A group, read from one part -/

theorem group_at_loop_eq (locs rl : alloc.vec.Vec Std.U64) (i : Std.Usize) {o}
    (h : group_at_loop locs rl i = ok o) : o.val = locs.val ++ rl.val.drop i.val := by
  rw [group_at_loop] at h
  by_cases h1 : i < alloc.vec.Vec.len rl
  · rw [ite_eq_left h1] at h
    have hi := lt_of_lt_len h1
    peel h as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    peel h as locs1, hlocs1
    peel h as i3, hi3
    rw [group_at_loop_eq locs1 rl i3 h, ConRon.Refine.vec_push_val hlocs1, usize_succ hi3,
      List.drop_eq_getElem_cons hi]
    simp
  · rw [ite_eq_right h1] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (lt_of_not_lt_len h1)]
    simp
termination_by rl.val.length - i.val
decreasing_by
  have := lt_of_lt_len h1
  have := usize_succ hi3
  omega

/-- **`group_at`'s accept is `groupAt`'s.** -/
theorem group_at_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {k : frontend.modular.reach.PartKey} {n : arena.handle.NIdx} :
    ACS pers (fun o c X => ReachCacheRel c X.1 ∧ X.2 = o.map absIDeclaration) st lst
      (group_at inst fsv pk pers st sp wr c k n)
      (ConRon.Arena.Modular.groupAt fs (absPins pk) (absRoots sp) E C (absPartKey k) (absNIdx n)) := by
  intro hrel hinv a st' c' h
  rw [group_at] at h
  unfold ConRon.Arena.Modular.groupAt
  peel h as ⟨r, st1, c1⟩, hq
  cases r with
  | Err e => simp at h
  | Ok u =>
  obtain ⟨C1, lst1, hx1, hc1, hrel1, hinv1⟩ := load_part_refines hfs hc hrel hinv u st1 c1 hq
  peel h as ⟨r1, st2, c2⟩, hq1
  cases r1 with
  | Err e => simp at h
  | Ok u1 =>
  obtain ⟨C2, lst2, hx2, hc2, hrel2, hinv2⟩ := look_of_refines hfs henv hc1 hrel1 hinv1 u1 st2 c2 hq1
  peel h as r2, hr2
  cases r2 with
  | Err e => simp at h
  | Ok o =>
  have hl := look_at_eq hc2 hr2 lst2
  cases o with
  | none =>
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
    obtain ⟨rfl, rfl, rfl⟩ := e2
    refine ⟨(C2, none), lst2, ?_, ⟨hc2, rfl⟩, hrel2, hinv2⟩
    refine (am_bind_ok hx1).trans ?_
    refine (am_bind_ok hx2).trans ?_
    refine (am_bind_ok hl).trans ?_
    rfl
  | some q =>
  peel h as ⟨r3, st3, c3⟩, hq3
  cases r3 with
  | Err e => simp at h
  | Ok t =>
  obtain ⟨⟨C3, t'⟩, lst3, hx3, ⟨hc3, ht⟩, hrel3, hinv3⟩ :=
    part_entry_refines hfs hc2 hrel2 hinv2 t st3 c3 hq3
  obtain ⟨tn, tlp, tty, tk⟩ := t
  obtain ⟨tn', tlp', tty', tk'⟩ := t'
  have hk := ht.kind
  cases tk with
  | Ax _ => repeat (peel h as _x, -); simp at h
  | Defn _ _ _ => repeat (peel h as _x, -); simp at h
  | Thm _ _ => repeat (peel h as _x, -); simp at h
  | Opaq _ _ => repeat (peel h as _x, -); simp at h
  | Quot _ => repeat (peel h as _x, -); simp at h
  | Ctor _ _ _ _ _ => repeat (peel h as _x, -); simp at h
  | Recur _ _ _ _ _ _ _ _ => repeat (peel h as _x, -); simp at h
  | Induct np ni all cs nn ir iu irf =>
  cases tk' with
  | induct np' ni' all' cs' nn' ir' iu' irf' => ?_
  | _ => simp only [KindRel] at hk
  obtain ⟨-, -, hall, -⟩ := hk
  peel h as all1, hall1
  have eall : all1.val.map absNIdx = all' := by rw [nidx_vec_dup_val hall1]; exact hall
  peel h as r4, hr4
  cases r4 with
  | Err e => simp at h
  | Ok o1 =>
  have hl4 := look_locs_eq hc3 hr4 lst3
  rw [eall] at hl4
  cases o1 with
  | none =>
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
    obtain ⟨rfl, rfl, rfl⟩ := e2
    refine ⟨(C3, none), lst3, ?_, ⟨hc3, rfl⟩, hrel3, hinv3⟩
    refine (am_bind_ok hx1).trans ?_
    refine (am_bind_ok hx2).trans ?_
    refine (am_bind_ok hl).trans ?_
    refine (am_bind_ok hx3).trans ?_
    simp only [pure_bind]
    refine (am_bind_ok hl4).trans ?_
    rfl
  | some ls =>
  peel h as ⟨r5, st4, c4⟩, hq5
  cases r5 with
  | Err e => simp at h
  | Ok tys =>
  obtain ⟨⟨C4, tys'⟩, lst4, hx4, ⟨hc4, htys⟩, hrel4, hinv4⟩ :=
    part_entries_refines hfs hc3 hrel3 hinv3 tys st4 c4 hq5
  peel h as v, hv
  have ev := group_ctor_names_eq htys hv
  peel h as r6, hr6
  cases r6 with
  | Err e => simp at h
  | Ok o2 =>
  have hl6 := look_locs_eq hc4 hr6 lst4
  rw [ev] at hl6
  cases o2 with
  | none =>
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
    obtain ⟨rfl, rfl, rfl⟩ := e2
    refine ⟨(C4, none), lst4, ?_, ⟨hc4, rfl⟩, hrel4, hinv4⟩
    refine (am_bind_ok hx1).trans ?_
    refine (am_bind_ok hx2).trans ?_
    refine (am_bind_ok hl).trans ?_
    refine (am_bind_ok hx3).trans ?_
    simp only [pure_bind]
    refine (am_bind_ok hl4).trans ?_
    refine (am_bind_ok hx4).trans ?_
    refine (am_bind_ok hl6).trans ?_
    rfl
  | some ls1 =>
  peel h as ⟨r7, st5, c5⟩, hq7
  cases r7 with
  | Err e => simp at h
  | Ok u7 =>
  obtain ⟨C5, lst5, hx5, hc5, hrel5, hinv5⟩ := rec_blocks_of_refines hfs henv hc4 hrel4 hinv4 u7 st5 c5 hq7
  peel h as r8, hr8
  cases r8 with
  | Err e => simp at h
  | Ok rl =>
  have hl8 := rec_locs_at_eq hc5 hr8 lst5
  rw [eall] at hl8
  peel h as locs, hlocs
  have elocs := group_at_loop_eq _ _ _ hlocs
  peel h as ⟨r9, st6, c6⟩, hq9
  cases r9 with
  | Err e => simp at h
  | Ok rest =>
  obtain ⟨⟨C6, rest'⟩, lst6, hx6, ⟨hc6, hrest⟩, hrel6, hinv6⟩ :=
    part_entries_refines hfs hc5 hrel5 hinv5 rest st6 c6 hq9
  have e0 : ((0#usize : Std.Usize).val) = 0 := rfl
  rw [elocs, e0, List.drop_zero, List.map_append] at hx6
  peel h as mg, hmg
  have hM := group_merged_rel ht htys hrest hmg
  rw [eall] at hM
  peel h as r10, hr10
  cases r10 with
  | Err e => simp at h
  | Ok d =>
  have e2 := Result.ok_injective h
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
  obtain ⟨rfl, rfl, rfl⟩ := e2
  obtain ⟨lst7, hx7, hrel7, hinv7⟩ := group_record_ok hrel6 hinv6 hM hr10
  refine ⟨(C6, some (absIDeclaration d)), lst7, ?_, ⟨hc6, rfl⟩, hrel7, hinv7⟩
  refine (am_bind_ok hx1).trans ?_
  refine (am_bind_ok hx2).trans ?_
  refine (am_bind_ok hl).trans ?_
  refine (am_bind_ok hx3).trans ?_
  simp only [pure_bind]
  refine (am_bind_ok hl4).trans ?_
  refine (am_bind_ok hx4).trans ?_
  refine (am_bind_ok hl6).trans ?_
  refine (am_bind_ok hx5).trans ?_
  refine (am_bind_ok hl8).trans ?_
  refine (am_bind_ok hx6).trans ?_
  refine (am_bind_ok hx7).trans ?_
  rfl

/-! ### A record read -/

/-- What a record read answers: the caches, the record and its home. -/
@[reducible] def RecR (p : arena.env.IDeclaration × arena.handle.NIdx) (c : frontend.modular.reach.ReachCache)
    (X : ConRon.Arena.Modular.ReachCache × IDeclaration × NIdx) : Prop :=
  ReachCacheRel c X.1 ∧ X.2.1 = absIDeclaration p.1 ∧ X.2.2 = absNIdx p.2

/-- **`stmt_record`'s accept is `stmtRecord`'s.** -/
theorem stmt_record_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {s : frontend.modular.reach.Spot} {cv : frontend.olean.spec.StmtRec} :
    ACS pers RecR st lst (stmt_record inst fsv pk pers st sp wr c s cv)
      (ConRon.Arena.Modular.stmtRecord fs (absPins pk) (absRoots sp) E C (absSpot s) (absStmtRec cv)) := by
  intro hrel hinv a st' c' h
  rw [stmt_record] at h
  unfold ConRon.Arena.Modular.stmtRecord
  peel h as hh, hhh
  cases nidx_dup2_ok hhh
  peel h as ⟨r, st1⟩, hq
  cases r with
  | Err e => simp at h
  | Ok ops =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := (reduce_op_names_refines hrel hinv hq).apply
  peel h as b, hb
  have eb := ConRon.Refine2.Lockstep.nidx_vec_contains_spec ops cv.name b hb
  by_cases hb' : b = true
  · rw [ite_eq_left hb'] at h
    have hcon : (absNIdxL ops).contains (absNIdx cv.name) = true := by
      rw [← hb']; rw [eb]; rfl
    peel h as ⟨r1, st2, c1⟩, hq1
    cases r1 with
    | Err e => simp at h
    | Ok p =>
    obtain ⟨⟨C1, p'⟩, lst2, hx2, ⟨hc1, hp⟩, hrel2, hinv2⟩ :=
      priv_spot_refines hfs henv hc hrel1 hinv1 p st2 c1 hq1
    change (if p.pos.tag = 0#u64 then _ else _) = _ at h
    by_cases h0 : p.pos.tag = 0#u64
    · rw [ite_eq_left h0] at h
      peel h as i, hi
      have ei := axiom_of_eq hi
      have e2 := Result.ok_injective h
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
      obtain ⟨rfl, rfl, rfl⟩ := e2
      refine ⟨(C1, absIDeclaration i, absNIdx s.part.module), lst2, ?_, ⟨hc1, rfl, rfl⟩, hrel2, hinv2⟩
      refine (am_bind_ok hx1).trans ?_
      simp only [absStmtRec_name, hcon, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
      refine (am_bind_ok hx2).trans ?_
      have : (p'.pos.tag == 0) = true := by rw [show p' = absSpot p from hp]; simp [h0]
      simp only [this, Bool.true_or, ↓reduceIte, ei]
      rfl
    · rw [ite_eq_right h0] at h
      by_cases h3 : p.pos.tag = 3#u64
      · rw [ite_eq_left h3] at h
        peel h as i, hi
        have ei := axiom_of_eq hi
        have e2 := Result.ok_injective h
        simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
        obtain ⟨rfl, rfl, rfl⟩ := e2
        refine ⟨(C1, absIDeclaration i, absNIdx s.part.module), lst2, ?_, ⟨hc1, rfl, rfl⟩, hrel2, hinv2⟩
        refine (am_bind_ok hx1).trans ?_
        simp only [absStmtRec_name, hcon, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
        refine (am_bind_ok hx2).trans ?_
        have : (p'.pos.tag == 3) = true := by rw [show p' = absSpot p from hp]; simp [h3]
        simp only [this, Bool.or_true, ↓reduceIte, ei]
        rfl
      · rw [ite_eq_right h3] at h
        repeat (peel h as _x, -)
        simp at h
  · rw [ite_eq_right hb'] at h
    peel h as i, hi
    have ei := axiom_of_eq hi
    have e2 := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
    obtain ⟨rfl, rfl, rfl⟩ := e2
    have hcon : (absNIdxL ops).contains (absNIdx cv.name) = false := by
      have : b = false := by simpa using hb'
      rw [← this, eb]; rfl
    refine ⟨(C, absIDeclaration i, absNIdx s.part.module), lst1, ?_, ⟨hc, rfl, rfl⟩, hrel1, hinv1⟩
    refine (am_bind_ok hx1).trans ?_
    simp only [absStmtRec_name, hcon, Bool.not_false, ↓reduceIte, ei]
    rfl

/-- **`read_record`'s accept is `readRecord`'s.** -/
theorem read_record_refines (hfs : FsRel inst fsv fs) {pk pers st lst} {sp : frontend.olean.files.Roots}
    {env wr own E} (henv : ReachEnvRel env wr own E) {c C} (hc : ReachCacheRel c C)
    {x : arena.handle.NIdx} :
    ACS pers RecR st lst (read_record inst fsv pk pers st sp wr c x)
      (ConRon.Arena.Modular.readRecord fs (absPins pk) (absRoots sp) E C (absNIdx x)) := by
  intro hrel hinv a st' c' h
  rw [read_record] at h
  unfold ConRon.Arena.Modular.readRecord
  peel h as o, ho
  have eo := record_spot_eq henv.wr hc ho
  cases o with
  | none =>
    repeat (peel h as _x, -)
    simp at h
  | some p =>
  obtain ⟨s, completed⟩ := p
  rw [← eo]
  peel h as hh, hhh
  cases nidx_dup2_ok hhh
  by_cases hsk : s.pos.skipped = true
  · rw [ite_eq_left hsk] at h
    repeat (peel h as _x, -)
    simp at h
  · rw [ite_eq_right hsk] at h
    have hsk' : s.pos.skipped = false := by simpa using hsk
    peel h as ⟨r, st1, c1⟩, hq
    cases r with
    | Err e => simp at h
    | Ok p1 =>
    obtain ⟨cv, k⟩ := p1
    obtain ⟨⟨C1, cv', k'⟩, lst1, hx1, ⟨hc1, hcv, hk⟩, hrel1, hinv1⟩ :=
      stmt_at_refines hfs hc hrel hinv (cv, k) st1 c1 hq
    peel h as o1, ho1
    have eo1 := group_of_kind_eq hk ho1
    cases o1 with
    | some n =>
      peel h as pk1, hpk1
      obtain ⟨rfl, ek⟩ := priv_key_eq hpk1
      peel h as ⟨r1, st2, c2⟩, hq2
      cases r1 with
      | Err e => simp at h
      | Ok o2 =>
      obtain ⟨⟨C2, o2'⟩, lst2, hx2, ⟨hc2, ho2⟩, hrel2, hinv2⟩ :=
        group_at_refines hfs henv hc1 hrel1 hinv1 o2 st2 c2 hq2
      cases o2 with
      | none =>
        repeat (peel h as _x, -)
        simp at h
      | some d =>
      have e2 := Result.ok_injective h
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
      obtain ⟨rfl, rfl, rfl⟩ := e2
      refine ⟨(C2, absIDeclaration d, absNIdx s.part.module), lst2, ?_, ⟨hc2, rfl, rfl⟩, hrel2, hinv2⟩
      simp only [Option.map_some, absSpot, absNamePosition_skipped, hsk', Bool.false_eq_true, ↓reduceIte,
        pure_bind]
      refine (am_bind_ok hx1).trans ?_
      simp only [← eo1, Option.map_some]
      rw [← ek]
      refine (am_bind_ok hx2).trans ?_
      rw [show o2' = some (absIDeclaration d) from ho2]
      rfl
    | none =>
    have hcv' : cv' = absStmtRec cv := hcv
    subst hcv'
    cases k <;> cases k' <;> simp only [KindNamesRel, KindRel] at hk
    case Induct.induct => simp [ConRon.Arena.Modular.groupOfKind] at eo1
    case Ctor.ctor => simp [ConRon.Arena.Modular.groupOfKind] at eo1
    case Recur.recur => simp [ConRon.Arena.Modular.groupOfKind] at eo1
    case Ax.ax =>
      obtain ⟨b, lst2, hx2, hR, hrel2, hinv2⟩ := stmt_record_refines hfs henv hc1 hrel1 hinv1 a st' c' h
      refine ⟨b, lst2, ?_, hR, hrel2, hinv2⟩
      simp only [Option.map_some, absSpot, absNamePosition_skipped, hsk', Bool.false_eq_true, ↓reduceIte,
        pure_bind]
      refine (am_bind_ok hx1).trans ?_
      exact hx2
    case Thm.thm =>
      obtain ⟨b, lst2, hx2, hR, hrel2, hinv2⟩ := stmt_record_refines hfs henv hc1 hrel1 hinv1 a st' c' h
      refine ⟨b, lst2, ?_, hR, hrel2, hinv2⟩
      simp only [Option.map_some, absSpot, absNamePosition_skipped, hsk', Bool.false_eq_true, ↓reduceIte,
        pure_bind]
      refine (am_bind_ok hx1).trans ?_
      exact hx2
    case Opaq.opaq =>
      obtain ⟨b, lst2, hx2, hR, hrel2, hinv2⟩ := stmt_record_refines hfs henv hc1 hrel1 hinv1 a st' c' h
      refine ⟨b, lst2, ?_, hR, hrel2, hinv2⟩
      simp only [Option.map_some, absSpot, absNamePosition_skipped, hsk', Bool.false_eq_true, ↓reduceIte,
        pure_bind]
      refine (am_bind_ok hx1).trans ?_
      exact hx2
    case Defn.defn =>
      cases completed with
      | true =>
        obtain ⟨b, lst2, hx2, hR, hrel2, hinv2⟩ := stmt_record_refines hfs henv hc1 hrel1 hinv1 a st' c' h
        refine ⟨b, lst2, ?_, hR, hrel2, hinv2⟩
        simp only [Option.map_some, absSpot, absNamePosition_skipped, hsk', Bool.false_eq_true, ↓reduceIte,
          pure_bind]
        refine (am_bind_ok hx1).trans ?_
        simp only
        refine (am_bind_ok hx2).trans ?_
        rfl
      | false =>
        peel h as ⟨r1, st2, c2⟩, hq2
        cases r1 with
        | Err e => simp at h
        | Ok e =>
        obtain ⟨⟨C2, e'⟩, lst2, hx2, ⟨hc2, he⟩, hrel2, hinv2⟩ :=
          part_entry_refines hfs hc1 hrel1 hinv1 e st2 c2 hq2
        peel h as r2, hr2
        cases r2 with
        | Err e => simp at h
        | Ok d =>
        have e2 := Result.ok_injective h
        simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
        obtain ⟨rfl, rfl, rfl⟩ := e2
        obtain ⟨lst3, hx3, hrel3, hinv3⟩ := record_of_entry_ok hrel2 hinv2 he hr2
        refine ⟨(C2, absIDeclaration d, absNIdx s.part.module), lst3, ?_, ⟨hc2, rfl, rfl⟩, hrel3, hinv3⟩
        simp only [Option.map_some, absSpot, absNamePosition_skipped, hsk', Bool.false_eq_true, ↓reduceIte,
          pure_bind]
        refine (am_bind_ok hx1).trans ?_
        simp only
        refine (am_bind_ok hx2).trans ?_
        refine (am_bind_ok hx3).trans ?_
        rfl
    case Quot.quot =>
      peel h as r1, hr1
      cases r1 with
      | Err e => simp at h
      | Ok d =>
      have e2 := Result.ok_injective h
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e2
      obtain ⟨rfl, rfl, rfl⟩ := e2
      rename_i q q'
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := record_of_entry_ok hrel1 hinv1
        (c := { «name» := cv.name, level_params := cv.level_params, ty := cv.ty, kind := .Quot q })
        (c' := ⟨absNIdx cv.name, cv.level_params.val.map absNIdx, absEIdx cv.ty, .quot q'⟩)
        ⟨rfl, rfl, rfl, hk⟩ hr1
      refine ⟨(C1, absIDeclaration d, absNIdx s.part.module), lst2, ?_, ⟨hc1, rfl, rfl⟩, hrel2, hinv2⟩
      simp only [Option.map_some, absSpot, absNamePosition_skipped, hsk', Bool.false_eq_true, ↓reduceIte,
        pure_bind]
      refine (am_bind_ok hx1).trans ?_
      refine (am_bind_ok hx2).trans ?_
      rfl

end reads

end ConRon.Refine2.Modular
