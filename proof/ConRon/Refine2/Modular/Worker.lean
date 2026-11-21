/-
# `ConRon.Refine2.Modular.Worker` — `modular/worker.rs`: the own records and the roots

**Task #166, Theorem 2.**  The worker's functions up to the reach, against their twins
(`Arena/Modular/Worker.lean`).  The store-free ones are equations under the abstraction (a name
set `HashMap2<NIdx, bool>` is `NSet`, the load's index by name `IdxRel`, a load's constants
`List.Forall₂ CEntryRel`); `home_of` and `own_records` claim their accept (`AS`-style); the
pin ground's reader walks are `UOut`/`UOutS` (`nat_op_ground`'s shapes); every other state
walk is a lockstep `LS`.

**`reach::record_reads`** is lane L2's: `records_roots`, `own_roots`, `roots_at` take its Theorem 2
as `RecordReadsRel`, which `recordReadsRel_holds` discharges.  `module::check_views` over the
load (`check_views_refines`, with `loaded_entries`) is here; its module-system arm is
`CheckViews.lean`'s.
`reach::decl_names` (lane L2's): `decl_names_ls` (`ReachCheck.lean`).
-/
import ConRon.Refine2.Frontend.Olean.Index
import ConRon.Refine2.Frontend.Olean.Lazy
import ConRon.Refine2.Frontend.Olean.EmitWalk
import ConRon.Refine2.Frontend.Olean.EmitBlocks
import ConRon.Refine2.Frontend.Olean.Records
import ConRon.Refine2.Frontend.Olean.Group
import ConRon.Refine2.Frontend.NatOpGround
import ConRon.Refine2.Checker.DeclCheck
import ConRon.Refine2.Checker.Needs
import ConRon.Refine2.Checker.Pins
import ConRon.Refine2.Modular.Graph
import ConRon.Refine2.Frontend.Olean.Contract
import ConRon.Refine2.Frontend.Olean.CheckViews
import ConRon.Arena.Modular.Worker
import ConRon.Refine2.Modular.ReachCheck

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.modular.worker

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Modular

open ConRon.Arena
open ConRon.Arena.Modular (unskipped pushUnpinned pushLoaded ownUsesAt ownUsesThm ownNames
  namesNodupGo anyLoaded ownNamesOf unloadedConstants groundGo groundGoAll groundStmt groundStmts
  groundVariant pinGround)
open ConRon.Arena (pinFootprint declConstants)
open ConRon.Arena.Modular (declNames)
open ConRon.Arena.Modular (recordReads ownRoots recordsRoots groundRoots loadedRec recsLoaded ownRecs copyRecs
  rootsAt ctxNamesNodup ctxNamesNodupGo ownUsesOf ownRecords homeOf)
open ConRon.Refine2.Frontend (UOut UOutS HSetRel used_consts_go_refines absNIdxArr_push)
open ConRon.Refine2.Lockstep (LS LOut errSim_bind)
open ConRon.Refine2.Frontend.Olean
open ConRon.Refine2.Frontend (absNIdxArr absIDeclArr)
open ConRon.Refine.HashMap2 (Inv toFun)

/-! ## Small facts -/

theorem forall₂_snoc {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} {a : α} {b : β}
    (h : List.Forall₂ R l l') (hab : R a b) : List.Forall₂ R (l ++ [a]) (l' ++ [b]) :=
  List.rel_append h (.cons hab .nil)

theorem forall₂_at {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {i : Nat} (hi : i < l.length) :
    ∃ hi' : i < l'.length, R l[i] l'[i] := by
  have hl := h.length_eq
  refine ⟨by omega, ?_⟩
  obtain ⟨y, hy, hR⟩ := forall₂_getElem? h (List.getElem?_eq_getElem hi)
  rw [List.getElem?_eq_getElem (by omega)] at hy
  cases Option.some_injective _ hy
  exact hR

/-- A loop's rest, at the cursor of a related list. -/
theorem forall₂_drop_cons {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {i : Nat} (hi : i < l.length) :
    ∃ hi' : i < l'.length, R l[i] l'[i] ∧ l'.drop i = l'[i] :: l'.drop (i + 1) := by
  obtain ⟨hi', hR⟩ := forall₂_at h hi
  exact ⟨hi', hR, List.drop_eq_getElem_cons hi'⟩

theorem drop_of_not_lt {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {i : Nat} (hi : l.length ≤ i) : l'.drop i = [] :=
  List.drop_eq_nil_of_le (by rw [← h.length_eq]; exact hi)

/-! ## `unskipped` -/

theorem unskipped_loop_rel (cs : alloc.vec.Vec frontend.olean.lazy.CEntry)
    {L : List Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val L)
    (i : Std.Usize) {out : alloc.vec.Vec frontend.olean.lazy.CEntry} {O : List Arena.Frontend.Olean.CEntry}
    (hout : List.Forall₂ CEntryRel out.val O) {o} (h : unskipped_loop cs out i = ok o) :
    List.Forall₂ CEntryRel o.val (O ++ (L.drop i.val).filter (!·.skipped)) := by
  rw [unskipped_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    peel h as c, hc
    obtain ⟨hi, rfl⟩ := vec_index_eq hc
    obtain ⟨hi', hR, hd⟩ := forall₂_drop_cons hcs hi
    peel h as b, hb
    have eb := c_entry_skipped_eq hR hb
    peel h as out1, hout1
    peel h as i2, hi2
    rw [hd, List.filter_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at hout1
      cases Result.ok_injective hout1
      rw [ite_eq_right (by rw [← eb, cb]; decide)]
      have ih := unskipped_loop_rel cs hcs i2 hout h
      rw [usize_succ hi2] at ih
      exact ih
    · rw [ite_eq_right cb] at hout1
      peel hout1 as c1, hc1
      cases c_entry_dup_eq hc1
      rw [ite_eq_left (by rw [← eb]; simpa using cb), List.append_cons]
      have ih := unskipped_loop_rel cs hcs i2 (by rw [ConRon.Refine.vec_push_val hout1]; exact forall₂_snoc hout hR) h
      rw [usize_succ hi2] at ih
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [drop_of_not_lt hcs (not_lt_len hlt)]
    simpa using hout
termination_by cs.val.length - i.val
decreasing_by all_goals (have := lt_len hlt; rw [usize_succ hi2]; omega)

/-- **`unskipped` is `unskipped`.** -/
theorem unskipped_rel {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList)
    {o} (h : frontend.modular.worker.unskipped cs = ok o) :
    List.Forall₂ CEntryRel o.val (Arena.Modular.unskipped cs').toList := by
  have := unskipped_loop_rel cs hcs 0#usize (out := alloc.vec.Vec.new _) (O := [])
    (by rw [vec_new_val]; exact .nil) h
  simpa [Arena.Modular.unskipped, Array.toList_filter] using this

/-! ## `module::loaded_entries`, `module::check_views` -/

theorem loaded_entries_loop_rel (cs : alloc.vec.Vec frontend.olean.lazy.CEntry)
    {L : List Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val L)
    (i : Std.Usize) {out : alloc.vec.Vec (frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx)}
    {O : List (ConLeche.Frontend.Olean.CEntryF NIdx EIdx)}
    (hout : List.Forall₂ ERel out.val O) {o}
    (h : frontend.olean.module.loaded_entries_loop cs out i = ok o) :
    List.Forall₂ ERel o.val (O ++ (L.drop i.val).map (·.c)) := by
  rw [frontend.olean.module.loaded_entries_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    peel h as c, hc
    obtain ⟨hi, rfl⟩ := vec_index_eq hc
    obtain ⟨hi', hR, hd⟩ := forall₂_drop_cons hcs hi
    peel h as c1, hc1
    cases view_c_entry_dup_eq hc1
    peel h as out1, hout1
    peel h as i2, hi2
    rw [hd, List.map_cons, List.append_cons]
    have ih := loaded_entries_loop_rel cs hcs i2
      (by rw [ConRon.Refine.vec_push_val hout1]; exact forall₂_snoc hout hR.1) h
    rw [usize_succ hi2] at ih
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [drop_of_not_lt hcs (not_lt_len hlt)]
    simpa using hout
termination_by cs.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`loaded_entries` is `loadedEntries`.** -/
theorem loaded_entries_rel {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList)
    {o} (h : frontend.olean.module.loaded_entries cs = ok o) :
    List.Forall₂ ERel o.val (Arena.Frontend.Olean.loadedEntries cs').toList := by
  have := loaded_entries_loop_rel cs hcs 0#usize (out := alloc.vec.Vec.with_capacity _ _) (O := [])
    (by simp) h
  simpa [Arena.Frontend.Olean.loadedEntries] using this

/-- **`check_views`' accept is `checkViews`'**, over related loads. -/
theorem check_views_refines {pk pers st lst} {m : arena.handle.NIdx} {f l}
    {f' : ConLeche.Frontend.Olean.ModFiles} {l' : Arena.Frontend.Olean.Loaded}
    (hf : ModFilesRel f f') (hl : LoadedRel l l') :
    AS pers ExpoRel st lst (frontend.olean.module.check_views pk pers st.store m f l)
      (Arena.Frontend.Olean.checkViews (absPins pk) (absNIdx m) f' l') := by
  intro hrel hinv a s1 h
  rw [frontend.olean.module.check_views] at h
  peel h as cs, hcs0
  have hcs := loaded_entries_rel hl.constants hcs0
  have es := hf.server
  have ep := hf.private
  cases hs : f.server with
  | none =>
    rw [hs] at h es
    dsimp only at h
    peel h as r, hr
    obtain ⟨h3, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h3
    unfold Arena.Frontend.Olean.checkViews
    simp only [es, Option.map_none]
    exact ⟨_, lst, rfl, expo_same hcs hr, hrel, hinv⟩
  | some s =>
    rw [hs] at h es
    dsimp only at h
    cases hp : f.private_part with
    | none =>
      rw [hp] at h ep
      dsimp only at h
      peel h as r, hr
      obtain ⟨h3, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      cases h3
      unfold Arena.Frontend.Olean.checkViews
      simp only [es, ep, Option.map_none, Option.map_some]
      exact ⟨_, lst, rfl, expo_same hcs hr, hrel, hinv⟩
    | some p =>
      rw [hp] at h ep
      dsimp only at h
      peel h as b, hb
      have e := mod_files_is_module_eq hf hb
      cases b with
      | true =>
        rw [ite_eq_left rfl] at h
        exact check_views_module_refines hf hcs hs hp (es.trans rfl) (ep.trans rfl) e.symm hrel hinv a s1 h
      | false =>
        rw [ite_eq_right (by simp)] at h
        peel h as r, hr
        obtain ⟨h3, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
        cases h3
        unfold Arena.Frontend.Olean.checkViews
        simp only [es, ep, Option.map_some, ← e]
        exact ⟨_, lst, rfl, expo_same hcs hr, hrel, hinv⟩

/-! ## `push_unpinned`, `push_loaded` -/

theorem push_unpinned_loop_eq {ix ix'} (hix : NameIndexRel ix ix')
    {fp : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {fp' : _root_.Std.HashSet NIdx} (hfp : NSet fp fp')
    (xs : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (h : push_unpinned_loop out ix fp xs i = ok o) :
    o.val.map absNIdx = out.val.map absNIdx ++
      ((xs.val.drop i.val).map absNIdx).filter (fun x => ix'.first.contains x || !fp'.contains x) := by
  rw [push_unpinned_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len xs
  · rw [ite_eq_left hlt] at h
    peel h as n, hn
    obtain ⟨hi, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := hix.first.rel.contains_eq hb
    peel h as out1, hout1
    peel h as i2, hi2
    have ih := push_unpinned_loop_eq hix hfp xs i2 h
    rw [usize_succ hi2] at ih
    rw [ih, List.drop_eq_getElem_cons hi, List.map_cons, List.filter_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at hout1
      peel hout1 as n1, hn1
      cases nidx_dup2_ok hn1
      rw [ite_eq_left (by rw [← eb, cb]; rfl), ConRon.Refine.vec_push_val hout1]
      simp
    · rw [ite_eq_right cb] at hout1
      peel hout1 as b1, hb1
      have eb1 := SetRel.contains_key nidx_eq2 hfp hb1
      have hb' : ix'.first.contains (absNIdx xs.val[i.val]) = false := by rw [← eb]; simpa using cb
      by_cases cb1 : b1 = true
      · rw [ite_eq_left cb1] at hout1
        cases Result.ok_injective hout1
        rw [ite_eq_right (by rw [hb', ← eb1, cb1]; decide)]
      · rw [ite_eq_right cb1] at hout1
        peel hout1 as n1, hn1
        cases nidx_dup2_ok hn1
        rw [ite_eq_left (by rw [hb', ← eb1]; simpa using cb1), ConRon.Refine.vec_push_val hout1]
        simp
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by xs.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`push_unpinned` is `pushUnpinned`.** -/
theorem push_unpinned_eq {ix ix'} (hix : NameIndexRel ix ix')
    {fp : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {fp' : _root_.Std.HashSet NIdx} (hfp : NSet fp fp')
    {out xs : alloc.vec.Vec arena.handle.NIdx} {o}
    (h : frontend.modular.worker.push_unpinned out ix fp xs = ok o) :
    absNIdxArr o = pushUnpinned (absNIdxArr out) ix' fp' (absNIdxArr xs) := by
  have := push_unpinned_loop_eq hix hfp xs 0#usize h
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
  apply Array.ext'
  simp [pushUnpinned, absNIdxArr, this]

theorem push_loaded_loop_eq {ix ix'} (hix : NameIndexRel ix ix')
    (xs : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (h : push_loaded_loop out ix xs i = ok o) :
    o.val.map absNIdx = out.val.map absNIdx ++
      ((xs.val.drop i.val).map absNIdx).filter (fun x => ix'.first.contains x) := by
  rw [push_loaded_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len xs
  · rw [ite_eq_left hlt] at h
    peel h as n, hn
    obtain ⟨hi, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := hix.first.rel.contains_eq hb
    peel h as out1, hout1
    peel h as i2, hi2
    have ih := push_loaded_loop_eq hix xs i2 h
    rw [usize_succ hi2] at ih
    rw [ih, List.drop_eq_getElem_cons hi, List.map_cons, List.filter_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at hout1
      peel hout1 as n1, hn1
      cases nidx_dup2_ok hn1
      rw [ite_eq_left (by rw [← eb, cb]), ConRon.Refine.vec_push_val hout1]
      simp
    · rw [ite_eq_right cb] at hout1
      cases Result.ok_injective hout1
      rw [ite_eq_right (by rw [← eb]; simpa using cb)]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by xs.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`push_loaded` is `pushLoaded`.** -/
theorem push_loaded_eq {ix ix'} (hix : NameIndexRel ix ix')
    {out xs : alloc.vec.Vec arena.handle.NIdx} {o}
    (h : frontend.modular.worker.push_loaded out ix xs = ok o) :
    absNIdxArr o = pushLoaded (absNIdxArr out) ix' (absNIdxArr xs) := by
  have := push_loaded_loop_eq hix xs 0#usize h
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
  apply Array.ext'
  simp [pushLoaded, absNIdxArr, this]

/-! ## `own_uses_of`, `own_uses_thm` -/

/-- The twin's step of `ownUsesAt`. -/
def ouStep (acc : _root_.Std.HashMap NIdx Nat × Nat) (c : Arena.Frontend.Olean.CEntry) :
    _root_.Std.HashMap NIdx Nat × Nat :=
  (if acc.1.contains c.c.name then acc.1 else acc.1.insert c.c.name acc.2, acc.2 + 1)

theorem own_uses_of_loop_rel (cs : alloc.vec.Vec frontend.olean.lazy.CEntry)
    {L : List Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val L)
    (i : Std.Usize) {at_ A} (ha : IdxRel at_ A) {o} (h : own_uses_of_loop cs at_ i = ok o) :
    IdxRel o ((L.drop i.val).foldl ouStep (A, i.val)).1 := by
  rw [own_uses_of_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    peel h as c, hc
    obtain ⟨hi, rfl⟩ := vec_index_eq hc
    obtain ⟨hi', hR, hd⟩ := forall₂_drop_cons hcs hi
    have hn : absNIdx cs.val[i.val].c.name = L[i.val].c.name := hR.1.name
    peel h as b, hb
    have eb := ha.contains_eq hb
    rw [hn] at eb
    peel h as at1, hat1
    peel h as i2, hi2
    rw [hd, List.foldl_cons]
    have key : ∀ A', IdxRel at1 A' → A' = (ouStep (A, i.val) L[i.val]).1 →
        IdxRel o ((L.drop (i.val + 1)).foldl ouStep (ouStep (A, i.val) L[i.val])).1 := by
      intro A' h1 e
      have ih := own_uses_of_loop_rel cs hcs i2 h1 h
      rw [usize_succ hi2] at ih
      have e2 : ouStep (A, i.val) L[i.val] = (A', i.val + 1) := by rw [e]; rfl
      rw [e2]; exact ih
    by_cases cb : b = true
    · rw [ite_eq_left cb] at hat1
      cases Result.ok_injective hat1
      exact key A ha (by simp [ouStep, ← eb, cb])
    · rw [ite_eq_right cb] at hat1
      peel hat1 as n, hn1
      cases nidx_dup2_ok hn1
      peel hat1 as i3, hi3
      have hv := cast_u64_val hi3
      peel hat1 as ⟨_, at2⟩, hat2
      cases Result.ok_injective hat1
      have ins := ha.insert (by rw [hv]; scalar_tac) hat2
      rw [hv, hn] at ins
      exact key _ ins (by simp [ouStep, ← eb, cb])
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [drop_of_not_lt hcs (not_lt_len hlt)]
    exact ha
termination_by cs.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`OwnUses` against the twin's**: the load's constants, and their index by name. -/
structure OwnUsesRel (u : frontend.modular.worker.OwnUses) (cs' : _root_.Array Arena.Frontend.Olean.CEntry)
    (at' : _root_.Std.HashMap NIdx Nat) : Prop where
  cs : List.Forall₂ CEntryRel u.cs.val cs'.toList
  at_ : IdxRel u.at at'

/-- **`own_uses_of` is `ownUsesAt`.** -/
theorem own_uses_of_rel {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList)
    {o} (h : own_uses_of cs = ok o) : OwnUsesRel o cs' (ownUsesAt cs') := by
  rw [own_uses_of] at h
  peel h as at0, h0
  peel h as at1, h1
  cases Result.ok_injective h
  refine ⟨hcs, ?_⟩
  have := own_uses_of_loop_rel cs hcs 0#usize (IdxRel.empty h0) h1
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
  rw [ownUsesAt, ← Array.foldl_toList]
  exact this

/-- **`own_uses_thm` is `ownUsesThm`.** -/
theorem own_uses_thm_eq {u cs' at'} (hu : OwnUsesRel u cs' at') {n : arena.handle.NIdx} {o}
    (h : own_uses_thm u n = ok o) : o.map absNIdxArr = ownUsesThm cs' at' (absNIdx n) := by
  rw [own_uses_thm] at h
  peel h as g, hg
  obtain ⟨eg, hfit⟩ := hu.at_.get_eq hg
  rw [ownUsesThm, ← eg]
  cases g with
  | none => cases Result.ok_injective h; rfl
  | some i =>
    have hf := hfit i rfl
    peel h as i1, hi1
    have e1 := cast_usize_val hf hi1
    have hl := hu.cs.length_eq
    simp only [absOpt, Option.map_some]
    by_cases hlt : i1 < alloc.vec.Vec.len u.cs
    · rw [ite_eq_left hlt] at h
      peel h as i3, hi3
      have e3 := cast_usize_val hf hi3
      peel h as c, hc
      obtain ⟨hi, rfl⟩ := vec_index_eq hc
      peel h as v, hv
      cases Result.ok_injective h
      obtain ⟨hi', hR⟩ := forall₂_at hu.cs hi
      rw [← e3, ← Array.getElem?_toList, List.getElem?_eq_getElem hi']
      simp only [Option.map_some, absNIdxArr]
      rw [vec_ext (nidx_vec_dup_val hv), hR.2]
    · rw [ite_eq_right hlt] at h
      cases Result.ok_injective h
      have := not_lt_len hlt
      rw [e1] at this
      rw [← Array.getElem?_toList, List.getElem?_eq_none (by omega)]
      rfl

/-! ## `own_names`, `names_nodup_go`, `any_loaded`, `own_names_of`, `unloaded_constants` -/

theorem own_names_loop_rel (cs : alloc.vec.Vec frontend.olean.lazy.CEntry)
    {L : List Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val L)
    (i : Std.Usize) {s S} (hs : NSet s S) {o} (h : own_names_loop cs s i = ok o) :
    NSet o ((L.drop i.val).foldl (fun s c => s.insert c.c.name) S) := by
  rw [own_names_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    peel h as c, hc
    obtain ⟨hi, rfl⟩ := vec_index_eq hc
    obtain ⟨hi', hR, hd⟩ := forall₂_drop_cons hcs hi
    have hn : absNIdx cs.val[i.val].c.name = L[i.val].c.name := hR.1.name
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as ⟨_, s1⟩, hs1
    peel h as i2, hi2
    have ins := SetRel.insert nidx_eq2 absNIdx_inj hs hs1
    rw [hn] at ins
    have ih := own_names_loop_rel cs hcs i2 ins h
    rw [usize_succ hi2] at ih
    rw [hd, List.foldl_cons]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [drop_of_not_lt hcs (not_lt_len hlt)]
    exact hs
termination_by cs.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`own_names` is `ownNames`.** -/
theorem own_names_rel {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList)
    {o} (h : own_names cs = ok o) : NSet o (ownNames cs') := by
  rw [own_names] at h
  peel h as s, hs
  have := own_names_loop_rel cs hcs 0#usize (nset_empty hs) h
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
  rw [ownNames, ← Array.foldl_toList]
  exact this

theorem names_nodup_go_loop_eq (ns : alloc.vec.Vec arena.handle.NIdx) (k : Std.Usize) {s S}
    (hs : NSet s S) {o} (h : names_nodup_go_loop s ns k = ok o) :
    o.1 = (namesNodupGo S ((ns.val.drop k.val).map absNIdx)).1 ∧
      NSet o.2 (namesNodupGo S ((ns.val.drop k.val).map absNIdx)).2 := by
  rw [names_nodup_go_loop] at h
  by_cases hlt : k < alloc.vec.Vec.len ns
  · rw [ite_eq_left hlt] at h
    peel h as n, hn
    obtain ⟨hi, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := SetRel.contains_key nidx_eq2 hs hb
    rw [List.drop_eq_getElem_cons hi, List.map_cons, namesNodupGo]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      cases Result.ok_injective h
      rw [ite_eq_left (by rw [← eb, cb])]
      exact ⟨rfl, hs⟩
    · rw [ite_eq_right cb] at h
      peel h as n1, hn1
      cases nidx_dup2_ok hn1
      peel h as ⟨_, s1⟩, hs1
      peel h as k1, hk1
      have ins := SetRel.insert nidx_eq2 absNIdx_inj hs hs1
      have ih := names_nodup_go_loop_eq ns k1 ins h
      rw [usize_succ hk1] at ih
      rw [ite_eq_right (by rw [← eb]; simpa using cb)]
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨rfl, hs⟩
termination_by ns.val.length - k.val
decreasing_by have := lt_len hlt; rw [usize_succ hk1]; omega

/-- **`names_nodup_go` is `namesNodupGo`**, from the cursor on. -/
theorem names_nodup_go_eq {ns : alloc.vec.Vec arena.handle.NIdx} {k : Std.Usize} {s S}
    (hs : NSet s S) {o} (h : frontend.modular.worker.names_nodup_go s ns k = ok o) :
    o.1 = (namesNodupGo S ((ns.val.drop k.val).map absNIdx)).1 ∧
      NSet o.2 (namesNodupGo S ((ns.val.drop k.val).map absNIdx)).2 :=
  names_nodup_go_loop_eq ns k hs h

theorem any_loaded_loop_eq {ix ix'} (hix : NameIndexRel ix ix') (ns : alloc.vec.Vec arena.handle.NIdx)
    (i : Std.Usize) {o} (h : any_loaded_loop ix ns i = ok o) :
    o = ((ns.val.drop i.val).map absNIdx).any ix'.first.contains := by
  rw [any_loaded_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len ns
  · rw [ite_eq_left hlt] at h
    peel h as n, hn
    obtain ⟨hi, rfl⟩ := vec_index_eq hn
    peel h as b, hb
    have eb := hix.first.rel.contains_eq hb
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.any_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      cases Result.ok_injective h
      rw [← eb, cb, Bool.true_or]
    · rw [ite_eq_right cb] at h
      peel h as i2, hi2
      have ih := any_loaded_loop_eq hix ns i2 h
      rw [usize_succ hi2] at ih
      rw [ih, ← eb, show b = false by simpa using cb, Bool.false_or]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    rfl
termination_by ns.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`any_loaded` is `anyLoaded`.** -/
theorem any_loaded_eq {ix ix'} (hix : NameIndexRel ix ix') {ns : alloc.vec.Vec arena.handle.NIdx} {o}
    (h : frontend.modular.worker.any_loaded ix ns = ok o) : o = anyLoaded ix' (ns.val.map absNIdx) := by
  have := any_loaded_loop_eq hix ns 0#usize h
  simpa [anyLoaded] using this

theorem own_names_of_loop_rel {ix ix'} (hix : NameIndexRel ix ix') (cs : alloc.vec.Vec frontend.olean.lazy.CEntry)
    {L : List Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val L)
    (i : Std.Usize) {s S} (hs : NSet s S) {o} (h : own_names_of_loop ix cs s i = ok o) :
    NSet o ((L.drop i.val).foldl
      (fun s c => if ix'.first.contains c.c.name then s else s.insert c.c.name) S) := by
  rw [own_names_of_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    peel h as c, hc
    obtain ⟨hi, rfl⟩ := vec_index_eq hc
    obtain ⟨hi', hR, hd⟩ := forall₂_drop_cons hcs hi
    have hn : absNIdx cs.val[i.val].c.name = L[i.val].c.name := hR.1.name
    peel h as b, hb
    have eb := hix.first.rel.contains_eq hb
    rw [hn] at eb
    peel h as s1, hs1
    peel h as i2, hi2
    rw [hd, List.foldl_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at hs1
      cases Result.ok_injective hs1
      have ih := own_names_of_loop_rel hix cs hcs i2 hs h
      rw [usize_succ hi2] at ih
      rw [ite_eq_left (by rw [← eb, cb])]
      exact ih
    · rw [ite_eq_right cb] at hs1
      peel hs1 as n1, hn1
      cases nidx_dup2_ok hn1
      peel hs1 as ⟨_, s2⟩, hs2
      cases Result.ok_injective hs1
      have ins := SetRel.insert nidx_eq2 absNIdx_inj hs hs2
      rw [hn] at ins
      have ih := own_names_of_loop_rel hix cs hcs i2 ins h
      rw [usize_succ hi2] at ih
      rw [ite_eq_right (by rw [← eb]; simpa using cb)]
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [drop_of_not_lt hcs (not_lt_len hlt)]
    exact hs
termination_by cs.val.length - i.val
decreasing_by all_goals (have := lt_len hlt; rw [usize_succ hi2]; omega)

/-- **`own_names_of` is `ownNamesOf`.** -/
theorem own_names_of_rel {ix ix'} (hix : NameIndexRel ix ix')
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)} {x' : _root_.Array Arena.Frontend.Olean.ImportRec}
    (hx : x.val.length = x'.size) {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList)
    {o} (h : own_names_of x ix cs = ok o) : NSet o (ownNamesOf x' ix' cs') := by
  rw [own_names_of] at h
  rw [ownNamesOf]
  by_cases h0 : alloc.vec.Vec.len x = 0#usize
  · rw [ite_eq_left h0] at h
    have hz : x'.size = 0 := by
      have := congrArg Std.UScalar.val h0
      rw [vec_len_val] at this
      rw [← hx]; exact this
    rw [ite_eq_left (Array.isEmpty_iff_size_eq_zero.mpr hz)]
    exact own_names_rel hcs h
  · rw [ite_eq_right h0] at h
    have hz : x'.size ≠ 0 := by
      intro e
      apply h0
      have : (alloc.vec.Vec.len x).val = 0 := by rw [vec_len_val, hx, e]
      scalar_tac
    rw [ite_eq_right (fun e => hz (Array.isEmpty_iff_size_eq_zero.mp e))]
    peel h as s, hs
    have := own_names_of_loop_rel hix cs hcs 0#usize (nset_empty hs) h
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
    rw [← Array.foldl_toList]
    exact this

theorem unloaded_constants_loop_rel {ix ix'} (hix : NameIndexRel ix ix')
    (cs : alloc.vec.Vec frontend.olean.lazy.CEntry)
    {L : List Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val L)
    (i : Std.Usize) {out : alloc.vec.Vec frontend.olean.lazy.CEntry} {O : List Arena.Frontend.Olean.CEntry}
    (hout : List.Forall₂ CEntryRel out.val O) {o} (h : unloaded_constants_loop ix cs out i = ok o) :
    List.Forall₂ CEntryRel o.val (O ++ (L.drop i.val).filter fun c => !ix'.first.contains c.c.name) := by
  rw [unloaded_constants_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    peel h as c, hc
    obtain ⟨hi, rfl⟩ := vec_index_eq hc
    obtain ⟨hi', hR, hd⟩ := forall₂_drop_cons hcs hi
    have hn : absNIdx cs.val[i.val].c.name = L[i.val].c.name := hR.1.name
    peel h as b, hb
    have eb := hix.first.rel.contains_eq hb
    rw [hn] at eb
    peel h as out1, hout1
    peel h as i2, hi2
    rw [hd, List.filter_cons]
    by_cases cb : b = true
    · rw [ite_eq_left cb] at hout1
      cases Result.ok_injective hout1
      rw [ite_eq_right (by rw [← eb, cb]; decide)]
      have ih := unloaded_constants_loop_rel hix cs hcs i2 hout h
      rw [usize_succ hi2] at ih
      exact ih
    · rw [ite_eq_right cb] at hout1
      peel hout1 as c1, hc1
      cases c_entry_dup_eq hc1
      rw [ite_eq_left (by rw [← eb]; simpa using cb), List.append_cons]
      have ih := unloaded_constants_loop_rel hix cs hcs i2 (by rw [ConRon.Refine.vec_push_val hout1]; exact forall₂_snoc hout hR) h
      rw [usize_succ hi2] at ih
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [drop_of_not_lt hcs (not_lt_len hlt)]
    simpa using hout
termination_by cs.val.length - i.val
decreasing_by all_goals (have := lt_len hlt; rw [usize_succ hi2]; omega)

/-- **`unloaded_constants` is `unloadedConstants`.** -/
theorem unloaded_constants_rel {ix ix'} (hix : NameIndexRel ix ix')
    {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList)
    {o} (h : frontend.modular.worker.unloaded_constants ix cs = ok o) :
    List.Forall₂ CEntryRel o.val (unloadedConstants ix' cs').toList := by
  have := unloaded_constants_loop_rel hix cs hcs 0#usize (out := alloc.vec.Vec.new _) (O := [])
    (by rw [vec_new_val]; exact .nil) h
  simpa [unloadedConstants, Array.toList_filter] using this

/-! ## The copies: `decls_dup`, `worker_decls`, `home_values` -/

/-- A loop copying records onto `out`, as the abstraction sees it. -/
theorem copy_loop_abs (F : alloc.vec.Vec arena.env.IDeclaration → alloc.vec.Vec arena.env.IDeclaration →
      Std.Usize → Result (alloc.vec.Vec arena.env.IDeclaration))
    (hF : ∀ ds out i, F ds out i =
      if i < alloc.vec.Vec.len ds then do
        let x ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice arena.env.IDeclaration) ds i
        let y ← arena.env.i_declaration_dup x
        let out1 ← alloc.vec.Vec.push out y
        let i1 ← i + 1#usize
        F ds out1 i1
      else ok out)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (i : Std.Usize) {out o} (h : F ds out i = ok o) :
    o.val.map absIDeclaration = out.val.map absIDeclaration ++ (ds.val.drop i.val).map absIDeclaration := by
  rw [hF] at h
  by_cases hlt : i < alloc.vec.Vec.len ds
  · rw [ite_eq_left hlt] at h
    peel h as x, hx
    obtain ⟨hi, rfl⟩ := vec_index_eq hx
    peel h as y, hy
    peel h as out1, hout1
    peel h as i1, hi1
    have ih := copy_loop_abs F hF ds i1 h
    rw [usize_succ hi1] at ih
    rw [ih, ConRon.Refine.vec_push_val hout1, List.map_append, List.map_singleton, i_declaration_dup_abs hy,
      List.append_assoc, List.singleton_append, ← List.map_cons, ← List.drop_eq_getElem_cons hi]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by ds.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi1]; omega

/-- **`decls_dup` is the identity.** -/
theorem decls_dup_eq {ds : alloc.vec.Vec arena.env.IDeclaration} {o} (h : decls_dup ds = ok o) :
    absIDeclArr o = absIDeclArr ds := by
  rw [decls_dup] at h
  have := copy_loop_abs decls_dup_loop (fun ds out i => by rw [decls_dup_loop]) ds 0#usize h
  simp only [vec_with_capacity_val, List.map_nil, List.nil_append, show (0#usize : Std.Usize).val = 0 from rfl,
    List.drop_zero] at this
  simp [absIDeclArr, this]

/-- **`worker_decls` is `workerDecls`**: the context's records, then the own records. -/
theorem worker_decls_eq {w : frontend.modular.worker.WorkerRead} {w' : Arena.Modular.WorkerRead}
    (hctx : absIDeclArr w.reach.ctx = w'.reach.ctx) (hown : absIDeclArr w.own = w'.own) {o}
    (h : worker_decls w = ok o) : absIDeclArr o = Arena.Modular.workerDecls w' := by
  rw [worker_decls] at h
  peel h as i2, -
  peel h as out1, h1
  have e1 := copy_loop_abs worker_decls_loop0 (fun ds out i => by rw [worker_decls_loop0]) _ 0#usize h1
  have e2 := copy_loop_abs worker_decls_loop1 (fun ds out i => by rw [worker_decls_loop1]) _ 0#usize h
  simp only [vec_with_capacity_val, List.map_nil, List.nil_append, show (0#usize : Std.Usize).val = 0 from rfl,
    List.drop_zero] at e1 e2
  rw [Arena.Modular.workerDecls, ← hctx, ← hown]
  simp [absIDeclArr, e2, e1]

/-- **`home_values` is the twin's `#[⟨m, l.frontier⟩]`**, the home left with the empty
frontier. -/
theorem home_values_rel {m : arena.handle.NIdx} {l : frontend.olean.lazy.Loaded}
    {l' : Arena.Frontend.Olean.Loaded} (hl : LoadedRel l l') {o} (h : home_values m l = ok o) :
    List.Forall₂ ModRefRel o.1.val [⟨absNIdx m, l'.frontier⟩] ∧
      LoadedRel o.2 { l' with frontier := {} } := by
  rw [home_values] at h
  peel h as f, hf
  peel h as n, hn
  cases nidx_dup2_ok hn
  peel h as out1, hout1
  cases Result.ok_injective h
  rw [ConRon.Refine.vec_push_val hout1]
  refine ⟨?_, ⟨hl.name, hl.constants, frontier_empty_rel hf⟩⟩
  simp only [vec_with_capacity_val, List.nil_append]
  exact .cons ⟨rfl, hl.frontier⟩ .nil

/-! ## The pin ground

`ground_go`, `ground_go_all`, `ground_stmt` read the state and move the walk's visited set by value
(`UOut`, `nat_op_ground`'s shape); `ground_stmts`, `ground_variant` read the certificates too,
which interns (`UOutS`); `pin_ground` is a lockstep step (`LS`). -/

theorem uout_bind {β : Type} {lst : AState} {x : AM β} {k : β → AM (_root_.Std.HashSet EIdx × _root_.Array NIdx)}
    {v : β} {o} (hx : x.run lst = .ok (v, lst)) (h : UOut lst o (k v)) : UOut lst o (x >>= k) := by
  unfold UOut at *; rw [am_bind_ok hx]; exact h

theorem uout_err {β : Type} {lst : AState} {x : AM β} {k : β → AM (_root_.Std.HashSet EIdx × _root_.Array NIdx)}
    {e} {m} (hx : AErrSim e (x.run lst)) : UOut lst (.Err e, m) (x >>= k) := by
  unfold UOut; exact errSim_bind hx

theorem uouts_bind {β : Type} {pers lst lst1} {x : AM β}
    {k : β → AM (_root_.Std.HashSet EIdx × _root_.Array NIdx)}
    {v : β} {o} (hx : x.run lst = .ok (v, lst1)) (h : UOutS pers lst1 o (k v)) :
    UOutS pers lst o (x >>= k) := by
  unfold UOutS at *; rw [am_bind_ok hx]; exact h

theorem uouts_err {β : Type} {pers lst} {x : AM β} {k : β → AM (_root_.Std.HashSet EIdx × _root_.Array NIdx)}
    {e} {st m} (hx : AErrSim e (x.run lst)) : UOutS pers lst (.Err e, st, m) (x >>= k) := by
  unfold UOutS; exact errSim_bind hx

/-- A reader's outcome at a related state is a state walk's. -/
theorem uouts_of_uout {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {r m} {x : AM (_root_.Std.HashSet EIdx × _root_.Array NIdx)} (h : UOut lst (r, m) x) :
    UOutS pers lst (r, st, m) x := by
  unfold UOut UOutS at *
  cases r with
  | Ok a => obtain ⟨s', hx, hs⟩ := h; exact ⟨s', lst, hx, hs, hrel, hinv⟩
  | Err e => exact h

section Ground
variable {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
  (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
include hrel hinv

/-- **`ground_go` is `groundGo`.** -/
theorem ground_go_out {seen S acc e o} (hs : HSetRel seen S)
    (h : ground_go pers st seen acc e = ok o) :
    UOut lst o (groundGo (S, absNIdxArr acc) (absEIdx e)) := by
  rw [ground_go] at h
  have := used_consts_go_refines hrel hinv hs h
  rw [core_walk_fuel_abs] at this
  exact this

theorem ground_go_all_loop_out (es : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) {seen S acc o}
    (hs : HSetRel seen S) (h : ground_go_all_loop pers st seen es acc i = ok o) :
    UOut lst o (groundGoAll (S, absNIdxArr acc) ((es.val.drop i.val).map absEIdx)) := by
  rw [ground_go_all_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len es
  · rw [ite_eq_left hlt] at h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hi, rfl⟩ := vec_index_eq he
    obtain ⟨⟨r, seen1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hG := ground_go_out hrel hinv hs hr
    rw [List.drop_eq_getElem_cons hi, List.map_cons]
    unfold groundGoAll
    rw [List.foldlM_cons]
    cases r with
    | Err e =>
      cases Result.ok_injective h
      exact uout_err hG
    | Ok acc2 =>
      obtain ⟨s', hx, hs'⟩ := hG
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ih := ground_go_all_loop_out es i2 hs' h
      rw [usize_succ hi2] at ih
      exact uout_bind hx ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨S, rfl, hs⟩
termination_by es.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`ground_go_all` is `groundGoAll`.** -/
theorem ground_go_all_out {es : alloc.vec.Vec arena.handle.EIdx} {seen S acc o}
    (hs : HSetRel seen S) (h : ground_go_all pers st seen acc es = ok o) :
    UOut lst o (groundGoAll (S, absNIdxArr acc) (es.val.map absEIdx)) := by
  have := ground_go_all_loop_out hrel hinv es 0#usize hs h
  simpa using this

/-- **`ground_stmt` is `groundStmt`.** -/
theorem ground_stmt_out {s : alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx} {seen S acc o}
    (hs : HSetRel seen S) (h : ground_stmt pers st seen acc s = ok o) :
    UOut lst o (groundStmt (S, absNIdxArr acc) (s.1.val.map absEIdx, absEIdx s.2)) := by
  obtain ⟨v, e⟩ := s
  rw [ground_stmt] at h
  obtain ⟨⟨r, seen1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hG := ground_go_all_out hrel hinv hs hr
  unfold groundStmt
  cases r with
  | Err e =>
    cases Result.ok_injective h
    exact uout_err hG
  | Ok acc2 =>
    obtain ⟨s', hx, hs'⟩ := hG
    exact uout_bind hx (ground_go_out hrel hinv hs' h)

theorem ground_stmts_loop_out (stmts : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx))
    (i : Std.Usize) {seen S acc o}
    (hs : HSetRel seen S) (h : ground_stmts_loop pers st seen stmts acc i = ok o) :
    UOut lst o (((stmts.val.drop i.val).map fun p => (p.1.val.map absEIdx, absEIdx p.2)).foldlM
      groundStmt (S, absNIdxArr acc)) := by
  rw [ground_stmts_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len stmts
  · rw [ite_eq_left hlt] at h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hi, rfl⟩ := vec_index_eq hp
    obtain ⟨⟨r, seen1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hG := ground_stmt_out hrel hinv hs hr
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldlM_cons]
    cases r with
    | Err e =>
      cases Result.ok_injective h
      exact uout_err hG
    | Ok acc2 =>
      obtain ⟨s', hx, hs'⟩ := hG
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ih := ground_stmts_loop_out stmts i2 hs' h
      rw [usize_succ hi2] at ih
      exact uout_bind hx ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨S, rfl, hs⟩
termination_by stmts.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

theorem ground_variant_loop_out (tps : alloc.vec.Vec (arena.handle.NIdx × arena.handle.EIdx))
    (i : Std.Usize) {seen S acc o}
    (hs : HSetRel seen S) (h : ground_variant_loop pers st seen tps acc i = ok o) :
    UOut lst o (((tps.val.drop i.val).map fun q => (absNIdx q.1, absEIdx q.2)).foldlM
      (fun x p => groundGo (x.1, x.2.push p.1) p.2) (S, absNIdxArr acc)) := by
  rw [ground_variant_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len tps
  · rw [ite_eq_left hlt] at h
    obtain ⟨⟨n, e⟩, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hi, he⟩ := vec_index_eq hp
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases nidx_dup2_ok hn1
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r, seen1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hG := ground_go_out hrel hinv hs hr
    rw [absNIdxArr_push hout1] at hG
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldlM_cons, ← he]
    cases r with
    | Err e =>
      cases Result.ok_injective h
      exact uout_err hG
    | Ok acc2 =>
      obtain ⟨s', hx, hs'⟩ := hG
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ih := ground_variant_loop_out tps i2 hs' h
      rw [usize_succ hi2] at ih
      exact uout_bind hx ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨S, rfl, hs⟩
termination_by tps.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

end Ground

/-- **`ground_stmts` is `groundStmts`.** -/
theorem ground_stmts_outs {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {seen S acc c o} (hs : HSetRel seen S) (h : ground_stmts pers st seen acc c = ok o) :
    UOutS pers lst o (groundStmts (S, absNIdxArr acc) (absNIdx c)) := by
  rw [ground_stmts] at h
  obtain ⟨⟨r, st1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hL := div_mod_cert_stmts_ls (c := c) hrel hinv _ _ hr
  unfold groundStmts
  cases r with
  | Err e =>
    cases Result.ok_injective h
    exact uouts_err hL
  | Ok s =>
    obtain ⟨b, lst1, hx, rfl, hrel1, hinv1⟩ := hL
    obtain ⟨⟨r1, seen1⟩, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have hU := ground_stmts_loop_out hrel1 hinv1 s 0#usize hs hr1
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hU
    exact uouts_bind hx (uouts_of_uout hrel1 hinv1 hU)

/-- **`ground_variant` is `groundVariant`.** -/
theorem ground_variant_outs {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {seen S acc ps c o} (hs : HSetRel seen S) (h : ground_variant pers st seen acc ps c = ok o) :
    UOutS pers lst o (groundVariant (S, absNIdxArr acc) (absINatOpPinSet ps) (absNIdx c)) := by
  rw [ground_variant] at h
  unfold groundVariant
  obtain ⟨⟨r, st1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hL := div_mod_decl_pin_ls (ps := ps) (c := c) hrel hinv _ _ hr
  cases r with
  | Err e =>
    cases Result.ok_injective h
    exact uouts_err hL
  | Ok d =>
    obtain ⟨b, lst1, hx, rfl, hrel1, hinv1⟩ := hL
    refine uouts_bind hx ?_
    obtain ⟨⟨r1, seen1⟩, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hG := ground_go_out hrel1 hinv1 hs hr1
    cases r1 with
    | Err e =>
      cases Result.ok_injective h
      exact uouts_of_uout hrel1 hinv1 (uout_err hG)
    | Ok a =>
      obtain ⟨s1, hx1, hs1⟩ := hG
      refine uouts_bind hx1 ?_
      obtain ⟨⟨r2, st2⟩, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hL2 := div_mod_cert_proofs_ls (ps := ps) (c := c) hrel1 hinv1 _ _ hr2
      cases r2 with
      | Err e =>
        cases Result.ok_injective h
        exact uouts_err hL2
      | Ok p =>
        obtain ⟨b2, lst2, hx2, rfl, hrel2, hinv2⟩ := hL2
        refine uouts_bind hx2 ?_
        obtain ⟨⟨r3, seen2⟩, hr3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hG3 := ground_go_all_out hrel2 hinv2 hs1 hr3
        cases r3 with
        | Err e =>
          cases Result.ok_injective h
          exact uouts_of_uout hrel2 hinv2 (uout_err hG3)
        | Ok a1 =>
          obtain ⟨s2, hx3, hs2⟩ := hG3
          refine uouts_bind hx3 ?_
          obtain ⟨⟨r4, st3⟩, hr4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hL4 := div_mod_type_pins_ls (ps := ps) (c := c) hrel2 hinv2 _ _ hr4
          cases r4 with
          | Err e =>
            cases Result.ok_injective h
            exact uouts_err hL4
          | Ok t =>
            obtain ⟨b4, lst4, hx4, rfl, hrel4, hinv4⟩ := hL4
            refine uouts_bind hx4 ?_
            obtain ⟨⟨r5, seen3⟩, hr5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            cases Result.ok_injective h
            have hU := ground_variant_loop_out hrel4 hinv4 t 0#usize hs2 hr5
            simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hU
            exact uouts_of_uout hrel4 hinv4 hU

theorem pin_ground_loop_ls {pers} (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (c : arena.handle.NIdx) (i : Std.Usize) {st lst seen S out}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hs : HSetRel seen S) :
    LS pers (fun a b => b = absNIdxArr a) (pin_ground_loop pers st pins c seen out i) lst
      (do
        let x ← ((pins.val.drop i.val).map absINatOpPinSet).foldlM
          (fun x ps => groundVariant x ps (absNIdx c)) (S, absNIdxArr out)
        pure x.2) := by
  intro o st' h
  rw [pin_ground_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len pins
  · rw [ite_eq_left hlt] at h
    obtain ⟨ps, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hi, rfl⟩ := vec_index_eq hp
    obtain ⟨⟨r, st1, seen1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hV := ground_variant_outs hrel hinv hs hr
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldlM_cons, bind_assoc]
    unfold UOutS at hV
    cases r with
    | Err e =>
      cases Result.ok_injective h
      exact errSim_bind hV
    | Ok a =>
      obtain ⟨s', lst1, hx, hs', hrel1, hinv1⟩ := hV
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ih := pin_ground_loop_ls pins c i2 hrel1 hinv1 hs' _ _ h
      rw [usize_succ hi2] at ih
      rw [am_bind_ok hx]
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨_, lst, rfl, rfl, hrel, hinv⟩
termination_by pins.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`pin_ground` is `pinGround`.** -/
theorem pin_ground_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet) (c : arena.handle.NIdx) :
    LS pers (fun a b => b = absNIdxArr a) (pin_ground pers st pins c) lst
      (pinGround (absINatOpPinSetL pins) (absNIdx c)) := by
  intro o st' h
  rw [pin_ground] at h
  unfold pinGround
  obtain ⟨⟨r, st1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hL := Lockstep.PB.nat_div_mod_names_ls hrel hinv _ _ hr
  cases r with
  | Err e =>
    cases Result.ok_injective h
    exact errSim_bind hL
  | Ok d =>
    obtain ⟨b, lst1, hx, rfl, hrel1, hinv1⟩ := hL
    rw [am_bind_ok hx]
    obtain ⟨bc, hbc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ebc := Lockstep.nidx_vec_contains_spec d c _ hbc
    by_cases cb : bc = true
    · rw [ite_eq_left cb] at h
      rw [ite_eq_right (by rw [← ebc, cb]; decide), pure_bind]
      obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hE := pin_eq_ls hrel1 hinv1 _ hr1
      cases r1 with
      | Err e =>
        cases Result.ok_injective h
        exact errSim_bind hE
      | Ok n =>
        obtain ⟨b1, lst2, hx2, rfl, hrel2, hinv2⟩ := hE
        rw [am_bind_ok hx2]
        obtain ⟨seen, hseen, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hs : HSetRel seen (∅ : _root_.Std.HashSet EIdx) := by
          obtain ⟨hi0, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
            (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable) hseen
          exact ⟨fun k => by rw [hnone k]; simp, hi0⟩
        obtain ⟨acc, hacc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have eacc : absNIdxArr acc = #[absNIdx n] := by
          simp [ConRon.Refine2.Frontend.absNIdxArr, ConRon.Refine.vec_push_val hacc]
        obtain ⟨⟨r2, st2, seen1⟩, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hS := ground_stmts_outs hrel2 hinv2 hs hr2
        rw [eacc] at hS
        unfold UOutS at hS
        cases r2 with
        | Err e =>
          cases Result.ok_injective h
          exact errSim_bind hS
        | Ok a =>
          obtain ⟨s', lst3, hx3, hs', hrel3, hinv3⟩ := hS
          rw [am_bind_ok hx3]
          have := pin_ground_loop_ls pins c 0#usize hrel3 hinv3 hs' _ _ h
          simpa [absINatOpPinSetL] using this
    · rw [ite_eq_right cb] at h
      rw [ite_eq_left (by rw [← ebc]; simpa using cb)]
      cases Result.ok_injective h
      exact ⟨_, lst1, rfl, rfl, hrel1, hinv1⟩

/-! ## The roots -/

/-- **One lockstep step, by hand**: a Rust stateful bind against a twin bind. -/
theorem lout_bind {α β γ δ : Type} {pers : arena.store.PersTier} {R₁ : α → β → Prop} {R : γ → δ → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {k : core.result.Result α kernel.core_types.CheckError × arena.monad.AState →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} {g : β → AM δ} {o st'}
    (hf : LS pers R₁ f lst x) (h : Std.bind f k = ok (o, st'))
    (herr : ∀ e s, k (.Err e, s) = ok (o, st') → o = .Err e)
    (hok : ∀ a b s lst1, R₁ a b → AStateRel₀ pers s lst1 → AStateInv pers s →
      k (.Ok a, s) = ok (o, st') → LOut pers R o st' ((g b).run lst1)) :
    LOut pers R o st' ((x >>= g).run lst) := by
  obtain ⟨⟨r, s1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := hf r s1 hf1
  cases r with
  | Err e =>
    cases herr e s1 hk1
    exact errSim_bind h1
  | Ok a =>
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := h1
    rw [am_bind_ok hx]
    exact hok a b s1 lst1 hR hrel1 hinv1 hk1

/-- The Rust's error arm: the error passed on. -/
macro "errarm" : tactic =>
  `(tactic| (intro e s h; exact (Prod.mk.inj (Result.ok_injective h)).1.symm))

/-- A twin `pure` against a Rust `ok`. -/
theorem lout_pure {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop} {st lst a b}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hR : R a b) :
    LOut pers R (.Ok a) st ((pure b : AM β).run lst) := ⟨b, lst, rfl, hR, hrel, hinv⟩

theorem footprints_loop0_loop0_eq (ns : alloc.vec.Vec arena.handle.NIdx) (k : Std.Usize) {s S}
    (hs : NSet s S) {o} (h : footprints_loop0_loop0 s ns k = ok o) :
    NSet o (((ns.val.drop k.val).map absNIdx).foldl (fun s n => s.insert n) S) := by
  rw [footprints_loop0_loop0] at h
  by_cases hlt : k < alloc.vec.Vec.len ns
  · rw [ite_eq_left hlt] at h
    peel h as n, hn
    obtain ⟨hi, rfl⟩ := vec_index_eq hn
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as ⟨_, s1⟩, hs1
    peel h as k1, hk1
    have ih := footprints_loop0_loop0_eq ns k1 (SetRel.insert nidx_eq2 absNIdx_inj hs hs1) h
    rw [usize_succ hk1] at ih
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldl_cons]
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact hs
termination_by ns.val.length - k.val
decreasing_by have := lt_len hlt; rw [usize_succ hk1]; omega

/-- The twin's step of `footprints`. -/
def fpStep (s : _root_.Std.HashSet NIdx) (c : Arena.Frontend.Olean.CEntry) : AM (_root_.Std.HashSet NIdx) :=
  List.foldl (fun s n => s.insert n) s <$> pinFootprint c.c.name

theorem footprints_loop0_ls {pers} (cs : alloc.vec.Vec frontend.olean.lazy.CEntry)
    {L : List Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val L)
    (i : Std.Usize) {st lst s S} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hs : NSet s S) :
    LS pers NSet (footprints_loop0 st cs s i) lst ((L.drop i.val).foldlM fpStep S) := by
  intro o st' h
  rw [footprints_loop0] at h
  by_cases hlt : i < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hi, rfl⟩ := vec_index_eq hc
    obtain ⟨hi', hR, hd⟩ := forall₂_drop_cons hcs hi
    have hn : absNIdx cs.val[i.val].c.name = L[i.val].c.name := hR.1.name
    rw [hd, List.foldlM_cons]
    unfold fpStep
    rw [← hn, ← bind_pure_comp, bind_assoc]
    refine lout_bind (pin_footprint_ls hrel hinv _) h (by errarm) ?_
    rintro a b s1 lst1 rfl hrel1 hinv1 h
    simp only [pure_bind]
    obtain ⟨s2, hs2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hS := footprints_loop0_loop0_eq a 0#usize hs hs2
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hS
    have ih := footprints_loop0_ls cs hcs i2 hrel1 hinv1 hS _ _ h
    rw [usize_succ hi2] at ih
    have e : (fun s (c : Arena.Frontend.Olean.CEntry) =>
      List.foldl (fun s n => s.insert n) s <$> pinFootprint c.c.name) = fpStep := rfl
    rw [e]
    simpa [absNIdxList] using ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [drop_of_not_lt hcs (not_lt_len hlt)]
    exact lout_pure hrel hinv hs
termination_by cs.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`footprints` is `footprints`.** -/
theorem footprints_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList) :
    LS pers NSet (frontend.modular.worker.footprints st cs) lst (Arena.Modular.footprints cs') := by
  intro o st' h
  rw [frontend.modular.worker.footprints] at h
  obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have := footprints_loop0_ls cs hcs 0#usize hrel hinv (nset_empty hs) _ _ h
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
  rw [Arena.Modular.footprints, ← Array.foldlM_toList]
  exact this

/-! ## A record's names (`reach::decl_names`, lane L2's) -/

/-- `decl_names_ls` (`ReachCheck.lean`) with its answer as a mapped list. -/
theorem decl_names_ls' {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = a.val.map absNIdx) (frontend.modular.reach.decl_names pers st d) lst
      (declNames (absIDeclaration d)) :=
  decl_names_ls hrel hinv d

/-! ## `records_roots`, `own_roots`, `ground_roots` -/

/-- **`reach::record_reads` is `recordReads`**, as the roots below take it (`record_reads_ls`,
`ReachCheck.lean`, discharges it: `recordReadsRel_holds`). -/
def RecordReadsRel (pers : arena.store.PersTier) : Prop :=
  ∀ {st lst} (d : arena.env.IDeclaration), AStateRel₀ pers st lst → AStateInv pers st →
    LS pers (fun a b => b = a.val.map absNIdx) (frontend.modular.reach.record_reads pers st d) lst
      (recordReads (absIDeclaration d))

/-- **`RecordReadsRel` holds**: lane L2's `record_reads_ls`. -/
theorem recordReadsRel_holds (pers : arena.store.PersTier) : RecordReadsRel pers :=
  fun d hrel hinv => record_reads_ls hrel hinv d

/-- The twin's step of `recordsRoots`. -/
def rrStep (ix : Arena.Frontend.Olean.NameIndex) (fp : _root_.Std.HashSet NIdx) (out : _root_.Array NIdx)
    (d : IDeclaration) : AM (_root_.Array NIdx) :=
  do pure (pushUnpinned out ix fp (← recordReads d).toArray)

theorem records_roots_loop_ls {pers} (hRR : RecordReadsRel pers) {ix ix'} (hix : NameIndexRel ix ix')
    {fp : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {fp' : _root_.Std.HashSet NIdx} (hfp : NSet fp fp')
    (ds : alloc.vec.Vec arena.env.IDeclaration) (i : Std.Usize) {st lst out}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxArr a) (records_roots_loop pers st ix fp ds out i) lst
      (((ds.val.drop i.val).map absIDeclaration).foldlM (rrStep ix' fp') (absNIdxArr out)) := by
  intro o st' h
  rw [records_roots_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len ds
  · rw [ite_eq_left hlt] at h
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hi, rfl⟩ := vec_index_eq hd
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldlM_cons]
    unfold rrStep
    rw [bind_assoc]
    refine lout_bind (hRR _ hrel hinv) h (by errarm) ?_
    rintro a b s1 lst1 rfl hrel1 hinv1 h
    simp only [pure_bind]
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ih := records_roots_loop_ls hRR hix hfp ds i2 hrel1 hinv1 _ _ h
    rw [usize_succ hi2, push_unpinned_eq hix hfp hout1] at ih
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact lout_pure hrel hinv rfl
termination_by ds.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`records_roots` is `recordsRoots`**, given `record_reads`'s Theorem 2. -/
theorem records_roots_ls {pers st lst} (hRR : RecordReadsRel pers) (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {ix ix'} (hix : NameIndexRel ix ix')
    {fp : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {fp' : _root_.Std.HashSet NIdx} (hfp : NSet fp fp')
    (ds : alloc.vec.Vec arena.env.IDeclaration) :
    LS pers (fun a b => b = absNIdxArr a) (records_roots pers st ix fp ds) lst
      (recordsRoots ix' fp' (absIDeclArr ds)) := by
  have := records_roots_loop_ls hRR hix hfp ds 0#usize (out := alloc.vec.Vec.new _) hrel hinv
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
  rw [recordsRoots, ← Array.foldlM_toList]
  exact this

theorem own_roots_loop_eq {ix ix'} (hix : NameIndexRel ix ix')
    {fp : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {fp' : _root_.Std.HashSet NIdx} (hfp : NSet fp fp')
    (cs : alloc.vec.Vec frontend.olean.lazy.CEntry)
    {L : List Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val L)
    (k : Std.Usize) {out o} (h : own_roots_loop ix cs fp out k = ok o) :
    absNIdxArr o = (L.drop k.val).foldl
      (fun out c => if c.skipped then out else pushUnpinned out ix' fp' c.uses) (absNIdxArr out) := by
  rw [own_roots_loop] at h
  by_cases hlt : k < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    peel h as c, hc
    obtain ⟨hi, rfl⟩ := vec_index_eq hc
    obtain ⟨hi', hR, hd⟩ := forall₂_drop_cons hcs hi
    peel h as b, hb
    have eb := c_entry_skipped_eq hR hb
    peel h as out1, hout1
    peel h as k1, hk1
    have ih := own_roots_loop_eq hix hfp cs hcs k1 h
    rw [usize_succ hk1] at ih
    rw [ih, hd, List.foldl_cons]
    congr 1
    by_cases cb : b = true
    · rw [ite_eq_left cb] at hout1
      cases Result.ok_injective hout1
      rw [ite_eq_left (by rw [← eb, cb])]
    · rw [ite_eq_right cb] at hout1
      rw [ite_eq_right (by rw [← eb]; simpa using cb), push_unpinned_eq hix hfp hout1]
      congr 1
      apply Array.ext'
      simp [ConRon.Refine2.Frontend.absNIdxArr, hR.2]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [drop_of_not_lt hcs (not_lt_len hlt)]
    rfl
termination_by cs.val.length - k.val
decreasing_by have := lt_len hlt; rw [usize_succ hk1]; omega

/-- The twin's step of `groundRoots`. -/
def grStep (pins : List INatOpPinSet) (ix : Arena.Frontend.Olean.NameIndex) (out : _root_.Array NIdx)
    (c : Arena.Frontend.Olean.CEntry) : AM (_root_.Array NIdx) :=
  if c.skipped then pure out else pushLoaded out ix <$> pinGround pins c.c.name

theorem ground_roots_loop_ls {pers} (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    {ix ix'} (hix : NameIndexRel ix ix') (cs : alloc.vec.Vec frontend.olean.lazy.CEntry)
    {L : List Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val L)
    (j : Std.Usize) {st lst out} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxArr a) (ground_roots_loop pers st pins ix cs out j) lst
      ((L.drop j.val).foldlM (grStep (absINatOpPinSetL pins) ix') (absNIdxArr out)) := by
  intro o st' h
  rw [ground_roots_loop] at h
  by_cases hlt : j < alloc.vec.Vec.len cs
  · rw [ite_eq_left hlt] at h
    obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hi, rfl⟩ := vec_index_eq hc
    obtain ⟨hi', hR, hd⟩ := forall₂_drop_cons hcs hi
    have hn : absNIdx cs.val[j.val].c.name = L[j.val].c.name := hR.1.name
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have eb := c_entry_skipped_eq hR hb
    rw [hd, List.foldlM_cons]
    unfold grStep
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      rw [ite_eq_left (by rw [← eb, cb]), pure_bind]
      obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ih := ground_roots_loop_ls pins hix cs hcs j1 hrel hinv _ _ h
      rw [usize_succ hj1] at ih
      exact ih
    · rw [ite_eq_right cb] at h
      rw [ite_eq_right (by rw [← eb]; simpa using cb), ← hn, ← bind_pure_comp, bind_assoc]
      refine lout_bind (pin_ground_ls hrel hinv pins _) h (by errarm) ?_
      rintro a g s1 lst1 rfl hrel1 hinv1 h
      simp only [pure_bind]
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ih := ground_roots_loop_ls pins hix cs hcs j1 hrel1 hinv1 _ _ h
      rw [usize_succ hj1, push_loaded_eq hix hout1] at ih
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [drop_of_not_lt hcs (not_lt_len hlt)]
    exact lout_pure hrel hinv rfl
termination_by cs.val.length - j.val
decreasing_by all_goals (have := lt_len hlt; rw [usize_succ hj1]; omega)

/-- **`ground_roots` is `groundRoots`.** -/
theorem ground_roots_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet) {ix ix'} (hix : NameIndexRel ix ix')
    {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList)
    (out : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => b = absNIdxArr a) (ground_roots pers st pins ix cs out) lst
      (groundRoots (absINatOpPinSetL pins) ix' cs' (absNIdxArr out)) := by
  have := ground_roots_loop_ls pins hix cs hcs 0#usize (out := out) hrel hinv
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
  rw [groundRoots, ← Array.foldlM_toList]
  exact this

/-- **`own_roots` is `ownRoots`**, given `record_reads`'s Theorem 2. -/
theorem own_roots_ls {pers st lst} (hRR : RecordReadsRel pers) (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    {ix ix'} (hix : NameIndexRel ix ix') {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList)
    (ds : alloc.vec.Vec arena.env.IDeclaration) :
    LS pers (fun a b => b = absNIdxArr a) (own_roots pers st pins ix cs ds) lst
      (ownRoots (absINatOpPinSetL pins) ix' cs' (absIDeclArr ds)) := by
  intro o st' h
  rw [own_roots] at h
  unfold ownRoots
  refine lout_bind (footprints_ls hrel hinv hcs) h (by errarm) ?_
  rintro f fp' s1 lst1 hfp hrel1 hinv1 h
  refine lout_bind (records_roots_ls hRR hrel1 hinv1 hix hfp ds) h (by errarm) ?_
  rintro a b s2 lst2 rfl hrel2 hinv2 h
  obtain ⟨out, hout, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have eo := own_roots_loop_eq hix hfp cs hcs 0#usize hout
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at eo
  obtain ⟨⟨r2, st3⟩, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hG := ground_roots_ls hrel2 hinv2 pins hix hcs out _ _ hr2
  rw [eo, Array.foldl_toList] at hG
  cases r2 <;> (obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h); exact hG)

/-! ## The records some name of which is loaded -/

/-- **`loaded_rec` is `loadedRec`.** -/
theorem loaded_rec_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {ix ix'} (hix : NameIndexRel ix ix') (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = a) (loaded_rec pers st ix d) lst (loadedRec ix' (absIDeclaration d)) := by
  intro o st' h
  rw [loaded_rec] at h
  unfold loadedRec
  refine lout_bind (decl_names_ls' hrel hinv d) h (by errarm) ?_
  rintro ns b s1 lst1 rfl hrel1 hinv1 h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  exact lout_pure hrel1 hinv1 (any_loaded_eq hix hb).symm

/-- The twin's step of `recsLoaded`. -/
def rlStep (ix : Arena.Frontend.Olean.NameIndex) (want : Bool) (out : _root_.Array IDeclaration)
    (d : IDeclaration) : AM (_root_.Array IDeclaration) := do
  if (← loadedRec ix d) == want then pure (out.push d) else pure out

theorem recs_loaded_loop_ls {pers} {ix ix'} (hix : NameIndexRel ix ix')
    (ds : alloc.vec.Vec arena.env.IDeclaration) (want : Bool) (i : Std.Usize) {st lst out}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIDeclArr a) (recs_loaded_loop pers st ix ds want out i) lst
      (((ds.val.drop i.val).map absIDeclaration).foldlM (rlStep ix' want) (absIDeclArr out)) := by
  intro o st' h
  rw [recs_loaded_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len ds
  · rw [ite_eq_left hlt] at h
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hi, rfl⟩ := vec_index_eq hd
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldlM_cons]
    unfold rlStep
    rw [bind_assoc]
    refine lout_bind (loaded_rec_ls hrel hinv hix _) h (by errarm) ?_
    rintro b b' s1 lst1 hbb hrel1 hinv1 h
    rw [hbb]
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ih := recs_loaded_loop_ls hix ds want i2 hrel1 hinv1 _ _ h
    rw [usize_succ hi2] at ih
    by_cases cw : b = want
    · rw [ite_eq_left cw] at hout1
      obtain ⟨d1, hd1, hout1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hout1
      rw [ite_eq_left (by simp [cw]), pure_bind]
      have e : absIDeclArr out1 = (absIDeclArr out).push (absIDeclaration ds.val[i.val]) := by
        simp [absIDeclArr, ConRon.Refine.vec_push_val hout1, i_declaration_dup_abs hd1]
      rw [← e]
      exact ih
    · rw [ite_eq_right cw] at hout1
      cases Result.ok_injective hout1
      rw [ite_eq_right (by simp [cw]), pure_bind]
      exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact lout_pure hrel hinv rfl
termination_by ds.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi2]; omega

/-- **`recs_loaded` is `recsLoaded`.** -/
theorem recs_loaded_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {ix ix'} (hix : NameIndexRel ix ix') (ds : alloc.vec.Vec arena.env.IDeclaration) (want : Bool) :
    LS pers (fun a b => b = absIDeclArr a) (recs_loaded pers st ix ds want) lst
      (recsLoaded ix' (absIDeclArr ds) want) := by
  have := recs_loaded_loop_ls hix ds want 0#usize (out := alloc.vec.Vec.new _) hrel hinv
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
  rw [recsLoaded, ← Array.foldlM_toList]
  exact this

theorem len_zero_iff {α β : Type} {x : alloc.vec.Vec α} {x' : _root_.Array β}
    (hx : x.val.length = x'.size) : alloc.vec.Vec.len x = 0#usize ↔ x'.isEmpty = true := by
  rw [Array.isEmpty_iff_size_eq_zero, ← hx]
  constructor
  · intro h
    have := congrArg Std.UScalar.val h
    rw [vec_len_val] at this
    exact this
  · intro h
    have : (alloc.vec.Vec.len x).val = 0 := by rw [vec_len_val, h]
    scalar_tac

/-- **`own_recs` is `ownRecs`.** -/
theorem own_recs_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    {x' : _root_.Array Arena.Frontend.Olean.ImportRec} (hx : x.val.length = x'.size)
    {ix ix'} (hix : NameIndexRel ix ix') (ds : alloc.vec.Vec arena.env.IDeclaration) :
    LS pers (fun a b => b = absIDeclArr a) (own_recs pers st x ix ds) lst
      (ownRecs x' ix' (absIDeclArr ds)) := by
  rw [own_recs, ownRecs]
  by_cases h0 : alloc.vec.Vec.len x = 0#usize
  · rw [ite_eq_left h0, ite_eq_left ((len_zero_iff hx).mp h0)]
    intro o st' h
    cases Result.ok_injective h
    exact lout_pure hrel hinv rfl
  · rw [ite_eq_right h0, ite_eq_right (fun e => h0 ((len_zero_iff hx).mpr e))]
    exact recs_loaded_ls hrel hinv hix ds false

/-- **`copy_recs` is `copyRecs`.** -/
theorem copy_recs_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    {x' : _root_.Array Arena.Frontend.Olean.ImportRec} (hx : x.val.length = x'.size)
    {ix ix'} (hix : NameIndexRel ix ix') (ds : alloc.vec.Vec arena.env.IDeclaration) :
    LS pers (fun a b => b = absIDeclArr a) (copy_recs pers st x ix ds) lst
      (copyRecs x' ix' (absIDeclArr ds)) := by
  rw [copy_recs, copyRecs]
  by_cases h0 : alloc.vec.Vec.len x = 0#usize
  · rw [ite_eq_left h0, ite_eq_left ((len_zero_iff hx).mp h0)]
    intro o st' h
    cases Result.ok_injective h
    exact lout_pure hrel hinv rfl
  · rw [ite_eq_right h0, ite_eq_right (fun e => h0 ((len_zero_iff hx).mpr e))]
    exact recs_loaded_ls hrel hinv hix ds true

/-! ## `roots_at` -/

theorem roots_at_loop0_loop0_eq (ns : alloc.vec.Vec arena.handle.NIdx) (k : Std.Usize) {out o}
    (h : roots_at_loop0_loop0 out ns k = ok o) :
    o.val.map absNIdx = out.val.map absNIdx ++ (ns.val.drop k.val).map absNIdx := by
  rw [roots_at_loop0_loop0] at h
  by_cases hlt : k < alloc.vec.Vec.len ns
  · rw [ite_eq_left hlt] at h
    peel h as n, hn
    obtain ⟨hi, rfl⟩ := vec_index_eq hn
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as out1, hout1
    peel h as k1, hk1
    have ih := roots_at_loop0_loop0_eq ns k1 h
    rw [usize_succ hk1] at ih
    rw [ih, ConRon.Refine.vec_push_val hout1, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append, ← List.map_cons, ← List.drop_eq_getElem_cons hi]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    simp
termination_by ns.val.length - k.val
decreasing_by have := lt_len hlt; rw [usize_succ hk1]; omega

/-- The twin's step of `rootsAt`'s copies. -/
def raStep (out : _root_.Array NIdx) (d : IDeclaration) : AM (_root_.Array NIdx) := do
  pure (out ++ (← declNames d).toArray)

theorem roots_at_loop0_ls {pers} (copies : alloc.vec.Vec arena.env.IDeclaration) (i : Std.Usize)
    {st lst out} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxArr a) (roots_at_loop0 pers st out copies i) lst
      (((copies.val.drop i.val).map absIDeclaration).foldlM raStep (absNIdxArr out)) := by
  intro o st' h
  rw [roots_at_loop0] at h
  by_cases hlt : i < alloc.vec.Vec.len copies
  · rw [ite_eq_left hlt] at h
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hi, rfl⟩ := vec_index_eq hd
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.foldlM_cons]
    unfold raStep
    rw [bind_assoc]
    refine lout_bind (decl_names_ls' hrel hinv _) h (by errarm) ?_
    rintro ns b s1 lst1 rfl hrel1 hinv1 h
    simp only [pure_bind]
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ih := roots_at_loop0_ls copies i3 hrel1 hinv1 _ _ h
    have e1 := roots_at_loop0_loop0_eq ns 0#usize hout1
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e1
    have e : absNIdxArr out1 = absNIdxArr out ++ (ns.val.map absNIdx).toArray := by
      apply Array.ext'; simp [ConRon.Refine2.Frontend.absNIdxArr, e1]
    rw [usize_succ hi3, e] at ih
    exact ih
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact lout_pure hrel hinv rfl
termination_by copies.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi3]; omega

/-- **`roots_at` is `rootsAt`**, given `record_reads`'s Theorem 2. -/
theorem roots_at_ls {pers st lst} (hRR : RecordReadsRel pers) (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    {x' : _root_.Array Arena.Frontend.Olean.ImportRec} (hx : x.val.length = x'.size)
    {ix ix'} (hix : NameIndexRel ix ix') {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList)
    (ds : alloc.vec.Vec arena.env.IDeclaration) :
    LS pers (fun a b => b = absNIdxArr a) (roots_at pers st pins x ix cs ds) lst
      (rootsAt (absINatOpPinSetL pins) x' ix' cs' (absIDeclArr ds)) := by
  rw [roots_at, rootsAt]
  by_cases h0 : alloc.vec.Vec.len x = 0#usize
  · rw [ite_eq_left h0, ite_eq_left ((len_zero_iff hx).mp h0), bind_pure]
    exact own_roots_ls hRR hrel hinv pins hix hcs ds
  · rw [ite_eq_right h0, ite_eq_right (fun e => h0 ((len_zero_iff hx).mpr e))]
    simp only [pure_bind]
    intro o st' h
    refine lout_bind (recs_loaded_ls hrel hinv hix ds false) h (by errarm) ?_
    rintro own b s1 lst1 rfl hrel1 hinv1 h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hv' := unloaded_constants_rel hix hcs hv
    refine lout_bind (own_roots_ls hRR hrel1 hinv1 pins hix hv' own) h (by errarm) ?_
    rintro out b s2 lst2 rfl hrel2 hinv2 h
    refine lout_bind (recs_loaded_ls hrel2 hinv2 hix ds true) h (by errarm) ?_
    rintro copies b s3 lst3 rfl hrel3 hinv3 h
    have := roots_at_loop0_ls copies 0#usize (out := out) hrel3 hinv3 _ _ h
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
    rw [← Array.foldlM_toList]
    exact this

/-! ## The context's names distinct -/

theorem ctx_names_nodup_loop_ls {pers} (ctx : alloc.vec.Vec arena.env.IDeclaration) (i : Std.Usize)
    {st lst s S} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hs : NSet s S) :
    LS pers (fun a b => b = a) (ctx_names_nodup_loop pers st ctx s i) lst
      (ctxNamesNodupGo S ((ctx.val.drop i.val).map absIDeclaration)) := by
  intro o st' h
  rw [ctx_names_nodup_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len ctx
  · rw [ite_eq_left hlt] at h
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hi, rfl⟩ := vec_index_eq hd
    rw [List.drop_eq_getElem_cons hi, List.map_cons, ctxNamesNodupGo]
    refine lout_bind (decl_names_ls' hrel hinv _) h (by errarm) ?_
    rintro ns b s1 lst1 rfl hrel1 hinv1 h
    obtain ⟨⟨ok1, s2⟩, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, e2⟩ := names_nodup_go_eq hs hn
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at e1 e2
    rcases hp : namesNodupGo S (ns.val.map absNIdx) with ⟨ok', S'⟩
    rw [hp] at e1 e2
    simp only at e1 e2
    subst e1
    change (if ok1 = true then _ else _) = _ at h
    change LOut pers (fun a b => b = a) o st' (StateT.run (if ok1 = true then
      ctxNamesNodupGo S' ((ctx.val.drop (i.val + 1)).map absIDeclaration) else pure false) lst1)
    by_cases cb : ok1 = true
    · rw [ite_eq_left cb] at h
      rw [ite_eq_left cb]
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ih := ctx_names_nodup_loop_ls ctx i3 hrel1 hinv1 e2 _ _ h
      rw [usize_succ hi3] at ih
      exact ih
    · rw [ite_eq_right cb] at h
      rw [ite_eq_right cb]
      cases Result.ok_injective h
      exact lout_pure hrel1 hinv1 (by simp at cb; simp)
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (not_lt_len hlt), List.map_nil, ctxNamesNodupGo]
    exact lout_pure hrel hinv rfl
termination_by ctx.val.length - i.val
decreasing_by have := lt_len hlt; rw [usize_succ hi3]; omega

/-- **`ctx_names_nodup` is `ctxNamesNodup`.** -/
theorem ctx_names_nodup_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (ctx : alloc.vec.Vec arena.env.IDeclaration) :
    LS pers (fun a b => b = a) (ctx_names_nodup pers st ctx) lst (ctxNamesNodup (absIDeclArr ctx)) := by
  intro o st' h
  rw [ctx_names_nodup] at h
  obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have := ctx_names_nodup_loop_ls ctx 0#usize hrel hinv (nset_empty hs) _ _ h
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
  simpa [ctxNamesNodup, absIDeclArr] using this

/-! ## `OwnUses` as the hoist's `UsedConsts` -/

/-- **The worker's `UsedConsts` instance is `ownUsesOf`**: a theorem the load indexes reads what
the load read; any other record, its `usedConsts`. -/
theorem own_uses_used_rel {u cs' at'} (hu : OwnUsesRel u cs' at') (pers : arena.store.PersTier) :
    ConRon.Refine2.Frontend.UsedRel
      frontend.modular.worker.OwnUses.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts u
      (ownUsesOf cs' at') pers := by
  intro rst lst d o hrel hinv h
  have base : ∀ {o}, frontend.nat_op_ground.decl_used_consts pers rst d = ok o →
      Sim₀ absNIdxArr pers lst o (ConRon.Arena.Frontend.IDeclaration.usedConsts (absIDeclaration d)) :=
    fun h => ConRon.Refine2.Frontend.decl_used_consts_refines hrel hinv h
  simp only [OwnUses.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts.used_consts] at h
  cases d with
  | ThmDecl cv v =>
    obtain ⟨ou, hou, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have e := own_uses_thm_eq hu hou
    simp only [absIDeclaration, ownUsesOf]
    cases ou with
    | none =>
      have e' : ownUsesThm cs' at' (absIConstantVal cv).name = none := by
        simp only [absIConstantVal]; rw [← e]; rfl
      rw [e']
      exact base h
    | some w =>
      have e' : ownUsesThm cs' at' (absIConstantVal cv).name = some (absNIdxArr w) := by
        simp only [absIConstantVal]; rw [← e]; rfl
      rw [e']
      cases Result.ok_injective h
      exact ⟨lst, rfl, hrel, hinv⟩
  | AxiomDecl cv => exact base h
  | DefnDecl cv v hint => exact base h
  | OpaqueDecl cv v => exact base h
  | IndDecl b n => exact base h
  | QuotDecl k cv => exact base h

/-! ## The own records and the home -/

/-- **`own_records`' accept is `ownRecords`'**: the loaded constants, unsafe and partial ones left
out, their groups checked, emitted, read back. -/
theorem own_records_refines {pk : frontend.olean.spec.OleanPins} {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {l : frontend.olean.lazy.Loaded} {l' : Arena.Frontend.Olean.Loaded} (hl : LoadedRel l l') {o ar'}
    (h : own_records pk pers st.store l = ok (.Ok o, ar')) :
    ∃ lst', (ownRecords (absPins pk) l').run lst = .ok (.ok (absIDeclArr o), lst') ∧ ar' = st.store ∧
      AStateRel₀ pers st lst' ∧ AStateInv pers st := by
  rw [own_records] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨mg, hmg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hM := merged_of_list_rel (unskipped_rel hl.constants hv) hmg
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok u =>
  obtain ⟨b, hB, -⟩ := blocks_ok_pr hM _ hr lst
  obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok em =>
  obtain ⟨lem, hE, hER⟩ := emit_all_rel hM hM.order _ hr1 lst
  obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok p =>
  obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  cases h1
  obtain ⟨w, lst', hD, hPR, hrel', hinv'⟩ := decls_of_rel hrel hinv hER hr2
  refine ⟨lst', ?_, rfl, hrel', hinv'⟩
  unfold ownRecords
  rw [am_bind_ok hB, am_bind_ok hE, am_bind_ok hD]
  show (pure (Except.ok w.decls) : AM _).run lst' = _
  rw [hPR.decls]
  rfl

/-- **`home_of`'s accept is `homeOf`'s**: the private view loaded (`load_view`), its parts
checked against each other over the load (`check_views`). -/
theorem home_of_refines' {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {m : arena.handle.NIdx} {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles}
    (hf : ModFilesRel f f') {st lst} :
    AS pers (fun a b => LoadedRel a.1 b.1 ∧ ExpoRel a.2 b.2) st lst (home_of pk pers st.store m f)
      (homeOf (absPins pk) (absNIdx m) f') := by
  intro hrel hinv a s' h
  rw [home_of] at h
  obtain ⟨⟨r, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok l =>
  obtain ⟨l', lst1, hx1, hL, hrel1, hinv1⟩ := load_view_refines hf hrel hinv l ar1 h1
  obtain ⟨⟨r2, ar3⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok expo =>
  obtain ⟨h4, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  cases h4
  obtain ⟨e', lst3, hx3, hE, hrel3, hinv3⟩ :=
    check_views_refines (st := withStore st ar1) hf hL hrel1 hinv1 expo ar3 h3
  refine ⟨(l', e'), lst3, ?_, ⟨hL, hE⟩, hrel3, hinv3⟩
  have hx1' : (Arena.Frontend.Olean.loadView (absPins pk) 0 (absNIdx m) f').run lst = .ok (l', lst1) := hx1
  unfold homeOf
  rw [am_bind_ok hx1', am_bind_ok hx3]
  rfl

end ConRon.Refine2.Modular
