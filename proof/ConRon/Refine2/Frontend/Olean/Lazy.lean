/-
# `ConRon.Refine2.Frontend.Olean.Lazy` — `olean/lazy.rs` against the twin's

**Task #143, Theorem 2** (upstream task #481).  A module's load, its theorems' values left in
the file: what each constant mentions, read off the file (`uses_go`, `uses_roots`, `uses_of`,
`uses_read`), the constants with a theorem's value a reference (`lazy_entry`, `value_ref`),
the frontier (`frontier_walk`, `frontier_of`), and the load around them (`load_at`,
`load_view`).  The two walks carry fuel on both sides (the twin's `Arena/Frontend/Olean/
Lazy.lean` note); a stack is a `Vec` and its top against a `List` (`StackRel`).

A load is reached through a file read (`load_module`), so each statement here claims the
Rust's accept: its `Ok` is the twin's `some`, the answers and the states related.
-/
import ConRon.Refine2.Frontend.Olean.Sparse
import ConRon.Refine2.Frontend.Olean.Closure
import ConRon.Refine2.Frontend.Olean.View
import ConRon.Refine2.Frontend.Olean.FastRoots
import ConRon.Arena.Frontend.Olean.Lazy

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.lazy

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (loadAt loadView loadRoots valueRoots lazyEntries loadImports
  usesOf frontierWalk frontierOf)
open ConLeche.Frontend.Olean (usesNames lazyRoots maxLoc closureFuel moduleSkel)

/-! ## The judgement of an accepted read -/

/-- **A read's accept**: the Rust's `Ok` is the twin's `some`, the answers related by `R` and
the states as every reader relates them. -/
def AR {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore))
    (x : AM (Option β)) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st →
    ∀ a s', m = ok (.Ok a, s') →
      ∃ b lst', x.run lst = .ok (some b, lst') ∧ R a b ∧
        AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s')

/-- A read's lockstep judgement claims its accept. -/
theorem RS.ar {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {m} {x : AM (Option β)} (h : RS pers R st lst m x) :
    AR pers R st lst m x := by
  intro hrel hinv a s' hm
  exact h hrel hinv _ _ hm

/-! ## The relations of a load's data -/

/-- The walk's stamps, by slot, as the twin's. -/
def StampsRel (s : alloc.vec.Vec Std.U64) (t : Array Nat) : Prop := s.val.map (·.val) = t.toList

/-- What the walk writes, as the twin's words. -/
def OutRel (o : alloc.vec.Vec Std.U64) (t : Array UInt64) : Prop := o.val.map absWord = t.toList

/-- Every constant's output. -/
def OutsRel (o : alloc.vec.Vec (alloc.vec.Vec Std.U64)) (t : Array (Array UInt64)) : Prop :=
  List.Forall₂ OutRel o.val t.toList

/-! ## The roots of a load -/

/-- **`load_roots` is `loadRoots`**: the imports' names and every constant's names, and every
constant's expressions. -/
theorem load_roots_val {sk : frontend.olean.spec.ModSkel} {sk' : ConLeche.Frontend.Olean.ModSkel}
    {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hsk : ModSkelRel sk sk')
    (hv : List.Forall₂ EV v.val skels) {nb ea}
    (h : load_roots sk v = ok (nb, ea)) :
    nb.val.map absWord = (loadRoots sk' skels).1 ∧ ea.val.map absWord = (loadRoots sk' skels).2 := by
  sorry -- T143-STUB

/-- **`uses_of` is `usesOf`**, from fresh stamps: every constant's output. -/
theorem uses_of_ok {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {stamps : alloc.vec.Vec Std.U64} {ts : Array Nat} (hs : StampsRel stamps ts)
    {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hv : List.Forall₂ EV v.val skels)
    {o3 s'} (h : uses_of bs r stamps 1#u64 v = ok (some o3, s')) :
    ∃ outs, usesOf (absRegion bs r) ts 1 skels (Array.mkEmpty skels.length) = some outs ∧
      OutsRel o3 outs := by
  sorry -- T143-STUB

/-- **`uses_names` appends `usesNames`.** -/
theorem uses_names_val {o3 : alloc.vec.Vec (alloc.vec.Vec Std.U64)} {outs : Array (Array UInt64)}
    (ho : OutsRel o3 outs) {acc acc' : alloc.vec.Vec Std.U64}
    (h : uses_names o3 acc = ok acc') :
    acc'.val.map absWord = acc.val.map absWord ++ usesNames outs := by
  sorry -- T143-STUB

/-- **`load_at`'s loop collects `lazyRoots`.** -/
theorem load_at_loop_val {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hv : List.Forall₂ EV v.val skels)
    {o} (h : load_at_loop v (alloc.vec.Vec.new Std.U64) 0#usize = ok o) :
    o.val.map absWord = skels.flatMap lazyRoots := by
  sorry -- T143-STUB

/-- **`load_imports`' accept is `loadImports`' `true`.** -/
theorem load_imports_ok {pk pers st lst} {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r) (hd : DSRel d t)
    {sk : frontend.olean.spec.ModSkel} {sk' : ConLeche.Frontend.Olean.ModSkel} (hsk : ModSkelRel sk sk')
    {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles} (hf : ModFilesRel f f') :
    AR pers (fun (_ : Unit) (b : Unit) => b = ()) st lst (load_imports pk pers st.store bs r d sk f)
      (do if ← loadImports (absPins pk) (absRegion bs r) t sk' f' then pure (some ()) else pure none) := by
  sorry -- T143-STUB

/-- **`lazy_entries`' accept is `lazyEntries`'**: each constant read, a theorem's value its
reference, with what it mentions. -/
theorem lazy_entries_ok {pk pers st lst} {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r) (hd : DSRel d t) {i : Std.U64}
    {o3 : alloc.vec.Vec (alloc.vec.Vec Std.U64)} {outs : Array (Array UInt64)} (ho : OutsRel o3 outs)
    {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hv : List.Forall₂ EV v.val skels) :
    AR pers (fun cs L => List.Forall₂ CEntryRel cs.val L) st lst
      (lazy_entries pk pers st.store bs r d i o3 v)
      (lazyEntries (absPins pk) (absRegion bs r) t i.val outs 0 skels) := by
  sorry -- T143-STUB

/-- **`value_roots` is `valueRoots`.** -/
theorem value_roots_val {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hv : List.Forall₂ EV v.val skels)
    {o} (h : value_roots r v = ok o) : o.val.map (·.val) = valueRoots (absRegion bs r) skels := by
  sorry -- T143-STUB

/-- **`frontier_walk` is `frontierWalk`**, from the value roots on the stack. -/
theorem frontier_walk_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {env seen fr : alloc.vec.Vec Std.U8} {values : alloc.vec.Vec Std.U64}
    {o} (h : frontier_walk bs r env seen fr values (alloc.vec.Vec.len values) = ok o) :
    absM o.2.1 = frontierWalk (absRegion bs r) (absM env) (absM seen) (absM fr) closureFuel
      (values.val.map (·.val)).reverse := by
  sorry -- T143-STUB

/-- **`frontier_of` is `frontierOf`**, from the empty frontier. -/
theorem frontier_of_rel {m fr : alloc.vec.Vec Std.U8} {d : frontend.olean.fast.DS} {t : TDS}
    (hd : DSRel d t) {n : Std.U64} {b0 b} (hb0 : frontend.olean.sparse.frontier_empty = ok b0)
    (h : frontier_of m fr d n 0#u64 b0 = ok b) :
    FrontierRel b (frontierOf (absM m) (absM fr) t n.val 0 {}) := by
  sorry -- T143-STUB

/-! ## The load -/

/-- **`load_at`'s accept is `loadAt`'s**: the load of a module's private view, everything but
its theorems' values. -/
theorem load_at_ok {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {i : Std.U64} {m : arena.handle.NIdx}
    {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles}
    (hf : ModFilesRel f f') :
    AR pers LoadedRel st lst (load_at pk pers st.store i m f)
      (loadAt (absPins pk) i.val (absNIdx m) f') := by
  intro hrel hinv a s' h
  rw [load_at] at h
  peel h as o, ho
  have hV := mod_files_view_region_eq hf ho
  cases o with
  | none => cases (Prod.mk.inj (Result.ok_injective h)).1
  | some p =>
  obtain ⟨vb, a0⟩ := p
  peel h as bs, hbs
  peel h as r, hr
  obtain ⟨hvr, hfit⟩ := hV bs r hbs hr
  obtain ⟨⟨r1, ar1⟩, hq1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hC := const_names_ok_refines (pk := pk) (root := a0) hfit hrel hinv r1 ar1 hq1
  cases r1 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok b =>
  obtain ⟨b', lst1, hx1, hb', hrel1, hinv1⟩ := hC
  subst hb'
  cases b with
  | false => cases (Prod.mk.inj (Result.ok_injective h)).1
  | true =>
  dsimp only [↓reduceIte] at h
  peel h as o1, ho1
  have hsk := module_skel_eq hfit ho1
  cases o1 with
  | none => cases (Prod.mk.inj (Result.ok_injective h)).1
  | some sk =>
  obtain ⟨sk', hsk', hskR⟩ : ∃ sk', moduleSkel (absRegion bs r) (absWord a0) = some sk' ∧
      ModSkelRel sk sk' := by
    cases hh : moduleSkel (absRegion bs r) (absWord a0) with
    | none => rw [hh] at hsk; cases hsk
    | some sk' => rw [hh] at hsk; cases hsk with | some h => exact ⟨sk', rfl, h⟩
  peel h as r2, hr2
  have hP := consts_skel_ps (bs := bs) (r := r) hskR.consts r2 hr2 lst1
  cases r2 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok v =>
  obtain ⟨skels, hx2, hEV⟩ := hP
  dsimp only at h
  obtain ⟨⟨nb, ea⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hnb, hea⟩ := load_roots_val hskR hEV hq
  peel h as i1, hi1
  peel h as i2, hi2
  peel h as i3, hi3
  peel h as n, hn
  peel h as i4, hi4
  peel h as stamps, hstamps
  have e1 := max_loc_eq (bs := bs) hi1
  have e2 := max_loc_eq (bs := bs) hi2
  have e3 := ConRon.Refine.HashMap.uscalar_div_eq hi3
  have e4 := ConRon.Refine.HashMap.uscalar_add_eq hn
  have hnv : n.val = maxLoc (absRegion bs r) (loadRoots sk' skels).2
      (maxLoc (absRegion bs r) (loadRoots sk' skels).1 0) / 8 + 1 := by
    rw [e4, e3, e2, e1, hnb, hea]; rfl
  have hle := maxLoc_le hfit (ea.val.map absWord) (maxLoc_le hfit (nb.val.map absWord) (Nat.zero_le _))
  have hL := bytes_le_max bs
  have hLn : n.val = maxLoc (absRegion bs r) (ea.val.map absWord)
      (maxLoc (absRegion bs r) (nb.val.map absWord) 0) / 8 + 1 := by
    rw [e4, e3, e2, e1]; rfl
  have hmx := usize_max_ge
  have hnm : n.val ≤ Std.Usize.max := by omega
  have hi4v : i4.val = n.val := by
    simp only [lift] at hi4
    rw [← Result.ok_injective hi4]
    exact ConRon.Refine.ExprOps.u64_cast_usize_val hnm
  have hstv : StampsRel stamps (Array.replicate n.val 0) := by
    sorry -- T143-STUB
  obtain ⟨⟨o2, s2⟩, hq2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o2 with
  | none => cases (Prod.mk.inj (Result.ok_injective h)).1
  | some o3 =>
  obtain ⟨outs, hU, hO⟩ := uses_of_ok hfit hstv hEV hq2
  peel h as nb1, hnb1
  have enb1 := uses_names_val hO hnb1
  peel h as lz, hlz
  have elz := load_at_loop_val hEV hlz
  obtain ⟨⟨r3, ar2⟩, hq3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hM := run_marked_refines (pk := pk) (pers := pers) (st := withStore st ar1) (lst := lst1)
    (names := nb1) (exprs := lz) hfit hrel1 hinv1 r3 ar2 hq3
  cases r3 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok x =>
  obtain ⟨nm, ms, d⟩ := x
  obtain ⟨⟨nm', ms', t⟩, lst3, hx3, ⟨hnmv, hmsv, hd⟩, hrel3, hinv3⟩ := hM
  obtain ⟨⟨r4, ar3⟩, hq4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r4 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok u =>
  obtain ⟨u', lst4, hx4, -, hrel4, hinv4⟩ := load_imports_ok (pk := pk) hfit hd hskR hf hrel3 hinv3 _ _ hq4
  obtain ⟨⟨r5, ar4⟩, hq5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r5 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok cs =>
  obtain ⟨cs', lst5, hx5, hcs, hrel5, hinv5⟩ :=
    lazy_entries_ok (pk := pk) (i := i) hfit hd hO hEV hrel4 hinv4 _ _ hq5
  peel h as values, hvalues
  have evals := value_roots_val (bs := bs) hEV hvalues
  peel h as i5, hi5
  peel h as seen, hseen
  peel h as i6, hi6
  peel h as fr, hfr
  obtain ⟨⟨seen1, fr1, st1⟩, hq6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have efw := frontier_walk_eq hfit hq6
  peel h as b0, hb0
  peel h as frontier, hfront
  have efo := frontier_of_rel hd hb0 hfront
  peel h as n1, hn1
  obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  cases h1
  have hvr' : f'.viewRegion .private = some (absRegion bs r, absWord a0) := hvr
  refine ⟨⟨absNIdx m, cs'.toArray, frontierOf (absM ms) (absM fr1) t nm.val 0 {}⟩, lst5, ?_,
    ⟨by rw [nidx_dup2_ok hn1], by simpa using hcs, ?_⟩, hrel5, hinv5⟩
  · rw [loadAt]
    simp only [hvr']
    rw [StateT.run_bind, hx1]
    simp only [hsk']
    -- the twin's imports' check, out of its `Option` wrapper
    have hli : (loadImports (absPins pk) (absRegion bs r) t sk' f').run lst3 = .ok (true, lst4) := by
      rw [StateT.run_bind] at hx4
      cases hl : (loadImports (absPins pk) (absRegion bs r) t sk' f').run lst3 with
      | error e => rw [hl] at hx4; cases hx4
      | ok p =>
        obtain ⟨bb, l⟩ := p
        rw [hl] at hx4
        cases bb with
        | true => cases hx4; rfl
        | false => cases hx4
    rw [hnmv, hmsv] at efo
    rw [hnv] at hU
    rw [enb1, hnb, elz] at hx3
    have hi5v : i5.val = n.val := by
      simp only [lift] at hi5
      rw [← Result.ok_injective hi5]
      exact ConRon.Refine.ExprOps.u64_cast_usize_val hnm
    have hi6v : i6.val = n.val := by
      simp only [lift] at hi6
      rw [← Result.ok_injective hi6]
      exact ConRon.Refine.ExprOps.u64_cast_usize_val hnm
    rw [zeros_eq hseen, zeros_eq hfr, hi5v, hi6v, evals, hnv] at efw
    simp only [ConRon.Refine2.except_ok_bind, ↓reduceIte, StateT.run_bind, StateT.run_pure, pure_bind,
      hx2, hU, hx3, hli, hx5,
      hmsv, efw]
    rw [hnmv]
    rfl
  · exact efo

/-- **`load_view`'s accept is `loadView`'s.** -/
theorem load_view_refines {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {i : Std.U64} {m : arena.handle.NIdx}
    {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles}
    (hf : ModFilesRel f f') :
    AS pers LoadedRel st lst (load_view pk pers st.store i m f)
      (loadView (absPins pk) i.val (absNIdx m) f') := by
  intro hrel hinv a s' h
  rw [load_view] at h
  obtain ⟨⟨r, ar1⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Ok l =>
    obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := load_at_ok hf hrel hinv _ _ hq
    refine ⟨b, lst1, ?_, hR, hrel1, hinv1⟩
    rw [loadView, StateT.run_bind, hx]
    rfl
  | Err e =>
    cases e with
    | Bad =>
      obtain ⟨⟨ce, ar2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases (Prod.mk.inj (Result.ok_injective h)).1
    | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1

end ConRon.Refine2.Frontend.Olean
