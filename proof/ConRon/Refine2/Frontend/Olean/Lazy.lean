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
open ConLeche.Frontend.Olean (usesNames lazyRoots maxLoc closureFuel)

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
  sorry -- T143-STUB

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
