/-
# `ConRon.Refine2.Frontend.Olean.ClosureRead` — `olean/closure.rs`: the import walk, and the load

**Tasks #142, #143, Theorem 2.**  `closure_go`, `closure_order`, `load_module` (the module's
files, then its lazy load), `load_all`, `load_closure` against the twin's.  Each reaches a file
read, so each claims its accept (`AS`).
-/
import ConRon.Refine2.Frontend.Olean.Lazy
import ConRon.Refine2.Frontend.Olean.FilesRead

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.closure

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine2 (AErrKind absAErrKind AErrSim)
open ConRon.Refine.HashMap2 (Inv toFun)
open ConRon.Arena.Frontend.Olean (closureGo closureOrder loadModule loadClosure moduleImports)
open ConRon.Refine2.Lockstep (LSP)

/-! ## The twin's walk -/

theorem go_done {fs pk sp f m rest s d o} :
    closureGo fs pk sp (f + 1) ((m, true) :: rest) s d o = closureGo fs pk sp f rest s (d.insert m) (o.push m) := by
  rw [closureGo]

theorem go_seen {fs pk sp f m rest s d o} (hc : s.contains m = true) :
    closureGo fs pk sp (f + 1) ((m, false) :: rest) s d o = closureGo fs pk sp f rest s d o := by
  rw [closureGo, ite_eq_left hc]

theorem imports_modules (imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) :
    (absImports imps).map (·.module) = (imps.val.map impMod).toArray := by
  simp [absImports, absImportF, Function.comp_def]

/-- A first visit, the imports read and no import on the walk's path. -/
theorem go_expand {fs pk sp f m rest s d o} {lst lst1 : AState}
    {imps : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    (hc : s.contains m = false)
    (hx : (moduleImports fs pk sp m).run lst = .ok (absImports imps, lst1))
    (hf : (imps.val.map impMod).find? (fun i => (s.insert m).contains i && !d.contains i) = none) :
    (closureGo fs pk sp (f + 1) ((m, false) :: rest) s d o).run lst =
      (closureGo fs pk sp f (walkKids (s.insert m) (imps.val.map impMod) ++ (m, true) :: rest)
        (s.insert m) d o).run lst1 := by
  rw [closureGo, ite_eq_right (by simp [hc])]
  rw [am_bind_ok hx]
  dsimp only
  rw [imports_modules, List.find?_toArray, hf]

/-! ## `closure_go` -/

section walk

variable {F : Type} {inst : frontend.olean.files.OleanFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
  {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
  {sp_dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)}

/-- A tail that ends in an `Err`, with a store beside it. -/
macro "err_any2" : tactic => `(tactic| (
  repeat' first
    | exact fun _ h => ⟨_, by cases Result.ok_injective h; rfl⟩
    | (refine ConRon.Refine2.Lockstep.LSP.bind_eq fun _ _ => ?_)))

theorem not_ok_of_err2 {α : Type} {m : Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore)}
    {a s'} (hm : LSP m (fun o => ∃ e, o.1 = .Err e)) : m ≠ ok (.Ok a, s') := by
  intro h
  obtain ⟨_, he⟩ := hm _ h
  cases he

/-- **`closure_go`'s loop against `closureGo`.** -/
theorem closure_go_loop_ok (hfs : FsRel inst fsv fs)
    (f : Nat) (st : arena.monad.AState) (lst : AState) (stack : alloc.vec.Vec (arena.handle.NIdx × Bool))
    (sp : Std.Usize) (fuel : Std.U64) (seen done1 : ron.hashmap2.HashMap2 arena.handle.NIdx Bool)
    (out : alloc.vec.Vec arena.handle.NIdx) (l : List (NIdx × Bool)) (s d : _root_.Std.HashSet NIdx)
    (o' : _root_.Array NIdx) (hf : fuel.val = f) (hl : StackRel absWEnt stack sp l) (hs : NSet seen s)
    (hd : NSet done1 d) (ho : OutA out o') :
    AS pers OutA st lst (closure_go_loop inst fsv pk pers st.store sp_dirs stack sp fuel seen done1 out)
      (closureGo fs (absPins pk) (absSearchPath sp_dirs) f l s d o') := by
  intro hrel hinv a s' h
  rw [closure_go_loop] at h
  by_cases hsp : sp > 0#usize
  swap
  · rw [ite_eq_right hsp] at h
    obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
    have hnil := hl.nil_of_zero hsp
    subst hnil
    have e : closureGo fs (absPins pk) (absSearchPath sp_dirs) f [] s d o' = pure o' := by rw [closureGo]
    rw [e]
    exact ⟨o', lst, rfl, ho, hrel, hinv⟩
  rw [ite_eq_left hsp] at h
  by_cases h0 : fuel = 0#u64
  · rw [ite_eq_left h0] at h
    peel h as r0, hr0
    obtain ⟨c, rfl, -⟩ := out_of_fuel_eq hr0
    obtain ⟨h1, -⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
  rw [ite_eq_right h0] at h
  peel h as fuel1, hfuel1
  peel h as sp1, hsp1
  peel h as q, hq
  obtain ⟨n, b⟩ := q
  peel h as m, hm
  cases nidx_dup2_ok hm
  obtain ⟨hi, l', rfl, hl'⟩ := hl.pop hsp hsp1
  obtain ⟨hi', he⟩ := vec_index_eq hq
  rw [← he]
  have hfv : fuel1.val = f - 1 := by
    rw [ConRon.Refine.HashMap.uscalar_sub_eq hfuel1, hf]; rfl
  have hfp : f ≠ 0 := by
    intro hz
    apply h0
    apply UScalar.eq_of_val_eq
    rw [hf, hz]; rfl
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hfv' : fuel1.val = f' := by rw [hfv]; rfl
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    peel h as p, hp
    obtain ⟨_, done2⟩ := p
    peel h as out1, ho1
    have ins := SetRel.insert nidx_eq2 absNIdx_inj hd hp
    have ho' : OutA out1 (o'.push (absNIdx n)) := by
      show out1.val.map absNIdx = _
      rw [ConRon.Refine.vec_push_val ho1, List.map_append, ho]
      simp
    have e : closureGo fs (absPins pk) (absSearchPath sp_dirs) (f' + 1) (absWEnt (n, true) :: l') s d o' =
        closureGo fs (absPins pk) (absSearchPath sp_dirs) f' l' s (d.insert (absNIdx n)) (o'.push (absNIdx n)) :=
      go_done
    rw [e]
    exact closure_go_loop_ok hfs f' st lst stack sp1 fuel1 seen done2 out1 l' s _ _ hfv' hl' hs ins ho' hrel hinv a s' h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    peel h as c, hc
    have ec := SetRel.contains_key nidx_eq2 hs hc
    by_cases cc : c = true
    · rw [ite_eq_left cc] at h
      have e : closureGo fs (absPins pk) (absSearchPath sp_dirs) (f' + 1) (absWEnt (n, false) :: l') s d o' =
          closureGo fs (absPins pk) (absSearchPath sp_dirs) f' l' s d o' :=
        go_seen (by rw [← ec]; exact cc)
      rw [e]
      exact closure_go_loop_ok hfs f' st lst stack sp1 fuel1 seen done1 out l' s d o' hfv' hl' hs hd ho hrel hinv a s' h
    rw [ite_eq_right cc] at h
    peel h as p, hp
    obtain ⟨r, ar1⟩ := p
    cases r with
    | Err x =>
      obtain ⟨h1, -⟩ := Prod.mk.inj (Result.ok_injective h)
      cases h1
    | Ok imps =>
      obtain ⟨b1, lst1, hx, hR, hrel1, hinv1⟩ := module_imports_refines (st := st) (lst := lst) (sp := sp_dirs)
        hfs hrel hinv _ _ hp
      cases show b1 = absImports imps from hR
      peel h as n1, hn1
      cases nidx_dup2_ok hn1
      peel h as p1, hp1
      obtain ⟨_, seen1⟩ := p1
      have ins := SetRel.insert nidx_eq2 absNIdx_inj hs hp1
      peel h as o, hoo
      have eo := import_on_path_eq ins hd hoo
      cases o with
      | some x =>
        exact absurd h (not_ok_of_err2 (by err_any2))
      | none =>
        dsimp only at h
        peel h as p2, hp2
        obtain ⟨sp2, stack1⟩ := p2
        have hS := walk_expand_eq ins hl' hp2
        have e := go_expand (fs := fs) (pk := absPins pk) (sp := absSearchPath sp_dirs) (f := f') (m := absNIdx n)
          (rest := l') (s := s) (d := d) (o := o') (lst := lst) (lst1 := lst1) (imps := imps)
          (by rw [← ec]; simpa using cc) hx eo.symm
        have e' : (closureGo fs (absPins pk) (absSearchPath sp_dirs) (f' + 1) (absWEnt (n, false) :: l') s d o').run lst = _ := e
        rw [e']
        exact closure_go_loop_ok hfs f' (withStore st ar1) lst1 stack1 sp2 fuel1 seen1 done1 out _ _ _ _ hfv' hS ins hd ho
          hrel1 hinv1 a s' h
termination_by f
decreasing_by all_goals omega

theorem nset_empty {m : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    (hm : ron.hashmap2.HashMap2.new arena.handle.NIdx Bool = ok m) : NSet m {} := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hm
  exact ⟨hinv, fun k => by rw [hnone]; simp⟩

/-- **`closure_go`'s accept is `closureGo`**, from nothing seen. -/
theorem closure_go_refines {st : arena.monad.AState} {lst : AState}
    {stack : alloc.vec.Vec (arena.handle.NIdx × Bool)} {top : Std.Usize} {l : List (NIdx × Bool)}
    (hfs : FsRel inst fsv fs) (hl : StackRel absWEnt stack top l) :
    AS pers OutA st lst (closure_go inst fsv pk pers st.store sp_dirs stack top)
      (closureGo fs (absPins pk) (absSearchPath sp_dirs) ConLeche.Frontend.Olean.closureFuel l {} {} #[]) := by
  intro hrel hinv a s' h
  rw [closure_go] at h
  peel h as fuel, hfuel
  peel h as seen, hseen
  exact closure_go_loop_ok hfs _ st lst stack top fuel seen seen _ l {} {} #[] (closure_fuel_val hfuel) hl
    (nset_empty hseen) (nset_empty hseen) (by simp [OutA, alloc.vec.Vec.new]) hrel hinv a s' h

/-- **`closure_order`'s accept is `closureOrder`.** -/
theorem closure_order_refines {st : arena.monad.AState} {lst : AState}
    {roots : alloc.vec.Vec arena.handle.NIdx} (hfs : FsRel inst fsv fs) :
    AS pers OutA st lst (closure_order inst fsv pk pers st.store sp_dirs roots)
      (closureOrder fs (absPins pk) (absSearchPath sp_dirs) (absNIdxArr roots)) := by
  intro hrel hinv a s' h
  rw [closure_order] at h
  peel h as q, hq
  obtain ⟨stack1, sp⟩ := q
  have hS := closure_order_loop_eq roots _ _ _ (StackRel.empty absWEnt _) hq
  rw [vec_len_val, List.take_length, List.append_nil] at hS
  have e : closureOrder fs (absPins pk) (absSearchPath sp_dirs) (absNIdxArr roots) =
      closureGo fs (absPins pk) (absSearchPath sp_dirs) ConLeche.Frontend.Olean.closureFuel
        (roots.val.map fun r => (absNIdx r, false)) {} {} #[] := by
    simp [closureOrder, absNIdxArr, List.map_map, Function.comp_def]
  rw [e]
  exact closure_go_refines hfs hS hrel hinv a s' h

/-! ## The load -/

theorem array_mapM_run {α β : Type} (f : α → AM β) (a : _root_.Array α) (lst : AState) :
    (a.mapM f).run lst = ((a.toList.mapM f >>= fun ys => pure ys.toArray) : AM _).run lst := by
  rw [Array.mapM_eq_mapM_toList]
  rfl

/-- **`load_module`'s accept is `loadModule`**: the module's files, then its lazy load. -/
theorem load_module_ok {st : arena.monad.AState} {lst : AState} {total idx : Std.U64}
    {m : arena.handle.NIdx} (hfs : FsRel inst fsv fs)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) {a s'}
    (h : load_module inst fsv pk pers st.store sp_dirs total m idx = ok (.Ok a, s')) :
    ∃ b lst', (loadModule fs (absPins pk) (absSearchPath sp_dirs) total.val (absNIdx m) idx.val).run lst
        = .ok (b, lst') ∧
      LoadedRel a b ∧ AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s') := by
  rw [load_module] at h
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok f =>
    dsimp only at h
    obtain ⟨n, hn⟩ := read_files_name hr
    obtain ⟨f', e1, hf⟩ := read_files_refines hfs hn hr
    peel h as q, hq
    obtain ⟨r1, ar1⟩ := q
    peel h as q2, hq2
    obtain ⟨r2, size⟩ := q2
    peel h as u, -
    obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    have hr2 : r2 = r1 := by
      cases r1 with
      | Ok l =>
        dsimp only at hq2
        peel hq2 as sz, -
        exact (Prod.mk.inj (Result.ok_injective hq2)).1.symm
      | Err _ => exact (Prod.mk.inj (Result.ok_injective hq2)).1.symm
    subst hr2 h1
    have hF := load_view_refines (st := st) (lst := lst) (i := idx) (m := m) hf hrel hinv _ _ hq
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := hF
    refine ⟨b, lst1, ?_, hR, hrel1, hinv1⟩
    show ((Arena.readName (absNIdx m)) >>= _).run lst = _
    rw [am_bind_ok (read_name_run hrel hn)]
    have e1' : Arena.Frontend.Olean.readFiles fs (absSearchPath sp_dirs) (ConRon.Refine.absName n)
        .private = .ok f' := e1
    simp only [e1', Arena.Frontend.Olean.liftE]
    show ((pure f' : AM _) >>= _).run lst = _
    rw [am_bind_ok rfl, am_bind_ok hx]
    rfl

/-- The loop of `load_all`: the rest of the order, each module with its position. -/
theorem load_all_loop_ok (hfs : FsRel inst fsv fs)
    (order : alloc.vec.Vec arena.handle.NIdx) (st : arena.monad.AState) (lst : AState)
    (out : alloc.vec.Vec frontend.olean.lazy.Loaded) (total : Std.U64) (i : Std.Usize)
    {acc : List Arena.Frontend.Olean.Loaded} (ho : List.Forall₂ LoadedRel out.val acc) :
    AS pers (fun (o : alloc.vec.Vec frontend.olean.lazy.Loaded) (ys : List Arena.Frontend.Olean.Loaded) =>
        List.Forall₂ LoadedRel o.val (acc ++ ys)) st lst
      (load_all_loop inst fsv pk pers st.store sp_dirs order out total i)
      ((((order.val.drop i.val).map absNIdx).zipIdx i.val).mapM fun (p : NIdx × Nat) =>
        loadModule fs (absPins pk) (absSearchPath sp_dirs) total.val p.1 p.2) := by
  intro hrel hinv a s' h
  rw [load_all_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len order
  · rw [ite_eq_left hlt] at h
    peel h as n, hn
    obtain ⟨hi, rfl⟩ := vec_index_eq hn
    peel h as i2, hi2
    have hi2v : i2.val = i.val := by
      simp only [lift, Result.ok.injEq] at hi2
      subst hi2
      rw [usize_cast_u64_val']
    peel h as q, hq
    obtain ⟨r, ar1⟩ := q
    cases r with
    | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
    | Ok l =>
      obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := load_module_ok hfs hrel hinv hq
      peel h as out1, ho1
      peel h as i3, hi3
      have hi3v : i3.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi3]; rfl
      have ho' : List.Forall₂ LoadedRel out1.val (acc ++ [b]) := by
        rw [ConRon.Refine.vec_push_val ho1]
        exact List.rel_append ho (.cons hR .nil)
      obtain ⟨ys, lst2, hys, hF, hrel2, hinv2⟩ :=
        load_all_loop_ok hfs order (withStore st ar1) lst1 out1 total i3 ho' hrel1 hinv1 a s' h
      rw [hi3v] at hys
      refine ⟨b :: ys, lst2, ?_, by simpa using hF, hrel2, hinv2⟩
      rw [List.drop_eq_getElem_cons hi, List.map_cons, List.zipIdx_cons, List.mapM_cons]
      rw [hi2v] at hx
      rw [am_bind_ok hx, am_bind_ok hys]
      rfl
  · rw [ite_eq_right hlt] at h
    obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
    have hle : order.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len order).val := hlt
      rw [vec_len_val] at this; omega
    rw [List.drop_of_length_le hle]
    exact ⟨[], lst, rfl, by simpa using ho, hrel, hinv⟩
termination_by order.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len order).val := hlt
  rw [vec_len_val] at this
  omega

/-- The relation of a load. -/
abbrev LoadedA (ls : alloc.vec.Vec frontend.olean.lazy.Loaded) (ls' : _root_.Array Arena.Frontend.Olean.Loaded) : Prop :=
  List.Forall₂ LoadedRel ls.val ls'.toList

/-- **`load_all`'s accept is the twin's `loadAll`.** -/
theorem load_all_refines {st : arena.monad.AState} {lst : AState}
    {order : alloc.vec.Vec arena.handle.NIdx} {order' : _root_.Array NIdx} (ho : OutA order order')
    (hfs : FsRel inst fsv fs) :
    AS pers LoadedA st lst (load_all inst fsv pk pers st.store sp_dirs order)
      (Arena.Frontend.Olean.loadAll fs (absPins pk) (absSearchPath sp_dirs) order') := by
  intro hrel hinv a s' h
  rw [load_all] at h
  peel h as total, htotal
  have htv : total.val = order'.size := by
    simp only [lift, Result.ok.injEq] at htotal
    subst htotal
    rw [usize_cast_u64_val', vec_len_val, ← Array.length_toList, ← ho, List.length_map]
  obtain ⟨ys, lst1, hys, hF, hrel1, hinv1⟩ := load_all_loop_ok hfs order st lst _ total _
    (acc := []) .nil hrel hinv a s' h
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero, ho, htv] at hys
  refine ⟨ys.toArray, lst1, ?_, by simpa using hF, hrel1, hinv1⟩
  rw [Arena.Frontend.Olean.loadAll]
  show ((List.mapM _ _ : AM _) >>= fun ys => pure ys.toArray).run lst = _
  rw [StateT.run_bind, hys]
  rfl

/-- **`load_closure`'s accept is `loadClosure`.** -/
theorem load_closure_refines {st : arena.monad.AState} {lst : AState}
    {roots : alloc.vec.Vec arena.handle.NIdx} (hfs : FsRel inst fsv fs) :
    AS pers LoadedA st lst (load_closure inst fsv pk pers st.store sp_dirs roots)
      (loadClosure fs (absPins pk) (absSearchPath sp_dirs) (absNIdxArr roots)) := by
  intro hrel hinv a s' h
  rw [load_closure] at h
  peel h as s0, -
  peel h as v0, -
  peel h as u0, -
  peel h as q, hq
  obtain ⟨r, ar1⟩ := q
  cases r with
  | Err e =>
    obtain ⟨h1, -⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
  | Ok order =>
    dsimp only at h
    peel h as s1, -
    peel h as v1, -
    peel h as i1, -
    peel h as v2, -
    peel h as s2, -
    peel h as v3, -
    peel h as line, -
    peel h as u1, -
    obtain ⟨o', lst1, hx, hR, hrel1, hinv1⟩ := closure_order_refines (st := st) (lst := lst) (pk := pk) (pers := pers)
      (sp_dirs := sp_dirs) (roots := roots) hfs hrel hinv _ _ hq
    obtain ⟨b, lst2, hb, hR2, hrel2, hinv2⟩ := load_all_refines hR hfs hrel1 hinv1 a s' h
    refine ⟨b, lst2, ?_, hR2, hrel2, hinv2⟩
    show ((closureOrder fs (absPins pk) (absSearchPath sp_dirs) (absNIdxArr roots)) >>= _).run lst = _
    rw [am_bind_ok hx]
    exact hb

end walk

end ConRon.Refine2.Frontend.Olean
