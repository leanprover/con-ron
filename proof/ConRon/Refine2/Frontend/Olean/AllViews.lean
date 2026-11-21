/-
# `ConRon.Refine2.Frontend.Olean.AllViews` — `view::parse_all_views` against `parseAllViews`

**Task #166, Theorem 2.**  A module's three views, each object read once: `parse_many`
(`fast.rs`: the name tables, the skeletons, the roots, both passes, the values read back out of
the memo) and `parse_at` against the twin's `parseMany`, `parseAt`; `parse_view` against
`parseView`; `parse_all_views` against `parseAllViews`, the views related by `AllViewsRel`.
`mod_decoded_dup` is the identity.
-/
import ConRon.Refine2.Frontend.Olean.View
import ConRon.Refine2.Frontend.Olean.Stmts
import ConRon.Refine2.Frontend.ExportC

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_loc region_single part_module_data_addr region_of_parts2
  region_of_parts3)
open frontend.olean.fast (consts_skel consts_skel_loop many_skels many_skels_loop many_read
  many_read_loop mod_skel_read mod_skel_imports mod_skel_imports_loop mod_skel_constants
  mod_skel_constants_loop all_const_names_ok all_const_names_ok_loop many_roots many_roots_loop0
  many_roots_loop0_loop0 many_roots_loop1 many_roots_loop1_loop0 parse_many parse_at
  take_decoded run_passes c_entry_names c_entry_exprs)
open frontend.olean.spec (const_skel module_skel skel_fits import_map c_entry_map names_map
  const_names_ok)
open frontend.olean.view (mod_files_is_module rules_dup rules_dup_loop c_kind_dup c_entry_dup
  mod_decoded_dup mod_decoded_dup_loop0 mod_decoded_dup_loop1 loc_is_some loc_in_two
  check_imports_pre parse_view parse_all_views parse_all_views_module)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (constsSkel manySkels skelFits entryMap allConstNamesOk parseMany
  parseAt runPasses constNamesOk checkImportsPre parseView parseAllViews parseAllViewsModule
  importsPre)
open ConLeche.Frontend.Olean (CKindF CEntryF ImportF ModSkel constSkel moduleSkel ModFiles OLeanLevel)
open ConLeche.Frontend.Olean.Region (ofParts single)
open ConRon.Refine.HashMap (uscalar_add_eq uscalar_div_eq)

/-! ## Two reads in sequence -/

/-- **The bind of two reads**: the first's `Ok` feeds the second, its failures are the
answer, and the twin's `match ← x with | none => pure none | some b => g b`. -/
theorem RS.bind {α₁ β₁ α β : Type} {pers : arena.store.PersTier} {R₁ : α₁ → β₁ → Prop}
    {R : α → β → Prop} {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result α₁ frontend.olean.spec.RdErr × arena.store.EStore)}
    {k : core.result.Result α₁ frontend.olean.spec.RdErr × arena.store.EStore →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {x : AM (Option β₁)} {g : β₁ → AM (Option β)}
    (hf : RS pers R₁ st lst f x)
    (he : ∀ e s1, k (.Err e, s1) = ok (.Err e, s1))
    (hk : ∀ a b s1 lst1, R₁ a b → RS pers R (withStore st s1) lst1 (k (.Ok a, s1)) (g b)) :
    RS pers R st lst (Std.bind f k)
      (do match ← x with
          | Option.none => pure Option.none
          | Option.some b => g b) := by
  intro hrel hinv o s' hm
  obtain ⟨⟨r, s1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf hrel hinv r s1 hf1
  cases r with
  | Ok a =>
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := h1
    rw [am_bind_ok hx]
    exact hk a b s1 lst1 hR hrel1 hinv1 o s' hk1
  | Err e =>
    rw [he e s1] at hk1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hk1)
    cases e with
    | Bad =>
      obtain ⟨lst1, hx, hrel1, hinv1⟩ := h1
      rw [am_bind_ok hx]
      exact ⟨lst1, rfl, hrel1, hinv1⟩
    | Err e =>
      intro k' hk'
      obtain ⟨le, hle, hkk⟩ := h1 k' hk'
      refine ⟨le, ?_, hkk⟩
      rw [StateT.run_bind, hle]; rfl

/-- The tail of a read: the twin's run moved along an equation. -/
theorem RS.of_eq {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState}
    {m : Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {x y : AM (Option β)} (h : RS pers R st lst m x) (hxy : y = x) : RS pers R st lst m y := by
  rw [hxy]; exact h


/-! ## A module's value -/

/-- **`spec::ModDecoded` against the twin's.** -/
structure ModDecodedRel (d : frontend.olean.spec.ModDecoded)
    (d' : ConRon.Arena.Frontend.Olean.ModDecoded) : Prop where
  isModule : d.is_module = d'.isModule
  imports : d.imports.val.map (absImportF absNIdx) = d'.imports.toList
  constants : List.Forall₂ (EntryRel absNIdx absEIdx ValRel) d.constants.val d'.constants.toList

/-! ## The roots -/

/-- **`many_roots`' first loop: the imports' names.** -/
theorem many_roots_loop0_val {sks names o} (h : many_roots_loop0 sks names 0#usize = ok o) :
    o.val = names.val ++ sks.val.flatMap fun m => m.imports.val.map (·.module) := by
  refine append_loop0 (src := sks.val) (Ab := fun s : alloc.vec.Vec Std.U64 => s.val)
    (loop := many_roots_loop0 sks) (fun s i o h => ?_) h
  rw [many_roots_loop0] at h
  by_cases hi : i < alloc.vec.Vec.len sks
  · right
    rw [ite_eq_left hi] at h
    peel h as s1, hs1
    peel h as i1, hi1
    have hin : sks.val[i.val]? = some (sks.val[i.val]'(by scalar_tac)) := List.getElem?_eq_getElem _
    refine ⟨_, s1, i1, hin, ?_, uscalar_add_eq hi1, h⟩
    have := append_loop (src := (sks.val[i.val]'(by scalar_tac)).imports.val)
      (Ab := fun s : alloc.vec.Vec Std.U64 => s.val) (f := fun x => [x.module])
      (loop := fun s j => many_roots_loop0_loop0 sks s i j) ?_ _ (Nat.le_refl _) hs1
    · simpa [flatMap_single] using this
    · intro s j o h
      rw [many_roots_loop0_loop0] at h
      peel h as m, hm
      obtain ⟨_, rfl⟩ := vec_index_eq hm
      by_cases hj : j < alloc.vec.Vec.len (sks.val[i.val]'(by scalar_tac)).imports
      · right
        rw [ite_eq_left hj] at h
        peel h as x, hx
        peel h as s2, hs2
        peel h as j1, hj1
        exact ⟨x, s2, j1, ConRon.Refine.ExprOps.vec_index_getElem? hx, ConRon.Refine.vec_push_val hs2,
          uscalar_add_eq hj1, h⟩
      · left
        rw [ite_eq_right hj] at h
        exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩
  · left
    rw [ite_eq_right hi] at h
    exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩

/-- `many_roots_loop1_loop0`'s turn. -/
theorem roots_inner_step {skels a} {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    (hv : skels.val[a.val]? = some v) {Ab : (alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64) → List Std.U64}
    {f : frontend.olean.spec.CEntryF Std.U64 Std.U64 → List Std.U64}
    (hf : ∀ {c n e n1 e1}, c_entry_names c n = ok n1 → c_entry_exprs c e = ok e1 → Ab (n1, e1) = Ab (n, e) ++ f c) :
    ∀ s i o, many_roots_loop1_loop0 skels s.1 s.2 a i = ok o → (v.val.length ≤ i.val ∧ o = s) ∨
      ∃ x s1 i1, v.val[i.val]? = some x ∧ Ab s1 = Ab s ++ f x ∧ i1.val = i.val + 1 ∧
        many_roots_loop1_loop0 skels s1.1 s1.2 a i1 = ok o := by
  intro s i o h
  rw [many_roots_loop1_loop0] at h
  peel h as w, hw
  have hw2 := ConRon.Refine.ExprOps.vec_index_getElem? hw
  rw [hv] at hw2
  cases Option.some.inj hw2
  by_cases hi : i < alloc.vec.Vec.len v
  · right
    rw [ite_eq_left hi] at h
    peel h as c, hc
    peel h as n1, hn1
    peel h as c1, hc1
    peel h as e1, he1
    peel h as i1, hi1
    have e := ConRon.Refine.ExprOps.vec_index_getElem? hc
    have e2 := ConRon.Refine.ExprOps.vec_index_getElem? hc1
    rw [e] at e2
    cases Option.some.inj e2
    exact ⟨c, (n1, e1), i1, e, hf hn1 he1, uscalar_add_eq hi1, h⟩
  · left
    rw [ite_eq_right hi] at h
    exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩

/-- `many_roots_loop1`'s turn. -/
theorem roots_outer_step {skels : alloc.vec.Vec (alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64))}
    {Ab : (alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64) → List Std.U64}
    {f : frontend.olean.spec.CEntryF Std.U64 Std.U64 → List Std.U64}
    (hf : ∀ {c n e n1 e1}, c_entry_names c n = ok n1 → c_entry_exprs c e = ok e1 → Ab (n1, e1) = Ab (n, e) ++ f c) :
    ∀ s i o, many_roots_loop1 skels s.1 s.2 i = ok o → (skels.val.length ≤ i.val ∧ o = s) ∨
      ∃ x s1 i1, skels.val[i.val]? = some x ∧ Ab s1 = Ab s ++ x.val.flatMap f ∧ i1.val = i.val + 1 ∧
        many_roots_loop1 skels s1.1 s1.2 i1 = ok o := by
  intro s i o h
  rw [many_roots_loop1] at h
  by_cases hi : i < alloc.vec.Vec.len skels
  · right
    rw [ite_eq_left hi] at h
    peel h as q, hq
    obtain ⟨n1, e1⟩ := q
    peel h as i1, hi1
    have hlt : i.val < skels.val.length := by scalar_tac
    have hx : skels.val[i.val]? = some (skels.val[i.val]'hlt) := List.getElem?_eq_getElem hlt
    refine ⟨_, (n1, e1), i1, hx, ?_, uscalar_add_eq hi1, h⟩
    exact append_loop0 (src := (skels.val[i.val]'hlt).val) (Ab := Ab) (f := f)
      (loop := fun s j => many_roots_loop1_loop0 skels s.1 s.2 i j) (roots_inner_step hx hf) hq
  · left
    rw [ite_eq_right hi] at h
    exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩

/-- **`many_roots` collects the imports' names and the skeletons' pointers.** -/
theorem many_roots_val {sks skels n e} (h : many_roots sks skels = ok (n, e)) :
    n.val = (sks.val.flatMap fun m => m.imports.val.map (·.module)) ++
        skels.val.flatMap (fun v => v.val.flatMap namesL) ∧
      e.val = skels.val.flatMap (fun v => v.val.flatMap exprsL) := by
  rw [many_roots] at h
  peel h as n0, hn0
  have e0 := many_roots_loop0_val hn0
  have hnew : (alloc.vec.Vec.new Std.U64).val = [] := Slice.from_val _ _
  rw [hnew, List.nil_append] at e0
  have en := append_loop0 (src := skels.val)
    (Ab := fun s : alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64 => s.1.val)
    (f := fun v => v.val.flatMap namesL)
    (loop := fun s i => many_roots_loop1 skels s.1 s.2 i)
    (s := (n0, alloc.vec.Vec.new Std.U64))
    (roots_outer_step (fun h1 _ => c_entry_names_val h1)) h
  have ee := append_loop0 (src := skels.val)
    (Ab := fun s : alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64 => s.2.val)
    (f := fun v => v.val.flatMap exprsL)
    (loop := fun s i => many_roots_loop1 skels s.1 s.2 i)
    (s := (n0, alloc.vec.Vec.new Std.U64))
    (roots_outer_step (fun _ h2 => c_entry_exprs_val h2)) h
  refine ⟨?_, ?_⟩
  · simpa [e0] using en
  · simpa [hnew] using ee


/-- A read that takes no store, then one that does. -/
theorem RS.ps_bind {α β α' β' : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {R' : α' → β' → Prop} {st : arena.monad.AState} {lst : AState}
    {m : Result (core.result.Result α frontend.olean.spec.RdErr)} {x : AM (Option β)}
    {K : core.result.Result α frontend.olean.spec.RdErr →
      Result (core.result.Result α' frontend.olean.spec.RdErr × arena.store.EStore)}
    {g : Option β → AM (Option β')}
    (hp : PS R m x) (he : ∀ e, K (.Err e) = ok (.Err e, st.store)) (h0 : g Option.none = pure Option.none)
    (hk : ∀ a b, R a b → RS pers R' st lst (K (.Ok a)) (g (Option.some b))) :
    RS pers R' st lst (Std.bind m K) (x >>= g) := by
  intro hrel hinv o s' hm
  obtain ⟨r, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hP := hp r h1 lst
  cases r with
  | Ok a =>
    obtain ⟨b, hx, hR⟩ := hP
    rw [am_bind_ok hx]
    exact hk a b hR hrel hinv o s' h2
  | Err e =>
    rw [he e] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h2)
    cases e with
    | Bad =>
      rw [am_bind_ok hP, h0]
      exact ⟨lst, rfl, hrel, hinv⟩
    | Err e =>
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind hP _

/-- A module's skeleton and those of its constants, against the twin's list of pairs. -/
structure MsRel (p : alloc.vec.Vec frontend.olean.spec.ModSkel ×
    alloc.vec.Vec (alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)))
    (ms : List (ModSkel × List (CEntryF UInt64 UInt64))) : Prop where
  sks : List.Forall₂ ModSkelRel p.1.val (ms.map (·.1))
  skels : List.Forall₂ (fun v l => List.Forall₂ EV v.val l) p.2.val (ms.map (·.2))

/-- `many_skels`' loop, with what it has so far. -/
theorem many_skels_loop_ps {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {addrs : alloc.vec.Vec Std.U64} (hr : RegionFits bs r) :
    ∀ (k : Nat) {i : Std.Usize} {sks skels} {pre : List (ModSkel × List (CEntryF UInt64 UInt64))} {o}
      (lst : AState), addrs.val.length - i.val ≤ k → MsRel (sks, skels) pre →
      many_skels_loop bs r addrs sks skels i = ok o →
      PSOut (fun p l => MsRel p (pre ++ l)) lst o
        ((manySkels (absRegion bs r) ((addrs.val.drop i.val).map absWord)).run lst) := by
  intro k
  induction k with
  | zero =>
    intro i sks skels pre o lst hk hpre h
    rw [many_skels_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]
    exact ⟨[], rfl, by simpa using hpre⟩
  | succ k ih =>
    intro i sks skels pre o lst hk hpre h
    rw [many_skels_loop] at h
    by_cases hi : i < alloc.vec.Vec.len addrs
    · rw [ite_eq_left hi] at h
      have hlt : i.val < addrs.val.length := by scalar_tac
      peel h as a, ha
      obtain ⟨_, hae⟩ := vec_index_eq ha
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, ← hae, manySkels]
      peel h as o1, ho1
      refine sat_elim (module_skel_eq hr ho1) (fun hA hy => ?_) (fun sk sk' hA hy hS => ?_)
      · subst hA
        rw [hy]
        cases Result.ok_injective h
        rfl
      subst hA
      rw [hy]
      dsimp only at h ⊢
      peel h as r1, hr1
      have hF := consts_skel_ps (bs := bs) (r := r) hS.consts r1 hr1 lst
      cases r1 with
      | Ok cs =>
        obtain ⟨cl, hx, hR⟩ := hF
        rw [am_bind_ok hx]
        peel h as sks1, hs1
        peel h as skels1, hs2
        peel h as i3, hi3
        have hiv : i3.val = i.val + 1 := uscalar_add_eq hi3
        have hin : MsRel (sks1, skels1) (pre ++ [(sk', cl)]) := by
          refine ⟨?_, ?_⟩
          · show List.Forall₂ _ sks1.val _
            rw [ConRon.Refine.vec_push_val hs1, List.map_append]
            exact List.rel_append hpre.sks (List.Forall₂.cons hS List.Forall₂.nil)
          · show List.Forall₂ _ skels1.val _
            rw [ConRon.Refine.vec_push_val hs2, List.map_append]
            exact List.rel_append hpre.skels (List.Forall₂.cons hR List.Forall₂.nil)
        have hrest := ih (i := i3) lst (by omega) hin (show many_skels_loop bs r addrs sks1 skels1 i3 = ok o from h)
        rw [hiv] at hrest
        dsimp only
        cases o with
        | Ok a =>
          obtain ⟨l, hx2, hR2⟩ := hrest
          rw [am_bind_ok hx2]
          exact ⟨_, rfl, by simpa using hR2⟩
        | Err e =>
          cases e with
          | Bad =>
            rw [am_bind_ok hrest]
            rfl
          | Err e =>
            show AErrSim e _
            rw [StateT.run_bind]
            exact AErrSim.bind hrest _
      | Err e =>
        cases Result.ok_injective h
        cases e with
        | Bad =>
          rw [am_bind_ok hF]
          rfl
        | Err e =>
          show AErrSim e _
          rw [StateT.run_bind]
          exact AErrSim.bind hF _
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      exact ⟨[], rfl, by simpa using hpre⟩

/-- **`many_skels` is `manySkels`.** -/
theorem many_skels_ps {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {addrs : alloc.vec.Vec Std.U64} (hr : RegionFits bs r) :
    PS MsRel (many_skels bs r addrs) (manySkels (absRegion bs r) (addrs.val.map absWord)) := by
  intro o h lst
  rw [many_skels] at h
  have := many_skels_loop_ps hr (pre := []) _ lst (Nat.le_refl _)
    (by exact ⟨List.Forall₂.nil, List.Forall₂.nil⟩) h
  simpa using this

/-! ## The roots, on the twin's lists -/

theorem flat_inner {F : frontend.olean.spec.CEntryF Std.U64 Std.U64 → List Std.U64}
    {G : CEntryF UInt64 UInt64 → List UInt64}
    (hFG : ∀ {c c'}, EV c c' → (F c).map absWord = G c')
    {l0 : List (frontend.olean.spec.CEntryF Std.U64 Std.U64)} {l : List (CEntryF UInt64 UInt64)}
    (h : List.Forall₂ EV l0 l) : (l0.flatMap F).map absWord = l.flatMap G := by
  induction h with
  | nil => rfl
  | cons h1 _ ih2 => simp only [List.flatMap_cons, List.map_append, ih2, hFG h1]

theorem flat_abs {F : frontend.olean.spec.CEntryF Std.U64 Std.U64 → List Std.U64}
    {G : CEntryF UInt64 UInt64 → List UInt64}
    (hFG : ∀ {c c'}, EV c c' → (F c).map absWord = G c')
    {skels : List (alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64))}
    {L : List (List (CEntryF UInt64 UInt64))}
    (h : List.Forall₂ (fun v l => List.Forall₂ EV v.val l) skels L) :
    (skels.flatMap fun v => v.val.flatMap F).map absWord = L.flatten.flatMap G := by
  induction h with
  | nil => rfl
  | @cons v l _ _ h0 _ ih =>
    simp only [List.flatMap_cons, List.map_append, List.flatten_cons, List.flatMap_append, ih,
      flat_inner hFG h0]

theorem imports_abs {sks : List frontend.olean.spec.ModSkel} {L : List ModSkel}
    (h : List.Forall₂ ModSkelRel sks L) :
    (sks.flatMap fun m => m.imports.val.map (·.module)).map absWord =
      L.flatMap fun sk => sk.imports.map (·.module) := by
  induction h with
  | nil => rfl
  | @cons m m' _ _ h0 _ ih =>
    simp only [List.flatMap_cons, List.map_append, ih, ← h0.imports, List.map_map]
    rfl

/-- **`many_roots` is `parseMany`'s roots.** -/
theorem many_roots_abs {p ms n e} (hm : MsRel p ms) (h : many_roots p.1 p.2 = ok (n, e)) :
    n.val.map absWord = (ms.map (·.1)).flatMap (fun sk => sk.imports.map (·.module)) ++
        (ms.map (·.2)).flatten.flatMap CEntryF.names ∧
      e.val.map absWord = (ms.map (·.2)).flatten.flatMap CEntryF.exprs := by
  obtain ⟨hn, he⟩ := many_roots_val h
  refine ⟨?_, ?_⟩
  · rw [hn, List.map_append, imports_abs hm.sks, flat_abs namesL_abs hm.skels]
  · rw [he, flat_abs exprsL_abs hm.skels]

/-! ## A module's value from its skeletons -/

/-- **`mod_skel_imports` is `sk.imports.mapM`.** -/
theorem mod_skel_imports_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {sk : frontend.olean.spec.ModSkel} {l : List (ImportF UInt64)}
    (hl : sk.imports.val.map (absImportF absWord) = l) (st lst) :
    RS pers (fun v l' => List.Forall₂ (EqA (absImportF absNIdx)) v.val l') st lst
      (mod_skel_imports inst rd pk pers st.store bs r sk)
      (l.mapM (m := OptionT AM) fun i => ImportF.mapM (m := OptionT AM) (fun v => OptionT.mk (t.rdName v)) i) := by
  subst hl
  rw [mod_skel_imports]
  refine RS.vec_map (R := EqA (absImportF absNIdx))
    (loop := fun ar out i => mod_skel_imports_loop inst rd pk pers ar bs r sk.imports out i)
    (forall₂_of_map (A := absImportF absWord) sk.imports.val) ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show mod_skel_imports_loop inst rd pk pers ar bs r sk.imports out i = _
    rw [mod_skel_imports_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    cases hS
    show RS _ _ _ _ (mod_skel_imports_loop inst rd pk pers st.store bs r sk.imports out i) _
    rw [mod_skel_imports_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    refine RS.bindT (import_map_refines hp st lst) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-- **`mod_skel_constants` is `cs.mapM`.** -/
theorem mod_skel_constants_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {cs : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)} {l : List (CEntryF UInt64 UInt64)}
    (hl : List.Forall₂ EV cs.val l) (st lst) :
    RS pers (fun v l' => List.Forall₂ (EntryRel absNIdx absEIdx ValRel) v.val l') st lst
      (mod_skel_constants inst rd pk pers st.store bs r cs)
      (l.mapM (m := OptionT AM) fun c => OptionT.mk (entryMap t c)) := by
  rw [mod_skel_constants]
  refine RS.vec_map (R := EntryRel absNIdx absEIdx ValRel)
    (loop := fun ar out i => mod_skel_constants_loop inst rd pk pers ar bs r cs out i)
    hl ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show mod_skel_constants_loop inst rd pk pers ar bs r cs out i = _
    rw [mod_skel_constants_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    show RS _ _ _ _ (mod_skel_constants_loop inst rd pk pers st.store bs r cs out i) _
    rw [mod_skel_constants_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    refine RS.bindT (c_entry_map_refines hp hS st lst) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-- **`mod_skel_read` is `ModSkel.read`.** -/
theorem mod_skel_read_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {sk : frontend.olean.spec.ModSkel} {sk' : ModSkel} (hs : ModSkelRel sk sk')
    {cs : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)} {l : List (CEntryF UInt64 UInt64)}
    (hl : List.Forall₂ EV cs.val l) (st lst) :
    RS pers ModDecodedRel st lst (mod_skel_read inst rd pk pers st.store bs r sk cs)
      (Arena.Frontend.Olean.ModSkel.read t sk' l) := by
  rw [mod_skel_read]
  show RS _ _ _ _ _ (_ >>= _ : OptionT AM _)
  refine RS.bindT (mod_skel_imports_refines hp hs.imports st lst) (fun _ _ => by rfl)
    fun a b s1 lst1 hR => ?_
  show RS _ _ _ _ _ (_ >>= _ : OptionT AM _)
  refine RS.bindT (mod_skel_constants_refines hp hl (withStore st s1) lst1) (fun _ _ => by rfl)
    fun a2 b2 s2 lst2 hR2 => ?_
  refine RS.some ⟨hs.isModule, ?_, ?_⟩
  · simpa using forall₂_eqA hR
  · simpa using hR2

/-- The pairs of `MsRel`, as `many_read` walks them. -/
theorem ms_zip {sks : List frontend.olean.spec.ModSkel}
    {skels : List (alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64))} :
    ∀ {ms : List (ModSkel × List (CEntryF UInt64 UInt64))},
      List.Forall₂ ModSkelRel sks (ms.map (·.1)) →
      List.Forall₂ (fun v l => List.Forall₂ EV v.val l) skels (ms.map (·.2)) →
      List.Forall₂ (fun x x' => ModSkelRel x.1 x'.1 ∧ List.Forall₂ EV x.2.val x'.2) (sks.zip skels) ms := by
  induction sks generalizing skels with
  | nil =>
    intro ms h1 _
    cases ms with
    | nil => exact List.Forall₂.nil
    | cons _ _ => cases h1
  | cons a t ih =>
    intro ms h1 h2
    cases ms with
    | nil => cases h1
    | cons q ms' =>
      cases h1 with
      | cons ha ht =>
        cases h2 with
        | cons hb hs => exact List.Forall₂.cons ⟨ha, hb⟩ (ih ht hs)

/-- **`many_read` is `parseMany`'s last step.** -/
theorem many_read_refines {pk bs r pers} {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r)
    (hd : DSRel d t) {p ms} (hm : MsRel p ms) (st lst) :
    RS pers (fun v l => List.Forall₂ ModDecodedRel v.val l) st lst
      (many_read d pk pers st.store bs r p.1 p.2)
      (ms.mapM (m := OptionT AM) fun q => OptionT.mk
        (Arena.Frontend.Olean.ModSkel.read (ConRon.Arena.Frontend.Olean.DS.read (absPins pk) (absRegion bs r) t) q.1 q.2)) := by
  have hp := ds_ptr_rel (pk := pk) (pers := pers) hr hd
  have hl1 : p.1.val.length = ms.length := by simpa using hm.sks.length_eq
  rw [many_read]
  refine RS.vec_map (R := ModDecodedRel) (src := p.1.val.zip p.2.val)
    (loop := fun ar out i => many_read_loop d pk pers ar bs r p.1 p.2 out i)
    (ms_zip hm.sks hm.skels) ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    have hl2 : p.2.val.length = ms.length := by simpa using hm.skels.length_eq
    show many_read_loop d pk pers ar bs r p.1 p.2 out i = _
    have : p.1.val.length ≤ i.val := by
      rw [List.length_zip] at hi
      omega
    rw [many_read_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    obtain ⟨hx1, hx2⟩ := List.getElem?_zip_eq_some.mp hx
    show RS _ _ _ _ (many_read_loop d pk pers st.store bs r p.1 p.2 out i) _
    rw [many_read_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx1).1; scalar_tac)]
    refine RS.pure_step fun y hy => RS.pure_step fun y2 hy2 => ?_
    have e1 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    have e2 := ConRon.Refine.ExprOps.vec_index_getElem? hy2
    rw [hx1] at e1
    rw [hx2] at e2
    cases Option.some.inj e1
    cases Option.some.inj e2
    refine RS.bindT (mod_skel_read_refines hp hS.1 hS.2 st lst) (fun _ _ => by rfl)
      fun a b s1 lst1 hR => RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-! ## The name tables -/

/-- `all_const_names_ok`'s loop. -/
theorem all_const_names_ok_loop_cs {pk bs r pers} {addrs : alloc.vec.Vec Std.U64}
    (hr : RegionFits bs r) :
    ∀ (k : Nat) {i : Std.Usize} {st lst}, addrs.val.length - i.val ≤ k →
      CS pers (· = ·) st lst (all_const_names_ok_loop pk pers st.store bs r addrs i)
        (allConstNamesOk (absPins pk) (absRegion bs r) ((addrs.val.drop i.val).map absWord)) := by
  intro k
  induction k with
  | zero =>
    intro i st lst hk
    rw [all_const_names_ok_loop, ite_eq_right (by scalar_tac), List.drop_eq_nil_of_le (by omega)]
    exact CS.pure rfl
  | succ k ih =>
    intro i st lst hk
    rw [all_const_names_ok_loop]
    by_cases hi : i < alloc.vec.Vec.len addrs
    · rw [ite_eq_left hi]
      have hlt : i.val < addrs.val.length := by scalar_tac
      refine CS.pure_step fun a ha => ?_
      obtain ⟨_, hae⟩ := vec_index_eq ha
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, ← hae, allConstNamesOk]
      intro hrel hinv o s' hm
      obtain ⟨⟨r1, ar1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
      have hF := const_names_ok_refines (pk := pk) (root := a) hr hrel hinv r1 ar1 h1
      cases r1 with
      | Err e =>
        cases Result.ok_injective h2
        show AErrSim e _
        rw [StateT.run_bind]
        exact AErrSim.bind hF _
      | Ok b =>
        obtain ⟨b', lst1, hx, hb, h3, h4⟩ := hF
        cases hb
        rw [am_bind_ok hx]
        cases b with
        | false =>
          cases Result.ok_injective h2
          exact ⟨false, lst1, rfl, rfl, h3, h4⟩
        | true =>
          simp only [↓reduceIte] at h2 ⊢
          peel h2 as i3, hi3
          have hiv : i3.val = i.val + 1 := uscalar_add_eq hi3
          rw [← hiv]
          exact ih (st := withStore st ar1) (by omega) h3 h4 o s' h2
    · rw [ite_eq_right hi, List.drop_eq_nil_of_le (by scalar_tac)]
      exact CS.pure rfl

/-- A check in `CS`, then a read that goes on with its answer. -/
theorem RS.cs_bool {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result Bool kernel.core_types.CheckError × arena.store.EStore)}
    {x : AM Bool} {g : Bool → AM (Option β)}
    {K : core.result.Result Bool kernel.core_types.CheckError × arena.store.EStore →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    (hf : CS pers (· = ·) st lst f x)
    (he : ∀ e s1, K (.Err e, s1) = ok (.Err (.Err e), s1))
    (hk : ∀ b s1 lst1, RS pers R (withStore st s1) lst1 (K (.Ok b, s1)) (g b)) :
    RS pers R st lst (Std.bind f K) (x >>= g) := by
  intro hrel hinv o s' hm
  obtain ⟨⟨r1, ar1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hF := hf hrel hinv r1 ar1 h1
  cases r1 with
  | Ok b =>
    obtain ⟨b', lst1, hx, hb, h3, h4⟩ := hF
    cases hb
    rw [am_bind_ok hx]
    exact hk b ar1 lst1 h3 h4 o s' h2
  | Err e =>
    rw [he e ar1] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h2)
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind hF _

/-- **`all_const_names_ok` is `allConstNamesOk`.** -/
theorem all_const_names_ok_cs {pk bs r pers st lst} {addrs : alloc.vec.Vec Std.U64}
    (hr : RegionFits bs r) :
    CS pers (· = ·) st lst (all_const_names_ok pk pers st.store bs r addrs)
      (allConstNamesOk (absPins pk) (absRegion bs r) (addrs.val.map absWord)) := by
  rw [all_const_names_ok]
  simpa using all_const_names_ok_loop_cs (pk := pk) (pers := pers) (addrs := addrs) hr _
    (i := 0#usize) (st := st) (lst := lst) (Nat.le_refl _)

/-! ## `parse_many`, `parse_at` -/

/-- **`parse_many` is `parseMany`.** -/
theorem parse_many_refines {pk bs r pers st lst} {addrs : alloc.vec.Vec Std.U64}
    (hr : RegionFits bs r) :
    RS pers (fun v l => List.Forall₂ ModDecodedRel v.val l) st lst
      (parse_many pk pers st.store bs r addrs)
      (parseMany (absPins pk) (absRegion bs r) (addrs.val.map absWord)) := by
  rw [parse_many, parseMany]
  refine RS.cs_bool (all_const_names_ok_cs hr) (fun _ _ => rfl) fun b s1 lst1 => ?_
  cases b with
  | false => exact RS.none
  | true =>
    simp only [↓reduceIte, pure_bind]
    refine RS.ps_bind (many_skels_ps hr) (fun _ => rfl) rfl fun p ms hm => ?_
    obtain ⟨sks, skels⟩ := p
    dsimp only
    refine RS.pure_step fun q hq => ?_
    obtain ⟨n, e⟩ := q
    obtain ⟨hn, he⟩ := many_roots_abs hm hq
    rw [← hn, ← he]
    exact RS.bind_of (run_passes_refines hr) (fun _ _ => rfl) rfl
      fun d t s2 lst2 hd => many_read_refines hr hd hm _ _

/-- `take_decoded`: entry `i`. -/
theorem take_decoded_eq {ds : alloc.vec.Vec frontend.olean.spec.ModDecoded} {i : Std.Usize} {o}
    (h : take_decoded ds i = ok o) : ds.val[i.val]? = some o.1 := by
  rw [take_decoded] at h
  peel h as q, hq
  obtain ⟨y, f⟩ := q
  rw [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize] at hq
  simp only [bind_tc_eq, ConRon.Refine.bind_eq_ok_iff] at hq
  obtain ⟨z, hz, hq⟩ := hq
  have hyz : z = y := congrArg Prod.fst (Result.ok_injective hq)
  subst hyz
  have e := ConRon.Refine.ExprOps.vec_index_getElem? (show alloc.vec.Vec.index
    (core.slice.index.SliceIndexUsizeSlice _) ds i = ok z by
      rw [alloc.vec.Vec.index_slice_index]; exact hz)
  cases Result.ok_injective h
  exact e

/-- **`parse_at` is `parseAt`.** -/
theorem parse_at_refines {pk bs r pers st lst} {addr : Std.U64} (hr : RegionFits bs r) :
    RS pers ModDecodedRel st lst (parse_at pk pers st.store bs r addr)
      (parseAt (absPins pk) (absRegion bs r) (absWord addr)) := by
  rw [parse_at, parseAt]
  refine RS.pure_step fun addrs ha => ?_
  have hv : addrs.val = [addr] := by
    rw [ConRon.Refine.vec_push_val ha]; rfl
  have hm := parse_many_refines (pk := pk) (pers := pers) (st := st) (lst := lst) (addrs := addrs) hr
  rw [hv] at hm
  refine RS.bind_of hm (fun _ _ => rfl) rfl fun ds l s1 lst1 hR => ?_
  by_cases hl : alloc.vec.Vec.len ds = 1#usize
  · have hl' : ds.val.length = 1 := by
      have := congrArg UScalar.val hl
      rw [alloc.vec.Vec.len_val] at this
      exact this
    show RS _ _ _ _ (if alloc.vec.Vec.len ds = 1#usize then _ else _) _
    rw [ite_eq_left hl]
    refine RS.pure_step fun q hq => ?_
    obtain ⟨md, ds1⟩ := q
    have he := take_decoded_eq hq
    obtain ⟨hlt, hmd⟩ := List.getElem?_eq_some_iff.mp he
    dsimp only at hmd
    cases hds : ds.val with
    | nil => rw [hds] at hl'; cases hl'
    | cons x t =>
      rw [hds] at hl' hR
      have ht : t = [] := List.eq_nil_of_length_eq_zero (by simpa using hl')
      subst ht
      cases hR with
      | cons hx hnil =>
        cases hnil
        have : md = x := by
          have e0 : (0#usize : Std.Usize).val = 0 := by decide
          simp only [e0] at hmd
          simpa [hds] using hmd.symm
        subst this
        exact RS.some hx
  · show RS _ _ _ _ (if alloc.vec.Vec.len ds = 1#usize then _ else _) _
    rw [ite_eq_right hl]
    have hne : l.length ≠ 1 := by
      rw [← hR.length_eq]
      intro he
      apply hl
      apply UScalar.eq_of_val_eq
      simp only [alloc.vec.Vec.len_val]
      exact he
    cases l with
    | nil => exact RS.none
    | cons x t =>
      cases t with
      | nil => exact absurd rfl hne
      | cons y u => exact RS.none


/-! ## The copies -/

/-- **`rules_dup` is the identity.** -/
theorem rules_dup_eq {r r' : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)}
    (h : rules_dup r = ok r') : r' = r := by
  rw [rules_dup] at h
  refine vec_ext (dup_walk0 (L := fun i out => rules_dup_loop r out i) ?_ h)
  intro i out o h
  rw [rules_dup_loop] at h
  by_cases hc : i < alloc.vec.Vec.len r
  · rw [ite_eq_left hc] at h
    peel h as ⟨n, u, e⟩, hx
    peel h as n1, hn1
    obtain rfl := nidx_dup2_ok hn1
    peel h as e1, he1
    obtain rfl := eidx_dup2_ok he1
    peel h as o1, ho1
    peel h as j, hj
    exact Or.inr ⟨_, o1, j, ConRon.Refine.ExprOps.vec_index_getElem? hx,
      ConRon.Refine.vec_push_val ho1, add_one_usize hj, h⟩
  · rw [ite_eq_right hc] at h
    exact Or.inl ⟨len_le_of_not_lt hc, (Result.ok_injective h).symm⟩

theorem nidx_vec_dup_eq {v v' : alloc.vec.Vec arena.handle.NIdx}
    (h : arena.env.nidx_vec_dup v = ok v') : v' = v :=
  vec_ext (ConRon.Refine2.nidx_vec_dup_val h)

theorem hints_dup_self {h r : frontend.scan_types.HintsRec}
    (e : frontend.olean.spec.hints_dup h = ok r) : r = h := by
  cases h <;> exact (Result.ok_injective e).symm

/-- **`c_kind_dup` is the identity.** -/
theorem c_kind_dup_eq {k k' : frontend.olean.spec.CKindF arena.handle.NIdx arena.handle.EIdx}
    (h : c_kind_dup k = ok k') : k' = k := by
  delta c_kind_dup at h
  cases k <;> dsimp only at h
  · exact (Result.ok_injective h).symm
  · peel h as e, he
    obtain rfl := eidx_dup2_ok he
    peel h as hr, hhr
    obtain rfl := hints_dup_self hhr
    peel h as v, hv
    cases Result.ok_injective h
    rw [ConRon.Refine.Expr.str_copy_eq hv]
  · peel h as e, he
    obtain rfl := eidx_dup2_ok he
    peel h as v, hv
    cases Result.ok_injective h
    rw [nidx_vec_dup_eq hv]
  · peel h as e, he
    obtain rfl := eidx_dup2_ok he
    cases Result.ok_injective h
    rfl
  · peel h as v, hv
    cases Result.ok_injective h
    rw [ConRon.Refine.Expr.str_copy_eq hv]
  · peel h as v, hv
    peel h as v1, hv1
    cases Result.ok_injective h
    rw [nidx_vec_dup_eq hv, nidx_vec_dup_eq hv1]
  · peel h as n, hn
    obtain rfl := nidx_dup2_ok hn
    cases Result.ok_injective h
    rfl
  · peel h as v, hv
    peel h as v1, hv1
    cases Result.ok_injective h
    rw [nidx_vec_dup_eq hv, rules_dup_eq hv1]

/-- **`c_entry_dup` is the identity.** -/
theorem c_entry_dup_eq {c c' : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    (h : c_entry_dup c = ok c') : c' = c := by
  rw [c_entry_dup] at h
  peel h as n, hn
  obtain rfl := nidx_dup2_ok hn
  peel h as v, hv
  peel h as e, he
  obtain rfl := eidx_dup2_ok he
  peel h as k, hk
  cases Result.ok_injective h
  rw [nidx_vec_dup_eq hv, c_kind_dup_eq hk]

/-- **`mod_decoded_dup` is the identity.** -/
theorem mod_decoded_dup_eq {d d' : frontend.olean.spec.ModDecoded}
    (h : mod_decoded_dup d = ok d') : d' = d := by
  rw [mod_decoded_dup] at h
  peel h as im, him
  peel h as cs, hcs
  cases Result.ok_injective h
  have e1 : im = d.imports := by
    refine vec_ext (dup_walk0 (L := fun i out => mod_decoded_dup_loop0 d.imports out i) ?_ him)
    intro i out o h
    rw [mod_decoded_dup_loop0] at h
    by_cases hc : i < alloc.vec.Vec.len d.imports
    · rw [ite_eq_left hc] at h
      peel h as x, hx
      peel h as n, hn
      obtain rfl := nidx_dup2_ok hn
      peel h as o1, ho1
      peel h as j, hj
      exact Or.inr ⟨x, o1, j, ConRon.Refine.ExprOps.vec_index_getElem? hx,
        ConRon.Refine.vec_push_val ho1, add_one_usize hj, h⟩
    · rw [ite_eq_right hc] at h
      exact Or.inl ⟨len_le_of_not_lt hc, (Result.ok_injective h).symm⟩
  have e2 : cs = d.constants := by
    refine vec_ext (dup_walk0 (L := fun i out => mod_decoded_dup_loop1 d.constants out i) ?_ hcs)
    intro i out o h
    rw [mod_decoded_dup_loop1] at h
    by_cases hc : i < alloc.vec.Vec.len d.constants
    · rw [ite_eq_left hc] at h
      peel h as x, hx
      peel h as c1, hc1
      obtain rfl := c_entry_dup_eq hc1
      peel h as o1, ho1
      peel h as j, hj
      exact Or.inr ⟨_, o1, j, ConRon.Refine.ExprOps.vec_index_getElem? hx,
        ConRon.Refine.vec_push_val ho1, add_one_usize hj, h⟩
    · rw [ite_eq_right hc] at h
      exact Or.inl ⟨len_le_of_not_lt hc, (Result.ok_injective h).symm⟩
  rw [e1, e2]


/-! ## The location tests -/

/-- `loc_is_some` is `(r.loc a).isSome`. -/
theorem loc_is_some_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {a : Std.U64} {b : Bool}
    (h : loc_is_some r a = ok b) : b = ((absRegion bs r).loc (absWord a)).isSome := by
  rw [loc_is_some] at h
  peel h as o, ho
  rw [← region_loc_eq bs ho]
  cases o <;> exact (Result.ok_injective h).symm

/-- `loc_in_two`: the location test in the region of two files. -/
theorem loc_in_two_eq {a b : frontend.olean.region.Part} {addr : Std.U64} {o : Bool}
    (ha : PartFits a) (hb : PartFits b) (h : loc_in_two a b addr = ok o) :
    o = match ofParts #[absPart a, absPart b] with
      | .error _ => false
      | .ok r2 => (r2.loc (absWord addr)).isSome := by
  rw [loc_in_two] at h
  peel h as r, hr
  have e := region_of_parts2_eq ha hb hr
  cases r with
  | Err _ =>
    obtain ⟨-, m, em⟩ := e
    rw [em]
    exact (Result.ok_injective h).symm
  | Ok b2 =>
    obtain ⟨em, -⟩ := e
    rw [em]
    exact loc_is_some_eq _ h

/-! ## A decoded view -/

/-- A stored constant, as the twin's. -/
abbrev ERel := EntryRel (N := arena.handle.NIdx) (E := arena.handle.EIdx) absNIdx absEIdx ValRel

/-- **`view::AllViews` against the twin's.** -/
structure AllViewsRel (v : frontend.olean.view.AllViews) (v' : Arena.Frontend.Olean.AllViews) :
    Prop where
  exported : ModDecodedRel v.exported v'.exported
  server : ModDecodedRel v.server v'.server
  «private» : ModDecodedRel v.private_part v'.private

/-! ## `parse_view`, `parse_all_views` -/

theorem dec_imports {d d'} (hd : ModDecodedRel d d') : d'.imports = absImports d.imports := by
  rw [absImports, hd.imports]

theorem am_pure_bind {α β : Type} (a : α) (g : α → AM β) : (pure a >>= g) = g a := rfl

theorem f2_get {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {i : Nat} {x : α} (hi : l[i]? = some x) :
    ∃ y, l'[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hab _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨_, rfl, hab⟩
    | succ i => simpa using ih (by simpa using hi)

theorem list3 {α : Type} {l : List α} {a b c : α} (h : l.length = 3) (h0 : l[0]? = some a)
    (h1 : l[1]? = some b) (h2 : l[2]? = some c) : l = [a, b, c] := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩ <;> simp_all

theorem len_bne_three {α : Type} {ds : alloc.vec.Vec α} (h : ds.val.length = 3) :
    ¬ (alloc.vec.Vec.len ds != 3#usize) = true := by
  simp only [bne_iff_ne]
  intro hn
  exact hn (UScalar.eq_of_val_eq (by simpa using h))

theorem len_bne_ne {α : Type} {ds : alloc.vec.Vec α} (h : ¬ ds.val.length = 3) :
    (alloc.vec.Vec.len ds != 3#usize) = true := by
  simp only [bne_iff_ne]
  intro he
  apply h
  have := congrArg (fun x : Std.Usize => x.val) he
  simpa using this

/-- `take_decoded`: the value at `i`, and the others stay. -/
theorem take_dec {ds i d ds'} (h : frontend.olean.fast.take_decoded ds i = ok (d, ds')) :
    ds.val[i.val]? = some d ∧ ∀ j, j ≠ i.val → ds'.val[j]? = ds.val[j]? := by
  rw [frontend.olean.fast.take_decoded] at h
  peel h as ⟨md, back⟩, hm
  have hb := ConRon.Refine2.Frontend.idt_index_mut_back hm
  rw [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize] at hm
  peel hm as y, hy
  simp only [Result.ok.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  cases Result.ok_injective h
  subst hb
  refine ⟨ConRon.Refine.ExprOps.vec_index_getElem? (by rw [alloc.vec.Vec.index_slice_index]; exact hy), ?_⟩
  intro j hj
  rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_ne (Ne.symm hj)]

/-- **`check_imports_pre` is `checkImportsPre`.** -/
theorem check_imports_pre_refines {pk pers st lst f f' d d'}
    (hf : ModFilesRel f f') (hd : ModDecodedRel d d') :
    RS pers ModDecodedRel st lst (check_imports_pre pk pers st.store f d) (checkImportsPre (absPins pk) f' d') := by
  rw [check_imports_pre, checkImportsPre, hf.exported]
  refine RS.of_eq (RS.bind (g := fun pre => if pre == d'.imports then pure (some d') else pure none)
    (imports_pre_ok hf st lst) (fun e s1 => by cases e <;> rfl) fun a b s1 lst1 hab => ?_) ?_
  · cases hab
    refine RS.pure_step fun c hc => ?_
    rw [dec_imports hd, ← imports_beq_eq hc]
    cases c with
    | true =>
      rw [ite_eq_left rfl]
      exact RS.some hd
    | false =>
      rw [ite_eq_right (by simp)]
      exact RS.none
  · congr 1
    funext o
    cases o <;> rfl

/-- **`parse_view` is `parseView`.** -/
theorem parse_view_refines {pk pers st lst f f' level}
    (hf : ModFilesRel f f') :
    RS pers ModDecodedRel st lst (parse_view pk pers st.store f level) (parseView (absPins pk) f' (absLevel level)) := by
  rw [parse_view, parseView]
  refine RS.pure_step fun o ho => ?_
  have hV := mod_files_view_region_eq hf ho
  cases o with
  | none =>
    rw [show f'.viewRegion (absLevel level) = none from hV]
    exact RS.none
  | some p =>
    obtain ⟨vb, a⟩ := p
    dsimp only
    refine RS.pure_step fun bs hb => RS.pure_step fun r hr => ?_
    obtain ⟨e, hfit⟩ := hV bs r hb hr
    rw [e]
    dsimp only
    refine RS.of_eq (RS.bind (g := fun d => checkImportsPre (absPins pk) f' d) (parse_at_refines hfit) ?_ ?_) ?_
    · intros; rfl
    · intro _ _ _ _ hab
      exact check_imports_pre_refines hf hab
    · congr 1
      funext o
      cases o <;> rfl

/-- **`parse_all_views_module` is `parseAllViewsModule`.** -/
theorem parse_all_views_module_refines {pk pers st lst f f' s p}
    (hf : ModFilesRel f f') (hs : f.server = some s) (hp : f.private_part = some p) :
    RS pers AllViewsRel st lst (parse_all_views_module pk pers st.store f s p)
      (parseAllViewsModule (absPins pk) f' (absPart s) (absPart p)) := by
  have fE := hf.fitsE
  have fS := hf.fitsS s hs
  have fP := hf.fitsP p hp
  rw [parse_all_views_module, parseAllViewsModule, hf.exported]
  refine RS.pure_step fun ae hae => RS.pure_step fun a_s has => RS.pure_step fun ap hap =>
    RS.pure_step fun r1 hr1 => RS.pure_step fun b hb => ?_
  obtain ⟨e1, -⟩ := region_single_eq fE hr1
  rw [loc_is_some_eq (alloc.vec.Vec.deref f.exported.bytes) hb, e1, part_module_data_addr_eq hae]
  rw [← part_module_data_addr_eq hae, ← part_module_data_addr_eq has, ← part_module_data_addr_eq hap]
  by_cases c1 : ((single (absPart f.exported)).loc (absWord ae)).isSome = true
  · rw [ite_eq_left c1, ite_eq_left c1]
    simp only [am_pure_bind]
    refine RS.pure_step fun b1 hb1 => ?_
    rw [loc_in_two_eq fE fS hb1]
    cases e2 : ofParts #[absPart f.exported, absPart s] with
    | error _ =>
      rw [ite_eq_right (by simp)]
      exact RS.none
    | ok r2 =>
      dsimp only
      by_cases c2 : (r2.loc (absWord a_s)).isSome = true
      · rw [ite_eq_left c2, ite_eq_left c2]
        refine RS.pure_step fun o3 ho3 => ?_
        have e3 := region_of_parts3_eq fE fS fP ho3
        cases o3 with
        | Err _ =>
          obtain ⟨-, _, em⟩ := e3
          rw [em]
          exact RS.none
        | Ok buf =>
          obtain ⟨em, hfit⟩ := e3
          rw [em]
          dsimp only
          intro hrel hinv o s' h
          peel h as a1, h1
          peel h as a2, h2
          peel h as a3, h3
          peel h as ⟨r2', ar1⟩, hmany
          have hS := parse_many_refines (addrs := a3) hfit hrel hinv r2' ar1 hmany
          have ha : a3.val.map absWord = [absWord ae, absWord a_s, absWord ap] := by
            rw [ConRon.Refine.vec_push_val h3, ConRon.Refine.vec_push_val h2, ConRon.Refine.vec_push_val h1]
            rfl
          rw [ha] at hS
          cases r2' with
          | Err ee =>
            cases Result.ok_injective h
            cases ee with
            | Bad =>
              obtain ⟨lst1, hx, hrel1, hinv1⟩ := hS
              rw [am_bind_ok hx]
              exact ⟨lst1, rfl, hrel1, hinv1⟩
            | Err e =>
              intro k' hk'
              obtain ⟨le, hle, hkk⟩ := hS k' hk'
              refine ⟨le, ?_, hkk⟩
              rw [StateT.run_bind, hle]
              rfl
          | Ok ds =>
            obtain ⟨l, lst1, hx, hl, hrel1, hinv1⟩ := hS
            rw [am_bind_ok hx]
            replace h : (if (alloc.vec.Vec.len ds != 3#usize) = true then _ else _) = ok (o, s') := h
            by_cases hlen : ds.val.length = 3
            · rw [ite_eq_right (len_bne_three hlen)] at h
              peel h as ⟨dp, ds1⟩, ht2
              peel h as ⟨d_s, ds2⟩, ht1
              peel h as ⟨de, _⟩, ht0
              obtain ⟨g2, k2⟩ := take_dec ht2
              obtain ⟨g1, k1⟩ := take_dec ht1
              obtain ⟨g0, -⟩ := take_dec ht0
              have g0' := g0
              rw [k1 _ (by decide), k2 _ (by decide)] at g0'
              have g1' := g1
              rw [k2 _ (by decide)] at g1'
              obtain ⟨y0, hy0, r0⟩ := f2_get hl g0'
              obtain ⟨y1, hy1, r1'⟩ := f2_get hl g1'
              obtain ⟨y2, hy2, r2'⟩ := f2_get hl g2
              have el := list3 (by rw [← hl.length_eq]; exact hlen) hy0 hy1 hy2
              subst el
              dsimp only
              peel h as ⟨r3, ar2⟩, himp
              have hS3 : RdOut pers (EqA absImports) (withStore st ar2) r3
                  ((importsPre (absPins pk) (absPart f.exported).bytes).run lst1) :=
                imports_pre_ok hf (withStore st ar1) lst1 hrel1 hinv1 r3 ar2 himp
              cases r3 with
              | Err ee =>
                cases Result.ok_injective h
                cases ee with
                | Bad =>
                  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := hS3
                  rw [am_bind_ok hx2]
                  exact ⟨lst2, rfl, hrel2, hinv2⟩
                | Err e =>
                  intro k' hk'
                  obtain ⟨le, hle, hkk⟩ := hS3 k' hk'
                  refine ⟨le, ?_, hkk⟩
                  rw [StateT.run_bind, hle]
                  rfl
              | Ok pre =>
                obtain ⟨_, lst2, hx2, rfl, hrel2, hinv2⟩ := hS3
                rw [am_bind_ok hx2]
                dsimp only
                replace h : (Std.bind (frontend.olean.spec.imports_beq _ de.imports) _) = ok (o, s') := h
                rw [dec_imports r0, dec_imports r1', dec_imports r2']
                peel h as b3, hb3
                rw [← imports_beq_eq hb3]
                cases b3 with
                | false =>
                  rw [ite_eq_right (by simp)] at h ⊢
                  cases Result.ok_injective h
                  exact ⟨lst2, rfl, hrel2, hinv2⟩
                | true =>
                  rw [ite_eq_left rfl] at h
                  peel h as b4, hb4
                  rw [← imports_beq_eq hb4]
                  cases b4 with
                  | false =>
                    rw [ite_eq_right (by simp)] at h ⊢
                    cases Result.ok_injective h
                    exact ⟨lst2, rfl, hrel2, hinv2⟩
                  | true =>
                    rw [ite_eq_left rfl] at h
                    peel h as b5, hb5
                    rw [← imports_beq_eq hb5]
                    cases b5 with
                    | false =>
                      rw [ite_eq_right (by simp)] at h ⊢
                      cases Result.ok_injective h
                      exact ⟨lst2, rfl, hrel2, hinv2⟩
                    | true =>
                      rw [ite_eq_left rfl] at h
                      rw [ite_eq_left (show (true && true && true) = true from rfl)]
                      cases Result.ok_injective h
                      exact ⟨_, lst2, rfl, ⟨r0, r1', r2'⟩, hrel2, hinv2⟩
            · rw [ite_eq_left (len_bne_ne hlen)] at h
              cases Result.ok_injective h
              have hne : l.length ≠ 3 := by rw [← hl.length_eq]; exact hlen
              have hn : ∀ a b c, l ≠ [a, b, c] := by
                rintro a b c rfl
                exact hne rfl
              refine ⟨lst1, ?_, hrel1, hinv1⟩
              revert hn hne
              rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> intro hne hn <;>
                first | exact absurd rfl (hn _ _ _) | rfl
      · rw [ite_eq_right c2, ite_eq_right c2]
        exact RS.none
  · rw [ite_eq_right c1, ite_eq_right c1]
    exact RS.none

/-- **`parse_all_views` is `parseAllViews`.** -/
theorem parse_all_views_refines {pk pers st lst f f'}
    (hf : ModFilesRel f f') :
    RS pers AllViewsRel st lst (parse_all_views pk pers st.store f) (parseAllViews (absPins pk) f') := by
  rw [parse_all_views, parseAllViews]
  refine RS.pure_step fun b hb => ?_
  rw [← mod_files_is_module_eq hf hb]
  cases b with
  | true =>
    rw [ite_eq_left rfl, ite_eq_left rfl, hf.server, hf.private]
    cases hs : f.server with
    | none => exact RS.none
    | some s =>
      cases hp : f.private_part with
      | none => exact RS.none
      | some p => exact parse_all_views_module_refines hf hs hp
  | false =>
    rw [ite_eq_right (by simp), ite_eq_right (by simp)]
    refine RS.of_eq (RS.bind (g := fun d => pure (some ⟨d, d, d⟩))
      (parse_view_refines (level := .Exported) hf) ?_ ?_) ?_
    · intros; rfl
    · intro d d' s1 lst1 hd
      refine RS.pure_step fun d2 hd2 => ?_
      obtain rfl := mod_decoded_dup_eq hd2
      exact RS.some ⟨hd, hd, hd⟩
    · congr 1
      funext o
      cases o <;> rfl

end ConRon.Refine2.Frontend.Olean
