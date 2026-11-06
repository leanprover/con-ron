/-
# `ConRon.Refine2.Frontend.Olean.FastMany` — the module reads of `olean/fast.rs`

**Task #142, Theorem 2.**  `parse_many`, `parse_at`, `stmts_fast`: the name tables checked,
the skeletons, both passes, and the values read back out of the memo.
-/
import ConRon.Refine2.Frontend.Olean.FastRoots

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_loc)
open frontend.olean.fast (consts_skel consts_skel_loop many_skels many_skels_loop many_read
  many_read_loop mod_skel_read mod_skel_imports mod_skel_imports_loop mod_skel_constants
  mod_skel_constants_loop all_const_names_ok all_const_names_ok_loop many_roots parse_many parse_at
  take_decoded stmts_read stmts_read_loop stmts_roots stmts_fast run_passes)
open frontend.olean.spec (const_skel module_skel skel_fits import_map c_entry_map names_map
  const_names_ok)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (constsSkel manySkels skelFits entryMap allConstNamesOk parseMany
  parseAt stmtsFast runPasses constNamesOk)
open ConLeche.Frontend.Olean (CKindF CEntryF ImportF ModSkel constSkel moduleSkel)
open ConRon.Refine.HashMap (uscalar_add_eq uscalar_div_eq)

/-! ## `PS`: a read that takes no store -/

/-- What a read that takes no store claims of a twin's run that leaves the state alone. -/
def POut {α β : Type} (R : α → β → Prop) (lst : AState)
    (o : core.result.Result α frontend.olean.spec.RdErr)
    (y : Except Arena.CheckError (Option β × AState)) : Prop :=
  match o with
  | .Ok a => ∃ b, y = .ok (some b, lst) ∧ R a b
  | .Err .Bad => y = .ok (none, lst)
  | .Err (.Err e) => AErrSim e y

/-- **The judgement of a read that takes no store.** -/
def PS {α β : Type} (R : α → β → Prop) (m : Result (core.result.Result α frontend.olean.spec.RdErr))
    (x : AM (Option β)) : Prop :=
  ∀ o, m = ok o → ∀ lst, POut R lst o (x.run lst)

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

/-- The answer of the rest of a list read, then this element in front of it. -/
theorem POut.cons {α β : Type} {R : α → β → Prop} {lst : AState} {pre : List β} {b : β}
    {o : core.result.Result (alloc.vec.Vec α) frontend.olean.spec.RdErr} {x : AM (Option (List β))}
    {g : Option (List β) → AM (Option (List β))}
    (h : POut (fun v l => List.Forall₂ R v.val ((pre ++ [b]) ++ l)) lst o (x.run lst))
    (h0 : g none = pure none) (hs : ∀ l, g (some l) = pure (some (b :: l))) :
    POut (fun v l => List.Forall₂ R v.val (pre ++ l)) lst o ((x >>= g).run lst) := by
  cases o with
  | Ok a =>
    obtain ⟨l, hx, hR⟩ := h
    rw [am_bind_ok hx, hs]
    exact ⟨b :: l, rfl, by simpa using hR⟩
  | Err e =>
    cases e with
    | Bad =>
      rw [am_bind_ok h, h0]
      rfl
    | Err e =>
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind h _

/-! ## The skeletons -/

/-- A skeleton whose numbers fit. -/
abbrev EV := EntryRel absWord absWord ValRel

/-- `consts_skel`'s loop, with what it has so far. -/
theorem consts_skel_loop_ps {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {consts : alloc.vec.Vec Std.U64} :
    ∀ (k : Nat) {i : Std.Usize} {out} {pre : List (CEntryF UInt64 UInt64)} {o} (lst : AState),
      consts.val.length - i.val ≤ k → List.Forall₂ EV out.val pre →
      consts_skel_loop bs r consts out i = ok o →
      POut (fun v l => List.Forall₂ EV v.val (pre ++ l)) lst o
        ((constsSkel (absRegion bs r) ((consts.val.drop i.val).map (·.val))).run lst) := by
  intro k
  induction k with
  | zero =>
    intro i out pre o lst hk hpre h
    rw [consts_skel_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]
    exact ⟨[], rfl, by simpa using hpre⟩
  | succ k ih =>
    intro i out pre o lst hk hpre h
    rw [consts_skel_loop] at h
    by_cases hi : i < alloc.vec.Vec.len consts
    · rw [ite_eq_left hi] at h
      have hlt : i.val < consts.val.length := by scalar_tac
      peel h as c, hc
      obtain ⟨_, hce⟩ := vec_index_eq hc
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, ← hce, constsSkel]
      peel h as o1, ho1
      refine sat_elim (const_skel_eq (bs := bs) (r := r) ho1) (fun hA hy => ?_) (fun sk sk' hA hy hS => ?_)
      · subst hA
        rw [hy]
        cases Result.ok_injective h
        rfl
      subst hA
      rw [hy]
      dsimp only at h ⊢
      peel h as r1, hr1
      have hF := skel_fits_refines hS hr1 (lst := lst)
      cases r1 with
      | Ok u =>
        obtain ⟨hrun, hEV⟩ := hF
        rw [am_bind_ok hrun]
        peel h as out1, ho
        peel h as i3, hi3
        have hiv : i3.val = i.val + 1 := uscalar_add_eq hi3
        rw [← hiv]
        exact POut.cons (ih (i := i3) lst (by omega) (pre := pre ++ [sk'])
          (by rw [ConRon.Refine.vec_push_val ho]; exact List.rel_append hpre (List.Forall₂.cons hEV List.Forall₂.nil)) h)
          rfl (fun _ => rfl)
      | Err e =>
        cases Result.ok_injective h
        cases e with
        | Bad => exact hF.elim
        | Err e =>
          show AErrSim e _
          rw [StateT.run_bind]
          exact AErrSim.bind hF _
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      exact ⟨[], rfl, by simpa using hpre⟩

/-- **`consts_skel` is `constsSkel`.** -/
theorem consts_skel_ps {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {consts : alloc.vec.Vec Std.U64} {l : List Nat} (hl : consts.val.map (·.val) = l) :
    PS (fun v l => List.Forall₂ EV v.val l) (consts_skel bs r consts) (constsSkel (absRegion bs r) l) := by
  subst hl
  intro o h lst
  rw [consts_skel] at h
  have := consts_skel_loop_ps (pre := []) _ lst (Nat.le_refl _) (by exact List.Forall₂.nil) h
  simpa using this

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
      POut (fun p l => MsRel p (pre ++ l)) lst o
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

/-! ## The memo as a pointer read -/

/-- A word of the memo at a location of the region, as the twin's. -/
theorem memo_word {β : Type} {A : Std.U32 → β} {v : alloc.vec.Vec Std.U32} {a : Array β}
    (h : v.val.map A = a.toList) {bs : Slice Std.U8} {c i : Std.U64} {x : Std.U32} {d : β}
    (hc : c.val + 8 ≤ bs.val.length) (hi : c / 8#u64 = ok i)
    (hx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32) v
      (UScalar.cast UScalarTy.Usize i) = ok x) :
    a.getD (c.val / 8) d = A x := by
  rw [← word_at h hi hx (d := d), tr_of_le]
  have := bytes_le_max bs
  omega

/-- **The memo as `PtrRead`.** -/
theorem ds_ptr_rel {pk bs r pers} {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r)
    (hd : DSRel d t) :
    PtrRel frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead d
      (ConRon.Arena.Frontend.Olean.DS.read (absPins pk) (absRegion bs r) t) pk bs r pers where
  nm st lst v := by
    show RS _ _ _ _ (frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead.rd_name d pk pers st.store bs r v)
      (pure (ConRon.Arena.Frontend.Olean.DS.nameOf (absPins pk) (absRegion bs r) t (absWord v)))
    rw [frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead.rd_name]
    simp only [ConRon.Arena.Frontend.Olean.DS.nameOf]
    by_cases hv : v = 1#u64
    · rw [ite_eq_left hv, ite_eq_left (word_eq_one.mpr hv)]
      refine RS.pure_step fun n hn => ?_
      rw [nidx_dup2_ok hn]
      exact RS.some rfl
    · rw [ite_eq_right hv, ite_eq_right (fun he => hv (word_eq_one.mp he))]
      refine RS.pure_step fun o ho => ?_
      rw [← region_loc_eq bs ho]
      cases o with
      | none => exact RS.none
      | some c =>
        simp only [lift, bind_ok]
        refine RS.pure_step fun i hi => RS.pure_step fun x hx => RS.pure_step fun n hn => ?_
        cases Result.ok_injective hn
        simp only [locOf, Option.map_some]
        rw [memo_word hd.names (region_loc_fits hr ho) hi hx]
        exact RS.some rfl
  ex st lst v := by
    show RS _ _ _ _ (frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead.rd_expr d pk pers st.store bs r v)
      (pure (ConRon.Arena.Frontend.Olean.DS.exprOf (absRegion bs r) t (absWord v)))
    rw [frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead.rd_expr]
    simp only [ConRon.Arena.Frontend.Olean.DS.exprOf]
    refine RS.pure_step fun o ho => ?_
    rw [← region_loc_eq bs ho]
    cases o with
    | none => exact RS.none
    | some c =>
      simp only [lift, bind_ok]
      refine RS.pure_step fun i hi => RS.pure_step fun x hx => RS.pure_step fun n hn => ?_
      cases Result.ok_injective hn
      simp only [locOf, Option.map_some]
      rw [memo_word hd.exprs (region_loc_fits hr ho) hi hx]
      exact RS.some rfl

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

/-! ## `stmts_fast` -/

/-- A pure `mapM` at `Option`, as `mapM` at `OptionT AM`. -/
theorem mapM_pure_option {α β : Type} (f : α → Option β) (l : List α) :
    (l.mapM (m := OptionT AM) fun a => OptionT.mk (pure (f a))) = OptionT.mk (pure (l.mapM f)) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.mapM_cons, List.mapM_cons, ih]
    cases f a with
    | none => rfl
    | some b =>
      show (OptionT.mk (pure (t.mapM f)) >>= fun r => pure (b :: r) : OptionT AM _) = _
      cases t.mapM f <;> rfl

/-- The twin's statement of a constant, at `OptionT AM`. -/
def stmtT (t : ConRon.Arena.Frontend.Olean.PtrRead) (s : CEntryF UInt64 UInt64) :
    OptionT AM ConRon.Arena.Frontend.Olean.StmtRec :=
  OptionT.mk (t.rdName s.name) >>= fun n =>
    (s.levelParams.mapM (m := OptionT AM) fun v => OptionT.mk (t.rdName v)) >>= fun lps =>
      OptionT.mk (t.rdExpr s.type) >>= fun e => pure ⟨n, lps, e⟩

/-- `stmtT` of the memo is the twin's pure function. -/
theorem stmtT_eq (P : ConRon.Arena.Frontend.Olean.OleanPins) (R : ConLeche.Frontend.Olean.Region) (t : TDS)
    (s : CEntryF UInt64 UInt64) :
    stmtT (ConRon.Arena.Frontend.Olean.DS.read P R t) s = OptionT.mk (pure (do
      pure ⟨← ConRon.Arena.Frontend.Olean.DS.nameOf P R t s.name,
        ← s.levelParams.mapM (ConRon.Arena.Frontend.Olean.DS.nameOf P R t),
        ← ConRon.Arena.Frontend.Olean.DS.exprOf R t s.type⟩)) := by
  rw [stmtT]
  show (OptionT.mk (pure (ConRon.Arena.Frontend.Olean.DS.nameOf P R t s.name)) >>= fun n =>
    (s.levelParams.mapM (m := OptionT AM) fun v => OptionT.mk (pure (ConRon.Arena.Frontend.Olean.DS.nameOf P R t v))) >>= fun lps =>
      OptionT.mk (pure (ConRon.Arena.Frontend.Olean.DS.exprOf R t s.type)) >>= fun e =>
        pure (⟨n, lps, e⟩ : ConRon.Arena.Frontend.Olean.StmtRec) : OptionT AM _) = _
  rw [mapM_pure_option]
  cases ConRon.Arena.Frontend.Olean.DS.nameOf P R t s.name with
  | none => rfl
  | some n =>
    show (OptionT.mk (pure (s.levelParams.mapM (ConRon.Arena.Frontend.Olean.DS.nameOf P R t))) >>= _ : OptionT AM _) = _
    cases s.levelParams.mapM (ConRon.Arena.Frontend.Olean.DS.nameOf P R t) with
    | none => rfl
    | some lps =>
      show (OptionT.mk (pure (ConRon.Arena.Frontend.Olean.DS.exprOf R t s.type)) >>= _ : OptionT AM _) = _
      cases ConRon.Arena.Frontend.Olean.DS.exprOf R t s.type <;> rfl

/-- **`stmts_read` is `stmtsFast`'s last step.** -/
theorem stmts_read_refines {pk bs r pers} {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r)
    (hd : DSRel d t) {sks : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {l : List (CEntryF UInt64 UInt64)} (hl : List.Forall₂ EV sks.val l) (st lst) :
    RS pers (fun v l' => List.Forall₂ (EqA absStmt) v.val l') st lst
      (stmts_read d pk pers st.store bs r sks)
      (l.mapM (m := OptionT AM) (stmtT (ConRon.Arena.Frontend.Olean.DS.read (absPins pk) (absRegion bs r) t))) := by
  have hp := ds_ptr_rel (pk := pk) (pers := pers) hr hd
  rw [stmts_read]
  refine RS.vec_map (R := EqA absStmt)
    (loop := fun ar out i => stmts_read_loop d pk pers ar bs r sks out i)
    hl ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show stmts_read_loop d pk pers ar bs r sks out i = _
    rw [stmts_read_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    show RS _ _ _ _ (stmts_read_loop d pk pers st.store bs r sks out i) _
    rw [stmts_read_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    obtain ⟨n', lp', ty', k'⟩ := x'
    obtain ⟨hn, hlp, he, -⟩ := hS
    dsimp only at hn he hlp
    subst hn he
    simp only [stmtT, bind_assoc, pure_bind]
    refine RS.bindT (hp.nm st lst x.name) (fun _ _ => by rfl)
      fun a b s1 lst1 hR => RS.bindT
        (names_map_refines hp hlp (withStore st s1) lst1) (fun _ _ => by rfl)
        fun a2 b2 s2 lst2 hR2 => RS.bindT (hp.ex (withStore (withStore st s1) s2) lst2 x.ty) (fun _ _ => by rfl)
          fun a3 b3 s3 lst3 hR3 => RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    cases hR; cases hR3
    cases (show _ = b2 from hR2)
    exact hK _ _ s3 lst3 out1 i3 rfl (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

theorem stmts_names_abs {l0 : List (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {l : List (CEntryF UInt64 UInt64)} (h : List.Forall₂ EV l0 l) :
    (l0.flatMap fun s => s.name :: s.level_params.val).map absWord =
      l.flatMap fun s => s.name :: s.levelParams := by
  induction h with
  | nil => rfl
  | cons h0 _ ih =>
    simp only [List.flatMap_cons, List.map_append, ih, List.map_cons, List.cons_append, h0.name]
    rw [show List.map absWord _ = _ from h0.levelParams]

theorem stmts_types_abs {l0 : List (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {l : List (CEntryF UInt64 UInt64)} (h : List.Forall₂ EV l0 l) :
    (l0.map (·.ty)).map absWord = l.map (·.type) := by
  induction h with
  | nil => rfl
  | cons h0 _ ih => simp only [List.map_cons, ih, h0.type]

/-- **`stmts_fast` is `stmtsFast`.** -/
theorem stmts_fast_refines {pk bs r pers st lst}
    {sks : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {l : List (CEntryF UInt64 UInt64)} (hr : RegionFits bs r) (hl : List.Forall₂ EV sks.val l) :
    RS pers (fun v l' => List.Forall₂ (EqA absStmt) v.val l') st lst
      (stmts_fast pk pers st.store bs r sks)
      (stmtsFast (absPins pk) (absRegion bs r) l) := by
  rw [stmts_fast, stmtsFast]
  refine RS.pure_step fun q hq => ?_
  obtain ⟨n, e⟩ := q
  obtain ⟨hn, he⟩ := stmts_roots_val hq
  rw [← stmts_names_abs hl, ← stmts_types_abs hl, ← hn, ← he]
  refine RS.bind_of (run_passes_refines hr) (fun _ _ => rfl) rfl fun d t s1 lst1 hd => ?_
  refine RS.of_eq (stmts_read_refines hr hd hl _ _) ?_
  rw [show stmtT (ConRon.Arena.Frontend.Olean.DS.read (absPins pk) (absRegion bs r) t) = _ from
    funext (stmtT_eq _ _ t), mapM_pure_option]
  rfl

end ConRon.Refine2.Frontend.Olean
