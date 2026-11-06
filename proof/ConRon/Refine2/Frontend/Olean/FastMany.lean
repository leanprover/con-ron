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

end ConRon.Refine2.Frontend.Olean
