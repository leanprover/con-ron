/-
# `ConRon.Bridge.Modular.Reads` — the worker's reads, Theorem 1 (task #166)

**An accepting twin run of `workerReads` is upstream's run on the snapshot, read back**
(`workerReads_run`): the own part's names (`readPartNames_run`), the header fixpoint
(`headerFixpoint_gives`, over `Levels.lean`'s `levelsGo_run`), every loaded part's
names, the name index (`nameIndexOf_rel`), Lean's refusal of a classic import from a module, the
doubly held names (`clashCopies_rel`), their copies' statements (`readInfos_run`), the clash
rule's heads (exactly upstream's, `isPropCheapHeadOf_run`), their statements, the clash rule over
every name (`clashOk_run`), freshness, the public-import closures.  Upstream's `parMapExcept` is
the sequential map at `ModelIO` (`mapExcept`), so `jobs` is 1.  Run style, not `vcgen`.
-/
module

public import ConRon.Bridge.Modular.Infos
public import ConRon.Bridge.Modular.Fuel

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins LvState levelsGo)
open ConLeche.Frontend.Olean (CEntryF CKindF bind_some_left Copy Roots OLeanLevel ModFiles ImportF
  ImportRec)

/-! ## The header fixpoint, as a `Gives` -/

/-- con-leche: none — **the loads' indices hold only the loaded modules**, on both sides: what
makes the loads' relation survive the store's growth (`LoadsRel.ext'`). -/
@[expose] def LoadsKeys (ld : ConRon.Arena.Frontend.Olean.HeaderLoads)
    (ldC : ConLeche.Frontend.Olean.HeaderLoads) : Prop :=
  (∀ (h : NIdx) (k : Nat), ld.index[h]? = some k → h ∈ ld.order.toList) ∧
    (∀ (n : ConLeche.Name) (k : Nat), ldC.index[n]? = some k → ldC.order[k]? = some n)

theorem foldIdx_keys :
    ∀ (l : List NIdx) (M : Std.HashMap NIdx Nat) (i : Nat) (h : NIdx) (j : Nat),
      (l.foldl (fun (acc : Std.HashMap NIdx Nat × Nat) m => (acc.1.insert m acc.2, acc.2 + 1))
        (M, i)).1[h]? = some j → h ∈ l ∨ (M[h]?).isSome = true
  | [], M, i, h, j, hj => .inr (by simp at hj; simp [hj])
  | m :: l, M, i, h, j, hj => by
    rw [List.foldl_cons] at hj
    rcases foldIdx_keys l _ _ h j hj with hh | hh
    · exact .inl (List.mem_cons_of_mem _ hh)
    · rw [Std.HashMap.getElem?_insert] at hh
      split at hh
      · rename_i he
        obtain rfl := eq_of_beq he
        exact .inl List.mem_cons_self
      · exact .inr hh

/-- The loads' relation at a larger store. -/
theorem _root_.ConRon.Bridge.Frontend.Olean.LoadsRel.ext' {st st' : EStore} (hx : Ext st st') (hw' : NStoreWF st'.ns)
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    (h : LoadsRel st ld ldC) (hk : LoadsKeys ld ldC) : LoadsRel st' ld ldC := by
  refine ⟨NR_list_ext hx h.order, h.flags,
    listRel_ext (fun _ _ hi => ImpsD.ext hx hi) h.imports, fun a n hd => ?_⟩
  cases hdo : denoteN st.ns a with
  | some n' =>
    have e : n' = n := Option.some.inj ((denoteN_ext hdo hx).symm.trans hd)
    subst e
    exact h.index a _ hdo
  | none =>
    have h1 : ld.index[a]? = none := by
      cases hi : ld.index[a]? with
      | none => rfl
      | some k =>
        obtain ⟨b, -, hab⟩ := listRel_memL h.order (hk.1 a k hi)
        have hab' : denoteN st.ns a = some b := hab
        rw [hdo] at hab'; cases hab'
    have h2 : ldC.index[n]? = none := by
      cases hi : ldC.index[n]? with
      | none => rfl
      | some k =>
        have ho := hk.2 n k hi
        rcases optRel_cases (listRel_getElem? h.order k) with ⟨g1, g2⟩ | ⟨b, c, g1, g2, g3⟩
        · rw [Array.getElem?_toList] at g2; rw [ho] at g2; cases g2
        · rw [Array.getElem?_toList] at g2; rw [ho] at g2; cases g2
          have g3' : denoteN st.ns b = some n := g3
          have := denoteN_inj hw' (denoteN_ext g3' hx) hd
          subst this
          rw [hdo] at g3'; cases g3'
    rw [h1, h2]

/-- con-leche: ConLeche/Verify/Driver/Loads.lean:669 headerFixpoint_sound — **the header fixpoint at
the twin is upstream's run**, given from any open handles. -/
theorem headerFixpoint_gives {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {isM : Bool} {imps : Array (ImportF NIdx)} {impsC : Array ImportRec}
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {s s' : AState} (hctx : Ctx pk s)
    (hi : imps.toList.mapM (denoteImport s.store) = some impsC.toList)
    (h : ConRon.Arena.Frontend.Olean.headerFixpoint (modelFs F) pk sp isM imps s = .ok (ld, s')) :
    ParseStep s s' ∧ ∃ ldC, ModelIO.Gives
      (ConLeche.Frontend.Olean.headerFixpoint (ConLeche.Frontend.Olean.moduleImports sp) isM impsC :
        ModelIO _) F (.ok ldC) ∧ LoadsRel s'.store ld ldC ∧ LoadsKeys ld ldC := by
  unfold ConRon.Arena.Frontend.Olean.headerFixpoint at h
  obtain ⟨x, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨hv, hs⟩ := AM.pure_ok h2
  subst hv hs
  obtain ⟨hst, xC, hG, hR⟩ := levelsGo_run hsp _ _ _ _ _ {} hctx (ofImports_rel _ hi)
    ⟨HMRel.empty _ _, SetRel.empty _, .nil, HMRel.empty _ _⟩ h1
  have hC : ModelIO.Gives
      (ConLeche.Frontend.Olean.headerFixpoint (ConLeche.Frontend.Olean.moduleImports sp) isM impsC :
        ModelIO _) F (.ok
      { order := xC.order, flags := xC.order.map fun m => (xC.flags[m]?).getD default,
        imports := xC.order.map fun m => (xC.imports[m]?).getD #[],
        index := xC.order.foldl (fun (acc : Std.HashMap ConLeche.Name Nat × Nat) m =>
          (acc.1.insert m acc.2, acc.2 + 1)) ({}, 0) |>.1 }) := by
    unfold ConLeche.Frontend.Olean.headerFixpoint
    dsimp only
    refine hG.bind ?_
    exact ModelIO.gives_pure _ _
  obtain ⟨-, -, hnd, -, hkC⟩ := ConLeche.Driver.headerFixpoint_sound hC.canGive
  refine ⟨hst, _, hC, ofState_rel (nsWF_of_StateOK hst.ok) hR hnd, fun h k hk => ?_, hkC⟩
  have := ofStateGo_index x.flags x.order.toList 0 x.imports #[] #[] {}
  unfold ConRon.Arena.Frontend.Olean.HeaderLoads.ofState at hk ⊢
  generalize ConRon.Arena.Frontend.Olean.HeaderLoads.ofStateGo x.flags x.order.toList 0 x.imports
    #[] #[] {} = r at this hk
  obtain ⟨fl, is, ix⟩ := r
  simp only at this hk ⊢
  subst this
  exact (foldIdx_keys _ _ _ _ _ hk).resolve_right (by simp)

/-! ## The parts -/

theorem withImports_rel {st : EStore} {own : ConRon.Arena.Frontend.Olean.NamePositions}
    {ownC : ConLeche.Frontend.Olean.NamePositions} (h : NPsRel st own ownC)
    {x : Array (ImportF NIdx)} {xC : Array ImportRec} (hx : ImpsD st x xC) :
    NPsRel st (own.withImports x) (ownC.withImports xC) := by
  have hsz : x.size = xC.size := by
    have := mapM_length hx
    simpa using this.symm
  have hE : x.isEmpty = xC.isEmpty := by unfold Array.isEmpty; rw [hsz]
  unfold ConRon.Arena.Frontend.Olean.NamePositions.withImports
    ConLeche.Frontend.Olean.NamePositions.withImports
  rw [← hE]
  cases x.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨h.isModule, ?_, by simpa using (ListRel.nil : ListRel (NPRel st) [] [])⟩
    have h1 := h.imports
    unfold ImpsD at h1 hx ⊢
    simp only [Array.toList_append, List.mapM_append, h1, hx]
    rfl
  · simp only [↓reduceIte]
    exact h

/-- The loaded parts' names, each upstream's. -/
theorem parts_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp) :
    ∀ (l : List (NIdx × ConLeche.Frontend.Olean.LoadFlags))
      (lC : List (ConLeche.Name × ConLeche.Frontend.Olean.LoadFlags))
      {parts : List ConRon.Arena.Frontend.Olean.NamePositions} {s s' : AState}, Ctx pk s →
      ListRel (fun a b => denoteN s.store.ns a.1 = some b.1 ∧ a.2 = b.2) l lC →
      l.mapM (m := AM) (fun (x : NIdx × ConLeche.Frontend.Olean.LoadFlags) => match x with
        | (n, fl) => ConRon.Arena.Frontend.Olean.readPartNames (modelFs F) pk sp n fl.level) s
        = .ok (parts, s') →
      ParseStep s s' ∧ ∃ partsC, ModelIO.Gives (ConLeche.mapExcept
          (ConLeche.Frontend.Olean.readPartNames sp) (lC.map fun x => (x.1, x.2.level)) :
          ModelIO (Except ConLeche.CheckError (List ConLeche.Frontend.Olean.NamePositions))) F
          (Except.ok partsC) ∧ ListRel (NPsRel s'.store) parts partsC := by
  intro l
  induction l with
  | nil =>
    intro lC parts s s' hctx hrel h
    cases hrel
    simp only [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, [], ModelIO.gives_pure _ _, .nil⟩
  | cons x l ih =>
    intro lC parts s s' hctx hrel h
    cases hrel with
    | @cons _ y _ lC' hxy t =>
    obtain ⟨n, fl⟩ := x
    obtain ⟨nC, flC⟩ := y
    obtain ⟨hn, hfl⟩ := hxy
    dsimp only at hn hfl
    subst hfl
    simp only [List.mapM_cons] at h
    obtain ⟨p, s₁, h1, hA⟩ := AM.bind_ok h
    obtain ⟨ps, s₂, h2, hB⟩ := AM.bind_ok hA
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hB
    obtain ⟨hst1, pC, hg, hr⟩ := readPartNames_run (R := sp) (roots_ok_of_bare hsp) rfl hctx hn h1
    obtain ⟨hst2, psC, hgs, hrs⟩ := ih lC' (hctx.step hst1)
      (listRel_ext (fun a b hab => ⟨denoteN_ext hab.1 hst1.ext, hab.2⟩) t) h2
    refine ⟨hst1.trans hst2, pC :: psC, ?_, .cons (hr.ext hst2.ext) hrs⟩
    simp only [List.map_cons]
    unfold ConLeche.mapExcept
    refine hg.bind ?_
    dsimp only
    refine hgs.bind ?_
    exact ModelIO.gives_pure _ _

theorem order_flags_rel {st : EStore} {ld : ConRon.Arena.Frontend.Olean.HeaderLoads}
    {ldC : ConLeche.Frontend.Olean.HeaderLoads} (h : LoadsRel st ld ldC) :
    ListRel (fun (a : NIdx × ConLeche.Frontend.Olean.LoadFlags)
        (b : ConLeche.Name × ConLeche.Frontend.Olean.LoadFlags) =>
        denoteN st.ns a.1 = some b.1 ∧ a.2 = b.2)
      (ld.order.zip ld.flags).toList (ldC.order.zip ldC.flags).toList := by
  rw [Array.toList_zip, Array.toList_zip, h.flags]
  generalize ldC.flags.toList = fl
  have ho := h.order
  generalize ld.order.toList = o at ho
  generalize ldC.order.toList = oC at ho
  induction ho generalizing fl with
  | nil => exact .nil
  | cons ha _ ih =>
    cases fl with
    | nil => exact .nil
    | cons f fl => exact .cons ⟨ha, rfl⟩ (ih fl)

/-! ## The clashes -/

theorem ClashRel.ext {st st' : EStore} (hx : Ext st st') {cl : ConRon.Arena.Frontend.Olean.Clash}
    {clC : ConLeche.Frontend.Olean.Clash} (h : ClashRel st cl clC) : ClashRel st' cl clC :=
  ⟨denoteN_ext h.name hx, listRel_ext (fun _ _ hq => hq.ext hx) h.copies⟩

theorem flatMap_copies_eq {st : EStore} :
    ∀ {cc : List (NIdx × Array Copy)} {ccC : List (ConLeche.Name × Array Copy)},
      ListRel (CCR st) cc ccC → cc.flatMap (·.2.toList) = ccC.flatMap (·.2.toList)
  | _, _, .nil => rfl
  | _, _, .cons ⟨_, h⟩ t => by simp [h, flatMap_copies_eq t]

theorem clashCopies_flat_eq {st : EStore} {cc : Array (NIdx × Array Copy)}
    {ccC : Array (ConLeche.Name × Array Copy)} (h : ListRel (CCR st) cc.toList ccC.toList) :
    cc.flatMap (·.2) = ccC.flatMap (·.2) := by
  apply Array.ext'
  simp only [Array.toList_flatMap]
  exact flatMap_copies_eq h

/-- A clash's copies with their statements, read back, at copies all requested. -/
theorem copies_rel {st : EStore} {cs : Array Copy} {req : Array Copy}
    {infos : Std.HashMap Copy (ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)}
    {infosC : Std.HashMap Copy (ConstantVal × CKindF ConLeche.Name Unit)}
    (hi : InfosRel st req infos infosC) (hsub : ∀ c ∈ cs.toList, c ∈ req.toList) :
    ListRel (CopyInfoRel st)
      (cs.filterMap fun c => (infos[c]?).map fun (s, k) => (c, s, k)).toList
      (cs.filterMap fun c => (infosC[c]?).map fun (s, k) => (c, s, k)).toList := by
  rw [Array.toList_filterMap, Array.toList_filterMap]
  have hsub' := hsub
  generalize cs.toList = l at hsub'
  induction l with
  | nil => exact .nil
  | cons c l ih =>
    obtain ⟨v, w, h1, h2, h3, h4⟩ := hi.rel c (hsub' c List.mem_cons_self)
    simp only [List.filterMap_cons, h1, h2, Option.map_some]
    exact .cons ⟨rfl, h3, h4⟩ (ih fun x hx => hsub' x (List.mem_cons_of_mem _ hx))

theorem clashes_rel {st : EStore} {cc : Array (NIdx × Array Copy)}
    {ccC : Array (ConLeche.Name × Array Copy)} (hcc : ListRel (CCR st) cc.toList ccC.toList)
    {infos : Std.HashMap Copy (ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)}
    {infosC : Std.HashMap Copy (ConstantVal × CKindF ConLeche.Name Unit)}
    (hi : InfosRel st (cc.flatMap (·.2)) infos infosC) :
    ListRel (ClashRel st)
      (cc.map fun (x : NIdx × Array Copy) => match x with
        | (n, cs) => ({ name := n, copies := cs.filterMap fun c => (infos[c]?).map fun (s, k) => (c, s, k) } :
          ConRon.Arena.Frontend.Olean.Clash)).toList
      (ccC.map fun (x : ConLeche.Name × Array Copy) => match x with
        | (n, cs) => ({ name := n, copies := cs.filterMap fun c => (infosC[c]?).map fun (s, k) => (c, s, k) } :
          ConLeche.Frontend.Olean.Clash)).toList := by
  rw [Array.toList_map, Array.toList_map]
  have hmem : ∀ a ∈ cc.toList, ∀ c ∈ a.2.toList, c ∈ (cc.flatMap (·.2)).toList := by
    intro a ha c hc
    simp only [Array.toList_flatMap, List.mem_flatMap]
    exact ⟨a, ha, hc⟩
  revert hmem
  generalize cc.toList = l at hcc
  generalize ccC.toList = lC at hcc
  intro hmem
  induction hcc with
  | nil => exact .nil
  | @cons a b as bs hab t ih =>
    obtain ⟨n, cs⟩ := a
    obtain ⟨nC, csC⟩ := b
    obtain ⟨hn, rfl⟩ := hab
    refine .cons ⟨hn, copies_rel hi (hmem _ List.mem_cons_self)⟩ ?_
    exact ih fun a ha => hmem a (List.mem_cons_of_mem _ ha)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads — **the twin's heads are
upstream's**, exactly. -/
theorem clashHeads_run {s : AState} (hok : StateOK s)
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    (hix : IndexRel s.store ix ixC) :
    ∀ (cls : List ConRon.Arena.Frontend.Olean.Clash) (clsC : List ConLeche.Frontend.Olean.Clash)
      (acc : Array Copy) {heads : Array Copy} {s' : AState},
      ListRel (ClashRel s.store) cls clsC →
      cls.foldlM (m := AM) (fun (acc : Array Copy) (cl : ConRon.Arena.Frontend.Olean.Clash) => do
        match (cl.copies[0]? : Option (Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)) with
        | some (_, cv, .ax _) =>
          match (← ConRon.Arena.Frontend.Olean.isPropCheapHeadOf cv.type).bind (ix.first[·]?) with
          | some c => pure (acc.push c)
          | none => pure acc
        | _ => pure acc) acc s = .ok (heads, s') →
      s' = s ∧ heads = clsC.foldl (fun (acc : Array Copy) (cl : ConLeche.Frontend.Olean.Clash) =>
        match (cl.copies[0]? : Option (Copy × ConstantVal × CKindF ConLeche.Name Unit)) with
        | some (_, cv, .ax _) =>
          match (ConLeche.Frontend.Olean.isPropCheap.headOf cv.type).bind (ixC.first[·]?) with
          | some c => acc.push c
          | none => acc
        | _ => acc) acc := by
  intro cls
  induction cls with
  | nil =>
    intro clsC acc heads s' hrel h
    cases hrel
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨rfl, rfl⟩
  | cons cl cls ih =>
    intro clsC acc heads s' hrel h
    cases hrel with
    | @cons _ clC _ clsC hc t =>
    have hw := nsWF_of_StateOK hok
    rw [List.foldlM_cons] at h
    rw [List.foldl_cons]
    obtain ⟨acc', s₁, h1, h2⟩ := AM.bind_ok h
    -- the first copy: an axiom on both sides or on neither
    have hfirst := hc.copies
    have step : s₁ = s ∧ acc' = (match (clC.copies[0]? : Option (Copy × ConstantVal × CKindF ConLeche.Name Unit)) with
        | some (_, cv, .ax _) =>
          match (ConLeche.Frontend.Olean.isPropCheap.headOf cv.type).bind (ixC.first[·]?) with
          | some c => acc.push c
          | none => acc
        | _ => acc) := by
      try rw [← Array.getElem?_toList] at h1
      try rw [← Array.getElem?_toList]
      revert h1
      generalize cl.copies.toList = l at hfirst
      generalize clC.copies.toList = lC at hfirst
      intro h1
      cases hfirst with
      | nil => obtain ⟨rfl, rfl⟩ := AM.pure_ok h1; exact ⟨rfl, rfl⟩
      | @cons x y xs ys hxy _ =>
        obtain ⟨c, cv, k⟩ := x
        obtain ⟨c', cvC, kC⟩ := y
        obtain ⟨rfl, hcv, hk⟩ := hxy
        dsimp only at hcv hk
        simp only [List.getElem?_cons_zero] at h1 ⊢
        cases k with
        | ax u =>
          simp only [denoteKindN, CKindF.mapM, pure, Option.some.injEq] at hk
          subst hk
          obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨rfl, hrel⟩ := isPropCheapHeadOf_run hok (denoteStmt_parts hcv).2.2 h3
          dsimp only
          rcases optRel_cases hrel with ⟨ho1, ho2⟩ | ⟨n, nC, ho1, ho2, hn⟩
          · rw [ho1] at h4; rw [ho2]
            simp only [Option.bind_none] at h4 ⊢
            exact ⟨(AM.pure_ok h4).2, (AM.pure_ok h4).1⟩
          · rw [ho1] at h4; rw [ho2]
            simp only [Option.bind_some] at h4 ⊢
            rw [hix.first.get_eq hw hn] at h4
            cases hf : ixC.first[nC]? with
            | none => rw [hf] at h4; exact ⟨(AM.pure_ok h4).2, (AM.pure_ok h4).1⟩
            | some c0 => rw [hf] at h4; exact ⟨(AM.pure_ok h4).2, (AM.pure_ok h4).1⟩
        | _ =>
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h1
          refine ⟨rfl, ?_⟩
          cases kC <;> first
            | rfl
            | exact absurd (ConLeche.Frontend.Olean.CKindF.mapM_tag hk).1 (by simp [CKindF.tag])
    obtain ⟨rfl, rfl⟩ := step
    exact ih clsC _ t h2

/-! ## The heads' types -/

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads — `headTysOf`'s step. -/
@[expose] def htStep (ix : ConRon.Arena.Frontend.Olean.NameIndex)
    (infos : Std.HashMap Copy (ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit))
    (m : Std.HashMap NIdx EIdx) (c : Copy) : Std.HashMap NIdx EIdx :=
  match ix.at c with
  | none => m
  | some q =>
    match (ix.first[q.name]?).bind (infos[·]?) with
    | some x => m.insert q.name x.1.type
    | none => m

theorem htStep_get {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {infos : Std.HashMap Copy (ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)}
    {m : Std.HashMap NIdx EIdx} {c : Copy} {n : NIdx} {t : EIdx}
    (h : (htStep ix infos m c)[n]? = some t) :
    m[n]? = some t ∨ ∃ c x, ix.first[n]? = some c ∧ infos[c]? = some x ∧ t = x.1.type := by
  unfold htStep at h
  split at h
  · exact .inl h
  · rename_i q _
    split at h
    · rename_i x hx
      rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i he
        obtain rfl := eq_of_beq he
        cases h
        obtain ⟨c', hc', hx'⟩ := Option.bind_eq_some_iff.mp hx
        exact .inr ⟨c', x, hc', hx', rfl⟩
      · exact .inl h
    · exact .inl h

theorem headTys_fold {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {infos : Std.HashMap Copy (ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)} :
    ∀ (l : List Copy) (m : Std.HashMap NIdx EIdx) (n : NIdx) (t : EIdx),
      (l.foldl (htStep ix infos) m)[n]? = some t →
      m[n]? = some t ∨ ∃ c x, ix.first[n]? = some c ∧ infos[c]? = some x ∧ t = x.1.type
  | [], m, n, t, h => .inl h
  | c :: l, m, n, t, h => by
    rw [List.foldl_cons] at h
    rcases headTys_fold l _ n t h with hA | hB
    · exact htStep_get hA
    · exact .inr hB

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads — **the twin's table of the
heads' types answers as upstream's `headTy`** where it answers. -/
theorem headTys_rel {st : EStore} (hw : NStoreWF st.ns)
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    (hix : IndexRel st ix ixC) {heads : Array Copy}
    {hinfos : Std.HashMap Copy (ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)}
    {hinfosC : Std.HashMap Copy (ConstantVal × CKindF ConLeche.Name Unit)}
    (hi : InfosRel st heads hinfos hinfosC) :
    HeadRel st ((ConRon.Arena.Frontend.Olean.headTysOf ix hinfos heads)[·]?)
      (fun n => (ixC.first[n]?).bind fun c => (hinfosC[c]?).map (·.1.type)) := by
  intro n t nC ht hn
  unfold ConRon.Arena.Frontend.Olean.headTysOf at ht
  rw [← Array.foldl_toList] at ht
  rcases headTys_fold _ {} n t ht with h | ⟨c, x, hc, hx, rfl⟩
  · simp at h
  · have hdom := hi.dom c x hx
    obtain ⟨v, w, h1, h2, h3, -⟩ := hi.rel c hdom
    rw [hx] at h1; cases h1
    refine ⟨w.1.type, ?_, (denoteStmt_parts h3).2.2⟩
    dsimp only
    rw [← hix.first.get_eq hw hn, hc]
    simp [h2]

/-- The clash rule over every name: the twin's accept is upstream's. -/
theorem clashesOk_run {pk : OleanPins} {ld : ConRon.Arena.Frontend.Olean.HeaderLoads}
    {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    {headTy : NIdx → Option EIdx} {headTyC : ConLeche.Name → Option Expr} :
    ∀ {cls : List ConRon.Arena.Frontend.Olean.Clash} {clsC : List ConLeche.Frontend.Olean.Clash}
      {s s' : AState}, StateOK s → NullsRel s.store pk → HeadRel s.store headTy headTyC →
      ListRel (ClashRel s.store) cls clsC →
      cls.forM (ConRon.Arena.Frontend.Olean.clashOk pk ld headTy) s = .ok ((), s') →
      s' = s ∧ clsC.forM (ConLeche.Frontend.Olean.clashOk ldC headTyC) = .ok () := by
  intro cls
  induction cls with
  | nil =>
    intro clsC s s' _ _ _ hrel h
    cases hrel
    exact ⟨(AM.pure_ok (show (pure () : AM Unit) s = .ok ((), s') from h)).2, rfl⟩
  | cons cl cls ih =>
    intro clsC s s' hok hnu hh hrel h
    cases hrel with
    | @cons _ clC _ clsC hc t =>
    have h' : (ConRon.Arena.Frontend.Olean.clashOk pk ld headTy cl >>= fun _ =>
        cls.forM (ConRon.Arena.Frontend.Olean.clashOk pk ld headTy)) s = .ok ((), s') := h
    suffices H : s' = s ∧ (ConLeche.Frontend.Olean.clashOk ldC headTyC clC >>= fun _ =>
        clsC.forM (ConLeche.Frontend.Olean.clashOk ldC headTyC)) = .ok () from H
    obtain ⟨u, s₁, h1, h2⟩ := AM.bind_ok h'
    obtain ⟨rfl, hC⟩ := clashOk_run hok hnu hh hc h1
    obtain ⟨rfl, hC'⟩ := ih hok hnu hh t h2
    rw [hC]
    exact ⟨rfl, hC'⟩

/-! ## The reads -/

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads — **an accepting twin run of
the worker's reads is upstream's run on the snapshot, read back** (the module note). -/
theorem workerReads_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {m : NIdx} {mC : ConLeche.Name} {x : Array (ImportF NIdx)} {xC : Array ImportRec}
    {wr : ConRon.Arena.Frontend.Olean.WorkerReads} {s s' : AState} (hctx : Ctx pk s)
    (hm : denoteN s.store.ns m = some mC) (hx : ImpsD s.store x xC)
    (h : ConRon.Arena.Frontend.Olean.workerReads (modelFs F) pk sp m x s = .ok (wr, s')) :
    ParseStep s s' ∧ ∃ wrC, ModelIO.Gives (ConLeche.Frontend.Olean.workerReads (.ofPath sp) mC 1 xC :
        ModelIO _) F (.ok wrC) ∧ WorkerReadsRel s'.store wr wrC ∧ LoadsKeys wr.loads wrC.loads := by
  unfold ConRon.Arena.Frontend.Olean.workerReads at h
  -- the own part
  obtain ⟨own0, s₁, h1, hA⟩ := AM.bind_ok h
  obtain ⟨hst1, own0C, hg1, hr1⟩ := readPartNames_run (roots_ok_of_bare hsp) rfl hctx hm h1
  have hctx1 := hctx.step hst1
  have hown := withImports_rel hr1 (hx.ext hst1.ext)
  -- the header fixpoint
  obtain ⟨ld, s₂, h2, hB⟩ := AM.bind_ok hA
  obtain ⟨hst2, ldC, hg2, hld, hkeys⟩ := headerFixpoint_gives hsp hctx1 hown.imports h2
  have hctx2 := hctx1.step hst2
  rw [hown.isModule] at hg2
  -- the loaded parts
  obtain ⟨parts, s₃, h3, hC⟩ := AM.bind_ok hB
  obtain ⟨hst3, partsC, hg3, hr3⟩ := parts_run hsp _ _ hctx2 (order_flags_rel hld) h3
  have hctx3 := hctx2.step hst3
  have hw3 := nsWF_of_StateOK hctx3.ok
  have hld3 := hld.ext' hst3.ext hw3 hkeys
  have hix := nameIndexOf_rel hw3 (ps := parts.toArray) (psC := partsC.toArray) (by simpa using hr3)
  -- the imports' module system
  obtain ⟨u, s₄, h4, hD⟩ := AM.bind_ok hC
  obtain ⟨rfl, hg4⟩ := importsModulesOk_run (mC := mC) hld3 hix ((hown.ext (hst2.trans hst3).ext).imports)
    h4
  -- the doubly held names, their copies' statements
  have hcc := clashCopies_rel hw3 hix
  obtain ⟨infos, s₅, h5, hE⟩ := AM.bind_ok hD
  obtain ⟨hst5, infosC, hg5, hi5⟩ := readInfos_run hsp hctx3 (loadsOF_of hld3) hix h5
  have hctx5 := hctx3.step hst5
  have hcl := clashes_rel (listRel_ext (fun _ _ hq => ⟨denoteN_ext hq.1 hst5.ext, hq.2⟩) hcc) hi5
  -- the heads, their statements
  obtain ⟨heads, s₆, h6, hF⟩ := AM.bind_ok hE
  unfold ConRon.Arena.Frontend.Olean.clashHeads at h6
  rw [← Array.foldlM_toList] at h6
  obtain ⟨rfl, hheads⟩ := clashHeads_run hctx5.ok (hix.ext' hst5.ext) _ _ #[] hcl h6
  obtain ⟨hinfos, s₇, h7, hG⟩ := AM.bind_ok hF
  obtain ⟨hst7, hinfosC, hg7, hi7⟩ := readInfos_run hsp hctx5
    ((loadsOF_of hld3).ext hst5.ext)
    (hix.ext' hst5.ext) h7
  have hctx7 := hctx5.step hst7
  have hw7 := nsWF_of_StateOK hctx7.ok
  have hix7 := hix.ext' (hst5.trans hst7).ext
  -- the clash rule
  obtain ⟨u, s₈, h8, hH⟩ := AM.bind_ok hG
  obtain ⟨rfl, hg8⟩ := clashesOk_run hctx7.ok hctx7.nulls (headTys_rel hw7 hix7 hi7)
    (listRel_ext (fun (a : ConRon.Arena.Frontend.Olean.Clash) (b : ConLeche.Frontend.Olean.Clash)
      (hq : ClashRel _ a b) => hq.ext hst7.ext) hcl) h8
  -- freshness
  obtain ⟨u, s₉, h9, hI⟩ := AM.bind_ok hH
  obtain ⟨rfl, hg9⟩ := freshOk_run (mC := mC) hw7 hix7 (hown.ext (hst2.trans (hst3.trans (hst5.trans hst7))).ext) h9
  obtain ⟨rfl, rfl⟩ := AM.pure_ok hI
  have hst := hst1.trans (hst2.trans (hst3.trans (hst5.trans hst7)))
  refine ⟨hst, ⟨ConLeche.Frontend.Olean.WorkerReads.mk (own0C.withImports xC) ldC
      (ConLeche.Frontend.Olean.pubClosures ldC)
      (ConLeche.Frontend.Olean.nameIndexOf partsC.toArray)
      ((ConLeche.Frontend.Olean.clashCopies (ConLeche.Frontend.Olean.nameIndexOf
        partsC.toArray)).map fun (x : ConLeche.Name × Array Copy) => match x with
          | (n, cs) => (ConLeche.Frontend.Olean.Clash.mk n (cs.filterMap fun c =>
              (infosC[c]?).map fun (s, k) => (c, s, k)))), ?_, ?_, hkeys⟩⟩
  rotate_left
  · exact ⟨hown.ext (hst2.trans (hst3.trans (hst5.trans hst7))).ext,
      hld3.ext' (hst5.trans hst7).ext hw7 hkeys, pubClosures_eq hld3, hix7,
      listRel_ext (fun (a : ConRon.Arena.Frontend.Olean.Clash) (b : ConLeche.Frontend.Olean.Clash)
        (hq : ClashRel _ a b) => hq.ext hst7.ext) hcl⟩
  -- upstream's run, step by step
  unfold ConLeche.Frontend.Olean.workerReads
  refine hg1.bind ?_
  dsimp only
  refine hg2.bind ?_
  dsimp only
  refine (show (CheckerIO.parMapExcept 1 (ConLeche.Frontend.Olean.OleanReads.ofPath (μ := ModelIO) sp).names
      ((ldC.order.zip ldC.flags).toList.map fun x => (x.1, x.2.level)) : ModelIO _).Gives F (.ok partsC)
    from hg3).bind ?_
  dsimp only
  rw [hown.isModule] at hg4
  rw [hg4]
  dsimp only
  rw [← clashCopies_flat_eq hcc]
  refine hg5.bind ?_
  dsimp only
  rw [hheads] at hg7
  rw [← Array.foldl_toList]
  refine hg7.bind ?_
  dsimp only
  split
  · rename_i e heq
    exact absurd (heq.symm.trans hg8) (by simp)
  · split
    · rename_i e heq
      exact absurd (heq.symm.trans hg9) (by simp)
    · exact ModelIO.gives_pure _ _

end ConRon.Bridge.Modular
