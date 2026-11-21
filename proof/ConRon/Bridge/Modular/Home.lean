/-
# `ConRon.Bridge.Modular.Home` — the worker's home, Theorem 1 (task #166)

**The twin's home of a module is upstream's `WorkerFacts.home`** (`home_run`): the private part's
files read off the snapshot (`readFiles`), the private view's load a load by the specification
(`LoadOf 0 mC f lC`, `loadAt_runOf`), and the views' check upstream's accept
(`checkViews mC f lC = .ok expo`).

The twin checks the views over the views parsed whole (`parseAllViews`, then its `checkViews`
over the parsed private view); upstream over the load.  So the proof reads the twin's parse as
upstream's (`parseMany_run`, `parseAllViews_run`: each view `decodeAt`'s), and then what
upstream's check asks of the parts over the load is the parse's: each part's flag, the server
part's imports, the name tables (`decodeAt` checks them), and the exported level of each private
constant (`expoOfParts_run`), the load's constants being the parse's but for a theorem's value,
which upstream reads off the file where it compares one (`entryAt`).

Run style (simulations over `AM.bind_ok`), as `Bridge/Frontend/Olean/Closure.lean`.
-/
module

public import ConRon.Bridge.Modular.Rel
public import ConRon.Bridge.Frontend.Olean.Sparse
public import ConRon.Bridge.Frontend.Olean.Parse
public import ConRon.Bridge.Frontend.Olean.Closure
public import ConLeche.Verify.Driver.Loads
public import ConLeche.Frontend.Olean.Module
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.View

public section

namespace ConRon.Bridge.Modular.Home

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins DS)
open ConLeche.Frontend.Olean (Region CEntryF CKindF ImportF ImportRec Roots OLeanLevel ModFiles
  ModSkel constSkel moduleSkel nameP exprP decodeAt constSpec bind_some_left)

/-! ## A decoded view read back -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:437-440 ModDecoded — a decoded view read back:
its flag, its imports and its constants denoted. -/
structure DecRel (st : EStore) (d : ConRon.Arena.Frontend.Olean.ModDecoded)
    (dC : ConLeche.Frontend.Olean.ModDecoded) : Prop where
  isModule : d.isModule = dC.isModule
  imports : d.imports.toList.mapM (denoteImport st) = some dC.imports.toList
  constants : d.constants.toList.mapM (denoteEntry st) = some dC.constants.toList

theorem DecRel.ext {st st' : EStore} (hx : Ext st st') {d : ConRon.Arena.Frontend.Olean.ModDecoded}
    {dC : ConLeche.Frontend.Olean.ModDecoded} (h : DecRel st d dC) : DecRel st' d dC :=
  ⟨h.isModule, list_mono (fun _ _ hy => denoteImport_ext hx hy) _ h.imports,
    list_mono (fun _ _ hy => denoteEntry_ext hx hy) _ h.constants⟩

/-! ## The passes' parse -/

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:327-337 parseMany — `addrs.all (constNamesOk r)`. -/
theorem allConstNamesOk_run {pk : OleanPins} {r : Region} :
    ∀ (addrs : List UInt64) {s s' : AState}, Ctx pk s →
      ConRon.Arena.Frontend.Olean.allConstNamesOk pk r addrs s = .ok (true, s') →
      ParseStep s s' ∧ addrs.all (ConLeche.Frontend.Olean.constNamesOk r) = true
  | [], s, s', hctx, h => by
    rw [ConRon.Arena.Frontend.Olean.allConstNamesOk] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, rfl⟩
  | a :: as, s, s', hctx, h => by
    rw [ConRon.Arena.Frontend.Olean.allConstNamesOk] at h
    obtain ⟨b, s₁, h1, h2⟩ := AM.bind_ok h
    cases b with
    | false => cases (AM.pure_ok h2).1
    | true =>
      simp only [↓reduceIte] at h2
      obtain ⟨hst1, ha⟩ := constNamesOk_run hctx h1
      obtain ⟨hst2, has⟩ := allConstNamesOk_run as (hctx.step hst1) h2
      exact ⟨hst1.trans hst2, by simp [ha, has]⟩

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:327-337 parseMany — each address's module
skeleton and its constants' skeletons. -/
theorem manySkels_run {r : Region} :
    ∀ (addrs : List UInt64) {ms : List (ModSkel × List (CEntryF UInt64 UInt64))} {s s' : AState},
      ConRon.Arena.Frontend.Olean.manySkels r addrs s = .ok (some ms, s') →
      s' = s ∧ ListRel (fun a (p : ModSkel × List (CEntryF UInt64 UInt64)) =>
        moduleSkel r a = some p.1 ∧ p.1.consts.mapM (constSkel r) = some p.2) addrs ms
  | [], ms, s, s', h => by
    rw [ConRon.Arena.Frontend.Olean.manySkels] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    exact ⟨hs, .nil⟩
  | a :: as, ms, s, s', h => by
    rw [ConRon.Arena.Frontend.Olean.manySkels] at h
    cases hsk : moduleSkel r a with
    | none =>
      simp only [hsk] at h
      cases (AM.pure_ok h).1
    | some sk =>
      simp only [hsk] at h
      obtain ⟨o, s₁, h1, h⟩ := AM.bind_ok h
      cases o with
      | none => cases (AM.pure_ok h).1
      | some cs =>
        have h' : (ConRon.Arena.Frontend.Olean.manySkels r as >>=
            fun (o : Option (List (ModSkel × List (CEntryF UInt64 UInt64)))) =>
              (match o with
                | none => pure none
                | some rest => pure (some ((sk, cs) :: rest)) :
                AM (Option (List (ModSkel × List (CEntryF UInt64 UInt64)))))) s₁ =
            .ok (some ms, s') := h
        obtain ⟨hs1, hcs⟩ := constsSkel_run _ h1
        subst hs1
        obtain ⟨o', s₂, h2, h⟩ := AM.bind_ok h'
        cases o' with
        | none => cases (AM.pure_ok h).1
        | some rest =>
          obtain ⟨hv, hs⟩ := AM.pure_ok h
          cases hv
          subst hs
          obtain ⟨hs2, hrest⟩ := manySkels_run as h2
          exact ⟨hs2, .cons ⟨hsk, hcs⟩ hrest⟩

/-- A constant read off the memo is a pure read of it. -/
theorem entryMap_pr (pk : OleanPins) (r : Region) (st : DS) (c : CEntryF UInt64 UInt64) :
    PR (OptionT.mk (ConRon.Arena.Frontend.Olean.entryMap (DS.read pk r st) c))
      (c.mapM (st.nameOf pk r) (st.exprOf r)) :=
  PR.entryMap (fn := fun v => OptionT.mk ((DS.read pk r st).rdName v))
    (fe := fun v => OptionT.mk ((DS.read pk r st).rdExpr v)) (fun _ _ => rfl) (fun _ _ => rfl) c

/-- `ModSkel.read` over the memo is a pure read of it. -/
theorem modSkelRead_pr (pk : OleanPins) (r : Region) (st : DS) (sk : ModSkel)
    (cs : List (CEntryF UInt64 UInt64)) :
    PR (OptionT.mk (ConRon.Arena.Frontend.Olean.ModSkel.read (DS.read pk r st) sk cs))
      ((sk.imports.mapM fun i => i.mapM (st.nameOf pk r)) >>= fun imports =>
        (cs.mapM fun c => c.mapM (st.nameOf pk r) (st.exprOf r)) >>= fun constants =>
          some (⟨sk.isModule, imports.toArray, constants.toArray⟩ :
            ConRon.Arena.Frontend.Olean.ModDecoded)) := by
  have himp : ∀ i : ImportF UInt64, PR (i.mapM (m := OptionT AM)
      fun v => OptionT.mk ((DS.read pk r st).rdName v)) (i.mapM (st.nameOf pk r)) :=
    fun i => (show PR (OptionT.mk ((DS.read pk r st).rdName i.module)) (st.nameOf pk r i.module)
      from fun _ => rfl).bind fun _ => PR.pure _
  exact (PR.mapM himp sk.imports).bind fun _ =>
    (PR.mapM (entryMap_pr pk r st) cs).bind fun _ => PR.pure _

/-- The specification's constants of some skeletons: each `constSpec`. -/
theorem mapM_constSpec {r : Region} :
    ∀ {ls : List Nat} {sks : List (CEntryF UInt64 UInt64)} {cs : List (CEntryF Name Expr)},
      ls.mapM (constSkel r) = some sks → sks.mapM (fun c => c.mapM (nameP r) (exprP r)) = some cs →
      ls.mapM (constSpec r) = some cs
  | [], sks, cs, h1, h2 => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h1
    subst h1
    simpa using h2
  | l :: ls, sks, cs, h1, h2 => by
    simp only [List.mapM_cons] at h1
    obtain ⟨sk, hsk, h1⟩ := bind_some_left h1
    obtain ⟨sks', hsks, h1⟩ := bind_some_left h1
    simp only [pure, Option.some.injEq] at h1
    subst h1
    simp only [List.mapM_cons] at h2
    obtain ⟨c, hc, h2⟩ := bind_some_left h2
    obtain ⟨cs', hcs, h2⟩ := bind_some_left h2
    simp only [pure, Option.some.injEq] at h2
    subst h2
    simp only [List.mapM_cons, constSpec, hsk, mapM_constSpec hsks hcs]
    simp only [bind, Option.bind, hc]
    rfl

/-- con-leche: ConLeche/Verify/Frontend/Olean/Equiv.lean:393 parseMany_eq — **the twin's parse of
some views is each one's `decodeAt`, read back.** -/
theorem parseMany_run {pk : OleanPins} {r : Region} {addrs : List UInt64}
    {ds : List ConRon.Arena.Frontend.Olean.ModDecoded} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.parseMany pk r addrs s = .ok (some ds, s')) :
    ParseStep s s' ∧ ∃ dsC, addrs.mapM (decodeAt r) = some dsC ∧
      ListRel (DecRel s'.store) ds dsC := by
  unfold ConRon.Arena.Frontend.Olean.parseMany at h
  obtain ⟨b, s₁, h1, hA⟩ := AM.bind_ok h
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hA
    cases (AM.pure_ok hA).1
  | true =>
  simp only [↓reduceIte, pure_bind] at hA
  obtain ⟨hst1, hall⟩ := allConstNamesOk_run addrs hctx h1
  obtain ⟨o, s₂, h2, hB⟩ := AM.bind_ok hA
  cases o with
  | none => cases (AM.pure_ok hB).1
  | some ms =>
  obtain ⟨hs2, hms⟩ := manySkels_run addrs h2
  subst hs2
  obtain ⟨o, s₃, h3, hC⟩ := AM.bind_ok hB
  cases o with
  | none => cases (AM.pure_ok hC).1
  | some st =>
  unfold ConRon.Arena.Frontend.Olean.runPasses at h3
  obtain ⟨o', s₄, h4, h5⟩ := AM.bind_ok h3
  rcases o' with _ | ⟨nm, mk, st'⟩
  · cases (AM.pure_ok h5).1
  obtain ⟨hv, hs⟩ := AM.pure_ok h5
  cases hv
  subst hs
  obtain ⟨hst3, hN, hE, -⟩ := runMarked_run (hctx.step hst1) h4
  -- the reads off the memo are pure
  have hpr := PR.mapM (f := fun p : ModSkel × List (CEntryF UInt64 UInt64) =>
      OptionT.mk (ConRon.Arena.Frontend.Olean.ModSkel.read (DS.read pk r st) p.1 p.2))
    (fun p => modSkelRead_pr pk r st p.1 p.2) ms
  have h' := hpr s₃
  have hh : (ms.mapM (m := OptionT AM) fun p =>
      OptionT.mk (ConRon.Arena.Frontend.Olean.ModSkel.read (DS.read pk r st) p.1 p.2)).run s₃ =
      .ok (some ds, s') := hC
  rw [OptionT.run, h'] at hh
  injection hh with hh
  simp only [Prod.mk.injEq] at hh
  obtain ⟨hds, rfl⟩ := hh
  refine ⟨hst1.trans hst3, ?_⟩
  -- each module, by the specification
  have key : ∀ (as : List UInt64) (ps : List (ModSkel × List (CEntryF UInt64 UInt64)))
      (ds : List ConRon.Arena.Frontend.Olean.ModDecoded),
      (∀ p ∈ ps, p ∈ ms) → (∀ a ∈ as, a ∈ addrs) →
      ListRel (fun a (p : ModSkel × List (CEntryF UInt64 UInt64)) =>
        moduleSkel r a = some p.1 ∧ p.1.consts.mapM (constSkel r) = some p.2) as ps →
      ps.mapM (fun p => (p.1.imports.mapM fun i => i.mapM (st.nameOf pk r)) >>= fun imports =>
        (p.2.mapM fun c => c.mapM (st.nameOf pk r) (st.exprOf r)) >>= fun constants =>
          some (⟨p.1.isModule, imports.toArray, constants.toArray⟩ :
            ConRon.Arena.Frontend.Olean.ModDecoded)) = some ds →
      ∃ dsC, as.mapM (decodeAt r) = some dsC ∧ ListRel (DecRel s₃.store) ds dsC := by
    intro as ps ds hps has h2 hm
    induction h2 generalizing ds with
    | nil =>
      simp only [List.mapM_nil, pure, Option.some.injEq] at hm
      subst hm
      exact ⟨[], rfl, .nil⟩
    | @cons a p as ps hap _ ih =>
      simp only [List.mapM_cons] at hm
      obtain ⟨d, hd, hm⟩ := bind_some_left hm
      obtain ⟨ds', hds', hm⟩ := bind_some_left hm
      simp only [pure, Option.some.injEq] at hm
      subst hm
      obtain ⟨imps, himps, hd⟩ := bind_some_left hd
      obtain ⟨cs, hcs, hd⟩ := bind_some_left hd
      simp only [Option.some.injEq] at hd
      subst hd
      have hpm : p ∈ ms := hps p (by simp)
      have ham : a ∈ addrs := has a (by simp)
      -- the names and expressions of this module's roots
      have hNp : ∀ x, (x ∈ p.1.imports.map (·.module) ∨ ∃ c ∈ p.2, x ∈ c.names) →
          ∀ y, st.nameOf pk r x = some y → ∃ z, nameP r x = some z ∧ denoteN s₃.store.ns y = some z := by
        intro x hx y hy
        refine hN x ?_ y hy
        rcases hx with hx | ⟨c, hc, hx⟩
        · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨p.1, List.mem_map_of_mem hpm, hx⟩)
        · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨c,
            List.mem_flatten.mpr ⟨p.2, List.mem_map_of_mem hpm, hc⟩, hx⟩)
      have hEp : ∀ c ∈ p.2, ∀ x ∈ c.exprs, ∀ y, st.exprOf r x = some y →
          ∃ z, exprP r x = some z ∧ denoteE s₃.store y = some z := by
        intro c hc x hx y hy
        exact hE x (List.mem_flatMap.mpr ⟨c, List.mem_flatten.mpr ⟨p.2, List.mem_map_of_mem hpm, hc⟩,
          hx⟩) y hy
      obtain ⟨impsC, himpsC, hdimps⟩ := list_sim (g := ImportF.mapM (nameP r))
        (d := denoteImport s₃.store) p.1.imports himps (fun i hi y hy => by
          simp only [ImportF.mapM, bind, Option.bind] at hy
          cases hmn : st.nameOf pk r i.module with
          | none => rw [hmn] at hy; cases hy
          | some x =>
            rw [hmn] at hy
            cases hy
            obtain ⟨z, hz, hdz⟩ := hNp i.module (.inl (List.mem_map_of_mem hi)) x hmn
            refine ⟨{ i with module := z }, ?_, ?_⟩
            · simp only [ImportF.mapM, hz]; rfl
            · simp only [denoteImport, ImportF.mapM, hdz]; rfl)
      obtain ⟨csC, hcsC, hdcs⟩ := list_sim (g := fun c => c.mapM (nameP r) (exprP r))
        (d := denoteEntry s₃.store) p.2 hcs (fun c hc y hy => by
          obtain ⟨z, hz, hdz⟩ := entry_sim (fnC := nameP r) (feC := exprP r)
            (dn := denoteN s₃.store.ns) (de := denoteE s₃.store) c hy
            (fun x hx => hNp x (.inr ⟨c, hc, hx⟩)) (hEp c hc)
          exact ⟨z, hz, hdz⟩)
      obtain ⟨dsC, hdsC, hrel⟩ := ih ds' (fun q hq => hps q (List.mem_cons_of_mem _ hq))
        (fun b hb => has b (List.mem_cons_of_mem _ hb)) hds'
      have hcn : ConLeche.Frontend.Olean.constNamesOk r a = true := by
        have := List.all_eq_true.mp hall a ham
        exact this
      refine ⟨⟨p.1.isModule, impsC.toArray, csC.toArray⟩ :: dsC, ?_, .cons ⟨rfl, ?_, ?_⟩ hrel⟩
      · simp only [List.mapM_cons, hdsC]
        have hdec : decodeAt r a = some ⟨p.1.isModule, impsC.toArray, csC.toArray⟩ := by
          simp [decodeAt, hcn, hap.1, himpsC, mapM_constSpec hap.2 hcsC, bind, Option.bind]
        rw [hdec]
        rfl
      · simpa using hdimps
      · simpa using hdcs
  exact key addrs ms ds (fun p hp => hp) (fun a ha => ha) hms hds

/-! ## The views -/

/-- Two arrays read back off one array of import handles are one. -/
theorem imports_den_eq {st : EStore} {a : Array (ImportF NIdx)} {zs ws : Array ImportRec}
    (h1 : a.toList.mapM (denoteImport st) = some zs.toList)
    (h2 : a.toList.mapM (denoteImport st) = some ws.toList) : zs = ws := by
  rw [h1] at h2
  exact Array.toList_inj.mp (Option.some.inj h2)

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:339-343 parseAt -/
theorem parseAt_run {pk : OleanPins} {r : Region} {a : UInt64}
    {d : ConRon.Arena.Frontend.Olean.ModDecoded} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.parseAt pk r a s = .ok (some d, s')) :
    ParseStep s s' ∧ ∃ dC, ConLeche.Frontend.Olean.parseAt r a = some dC ∧ DecRel s'.store d dC := by
  unfold ConRon.Arena.Frontend.Olean.parseAt at h
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
  split at h2
  · rename_i _ d'
    obtain ⟨hv, rfl⟩ := AM.pure_ok h2
    cases hv
    obtain ⟨hst, dsC, hdec, hrel⟩ := parseMany_run hctx h1
    cases hrel with
    | cons hd hrest =>
      cases hrest
      refine ⟨hst, _, ?_, hd⟩
      unfold ConLeche.Frontend.Olean.parseAt
      rw [ConLeche.Frontend.Olean.parseMany_eq, hdec]
  · cases (AM.pure_ok h2).1

/-- con-leche: ConLeche/Frontend/Olean/View.lean:87-92 parseView — the check against the start of
`M.olean`. -/
theorem checkImportsPre_run {pk : OleanPins} {f : ModFiles}
    {d d' : ConRon.Arena.Frontend.Olean.ModDecoded} {dC : ConLeche.Frontend.Olean.ModDecoded}
    {s s' : AState} (hctx : Ctx pk s) (hd : DecRel s.store d dC)
    (h : ConRon.Arena.Frontend.Olean.checkImportsPre pk f d s = .ok (some d', s')) :
    ParseStep s s' ∧ d' = d ∧
      ConLeche.Frontend.Olean.importsPre f.exported.bytes = some dC.imports := by
  unfold ConRon.Arena.Frontend.Olean.checkImportsPre at h
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
  cases o with
  | none => cases (AM.pure_ok h2).1
  | some pre =>
    simp only at h2
    split at h2
    · rename_i he
      obtain ⟨hv, rfl⟩ := AM.pure_ok h2
      cases hv
      obtain ⟨hst, zs, hzs, hdz⟩ := importsPre_run hctx h1
      have he' : pre = d.imports := by simpa using he
      subst he'
      refine ⟨hst, rfl, ?_⟩
      rw [hzs, imports_den_eq hdz (list_mono (fun _ _ hy => denoteImport_ext hst.ext hy) _ hd.imports)]
    · cases (AM.pure_ok h2).1

/-- con-leche: ConLeche/Verify/Frontend/Olean/View.lean:27 parseView_eq_spec — **one view of the
twin's is upstream's**. -/
theorem parseView_run {pk : OleanPins} {f : ModFiles} {level : OLeanLevel}
    {d : ConRon.Arena.Frontend.Olean.ModDecoded} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.parseView pk f level s = .ok (some d, s')) :
    ParseStep s s' ∧ ∃ dC, ConLeche.Frontend.Olean.parseView f level = some dC ∧
      DecRel s'.store d dC := by
  unfold ConRon.Arena.Frontend.Olean.parseView at h
  cases hvr : f.viewRegion level with
  | none => simp only [hvr] at h; cases (AM.pure_ok h).1
  | some ra =>
    obtain ⟨r, a⟩ := ra
    simp only [hvr] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    cases o with
    | none => cases (AM.pure_ok h2).1
    | some d₁ =>
      simp only at h2
      obtain ⟨hst1, dC, hdC, hrel⟩ := parseAt_run hctx h1
      obtain ⟨hst2, rfl, hpre⟩ := checkImportsPre_run (hctx.step hst1) hrel h2
      refine ⟨hst1.trans hst2, dC, ?_, hrel.ext hst2.ext⟩
      simp [ConLeche.Frontend.Olean.parseView, hvr, hdC, hpre, bind, Option.bind]

/-- con-leche: ConLeche/Frontend/Olean/View.lean:94-98 AllViews — the three views read back. -/
structure AllRel (st : EStore) (v : ConRon.Arena.Frontend.Olean.AllViews)
    (vC : ConLeche.Frontend.Olean.AllViews) : Prop where
  exported : DecRel st v.exported vC.exported
  server : DecRel st v.server vC.server
  «private» : DecRel st v.private vC.private

/-- con-leche: ConLeche/Verify/Frontend/Olean/View.lean:85 parseAllViews_eq — **the twin's three
views are upstream's**. -/
theorem parseAllViews_run {pk : OleanPins} {f : ModFiles}
    {v : ConRon.Arena.Frontend.Olean.AllViews} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.parseAllViews pk f s = .ok (some v, s')) :
    ParseStep s s' ∧ ∃ vC, ConLeche.Frontend.Olean.parseAllViews f = some vC ∧
      AllRel s'.store v vC := by
  unfold ConRon.Arena.Frontend.Olean.parseAllViews at h
  by_cases hm : f.isModule = true
  · simp only [hm, ↓reduceIte] at h
    obtain ⟨ex, fs, fp⟩ := f
    cases fs with
    | none => cases (AM.pure_ok h).1
    | some sv =>
    cases fp with
    | none => cases (AM.pure_ok h).1
    | some pv =>
    simp only at h
    unfold ConRon.Arena.Frontend.Olean.parseAllViewsModule at h
    rw [ConLeche.Frontend.Olean.parseAllViews_parts hm]
    simp only at h ⊢
    by_cases L1 : ((Region.single ex).loc ex.moduleDataAddr).isSome = true
    · simp only [L1, ↓reduceIte, pure_bind] at h ⊢
      cases hr2 : Region.ofParts #[ex, sv] with
      | error e => simp only [hr2] at h; cases (AM.pure_ok h).1
      | ok r2 =>
      simp only [hr2] at h ⊢
      by_cases L2 : (r2.loc sv.moduleDataAddr).isSome = true
      · simp only [L2, ↓reduceIte] at h ⊢
        cases hr3 : Region.ofParts #[ex, sv, pv] with
        | error e => simp only [hr3] at h; cases (AM.pure_ok h).1
        | ok r =>
        simp only [hr3] at h ⊢
        obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
        split at h2
        · rename_i _ de ds dp
          obtain ⟨hst1, dsC, hdec, hrel⟩ := parseMany_run hctx h1
          obtain ⟨o', s₂, h3, h4⟩ := AM.bind_ok h2
          cases o' with
          | none => cases (AM.pure_ok h4).1
          | some pre =>
          simp only at h4
          split at h4
          · rename_i hall
            obtain ⟨hv, rfl⟩ := AM.pure_ok h4
            cases hv
            obtain ⟨deC, dsC', dpC, rfl, hde, hds, hdp⟩ : ∃ a b c, dsC = [a, b, c] ∧
                DecRel s₁.store de a ∧ DecRel s₁.store ds b ∧ DecRel s₁.store dp c := by
              rcases hrel with _ | ⟨h1', _ | ⟨h2', _ | ⟨h3', _ | _⟩⟩⟩
              exact ⟨_, _, _, rfl, h1', h2', h3'⟩
            obtain ⟨hst3, zs, hzs, hdz⟩ := importsPre_run (hctx.step hst1) h3
            simp only [Bool.and_eq_true, beq_iff_eq] at hall
            obtain ⟨⟨e1, e2⟩, e3⟩ := hall
            have hx := hst3.ext
            have z1 := imports_den_eq hdz (e1 ▸ list_mono (fun _ _ hy => denoteImport_ext hx hy) _ hde.imports)
            have z2 := imports_den_eq hdz (e2 ▸ list_mono (fun _ _ hy => denoteImport_ext hx hy) _ hds.imports)
            have z3 := imports_den_eq hdz (e3 ▸ list_mono (fun _ _ hy => denoteImport_ext hx hy) _ hdp.imports)
            refine ⟨hst1.trans hst3, ⟨deC, dsC', dpC⟩, ?_, ⟨hde.ext hx, hds.ext hx, hdp.ext hx⟩⟩
            rw [ConLeche.Frontend.Olean.parseMany_eq, hdec]
            simp [hzs, ← z1, ← z2, ← z3]
          · cases (AM.pure_ok h4).1
        · cases (AM.pure_ok h2).1
      · simp only [L2] at h
        cases (AM.pure_ok h).1
    · simp only [L1] at h
      cases (AM.pure_ok h).1
  · simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    cases o with
    | none => cases (AM.pure_ok h2).1
    | some d =>
      obtain ⟨hv, rfl⟩ := AM.pure_ok h2
      cases hv
      obtain ⟨hst, dC, hdC, hrel⟩ := parseView_run hctx h1
      refine ⟨hst, ⟨dC, dC, dC⟩, ?_, ⟨hrel, hrel, hrel⟩⟩
      simp only [ConLeche.Frontend.Olean.parseAllViews, hm, Bool.false_eq_true, ↓reduceIte, hdC]
      rfl

end ConRon.Bridge.Modular.Home
