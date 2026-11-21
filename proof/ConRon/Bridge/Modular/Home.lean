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
public import ConRon.Bridge.Modular.ReadsParts
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

/-! ## A constant compared, read back -/

/-- A `mapM` of an injective partial function is injective. -/
theorem mapM_inj {α β : Type} {f : α → Option β}
    (hf : ∀ a b z, f a = some z → f b = some z → a = b) :
    ∀ {l l' : List α} {zs : List β}, l.mapM f = some zs → l'.mapM f = some zs → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: l', zs, h1, h2 => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h1
    subst h1
    simp only [List.mapM_cons] at h2
    obtain ⟨_, _, g⟩ := bind_some_left h2
    obtain ⟨_, _, g'⟩ := bind_some_left g
    cases g'
  | a :: l, [], zs, h1, h2 => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h2
    subst h2
    simp only [List.mapM_cons] at h1
    obtain ⟨_, _, g⟩ := bind_some_left h1
    obtain ⟨_, _, g'⟩ := bind_some_left g
    cases g'
  | a :: l, b :: l', zs, h1, h2 => by
    simp only [List.mapM_cons] at h1 h2
    obtain ⟨x, hx, g1⟩ := bind_some_left h1
    obtain ⟨xs, hxs, g2⟩ := bind_some_left g1
    obtain ⟨y, hy, g3⟩ := bind_some_left h2
    obtain ⟨ys, hys, g4⟩ := bind_some_left g3
    simp only [pure, Option.some.injEq] at g2 g4
    subst g2
    simp only [List.cons.injEq] at g4
    obtain ⟨rfl, rfl⟩ := g4
    rw [hf a b _ hx hy, mapM_inj hf hxs hys]

/-- `denoteN` at a well-formed store, as `mapM_inj` asks. -/
theorem denN_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (a b : NIdx) (z : ConLeche.Name), denoteN st.ns a = some z → denoteN st.ns b = some z → a = b := by
  intro a b z ha hb
  obtain ⟨rk, hrk⟩ := hwf
  exact ConRon.Arena.denoteN_inj hrk.nsWF ha hb

/-- `denoteE` at a well-formed store, as `mapM_inj` asks. -/
theorem denE_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (a b : EIdx) (z : Expr), denoteE st a = some z → denoteE st b = some z → a = b :=
  fun _ _ _ ha hb => ConRon.Arena.denoteE_inj hwf ha hb

/-- A kind's denotation keeps its constructor. -/
theorem kind_tag {st : EStore} {k : CKindF NIdx EIdx} {z : CKindF Name Expr}
    (h : k.mapM (denoteN st.ns) (denoteE st) = some z) : z.tag = k.tag := by
  cases k <;> simp only [CKindF.mapM] at h
  all_goals first
    | (simp only [pure, Option.some.injEq] at h; subst h; rfl)
    | (obtain ⟨_, _, g⟩ := bind_some_left h
       first
         | (simp only [pure, Option.some.injEq] at g; subst g; rfl)
         | (obtain ⟨_, _, g'⟩ := bind_some_left g
            simp only [pure, Option.some.injEq] at g'; subst g'; rfl))

/-- A recursor rule's denotation is injective. -/
theorem rule_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (a b : NIdx × Nat × EIdx) (z : Name × Nat × Expr),
      (do let c ← denoteN st.ns a.1; let e ← denoteE st a.2.2; pure (c, a.2.1, e)) = some z →
      (do let c ← denoteN st.ns b.1; let e ← denoteE st b.2.2; pure (c, b.2.1, e)) = some z →
      a = b := by
  rintro ⟨c, m, e⟩ ⟨c', m', e'⟩ z ha hb
  obtain ⟨x1, g1, ha⟩ := bind_some_left ha
  obtain ⟨x2, g2, ha⟩ := bind_some_left ha
  obtain ⟨y1, g1', hb⟩ := bind_some_left hb
  obtain ⟨y2, g2', hb⟩ := bind_some_left hb
  simp only [pure, Option.some.injEq] at ha hb
  subst ha
  simp only [Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl, rfl⟩ := hb
  rw [denN_inj hwf c c' _ g1 g1', denE_inj hwf e e' _ g2 g2']

/-- **A kind's denotation is injective** at a well-formed store. -/
theorem kind_inj {st : EStore} (hwf : StoreWF st) {k k' : CKindF NIdx EIdx} {z : CKindF Name Expr}
    (h : k.mapM (denoteN st.ns) (denoteE st) = some z)
    (h' : k'.mapM (denoteN st.ns) (denoteE st) = some z) : k = k' := by
  have hN := denN_inj hwf
  have hE := denE_inj hwf
  have ht : k.tag = k'.tag := (kind_tag h).symm.trans (kind_tag h')
  cases k <;> cases k' <;> (try simp [CKindF.tag] at ht) <;>
    simp only [CKindF.mapM] at h h'
  case ax.ax u u' =>
    simp only [pure, Option.some.injEq] at h h'; subst h; cases h'; rfl
  case quot.quot u u' =>
    simp only [pure, Option.some.injEq] at h h'; subst h; cases h'; rfl
  case defn.defn v hs sf v' hs' sf' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    simp only [pure, Option.some.injEq] at g g'; subst g; cases g'
    rw [hE v v' _ hx hy]
  case opaq.opaq v u v' u' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    simp only [pure, Option.some.injEq] at g g'; subst g; cases g'
    rw [hE v v' _ hx hy]
  case thm.thm v all v' all' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨xs, hxs, g1⟩ := bind_some_left g
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    obtain ⟨ys, hys, g1'⟩ := bind_some_left g'
    simp only [pure, Option.some.injEq] at g1 g1'; subst g1; cases g1'
    rw [hE v v' _ hx hy, mapM_inj hN hxs hys]
  case induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨xs, hxs, g1⟩ := bind_some_left g
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    obtain ⟨ys, hys, g1'⟩ := bind_some_left g'
    simp only [pure, Option.some.injEq] at g1 g1'; subst g1; cases g1'
    rw [mapM_inj hN hx hy, mapM_inj hN hxs hys]
  case ctor.ctor ind ci np nf iu ind' ci' np' nf' iu' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    simp only [pure, Option.some.injEq] at g g'; subst g; cases g'
    rw [hN ind ind' _ hx hy]
  case recur.recur all np ni nmo nmi rules kk iu all' np' ni' nmo' nmi' rules' kk' iu' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨xs, hxs, g1⟩ := bind_some_left g
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    obtain ⟨ys, hys, g1'⟩ := bind_some_left g'
    simp only [pure, Option.some.injEq] at g1 g1'; subst g1; cases g1'
    rw [mapM_inj hN hx hy, mapM_inj (rule_inj hwf) hxs hys]

/-- **A constant's denotation is injective** at a well-formed store. -/
theorem denoteEntry_inj {st : EStore} (hwf : StoreWF st) {a b : CEntryF NIdx EIdx}
    {z : CEntryF Name Expr} (ha : denoteEntry st a = some z) (hb : denoteEntry st b = some z) :
    a = b := by
  rcases a with ⟨n, l, t, k⟩
  rcases b with ⟨n', l', t', k'⟩
  simp only [denoteEntry, CEntryF.mapM] at ha hb
  obtain ⟨zn, h1, ga⟩ := bind_some_left ha
  obtain ⟨zl, h2, ga⟩ := bind_some_left ga
  obtain ⟨zt, h3, ga⟩ := bind_some_left ga
  obtain ⟨zk, h4, ga⟩ := bind_some_left ga
  obtain ⟨zn', h1', gb⟩ := bind_some_left hb
  obtain ⟨zl', h2', gb⟩ := bind_some_left gb
  obtain ⟨zt', h3', gb⟩ := bind_some_left gb
  obtain ⟨zk', h4', gb⟩ := bind_some_left gb
  simp only [pure, Option.some.injEq] at ga gb
  subst ga
  simp only [CEntryF.mk.injEq] at gb
  obtain ⟨rfl, rfl, rfl, rfl⟩ := gb
  rw [denN_inj hwf n n' _ h1 h1', mapM_inj (denN_inj hwf) h2 h2', denE_inj hwf t t' _ h3 h3',
    kind_inj hwf h4 h4']

/-- `hintsEq` is equality. -/
theorem hintsEq_iff (h h' : ConLeche.Frontend.HintsRec) :
    ConLeche.Frontend.Olean.hintsEq h h' = true ↔ h = h' := by
  cases h <;> cases h' <;> simp [ConLeche.Frontend.Olean.hintsEq]

/-- The twin's `rulesEq` is equality. -/
theorem rulesEqT_iff : ∀ (a b : List (NIdx × Nat × EIdx)),
    ConRon.Arena.Frontend.Olean.rulesEq a b = true ↔ a = b
  | [], [] => by simp [ConRon.Arena.Frontend.Olean.rulesEq]
  | [], _ :: _ => by simp [ConRon.Arena.Frontend.Olean.rulesEq]
  | _ :: _, [] => by simp [ConRon.Arena.Frontend.Olean.rulesEq]
  | (x, y, z) :: as, (x', y', z') :: bs => by
    simp [ConRon.Arena.Frontend.Olean.rulesEq, rulesEqT_iff as bs, and_assoc]

/-- Upstream's `rulesEq` is equality. -/
theorem rulesEqU_iff : ∀ (a b : List (Name × Nat × Expr)),
    ConLeche.Frontend.Olean.rulesEq a b = true ↔ a = b
  | [], [] => by simp [ConLeche.Frontend.Olean.rulesEq]
  | [], _ :: _ => by simp [ConLeche.Frontend.Olean.rulesEq]
  | _ :: _, [] => by simp [ConLeche.Frontend.Olean.rulesEq]
  | (x, y, z) :: as, (x', y', z') :: bs => by
    simp [ConLeche.Frontend.Olean.rulesEq, rulesEqU_iff as bs, and_assoc]

/-- The twin's `entrySame` is equality. -/
theorem entrySameT_iff (a b : CEntryF NIdx EIdx) :
    ConRon.Arena.Frontend.Olean.entrySame a b = true ↔ a = b := by
  rcases a with ⟨n, l, t, k⟩
  rcases b with ⟨n', l', t', k'⟩
  cases k <;> cases k' <;>
    simp [ConRon.Arena.Frontend.Olean.entrySame, hintsEq_iff, rulesEqT_iff, and_assoc]

/-- Upstream's `entrySame` is equality. -/
theorem entrySameU_iff (a b : CEntryF Name Expr) :
    ConLeche.Frontend.Olean.entrySame a b = true ↔ a = b := by
  rcases a with ⟨n, l, t, k⟩
  rcases b with ⟨n', l', t', k'⟩
  cases k <;> cases k' <;>
    simp [ConLeche.Frontend.Olean.entrySame, hintsEq_iff, rulesEqU_iff, and_assoc]

/-- A constant's denotation, field by field. -/
theorem denoteEntry_parts {st : EStore} {a : CEntryF NIdx EIdx} {z : CEntryF Name Expr}
    (h : denoteEntry st a = some z) :
    denoteN st.ns a.name = some z.name ∧ a.levelParams.mapM (denoteN st.ns) = some z.levelParams ∧
      denoteE st a.type = some z.type ∧ a.kind.mapM (denoteN st.ns) (denoteE st) = some z.kind := by
  rcases a with ⟨n, l, t, k⟩
  simp only [denoteEntry, CEntryF.mapM] at h
  obtain ⟨zn, h1, g⟩ := bind_some_left h
  obtain ⟨zl, h2, g⟩ := bind_some_left g
  obtain ⟨zt, h3, g⟩ := bind_some_left g
  obtain ⟨zk, h4, g⟩ := bind_some_left g
  simp only [pure, Option.some.injEq] at g
  subst g
  exact ⟨h1, h2, h3, h4⟩

/-- Two handles compare as their denotations, at a well-formed store. -/
theorem beq_den {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → Option β}
    (hf : ∀ a b z, f a = some z → f b = some z → a = b) {a b : α} {x y : β}
    (ha : f a = some x) (hb : f b = some y) : (a == b) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
  · rintro rfl; exact hf a b x ha hb

/-- A list's `mapM` compares as its denotation. -/
theorem beq_mapM {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → Option β}
    (hf : ∀ a b z, f a = some z → f b = some z → a = b) {a b : List α} {x y : List β}
    (ha : a.mapM f = some x) (hb : b.mapM f = some y) : (a == b) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
  · rintro rfl; exact mapM_inj hf ha hb

/-- **`expoOf` reads back**: the twin's verdict on two handle constants is upstream's on their
denotations, at a well-formed store. -/
theorem expoOf_den {st : EStore} (hwf : StoreWF st) {a b : CEntryF NIdx EIdx}
    {aC bC : CEntryF Name Expr} (ha : denoteEntry st a = some aC) (hb : denoteEntry st b = some bC) :
    ConRon.Arena.Frontend.Olean.expoOf a b = ConLeche.Frontend.Olean.expoOf aC bC := by
  have e1 : ConRon.Arena.Frontend.Olean.entrySame a b = ConLeche.Frontend.Olean.entrySame aC bC := by
    rw [Bool.eq_iff_iff, entrySameT_iff, entrySameU_iff]
    constructor
    · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
    · rintro rfl; exact denoteEntry_inj hwf ha hb
  obtain ⟨an, al, at', ak⟩ := denoteEntry_parts ha
  obtain ⟨bn, bl, bt, bk⟩ := denoteEntry_parts hb
  have e2 : (a.name == b.name) = (aC.name == bC.name) := beq_den (denN_inj hwf) an bn
  have e3 : (a.levelParams == b.levelParams) = (aC.levelParams == bC.levelParams) :=
    beq_mapM (denN_inj hwf) al bl
  have e4 : (a.type == b.type) = (aC.type == bC.type) := beq_den (denE_inj hwf) at' bt
  unfold ConRon.Arena.Frontend.Olean.expoOf ConLeche.Frontend.Olean.expoOf
  rw [e1, e2, e3, e4]
  rcases a with ⟨n1, l1, t1, k1⟩
  rcases b with ⟨n2, l2, t2, k2⟩
  rcases aC with ⟨n1', l1', t1', k1'⟩
  rcases bC with ⟨n2', l2', t2', k2'⟩
  simp only at ak bk ⊢
  cases k1 <;> cases k2 <;> simp only [CKindF.mapM] at ak bk <;>
    (repeat (first
      | (obtain ⟨_, _, ak⟩ := bind_some_left ak)
      | (obtain ⟨_, _, bk⟩ := bind_some_left bk))) <;>
    simp only [pure, Option.some.injEq] at ak bk <;> subst ak bk <;> rfl

/-! ## A constant read sparsely -/

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:244-248 sparseExprP — **an expression read
sparsely is the specification's**. -/
theorem sparseExprP_run {pk : OleanPins} {r : Region} {v : UInt64} {s s' : AState}
    (hok : StateOK s) (hpk : NullsRel s.store pk) {x : EIdx}
    (h : ConRon.Arena.Frontend.Olean.sparseExprP pk r v s = .ok (some x, s')) :
    ParseStep s s' ∧ ∃ e, exprP r v = some e ∧ denoteE s'.store x = some e := by
  unfold ConRon.Arena.Frontend.Olean.sparseExprP at h
  unfold exprP
  cases hc : r.loc v with
  | none => simp only [hc] at h; cases (AM.pure_ok h).1
  | some c =>
    simp only [hc] at h
    unfold ConRon.Arena.Frontend.Olean.frontierExpr at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    cases o with
    | none => cases (AM.pure_ok h2).1
    | some m =>
      obtain ⟨hx, rfl⟩ := AM.pure_ok h2
      obtain ⟨hst, hg, -, -⟩ := sGo_run c hok hpk (Or.inr (Or.inr (Or.inl rfl))) (SMGood.empty _ _)
        (FrontierGood.empty _ _) h1
      obtain ⟨e, h3, h4⟩ := lookup_good hg.exprs (FrontierGood.empty _ r).exprs hx.symm
      exact ⟨hst, e, h3, h4⟩

/-- An expression read in `OptionT AM`, upstream's, read back. -/
theorem exprs_run {pk : OleanPins} {fe : UInt64 → AM (Option EIdx)} {ge : UInt64 → Option Expr}
    (hstep : ∀ a s s' y, Ctx pk s → fe a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, ge a = some z ∧ denoteE s'.store y = some z)
    (v : UInt64) {y : EIdx} {s s' : AState} (hctx : Ctx pk s)
    (h : (OptionT.mk (fe v) : OptionT AM EIdx) s = .ok (some y, s')) :
    ParseStep s s' ∧ ∃ z, ge v = some z ∧ denoteE s'.store y = some z :=
  hstep v s s' y hctx h

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:275-296 CKindF.mapM — **a kind read in
`OptionT AM`**, upstream's, read back. -/
theorem kindMap_run {pk : OleanPins} {fn : UInt64 → AM (Option NIdx)} {fe : UInt64 → AM (Option EIdx)}
    {gn : UInt64 → Option ConLeche.Name} {ge : UInt64 → Option Expr}
    (hn : ∀ a s s' y, Ctx pk s → fn a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, gn a = some z ∧ denoteN s'.store.ns y = some z)
    (he : ∀ a s s' y, Ctx pk s → fe a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, ge a = some z ∧ denoteE s'.store y = some z)
    (k : CKindF UInt64 UInt64) {kr : CKindF NIdx EIdx} {s s' : AState} (hctx : Ctx pk s)
    (h : (k.mapM (m := OptionT AM) (fun v => OptionT.mk (fn v)) (fun v => OptionT.mk (fe v))) s
      = .ok (some kr, s')) :
    ParseStep s s' ∧ ∃ kC, k.mapM gn ge = some kC ∧
      kr.mapM (denoteN s'.store.ns) (denoteE s'.store) = some kC := by
  cases k with
  | ax u =>
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | quot u =>
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | defn v hh sf =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := he v s _ a hctx h1
    refine ⟨hst, .defn z hh sf, ?_, ?_⟩
    · simp [CKindF.mapM, hz, bind, Option.bind, pure]
    · simp [CKindF.mapM, hd, bind, Option.bind, pure]
  | opaq v u =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := he v s _ a hctx h1
    refine ⟨hst, .opaq z u, ?_, ?_⟩
    · simp [CKindF.mapM, hz, bind, Option.bind, pure]
    · simp [CKindF.mapM, hd, bind, Option.bind, pure]
  | thm v all =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨ns, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, z, hz, hd⟩ := he v s _ a hctx h1
    obtain ⟨hst2, zs, hzs, hds⟩ := names_run hn all (hctx.step hst1) h3
    refine ⟨hst1.trans hst2, .thm z zs, ?_, ?_⟩
    · simp [CKindF.mapM, hz, hzs, bind, Option.bind, pure]
    · simp [CKindF.mapM, denote_ext hd hst2.ext, hds, bind, Option.bind, pure]
  | induct np ni all cs nn ir iu irf =>
    simp only [CKindF.mapM] at h
    obtain ⟨as, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨bs, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, zs, hz, hd⟩ := names_run hn all hctx h1
    obtain ⟨hst2, ws, hw, hdw⟩ := names_run hn cs (hctx.step hst1) h3
    refine ⟨hst1.trans hst2, .induct np ni zs ws nn ir iu irf, ?_, ?_⟩
    · simp [CKindF.mapM, hz, hw, bind, Option.bind, pure]
    · have hd' := mapM_denoteN_ext hst2.ext hd
      simp [CKindF.mapM, hd', hdw, bind, Option.bind, pure]
  | ctor ind ci np nf iu =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := hn ind s _ a hctx h1
    refine ⟨hst, .ctor z ci np nf iu, ?_, ?_⟩
    · simp [CKindF.mapM, hz, bind, Option.bind, pure]
    · simp [CKindF.mapM, hd, bind, Option.bind, pure]
  | recur all np ni nmo nmi rules kk iu =>
    rw [recur_mapM] at h ⊢
    obtain ⟨as, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rs, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, zs, hz, hd⟩ := names_run hn all hctx h1
    obtain ⟨hst2, ws, hw, hdw⟩ := optT_list_run (pk := pk)
      (den := fun st (x : NIdx × Nat × EIdx) => do
        let c ← denoteN st.ns x.1
        let e ← denoteE st x.2.2
        pure (c, x.2.1, e))
      (g := fun (x : UInt64 × Nat × UInt64) => do
        let c ← gn x.1
        let e ← ge x.2.2
        pure (c, x.2.1, e))
      (fun {st st' y z} hx hy => by
        obtain ⟨c, hc, hy⟩ := bind_some_left hy
        obtain ⟨e, he', hy⟩ := bind_some_left hy
        simp only [denoteN_ext hc hx, denote_ext he' hx]
        exact hy)
      (fun x s s' y hctx hrun => by
        obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok hrun
        obtain ⟨b, s₂, h3, h4⟩ := OT.bind_ok h2
        obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
        obtain ⟨hst1, z, hz, hd⟩ := hn x.1 s _ a hctx h1
        obtain ⟨hst2, w, hw', hdw'⟩ := he x.2.2 s₁ _ b (hctx.step hst1) h3
        exact ⟨hst1.trans hst2, (z, x.2.1, w), by simp [hz, hw', bind, Option.bind, pure],
          by simp [denoteN_ext hd hst2.ext, hdw', bind, Option.bind, pure]⟩) rules (hctx.step hst1) h3
    refine ⟨hst1.trans hst2, .recur zs np ni nmo nmi ws kk iu, ?_, ?_⟩
    · rw [hz, hw]; rfl
    · have hd' := mapM_denoteN_ext hst2.ext hd
      rw [recur_mapM, hd', hdw]; rfl

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:298-305 CEntryF.mapM — **a constant read in
`OptionT AM`**, upstream's, read back. -/
theorem entryMapRd_run {pk : OleanPins} {rd : ConRon.Arena.Frontend.Olean.PtrRead}
    {gn : UInt64 → Option ConLeche.Name} {ge : UInt64 → Option Expr}
    (hn : ∀ a s s' y, Ctx pk s → rd.rdName a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, gn a = some z ∧ denoteN s'.store.ns y = some z)
    (he : ∀ a s s' y, Ctx pk s → rd.rdExpr a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, ge a = some z ∧ denoteE s'.store y = some z)
    (c : CEntryF UInt64 UInt64) {e : CEntryF NIdx EIdx} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.entryMap rd c s = .ok (some e, s')) :
    ParseStep s s' ∧ ∃ z, c.mapM gn ge = some z ∧ denoteEntry s'.store e = some z := by
  unfold ConRon.Arena.Frontend.Olean.entryMap at h
  rcases c with ⟨name, lps, type, kind⟩
  have h' : (CEntryF.mapM (m := OptionT AM) (fun v => OptionT.mk (rd.rdName v))
      (fun v => OptionT.mk (rd.rdExpr v)) ⟨name, lps, type, kind⟩) s = .ok (some e, s') := h
  simp only [CEntryF.mapM] at h'
  obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h'
  obtain ⟨ls, s₂, h3, h4⟩ := OT.bind_ok h2
  obtain ⟨t, s₃, h5, h6⟩ := OT.bind_ok h4
  obtain ⟨k, s₄, h7, h8⟩ := OT.bind_ok h6
  obtain ⟨rfl, rfl⟩ := OT.pure_ok h8
  obtain ⟨hst1, zn, hzn, hdn⟩ := hn name s _ a hctx h1
  obtain ⟨hst2, zl, hzl, hdl⟩ := names_run hn lps (hctx.step hst1) h3
  obtain ⟨hst3, zt, hzt, hdt⟩ := he type s₂ _ t (hctx.step (hst1.trans hst2)) h5
  obtain ⟨hst4, zk, hzk, hdk⟩ := kindMap_run hn he kind (hctx.step ((hst1.trans hst2).trans hst3)) h7
  refine ⟨((hst1.trans hst2).trans hst3).trans hst4, ⟨zn, zl, zt, zk⟩, ?_, ?_⟩
  · simp [CEntryF.mapM, hzn, hzl, hzt, hzk, bind, Option.bind, pure]
  · have x1 := denoteN_ext hdn ((hst2.trans hst3).trans hst4).ext
    have x2 := mapM_denoteN_ext (hst3.trans hst4).ext hdl
    have x3 := denote_ext hdt hst4.ext
    simp [denoteEntry, CEntryF.mapM, x1, x2, x3, hdk, bind, Option.bind, pure]

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:82-84 entryAt — **a constant read sparsely is
the specification's** (`entryAt_eq`). -/
theorem entryAt_run {pk : OleanPins} {r : Region} {c : Nat} {e : CEntryF NIdx EIdx} {s s' : AState}
    (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.entryAt pk r c s = .ok (some e, s')) :
    ParseStep s s' ∧ ∃ z, ConLeche.Frontend.Olean.entryAt r c = some z ∧ denoteEntry s'.store e = some z := by
  unfold ConRon.Arena.Frontend.Olean.entryAt at h
  rw [ConLeche.Frontend.Olean.entryAt_eq]
  unfold constSpec
  cases hsk : constSkel r c with
  | none => simp only [hsk] at h; cases (AM.pure_ok h).1
  | some sk =>
    simp only [hsk] at h
    obtain ⟨u, s₁, h1, h2⟩ := AM.bind_ok h
    have := skelFits_run h1
    subst this
    unfold ConRon.Arena.Frontend.Olean.sparseEntry at h2
    obtain ⟨hst, z, hz, hd⟩ := entryMapRd_run (gn := nameP r) (ge := exprP r)
      (fun a s s' y hctx hrun => sparseNameP_run hctx.ok hctx.nulls hrun)
      (fun a s s' y hctx hrun => sparseExprP_run hctx.ok hctx.nulls hrun) sk hctx h2
    exact ⟨hst, z, by simpa [bind, Option.bind] using hz, hd⟩

/-! ## The load -/

/-- A lazy load related position by position is a lazy load. -/
theorem lazyOf_of_rel {r : Region} {i : Nat} :
    ∀ {ss : List (CEntryF UInt64 UInt64)} {es : List ConLeche.Frontend.Olean.CEntry},
      ListRel (fun sk e => ConLeche.Frontend.Olean.lazyEntry (nameP r) (exprP r) r i sk =
        some e.toCEntryF) ss es → ConLeche.Frontend.Olean.LazyOf r i ss es
  | [], [], .nil => ⟨by simp, by simp⟩
  | _ :: _, _ :: _, .cons hh ht =>
    let ih := lazyOf_of_rel ht
    ⟨fun s0 hs0 => by
      rcases List.mem_cons.mp hs0 with rfl | hs0
      · exact ⟨_, List.mem_cons_self, hh⟩
      · obtain ⟨x, hx, h⟩ := ih.of_skel s0 hs0
        exact ⟨x, List.mem_cons_of_mem _ hx, h⟩,
     fun e0 he0 => by
      rcases List.mem_cons.mp he0 with rfl | he0
      · exact ⟨_, List.mem_cons_self, hh⟩
      · obtain ⟨x, hx, h⟩ := ih.to_skel e0 he0
        exact ⟨x, List.mem_cons_of_mem _ hx, h⟩⟩

/-- A relation position by position, at each position. -/
theorem listRel_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, ListRel R l l' →
      ∃ hl : l'.length = l.length, ∀ (j : Nat) (hj : j < l.length), R l[j] (l'[j]'(hl ▸ hj))
  | [], [], .nil => ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | _ :: _, _ :: _, .cons hh ht => by
    obtain ⟨hl, hk⟩ := listRel_getElem ht
    refine ⟨by simp [hl], fun j hj => ?_⟩
    cases j with
    | zero => exact hh
    | succ j => exact hk j (by simpa using hj)

/-- con-leche: ConLeche/Verify/Driver/Loads.lean:950 loadAt_loadOf — **the twin's load of the
home is a load by the specification** (`LoadOf`). -/
theorem loadView_run {pk : OleanPins} {m : NIdx} {mn : ConLeche.Name} {f : ModFiles}
    {l : ConRon.Arena.Frontend.Olean.Loaded} {s s' : AState}
    (hctx : Ctx pk s) (hp : PinsRel s.store pk) (hm : denoteN s.store.ns m = some mn)
    (h : ConRon.Arena.Frontend.Olean.loadView pk 0 m f s = .ok (l, s')) :
    ParseStep s s' ∧ ∃ lC, LoadedRel s'.store l lC ∧ ConLeche.Driver.LoadOf 0 mn f lC := by
  unfold ConRon.Arena.Frontend.Olean.loadView at h
  obtain ⟨o, s₄, h7, h8⟩ := AM.bind_ok h
  cases o with
  | none =>
    obtain ⟨e, s₅, -, h9⟩ := AM.bind_ok h8
    obtain ⟨e', s₆, -, h10⟩ := AM.bind_ok h9
    exact absurd (AM.fail_ok h10) (by simp)
  | some l'' =>
  obtain ⟨hv, hs⟩ := AM.pure_ok h8
  cases hv
  subst hs
  obtain ⟨hst, -, lC, hrel, hn, -, hfr, r, a, sk, skels, hvr, hcno, hsk, hskels, hal, imports,
    himps, hpre⟩ := loadAt_runOf hctx hp hm h7
  obtain ⟨hl, hk⟩ := listRel_getElem hal
  refine ⟨hst, lC, hrel, ⟨r, a, sk, skels, hvr, hcno, hsk, hskels, hn, ?_, lazyOf_of_rel hal⟩,
    ⟨r, a, sk, skels, hvr, hsk, hskels, by simpa using hl, fun j hj => ?_⟩,
    r, a, sk, imports, hvr, hsk, himps, hpre⟩
  · rw [hfr]; exact ConLeche.Frontend.Olean.Frontier.good_empty r
  · have := hk j hj
    simpa using this

/-! ## The exported level of the private constants -/

open ConLeche.Frontend.Olean (Expo)

/-- Two position indexes built over the same positions answer alike at keys that agree. -/
theorem foldIdx_get {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [BEq β] [Hashable β]
    [LawfulBEq β] {x : α} {y : β} :
    ∀ (n m : Nat) (hnm : n = m) (kT : (i : Nat) → i < n → α) (kU : (i : Nat) → i < m → β),
      (∀ i (h1 : i < n) (h2 : i < m), kT i h1 = x ↔ kU i h2 = y) →
      (n.fold (fun i h (acc : Std.HashMap α Nat) => acc.insert (kT i h) i) {})[x]? =
        (m.fold (fun i h (acc : Std.HashMap β Nat) => acc.insert (kU i h) i) {})[y]? := by
  intro n m hnm
  cases hnm
  induction n with
  | zero => intro _ _ _; simp
  | succ n ih =>
    intro kT kU hk
    rw [Nat.fold_succ, Nat.fold_succ, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
    have e := hk n (by omega) (by omega)
    by_cases h1 : kT n (by omega) = x
    · have h2 := e.mp h1
      simp [h1, h2]
    · have h2 : ¬ kU n (by omega) = y := fun h => h1 (e.mpr h)
      simp only [beq_iff_eq, h1, h2, ↓reduceIte]
      exact ih _ _ (fun i a b => hk i (by omega) (by omega))

/-- An array's `mapM`, at each position. -/
theorem mapM_getElem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {zs : List β}, l.mapM f = some zs →
      ∃ hl : zs.length = l.length, ∀ (j : Nat) (hj : j < l.length), f l[j] = some (zs[j]'(hl ▸ hj))
  | [], zs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | a :: l, zs, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨z, hz, g⟩ := bind_some_left h
    obtain ⟨zs', hzs, g⟩ := bind_some_left g
    simp only [pure, Option.some.injEq] at g
    subst g
    obtain ⟨hl, hk⟩ := mapM_getElem hzs
    refine ⟨by simp [hl], fun j hj => ?_⟩
    cases j with
    | zero => exact hz
    | succ j => exact hk j (by simpa using hj)

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:106-152 expoOfParts — **the twin's loop over
the exported constants is upstream's `for`**, step by step. -/
theorem expoLoop_run {pk : OleanPins} {r : Region} {privLoc : Std.HashMap Nat Nat}
    {privIdx : Std.HashMap NIdx Nat} {privLocs : Array Nat} {cs : Array (CEntryF NIdx EIdx)}
    {f : Nat → Array Expo → Except String (ForInStep (Array Expo))} :
    ∀ (l : List Nat),
      (∀ c ∈ l, ∀ i expo, privLoc[c]? = some i → f c expo = .ok (.yield (expo.set! i .same))) →
      (∀ c ∈ l, privLoc[c]? = none → ∀ expo s s₁ expo₁, Ctx pk s →
        ConRon.Arena.Frontend.Olean.expoStep pk r privIdx privLocs cs expo c s =
          .ok (.ok expo₁, s₁) → ParseStep s s₁ ∧ f c expo = .ok (.yield expo₁)) →
      ∀ expo {s s' : AState} {e : Array Expo}, Ctx pk s →
        ConRon.Arena.Frontend.Olean.expoLoop pk r privLoc privIdx privLocs cs l expo s =
          .ok (.ok e, s') →
        ParseStep s s' ∧ forIn l expo f = .ok e
  | [], _, _, expo, s, s', e, hctx, h => by
    rw [ConRon.Arena.Frontend.Olean.expoLoop] at h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    cases hv
    exact ⟨ParseStep.refl hctx.ok, rfl⟩
  | c :: l, hsame, hstep, expo, s, s', e, hctx, h => by
    rw [ConRon.Arena.Frontend.Olean.expoLoop] at h
    rw [List.forIn_cons]
    cases hp : privLoc[c]? with
    | some i =>
      simp only [hp] at h
      obtain ⟨hst, hl⟩ := expoLoop_run l (fun c' hc' => hsame c' (List.mem_cons_of_mem _ hc'))
        (fun c' hc' => hstep c' (List.mem_cons_of_mem _ hc')) _ hctx h
      refine ⟨hst, ?_⟩
      rw [hsame c List.mem_cons_self i expo hp]
      exact hl
    | none =>
      simp only [hp] at h
      obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
      cases o with
      | error m => cases (AM.pure_ok h2).1
      | ok expo₁ =>
        simp only at h2
        obtain ⟨hst1, hf⟩ := hstep c List.mem_cons_self hp expo s s₁ expo₁ hctx h1
        obtain ⟨hst2, hl⟩ := expoLoop_run l (fun c' hc' => hsame c' (List.mem_cons_of_mem _ hc'))
          (fun c' hc' => hstep c' (List.mem_cons_of_mem _ hc')) _ (hctx.step hst1) h2
        refine ⟨hst1.trans hst2, ?_⟩
        rw [hf]
        exact hl

end ConRon.Bridge.Modular.Home
