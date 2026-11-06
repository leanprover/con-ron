/-
# `ConRon.Bridge.Frontend.Olean.Records` — **Theorem 1 for the `.olean` reader**

`readOleans_run`: on the record `modelFs F` of a snapshot `F`, where the twin's whole read
answers, its records denote a stream `ds`, and a theorem of the private view of a module of the
closure is among them, with its statement; its value is the reference the check reads.  It is
upstream's `readOleans_thm` (`Verify/Frontend/Olean/Files.lean`), re-run over the lemmas it rests
on: upstream's `readOleans_ok` states its `Loaded`s through upstream's `loadAt`, whose `usesOf`
and `frontierWalk` are `partial`, so it cannot speak of the twin's `uses` or frontier;
`loadAt_spec`'s `LazyOf` (`Closure.lean`'s `loadAt_run`), `mergeAll_ok`, `blocksOk_good`,
`declsOf_thm` hold of any `Merged`, and nothing of the emission reads what `uses` holds.

The records are built by the stream parser's own `processLineCoreD`, so `Lines.lean`'s theorem
about it is what relates them, and upstream's `declOfF` over the emitter's tables is that function
over a `StateD` whose tables are the emitter's.
-/
module

public import ConRon.Arena.Frontend.Olean.Records
public import ConRon.Bridge.Frontend.Olean.Blocks
public import ConLeche.Frontend.Olean.Records
public import ConLeche.Verify.Frontend.Olean.Files
public import ConLeche.Verify.Frontend.Olean.Emit
public import ConRon.Bridge.Frontend.Prepare

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Merged CEntry Emit Work emitAll declsGo declsOf)
open ConLeche.Frontend (DeclRec)
open ConLeche.Frontend.Olean (CEntryF CKindF SearchPath InClosure ViewOf bind_some_left)

/-! ## The emission -/

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:357-359 emitAll -/
theorem emitAll_run {pk : OleanPins} {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    {s : AState} (hc : WalkCtx s.store mg mgC) (hp : PinsRel s.store pk) {cs : Array NIdx}
    {csC : Array ConLeche.Name} (hcs : ListRel (NR s.store) cs.toList csC.toList) {em : Emit}
    {s' : AState} (h : emitAll pk mg cs s = .ok (em, s')) :
    s' = s ∧ EmitRel s.store em (ConLeche.Frontend.Olean.emitAll mgC csC) := by
  unfold emitAll at h
  exact emitLoop_run hc hp (recMapOf_rel hc) _ _ _ _ _ (visits_rel hcs) (EmitRel.empty _) h

/-! ## The records -/

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:47-55 declsGo — the parse state over the
emitter's tables, `acc` the records so far. -/
@[expose] def scOf (emC : ConLeche.Frontend.Olean.Emit) (acc : Array Declaration) :
    ConLeche.Frontend.StateD :=
  { names := { dense := emC.names }, levels := {}, exprs := { dense := emC.exprs }, decls := acc }

/-- A dense table against a dense table. -/
theorem denseTable_rel {α β : Type} {R : α → β → Prop} {a : Array α} {b : Array β}
    (h : ListRel R a.toList b.toList) :
    IdTableRel R { dense := a } { dense := b } := by
  intro i
  have hsz := array_size_of_rel h
  simp only [ConLeche.Frontend.IdTable.get?]
  by_cases hi : i < a.size
  · have hi' : i < b.size := by omega
    simp only [hi, hi', dite_true]
    obtain ⟨hj, hr⟩ := listRel_get h (i := i) (by simpa using hi)
    simp only [Array.getElem_toList] at hr
    exact hr
  · have hi' : ¬ i < b.size := by omega
    simp only [hi, hi', dite_false]
    simp [OptRel]

theorem declOfF_scOf (emC : ConLeche.Frontend.Olean.Emit) (acc : Array Declaration) (r : DeclRec) :
    ConLeche.Frontend.declOf (scOf emC acc).lk r =
      ConLeche.Frontend.declOfF emC.nm emC.lv emC.ex r := by
  have hn : (scOf emC acc).name = emC.nm := by
    funext i
    simp only [ConLeche.Frontend.StateD.name, ConLeche.Frontend.Olean.Emit.nm, scOf,
      ConLeche.Frontend.IdTable.get?]
    by_cases hi : i < emC.names.size
    · simp [hi]
    · simp [hi]
  have he : (scOf emC acc).expr = emC.ex := by
    funext i
    simp only [ConLeche.Frontend.StateD.expr, ConLeche.Frontend.Olean.Emit.ex, scOf,
      ConLeche.Frontend.IdTable.get?]
    by_cases hi : i < emC.exprs.size
    · simp [hi]
    · simp [hi]
  show ConLeche.Frontend.declOfF (scOf emC acc).name (scOf emC acc).level (scOf emC acc).expr r = _
  rw [hn, he]
  rfl

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:47-55 declsGo -/
theorem declsGo_run {emC : ConLeche.Frontend.Olean.Emit} :
    ∀ (rs : List DeclRec) (k : Nat) (sd sdF : StateD) (acc : Array Declaration) {s s' : AState},
      StateOK s → s.store.scratchOn = false → PinsOK s → StateDRel s.store sd (scOf emC acc) →
      PersStateD sd → declsGo k rs sd s = .ok (.ok sdF, s') →
      ParseStep s s' ∧ PersStateD sdF ∧ ∃ ds, ConLeche.Frontend.Olean.declsGo emC k rs acc = .ok ds ∧
        denoteDeclArray s'.store sdF.decls = some ds
  | [], k, sd, sdF, acc, s, s', hok, _, _, hrel, hp, h => by
    rw [declsGo] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    exact ⟨ParseStep.refl hok, hp, acc, rfl, hrel.decls⟩
  | r :: rs, k, sd, sdF, acc, s, s', hok, hoff, hpins, hrel, hp, h => by
    rw [declsGo] at h
    obtain ⟨x, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hst, hpx, y, hy, hsum⟩ := processLineCoreD_run hok hoff hpins hrel hp h1
    cases x with
    | inr v => cases (AM.pure_ok h2).1
    | inl sd' =>
      obtain ⟨sc', rfl, hrel'⟩ := hsum.inl_left rfl
      simp only [ConLeche.Frontend.processLineCoreD] at hy
      rw [declOfF_scOf] at hy
      rw [ConLeche.Frontend.Olean.declsGo]
      cases hd : ConLeche.Frontend.declOfF emC.nm emC.lv emC.ex r with
      | error e =>
        rw [hd] at hy
        cases hy
      | ok o =>
        rw [hd] at hy
        cases o with
        | inr v => cases hy
        | inl d =>
          have hy' : (Except.ok (.inl (ConLeche.Frontend.pushDecl (scOf emC acc) d)) :
              Except String (ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict)) = .ok (.inl sc') := hy
          injection hy' with hy1
          injection hy1 with hy2
          have hsc : sc' = scOf emC (acc.push d) := hy2.symm
          subst hsc
          obtain ⟨hst2, hpf, ds, hds, hden⟩ := declsGo_run rs (k + 1) _ _ _ hst.ok
            (by rw [hst.scratch]; exact hoff) (hpins.mono hst.ext hst.pins) hrel' (hpx _ rfl) h2
          exact ⟨hst.trans hst2, hpf, ds, hds, hden⟩

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:57-61 declsOf -/
theorem declsOf_run {em : Emit} {emC : ConLeche.Frontend.Olean.Emit} {r : ParseResultD}
    {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false) (hpins : PinsOK s)
    (hrel : EmitRel s.store em emC)
    (h : declsOf em s = .ok (.ok r, s')) :
    ParseStep s s' ∧ PersParseResult r ∧ ∃ ds, ConLeche.Frontend.Olean.declsOf emC = .ok ds ∧
      denoteDeclArray s'.store r.decls = some ds := by
  unfold declsOf at h
  obtain ⟨x, s₁, h1, h2⟩ := AM.bind_ok h
  cases x with
  | error e => cases (AM.pure_ok h2).1
  | ok sdF =>
    obtain ⟨hv, hs⟩ := AM.pure_ok h2
    cases hv
    subst hs
    have hsr : StateDRel s.store { names := { dense := em.names }, levels := {}, exprs := { dense := em.exprs } }
        (scOf emC #[]) :=
      { names := denseTable_rel hrel.names
        levels := fun i => by simp [ConLeche.Frontend.IdTable.get?, scOf, OptRel]
        exprs := denseTable_rel hrel.exprs
        decls := denoteDeclArray_empty _ }
    have hps : PersStateD { names := { dense := em.names }, levels := {}, exprs := { dense := em.exprs } } :=
      { names := fun i h hg => by
          obtain ⟨z, -, hz⟩ := OptRel.some_left (hsr.names i) hg
          exact PersN_of_denote hok.wf hoff hz
        levels := fun i l hg => by simp [ConLeche.Frontend.IdTable.get?] at hg
        exprs := fun i e hg => by
          obtain ⟨z, -, hz⟩ := OptRel.some_left (hsr.exprs i) hg
          exact PersE_of_denote hok.wf hoff hz
        decls := fun d hd => by simp at hd }
    obtain ⟨hst, hp, ds, hds, hden⟩ := declsGo_run _ 0 _ sdF #[] hok hoff hpins hsr hps
      (by rw [hrel.out] at h1; exact h1)
    exact ⟨hst, hp.decls, ds, hds, hden⟩

/-! ## What a record mentions -/

/-- con-leche: ConLeche/Driver/CheckMain.lean:102-104 usedOf — upstream's side of the twin's
`OleanRead.usedOf`, over a merged map: a theorem's record mentions what its stored constant's
load read off the file, any other record what its expressions mention. -/
@[expose] def usedOfC (mgC : ConLeche.Frontend.Olean.Merged) (d : Declaration) :
    Array ConLeche.Name :=
  match d with
  | .thmDecl cv _ => (mgC.map[cv.name]?.map (·.uses)).getD d.usedConsts
  | _ => d.usedConsts

/-- con-leche: none — `denoteNList` is the `mapM` of `denoteN`. -/
theorem denoteNList_eq_mapM (st : NStore) :
    ∀ (l : List NIdx), denoteNList st l = l.mapM (denoteN st)
  | [] => rfl
  | h :: hs => by
    simp only [denoteNList, List.mapM_cons, denoteNList_eq_mapM st hs]
    cases denoteN st h <;> cases hs.mapM (denoteN st) <;> rfl

/-- The reads of a merge do not look at a module's frontier. -/
theorem MergedRel.strip {st : EStore} {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged}
    (h : MergedRel st mg mgC) :
    MergedRel st { mg with ls := mg.ls.map fun l => { l with frontier := {} } } mgC := by
  have hget : ∀ n, ({ mg with ls := mg.ls.map fun l => { l with frontier := {} } } : Merged).get n
      = mg.get n := by
    intro n
    simp only [Merged.get, Array.getElem?_map, Option.bind_map]
    rfl
  exact ⟨fun hdn hx => h.got hdn (by rw [← hget]; exact hx),
    fun hdn hx => h.absent hdn (by rw [← hget]; exact hx), h.contains, h.order, h.keys, h.keysC⟩

/-- con-leche: ConLeche/Driver/CheckMain.lean:102-104 usedOf — **what the twin's `usedOf` says
of a record is what upstream's says**, on a store that extends the merge's: a theorem's record
through the merged map (`MergedRel`; its keys denote on both sides), any other through
`usedConsts_run`. -/
theorem usedRel_usedOf {st0 : EStore} {rd : ConRon.Arena.Frontend.Olean.OleanRead}
    {mgC : ConLeche.Frontend.Olean.Merged} (hm : MergedRel st0 rd.merged mgC) :
    UsedRel st0 rd.usedOf (usedOfC mgC) := by
  intro s s' d dP ns hx hok hoff hd hrun
  have hw := nsWF_of_StateOK hok
  have hother : ConRon.Arena.Frontend.Olean.OleanRead.thmUses rd d = none →
      ConLeche.Declaration.usedConsts dP = usedOfC mgC dP →
      ParseStep s s' ∧ denoteNList s'.store.ns ns.toList = some (usedOfC mgC dP).toList := by
    intro hu he
    simp only [ConRon.Arena.Frontend.Olean.OleanRead.usedOf, hu] at hrun
    rw [← he]
    exact usedConsts_run hok hoff hd hrun
  cases d with
  | thmDecl cv v =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hcv : ConRon.Arena.Frontend.denoteCV s.store cv with
    | none => simp [hcv] at hd
    | some cvP =>
    cases he : denoteE s.store v with
    | none => simp [hcv, he] at hd
    | some vP =>
    simp only [hcv, he, Option.some.injEq] at hd
    subst hd
    have hname := denoteCV_name hcv
    cases hg : rd.merged.get cv.name with
    | none =>
      have habs : mgC.map[cvP.name]? = none := by
        cases hc : mgC.map[cvP.name]? with
        | none => rfl
        | some z =>
          obtain ⟨n0, hd0, hc0⟩ := hm.keysC hc
          obtain rfl : n0 = cv.name := denoteN_inj hw (denoteN_ext hd0 hx) hname
          rw [hm.absent hd0 hg] at hc
          cases hc
      refine hother (by simp [ConRon.Arena.Frontend.Olean.OleanRead.thmUses, hg]) ?_
      simp [usedOfC, habs]
    | some c =>
      simp only [ConRon.Arena.Frontend.Olean.OleanRead.usedOf,
        ConRon.Arena.Frontend.Olean.OleanRead.thmUses, hg, Option.map_some] at hrun
      obtain ⟨hv, rfl⟩ := AM.pure_ok hrun
      subst hv
      have hkey : ∃ p, rd.merged.map[cv.name]? = some p := by
        simp only [Merged.get] at hg
        split at hg
        · cases hg
        · exact ⟨_, by assumption⟩
      obtain ⟨p, hp⟩ := hkey
      obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp (hm.keys hp)
      obtain rfl : n0 = cvP.name :=
        Option.some.inj ((denoteN_ext hn0 hx).symm.trans hname)
      obtain ⟨cC, hcC, hdc⟩ := hm.got hn0 hg
      unfold denoteCEntry at hdc
      obtain ⟨e, -, hdc⟩ := ConLeche.Frontend.Olean.bind_some_left hdc
      obtain ⟨u, hu, hdc⟩ := ConLeche.Frontend.Olean.bind_some_left hdc
      simp only [pure, Option.some.injEq] at hdc
      subst hdc
      refine ⟨ParseStep.refl hok, ?_⟩
      simp only [usedOfC, hcC, Option.map_some, Option.getD_some, List.toList_toArray]
      rw [denoteNList_eq_mapM]
      exact list_mono (fun _ _ hy => denoteN_ext hy hx) _ hu
  | _ =>
    exact hother rfl (by
      first
      | (simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
         obtain ⟨_, -, rfl⟩ := hd; rfl)
      | (simp only [ConRon.Arena.Frontend.denoteDecl] at hd
         split at hd <;> simp at hd
         subst hd; rfl))

/-! ## The values' references -/

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:76-79 ModRef — **what a theorem's check needs
of the closure's modules, on both sides**: the module's name, and a frontier good on the region of
its files on the snapshot.  Upstream's `ValueAt` reads `valuesP`. -/
@[expose] def ValuesRel (sp : SearchPath) (F : FS) (st : EStore)
    (values : Array ConRon.Arena.Frontend.Olean.ModRef)
    (valuesP : Array ConLeche.Frontend.Olean.ModRef) : Prop :=
  ListRel (fun md mdP => denoteN st.ns md.name = some mdP.name ∧
      ∃ f, (ConLeche.Frontend.Olean.readFiles sp mdP.name .private : ModelIO _) F (.ok (.ok f)) ∧
        FrontGoodAt st f md.frontier)
    values.toList valuesP.toList

theorem valuesRel_of_loads {sp : SearchPath} {F : FS} {st : EStore} :
    ∀ {ls : List ConRon.Arena.Frontend.Olean.Loaded} {lsC : List ConLeche.Frontend.Olean.Loaded},
      ListRel (LoadedRel st) ls lsC → ListRel (ModFront sp F st) ls lsC →
      ListRel (fun (md : ConRon.Arena.Frontend.Olean.ModRef) (mdP : ConLeche.Frontend.Olean.ModRef) =>
          denoteN st.ns md.name = some mdP.name ∧
          ∃ f, (ConLeche.Frontend.Olean.readFiles sp mdP.name .private : ModelIO _) F (.ok (.ok f)) ∧
            FrontGoodAt st f md.frontier)
        (ls.map fun l => ⟨l.name, l.frontier⟩) (lsC.map fun l => ⟨l.name, l.frontier⟩)
  | _, _, .nil, .nil => .nil
  | _, _, .cons a h1, .cons b h2 => .cons ⟨a.name, b⟩ (valuesRel_of_loads h1 h2)

/-- con-leche: ConLeche/Verify/Frontend/Olean/Files.lean:835 readOleans_filled — **a theorem's
record, with its value in place, is the specification's constant**: the reference in a record
stands, on the snapshot, for the value of the theorem the specification reads off the files of
the reference's module (`constSpec`), and the record's statement is that theorem's.  Upstream's
proof, over the loads `loadClosure_run` gives (`LoadSpec`) and the values they make. -/
theorem filled_of {sp : SearchPath} {F : FS} {orderC : Array ConLeche.Name}
    {lsC : List ConLeche.Frontend.Olean.Loaded} {mgC : ConLeche.Frontend.Olean.Merged}
    {ds : Array Declaration}
    (hnames : lsC.map (·.name) = orderC.toList)
    (hloads : ∀ lC ∈ lsC, ∃ i f, (lC.name, i) ∈ orderC.toList.zipIdx ∧
      (ConLeche.Frontend.Olean.readFiles sp lC.name .private : ModelIO _) F (.ok (.ok f)) ∧
      LoadSpec f i lC)
    (hm : ConLeche.Frontend.Olean.mergeAll lsC.toArray = .ok mgC)
    (hds : ConLeche.Frontend.Olean.declsOf (ConLeche.Frontend.Olean.emitAll mgC mgC.order) = .ok ds)
    {cv : ConstantVal} {code : Nat} {e : Expr}
    (hd : Declaration.thmDecl cv (.bvar code) ∈ ds)
    (hv : ConLeche.Frontend.Olean.ValueAt sp F
      (lsC.map fun l => (⟨l.name, l.frontier⟩ : ConLeche.Frontend.Olean.ModRef)).toArray code e) :
    ∃ md f r a sk loc c all,
      (lsC.map fun l => (⟨l.name, l.frontier⟩ : ConLeche.Frontend.Olean.ModRef)).toArray[
        ConLeche.Frontend.Olean.refModule code]? = some md ∧
      (ConLeche.Frontend.Olean.readFiles sp md.name .private : ModelIO _) F (.ok (.ok f)) ∧
      f.viewRegion .private = some (r, a) ∧ ConLeche.Frontend.Olean.moduleSkel r a = some sk ∧
      loc ∈ sk.consts ∧ ConLeche.Frontend.Olean.constSpec r loc = some c ∧ c.kind = .thm e all ∧
      cv = ⟨c.name, c.levelParams, c.type⟩ := by
  obtain ⟨hk1, hk2, hk3, hk4⟩ := ConLeche.Frontend.Olean.mergeAll_ok hm
  have hN : ∀ (n : ConLeche.Name) (x : ConLeche.Frontend.Olean.CEntry), mgC.map[n]? = some x →
      x.name = n := fun n x hx => (hk2 n x hx).1
  -- the record's constant
  obtain ⟨E, hS, hE⟩ : ∃ E, ConLeche.Frontend.Olean.Stored mgC E ∧
      ConLeche.Frontend.Olean.entryDecl E = some (.thmDecl cv (.bvar code)) := by
    rcases ConLeche.Frontend.Olean.declsOf_from hN hds hd with h' | ⟨ts, cts, rcs, -, hb⟩
    · exact h'
    · exact (ConLeche.Frontend.Olean.declOfF_ind_thm hb).elim
  obtain ⟨all, hkE, hcv⟩ : ∃ all, E.kind = .thm (.bvar code) all ∧
      cv = ⟨E.name, E.levelParams, E.type⟩ := by
    unfold ConLeche.Frontend.Olean.entryDecl at hE
    cases hk : E.kind with
    | thm v all =>
      simp only [hk, Option.some.injEq, Declaration.thmDecl.injEq] at hE
      obtain ⟨rfl, rfl⟩ := hE
      exact ⟨all, rfl, rfl⟩
    | ax u => simp [hk] at hE
    | defn v h s =>
      simp only [hk] at hE
      split at hE <;> first | contradiction | simp at hE
    | opaq v u => simp [hk] at hE
    | quot k =>
      simp only [hk] at hE
      split at hE <;> first | contradiction | simp at hE
    | induct _ _ _ _ _ _ _ _ => simp [hk] at hE
    | ctor _ _ _ _ _ => simp [hk] at hE
    | recur _ _ _ _ _ _ _ _ => simp [hk] at hE
  -- its module and its skeleton
  obtain ⟨-, l, hl, hEl⟩ := hk2 _ _ hS
  have hl' : l ∈ lsC := by simpa using hl
  obtain ⟨i, f, hzip, hf, r, a, sk, skels, hreg, hsk, hskels, hlazy⟩ := hloads l hl'
  obtain ⟨s, hs, hent⟩ := hlazy.to_skel E (by simpa using hEl)
  obtain ⟨p, g, all₀, hsk1, hw, hloc, hi, hn, hlp, hty, hall⟩ :=
    ConLeche.Frontend.Olean.lazyEntry_thm hent hkE
  obtain ⟨hm1, hm2⟩ := ConLeche.Frontend.Olean.refParts (g := g) hi
  have hcode : code = g * ConLeche.Frontend.Olean.refBase + i := by
    simp only [ConLeche.Frontend.Olean.valueRef, Expr.bvar.injEq] at hw
    exact hw
  subst hcode
  -- the module the reference names is this one
  have hzi : orderC.toList[i]? = some l.name := List.mem_zipIdx_iff_getElem?.mp hzip
  rw [← hnames] at hzi
  obtain ⟨md, f', r', a', hmd, hf', hreg', hval⟩ := hv
  rw [hm1] at hmd
  rw [hm2] at hval
  have hname : md.name = l.name := by
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hzi
    obtain ⟨y, hy, hyn⟩ := hzi
    simp only [List.getElem?_toArray, List.getElem?_map, hy, Option.map_some,
      Option.some.injEq] at hmd
    rw [← hmd]
    exact hyn
  rw [hname] at hf'
  obtain rfl := ConLeche.Frontend.Olean.readFiles_unique hf hf'
  rw [hreg] at hreg'
  cases hreg'
  obtain ⟨loc, hlocm, hcs⟩ := ConLeche.Frontend.Olean.mapM_mem_inv hskels hs
  have hep : ConLeche.Frontend.Olean.exprP r p = some e := by
    simp only [ConLeche.Frontend.Olean.exprP, hloc]
    exact hval
  have hspec : ConLeche.Frontend.Olean.constSpec r loc =
      some ⟨E.name, E.levelParams, E.type, .thm e all⟩ := by
    unfold ConLeche.Frontend.Olean.constSpec
    rcases s with ⟨sn, sl, st, sk'⟩
    simp only at hsk1 hn hlp hty
    subst hsk1
    simp only [hcs, bind, Option.bind, ConLeche.Frontend.Olean.CEntryF.mapM,
      ConLeche.Frontend.Olean.CKindF.mapM, hn, hlp, hty, hep, hall, pure]
  refine ⟨md, f, r, a, sk, loc, _, all, ?_, by rw [hname]; exact hf, hreg, hsk, hlocm, hspec, rfl, hcv⟩
  rw [hm1, hmd]

/-! ## The whole read -/

/-- con-leche: ConLeche/Verify/Frontend/Olean/Files.lean:698 readOleans_thm — **THEOREM 1 FOR THE
READER**: the twin's accepting read on a snapshot leaves a store its records denote in, and a
theorem of the private view of a module of the closure, by the specification, is among them with
its statement.  The record's value is the reference to where the theorem's value is stored (a
`bvar`, upstream's `valueRef`): the check reads it.  `hroots` is the roots' denotation. -/
theorem readOleans_run {F : FS} {sp : SearchPath} {roots : Array NIdx}
    {rootsC : Array ConLeche.Name} {rd : ConRon.Arena.Frontend.Olean.OleanRead} {s s' : AState}
    (hok : StateOK s) (hoff : s.store.scratchOn = false) (hpins : PinsOK s)
    (hroots : ListRel (NR s.store) roots.toList rootsC.toList)
    (h : ConRon.Arena.Frontend.Olean.readOleans (modelFs F) sp roots none s = .ok (.ok rd, s')) :
    ParseStep s s' ∧ PersDecls rd.decls ∧ PinsRel s'.store rd.pins ∧
      (∃ usedC, UsedRel s'.store rd.usedOf usedC) ∧
      ∃ valuesP ds, ValuesRel sp F s'.store rd.values valuesP ∧
      denoteDeclArray s'.store rd.decls = some ds ∧
      (∀ {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded} {c : CEntryF ConLeche.Name Expr}
        {v : Expr} {all : List ConLeche.Name}, InClosure sp F rootsC m → ViewOf sp F m d →
        c ∈ d.constants → c.kind = .thm v all →
        ∃ code, Declaration.thmDecl ⟨c.name, c.levelParams, c.type⟩ (.bvar code) ∈ ds) ∧
      ∀ {cv : ConstantVal} {code : Nat} {x : Expr}, Declaration.thmDecl cv (.bvar code) ∈ ds →
        ConLeche.Frontend.Olean.ValueAt sp F valuesP code x →
        ∃ md f r a sk loc c all, valuesP[ConLeche.Frontend.Olean.refModule code]? = some md ∧
          (ConLeche.Frontend.Olean.readFiles sp md.name .private : ModelIO _) F (.ok (.ok f)) ∧
          f.viewRegion .private = some (r, a) ∧ ConLeche.Frontend.Olean.moduleSkel r a = some sk ∧
          loc ∈ sk.consts ∧ ConLeche.Frontend.Olean.constSpec r loc = some c ∧ c.kind = .thm x all ∧
          cv = ⟨c.name, c.levelParams, c.type⟩ := by
  unfold ConRon.Arena.Frontend.Olean.readOleans at h
  obtain ⟨pk, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hst1, hp1⟩ := oleanPins_run hok hoff h1
  have hctx1 : Ctx pk s₁ := ⟨hst1.ok, by rw [hst1.scratch]; exact hoff, hp1.nulls⟩
  obtain ⟨ls, s₂, h2, h⟩ := AM.bind_ok h
  obtain ⟨hst2, orderC, lsC, ho, hlsR, hfront, hnames, hloads⟩ :=
    loadClosure_run hctx1 hp1 (NR_list_ext hst1.ext hroots) h2
  have hctx2 := hctx1.step hst2
  have hp2 := hp1.ext hst2.ext
  obtain ⟨mg, s₃, h3, h⟩ := AM.bind_ok h
  obtain ⟨hs3, hmls, mgC, hm, hmr⟩ := mergeAll_run hctx2.ok hctx2.nulls hlsR h3
  rw [hs3] at h
  obtain ⟨hk1, hk2, hk3, -⟩ := ConLeche.Frontend.Olean.mergeAll_ok hm
  have hN : ∀ (n : ConLeche.Name) (x : ConLeche.Frontend.Olean.CEntry), mgC.map[n]? = some x →
      x.name = n := fun n x hx => (hk2 n x hx).1
  have hwc : WalkCtx s₂.store mg mgC := ⟨hmr, nsWF_of_StateOK hctx2.ok, hN⟩
  obtain ⟨u, s₄, h4, h⟩ := AM.bind_ok h
  obtain ⟨hs4, hb⟩ := blocksOk_run hwc hp2 h4
  rw [hs4] at h
  obtain ⟨cs, s₅, h5, h⟩ := AM.bind_ok h
  obtain ⟨hv5, hs5⟩ := AM.pure_ok h5
  subst hv5
  rw [hs5] at h
  obtain ⟨em, s₆, h6, h⟩ := AM.bind_ok h
  obtain ⟨hs6, hem⟩ := emitAll_run hwc hp2 hmr.order h6
  rw [hs6] at h
  obtain ⟨x, s₇, h7, h⟩ := AM.bind_ok h
  cases x with
  | error e => cases (AM.pure_ok h).1
  | ok r =>
  simp only [ConRon.Arena.Frontend.Olean.modRefs] at h
  obtain ⟨hv, hs⟩ := AM.pure_ok h
  cases hv
  subst hs
  have hpinsS : PinsOK s₂ := (hpins.mono (hst1.trans hst2).ext (hst1.trans hst2).pins)
  obtain ⟨hst3, hpers, ds, hds, hden⟩ := declsOf_run hctx2.ok hctx2.off hpinsS hem h7
  refine ⟨(hst1.trans hst2).trans hst3, hpers, hp2.ext hst3.ext,
    ⟨usedOfC mgC, UsedRel.mono hst3.ext (usedRel_usedOf hmr.strip)⟩,
    (lsC.map fun l => (⟨l.name, l.frontier⟩ : ConLeche.Frontend.Olean.ModRef)).toArray, ds, ?_, hden,
    ?_, fun hd hv => filled_of hnames hloads hm hds hd hv⟩
  · have := valuesRel_of_loads (ListRel.mono' (fun _ _ h => h.ext hst3.ext) hlsR)
      (ListRel.mono' (fun _ _ h => ModFront.ext h hst3.ext) hfront) (sp := sp) (F := F)
    simp only [ValuesRel, hmls]
    simpa using this
  intro m d c v all hcl hv hc hk
  obtain ⟨hco, hcr⟩ := ConLeche.Frontend.Olean.closureOrder_ok ho
  have hmo := hcl.mem_order hco hcr
  have hmem : m ∈ lsC.map (·.name) := by
    rw [hnames]
    simpa using hmo
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem
  obtain ⟨i, f, -, hf, r, a, sk, skels, hreg, hsk, hskels, hlazy⟩ := hloads l hl
  obtain ⟨f', hf', hview⟩ := hv
  obtain rfl := ConLeche.Frontend.Olean.readFiles_unique hf hf'
  obtain ⟨sk', hsk', hspec⟩ := ConLeche.Frontend.Olean.view_parts hreg hview
  rw [hsk] at hsk'
  cases hsk'
  obtain ⟨loc, hloc, hcs⟩ := ConLeche.Frontend.Olean.mapM_mem_inv hspec (by simpa using hc)
  obtain ⟨sc, hs1, hs2⟩ := ConLeche.Frontend.Olean.constSpec_parts hcs
  obtain ⟨sc', hs'mem, hs'⟩ := ConLeche.Frontend.Olean.mapM_mem hskels hloc
  rw [hs1] at hs'
  cases hs'
  obtain ⟨e, he, hent⟩ := hlazy.of_skel _ hs'mem
  obtain ⟨hn, hlp, hty, hth⟩ := ConLeche.Frontend.Olean.lazyEntry_of_spec hs2 hent
  obtain ⟨_, g, _, _, hkind, _, _⟩ := hth v all hk
  obtain ⟨c', hc', hs⟩ := hk1 l (by simpa using hl) e (by simpa using he)
  have hst : ∃ v' all', c'.kind = .thm v' all' ∧ c'.name = e.name ∧ c'.levelParams = e.levelParams ∧
      c'.type = e.type := by
    rcases hs with rfl | ⟨n1, t1, l1, k1⟩
    · exact ⟨_, all, hkind, rfl, rfl, rfl⟩
    · rw [hkind] at k1
      cases hk2' : c'.kind with
      | thm v' all' => exact ⟨v', all', rfl, n1, l1, t1⟩
      | ax _ => rw [hk2'] at k1; exact k1.elim
      | defn _ _ _ => rw [hk2'] at k1; exact k1.elim
      | opaq _ _ => rw [hk2'] at k1; exact k1.elim
      | quot _ => rw [hk2'] at k1; exact k1.elim
      | induct _ _ _ _ _ _ _ _ => rw [hk2'] at k1; exact k1.elim
      | ctor _ _ _ _ _ => rw [hk2'] at k1; exact k1.elim
      | recur _ _ _ _ _ _ _ _ => rw [hk2'] at k1; exact k1.elim
  obtain ⟨v', all', hk5, hn', hlp', hty'⟩ := hst
  have := ConLeche.Frontend.Olean.declsOf_thm hN hk3 hds hb
    ((hk3 _).2 (ConLeche.Frontend.Olean.contains_of_getElem hc')) hc' hk5
  rw [hn', hlp', hty', show e.name = c.name from hn, show e.levelParams = c.levelParams from hlp,
    show e.type = c.type from hty] at this
  -- the kept copy is a loaded constant, so its value is a reference
  obtain ⟨-, l', hl', hcl'⟩ := hk2 _ _ hc'
  obtain ⟨i', f'', -, -, r', a', sk'', skels', -, -, -, hlazy'⟩ := hloads l' (by simpa using hl')
  obtain ⟨s0, -, hent0⟩ := hlazy'.to_skel c' (by simpa using hcl')
  obtain ⟨-, g0, -, -, hw, -⟩ := ConLeche.Frontend.Olean.lazyEntry_thm hent0 hk5
  rw [hw] at this
  exact ⟨_, this⟩

end ConRon.Bridge.Frontend.Olean
