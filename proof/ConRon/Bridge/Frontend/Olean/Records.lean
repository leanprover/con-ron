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
    ParseStep s s' ∧ PersDecls rd.decls ∧ ∃ ds, denoteDeclArray s'.store rd.decls = some ds ∧
      ∀ {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded} {c : CEntryF ConLeche.Name Expr}
        {v : Expr} {all : List ConLeche.Name}, InClosure sp F rootsC m → ViewOf sp F m d →
        c ∈ d.constants → c.kind = .thm v all →
        ∃ v', Declaration.thmDecl ⟨c.name, c.levelParams, c.type⟩ v' ∈ ds := by
  unfold ConRon.Arena.Frontend.Olean.readOleans at h
  obtain ⟨pk, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hst1, hp1⟩ := oleanPins_run hok hoff h1
  have hctx1 : Ctx pk s₁ := ⟨hst1.ok, by rw [hst1.scratch]; exact hoff, hp1.nulls⟩
  obtain ⟨ls, s₂, h2, h⟩ := AM.bind_ok h
  obtain ⟨hst2, orderC, lsC, ho, hlsR, hnames, hloads⟩ :=
    loadClosure_run hctx1 hp1 (NR_list_ext hst1.ext hroots) h2
  have hctx2 := hctx1.step hst2
  have hp2 := hp1.ext hst2.ext
  obtain ⟨mg, s₃, h3, h⟩ := AM.bind_ok h
  obtain ⟨hs3, mgC, hm, hmr⟩ := mergeAll_run hctx2.ok hctx2.nulls hlsR h3
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
  refine ⟨(hst1.trans hst2).trans hst3, hpers, ds, hden, ?_⟩
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
  exact ⟨v', this⟩

end ConRon.Bridge.Frontend.Olean
