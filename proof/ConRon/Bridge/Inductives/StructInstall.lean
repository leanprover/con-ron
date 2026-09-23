/-
# `ConRon.Bridge.Inductives.StructInstall` — Theorem 1 for the projection table

`Arena/Inductives/StructInstall.lean` is two twins, and
`Arena/Inductives/StructInstallF.lean`'s three `abbrev`s are the SAME two
(task #97d-2's deviation 1: the arena has one environment type, so
con-leche's `…F` mirrors collapse and their names survive as `abbrev`s).
So there are two statements here and the three `…F` names are `abbrev`s of
them, exactly as the twins are of theirs.

`checkStructDomsAt` is the first CORE-grade twin of the tier: it calls
`isDefEqCore`, so its frame is `CoreStep` and its statement takes `CheckOK`.
`checkStructProjTable` is pure grade at the store but installs, so it answers
an `InstRel`.

## `checkStructDomsAtFA`'s `Array` spelling

con-leche has a second copy of `checkStructDomsAtF` over `Array Expr`
(`StructInstallF.lean:38-48`) because its caller holds an array; the twin's
list version serves both (deviation 1), and the `Array` statement is the list
one at `hs.toList` — which is what `Frontend.denoteEArray` is defined as.
-/
import ConRon.Bridge.Inductives.NativeParts

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The parameter domains, pinned definitionally -/

/-- con-leche: none — the pure walk is monotone in the fuel of its `isDefEq`:
`ConLeche.isDefEqCore_mono` at every pair. -/
theorem checkStructDomsAt_mono {μ : CheckMode} {env : Env} {F F' : Nat}
    (hle : F ≤ F') {off : Nat} {fvsP domsP : List Expr} :
    ∀ {j : Nat}, ConLeche.checkStructDomsAt (ConLeche.fueledOps μ F) env off fvsP
        domsP j = (.ok () : CheckM Unit) →
      ConLeche.checkStructDomsAt (ConLeche.fueledOps μ F') env off fvsP domsP j
        = (.ok () : CheckM Unit) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    simp only [ConLeche.checkStructDomsAt, ConLeche.fueledOps] at h ⊢
    cases ha : fvsP[j]? with
    | none => simp [ha, ConLeche.unwrapOr, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at h
    | some a =>
    cases hb : domsP[j]? with
    | none => simp [ha, hb, ConLeche.unwrapOr, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, pure, Except.pure] at h
    | some b =>
    simp only [ha, hb, ConLeche.unwrapOr, bind, Except.bind, pure, Except.pure] at h ⊢
    cases hd : ConLeche.isDefEqCore μ env F (off + j) a.fvarTypeD b with
    | error e => rw [hd] at h; exact nomatch h
    | ok c =>
      rw [hd] at h
      rw [ConLeche.isDefEqCore_mono hle hd]
      cases c with
      | false => exact nomatch h
      | true =>
        simp only [if_true] at h ⊢
        exact ih h

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:32-51 checkStructDomsAt
con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:27-36 checkStructDomsAtF
con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:38-48 checkStructDomsAtFA
The first `j` parameter domains are definitionally the declared ones.  A
`Unit` answer: what it claims is that con-leche's own check SUCCEEDS at some
fuel.

**CLOSED** (task #97-P3-Ind round 6): a `Nat` recursion over `CoreSpec.knot`'s
`defeq` slot, `fvarTypeD_run` for the left side, and one fuel for the whole
walk (`ConLeche.isDefEqCore_mono` at `max`).

**Two preconditions it was missing** (round 6), both the knot's own: the
`defeq` slot is stated at a well-formed environment (`CoreSpec.knot` takes
`EnvWF env`) and at WELL-SCOPED arguments (`Expr.WScoped` at the depth of the
comparison, `off + i` at the `i`-th pair).  `Bridge/Checker/Base.lean`'s
`checkDefEqList_bridge` carries exactly the same two for exactly the same
reason.  Nothing consumes this statement yet (the arena's install inlines no
call to it), so no caller moved. -/
theorem checkStructDomsAt_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (off : Nat)
    (fvs doms : List EIdx) (fvsP domsP : List Expr) (j : Nat)
    (hws : ∀ i, i < j → ∀ a b, fvsP[i]? = some a → domsP[i]? = some b →
      Expr.WScoped (off + i) a.fvarTypeD ∧ Expr.WScoped (off + i) b) :
    CSpec μ env fe
      (fun st => Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st doms = some domsP ∧
        denoteFEnv st fe = some env)
      (Arena.checkStructDomsAt μ fe off fvs doms j)
      (fun _ _ => ∃ F, ConLeche.checkStructDomsAt (ConLeche.fueledOps μ F)
        env off fvsP domsP j = (.ok () : CheckM Unit)) := by
  have hknot := hk.knot env fe henv
  induction j with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.checkStructDomsAt] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, 0, rfl⟩
  | succ j ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hfvs, hdoms, hfe⟩ := hpre
    simp only [Arena.checkStructDomsAt] at hrun
    obtain ⟨a, s1, k1, hz1⟩ := bindOk hrun
    cases ha : fvs[j]? with
    | none =>
      rw [ha] at k1; simp only [Arena.unwrapOr] at k1; exact absurd k1 (fun h => failOk h)
    | some a' =>
    rw [ha] at k1; simp only [Arena.unwrapOr] at k1
    obtain ⟨rfl, hs1⟩ := pureOk k1
    rw [hs1] at hz1
    obtain ⟨b, s2, k2, hz2⟩ := bindOk hz1
    cases hb : doms[j]? with
    | none =>
      rw [hb] at k2; simp only [Arena.unwrapOr] at k2; exact absurd k2 (fun h => failOk h)
    | some b' =>
    rw [hb] at k2; simp only [Arena.unwrapOr] at k2
    obtain ⟨rfl, hs2⟩ := pureOk k2
    rw [hs2] at hz2
    obtain ⟨aP, haP, hda⟩ := ExprOps.denoteEList_getElem? fvs fvsP hfvs j a ha
    obtain ⟨bP, hbP, hdb⟩ := ExprOps.denoteEList_getElem? doms domsP hdoms j b hb
    obtain ⟨t, s3, k3, hz3⟩ := bindOk hz2
    obtain ⟨hs3, ht⟩ := fvarTypeD_run hok.state hda k3
    rw [hs3] at hz3
    obtain ⟨c, s4, k4, hz4⟩ := bindOk hz3
    obtain ⟨hws1, hws2⟩ := hws j (Nat.lt_succ_self j) aP bP haP hbP
    obtain ⟨hok4, hx4, hp4, hsim⟩ := AM.of_run (P := fun u => u = s₀)
      (Q := fun r u => CheckOK μ env fe u ∧ Ext s₀.store u.store ∧
        u.pins = s₀.pins ∧
        Core.SimV (ConLeche.isDefEqCore μ env) (off + j) aP.fvarTypeD bP r)
      rfl k4 (hknot.defeq s₀ (off + j) t b aP.fvarTypeD bP hok ht hdb hws1 hws2)
    obtain ⟨F1, hF1⟩ := hsim
    obtain ⟨hc, hz5⟩ := AM.dunless_ok AM.Never.fail_any hz4
    replace hz5 := AM.pure_bind_ok hz5
    subst hc
    obtain ⟨hstep, F2, hF2⟩ := ih (fun i hi => hws i (Nat.lt_succ_of_lt hi)) s4 s' r
      hok4 ⟨denoteEList_ext hx4 _ _ hfvs, denoteEList_ext hx4 _ _ hdoms,
        denoteFEnv_ext hx4 hfe⟩ hz5
    refine ⟨⟨hstep.ok, hx4.trans hstep.ext, by rw [hstep.pins, hp4]⟩, max F1 F2, ?_⟩
    have h1 := ConLeche.isDefEqCore_mono (Nat.le_max_left F1 F2) hF1
    have h2 := checkStructDomsAt_mono (Nat.le_max_right F1 F2) hF2
    simp only [ConLeche.checkStructDomsAt, haP, hbP, ConLeche.unwrapOr,
      ConLeche.fueledOps, bind, Except.bind, pure, Except.pure, h1, if_true]
    exact h2

/-! ## The projection table -/

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:53-86 checkStructProjTable
con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:73-95 checkStructProjTableF
**The structure-like block's projection table**: one constant per structure
(task #175 S1), carrying the fields' bodies off the annotated constructor type
and the guard levels the constructors' stage measured.

**The `guards` hypothesis, and what it buys** (task #97-P3-Ind round 2).
`InstRel`'s `proj` field is `ProjOut` — "every projection table the new index
holds was already in the old one, or is well shaped at the new store" — and
this is the ONE install of the whole arena that pushes a `.projInfo` row, so
this is the one theorem where that field has content.  `IProjTableOK`'s three
clauses are `bodies.size = numFields` (the twin's own `unless bodies.size =
nF`), `guards.length = numFields` and the table's two names (the twin's
`let tn ← projTableName T`).  The middle one is about an ARGUMENT, so the
install cannot test it and does not: `hg` is it, and
`checkNativeTable_spec` — the caller that builds `structProjGuards cA.1.type
p.nP cA.2 sorts` and passes it beside `cA.2` — discharges it from
`structProjGuards_length`.  `Bridge/Checker/Inv.lean`'s
`projTableOK_of_install` is the same statement at the same hypothesis, stated
there so that `IFEnvOK`'s new field has one named debtor; this is its site.

**CLOSED** (task #97-P3-Ind round 8), over `structProjBodies_spec` (`Bridge/Inductives/StructParts.lean`), the
`IProjTable` record's denotation (`Bridge/Rel.lean`'s `denoteProjTable`), and
`IFEnv.push`'s own two lemmas — `IFEnvCoh` is preserved by `push` and `Pushed`
is `⟨[ci], rfl⟩`.  The `denoteFEnv` clause is the push's `denoteCI` at the new
`.projInfo` row; the `proj` clause is `hg`, the `bodies.size` test read off
the `unless`, and `projTableName_spec` at `tn`. -/
theorem checkStructProjTable_run (fe : IFEnv) (env : Env)
    (T C : NIdx) (TP CP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF : Nat) (resSort : LIdx)
    (resSortP : Level) (guards : List LIdx) (guardsP : List Level) (off : Nat)
    (cvCa : IConstantVal) (cvCaP : ConstantVal)
    (hg : guards.length = nF) (hcoh : IFEnvCoh fe) :
    PSpecP
      (fun st => denoteN st.ns T = some TP ∧ denoteN st.ns C = some CP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls resSort = some resSortP ∧
        denoteLList st.ls guards = some guardsP ∧
        Frontend.denoteCV st cvCa = some cvCaP ∧
        denoteFEnv st fe = some env ∧ IFEnvOKS env fe st)
      (Arena.checkStructProjTable T C lps nP nF resSort guards off cvCa fe)
      (InstRel fe (fun env' =>
        @ConLeche.checkStructProjTable CheckM _ _ TP CP lpsP nP nF resSortP
          guardsP off cvCaP env = .ok env')) := by
  intro s₀ s' r hok hpins hpre hrun
  obtain ⟨hT, hC, hlps, hrs, hgd, hcv, hfe, hienvS⟩ := hpre
  have hread : ReadOK env fe s₀ := ⟨hok, hpins, hienvS s₀ rfl⟩
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  simp only [Arena.checkStructProjTable] at hrun
  -- the bodies
  obtain ⟨o, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := structProjBodies_spec T TP nP nF cvCa.type cvCaP.type s₀ s₁ o hok
    ⟨hT, denoteCV_type hcv⟩ k1
  obtain ⟨bodies, s₂, k2, z2⟩ := bindOk z1
  cases o with
  | none => simp only [Arena.unwrapOr] at k2; exact absurd k2 (fun h => failOk h)
  | some o' =>
  simp only [Arena.unwrapOr] at k2
  obtain ⟨hb2, hs2⟩ := pureOk k2
  subst hb2
  rw [hs2] at z2
  obtain ⟨bodiesP, hbP, hbodies⟩ := ho
  have hbl : Frontend.denoteEList s₁.store bodies.toList = some bodiesP.toList := by
    have h' : Frontend.denoteEArray s₁.store bodies = some bodiesP := hbodies
    simp only [Frontend.denoteEArray] at h'
    split at h'
    · rename_i xs hxs
      obtain rfl := (Option.some.inj h').symm
      simpa using hxs
    · exact nomatch h'
  -- their scoping, one guard per body
  obtain ⟨sc, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨p3, hsc⟩ := allM_E_ckQ (env := env) (fe := fe)
    (F := fun b => !b.hasFvar && b.allLevelParamsDefined lpsP && b.constsResolve env &&
      b.looseBVarsBounded (nP + 1))
    (fun st => Frontend.denoteNList st.ns lps = some lpsP)
    (fun hx h => denoteNListE_ext hx _ _ h)
    (fun e eP t t' x hr hq he hrun => by
      obtain ⟨b1, t1, g1, y1⟩ := bindOk hrun
      obtain ⟨h11, h12, h13, hb1⟩ := AM.of_run (P := fun u => u = t) rfl g1
        (ExprOps.hasFvarFast_spec Arena.coreWalkFuel t e hr.state (by rw [he]; rfl))
      have q1 : PStep t t1 := PStep.of_caches ⟨by rw [h11]; exact hr.state.wf⟩
        (by rw [h11]; exact Ext.refl _) (by rw [h11]; exact BMExt.refl _) h12 h13
      have he1 : denoteE t1.store e = some eP := by rw [h11]; exact he
      obtain ⟨b2, t2, g2, y2⟩ := bindOk y1
      obtain ⟨h21, h22, h23, hb2⟩ := allLevelParamsDefined_run q1.ok
        (by rw [h11]; exact hq) he1 g2
      have q2 : PStep t1 t2 := PStep.of_caches ⟨by rw [h21]; exact q1.ok.wf⟩
        (by rw [h21]; exact Ext.refl _) (by rw [h21]; exact BMExt.refl _) h22 h23
      have he2 : denoteE t2.store e = some eP := by rw [h21]; exact he1
      obtain ⟨b3, t3, g3, y3⟩ := bindOk y2
      obtain ⟨h31, h32, h33, hb3⟩ := constsResolveFFast_runR
        (hr.mono q2.ok (q1.ext.trans q2.ext) (by rw [q2.pins, q1.pins])) he2 g3
      have q3 : PStep t2 t3 := PStep.of_caches ⟨by rw [h31]; exact q2.ok.wf⟩
        (by rw [h31]; exact Ext.refl _) (by rw [h31]; exact BMExt.refl _) h32 h33
      have he3 : denoteE t3.store e = some eP := by rw [h31]; exact he2
      obtain ⟨b4, t4, g4, y4⟩ := bindOk y3
      obtain ⟨h41, h42, h43, hb4⟩ := AM.of_run (P := fun u => u = t3) rfl g4
        (ExprOps.looseBVarsBoundedFast_spec Arena.coreWalkFuel (nP + 1) t3 e q3.ok
          (by rw [he3]; rfl))
      have q4 : PStep t3 t4 := PStep.of_caches ⟨by rw [h41]; exact q3.ok.wf⟩
        (by rw [h41]; exact Ext.refl _) (by rw [h41]; exact BMExt.refl _) h42 h43
      obtain ⟨rfl, rfl⟩ := pureOk y4
      refine ⟨q1.trans (q2.trans (q3.trans q4)), ?_⟩
      rw [hb1 eP he, hb2, hb3, hb4 eP he3])
    bodies.toList bodiesP.toList s₁ s₃ sc (hread.mono p1.ok p1.ext p1.pins)
    (denoteNListE_ext p1.ext _ _ hlps) hbl k3
  obtain ⟨hg1, z4⟩ := AM.dunless_ok hnever z3
  replace z4 := AM.pure_bind_ok z4
  have x13 := p3.ext
  -- the projection-function name family
  have hread₃ : ReadOK env fe s₃ := hread.mono p3.ok (p1.ext.trans p3.ext) (by rw [p3.pins, p1.pins])
  obtain ⟨b5, s₅, k5, z5⟩ := bindOk z4
  obtain ⟨p5, hb5⟩ := allM_ck (env := env) (fe := fe)
    (g := fun j => (env.find? (ConLeche.projFnName TP j)).isNone)
    (fun _ st => denoteN st.ns T = some TP) (fun hx h => denoteN_ext h hx)
    (fun j t t' b hok hP hrun => by
      obtain ⟨h, t1, g1, y1⟩ := bindOk hrun
      obtain ⟨q1, hh⟩ := projFnName_run hok.state hP g1
      obtain ⟨rfl, rfl⟩ := pureOk y1
      refine ⟨q1, ?_⟩
      have e := (hok.mono q1.ok q1.ext q1.pins).ienv.find_isSome q1.ok hh
      revert e
      cases fe.find? h <;> cases env.find? (ConLeche.projFnName TP j) <;> simp)
    (List.range nF) s₃ s₅ b5 hread₃ (fun _ _ => denoteN_ext hT (p1.ext.trans x13)) k5
  obtain ⟨hg2, z6⟩ := AM.dunless_ok hnever z5
  replace z6 := AM.pure_bind_ok z6
  rw [hb5] at hg2
  -- the table's own name
  obtain ⟨tn, s₆, k6, z7⟩ := bindOk z6
  have x05 : Ext s₀.store s₅.store := p1.ext.trans (x13.trans p5.ext)
  obtain ⟨p6, htn⟩ := (by
    simp only [Arena.projTableName] at k6
    obtain ⟨m, u1, j1, j2⟩ := bindOk k6
    obtain ⟨r1, hm⟩ := internStrN_run p5.ok (denoteN_ext hT x05) j1
    obtain ⟨r2, hr⟩ := internNumN_run r1.ok hm j2
    exact ⟨r1.trans r2, hr⟩ : PStep s₅ s₆ ∧
      denoteN s₆.store.ns tn = some (ConLeche.projTableName TP))
  have hread₆ : ReadOK env fe s₆ :=
    hread₃.mono p6.ok (p5.ext.trans p6.ext) (by rw [p6.pins, p5.pins])
  obtain ⟨hg3, z8⟩ := AM.dunless_ok hnever z7
  replace z8 := AM.pure_bind_ok z8
  have hg3' : (env.find? (ConLeche.projTableName TP)).isNone = true := by
    have e := hread₆.ienv.find_isSome p6.ok htn
    revert e hg3
    cases fe.find? tn <;> cases env.find? (ConLeche.projTableName TP) <;> simp
  obtain ⟨rfl, rfl⟩ := pureOk z8
  -- the pushed table
  have x06 : Ext s₀.store s'.store := x05.trans p6.ext
  have hsize : bodies.size = nF := hg1.1
  have hall : (bodiesP.toList.all fun b => !b.hasFvar && b.allLevelParamsDefined lpsP &&
      b.constsResolve env && b.looseBVarsBounded (nP + 1)) = true := by
    rw [← hsc]; exact hg1.2
  have hsizeP : bodiesP.size = nF := by
    rw [← hsize]
    have := ExprOps.denoteEList_length _ _ hbl
    simpa using this
  have hdt : Frontend.denoteProjTable s'.store ⟨T, tn, lps, nP, C, nF, resSort, bodies, guards, off⟩
      = some ⟨TP, lpsP, nP, CP, nF, resSortP, bodiesP, guardsP, off⟩ := by
    simp only [Frontend.denoteProjTable, denoteN_ext hT x06, denoteNListE_ext x06 _ _ hlps,
      denoteN_ext hC x06, denoteL_ext hrs x06, denoteEArray_ext hbodies (x13.trans (p5.ext.trans p6.ext))]
    have e1 : denoteLList s'.store.ls guards = some guardsP := denoteLList_ext x06.lss.ls _ _ hgd
    rw [e1]
  have hci : Frontend.denoteCI s'.store (.projInfo ⟨T, tn, lps, nP, C, nF, resSort, bodies, guards, off⟩)
      = some (.projInfo ⟨TP, lpsP, nP, CP, nF, resSortP, bodiesP, guardsP, off⟩) := by
    simp only [Frontend.denoteCI, hdt, Option.map_some]
  refine ⟨p1.trans (p3.trans (p5.trans p6)), hcoh.push _, Pushed.push _ _, Nat.le_succ _,
    ⟨_, denoteFEnv_push (denoteFEnv_ext x06 hfe) hci, ?_⟩, ?_⟩
  · simp only [ConLeche.checkStructProjTable, hbP, ConLeche.unwrapOr, bind, Except.bind, pure,
      Except.pure]
    rw [if_pos ⟨hsizeP, by rw [← Array.all_toList]; exact hall⟩,
      if_pos hg2, if_pos hg3']
  · exact ProjOut.push_table hcoh _ ⟨hsize, hg, TP, denoteN_ext hT x06, htn⟩

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:53-86 checkStructProjTable
The same at the core grade, read off `checkStructProjTable_run` (the twin is
pure, so it needs no `CheckOK` and leaves `PStep`).  **`hcoh` added** (task
#97-P3-Ind round 8, ruling 3 on round 7's R7.5: `InstRel.coh` of the pushed
index needs the old index coherent). -/
theorem checkStructProjTable_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (T C : NIdx) (TP CP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF : Nat) (resSort : LIdx)
    (resSortP : Level) (guards : List LIdx) (guardsP : List Level) (off : Nat)
    (cvCa : IConstantVal) (cvCaP : ConstantVal)
    (hg : guards.length = nF) (hcoh : IFEnvCoh fe) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧ denoteN st.ns C = some CP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls resSort = some resSortP ∧
        denoteLList st.ls guards = some guardsP ∧
        Frontend.denoteCV st cvCa = some cvCaP ∧
        denoteFEnv st fe = some env)
      (Arena.checkStructProjTable T C lps nP nF resSort guards off cvCa fe)
      (InstRel fe (fun env' =>
        @ConLeche.checkStructProjTable CheckM _ _ TP CP lpsP nP nF resSortP
          guardsP off cvCaP env = .ok env')) :=
  (checkStructProjTable_run fe env T C TP CP lps lpsP nP nF resSort resSortP guards
    guardsP off cvCa cvCaP hg hcoh).toCSpec μ env fe |> fun h => by
      intro s₀ s' r hok hpre hrun
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hpre
      exact h s₀ s' r hok ⟨a1, a2, a3, a4, a5, a6, a7, hok.ienv.toS⟩ hrun

end ConRon.Bridge.Inductives
