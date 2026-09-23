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

`sorry`: `structProjBodies_spec` (`Bridge/Inductives/StructParts.lean`), the
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
        denoteFEnv st fe = some env)
      (Arena.checkStructProjTable T C lps nP nF resSort guards off cvCa fe)
      (InstRel fe (fun env' =>
        @ConLeche.checkStructProjTable CheckM _ _ TP CP lpsP nP nF resSortP
          guardsP off cvCaP env = .ok env')) := by
  sorry

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
    guardsP off cvCa cvCaP hg hcoh).toCSpec μ env fe

end ConRon.Bridge.Inductives
