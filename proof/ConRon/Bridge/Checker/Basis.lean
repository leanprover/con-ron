/-
# `ConRon.Bridge.Checker.Basis` — the pinned blocks and the axiom installs

Three things that share a shape: they compare a stream record against a
BUILD-TIME literal and install the literal, not the record.

* `Arena/Basis.lean` — `BasisKind.decls` / `declsA` (the six pinned blocks in
  raw and annotated form), `basisPinHit`, `quotPinHit`;
* `Arena/StdAxioms.lean` — `propext`, `Classical.choice`, the `Iff` and
  `Nonempty` families;
* `Arena/TrustAxioms.lean` — `Lean.trustCompiler`, the two `reduce*` opaques
  and the two `ofReduce*` axioms.

**Why all three are one module of the bridge.**  Each arena definition is
`internCI`/`internCV`/`internExpr` of the corresponding con-leche VALUE
(`Arena/Intern.lean`), so each one's bridge theorem is one instance of the
frontend tier's intern exactness — `denoteCI st (internCI c) = some c` — and
nothing else.  There is no algorithm to mirror: the literal is the same
literal, and the only question is whether interning it preserves its meaning.

**What DOES have content** is `checkBasisDecl`, because it is the one place
the environment grows by a whole block at once: `installBasisDecls` pushes six
or seven constants in one step, so `Pushed` is a six-fold `Pushed.push` and
the `k` the fold's promotion computes is the block's length.  That is the only
place in the checker where a step installs more than one constant outside the
inductive route, and the fold's counter arithmetic has to survive it.
-/
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Frontend.Shared

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The interned literals -/

/-- con-leche: ConLeche/Kernel/Basis.lean:41-66 BasisKind.decls — the raw
pinned block denotes con-leche's.

`sorry`: `internCIList` over the frontend tier's intern exactness.  Task
#97-P3-Checker's sorry list, item 15. -/
theorem BasisKind.decls_run {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s) (hrun : BasisKind.decls k s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      Frontend.denoteCIList s'.store r = some k.decls := by
  simp only [ConRon.Arena.BasisKind.decls, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, cis⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨hstep, hden, -, -⟩ :=
    Frontend.internCIList_sstep (ConLeche.BasisKind.decls k) hok
      (Frontend.EMemoOK.empty s.store) hgo
  exact ⟨hstep.ok, hstep.ext, hstep.caches, hstep.pins, hden⟩

/-- con-leche: ConLeche/Kernel/BasisA.lean:51-57 BasisKind.declsA — the
ANNOTATED pinned block denotes con-leche's.  This is the one the install
puts in the environment.

`sorry`: as `BasisKind.decls_run`.  Task #97-P3-Checker's sorry list,
item 15. -/
theorem BasisKind.declsA_run {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s)
    (hrun : BasisKind.declsA k s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      Frontend.denoteCIList s'.store r = some k.declsA := by
  simp only [ConRon.Arena.BasisKind.declsA, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, cis⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨hstep, hden, -, -⟩ :=
    Frontend.internCIList_sstep (ConLeche.BasisKind.declsA k) hok
      (Frontend.EMemoOK.empty s.store) hgo
  exact ⟨hstep.ok, hstep.ext, hstep.caches, hstep.pins, hden⟩

/-- con-leche: none — the same walk's fourth conjunct, kept as its own
theorem so that `BasisKind.decls_run`'s conclusion stays the five clauses its
consumers read: every member of the interned block is rightly named, which is
what `toConstantVal_sstep` asks of a `.projInfo` member (there is none, but
the theorem below does not know that). -/
theorem BasisKind.decls_proj {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s)
    (hrun : BasisKind.decls k s = .ok (r, s')) :
    ∀ ci ∈ r, Frontend.CIProjNamed s'.store ci := by
  simp only [ConRon.Arena.BasisKind.decls, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, cis⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨-, -, -, hnamed⟩ :=
    Frontend.internCIList_sstep (ConLeche.BasisKind.decls k) hok
      (Frontend.EMemoOK.empty s.store) hgo
  exact hnamed

/-! ## The common data of a pinned constant

`IConstantInfo.toConstantVal` is pure on six of its seven arms and interns a
`Sort 1` on the seventh (`Arena/Env.lean`: `denoteProjTable` drops
`tableName`, so the table's common data is rebuilt rather than stored).  That
makes it the tier's FIFTH `.projInfo` site, and it is stated here in the
scratch-agnostic frame — `Frontend.IStepS`, not `IStep` — because every
consumer of it inside the checker (`quotPinHit`, `natOpGuard`) runs inside the
per-declaration bracket, where the scratch tier is open and no `hoff` exists.
`Bridge/Frontend/Lines.lean`'s `toConstantVal_run` is the same theorem at the
parse's own frame, where `hoff` is available and the `Pers…` half is wanted. -/

/-- con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo.toConstantVal —
**the common data of a stored constant denotes con-leche's**, with no
assumption about the scratch tier. -/
theorem toConstantVal_sstep {s s' : AState} (hok : StateOK s)
    {ci : IConstantInfo} {c : ConstantInfo}
    (hn : Frontend.CIProjNamed s.store ci)
    (hd : Frontend.denoteCI s.store ci = some c) {v : IConstantVal}
    (hrun : IConstantInfo.toConstantVal ci s = .ok (v, s')) :
    Frontend.IStepS s s' ∧
      Frontend.denoteCV s'.store v = some c.toConstantVal := by
  have hpure : ∀ (w : IConstantVal) (cw : ConstantVal),
      Frontend.denoteCV s.store w = some cw →
      (pure w : AM IConstantVal) s = .ok (v, s') →
      Frontend.IStepS s s' ∧ Frontend.denoteCV s'.store v = some cw := by
    intro w cw hw hr
    obtain ⟨hvv, hss⟩ := AM.pure_ok hr
    subst hvv; subst hss
    exact ⟨Frontend.IStepS.refl hok, hw⟩
  cases ci with
  | axiomInfo w =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨cw, hw, rfl⟩ := hd
    exact hpure w cw hw hrun
  | ctorInfo w nP nF =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨cw, hw, rfl⟩ := hd
    exact hpure w cw hw hrun
  | defnInfo w e hh =>
    simp only [Frontend.denoteCI] at hd
    cases hw : Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | thmInfo w e =>
    simp only [Frontend.denoteCI] at hd
    cases hw : Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | indInfo w cps =>
    simp only [Frontend.denoteCI] at hd
    cases hw : Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases hc : Frontend.denoteCaps s.store cps with
      | none => rw [hw, hc] at hd; simp at hd
      | some x =>
        rw [hw, hc] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | recInfo w mI rP rs =>
    simp only [Frontend.denoteCI] at hd
    cases hw : Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases hr : Frontend.denoteRules s.store rs with
      | none => rw [hw, hr] at hd; simp at hd
      | some x =>
        rw [hw, hr] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | projInfo tbl =>
    obtain ⟨sn, hsn, htn⟩ := hn tbl rfl
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨pt, hpt, rfl⟩ := hd
    have hlps : Frontend.denoteNList s.store.ns tbl.levelParams
        = some pt.levelParams ∧ pt.structName = sn := by
      simp only [Frontend.denoteProjTable, hsn] at hpt
      cases hl : Frontend.denoteNList s.store.ns tbl.levelParams with
      | none => rw [hl] at hpt; simp at hpt
      | some lps =>
        cases hc : denoteN s.store.ns tbl.ctor with
        | none => rw [hl, hc] at hpt; simp at hpt
        | some cn =>
          cases hss : denoteL s.store.ls tbl.structSort with
          | none => rw [hl, hc, hss] at hpt; simp at hpt
          | some ss =>
            cases hbs : Frontend.denoteEArray s.store tbl.bodies with
            | none => rw [hl, hc, hss, hbs] at hpt; simp at hpt
            | some bs =>
              cases hgs : denoteLList s.store.ls tbl.guards with
              | none => rw [hl, hc, hss, hbs, hgs] at hpt; simp at hpt
              | some gs =>
                rw [hl, hc, hss, hbs, hgs] at hpt
                obtain rfl := Option.some.inj hpt
                exact ⟨rfl, rfl⟩
    obtain ⟨hdlps, hstruct⟩ := hlps
    rw [ConRon.Arena.IConstantInfo.toConstantVal] at hrun
    obtain ⟨z, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hdz⟩ :=
      Frontend.internLNode_sstep hok
        ⟨by intro c hc; simp only [LNodeView.lchildren] at hc; exact absurd hc (by simp),
         by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩ h1
    have hdz' : denoteL s₁.store.ls z = some .zero := by
      rw [hdz]; rfl
    obtain ⟨one, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hdo⟩ :=
      Frontend.internLNode_sstep hstep1.ok
        ⟨by intro c hc
            simp only [LNodeView.lchildren, List.mem_singleton] at hc
            subst hc; exact lview_isSome_of_denote hdz',
         by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩ h2
    have hdo' : denoteL s₂.store.ls one = some (.succ .zero) := by
      rw [hdo]
      simp only [denoteLView, denoteL_ext hdz' hstep2.ext, Option.map_some]
    obtain ⟨ty, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hstep3, hdty⟩ :=
      Frontend.internE_sstep hstep2.ok (viewOK_sort (lview_isSome_of_denote hdo')) h3
    have hdty' : denoteE s₃.store ty = some (.sort (.succ .zero)) := by
      rw [hdty]
      simp only [denoteEView, denoteL_ext hdo' hstep3.ext, Option.map_some]
    have hx : Ext s.store s₃.store :=
      (hstep1.ext.trans hstep2.ext).trans hstep3.ext
    obtain ⟨hvv, hss⟩ := AM.pure_ok hrest3
    subst hss; subst hvv
    refine ⟨(hstep1.trans hstep2).trans hstep3, ?_⟩
    simp only [Frontend.denoteCV, ConstantInfo.toConstantVal, hstruct,
      denoteN_ext htn hx, denoteNListE_ext hx _ _ hdlps, hdty']

/-! ## The recognisers -/

/-- con-leche: ConLeche/Kernel/Basis.lean:68-75 basisPinHit — **the
recogniser**: a stream block under a pinned name that matches the pin.  The
arena's answer is con-leche's at the denoted block.

`sorry`: `blockNames` through `denoteN`'s injectivity, then
`canonEqList_run` (`Bridge/Checker/Canon.lean`) at the raw pin.  Task
#97-P3-Checker's sorry list, item 15 — and it is what `checkDecl`'s
`.indDecl` arm needs before it may hand the block to `IndSpec`. -/
theorem basisPinHit_run {block : List IConstantInfo} {b : List ConstantInfo}
    {r : Option BasisKind} {s s' : AState} (hok : StateOK s)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hrun : basisPinHit block s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.basisPinHit b := by
  sorry

/-- con-leche: ConLeche/Kernel/Basis.lean:77-84 quotPinHit — the quotient
package's four-record recogniser.

`sorry`: `IConstantVal.canonEq_run` at the pinned quotient block's `k`-th
constant.  Task #97-P3-Checker's sorry list, item 15. -/
theorem quotPinHit_run {k : QuotKind} {cv : IConstantVal} {c : ConstantVal}
    {r : Bool} {s s' : AState} (hok : StateOK s)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : quotPinHit k cv s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.quotPinHit k c := by
  simp only [ConRon.Arena.quotPinHit] at hrun
  obtain ⟨blk, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hok1, hx1, hc1, hp1, hden1⟩ := BasisKind.decls_run hok hgo
  have hnamed := BasisKind.decls_proj hok hgo
  have hlen : blk.length = (ConLeche.BasisKind.decls .quotK).length :=
    denoteCIList_length blk _ hden1
  have hslot : k.slot < blk.length := by
    rw [hlen]; cases k <;> decide
  cases hb : blk[k.slot]? with
  | none =>
    exact absurd (List.getElem?_eq_none_iff.mp hb) (by omega)
  | some ci =>
    rw [hb] at hrest
    simp only [] at hrest
    obtain ⟨pcv, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨x, hx, hdci⟩ := denoteCIList_get blk _ k.slot ci hden1 hb
    have hmem : ci ∈ blk := by
      obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hb
      exact he ▸ List.getElem_mem hlt
    obtain ⟨hstep2, hdpcv⟩ :=
      toConstantVal_sstep hok1 (hnamed ci hmem) hdci h2
    obtain ⟨hok3, hx3, hc3, hp3, he⟩ :=
      IConstantVal.canonEq_run hstep2.ok
        (denoteCV_ext (denoteCV_ext hcv hx1) hstep2.ext) hdpcv hrest2
    refine ⟨hok3, (hx1.trans hstep2.ext).trans hx3, ?_, ?_, ?_⟩
    · rw [hc3, hstep2.caches, hc1]
    · rw [hp3, hstep2.pins, hp1]
    · rw [he]
      have hgetD : (ConLeche.BasisKind.decls .quotK).getD k.slot
          (.axiomInfo default) = x := by
        rw [List.getD_eq_getElem?_getD, hx]; rfl
      simp only [ConLeche.quotPinHit, hgetD]

/-! ## The install -/

/-- con-leche: ConLeche/Kernel/Checker.lean:27-30 installBasisDecl — one
pinned constant, duplicate-checked.

**PROVED** (task #97-P3-Checker round 4), and **the statement gained
`hproj`** — the `.projInfo` clause round 2 §8 item 5 and round 3 §3.1 both
stopped at.  The duplicate test gives `fe.find? ci.name = none`; turning that
into con-leche's `env.find? c.name = none` through `IFEnvOK.miss` needs

    denoteN s.store.ns ci.name = some c.name

and that is `Bridge/StateOK.lean`'s `denoteCI_name_of`, whose `.projInfo` arm
takes `IProjTableOK` (`Frontend.denoteProjTable` drops `tableName`, so nothing
in the denotation ties the index's key to the recomputed name).  Six of the
seven constructors need nothing; `hproj` is what the seventh costs, and it is
the SAME hypothesis `Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote` already
takes at the same gap.  Free at the one call site: `checkBasisDecl` installs a
pinned block, which contains no `.projInfo` (a table never occurs in parsed
input, and the six basis blocks are `axiomInfo`/`defnInfo`/`indInfo`/
`ctorInfo`/`recInfo` only). -/
theorem installBasisDecl_bridge {μ : CheckMode} {_F : Nat} {env : Env}
    {fe fe' : IFEnv} {ci : IConstantInfo} {c : ConstantInfo} {s s' : AState}
    (hok : FoldOK μ env fe s) (hci : Frontend.denoteCI s.store ci = some c)
    (hproj : ∀ t, ci = .projInfo t → IProjTableOK s.store t)
    (hrun : installBasisDecl fe ci s = .ok (fe', s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env', denoteFEnv s'.store fe' = some env' ∧
        ConLeche.installBasisDecl (m := CheckM) env c = .ok env' := by
  simp only [Arena.installBasisDecl] at hrun
  obtain ⟨hdup, r1⟩ := AM.dunless_ok
    (AM.Never.bind fun _ => AM.Never.fail_any) hrun
  replace r1 := AM.pure_bind_ok r1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
  have hfind : fe.find? ci.name = none := by
    cases hf : fe.find? ci.name with
    | none => rfl
    | some d => rw [hf] at hdup; exact absurd hdup (by simp)
  have hnm := denoteCI_name_of (fun t ht => (hproj t ht).toNamed) hci
  have hfindP : env.find? c.name = none :=
    IFEnvOK.miss hok.check.state hok.check.ienv hnm hfind
  refine ⟨hok.check.state, Ext.refl _, rfl, hok.coh.push ci, Pushed.push _ _,
    ⟨c :: env.consts⟩, denoteFEnv_push hok.denote hci, ?_⟩
  simp only [ConLeche.installBasisDecl, hfindP, Option.isNone_none, if_true,
    bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Checker.lean:427-437 checkBasisDecl —
**install the pinned basis block**, the three records that reach it sharing
one body.  `Pushed` here is the block's length, which is the one place outside
the inductive route where a step installs more than one constant.

`sorry`: `BasisKind.declsA_run` and a list induction over
`installBasisDecl_bridge`, plus the `.quotK` precondition (`fe.find? eqName =
some eqA`) through `IFEnvOK`.  Task #97-P3-Checker's sorry list, item 15. -/
theorem checkBasisDecl_bridge {μ : CheckMode} {F : Nat} {env : Env}
    {fe fe' : IFEnv} {kind : BasisKind} {s s' : AState}
    (hok : FoldOK μ env fe s)
    (hrun : checkBasisDecl fe kind s = .ok (fe', s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env', denoteFEnv s'.store fe' = some env' ∧
        ConLeche.checkBasisDecl (m := CheckM) env kind = .ok env' := by
  sorry

/-! ## The axiom shapes

`stdAxiomOk`, `trustCompilerOk` and `ofReduceAxOk` (`Arena/DeclCheck.lean`)
are the `.axiomDecl` arm's four environment tests.  Each reads the environment
index and compares an interned literal, so each is `IFEnvOK` plus one intern
exactness; none of them calls the core — which is why each concludes
`s'.caches = s.caches` (task #97-P3-Checker-2: the arm needs it to rebuild
`CheckOK` after the test). -/

/-- con-leche: ConLeche/Kernel/DeclCheck.lean (stdAxiomOk) — the standard
axioms' environment shape test is con-leche's.

`sorry`: `IFEnvOK` at the `Iff`/`Nonempty` family lookups and
`IConstantVal.matchesPin` through `erasePwEq`.  Task #97-P3-Checker's sorry
list, item 16. -/
theorem stdAxiomOk_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : stdAxiomOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.stdAxiomOk env c := by
  sorry

/-- con-leche: ConLeche/Kernel/DeclCheck.lean (trustCompilerOk) — the
`Lean.trustCompiler` environment shape test is con-leche's.

`sorry`: `IFEnvOK` at the `True`/`True.intro` lookups and
`IConstantVal.matchesPin` through `erasePwEq`, exactly as `stdAxiomOk_run`.
Task #97-P3-Checker's sorry list, item 16. -/
theorem trustCompilerOk_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : trustCompilerOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.trustCompilerOk env c := by
  sorry

/-- con-leche: ConLeche/Kernel/DeclCheck.lean (ofReduceAxOk) — the
`Lean.ofReduceNat`/`ofReduceBool` environment shape test is con-leche's.

`sorry`: `ofReduceOp`'s handle comparison, then `IFEnvOK` at the pinned `Eq`
basis and at `reduceElemOk` / `reduceStoredOk`.  Task #97-P3-Checker's sorry
list, item 16. -/
theorem ofReduceAxOk_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : ofReduceAxOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.ofReduceAxOk env c := by
  sorry

end ConRon.Bridge
