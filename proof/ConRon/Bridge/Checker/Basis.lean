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
  sorry

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
  sorry

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
  sorry

/-! ## The install -/

/-- con-leche: ConLeche/Kernel/Checker.lean:27-30 installBasisDecl — one
pinned constant, duplicate-checked.

`sorry`: `IFEnvOK`'s `hit`/`miss` pair at the duplicate test, then
`IFEnv.push`.  Task #97-P3-Checker's sorry list, item 15. -/
theorem installBasisDecl_bridge {μ : CheckMode} {F : Nat} {env : Env}
    {fe fe' : IFEnv} {ci : IConstantInfo} {c : ConstantInfo} {s s' : AState}
    (hok : FoldOK μ env fe s) (hci : Frontend.denoteCI s.store ci = some c)
    (hrun : installBasisDecl fe ci s = .ok (fe', s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env', denoteFEnv s'.store fe' = some env' ∧
        ConLeche.installBasisDecl (m := CheckM) env c = .ok env' := by
  sorry

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
