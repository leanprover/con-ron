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

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:32-51 checkStructDomsAt
con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:27-36 checkStructDomsAtF
con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:38-48 checkStructDomsAtFA
The first `j` parameter domains are definitionally the declared ones.  A
`Unit` answer: what it claims is that con-leche's own check SUCCEEDS at some
fuel.

`sorry`: a `Nat` recursion over `CoreSpec.knot`'s `defeq` slot
(`Bridge/Core/Knot.lean`), with `unwrapOr`'s spec
(`Bridge/Checker/Base.lean`) at the two list indexings.  This is the tier's
first `KnotSpec` consumer and its shape is the one the other eleven copy. -/
theorem checkStructDomsAt_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (off : Nat) (fvs doms : List EIdx)
    (fvsP domsP : List Expr) (j : Nat) :
    CSpec μ env fe
      (fun st => Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st doms = some domsP ∧
        denoteFEnv st fe = some env)
      (Arena.checkStructDomsAt μ fe off fvs doms j)
      (fun _ _ => ∃ F, ConLeche.checkStructDomsAt (ConLeche.fueledOps μ F)
        env off fvsP domsP j = (.ok () : CheckM Unit)) := by
  sorry

/-! ## The projection table -/

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:53-86 checkStructProjTable
con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:73-95 checkStructProjTableF
**The structure-like block's projection table**: one constant per structure
(task #175 S1), carrying the fields' bodies off the annotated constructor type
and the guard levels the constructors' stage measured.

`sorry`: `structProjBodies_spec` (`Bridge/Inductives/StructParts.lean`), the
`IProjTable` record's denotation (`Bridge/Rel.lean`'s `denoteProjTable`), and
`IFEnv.push`'s own two lemmas — `IFEnvCoh` is preserved by `push` and `Pushed`
is `⟨[ci], rfl⟩`.  The `denoteFEnv` clause is the push's `denoteCI` at the new
`.projInfo` row. -/
theorem checkStructProjTable_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (T C : NIdx) (TP CP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF : Nat) (resSort : LIdx)
    (resSortP : Level) (guards : List LIdx) (guardsP : List Level) (off : Nat)
    (cvCa : IConstantVal) (cvCaP : ConstantVal) :
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
          guardsP off cvCaP env = .ok env')) := by
  sorry

end ConRon.Bridge.Inductives
