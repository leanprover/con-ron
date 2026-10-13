/-
# `ConRon.Arena.TrustAxioms` — the compiler-trust family, over handles

The twin of `ConLeche/Kernel/TrustAxioms.lean` and of
`ConLeche/Kernel/TrustPins.lean`: the reserved names of `Lean.trustCompiler`,
`Lean.reduceNat` / `Lean.reduceBool` and the two `ofReduce*` axioms, the
pinned shapes they are matched against, and the pinned defining expression
the reduce opaques' install compares their stored value with.

Same three deviations as `Arena/StdAxioms.lean`: the pins are con-leche's own
values interned (`Arena/Intern.lean`), and the four environment PREDICATES —
`trustCompilerOk`, `reduceStoredOk`, `reduceElemOk`, `ofReduceAxOk`,
`reducePinGuard` — are `Arena/DeclCheck.lean`'s `…F` twins, which cite both
halves of con-leche's `Env`/`FEnv` pair.
-/
import ConRon.Arena.StdAxioms
import ConLeche.Kernel.TrustAxioms

namespace ConRon.Arena

open ConLeche

/-! ## The reserved names, interned -/

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:49-50 trueName -/
def trueName : AM NIdx := pinTrue
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:52-53 trueIntroName -/
def trueIntroName : AM NIdx := pinTrueIntro
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:55-56 trustCompilerName -/
def trustCompilerName : AM NIdx := pinTrustCompiler
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:58-59 reduceNatName -/
def reduceNatName : AM NIdx := pinReduceNat
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:61-62 reduceBoolName -/
def reduceBoolName : AM NIdx := pinReduceBool
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:64-65 ofReduceNatName -/
def ofReduceNatName : AM NIdx := pinOfReduceNat
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:67-68 ofReduceBoolName -/
def ofReduceBoolName : AM NIdx := pinOfReduceBool

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:70-71 reduceOpNames — the
reduce operations pinned at their `opaque` install. -/
def reduceOpNames : AM (List NIdx) := do
  let a ← reduceNatName
  let b ← reduceBoolName
  pure [a, b]

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:73-75 ofReduceOp — the reduce
operation an `ofReduce*` axiom speaks about.  con-leche's `if n =
ofReduceNatName` is a handle comparison here. -/
def ofReduceOp (n : NIdx) : AM NIdx := do
  let orn ← ofReduceNatName
  if n == orn then reduceNatName else reduceBoolName

/-! ## The pinned shapes -/

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:83-84 trueCvA -/
def trueCvA : AM IConstantVal := internCV ConLeche.trueCvA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:86-87 trueIntroCvA -/
def trueIntroCvA : AM IConstantVal := internCV ConLeche.trueIntroCvA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:89-90 trustCompilerA -/
def trustCompilerA : AM IConstantVal := internCV ConLeche.trustCompilerA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:92-93 boolCvA -/
def boolCvA : AM IConstantVal := internCV ConLeche.boolCvA

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:95-97 reduceElemName — the
element inductive of a reduce operation. -/
def reduceElemName (c : NIdx) : AM NIdx := do
  let rn ← reduceNatName
  if c == rn then pinNat else boolName

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:99-101 reduceElemTy — the
element type of a reduce operation, as the pinned constant. -/
def reduceElemTy (c : NIdx) : AM EIdx := do
  constE (← reduceElemName c)

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:119-120 reduceNatCvA — the
pinned type of `Lean.reduceNat`. -/
def reduceNatCvA : AM IConstantVal := internCV ConLeche.reduceNatCvA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:122-123 reduceBoolCvA -/
def reduceBoolCvA : AM IConstantVal := internCV ConLeche.reduceBoolCvA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:125-126 ofReduceNatA -/
def ofReduceNatA : AM IConstantVal := internCV ConLeche.ofReduceNatA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:128-129 ofReduceBoolA -/
def ofReduceBoolA : AM IConstantVal := internCV ConLeche.ofReduceBoolA

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:131-133 reduceOpCvA — the
pinned type of a reduce operation. -/
def reduceOpCvA (c : NIdx) : AM IConstantVal := do
  let rn ← reduceNatName
  if c == rn then reduceNatCvA else reduceBoolCvA

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:135-137 ofReducePinA — the
pin an `ofReduce*` axiom is matched against. -/
def ofReducePinA (n : NIdx) : AM IConstantVal := do
  let orn ← ofReduceNatName
  if n == orn then ofReduceNatA else ofReduceBoolA

/-! ## The reduce-operation install pin -/

/-- con-leche: ConLeche/Kernel/TrustPins.lean:42-43 reduceBoolDeclPin —
`Lean.reduceBool`'s pinned value, `fun (b : Bool) => b`. -/
def reduceBoolDeclPin : AM EIdx := internExpr ConLeche.reduceBoolDeclPin

/-- con-leche: ConLeche/Kernel/TrustPins.lean:45-46 reduceNatDeclPin —
`Lean.reduceNat`'s pinned value, `fun (n : Nat) => n`. -/
def reduceNatDeclPin : AM EIdx := internExpr ConLeche.reduceNatDeclPin

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:185-190 reduceDeclPin — the
pinned defining expression of a reduce operation. -/
def reduceDeclPin (c : NIdx) : AM EIdx := do
  let rn ← reduceNatName
  if c == rn then reduceNatDeclPin else reduceBoolDeclPin

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:198-201 reduceCertVar — the
identity certificate's variable: `fvar 0` at the element type. -/
def reduceCertVar (c : NIdx) : AM EIdx := do
  internE (.fvar 0 (← reduceElemTy c))

end ConRon.Arena
