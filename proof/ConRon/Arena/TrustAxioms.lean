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

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:51-52 trueName -/
def trueName : AM NIdx := pin ConLeche.trueName
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:54-55 trueIntroName -/
def trueIntroName : AM NIdx := pin ConLeche.trueIntroName
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:57-58 trustCompilerName -/
def trustCompilerName : AM NIdx := pin ConLeche.trustCompilerName
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:60-61 reduceNatName -/
def reduceNatName : AM NIdx := pin ConLeche.reduceNatName
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:63-64 reduceBoolName -/
def reduceBoolName : AM NIdx := pin ConLeche.reduceBoolName
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:66-67 ofReduceNatName -/
def ofReduceNatName : AM NIdx := pin ConLeche.ofReduceNatName
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:69-70 ofReduceBoolName -/
def ofReduceBoolName : AM NIdx := pin ConLeche.ofReduceBoolName

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:72-73 reduceOpNames — the
reduce operations pinned at their `opaque` install. -/
def reduceOpNames : AM (List NIdx) := do
  let a ← reduceNatName
  let b ← reduceBoolName
  pure [a, b]

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:75-77 ofReduceOp — the reduce
operation an `ofReduce*` axiom speaks about.  con-leche's `if n =
ofReduceNatName` is a handle comparison here. -/
def ofReduceOp (n : NIdx) : AM NIdx := do
  let orn ← ofReduceNatName
  if n == orn then reduceNatName else reduceBoolName

/-! ## The pinned shapes -/

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:88-89 trueCvA -/
def trueCvA : AM IConstantVal := internCV ConLeche.trueCvA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:91-92 trueIntroCvA -/
def trueIntroCvA : AM IConstantVal := internCV ConLeche.trueIntroCvA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:94-95 trustCompilerA -/
def trustCompilerA : AM IConstantVal := internCV ConLeche.trustCompilerA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:97-98 boolCvA -/
def boolCvA : AM IConstantVal := internCV ConLeche.boolCvA

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:100-102 reduceElemName — the
element inductive of a reduce operation. -/
def reduceElemName (c : NIdx) : AM NIdx := do
  let rn ← reduceNatName
  if c == rn then pin ConLeche.natName else boolName

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:104-106 reduceElemTy — the
element type of a reduce operation, as the pinned constant. -/
def reduceElemTy (c : NIdx) : AM EIdx := do
  constE (← reduceElemName c)

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:108-110 reduceOpRaw — the raw
pinned type of `Lean.reduceNat` / `Lean.reduceBool`.  The con-leche constant
is a function of the operation's `Name`, so the twin reads the handle back to
call it and interns the result. -/
def reduceOpRaw (c : NIdx) : AM IConstantVal := do
  internCV (ConLeche.reduceOpRaw (← readName c))

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:112-122 ofReduceRaw — the raw
pinned type of `Lean.ofReduceNat` / `Lean.ofReduceBool`. -/
def ofReduceRaw (n : NIdx) : AM IConstantVal := do
  internCV (ConLeche.ofReduceRaw (← readName n))

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:139-141 _ — the annotated
pinned type of `Lean.reduceNat` (`#annotate_pins`' `reduceNatCvA`). -/
def reduceNatCvA : AM IConstantVal := internCV ConLeche.reduceNatCvA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:139-141 _ — `reduceBoolCvA`. -/
def reduceBoolCvA : AM IConstantVal := internCV ConLeche.reduceBoolCvA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:143-146 _ — `ofReduceNatA`. -/
def ofReduceNatA : AM IConstantVal := internCV ConLeche.ofReduceNatA
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:143-146 _ — `ofReduceBoolA`. -/
def ofReduceBoolA : AM IConstantVal := internCV ConLeche.ofReduceBoolA

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:148-150 reduceOpCvA — the
annotated pinned type of a reduce operation. -/
def reduceOpCvA (c : NIdx) : AM IConstantVal := do
  let rn ← reduceNatName
  if c == rn then reduceNatCvA else reduceBoolCvA

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:152-154 ofReducePinA — the
annotated pin an `ofReduce*` axiom is matched against. -/
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

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:202-207 reduceDeclPin — the
pinned defining expression of a reduce operation. -/
def reduceDeclPin (c : NIdx) : AM EIdx := do
  let rn ← reduceNatName
  if c == rn then reduceNatDeclPin else reduceBoolDeclPin

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:215-218 reduceCertVar — the
identity certificate's variable: `fvar 0` at the element type. -/
def reduceCertVar (c : NIdx) : AM EIdx := do
  internE (.fvar 0 (← reduceElemTy c))

end ConRon.Arena
