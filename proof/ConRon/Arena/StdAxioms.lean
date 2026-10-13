/-
# `ConRon.Arena.StdAxioms` — the recognized standard axioms, over handles

The twin of `ConLeche/Kernel/StdAxioms.lean`: the eight reserved names, the
shape comparison a pin hit is decided by, and the pinned `Iff` / `Nonempty`
families with `propext` and `Classical.choice`.

Two deviations, each of them one of DESIGN §8's own rules:

1. **The pins are con-leche's VALUES, interned** (`Arena/Intern.lean`'s module
   note).  `iffA`, `propextA` … are hand-written and
   elaborator-spliced `ConstantInfo`/`ConstantVal` constants with no algorithm
   in them, and DESIGN §8.7 rules that (B) imports con-leche's
   representation-free data rather than copying it.  So each twin here is
   `internCI`/`internCV` of the con-leche constant it cites, and the startup
   walk (`internAllPins`, `Arena/Checker.lean`) puts them in the PERSISTENT
   tier before the fold runs.
2. **`stdAxiomOk` is `Arena/DeclCheck.lean`'s** `stdAxiomOkF`, which cites both:
   the arena has ONE environment type, the index (`Arena/Core.lean`'s
   deviation 1), so con-leche's `Env`/`FEnv` pairs collapse.
-/
import ConRon.Arena.Canon
import ConRon.Arena.Intern
import ConLeche.Kernel.StdAxioms

namespace ConRon.Arena

open ConLeche

/-! ## The reserved names, interned -/

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:33-34 propextName -/
def propextName : AM NIdx := pinPropext
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:36-37 choiceName -/
def choiceName : AM NIdx := pinChoice
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:39-40 iffName -/
def iffName : AM NIdx := pinIff
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:42-43 iffIntroName -/
def iffIntroName : AM NIdx := pinIffIntro
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:45-46 iffRecName -/
def iffRecName : AM NIdx := pinIffRec
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:48-49 nonemptyName -/
def nonemptyName : AM NIdx := pinNonempty
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:51-52 nonemptyIntroName -/
def nonemptyIntroName : AM NIdx := pinNonemptyIntro
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:54-55 nonemptyRecName -/
def nonemptyRecName : AM NIdx := pinNonemptyRec

/-! ## The shape comparison -/

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:57-91 ConstantVal.matchesPin —
shape comparison for the standard pins: exact name, level parameters and type.
Since con-leche's task #342 the comparison is plain equality (no binder datum
is left to forgive), and over handles it is handle equality: `denoteE` and
`denoteN` are injective (DESIGN §8.3), so index equality IS structural
equality. -/
def IConstantVal.matchesPin (cv pin : IConstantVal) : AM Bool :=
  pure (cv.name == pin.name && cv.levelParams == pin.levelParams &&
    cv.type == pin.type)

/-! ## The pins

Each is `internCI` / `internCV` of the con-leche constant it cites, hand-written
through `ConLeche/Kernel/Basis/Builder.lean`.  The arena reads the results. -/

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:93-95 iffA -/
def iffA : AM IConstantInfo := internCI ConLeche.iffA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:97-105 iffIntroA -/
def iffIntroA : AM IConstantInfo := internCI ConLeche.iffIntroA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:114-124 iffRecA -/
def iffRecA : AM IConstantInfo := internCI ConLeche.iffRecA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:126-133 propextA -/
def propextA : AM IConstantVal := internCV ConLeche.propextA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:135-137 nonemptyA -/
def nonemptyA : AM IConstantInfo := internCI ConLeche.nonemptyA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:139-145 nonemptyIntroA -/
def nonemptyIntroA : AM IConstantInfo := internCI ConLeche.nonemptyIntroA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:147-159 nonemptyRecA -/
def nonemptyRecA : AM IConstantInfo := internCI ConLeche.nonemptyRecA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:161-166 choiceA -/
def choiceA : AM IConstantVal := internCV ConLeche.choiceA

/-- con-leche: ConLeche/Kernel/BasisA.lean:29-44 _ — the stored `Eq` pin,
`ConLeche.eqA` (spliced by `#stored_basis`, so the citation is the command's
range), interned.  It is the comparand of every "requires the pinned `Eq`
basis" test in the checker. -/
def eqA : AM IConstantInfo := internCI ConLeche.eqA

/-- con-leche: ConLeche/Kernel/BasisA.lean:29-44 _ — the stored `Nat` pin,
`ConLeche.natA`, interned. -/
def natA : AM IConstantInfo := internCI ConLeche.natA

end ConRon.Arena
