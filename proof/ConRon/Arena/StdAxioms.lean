/-
# `ConRon.Arena.StdAxioms` — the recognized standard axioms, over handles

The twin of `ConLeche/Kernel/StdAxioms.lean`: the eight reserved names, the
shape comparison a pin hit is decided by, and the pinned `Iff` / `Nonempty`
families with `propext` and `Classical.choice`.

Three deviations, each of them one of DESIGN §8's own rules:

1. **The pins are con-leche's VALUES, interned** (`Arena/Intern.lean`'s module
   note).  `iffRaw`, `iffA`, `propextA` … are hand-written and
   elaborator-spliced `ConstantInfo`/`ConstantVal` constants with no algorithm
   in them, and DESIGN §8.7 rules that (B) imports con-leche's
   representation-free data rather than copying it.  So each twin here is
   `internCI`/`internCV` of the con-leche constant it cites, and the startup
   walk (`internAllPins`, `Arena/Checker.lean`) puts them in the PERSISTENT
   tier before the fold runs.
2. **`erasePw` and `erasePwEq` collapse into one twin**, as
   `Arena/Canon.lean`'s comparisons do: con-leche carries the rebuild as the
   specification and the lockstep descent as the executed `@[csimp]` twin, and
   the arena writes one function per algorithm — the executed one.
3. **`stdAxiomOk` is `Arena/DeclCheck.lean`'s** `stdAxiomOkF`, which cites both:
   the arena has ONE environment type, the index (`Arena/Core.lean`'s
   deviation 1), so con-leche's `Env`/`FEnv` pairs collapse.
-/
import ConRon.Arena.Canon
import ConRon.Arena.Intern
import ConLeche.Kernel.StdAxioms

namespace ConRon.Arena

open ConLeche

/-! ## The reserved names, interned -/

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:38-39 propextName -/
def propextName : AM NIdx := pinPropext
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:41-42 choiceName -/
def choiceName : AM NIdx := pinChoice
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:44-45 iffName -/
def iffName : AM NIdx := pinIff
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:47-48 iffIntroName -/
def iffIntroName : AM NIdx := pinIffIntro
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:50-51 iffRecName -/
def iffRecName : AM NIdx := pinIffRec
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:53-54 nonemptyName -/
def nonemptyName : AM NIdx := pinNonempty
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:56-57 nonemptyIntroName -/
def nonemptyIntroName : AM NIdx := pinNonemptyIntro
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:59-60 nonemptyRecName -/
def nonemptyRecName : AM NIdx := pinNonemptyRec

/-! ## The shape comparison -/

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:62-113 Expr.erasePw
con-leche: ConLeche/Kernel/StdAxioms.lean:139-153 Expr.erasePwEq
`a.erasePw = b.erasePw`, decided in lockstep on two handles.  `erasePw`
preserves every node's constructor and its non-recursive fields (it only
resets the binder `pw` datum), so two erased terms are equal iff the originals
agree constructor by constructor down to their leaves — which is what this
descent tests.  The `pw` datum is the one thing not compared, which is exactly
what the erasure forgives (`StdAxioms.lean`'s "task #161 P5" note).

One twin, not two (module note 2): con-leche's rebuild is the specification
and this is the `@[csimp]` twin both binaries execute. -/
def erasePwEq : Nat → EIdx → EIdx → AM Bool
  | 0, _, _ => fail (.internal "fuel exhausted: erasePwEq")
  | fuel + 1, a, b => do
    match ← view a, ← view b with
    | .bvar i, .bvar j => pure (i == j)
    | .fvar i t, .fvar j t' =>
      if i == j then erasePwEq fuel t t' else pure false
    | .sort u, .sort v => pure (u == v)
    | .const n us, .const n' us' => pure (n == n' && us == us')
    | .app f x, .app f' x' =>
      if ← erasePwEq fuel f f' then erasePwEq fuel x x' else pure false
    | .lam t bd _, .lam t' bd' _ =>
      if ← erasePwEq fuel t t' then erasePwEq fuel bd bd' else pure false
    | .forallE t bd _, .forallE t' bd' _ =>
      if ← erasePwEq fuel t t' then erasePwEq fuel bd bd' else pure false
    | .letE t v bd, .letE t' v' bd' =>
      if ← erasePwEq fuel t t' then
        if ← erasePwEq fuel v v' then erasePwEq fuel bd bd' else pure false
      else pure false
    | .lit l, .lit l' => pure (l == l')
    | .proj s i e, .proj s' i' e' =>
      if s == s' && i == i' then erasePwEq fuel e e' else pure false
    | _, _ => pure false

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:115-117 ConstantVal.matchesPin
con-leche: ConLeche/Kernel/StdAxioms.lean:197-201 ConstantVal.matchesPinFast
Shape comparison for the standard pins: exact name, level parameters and
counts, type up to the `pw` datum.  A name comparison is a handle comparison
(DESIGN §8.3: `denoteN` is injective, so index inequality IS structural
inequality). -/
def IConstantVal.matchesPin (cv pin : IConstantVal) : AM Bool := do
  if cv.name == pin.name && cv.levelParams == pin.levelParams then
    erasePwEq coreWalkFuel cv.type pin.type
  else pure false

/-! ## The pins

Each is `internCI` / `internCV` of the con-leche constant it cites — the raw
pins hand-written through `ConLeche/Kernel/Basis/Builder.lean`, the annotated
ones computed from them by `#annotate_basis` / `#annotate_pins` while
con-leche elaborates.  The arena reads the results. -/

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:208-210 iffRaw -/
def iffRaw : AM IConstantInfo := internCI ConLeche.iffRaw
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:212-220 iffIntroRaw -/
def iffIntroRaw : AM IConstantInfo := internCI ConLeche.iffIntroRaw
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:222-227 iffRecIntro -/
def iffRecIntro : AM EIdx := internExpr ConLeche.iffRecIntro
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:229-239 iffRecRaw -/
def iffRecRaw : AM IConstantInfo := internCI ConLeche.iffRecRaw
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:241-243 iffFamily -/
def iffFamily : AM (List IConstantInfo) := internCIList ConLeche.iffFamily
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:245-252 propextRaw -/
def propextRaw : AM IConstantVal := internCV ConLeche.propextRaw
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:254-256 nonemptyRaw -/
def nonemptyRaw : AM IConstantInfo := internCI ConLeche.nonemptyRaw
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:258-264 nonemptyIntroRaw -/
def nonemptyIntroRaw : AM IConstantInfo := internCI ConLeche.nonemptyIntroRaw
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:266-278 nonemptyRecRaw -/
def nonemptyRecRaw : AM IConstantInfo := internCI ConLeche.nonemptyRecRaw
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:280-282 nonemptyFamily -/
def nonemptyFamily : AM (List IConstantInfo) :=
  internCIList ConLeche.nonemptyFamily
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:284-289 choiceRaw -/
def choiceRaw : AM IConstantVal := internCV ConLeche.choiceRaw

/-- con-leche: ConLeche/Kernel/BasisA.lean:29-49 _ — the annotated `Eq` pin,
`ConLeche.eqA` (spliced by `#annotate_basis`, so the citation is the command's
range), interned.  It is the comparand of every "requires the pinned `Eq`
basis" test in the checker. -/
def eqA : AM IConstantInfo := internCI ConLeche.eqA

/-- con-leche: ConLeche/Kernel/BasisA.lean:29-49 _ — the annotated `Nat` pin,
`ConLeche.natA`, interned. -/
def natA : AM IConstantInfo := internCI ConLeche.natA

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:299-305 _ — the annotated `Iff`
pin (`#annotate_basis`'s `iffA`), interned. -/
def iffA : AM IConstantInfo := internCI ConLeche.iffA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:299-305 _ — `iffIntroA`. -/
def iffIntroA : AM IConstantInfo := internCI ConLeche.iffIntroA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:299-305 _ — `iffRecA`. -/
def iffRecA : AM IConstantInfo := internCI ConLeche.iffRecA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:299-305 _ — `nonemptyA`. -/
def nonemptyA : AM IConstantInfo := internCI ConLeche.nonemptyA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:299-305 _ — `nonemptyIntroA`. -/
def nonemptyIntroA : AM IConstantInfo := internCI ConLeche.nonemptyIntroA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:299-305 _ — `nonemptyRecA`. -/
def nonemptyRecA : AM IConstantInfo := internCI ConLeche.nonemptyRecA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:307-310 _ — `propextA`. -/
def propextA : AM IConstantVal := internCV ConLeche.propextA
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:307-310 _ — `choiceA`. -/
def choiceA : AM IConstantVal := internCV ConLeche.choiceA

end ConRon.Arena
