/-
# `ConRon.Bridge.Inductives` — Theorem 1's inductive tier (index)

DESIGN §8.2's **Theorem 1** at the uniform inductive route (task #105):
`Arena/CheckDecl.lean`'s `.indDecl` arm past the pin recogniser — B-CORE's
`checkIndRoute` in `Bridge/Checker/Hyp.lean` — against con-leche 445b9cf4's
`checkDecl` arm (`Kernel/CheckDecl.lean`, `Kernel/Inductives/*`).  This tier
discharges the hypothesis `Hyp.lean` names `IndSpec` (`indSpec_of_bridge`).

## The modules, in dependency order

| module | what |
|---|---|
| `Records` | the twin records' denotations (`dShape`, `dCtx`, `dState`, …) and the `FOk` fuel calculus over `fueledOpsM` |
| `Run` | the pure grade: `PStep`, `PSpec`, answer relations, run forms of the store primitives |
| `Rel` | the core grade: `CSpec`, `CSpecF`, `InstRel`, `ProjOut`, `IndOut` |
| `BlockWF` | con-leche side only: `checkBlock` keeps `EnvWF` |
| `PosWalks` | the positivity walk's memoised leaves (`nestOcc`, `replaceFVars`, `replaceApps`, …) |
| `StructParts`, `StructInstall`, `FieldTele`, `SumInstall` | the shared generators, telescopes, constructor stage and projection table |
| `Positivity` | `nestPos` and its frames, the root, the seeds |
| `BlockParts`, `BlockRec` | the recogniser (two-sided) and the elimination guard |
| `BlockInstall` | the formers', constructors' and positivity stages |
| `ClassRead`, `RecCheck`, `GenRec` | the recursor pre-pass, class kit and generated recursor stage |
| `BlockTail` | `checkBlock_bridge`: the pass and the tail, producing `IndOut` |
| `Decl` | `checkIndRoute_bridge` and `indSpec_of_bridge` |
| `Axioms` | the trust census |

## Two grades

A twin that calls the knot (`inferTypeCore`, `isDefEqCore`, `whnf`,
`annotateCore`, `ensureSortCore`) or reads a verdict cache (`lvlEq?`) is CORE
grade: `CSpec`/`CSpecF`, invariant `CheckOK`, frame `CoreStep`, hypothesis
`CoreSpec`.  Everything else is PURE grade: `PSpec`, `StateOK`, `PStep`.  A
core-grade statement's pure side is the monad-generic con-leche function at
`fueledOpsM μ`, related through `FOk`; the tier's final `FOk` becomes
`IndSpec`'s `∃ F` by `checkDecl_datF`.
-/
import ConRon.Bridge.Inductives.Records
import ConRon.Bridge.Inductives.Run
import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.Inductives.BlockWF
import ConRon.Bridge.Inductives.PosWalks
import ConRon.Bridge.Inductives.StructParts
import ConRon.Bridge.Inductives.StructInstall
import ConRon.Bridge.Inductives.FieldTele
import ConRon.Bridge.Inductives.SumInstall
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.Inductives.BlockParts
import ConRon.Bridge.Inductives.BlockRec
import ConRon.Bridge.Inductives.BlockInstall
import ConRon.Bridge.Inductives.ClassRead
import ConRon.Bridge.Inductives.RecCheck
import ConRon.Bridge.Inductives.GenRec
import ConRon.Bridge.Inductives.BlockTail
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Inductives.Axioms
