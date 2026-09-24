/-
con-ron's proof library: the Aeneas model of `crates/con-ron-core`
(`ConRon.Generated`, produced by `scripts/extract.sh`), the refinement tier
that is still stated about it (`ConRon.Refine`), and the `DeclC` dump of §3.6.

**Task #97-SWAP moved the checker.**  `crates/con-ron-core` is the ARENA now
(DESIGN.md §8): the `Expr`-tree checker `ConRon.Refine` was grown over is
deleted, and the modules of that proof, set aside as `ConRon.RefineOld` at
the swap, were deleted at task #97-PRUNE (they are in git history).  What is
imported below is the 46 modules whose SUBJECT survived the swap, in tier
order: the runtime primitives (`Nat`, `HashMap`, `HashMap2`), the
representation-free types (`Name`, `Level`, `PropWhen`, `Expr`, `ExprOps`,
`Env`, `FEnv`, `Canon`), the `core_k` readers and shape guards, the pinned
data (`Basis*`, `StdAxioms`, `TrustAxioms`) and the `con-ron-pins/1` decoder
(`Pins*`).  Every one of them is in `ConRon.Capstone`'s import closure
(checked mechanically at task #97-PRUNE), so every lemma here is on the
verified chain.

`ConRon/Refine/README.md` has the tier map.  The arena checker itself is a
separate library root (`ConRonArena`, `ConRon.Arena.*`) and is not imported
here.
-/
import ConRon.Generated
import ConRon.Refine.SimpSets
import ConRon.Refine.Abs
import ConRon.Refine.Nat
import ConRon.Refine.HashMap
import ConRon.Refine.HashMapWF
import ConRon.Refine.HashMap2
import ConRon.Refine.HashMap2WF
import ConRon.Refine.Name
import ConRon.Refine.Level
import ConRon.Refine.PropWhen
import ConRon.Refine.Expr
import ConRon.Refine.ExprOps
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.Env
import ConRon.Refine.FEnv
import ConRon.Refine.Canon
import ConRon.Refine.BasisTables
import ConRon.Refine.CoreKBase
import ConRon.Refine.BasisNames
import ConRon.Refine.BasisRaw
import ConRon.Refine.CoreKNames
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKLits
import ConRon.Refine.CoreKSupport
import ConRon.Refine.CoreKGuards
import ConRon.Refine.CoreKNatOps
import ConRon.Refine.PropRead
import ConRon.Refine.CoreKShapes
import ConRon.Refine.CoreKInfer
import ConRon.Refine.CoreKProj
import ConRon.Refine.CoreKPinned
import ConRon.Refine.PinsDec
import ConRon.Refine.PinsAscii
import ConRon.Refine.PinsBytes
import ConRon.Refine.PinsAbs
import ConRon.Refine.PinsSplit
import ConRon.Refine.PinsRecords
import ConRon.Refine.PinsRead
import ConRon.Refine.PinsRun
import ConRon.Refine.Pins
import ConRon.Refine.BasisPins
import ConRon.Refine.StdAxioms
import ConRon.Refine.TrustAxioms
import ConRon.Dump.Pins
