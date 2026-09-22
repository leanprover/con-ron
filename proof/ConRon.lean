/-
con-ron's proof library: the Aeneas model of `crates/con-ron-core`
(`ConRon.Generated`, produced by `scripts/extract.sh`), the refinement tier
that is still stated about it (`ConRon.Refine`), and the `DeclC` dump of §3.6.

**Task #97-SWAP moved the checker.**  `crates/con-ron-core` is the ARENA now
(DESIGN.md §8): the `Expr`-tree checker `ConRon.Refine` was grown over is
deleted, so the 76 modules of that proof went to `ConRon.RefineOld`, out of
this import graph — `ConRon/RefineOld/README.md` says why they are kept and
what replaces them (§8.6's phases P3 and P5).  What is imported below is the
47 modules whose SUBJECT survived the swap, in tier order: the runtime
primitives (`Nat`, `HashMap`, `HashMap2`), the representation-free types
(`Name`, `Level`, `PropWhen`, `Expr`, `ExprOps`, `Env`, `FEnv`, `Canon`), the
`core_k` readers and shape guards, the pinned data (`Basis*`, `StdAxioms`,
`TrustAxioms`) and the `con-ron-pins/1` decoder (`Pins*`).  Those are exactly
the modules the arena still calls, so every lemma here is still a lemma about
code that ships.

`ConRon/Refine/README.md` has the tier map.  The arena checker itself is a
separate library root (`ConRonArena`, `ConRon.Arena.*`) and is not imported
here.

The task-#3/#5 spike (`ConRon.Spike.LevelName`) is *not* imported here: it
carries its own copy of the §3.2 pointer model -- `alloc.rc.Rc`, from a
spike crate compiled at `std::rc::Rc`, where the core's is `alloc.sync.Arc`
since task #45 -- and its own `Types`/`Funs` for the same declaration names,
which cannot live in one import graph.  It is a second library root
(`ConRonSpike` in `lakefile.toml`) and a plain `lake build` still elaborates
it.
-/
import ConRon.Generated
import ConRon.Refine.SimpSets
import ConRon.Refine.Scalars
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
