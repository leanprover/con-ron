/-
con-ron's proof library: the Aeneas model of `crates/con-ron-core`
(`ConRon.Generated`, produced by `scripts/extract.sh`), the refinement tier
being grown on top of it (`ConRon.Refine`), and the `DeclC` dump of §3.6.

The task-#3/#5 spike (`ConRon.Spike.LevelName`) is *not* imported here: it
carries its own copy of the §3.2 pointer model -- `alloc.rc.Rc`, from a
spike crate compiled at `std::rc::Rc`, where the core's is `alloc.sync.Arc`
since task #45 -- and its own `Types`/`Funs` for the same declaration names,
which cannot live in one import graph.  It is a second library root
(`ConRonSpike` in `lakefile.toml`) and a plain `lake build` still elaborates
it.
-/
import ConRon.Generated
import ConRon.Refine.Abs
import ConRon.Refine.Name
import ConRon.Refine.Level
import ConRon.Refine.PropWhen
import ConRon.Refine.Expr
import ConRon.Refine.ExprOps
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.ExprOpsC
import ConRon.Refine.ExprOpsCSubst
import ConRon.Refine.ExprOpsCAbs
import ConRon.Refine.ExprOpsCGuards
import ConRon.Refine.HashMap
import ConRon.Refine.Core.Statements
import ConRon.Refine.Automation.Study
import ConRon.Refine.Core.Knot
import ConRon.Refine.HashMapWF
import ConRon.Refine.Nat
import ConRon.Refine.Env
import ConRon.Refine.FEnv
import ConRon.Refine.State
import ConRon.Refine.StateC
import ConRon.Refine.StateCResolve
import ConRon.Refine.BasisTables
import ConRon.Refine.CoreKBase
import ConRon.Refine.CoreKProj
import ConRon.Refine.BasisNames
import ConRon.Refine.CoreKNames
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKLits
import ConRon.Refine.CoreKSupport
import ConRon.Refine.CoreKGuards
import ConRon.Refine.CoreKNatOps
import ConRon.Refine.PropRead
import ConRon.Refine.CoreKShapes
import ConRon.Refine.CoreKInfer
import ConRon.Refine.CoreKPinned
import ConRon.Refine.IndAbs
import ConRon.Refine.IndStructParts
import ConRon.Refine.IndSumParts
import ConRon.Refine.IndNativeParts
import ConRon.Refine.IndStructInstall
import ConRon.Refine.IndSumInstall
import ConRon.Refine.IndNativeInstall
import ConRon.Refine.IndModeled
import ConRon.Refine.IndSpec
import ConRon.Refine.IndIngredients
import ConRon.Refine.IndC
import ConRon.Refine.Pins
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.Core.Arms.Bridge
import ConRon.Refine.Core.Arms.Shared
import ConRon.Refine.Core.Arms.Certs
import ConRon.Refine.Core.Arms.InferTele
import ConRon.Refine.Core.Arms.DefEq
import ConRon.Refine.Core.Arms.DefEqStruct
import ConRon.Refine.Core.Arms.Arms
import ConRon.Refine.Core.Arms.Iota
import ConRon.Refine.Core.Arms.Major
import ConRon.Refine.Core.Arms.Infer
import ConRon.Refine.Core.Arms.InferIO
import ConRon.Refine.Core.Arms.Annotate
import ConRon.Refine.Core.Arms.Lits
import ConRon.Refine.Core.Arms.Whnf
import ConRon.Refine.Core.Arms.WhnfCore
import ConRon.Refine.Core.Arms.App
import ConRon.Refine.Core.Arms.InferSpine
import ConRon.Refine.Core.Arms.InferSpineIO
import ConRon.Dump.Pins
import ConRon.Refine.TypeChecker
import ConRon.Refine.IndSpec
import ConRon.Refine.CheckerC
import ConRon.Refine.BasisPins
import ConRon.Refine.StdAxioms
import ConRon.Refine.TrustAxioms
import ConRon.Refine.CheckerBase
import ConRon.Refine.DeclCheck
import ConRon.Refine.CheckerPinned
import ConRon.Refine.CheckerSplit
import ConRon.Refine.Checker
import ConRon.Refine.CheckerPins
import ConRon.Refine.PinsWF
import ConRon.Refine.CheckerDecl
import ConRon.Refine.Installed
import ConRon.Refine.Main
