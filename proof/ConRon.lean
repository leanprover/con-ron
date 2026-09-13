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
import ConRon.Refine.Pins
import ConRon.Dump.Read
