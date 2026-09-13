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
import ConRon.Refine.HashMap
import ConRon.Refine.Core.Statements
import ConRon.Refine.HashMapWF
import ConRon.Refine.Nat
import ConRon.Refine.Env
import ConRon.Refine.FEnv
import ConRon.Refine.State
import ConRon.Refine.BasisTables
import ConRon.Refine.Pins
import ConRon.Dump.Read
