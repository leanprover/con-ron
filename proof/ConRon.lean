/-
con-ron's proof library: the Aeneas model of `crates/con-ron-core`
(`ConRon.Generated`, produced by `scripts/extract.sh`), the refinement tier
being grown on top of it (`ConRon.Refine`), and the `DeclC` dump of §3.6.

The task-#3/#5 spike (`ConRon.Spike.LevelName`) is *not* imported here: it
carries its own copy of the `Rc` model of §3.2, and two top-level
`alloc.rc.Rc`s cannot live in one import graph.  It is a second library root
(`ConRonSpike` in `lakefile.toml`) and a plain `lake build` still elaborates
it.
-/
import ConRon.Generated
import ConRon.Refine.Smoke
import ConRon.Refine.Nat
import ConRon.Dump.Read
