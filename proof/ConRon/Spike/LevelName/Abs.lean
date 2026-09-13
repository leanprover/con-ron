/-
The abstraction functions for the task-#3 scale spike (`spikes/level-name`, removed at task #76):
they map the Aeneas model of the Rust `Name`/`Level` trees onto con-leche's
own `ConLeche.Name` and `ConLeche.Level` (DESIGN.md §1, §3.2, §3.3).

What they forget, in the order §3.3 lists it:
* the `Rc` indirection -- `alloc.rc.Rc T` *is* `T` in the model
  (`TypesExternal.lean`), so there is nothing to peel;
* the cached hash word (`NameNode.hash`, `LevelNode.hash`): con-leche keeps it
  in a `@[computed_field]`, which is a function of the value and invisible to
  every statement, so `abs` simply drops it;
* the machine-word representations: a string is a `Vec<u32>` of code points in
  the port and a `String` in con-leche; `Name.num`'s index is a `u64` there and
  a `Nat` here.

Definitions only -- the refinement theorems that use them come next.
-/
import ConLeche.Kernel.Level
import ConRon.Spike.LevelName.Types

open Aeneas Aeneas.Std

namespace ConRon.Spike.LevelName

/-- A port-side string (`Vec<u32>` of code points, DESIGN.md §3.3) as a Lean
`String`.  `Char.ofNat` sends a value that is not a valid code point to
`'\0'`; the port only ever stores code points that came from a `String`, so on
the image of the parser this is a bijection. -/
def absString (s : alloc.vec.Vec Std.U32) : String :=
  String.ofList (s.val.map fun c => Char.ofNat c.val)

/- `ConLeche/Kernel/Name.lean:34` -- the Rust `Name` tree as a `ConLeche.Name`. -/
mutual

def absName : level_name.name.Name → ConLeche.Name
  | .mk nd => absNameNode nd

def absNameNode : level_name.name.NameNode → ConLeche.Name
  | .mk _hash k => absNameKind k

def absNameKind : level_name.name.NameKind → ConLeche.Name
  | .Anonymous => .anonymous
  | .Str pre s => .str (absName pre) (absString s)
  | .Num pre n => .num (absName pre) n.val

end

/- `ConLeche/Kernel/Expr.lean:40` -- the Rust `Level` tree as a
`ConLeche.Level`. -/
mutual

def absLevel : level_name.level.Level → ConLeche.Level
  | .mk nd => absLevelNode nd

def absLevelNode : level_name.level.LevelNode → ConLeche.Level
  | .mk _hash k => absLevelKind k

def absLevelKind : level_name.level.LevelKind → ConLeche.Level
  | .Zero => .zero
  | .Succ u => .succ (absLevel u)
  | .Max u v => .max (absLevel u) (absLevel v)
  | .Imax u v => .imax (absLevel u) (absLevel v)
  | .Param n => .param (absName n)

end

/-- A `Vec<Level>` (the port's stand-in for a `List Level`, DESIGN.md §3.4) as
a `List ConLeche.Level`. -/
def absLevels (us : alloc.vec.Vec level_name.level.Level) : List ConLeche.Level :=
  us.val.map absLevel

end ConRon.Spike.LevelName
