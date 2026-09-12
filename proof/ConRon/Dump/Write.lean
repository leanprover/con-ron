/-
The `con-ron-decls/1` writer (DESIGN.md §3.6, task #10).

`dumpDecls : List DeclC → String` writes con-leche's parsed declaration list
in the text format `ConRon/Dump/FORMAT.md` specifies: one record per line,
one dense id space per record kind, shared nodes written once.  The Rust core
reads the result; `ConRon/Dump/Read.lean` reads it back in Lean, which is what
validates the format before any Rust exists.

`dumpPins : List NatOpPinSet → String` (task #31) writes the sibling format
`con-ron-pins/1` (FORMAT.md §7) with the same monad and the same interning
tables, so an `E` id means the same thing in both files.

Nothing here is a theorem: this is a test and porting tool.
-/
import ConLeche.Cached.ParsedC
import ConLeche.Kernel.NatOpPinSet

namespace ConRon.Dump

open ConLeche
open ConLeche.Cached

/-- The version header, the whole first line of a declaration dump. -/
def header : String := "con-ron-decls/1"

/-- The version header of the **sibling** pin dump (`FORMAT.md` §7).  The two
files share every record kind below the payload — `N`, `L`, `W`, `E`, the
escape, the id invariant — and differ in the header, the payload record (`S`
instead of `D`) and what the footer counts. -/
def pinsHeader : String := "con-ron-pins/1"

/-! ## Scalars -/

/-- `false`/`true` as `0`/`1`. -/
def boolStr (b : Bool) : String := if b then "1" else "0"

/-- Lowercase hexadecimal digits of `n`, prepended to `acc`. -/
def toHexGo (n : Nat) (acc : String) : String :=
  if _h : n = 0 then acc
  else
    let d := n % 16
    let c := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
    toHexGo (n / 16) (String.singleton c ++ acc)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _h) (by decide)

/-- Lowercase hexadecimal, no leading zeros (`0` is `"0"`). -/
def toHex (n : Nat) : String := if n == 0 then "0" else toHexGo n ""

/-- One code point, escaped: a literal printable non-backslash ASCII byte, or
`\<hex>;`.  Every code point round-trips and the result is space-free, which is
what lets a record be split on spaces. -/
def escChar (c : Char) : String :=
  let n := c.toNat
  if 0x21 ≤ n && n ≤ 0x7e && n ≠ 0x5c then String.singleton c
  else "\\" ++ toHex n ++ ";"

/-- A string, escaped (no length prefix; see `strField`). -/
def escapeString (s : String) : String :=
  s.foldl (fun acc c => acc ++ escChar c) ""

/-- A string as the two fields the format uses: code-point count, then the
escaped text (empty exactly when the count is `0`). -/
def strField (s : String) : String :=
  toString s.length ++ " " ++ escapeString s

/-- A counted id list: the length, then the ids. -/
def idList (ids : List Nat) : String :=
  ids.foldl (fun acc i => acc ++ " " ++ toString i) (toString ids.length)

/-- `ReducibilityHint` inline (`ConLeche/Kernel/Env.lean:315`). -/
def hintStr : ReducibilityHint → String
  | .opaque => "o"
  | .abbrev => "b"
  | .regular h => "r " ++ toString h

/-- `BasisKind` inline (`ConLeche/Kernel/Env.lean:353`). -/
def basisStr : BasisKind → String
  | .eqK => "eq"
  | .natK => "nat"
  | .punitK => "punit"
  | .emptyK => "empty"
  | .falseK => "false"
  | .quotK => "quot"

/-! ## The writer's state -/

/-- The emission state: the output lines and one interning table (or one
counter) per id space.  `Name`, `Level`, `PropWhen` and `Expr` are interned —
that is what keeps the DAG a DAG — and `ConstantVal`, `RecRule`, `IndCaps`,
`ProjTable` and `ConstantInfo` are merely numbered, each occurring once. -/
structure WState where
  buf : Array String := #[]
  names : Std.HashMap Name Nat := {}
  levels : Std.HashMap Level Nat := {}
  pws : Std.HashMap PropWhen Nat := {}
  exprs : Std.HashMap Expr Nat := {}
  nV : Nat := 0
  nR : Nat := 0
  nC : Nat := 0
  nP : Nat := 0
  nI : Nat := 0
  nD : Nat := 0
  nS : Nat := 0

/-- The writer's monad. -/
abbrev W := StateM WState

@[inline] def emit (s : String) : W Unit :=
  modify fun st => { st with buf := st.buf.push s }

/-! ## Names, levels, the zero-ness datum -/

/-- Emit a name (and its prefix), returning its id. -/
partial def wName (n : Name) : W Nat := do
  match (← get).names[n]? with
  | some i => return i
  | none =>
    let body ← match n with
      | .anonymous => pure "a"
      | .str p s => do
        let pi ← wName p
        pure ("s " ++ toString pi ++ " " ++ strField s)
      | .num p k => do
        let pi ← wName p
        pure ("n " ++ toString pi ++ " " ++ toString k)
    let st ← get
    let id := st.names.size
    set { st with names := st.names.insert n id,
                  buf := st.buf.push ("N " ++ toString id ++ " " ++ body) }
    return id

/-- Emit a level, returning its id. -/
partial def wLevel (u : Level) : W Nat := do
  match (← get).levels[u]? with
  | some i => return i
  | none =>
    let body ← match u with
      | .zero => pure "z"
      | .succ v => do let i ← wLevel v; pure ("s " ++ toString i)
      | .max a b => do
        let i ← wLevel a; let j ← wLevel b
        pure ("m " ++ toString i ++ " " ++ toString j)
      | .imax a b => do
        let i ← wLevel a; let j ← wLevel b
        pure ("i " ++ toString i ++ " " ++ toString j)
      | .param n => do let i ← wName n; pure ("p " ++ toString i)
    let st ← get
    let id := st.levels.size
    set { st with levels := st.levels.insert u id,
                  buf := st.buf.push ("L " ++ toString id ++ " " ++ body) }
    return id

/-- Emit a `PropWhen` through its public API (`toList?`), returning its id. -/
def wPw (pw : PropWhen) : W Nat := do
  match (← get).pws[pw]? with
  | some i => return i
  | none =>
    let body ← match pw.toList? with
      | none => pure "n"
      | some ps => do
        let ids ← ps.mapM wName
        pure ("z " ++ idList ids)
    let st ← get
    let id := st.pws.size
    set { st with pws := st.pws.insert pw id,
                  buf := st.buf.push ("W " ++ toString id ++ " " ++ body) }
    return id

/-! ## Expressions

The walk is an explicit worklist, not recursion: con-leche's terms reach
application spines and `let` chains tens of thousands of nodes deep, and a
recursive writer overflows the stack on the bigger fixtures. -/

/-- The id of an already-emitted node. -/
@[inline] def eid (e : Expr) : W Nat := do
  return (← get).exprs.getD e 0

/-- Emit one node, all of whose children are already emitted. -/
def emitExprNode (e : Expr) : W Unit := do
  let body ← match e with
    | .bvar i => pure ("b " ++ toString i)
    | .fvar idx ty => do
      let t ← eid ty
      pure ("v " ++ toString idx ++ " " ++ toString t)
    | .sort u => do let l ← wLevel u; pure ("s " ++ toString l)
    | .const n us => do
      let ni ← wName n
      let ls ← us.mapM wLevel
      pure ("c " ++ toString ni ++ " " ++ idList ls)
    | .app f a => do
      let fi ← eid f; let ai ← eid a
      pure ("a " ++ toString fi ++ " " ++ toString ai)
    | .lam ty b m => do
      let t ← eid ty; let bi ← eid b; let p ← wPw m.pw
      pure ("l " ++ toString t ++ " " ++ toString bi ++ " " ++ toString p)
    | .forallE ty b m => do
      let t ← eid ty; let bi ← eid b; let p ← wPw m.pw
      pure ("f " ++ toString t ++ " " ++ toString bi ++ " " ++ toString p)
    | .letE ty v b => do
      let t ← eid ty; let vi ← eid v; let bi ← eid b
      pure ("t " ++ toString t ++ " " ++ toString vi ++ " " ++ toString bi)
    | .lit (.natVal n) => pure ("n " ++ toString n)
    | .lit (.strVal s) => pure ("g " ++ strField s)
    | .proj sn i s => do
      let ni ← wName sn; let si ← eid s
      pure ("p " ++ toString ni ++ " " ++ toString i ++ " " ++ toString si)
  let st ← get
  let id := st.exprs.size
  set { st with exprs := st.exprs.insert e id,
                buf := st.buf.push ("E " ++ toString id ++ " " ++ body) }

/-- The worklist loop: `(e, false)` means "visit", `(e, true)` means "children
done, emit". -/
partial def wExprGo (stack : Array (Expr × Bool)) : W Unit := do
  if h : 0 < stack.size then
    let (e, done) := stack[stack.size - 1]'(by omega)
    let stack := stack.pop
    if (← get).exprs.contains e then
      wExprGo stack
    else if done then
      emitExprNode e
      wExprGo stack
    else
      let stack := stack.push (e, true)
      let stack := match e with
        | .bvar _ | .sort _ | .const _ _ | .lit _ => stack
        | .fvar _ ty => stack.push (ty, false)
        | .app f a => (stack.push (f, false)).push (a, false)
        | .lam ty b _ => (stack.push (ty, false)).push (b, false)
        | .forallE ty b _ => (stack.push (ty, false)).push (b, false)
        | .letE ty v b => ((stack.push (ty, false)).push (v, false)).push (b, false)
        | .proj _ _ s => stack.push (s, false)
      wExprGo stack
  else
    return ()

/-- Emit an expression DAG, returning the root's id. -/
def wExpr (e : Expr) : W Nat := do
  wExprGo #[(e, false)]
  eid e

/-! ## The records above expressions -/

/-- `ConstantVal` (`ConLeche/Kernel/Env.lean:197`). -/
def wCV (cv : ConstantVal) : W Nat := do
  let ni ← wName cv.name
  let lps ← cv.levelParams.mapM wName
  let ti ← wExpr cv.type
  let st ← get
  let id := st.nV
  set { st with nV := id + 1,
                buf := st.buf.push ("V " ++ toString id ++ " " ++ toString ni
                  ++ " " ++ idList lps ++ " " ++ toString ti) }
  return id

/-- `RecRule` with its `RecRuleFire` inline (`ConLeche/Kernel/Env.lean:255`). -/
def wRule (r : RecRule) : W Nat := do
  let ci ← wName r.ctor
  let fire ← match r.fire with
    | .inert => pure "i"
    | .plain => pure "p"
    | .nested lvls pins => do
      let ls ← lvls.mapM wLevel
      let ps ← pins.mapM wExpr
      pure ("n " ++ idList ls ++ " " ++ idList ps)
  let rhs ← wExpr r.rhs
  let st ← get
  let id := st.nR
  set { st with nR := id + 1,
                buf := st.buf.push ("R " ++ toString id ++ " " ++ toString ci
                  ++ " " ++ toString r.nfields ++ " " ++ toString r.ctorParams
                  ++ " " ++ fire ++ " " ++ toString rhs
                  ++ " " ++ boolStr r.k ++ " " ++ boolStr r.eta
                  ++ " " ++ boolStr r.paramsBlind) }
  return id

/-- `IndCaps` (`ConLeche/Kernel/Env.lean:359`). -/
def wCaps (c : IndCaps) : W Nat := do
  let ec ← wName c.etaCtor
  let sz ← wPw c.sortZ
  let st ← get
  let id := st.nC
  set { st with nC := id + 1,
                buf := st.buf.push ("C " ++ toString id ++ " " ++ boolStr c.eta
                  ++ " " ++ toString ec ++ " " ++ toString c.etaParams
                  ++ " " ++ toString c.etaFields ++ " " ++ boolStr c.unitlike
                  ++ " " ++ toString c.unitParams ++ " " ++ boolStr c.ruleK
                  ++ " " ++ toString sz) }
  return id

/-- `ProjTable` (`ConLeche/Kernel/Env.lean:397`). -/
def wTable (t : ProjTable) : W Nat := do
  let sn ← wName t.structName
  let lps ← t.levelParams.mapM wName
  let ct ← wName t.ctor
  let ss ← wLevel t.structSort
  let bs ← t.bodies.toList.mapM wExpr
  let gs ← t.guards.mapM wLevel
  let st ← get
  let id := st.nP
  set { st with nP := id + 1,
                buf := st.buf.push ("P " ++ toString id ++ " " ++ toString sn
                  ++ " " ++ idList lps ++ " " ++ toString t.numParams
                  ++ " " ++ toString ct ++ " " ++ toString t.numFields
                  ++ " " ++ toString ss ++ " " ++ idList bs
                  ++ " " ++ idList gs ++ " " ++ toString t.off) }
  return id

/-- `ConstantInfo` (`ConLeche/Kernel/Env.lean:471`). -/
def wInfo (ci : ConstantInfo) : W Nat := do
  let body ← match ci with
    | .axiomInfo v => do
      let i ← wCV v; pure ("a " ++ toString i)
    | .defnInfo v val h => do
      let i ← wCV v; let e ← wExpr val
      pure ("d " ++ toString i ++ " " ++ toString e ++ " " ++ hintStr h)
    | .thmInfo v val => do
      let i ← wCV v; let e ← wExpr val
      pure ("t " ++ toString i ++ " " ++ toString e)
    | .indInfo v caps => do
      let i ← wCV v; let c ← wCaps caps
      pure ("i " ++ toString i ++ " " ++ toString c)
    | .ctorInfo v np nf => do
      let i ← wCV v
      pure ("c " ++ toString i ++ " " ++ toString np ++ " " ++ toString nf)
    | .recInfo v mi rp rules => do
      let i ← wCV v
      let rs ← rules.mapM wRule
      pure ("r " ++ toString i ++ " " ++ toString mi ++ " " ++ toString rp
        ++ " " ++ idList rs)
    | .projInfo t => do
      let ti ← wTable t; pure ("p " ++ toString ti)
  let st ← get
  let id := st.nI
  set { st with nI := id + 1,
                buf := st.buf.push ("I " ++ toString id ++ " " ++ body) }
  return id

/-- `DeclC` (`ConLeche/Cached/ParsedC.lean:55`); no id — the order is the
payload. -/
def wDecl (d : DeclC) : W Unit := do
  let body ← match d with
    | .axiomDecl v => do
      let i ← wCV v; pure ("a " ++ toString i)
    | .defnDecl v val h => do
      let i ← wCV v; let e ← wExpr val
      pure ("d " ++ toString i ++ " " ++ toString e ++ " " ++ hintStr h)
    | .thmDecl v val => do
      let i ← wCV v; let e ← wExpr val
      pure ("t " ++ toString i ++ " " ++ toString e)
    | .opaqueDecl v val => do
      let i ← wCV v; let e ← wExpr val
      pure ("o " ++ toString i ++ " " ++ toString e)
    | .basisDecl k => pure ("b " ++ basisStr k)
    | .indDecl block np => do
      let is ← block.mapM wInfo
      pure ("i " ++ toString np ++ " " ++ idList is)
  emit ("D " ++ body)
  modify fun st => { st with nD := st.nD + 1 }

/-! ## The entry points -/

/-- The whole dump as the writer's final state (the line buffer plus the
per-kind counts, which the harness reports). -/
def dumpState (ds : List DeclC) : WState :=
  (do
    emit header
    ds.forM wDecl
    emit ("end " ++ toString (← get).nD) : W Unit).run {} |>.2

/-- Join a line buffer, one `\n` after every line.  The accumulator is
uniquely referenced, so Lean's string append grows it in place. -/
def joinLines (a : Array String) : String :=
  a.foldl (fun acc l => acc ++ l ++ "\n") ""

/-- **The writer.**  `parseDecls (dumpDecls ds)` is `.ok ds`
(`ConRon/Dump/Read.lean`; checked on every fixture by `lake exe
con-ron-dump`). -/
def dumpDecls (ds : List DeclC) : String :=
  joinLines (dumpState ds).buf

/-! ## The pin dump (`con-ron-pins/1`)

`natOpPinSets` is not a declaration list, so it gets a sibling file rather
than a record of `con-ron-decls/1`: the pins are per *toolchain*, dumped once,
and copying their 26 512 `E` records into each of the 348 fixture dumps would
be absurd.  Everything below the payload is the same format, so the writer is
the same monad and the same interning tables — an `E` id in a pin dump means
exactly what it means in a declaration dump. -/

/-- `NatOpPinSet` (`ConLeche/Kernel/NatOpPinSet.lean:30-49`).  No id, for `D`'s
reason: the record *is* the payload and its position in the file is the
position in `natOpPinSets`, which is the order the install gate tries the
variants in.  The eight pins come first, then the eight counted proof lists,
in the field order of the structure. -/
def wPinSet (s : NatOpPinSet) : W Unit := do
  let dv ← wExpr s.divPin
  let md ← wExpr s.modPin
  let gc ← wExpr s.gcdPin
  let la ← wExpr s.landPin
  let lo ← wExpr s.lorPin
  let xo ← wExpr s.xorPin
  let sl ← wExpr s.shiftLeftPin
  let sr ← wExpr s.shiftRightPin
  let dvp ← s.divProofs.mapM wExpr
  let mdp ← s.modProofs.mapM wExpr
  let gcp ← s.gcdProofs.mapM wExpr
  let lap ← s.landProofs.mapM wExpr
  let lop ← s.lorProofs.mapM wExpr
  let xop ← s.xorProofs.mapM wExpr
  let slp ← s.shiftLeftProofs.mapM wExpr
  let srp ← s.shiftRightProofs.mapM wExpr
  emit ("S " ++ strField s.toolchain
    ++ " " ++ toString dv ++ " " ++ toString md ++ " " ++ toString gc
    ++ " " ++ toString la ++ " " ++ toString lo ++ " " ++ toString xo
    ++ " " ++ toString sl ++ " " ++ toString sr
    ++ " " ++ idList dvp ++ " " ++ idList mdp ++ " " ++ idList gcp
    ++ " " ++ idList lap ++ " " ++ idList lop ++ " " ++ idList xop
    ++ " " ++ idList slp ++ " " ++ idList srp)
  modify fun st => { st with nS := st.nS + 1 }

/-- The whole pin dump as the writer's final state (the line buffer plus the
per-kind counts the harness reports). -/
def dumpPinsState (ss : List NatOpPinSet) : WState :=
  (do
    emit pinsHeader
    ss.forM wPinSet
    emit ("end " ++ toString (← get).nS) : W Unit).run {} |>.2

/-- **The pin writer.**  `parsePins (dumpPins ss)` is `.ok ss`
(`ConRon/Dump/Read.lean`; checked on `ConLeche.natOpPinSets` by `lake exe
con-ron-dump-pins`). -/
def dumpPins (ss : List NatOpPinSet) : String :=
  joinLines (dumpPinsState ss).buf

end ConRon.Dump
