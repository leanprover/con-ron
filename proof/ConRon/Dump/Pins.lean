/-
The `con-ron-pins/1` format, and `con-ron-dump-pins` (DESIGN.md §3.6's
runtime-data decision, task #31; one file since task #80).

    lake exe con-ron-dump-pins [--no-roundtrip] <out.pins>

`dumpPins : List NatOpPinSet → String` writes `ConLeche.natOpPinSets`
(`ConLeche/Kernel/NatOpPins.lean:61`, the plain `List NatOpPinSet` the
`#load_natop_pins` command splices out of the committed `pins/*.json` dumps)
in the text format `ConRon/Dump/FORMAT.md` specifies: one record per line, one
dense id space per record kind, shared nodes written once.  `parsePins` reads
it back, and `main` checks that

* `parsePins (dumpPins ss) = .ok ss'` with `ss'` equal to `ss` field by field
  (the `Expr` comparisons go through `BEq Expr`, i.e. con-leche's memoised
  pointer-guarded `Expr.beqMemo`, not the derived `O(tree)` walk), and
* re-dumping `ss'` is byte-identical to the file.

Exit 0 iff everything agrees, 1 on a mismatch, 3 on usage or IO failure.

**Who reads these bytes.**  `scripts/gen-pins.sh` wraps them in the verified
core's embedded `kernel::pins_text::PINS_TEXT`, whose freshness against
`natOpPinSets` is a gate; `con-ron --pins FILE` reads a file in this format
through the unverified Rust reader (`crates/con-ron-dump`) as a test override.
And `parsePins` is a *proof* obligation's right-hand side: `pins_decode_refines`
(`ConRon/Refine/Pins.lean`) says the core's verified decoder computes what this
function computes, which is why `runLines` below is total rather than `partial`.

**What used to be here.**  Until task #80 this directory also held
`con-ron-decls/1`, the `List DeclC` dump of task #10 (`Main.lean`, `Write.lean`,
`Read.lean`), whose purpose was to feed con-leche's own parsed declarations to
the Rust checker alone.  `scripts/diff-e2e.sh` runs the whole binary on every
fixture's raw export against con-leche's pinned expectations and subsumes that,
so the declaration dump was retired and the pin dump — which nothing subsumes —
kept.  The record grammar below the payload is what the two formats shared.

Nothing here is a theorem: this is a test and porting tool.
-/
import ConLeche.Expr
import ConLeche.Kernel.NatOpPinSet
import ConLeche.Kernel.NatOpPins

namespace ConRon.Dump

open ConLeche
open ConLeche.Cached

/-- The version header, the whole first line of a pin dump. -/
def pinsHeader : String := "con-ron-pins/1"

/-! ## Scalars -/

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

/-! ## The writer's state -/

/-- The emission state: the output lines, one interning table per interned id
space, and the payload counter.  `Name`, `Level`, `PropWhen` and `Expr` are
interned — that is what keeps the DAG a DAG, and it is not optional here: as a
tree one pin variant is 5.1 M nodes. -/
structure WState where
  buf : Array String := #[]
  names : Std.HashMap Name Nat := {}
  levels : Std.HashMap Level Nat := {}
  pws : Std.HashMap PropWhen Nat := {}
  exprs : Std.HashMap Expr Nat := {}
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
recursive writer overflows the stack on the bigger pin blobs. -/

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

/-! ## The payload -/

/-- `NatOpPinSet` (`ConLeche/Kernel/NatOpPinSet.lean:30-49`).  No id: the
record *is* the payload and its position in the file is the position in
`natOpPinSets`, which is the order the install gate tries the variants in.
The eight pins come first, then the eight counted proof lists, in the field
order of the structure. -/
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

/-! ## The writer's entry points -/

/-- The whole dump as the writer's final state (the line buffer plus the
per-kind counts the harness reports). -/
def dumpPinsState (ss : List NatOpPinSet) : WState :=
  (do
    emit pinsHeader
    ss.forM wPinSet
    emit ("end " ++ toString (← get).nS) : W Unit).run {} |>.2

/-- Join a line buffer, one `\n` after every line.  The accumulator is
uniquely referenced, so Lean's string append grows it in place. -/
def joinLines (a : Array String) : String :=
  a.foldl (fun acc l => acc ++ l ++ "\n") ""

/-- **The writer.**  `parsePins (dumpPins ss)` is `.ok ss`, checked on
`ConLeche.natOpPinSets` by `lake exe con-ron-dump-pins`. -/
def dumpPins (ss : List NatOpPinSet) : String :=
  joinLines (dumpPinsState ss).buf

/-! ## The reader's state

`parsePins` is deliberately a *single forward pass* with no fixups: every id
space is an `Array` that grows by one per record, and every reference is an
index into an array that is already long enough.  The Rust reader
(`crates/con-ron-dump`) is this function with `Vec` for `Array`, and the
core's verified decoder (`kernel::pins_decode`) is this function on bytes. -/

/-- One `Array` per id space, the payload, and the current record's tokens. -/
structure RState where
  names : Array Name := #[]
  levels : Array Level := #[]
  pws : Array PropWhen := #[]
  exprs : Array Expr := #[]
  pinSets : Array NatOpPinSet := #[]
  toks : Array String := #[]
  pos : Nat := 0
  lineNo : Nat := 0

/-- The reader's monad. -/
abbrev R := StateT RState (Except String)

/-- Fail, naming the line. -/
def rerr (msg : String) : R α :=
  fun st => Except.error ("line " ++ toString st.lineNo ++ ": " ++ msg)

/-! ## Tokens -/

def peekTok : R String := do
  let st ← get
  if h : st.pos < st.toks.size then return st.toks[st.pos]'h
  else rerr "unexpected end of record"

def nextTok : R String := do
  let st ← get
  if h : st.pos < st.toks.size then
    set { st with pos := st.pos + 1 }
    return st.toks[st.pos]'h
  else rerr "unexpected end of record"

def natTok : R Nat := do
  let s ← nextTok
  match s.toNat? with
  | some n => return n
  | none => rerr ("expected a decimal number, got '" ++ s ++ "'")

/-- A counted list of whatever `p` reads. -/
def listTok (p : R α) : R (List α) := do
  let n ← natTok
  let rec go (k : Nat) (acc : Array α) : R (Array α) := do
    match k with
    | 0 => return acc
    | k' + 1 => go k' (acc.push (← p))
  return (← go n #[]).toList

/-! ## Strings -/

/-- Hex digit value, or `none`. -/
def hexDigit? (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else none

/-- Undo `escapeString`.  Structural in the character list: `v` accumulates
the hexadecimal value of an escape and `inEsc` says whether one is open. -/
def unescapeGo : List Char → Nat → Bool → String → Except String String
  | [], _, inEsc, acc =>
    if inEsc then Except.error "unterminated string escape" else Except.ok acc
  | c :: rest, v, inEsc, acc =>
    if inEsc then
      if c == ';' then
        if Nat.isValidChar v then
          unescapeGo rest 0 false (acc.push (Char.ofNat v))
        else Except.error ("escape \\" ++ toHex v ++ "; is not a code point")
      else
        match hexDigit? c with
        | some d => unescapeGo rest (v * 16 + d) true acc
        | none => Except.error "bad character in a string escape"
    else if c == '\\' then unescapeGo rest 0 true acc
    else unescapeGo rest 0 false (acc.push c)

/-- A string field: the code-point count, then the escaped text. -/
def strTok : R String := do
  let n ← natTok
  let t ← nextTok
  match unescapeGo t.toList 0 false "" with
  | .error e => rerr e
  | .ok s =>
    if s.length == n then return s
    else rerr ("string length " ++ toString s.length ++ " ≠ the declared "
      ++ toString n)

/-! ### Self-tests of the string codec

The escape is the one part of the format a Rust reader has to reimplement
character by character, so its edge cases are pinned here rather than left to
whichever pin variant happens to contain them. -/

private def codecRT (s : String) : Bool :=
  match unescapeGo (escapeString s).toList 0 false "" with
  | .ok s' => s' == s
  | .error _ => false

#guard escapeString "" == ""
#guard escapeString " " == "\\20;"
#guard escapeString "\\" == "\\5c;"
#guard escapeString "A.b_1" == "A.b_1"
#guard codecRT ""
#guard codecRT " "
#guard codecRT "\\"
#guard codecRT "a b\nc\t;"
#guard codecRT "∀ x, x ≤ x₁ · y"
#guard codecRT (String.singleton (Char.ofNat 0))
#guard codecRT (String.singleton (Char.ofNat 0x10ffff))
-- the surrogate range is not a code point: an escape naming one is rejected
#guard (unescapeGo "\\d800;".toList 0 false "").isOk == false
#guard (unescapeGo "\\20".toList 0 false "").isOk == false

/-! ## References -/

def nameRef : R Name := do
  let i ← natTok
  let st ← get
  if h : i < st.names.size then return st.names[i]'h
  else rerr ("name id " ++ toString i ++ " is not defined yet")

def levelRef : R Level := do
  let i ← natTok
  let st ← get
  if h : i < st.levels.size then return st.levels[i]'h
  else rerr ("level id " ++ toString i ++ " is not defined yet")

def pwRef : R PropWhen := do
  let i ← natTok
  let st ← get
  if h : i < st.pws.size then return st.pws[i]'h
  else rerr ("propwhen id " ++ toString i ++ " is not defined yet")

def exprRef : R Expr := do
  let i ← natTok
  let st ← get
  if h : i < st.exprs.size then return st.exprs[i]'h
  else rerr ("expr id " ++ toString i ++ " is not defined yet")

/-- Check that a record's own id is the next one of its kind. -/
def expectId (want : Nat) (what : String) : R Unit := do
  let got ← natTok
  if got == want then return ()
  else rerr (what ++ " id " ++ toString got ++ ", expected " ++ toString want)

/-! ## Records -/

/-- Read one record, assuming its kind letter has already been consumed. -/
def parseRecord (kind : String) : R Unit := do
  if kind == "N" then
    expectId (← get).names.size "name"
    let t ← nextTok
    let v ← if t == "a" then pure Name.anonymous
      else if t == "s" then do let p ← nameRef; let s ← strTok; pure (Name.str p s)
      else if t == "n" then do let p ← nameRef; let k ← natTok; pure (Name.num p k)
      else rerr ("unknown name record '" ++ t ++ "'")
    modify fun st => { st with names := st.names.push v }
  else if kind == "L" then
    expectId (← get).levels.size "level"
    let t ← nextTok
    let v ← if t == "z" then pure Level.zero
      else if t == "s" then do pure (Level.succ (← levelRef))
      else if t == "m" then do let a ← levelRef; let b ← levelRef; pure (Level.max a b)
      else if t == "i" then do let a ← levelRef; let b ← levelRef; pure (Level.imax a b)
      else if t == "p" then do pure (Level.param (← nameRef))
      else rerr ("unknown level record '" ++ t ++ "'")
    modify fun st => { st with levels := st.levels.push v }
  else if kind == "W" then
    expectId (← get).pws.size "propwhen"
    let t ← nextTok
    let v ← if t == "n" then pure PropWhen.never
      else if t == "z" then do pure (PropWhen.ifAllZero (← listTok nameRef))
      else rerr ("unknown propwhen record '" ++ t ++ "'")
    modify fun st => { st with pws := st.pws.push v }
  else if kind == "E" then
    expectId (← get).exprs.size "expr"
    let t ← nextTok
    let v ← if t == "b" then do pure (Expr.mkBvar (← natTok))
      else if t == "v" then do
        let idx ← natTok; let ty ← exprRef; pure (Expr.mkFVar idx ty)
      else if t == "s" then do pure (Expr.mkSort (← levelRef))
      else if t == "c" then do
        let n ← nameRef; let us ← listTok levelRef; pure (Expr.mkConst n us)
      else if t == "a" then do
        let f ← exprRef; let a ← exprRef; pure (Expr.mkApp f a)
      else if t == "l" then do
        let ty ← exprRef; let b ← exprRef; let p ← pwRef
        pure (Expr.mkLam ty b ⟨p⟩)
      else if t == "f" then do
        let ty ← exprRef; let b ← exprRef; let p ← pwRef
        pure (Expr.mkForallE ty b ⟨p⟩)
      else if t == "t" then do
        let ty ← exprRef; let val ← exprRef; let b ← exprRef
        pure (Expr.mkLetE ty val b)
      else if t == "n" then do pure (Expr.mkLit (.natVal (← natTok)))
      else if t == "g" then do pure (Expr.mkLit (.strVal (← strTok)))
      else if t == "p" then do
        let sn ← nameRef; let i ← natTok; let s ← exprRef
        pure (Expr.mkProj sn i s)
      else rerr ("unknown expr record '" ++ t ++ "'")
    modify fun st => { st with exprs := st.exprs.push v }
  else if kind == "S" then
    let toolchain ← strTok
    let divPin ← exprRef
    let modPin ← exprRef
    let gcdPin ← exprRef
    let landPin ← exprRef
    let lorPin ← exprRef
    let xorPin ← exprRef
    let shiftLeftPin ← exprRef
    let shiftRightPin ← exprRef
    let divProofs ← listTok exprRef
    let modProofs ← listTok exprRef
    let gcdProofs ← listTok exprRef
    let landProofs ← listTok exprRef
    let lorProofs ← listTok exprRef
    let xorProofs ← listTok exprRef
    let shiftLeftProofs ← listTok exprRef
    let shiftRightProofs ← listTok exprRef
    let v : NatOpPinSet :=
      { toolchain, divPin, modPin, gcdPin, landPin, lorPin, xorPin,
        shiftLeftPin, shiftRightPin, divProofs, modProofs, gcdProofs,
        landProofs, lorProofs, xorProofs, shiftLeftProofs, shiftRightProofs }
    modify fun st => { st with pinSets := st.pinSets.push v }
  else
    rerr ("unknown record kind '" ++ kind ++ "'")

/-! ## The driver -/

/-- Read the records, stopping at the `end` footer.

**Total, not `partial`** (task #43).  The recursion is structural in the line
list, but the recursive call sits under a `bind`, which the structural checker
does not see through; `termination_by` closes it.  It matters for the *proof*
side and not for the runtime: a `partial def` is opaque, with no equations and
no unfolding, so nothing whatever can be proved about it — and
`ConRon/Refine/Pins.lean` needs to state that the Rust decoder computes what
this function computes. -/
def runLines : List String → R Unit
  | [] => rerr "the dump has no 'end' footer"
  | l :: ls => do
    modify fun st =>
      { st with lineNo := st.lineNo + 1, toks := (l.splitOn " ").toArray, pos := 0 }
    if l.isEmpty then runLines ls
    else
      let kind ← nextTok
      if kind == "end" then
        let n ← natTok
        let st ← get
        if n != st.pinSets.size then
          rerr ("footer count " ++ toString n ++ " ≠ the "
            ++ toString st.pinSets.size ++ " pin sets read")
        else if st.pos != st.toks.size then rerr "trailing fields in the footer"
        else if ls.any (fun x => !x.isEmpty) then rerr "content after the footer"
        else return ()
      else do
        parseRecord kind
        let st ← get
        if st.pos != st.toks.size then rerr "trailing fields in a record"
        else runLines ls
termination_by ls => ls.length

/-- **The reader.**  The inverse of `dumpPins`: one forward pass over the
record grammar, `S` for the payload, the footer counting pin sets. -/
def parsePins (s : String) : Except String (List NatOpPinSet) :=
  match s.splitOn "\n" with
  | [] => Except.error "empty input"
  | hdr :: rest =>
    if hdr != pinsHeader then
      Except.error ("bad header: expected '" ++ pinsHeader ++ "', got '" ++ hdr ++ "'")
    else
      match (runLines rest).run { lineNo := 1 } with
      | .error e => Except.error e
      | .ok (_, st) => Except.ok st.pinSets.toList

/-! ## Structural equality of `NatOpPinSet`

`NatOpPinSet` derives nothing, and the derived `DecidableEq` of `Expr` is the
plain structural walk, which is `O(tree)` on a shared DAG — and a pin variant
is a 20 000-node DAG whose tree expansion is 5.1 M nodes (DESIGN.md task #22).
These comparisons use `==`, i.e. `Expr.beq`, which the compiler substitutes by
the memoised pointer-and-hash-guarded `Expr.beqMemo`. -/

/-- Two pin variants, field by field. -/
def pinSetEq (a b : NatOpPinSet) : Bool :=
  a.toolchain == b.toolchain
    && a.divPin == b.divPin && a.modPin == b.modPin
    && a.gcdPin == b.gcdPin && a.landPin == b.landPin
    && a.lorPin == b.lorPin && a.xorPin == b.xorPin
    && a.shiftLeftPin == b.shiftLeftPin && a.shiftRightPin == b.shiftRightPin
    && a.divProofs == b.divProofs && a.modProofs == b.modProofs
    && a.gcdProofs == b.gcdProofs && a.landProofs == b.landProofs
    && a.lorProofs == b.lorProofs && a.xorProofs == b.xorProofs
    && a.shiftLeftProofs == b.shiftLeftProofs
    && a.shiftRightProofs == b.shiftRightProofs

/-- The index of the first differing variant, if any. -/
def firstPinDiff (xs ys : List NatOpPinSet) : Option Nat :=
  let rec go (i : Nat) : List NatOpPinSet → List NatOpPinSet → Option Nat
    | [], [] => none
    | x :: xs, y :: ys => if pinSetEq x y then go (i + 1) xs ys else some i
    | _, _ => some i
  go 0 xs ys

/-- The proof-blob counts of one variant, in the field order of the record:
the census `--no-roundtrip` prints. -/
def proofCounts (s : NatOpPinSet) : List Nat :=
  [s.divProofs.length, s.modProofs.length, s.gcdProofs.length,
   s.landProofs.length, s.lorProofs.length, s.xorProofs.length,
   s.shiftLeftProofs.length, s.shiftRightProofs.length]

end ConRon.Dump

def usage : String :=
  "usage: con-ron-dump-pins [--no-roundtrip] <out.pins>\n\
   \n\
   Writes `ConLeche.natOpPinSets` in the con-ron-pins/1 format\n\
   (proof/ConRon/Dump/FORMAT.md), reads it back and compares.\n\
   \n\
   --no-roundtrip   write the file and stop"

def run (outp : String) (doRoundTrip : Bool) : IO UInt32 := do
  let ss := ConLeche.natOpPinSets
  let t0 ← IO.monoMsNow
  let st := ConRon.Dump.dumpPinsState ss
  let text := ConRon.Dump.joinLines st.buf
  IO.FS.writeFile outp text
  let tWrite ← IO.monoMsNow
  let bytes := text.utf8ByteSize
  IO.println s!"con-ron-dump-pins: {outp}"
  IO.println s!"  pin sets {st.nS}  names {st.names.size}  levels \
    {st.levels.size}  propwhens {st.pws.size}  exprs {st.exprs.size}"
  IO.println s!"  lines {st.buf.size}  bytes {bytes}  write {tWrite - t0}ms"
  for s in ss do
    IO.println s!"  variant {s.toolchain}  proof blobs {ConRon.Dump.proofCounts s}"
  if !doRoundTrip then
    IO.println "  round trip skipped (--no-roundtrip)"
    return 0
  match ConRon.Dump.parsePins text with
  | .error e => do
    IO.eprintln s!"con-ron-dump-pins: FAIL the dump does not read back: {e}"
    return 1
  | .ok ss' => do
    let tRead ← IO.monoMsNow
    let structOk :=
      ss.length == ss'.length && (ConRon.Dump.firstPinDiff ss ss').isNone
    let redump := ConRon.Dump.dumpPins ss'
    let byteOk := redump == text
    IO.println s!"  read {tRead - tWrite}ms"
    unless structOk do
      IO.eprintln s!"con-ron-dump-pins: FAIL structural mismatch at variant \
        {ConRon.Dump.firstPinDiff ss ss'} (lengths {ss.length} vs {ss'.length})"
    unless byteOk do
      IO.eprintln "con-ron-dump-pins: FAIL re-dumping the re-read variants is \
        not byte-identical"
    if structOk && byteOk then
      IO.println "  round trip exact"
      return 0
    else
      return 1

def main (args : List String) : IO UInt32 := do
  let doRoundTrip := !args.contains "--no-roundtrip"
  match args.filter (fun a => !a.startsWith "--") with
  | [outp] => run outp doRoundTrip
  | _ => do IO.eprintln usage; return 3
