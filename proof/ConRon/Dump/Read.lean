/-
The `con-ron-decls/1` reader (DESIGN.md §3.6, task #10).

`parseDecls : String → Except String (List DeclC)` is the Lean counterpart of
the Rust reader that is still to be written: it validates the format
(`ConRon/Dump/FORMAT.md`) in Lean, before any Rust exists, and it is what
makes the round trip `parseDecls (dumpDecls ds) = .ok ds` a runnable test.

It is deliberately a *single forward pass* with no fixups: every id space is an
`Array` that grows by one per record, and every reference is an index into an
array that is already long enough.  The Rust reader is meant to be this
function with `Vec` for `Array`.

`parsePins` (task #31) reads the sibling format `con-ron-pins/1` (FORMAT.md
§7, the `Nat`-operation pin variants) and is *the same function*: the record
grammar below the payload is identical, so `RState.pins` is the flag that
swaps the payload record (`S` for `D`) and what the footer counts.
-/
import ConRon.Dump.Write

namespace ConRon.Dump

open ConLeche
open ConLeche.Cached

/-! ## The reader's state -/

/-- One `Array` per id space, plus the current record's tokens. -/
structure RState where
  names : Array Name := #[]
  levels : Array Level := #[]
  pws : Array PropWhen := #[]
  exprs : Array Expr := #[]
  cvs : Array ConstantVal := #[]
  rules : Array RecRule := #[]
  caps : Array IndCaps := #[]
  tables : Array ProjTable := #[]
  infos : Array ConstantInfo := #[]
  decls : Array DeclC := #[]
  /-- The `con-ron-pins/1` payload (`FORMAT.md` §7).  A file has one payload
  kind or the other, never both. -/
  pinSets : Array NatOpPinSet := #[]
  /-- Which file is being read: `false` a `con-ron-decls/1` dump (payload
  `D`), `true` a `con-ron-pins/1` one (payload `S`).  The flag is what makes
  the shared record grammar reject the wrong payload record and the footer
  count the right thing. -/
  pins : Bool := false
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

def boolTok : R Bool := do
  let s ← nextTok
  if s == "0" then return false
  else if s == "1" then return true
  else rerr ("expected 0 or 1, got '" ++ s ++ "'")

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
whichever fixture happens to contain them. -/

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

def cvRef : R ConstantVal := do
  let i ← natTok
  let st ← get
  if h : i < st.cvs.size then return st.cvs[i]'h
  else rerr ("constval id " ++ toString i ++ " is not defined yet")

def ruleRef : R RecRule := do
  let i ← natTok
  let st ← get
  if h : i < st.rules.size then return st.rules[i]'h
  else rerr ("recrule id " ++ toString i ++ " is not defined yet")

def capsRef : R IndCaps := do
  let i ← natTok
  let st ← get
  if h : i < st.caps.size then return st.caps[i]'h
  else rerr ("indcaps id " ++ toString i ++ " is not defined yet")

def tableRef : R ProjTable := do
  let i ← natTok
  let st ← get
  if h : i < st.tables.size then return st.tables[i]'h
  else rerr ("projtable id " ++ toString i ++ " is not defined yet")

def infoRef : R ConstantInfo := do
  let i ← natTok
  let st ← get
  if h : i < st.infos.size then return st.infos[i]'h
  else rerr ("constinfo id " ++ toString i ++ " is not defined yet")

/-- Check that a record's own id is the next one of its kind. -/
def expectId (want : Nat) (what : String) : R Unit := do
  let got ← natTok
  if got == want then return ()
  else rerr (what ++ " id " ++ toString got ++ ", expected " ++ toString want)

/-! ## Inline enumerations -/

def hintTok : R ReducibilityHint := do
  let t ← nextTok
  if t == "o" then return .opaque
  else if t == "b" then return .abbrev
  else if t == "r" then return .regular (← natTok)
  else rerr ("unknown reducibility hint '" ++ t ++ "'")

def basisTok : R BasisKind := do
  let t ← nextTok
  if t == "eq" then return .eqK
  else if t == "nat" then return .natK
  else if t == "punit" then return .punitK
  else if t == "empty" then return .emptyK
  else if t == "false" then return .falseK
  else if t == "quot" then return .quotK
  else rerr ("unknown basis kind '" ++ t ++ "'")

def fireTok : R RecRuleFire := do
  let t ← nextTok
  if t == "i" then return .inert
  else if t == "p" then return .plain
  else if t == "n" then
    let lvls ← listTok levelRef
    let pins ← listTok exprRef
    return .nested lvls pins
  else rerr ("unknown recursor-rule fire '" ++ t ++ "'")

/-! ## Records -/

/-- Read one record, assuming its kind letter has already been consumed. -/
def parseRecord (kind : String) : R Unit := do
  -- A file has ONE payload kind (`FORMAT.md` §7): the header decided which,
  -- so the other one's record is an error rather than an ignored line.
  if kind == "D" && (← get).pins then
    rerr "a declaration record 'D' in a con-ron-pins/1 dump"
  else if kind == "S" && !(← get).pins then
    rerr "a pin-set record 'S' in a con-ron-decls/1 dump"
  else if kind == "N" then
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
    let v ← if t == "b" then do pure (ExprC.mkBVar (← natTok))
      else if t == "v" then do
        let idx ← natTok; let ty ← exprRef; pure (ExprC.mkFVar idx ty)
      else if t == "s" then do pure (ExprC.mkSort (← levelRef))
      else if t == "c" then do
        let n ← nameRef; let us ← listTok levelRef; pure (ExprC.mkConst n us)
      else if t == "a" then do
        let f ← exprRef; let a ← exprRef; pure (ExprC.mkApp f a)
      else if t == "l" then do
        let ty ← exprRef; let b ← exprRef; let p ← pwRef
        pure (ExprC.mkLam ty b ⟨p⟩)
      else if t == "f" then do
        let ty ← exprRef; let b ← exprRef; let p ← pwRef
        pure (ExprC.mkForallE ty b ⟨p⟩)
      else if t == "t" then do
        let ty ← exprRef; let val ← exprRef; let b ← exprRef
        pure (ExprC.mkLetE ty val b)
      else if t == "n" then do pure (ExprC.mkLit (.natVal (← natTok)))
      else if t == "g" then do pure (ExprC.mkLit (.strVal (← strTok)))
      else if t == "p" then do
        let sn ← nameRef; let i ← natTok; let s ← exprRef
        pure (ExprC.mkProj sn i s)
      else rerr ("unknown expr record '" ++ t ++ "'")
    modify fun st => { st with exprs := st.exprs.push v }
  else if kind == "V" then
    expectId (← get).cvs.size "constval"
    let n ← nameRef
    let lps ← listTok nameRef
    let ty ← exprRef
    modify fun st => { st with cvs := st.cvs.push ⟨n, lps, ty⟩ }
  else if kind == "R" then
    expectId (← get).rules.size "recrule"
    let ctor ← nameRef
    let nfields ← natTok
    let ctorParams ← natTok
    let fire ← fireTok
    let rhs ← exprRef
    let k ← boolTok
    let eta ← boolTok
    let pb ← boolTok
    let v : RecRule :=
      { ctor, nfields, ctorParams, fire, rhs, k, eta, paramsBlind := pb }
    modify fun st => { st with rules := st.rules.push v }
  else if kind == "C" then
    expectId (← get).caps.size "indcaps"
    let eta ← boolTok
    let etaCtor ← nameRef
    let etaParams ← natTok
    let etaFields ← natTok
    let unitlike ← boolTok
    let unitParams ← natTok
    let ruleK ← boolTok
    let sortZ ← pwRef
    let v : IndCaps :=
      { eta, etaCtor, etaParams, etaFields, unitlike, unitParams, ruleK, sortZ }
    modify fun st => { st with caps := st.caps.push v }
  else if kind == "P" then
    expectId (← get).tables.size "projtable"
    let structName ← nameRef
    let levelParams ← listTok nameRef
    let numParams ← natTok
    let ctor ← nameRef
    let numFields ← natTok
    let structSort ← levelRef
    let bodies ← listTok exprRef
    let guards ← listTok levelRef
    let off ← natTok
    let v : ProjTable :=
      { structName, levelParams, numParams, ctor, numFields, structSort,
        bodies := bodies.toArray, guards, off }
    modify fun st => { st with tables := st.tables.push v }
  else if kind == "I" then
    expectId (← get).infos.size "constinfo"
    let t ← nextTok
    let v ← if t == "a" then do pure (ConstantInfo.axiomInfo (← cvRef))
      else if t == "d" then do
        let cv ← cvRef; let e ← exprRef; let h ← hintTok
        pure (ConstantInfo.defnInfo cv e h)
      else if t == "t" then do
        let cv ← cvRef; let e ← exprRef; pure (ConstantInfo.thmInfo cv e)
      else if t == "i" then do
        let cv ← cvRef; let c ← capsRef; pure (ConstantInfo.indInfo cv c)
      else if t == "c" then do
        let cv ← cvRef; let np ← natTok; let nf ← natTok
        pure (ConstantInfo.ctorInfo cv np nf)
      else if t == "r" then do
        let cv ← cvRef; let mi ← natTok; let rp ← natTok
        let rules ← listTok ruleRef
        pure (ConstantInfo.recInfo cv mi rp rules)
      else if t == "p" then do pure (ConstantInfo.projInfo (← tableRef))
      else rerr ("unknown constinfo record '" ++ t ++ "'")
    modify fun st => { st with infos := st.infos.push v }
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
  else if kind == "D" then
    let t ← nextTok
    let v ← if t == "a" then do pure (DeclC.axiomDecl (← cvRef))
      else if t == "d" then do
        let cv ← cvRef; let e ← exprRef; let h ← hintTok
        pure (DeclC.defnDecl cv e h)
      else if t == "t" then do
        let cv ← cvRef; let e ← exprRef; pure (DeclC.thmDecl cv e)
      else if t == "o" then do
        let cv ← cvRef; let e ← exprRef; pure (DeclC.opaqueDecl cv e)
      else if t == "b" then do pure (DeclC.basisDecl (← basisTok))
      else if t == "i" then do
        let np ← natTok; let block ← listTok infoRef
        pure (DeclC.indDecl block np)
      else rerr ("unknown declaration record '" ++ t ++ "'")
    modify fun st => { st with decls := st.decls.push v }
  else
    rerr ("unknown record kind '" ++ kind ++ "'")

/-! ## The driver -/

/-- Read the records, stopping at the `end` footer. -/
partial def runLines : List String → R Unit
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
        let want := if st.pins then st.pinSets.size else st.decls.size
        let what := if st.pins then " pin sets read" else " declarations read"
        if n != want then
          rerr ("footer count " ++ toString n ++ " ≠ the "
            ++ toString want ++ what)
        else if st.pos != st.toks.size then rerr "trailing fields in the footer"
        else if ls.any (fun x => !x.isEmpty) then rerr "content after the footer"
        else return ()
      else do
        parseRecord kind
        let st ← get
        if st.pos != st.toks.size then rerr "trailing fields in a record"
        else runLines ls

/-- **The reader.**  The inverse of `dumpDecls` (`ConRon/Dump/Write.lean`). -/
def parseDecls (s : String) : Except String (List DeclC) :=
  match s.splitOn "\n" with
  | [] => Except.error "empty input"
  | hdr :: rest =>
    if hdr != header then
      Except.error ("bad header: expected '" ++ header ++ "', got '" ++ hdr ++ "'")
    else
      match (runLines rest).run { lineNo := 1 } with
      | .error e => Except.error e
      | .ok (_, st) => Except.ok st.decls.toList

/-- **The pin reader** (`FORMAT.md` §7).  The inverse of `dumpPins`: the same
forward pass over the same record grammar, with `S` for the payload and the
footer counting pin sets. -/
def parsePins (s : String) : Except String (List NatOpPinSet) :=
  match s.splitOn "\n" with
  | [] => Except.error "empty input"
  | hdr :: rest =>
    if hdr != pinsHeader then
      Except.error ("bad header: expected '" ++ pinsHeader ++ "', got '" ++ hdr ++ "'")
    else
      match (runLines rest).run { lineNo := 1, pins := true } with
      | .error e => Except.error e
      | .ok (_, st) => Except.ok st.pinSets.toList

end ConRon.Dump
