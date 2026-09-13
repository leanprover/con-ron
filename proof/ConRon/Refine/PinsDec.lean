/-
`ConRon.Refine.PinsDec` — the **byte-level reference decoder** (task #64).

`ConRon/Refine/Pins.lean`'s `pins_decode_refines` relates two programs that do
not have the same shape: `kernel::pins_decode::decode` walks a `&[u8]` with an
index, while `ConRon.Dump.parsePins` splits a `String` into lines and each
line into space-separated tokens.  Task #43's docstring called the missing
piece "the tokenizer bridge" and put it first in the dependency order; this
file is the joint the bridge is built on.

`Dec` is `kernel::pins_decode`, function for function, in Lean:

* the byte string is a `List Nat` **suffix** rather than a slice and an index
  (`Dec.byteAt []` is the `256` sentinel the Rust `byte_at` returns past the
  end), so every reader is structural where the Rust one is an index
  recursion;
* failure is `none` rather than `CheckError::Internal`; the port has exactly
  one error value and no statement reads it;
* `readIndex` carries no machine-word bound where the port carries one
  (task #64's guard, `kernel/pins_decode.rs`): the mirror is the more
  permissive of the two there, which is the direction the refinement can
  afford;
* the tables are `List`s of **con-leche** values, not `Vec`s of the port's, so
  that the refinement of a record is the smart-constructor lemma of
  `Refine/{Name,Level,PropWhen,Expr}.lean` and nothing else.

With that, `pins_decode_refines` factors into two independent halves:

| half | statement | where |
|---|---|---|
| (A) the model against `Dec` | `decode t = ok (.Ok v) → Dec.decode (bytes t) = some (absPins v)` | `Refine/PinsBytes.lean`, `Refine/PinsRecords.lean`, `Refine/PinsRun.lean` |
| (B) `Dec` against the reader | `Dec.decode bs = some ps → parsePins (text bs) = .ok ps` | `Refine/PinsSplit.lean`, `Refine/PinsRead.lean` |

(A) is ordinary Aeneas refinement — one lemma per Rust function, no strings
anywhere.  (B) is pure Lean and is where `String.splitOn` is met.

**Why the bytes are ASCII, and why that is not a third pass.**  `absText` is a
UTF-8 *decode*, so relating a byte suffix to a character suffix needs every
byte to be ASCII.  `Dec` makes that a one-line induction rather than a second
walk over the port: every byte `Dec` ever looks at it either compares to a
fixed value or bounds into `33 … 126`, so `decode_ascii` below falls out of
`Dec`'s own equations, and `Refine/PinsSplit.lean` turns it into
`absText t = String.ofList …` once, at the top.

**Fuel, in one place.**  Every recursion here is structural — on the byte list
(`readNatFrom`, `unescapeFrom`), on the pattern (`startsWith`) or on the
counter (`nameListFrom` and its siblings) — except the record pass, whose step
consumes a record of unknown length.  `runRecords` therefore takes a `Nat`
fuel and `decode` passes the byte count, which is more than the record count.
That is also the shape the model's side wants: `kernel::pins_decode::
run_records` is a `partial_fixpoint`, so (A)'s proof is a fuel induction on
`t.length - i` either way.
-/
import ConRon.Dump.Pins

namespace ConRon.Refine.PinsDec

open ConLeche

/-! ## Bytes -/

/-- The byte string as the Rust decoder sees what is left of it. -/
abbrev Bytes := List Nat

/-- `byte_at`, with the `256` sentinel for "past the end". -/
def byteAt : Bytes → Nat
  | [] => 256
  | b :: _ => b

/-- `starts_with_from`: does `bs` open with the pattern `p`?  Structural in
`p`, where the Rust is an index recursion bounded by `p.len()`. -/
def startsWith : Bytes → Bytes → Bool
  | _, [] => true
  | [], _ :: _ => false
  | b :: bs, c :: p => b == c && startsWith bs p

/-- `pins_header`: `con-ron-pins/1` and its newline. -/
def headerBytes : Bytes :=
  [99, 111, 110, 45, 114, 111, 110, 45, 112, 105, 110, 115, 47, 49, 10]

/-- `after_space`. -/
def afterSpace : Bytes → Option Bytes
  | 32 :: r => some r
  | _ => none

/-- `after_newline`. -/
def afterNewline : Bytes → Option Bytes
  | 10 :: r => some r
  | _ => none

/-! ## Scalars -/

/-- Is `b` a decimal digit? -/
def isDigit (b : Nat) : Bool := 48 ≤ b && b ≤ 57

/-- `read_nat_from`: the accumulator loop, with the port's `u64` guard. -/
def readNatFrom : Bytes → Nat → Option (Nat × Bytes)
  | [], _ => none
  | b :: r, acc =>
    if isDigit b then
      if acc > 1000000000000000000 then none
      else readNatFrom r (acc * 10 + (b - 48))
    else if b = 32 || b = 10 then some (acc, b :: r)
    else none

/-- `read_nat`: at least one digit, ending at a space or a newline. -/
def readNat (bs : Bytes) : Option (Nat × Bytes) :=
  if isDigit (byteAt bs) then readNatFrom bs 0 else none

/-- `read_index` is `read_nat`, with the `as usize` cast dropped: after task
#64's guard the port rejects anything above `u32::MAX`, so on every accepted
value the cast is the identity and there is nothing to model.

This is the one place the mirror is deliberately *more permissive* than the
port: `readIndex` has no `4294967295` bound of its own.  That is the harmless
direction — the refinement runs model-accepts ⟹ mirror-accepts, so a mirror
that also accepts what the port rejects claims nothing extra — and it keeps
`PinsDec` free of a machine-word bound that has no counterpart in
`ConRon/Dump/Pins.lean`'s `natTok`. -/
def readIndex (bs : Bytes) : Option (Nat × Bytes) := readNat bs

/-- `read_big_nat_from`: the same loop without the machine-word guard. -/
def readBigNatFrom : Bytes → Nat → Option (Nat × Bytes)
  | [], _ => none
  | b :: r, acc =>
    if isDigit b then readBigNatFrom r (acc * 10 + (b - 48))
    else if b = 32 || b = 10 then some (acc, b :: r)
    else none

/-- `read_big_nat`. -/
def readBigNat (bs : Bytes) : Option (Nat × Bytes) :=
  if isDigit (byteAt bs) then readBigNatFrom bs 0 else none

/-- `expect_id`: a record's own id is the next one of its kind. -/
def expectId (bs : Bytes) (want : Nat) : Option Bytes :=
  match readIndex bs with
  | some (got, r) => if got = want then some r else none
  | none => none

/-! ## Strings (FORMAT.md §3's escape) -/

/-- `hex_digit`, with `16` for "not one". -/
def hexDigit (b : Nat) : Nat :=
  if 48 ≤ b && b ≤ 57 then b - 48
  else if 97 ≤ b && b ≤ 102 then b - 87
  else 16

/-- `is_valid_char`. -/
def isValidChar (v : Nat) : Bool :=
  if v < 55296 then true else v > 57343 && v < 1114112

/-- `unescape_from`: `v` accumulates an open escape's value, `inEsc` says
whether one is open, `out` is the code points read so far (in order). -/
def unescapeFrom : Bytes → Nat → Bool → List Nat → Option (List Nat × Bytes)
  | [], _, _, _ => none
  | b :: r, v, inEsc, out =>
    if b = 32 || b = 10 then
      (if inEsc then none else some (out, b :: r))
    else if inEsc then
      if b = 59 then
        (if isValidChar v then unescapeFrom r 0 false (out ++ [v]) else none)
      else
        let d := hexDigit b
        if d = 16 || v > 1114111 then none
        else unescapeFrom r (v * 16 + d) true out
    else if b = 92 then unescapeFrom r 0 true out
    else if b < 33 || b > 126 then none
    else unescapeFrom r 0 false (out ++ [b])

/-- `read_string`: the code-point count, a space, then the escaped text. -/
def readString (bs : Bytes) : Option (List Nat × Bytes) :=
  match readIndex bs with
  | none => none
  | some (n, r) =>
    match afterSpace r with
    | none => none
    | some r =>
      match unescapeFrom r 0 false [] with
      | none => none
      | some (s, r) => if s.length = n then some (s, r) else none

/-- The code points of a string field as a Lean `String` — `Refine/Abs.lean`'s
`absString` on the port's `Vec<u32>`, and `Read.lean`'s `unescapeGo` result on
the reader's side. -/
def decString (cps : List Nat) : String := String.ofList (cps.map Char.ofNat)

/-! ## The tables -/

/-- `pins_decode::Tables`, as con-leche values: one list per id space, in
emission order, plus the pin variants read so far.  A reference is an index
into a list that is already long enough. -/
structure Tables where
  names : List Name := []
  levels : List Level := []
  pws : List PropWhen := []
  exprs : List Expr := []
  sets : List NatOpPinSet := []
  deriving Inhabited

/-- `tables_new`. -/
def tablesNew : Tables := {}

/-! ## Backward references -/

/-- `name_ref`. -/
def nameRef (bs : Bytes) (tb : Tables) : Option (Name × Bytes) :=
  match readIndex bs with
  | none => none
  | some (k, r) => match tb.names[k]? with
    | some n => some (n, r)
    | none => none

/-- `level_ref`. -/
def levelRef (bs : Bytes) (tb : Tables) : Option (Level × Bytes) :=
  match readIndex bs with
  | none => none
  | some (k, r) => match tb.levels[k]? with
    | some u => some (u, r)
    | none => none

/-- `pw_ref`. -/
def pwRef (bs : Bytes) (tb : Tables) : Option (PropWhen × Bytes) :=
  match readIndex bs with
  | none => none
  | some (k, r) => match tb.pws[k]? with
    | some p => some (p, r)
    | none => none

/-- `expr_ref`. -/
def exprRef (bs : Bytes) (tb : Tables) : Option (Expr × Bytes) :=
  match readIndex bs with
  | none => none
  | some (k, r) => match tb.exprs[k]? with
    | some e => some (e, r)
    | none => none

/-- `name_list_from`. -/
def nameListFrom (bs : Bytes) (tb : Tables) : Nat → List Name →
    Option (List Name × Bytes)
  | 0, out => some (out, bs)
  | k + 1, out =>
    match afterSpace bs with
    | none => none
    | some r => match nameRef r tb with
      | none => none
      | some (n, r) => nameListFrom r tb k (out ++ [n])

/-- `name_list`. -/
def nameList (bs : Bytes) (tb : Tables) : Option (List Name × Bytes) :=
  match readIndex bs with
  | none => none
  | some (n, r) => nameListFrom r tb n []

/-- `level_list_from`. -/
def levelListFrom (bs : Bytes) (tb : Tables) : Nat → List Level →
    Option (List Level × Bytes)
  | 0, out => some (out, bs)
  | k + 1, out =>
    match afterSpace bs with
    | none => none
    | some r => match levelRef r tb with
      | none => none
      | some (u, r) => levelListFrom r tb k (out ++ [u])

/-- `level_list`. -/
def levelList (bs : Bytes) (tb : Tables) : Option (List Level × Bytes) :=
  match readIndex bs with
  | none => none
  | some (n, r) => levelListFrom r tb n []

/-- `expr_list_from`. -/
def exprListFrom (bs : Bytes) (tb : Tables) : Nat → List Expr →
    Option (List Expr × Bytes)
  | 0, out => some (out, bs)
  | k + 1, out =>
    match afterSpace bs with
    | none => none
    | some r => match exprRef r tb with
      | none => none
      | some (e, r) => exprListFrom r tb k (out ++ [e])

/-- `expr_list`. -/
def exprList (bs : Bytes) (tb : Tables) : Option (List Expr × Bytes) :=
  match readIndex bs with
  | none => none
  | some (n, r) => exprListFrom r tb n []

/-! ## The records (FORMAT.md §4, the kinds a pin dump uses) -/

/-- `record_name_str`. -/
def recordNameStr (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match nameRef r tb with
    | none => none
    | some (pre, r) => match afterSpace r with
      | none => none
      | some r => match readString r with
        | none => none
        | some (s, r) => match afterNewline r with
          | none => none
          | some r =>
            some ({ tb with names := tb.names ++ [.str pre (decString s)] }, r)

/-- `record_name_num`. -/
def recordNameNum (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match nameRef r tb with
    | none => none
    | some (pre, r) => match afterSpace r with
      | none => none
      | some r => match readNat r with
        | none => none
        | some (k, r) => match afterNewline r with
          | none => none
          | some r => some ({ tb with names := tb.names ++ [.num pre k] }, r)

/-- `record_name`: `N <id> a` | `N <id> s <pre> <string>` | `N <id> n <pre>
<k>`. -/
def recordName (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match expectId bs tb.names.length with
  | none => none
  | some r => match afterSpace r with
    | none => none
    | some [] => none
    | some (k :: r) =>
      if k = 97 then
        match afterNewline r with
        | none => none
        | some r => some ({ tb with names := tb.names ++ [.anonymous] }, r)
      else if k = 115 then recordNameStr r tb
      else if k = 110 then recordNameNum r tb
      else none

/-- `record_level_succ`. -/
def recordLevelSucc (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match levelRef r tb with
    | none => none
    | some (u, r) => match afterNewline r with
      | none => none
      | some r => some ({ tb with levels := tb.levels ++ [.succ u] }, r)

/-- `record_level_binop`: the `m` and `i` arms. -/
def recordLevelBinop (bs : Bytes) (tb : Tables) (isMax : Bool) :
    Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match levelRef r tb with
    | none => none
    | some (u, r) => match afterSpace r with
      | none => none
      | some r => match levelRef r tb with
        | none => none
        | some (v, r) => match afterNewline r with
          | none => none
          | some r =>
            some ({ tb with levels :=
              tb.levels ++ [if isMax then .max u v else .imax u v] }, r)

/-- `record_level_param`. -/
def recordLevelParam (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match nameRef r tb with
    | none => none
    | some (n, r) => match afterNewline r with
      | none => none
      | some r => some ({ tb with levels := tb.levels ++ [.param n] }, r)

/-- `record_level`: `L <id> z` | `s <u>` | `m <u> <v>` | `i <u> <v>` |
`p <name>`. -/
def recordLevel (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match expectId bs tb.levels.length with
  | none => none
  | some r => match afterSpace r with
    | none => none
    | some [] => none
    | some (k :: r) =>
      if k = 122 then
        match afterNewline r with
        | none => none
        | some r => some ({ tb with levels := tb.levels ++ [.zero] }, r)
      else if k = 115 then recordLevelSucc r tb
      else if k = 109 || k = 105 then recordLevelBinop r tb (k = 109)
      else if k = 112 then recordLevelParam r tb
      else none

/-- `record_pw_zero`. -/
def recordPwZero (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match nameList r tb with
    | none => none
    | some (ps, r) => match afterNewline r with
      | none => none
      | some r => some ({ tb with pws := tb.pws ++ [.ifAllZero ps] }, r)

/-- `record_pw`: `W <id> n` | `W <id> z <names>`. -/
def recordPw (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match expectId bs tb.pws.length with
  | none => none
  | some r => match afterSpace r with
    | none => none
    | some [] => none
    | some (k :: r) =>
      if k = 110 then
        match afterNewline r with
        | none => none
        | some r => some ({ tb with pws := tb.pws ++ [.never] }, r)
      else if k = 122 then recordPwZero r tb
      else none

/-- `record_expr_bvar`. -/
def recordExprBvar (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match readNat r with
    | none => none
    | some (k, r) => match afterNewline r with
      | none => none
      | some r => some ({ tb with exprs := tb.exprs ++ [.bvar k] }, r)

/-- `record_expr_fvar`. -/
def recordExprFvar (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match readNat r with
    | none => none
    | some (idx, r) => match afterSpace r with
      | none => none
      | some r => match exprRef r tb with
        | none => none
        | some (ty, r) => match afterNewline r with
          | none => none
          | some r => some ({ tb with exprs := tb.exprs ++ [.fvar idx ty] }, r)

/-- `record_expr_sort`. -/
def recordExprSort (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match levelRef r tb with
    | none => none
    | some (u, r) => match afterNewline r with
      | none => none
      | some r => some ({ tb with exprs := tb.exprs ++ [.sort u] }, r)

/-- `record_expr_const`. -/
def recordExprConst (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match nameRef r tb with
    | none => none
    | some (n, r) => match afterSpace r with
      | none => none
      | some r => match levelList r tb with
        | none => none
        | some (us, r) => match afterNewline r with
          | none => none
          | some r => some ({ tb with exprs := tb.exprs ++ [.const n us] }, r)

/-- `record_expr_app`. -/
def recordExprApp (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match exprRef r tb with
    | none => none
    | some (f, r) => match afterSpace r with
      | none => none
      | some r => match exprRef r tb with
        | none => none
        | some (a, r) => match afterNewline r with
          | none => none
          | some r => some ({ tb with exprs := tb.exprs ++ [.app f a] }, r)

/-- `record_expr_binder`: the `l` and `f` arms. -/
def recordExprBinder (bs : Bytes) (tb : Tables) (isLam : Bool) :
    Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match exprRef r tb with
    | none => none
    | some (ty, r) => match afterSpace r with
      | none => none
      | some r => match exprRef r tb with
        | none => none
        | some (body, r) => match afterSpace r with
          | none => none
          | some r => match pwRef r tb with
            | none => none
            | some (pw, r) => match afterNewline r with
              | none => none
              | some r =>
                some ({ tb with exprs := tb.exprs ++
                  [if isLam then .lam ty body ⟨pw⟩ else .forallE ty body ⟨pw⟩] }, r)

/-- `record_expr_let`. -/
def recordExprLet (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match exprRef r tb with
    | none => none
    | some (ty, r) => match afterSpace r with
      | none => none
      | some r => match exprRef r tb with
        | none => none
        | some (v, r) => match afterSpace r with
          | none => none
          | some r => match exprRef r tb with
            | none => none
            | some (body, r) => match afterNewline r with
              | none => none
              | some r =>
                some ({ tb with exprs := tb.exprs ++ [.letE ty v body] }, r)

/-- `record_expr_nat_lit`. -/
def recordExprNatLit (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match readBigNat r with
    | none => none
    | some (n, r) => match afterNewline r with
      | none => none
      | some r =>
        some ({ tb with exprs := tb.exprs ++ [.lit (.natVal n)] }, r)

/-- `record_expr_str_lit`. -/
def recordExprStrLit (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match readString r with
    | none => none
    | some (s, r) => match afterNewline r with
      | none => none
      | some r =>
        some ({ tb with exprs := tb.exprs ++ [.lit (.strVal (decString s))] }, r)

/-- `record_expr_proj`. -/
def recordExprProj (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match afterSpace bs with
  | none => none
  | some r => match nameRef r tb with
    | none => none
    | some (sn, r) => match afterSpace r with
      | none => none
      | some r => match readNat r with
        | none => none
        | some (idx, r) => match afterSpace r with
          | none => none
          | some r => match exprRef r tb with
            | none => none
            | some (s, r) => match afterNewline r with
              | none => none
              | some r =>
                some ({ tb with exprs := tb.exprs ++ [.proj sn idx s] }, r)

/-- `record_expr`: `E <id> <kind> …`, the ten `Expr` constructors. -/
def recordExpr (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match expectId bs tb.exprs.length with
  | none => none
  | some r => match afterSpace r with
    | none => none
    | some [] => none
    | some (k :: r) =>
      if k = 98 then recordExprBvar r tb
      else if k = 118 then recordExprFvar r tb
      else if k = 115 then recordExprSort r tb
      else if k = 99 then recordExprConst r tb
      else if k = 97 then recordExprApp r tb
      else if k = 108 || k = 102 then recordExprBinder r tb (k = 108)
      else if k = 116 then recordExprLet r tb
      else if k = 110 then recordExprNatLit r tb
      else if k = 103 then recordExprStrLit r tb
      else if k = 112 then recordExprProj r tb
      else none

/-! ## The payload record (FORMAT.md §4) -/

/-- `pins_eight_from`: the eight pinned defining expressions. -/
def pinsEightFrom (bs : Bytes) (tb : Tables) : Nat → List Expr →
    Option (List Expr × Bytes)
  | 0, out => some (out, bs)
  | k + 1, out =>
    match afterSpace bs with
    | none => none
    | some r => match exprRef r tb with
      | none => none
      | some (e, r) => pinsEightFrom r tb k (out ++ [e])

/-- `pins_eight`. -/
def pinsEight (bs : Bytes) (tb : Tables) : Option (List Expr × Bytes) :=
  pinsEightFrom bs tb 8 []

/-- `proofs_eight_from`: the eight counted certificate lists. -/
def proofsEightFrom (bs : Bytes) (tb : Tables) : Nat → List (List Expr) →
    Option (List (List Expr) × Bytes)
  | 0, out => some (out, bs)
  | k + 1, out =>
    match afterSpace bs with
    | none => none
    | some r => match exprList r tb with
      | none => none
      | some (es, r) => proofsEightFrom r tb k (out ++ [es])

/-- `proofs_eight`. -/
def proofsEight (bs : Bytes) (tb : Tables) :
    Option (List (List Expr) × Bytes) :=
  proofsEightFrom bs tb 8 []

/-- `record_pin_set`: `S <string> <expr>×8 (<k> <expr>*)×8`.  An `S` record
carries no id — the record *is* the payload. -/
def recordPinSet (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  match readString bs with
  | none => none
  | some (toolchain, r) => match pinsEight r tb with
    | none => none
    | some (pins, r) => match proofsEight r tb with
      | none => none
      | some (proofs, r) => match afterNewline r with
        | none => none
        | some r =>
          match pins, proofs with
          | [p0, p1, p2, p3, p4, p5, p6, p7],
            [q0, q1, q2, q3, q4, q5, q6, q7] =>
            some ({ tb with sets := tb.sets ++ [{
              toolchain := decString toolchain
              divPin := p0, modPin := p1, gcdPin := p2, landPin := p3
              lorPin := p4, xorPin := p5, shiftLeftPin := p6
              shiftRightPin := p7
              divProofs := q0, modProofs := q1, gcdProofs := q2
              landProofs := q3, lorProofs := q4, xorProofs := q5
              shiftLeftProofs := q6, shiftRightProofs := q7 }] }, r)
          | _, _ => none

/-! ## The pass -/

/-- `run_footer`: `nd <count>\n` and nothing after it (the `e` is already
consumed). -/
def runFooter : Bytes → Tables → Option (List NatOpPinSet)
  | 110 :: 100 :: bs, tb =>
    match afterSpace bs with
    | none => none
    | some r => match readIndex r with
      | none => none
      | some (n, r) => match afterNewline r with
        | none => none
        | some r =>
          if r ≠ [] || n ≠ tb.sets.length then none else some tb.sets
  | _, _ => none

/-- The record dispatch of `run_records`, as its own function so that the
pass's step is one call. -/
def recordStep (k : Nat) (bs : Bytes) (tb : Tables) : Option (Tables × Bytes) :=
  if k = 78 then recordName bs tb
  else if k = 76 then recordLevel bs tb
  else if k = 87 then recordPw bs tb
  else if k = 69 then recordExpr bs tb
  else if k = 83 then recordPinSet bs tb
  else none

/-- `run_records`: one record per step, stopping at the footer.  `fuel` is a
byte budget — `decode` passes the byte count and every step consumes at least
one byte, so it never binds. -/
def runRecords : Nat → Bytes → Tables → Option (List NatOpPinSet)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | f + 1, k :: bs, tb =>
    if k = 101 then runFooter bs tb
    else match afterSpace bs with
      | none => none
      | some body => match recordStep k body tb with
        | none => none
        | some (tb, r) => runRecords f r tb

/-- **The decoder.**  `kernel::pins_decode::decode`, in Lean. -/
def decode (bs : Bytes) : Option (List NatOpPinSet) :=
  if startsWith bs headerBytes then
    runRecords bs.length (bs.drop headerBytes.length) tablesNew
  else none

/-! ## Self-tests

`Refine/PinsBytes.lean` … `Refine/PinsRead.lean` prove that this file is both
`kernel::pins_decode` and `ConRon.Dump.parsePins`.  Until they are read, these
`#guard`s are what says the *definitions* are right — and they stay afterwards,
because a mirror is only as good as the day someone edits the Rust.

The first block is `kernel::pins_decode`'s own `mod tests`, text for text (the
empty dump, eight malformed ones, the `\<hex>;` escape and its surrogate
rejection): accept and reject must agree byte for byte.  The second is a dump
exercising **every** record kind a pin text can hold — `N` all three arms, `L`
all five, `W` both, `E` all ten, `S`, the footer — read both ways and compared
*value for value*, which is `pins_decode_refines` on those inputs. -/

deriving instance DecidableEq for ConLeche.NatOpPinSet

/-- A text as its bytes (these test texts are ASCII, so this is `absText`'s
inverse on them). -/
private def testBytes (s : String) : Bytes := s.toList.map Char.toNat

#guard (decode (testBytes "con-ron-pins/1\nend 0\n")).isSome
#guard decide (decode (testBytes "con-ron-pins/1\nend 0\n") = some [])
#guard (decode (testBytes "con-ron-pins/2\nend 0\n")).isNone
#guard (decode (testBytes "con-ron-pins/1\nend 1\n")).isNone
#guard (decode (testBytes "con-ron-pins/1\nD a 0\nend 0\n")).isNone
#guard (decode (testBytes "con-ron-pins/1\nN 1 a\nend 0\n")).isNone
#guard (decode (testBytes "con-ron-pins/1\nN 0 s 0 1 a\nend 0\n")).isNone
#guard (decode (testBytes "con-ron-pins/1\nend 0\nN 0 a\n")).isNone
#guard (decode (testBytes "con-ron-pins/1\nend 0")).isNone
#guard (decode (testBytes "con-ron-pins/1\nN 0 a\nN 1 s 0 2 a\nend 0\n")).isNone
#guard (decode (testBytes
  "con-ron-pins/1\nN 0 a\nN 1 s 0 3 a\\20;b\nN 2 s 1 1 \\5c;\nN 3 s 2 1 \\10ffff;\nend 0\n")).isSome
#guard (decode (testBytes "con-ron-pins/1\nN 0 a\nN 1 s 0 1 \\d800;\nend 0\n")).isNone

/-- Every record kind a pin dump can hold, in one text. -/
private def testSample : String :=
  "con-ron-pins/1\nN 0 a\nN 1 s 0 3 Nat\nL 0 z\nW 0 n\nE 0 c 1 0\nE 1 b 0\n" ++
  "E 2 s 0\nE 3 a 0 1\nE 4 l 0 1 0\nE 5 f 0 1 0\nE 6 t 0 1 1\nE 7 n 12345\n" ++
  "E 8 g 3 a\\20;b\nE 9 p 1 0 0\nE 10 v 2 0\nL 1 s 0\nL 2 m 0 1\nL 3 i 0 1\n" ++
  "L 4 p 1\nW 1 z 2 1 1\n" ++
  "S 3 v99 0 0 0 0 0 0 0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 0\nend 1\n"

/-- The two readers agree, value for value: `pins_decode_refines` on `s`. -/
private def testAgree (s : String) : Bool :=
  decide ((ConRon.Dump.parsePins s).toOption = decode (testBytes s))

#guard (decode (testBytes testSample)).isSome
#guard ((decode (testBytes testSample)).getD []).length == 1
#guard testAgree "con-ron-pins/1\nend 0\n"
#guard testAgree testSample
#guard testAgree
  "con-ron-pins/1\nN 0 a\nN 1 s 0 3 a\\20;b\nN 2 s 1 1 \\5c;\nN 3 s 2 1 \\10ffff;\nend 0\n"
#guard testAgree
  "con-ron-pins/1\nN 0 a\nN 1 n 0 7\nL 0 z\nE 0 s 0\nS 0  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0\nend 1\n"

end ConRon.Refine.PinsDec
