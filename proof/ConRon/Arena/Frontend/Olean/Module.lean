/-
# `ConRon.Arena.Frontend.Olean.Module` — a module's views against each other (task #142)

The twin of `olean/module.rs`.  `Expo` and `hintsEq` are upstream's own.  An
`Expr` compares by handle: the store is hash-consed.
-/
module

public import ConLeche.Frontend.Olean.Module
public import ConRon.Arena.Frontend.Olean.View

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Region CEntryF CKindF OLeanLevel ModFiles Expo hintsEq constSkel moduleSkel Part)

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:46-49 rulesEq -/
def rulesEq : List (NIdx × Nat × EIdx) → List (NIdx × Nat × EIdx) → Bool
  | [], [] => true
  | (a, b, c) :: xs, (a', b', c') :: ys => a == a' && b == b' && c == c' && rulesEq xs ys
  | _, _ => false

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:51-67 entrySame
Structural equality of two stored constants. -/
def entrySame (a b : CEntryF NIdx EIdx) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
  match a.kind, b.kind with
  | .ax u, .ax u' => u == u'
  | .defn v h s, .defn v' h' s' => v == v' && hintsEq h h' && s == s'
  | .thm v al, .thm v' al' => v == v' && al == al'
  | .opaq v u, .opaq v' u' => v == v' && u == u'
  | .quot k, .quot k' => k == k'
  | .induct a b c d e f g h, .induct a' b' c' d' e' f' g' h' =>
    a == a' && b == b' && c == c' && d == d' && e == e' && f == f' && g == g' && h == h'
  | .ctor a b c d e, .ctor a' b' c' d' e' =>
    a == a' && b == b' && c == c' && d == d' && e == e'
  | .recur a b c d e f g h, .recur a' b' c' d' e' f' g' h' =>
    a == a' && b == b' && c == c' && d == d' && e == e' && rulesEq f f' && g == g' && h == h'
  | _, _ => false

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:69-78 kindWord
A stored constant's kind, for messages. -/
def kindWord : CKindF NIdx EIdx → String
  | .ax u => s!"axiom{if u then " (unsafe)" else ""}"
  | .defn _ _ s => s!"definition ({s})"
  | .thm .. => "theorem"
  | .opaq _ u => s!"opaque{if u then " (unsafe)" else ""}"
  | .quot _ => "quotient"
  | .induct .. => "inductive"
  | .ctor .. => "constructor"
  | .recur .. => "recursor"

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:80-94 expoOf
**The exported level of one private constant**, given the exported part's constant
of that name; `none` is a constant the exported part does not refine. -/
def expoOf (priv ex : CEntryF NIdx EIdx) : Option Expo :=
  if entrySame priv ex then some .same
  else if priv.name == ex.name && priv.levelParams == ex.levelParams && priv.type == ex.type then
    match priv.kind, ex.kind with
    | .defn _ _ s, .ax u => if u == (s != "safe") then some .hidden else none
    | .thm .., .ax u => if !u then some .hidden else none
    | .opaq _ u', .ax u => if u == u' then some .hidden else none
    | _, _ => none
  else none

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
The two failures of `expoOfParts`: its message (`Except String`), and `AM`'s own. -/
def expoStep (pk : OleanPins) (r : Region) (privIdx : Std.HashMap NIdx Nat) (privLocs : Array Nat)
    (cs : Array (CEntryF NIdx EIdx)) (expo : Array Expo) (c : Nat) :
    AM (Except String (Array Expo)) := do
  let some se := constSkel r c | pure (.error "malformed exported constant")
  let some en ← nameP pk r se.name | pure (.error "malformed exported constant")
  let enName ← readName en
  let some i := privIdx[en]? |
    pure (.error s!"the exported constant {enName} is not stored at the private level")
  let some sp := (privLocs[i]?).bind (constSkel r) | pure (.error "malformed private constant")
  let samePtrs : Bool := se.type == sp.type && se.levelParams == sp.levelParams
  let hiddenKind : Bool := match se.kind, sp.kind with
    | .ax u, .defn _ _ s => u == (s != "safe")
    | .ax u, .thm .. => !u
    | .ax u, .opaq _ u' => u == u'
    | _, _ => false
  if hiddenKind && samePtrs then pure (.ok (expo.set! i .hidden))
  else
    let some e ← entryAt pk r c | pure (.error "malformed exported constant")
    let some pc := cs[i]? | pure (.error "malformed private constant")
    match expoOf pc e with
    | some x => pure (.ok (expo.set! i x))
    | none =>
      pure (.error s!"the exported view of {enName} is not a refinement of its private \
        constant ({kindWord pc.kind} / {kindWord e.kind})")

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
The `for c in skE.consts` of `expoOfParts`. -/
def expoLoop (pk : OleanPins) (r : Region) (privLoc : Std.HashMap Nat Nat)
    (privIdx : Std.HashMap NIdx Nat) (privLocs : Array Nat) (cs : Array (CEntryF NIdx EIdx)) :
    List Nat → Array Expo → AM (Except String (Array Expo))
  | [], expo => pure (.ok expo)
  | c :: rest, expo => do
    match privLoc[c]? with
    | some i => expoLoop pk r privLoc privIdx privLocs cs rest (expo.set! i .same)
    | none =>
      match ← expoStep pk r privIdx privLocs cs expo c with
      | .error m => pure (.error m)
      | .ok expo => expoLoop pk r privLoc privIdx privLocs cs rest expo

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
**The exported level of a module's private constants**. -/
def expoOfParts (pk : OleanPins) (r : Region) (privAddr expAddr : UInt64)
    (cs : Array (CEntryF NIdx EIdx)) : AM (Except String (Array Expo)) := do
  let some skP := moduleSkel r privAddr | pure (.error "malformed private part")
  let some skE := moduleSkel r expAddr | pure (.error "malformed exported part")
  let privLoc : Std.HashMap Nat Nat :=
    skP.consts.foldl (fun (m, i) c => (m.insert c i, i + 1)) ({}, 0) |>.1
  let privLocs := skP.consts.toArray
  let privIdx : Std.HashMap NIdx Nat :=
    cs.size.fold (init := {}) fun i _ acc => acc.insert cs[i].name i
  expoLoop pk r privLoc privIdx privLocs cs skE.consts (cs.map fun _ => .absent)

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:140-159 checkViews
**The views of a module against each other**: for each private constant, its
exported level.  Every constant is `.same` in a classic module. -/
def checkViews (pk : OleanPins) (m : Name) (f : ModFiles) (v : AllViews) : AM (Array Expo) := do
  let bad (what : String) : CheckError := .internal s!"module {m}: {what}"
  match f.server, f.private with
  | some s, some p =>
    unless f.isModule do return v.private.constants.map fun _ => .same
    match Region.ofParts #[f.exported, s, p] with
    | .error e => fail (toArenaError e)
    | .ok r =>
      unless v.server.isModule do
        fail (bad "the server part is not of a module of the module system, the exported part is")
      unless v.private.isModule do
        fail (bad "the private part is not of a module of the module system, the exported part is")
      let exp := f.exported.moduleDataAddr
      let e1 ← expoOfParts pk r p.moduleDataAddr exp v.private.constants
      let e2 ← expoOfParts pk r p.moduleDataAddr s.moduleDataAddr v.private.constants
      match e1, e2 with
      | .ok expo, .ok _ => pure expo
      | .error msg, _ => fail (bad s!"the exported part: {msg}")
      | _, .error msg => fail (bad s!"the server part: {msg}")
  | _, _ => pure (v.private.constants.map fun _ => .same)

end ConRon.Arena.Frontend.Olean
