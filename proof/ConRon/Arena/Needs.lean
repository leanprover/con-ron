/-
# `ConRon.Arena.Needs` — what a record reads

The twin of con-leche's `ConLeche/Cached/Needs.lean`: the names a term, a constant's laws and a
projection table read, as one memoised walk of each expression's DAG (`needsGo`).  Its reader is
the solution's justification (`Arena/Justify.lean`).

The walk's state (`NeedsSt`) is the compound nodes walked, keyed by the handle (hash-consing makes
the handle the node), and the names so far, as a list.  The walk recurses once per level of the
expression with the core's walk fuel, as `mentionsConstGo` does; a walk that runs out is an
internal error, never a verdict.
-/
module

public import ConRon.Arena.Inductives.StructParts
public import ConRon.Arena.TrustAxioms

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Cached/Needs.lean:71-72 NeedsSt — the walk's state through several
expressions: the compound nodes walked, and the names so far. -/
structure NeedsSt where
  seen : Std.HashMap EIdx Bool
  acc : List NIdx

/-- con-leche: ConLeche/Cached/Needs.lean:71-72 NeedsSt — the state of a fresh walk,
con-leche's `({}, #[])`. -/
def NeedsSt.empty : NeedsSt := ⟨∅, []⟩

/-- con-leche: none — `acc ++ (ns.drop i).take (stop - i)` over name-handle lists, the Rust's
cursor append. -/
def nidxAppend (acc ns : List NIdx) (i stop : Nat) : List NIdx :=
  acc ++ (ns.drop i).take (stop - i)

/-- con-leche: ConLeche/Cached/Needs.lean:24-29 litNeeds — **the names a literal reads**, pushed
onto `acc`: the `Nat` basis, and for a string the string-support constants.  They are the literal
guards' ten names, in the cited order (`litGuardNames`): a numeral's are the first three. -/
def litNeeds (l : ConLeche.Literal) (acc : List NIdx) : AM (List NIdx) := do
  let ns ← litGuardNames
  match l with
  | .natVal _ => pure (nidxAppend acc ns 0 3)
  | .strVal _ => pure (nidxAppend acc ns 0 ns.length)

/-- con-leche: ConLeche/Cached/Needs.lean:42-69 needsGo
con-leche: ConLeche/Cached/Needs.lean:31-40 _root_.ConLeche.Expr.needs — **`Expr.needs`, one
memoised walk of the DAG**: `seen` the compound nodes walked, `acc` the names so far.  A node is
recorded after its children.  The fuel bounds the depth. -/
def needsGo (seen : Std.HashMap EIdx Bool) (acc : List NIdx) :
    Nat → EIdx → AM (Std.HashMap EIdx Bool × List NIdx)
  | 0, _ => fail (.internal "fuel exhausted: needsGo")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure (seen, acc)
    | .sort _ => pure (seen, acc)
    | .lit l => do
      let acc ← litNeeds l acc
      pure (seen, acc)
    | .const n _ => pure (seen, acc ++ [n])
    | v =>
      match seen[h]? with
      | some _ => pure (seen, acc)
      | none => do
        let (s, a) ← match v with
          | .fvar _ ty => needsGo seen acc fuel ty
          | .app f a => do
            let (s, c) ← needsGo seen acc fuel f
            needsGo s c fuel a
          | .lam ty body => do
            let (s, c) ← needsGo seen acc fuel ty
            needsGo s c fuel body
          | .forallE ty body => do
            let (s, c) ← needsGo seen acc fuel ty
            needsGo s c fuel body
          | .letE ty val body => do
            let (s, c) ← needsGo seen acc fuel ty
            let (s2, c2) ← needsGo s c fuel val
            needsGo s2 c2 fuel body
          | .proj s _ sub => needsGo seen (acc ++ [s]) fuel sub
          | _ => pure (seen, acc)
        pure (s.insert h true, a)

/-- con-leche: ConLeche/Cached/Needs.lean:74-75 NeedsSt.expr — one more expression's names. -/
def NeedsSt.expr (x : NeedsSt) (e : EIdx) : AM NeedsSt := do
  let (seen, acc) ← needsGo x.seen x.acc coreWalkFuel e
  pure ⟨seen, acc⟩

/-- con-leche: ConLeche/Cached/Needs.lean:77-78 NeedsSt.names — some names. -/
def NeedsSt.names (x : NeedsSt) (ns : List NIdx) : NeedsSt :=
  ⟨x.seen, nidxAppend x.acc ns 0 ns.length⟩

/-- con-leche: ConLeche/Cached/Needs.lean:77-78 NeedsSt.names — one name, con-leche's
`x.names [n]`. -/
def NeedsSt.name (x : NeedsSt) (n : NIdx) : NeedsSt :=
  ⟨x.seen, x.acc ++ [n]⟩

/-- con-leche: ConLeche/Cached/Needs.lean:80-85 NeedsSt.rule — the cited
`pins.foldl NeedsSt.expr`. -/
def NeedsSt.exprs (x : NeedsSt) : List EIdx → AM NeedsSt
  | [] => pure x
  | e :: es => do
    let x2 ← x.expr e
    x2.exprs es

/-- con-leche: ConLeche/Cached/Needs.lean:80-85 NeedsSt.rule — **what a recursor rule reads**:
its right-hand side, its constructor, a nested datum's pins. -/
def NeedsSt.rule (x : NeedsSt) (r : IRecRule) : AM NeedsSt := do
  let x1 ← x.expr r.rhs
  let x2 := x1.name r.ctor
  match r.fire with
  | .nested _ pins => x2.exprs pins
  | _ => pure x2

/-- con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const — the cited
`rules.foldl NeedsSt.rule`. -/
def NeedsSt.rules (x : NeedsSt) : List IRecRule → AM NeedsSt
  | [] => pure x
  | r :: rs => do
    let x2 ← x.rule r
    x2.rules rs

/-- con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint — the second summand, pushed
onto `xs`: a compiler-trust operation's element type. -/
def pinFootprintReduce (n : NIdx) (xs : List NIdx) : AM (List NIdx) := do
  if (← reduceOpNames).contains n then pure (xs ++ [← reduceElemName n])
  else pure xs

/-- con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint — the first summand: the
operation's dependencies, the `Nat` basis, and `Bool` for `Nat.beq`, `Nat.ble` and the division
(`dms`, the cited `natDivModNames`). -/
def pinFootprintNat (n : NIdx) (dms : List NIdx) : AM (List NIdx) := do
  let deps ← natOpDeps n
  let lits ← litGuardNames
  let xs := nidxAppend deps lits 0 3
  let be ← natBeqName
  let bl ← natBleName
  if n == be || n == bl || dms.contains n then
    let b ← boolName
    let bt ← boolTrueName
    let bf ← boolFalseName
    pure (xs ++ [b] ++ [bt] ++ [bf])
  else pure xs

/-- con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint — **the names a pinned
constant's fast path reads**: a certified `Nat` operation's dependencies and the `Nat` basis (and
`Bool` for the comparisons and the division), a compiler-trust operation's element type. -/
def pinFootprint (n : NIdx) : AM (List NIdx) := do
  let ops ← natOpNames
  let dms ← natDivModNames
  if ops.contains n || dms.contains n then
    let xs ← pinFootprintNat n dms
    pinFootprintReduce n xs
  else pinFootprintReduce n []

/-- con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const — **what a constant's laws read**:
its type, a definition's value, a recursor's rules, a type former's block, and its pin's
fast-path names. -/
def NeedsSt.const (x : NeedsSt) (ci : IConstantInfo) : AM NeedsSt := do
  let x1 ← x.expr ci.toConstantVal.type
  let x2 ← match ci with
    | .defnInfo _ v _ => x1.expr v
    | .recInfo _ _ _ _ rules => x1.rules rules
    | .indInfo _ caps => pure (x1.names caps.all)
    | _ => pure x1
  let fp ← pinFootprint ci.name
  pure (x2.names fp)

/-- con-leche: ConLeche/Cached/Needs.lean:97-99 NeedsSt.table — **what a table reads**: its
structure, its constructor, its bodies. -/
def NeedsSt.table (x : NeedsSt) (t : IProjTable) : AM NeedsSt :=
  ((x.name t.structName).name t.ctor).exprs t.bodies.toList

end ConRon.Arena
