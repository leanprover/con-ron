/-
# `ConRon.Arena.Frontend.Olean.Merge` — the closure's constants merged (task #142)

The twin of `olean/merge.rs`.  **The map holds a constant's position**,
`(module, index)` into the loaded modules that `Merged` owns; `Merged.get` is
upstream's `mg.map[n]?`.
-/
module

public import ConRon.Arena.Frontend.Olean.Closure

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (CEntryF CKindF closureFuel)

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:65-68 Merged
The merged constants and the order they were first stored in. -/
structure Merged where
  ls : Array Loaded
  map : Std.HashMap NIdx (Nat × Nat) := {}
  order : Array NIdx := #[]

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:65-68 Merged
`mg.map[n]?`. -/
def Merged.get (mg : Merged) (n : NIdx) : Option CEntry :=
  match mg.map[n]? with
  | none => none
  | some (m, i) => (mg.ls[m]?).bind (·.constants[i]?)

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap
The result of a telescope. -/
def isPropBody : Nat → EIdx → AM EIdx
  | 0, e => pure e
  | fuel + 1, e => do
    match ← view e with
    | .forallE _ b => isPropBody fuel b
    | _ => pure e

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap
The head constant of an application, and its argument count. -/
def isPropHead : Nat → EIdx → Nat → AM (Option (NIdx × Nat))
  | 0, _, _ => pure none
  | fuel + 1, e, k => do
    match ← view e with
    | .app f _ => isPropHead fuel f (k + 1)
    | .const n _ => pure (some (n, k))
    | _ => pure none

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap
A telescope's result after `k` binders. -/
def isPropDrop : Nat → EIdx → AM (Option EIdx)
  | 0, e => pure (some e)
  | k + 1, e => do
    match ← view e with
    | .forallE _ b => isPropDrop k b
    | _ => pure none

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap
Lean's `isPropCheap`: the statement is a telescope over a constant applied to as many
arguments as its own type has binders before a `Prop` result. -/
def isPropCheap (pk : OleanPins) (mg : Merged) (ty : EIdx) : AM Bool := do
  let b ← isPropBody closureFuel ty
  match ← isPropHead closureFuel b 0 with
  | none => pure false
  | some (n, k) =>
    match mg.get n with
    | none => pure false
    | some d =>
      match ← isPropDrop k d.c.type with
      | none => pure false
      | some x =>
        match ← view x with
        | .sort u => pure (u == pk.zero)
        | _ => pure false

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap
Lean's `isPropCheap` over any `headTy` (the Rust's `HeadTy`). -/
def isPropCheapF (pk : OleanPins) (headTy : NIdx → Option EIdx) (ty : EIdx) : AM Bool := do
  let b ← isPropBody closureFuel ty
  match ← isPropHead closureFuel b 0 with
  | none => pure false
  | some (n, k) =>
    match headTy n with
    | none => pure false
    | some t =>
      match ← isPropDrop k t with
      | none => pure false
      | some x =>
        match ← view x with
        | .sort u => pure (u == pk.zero)
        | _ => pure false

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:45-47 isPropCheap.headOf
The constant `isPropCheap` asks the type of. -/
def isPropCheapHeadOf (ty : EIdx) : AM (Option NIdx) := do
  let b ← isPropBody closureFuel ty
  match ← isPropHead closureFuel b 0 with
  | none => pure none
  | some (n, _) => pure (some n)

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:49-59 subsumesF
**`subsumesInfo`** over statements and kinds. -/
def subsumesF {E₁ E₂ : Type} (pk : OleanPins) (headTy : NIdx → Option EIdx) (cv₁ : StmtRec)
    (k₁ : CKindF NIdx E₁) (cv₂ : StmtRec) (k₂ : CKindF NIdx E₂) : AM Bool := do
  if cv₁.name == cv₂.name && cv₁.type == cv₂.type && cv₁.levelParams == cv₂.levelParams then
    match k₁, k₂ with
    | .thm _ a₁, .thm _ a₂ => pure (a₁ == a₂)
    | .thm _ a₁, .ax u₂ => pure (a₁ == [cv₂.name] && !u₂)
    | .ax u₁, .ax u₂ =>
      if u₁ == u₂ then isPropCheapF pk headTy cv₁.type else pure false
    | _, _ => pure false
  else pure false

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:61-63 subsumes
`subsumesInfo`: may `c₁` stand for `c₂`? -/
def subsumes (pk : OleanPins) (mg : Merged) (c₁ c₂ : CEntry) : AM Bool := do
  if c₁.c.name == c₂.c.name && c₁.c.type == c₂.c.type && c₁.c.levelParams == c₂.c.levelParams then
    match c₁.c.kind, c₂.c.kind with
    | .thm _ a₁, .thm _ a₂ => pure (a₁ == a₂)
    | .thm _ a₁, .ax u₂ => pure (a₁ == [c₂.c.name] && !u₂)
    | .ax u₁, .ax u₂ =>
      if u₁ == u₂ then isPropCheap pk mg c₁.c.type else pure false
    | _, _ => pure false
  else pure false

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:70-81 mergeEntry
**Merge one constant**, the `i`-th of module `m`, `c`. -/
def mergeEntry (pk : OleanPins) (mg : Merged) (m i : Nat) (c : CEntry) : AM Merged := do
  match mg.get c.c.name with
  | none =>
    pure { mg with map := mg.map.insert c.c.name (m, i), order := mg.order.push c.c.name }
  | some prev =>
    if ← subsumes pk mg c prev then
      pure { mg with map := mg.map.insert c.c.name (m, i) }
    else if ← subsumes pk mg prev c then pure mg
    else fail (.invalid s!"two modules store different constants named {← readName c.c.name}")

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:83-84 mergeAll
The closure's constants merged. -/
def mergeAll (pk : OleanPins) (ls : Array Loaded) : AM Merged := do
  let mut mg : Merged := { ls }
  for hm : m in [0:ls.size] do
    let l := ls[m]'hm.2.1
    for hi : i in [0:l.constants.size] do
      mg ← mergeEntry pk mg m i (l.constants[i]'hi.2.1)
  pure mg

end ConRon.Arena.Frontend.Olean
