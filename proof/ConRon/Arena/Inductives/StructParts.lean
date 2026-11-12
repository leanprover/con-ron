/-
# `ConRon.Arena.Inductives.StructParts` — the direct install's generators
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/StructParts.lean`, over handles, as far as the
executed checker reads it after con-leche's uniform inductive route (task
#105): the parameter spines, the elimination level, the constructor-residual
test, the projection table's bodies, and the memoised occurrence walk
`mentionsConst`.  (The `hasLooseBVarB` walk and `structUsedLater` moved
upstream to `Kernel/CoreDefs.lean`; their twins are in `Arena/Core.lean`.)

**The systematic deviations** (all of them inherited from task #97c's list,
which is where they are argued; only what is NEW to this module is spelled out
here):

* every structural match on a term is a `view`, so a pure `Expr → α` becomes
  `EIdx → AM α` and every walk carries `coreWalkFuel`; a recursion structural
  on a binder count, a field index or a list takes none;
* every term the generators BUILD is interned, so a pure `Expr` constructor
  becomes `internE`;
* a level list `lps.map .param` is one interned `LsIdx` (`paramLevels`), which
  is what a `const` node carries;
* **the pure walk and the memoized walk collapse into one twin**, as task
  #97b's rule has it for the `…Go`/`…Fast` triples of `ExprOps`:
  `mentionsConst` / `mentionsConstGo` / `mentionsConstFast` are one algorithm.
  The `@[csimp]` equivalence theorem has no arena twin — the substitution it
  licenses has already happened here.  `MentionsMemoInv` is census class (S),
  `Prop`-only apparatus the port skips;
* **the memo stays an explicit argument.**  con-leche threads a
  `Std.HashMap Expr Bool` through `mentionsConstGo` rather than putting it in
  a state, because the answer depends on data that is fixed for one call
  (`T`).  The twin does the same at `EIdx` keys — nothing is added to
  `AState`.
-/
module

public import ConRon.Arena.Core

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## Level lists over handles -/

/-- con-leche: none — `lps.map .param`, interned: the universe arguments a
block's own constants carry.  con-leche writes the list inline at every use;
over handles a level list is a node, so it is built once by a function of its
own. -/
def paramLevels (lps : List NIdx) : AM LsIdx := do
  let rec go : List NIdx → AM (List LIdx)
    | [] => pure []
    | n :: ns => do
      let u ← internLNode (.param n)
      let rest ← go ns
      pure (u :: rest)
  internLsNode (← go lps)

/-! ## The spines -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:38-41 structPsAt
The parameter variables as seen from under `o` extra binders:
`p_k = bvar (o + nP - 1 - k)`. -/
def structPsAt (o nP : Nat) : AM (List EIdx) :=
  let rec go : Nat → Nat → AM (List EIdx)
    | 0, _ => pure []
    | n + 1, k => do
      let b ← internE (.bvar (o + nP - 1 - k))
      let rest ← go n (k + 1)
      pure (b :: rest)
  go nP 0

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:43-46 structElimLevel
The recursor's elimination level: the fresh parameter at the large
eliminator, `zero` at the small one. -/
def structElimLevel (elim : NIdx) (large : Bool) : AM LIdx :=
  if large then internLNode (.param elim) else internLNode .zero

/-! ## A constructor's residual at an indexed family -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:67-73 structCtorResidOk
A constructor residual's shape at an indexed family: the family at exactly the
parameter variables (`o` binders below the parameter frame) followed by `nIdx`
index expressions. -/
def structCtorResidOk (T : NIdx) (lps : List NIdx) (nP o nIdx : Nat)
    (cbody : EIdx) : AM Bool := do
  let us ← paramLevels lps
  let hd ← internE (.const T us)
  let fn ← getAppFn coreWalkFuel cbody
  let args ← getAppArgs coreWalkFuel cbody
  let ps ← structPsAt o nP
  pure (fn == hd && args.length == nP + nIdx && args.take ps.length == ps)

/-! ## The projection bodies -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:75-79 structProjPs
The parameter spine of the generated projection types, spelled at the frame of
the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar (nP - k)`. -/
def structProjPs (nP : Nat) : AM (List EIdx) := structPsAt 1 nP

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:81-87 structProjArgP
The `j`-th earlier-field substitute in a tower entry's generated type: the
first-class node `t.j` (`.proj T j` of the subject). -/
def structProjArgP (T : NIdx) (j : Nat) : AM EIdx := do
  let b ← internE (.bvar 0)
  internE (.proj T j b)

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:89-110 structProjBodiesGo
con-leche: ConLeche/Cached/CheckerC.lean:28-34 structProjBodiesGoC
**The projection bodies of a recognised block**, one walk of the constructor
telescope: field `i`'s raw domain is substituted once (`instantiateLiftFast`)
at the values of the binders before it, and the field's own value, the
subject's projection `.proj T i (bvar 0)`, is pushed onto the values before the
walk continues; the rest of the telescope is never rewritten.  `vs` is in PUSH
order: con-leche's list, innermost first, is its reverse. -/
def structProjBodiesGo (T : NIdx) (vs : Array EIdx) : Nat → Nat → EIdx → AM (Option (List EIdx))
  | 0, _, _ => pure (some [])
  | k + 1, i, h => do
    if h.tag == ETag.forallE then
      match ← view h with
      | .forallE fdom body => do
        let b ← instantiateLiftFast coreWalkFuel fdom vs 0
        let a ← structProjArgP T i
        match ← structProjBodiesGo T (vs.push a) k (i + 1) body with
        | some r => pure (some (b :: r))
        | none => pure none
      | _ => pure none
    else pure none

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:112-115 structProjBodies
con-leche: ConLeche/Cached/CheckerC.lean:36-41 structProjBodiesC
The block's projection bodies, as the table stores them: the parameter binders
skipped, then the fields' walk at the parameters' values (`structProjPs`,
which in push order is con-leche's reversed list itself). -/
def structProjBodies (T : NIdx) (nP nF : Nat) (cty : EIdx) :
    AM (Option (Array EIdx)) := do
  match ← stripPis nP cty with
  | some p => do
    let ps ← structProjPs nP
    match ← structProjBodiesGo T ps.toArray nF 0 p.2 with
    | some l => pure (some l.toArray)
    | none => pure none
  | none => pure none

/-! ## `mentionsConst` — `mentionsAnyConst` at one name -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:119-133 Expr.mentionsAnyConst
con-leche: ConLeche/Cached/ExprOpsC.lean:1783-1827 mentionsAnyConstXP
Does the constant `T` occur in `e`?  `mentionsAnyConst [T]`, the one name
the `sorryAx` test asks: a syntactic walk (`fvar` annotations included; a
`.proj` node names its structure) with a per-call memo keyed by the node, as
the cached walk has — `T` is fixed for the whole walk. -/
def mentionsConstGo (T : NIdx) (memo : Std.HashMap EIdx Bool) :
    Nat → EIdx → AM (Bool × Std.HashMap EIdx Bool)
  | 0, _ => fail (.internal "fuel exhausted: mentionsConst")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure (false, memo)
    | .sort _ => pure (false, memo)
    | .lit _ => pure (false, memo)
    | .const n _ => pure (n == T, memo)
    | v =>
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let (r, memo) ← match v with
          | .fvar _ ty => mentionsConstGo T memo fuel ty
          | .app f a => do
            let (b₁, memo) ← mentionsConstGo T memo fuel f
            let (b₂, memo) ← mentionsConstGo T memo fuel a
            pure (b₁ || b₂, memo)
          | .lam ty body => do
            let (b₁, memo) ← mentionsConstGo T memo fuel ty
            let (b₂, memo) ← mentionsConstGo T memo fuel body
            pure (b₁ || b₂, memo)
          | .forallE ty body => do
            let (b₁, memo) ← mentionsConstGo T memo fuel ty
            let (b₂, memo) ← mentionsConstGo T memo fuel body
            pure (b₁ || b₂, memo)
          | .letE ty val body => do
            let (b₁, memo) ← mentionsConstGo T memo fuel ty
            let (b₂, memo) ← mentionsConstGo T memo fuel val
            let (b₃, memo) ← mentionsConstGo T memo fuel body
            pure (b₁ || b₂ || b₃, memo)
          | .proj s _ sub => do
            let (b, memo) ← mentionsConstGo T memo fuel sub
            pure (s == T || b, memo)
          | _ => pure (false, memo)
        pure (r, memo.insert h r)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1829-1831 mentionsAnyConstC
The executed `mentionsAnyConst [T]` (one memoized DAG walk). -/
def mentionsConst (T : NIdx) (e : EIdx) : AM Bool := do
  pure (← mentionsConstGo T ∅ coreWalkFuel e).1

end ConRon.Arena
