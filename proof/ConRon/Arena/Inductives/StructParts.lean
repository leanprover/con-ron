/-
# `ConRon.Arena.Inductives.StructParts` — the direct install's generators
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/StructParts.lean`, over handles, as far as the
executed checker reads it after con-leche's uniform inductive route (task
#105): the parameter spines, the elimination level, the constructor-residual
test, and the projection table's generators (bodies, guards) with the two
memoised walks they share.  The recogniser and the generated recursor that
lived here (`structShape`, `structPartsCore?`, the family and spine
generators) went with the fixpoint route.

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
* **the fields' sorts are `List LIdx`, not the census's `LsIdx`.**
  `Arena/Env.lean`'s `IProjTable.guards` is a `List LIdx` (task #97e), and
  `structProjGuards` computes exactly that field; interning the list only to
  read it back at the table would be a round trip with no reader.  A `const`
  node's universe arguments stay `LsIdx`, as the representation requires;
* **the pure walk, the cutoff walk and the memoized walk collapse into one
  twin**, as task #97b's rule has it for the nine `…Go`/`…Fast` triples of
  `ExprOps`: `hasLooseBVar`, `hasLooseBVarB`, `hasLooseBVarBGo` and
  `hasLooseBVarBFast` are one algorithm and become one arena function, which
  cites all four.  The `@[csimp]` equivalence theorems have no arena twin —
  the substitution they license has already happened here.  Likewise
  `mentionsConst` / `mentionsConstGo` / `mentionsConstFast`.  The two
  `…MemoInv` predicates are census class (S), `Prop`-only apparatus the port
  skips;
* **the memos stay explicit arguments.**  con-leche threads a
  `Std.HashMap Expr Bool` through `hasLooseBVarBGo` and `mentionsConstGo`
  rather than putting it in a state, because the answer depends on data that
  is fixed for one call (`T`, and for `hasLooseBVarB` the index, which is in
  the key).  The twins do the same at `EIdx` keys — nothing is added to
  `AState`, and `structProjGuards`' one shared memo across `nF` calls is
  con-leche's own task #236 arrangement, unchanged.
-/
import ConRon.Arena.Core

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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:50-53 structPsAt
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:55-58 structElimLevel
The recursor's elimination level: the fresh parameter at the large
eliminator, `zero` at the small one. -/
def structElimLevel (elim : NIdx) (large : Bool) : AM LIdx :=
  if large then internLNode (.param elim) else internLNode .zero

/-! ## A constructor's residual at an indexed family -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:79-85 structCtorResidOk
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:87-93 structProjPs
The parameter spine of the generated projection types, spelled at the frame of
the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar (nP - k)`. -/
def structProjPs (nP : Nat) : AM (List EIdx) := structPsAt 1 nP

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:95-101 structProjArgP
The `j`-th earlier-field substitute in a tower entry's generated type: the
first-class node `t.j` (`.proj T j` of the subject). -/
def structProjArgP (T : NIdx) (j : Nat) : AM EIdx := do
  let b ← internE (.bvar 0)
  internE (.proj T j b)

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:103-109 structProjResidP
`structProjResid` in the `.proj`-node spelling: the constructor telescope
peeled at the parameters and the first `i` subject projections. -/
def structProjResidP (T : NIdx) (nP : Nat) (cty : EIdx) : Nat → AM (Option EIdx)
  | 0 => do instPisAtLift coreWalkFuel (← structProjPs nP) cty
  | i + 1 => do
    match ← structProjResidP T nP cty i with
    | some r => do instPisAtLift coreWalkFuel [← structProjArgP T i] r
    | none => pure none

/-! ## `hasLooseBVar` — one twin for the pure walk, the cutoff and the memo -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:190-195 Expr.hasLooseBVarBIns
Record one answer for `(e, i)` in the memo the walk hands back. -/
@[inline] def hasLooseBVarBIns (e : EIdx) (i : Nat)
    (r : Bool × Std.HashMap (EIdx × Nat) Bool) :
    Bool × Std.HashMap (EIdx × Nat) Bool :=
  (r.1, r.2.insert (e, i) r.1)

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:111-124 Expr.hasLooseBVar
con-leche: ConLeche/Kernel/Inductives/StructParts.lean:126-145 Expr.hasLooseBVarB
con-leche: ConLeche/Kernel/Inductives/StructParts.lean:197-233 Expr.hasLooseBVarBGo
Does `bvar i` occur loose in `e`?  con-leche's packed-bound cutoff
(`bvarB ≤ i`) and con-leche's per-call memo, both kept: the cutoff stops the
walk where the variable CANNOT occur, the memo shares a shared node's answer
across the paths that reach it.  The memo is keyed by the node and the index,
because the index shifts under binders. -/
def hasLooseBVarBGo (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat) :
    Nat → EIdx → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | 0, _ => fail (.internal "fuel exhausted: hasLooseBVarB")
  | fuel + 1, h => do
    let bb ← bvarB fuel h
    if bb ≤ i then pure (false, memo) else
    match ← view h with
    | .bvar j => pure (i == j, memo)
    | .fvar _ _ => pure (false, memo)
    | .sort _ => pure (false, memo)
    | .const _ _ => pure (false, memo)
    | .lit _ => pure (false, memo)
    | v =>
      match memo[(h, i)]? with
      | some r => pure (r, memo)
      | none => do
        let r ← match v with
          | .app f a => do
            match ← hasLooseBVarBGo memo i fuel f with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hasLooseBVarBGo memo i fuel a
          | .lam ty b _ => do
            match ← hasLooseBVarBGo memo i fuel ty with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
          | .forallE ty b _ => do
            match ← hasLooseBVarBGo memo i fuel ty with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
          | .letE t v b => do
            match ← hasLooseBVarBGo memo i fuel t with
            | (true, memo) => pure (true, memo)
            | (false, memo) => do
              match ← hasLooseBVarBGo memo i fuel v with
              | (true, memo) => pure (true, memo)
              | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
          | .proj _ _ sub => hasLooseBVarBGo memo i fuel sub
          | _ => pure (false, memo)
        pure (hasLooseBVarBIns h i r)

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:379-381 Expr.hasLooseBVarBFast
The executed `hasLooseBVarB` (one memoized DAG walk). -/
def hasLooseBVarBFast (i : Nat) (e : EIdx) : AM Bool := do
  pure (← hasLooseBVarBGo ∅ i coreWalkFuel e).1

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:388-396 structUsedLater
**Field `j` is used by a later field** — the official `infer_proj`'s
`has_loose_bvars(binding_body(r))` at step `j`. -/
def structUsedLater (cty : EIdx) (nP j : Nat) : AM Bool := do
  match ← stripPis (nP + j + 1) cty with
  | some (_, rest) => hasLooseBVarBFast 0 rest
  | none => pure false

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:424-429 structUsedLaterGo
Memoized `structUsedLater`, taking and returning the shared memo. -/
def structUsedLaterGo (memo : Std.HashMap (EIdx × Nat) Bool) (cty : EIdx)
    (nP j : Nat) : AM (Bool × Std.HashMap (EIdx × Nat) Bool) := do
  match ← stripPis (nP + j + 1) cty with
  | some (_, rest) => hasLooseBVarBGo memo 0 coreWalkFuel rest
  | none => pure (false, memo)

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:440-447 structUsedLaterList
`structUsedLater cty nP j` for `j = base, …, base + n - 1`, in order, through
one shared memo. -/
def structUsedLaterList (cty : EIdx) (nP : Nat) :
    Std.HashMap (EIdx × Nat) Bool → Nat → Nat → AM (List Bool)
  | _, 0, _ => pure []
  | memo, n + 1, base => do
    let r ← structUsedLaterGo memo cty nP base
    let rest ← structUsedLaterList cty nP r.2 n (base + 1)
    pure (r.1 :: rest)

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:398-411 structProjGuards
con-leche: ConLeche/Kernel/Inductives/StructParts.lean:477-487 structProjGuardsFast
**The projection guard levels**: for field `i`, its own sort joined with the
sorts of the earlier fields that a later field uses.  con-leche's two forms
are one twin here (task #97b's rule): the `nF` `structUsedLater` answers are
computed first through one shared memo (its task #236 arrangement), then the
fold runs over the recorded answers.  `sorts` and the result are `List LIdx`
— see the module note. -/
def structProjGuards (cty : EIdx) (nP nF : Nat) (sorts : List LIdx) :
    AM (List LIdx) := do
  let z ← zeroLevel
  let used ← structUsedLaterList cty nP ∅ nF 0
  let rec col : Nat → Nat → LIdx → AM LIdx
    | _, 0, acc => pure acc
    | j, k + 1, acc => do
      if used.getD j false then do
        let m ← internLNode (.max acc (sorts.getD j z))
        col (j + 1) k m
      else col (j + 1) k acc
  let rec row : Nat → Nat → AM (List LIdx)
    | _, 0 => pure []
    | i, k + 1 => do
      let g ← col 0 i (sorts.getD i z)
      let rest ← row (i + 1) k
      pure (g :: rest)
  row 0 nF

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:503-521 structProjBodiesGo
**The projection bodies of a recognised block**, one walk of the constructor
telescope: field `i`'s domain is body `i`, and the field is replaced by the
subject's projection `.proj T i (bvar 0)` before the walk continues. -/
def structProjBodiesGo (T : NIdx) : Nat → Nat → EIdx → AM (Option (List EIdx))
  | 0, _, _ => pure (some [])
  | k + 1, i, h => do
    if h.tag == ETag.forallE then
      match ← view h with
      | .forallE fdom body _ => do
        let a ← structProjArgP T i
        let b ← instantiate1LiftFast coreWalkFuel body a 0
        match ← structProjBodiesGo T k (i + 1) b with
        | some r => pure (some (fdom :: r))
        | none => pure none
      | _ => pure none
    else pure none

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:523-526 structProjBodies
The block's projection bodies, as the table stores them. -/
def structProjBodies (T : NIdx) (nP nF : Nat) (cty : EIdx) :
    AM (Option (Array EIdx)) := do
  match ← instPisAtLift coreWalkFuel (← structProjPs nP) cty with
  | some r => do
    match ← structProjBodiesGo T nF 0 r with
    | some l => pure (some l.toArray)
    | none => pure none
  | none => pure none

/-! ## `mentionsConst` — one twin for the pure walk and the memo -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:528-537 Expr.mentionsConst
con-leche: ConLeche/Kernel/Inductives/StructParts.lean:569-604 Expr.mentionsConstGo
Does the constant `T` occur in `e`?  A syntactic walk (`fvar` annotations
included; a `.proj` node names its structure), with con-leche's per-call memo
keyed by the node — `T` is fixed for the whole walk. -/
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
          | .lam ty body _ => do
            let (b₁, memo) ← mentionsConstGo T memo fuel ty
            let (b₂, memo) ← mentionsConstGo T memo fuel body
            pure (b₁ || b₂, memo)
          | .forallE ty body _ => do
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

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:677-679 Expr.mentionsConstFast
The executed `mentionsConst` (one memoized DAG walk). -/
def mentionsConst (T : NIdx) (e : EIdx) : AM Bool := do
  pure (← mentionsConstGo T ∅ coreWalkFuel e).1

end ConRon.Arena
