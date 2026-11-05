/-
# `ConRon.Arena.Inductives.StoredRecs` — the stored recursors, against the generated ones

`ConLeche/Kernel/Inductives/StoredRecs.lean` over handles.  The installer
GENERATES every recursor of a block (`genRecCheck`) and installs the STORED one
— the record's type and its rules' right-hand sides — once the two agree up to
definitional equality.  Everything else of the installed recursor is the
generator's.  The Rust twin is `arena::inductives::stored_recs`.

**The deviations of this module** (the Rust's, item for item):

* **The operations are not a record**: `ops` and `w` are `Arena/Core.lean`'s
  entry points and `constsResolveFFast` at the `IFEnv` in hand, whose visibility
  bound holds the generated recursors (`checkBlockTailStored`).
* **The messages are constants**, so the `rec`/`ctor` arguments that only name
  the slot are gone.
* **Upstream's `==` on terms and names is handle equality**.
* **Terms read from the store take the state**: `storedNestedOk` and
  `storedFireOf` intern, so they are `AM` functions.
* **`storedClosed`** is the closedness test `recTyCheck` and `ruleAgree` both
  open with, one function.
-/
module

public import ConRon.Arena.Inductives.RecCheck

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:45-59 recDomsAt
**The stored type's domains against the generated one's**, binder by binder
from binder `j` on (`k` of them): each stored domain `isDefEq` to the generated
one at its depth, both telescopes opened at their own locals. -/
def recDomsAt (mode : CheckMode) (fe : IFEnv) (sfvs gfvs : List EIdx) :
    Nat → Nat → AM Unit
  | _, 0 => pure ()
  | j, k + 1 => do
    match sfvs[j]?, gfvs[j]? with
    | some sv, some gv => do
      let a ← fvarTypeD sv
      let b ← fvarTypeD gv
      unless ← isDefEqCore mode fe checkFuel j a b do
        fail (.invalid "the type of the recursor  is not the generated one: the domain of binder  differs")
      recDomsAt mode fe sfvs gfvs (j + 1) k
    | _, _ => fail (.internal "stored recursor: domain index")

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:61-74 recTyOpened
The stored and the generated type, opened `n` binders deep: the domains, then
the residues. -/
def recTyOpened (mode : CheckMode) (fe : IFEnv) (n : Nat) :
    Option (List EIdx × EIdx) → Option (List EIdx × EIdx) → AM Unit
  | some (sfvs, srest), some (gfvs, grest) => do
    recDomsAt mode fe sfvs gfvs 0 n
    unless ← isDefEqCore mode fe checkFuel n srest grest do
      fail (.invalid "the type of the recursor  is not the generated one: its body after the major differs")
  | none, _ => fail (.invalid "the type of the recursor  is not the generated one: it has fewer than  binders")
  | some _, none => fail (.internal "the generated type of the recursor  has fewer than  binders")

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:76-90 recTyCheck
con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:92-113 ruleAgree
The test both open with: `s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar`. -/
def storedClosed (s g : EIdx) : AM Bool := do
  if ← looseBVarsBoundedFast coreWalkFuel 0 s then
    if ← hasFvarFast coreWalkFuel s then pure false
    else do
      let h ← hasFvarFast coreWalkFuel g
      pure !h
  else pure false

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:76-90 recTyCheck
**The stored type's check**: closed, at the record's level parameters `lps`,
resolving, a type (inferred, a sort), and the generated one binder by binder up
to the major (`n` binders): the domains, then the residues. -/
def recTyCheck (mode : CheckMode) (fe : IFEnv) (lps : List NIdx) (n : Nat) (s g : EIdx) :
    AM Unit := do
  unless ← storedClosed s g do
    fail (.invalid "the type of the recursor  is not closed")
  unless ← allLevelParamsDefined lps s do
    fail (.invalid "undeclared universe parameter in the type of the recursor ")
  unless ← constsResolveFFast fe s do
    fail (← unresolvedConstsError "the type of the recursor" s)
  let st ← inferTypeCore mode fe checkFuel 0 s
  let _ ← ensureSortCore mode fe checkFuel 0 st
  let so ← openPisAtFvars n s 0
  let go ← openPisAtFvars n g 0
  recTyOpened mode fe n so go

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:92-113 ruleAgree
**One stored rule's check**: the stored right-hand side `s` is closed, at the
record's level parameters `lps`, resolving; it and the generated `g` are
inferred, their types are definitionally equal, and so are they. -/
def ruleAgree (mode : CheckMode) (fe : IFEnv) (lps : List NIdx) (s g : EIdx) : AM Unit := do
  unless ← storedClosed s g do
    fail (.invalid "the recursor 's rule for  has a right-hand side that is not closed")
  unless ← allLevelParamsDefined lps s do
    fail (.invalid "the recursor 's rule for  has an undeclared universe parameter")
  unless ← constsResolveFFast fe s do
    fail (← unresolvedConstsError "the recursor's rule" s)
  let ts ← inferTypeCore mode fe checkFuel 0 s
  let tg ← inferTypeCore mode fe checkFuel 0 g
  unless ← isDefEqCore mode fe checkFuel 0 ts tg do
    fail (.invalid "the recursor 's rule for  has a right-hand side whose type is not the generated one's")
  unless ← isDefEqCore mode fe checkFuel 0 s g do
    fail (.invalid "the recursor 's rule for  has a right-hand side that is not definitionally equal to the generated one")

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:115-131 storedNestedOk
The major's domain against the firing data: its head a constant at the firing
levels, its arguments the pins lifted past the index binders and the index
variables.  The Rust's `stored_nested_pins` and `stored_nested_bvars` are the two
`mapM`s. -/
def storedNestedDom (dom : EIdx) (n : Nat) (lvls : List LIdx) (pins : List EIdx) : AM Bool := do
  let hd ← getAppFn coreWalkFuel dom
  if hd.tag == ETag.const then
    match ← viewConst hd with
    | none => failDanglingE
    | some (_, us) => do
      let usv ← viewLs us
      if usv == lvls then
        let args ← getAppArgs coreWalkFuel dom
        let ps ← pins.mapM (liftLooseBVarsFast coreWalkFuel n 0)
        let bs ← (List.range n).mapM (fun i => internBVarE (n - 1 - i))
        pure (args == ps ++ bs)
      else pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:115-131 storedNestedOk
**An auxiliary recursor's stored type fires where the generated one does**: its
major's domain (binder `mI`) is the container at the firing data's levels,
applied to the pins lifted past the index binders and the index variables.
`true` at a member major (its rules fire `.plain`). -/
def storedNestedOk (ty : EIdx) (mI rP : Nat) : IRecRuleFire → AM Bool
  | .plain => pure true
  | .nested lvls pins => do
    match ← stripPis mI ty with
    | none => pure false
    | some (_, rest) =>
      if rest.tag == ETag.forallE then
        match ← viewBind rest with
        | none => failDanglingE
        | some (dom, _) => storedNestedDom dom (mI - rP) lvls pins
      else pure false

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:133-138 storedFireOf
The firing mode the generated recursor's rules carry at its major: `.nested` at
an outside major, `.plain` at a member. -/
def storedFireOf (M : TargetMajor) (rP : Nat) : AM IRecRuleFire :=
  match M.member with
  | none => auxRuleFire M rP
  | some _ => pure .plain

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:140-152 storedRulesShape
The stored rules' shape against the generated recursor's class: one rule per
constructor of the class, in order, each with its field count. -/
def storedRulesShape : List IRecRule → List (IConstantVal × Nat) → AM Unit
  | [], [] => pure ()
  | r :: rs, c :: cs => do
    unless r.ctor == c.1.name && r.nfields == c.2 do
      fail (.invalid "the recursor 's rule for  is not the generated one's (constructor ,  fields)")
    storedRulesShape rs cs
  | _, _ => fail (.invalid "the recursor  carries  more or fewer rules than the generated one ( unmatched)")

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:154-163 storedRulesCheck
The stored rules' checks, each against the generated right-hand side at its
position (a rule equal to the generated one needs none). -/
def storedRulesCheck (mode : CheckMode) (fe : IFEnv) (lps : List NIdx) :
    List IRecRule → List EIdx → AM Unit
  | r :: rs, g :: gs => do
    unless r.rhs == g do
      ruleAgree mode fe lps r.rhs g
    storedRulesCheck mode fe lps rs gs
  | [], [] => pure ()
  | _, _ => fail (.internal "the recursor : the generated rules are not one per stored rule")

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:165-172 storedRecCompare
**The comparison of one recursor**: its stored type unless it is the generated
one, and its stored rules. -/
def storedRecCompare (mode : CheckMode) (fe : IFEnv) (rc : RecShape)
    (g : IConstantVal × TargetMajor × List EIdx) : AM Unit := do
  unless rc.cvR.type == g.1.type do
    recTyCheck mode fe g.1.levelParams (rc.mI + 1) rc.cvR.type g.1.type
  storedRulesCheck mode fe g.1.levelParams rc.rules g.2.2

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:174-183 storedRecCheck
**One recursor, stored against generated**: the rules' shape and the stored
major's container, decided before anything is compared, then the comparison. -/
def storedRecCheck (mode : CheckMode) (fe : IFEnv) (rc : RecShape)
    (g : IConstantVal × TargetMajor × List EIdx) : AM Unit := do
  storedRulesShape rc.rules g.2.1.ctors
  let fire ← storedFireOf g.2.1 rc.rP
  unless ← storedNestedOk rc.cvR.type rc.mI rc.rP fire do
    fail (.internal "the recursor 's stored type does not apply its major's container at the generated firing data")
  storedRecCompare mode fe rc g

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:185-193 storedRecsCheck
**The block's stored recursors against the generated ones**, record by record
(the generated family is in the records' order). -/
def storedRecsCheck (mode : CheckMode) (fe : IFEnv) :
    List RecShape → List (IConstantVal × TargetMajor × List EIdx) → AM Unit
  | rc :: rcs, g :: gs => do
    storedRecCheck mode fe rc g
    storedRecsCheck mode fe rcs gs
  | [], [] => pure ()
  | _, _ => fail (.internal "stored recursors: the generated family is not the records'")

/-- con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:195-202 storedOut
**What is installed**: each generated recursor with the stored type and the
stored right-hand sides, at the generated recursor's name, level parameters and
major. -/
def storedOut (recs : List RecShape) (out : List (IConstantVal × TargetMajor × List EIdx)) :
    List (IConstantVal × TargetMajor × List EIdx) :=
  List.zipWith (fun rc g => (⟨g.1.name, g.1.levelParams, rc.cvR.type⟩, g.2.1, rc.rules.map (·.rhs)))
    recs out

end ConRon.Arena
