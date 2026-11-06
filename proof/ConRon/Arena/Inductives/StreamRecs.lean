/-
# `ConRon.Arena.Inductives.StreamRecs` — the stream's recursors, against the generated ones

`ConLeche/Kernel/Inductives/StreamRecs.lean` over handles.  The block's check
GENERATES every recursor of a block (`genRecCheck`) and compares the stream's
records with them up to definitional equality.  What is installed is the
record, read off the block (`declConstants`, upstream `blockRecs`); these checks
say that it is the generated recursor.  The records' K flags are checked
against the block (`streamKCheck`).  The Rust twin is
`arena::inductives::stream_recs`.

**The deviations of this module** (the Rust's, item for item):

* **The operations are not a record**: `ops` and `w` are `Arena/Core.lean`'s
  entry points and `constsResolveFFast` at the `IFEnv` in hand, which holds
  the constructors and the generated recursors.
* **The messages are constants**, so the `rec`/`ctor` arguments that only name
  the slot are gone.
* **Upstream's `==` on terms and names is handle equality**.
* **Terms read from the store take the state**: `streamNestedOk` and
  `generatedFire` intern, so they are `AM` functions.
* **`streamClosed`** is the closedness test `recTyCheck` and `ruleAgree` both
  open with, one function.
-/
module

public import ConRon.Arena.Inductives.RecCheck

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:41-55 recDomsAt
**A record's type's domains against the generated one's**, binder by binder
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

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:57-70 recTyOpened
The record's and the generated type, opened `n` binders deep: the domains, then
the residues. -/
def recTyOpened (mode : CheckMode) (fe : IFEnv) (n : Nat) :
    Option (List EIdx × EIdx) → Option (List EIdx × EIdx) → AM Unit
  | some (sfvs, srest), some (gfvs, grest) => do
    recDomsAt mode fe sfvs gfvs 0 n
    unless ← isDefEqCore mode fe checkFuel n srest grest do
      fail (.invalid "the type of the recursor  is not the generated one: its body after the major differs")
  | none, _ => fail (.invalid "the type of the recursor  is not the generated one: it has fewer than  binders")
  | some _, none => fail (.internal "the generated type of the recursor  has fewer than  binders")

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:72-86 recTyCheck
con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:88-109 ruleAgree
The test both open with: `s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar`. -/
def streamClosed (s g : EIdx) : AM Bool := do
  if ← looseBVarsBoundedFast coreWalkFuel 0 s then
    if ← hasFvarFast coreWalkFuel s then pure false
    else do
      let h ← hasFvarFast coreWalkFuel g
      pure !h
  else pure false

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:72-86 recTyCheck
**A record's type's check**: closed, at the record's level parameters `lps`,
resolving, a type (inferred, a sort), and the generated one binder by binder up
to the major (`n` binders): the domains, then the residues. -/
def recTyCheck (mode : CheckMode) (fe : IFEnv) (lps : List NIdx) (n : Nat) (s g : EIdx) :
    AM Unit := do
  unless ← streamClosed s g do
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

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:88-109 ruleAgree
**One rule's check**: the record's right-hand side `s` is closed, at the
record's level parameters `lps`, resolving; it and the generated `g` are
inferred, their types are definitionally equal, and so are they. -/
def ruleAgree (mode : CheckMode) (fe : IFEnv) (lps : List NIdx) (s g : EIdx) : AM Unit := do
  unless ← streamClosed s g do
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

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:111-128 streamNestedOk
The major's domain against the firing data: its head a constant at the firing
levels, its arguments the pins lifted past the index binders and the index
variables.  The Rust's `stream_nested_pins` and `stream_nested_bvars` are the two
`mapM`s. -/
def streamNestedDom (dom : EIdx) (n : Nat) (lvls : List LIdx) (pins : List EIdx) : AM Bool := do
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

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:111-128 streamNestedOk
**An auxiliary recursor's type fires where the generated one does**: its major's
domain (binder `mI`) is the container at the firing data's levels, applied to
the pins lifted past the index binders and the index variables.  `true` at a
member major (its rules fire `.plain`) and at `.levels`. -/
def streamNestedOk (ty : EIdx) (mI rP : Nat) : IRecRuleFire → AM Bool
  | .plain => pure true
  | .levels _ => pure true
  | .nested lvls pins => do
    match ← stripPis mI ty with
    | none => pure false
    | some (_, rest) =>
      if rest.tag == ETag.forallE then
        match ← viewBind rest with
        | none => failDanglingE
        | some (dom, _) => streamNestedDom dom (mI - rP) lvls pins
      else pure false

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:130-135 generatedFire
The firing mode the generated recursor's rules carry at its major
(`generatedRules`): `.nested` at an outside major, `.plain` at a member. -/
def generatedFire (M : TargetMajor) (rP : Nat) : AM IRecRuleFire :=
  match M.member with
  | none => auxRuleFire M rP
  | some _ => pure .plain

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:137-149 streamRulesShape
The record's rules' shape against the generated recursor's class: one rule per
constructor of the class, in order, each with its field count. -/
def streamRulesShape : List IRecRule → List (IConstantVal × Nat) → AM Unit
  | [], [] => pure ()
  | r :: rs, c :: cs => do
    unless r.ctor == c.1.name && r.nfields == c.2 do
      fail (.invalid "the recursor 's rule for  is not the generated one's (constructor ,  fields)")
    streamRulesShape rs cs
  | _, _ => fail (.invalid "the recursor  carries  more or fewer rules than the generated one ( unmatched)")

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:151-160 streamRulesCheck
The record's rules' checks, each against the generated right-hand side at its
position (a rule equal to the generated one needs none). -/
def streamRulesCheck (mode : CheckMode) (fe : IFEnv) (lps : List NIdx) :
    List IRecRule → List EIdx → AM Unit
  | r :: rs, g :: gs => do
    unless r.rhs == g do
      ruleAgree mode fe lps r.rhs g
    streamRulesCheck mode fe lps rs gs
  | [], [] => pure ()
  | _, _ => fail (.internal "the recursor : the generated rules are not one per stored rule")

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:162-167 streamRecCompare
**The comparison of one recursor**: its type unless it is the generated one, and
its rules. -/
def streamRecCompare (mode : CheckMode) (fe : IFEnv) (rc : RecShape)
    (g : IConstantVal × TargetMajor × List EIdx) : AM Unit := do
  unless rc.cvR.type == g.1.type do
    recTyCheck mode fe g.1.levelParams (rc.mI + 1) rc.cvR.type g.1.type
  streamRulesCheck mode fe g.1.levelParams rc.rules g.2.2

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:169-178 streamRecCheck
**One recursor, the stream's against the generated one**: the rules' shape and
the record's major's container, then the comparison. -/
def streamRecCheck (mode : CheckMode) (fe : IFEnv) (rc : RecShape)
    (g : IConstantVal × TargetMajor × List EIdx) : AM Unit := do
  streamRulesShape rc.rules g.2.1.ctors
  let fire ← generatedFire g.2.1 rc.rP
  unless ← streamNestedOk rc.cvR.type rc.mI rc.rP fire do
    fail (.invalid "the recursor 's stored type does not apply its major's container at the generated firing data")
  streamRecCompare mode fe rc g

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:180-188 streamRecsCheck
**The block's recursors against the generated ones**, record by record (the
generated family is in the records' order). -/
def streamRecsCheck (mode : CheckMode) (fe : IFEnv) :
    List RecShape → List (IConstantVal × TargetMajor × List EIdx) → AM Unit
  | rc :: rcs, g :: gs => do
    streamRecCheck mode fe rc g
    streamRecsCheck mode fe rcs gs
  | [], [] => pure ()
  | _, _ => fail (.internal "stored recursors: the generated family is not the records'")

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:190-201 streamKCheck
**The records' K flags against the block**: each record's flag is the one the
generated recursor has (`recKExpected`); the message drops the interpolation. -/
def streamKCheck (p : BlockShape) :
    List RecShape → List (IConstantVal × TargetMajor × List EIdx) → AM Unit
  | rc :: rcs, g :: gs => do
    unless rc.isK == recKExpected p g.2.1 do
      fail (.invalid "recursor  declares k := ; the generated recursor of this block is K-like")
    streamKCheck p rcs gs
  | _, _ => pure ()

end ConRon.Arena
