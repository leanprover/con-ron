/-
# `ConRon.Arena.Inductives.StreamRecs` — the stream's recursors, against the generated ones

`ConLeche/Kernel/Inductives/StreamRecs.lean` over handles.  The block's check
GENERATES every recursor of a block (`genRecCheck`) and compares the stream's
records with them up to definitional equality.  What is installed is the
record, read off the block (`declConstants`, upstream `blockRecs`); these checks
say that it is the generated recursor.  The records' K flags are checked
against the block (`streamKCheck`), and the block's declared feature flags are
validated (`blockFlagsCheck`).  The Rust twin is
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
* **The declared flags' checks fail in the state** (`blockFlagsCheck`): the
  cited pure check, run through `ofExcept`, reads the block's sort, a handle
  here (`largeElimFlagOk`); its `for` loop is `majorsFlagsCheck`, its `hasProj`
  the environment's `findTable?`, and `BlockShape.headName` (which only names
  the block in a message) is not ported.
-/
module

public import ConRon.Arena.Inductives.RecCheck

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:44-58 recDomsAt
con-leche: ConLeche/Cached/IndTail.lean:82-92 recDomsAtC
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

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:60-73 recTyOpened
con-leche: ConLeche/Cached/IndTail.lean:94-106 recTyOpenedC
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

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:75-89 recTyCheck
con-leche: ConLeche/Cached/IndTail.lean:108-120 recTyCheckC
con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:91-112 ruleAgree
con-leche: ConLeche/Cached/IndTail.lean:122-140 ruleAgreeC
The test both open with: `s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar`. -/
def streamClosed (s g : EIdx) : AM Bool := do
  if ← looseBVarsBoundedFast coreWalkFuel 0 s then
    if ← hasFvarFast coreWalkFuel s then pure false
    else do
      let h ← hasFvarFast coreWalkFuel g
      pure !h
  else pure false

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:75-89 recTyCheck
con-leche: ConLeche/Cached/IndTail.lean:108-120 recTyCheckC
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

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:91-112 ruleAgree
con-leche: ConLeche/Cached/IndTail.lean:122-140 ruleAgreeC
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

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:114-131 streamNestedOk
con-leche: ConLeche/Cached/IndTail.lean:66-80 streamNestedOkC
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

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:114-131 streamNestedOk
con-leche: ConLeche/Cached/IndTail.lean:66-80 streamNestedOkC
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

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:133-138 generatedFire
con-leche: ConLeche/Cached/IndTail.lean:58-62 generatedFireC
The firing mode the generated recursor's rules carry at its major
(`generatedRules`): `.nested` at an outside major, `.plain` at a member. -/
def generatedFire (M : TargetMajor) (rP : Nat) : AM IRecRuleFire :=
  match M.member with
  | none => auxRuleFire M rP
  | some _ => pure .plain

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:140-152 streamRulesShape
con-leche: ConLeche/Cached/IndTail.lean:142-152 streamRulesShapeC
The record's rules' shape against the generated recursor's class: one rule per
constructor of the class, in order, each with its field count. -/
def streamRulesShape : List IRecRule → List (IConstantVal × Nat) → AM Unit
  | [], [] => pure ()
  | r :: rs, c :: cs => do
    unless r.ctor == c.1.name && r.nfields == c.2 do
      fail (.invalid "the recursor 's rule for  is not the generated one's (constructor ,  fields)")
    streamRulesShape rs cs
  | _, _ => fail (.invalid "the recursor  carries  more or fewer rules than the generated one ( unmatched)")

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:154-165 streamRulesCheck
con-leche: ConLeche/Cached/IndTail.lean:154-164 streamRulesCheckC
The record's rules' checks: each binds its arguments (`ruleBinds`) and agrees
with the generated right-hand side at its position (a rule equal to the
generated one needs no comparison). -/
def streamRulesCheck (mode : CheckMode) (fe : IFEnv) (lps : List NIdx) (rP : Nat) :
    List IRecRule → List EIdx → AM Unit
  | r :: rs, g :: gs => do
    ruleBinds rP r
    unless r.rhs == g do
      ruleAgree mode fe lps r.rhs g
    streamRulesCheck mode fe lps rP rs gs
  | [], [] => pure ()
  | _, _ => fail (.internal "the recursor : the generated rules are not one per stored rule")

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:167-172 streamRecCompare
con-leche: ConLeche/Cached/IndTail.lean:166-171 streamRecCompareC
**The comparison of one recursor**: its type unless it is the generated one, and
its rules. -/
def streamRecCompare (mode : CheckMode) (fe : IFEnv) (rc : RecShape)
    (g : IConstantVal × TargetMajor × List EIdx) : AM Unit := do
  unless rc.cvR.type == g.1.type do
    recTyCheck mode fe g.1.levelParams (rc.mI + 1) rc.cvR.type g.1.type
  streamRulesCheck mode fe g.1.levelParams rc.rP rc.rules g.2.2

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:174-183 streamRecCheck
con-leche: ConLeche/Cached/IndTail.lean:173-180 streamRecCheckC
**One recursor, the stream's against the generated one**: the rules' shape and
the record's major's container, then the comparison. -/
def streamRecCheck (mode : CheckMode) (fe : IFEnv) (rc : RecShape)
    (g : IConstantVal × TargetMajor × List EIdx) : AM Unit := do
  streamRulesShape rc.rules g.2.1.ctors
  let fire ← generatedFire g.2.1 rc.rP
  unless ← streamNestedOk rc.cvR.type rc.mI rc.rP fire do
    fail (.invalid "the recursor 's stored type does not apply its major's container at the generated firing data")
  streamRecCompare mode fe rc g

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:185-193 streamRecsCheck
con-leche: ConLeche/Cached/IndTail.lean:182-189 streamRecsCheckC
**The block's recursors against the generated ones**, record by record (the
generated family is in the records' order). -/
def streamRecsCheck (mode : CheckMode) (fe : IFEnv) :
    List RecShape → List (IConstantVal × TargetMajor × List EIdx) → AM Unit
  | rc :: rcs, g :: gs => do
    streamRecCheck mode fe rc g
    streamRecsCheck mode fe rcs gs
  | [], [] => pure ()
  | _, _ => fail (.internal "stored recursors: the generated family is not the records'")

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:195-211 streamKCheck
**The records' K flags against the block**: each record's flag is the one the
generated recursor has (`recKExpected`), and at a block whose recursors carry
no rules (`BlockShape.noRules`) a record with rules is rejected; the messages
drop the interpolation. -/
def streamKCheck (p : BlockShape) :
    List RecShape → List (IConstantVal × TargetMajor × List EIdx) → AM Unit
  | rc :: rcs, g :: gs => do
    if p.noRules && !rc.rules.isEmpty then
      fail (.invalid "the recursor  carries reduction rules, but its block has no large \
        eliminator (hasLargeElim is false), so its recursors have none")
    else do
      unless rc.isK == recKExpected p g.2.1 do
        fail (.invalid "recursor  declares k := ; the generated recursor of this block is K-like")
      streamKCheck p rcs gs
  | _, _ => pure ()

/-! ## The declared feature flags -/

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:219-235 memberFlagsCheck
**One member's flags** (official's checks of lean4 PR #16595): `isK` only at
the first member of a block of one, a proposition with one constructor without
fields; `hasProjections` only at one constructor, no index, not impredicative;
`hasEta` only with `hasProjections`, at a block that is not recursive.  The
three conditions are named first, as the Rust computes them; the messages drop
the interpolation. -/
def memberFlagsCheck (p : BlockShape) (isRec : Bool) (i : Nat) (ms : MemberShape)
    (f : IndFlags) : AM Unit :=
  let kOk : Bool := match ms.ctors with
    | [c] => if i == 0 && p.k == 1 && p.isProp then c.2 == 0 else false
    | _ => false
  let projOk : Bool := if ms.ctors.length == 1 && ms.nIdx == 0 then
      (if f.isImpredicative then false else true)
    else false
  let etaOk : Bool := if f.hasProjections then (if isRec then false else true) else false
  if f.isK && !kOk then
    fail (.invalid "inductive type  is declared with K-like reduction (isK), but it is \
      not a proposition alone in its block with one constructor without fields")
  else if f.hasProjections && !projOk then
    fail (.invalid "inductive type  is declared with projections (hasProjections), but it \
      does not have exactly one constructor and no indices, or it is impredicative")
  else if f.hasEta && !etaOk then
    fail (.invalid "inductive type  is declared with eta (hasEta), but it has no \
      projections or is recursive")
  else pure ()

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:237-243 membersFlagsCheck
The members' flags, from position `i` on, pairwise, stopping at the shorter
list. -/
def membersFlagsCheck (p : BlockShape) (isRec : Bool) :
    Nat → List MemberShape → List IndFlags → AM Unit
  | i, ms :: rest, f :: fs => do
    memberFlagsCheck p isRec i ms f
    membersFlagsCheck p isRec (i + 1) rest fs
  | _, _, _ => pure ()

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:245-288 blockFlagsCheck
**Is the declared `hasLargeElim` allowed?** Only at a block that is not
impredicative and whose sort is never zero, or of one type with no constructor,
or with one constructor and `hasEta` or `isK`.  The sort, a handle, is read only
where the flag is on and the block not impredicative. -/
def largeElimFlagOk (p : BlockShape) (f0 : IndFlags) : AM Bool := do
  if f0.hasLargeElim then
    if f0.isImpredicative then pure false
    else do
      let l ← readLevelM p.resSort
      if Level.isNeverZero l then pure true
      else
        let n := p.numCtors
        pure (p.k == 1 && (n == 0 || (n == 1 && (f0.hasEta || f0.isK))))
  else pure true

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:245-288 blockFlagsCheck
The cited `for M in Ms do`: an outside class that is a proposition with one
constructor without fields is rejected, and so is an outside class with a
projection table (the cited `hasProj`, the environment's `findTable?`) at an
impredicative block. -/
def majorsFlagsCheck (p : BlockShape) (f0 : IndFlags) (fe : IFEnv) :
    List TargetMajor → AM Unit
  | [] => pure ()
  | M :: Ms =>
    match M.member with
    | some _ => majorsFlagsCheck p f0 fe Ms
    | none =>
      if p.isProp && (match M.ctors with | [c] => c.2 == 0 | _ => false) then
        fail (.invalid "inductive block  nests , a proposition with one constructor without \
          fields; its K-like reduction cannot be kept inside the block")
      else if f0.isImpredicative then
        match fe.findTable? M.ind with
        | some _ => fail (.invalid "inductive block  is impredicative (isImpredicative) and \
            nests , which has projections; an impredicative type cannot have projections")
        | none => majorsFlagsCheck p f0 fe Ms
      else majorsFlagsCheck p f0 fe Ms

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:245-288 blockFlagsCheck
**The block's declared feature flags, validated** (lean4 PR #16595; nothing at
a block without them): `isImpredicative` and `hasLargeElim` agree across the
block; `isImpredicative` only at a proposition; `hasLargeElim` is what the
recursor records eliminate at, and allowed only where `largeElimFlagOk` says;
the members' own flags (`membersFlagsCheck`); the outside classes
(`majorsFlagsCheck`).  `isRec` is official's `is_rec`, `Ms` the classes the
recursors eliminate, `fe` the environment whose projection tables say whether
a stored type has projections.  It reads the sort's handle, so it is an `AM`
function failing in the state, where the cited pure check is run through
`ofExcept` (with `memberFlagsCheck` and `membersFlagsCheck`, which the Rust
writes as fallible functions too). -/
def blockFlagsCheck (p : BlockShape) (isRec : Bool) (Ms : List TargetMajor) (fe : IFEnv) :
    AM Unit :=
  match p.flags with
  | none => pure ()
  | some fl => do
    let f0 := fl.headD default
    if fl.length != p.k then
      fail (.internal "inductive block : flags for  of  types")
    else if !(fl.all fun f => f.isImpredicative == f0.isImpredicative &&
        f.hasLargeElim == f0.hasLargeElim) then
      fail (.invalid "inductive block : its types disagree on isImpredicative or hasLargeElim")
    else if f0.isImpredicative && !p.isProp then
      fail (.invalid "inductive block  is declared impredicative (isImpredicative), but its \
        type is not a proposition")
    else if f0.hasLargeElim != p.large then
      fail (.invalid "inductive block : hasLargeElim is , but its recursors eliminate ")
    else if !(← largeElimFlagOk p f0) then
      fail (.invalid "inductive block  is declared with a large eliminator (hasLargeElim), but \
        it may be a proposition and is not a single type with no constructor, or with one \
        constructor that has eta or K-like reduction")
    else do
      membersFlagsCheck p isRec 0 p.members fl
      majorsFlagsCheck p f0 fe Ms

end ConRon.Arena
