/-
# `ConRon.Arena.Justify` — axioms justified by a solution

The twin of con-leche's `ConLeche/Cached/Justify.lean`.  A stream may declare more axioms than the
standard ones when a **solution** justifies them: a second stream, checked as usual, whose index
holds a constant of the same name and type, everything that type reads being the same constant in
both up to the names of its level parameters (`justifyWhy`, the cone walk `coneGo`).  A
definition, theorem or opaque constant whose value uses `sorryAx` is the axiom of its statement
(`sideRecord`).  Without a solution every record takes its own check (`checkRecord none` is
`checkDecl`).

**One store.**  Both streams' records are handles of one store, so con-leche's structural
comparisons (`copyB`, `refinesB`, `ProjTable.beqP`) are handle comparisons (`==`); a renaming of
level parameters is the core's level substitution (`IConstantInfo.atLps`, the cited `atLpsC`).

**The record's job** (`recordCheck`, `recordJob`, con-leche's `Cached/StreamIndex.lean`) lives here
rather than in `Arena/StreamIndex.lean`, whose index this module reads: Lean modules do not import
each other in a cycle, Rust modules do (`arena::stream_index` calls `arena::justify`).
-/
module

public import ConRon.Arena.StreamIndex
public import ConRon.Arena.Needs

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## Which records offer a statement -/

/-- con-leche: ConLeche/Cached/Justify.lean:47-51 builtinAxiomName — **the built-in axioms**: they
keep their own check, solution or not. -/
def builtinAxiomName (n : NIdx) : AM Bool := do
  let a ← propextName
  let b ← choiceName
  let c ← pinQuotSound
  let d ← pinSorryAx
  let f ← trustCompilerName
  let g ← ofReduceNatName
  let h ← ofReduceBoolName
  pure (n == a || n == b || n == c || n == d || n == f || n == g || n == h)

/-- con-leche: ConLeche/Cached/Justify.lean:53-61 sideRecord — a value record's arm: the axiom of
its statement when its value uses a hole (and its name is no built-in axiom's), the record itself
otherwise. -/
def sideRecordVal (d : IDeclaration) (cv : IConstantVal) (v : EIdx) : AM IDeclaration := do
  if ← builtinAxiomName cv.name then pure d
  else
    let sa ← pinSorryAx
    if ← mentionsConst sa v then pure (.axiomDecl cv) else pure d

/-- con-leche: ConLeche/Cached/Justify.lean:53-61 sideRecord — **a definition, theorem or opaque
constant whose value uses a hole is the axiom of its statement**; every other record is itself. -/
def sideRecord (d : IDeclaration) : AM IDeclaration :=
  match d with
  | .defnDecl cv v _ => sideRecordVal d cv v
  | .thmDecl cv v => sideRecordVal d cv v
  | .opaqueDecl cv v => sideRecordVal d cv v
  | _ => pure d

/-- con-leche: ConLeche/Cached/Justify.lean:63-67 sideRecords — **the records a fold with a
solution checks**: every record through `sideRecord`, onto `out`.  The cited `none` arm is the flat path,
which does not call this. -/
def sideRecordsGo (out : List IDeclaration) : List IDeclaration → AM (List IDeclaration)
  | [] => pure out
  | d :: ds => do
    let d' ← sideRecord d
    sideRecordsGo (out ++ [d']) ds

/-- con-leche: ConLeche/Cached/Justify.lean:69-77 justifiable — **the statement a record offers to
a solution**: an axiom's, other than a built-in one's, and not at a certified `Nat` operation's or
a compiler-trust operation's name. -/
def justifiable (pd : IDeclaration) : AM (Option IConstantVal) := do
  match pd with
  | .axiomDecl cv =>
    if ← builtinAxiomName cv.name then pure none
    else if ← natOpName cv.name then pure none
    else if (← reduceOpNames).contains cv.name then pure none
    else pure (some cv)
  | _ => pure none

/-! ## The comparison -/

/-- con-leche: ConLeche/Cached/Justify.lean:81-83 levelsRenaming — two lists of level-parameter
names a renaming relates: as many, neither with a repeat. -/
def levelsRenaming (ps ps' : List NIdx) : Bool :=
  ps.length == ps'.length && nameNodup ps && nameNodup ps'

/-- con-leche: ConLeche/Cached/Justify.lean:85-91 sameCvUpToLevels
con-leche: ConLeche/Cached/CheckerC.lean:123-126 _root_.ConLeche.ConstantVal.atLpsC — **the
input's statement, the solution's up to the names of its level parameters**: the same, or a
renaming apart and the solution's (`cv'`) at the input's names the input's.  `IConstantVal.atLps`
is the cited `atLpsC`. -/
def sameCvUpToLevels (cv cv' : IConstantVal) : AM Bool := do
  if cv.levelParams == cv'.levelParams then pure (cv == cv')
  else if levelsRenaming cv.levelParams cv'.levelParams then
    let r ← cv'.atLps cv.levelParams
    pure (r == cv)
  else pure false

/-- con-leche: ConLeche/Cached/Justify.lean:99-103 tableBeqP — two lookups' tables. -/
def tableBeqP : Option IProjTable → Option IProjTable → Bool
  | none, none => true
  | some a, some b => a == b
  | _, _ => false

/-- con-leche: ConLeche/Kernel/Env.lean:435-438 isStmtKind — a definition, theorem or axiom: the
kinds whose copies may differ by a value. -/
def IConstantInfo.isStmtKind : IConstantInfo → Bool
  | .defnInfo .. | .thmInfo .. | .axiomInfo .. => true
  | _ => false

/-- con-leche: ConLeche/Cached/Justify.lean:105-115 copyB
con-leche: ConLeche/Cached/CheckerC.lean:128-142 _root_.ConLeche.ConstantInfo.atLpsC — **the
input's constant `ci` is a copy of the solution's `ci'`**: the same, or, for a definition, theorem
or axiom at a name no pin reserves, the solution's at the input's level-parameter names, a
renaming apart.  `IConstantInfo.atLps` is the cited `atLpsC`. -/
def copyB (ci' ci : IConstantInfo) : AM Bool := do
  let ps := ci.toConstantVal.levelParams
  if ps == ci'.toConstantVal.levelParams then pure (ci == ci')
  else if ci'.isStmtKind then
    let rs ← reservedBasisNames
    if !rs.contains ci'.toConstantVal.name &&
        levelsRenaming ci'.toConstantVal.levelParams ps then
      let r ← ci'.atLps ps
      pure (r == ci)
    else pure false
  else pure false

/-- con-leche: ConLeche/Cached/Justify.lean:117-126 refinesB — **the input's copy is the
solution's**: a copy of it, or an axiom that copies the statement of a solution definition,
theorem or axiom other than a compiler-trust operation. -/
def refinesB (ci ci' : IConstantInfo) : AM Bool := do
  if ← copyB ci' ci then pure true
  else
    match ci with
    | .axiomInfo _ =>
      if ci'.isStmtKind then
        let rs ← reduceOpNames
        if rs.contains ci'.toConstantVal.name then pure false
        else copyB (.axiomInfo ci'.toConstantVal) ci
      else pure false
    | .defnInfo .. | .thmInfo .. | .indInfo .. | .ctorInfo .. | .recInfo .. => pure false

/-! ## The solution -/

/-- con-leche: ConLeche/Cached/Justify.lean:128-133 Solution — **the solution, as the
justification reads it**: the solution stream's frozen index (every constant visible: con-leche's
`mkFEnv envS`), and the input's record mates. -/
structure ISolution where
  idx : IStreamIndex
  mates : Std.HashMap NIdx (List NIdx)

/-- con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates — one block's members, each mapped
to what it had and the block's names `ns`. -/
def matesInsert (m : Std.HashMap NIdx (List NIdx)) (ns : List NIdx) :
    List IConstantInfo → Std.HashMap NIdx (List NIdx)
  | [] => m
  | b :: bs =>
    let prev := m.getD b.name []
    matesInsert (m.insert b.name (nidxAppend prev ns 0 ns.length)) ns bs

/-- con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates — **the input's record mates**:
each name an inductive block declares, mapped to the names of every block that declares it. -/
def recordMatesGo (m : Std.HashMap NIdx (List NIdx)) :
    List IDeclaration → Std.HashMap NIdx (List NIdx)
  | [] => m
  | .indDecl block _ :: ds => recordMatesGo (matesInsert m (block.map (·.name)) block) ds
  | _ :: ds => recordMatesGo m ds

/-- con-leche: ConLeche/Cached/Justify.lean:144-146 solutionOf
con-leche: ConLeche/Driver/CheckPool.lean:57-75 Jobs.build — **the solution a fold over `ds`
reads**: the solution stream's frozen index `I` (the cited `mkFEnv e`), with the record mates of
`ds`, the challenge's records as the fold checks them. -/
def solutionOf (I : IStreamIndex) (ds : List IDeclaration) : ISolution :=
  ⟨I, recordMatesGo ∅ ds⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:278-283 FEnv.find? — **the solution's lookup**: its
index's first entry of `n`, every counter visible. -/
def ISolution.find? (J : ISolution) (n : NIdx) : Option IConstantInfo :=
  match J.idx.base.idx[n]? with
  | some (c, ci) => if c < J.idx.next then some ci else none
  | none => none

/-- con-leche: ConLeche/Kernel/FEnv.lean:413-417 FEnv.findTable? — the solution's table lookup:
`n`'s first table, visible where the constant `n` is (every record position). -/
def ISolution.findTable? (J : ISolution) (n : NIdx) : Option IProjTable :=
  if (J.find? n).isSome then
    match J.idx.base.tbls[n]? with
    | some (r, t) => if r < J.idx.firsts.size then some t else none
    | none => none
  else none

/-! ## The cone -/

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — `caps.all.map (·.str "rec")`,
interned, onto `out`. -/
def recNames (out : List NIdx) : List NIdx → AM (List NIdx)
  | [] => pure out
  | m :: ms => do
    let n ← internNNode (.str m "rec")
    recNames (out ++ [n]) ms

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — **what the justification follows
from a constant**: its laws' names, a type former's constructors and its block's recursors, its
record's mates, and the names of its projection table in the input's index `fe`. -/
def entryNeeds (mates : Std.HashMap NIdx (List NIdx)) (fe : IFEnv) (ci : IConstantInfo) :
    AM (List NIdx) := do
  let x0 ← NeedsSt.empty.const ci
  let x2 ← match ci with
    | .indInfo _ caps => do
      let x1 := x0.names caps.ctors
      let rn ← recNames [] caps.all
      pure (x1.names rn)
    | _ => pure x0
  let x3 := match mates[ci.name]? with
    | some ms => x2.names ms
    | none => x2
  match fe.findTable? ci.name with
  | some t => do
    let x4 ← x3.table t
    pure x4.acc
  | none => pure x3.acc

/-- con-leche: ConLeche/Cached/Justify.lean:163-183 coneGo — **one name of the cone, compared**:
`some` of what it reads when the input's constant is the solution's (`refinesB`) with the same
table, `none` when it is not (or either index lacks it). -/
def coneEntry (J : ISolution) (fe : IFEnv) (n : NIdx) : AM (Option (List NIdx)) := do
  match fe.find? n with
  | none => pure none
  | some ci =>
    match J.find? n with
    | none => pure none
    | some ci' =>
      if ← refinesB ci ci' then
        if tableBeqP (fe.findTable? n) (J.findTable? n) then
          let ns ← entryNeeds J.mates fe ci
          pure (some ns)
        else pure none
      else pure none

/-- con-leche: ConLeche/Cached/Justify.lean:163-183 coneGo — **the cone walk**: every name of
`work`, and everything it reads, is the same constant in the input's index `fe` and the
solution's; the first name that is not, or `none`.  Each name is compared once (`seen`); `fuel`
bounds the names compared.  The answer carries the fuel and `seen` on.  The cited work list,
`entryNeeds ci ++ work` after a name accepted. -/
def coneGo (J : ISolution) (fe : IFEnv) :
    Nat → Std.HashMap NIdx Bool → List NIdx → AM (Option NIdx × Nat × Std.HashMap NIdx Bool)
  | fuel, seen, [] => pure (none, fuel, seen)
  | fuel, seen, n :: work => do
    if seen.contains n then coneGo J fe fuel seen work
    else match fuel with
      | 0 => pure (some n, 0, seen)
      | fuel + 1 => do
        match ← coneEntry J fe n with
        | none => pure (some n, fuel + 1, seen)
        | some ns => coneGo J fe fuel (seen.insert n true) (ns ++ work)
termination_by fuel _ work => (fuel, work.length)

/-- con-leche: ConLeche/Cached/Justify.lean:185-196 justifyWhy — **is the statement `cv`
justified by the solution `J`**, at the input's index `fe`: `none`, or why not.  The cone's
fuel is the solution's constant count and one, the cited name count and one bounded by it: the
walk compares each name once, every one a solution constant, so neither bound is reached. -/
def justifyWhy (J : ISolution) (fe : IFEnv) (cv : IConstantVal) : AM (Option String) := do
  match J.find? cv.name with
  | none => pure (some s!"the solution has no constant {← readNameM cv.name}")
  | some cS =>
    if !(← sameCvUpToLevels cv cS.toConstantVal) then
      pure (some s!"the solution's {← readNameM cv.name} has another type")
    else
      let (_, ns) ← needsGo ∅ [] coreWalkFuel cv.type
      let (r, _, _) ← coneGo J fe (J.idx.next + 1) ∅ ns
      match r with
      | none => pure none
      | some n =>
        pure (some s!"its type reads {← readNameM n}, which the solution does not declare alike")

/-! ## The check of one record, with a solution -/

/-- con-leche: ConLeche/Cached/ParsedC.lean:334-343 declCLabel — a record's kind and name, for a
message. -/
def declLabel (d : IDeclaration) : AM String := do
  match d with
  | .defnDecl cv _ _ => pure s!"def {← readNameM cv.name}"
  | .thmDecl cv _ => pure s!"theorem {← readNameM cv.name}"
  | .opaqueDecl cv _ => pure s!"opaque {← readNameM cv.name}"
  | .axiomDecl cv => pure s!"axiom {← readNameM cv.name}"
  | .quotDecl _ cv => pure s!"quot {← readNameM cv.name}"
  | .indDecl block _ =>
    if h : block.length > 0 then pure s!"inductive {← readNameM (block[0]'h).name}"
    else pure s!"inductive {ConLeche.Name.anonymous}"

/-- con-leche: ConLeche/Cached/Justify.lean:200-216 checkRecordC — **the justification route**:
the statement `cv` justified by the solution (`justifyWhy`), its type checked (`checkConstantVal`,
no reserved name allowed), the reserved names' check, and its axiom pushed.  The cited `flushC`
is the job's bracket's (`recordJob`'s fresh caches). -/
def checkJustified (mode : CheckMode) (J : ISolution) (fe : IFEnv) (pd : IDeclaration)
    (cv : IConstantVal) : AM IFEnv := do
  match ← justifyWhy J fe cv with
  | some why => fail (.invalid s!"{← declLabel pd} is not justified by the solution: {why}")
  | none =>
    checkConstantVal mode fe cv false false false
    if ← basisNamesOk pd then pure (fe.push (.axiomInfo cv))
    else fail (← basisNamesError pd)

/-- con-leche: ConLeche/Cached/Justify.lean:200-216 checkRecordC — **the check of one record**,
with a solution or none.  A record that offers a statement (`justifiable`) takes the
justification route where there is a solution; every other record, and every record without
one, its own check (`checkDecl`, the cited `checkDeclStepC` past the bracket's flush). -/
def checkRecord (mode : CheckMode) (pins : List INatOpPinSet) (J : Option ISolution) (fe : IFEnv)
    (pd : IDeclaration) : AM IFEnv := do
  match J with
  | none => checkDecl mode pins fe pd
  | some j =>
    match ← justifiable pd with
    | none => checkDecl mode pins fe pd
    | some cv => checkJustified mode j fe pd cv

/-! ## A record's job -/

/-- con-leche: ConLeche/Cached/StreamIndex.lean:95-103 recordJob — what the fold's step asks of
record `pd` at position `k`, with the solution `J` if any: the `And` pin, then the record's check
at its view (`checkRecord`, the cited `checkRecordC`).  `recordJob` is this in its bracket. -/
def recordCheck (mode : CheckMode) (pins : List INatOpPinSet) (J : Option ISolution)
    (I : IStreamIndex) (k : Nat) (pd : IDeclaration) : AM Unit := do
  if ← andPinOk pd then
    let _ ← checkRecord mode pins J (I.view k) pd
    pure ()
  else fail (.invalid "`And` must be the standard `And`")

/-- con-leche: ConLeche/Cached/StreamIndex.lean:95-103 recordJob — **record `pd`'s job, at
position `k`**, with the solution `J` if any: `recordCheck` from fresh memos and an empty scratch
tier (the cited `checkDeclStepC`'s fresh `{}`), the tier dropped after it.  Nothing the job
builds outlives it. -/
def recordJob (mode : CheckMode) (pins : List INatOpPinSet) (J : Option ISolution)
    (I : IStreamIndex) (k : Nat) (pd : IDeclaration) : AM Unit := do
  enterScratch
  recordCheck mode pins J I k pd
  dropScratch

end ConRon.Arena
