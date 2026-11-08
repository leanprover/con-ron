/-
# `ConRon.Arena.Install` — what a declaration adds
(DESIGN.md §8, task #143)

`ConLeche/Kernel/Install.lean` over handles: a declaration's constants and
projection tables are a direct consequence of the declaration, read off it with
no environment, no inference and no reduction.  The block's check pushes exactly
this once its checks pass (`Arena/Inductives/BlockTail.lean`'s `checkBlock`),
and the stream's index is built from it before any check runs
(`Arena/StreamIndex.lean`).  The Rust twin is `arena::install`.

A block the checks reject may still read as something here (a recursor whose
major is not a container reads as firing `.plain`, a structure whose constructor
is too short has no table): what it reads as never reaches an accepted
environment.

**The deviations** (the Rust's, item for item):

* **`Env.pushDelta` and `FEnv.pushDelta` are one function** over the one
  environment type, `IFEnv` (task #97c's deviation 1).
* **Every reader is an `AM` function**: a term is read through `view`, and the
  pins' renaming (`quotAt`) and `Expr.dropVars`'s
  instantiation intern.
-/
module

public import ConRon.Arena.Inductives.BlockInstall
public import ConRon.Arena.Basis

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:122-125 FEnv.pushAll
Push a list of records, head first. -/
def IFEnv.pushAll : List IConstantInfo → IFEnv → IFEnv
  | [], fe => fe
  | ci :: rest, fe => IFEnv.pushAll rest (fe.push ci)

/-- con-leche: ConLeche/Kernel/Install.lean:22-24 Env.pushDelta
The tables, pushed in order. -/
def IFEnv.pushTables : List IProjTable → IFEnv → IFEnv
  | [], fe => fe
  | t :: rest, fe => IFEnv.pushTables rest (fe.pushTable t)

/-- con-leche: ConLeche/Kernel/Install.lean:22-24 Env.pushDelta
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:127-132 FEnv.pushDelta
**The environment with a declaration's constants and tables pushed**, each list
oldest first: the constants, then the tables. -/
def IFEnv.pushDelta (fe : IFEnv) (L : List IConstantInfo) (Q : List IProjTable) : IFEnv :=
  IFEnv.pushTables Q (IFEnv.pushAll L fe)

/-- con-leche: ConLeche/Kernel/Install.lean:26-28 blockFormers
**The formers**, in block order, as declared, with the capabilities their
block gives them. -/
def blockFormers (p : BlockShape) (isRec : Bool) : List IConstantInfo :=
  (p.members.map (·.declared)).zipIdx.map fun (cv, i) => .indInfo cv (blockCapsAt p i isRec)

/-- con-leche: ConLeche/Kernel/Install.lean:30-32 blockCtors
**The constructors of every member**, as declared, in block order. -/
def blockCtors (p : BlockShape) : List IConstantInfo :=
  p.allCtors.map fun c => .ctorInfo c.1 p.nP c.2

/-- con-leche: ConLeche/Kernel/Install.lean:34-37 Expr.dropVars
**`n` variables below a term's own, which do not occur in it, dropped**: each
instantiated at `Sort 0`. -/
def exprDropVars : Nat → EIdx → AM EIdx
  | 0, e => pure e
  | n + 1, e => do
    let s0 ← internSortE (← zeroLevel)
    exprDropVars n (← instantiate1Fast coreWalkFuel e s0 0)

/-- con-leche: ConLeche/Kernel/Install.lean:39-54 recFire
**How a recursor's rules fire**: `.plain` at a member major; at a major
outside the block, `.nested` at the levels and parameters of the major's
container.  Those are read off the major's domain, whose arguments end in the
`mI - rP` index variables; the parameters are moved from under the index
binders to the rule prefix. -/
def recFire (p : BlockShape) (rc : RecShape) : AM IRecRuleFire := do
  if rc.tgt < p.k then pure .plain
  else
    match ← stripPis rc.mI rc.cvR.type with
    | none => pure .plain
    | some q =>
      if q.2.tag == ETag.forallE then
        match ← viewBind q.2 with
        | none => failDanglingE
        | some (dom, _) => do
          let hd ← getAppFn coreWalkFuel dom
          if hd.tag == ETag.const then
            match ← viewConst hd with
            | none => failDanglingE
            | some (_, us) => do
              let lvls ← viewLs us
              let args ← getAppArgs coreWalkFuel dom
              let nI := rc.mI - rc.rP
              let ps ← (args.take (args.length - nI)).mapM (exprDropVars nI)
              pure (.nested lvls ps)
          else pure .plain
      else pure .plain

/-- con-leche: ConLeche/Kernel/Install.lean:56-61 blockRecs
**The recursors**, in block order: each record with its rules' firing mode. -/
def blockRecs (p : BlockShape) : List RecShape → AM (List IConstantInfo)
  | [] => pure []
  | rc :: rest => do
    let f ← recFire p rc
    let r : IConstantInfo :=
      .recInfo rc.cvR rc.mI rc.rP rc.isK (rc.rules.map ({ · with fire := f }))
    pure (r :: (← blockRecs p rest))

/-- con-leche: ConLeche/Kernel/Install.lean:63-73 blockTables
**The projection tables**, in block order: one per structure-like member whose
constructor reads as one. -/
def blockTables (p : BlockShape) : List MemberShape → AM (List IProjTable)
  | [] => pure []
  | ms :: rest => do
    match ms.structCtor? with
    | some c =>
      match ← structProjBodies ms.declared.name p.nP c.2 c.1.type with
      | some bodies =>
        let t : IProjTable := ⟨ms.declared.name, p.lps, p.nP, c.1.name, c.2, bodies⟩
        pure (t :: (← blockTables p rest))
      | none => blockTables p rest
    | none => blockTables p rest

/-- con-leche: ConLeche/Kernel/Install.lean:75-78 blockConstants
**The block's constants**, in push order: the formers (at official's `is_rec`,
`blockIsRec`), the constructors, the recursors. -/
def blockConstants (p : BlockShape) : AM (List IConstantInfo) := do
  let isRec ← blockIsRec p
  pure (blockFormers p isRec ++ blockCtors p ++ (← blockRecs p p.recs))

/-- con-leche: ConLeche/Kernel/Install.lean:80-94 declConstants
The `.axiomDecl` arm: `Quot.sound` installs its pin at the record's names,
`sorryAx` nothing, any other axiom itself. -/
def declConstantsAxiom (cv : IConstantVal) : AM (List IConstantInfo) := do
  if cv.name == (← pinQuotSound) then pure [← quotAt .sound cv]
  else if cv.name == (← pinSorryAx) then pure []
  else pure [.axiomInfo cv]

/-- con-leche: ConLeche/Kernel/Install.lean:80-94 declConstants
**The constants a declaration installs**, in push order.  A block `readBlock`
cannot read installs nothing (its check rejects it), and `sorryAx` nothing
(any use of it declines). -/
def declConstants : IDeclaration → AM (List IConstantInfo)
  | .defnDecl cv value hint => pure [.defnInfo cv value hint]
  | .thmDecl cv _ => pure [.thmInfo cv]
  | .opaqueDecl cv _ => pure [.axiomInfo cv]
  | .axiomDecl cv => declConstantsAxiom cv
  | .quotDecl k cv => do pure [← quotAt k cv]
  | .indDecl block nP => do
    match ← readBlock nP block with
    | .ok p => blockConstants p
    | .error _ => pure []

/-- con-leche: ConLeche/Kernel/Install.lean:96-102 declTables
**The projection tables a declaration installs**: those of an inductive block
`readBlock` reads. -/
def declTables : IDeclaration → AM (List IProjTable)
  | .indDecl block nP => do
    match ← readBlock nP block with
    | .ok p => blockTables p p.members
    | .error _ => pure []
  | _ => pure []

end ConRon.Arena
