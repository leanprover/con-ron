/-
# `ConRon.Arena.Inductives.BlockTail` — the inductive block's check
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/BlockTail.lean` over handles — `checkBlock`, the
block's check and install — at the executed tier's discipline:
`ConLeche/Cached/CheckerC.lean`'s `checkBlockKS`/`checkBlockPassS`/
`checkBlockTailS`/`reduceMemberS`, whose flushes at the environment transitions are the
arena's (task #97g item 4; the arena has one core, the cached one).  The Rust
twin is `arena::inductives::block_tail`.

**The deviations of this module** (the Rust's, item for item):

* **`BlockPass` is not generic** in the environment representation:
  con-leche parameterises it because it has two (`Env` and `FEnv`); the arena
  has one.
* **The index is threaded by value**, and the recursor stage hands it back
  (`Arena/Inductives/GenRec.lean`'s module note).
* **`checkBlockTablesF`'s walkers are the arena's**
  (`Arena/Inductives/StructInstall.lean`'s `checkStructProjTable`).
* **The generated install is pushed in place and popped** (`consBlockRecsTemp`,
  `IFEnv.popTemp`), where con-leche's cached driver reads an overlay on the
  constructors' index (`FEnv.overlay`): the same read-only environment, a flush
  entering and leaving it, and no copy of the index.
* **`checkBlockPass` is two functions in the Rust** (`check_block_pass` and
  `check_block_pass_classes`), and so are `checkBlock` (`check_block`,
  `check_block_reduced`) and `reduceMember` (`reduce_member`,
  `reduce_member_checked`); here each is one, with the same binds in the same
  order.  The Rust's `check_block_tail_stream` is the second half of
  `checkBlockTail`.
* **The block's install is pushed onto the constructors' environment the
  checks built**, not onto a kept copy of the environment the block was
  checked at: `checkBlockTail` hands that environment back, and it holds
  exactly `blockFormers p₀` and `blockCtors p₀` above the original (the formers
  are consed as declared, and `blockCapsAt` reads neither the sort the pass
  completes nor the members' reduced telescopes).  So the push of the
  recursors and the tables there is con-leche's
  `pushDelta (blockConstants p₀) (blockTables p₀ p₀.members)` on the original,
  with no copy of the index.
-/
module

public import ConRon.Arena.Inductives.GenRec
public import ConRon.Arena.Inductives.StreamRecs
public import ConRon.Arena.Install

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:24-42 BlockPass
**What one pass over the formers, the constructors and the classes yields**:
the environment holding all k formers, the completed record (the sort read),
the positivity function's field kinds, the canonical parameters, the pre-pass's
reading, the classes, and the positivity check's table. -/
structure BlockPass where
  env1 : IFEnv
  p : BlockShape
  kinds : List (List (List NestFieldKind))
  params : List EIdx
  rd : ClassRead
  cls : List TargetMajor
  tbl : List NestCtorNf

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:44-62 checkBlockPass
con-leche: ConLeche/Cached/CheckerC.lean:127-141 checkBlockPassS
**One pass over the formers, the constructors and the classes** at the
block's `is_rec` verdict: the formers (and the flush entering the environment
that holds them all), the constructors, the walk's context, the classes, and
the positivity check as ONE walk — the members' root frame, then every
outside class. -/
def checkBlockPass (mode : CheckMode) (fe : IFEnv) (p₀ : BlockShape) (isRec : Bool) :
    AM BlockPass := do
  let (fe₁, p₁) ← checkBlockInds mode fe p₀ isRec
  flushCaches
  checkBlockCtors mode fe₁ fe₁ p₁ p₁.members
  -- the Rust's `check_block_pass_classes`
  let (ctx, holes) ← blockNestCtx p₁
  let (rd, ms) ← checkBlockClasses mode fe₁ p₁ ctx.params
  let (outs, pos) ← checkBlockPositivity mode fe₁ p₁
  let seeds ← classSeeds ctx holes ms
  let ns ← nestSeeds mode fe₁ ctx seeds pos
  pure { env1 := fe₁, p := p₁, kinds := nestOutKinds outs, params := ctx.params,
         rd := rd, cls := ms, tbl := ns.ctorNfs.toList }

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:64-78 checkBlockRec
**The installer's recursor stage**: the GENERATED recursor stage at the
constructors' environment, on the stream's own recursor family (the raw
`block`), the pass's classes and table, and the container bit. -/
def checkBlockRec (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (nested : Bool)
    (params : List EIdx) (tbl : List NestCtorNf) (rd : ClassRead)
    (ms : List TargetMajor) (block : List IConstantInfo) :
    AM (IFEnv × List (IConstantVal × TargetMajor × List EIdx)) :=
  genRecCheck mode fe p nested params tbl rd ms block

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:80-91 consBlockRecsT
con-leche: ConLeche/Cached/CheckerC.lean:143-163 checkBlockTailS
**The checked family consed, at its majors, TEMPORARILY**: the records
`blockRecInfosTF` built (each recursor with its rules at ITS major), pushed in
place.  Returns the rows the pushes displaced (`idx[n]?` before each push), in
push order, for the pop. -/
def consBlockRecsTemp :
    List IConstantInfo → IFEnv → List (NIdx × Option IConstantInfo) →
      IFEnv × List (NIdx × Option IConstantInfo)
  | [], fe, prevs => (fe, prevs)
  | ci :: rest, fe, prevs =>
    let prev := fe.idx[ci.name]?
    consBlockRecsTemp rest (fe.push ci) (prevs ++ [(ci.name, prev)])

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:93-101 checkBlockTables
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:152-160 checkBlockTablesF
**The projection table's checks at every structure-like member**, at the
environment holding the formers and the constructors. -/
def checkBlockTables (p : BlockShape) (fe : IFEnv) : List MemberShape → AM Unit
  | [] => pure ()
  | ms :: rest => do
    match ms.structCtor? with
    | some c => checkStructProjTable ms.cvT.name p.lps p.nP c.2 c.1 fe
    | none => pure ()
    checkBlockTables p fe rest

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:103-115 checkBlockTail
con-leche: ConLeche/Cached/CheckerC.lean:143-163 checkBlockTailS
**The checks after the pass**: the index binders' sorts, the constructors
consed (and the flush entering that environment), the generated recursors, the
stream's K flags and recursors against them (at the generated family pushed in
place, a flush entering and leaving it, the pushes undone in reverse order),
and the projection tables' checks.  Returns the constructors' environment (the
module note's last deviation). -/
def checkBlockTail (mode : CheckMode) (block : List IConstantInfo) (q : BlockPass) :
    AM IFEnv := do
  let p := q.p
  checkBlockIdxSorts mode q.env1 p p.members
  let fe₂ := consBlockCtors p.nP p.memberCtors q.env1
  flushCaches
  let nested := blockNestedBit p q.kinds
  let (fe₂b, out) ← checkBlockRec mode fe₂ p nested q.params q.tbl q.rd q.cls block
  -- the Rust's `check_block_tail_stream`
  streamKCheck p p.recs out
  let infos ← blockRecInfosTF p 0 out
  let (feG, prevs) := consBlockRecsTemp infos fe₂b []
  flushCaches
  streamRecsCheck mode feG p.recs out
  let fe₃ := prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feG
  flushCaches
  checkBlockTables p fe₃ p.members
  pure fe₃

/-! ## The block's check -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:119-125 declinedAtDefinition
**The families declined at a definition**: the names a literal's constructor
form applies, and `Bool`. -/
def declinedAtDefinition : AM (List NIdx) := do
  pure [← pinStringOfList, ← pinListNil, ← pinListCons, ← pinCharOfNat, ← pinBool]

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:127-139 reduceMember
con-leche: ConLeche/Cached/CheckerC.lean:165-176 reduceMemberS
**A member's former at its telescope**, official's `whnf` loop where the
declared type does not show it: the declared type checked, reduced, and the two
compared; a member already at its telescope as it is. -/
def reduceMember (mode : CheckMode) (fe : IFEnv) (ms : MemberShape) (nP : Nat) :
    AM MemberShape := do
  if ← formerDefHeaded ms.cvT then
    if (← declinedAtDefinition).contains ms.cvT.name then
      fail (.notImplemented "this family stored at a definition")
    else do
      -- the Rust's `reduce_member_checked`
      checkConstantVal mode fe ms.cvT false
      let cvR ← reducedFormer mode fe ms.cvT (nP + ms.nIdx)
      unless ← isDefEqCore mode fe checkFuel 0 ms.cvT.type cvR.type do
        fail (.invalid "direct sum: a type former's declared type and its reduct differ")
      pure { ms with cvT := cvR }
  else pure ms

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:141-148 reduceMembers
con-leche: ConLeche/Cached/CheckerC.lean:178-185 reduceMembersS
The members, each at its telescope, a flush before each (the cached twin's). -/
def reduceMembers (mode : CheckMode) (fe : IFEnv) (nP : Nat) :
    List MemberShape → AM (List MemberShape)
  | [] => pure []
  | ms :: rest => do
    flushCaches
    let ms' ← reduceMember mode fe ms nP
    let rest' ← reduceMembers mode fe nP rest
    pure (ms' :: rest')

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:150-163 checkBlock
con-leche: ConLeche/Cached/CheckerC.lean:187-198 checkBlockKS
**Check an inductive block and install it**: the distinct names, no member at
a `Bool` constructor's name, each former reduced to its telescope once
(official's `check_inductive_types`), the flush, the pass at official's
`is_rec` (`blockIsRec`, read off the block as declared), the checks after it,
and the block's install (`blockRecs`/`blockTables` on the constructors'
environment: the module note's last deviation). -/
def checkBlock (mode : CheckMode) (fe : IFEnv) (block : List IConstantInfo)
    (p₀ : BlockShape) : AM IFEnv := do
  let ctorNames := p₀.allCtors.map (·.1.name)
  if !nameNodup ctorNames || !nameNodup p₀.memberNames then
    fail (.invalid "direct rec: duplicate constructor")
  else do
    let bt ← pinBoolTrue
    let bf ← pinBoolFalse
    if p₀.memberNames.contains bt || p₀.memberNames.contains bf then
      fail (.invalid "direct rec: a family at a `Bool` constructor's name")
    else do
      -- the Rust's `check_block_reduced`
      let ms ← reduceMembers mode fe p₀.nP p₀.members
      flushCaches
      let isRec ← blockIsRec p₀
      let q ← checkBlockPass mode fe { p₀ with members := ms } isRec
      let fe₂ ← checkBlockTail mode block q
      let recs ← blockRecs p₀ p₀.recs
      let tables ← blockTables p₀ p₀.members
      pure (fe₂.pushDelta recs tables)

end ConRon.Arena
