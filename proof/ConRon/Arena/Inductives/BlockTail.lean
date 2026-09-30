/-
# `ConRon.Arena.Inductives.BlockTail` — the uniform install's pass and tail
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/BlockTail.lean` over handles — `checkBlock`, the
uniform route's entry — at the executed tier's discipline:
`ConLeche/Cached/CheckerC.lean`'s `checkBlockKS`/`checkBlockPassS`/
`checkBlockTailS`, whose flushes at the environment transitions are the
arena's (task #97g item 4; the arena has one core, the cached one).  The Rust
twin is `arena::inductives::block_tail`.

**The deviations of this module** (the Rust's, item for item):

* **`BlockPass` is not generic** in the environment representation:
  con-leche parameterises it because it has two (`Env` and `FEnv`); the arena
  has one.
* **The index is threaded by value**, and the recursor stage hands it back
  (`Arena/Inductives/GenRec.lean`'s module note); the recursors' cons reads
  the constructors' environment at its visibility bound while it pushes above
  it (`consBlockRecsTF`'s fixed `find?`/`resolves`).
* **`checkBlockTablesF`'s walkers are the arena's**
  (`Arena/Inductives/StructInstall.lean`'s `checkStructProjTable`, the one
  table install).
* **`checkBlockPass` is two functions in the Rust** (`check_block_pass` and
  `check_block_pass_classes`, the latter "part of" the former); here it is
  one, with the same binds in the same order.
-/
import ConRon.Arena.Inductives.GenRec

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:25-52 BlockPass
**What one pass over the formers, the constructors and the classes yields**:
the environment holding all k formers, the annotated formers, the completed
record, the annotated constructors and their fields' sorts per member, the
positivity function's kinds and normal forms, the canonical parameters, the
pre-pass's reading, the classes, and the positivity check's table. -/
structure BlockPass where
  env1 : IFEnv
  cvTas : List IConstantVal
  p : BlockParts
  ctorsAs : List (List (IConstantVal × Nat))
  sortsss : List (List (List LIdx))
  kinds : List (List (List NestFieldKind))
  nfs : List (List EIdx)
  params : List EIdx
  rd : ClassRead
  cls : List TargetMajor
  tbl : List NestCtorNf

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:54-74 checkBlockPass
con-leche: ConLeche/Cached/CheckerC.lean:136-154 checkBlockPassS
**One pass over the formers, the constructors and the classes** at the
block's `is_rec` verdict: the formers (and the flush entering the environment
that holds them all), the constructors, the walk's context, the classes, and
the positivity check as ONE walk — the members' root frame, then every
outside class. -/
def checkBlockPass (mode : CheckMode) (fe : IFEnv) (p₀ : BlockParts) (isRec : Bool) :
    AM BlockPass := do
  let (fe₁, cvTas, p₁) ← checkBlockInds mode fe p₀ isRec
  let pc := p₀.complete p₁
  flushCaches
  let (ctorsAs, sortsss) ← checkBlockCtors mode fe₁ fe₁ pc.shape pc.shape.members cvTas
  -- the Rust's `check_block_pass_classes`
  let (ctx, holes) ← blockNestCtx fe₁ pc.shape cvTas
  let (rd, ms) ← checkBlockClasses mode fe₁ pc.shape ctx.params ctorsAs
  let (kinds, nfs, pos) ← checkBlockPositivity mode fe₁ pc cvTas ctorsAs
  let seeds ← classSeeds ctx holes ms
  let ns ← nestSeeds mode fe₁ ctx seeds pos
  pure { env1 := fe₁, cvTas := cvTas, p := pc, ctorsAs := ctorsAs,
         sortsss := sortsss, kinds := kinds, nfs := nfs, params := ctx.params,
         rd := rd, cls := ms, tbl := ns.ctorNfs }

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:76-91 checkBlockRec
**The recursor stage on the uniform route**: the GENERATED recursor stage at
the constructors' environment, on the stream's own recursor family (the raw
`block`), the pass's classes and table, and the container bit. -/
def checkBlockRec (mode : CheckMode) (fe : IFEnv) (p : BlockParts) (nested : Bool)
    (params : List EIdx) (tbl : List NestCtorNf) (rd : ClassRead)
    (ms : List TargetMajor) (block : List IConstantInfo) (cvTas : List IConstantVal) :
    AM (IFEnv × List (IConstantVal × TargetMajor × List EIdx)) :=
  genRecCheck mode fe p.shape nested params tbl rd ms cvTas block

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:108-123 checkBlockTables
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:191-204 checkBlockTablesF
**The projection table at every STRUCTURE-LIKE member** (one constructor, no
index): the member's table at the tagged tower's projection offset `1`;
nothing at any other member.  The three lists are walked side by side, as the
Rust's index `i` walks them. -/
def checkBlockTables (p : BlockShape) :
    List MemberShape → List (List (IConstantVal × Nat)) → List (List (List LIdx)) →
      IFEnv → AM IFEnv
  | m :: ms, cs :: css, ss :: sss, fe => do
    match cs, ss with
    | [(cA, nF)], [sorts] =>
      if m.nIdx == 0 then do
        let guards ← structProjGuards cA.type p.nP nF sorts
        let fe₂ ← checkStructProjTable m.cvT.name cA.name p.lps p.nP nF p.resSort
          guards 1 cA fe
        checkBlockTables p ms css sss fe₂
      else checkBlockTables p ms css sss fe
    | _, _ => checkBlockTables p ms css sss fe
  | _, _, _, fe => pure fe

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:125-138 checkBlockTail
con-leche: ConLeche/Cached/CheckerC.lean:156-169 checkBlockTailS
**The install after the pass**: the index binders' sorts, the constructors
consed (and the flush entering that environment), the recursor stage, the
recursors consed at their majors, and the projection tables. -/
def checkBlockTail (mode : CheckMode) (block : List IConstantInfo) (q : BlockPass) :
    AM IFEnv := do
  let _isorts ← checkBlockIdxSorts mode q.env1 q.p.shape q.p.shape.members q.cvTas
  let fe₂ := consBlockCtors q.p.shape.nP q.ctorsAs q.env1
  flushCaches
  let vis₂ := fe₂.visibleBelow
  let nested := blockNestedBit q.p.shape q.kinds
  let (fe₂b, out) ← checkBlockRec mode fe₂ q.p nested q.params q.tbl q.rd q.cls
    block q.cvTas
  let fe₃ ← consBlockRecsTF vis₂ q.p.shape 0 out fe₂b
  checkBlockTables q.p.shape q.p.shape.members q.ctorsAs q.sortsss fe₃

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:140-148 checkBlock
con-leche: ConLeche/Cached/CheckerC.lean:171-179 checkBlockKS
**Check and install a block on the uniform route**: the distinct names, the
flush, the pass at official's `is_rec`, and the install after it. -/
def checkBlock (mode : CheckMode) (fe : IFEnv) (block : List IConstantInfo)
    (p₀ : BlockParts) : AM IFEnv := do
  let ctorNames := p₀.shape.allCtors.map (·.1.name)
  if !nameNodup ctorNames || !nameNodup p₀.shape.memberNames then
    fail (.invalid "direct rec: duplicate constructor")
  else do
    flushCaches
    let raw ← blockRawRec p₀
    let q ← checkBlockPass mode fe p₀ raw
    checkBlockTail mode block q

end ConRon.Arena
