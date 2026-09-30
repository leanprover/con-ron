/-
# `ConRon.Arena.Inductives.BlockInstall` — the uniform inductive install, at k members
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/BlockInstall.lean` over handles, with its index
twins `ConLeche/Kernel/Inductives/BlockInstallF.lean` collapsed into it: the
capability record per member, official's `is_rec`, the formers' stage
(telescopes, the two agreements, the cons), the constructors' stage, the
positivity check on the stored constructors, the index sorts and the
constructors' cons.  The Rust twin is `arena::inductives::block_install`.

**The deviations** (the Rust's, item for item):

* **The `…F` twins collapse into these** (task #97c's deviation 1): the arena
  has one environment representation, `IFEnv`, so `checkBlockTeleF`,
  `checkBlockIndsF`, … ARE these functions, cited beside their pure twins.
  `consBlockRecs`, `consBlockRecsF`, `blockRecInfosF`, `FEnv.pushAll` and
  `consBlockRecsFFast` (the member-major recursor cons and its `@[csimp]` fast
  form) are not ported: the executed stage conses through `consBlockRecsTF`
  (`Arena/Inductives/RecCheck.lean`); `consBlockRecsBare` and
  `openPisParamsIdx` are read by nothing executed.
* **`blockCapsAt`'s record is built by branches**, not `&&`/`!` (AENEAS_FINDINGS
  F18), and it is an `AM` function: the result sort is a handle, read
  (`readLevelM`) for its zero-ness.
* **`checkBlockPositivity`'s `find?` is the environment** (the positivity
  module's note), and so is `blockNestCtx`'s; the Rust's `NestCtx.vis` (and
  `BlockShape.nestCtx`'s `vis` argument) is the `fe` the readers take, and
  `BlockShape.nestCtx` interns the block's levels once.
* **A list reversal is not needed**: the formers are consed in block order
  with member 0 deepest, which over the oldest-first `IFEnv` is pushing in
  block order.
* **A zipped list is two lists**: `checkBlockCtors` and `checkBlockIdxSorts`
  walk the members and the checked formers side by side, stopping at the
  shorter, as the Rust's index recursion does, instead of con-leche's
  `List (MemberShape × ConstantVal)`.
* **`piDomsMentionAny` recurses on a handle, so it carries a fuel**
  (`coreWalkFuel`): con-leche's is structural on the term.
-/
import ConRon.Arena.Inductives.BlockRec
import ConRon.Arena.Inductives.SumInstall

namespace ConRon.Arena

open ConLeche

/-! ## The capability record, per member -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:49-81 blockCapsAt
**The capability record of member `mi`**: at a member with ONE constructor, η
(index-free, not `Prop`, the block not recursive), unit-likeness (and no
field), rule K (one member, no field, `Prop`) and the result sort's zero-ness;
at every member the block's members, its parameter count and the member's
constructors.  (`p.members.getD mi default`: the default member has no
constructor.) -/
def blockCapsAt (p : BlockShape) (mi : Nat) (isRec : Bool) : AM IIndCaps := do
  let names := p.memberNames
  match p.members[mi]? with
  | some ms =>
    match ms.ctors with
    | [c] => do
      let nIdx := ms.nIdx
      let eta : Bool :=
        if nIdx != 0 then false
        else if p.isProp then false
        else if isRec then false
        else true
      let unitlike : Bool :=
        if nIdx != 0 then false
        else if c.2 != 0 then false
        else if isRec then false
        else true
      let ruleK : Bool := p.k == 1 && c.2 == 0 && p.isProp
      let l ← readLevelM p.resSort
      pure { eta := eta
             etaCtor := c.1.name
             etaParams := p.nP
             etaFields := c.2
             unitlike := unitlike
             unitParams := p.nP
             ruleK := ruleK
             sortZ := Level.zeronessOf l
             all := names
             nparams := p.nP
             ctors := [c.1.name] }
    | cs => pure { all := names, nparams := p.nP, ctors := cs.map (·.1.name) }
  | none => pure { all := names, nparams := p.nP, ctors := [] }

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:83-88 Expr.piDomsMentionAny
Does some binder domain of the SYNTACTIC `∀`-telescope of `e` mention one of
`names`?  No reduction; the `||` short-circuits.  Fueled (the module note). -/
def piDomsMentionAny (names : List NIdx) : Nat → EIdx → AM Bool
  | 0, _ => fail (.internal "fuel exhausted: piDomsMentionAny")
  | fuel + 1, e => do
    if e.tag == ETag.forallE then
      match ← viewBind e with
      | none => failDanglingE
      | some (ty, b, _) =>
        if ← mentionsAnyConst names ty then pure true
        else piDomsMentionAny names fuel b
    else pure false

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:90-102 blockRawRec
**Official's `is_rec`**: does SOME member of the block occur in SOME binder
domain of the syntactic telescope of SOME DECLARED constructor type? -/
def blockRawRec (p : BlockParts) : AM Bool := do
  let names := p.shape.memberNames
  p.shape.members.anyM fun ms =>
    ms.ctors.anyM fun c => piDomsMentionAny names coreWalkFuel c.1.type

/-! ## Stage 1: the formers -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:106-117 checkBlockTele
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:27-36 checkBlockTeleF
One member's type former: the constant check, official's telescope loop and
the result sort, without the environment cons. -/
def checkBlockTele (mode : CheckMode) (fe : IFEnv) (nP : Nat) (ms : MemberShape) :
    AM (IConstantVal × LIdx) := do
  let cvTa₀ ← checkConstantVal mode fe ms.cvT
  let (cvTa, s) ← checkSumTele mode fe ms.cvT (nP + ms.nIdx) cvTa₀
  match ← stripPis (nP + ms.nIdx) cvTa.type with
  | none => fail (.internal "direct sum: type former telescope")
  | some q => do
    let srt ← internSortE s
    if q.2 == srt then pure (cvTa, s)
    else fail (.internal "direct sum: type former result sort")

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:119-126 checkBlockTeles
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:38-45 checkBlockTelesF
The members' type formers, in block order. -/
def checkBlockTeles (mode : CheckMode) (fe : IFEnv) (nP : Nat) :
    List MemberShape → AM (List (IConstantVal × LIdx))
  | [] => pure []
  | ms :: rest => do
    let r ← checkBlockTele mode fe nP ms
    let rs ← checkBlockTeles mode fe nP rest
    pure (r :: rs)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:128-142 checkBlockDomsAt
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:47-56 checkBlockDomsAtF
**The parameter-domain agreement's comparison**: binder `j - 1`'s domain
against member 0's, defeq at depth `off + j - 1`, from the last binder to the
first; a mismatch is official's REJECT. -/
def checkBlockDomsAt (mode : CheckMode) (fe : IFEnv) (off : Nat)
    (fvs doms : List EIdx) : Nat → AM Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "block: domain index")
    let b ← unwrapOr doms[j]? (.internal "block: domain index")
    let aT ← fvarTypeD a
    unless ← isDefEqCore mode fe checkFuel (off + j) aT b do
      fail (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAt mode fe off fvs doms j

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:144-164 checkBlockAgree
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:58-73 checkBlockAgreeF
**Official's two agreements between the members**: every member's parameter
domains are DEFINITIONALLY member 0's, and every member's result sort is
equivalent to member 0's.  Both REJECT. -/
def checkBlockAgree (mode : CheckMode) (fe : IFEnv) (nP : Nat)
    (cvTa₀ : IConstantVal) (s₀ : LIdx) : List (IConstantVal × LIdx) → AM Unit
  | [] => pure ()
  | (cvTa, s) :: rest => do
    let tq₀ ← unwrapOr (← openPisAtFvarsF nP cvTa₀.type 0)
      (.internal "block: type former telescope")
    let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
      (.invalid "parameters of all inductive datatypes must match")
    unless tq.1.length == tq₀.1.length do
      fail (.invalid "parameters of all inductive datatypes must match")
    let doms ← fvarTypeDs tq₀.1
    checkBlockDomsAt mode fe 0 tq.1 doms nP
    unless ← liftFueled "level comparison" (← lvlEq? s s₀) do
      fail (.invalid "mutually inductive types must live in the same universe")
    checkBlockAgree mode fe nP cvTa₀ s₀ rest

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:166-172 consBlockInds
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:75-80 consBlockIndsF
The members' formers consed, in block order (member 0 deepest), each with ITS
capability record at the block's `is_rec` verdict. -/
def consBlockInds (p₁ : BlockShape) (isRec : Bool) :
    List IConstantVal → Nat → IFEnv → AM IFEnv
  | [], _, fe => pure fe
  | cvTa :: rest, i, fe => do
    let caps ← blockCapsAt p₁ i isRec
    consBlockInds p₁ isRec rest (i + 1) (fe.push (.indInfo cvTa caps))

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:174-187 checkBlockInds
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:82-93 checkBlockIndsF
**Stage 1**: the k type formers, checked, agreed and consed — official's
`declare_inductive_types`, which puts every former in the environment before
any constructor is looked at. -/
def checkBlockInds (mode : CheckMode) (fe : IFEnv) (p : BlockParts) (isRec : Bool) :
    AM (IFEnv × List IConstantVal × BlockShape) :=
  match p.shape.members with
  | [] => fail (.internal "block: no type former")
  | ms₀ :: rest => do
    let nP := p.shape.nP
    let (cvTa₀, s₀) ← checkBlockTele mode fe nP ms₀
    let cvs ← checkBlockTeles mode fe nP rest
    checkBlockAgree mode fe nP cvTa₀ s₀ cvs
    let p₁ ← p.shape.withSort s₀
    let cvTas := cvTa₀ :: cvs.map (·.1)
    let fe₁ ← consBlockInds p₁ isRec cvTas 0 fe
    pure (fe₁, cvTas, p₁)

/-! ## Stage 1b: the constructors, and the positivity check -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:191-197 BlockShape.nestCtx
**The block's positivity context** at the canonical parameter variables
`fvsP`; its lookup is the environment every reader takes beside it (the
positivity module's note: the Rust's `vis` field is `fe.visibleBelow`);
`lvls` the block's own levels, interned. -/
def BlockShape.nestCtx (p : BlockShape) (fvsP : List EIdx) : AM NestCtx := do
  let lps := p.lps
  let lvls ← paramLevels lps
  pure { names := p.memberNames, lps := lps, nP := p.nP, nIdxs := p.nIdxs,
         params := fvsP, sort := p.resSort, lvls := lvls }

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:199-210 checkBlockCtors
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:97-106 checkBlockCtorsF
The constructors of every member (beside its checked former), at the
environment holding ALL the formers, each stored as declared; the constructors
and their fields' sorts, per member. -/
def checkBlockCtors (mode : CheckMode) (fe₀ fe : IFEnv) (p : BlockShape) :
    List MemberShape → List IConstantVal →
      AM (List (List (IConstantVal × Nat)) × List (List (List LIdx)))
  | ms :: rest, cvTa :: cvTas => do
    let (cs, ss) ← checkSumCtors mode fe₀ fe ms.cvT.name p.lps p.nP ms.nIdx p.resSort
      p.isProp p.large cvTa ms.ctors
    let (restC, restS) ← checkBlockCtors mode fe₀ fe p rest cvTas
    pure (cs :: restC, ss :: restS)
  | _, _ => pure ([], [])

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:228-250 checkAbsCtorSorts
**The fields' universes at the holes**: each constructor's positivity normal
form within the block's level parameters (internal), its fields opened above
the holes and their sorts bounded by the block's (the root's line of
`checkStructFieldSortsI`); pairwise, stopping at the shorter list.  `isProp` is
the block's `isEquiv sort 0 == some true`, read once by the caller. -/
def checkAbsCtorSorts (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (isProp : Bool) :
    List (IConstantVal × Nat) → List (List NestFieldKind × EIdx) → AM Unit
  | c :: cs, o :: os => do
    let tyN := o.2
    let nF := c.2
    unless ← allLevelParamsDefined ctx.lps tyN do
      fail (.internal "direct rec: a positivity normal form outside the block's level \
        parameters")
    let hi := ctx.hiAt 0
    let xq ← unwrapOr (← openPisAtFvarsF nF tyN hi)
      (.internal "direct rec: abstracted constructor fields")
    let _ ← checkStructFieldSortsI mode fe isProp false ctx.sort hi xq.1 [] nF
    checkAbsCtorSorts mode fe ctx isProp cs os
  | _, _ => pure ()

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:252-258 checkAbsCtorSortsAll
`checkAbsCtorSorts` on every member's constructors; the block's
`isEquiv sort 0 == some true` read once. -/
def checkAbsCtorSortsAll (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (isProp : Bool) :
    List (List (IConstantVal × Nat)) → List (List (List NestFieldKind × EIdx)) → AM Unit
  | cs :: css, os :: oss => do
    checkAbsCtorSorts mode fe ctx isProp cs os
    checkAbsCtorSortsAll mode fe ctx isProp css oss
  | _, _ => pure ()

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:260-274 blockNestCtx
**The walk's context** of a block: the canonical parameter variables are the
first former's opened telescope, the lookup the environment `fe`, with the
members' holes. -/
def blockNestCtx (fe : IFEnv) (p : BlockShape) (cvTas : List IConstantVal) :
    AM (NestCtx × List EIdx) := do
  match cvTas with
  | [] => fail (.internal "direct rec: no type former")
  | cvTa₀ :: _ => do
    let pq ← unwrapOr (← openPisAtFvarsF p.nP cvTa₀.type 0)
      (.internal "direct rec: type former telescope")
    let ctx ← p.nestCtx pq.1
    let holes ← unwrapOr (← nestHoles fe ctx)
      (.internal "direct rec: a member is not a stored former")
    pure (ctx, holes)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:276-294 checkBlockPositivity
**The block's positivity, on its stored constructors**, at the walk's context:
official's uniform-occurrence check, the root frame from the empty state, the
fields' universes at the holes.  Returns the walk's kinds, its normal forms and
its state. -/
def checkBlockPositivity (mode : CheckMode) (fe : IFEnv) (p : BlockParts)
    (cvTas : List IConstantVal) (ctorsAs : List (List (IConstantVal × Nat))) :
    AM (List (List (List NestFieldKind)) × List (List EIdx) × NestState) := do
  let (ctx, holes) ← blockNestCtx fe p.shape cvTas
  -- official's `check_uniform_ind_occs`, before the walk
  nestUniform ctx ctorsAs
  -- the root frame on the STORED (declared) constructors
  let (outs, ns) ← nestRoot mode fe ctx holes ctorsAs {} []
  let z ← zeroLevel
  let isProp := (← lvlEq? ctx.sort z) == some true
  checkAbsCtorSortsAll mode fe ctx isProp ctorsAs outs
  pure (outs.map (·.map (·.1)), outs.map (·.map (·.2)), ns)

/-! ## Stage 2: the tail -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:298-311 checkBlockIdxSorts
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:110-120 checkBlockIdxSortsF
Every member's INDEX binders' universes (beside its checked former), read (no
bound is checked): the member's telescope opened, each index domain's sort
inferred. -/
def checkBlockIdxSorts (mode : CheckMode) (fe : IFEnv) (p : BlockShape) :
    List MemberShape → List IConstantVal → AM (List (List LIdx))
  | ms :: rest, cvTa :: cvTas => do
    let tq ← unwrapOr (← openPisAtFvarsF (p.nP + ms.nIdx) cvTa.type 0)
      (.internal "direct rec: type former telescope")
    let isorts ← checkStructFieldSortsI mode fe true false p.resSort p.nP (tq.1.drop p.nP) []
      ms.nIdx
    let rs ← checkBlockIdxSorts mode fe p rest cvTas
    pure (isorts :: rs)
  | _, _ => pure []

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:313-317 consBlockCtors
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:122-125 consBlockCtorsF
The members' constructors consed, member by member, in block order.  Pure: the
index push touches no term. -/
def consBlockCtors (nP : Nat) : List (List (IConstantVal × Nat)) → IFEnv → IFEnv
  | [], fe => fe
  | ctorsA :: rest, fe => consBlockCtors nP rest (consSumCtors nP ctorsA fe)

end ConRon.Arena
