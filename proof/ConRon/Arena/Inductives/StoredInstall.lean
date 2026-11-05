/-
# `ConRon.Arena.Inductives.StoredInstall` — the stored install of an inductive block

`ConLeche/Cached/StoredInstall.lean` over handles.  Phase A pushes an inductive
block **as the input stores it**: every constant and table is read off the
block's records, and nothing is generated.  The block's checked install runs
later, as a job of the check phase (`blockCheck`, `Arena/Checker.lean`), and
compares what it pushes with what this install pushed.  The Rust twin is
`arena::inductives::stored_install`.

**The deviations of this module** (the Rust's, item for item):

* **The reading's two inferences each have a scratch bracket of their own**
  (`storedTry`): a failed inference is a VALUE here, `none` or no guards, and the
  run goes on from the state the bracket opened at, its scratch tier dropped.
  What an accepted inference leaves is promoted before the drop.  The rest of the
  reading runs in one bracket at its end (`storedTail`), which promotes the
  block's new constants and tables as `installStep`'s does.
* **Upstream's `==` on terms is handle equality.**
* **The store's own failures stay failures**: upstream's reading has none.
* **A name already taken fails here** (`namesFree`), before anything is pushed:
  con-leche's commit loop, at the slot that does not match (`phaseAFailure` runs
  the block's job for the verdict).
* **`storedRecs` and `storedTables` push as they read**, at the constructors'
  bound for the rules' lookups, where upstream builds lists its caller pushes;
  the guards are read before the bracket the bodies are built in
  (`storedGuardsAll`), whether or not the bodies turn out to exist.
-/
module

public import ConRon.Arena.Inductives.BlockTail
public import ConRon.Arena.Promote
public import ConRon.Arena.Basis

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## Pointer-first equality of what an install pushes -/

/-- con-leche: ConLeche/Cached/StoredInstall.lean:62-65 listBeqBy
Element-wise comparison of two lists by `f`. -/
def listBeqBy {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listBeqBy f as bs
  | _, _ => false

/-- con-leche: ConLeche/Cached/StoredInstall.lean:76-77 ConstantVal.beqP
`IConstantVal` equality, the type by handle. -/
def IConstantVal.beqP (a b : IConstantVal) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type

/-- con-leche: ConLeche/Cached/StoredInstall.lean:87-90 RecRuleFire.beqP
`IRecRuleFire` equality, the pins by handle. -/
def IRecRuleFire.beqP : IRecRuleFire → IRecRuleFire → Bool
  | .plain, .plain => true
  | .nested l p, .nested l' p' => l == l' && p == p'
  | _, _ => false

/-- con-leche: ConLeche/Cached/StoredInstall.lean:96-98 RecRule.beqP
`IRecRule` equality, the right-hand side by handle. -/
def IRecRule.beqP (a b : IRecRule) : Bool :=
  a.ctor == b.ctor && a.nfields == b.nfields && a.ctorParams == b.ctorParams &&
    a.fire.beqP b.fire && a.rhs == b.rhs && a.k == b.k && a.eta == b.eta

/-- con-leche: ConLeche/Cached/StoredInstall.lean:109-117 ConstantInfo.beqP
**`IConstantInfo` equality, pointer-first**: every term by handle, the rest by
its decidable equality. -/
def IConstantInfo.beqP : IConstantInfo → IConstantInfo → Bool
  | .axiomInfo v, .axiomInfo v' => v.beqP v'
  | .defnInfo v e h, .defnInfo v' e' h' => v.beqP v' && e == e' && decide (h = h')
  | .thmInfo v, .thmInfo v' => v.beqP v'
  | .indInfo v c, .indInfo v' c' => v.beqP v' && decide (c = c')
  | .ctorInfo v a b, .ctorInfo v' a' b' => v.beqP v' && a == a' && b == b'
  | .recInfo v a b rs, .recInfo v' a' b' rs' =>
    v.beqP v' && a == a' && b == b' && listBeqBy IRecRule.beqP rs rs'
  | _, _ => false

/-- con-leche: ConLeche/Cached/StoredInstall.lean:132-135 ProjTable.beqP
**`IProjTable` equality, pointer-first**: every term and level by handle. -/
def IProjTable.beqP (a b : IProjTable) : Bool :=
  a.structName == b.structName && a.levelParams == b.levelParams &&
    a.numParams == b.numParams && a.ctor == b.ctor && a.numFields == b.numFields &&
    a.structSort == b.structSort && a.bodies == b.bodies && a.guards == b.guards

/-! ## The reading -/

/-- con-leche: ConLeche/Cached/StoredInstall.lean:161-170 storedTele
con-leche: ConLeche/Cached/StoredInstall.lean:214-223 storedGuards
**A stored inference, in a scratch bracket of its own**, from fresh caches:
`run`, framed (`scratchRun`), and what it answers promoted by `keep` before the drop.  A failure of `run`
is `none`, at the state the bracket opened at with its scratch tier dropped (the
Rust's `stored_abandon` makes the same state out of the one the failure left). -/
def storedTry {α β : Type} (run : AM α) (keep : α → AM β) : AM (Option β) := do
  flushCaches
  enterScratch
  let attempt : AM (Option β) := fun s =>
    match scratchRun run s with
    | .ok (a, s₁) => (do
        let b ← keep a
        dropScratch
        pure (some b) : AM (Option β)) s₁
    | .error _ => (do
        dropScratch
        pure none : AM (Option β)) s
  attempt

/-- con-leche: ConLeche/Cached/StoredInstall.lean:161-170 storedTele
The cited `run`: the telescope official's `whnf` loop reads, closed over its sort. -/
def storedTeleRun (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) (n : Nat) :
    AM (EIdx × LIdx) := do
  let (bs, s) ← whnfTelescope mode fe 0 n cv.type
  let sortS ← internE (.sort s)
  let ty ← closeTelescope bs 0 sortS
  pure (ty, s)

/-- con-leche: ConLeche/Cached/StoredInstall.lean:161-170 storedTele
**A former's telescope, as the checked install computes it** (`checkSumTele`,
without its checks): the stored type where it is a syntactic telescope of `n`
binders ending in a sort; else the telescope official's `whnf` loop reads, closed,
from fresh caches.  `none` where the loop does not reach a sort. -/
def storedTele (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) (n : Nat) :
    AM (Option (IConstantVal × LIdx)) := do
  let slow : AM (Option (IConstantVal × LIdx)) :=
    storedTry (storedTeleRun mode fe cv n) fun q => do
      let (m, ty) ← promoteE PMemo.empty coreWalkFuel q.1
      let (_, s) ← promoteL m coreWalkFuel q.2
      pure ({ cv with type := ty }, s)
  match ← stripPis n cv.type with
  | some (_, body) =>
    if body.tag == ETag.sort then
      match ← viewSort body with
      | none => failDanglingE
      | some s => pure (some (cv, s))
    else slow
  | none => slow

/-- con-leche: ConLeche/Cached/StoredInstall.lean:175-180 storedFormers
The members' formers at their telescopes, each at its record as declared where its
telescope cannot be read, and member 0's result sort (`s0`, the recogniser's
placeholder where it cannot be read); `i` is the member's position. -/
def storedFormers (mode : CheckMode) (fe : IFEnv) (nP : Nat) :
    List MemberShape → Nat → List IConstantVal → LIdx → AM (List IConstantVal × LIdx)
  | [], _, out, s0 => pure (out.reverse, s0)
  | ms :: rest, i, out, s0 => do
    match ← storedTele mode fe ms.cvT (nP + ms.nIdx) with
    | some (cv, s) =>
      storedFormers mode fe nP rest (i + 1) (cv :: out) (if i == 0 then s else s0)
    | none => storedFormers mode fe nP rest (i + 1) (ms.cvT :: out) s0

/-- con-leche: ConLeche/Cached/StoredInstall.lean:186-197 storedMajor
The outside container named by a major's domain, at the domain's levels and
parameters. -/
def storedMajorDom (fe : IFEnv) (dom : EIdx) : AM (Option TargetMajor) := do
  let hd ← getAppFn coreWalkFuel dom
  if hd.tag == ETag.const then
    match ← viewConst hd with
    | none => failDanglingE
    | some (I, us) =>
      match ← targetCtorsOf fe I with
      | none => pure none
      | some (nPc, ctors) => do
        let args ← getAppArgs coreWalkFuel dom
        pure (some { ind := I, lvls := us, ds := args.take nPc, nPc := nPc, nIdx := 0,
                     ctors := ctors, member := none })
  else pure none

/-- con-leche: ConLeche/Cached/StoredInstall.lean:186-197 storedMajor
**A recursor record's major**, as `tgtStoredRules` reads it: a member (its parameter
count and constructors), or an outside container at the levels and parameters of
the stored major domain opened at the recursor's prefix. -/
def storedMajor (fe : IFEnv) (p : BlockShape) (rc : RecShape) : AM (Option TargetMajor) := do
  match p.members[rc.tgt]? with
  | some ms => do
    let ls ← pinEmptyLevels
    pure (some { ind := ms.cvT.name, lvls := ls, ds := [], nPc := p.nP, nIdx := ms.nIdx,
                 ctors := ms.ctors, member := some rc.tgt })
  | none =>
    match ← openPisAtFvars rc.mI rc.cvR.type 0 with
    | none => pure none
    | some (_, body) =>
      if body.tag == ETag.forallE then
        match ← viewBind body with
        | none => failDanglingE
        | some (dom, _) => storedMajorDom fe dom
      else pure none

/-- con-leche: ConLeche/Cached/StoredInstall.lean:202-208 storedRecs
**The recursors' records**, in the block's order, pushed; the rules' lookups at the
constructors' bound `vis₂` while they are pushed above it.  A recursor whose major
cannot be read keeps its rules as declared. -/
def storedRecs (vis₂ : Nat) (p : BlockShape) : Nat → List RecShape → IFEnv → AM IFEnv
  | _, [], fe => pure fe
  | r, rc :: rest, fe => do
    match ← storedMajor (fe.restrictTo vis₂) p rc with
    | none =>
      storedRecs vis₂ p (r + 1) rest
        (fe.push (.recInfo rc.cvR (p.majorIdxAt r) (p.rulePrefixAt r) rc.rules))
    | some M => do
      let rules ← tgtStoredRules (fe.restrictTo vis₂) rc.cvR (p.rulePrefixAt r) M
        (rc.rules.map (·.rhs))
      storedRecs vis₂ p (r + 1) rest
        (fe.push (.recInfo rc.cvR (p.majorIdxAt r) (p.rulePrefixAt r) rules))

/-- con-leche: ConLeche/Cached/StoredInstall.lean:214-223 storedGuards
The cited `run` and the guards off its sorts. -/
def storedGuardsRun (mode : CheckMode) (fe₁ : IFEnv) (p : BlockShape)
    (c : IConstantVal × Nat) : AM (List LIdx) := do
  let cq ← unwrapOr (← openPisAtFvarsF p.nP c.1.type 0) (.internal "stored guards")
  let xq ← unwrapOr (← openPisAtFvarsF c.2 cq.2 p.nP) (.internal "stored guards")
  let args ← getAppArgs coreWalkFuel xq.2
  let sorts ← checkStructFieldSortsI mode fe₁ p.isProp p.large p.resSort p.nP xq.1
    (args.drop p.nP) c.2
  structProjGuards c.1.type p.nP c.2 sorts

/-- con-leche: ConLeche/Cached/StoredInstall.lean:214-223 storedGuards
**A structure's guard levels**: the fields' sorts at the formers' environment `fe₁`,
from fresh caches, by the constructor stage's own walk; `[]` where the walk fails
(the block's checked install then fails at the same walk, and the job reports it). -/
def storedGuards (mode : CheckMode) (fe₁ : IFEnv) (p : BlockShape)
    (c : IConstantVal × Nat) : AM (List LIdx) := do
  let g ← storedTry (storedGuardsRun mode fe₁ p c) fun gs => do
    let (_, gs') ← promoteLList PMemo.empty coreWalkFuel gs
    pure gs'
  pure (g.getD [])

/-- con-leche: ConLeche/Cached/StoredInstall.lean:228-241 storedTables
The guards of every structure-like member (one constructor, no index), one list
per member. -/
def storedGuardsAll (mode : CheckMode) (fe₁ : IFEnv) (p : BlockShape) :
    List MemberShape → AM (List (List LIdx))
  | [] => pure []
  | ms :: rest => do
    match ms.ctors with
    | [c] =>
      if ms.nIdx == 0 then do
        let gs ← storedGuards mode fe₁ p c
        let r ← storedGuardsAll mode fe₁ p rest
        pure (gs :: r)
      else do
        let r ← storedGuardsAll mode fe₁ p rest
        pure ([] :: r)
    | _ => do
      let r ← storedGuardsAll mode fe₁ p rest
      pure ([] :: r)

/-- con-leche: ConLeche/Cached/StoredInstall.lean:228-241 storedTables
**The projection tables**, member by member in block order, pushed, at every
structure-like member; none where the bodies cannot be built. -/
def storedTables (p : BlockShape) :
    List MemberShape → List (List LIdx) → IFEnv → AM IFEnv
  | [], _, fe => pure fe
  | ms :: rest, gs, fe => do
    match ms.ctors with
    | [c] =>
      if ms.nIdx == 0 then
        match ← structProjBodies ms.cvT.name p.nP c.2 c.1.type with
        | some bodies =>
          storedTables p rest gs.tail
            (fe.pushTable ⟨ms.cvT.name, p.lps, p.nP, c.1.name, c.2, p.resSort, bodies,
              gs.headD []⟩)
        | none => storedTables p rest gs.tail fe
      else storedTables p rest gs.tail fe
    | _ => storedTables p rest gs.tail fe

/-- con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
The cited `FEnv.pushAll ctors`, member by member: every constructor as declared. -/
def storedCtors (nP : Nat) : List MemberShape → IFEnv → IFEnv
  | [], fe => fe
  | ms :: rest, fe => storedCtors nP rest (consSumCtors nP ms.ctors fe)

/-- con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
The reading's last bracket: the constructors, the recursors and the tables pushed
above the formers, and everything new since the counter `vis` and the table count
`nt` promoted. -/
def storedTail (p : BlockShape) (guards : List (List LIdx)) (vis nt : Nat) (fe₁ : IFEnv) :
    AM IFEnv := do
  flushCaches
  enterScratch
  let fe₄ ← scratchRun do
    let fe₂ := storedCtors p.nP p.members fe₁
    let vis₂ := fe₂.visibleBelow
    let fe₃ ← storedRecs vis₂ p 0 p.recs fe₂
    storedTables p p.members guards fe₃
  let k := fe₄.visibleBelow - vis
  let kt := fe₄.env.tables.length - nt
  let (_, fe₅) ← promoteNew PMemo.empty coreWalkFuel k kt fe₄
  dropScratch
  pure fe₅

/-- con-leche: ConLeche/Driver/ParInstall.lean:690-808 commitLoop
**The names a block pushes are free**: the cited `slotsOk`, read before anything
is pushed. -/
def namesFree (fe : IFEnv) (ns : List NIdx) : Bool :=
  ns.all fun n => (fe.find? n).isNone

/-- con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
**A block the recogniser reads**: its names distinct and free; the formers read and
pushed with their capability records; the guards at the formers' environment; and
the last bracket.  The test of the scratch flag never fails: what it buys is that what
the recogniser answered is persistent, so it survives the reading's brackets. -/
def storedParts (mode : CheckMode) (fe : IFEnv) (p₀ : BlockParts) : AM IFEnv := do
  if (← get).store.scratchOn then fail (.internal "install: the scratch tier is open")
  let names := p₀.shape.memberNames ++ p₀.shape.allCtors.map (·.1.name) ++
    p₀.shape.recs.map (·.cvR.name)
  if !nameNodup names || !namesFree fe names then
    fail (.internal "install: a predicted slot did not match")
  else do
    let (cvTs, s0) ← storedFormers mode fe p₀.shape.nP p₀.shape.members 0 [] p₀.shape.resSort
    let p ← p₀.shape.withSort s0
    let isRec ← blockRawRec p₀
    let vis := fe.visibleBelow
    let nt := fe.env.tables.length
    let fe₁ ← consBlockInds p isRec cvTs 0 fe
    let guards ← storedGuardsAll mode fe₁ p p.members
    storedTail p guards vis nt fe₁

/-- con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
**The stored install of a block** on `fe`.  A block matching a basis pin pushes the
pin's constants, a block the recogniser does not read pushes nothing, and every
other block its reading, each part at its record as declared where the reading
fails. -/
def storedInstall (mode : CheckMode) (fe : IFEnv) (block : List IConstantInfo) (nP : Nat) :
    AM IFEnv := do
  match ← basisPinHit block with
  | some kind => do
    let decls ← BasisKind.declsA kind
    if (← get).store.scratchOn then fail (.internal "install: the scratch tier is open")
    if !namesFree fe (decls.map (·.name)) then
      fail (.internal "install: a predicted slot did not match")
    else
      pure (decls.foldl IFEnv.push fe)
  | none =>
    match ← blockParts? nP block with
    | none => pure fe
    | some p₀ => storedParts mode fe p₀

end ConRon.Arena
