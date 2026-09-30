/-
# `ConRon.Arena.Inductives.BlockParts` — the k-ary block: the record and the recogniser
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/BlockParts.lean` over handles: the record a block
on the uniform route is read into (`MemberShape`, `RecShape`, `BlockShape`,
`BlockParts`), its projections, and the recogniser (`blockSplit`,
`recTargetOf`, `blockCounts?`, `blockGroups`, `blockShape?`, `blockParts?`)
with the recursor records' name and level pins the recursor stage throws on.
The Rust twin is `arena::inductives::block_parts`.

**The deviations** (the Rust's, item for item):

* **`BlockParts extends BlockShape` is a `shape` field**, as `NativeParts`
  was.
* **The level lists are compared as interned lists**: `lps.map .param` is
  `paramLevels`, and `us == lvls` is handle equality (`memberIdxAt?`).
* **A projection that reads a term takes the state** (`withSort`'s
  `Level.isEquiv`, `recTargetOf`'s telescope), so it is an `AM` function.
* **`BlockShape.offs` and `BlockShape.recTgtAt` are not ported**: nothing the
  executed checker runs reads them (the model does); the skip list says so.
* **`blockRecNameSetOk` takes the members and the recursors apart**, and
  **`blockRecNamesUnreserved` takes the recursors**, as the Rust does (the
  caller's `{ p with recs := own }` is an argument, not a record copy).
* **`blockShape?`'s pins are read in the Rust's order** — the formers'
  reserved-name and level pins in one pass, then the recursors', then the
  constructors' — which is the cited conjunction reassociated (all four are
  pure).
-/
import ConRon.Arena.Inductives.Positivity

namespace ConRon.Arena

open ConLeche

/-! ## The record -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:54-69 MemberShape
One member of a block: its type former, its own index count and its
constructors (member-local, in block order, each with its field count). -/
structure MemberShape where
  /-- the member's type former -/
  cvT : IConstantVal
  /-- the member's index count -/
  nIdx : Nat
  /-- the member's constructors in block order, each with its field count -/
  ctors : List (IConstantVal × Nat)
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:71-96 RecShape
**One recursor of a block, as the stream carries it**: its constant, the
record's own rule prefix `rP` and major index `mI`, the member its MAJOR names
(`k`: none — a nested block's auxiliary recursor), and its rules' right-hand
sides as exported. -/
structure RecShape where
  /-- the recursor's constant -/
  cvR : IConstantVal
  /-- the recursor record's own rule prefix -/
  rP : Nat
  /-- the recursor record's own major-premise index -/
  mI : Nat
  /-- the member its MAJOR names -/
  tgt : Nat
  /-- the recursor's rules' right-hand sides as exported -/
  rhss : List EIdx
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:98-121 BlockShape
The pieces of a recognised block at any number of members: the members, the
recursors, the SHARED parameter count, elimination level parameter
(`.anonymous`, interned, for a small eliminator) and result sort, and the two
flags. -/
structure BlockShape where
  /-- the members in block order -/
  members : List MemberShape
  /-- the block's recursors, in the stream's order -/
  recs : List RecShape
  /-- the shared parameter count -/
  nP : Nat
  /-- the recursors' fresh elimination level parameter (`large` only) -/
  elim : NIdx
  /-- the result sort -/
  resSort : LIdx
  /-- large eliminator -/
  large : Bool
  /-- the result sort is provably `Prop` -/
  isProp : Bool
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:123-127 numCtorsOf
The constructors of a list of members, counted. -/
def numCtorsOf : List MemberShape → Nat
  | [] => 0
  | ms :: rest => ms.ctors.length + numCtorsOf rest

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:131-132 BlockShape.k
The number of members. -/
def BlockShape.k (p : BlockShape) : Nat := p.members.length

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:133-134 BlockShape.numCtors
The number of constructors of the whole block. -/
def BlockShape.numCtors (p : BlockShape) : Nat := numCtorsOf p.members

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:137-138 BlockShape.memberNames
The members' names, in block order. -/
def BlockShape.memberNames (p : BlockShape) : List NIdx := p.members.map (·.cvT.name)

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:139-140 BlockShape.nIdxs
The members' index counts, in block order. -/
def BlockShape.nIdxs (p : BlockShape) : List Nat := p.members.map (·.nIdx)

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:141-144 BlockShape.lps
The block's level parameters (member 0's; `[]` at no member). -/
def BlockShape.lps (p : BlockShape) : List NIdx :=
  match p.members with
  | [] => []
  | m :: _ => m.cvT.levelParams

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:145-147 BlockShape.allCtors
The constructors of the whole block, in block order. -/
def BlockShape.allCtors (p : BlockShape) : List (IConstantVal × Nat) :=
  (p.members.map (·.ctors)).flatten

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:154-160 BlockShape.rulePrefixAt
Recursor `r`'s rule prefix, the RECORD's (`0`, the default record's, off the
list). -/
def BlockShape.rulePrefixAt (p : BlockShape) (r : Nat) : Nat :=
  match p.recs[r]? with
  | some rc => rc.rP
  | none => 0

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:162-165 BlockShape.majorIdxAt
Recursor `r`'s major-premise index, the RECORD's. -/
def BlockShape.majorIdxAt (p : BlockShape) (r : Nat) : Nat :=
  match p.recs[r]? with
  | some rc => rc.mI
  | none => 0

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:167-171 BlockShape.withSort
The record completed with the former stage's result sort, `isProp` recomputed
from it (`Level.isEquiv s .zero == some true`, at handles: `lvlEq?`). -/
def BlockShape.withSort (p : BlockShape) (s : LIdx) : AM BlockShape := do
  let z ← zeroLevel
  let eq ← lvlEq? s z
  let isProp : Bool := match eq with
    | some true => true
    | some false => false
    | none => false
  pure { p with resSort := s, isProp := isProp }

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:198-201 BlockParts
A recognised block: its shape (`extends BlockShape`, a field here). -/
structure BlockParts where
  /-- the block's shape -/
  shape : BlockShape
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:203-206 BlockParts.complete
**The record completed by the formers' stage**: the shape the formers' run
returned. -/
def BlockParts.complete (_p₀ : BlockParts) (p₁ : BlockShape) : BlockParts :=
  ⟨p₁⟩

/-! ## Recognition -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:231-237 blockSplitRecs
The closing recursors: `none` at anything else. -/
def blockSplitRecs : List IConstantInfo →
    Option (List (IConstantVal × Nat × Nat × List IRecRule))
  | [] => some []
  | .recInfo cvR mI rP rules :: rest =>
    match blockSplitRecs rest with
    | some rs => some ((cvR, mI, rP, rules) :: rs)
    | none => none
  | _ :: _ => none

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:239-244 blockSplitCtors
The constructors, then the recursors. -/
def blockSplitCtors : List IConstantInfo →
    Option (List (IConstantVal × Nat × Nat) ×
      List (IConstantVal × Nat × Nat × List IRecRule))
  | .ctorInfo cvC nP nF :: rest =>
    match blockSplitCtors rest with
    | some q => some ((cvC, nP, nF) :: q.1, q.2)
    | none => none
  | rest =>
    match blockSplitRecs rest with
    | some rs => some ([], rs)
    | none => none

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:246-252 blockSplit
The type formers, the constructors and the recursors. -/
def blockSplit : List IConstantInfo →
    Option (List IConstantVal × List (IConstantVal × Nat × Nat) ×
      List (IConstantVal × Nat × Nat × List IRecRule))
  | .indInfo cvT _ :: rest =>
    match blockSplit rest with
    | some q => some (cvT :: q.1, q.2)
    | none => none
  | rest =>
    match blockSplitCtors rest with
    | some q => some ([], q.1, q.2)
    | none => none

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:254-271 recTargetOf
**The member a recursor's MAJOR names**: strip the `mI` binders the record
claims, the next binder is the major, and its domain's head constant is read
against the member names; `names.length` — no member — otherwise. -/
def recTargetOf (names : List NIdx) (mI : Nat) (ty : EIdx) : AM Nat := do
  let none' : Nat := names.length
  match ← stripPis mI ty with
  | none => pure none'
  | some q =>
    if q.2.tag == ETag.forallE then
      match ← viewBind q.2 with
      | none => failDanglingE
      | some (dom, _, _) => do
        let hd ← getAppFn coreWalkFuel dom
        if hd.tag == ETag.const then
          match ← viewConst hd with
          | none => failDanglingE
          | some (n, _) =>
            match names.findIdx? (· == n) with
            | some t => pure t
            | none => pure none'
        else pure none'
    else pure none'

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:273-299 blockCounts?
**One member's parameter and index counts**, read as official reads them: off
the member's own telescope when it is a syntactic one ending in a sort, else
off the argument sums `r` of a recursor whose major names the member (the
Rust's `block_counts_rec`, inlined as the second arm). -/
def blockCounts? (nPd k nC nR : Nat) (cvT : IConstantVal) (r : Option (Nat × Nat)) :
    AM (Option (Nat × Nat)) := do
  let (bs, res) ← piBinders coreWalkFuel cvT.type
  match ← view res with
  | .sort _ =>
    let n := bs.length
    if nPd ≤ n then pure (some (nPd, n - nPd)) else pure none
  | _ =>
    match r with
    | none => pure none
    | some (mI, rP) =>
      if rP < nC + k || mI < rP then pure none
      else if rP - (nC + k) == nPd then pure (some (nPd, mI - rP))
      else if k < nR && nPd + nR + nC ≤ rP then pure (some (nPd, mI - rP))
      else pure none

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:301-308 ctorMember?
The member a constructor belongs to: the one its RESULT names (at the block's
own levels `lvls`, `lps.map .param` interned). -/
def ctorMember? (names : List NIdx) (lvls : LsIdx) (nP : Nat) (c : IConstantVal × Nat) :
    AM (Option Nat) := do
  match ← stripPis (nP + c.2) c.1.type with
  | none => pure none
  | some q => do
    let hd ← getAppFn coreWalkFuel q.2
    memberIdxAt? names lvls hd

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:310-323 blockGroups
**The constructors grouped by member**, in block order: at ONE member all of
them, nothing read; at two or more read off the result head (a constructor
whose head is no member lands in no group).  The Rust's `block_groups_from`
and `block_group` are the `mapM` over the members and the `filterM` over the
constructors. -/
def blockGroups (names : List NIdx) (lvls : LsIdx) (nP k : Nat)
    (cs : List (IConstantVal × Nat)) : AM (List (List (IConstantVal × Nat))) := do
  if k == 1 then pure [cs]
  else
    (List.range k).mapM fun m =>
      cs.filterM fun c => do
        match ← ctorMember? names lvls nP c with
        | some t => pure (t == m)
        | none => pure false

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:325-333 blockRecLpsOk
**The recursor records' level-parameter pin**: every recursor carries the
block's level parameters, the elimination parameter in front at the large
eliminator. -/
def blockRecLpsOk (p : BlockShape) : Bool :=
  let lps := p.lps
  p.recs.all fun rc =>
    if p.large then rc.cvR.levelParams == p.elim :: lps
    else rc.cvR.levelParams == lps

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:335-357 blockRecNameSetOk
**The recursor names, as a SET**: exactly `T_m.rec` at every member, each once.
Takes the members and the recursors apart, as the Rust does (module note); the
generated names are interned in block order. -/
def blockRecNameSetOk (members : List MemberShape) (recs : List RecShape) : AM Bool := do
  let want ← members.mapM fun ms => internNNode (.str ms.cvT.name "rec")
  let got := recs.map (·.cvR.name)
  pure (got.length == want.length &&
    want.all (fun n => got.contains n) && got.all (fun n => want.contains n))

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:359-368 blockRecNamesUnreserved
**No recursor takes a name the environment's own guards look up**
(`reservedRecName`), read recursor by recursor and stopping at the first hit,
as the Rust does. -/
def blockRecNamesUnreserved : List RecShape → AM Bool
  | [] => pure true
  | rc :: rest => do
    if ← reservedRecName rc.cvR.name then pure false
    else blockRecNamesUnreserved rest

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:370-383 blockMemberCounts?
**The members' index counts**, one `blockCounts?` per member (from member `m`,
the formers `cvTs`), in order; the recursor handed to it is the first whose
major names the member (the Rust's `rec_for_member`, a `findM?`). -/
def blockMemberCounts? (nPd k nC : Nat) (names : List NIdx)
    (rs : List (IConstantVal × Nat × Nat × List IRecRule)) :
    Nat → List IConstantVal → AM (Option (List Nat))
  | _, [] => pure (some [])
  | m, cvT :: ts => do
    let q ← rs.findM? fun q => do pure ((← recTargetOf names q.2.1 q.1.type) == m)
    let r : Option (Nat × Nat) := match q with
      | some q => some (q.2.1, q.2.2.1)
      | none => none
    match ← blockCounts? nPd k nC rs.length cvT r with
    | none => pure none
    | some c =>
      match ← blockMemberCounts? nPd k nC names rs (m + 1) ts with
      | none => pure none
      | some ns => pure (some (c.2 :: ns))

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
**The block's shape**: split into formers, constructors and recursors (at least
one of each of the first and the last), the members' counts, the reserved-name
and level pins, the result sort (member 0's, or the placeholder `0` the
install's whnf loop replaces), the groups, the recursors in the stream's own
order each with the member its MAJOR names, and which eliminator they are
(`elim :: relps` with `relps == lps` and `elim` fresh is the large one;
anything else is the small one, at `.anonymous`, interned).  The Rust's
`block_shape_at`/`block_shape_sort`/`block_shape_elim` are the three stretches
of this `do` block. -/
def blockShape? (nPd : Nat) (block : List IConstantInfo) : AM (Option BlockShape) := do
  match blockSplit block with
  | none => pure none
  | some (cvTs, cs, rs) =>
    match cvTs, rs with
    | cvT0 :: _, (cvR0, _, _, _) :: _ =>
      let names := cvTs.map (·.name)
      let k := cvTs.length
      match ← blockMemberCounts? nPd k cs.length names rs 0 cvTs with
      | none => pure none
      | some nIdxs =>
        let lps := cvT0.levelParams
        let nP := nPd
        let reserved ← reservedBasisNames
        if (cvTs.all fun c => !reserved.contains c.name && c.levelParams == lps) &&
            (rs.all fun r => !reserved.contains r.1.name) &&
            (cs.all fun c => c.2.1 == nP && c.1.levelParams == lps &&
              !reserved.contains c.1.name) then
          let s ← match ← stripPis (nP + nIdxs.headD 0) cvT0.type with
            | some q => do
              match ← view q.2 with
              | .sort s => pure s
              | _ => zeroLevel
            | none => zeroLevel
          let z ← zeroLevel
          let eq ← lvlEq? s z
          let isProp : Bool := match eq with
            | some true => true
            | some false => false
            | none => false
          let ctors : List (IConstantVal × Nat) := cs.map fun c => (c.1, c.2.2)
          let lvls ← paramLevels lps
          let groups ← blockGroups names lvls nP k ctors
          let members : List MemberShape := ((cvTs.zip nIdxs).zip groups).map
            fun a => ⟨a.1.1, a.1.2, a.2⟩
          let recsL ← rs.mapM fun r => do
            let tgt ← recTargetOf names r.2.1 r.1.type
            pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.map (·.rhs)⟩ : RecShape)
          let large? : Option NIdx := match cvR0.levelParams with
            | [] => none
            | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
          match large? with
          | some elim => pure (some ⟨members, recsL, nP, elim, s, true, isProp⟩)
          | none => do
            let anon ← internNNode .anonymous
            pure (some ⟨members, recsL, nP, anon, s, false, isProp⟩)
        else pure none
    | _, _ => pure none

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:444-449 blockParts?
Recognise a block for the uniform route, at any number of members: its
SHAPE. -/
def blockParts? (nPd : Nat) (block : List IConstantInfo) : AM (Option BlockParts) := do
  match ← blockShape? nPd block with
  | none => pure none
  | some p => pure (some ⟨p⟩)

end ConRon.Arena
