/-
# `ConRon.Arena.Inductives.BlockShape` — the k-ary block: the record and the reader
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/BlockShape.lean` over handles: the record a block
is read into (`MemberShape`, `RecShape`, `BlockShape`), its projections, and
the reader (`blockSplit`, `recTargetOf`, `blockCounts`, `blockGroups`,
`readBlock`) with the recursor records' name and level pins the recursor stage
throws on.  A block the reader cannot read is an invalid input: the reader
returns the cited `Except` as a value (the Rust's inner `Result`), beside the
arena's own failure.  The Rust twin is `arena::inductives::block_shape`.

**The deviations** (the Rust's, item for item):

* **The level lists are compared as interned lists**: `lps.map .param` is
  `paramLevels`, and `us == lvls` is handle equality (`memberIdxAt?`).
* **A projection that reads a term takes the state** (`withSort`'s
  `Level.isEquiv`, `recTargetOf`'s telescope), so it is an `AM` function.
* **`BlockShape.recTgtAt` is not ported**: nothing the executed checker runs
  reads it (the model does); the skip list says so.
* **`blockRecNameSetOk` takes the members and the recursors apart**, and
  **`blockRecNamesUnreserved` takes the recursors**, as the Rust does (the
  caller's `{ p with recs := own }` is an argument, not a record copy).
* **`readBlock`'s three `find?` tests are `all` scans**: a hit only names the
  error, and the messages drop con-leche's interpolated names and counts
  (§3.1), as do `blockCounts`' (whose `r` therefore carries no recursor
  name).
-/
module

public import ConRon.Arena.Inductives.Positivity

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## The record -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:53-70 MemberShape
One member of a block: its type former at its telescope, its type former as
declared, its own index count and its constructors (member-local, in block
order, each with its field count). -/
structure MemberShape where
  /-- the member's type former at its telescope, what the block's check reads
  (`reduceMember`) -/
  cvT : IConstantVal
  /-- the member's type former as the stream declares it, what is installed -/
  declared : IConstantVal
  /-- the member's index count -/
  nIdx : Nat
  /-- the member's constructors in block order, each with its field count -/
  ctors : List (IConstantVal × Nat)
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:72-102 RecShape
**One recursor of a block, as the stream carries it**: its constant, the
record's own rule prefix `rP` and major index `mI`, the member its MAJOR names
(`k`: none — a nested block's auxiliary recursor), its rules as exported (what
the install stores, the checks having compared them with the generated ones,
`streamRecsCheck`) and the record's K flag (what is installed; the job checks
it). -/
structure RecShape where
  /-- the recursor's constant -/
  cvR : IConstantVal
  /-- the recursor record's own rule prefix -/
  rP : Nat
  /-- the recursor record's own major-premise index -/
  mI : Nat
  /-- the member its MAJOR names -/
  tgt : Nat
  /-- the recursor's rules as exported -/
  rules : List IRecRule
  /-- the recursor record's K flag (official's `is_k`) -/
  isK : Bool := false
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:104-108 MemberShape.structCtor?
A structure-like member's constructor: its only one, at no index. -/
def MemberShape.structCtor? (ms : MemberShape) : Option (IConstantVal × Nat) :=
  match ms.ctors with
  | [c] => if ms.nIdx == 0 then some c else none
  | _ => none

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:110-137 BlockShape
The pieces of a recognised block at any number of members: the members, the
recursors, the SHARED parameter count, elimination level parameter
(`.anonymous`, interned, for a small eliminator) and result sort, the two
flags, and the feature flags the members' records declare. -/
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
  /-- the feature flags the members' records declare, in member order: `none`
  when no record carries them, the block then checked at the derived ones
  (`BlockShape.flagsAt`) -/
  flags : Option (List IndFlags) := none
  deriving Repr, Inhabited

/-! ## The feature flags -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:151-162 BlockShape.derivedFlags
**The flags of a block without declared ones**, member `i`'s: what the
official kernel computed from the declaration before the flags were inputs.
`hasEta` is the structure-like shape; the capability takes official's `is_rec`
beside it (`blockCapsAt`).  (`p.members[i]?`'s miss is the cited
`getD default`: the default member has no constructor and no index.) -/
def BlockShape.derivedFlags (p : BlockShape) (i : Nat) : IndFlags :=
  let sf : Bool × Bool := match p.members[i]? with
    | some ms =>
      match ms.ctors with
      | [c] => (ms.nIdx == 0, c.2 == 0)
      | _ => (false, false)
    | none => (false, false)
  let isK : Bool := if p.members.length == 1 then (if p.isProp then sf.2 else false) else false
  { isImpredicative := p.isProp
    isK := isK
    hasProjections := sf.1
    hasEta := sf.1
    hasLargeElim := p.large }

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:164-168 BlockShape.flagsAt
**Member `i`'s feature flags**: its declared ones, or the derived ones at a
block without. -/
def BlockShape.flagsAt (p : BlockShape) (i : Nat) : IndFlags :=
  match p.flags with
  | some fl => fl.getD i default
  | none => p.derivedFlags i

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:170-176 BlockShape.noRules
**The block's recursors carry no rules**: a block with declared flags and
without a large eliminator. -/
def BlockShape.noRules (p : BlockShape) : Bool :=
  match p.flags with
  | some _ => if p.large then false else true
  | none => false

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:178-186 BlockShape.boundedProp
**A proposition whose fields take the ordinary universe bound**: a `Prop`
block that is not `isImpredicative` and has no large eliminator. -/
def BlockShape.boundedProp (p : BlockShape) : Bool :=
  if p.isProp then
    if p.large then false
    else if (p.flagsAt 0).isImpredicative then false
    else true
  else false

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:188-190 BlockShape.projAllowed
**May member `i` have projections?** Its `hasProjections`. -/
def BlockShape.projAllowed (p : BlockShape) (i : Nat) : Bool :=
  (p.flagsAt i).hasProjections

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:192-196 projMembersFrom
The members from position `i` on that may have projections (`projAllowed`). -/
def projMembersFrom (p : BlockShape) : Nat → List MemberShape → List MemberShape
  | _, [] => []
  | i, ms :: rest =>
    if p.projAllowed i then ms :: projMembersFrom p (i + 1) rest else projMembersFrom p (i + 1) rest

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:198-201 BlockShape.projMembers
**The members that may have projections**: the `hasProjections` ones.  The
projection tables are read off these. -/
def BlockShape.projMembers (p : BlockShape) : List MemberShape :=
  projMembersFrom p 0 p.members

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:203-204 BlockShape.formers
The members' formers, at the telescopes the check reads, in block order. -/
def BlockShape.formers (p : BlockShape) : List IConstantVal := p.members.map (·.cvT)

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:206-208 BlockShape.memberCtors
The members' constructors, per member, as declared. -/
def BlockShape.memberCtors (p : BlockShape) : List (List (IConstantVal × Nat)) :=
  p.members.map (·.ctors)

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:210-213 BlockShape.ctorGroups
The constructors grouped by member, each group under its member's name: what
the install conses (`consBlockCtors`), the name becoming each constructor's
`induct`. -/
def BlockShape.ctorGroups (p : BlockShape) : List (NIdx × List (IConstantVal × Nat)) :=
  p.members.map fun ms => (ms.cvT.name, ms.ctors)

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:215-219 numCtorsOf
The constructors of a list of members, counted. -/
def numCtorsOf : List MemberShape → Nat
  | [] => 0
  | ms :: rest => ms.ctors.length + numCtorsOf rest

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:223-224 BlockShape.k
The number of members. -/
def BlockShape.k (p : BlockShape) : Nat := p.members.length

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:225-226 BlockShape.numCtors
The number of constructors of the whole block. -/
def BlockShape.numCtors (p : BlockShape) : Nat := numCtorsOf p.members

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:227-228 BlockShape.memberNames
The members' names, in block order. -/
def BlockShape.memberNames (p : BlockShape) : List NIdx := p.members.map (·.cvT.name)

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:229-230 BlockShape.nIdxs
The members' index counts, in block order. -/
def BlockShape.nIdxs (p : BlockShape) : List Nat := p.members.map (·.nIdx)

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:231-234 BlockShape.lps
The block's level parameters (member 0's; `[]` at no member). -/
def BlockShape.lps (p : BlockShape) : List NIdx :=
  match p.members with
  | [] => []
  | m :: _ => m.cvT.levelParams

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:235-237 BlockShape.allCtors
The constructors of the whole block, in block order. -/
def BlockShape.allCtors (p : BlockShape) : List (IConstantVal × Nat) :=
  (p.members.map (·.ctors)).flatten

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:244-250 BlockShape.rulePrefixAt
Recursor `r`'s rule prefix, the RECORD's (`0`, the default record's, off the
list). -/
def BlockShape.rulePrefixAt (p : BlockShape) (r : Nat) : Nat :=
  match p.recs[r]? with
  | some rc => rc.rP
  | none => 0

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:252-255 BlockShape.majorIdxAt
Recursor `r`'s major-premise index, the RECORD's. -/
def BlockShape.majorIdxAt (p : BlockShape) (r : Nat) : Nat :=
  match p.recs[r]? with
  | some rc => rc.mI
  | none => 0

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:257-261 BlockShape.withSort
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

/-! ## Recognition -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:294-300 blockSplitRecs
The closing recursors: `none` at anything else. -/
def blockSplitRecs : List IConstantInfo →
    Option (List (IConstantVal × Nat × Nat × Bool × List IRecRule))
  | [] => some []
  | .recInfo cvR mI rP isK rules :: rest =>
    match blockSplitRecs rest with
    | some rs => some ((cvR, mI, rP, isK, rules) :: rs)
    | none => none
  | _ :: _ => none

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:302-307 blockSplitCtors
The constructors, then the recursors. -/
def blockSplitCtors : List IConstantInfo →
    Option (List (IConstantVal × Nat × Nat) ×
      List (IConstantVal × Nat × Nat × Bool × List IRecRule))
  | .ctorInfo cvC nP nF _ :: rest =>
    match blockSplitCtors rest with
    | some q => some ((cvC, nP, nF) :: q.1, q.2)
    | none => none
  | rest =>
    match blockSplitRecs rest with
    | some rs => some ([], rs)
    | none => none

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:309-315 blockSplit
The type formers, the constructors and the recursors. -/
def blockSplit : List IConstantInfo →
    Option (List IConstantVal × List (IConstantVal × Nat × Nat) ×
      List (IConstantVal × Nat × Nat × Bool × List IRecRule))
  | .indInfo cvT _ :: rest =>
    match blockSplit rest with
    | some q => some (cvT :: q.1, q.2)
    | none => none
  | rest =>
    match blockSplitCtors rest with
    | some q => some ([], q.1, q.2)
    | none => none

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:317-334 recTargetOf
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
      | some (dom, _) => do
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

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:336-371 blockCounts.recCountsError
A recursor whose argument counts do not fit the block (the cited names and
counts dropped, §3.1). -/
def recCountsError : CheckError :=
  .invalid "the argument counts of a recursor do not fit the block"

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:336-371 blockCounts
**One member's parameter and index counts**, read as official reads them: off
the member's own telescope when it is a syntactic one ending in a sort, else
off the argument sums `r` of a recursor whose major names the member (the
Rust's `block_counts_rec`, inlined as the second arm).  A member that cannot be
counted is an invalid input, with the reason.  The cited `r` also carries the
recursor's name, for the error text; the messages drop it (§3.1), so `r` is the
two counts. -/
def blockCounts (nPd k nC nR : Nat) (cvT : IConstantVal) (r : Option (Nat × Nat)) :
    AM (Except CheckError (Nat × Nat)) := do
  let (bs, res) ← piBinders coreWalkFuel cvT.type
  match ← view res with
  | .sort _ =>
    let n := bs.length
    if nPd ≤ n then pure (.ok (nPd, n - nPd))
    else pure (.error (.invalid "inductive type declares more parameters than its type has binders"))
  | _ =>
    match r with
    | none => pure (.error (.invalid "no recursor of the block eliminates the inductive type"))
    | some (mI, rP) =>
      if rP < nC + k || mI < rP then pure (.error recCountsError)
      else if rP - (nC + k) == nPd then pure (.ok (nPd, mI - rP))
      else if k < nR && nPd + nR + nC ≤ rP then pure (.ok (nPd, mI - rP))
      else pure (.error recCountsError)

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:373-380 ctorMember?
The member a constructor belongs to: the one its RESULT names (at the block's
own levels `lvls`, `lps.map .param` interned). -/
def ctorMember? (names : List NIdx) (lvls : LsIdx) (nP : Nat) (c : IConstantVal × Nat) :
    AM (Option Nat) := do
  match ← stripPis (nP + c.2) c.1.type with
  | none => pure none
  | some q => do
    let hd ← getAppFn coreWalkFuel q.2
    memberIdxAt? names lvls hd

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:382-395 blockGroups
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

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:397-405 blockRecLpsOk
**The recursor records' level-parameter pin**: every recursor carries the
block's level parameters, the elimination parameter in front at the large
eliminator. -/
def blockRecLpsOk (p : BlockShape) : Bool :=
  let lps := p.lps
  p.recs.all fun rc =>
    if p.large then rc.cvR.levelParams == p.elim :: lps
    else rc.cvR.levelParams == lps

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:407-429 blockRecNameSetOk
**The recursor names, as a SET**: exactly `T_m.rec` at every member, each once.
Takes the members and the recursors apart, as the Rust does (module note); the
generated names are interned in block order. -/
def blockRecNameSetOk (members : List MemberShape) (recs : List RecShape) : AM Bool := do
  let want ← members.mapM fun ms => internNNode (.str ms.cvT.name "rec")
  let got := recs.map (·.cvR.name)
  pure (got.length == want.length &&
    want.all (fun n => got.contains n) && got.all (fun n => want.contains n))

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:431-440 blockRecNamesUnreserved
**No recursor takes a name the environment's own guards look up**
(`reservedRecName`), read recursor by recursor and stopping at the first hit,
as the Rust does. -/
def blockRecNamesUnreserved : List RecShape → AM Bool
  | [] => pure true
  | rc :: rest => do
    if ← reservedRecName rc.cvR.name then pure false
    else blockRecNamesUnreserved rest

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:442-456 blockMemberCounts
**The members' index counts**, one `blockCounts` per member (from member `m`,
the formers `cvTs`), in order; the recursor handed to it is the first whose
major names the member (the Rust's `rec_for_member`, a `findM?`).  The first
member that cannot be counted gives the error. -/
def blockMemberCounts (nPd k nC : Nat) (names : List NIdx)
    (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)) :
    Nat → List IConstantVal → AM (Except CheckError (List Nat))
  | _, [] => pure (.ok [])
  | m, cvT :: ts => do
    let q ← rs.findM? fun q => do pure ((← recTargetOf names q.2.1 q.1.type) == m)
    let r : Option (Nat × Nat) := match q with
      | some q => some (q.2.1, q.2.2.1)
      | none => none
    match ← blockCounts nPd k nC rs.length cvT r with
    | .error e => pure (.error e)
    | .ok c =>
      match ← blockMemberCounts nPd k nC names rs (m + 1) ts with
      | .error e => pure (.error e)
      | .ok ns => pure (.ok (c.2 :: ns))

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:458-461 blockFlagRecs
The flags of the leading type records, in order. -/
def blockFlagRecs : List IConstantInfo → List (Option IndFlags)
  | .indInfo _ caps :: rest => caps.flags :: blockFlagRecs rest
  | _ => []

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:463-467 blockFlagsOf
**The block's declared feature flags**: every type record's, when all carry
them; `none` otherwise. -/
def blockFlagsOf (block : List IConstantInfo) : Option (List IndFlags) :=
  (blockFlagRecs block).mapM id

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:469-542 readBlockShape
**Read a declared inductive block's shape**: split into formers, constructors and
recursors (at least one of each of the first and the last), the members'
counts, the universe and parameter declarations (formers', then constructors'
parameter counts, then constructors' universe parameters; each cited `find?`
an `all`, its hit naming only the error), the result sort (member 0's, or the
placeholder `0` the check's whnf loop replaces), the groups, the recursors in
the stream's own order each with the member its MAJOR names, and which
eliminator they are (`elim :: relps` with `relps == lps` and `elim` fresh is
the large one; anything else is the small one, at `.anonymous`, interned).  A
block that cannot be read is an invalid input, and the error says why; the
messages drop con-leche's interpolated names and counts (§3.1).  The Rust's
`read_block_shape` is this `do` block, and `read_block_at`, `read_block_sort` and
`read_block_elim` are its three stretches. -/
def readBlockShape (nPd : Nat) (block : List IConstantInfo) :
    AM (Except CheckError BlockShape) := do
  match blockSplit block with
  | none => pure (.error (.invalid
      "inductive block: its records are not the inductive types, then the constructors, then the recursors"))
  | some (cvTs, cs, rs) =>
    match cvTs, rs with
    | cvT0 :: _, (cvR0, _, _, _, _) :: _ =>
      let names := cvTs.map (·.name)
      let k := cvTs.length
      match ← blockMemberCounts nPd k cs.length names rs 0 cvTs with
      | .error e => pure (.error e)
      | .ok nIdxs =>
        let lps := cvT0.levelParams
        let nP := nPd
        if !(cvTs.all fun c => c.levelParams == lps) then
          pure (.error (.invalid
            "inductive type declares other universe parameters than the block's first type"))
        else if !(cs.all fun c => c.2.1 == nP) then
          pure (.error (.invalid "constructor declares another parameter count than the block"))
        else if !(cs.all fun c => c.1.levelParams == lps) then
          if k == 1 then
            pure (.error (.invalid "constructor declares other universe parameters than its type"))
          else
            pure (.error (.invalid
              "constructor declares other universe parameters than the block's inductive types"))
        else
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
            fun a => ⟨a.1.1, a.1.1, a.1.2, a.2⟩
          let recsL ← rs.mapM fun r => do
            let tgt ← recTargetOf names r.2.1 r.1.type
            pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.2, r.2.2.2.1⟩ : RecShape)
          let large? : Option NIdx := match cvR0.levelParams with
            | [] => none
            | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
          match large? with
          | some elim => pure (.ok ⟨members, recsL, nP, elim, s, true, isProp, none⟩)
          | none => do
            let anon ← internNNode .anonymous
            pure (.ok ⟨members, recsL, nP, anon, s, false, isProp, none⟩)
    | [], _ => pure (.error (.invalid "inductive block declares no inductive type"))
    | _ :: _, [] => pure (.error (.invalid
        "inductive block carries no recursor records; the input must carry the recursors of every inductive block"))

/-- con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:544-547 readBlock
**Read a declared inductive block**: its shape (`readBlockShape`) and the
feature flags its type records declare (`blockFlagsOf`). -/
def readBlock (nPd : Nat) (block : List IConstantInfo) : AM (Except CheckError BlockShape) := do
  match ← readBlockShape nPd block with
  | .error e => pure (.error e)
  | .ok p => pure (.ok { p with flags := blockFlagsOf block })

end ConRon.Arena
