/-
# `ConRon.Arena.Inductives.IotaRead` — the ι reading rule

`ConLeche/Kernel/Inductives/IotaRead.lean` and `IotaEq.lean` over handles,
with the algorithm of their cached twin `ConLeche/Cached/IotaReadC.lean`
(`blockReadsOkC`): after a block's check, every recursor it installs must
state, in each minor premise, the constructor's fields, indices, levels and
parameters as the constructor's own type does — syntactically, up to
equivalent universe levels (`lvlEq`) and, in a `.plain` rule whose recursor
parameters fit the constructor's, up to Lean's consumed type annotations
(`annEq`: `optParam`/`autoParam`/`outParam`/`semiOutParam`, each only where
it is stored as the identity on its type argument).  The Rust twin is
`arena::inductives::iota_read`.

**The deviations of this module** (the Rust's, item for item):

* **The answer is a `Bool`**, and the arm (`Arena/CheckDecl.lean`) throws the
  rejection: the message is a constant (§3.1 drops the interpolation of the
  recursor's and the constructor's names), so `recReadsOk`'s first failing
  rule and the conjunction of all of them are the same verdict.
* **The environment after the install is the INPUT index with the block's
  constants pushed in place** (`blockReadsAt`), the way upstream's cached
  `checkBlockKS` builds it (`FEnv.pushDelta (blockConstantsC p₀) Q fe`):
  `checkBlock`'s own answer is the constructors' environment with the
  recursors pushed (`Arena/Inductives/BlockTail.lean`), whose formers are
  the REDUCED ones, so it is not the environment the rule reads.  The tables
  are not pushed: the rule reads constants only.  The pushes are undone
  before `checkBlock` runs, and the arm acts on the answer after it, so a
  block both reject has `checkBlock`'s verdict, as upstream's.
* **The recursor's frame is read once per recursor** (`iotaRecOf`): the rule
  prefix, the minor premises of the motive the body applies, and the major's
  levels and parameters do not depend on the rule; `iotaPartsOf` reads them
  per rule.  Each rule then reads its own minor (`iotaPartsOfAt`).
* **`iotaPartsAt` also answers the constructor's parameter domains**, which
  `paramsAnnEq` strips off the same instantiated type.
* **The annotations' names are interned** (`.str .anonymous "optParam"` &c.)
  and compared by handle; `n.missing` likewise.
* **`==` on terms, names and level lists is handle equality** (interning is
  injective).
-/
module

public import ConRon.Arena.Install
public import ConRon.Arena.Inductives.BlockTail
public import ConRon.Arena.Inductives.GenRec

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## The recursor's own type (`IotaEq.lean`) -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:83-86 Expr.piTele
A `∀`-telescope's binder count and its body. -/
def piTele : Nat → EIdx → AM (Nat × EIdx)
  | 0, _ => fail (.internal "fuel exhausted: piTele")
  | fuel + 1, h => do
    if h.tag == ETag.forallE then
      match ← viewBind h with
      | none => failDanglingE
      | some (_, b) => do
        let r ← piTele fuel b
        pure (r.1 + 1, r.2)
    else pure (0, h)

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:32-43 motiveLevel?
The sort level of a recursor's motive: the motive application `body` (under
the rule prefix `pre`, the `nIdx` indices and the major) has a prefix variable
as its head, and that binder's domain ends in `Sort u`. -/
def motiveLevel? (pre : List EIdx) (nIdx : Nat) (body : EIdx) : AM (Option LIdx) := do
  let hd ← getAppFn coreWalkFuel body
  if hd.tag == ETag.bvar then
    match ← viewBVar hd with
    | none => failDanglingE
    | some k =>
      if nIdx + 1 ≤ k then
        if k < nIdx + 1 + pre.length then do
          let d ← exprGetD pre (pre.length - 1 - (k - (nIdx + 1)))
          let r ← piResult coreWalkFuel d
          if r.tag == ETag.sort then
            match ← viewSort r with
            | none => failDanglingE
            | some u => pure (some u)
          else pure none
        else pure none
      else pure none
  else pure none

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:45-53 iotaFrame
**A recursor's frame**: its rule prefix (the first `rP` binders of its type),
the domains of the `mI - rP` index binders and the major's, the body after
them, and the sort level of the motive the body applies. -/
def iotaFrame (cv : IConstantVal) (mI rP : Nat) :
    AM (Option (List EIdx × List EIdx × EIdx × LIdx)) := do
  match ← stripPis rP cv.type with
  | none => pure none
  | some (pre, rest) =>
    match ← stripPis (mI - rP + 1) rest with
    | none => pure none
    | some (doms, body) =>
      match ← motiveLevel? pre (mI - rP) body with
      | none => pure none
      | some u => pure (some (pre, doms, body, u))

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:88-94 minorsOf
Is the prefix binder at position `q` a minor premise of the motive at prefix
position `mot`: its conclusion (behind all its `∀`s) headed by that motive. -/
def isMinorAt (pre : List EIdx) (mot q : Nat) : AM Bool := do
  let d ← exprGetD pre q
  let t ← piTele coreWalkFuel d
  let hd ← getAppFn coreWalkFuel t.2
  if hd.tag == ETag.bvar then
    match ← viewBVar hd with
    | none => failDanglingE
    | some m => if mot < q then pure (m == t.1 + (q - 1 - mot)) else pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:88-94 minorsOf
**The minor premises of the motive at prefix position `mot`** from position
`q` on: the positions of the prefix binders `isMinorAt` accepts, in order. -/
def minorsFrom (pre : List EIdx) (mot : Nat) (q : Nat) : AM (List Nat) := do
  if q < pre.length then do
    let b ← isMinorAt pre mot q
    let rest ← minorsFrom pre mot (q + 1)
    if b then pure (q :: rest) else pure rest
  else pure []
termination_by pre.length - q

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
**What every rule of a recursor reads off its type**: the rule prefix, the
minor premises of the motive the body applies, and the major premise's type
`C'.{us} params is` — its levels and its parameters (the `is` the index
variables, dropped). -/
structure IotaRec where
  pre : List EIdx
  minors : List Nat
  us : LsIdx
  params : List EIdx
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
`iotaRecOf` past the motive's head `k`: its minor premises, then the major's
type at a constant head — its levels and its leading arguments, the index
variables dropped. -/
def iotaRecMajor (pre doms : List EIdx) (nIdx rP k : Nat) : AM (Option IotaRec) := do
  let minors ← minorsFrom pre (rP + nIdx - k) 0
  let dom ← exprGetD doms nIdx
  let dh ← getAppFn coreWalkFuel dom
  if dh.tag == ETag.const then
    match ← viewConst dh with
    | none => failDanglingE
    | some (_, us) => do
      let args ← getAppArgs coreWalkFuel dom
      let ps ← (args.take (args.length - nIdx)).mapM (exprDropVars nIdx)
      pure (some ⟨pre, minors, us, ps⟩)
  else pure none

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
The rule-independent part of `iotaPartsOf`, read once per recursor: the frame,
the motive the body applies (a variable), then `iotaRecMajor`. -/
def iotaRecOf (cv : IConstantVal) (mI rP : Nat) : AM (Option IotaRec) := do
  let nIdx := mI - rP
  match ← iotaFrame cv mI rP with
  | none => pure none
  | some (pre, doms, body, _) =>
    let hd ← getAppFn coreWalkFuel body
    if hd.tag == ETag.bvar then
      match ← viewBVar hd with
      | none => failDanglingE
      | some k => iotaRecMajor pre doms nIdx rP k
    else pure none

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:55-62 IotaParts
**The parts a rule's ι equation is built from**: the fields' domains, the
indices, the constructor's levels and its parameters. -/
structure IIotaParts where
  fieldDoms : List EIdx
  idx : List EIdx
  us : LsIdx
  params : List EIdx
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
`fd.mapIdx (fun j d => d.liftLooseBVars amt j)`, from field `j` on. -/
def liftFieldDoms (amt : Nat) : List EIdx → Nat → AM (List EIdx)
  | [], _ => pure []
  | d :: ds, j => do
    let d' ← liftLooseBVarsFast coreWalkFuel amt j d
    let rest ← liftFieldDoms amt ds (j + 1)
    pure (d' :: rest)

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
The conclusion's leading arguments as indices: each with the `nT` induction
hypotheses behind it dropped, then lifted past the later prefix (`amt`) above
the `nF` fields. -/
def liftIdxArgs (amt nT nF : Nat) : List EIdx → AM (List EIdx)
  | [] => pure []
  | a :: as => do
    let b ← exprDropVars nT a
    let c ← liftLooseBVarsFast coreWalkFuel amt nF b
    let rest ← liftIdxArgs amt nT nF as
    pure (c :: rest)

/-- con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
**A rule's parts, read off the recursor's own type** (the statement's
reading), at the recursor's frame `rr`: the rule `i` reads the `i`-th minor
premise; its first `nfields` binders are the fields (lifted past the later
prefix binders), its conclusion's first `nIdx` arguments the indices. -/
def iotaPartsOfAt (rr : IotaRec) (rP nIdx i : Nat) (rl : IRecRule) :
    AM (Option IIotaParts) := do
  if i < rr.minors.length then do
    let q := rr.minors.getD i 0
    let d ← exprGetD rr.pre q
    match ← stripPis rl.nfields d with
    | none => pure none
    | some (fd, inner) => do
      let fds ← liftFieldDoms (rP - q) fd 0
      let t ← piTele coreWalkFuel inner
      let args ← getAppArgs coreWalkFuel t.2
      let idx ← liftIdxArgs (rP - q) t.1 rl.nfields (args.take nIdx)
      pure (some ⟨fds, idx, rr.us, rr.params⟩)
  else pure none

/-! ## The proofs' reading: through the constructor (`IotaRead.lean`) -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:50-58 RecRule.ctorLevels
The levels a recursor rule's constructor is used at, interned: the rule's
recorded levels where it records them, else the constructor's own
parameters. -/
def ctorLevelsAt (rl : IRecRule) (ctorLps : List NIdx) : AM LsIdx := do
  match rl.fire with
  | .nested lvls _ => internLsNode lvls
  | .levels lvls => internLsNode lvls
  | .plain => paramLevels ctorLps

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:60-66 RecRule.iotaParams
`(List.range n).map fun i => .bvar (rP - 1 - i)`, from `i` on. -/
def iotaBVars (rP n : Nat) (i : Nat) : AM (List EIdx) := do
  if i < n then do
    let b ← internBVarE (rP - 1 - i)
    let rest ← iotaBVars rP n (i + 1)
    pure (b :: rest)
  else pure []
termination_by n - i

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:60-66 RecRule.iotaParams
The parameters a recursor rule applies its constructor to, in the rule
prefix's context: a nested rule's recorded pins, else the prefix's first
`cnP` variables (as many as the prefix has). -/
def iotaParamsAt (rl : IRecRule) (rP cnP : Nat) : AM (List EIdx) := do
  match rl.fire with
  | .nested _ pins => pure pins
  | _ => iotaBVars rP (min cnP rP) 0

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:70-82 iotaPartsAt
con-leche: ConLeche/Cached/IotaReadC.lean:23-32 iotaPartsAtC
`iotaPartsAt` past the parameters: the constructor's body at the rule's
parameters, its next `nfields` binders, the indices behind the parameters,
and the shape guard. -/
def iotaPartsAtBody (cnP mI rP : Nat) (rl : IRecRule) (lvls : LsIdx) (params pd : List EIdx)
    (ctorBody : EIdx) : AM (Option (IIotaParts × List EIdx)) := do
  -- the arena's substitution vector is newest last: `params` is `params.reverse`'s reading
  let body ← instantiateLiftFast coreWalkFuel ctorBody params.toArray
  match ← stripPis rl.nfields body with
  | none => pure none
  | some (fieldDoms, concl) => do
    let args ← getAppArgs coreWalkFuel concl
    let indices := args.drop cnP
    if params.length = cnP then
      if rP ≤ mI then
        if indices.length = mI - rP then pure (some (⟨fieldDoms, indices, lvls, params⟩, pd))
        else pure none
      else pure none
    else pure none

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:70-82 iotaPartsAt
con-leche: ConLeche/Cached/IotaReadC.lean:23-32 iotaPartsAtC
**A rule's parts, read through the constructor `cvj`** (with `cnP`
parameters): its type at the rule's levels, instantiated at the rule's
parameters; the fields' domains are its next `nfields` binders, the indices
its conclusion's arguments behind the parameters.  Answered with the
constructor's parameter domains at the rule's levels (`paramsAnnEq`'s). -/
def iotaPartsAt (cvj : IConstantVal) (cnP mI rP : Nat) (rl : IRecRule) :
    AM (Option (IIotaParts × List EIdx)) := do
  let lvls ← ctorLevelsAt rl cvj.levelParams
  let params ← iotaParamsAt rl rP cnP
  let ty ← instLPFast coreWalkFuel cvj.levelParams lvls cvj.type
  match ← stripPis cnP ty with
  | none => pure none
  | some (pd, ctorBody) => iotaPartsAtBody cnP mI rP rl lvls params pd ctorBody

/-! ## The checker's rule: the two readings are one -/

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:99-112 Expr.lvlEq
**Equal up to equivalent universe levels**: the same handle, or the same
syntax form with each `Sort` and constant at levels `Level.isEquiv` decides
equal and its parts so related. -/
def lvlEq : Nat → EIdx → EIdx → AM Bool
  | 0, _, _ => fail (.internal "fuel exhausted: lvlEq")
  | fuel + 1, a, b => do
    if a == b then pure true
    else if a.tag == b.tag then
    if a.tag == ETag.sort then
      match ← viewSort a, ← viewSort b with
      | some u, some v => do
        let lu ← readLevelM u
        let lv ← readLevelM v
        pure (Level.isEquiv lu lv == some true)
      | _, _ => failDanglingE
    else if a.tag == ETag.const then
      match ← viewConst a, ← viewConst b with
      | some (n, us), some (m, vs) => do
        if n == m then do
          let lu ← readLevelsM us
          let lv ← readLevelsM vs
          pure (Level.isEquivList lu lv == some true)
        else pure false
      | _, _ => failDanglingE
    else if a.tag == ETag.app then
      match ← viewApp a, ← viewApp b with
      | some (f, x), some (g, y) => do
        if ← lvlEq fuel f g then lvlEq fuel x y else pure false
      | _, _ => failDanglingE
    else if a.tag == ETag.lam || a.tag == ETag.forallE then
      match ← viewBind a, ← viewBind b with
      | some (t, x), some (t', y) => do
        if ← lvlEq fuel t t' then lvlEq fuel x y else pure false
      | _, _ => failDanglingE
    else if a.tag == ETag.letE then
      match ← viewLet a, ← viewLet b with
      | some (t, v, x), some (t', v', y) => do
        if ← lvlEq fuel t t' then
          if ← lvlEq fuel v v' then lvlEq fuel x y else pure false
        else pure false
      | _, _ => failDanglingE
    else if a.tag == ETag.proj then
      match ← viewProj a, ← viewProj b with
      | some (s, i, x), some (s', i', y) => do
        if s == s' then
          if i == i' then lvlEq fuel x y else pure false
        else pure false
      | _, _ => failDanglingE
    else pure false
    else pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:114-118 optParamName
A top-level name, interned: `.str .anonymous s`. -/
def topName (s : String) : AM NIdx := do
  let a ← internNNode .anonymous
  internNNode (.str a s)

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:120-127 annWitness
**A type a stored constant inhabits**: `D` is a constant type `n` at no levels
and the constant `n.missing` is stored at no levels with type `D`. -/
def annWitness (fe : IFEnv) (D : EIdx) : AM Bool := do
  if D.tag == ETag.const then
    match ← viewConst D with
    | none => failDanglingE
    | some (n, us) => do
      match ← viewLsLen us with
      | some 0 => do
        let m ← internNNode (.str n "missing")
        match fe.find? m with
        | some c =>
          if c.toConstantVal.type == D then pure (c.toConstantVal.levelParams.length == 0)
          else pure false
        | none => pure false
      | some _ => pure false
      | none => failDanglingLs
  else pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:129-134 annIdentVal
The value's body under `fun (α : Sort p')`, at the definition's level
parameter `p`: `α` itself at arity 1, `fun (_ : D) => α` at arity 2 with `D`
either `α` or a type a stored constant inhabits. -/
def annIdentBody (fe : IFEnv) (p p' : NIdx) (arity : Nat) (b : EIdx) : AM Bool := do
  if arity == 1 then
    if b.tag == ETag.bvar then
      match ← viewBVar b with
      | none => failDanglingE
      | some j => if j == 0 then pure (p == p') else pure false
    else pure false
  else if arity == 2 then
    if b.tag == ETag.lam then
      match ← viewBind b with
      | none => failDanglingE
      | some (D, c) =>
        if c.tag == ETag.bvar then
          match ← viewBVar c with
          | none => failDanglingE
          | some j =>
            if j == 1 then
              if p == p' then do
                let z ← internBVarE 0
                if D == z then pure true else annWitness fe D
              else pure false
            else pure false
        else pure false
    else pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:129-134 annIdentVal
`annIdent`'s test of the definition's level parameters and value: one level
parameter `p`, the value `fun (α : Sort p') => …` with `annIdentBody`
accepting the body. -/
def annIdentVal (fe : IFEnv) (lps : List NIdx) (arity : Nat) (v : EIdx) : AM Bool := do
  if lps.length == 1 then
    if v.tag == ETag.lam then
      match ← viewBind v with
      | none => failDanglingE
      | some (ty, b) =>
        if ty.tag == ETag.sort then
          match ← viewSort ty with
          | none => failDanglingE
          | some u => do
            match ← viewL u with
            | .param p' => annIdentBody fe (lps.getD 0 default) p' arity b
            | _ => pure false
        else pure false
    else pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:136-145 annIdent
**An annotation stored as the identity on its type argument**: `n` is a
definition whose level parameters and value `annIdentVal` accepts. -/
def annIdent (fe : IFEnv) (n : NIdx) (arity : Nat) : AM Bool := do
  match fe.find? n with
  | some (.defnInfo cv v _) => annIdentVal fe cv.levelParams arity v
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:147-158 annEq
**`s` is `c` with type annotations consumed at its head** (Lean's
`consume_type_annotations`), up to equivalent levels. -/
def annEq (fe : IFEnv) : Nat → EIdx → EIdx → AM Bool
  | 0, _, _ => fail (.internal "fuel exhausted: annEq")
  | fuel + 1, s, c => do
    if ← lvlEq coreWalkFuel s c then pure true
    else if c.tag == ETag.app then
      match ← viewApp c with
      | none => failDanglingE
      | some (f, x) =>
        if f.tag == ETag.app then
          match ← viewApp f with
          | none => failDanglingE
          | some (g, a) =>
            if g.tag == ETag.const then
              match ← viewConst g with
              | none => failDanglingE
              | some (n, us) => do
                match ← viewLsLen us with
                | some 1 => do
                  let o ← topName "optParam"
                  let t ← topName "autoParam"
                  if n == o || n == t then
                    if ← annIdent fe n 2 then annEq fe fuel s a else pure false
                  else pure false
                | some _ => pure false
                | none => failDanglingLs
            else pure false
        else if f.tag == ETag.const then
          match ← viewConst f with
          | none => failDanglingE
          | some (n, us) => do
            match ← viewLsLen us with
            | some 1 => do
              let o ← topName "outParam"
              let t ← topName "semiOutParam"
              if n == o || n == t then
                if ← annIdent fe n 1 then annEq fe fuel s x else pure false
              else pure false
            | some _ => pure false
            | none => failDanglingLs
        else pure false
    else pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:160-164 listRel
`listRel Expr.lvlEq`: two lists, pairwise equal up to equivalent levels. -/
def listLvlEq : List EIdx → List EIdx → AM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← lvlEq coreWalkFuel a b then listLvlEq as bs else pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:160-164 listRel
`listRel (annEq find?)`: two lists, pairwise related by `annEq`. -/
def listAnnEq (fe : IFEnv) : List EIdx → List EIdx → AM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← annEq fe coreWalkFuel a b then listAnnEq fe as bs else pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:166-175 paramsAnnEq
con-leche: ConLeche/Cached/IotaReadC.lean:49-56 paramsAnnEqC
**A plain rule's parameters fit its constructor's**: the recursor's first
`cnP` binder domains are the constructor's parameter domains `pd` (at the
rule's levels, `iotaPartsAt`'s second answer) up to consumed annotations and
equivalent levels. -/
def paramsAnnEq (fe : IFEnv) (cnP : Nat) (cv : IConstantVal) (pd : List EIdx) : AM Bool := do
  match ← stripPis cnP cv.type with
  | some (rd, _) => listAnnEq fe rd pd
  | none => pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:177-185 iotaPartsRel
con-leche: ConLeche/Cached/IotaReadC.lean:58-64 iotaPartsRelC
**The two readings of a rule's parts are one**: the same indices, levels and
parameters; the fields' domains the constructor's up to equivalent levels,
or — in a plain rule whose parameters fit the constructor's — up to consumed
annotations as well. -/
def iotaPartsRel (fe : IFEnv) (cnP : Nat) (cv : IConstantVal) (rl : IRecRule)
    (p' p : IIotaParts) (pd : List EIdx) : AM Bool := do
  if p'.idx == p.idx then
    if p'.us == p.us then
      if p'.params == p.params then
        if ← listLvlEq p'.fieldDoms p.fieldDoms then pure true
        else
          match rl.fire with
          | .plain =>
            if ← paramsAnnEq fe cnP cv pd then listAnnEq fe p'.fieldDoms p.fieldDoms
            else pure false
          | _ => pure false
      else pure false
    else pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:187-196 ruleReadsB
con-leche: ConLeche/Cached/IotaReadC.lean:66-74 ruleReadsBC
**One rule reads**: its parts read off the recursor's type are the parts read
through its constructor, which the index stores under the rule's name. -/
def ruleReads (fe : IFEnv) (cv : IConstantVal) (rr : Option IotaRec) (mI rP i : Nat)
    (rl : IRecRule) : AM Bool := do
  match rr with
  | none => pure false
  | some r =>
    match ← iotaPartsOfAt r rP (mI - rP) i rl with
    | none => pure false
    | some p' =>
      match fe.find? rl.ctor with
      | some (.ctorInfo cvj cnP _ _) =>
        match ← iotaPartsAt cvj cnP mI rP rl with
        | some (p, pd) => iotaPartsRel fe cnP cv rl p' p pd
        | none => pure false
      | _ => pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:198-207 recReadsOk
con-leche: ConLeche/Cached/IotaReadC.lean:76-84 recReadsOkC
Each rule from position `i` on reads. -/
def rulesRead (fe : IFEnv) (cv : IConstantVal) (rr : Option IotaRec) (mI rP : Nat) :
    List IRecRule → Nat → AM Bool
  | [], _ => pure true
  | rl :: rest, i => do
    if ← ruleReads fe cv rr mI rP i rl then rulesRead fe cv rr mI rP rest (i + 1)
    else pure false

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:198-207 recReadsOk
con-leche: ConLeche/Cached/IotaReadC.lean:76-84 recReadsOkC
**The checker's rule, at one recursor**: each of its rules reads, by position;
any other constant reads trivially. -/
def recReads (fe : IFEnv) (ci : IConstantInfo) : AM Bool := do
  match ci with
  | .recInfo cv mI rP _ rules => do
    let rr ← iotaRecOf cv mI rP
    rulesRead fe cv rr mI rP rules 0
  | _ => pure true

/-- con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:209-213 blockReadsOk
con-leche: ConLeche/Cached/IotaReadC.lean:86-89 blockReadsOkC
Every recursor of the list reads. -/
def recsRead (fe : IFEnv) : List IConstantInfo → AM Bool
  | [] => pure true
  | ci :: rest => do
    if ← recReads fe ci then recsRead fe rest else pure false

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:28-170 checkDeclKind
con-leche: ConLeche/Cached/ParsedC.lean:106-126 checkIndDeclC
**The checker's rule, at a block** (`blockReadsOk`): every recursor the block
installs reads, against the environment after the install — the index `fe`
with the block's constants (`blockConstants`) pushed in place.  Answers the
verdict and the index with the pushes undone. -/
def blockReadsAt (fe : IFEnv) (p : BlockShape) : AM (Bool × IFEnv) := do
  let cs ← blockConstants p
  let recs ← blockRecs p p.recs
  let (feR, prevs) := consBlockRecsTemp cs fe []
  let ok ← recsRead feR recs
  let fe₀ := (prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feR).setFlags fe.natLit
    fe.strLit
  pure (ok, fe₀)

end ConRon.Arena
