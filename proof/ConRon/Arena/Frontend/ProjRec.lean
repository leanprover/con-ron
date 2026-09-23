/-
# `ConRon.Arena.Frontend.ProjRec` — projection functions as recursor
applications, over handles (DESIGN.md §8, task #97e part 2)

con-leche's `ConLeche/Frontend/ProjRec.lean`, clause for clause, over the
`ExprOps` twins of `Arena/ExprOps.lean`.  The rewrite it implements is
con-leche's own (its module doc has the design and the user's ruling): the
elaborator spells a structure's projection function as `fun p⃗ self => .proj T
i self`, this checker serves `.proj` only on the class its direct install
recognises, and for the others the definition is replaced — before
installation, transparently to the checked code — by the equivalent recursor
application

    fun p⃗ (self : T p⃗) =>
      T.rec.{ℓ, u⃗} p⃗ motive_1 … motive_m minor_1 … minor_k self

What changes over handles, and nothing else does:

* every structural read of a term is a `view`, so every walk carries DESIGN
  §8.4's explicit `fuel` (the store's node count bounds every path through it);
* every term the rewrite BUILDS is interned, so `mkLams`, `instPisOpen`,
  `buildBinders` and `projRecValue` are monadic where con-leche's are pure;
* a name comparison is a handle comparison — sound because `denoteN` is
  injective (task #97a's `denoteN_inj`, DESIGN §8.3's exactness obligation) —
  and a name the rewrite needs to SPEAK (`T.str "rec"`, `PUnit`, `PUnit.unit`,
  `Eq`, `T._model.proj_i.iota`) is interned;
* the level algorithm (`Level.isEquiv`) runs on a READ-BACK level tree
  (DESIGN §8.3 lesson 4, "intern the representation, not the algorithm").

## Three deviations, each forced

**1. `buildBinders` takes a KIND, not a function.**  con-leche passes
`mkMotive` / `mkMinor` as `mk : Expr → Option Expr`.  DESIGN §3.4 forbids a
closure in code Aeneas must translate, and this one would have to be monadic
besides.  The twin passes `ProjBinderKind` and a `ProjBuild` record of what
the two bodies read, and dispatches by the tag — which is the enum the Rust
would need anyway.  The two bodies are the two top-level functions
`mkProjMotive` and `mkProjMinor`, clause for clause with con-leche's lambdas.

**2. The three `List.any` / `List.find?` closures of `projRecOwners` are
explicit recursions** (`occursAnyOf`, `domsMentionAny`, `ctorsMentionBlock`,
`findCtorRec`, `findRecRec`), which is DESIGN §3.4's own rule for a `List`
recursion and what task #97b did to the same shapes in `ExprOps`.

**3. `projRecOwners` evaluates its guards in the cheap order, and the result
is the same value.**  con-leche computes `recursive` and runs
`structPartsCore?` / `nativeParts?` FIRST and the `filterMap` last; both early
branches return `[]`.  So when the `filterMap` is empty the whole function is
`[]` whatever the guards say, and computing the `filterMap` first and the
guards only when it is non-empty is the same function.

Task #97e part 2 had a second reason for the order: the two recognisers were
not twinned then, so this module read the block BACK and called con-leche's
own on `Expr` trees.  P2d twinned them (`Arena/Inductives/StructParts.lean`
and `Arena/Inductives/NativeParts.lean`), and task #97f's dedup pointed the
two guards at the twins — so nothing in the frontend crosses to the
denotation any more.  The cheap order stays, because it is still free and
still the same value.
-/
import ConRon.Arena.Frontend.Types
import ConRon.Arena.Frontend.Readback
import ConRon.Arena.ExprOps
import ConRon.Arena.Inductives.NativeParts
import ConLeche.Kernel.Level

namespace ConRon.Arena.Frontend

open ConLeche
open ConRon.Arena

/-! ## The artifact's name and level -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:106-111 projIotaName — the name
of the model family's constructor-reduction theorem for field `i` of `T`:
`T._model.proj_i.iota`.  Building a name means interning it, so the twin is
monadic (`Arena/Env.lean`'s `projFnName` note). -/
def projIotaName (T : NIdx) (i : Nat) : AM NIdx := do
  let a ← internNNode (.str T "_model")
  let b ← internNNode (.str a s!"proj_{i}")
  internNNode (.str b "iota")

/-- con-leche: ConLeche/Frontend/ProjRec.lean:113-118 isProjIotaName — is `n`
of the shape `X._model.proj_i.iota`?  The cheap pre-filter for the theorem
records; the last component decides before anything is compared. -/
def isProjIotaName (n : NIdx) : AM Bool := do
  match ← viewN n with
  | .str p1 "iota" =>
    match ← viewN p1 with
    | .str p2 s =>
      match ← viewN p2 with
      | .str _ "_model" => pure (s.startsWith "proj_")
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Frontend/ProjRec.lean:120-125 projIotaLevel — the `Eq`
level of an artifact iota statement `∀ …, @Eq.{ℓ} α a b`: the field's sort.
`none` on any other shape.  The universe argument list is ONE handle
(DESIGN §8.3's `LsIdx`), so the singleton test is a `viewLs`. -/
def projIotaLevel (fuel : Nat) (ty : EIdx) : AM (Option LIdx) := do
  let r ← piResult fuel ty
  let f ← getAppFn fuel r
  match ← view f with
  | .const n us =>
    match ← viewLs us with
    | [l] => do
      let eqH ← internName ConLeche.eqName
      pure (if n == eqH then some l else none)
    | _ => pure none
  | _ => pure none

/-! ## `occursConst`

con-leche carries FOUR declarations for one algorithm — a pure structural
walk, a budgeted allocation-free descent (`occursConstB`), a memoised one
(`occursConstGo`) and the entry `occursConstFast` — and the arena carries two,
by task #97b's rule that a twin is per ALGORITHM and cites every con-leche
declaration it stands for.

**The budgeted descent has no arena twin, and that is the representation
talking.**  Its purpose in con-leche is to answer a SMALL tree without
allocating the `Std.HashSet Expr`, falling back to the memoised walk when the
budget runs out; the threaded remaining budget is what bounds the total work.
Over handles the subject is a DAG, so the memo is not an optimisation but the
thing that makes the walk linear at all — a subterm reached by two parents is
visited twice without it — and the budget cannot be the walk's termination
measure either, since the budget a sub-call RETURNS is only bounded by the one
it was given, not below it (con-leche's recursion is structural on the `Expr`
and needs no measure).  So the arena walks once, memoised, on DESIGN §8.4's
explicit DAG fuel.  What is lost is an allocation on a small term; what is
gained is that a shared domain is not re-walked per occurrence, which is the
`ModularCurve` shape con-leche's own task #214 note describes. -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:127-136 occursConst
con-leche: ConLeche/Frontend/ProjRec.lean:151-178 occursConstB
con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
The memoised descent: the set holds the subterms already shown NOT to mention `n`.
Only `false` is recorded — a `true` aborts the walk, so no `true` is ever
re-queried.  The set is keyed on the handle, which is nanoda's identity hash
(DESIGN §8.3) and con-leche's `Std.HashSet Expr` with its cached hash. -/
def occursConstGo (n : NIdx) (seen : Std.HashSet EIdx) :
    Nat → EIdx → AM (Bool × Std.HashSet EIdx)
  | 0, _ => fail (.internal "fuel exhausted: occursConstGo")
  | fuel + 1, h => do
    match ← view h with
    | .const m _ => pure (m == n, seen)
    | .bvar _ | .fvar .. | .sort _ | .lit _ => pure (false, seen)
    | .app f a =>
      if seen.contains h then pure (false, seen) else do
        match ← occursConstGo n seen fuel f with
        | (false, seen) =>
          match ← occursConstGo n seen fuel a with
          | (false, seen) => pure (false, seen.insert h)
          | r => pure r
        | r => pure r
    | .lam ty b _ =>
      if seen.contains h then pure (false, seen) else do
        match ← occursConstGo n seen fuel ty with
        | (false, seen) =>
          match ← occursConstGo n seen fuel b with
          | (false, seen) => pure (false, seen.insert h)
          | r => pure r
        | r => pure r
    | .forallE ty b _ =>
      if seen.contains h then pure (false, seen) else do
        match ← occursConstGo n seen fuel ty with
        | (false, seen) =>
          match ← occursConstGo n seen fuel b with
          | (false, seen) => pure (false, seen.insert h)
          | r => pure r
        | r => pure r
    | .letE t v b =>
      if seen.contains h then pure (false, seen) else do
        match ← occursConstGo n seen fuel t with
        | (false, seen) =>
          match ← occursConstGo n seen fuel v with
          | (false, seen) =>
            match ← occursConstGo n seen fuel b with
            | (false, seen) => pure (false, seen.insert h)
            | r => pure r
          | r => pure r
        | r => pure r
    | .proj _ _ sub =>
      if seen.contains h then pure (false, seen) else do
        match ← occursConstGo n seen fuel sub with
        | (false, seen) => pure (false, seen.insert h)
        | r => pure r

/-- con-leche: ConLeche/Frontend/ProjRec.lean:227-231 occursConstFast — the
executed `occursConst`: the memoised descent at a fresh set (the section note
above says why the budgeted one has no twin). -/
def occursConstFast (fuel : Nat) (n : NIdx) (h : EIdx) : AM Bool := do
  pure (← occursConstGo n {} fuel h).1

/-! ## Telescopes the rewrite builds and takes apart -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:233-237 lamBody — the body under
every leading `λ` (the projection shape's pre-filter: the node under the
value's binders). -/
def lamBody : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: lamBody")
  | fuel + 1, h => do
    -- tag first, then the binder projection, as the port (task #97-T2-LOCKSTEP, D1)
    if h.tag == ETag.lam then
      match ← viewBind h with
      | none => failDanglingE
      | some (_, b, _) => lamBody fuel b
    else pure h

/-- con-leche: ConLeche/Frontend/ProjRec.lean:239-245 stripPisAll — strip every
leading `∀`: the binder list (outermost first) and the body. -/
def stripPisAll : Nat → EIdx → AM (List (EIdx × BinderMeta) × EIdx)
  | 0, _ => fail (.internal "fuel exhausted: stripPisAll")
  | fuel + 1, h => do
    match ← view h with
    | .forallE ty b m => do
      let p ← stripPisAll fuel b
      pure ((ty, m) :: p.1, p.2)
    | _ => pure ([], h)

/-- con-leche: ConLeche/Frontend/ProjRec.lean:247-249 mkLams — rebuild a
`λ`-telescope over a binder list (outermost first).  Structural on the list,
so no fuel; every binder is interned. -/
def mkLams : List (EIdx × BinderMeta) → EIdx → AM EIdx
  | [], body => pure body
  | (ty, m) :: bs, body => do
    let acc ← mkLams bs body
    internE (.lam ty acc m)

/-- con-leche: ConLeche/Frontend/ProjRec.lean:251-257 instPisOpen — instantiate
the leading `∀`-binders at *open* arguments (the body-frame variables and the
built motives/minors), one binder per argument, returning the residual
telescope.  Structural on the argument list; `fuel` is the one
`instantiate1LiftFast` needs. -/
def instPisOpen (fuel : Nat) : EIdx → List EIdx → AM (Option EIdx)
  | e, [] => pure (some e)
  | h, a :: as => do
    match ← view h with
    | .forallE _ body _ => do
      let b ← instantiate1LiftFast fuel body a 0
      instPisOpen fuel b as
    | _ => pure none

/-! ## The two binder bodies, and the peel that uses them -/

/-- con-leche: none — which of `projRecValue`'s two `mk` lambdas
`buildBinders` runs.  con-leche passes the lambda itself; DESIGN §3.4 forbids
a closure in translated code (and this one would be monadic besides), so the
twin passes the tag the Rust would need anyway. -/
inductive ProjBinderKind where
  | motive
  | minor
  deriving DecidableEq, Repr

/-- con-leche: none — what `projRecValue`'s two `mk` lambdas capture: the
owner's type former and constructor, the projection's own codomain `R`, the
field index, and the two `PUnit` constants at the elimination level, interned
once at the entry rather than rebuilt per binder. -/
structure ProjBuild where
  T : NIdx
  ctor : NIdx
  R : EIdx
  i : Nat
  punitC : EIdx
  punitUnitC : EIdx

/-- con-leche: ConLeche/Frontend/ProjRec.lean:271-277 headIs — is `T` the head
of the owner's own carrier: the motive domain `∀ (t : T p⃗), Sort ℓ` (exactly
one binder) or the major-premise domain. -/
def headIs (fuel : Nat) (T : NIdx) (e : EIdx) : AM Bool := do
  match ← view (← getAppFn fuel e) with
  | .const n _ => pure (n == T)
  | _ => pure false

/-- con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue — the motive
body (`mkMotive` inside `projRecValue`): the owner's motive is `fun (t : T p⃗)
=> R` — `R`'s parameter references skip the new binder, its subject reference
IS the new binder — and every other one is the constant `PUnit.{ℓ}` over its
telescope. -/
def mkProjMotive (pb : ProjBuild) (fuel : Nat) (dom : EIdx) : AM (Option EIdx) := do
  let (bs, body) ← stripPisAll fuel dom
  match ← view body with
  | .sort _ =>
    match bs with
    | [(d, m)] =>
      if ← headIs fuel pb.T d then do
        let rl ← liftLooseBVarsFast fuel 1 1 pb.R
        pure (some (← internE (.lam d rl m)))
      else
        pure (some (← internE (.lam d pb.punitC m)))
    | bs => pure (some (← mkLams bs pb.punitC))
  | _ => pure none

/-- con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue — the minor
body (`mkMinor` inside `projRecValue`): the owner constructor's minor returns
field `i` of its telescope (the fields come first, then the inductive
hypotheses recursion adds); every other one returns `PUnit.unit.{ℓ}`.  The
owner's minor is the one whose codomain applies a motive to the owner
constructor. -/
def mkProjMinor (pb : ProjBuild) (fuel : Nat) (dom : EIdx) : AM (Option EIdx) := do
  let (bs, cod) ← stripPisAll fuel dom
  match (← getAppArgs fuel cod).getLast? with
  | some major =>
    if ← headIs fuel pb.ctor major then
      if pb.i < bs.length then do
        let b ← internE (.bvar (bs.length - 1 - pb.i))
        pure (some (← mkLams bs b))
      else pure none
    else pure (some (← mkLams bs pb.punitUnitC))
  | none => pure none

/-- con-leche: ConLeche/Frontend/ProjRec.lean:259-269 buildBinders — peel `k`
binders of a telescope, building one term per binder from its (progressively
instantiated) domain, and instantiating the telescope with that term before
the next binder is read.  `kind` is con-leche's `mk` argument, as the module
note explains. -/
def buildBinders (kind : ProjBinderKind) (pb : ProjBuild) (fuel : Nat) :
    Nat → EIdx → AM (Option (List EIdx × EIdx))
  | 0, e => pure (some ([], e))
  | k + 1, h => do
    match ← view h with
    | .forallE dom body _ => do
      let t? ← match kind with
        | .motive => mkProjMotive pb fuel dom
        | .minor => mkProjMinor pb fuel dom
      match t? with
      | none => pure none
      | some t => do
        let body' ← instantiate1LiftFast fuel body t 0
        match ← buildBinders kind pb fuel k body' with
        | none => pure none
        | some (ts, rest) => pure (some (t :: ts, rest))
    | _ => pure none

/-! ## The rewrite -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue — **THE
REWRITE.**  `ty`/`val` are the definition's declared type and value, `i` the
projected field, `l` the field's sort (from the artifact).  `none` = the value
is not of the projection shape (the caller keeps the declaration unchanged).

con-leche's `guard (body == .proj o.T i (.bvar 0))` is a `view` of the body
here rather than an interned comparand: exactness makes the two the same test
(`denoteE_inj`), and destructuring does not put a node in the store when the
answer is `false`. -/
def projRecValue (fuel : Nat) (o : ProjRecOwner) (l : LIdx) (ty val : EIdx)
    (i : Nat) : AM (Option EIdx) := do
  match ← stripLams (o.nP + 1) val with
  | none => pure none
  | some (lbs, body) => do
    match ← view body with
    | .proj tn bi sub =>
      match ← view sub with
      | .bvar 0 =>
        if tn != o.T || bi != i || !(i < o.nF) then pure none else do
          match ← stripPis (o.nP + 1) ty with
          | none => pure none
          | some (_, r) => do
            -- the recursor's type at the chosen elimination level; the body
            -- frame is the value's own `nP + 1` binders: parameter `k` is
            -- `bvar (nP - k)`, the subject `bvar 0`
            let ups ← internParamLevels o.lps
            let us ← internLsNode (l :: ups)
            let rty0 ← instLPFast fuel o.recLps us o.recType
            let params ← bvarRange (o.nP + 1) o.nP 0
            match ← instPisOpen fuel rty0 params with
            | none => pure none
            | some rty1 => do
              let punitH ← internName ConLeche.punitName
              let punitUH ← internName ConLeche.punitUnitName
              let lsOne ← internLsNode [l]
              let pb : ProjBuild :=
                { T := o.T, ctor := o.ctor, R := r, i := i,
                  punitC := ← internE (.const punitH lsOne),
                  punitUnitC := ← internE (.const punitUH lsOne) }
              match ← buildBinders .motive pb fuel o.numMotives rty1 with
              | none => pure none
              | some (motives, rty2) => do
                match ← buildBinders .minor pb fuel o.numMinors rty2 with
                | none => pure none
                | some (minors, rty3) => do
                  -- the major premise: the owner has no indices, so the next
                  -- binder is the subject itself
                  match ← view rty3 with
                  | .forallE majDom _ _ =>
                    if !(← headIs fuel o.T majDom) then pure none else do
                      let rc ← internE (.const o.recName us)
                      let b0 ← internE (.bvar 0)
                      let app ← mkAppN rc (params ++ motives ++ minors ++ [b0])
                      pure (some (← mkLams lbs app))
                  | _ => pure none
      | _ => pure none
    | _ => pure none
where
  /-- con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue — `o.lps.map
  Level.param`, interned: a `List.map` with a closure is DESIGN §3.4's
  explicit recursion here. -/
  internParamLevels : List NIdx → AM (List LIdx)
    | [] => pure []
    | n :: ns => do
      let h ← internLNode (.param n)
      let hs ← internParamLevels ns
      pure (h :: hs)

/-! ## Which owners the rewrite serves -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners — does any
of `ns` occur in `d`?  con-leche's inner `blockNames.any`, as an explicit
recursion (DESIGN §3.4). -/
def occursAnyOf (fuel : Nat) (ns : List NIdx) (d : EIdx) : AM Bool := do
  match ns with
  | [] => pure false
  | n :: rest => do
    if ← occursConstFast fuel n d then pure true else occursAnyOf fuel rest d

/-- con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners — does any
of `ns` occur in any binder domain of the list?  con-leche's middle
`(stripPisAll cty).1.any`, as an explicit recursion. -/
def domsMentionAny (fuel : Nat) (ns : List NIdx) :
    List (EIdx × BinderMeta) → AM Bool
  | [] => pure false
  | (d, _) :: rest => do
    if ← occursAnyOf fuel ns d then pure true else domsMentionAny fuel ns rest

/-- con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners — a block
name in a constructor's binder *domains* (its result names the owner by
definition): con-leche's outer `ctors.any`, as an explicit recursion. -/
def ctorsMentionBlock (fuel : Nat) (ns : List NIdx) :
    List (NIdx × Nat × EIdx) → AM Bool
  | [] => pure false
  | (_, _, cty) :: rest => do
    let p ← stripPisAll fuel cty
    if ← domsMentionAny fuel ns p.1 then pure true
    else ctorsMentionBlock fuel ns rest

/-- con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners — `ctors.find?
(·.1 == C)`, as an explicit recursion (DESIGN §3.4). -/
def findCtorRec (c : NIdx) : List (NIdx × Nat × EIdx) → Option (NIdx × Nat × EIdx)
  | [] => none
  | r :: rest => if r.1 == c then some r else findCtorRec c rest

/-- con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners — `recs.find?
(·.1 == T.str "rec")`, as an explicit recursion. -/
def findRecRec (n : NIdx) :
    List (NIdx × List NIdx × EIdx × Nat × Nat) →
    Option (NIdx × List NIdx × EIdx × Nat × Nat)
  | [] => none
  | r :: rest => if r.1 == n then some r else findRecRec n rest

/-- con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners — the
`filterMap` of `projRecOwners`: the officially structure-like members (one
constructor, zero indices, non-propositional) whose recursor carries an
elimination level parameter.  An explicit recursion, since `filterMap` takes a
closure; `Level.isEquiv` runs on the READ-BACK level (DESIGN §8.3 lesson 4). -/
def projRecCandidates (fuel : Nat)
    (ctors : List (NIdx × Nat × EIdx))
    (recs : List (NIdx × List NIdx × EIdx × Nat × Nat)) :
    List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool) →
    AM (List ProjRecOwner)
  | [] => pure []
  | (t, lps, tty, nP, nI, cs, _) :: rest => do
    let tail ← projRecCandidates fuel ctors recs rest
    match cs with
    | [c] =>
      if nI != 0 then pure tail else do
        match ← stripPis nP tty with
        | some (_, body) => do
          match ← view body with
          | .sort s => do
            let sP ← readLevel s
            if Level.isEquiv sP .zero == some true then pure tail else
              match findCtorRec c ctors with
              | none => pure tail
              | some (_, nF, _) => do
                let rn ← internNNode (.str t "rec")
                match findRecRec rn recs with
                | none => pure tail
                | some (rn, rlps, rty, nM, nm) =>
                  if rlps.length != lps.length + 1 then pure tail
                  else pure (⟨t, lps, nP, c, nF, rn, rlps, rty, nM, nm⟩ :: tail)
          | _ => pure tail
        | none => pure tail
    | _ => pure tail

/-- con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners — **which
block members the rewrite serves**: the officially structure-like ones of a
block the direct install does not recognise — `structPartsCore?` rejects it
(mutual, multi-constructor, indexed, shape mismatch) or it is recursive (the
export's `isRec`, or a block name occurring in a constructor's binder domains)
— and which the fixpoint route does not serve natively either.
Propositional owners and owners whose recursor carries no elimination level
parameter are left out.

`types` are `(name, levelParams, type, numParams, numIndices, ctors, isRec)`,
`ctors` `(name, numFields, type)`, `recs` `(name, levelParams, type,
numMotives, numMinors)` — the export record's own data, over handles.

The guard ORDER is the module note's deviation 3; the two recognisers are
`Arena/Inductives/`'s own twins (task #97f's dedup — until then this read the
block back and called con-leche's). -/
def projRecOwners (fuel : Nat) (block : List IConstantInfo)
    (types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool))
    (ctors : List (NIdx × Nat × EIdx))
    (recs : List (NIdx × List NIdx × EIdx × Nat × Nat)) :
    AM (List ProjRecOwner) := do
  let owners ← projRecCandidates fuel ctors recs types
  match owners with
  | [] => pure []
  | _ :: _ => do
    let blockNames := types.map (·.1)
    let recursive := types.any (·.2.2.2.2.2.2) ||
      (← ctorsMentionBlock fuel blockNames ctors)
    if (← structPartsCore? block).isSome && !recursive then pure []
    -- a block the fixpoint route takes serves its structure-like member's
    -- `.proj` nodes natively, so no rewrite (the block's DECLARED parameter
    -- count: the first type record's, which is what the parse carries into
    -- `indDecl`)
    else if (← nativeParts? ((types.head?.map (·.2.2.2.1)).getD 0) block).isSome
      then pure []
    else pure owners

end ConRon.Arena.Frontend
