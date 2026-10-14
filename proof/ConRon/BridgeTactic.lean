/-
# `ConRon.BridgeTactic` — the meta code of Theorem 1's position-free closers

Task #120.  `bridge_frame`, `bridge_fwd` and `vc_arm` (documented at their
syntax below and in `Bridge/Frame.lean`, which holds the lemmas they compose).
A library of its own, importing Lean alone, so that it can be PRECOMPILED
(`precompileModules`): the closers run on every verification condition of the
`Bridge` tier, and interpreted they cost ~4x what they cost native.  The bridge
constants they build proofs from are named with single backticks — unchecked
here, and `Bridge/Frame.lean`'s census line checks they exist.
-/
import Lean

namespace ConRon.Bridge

/-! ## 2. The search

Everything below reads a SNAPSHOT of the goal's context, taken once per goal
(and once per `bridge_fwd` round): each hypothesis with its type instantiated
and its negations unfolded (`normNeg`), its head symbol, and — for a
`∀`-hypothesis — the answer-relation-unfolded telescope's conclusion heads,
so that the searches below filter by head before they unify.  Every
unification is REDUCIBLE (`same`): a default-transparency `isDefEq` between
`denoteE st h = some ?x` and a hypothesis unfolds `denoteE` itself (measured:
a heartbeat timeout on one goal), and `backward.isDefEq.respectTransparency`
is switched back on locally for the same reason (the project sets it `false`
for Aeneas). -/

/-- con-leche: none — a denoting handle's `isSome`. -/
theorem isSome_of_eq_some {α : Type} {o : Option α} {a : α} (h : o = some a) :
    o.isSome = true := by rw [h]; rfl

/-- con-leche: none — a function's answer is unique. -/
theorem eq_of_eq_some {α : Type} {o : Option α} {a b : α} (h₁ : o = some a)
    (h₂ : o = some b) : a = b := Option.some.inj (h₁.symm.trans h₂)

open Lean Meta Elab Tactic

namespace Frame

/-- Every bridge constant this module names with a single backtick
(unchecked here); `Bridge/Frame.lean` checks each exists. -/
def usedConstants : List Name :=
  [`ConLeche.Expr,
   `ConRon.Arena.AState,
   `ConRon.Arena.AState.caches,
   `ConRon.Arena.AState.store,
   `ConRon.Arena.EStore,
   `ConRon.Arena.EStore.view,
   `ConRon.Arena.Ext,
   `ConRon.Arena.Ext.refl,
   `ConRon.Arena.Ext.trans,
   `ConRon.Arena.StoreWF,
   `ConRon.Arena.denoteE,
   `ConRon.Bridge.CacheFrame,
   `ConRon.Bridge.CacheFrame.of_eq,
   `ConRon.Bridge.CacheFrame.refl,
   `ConRon.Bridge.CacheFrame.trans,
   `ConRon.Bridge.CheckOK,
   `ConRon.Bridge.CheckOK.mono,
   `ConRon.Bridge.CheckOK.monoF,
   `ConRon.Bridge.CheckOK.state,
   `ConRon.Bridge.Ext.of_eq,
   `ConRon.Bridge.RelE,
   `ConRon.Bridge.RelEL,
   `ConRon.Bridge.RelEO,
   `ConRon.Bridge.RelL,
   `ConRon.Bridge.RelLs,
   `ConRon.Bridge.RelV,
   `ConRon.Bridge.StateOK,
   `ConRon.Bridge.StateOK.of_store,
   `ConRon.Bridge.StateOK.of_wf,
   `ConRon.Bridge.StateOK.wf,
   `ConRon.Bridge.exprTag,
   `ConRon.Bridge.isSome_denote_ext,
   `Std.Do.Triple]

/-! ## 1. The lemma registries

The lemmas the closers compose are registered by attribute where they are
declared (or, for the bridge's older modules, in `Bridge/Frame.lean`), in
declaration order:

* `@[bridge_transport]` — `(hd : F st x = some v) → (hx : Ext st st') →
  F st' x = some v`, the denotation fact FIRST (so that the store it lives at
  is fixed by a hypothesis before the `Ext` path is searched).  The head `F`
  of its conclusion makes `F … = some …` a *fact*: what the transports carry,
  what the answer relations quantify over, what `bridge_auto` identifies.
* `@[bridge_frame]` — a backward rule of the frame search, applied to every
  goal it does not close otherwise (after the call's own list).
* `@[bridge_fwd]` — a forward rule of `bridge_auto`, instantiated at what the
  context knows (the view inversions, the tag tests, the optional handle). -/

/-- A registry: `(lemma, key)` in declaration order, imports first. -/
abbrev Registry := SimplePersistentEnvExtension (Name × Name) (Array (Name × Name))

/-- Register the attribute `attr`; `key` computes an entry's key from the
lemma's type (and rejects a lemma of the wrong shape). -/
def mkRegistry (attr : Name) (descr : String) (key : Expr → MetaM Name) : IO Registry := do
  let ext ← registerSimplePersistentEnvExtension {
    name := attr
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[] }
  registerBuiltinAttribute {
    name := attr
    descr
    add := fun decl _ kind => do
      unless kind == AttributeKind.global do throwError "`@[{attr}]` is global only"
      let k ← (key (← getConstInfo decl).type).run'
      modifyEnv (ext.addEntry · (decl, k)) }
  return ext

/-- A transport lemma's key: the head of its conclusion's left side. -/
def transportKey (ty : Expr) : MetaM Name := do
  let mut c := ty
  while c.isForall do c := c.bindingBody!
  let some (_, lhs, _) := c.eq? | throwError "@[bridge_transport]: not an equation"
  let some n := lhs.getAppFn.constName? | throwError "@[bridge_transport]: no head"
  return n

initialize transportExt : Registry ←
  mkRegistry `bridge_transport "a denotation fact carried along `Ext`" transportKey
initialize frameExt : Registry ←
  mkRegistry `bridge_frame "a backward rule of the frame search" fun _ => pure .anonymous
initialize fwdExt : Registry ←
  mkRegistry `bridge_fwd "a forward rule of `bridge_auto`" fun _ => pure .anonymous

/-- The registered lemmas of `ext`. -/
def registered (env : Environment) (ext : Registry) : Array Name :=
  (ext.getState env).map (·.1)

/-- The fact heads: the keys of the transport lemmas. -/
def factHeads (env : Environment) : Array Name :=
  (transportExt.getState env).map (·.2)

/-- The answer relations whose definitions are a `∀ e, denote… = some e → …`. -/
def relNames : List Name :=
  [`ConRon.Bridge.RelE, `ConRon.Bridge.RelEL, `ConRon.Bridge.RelEO, `ConRon.Bridge.RelV, `ConRon.Bridge.RelL, `ConRon.Bridge.RelLs]

/-- Reducible definitional equality, the node identity of every search. -/
def same (a b : Expr) : MetaM Bool :=
  withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency true) <|
    withReducible (Meta.isDefEq a b)

/-- `¬ p` and `a ≠ b` spelled `p → False` and `a = b → False`, so that a
reducible match sees through them (`Not` is not reducible).  The proofs are
unchanged: the two spellings are definitionally equal. -/
def normNeg (e : Expr) : MetaM Expr := do
  unless (e.find? fun x => x.isConstOf ``Not || x.isConstOf ``Ne).isSome do return e
  Meta.transform e (pre := fun x => do
    if x.isAppOfArity ``Not 1 then
      return .visit (.forallE `h x.appArg! (mkConst ``False) .default)
    if x.isAppOfArity ``Ne 3 then
      return .visit (.forallE `h (← mkEq x.appFn!.appArg! x.appArg!) (mkConst ``False)
        .default)
    return .continue)

/-- Supply `p` for the telescope argument `a`: an unassigned metavariable is
assigned once its type and `p`'s agree up to `normNeg` (a reducible check on
the raw types would not see through `Not`), which also unifies the
telescope's earlier implicit arguments; anything else is compared.  (The
type check is not optional: assigning outright let `CheckOK.mono h` be built
with `h` at the wrong state — a kernel error, found by task #120's Memo lane.) -/
def supply (a p : Expr) : MetaM Bool := do
  if a.isMVar && !(← a.mvarId!.isAssigned) then
    let ta ← normNeg (← instantiateMVars (← inferType a))
    let tp ← normNeg (← instantiateMVars (← inferType p))
    unless ← same ta tp do return false
    a.mvarId!.assign p; return true
  same a p

/-- Is `t` an equation whose left side is a denotation (`factHeads`)? -/
def isFactShape (env : Environment) (t : Expr) : Bool :=
  match t.eq? with
  | some (_, lhs, _) => lhs.getAppFn.constName?.any ((factHeads env).contains ·)
  | none => false

/-- Is `t` one of the frame predicates `prove` decides? -/
def isFrameShape (t : Expr) : Bool :=
  [`ConRon.Arena.StoreWF, `ConRon.Bridge.StateOK, `ConRon.Bridge.CheckOK, `ConRon.Arena.Ext, `ConRon.Bridge.CacheFrame].any t.isAppOf

/-- May a hypothesis with this head be unfolded to the `∧`/`∃` it is
defined as?  Not a frame predicate (`StoreWF` is `∃ rk, EWFAt st rk`, and
`bridge_frame` wants it whole), nor any other well-formedness invariant. -/
def peelable (n : Name) : Bool :=
  ![`ConRon.Arena.StoreWF, `ConRon.Bridge.StateOK, `ConRon.Bridge.CheckOK, `ConRon.Arena.Ext, `ConRon.Bridge.CacheFrame].contains n &&
    !(n.toString.endsWith "WF") && !(n.toString.endsWith "OK")

/-- Does `e` mention a Hoare triple (a callee's spec, never a fact)? -/
def mentionsTriple (e : Expr) : Bool :=
  (e.find? fun x => x.constName?.any fun n =>
    n == `Std.Do.Triple || n.toString.endsWith ".Triple").isSome

/-- Unfold an answer relation at the head (once): one of `relNames`, or any
definition whose body is a `∀` (a walk's own relation, `ExprOps.RelEA`). -/
def unfoldRel (t : Expr) : MetaM Expr := do
  let t := t.cleanupAnnotations
  match t.getAppFn.constName? with
  | some n =>
    if relNames.contains n then
      if let some t' ← unfoldDefinition? t then return t'.headBeta
      return t
    if let some (.defnInfo _) := (← getEnv).find? n then
      if let some t' ← unfoldDefinition? t then
        let t' := t'.headBeta
        if t'.isForall then return t'
    return t
  | none => return t

/-- The heads of the left sides of the equations a `∀`-telescope concludes
(through `∧`), read syntactically. -/
partial def conclHeads (t : Expr) : List Name :=
  match t with
  | .forallE _ _ b _ => conclHeads b
  | .mdata _ b => conclHeads b
  | _ =>
    if t.isAppOfArity ``And 2 then conclHeads t.appFn!.appArg! ++ conclHeads t.appArg!
    else match t.eq? with
      | some (_, lhs, _) => match lhs.getAppFn.constName? with
        | some n => [n]
        | none => []
      | none => []

/-- The conclusion of a `∀`-telescope and its conjuncts, syntactically. -/
partial def conclSkels (t : Expr) : List Expr :=
  match t with
  | .forallE _ _ b _ => conclSkels b
  | .mdata _ b => conclSkels b
  | _ =>
    if t.isAppOfArity ``And 2 then t :: (conclSkels t.appFn!.appArg! ++ conclSkels t.appArg!)
    else [t]

/-- One hypothesis of the snapshot. -/
structure Hyp where
  pf : Expr
  ty : Expr
  /-- the answer-relation-unfolded, negation-normalised `∀` form, if any -/
  rel? : Option Expr
  /-- `conclHeads` of `rel?` -/
  heads : List Name
  /-- the conclusions of `rel?` (and their conjuncts), loose bound variables
  and all — `quickMatch` treats a bound variable as a hole -/
  concls : List Expr := []

/-- The snapshot of a goal's context. -/
structure Snap where
  hyps : Array Hyp
  /-- `Ext` edges `(src, dst, proof)` -/
  ext : Array (Expr × Expr × Expr)
  /-- `bridge_frame [l₁, …]`'s extra lemmas, tried last (their elaboration
  metavariables abstracted, so that each use instantiates afresh) -/
  lemmas : Array AbstractMVarsResult := #[]
  /-- per lemma: its telescope length and its conclusion after each length,
  syntactically (computed once per snapshot, for `quickMatch`) -/
  lemmaSkels : Array (Nat × Array Expr) := #[]
  /-- the closed goals `prove` already failed on, with the fuel it had: a
  monotonicity chain (`∀ i v, a.view i = some v → b.view i = some v`) tried
  backwards re-asks the same intermediate goals exponentially often -/
  failCache : Option (IO.Ref (Std.HashMap Expr Nat)) := none

abbrev FM := ReaderT Snap MetaM

/-- The equation-typed fields of a hypothesis `h : S a…` with `S` a `Prop`
structure, as snapshot entries `h.f : x = y`. -/
def fieldEqs (h t : Expr) : MetaM (Array Hyp) := do
  let some n := t.getAppFn.constName? | return #[]
  let env ← getEnv
  unless isStructure env n do return #[]
  let mut out := #[]
  for f in getStructureFields env n do
    let some pj := getProjFnForField? env n f | continue
    let some e ← observing? (mkAppM pj #[h]) | continue
    let ty := (← instantiateMVars (← inferType e)).cleanupAnnotations
    if ty.isAppOfArity ``Eq 3 then
      out := out.push { pf := e, ty, rel? := none, heads := [] }
  return out

/-- Take the snapshot of the current local context. -/
def snapshot (cache : Std.HashMap FVarId Hyp := {}) : MetaM Snap := do
  let mut hs := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if let some h := cache[d.fvarId]? then
      hs := hs.push h; continue
    let t ← normNeg (← instantiateMVars d.type).cleanupAnnotations
    let mut rel? := none
    let mut heads := []
    unless mentionsTriple t do
      let r ← normNeg (← unfoldRel t)
      if r.isForall then
        rel? := some r
        heads := conclHeads r
    let concls := match rel? with | some r => conclSkels r | none => []
    hs := hs.push { pf := d.toExpr, ty := t, rel?, heads, concls }
    -- a structure hypothesis's EQUATION fields (`ReadbackFrame`'s `store`,
    -- `pins`, …) are equations of the context too
    hs := hs ++ (← fieldEqs d.toExpr t)
  let mut ext := #[]
  for h in hs do
    let t := h.ty
    if t.isAppOfArity `ConRon.Arena.Ext 2 then
      ext := ext.push (t.appFn!.appArg!, t.appArg!, h.pf)
    else if let some (ty, a, b) := t.eq? then
      let ty ← whnfR ty
      if ty.isConstOf `ConRon.Arena.EStore then
        ext := ext.push (a, b, ← mkAppM `ConRon.Bridge.Ext.of_eq #[h.pf])
        ext := ext.push (b, a, ← mkAppM `ConRon.Bridge.Ext.of_eq #[← mkEqSymm h.pf])
      else if ty.isConstOf `ConRon.Arena.AState then
        let hs' ← mkCongrArg (mkConst `ConRon.Arena.AState.store) h.pf
        ext := ext.push (← mkAppM `ConRon.Arena.AState.store #[a], ← mkAppM `ConRon.Arena.AState.store #[b],
          ← mkAppM `ConRon.Bridge.Ext.of_eq #[hs'])
        ext := ext.push (← mkAppM `ConRon.Arena.AState.store #[b], ← mkAppM `ConRon.Arena.AState.store #[a],
          ← mkAppM `ConRon.Bridge.Ext.of_eq #[← mkEqSymm hs'])
  return { hyps := hs, ext }

/-- Run `k`; on `none` (or an exception) roll the metavariable context back. -/
def attemptM (k : MetaM (Option Expr)) : MetaM (Option Expr) := do
  let s ← saveState
  try
    match ← k with
    | some e => return some e
    | none => s.restore; return none
  catch _ => s.restore; return none

/-- `attemptM` in the snapshot monad. -/
def attempt (k : FM (Option Expr)) : FM (Option Expr) := fun snap => attemptM (k snap)

/-- The metavariable context, saved and restored from the snapshot monad. -/
def save : FM Meta.SavedState := (saveState : MetaM _)
def restore (s : Meta.SavedState) : FM Unit := (s.restore : MetaM Unit)

/-- A proof of `Ext a b` from the snapshot's chain, breadth first. -/
def extPath (a b : Expr) : FM (Option Expr) := do
  if ← same a b then return some (← mkAppM `ConRon.Arena.Ext.refl #[a])
  let edges := (← read).ext
  let mut frontier : Array (Expr × Expr) := #[(a, ← mkAppM `ConRon.Arena.Ext.refl #[a])]
  let mut seen : Array Expr := #[a]
  for _ in [0:edges.size] do
    let mut next := #[]
    for (n, pn) in frontier do
      for (src, dst, pe) in edges do
        unless ← same n src do continue
        if ← seen.anyM (fun x => (same dst x : MetaM Bool)) then continue
        let p ← mkAppM `ConRon.Arena.Ext.trans #[pn, pe]
        if ← same dst b then return some p
        seen := seen.push dst
        next := next.push (dst, p)
    if next.isEmpty then return none
    frontier := next
  return none

/-- Could `a` match `b` reducibly?  A syntactic over-approximation in front of
`same`: two applications of DIFFERENT constants (or of one constant at
different arities) never match at reducible transparency unless a head is
reducible, and the heads compared here (`Eq`, `denoteE`, `EStore.view`, the
`ENodeView` constructors, …) are not; a metavariable, a local or a binder
matches anything.  Three levels deep. -/
partial def quickMatch (env : Environment) (a b : Expr) (depth : Nat := 3) : Bool :=
  if depth == 0 then true else
  let a := a.cleanupAnnotations
  let b := b.cleanupAnnotations
  let rigid (n : Name) : Bool :=
    getReducibilityStatusCore env n != .reducible && !env.isProjectionFn n
  let f := a.getAppFn
  let g := b.getAppFn
  match f, g with
  | .const n _, .const m _ =>
    if n != m then !(rigid n && rigid m)
    else if a.getAppNumArgs != b.getAppNumArgs then false
    else (a.getAppArgs.zip b.getAppArgs).all fun (x, y) => quickMatch env x y (depth - 1)
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ =>
    quickMatch env d₁ d₂ (depth - 1) && quickMatch env b₁ b₂ (depth - 1)
  | .const n _, .forallE .. => !rigid n
  | .forallE .., .const n _ => !rigid n
  -- two different locals never match (no `let` locals here), nor a local
  -- and an application of a rigid constant
  | .fvar a, .fvar b => a == b
  | .fvar _, .const n _ => !rigid n
  | .const n _, .fvar _ => !rigid n
  | _, _ => true

/-- A proof of `a = b` from the snapshot's equalities of the same type,
breadth first, in either orientation. -/
def eqPath (ty a b : Expr) : FM (Option Expr) := do
  if ← same a b then return some (← mkEqRefl a)
  let env ← getEnv
  let mut edges : Array (Expr × Expr × Expr) := #[]
  for h in (← read).hyps do
    if let some (ty', u, v) := h.ty.eq? then
      if isFactShape (← getEnv) h.ty then continue
      unless ← same ty ty' do continue
      edges := edges.push (u, v, h.pf)
      edges := edges.push (v, u, ← mkEqSymm h.pf)
  if edges.isEmpty then return none
  let mut frontier : Array (Expr × Expr) := #[(a, ← mkEqRefl a)]
  let mut seen : Array Expr := #[a]
  for _ in [0:edges.size] do
    let mut next := #[]
    for (n, pn) in frontier do
      for (src, dst, pe) in edges do
        unless quickMatch env n src do continue
        unless ← same n src do continue
        if ← seen.anyM (fun x => (do
            if !quickMatch env dst x then return false
            same dst x : MetaM Bool)) then continue
        let p ← mkEqTrans pn pe
        if quickMatch env dst b then
          if ← same dst b then return some p
        seen := seen.push dst
        next := next.push (dst, p)
    if next.isEmpty then return none
    frontier := next
  return none

/-- Reduce projections of structure instances, innermost first:
`{ m with liftC := x }.inst1LC` is `m.inst1LC`.  Nothing else is unfolded (a
`whnfD` would open `HashMap.insert`). -/
partial def projNorm (e : Expr) : MetaM Expr := do
  let e := e.cleanupAnnotations
  match e.getAppFn with
  | .const n _ =>
    let some info ← getProjectionFnInfo? n | return e
    let args := e.getAppArgs
    if args.size != info.numParams + 1 then return e
    let st ← projNorm args[info.numParams]!
    let stw ← whnfR st
    if let .const cn _ := stw.getAppFn then
      if let some (.ctorInfo ctor) := (← getEnv).find? cn then
        let fields := stw.getAppArgs.extract ctor.numParams stw.getAppNumArgs
        if let some f := fields[info.i]? then return ← projNorm f
    return mkAppN e.getAppFn (args.set! info.numParams st)
  | _ => return e

/-- A FRAME term: a local, a projection of one, or a structure instance whose
fields are (`s₂.memos.inst1LC`, `{ s.caches with readLC := … }`). -/
partial def projShaped (e : Expr) : MetaM Bool := do
  let e := e.cleanupAnnotations
  if e.isFVar then return true
  -- a closed value (`∅`, a cleared table)
  if !e.hasFVar && !e.hasMVar then return true
  match e with
  | .proj _ _ x => projShaped x
  | _ =>
    let .const n _ := e.getAppFn | return false
    if let some info ← getProjectionFnInfo? n then
      let args := e.getAppArgs
      if args.size == info.numParams + 1 then return ← projShaped args[info.numParams]!
      return false
    if let some (.ctorInfo ci) := (← getEnv).find? n then
      let args := e.getAppArgs
      for x in args.extract ci.numParams args.size do
        unless ← projShaped x do return false
      return true
    return false

/-- `eqPath` through CONGRUENCE: a step rewrites, inside the current node, an
occurrence of one side of a hypothesis `u = v` of ANY type by the other, and
then reduces projections of structure instances — so that `s₂.memos = { s₁.memos with
liftC := … }` carries `s₂.memos.inst1LC = s₁.memos.inst1LC` (task #120: the
memo-table frame of every memoized walk).  Both sides are rewritten (at most six steps each) and the search meets in
the middle, so a target that itself mentions projections of later states
(`{ s₂.caches with readLC := s.caches.readLC }`) is reached too. -/
def eqPathCongr (a b : Expr) : FM (Option Expr) := do
  let mut edges : Array (Expr × Expr × Expr) := #[]
  for h in (← read).hyps do
    if let some (_, u, v) := h.ty.eq? then
      if isFactShape (← getEnv) h.ty then continue
      if u.isFVar && v.isFVar then continue
      edges := edges.push (u, v, h.pf)
      edges := edges.push (v, u, ← mkEqSymm h.pf)
  if edges.isEmpty then return none
  -- every node reachable from `x` in at most four rewrites, with `x = node`
  let reach (x : Expr) : MetaM (Array (Expr × Expr)) := do
    let mut all : Array (Expr × Expr) := #[(x, ← mkEqRefl x)]
    let mut frontier := all
    for _ in [0:6] do
      let mut next := #[]
      for (n, pn) in frontier do
        for (u, v, pe) in edges do
          unless (n.find? (· == u)).isSome do continue
          let ty ← inferType u
          -- abstracted through a local, not `.bvar 0`: an occurrence under
          -- a binder must not be captured by it
          let motive ← withLocalDeclD `z ty fun z =>
            mkLambdaFVars #[z] (n.replace fun x => if x == u then some z else none)
          let n' ← projNorm (n.replace fun x => if x == u then some v else none)
          if ← all.anyM (fun (y, _) => same n' y) then continue
          let p ← mkEqTrans pn (← mkCongrArg motive pe)
          all := all.push (n', p)
          next := next.push (n', p)
          if all.size > 128 then return all
      if next.isEmpty then return all
      frontier := next
    return all
  -- meet in the middle: a node both sides reach (the target may mention
  -- the same projections, `{ s₂.caches with readLC := s.caches.readLC }`)
  let ra ← reach a
  let rb ← reach b
  for (na, pa) in ra do
    for (nb, pb) in rb do
      if ← same na nb then
        return some (← mkEqTrans pa (← mkEqSymm pb))
  return none

/-- `quickMatch` at the top: the filter every search runs before `same`. -/
def mayMatch (ht t : Expr) : MetaM Bool := return quickMatch (← getEnv) ht t

/-- A default-transparency `isDefEq` with its own small heartbeat budget: a
pure function at symbolic arguments (`defEqList (pureFns …) …`) would
otherwise unfold until the declaration's limit (measured: Core/Walks/Owed). -/
def boundedDefEq (a b : Expr) (budget : Nat := 20000) : MetaM Bool :=
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context
      (fun c => { c with maxHeartbeats := budget * 1000 })
      (withDefault (Meta.isDefEq a b)))
    (fun _ => pure false)

/-- A CLOSED equation (no local, no metavariable) by `rfl` at default
transparency: a pin table's entry, `pinNames[PIN_NAT]? = some natName`, which
a callee's `∀ x, pinNames[i]? = some x → …` premise asks for.  Closed terms
evaluate; nothing in the context can make the check expensive. -/
def closedRfl (t : Expr) : FM (Option Expr) := do
  let some (_, a, b) := t.eq? | return none
  if t.hasFVar || t.hasMVar then return none
  let s ← (saveState : MetaM _)
  try
    if ← boundedDefEq a b then
      -- typed as the equation itself, so that `supply`'s check sees `t`
      return some (← mkExpectedTypeHint (← mkEqRefl a) t)
    s.restore; return none
  catch _ => s.restore; return none

/-- An equation whose left side is con-leche's PURE function at constructor
arguments (`(Expr.lam t b).lamPair? (Expr.lam t' b') = some (t, b, t', b')`), by
`rfl` at default transparency: the function's own clause.  No metavariable,
and the head must live in `ConLeche` (never a store read, which would unfold
the arena). -/
def pureRfl (t : Expr) : FM (Option Expr) := do
  let some (_, a, b) := t.eq? | return none
  if t.hasMVar then return none
  let some n := a.getAppFn.constName? | return none
  unless (`ConLeche).isPrefixOf n do return none
  -- at a CONSTRUCTOR argument (the clause to compute); a pure function at
  -- symbolic arguments only unfolds
  let env ← getEnv
  unless a.getAppArgs.any (fun x => x.getAppFn.constName?.any (env.isConstructor ·)) do
    return none
  let s ← (saveState : MetaM _)
  try
    if ← boundedDefEq a b then
      return some (← mkExpectedTypeHint (← mkEqRefl a) t)
    s.restore; return none
  catch _ => s.restore; return none

/-- A hypothesis whose type is `t` (reducibly, the most recent first). -/
def findHyp (t : Expr) : FM (Option Expr) := do
  let t ← normNeg t
  for h in (← read).hyps.reverse do
    unless ← mayMatch h.ty t do continue
    if let some p ← attempt (do if ← same h.ty t then return some h.pf else return none) then
      return some p
  return none

/-- A lemma's telescope length and its conclusion after each length. -/
def lemmaSkel (lr : AbstractMVarsResult) : MetaM (Nat × Array Expr) := do
  let (_, _, l) ← openAbstractMVarsResult lr
  let ty ← instantiateMVars (← inferType l)
  let (args, _, _) ← forallMetaTelescope ty
  let mut c := ty
  let mut cs : Array Expr := #[c]
  while c.isForall do
    c := c.bindingBody!
    cs := cs.push c
  return (args.size, cs)

/-- A hypothesis that is `t` up to ONE store equation of the context
(`s'.store = s.store`, the frame of a memo insert): `t` with the store
replaced, found by `findHyp`, carried back by `Eq.mpr`.  Only for a goal
that is not itself a frame predicate (those have their own chains). -/
def findHypModStoreEq (t : Expr) : FM (Option Expr) := do
  if isFrameShape t || t.hasMVar then return none
  for h in (← read).hyps do
    let some (ty, a, b) := h.ty.eq? | continue
    let ty ← whnfR ty
    unless ty.isConstOf `ConRon.Arena.EStore do continue
    for (x, y, pxy) in [(a, b, h.pf), (b, a, ← mkEqSymm h.pf)] do
      -- `t` mentions `x` (up to reducible defeq: `vcgen` writes `s.store` as
      -- a projection where a postcondition writes the projection function)
      let r ← withLocalDeclD `z ty fun z => do
        let mut hit := false
        let body ← Meta.transform t (pre := fun e => do
          if e.isFVar || e.isConst then return .continue
          unless e.isProj || e.isApp do return .continue
          if ← same e x then return .done z
          return .continue)
        if body == t then return none
        let _ := hit
        return some (← mkLambdaFVars #[z] body)
      let some lam := r | continue
      let t' := lam.beta #[y]
      let some p ← findHyp t' | continue
      -- `pxy : x = y`, `p : t[y]`; `t[x]` by rewriting back
      return some (← mkEqMPR (← mkCongrArg lam pxy) p)
  return none

mutual

/-- The frame solver: a proof of `t`, or `none` — `proveCore`'s built-in
rules, then `bridge_frame [l₁, …]`'s lemmas (for every goal shape: an `∃ F`
fuel merge, an equation a walk-specific lemma concludes). -/
partial def prove (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  let t ← instantiateMVars t
  let fc := (← read).failCache
  let key? : Option (IO.Ref (Std.HashMap Expr Nat)) := if t.hasMVar then none else fc
  if let some ref := key? then
    let m ← (ref.get : IO _)
    if let some f := m[t]? then
      if f ≥ fuel then return none
  let r ← (do
    if let some p ← attempt (proveCore fuel t) then return some p
    if (← read).lemmas.isEmpty || fuel == 0 then return none
    proveByLemmas fuel t.cleanupAnnotations : FM (Option Expr))
  if r.isNone then
    if let some ref := key? then (ref.modify (·.insert t fuel) : IO Unit)
  return r

/-- The built-in rules of `prove`.  `fuel` bounds the backward chaining
through `CheckOK.mono`, `StateOK` and the `∃` intro. -/
partial def proveCore (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  let t := (← instantiateMVars t).cleanupAnnotations
  if t.isConstOf ``True then return some (mkConst ``True.intro)
  if t.isAppOfArity ``And 2 then
    let l := t.appFn!.appArg!
    let r := t.appArg!
    let lr ← attempt do
      let some pa ← prove fuel l | return none
      let some pb ← prove fuel r | return none
      return some (mkApp4 (mkConst ``And.intro) l r pa pb)
    if let some p := lr then return some p
    -- a left conjunct with an `∃`-witness hole the right one fixes
    -- (`f x = some ?w ∧ denoteE st h = some ?w`): the right one first
    unless (← instantiateMVars l).hasExprMVar do return none
    let some pb ← prove fuel r | return none
    let some pa ← prove fuel (← instantiateMVars l) | return none
    return some (mkApp4 (mkConst ``And.intro) (← instantiateMVars l) (← instantiateMVars r) pa pb)
  if let some h ← findHyp t then return some h
  if let some h ← findHypModStoreEq t then return some h
  if fuel == 0 then return none
  -- a disjunction (a bracket's "the table was dropped or nothing moved"):
  -- either side
  if t.isAppOfArity ``Or 2 then
    let a := t.appFn!.appArg!; let b := t.appArg!
    if let some p ← attempt (prove fuel a) then
      return some (mkApp3 (mkConst ``Or.inl) a b p)
    if let some p ← attempt (prove fuel b) then
      return some (mkApp3 (mkConst ``Or.inr) a b p)
    return none
  if t.isAppOfArity `ConRon.Arena.Ext 2 then
    return ← extPath t.appFn!.appArg! t.appArg!
  if let some (ty, a, b) := t.eq? then
    -- a denotation at the current store: a fact at an earlier one, transported
    if isFactShape (← getEnv) t then return ← provedFact fuel t
    -- `o.isSome = true` from a denotation fact `o = some x`
    if b.isConstOf ``Bool.true && a.isAppOfArity ``Option.isSome 2 then
      let o := a.appArg!
      let α := a.appFn!.appArg!
      let x ← mkFreshExprMVar α
      let ft ← mkEq o (← mkAppM ``Option.some #[x])
      if isFactShape (← getEnv) ft then
        if let some ph ← attempt (provedFact fuel ft) then
          return some (← mkAppM ``ConRon.Bridge.isSome_of_eq_some #[ph])
        -- an `isSome` hypothesis at an earlier store, carried along the chain
        if o.isAppOfArity `ConRon.Arena.denoteE 2 then
          for h in (← read).hyps.reverse do
            let some (_, a', b') := h.ty.eq? | continue
            unless b'.isConstOf ``Bool.true && a'.isAppOfArity ``Option.isSome 2 do continue
            let o' := a'.appArg!
            unless o'.isAppOfArity `ConRon.Arena.denoteE 2 do continue
            unless ← same o'.appArg! o.appArg! do continue
            let some px ← extPath o'.appFn!.appArg! o.appFn!.appArg! | continue
            return some (← mkAppM `ConRon.Bridge.isSome_denote_ext #[h.pf, px])
      -- a VIEW's `isSome` (`ViewOK`'s premises): the lemmas
      return ← proveByLemmas fuel t
    if let some p ← eqPath ty a b then return some p
    -- the congruence search only for a CLOSED equation: with metavariables
    -- (a lemma premise `st.view h = some (.app ?f ?a)` no hypothesis states)
    -- every rewrite unifies, and the search is the dearest step of a frame
    if t.hasExprMVar then return none
    -- and only at a structure type (a state, its caches, a table) or between
    -- FRAME terms (projections of states, structure updates); a view read
    -- (`Option ENodeView`) is never one (measured: an `internRebuilt`
    -- "unchanged child" view goal cost 1.5 s here)
    let isStruct ← do
      let ty' ← whnfR ty
      pure (ty'.getAppFn.constName?.any (isStructure (← getEnv)))
    unless isStruct || ((← projShaped a) && (← projShaped b)) do
      if let some p ← closedRfl t then return some p
      return ← pureRfl t
    if let some p ← eqPathCongr a b then return some p
    if let some p ← closedRfl t then return some p
    return ← pureRfl t
  if t.isAppOfArity ``Exists 2 then
    let body := t.appArg!
    let α := t.appFn!.appArg!
    let x ← mkFreshExprMVar α
    let inst := (body.beta #[x]).cleanupAnnotations
    let some pa ← attempt (prove fuel inst) | return none
    -- a witness the proof did not fix (a fuel the lemma is uniform in): any
    if !(← x.mvarId!.isAssigned) then
      let some d ← attempt (do return some (← mkAppOptM ``Inhabited.default #[α, none]))
        | return none
      x.mvarId!.assign d
    return some (← mkAppOptM ``Exists.intro #[α, body, ← instantiateMVars x,
      ← instantiateMVars pa])
  match t.getAppFn.constName? with
  | some `ConRon.Bridge.StateOK =>
    let s := t.appArg!
    for h in (← read).hyps.reverse do
      let src? : Option Expr ←
        if h.ty.isAppOfArity `ConRon.Bridge.CheckOK 4 then pure (some (← mkAppM `ConRon.Bridge.CheckOK.state #[h.pf]))
        else if h.ty.isAppOfArity `ConRon.Bridge.StateOK 1 then pure (some h.pf) else pure none
      let some src := src? | do
        -- a bare `StoreWF s.store` is a `StateOK s`
        if h.ty.isAppOfArity `ConRon.Arena.StoreWF 1 then
          let he ← mkEq (← mkAppM `ConRon.Arena.AState.store #[s]) h.ty.appArg!
          if let some pe ← attempt (prove (fuel - 1) he) then
            return some (← mkAppM `ConRon.Bridge.StateOK.of_wf #[h.pf, pe])
        continue
      let s' := (← inferType src).appArg!
      let he ← mkEq (← mkAppM `ConRon.Arena.AState.store #[s]) (← mkAppM `ConRon.Arena.AState.store #[s'])
      if let some pe ← attempt (prove (fuel - 1) he) then
        return some (← mkAppM `ConRon.Bridge.StateOK.of_store #[src, pe])
    proveByLemmas fuel t
  | some `ConRon.Arena.StoreWF =>
    let st := t.appArg!
    for h in (← read).hyps.reverse do
      let src? : Option Expr ←
        if h.ty.isAppOfArity `ConRon.Bridge.CheckOK 4 then pure (some (← mkAppM `ConRon.Bridge.CheckOK.state #[h.pf]))
        else if h.ty.isAppOfArity `ConRon.Bridge.StateOK 1 then pure (some h.pf) else pure none
      let some src := src? | continue
      let s' := (← inferType src).appArg!
      if ← same (← mkAppM `ConRon.Arena.AState.store #[s']) st then
        return some (← mkAppM `ConRon.Bridge.StateOK.wf #[src])
    proveByLemmas fuel t
  | some `ConRon.Bridge.CheckOK =>
    for h in (← read).hyps.reverse do
      unless h.ty.isAppOfArity `ConRon.Bridge.CheckOK 4 do continue
      for lem in [`ConRon.Bridge.CheckOK.mono, `ConRon.Bridge.CheckOK.monoF] do
        if let some p ← attempt (applyLemma fuel lem h.pf t) then return some p
    if let some p ← proveByLemmas fuel t then return some p
    -- `CheckOK` at an earlier state by one of the lemmas (`CheckOK.ofInstLP`),
    -- then carried here
    if fuel ≥ 2 then
      let s := t.appArg!
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        unless (← whnfR d.type).isConstOf `ConRon.Arena.AState do continue
        if ← same d.toExpr s then continue
        let t' := mkApp t.appFn! d.toExpr
        let some h' ← attempt (proveByLemmas (fuel - 1) t') | continue
        for lem in [`ConRon.Bridge.CheckOK.mono, `ConRon.Bridge.CheckOK.monoF] do
          if let some p ← attempt (applyLemma (fuel - 1) lem h' t) then return some p
    return none
  | some n =>
    -- a transitive relation of the bridge (`ReadbackFrame`, …: it has
    -- `.refl` and `.trans`): a path through the context
    let env ← getEnv
    if t.getAppNumArgs ≥ 2 && env.contains (n ++ `trans) && env.contains (n ++ `refl) then
      if let some p ← relPath fuel n t then return some p
    -- a definition that unfolds to an `∃`/`∧` (`SimBOp`, `SimE`): unfolded
    if peelable n then
      if let some (.defnInfo _) := env.find? n then
        if let some t' ← unfoldDefinition? t then
          let t' := t'.headBeta
          if t'.isAppOfArity ``Exists 2 || t'.isAppOfArity ``And 2 then
            if let some p ← attempt (prove fuel t') then
              return some (← mkExpectedTypeHint p t)
    return none
  | none => return none

/-- `R a b` for a transitive `R` (with `R.refl`, `R.trans`): breadth first
over the locals of `a`'s type, an edge `R x y` being a hypothesis or one of
`bridge_frame [l₁, …]`'s lemmas (whose premises `prove` discharges). -/
partial def relPath (fuel : Nat) (n : Name) (t : Expr) : FM (Option Expr) := do
  let a := t.appFn!.appArg!
  let b := t.appArg!
  let pre := t.appFn!.appFn!
  if ← same a b then
    return ← attempt (do
      let r ← mkAppM (n ++ `refl) #[a]
      if ← same (← inferType r) t then return some r else return none)
  if fuel == 0 then return none
  let ty ← inferType a
  let mut nodes : Array Expr := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if ← same d.type ty then nodes := nodes.push d.toExpr
  unless ← nodes.anyM (same · b) do nodes := nodes.push b
  let edge (x y : Expr) : FM (Option Expr) := do
    let g := mkApp2 pre x y
    if let some h ← findHyp g then return some h
    proveByLemmas (fuel - 1) g
  let mut frontier : Array (Expr × Expr) := #[(a, ← mkAppM (n ++ `refl) #[a])]
  let mut seen : Array Expr := #[a]
  for _ in [0:nodes.size] do
    let mut next := #[]
    for (x, px) in frontier do
      for y in nodes do
        if ← seen.anyM (same · y) then continue
        let some pe ← attempt (edge x y) | continue
        let p ← mkAppM (n ++ `trans) #[px, pe]
        if ← same y b then return some p
        seen := seen.push y
        next := next.push (y, p)
    if next.isEmpty then return none
    frontier := next
  return none

/-- The goal from one of `bridge_frame [l₁, …]`'s lemmas (also the fallback of
the `StateOK`/`StoreWF`/`CheckOK` searches: a walk's own frame rule — a cache
insert, a readback frame — is passed this way): its conclusion unified with
`t`, every premise proved by `prove`. -/
partial def proveByLemmas (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  let snap ← read
  for lr in snap.lemmas, (n, skels) in snap.lemmaSkels do
    -- the lemma's conclusion may itself be a `∀` (a monotonicity chain's
    -- `∀ i v, a.view i = some v → c.view i = some v`): every telescope
    -- length, longest first
    -- a cheap syntactic filter first: the conclusion at telescope length
    -- `n - k'` must match the goal (either way round for an equation)
    let env ← getEnv
    let skelOk (c : Expr) : Bool :=
      quickMatch env c t || (match c.eq? with
        | some (ty, a, b) => quickMatch env (mkApp3 c.getAppFn ty b a) t
        | none => false)
    for k' in [0:n + 1] do
     unless skelOk (skels[n - k']?.getD t) do continue
     -- an equation also in the other orientation (`false = f x` from a lemma
     -- `f x = false`)
     for flip in [false, true] do
      let r ← attempt do
        let (_, _, l) ← openAbstractMVarsResult lr
        let (args, _, concl) ← forallMetaBoundedTelescope (← inferType l) (n - k')
        let concl ← if flip then
            match concl.eq? with
            | some (ty, a, b) => pure (mkApp3 (mkConst ``Eq [← getLevel ty]) ty b a)
            | none => pure concl
          else pure concl
        if flip && !concl.isAppOfArity ``Eq 3 then return none
        unless ← mayMatch concl t do return none
        unless ← same concl t do return none
        unless ← proveArgs fuel t.getAppFn.constName? args.toList do return none
        -- the lemma's own arguments must be determined; a metavariable of
        -- the goal's (an `∃`'s witness the lemma is uniform in) may remain
        for a in args do
          unless ← a.mvarId!.isAssigned do return none
        let p ← instantiateMVars (mkAppN l args)
        if flip then return some (← mkEqSymm p)
        return some p
      if let some p := r then return some p
  -- a `∀`-HYPOTHESIS as a lemma: a callee's postcondition that concludes a
  -- non-fact (`memo insert's ∀ f, MemoOK f … → RelE … → MemoOK f …`); its
  -- conclusion is not a denotation (those are `chainHyp`'s)
  if isFactShape (← getEnv) t then return none
  let env ← getEnv
  for h in (← read).hyps.reverse do
    let some rt := h.rel? | continue
    unless h.concls.any (quickMatch env · t) do continue
    let r ← attempt do
      let (args, _, concl) ← forallMetaTelescope rt
      if isFactShape (← getEnv) concl then return none
      unless ← mayMatch concl t do return none
      unless ← same concl t do return none
      unless ← proveArgs fuel t.getAppFn.constName? args.toList do return none
      let e ← instantiateMVars (mkAppN h.pf args)
      if e.hasExprMVar then return none
      return some e
    if let some p := r then return some p
  return none

/-- The `Prop` premises of a lemma, in order.  A premise that is neither a
frame predicate nor a denotation fact (`MemoOK f tbl st`) is matched against
EVERY hypothesis, with backtracking: the first match fixes metavariables
(here the store) that a later premise (`Ext st s`) may refute. -/
partial def proveArgs (fuel : Nat) (ghd : Option Name) (args : List Expr) : FM Bool := do
  match args with
  | [] => return true
  | a :: rest =>
    if ← a.mvarId!.isAssigned then return ← proveArgs fuel ghd rest
    let aT ← instantiateMVars (← inferType a)
    unless ← isProp aT do return ← proveArgs fuel ghd rest
    -- a closed premise: proved; one with metavariables (`CheckOK ?s`, a
    -- frame or fact premise included) branches over the hypotheses first
    if !aT.hasExprMVar then
      let some pa ← prove (fuel - 1) aT | return false
      unless ← supply a pa do return false
      return ← proveArgs fuel ghd rest
    let aTn ← normNeg aT
    for h in (← read).hyps.reverse do
      unless ← mayMatch h.ty aTn do continue
      let s ← save
      if (← same h.ty aTn) && (← supply a h.pf) then
        if ← proveArgs fuel ghd rest then return true
      restore s
    -- no hypothesis: the search itself — except for an answer-relation
    -- premise (`RelE f ?st c st' r`, through `abbrev`s: a transport lemma's,
    -- a step lemma's child), an equation (a view read `st.view h = some
    -- (.app ?f ?a)`: the search would unify it with every equation), or one
    -- of the goal's own head, with metavariables: it would re-enter the lemma
    -- list with a free store, every lemma unifying with it, at every fuel
    -- level — 27 s on one walk (task #120 wave 2).  It is matched against
    -- hypotheses only; `bridge_auto`'s forward step has put the step
    -- lemmas' answers there.
    let hd := (← whnfR aT).getAppFn.constName?
    -- (the goal's own head only near the bottom of the fuel: a chain of
    -- `SeenGrow.trans` is a search through it, a free-store lemma list is not)
    if !(isFrameShape aT || isFactShape (← getEnv) aT) &&
        ((hd == ghd && fuel < 4) || hd.any relNames.contains || hd == some ``Eq) then
      return false
    let s ← save
    if let some pa ← prove (fuel - 1) aT then
      if ← supply a pa then
        if ← proveArgs fuel ghd rest then return true
    restore s
    return false

/-- `lem h ?…` at the goal `t`: the first explicit argument is `h`, the
conclusion is unified with `t`, and every other explicit argument is proved by
`prove`. -/
partial def applyLemma (fuel : Nat) (lem : Name) (h t : Expr) : FM (Option Expr) := do
  let pf ← mkConstWithFreshMVarLevels lem
  let (args, bis, concl) ← forallMetaTelescope (← inferType pf)
  let mut first := true
  for a in args, bi in bis do
    if bi.isExplicit && first then
      first := false
      unless ← supply a h do return none
  unless ← same concl t do return none
  first := true
  for a in args, bi in bis do
    if bi.isExplicit then
      if first then first := false; continue
      let aT ← instantiateMVars (← inferType a)
      let some pa ← prove (fuel - 1) aT | return none
      unless ← supply a pa do return none
  return some (← instantiateMVars (mkAppN pf args))

/-- A fact from a universally quantified hypothesis whose conclusion (or a
conjunct of it) is the fact: the answer relations, a callee's
`∀ x, denoteE s c = some x → …` postcondition.  Its premises are facts too,
proved by `provedFact` at one less fuel. -/
partial def chainHyp (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  if fuel == 0 then return none
  let some (_, lhs, _) := t.eq? | return none
  let some hd := lhs.getAppFn.constName? | return none
  let env ← getEnv
  for h in (← read).hyps.reverse do
    let some rt := h.rel? | continue
    unless h.heads.contains hd do continue
    unless h.concls.any (quickMatch env · t) do continue
    let r ← attempt do
      let (args, _, concl) ← forallMetaTelescope rt
      -- the conclusion, or a projection of a conjunction
      let mut cands : Array (Expr × (Expr → MetaM Expr)) := #[(concl, pure)]
      let mut c := concl.cleanupAnnotations
      let mut proj : Expr → MetaM Expr := pure
      while c.isAppOfArity ``And 2 do
        let pl := proj
        cands := cands.push (c.appFn!.appArg!, fun e => do mkAppM ``And.left #[← pl e])
        proj := fun e => do mkAppM ``And.right #[← pl e]
        c := c.appArg!.cleanupAnnotations
        cands := cands.push (c, proj)
      for (cc, pj) in cands do
        unless ← mayMatch cc t do continue
        let r ← attempt do
          unless ← same cc t do return none
          for a in args do
            if ← a.mvarId!.isAssigned then continue
            let aT ← instantiateMVars (← inferType a)
            unless ← isProp aT do continue
            let some pa ← provedFact (fuel - 1) aT | return none
            unless ← supply a pa do return none
          for a in args do
            unless ← a.mvarId!.isAssigned do return none
          return some (← pj (← instantiateMVars (mkAppN h.pf args)))
        if let some p := r then return some p
      return none
    if let some p := r then return some p
  return none

/-- A denotation fact `t` — `denote… st h = some x`, `x` possibly a
metavariable — from a hypothesis, from a `∀`-hypothesis (`chainHyp`), or from
either at an earlier store and an `Ext` path. -/
partial def provedFact (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  if !isFactShape (← getEnv) t then
    if let some h ← findHyp t then return some h
    return ← closedRfl t
  if let some h ← findHyp t then return some h
  if let some h ← chainHyp fuel t then return some h
  -- the one transport lemma whose conclusion has `t`'s head
  let some (_, lhs, _) := t.eq? | return none
  let some hd := lhs.getAppFn.constName? | return none
  for (lem, k) in transportExt.getState (← getEnv) do
    unless k == hd do continue
    let r ← attempt do
      let pf ← mkConstWithFreshMVarLevels lem
      let (args, _, concl) ← forallMetaTelescope (← inferType pf)
      unless ← mayMatch concl t do return none
      unless ← same concl t do return none
      -- the last two explicit arguments are `hd` and `hx`
      let hd := args[args.size - 2]!
      let hx := args[args.size - 1]!
      let hdT ← instantiateMVars (← inferType hd)
      let some ph ← (do if let some p ← findHyp hdT then pure (some p)
                         else chainHyp fuel hdT) | return none
      unless ← supply hd ph do return none
      let hxT ← instantiateMVars (← inferType hx)
      let some px ← extPath hxT.appFn!.appArg! hxT.appArg! | return none
      unless ← supply hx px do return none
      return some (← instantiateMVars (mkAppN pf args))
    if let some p := r then return some p
  return none

end

/-- The number of top-level conjuncts. -/
partial def conjuncts (t : Expr) : MetaM Nat := do
  let t := t.cleanupAnnotations
  if t.isAppOfArity ``And 2 then
    return (← conjuncts t.appFn!.appArg!) + (← conjuncts t.appArg!)
  return 1

/-- Close `g` if the frame solver proves it; otherwise split its top-level
conjunction and close the conjuncts it can.  Returns the open goals. -/
partial def frameGoal (snap : Snap) (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  if let some p ← attemptM ((prove 6 t).run snap) then
    g.assign p
    return []
  if t.isAppOfArity ``And 2 then
    let s ← saveState
    let ga ← mkFreshExprSyntheticOpaqueMVar t.appFn!.appArg! (← g.getTag)
    let gb ← mkFreshExprSyntheticOpaqueMVar t.appArg! (← g.getTag)
    g.assign (mkApp4 (mkConst ``And.intro) t.appFn!.appArg! t.appArg! ga gb)
    let rest := (← frameGoal snap ga.mvarId!) ++ (← frameGoal snap gb.mvarId!)
    -- split only if a conjunct closed: an arm's own conjunction stays whole
    if rest.length ≥ 2 && (← conjuncts t) == rest.length then
      s.restore
      return [g]
    return rest
  return [g]

/-! ## 3. Forward: instantiate what the context already knows -/

/-- The premise with its head constant unfolded once, if that constant is a
non-reducible definition (not a frame predicate or an answer relation). -/
def unfoldHeadOnce (t : Expr) : MetaM (Option Expr) := do
  let some n := t.getAppFn.constName? | return none
  if relNames.contains n || isFrameShape t then return none
  unless (← getEnv).find? n matches some (.defnInfo _) do return none
  if getReducibilityStatusCore (← getEnv) n == .reducible then return none
  let some t' ← unfoldDefinition? t | return none
  return some t'.headBeta

/-- All the ways to instantiate the telescope `args` (premises matched
against hypotheses, facts proved by `provedFact`, frame premises by `prove`):
each a closed instance of `mk`. -/
partial def instances (args : List Expr) (mk : Expr) (acc : Array Expr) :
    FM (Array Expr) := do
  match args with
  | [] =>
    let e ← instantiateMVars mk
    if e.hasExprMVar then return acc
    return acc.push e
  | a :: rest =>
    if ← a.mvarId!.isAssigned then return ← instances rest mk acc
    let aT ← instantiateMVars (← inferType a)
    unless ← isProp aT do return ← instances rest mk acc
    if isFrameShape aT then
      let s ← save
      let some p ← attempt (prove 3 aT) | return acc
      unless ← supply a p do restore s; return acc
      let r ← instances rest mk acc
      restore s
      return r
    if isFactShape (← getEnv) aT then
      -- every hypothesis that IS the fact (an inversion lemma fires at each),
      -- else one derived fact (transported, or read off a relation)
      let mut acc := acc
      let mut direct := false
      for h in (← read).hyps.reverse do
        unless ← mayMatch h.ty aT do continue
        let s ← save
        if ← same h.ty aT then
          direct := true
          a.mvarId!.assign h.pf
          acc ← instances rest mk acc
        restore s
      if direct then return acc
      let s ← save
      let some p ← attempt (provedFact 2 aT) | return acc
      unless ← supply a p do restore s; return acc
      let r ← instances rest mk acc
      restore s
      return r
    -- a premise matched against every hypothesis: branch (as stated, and
    -- with a non-reducible head definition unfolded once: a lemma's
    -- `st.capOK w` against the program's own branch condition)
    let aT ← normNeg aT
    let aTs := #[aT] ++ (← unfoldHeadOnce aT).toArray
    let mut acc := acc
    for h in (← read).hyps.reverse do
      for aT in aTs do
        unless ← mayMatch h.ty aT do continue
        let s ← save
        if ← same h.ty aT then
          a.mvarId!.assign h.pf
          acc ← instances rest mk acc
        restore s
    -- an equation about a CLOSED term (`pinNames[PIN_NAT]? = some x`): no
    -- hypothesis states it, evaluation decides it
    if acc.isEmpty then
      if let some (_, l, r) := aT.eq? then
        if !l.hasFVar && !l.hasMVar then
          let s ← save
          let ok ← try withTransparency .default (Meta.isDefEq l r) catch _ => pure false
          if ok then
            a.mvarId!.assign (← mkEqRefl l)
            acc ← instances rest mk acc
          restore s
    -- an equation no hypothesis states, whose two sides unify (`tg = h.tag`
    -- once `tg` is fixed): `rfl`
    if acc.isEmpty then
      if let some (_, l, r) := aT.eq? then
        let s ← save
        if ← same l r then
          a.mvarId!.assign (← mkEqRefl (← instantiateMVars l))
          acc ← instances rest mk acc
        restore s
    return acc

/-- Order a telescope: matched premises first (they branch and fix the
variables), then facts, then frame premises. -/
def orderArgs (args : Array Expr) : MetaM (List Expr) := do
  let mut m := #[]; let mut f := #[]; let mut r := #[]
  for a in args do
    let aT ← instantiateMVars (← inferType a)
    if !(← isProp aT) then r := r.push a
    else if isFrameShape aT then r := r.push a
    else if isFactShape (← getEnv) aT then f := f.push a
    else m := m.push a
  return (m ++ f ++ r).toList

/-- One round: every new instance of every source, as `(proof, type)`.  A
source is a `∀`-hypothesis of the snapshot or a lemma of the list; it is
instantiated along the LONGEST prefix of its telescope that ends at a premise
and instantiates (a conclusion may itself be a `∀`: `∀ n us, e ≠ .const n us`). -/
def fwdRound (lemmas : Array Expr) (nViews : Nat) (seen : Array Expr) (deadL : Array Bool)
    (fresh? : Option (Array Hyp)) :
    FM (Array (Expr × Expr) × Array Bool) := do
  let mut out : Array (Expr × Expr) := #[]
  let mut srcs : Array (Expr × Expr × Option Nat) := #[]
  -- the telescopes are taken WITHOUT `normNeg`: a conclusion `ls ≠ []` must
  -- stay a conclusion, not become a premise `ls = []` (premises are
  -- normalised where they are matched)
  for h in (← read).hyps do
    if h.rel?.isSome then
      let r ← unfoldRel (← instantiateMVars (← inferType h.pf))
      if r.isForall then srcs := srcs.push (h.pf, r, none)
  for l in lemmas, i in [0:lemmas.size] do
    if deadL[i]?.getD false then continue
    let lt ← inferType l
    srcs := srcs.push (l, lt, some i)
  let mut deadL := deadL
  if deadL.size < lemmas.size then deadL := Array.replicate lemmas.size false
  for (h, ht, li?) in srcs do
    let s ← save
    let (args, _, _) ← forallMetaTelescope ht
    -- semi-naive: after the first round, a source fires again only if it is
    -- new itself or one of its premises could match a new hypothesis
    if let some fresh := fresh? then
      unless fresh.any (·.pf == h) do
        let mut hit := false
        for a in args do
          let aT ← instantiateMVars (← inferType a)
          unless ← isProp aT do continue
          if isFrameShape aT then continue
          let aT ← normNeg aT
          if ← fresh.anyM (fun f => (mayMatch f.ty aT : MetaM Bool)) then
            hit := true; break
        unless hit do restore s; continue
    -- the candidate prefixes: each ends at a premise block (a `Prop` binder
    -- followed by a data binder or by the conclusion), contains a fact or a
    -- matched premise, and the SHORTEST that instantiates wins — a
    -- conclusion may itself be a `∀` (`∀ n us, e ≠ .const n us`)
    let mut kinds : Array (Bool × Bool) := #[]   -- (isProp, isAnchor)
    -- the first matched premise no hypothesis can match: no prefix through
    -- it instantiates
    let mut dead := args.size
    for a in args do
      let aT ← instantiateMVars (← inferType a)
      let p ← isProp aT
      kinds := kinds.push (p, p && !isFrameShape aT)
      if p && !isFrameShape aT && !isFactShape (← getEnv) aT && !aT.isAppOf ``Eq && dead == args.size then
        let aT' ← normNeg aT
        let closedEq := match aT'.eq? with
          | some (_, l, _) => !l.hasFVar && !l.hasMVar
          | none => false
        let aTs := #[aT'] ++ (← unfoldHeadOnce aT').toArray
        unless closedEq do
          unless ← (← read).hyps.anyM (fun h => aTs.anyM (fun t => (mayMatch h.ty t : MetaM Bool))) do
            dead := kinds.size - 1
    let mut insts := #[]
    let mut anchor := false
    -- a view inversion with no anchor before its first dead premise stays
    -- dead: the views it matches come from the program, never from a round
    if let some li := li? then
      if li < nViews then
        let mut any := false
        for k in [0:dead] do
          if kinds[k]!.2 then any := true
        unless any do
          deadL := deadL.set! li true
    for k in [1:dead + 1] do
      let (p, an) := kinds[k - 1]!
      anchor := anchor || an
      unless p && anchor do continue
      if k < args.size && kinds[k]!.1 then continue
      let pre := args.extract 0 k
      insts ← instances (← orderArgs pre) (mkAppN h pre) #[]
      unless insts.isEmpty do break
    restore s
    for p in insts do
      let pt ← instantiateMVars (← inferType p)
      if (← findHyp pt).isSome then continue
      let ptn ← normNeg pt
      if ← seen.anyM (fun x => (do try same ptn x catch _ => pure false : MetaM Bool)) then continue
      if ← out.anyM (fun (_, t) => (same t ptn : MetaM Bool)) then continue
      out := out.push (p, ptn)
  return (out, deadL)

/-- `(a && b) = true`, as `(a, b)`. -/
def andTrue? (t : Expr) : Option (Expr × Expr) :=
  match t.eq? with
  | some (_, l, r) =>
    if r.isConstOf ``Bool.true && l.isAppOfArity ``and 2 then
      some (l.appFn!.appArg!, l.appArg!)
    else none
  | none => none

/-- Split conjunctions and existentials among the hypotheses `fvs`. -/
partial def peelNew (g : MVarId) (fvs : Array FVarId) : MetaM MVarId := do
  let mut g := g
  let mut todo := fvs.toList
  while !todo.isEmpty do
    let fv := todo.head!
    todo := todo.tail!
    let some d := (← g.getDecl).lctx.find? fv | continue
    let t ← instantiateMVars d.type
    let mut t := t.cleanupAnnotations
    -- a Boolean conjunction tested true (`(a.tag == t₁ && b.tag == t₂) = true`):
    -- its two tests, each a fact the tag defaults read
    -- (added beside it: a lemma may want the conjunction whole, Nat's
    -- `succ_guard`)
    if let some (a, b) := andTrue? t then
      let t' := mkAnd (← mkEq a (mkConst ``Bool.true)) (← mkEq b (mkConst ``Bool.true))
      let pf ← g.withContext (mkEqMP (mkApp2 (mkConst ``Bool.and_eq_true) a b) (mkFVar fv))
      let (fv', g') ← (← g.assert `fwd t' pf).intro1P
      g := g'
      todo := fv' :: todo
      continue
    -- a definition that unfolds to a conjunction or an existential (`SimE`,
    -- `SimOOp`, `SimBOp`, `Expr.WScoped` at a constructor): unfolded first
    if !(t.isAppOfArity ``And 2 || t.isAppOfArity ``Exists 2) then
      if let some n := t.getAppFn.constName? then
        if let some (.defnInfo _) := (← getEnv).find? n then
          unless peelable n do continue
          let t' ← g.withContext (whnfD t)
          if t'.isAppOfArity ``And 2 || t'.isAppOfArity ``Exists 2 then
            g ← g.replaceLocalDeclDefEq fv t'
            t := t'
          else
            -- a well-founded definition (`Expr.WScoped`): its equation lemmas
            let r? ← g.withContext (observing? (Meta.unfold t n))
            if let some r := r? then
              let e := r.expr.cleanupAnnotations
              if e.isAppOfArity ``And 2 || e.isAppOfArity ``Exists 2 then
                if let some (fv', g') ← g.withContext (applySimpResultToLocalDecl g fv r false) then
                  g := g'
                  todo := fv' :: todo
                  continue
    if t.isAppOfArity ``And 2 || t.isAppOfArity ``Exists 2 then
      -- (an `∃` cannot be destructured in a goal that is data: `vcgen`'s
      -- unsolved spec parameter)
      let some subs ← observing? (g.cases fv) | continue
      if subs.size != 1 then continue
      let some sub := subs[0]? | continue
      g := sub.mvarId
      let news := sub.fields.filterMap fun e => if e.isFVar then some e.fvarId! else none
      -- a field of an unfolded `∃ F, (fun F => …) F = …` carries a β-redex
      for n in news do
        if let some dn := (← g.getDecl).lctx.find? n then
          let tn ← instantiateMVars dn.type
          if (tn.find? fun x => x.isApp && x.getAppFn.isLambda).isSome then
            g ← g.replaceLocalDeclDefEq n (← Core.betaReduce tn)
      todo := news.toList ++ todo
  return g

/-- For two hypotheses `o = some a` and `o = some b` with the same
denotation `o` (`isFactShape`) and `a`, `b` different, add `a = b`. -/
def unifyFacts (g : MVarId) : MetaM MVarId := do
  let mut facts : Array (Expr × Expr × Expr) := #[]   -- (lhs, rhs value, proof)
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).cleanupAnnotations
    -- a denotation, or any other function answering `some` (`env.find? nm`)
    let some (_, l, r) := t.eq? | continue
    unless r.isAppOfArity ``Option.some 2 do continue
    unless isFactShape (← getEnv) t || l.getAppFn.isConst do continue
    facts := facts.push (l, r.appArg!, d.toExpr)
  let mut news : Array Hypothesis := #[]
  let mut snap? : Option Snap := none
  for i in [0:facts.size] do
    for j in [i+1:facts.size] do
      let (l₁, a, p₁) := facts[i]!
      let (l₂, b, p₂) := facts[j]!
      if a == b then continue
      unless l₁.getAppFn == l₂.getAppFn do continue
      if ← same a b then continue
      if ← same l₁ l₂ then
        news := news.push { userName := `fwd, type := ← mkEq a b,
                            value := ← mkAppM ``ConRon.Bridge.eq_of_eq_some #[p₁, p₂] }
        continue
      -- the same handle at two stores of one `Ext` chain: one value
      unless isFactShape (← getEnv) (← mkEq l₁ (← mkAppM ``Option.some #[a])) do continue
      let snap ← snap?.getDM snapshot
      snap? := some snap
      let t₂ ← mkEq l₂ (← mkAppM ``Option.some #[a])
      if let some q ← attemptM ((provedFact 0 t₂).run snap) then
        news := news.push { userName := `fwd, type := ← mkEq a b,
                            value := ← mkAppM ``ConRon.Bridge.eq_of_eq_some #[q, p₂] }
        continue
      let t₁ ← mkEq l₁ (← mkAppM ``Option.some #[b])
      if let some q ← attemptM ((provedFact 0 t₁).run snap) then
        news := news.push { userName := `fwd, type := ← mkEq a b,
                            value := ← mkAppM ``ConRon.Bridge.eq_of_eq_some #[p₁, q] }
  if news.isEmpty then return g
  let (fvs, g) ← g.assertHypotheses news
  -- two answers built by one constructor (`.defnInfo cv val hint` against
  -- `.defnInfo cv' val' hint'`): their fields, by injection
  let mut g := g
  for fv in fvs do
    let ok ← g.withContext do
      let t ← instantiateMVars (← fv.getType)
      let some (_, a, b) := t.eq? | return false
      let env ← getEnv
      let ctor (e : Expr) : Option Name := e.getAppFn.constName?.bind fun n =>
        match env.find? n with
        | some (.ctorInfo _) => some n
        | _ => none
      return (ctor a).isSome && ctor a == ctor b
    unless ok do continue
    match ← observing? (Meta.injection g fv) with
    | some (.subgoal g' _ _) => g := g'
    | _ => pure ()
  return g

/-- Clear what the substitutions left trivial among the hypotheses NOT in
`old`: an equation `a = a`.  (Not a repeated type: an arm may name either
copy.) -/
def clearTrivial (g : MVarId) (old : Std.HashSet FVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if old.contains d.fvarId then continue
    let triv := match t.eq? with
      | some (_, a, b) => a == b
      | none => false
    if triv then
      if let some g' ← observing? (g.clear d.fvarId) then g := g'
  return g

/-- A denotation's `isSome` hypothesis (`(denoteE st h).isSome = true`, how
the walks' preconditions state a subject) opened to its value: a fresh
`x` and `denoteE st h = some x`, so that the view inversions and the answer
relations fire on it (task #120, `bridge_auto` only).  The original stays. -/
def openIsSome (g : MVarId) (done : Std.HashSet FVarId) :
    MetaM (MVarId × Std.HashSet FVarId) := g.withContext do
  let mut news : Array Hypothesis := #[]
  let mut done := done
  for d in (← getLCtx) do
    if d.isImplementationDetail || done.contains d.fvarId then continue
    done := done.insert d.fvarId
    let t := (← instantiateMVars d.type).cleanupAnnotations
    let some (_, a, b) := t.eq? | continue
    unless b.isConstOf ``Bool.true && a.isAppOfArity ``Option.isSome 2 do continue
    let o := a.appArg!
    let x ← mkFreshExprMVar a.appFn!.appArg!
    unless isFactShape (← getEnv) (← mkEq o (← mkAppM ``Option.some #[x])) do continue
    let pf ← mkAppM ``Iff.mp #[← mkAppOptM ``Option.isSome_iff_exists
      #[a.appFn!.appArg!, o], d.toExpr]
    news := news.push { userName := `fwd, type := ← inferType pf, value := pf }
  if news.isEmpty then return (g, done)
  let (fvs, g) ← g.assertHypotheses news
  let g ← g.withContext (peelNew g fvs)
  -- the opened values' own fvars: never opened again
  let done' ← g.withContext do
    let mut acc := done
    for d in (← getLCtx) do acc := acc.insert d.fvarId
    pure acc
  return (g, done')

/-- `peelNew` at every hypothesis that is (or unfolds to) a conjunction or an
existential. -/
def peelAll (g : MVarId) (boolAnd : Bool := false) : MetaM MVarId := do
  let exs ← g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t := (← instantiateMVars d.type).cleanupAnnotations
      if t.isAppOfArity ``Exists 2 || t.isAppOfArity ``And 2 then out := out.push d.fvarId
      else if boolAnd && (andTrue? t).isSome then out := out.push d.fvarId
      -- a definition that unfolds to one (`peelNew` unfolds it)
      else if let some n := t.getAppFn.constName? then
        if (← getEnv).find? n matches some (.defnInfo _) then
          if peelable n && !(mentionsTriple t) && (← isProp t) then
            let t' ← whnfD t
            if t'.isAppOfArity ``Exists 2 || t'.isAppOfArity ``And 2 then
              out := out.push d.fvarId
            else if let some r ← observing? (Meta.unfold t n) then
              let e := r.expr.cleanupAnnotations
              if e.isAppOfArity ``Exists 2 || e.isAppOfArity ``And 2 then
                out := out.push d.fvarId
    pure out
  if exs.isEmpty then return g
  g.withContext (peelNew g exs)

/-- Substitute the equations among the hypotheses NOT in `old` that solve a
local variable (`subst_vars` restricted to what `bridge_fwd` added: on a
verification condition's context a full `substVars` is the dearest step). -/
partial def substNew (g : MVarId) (old : Std.HashSet FVarId)
    (skip : Array FVarId := #[]) : MetaM MVarId := do
  let next ← g.withContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail || old.contains d.fvarId || skip.contains d.fvarId then
        continue
      let some (_, a, b) := (← instantiateMVars d.type).cleanupAnnotations.eq? | continue
      let va := a.isFVar && !b.containsFVar a.fvarId!
      let vb := b.isFVar && !a.containsFVar b.fvarId!
      -- eliminate the NEWER variable when both sides are one (an introduced
      -- `x` identified with the statement's own `x` keeps the latter's name)
      if va && vb then
        return some (d.fvarId, old.contains a.fvarId!)
      if va then return some (d.fvarId, false)
      if vb then return some (d.fvarId, true)
    return none
  let some (fv, symm) := next | return g
  match ← observing? (substCore g fv (symm := symm)) with
  | some (_, g') => substNew g' old skip
  | none => substNew g old (skip.push fv)

/-- Reduce every `match` of the goal whose discriminants are constructors
(`match some (a, b) with …`: a postcondition `vcgen` instantiated at the
program's answer). -/
def reduceGoalMatches (g : MVarId) : MetaM MVarId := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (post := fun e => do
    match ← reduceMatcher? e with
    | .reduced e' => return .visit e'
    | _ => return .continue)
  if t' == t then return g
  g.replaceTargetDefEq t'

/-- The STORE ALIASES of a verification condition: a call that leaves the
store alone (a memo insert, a pure read) hands `s'.store = s.store`, and the
goal and the step lemmas then name one store twice.  Rewrite every
`a.store` with such an equation to its representative (the end of the
chain, followed to a fixpoint) in the target and in every other hypothesis,
so that a lemma whose source and target store coincide (a leaf, a cutoff)
unifies with the goal (task #120 wave 2, `bridge_auto` only). -/
def storeNorm (g : MVarId) : MetaM MVarId := g.withContext do
  -- the equations `a.store = b.store`, `a` and `b` locals of type `AState`
  let mut rep : Std.HashMap FVarId Expr := {}   -- a ↦ (proof of a.store = b.store)
  let mut tgt : Std.HashMap FVarId FVarId := {}
  let mut eqs : Array FVarId := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).cleanupAnnotations
    let some (_, l, r) := t.eq? | continue
    unless l.isAppOfArity `ConRon.Arena.AState.store 1 &&
      r.isAppOfArity `ConRon.Arena.AState.store 1 do continue
    let a := l.appArg!; let b := r.appArg!
    unless a.isFVar && b.isFVar && a != b do continue
    if rep.contains a.fvarId! then continue
    -- no cycles: never map a store onto one that already maps back
    let mut x := b.fvarId!
    let mut cyc := false
    for _ in [0:64] do
      if x == a.fvarId! then cyc := true; break
      match tgt[x]? with
      | some y => x := y
      | none => break
    if cyc then continue
    rep := rep.insert a.fvarId! d.toExpr
    tgt := tgt.insert a.fvarId! b.fvarId!
    eqs := eqs.push d.fvarId
  if rep.isEmpty then return g
  -- the proof that `a.store` is its representative's: follow the chain
  let mut subst : Array (Expr × Expr × Expr) := #[]   -- (a.store, rep, proof)
  for (a, pf0) in rep.toList do
    let some b0 := tgt[a]? | continue
    let mut pf := pf0
    let mut b := b0
    for _ in [0:64] do
      match rep[b]?, tgt[b]? with
      | some p, some c => pf ← mkEqTrans pf p; b := c
      | _, _ => break
    subst := subst.push (← mkAppM `ConRon.Arena.AState.store #[mkFVar a],
      ← mkAppM `ConRon.Arena.AState.store #[mkFVar b], pf)
  -- `a.store` as an application or as a primitive projection
  let storeIdx := (getStructureFields (← getEnv) `ConRon.Arena.AState).idxOf `store
  let isStore (x lhs : Expr) : Bool :=
    x == lhs || (match x with
      | .proj n i e => n == `ConRon.Arena.AState && i == storeIdx && e == lhs.appArg!
      | _ => false)
  let rewrite (e : Expr) : MetaM (Option (Expr × Expr)) := do
    let mut e := e
    let mut pf : Option Expr := none
    for (lhs, r, pr) in subst do
      unless (e.find? (isStore · lhs)).isSome do continue
      let ty ← inferType lhs
      let motive ← withLocalDeclD `z ty fun z =>
        mkLambdaFVars #[z] (e.replace fun x => if isStore x lhs then some z else none)
      let e' := e.replace fun x => if isStore x lhs then some r else none
      let step ← mkCongrArg motive pr
      let pf' ← match pf with
        | some p => mkEqTrans p step
        | none => pure step
      pf := some pf'
      e := e'
    return pf.map (e, ·)
  let mut g := g
  -- the target
  let t ← instantiateMVars (← g.getType)
  if let some (t', pf) ← rewrite t then
    g ← g.replaceTargetEq t' pf
  -- the hypotheses (not the store equations themselves): the rewritten
  -- copies appended, the originals cleared (where nothing depends on them).
  -- Appending, not `replaceLocalDecl`: that re-introduces the later locals
  -- under new ids, the store equations the proofs cite among them.
  let (news, olds) ← g.withContext do
    let mut news : Array Hypothesis := #[]
    let mut olds : Array FVarId := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if let some (_, l, r) := ty.cleanupAnnotations.eq? then
        if l.isAppOfArity `ConRon.Arena.AState.store 1 &&
            r.isAppOfArity `ConRon.Arena.AState.store 1 then continue
      unless ← isProp ty do continue
      if let some (ty', pf) ← rewrite ty then
        news := news.push { userName := d.userName, type := ty',
                            value := ← mkEqMP pf d.toExpr }
        olds := olds.push d.fvarId
    pure (news, olds)
  unless news.isEmpty do
    let (_, g') ← g.assertHypotheses news
    g ← g'.tryClearMany olds
  return g

/-- `bridge_fwd` on one goal. -/
def fwdGoal (g : MVarId) (defaults : List Name) (extra : Array Term)
    (unfoldRelGoal : Bool := false) : TacticM MVarId := do
  let mut g := g
  let old ← g.withContext do
    let mut st : Std.HashSet FVarId := {}
    for d in (← getLCtx) do st := st.insert d.fvarId
    pure st
  -- `bridge_auto`: the goal's `∀ x, denote… = some x → …` binders become
  -- hypotheses before the rounds, so that the facts take part; a known
  -- denotation is identified at the end (`unifyFacts`)
  g ← reduceGoalMatches g
  -- an answer relation the frame could not close: its `∀` form
  let tg ← g.withContext do instantiateMVars (← g.getType)
  if unfoldRelGoal && tg.getAppFn.constName?.any (relNames.contains ·) then
    let tu ← g.withContext (unfoldRel tg)
    if tu != tg then g ← g.replaceTargetDefEq (← Core.betaReduce tu)
  -- a block of data binders followed by facts about them
  -- (`∀ xs ys, denoteEList … = some xs → denoteEList … = some ys → …`)
  let block ← g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    forallTelescopeReducing t fun xs _ => do
      let mut n := 0
      while n < xs.size do
        unless ← isProp (← inferType xs[n]!) do n := n + 1; continue
        break
      if n < 2 then return 0
      let mut k := n
      while k < xs.size do
        let ty ← inferType xs[k]!
        if (← isProp ty) && isFactShape (← getEnv) ty then k := k + 1 else break
      if k == n then return 0
      -- and the lookups that follow (`env.find? nm = some ci`), which
      -- `unifyFacts` identifies with the context's own
      while k < xs.size do
        let ty ← inferType xs[k]!
        match ty.eq? with
        | some (_, _, r) => if r.isAppOfArity ``Option.some 2 then k := k + 1 else break
        | none => break
      return k
  if block > 0 then
    let (_, g') ← g.introNP block
    g := g'
  repeat
    -- `∀ x₁ … xₖ, P₁ → … → Pₘ → …` with every `Pⱼ` a denotation fact about
    -- the `xᵢ` (`∀ ea eb, denoteE st a = some ea → denoteE st b = some eb → …`)
    let n ← g.withContext do
      let t ← whnfR (← instantiateMVars (← g.getType))
      forallTelescope t fun xs _ => do
        let mut k := 0
        while k < xs.size do
          if ← isProp (← inferType xs[k]!) then break
          k := k + 1
        if k == 0 then return 0
        let mut m := 0
        while k + m < xs.size do
          let pt ← instantiateMVars (← inferType xs[k + m]!)
          unless ← isProp pt do break
          unless isFactShape (← getEnv) pt && xs[0:k].toArray.any (pt.containsFVar ·.fvarId!) do break
          m := m + 1
        return if m == 0 then 0 else k + m
    if n == 0 then break
    let (_, g') ← g.introNP n
    g := g'
  -- the program's own `∃`s (a callee's postcondition): destructured first;
  -- under `bridge_auto` also a Boolean conjunction tested true
  g ← peelAll g (boolAnd := true)
  g ← storeNorm g
  let mut opened : Std.HashSet FVarId := {}
  let (g', o) ← openIsSome g opened
  g := g'; opened := o
  let mut seen : Array Expr := #[]
  let mut deadL : Array Bool := #[]
  let mut cache : Std.HashMap FVarId Hyp := {}
  let mut first := true
  for _ in [0:8] do
    let (news, snap) ← g.withContext do
      let mut ls := #[]
      for n in defaults do ls := ls.push (← mkConstWithFreshMVarLevels n)
      for t in extra do ls := ls.push (← Tactic.elabTerm t none)
      let snap ← snapshot cache
      let fresh? := if first then none else
        some (snap.hyps.filter fun h => !h.pf.isFVar || !cache.contains h.pf.fvarId!)
      pure (← (fwdRound ls defaults.length seen deadL fresh?).run snap, snap)
    first := false
    cache := {}
    for h in snap.hyps do
      if h.pf.isFVar then cache := cache.insert h.pf.fvarId! h
    let (news, dl) := news
    deadL := dl
    if news.isEmpty then break
    -- a round that derived a VIEW (a lemma of the list read one off a
    -- projection's answer) revives the view inversions
    if news.any (fun (_, t) => match t.eq? with
        | some (_, l, _) => l.isAppOf `ConRon.Arena.EStore.view
        | none => false) then
      deadL := #[]
    seen := seen ++ news.map (·.2)
    let (fvs, g') ← g.assertHypotheses (news.map fun (p, t) =>
      { userName := `fwd, type := t, value := p })
    g ← g'.withContext (peelNew g' fvs)
    -- a round's new `isSome` facts (a binder's children) opened too
    let (g', o) ← openIsSome g opened
    g := g'; opened := o
  -- a function's answer is unique: two denotations of one handle (two
  -- callees read the same node) are one value
  g ← g.withContext (unifyFacts g)
  -- `subst_vars` once at the end (between rounds it would rename the locals
  -- `seen` mentions), and only when an equation solves a variable: on a
  -- verification condition's context `substVars` is the dearest step
  g ← substNew g old
  -- once more: an identification can make two lookups' keys equal
  -- (`nm' = nm`, then `env.find? nm = some ci'` against `… = some ci`)
  let g' ← g.withContext (unifyFacts g)
  if g' != g then g ← substNew g' old
  -- what the substitution made reducible (`Expr.WScoped d x` at `x := .app …`)
  let g' ← peelAll g
  if g' != g then g ← substNew g' old
  g ← clearTrivial g old
  return g

/-- Close `g` when it is (or unfolds to) `∃ x, P x` and a hypothesis is
`P w` for some `w` (reducibly, after β): the answer relations `SimBOp`,
`SimE`, … are such `∃ F, …`, and `bridge_fwd` peels the instance a lemma
produced into its witness and its body. -/
def closeExistsByHyp (g : MVarId) : MetaM Bool := g.withContext do
  let t ← whnfD (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``Exists 2 do return false
  let α := t.appFn!.appArg!
  let p := t.appArg!
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let s ← saveState
    let w ← mkFreshExprMVar α
    let body ← Core.betaReduce (p.beta #[w])
    let ht ← Core.betaReduce (← instantiateMVars d.type)
    if ← same ht body then
      let w ← instantiateMVars w
      unless w.hasExprMVar do
        g.assign (← mkAppOptM ``Exists.intro #[α, p, w, d.toExpr])
        return true
    s.restore
  -- no hypothesis: the body may hold by `rfl` whatever the witness (a pure
  -- function's base case, `defEqList … [] [] = .ok true` at any fuel); the
  -- check is bounded, and the witness defaults when the body ignores it
  let s ← saveState
  try
    let w ← mkFreshExprMVar α
    let body ← Core.betaReduce (p.beta #[w])
    if let some (_, l, r) := body.eq? then
      let ok ← tryCatchRuntimeEx
        (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000 })
          (withDefault (Meta.isDefEq l r)))
        (fun _ => pure false)
      if ok then
        let w ← instantiateMVars w
        let w ← if w.hasExprMVar then mkAppOptM ``Inhabited.default #[α, none] else pure w
        let body ← Core.betaReduce (p.beta #[w])
        let some (_, l, _) := body.eq? | do s.restore; return false
        g.assign (← mkAppOptM ``Exists.intro #[α, p, w, ← mkEqRefl l])
        return true
  catch _ => pure ()
  s.restore
  return false

/-- Carry the context's denotation facts to the stores the GOAL mentions: a
fact `denote… (A.store…) h = some v` is restated at every state `B` whose
`B.store` occurs in the goal, when `bridge_frame`'s search proves it there
(an `Ext`/equation path `A → B`).  What lets `simp only [f, *]` rewrite a
goal at the final state with facts the walk established earlier. -/
def transportToGoal (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut goalStores : Array Expr := #[]
  -- every `AState.store B` subterm of the goal
  let rec collect (e : Expr) (acc : Array Expr) : Array Expr :=
    if e.isAppOfArity `ConRon.Arena.AState.store 1 then
      if acc.contains e.appArg! then acc else acc.push e.appArg!
    else match e with
      | .app f a => collect a (collect f acc)
      | .lam _ t b _ | .forallE _ t b _ => collect b (collect t acc)
      | .mdata _ b => collect b acc
      | _ => acc
  goalStores := collect tgt #[]
  if goalStores.isEmpty then return g
  let snap ← snapshot
  let mut news : Array Hypothesis := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).cleanupAnnotations
    unless isFactShape (← getEnv) t do continue
    let srcs := collect t #[]
    let some a := srcs[0]? | continue
    unless srcs.size == 1 do continue
    for b in goalStores do
      if a == b then continue
      let t' := t.replace fun e =>
        if e.isAppOfArity `ConRon.Arena.AState.store 1 && e.appArg! == a then
          some (mkApp (mkConst `ConRon.Arena.AState.store) b) else none
      if (← (snap.hyps.anyM fun h => (same h.ty t' : MetaM Bool))) then continue
      if ← news.anyM (fun h => (same h.type t' : MetaM Bool)) then continue
      if let some p ← attemptM ((provedFact 1 t').run snap) then
        news := news.push { userName := `fwd, type := t', value := p }
  if news.isEmpty then return g
  let (_, g) ← g.assertHypotheses news
  return g

/-- The arguments of the `exprTag _` subterms of `t` (closed ones). -/
partial def tagSubjects (t : Expr) : Array Expr :=
  match t with
  | .app f a =>
    if t.isAppOfArity `ConRon.Bridge.exprTag 1 && !a.hasLooseBVars then #[a]
    else tagSubjects f ++ tagSubjects a
  | .forallE _ d b _ => tagSubjects d ++ tagSubjects b
  | .lam _ d b _ => tagSubjects d ++ tagSubjects b
  | .mdata _ b => tagSubjects b
  | _ => #[]

/-- The `Expr`s a case split may settle: the subjects of the tag facts
(`exprTag t …`) and of the "not this constructor" facts (`∀ …, t = C … →
False`) — a local, or a term such as `x.getAppFn` (generalized first). -/
def splitCandidates (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut out : Array Expr := #[]
  for h in (← getLCtx) do
    if h.isImplementationDetail then continue
    let t ← instantiateMVars h.type
    -- tag facts
    for e in tagSubjects t do
      unless out.contains e do out := out.push e
    -- not-this-constructor facts
    let tn ← normNeg t
    if tn.isForall then
      let mut b := tn
      while b.isForall do b := b.bindingBody!
      if b.isConstOf ``False then
        let mut c := tn
        let mut prem : Option Expr := none
        while c.isForall do
          prem := some c.bindingDomain!
          c := c.bindingBody!
        if let some pr := prem then
          if let some (ty, l, _) := pr.eq? then
            if ty.isConstOf `ConLeche.Expr && !l.hasLooseBVars && !out.contains l then
              out := out.push l
  return out

/-- Split `e` in `g`: `cases` a local; generalize a term first (in the goal
and every hypothesis that mentions it). -/
def splitOn (g : MVarId) (e : Expr) : MetaM (Array MVarId) := g.withContext do
  if e.isFVar then
    return (← g.cases e.fvarId!).map (·.mvarId)
  let mut hyps : Array FVarId := #[]
  for d in (← getLCtx) do
    unless d.isImplementationDetail do hyps := hyps.push d.fvarId
  let (_, xs, g') ← g.generalizeHyp #[{ expr := e, xName? := `e }] hyps
  let some x := xs[0]? | return #[]
  return (← g'.cases x).map (·.mvarId)

/-- A cheap gate in front of `contradiction` (which costs ~130 ms on a
verification condition's context, closing or not): is some hypothesis
`False`, an equation of two different constructors, or the negation of an
equation of one constructor with itself — after a bounded unfolding
(`(exprTag (.sort l) == ETag.app) = true` reduces to `false = true`)? -/
def contraGate (g : MVarId) : MetaM Bool := g.withContext do
  let whnfB (e : Expr) : MetaM Expr :=
    tryCatchRuntimeEx
      (withCurrHeartbeats <| withTheReader Core.Context
        (fun c => { c with maxHeartbeats := 2000 * 1000 }) (whnfD e))
      (fun _ => pure e)
  let ctorOf (e : Expr) : MetaM (Option (Name × Nat)) := do
    let e ← whnfB e
    match e.getAppFn.constName? with
    | some n =>
      if (← getEnv).isConstructor n then return some (n, e.getAppNumArgs) else
      return none
    | none => return none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).cleanupAnnotations
    if t.isConstOf ``False then return true
    if let some (_, a, b) := t.eq? then
      if let (some (ca, _), some (cb, _)) := (← ctorOf a, ← ctorOf b) then
        if ca != cb then return true
      continue
    let t ← normNeg t
    if t.isForall && t.bindingBody!.isConstOf ``False then
      if let some (_, a, b) := t.bindingDomain!.eq? then
        if let (some (ca, 0), some (cb, 0)) := (← ctorOf a, ← ctorOf b) then
          if ca == cb then return true
  return false

/-- `bridge_finish` on one goal: the cheap closers, else a case split on a
candidate `Expr` and the closers on every constructor (depth two); else the
pure functions unfolded once and the split tried again. -/
partial def finishGoal (g : MVarId) (closer : Syntax) (unfold : Option Syntax)
    (depth : Nat) : TacticM Bool := do
  let s ← saveState
  setGoals [g]
  try
    evalTactic (← `(tactic| first
      | rfl
      | assumption
      | exact True.intro))
    if (← getUnsolvedGoals).isEmpty then return true
  catch _ => pure ()
  s.restore
  if ← contraGate g then
    setGoals [g]
    try
      evalTactic (← `(tactic| contradiction))
      if (← getUnsolvedGoals).isEmpty then return true
    catch _ => pure ()
    s.restore
  -- an `∃` goal (`SimBOp`) from a hypothesis, or by `rfl` at a default
  -- witness: only at the top (its bounded default-transparency check, at every
  -- node of the split tree, added up past the heartbeat limit — Core/Walks/Owed)
  if depth == 2 then
    if ← closeExistsByHyp g then return true
  -- a conjunction: each conjunct finished on its own
  let tg ← g.withContext do whnfR (← instantiateMVars (← g.getType))
  if tg.isAppOfArity ``And 2 then
    let s ← saveState
    try
      let ga ← mkFreshExprSyntheticOpaqueMVar tg.appFn!.appArg! (← g.getTag)
      let gb ← mkFreshExprSyntheticOpaqueMVar tg.appArg! (← g.getTag)
      g.assign (mkApp4 (mkConst ``And.intro) tg.appFn!.appArg! tg.appArg! ga gb)
      if (← finishGoal ga.mvarId! closer unfold depth) &&
          (← finishGoal gb.mvarId! closer unfold depth) then return true
    catch _ => pure ()
    s.restore
  if depth == 0 then
    setGoals [g]
    try
      evalTactic closer
      if (← getUnsolvedGoals).isEmpty then return true
    catch _ => pure ()
    s.restore
    return false
  -- the pure functions unfolded first: a `match` on a term the facts settle
  if let some u := unfold then
    let s ← saveState
    try
      setGoals [g]
      evalTactic u
      match ← getUnsolvedGoals with
      | [] => return true
      | [g'] =>
        if g' != g then
          if ← finishGoal g' closer none depth then return true
      | _ => pure ()
    catch _ => pure ()
    s.restore
  for e in ← splitCandidates g do
    let s ← saveState
    try
      let subs ← splitOn g e
      if subs.isEmpty then s.restore; continue
      let mut all := true
      for sub in subs do
        unless ← finishGoal sub closer none (depth - 1) do all := false; break
      if all then return true
    catch _ => pure ()
    s.restore
  -- the full closer (`simp only [fᵢ, *]`), dearest
  setGoals [g]
  try
    evalTactic closer
    if (← getUnsolvedGoals).isEmpty then return true
  catch _ => pure ()
  s.restore
  return false

/-- The finisher's closer, as a tactic. -/
def finishCloser (fns : Array Term) : TacticM Syntax := do
  let base ← `(tactic| first
    | rfl
    | assumption
    | exact True.intro)
  if fns.isEmpty then `(tactic| first | $(⟨base⟩):tactic | trivial)
  else
  -- with the Boolean connectives at constants (a guard the walk tested
  -- arrives as `(true && b)`, `(!g) = true`)
  let bools : Array Term := #[← `(Bool.and_true), ← `(Bool.true_and), ← `(Bool.and_false),
    ← `(Bool.false_and), ← `(Bool.or_true), ← `(Bool.true_or), ← `(Bool.or_false),
    ← `(Bool.false_or), ← `(Bool.not_true), ← `(Bool.not_false), ← `(Bool.not_eq_true')]
  let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    (fns ++ bools).mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  `(tactic| first
    | $(⟨base⟩):tactic
    | (simp only [$lems,*]; done)
    | (simp only [$lems,*, *]; done)
    | trivial)

/-- The finisher on every goal: what it closes, it closes; the others are
handed back as they were. -/
def finishGoals (fns : Array Term) : TacticM Unit := do
  let closer ← finishCloser fns
  let unfold? : Option Syntax ← if fns.isEmpty then pure none else do
    let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      fns.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    pure (some (← `(tactic| simp only [$lems,*])))
  let gs ← getGoals
  let mut out := []
  for g in gs do
    if ← g.isAssigned then continue
    let s ← saveState
    let g' ← transportToGoal g
    if ← finishGoal g' closer unfold? 2 then continue
    s.restore
    out := out ++ [g]
  setGoals out

/-- The hypothesis patterns, matched depth first: each pattern's candidates
(the most recent first, distinct from the earlier patterns' choices) are
tried in turn, and a later pattern that finds nothing backtracks into the
next candidate of an earlier one (the nat lane's fix: `(hck : CheckOK _ _ _
?s) (hd : denoteE ?s.store _ = …)` failed when a CheckOK at another state
came first). -/
partial def matchPats (g : MVarId) (pats : List (Ident × Term)) (used : Array FVarId) :
    TacticM (Option (Array FVarId)) := g.withContext do
  match pats with
  | [] => return some #[]
  | (_, pat) :: rest =>
    let s0 ← saveState
    let pt ← Term.withoutErrToSorry <| Tactic.elabTerm pat none (mayPostpone := true)
    let pt ← normNeg (← instantiateMVars pt)
    for d in (← getLCtx).decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail || used.contains d.fvarId then continue
      let dt ← normNeg (← instantiateMVars d.type)
      unless ← mayMatch dt pt do continue
      let st ← saveState
      if ← withAssignableSyntheticOpaque (same dt pt) then
        if let some more ← matchPats g rest (used.push d.fvarId) then
          return some (#[d.fvarId] ++ more)
      st.restore
    s0.restore
    return none

/-- `?x` in a pattern, renamed `?_vcarm.x`: a hole of a name of its own, so
that it never meets a metavariable `vcgen` named after a program binder
(`?tbl`: "synthetic hole has already been defined"). -/
def freshHoles (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp fun s =>
    if s.getKind == ``Lean.Parser.Term.syntheticHole && s[1].isIdent then
      s.setArg 1 (mkIdent (`_vcarm ++ s[1].getId))
    else s

/-- Match the patterns against `g`'s context; on success, the goal with the
matched hypotheses (and `?x` variables) renamed. -/
def matchArm (g : MVarId) (pats : Array (Ident × Term)) (tgt? : Option Term) :
    TacticM (Except MessageData MVarId) := g.withContext do
  let pats := pats.map fun (n, p) => (n, (⟨freshHoles p⟩ : Term))
  let tgt? := tgt?.map fun t => (⟨freshHoles t⟩ : Term)
  -- a `?x` of the patterns must be a FRESH hole: forget any metavariable an
  -- earlier arm (or goal) left under that name
  let mut holes : Array Name := #[]
  for stx in (pats.map (·.2.raw)) ++ (tgt?.map (·.raw)).toArray do
    for t in stx.topDown do
      if t.isOfKind ``Lean.Parser.Term.syntheticHole && t[1].isIdent then
        holes := holes.push t[1].getId
  for n in holes do
    if let some mv := (← getMCtx).findUserName? n then mv.setUserName .anonymous
  let s ← saveState
  let before := (← getMCtx).decls
  try
    let mut renames : Array (FVarId × Name) := #[]
    -- the target first: its `?x` constrain the hypothesis patterns
    if let some tgt := tgt? then
      let tt ← Term.withoutErrToSorry <| Tactic.elabTerm tgt none (mayPostpone := true)
      unless ← withAssignableSyntheticOpaque (same (← instantiateMVars (← g.getType)) tt) do
        s.restore; return .error m!"the target is not {tgt}"
    -- the hypotheses, with backtracking: a later pattern that fails sends
    -- the search back to the next candidate of an earlier one
    let some fvs ← matchPats g pats.toList #[] | do
      -- which pattern? the first with no candidate on its own, if any
      let mut culprit : MessageData := m!"no consistent choice of hypotheses"
      for (n, pat) in pats do
        let s1 ← saveState
        let ok ← (do
          let some _ ← matchPats g [(n, pat)] #[] | pure false
          pure true)
        s1.restore
        unless ok do
          culprit := m!"no hypothesis `{n.getId} : {pat}`"
          break
      s.restore
      return .error culprit
    for (n, _) in pats, fv in fvs do
      renames := renames.push (fv, n.getId)
    -- `?x` in a pattern names the local it matched
    for (mv, n) in (← getMCtx).decls.toList.filterMap (fun (mv, d) =>
        if d.userName.isAnonymous || before.contains mv then none
        else some (mv, d.userName)) do
      if let some v ← getExprMVarAssignment? mv then
        let v ← instantiateMVars v
        if v.isFVar && !(renames.any (·.1 == v.fvarId!)) then
          if (`_vcarm).isPrefixOf n then
            renames := renames.push (v.fvarId!, n.replacePrefix `_vcarm .anonymous)
      -- forget the name, so that the next arm's `?x` is a fresh hole
      mv.setUserName .anonymous
    let mut g := g
    for (fv, n) in renames do
      g ← g.rename fv n
    return .ok g
  catch e => s.restore; return .error m!"the patterns do not elaborate: {e.toMessageData}"

end Frame

/-- con-leche: none — **the frame closer** (task #120).  On every goal:
close it if it is a frame fact — a hypothesis, an `Ext` chain, an equation
chain (`s₃.pins = s₀.pins`), `StateOK`/`StoreWF`/`CheckOK` past the chain
(`CheckOK.mono`/`.monoF`), a `CacheFrame` chain, a denotation carried along
the chain or read off an answer relation, its `isSome`, or
`∃ v, denote… = some v ∧ P v` from one; otherwise split the top-level `∧` and
close the frame conjuncts, leaving the rest.  `bridge_frame [l₁, …]` also
applies the lemmas `lᵢ` (their premises proved the same way): a walk's own
side-condition rule, `viewOK_lit`.  Deterministic meta code, no `grind`. -/
syntax (name := bridgeFrame) "bridge_frame" (" [" term,* "]")? : tactic

@[tactic bridgeFrame] def evalBridgeFrame : Tactic := fun stx => do
  let extra : Array Term :=
    if stx[1].isNone then #[] else (stx[1][1].getSepArgs.map (⟨·⟩))
  let gs ← getGoals
  let mut out := []
  for g in gs do
    if ← g.isAssigned then continue
    let snap ← g.withContext do
      let snap ← Frame.snapshot
      let mut ls := #[]
      for t in extra do ls := ls.push (← abstractMVars (← Tactic.elabTerm t none))
      for n in Frame.registered (← getEnv) Frame.frameExt do
        ls := ls.push (← abstractMVars (← mkConstWithFreshMVarLevels n))
      let sks ← ls.mapM (fun l => (Frame.lemmaSkel l : MetaM _))
      let fc ← IO.mkRef {}
      pure { snap with lemmas := ls, lemmaSkels := sks, failCache := some fc }
    out := out ++ (← Frame.frameGoal snap g)
  setGoals out

/-- con-leche: none — **the whole pipeline** (task #120):
`bridge_auto [l₁, …] unfolding [f₁, …]` is `bridge_frame [lᵢ]`,
`bridge_fwd [lᵢ]` with the goal's `∀ x, denote… = some x →` binders
introduced and the tag/`denoteEO` defaults, `bridge_frame [lᵢ]` and
`bridge_finish [fᵢ]`.  What it leaves open are the arms with real reasoning,
for `vc_arm`. -/
syntax (name := bridgeAuto) "bridge_auto" (" [" term,* "]")?
  (" unfolding" " [" term,* "]")? : tactic

/-- con-leche: none — **an arm addressed by shape** (task #120):
`vc_arm (h₁ : T₁) … (hₙ : Tₙ) => tac` runs `tac` on every open goal whose
context has hypotheses of types `T₁ … Tₙ` (elaborated in that goal, `_` holes
allowed, matched reducibly, the most recent first, distinct), each renamed
`hᵢ`; a `?x` in a pattern names the local it matched `x`.  Goals it does not
match stay open for the next `vc_arm`; it is an error if NO goal matches, so
an arm the program no longer has is reported, not skipped.
`vc_arm … ⊢ T => tac` also matches the target. -/
syntax (name := vcArm) "vc_arm" (ppSpace "(" ident " : " term ")")*
  (" ⊢ " term)? " => " tacticSeq : tactic

@[tactic vcArm] def evalVcArm : Tactic := fun stx => do
  let hs := stx[1].getArgs
  let pats : Array (Ident × Term) := hs.map fun h => (⟨h[1]⟩, ⟨h[3]⟩)
  let tgt? : Option Term := if stx[2].isNone then none else some ⟨stx[2][1]⟩
  let tac := stx[4]
  let gs ← getGoals
  let mut out := []
  let mut hit := false
  let mut why : Array MessageData := #[]
  for g in gs do
    if ← g.isAssigned then continue
    match ← Frame.matchArm g pats tgt? with
    | .error m =>
      out := out ++ [g]
      why := why.push m!"• {← g.getTag}: {m}"
    | .ok g' =>
      hit := true
      setGoals [g']
      evalTactic tac
      out := out ++ (← getUnsolvedGoals)
  unless hit do
    throwError "vc_arm: no open goal matches this arm{indentD (MessageData.joinSep why.toList "\n")}"
  setGoals out

@[tactic bridgeAuto] def evalBridgeAuto : Tactic := fun stx => do
  let ls : Array Term := if stx[1].isNone then #[] else (stx[1][1].getSepArgs.map (⟨·⟩))
  let fns : Array Term := if stx[2].isNone then #[] else (stx[2][2].getSepArgs.map (⟨·⟩))
  evalTactic (← `(tactic| bridge_frame [$ls,*]))
  let goals ← getGoals
  let mut out := []
  for g in goals do
    if ← g.isAssigned then continue
    out := out ++ [← Frame.fwdGoal g (Frame.registered (← getEnv) Frame.fwdExt).toList ls]
  setGoals out
  evalTactic (← `(tactic| bridge_frame [$ls,*]))
  Frame.finishGoals fns
  -- second pass: an answer-relation goal (`RelE f st c st' r`) the step
  -- lemmas did not close is unfolded to its `∀ e, denoteE st c = some e → …`
  -- form, and the pipeline runs once more on the introduced denotation —
  -- kept only if it closes the goal (an arm may still want the `RelE`)
  let goals ← getGoals
  let mut out2 := []
  for g in goals do
    if ← g.isAssigned then continue
    let isRel ← g.withContext do
      let t ← instantiateMVars (← g.getType)
      return t.getAppFn.constName?.any (Frame.relNames.contains ·)
    unless isRel do out2 := out2 ++ [g]; continue
    let s ← saveState
    try
      let g' ← Frame.fwdGoal g (Frame.registered (← getEnv) Frame.fwdExt).toList ls
        (unfoldRelGoal := true)
      setGoals [g']
      evalTactic (← `(tactic| bridge_frame [$ls,*]))
      Frame.finishGoals fns
      if (← getUnsolvedGoals).isEmpty then continue
    catch _ => pure ()
    s.restore
    out2 := out2 ++ [g]
  setGoals out2

end ConRon.Bridge
