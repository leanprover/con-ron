/-
# `ConRon.BridgeTactic` — the closers of Theorem 1's verification conditions

The meta code of `bridge_frame`, `bridge_auto` and `vc_arm` (DESIGN.md, tasks
#120 and #121; the idiom is at `bridge_auto`'s syntax below).  A library of its
own, importing Lean alone, so that it can be PRECOMPILED (`precompileModules`):
the closers run on every verification condition of the `Bridge` tier, and
interpreted they cost ~3× what they cost native.

The structure:

1. **Registries** — the lemmas the closers compose, by attribute
   (`@[bridge_transport]`, `@[bridge_frame]`, `@[bridge_fwd]`).
2. **Matching** — every unification is REDUCIBLE (`same`), behind a syntactic
   filter (`quickMatch`).
3. **The snapshot** — a goal's hypotheses, read once.
4. **Paths** — a goal `R a b` for a preorder `R` (`Eq`, `Ext`, `CacheFrame`,
   …) as a chain of the context's steps; equations also by congruence.
5. **The backward search** `prove` — connectives, hypotheses, paths, facts
   (a denotation, carried along `Ext` or read off a `∀`-hypothesis), rules
   (the lemmas and the `∀`-hypotheses, premises proved recursively),
   evaluation.  `bridge_frame` is this search on every goal.
6. **The forward step** — every `∀`-hypothesis and `@[bridge_fwd]` lemma
   instantiated at what the context knows, saturated.
7. **The finisher** — `rfl`, `contradiction`, a case split, `simp only`.
8. **`vc_arm`** — an arm addressed by the shape of its hypotheses.

The bridge constants named with single backticks (`usedConstants`) are
unchecked here; `Bridge/Frame.lean` checks they exist.
-/
import Lean

namespace ConRon.Bridge

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
   `ConRon.Arena.AState.store,
   `ConRon.Arena.EStore,
   `ConRon.Arena.EStore.view,
   `ConRon.Arena.Ext,
   `ConRon.Arena.StoreWF,
   `ConRon.Arena.denoteE,
   `ConRon.Bridge.CacheFrame,
   `ConRon.Bridge.CheckOK,
   `ConRon.Bridge.StateOK,
   `ConRon.Bridge.exprTag,
   `Std.Do.Triple]

/-! ## 1. The registries

The lemmas the closers compose are registered by attribute where they are
declared (for the bridge's older modules, which do not import this library,
in `Bridge/Frame.lean`), in declaration order:

* `@[bridge_transport]` — `(hd : F st x = some v) → (hx : Ext st st') →
  F st' x = some v`, the fact FIRST (so that the store it lives at is fixed by
  a hypothesis before the `Ext` path is searched).  The head `F` of its
  conclusion makes `F … = some …` a FACT: what the transports carry, what the
  answer relations quantify over, what `bridge_auto` identifies.
* `@[bridge_frame]` — a backward rule of `prove`, after the call's own list.
* `@[bridge_fwd]` — a forward rule of `bridge_auto` (the view inversions, the
  tag tests, the optional handle). -/

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
  mkRegistry `bridge_transport "a fact carried along `Ext`" transportKey
initialize frameExt : Registry ←
  mkRegistry `bridge_frame "a backward rule of the frame search" fun _ => pure .anonymous
initialize fwdExt : Registry ←
  mkRegistry `bridge_fwd "a forward rule of `bridge_auto`" fun _ => pure .anonymous

initialize registerTraceClass `bridge

/-- The registered lemmas of `ext`. -/
def registered (env : Environment) (ext : Registry) : Array Name :=
  (ext.getState env).map (·.1)

/-- Is `t` a FACT — an equation whose left side has a transport lemma's head
(`denoteE st h = some e`, `denoteN …`, `denoteEList …`, …)? -/
def isFactShape (env : Environment) (t : Expr) : Bool :=
  match t.eq? with
  | some (_, lhs, _) =>
    lhs.getAppFn.constName?.any fun n => (transportExt.getState env).any (·.2 == n)
  | none => false

/-- Is `t` a frame predicate — the state invariants and the store and cache
frames (a premise of this shape is searched for, never guessed)? -/
def isFrameShape (t : Expr) : Bool :=
  [`ConRon.Arena.StoreWF, `ConRon.Bridge.StateOK, `ConRon.Bridge.CheckOK, `ConRon.Arena.Ext,
   `ConRon.Bridge.CacheFrame].any t.isAppOf

/-- May a hypothesis with this head be unfolded to the `∧`/`∃` it is
defined as?  Not a frame predicate (`StoreWF` is `∃ rk, EWFAt st rk`, wanted
whole), nor any other well-formedness invariant (`…WF`, `…OK`). -/
def peelable (n : Name) : Bool :=
  ![`ConRon.Arena.StoreWF, `ConRon.Bridge.StateOK, `ConRon.Bridge.CheckOK, `ConRon.Arena.Ext,
    `ConRon.Bridge.CacheFrame].contains n &&
    !(n.toString.endsWith "WF") && !(n.toString.endsWith "OK")

/-- Does `e` mention a Hoare triple (a callee's spec, never a fact)? -/
def mentionsTriple (e : Expr) : Bool :=
  (e.find? fun x => x.constName?.any fun n =>
    n == `Std.Do.Triple || n.toString.endsWith ".Triple").isSome

/-- Is `n` an ANSWER RELATION — a definition whose body is `∀ x…, F … = some x
→ … → a = b`: for every denotation of the input (its first premise is a fact),
an equation about the answer (`RelE`, `RelEL`, `RelV`, `ExprOps.RelEA`, …)?
Read off the definition, syntactically. -/
def isAnswerRel (env : Environment) (n : Name) : Bool := Id.run do
  let some (.defnInfo d) := env.find? n | return false
  let mut b := d.value
  while b.isLambda do b := b.bindingBody!
  let mut factPremise := false
  while b.isForall do
    let dom := b.bindingDomain!
    if !factPremise && dom.isAppOfArity ``Eq 3 then
      unless isFactShape env dom do return false
      factPremise := true
    b := b.bindingBody!
  return factPremise && b.isAppOfArity ``Eq 3

/-- Unfold a definition whose body is a `∀` at the head (once): an answer
relation, a walk's own `∀` relation. -/
def unfoldRel (t : Expr) : MetaM Expr := do
  let t := t.cleanupAnnotations
  let some n := t.getAppFn.constName? | return t
  unless (← getEnv).find? n matches some (.defnInfo _) do return t
  let some t' ← unfoldDefinition? t | return t
  let t' := t'.headBeta
  return if t'.isForall then t' else t

/-! ## 2. Matching -/

/-- Reducible definitional equality, the node identity of every search.  A
default-transparency `isDefEq` between `denoteE st h = some ?x` and a
hypothesis unfolds `denoteE` itself (a heartbeat timeout on one goal), and
`backward.isDefEq.respectTransparency` (which the project sets `false` for
Aeneas) is switched back on for the same reason. -/
def same (a b : Expr) : MetaM Bool :=
  withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency true) <|
    withReducible (Meta.isDefEq a b)

/-- `¬ p` and `a ≠ b` spelled `p → False` and `a = b → False`, so that a
reducible match sees through them (`Not` is not reducible).  The two spellings
are definitionally equal, so proofs are unchanged. -/
def normNeg (e : Expr) : MetaM Expr := do
  unless (e.find? fun x => x.isConstOf ``Not || x.isConstOf ``Ne).isSome do return e
  Meta.transform e (pre := fun x => do
    if x.isAppOfArity ``Not 1 then
      return .visit (.forallE `h x.appArg! (mkConst ``False) .default)
    if x.isAppOfArity ``Ne 3 then
      return .visit (.forallE `h (← mkEq x.appFn!.appArg! x.appArg!) (mkConst ``False)
        .default)
    return .continue)

/-- Could `a` match `b` reducibly?  A syntactic over-approximation in front of
`same`: two applications of DIFFERENT constants (or of one constant at
different arities) never match at reducible transparency unless a head is
reducible or a projection; a metavariable or a binder matches anything, two
different locals never.  Three levels deep. -/
partial def quickMatch (env : Environment) (a b : Expr) (depth : Nat := 3) : Bool :=
  if depth == 0 then true else
  let a := a.cleanupAnnotations
  let b := b.cleanupAnnotations
  let rigid (n : Name) : Bool :=
    getReducibilityStatusCore env n != .reducible && !env.isProjectionFn n
  match a.getAppFn, b.getAppFn with
  | .const n _, .const m _ =>
    if n != m then !(rigid n && rigid m)
    else if a.getAppNumArgs != b.getAppNumArgs then false
    else (a.getAppArgs.zip b.getAppArgs).all fun (x, y) => quickMatch env x y (depth - 1)
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ =>
    quickMatch env d₁ d₂ (depth - 1) && quickMatch env b₁ b₂ (depth - 1)
  | .const n _, .forallE .. => !rigid n
  | .forallE .., .const n _ => !rigid n
  | .fvar a, .fvar b => a == b
  | .fvar _, .const n _ => !rigid n
  | .const n _, .fvar _ => !rigid n
  | _, _ => true

/-- `quickMatch` at the top: the filter every search runs before `same`. -/
def mayMatch (ht t : Expr) : MetaM Bool := return quickMatch (← getEnv) ht t

/-- Supply `p` for the telescope argument `a`: an unassigned metavariable is
assigned once its type and `p`'s agree up to `normNeg`, which also unifies
the telescope's earlier implicit arguments; anything else is compared.  (The
type check is not optional: assigning outright built `CheckOK.mono h` with
`h` at the wrong state — a kernel error.) -/
def supply (a p : Expr) : MetaM Bool := do
  if a.isMVar && !(← a.mvarId!.isAssigned) then
    let ta ← normNeg (← instantiateMVars (← inferType a))
    let tp ← normNeg (← instantiateMVars (← inferType p))
    unless ← same ta tp do return false
    a.mvarId!.assign p; return true
  same a p

/-- Run `k`; on `none` (or an exception) roll the metavariable context back. -/
def attemptM (k : MetaM (Option Expr)) : MetaM (Option Expr) := do
  let s ← saveState
  try
    match ← k with
    | some e => return some e
    | none => s.restore; return none
  catch _ => s.restore; return none

/-- A default-transparency `isDefEq` with its own heartbeat budget: a pure
function at symbolic arguments would otherwise unfold until the declaration's
limit. -/
def boundedDefEq (a b : Expr) (budget : Nat := 20000) : MetaM Bool :=
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context
      (fun c => { c with maxHeartbeats := budget * 1000 })
      (withDefault (Meta.isDefEq a b)))
    (fun _ => pure false)

/-- An equation decided by EVALUATION, as `rfl` within `boundedDefEq`: a
closed one (a pin table's entry, `pinNames[PIN_NAT]? = some natName`), or one
whose left side is a function of con-leche's pure checker at a constructor
(its defining clause, `(Expr.lam t b).lamPair? (.lam t' b') = some …`).  Never
an arena function: those read the store. -/
def rflBounded (t : Expr) : MetaM (Option Expr) := do
  let some (_, a, b) := t.eq? | return none
  if t.hasMVar then return none
  if t.hasFVar then
    let some n := a.getAppFn.constName? | return none
    unless (`ConLeche).isPrefixOf n do return none
    let env ← getEnv
    unless a.getAppArgs.any (·.getAppFn.constName?.any env.isConstructor) do return none
  attemptM do
    unless ← boundedDefEq a b do return none
    -- typed as the equation itself, so that `supply`'s check sees `t`
    return some (← mkExpectedTypeHint (← mkEqRefl a) t)

/-! ## 3. The snapshot

A goal's hypotheses, read once per goal (and once per forward round): each
with its type instantiated and its negations unfolded, and — for a
`∀`-hypothesis (after unfolding an answer relation) — its telescope and the
skeletons of its conclusion and conjuncts, so that the searches filter before
they unify. -/

/-- One hypothesis of the snapshot. -/
structure Hyp where
  /-- the local it is (or is a field of) -/
  src : FVarId
  pf : Expr
  ty : Expr
  /-- the relation-unfolded, negation-normalised `∀` form, if any -/
  rel? : Option Expr := none
  /-- the conclusions of `rel?` (and their conjuncts), loose bound variables
  and all — `quickMatch` treats a bound variable as a hole -/
  concls : List Expr := []

/-- The snapshot of a goal's context. -/
structure Snap where
  hyps : Array Hyp
  /-- the rules (`bridge_frame [l₁, …]`'s list, then `@[bridge_frame]`), their
  elaboration metavariables abstracted so that each use instantiates afresh -/
  lemmas : Array AbstractMVarsResult := #[]
  /-- per rule: its telescope length and its conclusion after each length,
  syntactically (for `quickMatch`) -/
  lemmaSkels : Array (Nat × Array Expr) := #[]
  /-- the goals `prove` already failed on (metavariables abstracted), with the
  fuel it had: a monotonicity chain tried backwards re-asks the same goals
  exponentially often -/
  failCache : Option (IO.Ref (Std.HashMap Expr Nat)) := none

abbrev FM := ReaderT Snap MetaM

/-- `attemptM` in the snapshot monad. -/
def attempt (k : FM (Option Expr)) : FM (Option Expr) := fun snap => attemptM (k snap)

/-- The metavariable context, saved and restored from the snapshot monad. -/
def save : FM Meta.SavedState := (saveState : MetaM _)
def restore (s : Meta.SavedState) : FM Unit := (s.restore : MetaM Unit)

/-- The conclusion of a `∀`-telescope and its conjuncts, syntactically. -/
partial def conclSkels (t : Expr) : List Expr :=
  match t with
  | .forallE _ _ b _ => conclSkels b
  | .mdata _ b => conclSkels b
  | _ =>
    if t.isAppOfArity ``And 2 then t :: (conclSkels t.appFn!.appArg! ++ conclSkels t.appArg!)
    else [t]

/-- The fields of a hypothesis `h : S a…` with `S` a `Prop` structure that are
equations or frame predicates (`ReadbackFrame`'s `store`, `CheckOK`'s `state`
and in turn its `wf`), as snapshot entries: hypotheses too. -/
partial def structFields (src : FVarId) (h t : Expr) : MetaM (Array Hyp) := do
  let some n := t.getAppFn.constName? | return #[]
  let env ← getEnv
  unless isStructure env n do return #[]
  let mut out := #[]
  for f in getStructureFields env n do
    let some pj := getProjFnForField? env n f | continue
    let some e ← observing? (mkAppM pj #[h]) | continue
    let ty := (← instantiateMVars (← inferType e)).cleanupAnnotations
    if ty.isAppOfArity ``Eq 3 then out := out.push { src, pf := e, ty }
    else if isFrameShape ty then
      out := out.push { src, pf := e, ty }
      out := out ++ (← structFields src e ty)
  return out

/-- Take the snapshot of the current local context (`cache`: entries of an
earlier snapshot of the same goal, by local). -/
def snapshot (cache : Std.HashMap FVarId (Array Hyp) := {}) : MetaM Snap := do
  let mut hs := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if let some h := cache[d.fvarId]? then
      hs := hs ++ h; continue
    let t ← normNeg (← instantiateMVars d.type).cleanupAnnotations
    let mut rel? := none
    unless mentionsTriple t do
      let r ← normNeg (← unfoldRel t)
      if r.isForall then rel? := some r
    hs := hs.push { src := d.fvarId, pf := d.toExpr, ty := t, rel?,
                    concls := (rel?.map conclSkels).getD [] }
    hs := hs ++ (← structFields d.fvarId d.toExpr t)
  return { hyps := hs }

/-- A hypothesis whose type is `t` (reducibly, the most recent first). -/
def findHyp (t : Expr) : FM (Option Expr) := do
  let t ← normNeg t
  for h in (← read).hyps.reverse do
    unless ← mayMatch h.ty t do continue
    if let some p ← attempt (do if ← same h.ty t then return some h.pf else return none) then
      return some p
  return none

/-- A hypothesis that is `t` up to ONE store equation of the context
(`s'.store = s.store`, the frame of a memo insert): `t` with the store
replaced, found by `findHyp`, carried back by `Eq.mpr`.  Only for a goal that
is not itself a frame predicate (those have their own chains). -/
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
        let body ← Meta.transform t (pre := fun e => do
          if e.isFVar || e.isConst then return .continue
          unless e.isProj || e.isApp do return .continue
          if ← same e x then return .done z
          return .continue)
        if body == t then return none
        return some (← mkLambdaFVars #[z] body)
      let some lam := r | continue
      let some p ← findHyp (lam.beta #[y]) | continue
      return some (← mkEqMPR (← mkCongrArg lam pxy) p)
  return none

/-! ## 4. Paths

A goal `R a b` with `R` a PREORDER — `Eq` at some type, or a relation with
`R.refl` and `R.trans` lemmas (`Ext`, `CacheFrame`, `ReadbackFrame`, …) — is a
chain of the context's steps, found breadth first: a hypothesis `R x y`; an
equation `x = y` at `R`'s carrier, read as a step both ways; for `Eq` every
equation both ways.  An equation between structure terms is also found by
CONGRUENCE (`eqPathCongr`). -/

/-- `t` as `(R, R-prefix, a, b)` when `R` is a preorder. -/
def preorder? (t : Expr) : MetaM (Option (Name × Expr × Expr × Expr)) := do
  let t := t.cleanupAnnotations
  let some n := t.getAppFn.constName? | return none
  unless t.getAppNumArgs ≥ 2 do return none
  let env ← getEnv
  unless n == ``Eq || (env.contains (n ++ `refl) && env.contains (n ++ `trans)) do
    return none
  return some (n, t.appFn!.appFn!, t.appFn!.appArg!, t.appArg!)

def preRefl (n : Name) (a : Expr) : MetaM Expr :=
  if n == ``Eq then mkEqRefl a else mkAppM (n ++ `refl) #[a]

def preTrans (n : Name) (p q : Expr) : MetaM Expr :=
  if n == ``Eq then mkEqTrans p q else mkAppM (n ++ `trans) #[p, q]

/-- The steps of `R` (prefix `pre`, carrier `ty`) the snapshot states, as
`(source, target, proof)`. -/
def steps (n : Name) (pre ty : Expr) : FM (Array (Expr × Expr × Expr)) := do
  let env ← getEnv
  let mut out := #[]
  for h in (← read).hyps do
    let t := h.ty
    if let some (ty', u, v) := t.eq? then
      if isFactShape env t then continue
      unless ← same ty ty' do continue
      if n == ``Eq then
        out := out.push (u, v, h.pf) |>.push (v, u, ← mkEqSymm h.pf)
      else
        -- `x = y` as the step `R x y`: `refl x` rewritten
        let step (x pxy : Expr) : MetaM Expr := do
          let motive ← withLocalDeclD `z ty fun z => mkLambdaFVars #[z] (mkApp2 pre x z)
          mkEqNDRec motive (← preRefl n x) pxy
        out := out.push (u, v, ← step u h.pf) |>.push (v, u, ← step v (← mkEqSymm h.pf))
    else if n != ``Eq && t.isAppOf n && t.getAppNumArgs == pre.getAppNumArgs + 2 then
      unless ← same t.appFn!.appFn! pre do continue
      out := out.push (t.appFn!.appArg!, t.appArg!, h.pf)
  return out

/-- Breadth first from `a` (its chain `pa`) to `b`: `next seen x px` lists the
nodes one step from `x` that are not `seen`, each with its chain from `a`. -/
def bfs (a pa b : Expr) (bound : Nat)
    (next : Array Expr → Expr → Expr → FM (Array (Expr × Expr))) : FM (Option Expr) := do
  let env ← getEnv
  let mut frontier : Array (Expr × Expr) := #[(a, pa)]
  let mut seen : Array Expr := #[a]
  for _ in [0:bound] do
    let mut layer := #[]
    for (x, px) in frontier do
      for (y, py) in ← next seen x px do
        if ← seen.anyM (fun z => do
            if !quickMatch env y z then return false
            same y z) then continue
        if quickMatch env y b then
          if ← same y b then return some py
        seen := seen.push y
        layer := layer.push (y, py)
    if layer.isEmpty then return none
    frontier := layer
  return none

/-- A chain `R a b` of the snapshot's steps. -/
def path (n : Name) (pre a b : Expr) : FM (Option Expr) := do
  if ← same a b then return some (← preRefl n a)
  let edges ← steps n pre (← inferType a)
  if edges.isEmpty then return none
  let env ← getEnv
  bfs a (← preRefl n a) b edges.size fun _ x px => do
    let mut out := #[]
    for (src, dst, pe) in edges do
      unless quickMatch env x src do continue
      unless ← same x src do continue
      out := out.push (dst, ← preTrans n px pe)
    return out

/-- Reduce projections of structure instances, innermost first:
`{ m with liftC := x }.inst1LC` is `m.inst1LC`.  Nothing else is unfolded (a
`whnfD` would open `HashMap.insert`). -/
partial def projNorm (e : Expr) : MetaM Expr := do
  let e := e.cleanupAnnotations
  let .const n _ := e.getAppFn | return e
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

/-- A FRAME term: a local, a closed value, a projection of one, or a structure
instance whose fields are (`s₂.memos.inst1LC`, `{ s.caches with readLC := … }`). -/
partial def projShaped (e : Expr) : MetaM Bool := do
  let e := e.cleanupAnnotations
  if e.isFVar || (!e.hasFVar && !e.hasMVar) then return true
  match e with
  | .proj _ _ x => projShaped x
  | _ =>
    let .const n _ := e.getAppFn | return false
    let args := e.getAppArgs
    if let some info ← getProjectionFnInfo? n then
      return args.size == info.numParams + 1 && (← projShaped args[info.numParams]!)
    if let some (.ctorInfo ci) := (← getEnv).find? n then
      return ← (args.extract ci.numParams args.size).allM projShaped
    return false

/-- An equation `a = b` by CONGRUENCE: a step rewrites, inside the current
term, an occurrence of one side of an equation of the context (of any type) by
the other, then reduces projections of structure instances — so that
`s₂.memos = { s₁.memos with liftC := … }` carries `s₂.memos.inst1LC =
s₁.memos.inst1LC` (the memo-table frame of every memoized walk).  Both sides
are rewritten (at most six steps, 128 terms each) and the search meets in the
middle, so a target that itself mentions projections of later states is
reached too. -/
def eqPathCongr (a b : Expr) : FM (Option Expr) := do
  let env ← getEnv
  let mut edges : Array (Expr × Expr × Expr) := #[]
  for h in (← read).hyps do
    if let some (_, u, v) := h.ty.eq? then
      if isFactShape env h.ty || (u.isFVar && v.isFVar) then continue
      edges := edges.push (u, v, h.pf) |>.push (v, u, ← mkEqSymm h.pf)
  if edges.isEmpty then return none
  let reach (x : Expr) : MetaM (Array (Expr × Expr)) := do
    let mut all : Array (Expr × Expr) := #[(x, ← mkEqRefl x)]
    let mut frontier := all
    for _ in [0:6] do
      let mut next := #[]
      for (n, pn) in frontier do
        for (u, v, pe) in edges do
          unless (n.find? (· == u)).isSome do continue
          -- abstracted through a local, not `.bvar 0`: an occurrence under
          -- a binder must not be captured by it
          let motive ← withLocalDeclD `z (← inferType u) fun z =>
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
  let ra ← reach a
  let rb ← reach b
  for (na, pa) in ra do
    for (nb, pb) in rb do
      if ← same na nb then
        return some (← mkEqTrans pa (← mkEqSymm pb))
  return none

/-! ## 5. The backward search

`prove fuel t` — the rules, in order:

* **connectives**: `True`, `∧` (both sides; the right one first when the left
  has an `∃`-witness hole), `∨` (either side), `∃` (a witness hole the proof
  fixes, else a default), a definition that unfolds to `∧`/`∃` (`SimE`);
* **a hypothesis** (reducibly; also up to one store equation);
* **a fact** (`provedFact`): a hypothesis, the conclusion (or a conjunct) of a
  `∀`-hypothesis whose premises are proved, or a fact at an earlier store
  carried by a transport lemma along an `Ext` path;
* **a path** of a preorder (§4), for a non-`Eq` preorder also through steps
  the rules prove; an equation between frame terms by congruence;
* **evaluation** (`rflBounded`);
* **the rules**: the call's lemmas, then `@[bridge_frame]`, then the
  `∀`-hypotheses — the conclusion (at any telescope length, an equation in
  either orientation) unified with the goal, the premises proved by
  `proveArgs`.

`fuel` bounds the recursion; a closed goal that failed is not tried again at
the same fuel. -/

/-- A conclusion and its conjuncts (along the right spine), each with the
projection that extracts it. -/
def conjunctProjs (c : Expr) : Array (Expr × (Expr → MetaM Expr)) := Id.run do
  let mut out : Array (Expr × (Expr → MetaM Expr)) := #[(c, pure)]
  let mut c := c.cleanupAnnotations
  let mut proj : Expr → MetaM Expr := pure
  while c.isAppOfArity ``And 2 do
    let pl := proj
    out := out.push (c.appFn!.appArg!, fun e => do mkAppM ``And.left #[← pl e])
    proj := fun e => do mkAppM ``And.right #[← pl e]
    c := c.appArg!.cleanupAnnotations
    out := out.push (c, proj)
  return out

mutual

/-- The backward search: a proof of `t`, or `none`. -/
partial def prove (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  let t := (← instantiateMVars t).cleanupAnnotations
  -- the failure cache, keyed by the goal with its metavariables abstracted
  -- (`CheckOK ?m ?e ?f ?s` fails the same way every time it is asked)
  let key ← if t.hasMVar then pure (← abstractMVars t).expr else pure t
  let key? := (← read).failCache
  if let some ref := key? then
    if let some f := (← (ref.get : IO _))[key]? then
      if f ≥ fuel then return none
  let r ← withTraceNode `bridge (fun r => return m!"{match r with | .ok (some _) => "✅" | _ => "❌"} {t}") do
    if let some p ← attempt (proveCore fuel t) then return some p
    if fuel == 0 then return none
    byRules fuel t
  if r.isNone then
    if let some ref := key? then (ref.modify (·.insert key fuel) : IO Unit)
  return r

/-- `prove`'s rules before the lemmas. -/
partial def proveCore (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  if t.isConstOf ``True then return some (mkConst ``True.intro)
  if t.isAppOfArity ``And 2 then
    let l := t.appFn!.appArg!
    let r := t.appArg!
    if let some p ← attempt (do
        let some pa ← prove fuel l | return none
        let some pb ← prove fuel r | return none
        return some (mkApp4 (mkConst ``And.intro) l r pa pb)) then return some p
    -- a left conjunct with an `∃`-witness hole the right one fixes
    -- (`f x = some ?w ∧ denoteE st h = some ?w`)
    unless (← instantiateMVars l).hasExprMVar do return none
    let some pb ← prove fuel r | return none
    let some pa ← prove fuel (← instantiateMVars l) | return none
    return some (mkApp4 (mkConst ``And.intro) (← instantiateMVars l) (← instantiateMVars r) pa pb)
  if let some h ← findHyp t then return some h
  if let some h ← findHypModStoreEq t then return some h
  if fuel == 0 then return none
  if t.isAppOfArity ``Or 2 then
    let a := t.appFn!.appArg!; let b := t.appArg!
    if let some p ← attempt (prove fuel a) then return some (mkApp3 (mkConst ``Or.inl) a b p)
    if let some p ← attempt (prove fuel b) then return some (mkApp3 (mkConst ``Or.inr) a b p)
    return none
  if t.isAppOfArity ``Exists 2 then
    let α := t.appFn!.appArg!
    let x ← mkFreshExprMVar α
    let some pa ← attempt (prove fuel (t.appArg!.beta #[x]).cleanupAnnotations) | return none
    -- a witness the proof did not fix (a fuel the lemma is uniform in): any
    unless ← x.mvarId!.isAssigned do
      let some d ← attemptM (do return some (← mkAppOptM ``Inhabited.default #[α, none]))
        | return none
      x.mvarId!.assign d
    return some (← mkAppOptM ``Exists.intro #[α, t.appArg!, ← instantiateMVars x,
      ← instantiateMVars pa])
  let env ← getEnv
  if isFactShape env t then return ← provedFact fuel t
  if let some (n, pre, a, b) ← preorder? t then
    if let some p ← path n pre a b then return some p
    if n == ``Eq then
      -- by congruence only between FRAME terms (a state, its caches, a table)
      -- and only closed: with metavariables every rewrite unifies, and a view
      -- read is never one (measured: 1.5 s on one goal)
      unless t.hasExprMVar do
        let isStruct := (← whnfR (← inferType a)).getAppFn.constName?.any (isStructure env)
        if isStruct || ((← projShaped a) && (← projShaped b)) then
          if let some p ← eqPathCongr a b then return some p
        if let some p ← rflBounded t then return some p
    else if let some p ← pathByRules fuel n pre a b then return some p
    return none
  -- a definition that unfolds to an `∃`/`∧` (`SimBOp`, `SimE`)
  let some n := t.getAppFn.constName? | return none
  unless peelable n && env.find? n matches some (.defnInfo _) do return none
  let some t' ← unfoldDefinition? t | return none
  let t' := t'.headBeta
  unless t'.isAppOfArity ``Exists 2 || t'.isAppOfArity ``And 2 do return none
  let some p ← attempt (prove fuel t') | return none
  return some (← mkExpectedTypeHint p t)

/-- `R a b` for a preorder `R` through steps the rules prove (`ReadbackFrame`
of a readback call, from `ReadbackFrame.ofReadN`): breadth first over the
locals of `a`'s type, a step `R x y` being a hypothesis or proved by
`byRules`.  Only when there is a local besides `a` and `b` (else the one step
is `prove`'s own rule fallback). -/
partial def pathByRules (fuel : Nat) (n : Name) (pre a b : Expr) : FM (Option Expr) := do
  let ty ← inferType a
  let mut nodes : Array Expr := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if (← same d.toExpr a) || (← same d.toExpr b) then continue
    if ← same d.type ty then nodes := nodes.push d.toExpr
  if nodes.isEmpty then return none
  nodes := nodes.push b
  bfs a (← preRefl n a) b nodes.size fun seen x px => do
    let mut out := #[]
    for y in nodes do
      if ← seen.anyM (same · y) then continue
      let g := mkApp2 pre x y
      let some pe ← attempt (do
          if let some h ← findHyp g then return some h
          byRules (fuel - 1) g) | continue
      out := out.push (y, ← preTrans n px pe)
    return out

/-- The rules: the lemmas (the call's list, then `@[bridge_frame]`), then the
`∀`-hypotheses (a fact's are `provedFact`'s). -/
partial def byRules (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  if let some p ← byLemmas fuel t then return some p
  if isFactShape (← getEnv) t then return none
  byForallHyp fuel t

/-- The goal from a lemma: its conclusion — at any telescope length (a
conclusion may itself be a `∀`), an equation in either orientation —
unified with `t`, its premises proved by `proveArgs`. -/
partial def byLemmas (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  let snap ← read
  let env ← getEnv
  -- the syntactic filter: the conclusion at telescope length `n - k` must
  -- match the goal (either way round for an equation)
  let skelOk (c : Expr) : Bool :=
    quickMatch env c t || (match c.eq? with
      | some (ty, a, b) => quickMatch env (mkApp3 c.getAppFn ty b a) t
      | none => false)
  for lr in snap.lemmas, (n, skels) in snap.lemmaSkels do
    for k in [0:n + 1] do
      unless skelOk (skels[n - k]?.getD t) do continue
      for flip in [false, true] do
        let r ← attempt do
          let (_, _, l) ← openAbstractMVarsResult lr
          let (args, _, concl) ← forallMetaBoundedTelescope (← inferType l) (n - k)
          let concl ← if !flip then pure concl else
            match concl.eq? with
            | some (ty, a, b) => pure (mkApp3 (mkConst ``Eq [← getLevel ty]) ty b a)
            | none => return none
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
  return none

/-- The goal from a `∀`-HYPOTHESIS — an answer relation, a callee's
`∀ x, denoteE s c = some x → …` postcondition, a callee's frame rule — whose
conclusion, or a conjunct of it, unifies with `t`; its premises proved by
`proveArgs`. -/
partial def byForallHyp (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  if fuel == 0 then return none
  let env ← getEnv
  for h in (← read).hyps.reverse do
    let some rt := h.rel? | continue
    unless h.concls.any (quickMatch env · t) do continue
    let r ← attempt do
      let (args, _, concl) ← forallMetaTelescope rt
      for (cc, pj) in conjunctProjs concl do
        unless ← mayMatch cc t do continue
        let r ← attempt do
          unless ← same cc t do return none
          unless ← proveArgs fuel t.getAppFn.constName? args.toList do return none
          let e ← instantiateMVars (mkAppN h.pf args)
          if e.hasExprMVar then return none
          return some (← pj e)
        if let some p := r then return some p
      return none
    if let some p := r then return some p
  return none

/-- Prove the `Prop` premises `args` of a rule, in order.  A closed premise is
proved by `prove`; one with metavariables is matched against EVERY hypothesis,
with backtracking (the first match fixes metavariables — here the store — that
a later premise may refute), and searched for only if it is a fact or a frame
predicate: an answer relation, an equation (a view read `st.view h = some
(.app ?f ?a)`), or the goal's own head near the bottom of the fuel would
re-enter the rules with a free store, every rule unifying with it. -/
partial def proveArgs (fuel : Nat) (ghd : Option Name) (args : List Expr) : FM Bool := do
  match args with
  | [] => return true
  | a :: rest =>
    if ← a.mvarId!.isAssigned then return ← proveArgs fuel ghd rest
    let aT ← instantiateMVars (← inferType a)
    unless ← isProp aT do return ← proveArgs fuel ghd rest
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
    let env ← getEnv
    let hd := (← whnfR aT).getAppFn.constName?
    if !(isFrameShape aT || isFactShape env aT) &&
        ((hd == ghd && fuel < 4) || hd.any (isAnswerRel env) || hd == some ``Eq) then
      return false
    let s ← save
    if let some pa ← prove (fuel - 1) aT then
      if ← supply a pa then
        if ← proveArgs fuel ghd rest then return true
    restore s
    return false

/-- A FACT `t` — `denote… st h = some x`, `x` possibly a metavariable — from a
hypothesis, from a `∀`-hypothesis, or from either at an earlier store carried
by the transport lemma of `t`'s head along an `Ext` path.  (A non-fact: a
hypothesis or evaluation.) -/
partial def provedFact (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  if let some h ← findHyp t then return some h
  let env ← getEnv
  unless isFactShape env t do return ← rflBounded t
  if let some h ← byForallHyp fuel t then return some h
  let some (_, lhs, _) := t.eq? | return none
  let some hd := lhs.getAppFn.constName? | return none
  for (lem, k) in transportExt.getState env do
    unless k == hd do continue
    let r ← attempt do
      let pf ← mkConstWithFreshMVarLevels lem
      let (args, _, concl) ← forallMetaTelescope (← inferType pf)
      unless ← mayMatch concl t do return none
      unless ← same concl t do return none
      -- the last two explicit arguments are the fact and the `Ext`
      let hd := args[args.size - 2]!
      let hx := args[args.size - 1]!
      let hdT ← instantiateMVars (← inferType hd)
      let some ph ← (do if let some p ← findHyp hdT then pure (some p)
                         else byForallHyp fuel hdT) | return none
      unless ← supply hd ph do return none
      let hxT ← instantiateMVars (← inferType hx)
      let some px ← path `ConRon.Arena.Ext hxT.appFn!.appFn! hxT.appFn!.appArg! hxT.appArg!
        | return none
      unless ← supply hx px do return none
      return some (← instantiateMVars (mkAppN pf args))
    if let some p := r then return some p
  return none

end

/-- Close `g` if `prove` does; otherwise split its top-level conjunction and
close the conjuncts it can — only if one closes, so that an arm's own
conjunction stays whole.  Returns the open goals. -/
partial def frameGoal (snap : Snap) (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  if let some p ← attemptM ((prove 6 t).run snap) then
    g.assign p
    return []
  unless t.isAppOfArity ``And 2 do return [g]
  let s ← saveState
  let ga ← mkFreshExprSyntheticOpaqueMVar t.appFn!.appArg! (← g.getTag)
  let gb ← mkFreshExprSyntheticOpaqueMVar t.appArg! (← g.getTag)
  g.assign (mkApp4 (mkConst ``And.intro) t.appFn!.appArg! t.appArg! ga gb)
  let rest := (← frameGoal snap ga.mvarId!) ++ (← frameGoal snap gb.mvarId!)
  if rest == [ga.mvarId!, gb.mvarId!] then
    s.restore
    return [g]
  return rest

/-- A rule's telescope length and its conclusion after each length. -/
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

/-- The rules `prove` applies: the terms `extra` (elaborated in the current
goal), then `@[bridge_frame]`; with their skeletons. -/
def rules (extra : Array Term) : TacticM (Array AbstractMVarsResult × Array (Nat × Array Expr)) := do
  let mut ls := #[]
  for t in extra do ls := ls.push (← abstractMVars (← Tactic.elabTerm t none))
  for n in registered (← getEnv) frameExt do
    ls := ls.push (← abstractMVars (← mkConstWithFreshMVarLevels n))
  return (ls, ← ls.mapM (fun l => (lemmaSkel l : MetaM _)))

/-- `bridge_frame [l₁, …]` on one goal. -/
def frameGoals (extra : Array Term) (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let (ls, sks) ← rules extra
  let snap ← snapshot
  frameGoal { snap with lemmas := ls, lemmaSkels := sks, failCache := some (← IO.mkRef {}) } g

/-! ## 6. The forward step: instantiate what the context already knows -/

/-- The premise with its head constant unfolded once, if that constant is a
non-reducible definition (not a frame predicate or an answer relation). -/
def unfoldHeadOnce (t : Expr) : MetaM (Option Expr) := do
  let some n := t.getAppFn.constName? | return none
  if isAnswerRel (← getEnv) n || isFrameShape t then return none
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
def peelAll (g : MVarId) (boolAnd : Bool := false) (old : Std.HashSet FVarId := {}) :
    MetaM MVarId := do
  let exs ← g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || old.contains d.fvarId then continue
      let t := (← instantiateMVars d.type).cleanupAnnotations
      if t.isAppOfArity ``Exists 2 || t.isAppOfArity ``And 2 ||
          (boolAnd && (andTrue? t).isSome) then
        out := out.push d.fvarId
      -- a definition that may unfold to one (`peelNew` decides)
      else if let some n := t.getAppFn.constName? then
        if (← getEnv).find? n matches some (.defnInfo _) then
          if peelable n && !(mentionsTriple t) && (← isProp t) then out := out.push d.fvarId
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

/-- Introduce the goal's leading `∀ x₁ … xₖ, P₁ → … → Pₘ → …` while the
premises are facts about the `xᵢ` (then `… = some …` lookups): a
postcondition's `∀ e, denoteE st c = some e → …`, so that its facts take part
in the rounds; `unifyFacts` identifies a known denotation with the new one. -/
partial def introFacts (g : MVarId) : MetaM MVarId := do
  let n ← g.withContext do
    let env ← getEnv
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
        if isFactShape env pt && xs[0:k].toArray.any (pt.containsFVar ·.fvarId!) then
          m := m + 1; continue
        -- a lookup `env.find? nm = some ci`, after the facts
        unless m > 0 && pt.eq?.any (·.2.2.isAppOfArity ``Option.some 2) do break
        m := m + 1
      return if m == 0 then 0 else k + m
  if n == 0 then return g
  let (_, g') ← g.introNP n
  introFacts g'

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
  if unfoldRelGoal && tg.getAppFn.constName?.any (isAnswerRel (← getEnv)) then
    let tu ← g.withContext (unfoldRel tg)
    if tu != tg then g ← g.replaceTargetDefEq (← Core.betaReduce tu)
  g ← introFacts g
  -- the program's own `∃`s (a callee's postcondition): destructured first;
  -- under `bridge_auto` also a Boolean conjunction tested true
  g ← peelAll g (boolAnd := true)
  g ← storeNorm g
  let mut opened : Std.HashSet FVarId := {}
  let (g', o) ← openIsSome g opened
  g := g'; opened := o
  let mut seen : Array Expr := #[]
  let mut deadL : Array Bool := #[]
  let mut cache : Std.HashMap FVarId (Array Hyp) := {}
  let mut first := true
  -- the frame premises of the sources are proved with `@[bridge_frame]`
  let (rl, rsk) ← g.withContext (rules #[])
  for _ in [0:8] do
    let (news, snap) ← g.withContext do
      let mut ls := #[]
      for n in defaults do ls := ls.push (← mkConstWithFreshMVarLevels n)
      for t in extra do ls := ls.push (← Tactic.elabTerm t none)
      let snap := { (← snapshot cache) with lemmas := rl, lemmaSkels := rsk }
      let fresh? := if first then none else
        some (snap.hyps.filter fun h => !cache.contains h.src)
      pure (← (fwdRound ls defaults.length seen deadL fresh?).run snap, snap)
    first := false
    cache := {}
    for h in snap.hyps do
      cache := cache.insert h.src ((cache.getD h.src #[]).push h)
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
  -- a function's answer is unique: two denotations of one handle are one
  -- value (`unifyFacts`); the new equations substituted (only those, and only
  -- after the rounds, which name the locals: on a verification condition's
  -- context `substVars` is the dearest step); once more, since an
  -- identification can make two lookups' keys equal; and what the
  -- substitution made a constructor split (`Expr.WScoped d x` at `x := .app …`)
  let then_subst (g' : MVarId) : MetaM MVarId := if g' == g then pure g' else substNew g' old
  g ← substNew (← g.withContext (unifyFacts g)) old
  g ← then_subst (← g.withContext (unifyFacts g))
  g ← then_subst (← peelAll g)
  clearTrivial g old

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
  let mut out := []
  for g in ← getGoals do
    unless ← g.isAssigned do out := out ++ (← Frame.frameGoals extra g)
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
      return t.getAppFn.constName?.any (Frame.isAnswerRel (← getEnv))
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
