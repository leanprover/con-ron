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

open Lean Meta Elab Tactic

namespace Frame

/-- Every bridge constant this module names with a single backtick
(unchecked here); `Bridge/Frame.lean` checks each exists. -/
def usedConstants : List Name :=
  [`ConRon.Arena.AState,
   `ConRon.Arena.AState.caches,
   `ConRon.Arena.AState.store,
   `ConRon.Arena.EStore,
   `ConRon.Arena.Ext,
   `ConRon.Arena.Ext.refl,
   `ConRon.Arena.Ext.trans,
   `ConRon.Arena.Frontend.denoteEList,
   `ConRon.Arena.Frontend.denoteNList,
   `ConRon.Arena.StoreWF,
   `ConRon.Arena.denoteE,
   `ConRon.Arena.denoteL,
   `ConRon.Arena.denoteLs,
   `ConRon.Arena.denoteN,
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
   `ConRon.Bridge.denoteEList_ext_fr,
   `ConRon.Bridge.denoteEO,
   `ConRon.Bridge.denoteEO_ext,
   `ConRon.Bridge.denoteL_ext,
   `ConRon.Bridge.denoteLs_ext,
   `ConRon.Bridge.denoteNList_ext_fr,
   `ConRon.Bridge.denoteN_ext,
   `ConRon.Bridge.denote_app_inv,
   `ConRon.Bridge.denote_const_inv,
   `ConRon.Bridge.denote_ext,
   `ConRon.Bridge.denote_forallE_inv,
   `ConRon.Bridge.denote_fvar_inv,
   `ConRon.Bridge.denote_lam_inv,
   `ConRon.Bridge.denote_letE_inv,
   `ConRon.Bridge.denote_proj_inv,
   `ConRon.Bridge.denote_sort_inv,
   `ConRon.Bridge.eq_of_eq_some,
   `ConRon.Bridge.isSome_of_eq_some,
   `Std.Do.Triple]

/-- The transport lemmas: each is `(hd : P st) → (hx : Ext st st') → P st'`,
with the denotation fact FIRST so that the store it lives at is fixed by a
hypothesis before the `Ext` path is searched. -/
def transportLemmas : List Name :=
  [`ConRon.Bridge.denote_ext, `ConRon.Bridge.denoteN_ext, `ConRon.Bridge.denoteL_ext, `ConRon.Bridge.denoteLs_ext,
   `ConRon.Bridge.denoteEList_ext_fr, `ConRon.Bridge.denoteNList_ext_fr, `ConRon.Bridge.denoteEO_ext]
-- (in `factHeads`' order: `provedFact` picks the one at its fact's head)

/-- The heads of the denotation facts the transports conclude. -/
def factHeads : List Name :=
  [`ConRon.Arena.denoteE, `ConRon.Arena.denoteN, `ConRon.Arena.denoteL, `ConRon.Arena.denoteLs, `ConRon.Arena.Frontend.denoteEList,
   `ConRon.Arena.Frontend.denoteNList, `ConRon.Bridge.denoteEO]

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
def isFactShape (t : Expr) : Bool :=
  match t.eq? with
  | some (_, lhs, _) => lhs.getAppFn.constName?.any (· ∈ factHeads)
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

abbrev FM := ReaderT Snap MetaM

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

/-- A proof of `a = b` from the snapshot's equalities of the same type,
breadth first, in either orientation. -/
def eqPath (ty a b : Expr) : FM (Option Expr) := do
  if ← same a b then return some (← mkEqRefl a)
  let mut edges : Array (Expr × Expr × Expr) := #[]
  for h in (← read).hyps do
    if let some (ty', u, v) := h.ty.eq? then
      if isFactShape h.ty then continue
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
        unless ← same n src do continue
        if ← seen.anyM (fun x => (same dst x : MetaM Bool)) then continue
        let p ← mkEqTrans pn pe
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
  let rigid (n : Name) : Bool := getReducibilityStatusCore env n != .reducible
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

/-- `quickMatch` at the top: the filter every search runs before `same`. -/
def mayMatch (ht t : Expr) : MetaM Bool := return quickMatch (← getEnv) ht t

/-- A hypothesis whose type is `t` (reducibly, the most recent first). -/
def findHyp (t : Expr) : FM (Option Expr) := do
  let t ← normNeg t
  for h in (← read).hyps.reverse do
    unless ← mayMatch h.ty t do continue
    if let some p ← attempt (do if ← same h.ty t then return some h.pf else return none) then
      return some p
  return none

mutual

/-- The frame solver: a proof of `t`, or `none`.  `fuel` bounds the
backward chaining through `CheckOK.mono`, `StateOK` and the `∃` intro. -/
partial def prove (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  let t := (← instantiateMVars t).cleanupAnnotations
  if t.isConstOf ``True then return some (mkConst ``True.intro)
  if t.isAppOfArity ``And 2 then
    let some pa ← prove fuel t.appFn!.appArg! | return none
    let some pb ← prove fuel t.appArg! | return none
    return some (mkApp4 (mkConst ``And.intro) t.appFn!.appArg! t.appArg! pa pb)
  if let some h ← findHyp t then return some h
  if fuel == 0 then return none
  if t.isAppOfArity `ConRon.Arena.Ext 2 then
    return ← extPath t.appFn!.appArg! t.appArg!
  if let some (ty, a, b) := t.eq? then
    -- a denotation at the current store: a fact at an earlier one, transported
    if isFactShape t then return ← provedFact fuel t
    -- `o.isSome = true` from a denotation fact `o = some x`
    if b.isConstOf ``Bool.true && a.isAppOfArity ``Option.isSome 2 then
      let o := a.appArg!
      let α := a.appFn!.appArg!
      let x ← mkFreshExprMVar α
      let ft ← mkEq o (← mkAppM ``Option.some #[x])
      if isFactShape ft then
        let some ph ← attempt (provedFact fuel ft) | return none
        return some (← mkAppM `ConRon.Bridge.isSome_of_eq_some #[ph])
      return none
    return ← eqPath ty a b
  if t.isAppOfArity ``Exists 2 then
    let body := t.appArg!
    let α := t.appFn!.appArg!
    let x ← mkFreshExprMVar α
    let inst := (body.beta #[x]).cleanupAnnotations
    if inst.isAppOfArity ``And 2 then
      let some pa ← attempt (prove fuel inst.appFn!.appArg!) | return none
      let some pb ← attempt (prove fuel inst.appArg!) | return none
      let x ← instantiateMVars x
      return some (← mkAppOptM ``Exists.intro #[α, body, x,
        mkApp4 (mkConst ``And.intro) (← instantiateMVars inst.appFn!.appArg!)
          (← instantiateMVars inst.appArg!) pa pb])
    let some pa ← attempt (prove fuel inst) | return none
    return some (← mkAppOptM ``Exists.intro #[α, body, ← instantiateMVars x, pa])
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
    return none
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
    return none
  | some `ConRon.Bridge.CheckOK =>
    for h in (← read).hyps.reverse do
      unless h.ty.isAppOfArity `ConRon.Bridge.CheckOK 4 do continue
      for lem in [`ConRon.Bridge.CheckOK.mono, `ConRon.Bridge.CheckOK.monoF] do
        if let some p ← attempt (applyLemma fuel lem h.pf t) then return some p
    return none
  | some `ConRon.Bridge.CacheFrame =>
    let a := t.appFn!.appArg!
    let b := t.appArg!
    if ← same a b then return some (← mkAppM `ConRon.Bridge.CacheFrame.refl #[a])
    for h in (← read).hyps.reverse do
      unless h.ty.isAppOfArity `ConRon.Bridge.CacheFrame 2 do continue
      unless ← same h.ty.appFn!.appArg! a do continue
      let m := h.ty.appArg!
      if ← same m b then return some h.pf
      if let some p ← attempt (prove (fuel - 1) (← mkAppM `ConRon.Bridge.CacheFrame #[m, b])) then
        return some (← mkAppM `ConRon.Bridge.CacheFrame.trans #[h.pf, p])
    -- the frame of a call that moved no cache
    let hc ← mkEq (← mkAppM `ConRon.Arena.AState.caches #[b]) (← mkAppM `ConRon.Arena.AState.caches #[a])
    let some pc ← attempt (prove (fuel - 1) hc) | return none
    let some px ← extPath (← mkAppM `ConRon.Arena.AState.store #[a]) (← mkAppM `ConRon.Arena.AState.store #[b])
      | return none
    return some (← mkAppM `ConRon.Bridge.CacheFrame.of_eq #[pc, px])
  | _ => proveByLemmas fuel t

/-- The goal from one of `bridge_frame [l₁, …]`'s lemmas: its conclusion
unified with `t`, every premise proved by `prove`. -/
partial def proveByLemmas (fuel : Nat) (t : Expr) : FM (Option Expr) := do
  for lr in (← read).lemmas do
    let r ← attempt do
      let (_, _, l) ← openAbstractMVarsResult lr
      let (args, _, concl) ← forallMetaTelescope (← inferType l)
      unless ← mayMatch concl t do return none
      unless ← same concl t do return none
      for a in args do
        if ← a.mvarId!.isAssigned then continue
        let aT ← instantiateMVars (← inferType a)
        unless ← isProp aT do continue
        let some pa ← prove (fuel - 1) aT | return none
        unless ← supply a pa do return none
      let e ← instantiateMVars (mkAppN l args)
      if e.hasExprMVar then return none
      return some e
    if let some p := r then return some p
  return none

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
  if !isFactShape t then return ← findHyp t
  if let some h ← findHyp t then return some h
  if let some h ← chainHyp fuel t then return some h
  -- the one transport lemma whose conclusion has `t`'s head
  let some (_, lhs, _) := t.eq? | return none
  let some hd := lhs.getAppFn.constName? | return none
  let some i := factHeads.idxOf? hd | return none
  for lem in [transportLemmas[i]!] do
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
  if let some p ← attemptM ((prove 4 t).run snap) then
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
    if isFactShape aT then
      let s ← save
      let some p ← attempt (provedFact 2 aT) | return acc
      unless ← supply a p do restore s; return acc
      let r ← instances rest mk acc
      restore s
      return r
    -- a premise matched against every hypothesis: branch
    let aT ← normNeg aT
    let mut acc := acc
    for h in (← read).hyps.reverse do
      unless ← mayMatch h.ty aT do continue
      let s ← save
      if ← same h.ty aT then
        a.mvarId!.assign h.pf
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
    else if isFactShape aT then f := f.push a
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
  for h in (← read).hyps do
    if let some r := h.rel? then srcs := srcs.push (h.pf, r, none)
  for l in lemmas, i in [0:lemmas.size] do
    if deadL[i]?.getD false then continue
    srcs := srcs.push (l, ← normNeg (← inferType l), some i)
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
      if p && !isFrameShape aT && !isFactShape aT && dead == args.size then
        let aT' ← normNeg aT
        unless ← (← read).hyps.anyM (fun h => (mayMatch h.ty aT' : MetaM Bool)) do
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
      let subs ← g.cases fv
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
    unless isFactShape t do continue
    let some (_, l, r) := t.eq? | continue
    unless r.isAppOfArity ``Option.some 2 do continue
    facts := facts.push (l, r.appArg!, d.toExpr)
  let mut news : Array Hypothesis := #[]
  for i in [0:facts.size] do
    for j in [i+1:facts.size] do
      let (l₁, a, p₁) := facts[i]!
      let (l₂, b, p₂) := facts[j]!
      if a == b then continue
      unless l₁.getAppFn == l₂.getAppFn do continue
      unless ← same l₁ l₂ do continue
      if ← same a b then continue
      news := news.push { userName := `fwd, type := ← mkEq a b,
                          value := ← mkAppM `ConRon.Bridge.eq_of_eq_some #[p₁, p₂] }
  if news.isEmpty then return g
  let (_, g) ← g.assertHypotheses news
  return g

/-- `peelNew` at every hypothesis that is (or unfolds to) a conjunction or an
existential. -/
def peelAll (g : MVarId) : MetaM MVarId := do
  let exs ← g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t := (← instantiateMVars d.type).cleanupAnnotations
      if t.isAppOfArity ``Exists 2 || t.isAppOfArity ``And 2 then out := out.push d.fvarId
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

/-- `substVars`, if some hypothesis is an equation with a local variable on
one side that the other side does not mention. -/
def substIfAny (g : MVarId) : MetaM MVarId := g.withContext do
  let mut any := false
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).cleanupAnnotations.eq? | continue
    if (a.isFVar && !b.containsFVar a.fvarId!) || (b.isFVar && !a.containsFVar b.fvarId!) then
      any := true; break
  unless any do return g
  match ← observing? (substVars g) with
  | some g' => pure g'
  | none => pure g

/-- Substitute the equations among the hypotheses NOT in `old` that solve a
local variable (`subst_vars` restricted to what `bridge_fwd` added: on a
verification condition's context a full `substVars` is the dearest step). -/
partial def substNew (g : MVarId) (old : Std.HashSet FVarId) : MetaM MVarId := do
  let next ← g.withContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail || old.contains d.fvarId then continue
      let some (_, a, b) := (← instantiateMVars d.type).cleanupAnnotations.eq? | continue
      if a.isFVar && !b.containsFVar a.fvarId! then return some (d.fvarId, false)
      if b.isFVar && !a.containsFVar b.fvarId! then return some (d.fvarId, true)
    return none
  let some (fv, symm) := next | return g
  match ← observing? (substCore g fv (symm := symm)) with
  | some (_, g') => substNew g' old
  | none => return g

/-- `bridge_fwd` on one goal. -/
def fwdGoal (g : MVarId) (defaults : List Name) (extra : Array Term) :
    TacticM MVarId := do
  let mut g := g
  let old ← g.withContext do
    let mut st : Std.HashSet FVarId := {}
    for d in (← getLCtx) do st := st.insert d.fvarId
    pure st
  -- the program's own `∃`s (a callee's postcondition): destructured first
  g ← peelAll g
  let mut seen : Array Expr := #[]
  let mut deadL : Array Bool := #[]
  let mut cache : Std.HashMap FVarId Hyp := {}
  let mut first := true
  for _ in [0:4] do
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
    seen := seen ++ news.map (·.2)
    let (fvs, g') ← g.assertHypotheses (news.map fun (p, t) =>
      { userName := `fwd, type := t, value := p })
    g ← g'.withContext (peelNew g' fvs)
  -- a function's answer is unique: two denotations of one handle (two
  -- callees read the same node) are one value
  g ← g.withContext (unifyFacts g)
  -- `subst_vars` once at the end (between rounds it would rename the locals
  -- `seen` mentions), and only when an equation solves a variable: on a
  -- verification condition's context `substVars` is the dearest step
  g ← substNew g old
  -- what the substitution made reducible (`Expr.WScoped d x` at `x := .app …`)
  let g' ← peelAll g
  if g' != g then g ← substNew g' old
  -- the goal's own `∀ x, denote… = some x → …`
  repeat
    let t ← g.withContext do whnfR (← instantiateMVars (← g.getType))
    let .forallE _ α body _ := t | break
    let .forallE _ hT _ _ := body | break
    let found ← g.withContext do
      let y ← mkFreshExprMVar α
      let hT' := hT.instantiate1 y
      unless isFactShape hT' do return none
      let snap ← snapshot
      attemptM ((provedFact 2 hT').run snap)
    let some p := found | break
    let (_, g1) ← g.intro1
    let (hx, g2) ← g1.intro1
    let (fv, g3) ← g2.withContext do
      let heq ← mkAppM `ConRon.Bridge.eq_of_eq_some #[p, mkFVar hx]
      let (fv, g3) ← g2.note `hxeq heq
      let g3 ← g3.clear hx
      pure (fv, g3)
    g ← g3.withContext (do
      match ← observing? (substCore g3 fv (symm := true)) with
      | some (_, g4) => pure g4
      | none => pure g3)
  return g

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
      pure { snap with lemmas := ls }
    out := out ++ (← Frame.frameGoal snap g)
  setGoals out

/-- con-leche: none — **the forward step** (task #120): instantiate every
answer relation and every `∀`-hypothesis of the context — and the lemmas in
the list, with the view inversions `denote_*_inv` always — at what the
context already knows (denotations transported along the `Ext` chain, frame
facts by `bridge_frame`'s search), add each new instance as a hypothesis
(`fwd✝`), split its `∧`/`∃`, and `subst_vars`; at most three rounds.  On a
goal `∀ x, denote… = some x → …` whose denotation the context already has, it
introduces `x` and identifies it with the known one. -/
syntax (name := bridgeFwd) "bridge_fwd" (" [" term,* "]")? : tactic

@[tactic bridgeFwd] def evalBridgeFwd : Tactic := fun stx => do
  let extra : Array Term :=
    if stx[1].isNone then #[] else (stx[1][1].getSepArgs.map (⟨·⟩))
  let defaults : List Name := [`ConRon.Bridge.denote_fvar_inv, `ConRon.Bridge.denote_sort_inv,
    `ConRon.Bridge.denote_const_inv, `ConRon.Bridge.denote_app_inv, `ConRon.Bridge.denote_lam_inv, `ConRon.Bridge.denote_forallE_inv,
    `ConRon.Bridge.denote_letE_inv, `ConRon.Bridge.denote_proj_inv]
  let goals ← getGoals
  let mut out := []
  for g in goals do
    if ← g.isAssigned then continue
    out := out ++ [← Frame.fwdGoal g defaults extra]
  setGoals out

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

namespace Frame

/-- Match the patterns against `g`'s context; on success, the goal with the
matched hypotheses (and `?x` variables) renamed. -/
def matchArm (g : MVarId) (pats : Array (Ident × Term)) (tgt? : Option Term) :
    TacticM (Option MVarId) := g.withContext do
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
    let mut used : Array FVarId := #[]
    let mut renames : Array (FVarId × Name) := #[]
    -- the target first: its `?x` constrain the hypothesis patterns
    if let some tgt := tgt? then
      let tt ← Term.withoutErrToSorry <| Tactic.elabTerm tgt none (mayPostpone := true)
      unless ← withAssignableSyntheticOpaque (same (← instantiateMVars (← g.getType)) tt) do
        s.restore; return none
    for (n, pat) in pats do
      let pt ← normNeg (← Term.withoutErrToSorry <|
        Tactic.elabTerm pat none (mayPostpone := true))
      let mut found := none
      for d in (← getLCtx).decls.toArray.reverse do
        let some d := d | continue
        if d.isImplementationDetail || used.contains d.fvarId then continue
        let dt ← normNeg (← instantiateMVars d.type)
        unless ← mayMatch dt pt do continue
        let st ← saveState
        if ← withAssignableSyntheticOpaque (same dt pt) then
          found := some d.fvarId; break
        st.restore
      let some fv := found | s.restore; return none
      used := used.push fv
      renames := renames.push (fv, n.getId)
    -- `?x` in a pattern names the local it matched
    for (mv, n) in (← getMCtx).decls.toList.filterMap (fun (mv, d) =>
        if d.userName.isAnonymous || before.contains mv then none
        else some (mv, d.userName)) do
      if let some v ← getExprMVarAssignment? mv then
        let v ← instantiateMVars v
        if v.isFVar && !(renames.any (·.1 == v.fvarId!)) then
          renames := renames.push (v.fvarId!, n)
      -- forget the name, so that the next arm's `?x` is a fresh hole
      mv.setUserName .anonymous
    let mut g := g
    for (fv, n) in renames do
      g ← g.rename fv n
    return some g
  catch _ => s.restore; return none

end Frame

@[tactic vcArm] def evalVcArm : Tactic := fun stx => do
  let hs := stx[1].getArgs
  let pats : Array (Ident × Term) := hs.map fun h => (⟨h[1]⟩, ⟨h[3]⟩)
  let tgt? : Option Term := if stx[2].isNone then none else some ⟨stx[2][1]⟩
  let tac := stx[4]
  let gs ← getGoals
  let mut out := []
  let mut hit := false
  for g in gs do
    if ← g.isAssigned then continue
    match ← Frame.matchArm g pats tgt? with
    | none => out := out ++ [g]
    | some g' =>
      hit := true
      setGoals [g']
      evalTactic tac
      out := out ++ (← getUnsolvedGoals)
  unless hit do throwError "vc_arm: no open goal matches this arm"
  setGoals out

end ConRon.Bridge
