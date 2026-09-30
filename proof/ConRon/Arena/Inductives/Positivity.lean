/-
# `ConRon.Arena.Inductives.Positivity` — positivity through containers
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/Positivity.lean` over handles: the occurrence
tests, the whole-application abstraction of a frame's group to its holes, the
readback of a walked term, and the ONE positivity function `nestPos` with its
container case (`nestCont`, `nestContKey`, `nestContNew`, `nestFrame`), its
root frame (`nestRoot`), official's uniform-occurrence check (`nestUniform`)
and the seeds (`nestSeeds`).  The Rust twin is
`arena::inductives::positivity`; this module mirrors it item for item.

## The twin's deviations (the Rust's, shared)

* **A pure walk, its memoised walk and its `Fast` entry are ONE memoised walk
  over handles** (`mentionsAnyConst`, `nestOcc`, `replaceFVars`,
  `replaceApps`, `Expr.depth`), keyed by the handle, with a fresh memo per
  top-level call as con-leche's `…Fast` has.  The Rust splits each into a
  `…_go` walk and a `…_node` step (extraction rule 5); the twin keeps the
  step inline in its `…Go`.  The `MemoInv`s and `_spec`s are proofs.
* **`NestCtx.find?` is the environment**: every function that reads the
  environment takes `fe : IFEnv` beside the context.  The Rust record also
  carries the visibility bound `vis`; over the twin's `IFEnv` the bound is
  `fe.visibleBelow` (the Rust passes `vis = fe.visible_below` beside the
  same `fe`), so the twin's record has no `vis` and a function that read
  only `ctx.vis` (`nestBlockOf`, `nestFrameMates`, `nestArity`,
  `nestGroupCtors`) does not take the context.  The record carries `lvls`,
  the block's own level parameters as levels (`ctx.lps.map .param`),
  interned once: over handles `List Level` equality is the interned list's
  handle.
* **`replaceFVars`' function argument is the enum `FvMap`**, one variant per
  instantiation con-leche writes (`nestHoleImg ctx prog`, `nestKeyMap ds
  holes`, `eraseFVarTys`' constant map, `targetCanonParams`' opener lookup),
  dispatched by `fvMapAt`.  `replaceApps` has ONE instantiation
  (`nestCanonSub`), so it is that walk, specialised.
* **The frame stack `prog` is a list in OUTERMOST-first order** (the reverse
  of con-leche's innermost-first list): a frame's group is appended where
  con-leche prepends its reversal, `nestHoleAt`'s `rootHoles ++ prog.reverse`
  is `rootHoles ++ prog`, and `nestHoleImg`'s `h :: prog` is the prefix of
  length `n` with `h` its last.
* **`nestPos`'s continuation `rec` is the function itself** at an explicit
  fuel: every `rec` con-leche passes is `nestPos ops env ctx F` for some `F`
  — the enclosing walk's fuel inside a frame, `whnfWalkFuel crest` per root
  constructor (`nestRoot`), the seed's fold (`nestSeeds`) — so `nestCtors`
  takes a `root` flag and a fuel.
* **A pure term computed twice is computed once**: `closeTelescope nds hi
  cur` (U4, the normal-form record and the returned form) and
  `ty.piBinders` (`nestInstType`).
* **`NestedPositivity` and `nestedBlockPositivity` are not ported**: the unit
  tests' entry; the install runs `nestUniform`/`nestRoot` itself.

## The twin's shapes against the Rust (for Theorem 2)

* **`vis` dropped** (the campaign lead's ruling): the Rust's `NestCtx.vis`
  and every `(vis, fe)` pair are the twin's `fe`, related by `absU vis =
  lfe.visibleBelow`; every caller passes the `fe` whose `visibleBelow` the
  Rust stores in `ctx.vis` (`shape_nest_ctx(…, fe.visible_below)`).  The
  twin's `NestCtx` fields are `names lps nP nIdxs params sort lvls`.  Five
  signatures lose an argument and keep the Rust's order otherwise:
  `nestContainer fe C` (Rust `vis, fe, c`), `nestBlockOf fe C`,
  `nestFrameMates fe C`, `nestArity fe C` (Rust `ctx, fe, c`), and
  `nestGroupCtors fe nPc cs out` (Rust `fe, ctx, n_pc, cs, i, out`).
* `NestState` is `keys : Array NestKey`, `active : List NestKey` (innermost
  first: the Rust's `group_keys ++ active`), `ctorNfs : Array NestCtorNf`;
  every other Rust `Vec` is a `List`, an index cursor `i` being structural
  recursion on the list's tail (`nestCtors`, `nestRoot`, `nestSeeds`,
  `nestGrowGroup`, `nestAcceptGroup`, `nestGroupCtors`, `closeTelescope`,
  `instPisWith`).
* `FvMap.holeImg ctx prog n` flattens the Rust's `HoleImg(HoleImgMap { ctx,
  prog, n })`; `FvMap.rank` (no Rust counterpart) is the measure of the
  `fvMapAt`/`replaceFVarsGo`/`replaceFVars`/`nestHoleImg` mutual block.
* The `nestPos` block (`nestFields`, `nestCtors`, `nestFrame`,
  `nestContNew`, `nestContKey`, `nestCont`, `nestPos`) is well-founded on
  `(root, fuel, tag, size)`: the Rust's `nest_ctors_walk` split (root fuel
  vs. enclosing fuel, two tail calls) is the twin's `if _h : root` around the
  one `nestFields` call.  The helper sets that the Rust splits for
  extraction (`nest_pos_at`/`nest_pos_hole`, `nest_cont_params`,
  `nest_frame_at`/`nest_frame_walk`, `nest_ctors_typed`/`_walk`/`_done`,
  `nest_u4`, `nest_res_ok`) are inline.

The Rust's index-cursor helpers (`names_contain`, `nest_occ_any`,
`replace_fvars_list`, `params_closed`, `all_fvar_b_le`, `frame_stack`, …) are
the list operations they cite (`List.contains`, `List.anyM`, `List.mapM`,
`List.allM`, `++`); the Rust's `…_at`/`…_typed`/`…_walk`/`…_done`/`_hole`
continuations are inline in the twin they are "part of".  Definitions that the
twins' mutual recursion needs earlier (`nestKeyMap`, the frame's helpers ahead
of the `nestPos` block, `nestCtorNf`) are moved up.
-/
import ConRon.Arena.Inductives.FieldTele
import ConRon.Arena.CheckerBase

namespace ConRon.Arena

open ConLeche

/-! ## `mentionsAnyConst`: the positivity walk's question at k names -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:42-54 Expr.mentionsAnyConst
con-leche: ConLeche/Kernel/Inductives/Positivity.lean:84-119 Expr.mentionsAnyGo
Does any of the constants `names` occur in `h`?  A syntactic walk (`fvar`
annotations included; a `.proj` node names its structure), memoised on the
node.  Both children of a binary node are evaluated (no short circuit), as
con-leche's `mentionsAnyGo` does. -/
def mentionsAnyGo (names : List NIdx) (memo : Std.HashMap EIdx Bool) :
    Nat → EIdx → AM (Bool × Std.HashMap EIdx Bool)
  | 0, _ => fail (.internal "fuel exhausted: mentionsAnyConst")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure (false, memo)
    | .sort _ => pure (false, memo)
    | .lit _ => pure (false, memo)
    | .const n _ => pure (names.contains n, memo)
    | v =>
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let (r, m) ← match v with
          | .fvar _ ty => mentionsAnyGo names memo fuel ty
          | .app f a => do
            let (b1, m) ← mentionsAnyGo names memo fuel f
            let (b2, m2) ← mentionsAnyGo names m fuel a
            pure (b1 || b2, m2)
          | .lam ty body _ => do
            let (b1, m) ← mentionsAnyGo names memo fuel ty
            let (b2, m2) ← mentionsAnyGo names m fuel body
            pure (b1 || b2, m2)
          | .forallE ty body _ => do
            let (b1, m) ← mentionsAnyGo names memo fuel ty
            let (b2, m2) ← mentionsAnyGo names m fuel body
            pure (b1 || b2, m2)
          | .letE ty val body => do
            let (b1, m) ← mentionsAnyGo names memo fuel ty
            let (b2, m2) ← mentionsAnyGo names m fuel val
            let (b3, m3) ← mentionsAnyGo names m2 fuel body
            pure (b1 || b2 || b3, m3)
          | .proj s _ sub => do
            let (b, m) ← mentionsAnyGo names memo fuel sub
            pure (names.contains s || b, m)
          | _ => pure (false, memo)
        pure (r, m.insert h r)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:192-194 Expr.mentionsAnyConstFast
The executed `mentionsAnyConst` (one memoised DAG walk). -/
def mentionsAnyConst (names : List NIdx) (e : EIdx) : AM Bool := do
  let r ← mentionsAnyGo names ∅ coreWalkFuel e
  pure r.1

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:201-207 memberIdxAt?
Which member of the block a head expression names, at the block's own level
parameters `lvls` (an interned list, so `us == lvls` is handle equality);
`none` at any other head. -/
def memberIdxAt? (names : List NIdx) (lvls : LsIdx) (e : EIdx) : AM (Option Nat) := do
  if e.tag == ETag.const then
    match ← viewConst e with
    | none => failDanglingE
    | some (n, us) =>
      if us == lvls then pure (names.findIdx? (· == n)) else pure none
  else pure none

/-! ## Closing a telescope -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:211-219 closeTelescope
Close a telescope opened at the free variables `i ..< i + bs.length` back into
a syntactic Π-telescope over `body`, the innermost binder first. -/
def closeTelescope : List (EIdx × BinderMeta) → Nat → EIdx → AM EIdx
  | [], _, body => pure body
  | (d, m) :: bs, i, body => do
    let inner ← closeTelescope bs (i + 1) body
    let closed ← abstract1Fast coreWalkFuel inner i 0
    internForallEE d closed m

/-! ## `nestOcc`: official's `has_ind_occ`, with the holes -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:328-345 Expr.nestOcc
con-leche: ConLeche/Kernel/Inductives/Positivity.lean:347-377 Expr.nestOccGo
Does a MEMBER or a HOLE (the free variables `lo ..< hi`) occur in `h`?  A
free variable's annotation is NOT looked into, and a `.proj` node's structure
name is no occurrence.  Short-circuiting, memoised on the node. -/
def nestOccGo (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) :
    Nat → EIdx → AM (Bool × Std.HashMap EIdx Bool)
  | 0, _ => fail (.internal "fuel exhausted: nestOcc")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure (false, memo)
    | .sort _ => pure (false, memo)
    | .lit _ => pure (false, memo)
    | .fvar i _ => pure (decide (lo ≤ i) && decide (i < hi), memo)
    | .const n _ => pure (names.contains n, memo)
    | v =>
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let (r, m) ← match v with
          | .app f a => do
            let (b, m) ← nestOccGo names lo hi memo fuel f
            if b then pure (true, m) else nestOccGo names lo hi m fuel a
          | .lam ty body _ => do
            let (b, m) ← nestOccGo names lo hi memo fuel ty
            if b then pure (true, m) else nestOccGo names lo hi m fuel body
          | .forallE ty body _ => do
            let (b, m) ← nestOccGo names lo hi memo fuel ty
            if b then pure (true, m) else nestOccGo names lo hi m fuel body
          | .letE ty val body => do
            let (b, m) ← nestOccGo names lo hi memo fuel ty
            if b then pure (true, m) else do
              let (b2, m2) ← nestOccGo names lo hi m fuel val
              if b2 then pure (true, m2) else nestOccGo names lo hi m2 fuel body
          | .proj _ _ sub => nestOccGo names lo hi memo fuel sub
          | _ => pure (false, memo)
        pure (r, m.insert h r)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:506-508 Expr.nestOccFast
The executed `nestOcc` (one memoised DAG walk). -/
def nestOcc (names : List NIdx) (lo hi : Nat) (e : EIdx) : AM Bool := do
  let r ← nestOccGo names lo hi ∅ coreWalkFuel e
  pure r.1

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:514-519 instPisWith
Instantiate the leading `Π` binders of `e` at `args`, in order; `none` when
`e` runs out of binders first. -/
def instPisWith : List EIdx → EIdx → AM (Option EIdx)
  | [], e => pure (some e)
  | a :: args, e => do
    if e.tag == ETag.forallE then
      match ← viewBind e with
      | none => failDanglingE
      | some (_, body, _) => do
        let b ← instantiate1Fast coreWalkFuel body a 0
        instPisWith args b
    else pure none

/-! ## The records -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:521-528 NestKey
A container INSTANTIATION `C.{lvls} Ds`, the key of the only cache there is.
`lvls` is the interned level list (a `const` node's own); the cited
`DecidableEq` is handle equality componentwise. -/
structure NestKey where
  cname : NIdx
  lvls : LsIdx
  ds : List EIdx
  deriving BEq, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:530-536 NestHole
A HOLE of the walk: the instantiation it stands for, and the first hole index
of its frame. -/
structure NestHole where
  key : NestKey
  base : Nat
  deriving BEq, Inhabited

/-! ## The input-derived fuel -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:553-554 fuelSlack
The fuel's slack above the term's depth. -/
def fuelSlack : Nat := 1024

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:556-588 Expr.depthGo
The longest root-to-leaf path (`fvar` annotations not descended), memoised on
the node, so a DAG costs its distinct nodes. -/
def depthGo (memo : Std.HashMap EIdx Nat) : Nat → EIdx → AM (Nat × Std.HashMap EIdx Nat)
  | 0, _ => fail (.internal "fuel exhausted: depth")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure (1, memo)
    | .fvar _ _ => pure (1, memo)
    | .sort _ => pure (1, memo)
    | .const _ _ => pure (1, memo)
    | .lit _ => pure (1, memo)
    | v =>
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let (r, m) ← match v with
          | .app f a => do
            let (d1, m) ← depthGo memo fuel f
            let (d2, m2) ← depthGo m fuel a
            pure (max d1 d2 + 1, m2)
          | .lam ty body _ => do
            let (d1, m) ← depthGo memo fuel ty
            let (d2, m2) ← depthGo m fuel body
            pure (max d1 d2 + 1, m2)
          | .forallE ty body _ => do
            let (d1, m) ← depthGo memo fuel ty
            let (d2, m2) ← depthGo m fuel body
            pure (max d1 d2 + 1, m2)
          | .letE ty val body => do
            let (d1, m) ← depthGo memo fuel ty
            let (d2, m2) ← depthGo m fuel val
            let (d3, m3) ← depthGo m2 fuel body
            pure (max (max d1 d2) d3 + 1, m3)
          | .proj _ _ x => do
            let (d, m) ← depthGo memo fuel x
            pure (d + 1, m)
          | _ => pure (1, memo)
        pure (r, m.insert h r)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:590-592 Expr.depth
A term's depth, memoised. -/
def depth (e : EIdx) : AM Nat := do
  let r ← depthGo ∅ coreWalkFuel e
  pure r.1

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:594-596 whnfWalkFuel
The fuel of a walk through whnf starting at `e`: its depth plus the slack. -/
def whnfWalkFuel (e : EIdx) : AM Nat := do
  let d ← depth e
  pure (d + fuelSlack)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:598-608 NestFieldKind
The field's kind as the run found it. -/
inductive NestFieldKind where
  | ordinary
  | recursive (tgt : Nat)
  | reflexive (tgt : Nat)
  | inProgress
  | nested (refl : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:610-613 NestFieldKind.flat
A field kind the uniform route installs: no container instantiation. -/
def NestFieldKind.flat : NestFieldKind → Bool
  | .ordinary | .recursive _ | .reflexive _ => true
  | _ => false

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:615-619 nestKindsFlat
Every field of every constructor of every member is flat. -/
def nestKindsFlat (kss : List (List (List NestFieldKind))) : Bool :=
  kss.all (·.all (·.all NestFieldKind.flat))

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:621-641 NestCtorNf
A constructor's walked normal form, recorded (K.53′): the constructor, the
class's levels and parameters, and its walked field telescope, all read
back. -/
structure NestCtorNf where
  ctor : NIdx
  lvls : LsIdx
  ds : List EIdx
  ty : EIdx
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:643-654 NestCtx
The block, as the function needs it.  `find?` is the `fe` every reader takes
beside the record (the module note; the Rust's `vis` is `fe.visibleBelow`);
`lvls` is `lps.map .param`, interned once. -/
structure NestCtx where
  names : List NIdx
  lps : List NIdx
  nP : Nat
  nIdxs : List Nat
  params : List EIdx
  sort : LIdx
  lvls : LsIdx
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:656-668 NestState
The run's state: the accepted instantiations (the cache), the instantiations
in progress (innermost first), and every derived node's constructors
normalised and read back, in walk order. -/
structure NestState where
  keys : Array NestKey := #[]
  active : List NestKey := []
  ctorNfs : Array NestCtorNf := #[]
  deriving Inhabited

/-! ## Containers -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:684-695 nestCtorEntry
A stored constant's entry as a constructor of `C`: a constructor record whose
result, past its parameters and fields, is headed by `C`. -/
def nestCtorEntry (C : NIdx) (ci : IConstantInfo) :
    AM (Option (IConstantVal × Nat × Nat)) := do
  match ci with
  | .ctorInfo cv nPc nF =>
    match ← stripPis (nPc + nF) cv.type with
    | none => pure none
    | some q => do
      let hd ← getAppFn coreWalkFuel q.2
      if hd.tag == ETag.const then
        match ← viewConst hd with
        | none => failDanglingE
        | some (n, _) => if n == C then pure (some (cv, nPc, nF)) else pure none
      else pure none
  | _ => pure none

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:697-712 nestContainer
The constructors of the inductive `C` and its parameter count, looked up by
the names its stored record lists (`IndCaps.ctors`); for an inductive without
constructors its RECORDED parameter count (`IndCaps.nparams`); `none` when `C`
is no inductive.  Takes the lookup `fe` rather than the whole context. -/
def nestContainer (fe : IFEnv) (C : NIdx) :
    AM (Option (Nat × List (IConstantVal × Nat))) := do
  match fe.find? C with
  | some (.indInfo _ caps) => do
    let cs ← caps.ctors.filterMapM fun n =>
      match fe.find? n with
      | some ci => nestCtorEntry C ci
      | none => pure none
    match cs with
    | [] => pure (some (caps.nparams, []))
    | c :: _ => pure (some (c.2.1, cs.map fun c => (c.1, c.2.2)))
  | _ => pure none

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:714-716 nestNonValid
Official's "non valid occurrence". -/
def nestNonValid : CheckError :=
  .invalid "nested positivity: non valid occurrence of the datatypes being declared"

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:718-721 NestCtx.hiAt
The first hole-free variable index of a walk under `nf` frames. -/
def NestCtx.hiAt (ctx : NestCtx) (nf : Nat) : Nat :=
  ctx.nP + ctx.names.length + nf

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:723-727 NestCtx.rootHoles
The ROOT frame's entries: each member at the block's own levels and canonical
parameters, base `nP`. -/
def NestCtx.rootHoles (ctx : NestCtx) : List NestHole :=
  ctx.names.map fun n => { key := ⟨n, ctx.lvls, ctx.params⟩, base := ctx.nP }

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:729-734 nestHoleAt
The hole `i`'s entry under the frames `prog`: the stack read root first — the
root frame's entries, then `prog` from the outside (`prog` IS that order, the
module note); `none` off the holes. -/
def nestHoleAt (ctx : NestCtx) (prog : List NestHole) (i : Nat) : Option NestHole :=
  if ctx.nP ≤ i then (ctx.rootHoles ++ prog)[i - ctx.nP]? else none

/-! ## Reading a walked term back: `replaceFVars` and its four maps -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:744-757 Expr.replaceFVars
The function argument of `replaceFVars`, one variant per instantiation
con-leche writes (the module note): `nestHoleImg ctx prog` (at the stack
prefix of length `n`), `nestKeyMap ds holes`, `eraseFVarTys`' `fun i => some
(.fvar i (.sort .zero))` and `targetCanonParams`' `fun i => pfvs[i]?`. -/
inductive FvMap where
  | holeImg (ctx : NestCtx) (prog : List NestHole) (n : Nat)
  | keyMap (ds holes : List EIdx)
  | erase
  | canon (pfvs : List EIdx)

/-- con-leche: none — the termination measure of the readback's mutual
recursion: a `holeImg` map reads back through the stack prefix below its own
length, which is shorter. -/
def FvMap.rank : FvMap → Nat
  | .holeImg _ _ n => n + 1
  | _ => 0

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1104-1108 nestKeyMap
The variable replacement of a key: the canonical parameter variable `i` to
`ds[i]`, the canonical hole `|ds| + m` to `holes[m]`.  Placed ahead of
`fvMapAt`, which dispatches to it. -/
def nestKeyMap (ds holes : List EIdx) (i : Nat) : Option EIdx :=
  if i < ds.length then ds[i]? else holes[i - ds.length]?

mutual

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:744-757 Expr.replaceFVars
The map `f` applied to the variable `i`, by the variant. -/
def fvMapAt (f : FvMap) (i : Nat) : AM (Option EIdx) := do
  match f with
  | .holeImg ctx prog n => nestHoleImg ctx prog n i
  | .keyMap ds holes => pure (nestKeyMap ds holes i)
  | .erase => do
    let z ← zeroLevel
    let s ← internSortE z
    let v ← internFVarE i s
    pure (some v)
  | .canon pfvs => pure pfvs[i]?
termination_by (f.rank, 0, 0)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def, FvMap.rank] at *; (try split at *) <;> (try simp_all) <;> omega)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:744-757 Expr.replaceFVars
con-leche: ConLeche/Kernel/Inductives/Positivity.lean:775-810 Expr.replaceFVarsGo
Replace the free variables `f` maps (a mapped variable is replaced whole, its
annotation not descended into), memoised on the node. -/
def replaceFVarsGo (f : FvMap) (memo : Std.HashMap EIdx EIdx) (fuel : Nat) (h : EIdx) :
    AM (EIdx × Std.HashMap EIdx EIdx) := do
  match fuel with
  | 0 => fail (.internal "fuel exhausted: replaceFVars")
  | fuel + 1 =>
    match ← view h with
    | .bvar _ => pure (h, memo)
    | .sort _ => pure (h, memo)
    | .lit _ => pure (h, memo)
    | .const _ _ => pure (h, memo)
    | .fvar i _ =>
      match ← fvMapAt f i with
      | some r => pure (r, memo)
      | none => pure (h, memo)
    | v =>
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let (r, m) ← match v with
          | .app a b => do
            let (a2, m) ← replaceFVarsGo f memo fuel a
            let (b2, m2) ← replaceFVarsGo f m fuel b
            let r ← internAppE a2 b2
            pure (r, m2)
          | .lam ty body bm => do
            let (t2, m) ← replaceFVarsGo f memo fuel ty
            let (b2, m2) ← replaceFVarsGo f m fuel body
            let r ← internLamE t2 b2 bm
            pure (r, m2)
          | .forallE ty body bm => do
            let (t2, m) ← replaceFVarsGo f memo fuel ty
            let (b2, m2) ← replaceFVarsGo f m fuel body
            let r ← internForallEE t2 b2 bm
            pure (r, m2)
          | .letE ty val body => do
            let (t2, m) ← replaceFVarsGo f memo fuel ty
            let (v2, m2) ← replaceFVarsGo f m fuel val
            let (b2, m3) ← replaceFVarsGo f m2 fuel body
            let r ← internLetEE t2 v2 b2
            pure (r, m3)
          | .proj s i sub => do
            let (u, m) ← replaceFVarsGo f memo fuel sub
            let r ← internProjE s i u
            pure (r, m)
          -- the leaves are answered above and never reach here
          | _ => pure (h, memo)
        pure (r, m.insert h r)
termination_by (f.rank, 0, fuel)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def, FvMap.rank] at *; (try split at *) <;> (try simp_all) <;> omega)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:875-877 Expr.replaceFVarsFast
The executed `replaceFVars` (one memoised DAG walk, a fresh memo per
call). -/
def replaceFVars (f : FvMap) (e : EIdx) : AM EIdx := do
  let r ← replaceFVarsGo f ∅ coreWalkFuel e
  pure r.1
termination_by (f.rank, 1, 0)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def, FvMap.rank] at *; (try split at *) <;> (try simp_all) <;> omega)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:884-900 nestHoleImg
**The holes read back** under the frames `prog[..n]` (the stack prefix of
length `n`, its last element the innermost frame): member `m`'s hole `nP + m`
is `T_m.{lps} p⃗`, a frame's hole its container applied to the frame's
parameters, themselves read back under the frames below it. -/
def nestHoleImg (ctx : NestCtx) (prog : List NestHole) (n i : Nat) :
    AM (Option EIdx) := do
  match n with
  | 0 =>
    if ctx.nP ≤ i && i < ctx.hiAt 0 then do
      let nm := ctx.names.getD (i - ctx.nP) default
      let hd ← internConstE nm ctx.lvls
      let r ← mkAppN hd ctx.params
      pure (some r)
    else pure none
  | n + 1 =>
    if i == ctx.hiAt n then do
      let h := prog.getD n default
      let f := FvMap.holeImg ctx prog n
      let ds ← h.key.ds.mapM fun x => replaceFVars f x
      let hd ← internConstE h.key.cname h.key.lvls
      let r ← mkAppN hd ds
      pure (some r)
    else nestHoleImg ctx prog n i
termination_by (n, 2, 0)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def, FvMap.rank] at *; (try split at *) <;> (try simp_all) <;> omega)

end

/-! ## The whole-application abstraction (`replaceApps` at `nestCanonSub`) -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:917-923 Expr.phApp?
`e` is a constant applied to EXACTLY the placeholder variables `fvar b, …,
fvar (b + n - 1)` (annotations not compared): the constant's name and
levels. -/
def phApp? (b : Nat) : EIdx → Nat → AM (Option (NIdx × LsIdx))
  | e, 0 => do
    if e.tag == ETag.const then
      match ← viewConst e with
      | none => failDanglingE
      | some (c, us) => pure (some (c, us))
    else pure none
  | e, n + 1 => do
    if e.tag == ETag.app then
      match ← viewApp e with
      | none => failDanglingE
      | some (f, a) =>
        if a.tag == ETag.fvar then
          match ← viewFVarIdx a with
          | none => failDanglingE
          | some j => if j == b + n then phApp? b f n else pure none
        else pure none
    else pure none

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1089-1095 nestCanonSub
**The canonical whole-application substitution** of the group `names` at the
levels `us` over `n` parameters: member `m` to the canonical hole `fvar (n +
m)`; `v == us` is interned-list handle equality. -/
def nestCanonSub (names : List NIdx) (us : LsIdx) (n : Nat) (c : NIdx) (v : LsIdx) :
    AM (Option EIdx) := do
  if v == us then
    match names.findIdx? (· == c) with
    | none => pure none
    | some m => do
      let z ← zeroLevel
      let s ← internSortE z
      let r ← internFVarE (n + m) s
      pure (some r)
  else pure none

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:925-928 Expr.appHole?
The hole a whole application is replaced by (`nestCanonSub` at its
constant). -/
def appHole? (names : List NIdx) (us : LsIdx) (b n : Nat) (e : EIdx) :
    AM (Option EIdx) := do
  match ← phApp? b e n with
  | none => pure none
  | some (c, v) => nestCanonSub names us n c v

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:930-947 Expr.replaceApps
con-leche: ConLeche/Kernel/Inductives/Positivity.lean:966-1004 Expr.replaceAppsGo
**The whole-application replacement**, pre-order, at `nestCanonSub names us`:
a subterm that is a whole application is replaced by its hole and not
descended into; free variables are leaves.  Memoised on the node. -/
def replaceAppsGo (names : List NIdx) (us : LsIdx) (b n : Nat)
    (memo : Std.HashMap EIdx EIdx) : Nat → EIdx → AM (EIdx × Std.HashMap EIdx EIdx)
  | 0, _ => fail (.internal "fuel exhausted: replaceApps")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure (h, memo)
    | .sort _ => pure (h, memo)
    | .lit _ => pure (h, memo)
    | .fvar _ _ => pure (h, memo)
    | .const _ _ =>
      match ← appHole? names us b n h with
      | some r => pure (r, memo)
      | none => pure (h, memo)
    | v =>
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let (r, m) ← match v with
          | .app a x => do
            match ← appHole? names us b n h with
            | some r => pure (r, memo)
            | none => do
              let (a2, m) ← replaceAppsGo names us b n memo fuel a
              let (x2, m2) ← replaceAppsGo names us b n m fuel x
              let r ← internAppE a2 x2
              pure (r, m2)
          | .lam t body bm => do
            let (t2, m) ← replaceAppsGo names us b n memo fuel t
            let (b2, m2) ← replaceAppsGo names us b n m fuel body
            let r ← internLamE t2 b2 bm
            pure (r, m2)
          | .forallE t body bm => do
            let (t2, m) ← replaceAppsGo names us b n memo fuel t
            let (b2, m2) ← replaceAppsGo names us b n m fuel body
            let r ← internForallEE t2 b2 bm
            pure (r, m2)
          | .letE t val body => do
            let (t2, m) ← replaceAppsGo names us b n memo fuel t
            let (v2, m2) ← replaceAppsGo names us b n m fuel val
            let (b2, m3) ← replaceAppsGo names us b n m2 fuel body
            let r ← internLetEE t2 v2 b2
            pure (r, m3)
          | .proj s i x => do
            let (x2, m) ← replaceAppsGo names us b n memo fuel x
            let r ← internProjE s i x2
            pure (r, m)
          | _ => pure (h, memo)
        pure (r, m.insert h r)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1077-1079 Expr.replaceAppsFast
The executed `replaceApps` at `nestCanonSub names us n` (one memoised DAG
walk). -/
def replaceApps (names : List NIdx) (us : LsIdx) (b n : Nat) (e : EIdx) : AM EIdx := do
  let r ← replaceAppsGo names us b n ∅ coreWalkFuel e
  pure r.1

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1086-1087 nestPhs
The canonical parameter variables `fvar 0, …, fvar (n - 1)` at `Sort 0`. -/
def nestPhs (n : Nat) : AM (List EIdx) :=
  (List.range n).mapM fun i => do
    let z ← zeroLevel
    let s ← internSortE z
    internFVarE i s

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1097-1102 nestCanonCrest
**A stored constructor type, canonically abstracted**: instantiated at the
canonical parameter variables, every whole application of a member of `names`
at the levels `us` replaced by its canonical hole. -/
def nestCanonCrest (names : List NIdx) (us : LsIdx) (n : Nat) (cty : EIdx) :
    AM (Option EIdx) := do
  let phs ← nestPhs n
  match ← instPisWith phs cty with
  | none => pure none
  | some t => do
    let r ← replaceApps names us 0 n t
    pure (some r)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1110-1116 nestCrest
**A stored constructor type at a key**: its canonical abstraction, then the
key's parameters and the frame's holes put in. -/
def nestCrest (names : List NIdx) (us : LsIdx) (ds holes : List EIdx) (cty : EIdx) :
    AM (Option EIdx) := do
  match ← nestCanonCrest names us ds.length cty with
  | none => pure none
  | some c => do
    let r ← replaceFVars (.keyMap ds holes) c
    pure (some r)

/-! ## The container's former, and a frame's constructors -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1118-1158 nestInstType
The instantiation's type former, checked as official checks the auxiliary
type before the block exists: the level count, the parameters bound, (N2) the
index telescope names no member and no hole below `hi`, (N3) the sort is
`Level.isEquiv` the block's.  Returns the index count and the container's type
at the key (the type of the frame's hole). -/
def nestInstType (fe : IFEnv) (ctx : NestCtx) (hi : Nat) (key : NestKey) :
    AM (Nat × EIdx) := do
  let cvC ← unwrapOr
    (match fe.find? key.cname with
     | some (.indInfo cv _) => some cv
     | _ => none)
    (.internal "nested positivity: container vanished")
  match ← viewLsLen key.lvls with
  | none => failDanglingLs
  | some nl =>
    if nl != cvC.levelParams.length then
      fail (.invalid "nested positivity: incorrect number of universe levels for a nested inductive datatype (official: incorrect number of universe levels)")
    else
      match ← stripPis key.ds.length cvC.type with
      | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind its parameters (official: ill-formed inductive type)")
      | some _ => do
        let tl ← instLPFast coreWalkFuel cvC.levelParams key.lvls cvC.type
        match ← instPisWith key.ds tl with
        | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind its parameters (official: ill-formed inductive type)")
        | some ty => do
          let (bs, res) ← piBinders coreWalkFuel ty
          match ← view res with
          | .sort s => do
            if ← bs.anyM (fun b => nestOcc ctx.names ctx.nP hi b.1) then
              fail (.invalid "nested positivity: a container's index telescope mentions the block (official: unknown constant)")
            else do
              let o ← lvlEq? s ctx.sort
              let ok ← liftFueled "level comparison" o
              if ok then pure (bs.length, ty)
              else fail (.invalid "nested positivity: mutually inductive types must live in the same universe")
          | _ => fail (.invalid "nested positivity: invalid nested inductive datatype, its type is not a telescope ending in a sort (official: type expected)")

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1160-1167 nestResHead
A constructor's result is headed by a variable (its hole). -/
def nestResHead (e : EIdx) : AM Bool := do
  let hd ← getAppFn coreWalkFuel e
  pure (hd.tag == ETag.fvar)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1188-1196 nestCtorNf
**A frame constructor's record** (K.53′): the constructor at the frame's key
`(us, ds)` under the frames `prog`, its walked telescope `closed`
(con-leche's `closeTelescope nds hi cur`, computed once by the caller), all
read back.  Placed ahead of the `nestPos` block, which calls it. -/
def nestCtorNf (ctx : NestCtx) (prog : List NestHole) (us : LsIdx) (ds : List EIdx)
    (cv : IConstantVal) (closed : EIdx) : AM NestCtorNf := do
  let f := FvMap.holeImg ctx prog prog.length
  let ds2 ← ds.mapM fun x => replaceFVars f x
  let ty ← replaceFVars f closed
  pure { ctor := cv.name, lvls := us, ds := ds2, ty }

/-! ## A container frame's helpers -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1264-1276 nestGroupCtors
The constructors of every container in `cs` (at one parameter count), looked
up; `ctors ++ rest` with the head's effects first, as an accumulator. -/
def nestGroupCtors (fe : IFEnv) (nPc : Nat) :
    List NIdx → List (IConstantVal × Nat) → AM (List (IConstantVal × Nat))
  | [], out => pure out
  | c :: cs, out => do
    match ← nestContainer fe c with
    | none => fail nestNonValid
    | some (nPc2, ctors) =>
      if !(nPc2 == nPc || ctors.length == 0) then
        fail (.invalid "nested positivity: number of parameters mismatch in inductive datatype declaration (a container's group)")
      else nestGroupCtors fe nPc cs (out ++ ctors)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1278-1283 nestBlockOf
The recorded block of the inductive `C` (`IndCaps.all`): `[]` when none is
recorded. -/
def nestBlockOf (fe : IFEnv) (C : NIdx) : List NIdx :=
  match fe.find? C with
  | some (.indInfo _ caps) => caps.all
  | _ => []

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1285-1291 nestFrameMates
**A frame's group-mates** (N2-eager): every OTHER member of the container
`C`'s recorded block, each once — the cited `eraseDups` then `filter (· !=
C)` in one pass keeping first occurrences. -/
def nestFrameMates (fe : IFEnv) (C : NIdx) : List NIdx :=
  let rec go : List NIdx → List NIdx → List NIdx
    | [], out => out
    | n :: ns, out =>
      if n == C || out.contains n then go ns out else go ns (out ++ [n])
  go (nestBlockOf fe C) []

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1293-1307 nestArity
**A frame hole's full arity**: its container member's recorded type's binder
count. -/
def nestArity (fe : IFEnv) (C : NIdx) : AM Nat := do
  match fe.find? C with
  | some (.indInfo cv _) => do
    let (bs, _) ← piBinders coreWalkFuel cv.type
    pure bs.length
  | _ => pure 0

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1309-1316 nestGrowGroup
A frame's group grown by the named containers, each at the frame's
instantiation, its hole typed by its instantiated former. -/
def nestGrowGroup (fe : IFEnv) (ctx : NestCtx) (hi : Nat) (us : LsIdx) (ds : List EIdx) :
    List NIdx → List (NIdx × EIdx) → AM (List (NIdx × EIdx))
  | [], grp => pure grp
  | c :: cs, grp => do
    let (_, cty) ← nestInstType fe ctx hi ⟨c, us, ds⟩
    nestGrowGroup fe ctx hi us ds cs (grp ++ [(c, cty)])

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1318-1325 nestAcceptGroup
A frame's group accepted with its instantiation: every member at `(us, ds)`
cached, those not cached yet. -/
def nestAcceptGroup (us : LsIdx) (ds : List EIdx) :
    List (NIdx × EIdx) → Array NestKey → Array NestKey
  | [], keys => keys
  | (c, _) :: grp, keys =>
    let k : NestKey := ⟨c, us, ds⟩
    if keys.contains k then nestAcceptGroup us ds grp keys
    else nestAcceptGroup us ds grp (keys.push k)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1353-1357 nestWalkStack
**The frame stack an instantiation is walked under**: the EMPTY one when its
parameters mention no frame hole (`ds.all (·.fvarB ≤ hiAt 0)`, in order,
stopping at the first failure), else the frames it was met under. -/
def nestWalkStack (ctx : NestCtx) (prog : List NestHole) (ds : List EIdx) :
    AM (List NestHole) := do
  let closed ← ds.allM fun x => do
    let b ← fvarB coreWalkFuel x
    pure (decide (b ≤ ctx.hiAt 0))
  if closed then pure [] else pure prog

/-! ## The positivity function and the container frames

One mutual block: a frame walks its constructors' fields through `nestPos`,
and `nestPos` opens a frame at a container.  The measure is the fuel, with the
root frame's constructors (`root`, each at its own input-derived fuel) above
every fuel. -/

mutual

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1169-1186 nestFields
A constructor's field telescope `cur` (`nF` fields from field `j`), each field
through the walk at its depth `base + j`, the field opened at the variable
`base + j` (annotated by its DECLARED domain): the fields' kinds, their walked
forms, and the result.  The accumulators are appended to on the way in, as
the Rust pushes (the same order of effects as con-leche's cons on the way
out). -/
def nestFields (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat)
    (prog : List NestHole) (base nF j : Nat) (cur : EIdx) (ns : NestState)
    (ks : List NestFieldKind) (nds : List (EIdx × BinderMeta)) :
    AM (List NestFieldKind × List (EIdx × BinderMeta) × EIdx × NestState) := do
  match nF with
  | 0 => pure (ks, nds, cur, ns)
  | nF + 1 =>
    if cur.tag == ETag.forallE then
      match ← viewBind cur with
      | none => failDanglingE
      | some (a, b, bm) => do
        let (k, nd, ns2) ← nestPos mode fe ctx fuel prog (base + j) 0 a ns
        let fv ← internFVarE (base + j) a
        let b2 ← instantiate1Fast coreWalkFuel b fv 0
        nestFields mode fe ctx fuel prog base nF (j + 1) b2 ns2 (ks ++ [k]) (nds ++ [(nd, bm)])
    else
      fail (.invalid "nested positivity: invalid nested inductive datatype, its constructor type does not bind its fields (official: ill-formed constructor)")
termination_by (0, fuel, 1, nF)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def] at *; (try split at *) <;> (try simp_all) <;> omega)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1198-1262 nestCtors
**A frame's constructors**, the root frame's (`root`: each constructor walked
at the input-derived fuel of its instantiated type) and every container
frame's (at the enclosing walk's `fuel`) alike: each with the frame's group
abstracted (`nestCrest`), TYPED at the frame's context, its fields walked
above `hi`, U4 (a non-ordinary field read later, the kind tested first), its
result headed by its hole with hole-free indices (the head tested first), and
its walked normal form recorded.  Returns every constructor's kinds and walked
form, in order. -/
def nestCtors (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (root : Bool) (fuel : Nat)
    (prog : List NestHole) (hi : Nat) (us : LsIdx) (ds : List EIdx) (names : List NIdx)
    (holes : List EIdx) (cs : List (IConstantVal × Nat)) (ns : NestState)
    (outs : List (List NestFieldKind × EIdx)) :
    AM (List (List NestFieldKind × EIdx) × NestState) := do
  match cs with
  | [] => pure (outs, ns)
  | (cv, nF) :: cs' =>
    if !nameNodup cv.levelParams then
      fail (.invalid "nested positivity: invalid nested inductive datatype, its constructor has a duplicate universe level parameter (official: duplicate universe level parameter)")
    else do
      let cty ← instLPFast coreWalkFuel cv.levelParams us cv.type
      match ← nestCrest names us ds holes cty with
      | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its constructor type does not bind the parameters (official: ill-formed constructor)")
      | some crest => do
        let ty ← inferTypeCore mode fe checkFuel hi crest
        let _ ← ensureSortCore mode fe checkFuel hi ty
        let (ks, nds, cur, ns2) ←
          if _h : root = true then do
            let fuelC ← whnfWalkFuel crest
            nestFields mode fe ctx fuelC prog hi nF 0 crest ns [] []
          else nestFields mode fe ctx fuel prog hi nF 0 crest ns [] []
        let closed ← closeTelescope nds hi cur
        let u4 ← (List.range nF).anyM fun i =>
          if (ks[i]?.map (· == .ordinary)).getD true then pure false
          else structUsedLater closed 0 i
        if u4 then
          fail (.invalid "nested positivity: non valid occurrence of the datatypes being declared (a later field or the result depends on a recursive or nested field)")
        else do
          let resOk ← do
            if ← nestResHead cur then do
              let args ← getAppArgs coreWalkFuel cur
              let occ ← args.anyM fun x => nestOcc ctx.names ctx.nP hi x
              pure !occ
            else pure false
          if !resOk then
            fail (.invalid "nested positivity: invalid return type — a constructor's result index mentions the block")
          else do
            let nf ← nestCtorNf ctx prog us ds cv closed
            let ns3 := { ns2 with ctorNfs := ns2.ctorNfs.push nf }
            nestCtors mode fe ctx root fuel prog hi us ds names holes cs' ns3 (outs ++ [(ks, closed)])
termination_by (if root then 1 else 0, fuel, 2, cs.length)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def] at *; (try split at *) <;> (try simp_all) <;> omega)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1327-1351 nestFrame
**A container frame** at the instantiation `(us, ds)`: the instantiation
`hn.{us} ds` TYPED at the frame's depth (K.52), its holes the container's
WHOLE recorded group `grp`, every one of their constructors walked with all
of them abstracted, in one pass (N2-eager).  `grp` is never empty (it starts
at the instantiation met); the cited `grp.headD default` falls back to the
anonymous name, which the twin interns.  The stack grows by the group's holes
at its OUTER end's opposite — appended, the module note. -/
def nestFrame (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat)
    (prog : List NestHole) (hi : Nat) (us : LsIdx) (ds : List EIdx) (nPc : Nat)
    (grp : List (NIdx × EIdx)) (ns : NestState) : AM NestState := do
  let hn ← match grp with
    | [] => internNNode .anonymous
    | (c, _) :: _ => pure c
  let hc ← internConstE hn us
  let app ← mkAppN hc ds
  let _ ← inferTypeCore mode fe checkFuel hi app
  let prog2 := prog ++ grp.map fun (c, _) => { key := ⟨c, us, ds⟩, base := hi }
  let names := grp.map (·.1)
  let ctors ← nestGroupCtors fe nPc names []
  let holes ← grp.zipIdx.mapM fun ((_, ty), i) => internFVarE (hi + i) ty
  let (_, ns2) ← nestCtors mode fe ctx false fuel prog2 (hi + grp.length) us ds names
    holes ctors ns []
  pure ns2
termination_by (0, fuel, 3, 0)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def] at *; (try split at *) <;> (try simp_all) <;> omega)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1359-1382 nestContNew
An instantiation's frame: the group-mates' former checks, the frame walked
with the whole group in progress, and the whole group cached when its
parameters mention no frame hole. -/
def nestContNew (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat)
    (prog : List NestHole) (kb : Nat) (n : NIdx) (us : LsIdx) (ds : List EIdx)
    (nPc : Nat) (cty : EIdx) (ns : NestState) : AM (NestFieldKind × NestState) := do
  let wp ← nestWalkStack ctx prog ds
  let mates := nestFrameMates fe n
  let hw := ctx.hiAt wp.length
  let grp ← nestGrowGroup fe ctx hw us ds mates [(n, cty)]
  let act := ns.active
  let active := grp.map (fun (c, _) => (⟨c, us, ds⟩ : NestKey)) ++ ns.active
  let ns1 : NestState := { keys := ns.keys, active, ctorNfs := ns.ctorNfs }
  let ns2 ← nestFrame mode fe ctx fuel wp hw us ds nPc grp ns1
  let closed ← ds.allM fun x => do
    let b ← fvarB coreWalkFuel x
    pure (decide (b ≤ ctx.hiAt 0))
  let keys := if closed then nestAcceptGroup us ds grp ns2.keys else ns2.keys
  pure (.nested (kb != 0), { keys, active := act, ctorNfs := ns2.ctorNfs })
termination_by (0, fuel, 4, 0)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def] at *; (try split at *) <;> (try simp_all) <;> omega)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1384-1404 nestContKey
The instantiation `(n, us, ds)` met: IN PROGRESS (met as a constant, which
only reduction produces: official's "non valid occurrence"); cached — a hit,
but only when its parameters mention no frame hole; else a new frame. -/
def nestContKey (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat)
    (prog : List NestHole) (kb : Nat) (n : NIdx) (us : LsIdx) (ds : List EIdx)
    (nPc : Nat) (cty : EIdx) (ns : NestState) : AM (NestFieldKind × NestState) := do
  let key : NestKey := ⟨n, us, ds⟩
  if ns.active.contains key then
    fail (.invalid "nested positivity: non valid occurrence of the datatypes being declared (an instantiation in progress, reached through reduction)")
  else do
    let closed ← ds.allM fun x => do
      let b ← fvarB coreWalkFuel x
      pure (decide (b ≤ ctx.hiAt 0))
    if closed && ns.keys.contains key then pure (.nested (kb != 0), ns)
    else nestContNew mode fe ctx fuel prog kb n us ds nPc cty ns
termination_by (0, fuel, 5, 0)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def] at *; (try split at *) <;> (try simp_all) <;> omega)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1406-1440 nestCont
**The container case** of `nestPos`: the reduct is the stored inductive
`n.{us}` applied to `args`; its constructors looked up (`nestContainer`), its
checks (enough arguments and hole-free indices, not `Quot`, parameters without
local variables — `bvarB` read first), the instantiation's former
(`nestInstType`), full application; then the instantiation (`nestContKey`).
`fuel` is the walk's own, one lower. -/
def nestCont (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat)
    (prog : List NestHole) (kb : Nat) (n : NIdx) (us : LsIdx) (args : List EIdx)
    (ns : NestState) : AM (NestFieldKind × NestState) := do
  match ← nestContainer fe n with
  | none => fail nestNonValid
  | some (nPc, _) =>
    let hp := ctx.hiAt prog.length
    if args.length < nPc then fail nestNonValid
    else do
      let idx := args.drop nPc
      if ← idx.anyM (fun x => nestOcc ctx.names ctx.nP hp x) then fail nestNonValid
      else do
        let q ← pinQuot
        if n == q then fail nestNonValid
        else do
          let ds := args.take nPc
          let pc ← ds.allM fun x => do
            let bb ← bvarB coreWalkFuel x
            if bb != 0 then pure false
            else do
              let fb ← fvarB coreWalkFuel x
              pure (decide (fb ≤ hp))
          if !pc then
            fail (.invalid "nested positivity: nested inductive datatypes parameters cannot contain local variables")
          else do
            let (nI, cty) ← nestInstType fe ctx hp ⟨n, us, ds⟩
            if args.length != nPc + nI then
              fail (.invalid "nested positivity: type expected (a container instance that is not fully applied)")
            else nestContKey mode fe ctx fuel prog kb n us ds nPc cty ns
termination_by (0, fuel, 6, 0)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def] at *; (try split at *) <;> (try simp_all) <;> omega)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1442-1496 nestPos
**The positivity function**: the domain `e` at depth `dep`, `kb` `Π` binders
into the field, `prog` the instantiations in progress.  The reduct (the
kernel's own whnf) mentions no member and no hole — ordinary, its normal form
the input unless the input mentions one — or it is a `Π` whose domain is
hole-free (the codomain walked one binder in), a hole application at its full
arity with hole-free indices (official `is_valid_ind_app`: a member hole is
recursive, or reflexive under `Π` binders; a frame hole an instantiation in
progress), a stored inductive's application (`nestCont`), or official's "non
valid occurrence".  Running out of fuel DECLINES. -/
def nestPos (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat)
    (prog : List NestHole) (dep kb : Nat) (e : EIdx) (ns : NestState) :
    AM (NestFieldKind × EIdx × NestState) := do
  match fuel with
  | 0 => fail (.notImplemented "nested positivity: fuel")
  | fuel + 1 =>
    let hi := ctx.hiAt prog.length
    let w ← whnf mode fe checkFuel dep e
    if !(← nestOcc ctx.names ctx.nP hi w) then
      if ← nestOcc ctx.names ctx.nP hi e then pure (.ordinary, w, ns)
      else pure (.ordinary, e, ns)
    else if w.tag == ETag.forallE then
      match ← viewBind w with
      | none => failDanglingE
      | some (a, b, bm) =>
        if ← nestOcc ctx.names ctx.nP hi a then
          fail (.invalid "nested positivity: non positive occurrence of the datatypes being declared")
        else do
          let fv ← internFVarE dep a
          let b2 ← instantiate1Fast coreWalkFuel b fv 0
          let (k, nb, ns2) ← nestPos mode fe ctx fuel prog (dep + 1) (kb + 1) b2 ns
          let nb2 ← abstract1Fast coreWalkFuel nb dep 0
          let r ← internForallEE a nb2 bm
          pure (k, r, ns2)
    else do
      let args ← getAppArgs coreWalkFuel w
      let hd ← getAppFn coreWalkFuel w
      match ← view hd with
      | .fvar i _ =>
        match nestHoleAt ctx prog i with
        | none => fail nestNonValid
        | some h =>
          if ← args.anyM (fun x => nestOcc ctx.names ctx.nP hi x) then fail nestNonValid
          else do
            let ar ← nestArity fe h.key.cname
            if args.length + h.key.ds.length == ar then
              let k : NestFieldKind :=
                if i < ctx.hiAt 0 then
                  (if kb == 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP))
                else .inProgress
              pure (k, w, ns)
            else fail nestNonValid
      | .const n us =>
        if ctx.names.contains n then fail nestNonValid
        else do
          let (k, ns2) ← nestCont mode fe ctx fuel prog kb n us args ns
          pure (k, w, ns2)
      | _ => fail nestNonValid
termination_by (0, fuel, 0, 0)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def] at *; (try split at *) <;> (try simp_all) <;> omega)

end

/-! ## The member holes and the root frame's crest -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1498-1507 nestHoles
The member holes: member `m` is the free variable `nP + m`, typed by its
former's type instantiated at the canonical parameters; `none` when a member
is not a stored former or its type does not bind the parameters (the cited
`mapM`, as an accumulator recursion). -/
def nestHoles (fe : IFEnv) (ctx : NestCtx) : AM (Option (List EIdx)) :=
  let rec go : Nat → List NIdx → List EIdx → AM (Option (List EIdx))
    | _, [], out => pure (some out)
    | mm, n :: ns, out =>
      match fe.find? n with
      | some (.indInfo cv _) => do
        match ← instPisWith ctx.params cv.type with
        | none => pure none
        | some t => do
          let v ← internFVarE (ctx.nP + mm) t
          go (mm + 1) ns (out ++ [v])
      | _ => pure none
  go 0 ctx.names []

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1509-1515 nestRootCanon
**The root frame's canonical crest** of a member constructor: its whole member
applications abstracted, at the block's levels. -/
def nestRootCanon (ctx : NestCtx) (cv : IConstantVal) : AM (Option EIdx) := do
  let t ← instLPFast coreWalkFuel cv.levelParams ctx.lvls cv.type
  nestCanonCrest ctx.names ctx.lvls ctx.nP t

/-! ## Uniform occurrences: official's `check_uniform_ind_occs` -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1543-1548 Expr.piDomsOcc
Does a member or a hole occur in one of the first `n` binder domains of
`e`? -/
def piDomsOcc (names : List NIdx) (lo hi : Nat) : Nat → EIdx → AM Bool
  | 0, _ => pure false
  | n + 1, e => do
    if e.tag == ETag.forallE then
      match ← viewBind e with
      | none => failDanglingE
      | some (d, b, _) =>
        if ← nestOcc names lo hi d then pure true
        else piDomsOcc names lo hi n b
    else pure false

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1550-1559 nestUniformOk
**Official's `check_uniform_ind_occs` at one constructor**: the parameters'
domains name no member, and its canonical crest has no member constant
left. -/
def nestUniformOk (ctx : NestCtx) (cv : IConstantVal) : AM Bool := do
  if ← piDomsOcc ctx.names ctx.nP (ctx.hiAt 0) ctx.nP cv.type then pure false
  else
    match ← nestRootCanon ctx cv with
    | none => pure false
    | some crest => do
      let occ ← nestOcc ctx.names 0 0 crest
      pure !occ

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1561-1569 nestUniform
`nestUniformOk` at every stored constructor of every member, before the walk,
in order, stopping at the first failure: a REJECT with official's wording (the
constructor's name dropped, §3.1). -/
def nestUniform (ctx : NestCtx) : List (List (IConstantVal × Nat)) → AM Unit
  | [] => pure ()
  | cs :: ctorss => do
    if ← cs.allM (fun c => nestUniformOk ctx c.1) then nestUniform ctx ctorss
    else fail (.invalid "invalid occurrence of a datatype being declared in the type of : it must be applied to the parameters and universe levels of the mutual declaration")

/-! ## The root frame and the seeds -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1585-1600 nestRoot
**The root frame**: every member's constructors through `nestCtors` at the
root key (the block's levels, the canonical parameters, the holes above
them), member by member, sharing the walk's state; each constructor at the
input-derived fuel of its instantiated type. -/
def nestRoot (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (holes : List EIdx) :
    List (List (IConstantVal × Nat)) → NestState → List (List (List NestFieldKind × EIdx)) →
    AM (List (List (List NestFieldKind × EIdx)) × NestState)
  | [], ns, outs => pure (outs, ns)
  | cs :: ctorss, ns, outs => do
    let (o, ns2) ← nestCtors mode fe ctx true 0 [] (ctx.hiAt 0) ctx.lvls ctx.params
      ctx.names holes cs ns []
    nestRoot mode fe ctx holes ctorss ns2 (outs ++ [o])

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1630-1638 nestSeedOf
**A resolved class as a seed**: the outside class `I.{us} ds` in the walk's
representation — each parameter's whole member applications abstracted to
the canonical holes, then every free variable replaced whole by the canonical
parameter or the hole — with its parameter count. -/
def nestSeedOf (ctx : NestCtx) (holes : List EIdx) (I : NIdx) (us : LsIdx)
    (ds : List EIdx) (nPc : Nat) : AM (NestKey × Nat) := do
  let ds2 ← ds.mapM fun x => do
    let y ← replaceApps ctx.names ctx.lvls 0 ctx.nP x
    replaceFVars (.keyMap ctx.params holes) y
  pure (⟨I, us, ds2⟩, nPc)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1640-1654 nestSeeds
**The seeds walked**, in order, at the root: each class a container instance
met at the empty frame stack (`nestContKey`), at the fuel its parameters'
depths give (`key.ds.foldl (fun a d => max a (whnfWalkFuel d)) fuelSlack`,
left to right). -/
def nestSeeds (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) :
    List (NestKey × Nat) → NestState → AM NestState
  | [], ns => pure ns
  | (key, nPc) :: seeds, ns => do
    let f ← key.ds.foldlM (fun a d => do
      let w ← whnfWalkFuel d
      pure (max a w)) fuelSlack
    let (_, cty) ← nestInstType fe ctx (ctx.hiAt 0) key
    let (_, ns2) ← nestContKey mode fe ctx f [] 0 key.cname key.lvls key.ds nPc cty ns
    nestSeeds mode fe ctx seeds ns2

end ConRon.Arena
