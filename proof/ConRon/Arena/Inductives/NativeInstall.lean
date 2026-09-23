/-
# `ConRon.Arena.Inductives.NativeInstall` — the fixpoint route's install
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/NativeInstall.lean` whole, over handles: the
capability record, official's `is_rec`, the re-check of the field kinds on the
opened annotated constructors, the generated recursor and its rules, the
projection table at a structure-like block, and the two-pass install.

**The deviations of this module:**

* **The `…F` twins collapse into these** (task #97c's deviation 1), and with
  them the `StructWalkers` record every `F` function takes — the arena's
  `constsResolve` and `structProjBodies` ARE the memoised walks that record
  exists to substitute (`Arena/Inductives/StructInstallF.lean`'s note).  The
  `F` names live on as `abbrev`s in `Arena/Inductives/NativeInstallF.lean`.
* **`nativeCapsAt` is in `Arena/Inductives/SumInstall.lean`**, because
  `checkSumInd` calls it where con-leche passes it in as a closure; that
  module's note says why.
* **`NativePass` is not generic.**  con-leche parameterises it by the
  environment representation (`Env` at the pure install, `FEnv` at the cached
  driver's mirror); the arena has one.
* **`mentionsFvar` collapses its pure walk, its memoized walk and its entry
  into one twin**, as `Arena/Inductives/StructParts.lean` does for
  `hasLooseBVarB` and `mentionsConst`.  Its memo is keyed by the node alone —
  `q` is fixed for the walk — and con-leche's own note says why there is no
  derived-word cutoff to put in front of it: `fvarB` stops at an `fvar` leaf
  while the walk descends into the leaf's TYPE ANNOTATION.
-/
import ConRon.Arena.Inductives.NativeParts

namespace ConRon.Arena

open ConLeche

/-! ## The capability record -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:100-103 nativeIsRec
Official's `is_rec` off the classified kinds: some field is recursive or
reflexive. -/
def nativeIsRec (kinds : List (List RecFieldKind)) : Bool :=
  kinds.any fun ks => ks.any fun k => k == .recursive || k == .reflexive

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:105-108 nativeCaps
The block's capability record at its classified kinds. -/
def nativeCaps (p : NativeParts) : AM IIndCaps :=
  nativeCapsAt p.toInductiveShape (nativeIsRec p.kinds)

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:110-128 nativeRawRec
**The syntactic reading of `is_rec`** (task #268): does the block occur in some
declared field domain of some constructor? -/
def nativeRawRec (p : NativeParts) : AM Bool := do
  match p.ctors with
  | [c] => do
    match ← stripPis (p.nP + c.2) c.1.type with
    | some (cbs, _) =>
      (cbs.drop p.nP).anyM fun b => mentionsConst p.cvT.name b.1
    | none => pure false
  | _ => pure false

/-! ## `mentionsFvar` -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:214-219 Expr.mentionsFvarIns
Record one answer for `e` in the memo the walk hands back. -/
@[inline] def mentionsFvarIns (e : EIdx) (r : Bool × Std.HashMap EIdx Bool) :
    Bool × Std.HashMap EIdx Bool :=
  (r.1, r.2.insert e r.1)

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:139-141 Expr.mentionsFvar
con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:221-257 Expr.mentionsFvarGo
Does the variable `q` occur as a leaf of `e` (annotations included, as
`fvarLeaves` walks them)?  con-leche's per-call memo, keyed by the node. -/
def mentionsFvarGo (q : Nat) (memo : Std.HashMap EIdx Bool) :
    Nat → EIdx → AM (Bool × Std.HashMap EIdx Bool)
  | 0, _ => fail (.internal "fuel exhausted: mentionsFvar")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure (false, memo)
    | .sort _ => pure (false, memo)
    | .const _ _ => pure (false, memo)
    | .lit _ => pure (false, memo)
    | v =>
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let r ← match v with
          | .fvar idx ty =>
            if idx == q then pure (true, memo) else mentionsFvarGo q memo fuel ty
          | .app f a => do
            match ← mentionsFvarGo q memo fuel f with
            | (true, memo) => pure (true, memo)
            | (false, memo) => mentionsFvarGo q memo fuel a
          | .lam ty b _ => do
            match ← mentionsFvarGo q memo fuel ty with
            | (true, memo) => pure (true, memo)
            | (false, memo) => mentionsFvarGo q memo fuel b
          | .forallE ty b _ => do
            match ← mentionsFvarGo q memo fuel ty with
            | (true, memo) => pure (true, memo)
            | (false, memo) => mentionsFvarGo q memo fuel b
          | .letE t v b => do
            match ← mentionsFvarGo q memo fuel t with
            | (true, memo) => pure (true, memo)
            | (false, memo) => do
              match ← mentionsFvarGo q memo fuel v with
              | (true, memo) => pure (true, memo)
              | (false, memo) => mentionsFvarGo q memo fuel b
          | .proj _ _ sub => mentionsFvarGo q memo fuel sub
          | _ => pure (false, memo)
        pure (mentionsFvarIns h r)

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:379-381 Expr.mentionsFvarFast
The executed `mentionsFvar` (one memoized DAG walk). -/
def mentionsFvar (q : Nat) (e : EIdx) : AM Bool := do
  pure (← mentionsFvarGo q ∅ coreWalkFuel e).1

/-! ## The field kinds, re-checked on the opened constructors -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
The kinds the recogniser computed, re-checked on the annotated constructor type
OPENED at variables, in the form the model reads. -/
def nativeOpenedOk (fe₀ : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat)
    (cty : EIdx) (nF : Nat) (ks : List RecFieldKind) : AM Bool := do
  match ← openPisAtFvarsF nP cty 0 with
  | none => pure false
  | some (fvsP, crest) => do
    match ← openPisAtFvarsF nF crest nP with
    | none => pure false
    | some (xFvs, xrest) => do
      let us ← paramLevels lps
      let hd ← internE (.const T us)
      let xargs ← getAppArgs coreWalkFuel xrest
      let residOk ← (xargs.drop nP).allM fun e => constsResolveFFast fe₀ e
      if !residOk then pure false else
      (List.range nF).allM fun i => do
        match xFvs[i]? with
        | none => pure false
        | some x =>
          match ks.getD i .ordinary with
          | .ordinary => do constsResolveFFast fe₀ (← fvarTypeD x)
          | .recursive => do
            let xt ← fvarTypeD x
            let fn ← getAppFn coreWalkFuel xt
            let args ← getAppArgs coreWalkFuel xt
            if !(fn == hd && args.take nP == fvsP && args.length == nP + nIdx) then
              pure false
            else do
              let idxOk ← (args.drop nP).allM fun e => constsResolveFFast fe₀ e
              if !idxOk then pure false else do
              let later ← (xFvs.drop (i + 1)).anyM fun y => do
                mentionsFvar (nP + i) (← fvarTypeD y)
              if later then pure false else
              pure !(← mentionsFvar (nP + i) xrest)
          | .reflexive => do
            -- the field's own telescope, OPENED at variables at the field's
            -- depth (task #202)
            let xt ← fvarTypeD x
            let (tele, _) ← piBinders coreWalkFuel xt
            match ← openPisAtFvarsF tele.length xt (nP + i) with
            | none => pure false
            | some (afvs, body) => do
              if afvs.length == 0 then pure false else do
              let domsOk ← afvs.allM fun a => do constsResolveFFast fe₀ (← fvarTypeD a)
              if !domsOk then pure false else do
              let fn ← getAppFn coreWalkFuel body
              let args ← getAppArgs coreWalkFuel body
              if !(fn == hd && args.take nP == fvsP && args.length == nP + nIdx) then
                pure false
              else do
                let idxOk ← (args.drop nP).allM fun e => constsResolveFFast fe₀ e
                if !idxOk then pure false else do
                let later ← (xFvs.drop (i + 1)).anyM fun y => do
                  mentionsFvar (nP + i) (← fvarTypeD y)
                if later then pure false else
                pure !(← mentionsFvar (nP + i) xrest)
          | _ => pure false

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:435-445 nativeFieldsOk
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:61-69 nativeFieldsOkF
The kinds, re-checked on every annotated constructor, one kind list per
constructor, one kind per field. -/
def nativeFieldsOk (fe₀ : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat)
    (ctorsA : List (IConstantVal × Nat)) (kinds : List (List RecFieldKind)) :
    AM Bool := do
  if !(ctorsA.length == kinds.length) then pure false else
  (List.range ctorsA.length).allM fun j => do
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks => do
      if !(ks.length == cA.2) then pure false
      else nativeOpenedOk fe₀ T lps nP nIdx cA.1.type cA.2 ks
    | _, _ => pure false

/-! ## The recursor -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:447-463 checkNativeRules
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:71-85 checkNativeRulesF
The generated rules for constructors `j, j+1, …` (`k` of them), each scoped at
the environment holding the recursor's constant. -/
def checkNativeRules (feR : IFEnv) (rlps : List NIdx) (T : NIdx) (lps : List NIdx)
    (elim : NIdx) (large : Bool) (nP nIdx : Nat) (tty : EIdx)
    (ctors : List (NIdx × Nat × EIdx × List Nat)) (recC : NIdx) (rlvls : LsIdx) :
    Nat → Nat → AM (List EIdx)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (← structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (.internal "direct rec: recursor rule")
    unless (← allLevelParamsDefined rlps rhs) && (← constsResolveFFast feR rhs) &&
        (← looseBVarsBoundedFast coreWalkFuel 0 rhs) &&
        !(← hasFvarFast coreWalkFuel rhs) do
      fail (.internal "direct rec: recursor rule scoping")
    let rest ← checkNativeRules feR rlps T lps elim large nP nIdx tty ctors recC rlvls k
      (j + 1)
    pure (rhs :: rest)

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115 checkNativeRecF
Stage 3: the recursor, generated and compared — the generated type has the
inductive-hypothesis binders in each minor; the generated rules are scoped at
the environment holding the recursor's constant. -/
def checkNativeRec (mode : CheckMode) (fe : IFEnv) (p : NativeParts)
    (cvTa : IConstantVal) (ctorsA : List (IConstantVal × Nat)) :
    AM (IConstantVal × List EIdx) := do
  -- THE RECURSOR PIN (task #220): official generates the recursor and its
  -- replay compares the exported record with the generated one structurally
  let recName ← internNNode (.str p.cvT.name "rec")
  unless p.cvR.name == recName do
    fail (.invalid "direct rec: the block's recursor is not the generated T.rec")
  unless nativeRecLpsOk p.toInductiveShape do
    fail (.invalid "direct rec: the recursor's level parameters are not the generated ones")
  unless p.recPinned do
    fail (.invalid "direct rec: the recursor record is not the generated recursor")
  let cvRi ← checkConstantVal mode fe p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := nativeCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (← structRecTyR T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless (← allLevelParamsDefined p.cvR.levelParams recTy) &&
      (← constsResolveFFast fe recTy) &&
      (← looseBVarsBoundedFast coreWalkFuel 0 recTy) &&
      !(← hasFvarFast coreWalkFuel recTy) do
    fail (.internal "direct rec: recursor type scoping")
  let sty ← inferTypeCore mode fe checkFuel 0 recTy
  let _u ← ensureSortCore mode fe checkFuel 0 sty
  -- the stream's recursor is the generated one
  unless ← isDefEqCore mode fe checkFuel 0 cvRi.type recTy do
    fail (.invalid "direct rec: recursor type is not the generated one")
  let cvRa : IConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let feR := fe.push (.recInfo cvRa p.majorIdx p.rulePrefix [])
  let rlvls ← paramLevels p.cvR.levelParams
  let rhss ← checkNativeRules feR p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors p.cvR.name rlvls ctors.length 0
  pure (cvRa, rhss)

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:504-519 checkNativeTable
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:117-126 checkNativeTableF
Stage 4: **the projection table** at a STRUCTURE-LIKE block — one constructor,
no index — at the tagged tower's projection offset `1`; nothing at any other
block. -/
def checkNativeTable (p : NativeParts) (ctorsA : List (IConstantVal × Nat))
    (sortss : List (List LIdx)) (fe : IFEnv) : AM IFEnv := do
  match ctorsA, sortss with
  | [cA], [sorts] =>
    if p.nIdx == 0 then do
      let guards ← structProjGuards cA.1.type p.nP cA.2 sorts
      checkStructProjTable p.cvT.name cA.1.name p.cvT.levelParams p.nP cA.2 p.resSort
        guards 1 cA.1 fe
    else pure fe
  | _, _ => pure fe

/-! ## The two-pass install -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:521-537 NativePass
**What one pass over the former and the constructors yields** (task #268).  Not
generic in the environment: the arena has one (module note). -/
structure NativePass where
  /-- the environment holding the former, at the record the pass ran at -/
  env₁ : IFEnv
  /-- the annotated former -/
  cvTa : IConstantVal
  /-- the completed record: the sort read, the kinds classified -/
  p : NativeParts
  /-- the annotated (normalised) constructors -/
  ctorsA : List (IConstantVal × Nat)
  /-- the fields' sorts, one list per constructor -/
  sortss : List (List LIdx)

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
`ctorsA.mapM (recCtorKinds T lps nP nIdx)` at the `Option` monad, spelled as an
explicit recursion because the twin of `recCtorKinds` is monadic in `AM` and
optional in its result. -/
def recCtorKindsAll (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) :
    List (IConstantVal × Nat) → AM (Option (List (List RecFieldKind)))
  | [] => pure (some [])
  | c :: cs => do
    match ← recCtorKinds T lps nP nIdx c with
    | none => pure none
    | some ks => do
      match ← recCtorKindsAll T lps nP nIdx cs with
      | none => pure none
      | some rest => pure (some (ks :: rest))

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
**The fields' kinds, classified at install** (task #210 Part D) on the stored
constructors: a non-positive or non-valid occurrence is INVALID, a nested
occurrence a positive decline. -/
def classifyFixKinds (T : NIdx) (lps : List NIdx) (nP nIdx : Nat)
    (ctorsA : List (IConstantVal × Nat)) : AM (List (List RecFieldKind)) := do
  let kinds ← unwrapOr (← recCtorKindsAll T lps nP nIdx ctorsA)
    (.notImplemented "direct rec: constructor telescope")
  if kinds.any (fun ks => ks.any (· == .negative)) then
    fail (.invalid "direct rec: non positive or non valid occurrence of the inductive type")
  if kinds.any (fun ks => ks.any (· == .unsupported)) then
    fail (.notImplemented "direct rec: a nested occurrence of the block (not modeled here)")
  pure kinds

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:556-574 checkNativePass
**One pass over the former and the constructors** (task #268) at a given
`is_rec` verdict.  The last component says whether the classification confirms
the verdict the pass ran at. -/
def checkNativePass (mode : CheckMode) (fe : IFEnv) (p₀ : NativeParts) (isRec : Bool) :
    AM (NativePass × Bool) := do
  let (fe₁, cvTa, p₁) ← checkSumInd mode fe p₀.toInductiveShape isRec
  let pC := p₀.complete p₁
  -- con-leche: ConLeche/Cached/CheckerC.lean:179-191 checkNativePassS
  flushCaches
  let (ctorsA, sortss) ← checkSumCtors mode fe₁ fe₁ pC.cvT.name pC.cvT.levelParams pC.nP
    pC.nIdx pC.resSort pC.isProp pC.large cvTa pC.ctors
  let kinds ← classifyFixKinds pC.cvT.name pC.cvT.levelParams pC.nP pC.nIdx ctorsA
  let p := pC.withKinds kinds
  let settled := (← nativeCaps p) == (← nativeCapsAt p₁ isRec)
  pure (⟨fe₁, cvTa, p, ctorsA, sortss⟩, settled)

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
**The install after the pass** (task #268): the elimination restriction, the
index binders' sorts, the kinds re-checked, the stream's rules against the
generated ones, the constructors consed, the recursor with its rules, and — at
a structure-like block — the projection table. -/
def checkNativeTail (mode : CheckMode) (fe : IFEnv) (q : NativePass) : AM IFEnv := do
  let p := q.p
  -- a large eliminator on a block whose sort may be `Prop`: two or more
  -- constructors is `.invalid` (official's `elim_only_at_universe_zero`)
  let neverZero := (← readLevelM p.resSort).isNeverZero
  if p.large && !neverZero && decide (2 ≤ p.ctors.length) then
    fail (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  -- the index binders' universes, exposed for the model's index-tuple universe
  let tq ← unwrapOr (← openPisAtFvarsF (p.nP + p.nIdx) q.cvTa.type 0)
    (.internal "direct rec: type former telescope")
  let _isorts ← checkStructFieldSortsI mode q.env₁ true false p.resSort p.nP
    (tq.1.drop p.nP) [] p.nIdx
  -- the kinds, re-checked on the stored (normalised) constructors
  unless ← nativeFieldsOk fe p.cvT.name p.cvT.levelParams p.nP p.nIdx q.ctorsA p.kinds do
    fail (.internal "direct rec: field kinds")
  -- the stream's rules are the generated ones
  let rlvls ← paramLevels p.cvR.levelParams
  unless ← nativeRulesOk p.cvR.name rlvls .never p.nP p.ctors.length q.ctorsA p.kinds
      p.rhss p.cvR.type do
    fail (.invalid "direct rec: recursor rules are not the generated ones")
  let fe₂ := consSumCtors p.nP q.ctorsA q.env₁
  -- con-leche: ConLeche/Cached/CheckerC.lean:194-217 checkNativeTailS
  flushCaches
  let (cvRa, rhss) ← checkNativeRec mode fe₂ p q.cvTa q.ctorsA
  let rules ← sumRules fe₂ cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type q.ctorsA rhss
  checkNativeTable p q.ctorsA q.sortss
    (fe₂.push (.recInfo cvRa p.majorIdx p.rulePrefix rules))

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
Check and install a **direct recursive block**: the distinct names, the pass
over the former and the constructors — again where the record's syntactic
reading overshot — and the install after it. -/
def checkNative (mode : CheckMode) (fe : IFEnv) (p₀ : NativeParts) : AM IFEnv := do
  unless (p₀.ctors.map (·.1.name)).Nodup do
    fail (.invalid "direct rec: duplicate constructor")
  -- con-leche: ConLeche/Cached/CheckerC.lean:220-231 checkNativeS
  flushCaches
  -- THE CAPABILITY RECORD'S VERDICT (task #268): the pass runs at the
  -- syntactic reading of `is_rec`, which the classification of the
  -- constructors it stored confirms at every block but one whose declared
  -- field domain mentions the block under a redex that reduces it away
  let (q, settled) ← checkNativePass mode fe p₀ (← nativeRawRec p₀)
  if settled then checkNativeTail mode fe q
  else do
    -- con-leche: ConLeche/Cached/CheckerC.lean:220-231 checkNativeS
    flushCaches
    let (q', settled') ← checkNativePass mode fe p₀ (nativeIsRec q.p.kinds)
    unless settled' do
      fail (.internal "direct rec: the capability record did not settle")
    checkNativeTail mode fe q'

end ConRon.Arena
