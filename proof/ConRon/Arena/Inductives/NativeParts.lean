/-
# `ConRon.Arena.Inductives.NativeParts` — the direct recursive class
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/NativeParts.lean` whole, over handles: the field
kinds and official's positivity classification, the generated recursor with
its inductive-hypothesis binders, the comparison of the stream's rules against
the generated ones, and the recogniser.

**The deviations of this module:**

* **`RecFieldKind` is TWINNED, not imported.**  It carries no term, so
  DESIGN §8.7's rule would have (B) import con-leche's.  It cannot:
  `ConLeche/Kernel/Inductives/NativeParts.lean` also declares `structFam`,
  `structPsAt`, `structShape`, `sumSplit`, `InductiveShape` and
  `NativeParts`, and every module here does `open ConLeche` — importing it
  would make a dozen names ambiguous against this port's own.  Five
  constructors and no field is a cheap copy; the judgement is the same one
  `Arena/Env.lean` makes for the types it twins.
* **`structIhPis` and `structRuleBodyR` take the constructor type, not two
  functions.**  con-leche passes `teleOf : Nat → List (Expr × BinderMeta)`
  and `idxOf : Nat → List Expr`, and every call site instantiates them at
  `structFieldTeleOf cty nP nF` and `structFieldIdxOf cty nP nF`.  Two
  closures per call is what DESIGN §3.4 forbids, so the twins take `cty` and
  the counts and call the two readers themselves — the same substitution
  task #97b's closure audit made for `stripLams`' `Option.map` and
  `instLPGo`'s `vs.map`.  Nothing is recomputed that con-leche's partial
  applications did not recompute.
* **`nativeRecPinOk`, `nativeRecLpsOk`, `recIdxOf`, `NativeParts.complete` and
  `NativeParts.withKinds` stay PURE** — they read counts, names and tags and
  touch no term (`Arena/Inductives/SumParts.lean`'s note).
-/
import ConRon.Arena.Inductives.SumInstallF

namespace ConRon.Arena

open ConLeche
open ConRon.Arena.IndBase (unwrapOr)

/-! ## The field kinds -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:60-76 RecFieldKind
The kind of a constructor field of a recursive block.  Twinned rather than
imported; see the module note. -/
inductive RecFieldKind where
  /-- the domain does not mention the block -/
  | ordinary
  /-- the domain is exactly `T p⃗ e⃗`: a finitary recursive field -/
  | recursive
  /-- the domain is `Π a⃗ : A⃗, T p⃗ e⃗(a⃗)` with `A⃗` free of the block -/
  | reflexive
  /-- a non-positive (or non-valid) occurrence: the official kernel rejects -/
  | negative
  /-- an occurrence the official kernel accepts that this route does not model -/
  | unsupported
  deriving Repr, DecidableEq, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:78-87 recFamOk
Is `e` the family at the parameter variables (sitting `o` binders up) followed
by `nIdx` index expressions none of which mentions the block?  Official's
`is_valid_ind_app` exactly. -/
def recFamOk (T : NIdx) (lps : List NIdx) (nP nIdx o : Nat) (e : EIdx) : AM Bool := do
  let us ← paramLevels lps
  let hd ← internE (.const T us)
  let fn ← getAppFn coreWalkFuel e
  let args ← getAppArgs coreWalkFuel e
  let ps ← structPsAt o nP
  if !(fn == hd && args.length == nP + nIdx && args.take nP == ps) then pure false
  else (args.drop nP).allM fun a => do pure !(← mentionsConst T a)

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:89-111 recPositivity
Official `check_positivity`'s telescope walk on a field domain that mentions
the block, syntactically. -/
def recPositivity (T : NIdx) (lps : List NIdx) (nP nIdx o : Nat) :
    Nat → EIdx → Nat → AM RecFieldKind
  | 0, _, _ => fail (.internal "fuel exhausted: recPositivity")
  | fuel + 1, h, k => do
    match ← view h with
    | .forallE dom body _ => do
      if ← mentionsConst T dom then pure .negative
      else recPositivity T lps nP nIdx o fuel body (k + 1)
    | _ => do
      if !(← mentionsConst T h) then pure .ordinary else do
      let us ← paramLevels lps
      let hd ← internE (.const T us)
      let fn ← getAppFn coreWalkFuel h
      let args ← getAppArgs coreWalkFuel h
      if fn == hd then do
        let ps ← structPsAt (o + k) nP
        if args.length == nP + nIdx && args.take nP == ps then
          if ← recFamOk T lps nP nIdx (o + k) h then
            pure (if k == 0 then .recursive else .reflexive)
          else pure .negative
        else pure .negative
      else
        match ← view fn with
        | .const T' _ => pure (if T' == T then .negative else .unsupported)
        | _ => pure .unsupported

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:113-116 recFieldKind
The kind of a field whose domain is `dom`, `o` fields into the constructor's
telescope. -/
def recFieldKind (T : NIdx) (lps : List NIdx) (nP nIdx o : Nat) (dom : EIdx) :
    AM RecFieldKind := do
  if ← mentionsConst T dom then recPositivity T lps nP nIdx o coreWalkFuel dom 0
  else pure .ordinary

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
The kinds of one constructor's fields, off its (raw or annotated) type.  A
recursive field that a LATER binder or the residual mentions is marked
unsupported. -/
def recCtorKinds (T : NIdx) (lps : List NIdx) (nP nIdx : Nat)
    (c : IConstantVal × Nat) : AM (Option (List RecFieldKind)) := do
  match ← stripPis (nP + c.2) c.1.type with
  | some (cbs, cbody) => do
    let ks ← (List.range c.2).mapM fun i => do
      match ← recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
      | .recursive =>
        pure (if ← structUsedLater c.1.type nP i then .unsupported else .recursive)
      | .reflexive =>
        pure (if ← structUsedLater c.1.type nP i then .unsupported else .reflexive)
      | k => pure k
    let cargs ← getAppArgs coreWalkFuel cbody
    let resOk ← (cargs.drop nP).allM fun a => do pure !(← mentionsConst T a)
    if resOk then pure (some ks)
    else pure (some (ks.map fun _ => .negative))
  | none => pure none

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:147-154 Expr.piBinders
All leading `∀` binders of an expression (outermost first) and the body. -/
def piBinders : Nat → EIdx → AM (List (EIdx × BinderMeta) × EIdx)
  | 0, _ => fail (.internal "fuel exhausted: piBinders")
  | fuel + 1, h => do
    match ← view h with
    | .forallE ty b m => do
      let (bs, e) ← piBinders fuel b
      pure ((ty, m) :: bs, e)
    | _ => pure ([], h)

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:156-161 structFieldTeleOf
Field `i`'s own telescope `a⃗ : A⃗` (at the field's frame), off the
constructor's type. -/
def structFieldTeleOf (cty : EIdx) (nP nF i : Nat) : AM (List (EIdx × BinderMeta)) := do
  match ← stripPis (nP + nF) cty with
  | some (cbs, _) => do
    let (bs, _) ← piBinders coreWalkFuel (cbs.getD (nP + i) default).1
    pure bs
  | none => pure []

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:163-169 structFieldIdxOf
The index expressions of field `i`'s domain `Π a⃗, T p⃗ e⃗`, off the
constructor's type; `[]` when the field is not of that shape. -/
def structFieldIdxOf (cty : EIdx) (nP nF i : Nat) : AM (List EIdx) := do
  match ← stripPis (nP + nF) cty with
  | some (cbs, _) => do
    let (_, body) ← piBinders coreWalkFuel (cbs.getD (nP + i) default).1
    let args ← getAppArgs coreWalkFuel body
    pure (args.drop nP)
  | none => pure []

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:171-175 recIdxOf
The positions of the recursive fields (finitary or reflexive). -/
def recIdxOf (ks : List RecFieldKind) : List Nat :=
  (List.range ks.length).filter fun i =>
    ks.getD i .ordinary == .recursive || ks.getD i .ordinary == .reflexive

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:177-192 NativeParts
The pieces of a recognised direct recursive block: the sum parts with the
family's index count, and the per-constructor field kinds. -/
structure NativeParts extends InductiveShape where
  /-- per constructor, per field: its kind -/
  kinds : List (List RecFieldKind)
  /-- **the stream's recursor record passed the structural pin** (task #220) -/
  recPinned : Bool
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:194-199 NativeParts.complete
**The record completed by the former's stage**: the sum parts the former's run
returned with the recogniser's field kinds. -/
def NativeParts.complete (p₀ : NativeParts) (p₁ : InductiveShape) : NativeParts :=
  ⟨p₁, p₀.kinds, p₀.recPinned⟩

/-! ## The generated recursor with inductive hypotheses -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:230-235 structRecPrefixAt
The parameter, motive and minor variables as seen from under the `nF` fields
(and `e` further binders): the recursor's leading spine `p⃗ motive m⃗`. -/
def structRecPrefixAt (nP n nF e : Nat) : AM (List EIdx) := do
  let ps ← structPsAt (e + nF + n + 1) nP
  let motive ← internE (.bvar (e + nF + n))
  let minors ← structPsAt (e + nF) n
  pure (ps ++ [motive] ++ minors)

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:237-244 structIdxAt
An expression of recursive field `i`'s domain sitting under `m` binders of the
field's own telescope, spelled at the recursor-rule frame. -/
def structIdxAt (nF o i l m : Nat) (e : EIdx) : AM EIdx := do
  let a ← liftLooseBVarsFast coreWalkFuel (nF - i + l) m e
  liftLooseBVarsFast coreWalkFuel o (nF + l + m) a

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:246-252 structTeleAt
Field `i`'s own telescope moved as `structIdxAt` moves its expressions. -/
def structTeleAt (nF o i l : Nat) (pw : PropWhen) (tele : List (EIdx × BinderMeta)) :
    AM (List (EIdx × BinderMeta)) :=
  (List.range tele.length).mapM fun k => do
    let b := tele.getD k default
    pure (← structIdxAt nF o i l k b.1, ⟨pw⟩)

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:254-255 structTeleVars
The variables of an `m`-binder telescope, innermost last. -/
def structTeleVars (m : Nat) : AM (List EIdx) := bvarsDesc m

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:257-260 Expr.mkPisOf
`∀ tele, body` over a binder list (outermost first). -/
def mkPisOf : List (EIdx × BinderMeta) → EIdx → AM EIdx
  | [], body => pure body
  | (ty, mt) :: bs, body => do internE (.forallE ty (← mkPisOf bs body) mt)

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:261-263 Expr.mkLamsOf
`λ tele, body` over a binder list (outermost first). -/
def mkLamsOf : List (EIdx × BinderMeta) → EIdx → AM EIdx
  | [], body => pure body
  | (ty, mt) :: bs, body => do internE (.lam ty (← mkLamsOf bs body) mt)

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:265-277 structIhApp
The inductive hypothesis' value for recursive field `i` with telescope `tele`
and index expressions `idx`, spelled under the fields of a rule body. -/
def structIhApp (recC : NIdx) (rlvls : LsIdx) (pw : PropWhen) (nP n nF i : Nat)
    (tele : List (EIdx × BinderMeta)) (idx : List EIdx) : AM EIdx := do
  let m := tele.length
  let hd ← internE (.const recC rlvls)
  let prefixSpine ← structRecPrefixAt nP n nF m
  let idx' ← idx.mapM fun e => structIdxAt nF (n + 1) i 0 m e
  let fvar ← internE (.bvar (nF - 1 - i + m))
  let fapp ← mkAppN fvar (← structTeleVars m)
  let body ← mkAppN hd (prefixSpine ++ idx' ++ [fapp])
  mkLamsOf (← structTeleAt nF (n + 1) i 0 pw tele) body

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:279-288 structRuleBodyR
The right-hand side body of rule `j` at a recursive block: minor `j` at the
fields, then at the inductive hypotheses of the recursive fields.  `cty` and
the counts replace con-leche's two function arguments (module note). -/
def structRuleBodyR (recC : NIdx) (rlvls : LsIdx) (pw : PropWhen)
    (nP n nF j : Nat) (recIdx : List Nat) (cty : EIdx) : AM EIdx := do
  let hd ← internE (.bvar (nF + n - 1 - j))
  let fs ← bvarsDesc nF
  let ihs ← recIdx.mapM fun i => do
    structIhApp recC rlvls pw nP n nF i (← structFieldTeleOf cty nP nF i)
      (← structFieldIdxOf cty nP nF i)
  mkAppN hd (fs ++ ihs)

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:290-305 structIhPis
The `ih` binders of a minor premise: for each recursive field position, `∀ a⃗,
motive e⃗_i(a⃗) (f_i a⃗)` under the `l` earlier `ih` binders.  `cty` and `nP`
replace con-leche's two function arguments (module note). -/
def structIhPis (nF o nP : Nat) (pw : PropWhen) (cty : EIdx) :
    List Nat → Nat → EIdx → AM EIdx
  | [], _, body => pure body
  | i :: is, l, body => do
    let tele ← structFieldTeleOf cty nP nF i
    let idx ← structFieldIdxOf cty nP nF i
    let m := tele.length
    let motive ← internE (.bvar (nF + o - 1 + l + m))
    let idx' ← idx.mapM fun e => structIdxAt nF o i l m e
    let fvar ← internE (.bvar (nF - 1 - i + l + m))
    let fapp ← mkAppN fvar (← structTeleVars m)
    let concl ← mkAppN motive (idx' ++ [fapp])
    let dom ← mkPisOf (← structTeleAt nF o i l pw tele) concl
    let rest ← structIhPis nF o nP pw cty is (l + 1) body
    internE (.forallE dom rest ⟨pw⟩)

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:307-320 structMinorTyR
A constructor's minor premise at a recursive block: its field telescope lifted
under the `o` extras, every binder's datum reset to the elimination datum, then
the `ih` binders, ending in `motive e⃗ (C p⃗ f⃗)` lifted above the `ih`s. -/
def structMinorTyR (C : NIdx) (lps : List NIdx) (nP nF o : Nat) (pw : PropWhen)
    (cty : EIdx) (recIdx : List Nat) : AM (Option EIdx) := do
  match ← stripPis nP cty with
  | none => pure none
  | some (_, q2) => do
    match ← stripPis nF q2 with
    | none => pure none
    | some (_, r2) => do
      let motive ← internE (.bvar (nF + o - 1))
      let rargs ← getAppArgs coreWalkFuel r2
      let idx ← (rargs.drop nP).mapM fun e => liftLooseBVarsFast coreWalkFuel o nF e
      let spine ← structCtorSpineAt C lps o nP nF
      let concl0 ← mkAppN motive (idx ++ [spine])
      let concl ← liftLooseBVarsFast coreWalkFuel recIdx.length 0 concl0
      let inner ← structIhPis nF o nP pw cty recIdx 0 concl
      let lifted ← liftLooseBVarsFast coreWalkFuel o 0 q2
      replacePisPw pw nF lifted inner

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:322-330 structMinorsPisR
The minor premises' `∀`-telescope at a recursive block, one per
constructor. -/
def structMinorsPisR (lps : List NIdx) (nP : Nat) (pw : PropWhen) :
    List (NIdx × Nat × EIdx × List Nat) → Nat → EIdx → AM (Option EIdx)
  | [], _, body => pure (some body)
  | (C, nF, cty, recIdx) :: cs, o, body => do
    match ← structMinorTyR C lps nP nF o pw cty recIdx with
    | none => pure none
    | some mty => do
      match ← structMinorsPisR lps nP pw cs (o + 1) body with
      | none => pure none
      | some rest => do pure (some (← internE (.forallE mty rest ⟨pw⟩)))

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:332-339 structMinorsLamsR
The `λ` twin of `structMinorsPisR`. -/
def structMinorsLamsR (lps : List NIdx) (nP : Nat) (pw : PropWhen) :
    List (NIdx × Nat × EIdx × List Nat) → Nat → EIdx → AM (Option EIdx)
  | [], _, body => pure (some body)
  | (C, nF, cty, recIdx) :: cs, o, body => do
    match ← structMinorTyR C lps nP nF o pw cty recIdx with
    | none => pure none
    | some mty => do
      match ← structMinorsLamsR lps nP pw cs (o + 1) body with
      | none => pure none
      | some rest => do pure (some (← internE (.lam mty rest ⟨pw⟩)))

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:341-362 structRecTyR
**The generated recursor type at a recursive block.** -/
def structRecTyR (T : NIdx) (lps : List NIdx) (elim : NIdx) (large : Bool)
    (nP nIdx : Nat) (tty : EIdx) (ctors : List (NIdx × Nat × EIdx × List Nat)) :
    AM (Option EIdx) := do
  let l ← structElimLevel elim large
  let pw := Level.zeronessOf (← readLevel l)
  let n := ctors.length
  match ← stripPis nP tty with
  | none => pure none
  | some (_, q2) => do
    match ← structMotiveTyI T lps nP nIdx l q2 with
    | none => pure none
    | some motiveTy => do
      let fam ← structFamI T lps nP nIdx (n + 1) 0
      let motiveVar ← internE (.bvar (nIdx + n + 1))
      let idxVars ← structPsAt 1 nIdx
      let b0 ← internE (.bvar 0)
      let concl ← mkAppN motiveVar (idxVars ++ [b0])
      let majorBody ← internE (.forallE fam concl ⟨pw⟩)
      let lifted ← liftLooseBVarsFast coreWalkFuel (n + 1) 0 q2
      match ← replacePisPw pw nIdx lifted majorBody with
      | none => pure none
      | some major => do
        match ← structMinorsPisR lps nP pw ctors 1 major with
        | none => pure none
        | some minors => do
          let body ← internE (.forallE motiveTy minors ⟨pw⟩)
          replacePisPw pw nP tty body

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:364-386 structRecRhsR
**The generated rule** for constructor `j` at a recursive block. -/
def structRecRhsR (T : NIdx) (lps : List NIdx) (elim : NIdx) (large : Bool)
    (nP nIdx : Nat) (tty : EIdx) (ctors : List (NIdx × Nat × EIdx × List Nat))
    (recC : NIdx) (rlvls : LsIdx) (j : Nat) : AM (Option EIdx) := do
  let l ← structElimLevel elim large
  let pw := Level.zeronessOf (← readLevel l)
  let n := ctors.length
  match ctors[j]? with
  | none => pure none
  | some (_, nF, cty, recIdx) => do
    match ← stripPis nP tty with
    | none => pure none
    | some (_, tq2) => do
      match ← structMotiveTyI T lps nP nIdx l tq2 with
      | none => pure none
      | some motiveTy => do
        match ← stripPis nP cty with
        | none => pure none
        | some (_, q2) => do
          let body ← structRuleBodyR recC rlvls pw nP n nF j recIdx cty
          let lifted ← liftLooseBVarsFast coreWalkFuel (n + 1) 0 q2
          match ← pisToLamsPw pw nF lifted body with
          | none => pure none
          | some inner => do
            match ← structMinorsLamsR lps nP pw ctors 1 inner with
            | none => pure none
            | some minors => do
              let lam ← internE (.lam motiveTy minors ⟨pw⟩)
              pisToLamsPw pw nP tty lam

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:388-392 nativeCtors4
The constructors zipped with their recursive positions, as the generators take
them. -/
def nativeCtors4 (ctorsA : List (IConstantVal × Nat))
    (kinds : List (List RecFieldKind)) : List (NIdx × Nat × EIdx × List Nat) :=
  List.zipWith (fun cA ks => (cA.1.name, cA.2, cA.1.type, recIdxOf ks)) ctorsA kinds

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:394-445 nativeRulePrefixOk
**The rule's `λ` prefix against the stream's own recursor type** (task #271):
the rule binds the recursor's parameters, its motive, its minor premises and
constructor `j`'s fields, and every one of those binder types appears again in
the recursor RECORD's own type. -/
def nativeRulePrefixOk (recTy : EIdx) (nP n j nF : Nat) (rhs : EIdx) : AM Bool := do
  match ← stripLams (nP + 1 + n + nF) rhs, ← stripPis (nP + 1 + n) recTy with
  | some (rbs, _), some (tbs, _) => do
    let prefixOk ← (List.range (nP + 1 + n)).allM fun i => do
      match rbs[i]?, tbs[i]? with
      | some b, some t => do
        pure ((← resetMetaFast coreWalkFuel b.1) == (← resetMetaFast coreWalkFuel t.1))
      | _, _ => pure false
    if !prefixOk then pure false else
    match tbs[nP + 1 + j]? with
    | some mty => do
      let lifted ← liftLooseBVarsFast coreWalkFuel (n - j) 0 mty.1
      match ← stripPis nF lifted with
      | some (fbs, _) =>
        (List.range nF).allM fun i => do
          match rbs[nP + 1 + n + i]?, fbs[i]? with
          | some b, some f => do
            pure ((← resetMetaFast coreWalkFuel b.1) == (← resetMetaFast coreWalkFuel f.1))
          | _, _ => pure false
      | none => pure false
    | none => pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:447-475 nativeRulesOk
**The stream's rules against the generated ones** (at install): rule `j` fires
constructor `j` with its field count, and its body is the canonical right-hand
side with the inductive hypotheses, at the parse placeholder's binder data. -/
def nativeRulesOk (recC : NIdx) (rlvls : LsIdx) (pw : PropWhen) (nP n : Nat)
    (cs : List (IConstantVal × Nat)) (kinds : List (List RecFieldKind))
    (rhss : List EIdx) (recTy : EIdx) : AM Bool := do
  if !(rhss.length == n && kinds.length == n) then pure false else
  (List.range n).allM fun j => do
    match rhss[j]?, cs[j]?, kinds[j]? with
    | some rhs, some (cA, nF), some ks => do
      if !(ks.length == nF) then pure false else do
      let bodyOk ← match ← stripLams (nP + 1 + n + nF) rhs with
        | some (_, rbody) => do
          let want ← structRuleBodyR recC rlvls pw nP n nF j (recIdxOf ks) cA.type
          pure (rbody == (← resetMetaFast coreWalkFuel want))
        | none => pure false
      if !bodyOk then pure false else
      nativeRulePrefixOk recTy nP n j nF rhs
    | _, _, _ => pure false

/-! ## Recognition -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:501-523 nativeCounts?
**The block's parameter and index counts** (task #228), read as official reads
them. -/
def nativeCounts? (nPd : Nat) (cvT : IConstantVal)
    (cs : List (IConstantVal × Nat × Nat)) (mI rP : Nat) : AM (Option (Nat × Nat)) := do
  let (bs, body) ← piBinders coreWalkFuel cvT.type
  match ← view body with
  | .sort _ => pure (if nPd ≤ bs.length then some (nPd, bs.length - nPd) else none)
  | _ =>
    if rP < cs.length + 1 || mI < rP then pure none
    else if rP - (cs.length + 1) == nPd then pure (some (nPd, mI - rP)) else pure none

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:525-549 nativeRecPinOk
**The recursor record's structural pin** (task #220): the two argument sums the
record claims, one rule per constructor in constructor order, each rule naming
its constructor with its field count.  Pure: tags, names and counts only. -/
def nativeRecPinOk (p : InductiveShape) (block : List IConstantInfo) : Bool :=
  match block with
  | .indInfo _ _ :: rest =>
    match sumSplit rest with
    | some (cs, _, mI, rP, rules) =>
      rP == p.nP + 1 + p.ctors.length && mI == p.nP + 1 + p.ctors.length + p.nIdx &&
      rules.length == p.ctors.length &&
      (List.range p.ctors.length).all fun j =>
        match rules[j]?, cs[j]? with
        | some rule, some (cvC, _, nF) => rule.ctor == cvC.name && rule.nfields == nF
        | _, _ => false
    | none => false
  | _ => false

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:551-560 nativeRecLpsOk
**The recursor record's level-parameter pin** (task #220). -/
def nativeRecLpsOk (p : InductiveShape) : Bool :=
  if p.large then p.cvR.levelParams == p.elim :: p.cvT.levelParams
  else p.cvR.levelParams == p.cvT.levelParams

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
The block's shape at a recursive block: the type former, the constructors and
the counts, with the rules' right-hand sides as exported and the recursor's
level-parameter shape. -/
def nativeShape? (nPd : Nat) (block : List IConstantInfo) :
    AM (Option InductiveShape) := do
  match block with
  | .indInfo cvT _ :: rest => do
    match sumSplit rest with
    | some (cs, cvR, mI, rP, rules) => do
      let T := cvT.name
      let lps := cvT.levelParams
      match ← nativeCounts? nPd cvT cs mI rP with
      | none => pure none
      | some (nP, nIdx) => do
        let reserved ← reservedBasisNames
        if reserved.contains T == false &&
            reserved.contains cvR.name == false &&
            cs.all (fun c => c.2.1 == nP && c.1.levelParams == lps &&
              reserved.contains c.1.name == false) then do
          -- the result sort: read off the declared type when it is a syntactic
          -- telescope ending in a sort; otherwise a PLACEHOLDER the install's
          -- whnf loop replaces (task #195)
          let s ← match ← stripPis (nP + nIdx) cvT.type with
            | some (_, body) => do
              match ← view body with
              | .sort s => pure s
              | _ => zeroLevel
            | _ => zeroLevel
          let z ← zeroLevel
          let isProp := (← lvlEq? s z) == some true
          let ctors := cs.map fun c => (c.1, c.2.2)
          let rhss := rules.map (·.rhs)
          -- WHICH ELIMINATOR the block's recursor is (task #220)
          let large? : Option NIdx := match cvR.levelParams with
            | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
            | [] => none
          match large? with
          | some elim => pure (some ⟨cvT, ctors, nP, nIdx, cvR, elim, s, rhss, true, isProp⟩)
          | none => do
            let anon ← internNNode .anonymous
            pure (some ⟨cvT, ctors, nP, nIdx, cvR, anon, s, rhss, false, isProp⟩)
        else pure none
    | none => pure none
  | _ => pure none

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:616-622 NativeParts.withKinds
The record completed with the fields' kinds (task #210 Part D). -/
def NativeParts.withKinds (p : NativeParts) (ks : List (List RecFieldKind)) :
    NativeParts :=
  { p with kinds := ks }

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:631-652 nativeParts?
Recognise a direct block — ONE ROUTE (task #210): its SHAPE; the fields' kinds
are a PLACEHOLDER the install fills after normalising every field domain by
official's positivity walk. -/
def nativeParts? (nPd : Nat) (block : List IConstantInfo) : AM (Option NativeParts) := do
  match ← nativeShape? nPd block with
  | some p => pure (some ⟨p, [], nativeRecPinOk p block⟩)
  | none => pure none

end ConRon.Arena
