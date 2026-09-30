/-
# `ConRon.Arena.Inductives.GenRec` — the recursor family, GENERATED
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/GenRec.lean` over handles, the twin of the Rust
`arena::inductives::gen_rec`: the classes read and checked
(`checkBlockClasses`), per class and constructor the positivity table's datum
and node agreement (`classCtorOf`), the generator (`ClassGen`: the shared
prefix, each recursor's type, each rule), the generated types checked and
compared with the stream's (`classRecTyOk`), and the generated rules installed
(`classRuleOk`) — `genRecCheck`.

**The deviations** (the Rust's, which this twin mirrors):

* **The shadow operations are the core's, with `shadowOpsC`'s flushes**
  (`Arena/Inductives/RecCheck.lean`'s note): `so.flush` is `flushCaches`, and
  the rule stage's `opsRuleR feR` is the core at the rule-less recursors'
  environment with a flush LEAVING its `inferType` (`sharedOpsRuleR`; the
  stage never calls its `annotate`).  No `ShadowOps`/`CheckerOps`/
  `StructWalkers` record: `mode` and the environment are passed.
* **`feR` is `fe` with the rule-less recursors pushed TEMPORARILY** and
  popped once the rules are typed (`classFeR`, `IFEnv.popTemp`), so `feT`
  (the constructors' environment) is `feR` at its lower visibility bound
  `visT` — `consBlockRecsBareF`'s cons, as the port does it (task #97-P6-5's
  lever 4).  `genRecCheck` hands the popped index back, as the Rust does.
* **`recOf` is `classRecOf recCls cvGs`, specialised**: `classGenRule`,
  `classRulesOk` and `classRecsRulesOk` take `recCls` and `cvGs`.
* **`ClassGen.bm` is a field**, computed once from `elim` (`classGenBm`)
  where con-leche recomputes the pure `⟨Level.zeronessOf g.elim⟩` at every
  use.
* **The messages drop their interpolation** (DESIGN.md §3.1), as the Rust's
  code-point constants do; the gaps are kept.
* **A `getD … default` out of range** reads the interned default, as the Rust
  does: `exprGetD` (`.bvar 0` for a term), `targetMajorAt` (RecCheck's
  `targetMajorDefault` for a class).  The stage never forms such an index.
-/
import ConRon.Arena.Inductives.RecCheck
import ConRon.Arena.Inductives.ClassRead

namespace ConRon.Arena

open ConLeche

/-! ## The generator -/

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:60-66 ClassField
A field of a class's constructor, as the generator reads it: ordinary, or
recursive at class `cls` with a telescope of `tele` binders. -/
inductive ClassField where
  | ordinary
  | recursive (cls : Nat) (tele : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:68-81 ClassCtor
A class's constructor as the generator reads it: its DECLARED type at the
class's levels and parameters `tyD`, the datum's WALKED telescope `tyN`, the
field count and the fields' kinds. -/
structure ClassCtor where
  cv : IConstantVal
  nF : Nat
  kinds : List ClassField
  tyD : EIdx
  tyN : EIdx
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:83-86 closeLams
Close a telescope of `λ`s opened at `i ..< i + bs.length` (`closeTelescope`'s
twin), innermost first. -/
def closeLams : List (EIdx × BinderMeta) → Nat → EIdx → AM EIdx
  | [], _, body => pure body
  | (dom, bm) :: bs, i, body => do
    let inner ← closeLams bs (i + 1) body
    let closed ← abstract1Fast coreWalkFuel inner i 0
    internE (.lam dom closed bm)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:88-100 ClassGen
What generation reads: the block, the classes, the layout, the constructors,
the elimination level, the generated prefix; `bm` is the generated binders'
datum, computed once (`classGenBm`, the module note). -/
structure ClassGen where
  nP : Nat
  params : List EIdx
  cls : List TargetMajor
  /-- per class, the former's type (its own levels instantiated) -/
  formerTys : List EIdx
  slots : List ClassSlot
  ctors : List (List ClassCtor)
  elim : LIdx
  /-- the generated binders' datum (con-leche's `ClassGen.bm`) -/
  bm : BinderMeta
  /-- the generated prefix binders (`ClassGen.prefixBinders`), computed once -/
  pre : List (EIdx × BinderMeta)

/-- con-leche: none — `xs.getD i default` on a term list, the default interned (`.bvar 0`)
The Rust's `expr_get_d`: the element in range, else the interned `.bvar 0`
(the stage never reads out of range). -/
def exprGetD (xs : List EIdx) (i : Nat) : AM EIdx :=
  match xs[i]? with
  | some x => pure x
  | none => internE (.bvar 0)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:102-104 classBinder
The binder of an opened variable at the default datum (`.never`); the Rust's
`class_binders` is `xs.mapM classBinder`. -/
def classBinder (x : EIdx) : AM (EIdx × BinderMeta) := do
  let t ← fvarTypeD x
  pure (t, ⟨.never⟩)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:106-111 ClassGen.bm
**The generated binders' datum**: the elimination level's zero-ness, computed
once into the `ClassGen.bm` field (the module note). -/
def classGenBm (elim : LIdx) : AM BinderMeta := do
  let l ← readLevelM elim
  pure ⟨Level.zeronessOf l⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:113-114 ClassGen.binder
A generated binder of an opened variable; the Rust's `gen_binders` is
`xs.mapM g.binder`. -/
def ClassGen.binder (g : ClassGen) (x : EIdx) : AM (EIdx × BinderMeta) := do
  let t ← fvarTypeD x
  pure (t, g.bm)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:116-117 ClassGen.slotVar
The prefix variable of slot `s`. -/
def ClassGen.slotVar (g : ClassGen) (s : Nat) : AM EIdx := do
  let z ← internE (.sort (← zeroLevel))
  internE (.fvar (g.nP + s) z)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:119-121 ClassGen.motVar
Class `c`'s motive variable. -/
def ClassGen.motVar (g : ClassGen) (c : Nat) : AM EIdx :=
  g.slotVar ((ClassRead.motiveSlot g.slots c).getD 0)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:123-128 ClassGen.major
Class `c`'s index telescope opened at `d`, and its major domain. -/
def ClassGen.major (g : ClassGen) (c d : Nat) : AM (Option (List EIdx × EIdx)) := do
  let ci ← targetMajorAt g.cls c
  let fty ← exprGetD g.formerTys c
  match ← instPisWith ci.ds fty with
  | none => pure none
  | some ty =>
    match ← openPisAtFvarsF ci.nIdx ty d with
    | none => pure none
    | some (ifs, _) => do
      let hd ← internE (.const ci.ind ci.lvls)
      let maj ← mkAppN hd (ci.ds ++ ifs)
      pure (some (ifs, maj))

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:130-133 ClassGen.motiveTy
Class `c`'s motive type at depth `d`: `∀ ı⃗ (t : I D⃗ ı⃗), Sort ℓ`. -/
def ClassGen.motiveTy (g : ClassGen) (c d : Nat) : AM (Option EIdx) := do
  match ← g.major c d with
  | none => pure none
  | some (ifs, maj) => do
    let srt ← internE (.sort g.elim)
    let body ← internE (.forallE maj srt ⟨.never⟩)
    let bs ← ifs.mapM classBinder
    let r ← closeTelescope bs d body
    pure (some r)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:135-141 ClassGen.ihParts
The inductive hypothesis of a recursive field whose WALKED type is `w`
(landing at class `t`), opened at `d`: its telescope and its index
arguments. -/
def ClassGen.ihParts (g : ClassGen) (t tele : Nat) (w : EIdx) (d : Nat) :
    AM (Option (List EIdx × List EIdx)) := do
  match ← openPisAtFvarsF tele w d with
  | none => pure none
  | some (xs, leaf) => do
    -- `(g.cls.getD t default).nPc`: the default class has none
    let nPc := match g.cls[t]? with | some m => m.nPc | none => 0
    let args ← getAppArgs coreWalkFuel leaf
    pure (some (xs, args.drop nPc))

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:143-163 ClassGen.minorTy
Constructor `x`'s minor premise type at depth `d`, of class `c`: its declared
fields, then per recursive field `f` (walked type `w`) its inductive
hypothesis `∀ a⃗, motive_t e⃗ (f a⃗)` at depth `d + nF + l`, over the motive at
the declared result indices and the constructor applied.  The Rust's
`rec_fields`, `minor_ihs` and `minor_ty_concl` are this function's parts
(`recs`, `ihsGo`, the tail), in the Rust's bind order. -/
def ClassGen.minorTy (g : ClassGen) (c : Nat) (x : ClassCtor) (d : Nat) :
    AM (Option EIdx) := do
  let ci ← targetMajorAt g.cls c
  match ← openPisAtFvarsF x.nF x.tyD d with
  | none => pure none
  | some (fvs, res) =>
    match ← targetPiDomsWith fvs x.tyN with
    | none => pure none
    | some ws => do
      let recs := (List.range x.nF).filterMap fun i =>
        match x.kinds.getD i .ordinary with
        | .recursive t tele => some (i, t, tele)
        | .ordinary => none
      let rec ihsGo : Nat → List (Nat × Nat × Nat) → AM (Option (List (EIdx × BinderMeta)))
        | _, [] => pure (some [])
        | l, (i, t, tele) :: rest => do
          let e := d + x.nF + l
          let w ← exprGetD ws i
          match ← g.ihParts t tele w e with
          | none => pure none
          | some (xs, idx) => do
            let f ← exprGetD fvs i
            let fx ← mkAppN f xs
            let mt ← g.motVar t
            let body ← mkAppN mt (idx ++ [fx])
            let bs ← xs.mapM g.binder
            let ih ← closeTelescope bs e body
            match ← ihsGo (l + 1) rest with
            | none => pure none
            | some ihs => pure (some ((ih, g.bm) :: ihs))
      match ← ihsGo 0 recs with
      | none => pure none
      | some ihs => do
        let ra ← getAppArgs coreWalkFuel res
        let cc ← internE (.const x.cv.name ci.lvls)
        let capp ← mkAppN cc (ci.ds ++ fvs)
        let mc ← g.motVar c
        let concl ← mkAppN mc (ra.drop ci.nPc ++ [capp])
        let fbs ← fvs.mapM g.binder
        let r ← closeTelescope (fbs ++ ihs) d concl
        pure (some r)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:165-178 ClassGen.prefixBinders
The prefix binders: the parameters, then every slot in the stream's order,
slot `s` at depth `nP + s` — a motive's type (its class the count of motives
before it) or the minor premise of its constructor.  The Rust's
`motives_before`, `find_class_ctor`, `slot_binder` and `slot_binders` are its
parts. -/
def ClassGen.prefixBinders (g : ClassGen) : AM (Option (List (EIdx × BinderMeta))) := do
  let pbs ← g.params.mapM g.binder
  let rec slotsGo : Nat → List ClassSlot → AM (Option (List (EIdx × BinderMeta)))
    | _, [] => pure (some [])
    | s, sl :: sls => do
      let d := g.nP + s
      let ty? ← match sl with
        | .motive _ =>
          let c := ((g.slots.take s).filter fun s' =>
            match s' with | .motive _ => true | _ => false).length
          g.motiveTy c d
        | .minor c C _ =>
          match (g.ctors.getD c []).find? (·.cv.name == C) with
          | none => pure none
          | some x => g.minorTy c x d
      match ty? with
      | none => pure none
      | some ty =>
        match ← slotsGo (s + 1) sls with
        | none => pure none
        | some rest => pure (some ((ty, g.bm) :: rest))
  match ← slotsGo 0 g.slots with
  | none => pure none
  | some sbs => pure (some (pbs ++ sbs))

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:180-187 classGenRecTy
**The generated recursor type** at class `c`: the prefix, the class's indices
and its major, over the motive applied to them. -/
def classGenRecTy (g : ClassGen) (c : Nat) : AM (Option EIdx) := do
  let rP := g.pre.length
  match ← g.major c rP with
  | none => pure none
  | some (ifs, maj) => do
    let t ← internE (.fvar (rP + ifs.length) maj)
    let ibs ← ifs.mapM g.binder
    let bs := g.pre ++ ibs ++ [(maj, g.bm)]
    let mv ← g.motVar c
    let body ← mkAppN mv (ifs ++ [t])
    let r ← closeTelescope bs 0 body
    pure (some r)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:538-543 classRecOf
The recursor a call at class `t` names: the family's first recursor at that
class (`recCls` the pre-pass's reading, `cvGs` the generated constants).
Placed ahead of `classGenRule`, which the Rust specialises to it. -/
def classRecOf (recCls : List Nat) (cvGs : List IConstantVal) (t : Nat) : Option NIdx :=
  ((List.range cvGs.length).find? fun r => recCls.getD r 0 == t).map fun r =>
    (cvGs.getD r default).name

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:189-212 classGenRule
**The generated rule** of a recursor at class `c` for its constructor `x`:
`λ p⃗ (prefix) f⃗, minor f⃗ (λ a⃗, rec_t p⃗ (prefix) e⃗ (f a⃗))…`, the callee the
family's recursor at the landing class (`classRecOf recCls cvGs`, the module
note).  The Rust's `find_minor_slot`, `minor_is`, `prefix_vars`,
`rule_calls`, `rule_call` and `class_gen_rule_close` are its parts. -/
def classGenRule (g : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (rlvls : LsIdx) (c : Nat) (x : ClassCtor) : AM (Option EIdx) := do
  let rP := g.pre.length
  let hit := ((List.range g.slots.length).zip g.slots).find? fun (_, sl) =>
    match sl with
    | .minor c' C _ => c' == c && C == x.cv.name
    | .motive _ => false
  match hit with
  | none => pure none
  | some (s, _) =>
    match ← openPisAtFvarsF x.nF x.tyD rP with
    | none => pure none
    | some (fvs, _) =>
      match ← targetPiDomsWith fvs x.tyN with
      | none => pure none
      | some ws => do
        let pvars ← (List.range rP).mapM fun i =>
          if i < g.nP then exprGetD g.params i else g.slotVar (i - g.nP)
        let rec callsGo : Nat → Nat → AM (Option (List EIdx))
          | 0, _ => pure (some [])
          | n + 1, i => do
            match x.kinds.getD i .ordinary with
            | .ordinary => callsGo n (i + 1)
            | .recursive t tele => do
              let w ← exprGetD ws i
              match ← g.ihParts t tele w (rP + x.nF) with
              | none => pure none
              | some (xs, idx) =>
                match classRecOf recCls cvGs t with
                | none => pure none
                | some r => do
                  let f ← exprGetD fvs i
                  let fx ← mkAppN f xs
                  let rc ← internE (.const r rlvls)
                  let app ← mkAppN rc (pvars ++ idx ++ [fx])
                  let bs ← xs.mapM g.binder
                  let call ← closeLams bs (rP + x.nF) app
                  match ← callsGo n (i + 1) with
                  | none => pure none
                  | some rest => pure (some (call :: rest))
        match ← callsGo x.nF 0 with
        | none => pure none
        | some ihs => do
          let sv ← g.slotVar s
          let body ← mkAppN sv (fvs ++ ihs)
          let fbs ← fvs.mapM g.binder
          let r ← closeLams (g.pre ++ fbs) 0 body
          pure (some r)

/-! ## The stage -/

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:218-221 ClassSlot.isMinor
A minor premise's slot. -/
def ClassSlot.isMinor : ClassSlot → Bool
  | .minor .. => true
  | .motive _ => false

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:223-232 classMinorSlot
The minor premise slot of class `c`'s constructor `C`: exactly one. -/
def classMinorSlot (rd : ClassRead) (c : Nat) (C : NIdx) : AM (Nat × List (Nat × Nat)) := do
  let hits := (List.range rd.slots.length).filterMap fun s =>
    match (rd.slots[s]? : Option ClassSlot) with
    | some (.minor c' C' ihs) => if c' == c && C' == C then some (s, ihs) else none
    | _ => none
  match hits with
  | [h] => pure h
  | _ => fail (.invalid "generated recursor: the recursors' prefix does not have exactly one \
      minor premise for  (official: invalid recursor)")

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:234-254 classFieldsOf
**The minor premise's inductive hypotheses are the datum's recursive
fields**, one each: a field whose walked type names a member has exactly
one, at the class it names; an ordinary one none.  The Rust's `ihs_at` is
`ihs.filter`. -/
def classFieldsOf (p : BlockShape) (ihs : List (Nat × Nat)) :
    Nat → List EIdx → AM (List ClassField)
  | _, [] => pure []
  | i, f :: fs => do
    let w ← fvarTypeD f
    let occ ← nestOcc p.memberNames 0 0 w
    let hits := ihs.filter (·.1 == i)
    if !occ && hits.length == 0 then do
      let rest ← classFieldsOf p ihs (i + 1) fs
      pure (.ordinary :: rest)
    else if occ && hits.length == 1 then do
      let (bs, _) ← piBinders coreWalkFuel w
      let rest ← classFieldsOf p ihs (i + 1) fs
      pure (.recursive (hits.getD 0 default).2 bs.length :: rest)
    else
      fail (.invalid "generated recursor: the inductive hypotheses of 's minor premise are \
        not its recursive fields (official: invalid recursor)")

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:256-271 classNodesAgree
**Node agreement at one recursive field** (K.53′): at every entry of the
constructor, field `i` (opened at the datum's variables `fvs`) passes
`targetK53` against the inductive hypothesis's class `mc`. -/
def classNodesAgree (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx)
    (mc : TargetMajor) (tele : List (EIdx × BinderMeta)) (leaf : EIdx) (fvs : List EIdx)
    (i : Nat) : List NestCtorNf → AM Unit
  | [] => pure ()
  | e :: es => do
    let o ← targetPiDomsWith fvs e.ty
    let doms := o.getD []
    match doms[i]? with
    | none => fail (.invalid "generated recursor: a recorded normal form of  is too short")
    | some f =>
      if ← targetK53 mode fe p formerTys mc tele leaf f then
        classNodesAgree mode fe p formerTys mc tele leaf fvs i es
      else
        fail (.invalid "generated recursor: field  of  does not land at its inductive \
          hypothesis's class at every node of the positivity check (official: invalid recursor)")

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:273-277 classLeafAt
A walked field's leaf is headed by class `m`'s inductive. -/
def classLeafAt (m : TargetMajor) (leaf : EIdx) : AM Bool := do
  let hd ← getAppFn coreWalkFuel leaf
  if hd.tag == ETag.const then
    match ← viewConst hd with
    | none => failDanglingE
    | some (I, _) => pure (I == m.ind)
  else pure false

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:279-293 classFieldsAgree
Node agreement at every recursive field of the datum (`ks` from field `i`
on). -/
def classFieldsAgree (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx)
    (ms : List TargetMajor) (fvs : List EIdx) (es : List NestCtorNf) :
    Nat → List ClassField → AM Unit
  | _, [] => pure ()
  | i, .ordinary :: ks => classFieldsAgree mode fe p formerTys ms fvs es (i + 1) ks
  | i, .recursive t tele :: ks => do
    let fv ← exprGetD fvs i
    let fty ← fvarTypeD fv
    match ← stripPis tele fty with
    | none => fail (.internal "generated recursor: field telescope")
    | some (teleB, leaf) => do
      let mt ← targetMajorAt ms t
      if ← classLeafAt mt leaf then do
        classNodesAgree mode fe p formerTys mt teleB leaf fvs i es
        classFieldsAgree mode fe p formerTys ms fvs es (i + 1) ks
      else
        fail (.invalid "generated recursor: field  of  does not end in its inductive \
          hypothesis's class (official: invalid recursor)")

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:295-313 classCtorOf
**One constructor of class `c`, read for the generator**: its entries in the
class's table (the first the DATUM), the minor premise's inductive hypotheses
against the datum's recursive fields, node agreement at every entry, and the
constructor's declared type at the class.  The Rust's `nfs_of_ctor` is the
`filter`. -/
def classCtorOf (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx)
    (rd : ClassRead) (ms : List TargetMajor) (c : Nat) (cA : IConstantVal × Nat) :
    AM ClassCtor := do
  let m ← targetMajorAt ms c
  let es := m.nfs.filter (·.ctor == cA.1.name)
  match es with
  | [] => fail (.internal "generated recursor: the constructor  of a class has no entry in \
      the positivity check's table")
  | e0 :: _ => do
    let (_, ihs) ← classMinorSlot rd c cA.1.name
    match ← openPisAtFvarsF cA.2 e0.ty (p.nP + p.k) with
    | none => fail (.internal "generated recursor: datum telescope")
    | some (fvs, _) => do
      let kinds ← classFieldsOf p ihs 0 fvs
      classFieldsAgree mode fe p formerTys ms fvs es 0 kinds
      let t0 ← targetCtorAt m cA.1
      match ← instPisWith m.ds t0 with
      | none => fail (.internal "generated recursor: constructor parameter telescope")
      | some tyD => pure ⟨cA.1, cA.2, kinds, tyD, e0.ty⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:315-323 classCtorsOf
Every constructor of class `c`. -/
def classCtorsOf (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx)
    (rd : ClassRead) (ms : List TargetMajor) (c : Nat) :
    List (IConstantVal × Nat) → AM (List ClassCtor)
  | [] => pure []
  | cA :: cs => do
    let x ← classCtorOf mode fe p formerTys rd ms c cA
    let xs ← classCtorsOf mode fe p formerTys rd ms c cs
    pure (x :: xs)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:325-332 classesCtors
Every class's constructors, from class `c` on (the Rust walks `ms` itself
from index `c`; the twin walks its tail alongside). -/
def classesCtors (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx)
    (rd : ClassRead) (ms : List TargetMajor) : Nat → List TargetMajor → AM (List (List ClassCtor))
  | _, [] => pure []
  | c, m :: rest => do
    let xs ← classCtorsOf mode fe p formerTys rd ms c m.ctors
    let xss ← classesCtors mode fe p formerTys rd ms (c + 1) rest
    pure (xs :: xss)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:334-344 classMajors
Every class checked as a major (`targetMajorOf`, `targetMajorPins`), over the
block's canonical parameters `pfvs`. -/
def classMajors (mode : CheckMode) (fe : IFEnv) (p : BlockShape)
    (ctorsAs : List (List (IConstantVal × Nat))) (pfvs : List EIdx) :
    List ClassKey → AM (List TargetMajor)
  | [] => pure []
  | key :: keys => do
    let hd ← internE (.const key.ind key.lvls)
    let mty ← mkAppN hd key.ds
    let m ← targetMajorOf fe p ctorsAs pfvs pfvs mty
    targetMajorPins mode fe p.nP m
    let ms ← classMajors mode fe p ctorsAs pfvs keys
    pure (m :: ms)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:346-353 classesNfs
Every class with its entries of the table `tbl` (`targetMajorNfs`). -/
def classesNfs (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx)
    (tbl : List NestCtorNf) : List TargetMajor → AM (List TargetMajor)
  | [] => pure []
  | m :: ms => do
    let es ← targetMajorNfs mode fe p formerTys m.pfvs m.lvls m.ds m.ctors tbl
    let rest ← classesNfs mode fe p formerTys tbl ms
    pure ({ m with nfs := es } :: rest)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:355-362 classFormerTy
A class's former type: a member's own, an outside class's stored former at
the class's levels.  The Rust's `class_former_tys` is `ms.mapM`. -/
def classFormerTy (fe : IFEnv) (cvTas : List IConstantVal) (m : TargetMajor) : AM EIdx :=
  match m.member with
  | some t =>
    match cvTas[t]? with
    | some cv => pure cv.type
    | none => internE (.bvar 0)
  | none =>
    match fe.find? m.ind with
    | some (.indInfo cv _) => instLPFast coreWalkFuel cv.levelParams m.lvls cv.type
    | _ => fail (.internal "generated recursor: a class's former vanished")

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:364-387 classConstOk
**A generated constant, checked**: `checkConstantValF` without the annotation
pass (the generator writes every binder datum), the guards in the cited
order, then its type inferred and a sort.  The Rust's `class_const_ok_type`
is its second half. -/
def classConstOk (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal) : AM IConstantVal := do
  if (fe.find? cv.name).isSome then
    fail (.invalid "duplicate declaration")
  if (← reservedBasisNames).contains cv.name then
    fail (.invalid "reserved basis name")
  if ← NIdx.isProjFnShape cv.name then
    fail (.invalid "reserved projection name")
  unless nameNodup cv.levelParams do
    fail (.invalid "duplicate universe parameters in")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.internal "generated recursor: loose bound variable in type of")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.internal "generated recursor: free variable in type of")
  unless ← allLevelParamsDefined cv.levelParams cv.type do
    fail (.invalid "undeclared universe parameter in type of")
  unless ← constsResolveFFast fe cv.type do
    fail (← unresolvedConstsError "type of" cv.type)
  let stype ← inferTypeCore mode fe checkFuel 0 cv.type
  let _u ← ensureSortCore mode fe checkFuel 0 stype
  pure cv

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:389-407 classRecTyOk
**One recursor's generated type, checked and compared**: the record's member,
rule prefix and major index are the generated ones; the generated type is
checked as a constant under the record's name and level parameters and must
be defeq to the stream's checked type `cvRi`. -/
def classRecTyOk (mode : CheckMode) (fe : IFEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (cvRi : IConstantVal) (c : Nat) : AM IConstantVal := do
  let ci ← targetMajorAt g.cls c
  unless rc.tgt == ci.member.getD k do
    fail (.invalid "generated recursor: the recursor record's member is not its class's")
  unless rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + ci.nIdx do
    fail (.invalid "generated recursor: the recursor record's rule prefix or major index is \
      not the generated one")
  match ← classGenRecTy g c with
  | none => fail (.internal "generated recursor: recursor type")
  | some gty => do
    let cvG ← classConstOk mode fe ⟨rc.cvR.name, rc.cvR.levelParams, gty⟩
    if ← isDefEqCore mode fe checkFuel 0 cvRi.type cvG.type then pure cvG
    else fail (.invalid "generated recursor: the type of  is not the generated one \
      (official: invalid recursor)")

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:409-418 classRecTysOk
Every recursor's generated type, pairwise with the stream's checked types and
the recursors' classes; the lists running out unevenly is internal. -/
def classRecTysOk (mode : CheckMode) (fe : IFEnv) (g : ClassGen) (k : Nat) :
    List RecShape → List IConstantVal → List Nat → AM (List IConstantVal)
  | rc :: rcs, cvRi :: cvs, c :: cs => do
    let x ← classRecTyOk mode fe g k rc cvRi c
    let xs ← classRecTysOk mode fe g k rcs cvs cs
    pure (x :: xs)
  | [], _, _ => pure []
  | _, _, _ => fail (.internal "generated recursor: recursor list")

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:420-446 classRuleOk
con-leche: ConLeche/Cached/CheckerC.lean:98-126 sharedOpsRuleR
**One generated rule, installed as generated**: closed, its level parameters
the recursor's, resolving and typed at the rule-less recursors' environment
`feR` (`sharedOpsRuleR`'s flush leaving the inference), its λ-telescope `n`
long, its λ-domains resolving at the constructors' environment (`feR` at the
bound `visT`) and annotated with the family's datum `pw`.  The Rust's
`domains_resolve`, `domains_pw` and `class_rule_ok_tail` are its parts. -/
def classRuleOk (mode : CheckMode) (visT : Nat) (feR : IFEnv) (cvR : IConstantVal)
    (pw : PropWhen) (n : Nat) (gen : EIdx) : AM EIdx := do
  unless ← looseBVarsBoundedFast coreWalkFuel 0 gen do
    fail (.internal "generated recursor: a rule of  is not closed")
  if ← hasFvarFast coreWalkFuel gen then
    fail (.internal "generated recursor: a rule of  is not closed")
  unless ← allLevelParamsDefined cvR.levelParams gen do
    fail (.internal "generated recursor: a rule of  names an undeclared universe parameter")
  unless ← constsResolveFFast feR gen do
    fail (← unresolvedConstsError "generated rule of" gen)
  let _ ← inferTypeCore mode feR checkFuel 0 gen
  -- `sharedOpsRuleR`'s `inferType`: the flush leaving the rule-less
  -- recursors' environment
  flushCaches
  match ← stripLams n gen with
  | none => fail (.internal "generated recursor: a rule of  is not a λ-telescope over the \
      recursor's prefix and the constructor's fields")
  | some (rbs, _) => do
    unless ← rbs.allM (fun b => constsResolveFFast (feR.restrictTo visT) b.1) do
      fail (← unresolvedConstsError "the domains of a generated rule of" gen)
    if rbs.all (fun b => b.2.pw == pw) then pure gen
    else fail (.internal "generated recursor: a rule of  does not annotate its λ-binders \
      with the family's elimination datum")

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:448-459 classRulesOk
A recursor's generated rules, one per constructor of its class. -/
def classRulesOk (mode : CheckMode) (visT : Nat) (feR : IFEnv) (g : ClassGen)
    (recCls : List Nat) (cvGs : List IConstantVal) (cvR : IConstantVal) (pw : PropWhen)
    (c : Nat) : List ClassCtor → AM (List EIdx)
  | [] => pure []
  | x :: xs => do
    let rlvls ← paramLevels cvR.levelParams
    match ← classGenRule g recCls cvGs rlvls c x with
    | none => fail (.invalid "generated recursor: the rule of  calls a class whose recursor \
        the stream omits (official: unknown constant)")
    | some gen => do
      let r ← classRuleOk mode visT feR cvR pw (g.nP + g.slots.length + x.nF) gen
      let rs ← classRulesOk mode visT feR g recCls cvGs cvR pw c xs
      pure (r :: rs)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:461-470 classRecsRulesOk
Every recursor's generated rules, with its class (the shorter of the two
lists decides, as the cited zip does).  `recCls` and `cvGs` are the whole
lists `classRecOf` reads; the two walked lists are their tails. -/
def classRecsRulesOk (mode : CheckMode) (visT : Nat) (feR : IFEnv) (g : ClassGen)
    (recCls : List Nat) (pw : PropWhen) (cvGs : List IConstantVal) :
    List IConstantVal → List Nat → AM (List (IConstantVal × TargetMajor × List EIdx))
  | cvG :: cvs, c :: cs => do
    let xs := g.ctors.getD c []
    let rhss ← classRulesOk mode visT feR g recCls cvGs cvG pw c xs
    let m ← targetMajorAt g.cls c
    let rest ← classRecsRulesOk mode visT feR g recCls pw cvGs cvs cs
    pure ((cvG, m, rhss) :: rest)
  | _, _ => pure []

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:472-479 classStreamRecs
The stream's recursor constants, checked (`checkConstantValF`). -/
def classStreamRecs (mode : CheckMode) (fe : IFEnv) : List RecShape → AM (List IConstantVal)
  | [] => pure []
  | rc :: rcs => do
    let cv ← checkConstantVal mode fe rc.cvR
    let cvs ← classStreamRecs mode fe rcs
    pure (cv :: cvs)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:481-484 classKeyCanon
A class key's parameters moved to the block's canonical parameter
variables. -/
def classKeyCanon (params : List EIdx) (k : ClassKey) : AM ClassKey := do
  let ds ← k.ds.mapM (targetCanonParams params)
  pure { k with ds := ds }

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:494-499 classSeeds
The seeds: every OUTSIDE class in the positivity check's representation
(`nestSeedOf`), in order. -/
def classSeeds (ctx : NestCtx) (holes : List EIdx) : List TargetMajor → AM (List (NestKey × Nat))
  | [] => pure []
  | m :: ms => do
    match m.member with
    | some _ => classSeeds ctx holes ms
    | none => do
      let sd ← nestSeedOf ctx holes m.ind m.lvls m.ds m.nPc
      let rest ← classSeeds ctx holes ms
      pure (sd :: rest)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:501-516 classKeyOf
**A class key, made checkable**: moved to the canonical parameter variables,
its parameters closed over them (the Rust's `params_closed`, the `bvarB`
read first), and annotated at the formers' environment over the parameters
(the Rust's `annotate_list`). -/
def classKeyOf (mode : CheckMode) (fe : IFEnv) (nP : Nat) (params : List EIdx)
    (k : ClassKey) : AM ClassKey := do
  let k2 ← classKeyCanon params k
  let closed ← k2.ds.allM fun x => do
    if (← bvarB coreWalkFuel x) != 0 then pure false
    else pure ((← fvarB coreWalkFuel x) ≤ nP)
  unless closed do
    fail (.invalid "target rec: the major's parameters mention more than the \
      recursor's parameters")
  let ds ← k2.ds.mapM fun x => annotateCore mode fe checkFuel nP x
  pure { k2 with ds := ds }

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:518-536 checkBlockClasses
**The classes, read and checked** at the formers' environment `fe`: the
pre-pass on the stream's raw recursor types, every class key made checkable,
every class checked as a major over the canonical parameters, exactly one
class per member.  The Rust's `class_keys_of`, `classes_at_member` and
`one_class_per_member` are its parts. -/
def checkBlockClasses (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (params : List EIdx)
    (ctorsAs : List (List (IConstantVal × Nat))) : AM (ClassRead × List TargetMajor) := do
  match ← classRead p fe p.nP p.recs with
  | none => fail (.invalid "generated recursor: the recursor family is not of the generated \
      shape (official: invalid recursor)")
  | some rd => do
    let ks := ClassRead.classes rd.slots
    let keys ← ks.mapM (classKeyOf mode fe p.nP params)
    let ms ← classMajors mode fe p ctorsAs params keys
    if (List.range p.k).all (fun t => (ms.filter (·.member == some t)).length == 1) then
      pure (rd, ms)
    else
      fail (.invalid "generated recursor: the recursor family does not have exactly one \
        class per member (official: invalid recursor)")

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:545-549 classFeR
con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:338-346 consBlockRecsBare
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:175-180 consBlockRecsBareF
**The rule-less generated recursors consed onto the constructors'
environment**, pushed TEMPORARILY (the module note): each recursor `m` at its
record's major index and rule prefix, with no rule.  Returns the rows the
pushes displaced (`idx[n]?` before each push), in push order, for the pop. -/
def classFeR (p : BlockShape) (cvGs : List IConstantVal) (recCls : List Nat) (fe : IFEnv) :
    IFEnv × List (NIdx × Option (Nat × IConstantInfo)) :=
  go 0 (cvGs.zip recCls) fe []
where
  go : Nat → List (IConstantVal × Nat) → IFEnv → List (NIdx × Option (Nat × IConstantInfo)) →
      IFEnv × List (NIdx × Option (Nat × IConstantInfo))
    | _, [], fe, prevs => (fe, prevs)
    | m, (cv, _) :: rest, fe, prevs =>
      let prev := fe.idx[cv.name]?
      let fe2 := fe.push (.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m) [])
      go (m + 1) rest fe2 (prevs ++ [(cv.name, prev)])

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:551-593 genRecCheck
con-leche: ConLeche/Cached/CheckerC.lean:128-134 shadowOpsC
**The generated recursor stage**, at the constructors' environment `fe`, on
the classes and the positivity check's table: the pins, the stream's recursor
types checked, the elimination guard, the classes' table entries and
constructors, then generation — the prefix, every recursor's type checked and
compared, the rule-less recursors pushed, the flush entering them, every rule
installed, the recursors popped (the pushes undone in reverse order) and the
flush leaving them.  Hands the index back, as the Rust does (the module
note).  The Rust's `some_outside`, `minor_count`, `ctor_count`,
`former_types`, `gen_rec_classes` and `gen_rec_generate` are its parts. -/
def genRecCheck (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (nestedBit : Bool)
    (params : List EIdx) (tbl : List NestCtorNf) (rd : ClassRead) (ms : List TargetMajor)
    (cvTas : List IConstantVal) (block : List IConstantInfo) :
    AM (IFEnv × List (IConstantVal × TargetMajor × List EIdx)) := do
  targetRecPins p block
  -- the stream's recursor types, checked: the generated types are compared with them
  let cvRis ← classStreamRecs mode fe p.recs
  -- the elimination guard
  if p.k == 0 then
    fail (.invalid "generated recursor: the block declares no family")
  if p.large then
    let nb := nestedBit || ms.any (·.member.isNone)
    unless ← blockLargeElimAllowed p nb do
      fail (.invalid "generated recursor: large eliminator on a block whose sort may be Prop \
        (official: elim_only_at_universe_zero)")
  let formerTys := cvTas.map (·.type)
  let ms2 ← classesNfs mode fe p formerTys tbl ms
  -- per class and constructor: the datum, the inductive hypotheses, node agreement
  let ctors ← classesCtors mode fe p formerTys rd ms2 0 ms2
  unless (rd.slots.filter ClassSlot.isMinor).length == (ctors.map List.length).sum do
    fail (.invalid "generated recursor: the recursors' prefix has a minor premise for no \
      constructor of a class (official: invalid recursor)")
  -- generation
  let formerTysC ← ms2.mapM (classFormerTy fe cvTas)
  let elim ← structElimLevel p.elim p.large
  let bm ← classGenBm elim
  let g0 : ClassGen := ⟨p.nP, params, ms2, formerTysC, rd.slots, ctors, elim, bm, []⟩
  match ← g0.prefixBinders with
  | none => fail (.internal "generated recursor: recursor prefix")
  | some pre => do
    let g := { g0 with pre := pre }
    let cvGs ← classRecTysOk mode fe g p.k p.recs cvRis rd.recCls
    let visT := fe.visibleBelow
    let (feR, prevs) := classFeR p cvGs rd.recCls fe
    flushCaches
    let out ← classRecsRulesOk mode visT feR g rd.recCls g.bm.pw cvGs cvGs rd.recCls
    let fe2 := prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feR
    flushCaches
    pure (fe2, out)

end ConRon.Arena
