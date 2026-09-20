/-
# The `ProjRec` twins, differentially (task #97e part 2)

The module-level differential check of `Arena/Frontend/ProjRec.lean`, in the
shape `Arena/ExprOpsTest.lean` established for the `ExprOps` twins:

> build a fixture as con-leche `Expr` values, intern it, run the twin, read
> the answer back with `denoteE`, and compare against con-leche's own
> `ConLeche/Frontend/ProjRec.lean` function applied to the fixture.

The expected side is **computed, never written out**: every `#guard` below
names a con-leche function applied to the same con-leche value the store was
interned from, so a check cannot drift from the twin.  What IS written by hand
is the fixture itself — and the round-trip guards (§"The fixture denotes what
it should") say that the store holds exactly it.

**The fixture** is a two-field structure and its two projection functions,
which is the smallest thing the rewrite is about:

    S.{u}      : ∀ (α : Sort (u+1)), Sort (u+1)
    S.mk.{u}   : ∀ (α : Sort (u+1)) (a b : α), S α
    S.rec.{v,u}: ∀ (α : Sort (u+1)) (motive : S α → Sort v)
                   (mk : ∀ (a b : α), motive (S.mk α a b)) (t : S α), motive t
    S.fst.{u}  : ∀ (α : Sort (u+1)) (self : S α), α
               := fun α self => .proj S 0 self
    S.snd.{u}  : the same at field 1

`projRecOwners` is checked at TWO blocks: the structure alone, which
`nativeParts?` recognises as a direct block so that the rewrite serves none of
it, and the same structure beside a second (indexed) type former, which is the
MUTUAL shape neither recogniser takes and where the rewrite's owner list is
`[S]`.  Both are compared against con-leche's `projRecOwners` on the
denotation, so the delegation of the two recognisers (`ProjRec.lean`'s
deviation 3) is checked on both sides of its verdict.
-/
import ConRon.Arena.Frontend.ProjRec
import ConLeche.Frontend.ProjRec

namespace ConRon.Arena.ProjRecTest

open ConLeche
open ConRon.Arena
open ConRon.Arena.Frontend

/-! ## The fixture, as con-leche values -/

/-- con-leche: none — the fixture's level parameter `u`. -/
private def uName : ConLeche.Name := .str .anonymous "u"
/-- con-leche: none — the recursor's elimination level parameter `v`. -/
private def vName : ConLeche.Name := .str .anonymous "v"
/-- con-leche: none — the fixture structure's name. -/
private def sName : ConLeche.Name := .str .anonymous "S"
/-- con-leche: none — the mutual block's second type former. -/
private def tName : ConLeche.Name := .str .anonymous "T"
/-- con-leche: none — the structure's constructor. -/
private def mkName : ConLeche.Name := .str sName "mk"
/-- con-leche: none — the structure's recursor. -/
private def recName : ConLeche.Name := .str sName "rec"
/-- con-leche: none — the level `u`. -/
private def pu : Level := .param uName
/-- con-leche: none — the level `v`. -/
private def pv : Level := .param vName
/-- con-leche: none — the binder metadata the parse writes. -/
private def bm : BinderMeta := ⟨.never⟩

/-- con-leche: none — `S α`, with `α` at `bvar k`. -/
private def sApp (k : Nat) : Expr := .app (.const sName [pu]) (.bvar k)

/-- con-leche: none — `S.{u} : ∀ (α : Sort (u+1)), Sort (u+1)`. -/
private def sTy : Expr := .forallE (.sort (.succ pu)) (.sort (.succ pu)) bm

/-- con-leche: none — `T.{u} : ∀ (α : Sort (u+1)) (i : Sort (u+1)), Sort (u+1)`,
the block's second type former: an INDEXED one, so it is not a candidate for
the rewrite and only `S` is. -/
private def tTy : Expr :=
  .forallE (.sort (.succ pu)) (.forallE (.sort (.succ pu)) (.sort (.succ pu)) bm) bm

/-- con-leche: none — `S.mk.{u} : ∀ (α : Sort (u+1)) (a b : α), S α`. -/
private def ctorTy : Expr :=
  .forallE (.sort (.succ pu))
    (.forallE (.bvar 0) (.forallE (.bvar 1) (sApp 2) bm) bm) bm

/-- con-leche: none — `S.mk α a b` in the minor's codomain frame
(`b = bvar 0`, `a = bvar 1`, `motive = bvar 2`, `α = bvar 3`). -/
private def mkSpine : Expr :=
  .app (.app (.app (.const mkName [pu]) (.bvar 3)) (.bvar 1)) (.bvar 0)

/-- con-leche: none — `S.rec.{v,u}`, the eliminator: one motive, one minor,
no indices. -/
private def recTy : Expr :=
  .forallE (.sort (.succ pu))
    (.forallE (.forallE (sApp 0) (.sort pv) bm)
      (.forallE
        (.forallE (.bvar 1) (.forallE (.bvar 2) (.app (.bvar 2) mkSpine) bm) bm)
        (.forallE (sApp 2) (.app (.bvar 2) (.bvar 0)) bm) bm) bm) bm

/-- con-leche: none — `S.fst.{u} : ∀ (α : Sort (u+1)) (self : S α), α` (the
type is the same for both fields of this structure). -/
private def projTy : Expr :=
  .forallE (.sort (.succ pu)) (.forallE (sApp 0) (.bvar 1) bm) bm

/-- con-leche: none — `fun α self => .proj S i self`, the shape the rewrite
recognises. -/
private def projVal (i : Nat) : Expr :=
  .lam (.sort (.succ pu)) (.lam (sApp 0) (.proj sName i (.bvar 0)) bm) bm

/-- con-leche: none — a value that is NOT of the projection shape: the
subject is not `bvar 0`. -/
private def badVal : Expr :=
  .lam (.sort (.succ pu)) (.lam (sApp 0) (.proj sName 0 (.bvar 1)) bm) bm

/-- con-leche: none — an artifact iota statement `∀ (x : Sort (u+1)),
@Eq.{u} x x x`: what `projIotaLevel` reads the field's sort off. -/
private def iotaTy : Expr :=
  .forallE (.sort (.succ pu))
    (.app (.app (.app (.const ConLeche.eqName [pu]) (.bvar 0)) (.bvar 0))
      (.bvar 0)) bm

/-- con-leche: none — `S._model.proj_0.iota`, the artifact's own name. -/
private def iotaName : ConLeche.Name :=
  ((sName.str "_model").str "proj_0").str "iota"

/-- con-leche: none — the rewrite's owner record, as con-leche states it. -/
private def ownerP : ConLeche.Frontend.ProjRecOwner :=
  ⟨sName, [uName], 1, mkName, 2, recName, [vName, uName], recTy, 1, 1⟩

/-- con-leche: none — a dummy iota rule, enough to make a recursor record
carry one. -/
private def dummyRule : RecRule :=
  ⟨mkName, 2, 0, .inert, .bvar 0, false, false, false⟩

/-- con-leche: none — **the MUTUAL block**: two type formers, so neither
`structPartsCore?` (which pattern-matches a three-constant block) nor
`nativeParts?` (whose `sumSplit` refuses several formers) recognises it — the
class the rewrite exists for.  `S` is its structure-like member and `T`, being
indexed, is not a candidate. -/
private def blockP : List ConstantInfo :=
  [ .indInfo ⟨sName, [uName], sTy⟩ {},
    .indInfo ⟨tName, [uName], tTy⟩ {},
    .ctorInfo ⟨mkName, [uName], ctorTy⟩ 1 2,
    .recInfo ⟨recName, [vName, uName], recTy⟩ 3 3 [dummyRule] ]

/-- con-leche: none — **the DIRECT block**: the same structure alone, which
`nativeParts?` recognises, so the rewrite serves none of it.  The two blocks
put the delegated recognisers on both sides of their verdict. -/
private def blockD : List ConstantInfo :=
  [ .indInfo ⟨sName, [uName], sTy⟩ {},
    .ctorInfo ⟨mkName, [uName], ctorTy⟩ 1 2,
    .recInfo ⟨recName, [vName, uName], recTy⟩ 3 3 [dummyRule] ]

/-- con-leche: none — the mutual block's type records, as `projRecOwners`
takes them. -/
private def typesP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat ×
    List ConLeche.Name × Bool) :=
  [(sName, [uName], sTy, 1, 0, [mkName], false),
   (tName, [uName], tTy, 1, 1, [], false)]
/-- con-leche: none — the direct block's type records. -/
private def typesD : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat ×
    List ConLeche.Name × Bool) :=
  [(sName, [uName], sTy, 1, 0, [mkName], false)]
/-- con-leche: none — the block's constructor records. -/
private def ctorsP : List (ConLeche.Name × Nat × Expr) := [(mkName, 2, ctorTy)]
/-- con-leche: none — the block's recursor records. -/
private def recsP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat) :=
  [(recName, [vName, uName], recTy, 1, 1)]

/-! ## The fixture, interned -/

/-- con-leche: none — the handles the checks below name. -/
private structure Fx where
  sH : NIdx
  mkH : NIdx
  recH : NIdx
  uH : NIdx
  vH : NIdx
  puH : LIdx
  sTyH : EIdx
  ctorTyH : EIdx
  recTyH : EIdx
  projTyH : EIdx
  projVal0 : EIdx
  projVal1 : EIdx
  badValH : EIdx
  iotaTyH : EIdx
  iotaNameH : NIdx
  sApp0 : EIdx
  owner : ConRon.Arena.Frontend.ProjRecOwner
  block : List IConstantInfo
  blockD : List IConstantInfo
  types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)
  typesD : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)
  ctors : List (NIdx × Nat × EIdx)
  recs : List (NIdx × List NIdx × EIdx × Nat × Nat)
  deriving Inhabited

/-- con-leche: none — intern the whole fixture into one empty store, with
`Arena/Frontend/Readback.lean`'s `internExpr` / `internCIList` (so the round
trip below checks those too). -/
private def build : AM Fx := do
  let sH ← internName sName
  let mkH ← internName mkName
  let recH ← internName recName
  let uH ← internName uName
  let vH ← internName vName
  let puH ← internLevel pu
  let sTyH ← internExpr sTy
  let ctorTyH ← internExpr ctorTy
  let recTyH ← internExpr recTy
  let projTyH ← internExpr projTy
  let projVal0 ← internExpr (projVal 0)
  let projVal1 ← internExpr (projVal 1)
  let badValH ← internExpr badVal
  let iotaTyH ← internExpr iotaTy
  let iotaNameH ← internName iotaName
  let sApp0 ← internExpr (sApp 0)
  let tH ← internName tName
  let tTyH ← internExpr tTy
  let (_, block) ← internCIList ∅ blockP
  let (_, blockD) ← internCIList ∅ blockD
  pure { sH, mkH, recH, uH, vH, puH, sTyH, ctorTyH, recTyH, projTyH,
         projVal0, projVal1, badValH, iotaTyH, iotaNameH, sApp0,
         owner := ⟨sH, [uH], 1, mkH, 2, recH, [vH, uH], recTyH, 1, 1⟩,
         block, blockD,
         types := [(sH, [uH], sTyH, 1, 0, [mkH], false),
                   (tH, [uH], tTyH, 1, 1, [], false)],
         typesD := [(sH, [uH], sTyH, 1, 0, [mkH], false)],
         ctors := [(mkH, 2, ctorTyH)],
         recs := [(recH, [vH, uH], recTyH, 1, 1)] }

/-- con-leche: none — the fixture built into an empty store. -/
private def buildRes : Except CheckError (Fx × AState) :=
  build.run (AState.init EStore.empty)

#guard (match buildRes with | .ok _ => true | .error _ => false)

/-- con-leche: none — the fixture's handles (the build cannot fail; the
`#guard` above says so). -/
private def fx : Fx :=
  match buildRes with | .ok (f, _) => f | .error _ => default

/-- con-leche: none — the state the checks run from: the store the fixture
was interned into. -/
private def S0 : AState :=
  match buildRes with | .ok (_, s) => s | .error _ => AState.init EStore.empty

/-- con-leche: none — the store the fixture was interned into. -/
private def st0 : EStore := S0.store

/-- con-leche: none — the fuel every check runs at.  The fixture's deepest
term is nine nodes deep and the store holds under a hundred; 1000 is a
comfortable margin. -/
private def F : Nat := 1000

/-! ## The fixture denotes what it should

The one place a con-leche value is compared against a hand-written one.
Everything after this compares a twin's answer against con-leche's function
applied to these same values, which is only meaningful because these hold. -/

#guard denoteE st0 fx.sTyH == some sTy
#guard denoteE st0 fx.ctorTyH == some ctorTy
#guard denoteE st0 fx.recTyH == some recTy
#guard denoteE st0 fx.projTyH == some projTy
#guard denoteE st0 fx.projVal0 == some (projVal 0)
#guard denoteE st0 fx.projVal1 == some (projVal 1)
#guard denoteE st0 fx.badValH == some badVal
#guard denoteE st0 fx.iotaTyH == some iotaTy
#guard denoteE st0 fx.sApp0 == some (sApp 0)
#guard denoteN st0.ns fx.sH == some sName
#guard denoteN st0.ns fx.iotaNameH == some iotaName
#guard denoteL st0.ls fx.puH == some pu
#guard denoteCIList st0 fx.block == some blockP
#guard denoteCIList st0 fx.blockD == some blockD

/-! ## The checkers

Each runs the twin from `S0` and reads the answer back against the store the
run *ended* in (the arena grows as the rewrite builds terms). -/

/-- con-leche: none — map `denoteE` over a list of handles. -/
private def mapDen (s : EStore) : List EIdx → Option (List Expr)
  | [] => some []
  | h :: hs =>
    match denoteE s h, mapDen s hs with
    | some e, some es => some (e :: es)
    | _, _ => none

/-- con-leche: none — map `denoteE` over a binder list. -/
private def mapDenB (s : EStore) :
    List (EIdx × BinderMeta) → Option (List (Expr × BinderMeta))
  | [] => some []
  | (h, m) :: hs =>
    match denoteE s h, mapDenB s hs with
    | some e, some es => some ((e, m) :: es)
    | _, _ => none

/-- con-leche: none — map the owner record's denotation. -/
private def denOwner (s : EStore) (o : ConRon.Arena.Frontend.ProjRecOwner) :
    Option ConLeche.Frontend.ProjRecOwner :=
  match denoteN s.ns o.T, denoteNList s.ns o.lps, denoteN s.ns o.ctor with
  | some t, some lps, some c =>
    match denoteN s.ns o.recName, denoteNList s.ns o.recLps, denoteE s o.recType with
    | some rn, some rlps, some rty =>
      some ⟨t, lps, o.nP, c, o.nF, rn, rlps, rty, o.numMotives, o.numMinors⟩
    | _, _, _ => none
  | _, _, _ => none

/-- con-leche: none — the denotation of an owner list. -/
private def denOwners (s : EStore) :
    List ConRon.Arena.Frontend.ProjRecOwner →
    Option (List ConLeche.Frontend.ProjRecOwner)
  | [] => some []
  | o :: os =>
    match denOwner s o, denOwners s os with
    | some x, some xs => some (x :: xs)
    | _, _ => none

/-- con-leche: none — `ProjRecOwner` derives `Repr` and `Inhabited` on both
sides and no `BEq`, so the owner comparison is field by field. -/
private def beqOwner (a b : ConLeche.Frontend.ProjRecOwner) : Bool :=
  a.T == b.T && a.lps == b.lps && a.nP == b.nP && a.ctor == b.ctor &&
  a.nF == b.nF && a.recName == b.recName && a.recLps == b.recLps &&
  a.recType == b.recType && a.numMotives == b.numMotives &&
  a.numMinors == b.numMinors

/-- con-leche: none — owner lists, compared field by field. -/
private def beqOwners :
    List ConLeche.Frontend.ProjRecOwner →
    List ConLeche.Frontend.ProjRecOwner → Bool
  | [], [] => true
  | a :: as, b :: bs => beqOwner a b && beqOwners as bs
  | _, _ => false

/-- con-leche: none — an `EIdx`-valued twin against a con-leche `Expr`. -/
private def chkE (c : AM EIdx) (expect : Expr) : Bool :=
  match c.run S0 with
  | .ok (r, s') => denoteE s'.store r == some expect
  | .error _ => false

/-- con-leche: none — an `Option EIdx`-valued twin. -/
private def chkOE (c : AM (Option EIdx)) (expect : Option Expr) : Bool :=
  match c.run S0, expect with
  | .ok (some r, s'), some e => denoteE s'.store r == some e
  | .ok (none, _), none => true
  | _, _ => false

/-- con-leche: none — an `NIdx`-valued twin against a con-leche `Name`. -/
private def chkN (c : AM NIdx) (expect : ConLeche.Name) : Bool :=
  match c.run S0 with
  | .ok (r, s') => denoteN s'.store.ns r == some expect
  | .error _ => false

/-- con-leche: none — a `Bool`-valued twin. -/
private def chkB (c : AM Bool) (expect : Bool) : Bool :=
  match c.run S0 with
  | .ok (r, _) => r == expect
  | .error _ => false

/-- con-leche: none — an `Option LIdx`-valued twin. -/
private def chkOL (c : AM (Option LIdx)) (expect : Option Level) : Bool :=
  match c.run S0, expect with
  | .ok (some r, s'), some u => denoteL s'.store.ls r == some u
  | .ok (none, _), none => true
  | _, _ => false

/-- con-leche: none — the `stripPisAll` shape. -/
private def chkStrip (c : AM (List (EIdx × BinderMeta) × EIdx))
    (expect : List (Expr × BinderMeta) × Expr) : Bool :=
  match c.run S0 with
  | .ok (r, s') =>
    mapDenB s'.store r.1 == some expect.1 && denoteE s'.store r.2 == some expect.2
  | .error _ => false

/-- con-leche: none — the `projRecOwners` shape. -/
private def chkOwners (c : AM (List ConRon.Arena.Frontend.ProjRecOwner))
    (expect : List ConLeche.Frontend.ProjRecOwner) : Bool :=
  match c.run S0 with
  | .ok (r, s') =>
    match denOwners s'.store r with
    | some os => beqOwners os expect
    | none => false
  | .error _ => false

/-! ## `projIotaName`, `isProjIotaName`, `projIotaLevel` -/

#guard chkN (projIotaName fx.sH 0) (ConLeche.Frontend.projIotaName sName 0)
#guard chkN (projIotaName fx.sH 3) (ConLeche.Frontend.projIotaName sName 3)

#guard chkB (isProjIotaName fx.iotaNameH)
  (ConLeche.Frontend.isProjIotaName iotaName)
#guard chkB (isProjIotaName fx.sH) (ConLeche.Frontend.isProjIotaName sName)
#guard chkB (isProjIotaName fx.mkH) (ConLeche.Frontend.isProjIotaName mkName)
-- the positive case really is positive, so the two `false`s above are not
-- a check that passes for the wrong reason
#guard ConLeche.Frontend.isProjIotaName iotaName == true

#guard chkOL (projIotaLevel F fx.iotaTyH) (ConLeche.Frontend.projIotaLevel iotaTy)
#guard chkOL (projIotaLevel F fx.recTyH) (ConLeche.Frontend.projIotaLevel recTy)
#guard ConLeche.Frontend.projIotaLevel iotaTy == some pu

/-! ## `occursConst` -/

#guard chkB (occursConstFast F fx.sH fx.recTyH)
  (ConLeche.Frontend.occursConstFast sName recTy)
#guard chkB (occursConstFast F fx.mkH fx.recTyH)
  (ConLeche.Frontend.occursConstFast mkName recTy)
#guard chkB (occursConstFast F fx.sH fx.sTyH)
  (ConLeche.Frontend.occursConstFast sName sTy)
#guard chkB (occursConstFast F fx.recH fx.recTyH)
  (ConLeche.Frontend.occursConstFast recName recTy)
#guard chkB (occursConstFast F fx.sH fx.ctorTyH)
  (ConLeche.Frontend.occursConstFast sName ctorTy)
-- both verdicts occur above
#guard ConLeche.Frontend.occursConstFast sName recTy == true
#guard ConLeche.Frontend.occursConstFast recName recTy == false

/-! ## `lamBody`, `stripPisAll`, `mkLams`, `instPisOpen`, `headIs` -/

#guard chkE (lamBody F fx.projVal0) (ConLeche.Frontend.lamBody (projVal 0))
#guard chkE (lamBody F fx.recTyH) (ConLeche.Frontend.lamBody recTy)

#guard chkStrip (stripPisAll F fx.recTyH) (ConLeche.Frontend.stripPisAll recTy)
#guard chkStrip (stripPisAll F fx.ctorTyH) (ConLeche.Frontend.stripPisAll ctorTy)
#guard chkStrip (stripPisAll F fx.sApp0) (ConLeche.Frontend.stripPisAll (sApp 0))

#guard chkE (do
    let p ← stripPisAll F fx.ctorTyH
    mkLams p.1 p.2)
  (ConLeche.Frontend.mkLams (ConLeche.Frontend.stripPisAll ctorTy).1
    (ConLeche.Frontend.stripPisAll ctorTy).2)

#guard chkOE (instPisOpen F fx.recTyH [fx.sApp0])
  (ConLeche.Frontend.instPisOpen recTy [sApp 0])
#guard chkOE (instPisOpen F fx.recTyH []) (ConLeche.Frontend.instPisOpen recTy [])
#guard chkOE (instPisOpen F fx.sApp0 [fx.sApp0])
  (ConLeche.Frontend.instPisOpen (sApp 0) [sApp 0])

#guard chkB (headIs F fx.sH fx.sApp0) (ConLeche.Frontend.headIs sName (sApp 0))
#guard chkB (headIs F fx.mkH fx.sApp0) (ConLeche.Frontend.headIs mkName (sApp 0))
#guard chkB (headIs F fx.sH fx.sTyH) (ConLeche.Frontend.headIs sName sTy)
#guard ConLeche.Frontend.headIs sName (sApp 0) == true

/-! ## `projRecValue` — the rewrite itself

Both fields, the shape that is not a projection, and a field index out of
range.  `buildBinders`, `mkProjMotive` and `mkProjMinor` have no con-leche
counterpart of their own (they are the two lambdas inside `projRecValue`), so
they are checked here, through it. -/

#guard chkOE (projRecValue F fx.owner fx.puH fx.projTyH fx.projVal0 0)
  (ConLeche.Frontend.projRecValue ownerP pu projTy (projVal 0) 0)
#guard chkOE (projRecValue F fx.owner fx.puH fx.projTyH fx.projVal1 1)
  (ConLeche.Frontend.projRecValue ownerP pu projTy (projVal 1) 1)
#guard chkOE (projRecValue F fx.owner fx.puH fx.projTyH fx.badValH 0)
  (ConLeche.Frontend.projRecValue ownerP pu projTy badVal 0)
#guard chkOE (projRecValue F fx.owner fx.puH fx.projTyH fx.projVal0 5)
  (ConLeche.Frontend.projRecValue ownerP pu projTy (projVal 0) 5)
#guard chkOE (projRecValue F fx.owner fx.puH fx.projTyH fx.recTyH 0)
  (ConLeche.Frontend.projRecValue ownerP pu projTy recTy 0)
-- the rewrite really fires on the first two, so the four checks above are not
-- four agreeing `none`s
#guard (ConLeche.Frontend.projRecValue ownerP pu projTy (projVal 0) 0).isSome
#guard (ConLeche.Frontend.projRecValue ownerP pu projTy (projVal 1) 1).isSome
#guard (ConLeche.Frontend.projRecValue ownerP pu projTy badVal 0).isNone

/-! ## `projRecOwners` — and with it the two delegated recognisers -/

#guard chkOwners (projRecOwners F fx.block fx.types fx.ctors fx.recs)
  (ConLeche.Frontend.projRecOwners blockP typesP ctorsP recsP)
#guard chkOwners (projRecOwners F fx.blockD fx.typesD fx.ctors fx.recs)
  (ConLeche.Frontend.projRecOwners blockD typesD ctorsP recsP)
-- the MUTUAL block is the one the rewrite serves and the DIRECT one is not,
-- so the delegated recognisers are exercised on both sides of their verdict
#guard (ConLeche.Frontend.projRecOwners blockP typesP ctorsP recsP).length == 1
#guard (ConLeche.Frontend.projRecOwners blockD typesD ctorsP recsP).length == 0

end ConRon.Arena.ProjRecTest
