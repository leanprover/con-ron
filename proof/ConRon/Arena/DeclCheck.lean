/-
# `ConRon.Arena.DeclCheck` — the declaration-level checks, over handles

The twin of `ConLeche/Kernel/DeclCheck.lean` and of the declaration-level
halves of `ConLeche/Kernel/Checker.lean`, `StdAxioms.lean` and
`TrustAxioms.lean`.

## One twin per PAIR

con-leche carries each of these functions twice — once reading the linear
environment (`Checker.lean`, `StdAxioms.lean`, `TrustAxioms.lean`) and once
the index (`DeclCheck.lean`'s `…F` mirrors, which is what both binaries run).
The arena has ONE environment type, the index (`Arena/Core.lean`'s deviation
1), so each pair collapses into one twin carrying a `con-leche:` line per
collapsed declaration, and the twin keeps the UNSUFFIXED name — as
`Arena/Core.lean`'s thirteen collapsed pairs do.

## No closures

* `divModCertStmts`' eleven local lambdas (`ble2`, `eqB`, `eqN`, `op2`, …) are
  named `def`s here, as `Arena/Core.lean`'s `natOpEquations` does with its
  three.  DESIGN §3.4 forbids a function value in code Aeneas must translate,
  and over handles each of them has to intern anyway.
* `divModCertsGuard`'s `(… .zip …).all (fun p => …)` is an explicit
  two-list recursion.

## What is P2d-2's

The modeled and native inductive installs (`ConLeche/Kernel/Inductives/*`)
are the other half of this phase.  Eight of `DeclCheck.lean`'s declarations
are theirs, because they call into those modules and nothing here does:
`ctorResidualOkF` (needs `StructParts.structFam`), `checkIotaThmF`,
`nestedRuleShapeF`, `checkIotaThmNF`, `checkIotaRuleF`, `checkIotaRulesF`
(need `Modeled.checkIotaSidesTy`), `checkProjTyF` and `checkProjIotaF` (need
`Modeled.projFwd`/`projBack`).  Everything else `DeclCheck.lean` declares is
here.
-/
import ConRon.Arena.CheckerSplit

namespace ConRon.Arena

open ConLeche

/-! ## The standard axioms' environment shape -/

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
Is this checked axiom one of the two recognized standard axioms, over
standardly-shaped stored `Iff` / `Nonempty` families (and the pinned `Eq`
basis)?  All three of each family's constants are pinned, not just the type,
because the verification has to REALIZE the axiom and nothing turns an
inhabitant of an opaque family into its fields except that family's own
recursor. -/
def stdAxiomOk (fe : IFEnv) (cvA : IConstantVal) : AM Bool := do
  let pn ← propextName
  let cn ← choiceName
  if cvA.name == pn then do
    let en ← pinEq
    let ea ← eqA
    if fe.find? en != some ea then pure false else do
      match fe.find? (← iffName) with
      | some (.indInfo cvI _) => do
        if !(← cvI.matchesPin (← (← iffA).toConstantVal)) then pure false else do
          match fe.find? (← iffIntroName) with
          | some (.ctorInfo cvIi 2 2) => do
            if !(← cvIi.matchesPin (← (← iffIntroA).toConstantVal)) then pure false
            else do
              match fe.find? (← iffRecName) with
              | some (.recInfo cvIr 4 4 _) => do
                if !(← cvIr.matchesPin (← (← iffRecA).toConstantVal)) then pure false
                else cvA.matchesPin (← propextA)
              | _ => pure false
          | _ => pure false
      | _ => pure false
  else if cvA.name == cn then do
    match fe.find? (← nonemptyName) with
    | some (.indInfo cvN _) => do
      if !(← cvN.matchesPin (← (← nonemptyA).toConstantVal)) then pure false else do
        match fe.find? (← nonemptyIntroName) with
        | some (.ctorInfo cvNi 1 1) => do
          if !(← cvNi.matchesPin (← (← nonemptyIntroA).toConstantVal)) then pure false
          else do
            match fe.find? (← nonemptyRecName) with
            | some (.recInfo cvNr 3 3 _) => do
              if !(← cvNr.matchesPin (← (← nonemptyRecA).toConstantVal)) then pure false
              else cvA.matchesPin (← choiceA)
            | _ => pure false
        | _ => pure false
    | _ => pure false
  else pure false

/-! ## The compiler-trust family's environment shape -/

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:158-169 trustCompilerOk
con-leche: ConLeche/Kernel/DeclCheck.lean:272-280 trustCompilerOkF
Is `Lean.trustCompiler` installable here?  The `True` family must be stored
with the pinned shapes, and the checked axiom's type must match the pin. -/
def trustCompilerOk (fe : IFEnv) (cvA : IConstantVal) : AM Bool := do
  match fe.find? (← trueName) with
  | some (.indInfo cvT _) => do
    if !(← cvT.matchesPin (← trueCvA)) then pure false else do
      match fe.find? (← trueIntroName) with
      | some (.ctorInfo cvTi 0 0) => do
        if !(← cvTi.matchesPin (← trueIntroCvA)) then pure false
        else cvA.matchesPin (← trustCompilerA)
      | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:171-177 reduceStoredOk
con-leche: ConLeche/Kernel/DeclCheck.lean:282-286 reduceStoredOkF
Is the reduce operation `c` stored as a checked opaque (`axiomInfo`, the
storage kind of every checked `opaque`) of the pinned type? -/
def reduceStoredOk (fe : IFEnv) (c : NIdx) : AM Bool := do
  match fe.find? c with
  | some (.axiomInfo cvR) => cvR.matchesPin (← reduceOpCvA c)
  | _ => pure false

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:179-186 reduceElemOk
con-leche: ConLeche/Kernel/DeclCheck.lean:288-294 reduceElemOkF
The element-inductive shape an `ofReduce*` axiom needs: the pinned `Nat` basis
resp. a standardly-shaped stored `Bool`. -/
def reduceElemOk (fe : IFEnv) (c : NIdx) : AM Bool := do
  let rn ← reduceNatName
  if c == rn then do
    let nn ← pinNat
    pure (fe.find? nn == some (← natA))
  else
    match fe.find? (← boolName) with
    | some (.indInfo cvB _) => cvB.matchesPin (← boolCvA)
    | _ => pure false

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:188-198 ofReduceAxOk
con-leche: ConLeche/Kernel/DeclCheck.lean:296-302 ofReduceAxOkF
Is this checked axiom a pinned `ofReduce*` over a standardly-shaped
environment? -/
def ofReduceAxOk (fe : IFEnv) (cvA : IConstantVal) : AM Bool := do
  let c ← ofReduceOp cvA.name
  let en ← pinEq
  if fe.find? en != some (← eqA) then pure false
  else if !(← reduceElemOk fe c) then pure false
  else if !(← reduceStoredOk fe c) then pure false
  else cvA.matchesPin (← ofReducePinA cvA.name)

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:209-213 reducePinGuard
con-leche: ConLeche/Kernel/DeclCheck.lean:304-308 reducePinGuardF
Syntactic guards on the generated reduce pin (checked once at install). -/
def reducePinGuard (fe : IFEnv) (c : NIdx) : AM Bool := do
  let p ← reduceDeclPin c
  if !(← looseBVarsBoundedFast coreWalkFuel 0 p) then pure false
  else if ← hasFvarFast coreWalkFuel p then pure false
  else if !(← allLevelParamsDefined [] p) then pure false
  else constsResolveFFast fe p

/-- con-leche: none — `(natOpDeps c).all (natOpStoredOk fe)`, as an explicit
list recursion (DESIGN §3.4 forbids the closure `List.all` takes).  con-leche's
`natOpGuard` has the WEAKER dependency test (`Arena/Core.lean`'s
`natOpDepsStored`: stored as a level-monomorphic definition); this is the
stronger one `divModEnvGuard` asks for, which pins the type too. -/
def natOpStoredOkAll (fe : IFEnv) : List NIdx → AM Bool
  | [] => pure true
  | n :: ns => do
    if ← natOpStoredOk fe n then natOpStoredOkAll fe ns else pure false

/-! `lps.map .param` as an interned universe-argument list — the spelling of
"the constant at its own level parameters", which every model statement below
is written with — is `Arena/Inductives/StructParts.lean`'s `paramLevels`
(P2d-2's half of this phase, which needs the same spelling for the block's
own types).  One twin, in the module that sits lower. -/

/-! ## The `Nat.div`/`Nat.mod` pin variants

`Arena/NatOpPinSet.lean` holds the record; these are the checks that read
it. -/

/-- con-leche: ConLeche/Kernel/Checker.lean:118-130 divModDeclPin — the pinned
defining expression of a pin-certified WF-recursive op in one pin variant.
con-leche's `c = natDivName` chain is a handle comparison here. -/
def divModDeclPin (ps : INatOpPinSet) (c : NIdx) : AM EIdx := do
  if c == (← natDivName) then pure ps.divPin
  else if c == (← natGcdName) then pure ps.gcdPin
  else if c == (← natLandName) then pure ps.landPin
  else if c == (← natLorName) then pure ps.lorPin
  else if c == (← natXorName) then pure ps.xorPin
  else if c == (← natShiftLeftName) then pure ps.shiftLeftPin
  else if c == (← natShiftRightName) then pure ps.shiftRightPin
  else pure ps.modPin

/-- con-leche: ConLeche/Kernel/Checker.lean:132-142 divModCertProofs — the
certificate proof terms of a pin-certified WF-recursive op in one pin
variant, one per statement of `divModCertStmts`. -/
def divModCertProofs (ps : INatOpPinSet) (c : NIdx) : AM (List EIdx) := do
  if c == (← natDivName) then pure ps.divProofs
  else if c == (← natGcdName) then pure ps.gcdProofs
  else if c == (← natLandName) then pure ps.landProofs
  else if c == (← natLorName) then pure ps.lorProofs
  else if c == (← natXorName) then pure ps.xorProofs
  else if c == (← natShiftLeftName) then pure ps.shiftLeftProofs
  else if c == (← natShiftRightName) then pure ps.shiftRightProofs
  else pure ps.modProofs

/-! ### The pinned characterization statements

con-leche writes `divModCertStmts` with eleven local lambdas over `Expr`
constructors.  Over handles every one of them interns, and DESIGN §3.4
forbids the function values, so each is a `def` — the treatment
`Arena/Core.lean` gives `natOpEquations`' three. -/

/-- con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts — the
statements' `Eq.{1} τ a b` former. -/
def eqAt1 (ty a b : EIdx) : AM EIdx := do
  let z ← zeroLevel
  let one ← internLNode (.succ z)
  let us ← internLsNode [one]
  let en ← pinEq
  let e ← internE (.const en us)
  let e1 ← internE (.app e ty)
  let e2 ← internE (.app e1 a)
  internE (.app e2 b)

/-- con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts — the
numeral `1` as `Nat.succ Nat.zero`. -/
def natOne : AM EIdx := do
  let s ← pinNatSucc
  let z ← pinNatZero
  natAp1 s (← constE z)

/-- con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts — the
open statements' variables `x := fvar 0`, `y := fvar 1` at `Nat`. -/
def natVar (i : Nat) : AM EIdx := do
  let nt ← pinNat
  internE (.fvar i (← constE nt))

/-- con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts — **the
pinned characterization statements** of a pin-certified WF-recursive op, in
*open* form over `x := fvar 0`, `y := fvar 1` (the hypotheses become
`fvar 2, fvar 3`): per certificate, the list of hypothesis types and the
characteristic equation `Eq Nat lhs rhs`.  The guards are spelled with the
already-certified `Nat.ble` and the numeral `1` as `Nat.succ Nat.zero`. -/
def divModCertStmts (c : NIdx) : AM (List (List EIdx × EIdx)) := do
  let nt ← pinNat
  let natTy ← constE nt
  let x ← natVar 0
  let y ← natVar 1
  let one ← natOne
  let bleN ← natBleName
  let bn ← boolName
  let boolTy ← constE bn
  let bT ← constE (← boolTrueName)
  let bF ← constE (← boolFalseName)
  let z ← constE (← pinNatZero)
  let two ← natAp1 (← pinNatSucc) one
  let modN ← natModName
  let divN ← natDivName
  let addN ← natAddName
  let mulN ← natMulName
  let subN ← natSubName
  let gcdN ← natGcdName
  let slN ← natShiftLeftName
  let srN ← natShiftRightName
  let landN ← natLandName
  let lorN ← natLorName
  let xorN ← natXorName
  if c == gcdN then do
    -- `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`
    let h1 ← eqAt1 boolTy (← natAp2 bleN one x) bT
    let h2 ← eqAt1 boolTy (← natAp2 bleN one x) bF
    let e1 ← eqAt1 natTy (← natAp2 c x y)
      (← natAp2 c (← natAp2 modN y x) x)
    let e2 ← eqAt1 natTy (← natAp2 c x y) y
    pure [([h1], e1), ([h2], e2)]
  else if c == slN then do
    -- `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`
    let h1 ← eqAt1 boolTy (← natAp2 bleN one y) bT
    let h2 ← eqAt1 boolTy (← natAp2 bleN one y) bF
    let e1 ← eqAt1 natTy (← natAp2 c x y)
      (← natAp2 c (← natAp2 mulN two x) (← natAp2 subN y one))
    let e2 ← eqAt1 natTy (← natAp2 c x y) x
    pure [([h1], e1), ([h2], e2)]
  else if c == srN then do
    -- `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`, `y = 0 → x >>> y = x`
    let h1 ← eqAt1 boolTy (← natAp2 bleN one y) bT
    let h2 ← eqAt1 boolTy (← natAp2 bleN one y) bF
    let e1 ← eqAt1 natTy (← natAp2 c x y)
      (← natAp2 divN (← natAp2 c x (← natAp2 subN y one)) two)
    let e2 ← eqAt1 natTy (← natAp2 c x y) x
    pure [([h1], e1), ([h2], e2)]
  else if c == landN then do
    -- `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`, `x = 0 → … = 0`
    let h1 ← eqAt1 boolTy (← natAp2 bleN one x) bT
    let h2 ← eqAt1 boolTy (← natAp2 bleN one x) bF
    let rec1 ← natAp2 c (← natAp2 divN x two) (← natAp2 divN y two)
    let e1 ← eqAt1 natTy (← natAp2 c x y)
      (← natAp2 addN (← natAp2 mulN two rec1)
        (← natAp2 mulN (← natAp2 modN x two) (← natAp2 modN y two)))
    let e2 ← eqAt1 natTy (← natAp2 c x y) z
    pure [([h1], e1), ([h2], e2)]
  else if c == lorN then do
    -- `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`
    let h1 ← eqAt1 boolTy (← natAp2 bleN one x) bT
    let h2 ← eqAt1 boolTy (← natAp2 bleN one x) bF
    let rec1 ← natAp2 c (← natAp2 divN x two) (← natAp2 divN y two)
    let mx ← natAp2 modN x two
    let my ← natAp2 modN y two
    let e1 ← eqAt1 natTy (← natAp2 c x y)
      (← natAp2 addN (← natAp2 mulN two rec1)
        (← natAp2 subN (← natAp2 addN mx my) (← natAp2 mulN mx my)))
    let e2 ← eqAt1 natTy (← natAp2 c x y) y
    pure [([h1], e1), ([h2], e2)]
  else if c == xorN then do
    -- `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`
    let h1 ← eqAt1 boolTy (← natAp2 bleN one x) bT
    let h2 ← eqAt1 boolTy (← natAp2 bleN one x) bF
    let rec1 ← natAp2 c (← natAp2 divN x two) (← natAp2 divN y two)
    let mx ← natAp2 modN x two
    let my ← natAp2 modN y two
    let e1 ← eqAt1 natTy (← natAp2 c x y)
      (← natAp2 addN (← natAp2 mulN two rec1)
        (← natAp2 modN (← natAp2 addN mx my) two))
    let e2 ← eqAt1 natTy (← natAp2 c x y) y
    pure [([h1], e1), ([h2], e2)]
  else do
    let recRhs ←
      if c == divN then natAp1 (← pinNatSucc) (← natAp2 c (← natAp2 subN x y) y)
      else natAp2 c (← natAp2 subN x y) y
    let baseRhs ← if c == divN then pure z else pure x
    let h1 ← eqAt1 boolTy (← natAp2 bleN y x) bT
    let h2 ← eqAt1 boolTy (← natAp2 bleN one y) bT
    let h3 ← eqAt1 boolTy (← natAp2 bleN y x) bF
    let h4 ← eqAt1 boolTy (← natAp2 bleN one y) bF
    let e1 ← eqAt1 natTy (← natAp2 c x y) recRhs
    let e2 ← eqAt1 natTy (← natAp2 c x y) baseRhs
    pure [([h1, h2], e1), ([h3], e2), ([h4], e2)]

/-- con-leche: ConLeche/Kernel/Checker.lean:224-237 divModCertApplied — the
vendored proof applied to the statement's free variables (`x`, `y`, then one
`fvar` per hypothesis, carrying the hypothesis *type* as its annotation — the
checker's implicit local context). -/
def divModCertApplied (proofS : EIdx) (hyps : List EIdx) : AM EIdx := do
  let x ← natVar 0
  let y ← natVar 1
  let b1 ← internE (.app proofS x)
  let base ← internE (.app b1 y)
  match hyps with
  | [h1] => do
    let f2 ← internE (.fvar 2 h1)
    internE (.app base f2)
  | [h1, h2] => do
    let f2 ← internE (.fvar 2 h1)
    let a1 ← internE (.app base f2)
    let f3 ← internE (.fvar 3 h2)
    internE (.app a1 f3)
  | _ => pure base

/-- con-leche: none — `hyps.map (Expr.substConst0 c annVal)`, as an explicit
list recursion (DESIGN §3.4 forbids the closure). -/
def substConst0List (n : NIdx) (r : EIdx) : List EIdx → AM (List EIdx)
  | [] => pure []
  | h :: hs => do
    let h' ← substConst0 n r coreWalkFuel h
    let hs' ← substConst0List n r hs
    pure (h' :: hs')

/-- con-leche: none — `(hyps.map …).all (fun h => h.constsResolveF fe)`, as an
explicit list recursion. -/
def constsResolveAll (fe : IFEnv) : List EIdx → AM Bool
  | [] => pure true
  | h :: hs => do
    if ← constsResolveFFast fe h then constsResolveAll fe hs else pure false

/-- con-leche: ConLeche/Kernel/Checker.lean:239-250 divModCertGuard
con-leche: ConLeche/Kernel/DeclCheck.lean:321-330 divModCertGuardF
The syntactic guards of one certificate check: the substituted proof is
closed, level-monomorphic and resolving, and the substituted statement
components resolve. -/
def divModCertGuard (fe : IFEnv) (c : NIdx) (annVal : EIdx)
    (hyps : List EIdx) (eqE proof : EIdx) : AM Bool := do
  let p ← substConstAll c annVal coreWalkFuel proof
  if !(← looseBVarsBoundedFast coreWalkFuel 0 p) then pure false
  else if ← hasFvarFast coreWalkFuel p then pure false
  else if !(← allLevelParamsDefined [] p) then pure false
  else if !(← constsResolveFFast fe p) then pure false
  else if !(← constsResolveAll fe (← substConst0List c annVal hyps)) then
    pure false
  else constsResolveFFast fe (← substConst0 c annVal coreWalkFuel eqE)

/-- con-leche: ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard
con-leche: ConLeche/Kernel/DeclCheck.lean:310-319 divModEnvGuardF
Environment prerequisites of a certified `Nat.div`/`Nat.mod`: dependency
guard, pinned dependencies, the pinned `Eq` basis, and the `Bool` constructors
stored at the type `Bool` itself. -/
def divModEnvGuard (fe2 : IFEnv) (c : NIdx) : AM Bool := do
  if !(← natOpGuard fe2 c) then pure false else do
    let deps ← natOpDeps c
    if !(← natOpStoredOkAll fe2 deps) then pure false else do
      let en ← pinEq
      if fe2.find? en != some (← eqA) then pure false else do
        let bn ← boolName
        let boolTy ← constE bn
        match fe2.find? (← boolTrueName) with
        | some ci => do
          if (← ci.toConstantVal).type != boolTy then pure false else do
            match fe2.find? (← boolFalseName) with
            | some ci' => pure ((← ci'.toConstantVal).type == boolTy)
            | none => pure false
        | none => pure false

/-- con-leche: ConLeche/Kernel/Checker.lean:292-297 divModPinGuard
con-leche: ConLeche/Kernel/DeclCheck.lean:332-336 divModPinGuardF
Syntactic guards on one variant's pin (generated; checked once at install
rather than proven about the blob). -/
def divModPinGuard (ps : INatOpPinSet) (fe : IFEnv) (c : NIdx) : AM Bool := do
  let p ← divModDeclPin ps c
  if !(← looseBVarsBoundedFast coreWalkFuel 0 p) then pure false
  else if ← hasFvarFast coreWalkFuel p then pure false
  else if !(← allLevelParamsDefined [] p) then pure false
  else constsResolveFFast fe p

/-- con-leche: ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard
con-leche: ConLeche/Kernel/DeclCheck.lean:338-342 divModCertsGuardF
All of one variant's certificates' syntactic guards at once, `zip`ped with
the statements.  Checked *before* the pin comparison; a failure moves on to
the next variant. -/
def divModCertsGuardGo (fe : IFEnv) (c : NIdx) (annVal : EIdx) :
    List (List EIdx × EIdx) → List EIdx → AM Bool
  | [], _ => pure true
  | _, [] => pure true
  | (hyps, eqE) :: srest, proof :: prest => do
    if ← divModCertGuard fe c annVal hyps eqE proof then
      divModCertsGuardGo fe c annVal srest prest
    else pure false

/-- con-leche: ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard
con-leche: ConLeche/Kernel/DeclCheck.lean:338-342 divModCertsGuardF
`List.zip` truncates at the shorter list, which is why the helper's two
`[]` clauses are both `true`. -/
def divModCertsGuard (ps : INatOpPinSet) (fe : IFEnv) (c : NIdx)
    (annVal : EIdx) : AM Bool := do
  divModCertsGuardGo fe c annVal (← divModCertStmts c) (← divModCertProofs ps c)

/-- con-leche: ConLeche/Kernel/Checker.lean:252-275 checkDivModCerts
con-leche: ConLeche/Kernel/DeclCheck.lean:861-875 checkDivModCertsF
Check the pinned certificates of op `c`: per certificate, the vendored proof
(with the op's self-references replaced by the stored annotated value — the
checks run in the *pre-insertion* environment) is applied to free variables
typed by the pinned open statement, its type inferred, and compared against
the pinned characteristic equation. -/
def checkDivModCerts (mode : CheckMode) (fe : IFEnv) (c : NIdx)
    (annVal : EIdx) : List (List EIdx × EIdx) → List EIdx → AM Bool
  | [], [] => pure true
  | (hyps, eqE) :: srest, proof :: prest => do
    if ← divModCertGuard fe c annVal hyps eqE proof then do
      let p ← substConstAll c annVal coreWalkFuel proof
      let hs ← substConst0List c annVal hyps
      let appliedA ← annotateCore mode fe checkFuel 4 (← divModCertApplied p hs)
      let tp ← inferTypeCore mode fe checkFuel 4 appliedA
      let rhs ← substConst0 c annVal coreWalkFuel eqE
      if ← isDefEqCore mode fe checkFuel 4 tp rhs then
        checkDivModCerts mode fe c annVal srest prest
      else pure false
    else pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Checker.lean:308-328 checkDivModPinAt
con-leche: ConLeche/Kernel/DeclCheck.lean:877-885 checkDivModPinAtF
**One pin variant's attempt**: the stored value against the variant's pin by
definitional equality, and on a match the variant's certificates.  `true` =
matched; `false` = the pin is not definitionally equal, or a certificate did
not check.  The third outcome is an error thrown from inside, which
`orElseAttempt` turns into "this variant does not match". -/
def checkDivModPinAt (mode : CheckMode) (fe : IFEnv) (c : NIdx)
    (value' : EIdx) (ps : INatOpPinSet) : AM Bool := do
  let pinA ← annotateCore mode fe checkFuel 0 (← divModDeclPin ps c)
  let okPin ← isDefEqCore mode fe checkFuel 0 value' pinA
  if okPin then
    checkDivModCerts mode fe c value' (← divModCertStmts c)
      (← divModCertProofs ps c)
  else pure false

/-- con-leche: ConLeche/Kernel/Checker.lean:330-336 divModAttemptReason — what
a variant failed on, for the decline message.  con-leche's pure
instantiations always report the `none` text; the arena's `orElseAttempt`
delivers the error, as the executable's `sharedOpsC` does. -/
def divModAttemptReason (ps : INatOpPinSet) : Option CheckError → String
  | none => s!"{ps.toolchain}: pin not definitionally equal, or a \
      certificate failed"
  | some e => s!"{ps.toolchain}: {reprStr e}"

/-- con-leche: ConLeche/Kernel/Checker.lean:338-360 checkDivModPinLoop
con-leche: ConLeche/Kernel/DeclCheck.lean:887-901 checkDivModPinLoopF
**The variant loop**: the first variant whose guards pass and whose attempt
succeeds enables the fast path; every other outcome moves on to the next
variant, and when none is left the stream DECLINES with the per-variant
reasons.

This is (B)'s one variant-fallback point.  con-leche's `ops.orElse … fun r =>
…` passes a continuation, which DESIGN §3.4 forbids; the continuation is this
loop's own tail call, exactly as `crates/con-ron-core/src/kernel/checker.rs`
spells it, and the decision is `orElseAttempt`'s four-way step — `.recovered`
resumes at the PRE-attempt state, `.failed` (a `native` error only) is the
verdict. -/
def checkDivModPinLoop (mode : CheckMode) (fe : IFEnv) (c : NIdx)
    (value' : EIdx) : List INatOpPinSet → List String → AM Unit
  | [], tried => do
    let cn ← readName c
    fail (.notImplemented s!"unsupported Nat.div/mod spelling ({cn}: \
      no pin variant matched — {String.intercalate "; " tried})")
  | ps :: rest, tried => do
    if (← divModPinGuard ps fe c) && (← divModCertsGuard ps fe c value') then
      match ← orElseAttempt (checkDivModPinAt mode fe c value' ps) with
      | .matched => pure ()
      | .continued =>
        checkDivModPinLoop mode fe c value' rest
          (tried ++ [divModAttemptReason ps none])
      | .recovered e =>
        checkDivModPinLoop mode fe c value' rest
          (tried ++ [divModAttemptReason ps (some e)])
      | .failed e => fail e
    else
      checkDivModPinLoop mode fe c value' rest
        (tried ++ [s!"{ps.toolchain}: pin or certificate ground constants \
          absent"])

/-- con-leche: ConLeche/Kernel/Checker.lean:362-388 checkDivModPin
con-leche: ConLeche/Kernel/DeclCheck.lean:903-913 checkDivModPinF
The pin-certified operations' install gate, run after the ordinary definition
check (`fe2` is the already-extended environment, `fe` the pre-insertion one
all checks run in).  The variant list is its parameter (con-leche's task
#304). -/
def checkDivModPin (mode : CheckMode) (pins : List INatOpPinSet)
    (fe fe2 : IFEnv) (c : NIdx) : AM Unit := do
  if ← divModEnvGuard fe2 c then
    match fe2.find? c with
    | some (.defnInfo _ value' _) =>
      checkDivModPinLoop mode fe c value' pins []
    | _ => fail (.internal s!"Nat.div/mod operation not stored ({← readName c})")
  else fail (.notImplemented
    s!"unsupported Nat.div/mod environment ({← readName c})")

/-- con-leche: ConLeche/Kernel/Checker.lean:390-425 checkReducePin
con-leche: ConLeche/Kernel/DeclCheck.lean:915-934 checkReducePinF
The `Lean.reduceNat`/`Lean.reduceBool` install gate, run after the ordinary
opaque check: the stored constant carries the pinned type, the witness value
is definitionally equal to the build-time pin, and the *identity certificate*
`value x ≡ x` over an opened `fvar` at the element type holds. -/
def checkReducePin (mode : CheckMode) (fe fe2 : IFEnv) (c : NIdx)
    (value : EIdx) : AM Unit := do
  if (← reduceStoredOk fe2 c) && (← reduceElemOk fe c) then
    if ← reducePinGuard fe c then do
      let valA ← annotateCore mode fe checkFuel 0 value
      let pinA ← annotateCore mode fe checkFuel 0 (← reduceDeclPin c)
      let okPin ← isDefEqCore mode fe checkFuel 0 valA pinA
      if okPin then do
        let x ← reduceCertVar c
        let ax ← internE (.app valA x)
        let ok ← isDefEqCore mode fe checkFuel 1 ax x
        if ok then pure ()
        else fail (.internal
          s!"pinned compiler-trust opaque is not the identity ({← readName c})")
      else fail (.notImplemented
        s!"unsupported compiler-trust opaque spelling ({← readName c})")
    else fail (.notImplemented
      s!"unsupported compiler-trust opaque spelling ({← readName c}: pin ground constants absent)")
  else fail (.notImplemented
    s!"unsupported compiler-trust opaque declaration ({← readName c})")

/-! ## The structural-`Nat` recurrence certification -/

/-- con-leche: ConLeche/Kernel/Checker.lean:108-116 certifyNatEqs — certify a
list of recurrence equations by definitional equality (at depth 2: the
equations' variables are `fvar 0`/`fvar 1`). -/
def certifyNatEqs (mode : CheckMode) (fe : IFEnv) :
    List (EIdx × EIdx) → AM Bool
  | [] => pure true
  | eq :: rest => do
    if ← isDefEqCore mode fe checkFuel 2 eq.1 eq.2 then
      certifyNatEqs mode fe rest
    else pure false

/-- con-leche: none — `(natOpEquations 0 c).map fun eq => (substConst0 c v
eq.1, substConst0 c v eq.2)`, as an explicit list recursion. -/
def substConst0Pairs (n : NIdx) (r : EIdx) : List (EIdx × EIdx) → AM (List (EIdx × EIdx))
  | [] => pure []
  | (a, b) :: rest => do
    let a' ← substConst0 n r coreWalkFuel a
    let b' ← substConst0 n r coreWalkFuel b
    let rest' ← substConst0Pairs n r rest
    pure ((a', b') :: rest')

/-! ## The three value kinds' full checks -/

/-- con-leche: ConLeche/Kernel/Checker.lean:32-50 checkDefnVal
con-leche: ConLeche/Kernel/DeclCheck.lean:838-853 checkDefnValF
Check a `def` declaration's value against its checked constant, returning the
pushed index.  The reducibility hint is stored untouched: it steers only the
lazy delta unfolding order, never a verdict. -/
def checkDefnVal (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) (hint : ReducibilityHint) : AM IFEnv := do
  let value ← installValue mode fe cv value
  let vtype ← inferTypeCore mode fe checkFuel 0 value
  unless ← isDefEqCore mode fe checkFuel 0 vtype cv.type do
    fail (.invalid s!"type mismatch in definition {← readName cv.name}")
  pure (fe.push (.defnInfo cv value hint))

/-- con-leche: ConLeche/Kernel/Checker.lean:52-82 checkThmVal — check a
`theorem` declaration's value against its checked constant (whose type must
additionally be a proposition).  **A theorem is stored by its statement**: the
constant keeps the record's own (raw) value as an unread datum, and the
annotated value is a realizability witness, checked and then discarded. -/
def checkThmVal (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) : AM IFEnv := do
  let stype ← inferTypeCore mode fe checkFuel 0 cv.type
  let u ← ensureSortCore mode fe checkFuel 0 stype
  let z ← zeroLevel
  unless ← liftFueled "level comparison" (← lvlEq? u z) do
    fail (.invalid s!"type of theorem {← readName cv.name} is not a proposition")
  let jv ← installValue mode fe cv value
  let vtype ← inferTypeCore mode fe checkFuel 0 jv
  unless ← isDefEqCore mode fe checkFuel 0 vtype cv.type do
    fail (.invalid s!"type mismatch in theorem {← readName cv.name}")
  pure (fe.push (.thmInfo cv value))

/-- con-leche: ConLeche/Kernel/Checker.lean:84-107 checkOpaqueVal — check an
`opaque` declaration's value against its checked constant: exactly the theorem
check without the is-a-proposition requirement.  The result is stored as an
`axiomInfo` — the checked value is a realizability witness, consumed by the
model extension and then discarded. -/
def checkOpaqueVal (mode : CheckMode) (fe : IFEnv) (cv : IConstantVal)
    (value : EIdx) : AM IFEnv := do
  let value ← installValue mode fe cv value
  let vtype ← inferTypeCore mode fe checkFuel 0 value
  unless ← isDefEqCore mode fe checkFuel 0 vtype cv.type do
    fail (.invalid s!"type mismatch in opaque {← readName cv.name}")
  pure (fe.push (.axiomInfo cv))

/-- con-leche: ConLeche/Kernel/Checker.lean:26-30 installBasisDecl
con-leche: ConLeche/Kernel/DeclCheck.lean:855-859 installBasisDeclF
Install one pinned basis declaration (duplicate-checked), returning the
pushed index. -/
def installBasisDecl (fe : IFEnv) (ci : IConstantInfo) : AM IFEnv := do
  unless (fe.find? ci.name).isNone do
    fail (.invalid s!"duplicate declaration {← readName ci.name}")
  pure (fe.push ci)

/-- con-leche: none — `kind.declsA.foldlM installBasisDecl`, as an explicit
list recursion (DESIGN §3.4). -/
def installBasisDecls (fe : IFEnv) : List IConstantInfo → AM IFEnv
  | [] => pure fe
  | ci :: cs => do installBasisDecls (← installBasisDecl fe ci) cs

/-! ## The modeled install's environment reads

`checkEtaThm`, `checkUnitThm`, `indBlockCaps`, `checkMemberVal` and
`checkProjLookups` — the five `DeclCheck.lean` declarations that read the
model companions a generated block leaves in the environment — are
`Arena/Inductives/Modeled.lean`'s (P2d-2's half of this phase).  They call
nothing this module has and everything they are called from is there, so
they live with their callers and there is ONE twin of each. -/

end ConRon.Arena
