/-
# The `ExprOps` twins, differentially (task #97 P2b)

**The module-level differential check.**  For every twin that has a
con-leche counterpart on `Expr`, one `#guard`:

> intern a term, run the twin, read the result back with `denoteE`, and
> compare with con-leche's own `ExprOps` function applied to the
> *denotation of the input*.

Nothing here is a proof and nothing here is an `#eval` print: every check is
kernel-reduced, so a wrong answer is a build failure.  It is the cheapest
guard against the class of bug the bridge cannot see before P3 lands — an arm
that rebuilds the wrong node, a cursor that is bumped in the wrong place, a
cutoff that fires when it should not.

The expected side is computed, not written out: `E h` is the *denotation* of
a fixture handle, so `chkE (twin …) (Expr.f (E h) …)` is literally "the twin
agrees with con-leche on this term".  What IS written out by hand is the
fixture's denotation (§"The fixture denotes what it should"), which is what
makes the computed expectations trustworthy.

DESIGN.md §8.4's "correctness before proofs": (B) must agree with con-leche
before a bridge lemma is written.  This is that check at module scope; the
whole-checker one is P2f's `scripts/diff-e2e.sh --bin=`.
-/
import ConRon.Arena.ExprOps
import ConLeche.Kernel.ExprOps

namespace ConRon.Arena

open ConLeche

/-! ## The fixture -/

/-- con-leche: none — the handles this module's checks name, in one record so
that the fixture is built by one `let` chain in the order a parser would. -/
private structure Fx where
  st : EStore
  z : LIdx
  one : LIdx
  pu : LIdx
  anon : NIdx
  foo : NIdx
  bar : NIdx
  uN : NIdx
  usZ : LsIdx
  usU : LsIdx
  s0 : EIdx
  s1 : EIdx
  su : EIdx
  cf : EIdx
  cb : EIdx
  b0 : EIdx
  b1 : EIdx
  b2 : EIdx
  lit7 : EIdx
  fv0 : EIdx
  fv1 : EIdx
  ap1 : EIdx
  pj : EIdx
  lamT : EIdx
  allT : EIdx
  letT : EIdx
  big : EIdx
  piT : EIdx
  piS : EIdx
  lamT2 : EIdx
  spine : EIdx

/-- con-leche: none — the fixture: two sorts, a parameter sort, two
constants, three loose `bvar`s, two `fvar`s with annotations, a literal, and
the composite terms the checks below walk (a λ over a `let` over a `∀` over a
`proj` over a spine; a two-binder `∀`-telescope and its λ twin; an
application spine). -/
private def fx : Fx :=
  let st := EStore.empty
  let (st, z) := st.internLevel .zero
  let (st, one) := st.internLevel (.succ z)
  let (st, anon) := st.internName .anonymous
  let (st, foo) := st.internName (.str anon "foo")
  let (st, bar) := st.internName (.str anon "bar")
  let (st, uN) := st.internName (.str anon "u")
  let (st, pu) := st.internLevel (.param uN)
  let (st, usZ) := st.internLevels [z]
  let (st, usU) := st.internLevels [pu]
  let (st, s0) := st.intern (.sort z)
  let (st, s1) := st.intern (.sort one)
  let (st, su) := st.intern (.sort pu)
  let (st, cf) := st.intern (.const foo usZ)
  let (st, cb) := st.intern (.const bar usU)
  let (st, b0) := st.intern (.bvar 0)
  let (st, b1) := st.intern (.bvar 1)
  let (st, b2) := st.intern (.bvar 2)
  let (st, lit7) := st.intern (.lit (.natVal 7))
  let (st, fv0) := st.intern (.fvar 0 s0)
  let (st, fv1) := st.intern (.fvar 1 s1)
  let (st, ap1) := st.intern (.app cf b0)
  let (st, pj) := st.intern (.proj foo 0 ap1)
  let (st, lamT) := st.intern (.lam s0 ap1 ⟨.never⟩)
  let (st, apbf) := st.intern (.app b1 fv0)
  let (st, allT) := st.intern (.forallE s0 apbf ⟨.never⟩)
  let (st, apbb) := st.intern (.app b0 b1)
  let (st, letT) := st.intern (.letE s0 cf apbb)
  let (st, apcb) := st.intern (.app cb b0)
  let (st, apfv) := st.intern (.app fv1 b0)
  let (st, apb2) := st.intern (.app b2 apfv)
  let (st, pj2) := st.intern (.proj foo 0 apb2)
  let (st, inner) := st.intern (.forallE s1 pj2 ⟨.never⟩)
  let (st, letB) := st.intern (.letE su apcb inner)
  let (st, big) := st.intern (.lam s0 letB ⟨.never⟩)
  let (st, apb10) := st.intern (.app b1 b0)
  let (st, piIn) := st.intern (.forallE s1 apb10 ⟨.never⟩)
  let (st, piT) := st.intern (.forallE s0 piIn ⟨.never⟩)
  let (st, piS) := st.intern (.forallE s0 s1 ⟨.never⟩)
  let (st, lamIn) := st.intern (.lam s1 apb10 ⟨.never⟩)
  let (st, lamT2) := st.intern (.lam s0 lamIn ⟨.never⟩)
  let (st, sp1) := st.intern (.app cf fv0)
  let (st, spine) := st.intern (.app sp1 b0)
  { st, z, one, pu, anon, foo, bar, uN, usZ, usU,
    s0, s1, su, cf, cb, b0, b1, b2, lit7, fv0, fv1,
    ap1, pj, lamT, allT, letT, big, piT, piS, lamT2, spine }

/-- con-leche: none — the initial checker state over the fixture. -/
private def S0 : AState := AState.init fx.st

/-- con-leche: none — the fuel every check runs at.  The fixture's deepest
term is six nodes deep; 100 is a comfortable margin and the walks all
terminate long before it. -/
private def F : Nat := 100

/-- con-leche: none — the denotation of a fixture handle.  Every handle below
is checked to denote (§"The fixture denotes what it should"), so the default
is unreachable. -/
private def E (h : EIdx) : Expr := (denoteE fx.st h).getD (.bvar 999)

/-- con-leche: none — the denotation of a fixture name handle. -/
private def N (h : NIdx) : ConLeche.Name := (denoteN fx.st.ns h).getD .anonymous

/-- con-leche: none — the denotation of a fixture level handle. -/
private def L (h : LIdx) : Level := (denoteL fx.st.ls h).getD .zero

/-! ## The fixture denotes what it should

The one place a con-leche value is written out by hand.  Everything after
this section compares the twin's answer against con-leche's function applied
to `E h`, which is only meaningful because these hold. -/

#guard denoteE fx.st fx.s0 == some (Expr.sort .zero)
#guard denoteE fx.st fx.s1 == some (Expr.sort (.succ .zero))
#guard denoteE fx.st fx.su == some (Expr.sort (.param (.str .anonymous "u")))
#guard denoteE fx.st fx.cf == some (Expr.const (.str .anonymous "foo") [.zero])
#guard denoteE fx.st fx.cb ==
  some (Expr.const (.str .anonymous "bar") [.param (.str .anonymous "u")])
#guard denoteE fx.st fx.fv1 == some (Expr.fvar 1 (.sort (.succ .zero)))
#guard denoteE fx.st fx.lit7 == some (Expr.lit (.natVal 7))
#guard denoteE fx.st fx.lamT ==
  some (Expr.lam (.sort .zero)
    (.app (.const (.str .anonymous "foo") [.zero]) (.bvar 0)) ⟨.never⟩)
#guard denoteE fx.st fx.big ==
  some (Expr.lam (.sort .zero)
    (.letE (.sort (.param (.str .anonymous "u")))
      (.app (.const (.str .anonymous "bar") [.param (.str .anonymous "u")]) (.bvar 0))
      (.forallE (.sort (.succ .zero))
        (.proj (.str .anonymous "foo") 0
          (.app (.bvar 2) (.app (.fvar 1 (.sort (.succ .zero))) (.bvar 0))))
        ⟨.never⟩))
    ⟨.never⟩)
#guard denoteE fx.st fx.piT ==
  some (Expr.forallE (.sort .zero)
    (.forallE (.sort (.succ .zero)) (.app (.bvar 1) (.bvar 0)) ⟨.never⟩) ⟨.never⟩)
#guard (denoteE fx.st fx.letT).isSome
#guard (denoteE fx.st fx.allT).isSome
#guard (denoteE fx.st fx.pj).isSome
#guard (denoteE fx.st fx.spine).isSome
#guard (denoteE fx.st fx.lamT2).isSome
#guard (denoteE fx.st fx.piS).isSome
#guard denoteN fx.st.ns fx.foo == some (.str .anonymous "foo")
#guard denoteL fx.st.ls fx.pu == some (.param (.str .anonymous "u"))
#guard denoteLs fx.st.lss fx.usZ == some [Level.zero]

/-! ## The checkers

One per result shape.  Each runs the twin from `S0`, reads the answer back
against the store the run *ended* in (the arena grows), and compares. -/

/-- con-leche: none — map `denoteE` over a list of handles. -/
private def mapDen (s : EStore) : List EIdx → Option (List Expr)
  | [] => some []
  | h :: hs =>
    match denoteE s h, mapDen s hs with
    | some e, some es => some (e :: es)
    | _, _ => none

/-- con-leche: none — map `denoteE` over a list of indexed handles. -/
private def mapDenIdx (s : EStore) : List (Nat × EIdx) → Option (List (Nat × Expr))
  | [] => some []
  | (i, h) :: hs =>
    match denoteE s h, mapDenIdx s hs with
    | some e, some es => some ((i, e) :: es)
    | _, _ => none

/-- con-leche: none — map `denoteE` over a binder list. -/
private def mapDenB (s : EStore) :
    List (EIdx × BinderMeta) → Option (List (Expr × BinderMeta))
  | [] => some []
  | (h, m) :: hs =>
    match denoteE s h, mapDenB s hs with
    | some e, some es => some ((e, m) :: es)
    | _, _ => none

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

/-- con-leche: none — a `List EIdx`-valued twin. -/
private def chkLE (c : AM (List EIdx)) (expect : List Expr) : Bool :=
  match c.run S0 with
  | .ok (r, s') => mapDen s'.store r == some expect
  | .error _ => false

/-- con-leche: none — a `Bool`-valued twin. -/
private def chkB (c : AM Bool) (expect : Bool) : Bool :=
  match c.run S0 with
  | .ok (r, _) => r == expect
  | .error _ => false

/-- con-leche: none — a `Nat`-valued twin. -/
private def chkN (c : AM Nat) (expect : Nat) : Bool :=
  match c.run S0 with
  | .ok (r, _) => r == expect
  | .error _ => false

/-- con-leche: none — an `Option PropWhen`-valued twin (no term crosses the
result, so the comparison is direct). -/
private def chkOPw (c : AM (Option PropWhen)) (expect : Option PropWhen) : Bool :=
  match c.run S0 with
  | .ok (r, _) => r == expect
  | .error _ => false

/-- con-leche: none — an `Option LIdx`-valued twin. -/
private def chkOL (c : AM (Option LIdx)) (expect : Option Level) : Bool :=
  match c.run S0, expect with
  | .ok (some r, s'), some u => denoteL s'.store.ls r == some u
  | .ok (none, _), none => true
  | _, _ => false

/-- con-leche: none — the `fvarLeaves` shape. -/
private def chkFvL (c : AM (List (Nat × EIdx))) (expect : List (Nat × Expr)) : Bool :=
  match c.run S0 with
  | .ok (r, s') => mapDenIdx s'.store r == some expect
  | .error _ => false

/-- con-leche: none — the `instPisAt` / `instLamsAt` shape. -/
private def chkPair (c : AM (Option (List EIdx × EIdx)))
    (expect : Option (List Expr × Expr)) : Bool :=
  match c.run S0, expect with
  | .ok (some r, s'), some p =>
    mapDen s'.store r.1 == some p.1 && denoteE s'.store r.2 == some p.2
  | .ok (none, _), none => true
  | _, _ => false

/-- con-leche: none — the `stripLams` / `stripPis` shape. -/
private def chkBinders (c : AM (Option (List (EIdx × BinderMeta) × EIdx)))
    (expect : Option (List (Expr × BinderMeta) × Expr)) : Bool :=
  match c.run S0, expect with
  | .ok (some r, s'), some p =>
    mapDenB s'.store r.1 == some p.1 && denoteE s'.store r.2 == some p.2
  | .ok (none, _), none => true
  | _, _ => false

/-! ## `instantiate1` — `ExprOps.lean:29-45`, `:80-116`, `:182-184` -/

#guard chkE (instantiate1Fast F fx.big fx.cf 0) ((E fx.big).instantiate1 (E fx.cf) 0)
#guard chkE (instantiate1Fast F fx.big fx.cf 1) ((E fx.big).instantiate1 (E fx.cf) 1)
#guard chkE (instantiate1Fast F fx.letT fx.s1 0) ((E fx.letT).instantiate1 (E fx.s1) 0)
#guard chkE (instantiate1Fast F fx.b2 fx.cf 0) ((E fx.b2).instantiate1 (E fx.cf) 0)
#guard chkE (instantiate1Fast F fx.b0 fx.cf 0) ((E fx.b0).instantiate1 (E fx.cf) 0)
#guard chkE (instantiate1Fast F fx.lit7 fx.cf 0) ((E fx.lit7).instantiate1 (E fx.cf) 0)
#guard chkE (instantiate1Fast F fx.pj fx.fv0 0) ((E fx.pj).instantiate1 (E fx.fv0) 0)
-- the memoized walk without the top-level bracket is the same answer
#guard chkE (instantiate1Go fx.cf F fx.big 0) ((E fx.big).instantiate1 (E fx.cf) 0)

/-! ## `instantiateList` — `ExprOps.lean:191-235`, `:267-303`, `:371-373` -/

#guard chkE (instantiateListFast F fx.big [fx.cf, fx.s1] 0)
  ((E fx.big).instantiateList [E fx.cf, E fx.s1] 0)
#guard chkE (instantiateListFast F fx.big [fx.cf, fx.s1] 1)
  ((E fx.big).instantiateList [E fx.cf, E fx.s1] 1)
#guard chkE (instantiateListFast F fx.letT [fx.fv0] 0)
  ((E fx.letT).instantiateList [E fx.fv0] 0)
#guard chkE (instantiateListFast F fx.b2 [fx.cf] 0) ((E fx.b2).instantiateList [E fx.cf] 0)
-- the unmemoized walk (the one `instantiateListGo`'s `bvar` arm calls)
#guard chkE (instantiateList [fx.cf, fx.s1] F fx.big 0)
  ((E fx.big).instantiateList [E fx.cf, E fx.s1] 0)
#guard chkE (instantiateList [fx.cf] F fx.b0 0) ((E fx.b0).instantiateList [E fx.cf] 0)

/-! ## `liftLooseBVars` — `ExprOps.lean:380-400`, `:430-466`, `:532-534` -/

#guard chkE (liftLooseBVarsFast F 2 0 fx.big) (Expr.liftLooseBVars 2 0 (E fx.big))
#guard chkE (liftLooseBVarsFast F 3 1 fx.big) (Expr.liftLooseBVars 3 1 (E fx.big))
#guard chkE (liftLooseBVarsFast F 1 0 fx.letT) (Expr.liftLooseBVars 1 0 (E fx.letT))
#guard chkE (liftLooseBVarsGo 2 F fx.big 0) (Expr.liftLooseBVars 2 0 (E fx.big))

/-! ## `resetMeta` — `ExprOps.lean:552-559`, `:579-615`, `:687-688` -/

#guard chkE (resetMetaFast F fx.big) (Expr.resetMeta (E fx.big))
#guard chkE (resetMetaFast F fx.lamT) (Expr.resetMeta (E fx.lamT))
#guard chkE (resetMetaFast F fx.fv1) (Expr.resetMeta (E fx.fv1))
#guard chkE (resetMetaGo F fx.big) (Expr.resetMeta (E fx.big))

/-! ## The measures and the scope predicates -/

#guard chkN (sizeB F fx.big) (Expr.sizeB (E fx.big))
#guard chkN (sizeB F fx.fv1) (Expr.sizeB (E fx.fv1))
#guard chkN (sizeF F fx.big) (Expr.sizeF (E fx.big))
#guard chkN (sizeF F fx.fv1) (Expr.sizeF (E fx.fv1))

#guard chkE (abstractRange F fx.big 0 2 0) (Expr.abstractRange (E fx.big) 0 2 0)
#guard chkE (abstractRange F fx.big 1 1 0) (Expr.abstractRange (E fx.big) 1 1 0)
#guard chkE (abstractRange F fx.allT 0 3 1) (Expr.abstractRange (E fx.allT) 0 3 1)

#guard chkFvL (fvarLeaves F fx.big) (Expr.fvarLeaves (E fx.big))
#guard chkFvL (fvarLeaves F fx.fv1) (Expr.fvarLeaves (E fx.fv1))
#guard chkFvL (fvarLeaves F fx.s0) (Expr.fvarLeaves (E fx.s0))

#guard chkB (wscopedB F 5 fx.big) (Expr.wscopedB 5 (E fx.big))
#guard chkB (wscopedB F 1 fx.big) (Expr.wscopedB 1 (E fx.big))
#guard chkB (wscopedB F 0 fx.big) (Expr.wscopedB 0 (E fx.big))
#guard chkB (wscopedB F 2 fx.letT) (Expr.wscopedB 2 (E fx.letT))

#guard chkB (looseBVarsBounded F 3 fx.big) (Expr.looseBVarsBounded 3 (E fx.big))
#guard chkB (looseBVarsBounded F 0 fx.big) (Expr.looseBVarsBounded 0 (E fx.big))
#guard chkB (looseBVarsBounded F 1 fx.letT) (Expr.looseBVarsBounded 1 (E fx.letT))

/-! ## The one-node readers -/

#guard chkB (isLam fx.big) (Expr.isLam (E fx.big))
#guard chkB (isLam fx.piT) (Expr.isLam (E fx.piT))
#guard chkOPw (lamPw fx.big) (Expr.lamPw (E fx.big))
#guard chkOPw (lamPw fx.piT) (Expr.lamPw (E fx.piT))
#guard chkOPw (forallPw fx.piT) (Expr.forallPw (E fx.piT))
#guard chkOPw (forallPw fx.big) (Expr.forallPw (E fx.big))
#guard chkB (hasFvar F fx.big) (Expr.hasFvar (E fx.big))
#guard chkB (hasFvar F fx.piT) (Expr.hasFvar (E fx.piT))
#guard chkB (hasFvar F fx.fv0) (Expr.hasFvar (E fx.fv0))

/-! ## Application spines -/

#guard chkE (getAppFn F fx.spine) (Expr.getAppFn (E fx.spine))
#guard chkE (getAppFn F fx.cf) (Expr.getAppFn (E fx.cf))
#guard chkLE (getAppArgs F fx.spine) (Expr.getAppArgs (E fx.spine))
#guard chkLE (getAppArgs F fx.cf) (Expr.getAppArgs (E fx.cf))
#guard chkE (mkAppN fx.cf [fx.fv0, fx.b0]) (Expr.mkAppN (E fx.cf) [E fx.fv0, E fx.b0])
#guard chkE (mkAppN fx.cf []) (Expr.mkAppN (E fx.cf) [])

/-! ## `renameConsts` — `ExprOps.lean:930-956`, `:999-1036`, `:1109-1111`

The twin's renaming is a map on name HANDLES; the bridge's obligation is that
it denotes con-leche's map on names, and here the two are written side by
side. -/

/-- con-leche: none — the fixture's renaming, on handles. -/
private def renH (n : NIdx) : NIdx := if n == fx.foo then fx.bar else n

/-- con-leche: none — the same renaming, on names. -/
private def renP (n : ConLeche.Name) : ConLeche.Name :=
  if n == N fx.foo then N fx.bar else n

#guard chkE (renameConstsFast F renH fx.big) (Expr.renameConsts renP (E fx.big))
#guard chkE (renameConstsFast F renH fx.cf) (Expr.renameConsts renP (E fx.cf))
#guard chkE (renameConstsFast F renH fx.fv1) (Expr.renameConsts renP (E fx.fv1))
#guard chkE (renameConstsGo renH F fx.big) (Expr.renameConsts renP (E fx.big))

/-! ## Telescopes -/

#guard chkBinders (stripLams 2 fx.lamT2) (Expr.stripLams 2 (E fx.lamT2))
#guard chkBinders (stripLams 0 fx.lamT2) (Expr.stripLams 0 (E fx.lamT2))
#guard chkBinders (stripLams 3 fx.lamT2) (Expr.stripLams 3 (E fx.lamT2))
#guard chkBinders (stripPis 2 fx.piT) (Expr.stripPis 2 (E fx.piT))
#guard chkBinders (stripPis 1 fx.piT) (Expr.stripPis 1 (E fx.piT))
#guard chkBinders (stripPis 3 fx.piT) (Expr.stripPis 3 (E fx.piT))

#guard chkE (piResult F fx.piT) (Expr.piResult (E fx.piT))
#guard chkE (piResult F fx.cf) (Expr.piResult (E fx.cf))
#guard chkN (piArity F fx.piT) (Expr.piArity (E fx.piT))
#guard chkN (piArity F fx.cf) (Expr.piArity (E fx.cf))
#guard chkOL (resultSort F fx.piS) (Expr.resultSort (E fx.piS))
#guard chkOL (resultSort F fx.piT) (Expr.resultSort (E fx.piT))
#guard chkOL (resultSort F fx.s1) (Expr.resultSort (E fx.s1))

#guard chkOE (instPis F fx.piT [fx.cf, fx.s1]) (Expr.instPis (E fx.piT) [E fx.cf, E fx.s1])
#guard chkOE (instPis F fx.piT []) (Expr.instPis (E fx.piT) [])
#guard chkOE (instPis F fx.cf [fx.s1]) (Expr.instPis (E fx.cf) [E fx.s1])

#guard chkPair (instPisAt F [fx.cf, fx.s1] fx.piT)
  (Expr.instPisAt [E fx.cf, E fx.s1] (E fx.piT))
#guard chkPair (instPisAt F [] fx.piT) (Expr.instPisAt [] (E fx.piT))
#guard chkPair (instPisAt F [fx.cf] fx.lamT2) (Expr.instPisAt [E fx.cf] (E fx.lamT2))
#guard chkPair (instLamsAt F [fx.cf, fx.s1] fx.lamT2)
  (Expr.instLamsAt [E fx.cf, E fx.s1] (E fx.lamT2))
#guard chkPair (instLamsAt F [fx.cf] fx.piT) (Expr.instLamsAt [E fx.cf] (E fx.piT))

#guard chkPair (instPisAtFGo F [] [fx.cf, fx.s1] fx.piT)
  (Expr.instPisAtFGo [] [E fx.cf, E fx.s1] (E fx.piT))
#guard chkPair (instPisAtFGo F [fx.fv0] [fx.cf] fx.piT)
  (Expr.instPisAtFGo [E fx.fv0] [E fx.cf] (E fx.piT))
#guard chkPair (instPisAtF F [fx.cf, fx.s1] fx.piT)
  (Expr.instPisAtF [E fx.cf, E fx.s1] (E fx.piT))
#guard chkPair (instPisAtF F [fx.cf] fx.lamT2) (Expr.instPisAtF [E fx.cf] (E fx.lamT2))
#guard chkPair (instLamsAtFGo F [] [fx.cf, fx.s1] fx.lamT2)
  (Expr.instLamsAtFGo [] [E fx.cf, E fx.s1] (E fx.lamT2))
#guard chkPair (instLamsAtF F [fx.cf, fx.s1] fx.lamT2)
  (Expr.instLamsAtF [E fx.cf, E fx.s1] (E fx.lamT2))
#guard chkPair (instLamsAtF F [fx.cf] fx.piT) (Expr.instLamsAtF [E fx.cf] (E fx.piT))

#guard chkE (fvarTypeD fx.fv1) (Expr.fvarTypeD (E fx.fv1))
#guard chkE (fvarTypeD fx.cf) (Expr.fvarTypeD (E fx.cf))

#guard chkE (instSpine F [fx.cf, fx.s1] 1 fx.big)
  (Expr.instSpine [E fx.cf, E fx.s1] 1 (E fx.big))
#guard chkE (instSpine F [] 0 fx.big) (Expr.instSpine [] 0 (E fx.big))

#guard chkB (recRulePlain F fx.piT 2 2 1) (Expr.recRulePlain (E fx.piT) 2 2 1)
#guard chkB (recRulePlain F fx.piT 1 1 1) (Expr.recRulePlain (E fx.piT) 1 1 1)
#guard chkB (recRulePlain F fx.piT 2 1 2) (Expr.recRulePlain (E fx.piT) 2 1 2)
#guard chkB (recRulePlain F fx.big 2 2 1) (Expr.recRulePlain (E fx.big) 2 2 1)

#guard chkOE (pisToLams 2 fx.piT fx.cf) (Expr.pisToLams 2 (E fx.piT) (E fx.cf))
#guard chkOE (pisToLams 0 fx.piT fx.cf) (Expr.pisToLams 0 (E fx.piT) (E fx.cf))
#guard chkOE (pisToLams 3 fx.piT fx.cf) (Expr.pisToLams 3 (E fx.piT) (E fx.cf))
#guard chkOE (replacePiBody 2 fx.piT fx.cf) (Expr.replacePiBody 2 (E fx.piT) (E fx.cf))
#guard chkOE (replacePiBody 1 fx.piT fx.cf) (Expr.replacePiBody 1 (E fx.piT) (E fx.cf))
#guard chkOE (replacePiBody 3 fx.piT fx.cf) (Expr.replacePiBody 3 (E fx.piT) (E fx.cf))

/-! ## The packed range fields -/

#guard chkN (bvarBoundMemo F fx.big) (Expr.bvarBound (E fx.big))
#guard chkN (bvarBoundMemo F fx.letT) (Expr.bvarBound (E fx.letT))
#guard chkN (bvarBoundMemo F fx.b2) (Expr.bvarBound (E fx.b2))
#guard chkN (bvarBoundGo F fx.big) (Expr.bvarBound (E fx.big))
#guard chkN (fvarRangeMemo F fx.big) (Expr.fvarRange (E fx.big))
#guard chkN (fvarRangeMemo F fx.fv1) (Expr.fvarRange (E fx.fv1))
#guard chkN (fvarRangeGo F fx.big) (Expr.fvarRange (E fx.big))
#guard chkN (bvarB F fx.big) (Expr.bvarB (E fx.big))
#guard chkN (bvarB F fx.b2) (Expr.bvarB (E fx.b2))
#guard chkN (fvarB F fx.big) (Expr.fvarB (E fx.big))
#guard chkN (fvarB F fx.fv1) (Expr.fvarB (E fx.fv1))
#guard chkB (hasFvarFast F fx.big) (Expr.hasFvarFast (E fx.big))
#guard chkB (hasFvarFast F fx.piT) (Expr.hasFvarFast (E fx.piT))
#guard chkB (looseBVarsBoundedFast F 3 fx.big) (Expr.looseBVarsBoundedFast 3 (E fx.big))
#guard chkB (looseBVarsBoundedFast F 0 fx.big) (Expr.looseBVarsBoundedFast 0 (E fx.big))

-- the field read and the walk agree, which is con-leche's `bvarB_eq` /
-- `fvarB_eq` / `hasFvar_eq` at the fixture
#guard chkN (bvarB F fx.big) (Expr.bvarBound (E fx.big))
#guard chkN (fvarB F fx.big) (Expr.fvarRange (E fx.big))
#guard chkB (hasFvarFast F fx.big) (Expr.hasFvar (E fx.big))
#guard chkB (looseBVarsBoundedFast F 3 fx.big) (Expr.looseBVarsBounded 3 (E fx.big))

/-! ## `abstract1` — `ExprOps.lean:760-776`, `:1789-1833`, `:1927-1929` -/

#guard chkE (abstract1Fast F fx.big 0 0) (Expr.abstract1 (E fx.big) 0 0)
#guard chkE (abstract1Fast F fx.big 1 0) (Expr.abstract1 (E fx.big) 1 0)
#guard chkE (abstract1Fast F fx.big 2 0) (Expr.abstract1 (E fx.big) 2 0)
#guard chkE (abstract1Fast F fx.big 1 3) (Expr.abstract1 (E fx.big) 1 3)
#guard chkE (abstract1Fast F fx.fv0 0 0) (Expr.abstract1 (E fx.fv0) 0 0)
#guard chkE (abstract1Go 1 F fx.big 0) (Expr.abstract1 (E fx.big) 1 0)

/-! ## `lowerBVars` — `ExprOps.lean:694-716`, `:2012-2049`, `:2144-2146` -/

#guard chkE (lowerBVarsFast F 1 0 fx.big) (Expr.lowerBVars 1 0 (E fx.big))
#guard chkE (lowerBVarsFast F 2 0 fx.big) (Expr.lowerBVars 2 0 (E fx.big))
#guard chkE (lowerBVarsFast F 1 1 fx.big) (Expr.lowerBVars 1 1 (E fx.big))
#guard chkE (lowerBVarsFast F 5 0 fx.big) (Expr.lowerBVars 5 0 (E fx.big))
#guard chkE (lowerBVarsGo 1 F fx.big 0) (Expr.lowerBVars 1 0 (E fx.big))

/-! ## `instantiate1Lift` — `ExprOps.lean:718-739`, `:2222-2261`, `:2356-2358` -/

#guard chkE (instantiate1LiftFast F fx.big fx.cf 0) ((E fx.big).instantiate1Lift (E fx.cf) 0)
#guard chkE (instantiate1LiftFast F fx.big fx.b1 0) ((E fx.big).instantiate1Lift (E fx.b1) 0)
#guard chkE (instantiate1LiftFast F fx.big fx.letT 1) ((E fx.big).instantiate1Lift (E fx.letT) 1)
#guard chkE (instantiate1LiftFast F fx.letT fx.b0 0) ((E fx.letT).instantiate1Lift (E fx.b0) 0)
#guard chkE (instantiate1LiftGo fx.cf F fx.big 0) ((E fx.big).instantiate1Lift (E fx.cf) 0)

#guard chkOE (instPisAtLift F [fx.cf, fx.b0] fx.piT)
  (Expr.instPisAtLift [E fx.cf, E fx.b0] (E fx.piT))
#guard chkOE (instPisAtLift F [] fx.piT) (Expr.instPisAtLift [] (E fx.piT))
#guard chkOE (instPisAtLift F [fx.cf] fx.lamT2) (Expr.instPisAtLift [E fx.cf] (E fx.lamT2))

/-! ## Equality, and the two derived bits -/

#guard exprPtrBEq fx.big fx.big == Expr.exprPtrBEq (E fx.big) (E fx.big)
#guard exprPtrBEq fx.big fx.letT == Expr.exprPtrBEq (E fx.big) (E fx.letT)
#guard exprPtrBEq fx.s0 fx.s1 == Expr.exprPtrBEq (E fx.s0) (E fx.s1)
-- interning is hash-consing, so a rebuilt node is the SAME handle and the
-- index test is the structural test (`denoteE_inj`, task #97a)
#guard
  match (internE (.app fx.cf fx.b0)).run S0 with
  | .ok (r, _) => exprPtrBEq r fx.ap1
  | .error _ => false

#guard chkB (LIdx.hasParam fx.pu) (Level.hasParam (L fx.pu))
#guard chkB (LIdx.hasParam fx.z) (Level.hasParam (L fx.z))
#guard chkB (LIdx.hasParam fx.one) (Level.hasParam (L fx.one))
#guard chkB (EIdx.hasLevelParam fx.big) (Expr.hasLevelParam (E fx.big))
#guard chkB (EIdx.hasLevelParam fx.piT) (Expr.hasLevelParam (E fx.piT))
#guard chkB (EIdx.hasLevelParam fx.su) (Expr.hasLevelParam (E fx.su))
#guard chkB (EIdx.hasLevelParam fx.cb) (Expr.hasLevelParam (E fx.cb))

/-! ## `instantiateLevelParams` — `ExprOps.lean:2564-2603`, `:2718-2720` -/

#guard chkE (instLPFast F [fx.uN] fx.usZ fx.big)
  (Expr.instantiateLevelParams [N fx.uN] [L fx.z] (E fx.big))
#guard chkE (instLPFast F [fx.uN] fx.usU fx.big)
  (Expr.instantiateLevelParams [N fx.uN] [L fx.pu] (E fx.big))
#guard chkE (instLPFast F [fx.uN] fx.usZ fx.su)
  (Expr.instantiateLevelParams [N fx.uN] [L fx.z] (E fx.su))
#guard chkE (instLPFast F [fx.uN] fx.usZ fx.cb)
  (Expr.instantiateLevelParams [N fx.uN] [L fx.z] (E fx.cb))
#guard chkE (instLPFast F [fx.uN] fx.usZ fx.piT)
  (Expr.instantiateLevelParams [N fx.uN] [L fx.z] (E fx.piT))
#guard chkE (instLPGo [N fx.uN] [L fx.z] F fx.big)
  (Expr.instantiateLevelParams [N fx.uN] [L fx.z] (E fx.big))

/-! ## The store primitives of `Monad.lean` -/

#guard
  match (view fx.big).run S0 with
  | .ok (.lam ty body _, _) => ty == fx.s0 && body != fx.s0
  | _ => false

#guard
  match (readLevel fx.pu).run S0 with
  | .ok (u, _) => u == Level.param (.str .anonymous "u")
  | .error _ => false

#guard
  match (readName fx.foo).run S0 with
  | .ok (n, _) => n == ConLeche.Name.str .anonymous "foo"
  | .error _ => false

#guard
  match (internLevel (.succ (.succ .zero))).run S0 with
  | .ok (u, s') => denoteL s'.store.ls u == some (.succ (.succ .zero))
  | .error _ => false

#guard
  match (internName (.str (.str .anonymous "a") "b")).run S0 with
  | .ok (n, s') => denoteN s'.store.ns n == some (.str (.str .anonymous "a") "b")
  | .error _ => false

#guard
  match (internLevels [Level.zero, .param (.str .anonymous "u")]).run S0 with
  | .ok (us, s') =>
    denoteLs s'.store.lss us == some [Level.zero, .param (.str .anonymous "u")]
  | .error _ => false

/-! ## Fuel exhaustion fails rather than answering wrongly -/

-- `big`'s loose-bvar bound is 0, so the derived-word cutoff answers it at
-- any fuel; `letT`'s is 1, so the walk really descends and fuel 1 runs out.
#guard chkE (instantiate1Fast 1 fx.big fx.cf 0) ((E fx.big).instantiate1 (E fx.cf) 0)

#guard
  match (instantiate1Fast 1 fx.letT fx.cf 0).run S0 with
  | .ok _ => false
  | .error _ => true

#guard
  match (sizeB 0 fx.big).run S0 with
  | .ok _ => false
  | .error _ => true

end ConRon.Arena
