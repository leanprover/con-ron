/-
# The uniform inductive route, differentially (task #97 P2d part 2; task #105)

The module-level differential check of `Arena/Inductives/*`, the shape
`CheckerTest.lean` uses (DESIGN §8.4, "correctness before proofs"):

> write a declaration list ONCE, as con-leche `Declaration` values — inductive
> blocks as an elaborator exports them; intern it into the arena; run the
> arena's `checkDeclsPure` and its two-phase `installThenCheck`; read the
> resulting environment back with `denoteCIList`, and compare with
> con-leche's own `checkDeclsPure` on the SAME values.

"Whole outcome": an accept must meet an accept at the same environment —
every installed constant (types, the GENERATED recursors' rules, capability
records, projection tables) compared as `ConstantInfo` values — and a failure
must meet a failure of the same KIND (messages are not compared, DESIGN §3.1).

**The blocks are written by hand**, recursor types included, in the official
shape (formers, then constructors, then recursors — `blockSplit`'s order).
The uniform route GENERATES each recursor and compares it with the stream's by
defeq, and it never reads the stream's rules (it installs its own), so a
fixture needs a correct recursor TYPE and nothing more; `accepts` pins that
con-leche accepts each positive fixture, so a wrong hand-written type cannot
make a check pass vacuously on two agreeing errors.

Covered: a recursive family (`N`), a structure with its projection table
(`Pair`), an indexed propositional family with a large eliminator (`Eq'`), a
`Prop` with rule K (`Tru`), a MUTUAL block (`A`/`B`), a NESTED block (`Tree`
through the container `L`, two recursors), and the rejects and declines: the
declared parameter count, a non-positive occurrence, a duplicate constructor,
a shapeless block, a wrong recursor type.

Nothing here is a proof and nothing here is an `#eval` print: every check is
kernel-reduced, so a disagreement is a build failure.
-/
import ConRon.Arena.Checker
import ConLeche.Kernel.CheckDecl

namespace ConRon.Arena.InductivesTest

open ConLeche
open ConRon.Arena

/-! ## The harness -/

/-- con-leche: none — the mode every check runs at. -/
private def MU : CheckMode := .verified

/-- con-leche: none — con-leche's entry point record. -/
private def OPS : ConLeche.CheckerOps ConLeche.CheckM := ConLeche.pureOps MU

/-- con-leche: none — an arena error against a con-leche error, by KIND. -/
private def errEq : CheckError → ConLeche.CheckError → Bool
  | .notImplemented _, .notImplemented _ => true
  | .invalid _, .invalid _ => true
  | .internal _, .internal _ => true
  | _, _ => false

/-- con-leche: none — intern a declaration list and run the arena's
`checkDeclsPure` on it. -/
private def runDecls (dsCL : List Declaration) : AM IFEnv := do
  let (_, ds) ← Frontend.internDecls ∅ dsCL
  checkDeclsPure MU [] ds

/-- con-leche: none — the arena's `checkDeclsPure` against con-leche's, over
the whole outcome. -/
private def chk (dsCL : List Declaration) : Bool :=
  match (do internReservedPins; runDecls dsCL).run (AState.init EStore.empty),
      (ConLeche.checkDeclsPure MU OPS [] dsCL : ConLeche.CheckM ConLeche.Env) with
  | .ok (fe, s'), .ok env =>
    Frontend.denoteCIList s'.store fe.env.consts == some env.consts
  | .error a, .error b => errEq a b
  | _, _ => false

/-- con-leche: none — the arena's TWO-PHASE fold (the one the binary runs),
with the startup pin walk in front. -/
private def runInstall (dsCL : List Declaration) :
    AM (Except (CheckError × Nat) IFEnv) := do
  let (_, ds) ← Frontend.internDecls ∅ dsCL
  let pins ← internAllPins []
  installThenCheck MU pins ds.toArray

/-- con-leche: none — the two-phase fold against con-leche's one-phase
`checkDeclsPure`, over the whole outcome. -/
private def chkInstall (dsCL : List Declaration) : Bool :=
  match (do internReservedPins; runInstall dsCL).run (AState.init EStore.empty),
      (ConLeche.checkDeclsPure MU OPS [] dsCL : ConLeche.CheckM ConLeche.Env) with
  | .ok (.ok fe, s'), .ok env =>
    Frontend.denoteCIList s'.store fe.env.consts == some env.consts
  | .ok (.error (a, _), _), .error b => errEq a b
  | _, _ => false

/-- con-leche: none — does con-leche accept the list?  Pins the positive
fixtures. -/
private def accepts (dsCL : List Declaration) : Bool :=
  (ConLeche.checkDeclsPure MU OPS [] dsCL : ConLeche.CheckM ConLeche.Env).toOption.isSome

/-- con-leche: none — how many constants con-leche's run installs. -/
private def installed (dsCL : List Declaration) : Nat :=
  match (ConLeche.checkDeclsPure MU OPS [] dsCL : ConLeche.CheckM ConLeche.Env) with
  | .ok e => e.consts.length
  | .error _ => 0

/-- con-leche: none — does con-leche's run install a projection TABLE? -/
private def hasTable (dsCL : List Declaration) : Bool :=
  match (ConLeche.checkDeclsPure MU OPS [] dsCL : ConLeche.CheckM ConLeche.Env) with
  | .ok e => e.consts.any fun ci => match ci with
    | .projInfo _ => true
    | _ => false
  | .error _ => false

/-! ## Term builders -/

/-- con-leche: none — a `∀` binder at the parse placeholder datum. -/
private def pi (ty b : ConLeche.Expr) : ConLeche.Expr := .forallE ty b ⟨.never⟩
/-- con-leche: none — a fixture name. -/
private def nm (s : String) : ConLeche.Name := ConLeche.Name.anonymous.str s
/-- con-leche: none — a fixture name `a.b`. -/
private def nm2 (a b : String) : ConLeche.Name := (nm a).str b
/-- con-leche: none — a constant at no universe arguments. -/
private def c0 (n : ConLeche.Name) : ConLeche.Expr := .const n []
/-- con-leche: none — a de Bruijn variable. -/
private def bv (i : Nat) : ConLeche.Expr := .bvar i
/-- con-leche: none — an application. -/
private def ap (f a : ConLeche.Expr) : ConLeche.Expr := .app f a
/-- con-leche: none — `Type`. -/
private def ty1 : ConLeche.Expr := .sort (.succ .zero)
/-- con-leche: none — `Sort u` at a named parameter. -/
private def sortP (u : String) : ConLeche.Expr := .sort (.param (nm u))
/-- con-leche: none — a stream rule placeholder: the uniform route never
reads the stream's rules, so only the constructor and the field count are
meaningful. -/
private def rl (c : ConLeche.Name) (nF : Nat) : RecRule :=
  { ctor := c, nfields := nF, ctorParams := 0, fire := .inert, rhs := ty1 }

/-! ## Fixture 1 — `N`, a recursive family -/

/-- con-leche: none — a fixture term. -/
private def cN : ConLeche.Expr := c0 (nm "N")
/-- con-leche: none — `N.rec.{u} : (motive : N → Sort u) → motive N.zero →
((n : N) → motive n → motive (N.succ n)) → (t : N) → motive t`. -/
private def nRecTy : ConLeche.Expr :=
  pi (pi cN (sortP "u"))
    (pi (ap (bv 0) (c0 (nm2 "N" "zero")))
      (pi (pi cN (pi (ap (bv 2) (bv 0)) (ap (bv 3) (ap (c0 (nm2 "N" "succ")) (bv 1)))))
        (pi cN (ap (bv 3) (bv 0)))))
/-- con-leche: none — the `N` block. -/
private def nBlock : List ConstantInfo :=
  [ .indInfo ⟨nm "N", [], ty1⟩ {},
    .ctorInfo ⟨nm2 "N" "zero", [], cN⟩ 0 0,
    .ctorInfo ⟨nm2 "N" "succ", [], pi cN cN⟩ 0 1,
    .recInfo ⟨nm2 "N" "rec", [nm "u"], nRecTy⟩ 3 3
      [rl (nm2 "N" "zero") 0, rl (nm2 "N" "succ") 1] ]

#guard accepts [.indDecl nBlock 0]
#guard installed [.indDecl nBlock 0] == 4
#guard !hasTable [.indDecl nBlock 0]
#guard chk [.indDecl nBlock 0]
#guard chkInstall [.indDecl nBlock 0]

/-! ## Fixture 2 — `Pair α β`, a structure and its projection table -/

/-- con-leche: none — `Pair a b`. -/
private def pairAt (a b : ConLeche.Expr) : ConLeche.Expr := ap (ap (c0 (nm "Pair")) a) b
/-- con-leche: none — `Pair.mk a b x y`. -/
private def mkAt (a b x y : ConLeche.Expr) : ConLeche.Expr :=
  ap (ap (ap (ap (c0 (nm2 "Pair" "mk")) a) b) x) y
/-- con-leche: none — `Pair.rec.{u} : {α β : Type} → {motive : Pair α β →
Sort u} → ((fst : α) → (snd : β) → motive (Pair.mk α β fst snd)) → (t : Pair
α β) → motive t`. -/
private def pairRecTy : ConLeche.Expr :=
  pi ty1 (pi ty1 (pi (pi (pairAt (bv 1) (bv 0)) (sortP "u"))
    (pi (pi (bv 2) (pi (bv 2) (ap (bv 2) (mkAt (bv 4) (bv 3) (bv 1) (bv 0)))))
      (pi (pairAt (bv 3) (bv 2)) (ap (bv 2) (bv 0))))))
/-- con-leche: none — the `Pair` block. -/
private def pairBlock : List ConstantInfo :=
  [ .indInfo ⟨nm "Pair", [], pi ty1 (pi ty1 ty1)⟩ {},
    .ctorInfo ⟨nm2 "Pair" "mk", [],
      pi ty1 (pi ty1 (pi (bv 1) (pi (bv 1) (pairAt (bv 3) (bv 2)))))⟩ 2 2,
    .recInfo ⟨nm2 "Pair" "rec", [nm "u"], pairRecTy⟩ 4 4 [rl (nm2 "Pair" "mk") 2] ]

#guard accepts [.indDecl pairBlock 2]
#guard hasTable [.indDecl pairBlock 2]
#guard chk [.indDecl pairBlock 2]
#guard chkInstall [.indDecl pairBlock 2]

/-! ## Fixture 3 — `Eq'`, an indexed propositional family, large eliminator -/

/-- con-leche: none — `Eq'.{u} a b c`. -/
private def eqAt (a b c : ConLeche.Expr) : ConLeche.Expr :=
  ap (ap (ap (.const (nm "Eq'") [.param (nm "u")]) a) b) c
/-- con-leche: none — `Eq'.refl.{u} a b`. -/
private def reflAt (a b : ConLeche.Expr) : ConLeche.Expr :=
  ap (ap (.const (nm2 "Eq'" "refl") [.param (nm "u")]) a) b
/-- con-leche: none — `Eq'.rec.{v, u} : {α : Sort u} → {a : α} → {motive : (b :
α) → Eq' α a b → Sort v} → motive a (Eq'.refl α a) → {b : α} → (t : Eq' α a b)
→ motive b t`. -/
private def eqRecTy : ConLeche.Expr :=
  pi (sortP "u") (pi (bv 0)
    (pi (pi (bv 1) (pi (eqAt (bv 2) (bv 1) (bv 0)) (sortP "v")))
      (pi (ap (ap (bv 0) (bv 1)) (reflAt (bv 2) (bv 1)))
        (pi (bv 3) (pi (eqAt (bv 4) (bv 3) (bv 0)) (ap (ap (bv 3) (bv 1)) (bv 0)))))))
/-- con-leche: none — the `Eq'` block. -/
private def eqBlock : List ConstantInfo :=
  [ .indInfo ⟨nm "Eq'", [nm "u"], pi (sortP "u") (pi (bv 0) (pi (bv 1) (.sort .zero)))⟩ {},
    .ctorInfo ⟨nm2 "Eq'" "refl", [nm "u"],
      pi (sortP "u") (pi (bv 0) (eqAt (bv 1) (bv 0) (bv 0)))⟩ 2 0,
    .recInfo ⟨nm2 "Eq'" "rec", [nm "v", nm "u"], eqRecTy⟩ 5 4 [rl (nm2 "Eq'" "refl") 0] ]

#guard accepts [.indDecl eqBlock 2]
#guard !hasTable [.indDecl eqBlock 2]
#guard chk [.indDecl eqBlock 2]
#guard chkInstall [.indDecl eqBlock 2]

/-! ## Fixture 4 — `Tru`, a `Prop` with rule K -/

/-- con-leche: none — `Tru.rec.{u} : (motive : Tru → Sort u) → motive Tru.intro
→ (t : Tru) → motive t`. -/
private def truRecTy : ConLeche.Expr :=
  pi (pi (c0 (nm "Tru")) (sortP "u"))
    (pi (ap (bv 0) (c0 (nm2 "Tru" "intro"))) (pi (c0 (nm "Tru")) (ap (bv 2) (bv 0))))
/-- con-leche: none — the `Tru` block. -/
private def truBlock : List ConstantInfo :=
  [ .indInfo ⟨nm "Tru", [], .sort .zero⟩ {},
    .ctorInfo ⟨nm2 "Tru" "intro", [], c0 (nm "Tru")⟩ 0 0,
    .recInfo ⟨nm2 "Tru" "rec", [nm "u"], truRecTy⟩ 2 2 [rl (nm2 "Tru" "intro") 0] ]

#guard accepts [.indDecl truBlock 0]
#guard chk [.indDecl truBlock 0]
#guard chkInstall [.indDecl truBlock 0]

/-! ## Fixture 5 — a MUTUAL block

`A : Type | a : A | ab : B → A` and `B : Type | b : A → B`: two formers, two
motives, two recursors, through the uniform route. -/

/-- con-leche: none — a fixture term. -/
private def cA : ConLeche.Expr := c0 (nm "A")
/-- con-leche: none — a fixture term. -/
private def cB : ConLeche.Expr := c0 (nm "B")
/-- con-leche: none — the shared prefix of `A.rec` and `B.rec`, closed by
`last`: `(m₁ : A → Sort u) → (m₂ : B → Sort u) → m₁ A.a → ((x : B) → m₂ x →
m₁ (A.ab x)) → ((x : A) → m₁ x → m₂ (B.b x)) → last`. -/
private def abRecTy (last : ConLeche.Expr) : ConLeche.Expr :=
  pi (pi cA (sortP "u")) (pi (pi cB (sortP "u"))
    (pi (ap (bv 1) (c0 (nm2 "A" "a")))
      (pi (pi cB (pi (ap (bv 2) (bv 0)) (ap (bv 4) (ap (c0 (nm2 "A" "ab")) (bv 1)))))
        (pi (pi cA (pi (ap (bv 4) (bv 0)) (ap (bv 4) (ap (c0 (nm2 "B" "b")) (bv 1)))))
          last))))
/-- con-leche: none — the mutual block. -/
private def abBlock : List ConstantInfo :=
  [ .indInfo ⟨nm "A", [], ty1⟩ {},
    .indInfo ⟨nm "B", [], ty1⟩ {},
    .ctorInfo ⟨nm2 "A" "a", [], cA⟩ 0 0,
    .ctorInfo ⟨nm2 "A" "ab", [], pi cB cA⟩ 0 1,
    .ctorInfo ⟨nm2 "B" "b", [], pi cA cB⟩ 0 1,
    .recInfo ⟨nm2 "A" "rec", [nm "u"], abRecTy (pi cA (ap (bv 5) (bv 0)))⟩ 5 5
      [rl (nm2 "A" "a") 0, rl (nm2 "A" "ab") 1],
    .recInfo ⟨nm2 "B" "rec", [nm "u"], abRecTy (pi cB (ap (bv 4) (bv 0)))⟩ 5 5
      [rl (nm2 "B" "b") 1] ]

#guard accepts [.indDecl abBlock 0]
-- seven constants and `B`'s projection table (one constructor, no index)
#guard installed [.indDecl abBlock 0] == 8
#guard chk [.indDecl abBlock 0]
#guard chkInstall [.indDecl abBlock 0]

/-! ## Fixture 6 — a NESTED block

`Tree : Type | node : L Tree → Tree` through the container `L α` (declared
first): the uniform route's positivity through a container at its concrete
instance, and the auxiliary recursor `Tree.rec_1` on `L Tree`. -/

/-- con-leche: none — `L a`. -/
private def lAt (a : ConLeche.Expr) : ConLeche.Expr := ap (c0 (nm "L")) a
/-- con-leche: none — `L.nil a`. -/
private def nilAt (a : ConLeche.Expr) : ConLeche.Expr := ap (c0 (nm2 "L" "nil")) a
/-- con-leche: none — `L.cons a h t`. -/
private def consAt (a h t : ConLeche.Expr) : ConLeche.Expr :=
  ap (ap (ap (c0 (nm2 "L" "cons")) a) h) t
/-- con-leche: none — `L.rec.{u} : {α : Type} → {motive : L α → Sort u} →
motive (L.nil α) → ((head : α) → (tail : L α) → motive tail → motive (L.cons α
head tail)) → (t : L α) → motive t`. -/
private def lRecTy : ConLeche.Expr :=
  pi ty1 (pi (pi (lAt (bv 0)) (sortP "u"))
    (pi (ap (bv 0) (nilAt (bv 1)))
      (pi (pi (bv 2) (pi (lAt (bv 3)) (pi (ap (bv 3) (bv 0))
            (ap (bv 4) (consAt (bv 5) (bv 2) (bv 1))))))
        (pi (lAt (bv 3)) (ap (bv 3) (bv 0))))))
/-- con-leche: none — the container block `L`. -/
private def lBlock : List ConstantInfo :=
  [ .indInfo ⟨nm "L", [], pi ty1 ty1⟩ {},
    .ctorInfo ⟨nm2 "L" "nil", [], pi ty1 (lAt (bv 0))⟩ 1 0,
    .ctorInfo ⟨nm2 "L" "cons", [], pi ty1 (pi (bv 0) (pi (lAt (bv 1)) (lAt (bv 2))))⟩ 1 2,
    .recInfo ⟨nm2 "L" "rec", [nm "u"], lRecTy⟩ 4 4
      [rl (nm2 "L" "nil") 0, rl (nm2 "L" "cons") 2] ]

/-- con-leche: none — a fixture term. -/
private def cT : ConLeche.Expr := c0 (nm "Tree")
/-- con-leche: none — the shared prefix of `Tree.rec` and `Tree.rec_1`,
closed by `last`: `(m₁ : Tree → Sort u) → (m₂ : L Tree → Sort u) → ((a : L
Tree) → m₂ a → m₁ (Tree.node a)) → m₂ (L.nil Tree) → ((head : Tree) → (tail :
L Tree) → m₁ head → m₂ tail → m₂ (L.cons Tree head tail)) → last`. -/
private def treeRecTy (last : ConLeche.Expr) : ConLeche.Expr :=
  pi (pi cT (sortP "u")) (pi (pi (lAt cT) (sortP "u"))
    (pi (pi (lAt cT) (pi (ap (bv 1) (bv 0)) (ap (bv 3) (ap (c0 (nm2 "Tree" "node")) (bv 1)))))
      (pi (ap (bv 1) (nilAt cT))
        (pi (pi cT (pi (lAt cT) (pi (ap (bv 5) (bv 1)) (pi (ap (bv 5) (bv 1))
              (ap (bv 6) (consAt cT (bv 3) (bv 2)))))))
          last))))
/-- con-leche: none — the nested block: one former, one constructor, TWO
recursors. -/
private def treeBlock : List ConstantInfo :=
  [ .indInfo ⟨nm "Tree", [], ty1⟩ {},
    .ctorInfo ⟨nm2 "Tree" "node", [], pi (lAt cT) cT⟩ 0 1,
    .recInfo ⟨nm2 "Tree" "rec", [nm "u"], treeRecTy (pi cT (ap (bv 5) (bv 0)))⟩ 5 5
      [rl (nm2 "Tree" "node") 1],
    .recInfo ⟨nm2 "Tree" "rec_1", [nm "u"], treeRecTy (pi (lAt cT) (ap (bv 4) (bv 0)))⟩ 5 5
      [rl (nm2 "L" "nil") 0, rl (nm2 "L" "cons") 2] ]

#guard accepts [.indDecl lBlock 1]
#guard accepts [.indDecl lBlock 1, .indDecl treeBlock 0]
-- `L`'s four constants, `Tree`'s four and `Tree`'s projection table
#guard installed [.indDecl lBlock 1, .indDecl treeBlock 0] == 9
#guard chk [.indDecl lBlock 1, .indDecl treeBlock 0]
#guard chkInstall [.indDecl lBlock 1, .indDecl treeBlock 0]

/-! ## Rejects and declines -/

/- The declared parameter count (task #228): official's own reject. -/
#guard !accepts [.indDecl nBlock 3]
#guard chk [.indDecl nBlock 3]

/- A non-positive occurrence: `Bad : Type | mk : (Bad → Bad) → Bad`. -/
/-- con-leche: none — the `Bad` block. -/
private def badBlock : List ConstantInfo :=
  [ .indInfo ⟨nm "Bad", [], ty1⟩ {},
    .ctorInfo ⟨nm2 "Bad" "mk", [], pi (pi (c0 (nm "Bad")) (c0 (nm "Bad"))) (c0 (nm "Bad"))⟩ 0 1,
    .recInfo ⟨nm2 "Bad" "rec", [nm "u"],
      pi (pi (c0 (nm "Bad")) (sortP "u"))
        (pi (pi (pi (c0 (nm "Bad")) (c0 (nm "Bad"))) (ap (bv 1) (ap (c0 (nm2 "Bad" "mk")) (bv 0))))
          (pi (c0 (nm "Bad")) (ap (bv 2) (bv 0))))⟩ 2 2
      [rl (nm2 "Bad" "mk") 1] ]

#guard !accepts [.indDecl badBlock 0]
#guard chk [.indDecl badBlock 0]

/- A duplicate constructor name. -/
/-- con-leche: none — `N` with both constructors under one name. -/
private def dupBlock : List ConstantInfo :=
  nBlock.map fun ci => match ci with
    | .ctorInfo cv nP 1 => .ctorInfo { cv with name := nm2 "N" "zero" } nP 1
    | c => c

#guard !accepts [.indDecl dupBlock 0]
#guard chk [.indDecl dupBlock 0]

/- A block the recogniser does not read (no recursor): the formers are
checked, then a positive decline. -/
#guard !accepts [.indDecl (nBlock.take 3) 0]
#guard chk [.indDecl (nBlock.take 3) 0]

/- A recursor whose type is not the generated one (`N.rec` with its minors
swapped). -/
/-- con-leche: none — `N` with a wrong recursor type. -/
private def wrongRecBlock : List ConstantInfo :=
  nBlock.map fun ci => match ci with
    | .recInfo cv mI rP rules => .recInfo { cv with type := truRecTy } mI rP rules
    | c => c

#guard !accepts [.indDecl wrongRecBlock 0]
#guard chk [.indDecl wrongRecBlock 0]

/- A member re-declaring a stored name. -/
#guard !accepts [.indDecl nBlock 0, .indDecl nBlock 0]
#guard chk [.indDecl nBlock 0, .indDecl nBlock 0]

end ConRon.Arena.InductivesTest
