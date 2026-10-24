/-
# `ConRon.Bridge.Checker.Decl` — what each of `checkDecl`'s seven arms concludes

`Arena/Checker.lean`'s `checkDecl` is a seven-way match, with one bridge
theorem per arm, all with the same conclusion (`DeclOut` below).
`Bridge/Checker/Fold.lean`'s `Arena.checkDecl_bridge` is then `cases pd` and
nothing else, which is what keeps the per-declaration theorem — the one DESIGN
§8.2 states — free of arm-specific hypotheses.

## What an arm concludes, and what it deliberately does not

`DeclOut` has eight clauses; the sixth is §8.2's:

    ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
      ConLeche.checkDecl μ (fueledOps μ F) pinsP env d = .ok env'

The five before it are the plumbing the FOLD needs and the arm is the only
place that can supply: the store invariant survives, the arena only grew, the
pin table is untouched, the index is still its list's index, and **the step
only pushed** (`Pushed`, `Bridge/Promote/Exact.lean`) — which is what makes
`checkDeclStep`'s promotion counter `k` mean "the constants this step
installed".  The two after it are what the
bracket's close needs of the pushed index and only the arm can supply: the
environment it denotes is well formed (`envWF`), and every projection table it
holds is either an old one or well shaped (`proj`).

There is **no persistence clause**: `checkDecl` does not promote.  The
environment it hands back names scratch handles, and it is `promoteNew`'s job
— one level up, in `checkDeclStep` — to make it persistent before
`dropScratch`.  Writing `PersIFEnv` into `DeclOut` would be stating a
falsehood about the very deviation DESIGN `### Task #97-P6-2` describes.

## The pins

`pins : List INatOpPinSet` on the arena side and `pinsP : List NatOpPinSet` on
con-leche's are related by `PinsDenote`, interned once by `internAllPins`
before the fold starts (`Bridge/Checker/Pins.lean`).  They are a PARAMETER of
`checkDecl` on both sides and no arm changes them, so the relation is a
standing hypothesis of every theorem here.

## Where the arms are

The seven arm theorems are in `Bridge/Checker/Arms.lean`, because proving
them needs `Bridge/Checker/Base.lean`, `DeclVal.lean` and `Basis.lean`, all
three of which import THIS module for `DeclOut` and `PinsDenote`.  What each
arm needs:

| arm | what it needs |
|---|---|
| `defn` | `checkConstantVal` + `checkDefnVal` + the two `Nat`-pin gates |
| `thm` / `opaque` | `checkConstantVal` + the value check; `opaque` also the `reduce*` pin gate |
| `axiom` | `Bridge/Checker/Canon.lean`'s `canonEq` and the four standard/trust shape tests |
| `basis` | `Bridge/Checker/Basis.lean`'s `checkBasisDecl` |
| `ind` | **nothing here** — it is `IndSpec`, the named hypothesis |
| `quot` | `quotPinHit`'s exactness |

Every one of them bottoms out in `checkConstantVal_bridge`
(`Bridge/Checker/Base.lean`), which bottoms out in `KnotSpec`.
-/
import ConRon.Bridge.Checker.Hyp

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The interned pin variants denote -/

/-- con-leche: ConLeche/Kernel/NatOpPinSet.lean:35-68 NatOpPinSet — an
interned type-pin list denotes con-leche's, pair by pair and in order. -/
def TypePinsDenote (st : EStore) :
    List (NIdx × EIdx) → List (ConLeche.Name × Expr) → Prop
  | [], [] => True
  | p :: ps, q :: qs =>
    denoteN st.ns p.1 = some q.1 ∧ denoteE st p.2 = some q.2 ∧ TypePinsDenote st ps qs
  | _, _ => False

/-- con-leche: none — a type-pin list's denotation transports across an
append. -/
theorem TypePinsDenote.mono {st st' : EStore} (hx : Ext st st') :
    ∀ ps qs, TypePinsDenote st ps qs → TypePinsDenote st' ps qs
  | [], [], _ => trivial
  | _ :: ps, _ :: qs, ⟨h1, h2, h3⟩ =>
    ⟨denoteN_ext h1 hx, denote_ext h2 hx, TypePinsDenote.mono hx ps qs h3⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- con-leche: ConLeche/Kernel/NatOpPinSet.lean:35-68 NatOpPinSet — one
interned pin variant denotes con-leche's: the toolchain string is carried
verbatim, each of the sixteen terms denotes its counterpart and each of the
eight type-pin lists its own. -/
structure PinSetDenote (st : EStore) (p : INatOpPinSet) (q : NatOpPinSet) :
    Prop where
  toolchain : p.toolchain = q.toolchain
  divPin : denoteE st p.divPin = some q.divPin
  modPin : denoteE st p.modPin = some q.modPin
  gcdPin : denoteE st p.gcdPin = some q.gcdPin
  landPin : denoteE st p.landPin = some q.landPin
  lorPin : denoteE st p.lorPin = some q.lorPin
  xorPin : denoteE st p.xorPin = some q.xorPin
  shiftLeftPin : denoteE st p.shiftLeftPin = some q.shiftLeftPin
  shiftRightPin : denoteE st p.shiftRightPin = some q.shiftRightPin
  divProofs : Frontend.denoteEList st p.divProofs = some q.divProofs
  modProofs : Frontend.denoteEList st p.modProofs = some q.modProofs
  gcdProofs : Frontend.denoteEList st p.gcdProofs = some q.gcdProofs
  landProofs : Frontend.denoteEList st p.landProofs = some q.landProofs
  lorProofs : Frontend.denoteEList st p.lorProofs = some q.lorProofs
  xorProofs : Frontend.denoteEList st p.xorProofs = some q.xorProofs
  shiftLeftProofs : Frontend.denoteEList st p.shiftLeftProofs
    = some q.shiftLeftProofs
  shiftRightProofs : Frontend.denoteEList st p.shiftRightProofs
    = some q.shiftRightProofs
  divTypePins : TypePinsDenote st p.divTypePins q.divTypePins
  modTypePins : TypePinsDenote st p.modTypePins q.modTypePins
  gcdTypePins : TypePinsDenote st p.gcdTypePins q.gcdTypePins
  landTypePins : TypePinsDenote st p.landTypePins q.landTypePins
  lorTypePins : TypePinsDenote st p.lorTypePins q.lorTypePins
  xorTypePins : TypePinsDenote st p.xorTypePins q.xorTypePins
  shiftLeftTypePins : TypePinsDenote st p.shiftLeftTypePins q.shiftLeftTypePins
  shiftRightTypePins : TypePinsDenote st p.shiftRightTypePins q.shiftRightTypePins

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _ — the interned pin LIST
denotes con-leche's, variant by variant and in order (the order is the order
the install gate tries them, so it is part of the statement). -/
def PinsDenote (st : EStore) : List INatOpPinSet → List NatOpPinSet → Prop
  | [], [] => True
  | p :: ps, q :: qs => PinSetDenote st p q ∧ PinsDenote st ps qs
  | _, _ => False

/-- con-leche: none — the pin list's denotation transports across an
append. -/
theorem PinsDenote.mono {st st' : EStore} (hx : Ext st st') :
    ∀ ps qs, PinsDenote st ps qs → PinsDenote st' ps qs := by
  intro ps
  induction ps with
  | nil => intro qs h; cases qs <;> exact h
  | cons a as ih =>
    intro qs h
    cases qs with
    | nil => exact h
    | cons b bs =>
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ih bs h2⟩
      exact {
        toolchain := h1.toolchain
        divPin := hx.expr _ _ h1.divPin
        modPin := hx.expr _ _ h1.modPin
        gcdPin := hx.expr _ _ h1.gcdPin
        landPin := hx.expr _ _ h1.landPin
        lorPin := hx.expr _ _ h1.lorPin
        xorPin := hx.expr _ _ h1.xorPin
        shiftLeftPin := hx.expr _ _ h1.shiftLeftPin
        shiftRightPin := hx.expr _ _ h1.shiftRightPin
        divProofs := denoteEList_ext hx _ _ h1.divProofs
        modProofs := denoteEList_ext hx _ _ h1.modProofs
        gcdProofs := denoteEList_ext hx _ _ h1.gcdProofs
        landProofs := denoteEList_ext hx _ _ h1.landProofs
        lorProofs := denoteEList_ext hx _ _ h1.lorProofs
        xorProofs := denoteEList_ext hx _ _ h1.xorProofs
        shiftLeftProofs := denoteEList_ext hx _ _ h1.shiftLeftProofs
        shiftRightProofs := denoteEList_ext hx _ _ h1.shiftRightProofs
        divTypePins := TypePinsDenote.mono hx _ _ h1.divTypePins
        modTypePins := TypePinsDenote.mono hx _ _ h1.modTypePins
        gcdTypePins := TypePinsDenote.mono hx _ _ h1.gcdTypePins
        landTypePins := TypePinsDenote.mono hx _ _ h1.landTypePins
        lorTypePins := TypePinsDenote.mono hx _ _ h1.lorTypePins
        xorTypePins := TypePinsDenote.mono hx _ _ h1.xorTypePins
        shiftLeftTypePins := TypePinsDenote.mono hx _ _ h1.shiftLeftTypePins
        shiftRightTypePins := TypePinsDenote.mono hx _ _ h1.shiftRightTypePins }

/-! ## What an arm concludes -/

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**the per-declaration bridge's conclusion**, at one `checkDecl` call.
DESIGN §8.2's statement is the sixth clause; the other seven are what the
fold needs and only the arm can supply.

`Ext` and not `PExt` here, deliberately: `checkDecl` appends and never drops,
so the TOTAL extension holds, and `checkDeclStep` is where it weakens
(`Bridge/Promote/Pers.lean`). -/
structure DeclOut (μ : CheckMode) (pinsP : List NatOpPinSet) (env : Env)
    (d : Declaration) (s : AState) (fe fe' : IFEnv) (s' : AState) : Prop where
  state : StateOK s'
  ext : Ext s.store s'.store
  pins : s'.pins = s.pins
  coh : IFEnvCoh fe'
  pushed : Pushed fe fe'
  run : ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env'
  /-- **the pushed environment is well formed**: what the bracket's close needs
  (`Bridge/Checker/Split.lean`'s `BodyOut.envWF`) and only the arm can
  supply.  Stated at every denotation, which `run` makes the one. -/
  envWF : ∀ env', denoteFEnv s'.store fe' = some env' → EnvWF env'
  /-- the step only pushed tables onto the table list (what makes the
  promotion's `kt` mean the step's tables) -/
  tpushed : TPushed fe fe'
  /-- **the pushed index's projection tables**: every table the index now
  holds is one it held before, or is well shaped — `IFEnvOK.tblHit`'s shape
  clause, over membership (the shape `IFEnvOK_of_denote` takes) and relative to
  the step (the shape `Bridge/Inductives/Rel.lean`'s `ProjOut` has), so that no
  arm needs the incoming tables' shape. -/
  proj : ∀ t ∈ fe'.env.tables, t ∈ fe.env.tables ∨ IProjTableOK t

/-- con-leche: none — `DeclOut`'s first six clauses and "no table installed",
which every arm off the inductive route assembles by the same transcription;
the last three clauses are derived from them once, in
`Bridge/Checker/Arms.lean`'s `DeclCore.out`. -/
structure DeclCore (μ : CheckMode) (pinsP : List NatOpPinSet) (env : Env)
    (d : Declaration) (s : AState) (fe fe' : IFEnv) (s' : AState) : Prop where
  state : StateOK s'
  ext : Ext s.store s'.store
  pins : s'.pins = s.pins
  coh : IFEnvCoh fe'
  pushed : Pushed fe fe'
  run : ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env'
  /-- no table installed: the arms off the inductive route push constants
  only -/
  tables : fe'.env.tables = fe.env.tables

end ConRon.Bridge
