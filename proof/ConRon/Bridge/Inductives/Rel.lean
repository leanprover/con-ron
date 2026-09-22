/-
# `ConRon.Bridge.Inductives.Rel` — the inductive tier's vocabulary

DESIGN §8.2's **Theorem 1** at `Arena/Inductives.lean` and the ten modules
under it (task #97d-2's twins of `ConLeche/Kernel/Inductives/*`).  This module
holds what every statement of the tier is phrased with — the two frames, the
two statement shapes, and the denotation relations for the tier's own record
types — so that `Bridge/Inductives/{StructParts,SumParts,NativeParts,
StructInstall,SumInstall,NativeInstall,Modeled}.lean` are statements and
proofs and nothing else.

## The two frames, and why there are two

Task #97-P3-0 §2's rule for the `ExprOps` tier — "`StateOK s` is `StoreWF
s.store` and nothing else, the only clause the tier mentions" — applies to
**two thirds of this tier**: `structFam`, `structPsAt`, `structRecTyR`,
`nativeCtors4` and their ~70 siblings intern nodes and read the store and do
nothing else.  Their frame is `PStep`: the store grows, the caches and the pin
table stand still, and `CheckOK.mono` lifts the whole invariant across them
whenever a caller needs it.

The other third calls the knot (`inferTypeCore`, `isDefEqCore`, `whnf`,
`annotateCore` through `Arena/CheckerBase.lean`), so it flushes and fills the
per-declaration caches.  Its frame is `Bridge/Checker/Hyp.lean`'s `CoreStep`,
already stated there for exactly this reason, and its statements take
`CheckOK` rather than `StateOK`.

`PStep.toCore` is the one-line bridge between them.

## The two statement shapes

Rather than write the statement out at ~110 declarations, the tier has
two combinators — `PSpec` for the pure grade and `CSpec` for the core grade —
each taking the ANSWER RELATION as a parameter, exactly as
`Bridge/Rel.lean`'s `RelE` family is generic in the pure function (task
#97-P3-0 §2: "five shapes for the whole tier where the spike's monomorphic
`Inst1At` would need one copy of its 822-line layer per walk").

    PSpec P c R  :  ∀ s₀ s' r, StateOK s₀ → P s₀.store →
                    c s₀ = .ok (r, s') → PStep s₀ s' ∧ R s'.store r

`P` is the PRECONDITION — "these argument handles denote these `Expr`s" — and
it is a predicate on the store rather than a hypothesis of the theorem for the
reason `Bridge/Core/Knot.lean`'s `BodySpec` makes `denoteE s₀.store i = some e`
a parameter: the statement quantifies over the initial state, so anything said
about that state's store has to travel inside.

The answer relation is an `EStore → α → Prop` and the ten the tier uses are
the `R…` abbreviations below.  A `Bool`- or `Nat`-valued twin uses `RV`, which
mentions no store — task #97-P3-0 §5's finding 1, "the cheapest group is the
one with no target store".

## The record relations

`InductiveShape`, `NativeParts`, `StructParts`, `IIndCaps` and the three ctor
lists are twinned records whose fields are handles; each gets a `…Rel`
structure saying every field denotes, with an `ext` transport beside it.
These are the tier's own instance of `Bridge/Rel.lean`'s ten
declaration-layer transports and they are what the install routes' statements
name.
-/
import ConRon.Bridge.Checker.Hyp

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ## The pure frame -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — **the frame of the tier's
PURE grade**: the store grows (and with it the binder-datum store), the
fourteen per-declaration caches and the pin table stand still.  The memo
tables are NOT framed: every rebuilding walk of `Arena/ExprOps.lean` writes
its own, and task #97-P3-0 §7's "per-call memo FRAME" is the item that would
say which. -/
structure PStep (s s' : AState) : Prop where
  ok : StateOK s'
  ext : Ext s.store s'.store
  bm : BMExt s.store s'.store
  caches : s'.caches = s.caches
  pins : s'.pins = s.pins

theorem PStep.refl {s : AState} (h : StateOK s) : PStep s s :=
  ⟨h, Ext.refl _, BMExt.refl _, rfl, rfl⟩

theorem PStep.trans {a b c : AState} (h₁ : PStep a b) (h₂ : PStep b c) :
    PStep a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, h₁.bm.trans h₂.bm,
    by rw [h₂.caches, h₁.caches], by rw [h₂.pins, h₁.pins]⟩

/-- con-leche: none — **the bridge between the two grades**: a pure step
preserves the whole checking invariant, by `Bridge/StateOK.lean`'s
`CheckOK.mono`.  This is what lets a core-grade function call a pure-grade one
and keep its own hypothesis. -/
theorem PStep.toCore {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    (h : PStep s s') (hc : CheckOK μ env fe s) : CoreStep μ env fe s s' :=
  ⟨hc.mono h.ok h.ext h.caches h.pins, h.ext, h.pins⟩

/-! ## The two statement shapes -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — **the PURE grade's
statement**: from a well-formed store, an ACCEPTING run of the twin returns an
answer related to the pure side's by `R`, having only grown the arena.

Partial correctness, as everywhere in this library: a (B) function may fail
and Theorem 1 claims nothing then — which is why the hypothesis is
`c s0 = .ok (r, s')` and not an unconditional equation.

**RUN form rather than a `Std.Do` triple**, and the reason is task
#97-P3-Checker §1's: this tier's work is composition, inversion and list
induction rather than verification conditions, and `Bridge/Checker/Fold.lean`
— the module that consumes `IndSpec` — is already written in run form
(`AM.bind_ok` is its only inversion).  A leaf walk proved with `mvcgen` in
task #97-P3-0's idiom reaches this shape by reading its triple at the `.ok`
branch; `Bridge/Inductives/Decl.lean`'s note says what that costs. -/
def PSpec {α : Type} (P : EStore → Prop) (c : AM α) (R : EStore → α → Prop) :
    Prop :=
  ∀ (s₀ s' : AState) (r : α), StateOK s₀ → P s₀.store → c s₀ = .ok (r, s') →
    PStep s₀ s' ∧ R s'.store r

/-- con-leche: none — the empty precondition, for a twin whose arguments are
all `Nat`s. -/
abbrev PT : EStore → Prop := fun _ => True

/-- con-leche: ConLeche/Verify/Cached/SimC.lean:366 SimC — **the CORE grade's
statement**: the same at a function that calls the knot, so the invariant is
`CheckOK` and the frame is `CoreStep`.  The pure side's fuel existential lives
inside `R`, as `Bridge/Core/Knot.lean`'s `SimE` has it. -/
def CSpec (μ : CheckMode) (env : Env) (fe : IFEnv) {α : Type}
    (P : EStore → Prop) (c : AM α) (R : EStore → α → Prop) : Prop :=
  ∀ (s₀ s' : AState) (r : α), CheckOK μ env fe s₀ → P s₀.store →
    c s₀ = .ok (r, s') → CoreStep μ env fe s₀ s' ∧ R s'.store r

/-- con-leche: none — a pure-grade twin is a core-grade twin at any
environment.  The one lemma that lets `Modeled.lean`'s core-grade bodies quote
`StructParts.lean`'s pure-grade lemmas without restating them. -/
theorem PSpec.toCSpec {α : Type} {P : EStore → Prop} {c : AM α}
    {R : EStore → α → Prop} (h : PSpec P c R) (μ : CheckMode) (env : Env)
    (fe : IFEnv) : CSpec μ env fe P c R := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hstep, hr⟩ := h s₀ s' r hok.state hp hrun
  exact ⟨hstep.toCore hok, hr⟩

/-! ### The `Option` lift

An `Option`-valued twin (`structPartsCore?`, `nativeParts?`, `replacePisPw`,
`structProjBodies`, …) needs its answer relation lifted through `Option`, and
the lift must say `none ↔ none`: a twin that answers `none` where con-leche
answers `some` would send the DISPATCH into the other route.  That is
`checkIndDecl`'s own soundness obligation and it is why this is a two-sided
relation rather than a one-sided implication. -/

/-- con-leche: none — an answer relation lifted through `Option`, both
directions. -/
def ROp {α β : Type} (R : β → EStore → α → Prop) (x : Option β) :
    EStore → Option α → Prop
  | _, none => x = none
  | st, some a => ∃ b, x = some b ∧ R b st a


/-! ## The answer relations

Ten shapes, one per result type the tier's ~110 twins answer with.  Each is an
`abbrev` so that `PSpec`'s `R` is transparent to `grind` at the call site
(task #97-P3-0 §4's rule 3 and §5's finding 1). -/

/-- an expression handle denotes a given `Expr`. -/
abbrev RE (v : Expr) : EStore → EIdx → Prop := fun st r => denoteE st r = some v
/-- a level handle denotes a given `Level`. -/
abbrev RL (u : Level) : EStore → LIdx → Prop := fun st r => denoteL st.ls r = some u
/-- a level-LIST handle denotes a given `List Level`. -/
abbrev RLs (us : List Level) : EStore → LsIdx → Prop :=
  fun st r => denoteLs st.lss r = some us
/-- a name handle denotes a given `Name`. -/
abbrev RN (n : ConLeche.Name) : EStore → NIdx → Prop :=
  fun st r => denoteN st.ns r = some n
/-- a LIST of expression handles denotes a given `List Expr`. -/
abbrev REL (vs : List Expr) : EStore → List EIdx → Prop :=
  fun st r => Frontend.denoteEList st r = some vs
/-- an ARRAY of expression handles denotes a given `Array Expr`. -/
abbrev REA (vs : Array Expr) : EStore → Array EIdx → Prop :=
  fun st r => Frontend.denoteEArray st r = some vs
/-- a LIST of level handles denotes a given `List Level`. -/
abbrev RLL (us : List Level) : EStore → List LIdx → Prop :=
  fun st r => denoteLList st.ls r = some us
/-- an `Option` expression handle denotes a given `Option Expr`. -/
abbrev REO (v : Option Expr) : EStore → Option EIdx → Prop :=
  fun st r => denoteEO st r = some v
/-- a stored constant's header denotes a given `ConstantVal`. -/
abbrev RCV (c : ConstantVal) : EStore → IConstantVal → Prop :=
  fun st r => Frontend.denoteCV st r = some c
/-- a representation-free answer (`Bool`, `Nat`, `List Nat`, `Unit`, …): NO
target store, task #97-P3-0 §5's finding 1. -/
abbrev RV {α : Type} (x : α) : EStore → α → Prop := fun _ r => r = x

/-! ## The binder telescope

`List (EIdx × BinderMeta)` is the shape `piBinders`, `structTeleAt`,
`normFieldDoms` and `whnfTelescope` answer with, and `Bridge/Rel.lean` has no
relation for it because the `ExprOps` tier never returns one. -/

/-- con-leche: none — a binder telescope denotes, domain by domain; the
`BinderMeta` datum is carried VERBATIM (it is representation-free: `BinderMeta`
is con-leche's own type, DESIGN §8.7's import rule). -/
def denoteBinders (st : EStore) :
    List (EIdx × BinderMeta) → Option (List (Expr × BinderMeta))
  | [] => some []
  | (t, m) :: bs =>
    match denoteE st t, denoteBinders st bs with
    | some x, some xs => some ((x, m) :: xs)
    | _, _ => none

/-- a binder telescope denotes a given one. -/
abbrev RB (bs : List (Expr × BinderMeta)) :
    EStore → List (EIdx × BinderMeta) → Prop :=
  fun st r => denoteBinders st r = some bs

theorem denoteBinders_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (bs : List (EIdx × BinderMeta)) (xs : List (Expr × BinderMeta)),
      denoteBinders st bs = some xs → denoteBinders st' bs = some xs := by
  intro bs
  induction bs with
  | nil => intro xs h; exact h
  | cons a as ih =>
    intro xs h
    obtain ⟨t, m⟩ := a
    simp only [denoteBinders] at h ⊢
    cases ht : denoteE st t with
    | none => rw [ht] at h; simp at h
    | some x =>
      cases has : denoteBinders st as with
      | none => rw [ht, has] at h; simp at h
      | some ys =>
        rw [ht, has] at h
        rw [denote_ext ht hx, ih ys has]
        exact h

/-! ## The constructor lists

`List (IConstantVal × Nat)` is `InductiveShape.ctors`; `List (IConstantVal ×
Nat × Nat)` is what `sumSplit` answers; `List (NIdx × Nat × EIdx × List Nat)`
is `nativeCtors4`'s, the four-tuple the generated recursor is built from. -/

/-- con-leche: none — the shape record's constructor list denotes. -/
def denoteCtors (st : EStore) :
    List (IConstantVal × Nat) → Option (List (ConstantVal × Nat))
  | [] => some []
  | (cv, n) :: cs =>
    match Frontend.denoteCV st cv, denoteCtors st cs with
    | some c, some rest => some ((c, n) :: rest)
    | _, _ => none

/-- con-leche: none — `sumSplit`'s constructor list denotes. -/
def denoteCtors3 (st : EStore) :
    List (IConstantVal × Nat × Nat) → Option (List (ConstantVal × Nat × Nat))
  | [] => some []
  | (cv, a, b) :: cs =>
    match Frontend.denoteCV st cv, denoteCtors3 st cs with
    | some c, some rest => some ((c, a, b) :: rest)
    | _, _ => none

/-- con-leche: none — `nativeCtors4`'s four-tuple list denotes. -/
def denoteCtors4 (st : EStore) :
    List (NIdx × Nat × EIdx × List Nat) →
      Option (List (ConLeche.Name × Nat × Expr × List Nat))
  | [] => some []
  | (n, k, ty, idx) :: cs =>
    match denoteN st.ns n, denoteE st ty, denoteCtors4 st cs with
    | some nm, some t, some rest => some ((nm, k, t, idx) :: rest)
    | _, _, _ => none

abbrev RCs (cs : List (ConstantVal × Nat)) :
    EStore → List (IConstantVal × Nat) → Prop :=
  fun st r => denoteCtors st r = some cs
abbrev RCs3 (cs : List (ConstantVal × Nat × Nat)) :
    EStore → List (IConstantVal × Nat × Nat) → Prop :=
  fun st r => denoteCtors3 st r = some cs
abbrev RCs4 (cs : List (ConLeche.Name × Nat × Expr × List Nat)) :
    EStore → List (NIdx × Nat × EIdx × List Nat) → Prop :=
  fun st r => denoteCtors4 st r = some cs

theorem denoteCtors_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (cs : List (IConstantVal × Nat)) (xs : List (ConstantVal × Nat)),
      denoteCtors st cs = some xs → denoteCtors st' cs = some xs := by
  intro cs
  induction cs with
  | nil => intro xs h; exact h
  | cons a as ih =>
    intro xs h
    obtain ⟨cv, n⟩ := a
    simp only [denoteCtors] at h ⊢
    cases hc : Frontend.denoteCV st cv with
    | none => rw [hc] at h; simp at h
    | some c =>
      cases has : denoteCtors st as with
      | none => rw [hc, has] at h; simp at h
      | some ys =>
        rw [hc, has] at h
        rw [denoteCV_ext hc hx, ih ys has]
        exact h

/-- con-leche: none — a list of level LISTS denotes: the fields' sorts, one
list per constructor (`checkSumCtors`' second answer). -/
def denoteLLists (st : EStore) : List (List LIdx) → Option (List (List Level))
  | [] => some []
  | l :: ls =>
    match denoteLList st.ls l, denoteLLists st ls with
    | some x, some xs => some (x :: xs)
    | _, _ => none

abbrev RLLL (us : List (List Level)) : EStore → List (List LIdx) → Prop :=
  fun st r => denoteLLists st r = some us

/-! ## The field kinds

`RecFieldKind` is TWINNED, not imported (task #97d-2's deviation 7), so the
tier needs the five-clause translation. -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:44-56 RecFieldKind
The twin's five constructors are con-leche's five, in order. -/
def kindOf : Arena.RecFieldKind → ConLeche.RecFieldKind
  | .ordinary => .ordinary
  | .recursive => .recursive
  | .reflexive => .reflexive
  | .negative => .negative
  | .unsupported => .unsupported

abbrev RK (k : ConLeche.RecFieldKind) : EStore → Arena.RecFieldKind → Prop :=
  fun _ r => kindOf r = k
abbrev RKs (ks : List ConLeche.RecFieldKind) : EStore → List Arena.RecFieldKind → Prop :=
  fun _ r => r.map kindOf = ks
abbrev RKss (ks : List (List ConLeche.RecFieldKind)) :
    EStore → List (List Arena.RecFieldKind) → Prop :=
  fun _ r => r.map (·.map kindOf) = ks

/-! ## The capability record -/

/-- con-leche: ConLeche/Kernel/Env.lean:352-372 IndCaps — the capability
record denotes: one name handle and seven representation-free fields.
`Frontend.denoteCaps` is the frontend tier's own readback of the same record,
and this is it as a RELATION so that a spec can name the pure value. -/
abbrev RCaps (c : IndCaps) : EStore → IIndCaps → Prop :=
  fun st r => Frontend.denoteCaps st r = some c

/-! ## `InductiveShape` -/

/-- con-leche: ConLeche/Kernel/Inductives/SumParts.lean:78-101 InductiveShape
The shape record denotes, field by field. -/
structure ShapeRel (st : EStore) (p : Arena.InductiveShape)
    (q : ConLeche.InductiveShape) : Prop where
  cvT : Frontend.denoteCV st p.cvT = some q.cvT
  ctors : denoteCtors st p.ctors = some q.ctors
  nP : p.nP = q.nP
  nIdx : p.nIdx = q.nIdx
  cvR : Frontend.denoteCV st p.cvR = some q.cvR
  elim : denoteN st.ns p.elim = some q.elim
  resSort : denoteL st.ls p.resSort = some q.resSort
  rhss : Frontend.denoteEList st p.rhss = some q.rhss
  large : p.large = q.large
  isProp : p.isProp = q.isProp

abbrev RShape (q : ConLeche.InductiveShape) :
    EStore → Arena.InductiveShape → Prop := fun st p => ShapeRel st p q

theorem ShapeRel.ext {st st' : EStore} {p : Arena.InductiveShape}
    {q : ConLeche.InductiveShape} (h : ShapeRel st p q) (hx : Ext st st') :
    ShapeRel st' p q where
  cvT := denoteCV_ext h.cvT hx
  ctors := denoteCtors_ext hx _ _ h.ctors
  nP := h.nP
  nIdx := h.nIdx
  cvR := denoteCV_ext h.cvR hx
  elim := hx.lss.ls.ns _ _ h.elim
  resSort := denoteL_ext h.resSort hx
  rhss := denoteEList_ext hx _ _ h.rhss
  large := h.large
  isProp := h.isProp

/-! ## `NativeParts` -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:177-192 NativeParts
The recognised direct-recursive block's record denotes: the shape, the field
kinds and the structural-pin bit. -/
structure PartsRel (st : EStore) (p : Arena.NativeParts)
    (q : ConLeche.NativeParts) : Prop where
  shape : ShapeRel st p.toInductiveShape q.toInductiveShape
  kinds : p.kinds.map (·.map kindOf) = q.kinds
  recPinned : p.recPinned = q.recPinned

abbrev RParts (q : ConLeche.NativeParts) : EStore → Arena.NativeParts → Prop :=
  fun st p => PartsRel st p q

theorem PartsRel.ext {st st' : EStore} {p : Arena.NativeParts}
    {q : ConLeche.NativeParts} (h : PartsRel st p q) (hx : Ext st st') :
    PartsRel st' p q :=
  ⟨h.shape.ext hx, h.kinds, h.recPinned⟩

/-! ## `StructParts` -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:213-244 StructParts
The recognised simple-structure block's record denotes, field by field. -/
structure SPartsRel (st : EStore) (p : Arena.StructParts)
    (q : ConLeche.StructParts) : Prop where
  cvT : Frontend.denoteCV st p.cvT = some q.cvT
  cvC : Frontend.denoteCV st p.cvC = some q.cvC
  nP : p.nP = q.nP
  nF : p.nF = q.nF
  cvR : Frontend.denoteCV st p.cvR = some q.cvR
  elim : denoteN st.ns p.elim = some q.elim
  resSort : denoteL st.ls p.resSort = some q.resSort
  rhs : denoteE st p.rhs = some q.rhs
  large : p.large = q.large
  isProp : p.isProp = q.isProp

abbrev RSParts (q : ConLeche.StructParts) :
    EStore → Arena.StructParts → Prop := fun st p => SPartsRel st p q

/-! ## The `AM` bind's inversion

`Bridge/Checker/Fold.lean` has this lemma under the name `AM.bind_ok`, and
this tier cannot import it: `Bridge/Checker/Decl.lean` will import
`Bridge/Inductives/Decl.lean` to discharge its `.indDecl` arm, so an import
the other way would close a cycle.  Six lines, restated, with the citation
that says where its twin lives. -/

/-- con-leche: none — the `AM` bind's inversion: an accepting composite is two
accepting halves.  `Bridge/Checker/Fold.lean`'s `AM.bind_ok`, restated here
for the reason the section note gives. -/
theorem bindOk {α β : Type} {x : AM α} {f : α → AM β} {s s' : AState}
    {b : β} (h : (x >>= f) s = .ok (b, s')) :
    ∃ a s₁, x s = .ok (a, s₁) ∧ f a s₁ = .ok (b, s') := by
  have h' : ((x s) >>= (fun p => f p.1 p.2)) = .ok (b, s') := h
  clear h
  revert h'
  cases hx : x s with
  | error e => intro h; exact nomatch h
  | ok p =>
    obtain ⟨a, s₁⟩ := p
    intro h
    exact ⟨a, s₁, rfl, h⟩

/-! ## Two transports the spec layer does not have

`Bridge/Rel.lean` stops at `denoteCI_ext`; `Bridge/Checker/Inv.lean` has the
`…_pext` twins at the WEAKER extension but not the plain `Ext` ones for the
list and the environment.  This tier needs both, because every install
function grows the arena while the environment it was handed stands still. -/

/-- con-leche: none — a constant LIST survives an append. -/
theorem denoteCIList_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (cs : List IConstantInfo) (xs : List ConstantInfo),
      Frontend.denoteCIList st cs = some xs →
        Frontend.denoteCIList st' cs = some xs := by
  intro cs
  induction cs with
  | nil => intro xs h; exact h
  | cons a as ih =>
    intro xs h
    simp only [Frontend.denoteCIList] at h ⊢
    cases ha : Frontend.denoteCI st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteCIList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteCI_ext ha hx, ih ys has]
        exact h

/-- con-leche: none — **the environment survives an append**, which is what
every install theorem of this tier needs of its own argument. -/
theorem denoteFEnv_ext {st st' : EStore} (hx : Ext st st') {fe : IFEnv}
    {env : Env} (h : denoteFEnv st fe = some env) :
    denoteFEnv st' fe = some env := by
  simp only [denoteFEnv, denoteIEnv, Option.map_eq_some_iff] at h ⊢
  obtain ⟨xs, hxs, he⟩ := h
  exact ⟨xs, denoteCIList_ext hx _ xs hxs, he⟩

/-! ## The environment's own relation

An install route's argument and answer are `IFEnv`s, and the pure side's are
`Env`s; `Bridge/Promote/Exact.lean`'s `denoteFEnv` is the function that
relates them and `Bridge/Checker/Inv.lean`'s `FoldOK` is where it is carried.
`IndOut` is what an install route CONCLUDES, and it is
`Bridge/Checker/Decl.lean`'s `DeclOut` with the run at the route rather than
at `checkDecl`. -/

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**an INSTALL function's answer relation**: the new index is still its list's
index, it only pushed, its visibility bound only rose, and it denotes an
environment con-leche's own install produces.

Every install twin of this tier (`checkStructProjTable`, `checkSumInd`,
`checkNativeTable`, `checkIndMember`, `checkProjFn`, `installProjFnStep`, the
two routes) answers an `IFEnv`, and this is the one relation all of them use;
`IndOut` below is `InstRel` plus what the STATE did, and
`Bridge/Inductives/Decl.lean` assembles the two. -/
structure InstRel (fe : IFEnv) (P : Env → Prop) (st : EStore) (fe' : IFEnv) :
    Prop where
  coh : IFEnvCoh fe'
  pushed : Pushed fe fe'
  visible : fe.visibleBelow ≤ fe'.visibleBelow
  denote : ∃ env', denoteFEnv st fe' = some env' ∧ P env'

/-- con-leche: none — `InstRel` composes along a chain of installs: the
environment relations chain by `Pushed.trans`, and the pure side's runs are
chained by the caller (each install's `P` names its own con-leche function). -/
theorem InstRel.trans {fe₀ fe₁ fe₂ : IFEnv} {P₁ P₂ : Env → Prop}
    {st₁ st₂ : EStore} (h₁ : InstRel fe₀ P₁ st₁ fe₁)
    (h₂ : InstRel fe₁ P₂ st₂ fe₂) : InstRel fe₀ P₂ st₂ fe₂ where
  coh := h₂.coh
  pushed := h₁.pushed.trans h₂.pushed
  visible := Nat.le_trans h₁.visible h₂.visible
  denote := h₂.denote

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**what an inductive install route leaves behind**.  Seven clauses, and the
correspondence with `DeclOut` is one-for-one except that the `run` clause is
abstracted: `Bridge/Inductives/Decl.lean` instantiates it at
`ConLeche.checkDecl … (.indDecl b nP)` and the two route theorems at their own
con-leche function.

**`visible` is here and not in `DeclOut`**, because `IndSpec`
(`Bridge/Checker/Hyp.lean`) asks for it: `Arena/Checker.lean`'s promotion
counter is read off `visibleBelow`, so the step needs to know the route only
moved it up. -/
structure IndOut (fe fe' : IFEnv) (s s' : AState) (run : Env → Prop) : Prop where
  state : StateOK s'
  ext : Ext s.store s'.store
  pins : s'.pins = s.pins
  coh : IFEnvCoh fe'
  pushed : Pushed fe fe'
  visible : fe.visibleBelow ≤ fe'.visibleBelow
  denote : ∃ env', denoteFEnv s'.store fe' = some env' ∧ run env'

end ConRon.Bridge.Inductives
