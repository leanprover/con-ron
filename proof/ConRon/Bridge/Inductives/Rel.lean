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
nothing else.  Their frame is `PStep`: the store grows, the pin table stands
still, the caches stand still up to the two tables a level comparison may
write, and `CheckOK.monoF` lifts the whole invariant across them whenever a
caller needs it.

The other third calls the knot (`inferTypeCore`, `isDefEqCore`, `whnf`,
`annotateCore` through `Arena/CheckerBase.lean`), so it flushes and fills the
per-declaration caches.  Its frame is `Bridge/Checker/Hyp.lean`'s `CoreStep`,
already stated there for exactly this reason, and its statements take
`CheckOK` rather than `StateOK`.

`PStep.toCore` is the one-line bridge between them.

**FINDING (task #97-P3-Ind round 2): `lvlEq?` is a CACHED call, and four
statements of this tier had it at a frame that stands still.**
`Arena/Core.lean`'s `lvlEq?` is a cached verdict walk: it probes
`caches.lvlEqC`, and on a miss it reads both handles back through
`readLevelM` (which writes `caches.readLC`) and records the verdict (which
writes `caches.lvlEqC`).  So a twin that calls it moves TWO of the fourteen
per-declaration cache tables, and round 1's `caches : s'.caches = s.caches`
was **false of it** — not hard to prove, false.

**RULING (task #97-P3-Frame): the STATEMENT was wrong, not the code.**  The
Rust does exactly what the twin does — `core.rs`'s `lvl_eq` probes, then on a
miss calls `read_level_m` twice and `lvl_eq_set`, and all three call sites
(`sum_parts.rs:170`, `struct_parts.rs:832`, `native_parts.rs:2129`) are
`zero_level` then `core::lvl_eq` — so changing the Lean twin to match
con-leche's uncached `Level.isEquiv (← readLevel s) .zero` would CREATE a
layer-B/layer-C divergence, and `Refine2/AbsState.lean`'s `CachesRel` relates
the two tables pointwise.  `PStep`'s cache clause is therefore
`Bridge/StateOK.lean`'s `CacheFrame`: the record equation that names the two
tables allowed to move, plus their invariants as IMPLICATIONS — exactly the
shape `Bridge/Specs.lean`'s three readback specs and
`Bridge/Core/Walks/Frame.lean`'s `ReadbackFrame` already carry.
`PStep.of_caches` is the constructor for the ~107 twins that move nothing.

Three twins of this tier call `lvlEq?` — `InductiveShape.withSort`
(`SumParts.lean:62`), `structPartsCore?` (`StructParts.lean:289`) and
`nativeShape?` (`NativeParts.lean:505`), the last of which `nativeParts?`
calls — and round 1 stated all four at `PSpec`.  They are `CSpec`, and task
#97-P3-Frame LEFT THEM THERE even though the corrected `PStep` makes their
FRAME provable at `StateOK` (`Core.lvlEq?_frame`,
`Bridge/Core/Walks/Cached.lean`, closed).  The frame was never what forced
them up: their ANSWER is what forces them up.  `withSort`'s `isProp` field is
the verdict `lvlEq?` returns, and a `lvlEqC` row is only the right verdict
because `LvlEqCacheOK` says so — an invariant `StateOK` does not carry.  At
`PSpec` a poisoned cache would make the twin answer a record the statement
claims is `ConLeche.InductiveShape.withSort`'s, and it is not.  `CSpec` is not
a weakening for convenience here; it is the grade the ANSWER lives at.

Every consumer inside this tier has `CheckOK` where it needs them
(`checkIndDecl_bridge` through `FoldOK.check`, `checkSumInd_spec` by its own
grade), so the correction costs the tier nothing.  Outside it,
`Bridge/Frontend/ProjRec.lean`'s `projRecOwners_run` calls `structPartsCore?`
AND `nativeParts?` (`Arena/Frontend/ProjRec.lean:510-515`) and concludes
`ParseStep` at `StateOK`.  Its frame is now true there — `lvlEq?_frame` needs
no cache-content hypothesis — and its answer conjunct survives because
neither recogniser's `isSome` depends on the verdict: `isProp` fills a FIELD
of a record that is already `some`.

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
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.ExprOps.Spine
import ConRon.Bridge.ExprOps.Ranges
import ConRon.Bridge.ExprOps.Subst

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ## The pure frame -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — **the frame of the tier's
PURE grade**: the store grows (and with it the binder-datum store), the pin
table stands still, and the fourteen per-declaration caches stand still up to
`readLC` and `lvlEqC` — the two a `lvlEq?` call may write (task #97-P3-Frame;
`Bridge/StateOK.lean`'s `CacheFrame` is the clause, and `PStep.of_caches` is
what a twin that writes neither uses).  The memo tables are NOT framed: every
rebuilding walk of `Arena/ExprOps.lean` writes its own, and task #97-P3-0 §7's
"per-call memo FRAME" is the item that would say which. -/
structure PStep (s s' : AState) : Prop where
  ok : StateOK s'
  ext : Ext s.store s'.store
  bm : BMExt s.store s'.store
  cframe : CacheFrame s s'
  pins : s'.pins = s.pins

theorem PStep.refl {s : AState} (h : StateOK s) : PStep s s :=
  ⟨h, Ext.refl _, BMExt.refl _, CacheFrame.refl _, rfl⟩

theorem PStep.trans {a b c : AState} (h₁ : PStep a b) (h₂ : PStep b c) :
    PStep a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, h₁.bm.trans h₂.bm,
    h₁.cframe.trans h₂.cframe, by rw [h₂.pins, h₁.pins]⟩

/-- con-leche: none — the frame of a twin that writes no per-declaration
table at all, which is what all but three of the tier's ~110 twins do.  The
shape a proof reaches when it has the plain cache equation in hand. -/
theorem PStep.of_caches {s s' : AState} (hok : StateOK s')
    (hx : Ext s.store s'.store) (hbm : BMExt s.store s'.store)
    (hc : s'.caches = s.caches) (hp : s'.pins = s.pins) : PStep s s' :=
  ⟨hok, hx, hbm, CacheFrame.of_eq hc hx, hp⟩

/-- con-leche: none — **the bridge between the two grades**: a pure step
preserves the whole checking invariant, by `Bridge/StateOK.lean`'s
`CheckOK.mono`.  This is what lets a core-grade function call a pure-grade one
and keep its own hypothesis. -/
theorem PStep.toCore {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    (h : PStep s s') (hc : CheckOK μ env fe s) : CoreStep μ env fe s s' :=
  ⟨hc.monoF h.ok h.ext h.cframe h.pins, h.ext, h.pins⟩

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

/-- con-leche: none — **the PURE grade AT A PIN READ** (task #97-P3-Ind round
3's finding; see `Bridge/Inductives/StructParts.lean`'s `structProjGuards_spec`).

`PSpec`'s precondition is a predicate on the STORE, so it cannot see the pin
table — and `Arena/Pins.lean`'s `pinsReady` tests only that the name array has
`pinCount` entries, not that any of the three nullary slots denotes what it
claims.  A twin that reads `zeroLevel`, `sortOne` or `emptyLevels` therefore
has no `PSpec`: at a state whose `pins.zeroLevel` denotes `.param foo` the
run ACCEPTS and answers something else.  `PinsOK` is the missing licence, and
this is the only shape that carries it while keeping `PStep`: the twin is
still pure — it interns and reads, it calls no knot — so dropping to `CSpec`
(the other statement that has `PinsOK`, through `CheckOK`) would give away the
`BMExt` and cache-frame conjuncts for nothing. -/
def PSpecP {α : Type} (P : EStore → Prop) (c : AM α) (R : EStore → α → Prop) :
    Prop :=
  ∀ (s₀ s' : AState) (r : α), StateOK s₀ → PinsOK s₀ → P s₀.store →
    c s₀ = .ok (r, s') → PStep s₀ s' ∧ R s'.store r

/-- con-leche: none — a twin that does NOT read the pin table has the
stronger statement, and every consumer may use it at the weaker one. -/
theorem PSpec.toPSpecP {α : Type} {P : EStore → Prop} {c : AM α}
    {R : EStore → α → Prop} (h : PSpec P c R) : PSpecP P c R :=
  fun s₀ s' r hok _ hp hrun => h s₀ s' r hok hp hrun


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

/-- con-leche: none — and a pin-reading pure twin is a core-grade twin at any
environment: `CheckOK.pins` is exactly what it was missing. -/
theorem PSpecP.toCSpec {α : Type} {P : EStore → Prop} {c : AM α}
    {R : EStore → α → Prop} (h : PSpecP P c R) (μ : CheckMode) (env : Env)
    (fe : IFEnv) : CSpec μ env fe P c R := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hstep, hr⟩ := h s₀ s' r hok.state hok.pins hp hrun
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

/-- con-leche: none — a denoting constructor list has con-leche's length. -/
theorem denoteCtors_length {st : EStore} :
    ∀ (cs : List (IConstantVal × Nat)) (xs : List (ConstantVal × Nat)),
      denoteCtors st cs = some xs → cs.length = xs.length := by
  intro cs
  induction cs with
  | nil => intro xs h; simp only [denoteCtors] at h; cases h; rfl
  | cons a as ih =>
    intro xs h
    obtain ⟨cv, n⟩ := a
    simp only [denoteCtors] at h
    cases hc : Frontend.denoteCV st cv with
    | none => rw [hc] at h; simp at h
    | some c =>
      cases has : denoteCtors st as with
      | none => rw [hc, has] at h; simp at h
      | some ys =>
        rw [hc, has] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [ih ys has]

/-- con-leche: none — a three-tuple constructor list's denotation keeps its
length; `nativeCounts?` compares `cs.length` against the recursor's claimed
prefix. -/
theorem denoteCtors3_length {st : EStore} :
    ∀ {cs : List (IConstantVal × Nat × Nat)}
      {csP : List (ConstantVal × Nat × Nat)},
      denoteCtors3 st cs = some csP → cs.length = csP.length := by
  intro cs
  induction cs with
  | nil => intro csP h; simp only [denoteCtors3, Option.some.injEq] at h; simp [← h]
  | cons a as ih =>
    intro csP h
    obtain ⟨cv, x, y⟩ := a
    simp only [denoteCtors3] at h
    cases hcv : Frontend.denoteCV st cv with
    | none => rw [hcv] at h; simp at h
    | some c =>
      cases has : denoteCtors3 st as with
      | none => rw [hcv, has] at h; simp at h
      | some rest =>
        rw [hcv, has] at h
        obtain rfl := Option.some.inj h
        simp only [List.length_cons, ih has]

/-- con-leche: none — a denoting rule list has con-leche's length. -/
theorem denoteRules_length {st : EStore} :
    ∀ {rs : List IRecRule} {rsP : List RecRule},
      Frontend.denoteRules st rs = some rsP → rs.length = rsP.length := by
  intro rs
  induction rs with
  | nil =>
    intro rsP h
    simp only [Frontend.denoteRules, Option.some.injEq] at h; simp [← h]
  | cons a as ih =>
    intro rsP h
    simp only [Frontend.denoteRules] at h
    cases hr : Frontend.denoteRule st a with
    | none => rw [hr] at h; simp at h
    | some x =>
      cases has : Frontend.denoteRules st as with
      | none => rw [hr, has] at h; simp at h
      | some xs =>
        rw [hr, has] at h
        obtain rfl := Option.some.inj h
        simp only [List.length_cons, ih has]

/-- con-leche: none — a denoting rule list reads AT AN INDEX with the
`Option` carried, both ways: `nativeRecPinOk` pairs the recursor's rules with
the block's constructors position by position and answers `false` as soon as
either runs out. -/
theorem denoteRules_getElem? {st : EStore} :
    ∀ {rs : List IRecRule} {rsP : List RecRule},
      Frontend.denoteRules st rs = some rsP → ∀ (j : Nat),
        (∀ rl, rs[j]? = some rl →
          ∃ x, rsP[j]? = some x ∧ Frontend.denoteRule st rl = some x) ∧
        (rs[j]? = none → rsP[j]? = none) := by
  intro rs
  induction rs with
  | nil =>
    intro rsP h j
    simp only [Frontend.denoteRules, Option.some.injEq] at h
    subst h
    exact ⟨by intro rl hrl; simp at hrl, by intro _; simp⟩
  | cons a as ih =>
    intro rsP h j
    simp only [Frontend.denoteRules] at h
    cases hr : Frontend.denoteRule st a with
    | none => rw [hr] at h; simp at h
    | some y =>
      cases has : Frontend.denoteRules st as with
      | none => rw [hr, has] at h; simp at h
      | some ys =>
        rw [hr, has] at h
        obtain rfl := Option.some.inj h
        cases j with
        | zero =>
          refine ⟨?_, ?_⟩
          · intro rl hrl
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hrl
            subst hrl
            exact ⟨y, by simp, hr⟩
          · intro hb; simp at hb
        | succ j =>
          obtain ⟨hA, hB⟩ := ih has j
          refine ⟨?_, ?_⟩
          · intro rl hrl
            simp only [List.getElem?_cons_succ] at hrl
            obtain ⟨x, hx, hd⟩ := hA rl hrl
            exact ⟨x, by simpa using hx, hd⟩
          · intro hb
            simp only [List.getElem?_cons_succ] at hb ⊢
            exact hB hb

/-- con-leche: none — the same for a three-tuple constructor list. -/
theorem denoteCtors3_getElem? {st : EStore} :
    ∀ {cs : List (IConstantVal × Nat × Nat)}
      {csP : List (ConstantVal × Nat × Nat)},
      denoteCtors3 st cs = some csP → ∀ (j : Nat),
        (∀ cv a b, cs[j]? = some (cv, a, b) →
          ∃ c, csP[j]? = some (c, a, b) ∧ Frontend.denoteCV st cv = some c) ∧
        (cs[j]? = none → csP[j]? = none) := by
  intro cs
  induction cs with
  | nil =>
    intro csP h j
    simp only [denoteCtors3, Option.some.injEq] at h
    subst h
    exact ⟨by intro cv a b hb; simp at hb, by intro _; simp⟩
  | cons e es ih =>
    intro csP h j
    obtain ⟨cv, x, y⟩ := e
    simp only [denoteCtors3] at h
    cases hcv : Frontend.denoteCV st cv with
    | none => rw [hcv] at h; simp at h
    | some c =>
      cases has : denoteCtors3 st es with
      | none => rw [hcv, has] at h; simp at h
      | some rest =>
        rw [hcv, has] at h
        obtain rfl := Option.some.inj h
        cases j with
        | zero =>
          refine ⟨?_, ?_⟩
          · intro cv' a b hb
            simp only [List.getElem?_cons_zero, Option.some.injEq,
              Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl, rfl⟩ := hb
            exact ⟨c, by simp, hcv⟩
          · intro hb; simp at hb
        | succ j =>
          obtain ⟨hA, hB⟩ := ih has j
          refine ⟨?_, ?_⟩
          · intro cv' a b hb
            simp only [List.getElem?_cons_succ] at hb
            obtain ⟨c', hc', hd⟩ := hA cv' a b hb
            exact ⟨c', by simpa using hc', hd⟩
          · intro hb
            simp only [List.getElem?_cons_succ] at hb ⊢
            exact hB hb

/-- con-leche: none — a denoting rule's CONSTRUCTOR handle denotes the pure
rule's constructor name, and its field count travels verbatim. -/
theorem denoteRule_ctor {st : EStore} {rl : IRecRule} {x : RecRule}
    (h : Frontend.denoteRule st rl = some x) :
    denoteN st.ns rl.ctor = some x.ctor ∧ rl.nfields = x.nfields := by
  simp only [Frontend.denoteRule] at h
  cases hc : denoteN st.ns rl.ctor with
  | none => rw [hc] at h; simp at h
  | some c =>
    cases hf : Frontend.denoteFire st rl.fire with
    | none => rw [hc, hf] at h; simp at h
    | some f =>
      cases he : denoteE st rl.rhs with
      | none => rw [hc, hf, he] at h; simp at h
      | some e =>
        rw [hc, hf, he] at h
        obtain rfl := Option.some.inj h
        exact ⟨rfl, rfl⟩

/-- con-leche: none — `denoteCI` preserves the constant's KIND at the
inductive tag too, for the recogniser's `| _ => false` arm (see
`denoteCI_not_ctor`). -/
theorem denoteCI_not_ind {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c)
    (hne : ∀ v caps, ci ≠ .indInfo v caps) :
    ∀ v caps, c ≠ .indInfo v caps := by
  cases ci <;>
    simp_all [Frontend.denoteCI, Option.map_eq_some_iff] <;> grind

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

/-- con-leche: none — the `AM` `pure`'s inversion, the other half of
`bindOk`: an accepting `pure` moved nothing and answered what it was given.
Every `do` block of the tier ends in one. -/
theorem pureOk {α : Type} {a r : α} {s s' : AState}
    (h : (pure a : AM α) s = .ok (r, s')) : r = a ∧ s' = s := by
  have h' : Except.ok ((a, s) : α × AState) = .ok (r, s') := h
  injection h' with h''
  injection h'' with h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- con-leche: none — **the `do`-elaborator's `if`, lifted out of the bind**.
`Arena/Inductives/StructParts.lean`'s `structShape` writes `let want ← if
large then internLNode (.param elim) else internLNode .zero`, and the
elaborator answers by DUPLICATING everything after it into both arms — the
minor premise and the major domain included.  This equation puts the `if` back
where the source wrote it, so the continuation is inverted once. -/
theorem am_if_bind {α β : Type} {c : Prop} [Decidable c] (x y : AM α)
    (k : α → AM β) :
    (if c then (x >>= k) else (y >>= k)) = ((if c then x else y) >>= k) := by
  split <;> rfl

/-! ## The primitives, in RUN form

`Bridge/Specs.lean` states one `@[spec]` triple per `Monad.lean` primitive,
and this tier is written in RUN form (the module note above says why: its work
is composition and `bind` inversion, not verification conditions).  So every
leaf proof here would otherwise begin with the same `AM.of_run` and the same
seven-way `obtain` over the frame equations — at some two hundred call sites.

The primitives the generators actually use get their run form ONCE, here,
each packaging the frame as a `PStep` and keeping only the conjunct its
callers read.  A proof downstream is then `bindOk` plus one of these plus the
answer's own algebra, which is what task #97-P3-0 §4's rule 3 asks of a
statement layer. -/

/-- con-leche: none — a FAILING primitive cannot have accepted.  The other
half of `pureOk`, for the fuel-exhaustion clause every walk of the tier
opens with. -/
theorem failOk {α : Type} {e : Arena.CheckError} {r : α} {s s' : AState}
    (h : (fail e : AM α) s = .ok (r, s')) : False := by
  simp only [Arena.fail, throwThe, MonadExceptOf.throw] at h
  exact nomatch h

/-- con-leche: none — **`view`, as a run**: it moves nothing and answers the
store's own decoding.  The first line of every walk of this tier. -/
theorem view_run {s s' : AState} {h : EIdx} {v : ENodeView}
    (hrun : view h s = .ok (v, s')) : s' = s ∧ s.store.view h = some v :=
  AM.of_run (P := fun t => t = s) rfl hrun (view_spec s h)

/-- con-leche: none — **`viewLs`, as a run**: `view_run` at the level-list
store.  `eqApp3?` reads a `const` node's universe arguments through it. -/
theorem viewLs_run {s s' : AState} {u : LsIdx} {v : List LIdx}
    (hrun : viewLs u s = .ok (v, s')) :
    s' = s ∧ s.store.lss.view u = some v :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewLs_spec s u)

/-- con-leche: none — a level-list handle's denotation, read through its
view. -/
theorem denoteLs_of_view {st : EStore} {u : LsIdx} {v : List LIdx}
    {ls : List Level} (hv : st.lss.view u = some v)
    (hd : denoteLs st.lss u = some ls) : denoteLList st.ls v = some ls := by
  have h : denoteLList st.lss.ls v = some ls := by
    simpa only [denoteLs, hv] using hd
  exact h

/-- con-leche: none — a level-handle list that denotes denotes at each
element. -/
theorem denoteLList_mem {st : LStore} :
    ∀ {us : List LIdx} {xs : List Level}, denoteLList st us = some xs →
      ∀ {c : LIdx}, c ∈ us → ∃ u, denoteL st c = some u := by
  intro us
  induction us with
  | nil => intro xs _ c hc; exact absurd hc (by simp)
  | cons u us ih =>
    intro xs h c hc
    simp only [denoteLList, opt2] at h
    cases hu : denoteL st u with
    | none => rw [hu] at h; simp at h
    | some y =>
      cases hus : denoteLList st us with
      | none => rw [hu, hus] at h; simp at h
      | some ys =>
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact ⟨y, hu⟩
        · exact ih hus hc'

/-- con-leche: none — a universe-argument list handle that denotes has a
view. -/
theorem lsview_isSome_of_denote {st : LsStore} {c : LsIdx} {us : List Level}
    (hd : denoteLs st c = some us) : (st.view c).isSome = true := by
  obtain ⟨v, hv, _⟩ := denoteLs_view hd
  rw [hv]; rfl

/-- con-leche: none — `EStore.viewBM` reads only `pers`, `scr` and
`scratchOn`, so a primitive that leaves those three alone leaves the whole
binder-datum store alone.  The three NESTED interners (name, level, level
list) are exactly that. -/
theorem bmExt_of_nested {st st' : EStore} (hp : st'.pers = st.pers)
    (hs : st'.scr = st.scr) (hon : st'.scratchOn = st.scratchOn) :
    BMExt st st' := by
  intro mi m h
  simp only [EStore.viewBM, EStore.persGetBM, hp, hs, hon]
  exact h

/-- con-leche: none — **`internE`, as a run**: the arena grew, nothing else
moved, and the new handle denotes what the node view says. -/
theorem internE_run {s s' : AState} {w : ENodeView} {h : EIdx}
    (hok : StateOK s) (hv : s.store.ViewOK w)
    (hrun : internE w s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = denoteEView s'.store w := by
  obtain ⟨h1, h2, h3, _h4, _h4b, _h5, h6, h7, _h8, h9⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internE_spec s w hok.wf hv)
  exact ⟨PStep.of_caches ⟨h1⟩ h2 h3 h6 h7, h9⟩

/-- con-leche: none — `internE` at a `.bvar`: no precondition at all. -/
theorem internBVarE_run {s s' : AState} {i : Nat} {h : EIdx} (hok : StateOK s)
    (hrun : internE (.bvar i) s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.bvar i) :=
  internE_run hok viewOK_bvar hrun

/-- con-leche: none — `internE` at a `.sort`. -/
theorem internSortE_run {s s' : AState} {u : LIdx} {uP : Level} {h : EIdx}
    (hok : StateOK s) (hu : denoteL s.store.ls u = some uP)
    (hrun : internE (.sort u) s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.sort uP) := by
  obtain ⟨hstep, hd⟩ :=
    internE_run hok (viewOK_sort (lview_isSome_of_denote hu)) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteEView, denoteL_ext hu hstep.ext, Option.map_some]

/-- con-leche: none — `internE` at a `.const`: the head of every family and
every spine this tier builds. -/
theorem internConstE_run {s s' : AState} {n : NIdx} {nm : ConLeche.Name}
    {us : LsIdx} {usP : List Level} {h : EIdx} (hok : StateOK s)
    (hn : denoteN s.store.ns n = some nm)
    (hus : denoteLs s.store.lss us = some usP)
    (hrun : internE (.const n us) s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.const nm usP) := by
  obtain ⟨hstep, hd⟩ :=
    internE_run hok (viewOK_const (nview_isSome_of_denote hn)
      (lsview_isSome_of_denote hus)) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteEView, denoteN_ext hn hstep.ext, denoteLs_ext hus hstep.ext,
    opt2]

/-- con-leche: none — `internE` at a `.proj`: `structProjArgP`'s node. -/
theorem internProjE_run {s s' : AState} {n : NIdx} {nm : ConLeche.Name}
    {i : Nat} {e : EIdx} {eP : Expr} {h : EIdx} (hok : StateOK s)
    (hn : denoteN s.store.ns n = some nm) (he : denoteE s.store e = some eP)
    (hrun : internE (.proj n i e) s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.proj nm i eP) := by
  obtain ⟨hstep, hd⟩ :=
    internE_run hok (viewOK_proj (nview_isSome_of_denote hn)
      (by rw [he]; rfl)) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteEView, denoteN_ext hn hstep.ext, denote_ext he hstep.ext,
    opt2]

/-- con-leche: none — `internE` at an `.app`: `structShape`'s two assembled
right-hand sides (`bvar 2 (bvar 0)` and the minor premise's body). -/
theorem internAppE_run {s s' : AState} {f a : EIdx} {fP aP : Expr} {h : EIdx}
    (hok : StateOK s) (hf : denoteE s.store f = some fP)
    (ha : denoteE s.store a = some aP)
    (hrun : internE (.app f a) s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.app fP aP) := by
  obtain ⟨hstep, hd⟩ :=
    internE_run hok (viewOK_app (by rw [hf]; rfl) (by rw [ha]; rfl)) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteEView, denote_ext hf hstep.ext, denote_ext ha hstep.ext,
    opt2]

/-- con-leche: none — `internE` at a binder whose datum is a VALUE
(`replacePisPw`, `pisToLamsPw` and the recursor generators build their binders
this way, not through the datum-handle face). -/
theorem internForallEE_run {s s' : AState} {ty b : EIdx} {tyP bP : Expr}
    {m : BinderMeta} {h : EIdx} (hok : StateOK s)
    (hty : denoteE s.store ty = some tyP) (hb : denoteE s.store b = some bP)
    (hrun : internE (.forallE ty b m) s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.forallE tyP bP m) := by
  obtain ⟨hstep, hd⟩ :=
    internE_run hok (viewOK_forallE (by rw [hty]; rfl) (by rw [hb]; rfl)) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteEView, denote_ext hty hstep.ext, denote_ext hb hstep.ext,
    opt2]

/-- con-leche: none — the same at a `.lam`. -/
theorem internLamE_run {s s' : AState} {ty b : EIdx} {tyP bP : Expr}
    {m : BinderMeta} {h : EIdx} (hok : StateOK s)
    (hty : denoteE s.store ty = some tyP) (hb : denoteE s.store b = some bP)
    (hrun : internE (.lam ty b m) s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.lam tyP bP m) := by
  obtain ⟨hstep, hd⟩ :=
    internE_run hok (viewOK_lam (by rw [hty]; rfl) (by rw [hb]; rfl)) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteEView, denote_ext hty hstep.ext, denote_ext hb hstep.ext,
    opt2]

/-- con-leche: none — **`internLNode`, as a run**.  The nested stores keep
`pers`/`scr`/`scratchOn`, so `BMExt` is `bmExt_of_nested`. -/
theorem internLNode_run {s s' : AState} {v : LNodeView} {h : LIdx}
    (hok : StateOK s) (hv : s.store.ls.ViewOK v)
    (hrun : internLNode v s = .ok (h, s')) :
    PStep s s' ∧ denoteL s'.store.ls h = denoteLView s'.store.ls v := by
  obtain ⟨h1, h2, h3, h4, h5, _h6, h7, h8, _h9, h10⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLNode_spec s v hok.wf hv)
  exact ⟨PStep.of_caches ⟨h1⟩ h2 (bmExt_of_nested h3 h4 h5) h7 h8, h10⟩

/-- con-leche: none — `internLNode` at `.zero`: `structElimLevel`'s small
arm. -/
theorem internZeroL_run {s s' : AState} {h : LIdx} (hok : StateOK s)
    (hrun : internLNode .zero s = .ok (h, s')) :
    PStep s s' ∧ denoteL s'.store.ls h = some .zero :=
  internLNode_run hok ⟨by simp [LNodeView.lchildren],
    by simp [LNodeView.nchildren]⟩ hrun

/-- con-leche: none — `internLNode` at a `.param`: `paramLevels`' element and
`structElimLevel`'s large arm. -/
theorem internParamL_run {s s' : AState} {n : NIdx} {nm : ConLeche.Name}
    {h : LIdx} (hok : StateOK s) (hn : denoteN s.store.ns n = some nm)
    (hrun : internLNode (.param n) s = .ok (h, s')) :
    PStep s s' ∧ denoteL s'.store.ls h = some (.param nm) := by
  obtain ⟨hstep, hd⟩ :=
    internLNode_run hok ⟨by simp [LNodeView.lchildren],
      by intro c hc
         simp only [LNodeView.nchildren] at hc
         rcases List.mem_singleton.mp hc with rfl
         exact nview_isSome_of_denote hn⟩ hrun
  refine ⟨hstep, ?_⟩
  have hx : denoteN s'.store.ls.ns n = some nm := denoteN_ext hn hstep.ext
  rw [hd]
  show Option.map Level.param (denoteN s'.store.ls.ns n) = some (Level.param nm)
  rw [hx]
  rfl

/-- con-leche: none — `internLNode` at a `.max`: `structProjGuards`' fold
step, and the one level node of this tier with two children. -/
theorem internMaxL_run {s s' : AState} {a b : LIdx} {aP bP : Level} {h : LIdx}
    (hok : StateOK s) (ha : denoteL s.store.ls a = some aP)
    (hb : denoteL s.store.ls b = some bP)
    (hrun : internLNode (.max a b) s = .ok (h, s')) :
    PStep s s' ∧ denoteL s'.store.ls h = some (.max aP bP) := by
  obtain ⟨hstep, hd⟩ :=
    internLNode_run hok
      ⟨by intro c hc
          simp only [LNodeView.lchildren, List.mem_cons] at hc
          rcases hc with rfl | rfl | hc
          · exact lview_isSome_of_denote ha
          · exact lview_isSome_of_denote hb
          · exact absurd hc (by simp),
       by simp [LNodeView.nchildren]⟩ hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteLView, denoteL_ext ha hstep.ext, denoteL_ext hb hstep.ext,
    opt2]

/-- con-leche: none — **a handle comparison IS a name comparison**, as an
equation between `Bool`s: `Bridge/Checker/Base.lean`'s `beq_handle_iff` read
at both signs (restated here rather than imported: that module is not in this
tier's closure), which is the shape a walk that RETURNS the comparison needs
(`mentionsConstGo`'s `.const` and `.proj` arms).  The `false` half is
`denoteN_inj` — DESIGN §8.3's soundness obligation. -/
theorem beq_handle_eq {st : EStore} (hwf : StoreWF st) {n p : NIdx}
    {nm x : ConLeche.Name} (hn : denoteN st.ns n = some nm)
    (hp : denoteN st.ns p = some x) : (n == p) = (nm == x) := by
  obtain ⟨rk, hrk⟩ := hwf
  cases hb : n == p with
  | true =>
    obtain rfl := eq_of_beq hb
    rw [hn] at hp
    obtain rfl := Option.some.inj hp
    simp
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro heq
    subst heq
    have hne : (n == p) = true := beq_iff_eq.mpr (denoteN_inj hrk.nsWF hn hp)
    rw [hb] at hne
    exact absurd hne (by simp)

/-- con-leche: none — `beq_handle_eq` with the pure side FLIPPED, which is
the shape `Arena/Inductives/Modeled.lean`'s `renameBy` needs: its lookup
compares `tbl.1 == n` where con-leche's rename compares `n` against the name
the entry stands for. -/
theorem beq_handle_eq' {st : EStore} (hwf : StoreWF st) {n p : NIdx}
    {nm x : ConLeche.Name} (hn : denoteN st.ns n = some nm)
    (hp : denoteN st.ns p = some x) : (n == p) = (x == nm) := by
  rw [beq_handle_eq hwf hn hp]
  cases h : (nm == x) with
  | true => obtain rfl := eq_of_beq h; simp
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro hc
    subst hc
    simp at h

/-- con-leche: none — **an EXPRESSION-handle comparison is a structural
comparison**, at both signs.  The `false` half is `denoteE_inj`
(`Arena/WFProofs.lean`) — DESIGN §8.3's soundness obligation, which the two
recognisers cash at every `==`. -/
theorem beq_ehandle_eq {st : EStore} (hwf : StoreWF st) {a b : EIdx}
    {x y : Expr} (ha : denoteE st a = some x) (hb : denoteE st b = some y) :
    (a == b) = (x == y) := by
  cases h1 : a == b with
  | true =>
    obtain rfl := eq_of_beq h1
    rw [ha] at hb
    obtain rfl := Option.some.inj hb
    simp
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro heq
    subst heq
    have hne : (a == b) = true := beq_iff_eq.mpr (denoteE_inj hwf ha hb)
    rw [h1] at hne
    exact absurd hne (by simp)

/-- con-leche: none — **a LEVEL-handle comparison is a structural comparison**,
at both signs: `beq_ehandle_eq` one store down.  The `false` half is
`denoteL_inj` (`Arena/WFProofs.lean`).  `structShape`'s motive branch is the
first consumer — it compares the motive codomain's level handle against the
`Sort elim` / `Prop` it interned, where con-leche compares `Level`s. -/
theorem beq_lhandle_eq {st : EStore} (hwf : StoreWF st) {a b : LIdx}
    {x y : Level} (ha : denoteL st.ls a = some x)
    (hb : denoteL st.ls b = some y) : (a == b) = (x == y) := by
  obtain ⟨rk, hrk⟩ := hwf
  cases h1 : a == b with
  | true =>
    obtain rfl := eq_of_beq h1
    rw [ha] at hb
    obtain rfl := Option.some.inj hb
    simp
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro heq
    subst heq
    have hne : (a == b) = true := beq_iff_eq.mpr (denoteL_inj hrk.lsWF ha hb)
    rw [h1] at hne
    exact absurd hne (by simp)

/-- con-leche: none — `denoteE_inj` at a LIST: two handle lists that denote
the same terms ARE the same list. -/
theorem denoteEList_inj {st : EStore} (hwf : StoreWF st) :
    ∀ {as bs : List EIdx} {xs : List Expr},
      Frontend.denoteEList st as = some xs →
      Frontend.denoteEList st bs = some xs → as = bs := by
  intro as
  induction as with
  | nil =>
    intro bs xs ha hb
    simp only [Frontend.denoteEList] at ha
    obtain rfl := Option.some.inj ha
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [Frontend.denoteEList] at hb
      split at hb
      · exact absurd hb (by simp)
      · exact absurd hb (by simp)
  | cons a as ih =>
    intro bs xs ha hb
    simp only [Frontend.denoteEList] at ha
    cases hx : denoteE st a with
    | none => rw [hx] at ha; simp at ha
    | some y =>
      cases hxs : Frontend.denoteEList st as with
      | none => rw [hx, hxs] at ha; simp at ha
      | some ys =>
        rw [hx, hxs] at ha
        obtain rfl := Option.some.inj ha
        cases bs with
        | nil => simp only [Frontend.denoteEList] at hb; exact absurd hb (by simp)
        | cons b bs =>
          simp only [Frontend.denoteEList] at hb
          cases hy : denoteE st b with
          | none => rw [hy] at hb; simp at hb
          | some z =>
            cases hys : Frontend.denoteEList st bs with
            | none => rw [hy, hys] at hb; simp at hb
            | some zs =>
              rw [hy, hys] at hb
              obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj hb)
              rw [denoteE_inj hwf hx hy, ih hxs hys]

/-- con-leche: none — and so a handle-LIST comparison is a structural one. -/
theorem beq_ehandleList_eq {st : EStore} (hwf : StoreWF st)
    {as bs : List EIdx} {xs ys : List Expr}
    (ha : Frontend.denoteEList st as = some xs)
    (hb : Frontend.denoteEList st bs = some ys) : (as == bs) = (xs == ys) := by
  cases h1 : as == bs with
  | true =>
    obtain rfl := eq_of_beq h1
    rw [ha] at hb
    obtain rfl := Option.some.inj hb
    simp
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro heq
    subst heq
    have hne : (as == bs) = true := beq_iff_eq.mpr (denoteEList_inj hwf ha hb)
    rw [h1] at hne
    exact absurd hne (by simp)

/-- con-leche: none — `denoteN_inj` at a LIST: two NAME-handle lists that
denote the same names ARE the same list.  `denoteEList_inj`'s twin, for the
level-parameter lists the recursor's pin compares. -/
theorem denoteNListE_inj {st : EStore} (hwf : StoreWF st) :
    ∀ {as bs : List NIdx} {xs : List ConLeche.Name},
      Frontend.denoteNList st.ns as = some xs →
      Frontend.denoteNList st.ns bs = some xs → as = bs := by
  obtain ⟨rk, hrk⟩ := hwf
  intro as
  induction as with
  | nil =>
    intro bs xs ha hb
    simp only [Frontend.denoteNList] at ha
    obtain rfl := Option.some.inj ha
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [Frontend.denoteNList] at hb
      split at hb
      · exact absurd hb (by simp)
      · exact absurd hb (by simp)
  | cons a as ih =>
    intro bs xs ha hb
    simp only [Frontend.denoteNList] at ha
    cases hx : denoteN st.ns a with
    | none => rw [hx] at ha; simp at ha
    | some y =>
      cases hxs : Frontend.denoteNList st.ns as with
      | none => rw [hx, hxs] at ha; simp at ha
      | some ys =>
        rw [hx, hxs] at ha
        obtain rfl := Option.some.inj ha
        cases bs with
        | nil => simp only [Frontend.denoteNList] at hb; exact absurd hb (by simp)
        | cons b bs =>
          simp only [Frontend.denoteNList] at hb
          cases hy : denoteN st.ns b with
          | none => rw [hy] at hb; simp at hb
          | some z =>
            cases hys : Frontend.denoteNList st.ns bs with
            | none => rw [hy, hys] at hb; simp at hb
            | some zs =>
              rw [hy, hys] at hb
              obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj hb)
              rw [denoteN_inj hrk.nsWF hx hy, ih hxs hys]

/-- con-leche: none — and so a NAME-handle-list comparison is a structural
one, at both signs. -/
theorem beq_nhandleList_eq {st : EStore} (hwf : StoreWF st)
    {as bs : List NIdx} {xs ys : List ConLeche.Name}
    (ha : Frontend.denoteNList st.ns as = some xs)
    (hb : Frontend.denoteNList st.ns bs = some ys) : (as == bs) = (xs == ys) := by
  cases h1 : as == bs with
  | true =>
    obtain rfl := eq_of_beq h1
    rw [ha] at hb
    obtain rfl := Option.some.inj hb
    simp
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro heq
    subst heq
    have hne : (as == bs) = true := beq_iff_eq.mpr (denoteNListE_inj hwf ha hb)
    rw [h1] at hne
    exact absurd hne (by simp)

/-- con-leche: none — a denoting handle list denotes at a PREFIX. -/
theorem denoteEList_take {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr},
      Frontend.denoteEList st hs = some xs → ∀ (n : Nat),
        Frontend.denoteEList st (hs.take n) = some (xs.take n) := by
  intro hs
  induction hs with
  | nil =>
    intro xs h n
    simp only [Frontend.denoteEList] at h
    obtain rfl := Option.some.inj h
    simp [Frontend.denoteEList]
  | cons a as ih =>
    intro xs h n
    simp only [Frontend.denoteEList] at h
    cases hx : denoteE st a with
    | none => rw [hx] at h; simp at h
    | some y =>
      cases hxs : Frontend.denoteEList st as with
      | none => rw [hx, hxs] at h; simp at h
      | some ys =>
        rw [hx, hxs] at h
        obtain rfl := Option.some.inj h
        cases n with
        | zero => simp [Frontend.denoteEList]
        | succ n =>
          simp only [List.take_succ_cons, Frontend.denoteEList, hx, ih hxs n]

/-- con-leche: none — a denoting handle list denotes at a SUFFIX, the other
half of `denoteEList_take`: `structFieldIdxOf` answers `getAppArgs.drop nP`. -/
theorem denoteEList_drop {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr},
      Frontend.denoteEList st hs = some xs → ∀ (n : Nat),
        Frontend.denoteEList st (hs.drop n) = some (xs.drop n) := by
  intro hs
  induction hs with
  | nil =>
    intro xs h n
    simp only [Frontend.denoteEList] at h
    obtain rfl := Option.some.inj h
    simp [Frontend.denoteEList]
  | cons a as ih =>
    intro xs h n
    simp only [Frontend.denoteEList] at h
    cases hx : denoteE st a with
    | none => rw [hx] at h; simp at h
    | some y =>
      cases hxs : Frontend.denoteEList st as with
      | none => rw [hx, hxs] at h; simp at h
      | some ys =>
        rw [hx, hxs] at h
        obtain rfl := Option.some.inj h
        cases n with
        | zero => simp only [List.drop_zero, Frontend.denoteEList, hx, hxs]
        | succ n => simpa only [List.drop_succ_cons] using ih hxs n

/-- con-leche: none — **`denoteBinders` IS `Bridge/ExprOps/Spine.lean`'s
`denoteBL`**: the same definition under two names, written independently by
the two tiers (this one's note says `Bridge/Rel.lean` has no relation for the
shape; the `ExprOps` tier grew one for `stripPis`' answer).  One induction
identifies them, and it is what lets this tier read the BINDERS off
`stripPis` rather than only the residual. -/
theorem denoteBinders_eq_denoteBL {st : EStore} :
    ∀ (bs : List (EIdx × BinderMeta)),
      denoteBinders st bs = ExprOps.denoteBL st bs := by
  intro bs
  induction bs with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨t, m⟩ := a
    simp only [denoteBinders, ExprOps.denoteBL, ih]
    rfl

/-- con-leche: none — `stripPis`' `some` answer, with its BINDER LIST: the
inversion `Bridge/Inductives/StructParts.lean`'s `stripPis_some` stopped short
of, because its three consumers only read the residual.  The two field
readers read the binders. -/
theorem denoteBP_someB {st : EStore} {k : Nat} {cP : Expr}
    {bs : List (EIdx × BinderMeta)} {e : EIdx}
    (h : ExprOps.denoteBP st (some (bs, e)) = some (Expr.stripPis k cP)) :
    ∃ xs x, Expr.stripPis k cP = some (xs, x) ∧
      denoteBinders st bs = some xs ∧ denoteE st e = some x := by
  simp only [ExprOps.denoteBP] at h
  cases hb : ExprOps.denoteBL st bs with
  | none => rw [hb] at h; simp at h
  | some xs =>
    cases he : denoteE st e with
    | none => rw [hb, he] at h; simp at h
    | some x =>
      rw [hb, he] at h
      refine ⟨xs, x, (Option.some.inj h).symm, ?_, ?_⟩
      · rw [denoteBinders_eq_denoteBL]; exact hb
      · first | exact he | rfl

/-! ### `stripPis`, in run form

`Bridge/ExprOps/Spine.lean`'s `stripPis_spec` is CLOSED; this tier's
consumers are the three telescope readers (`structUsedLater`,
`structUsedLaterGo` and, through them, `structProjGuards`) and — since round
5 — `structShape_spec`, which is why these live here rather than in
`StructParts.lean`.  Two inversions of `denoteBP` are the shape the readers
need; `denoteBP_someB` above is the third, for the twins that read the peeled
BINDERS. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis — the run form
at this tier's frame; `stripPis` is read-only, so the state does not move at
all. -/
theorem stripPis_pstep {k : Nat} {s₀ s' : AState} {c : EIdx} {cP : Expr}
    {r : Option (List (EIdx × BinderMeta) × EIdx)} (hok : StateOK s₀)
    (hd : denoteE s₀.store c = some cP)
    (hrun : Arena.stripPis k c s₀ = .ok (r, s')) :
    s' = s₀ ∧ ExprOps.denoteBP s₀.store r = some (Expr.stripPis k cP) := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.stripPis_spec k s₀ c hok (by rw [hd]; rfl))
  exact ⟨h1, h2 cP hd⟩

/-- con-leche: none — a `none` answer is `none` on the pure side too: the
two-sidedness `stripPis`' dispatch needs. -/
theorem stripPis_none {st : EStore} {k : Nat} {cP : Expr}
    (h : ExprOps.denoteBP st none = some (Expr.stripPis k cP)) :
    Expr.stripPis k cP = none := (Option.some.inj h).symm

/-- con-leche: none — and a `some` answer names the pure residual. -/
theorem stripPis_some {st : EStore} {k : Nat} {cP : Expr}
    {bs : List (EIdx × BinderMeta)} {e : EIdx}
    (h : ExprOps.denoteBP st (some (bs, e)) = some (Expr.stripPis k cP)) :
    ∃ xs x, Expr.stripPis k cP = some (xs, x) ∧ denoteE st e = some x := by
  simp only [ExprOps.denoteBP] at h
  cases hb : ExprOps.denoteBL st bs with
  | none => rw [hb] at h; simp at h
  | some xs =>
    cases he : denoteE st e with
    | none => rw [hb, he] at h; simp at h
    | some x =>
      rw [hb, he] at h
      exact ⟨xs, x, (Option.some.inj h).symm, rfl⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean getAppFn — the run form of
`Bridge/ExprOps/Spine.lean`'s closed `getAppFn_spec`. -/
theorem getAppFn_run {fuel : Nat} {s₀ s' : AState} {h r : EIdx} {hP : Expr}
    (hok : StateOK s₀) (hd : denoteE s₀.store h = some hP)
    (hrun : Arena.getAppFn fuel h s₀ = .ok (r, s')) :
    s' = s₀ ∧ denoteE s₀.store r = some hP.getAppFn := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.getAppFn_spec fuel s₀ h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 hP hd⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean getAppArgs — the same for the
argument list. -/
theorem getAppArgs_run {fuel : Nat} {s₀ s' : AState} {h : EIdx}
    {rs : List EIdx} {hP : Expr} (hok : StateOK s₀)
    (hd : denoteE s₀.store h = some hP)
    (hrun : Arena.getAppArgs fuel h s₀ = .ok (rs, s')) :
    s' = s₀ ∧ Frontend.denoteEList s₀.store rs = some hP.getAppArgs := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.getAppArgs_spec fuel s₀ h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 hP hd⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1212-1217 fvarTypeD — the run
form of `Bridge/ExprOps/Spine.lean`'s closed `fvarTypeD_spec`. -/
theorem fvarTypeD_run {s₀ s' : AState} {h r : EIdx} {hP : Expr}
    (hok : StateOK s₀) (hd : denoteE s₀.store h = some hP)
    (hrun : Arena.fvarTypeD h s₀ = .ok (r, s')) :
    s' = s₀ ∧ denoteE s₀.store r = some hP.fvarTypeD := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.fvarTypeD_spec s₀ h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 hP hd⟩

/-- con-leche: none — **the level list reads at an INDEX**, with the fallback
carried through: `structProjGuards`' `sorts.getD j z` against con-leche's
`sorts.getD j .zero`. -/
theorem denoteLList_getD {st : LStore} : ∀ {us : List LIdx} {xs : List Level},
    denoteLList st us = some xs → ∀ {z : LIdx} {zP : Level},
      denoteL st z = some zP → ∀ (j : Nat),
        denoteL st (us.getD j z) = some (xs.getD j zP) := by
  intro us
  induction us with
  | nil =>
    intro xs h z zP hz j
    simp only [denoteLList] at h
    obtain rfl := Option.some.inj h
    simpa using hz
  | cons u us ih =>
    intro xs h z zP hz j
    simp only [denoteLList, opt2] at h
    cases hu : denoteL st u with
    | none => rw [hu] at h; simp at h
    | some y =>
      cases hus : denoteLList st us with
      | none => rw [hu, hus] at h; simp at h
      | some ys =>
        rw [hu, hus] at h
        obtain rfl := Option.some.inj h
        cases j with
        | zero => simpa using hu
        | succ j => simpa using ih hus hz j

/-- con-leche: none — **`zeroLevel`, as a run**: the pin read this tier's
`structProjGuards` and `structPartsCore?` open with, and the reason
`PSpecP` exists. -/
theorem zeroLevel_run {s s' : AState} {u : LIdx} (hp : PinsOK s)
    (hrun : Arena.zeroLevel s = .ok (u, s')) :
    s' = s ∧ denoteL s.store.ls u = some .zero := by
  simp only [Arena.zeroLevel] at hrun
  exact AM.of_run (P := fun t => t = s) rfl hrun (pinZeroLevel_spec s hp)

/-- con-leche: none — **`internLsNode`, as a run**: a universe-argument list
node, which is what `paramLevels` answers. -/
theorem internLsNode_run {s s' : AState} {v : LsNodeView} {vP : List Level}
    {h : LsIdx} (hok : StateOK s) (hv : denoteLList s.store.ls v = some vP)
    (hrun : internLsNode v s = .ok (h, s')) :
    PStep s s' ∧ denoteLs s'.store.lss h = some vP := by
  have hvok : s.store.lss.ViewOK v := by
    intro c hc
    obtain ⟨u, hu⟩ := denoteLList_mem hv hc
    exact lview_isSome_of_denote hu
  obtain ⟨h1, h2, h3, h4, h5, _h6, h7, h8, _h9, h10⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLsNode_spec s v hok.wf hvok)
  have hstep : PStep s s' :=
    PStep.of_caches ⟨h1⟩ h2 (bmExt_of_nested h3 h4 h5) h7 h8
  refine ⟨hstep, ?_⟩
  rw [h10]
  exact denoteLList_ext hstep.ext.lss.ls _ _ hv

/-- con-leche: none — **`internNNode`, as a run**. -/
theorem internNNode_run {s s' : AState} {v : NNodeView} {h : NIdx}
    (hok : StateOK s) (hv : s.store.ns.ViewOK v)
    (hrun : internNNode v s = .ok (h, s')) :
    PStep s s' ∧ denoteN s'.store.ns h = denoteNView s'.store.ns v := by
  obtain ⟨h1, h2, h3, h4, h5, _h6, h7, h8, _h9, h10⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internNNode_spec s v hok.wf hv)
  exact ⟨PStep.of_caches ⟨h1⟩ h2 (bmExt_of_nested h3 h4 h5) h7 h8, h10⟩

/-- con-leche: none — `internNNode` at a `.str`: every name this tier builds
(`N._model`, `T.proj`, `T._model.proj_i`) goes through it. -/
theorem internStrN_run {s s' : AState} {p : NIdx} {pm : ConLeche.Name}
    {str : String} {h : NIdx} (hok : StateOK s)
    (hp : denoteN s.store.ns p = some pm)
    (hrun : internNNode (.str p str) s = .ok (h, s')) :
    PStep s s' ∧ denoteN s'.store.ns h = some (pm.str str) := by
  obtain ⟨hstep, hd⟩ := internNNode_run hok
    (by intro c hc
        simp only [NNodeView.children, List.mem_singleton] at hc
        subst hc
        exact nview_isSome_of_denote hp) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteNView, denoteN_ext hp hstep.ext, Option.map_some]

/-- con-leche: none — and at a `.num`: `projFnName`'s last component. -/
theorem internNumN_run {s s' : AState} {p : NIdx} {pm : ConLeche.Name}
    {i : Nat} {h : NIdx} (hok : StateOK s)
    (hp : denoteN s.store.ns p = some pm)
    (hrun : internNNode (.num p i) s = .ok (h, s')) :
    PStep s s' ∧ denoteN s'.store.ns h = some (pm.num i) := by
  obtain ⟨hstep, hd⟩ := internNNode_run hok
    (by intro c hc
        simp only [NNodeView.children, List.mem_singleton] at hc
        subst hc
        exact nview_isSome_of_denote hp) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteNView, denoteN_ext hp hstep.ext, Option.map_some]

/-- con-leche: none — a handle list's denotation splits over an append, which
is what the two-spine generators (`structCtorSpine`, `structFamI`) need before
`mkAppN`.  Belongs in `Bridge/Rel.lean` beside `denoteEList_snoc`. -/
theorem denoteEList_append {st : EStore} :
    ∀ {a : List EIdx} {as : List Expr} {b : List EIdx} {bs : List Expr},
      Frontend.denoteEList st a = some as →
      Frontend.denoteEList st b = some bs →
      Frontend.denoteEList st (a ++ b) = some (as ++ bs) := by
  intro a
  induction a with
  | nil =>
    intro as b bs ha hb
    simp only [Frontend.denoteEList, Option.some.injEq] at ha
    subst ha
    simpa using hb
  | cons x xs ih =>
    intro as b bs ha hb
    simp only [Frontend.denoteEList] at ha
    cases hx : denoteE st x with
    | none => rw [hx] at ha; simp at ha
    | some y =>
      cases hxs : Frontend.denoteEList st xs with
      | none => rw [hx, hxs] at ha; simp at ha
      | some ys =>
        rw [hx, hxs] at ha
        obtain rfl := Option.some.inj ha
        simp only [List.cons_append, Frontend.denoteEList, hx, ih hxs hb]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN — **`mkAppN`, as a
run**.  `Bridge/ExprOps/Spine.lean`'s `mkAppN_spec` is closed and says the
same thing, but its frame has no `BMExt` conjunct and `PStep` needs one, so
the four-line induction is done here rather than re-stated there (the twin is
`internE (.app f a)` folded over the list, so each step's `BMExt` is
`internE_run`'s own). -/
theorem mkAppN_run : ∀ (args : List EIdx) (argsP : List Expr) {s s' : AState}
    {f : EIdx} {fP : Expr} {r : EIdx}, StateOK s →
    denoteE s.store f = some fP →
    Frontend.denoteEList s.store args = some argsP →
    ConRon.Arena.mkAppN f args s = .ok (r, s') →
    PStep s s' ∧ denoteE s'.store r = some (Expr.mkAppN fP argsP) := by
  intro args
  induction args with
  | nil =>
    intro argsP s s' f fP r hok hf hargs hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hargs
    subst hargs
    simp only [ConRon.Arena.mkAppN, pure, StateT.pure, Except.pure] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Except.ok.inj hrun)
    exact ⟨PStep.refl hok, hf⟩
  | cons a as ih =>
    intro argsP s s' f fP r hok hf hargs hrun
    simp only [Frontend.denoteEList] at hargs
    cases ha : denoteE s.store a with
    | none => rw [ha] at hargs; simp at hargs
    | some x =>
      cases has : Frontend.denoteEList s.store as with
      | none => rw [ha, has] at hargs; simp at hargs
      | some xs =>
        rw [ha, has] at hargs
        obtain rfl := Option.some.inj hargs
        simp only [ConRon.Arena.mkAppN] at hrun
        obtain ⟨g, s₁, h1, h2⟩ := bindOk hrun
        obtain ⟨hstep1, hg⟩ :=
          internE_run hok (viewOK_app (by rw [hf]; rfl) (by rw [ha]; rfl)) h1
        have hg' : denoteE s₁.store g = some (.app fP x) := by
          rw [hg]
          simp only [denoteEView, denote_ext hf hstep1.ext,
            denote_ext ha hstep1.ext, opt2]
        obtain ⟨hstep2, hr⟩ :=
          ih xs hstep1.ok hg' (denoteEList_ext hstep1.ext _ _ has) h2
        exact ⟨hstep1.trans hstep2, hr⟩

/-! ### The stored constant's NAME, and the `.projInfo` name gap — MOVED

`denoteCV_type`, `denoteCV_name`, `denoteCI_name`, `denoteCI_name_proj` and
`denoteCI_name_of` were proved here in round 3 and **moved to
`Bridge/StateOK.lean` in round 4**, beside `IProjTableOK` — the lowest module
that has both `Frontend.denoteCI` and the invariant, and the one below the
Checker tier, whose `IFEnvOK_of_denote`, `denoteFEnv_restrictTo` and
`installBasisDecl_bridge` need them and cannot see `Bridge/Inductives/**`.
They are in scope here unchanged (`ConRon.Bridge` is this namespace's
parent), so every use in this tier reads the same. -/

/-- con-leche: none — **a denoting binder telescope denotes AT A POSITION**,
which is the read `structFieldTeleOf` and `structFieldIdxOf` make.  The bound
is not decoration: below it the two sides' `getD` FALLBACKS are unrelated
(`default : EIdx × BinderMeta` on one side, `default : Expr × BinderMeta` on
the other), which is the defect round 4 records at those two statements. -/
theorem denoteBinders_getD {st : EStore} :
    ∀ {bs : List (EIdx × BinderMeta)} {xs : List (Expr × BinderMeta)} {k : Nat},
      denoteBinders st bs = some xs → k < bs.length →
      denoteE st (bs.getD k default).1 = some (xs.getD k default).1 := by
  intro bs
  induction bs with
  | nil => intro xs k _ hk; simp at hk
  | cons a as ih =>
    intro xs k h hk
    obtain ⟨t, m⟩ := a
    simp only [denoteBinders] at h
    cases ht : denoteE st t with
    | none => rw [ht] at h; simp at h
    | some x =>
      cases has : denoteBinders st as with
      | none => rw [ht, has] at h; simp at h
      | some ys =>
        rw [ht, has] at h
        obtain rfl := Option.some.inj h
        cases k with
        | zero => simpa only [List.getD_cons_zero] using ht
        | succ k =>
          have hk' : k < as.length := by simpa using hk
          simpa only [List.getD_cons_succ] using ih has hk'

/-- con-leche: none — **a denoting binder telescope reads at an INDEX with the
`Option` CARRIED**, both ways.  `structShape` reads `rbs[nP]?`, `rbs[nP+1]?`
and `rbs[nP+2]?` and dispatches on the `Option`, so the `none` answers have to
correspond as well as the `some` ones; the `BinderMeta` travels verbatim
(`denoteBinders` copies it), which is why the two sides share one `m`. -/
theorem denoteBinders_getElem? {st : EStore} :
    ∀ {bs : List (EIdx × BinderMeta)} {xs : List (Expr × BinderMeta)},
      denoteBinders st bs = some xs → ∀ (k : Nat),
        (∀ b m, bs[k]? = some (b, m) →
          ∃ x, xs[k]? = some (x, m) ∧ denoteE st b = some x) ∧
        (bs[k]? = none → xs[k]? = none) := by
  intro bs
  induction bs with
  | nil =>
    intro xs h k
    simp only [denoteBinders, Option.some.injEq] at h
    subst h
    exact ⟨by intro b m hb; simp at hb, by intro _; simp⟩
  | cons a as ih =>
    intro xs h k
    obtain ⟨t, m⟩ := a
    simp only [denoteBinders] at h
    cases ht : denoteE st t with
    | none => rw [ht] at h; simp at h
    | some y =>
      cases has : denoteBinders st as with
      | none => rw [ht, has] at h; simp at h
      | some ys =>
        rw [ht, has] at h
        obtain rfl := Option.some.inj h
        cases k with
        | zero =>
          refine ⟨?_, ?_⟩
          · intro b m' hb
            simp only [List.getElem?_cons_zero, Option.some.injEq,
              Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl⟩ := hb
            exact ⟨y, by simp, ht⟩
          · intro hb; simp at hb
        | succ k =>
          obtain ⟨hA, hB⟩ := ih has k
          refine ⟨?_, ?_⟩
          · intro b m' hb
            simp only [List.getElem?_cons_succ] at hb
            obtain ⟨x, hx, hd⟩ := hA b m' hb
            exact ⟨x, by simpa using hx, hd⟩
          · intro hb
            simp only [List.getElem?_cons_succ] at hb ⊢
            exact hB hb

/-- con-leche: none — a binder telescope's denotation keeps its length. -/
theorem denoteBinders_length {st : EStore} :
    ∀ {bs : List (EIdx × BinderMeta)} {xs : List (Expr × BinderMeta)},
      denoteBinders st bs = some xs → bs.length = xs.length := by
  intro bs
  induction bs with
  | nil => intro xs h; simp only [denoteBinders, Option.some.injEq] at h; simp [← h]
  | cons a as ih =>
    intro xs h
    obtain ⟨t, m⟩ := a
    simp only [denoteBinders] at h
    cases ht : denoteE st t with
    | none => rw [ht] at h; simp at h
    | some y =>
      cases has : denoteBinders st as with
      | none => rw [ht, has] at h; simp at h
      | some ys =>
        rw [ht, has] at h
        obtain rfl := Option.some.inj h
        simp only [List.length_cons, ih has]

/-- con-leche: none — **`readLevel` in run form**: the readback IS `denoteL`
and the state does not move.  `Bridge/Frontend/ProjRec.lean` has the same
lemma; that module is ABOVE this tier, so it is restated here (the same
reason `beq_handle_eq` is). -/
theorem readLevel_run {s s' : AState} {h : LIdx} {u : Level}
    (hrun : readLevel h s = .ok (u, s')) :
    s' = s ∧ denoteL s.store.ls h = some u :=
  AM.of_run (P := fun t => t = s) rfl hrun (readLevel_spec s h)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1112-1114 liftLooseBVarsFast —
**the lift in run form at this tier's frame**.  Round 4 §R4.4 recorded that
`Bridge/ExprOps/Subst.lean`'s `LiftSpec` did not state `BMExt` and that this
blocked the whole of group 3; task #97-P3-ExprOps round 4 stated it, and this
is the lemma that cashes it.  `Bridge/Inductives/Rel.lean` gains the
`ExprOps.Subst` import for it — nothing else in the Bridge imported that
module. -/
theorem liftFast_pstep {fuel amount c : Nat} {s₀ s' : AState} {e r : EIdx}
    {eP : Expr} (hok : StateOK s₀) (hd : denoteE s₀.store e = some eP)
    (hrun : Arena.liftLooseBVarsFast fuel amount c e s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ denoteE s'.store r = some (eP.liftLooseBVars amount c) := by
  obtain ⟨h1, h2, h3, h4, h5, _, _, h8⟩ :=
    ExprOps.liftLooseBVarsFast_run hok (by rw [hd]; rfl) hrun
  exact ⟨PStep.of_caches h1 h2 h3 h4 h5, h8 eP hd⟩

/-! ## One reader on loan from the `ExprOps` tier

`Arena/Env.lean`'s `piSortTeleLen?` is the syntactic Π-telescope's length, and
its Theorem 1 **belongs in `Bridge/ExprOps/TelescopeF.lean`** beside
`stripPis`' — but that tier has not stated it and two statements here need it
(`Bridge/Inductives/Decl.lean`'s `indParamsOk_spec`, which is the arm's own
gate, and `Bridge/Inductives/NativeParts.lean`'s `nativeCounts?_spec`).  It is
proved here, at this tier's frame, with the citation that says where it should
move. -/

/-- con-leche: ConLeche/Kernel/Env.lean:583-586 Expr.piSortTeleLen? —
**THEOREM 1 for `piSortTeleLen?`**: the number of `∀`-binders before a `Sort`
residual, or `none`.  A fuel induction whose ten-way arm is the `view`
dispatch; the eight arms that are neither a binder nor a sort answer `none` on
both sides, which is the dispatch's own soundness (a handle's view and its
denotation have the same constructor). -/
theorem piSortTeleLen?_spec : ∀ (fuel : Nat) (h : EIdx) (hP : Expr),
    PSpec (fun st => denoteE st h = some hP) (Arena.piSortTeleLen? fuel h)
      (RV hP.piSortTeleLen?) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h hP s₀ s' r hok hd hrun
    simp only [Arena.piSortTeleLen?] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro h hP s₀ s' r hok hd hrun
    simp only [Arena.piSortTeleLen?] at hrun
    obtain ⟨v, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨hs1, hw⟩ := view_run h1
    rw [hs1] at h2
    have hde : denoteEView s₀.store v = some hP := by
      rw [denoteE_view_eq hok.wf hw] at hd; exact hd
    cases v
    case forallE ty body m =>
      obtain ⟨et, eb, rfl, hty, hb⟩ := denote_forallE_inv hok.wf hw hd
      obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨hstep, ho⟩ := ih body eb s₀ s₂ o hok hb h3
      obtain ⟨rfl, rfl⟩ := pureOk h4
      exact ⟨hstep, by rw [ho]; rfl⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨uP, _, rfl⟩ := Option.map_eq_some_iff.mp hde
      exact ⟨PStep.refl hok, rfl⟩
    all_goals
      (obtain ⟨rfl, rfl⟩ := pureOk h2
       refine ⟨PStep.refl hok, ?_⟩
       simp only [denoteEView] at hde
       first
       | (obtain ⟨x, y, z, _, _, _, rfl⟩ := opt3_eq_some_iff.mp hde; rfl)
       | (obtain ⟨x, y, _, _, rfl⟩ := opt2_eq_some_iff.mp hde; rfl)
       | (obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp hde; rfl)
       | (obtain rfl := Option.some.inj hde; rfl))

/-- con-leche: none — **`denoteCI` preserves the constant's KIND**: a handle
record that is not a constructor denotes a constant that is not one.  The
shape a twin that DISPATCHES on the stored constant's kind needs at its
fallthrough arm (`ctorResidualOk`'s `| _ => false`). -/
theorem denoteCI_not_ctor {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c)
    (hne : ∀ v n1 n2, ci ≠ .ctorInfo v n1 n2) :
    ∀ v n1 n2, c ≠ .ctorInfo v n1 n2 := by
  cases ci <;>
    simp_all [Frontend.denoteCI, Option.map_eq_some_iff] <;> grind

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

/-! ## The projection table's obligation

`Bridge/StateOK.lean`'s `IProjTableOK` is a field of `IFEnvOK`, and
`Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote` takes it as the hypothesis
`hproj`.  Its ONE debtor is `Arena.checkStructProjTable` — the only function
of the whole arena that pushes a `.projInfo` row — and this tier owns it;
`Bridge/Checker/Inv.lean`'s `projTableOK_of_install` names it by file and
theorem.

Two of the record's three clauses the install itself tests (`unless
bodies.size = nF` is `bodies` verbatim, `let tn ← projTableName T` is
`named`'s second half).  The third, `guards.length = numFields`, is about an
ARGUMENT, so it cannot be tested there and its site is the CALLER:
`Arena.checkNativeTable` builds `structProjGuards cA.1.type p.nP cA.2 sorts`
and passes it beside `cA.2`, and `structProjGuards`' own answer has length
`nF` by construction (`structProjGuards_length`).  So
`checkStructProjTable_spec` takes `guards.length = nF` as a HYPOTHESIS and
`checkNativeTable_spec` discharges it.

The clause an install can actually CONCLUDE is RELATIVE — "every projection
table the new index holds was already in the old one, or is well shaped at the
new store" — because a route chains a dozen installs and only the structure
route's stage 4 pushes one.  `ProjOut` is that clause; it composes
(`ProjOut.trans`, transporting the older tables over the store the chain
grew), and it is a FIELD of `InstRel` so that every install of the tier
carries it rather than each caller restating it.

`ProjOut.absolute` turns it back into the absolute statement
`IFEnvOK_of_denote` wants, against the fold's own `IFEnvOK env fe s` at the
index the step started from. -/

/-- con-leche: none — a level-handle list's denotation has its own length.
What `checkNativeTable_spec` reads `guards.length = nF` off, against
`structProjGuards_length`.  Belongs in `Bridge/Rel.lean` beside
`denoteLList_ext`. -/
theorem denoteLList_length {st : LStore} :
    ∀ (us : List LIdx) (xs : List Level), denoteLList st us = some xs →
      us.length = xs.length := by
  intro us
  induction us with
  | nil => intro xs h; simp only [denoteLList, Option.some.injEq] at h; simp [← h]
  | cons u us ih =>
    intro xs h
    simp only [denoteLList, opt2] at h
    cases hu : denoteL st u with
    | none => rw [hu] at h; simp at h
    | some y =>
      cases hus : denoteLList st us with
      | none => rw [hu, hus] at h; simp at h
      | some ys =>
        rw [hu, hus] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.length_cons, ih _ hus]

/-- con-leche: ConLeche/Verify/EnvWF.lean:191 ConstWF (the `.projInfo`
clause) — **what an install owes about projection tables**: every table the
new index holds is either one the old index already held, or one that is well
shaped and rightly named at the new store. -/
def ProjOut (fe : IFEnv) (st : EStore) (fe' : IFEnv) : Prop :=
  ∀ n t, fe'.find? n = some (.projInfo t) →
    fe.find? n = some (.projInfo t) ∨ IProjTableOK st t

/-- con-leche: none — an install that changes nothing owes nothing. -/
theorem ProjOut.refl (fe : IFEnv) (st : EStore) : ProjOut fe st fe :=
  fun _ _ h => Or.inl h

/-- con-leche: none — the obligation survives the arena's growth, by
`IProjTableOK.mono`. -/
theorem ProjOut.mono {fe fe' : IFEnv} {st st' : EStore}
    (h : ProjOut fe st fe') (hx : Ext st st') : ProjOut fe st' fe' := by
  intro n t hf
  rcases h n t hf with h' | h'
  · exact Or.inl h'
  · exact Or.inr (h'.mono hx)

/-- con-leche: none — **the obligation chains**, which is what a route's
dozen stages need of it.  The older half's tables are transported over the
store the later stages grew. -/
theorem ProjOut.trans {fe₀ fe₁ fe₂ : IFEnv} {st₁ st₂ : EStore}
    (h₁ : ProjOut fe₀ st₁ fe₁) (h₂ : ProjOut fe₁ st₂ fe₂) (hx : Ext st₁ st₂) :
    ProjOut fe₀ st₂ fe₂ := by
  intro n t hf
  rcases h₂ n t hf with h' | h'
  · rcases h₁ n t h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (h''.mono hx)
  · exact Or.inr h'

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **a push that is
not a projection table owes nothing**.  Thirteen of this tier's fourteen
install statements need exactly this; the fourteenth is
`checkStructProjTable`, the one install of the arena that pushes a
`.projInfo` row.

The coherence hypothesis is not decoration: `IFEnv.find?` hides an entry whose
counter is not below `visibleBelow`, and `push` raises the bound, so without
`IFEnvCoh fe` a push could REVEAL a stale projection table the old index was
hiding.  `mkIFEnvGo_counter_lt` is what rules that out. -/
theorem ProjOut.push {fe : IFEnv} (hcoh : IFEnvCoh fe) (st : EStore)
    {ci : IConstantInfo} (hci : ∀ t, ci ≠ .projInfo t) :
    ProjOut fe st (fe.push ci) := by
  intro n t hf
  left
  have hidx : fe.idx = (mkIFEnvGo fe.env.consts).2 := congrArg IFEnv.idx hcoh
  have hvb : fe.visibleBelow = (mkIFEnvGo fe.env.consts).1 :=
    congrArg IFEnv.visibleBelow hcoh
  simp only [IFEnv.find?, IFEnv.push, Std.HashMap.getElem?_insert] at hf
  by_cases hEq : (ci.name == n) = true
  · rw [if_pos hEq] at hf
    simp only [Nat.lt_succ_self, if_true] at hf
    exact absurd (Option.some.inj hf) (hci t)
  · rw [if_neg hEq] at hf
    cases hg : fe.idx[n]? with
    | none => rw [hg] at hf; exact nomatch hf
    | some p =>
      obtain ⟨cnt, cinfo⟩ := p
      rw [hg] at hf
      have hlt : cnt < fe.visibleBelow := by
        rw [hvb]
        exact mkIFEnvGo_counter_lt fe.env.consts n cnt cinfo (hidx ▸ hg)
      simp only [if_pos (Nat.lt_succ_of_lt hlt)] at hf
      simp only [IFEnv.find?, hg, if_pos hlt]
      exact hf

/-- con-leche: none — **the absolute form**, which is what
`Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote` asks for: the fold's invariant
at the index the step started from, plus the step's own `ProjOut`, is the
invariant at the index it produced. -/
theorem ProjOut.absolute {env : Env} {fe fe' : IFEnv} {s : AState}
    {st' : EStore} (hfe : IFEnvOK env fe s) (hx : Ext s.store st')
    (h : ProjOut fe st' fe') :
    ∀ n t, fe'.find? n = some (.projInfo t) → IProjTableOK st' t := by
  intro n t hf
  rcases h n t hf with h' | h'
  · exact (hfe.proj n t h').mono hx
  · exact h'

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
  /-- **the projection tables this install left behind are well shaped** —
  the section above says why the clause is relative and why it lives here
  rather than at the one install that can discharge it. -/
  proj : ProjOut fe st fe'

/-- con-leche: none — `InstRel` composes along a chain of installs: the
environment relations chain by `Pushed.trans`, the projection obligation by
`ProjOut.trans`, and the pure side's runs are chained by the caller (each
install's `P` names its own con-leche function).

**The `Ext` argument is what `proj` costs**: an earlier stage's tables are
well shaped at the store THAT stage left, and the chain's conclusion is at the
store the last stage left.  Every caller has it — it is the `ext` field of the
`PStep`/`CoreStep` the same two stages produced. -/
theorem InstRel.trans {fe₀ fe₁ fe₂ : IFEnv} {P₁ P₂ : Env → Prop}
    {st₁ st₂ : EStore} (hx : Ext st₁ st₂) (h₁ : InstRel fe₀ P₁ st₁ fe₁)
    (h₂ : InstRel fe₁ P₂ st₂ fe₂) : InstRel fe₀ P₂ st₂ fe₂ where
  coh := h₂.coh
  pushed := h₁.pushed.trans h₂.pushed
  visible := Nat.le_trans h₁.visible h₂.visible
  denote := h₂.denote
  proj := h₁.proj.trans h₂.proj hx

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
  /-- **the eighth clause** (task #97-P3-Ind round 2): the arm's own
  `ProjOut`.  `Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote` needs
  `IProjTableOK` at every stored table of the index the step produced, and
  `ProjOut.absolute` is what turns this clause plus the fold's incoming
  `IFEnvOK` into that.  `Bridge/Checker/Hyp.lean`'s `IndSpec` and
  `Bridge/Checker/Decl.lean`'s `DeclOut` do not carry it yet — that is the
  checker tier's two-line follow-on, and `indSpec_of_bridge` simply drops it
  until then. -/
  proj : ProjOut fe s'.store fe'

end ConRon.Bridge.Inductives
