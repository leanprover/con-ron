/-
# `ConRon.Bridge.Inductives.Run` — the tier's pure-grade vocabulary

The half of the tier's vocabulary that reads no knot and no environment
index: the pure frame `PStep`, the pure statement shapes (`PSpec`, `PSpecP`,
`PSpecL`), the `Option` lift `ROp`, the answer relations, the binder and
constructor-list denotations, the `AM` bind's inversion and the store
primitives in RUN form.  Split out of `Bridge/Inductives/Rel.lean` (task #105)
so that the pure-grade twins of the uniform route — the positivity walk's
memoised occurrence tests, the recogniser — build without the Core tier.
`Rel.lean` imports this and adds the core-grade shapes.
-/
import ConRon.Bridge.Inductives.Records
import ConRon.Bridge.Specs
import ConRon.Bridge.ExprOps.TagFirst

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

/-- con-leche: none — **the pure grade with the level-readback cache** (task
#97-T2-LOCKSTEP lane Inductives round 3, ruling 1).  A twin that reads a level
back through the CACHED `readLevelM` answers the denotation only under
`ReadLCacheOK`, which `StateOK` does not carry; the core grade (`CSpec`) does,
but its `CheckOK` also pins every knot cache to ONE environment, which the
native recursor's generators do not have (they run at the environment with
the rule-less recursor pushed, `checkNativeRec`).  This grade asks for the one
table and nothing else; `PSpecL.toCSpec` is the core grade. -/
def PSpecL {α : Type} (P : EStore → Prop) (c : AM α) (R : EStore → α → Prop) :
    Prop :=
  ∀ (s₀ s' : AState) (r : α), StateOK s₀ → ReadLCacheOK s₀.caches.readLC s₀.store →
    P s₀.store → c s₀ = .ok (r, s') → PStep s₀ s' ∧ R s'.store r

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
/-- a LIST of expression handles denotes a given `List Expr`. -/
abbrev REL (vs : List Expr) : EStore → List EIdx → Prop :=
  fun st r => Frontend.denoteEList st r = some vs
/-- an ARRAY of expression handles denotes a given `Array Expr`. -/
abbrev REA (vs : Array Expr) : EStore → Array EIdx → Prop :=
  fun st r => Frontend.denoteEArray st r = some vs
/-- a LIST of level handles denotes a given `List Level`. -/
abbrev RLL (us : List Level) : EStore → List LIdx → Prop :=
  fun st r => denoteLList st.ls r = some us
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

/-! ## The capability record -/

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

/-- con-leche: none — **the tag-first twin's test, in run form** (task
#97-P5-Core round 4): at a handle whose view is known, `if h.tag == t then
view h >>= f else e` ran as `view h >>= f`, because on the `else` side the
continuation's catch-all arm IS `e`. -/
theorem tagIf_view_run {α : Type} {h : EIdx} {t : UInt32} {v : ENodeView}
    {f : ENodeView → AM α} {e : AM α} {s s' : AState} {r : α}
    (hv : s.store.view h = some v) (he : v.tagOf ≠ t → f v = e)
    (hrun : (if h.tag == t then (Arena.view h >>= f) else e) s = .ok (r, s')) :
    (Arena.view h >>= f) s = .ok (r, s') := by
  by_cases ht : (h.tag == t) = true
  · rw [if_pos ht] at hrun; exact hrun
  · rw [if_neg ht] at hrun
    have hne : v.tagOf ≠ t := by rw [← EStore.tagOf_of_view hv]; simpa using ht
    have hb : (Arena.view h >>= f) s = f v s := by
      show StateT.bind (Arena.view h) f s = _
      simp only [StateT.bind, Arena.view, bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, Except.bind, Except.pure, hv]
    rw [hb, he hne]; exact hrun

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

/-- con-leche: none — **`zeroLevel`, as a run**: the pin read this tier's
`structProjGuards` and `structPartsCore?` open with, and the reason
`PSpecP` exists. -/
theorem zeroLevel_run {s s' : AState} {u : LIdx} (hp : PinsOK s)
    (hrun : Arena.zeroLevel s = .ok (u, s')) :
    s' = s ∧ denoteL s.store.ls u = some .zero := by
  simp only [Arena.zeroLevel] at hrun
  exact AM.of_run (P := fun t => t = s) rfl hrun (pinZeroLevel_spec s hp)

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

/-- con-leche: none — the two constructor-list denotations agree:
`Records.lean`'s `dCtors` (a `mapM`) is `Run.lean`'s `denoteCtors`. -/
theorem dCtors_eq_denoteCtors (st : EStore) :
    ∀ cs : List (IConstantVal × Nat), dCtors st cs = denoteCtors st cs
  | [] => rfl
  | (cv, n) :: cs => by
    have ih := dCtors_eq_denoteCtors st cs
    simp only [dCtors] at ih ⊢
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, dCtor, denoteCtors, ih]
    cases Frontend.denoteCV st cv <;> cases denoteCtors st cs <;> rfl

/-- con-leche: none — a denoted constructor list's names. -/
theorem dCtors_names {st : EStore} :
    ∀ {cs : List (IConstantVal × Nat)} {csP : List (ConstantVal × Nat)},
      dCtors st cs = some csP →
      Frontend.denoteNList st.ns (cs.map (·.1.name)) = some (csP.map (·.1.name))
  | [], csP, h => by
    simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | x :: xs, csP, h => by
    obtain ⟨y, ys', rfl, hy, hys⟩ := mapM_option_cons_inv h
    simp only [dCtor, Option.map_eq_some_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [List.map_cons, Frontend.denoteNList, denoteCV_name hz, dCtors_names hys]

/-! ## Views, tags and name/handle lists at the pure frame -/

/-- con-leche: none — `internE` at an `.fvar`. -/
theorem internFVarE_run {s s' : AState} {k : Nat} {ty : EIdx} {tyP : Expr}
    {h : EIdx} (hok : StateOK s) (hty : denoteE s.store ty = some tyP)
    (hrun : internFVarE k ty s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.fvar k tyP) := by
  obtain ⟨hstep, hd⟩ := internE_run hok (viewOK_fvar (by rw [hty]; rfl)) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteEView, denote_ext hty hstep.ext, Option.map_some]

/-- con-leche: none — `internE` at a `.letE`. -/
theorem internLetEE_run {s s' : AState} {ty v b : EIdx} {tyP vP bP : Expr}
    {h : EIdx} (hok : StateOK s) (hty : denoteE s.store ty = some tyP)
    (hv : denoteE s.store v = some vP) (hb : denoteE s.store b = some bP)
    (hrun : internLetEE ty v b s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.letE tyP vP bP) := by
  obtain ⟨hstep, hd⟩ := internE_run hok
    (viewOK_letE (by rw [hty]; rfl) (by rw [hv]; rfl) (by rw [hb]; rfl)) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteEView, denote_ext hty hstep.ext, denote_ext hv hstep.ext,
    denote_ext hb hstep.ext, opt3]

/-- con-leche: none — `viewConst`, as a run. -/
theorem viewConst_run {s s' : AState} {h : EIdx} {r : Option (NIdx × LsIdx)}
    (hrun : viewConst h s = .ok (r, s')) : s' = s ∧ r = s.store.viewConst h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewConst_spec s h)

/-- con-leche: none — `viewApp`, as a run. -/
theorem viewApp_run {s s' : AState} {h : EIdx} {r : Option (EIdx × EIdx)}
    (hrun : viewApp h s = .ok (r, s')) : s' = s ∧ r = s.store.viewApp h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewApp_spec s h)

/-- con-leche: none — `viewFVarIdx`, as a run. -/
theorem viewFVarIdx_run {s s' : AState} {h : EIdx} {r : Option Nat}
    (hrun : viewFVarIdx h s = .ok (r, s')) : s' = s ∧ r = s.store.viewFVarIdx h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewFVarIdx_spec s h)

/-- con-leche: none — `viewBind`, as a run. -/
theorem viewBind_run {s s' : AState} {h : EIdx}
    {r : Option (EIdx × EIdx × BinderMeta)}
    (hrun : viewBind h s = .ok (r, s')) : s' = s ∧ r = s.store.viewBind h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewBind_spec s h)

/-- con-leche: none — a failing `failDanglingE` cannot have accepted. -/
theorem failDanglingE_ok {α : Type} {r : α} {s s' : AState}
    (h : (failDanglingE : AM α) s = .ok (r, s')) : False :=
  failOk h

/-- con-leche: none — **a denoting handle's tag is its view's**, with the
view's denotation. -/
theorem denote_view_tag {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) :
    ∃ v, st.view h = some v ∧ h.tag = v.tagOf ∧ denoteEView st v = some e := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  exact ⟨v, hv, EStore.tagOf_of_view hv, by rw [← denoteE_view_eq hwf hv]; exact hd⟩

theorem tag_const_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : ConLeche.Name} {us : List Level}
    (hd : denoteE st h = some (.const n us)) : h.tag = ETag.const := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

theorem tag_app_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {f a : Expr} (hd : denoteE st h = some (.app f a)) : h.tag = ETag.app := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

theorem tag_fvar_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {k : Nat} {t : Expr} (hd : denoteE st h = some (.fvar k t)) :
    h.tag = ETag.fvar := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

theorem tag_forallE_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {d b : Expr} {m : BinderMeta} (hd : denoteE st h = some (.forallE d b m)) :
    h.tag = ETag.forallE := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

/-- con-leche: none — **a name-handle list's membership is the names'**,
through `beq_handle_eq` at each element. -/
theorem contains_handle_eq {st : EStore} (hwf : StoreWF st) {n : NIdx}
    {nm : ConLeche.Name} (hn : denoteN st.ns n = some nm) :
    ∀ {names : List NIdx} {namesP : List ConLeche.Name},
      Frontend.denoteNList st.ns names = some namesP →
      names.contains n = namesP.contains nm := by
  intro names
  induction names with
  | nil =>
    intro namesP h
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro namesP h
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp only [List.contains_cons, beq_handle_eq hwf hn ha, ih has]

/-- con-leche: none — and so is its `findIdx?` lookup. -/
theorem findIdx_handle_eq {st : EStore} (hwf : StoreWF st) {n : NIdx}
    {nm : ConLeche.Name} (hn : denoteN st.ns n = some nm) :
    ∀ {names : List NIdx} {namesP : List ConLeche.Name},
      Frontend.denoteNList st.ns names = some namesP →
      names.findIdx? (· == n) = namesP.findIdx? (· == nm) := by
  intro names
  induction names with
  | nil =>
    intro namesP h
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro namesP h
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp only [List.findIdx?_cons, beq_handle_eq hwf ha hn, ih has]

/-- con-leche: none — a denoting name-handle list has the names' length. -/
theorem denoteNList_length {st : NStore} :
    ∀ {names : List NIdx} {namesP : List ConLeche.Name},
      Frontend.denoteNList st names = some namesP → names.length = namesP.length := by
  intro names
  induction names with
  | nil =>
    intro namesP h
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro namesP h
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteNList st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp [ih has]

/-- con-leche: none — a denoting name-handle list at an index. -/
theorem denoteNList_getElem? {st : NStore} :
    ∀ {names : List NIdx} {namesP : List ConLeche.Name},
      Frontend.denoteNList st names = some namesP → ∀ (j : Nat) (n : NIdx),
        names[j]? = some n → ∃ nm, namesP[j]? = some nm ∧ denoteN st n = some nm := by
  intro names
  induction names with
  | nil => intro namesP _ j n hj; simp at hj
  | cons a as ih =>
    intro namesP h j n hj
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteNList st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          exact ⟨x, rfl, ha⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj ⊢
          exact ih has j n hj

/-- con-leche: none — a denoting expression-handle list has the terms'
length. -/
theorem denoteEList_length {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr},
      Frontend.denoteEList st hs = some xs → hs.length = xs.length := by
  intro hs
  induction hs with
  | nil =>
    intro xs h
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro xs h
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp [ih has]

/-- con-leche: none — a denoting expression-handle list at an index, with the
`Option` carried both ways. -/
theorem denoteEList_getElem? {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr},
      Frontend.denoteEList st hs = some xs → ∀ (j : Nat),
        (hs[j]? = none ↔ xs[j]? = none) ∧
        ∀ h, hs[j]? = some h → ∃ x, xs[j]? = some x ∧ denoteE st h = some x := by
  intro hs
  induction hs with
  | nil =>
    intro xs h j
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp
  | cons a as ih =>
    intro xs h j
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        cases j with
        | zero =>
          refine ⟨by simp, ?_⟩
          intro h' hj
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          exact ⟨x, rfl, ha⟩
        | succ j =>
          simp only [List.getElem?_cons_succ]
          exact ih has j

/-- con-leche: none — **a LEVEL-LIST-handle comparison is a structural
comparison**, at both signs: the interned list's handle is its identity
(`denoteLs_inj`, `Arena/WFProofs.lean`).  `memberIdxAt?` and `nestCanonSub`
compare a `const` node's level list against the block's this way. -/
theorem beq_lshandle_eq {st : EStore} (hwf : StoreWF st) {a b : LsIdx}
    {x y : List Level} (ha : denoteLs st.lss a = some x)
    (hb : denoteLs st.lss b = some y) : (a == b) = (x == y) := by
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
    have hne : (a == b) = true := beq_iff_eq.mpr (denoteLs_inj hrk.lssWF ha hb)
    rw [h1] at hne
    exact absurd hne (by simp)

/-- con-leche: none — the `fvar` index projection read means the type
projection reads too (one row of the `fvar` array): `TagFirst`'s
`viewFVarIdx_of_viewFVarTy`, the other way. -/
theorem viewFVarTy_of_viewFVarIdx {st : EStore} {i : EIdx} {k : Nat}
    (h : st.viewFVarIdx i = some k) : ∃ ty, st.viewFVarTy i = some ty := by
  unfold EStore.viewFVarIdx at h
  unfold EStore.viewFVarTy EStore.persGetFVarTy
  unfold EStore.persGetFVarIdx at h
  split at h
  · simp only [ETables.getFVarIdx, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, -⟩ := h
    exact ⟨r.ty, by simp [*, ETables.getFVarTy]⟩
  · split at h
    · simp only [ETables.getFVarIdx, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, -⟩ := h
      exact ⟨r.ty, by simp [*, ETables.getFVarTy]⟩
    · cases h

/-- con-leche: none — an `fvar`-tagged handle's index projection, with its
denotation: the term is that free variable. -/
theorem denote_of_viewFVarIdx {st : EStore} (hwf : StoreWF st) {a : EIdx} {j : Nat}
    {aP : Expr} (htg : (a.tag == ETag.fvar) = true) (hj : st.viewFVarIdx a = some j)
    (hd : denoteE st a = some aP) : ∃ t, aP = .fvar j t := by
  obtain ⟨ty, hty⟩ := viewFVarTy_of_viewFVarIdx hj
  have hw := view_of_viewFVar_tag htg hj hty
  obtain ⟨t, rfl, _⟩ := denote_fvar_inv hwf hw hd
  exact ⟨t, rfl⟩

/-- con-leche: none — a `sort`-tagged denoting handle denotes a sort. -/
theorem sort_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (htg : (h.tag == ETag.sort) = true) (hd : denoteE st h = some e) :
    ∃ u, e = .sort u := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht] at htg
  cases v with
  | sort u =>
    simp only [denoteEView, Option.map_eq_some_iff] at hv
    obtain ⟨l, -, rfl⟩ := hv
    exact ⟨l, rfl⟩
  | _ => revert htg; simp only [ENodeView.tagOf, beq_iff_eq]; intro hc; exact absurd hc (by decide)

/-- con-leche: none — and a sort denotes only at a `sort`-tagged handle. -/
theorem tag_sort_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx} {u : Level}
    (hd : denoteE st h = some (.sort u)) : h.tag = ETag.sort := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

/-- con-leche: none — a denoting handle list's last element, both ways. -/
theorem denoteEList_getLast? {st : EStore} {hs : List EIdx} {xs : List Expr}
    (h : Frontend.denoteEList st hs = some xs) :
    (hs.getLast? = none → xs.getLast? = none) ∧
      ∀ a, hs.getLast? = some a → ∃ x, xs.getLast? = some x ∧ denoteE st a = some x := by
  have hl := denoteEList_length h
  have hg := denoteEList_getElem? h (hs.length - 1)
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, ← hl]
  exact ⟨hg.1.mp, hg.2⟩

end ConRon.Bridge.Inductives
