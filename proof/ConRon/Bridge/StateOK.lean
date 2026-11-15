/-
# `ConRon.Bridge.StateOK` — the state invariant and the memo invariants

DESIGN.md §8.2.  con-leche's own `ISOK` (`Verify/SimI.lean:54`, quoted in
`_tmp/t97/conleche-arena-history.md` §2.3) split the way the arena's state is
split, and for the same reason con-leche split `ISOK` from `ISOKF`:

* **`StateOK s`** is the clause every tier needs and the only clause the
  `ExprOps` tier mentions: the arena is well formed.  It is one field, and it
  is deliberately NOT the whole invariant — an `ExprOps` theorem that carried
  the cache clauses would carry con-leche's pure knot into a module about
  `instantiate1`, and the caches are transported past an `ExprOps` call by
  `CheckOK.mono` below instead (`Ext` plus the frame equation
  `s'.caches = s₀.caches`, which is one equation because the tables are one
  record, DESIGN `### Task #97b`).
* **`CacheOK eager env s`** is the per-DECLARATION tables' clause, in
  con-leche's `CacheOK` shape and **depth-universal** (the history report's
  lesson 8: "memo keys carry no ambient depth … entries are justified by a
  depth-universal fact `∃ F, ∀ d, a.wscopedB d → op env F d a = .ok b`").
* **`PinsOK s`** is the pin record denoting the reserved names
  (`Arena/Pins.lean`'s `pinNames` and `reservedBasisNameValues`, which are
  con-leche's `reservedBasisNames` and the `natOpNames` the Nat-op pin sets
  are keyed by) and the three nullary values.
* **`IFEnvOK env fe s`** is lesson 13's unconditional index spec:
  `fe.find? n` is the denoted environment's `find?`.
* **`CheckOK`** bundles the four; `CheckOK.mono` is what carries it past a
  call that only grows the arena.

The **per-CALL** memo tables of `Monad.lean`'s `Memos` are not in any of
these, and cannot be: their rows depend on the walk's own parameter (the
substituted term, the lift amount, the level vectors), which is not a
function of the state.  They are one predicate each, as con-leche's eleven
`…MemoInv` are, and they arrive as ordinary hypotheses of a walk's theorem.

Each is an `abbrev` over one generic `MemoOK` rather than an application of
it (DESIGN `### Task #97b`, finding 2): an `abbrev` per table fixes `f` to a
concrete lambda whose only metavariables are first-order, where the generic
`MemoOK f tbl st` would leave `f` a higher-order metavariable in the memo
insert's spec.  `abbrev` and not `def`, so the generic lemmas still match
syntactically.
-/
module

public import ConRon.Bridge.Rel
public import ConLeche.Kernel.TypeChecker
public import ConRon.Arena.Pins
public import ConLeche.Kernel.FEnv

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The store clause -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the state invariant's
store clause, and the only one the `ExprOps` tier mentions.  A one-field
structure rather than an abbreviation of `StoreWF s.store`, so that `hok.wf`
reads the same in every proof and so that a later tier can add a field
without touching a statement. -/
structure StateOK (s : AState) : Prop where
  wf : StoreWF s.store

/-! ## The per-call memo tables

One generic invariant per KEY/VALUE shape, and thirteen `abbrev`s that fix
the pure function.  The four shapes are `Monad.lean`'s own: nine tables keyed
`(EIdx × Nat)` with a handle value, two keyed `EIdx` with a `Nat` value, one
keyed `LIdx` with a level handle and one keyed `LsIdx` with a
universe-argument list handle. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:61-63 Inst1MemoInv — the generic
handle-valued memo invariant: every recorded answer is the real one, at the
key's own cursor.  The walk's own parameter does not appear; the invariant
speaks of denotations, so the parameter's DENOTATION is enough. -/
def MemoOK (f : Nat → Expr → Expr) (tbl : Std.HashMap (EIdx × Nat) EIdx)
    (st : EStore) : Prop :=
  ∀ (k : EIdx × Nat) (r : EIdx), tbl[k]? = some r →
    ∃ e, denoteE st k.1 = some e ∧ denoteE st r = some (f k.2 e)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1497-1499 MemoBInv — the generic
VALUE-valued memo invariant (`bvarBound`, `fvarRange`): the answer is
representation-free, so the row names no second handle. -/
def MemoVOK {α : Type} (f : Expr → α) (tbl : Std.HashMap EIdx α)
    (st : EStore) : Prop :=
  ∀ (k : EIdx) (v : α), tbl[k]? = some v →
    ∃ e, denoteE st k = some e ∧ v = f e

/-- con-leche: none — the generic LEVEL-handle memo invariant
(`instLPLC`, DESIGN `### Task #97-P6-13`). -/
def MemoLOK (f : Level → Level) (tbl : Std.HashMap LIdx LIdx)
    (st : EStore) : Prop :=
  ∀ (k r : LIdx), tbl[k]? = some r →
    ∃ u, denoteL st.ls k = some u ∧ denoteL st.ls r = some (f u)

/-- con-leche: none — the same at a universe-argument LIST handle
(`instLPLsC`). -/
def MemoLsOK (f : List Level → List Level) (tbl : Std.HashMap LsIdx LsIdx)
    (st : EStore) : Prop :=
  ∀ (k r : LsIdx), tbl[k]? = some r →
    ∃ us, denoteLs st.lss k = some us ∧ denoteLs st.lss r = some (f us)

/-! ### The four generic lemma sets

`mono` (the table stood still while the arena grew), `of_empty` (a dropped
table satisfies the invariant FOR EVERY parameter — which is why a per-call
memo never appears in a caller's invariant), `get` (a hit, delivered as the
answer relation so that the caller never unfolds the invariant) and `insert`
(the invariant-carrying insert of template rule 6). -/

theorem MemoOK.mono {f : Nat → Expr → Expr}
    {tbl tbl' : Std.HashMap (EIdx × Nat) EIdx} {st st' : EStore}
    (hm : MemoOK f tbl st) (hx : Ext st st') (hc : tbl' = tbl) :
    MemoOK f tbl' st' := by
  intro k r hk
  rw [hc] at hk
  obtain ⟨e, h1, h2⟩ := hm k r hk
  exact ⟨e, denote_ext h1 hx, denote_ext h2 hx⟩

theorem MemoOK.of_empty {f : Nat → Expr → Expr}
    {tbl : Std.HashMap (EIdx × Nat) EIdx} {st : EStore} (h : tbl = ∅) :
    MemoOK f tbl st := by
  intro k r hk; rw [h] at hk; simp at hk

/-- con-leche: ConLeche/Kernel/ExprOps.lean:61-63 Inst1MemoInv — **the memo
hit**: a recorded entry *is* the answer.  Stated as `RelE` so that the caller
never has to unfold `MemoOK` (and so that `MemoOK` can stay out of `grind`'s
unfold list, where it would skolemise the goal — DESIGN `### Task #97s`,
template rule 6). -/
@[grind →] theorem MemoOK.get {f : Nat → Expr → Expr}
    {tbl : Std.HashMap (EIdx × Nat) EIdx} {st : EStore} {k : EIdx × Nat}
    {r : EIdx} (hm : MemoOK f tbl st) (hk : tbl[k]? = some r) :
    RelE (f k.2) st k.1 st r := by
  intro e he
  obtain ⟨e', h1, h2⟩ := hm k r hk
  rw [he] at h1
  obtain rfl := Option.some.inj h1
  exact h2

/-- con-leche: ConLeche/Kernel/ExprOps.lean:67-79 Inst1MemoInv.insert —
stated in the `isSome` + `RelE` idiom, so that nothing has to be *guessed*
when the automation applies it. -/
theorem MemoOK.insert {f : Nat → Expr → Expr}
    {tbl tbl' : Std.HashMap (EIdx × Nat) EIdx} {st : EStore} {k : EIdx × Nat}
    {r : EIdx} (hm : MemoOK f tbl st) (hc : tbl' = tbl.insert k r)
    (hk : (denoteE st k.1).isSome = true) (hr : RelE (f k.2) st k.1 st r) :
    MemoOK f tbl' st := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hk
  intro k' r' hk'
  rw [hc, Std.HashMap.getElem?_insert] at hk'
  split at hk'
  · rename_i hbeq
    cases hk'
    obtain rfl := eq_of_beq hbeq
    exact ⟨e, he, hr e he⟩
  · exact hm k' r' hk'

theorem MemoVOK.of_empty {α : Type} {f : Expr → α}
    {tbl : Std.HashMap EIdx α} {st : EStore} (h : tbl = ∅) :
    MemoVOK f tbl st := by
  intro k v hk; rw [h] at hk; simp at hk

@[grind →] theorem MemoVOK.get {α : Type} {f : Expr → α}
    {tbl : Std.HashMap EIdx α} {st : EStore} {k : EIdx} {v : α}
    (hm : MemoVOK f tbl st) (hk : tbl[k]? = some v) : RelV f st k v := by
  intro e he
  obtain ⟨e', h1, h2⟩ := hm k v hk
  rw [he] at h1
  obtain rfl := Option.some.inj h1
  exact h2

theorem MemoVOK.insert {α : Type} {f : Expr → α}
    {tbl tbl' : Std.HashMap EIdx α} {st : EStore} {k : EIdx} {v : α}
    (hm : MemoVOK f tbl st) (hc : tbl' = tbl.insert k v)
    (hk : (denoteE st k).isSome = true) (hr : RelV f st k v) :
    MemoVOK f tbl' st := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hk
  intro k' v' hk'
  rw [hc, Std.HashMap.getElem?_insert] at hk'
  split at hk'
  · rename_i hbeq
    cases hk'
    obtain rfl := eq_of_beq hbeq
    exact ⟨e, he, hr e he⟩
  · exact hm k' v' hk'

theorem MemoLOK.mono {f : Level → Level} {tbl tbl' : Std.HashMap LIdx LIdx}
    {st st' : EStore} (hm : MemoLOK f tbl st) (hx : Ext st st')
    (hc : tbl' = tbl) : MemoLOK f tbl' st' := by
  intro k r hk
  rw [hc] at hk
  obtain ⟨u, h1, h2⟩ := hm k r hk
  exact ⟨u, denoteL_ext h1 hx, denoteL_ext h2 hx⟩

theorem MemoLOK.of_empty {f : Level → Level} {tbl : Std.HashMap LIdx LIdx}
    {st : EStore} (h : tbl = ∅) : MemoLOK f tbl st := by
  intro k r hk; rw [h] at hk; simp at hk

@[grind →] theorem MemoLOK.get {f : Level → Level}
    {tbl : Std.HashMap LIdx LIdx} {st : EStore} {k r : LIdx}
    (hm : MemoLOK f tbl st) (hk : tbl[k]? = some r) : RelL f st k st r := by
  intro u hu
  obtain ⟨u', h1, h2⟩ := hm k r hk
  rw [hu] at h1
  obtain rfl := Option.some.inj h1
  exact h2

theorem MemoLOK.insert {f : Level → Level} {tbl tbl' : Std.HashMap LIdx LIdx}
    {st : EStore} {k r : LIdx} (hm : MemoLOK f tbl st)
    (hc : tbl' = tbl.insert k r) (hk : (denoteL st.ls k).isSome = true)
    (hr : RelL f st k st r) : MemoLOK f tbl' st := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hk
  intro k' r' hk'
  rw [hc, Std.HashMap.getElem?_insert] at hk'
  split at hk'
  · rename_i hbeq
    cases hk'
    obtain rfl := eq_of_beq hbeq
    exact ⟨u, hu, hr u hu⟩
  · exact hm k' r' hk'

theorem MemoLsOK.mono {f : List Level → List Level}
    {tbl tbl' : Std.HashMap LsIdx LsIdx} {st st' : EStore}
    (hm : MemoLsOK f tbl st) (hx : Ext st st') (hc : tbl' = tbl) :
    MemoLsOK f tbl' st' := by
  intro k r hk
  rw [hc] at hk
  obtain ⟨us, h1, h2⟩ := hm k r hk
  exact ⟨us, denoteLs_ext h1 hx, denoteLs_ext h2 hx⟩

theorem MemoLsOK.of_empty {f : List Level → List Level}
    {tbl : Std.HashMap LsIdx LsIdx} {st : EStore} (h : tbl = ∅) :
    MemoLsOK f tbl st := by
  intro k r hk; rw [h] at hk; simp at hk

@[grind →] theorem MemoLsOK.get {f : List Level → List Level}
    {tbl : Std.HashMap LsIdx LsIdx} {st : EStore} {k r : LsIdx}
    (hm : MemoLsOK f tbl st) (hk : tbl[k]? = some r) : RelLs f st k st r := by
  intro us hus
  obtain ⟨us', h1, h2⟩ := hm k r hk
  rw [hus] at h1
  obtain rfl := Option.some.inj h1
  exact h2

theorem MemoLsOK.insert {f : List Level → List Level}
    {tbl tbl' : Std.HashMap LsIdx LsIdx} {st : EStore} {k r : LsIdx}
    (hm : MemoLsOK f tbl st) (hc : tbl' = tbl.insert k r)
    (hk : (denoteLs st.lss k).isSome = true) (hr : RelLs f st k st r) :
    MemoLsOK f tbl' st := by
  obtain ⟨us, hus⟩ := Option.isSome_iff_exists.mp hk
  intro k' r' hk'
  rw [hc, Std.HashMap.getElem?_insert] at hk'
  split at hk'
  · rename_i hbeq
    cases hk'
    obtain rfl := eq_of_beq hbeq
    exact ⟨us, hus, hr us hus⟩
  · exact hm k' r' hk'

/-! ### The ten tables, one `abbrev` each

Each fixes the generic `f` to a concrete lambda whose free variables are the
walk's own parameters and are all first-order (DESIGN `### Task #97b`,
finding 2).  The one table `Monad.lean` keys at cursor `0` (`instLPC`)
ignores the cursor in the lambda, which is what makes it one invariant with
the other six handle-valued tables. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:61-63 Inst1MemoInv. -/
abbrev Inst1MemoA (ve : Expr) (s : AState) : Prop :=
  MemoOK (fun d e => e.instantiate1 ve d) s.memos.inst1C s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:248-250 InstLMemoInv. -/
abbrev InstLMemoA (ws : List Expr) (s : AState) : Prop :=
  MemoOK (fun d e => e.instantiateList ws d) s.memos.instLC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:411-413 LiftMemoInv. -/
abbrev LiftMemoA (amount : Nat) (s : AState) : Prop :=
  MemoOK (fun c e => Expr.liftLooseBVars amount c e) s.memos.liftC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1772-1774 Abs1MemoInv. -/
abbrev Abs1MemoA (d : Nat) (s : AState) : Prop :=
  MemoOK (fun k e => Expr.abstract1 e d k) s.memos.abs1C s.store

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:383-414 instantiateLiftXP (its
memo, `MemoXP (instantiateLiftP vs)`). -/
abbrev InstLiftMemoA (ws : List Expr) (s : AState) : Prop :=
  MemoOK (fun d e => Expr.instantiateLift e ws d) s.memos.inst1LC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2546-2550 InstLPMemoInv, at
cursor `0`. -/
abbrev InstLPMemoA (ks : List ConLeche.Name) (us : List Level) (s : AState) :
    Prop :=
  MemoOK (fun _ e => e.instantiateLevelParams ks us) s.memos.instLPC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1497-1499 MemoBInv. -/
abbrev MemoBA (s : AState) : Prop :=
  MemoVOK Expr.bvarBound s.memos.bvarBC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1618-1620 MemoFInv. -/
abbrev MemoFA (s : AState) : Prop :=
  MemoVOK Expr.fvarRange s.memos.fvarBC s.store

/-- con-leche: ConLeche/Kernel/Level.lean:28-40 Level.subst — the LEVEL
substitution's own per-call memo (DESIGN `### Task #97-P6-13`). -/
abbrev InstLPLMemoA (ks : List ConLeche.Name) (us : List Level) (s : AState) :
    Prop :=
  MemoLOK (Level.subst ks us) s.memos.instLPLC s.store

/-- con-leche: ConLeche/Kernel/Level.lean:28-40 Level.subst — the same at a
universe-argument LIST handle, for `instLPGo`'s `.const` arm. -/
abbrev InstLPLsMemoA (ks : List ConLeche.Name) (us : List Level) (s : AState) :
    Prop :=
  MemoLsOK (fun vs => vs.map (Level.subst ks us)) s.memos.instLPLsC s.store

/-! ## The per-declaration caches

con-leche's `CacheOK` shape, verbatim: *every entry `i ↦ j` is backed by
expressions `a, b` with `denote i = some a`, `denote j = some b`, and a pure
run `∀ d, a.wscopedB d → … = .ok b` at some fuel.*  The `∃ F, ∀ d` is
**lesson 8**, and it is what makes a hit usable at the CALL's depth: the key
carries no ambient depth because a handle determines its own typing context
(an `fvar` node carries its type, DESIGN §8.3 "Free variables"). -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `whnfC` clause) — the
generic unary entry-point cache clause, at a fuel-indexed pure operation. -/
@[expose] def EntryCacheOK (op : Nat → Nat → Expr → CheckM Expr)
    (tbl : Std.HashMap EIdx EIdx) (st : EStore) : Prop :=
  ∀ (i j : EIdx), tbl[i]? = some j →
    ∃ a b, denoteE st i = some a ∧ denoteE st j = some b ∧
      ∃ F, ∀ d, Expr.wscopedB d a = true → op F d a = .ok b

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `defeqC` clause) — the
`defeq` verdict cache, BOTH SIGNS: the pure run at the fixed fuel answered
`r`, and the memo answers `r`.  This is what makes a negative memo sound. -/
@[expose] def DefeqCacheOK (op : Nat → Nat → Expr → Expr → CheckM Bool)
    (tbl : Std.HashMap (EIdx × EIdx) Bool) (st : EStore) : Prop :=
  ∀ (k : EIdx × EIdx) (r : Bool), tbl[k]? = some r →
    ∃ a b, denoteE st k.1 = some a ∧ denoteE st k.2 = some b ∧
      ∃ F, ∀ d, Expr.wscopedB d a = true → Expr.wscopedB d b = true →
        op F d a b = .ok r

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `lsimp`/`eqv` clauses) —
the level-verdict cache: a recorded verdict is `Level.isEquiv`'s. -/
@[expose] def LvlEqCacheOK (tbl : Std.HashMap (LIdx × LIdx) Bool) (st : EStore) : Prop :=
  ∀ (k : LIdx × LIdx) (r : Bool), tbl[k]? = some r →
    ∃ u v, denoteL st.ls k.1 = some u ∧ denoteL st.ls k.2 = some v ∧
      Level.isEquiv u v = some r

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the same at two
universe-argument lists. -/
@[expose] def LvlsEqCacheOK (tbl : Std.HashMap (LsIdx × LsIdx) Bool) (st : EStore) :
    Prop :=
  ∀ (k : LsIdx × LsIdx) (r : Bool), tbl[k]? = some r →
    ∃ us vs, denoteLs st.lss k.1 = some us ∧ denoteLs st.lss k.2 = some vs ∧
      Level.isEquivList us vs = some r

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `constTy` clause) — a
row of the lazy instantiated-constant TYPE cache is the environment's own
constant at the key's universe arguments.  The environment is what makes the
key `(name, levels)` determine the subject; without it the clause would be
vacuous (`Arena/Core.lean`'s `constTyAt` takes the subject as an argument). -/
@[expose] def ConstTyCacheOK (env : Env) (tbl : Std.HashMap (NIdx × LsIdx) EIdx)
    (st : EStore) : Prop :=
  ∀ (k : NIdx × LsIdx) (i : EIdx), tbl[k]? = some i →
    ∃ nm ls ci, denoteN st.ns k.1 = some nm ∧ denoteLs st.lss k.2 = some ls ∧
      env.find? nm = some ci ∧
      denoteE st i = some (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams ls)

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the same for a stored
definition's VALUE.  The environment entry must be one that HAS a value, so
the clause names it. -/
@[expose] def ConstValCacheOK (env : Env) (tbl : Std.HashMap (NIdx × LsIdx) EIdx)
    (st : EStore) : Prop :=
  ∀ (k : NIdx × LsIdx) (i : EIdx), tbl[k]? = some i →
    ∃ nm ls cv value hint,
      denoteN st.ns k.1 = some nm ∧ denoteLs st.lss k.2 = some ls ∧
      env.find? nm = some (.defnInfo cv value hint) ∧
      denoteE st i = some (value.instantiateLevelParams cv.levelParams ls)

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — an iota rule's
right-hand side at the recursor's universe instantiation.  The key's three
data determine the subject through the environment: the recursor's stored
rules, the rule whose constructor is the key's second name, and that rule's
`rhs`. -/
@[expose] def RuleRhsCacheOK (env : Env) (tbl : Std.HashMap (NIdx × NIdx × LsIdx) EIdx)
    (st : EStore) : Prop :=
  ∀ (k : NIdx × NIdx × LsIdx) (i : EIdx), tbl[k]? = some i →
    ∃ rn cn ls cv mi rp isK rules rl,
      denoteN st.ns k.1 = some rn ∧ denoteN st.ns k.2.1 = some cn ∧
      denoteLs st.lss k.2.2 = some ls ∧
      env.find? rn = some (.recInfo cv mi rp isK rules) ∧
      rules.find? (fun r => r.ctor == cn) = some rl ∧
      denoteE st i = some (rl.rhs.instantiateLevelParams cv.levelParams ls)

/-- con-leche: none — the READBACK memos (DESIGN `### Task #97-P6-13`) are
the identity on the denotation, so their clause is an equation and not a
simulation. -/
@[expose] def ReadLCacheOK (tbl : Std.HashMap LIdx Level) (st : EStore) : Prop :=
  ∀ (k : LIdx) (u : Level), tbl[k]? = some u → denoteL st.ls k = some u

/-- con-leche: none — the same for a NAME handle. -/
@[expose] def ReadNCacheOK (tbl : Std.HashMap NIdx ConLeche.Name) (st : EStore) : Prop :=
  ∀ (k : NIdx) (x : ConLeche.Name), tbl[k]? = some x → denoteN st.ns k = some x

/-- con-leche: none — the same for an interned universe-argument list. -/
@[expose] def ReadLsCacheOK (tbl : Std.HashMap LsIdx (List Level)) (st : EStore) :
    Prop :=
  ∀ (k : LsIdx) (us : List Level), tbl[k]? = some us →
    denoteLs st.lss k = some us

/-- con-leche: ConLeche/Verify/Cached/SimC.lean ModeMemosOK — the six
mode-dependent tables of a `ModeMemos` set, valid at `.verified` over the store
`st`: `CacheOK`'s first six clauses, for the eager tower's stored set
(`CacheOK.eager`, at `eager := true`). -/
structure ModeMemosOK (eager : Bool) (env : Env) (mm : ModeMemos) (st : EStore) :
    Prop where
  whnfCore : EntryCacheOK (ConLeche.whnfCore .verified eager env) mm.whnfCoreC st
  whnfCoreCheap : EntryCacheOK (fun F d e => ConLeche.whnfCore .verified eager env F d e true)
    mm.whnfCoreCheapC st
  whnf : EntryCacheOK (ConLeche.whnf .verified eager env) mm.whnfC st
  infer : EntryCacheOK (ConLeche.inferTypeCore .verified eager env) mm.inferC st
  inferIO : EntryCacheOK (ConLeche.inferTypeIO .verified eager env) mm.inferIOC st
  defeq : DefeqCacheOK (ConLeche.isDefEqCore .verified eager env) mm.defeqC st

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the fourteen
per-declaration tables of `Caches`, in one record, at the pure knot the
bridge's Theorem 1 is stated against (`pureFns .verified eager env F`, con-leche's
`ConLeche/Kernel/TypeChecker.lean`), and the eager tower's stored set at
`eager := true` (con-leche's `CSOK.eager`). -/
structure CacheOK (eager : Bool) (env : Env) (s : AState) : Prop where
  whnfCore : EntryCacheOK (ConLeche.whnfCore .verified eager env) s.caches.whnfCoreC s.store
  /-- The cheap-projection mode's own table (con-leche `whnfCoreCheapC`). -/
  whnfCoreCheap : EntryCacheOK (fun F d e => ConLeche.whnfCore .verified eager env F d e true)
    s.caches.whnfCoreCheapC s.store
  whnf : EntryCacheOK (ConLeche.whnf .verified eager env) s.caches.whnfC s.store
  infer : EntryCacheOK (ConLeche.inferTypeCore .verified eager env) s.caches.inferC s.store
  inferIO : EntryCacheOK (ConLeche.inferTypeIO .verified eager env) s.caches.inferIOC s.store
  defeq : DefeqCacheOK (ConLeche.isDefEqCore .verified eager env) s.caches.defeqC s.store
  lvlEq : LvlEqCacheOK s.caches.lvlEqC s.store
  lvlsEq : LvlsEqCacheOK s.caches.lvlsEqC s.store
  constTy : ConstTyCacheOK env s.caches.constTyC s.store
  constVal : ConstValCacheOK env s.caches.constValC s.store
  ruleRhs : RuleRhsCacheOK env s.caches.ruleRhsC s.store
  readL : ReadLCacheOK s.caches.readLC s.store
  readN : ReadNCacheOK s.caches.readNC s.store
  readLs : ReadLsCacheOK s.caches.readLsC s.store
  /-- The eager tower's stored memos are backed by runs at `eager := true`,
  the mode the `defeqE` slot runs them at. -/
  eager : ModeMemosOK true env s.caches.eagerMemos s.store

/-! ## The pin table -/

/-- con-leche: none — a list of name handles denotes a list of names,
pointwise. -/
@[expose] def denoteNL (st : EStore) : List NIdx → List ConLeche.Name → Prop
  | [], [] => True
  | h :: hs, x :: xs => denoteN st.ns h = some x ∧ denoteNL st hs xs
  | _, _ => False

/-- con-leche: none — **the pin table denotes** (DESIGN
`### Task #97-P6-4a`): the fifty `PIN_*` slots hold handles for `pinNames`, the
reserved-basis list holds handles for `reservedBasisNameValues`, and the three
nullary values denote `[]`, `Level.zero` and `Sort 1`.  `pinsReady` is the
executable half of the first conjunct and is what makes an early read a stop
rather than a wrong answer. -/
structure PinsOK (s : AState) : Prop where
  ready : s.pins.names.size = pinCount
  names : denoteNL s.store s.pins.names.toList pinNames
  reserved : denoteNL s.store s.pins.reserved reservedBasisNameValues
  emptyLevels : denoteLs s.store.lss s.pins.emptyLevels = some []
  zeroLevel : denoteL s.store.ls s.pins.zeroLevel = some .zero
  sortOne : denoteE s.store s.pins.sortOne = some (.sort (.succ .zero))
  /-- **the ZERO name handle decodes, and it decodes to `.anonymous`**.

  The clause is EXACT rather than a weakening.  `.anonymous` is nullary, so
  the persistent name store's `anons` table holds at most one element, at slot
  0; `Idx.ofWord 0` is tag-`anonymous`, tier-persistent, slot 0.  So as soon
  as `.anonymous` is interned at all its handle IS the zero word, exactly and
  permanently — and it is interned, because every pin name is a `.str`/`.num`
  chain that bottoms out there.  False of `EStore.empty` and true after the
  pin phase, which is what `PinsOK` is for; `Bridge/Checker/Pins.lean`'s
  `internReservedPins_run` is the debtor. -/
  anon : denoteN s.store.ns (default : NIdx) = some ConLeche.Name.anonymous

/-! ## The environment index

DESIGN §8.3, lesson 13: "The environment index is `HashMap NIdx
IConstantInfo` with an **unconditional** spec `find? = denoteEnv.find?`".
Stated at the denoted `ConstantInfo`, so that the Core tier's every
`fe.find?` is one rewrite. -/

/-- con-leche: ConLeche/Verify/EnvWF.lean:161 TableWF (the size clause) —
**what a STORED projection table satisfies**, over the ARENA's `IProjTable`
and not over con-leche's `ProjTable`: the body column has `numFields`
entries.  `denoteProjTable` transports it pointwise and copies
`numFields` verbatim, so the pure table's sizes ARE ours — which is why
con-leche's own invariant is the wrong place to take this from (a simulation
B ⇒ A takes invariants on the REFINED side only).  Its debtor is the table
install (`Bridge/Inductives/StructInstall.lean`). -/
structure IProjTableOK (t : IProjTable) : Prop where
  bodies : t.bodies.size = t.numFields

/-- con-leche: ConLeche/Kernel/FEnv.lean:189-218 FEnv (the proof fields
`natLit_eq`, `strLit_eq`) — **the index's literal flags are its lookups'**:
`natLitStoredBy`/`strLitStoredBy` over the base's literal names.  con-leche
makes it a proof field; the twin's `IFEnv` is plain data, so it is an invariant
here, kept by every operation that makes or moves an index
(`Bridge/Checker/Inv.lean`'s `FlagsOK.push` and siblings). -/
structure FlagsOK (fe : IFEnv) : Prop where
  nat : fe.natLit = fe.natLitStoredBy
  str : fe.strLit = fe.strLitStoredBy

/-- con-leche: ConLeche/Kernel/FEnv.lean:57-60 strLitNames — **the base's
literal names denote con-leche's ten**, in order: what the flags' lookups at
handles (`FlagsOK`) mean at names. -/
@[expose] def LitsOK (b : IFBase) (st : EStore) : Prop :=
  b.lits.map (denoteN st.ns) = ConLeche.strLitNames.map some

/-- con-leche: ConLeche/Kernel/FEnv.lean:98-105 FEnv.lookup — the emptiness test
answers what the hash map answers. -/
theorem IFEnv.find?_eq (fe : IFEnv) (n : NIdx) :
    fe.find? n = match fe.idx[n]? with
      | some ci => some ci
      | none => fe.base.find? n := by
  simp only [IFEnv.find?, IFEnv.lookup]
  split
  · rename_i he
    rw [Std.HashMap.isEmpty_iff_forall_not_mem] at he
    have : fe.idx[n]? = none := Std.HashMap.getElem?_eq_none (he n)
    rw [this]
  · rfl

/-- con-leche: none — `litsStored` reads the base's literal names and the lookups at them only. -/
theorem IFEnv.litsStored_congr {fe fe' : IFEnv} (hb : fe'.base.lits = fe.base.lits)
    (hf : ∀ n ∈ fe.base.lits, fe'.find? n = fe.find? n) (i stop : Nat) :
    fe'.litsStored i stop = fe.litsStored i stop := by
  rw [IFEnv.litsStored.eq_1 fe', IFEnv.litsStored.eq_1 fe]
  by_cases hi : i ≥ stop
  · simp [hi]
  · simp only [hi, ite_false]
    by_cases hl : i < fe.base.lits.length
    · have hl' : i < fe'.base.lits.length := hb ▸ hl
      rw [dite_eq_left hl', dite_eq_left hl]
      have he : fe'.base.lits[i] = fe.base.lits[i] := List.getElem_of_eq hb hl'
      rw [he, hf _ (List.getElem_mem hl)]
      split
      · exact IFEnv.litsStored_congr hb hf (i + 1) stop
      · rfl
    · have hl' : ¬ i < fe'.base.lits.length := hb ▸ hl
      rw [dite_eq_right hl', dite_eq_right hl]
termination_by stop - i

/-- con-leche: none — Every lookup that answers still answers: the stored names stay stored. -/
theorem IFEnv.litsStored_mono {fe fe' : IFEnv} (hb : fe'.base.lits = fe.base.lits)
    (hf : ∀ n, (fe.find? n).isSome → (fe'.find? n).isSome) (i stop : Nat)
    (h : fe.litsStored i stop = true) : fe'.litsStored i stop = true := by
  rw [IFEnv.litsStored.eq_1] at h ⊢
  by_cases hi : i ≥ stop
  · simp [hi]
  · simp only [hi, ite_false] at h ⊢
    by_cases hl : i < fe.base.lits.length
    · have hl' : i < fe'.base.lits.length := hb ▸ hl
      rw [dite_eq_left hl] at h
      rw [dite_eq_left hl']
      have he : fe'.base.lits[i] = fe.base.lits[i] := List.getElem_of_eq hb hl'
      rw [he]
      cases hfi : fe.find? fe.base.lits[i] with
      | none => rw [hfi] at h; simp at h
      | some c =>
        rw [hfi] at h
        simp only at h
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (hf _ (by rw [hfi]; rfl))
        rw [hc']
        exact IFEnv.litsStored_mono hb hf (i + 1) stop h
    · rw [dite_eq_right hl] at h; simp at h
termination_by stop - i

/-- con-leche: none — A lookup reads the own index's row and the base. -/
theorem IFEnv.find?_congr {fe fe' : IFEnv} {n : NIdx} (hb : fe'.base = fe.base)
    (hi : fe'.idx[n]? = fe.idx[n]?) : fe'.find? n = fe.find? n := by
  rw [IFEnv.find?_eq, IFEnv.find?_eq, hi, hb]

/-- con-leche: none — the literal names in two runs, `[i, mid)` then `[mid, stop)`. -/
theorem IFEnv.litsStored_split (fe : IFEnv) {i mid stop : Nat} (h1 : i ≤ mid) (h2 : mid ≤ stop) :
    fe.litsStored i stop = (fe.litsStored i mid && fe.litsStored mid stop) := by
  by_cases he : i = mid
  · subst he
    rw [IFEnv.litsStored.eq_1 fe i i]; simp
  · have hlt : i < mid := Nat.lt_of_le_of_ne h1 he
    rw [IFEnv.litsStored.eq_1 fe i stop, IFEnv.litsStored.eq_1 fe i mid,
      ite_eq_right (by omega), ite_eq_right (by omega)]
    by_cases hl : i < fe.base.lits.length
    · rw [dite_eq_left hl, dite_eq_left hl]
      cases fe.find? fe.base.lits[i] with
      | none => rfl
      | some _ => exact IFEnv.litsStored_split fe (by omega) h2
    · rw [dite_eq_right hl, dite_eq_right hl]; rfl
termination_by mid - i

/-- con-leche: none — Two indices with the same own rows and base answer the same literal lookups. -/
theorem IFEnv.litsStored_same {fe fe' : IFEnv} (hi : fe'.idx = fe.idx) (hb : fe'.base = fe.base)
    (i stop : Nat) : fe'.litsStored i stop = fe.litsStored i stop :=
  IFEnv.litsStored_congr (by rw [hb]) (fun _ _ => IFEnv.find?_congr hb (by rw [hi])) i stop

/-- con-leche: none — `litsStored` as a function of the own rows and the base only, so that `simp` can compare
the lookups of two indices that differ in their flags or their constant list. -/
@[irreducible] def litsStoredOn (idx : Std.HashMap NIdx IConstantInfo) (base : IFBase)
    (i stop : Nat) : Bool :=
  (IFEnv.mk ⟨[], []⟩ idx base ∅ false false).litsStored i stop

@[simp] theorem IFEnv.litsStored_on (fe : IFEnv) (i stop : Nat) :
    fe.litsStored i stop = litsStoredOn fe.idx fe.base i stop := by
  unfold litsStoredOn
  exact (IFEnv.litsStored_same (fe := fe) (fe' := IFEnv.mk ⟨[], []⟩ fe.idx fe.base ∅ false false)
    rfl rfl i stop).symm

/-- con-leche: none — **Flags recomputed are the lookups'.** -/
theorem FlagsOK.recompute (fe1 : IFEnv) :
    FlagsOK { ({ fe1 with natLit := fe1.natLitStoredBy } : IFEnv) with
      strLit := ({ fe1 with natLit := fe1.natLitStoredBy } : IFEnv).strLitStoredBy } :=
  ⟨by simp [IFEnv.natLitStoredBy], by simp [IFEnv.strLitStoredBy, IFEnv.natLitStoredBy]⟩

/-- con-leche: none — `litNameAt` from `i` on is a membership test of the rest of the list. -/
theorem litNameAt_false {lits : List NIdx} {n : NIdx} :
    ∀ {i : Nat}, litNameAt lits n i = false → ∀ j (hj : j < lits.length), i ≤ j → lits[j] ≠ n := by
  intro i h j hj hij
  rw [litNameAt.eq_1] at h
  have hi : i < lits.length := Nat.lt_of_le_of_lt hij hj
  rw [dite_eq_left hi] at h
  by_cases he : lits[i] == n
  · rw [ite_eq_left he] at h; cases h
  · rw [ite_eq_right he] at h
    rcases Nat.lt_or_eq_of_le hij with hlt | rfl
    · exact litNameAt_false h j hj hlt
    · simpa using he
termination_by i => lits.length - i

theorem litNameAt_false_mem {lits : List NIdx} {n : NIdx} (h : litNameAt lits n 0 = false) :
    ∀ m ∈ lits, m ≠ n := by
  intro m hm
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
  exact litNameAt_false h j hj (Nat.zero_le _)

/-- con-leche: none — `strLitStoredBy` holding, `natLitStoredBy` holds. -/
theorem IFEnv.natLitStoredBy_of_str {fe : IFEnv} (h : fe.strLitStoredBy = true) :
    fe.natLitStoredBy = true := by
  rw [IFEnv.strLitStoredBy] at h
  exact (Bool.and_eq_true _ _ ▸ h).1

/-- con-leche: none — **The flags are a push's lookups'**: recomputed at a literal name before string literals
are expandable; otherwise no lookup they read changed (`litNameAt`), or both hold and a push only
adds answers (con-leche's `push_flags`). -/
theorem FlagsOK.push {fe : IFEnv} (h : FlagsOK fe) (ci : IConstantInfo) : FlagsOK (fe.push ci) := by
  let fe1 : IFEnv := ⟨⟨ci :: fe.env.consts, fe.env.tables⟩, fe.idx.insert ci.name ci,
    fe.base, fe.tbls, fe.natLit, fe.strLit⟩
  have hf1 : ∀ n, fe1.find? n = if (ci.name == n) = true then some ci else fe.find? n := by
    intro n
    rw [IFEnv.find?_eq, IFEnv.find?_eq]
    simp only [fe1, Std.HashMap.getElem?_insert]
    by_cases hb : (ci.name == n) = true <;> simp [hb]
  unfold IFEnv.push
  by_cases hre : (!fe.strLit && litNameAt fe.base.lits ci.name 0) = true
  · rw [ite_eq_left hre]
    exact FlagsOK.recompute _
  · rw [ite_eq_right hre]
    show FlagsOK fe1
    cases hs : fe.strLit
    · -- no literal name pushed: the lookups the flags read are the old ones
      have hn : litNameAt fe.base.lits ci.name 0 = false := by simpa [hs] using hre
      have hc : ∀ n ∈ fe.base.lits, fe1.find? n = fe.find? n := by
        intro n hm
        rw [hf1, ite_eq_right (by simpa using (litNameAt_false_mem hn n hm).symm)]
      have hl := IFEnv.litsStored_congr (fe := fe) (fe' := fe1) rfl hc
      exact ⟨by rw [IFEnv.natLitStoredBy, hl]; exact h.nat,
        by rw [IFEnv.strLitStoredBy, IFEnv.natLitStoredBy, hl, hl]; exact hs ▸ h.str⟩
    · -- string literals expandable: both hold, and a push only adds answers
      have hstr : fe.strLitStoredBy = true := h.str ▸ hs
      have hnat : fe.natLitStoredBy = true := IFEnv.natLitStoredBy_of_str hstr
      have hm : ∀ n, (fe.find? n).isSome → (fe1.find? n).isSome := by
        intro n hn
        rw [hf1]; split
        · rfl
        · exact hn
      have hn1 : fe1.natLitStoredBy = true :=
        IFEnv.litsStored_mono (fe := fe) (fe' := fe1) rfl hm 0 NAT_LIT_COUNT hnat
      have hs1 : fe1.strLitStoredBy = true := by
        rw [IFEnv.strLitStoredBy] at hstr ⊢
        rw [Bool.and_eq_true] at hstr ⊢
        exact ⟨hn1, IFEnv.litsStored_mono (fe := fe) (fe' := fe1) rfl hm _ _ hstr.2⟩
      exact ⟨by show fe.natLit = _; rw [h.nat, hnat, hn1], by show fe.strLit = _; rw [hs, hs1]⟩

/-- con-leche: none — A table push moves no lookup. -/
theorem FlagsOK.pushTable {fe : IFEnv} (h : FlagsOK fe) (t : IProjTable) :
    FlagsOK (fe.pushTable t) := by
  have hl := IFEnv.litsStored_congr (fe := fe) (fe' := fe.pushTable t) rfl
    (fun n _ => IFEnv.find?_congr rfl rfl)
  exact ⟨by rw [IFEnv.natLitStoredBy, hl]; exact h.nat,
    by rw [IFEnv.strLitStoredBy, IFEnv.natLitStoredBy, hl, hl]; exact h.str⟩

/-- con-leche: none — **flags carried to an index answering alike**: the same literal names,
the same lookups, the same flags. -/
theorem FlagsOK.of_same {fe fe0 : IFEnv} (h : FlagsOK fe0) (hb : fe.base.lits = fe0.base.lits)
    (hf : ∀ n, fe.find? n = fe0.find? n) (hn : fe.natLit = fe0.natLit)
    (hs : fe.strLit = fe0.strLit) : FlagsOK fe := by
  have hl := IFEnv.litsStored_congr (fe := fe0) (fe' := fe) hb (fun n _ => hf n)
  exact ⟨by rw [IFEnv.natLitStoredBy, hl, hn]; exact h.nat,
    by rw [IFEnv.strLitStoredBy, IFEnv.natLitStoredBy, hl, hl, hs]; exact h.str⟩

/-- con-leche: none — An index from its components carries its lookups' flags. -/
theorem FlagsOK.ofParts (env : IEnv) (idx : Std.HashMap NIdx IConstantInfo) (base : IFBase)
    (tbls : Std.HashMap NIdx IProjTable) : FlagsOK (IFEnv.ofParts env idx base tbls) :=
  ⟨by simp [IFEnv.ofParts, IFEnv.natLitStoredBy], by
    simp [IFEnv.ofParts, IFEnv.strLitStoredBy, IFEnv.natLitStoredBy]⟩


/-- con-leche: ConLeche/Kernel/FEnv.lean:78-100 FBase.fromLe_litFrom — **a view of the frozen
layer holds the literal names exactly from `litFrom` on**: the threshold's comparison is the
view's lookups. -/
theorem fromLe_litFrom (e : IEnv) (t : Std.HashMap NIdx IProjTable) (x y : Bool) (b : IFBase)
    (i stop : Nat) :
    Arena.fromLe (Arena.litFrom b.idx b.lits i stop) b.below = (IFEnv.mk e ∅ b t x y).litsStored i stop := by
  rw [Arena.litFrom.eq_1, IFEnv.litsStored.eq_1]
  by_cases hi : i ≥ stop
  · simp [hi, Arena.fromLe]
  · simp only [hi, ite_false]
    by_cases hl : i < b.lits.length
    · rw [dite_eq_left hl]
      rw [dite_eq_left (show i < (IFEnv.mk e ∅ b t x y).base.lits.length from hl)]
      have hf : (IFEnv.mk e ∅ b t x y).find? b.lits[i] = b.find? b.lits[i] := by
        rw [IFEnv.find?_eq]; simp
      show _ = (match (IFEnv.mk e ∅ b t x y).find? b.lits[i] with
        | some _ => _ | none => false)
      rw [hf]
      have ih := fromLe_litFrom e t x y b (i + 1) stop
      simp only [IFBase.find?]
      cases hc : b.idx[b.lits[i]]? with
      | none => simp [Arena.fromLe]
      | some p =>
        obtain ⟨c, ci⟩ := p
        simp only
        cases hr : Arena.litFrom b.idx b.lits (i + 1) stop with
        | none =>
          rw [hr] at ih
          by_cases hlt : c < b.below
          · simp only [hlt, ite_true]; exact ih
          · simp [hlt, Arena.fromLe]
        | some k =>
          rw [hr] at ih
          by_cases hlt : c < b.below
          · simp only [hlt, ite_true]
            rw [← ih]
            by_cases hk : c + 1 ≤ k
            · simp only [hk, ite_true]
            · simp only [hk, ite_false, Arena.fromLe, decide_eq_decide]; omega
          · simp only [hlt, ite_false]
            by_cases hk : c + 1 ≤ k
            · simp only [hk, ite_true, Arena.fromLe, decide_eq_false_iff_not]; omega
            · simp only [hk, ite_false, Arena.fromLe, decide_eq_false_iff_not]; omega
    · rw [dite_eq_right hl, dite_eq_right (show ¬ i < (IFEnv.mk e ∅ b t x y).base.lits.length from hl)]
      rfl
termination_by stop - i

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `ienv` clause) — the
index answers exactly what the denoted environment answers, and its literal
flags are its lookups' at handles that denote the literal names (`FlagsOK`,
`LitsOK`), so that they are `natLitStored`/`strLitStored` of the environment
(`IFEnvOK.natLit_eq`, `IFEnvOK.strLit_eq`).

**Two clauses, and the second is `cover` rather than `miss`.**  The naive
spelling of the second direction — "a `find?` miss at a handle that denotes
`nm` means `env.find? nm = none`" — is NOT preserved by an arena extension,
because a handle that decoded to nothing before the extension may decode to
`nm` after it and the hypothesis then says nothing about `env`.  `cover`
("every entry of the environment is named by a handle the index knows") IS
preserved (its witnesses' denotations transport), and `IFEnvOK.miss` below
derives the naive form from it through `denoteN_inj` — which is exactly the
role DESIGN §8.3 lesson 13 gives injectivity. -/
structure IFEnvOK (env : Env) (fe : IFEnv) (s : AState) : Prop where
  hit : ∀ n ci, fe.find? n = some ci →
    ∃ nm c, denoteN s.store.ns n = some nm ∧
      Frontend.denoteCI s.store ci = some c ∧ env.find? nm = some c
  cover : ∀ nm c, env.find? nm = some c →
    ∃ n ci, denoteN s.store.ns n = some nm ∧ fe.find? n = some ci ∧
      Frontend.denoteCI s.store ci = some c
  /-- **the table lookup answers what the environment's table lookup
  answers**, both gated by their structure's lookup (`IFEnv.findTable?`,
  `Env.findTable?`), so that a prefix view hides a table by hiding its
  structure on both sides — and a table the index answers with is well shaped
  (`IProjTableOK`).  `tblCover` is `cover`'s twin. -/
  tblHit : ∀ n t, fe.findTable? n = some t →
    ∃ nm pt, denoteN s.store.ns n = some nm ∧
      Frontend.denoteProjTable s.store t = some pt ∧ env.findTable? nm = some pt ∧
      IProjTableOK t
  tblCover : ∀ nm pt, env.findTable? nm = some pt →
    ∃ n t, denoteN s.store.ns n = some nm ∧ fe.findTable? n = some t ∧
      Frontend.denoteProjTable s.store t = some pt
  /-- the literal flags are the index's lookups' -/
  flags : FlagsOK fe
  /-- at handles that denote the literal names -/
  lits : LitsOK fe.base s.store

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the index's MISS half,
derived: a handle the index does not know cannot denote a name the
environment knows.  `denoteN_inj` is what makes the two handles one. -/
theorem IFEnvOK.miss {env : Env} {fe : IFEnv} {s : AState}
    (hok : StateOK s) (h : IFEnvOK env fe s) {n : NIdx} {nm : ConLeche.Name}
    (hd : denoteN s.store.ns n = some nm) (hf : fe.find? n = none) :
    env.find? nm = none := by
  cases he : env.find? nm with
  | none => rfl
  | some c =>
    obtain ⟨n', ci, hd', hf', _⟩ := h.cover nm c he
    obtain ⟨rk, hrk⟩ := hok.wf
    obtain rfl := denoteN_inj hrk.nsWF hd hd'
    rw [hf] at hf'
    exact absurd hf' (by simp)

/-- con-leche: none — the literal names' denotations survive the arena's
growth. -/
theorem LitsOK.mono {b : IFBase} {st st' : EStore} (h : LitsOK b st) (hx : Ext st st') :
    LitsOK b st' := by
  unfold LitsOK at h ⊢
  rw [← h]
  apply List.map_congr_left
  intro n hn
  cases hd : denoteN st.ns n with
  | none =>
    exfalso
    have : (none : Option ConLeche.Name) ∈ ConLeche.strLitNames.map some := by
      rw [← h]; exact List.mem_map.mpr ⟨n, hn, hd⟩
    simp at this
  | some nm => exact denoteN_ext hd hx

/-- con-leche: none — a lookup at a handle that denotes a name answers exactly
when the environment does (`hit`, and `IFEnvOK.miss`). -/
theorem IFEnvOK.isSome_find {env : Env} {fe : IFEnv} {s : AState}
    (hok : StateOK s) (h : IFEnvOK env fe s) {n : NIdx} {nm : ConLeche.Name}
    (hd : denoteN s.store.ns n = some nm) : (fe.find? n).isSome = (env.find? nm).isSome := by
  cases hf : fe.find? n with
  | none => rw [IFEnvOK.miss hok h hd hf]; rfl
  | some ci =>
    obtain ⟨nm', c, hd', -, he⟩ := h.hit n ci hf
    rw [hd] at hd'
    obtain rfl := Option.some.inj hd'
    rw [he]; rfl

/-- con-leche: none — one step of `litsStored` at a known literal handle. -/
theorem IFEnv.litsStored_step (fe : IFEnv) {i stop : Nat} {h : NIdx} (hi : i < stop)
    (hl : fe.base.lits[i]? = some h) :
    fe.litsStored i stop = ((fe.find? h).isSome && fe.litsStored (i + 1) stop) := by
  rw [IFEnv.litsStored.eq_1, ite_eq_right (by omega)]
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hl
  rw [dite_eq_left hlt, he]
  cases fe.find? h <;> rfl

/-- con-leche: none — `litsStored` over no names. -/
theorem IFEnv.litsStored_self (fe : IFEnv) (i : Nat) : fe.litsStored i i = true := by
  rw [IFEnv.litsStored.eq_1, ite_eq_left (Nat.le_refl i)]

/-- con-leche: ConLeche/Kernel/FEnv.lean:57-60 strLitNames — **the ten literal
handles**, one per name, read off `LitsOK`. -/
theorem LitsOK.ten {b : IFBase} {st : EStore} (h : LitsOK b st) :
    ∃ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, b.lits = [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] ∧
      denoteN st.ns h0 = some natName ∧ denoteN st.ns h1 = some natZeroName ∧
      denoteN st.ns h2 = some natSuccName ∧ denoteN st.ns h3 = some stringName ∧
      denoteN st.ns h4 = some stringOfListName ∧ denoteN st.ns h5 = some listName ∧
      denoteN st.ns h6 = some listNilName ∧ denoteN st.ns h7 = some listConsName ∧
      denoteN st.ns h8 = some charName ∧ denoteN st.ns h9 = some charOfNatName := by
  unfold LitsOK at h
  generalize b.lits = l at h ⊢
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7,
    _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [ConLeche.strLitNames, ConLeche.natLitNames] at h
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := h
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, rfl, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩

/-- con-leche: ConLeche/Verify/EnvBound.lean:96 mkFEnv_natLit — **the index's
`Nat`-literal flag is `natLitStored` of its environment**. -/
theorem IFEnvOK.natLit_eq {env : Env} {fe : IFEnv} {s : AState}
    (hok : StateOK s) (h : IFEnvOK env fe s) : fe.natLit = ConLeche.natLitStored env := by
  obtain ⟨h0, h1, h2, _, _, _, _, _, _, _, hb, d0, d1, d2, _⟩ := h.lits.ten
  rw [h.flags.nat, IFEnv.natLitStoredBy, NAT_LIT_COUNT, ConLeche.natLitStored,
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl), IFEnv.litsStored_self,
    IFEnvOK.isSome_find hok h d0, IFEnvOK.isSome_find hok h d1,
    IFEnvOK.isSome_find hok h d2, Bool.and_true, Bool.and_assoc]

/-- con-leche: ConLeche/Verify/EnvBound.lean:102 mkFEnv_strLit — **the index's
string-literal flag is `strLitStored` of its environment**. -/
theorem IFEnvOK.strLit_eq {env : Env} {fe : IFEnv} {s : AState}
    (hok : StateOK s) (h : IFEnvOK env fe s) : fe.strLit = ConLeche.strLitStored env := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hb, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
    h.lits.ten
  rw [h.flags.str, IFEnv.strLitStoredBy, IFEnv.natLitStoredBy, NAT_LIT_COUNT, STR_LIT_COUNT,
    ConLeche.strLitStored, ConLeche.natLitStored,
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl), IFEnv.litsStored_self,
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hb]; rfl), IFEnv.litsStored_self,
    IFEnvOK.isSome_find hok h d0, IFEnvOK.isSome_find hok h d1,
    IFEnvOK.isSome_find hok h d2, IFEnvOK.isSome_find hok h d3,
    IFEnvOK.isSome_find hok h d4, IFEnvOK.isSome_find hok h d5,
    IFEnvOK.isSome_find hok h d6, IFEnvOK.isSome_find hok h d7,
    IFEnvOK.isSome_find hok h d8, IFEnvOK.isSome_find hok h d9]
  simp only [Bool.and_true, Bool.and_assoc]

/-! ## The whole invariant, and what carries it -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the checker's state
invariant: the store, the fourteen per-declaration caches, the pin table and
the environment index.  The `ExprOps` tier does not mention it (it mentions
`StateOK` alone); the Core tier does. -/
structure CheckOK (eager : Bool) (env : Env) (fe : IFEnv) (s : AState) :
    Prop where
  state : StateOK s
  caches : CacheOK eager env s
  pins : PinsOK s
  ienv : IFEnvOK env fe s

/-- con-leche: ConLeche/Verify/EnvBound.lean:96 mkFEnv_natLit — the index's
`Nat`-literal flag, at a checking state: `natLitStored` of the environment. -/
theorem CheckOK.natLitEq {eager : Bool} {env : Env} {fe : IFEnv} {s : AState}
    (h : CheckOK eager env fe s) : fe.natLit = ConLeche.natLitStored env :=
  h.ienv.natLit_eq h.state

/-- con-leche: ConLeche/Verify/EnvBound.lean:102 mkFEnv_strLit — the index's
string-literal flag, at a checking state: `strLitStored` of the environment. -/
theorem CheckOK.strLitEq {eager : Bool} {env : Env} {fe : IFEnv} {s : AState}
    (h : CheckOK eager env fe s) : fe.strLit = ConLeche.strLitStored env :=
  h.ienv.strLit_eq h.state

/-! ### Transport

`CheckOK.mono` is what the `ExprOps` tier's frame conditions buy: a call that
only GROWS the arena and leaves `caches` and `pins` alone preserves the whole
invariant.  This is con-leche's `flushS_isok`/`ISOKF.residue` pair played the
other way round — there the environment moved and the store stood still, here
the store moves and the environment stands still. -/

theorem EntryCacheOK.mono {op : Nat → Nat → Expr → CheckM Expr}
    {tbl : Std.HashMap EIdx EIdx} {st st' : EStore} (h : EntryCacheOK op tbl st)
    (hx : Ext st st') : EntryCacheOK op tbl st' := by
  intro i j hk
  obtain ⟨a, b, h1, h2, hF⟩ := h i j hk
  exact ⟨a, b, denote_ext h1 hx, denote_ext h2 hx, hF⟩

theorem DefeqCacheOK.mono {op : Nat → Nat → Expr → Expr → CheckM Bool}
    {tbl : Std.HashMap (EIdx × EIdx) Bool} {st st' : EStore}
    (h : DefeqCacheOK op tbl st) (hx : Ext st st') :
    DefeqCacheOK op tbl st' := by
  intro k r hk
  obtain ⟨a, b, h1, h2, hF⟩ := h k r hk
  exact ⟨a, b, denote_ext h1 hx, denote_ext h2 hx, hF⟩

theorem LvlEqCacheOK.mono {tbl : Std.HashMap (LIdx × LIdx) Bool}
    {st st' : EStore} (h : LvlEqCacheOK tbl st) (hx : Ext st st') :
    LvlEqCacheOK tbl st' := by
  intro k r hk
  obtain ⟨u, v, h1, h2, hF⟩ := h k r hk
  exact ⟨u, v, denoteL_ext h1 hx, denoteL_ext h2 hx, hF⟩

theorem LvlsEqCacheOK.mono {tbl : Std.HashMap (LsIdx × LsIdx) Bool}
    {st st' : EStore} (h : LvlsEqCacheOK tbl st) (hx : Ext st st') :
    LvlsEqCacheOK tbl st' := by
  intro k r hk
  obtain ⟨u, v, h1, h2, hF⟩ := h k r hk
  exact ⟨u, v, denoteLs_ext h1 hx, denoteLs_ext h2 hx, hF⟩

theorem ConstTyCacheOK.mono {env : Env} {tbl : Std.HashMap (NIdx × LsIdx) EIdx}
    {st st' : EStore} (h : ConstTyCacheOK env tbl st) (hx : Ext st st') :
    ConstTyCacheOK env tbl st' := by
  intro k i hk
  obtain ⟨nm, ls, ci, h1, h2, h3, h4⟩ := h k i hk
  exact ⟨nm, ls, ci, denoteN_ext h1 hx, denoteLs_ext h2 hx, h3,
    denote_ext h4 hx⟩

theorem ConstValCacheOK.mono {env : Env}
    {tbl : Std.HashMap (NIdx × LsIdx) EIdx} {st st' : EStore}
    (h : ConstValCacheOK env tbl st) (hx : Ext st st') :
    ConstValCacheOK env tbl st' := by
  intro k i hk
  obtain ⟨nm, ls, cv, value, hint, h1, h2, h3, h4⟩ := h k i hk
  exact ⟨nm, ls, cv, value, hint, denoteN_ext h1 hx, denoteLs_ext h2 hx, h3,
    denote_ext h4 hx⟩

theorem RuleRhsCacheOK.mono {env : Env}
    {tbl : Std.HashMap (NIdx × NIdx × LsIdx) EIdx} {st st' : EStore}
    (h : RuleRhsCacheOK env tbl st) (hx : Ext st st') :
    RuleRhsCacheOK env tbl st' := by
  intro k i hk
  obtain ⟨rn, cn, ls, cv, mi, rp, isK, rules, rl, h1, h2, h3, h4, h5, h6⟩ := h k i hk
  exact ⟨rn, cn, ls, cv, mi, rp, isK, rules, rl, denoteN_ext h1 hx,
    denoteN_ext h2 hx, denoteLs_ext h3 hx, h4, h5, denote_ext h6 hx⟩

theorem ReadLCacheOK.mono {tbl : Std.HashMap LIdx Level} {st st' : EStore}
    (h : ReadLCacheOK tbl st) (hx : Ext st st') : ReadLCacheOK tbl st' :=
  fun k u hk => denoteL_ext (h k u hk) hx

theorem ReadNCacheOK.mono {tbl : Std.HashMap NIdx ConLeche.Name}
    {st st' : EStore} (h : ReadNCacheOK tbl st) (hx : Ext st st') :
    ReadNCacheOK tbl st' :=
  fun k x hk => denoteN_ext (h k x hk) hx

theorem ReadLsCacheOK.mono {tbl : Std.HashMap LsIdx (List Level)}
    {st st' : EStore} (h : ReadLsCacheOK tbl st) (hx : Ext st st') :
    ReadLsCacheOK tbl st' :=
  fun k us hk => denoteLs_ext (h k us hk) hx

/-- con-leche: none — `ModeMemosOK` transports along the store order. -/
theorem ModeMemosOK.mono {eager : Bool} {env : Env} {mm : ModeMemos}
    {st st' : EStore} (h : ModeMemosOK eager env mm st) (hx : Ext st st') :
    ModeMemosOK eager env mm st' :=
  ⟨h.whnfCore.mono hx, h.whnfCoreCheap.mono hx, h.whnf.mono hx, h.infer.mono hx,
    h.inferIO.mono hx, h.defeq.mono hx⟩

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the cache record
transports in one equation**, which is what putting the fourteen tables in a
record buys (DESIGN `### Task #97b`: "a frame condition … is one equation
instead of eleven"). -/
theorem CacheOK.mono {eager : Bool} {env : Env} {s s' : AState}
    (h : CacheOK eager env s) (hx : Ext s.store s'.store)
    (hc : s'.caches = s.caches) : CacheOK eager env s' where
  whnfCore := by rw [hc]; exact h.whnfCore.mono hx
  whnfCoreCheap := by rw [hc]; exact h.whnfCoreCheap.mono hx
  whnf := by rw [hc]; exact h.whnf.mono hx
  infer := by rw [hc]; exact h.infer.mono hx
  inferIO := by rw [hc]; exact h.inferIO.mono hx
  defeq := by rw [hc]; exact h.defeq.mono hx
  lvlEq := by rw [hc]; exact h.lvlEq.mono hx
  lvlsEq := by rw [hc]; exact h.lvlsEq.mono hx
  constTy := by rw [hc]; exact h.constTy.mono hx
  constVal := by rw [hc]; exact h.constVal.mono hx
  ruleRhs := by rw [hc]; exact h.ruleRhs.mono hx
  readL := by rw [hc]; exact h.readL.mono hx
  readN := by rw [hc]; exact h.readN.mono hx
  readLs := by rw [hc]; exact h.readLs.mono hx
  eager := by rw [hc]; exact h.eager.mono hx

/-- con-leche: none — a name-handle list's denotation transports. -/
theorem denoteNL_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name),
      denoteNL st hs xs → denoteNL st' hs xs := by
  intro hs
  induction hs with
  | nil => intro xs h; cases xs with
    | nil => exact h
    | cons _ _ => exact h.elim
  | cons a as ih =>
    intro xs h
    cases xs with
    | nil => exact h.elim
    | cons x xs =>
      exact ⟨denoteN_ext h.1 hx, ih xs h.2⟩

theorem PinsOK.mono {s s' : AState} (h : PinsOK s) (hx : Ext s.store s'.store)
    (hp : s'.pins = s.pins) : PinsOK s' where
  ready := by rw [hp]; exact h.ready
  names := by rw [hp]; exact denoteNL_ext hx _ _ h.names
  reserved := by rw [hp]; exact denoteNL_ext hx _ _ h.reserved
  emptyLevels := by rw [hp]; exact denoteLs_ext h.emptyLevels hx
  zeroLevel := by rw [hp]; exact denoteL_ext h.zeroLevel hx
  sortOne := by rw [hp]; exact denote_ext h.sortOne hx
  anon := denoteN_ext h.anon hx


theorem IFEnvOK.mono {env : Env} {fe : IFEnv} {s s' : AState}
    (h : IFEnvOK env fe s) (hx : Ext s.store s'.store) : IFEnvOK env fe s' where
  hit := by
    intro n ci hf
    obtain ⟨nm, c, h1, h2, h3⟩ := h.hit n ci hf
    exact ⟨nm, c, denoteN_ext h1 hx, denoteCI_ext h2 hx, h3⟩
  cover := by
    intro nm c he
    obtain ⟨n, ci, h1, h2, h3⟩ := h.cover nm c he
    exact ⟨n, ci, denoteN_ext h1 hx, h2, denoteCI_ext h3 hx⟩
  tblHit := by
    intro n t hf
    obtain ⟨nm, pt, h1, h2, h3, h4⟩ := h.tblHit n t hf
    exact ⟨nm, pt, denoteN_ext h1 hx, denoteProjTable_ext h2 hx, h3, h4⟩
  tblCover := by
    intro nm pt he
    obtain ⟨n, t, h1, h2, h3⟩ := h.tblCover nm pt he
    exact ⟨n, t, denoteN_ext h1 hx, h2, denoteProjTable_ext h3 hx⟩
  flags := h.flags
  lits := LitsOK.mono h.lits hx

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the whole invariant
transports past a call that only grows the arena.**  This is the theorem the
`ExprOps` tier's frame conditions exist for: the caches and the pin table are
two equations, the store half comes from the call's own postcondition, and
the environment index needs nothing but `Ext`. -/
theorem CheckOK.mono {eager : Bool} {env : Env} {fe : IFEnv}
    {s s' : AState} (h : CheckOK eager env fe s) (hok : StateOK s')
    (hx : Ext s.store s'.store) (hc : s'.caches = s.caches)
    (hp : s'.pins = s.pins) : CheckOK eager env fe s' where
  state := hok
  caches := h.caches.mono hx hc
  pins := h.pins.mono hx hp
  ienv := h.ienv.mono hx

/-! ### The LEVEL-VERDICT frame

`CheckOK.mono` above wants `s'.caches = s.caches`, and that equation is FALSE
of any call that compares two LEVEL handles.  `Arena/Core.lean`'s `lvlEq?` is
a cached verdict walk: it probes `caches.lvlEqC`, and on a miss it reads both
handles back through `readLevelM` — which writes `caches.readLC` — and records
the verdict in `caches.lvlEqC`.  The Rust does exactly the same
(`core.rs`'s `lvl_eq` → `read_level_m` twice → `lvl_eq_set`), so the port is
not at fault and the frame is.

`CacheFrame` is the honest frame, in `Bridge/Core/Walks/Frame.lean`'s
`ReadbackFrame` shape:

* **the record EQUATION** — the cache record afterwards is the record
  beforehand with the two tables the call may write replaced.  One equation
  rather than twelve: `rw` recovers each clause that did not move.
* **two IMPLICATIONS** rather than facts, for the reason `ReadbackFrame`
  gives: a `StateOK`-graded statement says nothing about cache CONTENTS, so a
  frame that asserted `ReadLCacheOK` outright could not be proved there.  As
  implications `.refl` is `id`, `.trans` composes, and a caller holding
  `CheckOK` — which is where the two invariants live — gets them back.

The second implication takes BOTH invariants, and that is not slack: on a
miss the verdict inserted into `lvlEqC` is `Level.isEquiv` of whatever
`readLevelM` answered, so a poisoned `readLC` poisons `lvlEqC`.  `LvlEqCacheOK`
alone does not survive the call; the pair does.

**Four tables.**  `instLPFast`'s readbacks write `readNC` and `readLsC` as
well (`Bridge/ExprOps/Owed.lean`'s `instLPFast_spec`), so the frame names the
two other readback tables too, with their invariants carried as implications
in the same way.  A call that compares levels only is the special case, and
every consumer reads the frame through `CacheOK.monoF`. -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC —
**the frame of a call that may compare LEVELS or read handles back**: it moved
`readLC`, `lvlEqC`, `readNC` and `readLsC` and no other per-declaration table,
and it kept their invariants. -/
structure CacheFrame (s s' : AState) : Prop where
  caches : s'.caches = { s.caches with
    readLC := s'.caches.readLC, lvlEqC := s'.caches.lvlEqC,
    readNC := s'.caches.readNC, readLsC := s'.caches.readLsC }
  readL : ReadLCacheOK s.caches.readLC s.store →
    ReadLCacheOK s'.caches.readLC s'.store
  lvlEq : ReadLCacheOK s.caches.readLC s.store →
    LvlEqCacheOK s.caches.lvlEqC s.store →
    LvlEqCacheOK s'.caches.lvlEqC s'.store
  readN : ReadNCacheOK s.caches.readNC s.store →
    ReadNCacheOK s'.caches.readNC s'.store
  readLs : ReadLsCacheOK s.caches.readLsC s.store →
    ReadLsCacheOK s'.caches.readLsC s'.store

/-- con-leche: none — the identity frame. -/
theorem CacheFrame.refl (s : AState) : CacheFrame s s :=
  ⟨rfl, id, fun _ h => h, id, id⟩

/-- con-leche: none — frames compose. -/
theorem CacheFrame.trans {a b c : AState} (h : CacheFrame a b)
    (h' : CacheFrame b c) : CacheFrame a c where
  caches := by rw [h'.caches, h.caches]
  readL := fun x => h'.readL (h.readL x)
  lvlEq := fun hr hl => h'.lvlEq (h.readL hr) (h.lvlEq hr hl)
  readN := fun x => h'.readN (h.readN x)
  readLs := fun x => h'.readLs (h.readLs x)

/-- con-leche: none — **the frame of a call that writes NO per-declaration
table at all**, which is what the other ~110 twins of the inductive tier and
every step of the parse but one deliver.  The four implications are the
invariants' own `mono` past the arena extension. -/
theorem CacheFrame.of_eq {s s' : AState} (hc : s'.caches = s.caches)
    (hx : Ext s.store s'.store) : CacheFrame s s' where
  caches := by rw [hc]
  readL := fun h => by rw [hc]; exact h.mono hx
  lvlEq := fun _ h => by rw [hc]; exact h.mono hx
  readN := fun h => by rw [hc]; exact h.mono hx
  readLs := fun h => by rw [hc]; exact h.mono hx

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **`CacheOK` past a level
comparison**: twelve clauses that did not move, recovered from the one
equation, and the two that did, carried by the frame itself. -/
theorem CacheOK.monoF {eager : Bool} {env : Env} {s s' : AState}
    (h : CacheOK eager env s) (hx : Ext s.store s'.store)
    (hf : CacheFrame s s') : CacheOK eager env s' where
  whnfCore := by rw [hf.caches]; exact h.whnfCore.mono hx
  whnfCoreCheap := by rw [hf.caches]; exact h.whnfCoreCheap.mono hx
  whnf := by rw [hf.caches]; exact h.whnf.mono hx
  infer := by rw [hf.caches]; exact h.infer.mono hx
  inferIO := by rw [hf.caches]; exact h.inferIO.mono hx
  defeq := by rw [hf.caches]; exact h.defeq.mono hx
  lvlEq := hf.lvlEq h.readL h.lvlEq
  lvlsEq := by rw [hf.caches]; exact h.lvlsEq.mono hx
  constTy := by rw [hf.caches]; exact h.constTy.mono hx
  constVal := by rw [hf.caches]; exact h.constVal.mono hx
  ruleRhs := by rw [hf.caches]; exact h.ruleRhs.mono hx
  readL := hf.readL h.readL
  readN := hf.readN h.readN
  readLs := hf.readLs h.readLs
  eager := by rw [hf.caches]; exact h.eager.mono hx

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **`CheckOK` past a call
that grows the arena and may compare levels**: `CheckOK.mono` with the cache
equation replaced by the frame.  `CheckOK.mono` is the special case
(`CacheFrame.of_eq`) and is kept because most callers still have it. -/
theorem CheckOK.monoF {eager : Bool} {env : Env} {fe : IFEnv}
    {s s' : AState} (h : CheckOK eager env fe s) (hok : StateOK s')
    (hx : Ext s.store s'.store) (hf : CacheFrame s s')
    (hp : s'.pins = s.pins) : CheckOK eager env fe s' where
  state := hok
  caches := h.caches.monoF hx hf
  pins := h.pins.mono hx hp
  ienv := h.ienv.mono hx

/-! ## The stored constant's NAME

These live in this module because it is the lowest one that has
`Frontend.denoteCI`, and it is below the Checker tier — whose
`IFEnvOK_of_denote`, `IFEnvOK_restrictTo` and `installBasisDecl_bridge` need
them and cannot see `Bridge/Inductives/**`. -/

/-- con-leche: none — a denoting `IConstantVal`'s TYPE denotes: the one
projection of `Frontend.denoteCV` this tier reads directly. -/
theorem denoteCV_type {st : EStore} {cv : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st cv = some c) : denoteE st cv.type = some c.type := by
  simp only [Frontend.denoteCV] at h
  cases hn : denoteN st.ns cv.name with
  | none => rw [hn] at h; simp at h
  | some n =>
    cases hl : Frontend.denoteNList st.ns cv.levelParams with
    | none => rw [hn, hl] at h; simp at h
    | some lps =>
      cases ht : denoteE st cv.type with
      | none => rw [hn, hl, ht] at h; simp at h
      | some ty =>
        rw [hn, hl, ht] at h
        obtain rfl := Option.some.inj h
        rfl

/-- con-leche: none — a denoting `IConstantVal`'s LEVEL PARAMETERS denote.
(`Bridge/Checker/Base.lean`'s `denoteCV_inv` is the three-way version, but it
sits in a module the inductive tier cannot see.) -/
theorem denoteCV_lps {st : EStore} {cv : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st cv = some c) :
    Frontend.denoteNList st.ns cv.levelParams = some c.levelParams := by
  simp only [Frontend.denoteCV] at h
  cases hn : denoteN st.ns cv.name with
  | none => rw [hn] at h; simp at h
  | some n =>
    cases hl : Frontend.denoteNList st.ns cv.levelParams with
    | none => rw [hn, hl] at h; simp at h
    | some lps =>
      cases ht : denoteE st cv.type with
      | none => rw [hn, hl, ht] at h; simp at h
      | some ty =>
        rw [hn, hl, ht] at h
        obtain rfl := Option.some.inj h
        rfl

/-- con-leche: none — a denoting `IConstantVal`'s NAME denotes. -/
theorem denoteCV_name {st : EStore} {cv : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st cv = some c) :
    denoteN st.ns cv.name = some c.name := by
  simp only [Frontend.denoteCV] at h
  cases hn : denoteN st.ns cv.name with
  | none => rw [hn] at h; simp at h
  | some n =>
    cases hl : Frontend.denoteNList st.ns cv.levelParams with
    | none => rw [hn, hl] at h; simp at h
    | some lps =>
      cases ht : denoteE st cv.type with
      | none => rw [hn, hl, ht] at h; simp at h
      | some ty =>
        rw [hn, hl, ht] at h
        obtain rfl := Option.some.inj h
        rfl


/-- con-leche: ConLeche/Kernel/Env.lean:506 ConstantInfo.name — **a stored
constant is named by its own handle.**  Every constructor carries an
`IConstantVal` and `denoteCV_name` is the whole proof. -/
theorem denoteCI_name {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) :
    denoteN st.ns ci.name = some c.name := by
  cases ci with
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact denoteCV_name hcv
  | ctorInfo v nP nF T =>
    obtain ⟨cv, _, hcv, _, rfl⟩ := denoteCI_ctorInfo_some h
    exact denoteCV_name hcv
  | defnInfo v e hh =>
    simp only [Frontend.denoteCI] at h
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h
        obtain rfl := Option.some.inj h
        exact denoteCV_name hcv
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact denoteCV_name hcv
  | indInfo v caps =>
    simp only [Frontend.denoteCI] at h
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases hc : Frontend.denoteCaps st caps with
      | none => rw [hcv, hc] at h; simp at h
      | some x =>
        rw [hcv, hc] at h
        obtain rfl := Option.some.inj h
        exact denoteCV_name hcv
  | recInfo v mI rP k rs =>
    simp only [Frontend.denoteCI] at h
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases hr : Frontend.denoteRules st rs with
      | none => rw [hcv, hr] at h; simp at h
      | some x =>
        rw [hcv, hr] at h
        obtain rfl := Option.some.inj h
        exact denoteCV_name hcv

/-- con-leche: ConLeche/Kernel/Env.lean:502-504 ConstantInfo.toConstantVal — a
stored constant's record denotes the denoted constant's. -/
theorem denoteCI_toConstantVal {st : EStore} {ci : IConstantInfo}
    {c : ConstantInfo} (h : Frontend.denoteCI st ci = some c) :
    Frontend.denoteCV st ci.toConstantVal = some c.toConstantVal := by
  cases ci with
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact hcv
  | ctorInfo v nP nF T =>
    obtain ⟨cv, _, hcv, _, rfl⟩ := denoteCI_ctorInfo_some h
    exact hcv
  | defnInfo v e hh =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv x hcv _; cases h; exact hcv
    · simp at h
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h; exact hcv
  | indInfo v caps =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv x hcv _; cases h; exact hcv
    · simp at h
  | recInfo v mI rP k rs =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv x hcv _; cases h; exact hcv
    · simp at h

end ConRon.Bridge
