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
  `s'.caches = s₀.caches`, which is one equation because task #97b put the
  tables in one record).
* **`CacheOK mode env s`** is the per-DECLARATION tables' clause, in
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

Task #97b's finding 2 is why each is an `abbrev` over one generic `MemoOK`
rather than an application of it:

> A generic memo invariant breaks `mspec` outright.  With `MemoOK f tbl st`
> the memo insert's spec leaves `f` a higher-order metavariable and the arm's
> verification condition comes out as `RelAt (?f d) …`, which is not a Miller
> pattern and no `exact` can close.  The fix is an `abbrev` per table fixing
> `f` to a concrete lambda whose only metavariable is first-order.

`abbrev` and not `def`, so the generic lemmas still match syntactically.
-/
import ConRon.Bridge.Rel
import ConLeche.Kernel.TypeChecker

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena Std.Do

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
(`instLPLC`, task #97-P6-13). -/
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
unfold list, where it would skolemise the goal — task #97s template rule
6). -/
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

theorem MemoVOK.mono {α : Type} {f : Expr → α} {tbl tbl' : Std.HashMap EIdx α}
    {st st' : EStore} (hm : MemoVOK f tbl st) (hx : Ext st st')
    (hc : tbl' = tbl) : MemoVOK f tbl' st' := by
  intro k v hk
  rw [hc] at hk
  obtain ⟨e, h1, h2⟩ := hm k v hk
  exact ⟨e, denote_ext h1 hx, h2⟩

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

/-! ### The thirteen tables, one `abbrev` each

Each fixes the generic `f` to a concrete lambda whose free variables are the
walk's own parameters and are all first-order (task #97b finding 2).  The
three tables `Monad.lean` keys at cursor `0` (`resetC`, `renameC`, `instLPC`)
ignore the cursor in the lambda, which is what makes them one invariant with
the other six. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:61-63 Inst1MemoInv. -/
abbrev Inst1MemoA (ve : Expr) (s : AState) : Prop :=
  MemoOK (fun d e => e.instantiate1 ve d) s.memos.inst1C s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:248-250 InstLMemoInv. -/
abbrev InstLMemoA (ws : List Expr) (s : AState) : Prop :=
  MemoOK (fun d e => e.instantiateList ws d) s.memos.instLC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:411-413 LiftMemoInv. -/
abbrev LiftMemoA (amount : Nat) (s : AState) : Prop :=
  MemoOK (fun c e => Expr.liftLooseBVars amount c e) s.memos.liftC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:562-564 ResetMemoInv, at cursor
`0`. -/
abbrev ResetMemoA (s : AState) : Prop :=
  MemoOK (fun _ e => Expr.resetMeta e) s.memos.resetC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:983-985 RenameMemoInv, at cursor
`0`.  The renaming is a function on con-leche `Name`s: the twin's
`f : NIdx → NIdx` is related to it by the walk's own hypothesis, not by this
invariant. -/
abbrev RenameMemoA (fn : ConLeche.Name → ConLeche.Name) (s : AState) : Prop :=
  MemoOK (fun _ e => Expr.renameConsts fn e) s.memos.renameC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1772-1774 Abs1MemoInv. -/
abbrev Abs1MemoA (d : Nat) (s : AState) : Prop :=
  MemoOK (fun k e => Expr.abstract1 e d k) s.memos.abs1C s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1995-1997 LowerMemoInv. -/
abbrev LowerMemoA (amount : Nat) (s : AState) : Prop :=
  MemoOK (fun c e => Expr.lowerBVars amount c e) s.memos.lowerC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2205-2207 Inst1LMemoInv. -/
abbrev Inst1LMemoA (ve : Expr) (s : AState) : Prop :=
  MemoOK (fun d e => Expr.instantiate1Lift e ve d) s.memos.inst1LC s.store

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
substitution's own per-call memo (task #97-P6-13). -/
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
def EntryCacheOK (op : Nat → Nat → Expr → CheckM Expr)
    (tbl : Std.HashMap EIdx EIdx) (st : EStore) : Prop :=
  ∀ (i j : EIdx), tbl[i]? = some j →
    ∃ a b, denoteE st i = some a ∧ denoteE st j = some b ∧
      ∃ F, ∀ d, Expr.wscopedB d a = true → op F d a = .ok b

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `defeqC` clause) — the
`defeq` verdict cache, BOTH SIGNS: the pure run at the fixed fuel answered
`r`, and the memo answers `r`.  This is what makes a negative memo sound. -/
def DefeqCacheOK (op : Nat → Nat → Expr → Expr → CheckM Bool)
    (tbl : Std.HashMap (EIdx × EIdx) Bool) (st : EStore) : Prop :=
  ∀ (k : EIdx × EIdx) (r : Bool), tbl[k]? = some r →
    ∃ a b, denoteE st k.1 = some a ∧ denoteE st k.2 = some b ∧
      ∃ F, ∀ d, Expr.wscopedB d a = true → Expr.wscopedB d b = true →
        op F d a b = .ok r

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `lsimp`/`eqv` clauses) —
the level-verdict cache: a recorded verdict is `Level.isEquiv`'s. -/
def LvlEqCacheOK (tbl : Std.HashMap (LIdx × LIdx) Bool) (st : EStore) : Prop :=
  ∀ (k : LIdx × LIdx) (r : Bool), tbl[k]? = some r →
    ∃ u v, denoteL st.ls k.1 = some u ∧ denoteL st.ls k.2 = some v ∧
      Level.isEquiv u v = some r

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the same at two
universe-argument lists. -/
def LvlsEqCacheOK (tbl : Std.HashMap (LsIdx × LsIdx) Bool) (st : EStore) :
    Prop :=
  ∀ (k : LsIdx × LsIdx) (r : Bool), tbl[k]? = some r →
    ∃ us vs, denoteLs st.lss k.1 = some us ∧ denoteLs st.lss k.2 = some vs ∧
      Level.isEquivList us vs = some r

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `constTy` clause) — a
row of the lazy instantiated-constant TYPE cache is the environment's own
constant at the key's universe arguments.  The environment is what makes the
key `(name, levels)` determine the subject; without it the clause would be
vacuous (`Arena/Core.lean`'s `constTyAt` takes the subject as an argument). -/
def ConstTyCacheOK (env : Env) (tbl : Std.HashMap (NIdx × LsIdx) EIdx)
    (st : EStore) : Prop :=
  ∀ (k : NIdx × LsIdx) (i : EIdx), tbl[k]? = some i →
    ∃ nm ls ci, denoteN st.ns k.1 = some nm ∧ denoteLs st.lss k.2 = some ls ∧
      env.find? nm = some ci ∧
      denoteE st i = some (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams ls)

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the same for a stored
definition's VALUE.  The environment entry must be one that HAS a value, so
the clause names it. -/
def ConstValCacheOK (env : Env) (tbl : Std.HashMap (NIdx × LsIdx) EIdx)
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
def RuleRhsCacheOK (env : Env) (tbl : Std.HashMap (NIdx × NIdx × LsIdx) EIdx)
    (st : EStore) : Prop :=
  ∀ (k : NIdx × NIdx × LsIdx) (i : EIdx), tbl[k]? = some i →
    ∃ rn cn ls cv mi rp rules rl,
      denoteN st.ns k.1 = some rn ∧ denoteN st.ns k.2.1 = some cn ∧
      denoteLs st.lss k.2.2 = some ls ∧
      env.find? rn = some (.recInfo cv mi rp rules) ∧
      rules.find? (fun r => r.ctor == cn) = some rl ∧
      denoteE st i = some (rl.rhs.instantiateLevelParams cv.levelParams ls)

/-- con-leche: none — the READBACK memos (task #97-P6-13) are the identity on
the denotation, so their clause is an equation and not a simulation. -/
def ReadLCacheOK (tbl : Std.HashMap LIdx Level) (st : EStore) : Prop :=
  ∀ (k : LIdx) (u : Level), tbl[k]? = some u → denoteL st.ls k = some u

/-- con-leche: none — the same for a NAME handle. -/
def ReadNCacheOK (tbl : Std.HashMap NIdx ConLeche.Name) (st : EStore) : Prop :=
  ∀ (k : NIdx) (x : ConLeche.Name), tbl[k]? = some x → denoteN st.ns k = some x

/-- con-leche: none — the same for an interned universe-argument list. -/
def ReadLsCacheOK (tbl : Std.HashMap LsIdx (List Level)) (st : EStore) :
    Prop :=
  ∀ (k : LsIdx) (us : List Level), tbl[k]? = some us →
    denoteLs st.lss k = some us

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the fourteen
per-declaration tables of `Caches`, in one record, at the pure knot the
bridge's Theorem 1 is stated against (`pureFns mode env F`, con-leche's
`ConLeche/Kernel/TypeChecker.lean`). -/
structure CacheOK (mode : CheckMode) (env : Env) (s : AState) : Prop where
  whnfCore : EntryCacheOK (ConLeche.whnfCore mode env) s.caches.whnfCoreC s.store
  whnf : EntryCacheOK (ConLeche.whnf mode env) s.caches.whnfC s.store
  infer : EntryCacheOK (ConLeche.inferTypeCore mode env) s.caches.inferC s.store
  inferIO : EntryCacheOK (ConLeche.inferTypeIO mode env) s.caches.inferIOC s.store
  annot : EntryCacheOK (ConLeche.annotateCore mode env) s.caches.annotC s.store
  defeq : DefeqCacheOK (ConLeche.isDefEqCore mode env) s.caches.defeqC s.store
  lvlEq : LvlEqCacheOK s.caches.lvlEqC s.store
  lvlsEq : LvlsEqCacheOK s.caches.lvlsEqC s.store
  constTy : ConstTyCacheOK env s.caches.constTyC s.store
  constVal : ConstValCacheOK env s.caches.constValC s.store
  ruleRhs : RuleRhsCacheOK env s.caches.ruleRhsC s.store
  readL : ReadLCacheOK s.caches.readLC s.store
  readN : ReadNCacheOK s.caches.readNC s.store
  readLs : ReadLsCacheOK s.caches.readLsC s.store

/-! ## The pin table -/

/-- con-leche: none — a list of name handles denotes a list of names,
pointwise. -/
def denoteNL (st : EStore) : List NIdx → List ConLeche.Name → Prop
  | [], [] => True
  | h :: hs, x :: xs => denoteN st.ns h = some x ∧ denoteNL st hs xs
  | _, _ => False

/-- con-leche: none — **the pin table denotes** (task #97-P6-4a): the
forty-nine `PIN_*` slots hold handles for `pinNames`, the reserved-basis list
holds handles for `reservedBasisNameValues`, and the three nullary values
denote `[]`, `Level.zero` and `Sort 1`.  `pinsReady` is the executable half of
the first conjunct and is what makes an early read a stop rather than a wrong
answer. -/
structure PinsOK (s : AState) : Prop where
  ready : s.pins.names.size = pinCount
  names : denoteNL s.store s.pins.names.toList pinNames
  reserved : denoteNL s.store s.pins.reserved reservedBasisNameValues
  emptyLevels : denoteLs s.store.lss s.pins.emptyLevels = some []
  zeroLevel : denoteL s.store.ls s.pins.zeroLevel = some .zero
  sortOne : denoteE s.store s.pins.sortOne = some (.sort (.succ .zero))
  /-- **the ZERO name handle decodes, and it decodes to `.anonymous`** (task
  #97-P3-Ind round 5's finding, ruled on by the maintainer).

  `Arena/Env.lean`'s `IIndCaps.etaCtor` defaults to `(default : NIdx)` — the
  zero word — where `ConLeche.IndCaps.etaCtor` defaults to `.anonymous`, and
  `Frontend.denoteCaps` reads the field UNCONDITIONALLY.  So every capability
  record built at a block that earns nothing — which is every multi-constructor
  block the fixpoint route installs — denotes only if the zero handle decodes
  to `.anonymous`, and until this clause nothing said it did:
  `Frontend.denoteCI` of the pushed `.indInfo` row was `none`, and with it
  `denoteFEnv`, `InstRel.denote` and `FoldOK.denote`.

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

/-- con-leche: ConLeche/Kernel/Env.lean:631-635 projTableName — **the
projection table's NAME clause, standing alone**: the stored `tableName`
decodes to the name con-leche recomputes from the structure's.

It is separated from the other two clauses because the two halves have
different debtors (task #97-P3-Frontend round 5's finding, ruled on by the
maintainer).  `IProjTableOK`'s size clauses are established by the INSTALL
(`Bridge/Inductives/StructInstall.lean`'s `checkStructProjTable`, through
`Bridge/Checker/Inv.lean`'s `projTableOK_of_install`); this one is also true
by CONSTRUCTION of the modeller's readback, because
`Arena/Frontend/Readback.lean`'s `internProjTable` interns `projTableName sn`
itself — and it is the only one of the three that the modeller seam can
discharge, since `bodies.size = numFields` would have to come from a con-leche
fact about `ProjTable` that nothing states.  So the NAME clause is the one
that travels, and every consumer that only reads the name takes this. -/
def IProjNamed (st : EStore) (t : IProjTable) : Prop :=
  ∃ sn, denoteN st.ns t.structName = some sn ∧
    denoteN st.ns t.tableName = some (ConLeche.projTableName sn)

/-- con-leche: none — both halves are `denoteN`s, so an append keeps them. -/
theorem IProjNamed.mono {st st' : EStore} {t : IProjTable}
    (h : IProjNamed st t) (hx : Ext st st') : IProjNamed st' t := by
  obtain ⟨sn, h1, h2⟩ := h
  exact ⟨sn, denoteN_ext h1 hx, denoteN_ext h2 hx⟩

/-- con-leche: ConLeche/Verify/EnvWF.lean:191 ConstWF (the `.projInfo`
clause) — **what a STORED projection table satisfies**, over the ARENA's
`IProjTable` and not over con-leche's `ProjTable`.

Three clauses, and not one of them is visible in the denotation:

* the two indexed columns have `numFields` entries.  `denoteProjTable`
  transports both pointwise and copies `numFields` verbatim, so the pure
  table's sizes ARE ours — which is exactly why con-leche's own invariant is
  the wrong place to take this from (a simulation B ⇒ A takes invariants on
  the REFINED side only);
* **the table's own name**: `IConstantInfo.name (.projInfo t)` is the STORED
  `t.tableName` (`Arena/Env.lean`'s one added field, kept so that the index's
  key is pure) while `ConstantInfo.name (.projInfo tbl)` is the RECOMPUTED
  `projTableName tbl.structName` — and `Frontend.denoteProjTable` drops
  `tableName` entirely.  Without this clause nothing ties the two, and
  `Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote` is false.

Both findings are the SAME problem — the projection-table denotation does not
carry what its consumers need — and both are fixed here, on our side, rather
than by strengthening `Arena/Frontend/Readback.lean` (task #97-P3-Checker-2's
answer to task #97-P3-Core-2's `ProjTablesShaped`). -/
structure IProjTableOK (st : EStore) (t : IProjTable) : Prop where
  bodies : t.bodies.size = t.numFields
  guards : t.guards.length = t.numFields
  named : ∃ sn, denoteN st.ns t.structName = some sn ∧
    denoteN st.ns t.tableName = some (ConLeche.projTableName sn)

/-- con-leche: none — the environment invariant implies the name clause, so a
site that holds the stronger fact never re-proves this one. -/
theorem IProjTableOK.toNamed {st : EStore} {t : IProjTable}
    (h : IProjTableOK st t) : IProjNamed st t := h.named

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `ienv` clause) — the
index answers exactly what the denoted environment answers.

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
  /-- **the stored projection tables are well shaped and rightly named** —
  the clause task #97-P3-Core-2 carried as a free hypothesis on
  `IFEnv.findProj?_spec` and task #97-P3-Checker-2's `IFEnvOK_of_denote`
  needed and did not have.  Its one debtor is the projection-table install;
  see `IProjTableOK`. -/
  proj : ∀ n t, fe.find? n = some (.projInfo t) → IProjTableOK s.store t

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

/-! ## The whole invariant, and what carries it -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the checker's state
invariant: the store, the fourteen per-declaration caches, the pin table and
the environment index.  The `ExprOps` tier does not mention it (it mentions
`StateOK` alone); the Core tier does. -/
structure CheckOK (mode : CheckMode) (env : Env) (fe : IFEnv) (s : AState) :
    Prop where
  state : StateOK s
  caches : CacheOK mode env s
  pins : PinsOK s
  ienv : IFEnvOK env fe s

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
  obtain ⟨rn, cn, ls, cv, mi, rp, rules, rl, h1, h2, h3, h4, h5, h6⟩ := h k i hk
  exact ⟨rn, cn, ls, cv, mi, rp, rules, rl, denoteN_ext h1 hx,
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

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the cache record
transports in one equation**, which is what putting the fourteen tables in a
record bought (task #97b: "a frame condition … is one equation instead of
eleven"). -/
theorem CacheOK.mono {mode : CheckMode} {env : Env} {s s' : AState}
    (h : CacheOK mode env s) (hx : Ext s.store s'.store)
    (hc : s'.caches = s.caches) : CacheOK mode env s' where
  whnfCore := by rw [hc]; exact h.whnfCore.mono hx
  whnf := by rw [hc]; exact h.whnf.mono hx
  infer := by rw [hc]; exact h.infer.mono hx
  inferIO := by rw [hc]; exact h.inferIO.mono hx
  annot := by rw [hc]; exact h.annot.mono hx
  defeq := by rw [hc]; exact h.defeq.mono hx
  lvlEq := by rw [hc]; exact h.lvlEq.mono hx
  lvlsEq := by rw [hc]; exact h.lvlsEq.mono hx
  constTy := by rw [hc]; exact h.constTy.mono hx
  constVal := by rw [hc]; exact h.constVal.mono hx
  ruleRhs := by rw [hc]; exact h.ruleRhs.mono hx
  readL := by rw [hc]; exact h.readL.mono hx
  readN := by rw [hc]; exact h.readN.mono hx
  readLs := by rw [hc]; exact h.readLs.mono hx

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

theorem IProjTableOK.mono {st st' : EStore} {t : IProjTable}
    (h : IProjTableOK st t) (hx : Ext st st') : IProjTableOK st' t where
  bodies := h.bodies
  guards := h.guards
  named := by
    obtain ⟨sn, h1, h2⟩ := h.named
    exact ⟨sn, denoteN_ext h1 hx, denoteN_ext h2 hx⟩

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
  proj := fun n t hf => (h.proj n t hf).mono hx

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the whole invariant
transports past a call that only grows the arena.**  This is the theorem the
`ExprOps` tier's frame conditions exist for: the caches and the pin table are
two equations, the store half comes from the call's own postcondition, and
the environment index needs nothing but `Ext`. -/
theorem CheckOK.mono {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s s' : AState} (h : CheckOK mode env fe s) (hok : StateOK s')
    (hx : Ext s.store s'.store) (hc : s'.caches = s.caches)
    (hp : s'.pins = s.pins) : CheckOK mode env fe s' where
  state := hok
  caches := h.caches.mono hx hc
  pins := h.pins.mono hx hp
  ienv := h.ienv.mono hx

/-! ### The LEVEL-VERDICT frame (task #97-P3-Frame)

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
alone does not survive the call; the pair does. -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC —
**the frame of a call that may compare LEVELS**: it moved `readLC` and
`lvlEqC` and no other per-declaration table, and it kept their invariants. -/
structure CacheFrame (s s' : AState) : Prop where
  caches : s'.caches = { s.caches with
    readLC := s'.caches.readLC, lvlEqC := s'.caches.lvlEqC }
  readL : ReadLCacheOK s.caches.readLC s.store →
    ReadLCacheOK s'.caches.readLC s'.store
  lvlEq : ReadLCacheOK s.caches.readLC s.store →
    LvlEqCacheOK s.caches.lvlEqC s.store →
    LvlEqCacheOK s'.caches.lvlEqC s'.store

/-- con-leche: none — the identity frame. -/
theorem CacheFrame.refl (s : AState) : CacheFrame s s :=
  ⟨rfl, id, fun _ h => h⟩

/-- con-leche: none — frames compose. -/
theorem CacheFrame.trans {a b c : AState} (h : CacheFrame a b)
    (h' : CacheFrame b c) : CacheFrame a c where
  caches := by rw [h'.caches, h.caches]
  readL := fun x => h'.readL (h.readL x)
  lvlEq := fun hr hl => h'.lvlEq (h.readL hr) (h.lvlEq hr hl)

/-- con-leche: none — **the frame of a call that writes NO per-declaration
table at all**, which is what the other ~110 twins of the inductive tier and
every step of the parse but one deliver.  The two implications are the two
invariants' own `mono` past the arena extension. -/
theorem CacheFrame.of_eq {s s' : AState} (hc : s'.caches = s.caches)
    (hx : Ext s.store s'.store) : CacheFrame s s' where
  caches := by rw [hc]
  readL := fun h => by rw [hc]; exact h.mono hx
  lvlEq := fun _ h => by rw [hc]; exact h.mono hx

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **`CacheOK` past a level
comparison**: twelve clauses that did not move, recovered from the one
equation, and the two that did, carried by the frame itself. -/
theorem CacheOK.monoF {mode : CheckMode} {env : Env} {s s' : AState}
    (h : CacheOK mode env s) (hx : Ext s.store s'.store)
    (hf : CacheFrame s s') : CacheOK mode env s' where
  whnfCore := by rw [hf.caches]; exact h.whnfCore.mono hx
  whnf := by rw [hf.caches]; exact h.whnf.mono hx
  infer := by rw [hf.caches]; exact h.infer.mono hx
  inferIO := by rw [hf.caches]; exact h.inferIO.mono hx
  annot := by rw [hf.caches]; exact h.annot.mono hx
  defeq := by rw [hf.caches]; exact h.defeq.mono hx
  lvlEq := hf.lvlEq h.readL h.lvlEq
  lvlsEq := by rw [hf.caches]; exact h.lvlsEq.mono hx
  constTy := by rw [hf.caches]; exact h.constTy.mono hx
  constVal := by rw [hf.caches]; exact h.constVal.mono hx
  ruleRhs := by rw [hf.caches]; exact h.ruleRhs.mono hx
  readL := hf.readL h.readL
  readN := by rw [hf.caches]; exact h.readN.mono hx
  readLs := by rw [hf.caches]; exact h.readLs.mono hx

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **`CheckOK` past a call
that grows the arena and may compare levels**: `CheckOK.mono` with the cache
equation replaced by the frame.  `CheckOK.mono` is the special case
(`CacheFrame.of_eq`) and is kept because most callers still have it. -/
theorem CheckOK.monoF {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s s' : AState} (h : CheckOK mode env fe s) (hok : StateOK s')
    (hx : Ext s.store s'.store) (hf : CacheFrame s s')
    (hp : s'.pins = s.pins) : CheckOK mode env fe s' where
  state := hok
  caches := h.caches.monoF hx hf
  pins := h.pins.mono hx hp
  ienv := h.ienv.mono hx

/-! ## The stored constant's NAME, and the `.projInfo` name gap

Task #97-P3-Ind round 3 found and proved these five, in
`Bridge/Inductives/Rel.lean`, and named this module as where they belong:
the lowest one that has both `Frontend.denoteCI` and `IProjTableOK`, and the
one below the Checker tier — whose `IFEnvOK_of_denote`, `IFEnvOK_restrictTo`
and `installBasisDecl_bridge` were the three sites stuck on them and cannot
see `Bridge/Inductives/**`.  Round 4 moved them here unchanged.

`Frontend.denoteProjTable` drops `tableName`, so
`Frontend.denoteCI st ci = some c` does NOT give
`denoteN st.ns ci.name = some c.name` at a `.projInfo`: the handle side is the
STORED `t.tableName` and the pure side the RECOMPUTED
`projTableName t.structName`.  The fix is neither a hypothesis at each site
(that weakens the statement) nor a `denoteProjTable` that reads `tableName`
(the denotation is deliberately forgetful — `tableName` is the arena's own
redundancy, kept so the index's key is pure).  It is `IProjTableOK.named`,
the invariant that ties the two names, and it is available at every site that
needs it: inside the index through `IFEnvOK.proj`, and at the ONE install that
creates a `.projInfo` row (`checkStructProjTable`) because the table was just
built there.  Everywhere else `ci` is provably not a `.projInfo` and
`denoteCI_name` applies with no invariant at all. -/

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


/-! ### The `.projInfo` NAME GAP

`Frontend.denoteProjTable` drops `tableName`, so
`Frontend.denoteCI st ci = some c` does NOT give
`denoteN st.ns ci.name = some c.name` at a `.projInfo`: the handle side is the
STORED `t.tableName` and the pure side is the RECOMPUTED
`projTableName t.structName`.  Three sites above this tier have hit the same
wall — `IFEnvOK_of_denote`, `IFEnvOK_restrictTo` and (task #97-P3-Checker
round 2) `installBasisDecl_bridge` — and the fix is NOT to add a hypothesis to
any of them, nor to make `denoteProjTable` read `tableName` (the denotation is
deliberately forgetful; `tableName` is the arena's own redundancy, kept so the
index's key is pure).

The fix is these three lemmas.  `IProjTableOK.named` is the invariant that
ties the two names, and it is available at every site that needs it: inside
the index through `IFEnvOK.proj`, and at the ONE install that creates a
`.projInfo` row (`checkStructProjTable`, this tier's) because the table was
just built there.  Everywhere else `ci` is provably not a `.projInfo` and the
first lemma applies with no invariant at all.

**They belong in `Bridge/StateOK.lean`, beside `IProjTableOK`** — that is the
lowest module that has both `Frontend.denoteCI` and the invariant, and it is
below the Checker tier, which cannot see this file.  They are proved here
because this tier owns `IProjTableOK`'s `named` clause and its debtor. -/

/-- con-leche: ConLeche/Kernel/Env.lean:644 ConstantInfo.name — **a stored
constant that is not a projection table is named by its own handle.**  Six of
the seven constructors carry an `IConstantVal` and `denoteCV_name` is the
whole proof. -/
theorem denoteCI_name {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (hnp : ∀ t, ci ≠ .projInfo t)
    (h : Frontend.denoteCI st ci = some c) :
    denoteN st.ns ci.name = some c.name := by
  cases ci with
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact denoteCV_name hcv
  | ctorInfo v nP nF =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h
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
  | thmInfo v e =>
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
  | recInfo v mI rP rs =>
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
  | projInfo t => exact absurd rfl (hnp t)

/-- con-leche: ConLeche/Kernel/Env.lean:642 ConstantInfo.toConstantVal (the
`.projInfo` arm) — **and a projection table is named by its handle exactly
when `IProjTableOK.named` says so.**  That clause is not decoration: it is the
only thing that ties the stored `tableName` to the recomputed
`projTableName`. -/
theorem denoteCI_name_proj {st : EStore} {t : IProjTable} {c : ConstantInfo}
    (hok : IProjNamed st t)
    (h : Frontend.denoteCI st (.projInfo t) = some c) :
    denoteN st.ns (IConstantInfo.name (.projInfo t)) = some c.name := by
  obtain ⟨sn, hsn, htn⟩ := hok
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  obtain ⟨pt, hpt, rfl⟩ := h
  simp only [Frontend.denoteProjTable, hsn] at hpt
  cases hlps : Frontend.denoteNList st.ns t.levelParams with
  | none => rw [hlps] at hpt; simp at hpt
  | some lps =>
    cases hc : denoteN st.ns t.ctor with
    | none => rw [hlps, hc] at hpt; simp at hpt
    | some cn =>
      cases hss : denoteL st.ls t.structSort with
      | none => rw [hlps, hc, hss] at hpt; simp at hpt
      | some ss =>
        cases hbs : Frontend.denoteEArray st t.bodies with
        | none => rw [hlps, hc, hss, hbs] at hpt; simp at hpt
        | some bs =>
          cases hgs : denoteLList st.ls t.guards with
          | none => rw [hlps, hc, hss, hbs, hgs] at hpt; simp at hpt
          | some gs =>
            rw [hlps, hc, hss, hbs, hgs] at hpt
            obtain rfl := Option.some.inj hpt
            exact htn

/-- con-leche: none — **the two halves as one**: the name fact at any stored
constant, asking for `IProjTableOK` only where it is a projection table.  This
is the shape the three stuck sites want. -/
theorem denoteCI_name_of {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (hproj : ∀ t, ci = .projInfo t → IProjNamed st t)
    (h : Frontend.denoteCI st ci = some c) :
    denoteN st.ns ci.name = some c.name := by
  cases ci with
  | projInfo t => exact denoteCI_name_proj (hproj t rfl) h
  | axiomInfo v => exact denoteCI_name (by simp) h
  | defnInfo v e hh => exact denoteCI_name (by simp) h
  | thmInfo v e => exact denoteCI_name (by simp) h
  | indInfo v caps => exact denoteCI_name (by simp) h
  | ctorInfo v nP nF => exact denoteCI_name (by simp) h
  | recInfo v mI rP rs => exact denoteCI_name (by simp) h


end ConRon.Bridge
