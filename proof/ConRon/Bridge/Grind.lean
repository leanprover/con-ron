/-
# `ConRon.Bridge.Grind` — the vocabulary `grind` closes Theorem 1's verification conditions with

A Theorem 1 walk proof is

```lean
  sym only [bridge_grind] =>
    vcgen [f, callee specs…] <;> finish
```

`vcgen` runs in `SymM` and internalizes each verification condition's
hypotheses into `grind`'s E-graph as it generates them; `finish` closes each
condition in that same E-graph.  `only`: the bridge's set and nothing else
(the default `@[grind]` set carries `Bridge/Rel.lean`'s forward rules, which
fire on every denotation in sight).  What `grind` needs from the bridge is this
module's vocabulary and the walks' own arm lemmas, all registered with
`@[bridge_grind]`.  This module is the ONE place general vocabulary lives:
a walk module adds only what is about its own walk.

1. **The store order.**  `Ext` is the preorder `≤` on `EStore`
   (`Std.IsPreorder`), so `grind`'s order solver decides the chains
   `s₀.store ≤ s₁.store ≤ … ≤ sₙ.store` a sequence of calls leaves.  The
   statements keep `Ext`; `ext_eq_le` turns each `Ext` atom into its `≤`.
2. **Transport as an equation.**  `denote_le` (and its siblings at names,
   levels, level lists and handle lists): past `st ≤ st'` a handle that
   denotes denotes the same — an equation between the two denotation terms,
   with the multi-pattern `st ≤ st', denoteE st h`, so that congruence
   closure carries every denotation along the chain.  The table invariants
   (`MemoOK`, `MemoLOK`, `MemoLsOK`, `Read*CacheOK`) travel the same way.
3. **Answers about an optional subject as atoms.**  The answer relations
   (`RelE`, `RelEL`, `RelEO`, `RelL`, `RelLs`, `RelV`) ARE named predicates
   on the denotation terms (`MapRel`, `MapRelV`), whose equation at `some`
   fires when congruence closure learns that the subject denotes; e-matching
   binds the denotation from the subject's equivalence class.  A spec whose
   answer is not a function image states `Ans P (denoteE st i)` with its
   equation `Ans P (some e) = P e`.  (The `∀ e, denoteE st i = some e → P e`
   spelling both replace is the same proposition, but as a hypothesis its
   only pattern is `some e`, which matches every `some` in the context; and a
   `fun` inside an atom is what `grind`'s `funext` splits on, which is why the
   relations are `MapRel`, not `Ans`.)
4. **The state invariant** (`CheckOK → StateOK = StoreWF`), and small facts
   (`opt2`/`opt3`, `denoteEO`, the handle lists).
5. **The memo tables**: the hit, the insert and the dropped table of the
   generic expression memo invariant, each keyed by the table term the
   program builds.
6. **Views and tags as equations** (the dispatch walks).  A
   dispatch walk tests a handle's TAG, matches its VIEW, and compares against
   a con-leche function that matches the DENOTATION's constructor.  `grind`
   must see all three without a case split, so each fact is an equation
   between terms built from the subject, never a disjunction or an `∃`:
   * the denotation's constructor is its tag, `exprTag e = h.tag`, and its
     fields are PROJECTIONS (`exprFn e`, `exprConstName e`, …), so a view
     `.app f a` says `denoteE st f = some (exprFn e)` — no fresh variable;
     conversely an expression whose tag is KNOWN is its constructor at its
     projections (`exprTag_app`, …, guarded at the known tag);
   * all of it is one fact per viewed handle, `DenoteView st (st.view h)
     (denoteE st h)` (and `DenoteTag h (denoteE st h)` per tag-tested one),
     keyed by the handle's own terms; per-constructor extraction lemmas fire
     on `DenoteView st (some (.K …)) (some e)` once congruence closure knows
     the view's constructor and that the handle denotes — the precise trigger
     the `→` form of a view hypothesis (`st.view h = some (.app f a)`) cannot
     give, since its inferred multi-pattern `st.view h, .app f a` relates
     nothing;
   * a one-constructor projection the program read under its tag
     (`st.viewApp i = some (f, a)`) is the view (`view_of_viewApp`, guarded at
     that read);
   * the predicate arguments are named functions, never `fun`s;
   * a name store index is the inverse of `denoteN` (`idxOfName`), so "the
     handles are equal iff the names are" is congruence closure in both
     directions;
   * a view's constructor follows from its tag through the view projections
     (`ENodeView.tagOf_app`, …), which is what refutes a match's
     fall-through arm after a tag test;
   * a con-leche function the walk compares against is restated ONCE as an
     unconditional equation over tags and projections (`sameConstHeads_eq`,
     `Core/Walks/Spine.lean`), so `grind` never splits its `match`.
7. **Interning**: the binder record's faces, the capacity branch, a node's
   denotation from its view, its `ViewOK` side condition.
8. **The environment index as equations.**  A lookup `fe.find? c` and the
   environment's `env.find? nm` at the name `c` denotes agree on every
   projection the walks read — ONE fact per lookup (`IndexAt`): is it
   present, a definition, a constructor, a tower entry; a definition's hint,
   record and value, a constructor's record, any record off the tower.  A lookup that is a definition IS one (`iDefn?_eta`),
   which refutes a match's fall-through arm; the one case split left is on
   "definition or not" where a walk needs the hint of a lookup it did not
   match (`iDefnHint_cases`).
-/
import ConRon.Bridge.StateOK
import ConRon.Bridge.GrindAttr

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## 1. The store order -/

/-- con-leche: none — `Ext` is the store order: `st ≤ st'` is
"`st'` extends `st`". -/
instance : LE EStore := ⟨Ext⟩

/-- con-leche: none — the store order is a preorder (`Ext.refl`/`Ext.trans`),
which is what `grind`'s order solver needs. -/
instance : Std.IsPreorder EStore where
  le_refl := Ext.refl
  le_trans := fun _ _ _ => Ext.trans

/-- con-leche: none — an `Ext` atom is its `≤` (definitionally). -/
@[bridge_grind =] theorem ext_eq_le (a b : EStore) : Ext a b = (a ≤ b) := rfl

/-! ## 2. Transport

Every denotation and every table invariant along the store order, each keyed
by the order fact and the term it carries (so that congruence closure moves
it along the chain a sequence of calls leaves, and a term nobody reads costs
nothing).  The denotations are EQUATIONS between the two stores' terms; the
invariants' table is the same term at both stores (the frame equations make
it so). -/

/-- con-leche: none — `denote_ext` as an equation: past an extension, a
handle that denotes denotes the same. -/
theorem denote_le {st st' : EStore} {h : EIdx} (hx : st ≤ st')
    (hd : denoteE st h ≠ none) : denoteE st' h = denoteE st h := by
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hd
  rw [he]; exact hx.expr h e he
grind_pattern [bridge_grind] denote_le => st ≤ st', denoteE st h

/-- con-leche: none — `denote_le` for a NAME handle. -/
theorem denoteN_le {st st' : EStore} {c : NIdx} (hx : st ≤ st')
    (hd : denoteN st.ns c ≠ none) : denoteN st'.ns c = denoteN st.ns c := by
  obtain ⟨x, hx'⟩ := Option.ne_none_iff_exists'.mp hd
  rw [hx']; exact denoteN_ext hx' hx
grind_pattern [bridge_grind] denoteN_le => st ≤ st', denoteN st.ns c

/-- con-leche: none — `denote_le` for a LEVEL handle. -/
theorem denoteL_le {st st' : EStore} {c : LIdx} (hx : st ≤ st')
    (hd : denoteL st.ls c ≠ none) : denoteL st'.ls c = denoteL st.ls c := by
  obtain ⟨x, hx'⟩ := Option.ne_none_iff_exists'.mp hd
  rw [hx']; exact denoteL_ext hx' hx
grind_pattern [bridge_grind] denoteL_le => st ≤ st', denoteL st.ls c

/-- con-leche: none — `denote_le` for a universe-argument LIST handle. -/
theorem denoteLs_le {st st' : EStore} {c : LsIdx} (hx : st ≤ st')
    (hd : denoteLs st.lss c ≠ none) : denoteLs st'.lss c = denoteLs st.lss c := by
  obtain ⟨x, hx'⟩ := Option.ne_none_iff_exists'.mp hd
  rw [hx']; exact denoteLs_ext hx' hx
grind_pattern [bridge_grind] denoteLs_le => st ≤ st', denoteLs st.lss c

/-- con-leche: none — `denote_le` for a handle LIST. -/
theorem denoteEList_le {st st' : EStore} {hs : List EIdx} (hx : st ≤ st')
    (hd : Frontend.denoteEList st hs ≠ none) :
    Frontend.denoteEList st' hs = Frontend.denoteEList st hs := by
  obtain ⟨xs, h⟩ := Option.ne_none_iff_exists'.mp hd
  rw [h]; exact denoteEList_ext hx _ _ h
grind_pattern [bridge_grind] denoteEList_le => st ≤ st', Frontend.denoteEList st hs

/-- con-leche: none — `denote_le` for a name-handle LIST. -/
theorem denoteNList_le {st st' : EStore} {hs : List NIdx} (hx : st ≤ st')
    (hd : Frontend.denoteNList st.ns hs ≠ none) :
    Frontend.denoteNList st'.ns hs = Frontend.denoteNList st.ns hs := by
  obtain ⟨xs, h⟩ := Option.ne_none_iff_exists'.mp hd
  rw [h]; exact denoteNListE_ext hx _ _ h
grind_pattern [bridge_grind] denoteNList_le => st ≤ st', Frontend.denoteNList st.ns hs

/-- con-leche: none — `denote_le` for a capability record. -/
theorem denoteCaps_le {st st' : EStore} {c : IIndCaps} (hx : st ≤ st')
    (hd : Frontend.denoteCaps st c ≠ none) :
    Frontend.denoteCaps st' c = Frontend.denoteCaps st c := by
  obtain ⟨xs, h⟩ := Option.ne_none_iff_exists'.mp hd
  rw [h]; exact denoteCaps_ext h hx
grind_pattern [bridge_grind] denoteCaps_le => st ≤ st', Frontend.denoteCaps st c

/-- con-leche: none — `denote_le` for a rule list. -/
theorem denoteRules_le {st st' : EStore} {rs : List IRecRule} (hx : st ≤ st')
    (hd : Frontend.denoteRules st rs ≠ none) :
    Frontend.denoteRules st' rs = Frontend.denoteRules st rs := by
  obtain ⟨xs, h⟩ := Option.ne_none_iff_exists'.mp hd
  rw [h]; exact denoteRules_ext hx _ _ h
grind_pattern [bridge_grind] denoteRules_le => st ≤ st', Frontend.denoteRules st rs

/-- con-leche: none — `denote_le` for a constant record. -/
theorem denoteCV_le {st st' : EStore} {cv : IConstantVal} (hx : st ≤ st')
    (hd : Frontend.denoteCV st cv ≠ none) :
    Frontend.denoteCV st' cv = Frontend.denoteCV st cv := by
  obtain ⟨c, h⟩ := Option.ne_none_iff_exists'.mp hd
  rw [h]; exact denoteCV_ext h hx
grind_pattern [bridge_grind] denoteCV_le => st ≤ st', Frontend.denoteCV st cv

/-- con-leche: none — `denote_le` for a level-handle LIST. -/
theorem denoteLList_le {st st' : EStore} {hs : List LIdx} (hx : st ≤ st')
    (hd : denoteLList st.ls hs ≠ none) :
    denoteLList st'.ls hs = denoteLList st.ls hs := by
  obtain ⟨xs, h⟩ := Option.ne_none_iff_exists'.mp hd
  rw [h]; exact denoteLListE_ext hx _ _ h
grind_pattern [bridge_grind] denoteLList_le => st ≤ st', denoteLList st.ls hs

/-- con-leche: ConLeche/Kernel/ExprOps.lean:61-63 Inst1MemoInv — a memo
invariant survives a store extension when the table stood still. -/
theorem MemoOK.le {f : Nat → Expr → Expr} {tbl : Std.HashMap (EIdx × Nat) EIdx}
    {st st' : EStore} (hm : MemoOK f tbl st) (hx : st ≤ st') : MemoOK f tbl st' :=
  MemoOK.mono hm hx rfl
grind_pattern [bridge_grind] MemoOK.le => MemoOK f tbl st, st ≤ st'

/-- con-leche: none — `MemoLOK.mono` with the table the same term. -/
theorem MemoLOK.le {f : Level → Level} {tbl : Std.HashMap LIdx LIdx} {st st' : EStore}
    (hm : MemoLOK f tbl st) (hx : st ≤ st') : MemoLOK f tbl st' := MemoLOK.mono hm hx rfl
grind_pattern [bridge_grind] MemoLOK.le => MemoLOK f tbl st, st ≤ st'

/-- con-leche: none — `MemoLsOK.mono` with the table the same term. -/
theorem MemoLsOK.le {f : List Level → List Level} {tbl : Std.HashMap LsIdx LsIdx}
    {st st' : EStore} (hm : MemoLsOK f tbl st) (hx : st ≤ st') : MemoLsOK f tbl st' :=
  MemoLsOK.mono hm hx rfl
grind_pattern [bridge_grind] MemoLsOK.le => MemoLsOK f tbl st, st ≤ st'

/-- con-leche: none — `ReadLCacheOK.mono` at the store order. -/
theorem ReadLCacheOK.le {tbl : Std.HashMap LIdx Level} {st st' : EStore}
    (h : ReadLCacheOK tbl st) (hx : st ≤ st') : ReadLCacheOK tbl st' := h.mono hx
grind_pattern [bridge_grind] ReadLCacheOK.le => ReadLCacheOK tbl st, st ≤ st'

/-- con-leche: none — `ReadLsCacheOK.mono` at the store order. -/
theorem ReadLsCacheOK.le {tbl : Std.HashMap LsIdx (List Level)} {st st' : EStore}
    (h : ReadLsCacheOK tbl st) (hx : st ≤ st') : ReadLsCacheOK tbl st' := h.mono hx
grind_pattern [bridge_grind] ReadLsCacheOK.le => ReadLsCacheOK tbl st, st ≤ st'

/-- con-leche: none — `ReadNCacheOK.mono` at the store order. -/
theorem ReadNCacheOK.le {tbl : Std.HashMap NIdx ConLeche.Name} {st st' : EStore}
    (h : ReadNCacheOK tbl st) (hx : st ≤ st') : ReadNCacheOK tbl st' := h.mono hx
grind_pattern [bridge_grind] ReadNCacheOK.le => ReadNCacheOK tbl st, st ≤ st'

/-! ## 3. Answers about an optional subject

A spec that does not know its subject's denotation answers about whatever the
subject denotes.  Two spellings, both atoms that are never unfolded:

* the answer RELATIONS of `Bridge/Rel.lean` (`RelE`, `RelEL`, `RelEO`,
  `RelL`, `RelLs`; `RelV`) are, as equations, the named predicates `MapRel`
  (`MapRelV`) on the two DENOTATION TERMS, with an equation at `some` that
  fires once congruence closure knows the subject denotes — in a hypothesis
  and in a goal alike, and with no `fun` for `grind`'s `funext` to split on;
* a spec whose answer is not a function image states `Ans P (denoteE st i)`
  (`P` a `fun`; the memo/whnf chain's loops), with `Ans.some_eq`.

A subject known only to denote (`isSome`, the walks' precondition) is equated
with a `some` of a named term, so that the `some` equations fire. -/

/-- con-leche: none — **whatever `o` denotes satisfies `P`**: the answer
shape of a spec whose subject's denotation is not a parameter (the
spelling `∀ e, o = some e → P e`, behind a head symbol).  `o` is a `denoteE st i`
(or a `st.view i`, for the facts a view carries). -/
def Ans {α : Type} (P : α → Prop) (o : Option α) : Prop := ∀ e, o = some e → P e

/-- con-leche: none — `Ans` at a denoting subject. -/
@[bridge_grind =] theorem Ans.some_eq {α : Type} (P : α → Prop) (e : α) :
    Ans P (some e) = P e :=
  propext ⟨fun h => h e rfl, fun h _ he => Option.some.inj he ▸ h⟩

/-- con-leche: none — **an answer relation at an optional subject**: whatever
the subject `o` denotes, the answer `o'` denotes its image under `g` (the
named-predicate form of `Ans (fun e => o' = some (g e))`). -/
def MapRel {α β : Type} (g : α → β) : Option α → Option β → Prop
  | some a, o => o = some (g a)
  | none, _ => True

/-- con-leche: none — `MapRel` at a denoting subject, as an equation (both
polarities: a `MapRel` goal too). -/
@[bridge_grind =] theorem MapRel.some_eq {α β : Type} (g : α → β) (a : α) (o : Option β) :
    MapRel g (some a) o = (o = some (g a)) := rfl

/-- con-leche: none — **an answer relation at two optional subjects**: whatever
the subjects `oa`, `ob` denote, the answer `o` denotes their image under `g`
(`MapRel` with a second subject). -/
def MapRel2 {α β γ : Type} (g : α → β → γ) : Option α → Option β → Option γ → Prop
  | some a, some b, o => o = some (g a b)
  | _, _, _ => True

/-- con-leche: none — `MapRel2` at two denoting subjects, as an equation. -/
@[bridge_grind =] theorem MapRel2.some_eq {α β γ : Type} (g : α → β → γ) (a : α) (b : β)
    (o : Option γ) : MapRel2 g (some a) (some b) o = (o = some (g a b)) := rfl

/-- con-leche: none — the `∀` spelling of every answer relation IS `MapRel`. -/
theorem forall_eq_mapRel {α β : Type} (g : α → β) (o : Option α) (o' : Option β) :
    (∀ a, o = some a → o' = some (g a)) = MapRel g o o' := by
  cases o with
  | none => exact propext ⟨fun _ => trivial, fun _ a he => nomatch he⟩
  | some a => exact propext ⟨fun H => H a rfl, fun H a' he => by cases he; exact H⟩

/-- con-leche: none — `RelE` IS `MapRel` on the two denotation terms. -/
@[bridge_grind =] theorem relE_eq_mapRel (g : Expr → Expr) (st : EStore) (c : EIdx)
    (st' : EStore) (r : EIdx) :
    RelE g st c st' r = MapRel g (denoteE st c) (denoteE st' r) :=
  forall_eq_mapRel _ _ _

/-- con-leche: none — `RelEL` IS `MapRel` at a list answer. -/
@[bridge_grind =] theorem relEL_eq_mapRel (g : Expr → List Expr) (st : EStore) (c : EIdx)
    (st' : EStore) (rs : List EIdx) :
    RelEL g st c st' rs = MapRel g (denoteE st c) (Frontend.denoteEList st' rs) :=
  forall_eq_mapRel _ _ _

/-- con-leche: none — `RelEO` IS `MapRel` at an optional answer. -/
@[bridge_grind =] theorem relEO_eq_mapRel (g : Expr → Option Expr) (st : EStore) (c : EIdx)
    (st' : EStore) (r : Option EIdx) :
    RelEO g st c st' r = MapRel g (denoteE st c) (denoteEO st' r) :=
  forall_eq_mapRel _ _ _

/-- con-leche: none — `RelL` IS `MapRel` on the two level denotations. -/
@[bridge_grind =] theorem relL_eq_mapRel (g : Level → Level) (st : EStore) (c : LIdx)
    (st' : EStore) (r : LIdx) :
    RelL g st c st' r = MapRel g (denoteL st.ls c) (denoteL st'.ls r) :=
  forall_eq_mapRel _ _ _

/-- con-leche: none — `RelLs` IS `MapRel` on the two level-list denotations. -/
@[bridge_grind =] theorem relLs_eq_mapRel (g : List Level → List Level) (st : EStore)
    (c : LsIdx) (st' : EStore) (r : LsIdx) :
    RelLs g st c st' r = MapRel g (denoteLs st.lss c) (denoteLs st'.lss r) :=
  forall_eq_mapRel _ _ _

/-- con-leche: none — `RelV`'s answer at an optional subject (a VALUE, not a
denotation). -/
def MapRelV {α : Type} (g : Expr → α) : Option Expr → α → Prop
  | some e, x => x = g e
  | none, _ => True

/-- con-leche: none — `MapRelV` at a denoting subject. -/
@[bridge_grind =] theorem MapRelV.some_eq {α : Type} (g : Expr → α) (e : Expr) (x : α) :
    MapRelV g (some e) x = (x = g e) := rfl

/-- con-leche: none — `RelV` IS `MapRelV` at the denotation term. -/
@[bridge_grind =] theorem relV_eq_mapRelV {α : Type} (g : Expr → α) (st : EStore) (c : EIdx)
    (x : α) : RelV g st c x = MapRelV g (denoteE st c) x := by
  show (∀ e, denoteE st c = some e → x = g e) = _
  generalize denoteE st c = o
  cases o with
  | none => exact propext ⟨fun _ => trivial, fun _ e he => nomatch he⟩
  | some e => exact propext ⟨fun H => H e rfl, fun H e' he => by cases he; exact H⟩

/-- con-leche: none — a subject known only to denote (`isSome`, the walks'
precondition) denotes SOMETHING: the witness congruence closure needs to fire
the `some` equations.  This is the one place the vocabulary keeps an `∃`
conclusion: the witness IS the denotation's value, and it is pinned by the
equation it comes with.  The `∃`-free spelling `o = some (o.getD _)` puts the
witness one generation deeper, and `finish` then fails in `ExprOps/Inst1`,
`ExprOps/Ranges` and `ExprOps/Leaves`. -/
@[bridge_grind →] theorem denote_some_of_isSome {st : EStore} {h : EIdx}
    (hs : (denoteE st h).isSome = true) : ∃ e, denoteE st h = some e :=
  Option.isSome_iff_exists.mp hs

/-- con-leche: none — `denote_some_of_isSome` at a handle LIST. -/
@[bridge_grind →] theorem denoteEList_some_of_isSome {st : EStore} {hs : List EIdx}
    (h : (Frontend.denoteEList st hs).isSome = true) :
    ∃ xs, Frontend.denoteEList st hs = some xs :=
  Option.isSome_iff_exists.mp h

/-! A `Bool` answer about two or three optional subjects, as a named predicate
on their denotations (`PairAns`, `TripleAns`), with its equation at `some`
(`Core/Knot.lean` has the slot answers and the `DenWS` precondition). -/

/-- con-leche: none — a `Bool` answer about two optional subjects, as a named
predicate `P` on their denotations (`P` a partial application, never a
`fun`). -/
def PairAns (P : Expr → Expr → Bool → Prop) : Option Expr → Option Expr → Bool → Prop
  | some x, some y, r => P x y r
  | _, _, _ => True

/-- con-leche: none — `PairAns` at denoting subjects. -/
@[bridge_grind =] theorem PairAns.some_eq (P : Expr → Expr → Bool → Prop) (x y : Expr)
    (r : Bool) : PairAns P (some x) (some y) r = P x y r := rfl

/-- con-leche: none — a `Bool` answer about three optional subjects, as a
named predicate on their denotations. -/
def TripleAns (P : Expr → Expr → Expr → Bool → Prop) :
    Option Expr → Option Expr → Option Expr → Bool → Prop
  | some x, some y, some w, r => P x y w r
  | _, _, _, _ => True

/-- con-leche: none — `TripleAns` at denoting subjects. -/
@[bridge_grind =] theorem TripleAns.some_eq (P : Expr → Expr → Expr → Bool → Prop)
    (x y w : Expr) (r : Bool) : TripleAns P (some x) (some y) (some w) r = P x y w r := rfl

/-! ## 4. The state invariant, and small facts -/

attribute [bridge_grind →] CheckOK.state StateOK.wf

/-- con-leche: none — the state invariant IS its store's well-formedness (an
equation, so that a `StateOK` goal meets the callees' `StoreWF` posts). -/
@[bridge_grind =] theorem stateOK_eq (s : AState) : StateOK s = StoreWF s.store :=
  propext ⟨fun h => h.wf, fun h => ⟨h⟩⟩

/-- con-leche: none — a successful run is `isOk` (the fuel-merge lemmas take
a callee's run as `isOk`, which names no answer). -/
@[bridge_grind =] theorem except_isOk_ok {ε α : Type} (a : α) :
    (Except.ok a : Except ε α).isOk = true := rfl

attribute [bridge_grind =] Option.isSome_some Option.isSome_none Option.map_some
  Option.map_none Option.bind_some Option.bind_none

/-- con-leche: none — a list is empty iff its length is `0` (the twin reads
the stored list, con-leche the denoted one: their lengths agree). -/
theorem List.isEmpty_eq_len {α : Type} (l : List α) : l.isEmpty = (l.length == 0) := by
  cases l <;> rfl
attribute [bridge_grind =] List.isEmpty_eq_len

/-- con-leche: none — `opt2` at two present arguments. -/
@[bridge_grind =] theorem opt2_some_some {α β γ : Type} (f : α → β → γ) (a : α) (b : β) :
    opt2 f (some a) (some b) = some (f a b) := rfl

/-- con-leche: none — `opt3` at three present arguments. -/
@[bridge_grind =] theorem opt3_some_some {α β γ δ : Type} (f : α → β → γ → δ) (a : α) (b : β)
    (c : γ) : opt3 f (some a) (some b) (some c) = some (f a b c) := rfl

/-- con-leche: none — an optional handle that is `some` denotes a `some`
(for term-mode callers that name it; `grind` reads `denoteEO_some_eq_inv`). -/
theorem denoteEO_some_inv {st : EStore} {r : EIdx} {v : Option Expr}
    (h : denoteEO st (some r) = some v) : ∃ x, v = some x ∧ denoteE st r = some x := by
  simp only [denoteEO, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, rfl, hx⟩

/-- con-leche: none — an optional handle that is `some`: the inner option IS
the handle's denotation, and it is present (an equation and an `isSome`;
`denote_some_of_isSome` names the value). -/
@[bridge_grind →] theorem denoteEO_some_eq_inv {st : EStore} {r : EIdx} {v : Option Expr}
    (h : denoteEO st (some r) = some v) :
    denoteE st r = v ∧ (denoteE st r).isSome = true := by
  obtain ⟨x, rfl, hx⟩ := denoteEO_some_inv h
  exact ⟨hx, by rw [hx]; rfl⟩

/-- con-leche: none — an absent handle's denotation is `none`. -/
theorem denoteEO_none_inv {st : EStore} {v : Option Expr}
    (h : denoteEO st none = some v) : v = none :=
  (Option.some.inj h).symm

/-- con-leche: none — the absent handle denotes `none`. -/
@[bridge_grind =] theorem denoteEO_none_eq (st : EStore) : denoteEO st none = some none := rfl

/-- con-leche: none — `denoteEO` at a handle is its denotation, optionally. -/
@[bridge_grind =] theorem denoteEO_some_eq (st : EStore) (r : EIdx) :
    denoteEO st (some r) = (denoteE st r).map some := rfl

/-! ### Handle lists -/

/-- con-leche: none — the empty handle list denotes the empty list. -/
@[bridge_grind =] theorem denoteEList_nil_eq (st : EStore) :
    Frontend.denoteEList st [] = some [] := rfl

/-- con-leche: none — the empty handle list denotes the empty list. -/
theorem denoteEList_nil_inv {st : EStore} {xs : List Expr}
    (h : Frontend.denoteEList st [] = some xs) : xs = [] := by
  simp only [Frontend.denoteEList] at h; exact (Option.some.inj h).symm

/-- con-leche: none — a denoting cons is a cons of denotations. -/
theorem denoteEList_cons_inv {st : EStore} {a : EIdx} {as : List EIdx}
    {xs : List Expr} (h : Frontend.denoteEList st (a :: as) = some xs) :
    ∃ x xs', denoteE st a = some x ∧ Frontend.denoteEList st as = some xs' ∧
      xs = x :: xs' := by
  simp only [Frontend.denoteEList] at h
  cases ha : denoteE st a with
  | none => rw [ha] at h; simp at h
  | some x =>
    cases has : Frontend.denoteEList st as with
    | none => rw [ha, has] at h; simp at h
    | some xs' => rw [ha, has] at h; exact ⟨x, xs', rfl, rfl, (Option.some.inj h).symm⟩

/-- con-leche: none — a cons of handles denotes the cons of the head's and
the tail's denotations (`opt2`, an equation over the three denotation
terms). -/
@[bridge_grind =] theorem denoteEList_cons_eq (st : EStore) (a : EIdx) (as : List EIdx) :
    Frontend.denoteEList st (a :: as) =
      opt2 List.cons (denoteE st a) (Frontend.denoteEList st as) := by
  simp only [Frontend.denoteEList, opt2]
  cases denoteE st a <;> cases Frontend.denoteEList st as <;> rfl

/-- con-leche: none — the denotation of an appended handle list, as ONE
equation (`opt2` of the two halves). -/
theorem denoteEList_append_eq (st : EStore) (as bs : List EIdx) :
    Frontend.denoteEList st (as ++ bs) =
      opt2 HAppend.hAppend (Frontend.denoteEList st as) (Frontend.denoteEList st bs) := by
  induction as with
  | nil => cases h : Frontend.denoteEList st bs <;> simp [Frontend.denoteEList, opt2, h]
  | cons a as ih =>
    simp only [List.cons_append, Frontend.denoteEList, ih]
    cases denoteE st a <;> cases Frontend.denoteEList st as <;>
      cases Frontend.denoteEList st bs <;> rfl

/-- con-leche: none — an `opt2` that is `some` has both arguments present
(so that `denote_some_of_isSome` names them and `opt2_some_some` fires). -/
theorem opt2_isSome_of_eq_some {α β γ : Type} {f : α → β → γ} {a : Option α}
    {b : Option β} {c : γ} (h : opt2 f a b = some c) :
    a.isSome = true ∧ b.isSome = true := by
  cases a <;> cases b <;> simp_all [opt2]
grind_pattern [bridge_grind] opt2_isSome_of_eq_some => opt2 f a b, some c where
  guard opt2 f a b = some c

/-- con-leche: none — a handle list extended at the END denotes its
denotation's `concat`. -/
@[bridge_grind =] theorem denoteEList_concat_eq (st : EStore) (a : EIdx) :
    ∀ rs : List EIdx, Frontend.denoteEList st (rs ++ [a]) =
      opt2 List.concat (Frontend.denoteEList st rs) (denoteE st a)
  | [] => by
    simp only [List.nil_append, Frontend.denoteEList, opt2]
    cases denoteE st a <;> rfl
  | j :: js => by
    simp only [List.cons_append, Frontend.denoteEList, denoteEList_concat_eq st a js, opt2]
    cases denoteE st j <;> cases Frontend.denoteEList st js <;> cases denoteE st a <;> rfl

attribute [bridge_grind =] List.concat_eq_append

/-- con-leche: none — a handle list's length is its denotation's. -/
def EListLen (hs : List EIdx) : Option (List Expr) → Prop
  | some xs => xs.length = hs.length
  | none => True

/-- con-leche: none — `denoteEList_len` at the denotation term. -/
theorem eListLen (st : EStore) (hs : List EIdx) : EListLen hs (Frontend.denoteEList st hs) := by
  cases h : Frontend.denoteEList st hs with
  | none => trivial
  | some xs => exact denoteEList_len h
grind_pattern [bridge_grind] eListLen => Frontend.denoteEList st hs

/-- con-leche: none — `EListLen` at a denoting list. -/
theorem EListLen.some {hs : List EIdx} {xs : List Expr} (H : EListLen hs (some xs)) :
    xs.length = hs.length := H
grind_pattern [bridge_grind] EListLen.some => EListLen hs (some xs)

/-- con-leche: none — a denoting NAME-handle list keeps its length.
`Bridge/Rel.lean` has this at expression and level handles
(`denoteEList_len`, `denoteLList_len`) and not at names. -/
theorem denoteNList_len {st : NStore} :
    ∀ {hs : List NIdx} {xs : List ConLeche.Name},
      Frontend.denoteNList st hs = some xs → xs.length = hs.length
  | [], xs, h => by
    simp only [Frontend.denoteNList] at h
    obtain rfl := Option.some.inj h; rfl
  | a :: as, xs, h => by
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp [denoteNList_len has]

/-- con-leche: none — a name-handle list's length is its denotation's. -/
def NListLen (hs : List NIdx) : Option (List ConLeche.Name) → Prop
  | some xs => xs.length = hs.length
  | none => True

/-- con-leche: none — `denoteNList_len` at the denotation term. -/
theorem nListLen (st : NStore) (hs : List NIdx) :
    NListLen hs (Frontend.denoteNList st hs) := by
  cases h : Frontend.denoteNList st hs with
  | none => trivial
  | some xs => exact denoteNList_len h
grind_pattern [bridge_grind] nListLen => Frontend.denoteNList st hs

/-- con-leche: none — `NListLen` at a denoting list. -/
theorem NListLen.some {hs : List NIdx} {xs : List ConLeche.Name} (H : NListLen hs (some xs)) :
    xs.length = hs.length := H
grind_pattern [bridge_grind] NListLen.some => NListLen hs (some xs)

/-- con-leche: none — a denoting cons of level handles is a cons of denotations. -/
theorem denoteLList_cons_inv {st : LStore} {u : LIdx} {us : List LIdx} {L : List Level}
    (h : denoteLList st (u :: us) = some L) :
    ∃ l L', denoteL st u = some l ∧ denoteLList st us = some L' ∧ L = l :: L' := by
  simp only [denoteLList] at h
  cases h1 : denoteL st u <;> cases h2 : denoteLList st us <;> simp_all [opt2]

/-- con-leche: none — a denoting cons of name handles is a cons of denotations. -/
theorem denoteNList_cons_inv {st : NStore} {u : NIdx} {us : List NIdx} {L : List ConLeche.Name}
    (h : Frontend.denoteNList st (u :: us) = some L) :
    ∃ l L', denoteN st u = some l ∧ Frontend.denoteNList st us = some L' ∧ L = l :: L' := by
  simp only [Frontend.denoteNList] at h
  cases h1 : denoteN st u <;> cases h2 : Frontend.denoteNList st us <;> simp_all

/-! ### Membership in a name-handle list -/

/-- con-leche: none — **a handle comparison is a name comparison, at a LIST**:
`List.contains` over handles answers what `List.contains` over the denoted
names answers.  Both directions come from different places — `denoteN` is a
function (handles equal ⇒ names equal) and it is INJECTIVE (names equal ⇒
handles equal), which is DESIGN §8.3's soundness obligation cashed. -/
theorem denoteNList_contains {st : EStore} (hwf : StoreWF st) :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns ns = some xs →
      ∀ (n : NIdx) (x : ConLeche.Name), denoteN st.ns n = some x →
        ns.contains n = xs.contains x := by
  obtain ⟨rk, hrk⟩ := hwf
  have hns : NStoreWF st.ns := hrk.nsWF
  intro ns
  induction ns with
  | nil => intro xs h n x _; simp only [Frontend.denoteNList, Option.some.injEq] at h
           subst h; rfl
  | cons a as ih =>
    intro xs h n x hx
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        have hhead : (n == a) = (x == y) := by
          by_cases hae : a = n
          · subst hae
            rw [hx] at ha
            obtain rfl := Option.some.inj ha
            simp
          · have hae' : ¬ n = a := fun hh => hae hh.symm
            have hne' : ¬ x = y := by
              intro hxy; subst hxy
              exact hae (denoteN_inj hns ha hx)
            rw [beq_eq_false_iff_ne.mpr hae', beq_eq_false_iff_ne.mpr hne']
        simp only [List.contains_cons, hhead, ih ys has n x hx]

/-- con-leche: none — a name-list membership test at optional denotations. -/
def containsO : Option (List ConLeche.Name) → Option ConLeche.Name → Bool
  | some xs, some x => xs.contains x
  | _, _ => false

/-- con-leche: none — `containsO` at denoting subjects. -/
@[bridge_grind =] theorem containsO_some (xs : List ConLeche.Name) (x : ConLeche.Name) :
    containsO (some xs) (some x) = xs.contains x := rfl

/-- con-leche: none — `denoteNList_contains` as an equation: a handle-list
membership test is its denotations' (the store interns names injectively). -/
theorem contains_eq {st : EStore} (hwf : StoreWF st) (ns : List NIdx) (n : NIdx)
    (h1 : (Frontend.denoteNList st.ns ns).isSome = true) (h2 : (denoteN st.ns n).isSome = true) :
    ns.contains n = containsO (Frontend.denoteNList st.ns ns) (denoteN st.ns n) := by
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h2
  rw [hxs, hx]
  exact denoteNList_contains hwf ns xs hxs n x hx
grind_pattern [bridge_grind] contains_eq =>
  List.contains ns n, Frontend.denoteNList st.ns ns, denoteN st.ns n

/-- con-leche: none — `contains_eq` at `List.elem` (the spelling the twins'
`if` conditions reach `grind` in). -/
theorem elem_eq {st : EStore} (hwf : StoreWF st) (ns : List NIdx) (n : NIdx)
    (h1 : (Frontend.denoteNList st.ns ns).isSome = true) (h2 : (denoteN st.ns n).isSome = true) :
    List.elem n ns = containsO (Frontend.denoteNList st.ns ns) (denoteN st.ns n) :=
  contains_eq hwf ns n h1 h2
grind_pattern [bridge_grind] elem_eq =>
  List.elem n ns, Frontend.denoteNList st.ns ns, denoteN st.ns n

/-! ### The pin table

The names the reserved slots hold, as closed equations (`pinNames[i]?` at a
slot constant is what a pin read's answer is stated over). -/

/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT` slot names `natName`. -/
@[bridge_grind =] theorem pinNames_eq_natName : pinNames[PIN_NAT]? = some ConLeche.natName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_ZERO` slot names `natZeroName`. -/
@[bridge_grind =] theorem pinNames_eq_natZeroName : pinNames[PIN_NAT_ZERO]? = some ConLeche.natZeroName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_SUCC` slot names `natSuccName`. -/
@[bridge_grind =] theorem pinNames_eq_natSuccName : pinNames[PIN_NAT_SUCC]? = some ConLeche.natSuccName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_PRED` slot names `natPredName`. -/
@[bridge_grind =] theorem pinNames_eq_natPredName : pinNames[PIN_NAT_PRED]? = some ConLeche.natPredName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_ADD` slot names `natAddName`. -/
@[bridge_grind =] theorem pinNames_eq_natAddName : pinNames[PIN_NAT_ADD]? = some ConLeche.natAddName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_SUB` slot names `natSubName`. -/
@[bridge_grind =] theorem pinNames_eq_natSubName : pinNames[PIN_NAT_SUB]? = some ConLeche.natSubName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_MUL` slot names `natMulName`. -/
@[bridge_grind =] theorem pinNames_eq_natMulName : pinNames[PIN_NAT_MUL]? = some ConLeche.natMulName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_POW` slot names `natPowName`. -/
@[bridge_grind =] theorem pinNames_eq_natPowName : pinNames[PIN_NAT_POW]? = some ConLeche.natPowName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_BEQ` slot names `natBeqName`. -/
@[bridge_grind =] theorem pinNames_eq_natBeqName : pinNames[PIN_NAT_BEQ]? = some ConLeche.natBeqName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_BLE` slot names `natBleName`. -/
@[bridge_grind =] theorem pinNames_eq_natBleName : pinNames[PIN_NAT_BLE]? = some ConLeche.natBleName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_DIV` slot names `natDivName`. -/
@[bridge_grind =] theorem pinNames_eq_natDivName : pinNames[PIN_NAT_DIV]? = some ConLeche.natDivName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_MOD` slot names `natModName`. -/
@[bridge_grind =] theorem pinNames_eq_natModName : pinNames[PIN_NAT_MOD]? = some ConLeche.natModName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_GCD` slot names `natGcdName`. -/
@[bridge_grind =] theorem pinNames_eq_natGcdName : pinNames[PIN_NAT_GCD]? = some ConLeche.natGcdName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_LAND` slot names `natLandName`. -/
@[bridge_grind =] theorem pinNames_eq_natLandName : pinNames[PIN_NAT_LAND]? = some ConLeche.natLandName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_LOR` slot names `natLorName`. -/
@[bridge_grind =] theorem pinNames_eq_natLorName : pinNames[PIN_NAT_LOR]? = some ConLeche.natLorName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_XOR` slot names `natXorName`. -/
@[bridge_grind =] theorem pinNames_eq_natXorName : pinNames[PIN_NAT_XOR]? = some ConLeche.natXorName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_SHIFT_LEFT` slot names `natShiftLeftName`. -/
@[bridge_grind =] theorem pinNames_eq_natShiftLeftName : pinNames[PIN_NAT_SHIFT_LEFT]? = some ConLeche.natShiftLeftName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_NAT_SHIFT_RIGHT` slot names `natShiftRightName`. -/
@[bridge_grind =] theorem pinNames_eq_natShiftRightName : pinNames[PIN_NAT_SHIFT_RIGHT]? = some ConLeche.natShiftRightName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_BOOL_TRUE` slot names `boolTrueName`. -/
@[bridge_grind =] theorem pinNames_eq_boolTrueName : pinNames[PIN_BOOL_TRUE]? = some ConLeche.boolTrueName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_BOOL_FALSE` slot names `boolFalseName`. -/
@[bridge_grind =] theorem pinNames_eq_boolFalseName : pinNames[PIN_BOOL_FALSE]? = some ConLeche.boolFalseName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_STRING` slot names `stringName`. -/
@[bridge_grind =] theorem pinNames_eq_stringName : pinNames[PIN_STRING]? = some ConLeche.stringName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_STRING_OF_LIST` slot names `stringOfListName`. -/
@[bridge_grind =] theorem pinNames_eq_stringOfListName : pinNames[PIN_STRING_OF_LIST]? = some ConLeche.stringOfListName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_LIST` slot names `listName`. -/
@[bridge_grind =] theorem pinNames_eq_listName : pinNames[PIN_LIST]? = some ConLeche.listName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_LIST_NIL` slot names `listNilName`. -/
@[bridge_grind =] theorem pinNames_eq_listNilName : pinNames[PIN_LIST_NIL]? = some ConLeche.listNilName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_LIST_CONS` slot names `listConsName`. -/
@[bridge_grind =] theorem pinNames_eq_listConsName : pinNames[PIN_LIST_CONS]? = some ConLeche.listConsName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_CHAR` slot names `charName`. -/
@[bridge_grind =] theorem pinNames_eq_charName : pinNames[PIN_CHAR]? = some ConLeche.charName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_CHAR_OF_NAT` slot names `charOfNatName`. -/
@[bridge_grind =] theorem pinNames_eq_charOfNatName : pinNames[PIN_CHAR_OF_NAT]? = some ConLeche.charOfNatName := rfl

/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the
`PIN_AND` slot names `andName`. -/
@[bridge_grind =] theorem pinNames_eq_andName : pinNames[PIN_AND]? = some ConLeche.andName := rfl

/-! ## 5. The memo tables

`Bridge/StateOK.lean`'s four uses of the generic expression memo invariant,
keyed by the invariant and the table term the program builds: the hit at a
probe the program matched (guarded, so it fires at that probe only), the
insert at the update's table term, the dropped table (guarded: a table known
to be empty).  The transport is §2's `MemoOK.le`. -/

grind_pattern [bridge_grind] MemoOK.get => MemoOK f tbl st, tbl[k]?, some r where
  guard tbl[k]? = some r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:67-79 Inst1MemoInv.insert — the
insert at the table term the update builds. -/
theorem MemoOK.insert_at {f : Nat → Expr → Expr} {tbl : Std.HashMap (EIdx × Nat) EIdx}
    {st : EStore} {k : EIdx × Nat} {r : EIdx} (hm : MemoOK f tbl st)
    (hk : (denoteE st k.1).isSome = true) (hr : RelE (f k.2) st k.1 st r) :
    MemoOK f (tbl.insert k r) st := MemoOK.insert hm rfl hk hr
grind_pattern [bridge_grind] MemoOK.insert_at => MemoOK f (tbl.insert k r) st

grind_pattern [bridge_grind] MemoOK.of_empty => MemoOK f tbl st where
  guard tbl = ∅

/-! The handle-keyed, value-valued invariant `MemoVOK` and the level memos'
hits, in the same shape. -/

grind_pattern [bridge_grind] MemoVOK.get => MemoVOK f tbl st, tbl[k]?, some v where
  guard tbl[k]? = some v

grind_pattern [bridge_grind] MemoVOK.insert => MemoVOK f tbl' st, tbl.insert k v where
  guard tbl' = tbl.insert k v

grind_pattern [bridge_grind] MemoVOK.of_empty => MemoVOK f tbl st where
  guard tbl = ∅

grind_pattern [bridge_grind] MemoLOK.get => MemoLOK f tbl st, tbl[k]?, some r where
  guard tbl[k]? = some r

grind_pattern [bridge_grind] MemoLsOK.get => MemoLsOK f tbl st, tbl[k]?, some r where
  guard tbl[k]? = some r

grind_pattern [bridge_grind] MemoLOK.of_empty => MemoLOK f tbl st where
  guard tbl = ∅

grind_pattern [bridge_grind] MemoLsOK.of_empty => MemoLsOK f tbl st where
  guard tbl = ∅

/-! ## 6. Views and tags as equations -/

/-- con-leche: none — **the constructor tag of a denotation**: the four tag
bits of a handle are the tag of the expression it denotes. -/
def exprTag : Expr → UInt32
  | .bvar _ => ETag.bvar
  | .fvar _ _ => ETag.fvar
  | .sort _ => ETag.sort
  | .const _ _ => ETag.const
  | .app _ _ => ETag.app
  | .lam _ _ => ETag.lam
  | .forallE _ _ => ETag.forallE
  | .letE _ _ _ => ETag.letE
  | .lit _ => ETag.lit
  | .proj _ _ _ => ETag.proj

/-- con-leche: none — DESIGN §8.3: a handle's tag is its denotation's. -/
theorem tag_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) : h.tag = exprTag e := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  rw [EStore.tagOf_of_view hv]
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv hd]; rfl
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv hd; rfl
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hd; rfl
  | const n us => obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv hd; rfl
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv hd; rfl
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv hd; rfl
  | forallE ty b =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv hd; rfl
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv hd; rfl
  | lit l => rw [denote_lit_inv hwf hv hd]; rfl
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv hd; rfl

/-! The fields of an expression as total projections (the expression itself, or
a default, off their constructor): what a view's children denote, without a
fresh variable. -/

/-- con-leche: none — the function of an application. -/
def exprFn : Expr → Expr | .app f _ => f | e => e
/-- con-leche: none — the argument of an application. -/
def exprArg : Expr → Expr | .app _ a => a | e => e
/-- con-leche: none — the name of a constant. -/
def exprConstName : Expr → ConLeche.Name | .const n _ => n | _ => .anonymous
/-- con-leche: none — the universe arguments of a constant. -/
def exprConstLevels : Expr → List Level | .const _ us => us | _ => []
/-- con-leche: none — the index of a bound variable. -/
def exprBVar : Expr → Nat | .bvar i => i | _ => 0
/-- con-leche: none — the index of a free variable. -/
def exprFVarIdx : Expr → Nat | .fvar k _ => k | _ => 0
/-- con-leche: none — the type of a free variable. -/
def exprFVarType : Expr → Expr | .fvar _ t => t | e => e
/-- con-leche: none — the level of a sort. -/
def exprSort : Expr → Level | .sort u => u | _ => .zero
/-- con-leche: none — the binder type of a `lam`/`forallE`/`letE`. -/
def exprBinderType : Expr → Expr
  | .lam t _ => t | .forallE t _ => t | .letE t _ _ => t | e => e
/-- con-leche: none — the body of a `lam`/`forallE`/`letE`. -/
def exprBody : Expr → Expr
  | .lam _ b => b | .forallE _ b => b | .letE _ _ b => b | e => e
/-- con-leche: none — the value of a `letE`. -/
def exprLetVal : Expr → Expr | .letE _ v _ => v | e => e
/-- con-leche: none — the literal of a `lit`. -/
def exprLit : Expr → Literal | .lit l => l | _ => .natVal 0
/-- con-leche: none — the structure name of a projection. -/
def exprProjName : Expr → ConLeche.Name | .proj n _ _ => n | _ => .anonymous
/-- con-leche: none — the field index of a projection. -/
def exprProjIdx : Expr → Nat | .proj _ i _ => i | _ => 0
/-- con-leche: none — the projected structure. -/
def exprProjStruct : Expr → Expr | .proj _ _ s => s | e => e

/-! A literal's two readings, and `Expr.isStrLit` over them. -/

/-- con-leche: none — a literal's `Nat`, if it is one. -/
def litNat? : Literal → Option Nat | .natVal n => some n | .strVal _ => none
attribute [bridge_grind =] litNat?

/-- con-leche: none — a literal's string, if it is one. -/
def litStr? : Literal → Option String | .strVal s => some s | .natVal _ => none
attribute [bridge_grind =] litStr?

/-- con-leche: ConLeche/Kernel/Core.lean:687-691 Expr.isStrLit — as one equation over
the tag and the literal. -/
theorem isStrLit_eq (e : Expr) :
    e.isStrLit = (exprTag e == ETag.lit && (litStr? (exprLit e)).isSome) := by
  cases e <;> try rfl
  rename_i l; cases l <;> rfl

/-! **A denotation's constructor from its tag**: an expression whose tag is
KNOWN is its constructor applied to its projections.  Guarded — the lemma
fires only where congruence closure already has `exprTag e = ETag.k`;
unguarded, every `exprTag e` term instantiates all ten, and `grind` splits on
the equalities between the (opaque) tag constants. -/

/-- con-leche: none — an expression tagged `bvar` IS a bound variable. -/
theorem exprTag_bvar {e : Expr} (h : exprTag e = ETag.bvar) : e = .bvar (exprBVar e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_bvar => exprTag e where
  guard exprTag e = ETag.bvar

/-- con-leche: none — an expression tagged `fvar` IS a free variable. -/
theorem exprTag_fvar {e : Expr} (h : exprTag e = ETag.fvar) :
    e = .fvar (exprFVarIdx e) (exprFVarType e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_fvar => exprTag e where
  guard exprTag e = ETag.fvar

/-- con-leche: none — an expression tagged `sort` IS a sort. -/
theorem exprTag_sort {e : Expr} (h : exprTag e = ETag.sort) : e = .sort (exprSort e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_sort => exprTag e where
  guard exprTag e = ETag.sort

/-- con-leche: none — an expression tagged `const` IS a constant. -/
theorem exprTag_const {e : Expr} (h : exprTag e = ETag.const) :
    e = .const (exprConstName e) (exprConstLevels e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_const => exprTag e where
  guard exprTag e = ETag.const

/-- con-leche: none — an expression tagged `app` IS an application. -/
theorem exprTag_app {e : Expr} (h : exprTag e = ETag.app) :
    e = .app (exprFn e) (exprArg e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_app => exprTag e where
  guard exprTag e = ETag.app

/-- con-leche: none — an expression tagged `lam` IS a λ. -/
theorem exprTag_lam {e : Expr} (h : exprTag e = ETag.lam) :
    e = .lam (exprBinderType e) (exprBody e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_lam => exprTag e where
  guard exprTag e = ETag.lam

/-- con-leche: none — an expression tagged `forallE` IS a ∀. -/
theorem exprTag_forallE {e : Expr} (h : exprTag e = ETag.forallE) :
    e = .forallE (exprBinderType e) (exprBody e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_forallE => exprTag e where
  guard exprTag e = ETag.forallE

/-- con-leche: none — an expression tagged `letE` IS a `let`. -/
theorem exprTag_letE {e : Expr} (h : exprTag e = ETag.letE) :
    e = .letE (exprBinderType e) (exprLetVal e) (exprBody e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_letE => exprTag e where
  guard exprTag e = ETag.letE

/-- con-leche: none — an expression tagged `lit` IS a literal. -/
theorem exprTag_lit {e : Expr} (h : exprTag e = ETag.lit) : e = .lit (exprLit e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_lit => exprTag e where
  guard exprTag e = ETag.lit

/-- con-leche: none — an expression tagged `proj` IS a projection. -/
theorem exprTag_proj {e : Expr} (h : exprTag e = ETag.proj) :
    e = .proj (exprProjName e) (exprProjIdx e) (exprProjStruct e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_proj => exprTag e where
  guard exprTag e = ETag.proj

open Classical in
/-- con-leche: none — **the name handle of a name**, `denoteN`'s inverse on
the names the store denotes (DESIGN §8.3's "index equality IS structural
equality" as a function): with it, two handles are equal iff their names are
by congruence closure alone. -/
noncomputable def idxOfName (st : NStore) (nm : ConLeche.Name) : NIdx :=
  if h : ∃ n, denoteN st n = some nm then Classical.choose h else default

/-- con-leche: none — `idxOfName` inverts `denoteN` (its injectivity). -/
theorem idxOfName_eq {st : NStore} (hwf : NStoreWF st) {n : NIdx} {nm : ConLeche.Name}
    (h : denoteN st n = some nm) : idxOfName st nm = n := by
  have hex : ∃ n, denoteN st n = some nm := ⟨n, h⟩
  simp only [idxOfName, hex, dite_true]
  exact denoteN_inj hwf (Classical.choose_spec hex) h

/-- con-leche: none — two name handles of one store with one denotation are one handle
(`denoteN`'s injectivity), instantiated only for pairs `grind` knows to denote alike. -/
theorem nidx_eq_of_denote {st : EStore} (hwf : StoreWF st) {a b : NIdx}
    (h : denoteN st.ns a = denoteN st.ns b) (hs : denoteN st.ns a ≠ none) : a = b := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hs
  obtain ⟨rk, hrk⟩ := hwf
  exact denoteN_inj hrk.nsWF hx (h ▸ hx)
grind_pattern [bridge_grind] nidx_eq_of_denote => StoreWF st, denoteN st.ns a, denoteN st.ns b where
  guard denoteN st.ns a = denoteN st.ns b
  a =/= b

/-! **The handle inverses at the other stores** (`idxOfName` at the level-list
and expression stores, and the name store's keyed by the denotation term).
Each fires on EVERY denotation term in sight, which costs the walks that never
compare handles 10–20 % (measured on the `ExprOps` tier), so they are NOT
registered here: the walks that compare a handle against a pin or an interned
list (`Core/Walks/{Nat,StrLit}.lean`) register them locally, with
`ETag`'s and `exprTag`'s defining equations (the tags as literals). -/

/-- con-leche: none — **the name handle of a denoted name** at the name
store, keyed by the denotation term (`idxOfName_eq` as a fact): with it, a
handle test against a pin is the name test by congruence closure. -/
def NameIdx (st : NStore) (n : NIdx) : Option ConLeche.Name → Prop
  | some nm => idxOfName st nm = n
  | none => True

/-- con-leche: none — every denoting name handle is its name's handle. -/
theorem nameIdx {st : EStore} (hwf : StoreWF st) (n : NIdx) :
    NameIdx st.ns n (denoteN st.ns n) := by
  cases h : denoteN st.ns n with
  | none => trivial
  | some nm => obtain ⟨rk, hrk⟩ := hwf; exact idxOfName_eq hrk.nsWF h

/-- con-leche: none — `NameIdx` at a denoting handle. -/
theorem NameIdx.some {st : NStore} {n : NIdx} {nm : ConLeche.Name}
    (H : NameIdx st n (some nm)) : idxOfName st nm = n := H

open Classical in
/-- con-leche: none — **the level-list handle of a level list**, `denoteLs`'s
inverse on the lists the store denotes (`idxOfName` at the level-list
store). -/
noncomputable def idxOfLs (st : LsStore) (ls : List Level) : LsIdx :=
  if h : ∃ n, denoteLs st n = some ls then Classical.choose h else default

/-- con-leche: none — a denoting level-list handle is its list's handle. -/
def LsIdxAt (st : LsStore) (n : LsIdx) : Option (List Level) → Prop
  | some ls => idxOfLs st ls = n
  | none => True

/-- con-leche: none — `idxOfLs` inverts `denoteLs` (`denoteLs_inj`). -/
theorem lsIdxAt {st : EStore} (hwf : StoreWF st) (n : LsIdx) :
    LsIdxAt st.lss n (denoteLs st.lss n) := by
  cases h : denoteLs st.lss n with
  | none => trivial
  | some ls =>
    obtain ⟨rk, hrk⟩ := hwf
    have hex : ∃ n, denoteLs st.lss n = some ls := ⟨n, h⟩
    show idxOfLs _ _ = _
    simp only [idxOfLs, hex, dite_true]
    exact denoteLs_inj hrk.lss (Classical.choose_spec hex) h

/-- con-leche: none — `LsIdxAt` at a denoting handle. -/
theorem LsIdxAt.some {st : LsStore} {n : LsIdx} {ls : List Level}
    (H : LsIdxAt st n (some ls)) : idxOfLs st ls = n := H

open Classical in
/-- con-leche: none — **the expression handle of an expression**, `denoteE`'s
inverse on the expressions the store denotes (DESIGN §8.3 at the expression
store, `denoteE_inj`). -/
noncomputable def idxOfExpr (st : EStore) (e : Expr) : EIdx :=
  if h : ∃ n, denoteE st n = some e then Classical.choose h else default

/-- con-leche: none — a denoting expression handle is its expression's
handle. -/
def EIdxAt (st : EStore) (n : EIdx) : Option Expr → Prop
  | some e => idxOfExpr st e = n
  | none => True

/-- con-leche: none — `idxOfExpr` inverts `denoteE`. -/
theorem eIdxAt {st : EStore} (hwf : StoreWF st) (n : EIdx) : EIdxAt st n (denoteE st n) := by
  cases h : denoteE st n with
  | none => trivial
  | some e =>
    have hex : ∃ n, denoteE st n = some e := ⟨n, h⟩
    show idxOfExpr _ _ = _
    simp only [idxOfExpr, hex, dite_true]
    exact denoteE_inj hwf (Classical.choose_spec hex) h

/-- con-leche: none — `EIdxAt` at a denoting handle. -/
theorem EIdxAt.some {st : EStore} {n : EIdx} {e : Expr} (H : EIdxAt st n (some e)) :
    idxOfExpr st e = n := H

/-- con-leche: none — **what a view says about the denotation**: at a denoting
handle (view `ov`, denotation `oe`), each child of the view denotes the
matching projection.  `denote_view` states it of every handle whose view and
denotation the walk reads; the extraction lemmas below fire once the view's
constructor is known. -/
def DenoteView (st : EStore) : Option ENodeView → Option Expr → Prop
  | some v, some e => match v with
    | .bvar i => exprBVar e = i
    | .fvar k ty => exprFVarIdx e = k ∧ denoteE st ty = some (exprFVarType e)
    | .sort u => denoteL st.ls u = some (exprSort e)
    | .const c us => denoteN st.ns c = some (exprConstName e) ∧
        idxOfName st.ns (exprConstName e) = c ∧ denoteLs st.lss us = some (exprConstLevels e)
    | .app f a => denoteE st f = some (exprFn e) ∧ denoteE st a = some (exprArg e)
    | .lam ty b => denoteE st ty = some (exprBinderType e) ∧ denoteE st b = some (exprBody e)
    | .forallE ty b =>
      denoteE st ty = some (exprBinderType e) ∧ denoteE st b = some (exprBody e)
    | .letE ty w b => denoteE st ty = some (exprBinderType e) ∧
        denoteE st w = some (exprLetVal e) ∧ denoteE st b = some (exprBody e)
    | .lit l => exprLit e = l
    | .proj n i sub => denoteN st.ns n = some (exprProjName e) ∧
        idxOfName st.ns (exprProjName e) = n ∧ exprProjIdx e = i ∧
        denoteE st sub = some (exprProjStruct e)
  | _, _ => True

/-- con-leche: none — **a viewed handle's view fact**, keyed by its view and
its denotation (a walk that never views a handle pays nothing for it). -/
theorem denote_view {st : EStore} (hwf : StoreWF st) (h : EIdx) :
    DenoteView st (st.view h) (denoteE st h) := by
  cases he : denoteE st h with
  | none => cases st.view h <;> trivial
  | some e =>
  obtain ⟨v, hv⟩ := denoteE_view he
  rw [hv]
  have hns : NStoreWF st.ns := by obtain ⟨rk, hrk⟩ := hwf; exact hrk.nsWF
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; rfl
  | fvar k t => obtain ⟨_, rfl, h1⟩ := denote_fvar_inv hwf hv he; exact ⟨rfl, h1⟩
  | sort u => obtain ⟨_, rfl, h1⟩ := denote_sort_inv hwf hv he; exact h1
  | const n us =>
    obtain ⟨_, _, rfl, h1, h2⟩ := denote_const_inv hwf hv he
    exact ⟨h1, idxOfName_eq hns h1, h2⟩
  | app f a => obtain ⟨_, _, rfl, h1, h2⟩ := denote_app_inv hwf hv he; exact ⟨h1, h2⟩
  | lam ty b => obtain ⟨_, _, rfl, h1, h2⟩ := denote_lam_inv hwf hv he; exact ⟨h1, h2⟩
  | forallE ty b =>
    obtain ⟨_, _, rfl, h1, h2⟩ := denote_forallE_inv hwf hv he; exact ⟨h1, h2⟩
  | letE ty w b =>
    obtain ⟨_, _, _, rfl, h1, h2, h3⟩ := denote_letE_inv hwf hv he; exact ⟨h1, h2, h3⟩
  | lit l => rw [denote_lit_inv hwf hv he]; rfl
  | proj n i sub =>
    obtain ⟨_, _, rfl, h1, h2⟩ := denote_proj_inv hwf hv he
    exact ⟨h1, idxOfName_eq hns h1, rfl, h2⟩
grind_pattern [bridge_grind] denote_view => st.view h, denoteE st h

/-! The extraction lemmas, one per constructor a walk views, each keyed by the
`DenoteView` fact at a known constructor and a denoting handle. -/

/-- con-leche: none — a `bvar` view's index is the bound variable's. -/
theorem DenoteView.bvar {st : EStore} {i : Nat} {e : Expr}
    (H : DenoteView st (some (.bvar i)) (some e)) : exprBVar e = i := H
grind_pattern [bridge_grind] DenoteView.bvar => DenoteView st (some (.bvar i)) (some e)

/-- con-leche: none — an `fvar` view's index and type annotation. -/
theorem DenoteView.fvar {st : EStore} {k : Nat} {ty : EIdx} {e : Expr}
    (H : DenoteView st (some (.fvar k ty)) (some e)) :
    exprFVarIdx e = k ∧ denoteE st ty = some (exprFVarType e) := H
grind_pattern [bridge_grind] DenoteView.fvar => DenoteView st (some (.fvar k ty)) (some e)

/-- con-leche: none — a `sort` view's level. -/
theorem DenoteView.sort {st : EStore} {u : LIdx} {e : Expr}
    (H : DenoteView st (some (.sort u)) (some e)) : denoteL st.ls u = some (exprSort e) := H
grind_pattern [bridge_grind] DenoteView.sort => DenoteView st (some (.sort u)) (some e)

/-- con-leche: none — a `const` view's name handle denotes the constant's name
(and is that name's handle), its level list the constant's levels. -/
theorem DenoteView.const {st : EStore} {c : NIdx} {us : LsIdx} {e : Expr}
    (H : DenoteView st (some (.const c us)) (some e)) :
    denoteN st.ns c = some (exprConstName e) ∧ idxOfName st.ns (exprConstName e) = c ∧
      denoteLs st.lss us = some (exprConstLevels e) := H
grind_pattern [bridge_grind] DenoteView.const => DenoteView st (some (.const c us)) (some e)

/-- con-leche: none — an `app` view's children denote the application's
function and argument. -/
theorem DenoteView.app {st : EStore} {f a : EIdx} {e : Expr}
    (H : DenoteView st (some (.app f a)) (some e)) :
    denoteE st f = some (exprFn e) ∧ denoteE st a = some (exprArg e) := H
grind_pattern [bridge_grind] DenoteView.app => DenoteView st (some (.app f a)) (some e)

/-- con-leche: none — a `lam` view's children. -/
theorem DenoteView.lam {st : EStore} {ty b : EIdx} {e : Expr}
    (H : DenoteView st (some (.lam ty b)) (some e)) :
    denoteE st ty = some (exprBinderType e) ∧ denoteE st b = some (exprBody e) := H
grind_pattern [bridge_grind] DenoteView.lam => DenoteView st (some (.lam ty b)) (some e)

/-- con-leche: none — a `forallE` view's children. -/
theorem DenoteView.forallE {st : EStore} {ty b : EIdx} {e : Expr}
    (H : DenoteView st (some (.forallE ty b)) (some e)) :
    denoteE st ty = some (exprBinderType e) ∧ denoteE st b = some (exprBody e) := H
grind_pattern [bridge_grind] DenoteView.forallE =>
  DenoteView st (some (.forallE ty b)) (some e)

/-- con-leche: none — a `letE` view's children. -/
theorem DenoteView.letE {st : EStore} {ty w b : EIdx} {e : Expr}
    (H : DenoteView st (some (.letE ty w b)) (some e)) :
    denoteE st ty = some (exprBinderType e) ∧ denoteE st w = some (exprLetVal e) ∧
      denoteE st b = some (exprBody e) := H
grind_pattern [bridge_grind] DenoteView.letE => DenoteView st (some (.letE ty w b)) (some e)

/-- con-leche: none — a `lit` view's denotation is that literal (its
projection). -/
theorem DenoteView.lit {st : EStore} {l : Literal} {e : Expr}
    (H : DenoteView st (some (.lit l)) (some e)) : exprLit e = l := H
grind_pattern [bridge_grind] DenoteView.lit => DenoteView st (some (.lit l)) (some e)

/-- con-leche: none — a `proj` view's struct name (and its handle), index and
subject. -/
theorem DenoteView.proj {st : EStore} {n : NIdx} {i : Nat} {sub : EIdx} {e : Expr}
    (H : DenoteView st (some (.proj n i sub)) (some e)) :
    denoteN st.ns n = some (exprProjName e) ∧ idxOfName st.ns (exprProjName e) = n ∧
      exprProjIdx e = i ∧ denoteE st sub = some (exprProjStruct e) := H
grind_pattern [bridge_grind] DenoteView.proj => DenoteView st (some (.proj n i sub)) (some e)

/-- con-leche: none — a denotation's constructor is its handle's tag. -/
def DenoteTag (h : EIdx) : Option Expr → Prop
  | some e => exprTag e = h.tag
  | none => True

/-- con-leche: none — `tag_of_denote` at a handle whose tag the walk tests,
keyed by the tag and the denotation. -/
theorem denote_tag {st : EStore} (hwf : StoreWF st) (h : EIdx) :
    DenoteTag h (denoteE st h) := by
  cases he : denoteE st h with
  | none => trivial
  | some e => exact (tag_of_denote hwf he).symm
grind_pattern [bridge_grind] denote_tag => Idx.tag h, denoteE st h

/-- con-leche: none — `DenoteTag` at a denoting handle. -/
theorem DenoteTag.some {h : EIdx} {e : Expr} (H : DenoteTag h (some e)) :
    exprTag e = h.tag := H
grind_pattern [bridge_grind] DenoteTag.some => DenoteTag h (some e)

/-! ### The view side: tags, projections, presence -/

/-- con-leche: none — a view's tag is its handle's (`EStore.tagOf_of_view`
at an optional view, keyed by the view term). -/
def ViewTag (h : EIdx) : Option ENodeView → Prop
  | some v => v.tagOf = h.tag
  | none => True

/-- con-leche: none — every view carries its handle's tag. -/
theorem view_tag (st : EStore) (h : EIdx) : ViewTag h (st.view h) := by
  cases hv : st.view h with
  | none => trivial
  | some v => exact (EStore.tagOf_of_view hv).symm
grind_pattern [bridge_grind] view_tag => st.view h

/-- con-leche: none — `ViewTag` at a present view. -/
theorem ViewTag.some {h : EIdx} {v : ENodeView} (H : ViewTag h (some v)) : v.tagOf = h.tag := H
grind_pattern [bridge_grind] ViewTag.some => ViewTag h (some v)

attribute [bridge_grind =] ENodeView.tagOf

/-- con-leche: none — the function handle of an `app` view (a default
elsewhere). -/
def nodeFn : ENodeView → EIdx | .app f _ => f | _ => default
/-- con-leche: none — the argument handle of an `app` view. -/
def nodeArg : ENodeView → EIdx | .app _ a => a | _ => default
/-- con-leche: none — the name handle of a `const` view. -/
def nodeConstName : ENodeView → NIdx | .const n _ => n | _ => default
/-- con-leche: none — the level-list handle of a `const` view. -/
def nodeConstLevels : ENodeView → LsIdx | .const _ us => us | _ => default

/-- con-leche: none — a view tagged `app` IS an `app` view: what refutes a
`match`'s fall-through arm after the walk tested the tag.  Guarded, as
`exprTag_app` is. -/
theorem ENodeView.tagOf_app {v : ENodeView} (h : v.tagOf = ETag.app) :
    v = .app (nodeFn v) (nodeArg v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_app => ENodeView.tagOf v where
  guard ENodeView.tagOf v = ETag.app

/-- con-leche: none — a view tagged `const` IS a `const` view. -/
theorem ENodeView.tagOf_const {v : ENodeView} (h : v.tagOf = ETag.const) :
    v = .const (nodeConstName v) (nodeConstLevels v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_const => ENodeView.tagOf v where
  guard ENodeView.tagOf v = ETag.const

/-- con-leche: none — the binder-type handle of a `forallE`/`lam` view. -/
def nodeBinderType : ENodeView → EIdx | .forallE t _ => t | .lam t _ => t | _ => default
/-- con-leche: none — the body handle of a `forallE`/`lam` view. -/
def nodeBody : ENodeView → EIdx | .forallE _ b => b | .lam _ b => b | _ => default
/-- con-leche: none — the literal of a `lit` view. -/
def nodeLit : ENodeView → Literal | .lit l => l | _ => .natVal 0
/-- con-leche: none — the handle of an `fvar` view's type. -/
def nodeFVarType : ENodeView → EIdx | .fvar _ t => t | _ => default
/-- con-leche: none — the index of an `fvar` view. -/
def nodeFVarIdx : ENodeView → Nat | .fvar k _ => k | _ => 0
/-- con-leche: none — the index of a `bvar` view. -/
def nodeBVar : ENodeView → Nat | .bvar i => i | _ => 0
/-- con-leche: none — the level of a `sort` view. -/
def nodeSort : ENodeView → LIdx | .sort u => u | _ => default
/-- con-leche: none — the name handle of a `proj` view. -/
def nodeProjName : ENodeView → NIdx | .proj n _ _ => n | _ => default
/-- con-leche: none — the field index of a `proj` view. -/
def nodeProjIdx : ENodeView → Nat | .proj _ i _ => i | _ => 0
/-- con-leche: none — the structure handle of a `proj` view. -/
def nodeProjStruct : ENodeView → EIdx | .proj _ _ s => s | _ => default

/-- con-leche: none — a view tagged `forallE` IS a `forallE` view. -/
theorem ENodeView.tagOf_forallE {v : ENodeView} (h : v.tagOf = ETag.forallE) :
    v = .forallE (nodeBinderType v) (nodeBody v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_forallE => ENodeView.tagOf v where
  guard ENodeView.tagOf v = ETag.forallE

/-- con-leche: none — a view tagged `lit` IS a `lit` view. -/
theorem ENodeView.tagOf_lit {v : ENodeView} (h : v.tagOf = ETag.lit) : v = .lit (nodeLit v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_lit => ENodeView.tagOf v where
  guard ENodeView.tagOf v = ETag.lit

/-- con-leche: none — a view tagged `fvar` IS an `fvar` view. -/
theorem ENodeView.tagOf_fvar {v : ENodeView} (h : v.tagOf = ETag.fvar) :
    v = .fvar (nodeFVarIdx v) (nodeFVarType v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_fvar => ENodeView.tagOf v where
  guard ENodeView.tagOf v = ETag.fvar

/-- con-leche: none — a view tagged `bvar` IS a `bvar` view. -/
theorem ENodeView.tagOf_bvar {v : ENodeView} (h : v.tagOf = ETag.bvar) :
    v = .bvar (nodeBVar v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_bvar => ENodeView.tagOf v where
  guard ENodeView.tagOf v = ETag.bvar

/-- con-leche: none — a view tagged `sort` IS a `sort` view. -/
theorem ENodeView.tagOf_sort {v : ENodeView} (h : v.tagOf = ETag.sort) :
    v = .sort (nodeSort v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_sort => ENodeView.tagOf v where
  guard ENodeView.tagOf v = ETag.sort

/-- con-leche: none — a view tagged `proj` IS a `proj` view. -/
theorem ENodeView.tagOf_proj {v : ENodeView} (h : v.tagOf = ETag.proj) :
    v = .proj (nodeProjName v) (nodeProjIdx v) (nodeProjStruct v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_proj => ENodeView.tagOf v where
  guard ENodeView.tagOf v = ETag.proj

/-! The one-constructor projections the tag-dispatching walks read
(`Bridge/Rel.lean` group 5) give the view, guarded so that each fires at the
projection the program read and nowhere else; `denote_view` then turns the
view into the `DenoteView` fact. -/

grind_pattern [bridge_grind] view_of_viewBVar => st.viewBVar i, some k where
  guard st.viewBVar i = some k
/-- con-leche: none — the head-NAME projection of a `const` node, against
`view`. -/
theorem view_of_viewConstName {st : EStore} {i : EIdx} {n : NIdx}
    (htg : i.tag = ETag.const) (h : st.viewConstName i = some n) :
    ∃ us, st.view i = some (.const n us) := by
  have key : ∀ t : ETables, t.getConstName i = some n →
      ∃ us, t.get i = some (.const n us) := by
    intro t ht
    simp only [ETables.getConstName, Option.map_eq_some_iff] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    exact ⟨r.us, ETables.get_of_getConst htg (by simp [ETables.getConst, hr])⟩
  simp only [EStore.viewConstName, EStore.persGetConstName] at h
  simp only [EStore.view]
  by_cases hp : i.isPersistent = true
  · rw [ite_eq_left hp] at h ⊢; exact key _ h
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h ⊢
    simp only [Bool.false_eq_true, ite_false] at h ⊢
    by_cases hon : st.scratchOn = true
    · rw [ite_eq_left hon] at h ⊢; exact key _ h
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

grind_pattern [bridge_grind] view_of_viewSort => st.viewSort i, some u where
  guard st.viewSort i = some u
/-- con-leche: none — the level-list handle of a `const` view (the
universe-argument projection, `default` off a `const` view). -/
def viewConstLevels (st : EStore) (i : EIdx) : LsIdx :=
  match st.view i with
  | some (.const _ us) => us
  | _ => default

/-- con-leche: none — `view_of_viewConstName` with the universe-argument
handle as the named projection `viewConstLevels`: one equation. -/
theorem view_of_viewConstName_eq {st : EStore} {i : EIdx} {n : NIdx}
    (htg : i.tag = ETag.const) (h : st.viewConstName i = some n) :
    st.view i = some (.const n (viewConstLevels st i)) := by
  obtain ⟨us, hv⟩ := view_of_viewConstName htg h
  simp only [viewConstLevels, hv]
grind_pattern [bridge_grind] view_of_viewConstName_eq => st.viewConstName i, some n where
  guard st.viewConstName i = some n
grind_pattern [bridge_grind] view_of_viewApp => st.viewApp i, some (f, a) where
  guard st.viewApp i = some (f, a)
grind_pattern [bridge_grind] view_of_viewBind => st.viewBind i, some (ty, b) where
  guard st.viewBind i = some (ty, b)
grind_pattern [bridge_grind] view_of_viewLet => st.viewLet i, some (ty, val, b) where
  guard st.viewLet i = some (ty, val, b)
grind_pattern [bridge_grind] view_of_viewProj => st.viewProj i, some (n, k, e) where
  guard st.viewProj i = some (n, k, e)

/-- con-leche: none — a handle whose literal read answers views as that literal. -/
theorem view_of_viewLit {st : EStore} {i : EIdx} {l : Literal}
    (htg : i.tag = ETag.lit) (h : st.viewLit i = some l) :
    st.view i = some (.lit l) :=
  EStore.view_of_proj (p := ETables.getLit) (fun t hh => by
    simp only [ETables.getLit, Option.map_eq_some_iff] at hh
    obtain ⟨r, hr, rfl⟩ := hh
    simp [ETables.get, htg, hr, ETag.lit, ETag.sort, ETag.bvar, ETag.fvar, ETag.const,
      ETag.app, ETag.lam, ETag.forallE, ETag.letE]) h
grind_pattern [bridge_grind] view_of_viewLit => st.viewLit i, some l where
  guard st.viewLit i = some l

/-- con-leche: none — the `fvar` index projection read means the type
projection reads too (one row of the `fvar` array);
`viewFVarIdx_isSome_of_viewFVarTy` is the other way. -/
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

/-- con-leche: none — the `fvar` index read under its tag gives the view, its
type the type projection's (`viewFVarTy_of_viewFVarIdx`). -/
theorem view_of_viewFVarIdx {st : EStore} {i : EIdx} {k : Nat}
    (htg : i.tag = ETag.fvar) (h : st.viewFVarIdx i = some k) :
    st.view i = some (.fvar k ((st.viewFVarTy i).getD default)) := by
  obtain ⟨ty, hty⟩ := viewFVarTy_of_viewFVarIdx h
  rw [hty]
  exact view_of_viewFVar htg h hty
grind_pattern [bridge_grind] view_of_viewFVarIdx => st.viewFVarIdx i, some k where
  guard st.viewFVarIdx i = some k

/-- con-leche: none — the `fvar` type projection read means the index
projection reads too (one row of the `fvar` array). -/
theorem viewFVarIdx_isSome_of_viewFVarTy {st : EStore} {i ty : EIdx}
    (h : st.viewFVarTy i = some ty) : (st.viewFVarIdx i).isSome = true := by
  unfold EStore.viewFVarTy at h
  unfold EStore.viewFVarIdx EStore.persGetFVarIdx
  unfold EStore.persGetFVarTy at h
  split at h
  · simp only [ETables.getFVarTy, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, -⟩ := h
    simp [*, ETables.getFVarIdx]
  · split at h
    · simp only [ETables.getFVarTy, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, -⟩ := h
      simp [*, ETables.getFVarIdx]
    · cases h

/-- con-leche: none — the `fvar` TYPE projection read under its tag gives the
view, its index the index projection's (`view_of_viewFVarIdx`'s twin),
guarded at that read. -/
theorem view_of_viewFVarTy {st : EStore} {i ty : EIdx}
    (htg : i.tag = ETag.fvar) (h : st.viewFVarTy i = some ty) :
    st.view i = some (.fvar ((st.viewFVarIdx i).getD 0) ty) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (viewFVarIdx_isSome_of_viewFVarTy h)
  rw [hk]
  exact view_of_viewFVar htg hk h
grind_pattern [bridge_grind] view_of_viewFVarTy => st.viewFVarTy i, some ty where
  guard st.viewFVarTy i = some ty

/-- con-leche: none — arena infrastructure: `EStore.view` reads `pers`, `scr`
and `scratchOn` and nothing else. -/
def viewAt (p s : ETables) (on : Bool) (i : EIdx) : Option ENodeView :=
  if i.isPersistent then p.get i else if on then s.get i else none

/-- con-leche: none — `EStore.view` as a function of the three tables it
reads, so that congruence closure carries a view across a step that frames
them (`substLMemoAt` moves only the LEVEL store).  Passed to `sym` by the walk
that needs it. -/
theorem view_eq_viewAt (st : EStore) (i : EIdx) :
    st.view i = viewAt st.pers st.scr st.scratchOn i := by
  rw [EStore.view_eq_tier]; rfl

/-! A handle that denotes has a view, in every store, keyed by the `isSome`
of the view (the intern specs' preconditions). -/

grind_pattern [bridge_grind] view_isSome => (st.view c).isSome

/-- con-leche: none — a name handle that denotes has a view. -/
theorem nview_isSome {st : NStore} {c : NIdx} (hd : (denoteN st c).isSome = true) :
    (st.view c).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
  exact nview_isSome_of_denote hx
grind_pattern [bridge_grind] nview_isSome => (st.view c).isSome

/-- con-leche: none — a level handle that denotes has a view. -/
theorem lview_isSome {st : LStore} {c : LIdx} (hd : (denoteL st c).isSome = true) :
    (st.view c).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
  exact lview_isSome_of_denote hx
grind_pattern [bridge_grind] lview_isSome => (st.view c).isSome

/-- con-leche: none — a denoting universe-argument list handle has a view
(`viewOK_const`'s premise; the name and level stores have theirs in
`Bridge/Rel.lean`). -/
theorem lsview_isSome_of_denote {st : LsStore} {c : LsIdx} {us : List ConLeche.Level}
    (hd : denoteLs st c = some us) : (st.view c).isSome = true := by
  obtain ⟨w, hw, _⟩ := denoteLs_view hd
  rw [hw]; rfl

/-- con-leche: none — a universe-argument list handle that denotes has a
view. -/
theorem lsview_isSome {st : LsStore} {c : LsIdx} (hd : (denoteLs st c).isSome = true) :
    (st.view c).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
  exact lsview_isSome_of_denote hx
grind_pattern [bridge_grind] lsview_isSome => (st.view c).isSome

/-! ## 7. Interning

What the intern specs ask and answer, as equations: the binder record's two
faces (`eBindView` at a literal tag is the constructor it spells, and
`internLam`/`internForallE` are `internBind` at that tag), the capacity
branch (`capOK` is the program's own condition), a node's denotation from its
view (`denoteEView`, `denoteLView`) and its `ViewOK` side condition. -/

attribute [bridge_grind =] eBindView ETag.isBind

/-- con-leche: none — `eBindView` at the `lam` tag. -/
@[bridge_grind =] theorem eBindView_lam (ty b : EIdx) :
    eBindView ETag.lam ty b = .lam ty b := rfl

/-- con-leche: none — `eBindView` at the `forallE` tag. -/
@[bridge_grind =] theorem eBindView_forallE (ty b : EIdx) :
    eBindView ETag.forallE ty b = .forallE ty b := rfl

/-- con-leche: none — `internLam` is `internBind` at the `lam` tag. -/
@[bridge_grind =] theorem EStore.internLam_eq (st : EStore) (ty b : EIdx) :
    st.internLam ty b = st.internBind ETag.lam ty b := rfl

/-- con-leche: none — `internForallE` is `internBind` at the `forallE` tag. -/
@[bridge_grind =] theorem EStore.internForallE_eq (st : EStore) (ty b : EIdx) :
    st.internForallE ty b = st.internBind ETag.forallE ty b := rfl

/-- con-leche: none — `capOK` is the program's own capacity branch
condition, as an equation (`EStore.intern_spec`'s premise meets the branch). -/
@[bridge_grind =] theorem EStore.capOK_eq (st : EStore) (v : ENodeView) :
    st.capOK v = ((if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap) :=
  rfl

/-- con-leche: none — `capOK` of the name store, as an equation. -/
@[bridge_grind =] theorem NStore.capOK_eq (st : NStore) (v : NNodeView) :
    st.capOK v = ((if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap) :=
  rfl

/-- con-leche: none — `capOK` of the level store, as an equation. -/
@[bridge_grind =] theorem LStore.capOK_eq (st : LStore) (v : LNodeView) :
    st.capOK v = ((if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap) :=
  rfl

/-- con-leche: none — `capOK` of the level-list store, as an equation. -/
@[bridge_grind =] theorem LsStore.capOK_eq (st : LsStore) (v : LsNodeView) :
    st.capOK v = ((if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap) :=
  rfl

attribute [bridge_grind =] denoteEView denoteLView
attribute [bridge_grind ←] viewOK_bvar viewOK_lit viewOK_sort viewOK_app viewOK_lam
  viewOK_forallE viewOK_letE viewOK_proj

/-- con-leche: none — `internLNode .zero`'s precondition. -/
@[bridge_grind .] theorem lviewOK_zero {st : EStore} : st.ls.ViewOK .zero :=
  ⟨fun c hc => by simp [LNodeView.lchildren] at hc,
   fun c hc => by simp [LNodeView.nchildren] at hc⟩

/-- con-leche: none — `internLNode (.succ u)`'s precondition, at a level
handle that has a view. -/
@[bridge_grind ←] theorem lviewOK_succ {st : EStore} {u : LIdx}
    (h : (st.ls.view u).isSome = true) : st.ls.ViewOK (.succ u) :=
  ⟨fun c hc => by simp [LNodeView.lchildren] at hc; subst hc; exact h,
   fun c hc => by simp [LNodeView.nchildren] at hc⟩

/-- con-leche: none — `internLNode (.imax u v)`'s precondition, at level
handles that denote. -/
@[bridge_grind ←] theorem lviewOK_imax {st : EStore} {u v : LIdx}
    (hu : (denoteL st.ls u).isSome = true) (hv : (denoteL st.ls v).isSome = true) :
    st.ls.ViewOK (.imax u v) := by
  obtain ⟨_, hu'⟩ := Option.isSome_iff_exists.mp hu
  obtain ⟨_, hv'⟩ := Option.isSome_iff_exists.mp hv
  constructor
  · intro c hc
    simp only [LNodeView.lchildren, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact lview_isSome_of_denote hu'
    · exact lview_isSome_of_denote hv'
  · intro c hc; simp [LNodeView.nchildren] at hc

/-! ## 8. The environment index as equations -/

/-- con-leche: none — is a stored lookup a definition. -/
def iDefn? : Option IConstantInfo → Bool | some (.defnInfo _ _ _) => true | _ => false
/-- con-leche: none — a stored definition's record (a default elsewhere). -/
def iDefnVal : Option IConstantInfo → IConstantVal | some (.defnInfo v _ _) => v | _ => default
/-- con-leche: none — a stored definition's value handle. -/
def iDefnValue : Option IConstantInfo → EIdx | some (.defnInfo _ e _) => e | _ => default
/-- con-leche: none — a stored definition's hint (`opaque` elsewhere, as
con-leche's `headHint` reads it). -/
def iDefnHint : Option IConstantInfo → ReducibilityHint
  | some (.defnInfo _ _ h) => h | _ => .opaque
/-- con-leche: none — is an environment lookup a definition. -/
def cDefn? : Option ConstantInfo → Bool | some (.defnInfo _ _ _) => true | _ => false
/-- con-leche: none — a definition's record. -/
def cDefnVal : Option ConstantInfo → ConstantVal | some (.defnInfo v _ _) => v | _ => default
/-- con-leche: none — a definition's value. -/
def cDefnValue : Option ConstantInfo → Expr | some (.defnInfo _ e _) => e | _ => .bvar 0
/-- con-leche: none — a definition's hint (`opaque` elsewhere). -/
def cDefnHint : Option ConstantInfo → ReducibilityHint
  | some (.defnInfo _ _ h) => h | _ => .opaque

/-- con-leche: none — `iDefn?` at a definition. -/
@[bridge_grind =] theorem iDefn?_defn (v : IConstantVal) (e : EIdx) (h : ReducibilityHint) :
    iDefn? (some (.defnInfo v e h)) = true := rfl
/-- con-leche: none — `iDefnVal` at a definition. -/
@[bridge_grind =] theorem iDefnVal_defn (v : IConstantVal) (e : EIdx) (h : ReducibilityHint) :
    iDefnVal (some (.defnInfo v e h)) = v := rfl
/-- con-leche: none — `iDefnValue` at a definition. -/
@[bridge_grind =] theorem iDefnValue_defn (v : IConstantVal) (e : EIdx) (h : ReducibilityHint) :
    iDefnValue (some (.defnInfo v e h)) = e := rfl
/-- con-leche: none — a lookup that is a definition IS one: what refutes a
`match`'s fall-through arm. -/
theorem iDefn?_eta {o : Option IConstantInfo} (h : iDefn? o = true) :
    o = some (.defnInfo (iDefnVal o) (iDefnValue o) (iDefnHint o)) := by
  match o, h with
  | some (.defnInfo _ _ _), _ => rfl
grind_pattern [bridge_grind] iDefn?_eta => iDefn? o

/-- con-leche: none — **the one case split**: a lookup is a definition, or
its hint is `opaque`. -/
theorem iDefnHint_cases (o : Option IConstantInfo) :
    iDefnHint o = if iDefn? o = true then iDefnHint o else .opaque := by
  match o with
  | some (.defnInfo _ _ _) => rfl
  | some (.axiomInfo _) | some (.thmInfo _) | some (.indInfo _ _) | some (.ctorInfo _ _ _)
  | some (.recInfo _ _ _ _) | some (.projInfo _) | none => rfl
grind_pattern [bridge_grind] iDefnHint_cases => iDefnHint o

/-! The same projections at the inductives and constructors. -/

/-- con-leche: none — is a stored lookup an inductive. -/
def iInd? : Option IConstantInfo → Bool | some (.indInfo _ _) => true | _ => false
/-- con-leche: none — a stored inductive's record. -/
def iIndVal : Option IConstantInfo → IConstantVal | some (.indInfo v _) => v | _ => default
/-- con-leche: none — a stored inductive's capabilities. -/
def iIndCaps : Option IConstantInfo → IIndCaps | some (.indInfo _ c) => c | _ => default
/-- con-leche: none — is a stored lookup a constructor. -/
def iCtor? : Option IConstantInfo → Bool | some (.ctorInfo _ _ _) => true | _ => false
/-- con-leche: none — a stored constructor's record. -/
def iCtorVal : Option IConstantInfo → IConstantVal | some (.ctorInfo v _ _) => v | _ => default
/-- con-leche: none — a stored constructor's parameter count. -/
def iCtorNP : Option IConstantInfo → Nat | some (.ctorInfo _ n _) => n | _ => 0
/-- con-leche: none — a stored constructor's field count. -/
def iCtorNF : Option IConstantInfo → Nat | some (.ctorInfo _ _ n) => n | _ => 0
/-- con-leche: none — is an environment lookup an inductive. -/
def cInd? : Option ConstantInfo → Bool | some (.indInfo _ _) => true | _ => false
/-- con-leche: none — an inductive's record. -/
def cIndVal : Option ConstantInfo → ConstantVal | some (.indInfo v _) => v | _ => default
/-- con-leche: none — is an environment lookup a constructor. -/
def cCtor? : Option ConstantInfo → Bool | some (.ctorInfo _ _ _) => true | _ => false
/-- con-leche: none — a constructor's record. -/
def cCtorVal : Option ConstantInfo → ConstantVal | some (.ctorInfo v _ _) => v | _ => default
attribute [bridge_grind =] iInd? iIndVal iIndCaps iCtor? iCtorVal iCtorNP iCtorNF

/-- con-leche: none — a lookup that is an inductive IS one. -/
theorem iInd?_eta {o : Option IConstantInfo} (h : iInd? o = true) :
    o = some (.indInfo (iIndVal o) (iIndCaps o)) := by
  match o, h with
  | some (.indInfo _ _), _ => rfl
grind_pattern [bridge_grind] iInd?_eta => iInd? o

/-- con-leche: none — a lookup that is a constructor IS one. -/
theorem iCtor?_eta {o : Option IConstantInfo} (h : iCtor? o = true) :
    o = some (.ctorInfo (iCtorVal o) (iCtorNP o) (iCtorNF o)) := by
  match o, h with
  | some (.ctorInfo _ _ _), _ => rfl
grind_pattern [bridge_grind] iCtor?_eta => iCtor? o

/-! The projections at any stored constant: tower-ness and the record off
the tower (`Core/Walks/PropRead.lean`'s readers). -/

/-- con-leche: none — a stored constant's record off the tower (`default` on
the tower arm, which interns). -/
def iPureVal : IConstantInfo → IConstantVal
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v => v
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ => v
  | .projInfo _ => default
/-- con-leche: none — is a stored lookup a tower entry. -/
def iTower? : Option IConstantInfo → Bool | some ci => ci.isTowerEntry | none => false
/-- con-leche: none — a stored lookup's record. -/
def iValP : Option IConstantInfo → IConstantVal | some ci => iPureVal ci | none => default
/-- con-leche: none — is an environment lookup a tower entry. -/
def cTower? : Option ConstantInfo → Bool | some ci => ci.isTowerEntry | none => false
/-- con-leche: none — an environment lookup's record. -/
def cValP : Option ConstantInfo → ConstantVal | some ci => ci.toConstantVal | none => default
attribute [bridge_grind =] iTower? iValP

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — a stored lookup against
the environment's, through every projection the walks read: the two
lookups agree on being present, a definition, a constructor and a tower
entry, on a definition's hint, and the stored records denote the
environment's (a definition's record and value, a constructor's record, any
record off the tower). -/
def IndexCI (st : EStore) (oi : Option IConstantInfo) (oc : Option ConstantInfo) : Prop :=
  cDefn? oc = iDefn? oi ∧ cDefnHint oc = iDefnHint oi ∧
  (iDefn? oi = true →
    Frontend.denoteCV st (iDefnVal oi) = some (cDefnVal oc) ∧
    denoteE st (iDefnValue oi) = some (cDefnValue oc)) ∧
  cCtor? oc = iCtor? oi ∧
  (iCtor? oi = true → Frontend.denoteCV st (iCtorVal oi) = some (cCtorVal oc)) ∧
  oi.isSome = oc.isSome ∧ iTower? oi = cTower? oc ∧
  (oi.isSome = true → iTower? oi = false →
    Frontend.denoteCV st (iValP oi) = some (cValP oc))

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the index at a name
handle `c` denoting `nm`**: `IndexCI` between the two lookups. -/
def IndexAt (env : Env) (fe : IFEnv) (st : EStore) (c : NIdx) : Option ConLeche.Name → Prop
  | some nm => IndexCI st (fe.find? c) (env.find? nm)
  | none => True

/-- con-leche: none — a stored constant and its denotation agree on every
projection `IndexAt` names. -/
theorem indexAt_hit {st : EStore} {ci : IConstantInfo} {cc : ConstantInfo}
    (h : Frontend.denoteCI st ci = some cc) :
    IndexCI st (some ci) (some cc) := by
  cases ci with
  | defnInfo v e hh =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv x hcv hx; cases h
      exact ⟨rfl, rfl, fun _ => ⟨hcv, hx⟩, rfl, nofun, rfl, rfl, fun _ _ => hcv⟩
    · cases h
  | indInfo v caps =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv x hcv _; cases h
      exact ⟨rfl, rfl, nofun, rfl, nofun, rfl, rfl, fun _ _ => hcv⟩
    · cases h
  | recInfo v mI rP rs =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv x hcv _; cases h
      exact ⟨rfl, rfl, nofun, rfl, nofun, rfl, rfl, fun _ _ => hcv⟩
    · cases h
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact ⟨rfl, rfl, nofun, rfl, nofun, rfl, rfl, fun _ _ => hcv⟩
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact ⟨rfl, rfl, nofun, rfl, nofun, rfl, rfl, fun _ _ => hcv⟩
  | ctorInfo v nP nF =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact ⟨rfl, rfl, nofun, rfl, fun _ => hcv, rfl, rfl, fun _ _ => hcv⟩
  | projInfo t =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨t', _, rfl⟩ := h
    exact ⟨rfl, rfl, nofun, rfl, nofun, rfl, rfl, fun _ h => nomatch h⟩

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — `IFEnvOK`'s two halves at
every lookup the program makes, keyed by the invariant and the lookup. -/
theorem indexAt {mode : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    (hok : CheckOK mode env fe s) (c : NIdx) :
    IndexAt env fe s.store c (denoteN s.store.ns c) := by
  cases hn : denoteN s.store.ns c with
  | none => trivial
  | some nm =>
  cases hf : fe.find? c with
  | none =>
    show IndexCI s.store (fe.find? c) (env.find? nm)
    simp only [hf, IFEnvOK.miss hok.state hok.ienv hn hf]
    exact ⟨rfl, rfl, nofun, rfl, nofun, rfl, rfl, nofun⟩
  | some ci =>
    obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c ci hf
    obtain rfl := Option.some.inj (hn'.symm.trans hn)
    show IndexCI s.store (fe.find? c) (env.find? nm')
    rw [hf, hfind]
    exact indexAt_hit hci
grind_pattern [bridge_grind] indexAt => CheckOK mode env fe s, fe.find? c

/-- con-leche: none — `IndexAt` at a denoting handle. -/
theorem IndexAt.some {env : Env} {fe : IFEnv} {st : EStore} {c : NIdx} {nm : ConLeche.Name}
    (H : IndexAt env fe st c (some nm)) :
    cDefn? (env.find? nm) = iDefn? (fe.find? c) ∧
      cDefnHint (env.find? nm) = iDefnHint (fe.find? c) ∧
      (iDefn? (fe.find? c) = true →
        Frontend.denoteCV st (iDefnVal (fe.find? c)) = some (cDefnVal (env.find? nm)) ∧
        denoteE st (iDefnValue (fe.find? c)) = some (cDefnValue (env.find? nm))) ∧
      cCtor? (env.find? nm) = iCtor? (fe.find? c) ∧
      (iCtor? (fe.find? c) = true →
        Frontend.denoteCV st (iCtorVal (fe.find? c)) = some (cCtorVal (env.find? nm))) ∧
      (fe.find? c).isSome = (env.find? nm).isSome ∧
      iTower? (fe.find? c) = cTower? (env.find? nm) ∧
      ((fe.find? c).isSome = true → iTower? (fe.find? c) = false →
        Frontend.denoteCV st (iValP (fe.find? c)) = some (cValP (env.find? nm))) := H
grind_pattern [bridge_grind] IndexAt.some => IndexAt env fe st c (some nm)

end ConRon.Bridge
