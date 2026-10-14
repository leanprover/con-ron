/-
# `ConRon.Bridge.Grind` — the vocabulary `grind` closes Theorem 1's verification conditions with

Task #122.  A Theorem 1 walk proof is

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
`@[bridge_grind]`:

1. **The store order.**  `Ext` is the preorder `≤` on `EStore`
   (`Std.IsPreorder`), so `grind`'s order solver decides the chains
   `s₀.store ≤ s₁.store ≤ … ≤ sₙ.store` a sequence of calls leaves.  The
   statements keep `Ext`; `ext_eq_le` turns each `Ext` atom into its `≤`.
2. **Transport as an equation.**  `denote_le`: past `st ≤ st'` a handle that
   denotes denotes the same — an equation between the two `denoteE` terms,
   with the multi-pattern `st ≤ st', denoteE st h`, so that congruence
   closure carries every denotation along the chain.
3. **Answers about an optional subject as atoms.**  A spec that does not
   know its subject's denotation states `Ans P (denoteE st i)` — whatever `i`
   denotes satisfies `P`.  `Ans` is never unfolded: its equation
   `Ans P (some e) = P e` fires when congruence closure learns that the
   denotation is a `some`, and e-matching binds `e` from the subject's
   equivalence class.  (The `∀ e, denoteE st i = some e → P e`
   spelling it replaces is the same proposition, but as a hypothesis its
   only pattern is `some e`, which matches every `some` in the context.)
4. **The state invariant's projections** (`CheckOK → StateOK → StoreWF`).
5. **Views and tags as equations** (task #123, the dispatch walks).  A
   dispatch walk tests a handle's TAG, matches its VIEW, and compares against
   a con-leche function that matches the DENOTATION's constructor.  `grind`
   must see all three without a case split, so each fact is an equation
   between terms built from the subject, never a disjunction or an `∃`:
   * the denotation's constructor is its tag, `exprTag e = h.tag`, and its
     fields are PROJECTIONS (`exprFn e`, `exprConstName e`, …), so a view
     `.app f a` says `denoteE st f = some (exprFn e)` — no fresh variable;
   * all of it is one fact per viewed handle, `DenoteView st (st.view h)
     (denoteE st h)` (and `DenoteTag h (denoteE st h)` per tag-tested one),
     keyed by the handle's own terms; per-constructor extraction lemmas fire
     on `DenoteView st (some (.K …)) (some e)` once congruence closure knows
     the view's constructor and that the handle denotes — the precise trigger
     the `→` form of a view hypothesis (`st.view h = some (.app f a)`) cannot
     give, since its inferred multi-pattern `st.view h, .app f a` relates
     nothing;
   * the predicate arguments are named functions, never `fun`s: `grind`'s
     `funext` splits on equalities between the lambdas of an `Ans`;
   * a name store index is the inverse of `denoteN` (`idxOfName`), so "the
     handles are equal iff the names are" is congruence closure in both
     directions;
   * a view's constructor follows from its tag through the view projections
     (`ENodeView.tagOf_app`, …), which is what refutes a match's
     fall-through arm after a tag test;
   * a con-leche function the walk compares against is restated ONCE as an
     unconditional equation over tags and projections (`sameConstHeads_eq`,
     `Core/Walks/Spine.lean`), so `grind` never splits its `match`;
   * every answer relation about optional subjects (`RelE`, `RelEL`, the
     lengths, a constant record's fields) is a named predicate on the
     DENOTATION TERMS with an extraction lemma at `some`, the `Ans` idea
     without its `fun`.
6. **The environment index as equations.**  A lookup `fe.find? c` and the
   environment's `env.find? nm` at the name `c` denotes agree on every
   projection the walks read (`FindAt`): is it a definition, its hint, its
   record and value.  A lookup that is a definition IS one (`iDefn?_eta`),
   which refutes a match's fall-through arm; the one case split left is on
   "definition or not" where a walk needs the hint of a lookup it did not
   match (`iDefnHint_cases`).
-/
import ConRon.Bridge.StateOK
import ConRon.Bridge.Frame
import ConRon.Bridge.GrindAttr

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## 1. The store order -/

/-- con-leche: none — `Ext` is the store order (task #122): `st ≤ st'` is
"`st'` extends `st`". -/
instance : LE EStore := ⟨Ext⟩

/-- con-leche: none — the store order is a preorder (`Ext.refl`/`Ext.trans`),
which is what `grind`'s order solver needs. -/
instance : Std.IsPreorder EStore where
  le_refl := Ext.refl
  le_trans := fun _ _ _ => Ext.trans

/-- con-leche: none — an `Ext` atom is its `≤` (definitionally). -/
@[bridge_grind =] theorem ext_eq_le (a b : EStore) : Ext a b = (a ≤ b) := rfl

/-! ## 2. Transport -/

/-- con-leche: none — `denote_ext` as an equation: past an extension, a
handle that denotes denotes the same. -/
theorem denote_le {st st' : EStore} {h : EIdx} (hx : st ≤ st')
    (hd : denoteE st h ≠ none) : denoteE st' h = denoteE st h := by
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hd
  rw [he]; exact hx.expr h e he
grind_pattern [bridge_grind] denote_le => st ≤ st', denoteE st h

/-! ## 3. Answers about an optional subject -/

/-- con-leche: none — **whatever `o` denotes satisfies `P`**: the answer
shape of a spec whose subject's denotation is not a parameter (task #122;
the spelling `∀ e, o = some e → P e` unfolded).  `o` is a `denoteE st i`
(or a `st.view i`, for the facts a view carries). -/
def Ans {α : Type} (P : α → Prop) (o : Option α) : Prop := ∀ e, o = some e → P e

/-- con-leche: none — `Ans` at a denoting subject. -/
@[bridge_grind =] theorem Ans.some_eq {α : Type} (P : α → Prop) (e : α) :
    Ans P (some e) = P e :=
  propext ⟨fun h => h e rfl, fun h _ he => Option.some.inj he ▸ h⟩

/-! ## 4. The state invariant's projections, and small facts -/

attribute [bridge_grind →] CheckOK.state StateOK.wf

/-- con-leche: none — a successful run is `isOk` (the fuel-merge lemmas take
a callee's run as `isOk`, which names no answer). -/
@[bridge_grind =] theorem except_isOk_ok {ε α : Type} (a : α) :
    (Except.ok a : Except ε α).isOk = true := rfl

/-- con-leche: none — an optional handle that is `some` denotes a `some`. -/
@[bridge_grind →] theorem denoteEO_some_some {st : EStore} {r : EIdx} {v : Option Expr}
    (h : denoteEO st (some r) = some v) : ∃ x, v = some x ∧ denoteE st r = some x := by
  simp only [denoteEO, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, rfl, hx⟩

/-- con-leche: none — the absent handle denotes `none`. -/
@[bridge_grind =] theorem denoteEO_none_eq (st : EStore) : denoteEO st none = some none := rfl

/-! ## 5. Views and tags as equations (task #123) -/

/-! `exprTag`, the tag of an expression's constructor, and `tag_of_denote`
(a handle's tag is its denotation's) are `Bridge/Frame.lean`'s (task #120). -/

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

/-- con-leche: none — an `app` view's children denote the application's
function and argument. -/
theorem DenoteView.app {st : EStore} {f a : EIdx} {e : Expr}
    (H : DenoteView st (some (.app f a)) (some e)) :
    denoteE st f = some (exprFn e) ∧ denoteE st a = some (exprArg e) := H
grind_pattern [bridge_grind] DenoteView.app => DenoteView st (some (.app f a)) (some e)

/-- con-leche: none — a `const` view's name handle denotes the constant's name
(and is that name's handle), its level list the constant's levels. -/
theorem DenoteView.const {st : EStore} {c : NIdx} {us : LsIdx} {e : Expr}
    (H : DenoteView st (some (.const c us)) (some e)) :
    denoteN st.ns c = some (exprConstName e) ∧ idxOfName st.ns (exprConstName e) = c ∧
      denoteLs st.lss us = some (exprConstLevels e) := H
grind_pattern [bridge_grind] DenoteView.const => DenoteView st (some (.const c us)) (some e)

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
`match`'s fall-through arm after the walk tested the tag. -/
theorem ENodeView.tagOf_app {v : ENodeView} (h : v.tagOf = ETag.app) :
    v = .app (nodeFn v) (nodeArg v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_app => ENodeView.tagOf v

/-- con-leche: none — a view tagged `const` IS a `const` view. -/
theorem ENodeView.tagOf_const {v : ENodeView} (h : v.tagOf = ETag.const) :
    v = .const (nodeConstName v) (nodeConstLevels v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_const => ENodeView.tagOf v

/-- con-leche: none — `RelE`'s answer at an optional subject: whatever `c`
denotes, `r` denotes its image under `g` (the named-predicate form of
`Ans (fun e => …)`, so that no `fun` reaches `grind`). -/
def MapRel (g : Expr → Expr) : Option Expr → Option Expr → Prop
  | some e, o => o = some (g e)
  | none, _ => True

/-- con-leche: none — a `RelE` answer is a `MapRel` fact on the two
denotation terms. -/
theorem RelE.mapRel {g : Expr → Expr} {st st' : EStore} {c r : EIdx}
    (h : RelE g st c st' r) : MapRel g (denoteE st c) (denoteE st' r) := by
  cases hc : denoteE st c with
  | none => trivial
  | some e => exact h e hc
grind_pattern [bridge_grind] RelE.mapRel => RelE g st c st' r

/-- con-leche: none — `MapRel` at a denoting subject. -/
theorem MapRel.some {g : Expr → Expr} {e : Expr} {o : Option Expr}
    (H : MapRel g (some e) o) : o = some (g e) := H
grind_pattern [bridge_grind] MapRel.some => MapRel g (some e) o

attribute [bridge_grind =] Option.isSome_some Option.map_some

/-- con-leche: none — `denoteEO` at a handle is its denotation, optionally. -/
@[bridge_grind =] theorem denoteEO_some_eq (st : EStore) (r : EIdx) :
    denoteEO st (some r) = (denoteE st r).map some := rfl

/-- con-leche: none — `RelEL`'s answer at an optional subject (`MapRel` at a
list answer). -/
def MapRelL (g : Expr → List Expr) : Option Expr → Option (List Expr) → Prop
  | some e, o => o = some (g e)
  | none, _ => True

/-- con-leche: none — a `RelEL` answer is a `MapRelL` fact. -/
theorem RelEL.mapRel {g : Expr → List Expr} {st st' : EStore} {c : EIdx} {rs : List EIdx}
    (h : RelEL g st c st' rs) : MapRelL g (denoteE st c) (Frontend.denoteEList st' rs) := by
  cases hc : denoteE st c with
  | none => trivial
  | some e => exact h e hc
grind_pattern [bridge_grind] RelEL.mapRel => RelEL g st c st' rs

/-- con-leche: none — `MapRelL` at a denoting subject. -/
theorem MapRelL.some {g : Expr → List Expr} {e : Expr} {o : Option (List Expr)}
    (H : MapRelL g (some e) o) : o = some (g e) := H
grind_pattern [bridge_grind] MapRelL.some => MapRelL g (some e) o

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

/-! ## 6. The environment index as equations (task #123) -/

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

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the index at a name
handle `c` denoting `nm`**, through the projections the walks read. -/
def FindAt (env : Env) (fe : IFEnv) (st : EStore) (c : NIdx) : Option ConLeche.Name → Prop
  | some nm => cDefn? (env.find? nm) = iDefn? (fe.find? c) ∧
      cDefnHint (env.find? nm) = iDefnHint (fe.find? c) ∧
      (iDefn? (fe.find? c) = true →
        Frontend.denoteCV st (iDefnVal (fe.find? c)) = some (cDefnVal (env.find? nm)) ∧
        denoteE st (iDefnValue (fe.find? c)) = some (cDefnValue (env.find? nm)))
  | none => True

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — `IFEnvOK`'s two halves at
every lookup the program makes, keyed by the invariant and the lookup. -/
theorem findAt {mode : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    (hok : CheckOK mode env fe s) (c : NIdx) : FindAt env fe s.store c (denoteN s.store.ns c) := by
  cases hn : denoteN s.store.ns c with
  | none => trivial
  | some nm =>
  cases hf : fe.find? c with
  | none =>
    show FindAt env fe s.store c (some nm)
    simp only [FindAt, hf, IFEnvOK.miss hok.state hok.ienv hn hf]
    exact ⟨rfl, rfl, fun h => nomatch h⟩
  | some ci =>
    obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c ci hf
    obtain rfl := Option.some.inj (hn'.symm.trans hn)
    simp only [FindAt, hf, hfind]
    cases ci with
    | defnInfo v e h =>
      simp only [Frontend.denoteCI] at hci
      cases hv : Frontend.denoteCV s.store v with
      | none => rw [hv] at hci; simp at hci
      | some cv =>
        cases he : denoteE s.store e with
        | none => rw [hv, he] at hci; simp at hci
        | some x =>
          rw [hv, he] at hci
          obtain rfl := (Option.some.inj hci).symm
          exact ⟨rfl, rfl, fun _ => ⟨hv, he⟩⟩
    | _ =>
      cases cc with
      | defnInfo cv x h =>
        simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
        first
          | (obtain ⟨_, _, hc⟩ := hci; cases hc)
          | (split at hci <;> simp at hci)
      | _ => exact ⟨rfl, rfl, fun h => nomatch h⟩
grind_pattern [bridge_grind] findAt => CheckOK mode env fe s, fe.find? c

/-- con-leche: none — `FindAt` at a denoting handle. -/
theorem FindAt.some {env : Env} {fe : IFEnv} {st : EStore} {c : NIdx} {nm : ConLeche.Name}
    (H : FindAt env fe st c (some nm)) :
    cDefn? (env.find? nm) = iDefn? (fe.find? c) ∧
      cDefnHint (env.find? nm) = iDefnHint (fe.find? c) ∧
      (iDefn? (fe.find? c) = true →
        Frontend.denoteCV st (iDefnVal (fe.find? c)) = some (cDefnVal (env.find? nm)) ∧
        denoteE st (iDefnValue (fe.find? c)) = some (cDefnValue (env.find? nm))) := H
grind_pattern [bridge_grind] FindAt.some => FindAt env fe st c (some nm)

end ConRon.Bridge
