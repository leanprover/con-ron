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
   * all of it is one fact per handle, `DenoteView st h (st.view h)
     (denoteE st h)`, whose pattern is the denotation term alone; per-
     constructor extraction lemmas fire on `DenoteView st h (some (.K …))
     (some e)` once congruence closure knows the view's constructor and that
     the handle denotes — the precise trigger the `→` form of a view
     hypothesis (`st.view h = some (.app f a)`) cannot give, since its
     inferred multi-pattern `st.view h, .app f a` relates nothing;
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
     `Core/Walks/Spine.lean`), so `grind` never splits its `match`.
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

/-- con-leche: none — **what a handle's view says about its denotation**: at
a denoting handle `h` (view `ov`, denotation `oe`), the denotation's tag is
the handle's, and each child of the view denotes the matching projection.
`denote_view` states it of every denoted handle; the extraction lemmas below
fire once the view's constructor is known. -/
def DenoteView (st : EStore) (h : EIdx) : Option ENodeView → Option Expr → Prop
  | _, none => True
  | none, some _ => False
  | some v, some e => exprTag e = h.tag ∧ match v with
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

/-- con-leche: none — **every denoted handle's view fact**, keyed by its
denotation term alone. -/
theorem denote_view {st : EStore} (hwf : StoreWF st) (h : EIdx) :
    DenoteView st h (st.view h) (denoteE st h) := by
  cases he : denoteE st h with
  | none => cases st.view h <;> trivial
  | some e =>
  obtain ⟨v, hv⟩ := denoteE_view he
  rw [hv]
  refine ⟨(tag_of_denote hwf he).symm, ?_⟩
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
grind_pattern [bridge_grind] denote_view => denoteE st h

/-- con-leche: none — a denotation's tag is its handle's. -/
theorem DenoteView.tag {st : EStore} {h : EIdx} {ov : Option ENodeView} {e : Expr}
    (H : DenoteView st h ov (some e)) : exprTag e = h.tag := by
  cases ov with
  | none => exact H.elim
  | some v => exact H.1
grind_pattern [bridge_grind] DenoteView.tag => DenoteView st h ov (some e)

/-- con-leche: none — an `app` view's children denote the application's
function and argument. -/
theorem DenoteView.app {st : EStore} {h f a : EIdx} {e : Expr}
    (H : DenoteView st h (some (.app f a)) (some e)) :
    denoteE st f = some (exprFn e) ∧ denoteE st a = some (exprArg e) := H.2
grind_pattern [bridge_grind] DenoteView.app => DenoteView st h (some (.app f a)) (some e)

/-- con-leche: none — a `const` view's name handle denotes the constant's name
(and is that name's handle), its level list the constant's levels. -/
theorem DenoteView.const {st : EStore} {h : EIdx} {c : NIdx} {us : LsIdx} {e : Expr}
    (H : DenoteView st h (some (.const c us)) (some e)) :
    denoteN st.ns c = some (exprConstName e) ∧ idxOfName st.ns (exprConstName e) = c ∧
      denoteLs st.lss us = some (exprConstLevels e) := H.2
grind_pattern [bridge_grind] DenoteView.const => DenoteView st h (some (.const c us)) (some e)

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
def viewFn : ENodeView → EIdx | .app f _ => f | _ => default
/-- con-leche: none — the argument handle of an `app` view. -/
def viewArg : ENodeView → EIdx | .app _ a => a | _ => default
/-- con-leche: none — the name handle of a `const` view. -/
def viewConstName : ENodeView → NIdx | .const n _ => n | _ => default
/-- con-leche: none — the level-list handle of a `const` view. -/
def viewConstLevels : ENodeView → LsIdx | .const _ us => us | _ => default

/-- con-leche: none — a view tagged `app` IS an `app` view: what refutes a
`match`'s fall-through arm after the walk tested the tag. -/
theorem ENodeView.tagOf_app {v : ENodeView} (h : v.tagOf = ETag.app) :
    v = .app (viewFn v) (viewArg v) := by
  cases v <;> first | rfl | (simp only [ENodeView.tagOf] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] ENodeView.tagOf_app => ENodeView.tagOf v

/-- con-leche: none — a view tagged `const` IS a `const` view. -/
theorem ENodeView.tagOf_const {v : ENodeView} (h : v.tagOf = ETag.const) :
    v = .const (viewConstName v) (viewConstLevels v) := by
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

attribute [bridge_grind =] Option.isSome_some

end ConRon.Bridge
