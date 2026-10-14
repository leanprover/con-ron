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
   denotes satisfies `P`.  `Ans` is never unfolded: its two equations
   (`Ans P (some e) = P e`, `Ans P none = True`) fire when congruence closure
   learns which constructor the denotation is, and e-matching binds `e` from
   the subject's equivalence class.  (The `∀ e, denoteE st i = some e → P e`
   spelling it replaces is the same proposition, but as a hypothesis its
   only pattern is `some e`, which matches every `some` in the context.)
4. **The state invariant's projections** (`CheckOK → StateOK → StoreWF`).
-/
import ConRon.Bridge.StateOK
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

/-- con-leche: none — `Ans` at a subject that does not denote. -/
@[bridge_grind =] theorem Ans.none_eq {α : Type} (P : α → Prop) : Ans P none = True :=
  propext ⟨fun _ => trivial, fun _ _ he => nomatch he⟩

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

end ConRon.Bridge
