/-
# `ConRon.Bridge.Frame` — the frame closer `bridge_frame` and the shape-addressed `vc_arm`

Task #120.  Theorem 1's simulation proofs run `vcgen` over an arena walk and
then had to discharge, by hand and BY POSITION, two kinds of residue:

* the **frame**: a callee's precondition (`CheckOK s`, `StateOK s`,
  `StoreWF s.store`, a handle that denotes at the CURRENT store, an
  `∃ v, denoteE … = some v ∧ WScoped d v`) and a postcondition's frame
  conjuncts (`Ext s₀.store s₃.store`, `s₃.pins = s₀.pins`, `CheckOK s₃`),
  each of which is a CHAIN through the calls' postconditions —
  `denote_ext hden (hx01.trans hx12)`, `hck2.mono hst hx23 hc32 hp32`,
  `by rw [hp32, hp21, hp10]`;
* the **arms**: the mathematics of one branch of the walk.

Both were written as `case vc15 => rename_i s0 s1 _ s2 … hx12 hp21 …`, and
both broke on every sync: one extra call shifts every verification-condition
number and every `rename_i` position, although nothing mathematical moved.

`bridge_frame` closes the first kind outright, by SEARCH rather than by
position: it collects the context's `Ext`/`=`/`CacheFrame` edges and finds the
chain itself.  It is deterministic meta code — no `grind`, no `simp` — so it
costs milliseconds per goal (task #97s: *the cost is `grind`*).  On a goal it
cannot close it splits the top-level conjunction and closes the frame
conjuncts it can, leaving the arm's mathematical conjunct(s) alone.

`vc_arm (h₁ : T₁) … => tac` addresses what remains BY SHAPE: it runs `tac` on
every open goal whose context has hypotheses of the given types (matched up to
`_` holes, the most recent first), naming them `h₁ …`.  A goal it does not
match is left for the next `vc_arm`; a `vc_arm` that matches nothing is an
error, so a stale arm is reported rather than silently skipped.

`bridge_fwd` is the forward half: it instantiates every answer relation
(`RelE`, `RelEL`, `RelEO`, `RelV`, and a bare `∀ e, denoteE st c = some e → …`)
at every denotation of its subject the context has — transported along the
`Ext` chain — and adds the result as a hypothesis, so an arm reads its callees'
answers off the context instead of `obtain`ing them by position.
-/
import ConRon.Bridge.StateOK
import ConRon.BridgeTactic

namespace ConRon.Bridge

open ConRon.Arena

/-! ## 1. The lemmas the search composes -/

/-- con-leche: none — an equality of stores is an extension. -/
theorem Ext.of_eq {a b : EStore} (h : a = b) : Ext a b := h ▸ Ext.refl a

/-- con-leche: none — `StateOK` reads only the store. -/
theorem StateOK.of_store {s s' : AState} (h : StateOK s) (he : s'.store = s.store) :
    StateOK s' := ⟨he ▸ h.wf⟩

/-- con-leche: none — a well-formed store is a `StateOK` state. -/
theorem StateOK.of_wf {s : AState} {st : EStore} (h : StoreWF st) (he : s.store = st) :
    StateOK s := ⟨he ▸ h⟩

/-- con-leche: none — `denoteEList` through an extension, hypothesis first. -/
theorem denoteEList_ext_fr {st st' : EStore} {rs : List EIdx} {xs : List ConLeche.Expr}
    (h : Frontend.denoteEList st rs = some xs) (hx : Ext st st') :
    Frontend.denoteEList st' rs = some xs :=
  denoteEList_ext hx _ _ h

/-- con-leche: none — `denoteNList` through an extension, hypothesis first. -/
theorem denoteNList_ext_fr {st st' : EStore} {hs : List NIdx}
    {xs : List ConLeche.Name}
    (h : Frontend.denoteNList st.ns hs = some xs) (hx : Ext st st') :
    Frontend.denoteNList st'.ns hs = some xs :=
  denoteNList_ext hx.lss.ls.ns _ _ h

/-- con-leche: none — an optional handle's denotation through an extension. -/
theorem denoteEO_ext {st st' : EStore} {r : Option EIdx} {v : Option ConLeche.Expr}
    (h : denoteEO st r = some v) (hx : Ext st st') : denoteEO st' r = some v := by
  cases r with
  | none => exact h
  | some j =>
    simp only [denoteEO, Option.map_eq_some_iff] at h ⊢
    obtain ⟨y, hy, rfl⟩ := h
    exact ⟨y, denote_ext hy hx, rfl⟩

/-- con-leche: none — a denoting handle's `isSome`. -/
theorem isSome_of_eq_some {α : Type} {o : Option α} {a : α} (h : o = some a) :
    o.isSome = true := by rw [h]; rfl

/-- con-leche: none — the denotation fact that discharges an
`∃ v, denote… = some v ∧ P v` precondition. -/
theorem exists_some_and {α : Type} {o : Option α} {a : α} {P : α → Prop}
    (h : o = some a) (hp : P a) : ∃ v, o = some v ∧ P v := ⟨a, h, hp⟩

/-- con-leche: none — a function's answer is unique. -/
theorem eq_of_eq_some {α : Type} {o : Option α} {a b : α} (h₁ : o = some a)
    (h₂ : o = some b) : a = b := Option.some.inj (h₁.symm.trans h₂)

-- `ConRon.BridgeTactic` names the constants above (and the bridge's own)
-- with single backticks, unchecked: this checks them.
run_cmd do
  for n in ConRon.Bridge.Frame.usedConstants do
    unless (← Lean.getEnv).contains n do
      throwError "ConRon.BridgeTactic names {n}, which does not exist"

end ConRon.Bridge
