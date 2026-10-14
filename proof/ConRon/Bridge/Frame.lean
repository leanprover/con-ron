/-
# `ConRon.Bridge.Frame` — the lemmas Theorem 1's closers compose

`ConRon/BridgeTactic.lean` holds the closers (`bridge_frame`, `bridge_auto`,
`vc_arm`; tasks #120, #121) and the three registries; this module, the first
of the `Bridge` tier to import that library, holds the general lemmas they
build proofs from and registers them:

* `@[bridge_transport]` — a fact carried along `Ext` (`denote_ext` and its
  siblings);
* `@[bridge_frame]` — the frame rules: `StateOK` past a store equation,
  `CheckOK.mono`, a denoting handle's `isSome`, an intern's `ViewOK`;
* `@[bridge_fwd]` — the forward rules: the view inversions, the tag tests
  read as tags of the denotation, the optional handle.

A walk's own lemmas go in its `bridge_auto [...]` list, or are tagged where
they are declared when every walk wants them.  The census line at the end
checks that the constants the tactic names with single backticks exist.
-/
import ConRon.Bridge.Grind
import ConRon.BridgeTactic

namespace ConRon.Bridge

open ConRon.Arena ConLeche

set_option autoImplicit false

/-! ## 1. The lemmas the search composes -/

/-- con-leche: none — `StateOK` reads only the store. -/
theorem StateOK.of_store {s s' : AState} (h : StateOK s) (he : s'.store = s.store) :
    StateOK s' := ⟨he ▸ h.wf⟩

/-- con-leche: none — a well-formed store is a `StateOK` state. -/
theorem StateOK.of_wf {s : AState} {st : EStore} (h : StoreWF st) (he : s.store = st) :
    StateOK s := ⟨he ▸ h⟩

/-! The rules the closers compose, registered (`ConRon/BridgeTactic.lean` §1);
the bridge's older modules do not import the tactic library, so their
lemmas are registered here.  The frame: the state invariants past a chain of
calls, a denoting handle's `isSome`, an intern's `ViewOK`. -/

attribute [bridge_frame] StateOK.of_store StateOK.of_wf CheckOK.mono
  isSome_of_eq_some

attribute [bridge_transport] denote_ext denoteN_ext denoteL_ext denoteLs_ext

attribute [bridge_frame] viewOK_bvar viewOK_lit viewOK_fvar viewOK_sort viewOK_const
  viewOK_app viewOK_lam viewOK_forallE viewOK_letE viewOK_proj view_isSome
  nview_isSome_of_denote lview_isSome_of_denote

attribute [bridge_fwd] denote_fvar_inv denote_sort_inv denote_const_inv denote_app_inv
  denote_lam_inv denote_forallE_inv denote_letE_inv denote_proj_inv

/-- con-leche: none — `denoteEList` through an extension, hypothesis first. -/
@[bridge_transport] theorem denoteEList_ext_fr {st st' : EStore} {rs : List EIdx} {xs : List ConLeche.Expr}
    (h : Frontend.denoteEList st rs = some xs) (hx : Ext st st') :
    Frontend.denoteEList st' rs = some xs :=
  denoteEList_ext hx _ _ h

/-- con-leche: none — `denoteNList` through an extension, hypothesis first. -/
@[bridge_transport] theorem denoteNList_ext_fr {st st' : EStore} {hs : List NIdx}
    {xs : List ConLeche.Name}
    (h : Frontend.denoteNList st.ns hs = some xs) (hx : Ext st st') :
    Frontend.denoteNList st'.ns hs = some xs :=
  denoteNList_ext hx.lss.ls.ns _ _ h

/-- con-leche: none — an optional handle's denotation through an extension. -/
@[bridge_transport] theorem denoteEO_ext {st st' : EStore} {r : Option EIdx} {v : Option ConLeche.Expr}
    (h : denoteEO st r = some v) (hx : Ext st st') : denoteEO st' r = some v := by
  cases r with
  | none => exact h
  | some j =>
    simp only [denoteEO, Option.map_eq_some_iff] at h ⊢
    obtain ⟨y, hy, rfl⟩ := h
    exact ⟨y, denote_ext hy hx, rfl⟩

/-- con-leche: none — a handle that denotes still denotes past an extension
(its `isSome`, as the walks' preconditions state it). -/
@[bridge_frame] theorem isSome_denote_ext {st st' : EStore} {h : EIdx}
    (hs : (denoteE st h).isSome = true) (hx : Ext st st') :
    (denoteE st' h).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [denote_ext he hx]; rfl

/-- con-leche: none — a memo HIT
answers by the invariant, in the shape a walk's hit arm has (`some r =
tbl'[(h, c)]?`, the key spelled out, the table and the stores up to the
frame's equations, and the answer's function `g` only equal to the table's
`f c` — `f c` is no pattern, so `bridge_frame [MemoOK.get_hit']` would not
unify with it): task #120's memo-hit lemma. -/
theorem MemoOK.get_hit' {f : Nat → ConLeche.Expr → ConLeche.Expr}
    {g : ConLeche.Expr → ConLeche.Expr}
    {tbl tbl' : Std.HashMap (EIdx × Nat) EIdx} {st st₁ st₂ : EStore} {h : EIdx}
    {c : Nat} {r : EIdx} (hm : MemoOK f tbl st) (hk : some r = tbl'[(h, c)]?)
    (ht : tbl' = tbl) (h₁ : st₁ = st) (h₂ : st₂ = st) (hg : g = f c) :
    RelE g st₁ h st₂ r := by
  subst ht h₁ h₂ hg
  exact MemoOK.get (k := (h, c)) hm hk.symm

/-! ## 2. The tag tests and the optional handle (task #120)

The tag-first twins test `h.tag == ETag.k` before they project; `exprTag`
turns such a test into a fact about the denotation, in the `Bool` shape
`contradiction` decides once the denotation is split by constructor — which
is `bridge_finish`'s case split.  (`exprTag` and `tag_of_denote` themselves
are `Bridge/Grind.lean`'s, §6, since task #123.) -/

/-- con-leche: none — a TRUE tag test is a tag of the denotation
(`bridge_fwd`'s default). -/
@[bridge_fwd] theorem exprTag_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    {t : UInt32} (hd : denoteE st h = some e) (ht : (h.tag == t) = true) :
    (exprTag e == t) = true := by
  rw [← tag_of_denote hwf hd]; exact ht

/-- con-leche: none — a FALSE tag test, likewise. -/
@[bridge_fwd] theorem exprTag_of_not_tag {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    {t : UInt32} (hd : denoteE st h = some e) (ht : ¬ (h.tag == t) = true) :
    ¬ (exprTag e == t) = true := by
  rw [← tag_of_denote hwf hd]; exact ht

/-- con-leche: none — the view projections' answers in the orientation
`vcgen` hands them (`some (f, a) = st.viewApp i`) under a true tag test: the
view itself, for the inversions (task #120: `bridge_fwd`'s defaults). -/
@[bridge_fwd] theorem view_of_viewApp_tag' {st : EStore} {i f a : EIdx}
    (htg : (i.tag == ETag.app) = true) (h : some (f, a) = st.viewApp i) :
    st.view i = some (.app f a) := view_of_viewApp_tag htg h.symm

@[bridge_fwd] theorem view_of_viewSort_tag' {st : EStore} {i : EIdx} {u : LIdx}
    (htg : (i.tag == ETag.sort) = true) (h : some u = st.viewSort i) :
    st.view i = some (.sort u) := view_of_viewSort_tag htg h.symm

@[bridge_fwd] theorem view_of_viewBVar_tag' {st : EStore} {i : EIdx} {k : Nat}
    (htg : (i.tag == ETag.bvar) = true) (h : some k = st.viewBVar i) :
    st.view i = some (.bvar k) := view_of_viewBVar_tag htg h.symm

@[bridge_fwd] theorem view_of_viewConst_tag' {st : EStore} {i : EIdx} {n : NIdx} {us : LsIdx}
    (htg : (i.tag == ETag.const) = true) (h : some (n, us) = st.viewConst i) :
    st.view i = some (.const n us) := view_of_viewConst_tag htg h.symm

@[bridge_fwd] theorem view_of_viewLet_tag' {st : EStore} {i ty val b : EIdx}
    (htg : (i.tag == ETag.letE) = true) (h : some (ty, val, b) = st.viewLet i) :
    st.view i = some (.letE ty val b) := view_of_viewLet_tag htg h.symm

@[bridge_fwd] theorem view_of_viewProj_tag' {st : EStore} {i : EIdx} {n : NIdx} {k : Nat} {s : EIdx}
    (htg : (i.tag == ETag.proj) = true) (h : some (n, k, s) = st.viewProj i) :
    st.view i = some (.proj n k s) := view_of_viewProj_tag htg h.symm

/-- con-leche: none — the binder view under a true `lam` tag, in the
orientation `vcgen` hands it (task #120: `bridge_auto`'s defaults). -/
@[bridge_fwd] theorem view_of_viewBind_lam_tag' {st : EStore} {i ty b : EIdx}
    (htg : (i.tag == ETag.lam) = true) (h : some (ty, b) = st.viewBind i) :
    st.view i = some (.lam ty b) := view_of_viewBind_lam (by simpa using htg) h.symm

/-- con-leche: none — the binder view under a true `forallE` tag. -/
@[bridge_fwd] theorem view_of_viewBind_forallE_tag' {st : EStore} {i ty b : EIdx}
    (htg : (i.tag == ETag.forallE) = true) (h : some (ty, b) = st.viewBind i) :
    st.view i = some (.forallE ty b) := by
  rw [view_of_viewBind h.symm, eBindView, show i.tag = ETag.forallE by simpa using htg]
  rfl

/-- con-leche: none — `view_of_viewBind` in the orientation `vcgen` hands the
binder arms (`some (ty, b) = st.viewBind i`). -/
@[bridge_fwd] theorem view_of_viewBind' {st : EStore} {i ty b : EIdx}
    (h : some (ty, b) = st.viewBind i) : st.view i = some (eBindView i.tag ty b) :=
  view_of_viewBind h.symm

attribute [bridge_fwd] isSome_eBindView

/-- con-leche: none — an optional handle that is `some` denotes a `some`. -/
@[bridge_fwd] theorem denoteEO_some_inv {st : EStore} {r : EIdx} {v : Option ConLeche.Expr}
    (h : denoteEO st (some r) = some v) : ∃ x, v = some x ∧ denoteE st r = some x := by
  simp only [denoteEO, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, rfl, hx⟩

/-- con-leche: none — the absent handle denotes `none`. -/
@[bridge_fwd] theorem denoteEO_none_inv {st : EStore} {v : Option ConLeche.Expr}
    (h : denoteEO st none = some v) : v = none :=
  (Option.some.inj h).symm

attribute [bridge_frame] lsview_isSome_of_denote

/-- con-leche: none — an answer relation moved at BOTH ends: its source
along an extension under which the subject denotes (`RelE.retarget`), its
target along one (`RelE.ext`).  `bridge_frame`'s one transport lemma for an
answer a hypothesis (or `bridge_auto`'s forward step) holds at other stores. -/
theorem RelE.transport {f : ConLeche.Expr → ConLeche.Expr} {st st0 st' st'' : EStore}
    {c r : EIdx} (h : RelE f st c st' r) (hs : Ext st st0)
    (hc : (denoteE st c).isSome = true) (ht : Ext st' st'') : RelE f st0 c st'' r :=
  (h.retarget hs hc).ext ht

-- `ConRon.BridgeTactic` names the constants above (and the bridge's own)
-- with single backticks, unchecked: this checks them.
run_cmd do
  for n in ConRon.Bridge.Frame.usedConstants do
    unless (← Lean.getEnv).contains n do
      throwError "ConRon.BridgeTactic names {n}, which does not exist"

end ConRon.Bridge
