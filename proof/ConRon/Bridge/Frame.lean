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

open ConRon.Arena ConLeche

set_option autoImplicit false

/-! ## 1. The lemmas the search composes -/

/-- con-leche: none — an equality of stores is an extension. -/
theorem Ext.of_eq {a b : EStore} (h : a = b) : Ext a b := h ▸ Ext.refl a

/-- con-leche: none — `StateOK` reads only the store. -/
theorem StateOK.of_store {s s' : AState} (h : StateOK s) (he : s'.store = s.store) :
    StateOK s' := ⟨he ▸ h.wf⟩

/-- con-leche: none — a well-formed store is a `StateOK` state. -/
theorem StateOK.of_wf {s : AState} {st : EStore} (h : StoreWF st) (he : s.store = st) :
    StateOK s := ⟨he ▸ h⟩

/-! The bridge's own lemmas the closers compose (declared in `Bridge/Rel.lean`,
which does not import the tactic library), registered here. -/

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
theorem isSome_denote_ext {st st' : EStore} {h : EIdx}
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
is `bridge_finish`'s case split. -/

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

/-- con-leche: none — a denoting universe-argument list handle has a view
(`viewOK_const`'s premise; the name and level stores have theirs in
`Bridge/Rel.lean`; moved here from `Bridge/Specs.lean`, task #120 wave 2). -/
@[bridge_frame] theorem lsview_isSome_of_denote {st : LsStore} {c : LsIdx} {us : List ConLeche.Level}
    (hd : denoteLs st c = some us) : (st.view c).isSome = true := by
  obtain ⟨w, hw, _⟩ := denoteLs_view hd
  rw [hw]; rfl

/-- con-leche: none — an answer relation moved at BOTH ends: its source
along an extension under which the subject denotes (`RelE.retarget`), its
target along one (`RelE.ext`).  `bridge_frame`'s one transport lemma for an
answer a hypothesis (or `bridge_auto`'s forward step) holds at other stores. -/
theorem RelE.transport {f : ConLeche.Expr → ConLeche.Expr} {st st0 st' st'' : EStore}
    {c r : EIdx} (h : RelE f st c st' r) (hs : Ext st st0)
    (hc : (denoteE st c).isSome = true) (ht : Ext st' st'') : RelE f st0 c st'' r :=
  (h.retarget hs hc).ext ht

/-- con-leche: none — a denoting `cons` list of handles: its head and its tail
denote (`bridge_auto`'s default inversion for the list subjects). -/
theorem denoteEList_cons_fr {st : EStore} {a : EIdx} {as : List EIdx}
    {xs : List ConLeche.Expr} (h : Frontend.denoteEList st (a :: as) = some xs) :
    ∃ x xs', denoteE st a = some x ∧ Frontend.denoteEList st as = some xs' ∧
      xs = x :: xs' := by
  simp only [Frontend.denoteEList] at h
  cases ha : denoteE st a with
  | none => rw [ha] at h; simp at h
  | some x =>
    cases has : Frontend.denoteEList st as with
    | none => rw [ha, has] at h; simp at h
    | some ys =>
      rw [ha, has] at h
      exact ⟨x, ys, rfl, rfl, (Option.some.inj h).symm⟩

-- `ConRon.BridgeTactic` names the constants above (and the bridge's own)
-- with single backticks, unchecked: this checks them.
run_cmd do
  for n in ConRon.Bridge.Frame.usedConstants do
    unless (← Lean.getEnv).contains n do
      throwError "ConRon.BridgeTactic names {n}, which does not exist"

end ConRon.Bridge
