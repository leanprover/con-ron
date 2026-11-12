/-
# `ConRon.Bridge.Rel` — the answer relations and the denotation calculus

DESIGN.md §8.2, Theorem 1.  This module is the *representation* half of the
bridge's foundation: everything that says "this handle denotes that term",
and nothing that mentions `AState`, a memo table or a Hoare triple.

It is six lemma groups over the `EStore` (DESIGN `### Task #97s`), and
**the answer relation is GENERIC** (DESIGN `### Task #97b`, finding 1):
`RelE f st c st' r` — "`r` in `st'` denotes `f` of what `c` denotes in
`st`" — gives all eleven structural walks one relation, where a monomorphic
relation per walk would need eleven.  The per-walk relations are `abbrev`s
that fix `f`, so `grind` still sees a head symbol (`Bridge/Grind.lean` reads
each as `MapRel`).

The groups, in order:

1. soundness — `AM.of_run`, the one step from a Hoare triple to a run;
2. transport — a denotation survives `Ext`, at all four handle kinds;
3. the ten denote INVERSIONS — the only place this tier unfolds `denoteE`;
4. the PROJECTIONS' exactness — `viewApp`, `viewBind` and their
   eleven siblings against `view`, the lemma `Arena/Store.lean` says "the
   bridge owes for each"; `denoteEView` and the declaration layer's
   denotations along `Ext` (4b, 4c);
5. the answer relations `RelE` / `RelV` / `RelEO` / `RelEL` / `RelL` /
   `RelLs` and the eliminators of the shapes `grind` does not read as
   `MapRel`;
6. `ViewOK` — `intern`'s precondition, one lemma per node shape.
-/
module

public import Std.WP
public import ConRon.Arena.Frontend.Readback
public import ConRon.Arena.WFProofs

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena Std.WP
open scoped Lean.Order

/-! ## 1. Soundness: from the triple back to a run -/

/-- con-leche: none — the `WP` soundness step for `AM`.  Everything `vcgen`
proves is a triple; Theorem 1 is stated on a *run*, and this is the
bridge (`Std.WP` ships `StateM.of_run_eq_wp` and `Except.of_eq_wp`, but
nothing for `StateT σ (Except ε)`). -/
theorem AM.of_run {α : Type} {prog : AM α} {s s' : AState} {a : α}
    {P : AState → Prop} {Q : α → AState → Prop}
    (hp : P s) (h : prog.run s = .ok (a, s'))
    (hwp : ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; ⊤⦄) : Q a s' := by
  have hs := hwp.le_wp s hp
  rw [Std.WP.StateT.wp_apply_eq, h] at hs
  exact hs

/-- con-leche: none — `AM.of_run`'s converse: a partial-correctness triple
from a statement about every accepting run. -/
theorem AM.triple_of_run {α : Type} {prog : AM α} {P : AState → Prop}
    {Q : α → AState → Prop}
    (h : ∀ (s : AState) (a : α) (s' : AState), P s → prog.run s = .ok (a, s') → Q a s') :
    ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; ⊤⦄ := by
  refine ⟨fun s hp => ?_⟩
  rw [Std.WP.StateT.wp_apply_eq]
  cases hr : prog.run s with
  | error e => change (⊤ : Arena.CheckError → Prop) e; simp
  | ok p => exact h s p.1 p.2 hp hr

/-! ## 2. Transport

Four facts; after them no proof in the bridge ever unfolds `denoteE`'s `Ext`
argument. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt (the `Ext` conjunct) — a
denotation survives every arena extension. -/
@[grind →] theorem denote_ext {st st' : EStore} {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) (hx : Ext st st') : denoteE st' h = some e :=
  hx.expr h e hd

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same for a NAME
handle: `Ext` carries the three nested stores too. -/
@[grind →] theorem denoteN_ext {st st' : EStore} {c : NIdx} {x : ConLeche.Name}
    (hd : denoteN st.ns c = some x) (hx : Ext st st') :
    denoteN st'.ns c = some x :=
  hx.lss.ls.ns c x hd

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same for a LEVEL
handle. -/
@[grind →] theorem denoteL_ext {st st' : EStore} {c : LIdx} {u : Level}
    (hd : denoteL st.ls c = some u) (hx : Ext st st') :
    denoteL st'.ls c = some u :=
  hx.lss.ls.lvl c u hd

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same for an interned
universe-argument LIST handle. -/
@[grind →] theorem denoteLs_ext {st st' : EStore} {c : LsIdx} {us : List Level}
    (hd : denoteLs st.lss c = some us) (hx : Ext st st') :
    denoteLs st'.lss c = some us :=
  hx.lss.lst c us hd

/-- con-leche: none — a denoting handle has a view; this is what discharges
`intern`'s `ViewOK` at a node whose children denote. -/
theorem view_isSome_of_denote {st : EStore} {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) : (st.view h).isSome = true := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  rw [hv]; rfl

/-- con-leche: none — a name handle that denotes has a view. -/
@[grind →] theorem nview_isSome_of_denote {st : NStore} {c : NIdx}
    {x : ConLeche.Name} (hd : denoteN st c = some x) :
    (st.view c).isSome = true := by
  obtain ⟨w, hw⟩ := denoteN_view hd; rw [hw]; rfl

/-- con-leche: none — a level handle that denotes has a view. -/
@[grind →] theorem lview_isSome_of_denote {st : LStore} {c : LIdx} {u : Level}
    (hd : denoteL st c = some u) : (st.view c).isSome = true := by
  obtain ⟨w, hw⟩ := denoteL_view hd; rw [hw]; rfl

/-! ## 3. The denote-inversion layer

Ten lemmas, one per constructor — the *only* place this tier unfolds
`denoteE`.  Each says: given the handle's view, the denoted term has the
matching shape and the children denote.  `vcgen` hands the view as a branch
condition, so one `obtain` per branch puts the children's denotations in
context and everything after is pure.  (con-leche's `Verify/Disc.lean` is the
same layer, site by site.) -/

/-- con-leche: none — trade the fuel for the rank once, at the top of each
inversion. -/
theorem denoteE_view_eq {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {w : ENodeView} (hw : st.view h = some w) :
    denoteE st h = denoteEView st w := by
  obtain ⟨rk, hr⟩ := hwf; exact denoteE_unfold hr hw

theorem denote_bvar_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {i : Nat}
    {e : Expr} (hw : st.view h = some (.bvar i)) (he : denoteE st h = some e) :
    e = .bvar i := by
  rw [denoteE_view_eq hwf hw, denoteEView] at he; exact (Option.some.inj he).symm

theorem denote_fvar_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {k : Nat}
    {ty : EIdx} {e : Expr} (hw : st.view h = some (.fvar k ty))
    (he : denoteE st h = some e) :
    ∃ t, e = .fvar k t ∧ denoteE st ty = some t := by
  rw [denoteE_view_eq hwf hw, denoteEView, Option.map_eq_some_iff] at he
  obtain ⟨t, ht, rfl⟩ := he; exact ⟨t, rfl, ht⟩

theorem denote_sort_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {u : LIdx}
    {e : Expr} (hw : st.view h = some (.sort u)) (he : denoteE st h = some e) :
    ∃ l, e = .sort l ∧ denoteL st.ls u = some l := by
  rw [denoteE_view_eq hwf hw, denoteEView, Option.map_eq_some_iff] at he
  obtain ⟨l, hl, rfl⟩ := he; exact ⟨l, rfl, hl⟩

theorem denote_const_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {n : NIdx}
    {us : LsIdx} {e : Expr} (hw : st.view h = some (.const n us))
    (he : denoteE st h = some e) :
    ∃ nm ls, e = .const nm ls ∧ denoteN st.ns n = some nm ∧
      denoteLs st.lss us = some ls := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨nm, ls, hn, hl, rfl⟩ := he; exact ⟨nm, ls, rfl, hn, hl⟩

theorem denote_lit_inv {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {l : Literal} {e : Expr} (hw : st.view h = some (.lit l))
    (he : denoteE st h = some e) : e = .lit l := by
  rw [denoteE_view_eq hwf hw, denoteEView] at he; exact (Option.some.inj he).symm

theorem denote_app_inv {st : EStore} (hwf : StoreWF st) {h f a : EIdx}
    {e : Expr} (hw : st.view h = some (.app f a))
    (he : denoteE st h = some e) :
    ∃ ef ea, e = .app ef ea ∧ denoteE st f = some ef ∧ denoteE st a = some ea := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

theorem denote_lam_inv {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {e : Expr} (hw : st.view h = some (.lam ty b))
    (he : denoteE st h = some e) :
    ∃ et eb, e = .lam et eb ∧ denoteE st ty = some et ∧
      denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

theorem denote_forallE_inv {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {e : Expr} (hw : st.view h = some (.forallE ty b))
    (he : denoteE st h = some e) :
    ∃ et eb, e = .forallE et eb ∧ denoteE st ty = some et ∧
      denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

theorem denote_letE_inv {st : EStore} (hwf : StoreWF st) {h ty w b : EIdx}
    {e : Expr} (hw : st.view h = some (.letE ty w b))
    (he : denoteE st h = some e) :
    ∃ et ew eb, e = .letE et ew eb ∧ denoteE st ty = some et ∧
      denoteE st w = some ew ∧ denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt3_eq_some_iff] at he
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := he; exact ⟨x, y, z, rfl, hx, hy, hz⟩

theorem denote_proj_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {n : NIdx}
    {i : Nat} {sub : EIdx} {e : Expr} (hw : st.view h = some (.proj n i sub))
    (he : denoteE st h = some e) :
    ∃ nm es, e = .proj nm i es ∧ denoteN st.ns n = some nm ∧
      denoteE st sub = some es := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

/-! ## 4. The projections' exactness

`Arena/Store.lean` states the obligation for each: "the exactness lemma the
bridge owes for each is `getApp t i = (t.get i).bind appParts` and its
siblings".  What the twins actually need is the *forward* direction, and with
the tag the caller has already tested off the handle word: a projection that
answers `some fields` at a handle whose tag is that constructor's fixes
`view`.

The tag hypothesis is not decoration.  A projection reads its array
**without** testing the tag (that is the whole point of a projection — the
caller tested it already), so without it the conclusion is false: a `bvar`
handle whose index happens to be in range of the `sorts` array projects a
`sort`.  (`ETables.getApp` alone tests something, the handle's wide shape, as
`get`'s `app` arm does, DESIGN §8.3; a wide handle's tag is `app`, so there
the hypothesis is implied, and it is kept for the uniform shape.)  The twins always test first (DESIGN
`### Task #97-P6-13`: "a clause that is one constructor plus a fallthrough tests
the handle's own tag word BEFORE reading the store"), so the hypothesis is
always available. -/

/-- con-leche: none — `view` IS the tier select over `ETables.get`, the binder
arms included. -/
theorem EStore.view_eq_tier {st : EStore} {i : EIdx} :
    st.view i = (if i.isPersistent then st.pers.get i
      else if st.scratchOn then st.scr.get i else none) := by
  simp only [EStore.view]

/-- con-leche: none — the tier select is the same for `view` and for every
projection, so the transfer is proved ONCE over an abstract pair of tier
readers and each projection below is three lines. -/
theorem EStore.view_of_proj {st : EStore} {i : EIdx} {v : ENodeView}
    {α : Type} {p : ETables → EIdx → Option α} {x : α}
    (hstep : ∀ t : ETables, p t i = some x → t.get i = some v)
    (h : (if i.isPersistent then p st.pers i
          else if st.scratchOn then p st.scr i else none) = some x) :
    st.view i = some v := by
  simp only [EStore.view]
  by_cases hp : i.isPersistent = true
  · rw [ite_eq_left hp] at h ⊢; exact hstep _ h
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h ⊢
    simp only [Bool.false_eq_true, ite_false] at h ⊢
    by_cases hon : st.scratchOn = true
    · rw [ite_eq_left hon] at h ⊢; exact hstep _ h
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

theorem ETables.get_of_getBVar {t : ETables} {i : EIdx} {k : Nat}
    (htg : i.tag = ETag.bvar) (h : t.getBVar i = some k) :
    t.get i = some (.bvar k) := by
  simp only [ETables.getBVar, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.bvar]

theorem ETables.get_of_getFVar {t : ETables} {i : EIdx} {k : Nat} {ty : EIdx}
    (htg : i.tag = ETag.fvar) (hk : t.getFVarIdx i = some k)
    (hty : t.getFVarTy i = some ty) : t.get i = some (.fvar k ty) := by
  simp only [ETables.getFVarIdx, Option.map_eq_some_iff] at hk
  obtain ⟨r, hr, rfl⟩ := hk
  simp only [ETables.getFVarTy, hr, Option.map_some, Option.some.injEq] at hty
  subst hty
  simp [ETables.get, htg, hr, ETag.fvar, ETag.bvar]

theorem ETables.get_of_getSort {t : ETables} {i : EIdx} {u : LIdx}
    (htg : i.tag = ETag.sort) (h : t.getSort i = some u) :
    t.get i = some (.sort u) := by
  simp only [ETables.getSort, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.sort, ETag.bvar, ETag.fvar]

theorem ETables.get_of_getConst {t : ETables} {i : EIdx} {n : NIdx} {us : LsIdx}
    (htg : i.tag = ETag.const) (h : t.getConst i = some (n, us)) :
    t.get i = some (.const n us) := by
  simp only [ETables.getConst, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨r, hr, rfl, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.const, ETag.bvar, ETag.fvar, ETag.sort]

theorem ETables.get_of_getApp {t : ETables} {i : EIdx} {f a : EIdx}
    (htg : i.tag = ETag.app) (h : t.getApp i = some (f, a)) :
    t.get i = some (.app f a) := by
  simp only [ETables.getApp] at h
  by_cases hw : i.isWide = true
  · rw [ite_eq_left hw] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨r, hr, rfl, rfl⟩ := h
    simp [ETables.get, htg, hw, hr, ETag.app, ETag.bvar, ETag.fvar, ETag.sort,
      ETag.const]
  · rw [ite_eq_right hw] at h; simp at h

theorem ETables.get_of_getLet {t : ETables} {i : EIdx} {ty val b : EIdx}
    (htg : i.tag = ETag.letE) (h : t.getLet i = some (ty, val, b)) :
    t.get i = some (.letE ty val b) := by
  simp only [ETables.getLet, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨r, hr, rfl, rfl, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.letE, ETag.bvar, ETag.fvar, ETag.sort,
    ETag.const, ETag.app, ETag.lam, ETag.forallE]

theorem ETables.get_of_getProj {t : ETables} {i : EIdx} {n : NIdx} {k : Nat}
    {e : EIdx} (htg : i.tag = ETag.proj) (h : t.getProj i = some (n, k, e)) :
    t.get i = some (.proj n k e) := by
  simp only [ETables.getProj, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨r, hr, rfl, rfl, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.proj, ETag.bvar, ETag.fvar, ETag.sort,
    ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE,
    ETag.lit]

theorem ETables.get_of_getBind {t : ETables} {i ty b : EIdx}
    (h : t.getBind i = some (ty, b)) :
    t.get i = some (eBindView i.tag ty b) := by
  simp only [ETables.getBind] at h
  by_cases hl : (i.tag == ETag.lam) = true
  · rw [ite_eq_left hl] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨r, hr, rfl, rfl⟩ := h
    have hl' : i.tag = ETag.lam := by simpa using hl
    simp [ETables.get, eBindView, hl', hr, ETag.lam, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.app]
  · simp only [Bool.not_eq_true] at hl
    rw [hl] at h; simp only [Bool.false_eq_true, ite_false] at h
    by_cases hf : (i.tag == ETag.forallE) = true
    · rw [ite_eq_left hf] at h
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨r, hr, rfl, rfl⟩ := h
      have hf' : i.tag = ETag.forallE := by simpa using hf
      simp [ETables.get, eBindView, hf', hr, ETag.lam, ETag.forallE, ETag.bvar,
        ETag.fvar, ETag.sort, ETag.const, ETag.app]
    · simp only [Bool.not_eq_true] at hf
      rw [hf] at h; simp at h

/-! ### The eleven `EStore` projections against `view` -/

theorem view_of_viewBVar {st : EStore} {i : EIdx} {k : Nat}
    (htg : i.tag = ETag.bvar) (h : st.viewBVar i = some k) :
    st.view i = some (.bvar k) :=
  EStore.view_of_proj (fun _ hh => ETables.get_of_getBVar htg hh) h

/-- con-leche: none — the `fvar` node is the one whose fields are read by TWO
projections (`viewFVarIdx` and `viewFVarTy`, DESIGN `### Task #97-P6-10`), so
the tier select is taken by hand here instead of through `view_of_proj`. -/
theorem view_of_viewFVar {st : EStore} {i : EIdx} {k : Nat} {ty : EIdx}
    (htg : i.tag = ETag.fvar) (hk : st.viewFVarIdx i = some k)
    (hty : st.viewFVarTy i = some ty) : st.view i = some (.fvar k ty) := by
  rw [EStore.view_eq_tier]
  simp only [EStore.viewFVarIdx, EStore.persGetFVarIdx] at hk
  simp only [EStore.viewFVarTy, EStore.persGetFVarTy] at hty
  by_cases hp : i.isPersistent = true
  · rw [ite_eq_left hp] at hk hty ⊢; exact ETables.get_of_getFVar htg hk hty
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at hk hty ⊢
    simp only [Bool.false_eq_true, ite_false] at hk hty ⊢
    by_cases hon : st.scratchOn = true
    · rw [ite_eq_left hon] at hk hty ⊢; exact ETables.get_of_getFVar htg hk hty
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at hk; simp at hk

theorem view_of_viewSort {st : EStore} {i : EIdx} {u : LIdx}
    (htg : i.tag = ETag.sort) (h : st.viewSort i = some u) :
    st.view i = some (.sort u) :=
  EStore.view_of_proj (fun _ hh => ETables.get_of_getSort htg hh) h

theorem view_of_viewConst {st : EStore} {i : EIdx} {n : NIdx} {us : LsIdx}
    (htg : i.tag = ETag.const) (h : st.viewConst i = some (n, us)) :
    st.view i = some (.const n us) :=
  EStore.view_of_proj (fun _ hh => ETables.get_of_getConst htg hh) h

theorem view_of_viewApp {st : EStore} {i f a : EIdx}
    (htg : i.tag = ETag.app) (h : st.viewApp i = some (f, a)) :
    st.view i = some (.app f a) :=
  EStore.view_of_proj (fun _ hh => ETables.get_of_getApp htg hh) h

theorem view_of_viewLet {st : EStore} {i ty val b : EIdx}
    (htg : i.tag = ETag.letE) (h : st.viewLet i = some (ty, val, b)) :
    st.view i = some (.letE ty val b) :=
  EStore.view_of_proj (fun _ hh => ETables.get_of_getLet htg hh) h

theorem view_of_viewProj {st : EStore} {i : EIdx} {n : NIdx} {k : Nat}
    {e : EIdx} (htg : i.tag = ETag.proj) (h : st.viewProj i = some (n, k, e)) :
    st.view i = some (.proj n k e) :=
  EStore.view_of_proj (fun _ hh => ETables.get_of_getProj htg hh) h

/-- con-leche: none — the BINDER projection: `viewBind` reads either binder
array, and `eBindView` rebuilds the constructor the handle's own tag names. -/
theorem view_of_viewBind {st : EStore} {i ty b : EIdx}
    (h : st.viewBind i = some (ty, b)) :
    st.view i = some (eBindView i.tag ty b) :=
  EStore.view_of_proj (fun _ hh => ETables.get_of_getBind hh) h

/-- con-leche: none — and the same at the `lam` tag, where `eBindView`
resolves. -/
theorem view_of_viewBind_lam {st : EStore} {i ty b : EIdx}
    (htg : i.tag = ETag.lam) (h : st.viewBind i = some (ty, b)) :
    st.view i = some (.lam ty b) := by
  rw [view_of_viewBind h, eBindView, htg]
  simp

/-- con-leche: none — and at the `forallE` tag. -/
theorem view_of_viewBind_forallE {st : EStore} {i ty b : EIdx}
    (htg : i.tag = ETag.forallE) (h : st.viewBind i = some (ty, b)) :
    st.view i = some (.forallE ty b) := by
  rw [view_of_viewBind h, eBindView, htg]
  simp [ETag.lam, ETag.forallE]

/-- con-leche: none — the converse at the tier: a tier that decodes a handle
to a binder view projects the same two fields. -/
theorem ETables.getBind_of_get {t : ETables} {i ty b : EIdx} {v : ENodeView}
    (h : t.get i = some v) (hv : v = .lam ty b ∨ v = .forallE ty b) :
    t.getBind i = some (ty, b) := by
  simp only [ETables.get] at h
  simp only [ETables.getBind]
  repeat' split at h
  all_goals first
    | (obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
       rcases hv with hv | hv <;> cases hv <;> simp_all [ETag.lam, ETag.forallE])
    | exact absurd h (by simp)

/-- con-leche: none — **the converse of `view_of_viewBind`**: a handle that
views to a λ (or a ∀) is read by `viewBind` as its two fields. -/
theorem viewBind_of_view {st : EStore} {i ty b : EIdx} {v : ENodeView}
    (h : st.view i = some v) (hv : v = .lam ty b ∨ v = .forallE ty b) :
    st.viewBind i = some (ty, b) := by
  rw [EStore.view_eq_tier] at h
  simp only [EStore.viewBind, EStore.persGetBind]
  by_cases hp : i.isPersistent = true
  · rw [ite_eq_left hp] at h ⊢; exact ETables.getBind_of_get h hv
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h ⊢; simp only [Bool.false_eq_true, ite_false] at h ⊢
    by_cases hon : st.scratchOn = true
    · rw [ite_eq_left hon] at h ⊢; exact ETables.getBind_of_get h hv
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

theorem viewBind_of_view_lam {st : EStore} {i ty b : EIdx}
    (h : st.view i = some (.lam ty b)) : st.viewBind i = some (ty, b) :=
  viewBind_of_view h (Or.inl rfl)

/-! ### The same eight, in the form the twins' tag dispatch produces

A twin tests `h.tag == ETag.C` (a `Bool`) and then takes the projection, so
what `vcgen` hands each arm is `(i.tag == ETag.C) = true` and an equation on
`st.viewC i`.  These are group 4's lemmas at that spelling, and they are
`@[grind →]` — the projection read is their ematch pattern, so the closer
derives the `view` fact itself and the arm proofs never mention it. -/

@[grind →] theorem view_of_viewApp_tag {st : EStore} {i f a : EIdx}
    (htg : (i.tag == ETag.app) = true) (h : st.viewApp i = some (f, a)) :
    st.view i = some (.app f a) :=
  view_of_viewApp (by simpa using htg) h

@[grind →] theorem view_of_viewSort_tag {st : EStore} {i : EIdx} {u : LIdx}
    (htg : (i.tag == ETag.sort) = true) (h : st.viewSort i = some u) :
    st.view i = some (.sort u) :=
  view_of_viewSort (by simpa using htg) h

@[grind →] theorem view_of_viewConst_tag {st : EStore} {i : EIdx} {n : NIdx}
    {us : LsIdx} (htg : (i.tag == ETag.const) = true)
    (h : st.viewConst i = some (n, us)) : st.view i = some (.const n us) :=
  view_of_viewConst (by simpa using htg) h

@[grind →] theorem view_of_viewFVar_tag {st : EStore} {i : EIdx} {k : Nat}
    {ty : EIdx} (htg : (i.tag == ETag.fvar) = true)
    (hk : st.viewFVarIdx i = some k) (hty : st.viewFVarTy i = some ty) :
    st.view i = some (.fvar k ty) :=
  view_of_viewFVar (by simpa using htg) hk hty

/-! ### The handle carries the tag of its own view

DESIGN `### Task #97-P6-13`'s licence for the tag dispatch, as a lemma: "a
handle in a well-formed store carries the tag of its own view (`StoreWF`'s
`intern`/`push` clause), and the two forms differ only on a DANGLING handle,
which `StoreWF` excludes".  It needs no `StoreWF` at all — `ETables.get`
dispatches on `i.tag` FIRST, so a handle that decodes decodes to that tag's
constructor — and it is what lets a walk's catch-all `else` arm know which four
constructors it is looking at. -/

/-- con-leche: none — a tier that decodes a handle decodes it to the
constructor its tag names. -/
theorem ETables.tagOf_of_get {t : ETables} {i : EIdx} {v : ENodeView}
    (h : t.get i = some v) : i.tag = v.tagOf := by
  simp only [ETables.get] at h
  repeat' split at h
  all_goals first
    | (obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp h
       simp_all [ENodeView.tagOf])
    | exact absurd h (by simp)

/-- con-leche: none — the same at the whole store.
-/
theorem EStore.tagOf_of_view {st : EStore} {i : EIdx} {v : ENodeView}
    (h : st.view i = some v) : i.tag = v.tagOf := by
  rw [EStore.view_eq_tier] at h
  by_cases hp : i.isPersistent = true
  · rw [ite_eq_left hp] at h; exact ETables.tagOf_of_get h
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h; simp only [Bool.false_eq_true, ite_false] at h
    by_cases hon : st.scratchOn = true
    · rw [ite_eq_left hon] at h; exact ETables.tagOf_of_get h
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

/-! ### The tag-first twin's two arms

A twin that tests a handle's TAG before it reads the node has two arm shapes:
the `else` arm, with the tag test's negation and the handle's view, and the
binder arm, which reads `viewBind`.  One lemma each. -/

/-- con-leche: none — **the `else` arm**: a handle whose tag is not `t`
views to a node whose tag is not `t`. -/
theorem view_tagOf_ne {st : EStore} {h : EIdx} {v : ENodeView} {t : UInt32}
    (hv : st.view h = some v) (ht : ¬ (h.tag == t) = true) : v.tagOf ≠ t := by
  rw [← EStore.tagOf_of_view hv]
  simpa using ht

/-- con-leche: none — **a `forallE`-tagged handle's `viewBind` is its view**. -/
theorem view_forallE_of_viewBind {st : EStore} {h ty b : EIdx}
    (htg : (h.tag == ETag.forallE) = true)
    (h1 : st.viewBind h = some (ty, b)) :
    st.view h = some (.forallE ty b) :=
  view_of_viewBind_forallE (by simpa using htg) h1

/-! ## 4b. `denoteEView` transports too

`internRebuilt`'s `same` branch (the upward cutoff, DESIGN `### Task #97-P6-5`)
answers the ORIGINAL handle, and what its caller must then show is that the
original handle denotes the rebuilt view — which is `denoteE_view_eq` plus this.
-/

/-! ## 4c. The declaration layer's denotation transports

`Arena/Frontend/Readback.lean` denotes the declaration layer
(`IConstantVal`, `IRecRule`, `IIndCaps`, `IProjTable`, `IConstantInfo`) and
DESIGN §8.2's parser-tier statement is about `denoteDecl`.  Ten mechanical
transports, one per denotation, so that `IFEnvOK` and the `DeclCheck` tier
have the same `Ext` calculus the expression layer has. -/

/-- con-leche: none — a list of handles denotes through an extension. -/
theorem denoteEList_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (rs : List EIdx) (xs : List Expr),
      Frontend.denoteEList st rs = some xs →
        Frontend.denoteEList st' rs = some xs := by
  intro rs
  induction rs with
  | nil => intro _ h; exact h
  | cons j js ih =>
    intro xs h
    simp only [Frontend.denoteEList] at h ⊢
    cases hj : denoteE st j with
    | none => rw [hj] at h; simp at h
    | some y =>
      cases hjs : Frontend.denoteEList st js with
      | none => rw [hj, hjs] at h; simp at h
      | some ys =>
        rw [hj, hjs] at h
        rw [denote_ext hj hx, ih ys hjs]
        exact h

theorem denoteNList_ext {st st' : NStore} (hx : NExt st st') :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st hs = some xs →
        Frontend.denoteNList st' hs = some xs := by
  intro hs
  induction hs with
  | nil => intro _ h; exact h
  | cons a as ih =>
    intro xs h
    simp only [Frontend.denoteNList] at h ⊢
    cases ha : denoteN st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys => rw [ha, has] at h; rw [hx a y ha, ih ys has]; exact h

theorem denoteLList_ext {st st' : LStore} (hx : LExt st st') :
    ∀ (hs : List LIdx) (xs : List Level),
      denoteLList st hs = some xs → denoteLList st' hs = some xs := by
  intro hs
  induction hs with
  | nil => intro _ h; exact h
  | cons a as ih =>
    intro xs h
    simp only [denoteLList] at h ⊢
    cases ha : denoteL st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : denoteLList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys => rw [ha, has] at h; rw [hx.lvl a y ha, ih ys has]; exact h

/-- con-leche: none — `denoteNList_ext` at the whole arena's `Ext`, so that
`st.ns` and not `st.lss.ls.ns` is what the rewrite sees. -/
theorem denoteNListE_ext {st st' : EStore} (hx : Ext st st')
    (hs : List NIdx) (xs : List ConLeche.Name)
    (h : Frontend.denoteNList st.ns hs = some xs) :
    Frontend.denoteNList st'.ns hs = some xs :=
  denoteNList_ext hx.lss.ls.ns hs xs h

/-- con-leche: none — the same for a level-handle list. -/
theorem denoteLListE_ext {st st' : EStore} (hx : Ext st st')
    (hs : List LIdx) (xs : List Level)
    (h : denoteLList st.ls hs = some xs) : denoteLList st'.ls hs = some xs :=
  denoteLList_ext hx.lss.ls hs xs h

theorem denoteEArray_ext {st st' : EStore} {hs : Array EIdx} {xs : Array Expr}
    (h : Frontend.denoteEArray st hs = some xs) (hx : Ext st st') :
    Frontend.denoteEArray st' hs = some xs := by
  simp only [Frontend.denoteEArray] at h ⊢
  cases hl : Frontend.denoteEList st hs.toList with
  | none => rw [hl] at h; simp at h
  | some ys => rw [hl] at h; rw [denoteEList_ext hx _ ys hl]; exact h

theorem denoteCV_ext {st st' : EStore} {cv : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st cv = some c) (hx : Ext st st') :
    Frontend.denoteCV st' cv = some c := by
  simp only [Frontend.denoteCV] at h ⊢
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
        rw [denoteN_ext hn hx, denoteNListE_ext hx _ lps hl,
          denote_ext ht hx]
        exact h

theorem denoteFire_ext {st st' : EStore} {f : IRecRuleFire} {g : RecRuleFire}
    (h : Frontend.denoteFire st f = some g) (hx : Ext st st') :
    Frontend.denoteFire st' f = some g := by
  cases f with
  | plain => exact h
  | nested lvls pins =>
    simp only [Frontend.denoteFire] at h ⊢
    cases hl : denoteLList st.ls lvls with
    | none => rw [hl] at h; simp at h
    | some ls =>
      cases hp : Frontend.denoteEList st pins with
      | none => rw [hl, hp] at h; simp at h
      | some ps =>
        rw [hl, hp] at h
        rw [denoteLListE_ext hx _ ls hl, denoteEList_ext hx _ ps hp]
        exact h
  | levels lvls =>
    simp only [Frontend.denoteFire, Option.map_eq_some_iff] at h ⊢
    obtain ⟨ls, hl, rfl⟩ := h
    exact ⟨ls, denoteLListE_ext hx _ ls hl, rfl⟩

theorem denoteRule_ext {st st' : EStore} {rl : IRecRule} {r : RecRule}
    (h : Frontend.denoteRule st rl = some r) (hx : Ext st st') :
    Frontend.denoteRule st' rl = some r := by
  simp only [Frontend.denoteRule] at h ⊢
  cases hc : denoteN st.ns rl.ctor with
  | none => rw [hc] at h; simp at h
  | some c =>
    cases hf : Frontend.denoteFire st rl.fire with
    | none => rw [hc, hf] at h; simp at h
    | some fr =>
      cases hr : denoteE st rl.rhs with
      | none => rw [hc, hf, hr] at h; simp at h
      | some rh =>
        rw [hc, hf, hr] at h
        rw [denoteN_ext hc hx, denoteFire_ext hf hx, denote_ext hr hx]
        exact h

theorem denoteRules_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (rs : List IRecRule) (xs : List RecRule),
      Frontend.denoteRules st rs = some xs →
        Frontend.denoteRules st' rs = some xs := by
  intro rs
  induction rs with
  | nil => intro _ h; exact h
  | cons a as ih =>
    intro xs h
    simp only [Frontend.denoteRules] at h ⊢
    cases ha : Frontend.denoteRule st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteRules st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteRule_ext ha hx, ih ys has]
        exact h

theorem denoteCaps_ext {st st' : EStore} {c : IIndCaps} {d : IndCaps}
    (h : Frontend.denoteCaps st c = some d) (hx : Ext st st') :
    Frontend.denoteCaps st' c = some d := by
  simp only [Frontend.denoteCaps] at h ⊢
  · cases ha : Frontend.denoteNList st.ns c.all with
    | none => rw [ha] at h; simp at h
    | some all =>
      cases hk : Frontend.denoteNList st.ns c.ctors with
      | none => rw [ha, hk] at h; simp at h
      | some ks =>
        rw [ha, hk] at h
        rw [denoteNListE_ext hx _ _ ha, denoteNListE_ext hx _ _ hk]
        exact h

theorem denoteProjTable_ext {st st' : EStore} {t : IProjTable} {p : ProjTable}
    (h : Frontend.denoteProjTable st t = some p) (hx : Ext st st') :
    Frontend.denoteProjTable st' t = some p := by
  simp only [Frontend.denoteProjTable] at h ⊢
  cases hs : denoteN st.ns t.structName with
  | none => rw [hs] at h; simp at h
  | some sn =>
    cases hl : Frontend.denoteNList st.ns t.levelParams with
    | none => rw [hs, hl] at h; simp at h
    | some lps =>
      cases hc : denoteN st.ns t.ctor with
      | none => rw [hs, hl, hc] at h; simp at h
      | some ct =>
        rw [hs, hl, hc] at h
        rw [denoteN_ext hs hx, denoteNListE_ext hx _ lps hl,
          denoteN_ext hc hx]
        cases hb : Frontend.denoteEArray st t.bodies with
        | none => rw [hb] at h; simp at h
        | some bs =>
          rw [hb] at h
          rw [denoteEArray_ext hb hx]
          exact h

/-! ### `denoteProjEntry` — the projection table's PER-FIELD denotation

The projection table has no per-field denotation of its own;
`denoteProjEntry` is the one piece of denotation machinery the Core walks tier
needs beyond the other ten transports (DESIGN `### Task #97-P3-CoreWalks`
§5).

**Why it is not `denoteProjTable` composed with `entry`.**
`Arena/Env.lean`'s `IProjTable.entry` and con-leche's `ProjTable.entry` both
read the indexed column with a DEFAULT — `bodies.getD i default` — and the two
defaults are a handle and a term that are unrelated: `(default : EIdx)` need
not denote `(default : Expr)` in any store.  So the transport
`denoteProjTable → denoteProjEntry` (`denoteProjTable_entry` below) holds
exactly where the index is IN RANGE, which is where both `findProj?`s read a
table and nowhere else.  `denoteProjTable_sizes` is what moves an in-range
hypothesis between the two sides.
-/

/-- con-leche: ConLeche/Kernel/Env.lean:433-452 ProjEntry — **the denotation
of one projection-table entry**: the four handle fields denote, the three
scalar fields (`idx`, `numParams`, `numFields`) are shared by the two tiers and
are copied.  `Frontend.denoteProjTable`'s shape exactly. -/
@[expose] def denoteProjEntry (st : EStore) (e : IProjEntry) : Option ProjEntry :=
  match denoteN st.ns e.structName, Frontend.denoteNList st.ns e.levelParams,
        denoteN st.ns e.ctor with
  | some sn, some lps, some c =>
    match denoteE st e.body with
    | some b => some ⟨sn, e.idx, lps, e.numParams, c, e.numFields, b⟩
    | none => none
  | _, _, _ => none

/-- con-leche: none — **the inversion**, and the workhorse of every walk that
reads an entry: a denoting entry denotes field by field, and its four scalar
fields are literally con-leche's.  `typeAt` needs `levelParams` and `body`;
`projCert`'s guard needs `ctor`, `numParams` and `numFields`. -/
theorem denoteProjEntry_inv {st : EStore} {e : IProjEntry} {p : ProjEntry}
    (h : denoteProjEntry st e = some p) :
    denoteN st.ns e.structName = some p.structName ∧
      Frontend.denoteNList st.ns e.levelParams = some p.levelParams ∧
      denoteN st.ns e.ctor = some p.ctor ∧
      denoteE st e.body = some p.body ∧
      p.idx = e.idx ∧ p.numParams = e.numParams ∧
      p.numFields = e.numFields := by
  simp only [denoteProjEntry] at h
  cases hs : denoteN st.ns e.structName with
  | none => rw [hs] at h; simp at h
  | some sn =>
    cases hl : Frontend.denoteNList st.ns e.levelParams with
    | none => rw [hs, hl] at h; simp at h
    | some lps =>
      cases hc : denoteN st.ns e.ctor with
      | none => rw [hs, hl, hc] at h; simp at h
      | some ct =>
        rw [hs, hl, hc] at h
        cases hb : denoteE st e.body with
        | none => rw [hb] at h; simp at h
        | some b =>
          rw [hb] at h
          obtain rfl := Option.some.inj h
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- con-leche: none — a denoting expression-handle list keeps its length. -/
theorem denoteEList_len {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr},
      Frontend.denoteEList st hs = some xs → xs.length = hs.length
  | [], xs, h => by
    simp only [Frontend.denoteEList] at h
    obtain rfl := Option.some.inj h; rfl
  | a :: as, xs, h => by
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp [denoteEList_len has]

/-- con-leche: none — the same at a LEVEL-handle list. -/
theorem denoteLList_len {st : LStore} :
    ∀ {hs : List LIdx} {us : List Level},
      denoteLList st hs = some us → us.length = hs.length
  | [], us, h => by
    simp only [denoteLList] at h
    obtain rfl := Option.some.inj h; rfl
  | a :: as, us, h => by
    simp only [denoteLList] at h
    cases ha : denoteL st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : denoteLList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp [denoteLList_len has]

/-- con-leche: none — the two indexed columns denote ELEMENTWISE, at the
`getD` both `entry`s use. -/
theorem denoteEList_getD {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr},
      Frontend.denoteEList st hs = some xs → ∀ {i : Nat}, i < hs.length →
      denoteE st (hs.getD i default) = some (xs.getD i default)
  | [], _, _, _, hi => by simp at hi
  | a :: as, xs, h, i, hi => by
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        cases i with
        | zero => simpa using ha
        | succ k =>
          simp only [List.getD_cons_succ]
          exact denoteEList_getD has (by simpa using hi)

/-- con-leche: ConLeche/Kernel/Env.lean:454-458 ProjTable.entry — **the
EXACTNESS lemma of the projection table**: taking the per-field view commutes
with the denotation, at every index the body column actually has.  This is the
only fact about `denoteProjEntry` a `findProj?` rule needs, and the range
hypothesis is exactly `IProjTable.entry`'s `getD` (see the group
note). -/
theorem denoteProjTable_entry {st : EStore} {t : IProjTable} {p : ProjTable}
    (h : Frontend.denoteProjTable st t = some p) {i : Nat}
    (hb : i < t.bodies.size) :
    denoteProjEntry st (t.entry i) = some (p.entry i) := by
  simp only [Frontend.denoteProjTable] at h
  cases hs : denoteN st.ns t.structName with
  | none => rw [hs] at h; simp at h
  | some sn =>
    cases hl : Frontend.denoteNList st.ns t.levelParams with
    | none => rw [hs, hl] at h; simp at h
    | some lps =>
      cases hc : denoteN st.ns t.ctor with
      | none => rw [hs, hl, hc] at h; simp at h
      | some ct =>
        rw [hs, hl, hc] at h
        cases hbb : Frontend.denoteEArray st t.bodies with
        | none => rw [hbb] at h; simp at h
        | some bs =>
          rw [hbb] at h
          obtain rfl := Option.some.inj h
          simp only [Frontend.denoteEArray] at hbb
          cases hbl : Frontend.denoteEList st t.bodies.toList with
          | none => rw [hbl] at hbb; simp at hbb
          | some bl =>
            rw [hbl] at hbb
            obtain rfl := Option.some.inj hbb
            have hbi : denoteE st (t.bodies.toList.getD i default)
                = some (bl.getD i default) :=
              denoteEList_getD hbl (by simpa using hb)
            have harr : t.bodies.getD i default
                = t.bodies.toList.getD i default := by
              simp only [Array.getD, List.getD]
              split
              · rw [List.getElem?_eq_getElem (by simpa using hb)]
                simp
              · rename_i hlt; exact absurd hb hlt
            have hbll : i < bl.toArray.size := by
              have : bl.toArray.size = bl.length := by simp
              rw [this, denoteEList_len hbl]
              simpa using hb
            have harr2 : bl.toArray.getD i default = bl.getD i default := by
              simp only [Array.getD, List.getD]
              split
              · rw [List.getElem?_eq_getElem (by simpa using hbll)]
                simp
              · rename_i hlt; exact absurd hbll hlt
            simp only [IProjTable.entry, ProjTable.entry, denoteProjEntry,
              harr, harr2, hs, hl, hc, hbi]

/-- con-leche: ConLeche/Kernel/Env.lean:281-326 ProjTable — the two SCALAR
fields of a table are shared by the two tiers and survive the denotation
literally.  `findProj?`'s guard is `i < numFields` on both sides, so this is
what makes the two guards the same test. -/
theorem denoteProjTable_fields {st : EStore} {t : IProjTable} {p : ProjTable}
    (h : Frontend.denoteProjTable st t = some p) :
    p.numFields = t.numFields ∧ p.numParams = t.numParams := by
  simp only [Frontend.denoteProjTable] at h
  cases hs : denoteN st.ns t.structName with
  | none => rw [hs] at h; simp at h
  | some sn =>
    cases hl : Frontend.denoteNList st.ns t.levelParams with
    | none => rw [hs, hl] at h; simp at h
    | some lps =>
      cases hc : denoteN st.ns t.ctor with
      | none => rw [hs, hl, hc] at h; simp at h
      | some ct =>
        rw [hs, hl, hc] at h
        cases hb : Frontend.denoteEArray st t.bodies with
        | none => rw [hb] at h; simp at h
        | some bs =>
          rw [hb] at h
          obtain rfl := Option.some.inj h
          exact ⟨rfl, rfl⟩

/-- con-leche: none — a denoting projection table's constructor handle denotes
the table's constructor. -/
theorem denoteProjTable_ctor {st : EStore} {t : IProjTable} {p : ProjTable}
    (h : Frontend.denoteProjTable st t = some p) :
    denoteN st.ns t.ctor = some p.ctor := by
  simp only [Frontend.denoteProjTable] at h
  cases hs : denoteN st.ns t.structName with
  | none => rw [hs] at h; simp at h
  | some sn =>
    cases hl : Frontend.denoteNList st.ns t.levelParams with
    | none => rw [hs, hl] at h; simp at h
    | some lps =>
      cases hc : denoteN st.ns t.ctor with
      | none => rw [hs, hl, hc] at h; simp at h
      | some ct =>
        rw [hs, hl, hc] at h
        cases hb : Frontend.denoteEArray st t.bodies with
        | none => rw [hb] at h; simp at h
        | some bs =>
          rw [hb] at h
          obtain rfl := Option.some.inj h
          rfl

/-- con-leche: none — a denoting constructor record: its record and its family
handle denote, and the denotation is the constructor at both. -/
theorem denoteCI_ctorInfo_some {st : EStore} {v : IConstantVal} {nP nF : Nat} {T : NIdx}
    {c : ConstantInfo} (h : Frontend.denoteCI st (.ctorInfo v nP nF T) = some c) :
    ∃ cv t, Frontend.denoteCV st v = some cv ∧ denoteN st.ns T = some t ∧
      c = .ctorInfo cv nP nF t := by
  simp only [Frontend.denoteCI] at h
  split at h
  · rename_i cv t hcv ht; cases h; exact ⟨cv, t, hcv, ht, rfl⟩
  · cases h

theorem denoteCI_ext {st st' : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) (hx : Ext st st') :
    Frontend.denoteCI st' ci = some c := by
  cases ci with
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_ext hcv hx, hc⟩
  | ctorInfo v nP nF T =>
    simp only [Frontend.denoteCI] at h ⊢
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases hT : denoteN st.ns T with
      | none => rw [hcv, hT] at h; simp at h
      | some t =>
        rw [hcv, hT] at h
        rw [denoteCV_ext hcv hx, denoteN_ext hT hx]; exact h
  | defnInfo v e hint =>
    simp only [Frontend.denoteCI] at h ⊢
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h
        rw [denoteCV_ext hcv hx, denote_ext he hx]; exact h
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_ext hcv hx, hc⟩
  | indInfo v cp =>
    simp only [Frontend.denoteCI] at h ⊢
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases hcp : Frontend.denoteCaps st cp with
      | none => rw [hcv, hcp] at h; simp at h
      | some caps =>
        rw [hcv, hcp] at h
        rw [denoteCV_ext hcv hx, denoteCaps_ext hcp hx]; exact h
  | recInfo v mI rP k rs =>
    simp only [Frontend.denoteCI] at h ⊢
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases hrs : Frontend.denoteRules st rs with
      | none => rw [hcv, hrs] at h; simp at h
      | some rules =>
        rw [hcv, hrs] at h
        rw [denoteCV_ext hcv hx, denoteRules_ext hx _ rules hrs]; exact h

/-! ## 5. The answer relations

**Generic** (DESIGN `### Task #97b`, finding 1): one relation per RESULT SHAPE,
not one per walk.  The per-walk relation is an `abbrev` that fixes the pure
function (`Bridge/ExprOps/*`), so the eliminators below still ematch and `grind`
still sees a head symbol.

Four shapes cover the whole `ExprOps` tier:

* `RelE f st c st' r` — a handle in, a handle out (`instantiate1`,
  `abstract1`, `liftLooseBVars`, …);
* `RelV f st c x` — a handle in, a REPRESENTATION-FREE value out (`Bool`,
  `Nat`: `wscopedB`, `sizeB`, `bvarBound`).  No target store,
  because the answer names none;
* `RelEO f st c st' r` — an `Option` handle out (`peelPis`);
* `RelEL f st c st' rs` — a LIST of handles out (`getAppArgs`, `bvarRange`).

The level and name shapes (`RelL`, `RelLs`) are the same at `denoteL` /
`denoteLs`. -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — **the answer relation**:
"`r` in `st'` denotes `f` of what `c` denotes in `st`".

Written as a bare `∀ e, denoteE st c = some e → …` at every call site it would
cost the automation dearly: a `∀`-hypothesis has no head symbol, so `grind`
cannot ematch on it and every use has to be supplied by hand.  Behind a `def`
it has one, and `Bridge/Grind.lean`'s `relE_eq_mapRel` reads it as `MapRel`. -/
@[expose] def RelE (f : Expr → Expr) (st : EStore) (c : EIdx) (st' : EStore) (r : EIdx) :
    Prop :=
  ∀ e, denoteE st c = some e → denoteE st' r = some (f e)

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — the answer relation at a
representation-free result. -/
@[expose] def RelV {α : Type} (f : Expr → α) (st : EStore) (c : EIdx) (x : α) : Prop :=
  ∀ e, denoteE st c = some e → x = f e

/-- con-leche: none — the denotation of an OPTIONAL handle, so that `RelEO`
has `RelE`'s shape exactly. -/
@[expose] def denoteEO (st : EStore) : Option EIdx → Option (Option Expr)
  | none => some none
  | some j => (denoteE st j).map some

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the answer relation at an
`Option` result. -/
@[expose] def RelEO (f : Expr → Option Expr) (st : EStore) (c : EIdx) (st' : EStore)
    (r : Option EIdx) : Prop :=
  ∀ e, denoteE st c = some e → denoteEO st' r = some (f e)

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the answer relation at a
LIST result. -/
@[expose] def RelEL (f : Expr → List Expr) (st : EStore) (c : EIdx) (st' : EStore)
    (rs : List EIdx) : Prop :=
  ∀ e, denoteE st c = some e → Frontend.denoteEList st' rs = some (f e)

/-- con-leche: ConLeche/Verify/SimI.lean:254 RelL — the answer relation whose
SUBJECT is a level handle and whose answer is one too (`substLMemoAt`). -/
@[expose] def RelL (f : Level → Level) (st : EStore) (c : LIdx) (st' : EStore) (r : LIdx) :
    Prop :=
  ∀ u, denoteL st.ls c = some u → denoteL st'.ls r = some (f u)

/-- con-leche: none — the same at an interned universe-argument LIST
(`substLsMemoAt`). -/
@[expose] def RelLs (f : List Level → List Level) (st : EStore) (c : LsIdx) (st' : EStore)
    (r : LsIdx) : Prop :=
  ∀ us, denoteLs st.lss c = some us → denoteLs st'.lss r = some (f us)

/-! ### The eliminators

The walks' proofs read `RelE` as `Bridge/Grind.lean`'s `MapRel`; the other
shapes keep these. -/

theorem RelV.congr {α : Type} {f g : Expr → α} {st : EStore} {c : EIdx} {x : α}
    (h : RelV f st c x) (hfg : ∀ e, f e = g e) : RelV g st c x :=
  fun e he => by rw [← hfg e]; exact h e he

@[grind →] theorem RelL.of_ext {f : Level → Level} {st st0 st' : EStore}
    {c r : LIdx} (h : RelL f st c st' r) (hx : Ext st0 st) :
    RelL f st0 c st' r :=
  fun u hu => h u (denoteL_ext hu hx)

@[grind →] theorem RelLs.of_ext {f : List Level → List Level}
    {st st0 st' : EStore} {c r : LsIdx} (h : RelLs f st c st' r)
    (hx : Ext st0 st) : RelLs f st0 c st' r :=
  fun u hu => h u (denoteLs_ext hu hx)

/-! ## 6. `ViewOK` — `intern`'s precondition

One lemma per node shape the twins build.  Each is "the children denote, hence
they have views". -/

/-- con-leche: none — a handle that denotes has a view (the `isSome`
spelling, so nothing has to be guessed). -/
theorem view_isSome {st : EStore} {c : EIdx}
    (hs : (denoteE st c).isSome = true) : (st.view c).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  exact view_isSome_of_denote he

theorem viewOK_bvar {st : EStore} {i : Nat} : st.ViewOK (.bvar i) :=
  ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

theorem viewOK_lit {st : EStore} {l : ConLeche.Literal} : st.ViewOK (.lit l) :=
  ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

theorem viewOK_fvar {st : EStore} {k : Nat} {ty : EIdx}
    (ht : (denoteE st ty).isSome = true) : st.ViewOK (.fvar k ty) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc; subst hc
      exact view_isSome ht,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

theorem viewOK_sort {st : EStore} {u : LIdx}
    (hu : (st.ls.view u).isSome = true) : st.ViewOK (.sort u) :=
  ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
   by intro c hc; simp [ENodeView.lchildren] at hc; subst hc; exact hu,
   by simp [ENodeView.lschildren]⟩

theorem viewOK_const {st : EStore} {n : NIdx} {us : LsIdx}
    (hn : (st.ns.view n).isSome = true) (hu : (st.lss.view us).isSome = true) :
    st.ViewOK (.const n us) :=
  ⟨by simp [ENodeView.echildren],
   by intro c hc; simp [ENodeView.nchildren] at hc; subst hc; exact hn,
   by simp [ENodeView.lchildren],
   by intro c hc; simp [ENodeView.lschildren] at hc; subst hc; exact hu⟩

theorem viewOK_app {st : EStore} {f a : EIdx}
    (hf : (denoteE st f).isSome = true) (ha : (denoteE st a).isSome = true) :
    st.ViewOK (.app f a) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact view_isSome hf
      · exact view_isSome ha,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

theorem viewOK_lam {st : EStore} {ty b : EIdx}
    (ht : (denoteE st ty).isSome = true) (hb : (denoteE st b).isSome = true) :
    st.ViewOK (.lam ty b) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact view_isSome ht
      · exact view_isSome hb,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

theorem viewOK_forallE {st : EStore} {ty b : EIdx}
    (ht : (denoteE st ty).isSome = true) (hb : (denoteE st b).isSome = true) :
    st.ViewOK (.forallE ty b) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact view_isSome ht
      · exact view_isSome hb,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

theorem viewOK_letE {st : EStore} {ty v b : EIdx}
    (ht : (denoteE st ty).isSome = true) (hv : (denoteE st v).isSome = true)
    (hb : (denoteE st b).isSome = true) : st.ViewOK (.letE ty v b) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl | rfl
      · exact view_isSome ht
      · exact view_isSome hv
      · exact view_isSome hb,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

theorem viewOK_proj {st : EStore} {n : NIdx} {i : Nat} {sub : EIdx}
    (hn : (st.ns.view n).isSome = true) (hs : (denoteE st sub).isSome = true) :
    st.ViewOK (.proj n i sub) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc; subst hc
      exact view_isSome hs,
   by intro c hc; simp [ENodeView.nchildren] at hc; subst hc; exact hn,
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

end ConRon.Bridge
