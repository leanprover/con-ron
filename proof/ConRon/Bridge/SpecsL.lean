/-
# `ConRon.Bridge.SpecsL` — the level store's three recursive interns, and the
memoised name-list readback

The four `@[spec]` theorems of `Monad.lean` that `Bridge/Specs.lean` does not
carry, in a module of their own only because they were written after the four
`ExprOps` groups had started against `Specs.lean`'s interface and adding to
that file would have moved the ground under them.  They belong in
`Specs.lean` and should be moved there at the next quiet moment.

* `internLevel` — intern a transient `Level` tree.  Structural on `Level`, so
  no fuel (DESIGN §8.4: "a recursion structural on something else … takes
  none"), and its `.param` arm goes through `internName`;
* `internLevelList` and `internLevels` — the same at a list, and the list
  node on top, which is what `.const`'s universe arguments are;
* `readNamesM` — the memoised `readNames`, whose recursion is on the list as
  `readNames`' is.

`internPersistentE` / `…N` / `…L` / `…Ls` are still deliberately absent:
`Arena/Store.lean`'s own note states their obligation **for the bracket** and
not for the operation (`internPersistent` breaks `fresh` transiently, and it
is `promote … dropScratch` as a whole that takes `StoreWF` to `StoreWF`), so
their specs belong to the `Promote` tier's statement.
-/
import ConRon.Bridge.Specs

namespace ConRon.Bridge

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena Std.Do

/-! ## Three forward rules the closer needs

`grind` will not compute a `match` on two `Option`s from two known branches,
so the three shapes these interns build are given to it as forward rules. -/

/-- con-leche: none — a level-handle list denotes, one cons at a time. -/
@[grind ->] theorem denoteLList_cons_of {st : EStore} {hd : LIdx}
    {tl : List LIdx} {u : Level} {us : List Level}
    (h1 : denoteL st.ls hd = some u) (h2 : denoteLList st.ls tl = some us) :
    denoteLList st.ls (hd :: tl) = some (u :: us) := by
  simp [denoteLList, h1, h2]

/-- con-leche: none — the `param` node view denotes. -/
theorem denoteLView_param_of {st : LStore} {n : NIdx}
    {x : ConLeche.Name} (h : denoteN st.ns n = some x) :
    denoteLView st (.param n) = some (.param x) := by
  simp only [denoteLView, h, Option.map_some]

/-- con-leche: none — the same at the whole arena's `ns`, so that `st.ns` and
not `st.lss.ls.ns` is what the closer sees (the wrapper `Bridge/Rel.lean`'s
`denoteNListE_ext` exists for the same reason). -/
@[grind ->] theorem denoteLView_param_ofE {st : EStore} {n : NIdx}
    {x : ConLeche.Name} (h : denoteN st.ns n = some x) :
    denoteLView st.ls (.param n) = some (.param x) :=
  denoteLView_param_of h

/-- con-leche: none — a universe-argument LIST node view denotes exactly what
its level-handle list denotes. -/
@[grind ->] theorem denoteLsView_of {st : LsStore} {v : LsNodeView}
    {us : List Level} (h : denoteLList st.ls v = some us) :
    denoteLsView st v = some us := by
  show denoteLList st.ls v = some us
  exact h

/-- con-leche: none — the cons rule with the extension chain already inside
it (task #97s's rule: "the same fact with the chain already inside it … is
not a liability"). -/
@[grind ->] theorem denoteLList_cons_ext {st st' : EStore} {hd : LIdx}
    {tl : List LIdx} {u : Level} {us : List Level} (hx : Ext st st')
    (h1 : denoteL st.ls hd = some u)
    (h2 : denoteLList st'.ls tl = some us) :
    denoteLList st'.ls (hd :: tl) = some (u :: us) :=
  denoteLList_cons_of (denoteL_ext h1 hx) h2

/-- con-leche: none — and the list node's own answer, with the chain inside
it: what `internLevels` needs. -/
@[grind ->] theorem denoteLs_of_list_ext {st st' : EStore} {h : LsIdx}
    {v : LsNodeView} {us : List Level} (hx : Ext st st')
    (h1 : denoteLList st.ls v = some us)
    (h2 : denoteLs st'.lss h = denoteLsView st'.lss v) :
    denoteLs st'.lss h = some us := by
  rw [h2]; exact denoteLsView_of (denoteLListE_ext hx v us h1)

/-- con-leche: none — `internLsNode`'s `ViewOK`, from the list's denotation:
every element of a denoting level-handle list has a view. -/
@[grind ->] theorem lsViewOK_of_denoteLList {st : EStore} :
    ∀ (hs : List LIdx) (us : List Level),
      denoteLList st.ls hs = some us → st.lss.ViewOK hs := by
  intro hs
  induction hs with
  | nil => intro _ _ c hc; simp at hc
  | cons a as ih =>
    intro us h c hc
    simp only [denoteLList] at h
    cases ha : denoteL st.ls a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : denoteLList st.ls as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact lview_isSome_of_denote ha
        · exact ih xs has c hc

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — intern a transient
level tree, by induction on `Level` (the recursion `internLevel` itself
takes). -/
@[spec] theorem internLevel_spec (s₀ : AState) (u : Level)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLevel u
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteL s'.store.ls h = some u⌝⦄ := by
  induction u generalizing s₀ with
  | zero =>
    mvcgen [internLevel, internLNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteLView, Arena.LStore.ViewOK, LNodeView.lchildren,
                 LNodeView.nchildren, Option.map_eq_some_iff])
  | succ u ih =>
    mvcgen [internLevel, ih, internLNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteLView, Arena.LStore.ViewOK, LNodeView.lchildren,
                 LNodeView.nchildren, Ext.trans, Option.map_eq_some_iff, denoteN_ext,
                 denoteL_ext])
  | max u v ihu ihv =>
    mvcgen [internLevel, ihu, ihv, internLNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteLView, Arena.LStore.ViewOK, LNodeView.lchildren,
                 LNodeView.nchildren, Ext.trans, opt2_eq_some_iff])
  | imax u v ihu ihv =>
    mvcgen [internLevel, ihu, ihv, internLNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteLView, Arena.LStore.ViewOK, LNodeView.lchildren,
                 LNodeView.nchildren, Ext.trans, opt2_eq_some_iff])
  | param n =>
    mvcgen [internLevel, internName_spec, internLNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteLView, Arena.LStore.ViewOK, LNodeView.lchildren,
                 LNodeView.nchildren, Ext.trans, Option.map_eq_some_iff, denoteN_ext,
                 denoteL_ext])

/-- con-leche: none — intern a list of transient levels, one handle each. -/
@[spec] theorem internLevelList_spec (s₀ : AState) (us : List Level)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLevelList us
    ⦃⇓? hs s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteLList s'.store.ls hs = some us⌝⦄ := by
  induction us generalizing s₀ with
  | nil =>
    mvcgen [internLevelList]
    all_goals (bridge_peel; subst_vars; grind [denoteLList, Ext.refl])
  | cons u us ih =>
    mvcgen [internLevelList, internLevel_spec, ih]
    all_goals (bridge_peel; subst_vars
               grind [denoteLList, Ext.trans, denoteL_ext, denoteLListE_ext])

/-- con-leche: none — intern a list of transient levels and hash-cons the
list node: what a `.const`'s universe arguments are. -/
@[spec] theorem internLevels_spec (s₀ : AState) (us : List Level)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLevels us
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteLs s'.store.lss h = some us⌝⦄ := by
  mvcgen [internLevels, internLevelList_spec, internLsNode_spec]
  all_goals (bridge_peel; subst_vars
             grind [denoteLsView, denoteLs, Arena.LsStore.ViewOK, Ext.trans,
               lview_isSome_of_denote, denoteLListE_ext, denoteLList])

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the memoised
`readNames`, whose recursion is on the list as `readNames`' is. -/
@[spec] theorem readNamesM_spec (s₀ : AState) (hs : List NIdx)
    (hc : ReadNCacheOK s₀.caches.readNC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readNamesM hs
    ⦃⇓? xs s' => ⌜s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readNC := s'.caches.readNC } ∧
        Frontend.denoteNList s₀.store.ns hs = some xs ∧
        ReadNCacheOK s'.caches.readNC s'.store⌝⦄ := by
  induction hs generalizing s₀ with
  | nil =>
    mvcgen [readNamesM]
    all_goals (bridge_peel; subst_vars
               grind [Frontend.denoteNList, ReadNCacheOK])
  | cons a as ih =>
    mvcgen [readNamesM, readNameM_spec, ih]
    all_goals (bridge_peel; subst_vars
               grind [Frontend.denoteNList, ReadNCacheOK])

#print axioms internLevel_spec
#print axioms internLevelList_spec
#print axioms internLevels_spec
#print axioms readNamesM_spec

end ConRon.Bridge
