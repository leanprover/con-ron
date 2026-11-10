/-
# `ConRon.Bridge.ExprOps.Walks` — Theorem 1 for the two one-node readers

DESIGN §8.2's Theorem 1 at the two twins of `Arena/ExprOps.lean` that read
ONE node and do not recurse: `isForallE` (a tag read off the handle word) and
`binderPair?` (both tags, then the two binder projections).  Neither interns, so
the state is unchanged.  The scalar walks of the tier are in
`ExprOps/Guards.lean`, `ExprOps/Ranges.lean` and `ExprOps/Leaves.lean`.

## The proof

`isForallE_rel` is an equation between the twin and con-leche at a denoting
handle, by the tag's view.  `binderPair?_spec` is, per kind,
`sym only [bridge_grind, Expr.binderPair?, Expr.binderOf] => vcgen [binderPair?] <;> finish`:
`grind` reads the binder view of a `lam`- or `forallE`-tagged handle from
`Bridge/Grind.lean`'s guarded `view_of_viewBind` and the `DenoteView`
extractions, and declines by `binderPair?_{lam,pi}_none_{left,right}`, all
`grind_pattern … where guard` so that they fire only at the denotation
`binderPair?` is applied to.
-/
module

import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr
public import ConRon.Bridge.StateOK
public import ConRon.Arena.ExprOps
public import ConLeche.Verify.Knot

public section

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## The two one-node readers — `ExprOps.lean:836`, `:840`

`isForallE` is a tag read off the handle word; `binderPair?` tests both tags
and then takes the two binder projections (con-leche's binder-telescope
comparison `defeqBinders` descends with it).  No recursion, no fuel. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:771-774 isForallE — **THEOREM 1
for `isForallE`**: the tag of a denoting handle is `forallE` exactly when its
denotation is a ∀. -/
theorem isForallE_rel {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (he : denoteE st h = some e) : isForallE h = Expr.isForallE e := by
  obtain ⟨v, hv⟩ := denoteE_view he
  have htag := EStore.tagOf_of_view hv
  rw [denoteE_view_eq hwf hv] at he
  simp only [isForallE, htag]
  cases v <;>
    simp_all [ENodeView.tagOf, denoteEView, Expr.isForallE, opt2_eq_some_iff,
      opt3_eq_some_iff, Option.map_eq_some_iff, ETag.bvar, ETag.fvar, ETag.sort,
      ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit,
      ETag.proj] <;> grind

/-- con-leche: none — a handle that denotes a λ carries the `lam` tag. -/
theorem tag_lam_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx} {t b : Expr}
    (he : denoteE st h = some (.lam t b)) : h.tag = ETag.lam := by
  obtain ⟨v, hv⟩ := denoteE_view he
  have htag := EStore.tagOf_of_view hv
  rw [denoteE_view_eq hwf hv] at he
  cases v <;>
    simp_all [ENodeView.tagOf, denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
      Option.map_eq_some_iff]

/-- con-leche: none — a handle that denotes a ∀ carries the `forallE` tag. -/
theorem tag_forallE_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx} {t b : Expr}
    (he : denoteE st h = some (.forallE t b)) : h.tag = ETag.forallE := by
  obtain ⟨v, hv⟩ := denoteE_view he
  have htag := EStore.tagOf_of_view hv
  rw [denoteE_view_eq hwf hv] at he
  cases v <;>
    simp_all [ENodeView.tagOf, denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
      Option.map_eq_some_iff]

/-! ## `binderPair?`'s arms as `grind` lemmas

The declining arm knows only that one of the two tags is not the kind's; the
lemma for each side and kind is guarded by the subject's denotation, so that
it fires at the pair `binderPair?` is applied to and nowhere else (unguarded,
the multi-pattern pairs every denoting handle with every `binderPair?` term,
and each instance is a case split on a tag). -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:840-845 binderPair? — a handle
without the `lam` tag denotes no λ: `binderPair? true` declines whatever the
other side is.  Guarded: `ea` is the handle's denotation. -/
theorem binderPair?_lam_none_left {st : EStore} (hwf : StoreWF st) {a : EIdx} {ea eb : Expr}
    (htg : a.tag ≠ ETag.lam) (hea : denoteE st a = some ea) :
    Expr.binderPair? true ea eb = none := by
  cases ea <;> try rfl
  exact absurd (tag_lam_of_denote hwf hea) htg
grind_pattern [bridge_grind] binderPair?_lam_none_left =>
  denoteE st a, Expr.binderPair? true ea eb where
  guard denoteE st a = some ea

/-- con-leche: ConLeche/Kernel/ExprOps.lean:840-845 binderPair? —
`binderPair?_lam_none_left` on the right. -/
theorem binderPair?_lam_none_right {st : EStore} (hwf : StoreWF st) {b : EIdx} {ea eb : Expr}
    (htg : b.tag ≠ ETag.lam) (heb : denoteE st b = some eb) :
    Expr.binderPair? true ea eb = none := by
  cases eb <;> cases ea <;> try rfl
  exact absurd (tag_lam_of_denote hwf heb) htg
grind_pattern [bridge_grind] binderPair?_lam_none_right =>
  denoteE st b, Expr.binderPair? true ea eb where
  guard denoteE st b = some eb

/-- con-leche: ConLeche/Kernel/ExprOps.lean:840-845 binderPair? — a handle
without the `forallE` tag denotes no ∀: `binderPair? false` declines. -/
theorem binderPair?_pi_none_left {st : EStore} (hwf : StoreWF st) {a : EIdx} {ea eb : Expr}
    (htg : a.tag ≠ ETag.forallE) (hea : denoteE st a = some ea) :
    Expr.binderPair? false ea eb = none := by
  cases ea <;> try rfl
  exact absurd (tag_forallE_of_denote hwf hea) htg
grind_pattern [bridge_grind] binderPair?_pi_none_left =>
  denoteE st a, Expr.binderPair? false ea eb where
  guard denoteE st a = some ea

/-- con-leche: ConLeche/Kernel/ExprOps.lean:840-845 binderPair? —
`binderPair?_pi_none_left` on the right. -/
theorem binderPair?_pi_none_right {st : EStore} (hwf : StoreWF st) {b : EIdx} {ea eb : Expr}
    (htg : b.tag ≠ ETag.forallE) (heb : denoteE st b = some eb) :
    Expr.binderPair? false ea eb = none := by
  cases eb <;> cases ea <;> try rfl
  exact absurd (tag_forallE_of_denote hwf heb) htg
grind_pattern [bridge_grind] binderPair?_pi_none_right =>
  denoteE st b, Expr.binderPair? false ea eb where
  guard denoteE st b = some eb

/-- con-leche: ConLeche/Kernel/ExprOps.lean:840-845 binderPair? — **THEOREM 1
for `binderPair?`**: the state does not move; `none` exactly when con-leche's
`binderPair?` of the two denotations is `none`, and otherwise the two handles
denote the binders of the kind (`Expr.binderOf`) of the four answered
handles' denotations.  Both arms are equations over the denotation terms
(`opt2`): no witness to name.  One `sym`/`vcgen`/`finish` per kind. -/
theorem binderPair?_spec (lam : Bool) (s₀ : AState) (a b : EIdx) (hok : StateOK s₀)
    (_ha : (denoteE s₀.store a).isSome = true)
    (_hb : (denoteE s₀.store b).isSome = true) :
    ⦃fun s => s = s₀⦄ binderPair? lam a b
    ⦃fun r s' => s' = s₀ ∧
        match r with
        | none => opt2 (Expr.binderPair? lam) (denoteE s₀.store a) (denoteE s₀.store b)
            = some none
        | some (t₁, b₁, t₂, b₂) =>
            denoteE s₀.store a = opt2 (Expr.binderOf lam) (denoteE s₀.store t₁)
              (denoteE s₀.store b₁) ∧
            denoteE s₀.store b = opt2 (Expr.binderOf lam) (denoteE s₀.store t₂)
              (denoteE s₀.store b₂); ⊤⦄ := by
  cases lam
  · sym only [bridge_grind, Expr.binderPair?, Expr.binderOf] =>
      vcgen [binderPair?] <;> finish
  · sym only [bridge_grind, Expr.binderPair?, Expr.binderOf] =>
      vcgen [binderPair?] <;> finish

/-! ## The axiom check -/

#print axioms isForallE_rel
#print axioms tag_lam_of_denote
#print axioms tag_forallE_of_denote
#print axioms binderPair?_spec

end ConRon.Bridge.ExprOps
