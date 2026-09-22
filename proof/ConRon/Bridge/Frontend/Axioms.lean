/-
# `ConRon.Bridge.Frontend.Axioms` — the frontend tier's trust census

`#print axioms` on every closed result of `Bridge/Frontend/**`, in the shape
`Bridge/Axioms.lean` and `Bridge/Checker/Axioms.lean` use.  The rule of the
campaign: **a result that carries `sorryAx` is not in this file**, so the
census is a list of what is actually proved rather than a list of what is
stated.

Every one below is `[propext, Classical.choice, Quot.sound]` — Lean's own
three, which come in through `Std.HashMap`, `Classical` in `Option`'s lemmas
and `Quot` in `String`, and which every tier of this repository already
carries.  No `sorryAx`, no `bv_decide` axiom.

**The four named hypotheses are hypotheses, not axioms.**  `CoreSpec`,
`IndSpec`, `ModellerWF` and `ModellerRefines` appear in the capstone's
STATEMENT; `#print axioms` on it therefore names none of them, which is what
makes "four named hypotheses" a checkable claim rather than an editorial one
(`Bridge/Checker/Axioms.lean` makes the same point about its two).  The
capstone itself carries `sorryAx` today and so is not in the list below; when
it closes, its census belongs here.
-/
import ConRon.Bridge.Frontend.Capstone

namespace ConRon.Bridge.Frontend

/-! ## The generic shapes -/

#print axioms OptRel.isSome
#print axioms OptRel.some_left
#print axioms OptRel.some_right
#print axioms OptRel.none_left
#print axioms IdTableRel.bound
#print axioms IdTableRel.singleton
#print axioms IdTableRel.insert

/-! ## The declaration stream -/

#print axioms denoteDecls_length

/-! ## The parse's frame -/

#print axioms ParseStep.refl
#print axioms ParseStep.trans
#print axioms ParseStep.of_eq

/-! ## The parse result -/

#print axioms ParseResultRel.ofState
#print axioms PersParseResult.ofState

/-! ## The three table reads -/

#print axioms StateD_name_run
#print axioms StateD_level_run
#print axioms StateD_expr_run
#print axioms getDeclD_run

/-! ## The readback -/

#print axioms DMemoOK.empty
#print axioms EMemoOK.empty

/-! ## The seam -/

#print axioms declineModeller_wf

/-! ## The headlines, and the four named hypotheses

These five are NOT closed — each reports `sorryAx` — and they are printed
anyway, for the one thing the census is for: **none of them names `CoreSpec`,
`IndSpec`, `ModellerWF` or `ModellerRefines`.**  Those four are hypotheses of
the statements, not axioms of the environment, which is what makes "four named
hypotheses" a checkable claim rather than an editorial one
(`Bridge/Checker/Axioms.lean` makes the same point about its two).

When the tier closes, the expected reading of all five is
`[propext, Classical.choice, Quot.sound]` — con-leche's own census for
`ConLeche.no_False_declaration` (`tests/ConLecheTests/Axioms.lean:121`) and
the original campaign's for `conron.no_False_declaration`
(`RefineOld/Main.lean:775`). -/

#print axioms parseChunks_exact
#print axioms preparePrelude_run
#print axioms Arena.no_False_declaration
#print axioms Arena.no_False_declaration_prelude
#print axioms Arena.no_False_declaration_pipeline

end ConRon.Bridge.Frontend
