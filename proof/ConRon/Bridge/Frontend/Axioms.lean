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

**Round two (task #97-P3-Frontend-2)** added the chunk tier, the preparation's
composition, the pure fold's stream ingredient and two of the three capstone
letters to the closed list; they are in their own sections below.
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

#print axioms ListRel.length_eq
#print axioms ListRel.mono
#print axioms IdTableRel.mono
#print axioms MapRel.mono
#print axioms MapRel.empty
#print axioms MapRel.insert
#print axioms IdTableRel.empty
#print axioms AM.pure_ok
#print axioms AM.fail_ok

/-! ## The declaration stream -/

#print axioms denoteDecls_length
#print axioms denoteDeclArray_empty
#print axioms denoteDeclArray_iff
#print axioms denoteDecls_append
#print axioms denoteDeclArray_append
#print axioms denoteCIList_ext
#print axioms denoteDecl_ext
#print axioms denoteDecls_ext
#print axioms denoteDeclArray_ext

/-! ## Transport across an append

The eighteen-clause relation and the seven-clause result relation both survive
an `intern`, which is what the streaming fold's induction rests on. -/

#print axioms ProjRecOwnerRel.ext
#print axioms MIndTypeRecRel.ext
#print axioms MIndCtorRecRel.ext
#print axioms MIndRecRecRel.ext
#print axioms BlockRecRel.ext
#print axioms StateDRel.ext
#print axioms ParseResultRel.ext

/-! ## The parse's frame -/

#print axioms ParseStep.refl
#print axioms ParseStep.trans
#print axioms ParseStep.of_eq

/-! ## The parse result -/

#print axioms ParseResultRel.ofState
#print axioms PersParseResult.ofState

/-! ## The three table reads, and the two list reads -/

#print axioms StateD_name_run
#print axioms StateD_level_run
#print axioms StateD_expr_run
#print axioms getDeclD_run
#print axioms readName_run
#print axioms readNames_mapM_run
#print axioms StateD_names_run

/-! ## The record headers (round two)

The three steps of items 5-6 that read the tables and nothing else; what is
left of those items is the three INTERNING entry parsers and the two that
write a `MapRel`. -/

#print axioms parsePwD_run
#print axioms parseCVD_run
#print axioms parseRuleD_run

/-! ## The readback -/

#print axioms DMemoOK.empty
#print axioms EMemoOK.empty

/-! ## The line's sum -/

#print axioms SumRel.inl_left
#print axioms SumRel.inr_left
#print axioms SumRel.of_state

/-! ## The streaming fold's escape hatch -/

#print axioms parseChunksC_eq
#print axioms parseChunks_eq

/-! ## The seam -/

#print axioms declineModeller_wf

/-! ## The pure fold's stream ingredient (round two) — CLOSED

`checkDeclsPure_thmDecl_const` and `no_False_theorem_accepted_pure` are the
one part of the capstone's path that is a con-leche-tier lemma, and they are
sorry-FREE: `annotateCore_const` is the annotation half and
`checkDeclsPure_prefix` replaces con-leche's cached-tier `PushChain` half
outright (`Bridge/Frontend/Capstone.lean` §2).  Task #97-P3-Frontend's sorry
list item 24 is therefore discharged, and the upstream ask is the RE-STATEMENT
(the prefix form), not the proof. -/

#print axioms annotateCore_const
#print axioms checkDeclsPure_prefix
#print axioms checkDeclsPure_thmDecl_const
#print axioms no_False_theorem_accepted_pure

/-! ## PROVED, but resting on an open leaf

The campaign's rule is that a result carrying `sorryAx` is not in the census
above, and these are not: each has a COMPLETE proof of its own and carries
`sorryAx` only through a lemma of the sorry list it cites.  They are printed
here because the distance between "proved" and "closed" is exactly what the
tier's remaining work is, and because the census is the only place a reader
can tell the two apart.

* the line and the chunk tier — `applyLine_run` rests on the three entry
  parsers and `processLineCoreD_run` (items 5-7, 9), and **everything below it
  is closed on `applyLine_run` and `StateD_init_run` alone** (items 16-18);
* the preparation and the prelude — `builtinPreludeE_run` on `parseBytes_run`,
  `preparePrelude_run` on `frontOf_run`/`hoistNatOpGround_run` (items 19-22);
* `FoldOK_post_parse` on `Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote`
  (the Checker tier's item 6) and nothing else. -/

#print axioms applyLine_run
#print axioms applyFinalLine_run
#print axioms feedChunk_run_le
#print axioms feedChunk_run
#print axioms chunkStep_run
#print axioms chunkFinish_run
#print axioms parseBytes_run
#print axioms parseChunksGo_run
#print axioms parseChunks_run
#print axioms builtinPreludeE_run
#print axioms preparePrelude_run
#print axioms mem_preparePrelude_denote
#print axioms FoldOK_post_parse

/-! ## The headlines, and the four named hypotheses

These five are still NOT closed — each reports `sorryAx`, because each rests
on a leaf of the sorry list (the memoised readback, the intern direction, the
`ExprOps` walks, the record-assembly steps and `processLineCoreD`'s six arms)
— and they are printed anyway, for the one thing the census is for: **none of
them names `CoreSpec`, `IndSpec`, `ModellerWF` or `ModellerRefines`.**  Those four are hypotheses of
the statements, not axioms of the environment, which is what makes "four named
hypotheses" a checkable claim rather than an editorial one
(`Bridge/Checker/Axioms.lean` makes the same point about its two).

When the tier closes, the expected reading of all five is
`[propext, Classical.choice, Quot.sound]` — con-leche's own census for
`ConLeche.no_False_declaration` (`tests/ConLecheTests/Axioms.lean:121`) and
the original campaign's for `conron.no_False_declaration`
(`RefineOld/Main.lean:775`). -/

#print axioms parseChunks_exact
#print axioms Arena.no_False_declaration
#print axioms Arena.no_False_declaration_prelude
#print axioms Arena.no_False_declaration_pipeline

end ConRon.Bridge.Frontend
