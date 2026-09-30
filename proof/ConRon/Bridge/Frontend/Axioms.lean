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

**The named hypotheses are hypotheses, not axioms.**  `CoreSpec` and
`IndSpec` appear in the capstone's STATEMENT; `#print axioms` on it therefore
names neither, which is what makes "two named hypotheses" a checkable claim
rather than an editorial one (`Bridge/Checker/Axioms.lean` makes the same
point about its two).  The capstones are printed in the last sections below.
-/
import ConRon.Bridge.Frontend.Capstone

namespace ConRon.Bridge.Frontend

/-! ## The generic shapes -/

#print axioms OptRel.isSome
#print axioms OptRel.some_left
#print axioms OptRel.none_left
#print axioms IdTableRel.bound
#print axioms IdTableRel.singleton
#print axioms IdTableRel.insert

#print axioms ciName_denote_proj
#print axioms ciName_denote_of
#print axioms ciNames_denote
#print axioms declNames_denote
#print axioms IProjNamed.mono
#print axioms CIProjNamed.mono
#print axioms CIProjNamed.of_ne
#print axioms CIProjNamed.of_proj
#print axioms DeclProjNamed.mono
#print axioms DeclProjNamed.of_indDecl
#print axioms DeclsProjNamed.mono
#print axioms DeclsProjNamed.empty
#print axioms DeclsProjNamed.push

#print axioms ListRel.length_eq
#print axioms IdTableRel.mono
#print axioms IdTableRel.empty
#print axioms AM.get_ok
#print axioms AM.pure_ok
#print axioms AM.fail_ok
#print axioms scratchOn_nested
#print axioms PersN_of_view
#print axioms PersL_of_view
#print axioms PersE_of_view

/-! ## The declaration stream -/

#print axioms denoteDecls_length
#print axioms denoteDeclArray_empty
#print axioms denoteDeclArray_iff
#print axioms denoteDecls_append
#print axioms denoteDeclArray_append
#print axioms denoteCIList_mono
#print axioms denoteDecl_ext
#print axioms denoteDecls_ext
#print axioms denoteDeclArray_ext

/-! ## Transport across an append

The eighteen-clause relation and the seven-clause result relation both survive
an `intern`, which is what the streaming fold's induction rests on. -/

#print axioms StateDRel.ext

/-! ## The parse's frame -/

#print axioms ParseStep.refl
#print axioms ParseStep.trans
#print axioms ParseStep.of_caches

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

The three steps of items 5-6 that read the tables and nothing else. -/

#print axioms parsePwD_run
#print axioms parseCVD_run
#print axioms parseRuleD_run

/-! ## The intern memo's invariant, empty -/

#print axioms EMemoOK.empty

/-! ## The intern direction (round 3) — CLOSED

Item 2 in full: the ten-arm structural recursion over `ConLeche.Expr` with the
intern memo carried (`internExprGo_istep`) and the twelve record layers over
it.  `IStep` is the frame every one of them answers in — `StateOK`, `Ext`, the
closed scratch tier and the three untouched state fields — and
`IStep.toParse` is the one line that turns it into the tier's `ParseStep`. -/

#print axioms EMemoOK.mono
#print axioms EMemoOK.insert
#print axioms IStep.trans
#print axioms IStep.toParse
#print axioms EStore.scratchOn_intern
#print axioms internE_scratchOn
#print axioms internE_istep
#print axioms internNNode_istep

/-! ## General readback helpers -/

#print axioms viewN_run
#print axioms readLevel_run
#print axioms view_run
#print axioms piResultD_run
#print axioms nsWF_of_StateOK
#print axioms denoteN_str_inv
#print axioms view_str_of_denoteN

/-! ## The parse's initial state (round 2) — CLOSED

`StateD_init_run` is the base case of the streaming fold's induction, and
round 2 closed it: the two intern specs through `AM.of_run`, `IdTableRel`'s
`singleton` and `empty`, and — the `PersStateD` half —
`PersN_of_view` / `PersL_of_view`. -/

#print axioms StateD_init_run

/-! ## The three table entries (round 4) — item 5 CLOSED

The rebinding guards, the `PersStateD` half of a table write, and the three
entry parsers: `parseNameEntryD_run`, `parseLevelEntryD_run` and — the tier's
real work, ten constructors — `parseExprEntryD_run`. -/

#print axioms freshName_run
#print axioms freshLevel_run
#print axioms freshExpr_run
#print axioms PersStateD.insertName
#print axioms PersStateD.insertLevel
#print axioms PersStateD.insertExpr
#print axioms denoteLList_mem
#print axioms StateD_levels_run
#print axioms internLNode_istep
#print axioms internLsNode_istep
#print axioms parseNameEntryD_run
#print axioms parseLevelEntryD_run
#print axioms parseExprEntryD_run

/-! ## The recursor rule list -/

#print axioms parseRules_run

/-! ## The line's sum -/

#print axioms SumRel.inl_left
#print axioms SumRel.of_state

/-! ## The streaming fold's escape hatch -/

#print axioms parseChunksC_eq
#print axioms parseChunks_eq

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

/-! ## Round seven — `validateIndD_run`, CLOSED

The inductive record's READ half, over its two loops: `forIn_sim` relates a
read-only `AM` loop to con-leche's `Except String` one through an arbitrary
state relation (the two `do` elaborators build different loop states), and
`denoteN_inj` is load-bearing three times — the duplicate-constructor guard
(`ListRel.nodup_iff_denoteN`), the constructor index (`ctorIx_fold_rel`) and
the `induct`/`T.rec` comparisons. -/

#print axioms except_ok_bind
#print axioms except_bind_ex
#print axioms ListRel.refl_eq
#print axioms readName_bind
#print axioms ListRel.singleton_right
#print axioms ListRel.singleton_left
#print axioms forIn_sim
#print axioms mapM_sim
#print axioms storeFuel_run
#print axioms indPiTeleLen_run
#print axioms piSortTeleLen?_run
#print axioms ListRel.mem_iff_denoteN
#print axioms ListRel.nodup_iff_denoteN
#print axioms ListRel.flatten
#print axioms ListRel.zip
#print axioms ctorIx_fold_rel
#print axioms VInv.nil
#print axioms VInv.inv
#print axioms VInv.res
#print axioms validateIndD_run'

/-! ## Round seven, continued — the install half, the line, the hoist, CLOSED

The machinery `installIndD_run`, `processLineCoreD_run`,
`hoistNatOpGround_run` and `projRewriteD_run` stand on.  Everything here is
at Lean's own three. -/

#print axioms ListRel.append
#print axioms denoteCIList_of_listRel
#print axioms denoteCaps_default
#print axioms pushDecl_built_run
#print axioms reorder_toList
#print axioms denoteDecls_filterMap
#print axioms movedNames_toList
#print axioms denoteNList_append'
#print axioms denoteNList_flatMap_names
#print axioms applyHoist_run

/-! ## Round eight — the target map, CLOSED

`hoistTargets_run` against the round-8 twin (`hoistClosure`'s fuel counts
marked records), and with it `hoistNatOpGround_run`, which rested on nothing
else.  Everything here is at Lean's own three. -/

#print axioms forIn_id_yield
#print axioms loop_id_unfold
#print axioms IdxRel.mono
#print axioms pushOne_sim
#print axioms arr_rev_cons
#print axioms loop_drop
#print axioms declAt_denote
#print axioms hoistClosure_sim
#print axioms isNatOpRecord_run
#print axioms hoistDeps_sim
#print axioms hoistTargetsGo_sim
#print axioms forIn_id_bind_yield
#print axioms forIn_id_ite_yield
#print axioms loop_congr
#print axioms clHoistTargets_eq
#print axioms IdxRel.insertOne
#print axioms insertNames_sim
#print axioms nameIndex_sim
#print axioms nameIndex_lt
#print axioms hoistTargets_run
#print axioms hoistNatOpGround_run

/-! ## PROVED, and once resting on an open leaf

When this section was written, each result below had a COMPLETE proof of its
own and carried `sorryAx` only through a lemma of the sorry list it cites; it
was printed here because the distance between "proved" and "closed" was
exactly what the tier's remaining work was.  Every leaf it names is closed
since, so these read Lean's own three now; the list is kept as the record of
what rested on what.

* the line and the chunk tier — `applyLine_run` rests on the three entry
  parsers and `processLineCoreD_run` (items 5-7, 9), and **everything below it
  is closed on `applyLine_run` and `StateD_init_run` alone** (items 16-18);
* the preparation and the prelude — `builtinPreludeE_run` on `parseBytes_run`,
  `preparePrelude_run` on `frontOf_run`/`hoistNatOpGround_run` (items 19-22);
* `FoldOK_post_parse` on `Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote`
  (the Checker tier's item 6) and nothing else;
* round 7's skeletons — `processLineCoreD_run`, `installIndD_run` and
  `registerProjOwners_run` rest on `projRecOwners_run`, which since round 8 is
  closed modulo `occursConstFast_run`'s two con-leche-tier asks and nothing
  else; `FoldOK_post_pins` on the Checker tier's `internAllPins_run`.
  (`hoistNatOpGround_run` and `projRewriteD_run` left this list in round 8.) -/

#print axioms installIndD_run
#print axioms processLineCoreD_run
#print axioms applyDeclD_run
#print axioms applyLine_run
#print axioms applyFinalLine_run
#print axioms feedChunk_run_le
#print axioms feedChunk_run
#print axioms chunkStep_run
#print axioms chunkFinish_run
#print axioms parseBytes_run
#print axioms parseChunksGo_run
#print axioms toConstantVal_run
#print axioms toConstantVal_type_run
#print axioms pushDecl_run
#print axioms denoteNList_contains
#print axioms declares_denote
#print axioms denoteDecls_getElem?
#print axioms denoteDecls_eraseIdx
#print axioms denoteDecls_findIdx
#print axioms mem_eraseIdxIfInBounds
#print axioms preludeKey_run
#print axioms pick_denote
#print axioms frontOf_run
#print axioms UCSeen.contains
#print axioms UCSeen.insert
#print axioms UCSeen.mono
#print axioms denoteNList_snoc
#print axioms usedConstsGo_run
#print axioms usedConstsRules_run
#print axioms ucBlockStep_denote
#print axioms usedConstsBlock_run
#print axioms usedConsts_run

#print axioms parseChunks_run
#print axioms builtinPreludeE_run
#print axioms preparePrelude_run
#print axioms FoldOK_of_start

/-! ## The headlines, and the two named hypotheses

These five reported `sorryAx` while they rested on leaves of the sorry list
(the intern direction, the `ExprOps` walks, the
record-assembly steps and `processLineCoreD`'s six arms); those are closed,
and the five are printed for the one thing the census is for: **none of
them names `CoreSpec` or `IndSpec`.**  Those two are hypotheses of
the statements, not axioms of the environment, which is what makes "two named
hypotheses" a checkable claim rather than an editorial one
(`Bridge/Checker/Axioms.lean` makes the same point about its two).

With the tier closed, the reading of all five is
`[propext, Classical.choice, Quot.sound]` — con-leche's own census for
`ConLeche.no_False_declaration` (`tests/ConLecheTests/Axioms.lean:121`) and
the original campaign's for `conron.no_False_declaration`
(`RefineOld/Main.lean:775`). -/


end ConRon.Bridge.Frontend
