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
point about its two).  The capstones carried `sorryAx` until the tier closed
and are printed in the last sections below; they read Lean's own three now
(task #97-MILESTONE).  **Task #105**: the original campaign's `ModellerWF`/
`ModellerRefines` are gone with the in-process modeller — the uniform
installer needs no analogous premise.

**Round two (task #97-P3-Frontend-2)** added the chunk tier, the preparation's
composition, the pure fold's stream ingredient and two of the three capstone
letters to the closed list; they are in their own sections below.

**Round four** adds item 5 in full (the three table entries), `blockRecOf_run`
of item 6, and four of `ProjRec.lean`'s nine — `isProjIotaName_run`,
`projIotaLevel_run`, `stripPisAll_run`, `mkLams_run`.  Its two findings are
statement defects, not proof gaps: finding 15 (`projIotaLevel_run`'s frame was
`s' = s` at a walk that interns `Eq`) is REPAIRED and closed here; finding 16
(`IConstantInfo.toConstantVal` and `IDeclaration.names` are not exact at a
`.projInfo` without `IProjTableOK`) is reported and left open, because the
repair adds a hypothesis and that is the maintainer's call.

**Round six** makes the intern family scratch-agnostic (the `IStepS` face of
`Bridge/Frontend/Shared.lean`, with the `IStep` one as a corollary through
`Bridge/Frontend/Rel.lean`'s `Pers…_of_denote`) and closes the two gray-memo
walks the tier still owed: `occursConstFast_run` — whose memo turns out to be
BLACK-only, so it needed no rank — and `usedConsts_run` with its three helpers,
whose memo IS gray and whose two sets are keyed differently on the two sides
(handle against `Expr`), which is where `denoteE_inj` earns its keep.
`toConstantVal_type_run` is the half of `toConstantVal` that needs no name
clause, stated so that `usedConsts_run` does not have to assume one.

**Round five** repairs finding 16 and closes five more.  The repair is two
things, and the census records both: the frame half is a CORRECTION (five
statements said `s' = s` of a run that interns `Sort 1` at a `.projInfo`) and
the name half is a STRENGTHENING of the seam's promise plus a new clause on
`StateDRel`/`ParseResultRel` — `projNamed`, the move `Bridge/StateOK.lean`'s
`IFEnvOK.proj` made one module over, for exactly the same reason.  What closes
on top of it is `noteDecl_run`/`pushDecl_run` (item 6) and the prelude's front,
`preludeKey_run`/`pick_denote`/`frontOf_run` (item 20), with the new
vocabulary and its name equations below.

It also states the two con-leche-tier facts `occursConstFast_run` needs and
con-leche does not have (`Bridge/Frontend/ProjRec.lean`'s `clOccursConstB_eq`
and `clOccursConstGo_eq`, §5's finding-6 shape).  Their corollary
`clOccursConstFast_eq` is proved on top of them and therefore carried
`sorryAx` until task #97-T1-OCC proved the two here (see the last section
below).

**Round three** adds the INTERN direction (item 2) and the seam (item 8).  Two
of the four named hypotheses are therefore no longer only hypotheses:
`ModellerWF` and `ModellerRefines` hold of the modeller the driver actually
runs, as theorems — `inProcessModeller_wf` and `inProcessModeller_refines`
below — and they still do not appear in any capstone's axiom list, because the
capstones are stated at an arbitrary `Modeller`.
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
#print axioms ListRel.mono
#print axioms IdTableRel.mono
#print axioms MapRel.mono
#print axioms MapRel.empty
#print axioms MapRel.insert
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
#print axioms denoteCIList_ext
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
#print axioms ParseStep.of_eq
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

The three steps of items 5-6 that read the tables and nothing else; what is
left of those items is the three INTERNING entry parsers and the two that
write a `MapRel`. -/

#print axioms parsePwD_run
#print axioms parseCVD_run
#print axioms parseRuleD_run

/-! ## The readback (round 2) — CLOSED

Item 1 in full: the ten-arm fuel induction both ways (`denoteEGo_spec_le` and
`denoteEGo_isSome`), the record layers over it, and the two `AM` faces.  Item
3 with them: `ctxOf_eq_of_rel`, over `nameHandle?`'s two exactness halves. -/

#print axioms DMemoOK.empty
#print axioms DMemoOK.insert
#print axioms EMemoOK.empty
#print axioms denoteEGo_spec
#print axioms denoteEShared_eq
#print axioms denoteEGo_isSome
#print axioms denoteEShared_isSome
#print axioms denoteEShared_eq_denoteE

/-! ## The intern direction (round 3) — CLOSED

Item 2 in full: the ten-arm structural recursion over `ConLeche.Expr` with the
intern memo carried (`internExprGo_istep`) and the twelve record layers over
it.  `IStep` is the frame every one of them answers in — `StateOK`, `Ext`, the
closed scratch tier and the three untouched state fields — and
`IStep.toParse` is the one line that turns it into the tier's `ParseStep`.

**Round 2's finding 13 was wrong** and this round withdraws it:
`internLevel_spec`, `internLevelList_spec` and `internLevels_spec` were not
missing at all — they have been in `Bridge/SpecsL.lean` since task #97-P3-0
(that module's own note says it holds "the four `@[spec]` theorems of
`Monad.lean` that `Bridge/Specs.lean` does not carry"), and the only thing
between this tier and them was an import line. -/

#print axioms EMemoOK.mono
#print axioms EMemoOK.insert
#print axioms IStep.trans
#print axioms IStep.toParse
#print axioms EStore.scratchOn_intern
#print axioms internE_scratchOn
#print axioms internE_istep
#print axioms internName_istep
#print axioms internNNode_istep
#print axioms internDecls_istep

/-! ## General readback helpers (rounds 3 and 4)

**Task #105**: round 3's seam section named `inProcessModeller`'s two
promises (`ctxOf_eq_of_rel`, `denoteBlockRec_eq_of_rel`, `internDecls_istep`)
and round 4's recogniser/level-read section named `isProjIotaName_run`/
`projIotaLevel_run` — all `Bridge/Frontend/ProjRec.lean`, deleted with the
modeller and the projection rewrite.  What survives from that file is the
handful of general-purpose readback helpers it happened to define alongside
them (`view_run`, `viewN_run`, `piResultD_run`, `readLevel_run`,
`nsWF_of_StateOK`, `denoteN_str_inv`, `view_str_of_denoteN`), relocated into
`Bridge/Frontend/{Rel,Lines}.lean`. -/

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
`singleton` and `empty`, `MapRel.empty`, and — the `PersStateD` half —
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

/-! ## The parsed block, resolved (round 4) -/

#print axioms parseRules_run

/-! ## The line's sum -/

#print axioms SumRel.inl_left
#print axioms SumRel.of_state

/-! ## The streaming fold's escape hatch -/

#print axioms parseChunksC_eq
#print axioms parseChunks_eq

/-! ## The seam -/


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
#print axioms MapRel.getElem?_rel
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

/-! ## Round eight — the projection rewrite and owner census, DELETED

**Task #105**: `Bridge/Frontend/{ProjRec,ProjRecOwners,ProjRecValue,
Scratch}.lean` are gone with the in-process modeller and the projection
rewrite; every result the two "round eight" sections here used to name
(`projRecOwners_run`, `projRecValue_run`, `projRewriteD_run`, the
scratch-frame family) went with them.  `ReadCachesOK` itself survives —
`Bridge/Frontend/Rel.lean` keeps the structure and its two lemmas because
`proof/ConRon/Capstone.lean` (a later task's file) still cites
`ReadCachesOK.ofEmpty` — but nothing in this tier threads it any more, since
nothing downstream of the parse reads a per-declaration cache. -/

#print axioms ReadCachesOK.step
#print axioms ReadCachesOK.ofEmpty

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

/-! ## Task #97-T1-OCC — the occurrence walks, CLOSED

`Bridge/Frontend/ProjRec.lean`'s two con-leche-tier lemmas, proved here: the
budgeted walk by induction with the budget generalised, the memoised one
from the memo invariant `clOccursMemoInv`.  With them every declaration this
census prints — the "resting on an open leaf" list above and the headlines
below included — reads at Lean's own three or fewer; the section titles
record where each stood when it was written. -/


/-! ## The headlines, and the four named hypotheses

These five reported `sorryAx` while they rested on leaves of the sorry list
(the memoised readback, the intern direction, the `ExprOps` walks, the
record-assembly steps and `processLineCoreD`'s six arms); those are closed,
and the five are printed for the one thing the census is for: **none of
them names `CoreSpec`, `IndSpec`, `ModellerWF` or `ModellerRefines`.**  Those four are hypotheses of
the statements, not axioms of the environment, which is what makes "four named
hypotheses" a checkable claim rather than an editorial one
(`Bridge/Checker/Axioms.lean` makes the same point about its two).

With the tier closed, the reading of all five is
`[propext, Classical.choice, Quot.sound]` — con-leche's own census for
`ConLeche.no_False_declaration` (`tests/ConLecheTests/Axioms.lean:121`) and
the original campaign's for `conron.no_False_declaration`
(`RefineOld/Main.lean:775`). -/


/-! ## What the third letter no longer carries

Round 2 assembled `Arena.no_False_declaration_pipeline` on a named hypothesis
`InternAllPinsFrame`, standing in for the one conjunct
`Bridge/Checker/Pins.lean`'s `internAllPins_run` did not state.  Task
#97-P3-Checker-2 landed the strengthening (`s'.caches = s.caches ∧ s'.memos =
s.memos`), so round 3 deleted the definition and the hypothesis: the letter's
hypotheses are again `CoreSpec`, `IndSpec` and the prelude gate, and nothing
else.  Task #98-HEADLINE dropped the prelude gate too (`builtinPreludeE_run`
is parametric in the bytes): the letter takes `CoreSpec` and `IndSpec`. -/

end ConRon.Bridge.Frontend
