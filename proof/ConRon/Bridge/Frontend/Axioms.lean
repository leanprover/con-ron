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
`clOccursConstFast_eq` is proved on top of them and therefore carries
`sorryAx`, so it is NOT in the list below — which is the rule working as
intended: the census lists what is proved, and that one is proved *modulo an
ask of con-leche*.

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
#print axioms OptRel.some_right
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
#print axioms denoteEListGo_spec
#print axioms denoteCVGo_spec
#print axioms denoteFireGo_spec
#print axioms denoteRuleGo_spec
#print axioms denoteRulesGo_spec
#print axioms denoteProjTableGo_spec
#print axioms denoteCIGo_spec
#print axioms denoteCIListGo_spec
#print axioms denoteEShared_eq
#print axioms denoteEGo_isSome
#print axioms denoteEShared_isSome
#print axioms denoteEShared_eq_denoteE
#print axioms readExpr_run
#print axioms readCIList_run
#print axioms denoteBlockRec_eq_of_rel
#print axioms nameHandle?_sound
#print axioms nameHandle?_isSome
#print axioms ctxOf_eq_of_rel

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
#print axioms IStep.refl
#print axioms IStep.trans
#print axioms IStep.toParse
#print axioms EStore.scratchOn_intern
#print axioms AM.set_state_ok
#print axioms internE_scratchOn
#print axioms internE_istep
#print axioms internName_istep
#print axioms internLevel_istep
#print axioms internLevels_istep
#print axioms internNameList_istep
#print axioms internLevelList_istep
#print axioms internExprGo_istep
#print axioms internExprList_istep
#print axioms internExpr_run
#print axioms internNNode_istep
#print axioms projTableName_istep
#print axioms internCV_istep
#print axioms internFire_istep
#print axioms internRule_istep
#print axioms internRules_istep
#print axioms internCaps_istep
#print axioms internProjTable_istep
#print axioms internCI_istep
#print axioms internCIList_istep
#print axioms internDecl_istep
#print axioms internDecls_istep
#print axioms internDecls_run

/-! ## The seam (round 3) — CLOSED

Item 8.  `inProcessModeller` delegates to con-leche's own generator, so both
promises are theorems about the readback and the intern rather than
assumptions about a foreign program: `ctxOf_eq_of_rel` and
`denoteBlockRec_eq_of_rel` on the way in, `internDecls_istep` on the way out.

Round 3's finding 14 is what made them provable: both promises were stated at
an ARBITRARY start state and concluded `StateOK s'`, which is false of a
modeller that returns `[]` at a state whose store is not well formed.  They
now take `StateOK s` and the closed scratch tier, which every call site
has. -/

#print axioms inProcessModeller_wf
#print axioms inProcessModeller_refines

/-! ## The projection artifact's name and level (rounds 3 and 4)

Round 4 adds the recogniser (`isProjIotaName_run`), the `Eq`-level read
(`projIotaLevel_run` — restated over `ParseStep` and as a two-sided `OptRel`,
finding 15) and the two telescope peels the rewrite is built out of. -/

#print axioms viewN_run
#print axioms viewLs_run
#print axioms readLevel_run
#print axioms view_run
#print axioms piResult_run
#print axioms getAppFn_run
#print axioms nsWF_of_StateOK
#print axioms denoteN_str_inv
#print axioms view_str_of_denoteN
#print axioms projIotaName_run
#print axioms clIsProjIotaName_false
#print axioms isProjIotaName_run
#print axioms denoteLList_length
#print axioms denoteLList_singleton
#print axioms clProjIotaLevel_eq
#print axioms projIotaLevel_none
#print axioms projIotaLevel_run

/-! ## The rewrite's two telescope peels (round 4) -/

#print axioms stripPisAll_stop
#print axioms stripPisAll_run
#print axioms mkLams_run

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
#print axioms blockRecOf_run

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

/-! ## Round seven — `validateIndD_run`, CLOSED

The inductive record's READ half, over its two loops: `forIn_sim` relates a
read-only `AM` loop to con-leche's `Except String` one through an arbitrary
state relation (the two `do` elaborators build different loop states), and
`denoteN_inj` is load-bearing three times — the duplicate-constructor guard
(`ListRel.nodup_iff_denoteN`), the constructor index (`ctorIx_fold_rel`) and
the `induct`/`T.rec` comparisons. -/

#print axioms except_ok_bind
#print axioms except_bind_of
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
#print axioms validateIndD_run

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
#print axioms toConstantVal_run
#print axioms toConstantVal_type_run
#print axioms noteBlock_run
#print axioms noteFold_rel
#print axioms noteDecl_run
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
#print axioms OccSeen.insert
#print axioms occursConstGo_run

#print axioms parseChunks_run
#print axioms builtinPreludeE_run
#print axioms preparePrelude_run
#print axioms mem_preparePrelude_denote
#print axioms FoldOK_of_start
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

/-! ## What the third letter no longer carries

Round 2 assembled `Arena.no_False_declaration_pipeline` on a named hypothesis
`InternAllPinsFrame`, standing in for the one conjunct
`Bridge/Checker/Pins.lean`'s `internAllPins_run` did not state.  Task
#97-P3-Checker-2 landed the strengthening (`s'.caches = s.caches ∧ s'.memos =
s.memos`), so round 3 deleted the definition and the hypothesis: the letter's
hypotheses are again `CoreSpec`, `IndSpec` and the prelude gate, and nothing
else. -/

end ConRon.Bridge.Frontend
