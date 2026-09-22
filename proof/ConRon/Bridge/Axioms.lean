/-
# `ConRon.Bridge.Axioms` — the trust census of Theorem 1's spec layer

DESIGN §3.7 / OVERVIEW §8: every closed result of this library must reach
`[propext, Classical.choice, Quot.sound]` and **nothing else** — in
particular no `sorryAx` (which is what makes "closed" mean closed) and no
`…_native.bv_decide.ax_…` (task #97a's reason for packing the handle word
with `*`/`/`/`%` instead of `<<<`/`&&&`).

The three standard axioms come in through `Std.HashMap`, `Classical` in
`Option`'s lemmas and `Quot` in `String`; they are the same three every tier
of this repository already carries.

This module is the counterpart of `Spike/Axioms.lean` (task #97s).  It prints,
not asserts: the gate is reading the output, and a `sorryAx` in any line is a
failure of the task rather than of the build.
-/
import ConRon.Bridge.Specs
import ConRon.Bridge.SpecsL
import ConRon.Bridge.StoreBM
import ConRon.Bridge.ExprOps.Inst1

namespace ConRon.Bridge

/-! ## The store obligations this phase closed -/

#print axioms EStore.internName_spec
#print axioms EStore.internLevel_spec
#print axioms EStore.internLevels_spec
#print axioms EStore.internBindI_spec
#print axioms EStore.viewBM_intern_mono

/-! ## The denotation calculus -/

#print axioms AM.of_run
#print axioms denoteE_view_eq
#print axioms denote_app_inv
#print axioms denote_leaf_of_tag
#print axioms EStore.tagOf_of_view
#print axioms view_of_viewApp
#print axioms view_of_viewBindI
#print axioms view_of_viewBindI_wf
#print axioms bmOK_of_viewBindI
#print axioms denoteEView_ext
#print axioms denoteCI_ext

/-! ## The answer relations -/

#print axioms RelE.retarget
#print axioms RelE.app
#print axioms RelE.lam
#print axioms RelE.letE
#print axioms RelE.proj
#print axioms RelE.of_view
#print axioms RelEO.ext
#print axioms RelEL.ext
#print axioms viewOK_eBindView

/-! ## The state invariant -/

#print axioms MemoOK.get
#print axioms MemoOK.insert
#print axioms MemoVOK.insert
#print axioms MemoLOK.insert
#print axioms MemoLsOK.insert
#print axioms CacheOK.mono
#print axioms CacheOK.of_empty
#print axioms PinsOK.mono
#print axioms IFEnvOK.mono
#print axioms IFEnvOK.miss
#print axioms CheckOK.mono

/-! ## The `@[spec]` layer -/

#print axioms fail_spec
#print axioms view_spec
#print axioms derivedE_spec
#print axioms internE_spec
#print axioms internAppE_spec
#print axioms internLamIE_spec
#print axioms internBindIE_spec
#print axioms internBindIE_spec'
#print axioms internRebuilt_spec
#print axioms internRebuiltBindI_spec'
#print axioms viewApp_spec
#print axioms viewBindI_spec
#print axioms viewBM_spec
#print axioms readName_spec
#print axioms readNames_spec
#print axioms internName_spec
#print axioms internNNode_spec
#print axioms internLNode_spec
#print axioms internLsNode_spec
#print axioms readLevelM_spec
#print axioms readNameM_spec
#print axioms readLevelsM_spec
#print axioms inst1Get_spec
#print axioms inst1Set_spec
#print axioms inst1Clear_spec
#print axioms instLPClear_spec
#print axioms instLPLSet_spec
#print axioms instLPLsSet_spec
#print axioms bvarBSet_spec
#print axioms fvarBSet_spec
#print axioms instListCutoff_spec
#print axioms internLevel_spec
#print axioms internLevelList_spec
#print axioms internLevels_spec
#print axioms readNamesM_spec
#print axioms flushCaches_spec
#print axioms dropScratch_spec
#print axioms enterScratch_spec
#print axioms pinAt_spec
#print axioms pinReserved_spec
#print axioms pinSortOne_spec

/-! ## The `ExprOps` tier's exemplar — **closed** (task #97-P3-1)

Task #97-P3-0 left `instantiate1Go_spec` with five open goals and printed only
what the file proved on its own.  All five are closed: the binder arm's two by
`Bridge/StoreBM.lean`'s `BMExt` threaded through the intern specs, the `bvar`
arm's three by the arm-split ruling, which makes the `bvar` arm a theorem of
its own where unfolding the answer relation cannot reach any other arm.  So
the whole chain is printed here — the five arm theorems, the dispatcher, the
entry bracket and the run form — and every one of them must report the three.

The binder-datum store's extension relation is printed with them: it is the
one piece of new store reasoning the round added, and the two `intern` facts
under it are what every rebuilding walk's binder arm now leans on. -/

#print axioms BMExt.intern
#print axioms BMExt.internAt
#print axioms BMExt.get
#print axioms BMExt.isSome
#print axioms ConRon.Arena.EStore.view_of_find
#print axioms ConRon.Arena.EStore.view_of_persFind
#print axioms ConRon.Arena.NStore.view_of_find
#print axioms ConRon.Arena.LStore.view_of_find
#print axioms ConRon.Arena.LsStore.view_of_find

#print axioms ExprOps.instantiate1ArmBVar_spec
#print axioms ExprOps.instantiate1ArmApp_spec
#print axioms ExprOps.instantiate1ArmBind_spec
#print axioms ExprOps.instantiate1ArmLet_spec
#print axioms ExprOps.instantiate1ArmProj_spec
#print axioms ExprOps.instantiate1Go_spec
#print axioms ExprOps.instantiate1Fast_spec
#print axioms ExprOps.instantiate1Fast_run

#print axioms ExprOps.instantiate1_of_bvarBound_le
#print axioms ExprOps.instantiate1_of_raw_le
#print axioms ExprOps.instantiate1_leaf
#print axioms ExprOps.Inst1At.cutoff
#print axioms ExprOps.Inst1At.leaf
#print axioms ExprOps.Inst1At.app_step
#print axioms ExprOps.Inst1At.app_step'
#print axioms ExprOps.Inst1At.bind_step
#print axioms ExprOps.Inst1At.bind_step'
#print axioms ExprOps.Inst1At.letE_step
#print axioms ExprOps.Inst1At.letE_step'
#print axioms ExprOps.Inst1At.proj_step
#print axioms ExprOps.Inst1At.proj_step'

end ConRon.Bridge
