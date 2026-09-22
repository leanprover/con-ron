/-
# `ConRon.Refine2.ExprOps.Mut` — Theorem 2 for the 65 state-WRITING functions of `arena::expr_ops`

**Deliverable 2 of task #97 P5, the main slice** (DESIGN.md §8.2, Theorem 2).
Every function of `crates/con-ron-core/src/arena/expr_ops.rs` that takes
`pers: &PersTier` and `st: &mut AState` — the substituting walks, the
`internRebuilt` family, the telescope instantiations, the two packed-range
recomputations and the level substitution — against its
`proof/ConRon/Arena/ExprOps.lean` twin.

## The statement

`Refine2/Shape.lean`'s `Sim`, one application per lemma:

    Sim A WF pers lst o (twin args)

where `o` is the Rust's own outcome PAIR
`(core.result.Result R CheckError) × AState` — the state threaded as a return
value, which is the shape task #97s round 2 measured and round 3 showed the
task-#70 idiom does not mind.  `Sim`'s success arm quantifies the twin's
post-state (the cons and memo tables are related by a probe agreement, so the
abstraction of the state is a RELATION — `RefineOld/State.lean`'s own shape)
and carries `Ext lst.store lst'.store`, which is what `orElseAttempt` will
need at the checker tier (task #97-LC's ledger row).

`WF` is `fun _ => True` throughout this file: every result is a handle, a
`Bool`, a count or a list of handles, and the well-formedness a caller wants
of a handle is a clause of `AStateRel`/`AStateInv` about the STORE, not a
predicate on the word.

## What does not line up one-to-one, and what was done about it

**Eleven `_from` cursor companions have no twin of their own.**  DESIGN §3.4's
standing deviation: where the twin recurses structurally on a `List`, the Rust
takes the whole `Vec` and an index, so `f_from … args i` is the twin `f`
applied to the list `args` *from `i` on*.  `absEIdxListFrom` is that reading,
and it is the only abstraction in this file that mentions a cursor:
`inst_pis_from`, `inst_pis_at_from`, `inst_lams_at_from`, `inst_spine_from`,
`inst_pis_at_lift_from` and `mk_app_n_from` are stated against `instPis`,
`instPisAt`, `instLamsAt`, `instSpine`, `instPisAtLift` and `mkAppNFrom`
respectively.  Two of the six are NOT of that kind and are worth naming:

* `mk_app_n_from` **does** have a twin of its own, `mkAppNFrom`, which takes
  an `Array` and the same increasing cursor (task #97-P6-15 gave the twin the
  cursor form because the batched β holds a push-order array).  So that pair
  is one-to-one and the `_from` lemma is stated at the twin's own cursor.
* `inst_pis_at_f_go` / `inst_lams_at_f_go` carry BOTH shapes at once — an
  `Array` accumulator (`acc`, push order, the twin's own) and a cursor into a
  `List` (`args`).  The statement therefore uses `absEIdxArr` for `acc` and
  `absEIdxListFrom` for `args`.

**`instantiate_list*`'s `vs` is an `Array` and `inst_pis*`'s `args` is a
`List`.**  Both are `Vec<EIdx>` in the Rust.  Task #97-P6-15 made every
substitution ACCUMULATOR an `Array` read from the end, while an argument
SPINE stayed a `List` con-leche's way; the twin distinguishes them and so does
this file (`absEIdxArr` against `absEIdxList`).  Getting the two the wrong way
round type-checks nowhere, which is the useful part.

**`rename_consts_go` / `rename_consts_fast` take a dictionary, not a
function.**  DESIGN §3.4 forbids closures in code Aeneas must translate, so
the Rust's `f : NIdx → NIdx` is the one-method trait `NIdxToNIdx`, which
Aeneas renders as `NIdxToNIdxInst.rename f : NIdx → Result NIdx` — a
`Result`, because a trait method may fail.  The twin's is a total
`NIdx → NIdx`.  The two are related by a hypothesis, `RenameRel`, and that
hypothesis is the whole of the difference.

**`bvar_range` returns a `Vec` the twin returns as a `List`**, and the Rust
builds it with `cons_eidx` on the way out, so the orders agree and the
abstraction is `absEIdxList` with no reversal.  The same holds of
`inst_pis_at`'s and `inst_lams_at`'s returned domain vectors.

## Proofs

Every lemma here is `sorry`: closing them needs the store and memo inversion
layer of `Refine2/Specs.lean` (`view`/`viewApp`/`viewBindI`/`derivedE`/
`internE` and the per-walk memo probe and insert), which is landing
separately.  The STATEMENT is the deliverable, and it elaborates — which is
what makes it worth anything.  The `Specs.lean` primitives each group waits on
are named in its section note.
-/
import ConRon.Refine2.Specs
import ConRon.Arena.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The handle-vector abstractions

Three readings of one Rust type.  `Vec<EIdx>` is the twin's `Array EIdx` where
it is a substitution ACCUMULATOR (task #97-P6-15's push order) and its
`List EIdx` where it is an argument SPINE (con-leche's own shape); a `_from`
cursor companion reads the spine from the cursor on. -/

/-- A `Vec<EIdx>` as the twin's push-order `Array EIdx`. -/
def absEIdxArr (v : alloc.vec.Vec arena.handle.EIdx) : Array EIdx :=
  (v.val.map absEIdx).toArray

/-- A `Vec<EIdx>` as the twin's `List EIdx`. -/
def absEIdxList (v : alloc.vec.Vec arena.handle.EIdx) : List EIdx :=
  v.val.map absEIdx

/-- A `Vec<EIdx>` read from a cursor on — DESIGN §3.4's standing
`List`-as-cursor deviation, and the only abstraction here that mentions one. -/
def absEIdxListFrom (v : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) :
    List EIdx := (v.val.drop i.val).map absEIdx

/-- A `Vec<NIdx>` as the twin's `List NIdx` (`instLPFast`'s level-parameter
names, which the arena keeps as handles). -/
def absNIdxList (v : alloc.vec.Vec arena.handle.NIdx) : List NIdx :=
  v.val.map absNIdx

/-- `Option<EIdx>`. -/
def absOptE (o : Option arena.handle.EIdx) : Option EIdx := o.map absEIdx

/-- `Option<(Vec<EIdx>, EIdx)>` — the domain list and the residual that
`inst_pis_at` and its three siblings answer. -/
def absOptArgsE (o : Option (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)) :
    Option (List EIdx × EIdx) :=
  o.map fun p => (absEIdxList p.1, absEIdx p.2)

attribute [simp] absEIdxArr absEIdxList absEIdxListFrom absNIdxList absOptE
  absOptArgsE

/-- **The renaming dictionary against the twin's function** (`rename_consts`'s
one higher-order argument).  Aeneas renders the `NIdxToNIdx` trait method as
`Result`-valued because a trait method may fail; the twin's argument is a
total `NIdx → NIdx`.  Read it forward from `= ok`, as everything in this tier
is: *whatever the dictionary answers, the twin's function answers the
abstraction of it.* -/
def RenameRel {F : Type} (inst : arena.expr_ops.NIdxToNIdx F) (f : F)
    (g : NIdx → NIdx) : Prop :=
  ∀ n r, inst.rename f n = ok r → g (absNIdx n) = absNIdx r

/-! ## `internRebuilt` and its twelve per-constructor entries

Task #97-P6-5's upward cutoff (`internRebuilt`) and task #97-P6-15's
per-constructor entries, which take the arm's own fields so that no
`ENodeView` is ever built.  `Specs.lean` primitives: `internE` and the ten
`intern<Ctor>E`, plus `internBindIE`. -/

/-- `Arena/ExprOps.lean:139 internRebuilt`. -/
theorem intern_rebuilt_refines {pers st lst} {h : arena.handle.EIdx} {same : Bool}
    {v : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt pers st h same v = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuilt (absEIdx h) same (absENodeView v)) := by
  sorry

/-- `Arena/ExprOps.lean:144 internRebuiltBVar`. -/
theorem intern_rebuilt_bvar_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_bvar pers st h same i = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltBVar (absEIdx h) same (absU i)) := by
  sorry

/-- `Arena/ExprOps.lean:147 internRebuiltFVar`. -/
theorem intern_rebuilt_fvar_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {idx : Std.U64} {ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_fvar pers st h same idx ty = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltFVar (absEIdx h) same (absU idx) (absEIdx ty)) := by
  sorry

/-- `Arena/ExprOps.lean:150 internRebuiltSort`. -/
theorem intern_rebuilt_sort_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {u : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_sort pers st h same u = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltSort (absEIdx h) same (absLIdx u)) := by
  sorry

/-- `Arena/ExprOps.lean:153 internRebuiltConst`. -/
theorem intern_rebuilt_const_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {n : arena.handle.NIdx} {us : arena.handle.LsIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_const pers st h same n us = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltConst (absEIdx h) same (absNIdx n) (absLsIdx us)) := by
  sorry

/-- `Arena/ExprOps.lean:156 internRebuiltApp`. -/
theorem intern_rebuilt_app_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {f a : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_app pers st h same f a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltApp (absEIdx h) same (absEIdx f) (absEIdx a)) := by
  sorry

/-- `Arena/ExprOps.lean:159 internRebuiltLam`. -/
theorem intern_rebuilt_lam_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {ty body : arena.handle.EIdx} {m : kernel.expr.BinderMeta} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_lam pers st h same ty body m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltLam (absEIdx h) same (absEIdx ty) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) := by
  sorry

/-- `Arena/ExprOps.lean:163 internRebuiltForallE`. -/
theorem intern_rebuilt_forall_e_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {ty body : arena.handle.EIdx} {m : kernel.expr.BinderMeta} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_forall_e pers st h same ty body m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltForallE (absEIdx h) same (absEIdx ty) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) := by
  sorry

/-- `Arena/ExprOps.lean:167 internRebuiltLetE`. -/
theorem intern_rebuilt_let_e_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {ty val body : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_let_e pers st h same ty val body = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltLetE (absEIdx h) same (absEIdx ty) (absEIdx val)
        (absEIdx body)) := by
  sorry

/-- `Arena/ExprOps.lean:170 internRebuiltLit`. -/
theorem intern_rebuilt_lit_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {l : kernel.expr.Literal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_lit pers st h same l = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltLit (absEIdx h) same (ConRon.Refine.absLiteral l)) := by
  sorry

/-- `Arena/ExprOps.lean:173 internRebuiltProj`. -/
theorem intern_rebuilt_proj_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {n : arena.handle.NIdx} {i : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_proj pers st h same n i e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltProj (absEIdx h) same (absNIdx n) (absU i) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:179 internRebuiltBind`. -/
theorem intern_rebuilt_bind_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {tag : Std.U32} {ty body : arena.handle.EIdx}
    {m : kernel.expr.BinderMeta} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_bind pers st h same tag ty body m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltBind (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) := by
  sorry

/-- `Arena/ExprOps.lean:189 internRebuiltBindI` — the datum carried across as
a HANDLE (task #97-P6-16). -/
theorem intern_rebuilt_bind_i_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {tag : Std.U32} {ty body : arena.handle.EIdx}
    {m : arena.handle.BMIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_bind_i pers st h same tag ty body m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltBindI (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx body)
        (absBMIdx m)) := by
  sorry

/-! ## `instantiate1` — the memoised single substitution

`Specs.lean` primitives: `derivedE`, `inst1Get`, `inst1Set`, `inst1Clear`,
`viewApp`, `viewBindI`, `viewBVar`, `viewLet`, `viewProj`, `failDanglingE`,
`internAppE`, `internBindIE`, `internBVarE`, `internLetEE`, `internProjE`.
This is the function round 3 priced at 22 lines of proof, and it is the
template for the other four walks of the same shape. -/

/-- `Arena/ExprOps.lean:254 instantiate1Go`. -/
theorem instantiate1_go_refines {pers st lst} {v : arena.handle.EIdx}
    {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate1_go pers st v fuel h d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiate1Go (absEIdx v) (absU fuel) (absEIdx h) (absU d)) := by
  sorry

/-- `Arena/ExprOps.lean:324 instantiate1Fast` — the memo fresh before and
dropped after. -/
theorem instantiate1_fast_refines {pers st lst} {fuel : Std.U64}
    {e v : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate1_fast pers st fuel e v d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiate1Fast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) := by
  sorry

/-! ## `instantiateList` — the bulk substitution, two twins

`Arena/ExprOps.lean`'s own note: TWO twins and not one, because
`instantiateListGo`'s `bvar` arm recurses into the replacement through the
UNMEMOIZED `instantiateList` with a shorter vector.  The accumulator is an
`Array` in push order (task #97-P6-15), read from the end.

`Specs.lean` primitives: `instListCutoff`'s `derivedE`, `instLGet`/`instLSet`/
`instLClear`, the five projections, the five `intern*E`. -/

/-- `Arena/ExprOps.lean:346 instantiateList` — the UNMEMOIZED bulk walk. -/
theorem instantiate_list_refines {pers st lst} {vs : alloc.vec.Vec arena.handle.EIdx}
    {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate_list pers st vs fuel h d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiateList (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)) := by
  sorry

/-- `Arena/ExprOps.lean:412 instantiateListGo` — the memoised one. -/
theorem instantiate_list_go_refines {pers st lst}
    {vs : alloc.vec.Vec arena.handle.EIdx} {fuel : Std.U64}
    {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate_list_go pers st vs fuel h d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiateListGo (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)) := by
  sorry

/-- `Arena/ExprOps.lean:474 instantiateListFast`. -/
theorem instantiate_list_fast_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {vs : alloc.vec.Vec arena.handle.EIdx}
    {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate_list_fast pers st fuel e vs d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiateListFast (absU fuel) (absEIdx e) (absEIdxArr vs) (absU d)) := by
  sorry

/-! ## `liftLooseBVars`, `resetMeta`, `abstract1`, `abstractRange`,
`lowerBVars`, `instantiate1Lift` — the five remaining memoised walks

Same shape as `instantiate1Go`, same `Specs.lean` primitives with the walk's
own memo triple (`liftGet`/`liftSet`/`liftClear`, `resetGet`/…, `abs1Get`/…,
`lowerGet`/…, `inst1LGet`/…).  `abstractRange` is the SPEC descent task
#97-P6-11 kept as the statement subject beside the executed
`abstractRangeGo`. -/

/-- `Arena/ExprOps.lean:491 liftLooseBVarsGo`. -/
theorem lift_loose_bvars_go_refines {pers st lst} {amount fuel : Std.U64}
    {h : arena.handle.EIdx} {c : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lift_loose_bvars_go pers st amount fuel h c = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (liftLooseBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)) := by
  sorry

/-- `Arena/ExprOps.lean:552 liftLooseBVarsFast`. -/
theorem lift_loose_bvars_fast_refines {pers st lst} {fuel amount c : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lift_loose_bvars_fast pers st fuel amount c e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (liftLooseBVarsFast (absU fuel) (absU amount) (absU c) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:567 resetMetaGo`. -/
theorem reset_meta_go_refines {pers st lst} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.reset_meta_go pers st fuel h = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (resetMetaGo (absU fuel) (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:633 resetMetaFast`. -/
theorem reset_meta_fast_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.reset_meta_fast pers st fuel e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (resetMetaFast (absU fuel) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:669 abstractRange` — the SPEC descent (task #97-P6-11
keeps it as the statement subject beside the executed `abstractRangeGo`). -/
theorem abstract_range_refines {pers st lst} {fuel : Std.U64}
    {h : arena.handle.EIdx} {d k c : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.abstract_range pers st fuel h d k c = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (abstractRange (absU fuel) (absEIdx h) (absU d) (absU k) (absU c)) := by
  sorry

/-- `Arena/ExprOps.lean:1520 abstract1Go`. -/
theorem abstract1_go_refines {pers st lst} {d fuel : Std.U64}
    {h : arena.handle.EIdx} {k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.abstract1_go pers st d fuel h k = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (abstract1Go (absU d) (absU fuel) (absEIdx h) (absU k)) := by
  sorry

/-- `Arena/ExprOps.lean:1585 abstract1Fast`. -/
theorem abstract1_fast_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {d k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.abstract1_fast pers st fuel e d k = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (abstract1Fast (absU fuel) (absEIdx e) (absU d) (absU k)) := by
  sorry

/-- `Arena/ExprOps.lean:1616 abstractRangeGo` — the EXECUTED range
abstraction (task #97-P6-11). -/
theorem abstract_range_go_refines {pers st lst} {d k fuel : Std.U64}
    {h : arena.handle.EIdx} {c : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.abstract_range_go pers st d k fuel h c = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (abstractRangeGo (absU d) (absU k) (absU fuel) (absEIdx h) (absU c)) := by
  sorry

/-- `Arena/ExprOps.lean:1686 abstractRangeFast`. -/
theorem abstract_range_fast_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {d k c : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.abstract_range_fast pers st fuel e d k c = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (abstractRangeFast (absU fuel) (absEIdx e) (absU d) (absU k) (absU c)) := by
  sorry

/-- `Arena/ExprOps.lean:1700 lowerBVarsGo`. -/
theorem lower_bvars_go_refines {pers st lst} {amount fuel : Std.U64}
    {h : arena.handle.EIdx} {c : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lower_bvars_go pers st amount fuel h c = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (lowerBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)) := by
  sorry

/-- `Arena/ExprOps.lean:1761 lowerBVarsFast`. -/
theorem lower_bvars_fast_refines {pers st lst} {fuel amount c : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lower_bvars_fast pers st fuel amount c e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (lowerBVarsFast (absU fuel) (absU amount) (absU c) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:1779 instantiate1LiftGo`. -/
theorem instantiate1_lift_go_refines {pers st lst} {v : arena.handle.EIdx}
    {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate1_lift_go pers st v fuel h d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiate1LiftGo (absEIdx v) (absU fuel) (absEIdx h) (absU d)) := by
  sorry

/-- `Arena/ExprOps.lean:1843 instantiate1LiftFast`. -/
theorem instantiate1_lift_fast_refines {pers st lst} {fuel : Std.U64}
    {e v : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.instantiate1_lift_fast pers st fuel e v d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiate1LiftFast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) := by
  sorry

/-! ## `renameConsts` — the module's one higher-order argument

`RenameRel` is the whole of the difference between the Rust's `NIdxToNIdx`
dictionary and the twin's `NIdx → NIdx`.  `Specs.lean` primitives: `view`,
`internE`, `internConstE`. -/

/-- `Arena/ExprOps.lean:1102 renameConstsGo`. -/
theorem rename_consts_go_refines {F : Type}
    {inst : arena.expr_ops.NIdxToNIdx F} {pers st lst} {f : F}
    {g : NIdx → NIdx} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hf : RenameRel inst f g)
    (hrun : arena.expr_ops.rename_consts_go inst pers st f fuel h = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (renameConstsGo g (absU fuel) (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:1168 renameConstsFast`. -/
theorem rename_consts_fast_refines {F : Type}
    {inst : arena.expr_ops.NIdxToNIdx F} {pers st lst} {fuel : Std.U64} {f : F}
    {g : NIdx → NIdx} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hf : RenameRel inst f g)
    (hrun : arena.expr_ops.rename_consts_fast inst pers st fuel f e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (renameConstsFast (absU fuel) g (absEIdx e)) := by
  sorry

/-! ## `mkAppN` — the application spine, rebuilt

The twin has BOTH shapes (task #97-P6-15 gave it the cursor form for the
batched β), so this pair is one-to-one: `mk_app_n` is `mkAppN` at the `List`
and `mk_app_n_from` is `mkAppNFrom` at the push-order `Array` and the same
increasing cursor.  `Specs.lean` primitives: `internE`, `internAppE`. -/

/-- `Arena/ExprOps.lean:1069 mkAppN`. -/
theorem mk_app_n_refines {pers st lst} {f : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.mk_app_n pers st f args = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (mkAppN (absEIdx f) (absEIdxList args)) := by
  sorry

/-- `Arena/ExprOps.lean:1079 mkAppNFrom`. -/
theorem mk_app_n_from_refines {pers st lst} {f : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.mk_app_n_from pers st f args i = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (mkAppNFrom (absEIdx f) (absEIdxArr args) (absSz i)) := by
  sorry

/-! ## The telescope instantiations

Six `_from` cursor companions with no twin of their own (DESIGN §3.4's
standing deviation) and their five entry points.  `Specs.lean` primitives:
`view`, `viewBind`, `failDanglingE`, and `instantiate1Fast` /
`instantiateListFast` through their own lemmas above. -/

/-- `Arena/ExprOps.lean:1212 instPis`. -/
theorem inst_pis_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis pers st fuel e args = ok o) :
    Sim absOptE (fun _ => True) pers lst o
      (instPis (absU fuel) (absEIdx e) (absEIdxList args)) := by
  sorry

/-- `Arena/ExprOps.lean:1212 instPis` — the cursor companion, stated at the
argument list FROM the cursor on. -/
theorem inst_pis_from_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {args : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_from pers st fuel e args i = ok o) :
    Sim absOptE (fun _ => True) pers lst o
      (instPis (absU fuel) (absEIdx e) (absEIdxListFrom args i)) := by
  sorry

/-- `Arena/ExprOps.lean:1225 instPisAt`. -/
theorem inst_pis_at_refines {pers st lst} {fuel : Std.U64}
    {args : alloc.vec.Vec arena.handle.EIdx} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at pers st fuel args h = ok o) :
    Sim absOptArgsE (fun _ => True) pers lst o
      (instPisAt (absU fuel) (absEIdxList args) (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:1225 instPisAt` — the cursor companion. -/
theorem inst_pis_at_from_refines {pers st lst} {fuel : Std.U64}
    {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at_from pers st fuel args i h = ok o) :
    Sim absOptArgsE (fun _ => True) pers lst o
      (instPisAt (absU fuel) (absEIdxListFrom args i) (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:1238 instLamsAt`. -/
theorem inst_lams_at_refines {pers st lst} {fuel : Std.U64}
    {args : alloc.vec.Vec arena.handle.EIdx} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lams_at pers st fuel args h = ok o) :
    Sim absOptArgsE (fun _ => True) pers lst o
      (instLamsAt (absU fuel) (absEIdxList args) (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:1238 instLamsAt` — the cursor companion. -/
theorem inst_lams_at_from_refines {pers st lst} {fuel : Std.U64}
    {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lams_at_from pers st fuel args i h = ok o) :
    Sim absOptArgsE (fun _ => True) pers lst o
      (instLamsAt (absU fuel) (absEIdxListFrom args i) (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:1252 instPisAtFGo` — BOTH shapes at once: a
push-order `Array` accumulator and a cursor into the argument list. -/
theorem inst_pis_at_f_go_refines {pers st lst} {fuel : Std.U64}
    {acc args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at_f_go pers st fuel acc args i h = ok o) :
    Sim absOptArgsE (fun _ => True) pers lst o
      (instPisAtFGo (absU fuel) (absEIdxArr acc) (absEIdxListFrom args i)
        (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:1269 instPisAtF`. -/
theorem inst_pis_at_f_refines {pers st lst} {fuel : Std.U64}
    {args : alloc.vec.Vec arena.handle.EIdx} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at_f pers st fuel args e = ok o) :
    Sim absOptArgsE (fun _ => True) pers lst o
      (instPisAtF (absU fuel) (absEIdxList args) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:1277 instLamsAtFGo`. -/
theorem inst_lams_at_f_go_refines {pers st lst} {fuel : Std.U64}
    {acc args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lams_at_f_go pers st fuel acc args i h = ok o) :
    Sim absOptArgsE (fun _ => True) pers lst o
      (instLamsAtFGo (absU fuel) (absEIdxArr acc) (absEIdxListFrom args i)
        (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:1294 instLamsAtF`. -/
theorem inst_lams_at_f_refines {pers st lst} {fuel : Std.U64}
    {args : alloc.vec.Vec arena.handle.EIdx} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lams_at_f pers st fuel args e = ok o) :
    Sim absOptArgsE (fun _ => True) pers lst o
      (instLamsAtF (absU fuel) (absEIdxList args) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:1309 instSpine`. -/
theorem inst_spine_refines {pers st lst} {fuel : Std.U64}
    {args : alloc.vec.Vec arena.handle.EIdx} {t : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_spine pers st fuel args t e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instSpine (absU fuel) (absEIdxList args) (absU t) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:1309 instSpine` — the cursor companion. -/
theorem inst_spine_from_refines {pers st lst} {fuel : Std.U64}
    {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {t : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_spine_from pers st fuel args i t e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instSpine (absU fuel) (absEIdxListFrom args i) (absU t) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:1851 instPisAtLift`. -/
theorem inst_pis_at_lift_refines {pers st lst} {fuel : Std.U64}
    {args : alloc.vec.Vec arena.handle.EIdx} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at_lift pers st fuel args h = ok o) :
    Sim absOptE (fun _ => True) pers lst o
      (instPisAtLift (absU fuel) (absEIdxList args) (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:1851 instPisAtLift` — the cursor companion. -/
theorem inst_pis_at_lift_from_refines {pers st lst} {fuel : Std.U64}
    {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_pis_at_lift_from pers st fuel args i h = ok o) :
    Sim absOptE (fun _ => True) pers lst o
      (instPisAtLift (absU fuel) (absEIdxListFrom args i) (absEIdx h)) := by
  sorry

/-! ## The recursor-rule and binder-surgery helpers

`Specs.lean` primitives: `view`, `internE`, `internBVarE`, plus `stripPis`
and `getAppArgs` through `ExprOps/Read.lean`. -/

/-- `Arena/ExprOps.lean:1318 bvarRange` — the Rust's `Vec` is built with
`cons_eidx` on the way out, so the two orders agree and the abstraction is
`absEIdxList` with no reversal. -/
theorem bvar_range_refines {pers st lst} {m_i n k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_range pers st m_i n k = ok o) :
    Sim absEIdxList (fun _ => True) pers lst o
      (bvarRange (absU m_i) (absU n) (absU k)) := by
  sorry

/-- `Arena/ExprOps.lean:1330 recRulePlain`. -/
theorem rec_rule_plain_refines {pers st lst} {fuel : Std.U64}
    {rec_ty : arena.handle.EIdx} {m_i r_p cn_p : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.rec_rule_plain pers st fuel rec_ty m_i r_p cn_p = ok o) :
    Sim id (fun _ => True) pers lst o
      (recRulePlain (absU fuel) (absEIdx rec_ty) (absU m_i) (absU r_p)
        (absU cn_p)) := by
  sorry

/-- `Arena/ExprOps.lean:1348 pisToLams`. -/
theorem pis_to_lams_refines {pers st lst} {k : Std.U64}
    {h body : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.pis_to_lams pers st k h body = ok o) :
    Sim absOptE (fun _ => True) pers lst o
      (pisToLams (absU k) (absEIdx h) (absEIdx body)) := by
  sorry

/-- `Arena/ExprOps.lean:1362 replacePiBody`. -/
theorem replace_pi_body_refines {pers st lst} {k : Std.U64}
    {h b : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.replace_pi_body pers st k h b = ok o) :
    Sim absOptE (fun _ => True) pers lst o
      (replacePiBody (absU k) (absEIdx h) (absEIdx b)) := by
  sorry

/-! ## The packed range fields and their saturated-branch recomputations

`Arena/ExprOps.lean`'s own note: the arena reads both ranges in `O(1)` off the
derived column and only walks on the saturated branch, where the walk is
memoised exactly as con-leche's is.  `Specs.lean` primitives: `derivedE`,
`bvarBGet`/`bvarBSet`/`bvarBClear`, `fvarBGet`/`fvarBSet`/`fvarBClear`, the
five projections. -/

/-- `Arena/ExprOps.lean:1408 bvarBoundGo`. -/
theorem bvar_bound_go_refines {pers st lst} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_bound_go pers st fuel h = ok o) :
    Sim absU (fun _ => True) pers lst o
      (bvarBoundGo (absU fuel) (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:1437 bvarBoundMemo`. -/
theorem bvar_bound_memo_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_bound_memo pers st fuel e = ok o) :
    Sim absU (fun _ => True) pers lst o
      (bvarBoundMemo (absU fuel) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:1447 fvarRangeGo`. -/
theorem fvar_range_go_refines {pers st lst} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_range_go pers st fuel h = ok o) :
    Sim absU (fun _ => True) pers lst o
      (fvarRangeGo (absU fuel) (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:1476 fvarRangeMemo`. -/
theorem fvar_range_memo_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_range_memo pers st fuel e = ok o) :
    Sim absU (fun _ => True) pers lst o
      (fvarRangeMemo (absU fuel) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:1486 bvarB` — the `O(1)` read with the saturated
fallback. -/
theorem bvar_b_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_b pers st fuel e = ok o) :
    Sim absU (fun _ => True) pers lst o (bvarB (absU fuel) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:1494 fvarB`. -/
theorem fvar_b_refines {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_b pers st fuel e = ok o) :
    Sim absU (fun _ => True) pers lst o (fvarB (absU fuel) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:1501 hasFvarFast`. -/
theorem has_fvar_fast_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.has_fvar_fast pers st fuel e = ok o) :
    Sim id (fun _ => True) pers lst o (hasFvarFast (absU fuel) (absEIdx e)) := by
  sorry

/-- `Arena/ExprOps.lean:1507 looseBVarsBoundedFast`. -/
theorem loose_bvars_bounded_fast_refines {pers st lst} {fuel k : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.loose_bvars_bounded_fast pers st fuel k e = ok o) :
    Sim id (fun _ => True) pers lst o
      (looseBVarsBoundedFast (absU fuel) (absU k) (absEIdx e)) := by
  sorry

/-! ## The level substitution

DESIGN §8.3's lesson 4, "intern the representation, not the algorithm": the
level ALGORITHM runs on transient `ConLeche.Level` trees read back out of the
store, so `ks`/`us` are VALUES on both sides and `Refine/Abs.lean`'s
`absNames`/`absLevels` are their abstraction.  `inst_lp_fast` is the one entry
that takes them as HANDLES (`Vec<NIdx>` and an `LsIdx`), which is what the
twin's `instLPFast` takes too.

`Specs.lean` primitives: `instLPLGet`/`instLPLSet`, `instLPLsGet`/
`instLPLsSet`, `readLevelM`, `readLevelsM`, `readNamesM`, `internLevel`,
`internLevels`, `instLPGet`/`instLPSet`/`instLPClear`, `derivedE`, `viewLs`. -/

/-- `Arena/ExprOps.lean:1914 substLMemoAt`. -/
theorem subst_l_memo_at_refines {pers st lst} {ks : alloc.vec.Vec kernel.name.Name}
    {us : alloc.vec.Vec kernel.level.Level} {u : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.subst_l_memo_at pers st ks us u = ok o) :
    Sim absLIdx (fun _ => True) pers lst o
      (substLMemoAt (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels us)
        (absLIdx u)) := by
  sorry

/-- `Arena/ExprOps.lean:1925 substLsMemoAt`. -/
theorem subst_ls_memo_at_refines {pers st lst}
    {ks : alloc.vec.Vec kernel.name.Name}
    {us : alloc.vec.Vec kernel.level.Level} {vs : arena.handle.LsIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.subst_ls_memo_at pers st ks us vs = ok o) :
    Sim absLsIdx (fun _ => True) pers lst o
      (substLsMemoAt (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels us)
        (absLsIdx vs)) := by
  sorry

/-- `Arena/ExprOps.lean:1941 instLPGo`. -/
theorem inst_lp_go_refines {pers st lst} {ks : alloc.vec.Vec kernel.name.Name}
    {us : alloc.vec.Vec kernel.level.Level} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lp_go pers st ks us fuel h = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instLPGo (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels us)
        (absU fuel) (absEIdx h)) := by
  sorry

/-- `Arena/ExprOps.lean:2016 instLPFast` — the entry that takes the level
parameters as HANDLES, reads them back and clears the three tables. -/
theorem inst_lp_fast_refines {pers st lst} {fuel : Std.U64}
    {ks : alloc.vec.Vec arena.handle.NIdx} {us : arena.handle.LsIdx}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_lp_fast pers st fuel ks us e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instLPFast (absU fuel) (absNIdxList ks) (absLsIdx us) (absEIdx e)) := by
  sorry

end ConRon.Refine2
