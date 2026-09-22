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

**Eight of the sixty-five are closed (task #97-P5-3): the packed-range family**
— `bvar_bound_go`, `bvar_bound_memo`, `fvar_range_go`, `fvar_range_memo`,
`bvar_b`, `fvar_b`, `has_fvar_fast`, `loose_bvars_bounded_fast` — which read
the derived column and the per-declaration memo and **intern nothing**.  They
are `ExprOps/Read.lean`'s memo idiom at a walk whose memo lives in the STATE
(`bvarBGet`/`bvarBSet`) rather than being threaded, so they are `Sim` and not
`WOut`.

**The other fifty-seven all intern**, and every intern wrapper they reach is
one of `Refine2/Specs.lean`'s remaining twelve — `intern_e_run` above all,
which waits on `Arena/WFProofs.lean`'s `EStore.internBindI_ext` (written on
branch `wf-ext`, not yet on `arena`).  So the thirteen `intern_rebuilt_*` are
only the most visible of fifty-seven blocked by one merge.  The STATEMENT is the deliverable, and it elaborates — which is
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

/-- `arena::expr_ops::intern_rebuilt_bvar` against `Arena.internRebuiltBVar`. -/
theorem intern_rebuilt_bvar_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hcap : same = false → lst.store.find? (.bvar (absU i)) = none →
      (if lst.store.scratchOn then lst.store.scr.sizeOf (.bvar (absU i))
        else lst.store.pers.sizeOf (.bvar (absU i))) < Idx.idxCap)
    (hrun : arena.expr_ops.intern_rebuilt_bvar pers st h same i = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltBVar (absEIdx h) same (absU i)) := by
  rw [arena.expr_ops.intern_rebuilt_bvar] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltBVar (absEIdx h) same (absU i)).run lst)
  rw [internRebuiltBVar]
  by_cases hs : same = true
  · subst hs
    rw [if_pos rfl] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    simp only [if_true]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · simp only [Bool.not_eq_true] at hs
    subst hs
    simp only [Bool.false_eq_true, if_false]
    exact intern_e_bvar_run hrel hinv hfrozen i (hcap rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_fvar` against `Arena.internRebuiltFVar`. -/
theorem intern_rebuilt_fvar_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {idx : Std.U64} {ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      (absEIdx ty).isPersistent = false →
      lst.store.pers.fvars.find? ⟨absU idx, absEIdx ty⟩ = none)
    (hcap : same = false → lst.store.find? (.fvar (absU idx) (absEIdx ty)) = none →
      (if lst.store.scratchOn then lst.store.scr.sizeOf (.fvar (absU idx) (absEIdx ty))
        else lst.store.pers.sizeOf (.fvar (absU idx) (absEIdx ty))) < Idx.idxCap)
    (hrun : arena.expr_ops.intern_rebuilt_fvar pers st h same idx ty = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltFVar (absEIdx h) same (absU idx) (absEIdx ty)) := by
  rw [arena.expr_ops.intern_rebuilt_fvar] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltFVar (absEIdx h) same (absU idx) (absEIdx ty)).run lst)
  rw [internRebuiltFVar]
  by_cases hs : same = true
  · subst hs
    rw [if_pos rfl] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    simp only [if_true]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · simp only [Bool.not_eq_true] at hs
    subst hs
    simp only [Bool.false_eq_true, if_false]
    exact intern_e_fvar_run hrel hinv hfrozen idx ty (hchild rfl) (hcap rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_sort` against `Arena.internRebuiltSort`. -/
theorem intern_rebuilt_sort_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {u : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      (absLIdx u).isPersistent = false →
      lst.store.pers.sorts.find? ⟨absLIdx u⟩ = none)
    (hcap : same = false → lst.store.find? (.sort (absLIdx u)) = none →
      (if lst.store.scratchOn then lst.store.scr.sizeOf (.sort (absLIdx u))
        else lst.store.pers.sizeOf (.sort (absLIdx u))) < Idx.idxCap)
    (hrun : arena.expr_ops.intern_rebuilt_sort pers st h same u = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltSort (absEIdx h) same (absLIdx u)) := by
  rw [arena.expr_ops.intern_rebuilt_sort] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltSort (absEIdx h) same (absLIdx u)).run lst)
  rw [internRebuiltSort]
  by_cases hs : same = true
  · subst hs
    rw [if_pos rfl] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    simp only [if_true]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · simp only [Bool.not_eq_true] at hs
    subst hs
    simp only [Bool.false_eq_true, if_false]
    exact intern_e_sort_run hrel hinv hfrozen u (hchild rfl) (hcap rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_const` against `Arena.internRebuiltConst`. -/
theorem intern_rebuilt_const_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {n : arena.handle.NIdx} {us : arena.handle.LsIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      ((absNIdx n).isPersistent = false ∨ (absLsIdx us).isPersistent = false) →
      lst.store.pers.consts.find? ⟨absNIdx n, absLsIdx us⟩ = none)
    (hcap : same = false → lst.store.find? (.const (absNIdx n) (absLsIdx us)) = none →
      (if lst.store.scratchOn then lst.store.scr.sizeOf (.const (absNIdx n) (absLsIdx us))
        else lst.store.pers.sizeOf (.const (absNIdx n) (absLsIdx us))) < Idx.idxCap)
    (hrun : arena.expr_ops.intern_rebuilt_const pers st h same n us = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltConst (absEIdx h) same (absNIdx n) (absLsIdx us)) := by
  rw [arena.expr_ops.intern_rebuilt_const] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltConst (absEIdx h) same (absNIdx n) (absLsIdx us)).run lst)
  rw [internRebuiltConst]
  by_cases hs : same = true
  · subst hs
    rw [if_pos rfl] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    simp only [if_true]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · simp only [Bool.not_eq_true] at hs
    subst hs
    simp only [Bool.false_eq_true, if_false]
    exact intern_e_const_run hrel hinv hfrozen n us (hchild rfl) (hcap rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_app` against `Arena.internRebuiltApp`. -/
theorem intern_rebuilt_app_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {f a : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      ((absEIdx f).isPersistent = false ∨ (absEIdx a).isPersistent = false) →
      lst.store.pers.apps.find? ⟨absEIdx f, absEIdx a⟩ = none)
    (hcap : same = false → lst.store.find? (.app (absEIdx f) (absEIdx a)) = none →
      (if lst.store.scratchOn then lst.store.scr.sizeOf (.app (absEIdx f) (absEIdx a))
        else lst.store.pers.sizeOf (.app (absEIdx f) (absEIdx a))) < Idx.idxCap)
    (hrun : arena.expr_ops.intern_rebuilt_app pers st h same f a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltApp (absEIdx h) same (absEIdx f) (absEIdx a)) := by
  rw [arena.expr_ops.intern_rebuilt_app] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltApp (absEIdx h) same (absEIdx f) (absEIdx a)).run lst)
  rw [internRebuiltApp]
  by_cases hs : same = true
  · subst hs
    rw [if_pos rfl] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    simp only [if_true]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · simp only [Bool.not_eq_true] at hs
    subst hs
    simp only [Bool.false_eq_true, if_false]
    exact intern_e_app_run hrel hinv hfrozen f a (hchild rfl) (hcap rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_let_e` against `Arena.internRebuiltLetE`. -/
theorem intern_rebuilt_let_e_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {ty val body : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      ((absEIdx ty).isPersistent = false ∨ (absEIdx val).isPersistent = false ∨
        (absEIdx body).isPersistent = false) →
      lst.store.pers.lets.find? ⟨absEIdx ty, absEIdx val, absEIdx body⟩ = none)
    (hcap : same = false → lst.store.find? (.letE (absEIdx ty) (absEIdx val) (absEIdx body)) = none →
      (if lst.store.scratchOn then lst.store.scr.sizeOf (.letE (absEIdx ty) (absEIdx val) (absEIdx body))
        else lst.store.pers.sizeOf (.letE (absEIdx ty) (absEIdx val) (absEIdx body))) < Idx.idxCap)
    (hrun : arena.expr_ops.intern_rebuilt_let_e pers st h same ty val body = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltLetE (absEIdx h) same (absEIdx ty) (absEIdx val) (absEIdx body)) := by
  rw [arena.expr_ops.intern_rebuilt_let_e] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltLetE (absEIdx h) same (absEIdx ty) (absEIdx val) (absEIdx body)).run lst)
  rw [internRebuiltLetE]
  by_cases hs : same = true
  · subst hs
    rw [if_pos rfl] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    simp only [if_true]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · simp only [Bool.not_eq_true] at hs
    subst hs
    simp only [Bool.false_eq_true, if_false]
    exact intern_e_let_e_run hrel hinv hfrozen ty val body (hchild rfl) (hcap rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_lit` against `Arena.internRebuiltLit`. -/
theorem intern_rebuilt_lit_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {l : kernel.expr.Literal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hwf : ConRon.Refine.LiteralWF l)
    (hcap : same = false → lst.store.find? (.lit (ConRon.Refine.absLiteral l)) = none →
      (if lst.store.scratchOn then lst.store.scr.sizeOf (.lit (ConRon.Refine.absLiteral l))
        else lst.store.pers.sizeOf (.lit (ConRon.Refine.absLiteral l))) < Idx.idxCap)
    (hrun : arena.expr_ops.intern_rebuilt_lit pers st h same l = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltLit (absEIdx h) same (ConRon.Refine.absLiteral l)) := by
  rw [arena.expr_ops.intern_rebuilt_lit] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltLit (absEIdx h) same (ConRon.Refine.absLiteral l)).run lst)
  rw [internRebuiltLit]
  by_cases hs : same = true
  · subst hs
    rw [if_pos rfl] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    simp only [if_true]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · simp only [Bool.not_eq_true] at hs
    subst hs
    simp only [Bool.false_eq_true, if_false]
    exact intern_e_lit_run hrel hinv hfrozen l hwf (hcap rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_proj` against `Arena.internRebuiltProj`. -/
theorem intern_rebuilt_proj_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {n : arena.handle.NIdx} {i : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      ((absNIdx n).isPersistent = false ∨ (absEIdx e).isPersistent = false) →
      lst.store.pers.projs.find? ⟨absNIdx n, absU i, absEIdx e⟩ = none)
    (hcap : same = false → lst.store.find? (.proj (absNIdx n) (absU i) (absEIdx e)) = none →
      (if lst.store.scratchOn then lst.store.scr.sizeOf (.proj (absNIdx n) (absU i) (absEIdx e))
        else lst.store.pers.sizeOf (.proj (absNIdx n) (absU i) (absEIdx e))) < Idx.idxCap)
    (hrun : arena.expr_ops.intern_rebuilt_proj pers st h same n i e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltProj (absEIdx h) same (absNIdx n) (absU i) (absEIdx e)) := by
  rw [arena.expr_ops.intern_rebuilt_proj] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltProj (absEIdx h) same (absNIdx n) (absU i) (absEIdx e)).run lst)
  rw [internRebuiltProj]
  by_cases hs : same = true
  · subst hs
    rw [if_pos rfl] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    simp only [if_true]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · simp only [Bool.not_eq_true] at hs
    subst hs
    simp only [Bool.false_eq_true, if_false]
    exact intern_e_proj_run hrel hinv hfrozen n i e (hchild rfl) (hcap rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_bind_i` against `Arena.internRebuiltBindI`. -/
theorem intern_rebuilt_bind_i_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {tag : Std.U32} {ty body : arena.handle.EIdx}
    {m : arena.handle.BMIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchildL : same = false → absU32 tag = ETag.lam →
      ((absEIdx ty).isPersistent = false ∨
        (absEIdx body).isPersistent = false ∨ (absBMIdx m).isPersistent = false) →
      lst.store.pers.lams.find? ⟨absEIdx ty, absEIdx body, absBMIdx m⟩ = none)
    (hchildF : same = false → absU32 tag ≠ ETag.lam →
      ((absEIdx ty).isPersistent = false ∨
        (absEIdx body).isPersistent = false ∨ (absBMIdx m).isPersistent = false) →
      lst.store.pers.foralls.find? ⟨absEIdx ty, absEIdx body, absBMIdx m⟩ = none)
    (hcapL : same = false → absU32 tag = ETag.lam →
      lst.store.scr.bindSizeOf ETag.lam < Idx.idxCap ∧
        lst.store.pers.bindSizeOf ETag.lam < Idx.idxCap)
    (hcapF : same = false → absU32 tag ≠ ETag.lam →
      lst.store.scr.bindSizeOf ETag.forallE < Idx.idxCap ∧
        lst.store.pers.bindSizeOf ETag.forallE < Idx.idxCap)
    (hrun : arena.expr_ops.intern_rebuilt_bind_i pers st h same tag ty body m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltBindI (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx body)
        (absBMIdx m)) := by
  rw [arena.expr_ops.intern_rebuilt_bind_i] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltBindI (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx body)
      (absBMIdx m)).run lst)
  rw [internRebuiltBindI]
  by_cases hs : same = true
  · subst hs
    rw [if_pos rfl] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    simp only [if_true]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · simp only [Bool.not_eq_true] at hs
    subst hs
    simp only [Bool.false_eq_true, if_false]
    exact intern_e_bind_i_run hrel hinv hfrozen tag ty body m
      (hchildL rfl) (hchildF rfl) (hcapL rfl) (hcapF rfl) hrun

/-- `Arena/ExprOps.lean:139 internRebuilt`. -/
theorem intern_rebuilt_refines {pers st lst} {h : arena.handle.EIdx} {same : Bool}
    {v : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt pers st h same v = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuilt (absEIdx h) same (absENodeView v)) := by
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

/-! ## The two `AOut` combinators, and the port's two `Nat` scalars -/

/-- The error arm of a chained recursive call: the callee threw, so the whole
bind throws, whatever the base states are. -/
theorem aout_err_bind {β γ δ : Type} {A : γ → β} {C : Type} {AC : C → δ}
    {e : kernel.core_types.CheckError} {pers : arena.store.PersTier}
    {lstA lstB : AState} {stA stB : arena.monad.AState}
    {x : AM β} {f : β → AM δ}
    (h : AOut A (fun _ => True) pers lstA (.Err e) stA (x.run lstA)) :
    AOut AC (fun _ => True) pers lstB (.Err e) stB
      ((do let v ← x; f v).run lstA) := by
  refine AOut.err ?_
  rw [StateT.run_bind]
  exact AErrSim.bind h _

/-- An outcome measured from a later state is one measured from an earlier
one, `Ext` composed. -/
theorem aout_rebase {γ δ : Type} {AC : γ → δ} {pers : arena.store.PersTier}
    {lst lst1 : AState} {st2 : arena.monad.AState}
    {o : core.result.Result γ kernel.core_types.CheckError}
    {y : Except Arena.CheckError (δ × AState)}
    (hext : Ext lst.store lst1.store)
    (h : AOut AC (fun _ => True) pers lst1 o st2 y) :
    AOut AC (fun _ => True) pers lst o st2 y := by
  cases o with
  | Err e => exact h
  | Ok c =>
    obtain ⟨lst2, hy, hrel2, hinv2, hext2, -⟩ := h
    exact AOut.ok hy hrel2 hinv2 (Ext.trans hext hext2) trivial

/-- `kernel::expr_ops::sub_nat` is `Nat` subtraction on the abstraction. -/
theorem sub_nat_val {a b r : Std.U64}
    (h : kernel.expr_ops.sub_nat a b = ok r) : absU r = absU a - absU b := by
  rw [kernel.expr_ops.sub_nat] at h
  split at h <;> rename_i hge
  · exact (ConRon.Refine.Nat.usub_val h).2
  · simp only [Result.ok.injEq] at h
    rw [← h]
    show (0 : Nat) = a.val - b.val
    scalar_tac

/-! ## `bvarBoundGo`'s node step, as an object -/

/-- **The twin's arm dispatch of `bvarBoundGo`, transcribed** — the port
inlines the arms where the twin (task #97-P3-1's split) names them. -/
def bvarBoundNodeSpec (fuel : Nat) : ENodeView → AM Nat
  | .bvar i => pure (i + 1)
  | .fvar _ _ | .sort _ | .const _ _ | .lit _ => pure 0
  | .app f a => bvarBoundArmApp fuel f a
  | .lam ty body _ | .forallE ty body _ => bvarBoundArmBind fuel ty body
  | .letE ty val body => bvarBoundArmLet fuel ty val body
  | .proj _ _ sub => bvarBoundGo fuel sub

/-- The owed twin equation, in the port's own association: the memo probe,
the node step, the memo write. -/
theorem bvarBoundGo_unfold (fuel : Nat) (h : EIdx) :
    bvarBoundGo (fuel + 1) h = (do
      match ← bvarBGet h with
      | some r => pure r
      | none => do
        let r ← (do let w ← view h; bvarBoundNodeSpec fuel w)
        bvarBSet h r
        pure r) := by
  rw [bvarBoundGo_succ]
  simp only [bvarBoundNodeSpec, bvarBoundArmApp, bvarBoundArmBind,
    bvarBoundArmLet]
  congr 1

/-- The `bvar_bound_go` statement at one fuel value. -/
def BGoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {fuel : Std.U64} {h : arena.handle.EIdx} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st →
    arena.expr_ops.bvar_bound_go pers st fuel h = ok o →
    Sim absU (fun _ => True) pers lst o (bvarBoundGo (absU fuel) (absEIdx h))

private theorem bvar_bound_go_aux (n : Nat) : BGoAt n := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.bvar_bound_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hrrv := fail_run hrr
    have ho := Result.ok_injective hrun
    rw [← ho, hrrv]
    show AErrSim _ ((bvarBoundGo (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, bvarBoundGo_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.bvar_bound_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hget := bvar_b_get_run hrel hinv hop
    show AOut absU (fun _ => True) pers lst o.1 o.2
      ((bvarBoundGo (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = m + 1 from hn, bvarBoundGo_unfold, StateT.run_bind, hget]
    cases hoc : op with
    | some r =>
      rw [hoc] at hrun
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
    | none =>
      rw [hoc] at hrun
      show AOut absU (fun _ => True) pers lst o.1 o.2
        ((do
          let r ← (do let w ← Arena.view (absEIdx h); bvarBoundNodeSpec m w)
          bvarBSet (absEIdx h) r
          pure r).run lst)
      obtain ⟨rv, hrv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hview := view_run hrel hinv hrv
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨st1, body⟩ := p
      have hnode : AOut absU (fun _ => True) pers lst body st1
          ((do let w ← Arena.view (absEIdx h); bvarBoundNodeSpec m w).run lst) := by
        cases hrc : rv with
        | Err e =>
          rw [hrc] at hp hview
          have hpp := Result.ok_injective hp
          simp only [Prod.mk.injEq] at hpp
          obtain ⟨rfl, rfl⟩ := hpp
          show AErrSim e _
          rw [StateT.run_bind]
          exact AErrSim.bind hview _
        | Ok ev =>
          rw [hrc] at hp hview
          obtain ⟨lst0, hx, -, -, -, -⟩ := hview
          have hlst : lst0 = lst := view_run_state hx
          rw [hlst] at hx
          rw [StateT.run_bind, hx]
          cases ev with
          | BVar i0 =>
            obtain ⟨i1, hi1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            refine AOut.ok ?_ hrel hinv (Ext.refl _) trivial
            show Except.ok (absU i0 + 1, lst) = _
            rw [show absU i1 = absU i0 + 1 from ConRon.Refine.Nat.uadd_val hi1]
          | FVar _ _ =>
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
          | «Sort» _ =>
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
          | Const _ _ =>
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
          | Lit _ =>
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
          | Proj _ _ s0 =>
            obtain ⟨i2, hi2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hi2v : i2.val = m := by
              have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
                (ConRon.Refine.Nat.usub_val hi2).2
              rw [h1, hn]; rfl
            obtain ⟨q1, hq1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            obtain ⟨r1, st2⟩ := q1
            have hrec1 := ih (h := s0) hi2v hrel hinv hq1
            rw [show absU i2 = m from hi2v] at hrec1
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            exact hrec1
          | App f0 a0 =>
            obtain ⟨i2, hi2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hi2v : i2.val = m := by
              have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
                (ConRon.Refine.Nat.usub_val hi2).2
              rw [h1, hn]; rfl
            obtain ⟨q1, hq1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            obtain ⟨r1, st2⟩ := q1
            have hrec1 := ih (h := f0) hi2v hrel hinv hq1
            rw [show absU i2 = m from hi2v] at hrec1
            show AOut absU (fun _ => True) pers lst body st1
              ((bvarBoundArmApp m (absEIdx f0) (absEIdx a0)).run lst)
            rw [bvarBoundArmApp]
            cases hr1c : r1 with
            | Err e =>
              rw [hr1c] at hp hrec1
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              exact aout_err_bind hrec1
            | Ok x1 =>
              rw [hr1c] at hp hrec1
              obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
              rw [StateT.run_bind, hx1]
              obtain ⟨q2, hq2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              obtain ⟨r2, st3⟩ := q2
              have hrec2 := ih (h := a0) hi2v hrel1 hinv1 hq2
              rw [show absU i2 = m from hi2v] at hrec2
              obtain ⟨r3, hr3, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              show AOut absU (fun _ => True) pers lst r3 st3
                ((do let y ← bvarBoundGo m (absEIdx a0)
                     pure (max (absU x1) y)).run lst1)
              cases hr2c : r2 with
              | Err e =>
                rw [hr2c] at hr3 hrec2
                have ho3 : (core.result.Result.Err e :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                exact aout_err_bind hrec2
              | Ok y1 =>
                rw [hr2c] at hr3 hrec2
                obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
                rw [StateT.run_bind, hx2]
                obtain ⟨i3, hi3, hr3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr3
                have ho3 : (core.result.Result.Ok i3 :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
                show Except.ok (max (absU x1) (absU y1), lst2) = _
                rw [show absU i3 = max (absU x1) (absU y1) from
                  ConRon.Refine.Expr.max_u64_val hi3]
          | Lam ty0 b0 mm =>
            obtain ⟨i2, hi2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hi2v : i2.val = m := by
              have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
                (ConRon.Refine.Nat.usub_val hi2).2
              rw [h1, hn]; rfl
            obtain ⟨q1, hq1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            obtain ⟨r1, st2⟩ := q1
            have hrec1 := ih (h := ty0) hi2v hrel hinv hq1
            rw [show absU i2 = m from hi2v] at hrec1
            show AOut absU (fun _ => True) pers lst body st1
              ((bvarBoundArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
            rw [bvarBoundArmBind]
            cases hr1c : r1 with
            | Err e =>
              rw [hr1c] at hp hrec1
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              exact aout_err_bind hrec1
            | Ok x1 =>
              rw [hr1c] at hp hrec1
              obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
              rw [StateT.run_bind, hx1]
              obtain ⟨q2, hq2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              obtain ⟨r2, st3⟩ := q2
              have hrec2 := ih (h := b0) hi2v hrel1 hinv1 hq2
              rw [show absU i2 = m from hi2v] at hrec2
              obtain ⟨r3, hr3, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              show AOut absU (fun _ => True) pers lst r3 st3
                ((do let y ← bvarBoundGo m (absEIdx b0)
                     pure (max (absU x1) (y - 1))).run lst1)
              cases hr2c : r2 with
              | Err e =>
                rw [hr2c] at hr3 hrec2
                have ho3 : (core.result.Result.Err e :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                exact aout_err_bind hrec2
              | Ok y1 =>
                rw [hr2c] at hr3 hrec2
                obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
                rw [StateT.run_bind, hx2]
                obtain ⟨i4, hi4, hr3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr3
                obtain ⟨i3, hi3, hr3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr3
                have ho3 : (core.result.Result.Ok i3 :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
                show Except.ok (max (absU x1) (absU y1 - 1), lst2) = _
                rw [show absU i3 = max (absU x1) (absU i4) from
                    ConRon.Refine.Expr.max_u64_val hi3,
                  show absU i4 = absU y1 - 1 from sub_nat_val hi4]
          | ForallE ty0 b0 mm =>
            obtain ⟨i2, hi2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hi2v : i2.val = m := by
              have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
                (ConRon.Refine.Nat.usub_val hi2).2
              rw [h1, hn]; rfl
            obtain ⟨q1, hq1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            obtain ⟨r1, st2⟩ := q1
            have hrec1 := ih (h := ty0) hi2v hrel hinv hq1
            rw [show absU i2 = m from hi2v] at hrec1
            show AOut absU (fun _ => True) pers lst body st1
              ((bvarBoundArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
            rw [bvarBoundArmBind]
            cases hr1c : r1 with
            | Err e =>
              rw [hr1c] at hp hrec1
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              exact aout_err_bind hrec1
            | Ok x1 =>
              rw [hr1c] at hp hrec1
              obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
              rw [StateT.run_bind, hx1]
              obtain ⟨q2, hq2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              obtain ⟨r2, st3⟩ := q2
              have hrec2 := ih (h := b0) hi2v hrel1 hinv1 hq2
              rw [show absU i2 = m from hi2v] at hrec2
              obtain ⟨r3, hr3, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              show AOut absU (fun _ => True) pers lst r3 st3
                ((do let y ← bvarBoundGo m (absEIdx b0)
                     pure (max (absU x1) (y - 1))).run lst1)
              cases hr2c : r2 with
              | Err e =>
                rw [hr2c] at hr3 hrec2
                have ho3 : (core.result.Result.Err e :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                exact aout_err_bind hrec2
              | Ok y1 =>
                rw [hr2c] at hr3 hrec2
                obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
                rw [StateT.run_bind, hx2]
                obtain ⟨i4, hi4, hr3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr3
                obtain ⟨i3, hi3, hr3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr3
                have ho3 : (core.result.Result.Ok i3 :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
                show Except.ok (max (absU x1) (absU y1 - 1), lst2) = _
                rw [show absU i3 = max (absU x1) (absU i4) from
                    ConRon.Refine.Expr.max_u64_val hi3,
                  show absU i4 = absU y1 - 1 from sub_nat_val hi4]
          | LetE ty0 v0 b0 =>
            obtain ⟨i2, hi2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hi2v : i2.val = m := by
              have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
                (ConRon.Refine.Nat.usub_val hi2).2
              rw [h1, hn]; rfl
            obtain ⟨q1, hq1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            obtain ⟨r1, st2⟩ := q1
            have hrec1 := ih (h := ty0) hi2v hrel hinv hq1
            rw [show absU i2 = m from hi2v] at hrec1
            show AOut absU (fun _ => True) pers lst body st1
              ((bvarBoundArmLet m (absEIdx ty0) (absEIdx v0) (absEIdx b0)).run lst)
            rw [bvarBoundArmLet]
            cases hr1c : r1 with
            | Err e =>
              rw [hr1c] at hp hrec1
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              exact aout_err_bind hrec1
            | Ok x1 =>
              rw [hr1c] at hp hrec1
              obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
              rw [StateT.run_bind, hx1]
              obtain ⟨q2, hq2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              obtain ⟨r2, st3⟩ := q2
              have hrec2 := ih (h := v0) hi2v hrel1 hinv1 hq2
              rw [show absU i2 = m from hi2v] at hrec2
              show AOut absU (fun _ => True) pers lst body st1
                ((do let y ← bvarBoundGo m (absEIdx v0)
                     let z ← bvarBoundGo m (absEIdx b0)
                     pure (max (max (absU x1) y) (z - 1))).run lst1)
              cases hr2c : r2 with
              | Err e =>
                rw [hr2c] at hp hrec2
                have hpp := Result.ok_injective hp
                simp only [Prod.mk.injEq] at hpp
                obtain ⟨rfl, rfl⟩ := hpp
                exact aout_err_bind hrec2
              | Ok y1 =>
                rw [hr2c] at hp hrec2
                obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
                rw [StateT.run_bind, hx2]
                obtain ⟨q3, hq3, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
                obtain ⟨r3, st4⟩ := q3
                have hrec3 := ih (h := b0) hi2v hrel2 hinv2 hq3
                rw [show absU i2 = m from hi2v] at hrec3
                obtain ⟨r4, hr4, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
                have hpp := Result.ok_injective hp
                simp only [Prod.mk.injEq] at hpp
                obtain ⟨rfl, rfl⟩ := hpp
                show AOut absU (fun _ => True) pers lst r4 st4
                  ((do let z ← bvarBoundGo m (absEIdx b0)
                       pure (max (max (absU x1) (absU y1)) (z - 1))).run lst2)
                cases hr3c : r3 with
                | Err e =>
                  rw [hr3c] at hr4 hrec3
                  have ho4 : (core.result.Result.Err e :
                      core.result.Result Std.U64 _) = r4 := Result.ok_injective hr4
                  rw [← ho4]
                  exact aout_err_bind hrec3
                | Ok z1 =>
                  rw [hr3c] at hr4 hrec3
                  obtain ⟨lst3, hx3, hrel3, hinv3, hext3, -⟩ := hrec3
                  rw [StateT.run_bind, hx3]
                  obtain ⟨i5, hi5, hr4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr4
                  obtain ⟨i6, hi6, hr4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr4
                  obtain ⟨i7, hi7, hr4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr4
                  have ho4 : (core.result.Result.Ok i7 :
                      core.result.Result Std.U64 _) = r4 := Result.ok_injective hr4
                  rw [← ho4]
                  refine AOut.ok ?_ hrel3 hinv3
                    (Ext.trans hext1 (Ext.trans hext2 hext3)) trivial
                  show Except.ok
                    (max (max (absU x1) (absU y1)) (absU z1 - 1), lst3) = _
                  rw [show absU i7 = max (absU i5) (absU i6) from
                      ConRon.Refine.Expr.max_u64_val hi7,
                    show absU i5 = max (absU x1) (absU y1) from
                      ConRon.Refine.Expr.max_u64_val hi5,
                    show absU i6 = absU z1 - 1 from sub_nat_val hi6]
      cases hbc : body with
      | Err e =>
        rw [hbc] at hrun hnode
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact aout_err_bind hnode
      | Ok r1 =>
        rw [hbc] at hrun hnode
        obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨st2, hst2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have ho := Result.ok_injective hrun
        rw [← ho]
        obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hnode
        rw [StateT.run_bind, hx1]
        have hee : e1 = h := dupId_eidx h e1 he1
        rw [hee] at hst2
        obtain ⟨lst2, hs2, hrel2, hinv2, hext2⟩ := bvar_b_set_run hrel1 hinv1 hst2
        show AOut absU (fun _ => True) pers lst (core.result.Result.Ok r1) st2
          ((do
            let _ ← Arena.bvarBSet (absEIdx h) (absU r1)
            pure (absU r1)).run lst1)
        rw [StateT.run_bind, hs2]
        exact AOut.ok rfl hrel2 hinv2 (Ext.trans hext1 hext2) trivial

theorem bvar_bound_go_refines {pers st lst} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_bound_go pers st fuel h = ok o) :
    Sim absU (fun _ => True) pers lst o (bvarBoundGo (absU fuel) (absEIdx h)) :=
  bvar_bound_go_aux fuel.val rfl hrel hinv hrun

/-- **The twin's arm dispatch of `fvarRangeGo`, transcribed** — the port
inlines the arms where the twin (task #97-P3-1's split) names them. -/
def fvarRangeNodeSpec (fuel : Nat) : ENodeView → AM Nat
  | .fvar idx _ => pure (idx + 1)
  | .bvar _ | .sort _ | .const _ _ | .lit _ => pure 0
  | .app f a => fvarRangeArmApp fuel f a
  | .lam ty body _ | .forallE ty body _ => fvarRangeArmBind fuel ty body
  | .letE ty val body => fvarRangeArmLet fuel ty val body
  | .proj _ _ sub => fvarRangeGo fuel sub

/-- The owed twin equation, in the port's own association: the memo probe,
the node step, the memo write. -/
theorem fvarRangeGo_unfold (fuel : Nat) (h : EIdx) :
    fvarRangeGo (fuel + 1) h = (do
      match ← fvarBGet h with
      | some r => pure r
      | none => do
        let r ← (do let w ← view h; fvarRangeNodeSpec fuel w)
        fvarBSet h r
        pure r) := by
  rw [fvarRangeGo_succ]
  simp only [fvarRangeNodeSpec, fvarRangeArmApp, fvarRangeArmBind,
    fvarRangeArmLet]
  congr 1

/-- The `bvar_bound_go` statement at one fuel value. -/
def FRGoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {fuel : Std.U64} {h : arena.handle.EIdx} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st →
    arena.expr_ops.fvar_range_go pers st fuel h = ok o →
    Sim absU (fun _ => True) pers lst o (fvarRangeGo (absU fuel) (absEIdx h))

private theorem fvar_range_go_aux (n : Nat) : FRGoAt n := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.fvar_range_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hrrv := fail_run hrr
    have ho := Result.ok_injective hrun
    rw [← ho, hrrv]
    show AErrSim _ ((fvarRangeGo (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, fvarRangeGo_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.fvar_range_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hget := fvar_b_get_run hrel hinv hop
    show AOut absU (fun _ => True) pers lst o.1 o.2
      ((fvarRangeGo (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = m + 1 from hn, fvarRangeGo_unfold, StateT.run_bind, hget]
    cases hoc : op with
    | some r =>
      rw [hoc] at hrun
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
    | none =>
      rw [hoc] at hrun
      show AOut absU (fun _ => True) pers lst o.1 o.2
        ((do
          let r ← (do let w ← Arena.view (absEIdx h); fvarRangeNodeSpec m w)
          fvarBSet (absEIdx h) r
          pure r).run lst)
      obtain ⟨rv, hrv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hview := view_run hrel hinv hrv
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨st1, body⟩ := p
      have hnode : AOut absU (fun _ => True) pers lst body st1
          ((do let w ← Arena.view (absEIdx h); fvarRangeNodeSpec m w).run lst) := by
        cases hrc : rv with
        | Err e =>
          rw [hrc] at hp hview
          have hpp := Result.ok_injective hp
          simp only [Prod.mk.injEq] at hpp
          obtain ⟨rfl, rfl⟩ := hpp
          show AErrSim e _
          rw [StateT.run_bind]
          exact AErrSim.bind hview _
        | Ok ev =>
          rw [hrc] at hp hview
          obtain ⟨lst0, hx, -, -, -, -⟩ := hview
          have hlst : lst0 = lst := view_run_state hx
          rw [hlst] at hx
          rw [StateT.run_bind, hx]
          cases ev with
          | BVar _ =>
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
          | FVar idx0 _ =>
            obtain ⟨i1, hi1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            refine AOut.ok ?_ hrel hinv (Ext.refl _) trivial
            show Except.ok (absU idx0 + 1, lst) = _
            rw [show absU i1 = absU idx0 + 1 from ConRon.Refine.Nat.uadd_val hi1]
          | «Sort» _ =>
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
          | Const _ _ =>
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
          | Lit _ =>
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
          | Proj _ _ s0 =>
            obtain ⟨i2, hi2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hi2v : i2.val = m := by
              have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
                (ConRon.Refine.Nat.usub_val hi2).2
              rw [h1, hn]; rfl
            obtain ⟨q1, hq1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            obtain ⟨r1, st2⟩ := q1
            have hrec1 := ih (h := s0) hi2v hrel hinv hq1
            rw [show absU i2 = m from hi2v] at hrec1
            have hpp := Result.ok_injective hp
            simp only [Prod.mk.injEq] at hpp
            obtain ⟨rfl, rfl⟩ := hpp
            exact hrec1
          | App f0 a0 =>
            obtain ⟨i2, hi2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hi2v : i2.val = m := by
              have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
                (ConRon.Refine.Nat.usub_val hi2).2
              rw [h1, hn]; rfl
            obtain ⟨q1, hq1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            obtain ⟨r1, st2⟩ := q1
            have hrec1 := ih (h := f0) hi2v hrel hinv hq1
            rw [show absU i2 = m from hi2v] at hrec1
            show AOut absU (fun _ => True) pers lst body st1
              ((fvarRangeArmApp m (absEIdx f0) (absEIdx a0)).run lst)
            rw [fvarRangeArmApp]
            cases hr1c : r1 with
            | Err e =>
              rw [hr1c] at hp hrec1
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              exact aout_err_bind hrec1
            | Ok x1 =>
              rw [hr1c] at hp hrec1
              obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
              rw [StateT.run_bind, hx1]
              obtain ⟨q2, hq2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              obtain ⟨r2, st3⟩ := q2
              have hrec2 := ih (h := a0) hi2v hrel1 hinv1 hq2
              rw [show absU i2 = m from hi2v] at hrec2
              obtain ⟨r3, hr3, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              show AOut absU (fun _ => True) pers lst r3 st3
                ((do let y ← fvarRangeGo m (absEIdx a0)
                     pure (max (absU x1) y)).run lst1)
              cases hr2c : r2 with
              | Err e =>
                rw [hr2c] at hr3 hrec2
                have ho3 : (core.result.Result.Err e :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                exact aout_err_bind hrec2
              | Ok y1 =>
                rw [hr2c] at hr3 hrec2
                obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
                rw [StateT.run_bind, hx2]
                obtain ⟨i3, hi3, hr3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr3
                have ho3 : (core.result.Result.Ok i3 :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
                show Except.ok (max (absU x1) (absU y1), lst2) = _
                rw [show absU i3 = max (absU x1) (absU y1) from
                  ConRon.Refine.Expr.max_u64_val hi3]
          | Lam ty0 b0 mm =>
            obtain ⟨i2, hi2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hi2v : i2.val = m := by
              have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
                (ConRon.Refine.Nat.usub_val hi2).2
              rw [h1, hn]; rfl
            obtain ⟨q1, hq1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            obtain ⟨r1, st2⟩ := q1
            have hrec1 := ih (h := ty0) hi2v hrel hinv hq1
            rw [show absU i2 = m from hi2v] at hrec1
            show AOut absU (fun _ => True) pers lst body st1
              ((fvarRangeArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
            rw [fvarRangeArmBind]
            cases hr1c : r1 with
            | Err e =>
              rw [hr1c] at hp hrec1
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              exact aout_err_bind hrec1
            | Ok x1 =>
              rw [hr1c] at hp hrec1
              obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
              rw [StateT.run_bind, hx1]
              obtain ⟨q2, hq2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              obtain ⟨r2, st3⟩ := q2
              have hrec2 := ih (h := b0) hi2v hrel1 hinv1 hq2
              rw [show absU i2 = m from hi2v] at hrec2
              obtain ⟨r3, hr3, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              show AOut absU (fun _ => True) pers lst r3 st3
                ((do let y ← fvarRangeGo m (absEIdx b0)
                     pure (max (absU x1) y)).run lst1)
              cases hr2c : r2 with
              | Err e =>
                rw [hr2c] at hr3 hrec2
                have ho3 : (core.result.Result.Err e :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                exact aout_err_bind hrec2
              | Ok y1 =>
                rw [hr2c] at hr3 hrec2
                obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
                rw [StateT.run_bind, hx2]
                obtain ⟨i3, hi3, hr3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr3
                have ho3 : (core.result.Result.Ok i3 :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
                show Except.ok (max (absU x1) (absU y1), lst2) = _
                rw [show absU i3 = max (absU x1) (absU y1) from
                  ConRon.Refine.Expr.max_u64_val hi3]
          | ForallE ty0 b0 mm =>
            obtain ⟨i2, hi2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hi2v : i2.val = m := by
              have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
                (ConRon.Refine.Nat.usub_val hi2).2
              rw [h1, hn]; rfl
            obtain ⟨q1, hq1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            obtain ⟨r1, st2⟩ := q1
            have hrec1 := ih (h := ty0) hi2v hrel hinv hq1
            rw [show absU i2 = m from hi2v] at hrec1
            show AOut absU (fun _ => True) pers lst body st1
              ((fvarRangeArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
            rw [fvarRangeArmBind]
            cases hr1c : r1 with
            | Err e =>
              rw [hr1c] at hp hrec1
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              exact aout_err_bind hrec1
            | Ok x1 =>
              rw [hr1c] at hp hrec1
              obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
              rw [StateT.run_bind, hx1]
              obtain ⟨q2, hq2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              obtain ⟨r2, st3⟩ := q2
              have hrec2 := ih (h := b0) hi2v hrel1 hinv1 hq2
              rw [show absU i2 = m from hi2v] at hrec2
              obtain ⟨r3, hr3, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              show AOut absU (fun _ => True) pers lst r3 st3
                ((do let y ← fvarRangeGo m (absEIdx b0)
                     pure (max (absU x1) y)).run lst1)
              cases hr2c : r2 with
              | Err e =>
                rw [hr2c] at hr3 hrec2
                have ho3 : (core.result.Result.Err e :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                exact aout_err_bind hrec2
              | Ok y1 =>
                rw [hr2c] at hr3 hrec2
                obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
                rw [StateT.run_bind, hx2]
                obtain ⟨i3, hi3, hr3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr3
                have ho3 : (core.result.Result.Ok i3 :
                    core.result.Result Std.U64 _) = r3 := Result.ok_injective hr3
                rw [← ho3]
                refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
                show Except.ok (max (absU x1) (absU y1), lst2) = _
                rw [show absU i3 = max (absU x1) (absU y1) from
                  ConRon.Refine.Expr.max_u64_val hi3]
          | LetE ty0 v0 b0 =>
            obtain ⟨i2, hi2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            have hi2v : i2.val = m := by
              have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
                (ConRon.Refine.Nat.usub_val hi2).2
              rw [h1, hn]; rfl
            obtain ⟨q1, hq1, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
            obtain ⟨r1, st2⟩ := q1
            have hrec1 := ih (h := ty0) hi2v hrel hinv hq1
            rw [show absU i2 = m from hi2v] at hrec1
            show AOut absU (fun _ => True) pers lst body st1
              ((fvarRangeArmLet m (absEIdx ty0) (absEIdx v0) (absEIdx b0)).run lst)
            rw [fvarRangeArmLet]
            cases hr1c : r1 with
            | Err e =>
              rw [hr1c] at hp hrec1
              have hpp := Result.ok_injective hp
              simp only [Prod.mk.injEq] at hpp
              obtain ⟨rfl, rfl⟩ := hpp
              exact aout_err_bind hrec1
            | Ok x1 =>
              rw [hr1c] at hp hrec1
              obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
              rw [StateT.run_bind, hx1]
              obtain ⟨q2, hq2, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
              obtain ⟨r2, st3⟩ := q2
              have hrec2 := ih (h := v0) hi2v hrel1 hinv1 hq2
              rw [show absU i2 = m from hi2v] at hrec2
              show AOut absU (fun _ => True) pers lst body st1
                ((do let y ← fvarRangeGo m (absEIdx v0)
                     let z ← fvarRangeGo m (absEIdx b0)
                     pure (max (max (absU x1) y) z)).run lst1)
              cases hr2c : r2 with
              | Err e =>
                rw [hr2c] at hp hrec2
                have hpp := Result.ok_injective hp
                simp only [Prod.mk.injEq] at hpp
                obtain ⟨rfl, rfl⟩ := hpp
                exact aout_err_bind hrec2
              | Ok y1 =>
                rw [hr2c] at hp hrec2
                obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
                rw [StateT.run_bind, hx2]
                obtain ⟨q3, hq3, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
                obtain ⟨r3, st4⟩ := q3
                have hrec3 := ih (h := b0) hi2v hrel2 hinv2 hq3
                rw [show absU i2 = m from hi2v] at hrec3
                obtain ⟨r4, hr4, hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp
                have hpp := Result.ok_injective hp
                simp only [Prod.mk.injEq] at hpp
                obtain ⟨rfl, rfl⟩ := hpp
                show AOut absU (fun _ => True) pers lst r4 st4
                  ((do let z ← fvarRangeGo m (absEIdx b0)
                       pure (max (max (absU x1) (absU y1)) z)).run lst2)
                cases hr3c : r3 with
                | Err e =>
                  rw [hr3c] at hr4 hrec3
                  have ho4 : (core.result.Result.Err e :
                      core.result.Result Std.U64 _) = r4 := Result.ok_injective hr4
                  rw [← ho4]
                  exact aout_err_bind hrec3
                | Ok z1 =>
                  rw [hr3c] at hr4 hrec3
                  obtain ⟨lst3, hx3, hrel3, hinv3, hext3, -⟩ := hrec3
                  rw [StateT.run_bind, hx3]
                  obtain ⟨i5, hi5, hr4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr4
                  obtain ⟨i7, hi7, hr4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr4
                  have ho4 : (core.result.Result.Ok i7 :
                      core.result.Result Std.U64 _) = r4 := Result.ok_injective hr4
                  rw [← ho4]
                  refine AOut.ok ?_ hrel3 hinv3
                    (Ext.trans hext1 (Ext.trans hext2 hext3)) trivial
                  show Except.ok
                    (max (max (absU x1) (absU y1)) (absU z1), lst3) = _
                  rw [show absU i7 = max (absU i5) (absU z1) from
                      ConRon.Refine.Expr.max_u64_val hi7,
                    show absU i5 = max (absU x1) (absU y1) from
                      ConRon.Refine.Expr.max_u64_val hi5]
      cases hbc : body with
      | Err e =>
        rw [hbc] at hrun hnode
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact aout_err_bind hnode
      | Ok r1 =>
        rw [hbc] at hrun hnode
        obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨st2, hst2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have ho := Result.ok_injective hrun
        rw [← ho]
        obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hnode
        rw [StateT.run_bind, hx1]
        have hee : e1 = h := dupId_eidx h e1 he1
        rw [hee] at hst2
        obtain ⟨lst2, hs2, hrel2, hinv2, hext2⟩ := fvar_b_set_run hrel1 hinv1 hst2
        show AOut absU (fun _ => True) pers lst (core.result.Result.Ok r1) st2
          ((do
            let _ ← Arena.fvarBSet (absEIdx h) (absU r1)
            pure (absU r1)).run lst1)
        rw [StateT.run_bind, hs2]
        exact AOut.ok rfl hrel2 hinv2 (Ext.trans hext1 hext2) trivial

theorem fvar_range_go_refines {pers st lst} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_range_go pers st fuel h = ok o) :
    Sim absU (fun _ => True) pers lst o (fvarRangeGo (absU fuel) (absEIdx h)) :=
  fvar_range_go_aux fuel.val rfl hrel hinv hrun

/-! ## The four range entry points and their two memo brackets -/

theorem bvar_bound_memo_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_bound_memo pers st fuel e = ok o) :
    Sim absU (fun _ => True) pers lst o (bvarBoundMemo (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.bvar_bound_memo] at hrun
  obtain ⟨st1, hst1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st2⟩ := q
  obtain ⟨lst1, hc1, hrel1, hinv1, hext1⟩ := bvar_b_clear_run hrel hinv hst1
  have hgo := bvar_bound_go_refines hrel1 hinv1 hq
  show AOut absU (fun _ => True) pers lst o.1 o.2
    ((do
      let _ ← Arena.bvarBClear
      let r ← bvarBoundGo (absU fuel) (absEIdx e)
      let _ ← Arena.bvarBClear
      pure r).run lst)
  rw [StateT.run_bind, hc1]
  show AOut absU (fun _ => True) pers lst o.1 o.2
    ((do
      let r ← bvarBoundGo (absU fuel) (absEIdx e)
      let _ ← Arena.bvarBClear
      pure r).run lst1)
  cases hrc : r with
  | Err er =>
    rw [hrc] at hrun hgo
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact aout_err_bind hgo
  | Ok r1 =>
    rw [hrc] at hrun hgo
    obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hgo
    rw [StateT.run_bind, hx2]
    obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    obtain ⟨lst3, hc3, hrel3, hinv3, hext3⟩ := bvar_b_clear_run hrel2 hinv2 hst3
    show AOut absU (fun _ => True) pers lst (core.result.Result.Ok r1) st3
      ((do
        let _ ← Arena.bvarBClear
        pure (absU r1)).run lst2)
    rw [StateT.run_bind, hc3]
    exact AOut.ok rfl hrel3 hinv3
      (Ext.trans hext1 (Ext.trans hext2 hext3)) trivial

theorem fvar_range_memo_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_range_memo pers st fuel e = ok o) :
    Sim absU (fun _ => True) pers lst o (fvarRangeMemo (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.fvar_range_memo] at hrun
  obtain ⟨st1, hst1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st2⟩ := q
  obtain ⟨lst1, hc1, hrel1, hinv1, hext1⟩ := fvar_b_clear_run hrel hinv hst1
  have hgo := fvar_range_go_refines hrel1 hinv1 hq
  show AOut absU (fun _ => True) pers lst o.1 o.2
    ((do
      let _ ← Arena.fvarBClear
      let r ← fvarRangeGo (absU fuel) (absEIdx e)
      let _ ← Arena.fvarBClear
      pure r).run lst)
  rw [StateT.run_bind, hc1]
  show AOut absU (fun _ => True) pers lst o.1 o.2
    ((do
      let r ← fvarRangeGo (absU fuel) (absEIdx e)
      let _ ← Arena.fvarBClear
      pure r).run lst1)
  cases hrc : r with
  | Err er =>
    rw [hrc] at hrun hgo
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact aout_err_bind hgo
  | Ok r1 =>
    rw [hrc] at hrun hgo
    obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hgo
    rw [StateT.run_bind, hx2]
    obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    obtain ⟨lst3, hc3, hrel3, hinv3, hext3⟩ := fvar_b_clear_run hrel2 hinv2 hst3
    show AOut absU (fun _ => True) pers lst (core.result.Result.Ok r1) st3
      ((do
        let _ ← Arena.fvarBClear
        pure (absU r1)).run lst2)
    rw [StateT.run_bind, hc3]
    exact AOut.ok rfl hrel3 hinv3
      (Ext.trans hext1 (Ext.trans hext2 hext3)) trivial

theorem bvar_b_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.bvar_b pers st fuel e = ok o) :
    Sim absU (fun _ => True) pers lst o (bvarB (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.bvar_b] at hrun
  obtain ⟨der, hder, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨sr, hsr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hderE := hder
  rw [arena.monad.derived_e] at hderE
  obtain ⟨hbv, -, -⟩ := derObsE_fields (estore_derived_abs hrel.store hderE)
  have hbb := ConRon.Refine.Expr.bvar_of_data_val hr
  have hsrv := ConRon.Refine.Expr.sat_range_val hsr
  have hbn : (ConLeche.bvarOfData (lst.store.derived (absEIdx e))).toNat = absU r := by
    rw [hbv]; exact hbb.symm
  show AOut absU (fun _ => True) pers lst o.1 o.2
    ((do
      let d ← Arena.derivedE (absEIdx e)
      if (ConLeche.bvarOfData d).toNat == ConLeche.satRange then
        bvarBoundMemo (absU fuel) (absEIdx e)
      else pure (ConLeche.bvarOfData d).toNat).run lst)
  rw [StateT.run_bind,
    show (Arena.derivedE (absEIdx e)).run lst
      = .ok (lst.store.derived (absEIdx e), lst) from rfl]
  show AOut absU (fun _ => True) pers lst o.1 o.2
    ((if ((ConLeche.bvarOfData (lst.store.derived (absEIdx e))).toNat
            == ConLeche.satRange) = true then
        bvarBoundMemo (absU fuel) (absEIdx e)
      else pure (ConLeche.bvarOfData (lst.store.derived (absEIdx e))).toNat).run lst)
  by_cases hc : r = sr
  · rw [if_pos hc] at hrun
    rw [if_pos (show ((ConLeche.bvarOfData (lst.store.derived (absEIdx e))).toNat
        == ConLeche.satRange) = true by rw [hbn, hc, ← hsrv]; simp)]
    exact bvar_bound_memo_refines hrel hinv hrun
  · rw [if_neg hc] at hrun
    rw [if_neg (show ¬ (((ConLeche.bvarOfData (lst.store.derived (absEIdx e))).toNat
        == ConLeche.satRange) = true) by
      rw [hbn, ← hsrv]
      simp only [beq_iff_eq]
      intro hz
      exact hc (Std.UScalar.eq_of_val_eq hz))]
    have ho := Result.ok_injective hrun
    rw [← ho]
    refine AOut.ok ?_ hrel hinv (Ext.refl _) trivial
    show Except.ok ((ConLeche.bvarOfData (lst.store.derived (absEIdx e))).toNat, lst)
      = _
    rw [hbn]

theorem fvar_b_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_b pers st fuel e = ok o) :
    Sim absU (fun _ => True) pers lst o (fvarB (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.fvar_b] at hrun
  obtain ⟨der, hder, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨sr, hsr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hderE := hder
  rw [arena.monad.derived_e] at hderE
  obtain ⟨-, hfv, -⟩ := derObsE_fields (estore_derived_abs hrel.store hderE)
  have hbb := ConRon.Refine.Expr.fvar_of_data_val hr
  have hsrv := ConRon.Refine.Expr.sat_range_val hsr
  have hbn : (ConLeche.fvarOfData (lst.store.derived (absEIdx e))).toNat = absU r := by
    rw [hfv]; exact hbb.symm
  show AOut absU (fun _ => True) pers lst o.1 o.2
    ((do
      let d ← Arena.derivedE (absEIdx e)
      if (ConLeche.fvarOfData d).toNat == ConLeche.satRange then
        fvarRangeMemo (absU fuel) (absEIdx e)
      else pure (ConLeche.fvarOfData d).toNat).run lst)
  rw [StateT.run_bind,
    show (Arena.derivedE (absEIdx e)).run lst
      = .ok (lst.store.derived (absEIdx e), lst) from rfl]
  show AOut absU (fun _ => True) pers lst o.1 o.2
    ((if ((ConLeche.fvarOfData (lst.store.derived (absEIdx e))).toNat
            == ConLeche.satRange) = true then
        fvarRangeMemo (absU fuel) (absEIdx e)
      else pure (ConLeche.fvarOfData (lst.store.derived (absEIdx e))).toNat).run lst)
  by_cases hc : r = sr
  · rw [if_pos hc] at hrun
    rw [if_pos (show ((ConLeche.fvarOfData (lst.store.derived (absEIdx e))).toNat
        == ConLeche.satRange) = true by rw [hbn, hc, ← hsrv]; simp)]
    exact fvar_range_memo_refines hrel hinv hrun
  · rw [if_neg hc] at hrun
    rw [if_neg (show ¬ (((ConLeche.fvarOfData (lst.store.derived (absEIdx e))).toNat
        == ConLeche.satRange) = true) by
      rw [hbn, ← hsrv]
      simp only [beq_iff_eq]
      intro hz
      exact hc (Std.UScalar.eq_of_val_eq hz))]
    have ho := Result.ok_injective hrun
    rw [← ho]
    refine AOut.ok ?_ hrel hinv (Ext.refl _) trivial
    show Except.ok ((ConLeche.fvarOfData (lst.store.derived (absEIdx e))).toNat, lst)
      = _
    rw [hbn]

theorem has_fvar_fast_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.has_fvar_fast pers st fuel e = ok o) :
    Sim id (fun _ => True) pers lst o (hasFvarFast (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.has_fvar_fast] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st1⟩ := q
  have hfb := fvar_b_refines hrel hinv hq
  show AOut id (fun _ => True) pers lst o.1 o.2
    ((do
      let r ← fvarB (absU fuel) (absEIdx e)
      pure (r != 0)).run lst)
  cases hrc : r with
  | Err er =>
    rw [hrc] at hrun hfb
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact aout_err_bind hfb
  | Ok r1 =>
    rw [hrc] at hrun hfb
    obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hfb
    rw [StateT.run_bind, hx1]
    have ho := Result.ok_injective hrun
    rw [← ho]
    refine AOut.ok ?_ hrel1 hinv1 hext1 trivial
    show Except.ok ((absU r1 != 0), lst1) = Except.ok (id (r1 != 0#u64), lst1)
    have hb : ((absU r1 != 0) : Bool) = id (r1 != 0#u64) := by
      show ((absU r1 != 0) : Bool) = (r1 != 0#u64)
      by_cases hz : r1 = 0#u64
      · subst hz; rfl
      · have hne : absU r1 ≠ 0 := fun hzz => hz (Std.UScalar.eq_of_val_eq hzz)
        have h1 : ((absU r1 != 0) : Bool) = true := by simp [hne]
        have h2 : ((r1 != 0#u64) : Bool) = true := by simp [hz]
        rw [h1, h2]
    exact congrArg (fun b => Except.ok ((b : Bool), lst1)) hb

theorem loose_bvars_bounded_fast_refines {pers st lst} {fuel k : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.loose_bvars_bounded_fast pers st fuel k e = ok o) :
    Sim id (fun _ => True) pers lst o
      (looseBVarsBoundedFast (absU fuel) (absU k) (absEIdx e)) := by
  rw [arena.expr_ops.loose_bvars_bounded_fast] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st1⟩ := q
  have hbb := bvar_b_refines hrel hinv hq
  show AOut id (fun _ => True) pers lst o.1 o.2
    ((do
      let r ← bvarB (absU fuel) (absEIdx e)
      pure (decide (r ≤ absU k))).run lst)
  cases hrc : r with
  | Err er =>
    rw [hrc] at hrun hbb
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact aout_err_bind hbb
  | Ok r1 =>
    rw [hrc] at hrun hbb
    obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hbb
    rw [StateT.run_bind, hx1]
    have ho := Result.ok_injective hrun
    rw [← ho]
    refine AOut.ok ?_ hrel1 hinv1 hext1 trivial
    show Except.ok (decide (absU r1 ≤ absU k), lst1)
      = Except.ok (id (decide (r1 ≤ k)), lst1)
    have hb : (decide (absU r1 ≤ absU k) : Bool) = id (decide (r1 ≤ k)) :=
      decide_eq_decide.mpr ⟨fun hx => by scalar_tac, fun hx => by scalar_tac⟩
    exact congrArg (fun b => Except.ok ((b : Bool), lst1)) hb










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


/-! ## The axiom census

The packed-range family — the two memoised walks, their two brackets and the
four entry points — plus the two owed twin equations and `sub_nat_val`, at
the three standard axioms and nothing else.  Everything else in this file is
still a `sorry`: see the module note. -/

/-- info: 'ConRon.Refine2.bvar_bound_go_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bvar_bound_go_refines

/-- info: 'ConRon.Refine2.bvar_bound_memo_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bvar_bound_memo_refines

/-- info: 'ConRon.Refine2.fvar_range_go_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvar_range_go_refines

/-- info: 'ConRon.Refine2.fvar_range_memo_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvar_range_memo_refines

/-- info: 'ConRon.Refine2.bvar_b_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bvar_b_refines

/-- info: 'ConRon.Refine2.fvar_b_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvar_b_refines

/-- info: 'ConRon.Refine2.has_fvar_fast_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms has_fvar_fast_refines

/-- info: 'ConRon.Refine2.loose_bvars_bounded_fast_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loose_bvars_bounded_fast_refines

/-- info: 'ConRon.Refine2.bvarBoundGo_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bvarBoundGo_unfold

/-- info: 'ConRon.Refine2.fvarRangeGo_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvarRangeGo_unfold

/-- info: 'ConRon.Refine2.sub_nat_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sub_nat_val


/-- info: 'ConRon.Refine2.intern_rebuilt_bvar_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_rebuilt_bvar_refines

/-- info: 'ConRon.Refine2.intern_rebuilt_fvar_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_rebuilt_fvar_refines

/-- info: 'ConRon.Refine2.intern_rebuilt_sort_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_rebuilt_sort_refines

/-- info: 'ConRon.Refine2.intern_rebuilt_const_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_rebuilt_const_refines

/-- info: 'ConRon.Refine2.intern_rebuilt_app_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_rebuilt_app_refines

/-- info: 'ConRon.Refine2.intern_rebuilt_let_e_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_rebuilt_let_e_refines

/-- info: 'ConRon.Refine2.intern_rebuilt_lit_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_rebuilt_lit_refines

/-- info: 'ConRon.Refine2.intern_rebuilt_proj_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_rebuilt_proj_refines

/-- info: 'ConRon.Refine2.intern_rebuilt_bind_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_rebuilt_bind_i_refines

end ConRon.Refine2
