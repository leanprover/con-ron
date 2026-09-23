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
import ConRon.Refine2.ExprOps.Pure
import ConRon.Refine2.ExprOps.Read
import ConRon.Arena.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.ExprOps (aout_err_bind aout_rebase EResolves)

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

@[simp] theorem absEIdxArr_size (v : alloc.vec.Vec arena.handle.EIdx) :
    (absEIdxArr v).size = v.val.length := by
  simp [absEIdxArr]

theorem absEIdxArr_get (v : alloc.vec.Vec arena.handle.EIdx) (k : Nat)
    (h : k < v.val.length) :
    (absEIdxArr v)[k]'(by simpa using h) = absEIdx (v.val[k]) := by
  simp [absEIdxArr]


/-- **The renaming dictionary against the twin's function** (`rename_consts`'s
one higher-order argument).  Aeneas renders the `NIdxToNIdx` trait method as
`Result`-valued because a trait method may fail; the twin's argument is a
total `NIdx → NIdx`.  Read it forward from `= ok`, as everything in this tier
is: *whatever the dictionary answers, the twin's function answers the
abstraction of it.* -/
def RenameRel {F : Type} (inst : arena.expr_ops.NIdxToNIdx F) (f : F)
    (g : NIdx → NIdx) : Prop :=
  ∀ n r, inst.rename f n = ok r → g (absNIdx n) = absNIdx r

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

/-! ## The `intern` flag lemmas moved into `Specs.lean` (task #97-P5-Twin
round 2)

Task #97-P5-Mut wrote eight store-level `intern_*_flags` and nine
`arena::monad` wrappers HERE — 661 lines — and said so in its own note:
*"they are one line INSIDE `estore_intern_*_abs`, where the tier select and
the six leaves are already split; they belong in `Specs.lean` beside the
`_abs` lemmas they shadow and are here only because that file is another lane
this round."*  It is this round's lane, so they are there now: each of the
eight `estore_intern_{fvar, sort, const, app, proj, let_e, lam_i,
forall_e_i}_abs` grows the third top-level conjunct
`rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on` that
`estore_intern_bvar_abs` has carried since task #97-P5-3 round 3 §4, and each
arm discharges it in one line.  **661 lines out, 56 lines in**, and the claim
is the same one: it is still UNCONDITIONAL (the third conjunct sits beside the
`Ok` and `Err` arms, not inside either), so a caller on the error path has it
too.

The four tactic rules those proofs were written to (peel with
`ConRon.Refine.bind_eq_ok_iff.mp`, never `subst`/`rw … at h` on the body,
case on the BOOLEANS, name every `obtain` witness) are task #97-P5-Mut §3 and
are still the rules for an Aeneas `do` chain; they are recorded in DESIGN.md
rather than here. -/


/-! ## Finding 19's scaffolding: what a walk carries that `Sim` does not

**Finding 19 (task #97-P5-Mut).**  `Refine2/Shape.lean`'s `AOut` carries the
run equation, the two invariants and `Ext`, and its `WF` slot is `α → Prop` —
it never sees the twin's POST-state.  Since task #97-P5-Specs put `StoreWF` in
`AStateRel` (finding 16), every `intern_e_*_run` asks its caller for
`hview : lst.store.ViewOK …` — *"the children decode"* — and a walk's children
are its own recursive ANSWERS.  So an interning walk cannot chain: nothing in
its callee's conclusion says the answer decodes.

**The statements of this file are not merely unprovable that way, they are
FALSE as written** wherever the node interned has a child the walk produced.
Take `instantiate1_go_refines`: nothing in `AStateRel`/`AStateInv`/`MemosRel`
constrains the VALUES in the twin's `inst1C`, so a state whose memo maps
`(h, d)` to a handle that decodes nowhere satisfies every hypothesis; the
`app` arm then answers that handle, the caller interns `app r a'`, and
`EWFAt.childOK` — *"every child of a decoding node decodes"* — fails at the
twin's post-store for every rank function, so `AStateRel`'s `storeWF`
conjunct, and with it the conclusion, is false.

`WOutE` below is the fix, and it is deliberately LOCAL: widening `Shape.lean`'s
`WF` slot to `α → AState → Prop` is the same claim tier-wide and touches every
`Sim` statement in `Refine2/**`, which is a coordinator's call and not a lane's.
A walk proves `WOutE` by induction and projects `Sim` at the boundary
(`WOutE.toSim`); the public statement keeps its shape and grows only the
hypotheses the port genuinely needs. -/

/-- **The twin's `intern` hands back a handle that DECODES to the node it
interned.**  Stated at `ECapBMAt` rather than at a non-binder tag (task
#97-P5-Mut round 2), so that the binder arms — where the datum probe hit —
use it too. -/
theorem intern_resolves {ls : EStore} {v : ENodeView} (hwf : StoreWF ls)
    (hview : ls.ViewOK v) (hcap : ECapAt ls v) (hbm : ECapBMAt ls v) :
    (ls.intern v).1.view (ls.intern v).2 = some v := by
  cases hf : ls.find? v with
  | some hh =>
    rw [intern_of_find hf]
    exact EStore.view_of_find hwf hf
  | none =>
    exact EStore.intern_view_spec hwf hview ⟨hcap hf, hbm⟩

/-! ### The datum reader only grows

A binder arm puts back the datum HANDLE it read before its two recursive
calls, so at the intern it needs the handle to still decode to the same datum
— `EViewExt`'s second half.  `intern` and `internBindI` touch the datum array
only by `pushBM`, which `getBM_pushBM_mono` covers, and the node pushes not at
all (`getBM_push` / `getBM_pushBind`). -/

theorem viewBM_internAt_mono (st : EStore) (w : ENodeView) (mi : BMIdx) {i : BMIdx}
    {m : ConLeche.BinderMeta} (h : st.viewBM i = some m) :
    (st.internAt w mi).1.viewBM i = some m := by
  rcases EStore.internAt_cases st w mi with he | he | he <;> rw [he]
  · exact h
  · refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hk => hk
    · exact fun _ _ hk => by rw [ETables.getBM_push]; exact hk
  · refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hk => by rw [ETables.getBM_push]; exact hk
    · exact fun _ _ hk => hk

theorem viewBM_internBM_mono (st : EStore) (m' : ConLeche.BinderMeta) {i : BMIdx}
    {m : ConLeche.BinderMeta} (h : st.viewBM i = some m) :
    (st.internBM m').1.viewBM i = some m := by
  rcases EStore.internBM_cases st m' with he | he | he <;> rw [he]
  · exact h
  · refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hk => hk
    · exact fun _ _ hk => ETables.getBM_pushBM_mono hk
  · refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hk => ETables.getBM_pushBM_mono hk
    · exact fun _ _ hk => hk

theorem viewBM_intern_mono (st : EStore) (w : ENodeView) {i : BMIdx}
    {m : ConLeche.BinderMeta} (h : st.viewBM i = some m) :
    (st.intern w).1.viewBM i = some m := by
  simp only [EStore.intern]
  refine viewBM_internAt_mono _ w _ ?_
  cases w
  case lam _ _ m' => exact viewBM_internBM_mono st m' h
  case forallE _ _ m' => exact viewBM_internBM_mono st m' h
  all_goals exact h

/-- The twin store's `view` and its datum reader only grow.  `Ext`
(`Arena/Denote.lean`) is the DENOTATION half of the same monotonicity and is
what the tier already carries; a walk that will intern a node built from a
handle it read two steps ago needs the `view` half, and a binder arm that puts
back a datum handle it read before its recursive calls needs the `viewBM`
half. -/
def EViewExt (ls ls' : EStore) : Prop :=
  (∀ i v, ls.view i = some v → ls'.view i = some v) ∧
    (∀ i m, ls.viewBM i = some m → ls'.viewBM i = some m) ∧
    (∀ i v, ls.ns.view i = some v → ls'.ns.view i = some v)

theorem EViewExt.refl (ls : EStore) : EViewExt ls ls :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem EViewExt.trans {a b c : EStore} (h1 : EViewExt a b) (h2 : EViewExt b c) :
    EViewExt a c :=
  ⟨fun i v h => h2.1 i v (h1.1 i v h), fun i m h => h2.2.1 i m (h1.2.1 i m h),
    fun i v h => h2.2.2 i v (h1.2.2 i v h)⟩

/-- An expression intern moves neither the name store nor the level stores. -/
theorem lss_intern (st : EStore) (w : ENodeView) : (st.intern w).1.lss = st.lss := by
  simp only [EStore.intern]
  rcases EStore.internAt_cases (st.internBMOfView w).1 w (st.internBMOfView w).2
    with he | he | he <;> rw [he] <;> exact EStore.lss_internBMOfView st w

theorem EViewExt.intern (ls : EStore) (w : ENodeView) : EViewExt ls (ls.intern w).1 :=
  ⟨fun _ _ h => EStore.view_intern_mono _ _ h, fun _ _ h => viewBM_intern_mono _ _ h,
    fun _ _ h => by simp only [EStore.ns, lss_intern]; exact h⟩

/-- `EViewExt` at a name handle. -/
theorem EViewExt.nsres {ls ls' : EStore} (h : EViewExt ls ls') {n : NIdx}
    (hn : (ls.ns.view n).isSome = true) : (ls'.ns.view n).isSome = true := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hn
  rw [h.2.2 n v hv]; rfl

theorem EViewExt.resolves {ls ls' : EStore} (h : EViewExt ls ls') {lst lst' : AState}
    (h1 : lst.store = ls) (h2 : lst'.store = ls') {i : EIdx}
    (hr : EResolves lst i) : EResolves lst' i := by
  show (lst'.store.view i).isSome = true
  rw [h2]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h1 ▸ hr : (ls.view i).isSome = true)
  rw [h.1 i v hv]; rfl

/-- `EViewExt.resolves` at the two stores of two twin states. -/
theorem EViewExt.res {lst lst' : AState} (h : EViewExt lst.store lst'.store) {i : EIdx}
    (hr : EResolves lst i) : EResolves lst' i := h.resolves rfl rfl hr

/-- **A side invariant a walk carries across its steps**, stable under
everything a step that does not write the memo does: the memo tables are the
same and the store only grew.  `MemoRes` below is the one the memoised walks
need; `fun _ => True` is the walks without a memo. -/
def QStable (Q : AState → Prop) : Prop :=
  ∀ l l' : AState, l'.memos = l.memos → EViewExt l.store l'.store → Q l → Q l'

theorem QStable.true : QStable (fun _ => True) := fun _ _ _ _ _ => trivial

/-- **Every handle a walk's memo holds decodes** — finding 19's MEMO half
(task #97-P5-Mut round 2).  `MemosRel` relates the twin's memo to the port's
key-wise and says nothing of the VALUES, so a state whose memo maps a key to a
dangling handle satisfies every hypothesis of a memoised walk; the walk then
answers that handle on the hit, its caller interns a node over it, and
`StoreWF`'s `childOK` fails.  This is the clause that excludes it, stated
locally (a hypothesis of the walk, re-established by its conclusion) and not
in `MemosRel`, which is tier-wide. -/
def MemoRes (sel : Memos → Std.HashMap (EIdx × Nat) EIdx) (lst : AState) : Prop :=
  ∀ (k : EIdx × Nat) (r : EIdx), (sel lst.memos)[k]? = some r → EResolves lst r

theorem MemoRes.stable (sel : Memos → Std.HashMap (EIdx × Nat) EIdx) :
    QStable (MemoRes sel) := by
  intro l l' hm hx hq k r hk
  rw [hm] at hk
  exact hx.res (hq k r hk)

/-- An emptied memo holds nothing. -/
theorem MemoRes.of_empty {sel : Memos → Std.HashMap (EIdx × Nat) EIdx} {lst : AState}
    (h : sel lst.memos = ∅) : MemoRes sel lst := by
  intro k r hk
  rw [h] at hk
  simp at hk

/-- **The outcome of an interning step, with everything a WALK needs**, over
the twin's RUN RESULT (so that a proof can `show` the run it is at, exactly as
`AOut` is used).

`Sim`'s `AOut` carries the run equation, the two invariants and `Ext`, and
task #97-P5-Mut's finding 19 is that those four are not enough for a caller
that will intern again: it needs

* `EResolves lst' r` — "the answer decodes", which is `intern_e_*_run`'s own
  `hview` at the next step and which `AOut`'s `WF : α → Prop` slot cannot
  say, because it never sees `lst'`;
* `EViewExt` — "what decoded before still decodes", for the handles the walk
  read before the intern;
* the two Rust tier flags, which is what carries `hfrozen` across the step;
* and a side invariant `Q` of the post-state — the memo clause `MemoRes` for
  a memoised walk. -/
def WOutR (Q : AState → Prop) (pers : arena.store.PersTier) (st : arena.monad.AState)
    (lst : AState)
    (o : core.result.Result arena.handle.EIdx kernel.core_types.CheckError ×
      arena.monad.AState) (res : Except Arena.CheckError (EIdx × AState)) : Prop :=
  match o.1 with
  | .Ok r => ∃ lst', res = .ok (absEIdx r, lst') ∧ AStateRel pers o.2 lst' ∧
      AStateInv pers o.2 ∧ Ext lst.store lst'.store ∧ EResolves lst' (absEIdx r) ∧
      EViewExt lst.store lst'.store ∧
      o.2.store.shared_on = st.store.shared_on ∧
      o.2.store.scratch_on = st.store.scratch_on ∧ Q lst'
  | .Err e => AErrSim e res

/-- `WOutR` at a twin action's run. -/
def WOutE (Q : AState → Prop) (pers : arena.store.PersTier) (st : arena.monad.AState)
    (lst : AState)
    (o : core.result.Result arena.handle.EIdx kernel.core_types.CheckError ×
      arena.monad.AState) (x : AM EIdx) : Prop :=
  WOutR Q pers st lst o (x.run lst)

theorem WOutE.toSim {Q pers st lst o x} (h : WOutE Q pers st lst o x) :
    Sim absEIdx (fun _ => True) pers lst o x := by
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2 (x.run lst)
  simp only [WOutE, WOutR] at h
  cases ho : o.1 with
  | Ok r =>
    rw [ho] at h
    obtain ⟨lst', hx, h1, h2, h3, -⟩ := h
    exact AOut.ok hx h1 h2 h3 trivial
  | Err e => rw [ho] at h; exact AOut.err h

/-- The success arm, from its nine parts. -/
theorem WOutR.ok {Q pers st lst} {r : arena.handle.EIdx} {st' : arena.monad.AState}
    {res : Except Arena.CheckError (EIdx × AState)} {lst' : AState}
    (hx : res = .ok (absEIdx r, lst')) (h1 : AStateRel pers st' lst')
    (h2 : AStateInv pers st') (h3 : Ext lst.store lst'.store)
    (h4 : EResolves lst' (absEIdx r)) (h5 : EViewExt lst.store lst'.store)
    (h6 : st'.store.shared_on = st.store.shared_on)
    (h7 : st'.store.scratch_on = st.store.scratch_on) (h8 : Q lst') :
    WOutR Q pers st lst (.Ok r, st') res :=
  ⟨lst', hx, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A `WOutR` is about the run RESULT only, so it transports along an equation
of results. -/
theorem WOutR.of_eq {Q pers st lst o} {res res' : Except Arena.CheckError (EIdx × AState)}
    (h : WOutR Q pers st lst o res') (he : res = res') : WOutR Q pers st lst o res := by
  rw [he]; exact h

/-- The answer is a handle the walk was HANDED, unchanged, at an unchanged
state: the cutoff, the memo hit, the leaf arms. -/
theorem WOutR.pure {Q pers st lst} {r : arena.handle.EIdx}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hr : EResolves lst (absEIdx r)) (hq : Q lst) :
    WOutR Q pers st lst (.Ok r, st) (.ok (absEIdx r, lst)) :=
  WOutR.ok rfl hrel hinv (Ext.refl _) hr (EViewExt.refl _) rfl rfl hq

/-- The error arm of a chained step: the callee threw, so the whole bind
throws. -/
theorem wout_err_bind {Q : AState → Prop} {e : kernel.core_types.CheckError}
    {pers : arena.store.PersTier} {st stB : arena.monad.AState} {lst0 lst : AState}
    {α : Type} {x : AM α} {f : α → AM EIdx}
    (h : AErrSim e (x.run lst)) :
    WOutR Q pers st lst0 (.Err e, stB) ((do let v ← x; f v).run lst) := by
  show AErrSim e _
  rw [StateT.run_bind]
  exact AErrSim.bind h _

/-- The error half of a `WOutE` at a call site. -/
theorem WOutE.err {Q pers st lst o x} {e : kernel.core_types.CheckError}
    (h : WOutE Q pers st lst o x) (he : o.1 = .Err e) : AErrSim e (x.run lst) := by
  simp only [WOutE, WOutR, he] at h; exact h

/-- The success half of a `WOutE` at a call site. -/
theorem WOutE.dest {Q pers st lst} {r : arena.handle.EIdx} {st' : arena.monad.AState}
    {x : AM EIdx} (h : WOutE Q pers st lst (.Ok r, st') x) :
    ∃ lst', x.run lst = .ok (absEIdx r, lst') ∧ AStateRel pers st' lst' ∧
      AStateInv pers st' ∧ Ext lst.store lst'.store ∧ EResolves lst' (absEIdx r) ∧
      EViewExt lst.store lst'.store ∧
      st'.store.shared_on = st.store.shared_on ∧
      st'.store.scratch_on = st.store.scratch_on ∧ Q lst' := h

/-- **The chained step**, which is what makes `WOutE` an induction hypothesis:
a first call that answered `g` at `lst1`, a continuation measured from there,
and the two extensions and the two flags composed. -/
theorem WOutE.bind {Q : AState → Prop} {pers : arena.store.PersTier}
    {st st1 : arena.monad.AState} {lst lst1 : AState}
    {o : core.result.Result arena.handle.EIdx kernel.core_types.CheckError ×
      arena.monad.AState}
    {g : arena.handle.EIdx} {x : AM EIdx} {k : EIdx → AM EIdx}
    (hx1 : x.run lst = .ok (absEIdx g, lst1))
    (hext1 : Ext lst.store lst1.store)
    (hmono1 : EViewExt lst.store lst1.store)
    (hfl1 : st1.store.shared_on = st.store.shared_on)
    (hfl2 : st1.store.scratch_on = st.store.scratch_on)
    (h : WOutE Q pers st1 lst1 o (k (absEIdx g))) :
    WOutE Q pers st lst o (do let v ← x; k v) := by
  have hrun : (do let v ← x; k v).run lst = (k (absEIdx g)).run lst1 := by
    rw [StateT.run_bind, hx1]; rfl
  simp only [WOutE, WOutR] at h ⊢
  cases ho : o.1 with
  | Ok r =>
    rw [ho] at h
    obtain ⟨lst', hx, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    exact ⟨lst', by rw [hrun]; exact hx, h1, h2, Ext.trans hext1 h3, h4,
      EViewExt.trans hmono1 h5, by rw [h6, hfl1], by rw [h7, hfl2], h8⟩
  | Err e => rw [ho] at h; rw [hrun]; exact h

/-- **The intern step's tail, once**: a twin action whose run IS
`EStore.intern w` at the pre-state, and a port store step `estore_intern_*_abs`
has related to it.  Every `intern_e_*_res` below is its `_abs` lemma and this. -/
theorem wout_intern_tail {Q : AState → Prop} (hQ : QStable Q)
    {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hq : Q lst)
    {w : ENodeView} (hview : lst.store.ViewOK w)
    {x : AM EIdx}
    (hx : ECapAt lst.store w → ECapBMAt lst.store w →
      x.run lst = .ok ((lst.store.intern w).2,
        { lst with store := (lst.store.intern w).1 }))
    {r : core.result.Result arena.handle.EIdx kernel.core_types.CheckError}
    {e : arena.store.EStore}
    (hok : ∀ hh, r = .Ok hh → absEIdx hh = (lst.store.intern w).2 ∧
      StoreRel pers e (lst.store.intern w).1 ∧ StoreInv pers e ∧ ECapAt lst.store w ∧
      ECapBMAt lst.store w ∧
      e.shared_on = st.store.shared_on ∧ e.scratch_on = st.store.scratch_on)
    (herr : ∀ ee, r = .Err ee → absAErrKind ee = none) :
    WOutE Q pers st lst (r, { st with store := e }) x := by
  cases hr : r with
  | Ok hh =>
    obtain ⟨hhd, hrel', hinv', hcap, hbm, hfl1, hfl2⟩ := hok hh hr
    have hext : EViewExt lst.store (lst.store.intern w).1 := EViewExt.intern _ _
    refine WOutR.ok (lst' := { lst with store := (lst.store.intern w).1 })
      (by rw [hx hcap hbm, hhd])
      ⟨hrel', hrel.memos, hrel.caches, hrel.pins,
        intern_storeWF hrel.storeWF hview hcap hbm⟩
      ⟨hinv', hinv.memos, hinv.caches⟩ (EStore.intern_ext _ _) ?_ hext hfl1 hfl2
      (hQ lst _ rfl hext hq)
    show ((lst.store.intern w).1.view (absEIdx hh)).isSome = true
    rw [hhd, intern_resolves hrel.storeWF hview hcap hbm]
    rfl
  | Err ee => exact AErrSim.of_none (herr ee hr)

/-- The shape `estore_intern_*_abs` concludes at a NON-binder view, into
`wout_intern_tail`'s. -/
theorem nb_hok {pers : arena.store.PersTier} {ls : EStore} {w : ENodeView}
    (hnb : EStore.eViewNeedsBM w = false) {rs rs' : arena.store.EStore}
    {r : core.result.Result arena.handle.EIdx kernel.core_types.CheckError}
    (hok : ∀ hh, r = .Ok hh → absEIdx hh = (ls.intern w).2 ∧
      StoreRel pers rs' (ls.intern w).1 ∧ StoreInv pers rs' ∧ ECapAt ls w)
    (hfl : rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on) :
    ∀ hh, r = .Ok hh → absEIdx hh = (ls.intern w).2 ∧
      StoreRel pers rs' (ls.intern w).1 ∧ StoreInv pers rs' ∧ ECapAt ls w ∧
      ECapBMAt ls w ∧ rs'.shared_on = rs.shared_on ∧ rs'.scratch_on = rs.scratch_on :=
  fun hh hr => let ⟨a1, a2, a3, a4⟩ := hok hh hr
    ⟨a1, a2, a3, a4, ECapBMAt.of_no_bm hnb, hfl.1, hfl.2⟩

/-- `arena::monad::intern_e_app` at `WOutE`. -/
theorem intern_e_app_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    (f a : arena.handle.EIdx)
    (hview : lst.store.ViewOK (.app (absEIdx f) (absEIdx a)))
    {o} (hrun : arena.monad.intern_e_app pers st f a = ok o) :
    WOutE Q pers st lst o (Arena.internAppE (absEIdx f) (absEIdx a)) := by
  rw [arena.monad.intern_e_app] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, hfl⟩ :=
    estore_intern_app_abs (ls := lst.store) hrel.store hinv.store hfrozen
      (fun h => hchild_app hrel.storeWF h) hp
  exact wout_intern_tail hQ hrel hinv hq hview
    (fun hcap _ => by rw [Arena.internAppE]; exact internE_run_of_cap rfl hcap)
    (nb_hok rfl hok hfl) herr

/-- `arena::monad::intern_e_bvar` at `WOutE`. -/
theorem intern_e_bvar_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    (i : Std.U64) {o} (hrun : arena.monad.intern_e_bvar pers st i = ok o) :
    WOutE Q pers st lst o (Arena.internBVarE (absU i)) := by
  rw [arena.monad.intern_e_bvar] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, hfl⟩ :=
    estore_intern_bvar_abs (ls := lst.store) hrel.store hinv.store hfrozen hp
  exact wout_intern_tail hQ hrel hinv hq (viewOK_bvar _)
    (fun hcap _ => by rw [Arena.internBVarE]; exact internE_run_of_cap rfl hcap)
    (nb_hok rfl hok hfl) herr

/-- `arena::monad::intern_e_let_e` at `WOutE`. -/
theorem intern_e_let_e_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    (ty val b : arena.handle.EIdx)
    (hview : lst.store.ViewOK (.letE (absEIdx ty) (absEIdx val) (absEIdx b)))
    {o} (hrun : arena.monad.intern_e_let_e pers st ty val b = ok o) :
    WOutE Q pers st lst o (Arena.internLetEE (absEIdx ty) (absEIdx val) (absEIdx b)) := by
  rw [arena.monad.intern_e_let_e] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, hfl⟩ :=
    estore_intern_let_e_abs (ls := lst.store) hrel.store hinv.store hfrozen
      (fun h => hchild_let_e hrel.storeWF h) hp
  exact wout_intern_tail hQ hrel hinv hq hview
    (fun hcap _ => by rw [Arena.internLetEE]; exact internE_run_of_cap rfl hcap)
    (nb_hok rfl hok hfl) herr

/-- `arena::monad::intern_e_proj` at `WOutE`. -/
theorem intern_e_proj_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    (n : arena.handle.NIdx) (i : Std.U64) (e0 : arena.handle.EIdx)
    (hview : lst.store.ViewOK (.proj (absNIdx n) (absU i) (absEIdx e0)))
    {o} (hrun : arena.monad.intern_e_proj pers st n i e0 = ok o) :
    WOutE Q pers st lst o (Arena.internProjE (absNIdx n) (absU i) (absEIdx e0)) := by
  rw [arena.monad.intern_e_proj] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, hfl⟩ :=
    estore_intern_proj_abs (ls := lst.store) hrel.store hinv.store hfrozen
      (fun h => hchild_proj hrel.storeWF h) hp
  exact wout_intern_tail hQ hrel hinv hq hview
    (fun hcap _ => by rw [Arena.internProjE]; exact internE_run_of_cap rfl hcap)
    (nb_hok rfl hok hfl) herr

/-! ### The binder arm at a datum HANDLE the walk read

A rebuilding walk takes a binder apart with `viewBindI` and puts it back with
`internBindIE` at the SAME datum handle.  At a well-formed store that handle
is the one the datum table answers for its datum (`findBM_of_viewBM`, from
`bmChildOK`'s `tag = 0`), and there `internBindI` IS `intern` at the binder
view — so every side condition `intern_e_bind_i_run` assumes for an arbitrary
`BMIdx` is a consequence: `EBindWFAt` is `intern_storeWF`, `hchild` is
`persFind_bind_none_of_child`, and `EBindCapAt` is the port's. -/

/-- At a datum handle the cons table answers, `internBindI` IS `intern`. -/
theorem internBindI_eq_intern {st : EStore} (hwf : StoreWF st) {tag : UInt32}
    {ty b : EIdx} {m : ConLeche.BinderMeta} {mi : BMIdx}
    (htag : ETag.isBind tag = true) (hfb : st.findBM m = some mi) :
    st.internBindI tag ty b mi = st.intern (eBindView tag ty b m) := by
  obtain ⟨rk, hw⟩ := hwf
  have hder : st.bmDer mi = (hash m.pw, m.pw.hasParams) :=
    hw.bmDerExact _ _ (hw.viewBM_of_findBM hfb)
  rw [EStore_internBindI_eq_internAt htag hder]
  have hbv : (eBindView tag ty b m).bmOf = some m := ENodeView.bmOf_eBindView tag ty b m
  show _ = (st.internBMOfView (eBindView tag ty b m)).1.internAt (eBindView tag ty b m)
    (st.internBMOfView (eBindView tag ty b m)).2
  have hib : st.internBMOfView (eBindView tag ty b m) = (st, mi) := by
    rcases ETag_isBind_eq htag with rfl | rfl
    · show st.internBM m = _; exact internBM_of_findBM hfb
    · show st.internBM m = _; exact internBM_of_findBM hfb
  rw [hib]

/-- At such a handle the node probe is the binder probe. -/
theorem find?_eBindView {st : EStore} {tag : UInt32} (htag : ETag.isBind tag = true)
    {ty b : EIdx} {m : ConLeche.BinderMeta} {mi : BMIdx} (hfb : st.findBM m = some mi) :
    st.find? (eBindView tag ty b m) = st.findBindI tag ty b mi := by
  rcases ETag_isBind_eq htag with rfl | rfl
  · show st.find? (.lam ty b m) = _
    simp only [EStore.find?, EStore.findBMOfView, hfb]
    exact findAt_lam_eq_findBindI st ty b m mi
  · show st.find? (.forallE ty b m) = _
    simp only [EStore.find?, EStore.findBMOfView, hfb]
    exact findAt_forallE_eq_findBindI st ty b m mi

theorem sizeOf_eBindView (t : ETables) {tag : UInt32} (htag : ETag.isBind tag = true)
    {ty b : EIdx} {m : ConLeche.BinderMeta} :
    t.sizeOf (eBindView tag ty b m) = t.bindSizeOf tag := by
  rcases ETag_isBind_eq htag with rfl | rfl
  · simp [eBindView, ETables.sizeOf, ETables.bindSizeOf]
  · simp [eBindView, ETables.sizeOf, ETables.bindSizeOf, ETag.lam, ETag.forallE]

/-- `ECapAt` at the binder view IS `EBindCapAt` at the handle. -/
theorem ECapAt_of_EBindCapAt {st : EStore} {tag : UInt32} (htag : ETag.isBind tag = true)
    {ty b : EIdx} {m : ConLeche.BinderMeta} {mi : BMIdx} (hfb : st.findBM m = some mi)
    (h : EBindCapAt st tag ty b mi) : ECapAt st (eBindView tag ty b m) := by
  intro hf
  rw [find?_eBindView htag hfb] at hf
  have := h hf
  rwa [sizeOf_eBindView _ htag, sizeOf_eBindView _ htag]

theorem EBindCapAt_of_ECapAt {st : EStore} {tag : UInt32} (htag : ETag.isBind tag = true)
    {ty b : EIdx} {m : ConLeche.BinderMeta} {mi : BMIdx} (hfb : st.findBM m = some mi)
    (h : ECapAt st (eBindView tag ty b m)) : EBindCapAt st tag ty b mi := by
  intro hf
  rw [← find?_eBindView htag hfb] at hf
  have := h hf
  rwa [sizeOf_eBindView _ htag, sizeOf_eBindView _ htag] at this

/-- **`arena::monad::intern_e_bind_i` at `WOutE`, at a datum handle that
decodes** — which is what a rebuilding walk's `viewBindI` hands it. -/
theorem intern_e_bind_i_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    (tag : Std.U32) (htag : ETag.isBind (absU32 tag) = true)
    (ty b : arena.handle.EIdx) (mi : arena.handle.BMIdx) {mm : ConLeche.BinderMeta}
    (hmv : lst.store.viewBM (absBMIdx mi) = some mm) (hm0 : (absBMIdx mi).tag = 0)
    (hty : EResolves lst (absEIdx ty)) (hb : EResolves lst (absEIdx b))
    {o} (hrun : arena.monad.intern_e_bind_i pers st tag ty b mi = ok o) :
    WOutE Q pers st lst o
      (Arena.internBindIE (absU32 tag) (absEIdx ty) (absEIdx b) (absBMIdx mi)) := by
  have hfb : lst.store.findBM mm = some (absBMIdx mi) := by
    obtain ⟨rk, hw⟩ := hrel.storeWF; exact hw.findBM_of_viewBM hm0 hmv
  have hview : lst.store.ViewOK (eBindView (absU32 tag) (absEIdx ty) (absEIdx b) mm) := by
    rcases ETag_isBind_eq htag with h | h <;> rw [h]
    · exact viewOK_lam hty hb
    · simp only [eBindView, ETag.lam, ETag.forallE]; exact viewOK_forallE hty hb
  have hbm : ECapBMAt lst.store (eBindView (absU32 tag) (absEIdx ty) (absEIdx b) mm) :=
    ECapBMAt.of_findBMOfView (mi := absBMIdx mi) (by
      rw [EStore.findBMOfView_eq_findBM _ (ENodeView.bmOf_eBindView _ _ _ _)]; exact hfb)
  have heq := internBindI_eq_intern (ty := absEIdx ty) (b := absEIdx b)
    hrel.storeWF htag hfb
  rw [arena.monad.intern_e_bind_i] at hrun
  by_cases hc : tag = arena.handle.ETAG_LAM
  · subst hc
    rw [if_pos rfl] at hrun
    have hl : absU32 arena.handle.ETAG_LAM = ETag.lam := etag_lam_abs
    obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, e⟩ := p
    have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
      Result.ok_injective hrun
    subst ho
    have hfb' : lst.store.findBM mm = some (absBMIdx mi) := hfb
    obtain ⟨hok, herr, hfl⟩ :=
      estore_intern_lam_i_abs (ls := lst.store) hrel.store hinv.store hfrozen
        (fun hc => persFind_bind_none_of_child
          (v := .lam (absEIdx ty) (absEIdx b) mm) hrel.storeWF rfl hfb'
          (bind_child_disj _ rfl hc)) hp
    have heqL : lst.store.internLamI (absEIdx ty) (absEIdx b) (absBMIdx mi)
        = lst.store.intern (eBindView (absU32 arena.handle.ETAG_LAM) (absEIdx ty)
            (absEIdx b) mm) := by
      rw [hl] at heq ⊢; exact heq
    refine wout_intern_tail hQ hrel hinv hq hview ?_ ?_ herr
    · intro hcap _
      rw [Arena.internBindIE, if_pos (by rw [hl]; simp), ← heqL]
      exact internLamIE_run_of_cap
        (by have := EBindCapAt_of_ECapAt htag hfb hcap; rwa [hl] at this)
    · intro hh hr
      obtain ⟨a1, a2, a3, a4⟩ := hok hh hr
      rw [heqL] at a1 a2
      exact ⟨a1, a2, a3, ECapAt_of_EBindCapAt htag hfb (by rw [hl]; exact a4), hbm,
        hfl.1, hfl.2⟩
  · rw [if_neg hc] at hrun
    have hne : absU32 tag ≠ ETag.lam := by
      rw [← etag_lam_abs]
      intro hcc; exact hc (absU32_inj hcc)
    have hf : absU32 tag = ETag.forallE := by
      rcases ETag_isBind_eq htag with h | h
      · exact absurd h hne
      · exact h
    obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, e⟩ := p
    have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
      Result.ok_injective hrun
    subst ho
    obtain ⟨hok, herr, hfl⟩ :=
      estore_intern_forall_e_i_abs (ls := lst.store) hrel.store hinv.store hfrozen
        (fun hc => persFind_bind_none_of_child
          (v := .forallE (absEIdx ty) (absEIdx b) mm) hrel.storeWF rfl hfb
          (bind_child_disj _ rfl hc)) hp
    have heqF : lst.store.internForallEI (absEIdx ty) (absEIdx b) (absBMIdx mi)
        = lst.store.intern (eBindView (absU32 tag) (absEIdx ty) (absEIdx b) mm) := by
      rw [← heq, hf]; rfl
    refine wout_intern_tail hQ hrel hinv hq hview ?_ ?_ herr
    · intro hcap _
      rw [Arena.internBindIE, if_neg (by simp [hne]), ← heqF]
      exact internForallEIE_run_of_cap
        (by have := EBindCapAt_of_ECapAt htag hfb hcap; rwa [hf] at this)
    · intro hh hr
      obtain ⟨a1, a2, a3, a4⟩ := hok hh hr
      rw [heqF] at a1 a2
      exact ⟨a1, a2, a3, ECapAt_of_EBindCapAt htag hfb (by rw [hf]; exact a4), hbm,
        hfl.1, hfl.2⟩

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
    exact intern_e_bvar_run hrel hinv hfrozen i hrun

/-- `arena::expr_ops::intern_rebuilt_fvar` against `Arena.internRebuiltFVar`. -/
theorem intern_rebuilt_fvar_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {idx : Std.U64} {ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      (absEIdx ty).isPersistent = false →
      lst.store.pers.fvars.find? ⟨absU idx, absEIdx ty⟩ = none)
    (hview : same = false → lst.store.ViewOK (.fvar (absU idx) (absEIdx ty)))
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
    exact intern_e_fvar_run hrel hinv hfrozen idx ty (hchild rfl) (hview rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_sort` against `Arena.internRebuiltSort`. -/
theorem intern_rebuilt_sort_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {u : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      (absLIdx u).isPersistent = false →
      lst.store.pers.sorts.find? ⟨absLIdx u⟩ = none)
    (hview : same = false → lst.store.ViewOK (.sort (absLIdx u)))
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
    exact intern_e_sort_run hrel hinv hfrozen u (hchild rfl) (hview rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_const` against `Arena.internRebuiltConst`. -/
theorem intern_rebuilt_const_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {n : arena.handle.NIdx} {us : arena.handle.LsIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      ((absNIdx n).isPersistent = false ∨ (absLsIdx us).isPersistent = false) →
      lst.store.pers.consts.find? ⟨absNIdx n, absLsIdx us⟩ = none)
    (hview : same = false → lst.store.ViewOK (.const (absNIdx n) (absLsIdx us)))
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
    exact intern_e_const_run hrel hinv hfrozen n us (hchild rfl) (hview rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_app` against `Arena.internRebuiltApp`. -/
theorem intern_rebuilt_app_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {f a : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      ((absEIdx f).isPersistent = false ∨ (absEIdx a).isPersistent = false) →
      lst.store.pers.apps.find? ⟨absEIdx f, absEIdx a⟩ = none)
    (hview : same = false → lst.store.ViewOK (.app (absEIdx f) (absEIdx a)))
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
    exact intern_e_app_run hrel hinv hfrozen f a (hchild rfl) (hview rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_let_e` against `Arena.internRebuiltLetE`. -/
theorem intern_rebuilt_let_e_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {ty val body : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      ((absEIdx ty).isPersistent = false ∨ (absEIdx val).isPersistent = false ∨
        (absEIdx body).isPersistent = false) →
      lst.store.pers.lets.find? ⟨absEIdx ty, absEIdx val, absEIdx body⟩ = none)
    (hview : same = false →
      lst.store.ViewOK (.letE (absEIdx ty) (absEIdx val) (absEIdx body)))
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
    exact intern_e_let_e_run hrel hinv hfrozen ty val body (hchild rfl) (hview rfl) hrun

/-- `arena::expr_ops::intern_rebuilt_lit` against `Arena.internRebuiltLit`. -/
theorem intern_rebuilt_lit_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {l : kernel.expr.Literal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hwf : ConRon.Refine.LiteralWF l)
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
    exact intern_e_lit_run hrel hinv hfrozen l hwf hrun

/-- `arena::expr_ops::intern_rebuilt_proj` against `Arena.internRebuiltProj`. -/
theorem intern_rebuilt_proj_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {n : arena.handle.NIdx} {i : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hchild : same = false →
      ((absNIdx n).isPersistent = false ∨ (absEIdx e).isPersistent = false) →
      lst.store.pers.projs.find? ⟨absNIdx n, absU i, absEIdx e⟩ = none)
    (hview : same = false →
      lst.store.ViewOK (.proj (absNIdx n) (absU i) (absEIdx e)))
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
    exact intern_e_proj_run hrel hinv hfrozen n i e (hchild rfl) (hview rfl) hrun

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
    (hwfL : same = false → absU32 tag = ETag.lam →
      EBindWFAt lst.store ETag.lam (absEIdx ty) (absEIdx body) (absBMIdx m))
    (hwfF : same = false → absU32 tag ≠ ETag.lam →
      EBindWFAt lst.store ETag.forallE (absEIdx ty) (absEIdx body) (absBMIdx m))
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
      (hchildL rfl) (hchildF rfl) (hwfL rfl) (hwfF rfl) hrun

/-- `Arena/ExprOps.lean:139 internRebuilt` — the view-taking cutoff, against
`Specs.lean`'s ten-way `intern_e_run`.

**Task #97-P5-Mut corrected the statement** (finding 19's first instance): as
written it carried `hrel`/`hinv` and nothing else, and `internE`'s side
conditions are not the port's to give — the same seven `intern_e_run` asks
for, each guarded by `same = false` exactly as the twelve per-constructor
siblings above guard theirs.  `hchild` is NOT among them: finding 14's
`hchild_*` derive it from `hrel.storeWF`, which is what `intern_e_run` already
does at six of its ten arms; what survives is `ViewOK`, the literal's
well-formedness, the datum-array capacity, the `PropWhen` shape, the two
persistent binder probes and `ECapAt`. -/
theorem intern_rebuilt_refines {pers st lst} {h : arena.handle.EIdx} {same : Bool}
    {v : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hview : same = false → lst.store.ViewOK (absENodeView v))
    (hlit : same = false → ∀ l, v = .Lit l → ConRon.Refine.LiteralWF l)
    (hpw : same = false → ∀ ty b m, v = .Lam ty b m ∨ v = .ForallE ty b m →
      ConRon.Refine.PropWhenWF m.pw)
(hrun : arena.expr_ops.intern_rebuilt pers st h same v = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuilt (absEIdx h) same (absENodeView v)) := by
  rw [arena.expr_ops.intern_rebuilt] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuilt (absEIdx h) same (absENodeView v)).run lst)
  rw [internRebuilt]
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
    exact intern_e_run hrel hinv hfrozen v (hview rfl) (hlit rfl)
      (hpw rfl) hrun



/-- `Arena/ExprOps.lean:159 internRebuiltLam`. -/
theorem intern_rebuilt_lam_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {ty body : arena.handle.EIdx} {m : kernel.expr.BinderMeta} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hpw : same = false → ConRon.Refine.PropWhenWF m.pw)
    (hview : same = false → lst.store.ViewOK
      (.lam (absEIdx ty) (absEIdx body) (ConRon.Refine.absBinderMeta m)))
    (hrun : arena.expr_ops.intern_rebuilt_lam pers st h same ty body m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltLam (absEIdx h) same (absEIdx ty) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.expr_ops.intern_rebuilt_lam] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltLam (absEIdx h) same (absEIdx ty) (absEIdx body)
      (ConRon.Refine.absBinderMeta m)).run lst)
  rw [internRebuiltLam]
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
    exact intern_e_lam_run hrel hinv hfrozen ty body m
      (hpw rfl) (hview rfl) hrun

/-- `Arena/ExprOps.lean:163 internRebuiltForallE`. -/
theorem intern_rebuilt_forall_e_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {ty body : arena.handle.EIdx} {m : kernel.expr.BinderMeta} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hpw : same = false → ConRon.Refine.PropWhenWF m.pw)
    (hview : same = false → lst.store.ViewOK
      (.forallE (absEIdx ty) (absEIdx body) (ConRon.Refine.absBinderMeta m)))
    (hrun : arena.expr_ops.intern_rebuilt_forall_e pers st h same ty body m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltForallE (absEIdx h) same (absEIdx ty) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.expr_ops.intern_rebuilt_forall_e] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltForallE (absEIdx h) same (absEIdx ty) (absEIdx body)
      (ConRon.Refine.absBinderMeta m)).run lst)
  rw [internRebuiltForallE]
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
    exact intern_e_forall_e_run hrel hinv hfrozen ty body m
      (hpw rfl) (hview rfl) hrun




/-- `Arena/ExprOps.lean:179 internRebuiltBind`. -/
theorem intern_rebuilt_bind_refines {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {tag : Std.U32} {ty body : arena.handle.EIdx}
    {m : kernel.expr.BinderMeta} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hpw : same = false → ConRon.Refine.PropWhenWF m.pw)
    (hviewL : same = false → absU32 tag = ETag.lam → lst.store.ViewOK
      (.lam (absEIdx ty) (absEIdx body) (ConRon.Refine.absBinderMeta m)))
    (hviewF : same = false → absU32 tag ≠ ETag.lam → lst.store.ViewOK
      (.forallE (absEIdx ty) (absEIdx body) (ConRon.Refine.absBinderMeta m)))
    (hrun : arena.expr_ops.intern_rebuilt_bind pers st h same tag ty body m = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (internRebuiltBind (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.expr_ops.intern_rebuilt_bind] at hrun
  show AOut absEIdx (fun _ => True) pers lst o.1 o.2
    ((internRebuiltBind (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx body)
      (ConRon.Refine.absBinderMeta m)).run lst)
  rw [internRebuiltBind]
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
    by_cases hc : tag = arena.handle.ETAG_LAM
    · subst hc
      rw [if_pos rfl] at hrun
      rw [if_pos (show (absU32 arena.handle.ETAG_LAM == ETag.lam) = true by
        rw [etag_lam_abs]; simp)]
      exact intern_e_lam_run hrel hinv hfrozen ty body m
        (hpw rfl) (hviewL rfl (by rw [etag_lam_abs])) hrun
    · rw [if_neg hc] at hrun
      have hne : absU32 tag ≠ ETag.lam := by
        rw [← etag_lam_abs]
        intro hcc; exact hc (absU32_inj hcc)
      rw [if_neg (show ¬ ((absU32 tag == ETag.lam) = true) by simp [hne])]
      exact intern_e_forall_e_run hrel hinv hfrozen ty body m
        (hpw rfl) (hviewF rfl hne) hrun



/-! ### The binder arm at a datum VALUE the walk read

A walk that reads a node with `view` (rather than `viewBindI`) gets the binder
datum as a VALUE and puts it back with `intern_e_lam` / `intern_e_forall_e`,
which intern the datum first.  The port's `intern_bm` wants the datum's
`PropWhenWF` (its record's `TblRel` is `RelOn BMNodeWF`), and that is a fact
about the PORT's store: the `bms` array's `TblInv` says every record in it is
well formed, and `view` reads the datum out of it.  So the one new fact here
is `view`'s: a binder view's datum is well formed. -/

theorem etables_get_bm_wf {rt : arena.store.ETables} (hinv : ETablesInv rt)
    {m : arena.handle.BMIdx} {o : Option kernel.expr.BinderMeta}
    (h : arena.store.ETables.get_bm rt m = ok o) :
    ∀ bm, o = some bm → ConRon.Refine.PropWhenWF bm.pw := by
  rw [arena.store.ETables.get_bm] at h
  obtain ⟨n, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hwf := tbl_node_wf hinv.bms hp
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option kernel.expr.BinderMeta) = o := Result.ok_injective h
    subst h2
    intro bm hbm; cases hbm
  | some r =>
    rw [hpc] at h hwf
    obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some bm = o := Result.ok_injective h
    subst h2
    rw [ConRon.Refine.PropWhen.dup_eq hpw] at hbm
    have h3 : bm = ⟨r.pw⟩ := by
      rw [kernel.expr.binder_meta] at hbm
      exact (Result.ok_injective hbm).symm
    subst h3
    intro bm' hbm'
    simp only [Option.some.injEq] at hbm'
    subst hbm'
    exact hwf r rfl

theorem estore_view_bm_wf {pers rs} (hinv : StoreInv pers rs)
    {m : arena.handle.BMIdx} {o}
    (h : arena.store.EStore.view_bm rs pers m = ok o) :
    ∀ bm, o = some bm → ConRon.Refine.PropWhenWF bm.pw := by
  rw [arena.store.EStore.view_bm] at h
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · rw [arena.store.EStore.pers_get_bm] at h
    have h3 : arena.store.ETables.get_bm (rPersE pers rs) m = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_bm_wf hinv.perst h3
  · split at h
    · exact etables_get_bm_wf hinv.scrt h
    · have h2 : (none : Option kernel.expr.BinderMeta) = o := Result.ok_injective h
      subst h2
      intro bm hbm; cases hbm

/-- At a non-binder tag `view` is `ETables.get`, which answers no binder
view. -/
theorem view_nonbind_bmOf {st : EStore} {i : EIdx} (hnb : ETag.isBind i.tag = false)
    {v : ENodeView} (hv : st.view i = some v) : v.bmOf = none := by
  rw [EStore.view, if_neg (by rw [hnb]; simp)] at hv
  split at hv
  · exact ETables.bmOf_get hv
  · split at hv
    · exact ETables.bmOf_get hv
    · cases hv

/-- **A binder view's datum is well formed** — `bms`' `TblInv`, read through
`view`.  The non-binder branch cannot produce a binder view, which the TWIN
says: `ETables.get` answers no binder view (`ETables.bmOf_get`). -/
theorem estore_view_bind_wf {pers rs ls} (hrel : StoreRel pers rs ls)
    (hinv : StoreInv pers rs) {i : arena.handle.EIdx} {o}
    (h : arena.store.EStore.view rs pers i = ok o) {ty b : arena.handle.EIdx}
    {m : kernel.expr.BinderMeta}
    (hv : o = some (.Lam ty b m) ∨ o = some (.ForallE ty b m)) :
    ConRon.Refine.PropWhenWF m.pw := by
  have habs := estore_view_abs hrel h
  rw [arena.store.EStore.view] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have htg := eidx_tag_abs ht
  have hib := etag_isBind_abs hbb
  split at h <;> rename_i hbv
  · obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases hqc : q with
    | none =>
      rw [hqc] at h
      have h2 : (none : Option arena.store.ENodeView) = o := Result.ok_injective h
      subst h2
      rcases hv with hv | hv <;> cases hv
    | some tt =>
      rw [hqc] at h
      obtain ⟨ty', bo', mm⟩ := tt
      obtain ⟨ev, hev, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 : some ev = o := Result.ok_injective h
      subst h2
      have hmm : m = mm := by
        rw [arena.store.e_bind_view] at hev
        split at hev
        · have := Result.ok_injective hev
          rcases hv with hv | hv <;> rw [← this] at hv <;>
            simp only [Option.some.injEq, reduceCtorEq] at hv
          exact (arena.store.ENodeView.Lam.inj hv).2.2.symm
        · have := Result.ok_injective hev
          rcases hv with hv | hv <;> rw [← this] at hv <;>
            simp only [Option.some.injEq, reduceCtorEq] at hv
          exact (arena.store.ENodeView.ForallE.inj hv).2.2.symm
      subst hmm
      rw [hqc] at hq
      rw [arena.store.EStore.view_bind] at hq
      obtain ⟨o1, -, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
      cases ho1 : o1 with
      | none =>
        rw [ho1] at hq
        have := Result.ok_injective hq
        cases this
      | some t3 =>
        rw [ho1] at hq
        obtain ⟨e1, e2, bmi⟩ := t3
        obtain ⟨o2, ho2, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
        cases ho2c : o2 with
        | none =>
          rw [ho2c] at hq
          have := Result.ok_injective hq
          cases this
        | some m2 =>
          rw [ho2c] at hq ho2
          have h3 := Result.ok_injective hq
          simp only [Option.some.injEq, Prod.mk.injEq] at h3
          rw [← h3.2.2]
          exact estore_view_bm_wf hinv ho2 m2 rfl
  · -- the non-binder branch: the twin view is `ETables.get`, which answers no
    -- binder view
    exfalso
    have hnb : ETag.isBind (absEIdx i).tag = false := by
      rw [htg, hib]; simpa using hbv
    rcases hv with hv | hv <;> subst hv <;>
      exact absurd (view_nonbind_bmOf hnb habs) (by simp [absENodeView, ENodeView.bmOf])

/-- `arena::monad::view`'s binder answer carries a well-formed datum. -/
theorem view_bind_wf {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.EIdx} {ev : arena.store.ENodeView}
    (hrun : arena.monad.view pers st h = ok (.Ok ev)) {ty b : arena.handle.EIdx}
    {m : kernel.expr.BinderMeta} (hv : ev = .Lam ty b m ∨ ev = .ForallE ty b m) :
    ConRon.Refine.PropWhenWF m.pw := by
  rw [arena.monad.view] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  cases hqc : q with
  | none =>
    rw [hqc] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    cases Result.ok_injective hrun
  | some v =>
    rw [hqc] at hrun hq
    have := Result.ok_injective hrun
    simp only [core.result.Result.Ok.injEq] at this
    subst this
    exact estore_view_bind_wf (ty := ty) (b := b) hrel.store hinv.store hq
      (by rcases hv with hv | hv
          · exact Or.inl (by rw [hv])
          · exact Or.inr (by rw [hv]))

/-- `ViewOK` at a binder view from its two expression children. -/
theorem viewOK_bind2 {st : EStore} {v : ENodeView} {ty b : EIdx}
    (hty : (st.view ty).isSome = true) (hb : (st.view b).isSome = true)
    (hv : v.echildren = [ty, b] ∧ v.nchildren = [] ∧ v.lchildren = [] ∧
      v.lschildren = [] := by simp [ENodeView.echildren, ENodeView.nchildren,
        ENodeView.lchildren, ENodeView.lschildren]) :
    st.ViewOK v :=
  ⟨by intro c hc; rw [hv.1] at hc; simp at hc
      rcases hc with rfl | rfl
      · exact hty
      · exact hb,
   by intro c hc; rw [hv.2.1] at hc; simp at hc,
   by intro c hc; rw [hv.2.2.1] at hc; simp at hc,
   by intro c hc; rw [hv.2.2.2] at hc; simp at hc⟩

/-- `arena::monad::intern_e_lam` at `WOutE`. -/
theorem intern_e_lam_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    (ty b : arena.handle.EIdx) (m : kernel.expr.BinderMeta)
    (hpw : ConRon.Refine.PropWhenWF m.pw)
    (hview : lst.store.ViewOK (.lam (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)))
    {o} (hrun : arena.monad.intern_e_lam pers st ty b m = ok o) :
    WOutE Q pers st lst o
      (Arena.internE (.lam (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m))) := by
  rw [arena.monad.intern_e_lam] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_lam_abs (ls := lst.store) hrel.store hinv.store hfrozen hrel.storeWF hpw hp
  refine wout_intern_tail hQ hrel hinv hq hview
    (fun hcap hbm => internE_run_of_caps hcap hbm) ?_ herr
  intro hh hr
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hok hh hr
  have hiv := intern_lam_eq (ty := absEIdx ty) (b := absEIdx b) hrel.storeWF a4
  rw [← hiv] at a1 a2
  exact ⟨a1, a2, a3, a5, a4, a6, a7⟩

/-- `arena::monad::intern_e_forall_e` at `WOutE`. -/
theorem intern_e_forall_e_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    (ty b : arena.handle.EIdx) (m : kernel.expr.BinderMeta)
    (hpw : ConRon.Refine.PropWhenWF m.pw)
    (hview : lst.store.ViewOK
      (.forallE (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)))
    {o} (hrun : arena.monad.intern_e_forall_e pers st ty b m = ok o) :
    WOutE Q pers st lst o
      (Arena.internE (.forallE (absEIdx ty) (absEIdx b)
        (ConRon.Refine.absBinderMeta m))) := by
  rw [arena.monad.intern_e_forall_e] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr⟩ :=
    estore_intern_forall_e_abs (ls := lst.store) hrel.store hinv.store hfrozen
      hrel.storeWF hpw hp
  refine wout_intern_tail hQ hrel hinv hq hview
    (fun hcap hbm => internE_run_of_caps hcap hbm) ?_ herr
  intro hh hr
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hok hh hr
  have hiv := intern_forall_e_eq (ty := absEIdx ty) (b := absEIdx b) hrel.storeWF a4
  rw [← hiv] at a1 a2
  exact ⟨a1, a2, a3, a5, a4, a6, a7⟩


/-! ## The memoised walks' shared steps (task #97-P5-Mut round 2)

What every arm of `instantiate1Go` and its four siblings does besides recurse:
the memo key, the memo probe, the projection read and what its children are,
the dangling-handle decline, and the memo write at the end.  Each is one lemma
here so that an arm is its recursion and nothing else. -/

/-- `Bridge/Rel.lean`'s `EStore.view_of_proj`, restated: `Refine2` does not
import `Bridge`.  The tier select is the same for `view` and for every
projection. -/
theorem view_of_proj' {st : EStore} {i : EIdx} {v : ENodeView}
    {α : Type} {p : ETables → EIdx → Option α} {x : α}
    (hb : ETag.isBind i.tag = false)
    (hstep : ∀ t : ETables, p t i = some x → t.get i = some v)
    (h : (if i.isPersistent then p st.pers i
          else if st.scratchOn then p st.scr i else none) = some x) :
    st.view i = some v := by
  simp only [EStore.view, hb, Bool.false_eq_true, if_false]
  by_cases hp : i.isPersistent = true
  · rw [if_pos hp] at h ⊢; exact hstep _ h
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h ⊢
    simp only [Bool.false_eq_true, if_false] at h ⊢
    by_cases hon : st.scratchOn = true
    · rw [if_pos hon] at h ⊢; exact hstep _ h
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

set_option linter.unusedSimpArgs false in
theorem view_of_viewApp' {st : EStore} {i f a : EIdx}
    (htg : i.tag = ETag.app) (h : st.viewApp i = some (f, a)) :
    st.view i = some (.app f a) :=
  view_of_proj' (by rw [htg]; decide) (fun t hh => by
    simp only [ETables.getApp, Option.map_eq_some_iff, Prod.mk.injEq] at hh
    obtain ⟨r, hr, rfl, rfl⟩ := hh
    simp [ETables.get, htg, hr, ETag.app, ETag.bvar, ETag.fvar, ETag.sort,
      ETag.const]) h

set_option linter.unusedSimpArgs false in
theorem view_of_viewLet' {st : EStore} {i ty val b : EIdx}
    (htg : i.tag = ETag.letE) (h : st.viewLet i = some (ty, val, b)) :
    st.view i = some (.letE ty val b) :=
  view_of_proj' (by rw [htg]; decide) (fun t hh => by
    simp only [ETables.getLet, Option.map_eq_some_iff, Prod.mk.injEq] at hh
    obtain ⟨r, hr, rfl, rfl, rfl⟩ := hh
    simp [ETables.get, htg, hr, ETag.letE, ETag.bvar, ETag.fvar, ETag.sort,
      ETag.const, ETag.app, ETag.isBind, ETag.lam, ETag.forallE]) h

set_option linter.unusedSimpArgs false in
theorem view_of_viewProj' {st : EStore} {i : EIdx} {n : NIdx} {k : Nat}
    {e : EIdx} (htg : i.tag = ETag.proj) (h : st.viewProj i = some (n, k, e)) :
    st.view i = some (.proj n k e) :=
  view_of_proj' (by rw [htg]; decide) (fun t hh => by
    simp only [ETables.getProj, Option.map_eq_some_iff, Prod.mk.injEq] at hh
    obtain ⟨r, hr, rfl, rfl, rfl⟩ := hh
    simp [ETables.get, htg, hr, ETag.proj, ETag.bvar, ETag.fvar, ETag.sort,
      ETag.const, ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit]) h

theorem view_of_viewBindI' {st : EStore} {i ty b : EIdx} {mi : BMIdx}
    {m : ConLeche.BinderMeta} (htg : ETag.isBind i.tag = true)
    (h1 : st.viewBindI i = some (ty, b, mi)) (h2 : st.viewBM mi = some m) :
    st.view i = some (eBindView i.tag ty b m) := by
  simp only [EStore.view, htg, if_true, EStore.viewBind, h1, h2]

theorem echildren_eBindView (tag : UInt32) (ty b : EIdx) (m : ConLeche.BinderMeta) :
    (eBindView tag ty b m).echildren = [ty, b] := by
  simp only [eBindView]; split <;> rfl

/-- **What a rebuilding walk's `viewBindI` gives it** at a well-formed store:
the datum decodes, its tag is `0`, and both expression children resolve. -/
theorem viewBindI_facts {lst : AState} (hwf : StoreWF lst.store) {i ty b : EIdx}
    {mi : BMIdx} (htg : ETag.isBind i.tag = true)
    (h1 : lst.store.viewBindI i = some (ty, b, mi)) :
    ∃ m, lst.store.viewBM mi = some m ∧ mi.tag = 0 ∧
      EResolves lst ty ∧ EResolves lst b := by
  obtain ⟨rk, hw⟩ := hwf
  obtain ⟨hs, -, htag0⟩ := hw.bmChildOK i ty b mi h1
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
  have hv := view_of_viewBindI' htg h1 hm
  refine ⟨m, hm, htag0, ?_, ?_⟩
  · exact EResolves.child ⟨rk, hw⟩ hv (by rw [echildren_eBindView]; simp)
  · exact EResolves.child ⟨rk, hw⟩ hv (by rw [echildren_eBindView]; simp)

/-- The memo key: `eidx_nat_key` is the pair. -/
theorem eidx_nat_key_abs {h : arena.handle.EIdx} {d : Std.U64}
    {k : arena.monad.EIdxNat} (hk : arena.monad.eidx_nat_key h d = ok k) :
    absEIdxNat k = (absEIdx h, absU d) := by
  rw [arena.monad.eidx_nat_key] at hk
  obtain ⟨e, he, hk⟩ := ConRon.Refine.bind_eq_ok_iff.mp hk
  have hee : e = h := dupId_eidx h e he
  have hkk : ({ h := e, d := d } : arena.monad.EIdxNat) = k := Result.ok_injective hk
  rw [← hkk, hee]; rfl

/-- The port's `fail_dangling_e` arm against the twin's `failDanglingE`. -/
theorem wout_dangling {Q : AState → Prop} {pers : arena.store.PersTier}
    {st st0 : arena.monad.AState} {lst : AState} {o}
    (hrun : (do
        let r ← arena.monad.fail_dangling_e arena.handle.EIdx
        ok (r, st0)) = ok o) :
    WOutR Q pers st lst o ((Arena.failDanglingE : AM EIdx).run lst) := by
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.monad.fail_dangling_e] at hr
  obtain ⟨s, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
  obtain ⟨v, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
  rw [fail_run hr] at hrun
  have ho := Result.ok_injective hrun
  rw [← ho]
  exact failDanglingE_errSim lst

/-- A port that DUPLICATES a handle and answers it, at an unchanged state. -/
theorem wout_dup {Q : AState → Prop} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hr : EResolves lst (absEIdx h)) (hq : Q lst)
    (hrun : (do
        let e ← arena.handle.EIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h
        ok (core.result.Result.Ok e, st)) = ok o) :
    WOutR Q pers st lst o (.ok (absEIdx h, lst)) := by
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [dupId_eidx _ _ he] at hrun
  have ho := Result.ok_injective hrun
  rw [← ho]
  exact WOutR.pure hrel hinv hr hq

theorem ite_ite_same {α : Sort _} {p q : Prop} [Decidable p] [Decidable q] (x y : α) :
    (if p then (if q then x else y) else y) = if p ∧ q then x else y := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-! ### The nine `(EIdx × Nat)`-keyed memos, probed, written and cleared

Stated once over the table's selector `sel`, its record update `upd` and the
twin's action, and instantiated per table in one line each: the twin's three
actions are `rfl`-level reads and writes of one `Memos` field, and the port's
are `Specs.lean`'s `*_get_run` / `*_set_run` / `*_clear_run`. -/

/-- The memo probe's twin value. -/
theorem memo_get_val {sel : Memos → Std.HashMap (EIdx × Nat) EIdx}
    {twinGet : EIdx × Nat → AM (Option EIdx)}
    (htg : ∀ key (l : AState), (twinGet key).run l = .ok ((sel l.memos)[key]?, l))
    {lst : AState} {key : EIdx × Nat} {op : Option arena.handle.EIdx}
    (h : SimR (Option.map absEIdx) lst op (twinGet key)) :
    (sel lst.memos)[key]? = op.map absEIdx := by
  have h1 := h.apply
  rw [htg] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  exact h1.1

/-- **The memo write at the end of an arm**: the step before answered `r3`
and the port records it; the twin records the same key and value, and the
memo clause survives because `r3` resolves. -/
theorem wout_memo_set {sel : Memos → Std.HashMap (EIdx × Nat) EIdx}
    {upd : Memos → Std.HashMap (EIdx × Nat) EIdx → Memos}
    (hsel : ∀ m v, sel (upd m v) = v)
    {twinSet : EIdx × Nat → EIdx → AM Unit}
    (hts : ∀ key r (l : AState), (twinSet key r).run l
      = .ok ((), { l with memos := upd l.memos ((sel l.memos).insert key r) }))
    {pers : arena.store.PersTier} {st st3 st4 : arena.monad.AState}
    {lst : AState} {x : AM EIdx} {key : EIdx × Nat} {r3 : arena.handle.EIdx}
    (hstep : WOutE (MemoRes sel) pers st lst (.Ok r3, st3) x)
    (hs4 : st4.store = st3.store)
    (hsim : ∀ lst1, AStateRel pers st3 lst1 → AStateInv pers st3 →
      SimS pers lst1 st4 (twinSet key (absEIdx r3))) :
    WOutE (MemoRes sel) pers st lst (.Ok r3, st4)
      (do let r ← x; twinSet key r; pure r) := by
  obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
    WOutE.dest hstep
  obtain ⟨lst2, hx2, hrel2, hinv2, hext2⟩ := hsim lst1 hrel1 hinv1
  rw [hts] at hx2
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hx2
  subst hx2
  refine WOutR.ok (lst' := { lst1 with
      memos := (upd lst1.memos ((sel lst1.memos).insert key (absEIdx r3))) }) ?_ hrel2 hinv2
    (Ext.trans hext1 hext2) hres1 hmono1 (by rw [hs4]; exact hfl1)
    (by rw [hs4]; exact hfl2) ?_
  · rw [StateT.run_bind, hx1]
    show (do (twinSet key (absEIdx r3)); pure (absEIdx r3) : AM EIdx).run lst1 = _
    rw [StateT.run_bind, hts]
    rfl
  · intro kk rr hk
    simp only [hsel, Std.HashMap.getElem?_insert] at hk
    split at hk
    · simp only [Option.some.injEq] at hk
      rw [← hk]; exact hres1
    · exact hq1 kk rr hk

/-- **The memo clear, at both sides**: the port's store is unmoved and the
twin's post-state is the pre-state with the table emptied. -/
theorem wmemo_clear_step
    {upd : Memos → Std.HashMap (EIdx × Nat) EIdx → Memos}
    {twinClear : AM Unit}
    (htc : ∀ l : AState, twinClear.run l = .ok ((), { l with memos := upd l.memos ∅ }))
    {pers : arena.store.PersTier} {st' : arena.monad.AState} {lst : AState}
    (hsim : SimS pers lst st' twinClear) :
    twinClear.run lst = .ok ((), { lst with memos := upd lst.memos ∅ }) ∧
      AStateRel pers st' { lst with memos := upd lst.memos ∅ } ∧
      AStateInv pers st' := by
  obtain ⟨lst1, hx1, hrel1, hinv1, -⟩ := hsim
  rw [htc] at hx1
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hx1
  rw [← hx1] at hrel1
  exact ⟨htc lst, hrel1, hinv1⟩

/-! #### `inst1C` -/

theorem inst1_get_val {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {op : Option arena.handle.EIdx}
    (hop : arena.monad.inst1_get st k = ok op) :
    lst.memos.inst1C[absEIdxNat k]? = op.map absEIdx :=
  memo_get_val (sel := Memos.inst1C) (fun _ _ => rfl) (inst1_get_run hrel hinv hop)

theorem inst1_set_store {st st' : arena.monad.AState} {k r}
    (h : arena.monad.inst1_set st k r = ok st') : st'.store = st.store := by
  rw [arena.monad.inst1_set] at h
  obtain ⟨e, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

theorem wout_inst1_set {pers : arena.store.PersTier} {st st3 st4 : arena.monad.AState}
    {lst : AState} {x : AM EIdx} {k : arena.monad.EIdxNat} {r3 : arena.handle.EIdx}
    (hstep : WOutE (MemoRes Memos.inst1C) pers st lst (.Ok r3, st3) x)
    (hset : arena.monad.inst1_set st3 k r3 = ok st4) :
    WOutE (MemoRes Memos.inst1C) pers st lst (.Ok r3, st4)
      (do let r ← x; Arena.inst1Set (absEIdxNat k) r; pure r) :=
  wout_memo_set (upd := fun m v => { m with inst1C := v }) (fun _ _ => rfl)
    (fun _ _ _ => rfl) hstep (inst1_set_store hset)
    (fun _ hr hi => inst1_set_run hr hi hset)

theorem inst1_clear_store {st st' : arena.monad.AState}
    (h : arena.monad.inst1_clear st = ok st') : st'.store = st.store := by
  rw [arena.monad.inst1_clear] at h
  obtain ⟨hm0, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

/-! #### `instLC` -/

theorem inst_l_get_val {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {op : Option arena.handle.EIdx}
    (hop : arena.monad.inst_l_get st k = ok op) :
    lst.memos.instLC[absEIdxNat k]? = op.map absEIdx :=
  memo_get_val (sel := Memos.instLC) (fun _ _ => rfl) (inst_l_get_run hrel hinv hop)

theorem inst_l_set_store {st st' : arena.monad.AState} {k r}
    (h : arena.monad.inst_l_set st k r = ok st') : st'.store = st.store := by
  rw [arena.monad.inst_l_set] at h
  obtain ⟨e, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

theorem wout_inst_l_set {pers : arena.store.PersTier} {st st3 st4 : arena.monad.AState}
    {lst : AState} {x : AM EIdx} {k : arena.monad.EIdxNat} {r3 : arena.handle.EIdx}
    (hstep : WOutE (MemoRes Memos.instLC) pers st lst (.Ok r3, st3) x)
    (hset : arena.monad.inst_l_set st3 k r3 = ok st4) :
    WOutE (MemoRes Memos.instLC) pers st lst (.Ok r3, st4)
      (do let r ← x; Arena.instLSet (absEIdxNat k) r; pure r) :=
  wout_memo_set (upd := fun m v => { m with instLC := v }) (fun _ _ => rfl)
    (fun _ _ _ => rfl) hstep (inst_l_set_store hset)
    (fun _ hr hi => inst_l_set_run hr hi hset)

theorem inst_l_clear_store {st st' : arena.monad.AState}
    (h : arena.monad.inst_l_clear st = ok st') : st'.store = st.store := by
  rw [arena.monad.inst_l_clear] at h
  obtain ⟨hm0, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

/-- `arena::monad::intern_e_fvar` at `WOutE`. -/
theorem intern_e_fvar_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    (idx : Std.U64) (ty : arena.handle.EIdx)
    (hview : lst.store.ViewOK (.fvar (absU idx) (absEIdx ty)))
    {o} (hrun : arena.monad.intern_e_fvar pers st idx ty = ok o) :
    WOutE Q pers st lst o (Arena.internFVarE (absU idx) (absEIdx ty)) := by
  rw [arena.monad.intern_e_fvar] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, hfl⟩ :=
    estore_intern_fvar_abs (ls := lst.store) hrel.store hinv.store hfrozen
      (fun h => hchild_fvar hrel.storeWF h) hp
  exact wout_intern_tail hQ hrel hinv hq hview
    (fun hcap _ => by rw [Arena.internFVarE]; exact internE_run_of_cap rfl hcap)
    (nb_hok rfl hok hfl) herr

/-! ### The `internRebuilt` cutoff at `WOutE`

A rebuilding walk answers the handle it was HANDED when nothing changed, and
interns otherwise; `wout_dup` is the first and the `intern_e_*_res` the
second. -/

/-- The port's handle equality is the twin's, through `absEIdx`'s
injectivity. -/
theorem eidx_eq2_abs {a b : arena.handle.EIdx} {c : Bool}
    (h : arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok c) :
    (absEIdx a == absEIdx b) = c := by
  have := eidx_eq2 a b c trivial trivial h
  subst this
  by_cases hab : a = b
  · subst hab; simp
  · have : absEIdx a ≠ absEIdx b := fun hh => hab (absEIdx_inj hh)
    simp [hab, this]

theorem intern_rebuilt_fvar_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    {h : arena.handle.EIdx} {same : Bool} {idx : Std.U64} {ty : arena.handle.EIdx}
    (hh : EResolves lst (absEIdx h)) (hty : EResolves lst (absEIdx ty))
    {o} (hrun : arena.expr_ops.intern_rebuilt_fvar pers st h same idx ty = ok o) :
    WOutE Q pers st lst o (internRebuiltFVar (absEIdx h) same (absU idx) (absEIdx ty)) := by
  rw [arena.expr_ops.intern_rebuilt_fvar] at hrun
  show WOutR Q pers st lst o ((internRebuiltFVar (absEIdx h) same (absU idx)
    (absEIdx ty)).run lst)
  rw [internRebuiltFVar]
  cases same with
  | true => rw [if_pos rfl] at hrun; rw [if_pos rfl]; exact wout_dup hrel hinv hh hq hrun
  | false =>
    rw [if_neg (by simp)] at hrun; rw [if_neg (by simp)]
    exact intern_e_fvar_res hQ hrel hinv hfrozen hq idx ty (viewOK_fvar hty) hrun

theorem intern_rebuilt_app_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    {h : arena.handle.EIdx} {same : Bool} {f a : arena.handle.EIdx}
    (hh : EResolves lst (absEIdx h)) (hf : EResolves lst (absEIdx f))
    (ha : EResolves lst (absEIdx a))
    {o} (hrun : arena.expr_ops.intern_rebuilt_app pers st h same f a = ok o) :
    WOutE Q pers st lst o (internRebuiltApp (absEIdx h) same (absEIdx f) (absEIdx a)) := by
  rw [arena.expr_ops.intern_rebuilt_app] at hrun
  show WOutR Q pers st lst o ((internRebuiltApp (absEIdx h) same (absEIdx f)
    (absEIdx a)).run lst)
  rw [internRebuiltApp]
  cases same with
  | true => rw [if_pos rfl] at hrun; rw [if_pos rfl]; exact wout_dup hrel hinv hh hq hrun
  | false =>
    rw [if_neg (by simp)] at hrun; rw [if_neg (by simp)]
    exact intern_e_app_res hQ hrel hinv hfrozen hq f a (viewOK_app hf ha) hrun

theorem intern_rebuilt_let_e_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    {h : arena.handle.EIdx} {same : Bool} {ty val b : arena.handle.EIdx}
    (hh : EResolves lst (absEIdx h)) (hty : EResolves lst (absEIdx ty))
    (hval : EResolves lst (absEIdx val)) (hb : EResolves lst (absEIdx b))
    {o} (hrun : arena.expr_ops.intern_rebuilt_let_e pers st h same ty val b = ok o) :
    WOutE Q pers st lst o
      (internRebuiltLetE (absEIdx h) same (absEIdx ty) (absEIdx val) (absEIdx b)) := by
  rw [arena.expr_ops.intern_rebuilt_let_e] at hrun
  show WOutR Q pers st lst o ((internRebuiltLetE (absEIdx h) same (absEIdx ty)
    (absEIdx val) (absEIdx b)).run lst)
  rw [internRebuiltLetE]
  cases same with
  | true => rw [if_pos rfl] at hrun; rw [if_pos rfl]; exact wout_dup hrel hinv hh hq hrun
  | false =>
    rw [if_neg (by simp)] at hrun; rw [if_neg (by simp)]
    exact intern_e_let_e_res hQ hrel hinv hfrozen hq ty val b (viewOK_letE hty hval hb) hrun

theorem intern_rebuilt_proj_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    {h : arena.handle.EIdx} {same : Bool} {n : arena.handle.NIdx} {i : Std.U64}
    {e : arena.handle.EIdx}
    (hh : EResolves lst (absEIdx h)) (hn : (lst.store.ns.view (absNIdx n)).isSome = true)
    (he : EResolves lst (absEIdx e))
    {o} (hrun : arena.expr_ops.intern_rebuilt_proj pers st h same n i e = ok o) :
    WOutE Q pers st lst o
      (internRebuiltProj (absEIdx h) same (absNIdx n) (absU i) (absEIdx e)) := by
  rw [arena.expr_ops.intern_rebuilt_proj] at hrun
  show WOutR Q pers st lst o ((internRebuiltProj (absEIdx h) same (absNIdx n) (absU i)
    (absEIdx e)).run lst)
  rw [internRebuiltProj]
  cases same with
  | true => rw [if_pos rfl] at hrun; rw [if_pos rfl]; exact wout_dup hrel hinv hh hq hrun
  | false =>
    rw [if_neg (by simp)] at hrun; rw [if_neg (by simp)]
    exact intern_e_proj_res hQ hrel hinv hfrozen hq n i e (viewOK_proj hn he) hrun

theorem intern_rebuilt_lam_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    {h : arena.handle.EIdx} {same : Bool} {ty b : arena.handle.EIdx}
    {m : kernel.expr.BinderMeta} (hpw : ConRon.Refine.PropWhenWF m.pw)
    (hh : EResolves lst (absEIdx h)) (hty : EResolves lst (absEIdx ty))
    (hb : EResolves lst (absEIdx b))
    {o} (hrun : arena.expr_ops.intern_rebuilt_lam pers st h same ty b m = ok o) :
    WOutE Q pers st lst o
      (internRebuiltLam (absEIdx h) same (absEIdx ty) (absEIdx b)
        (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.expr_ops.intern_rebuilt_lam] at hrun
  show WOutR Q pers st lst o ((internRebuiltLam (absEIdx h) same (absEIdx ty)
    (absEIdx b) (ConRon.Refine.absBinderMeta m)).run lst)
  rw [internRebuiltLam]
  cases same with
  | true => rw [if_pos rfl] at hrun; rw [if_pos rfl]; exact wout_dup hrel hinv hh hq hrun
  | false =>
    rw [if_neg (by simp)] at hrun; rw [if_neg (by simp)]
    exact intern_e_lam_res hQ hrel hinv hfrozen hq ty b m hpw (viewOK_bind2 hty hb) hrun

theorem intern_rebuilt_forall_e_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    {h : arena.handle.EIdx} {same : Bool} {ty b : arena.handle.EIdx}
    {m : kernel.expr.BinderMeta} (hpw : ConRon.Refine.PropWhenWF m.pw)
    (hh : EResolves lst (absEIdx h)) (hty : EResolves lst (absEIdx ty))
    (hb : EResolves lst (absEIdx b))
    {o} (hrun : arena.expr_ops.intern_rebuilt_forall_e pers st h same ty b m = ok o) :
    WOutE Q pers st lst o
      (internRebuiltForallE (absEIdx h) same (absEIdx ty) (absEIdx b)
        (ConRon.Refine.absBinderMeta m)) := by
  rw [arena.expr_ops.intern_rebuilt_forall_e] at hrun
  show WOutR Q pers st lst o ((internRebuiltForallE (absEIdx h) same (absEIdx ty)
    (absEIdx b) (ConRon.Refine.absBinderMeta m)).run lst)
  rw [internRebuiltForallE]
  cases same with
  | true => rw [if_pos rfl] at hrun; rw [if_pos rfl]; exact wout_dup hrel hinv hh hq hrun
  | false =>
    rw [if_neg (by simp)] at hrun; rw [if_neg (by simp)]
    exact intern_e_forall_e_res hQ hrel hinv hfrozen hq ty b m hpw (viewOK_bind2 hty hb) hrun

/-! #### `resetC` -/

theorem reset_get_val {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {op : Option arena.handle.EIdx}
    (hop : arena.monad.reset_get st k = ok op) :
    lst.memos.resetC[absEIdxNat k]? = op.map absEIdx :=
  memo_get_val (sel := Memos.resetC) (fun _ _ => rfl) (reset_get_run hrel hinv hop)

theorem reset_set_store {st st' : arena.monad.AState} {k r}
    (h : arena.monad.reset_set st k r = ok st') : st'.store = st.store := by
  rw [arena.monad.reset_set] at h
  obtain ⟨e, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

theorem wout_reset_set {pers : arena.store.PersTier} {st st3 st4 : arena.monad.AState}
    {lst : AState} {x : AM EIdx} {k : arena.monad.EIdxNat} {r3 : arena.handle.EIdx}
    (hstep : WOutE (MemoRes Memos.resetC) pers st lst (.Ok r3, st3) x)
    (hset : arena.monad.reset_set st3 k r3 = ok st4) :
    WOutE (MemoRes Memos.resetC) pers st lst (.Ok r3, st4)
      (do let r ← x; Arena.resetSet (absEIdxNat k) r; pure r) :=
  wout_memo_set (upd := fun m v => { m with resetC := v }) (fun _ _ => rfl)
    (fun _ _ _ => rfl) hstep (reset_set_store hset)
    (fun _ hr hi => reset_set_run hr hi hset)

theorem reset_clear_store {st st' : arena.monad.AState}
    (h : arena.monad.reset_clear st = ok st') : st'.store = st.store := by
  rw [arena.monad.reset_clear] at h
  obtain ⟨hm0, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

/-- The parse placeholder datum, `⟨.never⟩`, as the port builds it. -/
theorem never_meta {pw : Generated.kernel.prop_when.PropWhen}
    {m2 : kernel.expr.BinderMeta}
    (hpw : kernel.prop_when.never = ok pw) (hm2 : kernel.expr.binder_meta pw = ok m2) :
    ConRon.Refine.absBinderMeta m2 = ⟨.never⟩ ∧ ConRon.Refine.PropWhenWF m2.pw := by
  have h3 : m2 = ⟨pw⟩ := by
    rw [kernel.expr.binder_meta] at hm2
    exact (Result.ok_injective hm2).symm
  subst h3
  refine ⟨?_, ConRon.Refine.PropWhenWF.never hpw⟩
  simp only [ConRon.Refine.absBinderMeta]
  rw [ConRon.Refine.PropWhen.absPropWhen_never (ConRon.Refine.PropWhen.never_shape hpw).2]

/-! ### A walk that interns UNCONDITIONALLY against a twin that cuts off

`renameConstsGo`'s twin answers `h` when nothing changed (`internRebuilt*`),
where the port re-interns the node regardless.  The two agree because
hash-consing the node `h` already names hands back `h` itself: `consP` /
`consS` / `fresh` say the cons tables answer exactly the handle whose view it
is. -/

/-- **The cons tables answer the handle a view came from.** -/
theorem find?_of_view {st : EStore} (hwf : StoreWF st) {h : EIdx} {v : ENodeView}
    (hv : st.view h = some v) : st.find? v = some h := by
  obtain ⟨rk, hw⟩ := hwf
  cases hp : h.isPersistent with
  | true =>
    have hpf : st.persFind? v = some h := (hw.consP v h).mpr ⟨hv, hp⟩
    simp only [EStore.persFind?] at hpf
    simp only [EStore.find?]
    split at hpf
    · cases hpf
    · rename_i mi hmi
      simp only [EStore.findAt, hpf]
  | false =>
    have hsf : st.scrFind? v = some h := (hw.consS v h).mpr ⟨hv, hp⟩
    have hpf : st.persFind? v = none := hw.fresh v h hsf
    have hon : st.scratchOn = true := by
      cases hc : st.scratchOn with
      | false => rw [EStore.view_off hp hc] at hv; cases hv
      | true => rfl
    simp only [EStore.scrFind?] at hsf
    simp only [EStore.persFind?] at hpf
    simp only [EStore.find?]
    split at hsf
    · cases hsf
    · rename_i mi hmi
      have hpf' : st.pers.find? v mi = none := by rw [hmi] at hpf; exact hpf
      simp only [EStore.findAt, hpf', hon, if_true, hsf]

theorem internE_run_of_find {lst : AState} {w : ENodeView} {h : EIdx}
    (hf : lst.store.find? w = some h) : (Arena.internE w).run lst = .ok (h, lst) := by
  rw [Arena.internE, run_get_bind, hf]
  rfl

/-- The cutoff against the unconditional intern. -/
theorem wout_same_of_intern {Q : AState → Prop} {pers st lst o} {w : ENodeView}
    {h : EIdx} {same : Bool} (hwf : StoreWF lst.store)
    (hstep : WOutE Q pers st lst o (Arena.internE w))
    (hsame : same = true → lst.store.view h = some w) :
    WOutE Q pers st lst o (if same then pure h else Arena.internE w) := by
  cases same with
  | false => exact hstep
  | true =>
    show WOutR Q pers st lst o ((pure h : AM EIdx).run lst)
    exact WOutR.of_eq hstep
      (by rw [internE_run_of_find (find?_of_view hwf (hsame rfl))]; rfl)

/-- `arena::monad::intern_e_const` at `WOutE`. -/
theorem intern_e_const_res {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true) (hq : Q lst)
    (n : arena.handle.NIdx) (us : arena.handle.LsIdx)
    (hview : lst.store.ViewOK (.const (absNIdx n) (absLsIdx us)))
    {o} (hrun : arena.monad.intern_e_const pers st n us = ok o) :
    WOutE Q pers st lst o (Arena.internE (.const (absNIdx n) (absLsIdx us))) := by
  rw [arena.monad.intern_e_const] at hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, e⟩ := p
  have ho : (r, ({ st with store := e } : arena.monad.AState)) = o :=
    Result.ok_injective hrun
  subst ho
  obtain ⟨hok, herr, hfl⟩ :=
    estore_intern_const_abs (ls := lst.store) hrel.store hinv.store hfrozen
      (fun h => hchild_const hrel.storeWF h) hp
  exact wout_intern_tail hQ hrel hinv hq hview
    (fun hcap _ => internE_run_of_cap rfl hcap) (nb_hok rfl hok hfl) herr

/-- **The renaming dictionary names live constants** — what makes the `const`
arm's intern well formed. -/
def RenameRes {F : Type} (inst : arena.expr_ops.NIdxToNIdx F) (f : F) (ls : EStore) :
    Prop :=
  ∀ n r, inst.rename f n = ok r → (ls.ns.view (absNIdx r)).isSome = true

theorem RenameRes.mono {F : Type} {inst : arena.expr_ops.NIdxToNIdx F} {f : F}
    {ls ls' : EStore} (h : EViewExt ls ls') (hr : RenameRes inst f ls) :
    RenameRes inst f ls' := fun n r hn => h.nsres (hr n r hn)

/-! #### `renameC` -/

theorem rename_get_val {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {op : Option arena.handle.EIdx}
    (hop : arena.monad.rename_get st k = ok op) :
    lst.memos.renameC[absEIdxNat k]? = op.map absEIdx :=
  memo_get_val (sel := Memos.renameC) (fun _ _ => rfl) (rename_get_run hrel hinv hop)

theorem rename_set_store {st st' : arena.monad.AState} {k r}
    (h : arena.monad.rename_set st k r = ok st') : st'.store = st.store := by
  rw [arena.monad.rename_set] at h
  obtain ⟨e, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

theorem wout_rename_set {pers : arena.store.PersTier} {st st3 st4 : arena.monad.AState}
    {lst : AState} {x : AM EIdx} {k : arena.monad.EIdxNat} {r3 : arena.handle.EIdx}
    (hstep : WOutE (MemoRes Memos.renameC) pers st lst (.Ok r3, st3) x)
    (hset : arena.monad.rename_set st3 k r3 = ok st4) :
    WOutE (MemoRes Memos.renameC) pers st lst (.Ok r3, st4)
      (do let r ← x; Arena.renameSet (absEIdxNat k) r; pure r) :=
  wout_memo_set (upd := fun m v => { m with renameC := v }) (fun _ _ => rfl)
    (fun _ _ _ => rfl) hstep (rename_set_store hset)
    (fun _ hr hi => rename_set_run hr hi hset)

theorem rename_clear_store {st st' : arena.monad.AState}
    (h : arena.monad.rename_clear st = ok st') : st'.store = st.store := by
  rw [arena.monad.rename_clear] at h
  obtain ⟨hm0, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

/-! ## `instantiate1` — the memoised single substitution

`Specs.lean` primitives: `derivedE`, `inst1Get`, `inst1Set`, `inst1Clear`,
`viewApp`, `viewBindI`, `viewBVar`, `viewLet`, `viewProj`, `failDanglingE`,
`internAppE`, `internBindIE`, `internBVarE`, `internLetEE`, `internProjE`.
This is the function round 3 priced at 22 lines of proof, and it is the
template for the other four walks of the same shape. -/

/-- A bind whose first step's run is known. -/
theorem run_bind_of {α β : Type} {x : AM α} {f : α → AM β} {lst lst' : AState} {a : α}
    (hx : x.run lst = .ok (a, lst')) : (x >>= f).run lst = (f a).run lst' := by
  rw [StateT.run_bind, hx]; rfl

/-- The `instantiate1_go` statement at one fuel value, at `WOutE` with the
memo clause as its side invariant. -/
def I1GoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {v : arena.handle.EIdx} {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st →
    (st.store.shared_on = true → st.store.scratch_on = true) →
    EResolves lst (absEIdx v) → EResolves lst (absEIdx h) →
    MemoRes Memos.inst1C lst →
    arena.expr_ops.instantiate1_go pers st v fuel h d = ok o →
    WOutE (MemoRes Memos.inst1C) pers st lst o
      (instantiate1Go (absEIdx v) (absU fuel) (absEIdx h) (absU d))

private theorem instantiate1_go_aux (n : Nat) : I1GoAt n := by
  induction n with
  | zero =>
    intro pers st lst v fuel h d o hn hrel hinv hfrozen hv hh hm hrun
    rw [arena.expr_ops.instantiate1_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨vv, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hrrv := fail_run hrr
    have ho := Result.ok_injective hrun
    rw [← ho, hrrv]
    show AErrSim _ ((instantiate1Go (absEIdx v) (absU fuel) (absEIdx h) (absU d)).run lst)
    rw [show absU fuel = 0 from hn, instantiate1Go_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst v fuel h d o hn hrel hinv hfrozen hv hh hm hrun
    rw [arena.expr_ops.instantiate1_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨der, hder, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨sr, hsr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [ite_ite_same] at hrun
    -- the derived cutoff
    have hderE := hder
    rw [arena.monad.derived_e] at hderE
    obtain ⟨hbv, -, -⟩ := derObsE_fields (estore_derived_abs hrel.store hderE)
    have hbb := ConRon.Refine.Expr.bvar_of_data_val hb
    have hsrv := ConRon.Refine.Expr.sat_range_val hsr
    have hbn : (ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat = absU b := by
      rw [hbv]; exact hbb.symm
    have hcond : ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat
          < ConLeche.satRange &&
        (ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat ≤ absU d) = true
        ↔ (b < sr ∧ b ≤ d) := by
      rw [hbn, ← hsrv]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by scalar_tac, by scalar_tac⟩
      · rintro ⟨h1, h2⟩; exact ⟨by scalar_tac, by scalar_tac⟩
    show WOutR (MemoRes Memos.inst1C) pers st lst o
      ((instantiate1Go (absEIdx v) (absU fuel) (absEIdx h) (absU d)).run lst)
    rw [show absU fuel = m + 1 from hn, instantiate1Go_succ, StateT.run_bind,
      show (derivedE (absEIdx h)).run lst
        = .ok (lst.store.derived (absEIdx h), lst) from rfl]
    show WOutR (MemoRes Memos.inst1C) pers st lst o
      ((if ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat
            < ConLeche.satRange &&
          (ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat ≤ absU d) = true
        then pure (absEIdx h)
        else
          if (absEIdx h).tag == ETag.app then instantiate1ArmApp (absEIdx v) m (absEIdx h) (absU d)
          else if ETag.isBind (absEIdx h).tag then
            instantiate1ArmBind (absEIdx v) m (absEIdx h) (absU d)
          else if (absEIdx h).tag == ETag.bvar then
            instantiate1ArmBVar (absEIdx v) (absEIdx h) (absU d)
          else if (absEIdx h).tag == ETag.letE then
            instantiate1ArmLet (absEIdx v) m (absEIdx h) (absU d)
          else if (absEIdx h).tag == ETag.proj then
            instantiate1ArmProj (absEIdx v) m (absEIdx h) (absU d)
          else pure (absEIdx h)).run lst)
    by_cases hc : b < sr ∧ b ≤ d
    · rw [if_pos hc] at hrun
      rw [if_pos (hcond.mpr hc)]
      exact wout_dup hrel hinv hh hm hrun
    rw [if_neg hc] at hrun
    rw [if_neg (fun h' => hc (hcond.mp h'))]
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htg := eidx_tag_abs ht
    rw [htg]
    have hi1 : ∀ i1 : Std.U64, (fuel - 1#u64 = ok i1) → i1.val = m := by
      intro i1 hi1
      have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
        (ConRon.Refine.Nat.usub_val hi1).2
      rw [h1, hn]; rfl
    by_cases hA : t = arena.handle.ETAG_APP
    · rw [if_pos hA] at hrun
      rw [if_pos (show (absU32 t == ETag.app) = true by rw [hA, etag_app_abs]; simp)]
      have htA : (absEIdx h).tag = ETag.app := by rw [htg, hA, etag_app_abs]
      rw [instantiate1ArmApp]
      obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hkabs := eidx_nat_key_abs hk
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hget := (inst1_get_run hrel hinv hop).apply
      have hgv := inst1_get_val hrel hinv hop
      rw [hkabs] at hget hgv
      rw [run_bind_of hget]
      cases hopc : op with
      | some r =>
        rw [hopc] at hrun hgv
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact WOutR.pure hrel hinv (hm _ _ hgv) hm
      | none =>
        rw [hopc] at hrun
        simp only [Option.map_none]
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hva := (view_app_run hrel ho1).apply
        rw [run_bind_of hva]
        cases ho1c : o1 with
        | none =>
          rw [ho1c] at hrun
          exact wout_dangling hrun
        | some p =>
          rw [ho1c] at hrun
          obtain ⟨f, a⟩ := p
          have hvap : lst.store.viewApp (absEIdx h) = some (absEIdx f, absEIdx a) := by
            have h2 : (Arena.viewApp (absEIdx h)).run lst
                = .ok (lst.store.viewApp (absEIdx h), lst) := rfl
            rw [h2, ho1c] at hva
            simpa [absPairE] using hva
          have hvA := view_of_viewApp' htA hvap
          have hfR : EResolves lst (absEIdx f) :=
            EResolves.child hrel.storeWF hvA (by simp [ENodeView.echildren])
          have haR : EResolves lst (absEIdx a) :=
            EResolves.child hrel.storeWF hvA (by simp [ENodeView.echildren])
          simp only [Option.map_some, absPairE]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen hv hfR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok f2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res hv) (hmono1.res haR) hq1 hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok a2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep := intern_e_app_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                f2 a2 (viewOK_app (hmono2.res hres1) hres2) hp3
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok r4 =>
                rw [hr3] at hrun hstep
                obtain ⟨st4, hst4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_inst1_set hstep hst4
                rw [hkabs] at hset
                exact hset
    rw [if_neg hA] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.app) = true) by
      rw [← etag_app_abs]; simp only [beq_iff_eq]; intro hcc; exact hA (absU32_inj hcc))]
    obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hbind := etag_isBind_abs hb1
    cases b1 with
    | true =>
      rw [if_pos rfl] at hrun
      rw [if_pos hbind]
      have hbind' : ETag.isBind (absEIdx h).tag = true := by rw [htg]; exact hbind
      rw [instantiate1ArmBind]
      obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hkabs := eidx_nat_key_abs hk
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hget := (inst1_get_run hrel hinv hop).apply
      have hgv := inst1_get_val hrel hinv hop
      rw [hkabs] at hget hgv
      rw [run_bind_of hget]
      cases hopc : op with
      | some r =>
        rw [hopc] at hrun hgv
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact WOutR.pure hrel hinv (hm _ _ hgv) hm
      | none =>
        rw [hopc] at hrun
        simp only [Option.map_none]
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hvb := (view_bind_i_run hrel hbind' ho1).apply
        rw [run_bind_of hvb]
        cases ho1c : o1 with
        | none =>
          rw [ho1c] at hrun
          exact wout_dangling hrun
        | some p =>
          rw [ho1c] at hrun
          obtain ⟨ty, body, mi⟩ := p
          have hvbi : lst.store.viewBindI (absEIdx h)
              = some (absEIdx ty, absEIdx body, absBMIdx mi) := by
            have h2 : (Arena.viewBindI (absEIdx h)).run lst
                = .ok (lst.store.viewBindI (absEIdx h), lst) := rfl
            rw [h2, ho1c] at hvb
            simpa [absBindI] using hvb
          obtain ⟨mm, hmv, hm0, htyR, hbR⟩ := viewBindI_facts hrel.storeWF hbind' hvbi
          simp only [Option.map_some, absBindI]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen hv htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hi2v : absU i2 = absU d + 1 := by
              have h1 := ConRon.Refine.Nat.uadd_val hi2
              simpa using h1
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res hv) (hmono1.res hbR) hq1 hp2
            rw [show absU i1 = m from hi1v, hi2v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok b2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep := intern_e_bind_i_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                t hbind t2 b2 mi (hmono2.2.1 _ _ (hmono1.2.1 _ _ hmv)) hm0
                (hmono2.res hres1) hres2 hp3
              rw [← htg] at hstep
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok r4 =>
                rw [hr3] at hrun hstep
                obtain ⟨st4, hst4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_inst1_set hstep hst4
                rw [hkabs] at hset
                exact hset
    | false =>
    rw [if_neg (by simp)] at hrun
    rw [if_neg (by rw [hbind]; simp)]
    by_cases hBV : t = arena.handle.ETAG_BVAR
    · rw [if_pos hBV] at hrun
      rw [if_pos (show (absU32 t == ETag.bvar) = true by rw [hBV, etag_bvar_abs]; simp)]
      rw [instantiate1ArmBVar]
      obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hvb := (view_bvar_run hrel ho1).apply
      rw [run_bind_of hvb]
      cases ho1c : o1 with
      | none =>
        rw [ho1c] at hrun
        exact wout_dangling hrun
      | some i1 =>
        rw [ho1c] at hrun
        simp only at hrun
        simp only [Option.map_some]
        by_cases hq : i1 = d
        · rw [if_pos hq] at hrun
          rw [if_pos (by rw [hq])]
          exact wout_dup hrel hinv hv hm hrun
        rw [if_neg hq] at hrun
        rw [if_neg (fun h' => hq (Std.UScalar.eq_of_val_eq h'))]
        by_cases hgt : i1 > d
        · rw [if_pos hgt] at hrun
          rw [if_pos (show absU i1 > absU d by scalar_tac)]
          obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v : absU i2 = absU i1 - 1 := (ConRon.Refine.Nat.usub_val hi2).2
          rw [← hi2v]
          exact intern_e_bvar_res (MemoRes.stable _) hrel hinv hfrozen hm i2 hrun
        · rw [if_neg hgt] at hrun
          rw [if_neg (show ¬ (absU i1 > absU d) by scalar_tac)]
          exact wout_dup hrel hinv hh hm hrun
    rw [if_neg hBV] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.bvar) = true) by
      rw [← etag_bvar_abs]; simp only [beq_iff_eq]; intro hcc; exact hBV (absU32_inj hcc))]
    by_cases hL : t = arena.handle.ETAG_LET_E
    · rw [if_pos hL] at hrun
      rw [if_pos (show (absU32 t == ETag.letE) = true by rw [hL, etag_letE_abs]; simp)]
      have htL : (absEIdx h).tag = ETag.letE := by rw [htg, hL, etag_letE_abs]
      rw [instantiate1ArmLet]
      obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hkabs := eidx_nat_key_abs hk
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hget := (inst1_get_run hrel hinv hop).apply
      have hgv := inst1_get_val hrel hinv hop
      rw [hkabs] at hget hgv
      rw [run_bind_of hget]
      cases hopc : op with
      | some r =>
        rw [hopc] at hrun hgv
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact WOutR.pure hrel hinv (hm _ _ hgv) hm
      | none =>
        rw [hopc] at hrun
        simp only [Option.map_none]
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hvl := (view_let_run hrel ho1).apply
        rw [run_bind_of hvl]
        cases ho1c : o1 with
        | none =>
          rw [ho1c] at hrun
          exact wout_dangling hrun
        | some p =>
          rw [ho1c] at hrun
          obtain ⟨ty, val, body⟩ := p
          have hvlp : lst.store.viewLet (absEIdx h)
              = some (absEIdx ty, absEIdx val, absEIdx body) := by
            have h2 : (Arena.viewLet (absEIdx h)).run lst
                = .ok (lst.store.viewLet (absEIdx h), lst) := rfl
            rw [h2, ho1c] at hvl
            simpa [absLetT] using hvl
          have hvL := view_of_viewLet' htL hvlp
          have htyR : EResolves lst (absEIdx ty) :=
            EResolves.child hrel.storeWF hvL (by simp [ENodeView.echildren])
          have hvalR : EResolves lst (absEIdx val) :=
            EResolves.child hrel.storeWF hvL (by simp [ENodeView.echildren])
          have hbR : EResolves lst (absEIdx body) :=
            EResolves.child hrel.storeWF hvL (by simp [ENodeView.echildren])
          simp only [Option.map_some, absLetT]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen hv htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res hv) (hmono1.res hvalR)
              hq1 hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok w2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have hi2v : absU i2 = absU d + 1 := by
                have h1 := ConRon.Refine.Nat.uadd_val hi2
                simpa using h1
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hrec3 := ih hi1v hrel2 hinv2 hfroz2 (hmono2.res (hmono1.res hv))
                (hmono2.res (hmono1.res hbR)) hq2 hp3
              rw [show absU i1 = m from hi1v, hi2v] at hrec3
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hrec3
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hrec3.err rfl)
              | Ok b2 =>
                rw [hr3] at hrun hrec3
                obtain ⟨lst3, hx3, hrel3, hinv3, hext3, hres3, hmono3, hfl5, hfl6, hq3⟩ :=
                  hrec3.dest
                refine WOutE.bind hx3 hext3 hmono3 hfl5 hfl6 ?_
                have hfroz3 : st3.store.shared_on = true → st3.store.scratch_on = true := by
                  intro hs; rw [hfl6]; exact hfroz2 (hfl5 ▸ hs)
                obtain ⟨p4, hp4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                obtain ⟨r4, st4⟩ := p4
                have hstep := intern_e_let_e_res (MemoRes.stable _) hrel3 hinv3 hfroz3 hq3
                  t2 w2 b2 (viewOK_letE (hmono3.res (hmono2.res hres1))
                    (hmono3.res hres2) hres3) hp4
                cases hr4 : r4 with
                | Err e =>
                  rw [hr4] at hrun hstep
                  have ho := Result.ok_injective hrun
                  rw [← ho]
                  exact wout_err_bind (hstep.err rfl)
                | Ok r5 =>
                  rw [hr4] at hrun hstep
                  obtain ⟨st5, hst5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                  have ho := Result.ok_injective hrun
                  rw [← ho]
                  have hset := wout_inst1_set hstep hst5
                  rw [hkabs] at hset
                  exact hset
    rw [if_neg hL] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.letE) = true) by
      rw [← etag_letE_abs]; simp only [beq_iff_eq]; intro hcc; exact hL (absU32_inj hcc))]
    by_cases hP : t = arena.handle.ETAG_PROJ
    · rw [if_pos hP] at hrun
      rw [if_pos (show (absU32 t == ETag.proj) = true by rw [hP, etag_proj_abs]; simp)]
      have htP : (absEIdx h).tag = ETag.proj := by rw [htg, hP, etag_proj_abs]
      rw [instantiate1ArmProj]
      obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hkabs := eidx_nat_key_abs hk
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hget := (inst1_get_run hrel hinv hop).apply
      have hgv := inst1_get_val hrel hinv hop
      rw [hkabs] at hget hgv
      rw [run_bind_of hget]
      cases hopc : op with
      | some r =>
        rw [hopc] at hrun hgv
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact WOutR.pure hrel hinv (hm _ _ hgv) hm
      | none =>
        rw [hopc] at hrun
        simp only [Option.map_none]
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hvp := (view_proj_run hrel ho1).apply
        rw [run_bind_of hvp]
        cases ho1c : o1 with
        | none =>
          rw [ho1c] at hrun
          exact wout_dangling hrun
        | some p =>
          rw [ho1c] at hrun
          obtain ⟨n, i1, sub⟩ := p
          have hvpp : lst.store.viewProj (absEIdx h)
              = some (absNIdx n, absU i1, absEIdx sub) := by
            have h2 : (Arena.viewProj (absEIdx h)).run lst
                = .ok (lst.store.viewProj (absEIdx h), lst) := rfl
            rw [h2, ho1c] at hvp
            simpa [absProjT] using hvp
          have hvP := view_of_viewProj' htP hvpp
          have hsR : EResolves lst (absEIdx sub) :=
            EResolves.child hrel.storeWF hvP (by simp [ENodeView.echildren])
          have hnR : (lst.store.ns.view (absNIdx n)).isSome = true := by
            obtain ⟨rk, hw⟩ := hrel.storeWF
            exact (hw.nchildOK _ _ hvP _ (by simp [ENodeView.nchildren])).1
          simp only [Option.map_some, absProjT]
          obtain ⟨i2, hi2', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v := hi1 i2 hi2'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi2v hrel hinv hfrozen hv hsR hm hp1
          rw [show absU i2 = m from hi2v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok u =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hstep := intern_e_proj_res (MemoRes.stable _) hrel1 hinv1 hfroz1 hq1
              n i1 u (viewOK_proj (hmono1.nsres hnR) hres1) hp2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hstep
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hstep.err rfl)
            | Ok r3 =>
              rw [hr2] at hrun hstep
              obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have ho := Result.ok_injective hrun
              rw [← ho]
              have hset := wout_inst1_set hstep hst3
              rw [hkabs] at hset
              exact hset
    rw [if_neg hP] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.proj) = true) by
      rw [← etag_proj_abs]; simp only [beq_iff_eq]; intro hcc; exact hP (absU32_inj hcc))]
    exact wout_dup hrel hinv hh hm hrun

/-- `instantiate1_go` at `WOutE`: what a caller that interns again uses. -/
theorem instantiate1_go_wout {pers st lst} {v : arena.handle.EIdx}
    {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hv : EResolves lst (absEIdx v)) (hh : EResolves lst (absEIdx h))
    (hmemo : MemoRes Memos.inst1C lst)
    (hrun : arena.expr_ops.instantiate1_go pers st v fuel h d = ok o) :
    WOutE (MemoRes Memos.inst1C) pers st lst o
      (instantiate1Go (absEIdx v) (absU fuel) (absEIdx h) (absU d)) :=
  instantiate1_go_aux _ rfl hrel hinv hfrozen hv hh hmemo hrun

/-- `instantiate1_fast` at `WOutE`: the memo fresh before and dropped after,
so the memo clause is free on the way in and trivially true on the way out. -/
theorem instantiate1_fast_wout {pers st lst} {fuel : Std.U64}
    {e v : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (he : EResolves lst (absEIdx e)) (hv : EResolves lst (absEIdx v))
    (hrun : arena.expr_ops.instantiate1_fast pers st fuel e v d = ok o) :
    WOutE (MemoRes Memos.inst1C) pers st lst o
      (instantiate1Fast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) := by
  rw [arena.expr_ops.instantiate1_fast] at hrun
  obtain ⟨st1, hst1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st2⟩ := q
  have hs1 := inst1_clear_store hst1
  obtain ⟨hc1, hrel1, hinv1⟩ := wmemo_clear_step
    (upd := fun m v => { m with inst1C := v }) (twinClear := Arena.inst1Clear) (fun _ => rfl) (inst1_clear_run hrel hinv hst1)
  have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
    rw [hs1]; exact hfrozen
  have hgo := instantiate1_go_wout (lst := { lst with memos := { lst.memos with
      inst1C := ∅ } }) hrel1 hinv1 hfroz1 hv he (MemoRes.of_empty rfl) hq
  show WOutR _ pers st lst o ((do
    Arena.inst1Clear
    let r ← instantiate1Go (absEIdx v) (absU fuel) (absEIdx e) (absU d)
    Arena.inst1Clear
    pure r).run lst)
  rw [run_bind_of hc1]
  cases hr : r with
  | Err ee =>
    rw [hr] at hrun hgo
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact wout_err_bind (hgo.err rfl)
  | Ok r1 =>
    rw [hr] at hrun hgo
    obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl1, hfl2, -⟩ := hgo.dest
    obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    have hs3 := inst1_clear_store hst3
    obtain ⟨hc3, hrel3, hinv3⟩ := wmemo_clear_step
      (upd := fun m v => { m with inst1C := v }) (twinClear := Arena.inst1Clear) (fun _ => rfl)
      (inst1_clear_run hrel2 hinv2 hst3)
    rw [run_bind_of hx2, run_bind_of hc3]
    exact WOutR.ok rfl hrel3 hinv3 hext2 hres2 hmono2 (by rw [hs3, hfl1, hs1])
      (by rw [hs3, hfl2, hs1]) (MemoRes.of_empty rfl)

/-- `Arena/ExprOps.lean:254 instantiate1Go`.

**Task #97-P5-Mut round 2 corrected the statement** (finding 19): as written
it carried `hrel`/`hinv` and nothing else, and it was FALSE — a memo mapping
`(h, d)` to a handle that decodes nowhere satisfies both, the `app` arm
answers that handle, and the caller's intern breaks `StoreWF`.  What went in
is what the port genuinely needs: `hfrozen` (the tier flag the port's
`intern` tests), that the substituted term and the handle walked resolve, and
the memo clause `MemoRes` — the smallest hypotheses under which it is true,
and exactly what the walk re-establishes one step down. -/
theorem instantiate1_go_refines {pers st lst} {v : arena.handle.EIdx}
    {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hv : EResolves lst (absEIdx v)) (hh : EResolves lst (absEIdx h))
    (hmemo : MemoRes Memos.inst1C lst)
    (hrun : arena.expr_ops.instantiate1_go pers st v fuel h d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiate1Go (absEIdx v) (absU fuel) (absEIdx h) (absU d)) :=
  (instantiate1_go_wout hrel hinv hfrozen hv hh hmemo hrun).toSim

/-- `Arena/ExprOps.lean:324 instantiate1Fast` — the memo fresh before and
dropped after.  **Corrected** as `instantiate1_go_refines` was, minus the memo
clause, which the fresh memo pays for. -/
theorem instantiate1_fast_refines {pers st lst} {fuel : Std.U64}
    {e v : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (he : EResolves lst (absEIdx e)) (hv : EResolves lst (absEIdx v))
    (hrun : arena.expr_ops.instantiate1_fast pers st fuel e v d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiate1Fast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) :=
  (instantiate1_fast_wout hrel hinv hfrozen he hv hrun).toSim

/-! ## `instantiateList` — the bulk substitution, two twins

`Arena/ExprOps.lean`'s own note: TWO twins and not one, because
`instantiateListGo`'s `bvar` arm recurses into the replacement through the
UNMEMOIZED `instantiateList` with a shorter vector.  The accumulator is an
`Array` in push order (task #97-P6-15), read from the end.

`Specs.lean` primitives: `instListCutoff`'s `derivedE`, `instLGet`/`instLSet`/
`instLClear`, the five projections, the five `intern*E`. -/

/-! ### `instantiateList`, the unmemoised bulk walk

It writes no memo, so it preserves ANY side invariant `QStable` covers — which
is what `instantiateListGo`'s `bvar` arm, calling it under its own memo
clause, needs. -/

/-- A `u64` cast to a `usize` keeps its value when it fits
(`Refine/ExprOpsSubst.lean`'s lemma, restated: not imported here). -/
theorem u64_cast_usize_val' {x : Std.U64} {n : Nat} (hn : n ≤ Std.Usize.max)
    (hx : x.val < n) : (Std.UScalar.cast .Usize x : Std.Usize).val = x.val := by
  rw [Std.UScalar.cast_val_eq, Std.UScalarTy.Usize_numBits_eq]
  refine Nat.mod_eq_of_lt ?_
  have hmax : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
    simp only [Std.Usize.max, Std.Usize.numBits, Std.UScalarTy.Usize_numBits_eq]
  have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  omega

/-- Every entry of `lastEidx xs k` is an entry of `xs`. -/
theorem mem_lastEidx {xs : Array EIdx} {k : Nat} {x : EIdx}
    (h : x ∈ (lastEidx xs k).toList) : x ∈ xs.toList := by
  rw [lastEidx, ExprOps.eidxCopyUpto_toList xs xs.size xs.size _ #[] (by omega)] at h
  simp only [List.nil_append, Array.toList_empty] at h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- The `instantiate_list` statement at one fuel value, for any stable side
invariant. -/
def ILAt (n : Nat) : Prop :=
  ∀ {Q : AState → Prop}, QStable Q →
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {vs : alloc.vec.Vec arena.handle.EIdx} {fuel : Std.U64} {h : arena.handle.EIdx}
    {d : Std.U64} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st →
    (st.store.shared_on = true → st.store.scratch_on = true) →
    (∀ x ∈ vs.val, EResolves lst (absEIdx x)) → EResolves lst (absEIdx h) → Q lst →
    arena.expr_ops.instantiate_list pers st vs fuel h d = ok o →
    WOutE Q pers st lst o (instantiateList (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d))

private theorem instantiate_list_aux (n : Nat) : ILAt n := by
  induction n with
  | zero =>
    intro Q hQ pers st lst vs fuel h d o hn hrel hinv hfrozen hvs hh hq hrun
    rw [arena.expr_ops.instantiate_list] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨vv, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hrrv := fail_run hrr
    have ho := Result.ok_injective hrun
    rw [← ho, hrrv]
    show AErrSim _ ((instantiateList (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)).run lst)
    rw [show absU fuel = 0 from hn, instantiateList_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro Q hQ pers st lst vs fuel h d o hn hrel hinv hfrozen hvs hh hq hrun
    rw [arena.expr_ops.instantiate_list] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    have hi1 : ∀ i1 : Std.U64, (fuel - 1#u64 = ok i1) → i1.val = m := by
      intro i1 hi1
      have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
        (ConRon.Refine.Nat.usub_val hi1).2
      rw [h1, hn]; rfl
    show WOutR Q pers st lst o
      ((instantiateList (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)).run lst)
    rw [show absU fuel = m + 1 from hn, instantiateList_succ]
    obtain ⟨bc, hbc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hcut := (ExprOps.inst_list_cutoff_refines hrel hinv hbc).apply
    rw [run_bind_of hcut]
    cases bc with
    | true =>
      rw [if_pos rfl] at hrun
      exact wout_dup hrel hinv hh hq hrun
    | false =>
    rw [if_neg (by simp)] at hrun
    show WOutR Q pers st lst o
      ((if (absEIdx h).tag == ETag.app then instListArmApp (absEIdxArr vs) m (absEIdx h) (absU d)
        else if ETag.isBind (absEIdx h).tag then
          instListArmBind (absEIdxArr vs) m (absEIdx h) (absU d)
        else if (absEIdx h).tag == ETag.letE then
          instListArmLet (absEIdxArr vs) m (absEIdx h) (absU d)
        else if (absEIdx h).tag == ETag.proj then
          instListArmProj (absEIdxArr vs) m (absEIdx h) (absU d)
        else if (absEIdx h).tag == ETag.bvar then
          instListArmBVar (absEIdxArr vs) m (absEIdx h) (absU d)
        else pure (absEIdx h)).run lst)
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htg := eidx_tag_abs ht
    rw [htg]
    by_cases hA : t = arena.handle.ETAG_APP
    · rw [if_pos hA] at hrun
      rw [if_pos (show (absU32 t == ETag.app) = true by rw [hA, etag_app_abs]; simp)]
      have htA : (absEIdx h).tag = ETag.app := by rw [htg, hA, etag_app_abs]
      rw [instListArmApp]
      obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hva := (view_app_run hrel ho1).apply
      rw [run_bind_of hva]
      cases ho1c : o1 with
      | none =>
        rw [ho1c] at hrun
        exact wout_dangling hrun
      | some p =>
        rw [ho1c] at hrun
        obtain ⟨f, a⟩ := p
        have hvap : lst.store.viewApp (absEIdx h) = some (absEIdx f, absEIdx a) := by
          have h2 : (Arena.viewApp (absEIdx h)).run lst
              = .ok (lst.store.viewApp (absEIdx h), lst) := rfl
          rw [h2, ho1c] at hva
          simpa [absPairE] using hva
        have hvA := view_of_viewApp' htA hvap
        have hfR : EResolves lst (absEIdx f) :=
          EResolves.child hrel.storeWF hvA (by simp [ENodeView.echildren])
        have haR : EResolves lst (absEIdx a) :=
          EResolves.child hrel.storeWF hvA (by simp [ENodeView.echildren])
        simp only [Option.map_some, absPairE]
        obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v := hi1 i1 hi1'
        obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, st1⟩ := p1
        have hrec1 := ih hQ hi1v hrel hinv hfrozen hvs hfR hq hp1
        rw [show absU i1 = m from hi1v] at hrec1
        cases hr1 : r1 with
        | Err e =>
          rw [hr1] at hrun hrec1
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact wout_err_bind (hrec1.err rfl)
        | Ok f2 =>
          rw [hr1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
            hrec1.dest
          refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
          have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
            intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
          obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r2, st2⟩ := p2
          have hrec2 := ih hQ hi1v hrel1 hinv1 hfroz1 (fun x hx => hmono1.res (hvs x hx))
            (hmono1.res haR) hq1 hp2
          rw [show absU i1 = m from hi1v] at hrec2
          cases hr2 : r2 with
          | Err e =>
            rw [hr2] at hrun hrec2
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec2.err rfl)
          | Ok a2 =>
            rw [hr2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
              hrec2.dest
            refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
            have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
              intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
            exact intern_e_app_res hQ hrel2 hinv2 hfroz2 hq2
              f2 a2 (viewOK_app (hmono2.res hres1) hres2) hrun
    rw [if_neg hA] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.app) = true) by
      rw [← etag_app_abs]; simp only [beq_iff_eq]; intro hcc; exact hA (absU32_inj hcc))]
    obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hbind := etag_isBind_abs hb1
    cases b1 with
    | true =>
      rw [if_pos rfl] at hrun
      rw [if_pos hbind]
      have hbind' : ETag.isBind (absEIdx h).tag = true := by rw [htg]; exact hbind
      rw [instListArmBind]
      obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hvb := (view_bind_i_run hrel hbind' ho1).apply
      rw [run_bind_of hvb]
      cases ho1c : o1 with
      | none =>
        rw [ho1c] at hrun
        exact wout_dangling hrun
      | some p =>
        rw [ho1c] at hrun
        obtain ⟨ty, body, mi⟩ := p
        have hvbi : lst.store.viewBindI (absEIdx h)
            = some (absEIdx ty, absEIdx body, absBMIdx mi) := by
          have h2 : (Arena.viewBindI (absEIdx h)).run lst
              = .ok (lst.store.viewBindI (absEIdx h), lst) := rfl
          rw [h2, ho1c] at hvb
          simpa [absBindI] using hvb
        obtain ⟨mm, hmv, hm0, htyR, hbR⟩ := viewBindI_facts hrel.storeWF hbind' hvbi
        simp only [Option.map_some, absBindI]
        obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v := hi1 i1 hi1'
        obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, st1⟩ := p1
        have hrec1 := ih hQ hi1v hrel hinv hfrozen hvs htyR hq hp1
        rw [show absU i1 = m from hi1v] at hrec1
        cases hr1 : r1 with
        | Err e =>
          rw [hr1] at hrun hrec1
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact wout_err_bind (hrec1.err rfl)
        | Ok t2 =>
          rw [hr1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
            hrec1.dest
          refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
          have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
            intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
          obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v : absU i2 = absU d + 1 := by
            have h1 := ConRon.Refine.Nat.uadd_val hi2
            simpa using h1
          obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r2, st2⟩ := p2
          have hrec2 := ih hQ hi1v hrel1 hinv1 hfroz1 (fun x hx => hmono1.res (hvs x hx))
            (hmono1.res hbR) hq1 hp2
          rw [show absU i1 = m from hi1v, hi2v] at hrec2
          cases hr2 : r2 with
          | Err e =>
            rw [hr2] at hrun hrec2
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec2.err rfl)
          | Ok b2 =>
            rw [hr2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
              hrec2.dest
            refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
            have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
              intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
            have hstep := intern_e_bind_i_res hQ hrel2 hinv2 hfroz2 hq2
              t hbind t2 b2 mi (hmono2.2.1 _ _ (hmono1.2.1 _ _ hmv)) hm0
              (hmono2.res hres1) hres2 hrun
            rw [← htg] at hstep
            exact hstep
    | false =>
    rw [if_neg (by simp)] at hrun
    rw [if_neg (by rw [hbind]; simp)]
    by_cases hL : t = arena.handle.ETAG_LET_E
    · rw [if_pos hL] at hrun
      rw [if_pos (show (absU32 t == ETag.letE) = true by rw [hL, etag_letE_abs]; simp)]
      have htL : (absEIdx h).tag = ETag.letE := by rw [htg, hL, etag_letE_abs]
      rw [instListArmLet]
      obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hvl := (view_let_run hrel ho1).apply
      rw [run_bind_of hvl]
      cases ho1c : o1 with
      | none =>
        rw [ho1c] at hrun
        exact wout_dangling hrun
      | some p =>
        rw [ho1c] at hrun
        obtain ⟨ty, val, body⟩ := p
        have hvlp : lst.store.viewLet (absEIdx h)
            = some (absEIdx ty, absEIdx val, absEIdx body) := by
          have h2 : (Arena.viewLet (absEIdx h)).run lst
              = .ok (lst.store.viewLet (absEIdx h), lst) := rfl
          rw [h2, ho1c] at hvl
          simpa [absLetT] using hvl
        have hvL := view_of_viewLet' htL hvlp
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvL (by simp [ENodeView.echildren])
        have hvalR : EResolves lst (absEIdx val) :=
          EResolves.child hrel.storeWF hvL (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvL (by simp [ENodeView.echildren])
        simp only [Option.map_some, absLetT]
        obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v := hi1 i1 hi1'
        obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, st1⟩ := p1
        have hrec1 := ih hQ hi1v hrel hinv hfrozen hvs htyR hq hp1
        rw [show absU i1 = m from hi1v] at hrec1
        cases hr1 : r1 with
        | Err e =>
          rw [hr1] at hrun hrec1
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact wout_err_bind (hrec1.err rfl)
        | Ok t2 =>
          rw [hr1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
            hrec1.dest
          refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
          have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
            intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
          obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r2, st2⟩ := p2
          have hrec2 := ih hQ hi1v hrel1 hinv1 hfroz1 (fun x hx => hmono1.res (hvs x hx))
            (hmono1.res hvalR) hq1 hp2
          rw [show absU i1 = m from hi1v] at hrec2
          cases hr2 : r2 with
          | Err e =>
            rw [hr2] at hrun hrec2
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec2.err rfl)
          | Ok w2 =>
            rw [hr2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
              hrec2.dest
            refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
            have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
              intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
            obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hi2v : absU i2 = absU d + 1 := by
              have h1 := ConRon.Refine.Nat.uadd_val hi2
              simpa using h1
            obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r3, st3⟩ := p3
            have hrec3 := ih hQ hi1v hrel2 hinv2 hfroz2
              (fun x hx => hmono2.res (hmono1.res (hvs x hx)))
              (hmono2.res (hmono1.res hbR)) hq2 hp3
            rw [show absU i1 = m from hi1v, hi2v] at hrec3
            cases hr3 : r3 with
            | Err e =>
              rw [hr3] at hrun hrec3
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec3.err rfl)
            | Ok b2 =>
              rw [hr3] at hrun hrec3
              obtain ⟨lst3, hx3, hrel3, hinv3, hext3, hres3, hmono3, hfl5, hfl6, hq3⟩ :=
                hrec3.dest
              refine WOutE.bind hx3 hext3 hmono3 hfl5 hfl6 ?_
              have hfroz3 : st3.store.shared_on = true → st3.store.scratch_on = true := by
                intro hs; rw [hfl6]; exact hfroz2 (hfl5 ▸ hs)
              exact intern_e_let_e_res hQ hrel3 hinv3 hfroz3 hq3
                t2 w2 b2 (viewOK_letE (hmono3.res (hmono2.res hres1))
                  (hmono3.res hres2) hres3) hrun
    rw [if_neg hL] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.letE) = true) by
      rw [← etag_letE_abs]; simp only [beq_iff_eq]; intro hcc; exact hL (absU32_inj hcc))]
    by_cases hP : t = arena.handle.ETAG_PROJ
    · rw [if_pos hP] at hrun
      rw [if_pos (show (absU32 t == ETag.proj) = true by rw [hP, etag_proj_abs]; simp)]
      have htP : (absEIdx h).tag = ETag.proj := by rw [htg, hP, etag_proj_abs]
      rw [instListArmProj]
      obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hvp := (view_proj_run hrel ho1).apply
      rw [run_bind_of hvp]
      cases ho1c : o1 with
      | none =>
        rw [ho1c] at hrun
        exact wout_dangling hrun
      | some p =>
        rw [ho1c] at hrun
        obtain ⟨nn, i1, sub⟩ := p
        have hvpp : lst.store.viewProj (absEIdx h)
            = some (absNIdx nn, absU i1, absEIdx sub) := by
          have h2 : (Arena.viewProj (absEIdx h)).run lst
              = .ok (lst.store.viewProj (absEIdx h), lst) := rfl
          rw [h2, ho1c] at hvp
          simpa [absProjT] using hvp
        have hvP := view_of_viewProj' htP hvpp
        have hsR : EResolves lst (absEIdx sub) :=
          EResolves.child hrel.storeWF hvP (by simp [ENodeView.echildren])
        have hnR : (lst.store.ns.view (absNIdx nn)).isSome = true := by
          obtain ⟨rk, hw⟩ := hrel.storeWF
          exact (hw.nchildOK _ _ hvP _ (by simp [ENodeView.nchildren])).1
        simp only [Option.map_some, absProjT]
        obtain ⟨i2, hi2', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v := hi1 i2 hi2'
        obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, st1⟩ := p1
        have hrec1 := ih hQ hi2v hrel hinv hfrozen hvs hsR hq hp1
        rw [show absU i2 = m from hi2v] at hrec1
        cases hr1 : r1 with
        | Err e =>
          rw [hr1] at hrun hrec1
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact wout_err_bind (hrec1.err rfl)
        | Ok u =>
          rw [hr1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
            hrec1.dest
          refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
          have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
            intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
          exact intern_e_proj_res hQ hrel1 hinv1 hfroz1 hq1
            nn i1 u (viewOK_proj (hmono1.nsres hnR) hres1) hrun
    rw [if_neg hP] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.proj) = true) by
      rw [← etag_proj_abs]; simp only [beq_iff_eq]; intro hcc; exact hP (absU32_inj hcc))]
    by_cases hBV : t = arena.handle.ETAG_BVAR
    · rw [if_pos hBV] at hrun
      rw [if_pos (show (absU32 t == ETag.bvar) = true by rw [hBV, etag_bvar_abs]; simp)]
      rw [instListArmBVar]
      obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hvb := (view_bvar_run hrel ho1).apply
      rw [run_bind_of hvb]
      cases ho1c : o1 with
      | none =>
        rw [ho1c] at hrun
        exact wout_dangling hrun
      | some j =>
        rw [ho1c] at hrun
        simp only at hrun
        simp only [Option.map_some]
        by_cases hjd : j < d
        · rw [if_pos hjd] at hrun
          rw [if_pos (show absU j < absU d by scalar_tac)]
          exact wout_dup hrel hinv hh hq hrun
        rw [if_neg hjd] at hrun
        rw [if_neg (show ¬ (absU j < absU d) by scalar_tac)]
        obtain ⟨nn, hnn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hnnv : nn.val = vs.val.length := by
          simp only [lift, Result.ok.injEq] at hnn
          rw [← hnn, usize_cast_u64_val']; rfl
        obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = j.val - d.val := (ConRon.Refine.Nat.usub_val hi1').2
        by_cases hlt : i1 < nn
        · rw [if_pos hlt] at hrun
          have hlt' : absU j - absU d < (absEIdxArr vs).size := by
            rw [absEIdxArr_size]; scalar_tac
          rw [dif_pos hlt']
          obtain ⟨i2, hi2', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v : i2.val = i1.val := by
            simp only [lift, Result.ok.injEq] at hi2'
            rw [← hi2']
            exact u64_cast_usize_val' (n := vs.val.length) (by scalar_tac) (by scalar_tac)
          obtain ⟨i4, hi4', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi4v : i4.val = vs.val.length - 1 := by
            have := (ConRon.Refine.Nat.usub_val hi4').2; simpa using this
          obtain ⟨i5, hi5', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi5v : i5.val = i4.val - i2.val := (ConRon.Refine.Nat.usub_val hi5').2
          obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨hb5, hval5⟩ := ExprOps.vecIndexAt he
          obtain ⟨vi, hvi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hvie : vi = e := dupId_eidx e vi hvi
          have hidx : (absEIdxArr vs).size - 1 - (absU j - absU d) = i5.val := by
            rw [absEIdxArr_size, hi5v, hi4v, hi2v, hi1v]
          have hget : (absEIdxArr vs)[(absEIdxArr vs).size - 1 - (absU j - absU d)]'
              (by omega) = absEIdx vi := by
            simp only [hidx]
            rw [absEIdxArr_get vs i5.val hb5, hval5, hvie]
          have hviR : EResolves lst (absEIdx vi) := by
            rw [hvie, ← hval5]; exact hvs _ (List.getElem_mem hb5)
          simp only [hget]
          obtain ⟨b2, hb2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hcut2 := (ExprOps.inst_list_cutoff_refines hrel hinv hb2).apply
          rw [run_bind_of hcut2]
          cases b2 with
          | true =>
            rw [if_pos rfl] at hrun
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact WOutR.pure hrel hinv hviR hq
          | false =>
            rw [if_neg (by simp)] at hrun
            rw [if_neg (by simp)]
            obtain ⟨pre, hpre, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨i6, hi6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hl := ExprOps.last_eidx_refines hpre
            have harr : lastEidx (absEIdxArr vs) (absU j - absU d) = absEIdxArr pre := by
              apply Array.toList_inj.mp
              rw [show absU j - absU d = i2.val by rw [hi2v, hi1v]]
              simpa [absEIdxArr, ExprOps.absEIdxArr, ExprOps.absEIdxL] using hl
            have hpreR : ∀ x ∈ pre.val, EResolves lst (absEIdx x) := by
              intro x hx
              have hx1 : absEIdx x ∈ (lastEidx (absEIdxArr vs) (absU j - absU d)).toList := by
                rw [harr]; simp only [absEIdxArr, List.toList_toArray]
                exact List.mem_map_of_mem hx
              have hx2 := mem_lastEidx hx1
              simp only [absEIdxArr, List.toList_toArray, List.mem_map] at hx2
              obtain ⟨y, hy, hyx⟩ := hx2
              rw [← hyx]; exact hvs y hy
            have hrec := ih hQ (hi1 i6 hi6) hrel hinv hfrozen hpreR hviR hq hrun
            rw [show absU i6 = m from hi1 i6 hi6] at hrec
            rw [harr]
            exact hrec
        · rw [if_neg hlt] at hrun
          have hlt' : ¬ (absU j - absU d < (absEIdxArr vs).size) := by
            rw [absEIdxArr_size]; scalar_tac
          rw [dif_neg hlt']
          obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v : absU i2 = absU j - (absEIdxArr vs).size := by
            rw [absEIdxArr_size, ← hnnv]; exact (ConRon.Refine.Nat.usub_val hi2).2
          rw [← hi2v]
          exact intern_e_bvar_res hQ hrel hinv hfrozen hq i2 hrun
    rw [if_neg hBV] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.bvar) = true) by
      rw [← etag_bvar_abs]; simp only [beq_iff_eq]; intro hcc; exact hBV (absU32_inj hcc))]
    exact wout_dup hrel hinv hh hq hrun

/-- `Arena/ExprOps.lean:346 instantiateList` — the UNMEMOIZED bulk walk.
**Corrected** (task #97-P5-Mut round 2, finding 19): `hfrozen`, and that the
handle walked and every entry of the substitution resolve — the `bvar` arm
answers an entry, or walks into it. -/
theorem instantiate_list_refines {pers st lst} {vs : alloc.vec.Vec arena.handle.EIdx}
    {fuel : Std.U64} {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hvs : ∀ x ∈ vs.val, EResolves lst (absEIdx x)) (hh : EResolves lst (absEIdx h))
    (hrun : arena.expr_ops.instantiate_list pers st vs fuel h d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiateList (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)) :=
  (instantiate_list_aux _ QStable.true rfl hrel hinv hfrozen hvs hh trivial hrun).toSim

/-- The `instantiate_list_go` statement at one fuel value, with the memo
clause at `instLC` as its side invariant. -/
def ILGoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {vs : alloc.vec.Vec arena.handle.EIdx} {fuel : Std.U64} {h : arena.handle.EIdx}
    {d : Std.U64} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st →
    (st.store.shared_on = true → st.store.scratch_on = true) →
    (∀ x ∈ vs.val, EResolves lst (absEIdx x)) → EResolves lst (absEIdx h) →
    MemoRes Memos.instLC lst →
    arena.expr_ops.instantiate_list_go pers st vs fuel h d = ok o →
    WOutE (MemoRes Memos.instLC) pers st lst o
      (instantiateListGo (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d))

private theorem instantiate_list_go_aux (n : Nat) : ILGoAt n := by
  induction n with
  | zero =>
    intro pers st lst vs fuel h d o hn hrel hinv hfrozen hvs hh hm hrun
    rw [arena.expr_ops.instantiate_list_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨vv, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hrrv := fail_run hrr
    have ho := Result.ok_injective hrun
    rw [← ho, hrrv]
    show AErrSim _ ((instantiateListGo (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)).run lst)
    rw [show absU fuel = 0 from hn, instantiateListGo_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst vs fuel h d o hn hrel hinv hfrozen hvs hh hm hrun
    rw [arena.expr_ops.instantiate_list_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    have hi1 : ∀ i1 : Std.U64, (fuel - 1#u64 = ok i1) → i1.val = m := by
      intro i1 hi1
      have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
        (ConRon.Refine.Nat.usub_val hi1).2
      rw [h1, hn]; rfl
    show WOutR (MemoRes Memos.instLC) pers st lst o
      ((instantiateListGo (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)).run lst)
    rw [show absU fuel = m + 1 from hn, instantiateListGo_succ]
    obtain ⟨bc, hbc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hcut := (ExprOps.inst_list_cutoff_refines hrel hinv hbc).apply
    rw [run_bind_of hcut]
    cases bc with
    | true =>
      rw [if_pos rfl] at hrun
      exact wout_dup hrel hinv hh hm hrun
    | false =>
    rw [if_neg (by simp)] at hrun
    show WOutR (MemoRes Memos.instLC) pers st lst o
      ((if (absEIdx h).tag == ETag.app then
          instListGoArmApp (absEIdxArr vs) m (absEIdx h) (absU d)
        else if ETag.isBind (absEIdx h).tag then
          instListGoArmBind (absEIdxArr vs) m (absEIdx h) (absU d)
        else if (absEIdx h).tag == ETag.letE then
          instListGoArmLet (absEIdxArr vs) m (absEIdx h) (absU d)
        else if (absEIdx h).tag == ETag.proj then
          instListGoArmProj (absEIdxArr vs) m (absEIdx h) (absU d)
        else if (absEIdx h).tag == ETag.bvar then
          instantiateList (absEIdxArr vs) m (absEIdx h) (absU d)
        else pure (absEIdx h)).run lst)
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htg := eidx_tag_abs ht
    rw [htg]
    by_cases hA : t = arena.handle.ETAG_APP
    · rw [if_pos hA] at hrun
      rw [if_pos (show (absU32 t == ETag.app) = true by rw [hA, etag_app_abs]; simp)]
      have htA : (absEIdx h).tag = ETag.app := by rw [htg, hA, etag_app_abs]
      rw [instListGoArmApp]
      obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hkabs := eidx_nat_key_abs hk
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hget := (inst_l_get_run hrel hinv hop).apply
      have hgv := inst_l_get_val hrel hinv hop
      rw [hkabs] at hget hgv
      rw [run_bind_of hget]
      cases hopc : op with
      | some r =>
        rw [hopc] at hrun hgv
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact WOutR.pure hrel hinv (hm _ _ hgv) hm
      | none =>
        rw [hopc] at hrun
        simp only [Option.map_none]
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hva := (view_app_run hrel ho1).apply
        rw [run_bind_of hva]
        cases ho1c : o1 with
        | none =>
          rw [ho1c] at hrun
          exact wout_dangling hrun
        | some p =>
          rw [ho1c] at hrun
          obtain ⟨f, a⟩ := p
          have hvap : lst.store.viewApp (absEIdx h) = some (absEIdx f, absEIdx a) := by
            have h2 : (Arena.viewApp (absEIdx h)).run lst
                = .ok (lst.store.viewApp (absEIdx h), lst) := rfl
            rw [h2, ho1c] at hva
            simpa [absPairE] using hva
          have hvA := view_of_viewApp' htA hvap
          have hfR : EResolves lst (absEIdx f) :=
            EResolves.child hrel.storeWF hvA (by simp [ENodeView.echildren])
          have haR : EResolves lst (absEIdx a) :=
            EResolves.child hrel.storeWF hvA (by simp [ENodeView.echildren])
          simp only [Option.map_some, absPairE]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen hvs hfR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok f2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (fun x hx => hmono1.res (hvs x hx)) (hmono1.res haR) hq1 hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok a2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep := intern_e_app_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                f2 a2 (viewOK_app (hmono2.res hres1) hres2) hp3
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok r4 =>
                rw [hr3] at hrun hstep
                obtain ⟨st4, hst4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_inst_l_set hstep hst4
                rw [hkabs] at hset
                exact hset
    rw [if_neg hA] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.app) = true) by
      rw [← etag_app_abs]; simp only [beq_iff_eq]; intro hcc; exact hA (absU32_inj hcc))]
    obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hbind := etag_isBind_abs hb1
    cases b1 with
    | true =>
      rw [if_pos rfl] at hrun
      rw [if_pos hbind]
      have hbind' : ETag.isBind (absEIdx h).tag = true := by rw [htg]; exact hbind
      rw [instListGoArmBind]
      obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hkabs := eidx_nat_key_abs hk
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hget := (inst_l_get_run hrel hinv hop).apply
      have hgv := inst_l_get_val hrel hinv hop
      rw [hkabs] at hget hgv
      rw [run_bind_of hget]
      cases hopc : op with
      | some r =>
        rw [hopc] at hrun hgv
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact WOutR.pure hrel hinv (hm _ _ hgv) hm
      | none =>
        rw [hopc] at hrun
        simp only [Option.map_none]
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hvb := (view_bind_i_run hrel hbind' ho1).apply
        rw [run_bind_of hvb]
        cases ho1c : o1 with
        | none =>
          rw [ho1c] at hrun
          exact wout_dangling hrun
        | some p =>
          rw [ho1c] at hrun
          obtain ⟨ty, body, mi⟩ := p
          have hvbi : lst.store.viewBindI (absEIdx h)
              = some (absEIdx ty, absEIdx body, absBMIdx mi) := by
            have h2 : (Arena.viewBindI (absEIdx h)).run lst
                = .ok (lst.store.viewBindI (absEIdx h), lst) := rfl
            rw [h2, ho1c] at hvb
            simpa [absBindI] using hvb
          obtain ⟨mm, hmv, hm0, htyR, hbR⟩ := viewBindI_facts hrel.storeWF hbind' hvbi
          simp only [Option.map_some, absBindI]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen hvs htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hi2v : absU i2 = absU d + 1 := by
              have h1 := ConRon.Refine.Nat.uadd_val hi2
              simpa using h1
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (fun x hx => hmono1.res (hvs x hx)) (hmono1.res hbR) hq1 hp2
            rw [show absU i1 = m from hi1v, hi2v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok b2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep := intern_e_bind_i_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                t hbind t2 b2 mi (hmono2.2.1 _ _ (hmono1.2.1 _ _ hmv)) hm0
                (hmono2.res hres1) hres2 hp3
              rw [← htg] at hstep
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok r4 =>
                rw [hr3] at hrun hstep
                obtain ⟨st4, hst4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_inst_l_set hstep hst4
                rw [hkabs] at hset
                exact hset
    | false =>
    rw [if_neg (by simp)] at hrun
    rw [if_neg (by rw [hbind]; simp)]
    by_cases hBV : t = arena.handle.ETAG_BVAR
    · rw [if_pos hBV] at hrun
      rw [if_neg (show ¬ ((absU32 t == ETag.letE) = true) by
        rw [hBV, etag_bvar_abs]; decide)]
      rw [if_neg (show ¬ ((absU32 t == ETag.proj) = true) by
        rw [hBV, etag_bvar_abs]; decide)]
      rw [if_pos (show (absU32 t == ETag.bvar) = true by rw [hBV, etag_bvar_abs]; simp)]
      obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrec := instantiate_list_aux m (MemoRes.stable _) (hi1 i1 hi1') hrel hinv hfrozen
        hvs hh hm hrun
      rw [show absU i1 = m from hi1 i1 hi1'] at hrec
      exact hrec
    rw [if_neg hBV] at hrun
    by_cases hL : t = arena.handle.ETAG_LET_E
    · rw [if_pos hL] at hrun
      rw [if_pos (show (absU32 t == ETag.letE) = true by rw [hL, etag_letE_abs]; simp)]
      have htL : (absEIdx h).tag = ETag.letE := by rw [htg, hL, etag_letE_abs]
      rw [instListGoArmLet]
      obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hkabs := eidx_nat_key_abs hk
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hget := (inst_l_get_run hrel hinv hop).apply
      have hgv := inst_l_get_val hrel hinv hop
      rw [hkabs] at hget hgv
      rw [run_bind_of hget]
      cases hopc : op with
      | some r =>
        rw [hopc] at hrun hgv
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact WOutR.pure hrel hinv (hm _ _ hgv) hm
      | none =>
        rw [hopc] at hrun
        simp only [Option.map_none]
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hvl := (view_let_run hrel ho1).apply
        rw [run_bind_of hvl]
        cases ho1c : o1 with
        | none =>
          rw [ho1c] at hrun
          exact wout_dangling hrun
        | some p =>
          rw [ho1c] at hrun
          obtain ⟨ty, val, body⟩ := p
          have hvlp : lst.store.viewLet (absEIdx h)
              = some (absEIdx ty, absEIdx val, absEIdx body) := by
            have h2 : (Arena.viewLet (absEIdx h)).run lst
                = .ok (lst.store.viewLet (absEIdx h), lst) := rfl
            rw [h2, ho1c] at hvl
            simpa [absLetT] using hvl
          have hvL := view_of_viewLet' htL hvlp
          have htyR : EResolves lst (absEIdx ty) :=
            EResolves.child hrel.storeWF hvL (by simp [ENodeView.echildren])
          have hvalR : EResolves lst (absEIdx val) :=
            EResolves.child hrel.storeWF hvL (by simp [ENodeView.echildren])
          have hbR : EResolves lst (absEIdx body) :=
            EResolves.child hrel.storeWF hvL (by simp [ENodeView.echildren])
          simp only [Option.map_some, absLetT]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen hvs htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (fun x hx => hmono1.res (hvs x hx)) (hmono1.res hvalR)
              hq1 hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok w2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have hi2v : absU i2 = absU d + 1 := by
                have h1 := ConRon.Refine.Nat.uadd_val hi2
                simpa using h1
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hrec3 := ih hi1v hrel2 hinv2 hfroz2 (fun x hx => hmono2.res (hmono1.res (hvs x hx)))
                (hmono2.res (hmono1.res hbR)) hq2 hp3
              rw [show absU i1 = m from hi1v, hi2v] at hrec3
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hrec3
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hrec3.err rfl)
              | Ok b2 =>
                rw [hr3] at hrun hrec3
                obtain ⟨lst3, hx3, hrel3, hinv3, hext3, hres3, hmono3, hfl5, hfl6, hq3⟩ :=
                  hrec3.dest
                refine WOutE.bind hx3 hext3 hmono3 hfl5 hfl6 ?_
                have hfroz3 : st3.store.shared_on = true → st3.store.scratch_on = true := by
                  intro hs; rw [hfl6]; exact hfroz2 (hfl5 ▸ hs)
                obtain ⟨p4, hp4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                obtain ⟨r4, st4⟩ := p4
                have hstep := intern_e_let_e_res (MemoRes.stable _) hrel3 hinv3 hfroz3 hq3
                  t2 w2 b2 (viewOK_letE (hmono3.res (hmono2.res hres1))
                    (hmono3.res hres2) hres3) hp4
                cases hr4 : r4 with
                | Err e =>
                  rw [hr4] at hrun hstep
                  have ho := Result.ok_injective hrun
                  rw [← ho]
                  exact wout_err_bind (hstep.err rfl)
                | Ok r5 =>
                  rw [hr4] at hrun hstep
                  obtain ⟨st5, hst5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                  have ho := Result.ok_injective hrun
                  rw [← ho]
                  have hset := wout_inst_l_set hstep hst5
                  rw [hkabs] at hset
                  exact hset
    rw [if_neg hL] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.letE) = true) by
      rw [← etag_letE_abs]; simp only [beq_iff_eq]; intro hcc; exact hL (absU32_inj hcc))]
    by_cases hP : t = arena.handle.ETAG_PROJ
    · rw [if_pos hP] at hrun
      rw [if_pos (show (absU32 t == ETag.proj) = true by rw [hP, etag_proj_abs]; simp)]
      have htP : (absEIdx h).tag = ETag.proj := by rw [htg, hP, etag_proj_abs]
      rw [instListGoArmProj]
      obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hkabs := eidx_nat_key_abs hk
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hget := (inst_l_get_run hrel hinv hop).apply
      have hgv := inst_l_get_val hrel hinv hop
      rw [hkabs] at hget hgv
      rw [run_bind_of hget]
      cases hopc : op with
      | some r =>
        rw [hopc] at hrun hgv
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact WOutR.pure hrel hinv (hm _ _ hgv) hm
      | none =>
        rw [hopc] at hrun
        simp only [Option.map_none]
        obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hvp := (view_proj_run hrel ho1).apply
        rw [run_bind_of hvp]
        cases ho1c : o1 with
        | none =>
          rw [ho1c] at hrun
          exact wout_dangling hrun
        | some p =>
          rw [ho1c] at hrun
          obtain ⟨n, i1, sub⟩ := p
          have hvpp : lst.store.viewProj (absEIdx h)
              = some (absNIdx n, absU i1, absEIdx sub) := by
            have h2 : (Arena.viewProj (absEIdx h)).run lst
                = .ok (lst.store.viewProj (absEIdx h), lst) := rfl
            rw [h2, ho1c] at hvp
            simpa [absProjT] using hvp
          have hvP := view_of_viewProj' htP hvpp
          have hsR : EResolves lst (absEIdx sub) :=
            EResolves.child hrel.storeWF hvP (by simp [ENodeView.echildren])
          have hnR : (lst.store.ns.view (absNIdx n)).isSome = true := by
            obtain ⟨rk, hw⟩ := hrel.storeWF
            exact (hw.nchildOK _ _ hvP _ (by simp [ENodeView.nchildren])).1
          simp only [Option.map_some, absProjT]
          obtain ⟨i2, hi2', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v := hi1 i2 hi2'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi2v hrel hinv hfrozen hvs hsR hm hp1
          rw [show absU i2 = m from hi2v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok u =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hstep := intern_e_proj_res (MemoRes.stable _) hrel1 hinv1 hfroz1 hq1
              n i1 u (viewOK_proj (hmono1.nsres hnR) hres1) hp2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hstep
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hstep.err rfl)
            | Ok r3 =>
              rw [hr2] at hrun hstep
              obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have ho := Result.ok_injective hrun
              rw [← ho]
              have hset := wout_inst_l_set hstep hst3
              rw [hkabs] at hset
              exact hset
    rw [if_neg hP] at hrun
    rw [if_neg (show ¬ ((absU32 t == ETag.proj) = true) by
      rw [← etag_proj_abs]; simp only [beq_iff_eq]; intro hcc; exact hP (absU32_inj hcc))]
    rw [if_neg (show ¬ ((absU32 t == ETag.bvar) = true) by
      rw [← etag_bvar_abs]; simp only [beq_iff_eq]; intro hcc; exact hBV (absU32_inj hcc))]
    exact wout_dup hrel hinv hh hm hrun

/-- `instantiate_list_go` at `WOutE`. -/
theorem instantiate_list_go_wout {pers st lst}
    {vs : alloc.vec.Vec arena.handle.EIdx} {fuel : Std.U64}
    {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hvs : ∀ x ∈ vs.val, EResolves lst (absEIdx x)) (hh : EResolves lst (absEIdx h))
    (hmemo : MemoRes Memos.instLC lst)
    (hrun : arena.expr_ops.instantiate_list_go pers st vs fuel h d = ok o) :
    WOutE (MemoRes Memos.instLC) pers st lst o
      (instantiateListGo (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)) :=
  instantiate_list_go_aux _ rfl hrel hinv hfrozen hvs hh hmemo hrun

/-- `instantiate_list_fast` at `WOutE`: the memo fresh before and dropped after. -/
theorem instantiate_list_fast_wout {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {vs : alloc.vec.Vec arena.handle.EIdx}
    {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (he : EResolves lst (absEIdx e)) (hvs : ∀ x ∈ vs.val, EResolves lst (absEIdx x))
    (hrun : arena.expr_ops.instantiate_list_fast pers st fuel e vs d = ok o) :
    WOutE (MemoRes Memos.instLC) pers st lst o
      (instantiateListFast (absU fuel) (absEIdx e) (absEIdxArr vs) (absU d)) := by
  rw [arena.expr_ops.instantiate_list_fast] at hrun
  obtain ⟨st1, hst1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st2⟩ := q
  have hs1 := inst_l_clear_store hst1
  obtain ⟨hc1, hrel1, hinv1⟩ := wmemo_clear_step
    (upd := fun m v => { m with instLC := v }) (twinClear := Arena.instLClear)
    (fun _ => rfl) (inst_l_clear_run hrel hinv hst1)
  have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
    rw [hs1]; exact hfrozen
  have hgo := instantiate_list_go_wout (lst := { lst with memos := { lst.memos with
      instLC := ∅ } }) hrel1 hinv1 hfroz1 hvs he (MemoRes.of_empty rfl) hq
  show WOutR _ pers st lst o ((do
    Arena.instLClear
    let r ← instantiateListGo (absEIdxArr vs) (absU fuel) (absEIdx e) (absU d)
    Arena.instLClear
    pure r).run lst)
  rw [run_bind_of hc1]
  cases hr : r with
  | Err ee =>
    rw [hr] at hrun hgo
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact wout_err_bind (hgo.err rfl)
  | Ok r1 =>
    rw [hr] at hrun hgo
    obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl1, hfl2, -⟩ := hgo.dest
    obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    have hs3 := inst_l_clear_store hst3
    obtain ⟨hc3, hrel3, hinv3⟩ := wmemo_clear_step
      (upd := fun m v => { m with instLC := v }) (twinClear := Arena.instLClear)
      (fun _ => rfl) (inst_l_clear_run hrel2 hinv2 hst3)
    rw [run_bind_of hx2, run_bind_of hc3]
    exact WOutR.ok rfl hrel3 hinv3 hext2 hres2 hmono2 (by rw [hs3, hfl1, hs1])
      (by rw [hs3, hfl2, hs1]) (MemoRes.of_empty rfl)

/-- `Arena/ExprOps.lean:412 instantiateListGo` — the memoised one. -/
theorem instantiate_list_go_refines {pers st lst}
    {vs : alloc.vec.Vec arena.handle.EIdx} {fuel : Std.U64}
    {h : arena.handle.EIdx} {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hvs : ∀ x ∈ vs.val, EResolves lst (absEIdx x)) (hh : EResolves lst (absEIdx h))
    (hmemo : MemoRes Memos.instLC lst)
    (hrun : arena.expr_ops.instantiate_list_go pers st vs fuel h d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiateListGo (absEIdxArr vs) (absU fuel) (absEIdx h) (absU d)) :=
  (instantiate_list_go_wout hrel hinv hfrozen hvs hh hmemo hrun).toSim

/-- `Arena/ExprOps.lean:474 instantiateListFast`. -/
theorem instantiate_list_fast_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {vs : alloc.vec.Vec arena.handle.EIdx}
    {d : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (he : EResolves lst (absEIdx e)) (hvs : ∀ x ∈ vs.val, EResolves lst (absEIdx x))
    (hrun : arena.expr_ops.instantiate_list_fast pers st fuel e vs d = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (instantiateListFast (absU fuel) (absEIdx e) (absEIdxArr vs) (absU d)) :=
  (instantiate_list_fast_wout hrel hinv hfrozen he hvs hrun).toSim

/-! ## `liftLooseBVars`, `resetMeta`, `abstract1`, `abstractRange`,
`lowerBVars`, `instantiate1Lift` — the five remaining memoised walks

Same shape as `instantiate1Go`, same `Specs.lean` primitives with the walk's
own memo triple (`liftGet`/`liftSet`/`liftClear`, `resetGet`/…, `abs1Get`/…,
`lowerGet`/…, `inst1LGet`/…).  `abstractRange` is the SPEC descent task
#97-P6-11 kept as the statement subject beside the executed
`abstractRangeGo`. -/

/-! ### `liftLooseBVars`' memo -/

theorem lift_get_val {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.monad.EIdxNat} {op : Option arena.handle.EIdx}
    (hop : arena.monad.lift_get st k = ok op) :
    lst.memos.liftC[absEIdxNat k]? = op.map absEIdx :=
  memo_get_val (sel := Memos.liftC) (fun _ _ => rfl) (lift_get_run hrel hinv hop)

theorem lift_set_store {st st' : arena.monad.AState} {k r}
    (h : arena.monad.lift_set st k r = ok st') : st'.store = st.store := by
  rw [arena.monad.lift_set] at h
  obtain ⟨e, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

theorem wout_lift_set {pers : arena.store.PersTier} {st st3 st4 : arena.monad.AState}
    {lst : AState} {x : AM EIdx} {k : arena.monad.EIdxNat} {r3 : arena.handle.EIdx}
    (hstep : WOutE (MemoRes Memos.liftC) pers st lst (.Ok r3, st3) x)
    (hset : arena.monad.lift_set st3 k r3 = ok st4) :
    WOutE (MemoRes Memos.liftC) pers st lst (.Ok r3, st4)
      (do let r ← x; Arena.liftSet (absEIdxNat k) r; pure r) :=
  wout_memo_set (upd := fun m v => { m with liftC := v }) (fun _ _ => rfl)
    (fun _ _ _ => rfl) hstep (lift_set_store hset)
    (fun _ hr hi => lift_set_run hr hi hset)

theorem lift_clear_store {st st' : arena.monad.AState}
    (h : arena.monad.lift_clear st = ok st') : st'.store = st.store := by
  rw [arena.monad.lift_clear] at h
  obtain ⟨hm0, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

/-- The twin's `view` run, read back as the store's. -/
theorem store_view_of_run {lst lst' : AState} {hh : EIdx} {v : ENodeView}
    (h : (Arena.view hh).run lst = .ok (v, lst')) : lst.store.view hh = some v := by
  rw [show (Arena.view hh).run lst
      = (match lst.store.view hh with
         | some w => Except.ok (w, lst)
         | none => Except.error (Arena.CheckError.internal
             "arena: dangling expression handle")) by
    show ((match lst.store.view hh with
            | some w => (pure w : AM ENodeView)
            | none => Arena.fail
                (.internal "arena: dangling expression handle")).run lst) = _
    cases lst.store.view hh <;> rfl] at h
  split at h
  · rename_i w hw
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [hw, h.1]
  · simp at h

/-- The derived cutoff, as the port computes it (`inst_list_cutoff`) against
the twin's inline `bvarB < satRange && bvarB ≤ c`. -/
theorem cutoff_val {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.EIdx} {c : Std.U64} {b : Bool}
    (hb : arena.expr_ops.inst_list_cutoff pers st h c = ok b) :
    ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat < ConLeche.satRange &&
      (ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat ≤ absU c) = b := by
  have h1 := (ExprOps.inst_list_cutoff_refines hrel hinv hb).apply
  have h2 : (instListCutoff (absEIdx h) (absU c)).run lst
      = .ok ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat
          < ConLeche.satRange &&
        (ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat ≤ absU c, lst) := rfl
  rw [h2] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  exact h1.1

/-! ### `liftLooseBVarsGo` -/

def LiftGoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {amount fuel : Std.U64} {h : arena.handle.EIdx} {c : Std.U64} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st →
    (st.store.shared_on = true → st.store.scratch_on = true) →
    EResolves lst (absEIdx h) → MemoRes Memos.liftC lst →
    arena.expr_ops.lift_loose_bvars_go pers st amount fuel h c = ok o →
    WOutE (MemoRes Memos.liftC) pers st lst o
      (liftLooseBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c))

private theorem lift_loose_bvars_go_aux (n : Nat) : LiftGoAt n := by
  induction n with
  | zero =>
    intro pers st lst amount fuel h c o hn hrel hinv hfrozen hh hm hrun
    rw [arena.expr_ops.lift_loose_bvars_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨vv, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hrrv := fail_run hrr
    have ho := Result.ok_injective hrun
    rw [← ho, hrrv]
    show AErrSim _ ((liftLooseBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)).run lst)
    rw [show absU fuel = 0 from hn, liftLooseBVarsGo_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst amount fuel h c o hn hrel hinv hfrozen hh hm hrun
    rw [arena.expr_ops.lift_loose_bvars_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    have hi1 : ∀ i1 : Std.U64, (fuel - 1#u64 = ok i1) → i1.val = m := by
      intro i1 hi1
      have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
        (ConRon.Refine.Nat.usub_val hi1).2
      rw [h1, hn]; rfl
    show WOutR (MemoRes Memos.liftC) pers st lst o
      ((liftLooseBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)).run lst)
    rw [show absU fuel = m + 1 from hn, liftLooseBVarsGo_succ, StateT.run_bind,
      show (derivedE (absEIdx h)).run lst
        = .ok (lst.store.derived (absEIdx h), lst) from rfl]
    obtain ⟨bc, hbc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hcv := cutoff_val hrel hinv hbc
    show WOutR (MemoRes Memos.liftC) pers st lst o
      (((if ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat
            < ConLeche.satRange &&
          (ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat ≤ absU c) = true
        then pure (absEIdx h)
        else do
          match ← Arena.view (absEIdx h) with
          | .bvar i =>
            (if i ≥ absU c then internE (.bvar (i + absU amount)) else pure (absEIdx h))
          | .fvar _ _ => pure (absEIdx h)
          | .sort _ => pure (absEIdx h)
          | .const _ _ => pure (absEIdx h)
          | .lit _ => pure (absEIdx h)
          | .app a b => liftArmApp (absU amount) m (absEIdx h) (absU c) a b
          | .lam ty body mm => liftArmLam (absU amount) m (absEIdx h) (absU c) ty body mm
          | .forallE ty body mm =>
            liftArmForallE (absU amount) m (absEIdx h) (absU c) ty body mm
          | .letE ty val body =>
            liftArmLet (absU amount) m (absEIdx h) (absU c) ty val body
          | .proj nn i sub => liftArmProj (absU amount) m (absEIdx h) (absU c) nn i sub)
          : AM EIdx).run lst)
    rw [hcv]
    cases bc with
    | true =>
      rw [if_pos rfl] at hrun
      rw [if_pos rfl]
      exact wout_dup hrel hinv hh hm hrun
    | false =>
    rw [if_neg (by simp)] at hrun
    rw [if_neg (by simp)]
    obtain ⟨rv, hrv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hview := view_run hrel hinv hrv
    cases hrvc : rv with
    | Err e =>
      rw [hrvc] at hrun hview
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact wout_err_bind hview
    | Ok ev =>
      rw [hrvc] at hrun hview hrv
      obtain ⟨lst0, hx, -, -, -, -⟩ := hview
      have hlst : lst0 = lst := view_run_state hx
      rw [hlst] at hx
      have hvv := store_view_of_run hx
      rw [run_bind_of hx]
      cases ev with
      | BVar i =>
        simp only [absENodeView]
        simp only at hrun
        by_cases hge : i ≥ c
        · rw [if_pos hge] at hrun
          rw [if_pos (show absU i ≥ absU c by scalar_tac)]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v : absU i1 = absU i + absU amount := by
            have := ConRon.Refine.Nat.uadd_val hi1'; simpa using this
          rw [← hi1v]
          exact intern_e_bvar_res (MemoRes.stable _) hrel hinv hfrozen hm i1 hrun
        · rw [if_neg hge] at hrun
          rw [if_neg (show ¬ (absU i ≥ absU c) by scalar_tac)]
          exact wout_dup hrel hinv hh hm hrun
      | FVar _ _ => exact wout_dup hrel hinv hh hm hrun
      | «Sort» _ => exact wout_dup hrel hinv hh hm hrun
      | Const _ _ => exact wout_dup hrel hinv hh hm hrun
      | Lit _ => exact wout_dup hrel hinv hh hm hrun
      | App a b =>
        simp only [absENodeView]
        have haR : EResolves lst (absEIdx a) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx b) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [liftArmApp]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (lift_get_run hrel hinv hop).apply
        have hgv := lift_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen haR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok a2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1 hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok b2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep := intern_e_app_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                a2 b2 (viewOK_app (hmono2.res hres1) hres2) hp3
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok r4 =>
                rw [hr3] at hrun hstep
                obtain ⟨st4, hst4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_lift_set hstep hst4
                rw [hkabs] at hset
                exact hset
      | Lam ty body mb =>
        simp only [absENodeView]
        have hpw := view_bind_wf hrel hinv hrv (Or.inl rfl)
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [liftArmLam]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (lift_get_run hrel hinv hop).apply
        have hgv := lift_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hi2v : absU i2 = absU c + 1 := by
              have h1 := ConRon.Refine.Nat.uadd_val hi2
              simpa using h1
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1 hp2
            rw [show absU i1 = m from hi1v, hi2v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok b2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep := intern_e_lam_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                t2 b2 mb hpw ⟨by
                  intro cc hcc; simp [ENodeView.echildren] at hcc
                  rcases hcc with rfl | rfl
                  · exact hmono2.res hres1
                  · exact hres2,
                 by intro cc hcc; simp [ENodeView.nchildren] at hcc,
                 by intro cc hcc; simp [ENodeView.lchildren] at hcc,
                 by intro cc hcc; simp [ENodeView.lschildren] at hcc⟩ hp3
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok r4 =>
                rw [hr3] at hrun hstep
                obtain ⟨st4, hst4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_lift_set hstep hst4
                rw [hkabs] at hset
                exact hset
      | ForallE ty body mb =>
        simp only [absENodeView]
        have hpw := view_bind_wf hrel hinv hrv (Or.inr rfl)
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [liftArmForallE]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (lift_get_run hrel hinv hop).apply
        have hgv := lift_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hi2v : absU i2 = absU c + 1 := by
              have h1 := ConRon.Refine.Nat.uadd_val hi2
              simpa using h1
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1 hp2
            rw [show absU i1 = m from hi1v, hi2v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok b2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep := intern_e_forall_e_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                t2 b2 mb hpw ⟨by
                  intro cc hcc; simp [ENodeView.echildren] at hcc
                  rcases hcc with rfl | rfl
                  · exact hmono2.res hres1
                  · exact hres2,
                 by intro cc hcc; simp [ENodeView.nchildren] at hcc,
                 by intro cc hcc; simp [ENodeView.lchildren] at hcc,
                 by intro cc hcc; simp [ENodeView.lschildren] at hcc⟩ hp3
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok r4 =>
                rw [hr3] at hrun hstep
                obtain ⟨st4, hst4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_lift_set hstep hst4
                rw [hkabs] at hset
                exact hset
      | LetE ty val body =>
        simp only [absENodeView]
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hvalR : EResolves lst (absEIdx val) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [liftArmLet]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (lift_get_run hrel hinv hop).apply
        have hgv := lift_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res hvalR) hq1 hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok w2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have hi2v : absU i2 = absU c + 1 := by
                have h1 := ConRon.Refine.Nat.uadd_val hi2
                simpa using h1
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hrec3 := ih hi1v hrel2 hinv2 hfroz2 (hmono2.res (hmono1.res hbR)) hq2 hp3
              rw [show absU i1 = m from hi1v, hi2v] at hrec3
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hrec3
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hrec3.err rfl)
              | Ok b2 =>
                rw [hr3] at hrun hrec3
                obtain ⟨lst3, hx3, hrel3, hinv3, hext3, hres3, hmono3, hfl5, hfl6, hq3⟩ :=
                  hrec3.dest
                refine WOutE.bind hx3 hext3 hmono3 hfl5 hfl6 ?_
                have hfroz3 : st3.store.shared_on = true → st3.store.scratch_on = true := by
                  intro hs; rw [hfl6]; exact hfroz2 (hfl5 ▸ hs)
                obtain ⟨p4, hp4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                obtain ⟨r4, st4⟩ := p4
                have hstep := intern_e_let_e_res (MemoRes.stable _) hrel3 hinv3 hfroz3 hq3
                  t2 w2 b2 (viewOK_letE (hmono3.res (hmono2.res hres1))
                    (hmono3.res hres2) hres3) hp4
                cases hr4 : r4 with
                | Err e =>
                  rw [hr4] at hrun hstep
                  have ho := Result.ok_injective hrun
                  rw [← ho]
                  exact wout_err_bind (hstep.err rfl)
                | Ok r5 =>
                  rw [hr4] at hrun hstep
                  obtain ⟨st5, hst5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                  have ho := Result.ok_injective hrun
                  rw [← ho]
                  have hset := wout_lift_set hstep hst5
                  rw [hkabs] at hset
                  exact hset
      | Proj nn i1 sub =>
        simp only [absENodeView]
        have hsR : EResolves lst (absEIdx sub) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hnR : (lst.store.ns.view (absNIdx nn)).isSome = true := by
          obtain ⟨rk, hw⟩ := hrel.storeWF
          exact (hw.nchildOK _ _ hvv _ (by simp [ENodeView.nchildren])).1
        rw [liftArmProj]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (lift_get_run hrel hinv hop).apply
        have hgv := lift_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i2, hi2', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v := hi1 i2 hi2'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi2v hrel hinv hfrozen hsR hm hp1
          rw [show absU i2 = m from hi2v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok u =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hstep := intern_e_proj_res (MemoRes.stable _) hrel1 hinv1 hfroz1 hq1
              nn i1 u (viewOK_proj (hmono1.nsres hnR) hres1) hp2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hstep
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hstep.err rfl)
            | Ok r3 =>
              rw [hr2] at hrun hstep
              obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have ho := Result.ok_injective hrun
              rw [← ho]
              have hset := wout_lift_set hstep hst3
              rw [hkabs] at hset
              exact hset

/-- `lift_loose_bvars_go` at `WOutE`. -/
theorem lift_loose_bvars_go_wout {pers st lst} {amount fuel : Std.U64}
    {h : arena.handle.EIdx} {c : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hh : EResolves lst (absEIdx h)) (hmemo : MemoRes Memos.liftC lst)
    (hrun : arena.expr_ops.lift_loose_bvars_go pers st amount fuel h c = ok o) :
    WOutE (MemoRes Memos.liftC) pers st lst o
      (liftLooseBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)) :=
  lift_loose_bvars_go_aux _ rfl hrel hinv hfrozen hh hmemo hrun

/-- `lift_loose_bvars_fast` at `WOutE`: the memo fresh before and dropped after. -/
theorem lift_loose_bvars_fast_wout {pers st lst} {fuel amount c : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (he : EResolves lst (absEIdx e))
    (hrun : arena.expr_ops.lift_loose_bvars_fast pers st fuel amount c e = ok o) :
    WOutE (MemoRes Memos.liftC) pers st lst o
      (liftLooseBVarsFast (absU fuel) (absU amount) (absU c) (absEIdx e)) := by
  rw [arena.expr_ops.lift_loose_bvars_fast] at hrun
  obtain ⟨st1, hst1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st2⟩ := q
  have hs1 := lift_clear_store hst1
  obtain ⟨hc1, hrel1, hinv1⟩ := wmemo_clear_step
    (upd := fun m v => { m with liftC := v }) (twinClear := Arena.liftClear)
    (fun _ => rfl) (lift_clear_run hrel hinv hst1)
  have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
    rw [hs1]; exact hfrozen
  have hgo := lift_loose_bvars_go_wout (lst := { lst with memos := { lst.memos with
      liftC := ∅ } }) hrel1 hinv1 hfroz1 he (MemoRes.of_empty rfl) hq
  show WOutR _ pers st lst o ((do
    Arena.liftClear
    let r ← liftLooseBVarsGo (absU amount) (absU fuel) (absEIdx e) (absU c)
    Arena.liftClear
    pure r).run lst)
  rw [run_bind_of hc1]
  cases hr : r with
  | Err ee =>
    rw [hr] at hrun hgo
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact wout_err_bind (hgo.err rfl)
  | Ok r1 =>
    rw [hr] at hrun hgo
    obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl1, hfl2, -⟩ := hgo.dest
    obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    have hs3 := lift_clear_store hst3
    obtain ⟨hc3, hrel3, hinv3⟩ := wmemo_clear_step
      (upd := fun m v => { m with liftC := v }) (twinClear := Arena.liftClear)
      (fun _ => rfl) (lift_clear_run hrel2 hinv2 hst3)
    rw [run_bind_of hx2, run_bind_of hc3]
    exact WOutR.ok rfl hrel3 hinv3 hext2 hres2 hmono2 (by rw [hs3, hfl1, hs1])
      (by rw [hs3, hfl2, hs1]) (MemoRes.of_empty rfl)

/-- `Arena/ExprOps.lean:491 liftLooseBVarsGo`.  **Corrected** (task #97-P5-Mut
round 2, finding 19): `hfrozen`, the handle walked resolves, and the memo
clause. -/
theorem lift_loose_bvars_go_refines {pers st lst} {amount fuel : Std.U64}
    {h : arena.handle.EIdx} {c : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hh : EResolves lst (absEIdx h)) (hmemo : MemoRes Memos.liftC lst)
    (hrun : arena.expr_ops.lift_loose_bvars_go pers st amount fuel h c = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (liftLooseBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)) :=
  (lift_loose_bvars_go_wout hrel hinv hfrozen hh hmemo hrun).toSim

/-- `Arena/ExprOps.lean:552 liftLooseBVarsFast`.  **Corrected** as the walk,
minus the memo clause, which the fresh memo pays for. -/
theorem lift_loose_bvars_fast_refines {pers st lst} {fuel amount c : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (he : EResolves lst (absEIdx e))
    (hrun : arena.expr_ops.lift_loose_bvars_fast pers st fuel amount c e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (liftLooseBVarsFast (absU fuel) (absU amount) (absU c) (absEIdx e)) :=
  (lift_loose_bvars_fast_wout hrel hinv hfrozen he hrun).toSim

/-! ### `resetMetaGo` -/

/-- The twin's `==` on binder data is `decide`. -/
theorem bm_beq_decide (x y : ConLeche.BinderMeta) : (x == y) = decide (x = y) :=
  Bool.eq_iff_iff.mpr (by simp)

def ResetGoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {fuel : Std.U64} {h : arena.handle.EIdx} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st →
    (st.store.shared_on = true → st.store.scratch_on = true) →
    EResolves lst (absEIdx h) → MemoRes Memos.resetC lst →
    arena.expr_ops.reset_meta_go pers st fuel h = ok o →
    WOutE (MemoRes Memos.resetC) pers st lst o (resetMetaGo (absU fuel) (absEIdx h))

private theorem reset_meta_go_aux (n : Nat) : ResetGoAt n := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hfrozen hh hm hrun
    rw [arena.expr_ops.reset_meta_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨vv, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hrrv := fail_run hrr
    have ho := Result.ok_injective hrun
    rw [← ho, hrrv]
    show AErrSim _ ((resetMetaGo (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, resetMetaGo_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hfrozen hh hm hrun
    rw [arena.expr_ops.reset_meta_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    have hi1 : ∀ i1 : Std.U64, (fuel - 1#u64 = ok i1) → i1.val = m := by
      intro i1 hi1
      have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
        (ConRon.Refine.Nat.usub_val hi1).2
      rw [h1, hn]; rfl
    show WOutR (MemoRes Memos.resetC) pers st lst o
      ((resetMetaGo (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = m + 1 from hn, resetMetaGo_succ]
    obtain ⟨rv, hrv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hview := view_run hrel hinv hrv
    cases hrvc : rv with
    | Err e =>
      rw [hrvc] at hrun hview
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact wout_err_bind hview
    | Ok ev =>
      rw [hrvc] at hrun hview hrv
      obtain ⟨lst0, hx, -, -, -, -⟩ := hview
      have hlst : lst0 = lst := view_run_state hx
      rw [hlst] at hx
      have hvv := store_view_of_run hx
      rw [run_bind_of hx]
      cases ev with
      | BVar _ => exact wout_dup hrel hinv hh hm hrun
      | «Sort» _ => exact wout_dup hrel hinv hh hm hrun
      | Const _ _ => exact wout_dup hrel hinv hh hm hrun
      | Lit _ => exact wout_dup hrel hinv hh hm hrun
      | FVar idx ty =>
        simp only [absENodeView]
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [resetArmFVar]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (reset_get_run hrel hinv hop).apply
        have hgv := reset_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨same, hsame, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            rw [eidx_eq2_abs hsame]
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hstep := intern_rebuilt_fvar_res (MemoRes.stable _) hrel1 hinv1 hfroz1 hq1
              (hmono1.res hh) hres1 hp2
            cases hrX : r2 with
            | Err e =>
              rw [hrX] at hrun hstep
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hstep.err rfl)
            | Ok rX =>
              rw [hrX] at hrun hstep
              obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have ho := Result.ok_injective hrun
              rw [← ho]
              have hset := wout_reset_set hstep hstX
              rw [hkabs] at hset
              exact hset
      | App f a =>
        simp only [absENodeView]
        have hfR : EResolves lst (absEIdx f) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have haR : EResolves lst (absEIdx a) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [resetArmApp]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (reset_get_run hrel hinv hop).apply
        have hgv := reset_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen hfR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok f2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res haR) hq1 hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok a2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨bb, hbb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨same, hsame, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have hs : (absEIdx f2 == absEIdx f && absEIdx a2 == absEIdx a) = same := by
                rw [eidx_eq2_abs hbb]
                cases bb with
                | true => rw [if_pos rfl] at hsame; rw [eidx_eq2_abs hsame]; rfl
                | false =>
                  rw [if_neg (by simp)] at hsame
                  rw [← Result.ok_injective hsame]; rfl
              rw [hs]
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep := intern_rebuilt_app_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                (hmono2.res (hmono1.res hh)) (hmono2.res hres1) hres2 hp3
              cases hrX : r3 with
              | Err e =>
                rw [hrX] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok rX =>
                rw [hrX] at hrun hstep
                obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_reset_set hstep hstX
                rw [hkabs] at hset
                exact hset
      | Lam ty body m0 =>
        simp only [absENodeView]
        have hpw0 := view_bind_wf hrel hinv hrv (Or.inl rfl)
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [resetArmLam]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (reset_get_run hrel hinv hop).apply
        have hgv := reset_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1 hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok b2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨pw, hpwn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨m2, hm2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨hm2abs, hm2wf⟩ := never_meta hpwn hm2
              obtain ⟨bb, hbb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨q, hqq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨st3, same⟩ := q
              have hs : st3 = st2 ∧ (absEIdx t2 == absEIdx ty &&
                  absEIdx b2 == absEIdx body &&
                    ((⟨.never⟩ : ConLeche.BinderMeta) ==
                      ConRon.Refine.absBinderMeta m0)) = same := by
                rw [eidx_eq2_abs hbb]
                cases bb with
                | true =>
                  rw [if_pos rfl] at hqq
                  obtain ⟨b1, hb1, hqq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hqq
                  obtain ⟨b3, hb3, hqq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hqq
                  have := Result.ok_injective hqq
                  simp only [Prod.mk.injEq] at this
                  obtain ⟨rfl, rfl⟩ := this
                  refine ⟨rfl, ?_⟩
                  rw [eidx_eq2_abs hb1]
                  cases b1 with
                  | true =>
                    rw [if_pos rfl] at hb3
                    rw [ConRon.Refine.Expr.binder_meta_beq_refines hm2wf hpw0 hb3, hm2abs,
                      bm_beq_decide]
                    rfl
                  | false =>
                    rw [if_neg (by simp)] at hb3
                    rw [← Result.ok_injective hb3]; rfl
                | false =>
                  rw [if_neg (by simp)] at hqq
                  have := Result.ok_injective hqq
                  simp only [Prod.mk.injEq] at this
                  obtain ⟨rfl, rfl⟩ := this
                  exact ⟨rfl, rfl⟩
              obtain ⟨hst, hs2⟩ := hs
              rw [hs2, ← hm2abs]
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              rw [hst] at hp3
              obtain ⟨r3, st4⟩ := p3
              have hstep := intern_rebuilt_lam_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                hm2wf (hmono2.res (hmono1.res hh)) (hmono2.res hres1) hres2 hp3
              cases hrX : r3 with
              | Err e =>
                rw [hrX] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok rX =>
                rw [hrX] at hrun hstep
                obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_reset_set hstep hstX
                rw [hkabs] at hset
                exact hset
      | ForallE ty body m0 =>
        simp only [absENodeView]
        have hpw0 := view_bind_wf hrel hinv hrv (Or.inr rfl)
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [resetArmForallE]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (reset_get_run hrel hinv hop).apply
        have hgv := reset_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1 hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok b2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨pw, hpwn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨m2, hm2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨hm2abs, hm2wf⟩ := never_meta hpwn hm2
              obtain ⟨bb, hbb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨q, hqq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨st3, same⟩ := q
              have hs : st3 = st2 ∧ (absEIdx t2 == absEIdx ty &&
                  absEIdx b2 == absEIdx body &&
                    ((⟨.never⟩ : ConLeche.BinderMeta) ==
                      ConRon.Refine.absBinderMeta m0)) = same := by
                rw [eidx_eq2_abs hbb]
                cases bb with
                | true =>
                  rw [if_pos rfl] at hqq
                  obtain ⟨b1, hb1, hqq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hqq
                  obtain ⟨b3, hb3, hqq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hqq
                  have := Result.ok_injective hqq
                  simp only [Prod.mk.injEq] at this
                  obtain ⟨rfl, rfl⟩ := this
                  refine ⟨rfl, ?_⟩
                  rw [eidx_eq2_abs hb1]
                  cases b1 with
                  | true =>
                    rw [if_pos rfl] at hb3
                    rw [ConRon.Refine.Expr.binder_meta_beq_refines hm2wf hpw0 hb3, hm2abs,
                      bm_beq_decide]
                    rfl
                  | false =>
                    rw [if_neg (by simp)] at hb3
                    rw [← Result.ok_injective hb3]; rfl
                | false =>
                  rw [if_neg (by simp)] at hqq
                  have := Result.ok_injective hqq
                  simp only [Prod.mk.injEq] at this
                  obtain ⟨rfl, rfl⟩ := this
                  exact ⟨rfl, rfl⟩
              obtain ⟨hst, hs2⟩ := hs
              rw [hs2, ← hm2abs]
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              rw [hst] at hp3
              obtain ⟨r3, st4⟩ := p3
              have hstep := intern_rebuilt_forall_e_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                hm2wf (hmono2.res (hmono1.res hh)) (hmono2.res hres1) hres2 hp3
              cases hrX : r3 with
              | Err e =>
                rw [hrX] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok rX =>
                rw [hrX] at hrun hstep
                obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_reset_set hstep hstX
                rw [hkabs] at hset
                exact hset
      | LetE ty val body =>
        simp only [absENodeView]
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hvalR : EResolves lst (absEIdx val) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [resetArmLet]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (reset_get_run hrel hinv hop).apply
        have hgv := reset_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi1v hrel hinv hfrozen htyR hm hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hi1v hrel1 hinv1 hfroz1 (hmono1.res hvalR) hq1 hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok w2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hrec3 := ih hi1v hrel2 hinv2 hfroz2 (hmono2.res (hmono1.res hbR)) hq2 hp3
              rw [show absU i1 = m from hi1v] at hrec3
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hrec3
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hrec3.err rfl)
              | Ok b2 =>
                rw [hr3] at hrun hrec3
                obtain ⟨lst3, hx3, hrel3, hinv3, hext3, hres3, hmono3, hfl5, hfl6, hq3⟩ :=
                  hrec3.dest
                refine WOutE.bind hx3 hext3 hmono3 hfl5 hfl6 ?_
                have hfroz3 : st3.store.shared_on = true → st3.store.scratch_on = true := by
                  intro hs; rw [hfl6]; exact hfroz2 (hfl5 ▸ hs)
                obtain ⟨bb, hbb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                obtain ⟨q, hqq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                obtain ⟨st4, same⟩ := q
                have hs : st4 = st3 ∧ (absEIdx t2 == absEIdx ty &&
                    absEIdx w2 == absEIdx val && absEIdx b2 == absEIdx body) = same := by
                  rw [eidx_eq2_abs hbb]
                  cases bb with
                  | true =>
                    rw [if_pos rfl] at hqq
                    obtain ⟨b1, hb1, hqq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hqq
                    obtain ⟨b3, hb3, hqq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hqq
                    have := Result.ok_injective hqq
                    simp only [Prod.mk.injEq] at this
                    obtain ⟨rfl, rfl⟩ := this
                    refine ⟨rfl, ?_⟩
                    rw [eidx_eq2_abs hb1]
                    cases b1 with
                    | true => rw [if_pos rfl] at hb3; rw [eidx_eq2_abs hb3]; rfl
                    | false =>
                      rw [if_neg (by simp)] at hb3
                      rw [← Result.ok_injective hb3]; rfl
                  | false =>
                    rw [if_neg (by simp)] at hqq
                    have := Result.ok_injective hqq
                    simp only [Prod.mk.injEq] at this
                    obtain ⟨rfl, rfl⟩ := this
                    exact ⟨rfl, rfl⟩
                obtain ⟨hst, hs2⟩ := hs
                rw [hs2]
                obtain ⟨p4, hp4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                rw [hst] at hp4
                obtain ⟨r4, st5⟩ := p4
                have hstep := intern_rebuilt_let_e_res (MemoRes.stable _) hrel3 hinv3 hfroz3
                  hq3 (hmono3.res (hmono2.res (hmono1.res hh)))
                  (hmono3.res (hmono2.res hres1)) (hmono3.res hres2) hres3 hp4
                cases hrX : r4 with
                | Err e =>
                  rw [hrX] at hrun hstep
                  have ho := Result.ok_injective hrun
                  rw [← ho]
                  exact wout_err_bind (hstep.err rfl)
                | Ok rX =>
                  rw [hrX] at hrun hstep
                  obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                  have ho := Result.ok_injective hrun
                  rw [← ho]
                  have hset := wout_reset_set hstep hstX
                  rw [hkabs] at hset
                  exact hset
      | Proj nn i1 sub =>
        simp only [absENodeView]
        have hsR : EResolves lst (absEIdx sub) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hnR : (lst.store.ns.view (absNIdx nn)).isSome = true := by
          obtain ⟨rk, hw⟩ := hrel.storeWF
          exact (hw.nchildOK _ _ hvv _ (by simp [ENodeView.nchildren])).1
        rw [resetArmProj]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (reset_get_run hrel hinv hop).apply
        have hgv := reset_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i2, hi2', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v := hi1 i2 hi2'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hi2v hrel hinv hfrozen hsR hm hp1
          rw [show absU i2 = m from hi2v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok u =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨same, hsame, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            rw [eidx_eq2_abs hsame]
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hstep := intern_rebuilt_proj_res (MemoRes.stable _) hrel1 hinv1 hfroz1 hq1
              (hmono1.res hh) (hmono1.nsres hnR) hres1 hp2
            cases hrX : r2 with
            | Err e =>
              rw [hrX] at hrun hstep
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hstep.err rfl)
            | Ok rX =>
              rw [hrX] at hrun hstep
              obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have ho := Result.ok_injective hrun
              rw [← ho]
              have hset := wout_reset_set hstep hstX
              rw [hkabs] at hset
              exact hset

theorem reset_meta_go_wout {pers st lst} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hh : EResolves lst (absEIdx h)) (hmemo : MemoRes Memos.resetC lst)
    (hrun : arena.expr_ops.reset_meta_go pers st fuel h = ok o) :
    WOutE (MemoRes Memos.resetC) pers st lst o (resetMetaGo (absU fuel) (absEIdx h)) :=
  reset_meta_go_aux _ rfl hrel hinv hfrozen hh hmemo hrun


/-- `reset_meta_fast` at `WOutE`: the memo fresh before and dropped after. -/
theorem reset_meta_fast_wout {pers st lst} {fuel : Std.U64} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (he : EResolves lst (absEIdx e))
    (hrun : arena.expr_ops.reset_meta_fast pers st fuel e = ok o) :
    WOutE (MemoRes Memos.resetC) pers st lst o
      (resetMetaFast (absU fuel) (absEIdx e)) := by
  rw [arena.expr_ops.reset_meta_fast] at hrun
  obtain ⟨st1, hst1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st2⟩ := q
  have hs1 := reset_clear_store hst1
  obtain ⟨hc1, hrel1, hinv1⟩ := wmemo_clear_step
    (upd := fun m v => { m with resetC := v }) (twinClear := Arena.resetClear)
    (fun _ => rfl) (reset_clear_run hrel hinv hst1)
  have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
    rw [hs1]; exact hfrozen
  have hgo := reset_meta_go_wout (lst := { lst with memos := { lst.memos with
      resetC := ∅ } }) hrel1 hinv1 hfroz1 he (MemoRes.of_empty rfl) hq
  show WOutR _ pers st lst o ((do
    Arena.resetClear
    let r ← resetMetaGo (absU fuel) (absEIdx e)
    Arena.resetClear
    pure r).run lst)
  rw [run_bind_of hc1]
  cases hr : r with
  | Err ee =>
    rw [hr] at hrun hgo
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact wout_err_bind (hgo.err rfl)
  | Ok r1 =>
    rw [hr] at hrun hgo
    obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl1, hfl2, -⟩ := hgo.dest
    obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    have hs3 := reset_clear_store hst3
    obtain ⟨hc3, hrel3, hinv3⟩ := wmemo_clear_step
      (upd := fun m v => { m with resetC := v }) (twinClear := Arena.resetClear)
      (fun _ => rfl) (reset_clear_run hrel2 hinv2 hst3)
    rw [run_bind_of hx2, run_bind_of hc3]
    exact WOutR.ok rfl hrel3 hinv3 hext2 hres2 hmono2 (by rw [hs3, hfl1, hs1])
      (by rw [hs3, hfl2, hs1]) (MemoRes.of_empty rfl)

/-- `Arena/ExprOps.lean:567 resetMetaGo`.  **Corrected** (task #97-P5-Mut round
2, finding 19): `hfrozen`, the handle walked resolves, and the memo clause. -/
theorem reset_meta_go_refines {pers st lst} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hh : EResolves lst (absEIdx h)) (hmemo : MemoRes Memos.resetC lst)
    (hrun : arena.expr_ops.reset_meta_go pers st fuel h = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (resetMetaGo (absU fuel) (absEIdx h)) :=
  (reset_meta_go_wout hrel hinv hfrozen hh hmemo hrun).toSim

/-- `Arena/ExprOps.lean:633 resetMetaFast`.  **Corrected** as the walk, minus
the memo clause. -/
theorem reset_meta_fast_refines {pers st lst} {fuel : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (he : EResolves lst (absEIdx e))
    (hrun : arena.expr_ops.reset_meta_fast pers st fuel e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (resetMetaFast (absU fuel) (absEIdx e)) :=
  (reset_meta_fast_wout hrel hinv hfrozen he hrun).toSim

/-! ### `abstractRange`, the SPEC descent: no memo, no cutoff -/

def AbsRangeAt (n : Nat) : Prop :=
  ∀ {Q : AState → Prop}, QStable Q →
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {fuel : Std.U64} {h : arena.handle.EIdx} {d k c : Std.U64} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st →
    (st.store.shared_on = true → st.store.scratch_on = true) →
    EResolves lst (absEIdx h) → Q lst →
    arena.expr_ops.abstract_range pers st fuel h d k c = ok o →
    WOutE Q pers st lst o
      (abstractRange (absU fuel) (absEIdx h) (absU d) (absU k) (absU c))

private theorem abstract_range_aux (n : Nat) : AbsRangeAt n := by
  induction n with
  | zero =>
    intro Q hQ pers st lst fuel h d k c o hn hrel hinv hfrozen hh hm hrun
    rw [arena.expr_ops.abstract_range] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨vv, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hrrv := fail_run hrr
    have ho := Result.ok_injective hrun
    rw [← ho, hrrv]
    show AErrSim _ ((abstractRange (absU fuel) (absEIdx h) (absU d) (absU k) (absU c)).run lst)
    rw [show absU fuel = 0 from hn, abstractRange_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro Q hQ pers st lst fuel h d k c o hn hrel hinv hfrozen hh hm hrun
    rw [arena.expr_ops.abstract_range] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    have hi1 : ∀ i1 : Std.U64, (fuel - 1#u64 = ok i1) → i1.val = m := by
      intro i1 hi1
      have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
        (ConRon.Refine.Nat.usub_val hi1).2
      rw [h1, hn]; rfl
    show WOutR Q pers st lst o
      ((abstractRange (absU fuel) (absEIdx h) (absU d) (absU k) (absU c)).run lst)
    rw [show absU fuel = m + 1 from hn, abstractRange_succ]
    obtain ⟨rv, hrv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hview := view_run hrel hinv hrv
    cases hrvc : rv with
    | Err e =>
      rw [hrvc] at hrun hview
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact wout_err_bind hview
    | Ok ev =>
      rw [hrvc] at hrun hview hrv
      obtain ⟨lst0, hx, -, -, -, -⟩ := hview
      have hlst : lst0 = lst := view_run_state hx
      rw [hlst] at hx
      have hvv := store_view_of_run hx
      rw [run_bind_of hx]
      cases ev with
      | BVar _ => exact wout_dup hrel hinv hh hm hrun
      | FVar idx _ =>
        simp only [absENodeView]
        simp only at hrun
        by_cases h1 : d ≤ idx
        · rw [if_pos h1] at hrun
          obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hiv : absU i = absU d + absU k := by
            have := ConRon.Refine.Nat.uadd_val hi; simpa using this
          by_cases h2 : idx < i
          · rw [if_pos h2] at hrun
            rw [if_pos (show absU d ≤ absU idx ∧ absU idx < absU d + absU k by
              constructor <;> scalar_tac)]
            obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hv1 : absU i1 = absU i - 1 := (ConRon.Refine.Nat.usub_val hi1').2
            have hv2 : absU i2 = absU i1 - absU idx := (ConRon.Refine.Nat.usub_val hi2).2
            have hv3 : absU i3 = absU c + absU i2 := by
              have := ConRon.Refine.Nat.uadd_val hi3; simpa using this
            rw [show absU c + (absU d + absU k - 1 - absU idx) = absU i3 by
              rw [hv3, hv2, hv1, hiv]]
            exact intern_e_bvar_res hQ hrel hinv hfrozen hm i3 hrun
          · rw [if_neg h2] at hrun
            rw [if_neg (show ¬ (absU d ≤ absU idx ∧ absU idx < absU d + absU k) by
              intro ⟨_, hc⟩; exact h2 (by scalar_tac))]
            exact wout_dup hrel hinv hh hm hrun
        · rw [if_neg h1] at hrun
          rw [if_neg (show ¬ (absU d ≤ absU idx ∧ absU idx < absU d + absU k) by
            intro ⟨hc, _⟩; exact h1 (by scalar_tac))]
          exact wout_dup hrel hinv hh hm hrun
      | «Sort» _ => exact wout_dup hrel hinv hh hm hrun
      | Const _ _ => exact wout_dup hrel hinv hh hm hrun
      | Lit _ => exact wout_dup hrel hinv hh hm hrun
      | App a b =>
        simp only [absENodeView]
        have haR : EResolves lst (absEIdx a) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx b) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [absRangeArmApp]
        obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v := hi1 i1 hi1'
        obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, st1⟩ := p1
        have hrec1 := ih hQ hi1v hrel hinv hfrozen haR hm hp1
        rw [show absU i1 = m from hi1v] at hrec1
        cases hr1 : r1 with
        | Err e =>
          rw [hr1] at hrun hrec1
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact wout_err_bind (hrec1.err rfl)
        | Ok a2 =>
          rw [hr1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
            hrec1.dest
          refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
          have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
            intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
          obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r2, st2⟩ := p2
          have hrec2 := ih hQ hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1 hp2
          rw [show absU i1 = m from hi1v] at hrec2
          cases hr2 : r2 with
          | Err e =>
            rw [hr2] at hrun hrec2
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec2.err rfl)
          | Ok b2 =>
            rw [hr2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
              hrec2.dest
            refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
            have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
              intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
            exact intern_e_app_res hQ hrel2 hinv2 hfroz2 hq2
              a2 b2 (viewOK_app (hmono2.res hres1) hres2) hrun
      | Lam ty body mb =>
        simp only [absENodeView]
        have hpw := view_bind_wf hrel hinv hrv (Or.inl rfl)
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [absRangeArmLam]
        obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v := hi1 i1 hi1'
        obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, st1⟩ := p1
        have hrec1 := ih hQ hi1v hrel hinv hfrozen htyR hm hp1
        rw [show absU i1 = m from hi1v] at hrec1
        cases hr1 : r1 with
        | Err e =>
          rw [hr1] at hrun hrec1
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact wout_err_bind (hrec1.err rfl)
        | Ok t2 =>
          rw [hr1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
            hrec1.dest
          refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
          have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
            intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
          obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v : absU i2 = absU c + 1 := by
            have h1 := ConRon.Refine.Nat.uadd_val hi2
            simpa using h1
          obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r2, st2⟩ := p2
          have hrec2 := ih hQ hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1 hp2
          rw [show absU i1 = m from hi1v, hi2v] at hrec2
          cases hr2 : r2 with
          | Err e =>
            rw [hr2] at hrun hrec2
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec2.err rfl)
          | Ok b2 =>
            rw [hr2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
              hrec2.dest
            refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
            have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
              intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
            exact intern_e_lam_res hQ hrel2 hinv2 hfroz2 hq2
              t2 b2 mb hpw (viewOK_bind2 (hmono2.res hres1) hres2) hrun
      | ForallE ty body mb =>
        simp only [absENodeView]
        have hpw := view_bind_wf hrel hinv hrv (Or.inr rfl)
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [absRangeArmForallE]
        obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v := hi1 i1 hi1'
        obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, st1⟩ := p1
        have hrec1 := ih hQ hi1v hrel hinv hfrozen htyR hm hp1
        rw [show absU i1 = m from hi1v] at hrec1
        cases hr1 : r1 with
        | Err e =>
          rw [hr1] at hrun hrec1
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact wout_err_bind (hrec1.err rfl)
        | Ok t2 =>
          rw [hr1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
            hrec1.dest
          refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
          have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
            intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
          obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v : absU i2 = absU c + 1 := by
            have h1 := ConRon.Refine.Nat.uadd_val hi2
            simpa using h1
          obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r2, st2⟩ := p2
          have hrec2 := ih hQ hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1 hp2
          rw [show absU i1 = m from hi1v, hi2v] at hrec2
          cases hr2 : r2 with
          | Err e =>
            rw [hr2] at hrun hrec2
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec2.err rfl)
          | Ok b2 =>
            rw [hr2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
              hrec2.dest
            refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
            have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
              intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
            exact intern_e_forall_e_res hQ hrel2 hinv2 hfroz2 hq2
              t2 b2 mb hpw (viewOK_bind2 (hmono2.res hres1) hres2) hrun
      | LetE ty val body =>
        simp only [absENodeView]
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hvalR : EResolves lst (absEIdx val) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [absRangeArmLet]
        obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v := hi1 i1 hi1'
        obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, st1⟩ := p1
        have hrec1 := ih hQ hi1v hrel hinv hfrozen htyR hm hp1
        rw [show absU i1 = m from hi1v] at hrec1
        cases hr1 : r1 with
        | Err e =>
          rw [hr1] at hrun hrec1
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact wout_err_bind (hrec1.err rfl)
        | Ok t2 =>
          rw [hr1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
            hrec1.dest
          refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
          have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
            intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
          obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r2, st2⟩ := p2
          have hrec2 := ih hQ hi1v hrel1 hinv1 hfroz1 (hmono1.res hvalR) hq1 hp2
          rw [show absU i1 = m from hi1v] at hrec2
          cases hr2 : r2 with
          | Err e =>
            rw [hr2] at hrun hrec2
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec2.err rfl)
          | Ok w2 =>
            rw [hr2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
              hrec2.dest
            refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
            have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
              intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
            obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hi2v : absU i2 = absU c + 1 := by
              have h1 := ConRon.Refine.Nat.uadd_val hi2
              simpa using h1
            obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r3, st3⟩ := p3
            have hrec3 := ih hQ hi1v hrel2 hinv2 hfroz2 (hmono2.res (hmono1.res hbR)) hq2 hp3
            rw [show absU i1 = m from hi1v, hi2v] at hrec3
            cases hr3 : r3 with
            | Err e =>
              rw [hr3] at hrun hrec3
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec3.err rfl)
            | Ok b2 =>
              rw [hr3] at hrun hrec3
              obtain ⟨lst3, hx3, hrel3, hinv3, hext3, hres3, hmono3, hfl5, hfl6, hq3⟩ :=
                hrec3.dest
              refine WOutE.bind hx3 hext3 hmono3 hfl5 hfl6 ?_
              have hfroz3 : st3.store.shared_on = true → st3.store.scratch_on = true := by
                intro hs; rw [hfl6]; exact hfroz2 (hfl5 ▸ hs)
              exact intern_e_let_e_res hQ hrel3 hinv3 hfroz3 hq3
                t2 w2 b2 (viewOK_letE (hmono3.res (hmono2.res hres1))
                  (hmono3.res hres2) hres3) hrun
      | Proj nn i1 sub =>
        simp only [absENodeView]
        have hsR : EResolves lst (absEIdx sub) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hnR : (lst.store.ns.view (absNIdx nn)).isSome = true := by
          obtain ⟨rk, hw⟩ := hrel.storeWF
          exact (hw.nchildOK _ _ hvv _ (by simp [ENodeView.nchildren])).1
        rw [absRangeArmProj]
        obtain ⟨i2, hi2', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v := hi1 i2 hi2'
        obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, st1⟩ := p1
        have hrec1 := ih hQ hi2v hrel hinv hfrozen hsR hm hp1
        rw [show absU i2 = m from hi2v] at hrec1
        cases hr1 : r1 with
        | Err e =>
          rw [hr1] at hrun hrec1
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact wout_err_bind (hrec1.err rfl)
        | Ok u =>
          rw [hr1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
            hrec1.dest
          refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
          have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
            intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
          exact intern_e_proj_res hQ hrel1 hinv1 hfroz1 hq1
            nn i1 u (viewOK_proj (hmono1.nsres hnR) hres1) hrun

/-- `abstract_range` at `WOutE`, for any stable side invariant. -/
theorem abstract_range_wout {Q : AState → Prop} (hQ : QStable Q) {pers st lst}
    {fuel : Std.U64} {h : arena.handle.EIdx} {d k c : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hh : EResolves lst (absEIdx h)) (hq : Q lst)
    (hrun : arena.expr_ops.abstract_range pers st fuel h d k c = ok o) :
    WOutE Q pers st lst o
      (abstractRange (absU fuel) (absEIdx h) (absU d) (absU k) (absU c)) :=
  abstract_range_aux _ hQ rfl hrel hinv hfrozen hh hq hrun

/-- `Arena/ExprOps.lean:669 abstractRange` — the SPEC descent (task #97-P6-11
keeps it as the statement subject beside the executed `abstractRangeGo`). -/
theorem abstract_range_refines {pers st lst} {fuel : Std.U64}
    {h : arena.handle.EIdx} {d k c : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hh : EResolves lst (absEIdx h))
    (hrun : arena.expr_ops.abstract_range pers st fuel h d k c = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (abstractRange (absU fuel) (absEIdx h) (absU d) (absU k) (absU c)) :=
  (abstract_range_wout QStable.true hrel hinv hfrozen hh trivial hrun).toSim

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

/-! ### `renameConstsGo` -/

def RenameGoAt (n : Nat) : Prop :=
  ∀ {F : Type} {inst : arena.expr_ops.NIdxToNIdx F} {f : F} {g : NIdx → NIdx},
    RenameRel inst f g →
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {fuel : Std.U64} {h : arena.handle.EIdx} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st →
    (st.store.shared_on = true → st.store.scratch_on = true) →
    EResolves lst (absEIdx h) → MemoRes Memos.renameC lst →
    RenameRes inst f lst.store →
    arena.expr_ops.rename_consts_go inst pers st f fuel h = ok o →
    WOutE (MemoRes Memos.renameC) pers st lst o (renameConstsGo g (absU fuel) (absEIdx h))

private theorem rename_consts_go_aux (n : Nat) : RenameGoAt n := by
  induction n with
  | zero =>
    intro F inst f g hg pers st lst fuel h o hn hrel hinv hfrozen hh hm hren hrun
    rw [arena.expr_ops.rename_consts_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨vv, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hrrv := fail_run hrr
    have ho := Result.ok_injective hrun
    rw [← ho, hrrv]
    show AErrSim _ ((renameConstsGo g (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, renameConstsGo_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro F inst f g hg pers st lst fuel h o hn hrel hinv hfrozen hh hm hren hrun
    rw [arena.expr_ops.rename_consts_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    have hi1 : ∀ i1 : Std.U64, (fuel - 1#u64 = ok i1) → i1.val = m := by
      intro i1 hi1
      have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
        (ConRon.Refine.Nat.usub_val hi1).2
      rw [h1, hn]; rfl
    show WOutR (MemoRes Memos.renameC) pers st lst o
      ((renameConstsGo g (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = m + 1 from hn, renameConstsGo_succ]
    obtain ⟨rv, hrv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hview := view_run hrel hinv hrv
    cases hrvc : rv with
    | Err e =>
      rw [hrvc] at hrun hview
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact wout_err_bind hview
    | Ok ev =>
      rw [hrvc] at hrun hview hrv
      obtain ⟨lst0, hx, -, -, -, -⟩ := hview
      have hlst : lst0 = lst := view_run_state hx
      rw [hlst] at hx
      have hvv := store_view_of_run hx
      rw [run_bind_of hx]
      cases ev with
      | BVar _ => exact wout_dup hrel hinv hh hm hrun
      | «Sort» _ => exact wout_dup hrel hinv hh hm hrun
      | Lit _ => exact wout_dup hrel hinv hh hm hrun
      | Const nn us =>
        simp only [absENodeView] at hvv ⊢
        obtain ⟨n2, hn2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hgn := hg nn n2 hn2
        have husR : (lst.store.lss.view (absLsIdx us)).isSome = true := by
          obtain ⟨rk, hw⟩ := hrel.storeWF
          exact (hw.lschildOK _ _ hvv _ (by simp [ENodeView.lschildren])).1
        have hstep := intern_e_const_res (MemoRes.stable _) hrel hinv hfrozen hm n2 us
          (viewOK_const (hren nn n2 hn2) husR) hrun
        show WOutR _ pers st lst o ((internRebuiltConst (absEIdx h)
          (g (absNIdx nn) == absNIdx nn) (g (absNIdx nn)) (absLsIdx us)).run lst)
        rw [hgn, internRebuiltConst]
        exact wout_same_of_intern hrel.storeWF hstep (fun hs => by
          rw [beq_iff_eq] at hs; rw [hs]; exact hvv)
      | FVar idx ty =>
        simp only [absENodeView] at hvv ⊢
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [renameArmFVar]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (rename_get_run hrel hinv hop).apply
        have hgv := rename_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hg hi1v hrel hinv hfrozen htyR hm hren hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hstep0 := intern_e_fvar_res (MemoRes.stable _) hrel1 hinv1 hfroz1 hq1
              idx t2 (viewOK_fvar hres1) hp2
            have hstep : WOutE (MemoRes Memos.renameC) pers st1 lst1 (r2, st2)
                (internRebuiltFVar (absEIdx h) (absEIdx t2 == absEIdx ty) (absU idx)
                  (absEIdx t2)) := by
              rw [internRebuiltFVar]
              exact wout_same_of_intern hrel1.storeWF hstep0 (fun hs => by
                rw [beq_iff_eq] at hs; rw [hs]; exact hmono1.1 _ _ hvv)
            cases hrX : r2 with
            | Err e =>
              rw [hrX] at hrun hstep
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hstep.err rfl)
            | Ok rX =>
              rw [hrX] at hrun hstep
              obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have ho := Result.ok_injective hrun
              rw [← ho]
              have hset := wout_rename_set hstep hstX
              rw [hkabs] at hset
              exact hset
      | App a b =>
        simp only [absENodeView] at hvv ⊢
        have haR : EResolves lst (absEIdx a) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx b) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [renameArmApp]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (rename_get_run hrel hinv hop).apply
        have hgv := rename_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hg hi1v hrel hinv hfrozen haR hm hren hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok a2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hg hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1
              (hren.mono hmono1) hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok b2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep0 := intern_e_app_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                a2 b2 (viewOK_app (hmono2.res hres1) hres2) hp3
              have hstep : WOutE (MemoRes Memos.renameC) pers st2 lst2 (r3, st3)
                  (internRebuiltApp (absEIdx h) (absEIdx a2 == absEIdx a &&
                    absEIdx b2 == absEIdx b) (absEIdx a2) (absEIdx b2)) := by
                rw [internRebuiltApp]
                exact wout_same_of_intern hrel2.storeWF hstep0 (fun hs => by
                  simp only [Bool.and_eq_true, beq_iff_eq] at hs
                  rw [hs.1, hs.2]; exact hmono2.1 _ _ (hmono1.1 _ _ hvv))
              cases hrX : r3 with
              | Err e =>
                rw [hrX] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok rX =>
                rw [hrX] at hrun hstep
                obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_rename_set hstep hstX
                rw [hkabs] at hset
                exact hset
      | Lam ty body mb =>
        simp only [absENodeView] at hvv ⊢
        have hpw := view_bind_wf hrel hinv hrv (Or.inl rfl)
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [renameArmLam]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (rename_get_run hrel hinv hop).apply
        have hgv := rename_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hg hi1v hrel hinv hfrozen htyR hm hren hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hg hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1
              (hren.mono hmono1) hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok b2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep0 := intern_e_lam_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                t2 b2 mb hpw (viewOK_bind2 (hmono2.res hres1) hres2) hp3
              have hstep : WOutE (MemoRes Memos.renameC) pers st2 lst2 (r3, st3)
                  (internRebuiltLam (absEIdx h) (absEIdx t2 == absEIdx ty &&
                    absEIdx b2 == absEIdx body) (absEIdx t2) (absEIdx b2)
                    (ConRon.Refine.absBinderMeta mb)) := by
                rw [internRebuiltLam]
                exact wout_same_of_intern hrel2.storeWF hstep0 (fun hs => by
                  simp only [Bool.and_eq_true, beq_iff_eq] at hs
                  rw [hs.1, hs.2]; exact hmono2.1 _ _ (hmono1.1 _ _ hvv))
              cases hrX : r3 with
              | Err e =>
                rw [hrX] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok rX =>
                rw [hrX] at hrun hstep
                obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_rename_set hstep hstX
                rw [hkabs] at hset
                exact hset
      | ForallE ty body mb =>
        simp only [absENodeView] at hvv ⊢
        have hpw := view_bind_wf hrel hinv hrv (Or.inr rfl)
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [renameArmForallE]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (rename_get_run hrel hinv hop).apply
        have hgv := rename_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hg hi1v hrel hinv hfrozen htyR hm hren hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hg hi1v hrel1 hinv1 hfroz1 (hmono1.res hbR) hq1
              (hren.mono hmono1) hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok b2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hstep0 := intern_e_forall_e_res (MemoRes.stable _) hrel2 hinv2 hfroz2 hq2
                t2 b2 mb hpw (viewOK_bind2 (hmono2.res hres1) hres2) hp3
              have hstep : WOutE (MemoRes Memos.renameC) pers st2 lst2 (r3, st3)
                  (internRebuiltForallE (absEIdx h) (absEIdx t2 == absEIdx ty &&
                    absEIdx b2 == absEIdx body) (absEIdx t2) (absEIdx b2)
                    (ConRon.Refine.absBinderMeta mb)) := by
                rw [internRebuiltForallE]
                exact wout_same_of_intern hrel2.storeWF hstep0 (fun hs => by
                  simp only [Bool.and_eq_true, beq_iff_eq] at hs
                  rw [hs.1, hs.2]; exact hmono2.1 _ _ (hmono1.1 _ _ hvv))
              cases hrX : r3 with
              | Err e =>
                rw [hrX] at hrun hstep
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hstep.err rfl)
              | Ok rX =>
                rw [hrX] at hrun hstep
                obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have ho := Result.ok_injective hrun
                rw [← ho]
                have hset := wout_rename_set hstep hstX
                rw [hkabs] at hset
                exact hset
      | LetE ty val body =>
        simp only [absENodeView] at hvv ⊢
        have htyR : EResolves lst (absEIdx ty) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hvalR : EResolves lst (absEIdx val) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hbR : EResolves lst (absEIdx body) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        rw [renameArmLet]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (rename_get_run hrel hinv hop).apply
        have hgv := rename_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i1, hi1', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi1v := hi1 i1 hi1'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hg hi1v hrel hinv hfrozen htyR hm hren hp1
          rw [show absU i1 = m from hi1v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok t2 =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hrec2 := ih hg hi1v hrel1 hinv1 hfroz1 (hmono1.res hvalR) hq1
              (hren.mono hmono1) hp2
            rw [show absU i1 = m from hi1v] at hrec2
            cases hr2 : r2 with
            | Err e =>
              rw [hr2] at hrun hrec2
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hrec2.err rfl)
            | Ok w2 =>
              rw [hr2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl3, hfl4, hq2⟩ :=
                hrec2.dest
              refine WOutE.bind hx2 hext2 hmono2 hfl3 hfl4 ?_
              have hfroz2 : st2.store.shared_on = true → st2.store.scratch_on = true := by
                intro hs; rw [hfl4]; exact hfroz1 (hfl3 ▸ hs)
              obtain ⟨p3, hp3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨r3, st3⟩ := p3
              have hrec3 := ih hg hi1v hrel2 hinv2 hfroz2 (hmono2.res (hmono1.res hbR)) hq2
                ((hren.mono hmono1).mono hmono2) hp3
              rw [show absU i1 = m from hi1v] at hrec3
              cases hr3 : r3 with
              | Err e =>
                rw [hr3] at hrun hrec3
                have ho := Result.ok_injective hrun
                rw [← ho]
                exact wout_err_bind (hrec3.err rfl)
              | Ok b2 =>
                rw [hr3] at hrun hrec3
                obtain ⟨lst3, hx3, hrel3, hinv3, hext3, hres3, hmono3, hfl5, hfl6, hq3⟩ :=
                  hrec3.dest
                refine WOutE.bind hx3 hext3 hmono3 hfl5 hfl6 ?_
                have hfroz3 : st3.store.shared_on = true → st3.store.scratch_on = true := by
                  intro hs; rw [hfl6]; exact hfroz2 (hfl5 ▸ hs)
                obtain ⟨p4, hp4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                obtain ⟨r4, st4⟩ := p4
                have hstep0 := intern_e_let_e_res (MemoRes.stable _) hrel3 hinv3 hfroz3 hq3
                  t2 w2 b2 (viewOK_letE (hmono3.res (hmono2.res hres1))
                    (hmono3.res hres2) hres3) hp4
                have hstep : WOutE (MemoRes Memos.renameC) pers st3 lst3 (r4, st4)
                    (internRebuiltLetE (absEIdx h) (absEIdx t2 == absEIdx ty &&
                      absEIdx w2 == absEIdx val && absEIdx b2 == absEIdx body)
                      (absEIdx t2) (absEIdx w2) (absEIdx b2)) := by
                  rw [internRebuiltLetE]
                  exact wout_same_of_intern hrel3.storeWF hstep0 (fun hs => by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hs
                    rw [hs.1.1, hs.1.2, hs.2]
                    exact hmono3.1 _ _ (hmono2.1 _ _ (hmono1.1 _ _ hvv)))
                cases hrX : r4 with
                | Err e =>
                  rw [hrX] at hrun hstep
                  have ho := Result.ok_injective hrun
                  rw [← ho]
                  exact wout_err_bind (hstep.err rfl)
                | Ok rX =>
                  rw [hrX] at hrun hstep
                  obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                  have ho := Result.ok_injective hrun
                  rw [← ho]
                  have hset := wout_rename_set hstep hstX
                  rw [hkabs] at hset
                  exact hset
      | Proj nn i1 sub =>
        simp only [absENodeView] at hvv ⊢
        have hsR : EResolves lst (absEIdx sub) :=
          EResolves.child hrel.storeWF hvv (by simp [ENodeView.echildren])
        have hnR : (lst.store.ns.view (absNIdx nn)).isSome = true := by
          obtain ⟨rk, hw⟩ := hrel.storeWF
          exact (hw.nchildOK _ _ hvv _ (by simp [ENodeView.nchildren])).1
        rw [renameArmProj]
        obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hkabs := eidx_nat_key_abs hk
        rw [show absU (0#u64 : Std.U64) = 0 from rfl] at hkabs
        obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hget := (rename_get_run hrel hinv hop).apply
        have hgv := rename_get_val hrel hinv hop
        rw [hkabs] at hget hgv
        rw [run_bind_of hget]
        cases hopc : op with
        | some r =>
          rw [hopc] at hrun hgv
          have ho := Result.ok_injective hrun
          rw [← ho]
          exact WOutR.pure hrel hinv (hm _ _ hgv) hm
        | none =>
          rw [hopc] at hrun
          simp only [Option.map_none]
          obtain ⟨i2, hi2', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v := hi1 i2 hi2'
          obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, st1⟩ := p1
          have hrec1 := ih hg hi2v hrel hinv hfrozen hsR hm hren hp1
          rw [show absU i2 = m from hi2v] at hrec1
          cases hr1 : r1 with
          | Err e =>
            rw [hr1] at hrun hrec1
            have ho := Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind (hrec1.err rfl)
          | Ok u =>
            rw [hr1] at hrun hrec1
            obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, hq1⟩ :=
              hrec1.dest
            refine WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
            have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
              intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
            obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨r2, st2⟩ := p2
            have hstep0 := intern_e_proj_res (MemoRes.stable _) hrel1 hinv1 hfroz1 hq1
              nn i1 u (viewOK_proj (hmono1.nsres hnR) hres1) hp2
            have hstep : WOutE (MemoRes Memos.renameC) pers st1 lst1 (r2, st2)
                (internRebuiltProj (absEIdx h) (absEIdx u == absEIdx sub) (absNIdx nn)
                  (absU i1) (absEIdx u)) := by
              rw [internRebuiltProj]
              exact wout_same_of_intern hrel1.storeWF hstep0 (fun hs => by
                rw [beq_iff_eq] at hs; rw [hs]; exact hmono1.1 _ _ hvv)
            cases hrX : r2 with
            | Err e =>
              rw [hrX] at hrun hstep
              have ho := Result.ok_injective hrun
              rw [← ho]
              exact wout_err_bind (hstep.err rfl)
            | Ok rX =>
              rw [hrX] at hrun hstep
              obtain ⟨stX, hstX, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have ho := Result.ok_injective hrun
              rw [← ho]
              have hset := wout_rename_set hstep hstX
              rw [hkabs] at hset
              exact hset



theorem rename_consts_go_wout {F : Type} {inst : arena.expr_ops.NIdxToNIdx F}
    {f : F} {g : NIdx → NIdx} (hg : RenameRel inst f g) {pers st lst}
    {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hh : EResolves lst (absEIdx h)) (hmemo : MemoRes Memos.renameC lst)
    (hren : RenameRes inst f lst.store)
    (hrun : arena.expr_ops.rename_consts_go inst pers st f fuel h = ok o) :
    WOutE (MemoRes Memos.renameC) pers st lst o (renameConstsGo g (absU fuel) (absEIdx h)) :=
  rename_consts_go_aux _ hg rfl hrel hinv hfrozen hh hmemo hren hrun

/-- `rename_consts_fast` at `WOutE`: the memo fresh before and dropped after. -/
theorem rename_consts_fast_wout {pers st lst} {F : Type} {inst : arena.expr_ops.NIdxToNIdx F} {fuel : Std.U64} {f : F} {g : NIdx → NIdx} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hg : RenameRel inst f g) (he : EResolves lst (absEIdx e))
    (hren : RenameRes inst f lst.store)
    (hrun : arena.expr_ops.rename_consts_fast inst pers st fuel f e = ok o) :
    WOutE (MemoRes Memos.renameC) pers st lst o
      (renameConstsFast (absU fuel) g (absEIdx e)) := by
  rw [arena.expr_ops.rename_consts_fast] at hrun
  obtain ⟨st1, hst1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, st2⟩ := q
  have hs1 := rename_clear_store hst1
  obtain ⟨hc1, hrel1, hinv1⟩ := wmemo_clear_step
    (upd := fun m v => { m with renameC := v }) (twinClear := Arena.renameClear)
    (fun _ => rfl) (rename_clear_run hrel hinv hst1)
  have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
    rw [hs1]; exact hfrozen
  have hgo := rename_consts_go_wout hg (lst := { lst with memos := { lst.memos with
      renameC := ∅ } }) hrel1 hinv1 hfroz1 he (MemoRes.of_empty rfl) hren hq
  show WOutR _ pers st lst o ((do
    Arena.renameClear
    let r ← renameConstsGo g (absU fuel) (absEIdx e)
    Arena.renameClear
    pure r).run lst)
  rw [run_bind_of hc1]
  cases hr : r with
  | Err ee =>
    rw [hr] at hrun hgo
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact wout_err_bind (hgo.err rfl)
  | Ok r1 =>
    rw [hr] at hrun hgo
    obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hres2, hmono2, hfl1, hfl2, -⟩ := hgo.dest
    obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := Result.ok_injective hrun
    rw [← ho]
    have hs3 := rename_clear_store hst3
    obtain ⟨hc3, hrel3, hinv3⟩ := wmemo_clear_step
      (upd := fun m v => { m with renameC := v }) (twinClear := Arena.renameClear)
      (fun _ => rfl) (rename_clear_run hrel2 hinv2 hst3)
    rw [run_bind_of hx2, run_bind_of hc3]
    exact WOutR.ok rfl hrel3 hinv3 hext2 hres2 hmono2 (by rw [hs3, hfl1, hs1])
      (by rw [hs3, hfl2, hs1]) (MemoRes.of_empty rfl)

/-- `Arena/ExprOps.lean:1102 renameConstsGo`.  **Corrected** (task #97-P5-Mut
round 2, finding 19): `hfrozen`, the handle walked resolves, the memo clause,
and `RenameRes` — the dictionary names LIVE constants, without which the
`const` arm interns a node over a dangling name and `StoreWF` fails. -/
theorem rename_consts_go_refines {F : Type}
    {inst : arena.expr_ops.NIdxToNIdx F} {pers st lst} {f : F}
    {g : NIdx → NIdx} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hf : RenameRel inst f g)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hh : EResolves lst (absEIdx h)) (hmemo : MemoRes Memos.renameC lst)
    (hren : RenameRes inst f lst.store)
    (hrun : arena.expr_ops.rename_consts_go inst pers st f fuel h = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (renameConstsGo g (absU fuel) (absEIdx h)) :=
  (rename_consts_go_wout hf hrel hinv hfrozen hh hmemo hren hrun).toSim

/-- `Arena/ExprOps.lean:1168 renameConstsFast`.  **Corrected** as the walk,
minus the memo clause. -/
theorem rename_consts_fast_refines {F : Type}
    {inst : arena.expr_ops.NIdxToNIdx F} {pers st lst} {fuel : Std.U64} {f : F}
    {g : NIdx → NIdx} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hf : RenameRel inst f g)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (he : EResolves lst (absEIdx e)) (hren : RenameRes inst f lst.store)
    (hrun : arena.expr_ops.rename_consts_fast inst pers st fuel f e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (renameConstsFast (absU fuel) g (absEIdx e)) :=
  (rename_consts_fast_wout hrel hinv hfrozen hf he hren hrun).toSim

/-! ## `mkAppN` — the application spine, rebuilt

The twin has BOTH shapes (task #97-P6-15 gave it the cursor form for the
batched β), so this pair is one-to-one: `mk_app_n` is `mkAppN` at the `List`
and `mk_app_n_from` is `mkAppNFrom` at the push-order `Array` and the same
increasing cursor.  `Specs.lean` primitives: `internE`, `internAppE`. -/

/-! ### `mkAppN`, the tier's first walk closed under finding 19

**Task #97-P5-Mut corrected both statements**: they carried `hrel`/`hinv` and
nothing else, and the `app` each step interns has the PREVIOUS step's answer
as its function child.  What goes in is `hfrozen` (the tier flag the port's
own `intern` tests, carried across the step by `estore_intern_app_abs`'s
third conjunct) and the
two `EResolves` the `ViewOK` at each step needs — of the head and of every
argument.  They are the smallest hypotheses that make the statement true, and
they are what `WOutE` then re-establishes one step down. -/

/-- **Twin-only**: the cursor form over an array is the list form over what
the cursor has not consumed.  `mkAppN` is `mk_app_n`'s twin and `mkAppNFrom`
is `mk_app_n_from`'s, and this is the one place the two shapes meet. -/
theorem mkAppNFrom_eq (arr : Array EIdx) :
    ∀ (n i : Nat) (f : EIdx), arr.size - i = n →
      mkAppNFrom f arr i = mkAppN f (arr.toList.drop i) := by
  intro n
  induction n with
  | zero =>
    intro i f hn
    rw [mkAppNFrom, dif_neg (show ¬ (i < arr.size) from by omega),
      List.drop_eq_nil_of_le (by simpa using Nat.le_of_sub_eq_zero hn), mkAppN]
  | succ m ih =>
    intro i f hn
    have hlt : i < arr.size := by omega
    rw [mkAppNFrom, dif_pos hlt]
    rw [show arr.toList.drop i = arr[i] :: arr.toList.drop (i + 1) from by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp]
    rw [mkAppN]
    have : ∀ g : EIdx, mkAppNFrom g arr (i + 1) = mkAppN g (arr.toList.drop (i + 1)) :=
      fun g => ih (i + 1) g (by omega)
    simp only [Arena.internAppE]
    exact bind_congr (fun g => this g)

theorem absEIdxArr_toList (v : alloc.vec.Vec arena.handle.EIdx) :
    (absEIdxArr v).toList = absEIdxList v := by
  simp [absEIdxArr, absEIdxList]

private theorem mk_app_n_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {f : arena.handle.EIdx} {args : alloc.vec.Vec arena.handle.EIdx}
      {i : Std.Usize} {o},
      args.val.length - i.val = n →
      AStateRel pers st lst → AStateInv pers st →
      (st.store.shared_on = true → st.store.scratch_on = true) →
      EResolves lst (absEIdx f) →
      (∀ x ∈ args.val, EResolves lst (absEIdx x)) →
      arena.expr_ops.mk_app_n_from pers st f args i = ok o →
      WOutE (fun _ => True) pers st lst o
        (mkAppNFrom (absEIdx f) (absEIdxArr args) (absSz i)) := by
  induction n with
  | zero =>
    intro pers st lst f args i o hn hrel hinv hfrozen hf hargs hrun
    rw [arena.expr_ops.mk_app_n_from] at hrun
    have hge : i.val ≥ args.val.length := by omega
    rw [if_pos (show i ≥ alloc.vec.Vec.len args from by
      show args.val.length ≤ i.val
      omega)] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho, mkAppNFrom]
    rw [dif_neg (show ¬ (absSz i < (absEIdxArr args).size) from by
      rw [absEIdxArr_size]; show ¬ (i.val < args.val.length); omega)]
    exact WOutR.pure hrel hinv hf trivial
  | succ m ih =>
    intro pers st lst f args i o hn hrel hinv hfrozen hf hargs hrun
    rw [arena.expr_ops.mk_app_n_from] at hrun
    have hlt : i.val < args.val.length := by omega
    rw [if_neg (show ¬ (i ≥ alloc.vec.Vec.len args) from by
      show ¬ (args.val.length ≤ i.val)
      omega)] at hrun
    obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨hb, hval⟩ := ExprOps.vecIndexAt he1
    obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he2] at hrun
    obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, st1⟩ := p1
    have hres1 : EResolves lst (absEIdx e1) := hargs e1 (hval ▸ List.getElem_mem hb)
    have hview : lst.store.ViewOK (.app (absEIdx f) (absEIdx e1)) :=
      viewOK_app hf hres1
    have hstep := intern_e_app_res QStable.true hrel hinv hfrozen trivial f e1 hview hp1
    rw [mkAppNFrom, dif_pos (show absSz i < (absEIdxArr args).size from by
      rw [absEIdxArr_size]; exact hlt)]
    rw [show (absEIdxArr args)[absSz i]'(by rw [absEIdxArr_size]; exact hlt)
        = absEIdx e1 from by rw [absEIdxArr_get args i.val hlt, hval]]
    cases hr : r with
    | Err ee =>
      rw [hr] at hrun
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact wout_err_bind (hstep.err (by rw [hr]))
    | Ok g =>
      rw [hr] at hp1 hstep
      obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hg, hmono1, hfl1, hfl2, -⟩ :=
        WOutE.dest hstep
      rw [hr] at hrun
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v : absSz i2 = absSz i + 1 := absSz_add_one hi2
      have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
        intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
      have hargs1 : ∀ x ∈ args.val, EResolves lst1 (absEIdx x) := by
        intro x hx
        exact hmono1.res (hargs x hx)
      have hi2n : args.val.length - i2.val = m := by
        have : i2.val = i.val + 1 := hi2v
        omega
      have hrec := ih (st := st1) (lst := lst1) (f := g) (i := i2)
        hi2n hrel1 hinv1 hfroz1 hg hargs1 hrun
      rw [hi2v] at hrec
      exact WOutE.bind hx1 hext1 hmono1 hfl1 hfl2 hrec

/-- `Arena/ExprOps.lean:1079 mkAppNFrom`. -/
theorem mk_app_n_from_refines {pers st lst} {f : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hf : EResolves lst (absEIdx f))
    (hargs : ∀ x ∈ args.val, EResolves lst (absEIdx x))
    (hrun : arena.expr_ops.mk_app_n_from pers st f args i = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (mkAppNFrom (absEIdx f) (absEIdxArr args) (absSz i)) :=
  (mk_app_n_from_aux _ rfl hrel hinv hfrozen hf hargs hrun).toSim

/-- `Arena/ExprOps.lean:1069 mkAppN`. -/
theorem mk_app_n_refines {pers st lst} {f : arena.handle.EIdx}
    {args : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hf : EResolves lst (absEIdx f))
    (hargs : ∀ x ∈ args.val, EResolves lst (absEIdx x))
    (hrun : arena.expr_ops.mk_app_n pers st f args = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (mkAppN (absEIdx f) (absEIdxList args)) := by
  rw [arena.expr_ops.mk_app_n] at hrun
  have h := (mk_app_n_from_aux _ rfl hrel hinv hfrozen hf hargs hrun).toSim
  rw [show absSz (0#usize) = 0 from rfl,
    mkAppNFrom_eq (absEIdxArr args) ((absEIdxArr args).size - 0) 0 (absEIdx f) rfl,
    List.drop_zero, absEIdxArr_toList] at h
  exact h

/-! ## The telescopes' outcome (task #97-P5-Mut round 2)

The telescope walks answer an `Option` of a handle or of a domain list and a
handle, so `WOutE` (whose answer is ONE handle, with its `EResolves`) does not
fit them.  `WOutX` is `WOutE` at any result type, without the answer clause and
without a side invariant: the run equation, the two invariants, `Ext`,
`EViewExt` and the two tier flags — what a caller that walks again after the
call needs (`instPisAtFGo`'s domain intern after its recursive call). -/

def WOutX {α β : Type} (A : α → β) (pers : arena.store.PersTier)
    (st : arena.monad.AState) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState)
    (res : Except Arena.CheckError (β × AState)) : Prop :=
  match o.1 with
  | .Ok r => ∃ lst', res = .ok (A r, lst') ∧ AStateRel pers o.2 lst' ∧
      AStateInv pers o.2 ∧ Ext lst.store lst'.store ∧ EViewExt lst.store lst'.store ∧
      o.2.store.shared_on = st.store.shared_on ∧
      o.2.store.scratch_on = st.store.scratch_on
  | .Err e => AErrSim e res

theorem WOutX.toSim {α β : Type} {A : α → β} {pers st lst o} {x : AM β}
    (h : WOutX A pers st lst o (x.run lst)) : Sim A (fun _ => True) pers lst o x := by
  show AOut A (fun _ => True) pers lst o.1 o.2 (x.run lst)
  simp only [WOutX] at h
  cases ho : o.1 with
  | Ok r =>
    rw [ho] at h
    obtain ⟨lst', hx, h1, h2, h3, -⟩ := h
    exact AOut.ok hx h1 h2 h3 trivial
  | Err e => rw [ho] at h; exact AOut.err h

theorem WOutX.ok {α β : Type} {A : α → β} {pers st lst} {r : α}
    {st' : arena.monad.AState} {res : Except Arena.CheckError (β × AState)} {lst' : AState}
    (hx : res = .ok (A r, lst')) (h1 : AStateRel pers st' lst')
    (h2 : AStateInv pers st') (h3 : Ext lst.store lst'.store)
    (h5 : EViewExt lst.store lst'.store)
    (h6 : st'.store.shared_on = st.store.shared_on)
    (h7 : st'.store.scratch_on = st.store.scratch_on) :
    WOutX A pers st lst (.Ok r, st') res :=
  ⟨lst', hx, h1, h2, h3, h5, h6, h7⟩

theorem WOutX.dest {α β : Type} {A : α → β} {pers st lst} {r : α}
    {st' : arena.monad.AState} {res : Except Arena.CheckError (β × AState)}
    (h : WOutX A pers st lst (.Ok r, st') res) :
    ∃ lst', res = .ok (A r, lst') ∧ AStateRel pers st' lst' ∧
      AStateInv pers st' ∧ Ext lst.store lst'.store ∧ EViewExt lst.store lst'.store ∧
      st'.store.shared_on = st.store.shared_on ∧
      st'.store.scratch_on = st.store.scratch_on := h

theorem WOutX.err_bind {α β γ : Type} {A : α → β} {e : kernel.core_types.CheckError}
    {pers : arena.store.PersTier} {st stB : arena.monad.AState} {lst0 lst : AState}
    {x : AM γ} {f : γ → AM β} (h : AErrSim e (x.run lst)) :
    WOutX A pers st lst0 (.Err e, stB) ((do let v ← x; f v).run lst) := by
  show AErrSim e _
  rw [StateT.run_bind]
  exact AErrSim.bind h _

theorem WOutX.bind {α β γ : Type} {A : α → β} {pers : arena.store.PersTier}
    {st st1 : arena.monad.AState} {lst lst1 : AState}
    {o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState}
    {g : γ} {x : AM γ} {k : γ → AM β}
    (hx1 : x.run lst = .ok (g, lst1)) (hext1 : Ext lst.store lst1.store)
    (hmono1 : EViewExt lst.store lst1.store)
    (hfl1 : st1.store.shared_on = st.store.shared_on)
    (hfl2 : st1.store.scratch_on = st.store.scratch_on)
    (h : WOutX A pers st1 lst1 o ((k g).run lst1)) :
    WOutX A pers st lst o ((do let v ← x; k v).run lst) := by
  rw [run_bind_of hx1]
  simp only [WOutX] at h ⊢
  cases ho : o.1 with
  | Ok r =>
    rw [ho] at h
    obtain ⟨lst', hx, h1, h2, h3, h5, h6, h7⟩ := h
    exact ⟨lst', hx, h1, h2, Ext.trans hext1 h3, EViewExt.trans hmono1 h5,
      by rw [h6, hfl1], by rw [h7, hfl2]⟩
  | Err e => rw [ho] at h; exact h

/-- The twin's `view` run at a handle that decodes. -/
theorem view_run_some {lst : AState} {hh : EIdx} {v : ENodeView}
    (h : lst.store.view hh = some v) : (Arena.view hh).run lst = .ok (v, lst) := by
  show ((match lst.store.view hh with
          | some v => (pure v : AM ENodeView)
          | none => Arena.fail
              (.internal "arena: dangling expression handle")).run lst) = _
  rw [h]; rfl

theorem view_of_viewBind' {st : EStore} {i : EIdx} {ty b : EIdx}
    {m : ConLeche.BinderMeta} (htg : ETag.isBind i.tag = true)
    (h : st.viewBind i = some (ty, b, m)) :
    st.view i = some (eBindView i.tag ty b m) := by
  simp only [EStore.view, htg, if_true, h]

theorem view_none_of_viewBind {st : EStore} {i : EIdx}
    (htg : ETag.isBind i.tag = true) (h : st.viewBind i = none) :
    st.view i = none := by
  simp only [EStore.view, htg, if_true, h]

/-- A cursor below the length reads the element and moves on. -/
theorem listFrom_cons (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize)
    (hi : i.val < args.val.length) :
    absEIdxListFrom args i =
      absEIdx args.val[i.val] :: (args.val.drop (i.val + 1)).map absEIdx := by
  simp only [absEIdxListFrom]
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem listFrom_nil (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize)
    (hi : args.val.length ≤ i.val) : absEIdxListFrom args i = [] := by
  simp only [absEIdxListFrom]
  rw [List.drop_eq_nil_of_le hi]; rfl

theorem mem_drop_here {l : List arena.handle.EIdx} {i : Nat} (hi : i < l.length) :
    l[i] ∈ l.drop i := by
  rw [List.drop_eq_getElem_cons hi]; exact List.mem_cons_self

theorem mem_drop_succ {l : List arena.handle.EIdx} {i : Nat} {x : arena.handle.EIdx}
    (hi : i < l.length) (hx : x ∈ l.drop (i + 1)) : x ∈ l.drop i := by
  rw [List.drop_eq_getElem_cons hi]; exact List.mem_cons_of_mem _ hx

/-- The binder read of a `∀`-tagged handle that decodes: the twin's view is the
`forallE` the port's `view_bind` answered, and its body resolves. -/
theorem view_bind_forall {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {t : Std.U32} (htg : (absEIdx h).tag = absU32 t)
    (hF : t = arena.handle.ETAG_FORALL_E) (hh : EResolves lst (absEIdx h))
    {o} (ho : arena.monad.view_bind pers st h = ok o) :
    ∃ dom body m, o = some (dom, body, m) ∧
      lst.store.view (absEIdx h) = some (.forallE (absEIdx dom) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) ∧
      EResolves lst (absEIdx dom) ∧ EResolves lst (absEIdx body) := by
  have htF : (absEIdx h).tag = ETag.forallE := by rw [htg, hF, etag_forallE_abs]
  have hbind : ETag.isBind (absEIdx h).tag = true := by rw [htF]; decide
  have hvb := (view_bind_run hrel hbind ho).apply
  have h2 : (Arena.viewBind (absEIdx h)).run lst
      = .ok (lst.store.viewBind (absEIdx h), lst) := rfl
  rw [h2] at hvb
  simp only [Except.ok.injEq, Prod.mk.injEq, and_true] at hvb
  cases hoc : o with
  | none =>
    rw [hoc] at hvb
    have := view_none_of_viewBind hbind hvb
    simp [EResolves, this] at hh
  | some p =>
    obtain ⟨dom, body, m⟩ := p
    rw [hoc] at hvb
    have hv := view_of_viewBind' hbind hvb
    rw [htF] at hv
    simp only [eBindView, ETag.forallE, ETag.lam] at hv
    have hv' : lst.store.view (absEIdx h) = some (.forallE (absEIdx dom) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) := by
      rw [hv]; rfl
    exact ⟨dom, body, m, rfl, hv',
      EResolves.child hrel.storeWF hv' (by simp [ENodeView.echildren]),
      EResolves.child hrel.storeWF hv' (by simp [ENodeView.echildren])⟩

/-- A `∀`-less handle that decodes: the twin's view is not a `forallE`. -/
theorem view_not_forall {lst : AState} {h : arena.handle.EIdx} {t : Std.U32}
    (htg : (absEIdx h).tag = absU32 t) (hF : ¬ t = arena.handle.ETAG_FORALL_E)
    {v : ENodeView} (hv : lst.store.view (absEIdx h) = some v) :
    ∀ ty b m, v ≠ .forallE ty b m := by
  intro ty b m hc
  subst hc
  have := EStore_view_tagOf hv
  rw [htg] at this
  exact hF (absU32_inj (by rw [this, etag_forallE_abs]; rfl))

/-! ### `instPis` and its cursor companion -/

private theorem inst_pis_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {e : arena.handle.EIdx} {args : alloc.vec.Vec arena.handle.EIdx}
      {i : Std.Usize} {o},
      args.val.length - i.val = n → AStateRel pers st lst → AStateInv pers st →
      (st.store.shared_on = true → st.store.scratch_on = true) →
      EResolves lst (absEIdx e) →
      (∀ x ∈ args.val.drop i.val, EResolves lst (absEIdx x)) →
      arena.expr_ops.inst_pis_from pers st fuel e args i = ok o →
      WOutX absOptE pers st lst o
        ((instPis (absU fuel) (absEIdx e) (absEIdxListFrom args i)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel e args i o hn hrel hinv hfrozen he hargs hrun
    rw [arena.expr_ops.inst_pis_from] at hrun
    rw [if_pos (show i ≥ alloc.vec.Vec.len args from by
      show args.val.length ≤ i.val; omega)] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    rw [← Result.ok_injective hrun, listFrom_nil args i (by omega)]
    exact WOutX.ok rfl hrel hinv (Ext.refl _) (EViewExt.refl _) rfl rfl
  | succ k ih =>
    intro pers st lst fuel e args i o hn hrel hinv hfrozen he hargs hrun
    have hlt : i.val < args.val.length := by omega
    rw [arena.expr_ops.inst_pis_from] at hrun
    rw [if_neg (show ¬ (i ≥ alloc.vec.Vec.len args) from by
      show ¬ (args.val.length ≤ i.val); omega)] at hrun
    rw [listFrom_cons args i hlt]
    simp only [instPis]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp he
    rw [run_bind_of (view_run_some hv)]
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htg := eidx_tag_abs ht
    by_cases hF : t = arena.handle.ETAG_FORALL_E
    · rw [if_pos hF] at hrun
      obtain ⟨ob, hob, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨dom, body, mb, hobe, hvF, -, hbR⟩ := view_bind_forall hrel htg hF he hob
      rw [hvF] at hv
      simp only [Option.some.injEq] at hv
      subst hv
      rw [hobe] at hrun
      obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hb1, hval1⟩ := ExprOps.vecIndexAt he1
      obtain ⟨a, ha, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hae : a = args.val[i.val] := by rw [dupId_eidx _ _ ha, hval1]
      obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r1, st1⟩ := p1
      have haR : EResolves lst (absEIdx a) := by
        rw [hae]; exact hargs _ (mem_drop_here hlt)
      have hstep := instantiate1_fast_wout hrel hinv hfrozen hbR haR hp1
      rw [show absU (0#u64 : Std.U64) = 0 from rfl, hae] at hstep
      cases hr1 : r1 with
      | Err er =>
        rw [hr1] at hrun hstep
        rw [← Result.ok_injective hrun]
        exact WOutX.err_bind (hstep.err rfl)
      | Ok b =>
        rw [hr1] at hrun hstep
        obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, -⟩ :=
          hstep.dest
        refine WOutX.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
        have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
          intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
        obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi3v : i3.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi3; simpa using this
        have hrec := ih (i := i3) (by omega) hrel1 hinv1 hfroz1 hres1
          (fun x hx => hmono1.res (hargs x (mem_drop_succ hlt (hi3v ▸ hx)))) hrun
        simp only [absEIdxListFrom, hi3v] at hrec
        exact hrec
    · rw [if_neg hF] at hrun
      rw [← Result.ok_injective hrun]
      have hnf := view_not_forall htg hF hv
      cases v with
      | forallE ty b m => exact absurd rfl (hnf ty b m)
      | _ => exact WOutX.ok rfl hrel hinv (Ext.refl _) (EViewExt.refl _) rfl rfl

/-! ### `instPisAt` and its cursor companion -/

private theorem inst_pis_at_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
      {h : arena.handle.EIdx} {o},
      args.val.length - i.val = n → AStateRel pers st lst → AStateInv pers st →
      (st.store.shared_on = true → st.store.scratch_on = true) →
      EResolves lst (absEIdx h) →
      (∀ x ∈ args.val.drop i.val, EResolves lst (absEIdx x)) →
      arena.expr_ops.inst_pis_at_from pers st fuel args i h = ok o →
      WOutX absOptArgsE pers st lst o
        ((instPisAt (absU fuel) (absEIdxListFrom args i) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel args i h o hn hrel hinv hfrozen he hargs hrun
    rw [arena.expr_ops.inst_pis_at_from] at hrun
    rw [if_pos (show i ≥ alloc.vec.Vec.len args from by
      show args.val.length ≤ i.val; omega)] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    rw [← Result.ok_injective hrun, listFrom_nil args i (by omega)]
    exact WOutX.ok rfl hrel hinv (Ext.refl _) (EViewExt.refl _) rfl rfl
  | succ k ih =>
    intro pers st lst fuel args i h o hn hrel hinv hfrozen he hargs hrun
    have hlt : i.val < args.val.length := by omega
    rw [arena.expr_ops.inst_pis_at_from] at hrun
    rw [if_neg (show ¬ (i ≥ alloc.vec.Vec.len args) from by
      show ¬ (args.val.length ≤ i.val); omega)] at hrun
    rw [listFrom_cons args i hlt]
    simp only [instPisAt]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp he
    rw [run_bind_of (view_run_some hv)]
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htg := eidx_tag_abs ht
    by_cases hF : t = arena.handle.ETAG_FORALL_E
    · rw [if_pos hF] at hrun
      obtain ⟨ob, hob, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨dom, body, mb, hobe, hvF, -, hbR⟩ := view_bind_forall hrel htg hF he hob
      rw [hvF] at hv
      simp only [Option.some.injEq] at hv
      subst hv
      rw [hobe] at hrun
      obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hb1, hval1⟩ := ExprOps.vecIndexAt he1
      obtain ⟨a, ha, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hae : a = args.val[i.val] := by rw [dupId_eidx _ _ ha, hval1]
      obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r1, st1⟩ := p1
      have haR : EResolves lst (absEIdx a) := by
        rw [hae]; exact hargs _ (mem_drop_here hlt)
      have hstep := instantiate1_fast_wout hrel hinv hfrozen hbR haR hp1
      rw [show absU (0#u64 : Std.U64) = 0 from rfl, hae] at hstep
      cases hr1 : r1 with
      | Err er =>
        rw [hr1] at hrun hstep
        rw [← Result.ok_injective hrun]
        exact WOutX.err_bind (hstep.err rfl)
      | Ok b =>
        rw [hr1] at hrun hstep
        obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, -⟩ :=
          hstep.dest
        refine WOutX.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
        have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
          intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
        obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi3v : i3.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi3; simpa using this
        obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r2, st2⟩ := p2
        have hrec := ih (i := i3) (by omega) hrel1 hinv1 hfroz1 hres1
          (fun x hx => hmono1.res (hargs x (mem_drop_succ hlt (hi3v ▸ hx)))) hp2
        simp only [absEIdxListFrom, hi3v] at hrec
        cases hr2 : r2 with
        | Err er =>
          rw [hr2] at hrun hrec
          rw [← Result.ok_injective hrun]
          exact WOutX.err_bind hrec
        | Ok o1 =>
          rw [hr2] at hrun hrec
          obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hmono2, hfl3, hfl4⟩ := hrec.dest
          rw [run_bind_of hx2]
          cases ho1 : o1 with
          | none =>
            rw [ho1] at hrun
            rw [← Result.ok_injective hrun]
            exact WOutX.ok rfl hrel2 hinv2 hext2 hmono2 hfl3 hfl4
          | some pp =>
            rw [ho1] at hrun
            obtain ⟨vv, e2⟩ := pp
            obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            rw [← Result.ok_injective hrun]
            refine WOutX.ok ?_ hrel2 hinv2 hext2 hmono2 hfl3 hfl4
            show _ = Except.ok (some (absEIdxList v1, absEIdx e2), lst2)
            rw [show absEIdxList v1 = absEIdx dom :: absEIdxList vv from
              ExprOps.cons_eidx_refines hv1]
            rfl
    · rw [if_neg hF] at hrun
      rw [← Result.ok_injective hrun]
      have hnf := view_not_forall htg hF hv
      cases v with
      | forallE ty b m => exact absurd rfl (hnf ty b m)
      | _ => exact WOutX.ok rfl hrel hinv (Ext.refl _) (EViewExt.refl _) rfl rfl

/-- The binder read of a `λ`-tagged handle that decodes: the twin's view is the
`lam` the port's `view_bind` answered, and its body resolves. -/
theorem view_bind_lam {pers st lst} (hrel : AStateRel pers st lst)
    {h : arena.handle.EIdx} {t : Std.U32} (htg : (absEIdx h).tag = absU32 t)
    (hF : t = arena.handle.ETAG_LAM) (hh : EResolves lst (absEIdx h))
    {o} (ho : arena.monad.view_bind pers st h = ok o) :
    ∃ dom body m, o = some (dom, body, m) ∧
      lst.store.view (absEIdx h) = some (.lam (absEIdx dom) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) ∧
      EResolves lst (absEIdx dom) ∧ EResolves lst (absEIdx body) := by
  have htL : (absEIdx h).tag = ETag.lam := by rw [htg, hF, etag_lam_abs]
  have hbind : ETag.isBind (absEIdx h).tag = true := by rw [htL]; decide
  have hvb := (view_bind_run hrel hbind ho).apply
  have h2 : (Arena.viewBind (absEIdx h)).run lst
      = .ok (lst.store.viewBind (absEIdx h), lst) := rfl
  rw [h2] at hvb
  simp only [Except.ok.injEq, Prod.mk.injEq, and_true] at hvb
  cases hoc : o with
  | none =>
    rw [hoc] at hvb
    have := view_none_of_viewBind hbind hvb
    simp [EResolves, this] at hh
  | some p =>
    obtain ⟨dom, body, m⟩ := p
    rw [hoc] at hvb
    have hv := view_of_viewBind' hbind hvb
    rw [htL] at hv
    simp only [eBindView, ETag.lam, ETag.lam] at hv
    have hv' : lst.store.view (absEIdx h) = some (.lam (absEIdx dom) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) := by
      rw [hv]; rfl
    exact ⟨dom, body, m, rfl, hv',
      EResolves.child hrel.storeWF hv' (by simp [ENodeView.echildren]),
      EResolves.child hrel.storeWF hv' (by simp [ENodeView.echildren])⟩

/-- A `λ`-less handle that decodes: the twin's view is not a `lam`. -/
theorem view_not_lam {lst : AState} {h : arena.handle.EIdx} {t : Std.U32}
    (htg : (absEIdx h).tag = absU32 t) (hF : ¬ t = arena.handle.ETAG_LAM)
    {v : ENodeView} (hv : lst.store.view (absEIdx h) = some v) :
    ∀ ty b m, v ≠ .lam ty b m := by
  intro ty b m hc
  subst hc
  have := EStore_view_tagOf hv
  rw [htg] at this
  exact hF (absU32_inj (by rw [this, etag_lam_abs]; rfl))

/-! ### `instLamsAt` and its cursor companion -/

private theorem inst_lams_at_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {args : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
      {h : arena.handle.EIdx} {o},
      args.val.length - i.val = n → AStateRel pers st lst → AStateInv pers st →
      (st.store.shared_on = true → st.store.scratch_on = true) →
      EResolves lst (absEIdx h) →
      (∀ x ∈ args.val.drop i.val, EResolves lst (absEIdx x)) →
      arena.expr_ops.inst_lams_at_from pers st fuel args i h = ok o →
      WOutX absOptArgsE pers st lst o
        ((instLamsAt (absU fuel) (absEIdxListFrom args i) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel args i h o hn hrel hinv hfrozen he hargs hrun
    rw [arena.expr_ops.inst_lams_at_from] at hrun
    rw [if_pos (show i ≥ alloc.vec.Vec.len args from by
      show args.val.length ≤ i.val; omega)] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    rw [← Result.ok_injective hrun, listFrom_nil args i (by omega)]
    exact WOutX.ok rfl hrel hinv (Ext.refl _) (EViewExt.refl _) rfl rfl
  | succ k ih =>
    intro pers st lst fuel args i h o hn hrel hinv hfrozen he hargs hrun
    have hlt : i.val < args.val.length := by omega
    rw [arena.expr_ops.inst_lams_at_from] at hrun
    rw [if_neg (show ¬ (i ≥ alloc.vec.Vec.len args) from by
      show ¬ (args.val.length ≤ i.val); omega)] at hrun
    rw [listFrom_cons args i hlt]
    simp only [instLamsAt]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp he
    rw [run_bind_of (view_run_some hv)]
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htg := eidx_tag_abs ht
    by_cases hF : t = arena.handle.ETAG_LAM
    · rw [if_pos hF] at hrun
      obtain ⟨ob, hob, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨dom, body, mb, hobe, hvF, -, hbR⟩ := view_bind_lam hrel htg hF he hob
      rw [hvF] at hv
      simp only [Option.some.injEq] at hv
      subst hv
      rw [hobe] at hrun
      obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hb1, hval1⟩ := ExprOps.vecIndexAt he1
      obtain ⟨a, ha, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hae : a = args.val[i.val] := by rw [dupId_eidx _ _ ha, hval1]
      obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r1, st1⟩ := p1
      have haR : EResolves lst (absEIdx a) := by
        rw [hae]; exact hargs _ (mem_drop_here hlt)
      have hstep := instantiate1_fast_wout hrel hinv hfrozen hbR haR hp1
      rw [show absU (0#u64 : Std.U64) = 0 from rfl, hae] at hstep
      cases hr1 : r1 with
      | Err er =>
        rw [hr1] at hrun hstep
        rw [← Result.ok_injective hrun]
        exact WOutX.err_bind (hstep.err rfl)
      | Ok b =>
        rw [hr1] at hrun hstep
        obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hres1, hmono1, hfl1, hfl2, -⟩ :=
          hstep.dest
        refine WOutX.bind hx1 hext1 hmono1 hfl1 hfl2 ?_
        have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
          intro hs; rw [hfl2]; exact hfrozen (hfl1 ▸ hs)
        obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi3v : i3.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi3; simpa using this
        obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r2, st2⟩ := p2
        have hrec := ih (i := i3) (by omega) hrel1 hinv1 hfroz1 hres1
          (fun x hx => hmono1.res (hargs x (mem_drop_succ hlt (hi3v ▸ hx)))) hp2
        simp only [absEIdxListFrom, hi3v] at hrec
        cases hr2 : r2 with
        | Err er =>
          rw [hr2] at hrun hrec
          rw [← Result.ok_injective hrun]
          exact WOutX.err_bind hrec
        | Ok o1 =>
          rw [hr2] at hrun hrec
          obtain ⟨lst2, hx2, hrel2, hinv2, hext2, hmono2, hfl3, hfl4⟩ := hrec.dest
          rw [run_bind_of hx2]
          cases ho1 : o1 with
          | none =>
            rw [ho1] at hrun
            rw [← Result.ok_injective hrun]
            exact WOutX.ok rfl hrel2 hinv2 hext2 hmono2 hfl3 hfl4
          | some pp =>
            rw [ho1] at hrun
            obtain ⟨vv, e2⟩ := pp
            obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            rw [← Result.ok_injective hrun]
            refine WOutX.ok ?_ hrel2 hinv2 hext2 hmono2 hfl3 hfl4
            show _ = Except.ok (some (absEIdxList v1, absEIdx e2), lst2)
            rw [show absEIdxList v1 = absEIdx dom :: absEIdxList vv from
              ExprOps.cons_eidx_refines hv1]
            rfl
    · rw [if_neg hF] at hrun
      rw [← Result.ok_injective hrun]
      have hnf := view_not_lam htg hF hv
      cases v with
      | lam ty b m => exact absurd rfl (hnf ty b m)
      | _ => exact WOutX.ok rfl hrel hinv (Ext.refl _) (EViewExt.refl _) rfl rfl

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

/-! ## `bvarRange` — the tier's first INTERNING walk, and the keying measurement

**The one walk of this file that finding 14 fully unblocks.**  `bvarRange`
interns `bvar` nodes and nothing else, so its leaf wrapper
(`intern_e_bvar_run`) has no `hchild` at all (a `bvar` has no children) and,
after this round, no `hcap` either — leaving `hfrozen` as the only side
condition, which `intern_e_bvar_flags` carries across a step.  Every other
interning walk of this file descends into a node WITH children and is blocked
on §6's finding 16.

Two local names, because `ExprOps/Read.lean` is not imported here:
`aout_err_bind` is its `aout_err_bind`, and `cons_eidx_list` is
`ExprOps/Pure.lean`'s `cons_eidx_refines` at this file's own list
abstraction (`absEIdxList` here, `absEIdxL` there — P5-0 §9's first small
merge, still owed).

**The keying measurement** task #97-P5-3 round 3 §6 reports was taken on this
lemma: the four leaf closings below against `rust_grind2` over a keyed leaf
vocabulary.  Keying LOSES, and the section says why. -/

/-- `Pure.lean`'s `cons_eidx_refines`, at this file's list abstraction. -/
theorem cons_eidx_list {a : arena.handle.EIdx}
    {xs r : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.expr_ops.cons_eidx a xs = ok r) :
    absEIdxList r = absEIdx a :: absEIdxList xs := ExprOps.cons_eidx_refines h

private theorem bvar_range_aux (p : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {m_i n k : Std.U64} {o},
      n.val = p → AStateRel pers st lst → AStateInv pers st →
      (st.store.shared_on = true → st.store.scratch_on = true) →
      arena.expr_ops.bvar_range pers st m_i n k = ok o →
      Sim absEIdxList (fun _ => True) pers lst o
        (bvarRange (absU m_i) (absU n) (absU k)) := by
  induction p with
  | zero =>
    intro pers st lst m_i n k o hn hrel hinv hfrozen hrun
    rw [arena.expr_ops.bvar_range] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : n = 0#u64)] at hrun
    have ho := Result.ok_injective hrun
    show AOut absEIdxList (fun _ => True) pers lst o.1 o.2 _
    rw [← ho, show absU n = 0 from hn]
    refine AOut.ok (lst' := lst) ?_ hrel hinv (Ext.refl _) trivial
    show (bvarRange (absU m_i) 0 (absU k)).run lst
      = .ok (absEIdxList (alloc.vec.Vec.new arena.handle.EIdx), lst)
    rw [bvarRange]
    simp only [absEIdxList, alloc.vec.Vec.new, List.map_nil]
    rfl
  | succ q ih =>
    intro pers st lst m_i n k o hn hrel hinv hfrozen hrun
    rw [arena.expr_ops.bvar_range] at hrun
    have hne : ¬ (n = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, st1⟩ := p1
    have hidx : absU i1 = absU m_i - 1 - absU k := by
      rw [sub_nat_val hi1, sub_nat_val hi]; rfl
    have hsim := intern_e_bvar_run hrel hinv hfrozen i1 hp1
    have hflags := intern_e_bvar_flags hrel hinv hfrozen hp1
    show AOut absEIdxList (fun _ => True) pers lst o.1 o.2 _
    rw [show absU n = q + 1 from hn, bvarRange]
    rw [hidx] at hsim
    simp only [Arena.internBVarE] at hsim
    cases hr : r with
    | Err e =>
      have ho := Result.ok_injective (hr ▸ hrun)
      rw [← ho]
      exact aout_err_bind (hr ▸ hsim)
    | Ok b =>
      rw [hr] at hrun
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p2, hp2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r1, st2⟩ := p2
      obtain ⟨lst1, hy1, hrel1, hinv1, hext1, -⟩ := (hr ▸ hsim : AOut _ _ _ _ (.Ok b) _ _)
      rw [StateT.run_bind, hy1]
      have hi2v : i2.val = q := by
        have h1 := (ConRon.Refine.Nat.usub_val hi2).2
        rw [h1, hn]; rfl
      have hi3v : absU i3 = absU k + 1 := by
        have h1 := ConRon.Refine.Nat.uadd_val hi3
        simpa using h1
      have hfroz1 : st1.store.shared_on = true → st1.store.scratch_on = true := by
        intro hs
        have h1 : st1.store.shared_on = st.store.shared_on := hflags.1
        have h2 : st1.store.scratch_on = st.store.scratch_on := hflags.2
        rw [h2]; exact hfrozen (h1 ▸ hs)
      have hrec := ih (st := st1) (lst := lst1) hi2v hrel1 hinv1 hfroz1 hp2
      rw [show absU i2 = q from hi2v, hi3v] at hrec
      show AOut absEIdxList (fun _ => True) pers lst o.1 o.2
        ((do let rest ← bvarRange (absU m_i) q (absU k + 1)
             pure (absEIdx b :: rest)).run lst1)
      cases hr1 : r1 with
      | Err e =>
        have ho := Result.ok_injective (hr1 ▸ hrun)
        rw [← ho]
        exact aout_err_bind (hr1 ▸ hrec)
      | Ok rest =>
        rw [hr1] at hrun
        obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have ho := Result.ok_injective hrun
        obtain ⟨lst2, hy2, hrel2, hinv2, hext2, -⟩ :=
          (hr1 ▸ hrec : AOut _ _ _ _ (.Ok rest) _ _)
        rw [← ho]
        refine AOut.ok (lst' := lst2) ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
        rw [StateT.run_bind, hy2, cons_eidx_list hv]
        rfl

/-- `Arena/ExprOps.lean:1318 bvarRange` — the Rust's `Vec` is built with
`cons_eidx` on the way out, so the two orders agree and the abstraction is
`absEIdxList` with no reversal. -/
theorem bvar_range_refines {pers st lst} {m_i n k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfrozen : st.store.shared_on = true → st.store.scratch_on = true)
    (hrun : arena.expr_ops.bvar_range pers st m_i n k = ok o) :
    Sim absEIdxList (fun _ => True) pers lst o
      (bvarRange (absU m_i) (absU n) (absU k)) :=
  bvar_range_aux n.val rfl hrel hinv hfrozen hrun

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

/-! ## The port's two `Nat` scalars

`aout_err_bind` and `aout_rebase` now come from `ExprOps/Read.lean`, which
this file imports (task #97-P5-0 §9's owed merge, paid here). -/


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

/-! ### Task #97-P5-Mut's rows -/

/-- info: 'ConRon.Refine2.intern_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_resolves

/-- info: 'ConRon.Refine2.WOutE.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WOutE.bind

/-- info: 'ConRon.Refine2.intern_e_app_res' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_e_app_res

/-- info: 'ConRon.Refine2.mkAppNFrom_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mkAppNFrom_eq

/-- info: 'ConRon.Refine2.mk_app_n_from_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mk_app_n_from_refines

/-- info: 'ConRon.Refine2.mk_app_n_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mk_app_n_refines

/-- info: 'ConRon.Refine2.intern_rebuilt_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intern_rebuilt_refines

end ConRon.Refine2
