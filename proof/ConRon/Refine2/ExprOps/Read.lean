/-
# `ConRon.Refine2.ExprOps.Read` — Theorem 2 for `expr_ops`' READ-ONLY slice

**Deliverable 2 of task #97 P5, the thirty-three functions of
`crates/con-ron-core/src/arena/expr_ops.rs` that take `st : &AState`** — a
SHARED reference, so they read the store and never append.  The Rust's
post-state is its pre-state, which is why every statement below is `AOut`
(or `SimR`) at the *same* `st` on both sides and its `Ext` conjunct is
`Ext.refl`.

**CLOSED, end to end (task #97-P5-3).**  The statements were P5-0's; the
store-reader inversion layer they waited on landed at tasks #97-P5-1 and
#97-P5-2, and this file is now sorry-free.  Two of P5-0's statements had to
be CORRECTED on the way — finding 1's `StoreWF` is `EResolves` alone at the
four one-node readers (P5-2 §10's argument, mechanised below as
`estore_view_tagOf`), and `FOut`'s accumulator is the twin's list REVERSED
(finding 12, below).

## Three findings this file had to absorb, and they are DESIGN.md's business

**1. The Rust tests the handle's TAG where the twin reads the VIEW, at
nine of these thirty-three — and that makes the naive statement FALSE.**
Task #97-LC's ledger row for #97-P6-13 says the tag test is absorbed "under
the brief's own rule — on a well-formed store `h.tag == ETag.C` and `match ←
view h with | .C .. | _` are the same clause … the two differ only on a
DANGLING handle, which `StoreWF` excludes", and that the twin "nonetheless
spells the tag dispatch at the seven hottest walks … the other ~60 `if let`
sites keep `match ← view`".  Nine of those sites are in this slice
(`is_lam`, `lam_pw`, `forall_pw`, `fvar_type_d`, `strip_lams`, `strip_pis`,
`pi_result`, `pi_arity`, and `get_app_fn`/`get_app_args_go`'s `else` arm —
those last two spell the tag on BOTH sides and are fine), and at each the
divergence is not symmetric: on a dangling handle whose tag is *not* the one
tested, **the Rust answers `Ok` and the twin THROWS**.  Theorem 2's success
arm is exactly "Rust `Ok` ⇒ twin `ok`", so those statements are unprovable
without the excluded-middle hypothesis made explicit.  It is made explicit
here as `StoreWF lst.store` plus `EResolves lst h` — task #97s's template
rule 4 ("'the subject denotes' is an `isSome`, never a named `Expr`") at the
arena's own `view`.  **This is a hypothesis Theorem 1 owes and the ledger row
did not name.**

**2. Three walks thread their memo as an argument-and-result pair, so
`AOut` cannot state them.**  `AOut`'s `A : α → β` is a FUNCTION and the
abstraction of a `ron::HashMap2` is a RELATION
(`Refine2/AbsStore.lean`'s note), so `wscoped_b_go`, `fvar_leaves_go`,
`leaves_sub_go` and their five companions get `WOut` / `FOut` / `LOut` below:
`AOut` with the twin's post-MEMO existentially quantified beside its
post-state.  This is `RefineOld/State.lean`'s `Out` shape one level up and
costs three definitions once.

**3. `fvar_leaves_go`'s `seen` set is `HashMap<EIdx, bool>` in the Rust and
`Std.HashMap EIdx Unit` in the twin**, so what is related is MEMBERSHIP and
not the value (`SeenRel`).  A `Unit`-valued table has one inhabitant per key;
the Rust stores `true` at every key it inserts and never reads the value
(`fvl_seen` tests `is_some`).  Absorbed, and worth a ledger line.

## The six Rust-only splits

`wscoped_b_{node,two}`, `fvar_leaves_{node,two}` and `leaves_sub_{node,two}`
have **no named twin**: they are the fifteen Rust-only splits task #97-P6-2's
ledger absorbed, made so that "the `view`'s loans are dead at the memo's
join" (extraction rule 5).  The `_two` forms are three lines of the twin's own
arm and are stated inline, which is `Refine/README.md`'s "one equation per
inlined fragment" rule; the `_node` forms are the whole arm dispatch, so each
gets a local `*NodeSpec` transcription of the twin's `match` plus the
`*_unfold` equation tying it back to the twin — which is the one genuinely
owed lemma of this file that is not a `Specs.lean` primitive.
-/
import ConRon.Refine2.Specs
import ConRon.Refine2.ExprOps.Pure
import ConRon.Arena.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.ExprOps

open ConRon.Arena
open ConRon.Refine2
open ConRon.Refine.HashMap2 (Inv RelOn toFun)
open ConLeche (fvarOfData)

/-! ## The result abstractions this slice needs -/

/-- A `Vec<EIdx>` result as the twin's `List EIdx` (`get_app_args`). -/
def absEIdxList (v : alloc.vec.Vec arena.handle.EIdx) : List EIdx :=
  v.val.map absEIdx

/-- A `Vec<(u64, EIdx)>` leaf list as the twin's `List (Nat × EIdx)`. -/
def absLeaves (v : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) :
    List (Nat × EIdx) :=
  v.val.map fun p => (absU p.1, absEIdx p.2)

/-- A `Vec<(EIdx, BinderMeta)>` telescope as the twin's
`List (EIdx × BinderMeta)` (`strip_lams`, `strip_pis`). -/
def absBinders (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    List (EIdx × ConLeche.BinderMeta) :=
  v.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)

/-- `strip_lams`/`strip_pis`' whole answer. -/
def absStrip
    (o : Option ((alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) ×
      arena.handle.EIdx)) :
    Option (List (EIdx × ConLeche.BinderMeta) × EIdx) :=
  o.map fun p => (absBinders p.1, absEIdx p.2)

/-- `lam_pw`/`forall_pw`' answer. -/
def absPwOpt (o : Option kernel.prop_when.PropWhen) : Option ConLeche.PropWhen :=
  o.map ConRon.Refine.absPropWhen

/-- `result_sort`'s answer. -/
def absLIdxOpt (o : Option arena.handle.LIdx) : Option LIdx := o.map absLIdx

/-! ## "The handle resolves"

Finding 1's hypothesis.  `EResolves` is task #97s's template rule 4 at the
arena's `view`: an `isSome`, not a named view, so that a side goal is
metavariable-free.  `StoreWF` is what carries it to the children — `EWFAt`'s
`childOK` clause — and is `Arena/WF.lean`'s own predicate, so nothing new is
assumed here that Theorem 1 does not already establish. -/

/-- The handle decodes in the twin's store: the state the Rust's tag-first
dispatch and the twin's view-first dispatch agree on. -/
def EResolves (lst : AState) (h : EIdx) : Prop := (lst.store.view h).isSome = true

/-! ## The memo relations (finding 2, and finding 3 for `SeenRel`) -/

/-- `wscoped_b_go`'s memo, keyed on `(handle, depth)`. -/
def WMemoRel (rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
    (lm : Std.HashMap (EIdx × Nat) Bool) : Prop :=
  RelOn (fun _ => True) rm lm absEIdxNat id ∧
    Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm

/-- `leaves_sub_go`'s memo, keyed on the handle alone (`bl` is fixed for the
call, which is why it is not in the key). -/
def LMemoRel (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (lm : Std.HashMap EIdx Bool) : Prop :=
  RelOn (fun _ => True) rm lm absEIdx id ∧
    Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rm

/-- `fvar_leaves_go`'s `seen` set.  **Membership, not value** (finding 3): the
Rust's table is `bool`-valued and the twin's `Unit`-valued, and no reader
looks at either value — which is what `RelOn` at the value abstraction
`fun _ => ()` says, and stating it that way (rather than as an `isSome`
agreement) is what lets `Refine/HashMap2WF.lean`'s kit apply unchanged. -/
def SeenRel (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (lm : Std.HashMap EIdx Unit) : Prop :=
  RelOn (fun _ => True) rm lm absEIdx (fun _ => ()) ∧
    Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rm

/-! ## The three memo-threading outcome shapes (finding 2) -/

/-- The outcome of a `(Bool × memo)`-returning walk keyed on `(handle, depth)`. -/
def WOut (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result (Bool × ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
      kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError ((Bool × Std.HashMap (EIdx × Nat) Bool) × AState)) :
    Prop :=
  match o with
  | .Ok r => ∃ m' lst', x = .ok ((r.1, m'), lst') ∧ WMemoRel r.2 m' ∧
      AStateRel pers st' lst' ∧ AStateInv pers st' ∧ Ext lst.store lst'.store
  | .Err e => AErrSim e x

/-- The outcome of a `(Bool × memo)`-returning walk keyed on the handle. -/
def LOut (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result (Bool × ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError ((Bool × Std.HashMap EIdx Bool) × AState)) :
    Prop :=
  match o with
  | .Ok r => ∃ m' lst', x = .ok ((r.1, m'), lst') ∧ LMemoRel r.2 m' ∧
      AStateRel pers st' lst' ∧ AStateInv pers st' ∧ Ext lst.store lst'.store
  | .Err e => AErrSim e x

/-- The outcome of `fvar_leaves_go`'s accumulator-and-`seen` pair.

**Finding 12 (this round): the port's accumulator is the twin's list
REVERSED, and the statement has to say so.**  `fvar_leaves_go` pushes where
the twin conses — the port's own doc comment says "the two lists are each
other's reverse" and explains why (a `Vec` has no cons, and `leaf_mem`, the
only reader, is order blind).  P5-0 stated this group at `absLeaves r.1`,
which is false; it is `(absLeaves r.1).reverse`.  The same correction goes to
`fvar_leaves_fast_refines`, which P5-0 had "closed" against the wrong
statement (vacuously, off the `sorry` below it). -/
def FOut (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result ((alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) ×
      ron.hashmap2.HashMap2 arena.handle.EIdx Bool) kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError
      ((List (Nat × EIdx) × Std.HashMap EIdx Unit) × AState)) : Prop :=
  match o with
  | .Ok r => ∃ s' lst', x = .ok (((absLeaves r.1).reverse, s'), lst') ∧
      SeenRel r.2 s' ∧
      AStateRel pers st' lst' ∧ AStateInv pers st' ∧ Ext lst.store lst'.store
  | .Err e => AErrSim e x

/-! ## The `O(1)` derived-word reads

Three functions, and they are the three of this slice that return a bare
`bool` rather than a `Result<_, CheckError>`: they read the derived column and
cannot fail, so `SimR` — the read-only shape, no error arm — is what states
them. -/

/-- `inst_list_cutoff` is the twin's `instListCutoff`: `bvarB < satRange &&
bvarB ≤ d` off the packed word.  **Waits on `Specs.lean`'s `derivedE`**, and
on `Refine/Expr.lean`'s `bvar_of_data_val` / `sat_range` for the arithmetic. -/
theorem inst_list_cutoff_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {h : arena.handle.EIdx}
    {k : Std.U64} {o : Bool}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.inst_list_cutoff pers st h k = ok o) :
    SimR id lst o (instListCutoff (absEIdx h) (absU k)) := by
  rw [arena.expr_ops.inst_list_cutoff] at hrun
  obtain ⟨der, hder, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨sr, hsr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.monad.derived_e] at hder
  obtain ⟨hbv, -, -⟩ := derObsE_fields (estore_derived_abs hrel.store hder)
  have hbb := ConRon.Refine.Expr.bvar_of_data_val hb
  have hsrv := ConRon.Refine.Expr.sat_range_val hsr
  have hbn : (ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat = b.val := by
    rw [hbv, hbb]
  show (instListCutoff (absEIdx h) (absU k)).run lst = .ok (o, lst)
  rw [show (instListCutoff (absEIdx h) (absU k)).run lst
      = .ok (decide ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat
                < ConLeche.satRange) &&
          decide ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat ≤ absU k),
        lst) from rfl]
  split at hrun <;> rename_i hlt <;> simp only [Result.ok.injEq] at hrun <;> rw [← hrun]
  · have h1 : (ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat
        < ConLeche.satRange := by rw [hbn, ← hsrv]; exact hlt
    simp only [h1, decide_true, Bool.true_and]
    have h2 : ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat ≤ absU k)
        = (b ≤ k) := by
      rw [hbn]
      exact propext ⟨fun x => by scalar_tac, fun x => by scalar_tac⟩
    simp only [h2]
  · have h1 : ¬ ((ConLeche.bvarOfData (lst.store.derived (absEIdx h))).toNat
        < ConLeche.satRange) := by rw [hbn, ← hsrv]; simpa using hlt
    simp [h1]

/-- `lidx_has_param` is the twin's `LIdx.hasParam`: the level store's own
`hasParam` bit, off `derivedL` — the one field of a level's derived record
that `derObsL` keeps. -/
theorem lidx_has_param_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {h : arena.handle.LIdx} {o : Bool}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lidx_has_param pers st h = ok o) :
    SimR id lst o (LIdx.hasParam (absLIdx h)) := by
  rw [arena.expr_ops.lidx_has_param] at hrun
  obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨v, hv, hobs⟩ := derived_l_run hrel hl
  have hveq : v = lst.store.lder (absLIdx h) := by
    have : (Arena.derivedL (absLIdx h)).run lst
        = .ok (lst.store.lder (absLIdx h), lst) := rfl
    rw [this] at hv
    exact ((Prod.mk.injEq _ _ _ _ ▸ (Except.ok.injEq _ _ ▸ hv)).1).symm
  simp only [Result.ok.injEq] at hrun
  show (LIdx.hasParam (absLIdx h)).run lst = .ok (o, lst)
  rw [show (LIdx.hasParam (absLIdx h)).run lst
      = .ok ((lst.store.lder (absLIdx h)).hasParam, lst) from rfl, ← hrun,
    ← hveq]
  exact congrArg (fun x => Except.ok (x, lst)) hobs

/-- `eidx_has_level_param` is the twin's `EIdx.hasLevelParam`: the `hasLP` bit
of the packed derived word, which is `derObsE`'s third component. -/
theorem eidx_has_level_param_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {h : arena.handle.EIdx} {o : Bool}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.eidx_has_level_param pers st h = ok o) :
    SimR id lst o (EIdx.hasLevelParam (absEIdx h)) := by
  rw [arena.expr_ops.eidx_has_level_param] at hrun
  obtain ⟨d, hd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.monad.derived_e] at hd
  obtain ⟨-, -, hlp⟩ := derObsE_fields (estore_derived_abs hrel.store hd)
  have hbb := ConRon.Refine.Expr.lp_of_data_val hrun
  show (EIdx.hasLevelParam (absEIdx h)).run lst = .ok (o, lst)
  rw [show (EIdx.hasLevelParam (absEIdx h)).run lst
      = .ok (ConLeche.lpOfData (lst.store.derived (absEIdx h)), lst) from rfl,
    hlp, hbb]
  by_cases hc : d.val % 2 = 1 <;> simp [hc]

/-! ## The unmemoized `view` walks

Both sides read the view at every node, so these line up clause for clause and
need no resolution hypothesis: where the twin's `view` throws, the Rust's does
too, at the same `Internal` kind.  Each is a fuel induction with the ~12-line
shape step of task #97s round 3, and the twin's arms are `mutual` `def`s
(task #97-P3-1's split) where the Rust inlines them, so the shape step is the
peel plus one `rw` at the arm.

Two combinators carry the whole cost of the chain: `aout_err_bind` (the
callee threw, so the bind throws, whatever the base states are) and
`aout_rebase` (`Ext` composed across a two-child arm). -/

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

private theorem size_b_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      arena.expr_ops.size_b pers st fuel h = ok o →
      AOut absU (fun _ => True) pers lst o st
        ((sizeB (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.size_b] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((sizeB (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, sizeB_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.size_b] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hv := view_run hrel hinv hr
    rw [show absU fuel = m + 1 from hn, sizeB_succ]
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hv
      have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact aout_err_bind hv
    | Ok ev =>
      rw [hrc] at hrun hv
      obtain ⟨lst0, hx, hrel0, hinv0, hext0, -⟩ := hv
      have hlst : lst0 = lst := view_run_state hx
      rw [hlst] at hx
      rw [StateT.run_bind, hx]
      cases ev with
      | BVar _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | FVar _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | «Sort» _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Const _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Lit _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | App f0 a0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := f0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeBArmApp m (absEIdx f0) (absEIdx a0)).run lst)
        rw [sizeBArmApp]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := a0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absU (fun _ => True) pers lst o st
            ((do let y ← sizeB m (absEIdx a0); pure (absU x1 + y + 1)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨j2, hj2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok j2 :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
            have e1 : absU j1 = absU x1 + absU y1 := ConRon.Refine.Nat.uadd_val hj1
            have e2 : absU j2 = absU j1 + 1 := ConRon.Refine.Nat.uadd_val hj2
            show Except.ok (absU x1 + absU y1 + 1, lst2) = _
            rw [e2, e1]
      | Lam ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeBArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
        rw [sizeBArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := b0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absU (fun _ => True) pers lst o st
            ((do let y ← sizeB m (absEIdx b0); pure (absU x1 + y + 1)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨j2, hj2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok j2 :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
            have e1 : absU j1 = absU x1 + absU y1 := ConRon.Refine.Nat.uadd_val hj1
            have e2 : absU j2 = absU j1 + 1 := ConRon.Refine.Nat.uadd_val hj2
            show Except.ok (absU x1 + absU y1 + 1, lst2) = _
            rw [e2, e1]
      | ForallE ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeBArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
        rw [sizeBArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := b0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absU (fun _ => True) pers lst o st
            ((do let y ← sizeB m (absEIdx b0); pure (absU x1 + y + 1)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨j2, hj2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok j2 :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
            have e1 : absU j1 = absU x1 + absU y1 := ConRon.Refine.Nat.uadd_val hj1
            have e2 : absU j2 = absU j1 + 1 := ConRon.Refine.Nat.uadd_val hj2
            show Except.ok (absU x1 + absU y1 + 1, lst2) = _
            rw [e2, e1]
      | LetE ty0 v0 b0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeBArmLet m (absEIdx ty0) (absEIdx v0) (absEIdx b0)).run lst)
        rw [sizeBArmLet]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := v0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absU (fun _ => True) pers lst o st
            ((do
              let y ← sizeB m (absEIdx v0)
              let z ← sizeB m (absEIdx b0)
              pure (absU x1 + y + z + 1)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨r3, hr3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hrec3 := ih (h := b0) hi1v hrel2 hinv2 hr3
            rw [show absU i1 = m from hi1v] at hrec3
            show AOut absU (fun _ => True) pers lst o st
              ((do
                let z ← sizeB m (absEIdx b0)
                pure (absU x1 + absU y1 + z + 1)).run lst2)
            cases hrc3 : r3 with
            | Err e =>
              rw [hrc3] at hrun hrec3
              have ho : (core.result.Result.Err e :
                  core.result.Result Std.U64 _) = o := Result.ok_injective hrun
              rw [← ho]
              exact aout_err_bind hrec3
            | Ok z1 =>
              rw [hrc3] at hrun hrec3
              obtain ⟨lst3, hx3, hrel3, hinv3, hext3, -⟩ := hrec3
              rw [StateT.run_bind, hx3]
              obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨j2, hj2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨j3, hj3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have ho : (core.result.Result.Ok j3 :
                  core.result.Result Std.U64 _) = o := Result.ok_injective hrun
              rw [← ho]
              refine AOut.ok ?_ hrel3 hinv3
                (Ext.trans hext1 (Ext.trans hext2 hext3)) trivial
              have e1 : absU j1 = absU x1 + absU y1 := ConRon.Refine.Nat.uadd_val hj1
              have e2 : absU j2 = absU j1 + absU z1 := ConRon.Refine.Nat.uadd_val hj2
              have e3 : absU j3 = absU j2 + 1 := ConRon.Refine.Nat.uadd_val hj3
              show Except.ok (absU x1 + absU y1 + absU z1 + 1, lst3) = _
              rw [e3, e2, e1]
      | Proj _ _ s0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := s0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeBArmProj m (absEIdx s0)).run lst)
        rw [sizeBArmProj]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok j1 :
              core.result.Result Std.U64 _) = o := Result.ok_injective hrun
          rw [← ho]
          refine AOut.ok ?_ hrel1 hinv1 hext1 trivial
          have e1 : absU j1 = absU x1 + 1 := ConRon.Refine.Nat.uadd_val hj1
          show Except.ok (absU x1 + 1, lst1) = _
          rw [e1]

private theorem size_f_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      arena.expr_ops.size_f pers st fuel h = ok o →
      AOut absU (fun _ => True) pers lst o st
        ((sizeF (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.size_f] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((sizeF (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, sizeF_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.size_f] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hv := view_run hrel hinv hr
    rw [show absU fuel = m + 1 from hn, sizeF_succ]
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hv
      have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact aout_err_bind hv
    | Ok ev =>
      rw [hrc] at hrun hv
      obtain ⟨lst0, hx, hrel0, hinv0, hext0, -⟩ := hv
      have hlst : lst0 = lst := view_run_state hx
      rw [hlst] at hx
      rw [StateT.run_bind, hx]
      cases ev with
      | BVar _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | FVar _ ty1 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty1) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeFArmFVar m (absEIdx ty1)).run lst)
        rw [sizeFArmFVar]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok j1 :
              core.result.Result Std.U64 _) = o := Result.ok_injective hrun
          rw [← ho]
          refine AOut.ok ?_ hrel1 hinv1 hext1 trivial
          have e1 : absU j1 = absU x1 + 1 := ConRon.Refine.Nat.uadd_val hj1
          show Except.ok (absU x1 + 1, lst1) = _
          rw [e1]
      | «Sort» _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Const _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Lit _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | App f0 a0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := f0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeFArmApp m (absEIdx f0) (absEIdx a0)).run lst)
        rw [sizeFArmApp]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := a0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absU (fun _ => True) pers lst o st
            ((do let y ← sizeF m (absEIdx a0); pure (absU x1 + y + 1)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨j2, hj2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok j2 :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
            have e1 : absU j1 = absU x1 + absU y1 := ConRon.Refine.Nat.uadd_val hj1
            have e2 : absU j2 = absU j1 + 1 := ConRon.Refine.Nat.uadd_val hj2
            show Except.ok (absU x1 + absU y1 + 1, lst2) = _
            rw [e2, e1]
      | Lam ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeFArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
        rw [sizeFArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := b0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absU (fun _ => True) pers lst o st
            ((do let y ← sizeF m (absEIdx b0); pure (absU x1 + y + 1)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨j2, hj2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok j2 :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
            have e1 : absU j1 = absU x1 + absU y1 := ConRon.Refine.Nat.uadd_val hj1
            have e2 : absU j2 = absU j1 + 1 := ConRon.Refine.Nat.uadd_val hj2
            show Except.ok (absU x1 + absU y1 + 1, lst2) = _
            rw [e2, e1]
      | ForallE ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeFArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
        rw [sizeFArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := b0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absU (fun _ => True) pers lst o st
            ((do let y ← sizeF m (absEIdx b0); pure (absU x1 + y + 1)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            obtain ⟨j2, hj2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok j2 :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
            have e1 : absU j1 = absU x1 + absU y1 := ConRon.Refine.Nat.uadd_val hj1
            have e2 : absU j2 = absU j1 + 1 := ConRon.Refine.Nat.uadd_val hj2
            show Except.ok (absU x1 + absU y1 + 1, lst2) = _
            rw [e2, e1]
      | LetE ty0 v0 b0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeFArmLet m (absEIdx ty0) (absEIdx v0) (absEIdx b0)).run lst)
        rw [sizeFArmLet]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := v0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absU (fun _ => True) pers lst o st
            ((do
              let y ← sizeF m (absEIdx v0)
              let z ← sizeF m (absEIdx b0)
              pure (absU x1 + y + z + 1)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result Std.U64 _) = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨r3, hr3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hrec3 := ih (h := b0) hi1v hrel2 hinv2 hr3
            rw [show absU i1 = m from hi1v] at hrec3
            show AOut absU (fun _ => True) pers lst o st
              ((do
                let z ← sizeF m (absEIdx b0)
                pure (absU x1 + absU y1 + z + 1)).run lst2)
            cases hrc3 : r3 with
            | Err e =>
              rw [hrc3] at hrun hrec3
              have ho : (core.result.Result.Err e :
                  core.result.Result Std.U64 _) = o := Result.ok_injective hrun
              rw [← ho]
              exact aout_err_bind hrec3
            | Ok z1 =>
              rw [hrc3] at hrun hrec3
              obtain ⟨lst3, hx3, hrel3, hinv3, hext3, -⟩ := hrec3
              rw [StateT.run_bind, hx3]
              obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨j2, hj2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨j3, hj3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have ho : (core.result.Result.Ok j3 :
                  core.result.Result Std.U64 _) = o := Result.ok_injective hrun
              rw [← ho]
              refine AOut.ok ?_ hrel3 hinv3
                (Ext.trans hext1 (Ext.trans hext2 hext3)) trivial
              have e1 : absU j1 = absU x1 + absU y1 := ConRon.Refine.Nat.uadd_val hj1
              have e2 : absU j2 = absU j1 + absU z1 := ConRon.Refine.Nat.uadd_val hj2
              have e3 : absU j3 = absU j2 + 1 := ConRon.Refine.Nat.uadd_val hj3
              show Except.ok (absU x1 + absU y1 + absU z1 + 1, lst3) = _
              rw [e3, e2, e1]
      | Proj _ _ s0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := s0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absU (fun _ => True) pers lst o st
          ((sizeFArmProj m (absEIdx s0)).run lst)
        rw [sizeFArmProj]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Std.U64 _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok j1 :
              core.result.Result Std.U64 _) = o := Result.ok_injective hrun
          rw [← ho]
          refine AOut.ok ?_ hrel1 hinv1 hext1 trivial
          have e1 : absU j1 = absU x1 + 1 := ConRon.Refine.Nat.uadd_val hj1
          show Except.ok (absU x1 + 1, lst1) = _
          rw [e1]

/-- An outcome measured from a later state is an outcome measured from an
earlier one, `Ext` composed. -/
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

private theorem has_fvar_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      arena.expr_ops.has_fvar pers st fuel h = ok o →
      AOut id (fun _ => True) pers lst o st
        ((hasFvar (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.has_fvar] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((hasFvar (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, hasFvar_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.has_fvar] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hv := view_run hrel hinv hr
    rw [show absU fuel = m + 1 from hn, hasFvar_succ]
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hv
      have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact aout_err_bind hv
    | Ok ev =>
      rw [hrc] at hrun hv
      obtain ⟨lst0, hx, hrel0, hinv0, hext0, -⟩ := hv
      have hlst : lst0 = lst := view_run_state hx
      rw [hlst] at hx
      rw [StateT.run_bind, hx]
      cases ev with
      | BVar _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | FVar _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | «Sort» _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Const _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Lit _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Proj _ _ s0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := s0) hi1v hrel hinv hrun
        rw [show absU i1 = m from hi1v] at hrec1
        exact hrec1
      | App f0 a0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := f0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((hasFvarArmApp m (absEIdx f0) (absEIdx a0)).run lst)
        rw [hasFvarArmApp]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then (pure true : AM Bool)
              else hasFvar m (absEIdx a0)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            have ho : (core.result.Result.Ok true :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have hrec2 := ih (h := a0) hi1v hrel1 hinv1 hrun
            rw [show absU i1 = m from hi1v] at hrec2
            exact aout_rebase hext1 hrec2
      | Lam ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((hasFvarArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
        rw [hasFvarArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then (pure true : AM Bool)
              else hasFvar m (absEIdx b0)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            have ho : (core.result.Result.Ok true :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have hrec2 := ih (h := b0) hi1v hrel1 hinv1 hrun
            rw [show absU i1 = m from hi1v] at hrec2
            exact aout_rebase hext1 hrec2
      | ForallE ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((hasFvarArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
        rw [hasFvarArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then (pure true : AM Bool)
              else hasFvar m (absEIdx b0)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            have ho : (core.result.Result.Ok true :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have hrec2 := ih (h := b0) hi1v hrel1 hinv1 hrun
            rw [show absU i1 = m from hi1v] at hrec2
            exact aout_rebase hext1 hrec2
      | LetE ty0 v0 b0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((hasFvarArmLet m (absEIdx ty0) (absEIdx v0) (absEIdx b0)).run lst)
        rw [hasFvarArmLet]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then (pure true : AM Bool)
              else do
                let y ← hasFvar m (absEIdx v0)
                if y then pure true else hasFvar m (absEIdx b0)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            have ho : (core.result.Result.Ok true :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial
          · simp only [Bool.not_eq_true] at hb
            subst hb
            obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hrec2 := ih (h := v0) hi1v hrel1 hinv1 hr2
            rw [show absU i1 = m from hi1v] at hrec2
            refine aout_rebase hext1 ?_
            show AOut id (fun _ => True) pers lst1 o st
              ((do
                let y ← hasFvar m (absEIdx v0)
                if y then pure true else hasFvar m (absEIdx b0)).run lst1)
            cases hrc2 : r2 with
            | Err e =>
              rw [hrc2] at hrun hrec2
              have ho : (core.result.Result.Err e :
                  core.result.Result Bool _) = o := Result.ok_injective hrun
              rw [← ho]
              exact aout_err_bind hrec2
            | Ok y1 =>
              rw [hrc2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
              rw [StateT.run_bind, hx2]
              show AOut id (fun _ => True) pers lst1 o st
                ((if y1 then (pure true : AM Bool)
                  else hasFvar m (absEIdx b0)).run lst2)
              by_cases hb2 : y1 = true
              · subst hb2
                have ho : (core.result.Result.Ok true :
                    core.result.Result Bool _) = o := Result.ok_injective hrun
                rw [← ho]
                exact AOut.ok rfl hrel2 hinv2 hext2 trivial
              · simp only [Bool.not_eq_true] at hb2
                subst hb2
                have hrec3 := ih (h := b0) hi1v hrel2 hinv2 hrun
                rw [show absU i1 = m from hi1v] at hrec3
                exact aout_rebase hext2 hrec3

private theorem wscoped_b_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel d : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      arena.expr_ops.wscoped_b pers st fuel d h = ok o →
      AOut id (fun _ => True) pers lst o st
        ((wscopedB (absU fuel) (absU d) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel d h o hn hrel hinv hrun
    rw [arena.expr_ops.wscoped_b] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((wscopedB (absU fuel) (absU d) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, wscopedB_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel d h o hn hrel hinv hrun
    rw [arena.expr_ops.wscoped_b] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hv := view_run hrel hinv hr
    rw [show absU fuel = m + 1 from hn, wscopedB_succ]
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hv
      have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact aout_err_bind hv
    | Ok ev =>
      rw [hrc] at hrun hv
      obtain ⟨lst0, hx, hrel0, hinv0, hext0, -⟩ := hv
      have hlst : lst0 = lst := view_run_state hx
      rw [hlst] at hx
      rw [StateT.run_bind, hx]
      cases ev with
      | BVar _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | «Sort» _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Const _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Lit _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | FVar idx0 ty0 =>
        have hrun2 : (if idx0 < d then
            (do
              let i ← fuel - 1#u64
              arena.expr_ops.wscoped_b pers st i idx0 ty0)
          else ok (core.result.Result.Ok false)) = ok o := hrun
        show AOut id (fun _ => True) pers lst o st
          ((if absU idx0 < absU d then wscopedB m (absU idx0) (absEIdx ty0)
            else pure false).run lst)
        by_cases hlt : idx0 < d
        · rw [if_pos hlt] at hrun2
          rw [if_pos (show absU idx0 < absU d from hlt)]
          obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun2
          have hi1v : i1.val = m := by
            have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
              (ConRon.Refine.Nat.usub_val hi1).2
            rw [h1, hn]; rfl
          have hrec1 := ih (h := ty0) (d := idx0) hi1v hrel hinv hrun
          rw [show absU i1 = m from hi1v] at hrec1
          exact hrec1
        · rw [if_neg hlt] at hrun2
          rw [if_neg (show ¬ (absU idx0 < absU d) from hlt)]
          have ho := Result.ok_injective hrun2
          rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Proj _ _ s0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := s0) (d := d) hi1v hrel hinv hrun
        rw [show absU i1 = m from hi1v] at hrec1
        exact hrec1
      | App f0 a0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := f0) (d := d) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((wscopedBArmApp m (absU d) (absEIdx f0) (absEIdx a0)).run lst)
        rw [wscopedBArmApp]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then wscopedB m (absU d) (absEIdx a0)
              else (pure false : AM Bool)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            have hrec2 := ih (h := a0) (d := d) hi1v hrel1 hinv1 hrun
            rw [show absU i1 = m from hi1v] at hrec2
            exact aout_rebase hext1 hrec2
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have ho : (core.result.Result.Ok false :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial
      | Lam ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) (d := d) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((wscopedBArmBind m (absU d) (absEIdx ty0) (absEIdx b0)).run lst)
        rw [wscopedBArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then wscopedB m (absU d) (absEIdx b0)
              else (pure false : AM Bool)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            have hrec2 := ih (h := b0) (d := d) hi1v hrel1 hinv1 hrun
            rw [show absU i1 = m from hi1v] at hrec2
            exact aout_rebase hext1 hrec2
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have ho : (core.result.Result.Ok false :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial
      | ForallE ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) (d := d) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((wscopedBArmBind m (absU d) (absEIdx ty0) (absEIdx b0)).run lst)
        rw [wscopedBArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then wscopedB m (absU d) (absEIdx b0)
              else (pure false : AM Bool)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            have hrec2 := ih (h := b0) (d := d) hi1v hrel1 hinv1 hrun
            rw [show absU i1 = m from hi1v] at hrec2
            exact aout_rebase hext1 hrec2
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have ho : (core.result.Result.Ok false :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial
      | LetE ty0 v0 b0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) (d := d) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((wscopedBArmLet m (absU d) (absEIdx ty0) (absEIdx v0)
            (absEIdx b0)).run lst)
        rw [wscopedBArmLet]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then do
                let y ← wscopedB m (absU d) (absEIdx v0)
                if y then wscopedB m (absU d) (absEIdx b0) else pure false
              else (pure false : AM Bool)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hrec2 := ih (h := v0) (d := d) hi1v hrel1 hinv1 hr2
            rw [show absU i1 = m from hi1v] at hrec2
            refine aout_rebase hext1 ?_
            show AOut id (fun _ => True) pers lst1 o st
              ((do
                let y ← wscopedB m (absU d) (absEIdx v0)
                if y then wscopedB m (absU d) (absEIdx b0)
                else pure false).run lst1)
            cases hrc2 : r2 with
            | Err e =>
              rw [hrc2] at hrun hrec2
              have ho : (core.result.Result.Err e :
                  core.result.Result Bool _) = o := Result.ok_injective hrun
              rw [← ho]
              exact aout_err_bind hrec2
            | Ok y1 =>
              rw [hrc2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
              rw [StateT.run_bind, hx2]
              show AOut id (fun _ => True) pers lst1 o st
                ((if y1 then wscopedB m (absU d) (absEIdx b0)
                  else (pure false : AM Bool)).run lst2)
              by_cases hb2 : y1 = true
              · subst hb2
                have hrec3 := ih (h := b0) (d := d) hi1v hrel2 hinv2 hrun
                rw [show absU i1 = m from hi1v] at hrec3
                exact aout_rebase hext2 hrec3
              · simp only [Bool.not_eq_true] at hb2
                subst hb2
                have ho : (core.result.Result.Ok false :
                    core.result.Result Bool _) = o := Result.ok_injective hrun
                rw [← ho]
                exact AOut.ok rfl hrel2 hinv2 hext2 trivial
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have ho : (core.result.Result.Ok false :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial

private theorem loose_bvars_bounded_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel k : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      arena.expr_ops.loose_bvars_bounded pers st fuel k h = ok o →
      AOut id (fun _ => True) pers lst o st
        ((looseBVarsBounded (absU fuel) (absU k) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel k h o hn hrel hinv hrun
    rw [arena.expr_ops.loose_bvars_bounded] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((looseBVarsBounded (absU fuel) (absU k) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, looseBVarsBounded_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel k h o hn hrel hinv hrun
    rw [arena.expr_ops.loose_bvars_bounded] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hv := view_run hrel hinv hr
    rw [show absU fuel = m + 1 from hn, looseBVarsBounded_succ]
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hv
      have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact aout_err_bind hv
    | Ok ev =>
      rw [hrc] at hrun hv
      obtain ⟨lst0, hx, hrel0, hinv0, hext0, -⟩ := hv
      have hlst : lst0 = lst := view_run_state hx
      rw [hlst] at hx
      rw [StateT.run_bind, hx]
      cases ev with
      | BVar i0 =>
        have ho : (core.result.Result.Ok (decide (i0 < k)) :
            core.result.Result Bool _) = o := Result.ok_injective hrun
        rw [← ho]
        refine AOut.ok ?_ hrel hinv (Ext.refl _) trivial
        show Except.ok (decide (absU i0 < absU k), lst) = _
        rfl
      | «Sort» _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Const _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Lit _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | FVar _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Proj _ _ s0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := s0) (k := k) hi1v hrel hinv hrun
        rw [show absU i1 = m from hi1v] at hrec1
        exact hrec1
      | App f0 a0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := f0) (k := k) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((looseBArmApp m (absU k) (absEIdx f0) (absEIdx a0)).run lst)
        rw [looseBArmApp]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then looseBVarsBounded m (absU k) (absEIdx a0)
              else (pure false : AM Bool)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            have hrec2 := ih (h := a0) (k := k) hi1v hrel1 hinv1 hrun
            rw [show absU i1 = m from hi1v] at hrec2
            exact aout_rebase hext1 hrec2
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have ho : (core.result.Result.Ok false :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial
      | Lam ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) (k := k) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((looseBArmBind m (absU k) (absEIdx ty0) (absEIdx b0)).run lst)
        rw [looseBArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then looseBVarsBounded m (absU k + 1) (absEIdx b0)
              else (pure false : AM Bool)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hk1v : absU k1 = absU k + 1 := ConRon.Refine.Nat.uadd_val hk1
            have hrec2 := ih (h := b0) (k := k1) hi1v hrel1 hinv1 hrun
            rw [show absU i1 = m from hi1v, hk1v] at hrec2
            exact aout_rebase hext1 hrec2
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have ho : (core.result.Result.Ok false :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial
      | ForallE ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) (k := k) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((looseBArmBind m (absU k) (absEIdx ty0) (absEIdx b0)).run lst)
        rw [looseBArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then looseBVarsBounded m (absU k + 1) (absEIdx b0)
              else (pure false : AM Bool)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hk1v : absU k1 = absU k + 1 := ConRon.Refine.Nat.uadd_val hk1
            have hrec2 := ih (h := b0) (k := k1) hi1v hrel1 hinv1 hrun
            rw [show absU i1 = m from hi1v, hk1v] at hrec2
            exact aout_rebase hext1 hrec2
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have ho : (core.result.Result.Ok false :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial
      | LetE ty0 v0 b0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) (k := k) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut id (fun _ => True) pers lst o st
          ((looseBArmLet m (absU k) (absEIdx ty0) (absEIdx v0)
            (absEIdx b0)).run lst)
        rw [looseBArmLet]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          show AOut id (fun _ => True) pers lst o st
            ((if x1 then do
                let y ← looseBVarsBounded m (absU k) (absEIdx v0)
                if y then looseBVarsBounded m (absU k + 1) (absEIdx b0)
                else pure false
              else (pure false : AM Bool)).run lst1)
          by_cases hb : x1 = true
          · subst hb
            obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hrec2 := ih (h := v0) (k := k) hi1v hrel1 hinv1 hr2
            rw [show absU i1 = m from hi1v] at hrec2
            refine aout_rebase hext1 ?_
            show AOut id (fun _ => True) pers lst1 o st
              ((do
                let y ← looseBVarsBounded m (absU k) (absEIdx v0)
                if y then looseBVarsBounded m (absU k + 1) (absEIdx b0)
                else pure false).run lst1)
            cases hrc2 : r2 with
            | Err e =>
              rw [hrc2] at hrun hrec2
              have ho : (core.result.Result.Err e :
                  core.result.Result Bool _) = o := Result.ok_injective hrun
              rw [← ho]
              exact aout_err_bind hrec2
            | Ok y1 =>
              rw [hrc2] at hrun hrec2
              obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
              rw [StateT.run_bind, hx2]
              show AOut id (fun _ => True) pers lst1 o st
                ((if y1 then looseBVarsBounded m (absU k + 1) (absEIdx b0)
                  else (pure false : AM Bool)).run lst2)
              by_cases hb2 : y1 = true
              · subst hb2
                obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have hk1v : absU k1 = absU k + 1 := ConRon.Refine.Nat.uadd_val hk1
                have hrec3 := ih (h := b0) (k := k1) hi1v hrel2 hinv2 hrun
                rw [show absU i1 = m from hi1v, hk1v] at hrec3
                exact aout_rebase hext2 hrec3
              · simp only [Bool.not_eq_true] at hb2
                subst hb2
                have ho : (core.result.Result.Ok false :
                    core.result.Result Bool _) = o := Result.ok_injective hrun
                rw [← ho]
                exact AOut.ok rfl hrel2 hinv2 hext2 trivial
          · simp only [Bool.not_eq_true] at hb
            subst hb
            have ho : (core.result.Result.Ok false :
                core.result.Result Bool _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel1 hinv1 hext1 trivial

theorem absLeaves_eq (v : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) :
    absLeaves v = absFvlL v := rfl

private theorem fvar_leaves_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      arena.expr_ops.fvar_leaves pers st fuel h = ok o →
      AOut absLeaves (fun _ => True) pers lst o st
        ((fvarLeaves (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.fvar_leaves] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((fvarLeaves (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, fvarLeaves_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.fvar_leaves] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hv := view_run hrel hinv hr
    rw [show absU fuel = m + 1 from hn, fvarLeaves_succ]
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hv
      have ho : (core.result.Result.Err e :
          core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact aout_err_bind hv
    | Ok ev =>
      rw [hrc] at hrun hv
      obtain ⟨lst0, hx, hrel0, hinv0, hext0, -⟩ := hv
      have hlst : lst0 = lst := view_run_state hx
      rw [hlst] at hx
      rw [StateT.run_bind, hx]
      cases ev with
      | BVar _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | «Sort» _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Const _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Lit _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]; exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Proj _ _ s0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := s0) hi1v hrel hinv hrun
        rw [show absU i1 = m from hi1v] at hrec1
        exact hrec1
      | FVar idx0 ty0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absLeaves (fun _ => True) pers lst o st
          ((fvarLeavesArmFVar m (absU idx0) (absEIdx ty0)).run lst)
        rw [fvarLeavesArmFVar]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e :
              core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
              = o := Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok rest1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok v1 :
              core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
              = o := Result.ok_injective hrun
          rw [← ho]
          refine AOut.ok ?_ hrel1 hinv1 hext1 trivial
          have hee : e1 = ty0 := dupId_eidx ty0 e1 he1
          have hov : out1.val = [(idx0, e1)] := ConRon.Refine.push_new_val hout1
          have hres : absLeaves v1 = (absU idx0, absEIdx ty0) :: absLeaves rest1 := by
            rw [absLeaves_eq, fvl_copy_from_refines hv1]
            simp [absFvlL, absLeaves, hov, hee]
          show Except.ok ((absU idx0, absEIdx ty0) :: absLeaves rest1, lst1) = _
          rw [hres]
      | App f0 a0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := f0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absLeaves (fun _ => True) pers lst o st
          ((fvarLeavesArmApp m (absEIdx f0) (absEIdx a0)).run lst)
        rw [fvarLeavesArmApp]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e :
              core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
              = o := Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := a0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absLeaves (fun _ => True) pers lst o st
            ((do
              let y ← fvarLeaves m (absEIdx a0)
              pure (absLeaves x1 ++ y)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
                = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok v1 :
                core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
                = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
            show Except.ok (absLeaves x1 ++ absLeaves y1, lst2) = _
            rw [absLeaves_eq v1, fvl_append_refines hv1]
            rfl
      | Lam ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absLeaves (fun _ => True) pers lst o st
          ((fvarLeavesArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
        rw [fvarLeavesArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e :
              core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
              = o := Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := b0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absLeaves (fun _ => True) pers lst o st
            ((do
              let y ← fvarLeaves m (absEIdx b0)
              pure (absLeaves x1 ++ y)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
                = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok v1 :
                core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
                = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
            show Except.ok (absLeaves x1 ++ absLeaves y1, lst2) = _
            rw [absLeaves_eq v1, fvl_append_refines hv1]
            rfl
      | ForallE ty0 b0 mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := ty0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absLeaves (fun _ => True) pers lst o st
          ((fvarLeavesArmBind m (absEIdx ty0) (absEIdx b0)).run lst)
        rw [fvarLeavesArmBind]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e :
              core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
              = o := Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := b0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absLeaves (fun _ => True) pers lst o st
            ((do
              let y ← fvarLeaves m (absEIdx b0)
              pure (absLeaves x1 ++ y)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
                = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok v1 :
                core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
                = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
            show Except.ok (absLeaves x1 ++ absLeaves y1, lst2) = _
            rw [absLeaves_eq v1, fvl_append_refines hv1]
            rfl
      | LetE t0 v0 b0 =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec1 := ih (h := t0) hi1v hrel hinv hr1
        rw [show absU i1 = m from hi1v] at hrec1
        show AOut absLeaves (fun _ => True) pers lst o st
          ((fvarLeavesArmLet m (absEIdx t0) (absEIdx v0) (absEIdx b0)).run lst)
        rw [fvarLeavesArmLet]
        cases hrc1 : r1 with
        | Err e =>
          rw [hrc1] at hrun hrec1
          have ho : (core.result.Result.Err e :
              core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
              = o := Result.ok_injective hrun
          rw [← ho]
          exact aout_err_bind hrec1
        | Ok x1 =>
          rw [hrc1] at hrun hrec1
          obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hrec1
          rw [StateT.run_bind, hx1]
          obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hrec2 := ih (h := v0) hi1v hrel1 hinv1 hr2
          rw [show absU i1 = m from hi1v] at hrec2
          show AOut absLeaves (fun _ => True) pers lst o st
            ((do
              let y ← fvarLeaves m (absEIdx v0)
              let z ← fvarLeaves m (absEIdx b0)
              pure (absLeaves x1 ++ y ++ z)).run lst1)
          cases hrc2 : r2 with
          | Err e =>
            rw [hrc2] at hrun hrec2
            have ho : (core.result.Result.Err e :
                core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
                = o := Result.ok_injective hrun
            rw [← ho]
            exact aout_err_bind hrec2
          | Ok y1 =>
            rw [hrc2] at hrun hrec2
            obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hrec2
            rw [StateT.run_bind, hx2]
            obtain ⟨r3, hr3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hrec3 := ih (h := b0) hi1v hrel2 hinv2 hr3
            rw [show absU i1 = m from hi1v] at hrec3
            show AOut absLeaves (fun _ => True) pers lst o st
              ((do
                let z ← fvarLeaves m (absEIdx b0)
                pure (absLeaves x1 ++ absLeaves y1 ++ z)).run lst2)
            cases hrc3 : r3 with
            | Err e =>
              rw [hrc3] at hrun hrec3
              have ho : (core.result.Result.Err e :
                  core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
                  = o := Result.ok_injective hrun
              rw [← ho]
              exact aout_err_bind hrec3
            | Ok z1 =>
              rw [hrc3] at hrun hrec3
              obtain ⟨lst3, hx3, hrel3, hinv3, hext3, -⟩ := hrec3
              rw [StateT.run_bind, hx3]
              obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨v2, hv2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have ho : (core.result.Result.Ok v2 :
                  core.result.Result (alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) _)
                  = o := Result.ok_injective hrun
              rw [← ho]
              refine AOut.ok ?_ hrel3 hinv3
                (Ext.trans hext1 (Ext.trans hext2 hext3)) trivial
              show Except.ok (absLeaves x1 ++ absLeaves y1 ++ absLeaves z1, lst3) = _
              rw [absLeaves_eq v2, fvl_append_refines hv2, fvl_append_refines hv1]
              rfl


/-- `size_b` ⊑ `sizeB` — node count with `fvar` a leaf. -/
theorem size_b_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.size_b pers st fuel h = ok o) :
    AOut absU (fun _ => True) pers lst o st
      ((sizeB (absU fuel) (absEIdx h)).run lst) := by
  exact size_b_aux fuel.val rfl hrel hinv hrun

/-- `size_f` ⊑ `sizeF` — full node count, `fvar` annotations included. -/
theorem size_f_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.size_f pers st fuel h = ok o) :
    AOut absU (fun _ => True) pers lst o st
      ((sizeF (absU fuel) (absEIdx h)).run lst) := by
  exact size_f_aux fuel.val rfl hrel hinv hrun

/-- `fvar_leaves` ⊑ `fvarLeaves` — the unmemoized leaf walk.  The Rust builds
a `Vec` where the twin conses a `List`; `absLeaves` is the map. -/
theorem fvar_leaves_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_leaves pers st fuel h = ok o) :
    AOut absLeaves (fun _ => True) pers lst o st
      ((fvarLeaves (absU fuel) (absEIdx h)).run lst) := by
  exact fvar_leaves_aux fuel.val rfl hrel hinv hrun

/-- `wscoped_b` ⊑ `wscopedB` — the unmemoized scope check. -/
theorem wscoped_b_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {fuel d : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.wscoped_b pers st fuel d h = ok o) :
    AOut id (fun _ => True) pers lst o st
      ((wscopedB (absU fuel) (absU d) (absEIdx h)).run lst) := by
  exact wscoped_b_aux fuel.val rfl hrel hinv hrun

/-- `has_fvar` ⊑ `hasFvar` — the pure walk behind the `O(1)` field read. -/
theorem has_fvar_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.has_fvar pers st fuel h = ok o) :
    AOut id (fun _ => True) pers lst o st
      ((hasFvar (absU fuel) (absEIdx h)).run lst) := by
  exact has_fvar_aux fuel.val rfl hrel hinv hrun

/-- `loose_bvars_bounded` ⊑ `looseBVarsBounded` — the SPECIFICATION of the
packed-field cutoff (what executes is `loose_bvars_bounded_fast`, which is in
the `&mut` slice). -/
theorem loose_bvars_bounded_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel k : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.loose_bvars_bounded pers st fuel k h = ok o) :
    AOut id (fun _ => True) pers lst o st
      ((looseBVarsBounded (absU fuel) (absU k) (absEIdx h)).run lst) := by
  exact loose_bvars_bounded_aux fuel.val rfl hrel hinv hrun

/-- The fuel induction at a TEN-ARM view walk.  `view_run` answers the whole
view, so the ten arms of the port's `match` and the three of the twin's line
up by `cases` on the abstracted view — which is why the arm count costs
nothing beyond the `cases`. -/
private theorem result_sort_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      arena.expr_ops.result_sort pers st fuel h = ok o →
      AOut absLIdxOpt (fun _ => True) pers lst o st
        ((resultSort (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.result_sort] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((resultSort (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, resultSort, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.result_sort] at hrun
    have hne : ¬ (fuel = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hv := view_run hrel hinv hr
    rw [show absU fuel = m + 1 from hn, resultSort]
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hv
      have ho : (core.result.Result.Err e :
          core.result.Result (Option arena.handle.LIdx) _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      refine AOut.err ?_
      rw [StateT.run_bind]
      intro kk hk
      obtain ⟨le, hle, hlk⟩ := hv kk hk
      exact ⟨le, by rw [hle]; rfl, hlk⟩
    | Ok ev =>
      rw [hrc] at hrun hv
      obtain ⟨lst', hx, hrel', hinv', hext', -⟩ := hv
      have hlst : lst' = lst := view_run_state hx
      subst hlst
      rw [StateT.run_bind, hx]
      cases ev with
      | BVar _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | FVar _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | «Sort» u =>
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Const _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | App _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Lam _ _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | LetE _ _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Lit _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | Proj _ _ _ =>
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
      | ForallE ty b mm =>
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec := ih (fuel := i1) (h := b) hi1v hrel hinv hrun
        rw [show absU i1 = m from hi1v] at hrec
        exact hrec

/-- `result_sort` ⊑ `resultSort` — view-first on BOTH sides (the `∀` arm and
the `sort` arm are two of the ten), so no resolution hypothesis. -/
theorem result_sort_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.result_sort pers st fuel h = ok o) :
    AOut absLIdxOpt (fun _ => True) pers lst o st
      ((resultSort (absU fuel) (absEIdx h)).run lst) :=
  result_sort_aux fuel.val rfl hrel hinv hrun

/-! ## The application spine: tag-first on both sides

`get_app_fn` and `get_app_args_go` are two of the seven walks task #97-P6-13's
ledger says the twin DOES spell the tag dispatch at, so the two line up and
neither needs finding 1's hypothesis.  **They wait on `Specs.lean`'s
`viewApp` and on `EIdx.tag`'s abstraction (`eidx_tag_abs`, landed in
`Refine2/AbsStore.lean`).** -/

/-! ### The fuel induction, written out once

The shape step round 3 says does not automate, at the tier's simplest walk.
The Rust recurses on `fuel - 1#u64` and the twin on `Nat`, so the induction is
on `fuel.val` with everything else generalised; the `succ` case peels
`getAppFn (m+1)` and the `zero` case is the port's own `Internal`, which the
twin mirrors.  Every other fuelled walk of this tier is this proof with more
arms. -/

private theorem get_app_fn_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      arena.expr_ops.get_app_fn pers st fuel h = ok o →
      AOut absEIdx (fun _ => True) pers lst o st
        ((getAppFn (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.get_app_fn] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((getAppFn (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, getAppFn, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hrun
    rw [arena.expr_ops.get_app_fn] at hrun
    have hne : ¬ (fuel = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htag := eidx_tag_abs ht
    rw [show absU fuel = m + 1 from hn, getAppFn]
    by_cases hc : t = arena.handle.ETAG_APP
    · rw [if_pos hc] at hrun
      subst hc
      rw [show ((absEIdx h).tag == ETag.app) = true by
        rw [htag, etag_app_abs]; simp]
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hva := view_app_run hrel hp
      simp only [if_true]
      rw [StateT.run_bind, hva]
      cases hpc : p with
      | none =>
        rw [hpc] at hrun
        rw [arena.monad.fail_dangling_e] at hrun
        obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [fail_run hrun]
        refine AOut.err ?_
        show AErrSim _ ((Arena.failDanglingE : AM EIdx).run lst)
        exact failDanglingE_errSim lst
      | some q =>
        rw [hpc] at hrun
        obtain ⟨f1, a1⟩ := q
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        show AOut absEIdx (fun _ => True) pers lst o st
          ((getAppFn m (absEIdx f1)).run lst)
        have := ih (fuel := i1) (h := f1) hi1v hrel hinv hrun
        rw [show absU i1 = m from hi1v] at this
        exact this
    · rw [if_neg hc] at hrun
      obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [dupId_eidx _ _ he1] at hrun
      have ho : (core.result.Result.Ok h : core.result.Result _ _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      rw [show ((absEIdx h).tag == ETag.app) = false by
        rw [htag]
        have : absU32 t ≠ ETag.app := by
          rw [← etag_app_abs]
          intro hcc; exact hc (absU32_inj hcc)
        simp [this]]
      simp only [Bool.false_eq_true, if_false]
      exact AOut.ok rfl hrel hinv (Ext.refl _) trivial

/-- `get_app_fn` ⊑ `getAppFn`. -/
theorem get_app_fn_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.get_app_fn pers st fuel h = ok o) :
    AOut absEIdx (fun _ => True) pers lst o st
      ((getAppFn (absU fuel) (absEIdx h)).run lst) :=
  get_app_fn_aux fuel.val rfl hrel hinv hrun

private theorem get_app_args_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {k : Std.Usize} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      arena.expr_ops.get_app_args_go pers st fuel h k = ok o →
      AOut absEIdxList (fun _ => True) pers lst o st
        ((getAppArgs (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h k o hn hrel hinv hrun
    rw [arena.expr_ops.get_app_args_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((getAppArgs (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, getAppArgs, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h k o hn hrel hinv hrun
    rw [arena.expr_ops.get_app_args_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htag := eidx_tag_abs ht
    rw [show absU fuel = m + 1 from hn, getAppArgs]
    by_cases hc : t = arena.handle.ETAG_APP
    · rw [if_pos hc] at hrun
      subst hc
      rw [show ((absEIdx h).tag == ETag.app) = true by
        rw [htag, etag_app_abs]; simp]
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hva := view_app_run hrel hp
      simp only [if_true]
      rw [StateT.run_bind, hva]
      cases hpc : p with
      | none =>
        rw [hpc] at hrun
        rw [arena.monad.fail_dangling_e] at hrun
        obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [fail_run hrun]
        refine AOut.err ?_
        show AErrSim _ ((Arena.failDanglingE : AM (List EIdx)).run lst)
        exact failDanglingE_errSim lst
      | some q =>
        rw [hpc] at hrun
        obtain ⟨f1, a1⟩ := q
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hrec := ih (fuel := i1) (h := f1) (k := i2) hi1v hrel hinv hr
        rw [show absU i1 = m from hi1v] at hrec
        show AOut absEIdxList (fun _ => True) pers lst o st
          ((do let qs ← getAppArgs m (absEIdx f1); pure (qs ++ [absEIdx a1])).run lst)
        cases hrc : r with
        | Err e =>
          rw [hrc] at hrun hrec
          have ho : (core.result.Result.Err e :
              core.result.Result (alloc.vec.Vec arena.handle.EIdx) _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          refine AOut.err ?_
          rw [StateT.run_bind]
          intro kk hk
          obtain ⟨le, hle, hlk⟩ := hrec kk hk
          exact ⟨le, by rw [hle]; rfl, hlk⟩
        | Ok args =>
          rw [hrc] at hrun hrec
          obtain ⟨lst', hx, hrel', hinv', hext', -⟩ := hrec
          obtain ⟨args1, ha1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok args1 :
              core.result.Result (alloc.vec.Vec arena.handle.EIdx) _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          refine AOut.ok ?_ hrel' hinv' hext' trivial
          rw [StateT.run_bind, hx]
          show Except.ok _ = _
          rw [show absEIdxList args1 = absEIdxList args ++ [absEIdx a1] by
            unfold absEIdxList
            rw [ConRon.Refine.vec_push_val ha1, List.map_append]
            rfl]
    · rw [if_neg hc] at hrun
      have ho : (core.result.Result.Ok
          (alloc.vec.Vec.with_capacity arena.handle.EIdx k) :
          core.result.Result (alloc.vec.Vec arena.handle.EIdx) _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      rw [show ((absEIdx h).tag == ETag.app) = false by
        rw [htag]
        have : absU32 t ≠ ETag.app := by
          rw [← etag_app_abs]
          intro hcc; exact hc (absU32_inj hcc)
        simp [this]]
      simp only [Bool.false_eq_true, if_false]
      refine AOut.ok ?_ hrel hinv (Ext.refl _) trivial
      show Except.ok ([], lst) = _
      rfl

/-- `get_app_args_go` ⊑ `getAppArgs` — the cursor recursion.  **`k` does not
appear on the twin's side at all**: it is the capacity hint, so the statement
quantifies over it and says the answer does not depend on it. -/
theorem get_app_args_go_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {h : arena.handle.EIdx} {k : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.get_app_args_go pers st fuel h k = ok o) :
    AOut absEIdxList (fun _ => True) pers lst o st
      ((getAppArgs (absU fuel) (absEIdx h)).run lst) :=
  get_app_args_go_aux fuel.val rfl hrel hinv hrun

/-- `get_app_args` ⊑ `getAppArgs` — the `k = 0` wrapper, and it is the whole
proof: the Rust's `k` is spent as the `Vec`'s capacity and nothing else (task
#97-P6-9), so the wrapper is `get_app_args_go` at `k = 0` and the statement
above is already quantified over `k`.  **CLOSED** — no store read of its own,
which is why it is the one composition this file can discharge before
`Specs.lean` lands. -/
theorem get_app_args_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.get_app_args pers st fuel h = ok o) :
    AOut absEIdxList (fun _ => True) pers lst o st
      ((getAppArgs (absU fuel) (absEIdx h)).run lst) := by
  rw [arena.expr_ops.get_app_args] at hrun
  exact get_app_args_go_refines hrel hinv hrun

/-! ## The eight tag-first readers (finding 1), and the tag/view agreement

Task #97-P5-2 §10 argued that P5-0's finding 3 can be **weakened**: what these
eight need is `EResolves` — "this handle decodes" — and the tag/view agreement
lemma `st.view h = some v → h.tag = v.tagOf`, which is UNCONDITIONAL.  That
argument is mechanised here (`etables_get_tagOf`, `estore_view_tagOf`), and it
holds for the four ONE-NODE readers exactly as argued: `is_lam`, `lam_pw`,
`forall_pw` and `fvar_type_d` carry `EResolves` alone and no `StoreWF`.

**The four RECURSIVE ones keep `StoreWF`, and the §10 argument did not see
why**: `strip_lams`, `strip_pis`, `pi_result` and `pi_arity` descend into the
binder BODY, and the Rust's `Ok(None)` / `Ok(h)` at the child needs the child
to decode too.  "The children of a decoding node decode" is `EWFAt`'s
`childOK` clause and nothing weaker — `EResolves.child` below is that clause,
and it is the one place `StoreWF` is really used in this file.

These lemmas are `Arena/WFProofs.lean`'s business by rights (it owns
`ENodeView.tagOf` and the `ETables.get_inv` machinery); they live here because
this round does not touch `Arena/`. -/

/-! ## The tag/view agreement, mechanised -/

/-- The tag a decoded node lands under is the handle's own tag.  Unconditional
at one tier. -/
theorem etables_get_tagOf {t : ETables} {i : EIdx} {v : ENodeView}
    (h : t.get i = some v) : i.tag = v.tagOf := by
  simp only [ETables.get] at h
  tag_cases h <;>
    first
      | (simp only [Option.map_eq_some_iff] at h
         obtain ⟨r, -, rfl⟩ := h
         simp only [ENodeView.tagOf]
         exact eq_of_beq hc)
      | simp at h

/-- The bind arm of `EStore.view`, taken apart. -/
theorem estore_view_bind_parts {st : EStore} {i : EIdx} {v : ENodeView}
    (hb : ETag.isBind i.tag = true) (h : st.view i = some v) :
    ∃ ty b m, st.viewBind i = some (ty, b, m) ∧ v = eBindView i.tag ty b m := by
  rw [EStore.view, if_pos hb] at h
  cases hvb : st.viewBind i with
  | none => rw [hvb] at h; exact absurd h (by simp)
  | some p =>
    obtain ⟨ty, b, m⟩ := p
    rw [hvb] at h
    simp only [Option.some.injEq] at h
    exact ⟨ty, b, m, rfl, h.symm⟩

/-- `viewBindI` failing makes `viewBind` fail. -/
theorem estore_viewBind_none_of_viewBindI {st : EStore} {i : EIdx}
    (h : st.viewBindI i = none) : st.viewBind i = none := by
  rw [EStore.viewBind, h]

/-- `viewBind` failing makes `view` fail, at a binder tag. -/
theorem estore_view_none_of_viewBind {st : EStore} {i : EIdx}
    (hb : ETag.isBind i.tag = true) (h : st.viewBind i = none) :
    st.view i = none := by
  rw [EStore.view, if_pos hb, h]

/-- **The tag/view agreement**: `view` answers the view whose constructor is
the handle's own tag.  UNCONDITIONAL — no `StoreWF`. -/
theorem estore_view_tagOf {st : EStore} {i : EIdx} {v : ENodeView}
    (h : st.view i = some v) : i.tag = v.tagOf := by
  by_cases hb : ETag.isBind i.tag = true
  · obtain ⟨ty, b, m, -, rfl⟩ := estore_view_bind_parts hb h
    simp only [eBindView]
    split <;> rename_i hl
    · simp only [ENodeView.tagOf]; exact eq_of_beq hl
    · simp only [ENodeView.tagOf]
      simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with hb | hb
      · exact absurd (by simp [hb] : (i.tag == ETag.lam) = true) hl
      · exact hb
  · rw [EStore.view, if_neg hb] at h
    split at h
    · exact etables_get_tagOf h
    · split at h
      · exact etables_get_tagOf h
      · simp at h

/-- A view whose tag is `lam` IS a `lam`. -/
theorem eview_lam_of_tag {v : ENodeView} (h : v.tagOf = ETag.lam) :
    ∃ ty b m, v = .lam ty b m := by
  cases v <;> simp only [ENodeView.tagOf] at h <;>
    first
      | exact ⟨_, _, _, rfl⟩
      | exact absurd h (by decide)

/-- A view whose tag is `forallE` IS a `forallE`. -/
theorem eview_forallE_of_tag {v : ENodeView} (h : v.tagOf = ETag.forallE) :
    ∃ ty b m, v = .forallE ty b m := by
  cases v <;> simp only [ENodeView.tagOf] at h <;>
    first
      | exact ⟨_, _, _, rfl⟩
      | exact absurd h (by decide)

/-- A view whose tag is `fvar` IS an `fvar`. -/
theorem eview_fvar_of_tag {v : ENodeView} (h : v.tagOf = ETag.fvar) :
    ∃ i ty, v = .fvar i ty := by
  cases v <;> simp only [ENodeView.tagOf] at h <;>
    first
      | exact ⟨_, _, rfl⟩
      | exact absurd h (by decide)

/-- The twin's `view` at a resolving handle. -/
theorem arena_view_run_some {lst : AState} {hh : EIdx} {v : ENodeView}
    (h : lst.store.view hh = some v) : (Arena.view hh).run lst = .ok (v, lst) := by
  show ((match lst.store.view hh with
          | some w => (pure w : AM ENodeView)
          | none => Arena.fail
              (.internal "arena: dangling expression handle")).run lst) = _
  rw [h]
  rfl

/-- `EResolves` unpacked. -/
theorem EResolves.dest {lst : AState} {hh : EIdx} (h : EResolves lst hh) :
    ∃ v, lst.store.view hh = some v := Option.isSome_iff_exists.mp h

/-- A twin READER's value, read off its `SimR`. -/
theorem reader_eq {α β : Type} {A : α → β} {lst : AState} {r : α} {f : AState → β}
    (h : SimR A lst r (do let s ← get; pure (f s))) : f lst = A r := by
  have h' : (Except.ok (f lst, lst) : Except Arena.CheckError (β × AState))
      = Except.ok (A r, lst) := h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h'
  exact h'.1

/-- The twin's `isLam` at a resolving handle. -/
theorem isLam_run {lst : AState} {hh : EIdx} {v : ENodeView}
    (hv : lst.store.view hh = some v) :
    (isLam hh).run lst
      = ((match v with
          | .lam _ _ _ => (pure true : AM Bool)
          | _ => pure false).run lst) := by
  rw [show isLam hh = (do
        let w ← Arena.view hh
        match w with
        | .lam _ _ _ => (pure true : AM Bool)
        | _ => pure false) from rfl,
    StateT.run_bind, arena_view_run_some hv]
  rfl

theorem is_lam_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hres : EResolves lst (absEIdx h))
    (hrun : arena.expr_ops.is_lam pers st h = ok o) :
    AOut id (fun _ => True) pers lst o st ((isLam (absEIdx h)).run lst) := by
  rw [arena.expr_ops.is_lam] at hrun
  obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have htag := eidx_tag_abs ht
  obtain ⟨v, hv⟩ := EResolves.dest hres
  have htv : (absEIdx h).tag = v.tagOf := estore_view_tagOf hv
  rw [isLam_run hv]
  by_cases hc : t = arena.handle.ETAG_LAM
  · subst hc
    rw [if_pos rfl] at hrun
    have hlam : (absEIdx h).tag = ETag.lam := by rw [htag, etag_lam_abs]
    have hbind : ETag.isBind (absEIdx h).tag = true := by
      rw [hlam]; simp [ETag.isBind]
    obtain ⟨ty, b, m, rfl⟩ := eview_lam_of_tag (by rw [← htv]; exact hlam)
    obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hqa := reader_eq (view_bind_i_run hrel hbind hq)
    cases hqc : q with
    | none =>
      exfalso
      rw [hqc] at hqa
      simp only [Option.map_none] at hqa
      rw [estore_view_none_of_viewBind hbind
        (estore_viewBind_none_of_viewBindI hqa)] at hv
      simp at hv
    | some p =>
      rw [hqc] at hrun
      have ho : (core.result.Result.Ok true : core.result.Result Bool _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · rw [if_neg hc] at hrun
    have ho : (core.result.Result.Ok false : core.result.Result Bool _) = o :=
      Result.ok_injective hrun
    rw [← ho]
    have hne : v.tagOf ≠ ETag.lam := by
      rw [← htv, htag, ← etag_lam_abs]
      intro hcc; exact hc (absU32_inj hcc)
    cases v <;>
      first
        | (exact absurd rfl hne)
        | exact AOut.ok rfl hrel hinv (Ext.refl _) trivial

/-- The twin's `view`-bind at a resolving handle, once for every reader. -/
theorem view_bind_run_some {β : Type} {lst : AState} {hh : EIdx} {v : ENodeView}
    (hv : lst.store.view hh = some v) (f : ENodeView → AM β) :
    (do let w ← Arena.view hh; f w).run lst = (f v).run lst := by
  rw [StateT.run_bind, arena_view_run_some hv]; rfl

/-- `StoreWF` carries "this handle resolves" to the children. -/
theorem EResolves.child {lst : AState} {hh : EIdx} {v : ENodeView}
    (hwf : StoreWF lst.store) (hv : lst.store.view hh = some v)
    {c : EIdx} (hc : c ∈ v.echildren) : EResolves lst c := by
  obtain ⟨rk, hw⟩ := hwf
  exact (hw.childOK hh v hv c hc).1

/-- The binder view a resolving handle of a binder tag decodes to, with the
`viewBind` triple it came from. -/
theorem view_bind_parts_of_resolves {lst : AState} {hh : EIdx} {v : ENodeView}
    (hbind : ETag.isBind hh.tag = true) (hv : lst.store.view hh = some v) :
    ∃ ty b m, lst.store.viewBind hh = some (ty, b, m) ∧
      v = eBindView hh.tag ty b m :=
  estore_view_bind_parts hbind hv

theorem lam_pw_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hres : EResolves lst (absEIdx h))
    (hrun : arena.expr_ops.lam_pw pers st h = ok o) :
    AOut absPwOpt (fun _ => True) pers lst o st ((lamPw (absEIdx h)).run lst) := by
  rw [arena.expr_ops.lam_pw] at hrun
  obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have htag := eidx_tag_abs ht
  obtain ⟨v, hv⟩ := EResolves.dest hres
  have htv : (absEIdx h).tag = v.tagOf := estore_view_tagOf hv
  rw [show lamPw (absEIdx h) = (do
        let w ← Arena.view (absEIdx h)
        match w with
        | .lam _ _ m => (pure (some m.pw) : AM (Option ConLeche.PropWhen))
        | _ => pure none) from rfl,
    view_bind_run_some hv]
  by_cases hc : t = arena.handle.ETAG_LAM
  · subst hc
    rw [if_pos rfl] at hrun
    have hlam : (absEIdx h).tag = ETag.lam := by rw [htag, etag_lam_abs]
    have hbind : ETag.isBind (absEIdx h).tag = true := by
      rw [hlam]; simp [ETag.isBind]
    obtain ⟨ty0, b0, m0, hvb, hveq⟩ := estore_view_bind_parts hbind hv
    obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hqa := reader_eq (view_bind_run hrel hbind hq)
    rw [hvb] at hqa
    cases hqc : q with
    | none => rw [hqc] at hqa; simp at hqa
    | some p =>
      rw [hqc] at hrun hqa
      obtain ⟨rty, rb, rm⟩ := p
      simp only [Option.map_some, Option.some.injEq, absBindM, Prod.mk.injEq] at hqa
      have ho : (core.result.Result.Ok (some rm.pw) :
          core.result.Result (Option kernel.prop_when.PropWhen) _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      have hvv : v = .lam ty0 b0 m0 := by
        rw [hveq, eBindView, hlam]; simp
      subst hvv
      refine AOut.ok ?_ hrel hinv (Ext.refl _) trivial
      have hm : m0 = ConRon.Refine.absBinderMeta rm := by
        rw [← hqa.2.2]
      rw [hm]
      rfl
  · rw [if_neg hc] at hrun
    have ho : (core.result.Result.Ok (none : Option kernel.prop_when.PropWhen) :
        core.result.Result (Option kernel.prop_when.PropWhen) _) = o :=
      Result.ok_injective hrun
    rw [← ho]
    have hne : v.tagOf ≠ ETag.lam := by
      rw [← htv, htag, ← etag_lam_abs]
      intro hcc; exact hc (absU32_inj hcc)
    cases v <;>
      first
        | (exact absurd rfl hne)
        | exact AOut.ok rfl hrel hinv (Ext.refl _) trivial

theorem forall_pw_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hres : EResolves lst (absEIdx h))
    (hrun : arena.expr_ops.forall_pw pers st h = ok o) :
    AOut absPwOpt (fun _ => True) pers lst o st
      ((forallPw (absEIdx h)).run lst) := by
  rw [arena.expr_ops.forall_pw] at hrun
  obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have htag := eidx_tag_abs ht
  obtain ⟨v, hv⟩ := EResolves.dest hres
  have htv : (absEIdx h).tag = v.tagOf := estore_view_tagOf hv
  rw [show forallPw (absEIdx h) = (do
        let w ← Arena.view (absEIdx h)
        match w with
        | .forallE _ _ m => (pure (some m.pw) : AM (Option ConLeche.PropWhen))
        | _ => pure none) from rfl,
    view_bind_run_some hv]
  by_cases hc : t = arena.handle.ETAG_FORALL_E
  · subst hc
    rw [if_pos rfl] at hrun
    have hlam : (absEIdx h).tag = ETag.forallE := by rw [htag, etag_forallE_abs]
    have hbind : ETag.isBind (absEIdx h).tag = true := by
      rw [hlam]; simp [ETag.isBind, ETag.lam, ETag.forallE]
    obtain ⟨ty0, b0, m0, hvb, hveq⟩ := estore_view_bind_parts hbind hv
    obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hqa := reader_eq (view_bind_run hrel hbind hq)
    rw [hvb] at hqa
    cases hqc : q with
    | none => rw [hqc] at hqa; simp at hqa
    | some p =>
      rw [hqc] at hrun hqa
      obtain ⟨rty, rb, rm⟩ := p
      simp only [Option.map_some, Option.some.injEq, absBindM, Prod.mk.injEq] at hqa
      have ho : (core.result.Result.Ok (some rm.pw) :
          core.result.Result (Option kernel.prop_when.PropWhen) _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      have hvv : v = .forallE ty0 b0 m0 := by
        rw [hveq, eBindView, hlam]
        simp [ETag.lam, ETag.forallE]
      subst hvv
      refine AOut.ok ?_ hrel hinv (Ext.refl _) trivial
      have hm : m0 = ConRon.Refine.absBinderMeta rm := by rw [← hqa.2.2]
      rw [hm]
      rfl
  · rw [if_neg hc] at hrun
    have ho : (core.result.Result.Ok (none : Option kernel.prop_when.PropWhen) :
        core.result.Result (Option kernel.prop_when.PropWhen) _) = o :=
      Result.ok_injective hrun
    rw [← ho]
    have hne : v.tagOf ≠ ETag.forallE := by
      rw [← htv, htag, ← etag_forallE_abs]
      intro hcc; exact hc (absU32_inj hcc)
    cases v <;>
      first
        | (exact absurd rfl hne)
        | exact AOut.ok rfl hrel hinv (Ext.refl _) trivial

/-! ### `view` at a non-binder tag, and the `fvar` projection -/

theorem estore_view_nonbind {st : EStore} {i : EIdx}
    (hnb : ETag.isBind i.tag = false) :
    st.view i = (if i.isPersistent then st.pers.get i
      else if st.scratchOn then st.scr.get i else none) := by
  rw [EStore.view, if_neg (by simp [hnb])]

set_option linter.unusedSimpArgs false in
theorem etables_getFVarTy_of_get {t : ETables} {i : EIdx} {k : Nat} {ty : EIdx}
    (htg : i.tag = ETag.fvar) (h : t.get i = some (.fvar k ty)) :
    t.getFVarTy i = some ty := by
  cases hr : t.fvars.node? i.idxNat with
  | none =>
    simp [ETables.get, htg, ETag.fvar, ETag.bvar, ETag.sort, ETag.const,
      ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.letE, ETag.lit,
      ETag.proj, hr] at h
  | some r =>
    simp [ETables.get, htg, ETag.fvar, ETag.bvar, ETag.sort, ETag.const,
      ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.letE, ETag.lit,
      ETag.proj, hr] at h
    simp [ETables.getFVarTy, hr, h.2]

theorem estore_viewFVarTy_of_view {st : EStore} {i : EIdx} {k : Nat} {ty : EIdx}
    (hv : st.view i = some (.fvar k ty)) : st.viewFVarTy i = some ty := by
  have htg : i.tag = ETag.fvar := estore_view_tagOf hv
  rw [estore_view_nonbind (by rw [htg]; decide)] at hv
  simp only [EStore.viewFVarTy, EStore.persGetFVarTy]
  by_cases hp : i.isPersistent = true
  · rw [if_pos hp] at hv ⊢; exact etables_getFVarTy_of_get htg hv
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at hv ⊢
    simp only [Bool.false_eq_true, if_false] at hv ⊢
    by_cases hon : st.scratchOn = true
    · rw [if_pos hon] at hv ⊢; exact etables_getFVarTy_of_get htg hv
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at hv; simp at hv

theorem fvar_type_d_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hres : EResolves lst (absEIdx h))
    (hrun : arena.expr_ops.fvar_type_d pers st h = ok o) :
    AOut absEIdx (fun _ => True) pers lst o st
      ((fvarTypeD (absEIdx h)).run lst) := by
  rw [arena.expr_ops.fvar_type_d] at hrun
  obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have htag := eidx_tag_abs ht
  obtain ⟨v, hv⟩ := EResolves.dest hres
  have htv : (absEIdx h).tag = v.tagOf := estore_view_tagOf hv
  rw [show fvarTypeD (absEIdx h) = (do
        let w ← Arena.view (absEIdx h)
        match w with
        | .fvar _ ty => (pure ty : AM EIdx)
        | _ => pure (absEIdx h)) from rfl,
    view_bind_run_some hv]
  by_cases hc : t = arena.handle.ETAG_FVAR
  · subst hc
    rw [if_pos rfl] at hrun
    have hfv : (absEIdx h).tag = ETag.fvar := by rw [htag, etag_fvar_abs]
    obtain ⟨k0, ty0, rfl⟩ := eview_fvar_of_tag (by rw [← htv]; exact hfv)
    obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hqa := reader_eq (view_fvar_ty_run hrel hq)
    rw [estore_viewFVarTy_of_view hv] at hqa
    cases hqc : q with
    | none => rw [hqc] at hqa; simp at hqa
    | some ty1 =>
      rw [hqc] at hrun hqa
      simp only [Option.map_some, Option.some.injEq] at hqa
      have ho : (core.result.Result.Ok ty1 :
          core.result.Result arena.handle.EIdx _) = o := Result.ok_injective hrun
      rw [← ho]
      refine AOut.ok ?_ hrel hinv (Ext.refl _) trivial
      rw [← hqa]
      rfl
  · rw [if_neg hc] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho : (core.result.Result.Ok h : core.result.Result arena.handle.EIdx _) = o :=
      Result.ok_injective hrun
    rw [← ho]
    have hne : v.tagOf ≠ ETag.fvar := by
      rw [← htv, htag, ← etag_fvar_abs]
      intro hcc; exact hc (absU32_inj hcc)
    cases v <;>
      first
        | (exact absurd rfl hne)
        | exact AOut.ok rfl hrel hinv (Ext.refl _) trivial

/-- `viewBind` answering names the datum handle `viewBindI` answers with. -/
theorem estore_viewBindI_of_viewBind {st : EStore} {i : EIdx} {ty b : EIdx}
    {m : ConLeche.BinderMeta} (h : st.viewBind i = some (ty, b, m)) :
    ∃ mi, st.viewBindI i = some (ty, b, mi) := by
  cases hbi : st.viewBindI i with
  | none => rw [estore_viewBind_none_of_viewBindI hbi] at h; simp at h
  | some p =>
    obtain ⟨ty1, b1, mi⟩ := p
    refine ⟨mi, ?_⟩
    have hvb : st.viewBind i = (match st.viewBM mi with
        | none => none
        | some m => some (ty1, b1, m)) := by rw [EStore.viewBind, hbi]; rfl
    rw [hvb] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1, h.2.1]

private theorem pi_result_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      StoreWF lst.store → EResolves lst (absEIdx h) →
      arena.expr_ops.pi_result pers st fuel h = ok o →
      AOut absEIdx (fun _ => True) pers lst o st
        ((piResult (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hwf hres hrun
    rw [arena.expr_ops.pi_result] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((piResult (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, piResult, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hwf hres hrun
    rw [arena.expr_ops.pi_result] at hrun
    have hne : ¬ (fuel = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htag := eidx_tag_abs ht
    obtain ⟨v, hv⟩ := EResolves.dest hres
    have htv : (absEIdx h).tag = v.tagOf := estore_view_tagOf hv
    rw [show absU fuel = m + 1 from hn, piResult, StateT.run_bind,
      arena_view_run_some hv]
    by_cases hc : t = arena.handle.ETAG_FORALL_E
    · subst hc
      rw [if_pos rfl] at hrun
      have hfa : (absEIdx h).tag = ETag.forallE := by rw [htag, etag_forallE_abs]
      have hbind : ETag.isBind (absEIdx h).tag = true := by
        rw [hfa]; simp [ETag.isBind, ETag.lam, ETag.forallE]
      obtain ⟨ty0, b0, m0, hvb, hveq⟩ := estore_view_bind_parts hbind hv
      have hvv : v = .forallE ty0 b0 m0 := by
        rw [hveq, eBindView, hfa]; simp [ETag.lam, ETag.forallE]
      subst hvv
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hqa := reader_eq (view_bind_i_run hrel hbind hq)
      obtain ⟨mi, hbi⟩ := estore_viewBindI_of_viewBind hvb
      rw [hbi] at hqa
      cases hqc : q with
      | none => rw [hqc] at hqa; simp at hqa
      | some p =>
        obtain ⟨rty, rb, rmi⟩ := p
        rw [hqc] at hrun hqa
        simp only [Option.map_some, Option.some.injEq, absBindI,
          Prod.mk.injEq] at hqa
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hres' : EResolves lst b0 :=
          EResolves.child hwf hv (by simp [ENodeView.echildren])
        have hrec := ih hi1v hrel hinv hwf (by rw [← hqa.2.1]; exact hres') hrun
        rw [show absU i1 = m from hi1v, ← hqa.2.1] at hrec
        exact hrec
    · rw [if_neg hc] at hrun
      obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [dupId_eidx _ _ he1] at hrun
      have ho : (core.result.Result.Ok h :
          core.result.Result arena.handle.EIdx _) = o := Result.ok_injective hrun
      rw [← ho]
      have hnef : v.tagOf ≠ ETag.forallE := by
        rw [← htv, htag, ← etag_forallE_abs]
        intro hcc; exact hc (absU32_inj hcc)
      cases v <;>
        first
          | (exact absurd rfl hnef)
          | exact AOut.ok rfl hrel hinv (Ext.refl _) trivial

theorem pi_result_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : StoreWF lst.store) (hres : EResolves lst (absEIdx h))
    (hrun : arena.expr_ops.pi_result pers st fuel h = ok o) :
    AOut absEIdx (fun _ => True) pers lst o st
      ((piResult (absU fuel) (absEIdx h)).run lst) :=
  pi_result_aux fuel.val rfl hrel hinv hwf hres hrun

private theorem pi_arity_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {fuel : Std.U64} {h : arena.handle.EIdx} {o},
      fuel.val = n → AStateRel pers st lst → AStateInv pers st →
      StoreWF lst.store → EResolves lst (absEIdx h) →
      arena.expr_ops.pi_arity pers st fuel h = ok o →
      AOut absU (fun _ => True) pers lst o st
        ((piArity (absU fuel) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst fuel h o hn hrel hinv hwf hres hrun
    rw [arena.expr_ops.pi_arity] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    refine AOut.err ?_
    show AErrSim _ ((piArity (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, piArity, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst fuel h o hn hrel hinv hwf hres hrun
    rw [arena.expr_ops.pi_arity] at hrun
    have hne : ¬ (fuel = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htag := eidx_tag_abs ht
    obtain ⟨v, hv⟩ := EResolves.dest hres
    have htv : (absEIdx h).tag = v.tagOf := estore_view_tagOf hv
    rw [show absU fuel = m + 1 from hn, piArity, StateT.run_bind,
      arena_view_run_some hv]
    by_cases hc : t = arena.handle.ETAG_FORALL_E
    · subst hc
      rw [if_pos rfl] at hrun
      have hfa : (absEIdx h).tag = ETag.forallE := by rw [htag, etag_forallE_abs]
      have hbind : ETag.isBind (absEIdx h).tag = true := by
        rw [hfa]; simp [ETag.isBind, ETag.lam, ETag.forallE]
      obtain ⟨ty0, b0, m0, hvb, hveq⟩ := estore_view_bind_parts hbind hv
      have hvv : v = .forallE ty0 b0 m0 := by
        rw [hveq, eBindView, hfa]; simp [ETag.lam, ETag.forallE]
      subst hvv
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hqa := reader_eq (view_bind_run hrel hbind hq)
      rw [hvb] at hqa
      cases hqc : q with
      | none => rw [hqc] at hqa; simp at hqa
      | some p =>
        obtain ⟨rty, rb, rm⟩ := p
        rw [hqc] at hrun hqa
        simp only [Option.map_some, Option.some.injEq, absBindM,
          Prod.mk.injEq] at hqa
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hres' : EResolves lst b0 :=
          EResolves.child hwf hv (by simp [ENodeView.echildren])
        have hrec := ih hi1v hrel hinv hwf (by rw [← hqa.2.1]; exact hres') hr
        rw [show absU i1 = m from hi1v, ← hqa.2.1] at hrec
        show AOut absU (fun _ => True) pers lst o st
          ((do let x ← piArity m b0; pure (x + 1)).run lst)
        rw [StateT.run_bind]
        cases hrc : r with
        | Err e =>
          rw [hrc] at hrun hrec
          have ho : (core.result.Result.Err e :
              core.result.Result Std.U64 _) = o := Result.ok_injective hrun
          rw [← ho]
          exact AOut.err (AErrSim.bind hrec _)
        | Ok nn =>
          rw [hrc] at hrun hrec
          obtain ⟨lst', hx, hrel', hinv', hext', -⟩ := hrec
          obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok i2 :
              core.result.Result Std.U64 _) = o := Result.ok_injective hrun
          rw [← ho]
          refine AOut.ok ?_ hrel' hinv' hext' trivial
          rw [hx]
          have hi2v : absU i2 = absU nn + 1 := ConRon.Refine.Nat.uadd_val hi2
          show Except.ok (absU nn + 1, lst') = _
          rw [hi2v]
    · rw [if_neg hc] at hrun
      have ho : (core.result.Result.Ok 0#u64 :
          core.result.Result Std.U64 _) = o := Result.ok_injective hrun
      rw [← ho]
      have hnef : v.tagOf ≠ ETag.forallE := by
        rw [← htv, htag, ← etag_forallE_abs]
        intro hcc; exact hc (absU32_inj hcc)
      cases v <;>
        first
          | (exact absurd rfl hnef)
          | exact AOut.ok rfl hrel hinv (Ext.refl _) trivial

theorem pi_arity_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : StoreWF lst.store) (hres : EResolves lst (absEIdx h))
    (hrun : arena.expr_ops.pi_arity pers st fuel h = ok o) :
    AOut absU (fun _ => True) pers lst o st
      ((piArity (absU fuel) (absEIdx h)).run lst) :=
  pi_arity_aux fuel.val rfl hrel hinv hwf hres hrun

theorem absBinders_eq (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    absBinders v = absBinderL v := rfl

private theorem strip_lams_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {k : Std.U64} {h : arena.handle.EIdx} {o},
      k.val = n → AStateRel pers st lst → AStateInv pers st →
      StoreWF lst.store → EResolves lst (absEIdx h) →
      arena.expr_ops.strip_lams pers st k h = ok o →
      AOut absStrip (fun _ => True) pers lst o st
        ((stripLams (absU k) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst k h o hn hrel hinv hwf hres hrun
    rw [arena.expr_ops.strip_lams] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : k = 0#u64)] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho, show absU k = 0 from hn, stripLams]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  | succ m ih =>
    intro pers st lst k h o hn hrel hinv hwf hres hrun
    rw [arena.expr_ops.strip_lams] at hrun
    have hne : ¬ (k = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htag := eidx_tag_abs ht
    obtain ⟨v, hv⟩ := EResolves.dest hres
    have htv : (absEIdx h).tag = v.tagOf := estore_view_tagOf hv
    rw [show absU k = m + 1 from hn, stripLams, StateT.run_bind,
      arena_view_run_some hv]
    by_cases hc : t = arena.handle.ETAG_LAM
    · subst hc
      rw [if_pos rfl] at hrun
      have hla : (absEIdx h).tag = ETag.lam := by rw [htag, etag_lam_abs]
      have hbind : ETag.isBind (absEIdx h).tag = true := by
        rw [hla]; simp [ETag.isBind]
      obtain ⟨ty0, b0, m0, hvb, hveq⟩ := estore_view_bind_parts hbind hv
      have hvv : v = .lam ty0 b0 m0 := by
        rw [hveq, eBindView, hla]; simp
      subst hvv
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hqa := reader_eq (view_bind_run hrel hbind hq)
      rw [hvb] at hqa
      cases hqc : q with
      | none => rw [hqc] at hqa; simp at hqa
      | some p =>
        obtain ⟨rty, rb, rm⟩ := p
        rw [hqc] at hrun hqa
        simp only [Option.map_some, Option.some.injEq, absBindM,
          Prod.mk.injEq] at hqa
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = k.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hres' : EResolves lst b0 :=
          EResolves.child hwf hv (by simp [ENodeView.echildren])
        have hrec := ih hi1v hrel hinv hwf (by rw [← hqa.2.1]; exact hres') hr
        rw [show absU i1 = m from hi1v, ← hqa.2.1] at hrec
        show AOut absStrip (fun _ => True) pers lst o st
          ((do
            let w ← stripLams m b0
            match w with
            | some p => (pure (some ((ty0, m0) :: p.1, p.2)) :
                AM (Option (List (EIdx × ConLeche.BinderMeta) × EIdx)))
            | none => pure none).run lst)
        rw [StateT.run_bind]
        cases hrc : r with
        | Err e =>
          rw [hrc] at hrun hrec
          have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact AOut.err (AErrSim.bind hrec _)
        | Ok o1 =>
          rw [hrc] at hrun hrec
          obtain ⟨lst', hx, hrel', hinv', hext', -⟩ := hrec
          rw [hx]
          cases ho1 : o1 with
          | none =>
            rw [ho1] at hrun hx
            have ho : (core.result.Result.Ok (none :
                Option ((alloc.vec.Vec (arena.handle.EIdx ×
                  kernel.expr.BinderMeta)) × arena.handle.EIdx)) :
                core.result.Result _ _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel' hinv' hext' trivial
          | some pp =>
            obtain ⟨vv, ee⟩ := pp
            rw [ho1] at hrun hx
            obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok (some (v1, ee)) :
                core.result.Result _ _) = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel' hinv' hext' trivial
            show Except.ok (some ((ty0, m0) :: absBinders vv, absEIdx ee), lst')
              = Except.ok (absStrip (some (v1, ee)), lst')
            rw [show absStrip (some (v1, ee))
                = some (absBinders v1, absEIdx ee) from rfl,
              absBinders_eq v1, cons_binder_refines hv1, hqa.1, hqa.2.2]
            rfl
    · rw [if_neg hc] at hrun
      have ho : (core.result.Result.Ok (none :
          Option ((alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) ×
            arena.handle.EIdx)) : core.result.Result _ _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      have hnef : v.tagOf ≠ ETag.lam := by
        rw [← htv, htag, ← etag_lam_abs]
        intro hcc; exact hc (absU32_inj hcc)
      cases v <;>
        first
          | (exact absurd rfl hnef)
          | exact AOut.ok rfl hrel hinv (Ext.refl _) trivial

theorem strip_lams_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {k : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : StoreWF lst.store) (hres : EResolves lst (absEIdx h))
    (hrun : arena.expr_ops.strip_lams pers st k h = ok o) :
    AOut absStrip (fun _ => True) pers lst o st
      ((stripLams (absU k) (absEIdx h)).run lst) :=
  strip_lams_aux k.val rfl hrel hinv hwf hres hrun

private theorem strip_pis_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {k : Std.U64} {h : arena.handle.EIdx} {o},
      k.val = n → AStateRel pers st lst → AStateInv pers st →
      StoreWF lst.store → EResolves lst (absEIdx h) →
      arena.expr_ops.strip_pis pers st k h = ok o →
      AOut absStrip (fun _ => True) pers lst o st
        ((stripPis (absU k) (absEIdx h)).run lst) := by
  induction n with
  | zero =>
    intro pers st lst k h o hn hrel hinv hwf hres hrun
    rw [arena.expr_ops.strip_pis] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : k = 0#u64)] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [dupId_eidx _ _ he1] at hrun
    have ho := Result.ok_injective hrun
    rw [← ho, show absU k = 0 from hn, stripPis]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  | succ m ih =>
    intro pers st lst k h o hn hrel hinv hwf hres hrun
    rw [arena.expr_ops.strip_pis] at hrun
    have hne : ¬ (k = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have htag := eidx_tag_abs ht
    obtain ⟨v, hv⟩ := EResolves.dest hres
    have htv : (absEIdx h).tag = v.tagOf := estore_view_tagOf hv
    rw [show absU k = m + 1 from hn, stripPis, StateT.run_bind,
      arena_view_run_some hv]
    by_cases hc : t = arena.handle.ETAG_FORALL_E
    · subst hc
      rw [if_pos rfl] at hrun
      have hla : (absEIdx h).tag = ETag.forallE := by rw [htag, etag_forallE_abs]
      have hbind : ETag.isBind (absEIdx h).tag = true := by
        rw [hla]; simp [ETag.isBind, ETag.lam, ETag.forallE]
      obtain ⟨ty0, b0, m0, hvb, hveq⟩ := estore_view_bind_parts hbind hv
      have hvv : v = .forallE ty0 b0 m0 := by
        rw [hveq, eBindView, hla]; simp [ETag.lam, ETag.forallE]
      subst hvv
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hqa := reader_eq (view_bind_run hrel hbind hq)
      rw [hvb] at hqa
      cases hqc : q with
      | none => rw [hqc] at hqa; simp at hqa
      | some p =>
        obtain ⟨rty, rb, rm⟩ := p
        rw [hqc] at hrun hqa
        simp only [Option.map_some, Option.some.injEq, absBindM,
          Prod.mk.injEq] at hqa
        obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi1v : i1.val = m := by
          have h1 : i1.val = k.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hi1).2
          rw [h1, hn]; rfl
        have hres' : EResolves lst b0 :=
          EResolves.child hwf hv (by simp [ENodeView.echildren])
        have hrec := ih hi1v hrel hinv hwf (by rw [← hqa.2.1]; exact hres') hr
        rw [show absU i1 = m from hi1v, ← hqa.2.1] at hrec
        show AOut absStrip (fun _ => True) pers lst o st
          ((do
            let w ← stripPis m b0
            match w with
            | some p => (pure (some ((ty0, m0) :: p.1, p.2)) :
                AM (Option (List (EIdx × ConLeche.BinderMeta) × EIdx)))
            | none => pure none).run lst)
        rw [StateT.run_bind]
        cases hrc : r with
        | Err e =>
          rw [hrc] at hrun hrec
          have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          exact AOut.err (AErrSim.bind hrec _)
        | Ok o1 =>
          rw [hrc] at hrun hrec
          obtain ⟨lst', hx, hrel', hinv', hext', -⟩ := hrec
          rw [hx]
          cases ho1 : o1 with
          | none =>
            rw [ho1] at hrun hx
            have ho : (core.result.Result.Ok (none :
                Option ((alloc.vec.Vec (arena.handle.EIdx ×
                  kernel.expr.BinderMeta)) × arena.handle.EIdx)) :
                core.result.Result _ _) = o := Result.ok_injective hrun
            rw [← ho]
            exact AOut.ok rfl hrel' hinv' hext' trivial
          | some pp =>
            obtain ⟨vv, ee⟩ := pp
            rw [ho1] at hrun hx
            obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok (some (v1, ee)) :
                core.result.Result _ _) = o := Result.ok_injective hrun
            rw [← ho]
            refine AOut.ok ?_ hrel' hinv' hext' trivial
            show Except.ok (some ((ty0, m0) :: absBinders vv, absEIdx ee), lst')
              = Except.ok (absStrip (some (v1, ee)), lst')
            rw [show absStrip (some (v1, ee))
                = some (absBinders v1, absEIdx ee) from rfl,
              absBinders_eq v1, cons_binder_refines hv1, hqa.1, hqa.2.2]
            rfl
    · rw [if_neg hc] at hrun
      have ho : (core.result.Result.Ok (none :
          Option ((alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) ×
            arena.handle.EIdx)) : core.result.Result _ _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      have hnef : v.tagOf ≠ ETag.forallE := by
        rw [← htv, htag, ← etag_forallE_abs]
        intro hcc; exact hc (absU32_inj hcc)
      cases v <;>
        first
          | (exact absurd rfl hnef)
          | exact AOut.ok rfl hrel hinv (Ext.refl _) trivial

theorem strip_pis_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {k : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : StoreWF lst.store) (hres : EResolves lst (absEIdx h))
    (hrun : arena.expr_ops.strip_pis pers st k h = ok o) :
    AOut absStrip (fun _ => True) pers lst o st
      ((stripPis (absU k) (absEIdx h)).run lst) :=
  strip_pis_aux k.val rfl hrel hinv hwf hres hrun


/-! ## The three arm-dispatch transcriptions

`wscoped_b_node`, `fvar_leaves_node` and `leaves_sub_node` are three of task
#97-P6-2's Rust-only splits and have no named twin, so each gets a local
transcription of the twin's own `match` plus a `*_unfold` equation tying it
back.  They are hoisted here, ahead of the machinery that consumes them. -/

/-- **The twin's arm dispatch of `wscopedBGo`, transcribed** — `wscoped_b_node`
has no named twin (one of task #97-P6-2's fifteen Rust-only splits), so the
statement needs the fragment as an object.  The equation to the twin is
`wscopedBGo_unfold` below. -/
def wscopedBNodeSpec (memo : Std.HashMap (EIdx × Nat) Bool) (fuel d : Nat) :
    ENodeView → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (true, memo)
  | .fvar idx ty =>
    if idx < d then wscopedBGo memo fuel idx ty else pure (false, memo)
  | .app f a => do
    let (rf, memo) ← wscopedBGo memo fuel d f
    if rf then wscopedBGo memo fuel d a else pure (false, memo)
  | .lam ty body _ => do
    let (rt, memo) ← wscopedBGo memo fuel d ty
    if rt then wscopedBGo memo fuel d body else pure (false, memo)
  | .forallE ty body _ => do
    let (rt, memo) ← wscopedBGo memo fuel d ty
    if rt then wscopedBGo memo fuel d body else pure (false, memo)
  | .letE ty val body => do
    let (rt, memo) ← wscopedBGo memo fuel d ty
    if rt then do
      let (rv, memo) ← wscopedBGo memo fuel d val
      if rv then wscopedBGo memo fuel d body else pure (false, memo)
    else pure (false, memo)
  | .proj _ _ sub => wscopedBGo memo fuel d sub

/-- **The twin's arm dispatch of `fvarLeavesGo`, transcribed** — `fvar_leaves_node`
has no named twin.  Note that the twin inserts into `seen` BEFORE the
dispatch, so the fragment takes the already-extended set, which is what the
Rust's `fvl_record` has done by the time it calls this. -/
def fvarLeavesNodeSpec (acc : List (Nat × EIdx)) (seen : Std.HashMap EIdx Unit)
    (fuel : Nat) : ENodeView → AM (List (Nat × EIdx) × Std.HashMap EIdx Unit)
  | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (acc, seen)
  | .fvar idx ty => fvarLeavesGo ((idx, ty) :: acc) seen fuel ty
  | .app f a => do
    let (acc, seen) ← fvarLeavesGo acc seen fuel f
    fvarLeavesGo acc seen fuel a
  | .lam ty body _ => do
    let (acc, seen) ← fvarLeavesGo acc seen fuel ty
    fvarLeavesGo acc seen fuel body
  | .forallE ty body _ => do
    let (acc, seen) ← fvarLeavesGo acc seen fuel ty
    fvarLeavesGo acc seen fuel body
  | .letE ty val body => do
    let (acc, seen) ← fvarLeavesGo acc seen fuel ty
    let (acc, seen) ← fvarLeavesGo acc seen fuel val
    fvarLeavesGo acc seen fuel body
  | .proj _ _ sub => fvarLeavesGo acc seen fuel sub

/-- **The twin's arm dispatch of `leavesSubGo`, transcribed** —
`leaves_sub_node` has no named twin. -/
def leavesSubNodeSpec (bl : List (Nat × EIdx)) (memo : Std.HashMap EIdx Bool)
    (fuel : Nat) : ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (true, memo)
  | .fvar idx ty =>
    if leafMem bl idx ty then leavesSubGo bl memo fuel ty
    else pure (false, memo)
  | .app f a => do
    let (rf, memo) ← leavesSubGo bl memo fuel f
    if rf then leavesSubGo bl memo fuel a else pure (false, memo)
  | .lam ty body _ => do
    let (rt, memo) ← leavesSubGo bl memo fuel ty
    if rt then leavesSubGo bl memo fuel body else pure (false, memo)
  | .forallE ty body _ => do
    let (rt, memo) ← leavesSubGo bl memo fuel ty
    if rt then leavesSubGo bl memo fuel body else pure (false, memo)
  | .letE ty val body => do
    let (rt, memo) ← leavesSubGo bl memo fuel ty
    if rt then do
      let (rv, memo) ← leavesSubGo bl memo fuel val
      if rv then leavesSubGo bl memo fuel body else pure (false, memo)
    else pure (false, memo)
  | .proj _ _ sub => leavesSubGo bl memo fuel sub

/-! ## The memo-threading machinery (finding 2), and the three-body induction

`wscoped_b_{go,node,two}` is ONE `mutual` block in the Rust and one in the
twin, and the three bodies call each other at the SAME fuel except for
`go → node`, which decrements.  So the induction is on `go` alone
(`WGoAt`/`LGoAt`) and `two`/`node` are *derived at the same fuel* from it
(`wscoped_two_of_go`, `wscoped_node_of_go`) — which is the shape the Core
tier's `KnotRel` will want, one rung up.

The predicate `WGoAt n` has to be a `def` rather than an inline `∀`: a `have
htwo := wscoped_two_of_go hgo` instantiates the implicit binders of an inline
`∀` eagerly and then has nothing to apply.  That is the one idiom rule this
group added.

`wscopedBGo_unfold` / `leavesSubGo_unfold` are the twin-side equations that
make `wscopedBNodeSpec` / `leavesSubNodeSpec` the node step: they are
`<f>_succ` plus `bind_assoc` plus the arm `def`s, and the `bind_assoc` has to
come AFTER the arm identification — `simp` pushes the continuation into the
`match` arms otherwise and the spec no longer matches. -/

/-! ## `wscopedBGo`: the twin's arm dispatch identified with `wscopedBNodeSpec` -/

/-- The twin's own `match` at `wscopedBGo`'s node step IS
`wscopedBNodeSpec` — one `cases` and the three arm `def`s. -/
theorem wscopedBNodeSpec_eq (memo : Std.HashMap (EIdx × Nat) Bool)
    (fuel d : Nat) (w : ENodeView) :
    (match w with
      | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (true, memo)
      | .fvar idx ty =>
        if idx < d then wscopedBGo memo fuel idx ty else pure (false, memo)
      | .app f a => wscopedBGoArmApp memo fuel d f a
      | .lam ty body _ => wscopedBGoArmBind memo fuel d ty body
      | .forallE ty body _ => wscopedBGoArmBind memo fuel d ty body
      | .letE ty val body => wscopedBGoArmLet memo fuel d ty val body
      | .proj _ _ sub => wscopedBGo memo fuel d sub)
      = wscopedBNodeSpec memo fuel d w := by
  cases w <;>
    simp only [wscopedBNodeSpec, wscopedBGoArmApp, wscopedBGoArmBind,
      wscopedBGoArmLet]

theorem wscopedBGo_unfold (memo : Std.HashMap (EIdx × Nat) Bool) (fuel d : Nat) (h : EIdx) :
    wscopedBGo memo (fuel + 1) d h = (do
      if (ConLeche.fvarOfData (← derivedE h)).toNat == 0 then pure (true, memo)
      else
        match memo[(h, d)]? with
        | some r => pure (r, memo)
        | none => do
          let (r, memo') ← wscopedBNodeSpec memo fuel d (← view h)
          pure (r, memo'.insert (h, d) r)) := by
  rw [wscopedBGo_succ]
  simp only [wscopedBNodeSpec, wscopedBGoArmApp, wscopedBGoArmBind,
    wscopedBGoArmLet, bind_assoc]
  congr 1
  funext w
  split
  · rfl
  · cases hme : memo[(h, d)]? with
    | some r => rfl
    | none =>
      dsimp only
      congr 1
      funext v
      cases v <;> dsimp only <;> (try split) <;>
        first
          | rfl
          | simp only [bind_assoc]

/-! ### The two `WOut` combinators -/

theorem wout_err_bind {e : kernel.core_types.CheckError}
    {pers : arena.store.PersTier} {lstA lstB : AState}
    {stA stB : arena.monad.AState}
    {x : AM (Bool × Std.HashMap (EIdx × Nat) Bool)}
    {f : (Bool × Std.HashMap (EIdx × Nat) Bool) →
      AM (Bool × Std.HashMap (EIdx × Nat) Bool)}
    (h : WOut pers lstA (.Err e) stA (x.run lstA)) :
    WOut pers lstB (.Err e) stB ((do let v ← x; f v).run lstA) := by
  show AErrSim e _
  rw [StateT.run_bind]
  exact AErrSim.bind h _

theorem wout_rebase {pers : arena.store.PersTier} {lst lst1 : AState}
    {st2 : arena.monad.AState}
    {o : core.result.Result
      (Bool × ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
      kernel.core_types.CheckError}
    {y : Except Arena.CheckError
      ((Bool × Std.HashMap (EIdx × Nat) Bool) × AState)}
    (hext : Ext lst.store lst1.store) (h : WOut pers lst1 o st2 y) :
    WOut pers lst o st2 y := by
  cases o with
  | Err e => exact h
  | Ok r =>
    obtain ⟨m', lst2, hy, hmm, hrel2, hinv2, hext2⟩ := h
    exact ⟨m', lst2, hy, hmm, hrel2, hinv2, Ext.trans hext hext2⟩

/-- The `go`-shaped statement at one fuel value, as a predicate, so that the
three mutually recursive bodies can be proved in the order `go`, `two`,
`node` inside one induction. -/
def WGoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {fuel d : Std.U64}
    {h : arena.handle.EIdx} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st → WMemoRel rm lm →
    arena.expr_ops.wscoped_b_go pers st rm fuel d h = ok o →
    WOut pers lst o st ((wscopedBGo lm (absU fuel) (absU d) (absEIdx h)).run lst)

/-- The `two`-shaped statement at one fuel value. -/
def WTwoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {fuel d : Std.U64}
    {x y : arena.handle.EIdx} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st → WMemoRel rm lm →
    arena.expr_ops.wscoped_b_two pers st rm fuel d x y = ok o →
    WOut pers lst o st ((do
      let (rf, m) ← wscopedBGo lm (absU fuel) (absU d) (absEIdx x)
      if rf then wscopedBGo m (absU fuel) (absU d) (absEIdx y)
      else pure (false, m)).run lst)

/-- The `node`-shaped statement at one fuel value. -/
def WNodeAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {fuel d : Std.U64}
    {v : arena.store.ENodeView} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st → WMemoRel rm lm →
    arena.expr_ops.wscoped_b_node pers st rm fuel d v = ok o →
    WOut pers lst o st
      ((wscopedBNodeSpec lm (absU fuel) (absU d) (absENodeView v)).run lst)

private theorem wscoped_two_of_go {n : Nat} (hgo : WGoAt n) : WTwoAt n := by
  intro pers st lst rm lm fuel d x y o hn hrel hinv hm hrun
  rw [arena.expr_ops.wscoped_b_two] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hg1 := hgo hn hrel hinv hm hr
  cases hrc : r with
  | Err e =>
    rw [hrc] at hrun hg1
    have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
      Result.ok_injective hrun
    rw [← ho]
    exact wout_err_bind hg1
  | Ok p =>
    obtain ⟨b, mr⟩ := p
    rw [hrc] at hrun hg1
    obtain ⟨m1, lst1, heq, hm1, hrel1, hinv1, hext1⟩ := hg1
    rw [StateT.run_bind, heq]
    show WOut pers lst o st
      ((if b then wscopedBGo m1 (absU fuel) (absU d) (absEIdx y)
        else pure (false, m1)).run lst1)
    by_cases hb : b = true
    · subst hb
      have hg2 := hgo hn hrel1 hinv1 hm1 hrun
      exact wout_rebase hext1 hg2
    · simp only [Bool.not_eq_true] at hb
      subst hb
      have ho : (core.result.Result.Ok (false, mr) :
          core.result.Result _ _) = o := Result.ok_injective hrun
      rw [← ho]
      exact ⟨m1, lst1, rfl, hm1, hrel1, hinv1, hext1⟩

private theorem wscoped_node_of_go {n : Nat} (hgo : WGoAt n) : WNodeAt n := by
  have htwo : WTwoAt n := wscoped_two_of_go hgo
  intro pers st lst rm lm fuel d v o hn hrel hinv hm hrun
  rw [arena.expr_ops.wscoped_b_node.eq_def] at hrun
  cases v with
  | BVar _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
  | «Sort» _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
  | Const _ _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
  | Lit _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
  | Proj _ _ s0 => exact hgo hn hrel hinv hm hrun
  | App f0 a0 => exact htwo hn hrel hinv hm hrun
  | Lam ty0 b0 mm => exact htwo hn hrel hinv hm hrun
  | ForallE ty0 b0 mm => exact htwo hn hrel hinv hm hrun
  | FVar idx0 ty0 =>
    have hrun2 : (if idx0 < d then
        arena.expr_ops.wscoped_b_go pers st rm fuel idx0 ty0
      else ok (core.result.Result.Ok (false, rm))) = ok o := by
      simpa using hrun
    show WOut pers lst o st
      ((if absU idx0 < absU d then wscopedBGo lm (absU fuel) (absU idx0) (absEIdx ty0)
        else pure (false, lm)).run lst)
    by_cases hlt : idx0 < d
    · rw [if_pos hlt] at hrun2
      rw [if_pos (show absU idx0 < absU d from hlt)]
      exact hgo hn hrel hinv hm hrun2
    · rw [if_neg hlt] at hrun2
      rw [if_neg (show ¬ (absU idx0 < absU d) from hlt)]
      have ho := Result.ok_injective hrun2
      rw [← ho]
      exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
  | LetE ty0 v0 b0 =>
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hg1 := hgo hn hrel hinv hm hr
    show WOut pers lst o st ((do
      let (rt, memo) ← wscopedBGo lm (absU fuel) (absU d) (absEIdx ty0)
      if rt then do
        let (rv, memo) ← wscopedBGo memo (absU fuel) (absU d) (absEIdx v0)
        if rv then wscopedBGo memo (absU fuel) (absU d) (absEIdx b0)
        else pure (false, memo)
      else pure (false, memo)).run lst)
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hg1
      have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact wout_err_bind hg1
    | Ok p =>
      obtain ⟨b, mr⟩ := p
      rw [hrc] at hrun hg1
      obtain ⟨m1, lst1, heq, hm1, hrel1, hinv1, hext1⟩ := hg1
      rw [StateT.run_bind, heq]
      show WOut pers lst o st
        ((if b then do
            let (rv, memo) ← wscopedBGo m1 (absU fuel) (absU d) (absEIdx v0)
            if rv then wscopedBGo memo (absU fuel) (absU d) (absEIdx b0)
            else pure (false, memo)
          else pure (false, m1)).run lst1)
      by_cases hb : b = true
      · subst hb
        exact wout_rebase hext1 (htwo hn hrel1 hinv1 hm1 hrun)
      · simp only [Bool.not_eq_true] at hb
        subst hb
        have ho : (core.result.Result.Ok (false, mr) :
            core.result.Result _ _) = o := Result.ok_injective hrun
        rw [← ho]
        exact ⟨m1, lst1, rfl, hm1, hrel1, hinv1, hext1⟩

private theorem wscoped_go_aux (n : Nat) : WGoAt n := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel d h o hn hrel hinv hm hrun
    rw [arena.expr_ops.wscoped_b_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    show AErrSim _ ((wscopedBGo lm (absU fuel) (absU d) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, wscopedBGo_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst rm lm fuel d h o hn hrel hinv hm hrun
    rw [arena.expr_ops.wscoped_b_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨w, hw, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hder := hw
    rw [arena.monad.derived_e] at hder
    obtain ⟨-, hfv, -⟩ := derObsE_fields (estore_derived_abs hrel.store hder)
    have hi1v := ConRon.Refine.Expr.fvar_of_data_val hi1
    have hfz : (ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat = i1.val := by
      rw [hfv, hi1v]
    rw [show absU fuel = m + 1 from hn, wscopedBGo_unfold, StateT.run_bind,
      show (Arena.derivedE (absEIdx h)).run lst
        = .ok (lst.store.derived (absEIdx h), lst) from rfl]
    show WOut pers lst o st
      ((if ((ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat == 0) = true
        then pure (true, lm)
        else
          match lm[(absEIdx h, absU d)]? with
          | some r => pure (r, lm)
          | none => do
            let (r, memo') ← wscopedBNodeSpec lm m (absU d) (← view (absEIdx h))
            pure (r, memo'.insert (absEIdx h, absU d) r)).run lst)
    by_cases hc : i1 = 0#u64
    · rw [if_pos hc] at hrun
      have hz : ((ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat == 0)
          = true := by rw [hfz, hc]; rfl
      rw [if_pos hz]
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
    · rw [if_neg hc] at hrun
      have hz : ¬ (((ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat == 0)
          = true) := by
        rw [hfz]
        simp only [beq_iff_eq]
        intro hzz
        exact hc (Std.UScalar.eq_of_val_eq (by rw [hzz]; rfl))
      rw [if_neg hz]
      obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hkabs : absEIdxNat k = (absEIdx h, absU d) := by
        rw [arena.monad.eidx_nat_key] at hk
        obtain ⟨e, he, hk⟩ := ConRon.Refine.bind_eq_ok_iff.mp hk
        have hee : e = h := dupId_eidx h e he
        have hkk : ({ h := e, d := d } : arena.monad.EIdxNat) = k :=
          Result.ok_injective hk
        rw [← hkk, hee]; rfl
      have hget := wscoped_memo_get_refines hm.2
        ConRon.Refine.HashMap2.KeysOk_true hm.1 hop
      rw [hkabs] at hget
      cases hoc : op with
      | some b =>
        rw [hoc] at hrun hget
        rw [hget]
        have ho : (core.result.Result.Ok (b, rm) :
            core.result.Result _ _) = o := Result.ok_injective hrun
        rw [← ho]
        exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
      | none =>
        rw [hoc] at hrun hget
        rw [hget]
        obtain ⟨rv, hrv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hview := view_run hrel hinv hrv
        show WOut pers lst o st ((do
          let (r, memo') ← wscopedBNodeSpec lm m (absU d) (← view (absEIdx h))
          pure (r, memo'.insert (absEIdx h, absU d) r)).run lst)
        cases hrvc : rv with
        | Err e =>
          rw [hrvc] at hrun hview
          have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          show AErrSim e _
          rw [StateT.run_bind]
          intro kk hk2
          obtain ⟨le, hle, hlk⟩ := hview kk hk2
          exact ⟨le, by rw [hle]; rfl, hlk⟩
        | Ok v =>
          rw [hrvc] at hrun hview
          obtain ⟨lst0, hx, -, -, -, -⟩ := hview
          have hlst : lst0 = lst := view_run_state hx
          rw [hlst] at hx
          rw [StateT.run_bind, hx]
          obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v : i2.val = m := by
            have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
              (ConRon.Refine.Nat.usub_val hi2).2
            rw [h1, hn]; rfl
          have hnode := wscoped_node_of_go ih hi2v hrel hinv hm hr1
          rw [show absU i2 = m from hi2v] at hnode
          show WOut pers lst o st ((do
            let (r, memo') ← wscopedBNodeSpec lm m (absU d) (absENodeView v)
            pure (r, memo'.insert (absEIdx h, absU d) r)).run lst)
          cases hr1c : r1 with
          | Err e =>
            rw [hr1c] at hrun hnode
            have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
              Result.ok_injective hrun
            rw [← ho]
            exact wout_err_bind hnode
          | Ok p =>
            obtain ⟨b, mr⟩ := p
            rw [hr1c] at hrun hnode
            obtain ⟨m1, lst1, heq, hm1, hrel1, hinv1, hext1⟩ := hnode
            rw [StateT.run_bind, heq]
            obtain ⟨mset, hmset, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok (b, mset) :
                core.result.Result _ _) = o := Result.ok_injective hrun
            rw [← ho]
            have hset := wscoped_memo_set_refines hm1.2
              ConRon.Refine.HashMap2.KeysOk_true hm1.1 hmset
            rw [hkabs] at hset
            exact ⟨m1.insert (absEIdx h, absU d) b, lst1, rfl,
              ⟨hset.1, hset.2.1⟩, hrel1, hinv1, hext1⟩

theorem lout_err_bind {e : kernel.core_types.CheckError}
    {pers : arena.store.PersTier} {lstA lstB : AState}
    {stA stB : arena.monad.AState}
    {x : AM (Bool × Std.HashMap EIdx Bool)}
    {f : (Bool × Std.HashMap EIdx Bool) → AM (Bool × Std.HashMap EIdx Bool)}
    (h : LOut pers lstA (.Err e) stA (x.run lstA)) :
    LOut pers lstB (.Err e) stB ((do let v ← x; f v).run lstA) := by
  show AErrSim e _
  rw [StateT.run_bind]
  exact AErrSim.bind h _

theorem lout_rebase {pers : arena.store.PersTier} {lst lst1 : AState}
    {st2 : arena.monad.AState}
    {o : core.result.Result
      (Bool × ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      kernel.core_types.CheckError}
    {y : Except Arena.CheckError ((Bool × Std.HashMap EIdx Bool) × AState)}
    (hext : Ext lst.store lst1.store) (h : LOut pers lst1 o st2 y) :
    LOut pers lst o st2 y := by
  cases o with
  | Err e => exact h
  | Ok r =>
    obtain ⟨m', lst2, hy, hmm, hrel2, hinv2, hext2⟩ := h
    exact ⟨m', lst2, hy, hmm, hrel2, hinv2, Ext.trans hext hext2⟩

/-- The twin's own `match` at `leavesSubGo`'s node step IS
`leavesSubNodeSpec`. -/
theorem leavesSubNodeSpec_eq (bl : List (Nat × EIdx))
    (memo : Std.HashMap EIdx Bool) (fuel : Nat) (w : ENodeView) :
    (match w with
      | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (true, memo)
      | .fvar idx ty =>
        if leafMem bl idx ty then leavesSubGo bl memo fuel ty
        else pure (false, memo)
      | .app f a => leavesSubArmApp bl memo fuel f a
      | .lam ty body _ => leavesSubArmBind bl memo fuel ty body
      | .forallE ty body _ => leavesSubArmBind bl memo fuel ty body
      | .letE ty val body => leavesSubArmLet bl memo fuel ty val body
      | .proj _ _ sub => leavesSubGo bl memo fuel sub)
      = leavesSubNodeSpec bl memo fuel w := by
  cases w <;>
    simp only [leavesSubNodeSpec, leavesSubArmApp, leavesSubArmBind,
      leavesSubArmLet]

theorem leavesSubGo_unfold (bl : List (Nat × EIdx))
    (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) :
    leavesSubGo bl memo (fuel + 1) h = (do
      if (ConLeche.fvarOfData (← derivedE h)).toNat == 0 then pure (true, memo)
      else
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, memo') ← leavesSubNodeSpec bl memo fuel (← view h)
          pure (r, memo'.insert h r)) := by
  rw [leavesSubGo_succ]
  simp only [leavesSubNodeSpec, leavesSubArmApp, leavesSubArmBind,
    leavesSubArmLet, bind_assoc]
  congr 1
  funext w
  split
  · rfl
  · cases hme : memo[h]? with
    | some r => rfl
    | none =>
      dsimp only
      congr 1
      funext v
      cases v <;> dsimp only <;> (try split) <;>
        first
          | rfl
          | simp only [bind_assoc]

/-- **`leafMem` is append blind.** -/
theorem leafMem_app (l1 l2 : List (Nat × EIdx)) (i : Nat) (t : EIdx) :
    leafMem (l1 ++ l2) i t = (leafMem l1 i t || leafMem l2 i t) := by
  induction l1 with
  | nil => simp [leafMem]
  | cons p r ih =>
    rw [List.cons_append, leafMem_cons, leafMem_cons, ih, Bool.or_assoc]

/-- **`leafMem` is order blind**, which is what makes `fvar_leaves_go`'s
push-order deviation (finding 12) sound at its one reader. -/
theorem leafMem_reverse (l : List (Nat × EIdx)) (i : Nat) (t : EIdx) :
    leafMem l.reverse i t = leafMem l i t := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    rw [List.reverse_cons, leafMem_app, ih, leafMem_cons, leafMem_cons,
      leafMem, Bool.or_false, Bool.or_comm]

/-- The `go`-shaped statement at one fuel value, as a predicate, so that the
three mutually recursive bodies can be proved in the order `go`, `two`,
`node` inside one induction. -/
def LGoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {lbl : List (Nat × EIdx)} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o},
    fuel.val = n → (∀ i t, leafMem lbl i t = leafMem (absFvlL bl) i t) →
    AStateRel pers st lst → AStateInv pers st → LMemoRel rm lm →
    arena.expr_ops.leaves_sub_go pers st bl rm fuel h = ok o →
    LOut pers lst o st ((leavesSubGo lbl lm (absU fuel) (absEIdx h)).run lst)

/-- The `two`-shaped statement at one fuel value. -/
def LTwoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {lbl : List (Nat × EIdx)} {fuel : Std.U64}
    {x y : arena.handle.EIdx} {o},
    fuel.val = n → (∀ i t, leafMem lbl i t = leafMem (absFvlL bl) i t) →
    AStateRel pers st lst → AStateInv pers st → LMemoRel rm lm →
    arena.expr_ops.leaves_sub_two pers st bl rm fuel x y = ok o →
    LOut pers lst o st ((do
      let (rf, m) ← leavesSubGo lbl lm (absU fuel) (absEIdx x)
      if rf then leavesSubGo lbl m (absU fuel) (absEIdx y)
      else pure (false, m)).run lst)

/-- The `node`-shaped statement at one fuel value. -/
def LNodeAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {lbl : List (Nat × EIdx)} {fuel : Std.U64}
    {v : arena.store.ENodeView} {o},
    fuel.val = n → (∀ i t, leafMem lbl i t = leafMem (absFvlL bl) i t) →
    AStateRel pers st lst → AStateInv pers st → LMemoRel rm lm →
    arena.expr_ops.leaves_sub_node pers st bl rm fuel v = ok o →
    LOut pers lst o st
      ((leavesSubNodeSpec lbl lm (absU fuel) (absENodeView v)).run lst)

private theorem lsub_two_of_go {n : Nat} (hgo : LGoAt n) : LTwoAt n := by
  intro pers st lst rm lm bl lbl fuel x y o hn hbl hrel hinv hm hrun
  rw [arena.expr_ops.leaves_sub_two] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hg1 := hgo hn hbl hrel hinv hm hr
  cases hrc : r with
  | Err e =>
    rw [hrc] at hrun hg1
    have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
      Result.ok_injective hrun
    rw [← ho]
    exact lout_err_bind hg1
  | Ok p =>
    obtain ⟨b, mr⟩ := p
    rw [hrc] at hrun hg1
    obtain ⟨m1, lst1, heq, hm1, hrel1, hinv1, hext1⟩ := hg1
    rw [StateT.run_bind, heq]
    show LOut pers lst o st
      ((if b then leavesSubGo lbl m1 (absU fuel) (absEIdx y)
        else pure (false, m1)).run lst1)
    by_cases hb : b = true
    · subst hb
      have hg2 := hgo hn hbl hrel1 hinv1 hm1 hrun
      exact lout_rebase hext1 hg2
    · simp only [Bool.not_eq_true] at hb
      subst hb
      have ho : (core.result.Result.Ok (false, mr) :
          core.result.Result _ _) = o := Result.ok_injective hrun
      rw [← ho]
      exact ⟨m1, lst1, rfl, hm1, hrel1, hinv1, hext1⟩

private theorem lsub_node_of_go {n : Nat} (hgo : LGoAt n) : LNodeAt n := by
  have htwo : LTwoAt n := lsub_two_of_go hgo
  intro pers st lst rm lm bl lbl fuel v o hn hbl hrel hinv hm hrun
  rw [arena.expr_ops.leaves_sub_node.eq_def] at hrun
  cases v with
  | BVar _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
  | «Sort» _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
  | Const _ _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
  | Lit _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
  | Proj _ _ s0 => exact hgo hn hbl hrel hinv hm hrun
  | App f0 a0 => exact htwo hn hbl hrel hinv hm hrun
  | Lam ty0 b0 mm => exact htwo hn hbl hrel hinv hm hrun
  | ForallE ty0 b0 mm => exact htwo hn hbl hrel hinv hm hrun
  | FVar idx0 ty0 =>
    obtain ⟨b0, hb0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hlm := leaf_mem_refines hb0
    show LOut pers lst o st
      ((if leafMem lbl (absU idx0) (absEIdx ty0) then
          leavesSubGo lbl lm (absU fuel) (absEIdx ty0)
        else pure (false, lm)).run lst)
    rw [hbl (absU idx0) (absEIdx ty0), hlm]
    by_cases hb : b0 = true
    · subst hb
      rw [if_pos rfl] at hrun
      simp only [if_true]
      exact hgo hn hbl hrel hinv hm hrun
    · simp only [Bool.not_eq_true] at hb
      subst hb
      simp only [Bool.false_eq_true, if_false]
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
  | LetE ty0 v0 b0 =>
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hg1 := hgo hn hbl hrel hinv hm hr
    show LOut pers lst o st ((do
      let (rt, memo) ← leavesSubGo lbl lm (absU fuel) (absEIdx ty0)
      if rt then do
        let (rv, memo) ← leavesSubGo lbl memo (absU fuel) (absEIdx v0)
        if rv then leavesSubGo lbl memo (absU fuel) (absEIdx b0)
        else pure (false, memo)
      else pure (false, memo)).run lst)
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hg1
      have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact lout_err_bind hg1
    | Ok p =>
      obtain ⟨b, mr⟩ := p
      rw [hrc] at hrun hg1
      obtain ⟨m1, lst1, heq, hm1, hrel1, hinv1, hext1⟩ := hg1
      rw [StateT.run_bind, heq]
      show LOut pers lst o st
        ((if b then do
            let (rv, memo) ← leavesSubGo lbl m1 (absU fuel) (absEIdx v0)
            if rv then leavesSubGo lbl memo (absU fuel) (absEIdx b0)
            else pure (false, memo)
          else pure (false, m1)).run lst1)
      by_cases hb : b = true
      · subst hb
        exact lout_rebase hext1 (htwo hn hbl hrel1 hinv1 hm1 hrun)
      · simp only [Bool.not_eq_true] at hb
        subst hb
        have ho : (core.result.Result.Ok (false, mr) :
            core.result.Result _ _) = o := Result.ok_injective hrun
        rw [← ho]
        exact ⟨m1, lst1, rfl, hm1, hrel1, hinv1, hext1⟩

private theorem lsub_go_aux (n : Nat) : LGoAt n := by
  induction n with
  | zero =>
    intro pers st lst rm lm bl lbl fuel h o hn hbl hrel hinv hm hrun
    rw [arena.expr_ops.leaves_sub_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    show AErrSim _ ((leavesSubGo lbl lm (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, leavesSubGo_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst rm lm bl lbl fuel h o hn hbl hrel hinv hm hrun
    rw [arena.expr_ops.leaves_sub_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨w, hw, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hder := hw
    rw [arena.monad.derived_e] at hder
    obtain ⟨-, hfv, -⟩ := derObsE_fields (estore_derived_abs hrel.store hder)
    have hi1v := ConRon.Refine.Expr.fvar_of_data_val hi1
    have hfz : (ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat = i1.val := by
      rw [hfv, hi1v]
    rw [show absU fuel = m + 1 from hn, leavesSubGo_unfold, StateT.run_bind,
      show (Arena.derivedE (absEIdx h)).run lst
        = .ok (lst.store.derived (absEIdx h), lst) from rfl]
    show LOut pers lst o st
      ((if ((ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat == 0) = true
        then pure (true, lm)
        else
          match lm[absEIdx h]? with
          | some r => pure (r, lm)
          | none => do
            let (r, memo') ← leavesSubNodeSpec lbl lm m (← view (absEIdx h))
            pure (r, memo'.insert (absEIdx h) r)).run lst)
    by_cases hc : i1 = 0#u64
    · rw [if_pos hc] at hrun
      have hz : ((ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat == 0)
          = true := by rw [hfz, hc]; rfl
      rw [if_pos hz]
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
    · rw [if_neg hc] at hrun
      have hz : ¬ (((ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat == 0)
          = true) := by
        rw [hfz]
        simp only [beq_iff_eq]
        intro hzz
        exact hc (Std.UScalar.eq_of_val_eq (by rw [hzz]; rfl))
      rw [if_neg hz]
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hget := leaves_sub_get_refines hm.2
        ConRon.Refine.HashMap2.KeysOk_true hm.1 hop
      cases hoc : op with
      | some b =>
        rw [hoc] at hrun hget
        rw [hget]
        have ho : (core.result.Result.Ok (b, rm) :
            core.result.Result _ _) = o := Result.ok_injective hrun
        rw [← ho]
        exact ⟨lm, lst, rfl, hm, hrel, hinv, Ext.refl _⟩
      | none =>
        rw [hoc] at hrun hget
        rw [hget]
        obtain ⟨rv, hrv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hview := view_run hrel hinv hrv
        show LOut pers lst o st ((do
          let (r, memo') ← leavesSubNodeSpec lbl lm m (← view (absEIdx h))
          pure (r, memo'.insert (absEIdx h) r)).run lst)
        cases hrvc : rv with
        | Err e =>
          rw [hrvc] at hrun hview
          have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          show AErrSim e _
          rw [StateT.run_bind]
          intro kk hk2
          obtain ⟨le, hle, hlk⟩ := hview kk hk2
          exact ⟨le, by rw [hle]; rfl, hlk⟩
        | Ok v =>
          rw [hrvc] at hrun hview
          obtain ⟨lst0, hx, -, -, -, -⟩ := hview
          have hlst : lst0 = lst := view_run_state hx
          rw [hlst] at hx
          rw [StateT.run_bind, hx]
          obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v : i2.val = m := by
            have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
              (ConRon.Refine.Nat.usub_val hi2).2
            rw [h1, hn]; rfl
          have hnode := lsub_node_of_go ih hi2v hbl hrel hinv hm hr1
          rw [show absU i2 = m from hi2v] at hnode
          show LOut pers lst o st ((do
            let (r, memo') ← leavesSubNodeSpec lbl lm m (absENodeView v)
            pure (r, memo'.insert (absEIdx h) r)).run lst)
          cases hr1c : r1 with
          | Err e =>
            rw [hr1c] at hrun hnode
            have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
              Result.ok_injective hrun
            rw [← ho]
            exact lout_err_bind hnode
          | Ok p =>
            obtain ⟨b, mr⟩ := p
            rw [hr1c] at hrun hnode
            obtain ⟨m1, lst1, heq, hm1, hrel1, hinv1, hext1⟩ := hnode
            rw [StateT.run_bind, heq]
            obtain ⟨mset, hmset, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have ho : (core.result.Result.Ok (b, mset) :
                core.result.Result _ _) = o := Result.ok_injective hrun
            rw [← ho]
            have hset := leaves_sub_set_refines hm1.2
              ConRon.Refine.HashMap2.KeysOk_true hm1.1 hmset
            exact ⟨m1.insert (absEIdx h) b, lst1, rfl,
              ⟨hset.1, hset.2.1⟩, hrel1, hinv1, hext1⟩


/-! ## The memoized DAG walks (finding 2)

Three walks and their five Rust-only companions.  Each probes the derived
word's `fvarB` field first (the `O(1)` cutoff), then the memo, then the view —
and the twin does the same three in the same order, so the only shape work is
the memo relation.  **They wait on `Specs.lean`'s `derivedE` and `view`, and
on the `HashMap2` probe/insert pair (`Refine/HashMap2.lean`'s
`get_refines_wf` / `Rel_insert_wf`, which `Specs.lean` re-exports as the
memo primitives).** -/

/-- `wscoped_b_go` ⊑ `wscopedBGo`. -/
theorem wscoped_b_go_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {fuel d : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : WMemoRel rm lm)
    (hrun : arena.expr_ops.wscoped_b_go pers st rm fuel d h = ok o) :
    WOut pers lst o st
      ((wscopedBGo lm (absU fuel) (absU d) (absEIdx h)).run lst) := by
  exact wscoped_go_aux fuel.val rfl hrel hinv hm hrun

/-- `wscoped_b_node` ⊑ the twin's arm dispatch. -/
theorem wscoped_b_node_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {fuel d : Std.U64}
    {v : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : WMemoRel rm lm)
    (hrun : arena.expr_ops.wscoped_b_node pers st rm fuel d v = ok o) :
    WOut pers lst o st
      ((wscopedBNodeSpec lm (absU fuel) (absU d) (absENodeView v)).run lst) := by
  exact wscoped_node_of_go (wscoped_go_aux fuel.val) rfl hrel hinv hm hrun

/-- `wscoped_b_two` ⊑ the twin's two-child arm, INLINE (`Refine/README.md`'s
"one equation per inlined fragment"). -/
theorem wscoped_b_two_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState}
    {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} {fuel d : Std.U64}
    {x y : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : WMemoRel rm lm)
    (hrun : arena.expr_ops.wscoped_b_two pers st rm fuel d x y = ok o) :
    WOut pers lst o st ((do
      let (rf, m) ← wscopedBGo lm (absU fuel) (absU d) (absEIdx x)
      if rf then wscopedBGo m (absU fuel) (absU d) (absEIdx y)
      else pure (false, m)).run lst) := by
  exact wscoped_two_of_go (wscoped_go_aux fuel.val) rfl hrel hinv hm hrun

/-- `wscoped_b_fast` ⊑ `wscopedBFast` — one memoized walk from the empty
memo.  `Refine/HashMap2.lean`'s `Rel_empty` is the `WMemoRel` at the entry. -/
theorem wscoped_b_fast_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel d : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.wscoped_b_fast pers st fuel d h = ok o) :
    AOut id (fun _ => True) pers lst o st
      ((wscopedBFast (absU fuel) (absU d) (absEIdx h)).run lst) := by
  rw [arena.expr_ops.wscoped_b_fast] at hrun
  obtain ⟨memo, hmemo, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hnInv, -, hnNone⟩ :=
    ConRon.Refine.HashMap2.new_refines
      (HashableInst := arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable)
      hmemo
  have hm : WMemoRel memo ∅ :=
    ⟨ConRon.Refine.HashMap2.RelOn_empty hnNone, hnInv⟩
  have hgo := wscoped_b_go_refines hrel hinv hm hr
  show AOut id (fun _ => True) pers lst o st
    ((do let p ← wscopedBGo ∅ (absU fuel) (absU d) (absEIdx h); pure p.1).run lst)
  rw [StateT.run_bind]
  cases hrc : r with
  | Ok p =>
    rw [hrc] at hgo hrun
    obtain ⟨m', lst', heq, -, hrel', hinv', hext⟩ := hgo
    obtain ⟨b, m0⟩ := p
    have h2 : core.result.Result.Ok b = o := Result.ok_injective hrun
    rw [← h2]
    refine AOut.ok (lst' := lst') ?_ hrel' hinv' hext trivial
    rw [heq]
    rfl
  | Err e =>
    rw [hrc] at hgo hrun
    have h2 : core.result.Result.Err e = o := Result.ok_injective hrun
    rw [← h2]
    exact AOut.err (AErrSim.bind hgo _)

theorem fout_err_bind {e : kernel.core_types.CheckError}
    {pers : arena.store.PersTier} {lstA lstB : AState}
    {stA stB : arena.monad.AState}
    {x : AM (List (Nat × EIdx) × Std.HashMap EIdx Unit)}
    {f : (List (Nat × EIdx) × Std.HashMap EIdx Unit) →
      AM (List (Nat × EIdx) × Std.HashMap EIdx Unit)}
    (h : FOut pers lstA (.Err e) stA (x.run lstA)) :
    FOut pers lstB (.Err e) stB ((do let v ← x; f v).run lstA) := by
  show AErrSim e _
  rw [StateT.run_bind]
  exact AErrSim.bind h _

theorem fout_rebase {pers : arena.store.PersTier} {lst lst1 : AState}
    {st2 : arena.monad.AState}
    {o : core.result.Result ((alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) ×
      ron.hashmap2.HashMap2 arena.handle.EIdx Bool) kernel.core_types.CheckError}
    {y : Except Arena.CheckError
      ((List (Nat × EIdx) × Std.HashMap EIdx Unit) × AState)}
    (hext : Ext lst.store lst1.store) (h : FOut pers lst1 o st2 y) :
    FOut pers lst o st2 y := by
  cases o with
  | Err e => exact h
  | Ok r =>
    obtain ⟨s', lst2, hy, hss, hrel2, hinv2, hext2⟩ := h
    exact ⟨s', lst2, hy, hss, hrel2, hinv2, Ext.trans hext hext2⟩

/-- The twin's own `match` at `fvarLeavesGo`'s node step IS
`fvarLeavesNodeSpec`. -/
theorem fvarLeavesNodeSpec_eq (acc : List (Nat × EIdx))
    (seen : Std.HashMap EIdx Unit) (fuel : Nat) (w : ENodeView) :
    (match w with
      | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (acc, seen)
      | .fvar idx ty => fvarLeavesGo ((idx, ty) :: acc) seen fuel ty
      | .app f a => fvarLeavesGoArmApp acc seen fuel f a
      | .lam ty body _ => fvarLeavesGoArmBind acc seen fuel ty body
      | .forallE ty body _ => fvarLeavesGoArmBind acc seen fuel ty body
      | .letE ty val body => fvarLeavesGoArmLet acc seen fuel ty val body
      | .proj _ _ sub => fvarLeavesGo acc seen fuel sub)
      = fvarLeavesNodeSpec acc seen fuel w := by
  cases w <;>
    simp only [fvarLeavesNodeSpec, fvarLeavesGoArmApp, fvarLeavesGoArmBind,
      fvarLeavesGoArmLet]

theorem fvarLeavesGo_unfold (acc : List (Nat × EIdx))
    (seen : Std.HashMap EIdx Unit) (fuel : Nat) (h : EIdx) :
    fvarLeavesGo acc seen (fuel + 1) h = (do
      if (ConLeche.fvarOfData (← derivedE h)).toNat == 0 then pure (acc, seen)
      else
        match seen[h]? with
        | some _ => pure (acc, seen)
        | none => fvarLeavesNodeSpec acc (seen.insert h ()) fuel (← view h)) := by
  rw [fvarLeavesGo_succ]
  simp only [fvarLeavesNodeSpec, fvarLeavesGoArmApp, fvarLeavesGoArmBind,
    fvarLeavesGoArmLet]
  congr 1

/-- The `go`-shaped statement at one fuel value. -/
def FGoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {racc : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {rs : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashMap EIdx Unit} {fuel : Std.U64} {h : arena.handle.EIdx} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st → SeenRel rs ls →
    arena.expr_ops.fvar_leaves_go pers st racc rs fuel h = ok o →
    FOut pers lst o st
      ((fvarLeavesGo (absLeaves racc).reverse ls (absU fuel) (absEIdx h)).run lst)

/-- The `two`-shaped statement at one fuel value. -/
def FTwoAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {racc : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {rs : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashMap EIdx Unit} {fuel : Std.U64}
    {x y : arena.handle.EIdx} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st → SeenRel rs ls →
    arena.expr_ops.fvar_leaves_two pers st racc rs fuel x y = ok o →
    FOut pers lst o st ((do
      let (acc, seen) ←
        fvarLeavesGo (absLeaves racc).reverse ls (absU fuel) (absEIdx x)
      fvarLeavesGo acc seen (absU fuel) (absEIdx y)).run lst)

/-- The `node`-shaped statement at one fuel value. -/
def FNodeAt (n : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {racc : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {rs : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashMap EIdx Unit} {fuel : Std.U64}
    {v : arena.store.ENodeView} {o},
    fuel.val = n → AStateRel pers st lst → AStateInv pers st → SeenRel rs ls →
    arena.expr_ops.fvar_leaves_node pers st racc rs fuel v = ok o →
    FOut pers lst o st
      ((fvarLeavesNodeSpec (absLeaves racc).reverse ls (absU fuel)
        (absENodeView v)).run lst)

private theorem fvl_two_of_go {n : Nat} (hgo : FGoAt n) : FTwoAt n := by
  intro pers st lst racc rs ls fuel x y o hn hrel hinv hs hrun
  rw [arena.expr_ops.fvar_leaves_two] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hg1 := hgo hn hrel hinv hs hr
  cases hrc : r with
  | Err e =>
    rw [hrc] at hrun hg1
    have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
      Result.ok_injective hrun
    rw [← ho]
    exact fout_err_bind hg1
  | Ok p =>
    obtain ⟨a2, s2⟩ := p
    rw [hrc] at hrun hg1
    obtain ⟨s1, lst1, heq, hs1, hrel1, hinv1, hext1⟩ := hg1
    rw [StateT.run_bind, heq]
    show FOut pers lst o st
      ((fvarLeavesGo (absLeaves a2).reverse s1 (absU fuel) (absEIdx y)).run lst1)
    exact fout_rebase hext1 (hgo hn hrel1 hinv1 hs1 hrun)

private theorem fvl_node_of_go {n : Nat} (hgo : FGoAt n) : FNodeAt n := by
  have htwo : FTwoAt n := fvl_two_of_go hgo
  intro pers st lst racc rs ls fuel v o hn hrel hinv hs hrun
  rw [arena.expr_ops.fvar_leaves_node.eq_def] at hrun
  cases v with
  | BVar _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨ls, lst, rfl, hs, hrel, hinv, Ext.refl _⟩
  | «Sort» _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨ls, lst, rfl, hs, hrel, hinv, Ext.refl _⟩
  | Const _ _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨ls, lst, rfl, hs, hrel, hinv, Ext.refl _⟩
  | Lit _ =>
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact ⟨ls, lst, rfl, hs, hrel, hinv, Ext.refl _⟩
  | Proj _ _ s0 => exact hgo hn hrel hinv hs hrun
  | App f0 a0 => exact htwo hn hrel hinv hs hrun
  | Lam ty0 b0 mm => exact htwo hn hrel hinv hs hrun
  | ForallE ty0 b0 mm => exact htwo hn hrel hinv hs hrun
  | FVar idx0 ty0 =>
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨acc1, hacc1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hee : e1 = ty0 := dupId_eidx ty0 e1 he1
    have hav : (absLeaves acc1).reverse
        = (absU idx0, absEIdx ty0) :: (absLeaves racc).reverse := by
      unfold absLeaves
      rw [ConRon.Refine.vec_push_val hacc1, List.map_append, List.reverse_append,
        hee]
      rfl
    have hg := hgo hn hrel hinv hs hrun
    rw [hav] at hg
    exact hg
  | LetE ty0 v0 b0 =>
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hg1 := hgo hn hrel hinv hs hr
    show FOut pers lst o st ((do
      let (acc, seen) ←
        fvarLeavesGo (absLeaves racc).reverse ls (absU fuel) (absEIdx ty0)
      let (acc, seen) ← fvarLeavesGo acc seen (absU fuel) (absEIdx v0)
      fvarLeavesGo acc seen (absU fuel) (absEIdx b0)).run lst)
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hg1
      have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact fout_err_bind hg1
    | Ok p =>
      obtain ⟨a2, s2⟩ := p
      rw [hrc] at hrun hg1
      obtain ⟨s1, lst1, heq, hs1, hrel1, hinv1, hext1⟩ := hg1
      rw [StateT.run_bind, heq]
      show FOut pers lst o st ((do
        let (acc, seen) ←
          fvarLeavesGo (absLeaves a2).reverse s1 (absU fuel) (absEIdx v0)
        fvarLeavesGo acc seen (absU fuel) (absEIdx b0)).run lst1)
      exact fout_rebase hext1 (htwo hn hrel1 hinv1 hs1 hrun)

private theorem fvl_go_aux (n : Nat) : FGoAt n := by
  induction n with
  | zero =>
    intro pers st lst racc rs ls fuel h o hn hrel hinv hs hrun
    rw [arena.expr_ops.fvar_leaves_go] at hrun
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) : fuel = 0#u64)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    show AErrSim _ ((fvarLeavesGo (absLeaves racc).reverse ls
      (absU fuel) (absEIdx h)).run lst)
    rw [show absU fuel = 0 from hn, fvarLeavesGo_zero, arena_fail_run]
    exact AErrSim.internal rfl
  | succ m ih =>
    intro pers st lst racc rs ls fuel h o hn hrel hinv hs hrun
    rw [arena.expr_ops.fvar_leaves_go] at hrun
    have hne : ¬ (fuel = 0#u64) := by intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hne] at hrun
    obtain ⟨w, hw, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hder := hw
    rw [arena.monad.derived_e] at hder
    obtain ⟨-, hfv, -⟩ := derObsE_fields (estore_derived_abs hrel.store hder)
    have hi1v := ConRon.Refine.Expr.fvar_of_data_val hi1
    have hfz : (ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat = i1.val := by
      rw [hfv, hi1v]
    rw [show absU fuel = m + 1 from hn, fvarLeavesGo_unfold, StateT.run_bind,
      show (Arena.derivedE (absEIdx h)).run lst
        = .ok (lst.store.derived (absEIdx h), lst) from rfl]
    show FOut pers lst o st
      ((do
        if ((ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat == 0) = true
        then pure ((absLeaves racc).reverse, ls)
        else
          match ls[absEIdx h]? with
          | some _ => pure ((absLeaves racc).reverse, ls)
          | none =>
            fvarLeavesNodeSpec (absLeaves racc).reverse
              (ls.insert (absEIdx h) ()) m (← view (absEIdx h))).run lst)
    by_cases hc : i1 = 0#u64
    · rw [if_pos hc] at hrun
      have hz : ((ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat == 0)
          = true := by rw [hfz, hc]; rfl
      rw [if_pos hz]
      have ho := Result.ok_injective hrun
      rw [← ho]
      exact ⟨ls, lst, rfl, hs, hrel, hinv, Ext.refl _⟩
    · rw [if_neg hc] at hrun
      have hz : ¬ (((ConLeche.fvarOfData (lst.store.derived (absEIdx h))).toNat == 0)
          = true) := by
        rw [hfz]
        simp only [beq_iff_eq]
        intro hzz
        exact hc (Std.UScalar.eq_of_val_eq (by rw [hzz]; rfl))
      rw [if_neg hz]
      obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hsn := fvl_seen_refines hs.2 ConRon.Refine.HashMap2.KeysOk_true hs.1 hb
      cases hlk : ls[absEIdx h]? with
      | some u =>
        have hbt : b = true := by
          rw [hsn, Std.HashMap.contains_eq_isSome_getElem?, hlk]; rfl
        rw [hbt] at hrun
        rw [if_pos rfl] at hrun
        have ho := Result.ok_injective hrun
        rw [← ho]
        exact ⟨ls, lst, rfl, hs, hrel, hinv, Ext.refl _⟩
      | none =>
        have hbf : b = false := by
          rw [hsn, Std.HashMap.contains_eq_isSome_getElem?, hlk]; rfl
        rw [hbf] at hrun
        rw [if_neg (by simp)] at hrun
        simp only [Bool.false_eq_true, if_false]
        obtain ⟨rv, hrv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hview := view_run hrel hinv hrv
        cases hrvc : rv with
        | Err e =>
          rw [hrvc] at hrun hview
          have ho : (core.result.Result.Err e : core.result.Result _ _) = o :=
            Result.ok_injective hrun
          rw [← ho]
          show AErrSim e _
          rw [StateT.run_bind]
          intro kk hk2
          obtain ⟨le, hle, hlk2⟩ := hview kk hk2
          exact ⟨le, by rw [hle]; rfl, hlk2⟩
        | Ok v =>
          rw [hrvc] at hrun hview
          obtain ⟨lst0, hx, -, -, -, -⟩ := hview
          have hlst : lst0 = lst := view_run_state hx
          rw [hlst] at hx
          rw [StateT.run_bind, hx]
          obtain ⟨hm, hhm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi2v : i2.val = m := by
            have h1 : i2.val = fuel.val - (1#u64 : Std.U64).val :=
              (ConRon.Refine.Nat.usub_val hi2).2
            rw [h1, hn]; rfl
          have hrec := fvl_record_refines hs.2
            ConRon.Refine.HashMap2.KeysOk_true hs.1 hhm
          have hs' : SeenRel hm (ls.insert (absEIdx h) ()) :=
            ⟨hrec.1, hrec.2.1⟩
          have hnode := fvl_node_of_go ih hi2v hrel hinv hs' hrun
          rw [show absU i2 = m from hi2v] at hnode
          exact hnode

/-- `fvar_leaves_go` ⊑ `fvarLeavesGo`. -/
theorem fvar_leaves_go_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState}
    {racc : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {rs : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashMap EIdx Unit} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hs : SeenRel rs ls)
    (hrun : arena.expr_ops.fvar_leaves_go pers st racc rs fuel h = ok o) :
    FOut pers lst o st
      ((fvarLeavesGo (absLeaves racc).reverse ls (absU fuel)
        (absEIdx h)).run lst) :=
  fvl_go_aux fuel.val rfl hrel hinv hs hrun

/-- `fvar_leaves_node` ⊑ the twin's arm dispatch. -/
theorem fvar_leaves_node_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState}
    {racc : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {rs : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashMap EIdx Unit} {fuel : Std.U64}
    {v : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hs : SeenRel rs ls)
    (hrun : arena.expr_ops.fvar_leaves_node pers st racc rs fuel v = ok o) :
    FOut pers lst o st
      ((fvarLeavesNodeSpec (absLeaves racc).reverse ls (absU fuel)
        (absENodeView v)).run lst) :=
  fvl_node_of_go (fvl_go_aux fuel.val) rfl hrel hinv hs hrun

/-- `fvar_leaves_two` ⊑ the twin's two-child arm, inline. -/
theorem fvar_leaves_two_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState}
    {racc : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {rs : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashMap EIdx Unit} {fuel : Std.U64}
    {x y : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hs : SeenRel rs ls)
    (hrun : arena.expr_ops.fvar_leaves_two pers st racc rs fuel x y = ok o) :
    FOut pers lst o st ((do
      let (acc, seen) ←
        fvarLeavesGo (absLeaves racc).reverse ls (absU fuel) (absEIdx x)
      fvarLeavesGo acc seen (absU fuel) (absEIdx y)).run lst) :=
  fvl_two_of_go (fvl_go_aux fuel.val) rfl hrel hinv hs hrun

/-- `fvar_leaves_fast` ⊑ `fvarLeavesFast`. -/
theorem fvar_leaves_fast_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_leaves_fast pers st fuel h = ok o) :
    AOut (fun v => (absLeaves v).reverse) (fun _ => True) pers lst o st
      ((fvarLeavesFast (absU fuel) (absEIdx h)).run lst) := by
  rw [arena.expr_ops.fvar_leaves_fast] at hrun
  obtain ⟨seen, hseen, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hnInv, -, hnNone⟩ :=
    ConRon.Refine.HashMap2.new_refines
      (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable)
      hseen
  have hs : SeenRel seen ∅ :=
    ⟨ConRon.Refine.HashMap2.RelOn_empty hnNone, hnInv⟩
  have hacc : (absLeaves (alloc.vec.Vec.new (Std.U64 × arena.handle.EIdx))).reverse
      = [] := rfl
  have hgo := fvar_leaves_go_refines hrel hinv hs hr
  rw [hacc] at hgo
  show AOut (fun v => (absLeaves v).reverse) (fun _ => True) pers lst o st
    ((do let p ← fvarLeavesGo [] ∅ (absU fuel) (absEIdx h); pure p.1).run lst)
  rw [StateT.run_bind]
  cases hrc : r with
  | Ok p =>
    rw [hrc] at hgo hrun
    obtain ⟨s', lst', heq, -, hrel', hinv', hext⟩ := hgo
    obtain ⟨v, s0⟩ := p
    have h2 : core.result.Result.Ok v = o := Result.ok_injective hrun
    rw [← h2]
    refine AOut.ok (lst' := lst') ?_ hrel' hinv' hext trivial
    rw [heq]
    rfl
  | Err e =>
    rw [hrc] at hgo hrun
    have h2 : core.result.Result.Err e = o := Result.ok_injective hrun
    rw [← h2]
    exact AOut.err (AErrSim.bind hgo _)

/-- `leaves_sub_go` ⊑ `leavesSubGo`. -/
theorem leaves_sub_go_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState}
    {bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : LMemoRel rm lm)
    (hrun : arena.expr_ops.leaves_sub_go pers st bl rm fuel h = ok o) :
    LOut pers lst o st
      ((leavesSubGo (absLeaves bl) lm (absU fuel) (absEIdx h)).run lst) := by
  exact lsub_go_aux fuel.val rfl (fun _ _ => rfl) hrel hinv hm hrun

/-- `leaves_sub_node` ⊑ the twin's arm dispatch. -/
theorem leaves_sub_node_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState}
    {bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {fuel : Std.U64}
    {v : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : LMemoRel rm lm)
    (hrun : arena.expr_ops.leaves_sub_node pers st bl rm fuel v = ok o) :
    LOut pers lst o st
      ((leavesSubNodeSpec (absLeaves bl) lm (absU fuel)
        (absENodeView v)).run lst) := by
  exact lsub_node_of_go (lsub_go_aux fuel.val) rfl (fun _ _ => rfl) hrel hinv hm hrun

/-- `leaves_sub_two` ⊑ the twin's two-child arm, inline. -/
theorem leaves_sub_two_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState}
    {bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {fuel : Std.U64}
    {x y : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : LMemoRel rm lm)
    (hrun : arena.expr_ops.leaves_sub_two pers st bl rm fuel x y = ok o) :
    LOut pers lst o st ((do
      let (rf, m) ← leavesSubGo (absLeaves bl) lm (absU fuel) (absEIdx x)
      if rf then leavesSubGo (absLeaves bl) m (absU fuel) (absEIdx y)
      else pure (false, m)).run lst) := by
  exact lsub_two_of_go (lsub_go_aux fuel.val) rfl (fun _ _ => rfl) hrel hinv hm hrun

/-- `leaf_guard` ⊑ `leafGuard` — the fabrication leaf guard: the `fvarB = 0`
short-circuit, `base`'s leaf list, then one memoized walk of `fab`. -/
theorem leaf_guard_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {fab base : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.leaf_guard pers st fuel fab base = ok o) :
    AOut id (fun _ => True) pers lst o st
      ((leafGuard (absU fuel) (absEIdx fab) (absEIdx base)).run lst) := by
  rw [arena.expr_ops.leaf_guard] at hrun
  obtain ⟨w, hw, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hder := hw
  rw [arena.monad.derived_e] at hder
  obtain ⟨-, hfv, -⟩ := derObsE_fields (estore_derived_abs hrel.store hder)
  have hi1v := ConRon.Refine.Expr.fvar_of_data_val hi1
  have hfz : (ConLeche.fvarOfData (lst.store.derived (absEIdx fab))).toNat = i1.val := by
    rw [hfv, hi1v]
  rw [show leafGuard (absU fuel) (absEIdx fab) (absEIdx base) = (do
      if (ConLeche.fvarOfData (← derivedE (absEIdx fab))).toNat == 0 then pure true
      else do
        let bl ← fvarLeavesFast (absU fuel) (absEIdx base)
        let p ← leavesSubGo bl ∅ (absU fuel) (absEIdx fab)
        pure p.1) from rfl,
    StateT.run_bind,
    show (Arena.derivedE (absEIdx fab)).run lst
      = .ok (lst.store.derived (absEIdx fab), lst) from rfl]
  show AOut id (fun _ => True) pers lst o st
    ((do
      if ((ConLeche.fvarOfData (lst.store.derived (absEIdx fab))).toNat == 0) = true
      then pure true
      else do
        let bl ← fvarLeavesFast (absU fuel) (absEIdx base)
        let p ← leavesSubGo bl ∅ (absU fuel) (absEIdx fab)
        pure p.1).run lst)
  by_cases hc : i1 = 0#u64
  · rw [if_pos hc] at hrun
    have hz : ((ConLeche.fvarOfData (lst.store.derived (absEIdx fab))).toNat == 0)
        = true := by rw [hfz, hc]; rfl
    rw [if_pos hz]
    have ho := Result.ok_injective hrun
    rw [← ho]
    exact AOut.ok rfl hrel hinv (Ext.refl _) trivial
  · rw [if_neg hc] at hrun
    have hz : ¬ (((ConLeche.fvarOfData (lst.store.derived (absEIdx fab))).toNat == 0)
        = true) := by
      rw [hfz]
      simp only [beq_iff_eq]
      intro hzz
      exact hc (Std.UScalar.eq_of_val_eq (by rw [hzz]; rfl))
    rw [if_neg hz]
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hfl := fvar_leaves_fast_refines hrel hinv hr
    cases hrc : r with
    | Err e =>
      rw [hrc] at hrun hfl
      have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
        Result.ok_injective hrun
      rw [← ho]
      exact aout_err_bind hfl
    | Ok bl =>
      rw [hrc] at hrun hfl
      obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := hfl
      rw [StateT.run_bind, hx1]
      obtain ⟨memo, hmemo, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hnInv, -, hnNone⟩ :=
        ConRon.Refine.HashMap2.new_refines
          (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable)
          hmemo
      have hm : LMemoRel memo ∅ :=
        ⟨ConRon.Refine.HashMap2.RelOn_empty hnNone, hnInv⟩
      have hgo := lsub_go_aux (lbl := (absLeaves bl).reverse) fuel.val rfl
        (fun i t => leafMem_reverse _ i t) hrel1 hinv1 hm hr1
      show AOut id (fun _ => True) pers lst o st
        ((do
          let p ← leavesSubGo (absLeaves bl).reverse ∅ (absU fuel) (absEIdx fab)
          pure p.1).run lst1)
      rw [StateT.run_bind]
      cases hr1c : r1 with
      | Err e =>
        rw [hr1c] at hrun hgo
        have ho : (core.result.Result.Err e : core.result.Result Bool _) = o :=
          Result.ok_injective hrun
        rw [← ho]
        exact AOut.err (AErrSim.bind hgo _)
      | Ok p =>
        obtain ⟨b, m2⟩ := p
        rw [hr1c] at hrun hgo
        obtain ⟨m1, lst2, heq, -, hrel2, hinv2, hext2⟩ := hgo
        have ho : (core.result.Result.Ok b : core.result.Result Bool _) = o :=
          Result.ok_injective hrun
        rw [← ho]
        refine AOut.ok ?_ hrel2 hinv2 (Ext.trans hext1 hext2) trivial
        rw [heq]
        rfl



/-! ## The axiom census

The three `O(1)` derived reads and the three fuel inductions task #97-P5-2
closed, plus the whole of task #97-P5-3's file — the tag/view agreement, the
eight tag-first readers, the six arm-split walks, the three memo-threading
families with their owed twin equations, and `leaf_guard` — at the three
standard axioms and nothing else. -/

/-- info: 'ConRon.Refine2.ExprOps.inst_list_cutoff_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inst_list_cutoff_refines

/-- info: 'ConRon.Refine2.ExprOps.lidx_has_param_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lidx_has_param_refines

/-- info: 'ConRon.Refine2.ExprOps.eidx_has_level_param_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eidx_has_level_param_refines

/-- info: 'ConRon.Refine2.ExprOps.get_app_fn_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms get_app_fn_refines

/-- info: 'ConRon.Refine2.ExprOps.get_app_args_go_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms get_app_args_go_refines

/-- info: 'ConRon.Refine2.ExprOps.get_app_args_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms get_app_args_refines

/-- info: 'ConRon.Refine2.ExprOps.result_sort_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms result_sort_refines



/-- info: 'ConRon.Refine2.ExprOps.estore_view_tagOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_view_tagOf

/-- info: 'ConRon.Refine2.ExprOps.is_lam_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms is_lam_refines

/-- info: 'ConRon.Refine2.ExprOps.lam_pw_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lam_pw_refines

/-- info: 'ConRon.Refine2.ExprOps.forall_pw_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms forall_pw_refines

/-- info: 'ConRon.Refine2.ExprOps.fvar_type_d_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvar_type_d_refines

/-- info: 'ConRon.Refine2.ExprOps.strip_lams_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms strip_lams_refines

/-- info: 'ConRon.Refine2.ExprOps.strip_pis_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms strip_pis_refines

/-- info: 'ConRon.Refine2.ExprOps.pi_result_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pi_result_refines

/-- info: 'ConRon.Refine2.ExprOps.pi_arity_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pi_arity_refines

/-- info: 'ConRon.Refine2.ExprOps.size_b_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms size_b_refines

/-- info: 'ConRon.Refine2.ExprOps.size_f_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms size_f_refines

/-- info: 'ConRon.Refine2.ExprOps.has_fvar_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms has_fvar_refines

/-- info: 'ConRon.Refine2.ExprOps.wscoped_b_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wscoped_b_refines

/-- info: 'ConRon.Refine2.ExprOps.loose_bvars_bounded_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loose_bvars_bounded_refines

/-- info: 'ConRon.Refine2.ExprOps.fvar_leaves_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvar_leaves_refines

/-- info: 'ConRon.Refine2.ExprOps.wscopedBGo_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wscopedBGo_unfold

/-- info: 'ConRon.Refine2.ExprOps.wscoped_b_go_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wscoped_b_go_refines

/-- info: 'ConRon.Refine2.ExprOps.wscoped_b_node_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wscoped_b_node_refines

/-- info: 'ConRon.Refine2.ExprOps.wscoped_b_two_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wscoped_b_two_refines

/-- info: 'ConRon.Refine2.ExprOps.wscoped_b_fast_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wscoped_b_fast_refines

/-- info: 'ConRon.Refine2.ExprOps.leavesSubGo_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms leavesSubGo_unfold

/-- info: 'ConRon.Refine2.ExprOps.leaves_sub_go_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms leaves_sub_go_refines

/-- info: 'ConRon.Refine2.ExprOps.leaves_sub_node_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms leaves_sub_node_refines

/-- info: 'ConRon.Refine2.ExprOps.leaves_sub_two_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms leaves_sub_two_refines

/-- info: 'ConRon.Refine2.ExprOps.leafMem_reverse' depends on axioms: [propext] -/
#guard_msgs in #print axioms leafMem_reverse

/-- info: 'ConRon.Refine2.ExprOps.fvarLeavesGo_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvarLeavesGo_unfold

/-- info: 'ConRon.Refine2.ExprOps.fvar_leaves_go_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvar_leaves_go_refines

/-- info: 'ConRon.Refine2.ExprOps.fvar_leaves_node_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvar_leaves_node_refines

/-- info: 'ConRon.Refine2.ExprOps.fvar_leaves_two_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvar_leaves_two_refines

/-- info: 'ConRon.Refine2.ExprOps.fvar_leaves_fast_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fvar_leaves_fast_refines

/-- info: 'ConRon.Refine2.ExprOps.leaf_guard_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms leaf_guard_refines

end ConRon.Refine2.ExprOps
