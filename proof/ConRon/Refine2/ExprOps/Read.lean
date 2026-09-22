/-
# `ConRon.Refine2.ExprOps.Read` — Theorem 2 for `expr_ops`' READ-ONLY slice

**Deliverable 2 of task #97 P5, the thirty-three functions of
`crates/con-ron-core/src/arena/expr_ops.rs` that take `st : &AState`** — a
SHARED reference, so they read the store and never append.  The Rust's
post-state is its pre-state, which is why every statement below is `AOut`
(or `SimR`) at the *same* `st` on both sides and its `Ext` conjunct is
`Ext.refl`.

The statements are here; the proofs wait on `Refine2/Specs.lean`'s store-reader
inversion layer, which is not landed yet, and each `sorry` names the primitive
it waits on.

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
looks at either value. -/
def SeenRel (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (lm : Std.HashMap EIdx Unit) : Prop :=
  (∀ k, (toFun rm k).isSome = (lm[absEIdx k]?).isSome) ∧
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

/-- The outcome of `fvar_leaves_go`'s accumulator-and-`seen` pair. -/
def FOut (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result ((alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) ×
      ron.hashmap2.HashMap2 arena.handle.EIdx Bool) kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError
      ((List (Nat × EIdx) × Std.HashMap EIdx Unit) × AState)) : Prop :=
  match o with
  | .Ok r => ∃ s' lst', x = .ok ((absLeaves r.1, s'), lst') ∧ SeenRel r.2 s' ∧
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
shape step of task #97s round 3.  **All wait on `Specs.lean`'s `view`.** -/

/-- `size_b` ⊑ `sizeB` — node count with `fvar` a leaf. -/
theorem size_b_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.size_b pers st fuel h = ok o) :
    AOut absU (fun _ => True) pers lst o st
      ((sizeB (absU fuel) (absEIdx h)).run lst) := by
  sorry

/-- `size_f` ⊑ `sizeF` — full node count, `fvar` annotations included. -/
theorem size_f_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.size_f pers st fuel h = ok o) :
    AOut absU (fun _ => True) pers lst o st
      ((sizeF (absU fuel) (absEIdx h)).run lst) := by
  sorry

/-- `fvar_leaves` ⊑ `fvarLeaves` — the unmemoized leaf walk.  The Rust builds
a `Vec` where the twin conses a `List`; `absLeaves` is the map. -/
theorem fvar_leaves_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_leaves pers st fuel h = ok o) :
    AOut absLeaves (fun _ => True) pers lst o st
      ((fvarLeaves (absU fuel) (absEIdx h)).run lst) := by
  sorry

/-- `wscoped_b` ⊑ `wscopedB` — the unmemoized scope check. -/
theorem wscoped_b_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {fuel d : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.wscoped_b pers st fuel d h = ok o) :
    AOut id (fun _ => True) pers lst o st
      ((wscopedB (absU fuel) (absU d) (absEIdx h)).run lst) := by
  sorry

/-- `has_fvar` ⊑ `hasFvar` — the pure walk behind the `O(1)` field read. -/
theorem has_fvar_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.has_fvar pers st fuel h = ok o) :
    AOut id (fun _ => True) pers lst o st
      ((hasFvar (absU fuel) (absEIdx h)).run lst) := by
  sorry

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
  sorry

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
  sorry

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

/-- The owed equation: the twin's `wscopedBGo` at `fuel + 1` IS the cutoff,
the probe, `wscopedBNodeSpec` at the view, and the insert.  `rfl`-level once
the `do` block is unfolded; it is the one lemma of this file that is not a
`Specs.lean` primitive. -/
theorem wscopedBGo_unfold (memo : Std.HashMap (EIdx × Nat) Bool) (fuel d : Nat)
    (h : EIdx) :
    wscopedBGo memo (fuel + 1) d h = (do
      if (fvarOfData (← derivedE h)).toNat == 0 then pure (true, memo)
      else
        match memo[(h, d)]? with
        | some r => pure (r, memo)
        | none => do
          let (r, memo') ← wscopedBNodeSpec memo fuel d (← view h)
          pure (r, memo'.insert (h, d) r)) := by
  sorry

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
  sorry

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
  sorry

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
      ((fvarLeavesGo (absLeaves racc) ls (absU fuel) (absEIdx h)).run lst) := by
  sorry

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
      ((fvarLeavesNodeSpec (absLeaves racc) ls (absU fuel)
        (absENodeView v)).run lst) := by
  sorry

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
      let (acc, seen) ← fvarLeavesGo (absLeaves racc) ls (absU fuel) (absEIdx x)
      fvarLeavesGo acc seen (absU fuel) (absEIdx y)).run lst) := by
  sorry

/-- `fvar_leaves_fast` ⊑ `fvarLeavesFast`. -/
theorem fvar_leaves_fast_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.fvar_leaves_fast pers st fuel h = ok o) :
    AOut absLeaves (fun _ => True) pers lst o st
      ((fvarLeavesFast (absU fuel) (absEIdx h)).run lst) := by
  rw [arena.expr_ops.fvar_leaves_fast] at hrun
  obtain ⟨seen, hseen, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hnInv, -, hnNone⟩ :=
    ConRon.Refine.HashMap2.new_refines
      (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable)
      hseen
  have hs : SeenRel seen ∅ := by
    refine ⟨fun k => ?_, hnInv⟩
    rw [hnNone k]
    simp
  have hacc : absLeaves (alloc.vec.Vec.new (Std.U64 × arena.handle.EIdx)) = [] := rfl
  have hgo := fvar_leaves_go_refines hrel hinv hs hr
  rw [hacc] at hgo
  show AOut absLeaves (fun _ => True) pers lst o st
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
  sorry

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
  sorry

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
  sorry

/-- `leaf_guard` ⊑ `leafGuard` — the fabrication leaf guard: the `fvarB = 0`
short-circuit, `base`'s leaf list, then one memoized walk of `fab`. -/
theorem leaf_guard_refines {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {fuel : Std.U64}
    {fab base : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.leaf_guard pers st fuel fab base = ok o) :
    AOut id (fun _ => True) pers lst o st
      ((leafGuard (absU fuel) (absEIdx fab) (absEIdx base)).run lst) := by
  sorry


/-! ## The axiom census

The three `O(1)` derived reads and the three fuel inductions this round
closed, at the three standard axioms and nothing else. -/

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


end ConRon.Refine2.ExprOps
