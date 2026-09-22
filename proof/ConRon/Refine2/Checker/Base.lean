/-
# `ConRon.Refine2.Checker.Base` — Theorem 2 for `arena::checker_base` and `arena::checker_split`

**Task #97-P5-Checker**, deliverable 2 (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/{checker_base,checker_split}.rs` against
`proof/ConRon/Arena/{CheckerBase,CheckerSplit}.lean`: the declaration
checker's common ground — the per-declaration constant check, the two
memoised guard walks, the projection-rule stages, the attempt bracket — and
the install/check seam of a value declaration.

## The one seam where (B) and (C) are not the same state

`orElseAttempt` (DESIGN §8.3 and task #97-LC's ledger row).  The port keeps
its `&mut AState` across a failing attempt, so it restores the memos and the
caches and **KEEPS the store** — the attempt's appended nodes stay,
unreachable.  A throw in `StateT AState (Except ε)` carries no state at all,
so the twin's error arm can only resume at the pre-attempt state, whose store
is the pre-attempt one.  The two therefore differ on the handle NUMBERING
after a recovered variant attempt, never on a denotation and never on a
verdict.

*What the refinement owes at this seam is `Ext` rather than store equality* —
which is exactly why `Refine2/Shape.lean`'s `AOut` carries `Ext lst.store
lst'.store` in EVERY success arm rather than store equality, at no cost
(`Ext.refl` for a reader, `Ext.trans` through a bind).  `attempt_restore` and
`or_else_attempt` below are where that decision is cashed, and their
conclusions are the only ones in the tier that are `Ext`-ONLY: nothing is
claimed about the two stores beyond one extending the other.

## Finding 10 — `vis` out of the index is a hypothesis at seventy-one sites

Task #97-P6-6b took the visibility counter OUT of the environment record's
read path: `ifenv_find(vis, fe, n)` takes `vis : u64` beside `fe`, because
reading `fe.visible_below` inside the call forced a copy of the record.  The
twin's `IFEnv.find?` reads `fe.visibleBelow`.  So every statement whose Rust
takes a `vis` parameter carries

    hvis : absU vis = lf.visibleBelow

and it is discharged at the top by `IFEnvRel.visibleBelow` — the call sites
all pass `fe.visible_below` — but must be threaded through the tier, because
inside it `vis` is an ordinary argument.  **Seventy-one statements of this
tier carry it**, and like task #97-P5-0's finding 3
it is a fact about the port's own calling convention rather than a
divergence.

## What these lemmas wait on

`Refine2/Specs.lean`'s `view`/`intern_e` family (closed and open
respectively), `Refine2/ExprOps/**` (statements only so far) and
`Refine2/Core/**` — P5-Core's tier, which is where `annotateCore`,
`inferTypeCore`, `isDefEqCore` and `ensureSortCore` live.  `KnotRel` carries
them here (`Refine2/Checker/KnotHyp.lean`).
-/
import ConRon.Refine2.Checker.Axioms
import ConRon.Refine2.Checker.Spec

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine (NameWF NamesWF ExprWF)

/-! ## The attempt bracket — the `Ext`-only seam -/

/-- `arena::checker_base::AttemptSnapshot` against the twin's: the per-call
memo tables and the per-declaration caches, and **not** the store (task
#97-P6-2's ledger entry).  Related rather than abstracted, for the reason
every memo table in this tower is. -/
structure SnapRel (rs : arena.checker_base.AttemptSnapshot) (ls : AttemptSnapshot) :
    Prop where
  memos : MemosRel rs.memos ls.memos
  caches : CachesRel rs.caches ls.caches
  memosInv : MemosInv rs.memos
  cachesInv : CachesInv rs.caches

/-- `memos_dup` is the identity on the abstraction: `ron::hashmap::Dup`'s
`dup2` is `DupId` at every one of the thirteen tables (`Refine2/Inv.lean`). -/
theorem memos_dup_refines {rm lm} {o}
    (hrel : MemosRel rm lm) (hinv : MemosInv rm)
    (hrun : arena.checker_base.memos_dup rm = ok o) :
    MemosRel o lm ∧ MemosInv o := by
  sorry

/-- `caches_dup` is the identity on the abstraction. -/
theorem caches_dup_refines {rc lc} {o}
    (hrel : CachesRel rc lc) (hinv : CachesInv rc)
    (hrun : arena.checker_base.caches_dup rc = ok o) :
    CachesRel o lc ∧ CachesInv o := by
  sorry

/-- `attempt_snapshot` ⊑ `attemptSnapshot` — in Lean a read of two fields, in
Rust the two `dup`s above. -/
theorem attempt_snapshot_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.attempt_snapshot st = ok o) :
    SnapRel o (attemptSnapshot lst) := by
  sorry

/-- `attempt_restore` ⊑ `attemptRestore` — **the attempt's cache rows and memo
rows go, its interned nodes STAY**, which is why the conclusion is `Ext` and
not store equality: the Rust's post-state and the twin's agree on the memos
and the caches and on the STORE ONLY UP TO `Ext` (the Rust keeps the attempt's
unreachable appends; the twin, throwing in `StateT σ (Except ε)`, cannot). -/
theorem attempt_restore_refines {pers st lst} {snap lsnap} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hsnap : SnapRel snap lsnap)
    (hrun : arena.checker_base.attempt_restore st snap = ok o) :
    ∃ lst', AStateRel pers o lst' ∧ AStateInv pers o ∧
      lst'.memos = lsnap.memos ∧ lst'.caches = lsnap.caches ∧
      Ext lst.store lst'.store := by
  sorry

/-- `or_else_attempt` ⊑ `orElseStepOf` — the four-way step as a PURE function
of the attempt's outcome, which is the shape the port has and which the twin
copied.  `failed` carries **only** a `native` error (DESIGN §8.3's ruling): the
arena's own machine-word limit has no `throw` behind it in con-leche, so
"con-leche would have recovered from this too" is a claim about a run the
cited checker never has. -/
theorem or_else_attempt_refines {attempt} {o}
    (hrun : arena.checker_base.or_else_attempt attempt = ok o) :
    ∀ b, attempt = .Ok b → o = (if b then .Matched else .Continued) := by
  intro b hb
  subst hb
  rw [arena.checker_base.or_else_attempt] at hrun
  cases b <;> simp_all

/-! ## The `Vec` duplications

`vec_dup` and `vec_dup_range` are `ron::hashmap::Dup` lifted to a vector;
`Refine2/Inv.lean`'s five `DupId` lemmas say `dup2` is the identity at every
handle type, so both are the identity on the abstraction. -/

/-- `vec_dup_range` copies `xs[lo..hi]` onto `out`, `dup2` at each element. -/
theorem vec_dup_range_refines {T β : Type} {A : T → β}
    {inst : ron.hashmap.Dup T} {xs out : alloc.vec.Vec T}
    {lo hi : Std.Usize} {o}
    (hdup : ConRon.Refine.HashMap.DupId inst)
    (hrun : arena.checker_base.vec_dup_range inst xs out lo hi = ok o) :
    o.val.map A = out.val.map A ++
      ((xs.val.drop lo.val).take (hi.val - lo.val)).map A := by
  sorry

/-- `vec_dup` is the identity on the abstraction. -/
theorem vec_dup_refines {T β : Type} {A : T → β} {inst : ron.hashmap.Dup T}
    {xs : alloc.vec.Vec T} {o}
    (hdup : ConRon.Refine.HashMap.DupId inst)
    (hrun : arena.checker_base.vec_dup inst xs = ok o) :
    o.val.map A = xs.val.map A := by
  sorry

/-! ## The name-shape tests

`ConLeche/Kernel/Level.lean`'s three `Name` predicates: the declaration front
door is their only reader.  Each is a handle comparison or one `viewN`. -/

/-- `nidx_contains_from` is `ns.contains n` from the cursor on. -/
theorem nidx_contains_from_refines {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {n : arena.handle.NIdx} {o : Bool}
    (hrun : arena.checker_base.nidx_contains_from ns i n = ok o) :
    o = (absNIdxLFrom ns i).contains (absNIdx n) := by
  sorry

/-- `name_nodup_from` ⊑ `nameNodup` from the cursor on. -/
theorem name_nodup_from_refines {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.checker_base.name_nodup_from ns i = ok o) :
    o = nameNodup (absNIdxLFrom ns i) := by
  sorry

/-- `name_nodup` ⊑ `nameNodup` — no duplicates in a list of name HANDLES.  A
name comparison is a handle comparison, which is sound because `denoteN` is
injective (DESIGN §8.3 makes exactness a soundness obligation for exactly this
reason). -/
theorem name_nodup_refines {ns : alloc.vec.Vec arena.handle.NIdx} {o : Bool}
    (hrun : arena.checker_base.name_nodup ns = ok o) :
    o = nameNodup (absNIdxL ns) := by
  sorry

/-- `nidx_is_model_suffix` ⊑ `NIdx.isModelSuffix`. -/
theorem nidx_is_model_suffix_refines {pers st lst} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.nidx_is_model_suffix pers st n = ok o) :
    SimRE id lst o (NIdx.isModelSuffix (absNIdx n)) := by
  sorry

/-- `nidx_is_proj_fn_shape` ⊑ `NIdx.isProjFnShape`. -/
theorem nidx_is_proj_fn_shape_refines {pers st lst} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.nidx_is_proj_fn_shape pers st n = ok o) :
    SimRE id lst o (NIdx.isProjFnShape (absNIdx n)) := by
  sorry

/-! ## The two memoised guard walks

Both thread a `HashMap2<EIdx, bool>` exactly as `expr_ops`' three memoised
walks do; `Refine2/Checker/Shape.lean`'s `SimBM` / `SimBR` are the two shapes
(the second walk reads the store and interns nothing, so it is a reader). -/

/-- `memo_b_get` is the walk's `memo[h]?` — extraction rule 5's own function. -/
theorem memo_b_get_refines {rm lm} {k : arena.handle.EIdx} {o}
    (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.checker_base.memo_b_get rm k = ok o) :
    o = lm[absEIdx k]? := by
  rw [arena.checker_base.memo_b_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hmr, hminv⟩ := hm
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hminv
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hmr k trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option Bool) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    have h2 : some r = o := Result.ok_injective hrun
    subst h2
    rfl

/-- `consts_resolve_f_go` ⊑ `constsResolveFGo`.  Finding 10's `hvis`. -/
theorem consts_resolve_f_go_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rm lm} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.checker_base.consts_resolve_f_go pers vis st rf rm fuel h = ok o) :
    SimBM id pers lst o (constsResolveFGo lf lm (absU fuel) (absEIdx h)) := by
  sorry

/-- `consts_resolve_f_node` is `consts_resolve_f_go`'s miss arm past the
`view` (extraction rule 5), stated against the twin's arm at that view. -/
theorem consts_resolve_f_node_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rm lm} {fuel : Std.U64} {v : arena.store.ENodeView} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hm : ExprOps.LMemoRel rm lm)
    (hview : lst.store.view (absEIdx h) = some (absENodeView v))
    (hrun : arena.checker_base.consts_resolve_f_node pers vis st rf rm fuel v = ok o) :
    SimBM id pers lst o
      (constsResolveFNodeSpec lf lm (absU fuel) (absEIdx h) (absENodeView v)) := by
  sorry

/-- `consts_resolve_f_two` is the two-child arms' pair, in the twin's order
and WITHOUT a short-circuit (the twin's `.app` arm walks both and `&&`s). -/
theorem consts_resolve_f_two_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rm lm} {fuel : Std.U64} {a b : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.checker_base.consts_resolve_f_two pers vis st rf rm fuel a b = ok o) :
    SimBM id pers lst o
      (do
        let (b₁, memo) ← constsResolveFGo lf lm (absU fuel) (absEIdx a)
        let (b₂, memo) ← constsResolveFGo lf memo (absU fuel) (absEIdx b)
        pure (b₁ && b₂, memo)) := by
  sorry

/-- `consts_resolve_f_fast` ⊑ `constsResolveFFast` — one memoised DAG walk,
which is what every front door below calls. -/
theorem consts_resolve_f_fast_refines {pers st lst} {vis : Std.U64} {rf lf}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.consts_resolve_f_fast pers vis st rf e = ok o) :
    Sim id (fun _ => True) pers lst o (constsResolveFFast lf (absEIdx e)) := by
  sorry

/-- `all_params_defined_list` is `ls.all (Level.allParamsDefined params)` from
the cursor on — a PURE test on con-leche values, so it carries their WF. -/
theorem all_params_defined_list_refines
    {params : alloc.vec.Vec kernel.name.Name}
    {ls : alloc.vec.Vec kernel.level.Level} {i : Std.Usize} {o : Bool}
    (hp : NamesWF params) (hl : ConRon.Refine.LevelsWF ls)
    (hrun : arena.checker_base.all_params_defined_list params ls i = ok o) :
    o = (absLevelLFrom ls i).all
      (ConLeche.Level.allParamsDefined (ConRon.Refine.absNames params)) := by
  sorry

/-- `all_level_params_defined_go` ⊑ `allLevelParamsDefinedGo` — a READER
(`SimBR`): the level-parameter test interns nothing. -/
theorem all_level_params_defined_go_refines {pers st lst}
    {params : alloc.vec.Vec kernel.name.Name} {rm lm} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hp : NamesWF params) (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.checker_base.all_level_params_defined_go pers st params rm fuel h
      = ok o) :
    SimBR id lst o
      (allLevelParamsDefinedGo (ConRon.Refine.absNames params) lm (absU fuel)
        (absEIdx h)) := by
  sorry

/-- `all_level_params_defined_node` is the walk's miss arm past the probe. -/
theorem all_level_params_defined_node_refines {pers st lst}
    {params : alloc.vec.Vec kernel.name.Name} {rm lm} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hp : NamesWF params) (hm : ExprOps.LMemoRel rm lm)
    (hmiss : lm[absEIdx h]? = none)
    (hrun : arena.checker_base.all_level_params_defined_node pers st params rm fuel h
      = ok o) :
    SimBR id lst o
      (allLevelParamsDefinedGo (ConRon.Refine.absNames params) lm (absU fuel)
        (absEIdx h)) := by
  sorry

/-- `all_level_params_defined_binder` is the walk's `.lam` / `.forallE` arm —
the one that also tests the binder metadatum's `PropWhen`. -/
theorem all_level_params_defined_binder_refines {pers st lst}
    {params : alloc.vec.Vec kernel.name.Name} {rm lm} {fuel : Std.U64}
    {t b : arena.handle.EIdx} {m : kernel.expr.BinderMeta} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hp : NamesWF params) (hm : ExprOps.LMemoRel rm lm)
    (hmwf : ConRon.Refine.BinderMetaWF m)
    (hrun : arena.checker_base.all_level_params_defined_binder pers st params rm
      fuel t b m = ok o) :
    SimBR id lst o
      (do
        let (b₁, memo) ← allLevelParamsDefinedGo (ConRon.Refine.absNames params)
          lm (absU fuel) (absEIdx t)
        if !b₁ then pure (false, memo) else do
          let (b₂, memo) ← allLevelParamsDefinedGo (ConRon.Refine.absNames params)
            memo (absU fuel) (absEIdx b)
          pure (b₂ && (ConRon.Refine.absBinderMeta m).pw.paramsDefined
            (ConRon.Refine.absNames params), memo)) := by
  sorry

/-- `all_level_params_defined` ⊑ `allLevelParamsDefined` — one memoised DAG
walk, at the parameter list read back once. -/
theorem all_level_params_defined_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.all_level_params_defined pers st lps e = ok o) :
    SimRE id lst o (allLevelParamsDefined (absNIdxL lps) (absEIdx e)) := by
  sorry

/-! ## The front door's verdict at an unresolved constant -/

/-- `unresolved_consts_error` ⊑ `unresolvedConstsError`.  The result is a
CheckError, so it is a `SimRel` at the kind: a term that mentions `sorryAx`
DECLINES (`notImplemented`) and anything else REJECTS (`invalid`), and the
claim is that the two agree on WHICH — messages are never compared
(DESIGN §3.1). -/
theorem unresolved_consts_error_refines {pers st lst} {e : arena.handle.EIdx} {o}
    {w : String}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.unresolved_consts_error pers st e = ok o) :
    SimRel (fun r v => absAErrKind r = lAErrKind v) pers lst o
      (unresolvedConstsError w (absEIdx e)) := by
  sorry

/-! ## The per-declaration constant check -/

/-- `check_constant_val_guards_rest` is `check_constant_val_guards`'s tail past
the duplicate-declaration test (extraction rule 5). -/
theorem check_constant_val_guards_rest_refines {pers st lst}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.check_constant_val_guards_rest pers st cv = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkConstantValGuardsRestSpec (absIConstantVal cv)) := by
  sorry

/-- `check_constant_val_guards` is `installConstantVal`'s guard prefix — the
syntactic tests before the annotation. -/
theorem check_constant_val_guards_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_constant_val_guards pers vis st rf cv = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkConstantValGuardsSpec lf (absIConstantVal cv)) := by
  sorry

/-- `install_constant_val_tail` is `installConstantVal`'s tail past the
annotation: the level-parameter test and the constant-resolution test. -/
theorem install_constant_val_tail_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv : arena.env.IConstantVal} {ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.install_constant_val_tail pers vis st rf cv ty = ok o) :
    Sim absIConstantVal (fun _ => True) pers lst o
      (installConstantValTailSpec lf (absIConstantVal cv) (absEIdx ty)) := by
  sorry

/-- `check_constant_val_after_annot` is `checkConstantVal`'s tail: the
install-side tail plus the type's own inference and sort check. -/
theorem check_constant_val_after_annot_refines {pers st lst} {vis : Std.U64}
    {rf lf} {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_constant_val_after_annot pers vis st mode rf cv ty
      = ok o) :
    Sim absIConstantVal (fun _ => True) pers lst o
      (checkConstantValAfterAnnotSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx ty)) := by
  sorry

/-- **`check_constant_val` ⊑ `checkConstantVal`** — the common per-declaration
constant check, whole. -/
theorem check_constant_val_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_constant_val pers vis st mode rf cv = ok o) :
    Sim absIConstantVal (fun _ => True) pers lst o
      (checkConstantVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) := by
  sorry

/-! ## Opening a pi telescope at fresh free variables -/

/-- `open_pis_at_fvars` ⊑ `openPisAtFvars` — structural on `n`, so no fuel of
its own. -/
theorem open_pis_at_fvars_refines {pers st lst} {n : Std.U64}
    {h : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.open_pis_at_fvars pers st n h i = ok o) :
    Sim (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) (fun _ => True)
      pers lst o (openPisAtFvars (absU n) (absEIdx h) (absU i)) := by
  sorry

/-- `open_pis_at_fvars_f_go` ⊑ `openPisAtFvarsFGo` — `acc` holds the
already-created fvars, innermost binder first; one `instantiateList` pass per
domain instead of one whole-telescope `instantiate1` pass per binder. -/
theorem open_pis_at_fvars_f_go_refines {pers st lst}
    {acc : alloc.vec.Vec arena.handle.EIdx} {n : Std.U64}
    {h : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.open_pis_at_fvars_f_go pers st acc n h i = ok o) :
    Sim (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) (fun _ => True)
      pers lst o
      (openPisAtFvarsFGo (absEIdxL acc).toArray (absU n) (absEIdx h) (absU i)) := by
  sorry

/-- `open_pis_at_fvars_f` ⊑ `openPisAtFvarsF` — the one-pass form, with the
fallback that covers telescopes whose binders only appear after
substitution. -/
theorem open_pis_at_fvars_f_refines {pers st lst} {n : Std.U64}
    {e : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.open_pis_at_fvars_f pers st n e i = ok o) :
    Sim (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) (fun _ => True)
      pers lst o (openPisAtFvarsF (absU n) (absEIdx e) (absU i)) := by
  sorry

/-- `fvar_type_ds` ⊑ `fvarTypeDs` at the cursor — `xs.map Expr.fvarTypeD`,
with DESIGN §3.4's closure-free `List` recursion. -/
theorem fvar_type_ds_refines {pers st lst}
    {hs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.fvar_type_ds pers st hs i out = ok o) :
    SimRE (fun v => absEIdxL out ++ absEIdxL v) lst o
      (do pure (absEIdxL out ++ (← fvarTypeDs (absEIdxLFrom hs i)))) := by
  sorry

/-! ## The equality head -/

/-- `is_eq_head` ⊑ `isEqHead` — is the expression the pinned equality former at
one level? -/
theorem is_eq_head_refines {pers st lst} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.is_eq_head pers st h = ok o) :
    Sim id (fun _ => True) pers lst o (isEqHead (absEIdx h)) := by
  sorry

/-- `eq_head_level_at` is `eq_head_level`'s tail at the universe-argument list
(extraction rule 5). -/
theorem eq_head_level_at_refines {pers st lst} {us : arena.handle.LsIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.eq_head_level_at pers st us = ok o) :
    Sim absLIdx (fun _ => True) pers lst o
      (do
        match ← viewLs (absLsIdx us) with
        | [l] => pure l
        | _ => zeroLevel) := by
  sorry

/-- `eq_head_level` ⊑ `eqHeadLevel` — off shape it is `.zero`, which
`isEqHead` has already rejected wherever the result is used. -/
theorem eq_head_level_refines {pers st lst} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.eq_head_level pers st h = ok o) :
    Sim absLIdx (fun _ => True) pers lst o (eqHeadLevel (absEIdx h)) := by
  sorry

/-! ## The three list checks -/

/-- `check_typed_list` ⊑ `checkTypedList` at the cursor. -/
theorem check_typed_list_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {depth : Std.U64}
    {xs ts : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_typed_list pers vis st mode rf depth xs ts i
      = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkTypedList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i) (absEIdxLFrom ts i)) := by
  sorry

/-- `check_annot_list` ⊑ `checkAnnotList` at the cursor. -/
theorem check_annot_list_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {depth : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_annot_list pers vis st mode rf depth xs i
      = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkAnnotList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i)) := by
  sorry

/-- `check_def_eq_list` ⊑ `checkDefEqList` at the cursor. -/
theorem check_def_eq_list_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {depth : Std.U64}
    {xs ys : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_def_eq_list pers vis st mode rf depth xs ys i
      = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkDefEqList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i) (absEIdxLFrom ys i)) := by
  sorry

/-! ## `unwrapOr`, the environment lookup and the pi result sort -/

/-- `unwrap_or` ⊑ `unwrapOr` — unwrap an optional value or fail with the given
error.  Polymorphic, so the abstraction of the element and the correspondence
of the two errors are both parameters. -/
theorem unwrap_or_refines {T β : Type} {A : T → β} {lst} {o : Option T}
    {err : kernel.core_types.CheckError} {lerr : Arena.CheckError} {r}
    (herr : absAErrKind err = lAErrKind lerr)
    (hrun : arena.checker_base.unwrap_or o err = ok r) :
    SimRE A lst r (unwrapOr (o.map A) lerr) := by
  sorry

/-- `ifenv_find_cv` ⊑ `IFEnv.findCV?`.  Finding 10's `hvis`. -/
theorem ifenv_find_cv_refines {pers st lst} {vis : Std.U64} {rf lf}
    {n : arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.ifenv_find_cv pers vis st rf n = ok o) :
    Sim (Option.map absIConstantVal) (fun _ => True) pers lst o
      (lf.findCV? (absNIdx n)) := by
  sorry

/-- `pi_result_sort` ⊑ `piResultSort`. -/
theorem pi_result_sort_refines {pers st lst} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.pi_result_sort pers st e = ok o) :
    SimRE (Option.map absLIdx) lst o (piResultSort (absEIdx e)) := by
  sorry

/-! ## The projection stages

`checkProjShape` (stage 2b) and `checkProjRule` (stage 3) are twinned in
`Arena/CheckerBase.lean` because they need nothing from
`ConLeche/Kernel/Inductives/*`.  The Rust splits stage 3 into six, which is
extraction rule 5 at a function with eleven live handles. -/

/-- `doms_match_aux_from` ⊑ `domsMatchAux` from the cursor on — over handles a
domain comparison is a handle comparison, so this is PURE. -/
theorem doms_match_aux_from_refines
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 n i : Std.U64} {o : Bool}
    (hrun : arena.checker_base.doms_match_aux_from bs1 bs2 o1 o2 n i = ok o) :
    o = (List.range (absU n - absU i)).all fun j =>
      match (absBinderArr bs1)[absU o1 + absU i + j]?,
            (absBinderArr bs2)[absU o2 + absU i + j]? with
      | some b₁, some b₂ => b₁.1 == b₂.1
      | _, _ => false := by
  sorry

/-- `doms_match_aux` ⊑ `domsMatchAux` — con-leche's `List` version is
quadratic on a wide telescope and its `Array` twin is what the checker runs,
so the twin is the array one. -/
theorem doms_match_aux_refines
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 n : Std.U64} {o : Bool}
    (hrun : arena.checker_base.doms_match_aux bs1 bs2 o1 o2 n = ok o) :
    o = domsMatchAux (absBinderArr bs1) (absBinderArr bs2)
      (absU o1) (absU o2) (absU n) := by
  sorry

/-- `check_proj_shape_residual` is `check_proj_shape`'s tail: the
constructor's residual is the family applied to exactly the parameters. -/
theorem check_proj_shape_residual_refines {pers st lst}
    {cbody : arena.handle.EIdx} {n_p : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.check_proj_shape_residual pers st cbody n_p = ok o) :
    SimRE (fun _ : Unit => ()) lst o
      (do
        unless (← getAppArgs coreWalkFuel (absEIdx cbody)).length == absU n_p do
          fail (.notImplemented "projection constructor residual arity")
        match ← view (← getAppFn coreWalkFuel (absEIdx cbody)) with
        | .const _ _ => pure ()
        | _ => fail (.notImplemented "projection constructor residual head")) := by
  sorry

/-- `check_proj_shape` ⊑ `checkProjShape` — stage 2b. -/
theorem check_proj_shape_refines {pers st lst}
    {pty ctor_ty : arena.handle.EIdx} {n_p n_f : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.check_proj_shape pers st pty ctor_ty n_p n_f = ok o) :
    SimRE (fun _ : Unit => ()) lst o
      (checkProjShape (absEIdx pty) (absEIdx ctor_ty) (absU n_p) (absU n_f)) := by
  sorry

/-- `proj_rule_wf` is `check_proj_rule`'s four-way well-formedness conjunct. -/
theorem proj_rule_wf_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rhs_a : arena.handle.EIdx} {lps : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.proj_rule_wf pers vis st rf rhs_a lps = ok o) :
    Sim id (fun _ => True) pers lst o
      (do
        pure ((← allLevelParamsDefined (absNIdxL lps) (absEIdx rhs_a)) &&
          (← constsResolveFFast lf (absEIdx rhs_a)) &&
          (← looseBVarsBoundedFast coreWalkFuel 0 (absEIdx rhs_a)) &&
          !(← hasFvarFast coreWalkFuel (absEIdx rhs_a)))) := by
  sorry

/-- `check_proj_rule_frame` is stage 3's parameter-frame check: the type's
telescope opened at fresh free variables, the constructor's domains
instantiated at them and compared. -/
theorem check_proj_rule_frame_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {n_p n_f : Std.U64}
    {fvs_p : alloc.vec.Vec arena.handle.EIdx}
    {crest_p rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule_frame pers vis st mode rf n_p n_f
      fvs_p crest_p rhs_a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (checkProjRuleFrameSpec (ConRon.Refine.absMode mode) lf (absU n_p) (absU n_f)
        (absEIdxL fvs_p) (absEIdx crest_p) (absEIdx rhs_a)) := by
  sorry

/-- `check_proj_rule_certs` is stage 3's certificate tail. -/
theorem check_proj_rule_certs_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule_certs pers vis st mode rf pty cvj
      n_p n_f rhs_a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (checkProjRuleCertsSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absU n_p) (absU n_f) (absEIdx rhs_a)) := by
  sorry

/-- `check_proj_rule_shape` is stage 3's λ-telescope shape check. -/
theorem check_proj_rule_shape_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {bv rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule_shape pers vis st mode rf pty cvj
      n_p n_f bv rhs_a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (checkProjRuleShapeSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs_a)) := by
  sorry

/-- `check_proj_rule_wf` is stage 3 past the annotation. -/
theorem check_proj_rule_wf_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {bv rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule_wf pers vis st mode rf pty cvj lps
      n_p n_f bv rhs_a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (checkProjRuleWfSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs_a)) := by
  sorry

/-- `check_proj_rule_scoped` is stage 3 past the scoping test. -/
theorem check_proj_rule_scoped_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {bv rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule_scoped pers vis st mode rf pty cvj lps
      n_p n_f bv rhs = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (checkProjRuleScopedSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs)) := by
  sorry

/-- **`check_proj_rule` ⊑ `checkProjRule`** — stage 3, whole: λ over the
constructor telescope returning field `i`, annotated; its λ-domains stay the
constructor's. -/
theorem check_proj_rule_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule pers vis st mode rf pty cvj lps
      n_p n_f i = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (checkProjRule (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absU i)) := by
  sorry

/-! ## The block's partition and its declared parameter count -/

/-- `is_rec_info` ⊑ `isRecInfo`. -/
theorem is_rec_info_refines {ci : arena.env.IConstantInfo} {o : Bool}
    (hrun : arena.checker_base.is_rec_info ci = ok o) :
    o = isRecInfo (absIConstantInfo ci) := by
  rw [arena.checker_base.is_rec_info.eq_def] at hrun
  cases ci <;> (
    simp only [] at hrun
    have h2 := Result.ok_injective hrun
    subst h2
    rfl)

/-- `all_rec_info` is `rest.all isRecInfo` from the cursor on. -/
theorem all_rec_info_refines {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.checker_base.all_rec_info block i = ok o) :
    o = (absICILFrom block i).all isRecInfo := by
  sorry

/-- `recs_form_suffix` ⊑ `recsFormSuffix` from the cursor on — do the
recursors form a suffix of the block? -/
theorem recs_form_suffix_refines {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.checker_base.recs_form_suffix block i = ok o) :
    o = recsFormSuffix (absICILFrom block i) := by
  sorry

/-- `ind_params_ok_at` is `ind_params_ok`'s per-member test. -/
theorem ind_params_ok_at_refines {pers st lst} {n_p : Std.U64}
    {ci : arena.env.IConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.ind_params_ok_at pers st n_p ci = ok o) :
    Sim id (fun _ => True) pers lst o
      (indParamsOkAtSpec (absU n_p) (absIConstantInfo ci)) := by
  sorry

/-- `ind_params_ok` ⊑ `indParamsOk` from the cursor on — **the stream's
declared parameter count, checked as official checks it** (con-leche's task
#228).  Both halves are one-sided on purpose: `false` means official
rejects. -/
theorem ind_params_ok_refines {pers st lst} {n_p : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.ind_params_ok pers st n_p block i = ok o) :
    Sim id (fun _ => True) pers lst o
      (indParamsOk (absU n_p) (absICILFrom block i)) := by
  sorry

/-! ## `arena::checker_split` — the install/check seam of a value declaration

DESIGN §8.3's per-declaration bracket lives here: the install half writes the
annotated type and the annotated value (the terms the environment stores, so
they must be PERSISTENT and the half runs OUTSIDE the bracket), and the check
half infers and compares (everything it allocates is intermediate, and the
scratch tier is dropped at its end). -/

/-- `value_kind_word` ⊑ `ValueKind.word` — the kind's word in `checkDecl`'s
type-mismatch message, as code points (DESIGN §3.3). -/
theorem value_kind_word_refines {k : arena.checker_split.ValueKind} {o}
    (hrun : arena.checker_split.value_kind_word k = ok o) :
    ConRon.Refine.absString o = (absValueKind k).word := by
  sorry

/-- `is_thm` is the twin's `g.kind == .thm`. -/
theorem is_thm_refines {k : arena.checker_split.ValueKind} {o : Bool}
    (hrun : arena.checker_split.is_thm k = ok o) :
    o = (absValueKind k == .thm) := by
  rw [arena.checker_split.is_thm.eq_def] at hrun
  cases k <;> (
    simp only [] at hrun
    have h2 := Result.ok_injective hrun
    subst h2
    rfl)

/-- **`install_constant_val` ⊑ `installConstantVal`** — `checkConstantVal`
minus its inference: the syntactic guards and the annotation of the type. -/
theorem install_constant_val_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_split.install_constant_val pers vis st mode rf cv = ok o) :
    Sim absIConstantVal (fun _ => True) pers lst o
      (installConstantVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) := by
  sorry

/-- `install_value_tail` is `install_value`'s tail past the annotation. -/
theorem install_value_tail_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv : arena.env.IConstantVal} {value_a : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_split.install_value_tail pers vis st rf cv value_a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (installValueTailSpec lf (absIConstantVal cv) (absEIdx value_a)) := by
  sorry

/-- **`install_value` ⊑ `installValue`** — the value half of
`check{Defn,Thm,Opaque}Val` minus its inference. -/
theorem install_value_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_split.install_value pers vis st mode rf cv value = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (installValue (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  sorry

/-- `check_value_group_value` is `check_value_group`'s middle: the theorem's
is-a-proposition test and, for a theorem, the value's guards and annotation. -/
theorem check_value_group_value_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup}
    {u : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_split.check_value_group_value pers vis st mode rf g u
      = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkValueGroupValueSpec (ConRon.Refine.absMode mode) lf (absValueGroup g)
        (absLIdx u)) := by
  sorry

/-- `check_value_group_tail` is `check_value_group`'s tail: the value's type
against the declared one. -/
theorem check_value_group_tail_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup}
    {jv : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_split.check_value_group_tail pers vis st mode rf g jv
      = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkValueGroupTailSpec (ConRon.Refine.absMode mode) lf (absValueGroup g)
        (absEIdx jv)) := by
  sorry

/-- **`check_value_group` ⊑ `checkValueGroup`** — the check half of a value
declaration, at the environment the constant was installed at. -/
theorem check_value_group_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_split.check_value_group pers vis st mode rf g = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkValueGroup (ConRon.Refine.absMode mode) lf (absValueGroup g)) := by
  sorry


/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.or_else_attempt_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms or_else_attempt_refines

/-- info: 'ConRon.Refine2.is_rec_info_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms is_rec_info_refines

/-- info: 'ConRon.Refine2.memo_b_get_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memo_b_get_refines

/-- info: 'ConRon.Refine2.is_thm_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms is_thm_refines

end ConRon.Refine2
